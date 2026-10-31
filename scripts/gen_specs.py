#!/usr/bin/env python3
"""Generate SPECS.lean, SPECS_UNFOLDED.lean and SPECS_INTERNAL.lean: the specifications of every
function of the proof image, for review.

    python3 scripts/gen_specs.py            # write the three files (experiments/specs_pp.jsonl)
    python3 scripts/gen_specs.py --lean     # first rerun Lean's pretty printer (needs the build)
    python3 scripts/gen_specs.py --check    # fail if a file is not what it generates

SPECS.lean holds the concise specification of each public function's main contract: the theorems
of Tom/Machine/Specs/*.lean, verbatim (statement over Tom/Machine/Conventions.lean's `MpOwn`,
`MpOut`, `Conv`, `Eff`, `ApiTriple`, `MemOr`, … and its bridging proof from the machine contract); the
generator checks that each main form of experiments/specs.tsv has one (`mp_add_correct_ca` ↦
`Specs.mp_add_ca`) and that its proof names the form's machine proof. A main form without one is
printed unfolded instead. SPECS_UNFOLDED.lean has the same contracts unfolded, as follows.

In SPECS_UNFOLDED.lean and SPECS_INTERNAL.lean, every proved form of each function's contract (experiments/specs.tsv, most general first) is stated
as a theorem whose type is the contract expanded down to its `Triple` and whose proof is the machine
proof; after each function, its postcondition's `.spec` lemmas (the meaning over Int/Nat) restated.
The expansion is Lean's: scripts/specs_pp.lean (run by `--lean`, under `lake env lean`, with
SPECS.lean's imports) unfolds the statement's wrappers and definitions, splits its precondition
structures into one hypothesis per field and its witness bundle into one per region, and pretty
prints; its output is kept in experiments/specs_pp.jsonl so that the check needs no build.
SPECS.lean elaborating (scripts/check.sh, step 5) is what makes the printed statements faithful:
each is checked against the machine proof's own.
"""
import glob, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)
OUT = 'SPECS.lean'
OUT_UNF = 'SPECS_UNFOLDED.lean'
OUT_INT = 'SPECS_INTERNAL.lean'

# ---------------------------------------------------------------- Lean sources

def comments(s):
    """(start, end) of every comment of a Lean source (nested block comments, strings skipped)."""
    out, i, n = [], 0, len(s)
    while i < n:
        c = s[i]
        if c == '"':
            i += 1
            while i < n and s[i] != '"':
                i += 2 if s[i] == '\\' else 1
            i += 1
        elif c == "'" and (i == 0 or not re.match(r"[\w'!?À-￿]", s[i - 1])):
            if s[i + 1:i + 2] == '\\':
                j = s.find("'", i + 2)
                i = j + 1 if j > 0 else i + 1
            elif s[i + 2:i + 3] == "'":
                i += 3
            else:
                i += 1
        elif s.startswith('--', i):
            j = s.find('\n', i)
            j = n if j < 0 else j
            out.append((i, j)); i = j
        elif s.startswith('/-', i):
            depth, j = 1, i + 2
            while j < n and depth:
                if s.startswith('/-', j): depth += 1; j += 2
                elif s.startswith('-/', j): depth -= 1; j += 2
                else: j += 1
            out.append((i, j)); i = j
        elif c == '«':
            i = s.find('»', i) + 1
        else:
            i += 1
    return out


def blank(s):
    t = list(s)
    for a, b in comments(s):
        for i in range(a, b):
            if t[i] != '\n':
                t[i] = ' '
    return ''.join(t)


KW = r'(?:(?:private|protected|noncomputable|partial)\s+)*(def|theorem|abbrev|structure|inductive|class|instance)'


def index(files):
    """Top-level declarations: full name -> file, kind, namespace, open lines, verbatim text."""
    decls = {}
    for p in sorted(files):
        s = open(p, encoding='utf-8').read()
        t = blank(s)
        lines = [(m.start(), m.group(0)) for m in re.finditer(r'^\S.*$', t, re.M)]
        ns, frames, opens = [], [], [[]]
        for k, (i, line) in enumerate(lines):
            m = re.match(r'namespace (\S+)', line)
            if m:
                c = m.group(1).split('.')
                ns += c; frames.append(len(c)); opens.append(list(opens[-1])); continue
            if re.match(r'(?:noncomputable )?section\b', line):
                frames.append(0); opens.append(list(opens[-1])); continue
            m = re.match(r'end\b\s*(\S*)', line)
            if m:
                if frames:
                    n = len(m.group(1).split('.')) if m.group(1) else frames[-1]
                    n = min(n, frames[-1])
                    del ns[len(ns) - n:]
                    frames[-1] -= n
                    if frames[-1] <= 0 or not m.group(1):
                        frames.pop(); opens.pop()
                continue
            if re.match(r'open\s', line) and not re.search(r'\bin\s*$', line):
                opens[-1].append(line.strip()); continue
            m = re.match(r'(?:@\[[^\]]*\]\s*)?' + KW + r'\s+(\S+)', line)
            if not m:
                continue
            kind, name = m.group(1), m.group(2)
            j = k + 1
            while j < len(lines) and re.match(r'[|)\]}⟩·]|deriving\b|where\b|with\b', lines[j][1]):
                j += 1
            end = lines[j][0] if j < len(lines) else len(s)
            body = t[i:end].rstrip()
            end = i + len(body)
            a, pre = i, s[:i].rstrip()
            if pre.endswith('-/'):
                d = pre.rfind('/--')
                if d >= 0 and d >= pre.rfind('-/', 0, len(pre) - 2):
                    a = d
            full = '.'.join(ns + [name])
            decls[full] = dict(file=p, kind=kind, name=name, ns=list(ns), opens=list(opens[-1]),
                               line=s.count('\n', 0, i) + 1, text=s[a:end].rstrip(), code=t[i:end].rstrip(),
                               off=i - a)
    return decls


D = index(glob.glob('Tom/**/*.lean', recursive=True) + ['Vsa/Triple.lean'])

def open_names(d):
    out = []
    for o in d['opens']:
        body = re.sub(r'\([^)]*\)', ' ', o[len('open'):])
        out += [x for x in body.split() if x not in ('scoped', 'hiding', 'renaming', 'in')]
    return out


IDENT = re.compile(r"[A-Za-z_À-῿][\w'!?À-῿]*(?:\.[A-Za-z_À-῿][\w'!?À-῿]*)*")


def resolve(tok, d):
    if tok in D:
        return tok
    ns = d['ns']
    cands = ['.'.join(ns[:i] + [tok]) for i in range(len(ns), -1, -1)]
    cands += [o + '.' + tok for o in open_names(d)]
    cands += ['Tom.' + tok, 'Tom.Machine.' + tok, 'Tom.Machine.Api.' + tok]
    for c in cands:
        if c in D:
            return c
    parts = tok.split('.')
    if len(parts) > 1 and parts[0][:1].islower():
        for c in ('Tom.MpInt.' + parts[-1],):
            if c in D:
                return c
    return None


def refs(d, sig_only=False):
    code = signature(d['code']) if sig_only else d['code']
    code = re.sub(r'"(\\.|[^"\\])*"', '""', code)
    out = []
    for m in IDENT.finditer(code):
        r = resolve(m.group(0), d)
        if r and r not in out:
            out.append(r)
    return out


def signature(code):
    depth = 0
    for i, ch in enumerate(code):
        if ch in '([{⟨⦃':
            depth += 1
        elif ch in ')]}⟩⦄':
            depth -= 1
        elif code.startswith(':=', i) and depth == 0:
            return code[:i]
    return code

# ---------------------------------------------------------------- what to show

# The vocabulary printed once, first.
COMMON = ['Tom.radix', 'Tom.natUpTo', 'Tom.MpInt', 'Tom.MpInt.digit', 'Tom.MpInt.Shape',
          'Tom.MpInt.Valid', 'Tom.MpInt.mag', 'Tom.MpInt.val', 'Tom.ordCode', 'Tom.MpInt.ShapeU',
          'Tom.MpInt.ValidU', 'Vsa.Logic.Triple', 'Tom.Machine.At', 'Tom.Machine.MpAt',
          'Tom.Machine.Bundle', 'Tom.Machine.Sound', 'Tom.Machine.AHeap', 'Tom.Machine.HPost',
          'Tom.Machine.Api.Heap.OffHeap', 'Tom.Machine.Api.Heap.StkRes', 'Tom.Machine.Frm']
COMMON = [c for c in COMMON if c in D] + sorted(k for k in D if k.startswith('Tom.Layout.'))

# Names of the machine plumbing of a contract: summarised, never pasted.
PLUMB = {'lay', 'kind', 'out', 'isW', 'ws', "site'", 'site', 'hin', 'hout', 'args', 'rets', 'entry',
         'F', 'Fm', 'Fd', 'Fn', 'Ff', 'Fs', 'Fk', 'Ft', 'R', 'all', 'entryL', 'entL', 'entry1', 'retL',
         'jL', 'gpV', 'textIv', 'kcAddr', 'tcAddr', 'digBlk', 'memBV', 'regs', 'Fa',
         'Fb', 'Fc', 'Fr', 'Fq', 'depth', 'base', 'Iv', 'Kind'}
KINDS = ('def', 'abbrev', 'structure', 'inductive', 'class')


def allowed(name, root_files):
    d = D[name]
    if name in COMMON or d['kind'] not in KINDS or d['name'] in PLUMB:
        return False
    f = d['file']
    return f in root_files or f.startswith(('Tom/Machine/Api/', 'Tom/Spec/'))


def closure(roots, root_files, sig_only_first=False):
    """The definitions a statement is made of, breadth first."""
    seen, order, frontier = set(roots), [], list(roots)
    first = True
    while frontier:
        nxt = []
        for n in frontier:
            for r in refs(D[n], sig_only=first and sig_only_first and D[n]['kind'] == 'theorem'):
                if r not in seen and allowed(r, root_files):
                    seen.add(r); order.append(r); nxt.append(r)
        frontier, first = nxt, False
    return order


# ---------------------------------------------------------------- inputs

code = open('Tom/Machine/Code.lean', encoding='utf-8').read()
FUNCS = [f for f, _, _ in re.findall(r'/-- `([^`]+)`: (\d+) instructions at \[0x([0-9a-f]+)', code)]
TOM = sorted(f for f in FUNCS if f.startswith(('mp_', 's_mp_')))
LIB = [f for f in FUNCS if f not in TOM]

forms, lib_forms = {}, []
for row in open('experiments/specs.tsv', encoding='utf-8'):
    if row.startswith('#') or not row.strip():
        continue
    f, name, stmt, proof = row.rstrip('\n').split('\t')
    if f.startswith('@'):
        lib_forms.append((f[1:].split(), name, stmt, proof))
    else:
        forms.setdefault(f, []).append((name, stmt, proof))

missing = [f for f in TOM if f not in forms]
missing += [f for f in LIB if not any(f in fs for fs, *_ in lib_forms)]
if missing:
    sys.exit(f'gen_specs: no proved form listed in experiments/specs.tsv for {", ".join(missing)}')
def head(term):
    return re.sub(r'\.[12]$', '', term.split()[0])

for f, fs in list(forms.items()) + [(' '.join(x[0]), [x[1:]]) for x in lib_forms]:
    for name, stmt, proof in fs:
        for t in ([] if stmt == '-' else [stmt.replace('∀ n, ', '').split()[0]]) + [head(p) for p in proof.split()]:
            if head(t) not in D:
                sys.exit(f'gen_specs: {f}: unknown name {t}')

# ---------------------------------------------------------------- what Lean prints

PP = 'experiments/specs_pp.jsonl'


def scope(name):
    """The namespace and `open` lines a declaration is stated in."""
    d = D[name]
    return '.'.join(d['ns']), d['opens']


SPEC = {}
for k, d in D.items():
    if d['kind'] == 'theorem' and d['file'].startswith('Tom/Spec/') and \
            re.match(r'(spec|val|valid)', k.rsplit('.', 1)[1]):
        SPEC.setdefault(k.rsplit('.', 1)[0], []).append(k)


def spec_lemmas(fn_forms, done):
    """The `.spec` lemmas (Tom/Spec) of the definitions a function's statements are made of."""
    out = []
    for name, stmt, proof in fn_forms:
        root = head(proof) if stmt == '-' else stmt.replace('∀ n, ', '').split()[0]
        for n in closure([root], {D[root]['file']}, sig_only_first=stmt == '-'):
            for k in SPEC.get(n, []):
                if k not in done:
                    done.add(k); out.append(k)
    return out


# The public functions: declared in tommath.h. SPECS.lean has each one's main contract (the growing
# form, and its aliasing forms `mp_add(a, b, a)`, ...); SPECS_INTERNAL.lean everything else.
PUBLIC = set(re.findall(r'\b(mp_\w+)\s*\(', open('vendor/libtommath/tommath.h', encoding='utf-8').read()))


def main_form(fn, name):
    return fn in PUBLIC and re.fullmatch(re.escape(fn) + r'_correct(_ca|_cb|_inplace|_alias)?', name)


def items():
    """Every theorem, in order: (file, section, name, stmt or None, proof, scope decl)."""
    out, done = [], set()
    def form(f, fn, name, stmt, proof):
        out.append((f, fn, name, None if stmt == '-' else stmt, proof,
                    head(proof) if stmt == '-' else stmt.replace('∀ n, ', '').split()[0]))
    for f in (OUT_UNF, OUT_INT):
        for fn in TOM:
            fs = [x for x in forms[fn] if bool(main_form(fn, x[0])) == (f == OUT_UNF)]
            for name, stmt, proof in fs:
                form(f, fn, name, stmt, proof)
            for k in spec_lemmas(fs, done):
                out.append((f, fn, k.removeprefix('Tom.').replace('.', '_'), None, k, k))
    for fs, name, stmt, proof in lib_forms:
        form(OUT_INT, '@', name, stmt, proof)
    return out


ITEMS = items()


def imports(f):
    return sorted({D[head(p)]['file'][:-5].replace('/', '.') for g, *_, proof, _ in ITEMS if g == f
                   for p in proof.split()})


def lean_pp():
    """Run scripts/specs_pp.lean on every item; keep its output in experiments/specs_pp.jsonl."""
    import subprocess, tempfile, json
    src = open('scripts/specs_pp.lean', encoding='utf-8').read()
    src = src.split('\n', 1)[1] if src.startswith('import Lean\n') else src
    lines = [f'import {m}' for m in sorted(set(imports(OUT_UNF) + imports(OUT_INT)))] + ['import Lean', src]
    for _, _, name, stmt, proof, decl in ITEMS:
        ns, opens = scope(decl)
        lines += [f'namespace {ns}'] + opens
        if stmt is None:
            lines.append(f'#spec_pp_thm {name} := {proof}')
        else:
            lines.append(f'#spec_pp {name} : {stmt} := {proof}')
        lines.append(f'end {ns}')
    with tempfile.TemporaryDirectory() as t:
        drv = os.path.join(t, 'SpecsPP.lean')
        open(drv, 'w', encoding='utf-8').write('\n'.join(lines) + '\n')
        r = subprocess.run(['lake', 'env', 'lean', drv], capture_output=True, text=True)
    rows, errs = [], []
    for l in r.stdout.splitlines():
        if l.startswith('{'):
            rows.append(json.loads(l))
        else:
            errs.append(l)
    if r.returncode != 0 or len(rows) != len(ITEMS):
        sys.exit('gen_specs: scripts/specs_pp.lean failed:\n' + '\n'.join(errs[:40]) + r.stderr[-2000:])
    with open(PP, 'w', encoding='utf-8') as f:
        for j in rows:
            f.write(json.dumps(j, ensure_ascii=False, sort_keys=True) + '\n')

# ---------------------------------------------------------------- output

def hexify(s):
    """Large numerals (addresses, masks) in hex."""
    return re.sub(r"(?<![\w.'#])(\d{7,})(?![\w.])", lambda m: hex(int(m.group(1))) if int(m.group(1)) >= 1 << 20
                  else m.group(1), s)


def indent(text, n):
    return text.replace('\n', '\n' + ' ' * n)


def wrap(words, first, rest, width=100):
    """Words on lines of at most `width` columns."""
    lines, cur = [], first
    for w in words:
        if cur.strip() and (len(cur) + 1 + len(w.split('\n')[0]) > width or '\n' in cur):
            lines.append(cur.rstrip()); cur = rest + w
        else:
            cur = cur + (' ' if cur.strip() else '') + w
    lines.append(cur.rstrip())
    return '\n'.join(lines)


def binder_groups(binders):
    """Consecutive data binders of the same kind and type share one group: `{sp pa : Nat}`."""
    close = {'{': '}', '(': ')', '⦃': '⦄', '[': ']'}
    out = []
    for bi, n, ty, hyp in binders:
        ty = hexify(ty)
        if out and not hyp and not out[-1][3] and out[-1][0] == bi and out[-1][2] == ty and '\n' not in ty:
            out[-1][1].append(n)
        else:
            out.append([bi, [n], ty, hyp])
    return [(f'{bi}{" ".join(ns)} : {indent(ty, 6)}{close[bi]}', hyp) for bi, ns, ty, hyp in out]


def theorem(j, decl):
    ns, opens = scope(decl)
    binders = binder_groups(j['binders'])
    k = next((i for i, (_, hyp) in enumerate(binders) if hyp), len(binders))
    data = [b for b, _ in binders[:k]]     # the leading data binders on the first lines
    hyps = [b for b, _ in binders[k:]]     # then one binder per line, in order
    out = [f'namespace {ns}'] + opens
    head_ = wrap(data, f'theorem _root_.Specs.{j["name"]}', '    ')
    out.append(head_)
    for h in hyps:
        out.append('    ' + h)
    out[-1] += ' :'
    out.append('    ' + indent(hexify(j['concl']), 4) + ' :=')
    words = []
    for a in j['args']:
        m = re.match(r'\(fun r => match r with (.*)\)$', a)
        if m:
            alts = re.split(r' (?=\| \.)', m.group(1))
            words.append('(fun r => match r with\n        ' + '\n        '.join(alts) + ')')
        else:
            words += a.split(' ')
    if j['hasStmt']:
        stmt = next(x[3] for x in ITEMS if x[2] == j['name'])
        names = {b[1] for b in j['binders']}
        h = next(c for c in ['H', 'H0', 'H1', 'H2', 'HS'] if c not in names)
        out.append(f'  have {h} : {stmt} := {j["proof"]}')
        out.append(wrap(words, f'  @{h}', '      '))
    else:
        out.append(wrap(words, f'  @{j["proof"]}', '      '))
    out.append(f'end {ns}')
    return '\n'.join(out)


WHAT = {
    OUT_UNF: '''the public functions of libtommath v1.3.0 (those declared in tommath.h), compiled for RV64I
(c/tommath-arith.elf), unfolded: for each, alphabetically, the main contract that SPECS.lean states
concisely (the growing form, then the aliasing forms such as `mp_add(a, b, a)`), with no
definition of Tom/Machine/Conventions.lean, and the `.spec` lemmas that read its postcondition over
Int/Nat. SPECS_INTERNAL.lean has the other forms, the s_mp_* helpers and newlib/libgcc''',
    OUT_INT: '''the rest of c/tommath-arith.elf (libtommath v1.3.0 on RV64I): the forms of the public
functions not in SPECS.lean (destination with room, called D5 in the sources; narrower aliasing
forms), the s_mp_* helpers, and the newlib/libgcc routines (allocator, memset/memcpy, 64-bit
multiply and divide)''',
}

INTRO = '''/-
WHAT
Each statement is the contract with its definitions unfolded; its proof names the contract as
stated in the sources (`have H : …Statement := …`) and the machine proof:

  theorem Specs.f {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}
      (hyp₁ : ...) ... (hypₙ : ...) :
      Triple (At entry regs m v.keep outp)
        fun cf => ∃ x M, At ra rets M v.keep outp cf ∧ post x ∧ HPost ... m M

* `Triple P Q` is total correctness on the Sail RISC-V model: from every state satisfying `P`, some
  finite run reaches a state satisfying `Q`. `At pc regs m keep outp` is the machine at `pc` with
  the registers `regs` (`(1, ra)`, `(2, sp)`, `(10, a0)`, `(11, a1)`, ...), memory `m`, the
  callee-saved registers `keep` and console output `outp`. The run ends back at `ra` with memory `M`
  and result `x`: `none` is MP_MEM, `some (q, c')` the new `mp_int` `c'` with its digits at `q`.
* `p : P` (the structure `P` of the namespace opened above the theorem) names the `mp_int`s as
  `MpInt` values (`p.a.used`, `.alloc`, `.sign`, `.digits`; `mag`/`val` its Nat/Int value) and where
  they are: `p.pa` the struct, `p.adp` its digits, `p.sp` the stack pointer, `p.H` the live heap
  blocks. Some contracts take these as separate binders (`pa adp : Nat`, `a : MpInt`).
* The hypotheses are the precondition, one per line: the operands' invariants (`Valid`, `Shape`),
  the C's `int` bounds, the stack (`F` bytes below `p.sp` are free RAM above the heap), and memory:
  `Hdr m pa adp a` (the struct at `pa` holds `a`'s used/alloc/sign and the pointer `adp`),
  `Dig m adp n f` (`n` digits `f` at `adp`), `MpAt` (both), `Ram`, `Img m` (the program image),
  `Sound (lay p) isW` (the written regions are disjoint from all others), `AHeap m H` (the
  allocator's heap with live blocks `H`), `Off` (the regions lie off the allocator's memory).
* The postcondition: the result's arithmetic (`AddG`, `Post`, ... over Tom/Spec definitions; the
  `Specs.X_spec` theorems state what it means, e.g. `x.val = a.val + b.val`) and the frame
  (`HPost`, `Frm`: only the written regions `ws` and the allocator's footprint change).
* Any other name is a definition in the opened namespace or in Tom/Spec, Tom/Machine/Kit,
  Tom/Machine/Api; go to its definition for its meaning.
-/
'''


def render(f):
    import json
    rows = {}
    for l in open(PP, encoding='utf-8'):
        j = json.loads(l); rows[j['name']] = j
    missing = [x[2] for x in ITEMS if x[2] not in rows]
    if missing:
        sys.exit(f'gen_specs: {PP} lacks {", ".join(missing[:5])}: run python3 scripts/gen_specs.py --lean')
    body, prev = [], None
    for g, sec, name, stmt, proof, decl in ITEMS:
        if g != f:
            continue
        if sec != prev and prev is not None:
            body.append('')
        prev = sec
        body.append(theorem(rows[name], decl))
    import textwrap
    what = textwrap.fill(f'The specifications of {" ".join(WHAT[f].split())}. Generated by '
                         'scripts/gen_specs.py; `#print axioms` of each theorem shows only propext, '
                         'Classical.choice and Quot.sound.', 100)
    intro = INTRO.replace('WHAT', what)
    text = ('\n'.join(f'import {m}' for m in imports(f)) + '\n\n' + intro +
            '\nset_option linter.unusedVariables false\nset_option linter.ambiguousOpen false\n\n' + '\n\n'.join(body) + '\n')
    return re.sub(r'\n{4,}', '\n\n\n', text)


# ---------------------------------------------------------------- SPECS.lean: the concise forms

CONCISE_DIR = 'Tom/Machine/Specs'

INTRO_C = """/-
The specifications of the public functions of libtommath v1.3.0 (those declared in tommath.h),
compiled for RV64I (c/tommath-arith.elf): for each, alphabetically, its main contract (the growing
form, then the aliasing forms such as `mp_add(a, b, a)`), over Int/Nat, in the conventions of
Tom/Machine/Conventions.lean (read it once). The allocating functions read

  def eff (p : P) := Eff.heap (lay p) isW ws .cD (out p) (site' p) (hin p) (hout p) optView

  theorem Specs.f {p : P} (cv : Conv m ra p.sp F (eff p)) (a : MpOwn m p.H p.pa p.adp p.a) ...
      (c : MpOut m p.pc p.cdp p.c) (side conditions) :
      ApiTriple m v outp ra entry p.sp [p.pa, ..., p.pc] (eff p) (mem := when MP_MEM)
        fun c' => c'.Valid ∧ c'.val = ...

* `ApiTriple`: total correctness on the Sail RISC-V model: from `entry` with `a0, a1, ...` holding
  the arguments, the run returns to `ra` with `a0` `MP_MEM` (then `mem`, by default no claim) or
  `MP_OKAY` and the result `c'` meaning what the `fun` says. `m v outp ra` (the `variable`s below):
  the memory, the callee-saved registers, the console output, the return address.
* `p : P` (the structure `P` of the namespace above the theorem) names the `mp_int`s (`p.a : MpInt`;
  `.val`/`.mag` its Int/Nat value) and where they are: `p.pa` the struct, `p.adp` its digits, `p.sp`
  the stack pointer, `p.H` the live heap blocks.
* `eff p` (`Eff`): the contract's regions `lay`, written ones `isW`/`ws`, outcomes `out`, the
  result's site and heap blocks before/after (`site'`, `hin`, `hout`), and the result an outcome
  gives the caller (`optView`, `okView`, or the module's `res`); the memory frame it implies
  (`HPost`: only the written regions and the allocator's footprint change) is part of `ApiTriple`.
* `MpOwn`/`MpOut`: an `mp_int` argument read/written (struct and digits in memory, valid/initialized,
  digits a live heap block); `Conv`: the stack of `F` bytes, the program image, the allocator's
  heap, the written regions disjoint from all others (`Sound`).
* `CInt n` (`n < 2^31`), `CIdx n` (`n < 2^30`), `FitsBits n`, `Fits a`: the C's `int` arithmetic on
  sizes stays in range.
* The functions that do not allocate: `MpVal` (a valid `mp_int` in memory), `ConvL`/`ConvM`/`ConvS`,
  `ApiPure` (a value in `a0`, memory unchanged), `ApiTripleS` (the frame-pointer calls; `Post`, the
  contract's: the result in memory and the frame).
Each proof bridges from the machine contract (`Fn.….correct : Api.….Statement`) and the `.spec`
lemma of its postcondition; SPECS_UNFOLDED.lean states the same contracts with every definition
unfolded down to the triple (and the `.spec` lemmas). A form stated unfolded here has no concise
one. SPECS_INTERNAL.lean has the other forms, the s_mp_* helpers and newlib/libgcc. Generated by
scripts/gen_specs.py from Tom/Machine/Specs/*.lean; `#print axioms` of each theorem shows only
propext, Classical.choice and Quot.sound.
-/
"""


def concise_modules():
    """Tom/Machine/Specs/*.lean: imports, body (module doc dropped), the theorems they state."""
    mods = []
    for path in sorted(glob.glob(CONCISE_DIR + '/*.lean')):
        src = open(path, encoding='utf-8').read()
        imps = re.findall(r'^import (\S+)$', src, re.M)
        body = re.sub(r'^(import \S+|set_option autoImplicit false)\n', '', src, flags=re.M).lstrip('\n')
        # the file-level `open`/`variable` lines (before the first namespace) go to SPECS.lean's header
        k = body.find('\nnamespace ')
        pre, post = (body[:k], body[k:]) if k >= 0 else (body, '')
        head = re.findall(r'^(?:open|variable) .*$', pre, re.M)
        pre = re.sub(r'^(?:open|variable) .*\n', '', pre, flags=re.M)
        body = (pre + post).lstrip('\n')
        body = re.sub(r'\A/-!.*?-/\n+', '', body, flags=re.S)
        names = re.findall(r'^theorem _root_\.Specs\.(\S+)', blank(src), re.M)
        mods.append(dict(path=path, imports=imps, body=body.rstrip() + '\n', names=names, src=src,
                         head=head))
    return mods


def render_concise():
    import json
    rows = {}
    for l in open(PP, encoding='utf-8'):
        j = json.loads(l); rows[j['name']] = j
    mods = concise_modules()
    owner = {}
    for md in mods:
        for n in md['names']:
            if n in owner:
                sys.exit(f'gen_specs: Specs.{n} stated twice ({owner[n]["path"]}, {md["path"]})')
            owner[n] = md
    body, imps, done, used, n_thm = [], set(), set(), set(), 0
    header = []
    for md in mods:
        header += [h for h in md['head'] if h not in header]
    for fn in TOM:
        fs = [x for x in forms[fn] if main_form(fn, x[0])]
        sec = []
        for name, stmt, proof in fs:
            c = name.replace('_correct', '', 1)
            md = owner.get(c)
            if md is None:
                # no concise form yet: the unfolded statement
                decl = head(proof) if stmt == '-' else stmt.replace('∀ n, ', '').split()[0]
                sec.append(theorem(rows[name], decl)); n_thm += 1
                imps.update(D[head(p)]['file'][:-5].replace('/', '.') for p in proof.split())
                continue
            used.add(c)
            # the bridge must start from the form's machine proof
            short = '.'.join(head(proof.split()[0]).split('.')[-2:])
            t = re.search(r'^theorem _root_\.Specs\.' + re.escape(c) + r'\b.*?(?=^(?:theorem|end|namespace) )',
                          md['src'], re.M | re.S)
            last = short.split('.')[-1]
            if not t or not (short in t.group(0) or re.search(r'(?<![\w.])' + re.escape(last) + r'\b', t.group(0))
                             and short.split('.')[0] in md['src']):
                sys.exit(f'gen_specs: {md["path"]}: Specs.{c} does not cite {short} ({name} in experiments/specs.tsv)')
            if md['path'] not in done:
                done.add(md['path']); sec.append(md['body'].rstrip()); n_thm += len(md['names'])
                imps.update(i for i in md['imports'] if not i.startswith('Tom.Machine.Specs.'))
        if sec:
            body.append('\n\n'.join(sec))
    extra = sorted(set(owner) - used)
    if extra:
        sys.exit(f'gen_specs: Tom/Machine/Specs states {", ".join(extra)}, not a main form of experiments/specs.tsv')
    text = ('\n'.join(f'import {m}' for m in sorted(imps)) + '\n\n' + INTRO_C +
            '\nset_option autoImplicit false\nset_option linter.unusedVariables false\n'
            'set_option linter.ambiguousOpen false\n\n' + '\n'.join(header) + '\n\n' +
            '\n\n'.join(body) + '\n')
    return re.sub(r'\n{4,}', '\n\n\n', text), n_thm


if '--lean' in sys.argv:
    lean_pp()
bad = []
for f in (OUT, OUT_UNF, OUT_INT):
    text, n = render_concise() if f == OUT else (render(f), sum(1 for x in ITEMS if x[0] == f))
    if '--check' in sys.argv:
        old = open(f, encoding='utf-8').read() if os.path.exists(f) else ''
        if old != text:
            bad.append(f)
        continue
    open(f, 'w', encoding='utf-8').write(text)
    print(f'gen_specs: {n} theorems -> {f} ({text.count(chr(10))} lines)')
if bad:
    sys.exit(f'gen_specs: {", ".join(bad)} not what scripts/gen_specs.py generates')
