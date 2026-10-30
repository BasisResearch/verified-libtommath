#!/usr/bin/env python3
"""Generate SPECS.lean: the specification of every function of the proof image, for review.

    python3 scripts/gen_specs.py            # write SPECS.lean
    python3 scripts/gen_specs.py --check    # fail if SPECS.lean is not what it generates

For each libtommath function of c/tommath-arith.elf (alphabetical): its C prototype, every proved
form of its contract (experiments/specs.tsv, most general first) re-stated as a theorem whose proof
is the machine proof, and the definitions the statement is made of, copied verbatim from the Lean
sources (the contract's residue, result and postcondition, and the Tom/Spec definitions they use).
Machine plumbing (stack depth, registers, regions) is summarised in one line per contract. The
newlib/libgcc routines the functions reach are in a short appendix.
"""
import glob, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)
OUT = 'SPECS.lean'

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


def plumbing(stmt):
    """One line: entry, arguments, stack, regions of a contract's namespace."""
    ns = stmt.rsplit('.', 1)[0]
    d0 = D[stmt]
    def find(short):
        for c in [ns + '.' + short] + [o + '.' + short for o in open_names(d0)]:
            if c in D:
                return D[c]
    parts = []
    e = find('entry')
    if e:
        m = re.search(r'0x[0-9a-f]+', e['code'])
        if m: parts.append(f'entry `{m.group(0)}`')
    a = find('args')
    if a:
        m = re.search(r'/--\s*(.*?)\s*-/', a['text'], re.S)
        if m:
            t = ' '.join(m.group(1).split()).rstrip('.')
            parts.append(t[:1].lower() + t[1:])
    f = find('F')
    if f:
        rhs = ' '.join(f['code'].split(':=', 1)[-1].split())
        parts.append(f'stack reservation `F = {rhs}`' if len(rhs) < 90 else 'stack reservation `F` (by size)')
    r = find('R')
    if r and r['kind'] == 'inductive':
        ctors = re.findall(r'\|\s*([\w\']+)', r['code'])
        if ctors: parts.append('regions ' + ' '.join(ctors))
    w = find('ws')
    if w:
        rhs = ' '.join(w['code'].split(':=', 1)[-1].split())
        parts.append(f'written {rhs}')
    return '; '.join(parts)


def title(file):
    for l in open(file, encoding='utf-8'):
        if l.startswith('# '):
            return l[2:].strip()
    return ''


SHAPE = ('def Statement : Prop := ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, '
         'ra.toNat % 4 = 0 → Res p → Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → '
         '(∀ r, Off (lay p r) (hin p)) → Triple (At entry ((1, ra) :: args p) m v.keep outp) '
         '(fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧ '
         "HPost (lay p) ws SITE (out p x) (site' p x) (hin p) (hout p x) m M)")


def render(n):
    """A declaration's text, the standard statement and plain parameter records compressed."""
    d = D[n]
    flat = ' '.join(d['code'].split())
    m = re.fullmatch(re.escape(SHAPE).replace('SITE', r'(\.\w+)'), flat)
    if m:
        return f'def Statement : Prop := Standard.Statement Res Q (site {m.group(1)})  -- the standard shape (top of file)'
    if d['kind'] == 'structure' and d['name'] == 'P':
        fields = re.findall(r'^\s+(\w+) : (.+?)\s*$', d['code'], re.M)
        if fields and len(fields) == len([l for l in d['code'].splitlines()[1:] if l.strip()]):
            groups = []
            for f, ty in fields:
                if groups and groups[-1][1] == ty:
                    groups[-1][0].append(f)
                else:
                    groups.append(([f], ty))
            return 'structure P where  ' + '; '.join(f'({" ".join(fs)} : {ty})' for fs, ty in groups)
    return d['text']


def meaning(n):
    """Statements (not proofs) of the theorems that read a postcondition over Nat/Int: `X.spec`, …"""
    out = []
    for k, d in D.items():
        if d['kind'] == 'theorem' and k.rsplit('.', 1)[0] == n and \
                re.match(r'(spec|val|valid)', k.rsplit('.', 1)[1]) and d['file'].startswith('Tom/Spec/'):
            sig = d['text'][d['off']:d['off'] + len(signature(d['code']))].rstrip()
            out.append(f'{sig} := …  -- proved in {d["file"]}')
    return out


def verbatim(names, printed, where):
    """The definitions as a comment block; ones printed earlier are named only."""
    out, again, cur = [], [], None
    for n in names:
        if n in printed:
            again.append(n); continue
        printed[n] = where
        d = D[n]
        if d['file'] != cur:
            cur = d['file']
            out.append(f'-- {cur}')
        out.append(render(n))
        out += meaning(n)
        out.append('')
    if again:
        out.append('Also used (printed above): ' + ', '.join(
            f'`{n}` ({printed[n]})' for n in again))
    body = '\n'.join(out).rstrip()
    return body

# ---------------------------------------------------------------- inputs

code = open('Tom/Machine/Code.lean', encoding='utf-8').read()
FUNCS = [f for f, _, _ in re.findall(r'/-- `([^`]+)`: (\d+) instructions at \[0x([0-9a-f]+)', code)]
TOM = sorted(f for f in FUNCS if f.startswith(('mp_', 's_mp_')))
LIB = [f for f in FUNCS if f not in TOM]

hdr = open('vendor/libtommath/tommath.h').read() + open('vendor/libtommath/tommath_private.h').read()
def proto(f):
    m = re.search(r'^(?:MP_PRIVATE\s+)?([\w ]+?[ *]' + re.escape(f) + r'\([^;]*\))[^;]*;', hdr, re.M)
    return ' '.join(m.group(1).split()) + ';' if m else f

notes = {}
for row in open('experiments/coverage_map.tsv', encoding='utf-8'):
    if row.startswith('#') or not row.strip():
        continue
    f, thm, how = row.rstrip('\n').split('\t')[:3]
    notes.setdefault(f, []).append(how)

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
for name, *_ in [x for v in forms.values() for x in v] + [x[1:] for x in lib_forms]:
    pass

def head(term):
    return re.sub(r'\.[12]$', '', term.split()[0])

for f, fs in list(forms.items()) + [(' '.join(x[0]), [x[1:]]) for x in lib_forms]:
    for name, stmt, proof in fs:
        for t in ([] if stmt == '-' else [stmt.replace('∀ n, ', '').split()[0]]) + [head(p) for p in proof.split()]:
            if head(t) not in D:
                sys.exit(f'gen_specs: {f}: unknown name {t}')

# ---------------------------------------------------------------- output

def restate(thm, name):
    """A theorem re-stated under `Specs.name` in its own namespace and opens, proof by application."""
    d = D[thm]
    code = d['code']
    sig = d['text'][d['off']:d['off'] + len(signature(code))].rstrip()
    sig = re.sub(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+)?theorem\s+\S+', '', sig, count=1)
    doc = d['text'][:d['off']].strip()
    ns = '.'.join(d['ns'])
    out = [f'namespace {ns}'] + d['opens']
    out.append(doc if doc else f'/-- {title(d["file"])} -/')
    out.append(f'theorem _root_.Specs.{name}{sig} :=')
    out.append(f'  {thm} {" ".join(binders(" ".join(signature(code).split()[2:])))}'.rstrip())
    out.append(f'end {ns}')
    return out


def binders(sig):
    """Explicit binder names of a theorem signature `name binders : type`."""
    s = sig.split(None, 2)[2] if sig.startswith('theorem') else sig
    names, i = [], 0
    while i < len(s):
        if s[i].isspace():
            i += 1; continue
        if s[i] not in '({[⦃':
            break
        close = {'(': ')', '{': '}', '[': ']', '⦃': '⦄'}[s[i]]
        depth, j = 0, i
        while j < len(s):
            if s[j] in '({[⦃': depth += 1
            elif s[j] in ')}]⦄':
                depth -= 1
                if depth == 0: break
            j += 1
        if s[i] == '(':
            names += s[i + 1:j].split(':')[0].split()
        i = j + 1
    return names


imports, printed, sections = set(), {}, []

def form_block(fn, name, stmt, proof, primary):
    out = []
    if stmt == '-':
        thm = head(proof)
        d = D[thm]
        imports.add(d['file'])
        out += restate(thm, name)
        roots, files = [thm], {d['file']}
        defs = closure(roots, files, sig_only_first=True)
        summary = ''
    else:
        sname = stmt.replace('∀ n, ', '').split()[0]
        d = D[sname]
        for p in proof.split():
            imports.add(D[head(p)]['file'])
        doc = title(d['file'])
        out.append(f'/-- {doc} -/' if doc else '')
        out.append(f'theorem Specs.{name} : {stmt} :=')
        out.append(f'  {proof}')
        roots, files = [sname], {d['file']}
        defs = [sname] + closure(roots, files)
        summary = plumbing(sname) if d['file'].startswith('Tom/Machine/Api/') else ''
    block = verbatim(defs, printed, f'`{fn}`')
    text = []
    if summary:
        text.append('Machine plumbing: ' + summary + '.')
    if block:
        text.append(block)
    if text:
        out.append('/-\n' + '\n\n'.join(text) + '\n-/')
    return '\n'.join(x for x in out if x != '') + '\n'


def section(fn):
    out = [f'/-! ## `{fn}`\n\n`{proto(fn)}`']
    if fn in notes:
        out[0] += '\n\n' + '\n'.join(f'Coverage: {n}.' for n in notes[fn])
    out[0] += '\n-/\n'
    for k, (name, stmt, proof) in enumerate(forms[fn]):
        out.append(form_block(fn, name, stmt, proof, k == 0))
    return '\n'.join(out)


INTRO = '''/-!
# The specifications of libtommath v1.3.0 on RV64I, for review

Generated by `scripts/gen_specs.py` from `experiments/specs.tsv` and the Lean sources; do not edit.
Every theorem below is proved (its proof is the machine proof, named after `:=`), and
`#print axioms` on it shows only `propext`, `Classical.choice` and `Quot.sound`.

For each libtommath function of `c/tommath-arith.elf` (alphabetical): its C prototype, every proved
form of its contract (the most general first: growing destinations, then the forms that assume
the destination has room, called D5 in the sources, then aliasing variants), and the definitions
the statement is made of, copied verbatim from the sources. The newlib/libgcc routines the
functions reach are in the appendix.

## How to read a contract

A contract is a total-correctness `Triple` over the Sail RISC-V model: from every machine state
`At entry …` (the pc at the function's entry, the argument registers, memory `m`), some finite run
reaches a state `At ra …` (returned to the caller) whose memory `M` satisfies the postcondition.
Its parameters `p : P` name the `mp_int`s involved (`p.a`, `p.b`, …, as `MpInt` values: `used`,
`alloc`, `sign` and the digit array) and where they are in memory. A contract `Statement` reads:

    ∀ p m …, ra aligned → Res p →                      -- what the caller must provide
      Sound (lay p) isW → Bundle (lay p) (kind p) m →  -- the regions are disjoint and hold p's mp_ints
      AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) → -- the allocator's heap, regions off its blocks
      Triple (At entry (args p) m …)
        (fun cf => ∃ x M, At ra (rets p x ra) M … cf ∧ Q p x ∧   -- the result x satisfies Q
                         HPost (lay p) ws site (out p x) … m M)  -- only the written regions changed

Most allocating contracts state exactly this (`def Statement : Prop :=` in the sources); below,
`Standard.Statement Res Q (site .s)` abbreviates that verbatim text with the site `.s`:

    ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
      Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
      Triple (At entry ((1, ra) :: args p) m v.keep outp)
        (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
          HPost (lay p) ws .s (out p x) (site' p x) (hin p) (hout p x) m M)

`Res` (or `Pre`) is the precondition: validity of the operands (`MpInt.Valid`), the C's `int`
arithmetic bounds, the stack. `Q` (or `Post`) is the arithmetic postcondition, stated with the
`Tom/Spec` definitions (for `mp_add`: the result's `val` is `val a + val b`). The machine plumbing
(the stack reservation, the register map, the regions) is summarised in one line per contract.
-/
'''


def common():
    out = ['/-! ## The common vocabulary\n\n`MpInt` is the `mp_int` struct with its digit array read as a list; `mag` and `val`\n'
           'its magnitude (`Nat`) and value (`Int`); `Shape`/`Valid` the representation invariants;\n'
           '`ShapeU`/`ValidU` the same with the digits at and above `used` unconstrained. `Triple` is\n'
           'total correctness on the machine, `At` a machine state at a pc with registers and memory.\n-/\n']
    for n in COMMON:
        printed[n] = 'the common vocabulary'
    block = []
    cur = None
    for n in COMMON:
        d = D[n]
        if d['file'] != cur:
            cur = d['file']; block.append(f'-- {cur}')
        block.append(d['text']); block.append('')
    out.append('/-\n' + '\n'.join(block).rstrip() + '\n-/\n')
    imports.update(D[n]['file'] for n in COMMON)
    return '\n'.join(out)


def appendix():
    out = ['/-! ## Appendix: the newlib and libgcc routines\n\nThe allocator (newlib\'s dlmalloc, '
           'with its locks and `sbrk`), `memset`/`memcpy`/`memmove` and libgcc\'s 64-bit multiply and '
           'divide, as the libtommath functions call them. Each theorem covers the routines listed with it '
           '(callees run inside the proof of their caller).\n-/\n']
    for fs, name, stmt, proof in lib_forms:
        out.append(f'-- {", ".join(fs)}')
        if stmt == '-':
            thm = head(proof); d = D[thm]
            imports.add(d['file'])
            out += restate(thm, name) + ['']
        else:
            for p in proof.split():
                imports.add(D[head(p)]['file'])
            out.append(f'theorem Specs.{name} : {stmt} :=\n  {proof}\n')
    return '\n'.join(out)


body = [common()]
for fn in TOM:
    body.append(section(fn))
body.append(appendix())
mods = sorted(f[:-5].replace('/', '.') for f in imports)
text = '\n'.join(f'import {m}' for m in mods) + '\n\n' + INTRO + '\n' + '\n'.join(body)
text = re.sub(r'\n{3,}', '\n\n', text)

if '--check' in sys.argv:
    old = open(OUT, encoding='utf-8').read() if os.path.exists(OUT) else ''
    sys.exit(0 if old == text else f'gen_specs: {OUT} is not what scripts/gen_specs.py generates')
open(OUT, 'w', encoding='utf-8').write(text)
print(f'gen_specs: {len(TOM)} functions, {sum(len(v) for v in forms.values())} forms, '
      f'{len(LIB)} library routines -> {OUT} ({text.count(chr(10))} lines)')
