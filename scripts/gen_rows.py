#!/usr/bin/env python3
"""
    Python3 scripts/gen_rows.py experiments/segs/<src>.rows.json [--out DIR]

One annotation file per function. It holds what a segment's chain does not fix: the register lists at the cut points, the fact records, the
guards and bounds, and one row per segment naming its path. From it the
generator writes
  * experiments/segs/<src>.json (the chains) and, through scripts/gen_segs.py,
    Tom/Machine/Seg/<Mod>.lean;
  * Tom/Machine/Fn/<Mod>.lean: the register-list defs, the fact structures and
    one `theorem <row>_step` per row, proved by `seg_ctx` + `seg_go`
    (Tom/Machine/Kit/Gen.lean).
Both outputs are generated: change the annotation and regenerate.

Annotation (JSON object):
  fn, mod, src, pfx      C name, Lean module stem, chain-file stem, chain-name prefix
  imports                extra imports of the Fn module (optional)
  opens                  namespaces opened in the Fn module (optional): scoped `seg_val` sets
  bv, nat                the variables, by type (BitVec 64 / Nat), space separated
  keep                   the registers the function never writes (ABI names) or a
                         Lean GRegs term over `v : Abi`; the post keeps them
  regs                   {name: "r:val r:val …"}: a register list. `r` an ABI name;
                         `val` a Nat expression (pinned as `BitVec.ofNat 64 (val)`),
                         a BitVec variable, or `!term` (a raw BitVec term). `r`
                         alone means `r:r`. `@other` first copies list `other`;
                         `-r` drops `r`.
  facts                  {name: ["field: Prop", …]}: a fact structure (`field:` optional)
  segs                   rows: {n, at, to?, pre, post, h?, st?, lds?, eqs?, by?, doc?}
     at   "PC D…"        the start pc (hex, `0x8000` prefix optional) and the branch
                         decisions met on the path, in order (T taken / F not)
     to   "PC"           stop at PC (else at the first call, return or
                         instruction the evaluator lacks)
     pre, post           a register list: `name`, `name{x:=e, …}` (its own
                         parameters, some replaced) or a Lean application
     h                   hypotheses: a fact name (own parameters), `name{…}`, or a Prop
     st                  values of the stores the generator cannot evaluate, in order
     eqs, by             extra simp lemmas for the value goals; a closer for what is left
     alu                 one instruction by Kit/Alu1.lean instead of a chain: `sra`, `sltu`,
                         `snez`, `seqz`, `sltiu` (checked against the disassembly); `at` its pc,
                         pre/post lists, `h`, `eqs` as above (see `alu_row`)
Templates (only in a file with "let" or "families", so every other rows
file reads as before; `load_rows`, also used by gen_asm.py):
  let                    {W: text | list}: `{W}` in any text or key is replaced (repeatedly); a
                         text that is exactly "{W}" with W a list is that list; a list element that
                         is exactly "{W}" (W a list, or a text naming one) splices it, expanded where
                         it is spliced (a family member's words bound). `{x:=e}` is not a word.
  families               {f: {member: {W: text | list}}}: a `regs`/`facts` key naming `{f}` is one
                         copy per member; a list element {"family": f, "each": [items]} is the items
                         once per member (in member order), `{f}` the member's name, its words bound.
                         Top-level keys `#…` are comments.
Checks before Lean runs: every source register pinned, keep registers not
written, the post's registers pinned, load and store addresses known, row names
unique, and no row that reloads an address it stored and then branches
(r6d: `seg_go` ran out of memory): the message names the pc to stop the row at
(`"to"`, the instruction after the store); `"reload_ok": true` overrides.
"""
import json, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

ABI = {n: i for i, n in enumerate(
    'zero ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6'.split())}
ABI['fp'] = 8
KEEPV = {3: 'v.gp', 4: 'v.tp', 8: 'v.s0', 2: 'v.sp', 9: 'v.s.s1'}
for k in range(2, 12):
    KEEPV[ABI[f's{k}']] = f'v.s.s{k}'


def die(msg):
    sys.exit(f'gen_rows: {msg}')


def sext(v, b):
    return v - (1 << b) if v >> (b - 1) & 1 else v


def load_disasm():
    W = {}
    for l in open(os.path.join(ROOT, 'experiments/disasm.txt')):
        m = re.match(r'^\s+([0-9a-f]+):\t([0-9a-f]{8})\s+\t(.*)$', l)
        if m:
            W[int(m.group(1), 16)] = (int(m.group(2), 16), m.group(3).strip())
    return W


def dec(pc, w):
    """(kind, info): kinds alu, load, store, br, j, call, jr, bad."""
    op, rd, f3 = w & 0x7f, (w >> 7) & 31, (w >> 12) & 7
    rs1, rs2, f7 = (w >> 15) & 31, (w >> 20) & 31, w >> 25
    ii = sext(w >> 20, 12)
    si = sext(((w >> 25) << 5) | ((w >> 7) & 31), 12)
    if op == 0x03:
        wd = {0: None, 1: None, 2: (4, 'lw'), 3: (8, 'ld'), 4: (1, 'lbu'), 5: None, 6: (4, 'lwu')}[f3]
        if wd is None:
            return 'bad', {}
        return 'load', dict(rd=rd, rs1=rs1, imm=ii, w=wd[0], m=wd[1])
    if op == 0x23:
        return 'store', dict(rs1=rs1, rs2=rs2, imm=si, w={0: 1, 1: 2, 2: 4, 3: 8}[f3])
    if op == 0x63:
        b = sext(((w >> 31) & 1) << 12 | ((w >> 7) & 1) << 11 | ((w >> 25) & 0x3f) << 5 | ((w >> 8) & 0xf) << 1, 13)
        return 'br', dict(tgt=pc + b, rs=[rs1, rs2])
    if op == 0x6f:
        j = sext(((w >> 31) & 1) << 20 | ((w >> 12) & 0xff) << 12 | ((w >> 20) & 1) << 11 | ((w >> 21) & 0x3ff) << 1, 21)
        return ('j' if rd == 0 else 'call'), dict(tgt=pc + j, rd=rd)
    if op == 0x67:
        return 'jr', dict(rs=[rs1], rd=rd)
    if op == 0x13:
        if f3 == 3:
            return 'bad', {}
        name = {0: 'addi', 1: 'slli', 2: 'slti', 4: 'xori', 5: 'srli', 6: 'ori', 7: 'andi'}[f3]
        return 'alu', dict(rd=rd, rs=[rs1], op=name, imm=ii)
    if op == 0x1b:
        return 'alu', dict(rd=rd, rs=[rs1], op='w', imm=ii)
    if op in (0x33, 0x3b):
        if f7 == 1:
            return 'bad', {}
        if op == 0x33 and (f3 == 3 or (f3 == 5 and f7 == 0x20)):
            return 'bad', {}
        name = 'add' if (op, f3, f7) == (0x33, 0, 0) else 'r'
        return 'alu', dict(rd=rd, rs=[rs1, rs2], op=name)
    if op == 0x37:
        return 'alu', dict(rd=rd, rs=[], op='lui', imm=sext(w & 0xfffff000, 32))
    if op == 0x17:
        return 'alu', dict(rd=rd, rs=[], op='auipc', imm=sext(w & 0xfffff000, 32))
    return 'bad', {}


# ---- symbolic values: ('n', base, off) = BitVec.ofNat 64 (base + off); ('b', term); None


def split_aff(s):
    s = s.strip()
    m = re.match(r'^(.*\S)\s*([+-])\s*(\d+|0x[0-9a-fA-F]+)$', s)
    if m and balanced(m.group(1)):
        b, o = split_aff(m.group(1))
        k = int(m.group(3), 0)
        return b, o + (k if m.group(2) == '+' else -k)
    if re.match(r'^(\d+|0x[0-9a-fA-F]+)$', s):
        return None, int(s, 0)
    return s, 0


def pc_of(s):
    """A pc as the annotations write it: hex with or without `0x`, the image's `0x8000…` prefix
    optional at any length (`1f80`, `608` and `0608` are `0x80001f80`, `0x80000608`; a
    three-digit pc was read as `0x88000608`)."""
    v = int(s.strip(), 16)
    return v if v >= 0x80000000 else v + 0x80000000


def balanced(s):
    d = 0
    for ch in s:
        d += ch == '('
        d -= ch == ')'
        if d < 0:
            return False
    return d == 0


def render(b, o):
    if b is None:
        return str(o) if o < 4096 else hex(o)
    if o == 0:
        return b
    return f'{b} + {o}' if o > 0 else f'{b} - {-o}'


def spaced(s):
    """Spaces around `*`, `+`, `-` (`4*ix` would lex as Sail's `*i`)."""
    if s.startswith('!'):
        return s
    return re.sub(r'\s*([*+-])\s*', r' \1 ', s).strip()


def paren(s):
    return s if re.match(r'^[\w.]+$', s) or (s.startswith('(') and s.endswith(')') and balanced(s[1:-1])) else f'({s})'


class Fn:
    def __init__(self, ann):
        self.a = ann
        self.bv = ann.get('bv', '').split()
        self.nat = ann.get('nat', '').split()
        self.vars = self.bv + self.nat
        self.W = load_disasm()
        self.regs = {}      # name -> list of (regno, kind, text)
        for name, spec in ann.get('regs', {}).items():
            self.regs[name] = self.parse_regs(spec)
        self.facts = {}
        for name, fields in ann.get('facts', {}).items():
            self.facts[name] = [self.field(i, f) for i, f in enumerate(fields)]
        self.keep_keys, self.keep_term, self.keep_def = self.parse_keep(ann.get('keep', ''))

    # -- annotation pieces
    def parse_regs(self, spec):
        out = {}
        for tok in re.findall(r'(?:[^\s"]|"[^"]*")+', spec) if False else self.toks(spec):
            if tok.startswith('@'):
                for k, v in self.regs[tok[1:]].items():
                    out[k] = v
                continue
            if tok.startswith('-'):
                out.pop(ABI[tok[1:]], None)
                continue
            r, _, val = tok.partition(':')
            if r not in ABI:
                die(f'unknown register {r!r} in {spec!r}')
            if not val:
                val = r
            out[ABI[r]] = spaced(val)
        return dict(sorted(out.items()))

    @staticmethod
    def toks(spec):
        """Split on spaces outside parentheses."""
        out, cur, d = [], '', 0
        for ch in spec:
            if ch == ' ' and d == 0:
                if cur:
                    out.append(cur)
                cur = ''
                continue
            d += ch == '('
            d -= ch == ')'
            cur += ch
        if cur:
            out.append(cur)
        return out

    def field(self, i, f):
        m = re.match(r'^(\w+)\s*:\s+(.*)$', f)
        return (m.group(1), spaced(m.group(2))) if m else (f'f{i}', spaced(f))

    def parse_keep(self, k):
        regs = [ABI[t] for t in k.split()]
        regs.sort()
        body = ', '.join(f'({r}, {KEEPV[r]})' for r in regs)
        return regs, '(kp v)', f'def kp (v : Abi) : GRegs := [{body}]'

    def is_bv(self, val):
        return val in self.bv

    def pin(self, val):
        if val.startswith('!'):
            return val[1:]
        if self.is_bv(val):
            return val
        return f'BitVec.ofNat 64 {paren(val)}'

    def idents(self, s):
        out = []
        for t in re.findall(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_0-9']+)*", s):
            t = t.split('.')[0]
            if t in self.vars and t not in out:
                out.append(t)
        return out

    def params(self, texts):
        used = set()
        for s in texts:
            used.update(self.idents(s))
        return [v for v in self.vars if v in used]

    def binders(self, ps, mem=False):
        b = [x for x in ps if x in self.bv]
        n = [x for x in ps if x in self.nat]
        out = ['(M : Mem)'] if mem else []
        if b:
            out.append(f'({" ".join(b)} : BitVec 64)')
        if n:
            out.append(f'({" ".join(n)} : Nat)')
        return ' '.join(out)

    def reg_params(self, name):
        return self.params(self.regs[name].values())

    def fact_params(self, name):
        return self.params([p for _, p in self.facts[name]])

    def fact_mem(self, name):
        return any(re.search(r'\bM\b', p) for _, p in self.facts[name])

    def apply(self, spec, kind):
        """`name`, `name{x:=e,…}` or a Lean term; returns (term, head name or None)."""
        spec = spec.strip()
        m = re.match(r'^(\w+)(\{(.*)\})?$', spec)
        tbl = self.regs if kind == 'regs' else self.facts
        if m and m.group(1) in tbl:
            name = m.group(1)
            sub = {}
            if m.group(3):
                for part in split_top(m.group(3), ','):
                    x, _, e = part.partition(':=')
                    sub[x.strip()] = spaced(e.strip())
            ps = self.reg_params(name) if kind == 'regs' else self.fact_params(name)
            args = [paren(sub.get(p, p)) for p in ps]
            if kind == 'facts' and self.fact_mem(name):
                args = ['M'] + args
            return ' '.join([name] + args), name
        return spaced(spec), None

    def reg_values(self, spec):
        """The register list a pre/post spec denotes, as {regno: val text} with substitution."""
        spec = spec.strip()
        m = re.match(r'^(\w+)(\{(.*)\})?$', spec)
        if not m or m.group(1) not in self.regs:
            die(f'pre/post must name a register list: {spec!r}')
        sub = {}
        if m.group(3):
            for part in split_top(m.group(3), ','):
                x, _, e = part.partition(':=')
                sub[x.strip()] = spaced(e.strip())
        out = {}
        for r, val in self.regs[m.group(1)].items():
            out[r] = substitute(val, sub)
        return out

    # -- the chain
    def walk(self, row):
        at = row['at'].split()
        pc = pc_of(at[0])
        ds = list(at[1:])
        to = row.get('to')
        stop = None
        if to:
            stop = pc_of(to)
        blocks, cur, n, path = [], pc, 0, []
        p = pc
        end = None
        while True:
            if n > 0 and stop is not None and p == stop:
                blocks.append((cur, p, None))
                end = p
                break
            if p not in self.W:
                die(f'{row["n"]}: pc {p:x} not in the image')
            w, txt = self.W[p]
            k, info = dec(p, w)
            if k in ('call', 'bad'):
                if stop is not None and p != stop:
                    die(f'{row["n"]}: reached {txt} at {p:x} before {stop:x}')
                blocks.append((cur, p, None))
                end = p
                break
            path.append((p, k, info))
            n += 1
            if k == 'br':
                if not ds:
                    die(f'{row["n"]}: no decision for the branch at {p:x} ({txt})')
                t = ds.pop(0) == 'T'
                blocks.append((cur, p, ('br', t)))
                info['taken'] = t
                p = info['tgt'] if t else p + 4
                cur = p
            elif k == 'j':
                blocks.append((cur, p, 'j'))
                p = info['tgt']
                cur = p
            elif k == 'jr':
                blocks.append((cur, p, 'jr'))
                end = 'jr'
                break
            else:
                p += 4
            if n > 200:
                die(f'{row["n"]}: path too long')
        if ds:
            die(f'{row["n"]}: unused decisions {ds}')
        return blocks, end, path

    def evaluate(self, row, pre, path):
        """Symbolic run: lds, the write log, the written registers. A load of an address the row
        stored before, followed by a branch, is rejected (r6d: `seg_go` ran out of memory on such
        a row): the message names the pc to cut at (`"to"`); `"reload_ok": true` overrides."""
        self._stored, self._reload = {}, None
        st = {}
        for r, val in pre.items():
            if val.startswith('!'):
                st[r] = ('b', val[1:])
            elif self.is_bv(val):
                st[r] = ('b', val)
            else:
                b, o = split_aff(val)
                st[r] = ('n', b, o)
        keys = set(pre)
        written = set()
        lds, log = [], []
        # "st": one value per store, in order ("_" takes the value the walk knows);
        # "stu": values for the stores whose value the walk does not know, in order
        stv = list(row.get('st', []))
        stu = list(row.get('stu', []))
        keep = set(self.keep_keys)

        def src(r, p):
            if r != 0 and r not in keys:
                die(f'{row["n"]}: x{r} read at {p:x} is not pinned')
            return ('n', None, 0) if r == 0 else st.get(r)

        def addr(r, imm, p, what):
            v = src(r, p)
            if not v or v[0] != 'n':
                die(f'{row["n"]}: the {what} address at {p:x} is not known (cut before it, or pin its base)')
            return render(v[1], v[2] + imm)

        for p, k, info in path:
            if k in ('br', 'jr'):
                for r in info['rs']:
                    src(r, p)
                if k == 'jr' and info['rd'] != 0:
                    die(f'{row["n"]}: jalr with a link at {p:x}')
                continue
            if k == 'j':
                continue
            if k == 'load':
                a = addr(info['rs1'], info['imm'], p, 'load')
                if a in self._stored and not row.get('reload_ok'):
                    self._reload = (p, a, self._stored[a])
                lds.append(f'rd{info["w"]} M ({a})')
                rd, val = info['rd'], None
            elif k == 'store':
                a = addr(info['rs1'], info['imm'], p, 'store')
                v = src(info['rs2'], p)
                given = stv.pop(0) if stv else None
                if given == '_':
                    given = None
                if given is not None:
                    vt = self.pin(spaced(given))
                elif v and v[0] == 'n':
                    vt = f'BitVec.ofNat 64 {paren(render(v[1], v[2]))}'
                elif v and v[0] == 'b':
                    vt = v[1]
                elif stu:
                    vt = self.pin(spaced(stu.pop(0)))
                else:
                    die(f'{row["n"]}: the value stored at {p:x} is not known: give it in "stu" (or "st")')
                log.append(f'({a}, {info["w"]}, {vt})')
                self._stored.setdefault(a, p)
                continue
            else:
                rd = info['rd']
                vs = [src(r, p) for r in info['rs']]
                val = None
                o = info['op']
                if o == 'addi' and vs[0] and vs[0][0] == 'n':
                    val = ('n', vs[0][1], vs[0][2] + info['imm'])
                elif o == 'lui' and info['imm'] >= 0:
                    val = ('n', None, info['imm'])
                elif o == 'auipc':
                    val = ('n', None, p + info['imm'])
                elif o == 'add' and vs[0] and vs[1] and vs[0][0] == 'n' and vs[1][0] == 'n':
                    if vs[0][1] is None:
                        val = ('n', vs[1][1], vs[1][2] + vs[0][2])
                    elif vs[1][1] is None:
                        val = ('n', vs[0][1], vs[0][2] + vs[1][2])
            if rd == 0:
                continue
            if rd in keep:
                die(f'{row["n"]}: writes kept register x{rd} at {p:x}')
            st[rd] = val
            keys.add(rd)
            written.add(rd)
        if stv or stu:
            die(f'{row["n"]}: unused "st"/"stu" values')
        if self._reload:
            lp, a, sp_ = self._reload
            i = [q for q, _, _ in path].index(lp)
            if any(k == 'br' for _, k, _ in path[i + 1:]):
                die(f'{row["n"]}: reloads {a} (stored at {sp_:x}) at {lp:x} and branches after: '
                    f'split the row after the store ("to": "{sp_ + 4:x}"), or set "reload_ok": true')
        return lds, log, keys


# One-instruction ALU rows (`"alu"`), by `Kit/Alu1.lean`: the lemma, the register operands it
# names, and (for `snez`/`seqz`) the lemma turning the written `if` into an `ofNat` pin.
ALU1 = {
    'sra': dict(lem='sra_at', ops=('rd', 'rs1', 'rs2'), txt='sra'),
    'sltu': dict(lem='sltu_at', ops=('rd', 'rs1', 'rs2'), txt='sltu'),
    'slt': dict(lem='slt_at', ops=('rd', 'rs1', 'rs2'), txt='slt'),        # Kit/Alu1S.lean
    'snez': dict(lem='snez_at', ops=('rd', 'rs2'), txt='snez', src='rs2', ite='BitW.ite_ofNat_ne_zero'),
    'seqz': dict(lem='seqz_at', ops=('rd', 'rs1'), txt='seqz', src='rs1', ite='ite_ofNat_eq_zero'),
    'sltiu': dict(lem='sltiu_at', ops=('rd', 'rs1'), txt='sltiu', imm=True),
}


def alu_row(self, row, base, code):
    """One instruction the chain evaluator lacks (`sra`, `sltu`, `snez`, `seqz`, `sltiu`), by
    `Kit/Alu1.lean`; `slt` by `Kit/Alu1S.lean` (import it; its value on `ofNat` words: `slt_ofNat` in `eqs`). For `snez`/`seqz` on a source pinned to a Nat value `x` the written value
    is rewritten to `BitVec.ofNat 64 (if x = 0 then …)` (needs `x < 2 ^ 64` from `h` by `omega`);
    give it in the post as `name{e:=if x = 0 then 0 else 1}` (`snez` uses `BitW.ite_ofNat_ne_zero`:
    import `Tom.Machine.Kit.BitW`). Other values: `eqs`."""
    pc = pc_of(row['at'].split()[0])
    w, txt = self.W[pc]
    rd, rs1, rs2 = (w >> 7) & 31, (w >> 15) & 31, (w >> 20) & 31
    if row['alu'] not in ALU1:
        die(f'{row["n"]}: alu {row["alu"]!r}: one of {", ".join(ALU1)}')
    A = ALU1[row['alu']]
    if txt.split()[0] != A['txt']:
        die(f'{row["n"]}: the word at {pc:x} is `{txt}`, not `{A["txt"]}`')
    lem = A['lem']
    regno = dict(rd=rd, rs1=rs1, rs2=rs2)
    pre_t, pre_d = self.apply(row['pre'], 'regs')
    post_t, post_d = self.apply(row['post'], 'regs')
    hyps = [(f'h{i}', self.apply(h, 'facts')[0]) for i, h in enumerate(row.get('h', []))]
    ps = self.params([pre_t, post_t] + [t for _, t in hyps])
    bvs = [x for x in ps if x in self.bv]
    nats = [x for x in ps if x in self.nat]
    bind = []
    if bvs:
        bind.append(f'({" ".join(bvs)} : BitVec 64)')
    bind.append('(v : Abi) (outp : Array String)')
    if nats:
        bind.append(f'({" ".join(nats)} : Nat)')
    bind.append('(M : Mem)')
    bind.append(f'(hc : CodeAt M {base} {code})')
    bind += [f'({n} : {t})' for n, t in hyps]
    P, P4 = f'0x{pc:x}#64', f'0x{pc + 4:x}#64'
    ex = ', '.join([pre_d, post_d] + row.get('eqs', []))
    named = ' '.join(f'({o} := {regno[o]})' for o in A['ops'])
    if A.get('imm'):
        named += f' (imm := 0x{(w >> 20) & 0xfff:x}#12)'
    srcs = []
    for o in A['ops'][1:]:
        if regno[o] == 0:
            srcs.append('(Or.inl rfl) (by decide)')
        else:
            srcs.append(f'(Or.inr (by simp [keysG, {pre_d}])) (by decide)')
    lines = []
    if row.get('doc'):
        lines.append(f'/-- {row["doc"]} -/')
    lines += [f'theorem {row["n"]}_step {" ".join(bind)} :',
              f'    Triple (At {P} ({pre_t}) M {self.keep_term} outp)',
              f'      (At {P4} ({post_t}) M {self.keep_term} outp) := by',
              f'  have h := {lem} (pc := {P}) (w := 0x{w:08x}#32) {named}',
              f'    (L := {pre_t}) (keep := {self.keep_term}) (outp := outp)',
              f'    (hc.word (a := ({P} : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)',
              f'    (fun s h1 h2 h3 => decodeW s h1 h2 h3) ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩',
              f'    (by decide) {" ".join(srcs)}',
              f'    (by simp [keysG, {pre_d}]) (by simp [kp, keysG]) (by simp [kp, keysG])',
              f'  rw [show Sail.BitVec.addInt ({P} : BitVec 64) 4 = {P4} by decide] at h']
    if A.get('ite'):
        rs = regno[A['src']]
        val = self.reg_values(row['pre']).get(rs)
        if val is not None and not val.startswith('!') and not self.is_bv(val):
            lines.append(f'  rw [show srcVal {rs} ({pre_t}) = {self.pin(val)} from by simp [srcVal, lookupG, {pre_d}],')
            lines.append(f'    {A["ite"]} (by omega)] at h')
    lines.append(f'  exact Triple.rmap (fun _ h\' => At.weakenS h\' (by simp [SubL, eraseG, lookupG, srcVal, {ex}])) h')
    return '\n'.join(lines)


Fn.alu_row = alu_row


def split_top(s, sep):
    out, cur, d = [], '', 0
    for ch in s:
        if ch == sep and d == 0:
            out.append(cur)
            cur = ''
            continue
        d += ch in '([{'
        d -= ch in ')]}'
        cur += ch
    out.append(cur)
    return [x for x in out if x.strip()]


def substitute(s, sub):
    if not sub:
        return s
    def rep(m):
        t = m.group(0)
        return paren(sub[t]) if t in sub else t
    return re.sub(r"(?<![\w.'])[A-Za-z_][A-Za-z_0-9']*(?![\w'])", rep, s)


def code_names(fn):
    lines = open(os.path.join(ROOT, 'Tom/Machine/Code.lean')).read().splitlines()
    for i, l in enumerate(lines):
        if l.startswith(f'/-- `{fn}`:'):
            b = re.match(r'def (\w+) :', lines[i + 1]).group(1)
            c = re.match(r'def (\w+) :', lines[i + 2]).group(1)
            return b, c
    die(f'{fn} not in Tom/Machine/Code.lean')


def check_names(ann):
    """Row names are theorem names (`<n>_step`): a duplicate is rejected (r6d); a register list or
    fact named like a row variable too (grow6's gap)."""
    seen = set()
    for row in ann['segs']:
        if row['n'] in seen:
            die(f'duplicate row name {row["n"]!r}')
        seen.add(row['n'])
    # a register list or fact structure is a Lean `def`/`structure` applied inside theorems that
    # bind the row variables: one named like a variable is shadowed there — rejected
    vs = set((ann.get('bv', '') + ' ' + ann.get('nat', '')).split())
    for tbl in ('regs', 'facts'):
        for name in ann.get(tbl, {}):
            if name in vs:
                die(f'{"register" if tbl == "regs" else "fact"} list {name!r} is named like a row variable '
                    f'(the variable shadows it in the step theorems): rename it')


_TWORD = re.compile(r'\{([A-Za-z_]\w*)\}')


def _t_alias(x, env):
    """A text that is exactly `{W}`, through text aliases: the list or dict it names (or None)."""
    seen = 0
    m = _TWORD.fullmatch(x)
    while m and isinstance(env.get(m.group(1)), str) and seen < 8:
        x, seen = env[m.group(1)], seen + 1
        m = _TWORD.fullmatch(x)
    return env[m.group(1)] if m and isinstance(env.get(m.group(1)), (list, dict)) else None


def _t_str(s, env):
    for _ in range(8):
        t = _TWORD.sub(lambda m: env[m.group(1)] if isinstance(env.get(m.group(1)), str) else m.group(0), s)
        if t == s:
            break
        s = t
    return s


def _t_expand(t, env, fams):
    if isinstance(t, str):
        v = _t_alias(t, env)
        return _t_expand(v, env, fams) if v is not None else _t_str(t, env)
    if isinstance(t, list):
        out = []
        for x in t:
            if isinstance(x, str) and isinstance(_t_alias(x, env), list):
                out += _t_expand(_t_alias(x, env), env, fams)
            elif isinstance(x, dict) and set(x) == {'family', 'each'}:
                for mem, words in fams[x['family']].items():
                    out += _t_expand(x['each'], dict(env, **words, **{x['family']: mem}), fams)
            else:
                out.append(_t_expand(x, env, fams))
        return out
    if isinstance(t, dict):
        out = {}
        for k, v in t.items():
            fs = [f for f in _TWORD.findall(k) if f in fams and f not in env]
            if not fs:
                out[_t_str(k, env)] = _t_expand(v, env, fams)
                continue
            for mem, words in fams[fs[0]].items():
                out.update(_t_expand({k: v}, dict(env, **words, **{fs[0]: mem}), fams))
        return out
    return t


def load_rows(path):
    """A rows annotation as the generator reads it: its templates ("let", "families") expanded, the frame
    facts defaulted (`frame_defaults`)."""
    ann = json.load(open(path))
    if 'let' not in ann and 'families' not in ann:
        return frame_defaults(ann)
    fams = ann.pop('families', {})
    env = ann.pop('let', {})
    return frame_defaults(_t_expand({k: v for k, v in ann.items() if not k.startswith('#')}, env, fams))   # `#…`: comments


def frame_defaults(ann):
    """ Without a fact structure `FF`, it is the
    function's frame `F` (its entry `addi sp, sp, -F`): `rs: Ram (sp - F) F`, `sp % 16 = 0`, `F ≤ sp`,
    the frame off the function's code; `"h0"` (facts every row takes) defaults to `["FF"]`. `"frame": false`:
    no frame facts (rows that never take them)."""
    if ann.get('frame') is False:
        return ann
    facts = ann.setdefault('facts', {})
    if 'FF' not in facts:
        lines = open(os.path.join(ROOT, 'Tom/Machine/Code.lean')).read().splitlines()
        for i, l in enumerate(lines):
            m = re.match(r'/-- `' + re.escape(ann['fn']) + r'`: \d+ instructions at \[0x([0-9a-f]+), 0x([0-9a-f]+)\)', l)
            if m:
                lo, hi = int(m.group(1), 16), int(m.group(2), 16)
                base = re.match(r'def (\w+) :', lines[i + 1]).group(1)
                break
        else:
            die(f'{ann["fn"]} not in Tom/Machine/Code.lean')
        w = load_disasm()[lo][0]
        if w & 0xfffff == 0x10113 and (w >> 31):          # addi sp, sp, -F
            F = -((w >> 20) - (1 << 12))
            ann['facts'] = {'FF': [f'rs: Ram (sp - {F}) {F}', 'sp % 16 = 0', f'{F} ≤ sp',
                                   f'sp ≤ {base} ∨ {base} + {hi - lo} ≤ sp - {F}'], **facts}
    ann.setdefault('h0', ['FF'])
    return ann


def main():
    args = sys.argv[1:]
    out_dir = None
    if '--out' in args:
        i = args.index('--out')
        out_dir = args[i + 1]
        del args[i:i + 2]
    chunk = 8
    if '--chunk' in args:
        i = args.index('--chunk')
        chunk = int(args[i + 1])
        del args[i:i + 2]
    path = args[0]
    ann = load_rows(path)
    F = Fn(ann)
    check_names(ann)
    fn, mod, src, pfx = ann['fn'], ann['mod'], ann['src'], ann['pfx']
    base, code = code_names(fn)
    chains, thms = {}, []
    for row in ann['segs']:
        nm = row['n']
        cname = pfx + nm[0].upper() + nm[1:]
        if row.get('alu'):
            thms.append(F.alu_row(row, base, code))
            continue
        blocks, end, path_ = F.walk(row)
        pre = F.reg_values(row['pre'])
        post = F.reg_values(row['post'])
        lds, log, keys = F.evaluate(row, pre, path_)
        if row.get('lds') is not None:
            lds = row['lds']
        for r in post:
            if r not in keys:
                die(f'{nm}: post register x{r} is not pinned after the chain')
        if end == 'jr':
            ra = post.get(1)
            if ra is None:
                die(f'{nm}: a return needs ra in the post list')
            pc1 = F.pin(ra)
        else:
            pc1 = f'0x{end:x}#64'
        chains[cname] = [[hex(s), hex(e), (list(t) if isinstance(t, tuple) else t)] for s, e, t in blocks]
        pre_t, pre_d = F.apply(row['pre'], 'regs')
        post_t, post_d = F.apply(row['post'], 'regs')
        hyps = []
        for i, h in enumerate(([] if row.get('noh0') else ann.get('h0', [])) + row.get('h', [])):
            t, _ = F.apply(h, 'facts')
            hyps.append((f'h{i}', t))
        if end == 'jr':
            hyps.append(('hra', f'{paren(F.pin(post[1]))}.toNat % 4 = 0'))
        logt = '[' + ', '.join(log) + ']'
        if row.get('log'):
            logt = row['log']
        texts = [pre_t, post_t, logt, pc1] + [t for _, t in hyps] + lds
        ps = F.params(texts)
        bvs = [x for x in ps if x in F.bv]
        nats = [x for x in ps if x in F.nat]
        bind = []
        if bvs:
            bind.append(f'({" ".join(bvs)} : BitVec 64)')
        bind.append('(v : Abi) (outp : Array String)')
        if nats:
            bind.append(f'({" ".join(nats)} : Nat)')
        bind.append('(M : Mem)')
        bind.append(f'(hc : CodeAt M {base} {code})')
        bind += [f'({n} : {t})' for n, t in hyps]
        pc0 = pc_of(row['at'].split()[0])
        ks = '[' + ', '.join(str(k) for k in pre) + ']'
        kk = '[' + ', '.join(str(k) for k in F.keep_keys) + ']'
        ldst = '[' + ', '.join(lds) + ']' if lds else '([] : List (List (BitVec 8)))'
        ds = ', '.join(x for x in [pre_d] if x)
        pd = ', '.join(x for x in [post_d] if x)
        es = ', '.join(row.get('eqs', []))
        doc = row.get('doc')
        lines = []
        if doc:
            lines.append(f'/-- {doc} -/')
        lines.append(f'theorem {nm}_step {" ".join(bind)} :')
        lines.append(f'    Triple (At 0x{pc0:x}#64 ({pre_t}) M {F.keep_term} outp)')
        lines.append(f'      (At {pc1} ({post_t}) (writeLog M {logt}) {F.keep_term} outp) := by')
        lines.append('  seg_ctx hc')
        tail = f' using {row["by"]}' if row.get('by') else ''
        lines.append(f'  seg_go {cname} {pc1 if end == "jr" else pc1} {ldst} {ks} {kk} [{ds}] [{pd}] [{es}] hc{tail}')
        thms.append('\n'.join(lines))
    # chain file + Seg module
    cj = os.path.join(ROOT, f'experiments/segs/{src}.json')
    with open(cj, 'w') as f:
        f.write('{' + ',\n '.join(f'{json.dumps(k)}: {json.dumps(v)}' for k, v in chains.items()) + '}\n')
    if True:
        subprocess.run([sys.executable, os.path.join(ROOT, 'scripts/gen_segs.py'), src, mod], check=True, cwd=ROOT)
    # Fn module
    defs = [F.keep_def]
    for name, rl in F.regs.items():
        ps = F.reg_params(name)
        body = ', '.join(f'({r}, {F.pin(val)})' for r, val in rl.items())
        defs.append(f'def {name} {F.binders(ps)} : GRegs :=\n  [{body}]')
    for name, fields in F.facts.items():
        ps = F.fact_params(name)
        bnd = F.binders(ps, mem=F.fact_mem(name))
        body = '\n'.join(f'  {fn_} : {p}' for fn_, p in fields)
        defs.append(f'structure {name} {bnd} : Prop where\n{body}')
    imports = ['Tom.Machine.Seg.' + mod, 'Tom.Machine.Kit.Gen'] + ann.get('imports', [])
    rel = os.path.relpath(path, ROOT)
    opens = """open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg"""
    # scoped `seg_val` sets this annotation enables (Kit/WordVal.lean's `WV.Mask`, `WV.Sext`)
    for o in ann.get('opens', []):
        opens += f'\nopen {o}'

    # Segment proofs elaborate in the main thread (`Elab.async false`): run in parallel, the
    # theorems of a chunk share the large chain terms across threads, and the reference
    # counting of shared objects made a chunk cost ~15-25% more CPU for the same wall time.
    sync = '\nset_option Elab.async false\n'

    def module(imps, what, body):
        hdr = '\n'.join(f'import {i}' for i in imps)
        return f"""{hdr}

/-! Generated by scripts/gen_rows.py from {rel}: `{fn}`'s segments{what}.
Do not edit: change the annotation and regenerate. -/

namespace Tom.Machine.Fn.{mod}

{opens}
{sync if body.strip() and "theorem " in body else ""}
{body}
end Tom.Machine.Fn.{mod}
"""
    # One module per CHUNK rows (`--chunk`, default 8; 0 = one file): checking a row
    # re-checks only its chunk, and Lake builds the chunks in parallel. The umbrella
    # `Fn/<Mod>.lean` keeps the module name its importers use.
    base_dir = os.path.join(ROOT, 'Tom/Machine/Fn') if out_dir is None else out_dir
    fo = os.path.join(base_dir, f'{mod}.lean')
    sub = os.path.join(base_dir, mod)
    if os.path.isdir(sub):
        for f_ in os.listdir(sub):
            if f_.endswith('.lean'):
                os.remove(os.path.join(sub, f_))
    defs_txt = chr(10).join(d + chr(10) for d in defs)
    if chunk <= 0 or len(thms) <= chunk:
        open(fo, 'w').write(module(imports, '', defs_txt + chr(10) + (chr(10) + chr(10)).join(thms) + chr(10)))
    else:
        os.makedirs(sub, exist_ok=True)
        dm = f'Tom.Machine.Fn.{mod}.Defs'
        open(os.path.join(sub, 'Defs.lean'), 'w').write(module(imports, ' (definitions)', defs_txt))
        parts = []
        for k in range(0, len(thms), chunk):
            pn = f'P{k // chunk + 1}'
            parts.append(f'Tom.Machine.Fn.{mod}.{pn}')
            open(os.path.join(sub, f'{pn}.lean'), 'w').write(
                module([dm], f' (rows {k + 1}–{min(k + chunk, len(thms))})', (chr(10) + chr(10)).join(thms[k:k + chunk]) + chr(10)))
        open(fo, 'w').write(module([dm] + parts, ' (umbrella)', ''))
    print(f'gen_rows: {len(thms)} segments -> {os.path.relpath(fo, ROOT)}')


if __name__ == '__main__':
    main()
