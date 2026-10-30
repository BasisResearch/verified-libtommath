#!/usr/bin/env python3
"""Coverage of the proof image: for every function of Tom/Machine/Code.lean
(libtommath and what it calls), whether a machine contract is proved, and
where. A function counts as proved when some Tom/Machine/**/*.lean declares
`theorem correct` (or `correct_ok`/`correct_zero`, partial contracts, marked
so) in namespace `Tom.Machine.Fn.<Name>` or `Tom.Machine.Api.<Name>`.

    scripts/coverage.py            # print the table (markdown)"""
import glob, os, re
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)
code = open('Tom/Machine/Code.lean').read()
funcs = re.findall(r'/-- `([^`]+)`: (\d+) instructions at \[0x([0-9a-f]+)', code)
def camel(f):
    parts = f.strip('_').split('_')
    return ''.join(p[:1].upper() + p[1:] for p in parts if p)
proved = {}
for p in glob.glob('Tom/Machine/**/*.lean', recursive=True):
    src = open(p).read()
    ns = None
    for line in src.splitlines():
        m = re.match(r'namespace Tom\.Machine\.(?:Fn|Api)\.(\w+)', line)
        if m: ns = m.group(1)
        m = re.match(r'namespace (\w+)$', line)
        if m and ns: ns = m.group(1)
        m = re.match(r'theorem (correct\w*)\b', line)
        if m and ns:
            proved.setdefault(ns, set()).add((m.group(1), p))
        # `theorem free_correct` (namespace `Fn.Alloc`): the contract of `free`
        m = re.match(r'theorem (\w+)_correct\b', line)
        if m:
            proved.setdefault(m.group(1)[:1].upper() + m.group(1)[1:], set()).add(('correct', p))
# entry addresses of the standard contracts: `def entry … := 0x…#64` in Api/<Ns>.lean
entry_of = {}
for p in glob.glob('Tom/Machine/Api/*.lean'):
    m = re.search(r'def entry\s*:\s*BitVec 64\s*:=\s*0x([0-9a-f]+)#64', open(p).read())
    if m: entry_of[os.path.splitext(os.path.basename(p))[0]] = int(m.group(1), 16)
by_addr = {}
for ns, th in proved.items():
    if ns in entry_of: by_addr.setdefault(entry_of[ns], set()).update(th)
alias = {'MpCmpMag': 'CmpMag', 'MpClamp': 'Clamp', 'SMpAdd': 'SAdd', 'SMpSub': 'SSub',
         'HiddenUdivdi3': 'Udivdi3'}
# explicit coverage (experiments/coverage_map.tsv): a function covered by a named theorem's
# proof (a contract under another name, or code run inside a proved routine); the
# theorem must exist
src_all = '\n'.join(open(p).read() for p in glob.glob('Tom/Machine/**/*.lean', recursive=True))
cmap = {}
for row in open('experiments/coverage_map.tsv'):
    if not row.strip() or row.startswith('#'): continue
    f, thm, how = row.rstrip('\n').split('\t')[:3]
    short = thm.split('.')[-1]
    ns = thm.rsplit('.', 1)[0].split('Tom.Machine.')[-1]
    if re.search(r'theorem ' + re.escape(short) + r'\b', src_all):
        cmap[f] = (thm, how)
rows, n_full, n_part, n_ins, ins_done = [], 0, 0, 0, 0
for f, n, a in funcs:
    k = camel(f); k = alias.get(k, k)
    th = proved.get(k, set()) | by_addr.get(int(a, 16), set())
    # a map row whose "how" starts with "conditional" is a contract proved under named
    # premises not yet discharged (e.g. a recursion group's induction hypothesis): partial
    cond = f in cmap and cmap[f][1].startswith('conditional')
    full = any(t == 'correct' for t, _ in th) or (f in cmap and not cond)
    if f in cmap: th = th | {('correct' if not cond else 'cond', cmap[f][0] + ' (' + cmap[f][1] + ')')}
    st = 'proved' if full else ('partial' if th else '')
    n_ins += int(n)
    if full: n_full += 1; ins_done += int(n)
    elif th: n_part += 1
    where = ', '.join(sorted({p if ' (' in p else os.path.relpath(p) for _, p in th}))
    rows.append(f'| `{f}` | 0x{a} | {n} | {st} | {where} |')
print(f'{n_full} of {len(funcs)} functions proved ({n_part} partial); '
      f'{ins_done} of {n_ins} instructions.\n')
print('| function | address | instructions | status | proof |\n|---|---|---|---|---|')
print('\n'.join(rows))
