"""Parse the C41 rows (TomographyQuotRows/N<id>.lean) into plain parameters. Own code."""
import re, os, ast, csv, sys

ROOT = os.path.join(os.path.dirname(__file__), '..', '..', '..')
ROWS = os.path.join(ROOT, 'lean', 'SignedDifferenceSets', 'TomographyQuotRows')

def lean_list(txt):
    return ast.literal_eval(txt.replace('\n', ' '))

def parse_row(path):
    src = open(path, encoding='utf-8').read()
    r = {'file': os.path.basename(path), 'id': os.path.basename(path)[:-5]}
    m = re.search(r'theorem not_hasSDS : ¬ HasSDS \(([^)]*)\) (\d+) (-?\(?-?\d+\)?)\s*:=', src)
    r['stmt_group'] = [int(x) for x in re.findall(r'ZMod (\d+)', m.group(1))]
    r['k'] = int(m.group(2)); r['lam'] = int(m.group(3).strip('()'))
    tail = src[m.end():]
    r['nc'] = 'not_hasSDS_grp_nc' in tail
    r['ms'] = lean_list(re.search(r'\(ms := (\[[^\]]*\])\)', tail).group(1))
    r['p'] = int(re.search(r'\(ms := \[[^\]]*\]\) (\d+)', tail).group(1))
    r['A'] = lean_list(re.search(r'\(A := (\[.*?\]\])\)', tail, re.S).group(1))
    r['P'] = lean_list(re.search(r'\(P := (\[.*?\]\])\)', tail, re.S).group(1))
    r['c'] = int(re.search(r'\(c := (\d+)\)', tail).group(1))
    mt = re.search(r'\(t := (\d+)\)', tail)
    r['t'] = int(mt.group(1)) if mt else None
    mm = re.search(r'Or\.inr ⟨(\d+), (\[.*?\]), by norm_num', tail, re.S)
    r['mult'] = (int(mm.group(1)), lean_list(mm.group(2))) if mm else None
    r['closer'] = 'ptOK' if 'closes_of_ptOK' in tail else ('tomoGoL' if 'closes_of_tomoGoL' in tail else '?')
    r['lists'] = re.search(r'\((lists_\w+)', tail).group(1)
    mw = re.search(r'^def w : List \(List ℤ\) :=\s*(\[.*?\]\])\s*$', src, re.S | re.M)
    r['w'] = lean_list(mw.group(1)) if mw else None
    mv = re.search(r'^def v0 : List \(List ℤ\) :=\s*(\[.*?\]\])\s*$', src, re.S | re.M)
    r['v0'] = lean_list(mv.group(1)) if mv else None
    # numbers inside the kernel checks: (C : ℕ), k, s
    pat = (r'\(Indexed\.size \(ZMod (\d+)\)\) \(Indexed\.addIdx \(ZMod (\d+)\)\) \((\d+) \* (\d+) : ℕ\)\s*'
           r'\(\((\d+) : ℕ\) \+ \((-?\d+) : ℤ\) \* \(\((\d+) \* (\d+) : ℕ\) - 1\)\) '
           r'\(\((-?\d+) : ℤ\) \* \((\d+) \* (\d+) : ℕ\)\) \((\d+) : ℕ\) (-?\d+)')
    allm = [tuple(int(x) for x in mm.groups()) for mm in re.finditer(pat, src)]
    r['nchk'] = len(allm)
    r['chk_consistent'] = len(set(allm)) == 1
    if allm:
        g = allm[0]
        r['chk'] = dict(p=g[0], p1=g[1], c=g[2], p2=g[3], k=g[4], lam=g[5], c2=g[6], p3=g[7], lam2=g[8], c3=g[9], p4=g[10], k2=g[11], s=g[12])
    mp = re.search(r'theorem hpt : ptOK (\d+) (-?\d+) w (\d+)', src)
    r['pt'] = tuple(int(x) for x in mp.groups()) if mp else None
    mT = re.findall(r'tomoGoL (\d+) \(leafQ (\d+) (-?\d+) (\d+)\) w rows', src) + re.findall(r'tomoTopL (\d+) \(leafQ (\d+) (-?\d+) (\d+)\) w', src)
    r['leafQ'] = sorted(set(tuple(int(x) for x in t) for t in mT))
    mo = re.search(r'theorem ho : orbOK (\d+) (\d+) orb sz rep ex', src)
    r['orbOK'] = tuple(int(x) for x in mo.groups()) if mo else None
    for nm in ('orb', 'sz', 'rep', 'ex'):
        mm2 = re.search(r'^def %s : List ℕ :=\s*(\[.*?\])\s*$' % nm, src, re.S | re.M)
        r[nm] = lean_list(mm2.group(1)) if mm2 else None
    r['sorry'] = bool(re.search(r'\bsorry\b|native_decide|\baxiom\b|implemented_by|@\[extern|\bopaque\b|admit', src))
    return r

def all_rows():
    out = []
    for f in sorted(os.listdir(ROWS)):
        if f.endswith('.lean'):
            out.append(parse_row(os.path.join(ROWS, f)))
    return out

def table():
    t = {}
    with open(os.path.join(ROOT, 'instances.csv'), encoding='utf-8') as fh:
        for row in csv.DictReader(fh):
            t[row['id']] = row
    return t

if __name__ == '__main__':
    rs = all_rows()
    print(len(rs))
    for r in rs[:3]:
        print({k: v for k, v in r.items() if k not in ('w', 'v0')})
