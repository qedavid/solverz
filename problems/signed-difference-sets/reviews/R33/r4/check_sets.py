# Round 4: each appendix row has a Lean file with data and an objects/ file that agree in counts and params.
import re, sys, pathlib
root = pathlib.Path(sys.argv[1])
rows = [l for l in (root/'papers/P1/build/sets.tex').read_text(encoding='utf-8').splitlines() if l.startswith('N')]
sol = (root/'solutions.md').read_text(encoding='utf-8')
bad = 0
for l in rows:
    case, vkl, grp, z = [c.strip().rstrip(chr(92)).strip() for c in l.split('&')]
    v, k, lam = map(int, re.findall(r'-?\d+', vkl))
    lean = (root/f'lean/SignedDifferenceSets/Answer/{case}.lean').read_text(encoding='utf-8')
    o = re.search(r'objects/(O\d+)\.txt', lean).group(1)
    ot = (root/f'objects/{o}.txt').read_text(encoding='utf-8').splitlines()
    hdr = ot[0]; body = [x.split() for x in ot[1:] if x.strip()]
    hv = tuple(map(int, re.findall(r'-?\d+', hdr.split('(')[1])))
    npl = sum(1 for b in body if b[-1] == '+'); nmi = sum(1 for b in body if b[-1] == '-')
    m = re.search(r'def plus : ℕ := (0x[0-9a-f]+)', lean)
    if m:
        lp = bin(int(m.group(1), 16)).count('1'); lm = bin(int(re.search(r'def minus : ℕ := (0x[0-9a-f]+)', lean).group(1), 16)).count('1')
    else:
        vals = re.findall(r'-?\d+', ','.join(re.findall(r'!\[([-\d, ]+)\]', lean)))
        lp = vals.count('1'); lm = vals.count('-1')
    thm = re.search(r'theorem hasSDS :\s*HasSDS \((.*?)\) (\d+) (-?\d+)', lean)
    # solutions.md row of z mentions the case or defers to instances.csv
    zrow = [r for r in sol.splitlines() if r.startswith(f'| {z} |')][0]
    inz = re.search(rf'\b{case}\b', zrow) is not None or ('N' + case[1:]) in zrow
    ok = hv == (v, k, lam) and npl + nmi == k and (lp, lm) == (npl, nmi) and int(thm.group(2)) == k and int(thm.group(3)) == lam
    if not ok or not inz:
        bad += 1
    print(case, z, o, hdr, (npl, nmi), (lp, lm), thm.group(1), 'OK' if ok else 'BAD', 'inZ' if inz else 'NOT-IN-Z-ROW')
print('rows', len(rows), 'bad', bad)
