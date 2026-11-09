"""Check that every Row literal in FieldDescentRows.lean (both the per-row theorems and the list) matches instances.csv."""
import csv, re, sys
src = open(sys.argv[1], encoding='utf-8').read()
rows = {r['id']: r for r in csv.DictReader(open(sys.argv[2], encoding='utf-8'))}
pat = re.compile(r"⟨(\d+), \[([\d, ]*)\], (\d+), (-?\d+)⟩,?\s*⟨(\d+), (\d+), \[([\d, ]*)\], \[([\d, ]*)\]⟩")
found = pat.findall(src)
print('literals', len(found))
seen = {}
for i, ms, k, lam, m, p, A, P in found:
    key = f"SDS({eval('*'.join(ms.split(',')) or '1')},{k},{lam},[{ms.replace(' ', '')}])"
    r = rows['N' + i]
    if r['key'] != key:
        print('MISMATCH', i, key, r['key'])
    seen.setdefault(i, set()).add((ms, k, lam, m, p, A, P))
print('ids', len(seen), 'multi-variant ids', [i for i, s in seen.items() if len(s) > 1])
for i, s in sorted(seen.items()):
    for x in s:
        if x[0].replace(' ', '') != '207' and len(x[0].split(',')) > 1:
            print('noncyclic', i, x)
