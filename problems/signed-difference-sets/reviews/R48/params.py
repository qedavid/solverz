import sys, math, csv, re
sys.path.insert(0, '.')
from kill import verdict, klein_quot, KEY
sets = [(216,189,20),(240,187,18),(288,189,20),(324,237,68),(324,263,94),(336,301,132),(360,181,12),(384,203,34),
        (384,357,188),(420,207,38),(432,179,10),(468,273,104),(468,299,130),(480,231,62),(480,365,196)]
for key in sets:
    V = verdict(*key)
    # hand claim: every z has exactly one odd coord j and z = 2 mod 4 at both other coords
    hand = True
    for z in V['Z']:
        odd = [i for i in range(3) if z[i] % 2]
        if len(odd) != 1 or any(z[i] % 4 != 2 for i in range(3) if i != odd[0]): hand = False
    print(key, 'n', V['n'], 't', V['t'], 's', V['s'], 'Qz', V['Qz'], 'Bz', math.isqrt(V['Qz']), '#d', V['nD'], '#z', V['nZ'],
          'alive', V['alive'], 'kill', V['kill'], 'hand', hand)
V = verdict(216,189,20)
print('d triples n=169:', sorted(set(V['D'])))
print('Dres', V['Dres'])
# exists rows with a Klein quotient and square n: the check runs and must not kill
rows = list(csv.DictReader(open('../../../instances.csv', encoding='utf-8')))
for r in rows:
    if r['status'] != 'exists': continue
    v, k, lam, ms = KEY.match(r['key']).groups(); v, k, lam = int(v), int(k), int(lam); ms = [int(x) for x in ms.split(',')]
    if klein_quot(ms):
        W = verdict(v, k, lam)
        print('exists', r['id'], (v, k, lam), ms, None if W is None else ('alive', W['alive'], 'of', W['nZ'], 'kill', W['kill']))
