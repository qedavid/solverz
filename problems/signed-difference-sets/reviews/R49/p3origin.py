"""Is the value at 0 of a centred valid vector on Z_3 unique (3 !| s)? Brute force over (s, Q) with |x| <= 60."""
from collections import defaultdict
B = 60
seen = defaultdict(set)
for x in range(-B, B + 1):
    for y in range(-B, B + 1):
        for z in range(-B, B + 1):
            s = x + y + z
            if s % 3 == 0 or s <= 0: continue
            if (y - z) % 3: continue  # moment y + 2z = y - z mod 3
            seen[(s, x * x + y * y + z * z)].add(x)
multi = [(k, sorted(v)) for k, v in seen.items() if len(v) > 1]
print('pairs (s,Q) with centred vectors:', len(seen), 'with >1 value at 0:', len(multi))
for kq, vals in sorted(multi)[:15]: print(kq, vals)
