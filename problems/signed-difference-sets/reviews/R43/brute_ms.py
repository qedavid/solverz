"""Validate multisets() against brute force over [-c,c]^m for small m, c."""
import itertools
from collections import Counter
from multisets import multisets
bad = 0; tests = 0
for m in range(1, 6):
    for c in range(1, 4):
        seen = {}
        for z in itertools.product(range(-c, c + 1), repeat=m):
            key = (sum(z), sum(a * a for a in z))
            seen.setdefault(key, set()).add((tuple(sorted(Counter(z).items())), sum(abs(a) for a in z)))
        for (s1, Q), S in seen.items():
            for Ab in range(0, m * c + 1):
                for par in (None, 0, 1):
                    want = {ms for ms, A in S if A <= Ab and (par is None or (A - par) % 2 == 0)}
                    got = {tuple(sorted(x.items())) for x in multisets(m, c, s1, Q, Ab, par)}
                    tests += 1
                    if want != got: bad += 1
        # also (s1,Q) pairs with no vector: must give none
        for s1 in range(-m * c, m * c + 1):
            for Q in range(0, m * c * c + 1):
                if (s1, Q) not in seen:
                    tests += 1
                    if multisets(m, c, s1, Q, m * c): bad += 1
print("tests", tests, "bad", bad)
