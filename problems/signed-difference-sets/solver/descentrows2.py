"""P18 M2 rows: open rows killed by a chain of Schmidt's field descent steps (`FieldDescentChain.lean`).

A row dies on a cyclic quotient C_m (m | exp G, c = v/m) along a chain m = d0 -> d1 -> ... -> F, d_{i+1} = d_i/p_i,
when every step has p^2 | d_i (8 | d_i if p = 2), every prime of m divides d_{i+1}, and for every prime q | n
(n = k - lambda, q = p included) a unit t mod m with t = 1 + d_{i+1} (mod d_i) and t = q^e (mod m/q^a), q^a the
q-part of m; and m F c^2 < phi(m) n (`FieldDescentChainCert.Kills`). The witnesses t, e are found by brute force over
all t < m (independent of `scratch/p18/rows.py`'s CRT test); every certificate is re-checked by `kills`, a literal
mirror of `Kills`; the chain search also runs on the `exists` rows (none may die). Rows M1 already kills
(`scratch/p18/settle-m1.tsv`) are left out. Shortest chain first, then smallest m.
`python solver/descentrows2.py` writes `lean/SignedDifferenceSets/FieldDescentChainRows.lean` and
`scratch/p18/settle-m2.tsv`; `--check` only prints. Run from the problem folder.
"""

import math
import re
import sys
from functools import lru_cache
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from descentrows1 import EXISTS, NL, OPEN, ROOT, factor, form, lst, rows_of, totient  # noqa: E402

OUT = ROOT / "lean" / "SignedDifferenceSets" / "FieldDescentChainRows.lean"
TSV = ROOT / "scratch" / "p18" / "settle-m2.tsv"
M1 = ROOT / "scratch" / "p18" / "settle-m1.tsv"
SPIKE = ROOT / "scratch" / "p18" / "rows.out"
MAX_STEPS = 6


def q_part(m, q):
    """(a, q^a) with q^a the exact power of q in m."""
    a = 0
    while m % q ** (a + 1) == 0:
        a += 1
    return a, q ** a


def witness(m, d, p, q):
    """A unit t < m with t = 1 + d/p (mod d) and t = q^e (mod m/q^a), as (q, t, a, e), or None."""
    a, qa = q_part(m, q)
    mod = m // qa
    powers, y = {}, 1 % mod
    for e in range(mod + 1):
        powers.setdefault(y, e)
        y = y * q % mod
    target = (1 + d // p) % d
    for t in range(1, m):
        if math.gcd(t, m) == 1 and t % d == target and t % mod in powers:
            return q, t, a, powers[t % mod]
    return None


def step(m, n, d, p):
    """The witnesses of a valid step d -> d/p, or None."""
    if d % (p * p) or (p == 2 and d % 8):
        return None
    if any((d // p) % r for r in factor(m)):
        return None
    ws = [witness(m, d, p, q) for q in sorted(factor(n))]
    return None if None in ws else ws


@lru_cache(maxsize=None)
def chains(m, n):
    """Breadth-first: a shortest valid chain from m to each reachable d, as (d, [(p, witnesses), ...])."""
    out, level, seen = [], [(m, [])], {m}
    for _ in range(MAX_STEPS):
        nxt = []
        for d, ch in level:
            for p in sorted(factor(m)):
                ws = step(m, n, d, p) if d // p not in seen else None
                if ws is not None:
                    seen.add(d // p)
                    nxt.append((d // p, ch + [(p, ws)]))
        out += nxt
        level = nxt
    return out


def cert(v, k, lam, ms):
    """(m, steps) of the shortest killing chain (then smallest m), or None."""
    n = k - lam
    if n <= 1:
        return None
    w = math.lcm(*ms)
    best = None
    for m in range(2, w + 1):
        if w % m:
            continue
        c = v // m
        for F, ch in chains(m, n):
            if m * F * c * c < totient(m) * n:
                key = (len(ch), m)
                if best is None or key < best[0]:
                    best = (key, m, ch)
                break
    return None if best is None else (best[1], best[2])


def is_prime_td(p):
    return p >= 2 and all(p % d for d in range(2, p))


def kills(ms, k, lam, m, A, P, steps):
    """Literal mirror of `FieldDescentChainCert.Kills` (MapOk/SurjCert as M1's form checks)."""
    n = k - lam
    v = math.prod(ms)
    if not (all(x > 0 for x in ms) and m > 1 and v % m == 0 and n > 0):
        return False
    if not all(a * x % m == 0 for a, x in zip(A, ms)) or sum(a * x for a, x in zip(A, P)) % m != 1 % m:
        return False
    d = m
    for p, ws in steps:
        if not (is_prime_td(p) and d % (p * p) == 0 and (p % 2 == 1 or (p == 2 and d % 8 == 0))):
            return False
        if pow(d // p, m) % m:
            return False
        for q in range(2, n + 1):
            if n % q or not is_prime_td(q):
                continue
            if not any(wq == q and math.gcd(t, m) == 1 and t % d == (1 + d // p) % d and m % q ** a == 0
                       and t % (m // q ** a) == q ** e % (m // q ** a) for wq, t, a, e in ws):
                return False
        d //= p
    return m * d * (v // m) ** 2 < totient(m) * n


def collect():
    m1 = {ln.split("\t")[0] for ln in M1.read_text(encoding="utf-8").splitlines() if ln.strip()}
    rows = []
    for i, v, k, lam, ms in rows_of(OPEN):
        if i in m1:
            continue
        hit = cert(v, k, lam, ms)
        if hit:
            m, steps = hit
            A, P = form(ms, m)
            assert kills(ms, k, lam, m, A, P, steps), i
            rows.append((i, ms, k, lam, m, A, P, steps))
    bad = [(i, cert(v, k, lam, ms)) for i, v, k, lam, ms in rows_of(EXISTS) if cert(v, k, lam, ms)]
    return rows, bad


def chain_text(m, steps):
    ds = [m]
    for p, _ in steps:
        ds.append(ds[-1] // p)
    return " → ".join(map(str, ds))


def cert_lean(m, A, P, steps, indent):
    parts = []
    for p, ws in steps:
        wl = ", ".join(f"⟨{q}, {t}, {a}, {e}⟩" for q, t, a, e in ws)
        parts.append(f"⟨{p}, [{wl}]⟩")
    sep = "," + NL + " " * (indent + 2)
    return f"⟨{m}, {lst(A)}, {lst(P)},{NL}{' ' * (indent + 1)}[{sep.join(parts)}]⟩"


def render(rows):
    body, items = [], []
    for i, ms, k, lam, m, A, P, steps in rows:
        row = f"⟨{i[1:]}, {lst(ms)}, {k}, {lam}⟩"
        body.append(f"""/-- {i}: SDS{tuple([math.prod(ms), k, lam])} on {lst(ms)}, quotient `ZMod {m}`, chain {chain_text(m, steps)}. -/
theorem fieldDescentChainKill_{i} :
    FieldDescentChainCert.Kills {row}
      {cert_lean(m, A, P, steps, 6)} := by
  decide +kernel
""")
        items.append(f"  ({row},{NL}    {cert_lean(m, A, P, steps, 4)})")
    proof = "List.forall_mem_nil _"
    for i, *_ in reversed(rows):
        proof = f"List.forall_mem_cons.2 ⟨fieldDescentChainKill_{i},{NL}    {proof}⟩"
    return f"""module

public import SignedDifferenceSets.FieldDescentChain

/-!
# Rows killed by a chain of Schmidt's field descent steps (P18, M2)

{len(rows)} open rows, each with a cyclic quotient `ZMod m` (the form `A`, a preimage `P` of `1`)
and a descent chain `m → … → F` with its witnesses, such that `FieldDescentChainCert.Kills` holds;
each row is checked by its own `decide +kernel`. Generated by `solver/descentrows2.py`.
-/

@[expose] public section

namespace SignedDifferenceSets

{NL.join(body)}
/-- The rows and their certificates. -/
def fieldDescentChainRows : List (Row × FieldDescentChainCert) := [
{("," + NL).join(items)}]

theorem fieldDescentChainRows_kill : ∀ x ∈ fieldDescentChainRows, x.2.Kills x.1 :=
  {proof}

/-- No row of `fieldDescentChainRows` has an SDS. -/
theorem fieldDescentChainRows_not_hasSDS {{x : Row × FieldDescentChainCert}}
    (hx : x ∈ fieldDescentChainRows) (inst : Fintype (Grp x.1.ms)) :
    ¬ @HasSDS (Grp x.1.ms) _ inst x.1.k x.1.lam :=
  FieldDescentChainCert.not_hasSDS (fieldDescentChainRows_kill x hx) inst

end SignedDifferenceSets
"""


def main():
    rows, bad = collect()
    print(len(rows), "open rows killed (beyond M1);", len(bad), "exists rows killed", bad[:5])
    by_len = {}
    for r in rows:
        by_len[len(r[7])] = by_len.get(len(r[7]), 0) + 1
    print("chain lengths:", dict(sorted(by_len.items())), "| p = 2 rows:",
          sum(1 for r in rows if any(p == 2 for p, _ in r[7])))
    if SPIKE.exists():
        m1 = {ln.split("\t")[0] for ln in M1.read_text(encoding="utf-8").splitlines() if ln.strip()}
        spike = {ln.split()[0] for ln in SPIKE.read_text(encoding="utf-8").splitlines() if re.match(r"N\d+ ", ln)}
        mine = {r[0] for r in rows}
        print("rows.out minus M1:", len(spike - m1), "| only here:", sorted(mine - spike), "| only there:",
              sorted(spike - m1 - mine))
    if bad or "--check" in sys.argv:
        return
    text = render(rows)
    assert all(len(ln) <= 100 for ln in text.split(NL)), "line over 100 characters"
    OUT.write_text(text, encoding="utf-8", newline=NL)
    TSV.write_text("".join(f"{r[0]}\tnone\tP18 M2; FieldDescentChainRows\t"
                           f"SignedDifferenceSets.fieldDescentChainRows_not_hasSDS{NL}" for r in rows),
                   encoding="utf-8", newline=NL)
    print("wrote", OUT.name, "and", TSV.name)


if __name__ == "__main__":
    main()
