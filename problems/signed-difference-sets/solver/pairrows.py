"""C17x: N464 SDS(54,46,10) on C3 x C18 through C26's T-side, the Lean rows files.

pairrows.py [--check] [--control]: mirrors PairCheck's searches (PairSearch.go, tCheck, zSearch on
K = ZMod 3 x ZMod 9, numbered b + 9a) exactly, lists the coset-sum vectors LiftSearch.cover checks
(Z: (c, k, lam, s) = (3, 14, 5, 12); T: (3, 9, 0, 3)), groups the rotations of Z's list by their
node counts, splits each group's search at a front (PairSearch.front: the nodes whose subtree has
more than SLICE nodes are expanded) into slices of at most SLICE nodes, and writes
lean/SignedDifferenceSets/PairRows/N464/Lists.lean, N464/Part<k>.lean and N464.lean.
--control runs the same search for N449 SDS(54,38,2) (halves (27,10,1) and weight 9), which must
find the pair of object O101 (the search returns false).
The mirror checks every shift; Lean checks one of each pair g, -g (the same sums) and skips the
check after a zero (the parent's check implies it), so the node counts are the same.
"""
import os
import sys

V, Q9 = 27, 9
DIR = "lean/SignedDifferenceSets/PairRows"
TEST = "lean/SignedDifferenceSets/Tests/PairSearch.lean"
SLICE = 2500        # mirror nodes per kernel check
PART = 25000        # mirror nodes per part module
OFF = 32            # PairCheck's offset of the shift sums


def kadd(i, j):
    return ((i // 9 + j // 9) % 3) * 9 + (i % 9 + j % 9) % 9


def kneg(g):
    return next(y for y in range(V) if kadd(y, g) == 0)


def kcos(b):
    return [b, b + 9, b + 18] if b < 9 else []


NB = [[(kadd(x, g), kadd(x, kneg(g))) for g in range(V)] for x in range(V)]
K_SHIFTS = [g for g in range(1, V) if g < kneg(g)]
assert K_SHIFTS == [1, 2, 3, 4, 9, 10, 11, 12, 13, 14, 15, 16, 17]


def val(P, M, y):
    return ((P >> y) & 1) - ((M >> y) & 1)


def children(lam, vals, F, sts, P, M, A, acc, r, cand):
    """go's step: the states after each value of vals in order that is not cut."""
    x, rest = sts[0], sts[1:]
    out = []
    for a in vals:
        r2 = r if a == 0 else max(r - 1, 0)
        if a != 0 and r == 0:
            continue
        if len(rest) < r2:
            continue
        acc2 = [c + a * (val(P, M, y) + val(P, M, w)) for (y, w), c in zip(NB[x], acc)]
        if any(not (lam - c <= 2 * r2 and c - lam <= 2 * r2) for c in acc2[1:]):
            continue
        P2 = P | (1 << x) if a == 1 else P
        M2 = M | (1 << x) if a == -1 else M
        A2 = A | (1 << x)
        b = x % 9
        cs = kcos(b)
        if all(((A2 >> y) & 1) or ((F >> y) & 1) for y in cs):
            s = sum(val(P2, M2, y) for y in cs)
            cand2 = [c for c in cand if (c[b] if b < len(c) else 0) == s]
        else:
            cand2 = cand
        if not cand2:
            continue
        out.append((rest, P2, M2, A2, acc2, r2, cand2))
    return out


class Search:
    def __init__(self):
        self.nodes = 0

    def go(self, lam, vals, F, leaf, sts, P, M, A, acc, r, cand):
        self.nodes += 1
        if not sts:
            return r != 0 or leaf(P, M)
        for ch in children(lam, vals, F, sts, P, M, A, acc, r, cand):
            if not self.go(lam, vals, F, leaf, *ch):
                return False
        return True


def rcount(S, b):
    return sum(1 for y in kcos(b) if not (S >> y) & 1)


def insertion_sort(key, l):
    """Mathlib's List.insertionSort with r a b = key a <= key b."""
    def ins(a, l):
        if not l:
            return [a]
        return [a] + l if key(a) <= key(l[0]) else [l[0]] + ins(a, l[1:])
    out = []
    for a in reversed(l):
        out = ins(a, out)
    return out


def t_ord(S):
    """PairCheck.tOrd: cosets by their count outside S (0..3), ties by number."""
    o = [y for k in range(4) for b in range(9) if rcount(S, b) == k
         for y in kcos(b) if not (S >> y) & 1]
    assert o == [y for b in insertion_sort(lambda b: rcount(S, b), list(range(9)))
                 for y in kcos(b) if not (S >> y) & 1]
    return o


def t_start(S, tc):
    return [c for c in tc
            if all(not all((S >> y) & 1 for y in kcos(b)) or c[b] == 0 for b in range(9))]


Z_ORD = [y for b in range(9) for y in kcos(b) if y != 0]


def t_check(srch, tw, tc, P, M):
    S = P | M
    o = t_ord(S)
    assert len(set(o)) == len(o) and all(y < 27 for y in o)
    assert all((S >> y) & 1 or y in o for y in range(27))
    return srch.go(0, [1, -1, 0], S, lambda P, M: False, o, 0, 0, 0, [0] * 27, tw, t_start(S, tc))


def z_root(r, cand):
    return (Z_ORD, 0, 1, 1, [0] * 27, r, cand)


def z_search(srch, lam, vals, r, tw, tc, cand):
    return srch.go(lam, vals, 0, lambda P, M: t_check(srch, tw, tc, P, M), *z_root(r, cand))


def z_tree(lam, vals, tw, tc, st):
    """zSearch's tree from state st (which passes): [nodes, state, children]."""
    sts, P, M, A, acc, r, cand = st
    node = [1, st, []]
    if not sts:
        if r == 0:
            s = Search()
            assert t_check(s, tw, tc, P, M)
            node[0] += s.nodes
        return node
    for ch in children(lam, vals, 0, *st):
        k = z_tree(lam, vals, tw, tc, ch)
        node[2].append(k)
        node[0] += k[0]
    return node


def front(node, keys, out):
    """PairSearch.front: expand every node above SLICE that has steps left."""
    if node[0] <= SLICE or not node[1][0]:
        out.append(node[0])
        return
    sts, P, M, A = node[1][:4]
    keys.append((P, M, A))
    for k in node[2]:
        front(k, keys, out)


def cover_list(c, k, lam, s):
    """Every vector LiftSearch.cover checks: |w_i| <= c, |w_0| largest, sum s, sum of squares
    k + lam(c - 1), sum of |w| <= k with k - sum |w| even, autocorrelation lam c on Z9."""
    Q, t = k + lam * (c - 1), lam * c
    out = []

    def rec(w, top):
        if len(w) == 9:
            if (sum(w) == s and sum(x * x for x in w) == Q and sum(map(abs, w)) <= k
                    and (k - sum(map(abs, w))) % 2 == 0
                    and all(sum(w[h] * w[(h + g) % 9] for h in range(9)) == t
                            for g in range(1, 9))):
                out.append(list(w))
            return
        for x in range(-top, top + 1):
            if sum(y * y for y in w) + x * x <= Q:
                rec(w + [x], top)
    for x0 in range(-c, c + 1):
        rec([x0], abs(x0))
    return out


def rots(L):
    return [[w[(b + h) % 9] for b in range(9)] for w in L for h in range(9)]


def lean_list(L, per_line=3, indent="    "):
    """A list of integer vectors, `per_line` vectors per line (lines stay under 100 characters)."""
    vs = ["[" + ", ".join(map(str, w)) + "]" for w in L]
    lines = [", ".join(vs[i:i + per_line]) for i in range(0, len(vs), per_line)]
    return "[" + (",\n" + indent).join(lines) + "]"


def lean_keys(ks, indent="    "):
    vs = [f"({p}, {m}, {a})" for p, m, a in ks]
    lines = [", ".join(vs[i:i + 3]) for i in range(0, len(vs), 3)]
    return "[" + (",\n" + indent).join(lines) + "]"


def control():
    """N449: Z an SDS (27,10,1) with Z 0 = -1 (two minus), T weight 9; must find O101's pair.
    Returns the candidate (a rotation of Z's list) on which the search finds it soonest."""
    LY, LT = cover_list(3, 10, 1, 6), cover_list(3, 9, 0, 3)
    best = None
    for c in rots(LY):
        srch = Search()
        if not z_search(srch, 1, [1, -1, 0], 9, 9, rots(LT), [c]):
            if best is None or srch.nodes < best[1]:
                best = (c, srch.nodes)
    srch = Search()
    res = z_search(srch, 1, [1, -1, 0], 9, 9, rots(LT), rots(LY))
    print("N449 control: zSearch =", res, "nodes", srch.nodes, "(must be False); on", best[0],
          "alone it finds the pair after", best[1], "nodes", flush=True)
    return LY, best, res


def plan():
    """Groups (candidates, nodes, front keys, slice cuts with their nodes) of N464's search."""
    LY, LT = cover_list(3, 14, 5, 12), cover_list(3, 9, 0, 3)
    tc = rots(LT)
    cands = []
    for c in rots(LY):
        if c not in cands:
            cands.append(c)
    print(len(LY), "Z vectors,", len(LT), "T vectors,", len(cands), "distinct Z rotations",
          flush=True)
    costs = []
    for c in cands:
        srch = Search()
        assert z_search(srch, 5, [1, 0], 13, 9, tc, [c]), c
        costs.append(srch.nodes)
    print("nodes per candidate:", sum(costs), "max", max(costs), flush=True)
    packs, cur, cur_n = [], [], 0
    for c, n in sorted(zip(cands, costs), key=lambda p: p[1]):
        if cur and cur_n + n > SLICE:
            packs.append(cur)
            cur, cur_n = [], 0
        cur.append(c)
        cur_n += n
    packs.append(cur)
    groups = []
    for g in packs:
        root = z_tree(5, [1, 0], 9, tc, z_root(13, g))
        keys, sizes = [], []
        front(root, keys, sizes)
        cuts, slices, cur, cur_n = [], [], 0, 0
        for i, n in enumerate(sizes):
            if cur_n and cur_n + n > SLICE:
                cuts.append(i)
                slices.append(cur_n)
                cur_n = 0
            cur_n += n
        cuts.append(len(sizes))
        slices.append(cur_n)
        groups.append((g, root[0], keys, len(sizes), cuts, slices))
    print(len(groups), "groups,", sum(len(g[4]) for g in groups), "kernel checks, nodes",
          sum(g[1] for g in groups), "max slice", max(max(g[5]) for g in groups), flush=True)
    return LY, LT, groups


HEADER = """module

{imports}

/-!
{doc}
-/

@[expose] public section

namespace SignedDifferenceSets.PairRows.N464

open LiftSearch PairSearch PairCheck CosetSearch

set_option maxRecDepth 100000
-- one kernel check at a time
set_option Elab.async false
"""


def zs(args):
    return f"zSearch 37 [1, 0] 13 9 (rots tList) {args}"


def group_text(i, g):
    cands, n, keys, nfront, cuts, slices = g
    t = (f"\n/-- Group {i}: {len(cands)} candidate vectors, {n} nodes in `solver/pairrows.py`'s "
         f"mirror. -/\ndef grp{i} : List (List ℤ) :=\n  {lean_list(cands)}\n")
    if not keys:
        return t + f"\ntheorem group{i} : {zs(f'grp{i}')} = true := by decide +kernel\n"
    t += (f"\n/-- The nodes of group {i}'s search that its front expands, as `(P, M, A)`. -/\n"
          f"def keys{i} : List (ℕ × ℕ × ℕ) :=\n  {lean_keys(keys)}\n")
    t += (f"\ntheorem front{i} : (zFront 37 [1, 0] 13 keys{i} grp{i}).length ≤ {nfront} := by\n"
          f"  decide +kernel\n")
    a = 0
    for j, (b, sn) in enumerate(zip(cuts, slices)):
        t += (f"\n-- {sn} nodes\ntheorem slice{i}_{j} : zSlice 37 [1, 0] 13 9 (rots tList) keys{i} "
              f"grp{i} {a} {b} =\n    true := by decide +kernel\n")
        a = b
    proof = "SlicesPass.single"
    for j in reversed(range(len(cuts))):
        proof = f"(SlicesPass.cons slice{i}_{j} {proof})"
    t += (f"\ntheorem group{i} : {zs(f'grp{i}')} = true :=\n"
          + wrap(f"  zSearch_of_slices {cuts} front{i} {proof}") + "\n")
    return t


def wrap(s, width=100, indent="    "):
    """Break a long proof line at spaces."""
    lead = s[:len(s) - len(s.lstrip(" "))]
    out, line = [], ""
    for w in s.lstrip(" ").split(" "):
        if line and len(line) + 1 + len(w) > width:
            out.append(line)
            line = indent + w
        else:
            line = (line + " " + w) if line else lead + w
    out.append(line)
    return "\n".join(out)


def write(LY, LT, groups):
    os.makedirs(DIR + "/N464", exist_ok=True)
    lists = HEADER.format(imports="public import SignedDifferenceSets.PairCheck", doc=(
        "# N464: the covers of the coset-sum vectors (C17x)\n\n"
        "`zList`, `tList`: the coset-sum vectors along `snd` of `Z` (27, 14, 5) and `T` "
        "(27, 9, 0),\n`|w₀|` largest, checked complete by `LiftSearch.cover`. Generated by "
        "`solver/pairrows.py`."))
    lists += f'''
/-- The coset-sum vectors of `Z` along `snd`, `|w₀|` largest (`LiftSearch.cover`). -/
def zList : List (List ℤ) :=
  {lean_list(LY)}

/-- The coset-sum vectors of `T` along `snd`, `|w₀|` largest. -/
def tList : List (List ℤ) :=
  {lean_list(LT)}

theorem zCover : cover (Indexed.size (ZMod 9)) (Indexed.addIdx (ZMod 9)) ((3 : ℕ) : ℤ)
    (((14 : ℕ) : ℤ) + 5 * (((3 : ℕ) : ℤ) - 1)) (5 * ((3 : ℕ) : ℤ)) ((14 : ℕ) : ℤ) 12 zList =
      true := by decide +kernel

theorem tCover : cover (Indexed.size (ZMod 9)) (Indexed.addIdx (ZMod 9)) ((3 : ℕ) : ℤ)
    (((9 : ℕ) : ℤ) + 0 * (((3 : ℕ) : ℤ) - 1)) (0 * ((3 : ℕ) : ℤ)) ((9 : ℕ) : ℤ) 3 tList =
      true := by decide +kernel

end SignedDifferenceSets.PairRows.N464
'''
    write_file(DIR + "/N464/Lists.lean", lists)
    parts, cur, cur_n = [], [], 0
    for i, g in enumerate(groups):
        if cur and cur_n + g[1] > PART:
            parts.append(cur)
            cur, cur_n = [], 0
        cur.append(i)
        cur_n += g[1]
    parts.append(cur)
    for k, idx in enumerate(parts):
        n = sum(groups[i][1] for i in idx)
        checks = sum(len(groups[i][4]) + (1 if groups[i][2] else 0) for i in idx)
        text = HEADER.format(imports="public import SignedDifferenceSets.PairRows.N464.Lists", doc=(
            f"# N464, part {k}: groups {idx[0]}–{idx[-1]} of `zSearch` (C17x)\n\n"
            f"{n} nodes in `solver/pairrows.py`'s mirror, {checks} kernel checks: a group's "
            f"search\nwhole, or split at a front (`zSearch_of_slices`). Generated by "
            f"`solver/pairrows.py`."))
        for i in idx:
            text += group_text(i, groups[i])
        text += "\nend SignedDifferenceSets.PairRows.N464\n"
        write_file(DIR + f"/N464/Part{k}.lean", text)
    imports = "\n".join(["public import SignedDifferenceSets.Iso"] +
                        [f"public import SignedDifferenceSets.PairRows.N464.Part{k}"
                         for k in range(len(parts))])
    names = ", ".join(f"grp{i}" for i in range(len(groups)))
    rfls = " | ".join("rfl" for _ in groups)
    exacts = ", ".join(f"group{i}" for i in range(len(groups)))
    nchecks = sum(len(g[4]) + (1 if g[2] else 0) for g in groups)
    main = HEADER.format(imports=imports, doc=(
        "# N464: no SDS (54, 46, 10) in C₃ × C₁₈ (C17x)\n\n"
        "C26's T-side (`halves_of_isSDS`) splits an SDS on `C₂ × K`, `K = C₃ × C₉`, into an SDS "
        "`Z`\n(27, 14, 5) and an SDS `T` (27, 9, 0) with disjoint supports; `PairCheck.no_pair` "
        "rules the pair\nout, here with its covers (`zList`, `tList`) and "
        f"{len(groups)} groups of candidates whose\n`zSearch` passes "
        f"({nchecks} kernel checks in {len(parts)} part modules). Generated by\n"
        "`solver/pairrows.py`."))
    main += f'''
/-- The groups. -/
def groups : List (List (List ℤ)) :=
  {wrap("[" + names + "]", indent="    ")}

theorem groups_cover_b : ((rots zList).all fun c => groups.any fun grp => grp.contains c) =
    true := by decide +kernel

theorem groups_cover : ∀ c ∈ rots zList, ∃ grp ∈ groups, c ∈ grp := by
  intro c hc
  obtain ⟨grp, hg, h⟩ := List.any_eq_true.1 (List.all_eq_true.1 groups_cover_b c hc)
  exact ⟨grp, hg, List.contains_iff_mem.1 h⟩

theorem slices : ∀ grp ∈ groups, {zs("grp")} = true := by
  intro grp h
  simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at h
  {wrap("rcases h with " + rfls, indent="    ")}
  {wrap("exacts [" + exacts + "]", indent="    ")}

/-- `C₃ × C₁₈ → C₂ × C₃ × C₉`, `(a, b) ↦ (b mod 2, a, b mod 9)`. -/
def split : ZMod 3 × ZMod 18 →+ ZMod 2 × K :=
  AddMonoidHom.prod ((ZMod.castHom (by norm_num : 2 ∣ 18) (ZMod 2)).toAddMonoidHom.comp
      (AddMonoidHom.snd (ZMod 3) (ZMod 18)))
    (AddMonoidHom.prodMap (AddMonoidHom.id (ZMod 3))
      (ZMod.castHom (by norm_num : 9 ∣ 18) (ZMod 9)).toAddMonoidHom)

theorem split_bijective : Function.Bijective split := by
  refine (Fintype.bijective_iff_injective_and_card split).2 ⟨?_, by simp⟩
  rw [injective_iff_map_eq_zero]
  decide +kernel

/-- N464: C₃ × C₁₈ has no SDS with parameters (54, 46, 10). -/
theorem n464_not_hasSDS : ¬ HasSDS (ZMod 3 × ZMod 18) 46 10 := by
  rintro ⟨D, hD⟩
  have hD' := hD.comp_addEquiv (AddEquiv.ofBijective split split_bijective).symm
  obtain ⟨Z, T, hZ, hT, hd, -⟩ := halves_of_isSDS (K := K) (i := 3) (k' := 14) (k'' := 9)
    (lam' := 5) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hD'
  exact no_pair groups zCover tCover groups_cover slices hZ hT hd

end SignedDifferenceSets.PairRows.N464
'''
    write_file(DIR + "/N464.lean", main)
    return parts


def write_file(path, text):
    for i, l in enumerate(text.split("\n"), 1):
        assert len(l) <= 100, (path, i, len(l))
    open(path, "w", encoding="utf-8", newline="\n").write(text)
    print("wrote", path, flush=True)


def write_tests(LY449, best):
    text = f'''module

public import SignedDifferenceSets.PairRows.N464
public import SignedDifferenceSets.Answer.N449

/-!
# Tests of C17x's pair search (`PairSearch`, `PairCheck`, `PairRows.N464`)

Controls on N449, SDS (54, 38, 2) in the same group C₃ × C₁₈ with the same `n = 36` (object O101,
`Answer.N449`): C26's T-side splits it into an SDS (27, 10, 1) and an SDS (27, 9, 0) with disjoint
supports (`n449_halves`), and the same search on N449's halved parameters finds such a pair
(`n449_search_finds`: `zSearch` is `false` on one coset-sum vector of `zList449`, a rotation of a
vector `cover` lists). Generated by `solver/pairrows.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests.PairSearch

open LiftSearch PairCheck PairRows.N464

set_option maxRecDepth 100000

/-- N449's halves exist: the decomposition passes on an SDS that exists. -/
theorem n449_halves : ∃ Z T : K → SignType, IsSDS 10 1 Z ∧ IsSDS 9 0 T ∧
    ∀ y, Z y = 0 ∨ T y = 0 := by
  obtain ⟨Z, T, hZ, hT, hd, -⟩ := halves_of_isSDS (K := K) (i := 3) (k' := 10) (k'' := 9)
    (lam' := 1) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (Answer.N449.isSDS.comp_addEquiv (AddEquiv.ofBijective split split_bijective).symm)
  exact ⟨Z, T, hZ, hT, hd⟩

/-- N449's `Z` coset-sum vectors (`cover` with `(c, k, λ, s) = (3, 10, 1, 6)`). -/
def zList449 : List (List ℤ) :=
  {lean_list(LY449)}

theorem zCover449 : cover (Indexed.size (ZMod 9)) (Indexed.addIdx (ZMod 9)) ((3 : ℕ) : ℤ)
    (((10 : ℕ) : ℤ) + 1 * (((3 : ℕ) : ℤ) - 1)) (1 * ((3 : ℕ) : ℤ)) ((10 : ℕ) : ℤ) 6 zList449 =
      true := by decide +kernel

/-- A rotation of a vector of `zList449`. -/
theorem mem_rots449 : {best[0]} ∈ rots zList449 :=
  List.contains_iff_mem.1 (by decide +kernel)

/-- The search is not vacuous: on N449's halved parameters (`Z 0 = −1`, values `{{1, −1, 0}}`,
`λ = 33 − 32 = 1`) it finds a pair, so `zSearch` is `false` ({best[1]} nodes in the mirror). -/
theorem n449_search_finds :
    zSearch 33 [1, 2, 0] 9 9 (rots tList) [{best[0]}] = false := by
  decide +kernel

/-- The parameters' arithmetic of N464's halving. -/
example : 4 * (14 : ℤ) = 46 + 10 ∧ 2 * (5 : ℤ) = 10 ∧ 4 * (9 : ℤ) = 46 - 10 := by norm_num

end SignedDifferenceSets.Tests.PairSearch
'''
    write_file(TEST, text)


def main():
    if "--control" in sys.argv:
        control()
        return
    LY, LT, groups = plan()
    if "--check" in sys.argv:
        for i, g in enumerate(groups):
            print(i, "cands", len(g[0]), "nodes", g[1], "keys", len(g[2]), "front", g[3],
                  "slices", g[5])
        return
    parts = write(LY, LT, groups)
    print(len(parts), "parts:", [sum(groups[i][1] for i in p) for p in parts])
    LY449, best, res = control()
    assert res is False
    write_tests(LY449, best)


if __name__ == "__main__":
    main()
