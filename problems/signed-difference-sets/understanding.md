# Understanding

**Holds.**
- Gordon's table has 70,543 rows (`instances.csv`); He–Wu's four obstructions and three
  constructions leave 22,459 open (README, reproduced by the importer). On 2026-11-07 the table
  is 91.03% settled, 6,331 open (journal); our Lean-checked rules and objects settle 16,101 rows
  Gordon lists Open (`solutions.md`, Z1–Z33).
- Every `none` rule so far is local: one quotient H, one prime p, a congruence modulus
  (p^(e/2) from self-conjugacy C5/C13/C14/C23, Ma's lemma C21, the Sylow trace C22, the
  character rules C17/C19/C20) or a multiplier orbit structure (C9/C10 for every n, I13; the
  orbit search I5; coset sums A7, widened by self-conjugate primes C25; field descent C27)
  against the coefficient range 2c, c = v/|H|. Each is one Lean theorem plus one kernel check
  over its rows; all are classical in idea (Turyn, Ma, McFarland/Gordon Thm 5.1, Miller,
  Schmidt), new in SDS form and in Lean.
- The element of order 2 splits an SDS (C26, C28, I21): when 4 ∣ n on a quotient C_{2^j} × K
  (2 self-conjugate mod exp K), Ma's step makes D(x) ≡ D(x + u) mod 2, so D = P·Z + (1 − u)·T
  with Z an SDS-like vector (v/2, (k + λ)/4, λ/2) on G/P and T a weighing element of weight n/4
  (twisted when j ≥ 2). Both halves are smaller questions: a parity condition kills 177 rows,
  a `none` halved row kills 94 more (C26 at c = 1), the halved vector's demands kill 7 (C28),
  and conversely a known halved set plus a weighing element inside its zeros builds new sets
  (I21: eight rows). A halved row that has a set (N9540, N9542: the twin-prime-power
  (99, 49, 24) set) turns a nonexistence attempt into a construction attempt.
- A rule's edge is a rich source: C22 at p = 2 with equality, C21 at equality (I20) and
  self-conjugate primes inside the multiplier group (C25) each reach rows the plain rule
  misses.
- The smallest open rows yield to exhaustion: contraction to a quotient, then a lift coset
  by coset with affine-symmetry cuts (I16) settles rows up to v = 36 in minutes of kernel
  time; at v = 39–49 the same search already times out in Python.
- "Open" often means "never searched" or "the database lags": orbit and exhaustive
  searches found sets for open rows (E4, E7, E10, O34–O38), published Paley-type sets were
  never entered (O71–O78, `corrections.md`), and the cyclotomic and Singer constructions of
  ideator round 3 give more (O61–O70, I19). Every proposed row is first checked against
  Gordon, He–Chen–Ge and He–Wu.
- Kernel and memory are the bottleneck, not ideas, for many rows: kernel memory is per Lean
  process, so large checks are split into slices and parts (`SetCheckSplit`,
  `cosetSearch_of_slices`, `OrbitSearchSplit`); with about 17 GB free, one build runs at a
  time, and a few rows need more than 13 GB in one declaration (state.md, Next step 6).
  Coding the kernel's search over ℕ instead of ℤ makes it several times faster
  (`signSearchN`).
- Generators are untrusted like solvers: `halfrows.py` once cited an orbit proof by its leaf
  count; Lean rejected it, and the halved rows were the ones with a set (N9540, N9542).

**Blocks.** The open rows split by what is missing (ideator round 3 core reports, main
folder `scratch/ideator/2026-11-06-core-{none,exists}.md`):
- search power: rows with gcd(v, n) = 1 whose orbit search was cut (core B1/B2, about
  1,450); I17's mod-q split reaches only r ≲ 27 orbits as prototyped;
- a reduction at a rule's edge: about 1,800 near-misses (core A, Ma at equality; margins in
  [½, 1));
- constructions: p-groups with n a power of p (core D1, 350; the twins of X1's sets);
- the core K, about 3,100 rows: no usable multiplier (gcd(v, n) > 1, or tiny M), every
  congruence modulus below c, quotient vectors exist on every quotient E8 decides, and far
  below the random threshold. They are probably `none`, but no local view can show it.
  No exponent bound helps there (D14x, 2026-11-09, `scratch/d14x/report.md`): the published
  non-cyclic forms (Ma–Schmidt 1995 Lemma 3.2, the Hadamard descents) need D ≥ 0 or a ±1
  array, and apply only at C21 margin ≥ ½, which no open K-arith row reaches (≤ 0.444); a
  Ma lemma without the |S|/exp loss is false for SDS (it would kill 70 `exists` rows, e.g.
  N2, N127, N658). Of the 2,070 open K-arith rows, 698 have no non-cyclic Sylow subgroup at
  stake (227 with no p | gcd(v, n), b ≥ 1; 471 with cyclic ones).
- The near-miss classes still give way to sharper local rules: Ma's lemma at its edge (C33, and its divided search
  C34) and Schmidt's field descent (C32 one step, C35 chains) reach 257 open rows together (class C 142, D2 55, D3 36,
  A 24; 2026-11-09/10), none in the core K.
- Below a Ma quotient the coset sums are divisible by p (by p² two levels down), so W/p is a vector with much smaller
  entries and moments; it dies where the plain vector lives. Searched (C34, C36), with Turyn's residue class (C38), or
  without search when no value counts exist (C39), this reaches about 140 more rows, mostly p = 2 and class C/D2. Counting
  the plain coset sums adds nothing (C7's LP already has it; `x_counts`, 0 kills on 3,428 rows).
- All quotients at once can decide a group no single quotient can: on Z_p × Z_p the p + 1 line contractions determine D
  (Σᵢ Yᵢ(πᵢx) = pD(x) + s), and integrality mod p kills 49 of the 52 open Z_p² rows (I23, exploration; pairs of quotients
  are provably too weak, D15x). This is the first global argument that reaches core rows; whether it extends to other
  non-cyclic groups (Z_p³ through hyperplanes, Z_p² × K) is open.
- Open 2026-11-10: 6,044 rows; class C 2,095 (the arithmetic core), B1–B3 2,153 (cut orbit searches), D1–D3 1,340,
  A 232, unclassified 224.

**So a Solution must.** Per row: a set Lean checks, or a rule's Lean theorem plus its
Lean check for that row; and, before it is proposed, a check against the known
constructions of Gordon, He–Chen–Ge and He–Wu. For the core K, a rule that reads the
{0, ±1} values on G itself (several quotients or primes at once, or the lift from a quotient
to G as in I16, which today reaches only v ≤ 36), with a certificate the kernel can check.
