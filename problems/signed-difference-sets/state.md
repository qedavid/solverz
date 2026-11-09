# State

**Focus.** The user's plan of 2026-11-09 (`scratch/inventory/final-plan.md`, items cited by the IDs of `scratch/inventory/inventory.md`, both copied from the main folder). Research mode: Groups 1–3 below, in that order; now Group 1. Search mode only when the user says so. Table 91.06% settled (none 64,010, exists 229, open 6,304); Solutions Z1–Z33 (`solutions.md`), corrections in `corrections.md`.

**Rules.**
- **NO NEW IDEATORS.** A request for one goes with its reason under "Needs the user"; the user decides.
- Ideas that come up as a by-product of the work go into `ideas/` with a kill test; work them only if they fit the plan's work, otherwise list them for the user.
- Two modes. Research mode (default): the research plan below. Search mode: only when the user says so; then stop research and Lean work, run the search list below in its order with the PC's full power, wait, record each result (experiment, objects, statuses), and go on down the list until the user switches back.
- Compute (the user, 2026-11-09): at most 14 threads; Lean in up to 4 parallel slots (`scratch/lean-slot.sh`): a job starts only if free RAM minus its expected peak leaves 6 GB, a heavy job (≥ 8 GB) runs with at most one other, the watchdog kills a build under 4 GB free, every Lean process below normal priority; at most 3 agents; agents' briefs carry these limits.
- Not ours (the user and the main session do these): the paper P2, anything for D. M. Gordon (data export, write-ups, letters), the credit and literature checks E2, E3, E16, and anything shared outside the repo.

**Done in Lean (built, `--wfail`, in the library root).** Verified claims: C1–C3, C5, C7–C11, C13–C17, C19–C23, C25–C28 (`claims/_claims.md`); C18 proved (n ≥ 2). Searches checked by the kernel: I5's orbit search (`OrbitSearch.lean`, `OrbitSearchWitt.lean`, in slices `OrbitSearchSplit.lean`), A7's coset search (`CosetSearch.lean`, `CosetSearchSelfConj.lean`, `CosetSearchCongr.lean`), C28's vector search (`EvenContraction.lean`), I16's lift search (`LiftSearch.lean`); each has a Review (`solutions.md`).

**Next step.** Research plan, in this order.

Group 1, settle what is already proved:
| ID | What | Rows |
|---|---|---|
| P1 | A7: import the built CosetRows parts (Part22–35: 8 rows, 2026-11-09); the remaining parts' builds are in the search list | 76 none |
| P2 | I5: import the built OrbitRows parts (Part78–85, 2026-11-09); Part86–137's builds are in the search list | ~27 none |
| P3 | Six halved C26 rows (N1512, N7332, N9513, N13357, N3958, N13285) | 6 none |
| P4 | Refuter on the 16 Lean-checked objects not yet proposed (statement, object, credit), then propose them: done, [R34](reviews/R34.md), proposed under Needs the user | 16 exists |
| P5 | Lean sets for the database lags N14604, N31832, N63319: done (O105–O107), settled; proposed as corrections under Needs the user | 3 exists |
| C10x | E8's 4 kills (N2847, N2863, N6970, N26266): rerun on committed code, sliced `noVector` | 4 none |
| C20x | N1's kills N44059, N44123: done (A7 rows in CosetRows Part52, Part61), settled | 2 none |
| D1x | Ma × an extra self-conjugate modulus (p^b·Q > 2c), extending C21: done, C29 verified ([R35](reviews/R35.md)), settled | 11 none |
| C6x | N27692: integer certificate for C7 | 1 none |
| C17x(c) | N464: T-side of C26 and a kernel search over the 648 halved sets | 1 none |
| C1x, C2x, C5x, E11, E12 | C4's status (R28), C6 marked superseded by C13/C14, ModQ (C24) imported, full `#print axioms` and unreachable modules, code defects before reuse. Done: C1x (C4 verified), C2x, C5x (C24 verified), E11(a) (all 11,236 library constants use only the three standard axioms, `scratch/e11/AllAxioms.lean`), E11(b) (ModQ, Tests.UnramifiedDescent in the root), E11(c) (all 76 objects with a Lean answer equal their Lean data element by element, `scratch/e11/objects_vs_lean.py`), E11(d) (`AxiomsC27.lean` rerun 2026-11-07, clean), E11(e) (objects index), E12's R1-a (`solver/src/lib.rs`: k = 0 handled). E12's other defects are in scratch tools (tiers.py k < v, sc_rows.py `j = max(j, 1)`, sp_hits' producer, E8's k ≤ Σ maxm): fix them before reusing those tools | — |

In research mode the short Lean items of Group 1 come first (P4, P5, C10x, C20x, D1x, C6x, C17x(c), the housekeeping items), then Groups 2 and 3; P1's and P2's long builds wait for search mode (the user, 2026-11-09: they would hold the Lean lock for ~12 h).

Group 1 pointers:
- P1: CosetRows Part22–35 built, imported 2026-11-09 (8 open rows, settle from `scratch/settle-a7c.tsv`). The rest: search list, `scratch/group1_chain.sh`. Rows a Solution's rule settles later are proposed under "Needs the user" as additions to that Z (here Z28).
- P2: OrbitRows Part78–85 built, imported 2026-11-09; Part86–137 in the search list (log `scratch/agentX/parts.log`): halved rows N3958 (Part104), N13285 (Part127); Part128–137 hold 24 open rows (N31876, N15437, N32197, N31825, N45850 there are `none` by C27 already: keep that evidence). Review [R31](reviews/R31.md).
- P3: teach `solver/halfrows.py`'s `reduced_proof` to cite `OrbitRows.n…_not_hasSDS` (stated with `inst`).
- P4: I19's O61–O67, O103 (N236, N1008, N11602, N14597, N14828, N31880, N31994, N14472) and I21's O79–O84, O101, O104 (N448, N463, N3539, N931, N933, N934, N939, N449).
- P5: the constructions the refuter db-lags rebuilt ([R7](reviews/R7.md)): objects, `Answer/N<id>.lean`, settle, then propose them as corrections.

Group 2, known work (port known proofs, extend rules):
| ID | What | Rows |
|---|---|---|
| P18 | Schmidt's field descent in general (I10): spike done 2026-11-09, GO (`scratch/p18/`: `Spike.lean` proves steps S1–S4, `rows.py`/`rows.out` the 126 rows' descent chains; ~600–900 more lines, 3–5 agent-days). Next: move S1–S4 into `FieldDescent.lean`, then milestone M1 (one descent step at an odd prime: 46 rows), refuter, then M2 (chains, p = 2: 80 rows) | 126 none |
| P16 + C16x/D2x | Rules at their edge: Ma at equality for c ≥ 2, two-valued cosets for margins in [½, 1) | up to 1,658 (258 class A) |
| P17 (Lean part) | C24 on quotients, ContractionCheck-style certificates | up to 392 |
| C15x | I17's checker: per-branch echelon form over a certified field, `decide +kernel` slices | 11 none |
| C4x | C18's family in Lean | family |
| E14 | P2's statements that are only on paper, as claims with Lean or a Review (rdscomb, rdsfamily, (25, 12, 1), (27, 10, 1), N32, z17/z25, rem:z18) | paper |
| E5, C18x | Optional: the (4, 4, 4, 1) RDS construction; X1b/X2b family claims | explanation |

Group 3, technique tests (kill test first; work it if it hits):
| ID | What | Rows |
|---|---|---|
| D14x | Literature: generalizations of Ma's lemma to non-cyclic Sylow subgroups; if one gives a usable bound, it joins Group 2, else it goes to "Open" | ~2,200 |
| D15x (part) | Joint contraction: coset-sum vectors on two quotients at once must be compatible; kill test on the 124 core rows where every single quotient has a vector | ? |
| P19 | LP/Farkas: relaxation of the SDS constraints on 5 core rows; an infeasible LP gives a rational dual certificate for Lean | 0–20 |
| P14 | SAT with LRAT checked by the kernel: CaDiCaL (in the Lean toolchain) on N70, N76, N134 and one known set; measure solve time, certificate size, kernel time | 3–4 |
| C3x | NL family (C12): the m = 6 norm-class recipe at m = 8, 10, Walsh check; a proof attempt if it holds | 0 (paper) |

P14's catch: `bv_decide` proves with a native axiom (tested 2026-11-07, `scratch/sat/BvAxioms.lean`), which Trust forbids; an LRAT certificate counts only if the kernel checks it.

**Search list (search mode only), in this order.**
| Class | ID | Search | Rows |
|---|---|---|---|
| minutes | C3x | NL recipe at m = 8, 10 (if not done in Group 3) | 0 |
| minutes | C10x | Rerun E8's 4 kills on committed code | 4 |
| minutes | C15x | Second engine on I17's 11 NONE rows | 11 |
| minutes | C20x | Rerun N1's search on N44059, N44123 | 2 |
| minutes | E4 | A2 uncapped; C17 ε search at r = 5; C19 at N = 128, 256 | few |
| minutes–hours | E8 / P22c | N7891's witness under multiplier 3 in C₁₈₂ | 1 (exists backing) |
| minutes–hours | E17 | Validation-only cross-checks | 0 |
| minutes–hours | D11x | SAT for sets in the 11 open order-64 rows | 11 |
| hours (overnight) | P1 + P2 builds | A7's remaining CosetRows parts (Part36–39, 50, 52–94, 44, 15, 17) and OrbitRows Part86–137, one at a time through the lock: `sh scratch/group1_chain.sh`; measured 5–9.5 min per part, ~12 h; afterwards import, root build, `#print axioms`, settle (`scratch/settle-a7.tsv`; Part128–137's rows) | 68 + 24 none (+ P3's halved rows) |
| hours | C11x | I9 symmetry searches with larger budgets | ~851 |
| hours | C16x / D2x | Weighing-element and H/P searches after the edge reduction | 258 + 524 |
| hours | D3x | Support-parity zero-set search past d(d − 1) ≥ v − 1 (d ≤ 12) | ~406 |
| hours | P17 / D6x | Mod-q split inside E8 on quotients prime to q (core D3) | 392 |
| hours | D8x | X1 census at rank 16–30 (53 (q, e, j) cases) | 323 |
| hours | P13 | Gordon's 58 orbit-exhaust "No" rows with gcd(v, n) > 1: our verified rules, then exhaustion up to v = 36 | 58 |
| hours | P10 / C14x / D16x | I16 lift search in Rust on the open rows with v < 50 (v 39–48) | 15 |
| hours | P12 | Resume E7 on N204, N205, N207, N212 (a `none` needs a certificate: lift or SAT) | 4 |
| hours | C13x | (16, 4, 16, 4) RDS in five order-64 groups, exhaustive | → 2 each |
| hours | D5x | Finish A7 on every row with a coprime quotient | ? |
| hours | D9x | X3 census at rank ≤ 16, index ≤ 16 (two primes); rank 14–30 (three primes) | ? |
| hours | E9 | N3058 (121, 60, 7) in C₁₁² | 1 |
| hours | C7x (lookup) | PDS targets: literature lookup and bounds | 136 |
| hours–days | P11 | I17 rerun with DFS pruning on core B1 | 333 |
| hours–days | E1 | O35/O36 series t = 10, 12 (N29863, N62263) | 2 |
| hours–days | E19 | X4 at r 19–25; X5 with \|H\| > 4 | 1,851 |
| hours–days | D4x | Assumed-multiplier searches, r ≤ 40 | ? |
| days | E10 / C4x | N24175: (50, 6, 49, 8) RDS in C₅ × C₆₀, or direct | 1 |
| days | P9 | N9540, N9542: T with TT* = 25 inside the 50 zeros | 2 |
| days | C17x | I21 doubling with structured T | ~78 |
| days | D12x | Exhaustive with Aut(G) symmetry breaking (or SAT) for core B0, v ≤ 100 | 138 |

**Not in the plan for now** (the user may bring them back).
| ID | What | Rows | Why |
|---|---|---|---|
| C19x | E10/E11 `none` rows without a Lean file (+46 in unimported files) | 159 (+46) | kernel certificates need 45–175 h |
| P8 | C28's heavy kills | 18–24 | 36–140 h of kernel |
| P6, P7 | Heavy halved rows; N20961 | 7 | over 13 GB in one Lean process, or days |
| P13 (rest), P10 (rest) | Gordon's "No" rows with v ≥ 39 and no multiplier; N280, N282, N354 | ~25 | 10⁹–10²⁰ leaves |
| C7x (search) | PDS searches of order 256 | — | weeks |
| P15 | G1: stronger exact search for the cut rows | 1,901 | 10¹²–10²⁸ after the split |
| P20 / D10x / D18x | G4: Galois-ring / lifting constructions, twins, p-group rows | 562 | theory first, weeks |
| D13x | Character-value enumeration (A1/A2/B3) | ~2,700 | weeks; certificates not cheaply checkable |
| E7 | N63320 in C₄₇₅ | 1 | ~10¹⁷ leaves |
| D15x (whole) | A global argument for the core | ~3,000 | no known method |
| D14x (if no source) | Ma-type lemma for non-cyclic Sylow subgroups | ~2,200 | new mathematics |
| P21 | Planned ideator rounds on the core | — | dropped by the user (no new ideators) |

**Running.** (2026-11-09 20:25)
- Agents (3 of 3, 21:46): Lean helper on P18's milestone M1 (`scratch/p18/m1-brief.md`, notes `scratch/p18/m1-progress.md`); Lean helper on C17x(c), N464 (`scratch/c17x/brief.md`, notes `scratch/c17x/progress.md`); literature for D14x, Ma-type bounds for non-cyclic Sylow subgroups (`scratch/d14x/brief.md`, report `scratch/d14x/report.md`). The C6x refuter finished: SURVIVES ([R36](reviews/R36.md)); N27692 settles after the next root build.
- Lean: C10x's four contraction certificates (N6970, N26266, N2847, N2863; `answer.py contract`, prefixes as base-(2c+1) codes in batches of 50,000 nodes) building in slots (`scratch/c10x_chain.sh`, log `scratch/c10x_chain.log`); then the root alone (with `MarkedCountsInt` and the answers that built), `scratch/c10x_axioms.lean`, settle.
- The leftover processes are gone (checked 2026-11-09 20:14). I17's prototype finished both batches: of the 272 cyclic B1 rows, 234 too big, 16 NONE (11 still open: N3067, N15689, N17962, N26085, N44138, N45372, N47110, N49189, N49203, N49278, N60164; C15x), 4 FOUND (the known Paley-and-zero sets), the rest skipped (`scratch/n2/b1_cyc_{a,b}.out`). E7's partial output `scratch/e7.out` (11 of 22 rows, E7.md); its open rows N204, N205, N207, N212 are P12 in the search list.

**Building.** Lean through slots: `sh scratch/lean-slot.sh build <owner> <module> <expected peak GB>` (a leaf module whose SignedDifferenceSets imports are already built: checked with `lake build --no-build`, else it runs alone), `sh scratch/lean-slot.sh env <owner> <file> <peak>` (scratch files; output stops at 80 lines), `sh scratch/lean-slot.sh root <owner>` (the library root, alone). Parallel `lake build`s share the build directory, so only leaves build side by side; Lake 5.0 has no build lock of its own. Tested 2026-11-09 with 2 parallel builds (CosetRows Part36 beside a helper's builds, clean); raise to 4 after more clean runs. The old single lock (`lean-locked-big.sh`, `lenv-locked.sh`, used by agents started before) counts as one heavy job. Measured peaks: light leaf builds 3–7 GB; HalfRows heavy parts 12–14 GB; a contraction certificate checked in batches of 300,000 nodes 11.4 GB (killed), per prefix 3.9 GB: batches of 50,000 now (`solver/answer.py`). About 17 GB is free with no build and the user's usual apps. Large row files are split into parts with `set_option Elab.async false`. Generators in `solver/` write Lean row files: check `git status` on `lean/` after running one.

Results only in scratch (git-ignored):
- The worktree's `scratch/`: `e5.out`, `e6.out`, `e7.out`, `r4.out` (recorded in E5, E6, E7, E4 with SHA-256; `e7.out` still open in E7); the refuter's working folders (their reports and scripts are recorded in `reviews/`; outputs over 1 MB stay here); settle batches `settle-*.tsv`, `c26/half_rows.tsv`, `c26/even_rows.tsv`; `build-*.log`, `bench/*.lean`; `inventory/` (the plan and the inventory); `ideator/` (the six reports and their row lists, copied from the main folder). Keep.
- The **main folder's** `problems/signed-difference-sets/scratch/` (the overnight work of 2026-11-06, outside the worktree; copy it into the worktree's scratch before citing it there): the refuter's working folders of that night (recorded as [R4](reviews/R4.md)–[R9](reviews/R9.md)) and of paper P1 ([R33](reviews/R33.md)), with the downloaded papers they opened (not redistributed); `e8/` (exploration: the all-rows contraction passes, the orbit search, `turyn.py`, README); `other-session/` (another session's hand-off, N735 and N17201). Keep.

## Needs the user

- Proposed Solution: C29 (Ma's lemma with an extra self-conjugate modulus, p^b·Q > 2c): no SDS in 11 rows Gordon lists Open (N6822, N9200, N44532, N44533, N44562, N44563, N44662, N44663, N44752, N44753, N58644; `MaCombRows.n…_not_hasSDS`). Refuter SURVIVES ([R35](reviews/R35.md)). Origin: Ma's lemma (Ma 1985) with Turyn's self-conjugacy; the combination: ideator round 2, Lean proof ours; not found in print (Arasu–Ma 2001, Pott 1995, Leung–Ma–Schmidt not opened).
- CW(195, 100) (R35 Finding 3; C29's certificate proves `¬ HasSDS (ZMod 195) 100 0`, `reviews/R35/Probe2.lean`): stays in this problem (the user, 2026-11-09). A refuter started from the main session checks it (equivalence to HasSDS (ZMod 195) 100 0, Probe2.lean, the argument, the literature; report in the main folder's `scratch/refuter/cw195/report.md`); no check of ours. On its verdict: record a claim and a proposed Solution answering Arasu–Gordon–Zhang's Table 10.
- Proposed Solutions (plan item P4; refuter [R34](reviews/R34.md): statements and sets SURVIVE, the credit was FLAWED for I21 and is corrected as R34 says, in `ideas/I21.md` and `objects/_objects.md`; all 16 rows are `exists`, Open in Gordon's sds.json e3bf810, Lean `Answer.N<id>.hasSDS` in the root):
  - Cyclotomic constructions (I19, ideator round 3's X1, X3): 7 rows, N236 (42, 18, 2), N1008 (75, 26, 1), N11602 (217, 112, 12) by generalized cyclotomy on products of fields; N14597 (243, 121, 40), N14828 (243, 177, 96), N31880 (343, 199, 3), N31994 (343, 247, 51) by semilinear cyclotomy (O61–O67). Origin: ours, in known frameworks; none found in print; O64 is the nonzero squares of GF(243) (Paley) minus the Berlekamp–van Lint–Seidel PDS (243, 22, 1, 2).
  - N14472 (243, 82, 1) in C₃³ × C₉ (O103): He–Chen–Ge Thm 4.1 transported to the non-split index-3 subgroup C₃⁴; the transport and the set: ours.
  - Doubling (I21): 8 rows, N448, N463 (54, ·, ·), N3539 (128, 68, 4), N931, N933, N934 (72, 40, 4), N449 (54, 38, 2), N939 (72, 48, 12) (O79–O84, O101, O104). Origin: the weighing-matrix doubling of Arasu–Leung–Ma–Nabavi–Ray-Chaudhuri 2006 Thm 2.3 (Arasu–Kotsireas–Koukouvinos–Seberry 2010 Thm 4), extended to SDS with λ ≠ 0 and twisted: ours; the sets: ours.
- Proposed corrections (plan item P5; [R7](reviews/R7.md) SURVIVES these constructions): N14604 (243, 122, 59) in C₃⁵ and N31832 (343, 172, 84) in C₇³ (Gordon's Prop 2.3, Paley and zero; O105, O106), N63319 (475, 241, 120) in C₅ × C₉₅ (Gordon's Thm 4.1, q = 19, r = 25; O107): Open in Gordon's database, settled `exists` here with Lean-checked sets.
- Proposed corrections (refuter db-lags and a5-a3, [R7](reviews/R7.md), [R5](reviews/R5.md); listed in `corrections.md` only on approval):
  - N63320 (475, 241, 120) in C₄₇₅ is "Yes" ("Prime Power Pair", no stored set) while N63319, the same parameters in C₅ × C₉₅, is Open: Gordon's Thm 4.1 at q = 19, q + 6 = 25 builds its set in GF(19)⁺ × GF(25)⁺ ≅ C₅ × C₉₅, never cyclic (GF(25)⁺ = C₅²). The two entries look swapped; C₄₇₅ should be open (not "No": nothing rules a set there out).
  - "Yes" resting only on stored sets that fail the SDS check: 148 of 279 stored sets fail, 22 keys have no valid stored set (rechecked 2026-11-07 with the reading the other 131 sets pass; 1-based indices, swapped signs and primitive-root exponents do not fix them). Valid sets are ours for 21 of the 22 (O59, O60, O68–O70, O85–O100, Lean-checked); N7891 (182, 38, 2, "assuming multiplier 3") has no valid witness anywhere. Our table keeps them `exists` on Gordon's word.
- `scratch/lean-build.ps1` (the RAM watchdog) has no committed home.
- Requests for an ideator, with their reason (none so far).
