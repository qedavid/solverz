# State

**Focus.** Settle what is proved (the user, 2026-11-10, via the peer session): the row certificates for the tomography kills (I23: about 370 rows in exploration; C40–C42 and the flats in Lean), the C36 chain, the root build, settle. Then the open items of Groups 2 and 3 (P16's edge, P17, C15x, C4x, P19, C3x at m = 10, E5/C18x) before any further tomography extension. Plan of 2026-11-09: `scratch/inventory/final-plan.md` (IDs of `scratch/inventory/inventory.md`). Search mode only when the user says so. Table 91.97% settled (none 64,652, exists 229, open 5,662); Solutions Z1–Z33 (`solutions.md`), corrections in `corrections.md`.

**Frozen (the user, 2026-11-11 18:09):** 48 compute processes are suspended at the OS level, not stopped (`scratch/freeze.ps1`, PIDs in `scratch/frozen-pids.txt`): the C36 chain and the N40420/N56207 rebuild, the agents' Lean builds, chains and Python/Rust runs, the watchdogs and slot scripts. To continue: `powershell.exe -NoProfile -ExecutionPolicy Bypass -File scratch/freeze.ps1 thaw` (from the problem folder), C15x reported and finished (2026-11-12, C47: second engines agree on all 11 rows; three rows' builds left, restart `sh scratch/c15x/chain_run_<id>.sh`, notes `scratch/c15x/notes.md`). No agent is running. I25's A7 helper reported and finished at the freeze; its frozen jobs (Part03's build, `indep_lat_fast` on 35 problems) continue on thaw, results in `scratch/p17/a7/`, next steps in `scratch/p17/a7-progress.md` ("State at the pause"). Jobs under `timeout 3600` (three `indep_lat` runs) may be killed on thaw if their hour has passed; rerun them from the notes. If the session restarts, the agents are gone; successors continue from their notes. 2026-11-12 21:03: Claude Code's low-memory guard (free RAM 3.5 GB) stopped the C36 chain driver and the N40420/N56207 rebuild driver (10 shells of the frozen set); the frozen Lean build of N40420 survives but has no driver: after the thaw restart the chain from `scratch/c34/todo.txt` (plus N40420, N56207) with `xargs -P 2 -I{} sh scratch/c34/tree.sh {}`. 38 frozen processes remain (4.2 GB).

**No new agents (the user, 2026-11-11 16:10):** start no agent until the user says so; the three running ones finish. Builds, axioms and settling go on.

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
| P3 | Halved C26 rows: N7412 settled 2026-11-10 (N33806, N61082 by C33); N18643 (Part104), N60752 (Part127) follow P2's builds; N9513 has no open parent row | 3 settled + 2 none |
| P4 | Refuter on the 16 Lean-checked objects not yet proposed (statement, object, credit), then propose them: done, [R34](reviews/R34.md), proposed under Needs the user | 16 exists |
| P5 | Lean sets for the database lags N14604, N31832, N63319: done (O105–O107), settled; proposed as corrections under Needs the user | 3 exists |
| C10x | Done 2026-11-10: N6970 settled (split certificate, `Answer/N6970`), N2847, N2863, N26266 settled by C33 | 4 settled |
| C20x | N1's kills N44059, N44123: done (A7 rows in CosetRows Part52, Part61), settled | 2 none |
| D1x | Ma × an extra self-conjugate modulus (p^b·Q > 2c), extending C21: done, C29 verified ([R35](reviews/R35.md)), settled | 11 none |
| C6x | Done 2026-11-10: N27692 settled (`MarkedCountsInt`) | 1 settled |
| C17x(c) | Done 2026-11-10: N464 settled by C37 ([R44](reviews/R44.md)) | 1 settled |
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
| P18 | Done 2026-11-10: C32 (one step, 60 rows, 21 newly settled) and C35 (chains, 66 rows, 62 newly settled) verified, [R39](reviews/R39.md), [R41](reviews/R41.md) | 83 settled |
| P16 + C16x/D2x | Rules at their edge. Settled: C33 (151), C34 (23; N4195, N19445 building). Proved, settle after the root build: C36 (49 rows, 36 of 50 modules built, chain paused), C38 (14) and C39 (52), [R46](reviews/R46.md); N20961 (C38) built, unreviewed; N8416, N8422, N8476, N752 parked (kernel cost). Still open: Ma at equality for c ≥ 2 (two-valued cosets, I20), margins in [½, 1) | 174 settled, 115 pending |
| P17 (Lean part) | C24 on quotients, ContractionCheck-style certificates | up to 392 |
| C15x | I17's checker: per-branch echelon form over a certified field, `decide +kernel` slices | 11 none |
| C4x | C18's family in Lean | family |
| E14 | P2's statements that are only on paper: refuter round done 2026-11-09, SURVIVES ([R38](reviews/R38.md)): rdscomb is C30 (now proved, Lean checks the 19 sets), the (27, 10, 1) and (25, 12, 1) remarks, rem:z17, rem:z18 (full scope: same 629 rows), rem:z25; rdsfamily is C18 (C4x). P2's credit and wording findings are under Needs the user | — |
| E5, C18x | Optional: the (4, 4, 4, 1) RDS construction; X1b/X2b family claims | explanation |

Group 3, technique tests (kill test first; work it if it hits):
| ID | What | Rows |
|---|---|---|
| D14x | Done 2026-11-09: goes to "Open" (no published non-cyclic Ma-type bound transfers to SDS; the no-loss form kills 70 `exists` rows; `scratch/d14x/report.md`, understanding.md). Leads it left, untested: a signed Ma–Schmidt Lemma 3.2 with I20's two-valued cosets on 1,336 open rows at C21 margin (½, 1] (P16's ground); nonnegativity arguments on the 258 open rows with one minus sign | 0 |
| D15x (part) | Done 2026-11-10: pairs of quotients are provably too weak (`scratch/d15x/report.md`); all quotients at once gave I23 (tomography): C40–C42 and the flats, see the tomography line under Running | → I23 |
| P19 | LP/Farkas: relaxation of the SDS constraints on 5 core rows; an infeasible LP gives a rational dual certificate for Lean | 0–20 |
| P14 | SAT with LRAT checked by the kernel. Kill test 2026-11-09: negative for the off-the-shelf route. `bv_decide` proves with a native axiom; Std's checker (`Std.Tactic.BVDecide.LRAT.check_sound`) has the right theorem, but `decide +kernel` gets stuck on its `check.go` (well-founded recursion, private), even on x₀ ∧ ¬x₀ (`scratch/p14/Tiny.lean`). The route needs our own structurally recursive LRAT checker with a soundness proof for RUP steps (a substantial Lean project, not started) | 3–4 |
| C3x | NL family (C12): the m = 6 norm-class recipe at m = 8, 10. Kill test negative (2026-11-09): at m = 8 no Frobenius-invariant union of the norm classes of order 255 gives NL₂₅₆(126) (R9's complete run, `reviews/R9/cyc/big_16_255_126.out`: 0 hits, 5.3·10⁸ nodes), so the recipe gives no even-m family; m = 10 not run | 0 (paper) |


**Search list (search mode only), in this order.**
| Class | ID | Search | Rows |
|---|---|---|---|
| minutes | C3x | NL recipe at m = 8, 10 (if not done in Group 3) | 0 |
| minutes | C10x | Rerun E8's 4 kills on committed code: done 2026-11-09 (`e8_passes`, `scratch/e8_c10x.out`) | 4 |
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
| D14x | Ma-type lemma for non-cyclic Sylow subgroups (no source, D14x 2026-11-09) | ~2,200 | new mathematics; the no-loss form is false for SDS |
| P21 | Planned ideator rounds on the core | — | dropped by the user (no new ideators) |

**Running.** (2026-11-10 13:55; the user lifted every temporary restriction: CLAUDE.md's limits only, "never stop")
- Resumed 2026-11-11 (the user: "the pc is yours"). Agents (3): C15x, a second engine and Lean for I17's 11 NONE rows
  (`scratch/c15x/brief.md`; started 14:25); Lean helper for I24's 67 coset-type-count rows (`scratch/p16/lean-brief.md`, notes
  `scratch/p16/lean-progress.md`; 15:17); second engine (A7) and Lean for I25's 139 kills (`scratch/p17/a7-brief.md`, notes
  `scratch/p17/a7-progress.md`; 15:58). Done: the P16 explorer (I24: 89 open rows in exploration), the P17 explorer (I25: 162 rows,
  139 new, `scratch/p17/kills.tsv`); R50 (C44/C45) recorded from the paused refuter's report.
- 17:43: the three agents had stopped at the account's usage limit (about 17:30) and were resumed by message after its reset.
- Lanes finished 17:42. Lanes (restarted 2026-11-11): `scratch/tomo/q/lane2.sh` ×2 (queue `scratch/tomo/q/queue.txt`), `scratch/tomo/l5/lane.sh` on
  `scratch/tomo/l5/q7.txt` (8 rows), `scratch/tomo3/l4/lane.sh` (N758); log `scratch/lanes-restart.out`. C36 chain resumed on 16
  rows (14 C36, C34's N4195, N19445; `scratch/c34/todo.txt`, log `scratch/c34/chain.log`).
- Root: built 2026-11-10 21:42 and 22:01; 362 rows settled 2026-11-11. Next root build with priority (`scratch/root_prep.py
  --apply`, `sh scratch/lean-slot.sh root researcher`) when the lanes and the chain have built their rows; settle lists from
  `python scratch/settle_prep.py` (plus C43's, C44's, C45's lists).
- C41's rows build in two background lanes (`scratch/tomo/q/lane.sh`, queue `scratch/tomo/q/queue.txt`, results
  `scratch/tomo/q/build_all.out`; `sh scratch/tomo/q/collect.sh` gathers the result files the lanes leave in the problem folder):
  141 rows generated, 67 built at 17:44; then `python scratch/tomo/q/mkaxioms.py` and the AxiomsQ1/Q2 checks.
- Lean: the C36 chain is paused (20:09) so C41's lanes finish and the root can build: 36 of C36's 50 modules built. Resume after the
  root: unbuilt rows from `python scratch/root_prep.py` (C36 line) into `scratch/c34/todo.txt`, then
  `xargs -P 2 -I{} sh scratch/c34/tree.sh {} < scratch/c34/todo.txt` (log `scratch/c34/chain.log`); then N4195, N16779, N19445.
  N4195 and N16779B16 again (killed by the watchdog under memory pressure), N19445, then the root with MaDivided2 and the C36 rows
  (settle `scratch/maedge/settle-c36-merged.tsv` through `scratch/settle_safe.py`), after C38/C39's refuter MaDividedCounts,
  MaDividedRes and their 66 rows (settle `settle-c34b.tsv`, `settle-c36b.tsv`, `settle-c38.tsv`).
- Settled today so far: 237 (01:58–02:02) + 24 (12:52): C33, C32, C35, P3, N27692, N6970, C34 (23), C37 (N464). Table 91.43%.
  Always settle through `scratch/settle_safe.py`: `settle.py` overwrites the evidence of rows already settled.
- **Next steps, in order:**
  1. The C36 chain, the reruns, root import and build, axioms, settle; C36 → verified.
  2. One root build after the C36 chain, with C36's rows, C38/C39 (72 modules, already in the root file, uncommitted) and C40
     (13 modules, likewise); then axioms, settle `settle-c36-merged.tsv`, `settle-c34b.tsv`, `settle-c36b.tsv`, `settle-c38.tsv`,
     `scratch/tomo/settle-c40.tsv` through `settle_safe.py`; C36, C38, C39, C40 → verified; proposed Solutions. N20961 (C38, not
     reviewed) is imported but not settled. The root needs 9.1 GB + the 4 GB reserve: it waits for a nearly idle machine.
  3. C41: the lanes (141 rows + 15 Z_11² quotient rows from tomo4 queued 18:20, generated with `TSLICE=1500`/`2500`), the
     axioms, root, settle; the 15 are not in R47 (independent Python in `scratch/tomo4/` agrees). Still out of reach
     (lean2-progress.md): 41 p = 7 quotient rows without a multiplier (0.85M–2·10⁸ listing nodes), p | s rows, N3066, N6692,
     N6718, p = 19 with t of order 3, the U0 = 1 Z_p² rows (lattices), the n = p² Z_11²/Z_13² quotient rows (explicit V).
  3b. C42 (R48 SURVIVES): root (KleinTomography, Params, 67 rows, Tests.KleinTomography, TwistBox), settle.
  3a. The 10M-node rows N8416, N8422, N8476, N752: parked (about 5 ms and 0.25 MB per kernel node; C34.md).
  4. The tomography explorer's families, as they come.
- Slots (2026-11-09): admission counts each running job's headroom (calibrated peak − the working set its Lean processes hold now); peaks calibrated from `scratch/lean.peaks` (measured + 0.5 GB, written after every job); a mutex older than 2 minutes counts as stale. `answer.py contract <id> <divisors> [depth]`: depth 3 for N6970 (at depth 4 the join's coverage check over 2,812 prefixes hit 10.6 GB).
- The leftover processes are gone (checked 2026-11-09 20:14). I17's prototype finished both batches: of the 272 cyclic B1 rows, 234 too big, 16 NONE (11 still open: N3067, N15689, N17962, N26085, N44138, N45372, N47110, N49189, N49203, N49278, N60164; C15x), 4 FOUND (the known Paley-and-zero sets), the rest skipped (`scratch/n2/b1_cyc_{a,b}.out`). E7's partial output `scratch/e7.out` (11 of 22 rows, E7.md); its open rows N204, N205, N207, N212 are P12 in the search list.

**Building.** Lean through slots: `sh scratch/lean-slot.sh build <owner> <module> <expected peak GB>` (a leaf module whose SignedDifferenceSets imports are already built: checked with `lake build --no-build`, else it runs alone), `sh scratch/lean-slot.sh env <owner> <file> <peak>` (scratch files; output stops at 80 lines), `sh scratch/lean-slot.sh root <owner>` (the library root, alone). Parallel `lake build`s share the build directory, so only leaves build side by side; Lake 5.0 has no build lock of its own. Tested 2026-11-09 with 2 parallel builds (CosetRows Part36 beside a helper's builds, clean); raise to 4 after more clean runs. The old single lock (`lean-locked-big.sh`, `lenv-locked.sh`, used by agents started before) counts as one heavy job. Measured peaks: light leaf builds 3–7 GB; HalfRows heavy parts 12–14 GB; a contraction certificate checked in batches of 300,000 nodes 11.4 GB (killed), per prefix 3.9 GB: batches of 50,000 now (`solver/answer.py`). About 17 GB is free with no build and the user's usual apps. Large row files are split into parts with `set_option Elab.async false`. Generators in `solver/` write Lean row files: check `git status` on `lean/` after running one.

Results only in scratch (git-ignored):
- The worktree's `scratch/`: `e5.out`, `e6.out`, `e7.out`, `r4.out` (recorded in E5, E6, E7, E4 with SHA-256; `e7.out` still open in E7); the refuter's working folders (their reports and scripts are recorded in `reviews/`; outputs over 1 MB stay here); settle batches `settle-*.tsv`, `c26/half_rows.tsv`, `c26/even_rows.tsv`; `build-*.log`, `bench/*.lean`; `inventory/` (the plan and the inventory); `ideator/` (the six reports and their row lists, copied from the main folder). Keep.
- The **main folder's** `problems/signed-difference-sets/scratch/` (the overnight work of 2026-11-06, outside the worktree; copy it into the worktree's scratch before citing it there): the refuter's working folders of that night (recorded as [R4](reviews/R4.md)–[R9](reviews/R9.md)) and of paper P1 ([R33](reviews/R33.md)), with the downloaded papers they opened (not redistributed); `e8/` (exploration: the all-rows contraction passes, the orbit search, `turyn.py`, README); `other-session/` (another session's hand-off, N735 and N17201). Keep.

## Needs the user

- Proposed Solutions (2026-11-10; refuters SURVIVE; all rows Open in Gordon's table, settled `none` in `instances.csv`, Lean in the root, axioms standard):
  - C33, Ma's lemma at its edge (p ∣ λc; with a cyclic Sylow p of order ≥ p² and p² ∣ n, p ∣ λ): 151 rows (`MaEdgeRows`, [R40](reviews/R40.md)). Origin: ours; the method is classical (Ma's lemma, Turyn's self-conjugacy, the G/P step Feng–Leung–Schmidt–Smith use for difference sets); no SDS version found in print.
  - C32 and C35, Schmidt's field descent (one step at an odd prime; chains with odd p and p = 2): 60 + 66 rows, 21 + 62 of them not also C33's (`FieldDescentRows`, `FieldDescentChainRows`; [R39](reviews/R39.md), [R41](reviews/R41.md)). Origin: Schmidt's field descent and F-bound (Schmidt, LNM 1797, Thm 2.2.8; Tan, arXiv:1610.01914, Def 2.10, Results 2.11–2.12); the formalization and the rows: ours.
  - P3, C26 with I5's orbit search for the halved row: N7412 (and N33806, N61082, which C33 also settles). Origin: ours ([R31](reviews/R31.md) for the orbit rows).
  - C7's integer test: N27692 (`MarkedCountsInt`, [R36](reviews/R36.md)). Origin: ours.
  - C34, the divided contraction below a Ma quotient: 23 rows (26 with C35's four), `MaDividedRows` ([R42](reviews/R42.md)). Origin: ours; the method (contract, divide by p, solve the moments) is Arasu–Gordon–Zhang's for weighing matrices.
  - C37, N464 (54, 46, 10) in C₃ × C₁₈: the T-side of C26 and a pair search (`PairRows.N464`, [R44](reviews/R44.md)). Origin: ours; the λ = 0 case of the halving is Schmidt–Smith 2013 Lemma 6.2.
  - C10x, contraction certificate: N6970 (`Answer.N6970`, E8's kill rerun on committed code). Origin: ours (C3's contraction search).
- Proposed Solutions (2026-11-11; refuters SURVIVE; all rows Open in Gordon's table, settled `none` in `instances.csv`, Lean in the root, axioms standard):
  - C36, the divided contraction two levels below a Ma quotient: 32 rows (`MaDivided2Rows`, [R43](reviews/R43.md)). Origin: ours; the method is Arasu–Gordon–Zhang's for CW matrices (as C34).
  - C38 and C39, the divided vector's residue class (14 rows, `MaDividedResRows`) and value counts (52 rows, `MaCountRows`), [R46](reviews/R46.md). Origin: ours; C39's method and C38's trivial-solution analysis are Arasu–Gordon–Zhang's for CW matrices.
  - C40–C43, line tomography (I23): on Z_p × Z_p 9 rows (`TomographyRows`, [R45](reviews/R45.md)); on a Z_p × Z_p quotient 147 rows (`TomographyQuotRows`, [R47](reviews/R47.md), [R49](reviews/R49.md)); on a Z_2 × Z_2 × Z_3 quotient mod 4, 67 rows (`KleinTomographyRows`, [R48](reviews/R48.md)); through the hyperplanes of Z_p^r, 41 rows (`TomographyFlatRows`, [R49](reviews/R49.md)). Origin: the identities are folklore (Fourier inversion, the lines partition Z_p² ∖ 0); the exhaustive search over the valid contractions, its Lean form and the rows: ours (no precedent found).
  - C44, line tomography when n = p² (line contractions constant mod p): 15 rows (`TomographySquareRows`); C45, the Z_2-twist of a self-conjugate quotient: N1575 (90, 18, 2), N1593 (90, 72, 8) (`TwistSelfConjRows`); [R50](reviews/R50.md). Origin: constancy mod p for n = p² is classical (Turyn, Ma; Yayla, arXiv:1408.6883); its use with tomography, the twist argument, the Lean and the rows: ours.
- Proposed Solution: C29 (Ma's lemma with an extra self-conjugate modulus, p^b·Q > 2c): no SDS in 11 rows Gordon lists Open (N6822, N9200, N44532, N44533, N44562, N44563, N44662, N44663, N44752, N44753, N58644; `MaCombRows.n…_not_hasSDS`). Refuter SURVIVES ([R35](reviews/R35.md)). Origin: Ma's lemma (Ma 1985) with Turyn's self-conjugacy; the combination: ideator round 2, Lean proof ours; not found in print (Arasu–Ma 2001, Pott 1995, Leung–Ma–Schmidt not opened).
- CW(195, 100): user is checking literature and next steps; ask the user. (Nothing further here until the user comes back on it, 2026-11-09 22:20. Made before that, uncommitted in the worktree: Review R37 from the refuter's report (SURVIVES), claim C31, `lean/SignedDifferenceSets/CirculantWeighing.lean` (`cw195_100_not_hasSDS` and an unfolded form; builds, 23 s; not in the root).)
- Proposed Solutions (plan item P4; refuter [R34](reviews/R34.md): statements and sets SURVIVE, the credit was FLAWED for I21 and is corrected as R34 says, in `ideas/I21.md` and `objects/_objects.md`; all 16 rows are `exists`, Open in Gordon's sds.json e3bf810, Lean `Answer.N<id>.hasSDS` in the root):
  - Cyclotomic constructions (I19, ideator round 3's X1, X3): 7 rows, N236 (42, 18, 2), N1008 (75, 26, 1), N11602 (217, 112, 12) by generalized cyclotomy on products of fields; N14597 (243, 121, 40), N14828 (243, 177, 96), N31880 (343, 199, 3), N31994 (343, 247, 51) by semilinear cyclotomy (O61–O67). Origin: ours, in known frameworks; none found in print; O64 is the nonzero squares of GF(243) (Paley) minus the Berlekamp–van Lint–Seidel PDS (243, 22, 1, 2).
  - N14472 (243, 82, 1) in C₃³ × C₉ (O103): He–Chen–Ge Thm 4.1 transported to the non-split index-3 subgroup C₃⁴; the transport and the set: ours.
  - Doubling (I21): 8 rows, N448, N463 (54, ·, ·), N3539 (128, 68, 4), N931, N933, N934 (72, 40, 4), N449 (54, 38, 2), N939 (72, 48, 12) (O79–O84, O101, O104). Origin: the weighing-matrix doubling of Arasu–Leung–Ma–Nabavi–Ray-Chaudhuri 2006 Thm 2.3 (Arasu–Kotsireas–Koukouvinos–Seberry 2010 Thm 4), extended to SDS with λ ≠ 0 and twisted: ours; the sets: ours.
- Proposed corrections (plan item P5; [R7](reviews/R7.md) SURVIVES these constructions): N14604 (243, 122, 59) in C₃⁵ and N31832 (343, 172, 84) in C₇³ (Gordon's Prop 2.3, Paley and zero; O105, O106), N63319 (475, 241, 120) in C₅ × C₉₅ (Gordon's Thm 4.1, q = 19, r = 25; O107): Open in Gordon's database, settled `exists` here with Lean-checked sets.
- Proposed corrections (refuter db-lags and a5-a3, [R7](reviews/R7.md), [R5](reviews/R5.md); listed in `corrections.md` only on approval):
  - N63320 (475, 241, 120) in C₄₇₅ is "Yes" ("Prime Power Pair", no stored set) while N63319, the same parameters in C₅ × C₉₅, is Open: Gordon's Thm 4.1 at q = 19, q + 6 = 25 builds its set in GF(19)⁺ × GF(25)⁺ ≅ C₅ × C₉₅, never cyclic (GF(25)⁺ = C₅²). The two entries look swapped; C₄₇₅ should be open (not "No": nothing rules a set there out).
  - "Yes" resting only on stored sets that fail the SDS check: 148 of 279 stored sets fail, 22 keys have no valid stored set (rechecked 2026-11-07 with the reading the other 131 sets pass; 1-based indices, swapped signs and primitive-root exponents do not fix them). Valid sets are ours for 21 of the 22 (O59, O60, O68–O70, O85–O100, Lean-checked); N7891 (182, 38, 2, "assuming multiplier 3") has no valid witness anywhere. Our table keeps them `exists` on Gordon's word.
- Paper P2 (the user's; [R38](reviews/R38.md), 2026-11-09): Prop rdscomb's credit remark (`constructions.tex` l. 316–322) names neither family member Gordon's table already lists as a known cyclic set: (80, 72, 36) in C₈₀ (N1216, (2)(a), n = 8, q = 9) and (200, 151, 102) in C₂₀₀ (N9807, (2)(b), n = 4, q = 49). Wording: the citation for the (27, 17, 8) cases fits N73 (Gordon Thm 4.1, in C₃³); N74 (C₃ × C₉) is only a table entry.
- `scratch/lean-build.ps1` (the RAM watchdog) has no committed home.
- Requests for an ideator, with their reason (none so far).
