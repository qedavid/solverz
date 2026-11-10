# notes (refuter C37)
- 11:35 Lean re-elaboration of all C37 sources + Probe.lean launched via lanes.sh (env slot), logs in lean-out/.
- Independent search: rs/indep.rs (own indexing, support-first with parity filter, no covers/slices).
- 11:42 Probe.lean: statement probe + axioms clean (lean-out/probe.log). part4, lists, part5 re-elaborated clean.
- rs/indep: N464 216 Z, 0 pairs (also without parity filter); N449 684 Z, 252 with T, 75,168 pairs, doubled D all SDS.
- rs/small: halving holds on C6, C10, C18, C2xC3xC3, C3xC6; C14 control fails (8 sets).
- covercheck.py: covers exact (45 / 54 rotations all realised, none missing).
- Kernel checks in parts: 88 = 66 slices + 14 front-length + 8 whole groups (groups 0-7); claim's "74" = 66 + 8.
- Literature: Schmidt-Smith 2013 Lemma 6.2 (CW(v,36), D h = (1-g)X + (1+g)Y) is the lambda = 0 split.
- 11:46 Mutation.lean: the two FAIL examples fail with "decide proved ... is false"; front19 length = 15 passes;
  tw = 0 variant passes (no definite expectation; T = 0's coset vector is not in rots tList, so tStart has no start).
