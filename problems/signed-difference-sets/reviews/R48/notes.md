# C42 refuter notes (2026-11-10)

Statement restated: SDS D on G, phi: G -> Z2 x Z2 x K onto; z = contraction to K, d_eps = twists by the 3 nontrivial
characters of Z2^2. Then autocorr(d_eps) = n*delta, d_eps = z mod 2, z + d1 + d2 + d3 = 0 mod 4 pointwise.
For K = Z3, n = 169: every d is (mod 4) +-e_j, so all d odd exactly where z is odd (one coord j); z must be 0 mod 4
off j; claim: every valid z is 2 mod 4 off j -> no SDS. 67 rows, 15 parameter sets.

## Log
- Olean freshness: every KleinTomographyRows/*.olean, KleinTomography, Tests, deps exist and are newer than sources.
- Build log scratch/tomo4/klein_build.log: 66 rows ok=1; N11534 and Params not in it (built earlier, see lean3-progress).
- kill.py over instances.csv: exactly the 67 open rows killed, 487 none, 0 exists. params.py: Params data match, hand ok.
- objtest.py: 30 objects, all onto phi, q<=6: 0 bad; mut/ control all bad.
- rows.py: 67 rows match keys, certs onto. C42Check2.lean: all67 standard axioms, no errors.
- Literature: He-Wu (abs+HTML) four obstructions, none Z2^2/mod 4; Bright 2017 Cor 1 related. Nothing settles rows.
- small12.py: v=12 exhaustive, 5 killed params all nonexistent.
- Verdict SURVIVES. Report: scratch/refuter/C42-2026-11-10-1932.md
