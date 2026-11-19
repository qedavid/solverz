# C6x refuter notes
- 21:30 Check.lean (lean-slot env, 36 s): axioms clean on 5 theorems; rfl: statement group = Grp [2,4,40];
  search evals: k=306 all false, k=304 true at t0=0 both signs, k=305 false; order-independence ok; Valid by decide ok.
- intdp.py: independent DP agrees (304 max, LP 306.4).
- controls.py: 229 exists rows, 181 certs run, 2 skipped (size), 0 kills. Report findings 1, 2 written.
- Row N27692 in instances.csv: key SDS(320,306,162,[2,4,40]), status open (line 27693). Matches.
- Root SignedDifferenceSets.lean does NOT import MarkedCountsInt (nor its Tests): process finding to write.
- PAUSED 21:4x on coordinator's request. Still to do: finding on root import (process), finding on Lean statement reading
  (CountsOk/IsSDS.countsOk/anyCounts_of/orderVals/countSum_countOf all proved; read literally), axioms finding (done in
  Check.lean log: all 5 clean), object-level check of real coset sums (optional), literature search (check 5), verdict.
- Handback forced: findings 3-5, literature (not done), verdict written. Run ends.
- Coordinator correction: pause without handback. The report's "Literature" and "Verdict" sections are PROVISIONAL
  (written under a forced-handback prompt). On continue: do the literature search (check 5), then append a final
  "Verdict (final)" section superseding the provisional one; optional: object-level coset-sum check of stored sets.
- 21:41 continued. Literature: He-Wu 2608.22936v2 HTML (Lemma 4.1 = coset bound with parity; no count-vector enumeration;
  none of Thms 3.2/4.2/4.4/4.7 applies to N27692; v=320 absent). Arasu-Gordon-Zhang 1908.08447 (ar5iv): integer
  intersection-number solutions enumerated, no support/parity. Next: objects.py (stored sets' coset sums), final verdict.
- 21:50 findings 6, final literature, final verdict written. Handing back.
