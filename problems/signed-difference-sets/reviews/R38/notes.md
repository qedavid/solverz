# E14 refuter notes (2026-11-09)
Started 22:20. Brief: scratch/refuter/e14-brief.md. Five checks on P2's paper-only statements.
- sdslib.py validated: reproduces (v,k,lam) of O6,O7,O8,O10,O40-O58; rejects perturbed O6, O57.
- check1_semi.py (check1_semi.out): every semiregular RDS in abelian groups of order 8 (C8: 0; C2xC4: 12; C2^3: 28) and 27
  (C27: 0; C3xC9: 216 = 4 subgroups x 54; C3^3: 2106 = 13 x 162), normalized 0 in R: R-N and G-R-N are SDS with the claimed
  parameters in all 2362 cases. The paper's two algebraic RDSs ((x,y,xy) in F_p^3; (x+pxy,y) in Z_p2 x Z_p) are RDSs for p=2,3,5,7
  and give the claimed SDSs. Group-ring algebra rederived by hand: matches C30's proof line by line.
- check1_shape.py (check1_shape.out): O40-O42, O47-O52 are translates of R - N; O43-O46, O53-O56 of G - R - N (semiregular R
  verified as RDS); O57 = G - 2R - N, O58 = G - R - 2N (affine R verified as RDS). All 19 have the stated shape.
- Table: (80,72,36) in C80 = N1216 (Yes, Gordon: Orbit Exhaust w/ forced multiplier) is (2)(a) at n=8, q=9; (200,151,102) in
  C200 = N9807 (All, Gordon: Orbit Exhaust) is (2)(b) at n=4, q=49. P2's credit sentence names only (20,11,2), (78,53,28).
- check1_affine.py (check1_affine.out): own GF(q^2) + Bose RDS for every prime power q <= 49 and every n | q-1, n >= 2: RDS
  verified; G-2R-N SDS exactly at (q,n) = (9,8) [80,72,36], (25,12) [312,300,200], (49,16) [800,784,588]; G-R-2N exactly at
  (9,2) [20,11,2], (25,3) [78,53,28], (49,4) [200,151,102]; R-N exactly at Q=(n+1)^2 (thm rdsfamily). Matches the conditions.
- Gordon arXiv 2212.10630v1 HTML Table 1 (opened): cyclic sporadic SDSs; has (20,11,2), (78,53,28), (51,19,3), (104,29,4);
  not (80,72,36) nor (200,151,102) (those are in Gordon's online table as orbit-exhaust results: N1216, N9807).
- He-Wu 2608.22936v2 Thm 5.6 (opened): D = P - {0}xF5* via quartic characters; check3_hewu.py: P + {0} IS a semiregular
  (25,5,25,5) RDS rel {0}xF5, so "of the shape of (1)" is right. He-Wu/He-Chen-Ge do not mention RDSs.
- check3_hewu.py: P2's (25,12,1) set is an SDS; O6(Ax+t) = D(x) with A = [[0,4],[1,2]], t = (1,3), sign +1 (3 such maps).
- check2_o8.py (check2_o8.out): O8 = (0,5) + (R - N), N = <(1,3)>, R = {0,(0,4),(1,0),(1,1),(2,0),(2,2),(2,5),(2,7),(2,8)}
  a (9,3,9,3) RDS (verified). Unique decomposition. |Aut(C3xC9)| = 108; the 216 normalized R - N sets fall in 3 classes
  (108, 54, 54) under Aut x translation x sign; O8 is in one. O7 (C3^3) has no R - N decomposition (shape is Aut-invariant).
- check4_z17.py (check4_z17.out): closed form == z17 hypothesis == Lean RcCert tail on 293,280 triples (r 1..8, |m|<=70,
  0<=s<260), monotone in r; z17 kill <=> z25a(q=2 or 4, max b) or z25b kill on H = C2^t, same range, 0 mismatches.
  213 Lean rows (+1 test example parsed): all use r = R, keys match instances.csv, all Open@. Open rows z17 kills for some
  r <= R: 270 (213 rows + 57 not rows, presumably settled earlier); none killed at r < R but not at R.
  Largest b formula after z25a (ceil(e/2), phi >= 2) verified for e < 40.
- check5_z18.py (.out): all 67,823 Open@ rows; 11,094 with square n, square s^2 and G/4G != 0; every exponent-4 quotient
  type C2^a x C4^b of G (orders 2..256): weak (all R, = Lean GaussKills) settles 629 rows, strong (true R = 2^(a+b)) 629,
  0 differences. All 70,543 rows (check5_allrows.out): 629 / 629, 0 differences. Lean GaussCharsRows' 297 quotients have
  order 8 (90), 16 (155), 32 (52); all kill under both versions.
- check5_validate.py: my kill matches R18's decide results (8 4 8 kills; 8 4 12, 16 4 12, 4 3 9, 4 2 2, 1 3 5 do not);
  no exists row is killed (strong) at any quotient. Count with a C4 factor, N <= 64, Open@ rows: 408 (R18 F4 says 347 over
  "open rows", apparently a different row set; not pursued).
- Z3Cyclo.lean: the (25,12,1) set defined cyclotomically in Lean, IsSDS by decide; started via lean-slot (log Z3Cyclo.log).
- Z3Cyclo.lean compiled via lean-slot (22:40, 43 s): no errors; hasSDS axioms propext, Classical.choice, Quot.sound.
