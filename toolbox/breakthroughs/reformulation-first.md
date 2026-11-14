# A reformulation first
Nearly every solution starts from an equivalent or stronger restatement in another language (S57–S62, S67, S68; also S17, S30, S45); the reformulation, often by someone else, is what made the problem attackable. Outsiders enter through it: the reduction is the door.
Stuck on the problem as stated: restate it as a graph, matrix, incidence or stronger claim, and read the reductions others already made.

### S57 Fermat's Last Theorem
Stuck: 1637–1995 · `prove` · used: T524, T525, T532, T1369
- Unlock: a counterexample gives a Frey curve, which cannot be modular (Serre's epsilon conjecture, proved by Ribet 1986); Wiles proved semistable modularity. His failed Kolyvagin–Flach step was fixed in 1994 with Iwasawa theory and Taylor (failure as information).
- From: arithmetic geometry (Taniyama–Shimura–Weil), replacing 300 years of elementary attacks.
- Source: [Wikipedia: Wiles's proof](https://en.wikipedia.org/wiki/Wiles%27s_proof_of_Fermat%27s_Last_Theorem)

### S58 Kahn–Kalai conjecture
Stuck: 2006–2022 · `prove` · used: T363
- Unlock: work with covers instead of the expectation threshold; build a small cover by piece-by-piece random sampling and counting (Park–Pham). Six pages, found in one sleepless night; the conjecture's authors had doubted it.
- From: "spread" techniques from the 2019 sunflower breakthrough, born in theoretical computer science.
- Source: [Quanta](https://www.quantamagazine.org/elegant-six-page-proof-reveals-the-emergence-of-random-structure-20220425/), [arXiv:2203.17207](https://arxiv.org/abs/2203.17207), [Wikipedia: Sunflower](https://en.wikipedia.org/wiki/Sunflower_(mathematics))

### S59 Bieberbach conjecture
Stuck: 1916–1984 · `prove` · used: T302, T703, T1310, T1342
- Unlock: prove the stronger Milin conjecture (de Branges); the needed positivity of Jacobi sums was checked by computer, then found already proved by Askey–Gasper (1976): an overlooked simple tool.
- From: special functions.
- Source: [Wikipedia: De Branges's theorem](https://en.wikipedia.org/wiki/De_Branges%27s_theorem)

### S60 Erdős distinct distances
Stuck: 1946–2010 · `bound` · used: T739, T396, T397
- Unlock: Elekes–Sharir turn distances into line incidences in R³; polynomial ham-sandwich cell decomposition, Salmon's flecnode polynomial and ruled surfaces give N/log N.
- From: 19th-century algebraic geometry, in the wake of the polynomial method.
- Source: [Wikipedia: Erdős distinct distances problem](https://en.wikipedia.org/wiki/Erd%C5%91s_distinct_distances_problem), [arXiv:1011.4105](https://arxiv.org/abs/1011.4105)

### S61 Hilbert's tenth problem
Stuck: 1900–1970 (negative answer) · `prove` · used: T771
- Unlock: Davis–Putnam–Robinson reduced it to one Diophantine relation of exponential growth (Robinson's hypothesis, open 20 years); Matiyasevich supplied it with Fibonacci numbers.
- From: computability theory.
- Source: [Wikipedia: Hilbert's tenth problem](https://en.wikipedia.org/wiki/Hilbert%27s_tenth_problem)

### S62 Stanley–Wilf conjecture
Stuck: late 1980s–2004 · `prove` · used: T304, T842
- Unlock: Klazar (2000) showed that the Füredi–Hajnal conjecture on 0-1 matrices implies it; Marcus–Tardos then proved Füredi–Hajnal.
- From: someone else's reduction to 0-1 matrices.
- Source: [Wikipedia: Stanley–Wilf conjecture](https://en.wikipedia.org/wiki/Stanley%E2%80%93Wilf_conjecture)

### S67 (16, 4, 16, 4) relative difference sets of order 64
Stuck: to 2013 · `compute` · used: T1394, T30
- Unlock: such a relative difference set is the same as a class-regular symmetric (4, 4)-net with a regular automorphism group containing the forbidden subgroup; the nets were already classified, so listing the regular subgroups of order 64 in each net's automorphism group decides every group: 6 of the 11 abelian and 195 of the 256 nonabelian groups carry one.
- From: finite geometry (nets), then computational group theory.
- Source: [Clark–Tonchev 2013](https://doi.org/10.37236/2776)

### S68 Lin's conjecture
Stuck: 1998–2014 · `prove` · used: T1400, T1383
- Unlock: a second-order decimation-Hadamard transform writes the two-level autocorrelation of the ternary sequence as sums of products of Gauss sums; Stickelberger turns divisibility of every value by 3ⁿ into a base-3 digit-sum inequality, one more digit shows no value vanishes, and Parseval then forces every value to have modulus 3ⁿ; what remains is digit combinatorics.
- From: Gauss sums and p-adic valuations inside sequence design.
- Source: [Hu–Shao–Gong–Helleseth 2014](https://doi.org/10.1109/TIT.2014.2327625)
