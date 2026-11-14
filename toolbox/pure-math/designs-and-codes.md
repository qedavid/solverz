# Designs, codes and finite geometry
Constructions and nonexistence proofs for designs, difference sets, Hadamard matrices, projective planes and codes: cyclic developments, multipliers, quadratic-form obstructions, recursive constructions, code bounds, MacWilliams and invariant theory, zero-diagonal orthogonal matrices, two-intersection sets.

### T437 Difference sets and cyclic constructions
`find` · stage: construct · signals: group, set-family, construction
aka: difference sets, base blocks, developing a block through a group, Singer difference sets, Gordon–Mills–Welch difference sets, cyclic projective planes, symmetric designs
- What: develop a base block through a group to get a symmetric design.
- Fits when: designs, Hadamard matrices or sequences with group symmetry.
- Lean: the difference property of a given set in `ZMod n` by `decide +kernel`.
- Example: Singer difference sets give cyclic projective planes ([Wikipedia: Difference set](https://en.wikipedia.org/wiki/Difference_set)).
- See also: T438, T441, T27, T1389, T1391, T1392

### T438 Multiplier theorems and character sums for nonexistence
`prove` · stage: argue · signals: group, set-family, impossibility
aka: Hall's multiplier theorem, McFarland's multiplier theorem, multiplier orbits, fixed translates, group-ring equations, characters of abelian groups, Fourier criterion, contraction to quotients, circulant Hadamard matrices, difference set nonexistence, Muzychuk's multiplier transfer, Newman–Turyn n = 2q^a, McFarland's N(n) theorem, normalized solutions, extraneous multipliers, Frobenius criterion D^p ≡ gD mod p, Ko's multiplier theorem, fixed subgroup of a multiplier, sub-difference set on the fixed points, orbit lengths of differences, Adin–Epstein–Strassler
- What: group-ring and character arguments force multipliers and rule out parameters.
- Fits when: deciding which difference sets or circulant matrices exist.
- Lean: —
- Example: Hall's multiplier theorem; nonexistence results for circulant Hadamard matrices ([Wikipedia: Difference set](https://en.wikipedia.org/wiki/Difference_set), [Wikipedia: Hadamard matrix](https://en.wikipedia.org/wiki/Hadamard_matrix)).
- See also: T437, T439, T748, T1378, T1379, T1380, T1384, T1404, T1406, T1407

### T439 Number-theoretic obstruction via quadratic forms
`prove` · stage: argue · signals: matrix, integers, impossibility
aka: Bruck–Ryser–Chowla theorem, Bose–Connor theorem, divisible designs, Hasse–Minkowski invariants, Hilbert symbols, rational equivalence of quadratic forms, BRC on quotients, Hall–Ryser test, orbit matrices, Hughes's theorem, symmetric designs, projective plane of order 6
- What: an incidence matrix gives a rational equivalence of quadratic forms; Hasse–Minkowski invariants must match.
- Fits when: excluding parameters of symmetric designs or planes.
- Lean: —
- Example: Bruck–Ryser–Chowla: no projective plane of order 6 ([Wikipedia: Bruck–Ryser–Chowla theorem](https://en.wikipedia.org/wiki/Bruck–Ryser–Chowla_theorem)).
- See also: T513, T410, T7, T1379

### T440 Recursive constructions
`find` · stage: construct · signals: set-family, product-structure, construction
aka: product constructions, products of relative and Hadamard difference sets, Turyn's composition, PBD closure, pairwise balanced designs, Wilson's fundamental construction, orthogonal Latin squares, Graeco-Latin squares, Euler's 36 officers, product with a filler, core products (Belevitch, Ehlich), cross-correlation products
- What: combine small designs into large ones; Wilson's fundamental construction.
- Fits when: existence for all large admissible parameters once enough small cases exist.
- Lean: each small ingredient as a witness by `decide +kernel`; the recursion as a Lean construction.
- Example: Bose–Shrikhande–Parker: orthogonal Latin squares exist for all orders except 2 and 6 ([Wikipedia: Graeco-Latin square](https://en.wikipedia.org/wiki/Graeco-Latin_square), [Wikipedia: Combinatorial design](https://en.wikipedia.org/wiki/Combinatorial_design)).
- See also: T441, T360, T446, T1392, T1396, T1408

### T441 Hadamard matrix constructions
`find` · stage: construct · signals: matrix, finite-field, construction
aka: Hadamard matrices, Sylvester doubling, Kronecker product, Paley construction, quadratic residues, Williamson arrays, Williamson matrices, Hadamard conjecture
- What: Sylvester doubling, Paley quadratic residues, Williamson arrays.
- Fits when: orthogonal ±1 matrices of given order.
- Lean: Mathlib: `Matrix.IsHadamard` with `Matrix.IsHadamard.kronecker` (Sylvester) and the `4 ∣ n` obstruction (`LinearAlgebra/Matrix/HadamardMatrix.lean`); a concrete matrix by `decide +kernel`.
- Example: Paley's constructions from finite fields ([Wikipedia: Hadamard matrix](https://en.wikipedia.org/wiki/Hadamard_matrix)).
- See also: T437, T440, T39, T1389, T1390

### T442 Codes from groups and designs from codes
`find` · stage: construct · signals: group, set-family, construction
aka: extended Golay code, Mathieu group M24, Steiner system S(5,8,24), 5-designs, codewords of fixed weight
- What: code words of fixed weight form designs; automorphism groups give exceptional designs.
- Fits when: constructing 5-designs, Steiner systems.
- Lean: the design property of an explicit block list by `decide +kernel` at small size.
- Example: the Steiner system S(5,8,24) from the extended Golay code and the Mathieu group M24 ([Wikipedia: Steiner system](https://en.wikipedia.org/wiki/Steiner_system)).
- See also: T437, T444

### T443 Sphere-packing and averaging bounds for codes
`bound` · stage: argue · signals: set-family, inequality
aka: Hamming bound, sphere-packing bound, Plotkin bound, Gilbert–Varshamov bound, error-correcting codes, minimum distance
- What: Hamming (packing), Plotkin (double counting distances), Gilbert–Varshamov (greedy/random).
- Fits when: first bounds on code size at a given distance.
- Lean: Mathlib: `hammingDist` (`InformationTheory/Hamming.lean`); the counting by `Finset` sums.
- Example: Plotkin's bound by summing pairwise distances ([Wikipedia: Plotkin bound](https://en.wikipedia.org/wiki/Plotkin_bound), [Wikipedia: Hamming bound](https://en.wikipedia.org/wiki/Hamming_bound), [Wikipedia: Gilbert–Varshamov bound](https://en.wikipedia.org/wiki/Gilbert–Varshamov_bound)).
- See also: T327, T50, T53

### T444 MacWilliams duality
`prove` `compute` · stage: argue · signals: set-family, polynomial, identity
aka: MacWilliams identity, weight enumerators, dual codes, self-dual codes, code of a design, nonnegativity of dual weight counts
- What: the weight enumerator of a code determines that of its dual.
- Fits when: self-dual codes and nonexistence via nonnegativity of dual weight counts.
- Lean: —
- Example: MacWilliams identity ([Wikipedia: MacWilliams identity](https://en.wikipedia.org/wiki/MacWilliams_identity)).
- See also: T445, T50, T1386

### T445 Invariant theory of weight enumerators
`prove` `bound` · stage: argue · signals: polynomial, group, set-family
aka: Gleason's theorem, Molien series, invariant rings of finite groups, self-dual codes, minimum distance bounds
- What: weight enumerators of self-dual codes lie in a ring of invariants of a finite group (Gleason), computable by Molien series.
- Fits when: bounding minimum distance of self-dual codes.
- Lean: —
- Example: Molien's formula for the Hilbert series of an invariant ring, the engine of Gleason-type theorems ([Wikipedia: Molien series](https://en.wikipedia.org/wiki/Molien_series)).
- See also: T444, T568

### T446 Explicit resolvable constructions
`find` · stage: construct · signals: set-family, finite-field, construction
aka: resolvable designs, Kirkman triple systems, Kirkman's schoolgirl problem, Ray-Chaudhuri–Wilson, scheduling designs, parallel classes
- What: build resolutions by cyclic or finite-geometry patterns.
- Fits when: scheduling-type designs.
- Lean: an explicit resolution by `decide +kernel` at small size.
- Example: Kirkman's schoolgirl problem and Ray-Chaudhuri–Wilson's general solution ([Wikipedia: Kirkman's schoolgirl problem](https://en.wikipedia.org/wiki/Kirkman's_schoolgirl_problem)).
- See also: T440, T437

### T1411 Zero-diagonal orthogonal matrices: symmetric or skew
`prove` · stage: argue · signals: matrix, parity, impossibility
aka: Delsarte–Goethals–Seidel normal form, conference matrices, symmetric or skew, zero-diagonal ±1 matrices, W(n, n − 1), one zero per row, Belevitch's sign product, k = v − 1, Arasu–Jungnickel–Ma–Pott classification, λ − μ = −1
- What: a ±1 matrix with zero diagonal and MMᵀ = mI + (v − 1 − m)J (m ≠ v − 1) has an equivalent normal form B with constant row and column sums that is symmetric or skew: counting the four sign patterns of two rows outside their zeros gives 4n₁ = m − 1 − (b_ij − b_ji), so m is odd and b_ji = (−1)^((m−1)/2)b_ij; in the symmetric case the trace gives b + (a − c)√m = 0, so m is a square when b ≠ 0, and for a group-developed matrix the support of one sign is a PDS with λ − μ = −1.
- Fits when: conference matrices and group-developed matrices with exactly one zero per row, any group; for {0, ±1} solutions with k = v − 1 the same count gives n odd, n ≡ 3 mod 4 forcing a skew element with λ = −1, n ≡ 1 mod 4 a symmetric one up to translation with n a square when λ ≠ −1, and the PDS classification then lists the abelian cases.
- Lean: the four-pattern count proved once on ±1 vectors; each parameter consequence by `decide +kernel`.
- Example: orthogonal matrices with zero diagonal ([Delsarte–Goethals–Seidel 1971](https://doi.org/10.4153/CJM-1971-091-X)); every abelian PDS with λ − μ = −1 has Paley parameters or (243, 22, 1, 2) up to complement ([Arasu–Jungnickel–Ma–Pott 1994](https://doi.org/10.1016/0097-3165(94)90007-8)).
- See also: T1388, T401, T1387, T1389

### T1412 Projective two-intersection sets
`find` `prove` · stage: reformulate · signals: finite-field, geometry, set-family
aka: projective two-intersection sets, two-weight codes, Calderbank–Kantor dictionary, Delsarte, point sets of PG(n − 1, q), hyperplane sums, cyclotomy of projective lines, uniform cyclotomy, F_q*-invariant sets, strongly regular Cayley graphs
- What: a point set of PG(n − 1, q) meeting every hyperplane in one of two sizes is the same as a projective two-weight code and as a PDS in F_q^n invariant under F_q*; in cyclotomic terms the classes α^iF_q* of F_(q^n)* are the points, cyclotomic numbers of order (q^n − 1)/(q − 1) are 0 or 1 by collinearity, and a weighted point set has character values given by its hyperplane sums.
- Fits when: strongly regular graphs, two-weight codes and cyclotomic constructions invariant under F_q*; a {0, ±1} weighting w of the points (and of 0) is flat iff its hyperplane sums take two values a, b with q(a − b) = 2√n, or one value; for q odd such elements are symmetric, which leaves only k ∈ {0, 1, v − 1, v}, so the reduction helps for q = 2^f, f ≥ 2.
- Lean: the hyperplane sums of a given weighting by `decide +kernel`.
- Example: the geometry of two-weight codes ([Calderbank–Kantor 1986](https://doi.org/10.1112/blms/18.2.97)); cyclotomic numbers of projective lines beyond uniform cyclotomy ([Huczynska–Johnson–Paterson 2025](https://doi.org/10.1016/j.ffa.2025.102604)).
- See also: T444, T1383, T1388, T1391
