# Difference sets and group-ring methods
Character-value and group-ring methods for difference sets, relative and partial difference sets, group weighing matrices and ±1 arrays: cyclotomic integers, self-conjugacy, Ma's lemma, exponent bounds, field descent, Stickelberger, contractions, modular codes; constructions from cyclotomy, building sets, cocycles, transfers and switching. Multipliers, BRC and the basic constructions are in designs and codes (T437–T446).

### T1378 Modulus equation in cyclotomic integers
`prove` · stage: argue · signals: group, integers, impossibility
aka: character values as cyclotomic integers, XX̄ = n, Kronecker's theorem, roots of unity, prime ideal factorization in Q(ζ_m), ideal-class obstruction, principal ideals, cyclotomic integers of prescribed absolute value, ramified primes
- What: each character value X of a group-ring solution solves XX̄ = n in Z[ζ_m]; the prime-ideal factorization of n, Kronecker's theorem (an algebraic integer whose conjugates all have modulus 1 is a root of unity) and the class group list the possible X up to roots of unity; for n = p^b with p | m they are elements of a smaller cyclotomic ring or Gauss sums times smaller solutions.
- Fits when: difference sets, relative difference sets, circulant Hadamard and weighing matrices in abelian groups, when the possible character values decide existence; the equation is the same for {0, ±1} solutions.
- Lean: Mathlib: `IsCyclotomicExtension`, `NumberField.classNumber`; a divisibility in Z[ζ_m] as an integer-polynomial identity modulo the cyclotomic polynomial, checked by `decide +kernel`.
- Example: Schmidt's class-group criterion for cyclotomic integers of prescribed absolute value ([Schmidt 1998](https://doi.org/10.1006/jnth.1998.2275)).
- See also: T438, T517, T1379, T1382

### T1379 Self-conjugacy and the Mann test
`prove` · stage: argue · signals: group, integers, impossibility, congruence
aka: self-conjugate primes, Turyn's self-conjugacy, p^j ≡ −1 mod exp G, semiprimitive primes, decomposition groups, decomposition fields, Mann test, even p-part of n, coset sums congruent mod p^b
- What: if some power of p is −1 modulo the p-free part of the group exponent, every prime ideal above p is fixed by complex conjugation, so XX̄ ≡ 0 mod p^(2b) forces X ≡ 0 mod p^b; then the exact p-part of n is a square (Mann) and the coset sums on a quotient of order prime to p agree mod p^b.
- Fits when: nonexistence when n has a factor p^(2b) with p self-conjugate modulo the exponent of a quotient; for {0, ±1} solutions the coset sums lie in [−c, c], so they all agree once p^b > 2c.
- Lean: elementary in F_p[H]: the Frobenius power y^(p^i) = ȳ and yȳ = 0 give y = 0; prove it once, then check each instance's prime, quotient and exponents by `decide +kernel`.
- Example: Turyn's self-conjugacy theorem ([Turyn 1965](https://doi.org/10.2140/pjm.1965.15.319)); the Mann test ([Mann 1964](https://doi.org/10.1215/ijm/1256059669)).
- See also: T1378, T1380, T1381, T438

### T1380 Ma's lemma and inversion with divisibility
`prove` · stage: argue · signals: group, integers, congruence
aka: Ma's lemma, Ma tower, polynomial addition sets, Yamamoto's congruence criterion, Ma–Pott lemma, Legendre vector, Fourier inversion with divisibility, coset-constant coefficients, divided contraction, cyclic Sylow subgroups
- What: if every character value of Y ∈ Z[G] whose order is divisible by |S| (S a cyclic Sylow p-subgroup) is divisible by p^a, then Y = p^a X₁ + P X₂ with P of order p, layered as Σ p^(a−i) P_i X_i; for t prime to |H|, t dividing every nontrivial character value gives Y ≡ xH mod t; on a cyclic p-group with |χ(Y)|² = p^s the shape of Y is explicit (a p-power times a Legendre vector for p and s odd).
- Fits when: turning divisibility of character values into coefficient structure on quotients with a cyclic Sylow subgroup; no sign hypothesis is used, so it holds for {0, ±1} solutions (only X₁, X₂ ≥ 0 is lost).
- Lean: the cyclotomic input as a Bézout certificate (X − 1)^N f + Ψ g = p in ℤ[X], checked coefficientwise by `decide +kernel`; the lemma itself proved once on a quotient ring.
- Example: Ma's lemma ([Ma 1985](https://doi.org/10.5353/th_b3123054)), used for (p^a, p, p^a, p^(a−1)) relative difference sets ([Ma–Schmidt 1995](https://doi.org/10.1007/bf01390771)).
- See also: T1379, T1381, T1384, T438

### T1381 Exponent bounds
`prove` `bound` · stage: argue · signals: group, integers, impossibility, inequality
aka: Turyn's exponent bound, size argument, coefficient bound on a cyclic quotient, Arasu–Davis–Jedwab, complement counting, coset intersection lemma, character divisibility property, exp G ≤ C√|G|, Hadamard difference sets, McFarland difference sets
- What: when self-conjugacy (or √n dividing every character value) makes the image on a quotient with cyclic Sylow p-subgroup divisible by p^a, Ma's lemma forces a coefficient of size at least p^a, so the Sylow p-subgroup cannot have large exponent; counting the images under many complements of a cyclic factor, or combining many quotients, sharpens the bound.
- Fits when: bounding the exponent of abelian groups that can carry difference sets, relative difference sets or perfect arrays; for {0, ±1} solutions only the quotient form survives: the image is constant on cosets once p^a exceeds the coefficient range 2c.
- Lean: as T1379: the quotient form proved once, each instance's prime, quotient and exponent checked by `decide +kernel`.
- Example: Turyn's bound exp G ≤ 2^(a+2) for Hadamard difference sets in abelian groups of order 2^(2a+2), sharp by Kraemer ([Kraemer 1993](https://doi.org/10.1016/0097-3165(93)90012-W)); under self-conjugacy McFarland sets need an elementary abelian Sylow p-subgroup for odd p ([Ma–Schmidt 1995](https://doi.org/10.1016/0097-3165(95)90096-9)).
- See also: T1379, T1380, T1382, T441

### T1382 Field descent
`prove` `bound` · stage: argue · signals: group, integers, impossibility, inequality
aka: Schmidt's field descent, F(m, n), fixing theorem, F-bound, descent to a Gaussian-period subfield, quadratic subfield, Chan's method, Arasu–Pott bound, Yamamoto's test 4n = x² + qy², circulant Hadamard matrices, Barker sequences, skew Hadamard difference sets
- What: a solution of XX̄ = n in Z[ζ_m] becomes, after multiplying by a root of unity, an element of the smaller field Q(ζ_F) with F = F(m, n) read off the prime factorizations; coefficients in [0, C] then give n ≤ C²F²/(4φ(F)); where X lies in a Gaussian-period or imaginary quadratic subfield, a norm form must represent n, such as 4n = x² + qy².
- Fits when: n is small against the exponent of a cyclic quotient: circulant Hadamard and weighing matrices, Barker sequences, cyclic difference sets; the descent concerns X alone, so it holds for {0, ±1} solutions with C = 2c on a quotient with fibres of size c.
- Lean: in the unramified case the bound φ(m)n ≤ mFc² follows from multipliers and Parseval on functions G → ℤ; each instance's F checked by `decide +kernel`.
- Example: no circulant Hadamard matrix of order 4 < v ≤ 10¹¹ except possibly v = 4u², u ∈ {165, 11715, 82005} (Schmidt 2002, Characters and Cyclotomic Fields in Finite Geometry); the general method ([Leung–Schmidt 2005](https://doi.org/10.1007/s10623-004-1703-7)).
- See also: T1378, T1381, T1383, T530

### T1383 Stickelberger's theorem for character values
`prove` · stage: argue · signals: finite-field, integers, congruence
aka: Stickelberger's theorem, prime-ideal factorization of Gauss sums, p-adic valuation of Gauss sums, p-digit sums, Gross–Koblitz, Jacobi sums, semiprimitive case, two-weight irreducible cyclic codes, derived difference sets
- What: the prime ideals above p divide a Gauss sum over F_q to powers given by p-digit sums of its exponent, so the exact p-power dividing the character values of sets built from cyclotomic classes or traces is computable; p is semiprimitive exactly when that minimum is half the degree.
- Fits when: candidates from cyclotomic classes, Singer-type traces or Gauss sums, where exact divisibility of character values decides the structure, as for two-weight irreducible cyclic codes.
- Lean: Mathlib: `gaussSum`; the factorization by hand.
- Example: Stickelberger's theorem (Berndt, Evans, Williams 1998, Gauss and Jacobi Sums); with two-valued contractions it gives the numerical criterion for two-weight irreducible cyclic codes (Schmidt 2002, Characters and Cyclotomic Fields in Finite Geometry).
- See also: T530, T1382, T1384, T1391

### T1384 Contractions and intersection numbers
`prove` · stage: argue · signals: group, integers, impossibility
aka: contracted difference sets, homomorphic images, coset sums, intersection numbers, second-moment identity, difference lists, small-exponent quotients, real, Gaussian and Eisenstein characters, two-valued contraction, derived difference sets, Mullin's mod-4 rule
- What: the image of D on a quotient G/U has a fixed coefficient sum, sum of squares n + λ|U| and constant cross-sums λ|U|; on quotients whose characters take values in Z, Z[i] or Z[ω] the few solutions of zz̄ = n invert to explicit linear conditions on the coset sums, and an image with only two values is a smaller difference set.
- Fits when: first necessary conditions for difference sets and their relatives in groups with small quotients; no sign hypothesis is used, so they hold for {0, ±1} solutions with coset sums in [−c, c].
- Lean: the contraction identity proved once on functions G → ℤ; the excluded integer vectors on a quotient by `decide +kernel`.
- Example: a (16, 6, 2) difference set in Z₄ × Z₄ meets the cosets of a Z₄ quotient in (1, 1, 1, 3) or (2, 2, 2, 0) elements (Moore, Pollatsek 2013, Difference Sets: Connecting Algebra, Combinatorics, and Geometry).
- See also: T438, T1380, T1385, T1397

### T1385 Affine-geometry sieve on elementary abelian quotients
`prove` · stage: argue · signals: group, geometry, impossibility
aka: Iiams–Liebler–Smith sieve, line tomography, hyperplane collapses, weighted planes, special lines, weaving a cyclic factor, AG(2, p), AGL(2, p), moment equations of special hyperplanes, Lander's tables
- What: on a quotient C_p^r every hyperplane collapse must be a viable image on the smaller quotient; the line–point incidence of AG(2, p) (AᵀA = pI + J) rebuilds point weights from the p + 1 line contractions, a modulus that isolates one value per parallel class marks special lines, and the rest is settled by classifying weighted planes up to AGL(2, p) and counting plane types two ways.
- Fits when: nonexistence of difference sets in groups with an elementary abelian quotient of rank at least 2 where character values alone do not decide; the reconstruction holds for {0, ±1} solutions with signed weights in [−c, c].
- Lean: the reconstruction identity proved once; each excluded weighted plane or array by `decide +kernel`.
- Example: Iiams's completion of Lander's tables of abelian difference sets ([Iiams 1999](https://doi.org/10.1007/978-94-011-4459-9_10)).
- See also: T1384, T1397, T29

### T1386 Codes and p-ranks over the group algebra
`prove` · stage: argue · signals: group, matrix, finite-field, impossibility
aka: p-rank of a design, codes of difference sets, ideals of F_p[G], self-orthogonal codes, Lander's p-adic codes, Smith normal form symmetry, Frobenius multiplier, halving a cyclic Sylow p-subgroup, Wilbrink's theorem, linear complexity, Hamada's conjecture
- What: reduce the incidence or group matrix mod p: for p ∤ |G| its rank counts the characters with χ(D) ≢ 0 mod p; for p | n the rank is at most (v + 1)/2 and BBᵀ = nI + λJ makes the invariant factors symmetric (Lander's chain of codes); in F_p[G] the multiplier p and the vanishing of reversible self-orthogonal ideals give identities such as Wilbrink's.
- Fits when: p divides n and the group order, or p is a multiplier; ranks also tell apart designs with equal parameters; for {0, ±1} solutions the code is self-orthogonal exactly when p | n and p | λ.
- Lean: Mathlib: `Submodule.smithNormalForm`; a rank or Smith form of a given matrix as U·A·V = D with unimodular U, V, checked by `decide +kernel`.
- Example: Lander's p-adic codes of symmetric designs (Lander 1983, Symmetric Designs: An Algebraic Approach); p-ranks of cyclic difference sets from Gauss and Jacobi sums ([Evans–Hollmann–Krattenthaler–Xiang 1999](https://doi.org/10.1006/jcta.1998.2950)).
- See also: T410, T444, T445, T1383

### T1387 Structure of group weighing matrices
`prove` · stage: argue · signals: matrix, group, parity, impossibility
aka: circulant weighing matrices, CW(n, k), Eades' parity bound, zero patterns, Arasu–Ma reduction, weight p², support in a proper subgroup, proper circulant weighing matrices
- What: two rows of a weighing matrix W(n, k) of odd order have zero patterns meeting an odd number of times, so (n − k)(n − k − 1) ≥ n − 1, with equality only when the zero pattern is a projective plane; for weight p² on a cyclic group a translate lives on a proper subgroup, which reduces the order.
- Fits when: existence of circulant or group-developed weighing matrices of given order and weight; the parity count uses only the parity of the off-identity correlation and the support size, so it holds for {0, ±1} solutions with v odd and λ even, equality making the zeros a planar difference set.
- Lean: the parity count proved once over `ZMod 2`; reduced instances by `decide +kernel`.
- Example: Arasu–Ma's localization for weight p² rules out CW(55, 25), CW(133, 49) and others ([Arasu–Dillon 1999](https://doi.org/10.1007/978-94-011-4459-9_1)); Eades' bound (Seberry 2017, Orthogonal Designs: Hadamard Matrices, Quadratic Forms and Algebras).
- See also: T1389, T441, T39

### T1388 Paley-type partial difference sets and conference matrices
`prove` `find` · stage: argue · signals: group, graph, impossibility
aka: partial difference sets, PDS, strongly regular Cayley graphs, Paley-type PDS, Paley graphs, conference matrices, conference cores, skew Hadamard matrices, Turyn–Belevitch product
- What: in an abelian group of order p^(2s+1), p ≡ 1 mod 4, a Paley-type partial difference set meets every subgroup H in (|H| − 1)/2 elements; with its multipliers and congruences in Q(√p) this bounds the exponent (groups of order p³ and p⁵ must be elementary abelian); conference cores of equal order multiply to larger ones.
- Fits when: strongly regular Cayley graphs, Paley-type sets and conference matrices with an abelian regular group; through 2D + 1 − G a Paley-type set is the same as a symmetric {0, ±1} solution with parameters (v, v − 1, −1).
- Lean: a given set's PDS property by `decide +kernel` on its difference counts.
- Example: Ma's survey of partial difference sets ([Ma 1994](https://doi.org/10.1007/BF01388454)); Paley-type sets in groups of order n⁴ and 9n⁴ for every odd n > 1 ([Polhill 2010](https://doi.org/10.1016/j.jcta.2010.03.008)).
- See also: T401, T1389, T441

### T1389 ±1 arrays, signed sets and relative difference sets
`find` `prove` · stage: reformulate · signals: group, matrix, sequence
aka: perfect binary arrays, Menon–Hadamard difference sets, regular Hadamard matrices, A = 2D − G, ±1 sequences with constant autocorrelation, splitting relative difference sets, signing a difference set, balanced generalized weighing matrices, lift to C₂ × G
- What: A = 2D − G turns a difference set into a ±1 array with constant off-peak periodic autocorrelation v − 4n and back, so perfect binary arrays are Menon–Hadamard difference sets (v = 4n); a {0, ±1} element of Z[G] is a subset of C₂ × G meeting each fibre once, and signings of a difference set with zero off-peak correlation are splitting relative difference sets.
- Fits when: moving a question about ±1 sequences, arrays or weighing matrices into difference-set language and back; a {0, ±1} solution whose parameters satisfy k(k − 1) = λ(v − 1) is ± an ordinary difference set.
- Lean: the translation is one ring identity, proved once; the translated object checked by `decide +kernel`.
- Example: generalized perfect binary arrays and Menon difference sets ([Jedwab 1992](https://doi.org/10.1007/BF00124209)).
- See also: T437, T441, T39, T1390

### T1390 Cocyclic development
`find` `prove` · stage: reformulate · signals: group, matrix, construction
aka: cocyclic Hadamard matrices, twisted group development, 2-cocycles, orthogonal cocycles, central extensions, central relative difference sets, negacyclic and ω-cyclic matrices, generalized Hadamard matrices, Ito Hadamard matrices
- What: replace the group-developed matrix [φ(gh)] by [ψ(g, h)φ(gh)] with a 2-cocycle ψ; coboundaries give back group development, so the genuine twists are classified by H²(G, N), and a cocyclic generalized Hadamard matrix over a central N is the same as an orthogonal cocycle and as a central relative difference set in the extension group.
- Fits when: Hadamard, generalized Hadamard and weighing matrices that are not group-developed but have a large regular symmetry; for {0, ±1} matrices with Gram matrix nI + λJ, λ ≠ 0 and nonzero row sum, every automorphism is a permutation pair up to one sign, so cocycles give nothing beyond group development.
- Lean: Mathlib: `groupCohomology.H2`; a given cocyclic matrix by `decide +kernel` on its Gram matrix.
- Example: Sylvester's Hadamard matrices are cocyclic over Z₂ⁿ with cocycle (−1)^⟨u, v⟩ (Horadam 2007, Hadamard Matrices and Their Applications).
- See also: T604, T441, T1389, T1394

### T1391 Cyclotomic classes and cyclotomic numbers
`find` · stage: construct · signals: finite-field, group, construction
aka: cyclotomy, cyclotomic classes, cyclotomic numbers, power residues, residue difference sets, Paley difference sets, biquadratic and octic residues, Hall's sextic sets, generalized cyclotomy, Whiteman classes, twin prime powers, Lehmer's criterion
- What: take unions of cosets of a subgroup of F_q^× (or of Whiteman's generalized classes on Z_pq); the difference counts are sums of cyclotomic numbers (i, j)_N, so the union is a difference set exactly when these sums are constant, and Gauss sums give its character values.
- Fits when: difference sets, partial difference sets and sequences on F_q or Z_pq; for signed unions Σ ε_i C_i with ε_i ∈ {0, ±1} the same counts give a quadratic system in ε.
- Lean: the union's difference counts in `ZMod p` by `decide +kernel`.
- Example: Lehmer's analysis of power-residue difference sets ([Lehmer 1953](https://doi.org/10.4153/CJM-1953-047-3)); Whiteman's generalized cyclotomy on Z_pq ([Whiteman 1962](https://doi.org/10.1215/ijm/1255631810)).
- See also: T437, T530, T1383, T1392

### T1392 Building sets and hyperplane unions
`find` · stage: construct · signals: group, finite-field, construction
aka: McFarland difference sets, Spence difference sets, Davis–Jedwab building sets, covering extended building sets, hyperplane unions, Chen's families, Hadamard difference sets, Arasu–Pott lifting, Maiorana–McFarland bent functions
- What: in V = F_qⁿ the hyperplane sums satisfy H_i² = q^(n−1)H_i and H_iH_j = q^(n−2)V (i ≠ j), so one translate of each hyperplane, or of each block of a building set (blocks whose character values have modulus 0 or m), placed in distinct cosets of V gives a difference set whose correlation depends only on the index elements.
- Fits when: difference sets with gcd(v, n) > 1 in groups with a large elementary abelian or small-exponent subgroup: McFarland, Spence, Davis–Jedwab and Chen families, Hadamard difference sets.
- Lean: a found set by `decide +kernel`, packed as bit masks for large v; the family as a group-ring identity by hand.
- Example: McFarland's family ([McFarland 1973](https://doi.org/10.1016/0097-3165(73)90031-9)); building sets unify the McFarland, Spence and Hadamard families ([Davis–Jedwab 1997](https://doi.org/10.1006/jcta.1997.2796)).
- See also: T437, T440, T1391, T1396

### T1393 Group weighing matrices from difference sets and geometry
`find` · stage: construct · signals: group, matrix, construction
aka: circulant weighing matrices, group-developed weighing matrices, W(n, k), B² − G, Wallis–Whiteman, Singer set against a quadric, simplex codes, perfect ternary sequences, W(2s², s²) from Hadamard difference sets, (1 ± u) doubling, extension by zeros, orthogonal pieces on cosets
- What: build {0, ±1} elements with AA⁻¹ = k from classical objects (B² − G for a cyclic planar difference set B, the Singer set against a quadric, simplex codes, ternary trace sequences) and grow them recursively: extension by zeros to a larger group, products, (1 ± u) doubling, orthogonal pieces on the cosets of a subgroup.
- Fits when: circulant and group weighing matrices and perfect ternary sequences; for two difference sets D₁, D₂ in one abelian group, D₁D₂ − cG is a {0, ±1} solution with n = n₁n₂ whenever every coefficient of D₁D₂ lies in {c − 1, c, c + 1}.
- Lean: the element as two bit masks (plus and minus), its autocorrelation by `decide +kernel`.
- Example: Wallis–Whiteman's circulant W(q² + q + 1, q²) from a cyclic projective plane ([Wallis–Whiteman 1975](https://doi.org/10.1017/S0004972700024096)); circulant weighing matrices from relative difference sets with classical parameters ([Leung–Ma–Schmidt 2002](https://doi.org/10.1006/jcta.2002.3262)).
- See also: T441, T440, T1387, T1389

### T1394 Moving a difference set to another group
`find` · stage: construct · signals: group, symmetric, construction
aka: Dillon's dihedral trick, regular subgroups of the automorphism group, G-associates, regular actions, transfer between groups, top-down search, same parameters in another group
- What: compute the automorphism group of a known design or matrix and its regular subgroups; each one makes the object group-developed and gives a set with the same parameters in that group; Dillon's trick turns a set X + gY in a generalized dihedral extension of an abelian H into X + kY in every abelian group containing H with index 2.
- Fits when: a set is known in one group and wanted in another of the same order; for {0, ±1} solutions with λ ≠ 0 and nonzero row sum the automorphisms are permutations up to one sign, so the transfer works the same way.
- Lean: the transported set checked directly by `decide +kernel`; the group computation stays outside Lean.
- Example: the Sylvester SBIBD(16, 6, 2) is developed by every group of order 16 except C₁₆ and D₁₆ (de Launey, Flannery 2011, Algebraic Design Theory); Dillon's dihedral trick ([Dillon 1985](https://doi.org/10.1016/0097-3165(85)90043-3)).
- See also: T29, T27, T437, T1390

### T1395 Switching on a coset of a subgroup
`find` · stage: construct · signals: group, set-family, construction
aka: bent functions, Carlet's flip, modifying a bent function on a flat, affine subspaces, Hadamard difference sets in 2-groups, coset switching, ε-switch
- What: change a known flat object on one coset b + E of a subgroup and keep it flat: for f bent on F₂ⁿ, f + 1_(b+E) is bent iff every derivative D_af with a ∉ E is balanced on b + E, which needs dim E ≥ n/2.
- Fits when: new bent functions, Hadamard difference sets or perfect sequences from known ones by a local change; for {0, ±1} solutions D + ε·bE (with D ∈ {0, −ε} on bE) keeps |χ(D)|² = n iff Re(χ(D)·χ̄(b)) = −ε|E|/2 for every nontrivial χ trivial on E, so |E| ≤ 2√n.
- Lean: the switched object checked directly by `decide +kernel`.
- Example: Carlet's characterization of bent functions that stay bent after a flip on a flat (Carlet 2021, Boolean Functions for Cryptography and Coding Theory).
- See also: T1392, T1393, T437

### T1396 Kronecker products over groups of symmetries
`find` · stage: construct · signals: matrix, group, product-structure, construction
aka: Ionin's method, groups of symmetries, balanced generalized weighing matrices, BGW over a group, decomposable symmetric designs, productive regular Hadamard matrices, generalized Hadamard matrices, infinite families of symmetric designs
- What: a group S of matrices that preserves products and sums to a multiple of J lets each entry s of a balanced generalized weighing matrix over S be replaced by sX; the result is a larger symmetric design or BGW when k²μ = vλl, and the step iterates into infinite families.
- Fits when: symmetric designs with q = k²/(k − λ) a prime power and a cyclic group of symmetries of order dividing q − 1; the {0, ±1} version has the right Gram matrix but is not group-invariant.
- Lean: the product for given small factors as a matrix identity by `decide +kernel`; the construction by hand.
- Example: from a (16, 6, 2) design, symmetric designs (2(9^(t+1) − 1), 6·9^t, 2·9^t) for all t ≥ 1 (Colbourn, Dinitz 2007, Handbook of Combinatorial Designs).
- See also: T440, T1392, T1393
