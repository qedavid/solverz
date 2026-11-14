# Difference sets and group-ring methods
Character-value and group-ring methods for difference sets, relative and partial difference sets, group weighing matrices and ±1 arrays: cyclotomic integers, self-conjugacy, Ma's lemma, exponent bounds, field descent, Stickelberger, contractions, partial characters, Parseval squeeze, few character values, valuation reduction, rational idempotents, orbit character tables, modular codes; constructions from cyclotomy, Gauss periods and their lifts, building sets, amorphic schemes, cocycles, linking systems, typed perfect arrays, transfers and switching. Multipliers, BRC and the basic constructions are in designs and codes (T437–T446).

### T1378 Modulus equation in cyclotomic integers
`prove` · stage: argue · signals: group, integers, impossibility
aka: character values as cyclotomic integers, XX̄ = n, Kronecker's theorem, roots of unity, prime ideal factorization in Q(ζ_m), ideal-class obstruction, principal ideals, cyclotomic integers of prescribed absolute value, ramified primes, translate normalisation, Turyn's normalisation χψ(D) = ψ(D), Stickelberger relations, Hilbert class polynomial
- What: each character value X of a group-ring solution solves XX̄ = n in Z[ζ_m]; the prime-ideal factorization of n, Kronecker's theorem (an algebraic integer whose conjugates all have modulus 1 is a root of unity) and the class group list the possible X up to roots of unity; for n = p^b with p | m they are elements of a smaller cyclotomic ring or Gauss sums times smaller solutions.
- Fits when: difference sets, relative difference sets, circulant Hadamard and weighing matrices in abelian groups, when the possible character values decide existence; the equation is the same for {0, ±1} solutions.
- Lean: Mathlib: `IsCyclotomicExtension`, `NumberField.classNumber`; a divisibility in Z[ζ_m] as an integer-polynomial identity modulo the cyclotomic polynomial, checked by `decide +kernel`.
- Example: Schmidt's class-group criterion for cyclotomic integers of prescribed absolute value ([Schmidt 1998](https://doi.org/10.1006/jnth.1998.2275)).
- See also: T438, T517, T1379, T1382, T1409, T1413

### T1379 Self-conjugacy and the Mann test
`prove` · stage: argue · signals: group, integers, impossibility, congruence
aka: self-conjugate primes, Turyn's self-conjugacy, p^j ≡ −1 mod exp G, semiprimitive primes, decomposition groups, decomposition fields, Mann test, even p-part of n, coset sums congruent mod p^b, naive character values, non-naive (Gauss-type) values, self-conjugacy as the boundary of naivety
- What: if some power of p is −1 modulo the p-free part of the group exponent, every prime ideal above p is fixed by complex conjugation, so XX̄ ≡ 0 mod p^(2b) forces X ≡ 0 mod p^b; then the exact p-part of n is a square (Mann) and the coset sums on a quotient of order prime to p agree mod p^b.
- Fits when: nonexistence when n has a factor p^(2b) with p self-conjugate modulo the exponent of a quotient; for {0, ±1} solutions the coset sums lie in [−c, c], so they all agree once p^b > 2c.
- Lean: elementary in F_p[H]: the Frobenius power y^(p^i) = ȳ and yȳ = 0 give y = 0; prove it once, then check each instance's prime, quotient and exponents by `decide +kernel`.
- Example: Turyn's self-conjugacy theorem ([Turyn 1965](https://doi.org/10.2140/pjm.1965.15.319)); the Mann test ([Mann 1964](https://doi.org/10.1215/ijm/1256059669)).
- See also: T1378, T1380, T1381, T438

### T1380 Ma's lemma and inversion with divisibility
`prove` · stage: argue · signals: group, integers, congruence
aka: Ma's lemma, Ma tower, polynomial addition sets, Yamamoto's congruence criterion, Ma–Pott lemma, Legendre vector, Fourier inversion with divisibility, coset-constant coefficients, divided contraction, cyclic Sylow subgroups, Ikeda's method, element partition across an order-2 character, χ(D) ≡ χψ(D) mod 2
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
aka: Schmidt's field descent, F(m, n), fixing theorem, F-bound, descent to a Gaussian-period subfield, quadratic subfield, Chan's method, Arasu–Pott bound, Yamamoto's test 4n = x² + qy², circulant Hadamard matrices, Barker sequences, skew Hadamard difference sets, decomposition-field descent, Feng's descent, Feng–Liu class-group method, Chowla's theorem, Leung–Schmidt conditions, Wieferich pairs
- What: a solution of XX̄ = n in Z[ζ_m] becomes, after multiplying by a root of unity, an element of the smaller field Q(ζ_F) with F = F(m, n) read off the prime factorizations; coefficients in [0, C] then give n ≤ C²F²/(4φ(F)); where X lies in a Gaussian-period or imaginary quadratic subfield, a norm form must represent n, such as 4n = x² + qy².
- Fits when: n is small against the exponent of a cyclic quotient: circulant Hadamard and weighing matrices, Barker sequences, cyclic difference sets; the descent concerns X alone, so it holds for {0, ±1} solutions with C = 2c on a quotient with fibres of size c.
- Lean: in the unramified case the bound φ(m)n ≤ mFc² follows from multipliers and Parseval on functions G → ℤ; each instance's F checked by `decide +kernel`.
- Example: a circulant Hadamard matrix of order 4 < n ≤ 10¹⁴ needs n = 4u² with u ∈ {11715, 82005, 550605, 3854235, 3877665}; the earlier candidate u = 165 is excluded ([Borwein–Mossinghoff 2014](https://doi.org/10.1112/S1461157013000223)); the general method ([Leung–Schmidt 2005](https://doi.org/10.1007/s10623-004-1703-7)).
- See also: T1378, T1381, T1383, T530, T1413

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
aka: contracted difference sets, homomorphic images, coset sums, intersection numbers, second-moment identity, difference lists, small-exponent quotients, real, Gaussian and Eisenstein characters, two-valued contraction, derived difference sets, Mullin's mod-4 rule, support parity per coset, He–Wu support count, zero-distribution congruence
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
aka: p-rank of a design, codes of difference sets, ideals of F_p[G], self-orthogonal codes, Lander's p-adic codes, Smith normal form symmetry, Frobenius multiplier, halving a cyclic Sylow p-subgroup, Wilbrink's theorem, linear complexity, Hamada's conjecture, design invariants, block-triple counts, signed triple correlations, equivalence tests
- What: reduce the incidence or group matrix mod p: for p ∤ |G| its rank counts the characters with χ(D) ≢ 0 mod p; for p | n the rank is at most (v + 1)/2 and BBᵀ = nI + λJ makes the invariant factors symmetric (Lander's chain of codes); in F_p[G] the multiplier p and the vanishing of reversible self-orthogonal ideals give identities such as Wilbrink's.
- Fits when: p divides n and the group order, or p is a multiplier; ranks also tell apart designs with equal parameters; for {0, ±1} solutions the code is self-orthogonal exactly when p | n and p | λ.
- Lean: Mathlib: `Submodule.smithNormalForm`; a rank or Smith form of a given matrix as U·A·V = D with unimodular U, V, checked by `decide +kernel`.
- Example: Lander's p-adic codes of symmetric designs (Lander 1983, Symmetric Designs: An Algebraic Approach); p-ranks of cyclic difference sets from Gauss and Jacobi sums ([Evans–Hollmann–Krattenthaler–Xiang 1999](https://doi.org/10.1006/jcta.1998.2950)).
- See also: T410, T444, T445, T1383

### T1387 Structure of group weighing matrices
`prove` · stage: argue · signals: matrix, group, parity, impossibility
aka: circulant weighing matrices, CW(n, k), Eades' parity bound, zero patterns, Arasu–Ma reduction, weight p², support in a proper subgroup, proper circulant weighing matrices, Eades–Hain, CW(n, 4), rectangles and heptagons, even translate intersections, Geramita–Geramita–Wallis bound, de Launey's support-intersection bound
- What: two rows of a weighing matrix W(n, k) of odd order have zero patterns meeting an odd number of times, so (n − k)(n − k − 1) ≥ n − 1, with equality only when the zero pattern is a projective plane; for weight p² on a cyclic group a translate lives on a proper subgroup, which reduces the order.
- Fits when: existence of circulant or group-developed weighing matrices of given order and weight; the parity count uses only the parity of the off-identity correlation and the support size, so it holds for {0, ±1} solutions with v odd and λ even, equality making the zeros a planar difference set.
- Lean: the parity count proved once over `ZMod 2`; reduced instances by `decide +kernel`.
- Example: Arasu–Ma's localization for weight p² rules out CW(55, 25), CW(133, 49) and others ([Arasu–Dillon 1999](https://doi.org/10.1007/978-94-011-4459-9_1)); Eades' bound (Seberry 2017, Orthogonal Designs: Hadamard Matrices, Quadratic Forms and Algebras).
- See also: T1389, T441, T39

### T1388 Paley-type partial difference sets and conference matrices
`prove` `find` · stage: argue · signals: group, graph, impossibility
aka: partial difference sets, PDS, strongly regular Cayley graphs, Paley-type PDS, Paley graphs, conference matrices, conference cores, skew Hadamard matrices, Turyn–Belevitch product, Latin square type PDS, near-Menon sets, Ma's PDS theorems, no PDS with a cyclic Sylow subgroup, Stanton–Sprott product, twin prime powers, generalized skew Hadamard difference sets, Salazar-Lazaro's orbit transform, G-strings
- What: in an abelian group of order p^(2s+1), p ≡ 1 mod 4, a Paley-type partial difference set meets every subgroup H in (|H| − 1)/2 elements; with its multipliers and congruences in Q(√p) this bounds the exponent (groups of order p³ and p⁵ must be elementary abelian); conference cores of equal order multiply to larger ones.
- Fits when: strongly regular Cayley graphs, Paley-type sets and conference matrices with an abelian regular group; through 2D + 1 − G a Paley-type set is the same as a symmetric {0, ±1} solution with parameters (v, v − 1, −1).
- Lean: a given set's PDS property by `decide +kernel` on its difference counts.
- Example: Ma's survey of partial difference sets ([Ma 1994](https://doi.org/10.1007/BF01388454)); Paley-type sets in groups of order n⁴ and 9n⁴ for every odd n > 1 ([Polhill 2010](https://doi.org/10.1016/j.jcta.2010.03.008)); the orders of abelian groups with a Paley-type PDS are exactly the prime powers ≡ 1 mod 4 and n⁴, 9n⁴ for odd n > 1 ([Wang 2020](https://doi.org/10.1002/jcd.21691)).
- See also: T401, T1389, T441, T1403, T1411

### T1389 ±1 arrays, signed sets and relative difference sets
`find` `prove` · stage: reformulate · signals: group, matrix, sequence
aka: perfect binary arrays, Menon–Hadamard difference sets, regular Hadamard matrices, A = 2D − G, ±1 sequences with constant autocorrelation, splitting relative difference sets, signing a difference set, balanced generalized weighing matrices, lift to C₂ × G, difference element (1 − x)D/2, run vector, plateaued functions, Walsh dictionary, balancedly splittable Hadamard matrices
- What: A = 2D − G turns a difference set into a ±1 array with constant off-peak periodic autocorrelation v − 4n and back, so perfect binary arrays are Menon–Hadamard difference sets (v = 4n); a {0, ±1} element of Z[G] is a subset of C₂ × G meeting each fibre once, and signings of a difference set with zero off-peak correlation are splitting relative difference sets.
- Fits when: moving a question about ±1 sequences, arrays or weighing matrices into difference-set language and back; a {0, ±1} solution whose parameters satisfy k(k − 1) = λ(v − 1) is ± an ordinary difference set.
- Lean: the translation is one ring identity, proved once; the translated object checked by `decide +kernel`.
- Example: generalized perfect binary arrays and Menon difference sets ([Jedwab 1992](https://doi.org/10.1007/BF00124209)).
- See also: T437, T441, T39, T1390, T1410

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
aka: cyclotomy, cyclotomic classes, cyclotomic numbers, power residues, residue difference sets, Paley difference sets, biquadratic and octic residues, Hall's sextic sets, generalized cyclotomy, Whiteman classes, twin prime powers, Lehmer's criterion, generalised twin construction, character-diagonal sets, Gauss–Jacobi phase condition, rationality test |X|² ∈ Q, Thas–Zagier
- What: take unions of cosets of a subgroup of F_q^× (or of Whiteman's generalized classes on Z_pq); the difference counts are sums of cyclotomic numbers (i, j)_N, so the union is a difference set exactly when these sums are constant, and Gauss sums give its character values.
- Fits when: difference sets, partial difference sets and sequences on F_q or Z_pq; for signed unions Σ ε_i C_i with ε_i ∈ {0, ±1} the same counts give a quadratic system in ε.
- Lean: the union's difference counts in `ZMod p` by `decide +kernel`.
- Example: Lehmer's analysis of power-residue difference sets ([Lehmer 1953](https://doi.org/10.4153/CJM-1953-047-3)); Whiteman's generalized cyclotomy on Z_pq ([Whiteman 1962](https://doi.org/10.1215/ijm/1255631810)).
- See also: T437, T530, T1383, T1392, T1401, T1412, T1414

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
aka: circulant weighing matrices, group-developed weighing matrices, W(n, k), B² − G, Wallis–Whiteman, Singer set against a quadric, simplex codes, perfect ternary sequences, W(2s², s²) from Hadamard difference sets, (1 ± u) doubling, extension by zeros, orthogonal pieces on cosets, fold by an involution, halving a circulant Hadamard row, antipodal decomposition, negacyclic halves
- What: build {0, ±1} elements with AA⁻¹ = k from classical objects (B² − G for a cyclic planar difference set B, the Singer set against a quadric, simplex codes, ternary trace sequences) and grow them recursively: extension by zeros to a larger group, products, (1 ± u) doubling, orthogonal pieces on the cosets of a subgroup.
- Fits when: circulant and group weighing matrices and perfect ternary sequences; for two difference sets D₁, D₂ in one abelian group, D₁D₂ − cG is a {0, ±1} solution with n = n₁n₂ whenever every coefficient of D₁D₂ lies in {c − 1, c, c + 1}.
- Lean: the element as two bit masks (plus and minus), its autocorrelation by `decide +kernel`.
- Example: Wallis–Whiteman's circulant W(q² + q + 1, q²) from a cyclic projective plane ([Wallis–Whiteman 1975](https://doi.org/10.1017/S0004972700024096)); circulant weighing matrices from relative difference sets with classical parameters ([Leung–Ma–Schmidt 2002](https://doi.org/10.1006/jcta.2002.3262)).
- See also: T441, T440, T1387, T1389

### T1394 Moving a difference set to another group
`find` · stage: construct · signals: group, symmetric, construction
aka: Dillon's dihedral trick, regular subgroups of the automorphism group, G-associates, regular actions, transfer between groups, top-down search, same parameters in another group, holomorph read-off, Mandić–Vučičić, regular subgroups of Hol(H), index-2 transfer, converse Dillon chain
- What: compute the automorphism group of a known design or matrix and its regular subgroups; each one makes the object group-developed and gives a set with the same parameters in that group; Dillon's trick turns a set X + gY in a generalized dihedral extension of an abelian H into X + kY in every abelian group containing H with index 2.
- Fits when: a set is known in one group and wanted in another of the same order; for {0, ±1} solutions with λ ≠ 0 and nonzero row sum the automorphisms are permutations up to one sign, so the transfer works the same way.
- Lean: the transported set checked directly by `decide +kernel`; the group computation stays outside Lean.
- Example: the Sylvester SBIBD(16, 6, 2) is developed by every group of order 16 except C₁₆ and D₁₆ (de Launey, Flannery 2011, Algebraic Design Theory); Dillon's dihedral trick ([Dillon 1985](https://doi.org/10.1016/0097-3165(85)90043-3)).
- See also: T29, T27, T437, T1390, T1405

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

### T1399 Partial characters and subgroup channels
`prove` `find` · stage: reformulate · signals: group, integers, impossibility
aka: partial characters, χ ⊗ id, κ maps, images in Z[ζ_u][V], channel decomposition, fibre channels, exact compression-and-lifting, restriction to a subgroup, folded spectrum, Fourier dual of contraction, coset pieces, Eisenstein channel, tripled contraction
- What: on G = U × V evaluate only the U-part: κ = χ ⊗ id maps Z[G] to Z[ζ_u][V], and for nontrivial χ the λG term dies, so each channel is a weighing equation of weight n over the smaller group; dually, the conditions at all characters restricting to one ρ ∈ K̂ are an autocorrelation condition on one function on G/K, so the contraction plus one channel per conjugate pair ρ is an exact lift criterion; summing character values over a coset of K^⊥ restricts the set to K, and the coset pieces satisfy Σ_i|χ(D_i)|² = n for every nontrivial χ of K.
- Fits when: lifting a classified contraction that fibre sums cannot decide, or running multiplier and descent arguments on a smaller group; no sign is used, so it holds for {0, ±1} solutions, whose nontrivial channels have weight n with no λ term; only arguments through the trivial channel need λ.
- Lean: the channel identity proved once by Fourier inversion on the quotient; per instance the channel autocorrelations as integer-polynomial identities modulo the cyclotomic polynomial by `decide +kernel`.
- Example: Tan's multiplier and self-conjugacy bounds for group-invariant weighing matrices over Z[ζ_u][V] ([Tan 2018](https://doi.org/10.1007/s10623-018-0466-5)); no CW(105, 36): the Eisenstein channel of the tripled contraction, reduced mod (1 − ω), is a word of a ternary cyclic code, and none of its lifts works ([Tan 2026](https://arxiv.org/abs/2608.18468)).
- See also: T1384, T1386, T1397, T1400, T1417

### T1400 Parseval squeeze
`prove` `find` · stage: argue · signals: group, integers, finite-field, construction
aka: Parseval completeness, one-sided spectral test, flatness certificate, Chen–Xiang–Sehgal congruence lemma, CXS lemma, AM–GM over Galois orbits, Galois-orbit counting, character-value counts, Lin's conjecture, decimation-Hadamard transform
- What: support size and coefficient sum fix the mean of |χ(D)|² over the nontrivial characters (Parseval), so a one-sided bound at every character forces equality: all values ≤ n gives flatness, and so does every value nonzero and divisible by an ideal of norm n^(φ(m)/2), since AM–GM over each Galois orbit then gives a mean ≥ n; Parseval also fixes how many characters take each modulus, and that count must be a union of Galois orbits.
- Fits when: proving that a set built from Gauss sums or cyclotomy is a difference set (Stickelberger divisibility plus one nonvanishing digit), making a spectral filter exact, or killing a configuration whose value counts are not sums of orbit sizes; for {0, ±1} elements Σ_(χ≠1)|χ(D)|² = vk − s² = n(v − 1), so the squeeze holds unchanged.
- Lean: Parseval on functions G → ℤ proved once; per instance the divisibility and nonvanishing as cyclotomic-integer identities by `decide +kernel`.
- Example: Lin's conjecture on ternary sequences with two-level autocorrelation, by Stickelberger valuations, a nonvanishing digit and the squeeze ([Hu–Shao–Gong–Helleseth 2014](https://doi.org/10.1109/TIT.2014.2327625)); the Chen–Xiang–Sehgal lemma that proves skew Hadamard difference sets from a congruence ([Ding–Wang–Xiang 2007](https://doi.org/10.1016/j.jcta.2006.09.008)).
- See also: T1383, T1378, T1399, T1417

### T1401 Three-valued Gauss periods
`find` · stage: construct · signals: finite-field, group, construction
aka: Gauss periods, three-valued Gauss periods, Feng–Momihara–Xiang, periods as a function on Z_N, level sets of periods, Singer-subgroup orbits, arcs, circulant weighing matrices, three-class association schemes
- What: the Gauss periods of index N form a function on Z_N whose Fourier transform is the Gauss sums, so any weighting of their level sets I_i obeys (Σα_iI_i)(Σα_iI_i)^(−1) = q − ((q − 1)/N)Z_N; when the periods take three values in arithmetic progression with step t, I₁ − I₃ has constant off-peak autocorrelation with n = q/t², and λ = 0 gives a circulant weighing matrix; t is the exact p-power dividing the Gauss sums, and for cubic extensions the periods count how Singer-subgroup orbits meet a line.
- Fits when: cyclic difference sets, circulant weighing matrices and association schemes whose Gauss periods take few values; the three-valued case is itself a signed construction for any λ.
- Lean: a found set's autocorrelation in `ZMod N` by `decide +kernel`.
- Example: circulant weighing matrices and association schemes from three-valued Gauss periods ([Feng–Momihara–Xiang 2014](https://arxiv.org/abs/1409.8350)).
- See also: T1391, T1383, T530, T1393

### T1402 Lifting cyclotomic seeds
`find` · stage: construct · signals: finite-field, group, construction
aka: Momihara's lifting, relative Gauss sums, rationality of relative Gauss sums, Momihara–Xiang lifting, quadratic-form lift, level sets of a quadratic form, affine polar graphs, Davenport–Hasse lifting, infinite families from a seed, skew Hadamard and Paley-type families
- What: grow one cyclotomic strongly regular or skew set into an infinite family: (a) when the index conditions make the relative Gauss sum G_(f′)(χ′)/(p^((f′−f)/2)G_f(χ)) equal ±1 (Stickelberger plus congruences mod 1 − ζ), a union of classes of the larger field has the seed's character values times ±p^((f′−f)/2); (b) for a nonsingular quadratic form Q on F_q^(2m) the level sets Q⁻¹(C_i) have, off the singular vectors, character values −εq^(m−1) times Gauss periods of F_(q²), so a PDS made of classes of F_(q²) lifts to an (N)LS PDS {x : Q(x) ∈ ∪C_i}.
- Fits when: strongly regular Cayley graphs, skew Hadamard and Paley-type difference sets from a cyclotomic seed; both lifts are linear in the class weights, but a {0, ±1} weighting stays flat only for zero-sum (λ = −1) seeds in (a), and in (b) only if its value also matches at the singular vectors.
- Lean: a lifted set at a given q by `decide +kernel` on its difference counts; the lift itself by hand.
- Example: infinite families of skew Hadamard difference sets and strongly regular graphs from relative Gauss sums ([Momihara 2013](https://doi.org/10.1016/j.ejc.2012.10.006)); lifting constructions of strongly regular Cayley graphs ([Momihara–Xiang 2014](https://arxiv.org/abs/1212.5752)).
- See also: T530, T1383, T1391, T1401, T1403

### T1403 Amorphic schemes and PDS packings
`find` `prove` · stage: construct · signals: group, graph, construction
aka: amorphic association schemes, van Dam's amorphic fusion, Latin square type PDS, negative Latin square type PDS, LP-packings, NLP-packings, Jedwab–Li packings, spreads, unions of classes, one special class per character, three-value lemma, signed unions of a partition
- What: if G − 1 splits into PDS all of Latin square type (or all of negative Latin square type), the Cayley graphs form an amorphic scheme: every union of classes is again a PDS of that type, and each nontrivial character is special on exactly one class (value u − r_i there, −r_j on the others); Jedwab–Li packings relative to a subgroup behave the same way, so the character values of any union of classes are read off at once.
- Fits when: Menon–Hadamard, Paley-type and Latin square type sets as unions of classes, in abelian groups and, since amorphic class sums commute, in nonabelian ones; as a limit: three reals in arithmetic progression never share a modulus, so a {0, ±1} union is flat only with all signs ±1 (n = u², λ ∈ {−1, 0}) or as a 0/1 union of Menon type.
- Lean: a union's PDS property by `decide +kernel` on its difference counts.
- Example: packings of partial difference sets ([Jedwab–Li 2021](https://doi.org/10.5070/c61055384)); nonabelian PDS built from amorphic abelian ones ([Davis–Polhill–Smith–Swartz 2025](https://doi.org/10.5802/alco.416)).
- See also: T1388, T1392, T1402, T1405

### T1404 Orbit character tables
`compute` `find` · stage: symmetry · signals: group, symmetric, classification
aka: orbit character table, Schur ring, S-ring search, multiplier-invariant sets, rational-valued sets, orbit tree, tree characters, tree automorphisms, set-valued Gaussian elimination, 2-adic congruence propagation, one row per character class
- What: for a set constant on the orbits of a group of automorphisms, every character value is an integer combination of the orbit values and depends only on the character's class, so one row per class and one column per orbit test it; for C_(2^n)² under all units the orbits form a rooted tree, and tree automorphisms permute the rows, a far larger equivalence than Aut G; inside the search, linear statements χ(D) ∈ R_χ are pruned by row reduction with sets and by congruences mod 2^j that tie unknowns together.
- Fits when: classifying PDS, difference sets or flat elements invariant under a large multiplier group (a set with all values rational is fixed by every unit); for {0, ±1} weights the table and the tree equivalence work unchanged, the congruences prune less.
- Lean: each candidate by `decide +kernel` on its integer orbit sums; a search over tree classes needs a cover lemma.
- Example: complete enumeration of partial difference sets in C_(2^n) × C_(2^n) for n ≤ 9 ([Malandro–Smith 2018](https://arxiv.org/abs/1811.11223)).
- See also: T27, T438, T1397, T1405

### T1405 Transfer by algebraic isomorphism
`find` · stage: construct · signals: group, finite-field, construction
aka: Schur-ring isomorphism, algebraic isomorphism of Cayley schemes, formal-set transfer, parameter-determined structure constants, Hagita–Schmidt bijection, Teichmüller lift, Galois rings, pseudo-quadratic bent functions, fibre-sum transport, non-elementary abelian groups
- What: move a set to another group of the same order without a group isomorphism: an algebra isomorphism of Schur rings that maps basic sets to basic sets and commutes with inversion preserves every group-ring identity, so a set constant on the basic sets keeps its parameters; non-homomorphic bijections (Teichmüller digits into Galois rings, pseudo-quadratic bent functions) that preserve the relevant character or fibre sums carry quadric PDS out of elementary abelian groups.
- Fits when: a construction from quadratic forms, spreads or amorphic schemes exists in an elementary abelian group and is wanted in a non-elementary abelian or nonabelian group; the Schur-ring form is pure algebra and holds for {0, ±1} weights.
- Lean: the transported set checked directly by `decide +kernel`.
- Example: the first negative Latin square type PDS in non-elementary abelian 2-groups, via Galois rings ([Davis–Xiang 2004](https://arxiv.org/abs/math/0407423)); PDS and amorphic schemes from pseudo-quadratic bent functions ([Chen–Polhill 2012](https://doi.org/10.1007/s10801-012-0356-2)).
- See also: T1394, T1403, T1404, T1392

### T1406 Rational idempotents and gcd classes
`prove` `find` · stage: reformulate · signals: group, integers, impossibility
aka: rational idempotents, Ramanujan sums, gcd classes, integral circulants, rational-valued characters, Möbius bound, McKay–Wang bound, aliases, Webster's tiles, reversible difference sets, DRAD difference sets
- What: Q[G] splits by rational idempotents, one per kernel class of characters (characters with one kernel are Galois conjugate); a rational-valued element of Z[Z_v] is constant on each gcd class, so its faithful value is a Möbius sum over the divisors and |value| ≤ 2^(ω(v)) when coefficients are at most 1; constructively, one integer alias per kernel class with the target value, assembled from tiles with disjoint supports, builds the set.
- Fits when: symmetric or reversible sets (all values rational), rational circulants, constructions of reversible and DRAD Hadamard difference sets; zeros only lower the count, so √n ≤ 2^(ω(v)) holds for rational-valued cyclic {0, ±1} solutions.
- Lean: gcd-class constancy and the Möbius sum of a given element by `decide +kernel`.
- Example: reversible difference sets assembled from rational idempotents ([Webster 2013](https://doi.org/10.1007/s40065-012-0055-9)); a symmetric circulant Hadamard matrix has √n ≤ 2^(ω(n)) ([McKay–Wang 1987](https://doi.org/10.1016/0024-3795(87)90249-7)).
- See also: T1397, T438, T1404, T1407

### T1407 Few character values
`prove` · stage: argue · signals: group, integers, impossibility
aka: three-valued difference sets, few character values, Galois action on value classes, conjugation polynomial, integrality tables, quadratic value field, index-2 multiplier group
- What: complex conjugation and the Galois group permute the classes of characters with equal value; with three nontrivial values {a, ā, c} this forces c = ±√n ∈ Z, an index-2 group of multipliers fixing D (the stabilizer of a) and Q(a) imaginary quadratic of prime-power discriminant; Fourier inversion, with the class sums tabulated by how g meets D and D⁻¹, must give algebraic integers, which yields divisibility conditions and more multipliers.
- Fits when: difference sets, PDS and weighing-type elements whose spectrum takes few values; two values give derived difference sets (T1384); for {0, ±1} elements the Galois part is unchanged, the discriminant step needs s ∉ {√n, √n − v}, and a prime q | n, q ∤ v only gives D^(q) ∈ {D, D⁻¹}.
- Lean: the integrality conditions as integer divisibilities by `decide +kernel`.
- Example: difference sets with few character values ([Feng et al. 2013](https://doi.org/10.1007/s10623-013-9830-7)).
- See also: T1384, T1378, T438, T1400

### T1408 Linking systems of difference sets
`find` `prove` · stage: construct · signals: group, set-family, construction
aka: linked difference sets, linking systems, linked systems of symmetric designs, D_iD_j⁻¹ = (μ − ν)D + νG, Kerdock sets, bent sets, McFarland linking, products of difference sets, Noda's integrality test
- What: a linking system is a family of (v, k, λ) difference sets in one group whose pairwise products D_iD_j⁻¹ are (μ − ν) times a difference set plus νG; applying the (−1)-image gives (μ − ν)² = n and ν = k(k ± √n)/v, so integrality of ν is the first test; bent sets give maximal systems in Z₂^(2d+2), and McFarland sets indexed by a difference matrix give systems in nonelementary groups.
- Fits when: systems of linked symmetric designs, association schemes and codes; for {0, ±1} elements a product X = DE⁻¹ of two solutions in one group has XX⁻¹ = n_Dn_E + cG, so if X = aF + bG with F ∈ {0, ±1}[G], F is a new solution with n = n_Dn_E/a².
- Lean: the product identity of given sets by `decide +kernel`.
- Example: linking systems of difference sets ([Jedwab–Li–Simon 2018](https://doi.org/10.1002/jcd.21636)).
- See also: T440, T1392, T1395

### T1409 Valuation reduction modulo the prime above p
`prove` · stage: argue · signals: integers, finite-field, impossibility
aka: Eliahou–Kervaire–Saffari argument, leading terms, (1 − ζ)-adic valuation, reduction mod (1 − ζ_p), quadratic system over F_p, −1 a nonsquare mod p, p ≡ 3 mod 4
- What: for cyclotomic integers β_j ∈ Z[ζ_p] with Σ_j|β_j|² = N (and bilinear relations among them), divide by the least (1 − ζ)-adic valuation and reduce mod (1 − ζ): conjugation acts trivially on Z[ζ]/(1 − ζ) = F_p, so the leading residues satisfy Σu_j² = 0 and the reduced relations over F_p, which have no nonzero solution in small cases when −1 is a nonsquare mod p.
- Fits when: complementary pairs, and difference sets split into blocks over the cosets of a normal p-subgroup, with an equation Σ_j|χ(D_j)|² = N, p | N, p ≡ 3 mod 4; sign-free, so it holds for {0, ±1} blocks; the case where every β_j is divisible by p needs a separate argument (Ma's lemma).
- Lean: the F_p lemma by `decide`; the valuation bookkeeping by hand.
- Example: the length of a binary Golay pair has no prime factor ≡ 3 mod 4 ([Eliahou–Kervaire–Saffari 1990](https://doi.org/10.1016/0097-3165(90)90046-Y)).
- See also: T1379, T1380, T1378, T1398

### T1410 Perfect arrays by type
`find` · stage: construct · signals: matrix, sequence, group, construction
aka: generalized perfect binary arrays, GPBA, types of arrays, negaperiodic arrays, twisted extension, interleaving, shears, lifts, Blake's tower, Frank array, perfect arrays over roots of unity, Mow's construction, array orthogonality
- What: an array over the K-th roots of unity has type v if it becomes perfect after a fixed twist by roots of unity (K = 2 and type 1: negaperiodic); types obey a calculus: a twisted extension is flat on one coset of KZ² exactly when the type matches, interleaving pieces with disjoint spectral supports gives a perfect array, shears change the type through SL₂(Z_K), and K arrays of suitable types lift to a type-0 array K times larger.
- Fits when: perfect and generalized perfect arrays, Menon difference sets via perfect binary arrays, multidimensional constructions over roots of unity; for {0, ±1} pieces only K = 2 keeps the entries signed, and interleaving keeps flatness only for λ = 0 pieces.
- Lean: a constructed array's periodic autocorrelation by `decide +kernel` at small size.
- Example: generalized perfect binary arrays and Menon difference sets ([Jedwab 1992](https://doi.org/10.1007/BF00124209)); perfect K^n × K^n arrays over K-th roots of unity for all K, n from the Frank array ([Blake 2026](https://arxiv.org/abs/2610.24408)).
- See also: T1389, T1390, T1393
