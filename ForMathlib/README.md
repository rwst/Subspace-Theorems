# ForMathlib: general material Mathlib lacks

A library (`lean_lib ForMathlib`) of definitions and results that are not specific to one paper
or roadmap, and that Mathlib does not have. It is held to the rules of the other libraries (no
`sorry`, no `set_option`, std3 axioms, fine-grained imports, module system, Mathlib root
namespaces). Its files follow Mathlib's directory layout, so each one is a candidate upstream
contribution. It is modelled on `ForMathlib/` of the author's `lean-code` corpus.

| file | content | used by |
| --- | --- | --- |
| `NumberTheory/PisotNumber.lean` | `IsPisot`, `IsSalem`; the golden ratio is Pisot | `CorvajaZannier2004`, `AdamczewskiBugeaud2007` (Theorem 5) |
| `Analysis/Real/BetaExpansion.lean` | Rényi's `β`-transformation and `β`-digits; the expansion converges | `AdamczewskiBugeaud2007` (Theorems 1A–5A) |
| `Data/Nat/Choose/MultinomialSum.lean` | `∑_{|m| = d} 1/C(d; m) ≤ e^{2√n}` over the `m` of degree `d` on `n + 1` variables (Rémond 2001 Lemma 5.2), via Rémond's recurrence for the sums over `m` with fixed support | `QuantitativeSubspace` Q1.3 |
| `LinearAlgebra/SmallCombination.lean` | in characteristic `0`, finitely many vectors not all in any of `T` subspaces have a combination `∑ a_r v_r` with natural coefficients, `∑ a_r ≤ T`, outside all of them (Rémond 2001 Lemma 5.1, by the Combinatorial Nullstellensatz) | `QuantitativeSubspace` Q1.3 |
| `RingTheory/Ideal/LocalLength.lean` | `ℓ(A/I) = ℓ(A/(I : f)) + ℓ(A/(I + (f)))`; colon ideals commute with localization; the localized length `ℓ(A_𝔭/I_𝔭)` and its values on `𝔭`, on ideals not in `𝔭`, and on `A` | `QuantitativeSubspace` Q1.1 |
| `RingTheory/Ideal/LengthPow.lean` | `ℓ(A/J^n) ≤ C(n - 1 + d, d) · ℓ(A/J)` for `J = (x_1, …, x_d)` (Samuel multiplicity `≤` length, before the limit); chains with colon ideals in `𝔭` bound `ℓ(A_𝔭/L_𝔭)` from below; `ℓ(A_𝔭/L_𝔭) < ∞` at minimal primes of Noetherian rings | `QuantitativeSubspace` Q1.1 |
| `RingTheory/MvPolynomial/StandardMonomials.lean` | weighted homogeneous ideals; leading monomials for a monomial order; `dim I_d` = number of leading monomials of weight `d` | `QuantitativeSubspace` Q1.1 |
| `RingTheory/MvPolynomial/Multigraded.lean` | the multigrading by blocks of variables (`multiWeight`); monomial count `∏ C(N_i + d_i - 1, d_i)`; the Hilbert function; colon and span of homogeneous ideals; the exact-sequence identity for `J + (g)` | `QuantitativeSubspace` Q1.1 |
| `RingTheory/MvPolynomial/AgreeAbove.lean` | polynomials with the same coefficients in all degrees `≥ n`; products, substitutions `X i ↦ X i + c`, top coefficients of sums with positive top forms | `QuantitativeSubspace` Q1.1 |
| `RingTheory/MvPolynomial/HilbertPolynomial.lean` | the multigraded Hilbert–Samuel theorem (van der Waerden), `hilbertPoly`, its uniqueness, and `H_{J+(g)}(T) = H_J(T) − H_{(J:g)}(T − e)` | `QuantitativeSubspace` Q1.1 |
| `RingTheory/MvPolynomial/MultiprojectiveDegree.lean` | a Stanley decomposition of the standard monomials; the Hilbert polynomial as a sum of cone polynomials; top coefficients `α! · [T^α] H_I` are natural numbers; first-order Taylor formula; the degrees `d_α` and Evertse's Lemma 1(iv) for hypersurface sections | `QuantitativeSubspace` Q1.1 |
| `RingTheory/MvPolynomial/Associativity.lean` | the graded primality criterion; minimal primes of multihomogeneous ideals are multihomogeneous; multihomogeneous prime filtrations; nonnegative top forms do not cancel; dimension is monotone, strictly on primes; the associativity formula `d_α(I) = ∑ ℓ(K[X]_𝔭/I_𝔭) d_α(𝔭)` | `QuantitativeSubspace` Q1.1 |
| `RingTheory/MvPolynomial/Bezout.lean` | sections by regular sequences; the degrees of the whole space; Bézout's theorem with multiplicities for multiprojective complete intersections | `QuantitativeSubspace` Q1.1 |
| `RingTheory/MvPolynomial/ExcessBezout.lean` | the excess Bézout inequality `ℓ(K[X]_𝔭/I_𝔭) · d_β(𝔭) ≤` Bézout number at a component of the expected codimension (Rémond 2001 Prop. 3.2, degree part; Evertse's Lemma 4), assuming unmixedness of `K[X]_𝔭` (`IsUnmixedRing`); associated primes of multigraded quotients are multihomogeneous | `QuantitativeSubspace` Q1.1 |
| `RingTheory/MvPolynomial/Multiplicity.lean` | monomial ideals by degree and weight; the Taylor map at the generic point of a prime; the multiplicity estimate `ε^d ∏ δ_α ≤ ℓ(B_𝔭/(x)B_𝔭)` (Rémond 2001 Prop. 3.1 with Lemma 3.1), given transversal `Q_α`; at most `e` transversal equations when `ℓ(B_𝔭/(x_1, …, x_e)) < ∞` | `QuantitativeSubspace` Q1.1 |
| `RingTheory/MvPolynomial/MultiplicityBezout.lean` | `ε^t (∏ δ_α) d_β(𝔭) ≤` Bézout number: the degree inequality of the product theorem (Rémond 2001, proof of Prop. 2.1), from the two previous files | `QuantitativeSubspace` Q1.1 |
| `RingTheory/MvPolynomial/Transversal.lean` | the Jacobian criterion at the generic point in characteristic `0`, without Kähler differentials: a transcendence basis `T` of `K[X]/𝔭` adapted to ordered factors, and equations `Q_s ∈ 𝔭`, `s ∉ T`, with diagonal Jacobian invertible modulo `𝔭`; `𝔭` is minimal over them | `QuantitativeSubspace` Q1.1 |
| `RingTheory/MvPolynomial/TransversalHeight.lean` | the transversal equations number `ht 𝔭` (Krull's height theorem one way, the length comparison of `Multiplicity.lean` the other); the dimension formula `ht 𝔭 + trdeg_K (K[X]/𝔭) = |σ|` in characteristic `0` | `QuantitativeSubspace` Q1.1 |
| `RingTheory/MvPolynomial/Projection.lean` | the degree of a multihomogeneous prime in the type of a transcendence basis of variables meeting every block is a positive integer, and `deg H_𝔭 = |T| - |ι|` (Rémond LNM 1752 Ch. 5 Thm 2.10(3)); a variable outside `𝔭` is transcendental over the other blocks, so the adapted basis of `TransversalHeight.lean` meets every block; `deg H_𝔭 + ht 𝔭 + |ι| = |σ|`, with a type of degree `deg H_𝔭` where `d_β(𝔭) ≥ 1` (characteristic `0`) | `QuantitativeSubspace` Q1.1, Q1.3 |
| `RingTheory/MvPolynomial/ProductStructure.lean` | the algebraic matroid of the variables of `K[X]/𝔭` (`varMatroid`, the comap of Mathlib's `AlgebraicIndependent.matroid`); if the block ranks sum to at most the total rank, `𝔭` is minimal over its traces on the blocks (characteristic `0`); cut submodularity reduces this to the cuts `{b s < k}` | `QuantitativeSubspace` Q1.2 |
| `RingTheory/MvPolynomial/Product.lean` | products `V(I₁) × V(I₂)`: `h = h₁ h₂`, `H = H₁ H₂`, dimensions add, degrees multiply (Evertse's Lemma 2) | `QuantitativeSubspace` Q1.1 |

`IsPisot` was moved here from `CorvajaZannier2004/PseudoPisot.lean` unchanged, so the flat
Challenge of that paper, which repeats the definition verbatim, still matches.
