# Roadmap: Diophantine approximation and the Subspace Theorem

Diophantine approximation asks how well an algebraic number can be approximated by elements of a
number field, and its central theorem — Schmidt's Subspace Theorem, in the `S`-adic form of
Schlickewei and Evertse — says that the good approximations to a system of linear forms lie in
finitely many proper linear subspaces. Mathlib has the two elementary ends of the story over `ℚ`:
Dirichlet's approximation theorem and Legendre's theorem on convergents
(`Mathlib/NumberTheory/DiophantineApproximation/`), and Liouville's theorem with Liouville numbers
(`Mathlib/NumberTheory/Transcendental/Liouville/`). It has the height machinery. It has nothing in
between: no irrationality exponent, no Thue, no Roth, no Ridout, no unit equation, no Subspace
Theorem. This roadmap builds that middle: the **approximation exponents** of a real number; the
**Roth machinery** — index, generalized Wronskians, the auxiliary polynomial, Roth's lemma;
**Roth's theorem** over a number field with a finite set of places; the **geometry of numbers of
parallelepipeds** over a number field; the **Subspace Theorem** in its projective, affine,
general-position, algebraic-coefficient and parametric forms; and what the theorem exists to
prove — the approximation exponents of algebraic numbers, the **`S`-unit equation** in any number
of variables, **Thue–Mahler**, **norm-form** and **decomposable-form equations**, and the
transcendence of numbers whose expansions are too simple.

"Done" means a contributor who needs a finiteness statement in Diophantine approximation or
Diophantine equations finds it here in the form the literature applies it in, over a number field
and with a finite set of places, and finds the tools behind it — the index, Roth's lemma, the
successive minima of a parallelepiped — as developed objects with their own API, so that the next
theorem proved by the same method starts from a library and not from a paper. The Subspace Theorem
is the summit; Roth's theorem is the milestone halfway up that tests every piece of machinery the
summit reuses.

Suggested home: `TauCeti/NumberTheory/DiophantineApproximation/`, mirroring
`Mathlib/NumberTheory/DiophantineApproximation/` (with `…/Exponent.lean`, `…/MahlerKoksma.lean`,
`…/Index.lean`, `…/GeneralizedWronskian.lean`, `…/AuxiliaryPolynomial.lean`, `…/RothLemma.lean`,
`…/Roth.lean`, `…/Parallelepiped.lean`, `…/EvertseLemma.lean`, `…/Subspace.lean`,
`…/UnitEquation.lean`, `…/ThueMahler.lean`, `…/NormForm.lean`, `…/Expansions.lean`), with Layer 0
in `TauCeti/NumberTheory/NumberField/PlacesOver.lean`. ⚠ **0.1 alone wanted four files**, not one:
`…/PlacesOverFinite.lean` and `…/PlacesOverInfinite.lean` have almost nothing in common — one is
Dedekind-domain algebra, the other is normed-field analysis, and their imports are disjoint — and
the absolute-value infrastructure they share (`…/Nonarchimedean.lean`) is not about number fields
at all and belongs beside `Mathlib/Analysis/AbsoluteValue/`. `…/PlacesOver.lean` is then just the
assembly. ⚠ **0.2 wanted two more**, and along the same seam: `…/ConjugatePlaces.lean` is about
absolute values and the Galois group and needs nothing about ramification, while
`…/LocalExtension.lean` is ramification theory and needs nothing about `AbsoluteValue.LiesOver`.
⚠ **0.3 wanted two more, along the same seam**: `…/SIntegerLocalization.lean` is commutative
algebra over `𝓞 K` — the `S`-integers as a localization, and the enlargement of `S` that makes
them principal — with no height in it, while `…/SAdicHeight.lean` is height bookkeeping with no
ideal theory in it. ⚠ **0.4 split the same way and the prediction held**:
`…/FundamentalInequality.lean` is one element of one number field and no extension appears, while
`…/LiouvilleInequality.lean` is two elements and an extension. Layer 0 stands at **ten** files.
⚠ **1.1 split too, and for the first time not along an algebraic seam but along an *import*
one**: `…/IrrationalityExponent.lean` knows about `LiouvilleWith`, `ℝ≥0∞` and nothing else — no
number field, no height, no polynomial — while `…/LiouvilleExponent.lean` is the one statement
of 1.1 that consumes Layer 0.4 and with it the whole of Mathlib's number-field height machinery.
Keeping them apart is what lets a consumer of the exponent avoid that import. ⚠ **1.2 wanted
four, and the seam is again an import one**: `…/PolynomialSupNorm.lean` is the naive height of an
integer polynomial and Northcott's theorem for it, with no exponent in sight;
`…/MahlerExponent.lean` is the two exponents, their degree-one identification with Layer 1.1 and
the Möbius invariance of Mahler's, and needs nothing but `ℤ[X]` and `ℝ`;
`…/IrreducibleExponent.lean` is the first file of Layer 1 to consume `ArithmeticHeights`, for
Gelfond's inequality; and `…/KoksmaMobius.lean` is Koksma's Möbius invariance, which turned out to
need Gelfond too and so cannot sit with Mahler's. ⚠ **1.3 wanted four and took eight**, and the seam is
once more what each file is allowed to import: `…/PolynomialEval.lean` is the archimedean size of
a polynomial and its mean value form, over `ℤ` and `ℝ` alone; `…/KoksmaComparison.lean` is
`w_n^* ≤ w_n`, which needs nothing else; `…/BoxPrinciple.lean` is `n ≤ w_n`, whose only
ingredient is a pigeonhole; `…/AlgebraicExponent.lean` is `w_n ≤ d − 1`, the one file of
Layer 1 that imports a number field; and **Wirsing's third inequality needed four more**, along
the same seam — `…/SimultaneousBox.lean` is a pigeonhole and nothing else,
`…/RootLocation.lean` is the complex-root analysis and the one file of Layer 1 that imports
Mathlib's Mahler measure, `…/WirsingSystem.lean` is the test points and the real root they
produce, and `…/WirsingThird.lean` is the exponent bookkeeping. ⚠ **2.1 wanted one and took
three**, and for once the seam is not an import one but a *method* one: `…/MvHasseDeriv.lean` is
the definition and everything that is a computation with coefficients, `…/MvHasseDerivTaylor.lean`
is the substitution formula and the two rules that fall out of it, and `…/MvHasseDerivHeight.lean`
is the one file of Layer 2.1 that knows what an absolute value is. ⚠ **2.2 is the first
milestone of this roadmap to fit in the one file it asked for**, `…/DisjointVariables.lean`, and
the reason is that its two halves cannot be separated usefully: the coefficient identity is an
identity over a commutative semiring and the height identity is a statement about a number field,
but the second is three lines once the first is proved and there is nothing between them that
either half would rather not import. ⚠ **2.3 took two, and the seam is one the proof found
rather than one the milestone announced**: `…/WeightedOrder.lean` is the weighted order of a
support — no derivative, no point, no absolute value and no number field, a statement that
belongs as much to commutative algebra as to this roadmap — and `…/PolynomialIndex.lean` is the
translation carrying a point to the origin, after which every property the milestone lists is
three lines of rewriting. ⚠ **2.4 took two as well, and this time the second file is the one
Mathlib is missing**: `…/Wronskian.lean` is the Wronskian of `n` polynomials in *one* variable —
Mathlib has only the two-polynomial `Polynomial.wronskian` — and `…/GeneralizedWronskian.lean` is
the Kronecker substitution that reduces several variables to one. The seam is the same one as in
2.3: the first file knows nothing about the roadmap, and the second is the reduction. ⚠ **2.5
asked for one file and got one** — the second milestone of this roadmap to do so, and for the
opposite reason to 2.2's: not that its halves refuse to separate, but that its three estimates
turned out to be *one* estimate. `…/CountingVolume.lean` proves a single Chernoff bound in `m`
coordinates and then applies it twice, at two weights; the seam a second file would have followed
does not exist. ⚠ **2.6 took four, and every seam is one the milestone did not mention**:
`…/BoxMonomial.lean` is the dictionary between coefficient vectors and polynomials of bounded
*partial* degrees — the box, which `ArithmeticHeights`'s `…/MonomialIndex.lean` does not cover
because Siegel's lemma is packaged there on the simplex of bounded total degree;
`…/MonomialHeight.lean` is the height of one condition row, a statement about tuples of powers
with no polynomial in it; `…/IndexConditions.lean` turns the index into a finite linear system
and counts it by 2.5; and `…/AuxiliaryPolynomial.lean` is the index theorem. The first two know
nothing about each other. ⚠ **2.7 took eight, and only one of them is Roth's lemma**:
`…/HeightTransport.lean` is the transport from local factors to heights with a one-sided
nonarchimedean bound, a statement about finitely supported families with no polynomial in it;
`…/IndexRename.lean` is the dictionary for an injective renaming — a Hasse derivative, the index
and a partial degree each commute with one — together with the three shapes of the index a
determinant needs; `…/PolynomialDeterminantHeight.lean` is the local estimate for a sum, a
product and a determinant of polynomials, and the one file that knows both what an absolute
value is and what a determinant is; `…/RothDecomposition.lean` is the tensor decomposition and
the identity that makes the determinant of derivatives a product of two Wronskians, with no
height and no number field anywhere; `…/RothDeterminant.lean` assembles the degree, the height
and the index of that determinant; `…/RothBaseCase.lean` is the one-variable case, the only file
of the milestone that touches Gelfond's inequality; `…/RothEstimates.lean` is three inequalities
between real numbers and imports no algebra at all; and `…/RothLemma.lean` is the induction.
⚠ **3.1 took two, and the seam is the one the milestone's own sentence predicted**:
`…/ApproximationClass.lean` is Mahler's reduction with nothing arithmetic in it — a finite index
type, a family of maps into the unit simplex, a count and a pigeonhole — and
`…/IndependentHeights.lean` is the half that needs Northcott, and so the first file of the roadmap
since Layer 1 whose only import from Mathlib is a height.
⚠ **3.2 took seven, and they are the five steps of the book plus their two tools**:
`…/GlobalBound.lean` is the product formula read against local upper bounds — Step IV, and the
file that decides the constant `2` of the theorem; `…/MvPolynomialEvalBound.lean` bounds the value
of a polynomial at one absolute value, trivially and through a Taylor expansion, and knows nothing
of number fields; `…/RothLocalBound.lean` is the one-step translation of that bound into the base
field along `AbsoluteValue.LiesOver`; `…/RothClass.lean` is Step 0, Layer 3.1 in the form the
proof quotes; `…/RothKeyInequality.lean` is Steps III to V at a fixed multidegree;
`…/RothAuxiliary.lean` is Steps I and II, and the only file of the milestone that opens Layers 2.6
and 2.7; and `…/RothTheorem.lean` is the choice of `ε`, `N`, `m`, `σ`, `L`, `M` and `D`, in the
book's order, and nothing else.
Layers 0, 1.1, 1.2, 1.3, 2.1, 2.2, 2.3, 2.4, 2.5, 2.6, 2.7, 3.1 and 3.2 together
stand at **fifty-four** files, and nothing suggests the pattern stops.

**This roadmap stands on [`ArithmeticHeights`](../ArithmeticHeights/README.md).** That roadmap's
long-horizon section names the Subspace Theorem, Roth's theorem and unit equations as what its
material is for; this is the roadmap it points at. Every height, every Siegel lemma and every
successive minimum used below is consumed from there by milestone number and none is rebuilt. See
*[Consumed](#consumed)*.

## Scope and boundaries

### Owned here

- The **irrationality exponent** of a real number, built on Mathlib's `LiouvilleWith` — landed,
  with its Möbius invariance and Liouville's bound by the degree — and **Mahler's `w_n` and
  Koksma's `w_n^*`** — also landed, with their Möbius invariance and the identification of both
  with the irrationality exponent at degree one — with the inequalities between them: `w_n^* ≤
  w_n`, the box principle `n ≤ w_n`, Liouville's `w_n ≤ d − 1` and **Wirsing's third lower
  bound** `w_n^* ≥ w_n/(w_n − n + 1)` are landed, his **first two are not and are optional**
  (1.4 is their only consumer); and **Mahler's classification** into `A`-, `S`-, `T`- and
  `U`-numbers, **also optional** — no later layer consumes it.
- **Absolute values of a finite extension lying over a place**, in Mathlib's
  `AbsoluteValue.LiesOver` vocabulary: their classification, the Galois action on them, and the
  local extension formula. This is what lets every theorem below take algebraic targets and
  algebraic coefficients without a completion appearing in any statement.
- The **ring of `S`-integers as a ring**: the multiplicative set it localizes `𝓞 K` at, its
  Dedekind property, the enlargement of `S` that makes it principal, and **primitive** points and
  the height identity they satisfy. Mathlib defines `Set.integer` and stops there.
- **Liouville's inequality over a number field**: the fundamental inequality trapping the product
  of the local factors of a nonzero element between its height and the reciprocal of it, the
  exact value of the *truncated* product over all places, and the lower bound on the truncated
  local factors of `β − α` for `α` in an extension `F` and `β` in `K`. Mathlib has Liouville's
  inequality over `ℚ` only, for a real root of an integer polynomial and with no constant named.
- The **Roth machinery**: Hasse derivatives of multivariate polynomials — landed, with the
  substitution formula, the Leibniz rule, the Taylor expansion and the size estimate — the
  exactness of the height of a product in **disjoint sets of variables** — also landed, at every
  place and with the invariance of the height under an injective renaming of the variables — the
  **index** of a polynomial at a point — landed, as a valuation, with the derivative estimate and
  the agreement with `Polynomial.rootMultiplicity` in one variable — the **generalized
  Wronskian** criterion for linear independence — also landed, in any number of variables and
  with the `n`-polynomial Wronskian in one variable under it, which Mathlib has only for `n = 2`
  — the **counting and volume estimates** that say how many linear conditions the auxiliary
  polynomial has to satisfy — also landed, both directions of the lattice-point comparison and
  both exponential tails, with the book's constants — the **auxiliary polynomial** of prescribed
  index — also landed, in the `ε`–`D₀` form every application uses, with Siegel's lemma applied
  on the box of bounded partial degrees rather than on the simplex of bounded total degree — and
  **Roth's lemma** itself, Bombieri–Gubler's Lemma 6.3.7 — also landed, at the book's constants,
  with the induction run on `θ` rather than on `σ` so that no real power occurs inside it. Its
  multihomogeneous generalization, which Layer 5.3 consumes, is not this milestone.
- **Approximation classes** — Mahler's reduction of a Diophantine inequality to solutions that
  behave alike at every place — landed, stated for an arbitrary finite index set and an arbitrary
  family of maps into the unit simplex, with the count of the classes, the two-sided bound the
  class gives on each local factor, and the `(L, M)`-**independent** sequences Northcott's theorem
  produces inside any infinite set. Mathlib has the stars-and-bars count it rests on and nothing
  above it.
- **Roth's theorem** over a number field with a finite set of places (Lang's formulation) —
  **landed**, in the form with targets in a finite extension measured by a chosen absolute value
  over each place, which contains Roth's original theorem, Ridout's and Schmidt's algebraic-
  coefficient shapes at once — with Roth's original theorem, **Ridout's theorem** and the `p`-adic
  case still to be derived as instances; **Mahler's theorem** on the fractional parts of
  `(p/q)^k`; the **strong gap principle** and the resulting **bound on the number of
  approximations**; and Roth's theorem with **moving targets**.
- The **geometry of numbers of a parallelepiped over a number field**: `S`-adic approximation
  domains as a lattice and a convex body, successive minima counted over `K`, the two-sided
  Minkowski theorem for them, **Evertse's lemma**, and the passage to **exterior powers**.
- The **Subspace Theorem** — the summit — for a number field and a finite set of places: the
  **parametric** form, the projective form with coefficients in the field, the form with
  **algebraic coefficients**, the **affine** form for `S`-integral points, and **Vojta's
  general-position** form.
- The **elementary half of the quantitative theory**: systems of inequalities, the **gap
  principle** for subspaces, the count of **small solutions**, and the reduction of a count of
  subspaces to an interval result.
- The applications that are theorems about numbers: the approximation of algebraic numbers by
  algebraic numbers of bounded degree, the values `w_n(α) = w_n^*(α) = min (n, d − 1)`, the
  **combinatorial transcendence criterion** of Adamczewski–Bugeaud–Luca and the **complexity of
  the digits of an algebraic irrational**.
- The applications that are theorems about equations: the **`S`-unit equation** in two and in `n`
  variables, **Thue** and **Thue–Mahler equations**, the **hyperelliptic equation**, **norm-form
  equations**, **triangularly connected decomposable-form equations**, and the **Corvaja–Zannier
  bound** on `gcd (u − 1, v − 1)`.

### Consumed

- **Mathlib.** `Mathlib/NumberTheory/Height/`, `Mathlib/NumberTheory/DiophantineApproximation/`,
  `Mathlib/NumberTheory/Transcendental/Liouville/`, the places of a number field and
  `AbsoluteValue.LiesOver`, `S`-integers and `S`-units, Hasse derivatives and the Wronskian of
  univariate polynomials, exterior powers, and the geometry of numbers; itemised under *[What
  Mathlib already has](#what-mathlib-already-has-consume)*.
- **[`ArithmeticHeights`](../ArithmeticHeights/README.md)**, by milestone:
  - 0.3 and 0.4, extension invariance and the absolute height of a tuple — every reduction below
    that enlarges the field passes through them; ⚠ **Layer 0.4 is the first consumer of 0.3**:
    `NumberField.mulHeight₁_pow_finrank` is what puts the exponent `[F : K]` into Liouville's
    inequality, and without it the statement would have to be written in absolute heights;
  - 0.5, the affine height — Lemma 7.5.4's normalization of a solution is a statement about it;
  - 1.1 and 1.3, Northcott on projective space and with varying degree — every "all but finitely
    many" below is an appeal to one of them; 3.7, Northcott for subspaces — Layer 5.6;
  - 1.2, height and Mahler measure — the base case of Roth's lemma and the comparison
    `H(f_ξ) ≍ H(ξ)^{deg ξ}` of Layer 7.2;
  - 2.1–2.3, heights of polynomials, the multivariate Gauss lemma and the upper half of Gelfond's
    inequality for `MvPolynomial` — the height bookkeeping of Layers 2 and 5; 2.4 and 2.5, heights
    of linear forms and matrices;
  - 3.1–3.5, the Plücker point, the height of a subspace, Cauchy–Binet and duality — `h(V(Q))` in
    Layer 5.4 is a subspace height, and Layer 4.5 works in the exterior power that 3.1 builds;
  - 4.1, 4.2 and 4.4, successive minima, Minkowski's second theorem and the extraction lemma —
    Layer 4.2 is assembled from these three and proves no geometry of numbers of its own; 4.3's
    number-field lattice and its covolume — Layer 4.1;
  - 5.5, 5.6 and 5.7, Siegel's lemma with entry heights, its relative version and the
    auxiliary-polynomial form — the *only* source of auxiliary polynomials in Layers 2.5 and 5.2;
  - 6.4 and 6.5, heights of `S`-units and the `S`-unit theorem with the `S`-logarithmic lattice —
    Layers 5.1 and 8, and **Layer 0.3**, which is where the dependence on `ArithmeticHeights`
    begins: 6.4 *is* 0.3's membership dictionary, 6.5's product formula *is* 0.3's in logarithmic
    form, and 6.5's `NumberField.exists_mem_asIdeal_iff_eq` — a nonzero algebraic integer lying in
    one prime and in no other, the one use either layer makes of the finiteness of the class group
    — supplies the denominators that make `S.integer K` a localization.

### Not owned here

- **Metric Diophantine approximation** — Khinchin, Jarník–Besicovitch, Sprindžuk's theorem that
  almost every real number has `w_n = n`, Hausdorff dimension of sets of exponents. Layer 1
  defines the exponents and proves what holds for *every* number; statements about *almost every*
  number need measure theory this roadmap never touches.
- **Continued fractions** beyond what Mathlib has. Layer 1 consumes Dirichlet's and Legendre's
  theorems from Mathlib and adds no theory of convergents.
- **Effective methods**: Baker's theory of linear forms in logarithms, effective bounds for the
  heights of solutions of unit and Thue equations, the Thue–Siegel hypergeometric method. Every
  finiteness theorem here is ineffective in the height, and no statement below bounds a height.
- **Function fields.** The Subspace Theorem holds over function fields of characteristic zero
  with a different proof and fails in positive characteristic (Bombieri–Gubler 6.2.8). Everything
  from Layer 3 on is a number-field statement.
- **Siegel's theorem on integral points on curves.** The Corvaja–Zannier proof (Bombieri–Gubler
  7.3.9) is an application of Layer 6.4 to a basis of a Riemann–Roch space. The Riemann–Roch
  theory belongs to [`AlgebraicCurves`](../AlgebraicCurves/README.md), and the
  [`EllipticCurves`](../EllipticCurves/README.md) roadmap records Siegel's theorem as out of its
  scope for want of exactly the approximation theorem built here. Layer 6.4 is stated so that
  either can consume it; the curve-side argument is not in this roadmap.
- **Tori and the Mordell–Lang circle**: Laurent's theorem (Bombieri–Gubler 7.4.7), unit equations
  over an arbitrary field of characteristic zero by specialization, linear recurrences and the
  Skolem–Mahler–Lech theorem. Layer 8.2 is stated over a number field, for `S`-units and for
  finitely generated subgroups of `Kˣ`, and stops there.
- **Automatic sequences.** Layer 7.5 proves the transcendence criterion for an arbitrary sequence
  of digits. That the digits of an automatic sequence satisfy its hypothesis needs a theory of
  finite automata and Cobham's theorem, which no roadmap builds.
- **The quantitative Subspace Theorem** at the strength of Evertse–Schlickewei and
  Evertse–Ferretti, the absolute Subspace Theorem, Vojta's exceptional subspace, and the
  Faltings–Wüstholz theorem. See
  *[Long horizon](#long-horizon-a-roadmap-for-a-roadmap-not-work-to-attempt-here)*.

## Standing hypotheses

`K` is a number field of degree `d = [K : ℚ]` from Layer 0 on, except in Layers 1 and 2.1–2.3,
which are about real numbers and about polynomials over an arbitrary field of characteristic zero.
The theorems of Layers 3–9 are false over a general `Height.AdmissibleAbsValues` field — a global
field of positive characteristic has a product formula and Weil heights, and Roth's theorem fails
there already for one place and one target (Bombieri–Gubler 6.2.8, Mahler's example) — so none of
them is stated at that generality and none should be attempted at it.

Points are tuples `x : ι → K` with `[Fintype ι]`, following Mathlib's `Height.mulHeight`, and the
dimension `n + 1` of the literature is `Fintype.card ι`. Every form of the Subspace Theorem
carries `[Nontrivial ι]`, i.e. `n ≥ 1`: for a one-element `ι` the only proper subspace is `0`,
every nonzero `x` has height `1`, and the hypothesis can hold, so the statement is false there and
not merely empty. Subspaces are `Submodule K (ι → K)`, never `Module.Grassmannian` or
`Projectivization.Subspace`, for the reason `ArithmeticHeights` gives: the subspace height this
roadmap consumes is defined on `Submodule`.

## Pinned conventions

Decide these once. Most of them are the difference between a true statement and a false one, and
the rest are the difference between a theorem a consumer can apply and one they must re-derive.

| Question | Convention |
| --- | --- |
| a finite set of places | **Two typed finsets**, `S∞ : Finset (InfinitePlace K)` and `S₀ : Finset (FinitePlace K)`, in exactly the shape of Mathlib's `NumberField.mulHeight_eq`, which is a product over `InfinitePlace K` with exponent `mult` times a product over `FinitePlace K`. (In Lean source the binders are `Sinf` and `Sfin`: `S∞` stops being an identifier once `ENNReal`'s notation `∞` is open.) ⚠ **Never `S : Finset (AbsoluteValue K ℝ)` without a hypothesis that its members are places**: `\|·\|^{1/j}` is an absolute value on `ℚ` for every `j ≥ 1`, and with `S = {\|·\|, \|·\|^{1/2}, \|·\|^{1/3}, \|·\|^{1/4}}`, the coordinate forms and `ε = 1/12`, every `x = (1, q)` satisfies the inequality of the Subspace Theorem with equality, while no finite set of lines contains them all. The untyped statement is not a weaker theorem; it is a false one. |
| `S` for `S`-integers and `S`-units | `S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))`, **finite places only**, the carrier of Mathlib's `S.integer K` and `S.unit K` and the convention `ArithmeticHeights` pins. The affine Subspace Theorem and every equation of Layer 8 use it, with all infinite places implicitly present: there `S∞ = Finset.univ` and `S₀` is the image of `S` under `FinitePlace.mk`. ⚠ Bombieri–Gubler's `S` always **contains** the archimedean places in these statements; translate. |
| normalization | **Mathlib's, which is relative.** The local factor of `y` at `v : InfinitePlace K` is `v y ^ v.mult` and at `v : FinitePlace K` it is `v y`, and the height is `Height.mulHeight`. Bombieri–Gubler's absolute values and heights are **absolute** — each is the `d`-th root of Mathlib's. Every inequality below is homogeneous in that normalization, so it reads the same in both: raise Bombieri–Gubler's `∏ … < H(x)^{−n−1−ε}` to the `d`-th power. ⚠ The exception is any statement that mixes a relative quantity with an explicit constant or with a height over a different field; each such statement below says what it is in. |
| where the points live, where the coefficients live | **Points in `K`, coefficients and targets in a finite extension `F` of `K`**, with `[Algebra K F]`, measured at `v` by an absolute value `w v : AbsoluteValue F ℝ` with `(w v).LiesOver v` — Mathlib's `AbsoluteValue.LiesOver`. This is Bombieri–Gubler's Theorem 6.4.1 ("we extend `\|·\|_v` to an absolute value of `F`") and it is the one formulation that contains both forms in print: `F = K` is the Evertse–Schlickewei number-field form, and `K = ℚ` with `F` generated by the coefficients is Schmidt's form with algebraic coefficients. **Neither of those two specializes to the other**, which is why the general one is pinned. No completion `K_v` appears in any statement of this roadmap: "a `K`-algebraic element of `K_v`" is an element of some `F` together with a `w` over `v`. |
| the central quantity | `NumberField.approxProd S∞ S₀ w L x`, the product over `v ∈ S∞` of `(∏ i, w v (L v i x) / ⨆ j, v (x j)) ^ v.mult` times the product over `v ∈ S₀` of `∏ i, w v (L v i x) / ⨆ j, v (x j)`, where `L v i : Module.Dual F (ι → F)` and `x` is mapped into `F`. It is an object, not an abbreviation: it is invariant under scaling `x` by `Kˣ`, bounded above in terms of the forms alone, raised to `[K' : K]` under extension of `K`, and multiplicative in `S`. The local sup norm `⨆ j, v (x j)` inside it is written out and has no name, as in `ArithmeticHeights`. The forms are indexed by the underlying `AbsoluteValue K ℝ` of a place, `L : AbsoluteValue K ℝ → ι → Module.Dual F (ι → F)`, so that one family serves both finsets; its values off `S∞` and `S₀` are irrelevant. |
| strict or non-strict | **`≤`.** `approxProd … x ≤ mulHeight x ^ (−(card ι) − ε)`. The literature writes `<`; the two theorems are equivalent (pass to `ε/2` and discard the finitely many projective points of height `1`), and `≤` is what a consumer's estimate produces. |
| the conclusion | `∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧ ∀ x ≠ 0, … → ∃ W ∈ T, x ∈ W`. Subspaces of `Kⁿ⁺¹` — of the field of the **points**, not of `F`. Finiteness of a set of solutions is `Set.Finite`. |
| multiplicative or logarithmic | **Both**, multiplicative primary, as in Mathlib and `ArithmeticHeights`. The Roth machinery is additive by nature — the index theorem and Roth's lemma bound `h(P)` — so Layers 2 and 5 are stated in `logHeight`; Layers 3, 6, 7, 8 in `mulHeight`. |
| approximation exponents | **`ℝ≥0∞`-valued**, in the shape of Mathlib's `dimH`: `Real.irrationalityExponent ξ = ⨆ (p : ℝ≥0) (_ : LiouvilleWith p ξ), (p : ℝ≥0∞)`. The value `⊤` is not junk; it is the exponent of a Liouville number (`forall_liouvilleWith_iff`). A real-valued `sInf` of admissible exponents, as in the one Lean development that defines an irrationality measure (`frenzymath/PiIrrationalityMeasure`), gives Liouville numbers the junk value `0`, below every other irrational, and is not adopted. Rationals have exponent `1`, by Mathlib's `liouvilleWith_one` and `LiouvilleWith.irrational`. |
| the height in `w_n` and `w_n^*` | The **naive height** of an integer polynomial, `max_i \|a_i\|` — ⚠ which is Mathlib's `Polynomial.supNorm`, over `ℤ` directly, and *not* a wrapper around `Polynomial.gaussNorm`: Mathlib's own module documentation calls `supNorm` "the *(naive) height*" and declines the name only because `Height` is taken — and, for an algebraic number, the naive height of its primitive integer minimal polynomial in the sense of `ArithmeticHeights` 1.2. This is Mahler's and Koksma's convention and Bugeaud's. `w_n^*` is normalized with the exponent `−w − 1`, so that `w_1 = w_1^* = irrationalityExponent − 1`. |
| derivatives | **Hasse derivatives**, `∂_μ = (1/μ!) ∂^μ`, as `MvPolynomial.hasseDeriv`, extending Mathlib's univariate `Polynomial.hasseDeriv`. The factorial-free normalization is not cosmetic: `∂_μ` maps integer polynomials to integer polynomials and raises the height by at most `2^{deg}`, which is the estimate every height bound in Layers 2 and 5 uses, and `pderiv` iterated does neither. |
| the index | `ℝ≥0∞`-valued, with `index 0 = ⊤`: the index is a valuation (Bombieri–Gubler 6.3.2) and `⊤` is its value at `0`, not a junk value. Weights are `d : σ → ℝ` with `0 < d j`. |
| declaration names | Statement-named, as in Mathlib and `ArithmeticHeights`; Roth, Ridout, Schmidt, Schlickewei, Evertse, Thue, Mahler, Wirsing go in docstrings. `LiouvilleWith` is Mathlib's and stays. |
| effectivity | None. No statement bounds the height of a solution or of a subspace. Statements that bound a **number** — of approximations in Layer 3.7, of subspaces in Layer 9 — are in, and say which solutions they count. |

## What Mathlib already has (consume)

**Reuse these by name; do not rebuild them.**

- **Dirichlet and Legendre.** `Real.exists_int_int_abs_mul_sub_le`,
  `Real.exists_rat_abs_sub_le_and_den_le`,
  `Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational` — an irrational number has
  infinitely many `p/q` with `|ξ − p/q| < 1/q²`, and a rational one finitely many — and
  `Real.exists_rat_eq_convergent`, Legendre's theorem. This is the lower bound `2` for the
  irrationality exponent and the value `1` at rationals, already proved.
- **Liouville.** `Liouville`, `LiouvilleWith p x` ("`x` is approximable to order `p`": there is
  `C` with `|x − m/n| < C / n^p` for infinitely many `n`), its full invariance API under rational
  affine maps (`LiouvilleWith.add_rat`, `mul_rat`, `neg`, …), `liouvilleWith_one`,
  `LiouvilleWith.mono`, `LiouvilleWith.irrational`, `forall_liouvilleWith_iff`;
  `Liouville.exists_pos_real_of_irrational_root`, Liouville's inequality for a root of an integer
  polynomial, and `Liouville.transcendental`; Liouville's constant; and the measure-zero and
  residual statements, which belong to the metric theory this roadmap does not own. ⚠ The
  constant in `exists_pos_real_of_irrational_root` is produced by a compactness argument and is
  never exhibited; Layer 0.4 rederives the statement from the number-field inequality with
  `2 ^ [F : ℚ] * mulHeight₁ ξ * (⌈|ψ ξ|⌉₊ + 1) ^ [F : ℚ]` in its place.
- **Heights.** All of `Mathlib/NumberTheory/Height/`, as inventoried in `ArithmeticHeights`:
  `Height.mulHeight`, `mulHeight₁`, `NumberField.mulHeight_eq`, `totalWeight_eq_finrank`, the
  Northcott instances, `Rat.mulHeight_eq_max_abs_of_gcd_eq_one`, and
  `Height.mulHeight_linearMap_apply_le`. ⚠ `Height.mulHeight₁_sub_le` and `Height.mulHeight₁_inv`
  carry the *whole* arithmetic of Layer 0.4: the first is where the constant `2 ^ [F : ℚ]` comes
  from, and the second is what makes the lower half of the fundamental inequality free.
  `Rat.mulHeight₁_eq_max` is what the acceptance test needs and nothing else in this roadmap
  does.
- **Places.** `NumberField.InfinitePlace` with `mult`, `comap` and `InfinitePlace.LiesOver`;
  `NumberField.FinitePlace` with `FinitePlace.mk`, `maximalIdeal`, `equivHeightOneSpectrum` and
  the `NonarchimedeanHomClass` instance; `IsInfinitePlace`, `IsFinitePlace`; the product formula
  `NumberField.prod_abs_eq_one`; over `ℚ`, `Rat.AbsoluteValue.real`, `Rat.AbsoluteValue.padic`
  and Ostrowski's theorem `Rat.AbsoluteValue.equiv_real_or_padic`.
- **Absolute values above absolute values.** `AbsoluteValue.under`, `AbsoluteValue.LiesOver`
  (`Mathlib/Analysis/Normed/Ring/WithAbs.lean`), with the completion-level algebra structure in
  `Mathlib/Analysis/Normed/Field/WithAbs.lean`; equivalence of absolute values,
  `AbsoluteValue.IsEquiv` with `isEquiv_iff_lt_one_iff`, **`isEquiv_of_lt_one_imp`** and
  **`isEquiv_iff_exists_rpow_eq`** — the two that do the work of Layer 0.1's nonarchimedean half —
  and the independence statement `exists_one_lt_lt_one_pi_of_not_isEquiv`
  (`Mathlib/Analysis/AbsoluteValue/Equivalence.lean`); the Gelfand–Mazur / Ostrowski theorem on
  complete archimedean fields, **`NormedAlgebra.Real.nonempty_algEquiv_or`**
  (`Mathlib/Analysis/Normed/Algebra/GelfandMazur.lean`), which needs neither completeness nor
  finite dimension. Mathlib has Ostrowski's theorem over `ℚ` only; Layer 0.1 proves the fragment
  over a number field that this roadmap needs.
- **Completions at a place, and what they are.**
  `NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal` and `ringEquivComplexOfIsComplex`
  with their isometry statements: the only identification of a completion with `ℝ` or `ℂ` that
  Mathlib has. ⚠ There is **no** identification of `UniformSpace.Completion ℚ` with `ℝ`, which is
  why Layer 0.1's archimedean half goes through `K_v` and not through `ℚ`.
- **The local extension formula at a finite place.**
  `NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap`: `FinitePlace.mk 𝔓`
  restricted to `K` is `(FinitePlace.mk 𝔭) ^ (e f)`. ⚠ This is the finite half of Layer **0.2**,
  already in Mathlib; 0.1 consumes it and 0.2 should not rebuild it.
  `IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer`,
  `Ideal.absNorm_pow_inertiaDeg`, `Ideal.nonempty_primesOver` and
  `Algebra.QuasiFinite.finite_primesOver` are the rest of what Layer 0.1 consumes.
- **Galois action and local degrees.** `NumberField.InfinitePlace.exists_smul_eq_of_comap_eq`
  (the Galois group is transitive on the infinite places above one),
  `NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank` and `mult_mul_finrank`
  (`NumberField/Completion/Ramification.lean`) — ⚠ these two *are* the infinite half of Layer 0.2,
  and `InfinitePlace.inertiaDeg` there is the local degree `[F_w : K_v]`, not a residue degree;
  `Ideal.exists_comap_galRestrict_eq` and `Ideal.sum_ramification_inertia_eq_finrank` are the
  finite-side counterparts, and `IsFractionRing.finrank_eq` turns `[𝓞 F : 𝓞 K]` into `[F : K]`;
  for primes, transitivity in a Galois extension
  and `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`
  (`NumberTheory/RamificationInertia/Galois.lean`), and `Ideal.sum_ramification_inertia`.
- **`S`-integers and `S`-units.** `Set.integer`, `Set.unit`, `Set.unitEquivUnitsInteger`
  (`Mathlib/RingTheory/DedekindDomain/SInteger.lean`); finiteness of the class group, which is
  what makes `𝓞_S` a principal ideal domain after enlarging `S`. ⚠ **Mathlib's `Set.integer` is a
  `Subalgebra` and nothing more**: it is not known there to be a localization, Noetherian, or a
  Dedekind domain, and it has no class group. Layer 0.3 builds the localization
  (`Set.integerSubmonoid`, `NumberField.isLocalization_integer`) before Proposition 5.3.6 can be
  stated, and `IsLocalization.isDedekindDomain`, `IsLocalization.map_under`,
  `ClassGroup.mk0_surjective` and `Ideal.finite_factors` are what it consumes to do so.
- **Polynomials.** `Polynomial.hasseDeriv` with its Leibniz and Taylor API
  (`Mathlib/Algebra/Polynomial/HasseDeriv.lean`, `…/Taylor.lean`); `MvPolynomial.pderiv`;
  `MvPolynomial.IsHomogeneous` and `degreeOf`; `Polynomial.wronskian` for **two** polynomials
  (`Mathlib/RingTheory/Polynomial/Wronskian.lean`, built for Mason–Stothers);
  `Polynomial.rootMultiplicity`; `Polynomial.gaussNorm`.
- **Siegel's lemma over `ℤ`.** `Int.Matrix.exists_ne_zero_int_vec_norm_le`. Layers 2.5 and 5.2 do
  not use it directly; they use the number-field forms `ArithmeticHeights` builds on top of it.
- **Exterior powers and geometry of numbers**, as inventoried in `ArithmeticHeights`:
  `⋀[R]^n M`, `exteriorPower.ιMulti`, `Module.Basis.exteriorPower`, the pairing with the dual;
  `ZLattice`, `ZLattice.covolume`, `NumberField.mixedEmbedding`.

## What is missing (build here)

Nothing above gives: an irrationality exponent as a number, or any exponent of approximation by
algebraic numbers; Liouville's inequality over a number field in the form approximation arguments
use; a description of the absolute values of `F` lying over a place of `K`; an index or a
Wronskian criterion for polynomials in several variables; any auxiliary-polynomial
construction; Roth's lemma; any of the theorems of Thue, Siegel, Roth, Ridout, Mahler, Schmidt or
Schlickewei; successive minima counted over a number field, or any statement about
parallelepipeds; or a single finiteness theorem for a Diophantine equation that is not proved by
descent. `Suggested.lean` pins the signatures most likely to drift, and indexes the ones already
built: every landed milestone appears there in its delivered form, discharged by the declaration
that carries it, so a rename in the library shows up as a broken `lake build Roadmap`. ⚠ **The
description of the absolute values of `F` lying over a place of `K` is no longer missing**: Layers
0.1 and 0.2 are landed, and with them three pieces of general infrastructure Mathlib lacks — the
criterion *bounded on `ℕ` implies nonarchimedean*, the `rpow` of a nonarchimedean absolute value,
and the fact that an absolute value of `ℂ` restricting to `|·|` on `ℝ` is `|·|` — together with
the ramification vocabulary for **finite** places that Mathlib has for infinite ones and not for
finite ones: a `LiesOver`, a local degree, the set of places above a place, and the local
extension formula in product form. ⚠ **Layer 0.3 is landed too**, and with it the ring theory of
the `S`-integers that Mathlib's `Set.integer` stops short of: the multiplicative set they localize
`𝓞 K` at, the localization and Dedekind statements, Bombieri–Gubler's Proposition 5.3.6, and the
notion of an `S`-**primitive** point with the height identity it satisfies. ⚠ **Layer 0.4 is
landed**, and with it the whole of Layer 0: the fundamental inequality, Liouville's inequality
over an extension of number fields, and Liouville's theorem over `ℝ` with the constant named,
from which Mathlib's `Liouville.exists_pos_real_of_irrational_root` is derived. ⚠ **An
irrationality exponent as a number is no longer missing either**: Layer 1.1 is landed, with the
value at a rational, Dirichlet's lower bound, the characterization of `⊤` as Liouville, invariance
under the rational Möbius group — which needed `LiouvilleWith.inv`, a lemma Mathlib does not have
— two characterizations by the quality of approximations, and Liouville's bound by the degree.
⚠ **An exponent of approximation by algebraic numbers is no longer missing either**: Layer 1.2
is landed, with Mahler's `w_n`, Koksma's `w_n^*`, their monotonicity in the degree, the identity
`w_1 = w_1^* = irrationalityExponent − 1`, the invariance of both under the rational Möbius
group, and the two restrictions of `w_n` — to primitive and to **irreducible** polynomials, the
second by Gelfond's inequality. What Mathlib turned out to have is the naive height itself,
`Polynomial.supNorm`; what it does not have is **Northcott's theorem for integer polynomials**,
and that finiteness is what every statement of the layer runs on. ⚠ **The inequalities between
the two exponents are landed except for Wirsing's first two**: `w_n^* ≤ w_n` for every real `ξ`,
the box principle `n ≤ w_n` for `ξ` not algebraic of degree at most `n`, Liouville's
`w_n ≤ d − 1` at an algebraic `ξ` of degree `d` — together with **Liouville's inequality for the
value of an integer polynomial**, `|P ξ| ≥ c H(P)^{−(d−1)}`, which Mathlib does not have in any
form — and **Wirsing's third lower bound**, `w_n ≤ w_n^* (w_n + 1 − n)`, which at `w_n = n` says
`n ≤ w_n^*` and is what Layer 7.3 consumes. **Wirsing's first two lower bounds on `w_n^*`, and
1.4, are untouched — and all three are optional**: 1.4 is the only consumer of the two bounds,
and nothing in Layers 2–9 consumes 1.4. Both bounds need a hypothesis `1 ≤ n` that the roadmap's
prototypes omitted, since at `n = 0` both exponents vanish. ⚠ **Layer 2 is landed in full**: multivariate Hasse derivatives with the substitution formula
behind them, the exactness
of the height of a product in disjoint variables — Bombieri–Gubler's Proposition 1.6.2 — at every
absolute value at once, the index of a polynomial at a point, as a valuation in any
characteristic, the generalized Wronskian criterion for linear independence in characteristic
zero, the counting-and-volume estimates behind the auxiliary polynomial, **the auxiliary
polynomial itself**, Lemma 6.3.4, and **Roth's lemma**, Lemma 6.3.7. Mathlib has none of the
seven. What 2.2 needed from it is one lemma, the Segre
relation `Height.mulHeight_fun_mul_eq`, and the bridge to it is `Finsupp` and not `MvPolynomial`,
because that lemma is stated for tuples over a finite index type while the exponents of a
polynomial are not one. What 2.3 needed is nothing at all: the weighted order of a support is
built here, on Mathlib's weighted homogeneous components. ⚠ **A Wronskian criterion for
polynomials in several variables is no longer missing — and neither is one in a single
variable**, which is the part of 2.4 the milestone did not advertise: `Polynomial.wronskian` is
the two-polynomial determinant, built for Mason–Stothers, and the `n`-polynomial one with its
independence criterion is new here. ⚠ **What 2.5 needed from Mathlib is the decoupling of a
product over coordinates**, `MeasureTheory.integral_fintype_prod_volume_eq_pow`, and Haar
scaling; what it had to add is one inequality about `Real.sinh`, which Mathlib has no
inequalities for at all, and one about `Real.exp` that Mathlib very nearly has.
⚠ **What 2.6 needed from Mathlib is the Segre relation for an arbitrary finite family**,
`Height.mulHeight_fun_prod_eq`, which is what makes the height of a condition row a product of
one-variable heights with no loss; and what it had to add is the **one-input transport** from
local factors to the height that Layer 2.1 recorded as missing —
`Height.mulHeight_le_pow_totalWeight`, three lines, with `finprod_induction` in place of the
finite-support argument one would expect. The height of the tuple of powers
`α ^ k, k ≤ d`, is `H(α) ^ d` **exactly**, and Mathlib does not have that either.
⚠ **What 2.7 needed from Mathlib is `MvPolynomial.finSuccEquiv` and `Nat.factorial_le_pow`**,
and what it had to add is the *other* transport from local factors to heights — one object
against a **power** of another, with a one-sided inequality at the nonarchimedean absolute
values, which is what a Hasse derivative satisfies and a product does not. The obstruction there
was that the finite-support fact for the local factor of a *family* is private in Mathlib;
`AdmissibleAbsValues.hasFiniteMulSupport`, the same fact for a single element, gives it back in
three lines. Mathlib also has no bound on the height of a determinant of *polynomials*, and
there can be none in the projective height of the entries alone — the estimate has to be made
at each absolute value and transported once.
⚠ **Layer 3.1 is landed, and it is the one milestone so far that needed nothing new from
Mathlib.** The count of the approximation classes is stars and bars, which Mathlib has as
`Finset.card_finsuppAntidiag_nat_eq_choose`, and the existence of `(L, M)`-independent sequences
is `NumberField.finite_setOfPred_logHeight₁_le`, Mathlib's Northcott property for a number field.
What is added is the vocabulary — the cell of a point of the unit simplex, the normalized
logarithmic profile of a family of local factors, and the two-sided bound the cell gives on each
of them — none of which Mathlib has any reason to have.

⚠ **Layer 3.2 is landed, and it needed nothing new from Mathlib either — but it needed one thing
this roadmap had put in the wrong place.** Every input was already here: the index theorem, Roth's
lemma, the Hasse–Taylor expansion, the approximation classes, Northcott. What was missing was the
*global* step: this roadmap's route said "bound `Q(β)` below by 0.4", and Layer 0.4's fundamental
inequality is a product over `S`, which is not enough (see 3.2). The product formula over all the
places against local upper bounds — `NumberField.one_le_of_forall_apply_le_sum` — is the one
statement the milestone had to add, and Mathlib's `NumberField.prod_abs_eq_one` is all it stands
on. Beside it, the milestone adds the local bounds on the value of a polynomial at one absolute
value, which Mathlib has only for *homogeneous* polynomials and with a constant depending on the
polynomial rather than on its height (`Height.mulHeight_eval_le`), and that is the wrong shape
here because the polynomial varies with `D`.

## The build, in layers

### Layer 0: places above places and the `S`-adic dictionary

Small, and entirely algebraic number theory. It exists so that no later layer has to mention a
completion.

**0.1 Absolute values above a place** — **landed**, in
`DiophantineApproximation/Nonarchimedean.lean`, `…/PlacesOverFinite.lean`,
`…/PlacesOverInfinite.lean` and `…/PlacesOver.lean`. For a finite extension `F/K` of number fields
and a place `v` of `K`, classify the `w : AbsoluteValue F ℝ` with `w.LiesOver v`. For
`v : InfinitePlace K` they are exactly the underlying absolute values of the `w' : InfinitePlace F`
with
`w'.LiesOver v`. For `v = FinitePlace.mk 𝔭` they are exactly the functions
`y ↦ (FinitePlace.mk 𝔓 y) ^ ((e * f : ℝ)⁻¹)` for the primes `𝔓` of `𝓞 F` over `𝔭`, with `e` and
`f` the ramification index and inertia degree of `𝔓` over `𝔭` — a **root** of Mathlib's
`FinitePlace` of `F`, because `FinitePlace.mk 𝔓` restricted to `K` is `(FinitePlace.mk 𝔭) ^ (e f)`.
Deduce that the set of such `w` is finite and nonempty, that `w` is nonarchimedean exactly when
`v` is finite, and that every `w` over `v` extends to every further finite extension `F'/F`.
Route: a `w` over a finite place is bounded on `ℤ`, hence nonarchimedean and at most `1` on
`𝓞 F`, so `{y ∈ 𝓞 F | w y < 1}` is a prime over `𝔭` and `w` is equivalent to its adic absolute
value, the exponent being fixed by `w.under K = v`; a `w` over an infinite place restricts to the
usual absolute value on `ℚ`, its completion is a complete archimedean field, and Mathlib's
Gelfand–Mazur file makes that `ℝ` or `ℂ`. ⚠ `w` is **not** in general the absolute value of a
`FinitePlace F`, and a statement that asks for one excludes every ramified or non-split prime.
The classification is what is proved; the hypothesis consumers state is `w.LiesOver v`.

⚠ **The three signatures pinned in `Suggested.lean` survived verbatim**, and are kept there as
`example`s discharged by the library. Nothing in the statement of 0.1 had to move.

⚠ **The archimedean half needs no finiteness at all.** `NumberField.isInfinitePlace_of_liesOver`
is proved for an *arbitrary* field extension `F / K`: no `NumberField F`, no
`FiniteDimensional K F`, not even algebraicity. The whole argument happens inside the completion
`F_w`, and Mathlib's Gelfand–Mazur, `NormedAlgebra.Real.nonempty_algEquiv_or`, asks neither for
completeness nor for finite dimension. The finiteness hypothesis is real only in the
nonarchimedean half, whose *statement* mentions `e` and `f`.

⚠ **The route named above for the archimedean half does not work in Mathlib, and the reason is
worth knowing.** "A `w` over an infinite place restricts to the usual absolute value on `ℚ`, its
completion is a complete archimedean field" — true, but Mathlib does not identify
`UniformSpace.Completion ℚ` with `ℝ`, so there is no `NormedAlgebra ℝ F_w` to be had that way.
What Mathlib *does* identify is `K_v`, by
`NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal` and `ringEquivComplexOfIsComplex`.
So the copy of `ℝ` inside `F_w` is imported from `K_v`, not from `ℚ`, and `v` is used for nothing
else. Anyone porting this to a base field without Mathlib's `InfinitePlace.Completion` will have
to prove `Completion ℚ ≃ ℝ` first.

⚠ **Gelfand–Mazur gives an `ℝ`-algebra isomorphism, not an isometry**, and closing that gap needs
a lemma Mathlib lacks: *an absolute value of `ℂ` that restricts to `|·|` on `ℝ` is `|·|`*
(`AbsoluteValue.eq_norm_of_apply_ofReal`). The proof is four lines of `N(z)^n = N(z^n) ≤ 2‖z‖^n`
plus the same for `z⁻¹`, but without it the classification does not follow from Gelfand–Mazur at
all.

⚠ **The nonarchimedean half costs much less than the route suggests.** No discrete valuation ring,
no uniformizer, no unique factorization of ideals and no class group appears. The only inequality
proved by hand is `∀ x : F, 𝔓-adic x < 1 → w x < 1`, and writing `x = n / d` with `d` outside `𝔓`
(`IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer`) turns it into two
membership statements in `𝔓`. Mathlib's `AbsoluteValue.isEquiv_of_lt_one_imp` and
`isEquiv_iff_exists_rpow_eq` do the rest.

⚠ **Layer 0.2's finite half is already in Mathlib and 0.1 consumes it.**
`NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap` says exactly that
`FinitePlace.mk 𝔓` restricted to `K` is `(FinitePlace.mk 𝔭) ^ (e f)`, which is what pins the
exponent — so the sharp form `(e f)⁻¹` is *cheaper* than the bound `t ≤ 1`, not dearer, and
`NumberField.exists_finitePlace_rpow_inv_eq_of_liesOver` is the theorem proved, with `t ≤ 1`
deduced from it. ⚠ Without that formula the bound would still need `absNorm 𝔭 ≤ absNorm 𝔓`, i.e.
`Ideal.absNorm_pow_inertiaDeg`, so it is nowhere near free. **0.2 should be restated to consume
the finite half rather than to build it**; what 0.2 still owes is the infinite half and the Galois
transitivity.

⚠ **Three pieces of general infrastructure were missing from Mathlib** and are built in
`DiophantineApproximation/Nonarchimedean.lean`: *bounded by `1` on `ℕ` implies nonarchimedean*
(Mathlib's `Ostrowski.lean` proves this only inside its `ℚ`-specific development), *a
nonarchimedean absolute value bounded by `1` on `ℤ` is bounded by `1` on the integral elements*,
and **`AbsoluteValue.nonarchRpow`, the `t`-th power of a nonarchimedean absolute value**. The
last is needed for *nonemptiness*, not for the classification, and it has to exist at **every**
positive exponent: the exponent is only known to be `(e f)⁻¹` after the prime has been produced.
For an archimedean absolute value only `t ≤ 1` works, which is `Real.rpow_add_le_add_rpow`; the
rejection test for `t = 2` on `ℚ` is in the file.

⚠ **The fibre over a finite place is exhibited as an image, not quotiented by an injectivity
argument.** Every `w` over `v` is `(FinitePlace.mk 𝔓) ^ (e f)⁻¹` for a prime `𝔓` above `𝔭`, so the
fibre is contained in the image of the finite set of such primes and `Set.Finite.subset` finishes;
no `Set.InjOn` is needed. The finiteness of the set of primes above `𝔭` is
`Algebra.QuasiFinite.finite_primesOver`.

⚠ **The disjunction `IsInfinitePlace v ∨ IsFinitePlace v` is load-bearing for the route but the
conclusion is true without it.** It is what lets the proof case-split. An absolute value of `K`
that is neither — a proper power `v ^ t` of a place, which is again an absolute value when
`0 < t ≤ 1` — also has a finite nonempty fibre, by the same classification applied to `v`; nothing
in the file proves that, and a consumer who needs it will have to say so.

**0.2 Conjugate absolute values and the local extension formula** (Bombieri–Gubler, Corollary
1.3.2 and Corollary 1.3.5) — **landed**, in `DiophantineApproximation/ConjugatePlaces.lean` and
`DiophantineApproximation/LocalExtension.lean`. For `F/K` Galois, `Gal(F/K)` acts on the absolute
values of `F` over `v` by `w ↦ w ∘ σ⁻¹`, transitively — the `AbsoluteValue.LiesOver` form of
Mathlib's `InfinitePlace.exists_smul_eq_of_comap_eq` and of its prime-ideal counterpart. The local
extension formula, in Mathlib's normalization and for `y ∈ K`: the product over the infinite
places `w'` of `F` above `v` of `w' y ^ w'.mult` is `(v y ^ v.mult) ^ [F : K]`, and the product
over the finite places of `F` above `v` of their values at `y` is `v y ^ [F : K]`. These are
`sum_inertiaDeg_eq_finrank` and `Ideal.sum_ramification_inertia` read multiplicatively. They are
the **local** statements behind `ArithmeticHeights` 0.3, which proves the global identity
`mulHeight_pow_finrank` by a route that never isolates a place; Layer 6.3 needs the local ones.

⚠ **The per-prime finite formula is already in Mathlib and 0.1 landed on it.**
`NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap` is
`FinitePlace.mk 𝔓 (algebraMap K F y) = (FinitePlace.mk 𝔭 y) ^ (e f)`, restated for `FinitePlace.mk`
as `NumberField.FinitePlace.mk_algebraMap` in `DiophantineApproximation/PlacesOverFinite.lean`
and for finite *places* as `NumberField.FinitePlace.apply_algebraMap` in `LocalExtension.lean` —
the restatement Mathlib's own TODO on that lemma asks for. 0.2 consumes it and does not rebuild
it.

⚠ **Mathlib has ramification theory for infinite places and none for finite ones**, and that,
not the mathematics, is where 0.2's cost sits. `NumberField.InfinitePlace` carries `LiesOver`,
`comap`, `IsUnramified`, `placesOver`, a local degree (`InfinitePlace.inertiaDeg`) and the count
`sum_inertiaDeg_eq_finrank`; `NumberField.FinitePlace` carries none of it. So the infinite half
of the local extension formula is three lines — `mult w = mult v * [F_w : K_v]` is
`InfinitePlace.mult_mul_finrank`, and the sum of the local degrees is Mathlib's — while the
finite half needs the **vocabulary** built first: `FinitePlace.LiesOver`, `localDegree`,
`placesOver`, its finiteness and nonemptiness, and the transfer of Mathlib's sum over
`Ideal.primesOver` to a sum over places.

⚠ **`NumberField.InfinitePlace.inertiaDeg` is the local degree `[F_w : K_v]`, not a residue
degree.** It is `1` or `2`. At a finite place `Ideal.inertiaDeg` is the residue degree `f` alone
and the local degree is `e f`, which `LocalExtension.lean` names
`NumberField.FinitePlace.localDegree`. Once both sides are read as local degrees the two
fundamental identities are one statement: **the local degrees of the places above `v` sum to
`[F : K]`**. Beware the name collision when reading the two files side by side.

⚠ **`NumberField.FinitePlace.LiesOver` is not `AbsoluteValue.LiesOver`.** The first says the
primes lie over each other; the second says `w` restricts to `v` on the nose. They agree exactly
when the local degree is `1` — `FinitePlace.liesOver_val_iff_localDegree_eq_one` — and the gap is
precisely what forces 0.1 to classify the absolute values over `v` as *roots* of finite places.
At the infinite places there is no gap: Mathlib's `InfinitePlace.LiesOver` **is** the restriction
condition, and the local degree lives in `mult`, not in the place. Any statement that quantifies
over "the places of `F` above `v`" has to say which of the two it means.

⚠ **Galois transitivity needs no equivariance statement about finite places**, and Mathlib has
none to offer: neither `Ideal.absNorm (σ 𝔓) = Ideal.absNorm 𝔓` nor invariance of the adic
valuation under an automorphism is in the library. The proof instead classifies `w ∘ σ` on its
own with Layer 0.1 — it is an absolute value over `v` like any other — and uses 0.1's uniqueness
clause to name the prime it produces: `{y ∈ 𝓞 F | w (σ y) < 1}` is the contraction of
`{y | w y < 1}` along `σ`. Mathlib's `Ideal.exists_comap_galRestrict_eq` supplies the `σ`. The
exponents on the two sides are never compared, so the Galois invariance of `e` and `f` is not
needed either.

⚠ **The action is on all of `AbsoluteValue F ℝ`, not only on the places.** `σ • w = w ∘ σ⁻¹` is a
`MulAction (F ≃ₐ[K] F) (AbsoluteValue F ℝ)` for any algebra of semirings, extending Mathlib's
action on `NumberField.InfinitePlace`, and it has to be: the elements of the fibre over a finite
place are *not* finite places, so an action defined only on `FinitePlace F` would not see them.

**0.3 The `S`-adic dictionary** — **landed**, in
`DiophantineApproximation/SIntegerLocalization.lean` and
`DiophantineApproximation/SAdicHeight.lean`. For `S : Finset (HeightOneSpectrum (𝓞 K))`:
membership in `S.integer K` and `S.unit K` through `FinitePlace`
(`x ∈ S.integer K ↔ ∀ v ∉ S, v x ≤ 1`), the `S`-product formula
`(∏ v : InfinitePlace K, v u ^ v.mult) * ∏ v ∈ S, v u = 1` for an `S`-unit `u`, and the two facts
Bombieri–Gubler's Theorem 7.2.6 runs on: for `x` with coordinates in `S.integer K`, `mulHeight x`
is at most the product over the infinite places and `S` of the local sup norms, with equality when
the coordinates generate the unit ideal of `S.integer K` (**primitive** points); and (Proposition
5.3.6) every finite `S` is contained in a finite `S'` with `S'.integer K` a principal ideal
domain, from the finiteness of the class group. Over a principal `S'.integer K` every point of
`Kⁿ⁺¹` has a primitive scalar multiple. ⚠ The height characterization of `S`-units and the
`S`-unit theorem are `ArithmeticHeights` 6.4–6.5 and are not restated.

⚠ **Two of the four clauses were already `ArithmeticHeights`, and the milestone should say so.**
The membership dictionary *is* 6.4's `Set.mem_integer_iff_finitePlace` and
`Set.mem_unit_iff_finitePlace`, proved there from
`NumberField.FinitePlace.mk_apply_le_one_iff`; and the `S`-product formula is 6.5's
`NumberField.SUnit.sum_mult_mul_log_add_sum_log` in logarithmic form. Only the multiplicative
form had to be written, and it is two lines on Mathlib's `NumberField.prod_abs_eq_one` and 6.5's
`NumberField.SUnit.finprod_apply_eq_prod`. What 0.3 actually costs is Proposition 5.3.6 and the
tuple-height statement.

⚠ **Proposition 5.3.6 needs a ring structure on `S.integer K` that Mathlib does not have.**
Mathlib carries `Set.integer` as a `Subalgebra R K` cut out by valuations and proves nothing
about the ring it is: no localization, no Noetherianity, no Dedekind instance, no class group.
So the layer has to build that first. The multiplicative set is `Set.integerSubmonoid`, the
nonzero elements of `𝓞 K` lying in no prime outside `S`;
`NumberField.isLocalization_integer` identifies `S.integer K` with the localization at it, and
`NumberField.isDedekindDomain_integer` follows from Mathlib's
`IsLocalization.isDedekindDomain`. ⚠ **`S` must be finite for this**, because the denominator
produced is a finite product, one factor per place of `S`.

⚠ **The denominators come from `ArithmeticHeights` 6.5, and 0.3 is the first file of this roadmap
to consume `ArithmeticHeights` at all.** The single input is *a nonzero algebraic integer lying in
a given prime and in no other*, which is what the finiteness of the class group buys and what
6.5's rank computation already needed; it was `private` there and is now public as
`NumberField.exists_mem_asIdeal_iff_eq`. Layers 0.1 and 0.2 stood on Mathlib alone.

⚠ **The principal-ideal theorem uses no Dedekind theory of `S'.integer K`, no factorization of
ideals and no class number.** Choose one representative ideal per ideal class of `𝓞 K`
(`ClassGroup.mk0_surjective`), one nonzero element of each, and adjoin to `S` the finitely many
primes containing those elements (`Ideal.finite_factors`). Each representative then contains an
element of the multiplicative set, so its extension is the unit ideal; an arbitrary ideal of
`S'.integer K` is the extension of its contraction (`IsLocalization.map_under`), and multiplying
that contraction by the representative of the inverse class makes it principal. The usual proof
adjoins the *prime factors* of a representative; adjoining the primes containing one element of it
is enough and is cheaper.

⚠ **The exponent bookkeeping is done in `ℤ`, not in `ℤᵐ⁰`.** Comparing the pole of `z` at `v`
with the order of the denominator is an inequality between values of `HeightOneSpectrum.valuation`,
which live in `ℤᵐ⁰` and are painful. Moving to `Kˣ` and
`IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero`, whose values lie in `Multiplicative ℤ`,
turns every comparison into linear arithmetic that `omega` closes. ⚠ That normalisation is
Mathlib's and is the *negative* of the usual order: an algebraic integer has non-positive value
and a uniformizer has value `-1`.

⚠ **Only "primitive ⇒ no local factor is lost" is proved; the converse is open.** The proved
direction is the ultrametric inequality applied to `1 = ∑ cᵢ xᵢ` and is three lines. The converse
— all local sup norms equal to `1` away from `S` implies that the coordinates generate the unit
ideal — is a statement about the maximal ideals of `S.integer K`, and needs the prime
correspondence of the localization (`IsLocalization.orderIsoOfPrime`) on top of what is built
here. Nothing in this roadmap consumes it.

⚠ **`Fintype` must not occur in a statement that does not sum over `ι`.** Mathlib's
`unusedFintypeInType` linter rejects it, so `Set.IsPrimitive` and every height statement of 0.3
carry `[Finite ι]` and their proofs take a `Fintype` from `Fintype.ofFinite`.
`Set.isPrimitive_iff`, whose statement *is* a sum, is the single exception. The same rule bit
`ArithmeticHeights` 5.4.

⚠ **The finite mulSupport of `v ↦ ⨆ᵢ |xᵢ|_v` had to be reproved.** Mathlib proves exactly this
for a field with `AdmissibleAbsValues`, as `hasFiniteMulSupport_iSup_nonarchAbsVal`, but keeps it
`private`, and the public `HasFiniteMulSupport.iSup` asks for *every* coordinate to be nonzero,
which a tuple has no reason to satisfy. `NumberField.FinitePlace.hasFiniteMulSupport_iSup` bounds
the support by the union over the nonzero coordinates instead.

⚠ **The layer delivers one statement the milestone does not ask for, and it is the one Theorem
7.2.6 opens with**: `NumberField.exists_finset_superset_forall_exists_mulHeight_eq`, that every
finite `S` is contained in a finite `S'` such that the height of *every* nonzero point of `Kⁿ⁺¹`
is, after a single scaling, the product of the local sup norms over the infinite places and `S'`.
Separating 5.3.6 from the primitive multiple from the height identity, as the milestone does,
leaves the consumer to assemble them; this is the assembly.

⚠ **0.3 split along the same seam as 0.1 and 0.2, and the prediction above held.**
`…/SIntegerLocalization.lean` is commutative algebra over `𝓞 K` with no height in it;
`…/SAdicHeight.lean` is height bookkeeping with no ideal theory in it. ⚠ 0.4 did the same, along
the seam *one field* / *an extension*.

**0.4 Liouville's inequality over a number field** (Bombieri–Gubler (1.8) and Theorem 1.5.21; the
projective form is Theorem 2.8.21) — **landed**, in
`DiophantineApproximation/FundamentalInequality.lean` and
`DiophantineApproximation/LiouvilleInequality.lean`. The fundamental inequality: for `α ≠ 0` in
`K` and any `S∞`, `S₀`, the product of the local factors of `α` over those places is at least
`(mulHeight₁ α)⁻¹` and at most `mulHeight₁ α`. Liouville's inequality: for `α ∈ F`, `β ∈ K`,
`α ≠ β`, and `w v` over `v`, the product over `S∞` of `min 1 (w v (β − α)) ^ v.mult` times the
product over `S₀` of `min 1 (w v (β − α))` is at least
`(2 ^ [F : ℚ] * mulHeight₁ α * mulHeight₁ (β : K) ^ [F : K])⁻¹`, the heights being Mathlib's
relative ones of `α` over `F` and of `β` over `K` — Bombieri–Gubler's `(2 H(α) H(β))^{−[F : K]}`
raised to the power `d`, and weaker than theirs at a place where `F_w ≠ K_v`, where they take a
local norm and this statement takes one absolute value. Mathlib's
`Liouville.exists_pos_real_of_irrational_root` is derived from it as the acceptance test, with
the constant made explicit. This is Step IV of every proof in Layers 3 and 5.

⚠ **The two clauses are one statement, and the milestone should say so.** The truncated local
factors `min 1 |α|_v` of a nonzero `α`, taken over *all* the places, multiply to
`(mulHeight₁ α)⁻¹` exactly — that is the product formula read through `min 1 t * max t 1 = t`,
and it is `NumberField.prod_min_one_apply_eq_inv_mulHeight₁`. Cutting the product down to a
finite set of places can only increase it, every factor being at most `1`, and both halves of
the milestone are that one observation. The fundamental inequality is not an input to Liouville's
inequality; they are siblings.

⚠ **The fundamental inequality's lower bound needs no product formula.** The obvious route — the
product over the complementary places is the reciprocal, so the upper bound applies to it — runs
into the complement of a `Finset` of finite places, which is not a `Finset`. Applying the upper
bound to `α⁻¹` instead inverts the product over the *same* two sets, and `Height.mulHeight₁_inv`
says the bound is unchanged. Two lines instead of a `finprod` over a complement.

⚠ **Truncating by `min 1 ·` makes the statement stronger, not weaker.** Since `min 1 t ≤ t`, the
truncated product is at most the untruncated one, so what is proved here implies the same bound
without the truncation. Bombieri–Gubler's `min` is the sharp form, and the untruncated form is
not worth stating.

⚠ **0.4 uses nothing from 0.2.** Neither the local extension formula nor the Galois action on
the places above `v` appears anywhere. The inequality compares *one* chosen absolute value above
each `v` with the full product over `F`; it never counts the places above `v`, never adds their
local degrees and never conjugates one into another. What it consumes is 0.1 — an absolute value
over an infinite place is an infinite place, one over a finite place is a root of a finite place
— and `ArithmeticHeights` 0.3, of which **0.4 is this roadmap's first consumer**:
`NumberField.mulHeight₁_pow_finrank` is what turns `H_F(β)` into `H_K(β) ^ [F : K]`, and it is
the only reason the exponent `[F : K]` appears in the statement at all.

⚠ **Above an infinite place the work is a Mathlib lemma; above a finite place it is an `rpow`.**
An absolute value over an infinite `v` *is* an infinite place `u` of `F`, and the multiplicity
comparison `v.mult ≤ u.mult` is `NumberField.InfinitePlace.mult_comap_le` once
`AbsoluteValue.LiesOver` has been turned into `u.comap (algebraMap K F) = v`. Above a finite `v`
there is no such identification — 0.1 gives only `w = |·|_𝔓 ^ (e f)⁻¹` — and what saves the
comparison is that the exponent is at most `1`, so `min 1 (s ^ t) ≥ min 1 s`. That three-line
real inequality is the entire finite half.

⚠ **The comparison is a subproduct, so the chosen places have to be distinct.** On the infinite
side injectivity is free: `u v` determines `v` as its `comap`. On the finite side it is
`Ideal.LiesOver` followed by `NumberField.FinitePlace.maximalIdeal_inj` — a prime of `𝓞 F` lies
over exactly one prime of `𝓞 K`. Without it `Finset.prod_image` does not apply and the two
products cannot be compared factor by factor.

⚠ **The acceptance test is the case `F = K`, and the natural-looking `K = ℚ` is harder.**
Deriving `Liouville.exists_pos_real_of_irrational_root` looks like a job for the relative
inequality with `K = ℚ` and `F = ℚ⟮α⟯`, but that needs the infinite place of `ℚ` and an absolute
value of `F` lying over it. Reading everything inside `F = ℚ⟮α⟯` instead — one real embedding, no
finite places — needs only `NumberField.mulHeight₁_pow_finrank` to turn `H_F(β)` into
`H_ℚ(β) ^ [F : ℚ]`, and the only further arithmetic is `Rat.mulHeight₁_eq_max` with `q.num ∣ a`
and `q.den ∣ b + 1`. The constant delivered is
`2 ^ [F : ℚ] * mulHeight₁ ξ * (⌈|ψ ξ|⌉₊ + 1) ^ [F : ℚ]`.

⚠ **The multiplicity of the real place never has to be computed.** A real embedding of `F` could
a priori induce a place whose `mult` is `2`, and Mathlib has no direct lemma saying otherwise.
Because `min 1 t ≤ 1`, `(min 1 t) ^ mult ≤ min 1 t` for every `mult ≥ 1`, so the acceptance test
needs only `NumberField.InfinitePlace.mult_ne_zero`.

⚠ **0.4 split along the same seam as 0.1–0.3, and the prediction held.**
`…/FundamentalInequality.lean` is about *one* element of *one* number field and is pure height
bookkeeping; `…/LiouvilleInequality.lean` is about two elements and an extension and is where
0.1's classification is consumed. Layer 0 now stands at **ten** files.

### Layer 1: approximation exponents

Real numbers only. Nothing here uses Layers 2–6; Layer 7 returns to it with the Subspace Theorem
in hand.

**1.1 The irrationality exponent** — **landed**, in
`DiophantineApproximation/IrrationalityExponent.lean` and
`DiophantineApproximation/LiouvilleExponent.lean`. `Real.irrationalityExponent : ℝ → ℝ≥0∞` as
pinned, and the definition survived verbatim. Proved: the value `1` at rationals;
`2 ≤ irrationalityExponent ξ` for `ξ` irrational, from Dirichlet; `= ⊤ ↔ Liouville ξ`; invariance
under `ξ ↦ (a ξ + b)/(c ξ + d)` for a rational matrix of nonzero determinant, from
`LiouvilleWith`'s API for the affine part and one new lemma for `ξ ↦ ξ⁻¹`; the characterization by
`|ξ − p/q| < q^{−μ}` with and without a constant, and with `H(p/q) = max |p| q` in place of `q`;
and `irrationalityExponent ξ ≤ d` for `ξ` real algebraic of degree `d`, which is Liouville's
theorem as a statement about the exponent.

⚠ **Mathlib has Dirichlet's theorem, but not with unbounded denominators, and that — not the
approximation — is the gap.** `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` produces
infinitely many `q` with `|ξ − q| < 1/q.den²`, while `LiouvilleWith` asks for approximations along
`atTop` *in the denominator*; an infinite set of rationals is not visibly a set of unbounded
denominator, and seeing that it is would need the finiteness of the rationals of bounded height in
a bounded interval — a Northcott argument for a statement that should not need one.
`Irrational.liouvilleWith_two` never proves it. The observation that removes the need is that
**`LiouvilleWith` does not ask `m/n` to be in lowest terms**: a Dirichlet approximation of
denominator `d ≤ n` is *inflated* to denominator `d·t ≥ N` by multiplying numerator and
denominator by `t = N/d + 1`, and its quality `1/((n+1)d)` survives the inflation exactly when
`d t² < 4(n+1)`, which `n = N² + 1` guarantees. The constant is `4` and is not sharp.

⚠ **`LiouvilleWith` has no `inv` in Mathlib, and that single missing lemma is the whole Möbius
milestone.** The affine part is ready-made — `LiouvilleWith.add_rat_iff`, `mul_rat_iff` and
`neg_iff` — so the theorem is the partial-fraction identity
`(aξ + b)/(cξ + d) = (ξ + d/c)⁻¹·((bc − ad)/c²) + a/c` read as a composition of four maps, three
of which are free. The cost of the fourth is **not the inequality but the change of index**: the
approximations to `ξ⁻¹` are indexed by the *numerators* of those to `ξ`, so the target's `atTop`
is a different filter, and the numerator is bounded below only past the threshold
`C/n^p ≤ ξ/2`. Reaching that threshold is where the hypothesis `1 < p` is used (through
`n ≤ n^p`); below `p = 1` the statement is free from `liouvilleWith_one`. Reducing to `0 < ξ`
through `neg_iff` removes every sign case: the new denominator is then `m` itself and not `|m|`.

⚠ **Neither `d ≥ 2` nor irrationality is needed in Liouville's bound.** The statement
`irrationalityExponent ξ ≤ deg ξ` holds at a rational too — exponent `1`, degree `1` — so the
landed `Real.irrationalityExponent_le_natDegree` drops the hypothesis the prototype carried and
closes the rational branch with `minpoly.natDegree_pos`. What the *proof* needs irrationality for
is Liouville's comparison of `ξ` with a rational it must know to be different.

⚠ **Both characterizations are cheap, and one of them needs `0 < μ`.** "Without a constant" is
Mathlib's `LiouvilleWith.frequently_lt_rpow_neg` in one direction and, in the other, the density
of ℝ≥0∞ through `le_of_forall_lt_imp_le_of_dense`; "with `H(p/q) = max |p| q`" is two `rpow`
monotonicities, because
`n ≤ max |m| n ≤ (|ξ| + C + 1)·n` for every approximation of quality `C`, so the two conditions
differ by a constant that `LiouvilleWith` absorbs. There is no separate *height exponent* to
define. ⚠ `Real.le_irrationalityExponent_iff` carries `0 < μ`: at `μ = 0` its right-hand side
quantifies over negative `ν`, where `n^{−ν}` grows and the condition is a triviality about *bad*
approximations.

⚠ **Layer 0.4's real-number corollary had to be given a name.** 0.4 delivered it only as the
acceptance-test `example` that derives `Liouville.exists_pos_real_of_irrational_root`; 1.1 needs
the same statement with the *minimal* polynomial's degree, so
`Real.exists_pos_one_le_pow_natDegree_mul_abs_sub_div` was added to
`…/LiouvilleInequality.lean` and 0.4's acceptance test now derives from it. The `ℚ⟮ξ⟯ ⊆ ℝ`
scaffolding is built once, in Layer 0.

⚠ **The `ℝ≥0∞`-valued supremum costs nothing.** Every order statement of 1.1 is `le_iSup₂` or
`iSup₂_le_iff`, and the two `ENNReal` lemmas that carry the arithmetic are
`ENNReal.ofReal_lt_ofReal_iff'` — an `iff` with a conjunction and no nonnegativity hypothesis —
and `ENNReal.eq_top_of_forall_nnreal_le`. No `toReal` and no case split on `⊤` appears outside the
statement `irrationalityExponent ξ = ⊤ ↔ Liouville ξ` itself.

⚠ **The acceptance tests are `irrationalityExponent (√2) = 2` and Mathlib's
`Liouville.transcendental`.** The first is a *value*, not a bound: Dirichlet gives `2 ≤` and
Liouville gives `≤ 2` because the degree is `2`, and pinning the degree of `√2` at `2` is
`minpoly.two_le_natDegree_iff` against `irrational_sqrt_two`. The second falls out of
`irrationalityExponent ξ = ⊤ ↔ Liouville ξ` and the degree bound, with no transcendence argument
of its own. The rejection test is that the bound cannot be `deg ξ − 1`: that is false already at
`deg ξ = 2`. Replacing `deg ξ` by `2` is Roth's theorem (Layer 3.3), a different statement.

**1.2 Mahler's and Koksma's exponents** (Bugeaud, *Approximation by Algebraic Numbers*, Ch. 3) —
**landed**, in `DiophantineApproximation/{PolynomialSupNorm,MahlerExponent,IrreducibleExponent,
KoksmaMobius}.lean`.
`Real.mahlerExponent n ξ : ℝ≥0∞`, the supremum of the `w` for which `0 < |P(ξ)| ≤ H(P)^{−w}` has
infinitely many solutions `P ∈ ℤ[X]` of degree at most `n`; and `Real.koksmaExponent n ξ`, the
supremum of the `w` for which `0 < |ξ − α| ≤ H(α)^{−w−1}` has infinitely many solutions in real
algebraic `α` of degree at most `n`. Prove monotonicity in `n`; `mahlerExponent 1 = koksmaExponent
1 = irrationalityExponent − 1`; that restricting `P` to primitive, or to irreducible, polynomials
does not change `mahlerExponent` — the second is a theorem, from Gelfond's inequality
(`ArithmeticHeights` 2.3) — and that both exponents are invariant under rational Möbius maps.

⚠ **Mathlib has the naive height and says so, so no new object is defined.**
`Polynomial.supNorm` is the Gauss norm of the coefficient norm at `c = 1`, its own module
documentation calls it "the *(naive) height*", and it works over `ℤ` directly — no `map` into `ℝ`
and no wrapper. The `naiveHeight` abbreviation this roadmap had pinned is deleted rather than
landed. What is genuinely missing is the arithmetic of that norm (subadditivity, the behaviour
under a constant factor, and the exact invariance under `Polynomial.reflect`) and **Northcott's
theorem for integer polynomials**: a polynomial of bounded degree and bounded naive height lies in
a finite set. Over `ℚ` that fails — `C (1/n)` has height `1/n` — and the failure is exactly the
integrality that gives `1 ≤ H(P)` for `P ≠ 0`.

⚠ **The engine of the layer is a *height gap*, not a counting argument.** Every milestone here
replaces a solution by another polynomial — its primitive part, an irreducible factor, a Möbius
transform — and each time the question is whether the images are still *infinitely many*.
Counting the fibres of the replacement works for the primitive part and for nothing else. What
works every time is `Polynomial.exists_pos_lt_supNorm_of_abs_aeval_lt`: below a threshold that
depends only on a height bound, a **nonzero** value at `ξ` forces the naive height above that
bound, whatever polynomial produced it. Koksma's side needs the same statement about a *root*,
`Polynomial.exists_pos_lt_supNorm_of_abs_sub_root_lt`, which is Northcott plus the finiteness of
the real roots of finitely many polynomials.

⚠ **The two degree-one identifications are not mirror images.** On Mahler's side the leading
coefficient is the denominator and the height is `max |m| n`, so the height has to be shown
comparable to the denominator before `LiouvilleWith`'s `atTop` quantifier can be fed. On Koksma's
side the fractions must be in **lowest terms** — only then is the linear polynomial they name
primitive, and hence irreducible by Gauss's lemma — and reducing a fraction lowers its height,
which improves the approximation but threatens to bound the heights; ruling that out is the gap
lemma again. 1.1's `liouvilleWith_iff_frequently_max`, not `le_irrationalityExponent_iff`, is what
both directions consume, because only it measures by the height `max |m| n` that 1.2 normalizes
by.

⚠ **The Möbius decomposition of 1.1 transfers verbatim, and the inversion is free.** The group is
generated by the integer affine maps and by `ξ ↦ ξ⁻¹`; on polynomials the first is
`Polynomial.comp` with a linear substitution — or `Polynomial.scaleRoots` followed by one, on
Koksma's side, where the *roots* have to move — and the second is `Polynomial.reflect n`, which
permutes the coefficients and so preserves the naive height **exactly**. That step is the only one
in the layer with no constant, no threshold and no gap lemma.

⚠ **Gelfond's inequality is a prerequisite for Koksma's Möbius invariance, not an optional
extra.** On Mahler's side `ArithmeticHeights` 2.3 buys only the restriction to irreducible
polynomials. On Koksma's side the Möbius transform of a minimal polynomial is neither primitive
nor irreducible, so the minimal polynomial of the transformed approximant has to be *extracted* as
an irreducible factor of the transform — and the height of a factor is controlled by the height of
the product only through Gelfond. This is where Layer 1 first consumes `ArithmeticHeights`, and it
is one milestone earlier than "1.2 is where 2.3 enters" suggested: it enters twice, for two
different reasons.

⚠ **The integer form of Gelfond uses only the archimedean half of 2.3.** Over `ℤ` the naive height
*is* the sup norm of the complex image, so `Polynomial.supNorm_mul_supNorm_le_two_pow` on `ℂ[X]`
transports along `Polynomial.map` and the multivariate Gauss lemma of 2.3 is never consumed. The
factorization argument then runs at the scale `λ = 2^{−n}`, the unique scale with `λ² 2^n ≤ λ`,
which is what makes the loss in Gelfond reproduce itself along a factorization instead of
accumulating; and it needs the polynomial primitive first, because otherwise the prime factors of
the content make the number of irreducible factors unbounded.

⚠ **The acceptance test is `koksmaExponent 1 = mahlerExponent 1 = irrationalityExponent − 1`.**
Two definitions that look nothing alike — one quantifies over polynomials, the other over
algebraic numbers — meet the object of Layer 1.1 at the only degree where all three are defined.
The rejection tests are that `mahlerExponent 1` is *not* the irrationality exponent (the shift by
one is real: at a rational the first is `0` and the second is `1`), that the determinant
hypothesis of both Möbius invariances is load-bearing, that the degree bound in Northcott cannot
be dropped, that integrality is what gives `1 ≤ H(P)`, and that the constant `2^{deg}` in
Gelfond's inequality cannot be dropped — `(2X+1)(X−2)` has height `3` while both factors have
height `2`.

**1.3 The inequalities.** `n ≤ mahlerExponent n ξ` for `ξ` not algebraic of degree at most `n`,
from Minkowski's linear forms theorem or the box principle applied to `1, ξ, …, ξⁿ`;
`koksmaExponent n ξ ≤ mahlerExponent n ξ`; and, for the same `ξ`, **Wirsing's three lower bounds**,
`mahlerExponent n ξ − n + 1 ≤ koksmaExponent n ξ`,
`(mahlerExponent n ξ + 1)/2 ≤ koksmaExponent n ξ`, and
`w/(w − n + 1) ≤ koksmaExponent n ξ` for `w = mahlerExponent n ξ` (Wirsing 1961), stated in
`ℝ≥0∞` with the conventions that make each true at `w = ⊤`. For `ξ` algebraic of degree `d`:
`mahlerExponent n ξ ≤ d − 1`, from 0.4. — **landed except for Wirsing's first two bounds**, in
`DiophantineApproximation/PolynomialEval.lean`, `…/KoksmaComparison.lean`, `…/BoxPrinciple.lean`,
`…/AlgebraicExponent.lean`, `…/SimultaneousBox.lean`, `…/RootLocation.lean`,
`…/WirsingSystem.lean` and `…/WirsingThird.lean`. ⚠ **The first two need the hypothesis
`1 ≤ n`**, which the statement above omits: at `n = 0` both exponents are `0`, so
`w_n − n + 1 ≤ w_n^*` reads `1 ≤ 0`. The third needs no repair — at `n = 0` it reads `0 ≤ 0`.
⚠ **The two missing bounds are optional.** Every later milestone that names 1.3 — 7.3 above all
— is served by what is landed; the one consumer of the first two is 1.4, which is itself
optional. A contributor may treat 1.3 as complete and lose nothing outside this layer.

⚠ **`w_n^* ≤ w_n` holds for every real `ξ`, with no hypothesis — and the reason is a rigidity
statement.** The obvious proof feeds a Koksma solution `P`, the minimal polynomial of an
approximant `α`, to `mahlerSet` after the mean value theorem on `[α, ξ]`; `mahlerSet` demands
`0 < |P ξ|`, and that fails exactly when `ξ` is itself a root of `P`, which happens as soon as
`ξ` is algebraic of degree at most `n` and one of its conjugates is the approximant. It fails for
**one** `P` up to sign, because a primitive irreducible integer polynomial with a given real root
is unique up to sign — Gauss's lemma in both of its Mathlib forms, through `minpoly` over `ℚ` —
so the offenders share a single height and the height gap of 1.2 discards them. The roadmap's
prototype, which carried no hypothesis, is therefore proved as it stands.

⚠ **The box principle is a pigeonhole on `(H+1)^{n+1} − 1` boxes, and the `− 1` is the whole
argument.** With as many boxes as tuples nothing follows; and because the interval `[−T, T]` that
contains all the linear forms is closed, its right endpoint is attained and the box index has to
be clamped, `min ⌊u⌋₊ (N − 1)`. The loss from `(H+1)^{n+1} − 1` to `H^{n+1}` is a factor of two
and nothing more, so the constant is `4 ∑ |ξ|^k`; it is absorbed by
`Real.le_mahlerExponent_of_infinite` and never appears in the conclusion. Infinitude is once
again the height gap, not the pigeonhole: the box principle produces **one** polynomial per `H`,
nothing says two of them are distinct, and what makes the solutions infinite is that `|P ξ|` can
be made smaller than any threshold.

⚠ **`w_n ≤ d − 1` needs the norm, and Layer 0.4 gives only `w_n ≤ d`.** The fundamental
inequality bounds a nonzero `γ ∈ K` below by `(H_K γ)^{−1}` at a single place, and
`H_K(P ξ) ≍ H(P)^d`; the exponent that comes out is `d`, not `d − 1`. The missing factor is the
distinguished place itself: what is at least `1` is `∏_w w(γ)^{mult w} = |N(γ)|` for an algebraic
**integer** `γ`, and then only the *other* `d − 1` places are estimated by `H(P)`. So this file
consumes `NumberField.InfinitePlace.prod_eq_abs_norm` and the integrality of the norm, not
`NumberField.inv_mulHeight₁_le_prod_apply`. Integrality is bought with `Polynomial.scaleRoots`
rather than by replacing `ξ` with an algebraic integer `t ξ`, which would need `ℚ⟮t ξ⟯ = ℚ⟮ξ⟯` to
keep the degree; `t^{deg P} P(ξ)` is `(P.scaleRoots t)(t ξ)`, and the factor `t^{deg P} ≤ t^n` is
absorbed by the constant. That `ξ` is **real** is what makes the distinguished place real, so
`mult = 1` and the other multiplicities sum to `d − 1` rather than `d − 2`.

⚠ **Wirsing's third inequality is the one that escapes the real-root obstruction, and it escapes
by counting.** The other two start from an arbitrary Mahler approximant, whose nearest root need
not be real. The third does not: it *builds* its polynomial, asking it to be at most `H^{−w}` at
`ξ` and at most `H` at `n − 1` further points, `2` apart from `ξ` and `1` apart from each other.
Because `w` exceeds the Mahler exponent, the height of that polynomial is forced **above**
`H^{1+ε}`, so the polynomial is large relative to its own height at every test point, and
therefore has a root within `1/4` of each of the `n` points. With degree at most `n` that is
exactly one root per point, all roots simple; the disc around `ξ` is stable under conjugation, so
the root inside it equals its own conjugate and is **real**. This is the archimedean form of the
Krasner argument that the ultrametric analogues of this layer use, and it needs no discriminant.

⚠ **Pigeonhole replaces Minkowski's linear forms theorem, and only a constant is lost.** The
classical proof asks Minkowski for `n + 1` bounds on `n + 1` coefficients with the product of the
bounds equal to the determinant. `…/SimultaneousBox.lean` controls only the first `n` of those
forms and lets the last Minkowski bound be the *coefficient* box `A` of the pigeonhole itself —
which is what that bound was for. The exponent `w − n + 1` on `H(P)` is unchanged, and the
constant `K` that appears instead is absorbed by `Real.le_koksmaExponent_of_infinite`. Nothing in
this layer needs the geometry of numbers.

⚠ **The limit `w ↓ w_n(ξ)` is taken once, at the very end.** The construction needs a `w`
*strictly above* the Mahler exponent — that is what forces `H(P)` to be large — and the bound it
returns, `w/(w − n + 1)`, is *decreasing* in `w`, so no single `w` proves the theorem. What does
is continuity of `w ↦ w/(w − n + 1)` at `w_n(ξ)`, and that is the only limit in the layer.

⚠ **Wirsing's first two inequalities are not landed, and the obstruction is that `koksmaSet` asks
for a real root.** Both bound `w_n` *above* in terms of `w_n^*` starting from an arbitrary
approximant, so both have to manufacture a **real** algebraic approximant out of a small value
`|P ξ|`. The root of `P` nearest to `ξ` need not be real — `(X − ξ₀)² + ε²` is small near `ξ₀`
and has no real root. Following Bell–Bugeaud, a root that is *strictly* nearest **is** real, since
its conjugate would be a second root at the same distance; and when the minimum is attained `r ≥ 2`
times, `|P ξ| ≤ c H(P) |ξ − α|^r` together with the definition of `w_n` forces the complex-approximant
exponent `w_n^@` below `(w_n − 1)/2`. So the first inequality follows from the nearest-root
estimate `|ξ − α| ≤ c |P ξ| H(P)^{n−2}` exactly when `w_n > 2n − 3`, and the second is what covers
the rest. The nearest-root estimate is itself missing: it is `|P'(α)| ≥ 2^{−(d−1)(d−2)/2} M(P)^{−(d−2)}`,
which is `|disc P| ≥ 1` together with the product formula `disc P = lc(P)^{2d−2} ∏_{i<j}(α_i − α_j)²`.
Mathlib has `Polynomial.discr`, `Polynomial.resultant_deriv` and `Polynomial.resultant_eq_prod_eval`
— enough to write `∏_i P'(α_i) = ± disc P / lc(P)^{d−2}` — but **not** the pairing of the roots that
turns that product into a square, and the routes that avoid the square root lose a factor
`M(P)^{1/2}` and reach only `w_n − n + 1/2`. The second inequality is Wirsing's
generalized-resultant construction — a basis selected from the monomial multiples of a whole family
of polynomials, as in Poëls's and Dixit's treatments — and nothing in Mathlib comes near it. **In
the range `n ≤ w_n ≤ 2n − 3` the first inequality needs the second**, so the two stand or fall
together. **Of the two, only the second has a consumer** — 1.4, and nothing else — so it is
the one to aim for, and the first is a bonus that comes with the discriminant. Since 1.4 is
itself optional, **neither missing bound blocks any milestone of this roadmap**; they are worth
having because they complete a classical theorem, not because anything downstream waits.

⚠ **The acceptance test is that the two comparisons meet at degree one.** `w_1^* ≤ w_1` and
`1 ≤ w_1` for an irrational both specialize statements Layer 1.2 proved by other means, so each
is checked twice; Wirsing's third inequality is checked in the shape Layer 7.3 consumes, `w_n = n
⟹ n ≤ w_n^*`. The rejection tests are that the box principle fails without its hypothesis —
at a rational, `w_1 = 0` — that the factor `max 1 |x|^n` in the archimedean bound cannot be
dropped (`X²` at `x = 10`), that the factor `n + 1` cannot be dropped either (`X + 1` at `x = 1`),
that a Koksma solution need **not** be a Mahler solution (`√2` is a root of `X² − 2`), and that
Wirsing's first two inequalities are **false at `n = 0`**, which is how the missing hypothesis
`1 ≤ n` was found.

**1.4 Mahler's and Koksma's classifications** — **optional**, consumed by no later layer of this
roadmap, and the sole consumer of Wirsing's first two bounds. With
`w(ξ) = limsup_n mahlerExponent n ξ / n`:
`A`-numbers (`w = 0`), `S`-numbers (`0 < w < ⊤`), `T`-numbers (`w = ⊤`, every `w_n` finite) and
`U`-numbers (some `w_n = ⊤`), and Koksma's `A*`, `S*`, `T*`, `U*` from `koksmaExponent`. Prove:
the `A`-numbers are exactly the algebraic numbers; the two classifications coincide class by
class, from 1.3; Liouville numbers are `U`-numbers with `w_1 = ⊤`; and **Mahler's theorem** that
two algebraically dependent transcendental numbers lie in the same class. ⚠ That `T`-numbers
exist (Schmidt) and that almost every number is an `S`-number (Sprindžuk) are not targets: the
first needs Layer 6 and a construction of its own, the second is metric. ⚠ **"From 1.3" means
Wirsing's *second* inequality, and nothing in this roadmap needs his first.** `w_n^* ≤ w_n`
together with `w_n + 1 ≤ 2 w_n^*` gives `w/2 ≤ w^* ≤ w`, which matches the four classes one for
one — including `A = A^*`, because a transcendental number has `w_n ≥ n`, hence
`w_n^* ≥ (n + 1)/2` and `w^* ≥ 1/2 > 0`. The first inequality gives only `w − 1 ≤ w^* ≤ w`,
which settles `S`, `T` and `U` but leaves `A` open, since `w_n^* ≥ w_n − n + 1 ≥ 1` still allows
`w^* = limsup w_n^*/n = 0`; and the third gives nothing here at all, because
`w_n/(w_n − n + 1) ≤ 2` as soon as `w_n ≥ 2n`, so it cannot see a large `w`. 1.4 is the **only**
milestone of this roadmap that consumes either of the two missing bounds; 7.3 consumes the third
alone, and it is landed.

### Layer 2: the Roth machinery

The non-vanishing technology that Layers 3 and 5 share, and that Mordell's conjecture by Vojta's
method would share too. Milestones 2.1–2.4 are algebra over an arbitrary field, with no heights
and no number theory; they are claimable before anything else in this roadmap exists.

**2.1 Hasse derivatives in several variables** (Bombieri–Gubler 6.3.1). For `μ : σ →₀ ℕ`,
`MvPolynomial.hasseDeriv μ : MvPolynomial σ R →ₗ[R] MvPolynomial σ R`, with
`hasseDeriv μ (monomial m a) = monomial (m − μ) ((∏ j, (m j).choose (μ j)) • a)` when `μ ≤ m` and
`0` otherwise — the book's (6.1). Prove the API Mathlib proves for `Polynomial.hasseDeriv`:
commutation, `hasseDeriv μ ∘ hasseDeriv ν = (∏ j, (μ j + ν j).choose (μ j)) • hasseDeriv (μ + ν)`,
the Leibniz rule as a sum over the antidiagonal of `μ`, the Taylor expansion
`P (x + y) = ∑ μ, (hasseDeriv μ P)(x) * y ^ μ`, agreement with `Polynomial.hasseDeriv` along
`MvPolynomial.uniqueAlgEquiv` (the name the roadmap wrote, `pUnitAlgEquiv`, is not Mathlib's),
the relation `k ! • hasseDeriv (single j k) = ` the `k`-th iterate of `pderiv j`, and `degreeOf`
bounds. The height side, over a field with `AdmissibleAbsValues`: a Hasse derivative does not
increase the local factor at a nonarchimedean absolute value, and multiplies it by at most
`2 ^ totalDegree` at any absolute value, because a product of binomial coefficients
`∏ j, (m j).choose (μ j)` is a natural number at most `2 ^ (∑ j, m j)`. — **landed**, in
`DiophantineApproximation/MvHasseDeriv.lean`, `…/MvHasseDerivTaylor.lean` and
`…/MvHasseDerivHeight.lean`.

⚠ **The Leibniz rule cannot be reached by induction on `μ` from the one-variable case, and that
is the whole shape of the milestone.** The composition law reads
`∂_(single j 1) ∘ ∂_ν = (ν j + 1) • ∂_(ν + single j 1)`, so recovering `∂_(ν + single j 1)` from
it means dividing by `ν j + 1` — not invertible in a general commutative semiring, and
characteristic `p` is exactly where the Hasse derivative earns its keep. What works is the
**substitution formula** `coeff μ (P (C X + X)) = ∂_μ P` in `MvPolynomial σ (MvPolynomial σ R)`,
after which Leibniz is `MvPolynomial.coeff_mul` applied to a ring homomorphism, and the Taylor
expansion is one evaluation away. The substitution formula in turn is proved by
`MvPolynomial.induction_on` over `C`, `+` and `· * X j`, so the only differentiation done by hand
is against a single variable — and *that* is Pascal's rule,
`(a + b).choose b = (a − 1 + b).choose b + (a + (b − 1)).choose (b − 1)`. Proving the substitution
formula directly would need the multivariate binomial theorem; proving Leibniz directly would need
a reindexing of a double sum over two antidiagonals. Neither is needed, and neither was done.

⚠ **`R` may be a `CommSemiring`, and two statements will not typecheck in the shape this roadmap
wrote them.** Nothing in 2.1 subtracts. The composition law's scalar is a product of natural
numbers and is best written as an `ℕ`-action, which removes every `Nat.cast` downstream; and it
**cannot** be stated as a `Finsupp.prod` of single-variable operators, because that product would
live in `Module.End R (MvPolynomial σ R)`, a monoid and not a commutative one, where
`Finsupp.prod` does not typecheck. The usable exact form is
`∂_μ ∘ ∂_ν = ∂_(μ + ν)` for `μ` and `ν` with disjoint supports. The Taylor expansion has the same
trouble with its index set: there is no `LocallyFiniteOrderBot (σ →₀ ℕ)` instance, so
`Finset.Iic m` does not exist, and the expansion is stated over any finset containing the orders
at which the derivative survives — which is what every caller can supply.

⚠ **The height side is `2 ^ totalDegree`, and it stops at the local factor.** `∑ j, degreeOf j P`
is undefined when `σ` is infinite, which it is allowed to be; `totalDegree` is both sharper and
always available, because the binomial factor is bounded monomial by monomial. Turning the two
local estimates into a statement about `MvPolynomial.mulHeight` needs a transport lemma with
**one** input and a **one-sided** nonarchimedean hypothesis, and `ArithmeticHeights`'s
`Finsupp.mulHeight_le_of_forall_iSup_le` has two inputs and demands *equality* at the
nonarchimedean places — which Gauss's lemma supplies for a product and a Hasse derivative does
not. That transport belongs in the `ArithmeticHeights` roadmap; ⚠ **2.6 wrote the case it
needed** — `Height.mulHeight_le_pow_totalWeight`, one tuple, a constant at the archimedean
absolute values and `≤ 1` at the others — in `DiophantineApproximation/MonomialHeight.lean`, and
it is three lines. The general two-sided form is still the `ArithmeticHeights` roadmap's, and
5.6 still consumes the local estimates directly.

**2.2 Polynomials in disjoint variables** (Bombieri–Gubler, Proposition 1.6.2) — **landed**.
For `f : MvPolynomial σ K` and `g : MvPolynomial τ K`, the height of
`rename Sum.inl f * rename Sum.inr g` is `mulHeight f * mulHeight g`, exactly and at every place:
the coefficients of the product are the pairwise products of the coefficients, and Mathlib has
the Segre relation for tuples. This is the identity `h(W) = h(U) + h(V)` on which Roth's lemma
turns; Gelfond's inequality would lose a constant there that the induction cannot afford.

⚠ **The local identity needs no hypothesis at all, and the height identity needs two.** At a
single absolute value `⨆ v(coeff (FG)) = (⨆ v(coeff F))(⨆ v(coeff G))` holds for every `f` and
`g`, `f = 0` included, where both sides are `0`; and it holds at the archimedean places exactly
as at the finite ones, with **no** ultrametric hypothesis — Gauss's lemma needs one and is false
without it, but here there is no sum of several terms to apply a triangle inequality to, because
the antidiagonal of an exponent of `σ ⊕ τ` meets the two supports in a single point. The height
identity is the one that needs `f ≠ 0` and `g ≠ 0`, and only because `mulHeight 0 = 1` is a junk
value: at `f = 0` the left side is `1` and the right side is the height of `g`.

⚠ **The milestone is a statement about finitely supported families, and only its first line is
about polynomials.** Mathlib's Segre relation is stated for tuples over a *finite* index type and
the exponents of a polynomial are `σ →₀ ℕ`, which is not one, so the passage goes through
`ArithmeticHeights`'s `Finsupp.mulHeight_eq_mulHeight_comp` on the supports. Written that way the
statement is `Finsupp.mulHeight_eq_mulHeight_mul_mulHeight`: a family that is the multiplication
table of two others along an injection has the product of their heights, and the polynomial half
is the coefficient identity that produces the injection. That lemma and its local companion
belong to the `ArithmeticHeights` roadmap and are written so that they can move there unchanged.

⚠ **Renaming came free, and it is what 2.7 calls.** The statement above uses `Sum.inl` and
`Sum.inr`, but Roth's lemma multiplies two generalized Wronskians that already sit inside one
variable set. The height does not see how the variables are named —
`MvPolynomial.mulHeight_rename_of_injective`, proved from the same reindexing lemma — so the
usable form, with two injections of disjoint range into a common `υ`, follows in two lines, and
that is the form to consume.

**2.3 The index** (Bombieri–Gubler 6.3.2) — **landed**. For weights `d : σ → ℝ` with
`0 < d j`, a point `α : σ → R` and `P : MvPolynomial σ R` over a commutative ring,
`MvPolynomial.index d α P : ℝ≥0∞` is the infimum of `∑ j, μ j / d j` over the `μ` with
`(hasseDeriv μ P)(α) ≠ 0`. It is a valuation on a domain:
`index (P + Q) ≥ min (index P) (index Q)`, `index (P * Q) = index P + index Q`,
`index P = ⊤ ↔ P = 0`; with the derivative estimate
`index (hasseDeriv μ P) ≥ index P − ∑ j, μ j / d j`; invariance under an injective ring
homomorphism and under translation of `α` to `0`; homogeneity in `d`; and, as the test that the
definition means what it should, agreement with `Polynomial.rootMultiplicity` for `σ = Unit` and
`d = 1`. ⚠ Multiplicativity is the statement that the lowest weighted-degree part of the Taylor
expansion at `α` is multiplicative, which needs `R` to have no zero divisors and nothing about
its characteristic — provided the derivatives are Hasse derivatives. With `pderiv` the definition
itself is wrong in characteristic `p`.

⚠ **The milestone is one identity about coefficients, and it is Layer 2.1's.** Translating so
that `α` becomes the origin turns the Hasse derivatives at `α` into the coefficients at `0`:
`coeff μ (P (X + α)) = (∂_μ P)(α)`, which is the substitution formula of 2.1 read as a statement
about one polynomial rather than two. After it the index mentions neither a derivative nor a
point, and is the **weighted order** of the translate — the least weight `∑ j, μ j / d j` of a
monomial occurring in it. Every property above is a property of that order, and the file proving
them knows nothing about this roadmap.

⚠ **Multiplicativity needs no monomial order, and nothing at all about the variables.** The
textbook proof refines the weight by a term order so as to name a unique lowest *term* in each
factor, which would need `σ` well-ordered — a hypothesis the statement does not have and Roth's
lemma would not supply. The lowest weighted **homogeneous parts** are polynomials rather than
terms, and they multiply because Mathlib's weighted homogeneous components are a grading
(`IsWeightedHomogeneous.mul`); the absence of zero divisors is used exactly once, to know that
the product of the two lowest parts is not zero. The half `index P + index Q ≤ index (P * Q)`
needs nothing whatever.

⚠ **`0 < d j` is never used, and the degenerate case is the opposite of the expected one.**
Nonnegativity of the weights is what distributes the single `ENNReal.ofReal` of the definition
over the sum, and that is all the positivity any of the theorems needs — they are stated with
`0 ≤ d j`. Strict positivity is still the right thing to *read*, because Lean's `k / 0 = 0` makes
a variable of weight `0` invisible to the index rather than making the index infinite: at
`d j = 0` the index of `X j` is `0`, not `⊤`, which is not the degeneration Bombieri–Gubler are
excluding.

⚠ **The agreement with `rootMultiplicity` needs no domain, and the nonvanishing hypothesis is
Mathlib's junk value rather than ours.** `Polynomial.rootMultiplicity a p` is the trailing degree
of the translate over any commutative ring, so the prototype's `IsDomain` came out; what cannot
come out is `P ≠ 0`, because `rootMultiplicity a 0 = 0` while the index of `0` is `⊤`, which is
the correct value of a valuation and not a junk one.

**2.4 Generalized Wronskians** (Bombieri–Gubler, Proposition 6.3.10) — **landed**. Over a field
`K` of characteristic zero, polynomials `φ 1, …, φ n : MvPolynomial σ K` are linearly independent
over `K` if and only if some generalized Wronskian `det (hasseDeriv (μ i) (φ j))` with
`∑ j, μ i j ≤ i − 1` for each `i` is not the zero polynomial. The milestone includes the
univariate criterion it reduces to by the Kronecker substitution — `n` polynomials in `K[t]` are
linearly independent if and only if `det (derivative^[i − 1] (φ j))` is nonzero — which Mathlib
does not have: `Polynomial.wronskian` is the two-polynomial form. Define the `n`-polynomial
Wronskian as a determinant so that the existing one is its `n = 2` case. ⚠ Characteristic zero is
essential (`1` and `t^p` in characteristic `p`). In
`DiophantineApproximation/Wronskian.lean` (`Polynomial.wronskianDet`,
`Polynomial.hasseWronskianDet`, `Polynomial.linearIndependent_iff_wronskianDet_ne_zero`) and
`DiophantineApproximation/GeneralizedWronskian.lean` (`MvPolynomial.genWronskian`,
`MvPolynomial.linearIndependent_iff_exists_genWronskian_ne_zero`).

⚠ **The univariate criterion is the milestone, and it is proved by leading coefficients.** The
classical proof differentiates a relation with coefficients in `K(t)` and uses that the kernel of
`d/dt` is `K`; the proof here never leaves the polynomial ring. Every term of the Leibniz
expansion of the Wronskian sits in the **same** degree, `∑ j, deg ψ j − ∑ i, i`, because
differentiating `i` times lowers a degree by `i` whichever column it happens in. So the top
coefficient of the Wronskian of a family with pairwise distinct degrees `d j` — and every
finite-dimensional space of polynomials has a basis with pairwise distinct degrees, by one
elimination on leading terms — is the determinant of the binomial coefficients `(d j).choose i`,
which is nonzero exactly because **a polynomial with `n` terms cannot vanish to order `n` at
`1`**: apply the Euler operator `p ↦ t p'`, which lowers the order of vanishing at `1` by at most
one and multiplies `t^d` by `d`, and read off a Vandermonde determinant in the exponents. That
lacunary statement is the only arithmetic in the whole milestone.

⚠ **The chain rule for the Kronecker substitution is Layer 2.1's Taylor formula, and the order
bound `|μ i| ≤ i` is not imposed but produced.** Substituting `x_s ↦ t^{e_s}` and then expanding
around `t = a` is the same as translating the variables to `a^e` and then substituting
`x_s ↦ (a + u)^{e_s} − a^{e_s}` — polynomials with **zero constant term**. Hence the coefficient
of `u^i` in the image of a monomial `x^ν` vanishes as soon as `i < |ν|`, and the `i`-th row of the
one-variable Wronskian matrix is a `K`-linear combination of the vectors `(∂_ν φ j)(a^e)` with
`|ν| ≤ i`; expanding the determinant multilinearly in its rows produces an admissible generalized
Wronskian. No Faà di Bruno formula is needed, and no derivative of a composite is ever computed.

⚠ **Nothing is assumed about `σ`.** The Kronecker weights have only to separate the finitely many
exponent vectors that actually occur, and the weights `e t = x^{ι t}` do so unless `x` is a root
of one of finitely many nonzero polynomials over `ℤ` — an argument that never enumerates the
variables, where the usual base-`B` digit construction would have to.
`Finsupp.exists_weight_injOn` is the reusable half of it and mentions no polynomial ring.

⚠ **The easy half is free and uniform.** A linear relation over `K` is a relation between the
*columns* of the matrix, which kills the determinant over the integral domain `MvPolynomial σ K`:
it holds at **every** family of orders, in every characteristic, and uses no property of the
derivative beyond `K`-linearity. Characteristic zero is used only in the hard half, and there
twice — in the binomial determinant, and in the factor `∏ i, i !` relating the two normalisations
of the Wronskian.

**2.5 Counting and volume** (Bombieri–Gubler 6.3.3, Lemma 6.3.5, and (7.23)–(7.25)) —
**landed**. Three estimates, all elementary and all needed with explicit constants. *Lattice
points:* with `V_m(t)` the volume of `{x ∈ [0,1]^m | ∑ x j ≤ t}`, the number of `i` with
`0 ≤ i j ≤ d j` and `∑ j, i j / d j ≤ t` lies between `V_m(t) ∏ d j` and
`V_m(t) (1 + max 1 t⁻¹ ∑ j, 1/d j)^m ∏ d j`. *The tail:* `V_m((1/2 − ε) m) ≤ exp (−6 m ε²)` for
`0 ≤ ε ≤ 1/2`. *The multihomogeneous tail:* with `n ≥ 1` and `0 < η ≤ 2/(n + 1)`, the proportion
of exponent tuples `J` of multidegree `(d_1, …, d_m)` in `m` blocks of `n + 1` variables with
`∑ h, J h i / d h ≤ m/(n + 1) − m η` for a fixed `i` is, in the limit, less than
`exp (−(n + 1)(n + 2) η² m / 4)`; state it as a bound on the volume, as the book does, together
with the lattice-point comparison that makes it a count. The proofs are one exponential-moment
estimate each. State them in a file that imports no number theory.

⚠ **They are one exponential-moment estimate, not one each.** The lemma is
`MeasureTheory.setIntegral_prod_le_exp_mul_pow`: for a nonnegative weight `g` on the line,
`∫_{∑ x j ≤ s} ∏ j, g (x j) ≤ exp (λ s) · (∫ exp (−λ x) g x)^m`. Both tails are that one bound at
two weights — the indicator of `[0,1]`, and the Beta`(1, n)` density `n (1 − x)^{n−1}` of one
coordinate of a point taken uniformly in the standard `n`-simplex — and what separates them is a
single pointwise inequality about `exp`. Mathlib's
`MeasureTheory.integral_fintype_prod_volume_eq_pow` is what decouples the coordinates; nothing
probabilistic is needed and no independence is ever mentioned.

⚠ **Every restriction the book puts on the parameters is an artefact of its proof, and all three
came out.** `ε ≤ 1/2` in Lemma 6.3.5 is vacuous, since beyond `ε = 1/2` the region is empty; and
`0 < λ ≤ n + 4` and `η ≤ 2/(n + 1)` in (7.24)–(7.25) are the price of the book's method, which
truncates the alternating series `∑ (−λ)^k/(n+k)!` after three terms and has to pair off the tail
to see that the rest is negative. The pointwise bound `exp(−u) ≤ 1 − u + u²/2` gives exactly those
three terms for **every** `u ≥ 0`, and it follows in three lines from Mathlib's
`Real.quadratic_le_exp_of_nonneg` and the identity `(1+u+u²/2)(1−u+u²/2) = 1 + u⁴/4`. The landed
statements assume only `0 ≤ ε` and `0 ≤ η`.

⚠ **The `6` is `6^k k! ≤ (2k+1)!`, sharp at `k = 1`.** The uniform weight needs
`sinh u ≤ u exp(u²/6)`, which is that comparison of the two power series term by term, and the
constant `−6 m ε²` then comes out of `λ = 12 ε` on the nose. Mathlib has no inequality of this
kind for `Real.sinh`, so `Real.sinh_le_mul_exp_sq_div_six` is new; it is the only place in the
layer where a series is summed, and the only use made of `Real.exp`'s power series.

⚠ **The multihomogeneous estimate is stated as a proportion, and that is what removes the simplex
volume.** The book's `V` is an `mn`-dimensional volume which the book itself rewrites, in the very
next display, as an integral over `[0,1]^m` against the density of one simplex coordinate — and
that rewriting *is* the volume `r^k/k!` of a simplex, which Mathlib does not have and which would
have to be built by induction with Fubini on a pi measure. Stating the bound against the
**normalised** density makes the factor `V₀ = (n!)^{−m}` cancel from both sides of the book's
`V/V₀`, and what is left is literally the proportion this milestone asks for. The price is that
the landed statement bounds an integral against a probability density rather than an
`mn`-dimensional volume; the two differ by that missing factor and by nothing else.

⚠ **Both lattice-point bounds are one covering argument, and only the upper one needs `t > 0`.**
Attach to each admissible `i` the half-open box `∏ j, [i j/d j, (i j + 1)/d j)`. Rounding the
coordinates of a point of `𝒱_m(t)` down lands in such a box, so the boxes *cover* the region and
the lower bound needs no disjointness at all; and the boxes, which are disjoint, fit inside
`(1 + ρ) 𝒱_m(t)` for the book's `ρ = max 1 t⁻¹ ∑ j, 1/d j`, so the upper bound is
`Measure.addHaar_smul` and nothing else. At `t = 0` the origin is always an admissible lattice
point while `V_m(0) = 0`, so the hypothesis `t > 0` on the upper bound is not decoration — the
acceptance criteria record it as a rejection test.

**2.6 The auxiliary polynomial** (Bombieri–Gubler, Lemma 6.3.4 — the index theorem) —
**landed**. Let `F/K` be
a finite extension of degree `r`, let `α k : Fin m → F` for `k : Fin N` be points, and let
`t k > 0` with `r ∑ k, V_m(t k) < 1`. For every `δ > 0` there is `D₀` such that for all
`d : Fin m → ℕ` with `D₀ ≤ d j` there is a nonzero `P : MvPolynomial (Fin m) K` with
`degreeOf j P ≤ d j`, `index d (α k) P ≥ t k` for every `k`, and
`h(P) ≤ r/(1 − r ∑ k, V_m(t k)) · ∑ k, ∑ j, V_m(t k) (h(α k j) + log 2 + δ) d j`, in absolute
logarithmic heights. This is the `ε`–`D₀` reading of the book's `o(1)`, and it is the form to
state: every application lets `d j → ∞` with `m` fixed. Route: `ArithmeticHeights` 5.7 with the
relative Siegel lemma of 5.6 behind it, the conditions being the vanishing of
`hasseDeriv μ P` at `α k` for `∑ j, μ j / d j < t k`, counted by 2.5, with rows of height at most
`∏ j, (2 H(α k j)) ^ d j`. No other Siegel lemma is proved here. In
`DiophantineApproximation/AuxiliaryPolynomial.lean`
(`MvPolynomial.exists_ne_zero_le_index_logHeight_le`), on
`…/BoxMonomial.lean`, `…/MonomialHeight.lean` and `…/IndexConditions.lean`.

⚠ **The route is 5.6, not 5.7, and that is a statement about coefficient spaces rather than about
Siegel's lemma.** Layer 5.7 packages the relative Siegel lemma on the coefficients of a
polynomial of bounded **total** degree — the simplex of monomials — and Lemma 6.3.4 bounds the
**partial** degrees, which is a box. Neither shape contains the other usefully: shrinking `D`
until the simplex fits in the box discards the monomials of large total degree that carry the
construction, and enlarging it breaks the degree bound 2.7 needs. So 2.6 applies 5.6 —
`NumberField.exists_ne_zero_mem_ker_absMulHeight_le_relative_rank`, which is stated for an
arbitrary finite index type — to `∀ j, Fin (d j + 1)` directly, and carries its own dictionary
`MvPolynomial.ofBox` between coefficient vectors and polynomials. Naming the box by a `Pi` type
rather than by a subtype of the exponents is what makes its cardinality `∏ j, (d j + 1)` free and
a condition row literally a multiplication table.

⚠ **The rank form that 5.7 sent 5.6 back for is not what 2.6 needed.** What Layer 2.5 counts is
the number of *conditions*; `Matrix.rank_le_card_height` is the only thing said about the rank
here, and the row form of 5.6 would have served. Nothing in Roth's method asks whether conditions
at distinct orders at distinct points are independent.

⚠ **The `log 2` of the bound is the binomial coefficient, and it is the only loss in the row
height.** The entry of a row at the monomial `X ^ I` is
`(∏ j, (I j).choose (μ j)) ∏ j, α j ^ (I j − μ j)`, a multiplication table over the variables, so
Mathlib's Segre relation gives its height as a product of one-variable heights *exactly*; and the
tuple of powers `α j ^ k, k ≤ d j`, has height *exactly* `H(α j) ^ d j`, an equality this roadmap
had to prove and Mathlib does not have. The single estimate made anywhere is
`(I j).choose (μ j) ≤ 2 ^ d j`. The `+ δ` of the milestone pays for something else entirely.

⚠ **Three quantities have to be negligible and they are of three different orders, which is the
whole content of the book's `o(1)`.** The lattice-point correction `(1 + ρ)^m − 1` is `O(m²/D₀)`;
the `√M` by which the Arakelov normalization of Siegel's lemma exceeds the sup-norm one
contributes `½ log M = O(∑ j, log d j)`; and the discriminant of `K` contributes a constant. All
three are `o(∑ j, d j)`, and `δ` is exactly the room they need. The elementary inequalities behind
them are `log y ≤ 2 √y` and `(1 + x)^m ≤ 1 + x m 2^m`; neither is sharp and neither needs to be.

⚠ **`m = 0` is excluded by the hypothesis rather than handled by the proof.** `V₀(t) = 1` for
every `t ≥ 0`, so the feasibility hypothesis reads `r N < 1` and forces `N = 0`. That is as it
should be — a nonzero polynomial in no variables is a nonzero constant, whose index is `0` at
every point — and the acceptance criteria record it as a rejection test. The positivity
`0 < V_m(t)` for `t > 0` that this argument needs was added to 2.5.

**2.7 Roth's lemma** (Bombieri–Gubler, Lemma 6.3.7, with the base case 6.3.9) — **landed**. Let
`P : MvPolynomial (Fin m) K` be nonzero over a number field, with `degreeOf j P ≤ d j` and
`1 ≤ d j`, let `ξ : Fin m → K`, and let `0 < σ ≤ 1/2`. If `d (j + 1) / d j ≤ σ` for all `j` and
`σ⁻¹ (h(P) + 4 m d 0) ≤ d j · h(ξ j)` for all `j`, then
`index d ξ P ≤ 2 m σ ^ ((1/2) ^ (m − 1))`. Heights are absolute logarithmic heights; stated with
Mathlib's relative ones, the term `4 m d 0` carries the factor `totalWeight K` — which is how it
is stated, in `MvPolynomial.index_le_of_degree_ratio`. The base case `m = 1` is at the book's own
constant, `index · d 0 · h(ξ 0) ≤ h(P) + d 0 log 2`, from `ArithmeticHeights` 1.2 and 2.3:
`(X − ξ)^k` divides `P`. The induction is 2.4 applied to a decomposition
`P = ∑ f_j(x_1, …, x_{m−1}) g_j(x_m)` with both families linearly independent, 2.2 for the height
of the product of the two Wronskians, 2.1 and the local estimates of `ArithmeticHeights` 2.2–2.3
for the height of a determinant of derivatives, and 2.3 for the index of a determinant. ⚠ The
constants `4` and `2 m` are the book's and are not sharp; they are kept, because Layer 5.3 quotes
this lemma with them. ⚠ The sharpening of this lemma through Faltings's product theorem is *not*
this milestone; see *Long horizon*. In
`DiophantineApproximation/{HeightTransport,IndexRename,PolynomialDeterminantHeight,
RothDecomposition,RothDeterminant,RothBaseCase,RothEstimates,RothLemma}.lean`.

⚠ **The induction runs on `θ`, not on `σ`, and that is the whole reason no real power occurs
inside it.** Written with the book's `σ` the inductive step would have to replace `σ` by `√σ`,
and a `Real.rpow` would then appear in every hypothesis of every recursive call. Written with a
parameter `θ` and `σ = θ ^ (2 ^ m)` the step replaces `θ` by `θ ^ 2` and **leaves `σ` alone**: the
hypotheses on the degrees and on the heights carry over verbatim, the conclusion is
`index ≤ 2 m θ`, and the book's exponent is a single change of variable, `θ = σ ^ ((1/2)^(m−1))`,
made once at the end. Nothing in the induction knows what `Real.rpow` is.

⚠ **The constant `2 m` is uniform, and the reduction to `θ < 1/2` is what makes it so.** At
`θ ≥ 1/2` the conclusion is free: a nonzero polynomial of partial degrees at most `d` has index at
most the number of variables — `MvPolynomial.index_le_card`, which is a statement about the
support of the *translate* and needs 2.6's `hasseDeriv_eq_zero_of_lt` rather than a degree bound
on `taylorAt` — and `2 m θ ≥ m` there. So the step may assume `θ < 1/2`, and it is `θ² < θ/2` that
closes both halves of the quadratic estimate with room to spare. The first attempt at this proof
carried the one-variable case at its own sharper constant `1`, and the reduction removed the need
for it; the milestone's `2 m` is what the file proves at every `m ≥ 1`.

⚠ **The separated variable is `X 0`, so the induction runs with the degrees *increasing*.**
Mathlib's `MvPolynomial.finSuccEquiv` splits off the **first** variable, and Roth's lemma
separates the one of **smallest** degree; rather than build a `finSuccEquivLast`, the induction is
stated with `d j ≤ σ · d (j + 1)` and the book's decreasing form is recovered once, at the end,
by `rename Fin.rev` — under which the index, the height and the partial degrees all transform by
lemmas the milestone needed anyway.

⚠ **Both families of the decomposition are independent for one reason, and it is not a
minimality argument.** The textbook proof takes `p` minimal in `P = ∑ f_i g_i` and reads the
independence of both families off minimality. Here the first family is chosen to be a *basis of
the span of the coefficients* of `P` along the separated variable; then the independence of the
second is a statement about a linear functional — a relation among the coefficient columns kills
every coefficient of `P`, hence the span, hence every basis vector — and `p ≤ d 0 + 1` is
`finrank_range_le_card`. The degree bounds on the two families are then not needed at all:
`MvPolynomial.degreeOf_mul_eq` reads the degrees of the two Wronskians off the degrees of the
determinant, which are bounded entry by entry.

⚠ **There is no projective bound on the height of a *sum* of polynomials, so the determinant is
estimated at each absolute value and transported once.** `H(N X + 1) = N` while both summands
have height `1`, so the Leibniz expansion cannot be bounded term by term in the projective
height, and the general shape of the estimate — `p!` and the multiplication constants at the
archimedean absolute values, nothing at the others — has to be carried locally. The transport
that does it is the one with a **one-sided** inequality at the nonarchimedean absolute values,
which `ArithmeticHeights`'s `Finsupp.mulHeight_le_of_forall_iSup_le` does not provide: that one
demands an *equality* there, which Gauss's lemma supplies for a product and a Hasse derivative
does not. The obstruction Layer 2.6 hit — Mathlib's finite-support fact for the local factor of a
*family* is private — is removed in three lines by
`Finsupp.hasFiniteMulSupport_iSup_apply`, which derives it from
`AdmissibleAbsValues.hasFiniteMulSupport` for a single element.

⚠ **The support count, not the total degree, is what keeps the constant linear in `p`, and
`log 2 < 0.694` is load-bearing.** Iterating `MvPolynomial.iSup_coeff_mul_le_two_pow` over a
`p`-fold product costs `2 ^ (D p (p+1) / 2)`, because the accumulated factor's total degree grows
at every step; iterating `MvPolynomial.iSup_coeff_mul_le_card_support`, whose constant is the
*smaller* of the two supports and so is always the new factor's, costs `2 ^ (D p)`. In Roth's
lemma `p` can be as large as the smallest degree, so the difference is the whole estimate. What
then has to fit in the hypothesis's `4 p d` is `log p! + 2 D p log 2` with `D = ∑ j, d j ≤ 2 d`
and `p ≤ d + 1`: that is `p d + 4 p d log 2 ≈ 3.78 p d`, and with only `log 2 ≤ 1` it would be
`5 p d` and the milestone's constant would be wrong.

⚠ **Only `Finsupp.degree (μ i) ≤ i` is used of Layer 2.4, and its univariate half is not used at
all.** The orders of the generalized Wronskian never have to be pinned — an order reaching into
the wrong variable set kills its row, which is a theorem rather than a choice — and the
*multivariate* criterion serves for the family in one variable as well as for the family in
`m − 1`. So `Polynomial.hasseWronskianDet`, the `n`-polynomial Wronskian 2.4 had to build because
Mathlib has only `Polynomial.wronskian`, is consumed only inside 2.4's own proof.

⚠ **`0 < totalWeight K` is not decoration, which is why the milestone is stated over a number
field.** At `totalWeight K = 0` the hypothesis of the base case reads `h(P) ≤ σ d h(ξ)` with both
sides allowed to vanish, and nothing bounds the multiplicity of the root; the rest of the proof
is uniform in `totalWeight K` and would go through. Roth's theorem is false over function fields,
and this is where that shows up.

### Layer 3: Roth's theorem

**3.1 Approximation classes** (Bombieri–Gubler 6.4.2–6.4.4; reused at 7.5.6) — **landed**. For a
finite index set `A` and a family of maps `φ a : X → [0, 1]` with `∑ a, φ a x ≤ 1`, the partition
of `X` by the cell of side `1/N` containing `(φ a x)_a`: the number of nonempty cells is at most
`(N + |A|).choose |A|` (Lemma 6.4.3) — `Set.ncard_image_cellIndex_le`, and the count of *labels*
is that number exactly, `Set.ncard_setOf_sum_le` — and an infinite `X` has an infinite cell for
every `N`, `Set.Infinite.exists_cellIndex_eq`. With it: `(L, M)`-**independent** sequences,
`h(β 0) ≥ L` and `h(β (j + 1)) ≥ M h(β j)`, exist inside every infinite subset of `K`, by
Northcott — `NumberField.exists_isHeightIndependent`, and the two reductions together are
`NumberField.exists_cellIndex_eq_and_isHeightIndependent`. Stated once, abstractly, because
Layers 3.2, 3.7 and 5.1 each use it for a different family `φ`. In
`DiophantineApproximation/{ApproximationClass,IndependentHeights}.lean`.

⚠ **Lemma 6.4.3 is an equality, and the slack is a coordinate.** The book writes "the number of
solutions of this inequality is `(N + |S|).choose |S|`" and that is literally true: adding one
coordinate for `N − ∑ a, c a` turns the labels into the tuples on `Option A` that sum to `N`
*exactly*, which is Mathlib's `Finset.card_finsuppAntidiag_nat_eq_choose`. No induction on `N`
and no hockey-stick identity appears. What the applications quote is the inequality, because the
labels are what is counted and not every label is attained.

⚠ **What the milestone did not name is what the consumer actually uses: the book's (6.9).** An
approximation class does not merely say that its members behave alike — for a family `f` of
numbers in `(0, 1]` with `Λ = ∏ b, f b < 1` it traps every coordinate,
`Λ ^ ((c a + 1)/N) < f a ≤ Λ ^ (c a / N)`, so that `|A|` unrelated local factors are replaced by
one quantity raised to `|A|` exponents known to within `1/N`. That is the form Layers 3.2 and 3.7
consume, and it is proved here — `Real.le_rpow_cellIndex_div` and
`Real.rpow_cellIndex_add_one_div_lt`. The two halves are `≤` and `<` because the cell is
half-open, and neither can be strengthened: the upper half is attained.

⚠ **The hypothesis `∑ a, φ a x ≤ 1` is what makes the count a binomial coefficient.** Without it
the labels are the `(N + 1)^{|A|}` cells of the *cube*, not the `(N + |A|).choose |A|` cells that
meet the simplex — at `N = 1` and `|A| = 2`, four against three. The lower bound (6.10) of the
book needs more still, that the point lie *on* the hyperplane `∑ a, y a = 1`; the count and the
pigeonhole do not, and are stated with `≤ 1` so that a family that is only subadditive still has
a class.

⚠ **The profile is where `0 < f a` matters, and it is the book's "non-trivial approximation".** A
`β` equal to a target `α v` has local factor `0` at `v` and no logarithmic profile; there is at
most one such `β` per place, so a consumer discards finitely many solutions before classifying
the rest — which is what `Λ(β) < 1` does in the book.

⚠ **Northcott is the only arithmetic in the milestone, and it gives an infinite sequence.** The
recursion asks each time for an element of `X` whose height exceeds `M h(β j)`, and one exists
because a set of bounded height is finite while `X` is not; the book's "infinite subsequence of
`(L, M)`-independent elements" is therefore the statement proved, and the `m`-tuple the auxiliary
polynomial consumes is a restriction of it. `1 < M` and `0 < L` are needed only to make the terms
*distinct*, `NumberField.IsHeightIndependent.injective`; existence holds at every `L` and `M`.

**3.2 Roth's theorem** (Bombieri–Gubler, Theorem 6.4.1; Roth 1955 for `K = ℚ`, `S∞ = {∞}`;
Ridout 1958 over `ℚ`; Lang for number fields). Let `F/K` be a finite extension, `S∞` and `S₀`
finite sets of places of `K`, `w v` an absolute value of `F` over `v` and `α v ∈ F` for each `v`
in them, and `κ > 2`. Then the set of `β ∈ K` with

```text
(∏ v ∈ S∞, min 1 (w v (β − α v)) ^ v.mult) * ∏ v ∈ S₀, min 1 (w v (β − α v))  ≤  mulHeight₁ β ^ (−κ)
```

is finite — **landed**, `NumberField.finite_setOf_prod_min_one_le`, in
`DiophantineApproximation/{GlobalBound,MvPolynomialEvalBound,RothLocalBound,RothClass,
RothKeyInequality,RothAuxiliary,RothTheorem}.lean`. This is the book's statement raised to the
power `d`. The route is the one this milestone named, 6.4.2–6.4.10: reduce to
one approximation class (3.1) — `NumberField.exists_isHeightIndependent_forall_le_rpow` — take
`m` with `r |S| exp (−6 m ε²) < 1/2` and an
`(L, M)`-independent `m`-tuple in it, build `P` by 2.6 with `d j = ⌈D / h(β j)⌉`, find by 2.7 a
derivative `Q` of `P` of small order with `Q(β) ≠ 0` (Lemma 6.4.7) —
`NumberField.exists_auxiliary_deriv` — bound `Q(β)` above at each
place of `S` by the Taylor expansion at `(α v, …, α v)` (2.1), below by the product formula, and
compare — `NumberField.roth_key_inequality`.
⚠ The book's Theorem 6.2.3 — targets in the completions `K_v` — is this theorem and not a
different one: a `K`-algebraic element of `K_v` *is* an element of a finite extension with an
absolute value over `v` (0.1). It is not stated separately.

⚠ **Step IV is the product formula over all the places, and Layer 0.4 will not do it.** This
milestone's own route said "below by 0.4", and that is wrong. The fundamental inequality bounds
`∏_{v ∈ S} min 1 |y|_v ^ w_v` from below by `H(y)^{−1}`, which cuts the product down to `S`; but
the local bound on `|Q(β)|_v` carries the local factor of the *coefficients* of `Q`, and the
product of those over `S` alone is not bounded by `h(Q)` — the complementary product can be
smaller than `1`, and the height is projective, so no normalisation repairs it. Charging `h(Q)`
and the `h(β j)` twice turns the final inequality `κ(1 − |S|/N)(1/2 − 4ε) ≤ 1 + C/L` into
`κ(…) ≤ 2 + C/L` and proves Roth's theorem only for `κ > 4`. What Step IV needs is
`NumberField.one_le_of_forall_apply_le_sum`: local upper bounds at **every** place, multiplied by
the product formula. Layer 0.4 is consumed by Layers 5 and 7, not by this one.

⚠ **Nothing tends to infinity.** The book lets `D → ∞` and reads off (6.22). Here every error
term is explicit: all but one are `O(D/L)` and are killed by choosing `L` large, which happens
before `D` is introduced, and the one that is not is `([K : ℚ] + 2 ∑ w_v) log (D + 2)`, coming
from the `∏ j (d j + 1)` monomials of the box. `Real.exists_le_and_mul_log_add_lt` — a logarithm
is eventually beaten by any positive multiple of the identity — then produces one explicit `D`.
No filter, no `IsLittleO` and no `Tendsto` occurs anywhere in the milestone.

⚠ **`κ > 2` is used exactly once, as `1/κ < 1/2`.** It is what leaves room for the two losses,
`4ε` from the differentiation of the auxiliary polynomial and `|S|/N` from the size of the
approximation class, and the contradiction is `κ(1 − |S|/N)(1/2 − 4ε) > 1`. Every other step is
uniform in `κ`. The book's `(1/2 − 3ε)` is `(1/2 − 4ε)` here, because Roth's lemma is quoted
through an infimum and a strict inequality is needed to produce an order; `ε` is at the caller's
disposal, so the constant is immaterial and nothing downstream sees it.

⚠ **The index type of the places is the disjoint union of the two typed finsets**, `↥S∞ ⊕ ↥S₀`,
with `NumberField.sPlaceAbsValue` and `NumberField.sPlaceWeight` reading off the absolute value
and the weight. That is the shape Layer 3.1 asked for, and the weights are what make (6.10)
usable without a second estimate: `∑_a c a ≥ N(1 − |S|/N)` is unweighted, the product over the
places of `S` is weighted, and every weight is at least `1`.

⚠ **Two families of solutions are discarded before the classification, and both are forced.** A
`β` of height at most `1` has `Λ(β) ≤ 1` with no room and no logarithmic profile; a `β` equal to
a target at some place has local factor `0` there. The first set is finite by Northcott, the
second has at most one element per place, and an infinite solution set stays infinite after both
are removed. This is the book's "non-trivial approximation", and it is where `0 < κ` is used.

**3.3 The forms applications quote.** Each is 3.2 for a choice of data, and each is stated.
*Targets at infinity* (6.2.5): a target may be the point `∞`, with local factor
`min 1 (v β)⁻¹`; by a rational Möbius change of variable, under which `mulHeight₁` changes by a
bounded factor. State 3.2 with targets in `OnePoint F` so that every later form is an instance.
*Roth:* `irrationalityExponent α = 2` for every real algebraic irrational `α` — the value Layer
1.1 leaves open between `2` and `d`. *Ridout:* for real algebraic `α`, finite sets of primes
`S₁`, `S₂` and `ε > 0`, finitely many `p/q` in lowest terms with
`|α − p/q| · ∏_{ℓ ∈ S₁} |p|_ℓ · ∏_{ℓ ∈ S₂} |q|_ℓ ≤ max(|p|, |q|)^{−2−ε}`, with target `0` at
`S₁` and `∞` at `S₂`, after splitting the solutions by which of `p`, `q` a prime of `S₁ ∩ S₂`
divides. *`p`-adic* (6.2.6): for `α` in a number field `F`, `w` over `Rat.AbsoluteValue.padic p`
and `ε > 0`, finitely many `n ∈ ℤ` with `w (α − n) ≤ |n|^{−1−ε}`.

**3.4 Roth's theorem on the projective line.** The Subspace Theorem of Layer 6.3 for
`Fintype.card ι = 2`, proved *here*, from 3.3: at each place a solution `x` is close to the zero
of at most one of the two forms, so the solutions split into `2^{|S|}` sets according to which,
and on each set `approxProd` is comparable to the left side of 3.2 for that choice of targets,
with `β = x 1 / x 0`. Conversely 3.2 is this statement for `L v 0 = X 0`,
`L v 1 = X 1 − α v X 0` (Bombieri–Gubler, Example 7.2.7); prove both directions. This is the
interface Layers 8.1, 8.3, 8.4 and 8.6 consume, so that the two-variable unit equation and
everything resting on it are available without Layers 4–6.

**3.5 Mahler's theorem on `(p/q)^k`** (Mahler 1957; Bombieri–Gubler 6.2.7 for `3/2`). For coprime
integers `p > q ≥ 2` and `ε > 0`, the distance from `(p/q)^k` to the nearest integer exceeds
`exp (−ε k)` for all but finitely many `k`. Route: 3.3 over `ℚ` with `S₀` the primes dividing
`p q`, targets `1` at `∞`, `∞` at the primes of `q` and `0` at the primes of `p`, and
`β = p^k / (N q^k)` with `N` the nearest integer; the factor `|N|_ℓ` that appears when
`gcd (N, p) ≠ 1` cancels between the two sides. The acceptance test for 3.3, and the input to the
formula `g(k) = 2^k + ⌊(3/2)^k⌋ − 2` in Waring's problem for large `k`, which is not a target.

**3.6 Thue's equation** (Thue 1909; Bombieri–Gubler 6.2.1). For `G ∈ ℤ[X, Y]` homogeneous with at
least three pairwise non-proportional linear factors over `ℂ` and `m ≠ 0`, the equation
`G(x, y) = m` has finitely many solutions `(x, y) ∈ ℤ²`. By the book's direct argument from the
classical case of 3.3; Layer 8.3 contains it, and it is here as the first Diophantine equation the
roadmap solves and the test that 3.3 is usable.

**3.7 Counting approximations** (Bombieri–Gubler, Theorem 6.5.4, Lemma 6.5.6 and 6.5.7; Davenport
and Roth 1955 for one place). *The strong gap principle:* if `β ≠ β'` are solutions of 3.2 in one
approximation class of size `1/N` with `h(β) ≤ h(β')`, then
`h(β') ≥ ((1 − |S|/N) κ − 1) h(β) − log 4`. *The count in a window:* with
`c = (1 − |S|/N) κ − 1 > 1`, at most `⌈log A / log ((c + 1)/2)⌉ · (N + |S|).choose |S|` solutions
have `h(β) ∈ (X, A X]`, for `X > log 16 / (c − 1)`. *The count of large solutions:* with `ε`,
`m`, `L`, `M`, `N` chosen as in 6.5.7, the solutions with `h(β) > L` number at most
`m ⌈log M / log ((c + 1)/2)⌉ (N + |S|).choose |S|` — a bound depending only on `κ`, `|S|` and
`[F : K]`, while `L` depends on the heights of the targets — and those with `h(β) ≤ L` are
counted by the window bound and by Northcott. Absolute logarithmic heights throughout. ⚠ This is
a bound on the **number** of solutions and gives no bound on their height; that asymmetry is the
ineffectivity of the method and should be said in the docstring.

**3.8 Moving targets** (Vojta; Bombieri–Gubler, Theorem 6.5.2). There is no infinite sequence of
pairs `(α_j, β_j)` with `α_j : S → F`, `β_j ∈ K`, `1 + ∑ v, h(α_j v) = o(h(β_j))` and each
`β_j` a solution of the inequality of 3.2 with targets `α_j`. By the proof of 3.2 with `α`
replaced by `α_j` in 2.6; the book's argument is five lines once 3.2 is structured so that the
heights of the targets enter only through the bound on `h(P)`, and the milestone is to structure
it so.

### Layer 4: parallelepipeds over a number field

Schmidt's proof is geometry of numbers applied to a family of parallelepipeds. Bombieri–Gubler
run it in the adèles (their 7.5.6 and Appendix C.2). This layer runs it in the **real**
formulation `ArithmeticHeights` pins — a `ZLattice` in a real vector space and a convex body —
and for forms with coefficients **in `K`**. Both choices are free: Layer 6.3 removes the
restriction on the coefficients by the book's own Remark 7.2.3, and the adelic second theorem is
recovered below from `ArithmeticHeights` 4.2 and 4.4. No adèle and no Haar measure on a local
field appears.

**4.1 Approximation domains** (Bombieri–Gubler 7.5.6, Lemma 7.5.7, Corollary 7.5.8). Throughout
Layers 4 and 5 and in 6.1 the set of places consists of **every** infinite place together with a
finite `S₀` — a domain with no condition at some infinite place is unbounded there, and 6.2 adds
the missing infinite places before it starts. For forms `L v i : Module.Dual K (ι → K)` linearly
independent for each such `v`, exponents `c v i : ℝ` and `Q ≥ 1`, the **approximation domain**
`NumberField.approxDomain S₀ L c Q : Set (ι → K)` is the set of `x` with
`v (L v i x) ≤ Q ^ c v i` for every infinite place `v`, every `v ∈ S₀` and all `i`, and
`v (x j) ≤ 1` for every finite place `v ∉ S₀` and all `j`. It is a set of points of `Kⁿ⁺¹` and
is defined as one. Its **weight** is
`∑ v : InfinitePlace K, v.mult * ∑ i, c v i + ∑ v ∈ S₀, ∑ i, c v i`, the exponent of `Q` in the
product of all local bounds in Mathlib's normalization; Bombieri–Gubler's `d ∑ c` is this number
after their `Q` is replaced by `Q^d`. The structure: the conditions at the finite places cut out a full
`𝓞 K`-submodule `Λ` of `Kⁿ⁺¹`, the conditions at the infinite places a compact convex symmetric
body `B` in `(K ⊗ ℝ)ⁿ⁺¹` that is a product over the infinite places of bodies balanced over
`K_v`, and the domain is `Λ ∩ B`. Prove the covolume and volume formulas that replace Lemma
7.5.7: with `a v i` the largest value of `v` that is at most `Q ^ c v i`, the index of `Λ` in
`(𝓞 K)ⁿ⁺¹` (a generalized index; `Λ` need not be contained in it) is
`∏ v ∈ S₀, v (det (L v)) * ∏ i, (a v i)⁻¹`, and the volume of `B` is the volume of the unit
body times `∏ v : InfinitePlace K, (v (det (L v))⁻¹ * ∏ i, Q ^ c v i) ^ v.mult`. Hence `vol B / covol Λ` is
`Q` to the weight, up to a factor between two constants depending only on `K`, `S₀`, `n` and the
determinants. ⚠ The book states the finite-place volume as an equality in `Q ^ c v i`; it is an
equality in `a v i` and an inequality up to `∏ v ∈ S₀, (absNorm v) ^ (n + 1)` in `Q ^ c v i`,
because `Q ^ c v i` need not lie in the value group.

**4.2 Successive minima over `K`.** For an `𝓞 K`-module `Λ` and a body `B` as in 4.1, the `l`-th
**`K`-minimum** `μ l` is the infimum of the `λ` for which `Λ ∩ λ B` contains `l` vectors linearly
independent over `K`, for `l = 1, …, n + 1`. Prove that the `K`-minima are attained and that
vectors realizing them can be chosen `K`-independent; that with `λ` the successive minima of
`ArithmeticHeights` 4.1 for `Λ` as a `ZLattice` of rank `d (n + 1)`,
`λ l ≤ μ l ≤ λ (d (l − 1) + 1)` — the right-hand inequality is the extraction lemma,
`ArithmeticHeights` 4.4 — and `λ (d l) ≤ c_K μ l`, where `c_K` is the largest absolute value of
a conjugate of a member of a fixed integral basis `ω` of `𝓞 K`: if `x 1, …, x l` realize the
first `l` `K`-minima then the `d l` vectors `ω j • x i` lie in `Λ`, because `Λ` is an
`𝓞 K`-module, are independent over `ℤ`, and lie in `c_K μ l B`, because each factor of `B` is
balanced. Deduce **Minkowski's second theorem over `K`**, two-sided:

```text
c_K^{−d(n+1)} · (2^{d(n+1)} / (d(n+1))!) · covol Λ / vol B  ≤  (μ 1 ⋯ μ (n+1))^d  ≤  2^{d(n+1)} · covol Λ / vol B,
```

from `ArithmeticHeights` 4.2 and the monotonicity of `λ`. This is the content of the adelic
theorem of Bombieri–Vaaler and McFeat (Bombieri–Gubler, Theorem C.2.11) in the only generality
the Subspace Theorem uses, and it is proved from the real one.

**4.3 The rank of an approximation domain** (Bombieri–Gubler, Definition 7.5.11, Lemma 7.5.12).
`V(Q)`, the `K`-span of the approximation domain, and its **rank** `dim V(Q)`, which is the
number of `K`-minima that are at most `1`. If the weight of the domain is negative then the rank
is at most `n` for all sufficiently large `Q`, from the lower bound of 4.2: the last minimum is
at least a positive power of `Q`. Also: for `Q` bounded the domains are contained in one bounded
set, which holds finitely many points of `Λ`, so only finitely many subspaces `V(Q)` arise from a
bounded range of `Q`.

**4.4 Evertse's lemma** (Evertse 1996; Bombieri–Gubler, Lemma 7.5.29). Let `x 1, …, x (n+1)` be a
basis of `Kⁿ⁺¹`, and for each infinite place `v` and each `v ∈ S₀` let reals `0 < μ v 1 ≤ … ≤ μ v (n+1)` satisfy
`v (L v k (x j)) ≤ μ v j` for all `k`, `j`. Then there are vectors `y 1 = x 1`,
`y i = x i + ∑ j < i, ξ i j • x j` with `ξ i j` in the `S₀`-integers, and bijections `π v`
between the vectors and the forms, such that `v (L v (π v i) (y j)) ≤ C min (μ v i) (μ v j)` at
the infinite places and `≤ min (μ v i) (μ v j)` at the finite ones, `C` depending only on `K`,
`S₀` and the forms. It is the step that replaces Mahler's theorem on compound convex bodies and
Davenport's lemma in Schmidt's original argument (7.5.27–7.5.28), neither of which this roadmap
builds. Its arithmetic input is a **simultaneous approximation property of `S`-integers**, to be
proved first and stated without completions: for every family `γ v ∈ K` indexed by the infinite
places and `S₀` there is an `S₀`-integer `ξ` with `v (ξ + γ v) ≤ 1` at each finite place of `S₀` and
`v (ξ + γ v) ≤ A` at each infinite place, `A` depending only on `K`. Route: the Chinese remainder
theorem in `𝓞 K` localized away from `S₀` for the finite conditions, then a translation by an
element of `𝓞 K`, which does not disturb them, into a bounded fundamental domain of `𝓞 K` in
`K ⊗ ℝ`. With coefficients in `K`, the `γ v` of the book's (7.40) lie in `K`, which is why the
completion-free form suffices.

**4.5 Exterior powers of a system of forms** (Bombieri–Gubler 7.5.2, (7.16)–(7.17), Lemma 7.5.33,
7.5.30–7.5.31). For `1 ≤ p ≤ n`: the forms `L v I = L v (i 1) ∧ ⋯ ∧ L v (i p)` on
`⋀[K]^p (ι → K)`, indexed by `Set.powersetCard ι p` as in `ArithmeticHeights` 3.1, are linearly
independent when the `L v i` are, their determinant is a power of `det (L v)`, and **Laplace's
identity** `L v I (y J) = det (L v (i a) (y (j b)))` holds, through Mathlib's pairing of the
exterior power with the dual. Lemma 7.5.33: for a `k`-dimensional `W ≤ Kⁿ⁺¹` with basis extended
to a basis `x` of `Kⁿ⁺¹`, the span in `⋀^{n+1−k}` of the wedges `x J` with
`J ≠ {k+1, …, n+1}` depends only on `W` and determines `W`. And Lemma 7.5.31 in the language of
4.1–4.2: from the domain of `L`, `c`, `Q` of rank at most `n`, with `k` chosen in `[rank, n]` to
minimize `μ k / μ (k+1)` and `y` the vectors of 4.4 applied to vectors realizing the
`K`-minima, the wedges `y J` lie in an approximation domain for the forms `L v I` in
`⋀^{n+1−k}` — whose exponents depend on the `K`-minima of the original domain — of which all
`K`-minima but the last are at most `1` and the last is at least a positive power of `Q`.

### Layer 5: the Subspace machinery

Bombieri–Gubler's Theorem 7.5.13 — the Subspace Theorem under the extra hypothesis that the
penultimate minimum is small — by the Roth machinery of Layer 2 in multihomogeneous form.
Coefficients in `K` throughout, as in Layer 4.

**5.1 Reductions** (Bombieri–Gubler, Theorem 7.2.6, Lemma 7.5.4, Corollary 7.5.5, 7.5.6).
*Projective to affine:* by 0.3, after enlarging `S₀` every projective solution has a primitive
`S₀`-integral representative, for which `mulHeight x` equals the product of the local sup norms
over the infinite places and `S₀`. *Unit normalization* (Lemma 7.5.4): a primitive `x` has an
`S₀`-unit multiple `u • x` whose **affine** height (`ArithmeticHeights` 0.5) exceeds the
projective height of `x` by at most a constant depending on `K` and `S₀`, because the
`S₀`-logarithmic image of the `S₀`-units is a full lattice in the trace-zero hyperplane
(`ArithmeticHeights` 6.5); consequently (Corollary 7.5.5) each `log (v (L v i (u • x)))` is
`O(h(x))`, from 0.4. *Classes* (7.5.6): by 3.1, every solution of the inequality of 6.2 with no
`L v i x = 0`, so normalized, lies in `approxDomain S₀ L c (mulHeight x)` for one of finitely
many exponent systems `c` on a grid of mesh `1/N`, each of weight at most `−ε/2`.

**5.2 The multihomogeneous auxiliary polynomial** (Bombieri–Gubler 7.5.14, Lemma 7.5.15). For
`m` blocks of variables `X h : ι → K` and a multidegree `d : Fin m → ℕ`, the space of
multihomogeneous polynomials of multidegree `d`, of dimension `∏ h, (d h + n).choose n`; the
expansion of `hasseDeriv I P` in the monomials `∏ h, ∏ i, (L v i (X h)) ^ (J h i)` for each `v`,
with coefficients `a(L v; J; I)`; and the lemma: for `0 < η ≤ 2/(n+1)` and
`m ≥ 4 log (2 (n+1) |S|) / ((n+1)(n+2) η²)` there are constants `C₂`, `C₃` depending only on `K`
and the forms such that for all sufficiently large `d` there is a nonzero `P` of multidegree `d`
with `h(P) ≤ C₂ ∑ d h`, `h(a(L v; ·; I)) ≤ C₃ ∑ d h`, and `a(L v; J; I) = 0` for every `v`
whenever `∑ h, (∑ i, I h i) / d h ≤ m η` and some `i` has `∑ h, J h i / d h` outside
`(m/(n+1) − 2 m η, m/(n+1) + 2 n m η)`. Route: `ArithmeticHeights` 5.7 with the third estimate
of 2.5. With coefficients in `K` the book's `r = [F : K]` is `1` and its relative Siegel lemma is
the absolute one.

**5.3 The index along linear forms and the generalized Roth lemma** (Bombieri–Gubler, Definition
7.5.17, 7.5.18, Lemma 7.5.19). For nonzero linear forms `M h` in the `h`-th block, the ideal
`I(t; d; M)` generated by the monomials `∏ h, (M h (X h)) ^ (j h)` with `∑ h, j h / d h ≥ t`, and
`ind(P; d; M) = sup {t | P ∈ I(t; d; M)}`, with the valuation properties of 2.3 and agreement
with 2.3 for `n = 1`, `M h = X h 1 − α h X h 0`. Then: if `P` is multihomogeneous and nonzero of
multidegree at most `d`, `0 < σ ≤ 1/2`, `d (h+1)/d h ≤ σ`, and
`n σ⁻¹ (h(P) + 4 m d 0) ≤ d h · h(M h)` for all `h`, then
`ind(P; d; M) ≤ 2 m σ ^ ((1/2)^(m−1))`. By specializing all but two variables of each block to
`0` without killing `P`, losing at most the factor `n` in `h(M h)`, and applying 2.7.

**5.4 The height of `V(Q)` and the exceptional subspaces** (Bombieri–Gubler, Lemma 7.5.21). For
the domains of 4.1 with `c` of weight at most `−ε/2` there are a **finite set** `𝒲` of
`n`-dimensional subspaces of `Kⁿ⁺¹`, depending only on the forms, and constants `C₄`, `C₅`,
`C₆` depending only on `K`, `S₀`, the forms and `c` and **not on `Q`**, such that for every `Q`
with `log Q ≥ C₄ ε⁻¹` and rank `n`, either `V(Q) ∈ 𝒲` or
`(4 |S|)⁻¹ ε log Q − C₅ ≤ h(V(Q)) ≤ n c_max |S| log Q + C₆`, where `h(V(Q))` is the height of a
subspace of `ArithmeticHeights` 3.2 — equivalently, by its duality theorem 3.5, the height of a
linear form cutting out `V(Q)`. The displayed constants are the book's, in its absolute
normalization; in Mathlib's they change by factors of `d`, and what Layer 5.6 uses is that the
lower bound is a positive multiple of `ε log Q` and that nothing depends on `Q`. Route: the upper bound is Hadamard's inequality
for `y 1 ∧ ⋯ ∧ y n`; the lower bound is 0.4 applied to a nonvanishing
`L̂ v k ((y 1 ∧ ⋯ ∧ y n)^*)`, which Laplace's identity (4.5) expresses as a determinant of the
small numbers `L v i (y j)`; when no admissible choice of nonvanishing `L̂ v (i v)` exists, the
vector `(y 1 ∧ ⋯ ∧ y n)^*` is annihilated by the forms `L̂ v i` with `i` outside certain sets
`I v`, and `V(Q)` is then the kernel of a solution `w` of that system fixed in advance. ⚠ The
book says "a linear space `W`"; its proof fixes one `w` for each pattern `(I v)_v`, and the
pattern can change with `Q`, so the true statement has one exceptional subspace **per pattern** —
finitely many, all determined by the forms. A formal statement with a single `W` is not what the
proof gives. ⚠ Without the exceptional alternative the lower bound is false.

**5.5 Non-vanishing at a small point** (Bombieri–Gubler, Lemmas 7.5.24 and 7.5.25). *The grid
lemma:* a nonzero `f : MvPolynomial (Fin N) k` over a field of characteristic zero, with
`degreeOf j f ≤ e j`, and `B > 0`: there are integers `z j` with `|z j| ≤ B` and orders
`i j ≤ e j / B` with `(hasseDeriv i f)(z) ≠ 0`. *The small point:* if `hasseDeriv I P` does not
vanish identically on `V(Q 1) × ⋯ × V(Q m)`, each of rank `n` with a basis `y h l` in the domain
of level `Q h`, then some `hasseDeriv I' P`, with the order of `I'` exceeding that of `I` by at
most `m n / B` in the weighted sense, is nonzero at a point `x h = ∑ l, z h l • y h l` with
integers `|z h l| ≤ B`; with `B = 2 n / η` this is the polynomial `T` of Lemma 7.5.25, with its
four properties (a)–(d).

**5.6 The penultimate-minimum theorem** (Bombieri–Gubler, Theorem 7.5.13, Steps IV and VI). For
forms with coefficients in `K` and `c` of negative weight, the set of subspaces
`{V(Q) | 1 ≤ Q, rank = n}` is finite. Route: otherwise, by Northcott for subspaces
(`ArithmeticHeights` 3.7) and 5.4, there are `V(Q 1), …, V(Q m)`, none in `𝒲`, with
`log Q 1` large and `log Q (h+1) ≥ 2 σ⁻¹ log Q h`; take `d h ≈ D / log Q h`, `P` from 5.2, and
the forms `M h` cutting out `V(Q h)`, whose heights 5.4 controls; 5.3 gives a derivative of small
order not vanishing on `∏ V(Q h)`, 5.5 a point `X'` of small height where a further derivative
`T` does not vanish; bound `T(X')` above at each place of `S` by the vanishing pattern of 5.2
and the inequalities defining the domains, and below by the product formula; let `D → ∞`.

### Layer 6: the Subspace Theorem (the summit)

**6.1 The parametric Subspace Theorem** (Bombieri–Gubler 7.5.30–7.5.32, Steps VIII and IX;
Evertse–Schlickewei for the formulation). For forms with coefficients in `K`, linearly
independent at each place, and exponents `c` of negative weight, there are a finite set `T` of
proper subspaces of `Kⁿ⁺¹` and `Q₀` such that for every `Q ≥ Q₀` the approximation domain
`approxDomain S₀ L c Q` is contained in a member of `T`. Route: for rank `n` this is 5.6. For
rank `R < n`, 4.5 turns an unbounded family of domains of rank `R`, along which `k` and the
exponents of the wedge domain may be taken constant up to `γ` after a further use of 3.1, into
domains in `⋀^{n+1−k}` of rank one less than the dimension and negative weight; 5.6 in that
space makes their spans finite in number, and Lemma 7.5.33 recovers from each span the span of
the first `k` minimal vectors of the original domain, which contains `V(Q)` and is proper
because `k ≤ n`. A bounded range of `Q` contributes finitely many `V(Q)` by 4.3. ⚠ The book
states its conclusion only along `Q = H(x_ν)` for a hypothetical sequence of solutions, because
it is proving 6.2 by contradiction; but 7.5.32 opens with "let `(Q_ν)` be an unbounded family"
and uses nothing else, and the statement above is what that argument proves. It is pinned as the
primary form because it is the one the quantitative theory strengthens: Layer 9 and every
quantitative Subspace Theorem in print count the members of `T`.

**6.2 The Subspace Theorem, coefficients in `K`** (Schmidt 1972 for `K = ℚ`, `S = {∞}`;
Schlickewei 1977 with finite places; Bombieri–Gubler, Theorem 7.2.2 with `F = K`). For
`[Nontrivial ι]`, forms `L v i : Module.Dual K (ι → K)` linearly independent for each `v` in
`S∞` and `S₀`, and `ε > 0`, there is a finite set `T` of proper subspaces of `Kⁿ⁺¹` containing
every `x ≠ 0` with `approxProd S∞ S₀ L x ≤ mulHeight x ^ (−(n+1) − ε)`. From 6.1 and 5.1: an
infinite place missing from `S∞` is added with the coordinate forms, whose local factor is at
most `1`, so the hypothesis survives; the solutions with some `L v i x = 0` lie in the kernels; the others, normalized, lie in finitely
many parametric families, each covered by 6.1 once `mulHeight x ≥ Q₀`; and the projective points
of height below `Q₀` are finite in number by Northcott (`ArithmeticHeights` 1.1) and lie on that
many lines, which are proper because `n ≥ 1`.

**6.3 Algebraic coefficients** (Bombieri–Gubler, Theorem 7.2.2 in full and Remark 7.2.3). The
same with `L v i : Module.Dual F (ι → F)` over a finite extension `F/K`, linearly independent
over `F`, measured by `w v` over `v`: the solutions `x ∈ Kⁿ⁺¹` lie in finitely many proper
subspaces of `Kⁿ⁺¹`. Route: by 0.1 pass to the Galois closure `F'` of `F/K`; at each place `w'`
of `F'` above `v` put the conjugate system `σ(L v)`, where `σ` carries the chosen absolute value
to `w'` (0.2); for `x ∈ Kⁿ⁺¹` the local factors at all `w'` above `v` are equal, so by the local
extension formula of 0.2 and `ArithmeticHeights` 0.3 the inequality over `F'` is the inequality
over `K` raised to the power `[F' : K]`; apply 6.2 over `F'` and intersect the subspaces with
`Kⁿ⁺¹`, where they remain proper. **This is the form consumers apply**, and both forms in print
are instances: `F = K` is 6.2, and `K = ℚ` is Schmidt's theorem for linear forms with algebraic
coefficients in integer points — the form with real algebraic coefficients at `∞`, and the form
with a `p`-adic algebraic coefficient, which Layer 7 uses. ⚠ Over `K` of degree `> 1` the two are
genuinely different statements about rational points: the height of `x ∈ ℚⁿ⁺¹` relative to `K`
is its `d`-th power, so 6.2 over `K` applied to rational points loses a factor `d` in the
exponent, and only 6.3 over `ℚ` gives the sharp statement.

**6.4 The affine form** (Bombieri–Gubler, Corollary 7.2.5 and Theorem 7.2.6). For
`S : Finset (HeightOneSpectrum (𝓞 K))`, forms as in 6.3 at every infinite place and every place
of `S`, and `ε > 0`: the `x ≠ 0` with coordinates in `S.integer K` and

```text
(∏ v : InfinitePlace K, (∏ i, w v (L v i x)) ^ v.mult) * ∏ v ∈ S, ∏ i, w v (L v i x)  ≤  mulHeight x ^ (−ε)
```

lie in finitely many proper subspaces of `Kⁿ⁺¹`. Prove the equivalence with 6.3 in both
directions (0.3). This is the form every application in Layer 8 uses.

**6.5 General position** (Vojta 1987; Bombieri–Gubler, Definition 7.2.8, Theorem 7.2.9). A family of
linear forms is in **general position** if every subfamily of at most `n + 1` of them is linearly
independent. For families `L v : κ v → Module.Dual F (ι → F)` in general position, of any finite
sizes, the conclusion of 6.3 holds for the product over all of `κ v`. By splitting the solutions
according to the order of the `w v (L v i x)` and discarding all but the `n + 1` smallest, which
by general position form a basis and bound `⨆ j, v (x j)` from below.

**6.6 Consistency with Layer 3.** For `Fintype.card ι = 2`, 6.3 is 3.4. Prove that the two
statements agree, so that the library carries one theorem on the projective line and not two.

### Layer 7: approximation of algebraic numbers, and transcendence

What the Subspace Theorem says about numbers. Every milestone is 6.3 over `K = ℚ` with an
algebraic coefficient, followed by an induction on the dimension that uses the finitely many
subspaces.

**7.1 One linear form** (Bombieri–Gubler, Theorem 7.3.2). For complex algebraic
`α 0, …, α n` and `ε > 0`, finitely many `x ∈ ℤⁿ⁺¹` satisfy
`0 < |∑ i, α i * x i| ≤ mulHeight x ^ (−n − ε)`. The hypothesis is non-vanishing, not linear
independence of the `α i` (Remark 7.3.3), and the statement should keep that shape. By induction
on `n`: 6.3 with the forms `∑ α i X i, X 1, …, X n` at `∞` puts the solutions in finitely many
rational subspaces, and on each of them one variable is eliminated.

**7.2 Approximation by algebraic numbers of bounded degree** (Schmidt; Bombieri–Gubler, Corollary
7.3.5). For complex algebraic `α`, `D ≥ 1` and `ε > 0`, finitely many algebraic `ξ` of degree at
most `D` satisfy `|α − ξ| ≤ H(f_ξ)^{−D−1−ε}`, with `f_ξ` the primitive integer minimal polynomial
and `H` its naive height. From 7.1 applied to `1, α, …, α^D` and the mean value theorem; Remark
7.3.6, `H(f_ξ) ≍ H(ξ)^{deg ξ}`, is `ArithmeticHeights` 1.2 with 2.3.

**7.3 The exponents of an algebraic number** (Schmidt 1970). For real algebraic `α` of degree
`D` and every `n ≥ 1`, `mahlerExponent n α = koksmaExponent n α = min n (D − 1)`. Upper bounds:
7.1 for `n`, and 1.3 for `D − 1`. Lower bounds: 1.3 for `mahlerExponent` when `n < D`, Wirsing's
third inequality of 1.3 for `koksmaExponent` when `n < D` — at `w = n` it reads `n ≤ w_n^*`, and
it is **landed**, so this half of 7.3 is available now — and
monotonicity in `n` beyond. This closes what Layer 1 leaves open, and `n = 1` is Roth's theorem.
With it, **Schmidt's theorems on simultaneous approximation** (Schmidt 1970; *Diophantine
Approximation*, Ch. VI; Bombieri–Gubler, Remark 7.3.4): for real algebraic `α 1, …, α n` with
`1, α 1, …, α n` linearly independent over `ℚ` and `ε > 0`, finitely many `q ≥ 1` have
`q^{1+ε} ∏ i, ‖q α i‖ < 1`, and finitely many `q ∈ ℤⁿ` with no zero coordinate have
`(∏ i, |q i|)^{1+ε} ‖∑ i, q i α i‖ < 1`, where `‖·‖` is the distance to the nearest integer.

**7.4 The combinatorial transcendence criterion** (Adamczewski–Bugeaud–Luca 2004;
Adamczewski–Bugeaud 2007). For a finite word `V` and real `w ≥ 1`, `V^w` is `V` repeated
`⌊w⌋` times followed by the prefix of `V` of length `⌈(w − ⌊w⌋) |V|⌉`. A sequence `a : ℕ → Fin b`
is **stammering** if for some `w > 1` there are finite words `U k`, `V k` with `U k (V k)^w` a
prefix of `a`, `|U k| / |V k|` bounded, and `|V k|` strictly increasing. For `b ≥ 2`: if `a` is
stammering and not eventually periodic, then `∑ k, a k / b^(k+1)` is transcendental. Route: the
truncations `U k (V k)^∞` are rationals `p k / (b^{r k} (b^{s k} − 1))` that approximate the
number to the order the repetition gives; 6.3 over `ℚ` in **three** variables, with `S₀` the
primes dividing `b`, the forms `X, Y, α X − α Y − Z` at `∞` for the hypothetical algebraic value
`α`, and the coordinate forms at the primes of `b`, applied to the points
`(b^{r k + s k}, b^{r k}, p k)`; and an induction on the subspace that uses non-periodicity.
⚠ This genuinely needs three variables: the denominators have the special shape
`b^r (b^s − 1)`, the Subspace Theorem exploits both factors, and Ridout's theorem (3.3), which
sees only the factor `b^r`, gives the criterion only for `w > 2` (Ferenczi–Mauduit 1997). State
that weaker criterion too, as the consumer of 3.3 that needs none of Layers 4–6.

**7.5 The complexity of an algebraic irrational** (Adamczewski–Bugeaud 2007, Theorem 1). For
`a : ℕ → Fin b`, the **complexity** `p(n)` is the number of distinct words of length `n` occurring
in `a`. *The combinatorial lemma:* if `p(n) ≤ C n` for infinitely many `n`, then `a` is
stammering. *The theorem:* if `∑ k, a k / b^(k+1)` is an algebraic irrational then
`p(n) / n → ∞`. The lemma is the pigeonhole principle on the `p(n) + 1` factors of length `n` at
the first `p(n) + 1` positions and is stated for an arbitrary finite alphabet, with no reference
to a number. Prove also the two facts that make `p` an object: `p` is nondecreasing, and `a` is
eventually periodic if and only if `p` is bounded, if and only if `p(n) ≤ n` for some `n`
(Morse–Hedlund).

### Layer 8: unit equations and Diophantine equations

Throughout, `S : Finset (HeightOneSpectrum (𝓞 K))` and `S.unit K` is Mathlib's group of
`S`-units.

**8.1 The unit equation in two variables** (Siegel, Mahler, Lang). For `a, b ∈ Kˣ`, finitely many
pairs of `S`-units `(x, y)` satisfy `a x + b y = 1`. Route: enlarge `S` so that `a` and `b` are
`S`-units and absorb them; split the solutions by the coordinate of largest absolute value at
each place; on each part, with the forms `X j` for `j` not the largest and `X 1 + X 2` for the
largest, the left side of the affine inequality is *equal* to `(mulHeight x)⁻¹` by the
`S`-product formula (0.3), so 6.4 applies with `ε = 1`; the solutions lie on finitely many lines
through the origin, and each line meets `x 1 + x 2 = 1` once. ⚠ Use 6.4 **for
`Fintype.card ι = 2`**, which is 3.4 together with the affine equivalence of 6.4; that
equivalence is formal from 0.3 and is to be proved dimension by dimension so that this milestone
needs Layers 0, 2 and 3 only.

**8.2 The unit equation in `n` variables** (Evertse; van der Poorten–Schlickewei;
Bombieri–Gubler, Theorem 7.4.2 and Corollary 7.4.3). For `a : ι → Kˣ`, finitely many
`x : ι → S.unit K` satisfy `∑ i, a i * x i = 1` with **no vanishing subsum**,
`∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, a i * x i ≠ 0`. Without that condition (Corollary 7.4.3):
there is a finite `Φ ⊆ K` such that every solution has a coordinate with `a i * x i ∈ Φ`. And for
a finitely generated subgroup `Γ ≤ Kˣ`, the same two statements with `x i ∈ Γ`, since a finitely
generated subgroup of `Kˣ` lies in `S.unit K` for a finite `S`. By induction on the number of
variables, 6.4 with `ε = 1` at each step, as in 8.1; the induction enlarges `S` to turn the
coefficients of a relation into units.

**8.3 Triangularly connected decomposable forms** (Győry–Papp; Evertse–Győry, *Unit Equations in
Diophantine Number Theory*, Ch. 9). Let `𝓛` be a finite set of pairwise non-proportional linear
forms in `Module.Dual K (ι → K)` with common kernel `0`, and join `l, l' ∈ 𝓛` when some
`l'' ∈ 𝓛` equals `λ l + λ' l'` with `λ λ' ≠ 0`. If that graph is connected, then for every
product `G = c ∏ l ∈ 𝓛, l ^ e l` with `c ≠ 0` and `e l ≥ 1`, the set of `x` with coordinates in
`S.integer K` and `G x ∈ S.unit K` is finite modulo scaling by `S`-units, and for every `m ≠ 0`
the equation `G x = m` has finitely many solutions in `S.integer K`. Route: enlarge `S` so that
`c` and the coefficients are `S`-integral and `c` a unit; then every `l x` is an `S`-unit, each
edge is an instance of 8.1 for the pair `(l x / l'' x, l' x / l'' x)`, connectivity makes every
ratio `l x / l' x` range over a finite set, and the rank condition recovers `x` up to a scalar.
Forms whose linear factors are defined over a finite extension of `K` are included by passing to
that extension with the places above `S`. ⚠ This needs 8.1 and not 8.2.

**8.4 Thue and Thue–Mahler** (Thue 1909; Mahler 1933; Bombieri–Gubler 5.3.1–5.3.2, Siegel's
reduction). For a binary form `G` over `K` with at least three pairwise non-proportional linear
factors over an algebraic closure: finitely many solutions of `G(x, y) ∈ S.unit K` in
`S.integer K` modulo `S`-units; finitely many solutions of `G(x, y) = m`; and, over `ℚ`, finitely
many coprime integer solutions of `G(x, y) = ± p 1 ^ z 1 ⋯ p s ^ z s` in `x, y, z 1, …, z s`.
This is 8.3 for two variables, where three pairwise non-proportional forms are always dependent
with nonzero coefficients. The examples `x² − 2 y² = 1` and `x y = 1` over `ℤ[1/2]` show that
"three" cannot be lowered.

**8.5 The hyperelliptic equation** (Siegel 1926; Bombieri–Gubler, Theorem 5.3.5). For
`f ∈ (S.integer K)[X]` of degree at least `3` without multiple roots and `b ≠ 0`, finitely many
`(x, y)` in `S.integer K` satisfy `b y² = f(x)`. Route, as in the book: adjoin three roots of
`f`, enlarge `S` until the discriminant is a unit and the ring of `S`-integers principal (0.3),
so that each `x − α i` is a square times one of finitely many unit representatives; over the
extension generated by the square roots of those representatives the differences
`α j − α i` factor into units, and Siegel's identity among the three differences is a unit
equation (8.1). Qualitative only; the book's
count rests on the Beukers–Schlickewei bound, which is not built here.

**8.6 Norm-form equations** (Schmidt 1971–1972; Bombieri–Gubler 7.4.4–7.4.6). For a finitely
generated `ℤ`-submodule `M` of `K` and `c ∈ ℚˣ`, the solution set of `N_{K/ℚ}(μ) = c`, `μ ∈ M`,
is a finite union of **families**: sets `μ₀ • U` where `M'` is a full module in a subfield
`K' ⊆ K` with `α M' ⊆ M` for some `α ∈ Kˣ`, `μ₀ ∈ α M'` is a solution, and `U` is the group of
units of the order of `M'` of norm `1` over `ℚ`. (When `[K : K']` is even the units of norm `−1`
also preserve the equation; the book counts the two cosets as two families, and so does this
statement.) Consequently: if no such `K'` other than `ℚ` and the
imaginary quadratic fields occurs — `M` is **non-degenerate** — the equation has finitely many
solutions. Owned with it: full modules and their orders, the unit theorem for an order (finite
index in `(𝓞 K)ˣ`), and the finiteness of the solutions of a full module modulo units. From
Corollary 7.4.3 (8.2) applied to a linear relation among the conjugates of `μ`, by induction on
`[K : ℚ]`.

**8.7 The Corvaja–Zannier gcd bound** (Corvaja–Zannier; Bombieri–Gubler, Theorem 7.4.10 and
Corollary 7.4.11). For a finite set of primes and `ε > 0`, the pairs `(u, v)` of integers whose
prime factors lie in the set and with `gcd (u − 1) (v − 1) ≥ (max |u| |v|)^ε` lie in the union of
a finite set and finitely many sets `{u^a * v^b = 1}` with `(a, b) ≠ (0, 0)` in `ℤ²`; in
particular only finitely many of them are multiplicatively independent. Corollary: the greatest prime factor of `(a b + 1)(a c + 1)` tends
to infinity with `a`, for `a > b > c ≥ 1`. The acceptance test for 6.4 over `ℚ` with a number of
variables that grows with `1/ε`.

### Layer 9: counting subspaces

The elementary half of the quantitative Subspace Theorem (Evertse, "On the Quantitative Subspace
Theorem", §§2–4). It needs Layer 0, Hadamard's inequality and the product formula, and **nothing
from Layers 2–6**: it bounds how many subspaces the solutions in a range of heights can need,
whether or not one knows the solutions are there. Write `N = Fintype.card ι`. Heights in this
layer are **affine** (`ArithmeticHeights` 0.5), as in the source.

**9.1 Systems of inequalities.** For `S`, forms as in 6.4, constants `C v > 0` and exponents
`c v i`, the system `w v (L v i x) ≤ C v * H(x) ^ c v i` for all `v`, `i`, in `x` with
`S`-integral coordinates. Its **normalization**, Evertse's (2.4): the coefficients have height at
most `H` and degree at most `D` over `K`, the forms `L v i` range over a set of at most `R` forms
in all, `∏ v, C v ≤ ∏ v, (v (det (L v))) ^ (1/N)`, `∑ v, ∑ i, c v i ≤ −δ` with `0 < δ ≤ 1`, and
`max i, c v i` equal to the normalized local degree of `v` at the infinite places and `0` at the
finite ones, all in the absolute normalization. The equivalence with 6.4 — every solution of the
product inequality satisfies one of finitely many systems, and conversely — is 5.1 read as a
statement; prove it as one. A solution is **large** if `H(x) ≥ max (2 H) (N ^ (2 N / δ))`.

**9.2 The gap principle** (Evertse, Proposition 4.1). Under the normalization of 9.1 and for
`Q ≥ N ^ (2 N / δ)`, the solutions with `Q ≤ H(x) < Q ^ (1 + δ / (2 N))` lie in a **single**
proper subspace. By Hadamard's inequality at the infinite places, the ultrametric inequality at
the finite ones, and the product formula for `det (x 1, …, x N)`: any `N` such solutions are
linearly dependent.

**9.3 Small solutions** (Evertse, Theorem 2.2, Proposition 4.2, Lemmas 4.3–4.5). The solutions
that are not large lie in at most `δ⁻¹ ((10³ N)^{N d} + 4 N log log (4 H))` proper subspaces, and
over `ℚ` in at most `δ⁻¹ (10^{3 N} + 4 N log log (4 H))`. From 9.2 for heights above
`N ^ (2 N / δ)` and from the second gap principle below it: a partition of `ℂ^N` into at most
`(20 N)^N M²` classes on each of which `|det (y 1, …, y N)| ≤ M⁻¹ ∏ ‖y i‖`.

**9.4 From intervals to subspaces** (Evertse, proof of Theorem 2.1). If the solutions of a
normalized system outside a subspace `U₀` have `H(x) ∈ ⋃_{i < m} [Q i, (Q i)^ω)` with
`Q i ≥ N ^ (2 N / δ)`, then they lie in at most `m (1 + log ω / log (1 + δ / (2 N)))` proper
subspaces. This is 9.2 and a covering of intervals; it is the step that turns an *interval
result* — the form in which every quantitative Roth or Subspace theorem is actually proved —
into a count, and it is stated with the interval hypothesis explicit so that whichever interval
result is available can be fed to it. In this roadmap that is 3.7, recast in this form for
`N = 2`.

## Relationship to Mathlib

Mathlib's two directories on the subject are the floor this roadmap stands on, and neither is
restated: Layer 1 defines its exponent *through* `LiouvilleWith` and takes its lower bound from
`Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational`.

Several milestones are not about Diophantine approximation at all and are written in Mathlib's
namespaces and style because that is what they are: the classification of absolute values over a
place (0.1), which is the fragment of Ostrowski's theorem over a number field that Mathlib's
`NumberTheory/Ostrowski.lean` proves over `ℚ`; `MvPolynomial.hasseDeriv` (2.1), the multivariate
companion of `Polynomial.hasseDeriv`; the `n`-polynomial Wronskian and its independence criterion
(2.4), of which `Polynomial.wronskian` is the case `n = 2`; the index (2.3), which for one
variable is `rootMultiplicity`; the probability estimates of 2.5; the complexity function of a
sequence and the Morse–Hedlund theorem (7.5); and the irrationality exponent (1.1), which
belongs beside `LiouvilleWith`. **Before building any of these, search the open Mathlib pull
requests and the Lean Zulip for it** — Ostrowski over number fields, an irrationality measure,
multivariate Hasse derivatives — and adopt the names and shapes found there; then build it here
regardless of whether that work has landed, so that adopting Mathlib's version is a deletion plus
an import. One Lean development outside Mathlib defines an irrationality measure,
`frenzymath/PiIrrationalityMeasure` (Apache-2.0), as a real-valued `sInf`; the conventions table
says why this roadmap's is `ℝ≥0∞`-valued instead. A search found no Lean development of Thue's,
Roth's or Schmidt's theorem, or of a unit equation.

Follow Mathlib's shape throughout: `ℝ≥0∞`-valued invariants defined as an `iSup` over `ℝ≥0`, as
`dimH` is; typed places (`InfinitePlace`, `FinitePlace`) rather than raw absolute values;
`AbsoluteValue.LiesOver` for extensions; `Set.integer` and `Set.unit` for `S`-integers and
`S`-units; and heights through `Height.mulHeight` and the `Northcott` class, never through a
private normalization.

## Worked examples (acceptance criteria, keeping the definitions honest)

Each is a cheap check that a definition or a hypothesis means what it should; they belong in the
Tau Ceti test files beside the milestones named.

- **1.1** — **landed**, as the acceptance criteria of `…/IrrationalityExponent.lean` and
  `…/LiouvilleExponent.lean`. `irrationalityExponent (q : ℝ) = 1` for `q : ℚ`; `= ⊤` at Mathlib's
  Liouville constant; `irrationalityExponent (√2) = 2` from Layer 1 alone, since Liouville's bound
  for degree `2` meets Dirichlet's — pinning the degree of `√2` at `2` is
  `minpoly.two_le_natDegree_iff` against `irrational_sqrt_two`, and it is the only place in the
  layer where a minimal polynomial is computed. Two rejection tests were added that this list did
  not ask for: that `Irrational ξ` is needed for the lower bound `2`, and that the determinant
  hypothesis of the Möbius invariance is load-bearing. ⚠ `irrationalityExponent (2 ^ (1/3 : ℝ))`
  was **not** done: Layer 1 gives `[2, 3]` and the value `2` needs 3.3.
- **1.2.** `koksmaExponent 1 ξ = mahlerExponent 1 ξ` and `mahlerExponent 1 ξ + 1 =
  irrationalityExponent ξ` for every real `ξ`; `mahlerExponent 1 q = 0` at a rational and
  `1 ≤ mahlerExponent 1 (√2)` — **landed**, together with the Möbius invariance of both exponents
  and Gelfond's inequality over `ℤ`. ⚠ The rejection tests that this list did not ask for are the
  ones that pin the *normalization*: `mahlerExponent 1` is not the irrationality exponent, and
  the constant `2^{deg}` in Gelfond's inequality cannot be dropped.
- **1.3, 7.3.** `mahlerExponent n (√2) = 1` for all `n ≥ 1` from Layer 1 alone;
  `mahlerExponent n (2 ^ (1/3 : ℝ)) = min n 2` only after 7.1. ⚠ Neither is yet available: the
  landed half of 1.3 gives `mahlerExponent n (√2) ≤ 1` at once, from `d = 2`, and the matching
  lower bound `1 ≤ mahlerExponent n (√2)` is **not** the box principle — that one needs `ξ` not
  algebraic of degree at most `n`, which `√2` is — but monotonicity in `n` from the degree-one
  value of 1.2. Layer 1 alone therefore does settle `√2`, and the landed acceptance test one
  degree lower is `mahlerExponent n q = 0` at every rational and every `n`.
- **2.1.** The defining equation on a monomial, the composition law, the Leibniz rule, the
  Taylor expansion and the two local estimates are checked against the library — **landed**. ⚠ The
  rejection test the list did not ask for is the one that says why the milestone exists at all:
  over `ZMod 2`, `∂_(single j 2) (X j ^ 2) = 1` while `pderiv j (X j ^ 2) = 0`, so the index of
  2.3 is `2` and not `⊤`. With `pderiv` in place of the Hasse derivative, Layer 2.3 is false in
  characteristic `p`.
- **2.2.** The coefficient identity, the local identity at an arbitrary absolute value and
  Proposition 1.6.2 itself are checked against the library — **landed** — together with a
  numerical instance over `ℚ`: `(x + 2)(y + 3)` in two disjoint variables has height `6`, which
  is `2 · 3` on the nose, where the same product in one variable is allowed a factor
  `2 ^ (deg p + deg q)` by Gelfond. ⚠ Two rejection tests the list did not ask for: that the
  nonvanishing hypotheses are not decoration — at `f = 0` the two sides are `1` and `2` — and
  that the variables must be disjoint, since `(x + 1)^2` has middle coefficient `2` where each
  factor has coefficient `1`, so a coefficient of a product in *one* variable is a sum over the
  antidiagonal and not a single product.
- **2.3.** `index d (α, α) ((X 0 − X 1) ^ k) = k / max (d 0) (d 1)`: the index sees the weights,
  and a polynomial vanishing on the diagonal has small index when the weights are unbalanced —
  which is why Roth's lemma needs `d (j+1) / d j ≤ σ`. Checked against the library — **landed**,
  for every `k` at once, through multiplicativity rather than a binomial expansion: the index of
  the `k`-th power is `k` times the index, and the index of `X 0 − X 1` is the smaller of the two
  weights. ⚠ Two rejection tests the list did not ask for: over `ZMod 2` the square of a variable
  has index `2` at the origin while its `pderiv` is the zero polynomial, so a `pderiv`-based
  index would call it `⊤` and every valuation property above would be false — this is what Layer
  2.1 was for; and over `ZMod 4` the square of `2 X` is `0`, whose index is `⊤`, while the two
  indices add up to `2`, so the hypothesis on the ring is not decoration either.
- **2.4.** `1, X, Y` have the nonzero generalized Wronskian `det (id, ∂_X, ∂_Y) = 1`; every
  generalized Wronskian of `X, Y, X + Y` vanishes; and over `ZMod p` every Wronskian of `1, t^p`
  vanishes although they are independent — all three **landed**, the third at `p = 2` and in both
  the several-variable and the one-variable form, where `1` and `t²` are independent over
  `ZMod 2` while `det (id, d/dt)` and its Hasse normalisation both vanish. ⚠ The second is not a
  computation: it is the easy half applied to a dependent family, and it therefore holds at every
  family of orders at once rather than at the ones a computation would fix. ⚠ One test this list
  did not ask for was added, and it is the one that pins the normalisation: the `n = 2` case of
  the determinant is Mathlib's `Polynomial.wronskian` on the nose, and `1, t, t²` over `ℚ` have
  Wronskian `2` — the factorial that separates the two normalisations.
- **2.5.** This list asked for nothing, so the file fixes its own: `V_m(t) = 1` once `t` reaches
  `m` and `V_m(t) = 0` for `t < 0`, the two ends of the region; `V_1(t) = min 1 t`, which is what
  pins the normalization — in one variable the volume is a *length*, so `V_1(t) = t` on `[0,1]`;
  and that the density of the multihomogeneous estimate integrates to `1`, without which the
  third estimate would not be about a proportion. ⚠ The one that earns its place is a **rejection
  test**: the upper lattice-point bound is false at `t = 0`, where the origin is an admissible
  lattice point and the region has no volume, so the book's `t ∈ ℝ_+` is load-bearing — unlike
  its `ε ≤ 1/2`, `λ ≤ n + 4` and `η ≤ 2/(n+1)`, all three of which came out. All **landed**.
- **2.6.** This list asked for nothing here either, so the files fix their own — all **landed**.
  That the box has `∏ j, (d j + 1)` monomials, which is what makes the coefficient count of
  Lemma 6.3.4 a product and not a binomial coefficient; that the condition of order `0` is
  evaluation at the point, so that the first row of the system is "`P` vanishes at `α`"; that an
  order leaving the box carries no condition; and that the tuple of powers `α ^ k, k ≤ d`, has
  height `H(α) ^ d` exactly. ⚠ The two that earn their place are **rejection tests**: with no
  variables the feasibility hypothesis `r ∑ k, V₀(t k) < 1` forces `N = 0`, because a nonzero
  constant has index `0` at every point; and `r S < 1` does **not** imply `r (1+ε) S < 1`, which
  is why the choice of `ε` has to precede the choice of `D₀` and not follow it. ⚠ A third pins
  the hypothesis of `MvPolynomial.hasseDeriv_eq_zero_of_lt`: at `μ j = degreeOf j P` the
  derivative survives, `∂_(X 0) (X 0) = 1`, so the inequality there is strict for a reason.
- **2.7.** This list asked for nothing here either, and the milestone's own are the two ends of
  the exponent and two rejection tests — all **landed**. In one variable the conclusion is
  `index ≤ 2 σ`, linear in `σ`, and the lemma is Lemma 6.3.9 at a worse constant; in two it is
  `index ≤ 4 √σ`, which is the case that fixes the shape of the induction, since the quadratic
  lower bound on the index of the determinant is what turns `σ` into `√σ` and every further
  variable squares the exponent again. ⚠ The two that earn their place are **rejection tests**:
  the closing inequality of the induction is *false* without `θ < 1/2` — at `θ = 1` every other
  hypothesis holds and there is no contradiction, so the reduction that makes the constant
  uniform is load-bearing — and the `min` in the quadratic lower bound is not decoration, since
  at `p = 3`, `e = 2`, `x = 1/2` the sum is `1/2`, *less* than the linear half `p x / 2 = 3/4`,
  while the quadratic half `p x² / 4 = 3/16` survives. ⚠ Layer 2.3's own acceptance test is the
  third: `index d (α, α) ((X 0 − X 1)^k) = k / max (d 0) (d 1)` says that a polynomial vanishing
  on the diagonal has large index when the weights are *balanced*, which is exactly what the
  hypothesis `d (j+1) / d j ≤ σ` forbids.
- **Conventions.** The refutation of the untyped Subspace statement, as a theorem: over `ℚ`, with
  the four absolute values `|·|^{1/j}`, `j = 1, …, 4`, the coordinate forms on `ℚ²` and
  `ε = 1/12`, every `(1, q)` with `q ≥ 1` satisfies the inequality and no finite set of proper
  subspaces of `ℚ²` contains them all. And the failure at `Fintype.card ι = 1`.
- **3.1.** The count is checked against a hand enumeration at `N = 0`, where there is exactly one
  class and the formula gives `(0 + |A|).choose |A| = 1`. ⚠ The two that earn their place are a
  **rejection test** and a **sharpness test**: the classes are the cells of the *simplex* and not
  of the cube, and the constant family `y a = 1` — every coordinate in `[0, 1]` — has a label
  summing to `2` at `N = 1`, so without `∑ a, y a ≤ 1` the count would be `(N + 1)^{|A|}`, four
  against three at `N = 1`, `|A| = 2`; and the upper half of (6.9) is **attained**, at the
  one-coordinate family `f = 1/4` with `N = 2`, so its exponent is not off by one. The
  load-bearing hypothesis of the second half is `X.Infinite`: in `{0, 1} ⊆ ℚ` every element has
  height `1` and no sequence is `(1, 2)`-independent.
- **3.2.** The set the theorem bounds is nonempty for every `κ` — the target `0` at every place
  has `β = 0` as a solution, so the finiteness is not finiteness of the empty set — and the
  classical one-place shape is an instance of the milestone. Both **landed**. ⚠ The one this list
  asked for first, that **Roth's theorem is false with `κ = 2`**, was **not** done, and the
  reason is a boundary and not a difficulty: the witness is Dirichlet's theorem at an algebraic
  irrational, so it needs a second number field with a chosen real place and the dictionary
  between `Real.irrationalityExponent` and the product over the places of `ℚ` — which is
  precisely **Layer 3.3**, whose whole content is that dictionary. What is landed instead is a
  **rejection test** that costs no places: at `κ = 0` the right-hand side is `1`, the truncated
  product is always at most `1`, and *every* element of `K` is a solution, so the hypothesis on
  `κ` is load-bearing. ⚠ The third item on this list, about two targets at one place, is not a
  statement of this milestone at all — Roth's theorem carries one target per place — and is left
  to 3.3, where targets at `∞` make the question concrete.
- **3.5.** `‖(3/2)^k‖ > exp (−k/10)` for all but finitely many `k`, with no value of the
  exceptional set asserted.
- **6.3.** Schmidt's example that the conclusion cannot be finiteness of points: with
  `L 1 = X 1 + √2 X 2 + √3 X 3`, `L 2 = X 1 − √2 X 2 + √3 X 3`, `L 3 = X 1 − √2 X 2 − √3 X 3` at
  `∞`, every solution of `x 1 ² − 2 x 2 ² = 1`, `x 3 = 0` satisfies
  `|L 1 x · L 2 x · L 3 x| = (x 1 + √2 x 2)⁻¹ ≤ ‖x‖^{−ε}` for `ε ≤ 1`: infinitely many solutions,
  all in the plane `x 3 = 0`.
- **8.1, 8.2.** `(2, −1), (3, −2), (4, −3), (9, −8)` solve `x + y = 1` in `{2, 3}`-units of `ℚ`
  and the solution set is finite; the completeness of any list is not asked for. And
  `(u, −u, 1)` solves `x 1 + x 2 + x 3 = 1` for every unit `u`: the no-vanishing-subsum
  hypothesis is not removable.
- **8.4.** `x³ − 2 y³ = 1` has finitely many integer solutions; `x² − 2 y² = 1` has infinitely
  many, and has two linear factors.
- **7.5.** The characteristic sequence of the powers of `2` has `p(n) ≤ 3 n + 1` — a window of
  length `n` starting beyond `2 n` contains at most one `1` — so `∑ k, 2^{−2^k}` is
  transcendental by 7.5.

## Ordering

Four groups of milestones depend on nothing else in this roadmap and little in
`ArithmeticHeights`, and can be claimed at once: **Layer 1** (Mathlib, plus `ArithmeticHeights`
2.3 for one lemma of 1.2 and 0.4 below for the Liouville bounds); **0.1–0.4**, which are algebraic
number theory; **2.1–2.5**, which are algebra and one exponential-moment estimate, with no height
in sight except the last sentence of 2.1; and **Layer 9** with the combinatorial half of **7.5**.

⚠ **0.1 and 0.2 are landed** (six files, 61 declarations, no axioms beyond the allowlist). 0.1
was the cheapest of the four groups, not the dearest: the nonarchimedean half is Mathlib's
`isEquiv_of_lt_one_imp` plus one decomposition, and the archimedean half is Mathlib's
Gelfand–Mazur plus one lemma about `ℂ`. The expensive part was not mathematics but the three
pieces of general absolute-value infrastructure Mathlib turns out to lack; they are now in
`DiophantineApproximation/Nonarchimedean.lean` and 0.3 can use them. 0.2 was cheaper again, and
for a reason worth repeating: **its infinite half is entirely Mathlib's** — ramification theory
for infinite places is in the library, complete with a local degree and its sum — while its
finite half is vocabulary Mathlib has never written down for finite places. Neither half needed
any equivariance lemma. 0.3 is bookkeeping against `ArithmeticHeights` 6.4–6.5.

⚠ **0.3 and 0.4 are landed as well, and the whole of Layer 0 with them** (ten files). The
prediction that 0.4 "costs real work, because it is an inequality with an explicit constant and
nothing in Mathlib produces those" was **wrong on both counts**: the constant is Mathlib's, in
`Height.mulHeight₁_sub_le`, and the mathematics is one identity —
`min 1 t * max t 1 = t` turns the product formula into `(mulHeight₁ α)⁻¹` — read twice. What 0.4
cost was the bookkeeping that locates the chosen absolute value above `v` inside the places of
`F`, and the derivation of Mathlib's `Liouville.exists_pos_real_of_irrational_root`, which is
more rational-number arithmetic than Diophantine approximation. **0.3 was the dearest of the four
after all**, because Proposition 5.3.6 needs a ring structure on `S.integer K` that Mathlib does
not provide.

⚠ **1.1 is landed** (two files), and it confirmed the claim this section makes about Layer 1:
it uses *nothing* from this roadmap except 0.4, and 0.4 only for its last clause — which is
exactly why the milestone splits into an elementary file and an algebraic one, the first
importing no number field at all. What Mathlib turned out not to have is smaller than the group's
description suggests but is not empty: Dirichlet's theorem in `LiouvilleWith`'s shape (the gap is
the *denominator*, not the approximation) and `LiouvilleWith.inv`, without which the Möbius
invariance cannot be assembled from the affine API. ⚠ **1.2 is landed too** (four files), and it
is the first milestone of this roadmap to consume `ArithmeticHeights` for a reason other than
heights of number-field elements: Gelfond's inequality, 2.3, in its integer form. It enters
**twice** — once for the optional restriction of `w_n` to irreducible polynomials, and once,
unavoidably, for the Möbius invariance of `w_n^*`, where the minimal polynomial of a transformed
approximant has to be extracted as a factor of the transform. Layer 1 therefore does consume that
roadmap, one milestone earlier than this section predicted, and the Roth machinery is still
untouched. ⚠ **1.3 is landed except for Wirsing's first two inequalities** (eight more files). The
box principle, not Minkowski's linear forms theorem, is what it needed — twice: once at `ξ`
alone for `n ≤ w_n`, and once at `n` points at a time for Wirsing's third inequality, where it
replaces Minkowski at the cost of a constant. It needed nothing from `ArithmeticHeights`; the two
imports that grew are Mathlib's, because `w_n ≤ d − 1` is the first statement of this roadmap
whose *proof* opens a number field of its own, `ℚ⟮ξ⟯`, and because Wirsing's third inequality is
the first to use Mathlib's **Mahler measure** — `mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm`
and `supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure` are what make `H(P)` and `|lc(P)|`
comparable once the roots are known to be bounded. **Wirsing's first two bounds and 1.4 are
untouched, and both are optional** — nothing in Layers 2–9 consumes either, so the layer may be
treated as closed. They are where root separation — a discriminant estimate — enters; Mathlib
has `Polynomial.discr` and `Polynomial.resultant_deriv` but not `disc P = lc(P)^{2d−2}
∏_{i<j}(α_i − α_j)²`, and supplying that product formula is the concrete next step for the
**first** inequality. It is on no critical path: the only milestone that waits on Wirsing is the
optional 1.4, and 1.4 needs only the **second**, `w_n + 1 ≤ 2 w_n^*`, which that formula does not
supply. **The next step that is not optional is Layer 2**, which nothing in Layer 1 blocks.

⚠ **2.1 is landed** (three files), and it confirms this section's claim that Layers 2.1–2.5 need
nothing from anywhere: only its last file knows what an absolute value is, and even that one uses
`ArithmeticHeights` for a single lemma about the local factor of a `Finsupp`. What the milestone
actually cost was not the algebra but finding the *order* of it: the Leibniz rule is unreachable
by induction on `μ`, because the composition law would have to be divided by `ν j + 1`, so the
substitution formula `coeff μ (P (C X + X)) = ∂_μ P` has to come first — and it, in turn, reduces
to Pascal's rule. Everything else in 2.1 is a computation with coefficients.

⚠ **2.2 is landed** (one file), and it confirms the prediction that it would be
`ArithmeticHeights` work rather than Roth work — but not in the way the prediction meant it. The
milestone is not a height computation at all: it is one identity about coefficients, over a
commutative semiring, and after it the height statement is an instance of Mathlib's Segre
relation with `ArithmeticHeights` 2.1's reindexing lemma between them. Nothing had to be proved
about absolute values, and nothing about number fields. What the milestone did *not* need is
worth recording beside 2.1, which needed the opposite: **no ultrametric hypothesis anywhere**,
where Gauss's lemma cannot do without one.

⚠ **2.3 is landed** (two files), and it is where 2.1's insistence on Hasse derivatives rather
than `pderiv` pays: multiplicativity of the index is the statement that the lowest
weighted-degree part of a Taylor expansion is multiplicative, and with `pderiv` the definition
itself is wrong in characteristic `p` — the rejection test is `X²` over `ZMod 2`, whose index at
the origin is `2` and whose `pderiv` is zero. What the milestone cost, again, was finding the
*order*: translating the point to the origin first, after which the index is the weighted order
of a support and every valuation property is proved without a derivative or a point in sight.
⚠ **2.4 is landed** (two files), and the milestone's own prediction was right for the wrong
reason: it does need a univariate criterion Mathlib does not have, but that criterion, not the
several-variable statement, is where the work is. The reduction to one variable costs a Kronecker
substitution and a chain rule that is Layer 2.1's Taylor formula read once more — and it hands
back the order bound `|μ i| ≤ i` for free, because the translated substitution has zero constant
term. The univariate criterion is proved by *leading coefficients*: all terms of the Leibniz
expansion sit in one degree, so the top coefficient is a binomial determinant, and that is
nonzero because a polynomial with `n` terms cannot vanish to order `n` at `1`. Characteristic
zero is used exactly there and in the factorial between the two normalisations; the easy half
needs neither it nor any property of the derivative.
⚠ **2.5 is landed** (one file, and the first milestone since 2.2 to need only the one it asked
for), and what it taught is that the three estimates are *one*: a Chernoff bound in `m`
coordinates, applied at two weights. The book's own restrictions on the parameters — `ε ≤ 1/2`,
`0 < λ ≤ n + 4`, `η ≤ 2/(n+1)` — are artefacts of its alternating-series argument and all three
came out; what is load-bearing, and what the rejection test pins, is `t > 0` in the upper
lattice-point bound. The one thing the layer could not state as the book does is the
multihomogeneous *volume*, because the book's reduction of it to a one-variable integral is the
volume of a simplex and Mathlib has none; against the normalised density the estimate is the
proportion the milestone asked for, with the `(n!)^{−m}` cancelled.
⚠ **2.6 is landed** (four files, and the first milestone of Layer 2 with a height in it), and
what it taught is that the milestone's own route was one layer off: the relative Siegel lemma it
needs is `ArithmeticHeights` **5.6**, applied on the box of bounded partial degrees, and 5.7 —
the same lemma on the simplex of bounded total degree — is a sibling rather than an ancestor.
What the construction costs beyond the count of conditions is three quantities of three different
orders, all `o(∑ j, d j)`, and that is the whole of the book's `o(1)`; the `log 2` in the bound
is the binomial coefficient of the Hasse derivative and nothing else, because the height of a
condition row is a product of one-variable heights **exactly**.
⚠ **2.7 is landed** (eight files, and the largest milestone of this roadmap so far), and what
it taught is that the induction is not on `σ`: parameterising by `θ` with `σ = θ^(2^m)` leaves
`σ` fixed through every recursive call, so no real power occurs inside the proof and the book's
exponent is one change of variable at the end. The constant `2 m` is uniform because
`index ≤ (number of variables)` makes the conclusion free at `θ ≥ 1/2`; the independence of both
families of the decomposition follows from choosing the first to be a basis rather than from
minimality; and the height of the determinant has to be estimated place by place, because the
projective height of a *sum* of polynomials is not bounded by those of the summands.
**Layer 2 is complete.**

⚠ **3.1 is landed** (two files, the first milestone of Layer 3 and the shortest of this
roadmap since 2.2), and what it
taught is that the milestone's own abstraction is the load-bearing decision: nothing in Mahler's
reduction is about places, heights or number fields, so the count and the pigeonhole are stated
for an arbitrary finite index type — over a number field it is the disjoint union of the two
typed finsets, not a set of places — and the only arithmetic in the layer is Northcott's theorem
in the second half. The count is an *equality* and a stars-and-bars bijection, and the statement
the consumers will actually quote is the book's (6.9), which the milestone did not name.

⚠ **3.2 is landed, and Roth's theorem is proved** (seven files, the second largest milestone of
this roadmap after 2.7), and what it taught is that this section's own prediction — "3.2 is
bookkeeping around 2.6, 2.7 and 3.1" — was right about the *inputs* and wrong about the *route*:
the one step the roadmap had put in the wrong place is Step IV, which needs the product formula
over all the places and not the fundamental inequality of 0.4 over `S` (see 3.2 above), and
getting it wrong would have proved the theorem only for `κ > 4`. What the milestone also cost, and
this section did not predict, is the parameter order: `ε` and `N` from `κ`, the number of
variables from the feasibility of the index theorem, `σ` from the number of variables, `L` and `M`
from `σ` and from the constants of the data, the solutions from `L` and `M`, and `D` last — seven
choices, each depending on all the earlier ones, and the book states them in exactly that order
for exactly that reason. Against that, the book's `D → ∞` cost nothing: every error term but one
is `O(D/L)`, and the one that is not is a logarithm.

The path to Roth's theorem was 0.1 → 2.6 → 2.7 → 3.1 → 3.2, with 2.1–2.5 feeding 2.6 and
2.7, and **all of it is behind us**. Its one heavy import was the relative Siegel
lemma, `ArithmeticHeights` **5.6** — 5.7, which the ordering named, is packaged on the wrong
coefficient space and 2.6 repackages 5.6 itself; nothing from that roadmap's Layers 3, 4 or 6 is
used before Layer 4 here. ⚠ **Layer 0.4 turns out not to be on this path at all**: the ordering
put it there, and Step IV does not use it. Its consumers are Layers 5 and 7.
Now that 3.2 stands,
**3.3–3.8, 8.1, 8.3, 8.4, 8.5 and
the `w > 2` criterion of 7.4 are all within reach** — every classical application of
Thue–Siegel–Roth,
including Thue–Mahler and the two-variable unit equation, is available before any geometry of
numbers. The next milestone is **3.3**, the forms applications quote, which is also where the
dictionary between the places of `ℚ` and `Real.irrationalityExponent` gets built and where 3.2's
own sharpness test — that `κ = 2` is false — becomes stateable.

The path to the summit is Layer 4 → Layer 5 → 6.1 → 6.2 → 6.3. Layer 4 needs
`ArithmeticHeights` 4.1–4.4 and 3.1, and is independent of Layers 2 and 3 here; it can be built
in parallel with them by someone who prefers lattices to polynomials. Within Layer 5, 5.2 and 5.3
are Layer 2 in multihomogeneous dress and 5.5 is elementary; **5.4 is the delicate one**, because
its statement is easy to get wrong (the exceptional subspaces) and everything in 5.6 is
calibrated against its constants. 6.1 is where Layers 4 and 5 meet. After 6.3: 6.4–6.6, all of
Layer 7, 8.2, 8.6 and 8.7.

Register an intention before a substantial push; the layers are deliberately claimable
separately.

## Long horizon (a roadmap for a roadmap, not work to attempt here)

The theory built here is qualitative, with the elementary half of the quantitative theory beside
it. The quantitative Subspace Theorem proper — the statement that the finite set `T` of 6.1 has
at most an explicit number of members, uniformly in the field and in the heights of the forms —
is the natural next summit and is **not** work to attempt under this roadmap. Its statement is
recorded so that nobody mistakes 6.1 or Layer 9 for it. In the form of Evertse–Schlickewei (2002,
Theorem 2.1), as Bugeaud–Evertse quote it (2008, Proposition 4.1): for normalized forms and
exponents and `0 < δ ≤ 1`, there are proper subspaces `T_1, …, T_t` of `ℚ̄ⁿ`, defined over `K`,
with `t ≤ 4^{(n+8)²} δ^{−n−4} log (2r) log log (2r)`, such that for every
`Q > max (H^{1/\binom{r}{n}}, n^{2/δ})` the set of `x ∈ ℚ̄ⁿ` of twisted height
`H_{Q,L,c}(x) ≤ Q^{−δ}` lies in one `T_i`; Evertse–Ferretti (2013) improve the count to
`10^9 2^{2n} n^{14} δ^{−3} log (3 δ⁻¹ R D) log (δ⁻¹ log 3 R D)` for the large solutions of a
normalized system. The applications that need this strength — the bound
`p(n) > n (log n)^η` infinitely often for the digits of an algebraic irrational, every
`η < 1/11` (Bugeaud–Evertse 2008, Theorem 2.1), and their quantitative Ridout theorem — are
long-horizon with it. What separates it from this roadmap is one input and one reformulation.
The input: a polynomial dependence on `δ⁻¹` needs **Evertse's sharpening of Roth's lemma** (1995),
which is proved through an explicit form of **Faltings's product theorem** and so through
intersection theory on products of projective spaces; with the Roth's lemma of 2.7 the same
bookkeeping yields only Schmidt's doubly exponential count (1989). The reformulation: uniformity
in the field needs the **absolute** theory — twisted heights on `ℚ̄ⁿ`, and the absolute
Minkowski theorem of Roy–Thunder and Zhang in place of Layer 4.2, whose constants depend on `K`.

Also beyond this roadmap, each a roadmap of its own or part of one: **Vojta's refinement**, that
outside one effectively determinable exceptional subspace `U₀` the solutions are finite in number
(Vojta 1989; Schmidt 1993; Faltings–Wüstholz 1994, Theorem 9.1), which can be deduced from 6.4
but not in a few lines; the **Faltings–Wüstholz theorem** for forms of higher degree and the
Evertse–Ferretti deduction of it from the Subspace Theorem; the Subspace Theorem with **moving
targets** (Ru–Vojta); the uniform bound `exp ((6n)^{3n} (r + 1))` for the unit equation in a
group of rank `r` over any field of characteristic zero (Evertse–Schlickewei–Schmidt 2002) and
the Beukers–Schlickewei bound `2^{8(r+1)}` in two variables; **Laurent's theorem** and the rest of
the Mordell–Lang circle for tori; **Siegel's theorem** on integral points by the Corvaja–Zannier
method; the existence of `T`-numbers; and anything **effective**. **Do not attempt them here.**

## Provenance

Secondary to everything above: the milestones are the specification. Layers 0, 1.1–1.3, all
of Layer 2 and Layers 3.1–3.2 — **Roth's theorem** — are proved in this repository and nothing
else of Layers 3–9 is. What
exists elsewhere, in
[`rwst/lean-code`](https://github.com/rwst/lean-code)
(CC0), is the *other side* of the interface — statements of the Subspace Theorem recorded as
cited axioms, and sorry-free derivations of consequences from them — and it is useful in two
ways.

- As **consumers to test the pinned statements against**: `CITED/Ridout.lean`
  (`Ridout.finite_ratios` and its algebraic-multiplier form, a Ridout-type theorem derived from
  the two-variable Subspace Theorem — an instance of 3.3–3.4), `CITED/CorvajaZannierProof.lean`
  (the Corvaja–Zannier theorem on `‖α u‖` for `S`-units `u`), and
  `CITED/NairKumarRoutProof.lean` (an `S`-unit integrality statement from three variables over
  `ℚ`). A statement of 6.3 from which these three cannot be re-derived is the wrong statement.
- As **evidence for the conventions**. `CITED/SubspaceTheorem.lean` records the number-field form
  with points and coefficients in `K`, and `CITED/SchmidtSubspace.lean` the form with rational
  points and algebraic coefficients, as two axioms, because neither specializes to the other;
  6.3 is the statement that contains both. Both take `S : Finset (AbsoluteValue K ℝ)` with the
  membership of its elements among the places "documented, not enforced", and both are therefore
  refuted by the first example under *Conventions* above; `AB/SubspaceTheoremE.lean` carries the
  membership hypothesis and is sound, and omits the weights `mult`, which makes it weaker than the
  theorem over a field with a complex place. The conventions table is what those three files
  taught.
- `AB/StammeringSequences.lean`, `AB/ExpansionsInIntegerBases.lean` and
  `AB/ComplexityLowerBound.lean` state the definitions and theorems of 7.4–7.5, and
  `ForMathlib/Combinatorics/SubwordComplexity.lean` develops the complexity function; the
  theorems themselves are cited there, not proved.

## References

- E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge New Mathematical
  Monographs 4, 2006. **The reference for the whole roadmap**, and the source of every numbered
  citation above that names no other. §1.3 extensions of absolute values (Corollaries 1.3.2,
  1.3.5); §1.5 the fundamental inequality (1.8) and Liouville's inequality (Theorem 1.5.21);
  Proposition 1.6.2, heights of polynomials in disjoint variables; Theorem 2.8.21, the projective
  Liouville inequality; Chapter 5: the unit equation, Thue–Mahler (5.3.1–5.3.2), the
  hyperelliptic equation (Theorem 5.3.5), principal rings of `S`-integers (Proposition 5.3.6);
  Chapter 6: Roth's theorem (Theorems 6.2.3 and 6.4.1), the index (6.3.2), the index theorem
  (Lemma 6.3.4), the volume estimate (Lemma 6.3.5), Roth's lemma (Lemma 6.3.7), generalized
  Wronskians (Proposition 6.3.10), the proof (6.4.2–6.4.10), moving targets (Theorem 6.5.2), the
  strong gap principle and the count (Theorem 6.5.4, Lemma 6.5.6, 6.5.7), Mahler's example in
  characteristic `p` (6.2.8); Chapter 7: the Subspace Theorem (Theorem 7.2.2, Remark 7.2.3,
  Corollary 7.2.5, Theorem 7.2.6, Example 7.2.7, Theorem 7.2.9), its applications (Theorem 7.3.2,
  Corollary 7.3.5, Theorems 7.4.2, 7.4.6, 7.4.10), and its proof (7.5, Steps 0–IX: Lemmas 7.5.4,
  7.5.7, 7.5.12, Theorem 7.5.13, Lemmas 7.5.15, 7.5.19, 7.5.21, 7.5.24, 7.5.25, 7.5.29, 7.5.31,
  7.5.33). ⚠ The book's proof is adelic (7.5.6 and Appendix C.2); Layer 4 replaces exactly that
  part and nothing else. ⚠ The book treats forms with coefficients in a finite extension
  throughout 7.5 and remarks (7.5.3) that the reader may assume `F = K`; this roadmap takes the
  remark as its route.
- W. M. Schmidt, "Norm form equations", *Annals of Mathematics* **96** (1972), 526–551. The
  Subspace Theorem. "Simultaneous approximation to algebraic numbers by rationals", *Acta
  Mathematica* **125** (1970), 189–201, for 7.3.
- W. M. Schmidt, *Diophantine Approximation*, LNM 785, Springer, 1980. The classical exposition:
  Ch. V Roth's theorem, Ch. VI simultaneous approximation and the Subspace Theorem with its proof
  through Mahler's compound bodies and Davenport's lemma — the route Layer 4.4 replaces — Ch. VII
  norm forms, Ch. VIII approximation by algebraic numbers. Also *Diophantine Approximations and
  Diophantine Equations*, LNM 1467, 1991, for the `p`-adic statements in the form applications
  quote.
- H. P. Schlickewei, "The `p`-adic Thue–Siegel–Roth–Schmidt theorem", *Archiv der Mathematik*
  **29** (1977), 267–270. The Subspace Theorem with finite places.
- J.-H. Evertse, "An improvement of the quantitative Subspace theorem", *Compositio Mathematica*
  **101** (1996), 225–311. The lemma of 4.4. "The Subspace Theorem of W. M. Schmidt", in
  *Diophantine Approximation and Abelian Varieties*, LNM 1566, 1993, 31–50, for a short account of
  the whole proof.
- J.-H. Evertse, "On the Quantitative Subspace Theorem", *Journal of Mathematical Sciences*
  **171** (2010) (arXiv:1008.2268). The source of Layer 9, with complete proofs of the
  gap principles and the small-solutions bound, and of the statements in *Long horizon*.
- J.-H. Evertse and H. P. Schlickewei, "A quantitative version of the Absolute Subspace Theorem",
  *J. reine angew. Math.* **548** (2002), 21–127; J.-H. Evertse and R. G. Ferretti, "A further
  improvement of the Quantitative Subspace Theorem", *Annals of Mathematics* **177** (2013),
  513–590; J.-H. Evertse, "An explicit version of Faltings' Product theorem and an improvement of
  Roth's lemma", *Acta Arithmetica* **73** (1995), 215–248; W. M. Schmidt, "The Subspace Theorem
  in diophantine approximations", *Compositio Mathematica* **69** (1989), 121–173. Long horizon.
- K. F. Roth, "Rational approximations to algebraic numbers", *Mathematika* **2** (1955), 1–20;
  H. Davenport and K. F. Roth, *ibid.*, 160–167, for 3.7; D. Ridout, "The `p`-adic generalization
  of the Thue–Siegel–Roth theorem", *Mathematika* **5** (1958), 40–48.
- K. Mahler, "On the fractional parts of the powers of a rational number II", *Mathematika* **4**
  (1957), 122–124, for 3.5.
- Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge Tracts in Mathematics 160, 2004. The
  reference for Layer 1: Ch. 3 for `w_n`, `w_n^*`, the classifications and Wirsing's
  inequalities. E. Wirsing, "Approximation mit algebraischen Zahlen beschränkten Grades", *J.
  reine angew. Math.* **206** (1961), 67–77.
- B. Adamczewski and Y. Bugeaud, "On the complexity of algebraic numbers I. Expansions in integer
  bases", *Annals of Mathematics* **165** (2007), 547–565; B. Adamczewski, Y. Bugeaud and F. Luca,
  "Sur la complexité des nombres algébriques", *C. R. Acad. Sci. Paris* **339** (2004), 11–14, for
  7.4–7.5; S. Ferenczi and C. Mauduit, "Transcendence of numbers with a low complexity
  expansion", *Journal of Number Theory* **67** (1997), 146–161, for the `w > 2` criterion.
- Y. Bugeaud and J.-H. Evertse, "On two notions of complexity of algebraic numbers", *Acta
  Arithmetica* **133** (2008), 221–250. Long horizon; §§4–5 for the parametric statement and the
  systems of inequalities in the form quoted there.
- J.-H. Evertse and K. Győry, *Unit Equations in Diophantine Number Theory*, Cambridge Studies in
  Advanced Mathematics 146, 2015. Layer 8: unit equations, Thue–Mahler, and Ch. 9 for
  decomposable form equations.
- P. Corvaja and U. Zannier, "On the greatest prime factor of `(ab+1)(ac+1)`", *Proceedings of
  the American Mathematical Society* **131** (2003), 1705–1709, for 8.7; "A subspace theorem
  approach to integral points on curves", *C. R. Math. Acad. Sci. Paris* **334** (2002),
  267–271, for the proof of Siegel's theorem named under *Not owned here*; *Applications of
  Diophantine Approximation to Integral Points and Transcendence*, Cambridge Tracts 212, 2018.
- J.-H. Evertse, "On sums of `S`-units and linear recurrences", *Compositio Mathematica* **53**
  (1984), 225–244, for 8.2.
- P. Vojta, *Diophantine Approximations and Value Distribution Theory*, LNM 1239, Springer, 1987,
  for the general-position form 6.5; "A refinement of Schmidt's Subspace Theorem", *American
  Journal of Mathematics* **111** (1989), 489–518, and G. Faltings and G. Wüstholz, "Diophantine
  approximations on projective spaces", *Inventiones Mathematicae* **116** (1994), 109–138, for
  *Long horizon*.
