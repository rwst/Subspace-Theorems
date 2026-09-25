import Mathlib
import DiophantineApproximation.PlacesOver -- Layer 0.1
import DiophantineApproximation.ConjugatePlaces -- Layer 0.2, conjugates
import DiophantineApproximation.LocalExtension -- Layer 0.2, the local extension formula
import DiophantineApproximation.SIntegerLocalization -- Layer 0.3, the ring of `S`-integers
import DiophantineApproximation.SAdicHeight -- Layer 0.3, heights and primitive points
import DiophantineApproximation.FundamentalInequality -- Layer 0.4, the fundamental inequality
import DiophantineApproximation.LiouvilleInequality -- Layer 0.4, Liouville's inequality
import DiophantineApproximation.IrrationalityExponent -- Layer 1.1, the exponent
import DiophantineApproximation.LiouvilleExponent -- Layer 1.1, Liouville's theorem
import DiophantineApproximation.PolynomialSupNorm -- Layer 1.2, the naive height
import DiophantineApproximation.MahlerExponent -- Layer 1.2, the two exponents
import DiophantineApproximation.IrreducibleExponent -- Layer 1.2, Gelfond and irreducibility
import DiophantineApproximation.KoksmaMobius -- Layer 1.2, Koksma's Möbius invariance
import DiophantineApproximation.PolynomialEval -- Layer 1.3, archimedean bounds on a polynomial
import DiophantineApproximation.KoksmaComparison -- Layer 1.3, `w_n^* ≤ w_n`
import DiophantineApproximation.BoxPrinciple -- Layer 1.3, `n ≤ w_n`
import DiophantineApproximation.AlgebraicExponent -- Layer 1.3, `w_n ≤ d - 1`
import DiophantineApproximation.SimultaneousBox -- Layer 1.3, the box principle at several points
import DiophantineApproximation.RootLocation -- Layer 1.3, where the roots are
import DiophantineApproximation.WirsingSystem -- Layer 1.3, Wirsing's test points
import DiophantineApproximation.WirsingThird -- Layer 1.3, Wirsing's third inequality
import DiophantineApproximation.MvHasseDeriv -- Layer 2.1, Hasse derivatives in several variables
import DiophantineApproximation.MvHasseDerivTaylor -- Layer 2.1, Taylor and Leibniz
import DiophantineApproximation.MvHasseDerivHeight -- Layer 2.1, the size of a derivative
import DiophantineApproximation.DisjointVariables -- Layer 2.2, disjoint sets of variables
import DiophantineApproximation.WeightedOrder -- Layer 2.3, the weighted order of a polynomial
import DiophantineApproximation.PolynomialIndex -- Layer 2.3, the index at a point
import DiophantineApproximation.Wronskian -- Layer 2.4, the Wronskian in one variable
import DiophantineApproximation.GeneralizedWronskian -- Layer 2.4, generalized Wronskians
import DiophantineApproximation.CountingVolume -- Layer 2.5, counting and volume
import DiophantineApproximation.BoxMonomial -- Layer 2.6, the coefficients of the box
import DiophantineApproximation.MonomialHeight -- Layer 2.6, the height of a condition row
import DiophantineApproximation.IndexConditions -- Layer 2.6, the conditions behind the index
import DiophantineApproximation.AuxiliaryPolynomial -- Layer 2.6, the index theorem
import DiophantineApproximation.HeightTransport -- Layer 2.7, local factors to heights
import DiophantineApproximation.IndexRename -- Layer 2.7, the index under renaming
import DiophantineApproximation.PolynomialDeterminantHeight -- Layer 2.7, heights of determinants
import DiophantineApproximation.RothDecomposition -- Layer 2.7, the two Wronskians
import DiophantineApproximation.RothDeterminant -- Layer 2.7, the determinant of derivatives
import DiophantineApproximation.RothBaseCase -- Layer 2.7, Roth's lemma in one variable
import DiophantineApproximation.RothEstimates -- Layer 2.7, the three elementary estimates
import DiophantineApproximation.RothLemma -- Layer 2.7, Roth's lemma
import DiophantineApproximation.ApproximationClass -- Layer 3.1, approximation classes
import DiophantineApproximation.IndependentHeights -- Layer 3.1, independent sequences
import DiophantineApproximation.GlobalBound -- Layer 3.2, the product formula against bounds
import DiophantineApproximation.MvPolynomialEvalBound -- Layer 3.2, local bounds on a value
import DiophantineApproximation.RothLocalBound -- Layer 3.2, the bound at a place of `S`
import DiophantineApproximation.RothClass -- Layer 3.2, one approximation class
import DiophantineApproximation.RothKeyInequality -- Layer 3.2, Steps III to V
import DiophantineApproximation.RothAuxiliary -- Layer 3.2, Steps I and II
import DiophantineApproximation.RothTheorem -- Layer 3.2, Roth's theorem
import DiophantineApproximation.RationalPlaces -- Layer 3.3, the places of `ℚ`
import DiophantineApproximation.RothInfinity -- Layer 3.3, targets at infinity
import DiophantineApproximation.RothRational -- Layer 3.3, Roth's theorem over `ℚ`
import DiophantineApproximation.Ridout -- Layer 3.3, Ridout and the `p`-adic form
import DiophantineApproximation.ProjectiveTarget -- Layer 3.4, the zero of a form as a target
import DiophantineApproximation.ApproxProd -- Layer 3.4, the central quantity
import DiophantineApproximation.RothProjective -- Layer 3.4, the projective line
import DiophantineApproximation.PrimeProducts -- Layer 3.5, the primes of an integer
import DiophantineApproximation.MahlerPowers -- Layer 3.5, Mahler's theorem
import DiophantineApproximation.BinaryForm -- Layer 3.6, binary forms and their roots
import DiophantineApproximation.ThueEquation -- Layer 3.6, Thue's equation
import DiophantineApproximation.GapPrinciple -- Layer 3.7, the strong gap principle
import DiophantineApproximation.CountingApproximations -- Layer 3.7, counting approximations
import DiophantineApproximation.MovingTargets -- Layer 3.8, moving targets
import DiophantineApproximation.FinitePlaceValues -- Layer 4.1, the values of a finite place
import DiophantineApproximation.ModuleCovolume -- Layer 4.1, the covolume of an `𝓞 K`-lattice
import DiophantineApproximation.ApproximationDomain -- Layer 4.1, approximation domains
import DiophantineApproximation.ApproximationVolume -- Layer 4.1, volume against covolume
import DiophantineApproximation.FieldMinima -- Layer 4.2, successive minima over `K`
import DiophantineApproximation.FieldMinkowski -- Layer 4.2, Minkowski's second theorem over `K`
import DiophantineApproximation.ApproximationRank -- Layer 4.3, the rank of an approximation domain
import DiophantineApproximation.SIntegerApproximation -- Layer 4.4, approximation by `S`-integers
import DiophantineApproximation.EvertseLemma -- Layer 4.4, Evertse's lemma
import DiophantineApproximation.WedgeForm -- Layer 4.5, exterior powers of a system of forms
import DiophantineApproximation.WedgeDomain -- Layer 4.5, the wedge domain
import DiophantineApproximation.UnitNormalization -- Layer 5.1, the reductions
import DiophantineApproximation.SubspaceReduction -- Layer 5.1, the approximation classes
import DiophantineApproximation.MultiHomogeneous -- Layer 5.2, multihomogeneous polynomials
import DiophantineApproximation.MonomialDeviation -- Layer 5.2, counting the omitted monomials
import DiophantineApproximation.SubspaceAuxiliary -- Layer 5.2, the auxiliary polynomial
import DiophantineApproximation.FormIndex -- Layer 5.3, the index along linear forms
import DiophantineApproximation.FormSpecialization -- Layer 5.3, specializing a block
import DiophantineApproximation.GeneralizedRothLemma -- Layer 5.3, the generalized Roth lemma
import DiophantineApproximation.LinearFormValue -- Layer 5.4, Liouville for a linear form
import DiophantineApproximation.SubspaceNormal -- Layer 5.4, the normal vector of a hyperplane
import DiophantineApproximation.SubspaceHeightBounds -- Layer 5.4, the two bounds on `h(V(Q))`
import DiophantineApproximation.ExceptionalSubspace -- Layer 5.4, the exceptional subspaces
import DiophantineApproximation.PolynomialGrid -- Layer 5.5, the grid lemma
import DiophantineApproximation.SmallPoint -- Layer 5.5, non-vanishing at a small point
import DiophantineApproximation.LogComparison -- Layer 5.6, an elementary comparison of logs
import DiophantineApproximation.FormIndexSubspace -- Layer 5.6, index to surviving derivative
import DiophantineApproximation.SubspaceValueBound -- Layer 5.6, the local bounds of Step VI
import DiophantineApproximation.SubspaceKeyInequality -- Layer 5.6, Step VI
import DiophantineApproximation.PenultimateMinimum -- Layer 5.6, the penultimate minimum
import DiophantineApproximation.WedgeRecovery -- Layer 6.1, Lemma 7.5.33 as a function
import DiophantineApproximation.MinimaBounds -- Layer 6.1, the minima between two powers of `Q`
import DiophantineApproximation.ExponentGrid -- Layer 6.1, exponents on a grid
import DiophantineApproximation.WedgeExponentBound -- Layer 6.1, the box and the negative weight
import DiophantineApproximation.ParametricSubspace -- Layer 6.1, the parametric Subspace Theorem
import DiophantineApproximation.SubspaceTheorem -- Layer 6.2, the Subspace Theorem over `K`
import DiophantineApproximation.FormBaseChange -- Layer 6.3, forms along a ring homomorphism
import DiophantineApproximation.PlaceConjugation -- Layer 6.3, the places of a Galois extension
import DiophantineApproximation.ExtensionApproxProd -- Layer 6.3, the conjugated systems
import DiophantineApproximation.SubspaceAlgebraic -- Layer 6.3, algebraic coefficients
import DiophantineApproximation.AffineProd -- Layer 6.4, the affine quantity
import DiophantineApproximation.SubspaceAffine -- Layer 6.4, the affine Subspace Theorem
import DiophantineApproximation.GeneralPosition -- Layer 6.5, forms in general position
import DiophantineApproximation.SubspaceGeneralPosition -- Layer 6.5, Vojta's refinement
import DiophantineApproximation.SubspaceConsistency -- Layer 6.6, consistency with Layer 3
import DiophantineApproximation.LinearFormSubspaces -- Layer 7.1, the exceptional subspaces
import DiophantineApproximation.OneLinearForm -- Layer 7.1, one linear form
import DiophantineApproximation.BoundedDegreeApproximation -- Layer 7.2, bounded degree
import DiophantineApproximation.SchmidtExponents -- Layer 7.3, the exponents
import DiophantineApproximation.SimultaneousSubspaces -- Layer 7.3, two systems of forms
import DiophantineApproximation.SimultaneousApproximation -- Layer 7.3, simultaneous approximation
import DiophantineApproximation.StammeringWords -- Layer 7.4, stammering sequences
import DiophantineApproximation.DigitExpansions -- Layer 7.4, expansions in an integer base
import DiophantineApproximation.RepetitionSubspaces -- Layer 7.4, the primes of the base
import DiophantineApproximation.TranscendenceCriterion -- Layer 7.4, the criterion
import DiophantineApproximation.FactorComplexity -- Layer 7.5, the combinatorics
import DiophantineApproximation.ComplexityTranscendence -- Layer 7.5, the theorem
import DiophantineApproximation.UnitEquation -- Layer 8.1, the unit equation in two variables
import DiophantineApproximation.UnitEquationSeveral -- Layer 8.2, the unit equation in n variables
import DiophantineApproximation.DecomposableForm -- Layer 8.3, triangularly connected decomposable forms
import DiophantineApproximation.SIntegerExtension -- Layer 8.4, `S`-integers in an extension
import DiophantineApproximation.ThueMahler -- Layer 8.4, Thue and Thue–Mahler

/-!
# Diophantine approximation and the Subspace Theorem: target signatures

**This file is not the roadmap and is not exhaustive.** The definitive document is the
roadmap, `DiophantineApproximation/README.md`, which every `README.md` below refers to.
The statements here suggest Lean forms for the milestones whose names and shapes are most likely
to drift, so that contributors and reviewers converge on them; discharging all of them finishes
neither a layer nor the roadmap.

Everything below is stated against Mathlib alone: `Height.mulHeight`, the typed places
`NumberField.InfinitePlace` and `NumberField.FinitePlace`, `AbsoluteValue.LiesOver`, `Set.integer`
and `Set.unit`, and `LiouvilleWith`. The roadmap also consumes the `ArithmeticHeights` roadmap —
heights of polynomials and of subspaces, successive minima, Siegel's lemma — and the milestones
whose *statements* need those objects (Roth's lemma, the height of `V(Q)`,
Minkowski's second theorem over `K`) are specified in `README.md` and deliberately not prototyped
here: a prototype would have to restate those objects behind stand-ins. ⚠ The index theorem, Roth's
lemma and Minkowski's second theorem over `K` were on that list and have come off it: Layers 2.6,
2.7 and 4.2 are landed, so they appear below as discharged `example`s stated against the library
itself. The declarations elaborate
against the pinned Mathlib and are stated with `sorry` (allowed in this human-owned roadmap
library); what lands in `TauCeti/` must be proved.

Names here are unqualified inside `TauCetiRoadmap.DiophantineApproximation` so that the prototype
does not occupy Mathlib's root namespaces. In `TauCeti/` they take the names `README.md` pins:
`irrationalityExponent`, `mahlerExponent` and `koksmaExponent` sit in `Real`, `hasseDeriv` and
`index` in `MvPolynomial`, `approxProd` and `approxDomain` in `NumberField`.

**Landed milestones appear here as `example`s discharged by the library**, not as `sorry`s: a
milestone that `DiophantineApproximation/` proves is one whose signature has stopped drifting, and
the `example` is what certifies that the shape pinned here is the shape that was proved. Layers
0.1, 0.2, 0.3, 0.4, 1.1, 1.2, 2.1, 2.2, 2.3, 2.4, 2.5, 2.6, 2.7, 3.1, 3.2, 3.3, 3.4, 3.5, 3.6, 3.7,
3.8, 4.1, 4.2, 4.3, 4.4, 4.5, 5.1, 5.2, 5.3, 5.4, 5.5, 5.6, 6.1, 6.2, 6.3, 6.4, 6.5, 6.6, 7.1,
7.2, 7.3, 7.4, 7.5, 8.1, 8.2, 8.3 and 8.4 are landed —
Layers 3, 4, 5 and 6 are complete, and **the Subspace Theorem is proved, in the form its
consumers apply**: points in `K`, coefficients in a finite extension, in the affine form every
application of Layer 8 quotes, and for families of forms in general position of any finite
sizes, and on the projective line it is Roth's theorem and nothing else; **and it has begun to
say things about numbers** — one linear form with complex algebraic coefficients takes small
values at only finitely many integer points, an algebraic number is approached by algebraic
numbers of degree at most `D` to order at most `D + 1`, the two exponents of a real algebraic
number of degree `D` are both `min n (D - 1)` at every degree bound `n`, Schmidt's two
theorems on simultaneous approximation are proved, and a number whose digits stammer without
repeating is transcendental, and so is one whose digits have at most `C n` blocks of length `n`
infinitely often without repeating — and 1.3 is
landed **except for Wirsing's first two inequalities, which are optional** — their only consumer is
the optional Layer 1.4 — in
`DiophantineApproximation/{Nonarchimedean,PlacesOverFinite,PlacesOverInfinite,
PlacesOver,ConjugatePlaces,LocalExtension,SIntegerLocalization,SAdicHeight,FundamentalInequality,
LiouvilleInequality,IrrationalityExponent,LiouvilleExponent,PolynomialSupNorm,MahlerExponent,
IrreducibleExponent,KoksmaMobius,PolynomialEval,KoksmaComparison,BoxPrinciple,AlgebraicExponent,
SimultaneousBox,RootLocation,WirsingSystem,WirsingThird,MvHasseDeriv,MvHasseDerivTaylor,
MvHasseDerivHeight,DisjointVariables,WeightedOrder,PolynomialIndex,Wronskian,
GeneralizedWronskian,CountingVolume,BoxMonomial,MonomialHeight,IndexConditions,
AuxiliaryPolynomial,HeightTransport,IndexRename,PolynomialDeterminantHeight,RothDecomposition,
RothDeterminant,RothBaseCase,RothEstimates,RothLemma,ApproximationClass,
IndependentHeights,GlobalBound,MvPolynomialEvalBound,RothLocalBound,RothClass,
RothKeyInequality,RothAuxiliary,RothTheorem,RationalPlaces,RothInfinity,RothRational,
Ridout,ProjectiveTarget,ApproxProd,RothProjective,PrimeProducts,MahlerPowers,BinaryForm,
ThueEquation,GapPrinciple,CountingApproximations,MovingTargets,FinitePlaceValues,ModuleCovolume,
ApproximationDomain,ApproximationVolume,FieldMinima,FieldMinkowski,ApproximationRank,
SIntegerApproximation,EvertseLemma,WedgeForm,WedgeDomain,UnitNormalization,
SubspaceReduction,MultiHomogeneous,MonomialDeviation,SubspaceAuxiliary,FormIndex,
FormSpecialization,GeneralizedRothLemma,LinearFormValue,SubspaceNormal,SubspaceHeightBounds,
ExceptionalSubspace,PolynomialGrid,SmallPoint,LogComparison,FormIndexSubspace,
SubspaceValueBound,SubspaceKeyInequality,PenultimateMinimum,WedgeRecovery,MinimaBounds,
ExponentGrid,WedgeExponentBound,ParametricSubspace,SubspaceTheorem,FormBaseChange,
PlaceConjugation,ExtensionApproxProd,SubspaceAlgebraic,AffineProd,SubspaceAffine,
GeneralPosition,SubspaceGeneralPosition,SubspaceConsistency,LinearFormSubspaces,
OneLinearForm,BoundedDegreeApproximation,SchmidtExponents,SimultaneousSubspaces,
SimultaneousApproximation,StammeringWords,DigitExpansions,RepetitionSubspaces,
TranscendenceCriterion,FactorComplexity,ComplexityTranscendence,UnitEquation,
UnitEquationSeveral,DecomposableForm,SIntegerExtension,ThueMahler}.lean`;
0.1's three signatures below survived verbatim, 1.1's definition survived verbatim and one of its
five theorems lost a hypothesis, 1.2's two definitions survived and its `naiveHeight` abbreviation
did not, 1.3's two elementary signatures survived up to a **name collision**, 2.1's definition
survived verbatim and its one prototyped theorem survived with `R` weakened to a `CommSemiring`,
2.2 had nothing prototyped here at all and is stated below for the first time, 2.3's definition
survived verbatim while all three of its theorems lost hypotheses — twice the strict positivity of
the weights, once `IsDomain` as well — 2.4's one prototyped theorem survived verbatim, **3.2's one
prototyped theorem survived verbatim** — the statement of Roth's theorem pinned below is the
statement that was proved, hypothesis for hypothesis — **3.3's one prototyped theorem survived up
to the order of its two hypotheses** and was the only one of its four statements prototyped at
all, **3.4's one prototyped object — the definition `approxProd` — survived verbatim** and has
moved from this file into the library, where Layer 6.3 will find it, **3.5's one prototyped
theorem survived verbatim** — the second statement in a row to do so, and the first whose
hypotheses are all about natural numbers — **4.1's two prototyped definitions, `approxDomain` and
`approxWeight`, survived verbatim** and have moved into the library, where Layer 6.1 found them,
**6.1's one prototyped theorem survived verbatim** — the parametric Subspace Theorem pinned below
is the statement that was proved — **6.2's statement was never prototyped under its own name**,
since it is Layer 6.3's at `F = K` and `w = id` and was left implicit in it, and is stated below
for the first time — **6.3's one prototyped theorem survived verbatim**, hypothesis for hypothesis
and in order, which is the third statement of this file to do so and the only summit statement
that was pinned before any of the machinery under it existed, **6.4's one prototyped theorem
survived verbatim as well**, display for display — the fourth, and the two summit statements in a
row — its left-hand side having since been given the name `NumberField.affineProd`, which the
example below states in both shapes — **7.1's one prototyped theorem survived verbatim too**,
display for display, and changed only its name: `‖·‖` is a norm and not an absolute value, so
`finite_setOf_abs_sum_mul_le` is `Complex.finite_setOf_norm_sum_mul_le_fin`, the fifth statement
of this file to survive and the first outside Layers 3 to 6, **7.3's one prototyped theorem
survived up to the loss of a hypothesis** — `1 ≤ n` is not needed, since at `n = 0` both
exponents vanish and so does `min 0 (D - 1)` — **8.1's one prototyped theorem survived verbatim**,
the sixth to do so and the first of Layer 8, **and 8.2's two prototyped theorems survived
verbatim**, the seventh and eighth — and 0.2, 0.3, 0.4, 2.5, 2.6, 2.7,
3.1, 3.6, 3.7, 3.8, 4.2,
4.3, 4.4, 4.5, 5.1 5.2, 5.3, 5.4, 5.5, 5.6, 6.5, 6.6, 7.2, 7.4, 7.5, 8.3 and 8.4 had none to
survive: they are
prototyped here for the first time — 2.6, 2.7 and 4.2 deliberately, since the preamble above
judged their statements unstateable without the `ArithmeticHeights` objects, which was true until
those objects landed, 3.1 because it is elementary and was expected not to drift, 4.3 because its
rank is read from 4.2's minima, 4.4 because its bijections and triangular vectors had no settled
shape, 4.5 because its wedge domain is read from 4.4's output, 5.1 because the shape of its
approximation classes was settled only by the weight computation, 5.2 because the expansion
coefficients `a(L; J; I)` have no shape at all until one decides that they are coefficients of
`blockSubst A⁻¹ (∂_I P)`, and 7.2 because the height in its exponent is the naive height of the
primitive integer minimal polynomial of the approximant, an object Mathlib does not name and which
is defined only up to sign, and 7.4 because its hypothesis is a property of words — `V ^ w` for real
`w`, and prefixes of a sequence — that the roadmap's prose defined and nothing stated, and 7.5 because its complexity counts those
words. **7.3 was
prototyped in half**: its exponent identity was pinned and
survived, while **Schmidt's two theorems on simultaneous approximation**, which the roadmap's
prose names in the same paragraph, were not, and are stated below for the first time. What the
proofs taught:

* ⚠ **The archimedean half needs no finiteness at all.** `NumberField.isInfinitePlace_of_liesOver`
  is proved for an arbitrary field extension `F / K` — no `NumberField F`, no
  `FiniteDimensional K F`, not even algebraicity — because the whole argument happens inside the
  completion `F_w`, and Mathlib's Gelfand–Mazur (`NormedAlgebra.Real.nonempty_algEquiv_or`) asks
  neither for completeness nor for finite dimension. The `[NumberField F]` in the signature below
  is there only because the file states both halves together.
* ⚠ **The nonarchimedean exponent is `(e f)⁻¹` and Mathlib already knew it.**
  `NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap` is the local extension
  formula at a finite place — Layer 0.2's finite half — and it pins the exponent at once. The
  `t ≤ 1` asked for below is a corollary; `NumberField.exists_finitePlace_rpow_inv_eq_of_liesOver`
  is the sharp form, and it also exhibits `𝔓` above `𝔭`, which `t ≤ 1` alone does not.
* ⚠ **`AbsoluteValue.nonarchRpow` is new infrastructure.** Mathlib has no `rpow` of an absolute
  value. It is needed for *nonemptiness*, not for the classification, and it has to be available
  at **every** positive exponent, not just `t ≤ 1`: the exponent is only known to be `(e f)⁻¹`
  after the prime has been produced. For a nonarchimedean absolute value every positive exponent
  works; for an archimedean one only `t ≤ 1` does, and that half is `Real.rpow_add_le_add_rpow`.
* ⚠ **The hypothesis `IsInfinitePlace v ∨ IsFinitePlace v` in the third statement is load-bearing
  but not sharp.** It is what lets the proof case-split; an absolute value of `K` that is neither
  — a proper power of a place — also has a finite nonempty fibre, and nothing here proves that.
* ⚠ **Mathlib has ramification theory for infinite places and none for finite ones.**
  `InfinitePlace` carries `LiesOver`, `comap`, `IsUnramified`, `placesOver`, a local degree and
  the count `sum_inertiaDeg_eq_finrank`; `FinitePlace` carries none of it, and its one relevant
  lemma is stated for prime ideals with a TODO asking for places. So Layer 0.2's infinite half is
  three lines, and its finite half is mostly **vocabulary** — `FinitePlace.LiesOver`,
  `localDegree`, `placesOver`, their finiteness and nonemptiness, and the transfer of Mathlib's
  sum over `Ideal.primesOver` to a sum over places.
* ⚠ **`NumberField.InfinitePlace.inertiaDeg` is the local degree `[F_w : K_v]`, not a residue
  degree.** At a finite place `Ideal.inertiaDeg` is the residue degree `f` alone and the local
  degree is `e f`. The quantity the two halves of 0.2 share is the local degree, so the two
  fundamental identities are one statement read twice.
* ⚠ **`NumberField.FinitePlace.LiesOver` is not `AbsoluteValue.LiesOver`.** A finite place of `F`
  above `v` restricts to `v` itself only when `e f = 1`. The two notions are reconciled by
  `FinitePlace.liesOver_val_iff_localDegree_eq_one`, and the gap is exactly what forces Layer 0.1
  to classify the absolute values over `v` as *roots* of finite places.
* ⚠ **Galois transitivity needs no equivariance statement about finite places.** Neither
  `absNorm (σ 𝔓) = absNorm 𝔓` nor invariance of the adic valuation is used, and Mathlib has
  neither. Layer 0.1 classifies `w ∘ σ` on its own, and its uniqueness clause identifies the
  prime as the contraction of `{y | w y < 1}` along `σ`. The exponents are never compared.
* ⚠ **`InfinitePlace.mult` is what makes one statement out of two.** Above a *complex* place of
  `K` nothing is ramified — ramified means complex over real — so every multiplicity upstairs is
  `2` and the count is the bare degree; above a real place the multiplicities are mixed. The
  factor `v.mult` on the right reconciles the two cases.
* ⚠ **Layer 0.3's membership dictionary is already `ArithmeticHeights` 6.4 and is not restated.**
  `Set.mem_integer_iff_finitePlace` and `Set.mem_unit_iff_finitePlace` are the milestone's first
  clause verbatim, and `NumberField.SUnit.sum_mult_mul_log_add_sum_log` of 6.5 is its second in
  logarithmic form; only the multiplicative form had to be written, and it is two lines. The two
  `example`s below are the contract, not new work.
* ⚠ **`S.integer K` is a localization of `𝓞 K`, and that is what Layer 0.3 costs.** Mathlib
  carries `Set.integer` as a `Subalgebra` and proves nothing about the ring it is. Proposition
  5.3.6 needs the ring, so the localization has to be built first; the multiplicative set is
  `Set.integerSubmonoid`, the nonzero elements lying in no prime outside `S`, and the denominators
  come from `NumberField.exists_mem_asIdeal_iff_eq` of `ArithmeticHeights` 6.5 — which is why 0.3
  is the first file of this roadmap to consume `ArithmeticHeights`.
* ⚠ **The principal ideal theorem uses no Dedekind theory of `S'.integer K` and no ideal
  factorization.** One representative ideal per class, one nonzero element of each, and the
  finitely many primes containing those elements: that is the whole enlargement. The class number
  is never named and no power of an ideal is taken.
* ⚠ **Only "primitive ⇒ full local factors" is proved.** The converse is a statement about the
  maximal ideals of `S.integer K`; it has no consumer in this roadmap and is left open.
* ⚠ **`[Fintype ι]` must not appear in a statement that does not sum over `ι`.** Mathlib's
  `unusedFintypeInType` linter rejects it, so `Set.IsPrimitive` and every height statement of 0.3
  carry `[Finite ι]`, and the proofs take a `Fintype` from `Fintype.ofFinite`.
  `Set.isPrimitive_iff`, whose statement is a sum, is the one exception.
* ⚠ **Layer 0.4's two milestone clauses are one statement.** The truncated local factors
  `min 1 |α|_v` of a nonzero `α`, taken over *all* places, multiply to `(mulHeight₁ α)⁻¹` — that
  is the product formula read through `min 1 t * max t 1 = t`. The fundamental inequality and
  Liouville's inequality are both that identity cut down to a finite set of places, every factor
  being at most `1`.
* ⚠ **The fundamental inequality's lower bound needs no product formula.** The complementary
  product is not available: the complement of a `Finset` of finite places is not a `Finset`.
  Applying the upper bound to `α⁻¹` inverts the product over the *same* two sets, and
  `Height.mulHeight₁_inv` says the bound does not change.
* ⚠ **Truncating by `min 1 ·` makes Liouville's inequality stronger, not weaker.** Since
  `min 1 t ≤ t`, the truncated product is at most the untruncated one, so the statement proved
  implies the one without the truncation. There is no reason to state the other.
* ⚠ **Layer 0.4 uses none of Layer 0.2.** The local extension formula and the Galois action never
  appear: the inequality compares *one* chosen absolute value above each `v` with the full
  product over `F`, and never counts the places above `v` or adds their local degrees. What it
  consumes is 0.1's classification and `ArithmeticHeights` 0.3, `mulHeight₁_pow_finrank`, of
  which it is this roadmap's first consumer.
* ⚠ **Above an infinite place the work is `InfinitePlace.mult_comap_le`; above a finite place it
  is an `rpow`.** An absolute value over an infinite `v` *is* an infinite place `u` of `F`, and
  `v.mult ≤ u.mult` is Mathlib's once `AbsoluteValue.LiesOver` has become
  `u.comap (algebraMap K F) = v`. Above a finite `v` there is no identification — `w` is only
  `|·|_𝔓 ^ (e f)⁻¹` — and what saves the comparison is that the exponent is at most `1`, so
  `min 1 (s ^ t) ≥ min 1 s`.
* ⚠ **The acceptance test is the case `F = K`, and taking `K = ℚ` would be harder.** Deriving
  `Liouville.exists_pos_real_of_irrational_root` looks like a job for the relative inequality
  with `K = ℚ`, but that needs the infinite place of `ℚ` and an absolute value of `ℚ⟮α⟯` over it.
  Reading everything in `ℚ⟮α⟯` instead — one real embedding, no finite places — needs only
  `mulHeight₁_pow_finrank` and `Rat.mulHeight₁_eq_max`.
* ⚠ **The `ℝ≥0∞`-valued `iSup` was the right call and costs nothing.** Every statement of 1.1 is
  either `le_iSup₂` or `iSup₂_le_iff`, and the two `ENNReal` lemmas that carry the arithmetic are
  `ENNReal.ofReal_lt_ofReal_iff'` — an `iff` with a conjunction and no nonnegativity hypothesis —
  and `ENNReal.eq_top_of_forall_nnreal_le`. No `toReal`, no junk value, no case split on `⊤`
  anywhere except in the statement `irrationalityExponent ξ = ⊤ ↔ Liouville ξ` itself.
* ⚠ **Mathlib has Dirichlet's theorem, but not with unbounded denominators.**
  `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` gives infinitely many good
  approximations; `LiouvilleWith` asks for them along `atTop` *in the denominator*, and an
  infinite set of rationals is not visibly a set of unbounded denominator. The proof of
  `Irrational.liouvilleWith_two` never proves that it is: `LiouvilleWith` does not require
  `m / n` to be in lowest terms, so one Dirichlet approximation of denominator `d ≤ n` can be
  *inflated* to denominator `d * t ≥ N`, and its quality survives exactly when
  `d * t ^ 2 < 4 * (n + 1)`, which `n = N ^ 2 + 1` guarantees.
* ⚠ **`LiouvilleWith` has no `inv` in Mathlib and that one lemma is the whole Möbius milestone.**
  The affine part is ready-made (`add_rat_iff`, `mul_rat_iff`, `neg_iff`); what is missing is
  `ξ ↦ ξ⁻¹`, and its cost is not the inequality but the change of index: the approximations to
  `ξ⁻¹` are indexed by the *numerators* of those to `ξ`. Reducing to `0 < ξ` through `neg_iff`
  removes every sign case, and `1 < p` is needed only to reach the threshold `C / n ^ p ≤ ξ / 2`
  past which the numerator is bounded below.
* ⚠ **The naive height `max |m| n` and the denominator `n` give the same exponent**, because
  `n ≤ max |m| n ≤ (|ξ| + C + 1) * n` for every approximation of quality `C`: the two conditions
  differ by a constant, which `LiouvilleWith` absorbs. There is no separate "height exponent" to
  define, and `Real.liouvilleWith_iff_frequently_max` is the statement that there is not.
* ⚠ **Liouville's bound on the exponent needs no irrationality hypothesis.** The prototype below
  carried one and the proof does use it, but the statement holds at a rational too, where the
  exponent is `1` and the degree is `1`. The landed
  `Real.irrationalityExponent_le_natDegree` splits on `Irrational ξ` and closes the rational
  branch with `minpoly.natDegree_pos`.
* ⚠ **Mathlib already has the naive height of a polynomial: `Polynomial.supNorm`.** Its own module
  documentation calls it "the *(naive) height*" and declines the name only because `Height` is
  taken; it is the Gauss norm of the coefficient norm at `c = 1`, it works over `ℤ` directly, and
  it carries `le_supNorm` and `exists_eq_supNorm`. The `naiveHeight` abbreviation pinned below is
  therefore deleted, not landed. What is missing, and what Layer 1.2 builds, is the arithmetic of
  that norm and **Northcott's theorem for integer polynomials**.
* ⚠ **The engine of Layer 1.2 is a *height gap*, not a counting argument.** Every step replaces a
  solution by another polynomial — its primitive part, an irreducible factor, a Möbius transform —
  and has to show the images are still infinitely many. Counting fibres works for the primitive
  part and for nothing else. What works everywhere is
  `Polynomial.exists_pos_lt_supNorm_of_abs_aeval_lt`: below a threshold depending only on a height
  bound, a **nonzero** value at `ξ` forces the height above that bound. Koksma's side needs the
  root form, `Polynomial.exists_pos_lt_supNorm_of_abs_sub_root_lt`.
* ⚠ **`Polynomial.reflect` is the inversion, and it costs nothing.** The Möbius group is generated
  by integer affine maps and by `ξ ↦ ξ⁻¹`, exactly as in Layer 1.1; on polynomials the first is
  `Polynomial.comp` and the second is `Polynomial.reflect n`, which *permutes the coefficients* and
  so preserves the naive height on the nose. It is the only step of the layer with no constant, no
  threshold and no gap lemma.
* ⚠ **Gelfond's inequality is a prerequisite for Koksma's Möbius invariance, not an optional
  extra.** On Mahler's side `ArithmeticHeights` 2.3 buys only the restriction to irreducible
  polynomials. On Koksma's side the transform of a minimal polynomial is neither primitive nor
  irreducible, so the minimal polynomial of the image has to be *extracted* as an irreducible
  factor — and a factor's height is controlled by the product's height only through Gelfond.
* ⚠ **The integer form of Gelfond uses only the archimedean half of 2.3.** Over `ℤ` the naive
  height *is* the sup norm of the complex image, so `Polynomial.supNorm_mul_supNorm_le_two_pow` on
  `ℂ[X]` transports directly and the multivariate Gauss lemma is never consumed.
* ⚠ **The factorization argument runs at the scale `2 ^ (-n)`.** That is the unique scale with
  `λ ^ 2 * 2 ^ n ≤ λ`, and it is what makes the loss in Gelfond's inequality reproduce itself along
  a factorization instead of accumulating. The recursion is on `natDegree`, and it needs the
  polynomial primitive first — otherwise the prime factors of the content make the number of
  irreducible factors unbounded.
* ⚠ **`le_mahlerExponent` was already taken.** The name the box principle was prototyped under is
  Layer 1.2's order lemma — `(w : ℝ≥0∞) ≤ mahlerExponent n ξ` from an infinite `mahlerSet` — which
  every proof of Layer 1.3 uses. The box principle is `Real.le_mahlerExponent_of_aeval_ne_zero`.
* ⚠ **`w_n^* ≤ w_n` needs no hypothesis on `ξ`**, although the naive argument seems to: a Koksma
  solution `P` is fed to `mahlerSet`, which demands `0 < |P ξ|`, and that fails exactly when `ξ`
  is a root of `P`. It fails for **one** `P` up to sign, because a primitive irreducible integer
  polynomial with a given real root is unique up to sign (Gauss's lemma twice, through `minpoly`
  over `ℚ`), so the offenders have one height between them and the height gap discards them.
* ⚠ **The exponent `d - 1` needs the norm, not the height.** Layer 0.4's fundamental inequality
  bounds `|γ|` below by `(H_K γ)⁻¹` at a single place, and `H_K (P ξ) ≍ H(P) ^ d`; that proves
  only `w_n ≤ d`. The sharp `d - 1` comes from `∏ w, w γ ^ mult w = |N γ| ≥ 1` for an algebraic
  **integer** `γ`, where the distinguished place is the one *not* estimated — so Layer 1.3 uses
  `NumberField.InfinitePlace.prod_eq_abs_norm`, and integrality is bought with
  `Polynomial.scaleRoots` rather than by moving `ξ`.
* ⚠ **Wirsing's third inequality is landed, and it is the one that needs no root separation.**
  `w_n^* ≥ w_n / (w_n - n + 1)` is proved by Wirsing's own construction: a box principle at `n`
  points at once (`DiophantineApproximation/SimultaneousBox.lean`) produces, for every `H`, a
  polynomial that is `≤ H ^ (-w)` at `ξ` and `≤ H` at `n - 1` further points, and the count of
  roots in disjoint discs does the rest. The approximant is real for a **counting** reason — the
  disc around `ξ` holds exactly one root and is stable under conjugation — so the obstruction
  that blocks the other two never arises.
* ⚠ **Wirsing's first two inequalities need the hypothesis `1 ≤ n`, which the prototypes omitted.**
  At `n = 0` both exponents are `0` (`Real.mahlerExponent_degree_zero` and
  `Real.koksmaExponent_degree_zero`: a constant polynomial has `|P ξ| = H(P)`, and one with a root
  is the zero polynomial), so `w_n + 1 ≤ w_n^* + n` reads `1 ≤ 0`. The third inequality needs no
  such repair: at `n = 0` it reads `0 ≤ 0`.
* ⚠ **Wirsing's first two inequalities are not landed, and the obstruction is the real root.**
  Both bound `w_n` above in terms of `w_n^*`, so both must produce a **real** algebraic
  approximant from a small value `|P ξ|`, and the nearest root of an arbitrary `P` need not be
  real. Following Bell–Bugeaud, a root that is *strictly* nearest is real (its conjugate would be
  a second root at the same distance), and a root of multiplicity `r ≥ 2` in the distance ordering
  forces `w_n^@ ≤ (w_n - 1) / 2` for the exponent `w_n^@` measured with complex approximants; so
  the first inequality follows from the nearest-root estimate `|ξ - α| ≪ |P ξ| H(P) ^ (n - 2)`
  exactly when `w_n > 2 n - 3`. That estimate is itself missing: it needs
  `|P' (α)| ≫ M(P) ^ -(d - 2)`, which is `|disc P| ≥ 1` together with the product formula
  `disc P = lc(P) ^ (2d - 2) ∏_{i < j} (α_i - α_j) ^ 2` — Mathlib has `Polynomial.discr` and
  `Polynomial.resultant_deriv` but not that formula, and the routes that avoid it lose a factor
  `M(P) ^ (1/2)` and reach only `w_n - n + 1/2`. **In the remaining range `n ≤ w_n ≤ 2 n - 3` the
  first inequality needs the second**, and the second is Wirsing's generalized-resultant
  construction (a basis chosen from the monomial multiples of several polynomials, as in Poëls's
  and Dixit's treatments), which nothing in Mathlib comes near.
* ⚠ **Only the second inequality has a consumer, and it is Layer 1.4.** With `w_n^* ≤ w_n`, the
  second gives `w / 2 ≤ w^* ≤ w` for `w = limsup w_n / n`, which matches Mahler's four classes to
  Koksma's one for one — including `A = A^*`, since a transcendental `ξ` has `w_n ≥ n`, hence
  `w_n^* ≥ (n + 1) / 2` and `w^* ≥ 1 / 2`. The first gives only `w - 1 ≤ w^* ≤ w`, which settles
  `S`, `T` and `U` but leaves `A` open, because `w_n^* ≥ w_n - n + 1 ≥ 1` still allows
  `w^* = 0`; and the third gives nothing there, since `w_n / (w_n - n + 1) ≤ 2` once `w_n ≥ 2 n`.
  Layer 7.3 consumes the third alone, and no other milestone consumes any of the three. **Both
  missing bounds are therefore optional, and so is 1.4**: the roadmap's critical path leaves
  Layer 1 at what is landed.
* ⚠ **The Leibniz rule for Hasse derivatives cannot be reached by induction on `μ`.** The
  composition law reads `∂_(single j 1) ∘ ∂_ν = (ν j + 1) • ∂_(ν + single j 1)`, and recovering
  `∂_(ν + single j 1)` from it means dividing by `ν j + 1`, which is not invertible in a general
  commutative semiring — and characteristic `p` is exactly where the Hasse derivative earns its
  keep. What works is the **substitution formula** `coeff μ (P (C X + X)) = ∂_μ P`, after which
  Leibniz is `MvPolynomial.coeff_mul` applied to a ring homomorphism.
* ⚠ **The only differentiation Layer 2.1 does by hand is against a single variable, and it is
  Pascal's rule.** `∂_μ (P X j) = (∂_μ P) X j + ∂_(μ - single j 1) P` is
  `(a + b).choose b = (a - 1 + b).choose b + (a + (b - 1)).choose (b - 1)` one variable at a
  time; the substitution formula then follows by `MvPolynomial.induction_on` over `C`, `+` and
  `· * X j`. Proving the substitution formula directly would need the multivariate binomial
  theorem, and proving Leibniz directly would need a reindexing of a double sum over two
  antidiagonals. Neither is needed.
* ⚠ **`R` may be a `CommSemiring`, and the composition law's scalar is a natural number.**
  Nothing in 2.1 subtracts, so the `CommRing` prototyped here was too strong; and writing the
  scalar as an `ℕ`-action rather than a cast into `R` removes every `Nat.cast` from the
  statements that follow. The composition law cannot be stated as a `Finsupp.prod` of
  single-variable operators at all: that product would live in `Module.End R (MvPolynomial σ R)`,
  which is a monoid and not a commutative one, so `Finsupp.prod` does not typecheck there.
* ⚠ **The height side is `2 ^ totalDegree`, and it stops at the local factor.** The roadmap asked
  for `2 ^ (∑ j, degreeOf j P)`, which is undefined when `σ` is infinite; `totalDegree` is both
  sharper and always available. Turning the two local estimates into a statement about
  `MvPolynomial.mulHeight` needs a transport lemma with **one** input and a **one-sided**
  nonarchimedean hypothesis, and `ArithmeticHeights`'s `Finsupp.mulHeight_le_of_forall_iSup_le`
  has two inputs and demands *equality* at the nonarchimedean places — which Gauss's lemma
  supplies for a product and a Hasse derivative does not.
* ⚠ **In disjoint variables the height is multiplicative at every place, with no ultrametric
  hypothesis anywhere.** Gauss's lemma needs `IsNonarchimedean` and is false without it; Layer
  2.2 needs nothing, because there is no sum of several terms to which a triangle inequality
  could be applied — the antidiagonal of an exponent of `σ ⊕ τ` meets the two supports in exactly
  one point, so each coefficient of the product is a single product of coefficients. The
  archimedean places behave exactly as the finite ones do.
* ⚠ **The local identity needs no hypothesis; the height identity needs two.** At an absolute
  value the identity holds for all `f` and `g`, `f = 0` included, where both sides are `0`. The
  height identity does not, because `mulHeight 0 = 1` is a junk value: at `f = 0` the left side
  is `1` and the right side is the height of `g`. This is the same asymmetry as in Gauss's
  lemma, and it is why `f ≠ 0` and `g ≠ 0` appear below.
* ⚠ **The bridge to Mathlib's Segre relation is `Finsupp`, not `MvPolynomial`.**
  `Height.mulHeight_fun_mul_eq` is stated for tuples over *finite* index types, and the exponents
  of a polynomial are `σ →₀ ℕ`, which is not one. The passage goes through
  `ArithmeticHeights`'s `Finsupp.mulHeight_eq_mulHeight_comp` on the supports, and once it is
  made the whole milestone is a statement about finitely supported families —
  `Finsupp.mulHeight_eq_mulHeight_mul_mulHeight` — of which only the coefficient identity is
  about polynomials at all.
* ⚠ **Renaming invariance comes free and is what Layer 2.7 will consume.** The statement the
  roadmap writes uses `Sum.inl` and `Sum.inr`, but Roth's lemma multiplies two Wronskians already
  sitting inside one variable set. `MvPolynomial.mulHeight_rename_of_injective` — the height does
  not see how the variables are named — reduces the second to the first, and the usable form is
  stated for two injections with disjoint ranges.
* ⚠ **The index is the weighted order of the translate, and that is the whole of Layer 2.3.**
  `MvPolynomial.coeff_taylorAt` — the coefficients of `P (X + α)` are the Hasse derivatives of
  `P` at `α` — is Layer 2.1's Taylor expansion read as a statement about one polynomial instead
  of two. After it the index mentions no derivative and no point, so the valuation properties are
  proved once for the **weighted order of a support**, in a file that mentions neither
  (`WeightedOrder.lean`), and the index file is three lines of rewriting per theorem.
* ⚠ **Multiplicativity needs no monomial order.** The textbook proof refines the weight by a term
  order so as to name a unique lowest term in each factor, which would need the variables
  well-ordered — a hypothesis the statement does not have. The lowest *weighted homogeneous
  parts* are polynomials rather than terms, and they multiply because Mathlib's weighted
  homogeneous components are a grading (`IsWeightedHomogeneous.mul`). Nothing whatever is assumed
  about `σ`, and `NoZeroDivisors` is used exactly once, to know that the product of the two
  lowest parts is not zero.
* ⚠ **`0 < d j` is never used, and the degenerate case is not the expected one.** Nonnegativity
  is what distributes the single `ENNReal.ofReal` of the definition over the sum, and that is all
  the positivity any of the theorems needs. Strict positivity is still the right thing to read,
  because Lean's `k / 0 = 0` makes a variable of weight `0` *invisible* to the index rather than
  making the index infinite: at `d j = 0` the index of `X j` is `0`, not `⊤`.
* ⚠ **`index_of_unique` needs no domain.** `Polynomial.rootMultiplicity` at `a` is the trailing
  degree of the translate over any commutative ring, so the prototype's `IsDomain` came out; what
  cannot come out is `P ≠ 0`, because `rootMultiplicity a 0 = 0` while the index of `0` is `⊤`.
* ⚠ **Mathlib has no Wronskian of more than two polynomials, and the one-variable criterion is
  the whole of Layer 2.4.** `Polynomial.wronskian` is the pair `a b' - a' b`; the `n`-polynomial
  determinant, and the theorem that it detects linear independence in characteristic zero, are
  new here. They are proved by leading coefficients rather than by the classical argument that
  differentiates a relation over the field of rational functions: every term of the Leibniz
  expansion of the Wronskian sits in the *same* degree, because differentiating `i` times lowers
  a degree by `i` whichever column it happens in, so the top coefficient of the Wronskian of a
  family with pairwise distinct degrees `d j` is the determinant of the binomial coefficients
  `(d j).choose i`.
* ⚠ **That binomial determinant is a statement about lacunary polynomials.** It is nonzero
  exactly because a polynomial with `n` terms cannot vanish to order `n` at `1`, which the Euler
  operator `p ↦ X p'` and a Vandermonde determinant in the exponents settle in a dozen lines.
  This is the only arithmetic in the milestone, and the only place characteristic zero is used
  twice over — the other use is the factor `∏ i, i !` between the two normalisations of the
  Wronskian.
* ⚠ **The chain rule for the Kronecker substitution is Layer 2.1's Taylor formula again, and the
  order bound falls out of it.** Substituting `X s ↦ T ^ e s` and then translating `T` to `a + U`
  is the same as translating the variables to `a ^ e` and then substituting
  `X s ↦ (a + U) ^ e s - a ^ e s` — polynomials with **zero constant term**. So the coefficient
  of `U ^ i` cannot see a derivative of total order above `i`, and the admissible orders
  `|μ i| ≤ i` of the milestone are not imposed on the expansion: they are what the expansion
  produces. No Faà di Bruno formula appears anywhere.
* ⚠ **Nothing is assumed about `σ` here either.** The Kronecker weights have only to separate the
  finitely many exponent vectors that actually occur, and they are found by avoiding the roots of
  finitely many nonzero polynomials over `ℤ` — an argument that never enumerates the variables,
  where the usual base-`B` digit construction would have to. `Finsupp.exists_weight_injOn` is the
  reusable half and mentions no polynomial ring at all.
* ⚠ **The three estimates of Layer 2.5 are one exponential-moment estimate, not three.** The
  milestone said "one each"; in fact `∫_{∑ x j ≤ s} ∏ j, g (x j) ≤ exp (λ s) (∫ exp (-λ x) g x)^m`
  proves both tails, at two weights — the indicator of `[0, 1]` and the density of one coordinate
  of a point of the standard simplex — and Mathlib's `integral_fintype_prod_volume_eq_pow` is what
  decouples the coordinates. What separates the two is a single pointwise inequality about `exp`.
* ⚠ **Every restriction Bombieri–Gubler put on the parameters of these estimates is an artefact
  of their proof.** `ε ≤ 1/2` in Lemma 6.3.5 is vacuous — beyond `ε = 1/2` the region is empty —
  and `0 < λ ≤ n + 4`, `η ≤ 2/(n+1)` in (7.24)–(7.25) are the price of truncating an alternating
  series after three terms and pairing off the tail. The pointwise bound
  `exp (-u) ≤ 1 - u + u²/2`, which holds for **every** `u ≥ 0` and follows from Mathlib's
  `Real.quadratic_le_exp_of_nonneg` together with `(1+u+u²/2)(1-u+u²/2) = 1 + u⁴/4`, gives the
  same three terms with no restriction at all.
* ⚠ **The `6` in `exp (-6 m ε²)` is `6 ^ k * k ! ≤ (2k+1)!`**, sharp at `k = 1`: the termwise
  comparison of the series of `sinh u` with that of `exp (u²/6)`. Mathlib has no inequality of
  this kind for `sinh`, and it is the only place in the layer where a power series is summed.
* ⚠ **The multihomogeneous tail is a proportion, and that is what removes the simplex volume.**
  The book's `V` is an `m n`-dimensional volume which the book itself rewrites, in the next
  display, as an integral over `[0,1]^m` against the density of one simplex coordinate; the
  rewriting is the volume `r ^ k / k !` of a simplex, which Mathlib does not have. Against the
  *normalised* density the factor `V₀ = (n !)^(-m)` cancels from both sides of `V / V₀`.
* ⚠ **Only the upper lattice-point bound needs `t > 0`, and the hypothesis is not decoration.**
  At `t = 0` the origin is always an admissible lattice point while the region has no volume.
  The lower bound holds at every `t`, and needs no disjointness of the boxes either — a covering
  suffices.
* ⚠ **Layer 2.6 consumes `ArithmeticHeights` 5.6, not 5.7.** Layer 5.7 packages Siegel's lemma
  on the coefficient space of `totalDegree P ≤ D` — the simplex of monomials — while Lemma 6.3.4
  bounds the *partial* degrees, which is a box. Neither shape contains the other usefully, so
  2.6 applies the relative Siegel lemma of 5.6 to the box index type `∀ j, Fin (d j + 1)`
  directly and carries its own coefficient dictionary, `MvPolynomial.ofBox`. The roadmap's route
  was half right: 5.7 is a sibling of 2.6, not an ancestor.
* ⚠ **The rank form that 5.7 sent 5.6 back for is not what 2.6 needed.** Layer 2.5 counts
  *conditions*, and `Matrix.rank_le_card_height` is the only thing 2.6 says about the rank; the
  row form of 5.6 would have served. Nothing in Roth's method asks whether the conditions are
  independent.
* ⚠ **The `log 2` of Lemma 6.3.4 is the binomial coefficient, and it is the only loss.** A
  condition row is the multiplication table `(∏ j, (I j).choose (μ j)) ∏ j, α j ^ (I j - μ j)`,
  so Mathlib's Segre relation gives its height as a product of one-variable heights *exactly*,
  and the tuple of powers `α ^ k, k ≤ d`, has height *exactly* `H(α) ^ d`. The single estimate
  made is `(I j).choose (μ j) ≤ 2 ^ d j`.
* ⚠ **The transport from local factors to the height that the roadmap recorded as missing is
  three lines.** `Height.mulHeight_le_pow_totalWeight` takes one tuple, a constant at the
  archimedean absolute values and `≤ 1` at the others; `finprod_le_finprod₀` is not even needed,
  since `finprod_induction` bounds a `finprod` of factors in `[0, 1]` by `1` with no
  finite-support hypothesis at all.
* ⚠ **Three quantities have to be negligible, and they are of three different orders.** The
  lattice-point correction is `O(m² / D₀)`, the `√M` separating the Arakelov normalization from
  the sup-norm one is `O(∑ j, log (d j))`, and the discriminant of `K` is `O(1)`. All three are
  `o(∑ j, d j)`, and that is the whole content of the book's `o(1)`.
* ⚠ **Roth's lemma is an induction on `θ`, not on `σ`.** Written with the book's `σ` the step
  would have to replace `σ` by `√σ` and a real power would appear in every hypothesis; written
  with `θ` and `σ = θ ^ (2 ^ m)` it replaces `θ` by `θ ^ 2` and **leaves `σ` alone**, so the
  hypotheses on the degrees and on the heights carry over verbatim and no `Real.rpow` occurs
  anywhere inside the induction. The book's exponent is one change of variable at the end.
* ⚠ **The constant `2 m` is uniform, and the reduction to `θ < 1/2` is what makes it so.** At
  `θ ≥ 1/2` the conclusion `index ≤ 2 m θ` is free, because a nonzero polynomial of partial
  degrees at most `d` has index at most the number of variables; so the step may assume
  `θ < 1/2`, and it is `θ ^ 2 < θ / 2` that closes both cases of the quadratic estimate. Without
  that reduction the one-variable case would have to be carried at the sharper constant `1`.
* ⚠ **The separated variable is `X 0` and the induction runs with the degrees *increasing*.**
  Mathlib's `MvPolynomial.finSuccEquiv` splits off the *first* variable, and Roth's lemma
  separates the one of *smallest* degree; the book's decreasing statement is recovered once, at
  the end, by `rename Fin.rev`, which the index, the height and the partial degrees all follow.
* ⚠ **Both families of the tensor decomposition are independent for one reason.** Choosing the
  first to be a basis of the span of the coefficients of `P` along the separated variable makes
  the independence of the second a statement about a linear functional: a relation among the
  coefficient columns kills every coefficient, hence the span, hence every basis vector.
* ⚠ **There is no projective bound on the height of a *sum* of polynomials, so the determinant
  is estimated locally and transported once.** `H(N X + 1) = N` while both summands have height
  `1`, so the Leibniz expansion cannot be bounded term by term in the projective height. What is
  needed is the transport with a one-sided inequality at the nonarchimedean absolute values, and
  `AdmissibleAbsValues.hasFiniteMulSupport` gives the missing finite-support fact in three
  lines — Mathlib's own version, for a family rather than a single element, is private.
* ⚠ **The support count, not the total degree, keeps the constant linear in `p`.** Iterating
  `MvPolynomial.iSup_coeff_mul_le_two_pow` over a `p`-fold product costs `2 ^ (D p (p+1) / 2)`,
  because the accumulated factor's total degree grows; iterating
  `MvPolynomial.iSup_coeff_mul_le_card_support`, whose constant is the *smaller* support, costs
  `2 ^ (D p)`. In Roth's lemma `p` is as large as the smallest degree, so the difference is the
  whole estimate — and `Real.log 2 < 0.694` is then load-bearing, since `log 2 ≤ 1` would put
  `log p! + 2 (∑ j, d j) p log 2` above the `4 p d` the hypothesis allows.
* ⚠ **Only `Finsupp.degree (μ i) ≤ i` is used of Layer 2.4.** The orders of the generalized
  Wronskian never have to be pinned, and the *multivariate* criterion serves for the family in
  one variable as well, so Layer 2.4's univariate Hasse–Wronskian is not called here at all: it
  is used only inside 2.4's own proof.
* ⚠ **Lemma 6.4.3 is stars and bars, and the slack is a coordinate.** The labels are the tuples
  `c : A → ℕ` with `∑ a, c a ≤ N`, and adding one coordinate for `N - ∑ a, c a` turns them into
  the tuples on `Option A` that sum to `N` *exactly*, which is Mathlib's
  `Finset.card_finsuppAntidiag_nat_eq_choose`. The count comes out as an equality,
  `(N + |A|).choose |A|`, with no hockey-stick identity and no induction on `N`; the book's
  "the number of solutions of this inequality is" is literally true, not an estimate.
* ⚠ **Nothing in Mahler's reduction is about places, heights or number fields.** The whole of
  6.4.2–6.4.3 is the statement that finitely many cells cover the unit simplex, so it is stated
  for an arbitrary finite index type `A` and an arbitrary family `φ a : X → ℝ`. ⚠ Over a number
  field `A` is *not* a set of places: the roadmap's convention is two typed finsets, so a
  consumer instantiates `A` with the disjoint union of their coercions to types.
* ⚠ **The profile is what needs `0 < f a`, and that is the book's "non-trivial approximation".**
  A `β` with `β = α v` has local factor `0` at `v` and no logarithmic profile at all; there is at
  most one such `β` per place, so a consumer discards finitely many solutions before classifying
  the rest, exactly as the book does with `Λ(β) < 1`.
* ⚠ **Northcott is the only arithmetic in 3.1, and it gives an infinite sequence, not a tuple.**
  The recursion asks each time for an element of `X` of height above `M h(β j)`, which exists
  because a set of bounded height is finite and `X` is not. `1 < M` is needed only to make the
  terms distinct — existence holds at every `M` — and the `Fin m` form the auxiliary polynomial
  consumes is a restriction of the sequence.
* ⚠ **Step IV is the product formula over *all* the places, and Layer 0.4 will not do.** The
  fundamental inequality cuts the product down to `S`, and the local bound on `|Q(β)|_v` carries
  the local factor of the coefficients of `Q`, whose product over `S` alone is not bounded by
  `h(Q)`: the complementary product can be smaller than `1`. Routing Step IV through 0.4 charges
  `h(Q)` and the `h(β j)` twice and proves Roth's theorem only for `κ > 4`. Layer 0.4 is used by
  Layers 5 and 7 and by the gap principle of 3.7, not by Step IV; since 3.8 the core of the proof
  quotes its one-place bound, `max |x|_w 1 ≤ H(x)`, for the sizes of the targets.
* ⚠ **Nothing tends to infinity.** The book's `D → ∞` is replaced by one explicit `D`: every
  error term is `O(D / L)` except `([K : ℚ] + 2 ∑ a, w_a) log (D + 2)`, and
  `Real.exists_le_and_mul_log_add_lt` — `log` is eventually beaten by any positive multiple of
  the identity — settles the comparison. No filter, no `IsLittleO` and no `Tendsto` occurs in
  Layer 3.2; Layer 3.8's `o` is used once, to produce the `δ` of the chain statement.
* ⚠ **`κ > 2` is used exactly once, as `1 / κ < 1 / 2`.** It is what leaves room for the two
  losses, `4 ε` from the differentiation and `|S| / N` from the size of the approximation class,
  and the contradiction is `κ (1 - |S| / N) (1/2 - 4 ε) > 1`. Every other step of the proof is
  uniform in `κ`.
* ⚠ **The constants of the data are two, and both are hypotheses of the inner statements.**
  `C_α` bounds `|α v|_v` and `C₁` bounds `h(α v) + log 2 + 1`; the index theorem's own constant
  `r / (1 - r ∑ V)` cancels against the sum of the volumes under the feasibility hypothesis, which
  is why the number of variables may be taken as large as Lemma 6.3.5 demands without the height
  of the auxiliary polynomial growing with it. Since Layer 3.8 both are indexed by the coordinate,
  one per member of the chain.
* ⚠ **The factor at the target `∞` is `(max 1 |β| v)⁻¹`, not `min 1 (|β| v)⁻¹`.** The two agree
  away from `β = 0`, and the second is what `README.md` writes; but `(0 : ℝ)⁻¹ = 0` in Lean, so
  the literal reading gives `0` at `β = 0` where the value of the factor is `1`. Written as the
  reciprocal of a maximum the definition needs no case and no hypothesis.
* ⚠ **Inverting is not enough: the change of variable is `β ↦ (β - c)⁻¹`.** The map `β ↦ β⁻¹`
  exchanges the targets `0` and `∞` instead of removing `∞`, so it cannot clear a *mixed*
  configuration. The base point `c ∈ K` has to avoid the finitely many targets, which is possible
  because `K` is infinite; and the distortion it introduces is absorbed by lowering `κ` to some
  `κ₁ ∈ (2, κ)`, with Northcott collecting the finitely many solutions of small height. That is
  the only place in Layer 3.3 where `κ > 2` is used with room to spare.
* ⚠ **Ostrowski gives a *power* of `padicNorm p`, and a power would be fatal.** A finite place of
  `ℚ` is only known to be equivalent to some `padic p`; an exponent `t ≠ 1` would turn Ridout's
  `2 + ε` into `(2 + ε) / t`. The exponent is pinned to `1` by the height of `p⁻¹`, whose finite
  part is `p` and receives a contribution from exactly one finite place.
* ⚠ **The `p`-adic form gains its exponent at the infinite place.** With the `p`-adic place alone
  Roth's theorem gives `2 + ε`; the exponent `1 + ε` of `w (α - n) ≤ |n| ^ (-1 - ε)` comes from
  the target `∞` at the infinite place, where an integer has local factor exactly `H(n)⁻¹`. The
  `OnePoint` form is therefore not a convenience: without it the statement is out of reach.
* ⚠ **A prime of `S₁ ∩ S₂` carries two factors and Roth's theorem carries one target per place.**
  Coprimality reconciles them: such a prime divides at most one of `p` and `q`, so on each of the
  `2 ^ |S₁ ∩ S₂|` classes cut out by which it divides, one factor is `1`. Ridout's solution set
  is the union of those classes, and it is the only statement of Layer 3.3 whose proof splits it.
* ⚠ **`approxProd` is a function on projective space only because of `LiesOver`.** The numerator
  of a local factor is an absolute value of `F` and the denominator one of `K`; under `x ↦ c • x`
  the first scales by `w v (algebraMap K F c)` and the second by `v c`, and these agree only when
  `w v` lies over `v`. The hypothesis is free, since every layer carries it, but it belongs in
  the statement of the invariance — `README.md`'s table claims the invariance unconditionally.
* ⚠ **Linear independence of two forms enters exactly once, as `a₀ b₁ - a₁ b₀ ≠ 0`.** Everything
  local in Layer 3.4 is Cramer's rule read at one absolute value: the determinant bounds the sup
  norm of `x` against the larger of the two values, which is what stops both normalized values
  from being small at the same point, and the constant it produces is `∑ |coefficients| / |det|`.
* ⚠ **The comparison between a form and a target needs a constant that grows with the target.**
  At `β = t + 1` the truncated factor `min 1 |β - t|` is `1` while the normalized value of the
  form is `1 / max 1 |β|`, so no absolute constant can compare them; the working constant is
  `(2 + 2 |t|) / |b|` for the form `a X₀ + b X₁` with zero `t = -a/b`, and the proof splits at
  `|β| = 2 + 2 |t|`. The constant is then paid for by lowering the exponent, as in Layer 3.3.
* ⚠ **The choice of which form is small must be made at every absolute value of `K`, not on `S`.**
  Roth's theorem indexes its targets by an arbitrary `AbsoluteValue K ℝ`, so the `2 ^ |S|` split
  of Layer 3.4 needs `Function.extend` twice, and the two extensions compose only because no
  infinite place has the underlying absolute value of a finite place. That fact —
  `NumberField.InfinitePlace.val_ne_finitePlace_val`, proved from `v 2 = 2` against `v 2 ≤ 1` —
  is not in Mathlib and `README.md` had no occasion to name it.
* ⚠ **The line at infinity is a solution of 3.4 and cannot be dropped.** For the coordinate forms
  a point with `x i₀ = 0` makes one factor of `approxProd` vanish, so it satisfies the hypothesis
  for every `ε` and every height while lying on no line `K ⬝ (1, β)`. The conclusion of Layer 3.4
  is "finitely many points of `ℙ¹(K)`", never "finitely many `β ∈ K`", and the extra point is
  forced by the statement rather than an artefact of the proof.
* ⚠ **Moving targets enter Roth's proof twice, and the book names one of the two.** Its proof of
  6.5.2 says only (6.11), the height of the auxiliary polynomial, changes; the Taylor expansion
  at a place of `S` also carries `log⁺ |α_v|`, the `2 |S| max log⁺ |α_v|` inside the `C₂` of
  (6.19), and with moving targets it too must be `o(D)`. It is: an absolute value of `F` over a
  place of `K` is at most the height, `max |x|_w 1 ≤ H(x)`, which is Layer 0.1's classification
  and is now `NumberField.max_apply_one_le_mulHeight₁_of_liesOver_infinitePlace` and its finite
  twin. Mathlib has no single-place height bound at all.
* ⚠ **Layer 3.8 restructured 3.2 and changed nothing its consumers quote, but it did change a pinned
  shape.** The landed "Steps I and II" example below now takes one target *point* per place and one
  height constant per coordinate; Layer 2.6 had allowed target points all along. Roth's theorem,
  `NumberField.roth_no_chain` and every consumer are unchanged, and the core of the proof is
  `NumberField.roth_no_moving_chain`, of which `roth_no_chain` is the constant case.
* ⚠ **Layer 3.8 counts indices, not values, and its `1 +` is load-bearing.** A sequence may repeat
  a pair: without the `1`, the constant pair `(0, 0)` satisfies `0 = o(0)` and is a solution at
  every index. And a solution equal to one of its own targets — which with moving targets may
  happen infinitely often — is classified by 3.7's `NumberField.approxClass` into a corner, not
  discarded as in 3.2.
* ⚠ **Layer 4.1's finite-place covolume is exact in the value group, and Bombieri–Gubler's Lemma
  7.5.7(b) is not.** The book gives the `v`-adic volume as `|Δ_v|⁻¹ Q ^ (d ∑ c)`, an equality only
  when every `Q ^ c v i` is a value of `v`. The covolume of the lattice is exact in `a v i`, the
  largest value of `v` at most `Q ^ c v i` (`NumberField.FinitePlace.floorValue`), and at the
  `2`-adic place of `ℚ` with `Q ^ c = 3/2` it is `1` where the book's formula gives `2/3`. The
  error is a factor at most `∏_{v ∈ Sfin} N 𝔭_v ^ #ι`, so the comparison with `Q` to the weight
  is two-sided with constants, as the roadmap said; the upper bound, the one 4.3 uses, is exact.
* ⚠ **The index of a lattice cut out by local conditions is read from maximal determinants.** For
  a finitely generated `𝓞 K`-module `Λ ⊆ Kⁱ` spanning `Kⁱ`, `covol Λ = (∏ᶠ v, B v)⁻¹ covol (𝓞 K)^#ι`
  with `B v` the largest value of `v` on the determinants of tuples of `Λ`
  (`Submodule.covolume_mixedImage`). A pseudo-basis enters only its proof; the caller computes
  `B v` from the local conditions — the ultrametric Leibniz bound, attained by one vector per
  coordinate moved into `Λ` by an algebraic integer that is a unit at `v`. No localization, no
  quotient and no index appears.
* ⚠ **Mathlib's instance search does not find the Borel structure or the Haar property of the
  volume on `ι → mixedSpace K`.** It finds each factor's instance, but not the `∀ i`-family the
  product instances ask for; `NumberField.mixedEmbedding.instBorelSpacePi` and
  `NumberField.mixedEmbedding.instIsAddHaarMeasurePi` supply them once. The ambient of Layer 4 is
  `ι → mixedSpace K`, where `normAtPlace` lives, and not `ArithmeticHeights`' euclidean
  `mixedPi K ι`; the geometry of numbers of `ArithmeticHeights` 4.1, 4.2 and 4.4 is stated for any
  normed space and applies there directly.
* ⚠ **Layer 4.2's minima are indexed from `0`, and `Λ` enters only as a lattice.** The roadmap's
  `μ l`, `l = 1, …, n + 1`, is `NumberField.successiveMinimum Λ B (l - 1)`, as for
  `ZLattice.successiveMinimum`. Below `#ι` the admissible dilations are nonempty because the
  extraction lemma of `ArithmeticHeights` 4.4 turns the vectors realizing the real minima into
  `#ι` vectors of `Λ` independent over `K`, so every statement takes `Λ` through
  `[DiscreteTopology Λ.mixedImage]` and `[IsZLattice ℝ Λ.mixedImage]` alone, with no hypothesis
  that it spans `Kⁱ`.
* ⚠ **Attaining the minima over `K` needs no greedy minimality.** Each minimum is attained by
  finiteness — a dilate of a bounded body holds finitely many points of `Λ` — and one family
  realizing all of them is assembled afterwards by the selection step of the extraction lemma.
  Independence over `ℚ` reaches `ℝ` by base change in the coordinates of `latticeBasis`, through
  Mathlib's `linearIndependent_algebraMap_comp_iff`, not through the lattice.
* ⚠ **`c_K` is a house, and `c_ℚ = 1`.** The constant of `λ (d l) ≤ c_K μ l` is the largest house
  of a member of Mathlib's `integralBasis K` (`NumberField.integralBasisHouse`), and only this
  inequality — the lower half of Minkowski's second theorem over `K` — uses that the body is
  balanced over every completion. Over `ℚ` the basis is `± 1`, so in one variable both halves are
  equalities, `μ 0 · vol B = 2 · covol Λ`, which is the acceptance test.
* ⚠ **Layer 4.3's Lemma 7.5.12 is a statement about levels, not about solutions.** Bombieri–Gubler
  state `1 ≤ rank ≤ n` along the heights of a hypothetical infinite set of solutions, the lower
  bound because each solution lies in its own domain and "all but finitely many" by Northcott.
  What their proof shows about domains is `∀ᶠ Q in atTop, finrank K (approxSpan Sfin L c Q) < #ι`
  for negative weight, and that is what is stated; the rank of a domain can be `0`, and over `ℚ`
  with `c = -1` it is, past the level `1`, while at the level `1` it is still full.
* ⚠ **The rank is the number of minima at most `1`, and reading it needs attainment.** The count is
  `≤ 1`, not `< 1`: over `ℚ` with `c = 0` the domain `ℤ ∩ [-1, 1]` has rank `1` and minimum exactly
  `1`. That `μ i ≤ 1` yields `i + 1` independent points of the domain uses 4.2's attainment and the
  balancedness of the body; the statements hold for any lattice in any closed bounded symmetric
  convex body, and `V(Q)` is spanned by the vectors realizing the minima at most `1`.
* ⚠ **A bounded range of levels lies in one domain.** For `Q ∈ [Q₁, Q₂]` with `Q₁ > 0`, the domain
  of level `Q` lies in the domain of the exponents `|c|` at the level `max Q₂ Q₁⁻¹`, which is
  finite, so finitely many `V(Q)` arise. No Northcott is needed, and `Q₁ > 0` is.
* ⚠ **Layer 4.4's constant is chosen before the forms.** Bombieri–Gubler let the constant of
  Evertse's lemma depend on `K`, `S` and the forms, and 7.5.30 then applies the lemma to the forms
  `Q ^ (-c v i) L v i`, which move with `Q`. The proof gives a constant depending on `K` and `#ι`
  only, and `NumberField.exists_evertse` states `∃ C` before `Sfin`, the forms and the vectors.
* ⚠ **Layer 4.4's forms carry weights.** Over `K` the moving forms do not have coefficients in `K`,
  and at a finite place `Q ^ (-c v i)` is in general not a value of `v`, so rescaling would cost the
  factor `N 𝔭` and the exact finite bound. The lemma takes a weight `ν v i > 0` per form instead;
  the book's statement is `ν = 1` (`NumberField.exists_evertse_unweighted`), and 4.5 takes
  `ν v i = Q ^ c v i`.
* ⚠ **Approximation by `S`-integers needs neither completions nor the Chinese remainder theorem.**
  For targets in `K` the principal part at one finite place is written down from prime avoidance
  and a geometric sum, and a fundamental domain of `𝓞 K` in the mixed space handles the infinite
  places without disturbing the finite ones; the constant depends on `K` alone. The induction runs
  over any field whose places admit such an approximation, and one estimate serves both kinds of
  place. The constant at the infinite places cannot be `1`, even for real coefficients, and the
  minima must be sorted.
* ⚠ **Layer 4.5's exterior power is read in Plücker coordinates.** Layer 6.1 applies 4.2, 4.3
  and 5.6 to domains in `⋀^p Kⁱ`, and those layers live on `κ → K`; so the exterior power is
  `Set.powersetCard ι p → K`, the wedge of forms is a form there (`exteriorPower.wedgeForm`), and
  Laplace's identity is `ArithmeticHeights`' Cauchy–Binet. The wedges of independent forms are
  independent through a biorthogonal family; that their determinant is a power of `det (L v)` —
  the Sylvester–Franke theorem — is not needed, since the constants see only independence.
* ⚠ **Layer 4.5's Lemma 7.5.33 needs no pairing between `⋀^p` and `⋀^k`.** The span of the wedges
  meeting the first `k` indices is the kernel of the one wedge `f k ∧ ⋯ ∧ f (#ι - 1)` of the last
  coordinate forms (`exteriorPower.wedgeSpan_eq_ker`), and a vector lies in the span of the first
  `k` exactly when every wedge through it lies in that kernel, by Cramer's rule.
* ⚠ **Layer 4.5's wedge domain is an approximation domain whose exponents move with `Q`, and its
  weight is exact.** The book's `S(Q)` is `approxDomain` with the exponents
  `NumberField.wedgeExponent`, `logb Q` of its bounds; `Q` to its weight is `Q ^ (e w)` times
  `(C ^ M (∏ μ) ^ e μ (k - 1) / μ k) ^ d`, and Minkowski's upper bound leaves
  `(μ (k - 1) / μ k) ^ d` (`NumberField.rpow_approxWeight_wedgeExponent_le`), the form 6.1 needs
  after rounding the exponents to a grid. The choice of `k` needs rank `≥ 1`, and any `k` whose
  jump is at least the geometric mean will do.
* ⚠ **Layer 5.1's unit normalization is balanced, and its constant does not depend on `n`.** Lemma
  7.5.4 asks the `S₀`-unit `u` to make the affine height of `u • x` at most `h(x) + C₀`. The book
  picks one nonzero coordinate and bounds it from below at every place of `S`; here the target of
  the lattice approximation is the trace-zero vector `(mult v / D) h(x) - mult v log |x|_v`, so
  every place is handled at once and no coordinate and no distinguished place is chosen. The
  statement quantifies over the index type **after** the constant, which is the book's "depending
  only on `S` and `K`".
* ⚠ **Layer 5.1's Corollary 7.5.5 needs no independence of the forms.** The book compares
  `h_aff(L v (x))` with `h_aff(x)` in both directions, which uses independence; only the upper
  bound is needed, and it is the height of the single number `L v i x` against the affine height
  of `x` (`ArithmeticHeights` 0.5). The two-sided bound on `log v (L v i x)` is then the
  fundamental inequality of Layer 0.4 at one place, the book's (7.19).
* ⚠ **Layer 5.1's approximation classes are cells of a cube, and reuse nothing from Layer 3.1.**
  Layer 3.1's cells index points of the unit **simplex**, because in Roth's theorem every local
  factor is at most `1`; at 7.5.6 the exponents `log v (L v i y) / log H(x)` have both signs and
  are only bounded, so the classes are the cells of edge `1/N` of the cube `[-2, 2]`, as the book
  says, and their finiteness is that of a set of functions with finite support and values in a
  finite grid. The book's pigeonhole along an infinite sequence of solutions is not needed either:
  the statement is parametric in the solution.
* ⚠ **Layer 5.2's chain rule is the whole content of its vanishing statement.** The expansion
  coefficient `a(L v; J; I)` is *not* `binom (J + I) I · a(L v; J + I; 0)`: Bombieri–Gubler
  differentiate in the original coordinates and expand in the transformed ones, so a coefficient
  of `∂_I P` is a combination, over all orders with the same block degrees, of coefficients of `P`
  read in the transformed coordinates. `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero` proves
  what is needed by induction on the order and never names that combination. It needs
  characteristic zero, because `hasseDeriv_comp` produces a positive integer factor to invert.
* ⚠ **Layer 5.2's volume computation is avoidable, and so is most of its "sufficiently large".**
  The exponential moment of the exponent of one variable is exact on the lattice — the uniform
  distribution on the monomials of degree `N` in `n + 1` variables has `E[j i] = N/(n+1)` and
  `E[binom (j i) 2] = N(N−1)/((n+1)(n+2))`, two binomial identities — and `exp (−t) ≤ 1 − t + t²/2`
  turns them into the book's bound with one explicit error term `λ²/(2N(n+1))`. The book's
  restriction `0 < λ ≤ n + 4` disappears, and `d` has to be large only to make that term small.
* ⚠ **Layer 5.2's hypothesis on `m` is strict.** The book asks
  `m ≥ 4 log (2 (n+1) |S|) / ((n+1)(n+2) η²)`, which leaves no room for that error term; the
  strict inequality creates a positive slack and `D₀` is chosen against it. Replacing
  `2 (n+1) |S|` by `4 (n+1) |S|` and keeping `≥` would do the same. ⚠ And `C₂`, `C₃` are allowed
  to depend on `m`, `S` and `η` here: the `m`-dependence is the `O(log d)` term
  `log #multiMons d`, and Layer 5.6 fixes `m` before it uses `C₂`.
* ⚠ **The upper half of Layer 5.2's interval is free.** A Hasse derivative of a multihomogeneous
  polynomial is multihomogeneous of multidegree `d h − ∑ i, I (h, i)`, so a nonzero coefficient
  has `∑ i, ∑ h, J (h, i) / d h = m − ∑ h, (∑ i, I (h, i)) / d h`. If one exponent exceeds
  `m/(n+1) + 2 n m η` the remaining `n` average below `m/(n+1) − 2 m η`, and the lower half
  applies to one of them; `n ≥ 1` is load-bearing here as well as in the moment identity.
* ⚠ **Layer 5.3's index is a weighted order, and the ideal of Definition 7.5.17 is mentioned
  twice.** Solving `M h = X (h, i₀ h)` for one coordinate at which the form survives turns
  `I(t; d; M)` into a **monomial** ideal, and membership in a monomial ideal is a condition on
  each monomial separately. So the index along the forms is the weighted order of Layer 2.3 in
  the transformed coordinates, for the weights that see only the coordinates `i₀ h` — a weight of
  `0` elsewhere, which `MvPolynomial.weightedOrder` allows and which makes those variables
  invisible rather than infinite. Only the *definition* keeps the ideal, because that is what
  makes the index visibly independent of the choice of `i₀`.
* ⚠ **Layer 5.3's variables have to be specialized one at a time.** Bombieri–Gubler divide out
  the largest power of one variable, set it to `0`, and repeat; taking the componentwise minimum
  of the exponents and slicing once instead does not work, because `X 1 + X 2` has no monomial in
  which both exponents are minimal. The composite of the steps is a single slice, at an exponent
  no direct formula produces. ⚠ And the forms must be truncated as the variables are dropped:
  setting a variable to zero commutes with the change of coordinates only after the coefficient
  of the form at that variable has been set to zero as well.
* ⚠ **Only half of Layer 5.3's specialization claim is proved, and it is the half that is
  needed.** The book asserts that the specialization leaves the index unchanged, which needs the
  uniqueness of the decomposition in powers of the forms; what Lemma 7.5.19 consumes is that the
  index does not *decrease*, and that needs nothing beyond the monomial-by-monomial description
  of the ideal. ⚠ The book's "partial degrees at most `d`" has to be read as multihomogeneity of
  multidegree at most `d`: the dehomogenization is injective on monomials only because of the
  multidegree, and without it the index can jump — `x₁ + x₀² − x₀` is not divisible by `x₁`,
  while its dehomogenization at `x₀ = 1` is `t`.
* ⚠ **Layer 5.3's second kept coordinate need not be one where the form survives.** The book
  arranges `b (j 1) ≠ 0` so as to have a genuine point `ξ j = −b (j 0) / b (j 1)`; here the point
  is `−M h (i₁ h)` whatever that is, and the hypothesis on the heights passes to Layer 2.7
  verbatim. The case `M h (i₁ h) = 0` cannot occur under that hypothesis, and the proof never has
  to know it. ⚠ The factor `n` in the book's bound for the restricted form is the multiplication
  table: after normalizing one coordinate to `1`, the tuple of ratios is a re-indexing of the
  tuple of all products of subsets, whose height is the product of the heights of the pairs.

* ⚠ **Layer 5.4's bound on the height of a wedge value is not the book's, and the book's is
  false.** Bombieri–Gubler bound `h(L̂ (v i) (w))`, the height of a single number, by
  `h(V(Q)) + C₇`; the left-hand side changes when `w` is rescaled and the right-hand side does
  not, and over `ℚ` the vector `w = (N, 0)` has `h(V) = 0` and `h(w 0) = log N`. What Step III
  needs, and what is true, is a product-formula inequality between the **local factor** of the
  point and its **projective** height (`NumberField.InfinitePlace.iSup_mul_iSup_pow_mult_le`).
  It is also stronger: summing it over `S` costs `|S| - 1` powers of `h(V(Q))` and not `|S|`.

* ⚠ **Layer 5.4 has one exceptional subspace per pattern, not one exceptional subspace.** The
  book writes "there is a linear space `W`, independent of `Π(Q)` and `ε`"; its proof fixes one
  solution of a system that depends on the pattern — which indices survive at which place — and
  the pattern moves with `Q`. What is true is that there are finitely many patterns and hence
  finitely many exceptional subspaces, which is all Step IV consumes.

* ⚠ **Layer 5.4's exceptional system is an intersection of spans of coefficient vectors.** Read
  in the original coordinates, `L̂ (v i) (w) = 0` for `i` outside the pattern says that `w` lies
  in the span of the coefficient vectors of the forms the pattern names
  (`NumberField.patternSpace`). No Hodge star, no adjugate and no Laplace expansion of an
  `(n+1) × (n+1)` determinant appears anywhere in Layer 5.4, and the estimate reads its
  coefficients off that description.

* ⚠ **Layer 5.4's chosen exceptional vector has to be scaled into the integers.** A nonzero
  vector of a pattern space becomes integral at every finite place after multiplication by a
  common denominator, and only then is the product formula confined to `S`. Scaling changes
  neither the kernel nor the pattern, so nothing else is re-proved. ⚠ `n ≥ 1` is **not** needed:
  in rank `0` the pattern is full, the weight along the chosen index is the weight of the
  exponents, and every level falls in the exceptional branch.

* ⚠ **Layer 5.5's one-variable grid lemma is a count of roots, not a divisibility.** Bombieri
  and Gubler argue that a polynomial of degree at most `e` cannot be divisible by
  `(∏_{|b| ≤ B} (x − b)) ^ (e/B + 1)`; an induction on the variables applies that over a
  polynomial ring in the remaining ones, where it needs the factors to be pairwise coprime.
  Counting roots **with multiplicity** — which `Polynomial.roots` already carries — needs no
  coprimality and no unique factorization, and the whole lemma is then the inequality
  `(2B + 1) (e/B + 1) > e`.

* ⚠ **Layer 5.5 needs no chain rule, and the induction on the variables needs no substitution.**
  The book reads the derivative in the parameters back through the parametrization by the chain
  rule; what the argument consumes is only which orders can occur, and that is multihomogeneity:
  the parametrization preserves the degree in each block. The two evaluations become two
  coefficient extractions from the same shifted polynomial
  (`MvPolynomial.coeff_shift`, `MvPolynomial.shift_linSubst`). Likewise the induction carries
  "does not vanish identically on the affine subspace where the variables already handled sit at
  their grid values", so no Hasse derivative ever has to be commuted past a partial substitution.

* ⚠ **Layer 5.6 needs no chain rule either, for the third time.** Layer 5.3 measures the index
  in the coordinates in which the forms are the variables, Layer 5.5 wants a derivative in the
  original ones, and the change of coordinates **is** a block-wise linear substitution
  (`MvPolynomial.substFormInv_eq_linSubst`). Layer 5.5's own transport lemmas then carry a
  surviving coefficient between the two systems with the same degree in every block, which is
  exactly what makes the two weighted orders agree.

* ⚠ **Layer 5.6 needs two invariants of the system of exponents, not one.** Besides
  `NumberField.approxWeight`, which is negative, Step VI needs `NumberField.approxAbsWeight`,
  the weight of the `|c v i|`. It is the quantity the parameter `η` is chosen against, and it is
  the only place in the whole development where the size of the exponents rather than their sum
  enters.

* ⚠ **Layer 5.6 uses that `S` contains every archimedean place, and uses it exactly once.**
  Away from `S` the local bound of Step VI carries no constant and the point is integral, so the
  product formula is applied with `Sinf = univ`. This is the convention of Layers 4 and 5.4, and
  it is what makes the reference family of the estimate finite.

* ⚠ **Layer 6.1 needs no pigeonhole and no subsequence.** Bombieri–Gubler argue along an
  unbounded family of levels and extract a subfamily on which `k` and the rounded exponents of the
  wedge domain are constant. Neither is needed: the rounding is a **function** of the level
  (`NumberField.roundExponent`), its range is finite because the exponents stay in a box, and the
  finite set of subspaces is the union over that range. Layer 3.1's cells are not used, and
  neither is any infinite set of solutions.

* ⚠ **Layer 6.1's penultimate rank is not a separate case.** The book treats rank `#ι - 1` by
  Theorem 7.5.13 directly and the lower ranks by the exterior power. Here rank `#ι - 1` is the
  case `k = #ι - 1`, `p = 1` of the same construction — the wedge domain in `⋀^1 Kⁱ` is the
  domain re-indexed by the one-element subsets — so one mechanism covers every rank from `1` to
  `#ι - 1`, and Layer 5.6 is applied only through it.

* ⚠ **Layer 6.1 needs the minima confined between `Q ^ (-B)` and `Q ^ B`, and Layer 4.2 does not
  give it.** Minkowski's second theorem over `K` bounds the *product* of the minima from both
  sides, which bounds the first from above and the last from below — the two useless directions.
  The missing bound is the product formula: a nonzero point of `Λ ∩ t B` has height at least `1`
  and at most a constant times `t ^ d` times `Q` to the sum of the largest exponents, so `t` is at
  least a fixed negative power of `Q` (`NumberField.exists_pos_forall_rpow_le_successiveMinimum`).
  The upper bound then follows from Minkowski's.

* ⚠ **Layer 6.1 returns subspaces that contain the spans, not the spans.** `T` collects the spans
  of the first `k` minimal vectors, which contain `V(Q)`; whether the `V(Q)` themselves are finite
  in number is not claimed, and Layer 6.2 does not need it.

* ⚠ **Layer 6.2 is Layer 5.1 and Layer 6.1 and nothing else.** The Subspace Theorem over `K` adds
  no analysis to the two layers below it: Layer 5.1 turns the inequality, for a solution of large
  height, into membership in one of finitely many approximation domains of negative weight, Layer
  6.1 covers each of those by finitely many proper subspaces, and what is left is the solutions on
  the kernel of a form and the solutions of small height. One file, `…/SubspaceTheorem.lean`,
  and one theorem.

* ⚠ **Layer 6.3 is the Galois closure and nothing else.** Bombieri–Gubler's Remark 7.2.3 is the
  whole proof: pass to the Galois closure `E / K`, extend the chosen absolute value over each `v`,
  and put at every place of `E` above `v` the conjugate of the system at `v` under the
  automorphism that moves the chosen absolute value there. A point of `Kⁱ` is fixed by those
  automorphisms, so it sees the *same* local factor at every place above `v`, and the local
  degrees sum to `[E : K]` — the same degree by which the height grows. The transfer is therefore
  an **equality**, not an inequality (`NumberField.approxProd_conjSystem`).

* ⚠ **Conjugation and base change are one operation.** A linear form on `Fⁱ` is its vector of
  coefficients, so any ring homomorphism `f : F →+* E` carries it
  (`Module.Dual.compRingHom`); the base change is `f = algebraMap F E`, the conjugation is
  `f = σ`, and a conjugated base change is the single homomorphism `σ ∘ algebraMap F E`. No
  semilinear map and no tensor product appears in Layer 6.3. That independence survives the
  carrying is a determinant statement — the family is square, so independence is invertibility of
  the coefficient matrix and `RingHom.map_det` does the rest.

* ⚠ **Mathlib's finite places are normalized, and Layer 0.2 is not about them.** A finite place of
  `E` above a finite place `v` of `K` restricts to `v ^ (e f)`, not to `v`, so it is not an
  absolute value over `v` and Layer 0.2's orbit statement does not apply to it directly; its
  `(e f)`-th root is, and that root is an absolute value only because the place is nonarchimedean
  (`AbsoluteValue.nonarchRpow`). The `(e f)` then cancels against
  `NumberField.FinitePlace.sum_localDegree` exactly as `mult` cancels against
  `NumberField.InfinitePlace.sum_mult`, which is why both halves produce the same exponent.

* ⚠ **Layer 6.2's small-height solutions are collected as lines, not as points.** There is no
  Northcott property for `Height.mulHeight` on tuples — a whole line sits at one height — so the
  finitely many solutions below the threshold of Layer 5.1 do not exist; what is finite is the set
  of *projective* points, and each contributes the line it spans
  (`Projectivization.finite_setOfPred_mulHeight_le`, `ArithmeticHeights` 1.1). This is where
  `[Nontrivial ι]` earns its keep: a line is proper only for `2 ≤ #ι`, and at `#ι = 1` the theorem
  is false, the solutions being the roots of unity of `K`.

* ⚠ **Layer 6.4 is Layer 6.3 plus the `S`-part of the height, and no new estimate.** The affine
  inequality drops the `#ι` local denominators of `approxProd`; their product over the infinite
  places and `S` is exactly the part of the height that those places carry, so `affineProd` is
  `approxProd` times that part to the power `#ι`, and the exponent `-ε` of Corollary 7.2.5 does
  the work of the `-#ι - ε` of Theorem 7.2.2. Nothing is estimated anywhere in the passage.

* ⚠ **`S`-integrality suffices in one direction and does not suffice in the other.** At an
  `S`-integral point the `S`-part of the height can *exceed* the height — the factor lost at a
  place of `S` that the coordinates do not fill — so the affine inequality is the stronger of the
  two, which is the direction the milestone needs. The converse has to normalise to an
  `S`-primitive point, where Layer 0.3 makes the two equal. That asymmetry is why Bombieri–Gubler
  state Corollary 7.2.5 for `S`-integers and Theorem 7.2.6 for primitive points.

* ⚠ **The converse enlarges three things at once, one per layer below it.** Every infinite place
  has to be present and every finite place outside `S` harmless, which is Layer 5.1's coordinate
  forms; `S` has to be large enough for a primitive multiple to exist, which is Layer 0.3's
  localisation; and `w` has to be defined and to lie over `v` at the added places, which is Layer
  0.1's fibre. The last is why the converse returns a *new* family `w'` rather than reusing `w`:
  the affine statement asks for an absolute value of `F` at **every** infinite place, and the
  projective one only on `Sinf`.

* ⚠ **Layer 6.5 is one local observation and one partition, and no new arithmetic.** At a place
  where the forms are in general position, the `#ι` *smallest* values at a point come from
  linearly independent forms — that is what general position says — and the discarded values are
  bounded below, because the chosen forms are a basis and a basis bounds the coordinates. So the
  local factor of the chosen system is within a constant of the local factor of the whole family,
  and Layer 6.3 finishes. The families of fewer than `#ι` forms are the opposite case: there the
  family is independent outright and is *completed* by coordinate forms, whose factors are at most
  `1`, so the completion costs nothing.

* ⚠ **The two cases cannot be merged.** A family extended by the coordinate forms is not in
  general position — one of its members may already be a coordinate form — so "take the `#ι`
  smallest" is wrong for the extended family. Steinitz is used in the small case and the ordering
  argument in the large one, and neither covers the other.

* ⚠ **The chosen system has to range over a `Fintype`, and that is what fixes the signature.**
  The forms are `L : AbsoluteValue K ℝ → κ → Dual F (ι → F)` with a `B : AbsoluteValue K ℝ →
  Finset κ` for their number at each place, rather than a family of index *types* `κ v`: the
  systems chosen at the places of `S` are index maps `ι → κ ⊕ ι`, and they have to form one finite
  type for the partition into classes to be finite. Nothing is lost — take `κ` large enough — and
  `κ` is required finite for this reason and for no other.

* ⚠ **The constant is removed by halving `ε`, so Northcott reappears.** Layer 6.3 is applied with
  `ε / 2`, and only above a height threshold; below it the solutions are finite in projective space
  and are collected as lines, exactly as in Layer 6.2. That is the second and last appearance of
  Northcott in the Subspace Theorem.

* ⚠ **Layer 6.6 is an equation between statements, and the converse needs nothing.** Layer 3.4 was
  stated for an arbitrary index type with `Fintype.card ι = 2` and with `approxProd`, the very
  quantity Layer 6.3 uses; the only difference between the two conclusions is that Layer 6.3 asks
  for `[Nontrivial ι]`, which `Fintype.card ι = 2` supplies. So "Layer 6.3 at `card ι = 2` is no
  stronger" is not an implication to be proved — the two are the *same* proposition — and the
  library checks it with `rfl`, which is available because proof irrelevance is definitional.
  Layer 6.5 specializes the same way, since general position for two forms in two variables is
  linear independence.

* ⚠ **On the projective line the Subspace Theorem is a count of points.** A proper subspace of a
  plane holds at most one point of `ℙ¹`, so the finitely many exceptional subspaces of Layer 6.3
  at `card ι = 2` pin finitely many *solutions* — and the count cannot be moved to tuples, since
  both sides of the inequality are invariant under scaling and every solution has infinitely many
  nonzero multiples.

* ⚠ **Roth's theorem comes back out of Layer 6, and the library carries one of it.** Layer 3.4's
  converse implication takes the Subspace Theorem as a hypothesis and uses nothing of Layer 3
  besides Northcott, so discharging it from Layer 6.3 gives a second proof of Roth's theorem over
  a number field. It is the same theorem as Layer 3.2's — `rfl` again — and the module graph does
  not record the independence, since `SubspaceAlgebraic.lean` reaches `RothTheorem.lean` through
  `ApproxProd.lean`, where the central quantity is defined.

* ⚠ **Layer 7.1 needs `α j ≠ 0` and nothing else of the coefficients.** The system fed to Layer
  6.3 is `∑ i, α i X i` together with the coordinate forms `X i` for `i ≠ j`, and it is linearly
  independent exactly when the displaced coefficient `α j` is nonzero, whatever the others do.
  Linear independence of the `α i` over `ℚ` is never used, which is Bombieri–Gubler's Remark
  7.3.3 made visible.

* ⚠ **The exponent drops by one for free, and `mulHeight x ≤ max |x i|` is the whole of it.** The
  `n` coordinate forms contribute at most `M ^ n` against the denominator `M ^ (n+1)` of the
  central quantity, so what is left is `‖∑ α i x i‖ / M`; the Subspace Theorem's exponent
  `-(n+1) - ε` is then reached from `-n - ε` by the single inequality that the height of an
  *integer* point is at most its sup norm. That inequality is false for rational points — the
  height of `(1/2, 1/3)` is `3`, its sup norm `1/2` — and it makes the statement proved here
  **stronger** than the
  classical one, which reads the exponent against `max |x i|` rather than against the height.

* ⚠ **The induction eliminates a variable and reserves no room.** A proper subspace lies in the
  kernel of a nonzero form `∑ c i X i`; dropping a coordinate `k` with `c k ≠ 0` turns
  `∑ α i x i` into `∑ i ≠ k, (α i - α k c i / c k) x i`, whose coefficients are again algebraic.
  The restriction is injective on the subspace and does not raise the height, and the exponent
  weakens by exactly one when the number of variables drops by one, so the same `ε` serves at
  every step. The reduced index type is the subtype `{i // i ≠ k}`, never `Fin n`, and the
  recursion runs on `Fintype.card ι ≤ n` so that ordinary induction suffices.

* ⚠ **One variable is where the theorem degenerates.** Layer 6.3 is unavailable at
  `card ι = 1` — it asks for `[Nontrivial ι]` — and unnecessary: the height of a one-coordinate
  point is `1` by the product formula, so the inequality reads `‖α j‖ * |x j| ≤ 1` and bounds
  `x j` outright. The case where every `α i` vanishes has to be separated as well, since the
  Subspace step needs some `α j ≠ 0`.

* ⚠ **Layer 7.2 counts polynomials first, and has to.** The approximants `ξ` are bounded in
  number only through their minimal polynomials: a bounded set of complex numbers is not finite,
  while the integer polynomials of bounded degree and bounded naive height are, which is how the
  constant of the mean value theorem is disposed of. `‖f_ξ(α)‖ ≤ C * H ^ (-D - ε)` becomes
  `‖f_ξ(α)‖ ≤ H ^ (-D - ε/2)` as soon as `H ≥ C ^ (2/ε)`, and below that height Northcott's
  theorem for integer polynomials finishes the count. Bombieri–Gubler's "a familiar argument
  already used at the end of Example 7.2.7" is that paragraph.

* ⚠ **The mean value theorem had to be proved again over `ℂ`.** Layer 1.3's real one runs on
  `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` over `Set.uIcc`, and there is no interval
  between two complex numbers. The telescoping identity
  `z ^ k - w ^ k = z * (z ^ (k-1) - w ^ (k-1)) + w ^ (k-1) * (z - w)` gives the same constant
  `(n+1) ^ 2 * H(P) * max 1 (max ‖z‖ ‖w‖) ^ n` with no analysis at all, and the proof is shorter
  than the real one.

* ⚠ **The conjugates of `α` are the one family Layer 7.1 cannot see, and rigidity disposes of
  them.** Layer 7.1 asks for `0 < ‖∑ α ^ i x i‖`, which fails exactly when the minimal polynomial
  of the approximant vanishes at `α` — that is, when the approximant is a conjugate of `α`. Two
  primitive irreducible integer polynomials with a common root are associated, so those
  approximants are the roots of *one* polynomial and its height is a bound the Northcott branch
  already carries. That rigidity lemma is Layer 1.3's, stated there for a real root; it holds
  over any `ℚ`-algebra that is a domain, and Layer 7.2 generalized it in place rather than
  restating it.

* ⚠ **In the language of Layer 1.3, Layer 7.2 is `w_n^*(α) ≤ n` for algebraic `α`.** That is one
  of the two upper bounds Layer 7.3 asks for — the other, `w_n^* ≤ deg α - 1`, is Liouville's
  inequality and is landed in Layer 1.3 — and the library states it under that name as well.

* ⚠ **Layer 7.3's missing bound is Layer 7.2's proof with its first step deleted.** The only
  thing Layer 1 could not supply is `w_n(α) ≤ n`; it is Layer 7.1 applied to `1, α, …, α ^ n` and
  to the coefficient vector of the polynomial directly, with no mean value theorem in front of
  it. Everything else in the identity `w_n = w_n^* = min n (deg α - 1)` is assembly: Liouville's
  inequality for `≤ deg α - 1`, the box principle for the lower bounds, and Wirsing's third
  inequality — at the value the box principle forces — to carry them from Mahler's exponent to
  Koksma's. The conjugates of `α` cost nothing here, because `Real.mahlerSet` asks for a nonzero
  value in its definition, and with them go the rigidity lemma and the threshold height that
  Layer 7.2 had to carry.

* ⚠ **Schmidt's exponents are read against the product `∏ i, |q i|`, not against the sup norm.**
  For a tuple with no vanishing coordinate the product is at least the sup norm and can be very
  much smaller than its `n`-th power, so Layer 7.1's `Rat.approxProd_projWithSum_le`, which
  bounds the coordinate forms by `M ^ n` and keeps only the one nontrivial form, throws away
  exactly what these theorems are about. What Layer 7.3 needed instead is the Subspace Theorem
  over `ℚ` with the hypothesis on the bare product of the values of a full system of forms, and
  that is `Rat.exists_finset_submodule_of_prod_le`. The hypothesis that no coordinate vanishes is
  then unremovable: with one the product is `0` and the inequality is free.

* ⚠ **Two theorems, two inductions, and one of them feeds the other.** The linear form theorem
  eliminates one variable on each exceptional subspace and recurses. The theorem on
  `∑ i, q i * α i` has one variable more — the numerator — and its exceptional subspaces split in
  two: a relation that does not involve the numerator eliminates one `q` and is the recursion,
  while a relation that does involve it *determines* the numerator, and then the distance to `ℤ`
  is a linear form with algebraic coefficients, which the first theorem finishes.

* ⚠ **Simultaneous approximation needs no induction at all.** One exceptional subspace already
  bounds `q`: its relation `c₀ q + ∑ i, c i p i = 0` with `p i = q α i - θ i`, `|θ i| ≤ 1/2`,
  gives `q (c₀ + ∑ i, c i α i) = ∑ i, c i θ i`, and the left factor is nonzero *because*
  `1, α 1, …, α n` are independent over `ℚ`. That is the one place where the independence
  hypothesis is used as a nonvanishing statement rather than as an invariant of a recursion.

* ⚠ **The distance to the nearest integer is written as an existential over the numerator.** The
  numerator *is* a coordinate of the integer point the Subspace Theorem is applied to, so the
  existential is what the proof produces; `Real.abs_sub_round_le` — the nearest integer is
  nearest, which Mathlib does not state — says the two readings cut out the same set.

* ⚠ **Layer 7.4 needs no induction on the subspace.** The roadmap's route ends in "an induction on
  the subspace that uses non-periodicity"; what the proof found is one subspace and two cases. An
  equation `z 0 X + z 1 Y + z 2 Z = 0` holding at infinitely many points
  `(b ^ (r + s), b ^ r, p)` either does not involve `Z`, and then reads `z 0 b ^ s + z 1 = 0`,
  which holds for at most one `s`; or it does, and then the approximation turns into
  `|θ b ^ s + η| ≤ 1` with `θ = ξ + z 0 / z 2`, which forces `θ = 0`: `ξ` is rational.
  Non-periodicity is used exactly once, as the irrationality of `ξ`, and
  `Real.irrational_ofDigits` proves that without any uniqueness of expansions — the tails of the
  given digits satisfy `b T k = a k + T (k + 1)` and take finitely many values.

* ⚠ **Layer 7.4 went back to Layer 6 for the finite places.** Layer 7.3's Subspace step lives at
  `∞` alone; the criterion's gain is at the primes of `b`, where the first two coordinates of the
  point have size `b ^ (-(2 r + s))`. Without them the product is small only for
  `w > 2 + 2 r / s`. `Rat.exists_finset_submodule_of_prod_mul_prod_padicNorm_le` is the step with
  coordinate forms at a finite set of primes, and 7.3's step is its case `S = ∅`.

* ⚠ **The weaker criterion puts the primes of `b` on the denominator: `S₂`, not `S₁`.** The
  roadmap's prose had them the other way round. Ridout's theorem sees the approximant in lowest
  terms, and reducing may remove primes of `b` from its denominator — exactly the ones carrying the
  gain. What saves it is that the part of the denominator prime to `b` does not grow along
  divisors (`Rat.mul_prod_padicNorm_le_of_dvd`), so it stays below `b ^ s`.

* ⚠ **`1 ≤ |V k|` is Ridout's hypothesis and not the Subspace Theorem's.** The three-variable
  route never divides by `b ^ s - 1`, and strict monotonicity of `|V k|` is all it uses; the
  `w > 2` route needs `b ^ s - 1 ≠ 0`. `Function.IsStammeringWith.exists_periodic` supplies both,
  after dropping the first repetition.

* ⚠ **Layer 7.5's pigeonhole needs its period re-cut, and then needs no case split.** Two equal
  factors of length `n` at positions `r < t ≤ C n` give period `s = t - r` on a segment of length
  `n + s`; for small `s` the ratio `r / s` is unbounded. Replacing `s` by its multiple
  `P = (⌊n / 2 s⌋ + 1) s ∈ (n / 2, n / 2 + s]` gives `r ≤ 2 C P` and the exponent
  `1 + 1 / (1 + 2 C)` at once. And the theorem feeds 7.4's *working form*, not its definition:
  stammering is only the name of what the lemma proves.

* ⚠ **Layer 7.5's two hypotheses are one.** 7.4 needed only "not eventually periodic ⟹
  irrational"; the converse (`Real.irrational_ofDigits_iff`, for `b ≥ 2`) is a fixed point of
  `T ↦ (P + T) / b ^ p` on the tails, and lets the theorem be stated for an algebraic irrational
  as the roadmap states it.

Every height below is Mathlib's **relative** height over the fixed number field, the local factor
at an infinite place carries the exponent `InfinitePlace.mult`, and a finite set of places is a
pair of **typed** finsets, `Sinf` and `Sfin`. `README.md` writes them `S∞` and `S₀`; `S∞` stops
being an identifier as soon as `ENNReal`'s notation `∞` is open, which it is wherever an
approximation exponent is in sight. `README.md` explains why each of these choices is forced; in
particular the Subspace Theorem stated for a `Finset (AbsoluteValue K ℝ)` with no hypothesis on
its members is false.
-/

namespace TauCetiRoadmap.DiophantineApproximation

open Height NumberField Module Polynomial IsDedekindDomain
open scoped ENNReal NNReal

noncomputable section

/-! ## Layer 0: places above places

### Layer 0.1 — landed

The three signatures below are discharged by `DiophantineApproximation/PlacesOver.lean` and its
two halves. They are kept as `example`s, not deleted, because they are the contract: a change in
the library that broke any of them would break this file. -/

section PlacesOver

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- **Layer 0.1, landed.** An absolute value of `F` over an infinite place of `K` is the absolute
value of an infinite place of `F`. -/
example (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : ∃ w' : InfinitePlace F, w'.1 = w :=
  NumberField.exists_infinitePlace_eq_of_liesOver v w

/-- **Layer 0.1, landed.** An absolute value of `F` over a finite place of `K` is a positive power
of the absolute value of a finite place of `F`. `README.md` pins the exponent as `(e * f)⁻¹`; it is
at most `1`, and it is `1` exactly when the prime is unramified of inertia degree one, so `w` is in
general **not** itself a `FinitePlace F`. -/
example (v : FinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] :
    ∃ (P : HeightOneSpectrum (𝓞 F)) (t : ℝ), 0 < t ∧ t ≤ 1 ∧
      ∀ y : F, w y = FinitePlace.mk P y ^ t :=
  NumberField.exists_finitePlace_rpow_eq_of_liesOver v w

/-- **Layer 0.1, landed.** Above every place there is an absolute value, and only finitely many. -/
example (v : AbsoluteValue K ℝ)
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) :
    {w : AbsoluteValue F ℝ | w.LiesOver v}.Finite ∧
      {w : AbsoluteValue F ℝ | w.LiesOver v}.Nonempty :=
  NumberField.finite_nonempty_setOf_liesOver v hv

/-- **Layer 0.1, landed, sharp form.** The exponent is `(e f)⁻¹` and the prime lies over the prime
of `v`. This is what `README.md` pins and what the bound `t ≤ 1` above is deduced from. -/
example (v : FinitePlace K) (w : AbsoluteValue F ℝ) [w.LiesOver v.1] :
    ∃ P : HeightOneSpectrum (𝓞 F), P.asIdeal.LiesOver v.maximalIdeal.asIdeal ∧
      ∀ y : F, w y = FinitePlace.mk P y ^
        (((P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) : ℕ) : ℝ))⁻¹ :=
  NumberField.exists_finitePlace_rpow_inv_eq_of_liesOver v w

/-- **Layer 0.1, landed.** `w` is nonarchimedean exactly when `v` is finite — the second of the
three things the roadmap asks for beside the classification. -/
example (v : AbsoluteValue K ℝ) (hv : IsInfinitePlace v ∨ IsFinitePlace v)
    (w : AbsoluteValue F ℝ) [w.LiesOver v] :
    IsNonarchimedean (w : F → ℝ) ↔ IsFinitePlace v :=
  NumberField.isNonarchimedean_iff_isFinitePlace v hv w

/-- **Layer 0.1, landed.** Every `w` over `v` extends to every further number field — the third. -/
example (v : AbsoluteValue K ℝ) (hv : IsInfinitePlace v ∨ IsFinitePlace v)
    (w : AbsoluteValue F ℝ) [w.LiesOver v]
    {F' : Type*} [Field F'] [NumberField F'] [Algebra F F'] :
    ∃ w' : AbsoluteValue F' ℝ, w'.LiesOver w :=
  NumberField.exists_liesOver_of_liesOver v hv w

end PlacesOver

/-! ### Layer 0.2 — landed

Conjugate absolute values and the local extension formula, discharged by
`DiophantineApproximation/ConjugatePlaces.lean` and `DiophantineApproximation/LocalExtension.lean`.
The finite half of the local extension formula was already in Mathlib per place and is consumed,
not rebuilt; what is new is the product over the places above `v`, the whole infinite half, and
the Galois transitivity. -/

section ConjugatesAndLocalExtension

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- **Layer 0.2, landed.** For `F / K` Galois the Galois group acts transitively on the absolute
values of `F` lying over a place of `K`. The action is `σ • w = w ∘ σ⁻¹`, on all of
`AbsoluteValue F ℝ`, extending Mathlib's action on `NumberField.InfinitePlace`. -/
example [IsGalois K F] (v : AbsoluteValue K ℝ) (hv : IsInfinitePlace v ∨ IsFinitePlace v)
    (w w' : AbsoluteValue F ℝ) [w.LiesOver v] [w'.LiesOver v] :
    ∃ σ : F ≃ₐ[K] F, σ • w = w' :=
  NumberField.exists_smul_eq_of_liesOver v hv w w'

/-- **Layer 0.2, landed.** The same, as the statement Layer 6.3 uses: the fibre over `v` is a
single orbit. -/
example [IsGalois K F] (v : AbsoluteValue K ℝ) (hv : IsInfinitePlace v ∨ IsFinitePlace v)
    (w : AbsoluteValue F ℝ) [w.LiesOver v] :
    {w' : AbsoluteValue F ℝ | w'.LiesOver v} = Set.range fun σ : F ≃ₐ[K] F => σ • w :=
  NumberField.setOf_liesOver_eq_range_smul v hv w

/-- **Layer 0.2, landed.** The local extension formula at the finite places, in product form. -/
example (v : FinitePlace K) (y : K) :
    ∏ w ∈ FinitePlace.placesOverFinset F v, w (algebraMap K F y) = v y ^ finrank K F :=
  FinitePlace.prod_apply_algebraMap v y

/-- **Layer 0.2, landed.** The local extension formula at the infinite places, in product form.
The exponent `InfinitePlace.mult` appears on both sides; over a complex `v` the right-hand side
is `v y ^ (2 * [F : K])`. -/
example (v : InfinitePlace K) (y : K) :
    ∏ w ∈ InfinitePlace.placesOverFinset F v, w (algebraMap K F y) ^ w.mult
      = (v y ^ v.mult) ^ finrank K F :=
  InfinitePlace.prod_apply_algebraMap_pow_mult v y

/-- **Layer 0.2, landed.** The two fundamental identities the products rest on. -/
example (v : FinitePlace K) (v' : InfinitePlace K) :
    (∑ w ∈ FinitePlace.placesOverFinset F v, w.localDegree K = finrank K F) ∧
      ∑ w ∈ InfinitePlace.placesOverFinset F v', w.mult = v'.mult * finrank K F :=
  ⟨FinitePlace.sum_localDegree v, InfinitePlace.sum_mult v'⟩

/-- **Layer 0.2, landed.** The per-place formula at a finite place, `𝔚 y = 𝔳 y ^ (e f)`. This is
Mathlib's `FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap` restated for places, as that
lemma's own TODO asks; Layer 0.1 already consumes it. -/
example (w : FinitePlace F) (v : FinitePlace K) [w.LiesOver v] (y : K) :
    w (algebraMap K F y) = v y ^ w.localDegree K :=
  FinitePlace.apply_algebraMap w v y

/-- **Layer 0.2, landed.** ⚠ `NumberField.FinitePlace.LiesOver` — the primes lie over each other
— is **not** `AbsoluteValue.LiesOver`. The two agree exactly when the local degree is `1`. -/
example (w : FinitePlace F) (v : FinitePlace K) [w.LiesOver v] :
    w.1.LiesOver v.1 ↔ w.localDegree K = 1 :=
  FinitePlace.liesOver_val_iff_localDegree_eq_one w v

end ConjugatesAndLocalExtension

/-! ### Layer 0.3 — landed

The `S`-adic dictionary, discharged by `DiophantineApproximation/SIntegerLocalization.lean` and
`DiophantineApproximation/SAdicHeight.lean`. The milestone's first clause — membership in
`S.integer K` and `S.unit K` read at the finite places — is `ArithmeticHeights` 6.4 and is kept
here as an `example` of what is consumed, not as new work. -/

section SAdic

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]

/-- **Layer 0.3, consumed from `ArithmeticHeights` 6.4.** Membership in the `S`-integers and in
the `S`-units, read at the finite places. -/
example (S : Set (HeightOneSpectrum (𝓞 K))) (x : K) (u : Kˣ) :
    (x ∈ S.integer K ↔ ∀ v ∉ S, FinitePlace.mk v x ≤ 1) ∧
      (u ∈ S.unit K ↔ ∀ v ∉ S, FinitePlace.mk v (u : K) = 1) :=
  ⟨S.mem_integer_iff_finitePlace x, S.mem_unit_iff_finitePlace u⟩

/-- **Layer 0.3, landed.** The `S`-product formula for an `S`-unit, in multiplicative form; the
logarithmic form is `ArithmeticHeights` 6.5. -/
example (S : Finset (HeightOneSpectrum (𝓞 K))) {u : Kˣ}
    (hu : u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    ((∏ v : InfinitePlace K, v (u : K) ^ v.mult) * ∏ v ∈ S, FinitePlace.mk v (u : K)) = 1 :=
  NumberField.prod_apply_eq_one_of_mem_unit S hu

/-- **Layer 0.3, landed.** The height of an `S`-integral tuple is at most the product of the local
sup norms over the infinite places and `S`. ⚠ `[Finite ι]`, not `[Fintype ι]`: no sum over `ι`
occurs, and Mathlib's `unusedFintypeInType` linter rejects the stronger hypothesis. -/
example (S : Finset (HeightOneSpectrum (𝓞 K))) {x : ι → K} (hx : x ≠ 0)
    (hxS : ∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) :
    mulHeight x ≤ (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
      * ∏ v ∈ S, ⨆ i, FinitePlace.mk v (x i) :=
  NumberField.mulHeight_le_prod_of_forall_mem_integer S hx hxS

/-- **Layer 0.3, landed.** Equality for a **primitive** tuple: one whose coordinates generate the
unit ideal of `S.integer K`. That is `Set.IsPrimitive`, defined as
`1 ∈ Submodule.span ↥(S.integer K) (Set.range x)` together with `S`-integrality. -/
example (S : Finset (HeightOneSpectrum (𝓞 K))) {x : ι → K}
    (hprim : (S : Set (HeightOneSpectrum (𝓞 K))).IsPrimitive x) :
    mulHeight x = (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
      * ∏ v ∈ S, ⨆ i, FinitePlace.mk v (x i) :=
  NumberField.mulHeight_eq_prod_of_isPrimitive S hprim

/-- **Layer 0.3, landed** (Bombieri–Gubler, Proposition 5.3.6). Every finite `S` is contained in a
finite `S'` for which the `S'`-integers are a principal ideal domain. -/
example (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    ∃ S' : Set (HeightOneSpectrum (𝓞 K)), S ⊆ S' ∧ S'.Finite ∧
      IsPrincipalIdealRing ↥(S'.integer K) :=
  NumberField.exists_finite_superset_isPrincipalIdealRing S hS

/-- **Layer 0.3, landed.** Over a principal `S.integer K` every nonzero point of `Kⁿ⁺¹` has a
primitive scalar multiple. ⚠ No finiteness of `S` is needed. -/
example (S : Set (HeightOneSpectrum (𝓞 K))) [IsPrincipalIdealRing ↥(S.integer K)] {x : ι → K}
    (hx : x ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ S.IsPrimitive fun i ↦ c * x i :=
  NumberField.exists_isPrimitive_mul S hx

/-- **Layer 0.3, landed.** The two combined, in the form Bombieri–Gubler's Theorem 7.2.6 begins
with: after enlarging `S` once, the height of *every* nonzero point is, after one scaling, the
product of the local sup norms over the infinite places and the enlarged `S`. -/
example (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S' : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S' ∧
      ∀ x : ι → K, x ≠ 0 → ∃ c : K, c ≠ 0 ∧
        mulHeight x = (∏ v : InfinitePlace K, (⨆ i, v (c * x i)) ^ v.mult)
          * ∏ v ∈ S', ⨆ i, FinitePlace.mk v (c * x i) :=
  NumberField.exists_finset_superset_forall_exists_mulHeight_eq S

/-- **Layer 0.3, landed, infrastructure.** What Proposition 5.3.6 rests on and what Mathlib does
not have: `S.integer K` is the localization of `𝓞 K` at the elements supported in `S`, hence a
Dedekind domain. -/
example (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    IsLocalization S.integerSubmonoid ↥(S.integer K) ∧ IsDedekindDomain ↥(S.integer K) :=
  ⟨NumberField.isLocalization_integer S hS, NumberField.isDedekindDomain_integer S hS⟩

end SAdic

/-! ### Layer 0.4 — landed

Liouville's inequality, discharged by `DiophantineApproximation/FundamentalInequality.lean` and
`DiophantineApproximation/LiouvilleInequality.lean`. The milestone's two clauses turn out to be
one statement: the truncated local factors of a nonzero element, taken over *all* places,
multiply to the reciprocal of its height, and both the fundamental inequality and Liouville's
inequality are that identity cut down to a finite set of places. -/

section Liouville

variable {K : Type*} [Field K] [NumberField K]

/-- **Layer 0.4, landed** (Bombieri–Gubler (1.8)). The fundamental inequality: the product of the
local factors of a nonzero `α` over any set of places is trapped between the reciprocal of its
height and its height. ⚠ The lower bound uses no product formula — it is the upper bound applied
to `α⁻¹`, whose product over the *same* two sets is the inverse. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K)) {α : K} (hα : α ≠ 0) :
    ((mulHeight₁ α)⁻¹ ≤ (∏ v ∈ Sinf, v α ^ v.mult) * ∏ v ∈ Sfin, v α)
      ∧ ((∏ v ∈ Sinf, v α ^ v.mult) * ∏ v ∈ Sfin, v α ≤ mulHeight₁ α) :=
  ⟨inv_mulHeight₁_le_prod_apply Sinf Sfin hα, prod_apply_le_mulHeight₁ Sinf Sfin hα⟩

/-- **Layer 0.4, landed.** Over *all* the places the truncated product is the reciprocal of the
height on the nose: `min 1 t * max t 1 = t` turns the product formula into the definition of the
height. This, and not the inequality above, is what Liouville's inequality is built from. -/
example {α : K} (hα : α ≠ 0) :
    ((∏ v : InfinitePlace K, min 1 (v α) ^ v.mult) * ∏ᶠ v : FinitePlace K, min 1 (v α))
      = (mulHeight₁ α)⁻¹ :=
  prod_min_one_apply_eq_inv_mulHeight₁ hα

/-- **Layer 0.4, landed.** Liouville's inequality in the case `F = K`, where no place of `F` has
to be located above a place of `K`. This is the form the acceptance test runs on. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K)) {α β : K}
    (hne : β ≠ α) :
    (2 ^ finrank ℚ K * mulHeight₁ α * mulHeight₁ β)⁻¹
      ≤ (∏ v ∈ Sinf, min 1 (v (β - α)) ^ v.mult) * ∏ v ∈ Sfin, min 1 (v (β - α)) :=
  liouville_inequality_self Sinf Sfin hne

/-- **Layer 0.4, landed, the milestone's acceptance test.** Liouville's theorem over `ℝ` with the
constant named, for a number field with a real embedding. Mathlib's
`Liouville.exists_pos_real_of_irrational_root` follows from it by taking the number field to be
`ℚ⟮α⟯` inside `ℝ`; that derivation is an `example` in
`DiophantineApproximation/LiouvilleInequality.lean`. -/
example (ψ : K →+* ℝ) {ξ : K} (hξ : Irrational (ψ ξ)) {n : ℕ} (hn : finrank ℚ K ≤ n)
    (a : ℤ) (b : ℕ) :
    1 ≤ ((b : ℝ) + 1) ^ n * (|ψ ξ - a / (b + 1)| *
      (2 ^ finrank ℚ K * mulHeight₁ ξ * ((⌈|ψ ξ|⌉₊ : ℝ) + 1) ^ finrank ℚ K)) :=
  one_le_pow_mul_abs_sub_div ψ hξ hn a b

end Liouville

section LiouvilleExtension

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- **Layer 0.4, landed** (Bombieri–Gubler, Theorem 1.5.21). Liouville's inequality over an
extension: for every place `v` of `K` choose an absolute value `w v` of `F` lying over it. ⚠ The
choice is a *total* function on each kind of place; only its values on `Sinf` and `Sfin` are
read. ⚠ The heights are Mathlib's relative ones, of `α` over `F` and of `β` over `K`, which is
why the second carries the exponent `[F : K]`. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (winf : InfinitePlace K → AbsoluteValue F ℝ) (hwinf : ∀ v, (winf v).LiesOver v.1)
    (wfin : FinitePlace K → AbsoluteValue F ℝ) (hwfin : ∀ v, (wfin v).LiesOver v.1)
    {α : F} {β : K} (hne : algebraMap K F β ≠ α) :
    (2 ^ finrank ℚ F * mulHeight₁ α * mulHeight₁ β ^ finrank K F)⁻¹
      ≤ (∏ v ∈ Sinf, min 1 (winf v (algebraMap K F β - α)) ^ v.mult)
        * ∏ v ∈ Sfin, min 1 (wfin v (algebraMap K F β - α)) :=
  liouville_inequality Sinf Sfin winf hwinf wfin hwfin hne

end LiouvilleExtension

/-! ## Layer 1: approximation exponents

### Layer 1.1 — landed

Discharged by `DiophantineApproximation/IrrationalityExponent.lean` and
`DiophantineApproximation/LiouvilleExponent.lean`. The definition survived verbatim; of the four
theorems prototyped here, three survived verbatim and `irrationalityExponent_le_natDegree` lost
its `Irrational` hypothesis. The Möbius invariance and the two characterizations of the exponent
by the quality of approximations were not prototyped and are shown here for the first time. -/

section Exponents

/-- **Layer 1.1**, landed: the definition, verbatim. -/
example (ξ : ℝ) :
    Real.irrationalityExponent ξ = ⨆ (p : ℝ≥0) (_ : LiouvilleWith p ξ), (p : ℝ≥0∞) := rfl

/-- **Layer 1.1**, landed. -/
example (q : ℚ) : Real.irrationalityExponent q = 1 := Real.irrationalityExponent_ratCast q

/-- **Layer 1.1**, landed. Dirichlet. -/
example {ξ : ℝ} (hξ : Irrational ξ) : 2 ≤ Real.irrationalityExponent ξ :=
  Real.two_le_irrationalityExponent hξ

/-- **Layer 1.1**, landed. -/
example {ξ : ℝ} : Real.irrationalityExponent ξ = ⊤ ↔ Liouville ξ :=
  Real.irrationalityExponent_eq_top_iff

/-- **Layer 1.1**, landed. Liouville's theorem, as a statement about the exponent — and without
the `Irrational` hypothesis this file used to ask for. -/
example {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) :
    Real.irrationalityExponent ξ ≤ (minpoly ℚ ξ).natDegree :=
  Real.irrationalityExponent_le_natDegree hξ

/-- **Layer 1.1**, landed. Invariance under the rational Möbius group, in the form a consumer
applies: the determinant hypothesis and the hypothesis that the denominator does not vanish are
both needed, and both are on `ξ`, not on the matrix alone. -/
example (ξ : ℝ) {a b c d : ℚ} (hdet : a * d - b * c ≠ 0) (hden : (c : ℝ) * ξ + d ≠ 0) :
    Real.irrationalityExponent (((a : ℝ) * ξ + b) / ((c : ℝ) * ξ + d)) =
      Real.irrationalityExponent ξ :=
  Real.irrationalityExponent_mobius ξ hdet hden

/-- **Layer 1.1**, landed. The characterization with no constant in front of `n ^ (-ν)`. -/
example {ξ : ℝ} {μ : ℝ≥0} (hμ : 0 < μ) :
    (μ : ℝ≥0∞) ≤ Real.irrationalityExponent ξ ↔
      ∀ ν : ℝ, ν < μ → ∃ᶠ n : ℕ in Filter.atTop, ∃ m : ℤ,
        ξ ≠ m / n ∧ |ξ - m / n| < (n : ℝ) ^ (-ν) :=
  Real.le_irrationalityExponent_iff hμ

/-- **Layer 1.1**, landed. The characterization with the naive height `max |m| n` of the fraction
in place of its denominator. -/
example {ξ : ℝ} {μ : ℝ} (hμ : 0 ≤ μ) :
    LiouvilleWith μ ξ ↔ ∃ C : ℝ, ∃ᶠ n : ℕ in Filter.atTop, ∃ m : ℤ,
      ξ ≠ m / n ∧ |ξ - m / n| < C / (max |(m : ℝ)| n) ^ μ :=
  Real.liouvilleWith_iff_frequently_max hμ

/-! ### Layer 1.2 — landed

Discharged by `DiophantineApproximation/{PolynomialSupNorm,MahlerExponent,IrreducibleExponent,
KoksmaMobius}.lean`. Both definitions survived, with the two sets named (`Real.mahlerSet` and
`Real.koksmaSet`) because every proof is about them; the `naiveHeight` abbreviation pinned here
did **not** survive and is gone — Mathlib's `Polynomial.supNorm` is that height, over `ℤ`
directly, and it already carries `le_supNorm` and `exists_eq_supNorm`, which every proof uses.
The one theorem prototyped here survived verbatim. -/

/-- **Layer 1.2**, landed: Mahler's exponent `w_n`, the definition, verbatim up to the name of
the set. -/
example (n : ℕ) (ξ : ℝ) : Real.mahlerExponent n ξ =
    ⨆ (w : ℝ≥0) (_ : {P : ℤ[X] | P.natDegree ≤ n ∧ 0 < |aeval ξ P| ∧
      |aeval ξ P| ≤ P.supNorm ^ (-(w : ℝ))}.Infinite), (w : ℝ≥0∞) := rfl

/-- **Layer 1.2**, landed: Koksma's exponent `w_n^*`, normalized with `−w − 1` so that
`koksmaExponent 1 = mahlerExponent 1`. The approximants are real numbers that are roots of a
primitive irreducible integer polynomial of degree at most `n`, whose naive height is the height
of the approximant. -/
example (n : ℕ) (ξ : ℝ) : Real.koksmaExponent n ξ =
    ⨆ (w : ℝ≥0) (_ : {P : ℤ[X] | P.natDegree ≤ n ∧ P.IsPrimitive ∧ Irreducible P ∧
      ∃ a : ℝ, aeval a P = 0 ∧ 0 < |ξ - a| ∧
        |ξ - a| ≤ P.supNorm ^ (-(w : ℝ) - 1)}.Infinite), (w : ℝ≥0∞) := rfl

/-- **Layer 1.2**, landed, verbatim. -/
example (ξ : ℝ) : Real.mahlerExponent 1 ξ + 1 = Real.irrationalityExponent ξ :=
  Real.mahlerExponent_one_add_one ξ

/-- **Layer 1.2**, landed. The other half of `w_1 = w_1^* = μ − 1`, which was not prototyped. -/
example (ξ : ℝ) : Real.koksmaExponent 1 ξ = Real.mahlerExponent 1 ξ :=
  Real.koksmaExponent_one_eq_mahlerExponent_one ξ

/-- **Layer 1.2**, landed. Monotonicity in the degree. -/
example {n n' : ℕ} (h : n ≤ n') (ξ : ℝ) :
    Real.mahlerExponent n ξ ≤ Real.mahlerExponent n' ξ := Real.mahlerExponent_mono h ξ

/-- **Layer 1.2**, landed. Restricting to primitive polynomials does not change `w_n`. -/
example (n : ℕ) (ξ : ℝ) : Real.mahlerExponent n ξ =
    ⨆ (w : ℝ≥0) (_ : {P ∈ Real.mahlerSet n ξ (w : ℝ) | P.IsPrimitive}.Infinite), (w : ℝ≥0∞) :=
  Real.mahlerExponent_eq_iSup_primitive n ξ

/-- **Layer 1.2**, landed. Restricting to *irreducible* polynomials does not change `w_n`
either — this one is a theorem, and it is Gelfond's inequality (`ArithmeticHeights` 2.3) in its
integer form. -/
example (n : ℕ) (ξ : ℝ) : Real.mahlerExponent n ξ =
    ⨆ (w : ℝ≥0) (_ : {P ∈ Real.mahlerSet n ξ (w : ℝ) | Irreducible P}.Infinite), (w : ℝ≥0∞) :=
  Real.mahlerExponent_eq_iSup_irreducible n ξ

/-- **Layer 1.2**, landed. Both exponents are invariant under the rational Möbius group, in the
form a consumer applies. -/
example (n : ℕ) (ξ : ℝ) {a b c d : ℚ} (hdet : a * d - b * c ≠ 0)
    (hden : (c : ℝ) * ξ + d ≠ 0) :
    Real.mahlerExponent n (((a : ℝ) * ξ + b) / ((c : ℝ) * ξ + d)) = Real.mahlerExponent n ξ ∧
      Real.koksmaExponent n (((a : ℝ) * ξ + b) / ((c : ℝ) * ξ + d)) = Real.koksmaExponent n ξ :=
  ⟨Real.mahlerExponent_mobius n ξ hdet hden, Real.koksmaExponent_mobius n ξ hdet hden⟩

/-- **Layer 1.2**, landed. **Gelfond's inequality over `ℤ`**, for the naive height: the form
Layer 1.2 consumes `ArithmeticHeights` 2.3 in, and the only form it needs. -/
example (P Q : ℤ[X]) :
    P.supNorm * Q.supNorm ≤ 2 ^ (P.natDegree + Q.natDegree) * (P * Q).supNorm :=
  Polynomial.supNorm_mul_supNorm_le_two_pow_int P Q

/-! ### Layer 1.3 — landed except for Wirsing's first two inequalities, which are optional

Discharged by `DiophantineApproximation/{PolynomialEval,KoksmaComparison,BoxPrinciple,
AlgebraicExponent,SimultaneousBox,RootLocation,WirsingSystem,WirsingThird}.lean`. The two
elementary comparisons, the upper bound at an algebraic number and **Wirsing's third inequality**
are proved; his first two lower bounds on `w_n^*` are not, and are the `sorry`s below — with the
hypothesis `1 ≤ n` they were missing, since both are false at `n = 0`. **Those two are
optional**: every later milestone that consumes 1.3, Layer 7.3 above all, is served by what is
landed, and their one consumer is Layer 1.4, which no layer consumes in turn. -/

/-- **Layer 1.3**, landed, verbatim. Koksma's exponent is at most Mahler's — and, as the proof
showed, with no hypothesis on `ξ`. -/
example (n : ℕ) (ξ : ℝ) : Real.koksmaExponent n ξ ≤ Real.mahlerExponent n ξ :=
  Real.koksmaExponent_le_mahlerExponent n ξ

/-- **Layer 1.3**, landed. The box principle, under the name the library could give it —
`le_mahlerExponent` is Layer 1.2's order lemma. -/
example {n : ℕ} {ξ : ℝ}
    (hξ : ∀ P : ℤ[X], P ≠ 0 → P.natDegree ≤ n → aeval ξ P ≠ 0) :
    (n : ℝ≥0∞) ≤ Real.mahlerExponent n ξ :=
  Real.le_mahlerExponent_of_aeval_ne_zero hξ

/-- **Layer 1.3**, landed. The upper bound at an algebraic number, which was not prototyped: the
truncated subtraction is harmless because the degree of a minimal polynomial is positive. -/
example {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) (n : ℕ) :
    Real.mahlerExponent n ξ ≤ (((minpoly ℚ ξ).natDegree - 1 : ℕ) : ℝ≥0∞) :=
  Real.mahlerExponent_le_of_isAlgebraic hξ n

/-- **Layer 1.3**, landed, the tool both comparisons run on: **Liouville's inequality for the
value of an integer polynomial** at a real algebraic number. -/
example {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ P : ℤ[X], P.natDegree ≤ n → aeval ξ P ≠ 0 →
      c * P.supNorm ^ (-(((minpoly ℚ ξ).natDegree - 1 : ℕ) : ℝ)) ≤ |aeval ξ P| :=
  Real.exists_pos_le_abs_aeval hξ n

/-- **Layer 1.3**, landed, verbatim. The third of Wirsing's lower bounds,
`w_n^* ≥ w / (w - n + 1)` for `w = w_n`, cleared of the division; the truncated subtraction of
`ℝ≥0∞` is the right convention because the box principle gives `n ≤ w` under the same hypothesis.
At `w = n` it reads `n ≤ w_n^*`, which is what Layer 7.3 consumes. -/
example {n : ℕ} {ξ : ℝ} (hξ : ∀ P : ℤ[X], P ≠ 0 → P.natDegree ≤ n → aeval ξ P ≠ 0) :
    Real.mahlerExponent n ξ ≤
      Real.koksmaExponent n ξ * (Real.mahlerExponent n ξ + 1 - n) :=
  Real.mahlerExponent_le_koksmaExponent_mul hξ

/-- **Layer 1.3**, landed, the shape Layer 7.3 consumes: at the value the box principle forces
from below, Wirsing's conjecture holds. -/
example {n : ℕ} {ξ : ℝ} (hξ : ∀ P : ℤ[X], P ≠ 0 → P.natDegree ≤ n → aeval ξ P ≠ 0)
    (hw : Real.mahlerExponent n ξ = n) : (n : ℝ≥0∞) ≤ Real.koksmaExponent n ξ := by
  have h := Real.mahlerExponent_le_koksmaExponent_mul hξ
  rw [hw] at h
  have hone : (n : ℝ≥0∞) + 1 - (n : ℝ≥0∞) = 1 := by
    rw [add_comm]
    exact ENNReal.add_sub_cancel_right (by simp)
  rwa [hone, mul_one] at h

/-- **Layer 1.3**, **not landed** and **optional**: nothing in this roadmap consumes it except
Layer 1.4, which is optional itself. The first of Wirsing's lower bounds, in a form with no
subtraction in `ℝ≥0∞`. ⚠ The hypothesis `1 ≤ n` is not decoration: at `n = 0` both exponents
vanish and the statement reads `1 ≤ 0`. -/
theorem mahlerExponent_add_one_le_koksmaExponent_add {n : ℕ} {ξ : ℝ} (hn : 1 ≤ n)
    (hξ : ∀ P : ℤ[X], P ≠ 0 → P.natDegree ≤ n → aeval ξ P ≠ 0) :
    Real.mahlerExponent n ξ + 1 ≤ Real.koksmaExponent n ξ + n :=
  sorry

/-- **Layer 1.3**, **not landed** and **optional**, though it is the one of the two that Layer
1.4 would need. The second of Wirsing's lower bounds, `w_n^* ≥ (w_n + 1) / 2`, cleared of the
division, and with the same repair at `n = 0`. -/
theorem mahlerExponent_add_one_le_two_mul_koksmaExponent {n : ℕ} {ξ : ℝ} (hn : 1 ≤ n)
    (hξ : ∀ P : ℤ[X], P ≠ 0 → P.natDegree ≤ n → aeval ξ P ≠ 0) :
    Real.mahlerExponent n ξ + 1 ≤ 2 * Real.koksmaExponent n ξ :=
  sorry

/-- **Layer 7.3**, landed (Schmidt 1970). The exponents of a real algebraic number, in the shape
prototyped here. At `n = 1` this is Roth's theorem, and the acceptance criteria of
`DiophantineApproximation/SchmidtExponents.lean` check that reading. ⚠ The hypothesis `1 ≤ n`
turned out to be unnecessary — at `n = 0` both sides vanish — and the library states the two
halves separately. -/
example {α : ℝ} (hα : IsAlgebraic ℚ α) {n : ℕ} (_hn : 1 ≤ n) :
    Real.mahlerExponent n α = (min n ((minpoly ℚ α).natDegree - 1) : ℕ) ∧
      Real.koksmaExponent n α = (min n ((minpoly ℚ α).natDegree - 1) : ℕ) :=
  ⟨Real.mahlerExponent_eq_of_isAlgebraic hα n, Real.koksmaExponent_eq_of_isAlgebraic hα n⟩

/-- **Layer 7.3**, landed: the one bound Layer 1 could not supply, `w_n(α) ≤ n`. It is Layer 7.1
applied to `1, α, …, α ^ n` and to the coefficient vector of the polynomial, with no mean value
theorem between them — the proof of Layer 7.2 with its first step deleted. -/
example {α : ℝ} (hα : IsAlgebraic ℚ α) (n : ℕ) : Real.mahlerExponent n α ≤ (n : ℝ≥0∞) :=
  Real.mahlerExponent_le_natCast_of_isAlgebraic hα n

/-- **Layer 7.3**, landed, the polynomial-level statement the bound above is read off: for a
complex algebraic `α`, finitely many integer polynomials of degree at most `D` take a nonzero
value at `α` below `H(P) ^ (-D - ε)`. -/
example {α : ℂ} (hα : IsAlgebraic ℚ α) (D : ℕ) {ε : ℝ} (hε : 0 < ε) :
    {P : ℤ[X] | P.natDegree ≤ D ∧ aeval α P ≠ 0 ∧
      ‖aeval α P‖ ≤ P.supNorm ^ (-(D : ℝ) - ε)}.Finite :=
  Complex.finite_setOf_norm_aeval_le hα D hε

end Exponents

/-! ## Layer 2: the Roth machinery -/

section Machinery

variable {σ R : Type*} [CommRing R]

/-! ### Layer 2.1 — landed

Discharged by
`DiophantineApproximation/{MvHasseDeriv,MvHasseDerivTaylor,MvHasseDerivHeight}.lean`. The
definition prototyped here survived verbatim, with `R` weakened from a `CommRing` to a
`CommSemiring`; `MvPolynomial.hasseDeriv` is what 2.3 and 2.4 below differentiate with. -/

/-- **Layer 2.1**, landed, verbatim: the defining equation on a monomial, Bombieri–Gubler's
(6.1). The truncated subtraction is harmless, because `(m j).choose (μ j)` vanishes when
`μ j > m j`. -/
example (μ m : σ →₀ ℕ) (a : R) :
    MvPolynomial.hasseDeriv μ (MvPolynomial.monomial m a)
      = MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * a) :=
  MvPolynomial.hasseDeriv_monomial μ m a

/-- **Layer 2.1**, landed, verbatim. Agreement with `Polynomial.hasseDeriv` in one variable. -/
example [Unique σ] (k : ℕ) (P : MvPolynomial σ R) :
    MvPolynomial.uniqueAlgEquiv R σ (MvPolynomial.hasseDeriv (Finsupp.single default k) P) =
      Polynomial.hasseDeriv k (MvPolynomial.uniqueAlgEquiv R σ P) :=
  MvPolynomial.uniqueAlgEquiv_hasseDeriv k P

/-- **Layer 2.1**, landed. The composition law. The scalar is a product of natural numbers, so
the `•` is the `ℕ`-action and no cast into `R` appears. -/
example (μ ν : σ →₀ ℕ) (P : MvPolynomial σ R) :
    MvPolynomial.hasseDeriv μ (MvPolynomial.hasseDeriv ν P)
      = (μ.prod fun j k ↦ (k + ν j).choose k) • MvPolynomial.hasseDeriv (μ + ν) P :=
  MvPolynomial.hasseDeriv_comp μ ν P

/-- **Layer 2.1**, landed. The Leibniz rule, over the antidiagonal of `μ` in `σ →₀ ℕ`. -/
example [DecidableEq σ] (μ : σ →₀ ℕ) (P Q : MvPolynomial σ R) :
    MvPolynomial.hasseDeriv μ (P * Q)
      = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal μ,
          MvPolynomial.hasseDeriv x.1 P * MvPolynomial.hasseDeriv x.2 Q :=
  MvPolynomial.hasseDeriv_mul μ P Q

/-- **Layer 2.1**, landed. The Taylor expansion, over any finset carrying the orders at which the
derivative survives. -/
example (P : MvPolynomial σ R) (x y : σ → R) {s : Finset (σ →₀ ℕ)}
    (hs : ∀ μ, MvPolynomial.hasseDeriv μ P ≠ 0 → μ ∈ s) :
    MvPolynomial.eval (x + y) P
      = ∑ μ ∈ s,
          MvPolynomial.eval x (MvPolynomial.hasseDeriv μ P) * μ.prod fun j k ↦ y j ^ k :=
  MvPolynomial.eval_add_eq_sum_hasseDeriv P x y hs

/-- **Layer 2.1**, landed. `k ! • ∂_(single j k)` is the `k`-th iterate of `pderiv j`, one
variable at a time. -/
example (j : σ) (k : ℕ) (P : MvPolynomial σ R) :
    (Nat.factorial k) • MvPolynomial.hasseDeriv (Finsupp.single j k) P
      = (MvPolynomial.pderiv j)^[k] P :=
  MvPolynomial.factorial_smul_hasseDeriv_single j k P

/-- **Layer 2.1**, landed. The degree bound in one variable. -/
example (μ : σ →₀ ℕ) (P : MvPolynomial σ R) (j : σ) :
    (MvPolynomial.hasseDeriv μ P).degreeOf j ≤ P.degreeOf j - μ j :=
  MvPolynomial.degreeOf_hasseDeriv_le μ P j

/-- **Layer 2.1**, landed. The height side at an arbitrary absolute value: the constant is
`2 ^ totalDegree`, not the `2 ^ (∑ j, degreeOf j P)` the roadmap asked for, which is undefined
when `σ` is infinite. -/
example {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (μ : σ →₀ ℕ) (P : MvPolynomial σ K) :
    (⨆ n : σ →₀ ℕ, v ((MvPolynomial.hasseDeriv μ P).coeff n))
      ≤ 2 ^ P.totalDegree * ⨆ n : σ →₀ ℕ, v (P.coeff n) :=
  MvPolynomial.iSup_coeff_hasseDeriv_le v μ P

/-- **Layer 2.1**, landed. At a nonarchimedean absolute value there is no constant at all. -/
example {K : Type*} [Field K] {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v) (μ : σ →₀ ℕ)
    (P : MvPolynomial σ K) :
    (⨆ n : σ →₀ ℕ, v ((MvPolynomial.hasseDeriv μ P).coeff n))
      ≤ ⨆ n : σ →₀ ℕ, v (P.coeff n) :=
  MvPolynomial.iSup_coeff_hasseDeriv_le_of_isNonarchimedean hv μ P

/-! ### Layer 2.2 — landed

Discharged by `DiophantineApproximation/DisjointVariables.lean`. Nothing was prototyped here
before the proof, because the milestone's statement is Bombieri–Gubler's Proposition 1.6.2 read
literally; what the proof added is the renaming invariance and the two-injection form, which is
the shape Layer 2.7 will call. -/

/-- **Layer 2.2** (Bombieri–Gubler, Proposition 1.6.2), landed. The coefficients of a product in
disjoint sets of variables are the pairwise products of the coefficients, over any commutative
semiring. This is the whole content of the milestone; everything else is height bookkeeping. -/
example {τ S : Type*} [CommSemiring S] (f : MvPolynomial σ S) (g : MvPolynomial τ S)
    (m : σ →₀ ℕ) (n : τ →₀ ℕ) :
    (MvPolynomial.rename Sum.inl f * MvPolynomial.rename Sum.inr g).coeff (Finsupp.sumElim m n)
      = f.coeff m * g.coeff n :=
  MvPolynomial.coeff_sumElim_rename_mul_rename f g m n

/-- **Layer 2.2**, landed. The local factor of the height is multiplicative at **every** absolute
value, archimedean or not, and neither factor need be nonzero. -/
example {τ K : Type*} [Field K] (f : MvPolynomial σ K) (g : MvPolynomial τ K)
    (v : AbsoluteValue K ℝ) :
    (⨆ k : σ ⊕ τ →₀ ℕ,
        v ((MvPolynomial.rename Sum.inl f * MvPolynomial.rename Sum.inr g).coeff k))
      = (⨆ m : σ →₀ ℕ, v (f.coeff m)) * ⨆ n : τ →₀ ℕ, v (g.coeff n) :=
  MvPolynomial.iSup_coeff_rename_inl_mul_rename_inr f g v

/-- **Layer 2.2**, landed: Proposition 1.6.2 itself. The two nonvanishing hypotheses are forced
by the junk value `mulHeight 0 = 1`. -/
example {τ K : Type*} [Field K] [AdmissibleAbsValues K] {f : MvPolynomial σ K}
    {g : MvPolynomial τ K} (hf : f ≠ 0) (hg : g ≠ 0) :
    (MvPolynomial.rename Sum.inl f * MvPolynomial.rename Sum.inr g).mulHeight
      = f.mulHeight * g.mulHeight :=
  MvPolynomial.mulHeight_rename_inl_mul_rename_inr hf hg

/-- **Layer 2.2**, landed. The identity `h(U · V) = h(U) + h(V)` on which Roth's lemma turns. -/
example {τ K : Type*} [Field K] [AdmissibleAbsValues K] {f : MvPolynomial σ K}
    {g : MvPolynomial τ K} (hf : f ≠ 0) (hg : g ≠ 0) :
    (MvPolynomial.rename Sum.inl f * MvPolynomial.rename Sum.inr g).logHeight
      = f.logHeight + g.logHeight :=
  MvPolynomial.logHeight_rename_inl_mul_rename_inr hf hg

/-- **Layer 2.2**, landed. The height does not see how the variables are named. -/
example {τ K : Type*} [Field K] [AdmissibleAbsValues K] {e : σ → τ} (he : Function.Injective e)
    (P : MvPolynomial σ K) : (MvPolynomial.rename e P).mulHeight = P.mulHeight :=
  MvPolynomial.mulHeight_rename_of_injective he P

/-- **Layer 2.2**, landed. The form Layer 2.7 consumes: both factors already sit in one set of
variables, embedded along injections with disjoint ranges. -/
example {τ υ K : Type*} [Field K] [AdmissibleAbsValues K] {u : σ → υ} {w : τ → υ}
    (hu : Function.Injective u) (hw : Function.Injective w)
    (hd : Disjoint (Set.range u) (Set.range w)) {f : MvPolynomial σ K} {g : MvPolynomial τ K}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    (MvPolynomial.rename u f * MvPolynomial.rename w g).mulHeight = f.mulHeight * g.mulHeight :=
  MvPolynomial.mulHeight_rename_mul_rename_of_disjoint hu hw hd hf hg

/-! ### Layer 2.3 — landed

Discharged by `DiophantineApproximation/{WeightedOrder,PolynomialIndex}.lean`. The definition
prototyped here survived verbatim; of the three theorems two lost the strict positivity of the
weights and the third lost `IsDomain` with it. The file `WeightedOrder.lean` carries everything
that is not about derivatives or points, and is the reusable half. -/

/-- **Layer 2.3**, landed, verbatim: the index of `P` at `α` with respect to the weights `d`, the
least weighted order of a Hasse derivative not vanishing at `α`. It is `⊤` exactly at `P = 0`,
which is its value as a valuation and not a junk value. -/
example (d : σ → ℝ) (α : σ → R) (P : MvPolynomial σ R) :
    MvPolynomial.index d α P
      = ⨅ (μ : σ →₀ ℕ) (_ : MvPolynomial.eval α (MvPolynomial.hasseDeriv μ P) ≠ 0),
          ENNReal.ofReal (μ.sum fun j k ↦ k / d j) :=
  rfl

/-- **Layer 2.3**, landed, not prototyped — and the identity the milestone turns on. The
coefficients of the translate `P (X + α)` are the Hasse derivatives of `P` at `α`, so the index
is the weighted order of the translate and nothing else. -/
example (α : σ → R) (P : MvPolynomial σ R) (μ : σ →₀ ℕ) :
    (MvPolynomial.taylorAt α P).coeff μ = MvPolynomial.eval α (MvPolynomial.hasseDeriv μ P) :=
  MvPolynomial.coeff_taylorAt α P μ

/-- **Layer 2.3**, landed, with `0 < d j` weakened to `0 ≤ d j`. -/
example {d : σ → ℝ} (hd : ∀ j, 0 ≤ d j) (α : σ → R) (P : MvPolynomial σ R) :
    MvPolynomial.index d α P = ⊤ ↔ P = 0 :=
  MvPolynomial.index_eq_top_iff d hd α P

/-- **Layer 2.3**, landed, with `IsDomain` weakened to `NoZeroDivisors`: the index is a valuation
on a domain — in any characteristic, because the derivatives are Hasse derivatives. -/
example [NoZeroDivisors R] {d : σ → ℝ} (hd : ∀ j, 0 ≤ d j) (α : σ → R) (P Q : MvPolynomial σ R) :
    MvPolynomial.index d α (P * Q) = MvPolynomial.index d α P + MvPolynomial.index d α Q :=
  MvPolynomial.index_mul d hd α P Q

/-- **Layer 2.3**, landed, not prototyped: the other half of the valuation. -/
example {d : σ → ℝ} (hd : ∀ j, 0 ≤ d j) (α : σ → R) (P Q : MvPolynomial σ R) :
    min (MvPolynomial.index d α P) (MvPolynomial.index d α Q)
      ≤ MvPolynomial.index d α (P + Q) :=
  MvPolynomial.le_index_add d hd α P Q

/-- **Layer 2.3**, landed, not prototyped: the derivative estimate, in the form that keeps
truncated subtraction in `ℝ≥0∞` out of the statement. This is the form Roth's lemma consumes. -/
example {d : σ → ℝ} (hd : ∀ j, 0 ≤ d j) (α : σ → R) (P : MvPolynomial σ R) (μ : σ →₀ ℕ) :
    MvPolynomial.index d α P
      ≤ MvPolynomial.index d α (MvPolynomial.hasseDeriv μ P)
        + ENNReal.ofReal (μ.sum fun j k ↦ k / d j) :=
  MvPolynomial.index_le_hasseDeriv_add d hd α P μ

/-- **Layer 2.3**, landed, not prototyped: invariance under an injective change of coefficient
ring, and under translation of the point to the origin. -/
example {S : Type*} [CommRing S] {f : R →+* S} (hf : Function.Injective f) {d : σ → ℝ}
    (hd : ∀ j, 0 ≤ d j) (α : σ → R) (P : MvPolynomial σ R) :
    MvPolynomial.index d (fun j ↦ f (α j)) (MvPolynomial.map f P) = MvPolynomial.index d α P ∧
      MvPolynomial.index d 0 (MvPolynomial.taylorAt α P) = MvPolynomial.index d α P :=
  ⟨MvPolynomial.index_map d hf hd α P, MvPolynomial.index_taylorAt d hd α P⟩

/-- **Layer 2.3**, landed, not prototyped: homogeneity in the weights. -/
example {c : ℝ} (hc : 0 < c) {d : σ → ℝ} (hd : ∀ j, 0 ≤ d j) (α : σ → R)
    (P : MvPolynomial σ R) :
    MvPolynomial.index (fun j ↦ c * d j) α P
      = ENNReal.ofReal c⁻¹ * MvPolynomial.index d α P :=
  MvPolynomial.index_const_mul_weights d hc hd α P

/-- **Layer 2.3**, landed, with `IsDomain` dropped: in one variable with weight `1` the index is
the multiplicity of the root, over any commutative ring. -/
example [Unique σ] (a : R) {P : MvPolynomial σ R} (hP : P ≠ 0) :
    MvPolynomial.index (fun _ ↦ 1) (fun _ ↦ a) P
      = ((MvPolynomial.uniqueAlgEquiv R σ P).rootMultiplicity a : ℝ≥0∞) :=
  MvPolynomial.index_of_unique a hP

/-! ### Layer 2.4 — landed

Discharged by `DiophantineApproximation/{Wronskian,GeneralizedWronskian}.lean`. The one statement
prototyped here survived verbatim; what it did not mention, and what the milestone actually cost,
is the one-variable criterion it reduces to — Mathlib's `Polynomial.wronskian` is the
two-polynomial case and there is no `n`-polynomial Wronskian anywhere. -/

/-- **Layer 2.4**, landed, verbatim (Bombieri–Gubler, Proposition 6.3.10). The generalized
Wronskian criterion, over a field of characteristic zero: `φ` is linearly independent iff some
generalized Wronskian, with the `i`-th row a Hasse derivative of total order at most `i`, is not
the zero polynomial. In the library the determinant is `MvPolynomial.genWronskian` and the total
order is `Finsupp.degree`, which is this sum. -/
example {k : Type*} [Field k] [CharZero k] {n : ℕ} (φ : Fin n → MvPolynomial σ k) :
    LinearIndependent k φ ↔
      ∃ μ : Fin n → σ →₀ ℕ, (∀ i, ((μ i).sum fun _ e ↦ e) ≤ (i : ℕ)) ∧
        (Matrix.of fun i j ↦ MvPolynomial.hasseDeriv (μ i) (φ j)).det ≠ 0 :=
  MvPolynomial.linearIndependent_iff_exists_genWronskian_ne_zero φ

/-- **Layer 2.4**, landed, not prototyped: **the one-variable criterion**, which Mathlib does not
have. `n` polynomials over a field of characteristic zero are linearly independent exactly when
the determinant of their first `n` derivatives is not the zero polynomial. -/
example {k : Type*} [Field k] [CharZero k] {n : ℕ} (ψ : Fin n → Polynomial k) :
    LinearIndependent k ψ ↔
      (Matrix.of fun (i j : Fin n) ↦ Polynomial.derivative^[(i : ℕ)] (ψ j)).det ≠ 0 :=
  Polynomial.linearIndependent_iff_wronskianDet_ne_zero ψ

/-- **Layer 2.4**, landed, not prototyped: Mathlib's `Polynomial.wronskian` is the case `n = 2`,
which is what fixes the normalisation of the determinant. -/
example (a b : Polynomial R) :
    (Matrix.of fun (i j : Fin 2) ↦ Polynomial.derivative^[(i : ℕ)] (![a, b] j)).det
      = Polynomial.wronskian a b :=
  Polynomial.wronskianDet_fin_two a b

/-- **Layer 2.4**, landed, not prototyped: the easy half holds at **every** family of orders and
in every characteristic, and uses no property of the derivative. -/
example {k : Type*} [Field k] {n : ℕ} {φ : Fin n → MvPolynomial σ k}
    (hφ : ¬ LinearIndependent k φ) (μ : Fin n → σ →₀ ℕ) :
    (Matrix.of fun i j ↦ MvPolynomial.hasseDeriv (μ i) (φ j)).det = 0 :=
  MvPolynomial.genWronskian_eq_zero_of_not_linearIndependent hφ μ

/-- **Layer 2.4**, landed, not prototyped: Kronecker's choice of weights, the reusable half of the
reduction to one variable. Any finite set of exponent vectors, in any number of variables, is
separated by a single `ℕ`-valued weight. -/
example (T : Finset (σ →₀ ℕ)) :
    ∃ e : σ → ℕ, ∀ μ ∈ T, ∀ ν ∈ T, Finsupp.weight e μ = Finsupp.weight e ν → μ = ν :=
  Finsupp.exists_weight_injOn T

section CountingVolume

open MeasureTheory

/-! ### Layer 2.5 — landed

Discharged by `DiophantineApproximation/CountingVolume.lean`. Nothing was prototyped here, so
these are the first Lean statements of the three estimates; the file imports no number theory. -/

/-- **Layer 2.5**, landed, not prototyped: the region `𝒱_m(t) = {x ∈ [0,1]^m | ∑ j, x j ≤ t}` of
Bombieri–Gubler 6.3.3 and its volume `V_m(t)`. -/
example (m : ℕ) (t : ℝ) :
    cubeSimplexVolume m t
      = (volume {x : Fin m → ℝ | (∀ j, x j ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ j, x j ≤ t}).toReal := by
  have hset : cubeSimplex m t
      = {x : Fin m → ℝ | (∀ j, x j ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ j, x j ≤ t} :=
    Set.ext fun x ↦ mem_cubeSimplex
  rw [cubeSimplexVolume, hset]

/-- **Layer 2.5**, landed, not prototyped: **the lattice-point comparison**, the counting inside
Bombieri–Gubler's proof of Lemma 6.3.4. ⚠ `0 < t` is needed for the upper bound only. -/
example {m : ℕ} {d : Fin m → ℕ} (hd : ∀ j, 0 < d j) {t : ℝ} (ht : 0 < t) :
    cubeSimplexVolume m t * ∏ j, (d j : ℝ) ≤ ((latticePoints d t).card : ℝ) ∧
      ((latticePoints d t).card : ℝ)
        ≤ cubeSimplexVolume m t * (1 + max 1 t⁻¹ * ∑ j, (d j : ℝ)⁻¹) ^ m * ∏ j, (d j : ℝ) :=
  ⟨cubeSimplexVolume_mul_prod_le_card hd t, card_latticePoints_le hd ht⟩

/-- **Layer 2.5**, landed, not prototyped: **the tail** (Bombieri–Gubler, Lemma 6.3.5). ⚠ The
book's `ε ≤ 1/2` is not needed. -/
example (m : ℕ) {eps : ℝ} (heps : 0 ≤ eps) :
    cubeSimplexVolume m ((1 / 2 - eps) * m) ≤ Real.exp (-(6 * m * eps ^ 2)) :=
  cubeSimplexVolume_le_exp_neg m heps

/-- **Layer 2.5**, landed, not prototyped: **the multihomogeneous tail** (Bombieri–Gubler
(7.23)–(7.25)), as a bound on the proportion itself. ⚠ The book's `η ≤ 2/(n+1)` is not needed,
and `MeasureTheory.simplexCoordDensity` is a probability density, so no `(n !)^(-m)` appears. -/
example {n : ℕ} (hn : 1 ≤ n) {eta : ℝ} (heta : 0 ≤ eta) (m : ℕ) :
    ∫ x in {y : Fin m → ℝ | ∑ j, y j ≤ m / (n + 1) - m * eta},
        ∏ j, simplexCoordDensity n (x j)
      ≤ Real.exp (-((n + 1) * (n + 2) * eta ^ 2 * m / 4)) :=
  setIntegral_prod_simplexCoordDensity_le_exp hn heta m

/-- **Layer 2.5**, landed, not prototyped: the one exponential-moment estimate that both tails
are, at two different weights `g`. -/
example {g : ℝ → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hg : Integrable g) {lam : ℝ} (hlam : 0 ≤ lam)
    (hgl : Integrable fun x ↦ Real.exp (-(lam * x)) * g x) (m : ℕ) (s : ℝ) :
    ∫ x in {y : Fin m → ℝ | ∑ j, y j ≤ s}, ∏ j, g (x j)
      ≤ Real.exp (lam * s) * (∫ x, Real.exp (-(lam * x)) * g x) ^ m :=
  setIntegral_prod_le_exp_mul_pow hg0 hg hlam hgl m s

/-- **Layer 2.5**, landed, not prototyped: where the constant `6` comes from. Mathlib has no
inequality of this kind for `Real.sinh`. -/
example {u : ℝ} (hu : 0 ≤ u) : Real.sinh u ≤ u * Real.exp (u ^ 2 / 6) :=
  Real.sinh_le_mul_exp_sq_div_six hu

end CountingVolume

section AuxiliaryPolynomial

open MeasureTheory

/-! ### Layer 2.6 — landed

Discharged by `DiophantineApproximation/{BoxMonomial,MonomialHeight,IndexConditions,
AuxiliaryPolynomial}.lean`. The preamble above judged the index theorem unstateable here without
the `ArithmeticHeights` objects; those objects landed, so it is stated. -/

/-- **Layer 2.6**, landed, not prototyped: **the index theorem** (Bombieri–Gubler, Lemma 6.3.4),
in the `ε`–`D₀` reading of the book's `o(1)`. ⚠ The height bounded is the **absolute logarithmic**
height of `P`, and the heights of the coordinates of the points are absolute too. -/
example {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
    {m N : ℕ} (α : Fin N → Fin m → F) {t : Fin N → ℝ} (ht : ∀ k, 0 < t k)
    (hfeas : (finrank K F : ℝ) * ∑ k, cubeSimplexVolume m (t k) < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ D₀ : ℕ, ∀ d : Fin m → ℕ, (∀ j, D₀ ≤ d j) →
      ∃ P : MvPolynomial (Fin m) K, P ≠ 0 ∧ (∀ j, MvPolynomial.degreeOf j P ≤ d j) ∧
        (∀ k, ENNReal.ofReal (t k)
            ≤ MvPolynomial.index (fun j ↦ (d j : ℝ)) (α k) (P.map (algebraMap K F))) ∧
        Real.log P.mulHeight / (finrank ℚ K : ℝ)
          ≤ (finrank K F : ℝ) / (1 - (finrank K F : ℝ) * ∑ k, cubeSimplexVolume m (t k))
            * ∑ k, ∑ j, cubeSimplexVolume m (t k)
                * (absLogHeight₁ (α k j) + Real.log 2 + δ) * (d j : ℝ) :=
  MvPolynomial.exists_ne_zero_le_index_logHeight_le α ht hfeas hδ

/-- **Layer 2.6**, landed: the construction at a **fixed** multidegree, with the lattice-point
correction `κ` of Layer 2.5 left as a hypothesis. This is the whole of Lemma 6.3.4; the milestone
above is this plus a choice of `D₀`. -/
example {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
    {m N : ℕ} (α : Fin N → Fin m → F) {t : Fin N → ℝ} (ht : ∀ k, 0 < t k)
    {d : Fin m → ℕ} (hd : ∀ j, 0 < d j) {κ : ℝ} (hκ1 : 1 ≤ κ)
    (hκ : ∀ k, (1 + max 1 (t k)⁻¹ * ∑ j, ((d j : ℝ))⁻¹) ^ m ≤ κ)
    (hfeas : (finrank K F : ℝ) * κ * ∑ k, cubeSimplexVolume m (t k) < 1) :
    ∃ P : MvPolynomial (Fin m) K, P ≠ 0 ∧ (∀ j, MvPolynomial.degreeOf j P ≤ d j) ∧
      (∀ k, ENNReal.ofReal (t k)
          ≤ MvPolynomial.index (fun j ↦ (d j : ℝ)) (α k) (P.map (algebraMap K F))) ∧
      Real.log P.mulHeight / (finrank ℚ K : ℝ)
        ≤ (2 * (finrank ℚ K : ℝ))⁻¹ * Real.log |(NumberField.discr K : ℝ)|
          + (finrank K F : ℝ) * κ
              / (1 - (finrank K F : ℝ) * κ * ∑ k, cubeSimplexVolume m (t k))
            * ((∑ k, cubeSimplexVolume m (t k)
                  * ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ))
              + (∑ k, cubeSimplexVolume m (t k)) / 2
                * Real.log (Fintype.card (∀ j : Fin m, Fin (d j + 1)))) :=
  MvPolynomial.exists_ne_zero_le_index_logHeight_le_of_pow_le α ht hd hκ1 hκ hfeas

/-- **Layer 2.6**, landed: the coefficient space of Lemma 6.3.4 is the **box**
`∏ j, {0, …, d j}`, not the simplex of bounded total degree that `ArithmeticHeights` 5.7 puts
Siegel's lemma on. -/
example {K : Type*} [Field K] {m : ℕ} (d : Fin m → ℕ) (x : (∀ j, Fin (d j + 1)) → K)
    (I : ∀ j, Fin (d j + 1)) :
    (MvPolynomial.ofBox d x).coeff (MvPolynomial.boxMonomial d I) = x I ∧
      ∀ j, (MvPolynomial.ofBox d x).degreeOf j ≤ d j :=
  ⟨MvPolynomial.coeff_ofBox x I, MvPolynomial.degreeOf_ofBox_le x⟩

/-- **Layer 2.6**, landed: "`∂_μ P` vanishes at `α`" is a linear form in the coefficients on the
box, and `MvPolynomial.hasseDerivRow` is its row. -/
example {m : ℕ} {R : Type*} [CommRing R] {d : Fin m → ℕ} {Q : MvPolynomial (Fin m) R}
    (hQ : ∀ j, MvPolynomial.degreeOf j Q ≤ d j) (α : Fin m → R) (μ : Fin m →₀ ℕ) :
    MvPolynomial.eval α (MvPolynomial.hasseDeriv μ Q)
      = ∑ I : (∀ j, Fin (d j + 1)),
          MvPolynomial.hasseDerivRow d α μ I * Q.coeff (MvPolynomial.boxMonomial d I) :=
  MvPolynomial.eval_hasseDeriv_eq_sum hQ α μ

/-- **Layer 2.6**, landed: the height of a condition row — Bombieri–Gubler's
`∏ j, (2 H(α j)) ^ d j`, with the `√M` by which the Arakelov normalization of Siegel's lemma
exceeds the sup-norm one written out. -/
example {F : Type*} [Field F] [NumberField F] {m : ℕ} (d : Fin m → ℕ) (α : Fin m → F)
    {μ : Fin m →₀ ℕ} (hmu : ∀ j, μ j ≤ d j) :
    Real.log (arakelovMulHeight (MvPolynomial.hasseDerivRow d α μ)) / (finrank ℚ F : ℝ)
      ≤ 2⁻¹ * Real.log (Fintype.card (∀ j : Fin m, Fin (d j + 1)))
        + ∑ j, (d j : ℝ) * (Real.log 2 + absLogHeight₁ (α j)) :=
  MvPolynomial.absLogHeight_hasseDerivRow_le d α hmu

/-- **Layer 2.6**, landed: the one-input transport from local factors to the height, which the
roadmap recorded as missing from `ArithmeticHeights`. -/
example {K : Type*} [Field K] [Height.AdmissibleAbsValues K] {ι : Type*} [Finite ι] {x : ι → K}
    {C : ℝ} (hC : 1 ≤ C)
    (harch : ∀ v ∈ Height.AdmissibleAbsValues.archAbsVal (K := K), (⨆ i, v (x i)) ≤ C)
    (hnon : ∀ v ∈ Height.AdmissibleAbsValues.nonarchAbsVal (K := K), (⨆ i, v (x i)) ≤ 1) :
    Height.mulHeight x ≤ C ^ Height.totalWeight K :=
  Height.mulHeight_le_pow_totalWeight hC harch hnon

end AuxiliaryPolynomial

section RothLemma

/-! ### Layer 2.7 — landed

Discharged by `DiophantineApproximation/{HeightTransport,IndexRename,
PolynomialDeterminantHeight,RothDecomposition,RothDeterminant,RothBaseCase,RothEstimates,
RothLemma}.lean`. Nothing was prototyped here: the preamble judged Roth's lemma unstateable
without the `ArithmeticHeights` objects, and it was right until they landed. -/

/-- **Layer 2.7**, landed, not prototyped: **Roth's lemma** (Bombieri–Gubler, Lemma 6.3.7). The
degrees drop by a factor at least `σ ≤ 1/2` at every step, the point is high against the height
of `P`, and the index is at most `2 m σ ^ ((1/2) ^ (m - 1))` with `m` the number of variables.
⚠ Heights are Mathlib's **relative** ones, so the constant term `4 m d 0` of the hypothesis
carries the factor `Height.totalWeight K`; dividing every height by `totalWeight K = [K : ℚ]`
gives the book's statement in absolute logarithmic heights. -/
example {K : Type*} [Field K] [NumberField K] {m : ℕ} {d : Fin (m + 1) → ℕ} (hd1 : ∀ j, 1 ≤ d j)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 2)
    (hratio : ∀ j : Fin m, (d j.succ : ℝ) ≤ σ * (d j.castSucc : ℝ))
    {P : MvPolynomial (Fin (m + 1)) K} (hP : P ≠ 0)
    (hdeg : ∀ j, MvPolynomial.degreeOf j P ≤ d j) (ξ : Fin (m + 1) → K)
    (hheight : ∀ j, P.logHeight + 4 * ((m : ℝ) + 1) * (d 0 : ℝ) * (Height.totalWeight K : ℝ)
        ≤ σ * ((d j : ℝ) * Height.logHeight₁ (ξ j))) :
    MvPolynomial.index (fun j ↦ (d j : ℝ)) ξ P
      ≤ ENNReal.ofReal (2 * ((m : ℝ) + 1) * σ ^ ((1 / 2 : ℝ) ^ m)) :=
  MvPolynomial.index_le_of_degree_ratio hd1 hσ0 hσ1 hratio hP hdeg ξ hheight

/-- **Layer 2.7**, landed: **the base case** (Bombieri–Gubler, Lemma 6.3.9), at the book's own
constant `log 2`. `(X - ξ) ^ k` divides `P`, Gelfond's inequality bounds the height of a factor,
and the height of `(X - ξ) ^ k` is at least `mulHeight₁ ξ ^ k` because its coefficient vector
contains both `(-ξ) ^ k` and the leading `1`. -/
example {K : Type*} [Field K] [NumberField K] {q : Polynomial K} (hq : q ≠ 0) (a : K) :
    (q.rootMultiplicity a : ℝ) * Height.logHeight₁ a
      ≤ q.logHeight + (q.natDegree : ℝ) * Height.totalWeight K * Real.log 2 :=
  Polynomial.rootMultiplicity_mul_logHeight₁_le hq a

/-- **Layer 2.7**, landed: **the tensor decomposition**, with both families linearly independent
and `p` at most one more than the degree in the separated variable. -/
example {K : Type*} [Field K] {m : ℕ} {P : MvPolynomial (Fin (m + 1)) K} (hP : P ≠ 0) :
    ∃ (p : ℕ) (f : Fin p → MvPolynomial (Fin m) K) (g : Fin p → MvPolynomial (Fin 1) K),
      0 < p ∧ p ≤ MvPolynomial.degreeOf 0 P + 1 ∧
        LinearIndependent K f ∧ LinearIndependent K g ∧
        P = ∑ l, MvPolynomial.rename Fin.succ (f l)
              * MvPolynomial.rename (MvPolynomial.lastVar m) (g l) :=
  MvPolynomial.exists_tensor_decomposition hP

/-- **Layer 2.7**, landed: **the determinant identity**. The matrix of Hasse derivatives of `P`
at the orders `μ i` in the first `m` variables and `ν j` in the last is the product of the
Wronskian matrix of the `f` family with the transpose of that of the `g` family, so its
determinant is the product of the two generalized Wronskians — and Layer 2.2 then splits its
height exactly. -/
example {K : Type*} [Field K] {m p : ℕ} {P : MvPolynomial (Fin (m + 1)) K}
    (f : Fin p → MvPolynomial (Fin m) K) (g : Fin p → MvPolynomial (Fin 1) K)
    (hP : P = ∑ l, MvPolynomial.rename Fin.succ (f l)
        * MvPolynomial.rename (MvPolynomial.lastVar m) (g l))
    (μ : Fin p → (Fin m →₀ ℕ)) (ν : Fin p → (Fin 1 →₀ ℕ)) :
    (MvPolynomial.hasseDerivMatrix μ ν P).det
      = MvPolynomial.rename Fin.succ (MvPolynomial.genWronskian μ f)
        * MvPolynomial.rename (MvPolynomial.lastVar m) (MvPolynomial.genWronskian ν g) :=
  MvPolynomial.det_hasseDerivMatrix f g hP μ ν

/-- **Layer 2.7**, landed: **the height of the determinant**, `p` times the height of `P` plus
`totalWeight K` times `log p!` from the Leibniz expansion and `2 (∑ j, d j) p log 2` from the
`p` multiplications and the `p` differentiations. -/
example {σ K : Type*} [Fintype σ] [Field K] [Height.AdmissibleAbsValues K] {n : ℕ} {d : σ → ℕ}
    {P : MvPolynomial σ K} (hP : P ≠ 0) (hdeg : ∀ j, MvPolynomial.degreeOf j P ≤ d j)
    (ρ : Fin n → Fin n → (σ →₀ ℕ)) :
    (Matrix.of fun i j ↦ MvPolynomial.hasseDeriv (ρ i j) P).det.logHeight
      ≤ (Height.totalWeight K : ℝ)
          * (Real.log n.factorial + 2 * (∑ j, (d j : ℝ)) * n * Real.log 2)
        + n * P.logHeight :=
  MvPolynomial.logHeight_det_hasseDeriv_le hP hdeg ρ

/-- **Layer 2.7**, landed: **the transport with a one-sided nonarchimedean bound**, which
`ArithmeticHeights`'s `Finsupp.mulHeight_le_of_forall_iSup_le` does not provide: that one
demands an *equality* at the nonarchimedean absolute values, which Gauss's lemma supplies for a
product and a Hasse derivative does not. -/
example {K : Type*} [Field K] [Height.AdmissibleAbsValues K] {α γ : Type*} {x : α →₀ K}
    {z : γ →₀ K} {C : ℝ} {p : ℕ} (hx : x ≠ 0) (hC : 1 ≤ C)
    (harch : ∀ v ∈ Height.AdmissibleAbsValues.archAbsVal (K := K),
      (⨆ i : γ, v (z i)) ≤ C * (⨆ i : α, v (x i)) ^ p)
    (hnon : ∀ v ∈ Height.AdmissibleAbsValues.nonarchAbsVal (K := K),
      (⨆ i : γ, v (z i)) ≤ (⨆ i : α, v (x i)) ^ p) :
    z.mulHeight ≤ C ^ Height.totalWeight K * x.mulHeight ^ p :=
  Finsupp.mulHeight_le_pow_of_forall_iSup_le hx hC harch hnon

/-- **Layer 2.7**, landed: **the index under an injective renaming**, which is what lets the
induction be applied to the two Wronskians before they come back into the big polynomial ring. -/
example {σ τ R : Type*} [CommRing R] {e : σ → τ} (he : Function.Injective e) (d : τ → ℝ)
    (ξ : τ → R) (Q : MvPolynomial σ R) :
    MvPolynomial.index d ξ (MvPolynomial.rename e Q)
      = MvPolynomial.index (fun j ↦ d (e j)) (fun j ↦ ξ (e j)) Q :=
  MvPolynomial.index_rename he d ξ Q

/-- **Layer 2.7**, landed: **the quadratic lower bound**, the reason Roth's lemma has the
exponent `2 ^ (1 - m)`. For large `x` all `p` terms survive and the sum is about `p x`; for
small `x` only about `x e` of them do and the sum is about `x ^ 2 e / 2`. -/
example {p e : ℕ} (hp : 0 < p) (hple : p ≤ e + 1) (he : 1 ≤ e) {x : ℝ} (hx : 0 ≤ x) :
    (p : ℝ) * min (x / 2) (x ^ 2 / 4)
      ≤ ∑ i ∈ Finset.range p, max 0 (x - (i : ℕ) / (e : ℝ)) :=
  Real.le_sum_max_sub_div hp hple he hx

end RothLemma

end Machinery

/-! ## Layers 3 and 6: Roth's theorem and the Subspace Theorem

### Layer 3.1 — landed

Discharged by `DiophantineApproximation/{ApproximationClass,IndependentHeights}.lean`. Nothing
was prototyped here. The milestone is stated abstractly — a finite index type `A`, a family of
maps into the unit simplex, no place and no height in sight — because Layers 3.2, 3.7 and 5.1
each use it for a different family, and the arithmetic enters only through Northcott's theorem in
the second half. -/

section ApproximationClass

/-- **Layer 3.1**, landed, not prototyped: **Lemma 6.4.3**, the number of approximation classes
of size `1/N`. The labels are the solutions of `∑ a, c a ≤ N` in natural numbers, and the count
is exact. -/
example (A : Type*) [Fintype A] (N : ℕ) :
    {c : A → ℕ | ∑ a, c a ≤ N}.ncard = (N + Fintype.card A).choose (Fintype.card A) :=
  Set.ncard_setOf_sum_le A N

/-- **Layer 3.1**, landed: Lemma 6.4.3 in the form the applications quote — at most
`(N + |A|).choose |A|` of the classes are nonempty. -/
example {ι A : Type*} [Fintype A] {X : Set ι} (φ : A → ι → ℝ) (hφ0 : ∀ a, ∀ x ∈ X, 0 ≤ φ a x)
    (hφ1 : ∀ x ∈ X, ∑ a, φ a x ≤ 1) (N : ℕ) :
    ((fun x ↦ Real.cellIndex N fun a ↦ φ a x) '' X).ncard
      ≤ (N + Fintype.card A).choose (Fintype.card A) :=
  Set.ncard_image_cellIndex_le φ hφ0 hφ1 N

/-- **Layer 3.1**, landed: **an infinite set has an infinite approximation class**, for every
size `1/N`. This is the reduction Roth's proof opens with. -/
example {ι A : Type*} [Fintype A] {X : Set ι} (hX : X.Infinite) (φ : A → ι → ℝ)
    (hφ0 : ∀ a, ∀ x ∈ X, 0 ≤ φ a x) (hφ1 : ∀ x ∈ X, ∑ a, φ a x ≤ 1) (N : ℕ) :
    ∃ c : A → ℕ, (∑ a, c a ≤ N) ∧ {x ∈ X | Real.cellIndex N (fun a ↦ φ a x) = c}.Infinite :=
  hX.exists_cellIndex_eq φ hφ0 hφ1 N

/-- **Layer 3.1**, landed: the upper half of the book's **(6.9)**. The class of a family `f` of
numbers in `(0, 1]` with `∏ b, f b < 1` traps every `f a` between two powers of the product, and
the exponents are known to within `1/N`. -/
example {A : Type*} [Fintype A] {N : ℕ} (hN : 0 < N) {f : A → ℝ} (hpos : ∀ a, 0 < f a)
    (hf : ∀ a, f a ≤ 1) (hprod : ∏ b, f b < 1) (a : A) :
    f a ≤ (∏ b, f b) ^ ((Real.cellIndex N (Real.logProfile f) a : ℝ) / N) :=
  Real.le_rpow_cellIndex_div hN hpos hf hprod a

/-- **Layer 3.1**, landed: the book's **(6.10)**. ⚠ It needs the point to lie *on* the hyperplane
`∑ a, y a = 1`, which the counting and the pigeonhole do not. -/
example {A : Type*} [Fintype A] {N : ℕ} (hN : 0 < N) {y : A → ℝ} (hsum : ∑ a, y a = 1) :
    1 - (Fintype.card A : ℝ) / N < ∑ a, (Real.cellIndex N y a : ℝ) / N :=
  Real.one_sub_card_div_lt_sum_cellIndex_div hN hsum

/-- **Layer 3.1**, landed: **`(L, M)`-independent sequences exist inside every infinite subset of
a number field**, by Northcott's theorem. ⚠ Heights are Mathlib's relative `logHeight₁`; `M` is a
ratio and reads the same in both normalizations, and `L` is quantified, so this is the book's
statement. -/
example {K : Type*} [Field K] [NumberField K] {X : Set K} (hX : X.Infinite) (L M : ℝ) :
    ∃ β : ℕ → K, (∀ j, β j ∈ X) ∧ L ≤ logHeight₁ (β 0) ∧
      ∀ j, M * logHeight₁ (β j) ≤ logHeight₁ (β (j + 1)) := by
  obtain ⟨β, hβX, hβ0, hβs⟩ := NumberField.exists_isHeightIndependent hX L M
  exact ⟨β, hβX, hβ0, hβs⟩

/-- **Layer 3.1**, landed: **6.4.4**, the two reductions at once — an `(L, M)`-independent
sequence all of whose terms lie in one approximation class of size `1/N`. -/
example {K : Type*} [Field K] [NumberField K] {A : Type*} [Fintype A] (φ : A → K → ℝ)
    {X : Set K} (hX : X.Infinite) (hφ0 : ∀ a, ∀ x ∈ X, 0 ≤ φ a x)
    (hφ1 : ∀ x ∈ X, ∑ a, φ a x ≤ 1) (N : ℕ) (L M : ℝ) :
    ∃ c : A → ℕ, (∑ a, c a ≤ N) ∧ ∃ β : ℕ → K, (∀ j, β j ∈ X) ∧
      (∀ j, Real.cellIndex N (fun a ↦ φ a (β j)) = c) ∧ IsHeightIndependent L M β :=
  NumberField.exists_cellIndex_eq_and_isHeightIndependent φ hX hφ0 hφ1 N L M

end ApproximationClass

section Subspace

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι]

/-! ### Layer 3.2 — landed

Discharged by `DiophantineApproximation/{GlobalBound,MvPolynomialEvalBound,RothLocalBound,
RothClass,RothKeyInequality,RothAuxiliary,RothTheorem}.lean`. The signature prototyped here
survived verbatim, and it is the only signature of Layer 3 that was prototyped at all. -/

/-- **Layer 3.2**, landed (Roth; Ridout; Lang; Bombieri–Gubler, Theorem 6.4.1). Roth's theorem
over a number field with a finite set of places and targets in a finite extension, each measured
by an absolute value over the place. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ)}.Finite :=
  NumberField.finite_setOf_prod_min_one_le Sinf Sfin w hwInf hwFin α hκ

/-- **Layer 3.2**, landed: the central quantity of the layer, **the local approximation factor at
a place of `S`**, and its product over the two typed finsets. The index type is the disjoint union
`↥Sinf ⊕ ↥Sfin`, never a `Finset (AbsoluteValue K ℝ)`. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (α : AbsoluteValue K ℝ → F) (β : K) :
    ∏ a : (↥Sinf ⊕ ↥Sfin), NumberField.localApprox Sinf Sfin w α a β
      = (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult)
        * ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) :=
  NumberField.prod_localApprox Sinf Sfin w α β

/-- **Layer 3.2**, landed: **Step 0**, Layer 3.1 in the form the rest of the proof consumes — one
vector of exponents `λ` governing the local approximation factors of every term of an
`(L, M)`-independent sequence. Stated, like Layer 3.1 itself, for an arbitrary finite index type:
no place appears. -/
example {A : Type*} [Fintype A] (f : A → K → ℝ) {X : Set K} (hX : X.Infinite)
    (hpos : ∀ a, ∀ β ∈ X, 0 < f a β) (hle : ∀ a, ∀ β ∈ X, f a β ≤ 1)
    {κ : ℝ} (hκ : 0 < κ) (happrox : ∀ β ∈ X, (∏ a, f a β) ≤ mulHeight₁ β ^ (-κ))
    (hheight : ∀ β ∈ X, 1 < mulHeight₁ β) {N : ℕ} (hN : 0 < N) (L M : ℝ) :
    ∃ lam : A → ℝ, (∀ a, 0 ≤ lam a) ∧ 1 - (Fintype.card A : ℝ) / N ≤ ∑ a, lam a ∧
      ∃ β : ℕ → K, (∀ j, β j ∈ X) ∧ IsHeightIndependent L M β ∧
        ∀ j a, f a (β j) ≤ mulHeight₁ (β j) ^ (-κ * lam a) :=
  NumberField.exists_isHeightIndependent_forall_le_rpow f hX hpos hle hκ happrox hheight hN L M

/-- **Layer 3.2**, landed: **Step IV**, the product formula against local upper bounds at every
place. ⚠ This, and not the fundamental inequality of Layer 0.4, is what Roth's proof needs: the
product over `S` alone would charge the height of the polynomial twice. -/
example {y : K} (hy : y ≠ 0) {γ : Type*} [Finite γ] {x : γ → K} (hx : x ≠ 0)
    {ι : Type*} [Fintype ι] (β : ι → K) (e : ι → ℕ) {C : ℝ} (hC : 1 ≤ C)
    {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    {g : (↥Sinf ⊕ ↥Sfin) → ℝ} (hg0 : ∀ a, 0 ≤ g a)
    (hinf : ∀ v : InfinitePlace K, v y ≤ C * (⨆ i, v (x i)) * ∏ i, max (v (β i)) 1 ^ e i)
    (hfin : ∀ v : FinitePlace K, v y ≤ (⨆ i, v (x i)) * ∏ i, max (v (β i)) 1 ^ e i)
    (hS : ∀ a : ↥Sinf ⊕ ↥Sfin, NumberField.sPlaceAbsValue a y
      ≤ C * (⨆ i, NumberField.sPlaceAbsValue a (x i))
        * (∏ i, max (NumberField.sPlaceAbsValue a (β i)) 1 ^ e i) * g a) :
    1 ≤ C ^ totalWeight K * mulHeight x * (∏ i, mulHeight₁ (β i) ^ e i)
      * ∏ a, (C * g a) ^ NumberField.sPlaceWeight a :=
  NumberField.one_le_of_forall_apply_le_sum hy hx β e hC hg0 hinf hfin hS

/-- **Layer 3.2**, landed: **Steps I and II** — the auxiliary polynomial of Layer 2.6,
differentiated by Layer 2.7 until it survives at `β`, with the index at every target point and
the height of the derivative. ⚠ **This shape changed for Layer 3.8**: the target of a place is a
point `tgt a : Fin (m + 1) → F`, one coordinate per member of the chain, and `C₁` is a function
of the coordinate. Roth's theorem takes `tgt a = fun _ ↦ α a` and `C₁` constant. -/
example {A : Type*} [Fintype A] {m : ℕ} (tgt : A → Fin (m + 1) → F) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1 / 2)
    (hfeas : (finrank K F : ℝ) * (Fintype.card A : ℝ)
      * Real.exp (-(6 * ((m : ℝ) + 1) * ε ^ 2)) < 1 / 2)
    {C₁ : Fin (m + 1) → ℝ} (hC₁0 : ∀ j, 0 ≤ C₁ j)
    (hC₁ : ∀ a j, absLogHeight₁ (tgt a j) + Real.log 2 + 1 ≤ C₁ j) :
    ∃ D₀ : ℕ, ∀ d : Fin (m + 1) → ℕ, (∀ j, D₀ ≤ d j) → ∀ β : Fin (m + 1) → K,
      (∀ j : Fin m, (d j.succ : ℝ) ≤ ε ^ (2 ^ m) * (d j.castSucc : ℝ)) →
      (∀ j, (totalWeight K : ℝ) * ∑ i, C₁ i * (d i : ℝ)
            + 4 * ((m : ℝ) + 1) * (d 0 : ℝ) * (totalWeight K : ℝ)
          ≤ ε ^ (2 ^ m) * ((d j : ℝ) * logHeight₁ (β j))) →
      ∃ Q : MvPolynomial (Fin (m + 1)) K, MvPolynomial.eval β Q ≠ 0 ∧
        (∀ j, Q.degreeOf j ≤ d j) ∧
        (∀ a, ENNReal.ofReal ((1 / 2 - 4 * ε) * ((m : ℝ) + 1))
          ≤ MvPolynomial.index (fun j ↦ (d j : ℝ)) (tgt a) (Q.map (algebraMap K F))) ∧
        Real.log Q.mulHeight ≤ (totalWeight K : ℝ) * ∑ i, (C₁ i + Real.log 2) * (d i : ℝ) :=
  NumberField.exists_auxiliary_deriv tgt hε0 hε1 hfeas hC₁0 hC₁

/-! ### Layer 3.3 — landed

Discharged by `DiophantineApproximation/{RationalPlaces,RothInfinity,RothRational,Ridout}.lean`.
The signature prototyped here survived up to the order of its two hypotheses, and it was the only
one of the layer's four statements prototyped at all. -/

/-- **Layer 3.3**, landed (Roth 1955). Roth's theorem in the form it is usually quoted: the
irrationality exponent of a real algebraic irrational is `2`, whatever its degree. This is the
value Layer 1.1 leaves open between `2` and `deg ξ`. -/
example {α : ℝ} (hα : IsAlgebraic ℚ α) (hirr : Irrational α) :
    Real.irrationalityExponent α = 2 :=
  Real.irrationalityExponent_eq_two hirr hα

/-- **Layer 3.3**, landed: **targets at infinity**, the form every later one is an instance of.
The local factor at the target `∞` is `(max 1 |β| w)⁻¹`; ⚠ the reading `min 1 (|β| w)⁻¹` of
`README.md` is the same number away from `β = 0` and Lean's junk `0` at it. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → OnePoint F) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | (∏ v ∈ Sinf, (w v.1).onePointApprox (α v.1) (algebraMap K F β) ^ v.mult) *
        ∏ v ∈ Sfin, (w v.1).onePointApprox (α v.1) (algebraMap K F β)
      ≤ mulHeight₁ β ^ (-κ)}.Finite :=
  NumberField.finite_setOf_prod_onePointApprox_le Sinf Sfin w hwInf hwFin α hκ

/-- **Layer 3.3**, landed: **Ridout's theorem**, 1958. The targets are `0` at the primes of `S₁`
and `∞` at those of `S₂`; the height is the naive one, `max |p| q`. -/
example {ξ : ℝ} (halg : IsAlgebraic ℚ ξ) (S₁ S₂ : Finset Nat.Primes) {ε : ℝ} (hε : 0 < ε) :
    {β : ℚ | |ξ - (β : ℝ)| * (∏ l ∈ S₁, ((padicNorm (l : ℕ) β.num : ℚ) : ℝ))
        * ∏ l ∈ S₂, ((padicNorm (l : ℕ) β.den : ℚ) : ℝ)
      ≤ (max β.num.natAbs β.den : ℝ) ^ (-2 - ε)}.Finite :=
  Rat.finite_setOf_ridout halg S₁ S₂ hε

/-- **Layer 3.3**, landed: the **`p`-adic form** (Bombieri–Gubler 6.2.6). ⚠ The exponent is
`1 + ε` and not `2 + ε` because the target `∞` at the infinite place contributes exactly
`H(n)⁻¹` at a rational integer. -/
example (p : Nat.Primes) (w : AbsoluteValue F ℝ)
    (hw : w.LiesOver (Rat.AbsoluteValue.padic (p : ℕ))) (α : F) {ε : ℝ} (hε : 0 < ε) :
    {n : ℤ | w ((n : F) - α) ≤ |(n : ℝ)| ^ (-1 - ε)}.Finite :=
  Rat.finite_setOf_apply_intCast_sub_le p w hw α hε

/-- **Layer 3.3**, landed: the **dictionary** the layer is built on — every finite place of `ℚ`
is a `p`-adic absolute value on the nose, exponent `1`. -/
example (v : FinitePlace ℚ) : ∃ p : ℕ, ∃ _ : Fact p.Prime, v.1 = Rat.AbsoluteValue.padic p :=
  Rat.exists_prime_padic_eq v

/-! ### Layer 3.4 — landed

Discharged by `DiophantineApproximation/{ProjectiveTarget,ApproxProd,RothProjective}.lean`. The
definition prototyped here — `approxProd` — survived **verbatim** and now lives in the library,
which is why it no longer appears above; nothing else of the layer was prototyped. What the proof
taught is below. -/

/-- **Layer 3.4**, landed: the central quantity, verbatim. It is a `def` in the library, not an
abbreviation, and it is what Layer 6.3 will state the Subspace Theorem with. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) (x : ι → K) :
    approxProd Sinf Sfin w L x
      = (∏ v ∈ Sinf, (∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ^ v.mult) *
        ∏ v ∈ Sfin, ∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := rfl

/-- **Layer 3.4**, landed: **the Subspace Theorem in two variables**, which is Roth's theorem on
the projective line. This is `exists_finset_submodule_of_approxProd_le` below at
`Fintype.card ι = 2`, hypothesis for hypothesis, so Layer 6.6 — "for `card ι = 2`, 6.3 is 3.4" —
is a matter of discharging one equation. ⚠ `[Nontrivial ι]` is not needed here: `card ι = 2`
implies it. -/
example {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = 2)
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLInf : ∀ v ∈ Sinf, LinearIndependent F (L v.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent F (L v.1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 →
        approxProd Sinf Sfin w L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W :=
  NumberField.exists_finset_submodule_of_approxProd_le_card_two hcard Sinf Sfin w hwInf hwFin L
    hLInf hLFin hε

/-- **Layer 3.4**, landed: **the converse**, Roth's theorem of Layer 3.2 recovered from the
two-variable Subspace Theorem applied to the forms `X₀` and `X₁ - α v X₀`. The conclusion is
3.2's; what the theorem adds is that the Subspace shape specializes to it. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ)}.Finite :=
  NumberField.finite_setOf_prod_min_one_le_card_two Sinf Sfin w hwInf hwFin α hκ

/-- **Layer 3.4**, landed: ⚠ the central quantity is **invariant under scaling only because the
absolute values lie over the places**. The numerator of a local factor is measured in `F` and the
denominator in `K`; without `LiesOver` they scale by different numbers and `approxProd` is not a
function on projective space at all. The hypothesis is free — every layer carries it — but it
belongs in the statement of the invariance, and `README.md`'s table did not say so. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) (x : ι → K) {c : K} (hc : c ≠ 0) :
    approxProd Sinf Sfin w L (c • x) = approxProd Sinf Sfin w L x :=
  NumberField.approxProd_smul Sinf Sfin w hwInf hwFin L x hc

/-- **Layer 3.4**, landed: Layer 3.3 **with a constant in front of the height**. Both directions
of 3.4 produce an inequality with a constant, and both are finished by applying 3.3 at an
exponent strictly between `2` and `κ` and collecting the bounded-height remainder by Northcott.
⚠ This, and not a sharper local estimate, is how the constants of the two changes of variable are
paid for; it is the same device Layer 3.3 uses for the Möbius map. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → OnePoint F) (C : ℝ) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | (∏ v ∈ Sinf, (w v.1).onePointApprox (α v.1) (algebraMap K F β) ^ v.mult) *
        ∏ v ∈ Sfin, (w v.1).onePointApprox (α v.1) (algebraMap K F β)
      ≤ C * mulHeight₁ β ^ (-κ)}.Finite :=
  NumberField.finite_setOf_prod_onePointApprox_le_const Sinf Sfin w hwInf hwFin α C hκ

/-- **Layer 3.4**, landed: ⚠ the split by which form is small needs a choice function defined on
**every** absolute value of `K`, not only on `S`, because that is how Roth's theorem indexes its
targets. Extending it needs to know that no infinite place has the underlying absolute value of a
finite place, which `README.md` never had occasion to say. -/
example (v : InfinitePlace K) (u : FinitePlace K) : v.1 ≠ u.1 :=
  NumberField.InfinitePlace.val_ne_finitePlace_val v u

/-! ### Layer 3.5 — landed

Discharged by `DiophantineApproximation/{PrimeProducts,MahlerPowers}.lean`. The one statement
prototyped here survived **verbatim**, hypothesis for hypothesis; what the proof taught is
below. -/

/-- **Layer 3.5** (Mahler 1957), landed, verbatim. The distance from `(p/q)^k` to the nearest
integer. ⚠ The conclusion is `∀ᶠ` and cannot be `∀`: at `k = 0` the power is the integer `1`,
so `0` is in the exceptional set for every `ε`. -/
example {p q : ℕ} (hq : 2 ≤ q) (hpq : q < p) (hcop : p.Coprime q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in Filter.atTop,
      Real.exp (-ε * k) < |((p : ℝ) / q) ^ k - round (((p : ℝ) / q) ^ k)| :=
  Nat.eventually_exp_neg_lt_abs_sub_round hq hpq hcop hε

/-- **Layer 3.5**, landed: the finiteness the proof actually produces, of which the statement
above is the special case `N = round ((p/q)^k)`. ⚠ It quantifies over **every** integer `N`, not
only the nearest one, and so does not need the minimality of `round`. -/
example {p q : ℕ} (hq : 2 ≤ q) (hpq : q < p) (hcop : p.Coprime q) {ε : ℝ} (hε : 0 < ε) :
    {k : ℕ | ∃ N : ℤ, |((p : ℝ) / q) ^ k - (N : ℝ)| ≤ Real.exp (-ε * k)}.Finite :=
  Nat.finite_setOf_exists_int_abs_sub_ratPow_le hq hpq hcop hε

/-- **Layer 3.5**, landed: ⚠ **what Ridout's theorem gives is not `exp (-ε k)` but a power of
`p` with a constant in front**, and the constant `2 ^ (-2 - δ)` is not cosmetic — it is what the
height bound `max |β.num| β.den ≤ 2 β.den` leaves behind. Passing to the exponential form costs
one initial segment of `k`, and that is the only place the two differ. -/
example {p q : ℕ} (hq : 2 ≤ q) (hpq : q < p) (hcop : p.Coprime q) {δ : ℝ} (hδ : 0 < δ) :
    {k : ℕ | ∃ N : ℤ, |((p : ℝ) / q) ^ k - (N : ℝ)|
      ≤ (2 : ℝ) ^ (-2 - δ) * (p : ℝ) ^ (-δ * k)}.Finite :=
  Nat.finite_setOf_exists_int_abs_sub_ratPow_le_rpow hq hpq hcop hδ

/-- **Layer 3.5**, landed: ⚠ the arithmetic input Layer 3.3 did **not** have. Ridout's two
products are estimates in general and *identities* when the index set is the set of primes of the
number itself, and it is the identity — not an estimate — that makes the denominator of the
auxiliary rational cancel against its height. Over a smaller set of primes the product is too
large, never too small, which is the wrong direction for every application. -/
example (S : Finset Nat.Primes) (d : ℕ) (hd : d ≠ 0)
    (hS : ∀ l : Nat.Primes, (l : ℕ) ∣ d → l ∈ S) :
    ∏ l ∈ S, padicNorm (l : ℕ) ((d : ℕ) : ℚ) = ((d : ℕ) : ℚ)⁻¹ :=
  Rat.prod_padicNorm_natCast S d hd hS

/-- **Layer 3.5**, landed: ⚠ **the auxiliary rational is `N q ^ k / p ^ k`, and `README.md`'s
reciprocal `p ^ k / (N q ^ k)` is the orientation that forces the gcd into the proof.** In this
one the denominator divides `p ^ k`, so the product over the primes of `p` is `1 / β.den`
exactly and cancels against `max |β.num| β.den ≤ 2 β.den`; in the reciprocal the denominator is
`N q ^ k / gcd (N, p ^ k)`, whose prime factors need not divide `p q` at all, and the
cancellation has to be done by naming that gcd. Both orientations prove the theorem; only one
never mentions it. -/
example (p q : ℕ) (N : ℤ) (k : ℕ) :
    ((((N * (q : ℤ) ^ k : ℤ) : ℚ) / (((p : ℤ) ^ k : ℤ) : ℚ)).den : ℤ) ∣ ((p : ℤ) ^ k) := by
  rw [← Rat.divInt_eq_div]
  exact Rat.den_dvd _ _

/-! ### Layer 3.6 — landed

Discharged by `DiophantineApproximation/{BinaryForm,ThueEquation}.lean`. Nothing was prototyped
here; the statements below are pinned for the first time, in the shape that was proved. -/

/-- **Layer 3.6** (Thue 1909; Bombieri–Gubler, Theorem 6.2.1), landed. Thue's theorem with the
roadmap's hypothesis read literally: three linear forms over `ℂ`, pairwise non-proportional — a
nonzero `2 × 2` determinant — and each dividing `G`. ⚠ `G ∈ ℤ[X, Y]` homogeneous is
`MvPolynomial (Fin 2) ℤ` with `IsHomogeneous d`: Mathlib's `Polynomial.homogenize` and
`homogenize_eq_of_isHomogeneous` already make every such form the homogenization of a polynomial
in one variable, so nothing had to be defined. -/
example {G : MvPolynomial (Fin 2) ℤ} {d : ℕ} (hG : G.IsHomogeneous d)
    (hfac : ∃ l : Fin 3 → Fin 2 → ℂ, Pairwise (fun i j ↦ l i 0 * l j 1 ≠ l i 1 * l j 0) ∧
      ∀ i, (MvPolynomial.C (l i 0) * MvPolynomial.X 0 + MvPolynomial.C (l i 1) *
        MvPolynomial.X 1) ∣ G.map (Int.castRingHom ℂ))
    {m : ℤ} (hm : m ≠ 0) :
    {z : ℤ × ℤ | MvPolynomial.eval ![z.1, z.2] G = m}.Finite :=
  hG.finite_setOf_eval_eq hfac hm

/-- **Layer 3.6**, landed: the form the proof works with, the hypothesis counted on the complex
roots of the dehomogenization `g`, with the point at infinity counting once when `deg g < d`.
⚠ That branch — `Y` divides `G` — needs no approximation at all: `y ∣ m`. -/
example {g : ℤ[X]} {d : ℕ} (hd : g.natDegree ≤ d)
    (hroots : 3 ≤ (g.map (Int.castRingHom ℂ)).roots.toFinset.card +
      if g.natDegree = d then 0 else 1)
    {m : ℤ} (hm : m ≠ 0) :
    {z : ℤ × ℤ | MvPolynomial.eval ![z.1, z.2] (g.homogenize d) = m}.Finite :=
  Polynomial.finite_setOf_eval_homogenize_eq hd hroots hm

/-- **Layer 3.6**, landed: ⚠ **the price of not factoring first.** Bombieri–Gubler reduce to one
irreducible form over `ℤ` before approximating; run on `G` itself, repeated factors and all, the
argument has exponent `d / μ` at the nearest root, and Roth's theorem needs it above `2`. For an
irrational root that is this bound: `(minpoly ℚ r) ^ μ` divides `g`, the minimal polynomial has
degree at least `2`, and in degree exactly `2` the third root has to come from the cofactor. -/
example {g : ℤ[X]} (hg : g ≠ 0) {r : ℂ} (hr : r ∈ (g.map (Int.castRingHom ℂ)).roots)
    (hirr : r ∉ Set.range (algebraMap ℚ ℂ))
    (h3 : 3 ≤ (g.map (Int.castRingHom ℂ)).roots.toFinset.card) :
    2 * (g.map (Int.castRingHom ℂ)).roots.count r < g.natDegree :=
  Polynomial.two_mul_count_roots_lt_natDegree hg hr hirr h3

/-- **Layer 3.6**, landed: ⚠ **and at a rational root the bound is false.** `X ^ 2 (X ^ 2 - 2)`
has the root `0` with multiplicity `2` in degree `4`, so the exponent there is exactly `2`, where
Roth's theorem says nothing; the proof uses Liouville's inequality with exponent `1` at rational
roots instead. The book never meets the case, because its reduction leaves a single irreducible
factor, of degree at least `3`. -/
example : 2 * (X ^ 2 * (X ^ 2 - C 2) : ℂ[X]).rootMultiplicity 0 =
    (X ^ 2 * (X ^ 2 - C 2) : ℂ[X]).natDegree := by
  have h2 : (X ^ 2 - C 2 : ℂ[X]) ≠ 0 := X_pow_sub_C_ne_zero (by norm_num) 2
  rw [rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 X_ne_zero) h2),
    rootMultiplicity_eq_zero (p := (X ^ 2 - C 2 : ℂ[X])) (by simp),
    natDegree_mul (pow_ne_zero 2 X_ne_zero) h2, natDegree_X_pow_sub_C, natDegree_X_pow]
  have : (X ^ 2 : ℂ[X]) = (X - C 0) ^ 2 := by simp
  rw [this, rootMultiplicity_X_sub_C_pow]

/-- **Layer 3.6**, landed: Roth's theorem in the shape Thue's argument consumes — unreduced
fractions `x / y`, a power `μ` of the distance and a power `e > 2 μ` of the denominator. ⚠ Only
the one-place rational form of Layer 3.3 is used; no finite place appears. -/
example {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) (hirr : Irrational ξ) {μ e : ℕ} (hμ : 0 < μ)
    (he : 2 * μ < e) (C : ℝ) :
    {z : ℤ × ℤ | z.2 ≠ 0 ∧ |ξ - (z.1 : ℝ) / z.2| ^ μ * |(z.2 : ℝ)| ^ e ≤ C}.Finite :=
  Real.finite_setOf_pow_abs_sub_div_mul_pow_le hξ hirr hμ he C

/-! ### Layer 3.7 — landed

Discharged by `DiophantineApproximation/{GapPrinciple,CountingApproximations}.lean`, with the core
of Roth's proof exposed in `DiophantineApproximation/RothTheorem.lean`. Nothing was prototyped
here; the statements below are pinned for the first time, in the shape that was proved. Heights
are absolute, as the roadmap asks. -/

/-- **Layer 3.7** (Bombieri–Gubler, Theorem 6.5.4), landed: **the strong gap principle**, for two
different solutions in one approximation class of size `1 / N`. ⚠ The class is
`NumberField.approxClass`, which puts a solution equal to a target — a `β` the book's classes
leave out, since its logarithmic profile is `0 / 0` — in a corner of the simplex, where the
book's bounds (6.9) and (6.10) still hold. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) {β β' : K}
    (hsol : (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ))
    (hsol' : (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β' - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β' - α v.1)) ≤ mulHeight₁ β' ^ (-κ))
    (hne : β ≠ β')
    (hclass : NumberField.approxClass Sinf Sfin w α N β
      = NumberField.approxClass Sinf Sfin w α N β')
    (hle : absLogHeight₁ β ≤ absLogHeight₁ β') :
    ((1 - ((Sinf.card + Sfin.card : ℕ) : ℝ) / N) * κ - 1) * absLogHeight₁ β - Real.log 4
      ≤ absLogHeight₁ β' :=
  NumberField.mul_absLogHeight₁_sub_le_of_approxClass_eq hwInf hwFin hκ hN hsol hsol' hne hclass
    hle

/-- **Layer 3.7**, landed: ⚠ **the gap principle needs the class only through its bounds.** For any
vector of exponents `λ ≥ 0` governing the local approximation factors of both points the same
inequality holds, with `∑ λ` in place of `1 − |S| / N`; the book's first step, passing to the
places where `|β − α v| < 1`, is not needed. -/
example {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ}
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 0 ≤ κ) {lam : (↥Sinf ⊕ ↥Sfin) → ℝ}
    (hlam : ∀ a, 0 ≤ lam a) {β β' : K} (hne : β ≠ β')
    (hle : absLogHeight₁ β ≤ absLogHeight₁ β')
    (hβ : ∀ a, NumberField.localApprox Sinf Sfin w α a β ≤ mulHeight₁ β ^ (-κ * lam a))
    (hβ' : ∀ a, NumberField.localApprox Sinf Sfin w α a β' ≤ mulHeight₁ β' ^ (-κ * lam a)) :
    (κ * ∑ a, lam a - 1) * absLogHeight₁ β - Real.log 4 ≤ absLogHeight₁ β' :=
  NumberField.mul_absLogHeight₁_sub_le_of_localApprox_le hwInf hwFin α hκ hlam hne hle hβ hβ'

/-- **Layer 3.7** (Bombieri–Gubler, Lemma 6.5.6), landed: **the count in a window.** ⚠ The
hypothesis is `X ≥ log 16 / (c − 1)`: the book states it strictly and applies it at equality. -/
example {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ}
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) {c : ℝ}
    (hcdef : c = (1 - ((Sinf.card + Sfin.card : ℕ) : ℝ) / N) * κ - 1) (hc : 1 < c)
    {X A : ℝ} (hX : Real.log 16 / (c - 1) ≤ X) :
    {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ) ∧
      X < absLogHeight₁ β ∧ absLogHeight₁ β ≤ A * X}.ncard
      ≤ ⌈Real.log A / Real.log ((c + 1) / 2)⌉₊
        * (N + (Sinf.card + Sfin.card)).choose (Sinf.card + Sfin.card) :=
  NumberField.ncard_setOf_absLogHeight₁_mem_Ioc_le hwInf hwFin α hκ hN hcdef hc hX

/-- **Layer 3.7** (Bombieri–Gubler 6.5.7; Davenport and Roth 1955 at one place), landed: **the
count of large solutions.** Above a height `L` depending on the targets there are at most
`NumberField.rothLargeCount κ |S| [F : K]` solutions, a number that sees nothing else. ⚠ It is a
bound on the **number** of solutions and gives none on their height. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    ∃ L : ℝ, {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ) ∧
      L < absLogHeight₁ β}.ncard
        ≤ NumberField.rothLargeCount κ (Sinf.card + Sfin.card) (finrank K F) :=
  NumberField.exists_ncard_setOf_lt_absLogHeight₁_le Sinf Sfin w hwInf hwFin α hκ

/-- **Layer 3.7**, landed: ⚠ **the core of Roth's proof, which the count consumes and Layer 3.2
did not expose.** Above a height `L` there is no `(L, M)`-independent chain of `m + 1` solutions
in one class, with `m`, `M` and the class size `N` definitions depending on `κ`, `|S|` and
`[F : K]` alone. Layer 3.2 proved this only inside a proof by contradiction; Roth's theorem is
now derived from it. Heights here are Mathlib's relative ones, as in Layer 3.2. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    ∃ L : ℝ, ∀ lam : (↥Sinf ⊕ ↥Sfin) → ℝ, (∀ a, 0 ≤ lam a) →
      1 - ((Sinf.card + Sfin.card : ℕ) : ℝ) / NumberField.rothClassSize κ (Sinf.card + Sfin.card)
        ≤ ∑ a, lam a →
      ∀ β : Fin (NumberField.rothChainLength κ (Sinf.card + Sfin.card) (finrank K F) + 1) → K,
        L ≤ logHeight₁ (β 0) →
        (∀ j : Fin (NumberField.rothChainLength κ (Sinf.card + Sfin.card) (finrank K F)),
          NumberField.rothRatio κ (Sinf.card + Sfin.card) (finrank K F) * logHeight₁ (β j.castSucc)
            ≤ logHeight₁ (β j.succ)) →
        ¬ ∀ j a, NumberField.localApprox Sinf Sfin w α a (β j) ≤ mulHeight₁ (β j) ^ (-κ * lam a) :=
  NumberField.roth_no_chain Sinf Sfin w hwInf hwFin α hκ

/-! ### Layer 3.8 — landed

Discharged by `DiophantineApproximation/MovingTargets.lean`, with the core of Roth's proof
restated for moving targets in `DiophantineApproximation/RothTheorem.lean` and the size of a
target bounded by its height in `DiophantineApproximation/FundamentalInequality.lean`. Nothing was
prototyped here; the statements below are pinned for the first time, in the shape that was
proved. -/

/-- **Layer 3.8** (Vojta; Bombieri–Gubler, Theorem 6.5.2), landed: **Roth's theorem with moving
targets.** If `1 + ∑ v ∈ S, h(α j v) = o(h(β j))`, only finitely many indices `j` are solutions
with the targets `α j`. Heights in the growth condition are absolute. ⚠ The conclusion counts
indices, not values: the sequence may repeat a pair. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    {κ : ℝ} (hκ : 2 < κ) (α : ℕ → AbsoluteValue K ℝ → F) (β : ℕ → K)
    (hα : (fun j ↦ 1 + ∑ v ∈ Sinf, absLogHeight₁ (α j v.1) + ∑ v ∈ Sfin, absLogHeight₁ (α j v.1))
      =o[Filter.atTop] fun j ↦ absLogHeight₁ (β j)) :
    {j : ℕ | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F (β j) - α j v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F (β j) - α j v.1))
          ≤ mulHeight₁ (β j) ^ (-κ)}.Finite :=
  NumberField.finite_setOf_prod_min_one_le_of_isLittleO Sinf Sfin w hwInf hwFin hκ α β hα

/-- **Layer 3.8**, landed, in the book's form: no infinite sequence of pairs with
`1 + ∑ v ∈ S, h(α j v) = o(h(β j))` consists of solutions. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    {κ : ℝ} (hκ : 2 < κ) (α : ℕ → AbsoluteValue K ℝ → F) (β : ℕ → K)
    (hα : (fun j ↦ 1 + ∑ v ∈ Sinf, absLogHeight₁ (α j v.1) + ∑ v ∈ Sfin, absLogHeight₁ (α j v.1))
      =o[Filter.atTop] fun j ↦ absLogHeight₁ (β j)) :
    ¬ ∀ j, (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F (β j) - α j v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F (β j) - α j v.1))
          ≤ mulHeight₁ (β j) ^ (-κ) :=
  NumberField.not_forall_prod_min_one_le_of_isLittleO Sinf Sfin w hwInf hwFin hκ α β hα

/-- **Layer 3.8**, landed: ⚠ **the core of Roth's proof with moving targets**, which Layer 3.2 is
now derived from. There is a `δ > 0`, depending on `K`, `S`, `[F : ℚ]` and `κ` and on no target,
such that no chain of `m + 1` solutions in one class, with heights growing by the ratio `M` and
each member `β j` carrying its own targets `α j`, has `1 + ∑ v, h(α j v) ≤ δ h(β j)` throughout.
Layer 3.7's `roth_no_chain` is its constant case. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    {κ : ℝ} (hκ : 2 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : (↥Sinf ⊕ ↥Sfin) → ℝ, (∀ a, 0 ≤ lam a) →
      1 - ((Sinf.card + Sfin.card : ℕ) : ℝ) / NumberField.rothClassSize κ (Sinf.card + Sfin.card)
        ≤ ∑ a, lam a →
      ∀ (α : Fin (NumberField.rothChainLength κ (Sinf.card + Sfin.card) (finrank K F) + 1) →
          AbsoluteValue K ℝ → F)
        (β : Fin (NumberField.rothChainLength κ (Sinf.card + Sfin.card) (finrank K F) + 1) → K),
        (∀ j, 1 + ∑ a : ↥Sinf ⊕ ↥Sfin, absLogHeight₁ (α j (NumberField.sPlaceAbsValue a))
          ≤ δ * absLogHeight₁ (β j)) →
        (∀ j : Fin (NumberField.rothChainLength κ (Sinf.card + Sfin.card) (finrank K F)),
          NumberField.rothRatio κ (Sinf.card + Sfin.card) (finrank K F)
              * logHeight₁ (β j.castSucc) ≤ logHeight₁ (β j.succ)) →
        ¬ ∀ j a, NumberField.localApprox Sinf Sfin w (α j) a (β j)
          ≤ mulHeight₁ (β j) ^ (-κ * lam a) :=
  NumberField.roth_no_moving_chain Sinf Sfin w hwInf hwFin hκ

/-- **Layer 3.8**, landed: ⚠ **the size of a target is bounded by its height**, the fact the book's
proof of 6.5.2 uses without naming. An absolute value of `F` over an infinite place of `K` is an
infinite place of `F`, and one over a finite place is a root of exponent at most `1` of a finite
place of `F` (Layer 0.1); either way `max |x|_w 1 ≤ H(x)`. -/
example (v : InfinitePlace K) (w : AbsoluteValue F ℝ) [w.LiesOver v.1] (x : F) :
    max (w x) 1 ≤ mulHeight₁ x :=
  NumberField.max_apply_one_le_mulHeight₁_of_liesOver_infinitePlace v w x

example (v : FinitePlace K) (w : AbsoluteValue F ℝ) [w.LiesOver v.1] (x : F) :
    max (w x) 1 ≤ mulHeight₁ x :=
  NumberField.max_apply_one_le_mulHeight₁_of_liesOver_finitePlace v w x

/-! ### Layer 4.1 — landed

Discharged by `DiophantineApproximation/{FinitePlaceValues,ModuleCovolume,ApproximationDomain,
ApproximationVolume}.lean`. Both definitions prototyped here — `approxDomain` and `approxWeight` —
survived **verbatim** and now live in the library, which is why they no longer appear below; the
milestone's other statements — the domain as `Λ ∩ B`, the covolume of `Λ`, the volume of `B` and
their comparison with `Q` to the weight — are prototyped here for the first time. -/

/-- **Layer 4.1**, landed: the approximation domain, verbatim. -/
example (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) :
    approxDomain Sfin L c Q =
      {x | (∀ (v : InfinitePlace K) (i : ι), v (L v.1 i x) ≤ Q ^ c v.1 i) ∧
        (∀ v ∈ Sfin, ∀ i : ι, v (L v.1 i x) ≤ Q ^ c v.1 i) ∧
        ∀ v : FinitePlace K, v ∉ Sfin → ∀ j : ι, v (x j) ≤ 1} := rfl

/-- **Layer 4.1**, landed: the weight, verbatim. -/
example (Sfin : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ) :
    approxWeight Sfin c =
      ∑ v : InfinitePlace K, v.mult * ∑ i, c v.1 i + ∑ v ∈ Sfin, ∑ i, c v.1 i := rfl

/-- **Layer 4.1**, landed: **the domain is `Λ ∩ B`** — the finite conditions cut out an
`𝓞 K`-submodule of `Kⁱ`, the infinite ones a body in `(K ⊗ ℝ)ⁱ = ι → mixedSpace K`. ⚠ The
module is stated with `|Q|` so that it is a submodule for every real `Q`; the identity needs
`Q ≥ 0`. -/
example (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 ≤ Q) :
    approxDomain Sfin L c Q = {x | x ∈ approxModule Sfin L c Q ∧
      (fun j ↦ mixedEmbedding K (x j)) ∈ approxBody L c Q} :=
  NumberField.approxDomain_eq Sfin L c hQ

/-- **Layer 4.1**, landed: **the body is balanced over every completion at once**, the property
4.2's comparison `λ (d l) ≤ c_K μ l` spends: multiplying by an element of the mixed space whose
local norms are at most `1` keeps it. -/
example {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ}
    {z : ι → mixedEmbedding.mixedSpace K} (hz : z ∈ approxBody L c Q)
    {a : mixedEmbedding.mixedSpace K} (ha : ∀ w, mixedEmbedding.normAtPlace w a ≤ 1) :
    (fun j ↦ a * z j) ∈ approxBody L c Q :=
  NumberField.mul_mem_approxBody hz ha

open scoped Classical in
/-- **Layer 4.1**, landed: **the covolume of `Λ`** is that of `(𝓞 K)ⁱ` times the generalized index
`∏ v ∈ Sfin, v (det L v) * ∏ i, (a v i)⁻¹`, with `a v i` the largest value of `v` at most
`Q ^ c v i`. ⚠ It is exact in `a v i`, not in `Q ^ c v i`; see the preamble. -/
example {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hL : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : 0 < Q) :
    ZLattice.covolume (approxLattice Sfin L c Q) =
      (∏ v ∈ Sfin, v (LinearMap.det (LinearMap.pi (L v.1))) *
        ∏ i, (v.floorValue (Q ^ c v.1 i))⁻¹) *
      ZLattice.covolume (mixedEmbedding.integerLattice K) ^ Fintype.card ι :=
  NumberField.covolume_approxLattice hL c hQ

open scoped Classical in
/-- **Layer 4.1**, landed: **the volume of `B`** is that of the unit body,
`2 ^ (r₁ #ι) π ^ (r₂ #ι)`, times `∏_{v | ∞} (v (det L v)⁻¹ ∏ i, Q ^ c v i) ^ mult v`. -/
example {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hL : ∀ w : InfinitePlace K, LinearIndependent K (L w.1)) (c : AbsoluteValue K ℝ → ι → ℝ)
    {Q : ℝ} (hQ : 0 < Q) :
    MeasureTheory.volume (approxBody L c Q) =
      ENNReal.ofReal (2 ^ (InfinitePlace.nrRealPlaces K * Fintype.card ι) *
        Real.pi ^ (InfinitePlace.nrComplexPlaces K * Fintype.card ι) *
        ∏ w : InfinitePlace K,
          ((w (LinearMap.det (LinearMap.pi (L w.1))))⁻¹ * ∏ i, Q ^ c w.1 i) ^ w.mult) :=
  NumberField.volume_approxBody hL c hQ

open scoped Classical in
/-- **Layer 4.1**, landed: **`vol B / covol Λ` is `Q` to the weight up to two constants** depending
on `K`, `Sfin`, `#ι` and the determinants only (Bombieri–Gubler, Corollary 7.5.8). The upper
bound — the one 4.3 uses — carries no loss; the lower one loses `∏_{v ∈ Sfin} N 𝔭_v ^ #ι`. -/
example {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : 0 < Q) :
    approxConst Sfin L *
        (∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ Fintype.card ι)⁻¹ *
        Q ^ approxWeight Sfin c ≤
      (MeasureTheory.volume (approxBody L c Q)).toReal /
        ZLattice.covolume (approxLattice Sfin L c Q) ∧
    (MeasureTheory.volume (approxBody L c Q)).toReal /
        ZLattice.covolume (approxLattice Sfin L c Q) ≤
      approxConst Sfin L * Q ^ approxWeight Sfin c :=
  ⟨NumberField.le_volume_div_covolume hLInf hLFin c hQ,
    NumberField.volume_div_covolume_le hLInf hLFin c hQ⟩

/-! ### Layer 4.2 — landed

Discharged by `DiophantineApproximation/{FieldMinima,FieldMinkowski}.lean`. Nothing of 4.2 was
prototyped here — the preamble judged its statements unstateable without the `ArithmeticHeights`
minima — so every statement below is prototyped for the first time. ⚠ The minima are indexed from
`0`: the roadmap's `μ l` is `successiveMinimum Λ B (l - 1)`. -/

open scoped Pointwise in
/-- **Layer 4.2**, landed: the successive minima over `K` — the least dilation of `B` whose
intersection with `Λ` holds `i + 1` vectors independent over `K`. -/
example (Λ : Submodule (𝓞 K) (ι → K)) (B : Set (ι → mixedEmbedding.mixedSpace K)) (i : ℕ) :
    successiveMinimum Λ B i = sInf {t : ℝ | 0 < t ∧ ∃ x : Fin (i + 1) → ι → K,
      (∀ k, x k ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x k j)) ∈ t • B) ∧ LinearIndependent K x} :=
  rfl

open scoped Classical Pointwise in
/-- **Layer 4.2**, landed: **the minima over `K` are attained, by one family independent over
`K`**. -/
example (Λ : Submodule (𝓞 K) (ι → K)) [DiscreteTopology Λ.mixedImage]
    [IsZLattice ℝ Λ.mixedImage] {B : Set (ι → mixedEmbedding.mixedSpace K)} (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B)
    (hB₄ : IsClosed B) :
    ∃ x : Fin (Fintype.card ι) → ι → K, LinearIndependent K x ∧ ∀ k, x k ∈ Λ ∧
      (fun j ↦ mixedEmbedding K (x k j)) ∈ successiveMinimum Λ B k • B :=
  NumberField.exists_linearIndependent_mem_smul_successiveMinimum Λ hB₀ hB₁ hB₂ hB₃ hB₄

open scoped Classical in
/-- **Layer 4.2**, landed: **the three comparisons with the real minima**, `λ l ≤ μ l`,
`μ l ≤ λ (d (l - 1) + 1)` — the extraction lemma — and `λ (d l) ≤ c_K μ l`, read from `0`. -/
example (Λ : Submodule (𝓞 K) (ι → K)) [DiscreteTopology Λ.mixedImage]
    [IsZLattice ℝ Λ.mixedImage] {B : Set (ι → mixedEmbedding.mixedSpace K)} (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B)
    (hBbal : ∀ z ∈ B, ∀ a : mixedEmbedding.mixedSpace K,
      (∀ w, mixedEmbedding.normAtPlace w a ≤ 1) → (fun j ↦ a * z j) ∈ B)
    {i : ℕ} (hi : i < Fintype.card ι) :
    ZLattice.successiveMinimum Λ.mixedImage B i ≤ successiveMinimum Λ B i ∧
      successiveMinimum Λ B i ≤ ZLattice.successiveMinimum Λ.mixedImage B (finrank ℚ K * i) ∧
      ZLattice.successiveMinimum Λ.mixedImage B (finrank ℚ K * (i + 1) - 1) ≤
        integralBasisHouse K * successiveMinimum Λ B i :=
  ⟨NumberField.successiveMinimum_mixedImage_le Λ hB₀ hB₁ hB₂ hB₃ hi,
    NumberField.successiveMinimum_le_successiveMinimum_mixedImage Λ hB₀ hB₁ hB₂ hB₃ hi,
    NumberField.successiveMinimum_mixedImage_le_mul Λ hB₀ hB₁ hB₂ hB₃ hBbal hi⟩

open scoped Classical in
/-- **Layer 4.2**, landed: **Minkowski's second theorem over `K`, both halves**, stated
multiplicatively and for any Haar measure (Bombieri–Gubler, Theorem C.2.11, in the generality the
Subspace Theorem uses). -/
example (Λ : Submodule (𝓞 K) (ι → K)) [DiscreteTopology Λ.mixedImage]
    [IsZLattice ℝ Λ.mixedImage] (μ : MeasureTheory.Measure (ι → mixedEmbedding.mixedSpace K))
    [μ.IsAddHaarMeasure] {B : Set (ι → mixedEmbedding.mixedSpace K)} (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B)
    (hBbal : ∀ z ∈ B, ∀ a : mixedEmbedding.mixedSpace K,
      (∀ w, mixedEmbedding.normAtPlace w a ≤ 1) → (fun j ↦ a * z j) ∈ B) :
    2 ^ (finrank ℚ K * Fintype.card ι) / (finrank ℚ K * Fintype.card ι).factorial *
        ZLattice.covolume Λ.mixedImage μ ≤
      integralBasisHouse K ^ (finrank ℚ K * Fintype.card ι) *
        (∏ i ∈ Finset.range (Fintype.card ι), successiveMinimum Λ B i) ^ finrank ℚ K *
          (μ B).toReal ∧
    (∏ i ∈ Finset.range (Fintype.card ι), successiveMinimum Λ B i) ^ finrank ℚ K *
        (μ B).toReal ≤
      2 ^ (finrank ℚ K * Fintype.card ι) * ZLattice.covolume Λ.mixedImage μ :=
  ⟨NumberField.covolume_le_prod_successiveMinimum_pow_mul_measure Λ μ hB₀ hB₁ hB₂ hB₃ hBbal,
    NumberField.prod_successiveMinimum_pow_mul_measure_le Λ μ hB₀ hB₁ hB₂ hB₃⟩

open scoped Classical in
/-- **Layer 4.2**, landed: **for an approximation domain, `(μ 0 ⋯ μ n) ^ d` is `Q ^ (-weight)` up
to two constants** depending on `K`, `Sfin`, `#ι` and the determinants only. The lower bound is the
form Layer 4.3 consumes. -/
example {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : 0 < Q) :
    2 ^ (finrank ℚ K * Fintype.card ι) / ((finrank ℚ K * Fintype.card ι).factorial *
        integralBasisHouse K ^ (finrank ℚ K * Fintype.card ι) * approxConst Sfin L) *
        Q ^ (-approxWeight Sfin c) ≤
      (∏ i ∈ Finset.range (Fintype.card ι),
        successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) i) ^ finrank ℚ K ∧
    (∏ i ∈ Finset.range (Fintype.card ι),
        successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) i) ^ finrank ℚ K ≤
      2 ^ (finrank ℚ K * Fintype.card ι) *
        (∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ Fintype.card ι) /
          approxConst Sfin L * Q ^ (-approxWeight Sfin c) :=
  ⟨NumberField.le_prod_successiveMinimum_approx hLInf hLFin c hQ,
    NumberField.prod_successiveMinimum_approx_le hLInf hLFin c hQ⟩

/-! ### Layer 4.3 — landed

Discharged by `DiophantineApproximation/ApproximationRank.lean`. Nothing of 4.3 was prototyped
here, so every statement below is prototyped for the first time. ⚠ Lemma 7.5.12 is stated along
the levels, with `∀ᶠ Q in atTop`, and not along a sequence of solutions; see the preamble. -/

/-- **Layer 4.3**, landed: `V(Q)`, the span of the approximation domain (Bombieri–Gubler,
Definition 7.5.11); its dimension is the rank. -/
example (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) :
    approxSpan Sfin L c Q = Submodule.span K (approxDomain Sfin L c Q) := rfl

open scoped Classical Pointwise in
/-- **Layer 4.3**, landed: **the rank is the number of minima at most `1`**, and `V(Q)` is spanned
by the vectors realizing them, for any family realizing the minima. -/
example {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : 0 < Q) {x : Fin (Fintype.card ι) → ι → K} (hxind : LinearIndependent K x)
    (hx : ∀ k, x k ∈ approxModule Sfin L c Q ∧ (fun j ↦ mixedEmbedding K (x k j)) ∈
      successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) k • approxBody L c Q) :
    finrank K (approxSpan Sfin L c Q) = {i ∈ Finset.range (Fintype.card ι) |
      successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) i ≤ 1}.card ∧
    approxSpan Sfin L c Q = Submodule.span K
      (x '' {k | successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) k ≤ 1}) :=
  ⟨NumberField.finrank_approxSpan hLInf hLFin c hQ,
    NumberField.approxSpan_eq_span_image hLInf hLFin c hQ hxind hx⟩

open scoped Classical in
/-- **Layer 4.3**, landed: **Bombieri–Gubler, Lemma 7.5.12, in parametric form** — for exponents
of negative weight the rank is at most `n`, and `V(Q)` a proper subspace, at every large enough
level. -/
example {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {c : AbsoluteValue K ℝ → ι → ℝ}
    (hc : approxWeight Sfin c < 0) :
    (∀ᶠ Q in Filter.atTop, finrank K (approxSpan Sfin L c Q) < Fintype.card ι) ∧
      ∀ᶠ Q in Filter.atTop, approxSpan Sfin L c Q ≠ ⊤ :=
  ⟨NumberField.eventually_finrank_approxSpan_lt hLInf hLFin hc,
    NumberField.eventually_approxSpan_ne_top hLInf hLFin hc⟩

/-- **Layer 4.3**, landed: **a bounded range of levels contributes finitely many subspaces
`V(Q)`**; `0 < Q₁` is needed, since the bounds with negative exponent blow up as `Q → 0`. -/
example {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ)
    {Q₁ Q₂ : ℝ} (hQ₁ : 0 < Q₁) : (approxSpan Sfin L c '' Set.Icc Q₁ Q₂).Finite :=
  NumberField.finite_image_approxSpan hLInf hLFin c hQ₁

/-! ### Layer 4.4 — landed

Discharged by `DiophantineApproximation/{SIntegerApproximation,EvertseLemma}.lean`. Nothing of 4.4
was prototyped here, so every statement below is prototyped for the first time. ⚠ The constant is
chosen before the forms, and the forms carry weights; see the preamble. -/

/-- **Layer 4.4**, landed: **simultaneous approximation by `Sfin`-integers**, without completions —
the constant `A` depends only on `K`. -/
example : ∃ A : ℝ, 0 ≤ A ∧ ∀ (Sfin : Finset (FinitePlace K)) (γ : AbsoluteValue K ℝ → K),
    ∃ ξ : K, (∀ v : FinitePlace K, v ∉ Sfin → v ξ ≤ 1) ∧ (∀ v ∈ Sfin, v (ξ + γ v.1) ≤ 1) ∧
      ∀ w : InfinitePlace K, w (ξ + γ w.1) ≤ A :=
  NumberField.exists_forall_apply_add_le

/-- **Layer 4.4**, landed: **Evertse's lemma** (Bombieri–Gubler, Lemma 7.5.29), with a weight per
form and a constant depending only on `K` and `#ι`. -/
example : ∃ C : ℝ, 0 < C ∧
    ∀ (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)),
    (∀ w : InfinitePlace K, LinearIndependent K (L w.1)) →
    (∀ v ∈ Sfin, LinearIndependent K (L v.1)) →
    ∀ (x : Fin (Fintype.card ι) → ι → K), LinearIndependent K x →
    ∀ (μ : AbsoluteValue K ℝ → Fin (Fintype.card ι) → ℝ) (ν : AbsoluteValue K ℝ → ι → ℝ),
    (∀ v, Monotone (μ v)) → (∀ v i, 0 < ν v i) →
    (∀ (w : InfinitePlace K) i j, w (L w.1 i (x j)) ≤ ν w.1 i * μ w.1 j) →
    (∀ v ∈ Sfin, ∀ i j, v (L v.1 i (x j)) ≤ ν v.1 i * μ v.1 j) →
    ∃ ξ : Fin (Fintype.card ι) → Fin (Fintype.card ι) → K,
      (∀ i j, ∀ v : FinitePlace K, v ∉ Sfin → v (ξ i j) ≤ 1) ∧
      ∃ π : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι,
        (∀ (w : InfinitePlace K) i j,
          w (L w.1 (π w.1 i) (x j + ∑ l ∈ Finset.Iio j, ξ j l • x l)) ≤
            C * ν w.1 (π w.1 i) * min (μ w.1 i) (μ w.1 j)) ∧
        ∀ v ∈ Sfin, ∀ i j,
          v (L v.1 (π v.1 i) (x j + ∑ l ∈ Finset.Iio j, ξ j l • x l)) ≤
            ν v.1 (π v.1 i) * min (μ v.1 i) (μ v.1 j) :=
  NumberField.exists_evertse K ι

/-- **Layer 4.4**, landed: **Evertse's lemma in the book's form**, the weights `1`. -/
example : ∃ C : ℝ, 0 < C ∧
    ∀ (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)),
    (∀ w : InfinitePlace K, LinearIndependent K (L w.1)) →
    (∀ v ∈ Sfin, LinearIndependent K (L v.1)) →
    ∀ (x : Fin (Fintype.card ι) → ι → K), LinearIndependent K x →
    ∀ μ : AbsoluteValue K ℝ → Fin (Fintype.card ι) → ℝ, (∀ v, Monotone (μ v)) →
    (∀ (w : InfinitePlace K) i j, w (L w.1 i (x j)) ≤ μ w.1 j) →
    (∀ v ∈ Sfin, ∀ i j, v (L v.1 i (x j)) ≤ μ v.1 j) →
    ∃ ξ : Fin (Fintype.card ι) → Fin (Fintype.card ι) → K,
      (∀ i j, ∀ v : FinitePlace K, v ∉ Sfin → v (ξ i j) ≤ 1) ∧
      ∃ π : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι,
        (∀ (w : InfinitePlace K) i j,
          w (L w.1 (π w.1 i) (x j + ∑ l ∈ Finset.Iio j, ξ j l • x l)) ≤
            C * min (μ w.1 i) (μ w.1 j)) ∧
        ∀ v ∈ Sfin, ∀ i j,
          v (L v.1 (π v.1 i) (x j + ∑ l ∈ Finset.Iio j, ξ j l • x l)) ≤
            min (μ v.1 i) (μ v.1 j) :=
  NumberField.exists_evertse_unweighted K ι

/-! ### Layer 4.5 — landed

Discharged by `DiophantineApproximation/{WedgeForm,WedgeDomain}.lean`. Nothing of 4.5 was
prototyped here, so every statement below is prototyped for the first time. ⚠ The exterior power is
read in Plücker coordinates, and the wedge domain's exponents move with `Q`; see the preamble. -/

open exteriorPower in
/-- **Layer 4.5**, landed: **Laplace's identity** (Bombieri–Gubler (7.16)) — the wedge of `p` forms
on the wedge of `p` vectors is the determinant of the values. -/
example [LinearOrder ι] (p : ℕ) (l : Fin p → Dual K (ι → K)) (y : Fin p → ι → K) :
    wedgeForm p l (plucker p y) = (Matrix.of fun a b ↦ l a (y b)).det :=
  wedgeForm_plucker p l y

open exteriorPower in
/-- **Layer 4.5**, landed: **the wedges of independent forms are independent**, indexed by the
`p`-subsets. -/
example [LinearOrder ι] {l : ι → Dual K (ι → K)} (hl : LinearIndependent K l) (p : ℕ) :
    LinearIndependent K (wedgeForms l p) :=
  linearIndependent_wedgeForms hl p

open exteriorPower in
/-- **Layer 4.5**, landed: **Lemma 7.5.33** — the span of the wedges of a basis meeting the first
`k` indices depends only on the span of the first `k` vectors, and determines it. -/
example [LinearOrder ι] {x x' : Fin (Fintype.card ι) → ι → K} (hx : LinearIndependent K x)
    (hx' : LinearIndependent K x') {k p : ℕ} (h : k + p = Fintype.card ι) :
    wedgeSpan k p x = wedgeSpan k p x' ↔
      Submodule.span K (x '' {j | (j : ℕ) < k}) = Submodule.span K (x' '' {j | (j : ℕ) < k}) :=
  wedgeSpan_eq_wedgeSpan_iff hx hx' h

open exteriorPower in
open scoped Pointwise in
/-- **Layer 4.5**, landed: **Step VIII** (Bombieri–Gubler 7.5.30, (7.44)–(7.45)) — the wedges of
Evertse's vectors that meet the first `k` indices lie in the wedge domain, with a constant depending
only on `K` and `#ι`. -/
example [LinearOrder ι] : ∃ C : ℝ, 0 < C ∧
    ∀ (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)),
    (∀ w : InfinitePlace K, LinearIndependent K (L w.1)) →
    (∀ v ∈ Sfin, LinearIndependent K (L v.1)) →
    ∀ (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ), 1 < Q →
    ∀ (x : Fin (Fintype.card ι) → ι → K), LinearIndependent K x →
    ∀ μ : ℕ → ℝ, MonotoneOn μ (Set.Iio (Fintype.card ι)) →
    (∀ j < Fintype.card ι, 0 < μ j) →
    (∀ j, x j ∈ approxModule Sfin L c Q ∧
      (fun i ↦ mixedEmbedding K (x j i)) ∈ μ j • approxBody L c Q) →
    ∃ ξ : Fin (Fintype.card ι) → Fin (Fintype.card ι) → K,
      (∀ i j, ∀ v : FinitePlace K, v ∉ Sfin → v (ξ i j) ≤ 1) ∧
      ∃ π : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι, ∀ k p : ℕ,
        ∀ J : Set.powersetCard (Fin (Fintype.card ι)) p, (∃ j ∈ J, (j : ℕ) < k) →
          plucker p ((fun j ↦ x j + ∑ l ∈ Finset.Iio j, ξ j l • x l) ∘
              Set.powersetCard.ofFinEmbEquiv.symm J) ∈
            approxDomain Sfin (fun v ↦ wedgeForms (L v) p) (wedgeExponent c π μ C Q k p) Q :=
  NumberField.exists_plucker_mem_approxDomain_wedgeForms K ι

open exteriorPower in
/-- **Layer 4.5**, landed: **the weight of the wedge domain is a constant times the jump of the
minima**, the form Layer 6.1 consumes. -/
example [LinearOrder ι] {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (π : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι) {C Q : ℝ} {k p : ℕ} (hQ : 1 < Q)
    (hC : 0 < C) (h : k + p = Fintype.card ι) (hp : 0 < p) :
    Q ^ approxWeight Sfin (wedgeExponent c π
        (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)) C Q k p) ≤
      C ^ (Fintype.card (Set.powersetCard ι p) * finrank ℚ K) *
        (2 ^ (finrank ℚ K * Fintype.card ι) *
          (∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ Fintype.card ι) /
            approxConst Sfin L) ^ (Fintype.card ι - 1).choose (p - 1) *
        (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) (k - 1) /
          successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) k) ^ finrank ℚ K :=
  NumberField.rpow_approxWeight_wedgeExponent_le hLInf hLFin c π hQ hC h hp

open exteriorPower in
open scoped Pointwise in
/-- **Layer 4.5**, landed: **Bombieri–Gubler, Lemma 7.5.31, with the choice of `k`** — every
minimum of the wedge domain but the last is at most `1`, and the last to the power `d #ι (#ι - R)`
is at least a constant times `Q ^ (-weight)`. -/
example [LinearOrder ι] : ∃ C : ℝ, 0 < C ∧
    ∀ (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)),
    (∀ w : InfinitePlace K, LinearIndependent K (L w.1)) →
    (∀ v ∈ Sfin, LinearIndependent K (L v.1)) →
    ∃ A : ℝ, 0 < A ∧ ∀ (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ), 1 < Q →
    0 < finrank K (approxSpan Sfin L c Q) → finrank K (approxSpan Sfin L c Q) < Fintype.card ι →
    ∀ x : Fin (Fintype.card ι) → ι → K, LinearIndependent K x →
    (∀ j, x j ∈ approxModule Sfin L c Q ∧ (fun i ↦ mixedEmbedding K (x j i)) ∈
      successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) j • approxBody L c Q) →
    ∃ k, finrank K (approxSpan Sfin L c Q) ≤ k ∧ k < Fintype.card ι ∧
    ∃ ξ : Fin (Fintype.card ι) → Fin (Fintype.card ι) → K,
      (∀ i j, ∀ v : FinitePlace K, v ∉ Sfin → v (ξ i j) ≤ 1) ∧
      ∃ π : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι,
        (∀ J : Set.powersetCard (Fin (Fintype.card ι)) (Fintype.card ι - k),
          (∃ j ∈ J, (j : ℕ) < k) →
          plucker (Fintype.card ι - k) ((fun j ↦ x j + ∑ l ∈ Finset.Iio j, ξ j l • x l) ∘
              Set.powersetCard.ofFinEmbEquiv.symm J) ∈
            approxDomain Sfin (fun v ↦ wedgeForms (L v) (Fintype.card ι - k)) (wedgeExponent c π
              (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)) C Q k
                (Fintype.card ι - k)) Q) ∧
        (∀ m < Fintype.card (Set.powersetCard ι (Fintype.card ι - k)) - 1,
          successiveMinimum (approxModule Sfin (fun v ↦ wedgeForms (L v) (Fintype.card ι - k))
              (wedgeExponent c π (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q))
                C Q k (Fintype.card ι - k)) Q)
            (approxBody (fun v ↦ wedgeForms (L v) (Fintype.card ι - k)) (wedgeExponent c π
              (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)) C Q k
                (Fintype.card ι - k)) Q) m ≤ 1) ∧
        A * Q ^ (-approxWeight Sfin c) ≤
          successiveMinimum (approxModule Sfin (fun v ↦ wedgeForms (L v) (Fintype.card ι - k))
              (wedgeExponent c π (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q))
                C Q k (Fintype.card ι - k)) Q)
            (approxBody (fun v ↦ wedgeForms (L v) (Fintype.card ι - k)) (wedgeExponent c π
              (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)) C Q k
                (Fintype.card ι - k)) Q)
            (Fintype.card (Set.powersetCard ι (Fintype.card ι - k)) - 1) ^
              (finrank ℚ K * Fintype.card ι *
                (Fintype.card ι - finrank K (approxSpan Sfin L c Q))) :=
  NumberField.exists_successiveMinimum_wedge_pow K ι

/-! ### Layer 5.1 — landed

Discharged by `DiophantineApproximation/{UnitNormalization,SubspaceReduction}.lean`. Nothing of
5.1 was prototyped here, so every statement below is prototyped for the first time. ⚠ The
approximation classes of 7.5.6 are cells of a cube and reuse nothing from Layer 3.1; see the
preamble. -/

/-- **Layer 5.1**, landed: **Bombieri–Gubler, Theorem 7.2.6** — after enlarging `S₀` every nonzero
point has a **primitive** multiple, one whose local sup norms are `1` at every finite place
outside `S₀`. -/
example (Sfin : Finset (FinitePlace K)) :
    ∃ Sfin' : Finset (FinitePlace K), Sfin ⊆ Sfin' ∧
      ∀ {ι : Type*} [Finite ι] (x : ι → K), x ≠ 0 →
        ∃ t : K, t ≠ 0 ∧ ∀ v : FinitePlace K, v ∉ Sfin' → ⨆ i, v ((t • x) i) = 1 :=
  NumberField.exists_finset_superset_forall_exists_iSup_eq_one Sfin

/-- **Layer 5.1**, landed: **the height of a primitive point** is the product of its local sup
norms over the infinite places and `S₀`. -/
example {ι : Type*} (Sfin : Finset (FinitePlace K)) {x : ι → K} (hx : x ≠ 0)
    (h : ∀ v : FinitePlace K, v ∉ Sfin → ⨆ i, v (x i) = 1) :
    mulHeight x = (∏ w : InfinitePlace K, (⨆ i, w (x i)) ^ w.mult) * ∏ v ∈ Sfin, ⨆ i, v (x i) :=
  NumberField.mulHeight_eq_prod_of_forall_iSup_eq_one hx h

/-- **Layer 5.1**, landed: **Bombieri–Gubler, Lemma 7.5.4** — a primitive point has an `S₀`-unit
multiple whose affine height exceeds its projective height by at most a constant depending only on
`K` and `S₀`. ⚠ The constant comes before the index type: it does not depend on `n`. -/
example (Sfin : Finset (FinitePlace K)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} [Finite ι] (x : ι → K), x ≠ 0 →
      (∀ v : FinitePlace K, v ∉ Sfin → ⨆ i, v (x i) = 1) →
      ∃ u : K, u ≠ 0 ∧ (∀ v : FinitePlace K, v ∉ Sfin → v u = 1) ∧
        logHeight x ≤ logHeightAff (u • x) ∧ logHeightAff (u • x) ≤ logHeight x + C :=
  NumberField.exists_forall_logHeightAff_smul_le Sfin

/-- **Layer 5.1**, landed: **Bombieri–Gubler, Corollary 7.5.5** — the values of the forms at the
normalized point have height `h(x) + O(1)`. ⚠ No independence of the forms is needed. -/
example [Finite ι] (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ι → K, x ≠ 0 →
      (∀ v : FinitePlace K, v ∉ Sfin → ⨆ i, v (x i) = 1) →
      ∃ u : K, u ≠ 0 ∧ (∀ v : FinitePlace K, v ∉ Sfin → v u = 1) ∧
        (∀ (w : InfinitePlace K) (i : ι), logHeight₁ (L w.1 i (u • x)) ≤ logHeight x + C) ∧
        ∀ v ∈ Sfin, ∀ i : ι, logHeight₁ (L v.1 i (u • x)) ≤ logHeight x + C :=
  NumberField.exists_forall_logHeight₁_apply_smul_le Sfin L

/-- **Layer 5.1**, landed: **the book's (7.19)** — the fundamental inequality at one place, which
turns Corollary 7.5.5 into two-sided bounds on the local factors. -/
example (w : InfinitePlace K) {α : K} (hα : α ≠ 0) :
    |(w.mult : ℝ) * Real.log (w α)| ≤ logHeight₁ α :=
  NumberField.InfinitePlace.abs_mult_mul_log_le_logHeight₁ w hα

/-- **Layer 5.1**, landed: **Bombieri–Gubler, 7.5.6** — the approximation classes. Every solution
of large height with no vanishing form has a multiple in the approximation domain, at its own
height, of one of finitely many exponent systems, each of weight at most `-ε/2`. -/
example (Sfin : Finset (FinitePlace K))
    (hS : ∀ x : ι → K, x ≠ 0 → ∃ t : K, t ≠ 0 ∧
      ∀ v : FinitePlace K, v ∉ Sfin → ⨆ i, v ((t • x) i) = 1)
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ 𝒞 : Finset (AbsoluteValue K ℝ → ι → ℝ), (∀ c ∈ 𝒞, approxWeight Sfin c ≤ -ε / 2) ∧
      ∃ Q₀ : ℝ, ∀ x : ι → K, x ≠ 0 →
        (∀ (w : InfinitePlace K) (i : ι), L w.1 i x ≠ 0) → (∀ v ∈ Sfin, ∀ i, L v.1 i x ≠ 0) →
        approxProd Finset.univ Sfin (fun v ↦ v) L x ≤
          mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        Q₀ ≤ mulHeight x →
        ∃ c ∈ 𝒞, ∃ t : K, t ≠ 0 ∧ t • x ∈ approxDomain Sfin L c (mulHeight x) :=
  NumberField.exists_finset_forall_exists_smul_mem_approxDomain Sfin hS L hε

/-- **Layer 5.1**, landed: **the reduction as a whole** — what Layer 6.2 consumes. Every solution
of large height lies on the kernel of one of the forms, which are the given ones at the given
places and the coordinate forms elsewhere, or has a multiple in one of finitely many approximation
domains of negative weight. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (hLInf : ∀ v ∈ Sinf, LinearIndependent K (L v.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ Sfin' : Finset (FinitePlace K), Sfin ⊆ Sfin' ∧
      ∃ L' : AbsoluteValue K ℝ → ι → Dual K (ι → K),
        (∀ v ∈ Sinf, L' v.1 = L v.1) ∧ (∀ v ∈ Sfin, L' v.1 = L v.1) ∧
        (∀ w : InfinitePlace K, LinearIndependent K (L' w.1)) ∧
        (∀ v ∈ Sfin', LinearIndependent K (L' v.1)) ∧
        ∃ 𝒞 : Finset (AbsoluteValue K ℝ → ι → ℝ), (∀ c ∈ 𝒞, approxWeight Sfin' c ≤ -ε / 2) ∧
          ∃ Q₀ : ℝ, ∀ x : ι → K, x ≠ 0 →
            approxProd Sinf Sfin (fun v ↦ v) L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
            Q₀ ≤ mulHeight x →
            (∃ (w : InfinitePlace K) (i : ι), L' w.1 i x = 0) ∨
              (∃ v ∈ Sfin', ∃ i, L' v.1 i x = 0) ∨
              ∃ c ∈ 𝒞, ∃ t : K, t ≠ 0 ∧ t • x ∈ approxDomain Sfin' L' c (mulHeight x) :=
  NumberField.exists_forall_approxProd_le_imp Sinf Sfin L hLInf hLFin hε

/-! ### Layer 5.2 — landed

Discharged by `DiophantineApproximation/{MultiHomogeneous,MonomialDeviation,
SubspaceAuxiliary}.lean`. Nothing of 5.2 was prototyped here, so every statement below is
prototyped for the first time. ⚠ The chain rule is the content of the vanishing, the book's volume
computation is avoidable, the hypothesis on `m` is strict, and the upper half of the book's
interval is free; see the preamble. -/

/-- **Layer 5.2**, landed: **multihomogeneity and its monomials** (Bombieri–Gubler 7.5.14). A
polynomial in `m` blocks of `n + 1` variables is multihomogeneous of multidegree `d` when every
monomial has degree `d h` in the `h`-th block; those monomials are `MvPolynomial.multiMons d`, a
product over the blocks of the monomials of one degree, whence the dimension
`∏ h, (d h + n).choose n`. -/
example {κ : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι] (d : κ → ℕ) :
    (MvPolynomial.multiMons (ι := ι) d).card
      = (Fintype.piFinset fun h ↦ Finset.finsuppAntidiag (Finset.univ : Finset ι) (d h)).card :=
  MvPolynomial.card_multiMons d

/-- **Layer 5.2**, landed: **the block substitution is contravariant and preserves the
multidegree**, which is why the expansion coefficients `a(L v; J; I)` are read through `(A v)⁻¹`
and not through `A v`. -/
example {κ : Type*} [Finite κ] [DecidableEq ι] {d : κ → ℕ} {P : MvPolynomial (κ × ι) K}
    (hP : MvPolynomial.IsMultiHomogeneous d P) (A : Matrix ι ι K) (hA : IsUnit A.det) :
    MvPolynomial.IsMultiHomogeneous d (MvPolynomial.blockSubst A⁻¹ P) ∧
      MvPolynomial.blockSubst A (MvPolynomial.blockSubst A⁻¹ P) = P :=
  ⟨hP.blockSubst _, MvPolynomial.blockSubst_blockSubst (Matrix.nonsing_inv_mul _ hA) P⟩

/-- **Layer 5.2**, landed: **the key vanishing statement**, the chain rule in the only form the
milestone uses. A coefficient of the expansion of `∂_I P` vanishes as soon as the coefficients of
`P` read in the transformed coordinates vanish at every order `J + I'` with `I'` of the same block
degrees as `I`. ⚠ Characteristic zero is needed. -/
example {κ : Type*} [Fintype κ] [DecidableEq ι] {A M : Matrix ι ι K} (hAM : A * M = 1)
    (I : κ × ι →₀ ℕ) (Q : MvPolynomial (κ × ι) K) (J : κ × ι →₀ ℕ)
    (h : ∀ I' : κ × ι →₀ ℕ, (∀ h, ∑ i, I' (h, i) = ∑ i, I (h, i)) → Q.coeff (J + I') = 0) :
    (MvPolynomial.blockSubst M
        (MvPolynomial.hasseDeriv I (MvPolynomial.blockSubst A Q))).coeff J = 0 :=
  MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero hAM _ I rfl Q J h

/-- **Layer 5.2**, landed: **the counting** — the monomials of multidegree `d` whose exponent of
one variable lies below `m/(n+1) − m η` are fewer than the total by a factor
`exp (−(n+1)(n+2) η² m / 4)`, up to one explicit error term. ⚠ The book's volume computation is
not needed and the restriction `0 < λ ≤ n + 4` disappears. -/
example {κ : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι] {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card ι = n + 1) (i₀ : ι) {d : κ → ℕ} (hd : ∀ h, 1 ≤ d h) {η : ℝ}
    (hη : 0 ≤ η) (E : Finset (κ × ι →₀ ℕ)) (hE : E ⊆ MvPolynomial.multiMons d)
    (hEθ : ∀ N ∈ E, ∑ h, (N (h, i₀) : ℝ) / (d h : ℝ)
      ≤ Fintype.card κ / ((n : ℝ) + 1) - Fintype.card κ * η) :
    (E.card : ℝ) ≤ (MvPolynomial.multiMons (ι := ι) d).card *
      Real.exp (-(((n : ℝ) + 1) * ((n : ℝ) + 2) * η ^ 2 * Fintype.card κ / 4)
        + (η * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2) ^ 2 / (2 * ((n : ℝ) + 1))
          * ∑ h, ((d h : ℝ))⁻¹) :=
  MvPolynomial.card_le_of_subset_multiMons hn hcard i₀ hd hη E hE hEθ

/-- **Layer 5.2**, landed: **Siegel's lemma in the multihomogeneous setting**. At most half as
many linear conditions as monomials give a nonzero multihomogeneous polynomial satisfying them
all, of logarithmic height a constant times `∑ h, d h`. ⚠ With coefficients in `K` the book's
`r = [F : K]` is `1` and its relative Siegel lemma is the absolute one; `y` is one reference tuple
dominating the entries of every matrix and `1`. -/
example {κ : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι] [Nonempty ι] {d : κ → ℕ}
    {Row ρ : Type*} [Fintype Row] [Finite ρ] (Mat : Row → Matrix ι ι K)
    (Nrow : Row → (κ × ι →₀ ℕ)) {y : ρ → K} (hy : y ≠ 0)
    (hMy : ∀ (r : Row) (w : AbsoluteValue K ℝ),
      (⨆ p : ι × ι, w (Mat r p.1 p.2)) ⊔ 1 ≤ ⨆ s, w (y s))
    (hrow : 2 * (Fintype.card Row : ℝ) ≤ (MvPolynomial.multiMons (ι := ι) d).card) :
    ∃ P : MvPolynomial (κ × ι) K, P ≠ 0 ∧ MvPolynomial.IsMultiHomogeneous d P ∧
      (∀ r : Row, (MvPolynomial.blockSubst (Mat r) P).coeff (Nrow r) = 0) ∧
      P.logHeight ≤ 2⁻¹ * Real.log |(NumberField.discr K : ℝ)|
        + ((Module.finrank ℚ K : ℝ) / 2 * Fintype.card ι
            + Height.totalWeight K * Real.log (Fintype.card ι)
            + Real.log (Height.mulHeight y)) * ∑ h, (d h : ℝ) :=
  MvPolynomial.exists_ne_zero_isMultiHomogeneous_coeff_blockSubst_eq_zero Mat Nrow hy hMy hrow

/-- **Layer 5.2**, landed: **the milestone** (Bombieri–Gubler, Lemma 7.5.15). For every
multidegree all of whose entries are large enough there is a nonzero multihomogeneous polynomial
of logarithmic height `O (∑ h, d h)` whose Hasse derivatives, read in any of the coordinate
systems `A v`, again have logarithmic height `O (∑ h, d h)` and have a vanishing coefficient at
`J` whenever the order is small and one exponent of `J` is far from its mean. ⚠ The hypothesis on
`m` is strict, and `C₂`, `C₃` may depend on `m`, `S` and `η`. -/
example {κ : Type*} [Fintype κ] [Nonempty κ] [DecidableEq ι] [Nonempty ι] {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card ι = n + 1) {S : Type*} [Fintype S] [Nonempty S]
    (A : S → Matrix ι ι K) (hA : ∀ v, IsUnit (A v).det) {η : ℝ} (hη : 0 < η)
    (hm : 4 * Real.log (2 * ((n : ℝ) + 1) * Fintype.card S)
      < ((n : ℝ) + 1) * ((n : ℝ) + 2) * η ^ 2 * Fintype.card κ) :
    ∃ C₂ C₃ : ℝ, ∃ D₀ : ℕ, ∀ d : κ → ℕ, (∀ h, D₀ ≤ d h) →
      ∃ P : MvPolynomial (κ × ι) K, P ≠ 0 ∧ MvPolynomial.IsMultiHomogeneous d P ∧
        P.logHeight ≤ C₂ * ∑ h, (d h : ℝ) ∧
        (∀ (v : S) (I : κ × ι →₀ ℕ),
          (MvPolynomial.blockSubst (A v)⁻¹ (MvPolynomial.hasseDeriv I P)).logHeight
            ≤ C₃ * ∑ h, (d h : ℝ)) ∧
        ∀ (v : S) (I J : κ × ι →₀ ℕ),
          ∑ h, (∑ i, (I (h, i) : ℝ)) / (d h : ℝ) ≤ Fintype.card κ * η →
          (∃ i, ∑ h, (J (h, i) : ℝ) / (d h : ℝ)
                ≤ Fintype.card κ / ((n : ℝ) + 1) - 2 * Fintype.card κ * η ∨
              Fintype.card κ / ((n : ℝ) + 1) + 2 * (n : ℝ) * Fintype.card κ * η
                ≤ ∑ h, (J (h, i) : ℝ) / (d h : ℝ)) →
          (MvPolynomial.blockSubst (A v)⁻¹ (MvPolynomial.hasseDeriv I P)).coeff J = 0 :=
  MvPolynomial.exists_ne_zero_isMultiHomogeneous_forall_coeff_blockSubst_hasseDeriv_eq_zero
    hn hcard A hA hη hm

/-! ### Layer 5.3 — landed

Discharged by `DiophantineApproximation/{FormIndex,FormSpecialization,
GeneralizedRothLemma}.lean`. Nothing of 5.3 was prototyped here, so every statement below is
prototyped for the first time. ⚠ The index along the forms is a weighted order, the variables
have to be specialized one at a time, only half of the book's specialization claim is proved and
only half is needed, and the second kept coordinate need not be one where the form survives; see
the preamble. -/

/-- **Layer 5.3**, landed: **the index along the forms is a weighted order** (Bombieri–Gubler,
Definition 7.5.17). Solving `M h = X (h, i₀ h)` for one coordinate at which the form survives
turns the ideal `I(t; d; M)` into a monomial ideal, and the index becomes the weighted order of
Layer 2.3 for the weights that see only the coordinates `i₀ h`. -/
example {κ : Type*} [Fintype κ] [DecidableEq ι] {d : κ → ℝ} (hd : ∀ h, 0 ≤ d h) {i₀ : κ → ι}
    {M : κ → ι → K} (hM : ∀ h, M h (i₀ h) ≠ 0) (P : MvPolynomial (κ × ι) K) :
    MvPolynomial.formIndex d M P
      = MvPolynomial.weightedOrder (MvPolynomial.formWeight i₀ d)
          (MvPolynomial.substFormInv i₀ M P) :=
  MvPolynomial.formIndex_eq_weightedOrder hd hM P

/-- **Layer 5.3**, landed: **the index is a valuation**, as in Layer 2.3 — here multiplicativity,
which over a field needs nothing but the nonvanishing of the forms. -/
example {κ : Type*} [Fintype κ] [DecidableEq ι] {d : κ → ℝ} (hd : ∀ h, 0 ≤ d h)
    {M : κ → ι → K} (hM : ∀ h, M h ≠ 0) (P Q : MvPolynomial (κ × ι) K) :
    MvPolynomial.formIndex d M (P * Q)
      = MvPolynomial.formIndex d M P + MvPolynomial.formIndex d M Q :=
  MvPolynomial.formIndex_mul hd hM P Q

/-- **Layer 5.3**, landed: **Bombieri–Gubler 7.5.18** — for `n = 1` and the forms
`M h = X (h, 1) − α h * X (h, 0)` the index along the forms is the index of Layer 2.3 at the
point `α` of the dehomogenization. -/
example {m : ℕ} (α : Fin (m + 1) → K) {d : Fin (m + 1) → ℝ} (hd : ∀ h, 0 ≤ d h)
    {r : Fin (m + 1) → ℕ} {Q : MvPolynomial (Fin (m + 1) × Fin 2) K}
    (hQ : MvPolynomial.IsMultiHomogeneous r Q) :
    MvPolynomial.formIndex d (fun h ↦ ![-(α h), 1]) Q
      = MvPolynomial.index d α (MvPolynomial.deHom (fun _ ↦ 1) (fun _ ↦ 0) Q) := by
  have hvac : ∀ i : Fin 2, i ≠ 1 → i ≠ 0 → False := by decide
  have key := MvPolynomial.formIndex_eq_index_deHom (M := fun h ↦ ![-(α h), (1 : K)])
    (fun _ : Fin (m + 1) ↦ (1 : Fin 2)) (fun _ ↦ (0 : Fin 2)) hd (fun _ ↦ by decide)
    (fun _ ↦ by simp) (fun _ i h0 h1 ↦ (hvac i h0 h1).elim) hQ
    (fun _ i h0 h1 ↦ (hvac i h0 h1).elim)
  have hα : (fun h ↦ -((![-(α h), (1 : K)] : Fin 2 → K) 0)) = α := by
    funext h
    simp
  rw [hα] at key
  exact key

/-- **Layer 5.3**, landed: **the specialization to two coordinates in every block**. Dividing out
the largest power of a variable and setting it to zero, one variable at a time, leaves a nonzero
multihomogeneous polynomial of a smaller multidegree whose coefficients are coefficients of `P`
— so its height cannot go up — and whose index along the truncated forms is at least that of
`P`. ⚠ The book's equality of indices is not proved and is not needed. -/
example {κ : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι] {d : κ → ℝ} (hd : ∀ h, 0 ≤ d h)
    {i₀ : κ → ι} (T : Finset (κ × ι)) (hT : ∀ t ∈ T, t.2 ≠ i₀ t.1) (M : κ → ι → K)
    (hM : ∀ h, M h (i₀ h) ≠ 0) (r : κ → ℕ) (P : MvPolynomial (κ × ι) K) (hP0 : P ≠ 0)
    (hP : MvPolynomial.IsMultiHomogeneous r P) :
    ∃ (k : κ × ι →₀ ℕ) (Q : MvPolynomial (κ × ι) K),
      (∀ s, s ∉ T → k s = 0) ∧ Q ≠ 0 ∧
        (∀ ν, Q.coeff ν ≠ 0 → Q.coeff ν = P.coeff (ν + k)) ∧
        (∀ t ∈ T, ∀ ν ∈ Q.support, ν t = 0) ∧
        (∃ r' : κ → ℕ, (∀ h, r' h ≤ r h) ∧ MvPolynomial.IsMultiHomogeneous r' Q) ∧
        MvPolynomial.formIndex d M P
          ≤ MvPolynomial.formIndex d (MvPolynomial.zeroOut T M) Q :=
  MvPolynomial.exists_elimination hd T hT M hM r P hP0 hP

/-- **Layer 5.3**, landed: **the milestone** (Bombieri–Gubler, Lemma 7.5.19). A nonzero
multihomogeneous polynomial of multidegree at most `d`, with degrees dropping by a factor `σ` at
every step and forms whose heights are large against its own, has index at most
`2 (m + 1) σ ^ ((1/2) ^ m)` along the forms. ⚠ Heights are Mathlib's relative ones, so the
constant term carries `totalWeight K`, exactly as in Layer 2.7. -/
example [DecidableEq ι] {n m : ℕ} (hn : 1 ≤ n) (hcard : Fintype.card ι = n + 1)
    {d : Fin (m + 1) → ℕ} (hd1 : ∀ h, 1 ≤ d h) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 2)
    (hratio : ∀ h : Fin m, (d h.succ : ℝ) ≤ σ * d h.castSucc)
    {r : Fin (m + 1) → ℕ} {P : MvPolynomial (Fin (m + 1) × ι) K} (hP0 : P ≠ 0)
    (hP : MvPolynomial.IsMultiHomogeneous r P) (hrd : ∀ h, r h ≤ d h)
    {M : Fin (m + 1) → ι → K} (hM : ∀ h, M h ≠ 0)
    (hheight : ∀ h, (n : ℝ) * σ⁻¹ * (P.logHeight + 4 * (m + 1) * d 0 * Height.totalWeight K)
      ≤ d h * Height.logHeight (M h)) :
    MvPolynomial.formIndex (fun h ↦ (d h : ℝ)) M P
      ≤ ENNReal.ofReal (2 * ((m : ℝ) + 1) * σ ^ ((1 / 2 : ℝ) ^ m)) :=
  MvPolynomial.formIndex_le_of_degree_ratio hn hcard hd1 hσ0 hσ1 hratio hP0 hP hrd hM hheight

/-! ### Layer 5.4 — landed

Discharged by `DiophantineApproximation/{LinearFormValue,SubspaceNormal,SubspaceHeightBounds,
ExceptionalSubspace}.lean`. Nothing of 5.4 was prototyped here, so every statement below is
prototyped for the first time. ⚠ The book's bound on the height of the single number
`L̂_{v i}(w)` is false as stated and is replaced by a product-formula inequality that is
stronger; there is one exceptional subspace **per pattern**, not one; and the pattern is an
intersection of spans of coefficient vectors, so no Hodge star and no adjugate appears. See the
preamble. -/

/-- **Layer 5.4**, landed: **Liouville's inequality for the value of a linear form**. This
replaces Bombieri–Gubler's `h(L̂_{v i}(w)) ≤ h(V(Q)) + C₇`, which compares a scale-dependent
left-hand side with a scale-invariant right-hand side and is false: over `ℚ` the vector
`w = (N, 0)` has `h(V) = 0` and `h(w 0) = log N`. What is true, and what Step III needs, is that
the **local factor** of the point is controlled by its **projective** height. -/
example {σ : Type*} [Fintype σ] [Nonempty σ] (w : InfinitePlace K) (a z : σ → K)
    (hD : ∑ s, a s * z s ≠ 0) :
    ((⨆ s, w (a s)) * ⨆ s, w (z s)) ^ w.mult
      ≤ (Fintype.card σ : ℝ) ^ Height.totalWeight K
        * (Height.mulHeight a * Height.mulHeight z) * w (∑ s, a s * z s) ^ w.mult :=
  NumberField.InfinitePlace.iSup_mul_iSup_pow_mult_le w a z hD

/-- **Layer 5.4**, landed: **the normal vector of a hyperplane and its vanishing dictionary**.
A subspace of `Kⁿ⁺¹` of dimension `n` is the kernel of a single vector, and the Plücker
coordinate of a basis at the `n`-subset omitting `i` vanishes exactly when the `i`-th coordinate
of that vector does. This is Layer 3.5's Plücker duality at the ranks `n` and `1`, and it is what
identifies the pattern of `V(Q)` with the pattern of its normal vector. -/
example [LinearOrder ι] {n : ℕ} {V : Submodule K (ι → K)} {y : Fin n → ι → K}
    (hy : LinearIndependent K y) (hVy : Submodule.span K (Set.range y) = V)
    (hlk : 1 + n = Fintype.card ι) :
    ∃ ζ : ι → K, ζ ≠ 0 ∧ (∀ x, x ∈ V ↔ ζ ⬝ᵥ x = 0) ∧
      ∀ k : ι, (exteriorPower.plucker n y (Set.powersetCard.omitOne hlk k) = 0 ↔ ζ k = 0) :=
  Submodule.exists_normal hy hVy hlk

/-- **Layer 5.4**, landed: **the exceptional alternative**. The exceptional subspaces are the
kernels of vectors chosen one per **pattern** — the family, over the places of `S`, of the sets
of indices at which the wedge of the other forms survives on the Plücker point. There are
finitely many patterns, so finitely many exceptional subspaces, and each is fixed before `Q` is
chosen. ⚠ The book's "a linear space `W`" is one space per pattern. -/
example [LinearOrder ι] [Nonempty ι] {n : ℕ} {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Module.Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ}
    (hlk : 1 + n = Fintype.card ι)
    (hLinf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLfin : ∀ w ∈ S₀, LinearIndependent K (L w.1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (𝒲 : Set (Submodule K (ι → K))) (C₄ : ℝ), 𝒲.Finite ∧
      ∀ Q : ℝ, 1 ≤ Q → C₄ / ε ≤ Real.log Q →
      ∀ y : Fin n → ι → K, LinearIndependent K y →
        (∀ j, y j ∈ NumberField.approxDomain S₀ L c Q) →
        ∀ k : AbsoluteValue K ℝ → ι,
          (∀ (w : InfinitePlace K) (i : ι),
             exteriorPower.plucker n (fun j i' ↦ L w.1 i' (y j))
               (Set.powersetCard.omitOne hlk i) ≠ 0 → c w.1 i ≤ c w.1 (k w.1)) →
          (∀ w ∈ S₀, ∀ i : ι,
             exteriorPower.plucker n (fun j i' ↦ L w.1 i' (y j))
               (Set.powersetCard.omitOne hlk i) ≠ 0 → c w.1 i ≤ c w.1 (k w.1)) →
          NumberField.weightAt S₀ c k < -ε / 4 →
          Submodule.span K (Set.range y) ∈ 𝒲 :=
  NumberField.exists_finite_forall_mem_of_weightAt_lt hlk hLinf hLfin hε

/-- **Layer 5.4**, landed: **the milestone** (Bombieri–Gubler, Lemma 7.5.21). For exponents of
weight at most `−ε/2` there are a finite set of subspaces and three constants, none of them
depending on `Q`, such that at every level of rank `n` with `log Q ≥ C₄/ε` the span of the domain
is exceptional or its height is a positive multiple of `ε log Q` up to a constant, and at most a
multiple of `log Q`. ⚠ The lower bound's `(4 |S|)⁻¹` counts the places of `S` without
multiplicity: in Mathlib's normalization the local degrees sit inside the local factors, and the
upper bound reads `n ∑_{v ∈ S} d_v c_max(v)` where the book reads `n c_max |S|`. -/
example [LinearOrder ι] [Nonempty ι] {n : ℕ} {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Module.Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ}
    (hlk : 1 + n = Fintype.card ι)
    (hLinf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLfin : ∀ w ∈ S₀, LinearIndependent K (L w.1))
    {ε : ℝ} (hε : 0 < ε) (hweight : NumberField.approxWeight S₀ c ≤ -ε / 2) :
    ∃ (𝒲 : Set (Submodule K (ι → K))) (C₄ C₅ C₆ : ℝ), 𝒲.Finite ∧
      ∀ Q : ℝ, 1 ≤ Q → C₄ / ε ≤ Real.log Q →
        Module.finrank K (NumberField.approxSpan S₀ L c Q) = n →
          NumberField.approxSpan S₀ L c Q ∈ 𝒲 ∨
            (ε * Real.log Q / (4 * (Fintype.card (InfinitePlace K) + S₀.card : ℕ))
                  - C₅ ≤ (NumberField.approxSpan S₀ L c Q).logHeight ∧
              (NumberField.approxSpan S₀ L c Q).logHeight
                ≤ (n : ℝ) * (∑ w : InfinitePlace K, (w.mult : ℝ) * NumberField.cMax c w.1
                    + ∑ w ∈ S₀, NumberField.cMax c w.1) * Real.log Q + C₆) :=
  NumberField.exists_finite_forall_logHeight_approxSpan hlk hLinf hLfin hε hweight

/-! ### Layer 5.5 — landed

Discharged by `DiophantineApproximation/{PolynomialGrid,SmallPoint}.lean`. Nothing of 5.5 was
prototyped here, so every statement below is prototyped for the first time. ⚠ The one-variable
grid lemma is a count of roots with multiplicity and not a divisibility, and the chain rule the
book invokes to read the derivative back through the parametrization is not needed: only the
block degrees of the orders that can occur, which is multihomogeneity. See the preamble. -/

/-- **Layer 5.5**, landed: **the grid lemma** (Bombieri–Gubler, Lemma 7.5.24). A nonzero
polynomial over a field of characteristic zero, of degree at most `e j` in the variable `X j`,
has a Hasse derivative of order at most `e j / B` in each variable that does not vanish at some
point of the grid of integers `|z j| ≤ B`. -/
example {k : Type*} [Field k] [CharZero k] {σ : Type*} [Finite σ]
    {f : MvPolynomial σ k} (hf : f ≠ 0) {e : σ → ℕ} (he : ∀ j, f.degreeOf j ≤ e j)
    {B : ℕ} (hB : 0 < B) :
    ∃ z : σ → ℤ, (∀ j, (z j).natAbs ≤ B) ∧ ∃ i : σ →₀ ℕ, (∀ j, B * i j ≤ e j) ∧
      MvPolynomial.eval (fun j ↦ ((z j : k))) (MvPolynomial.hasseDeriv i f) ≠ 0 :=
  MvPolynomial.exists_eval_hasseDeriv_ne_zero hf he hB

/-- **Layer 5.5**, landed: **non-vanishing at a small point** (Bombieri–Gubler, 7.5.23 and Lemma
7.5.25 (a)). If a derivative of `P` does not vanish identically on the product of the spans of
the families `y h` — which is what the nonvanishing of the parametrized polynomial says
(`MvPolynomial.eval_linSubst`) — then a further derivative, of order at most `(card ρ) d h / B`
in each block, does not vanish at a point of the product whose coordinates in those families are
integers bounded by `B`. -/
example {k : Type*} [Field k] [CharZero k] {κ σ ρ : Type*} [Fintype σ] [Fintype ρ] [Finite κ]
    {d : κ → ℕ} {P : MvPolynomial (κ × σ) k} (hP : MvPolynomial.IsMultiHomogeneous d P)
    (y : κ → ρ → σ → k) (I : κ × σ →₀ ℕ)
    (hne : MvPolynomial.linSubst y (MvPolynomial.hasseDeriv I P) ≠ 0) {B : ℕ} (hB : 0 < B) :
    ∃ z : κ → ρ → ℤ, (∀ h l, (z h l).natAbs ≤ B) ∧ ∃ I' : κ × σ →₀ ℕ,
      (∀ h, B * ∑ i, I' (h, i) ≤ Fintype.card ρ * d h) ∧
      MvPolynomial.eval (fun p : κ × σ ↦ ∑ l, (z p.1 l : k) * y p.1 l p.2)
        (MvPolynomial.hasseDeriv (I + I') P) ≠ 0 :=
  MvPolynomial.exists_eval_hasseDeriv_add_ne_zero hP y I hne hB

/-- **Layer 5.5**, landed: **the milestone** (Bombieri–Gubler's (7.37)). With the grid
`B = 2 n / η` of Lemma 7.5.25, a derivative of weighted order at most `m η / 2` that does not
vanish identically on the product is replaced by one of weighted order at most `m η` that does
not vanish at an explicit point of it. ⚠ The bound on the coordinates of the point is
`2 n / η + 1` and not the book's `2 n / η`, because `B` is rounded up. -/
example {k : Type*} [Field k] [CharZero k] {κ σ ρ : Type*} [Fintype σ] [Fintype ρ] [Fintype κ]
    {d : κ → ℕ} {P : MvPolynomial (κ × σ) k} (hP : MvPolynomial.IsMultiHomogeneous d P)
    (y : κ → ρ → σ → k) {η : ℝ} (hη : 0 < η) (I : κ × σ →₀ ℕ)
    (hI : ∑ h, (∑ i, (I (h, i) : ℝ)) / (d h : ℝ) ≤ Fintype.card κ * η / 2)
    (hne : MvPolynomial.linSubst y (MvPolynomial.hasseDeriv I P) ≠ 0) :
    ∃ z : κ → ρ → ℤ, (∀ h l, ((z h l).natAbs : ℝ) ≤ 2 * Fintype.card ρ / η + 1) ∧
      ∃ I' : κ × σ →₀ ℕ, I ≤ I' ∧
        ∑ h, (∑ i, (I' (h, i) : ℝ)) / (d h : ℝ) ≤ Fintype.card κ * η ∧
        MvPolynomial.eval (fun p : κ × σ ↦ ∑ l, (z p.1 l : k) * y p.1 l p.2)
          (MvPolynomial.hasseDeriv I' P) ≠ 0 :=
  MvPolynomial.exists_eval_hasseDeriv_ne_zero_of_sum_div_le hP y hη I hI hne

/-! ### Layer 5.6 — landed

Discharged by `DiophantineApproximation/{FormIndexSubspace,SubspaceValueBound,
SubspaceKeyInequality,PenultimateMinimum}.lean`, with `LogComparison.lean` shared out of
`RothTheorem.lean`. Nothing of 5.6 was prototyped here, so every statement below is prototyped
for the first time. ⚠ No chain rule is needed between Layers 5.3 and 5.5; the vanishing pattern
of Layer 5.2 enters only as a two-sided bound on the exponents of the surviving monomials; and
the estimate needs a second invariant of the system of exponents, `approxAbsWeight`. See the
preamble. -/

/-- **Layer 5.6**, landed: **the bridge from the index along the forms to a derivative surviving
on the product of the kernels**. This is the whole of the dictionary between Layer 5.3, which
measures the index in the coordinates in which the forms are the variables, and Layer 5.5, which
wants a derivative in the original ones. -/
example [DecidableEq ι] {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    {d : κ → ℝ} (hd : ∀ h, 0 ≤ d h) {M : κ → ι → K} (hM : ∀ h, M h ≠ 0)
    {y : κ → ρ → ι → K}
    (hy : ∀ (h : κ) (x : ι → K), ∑ i, M h i * x i = 0 →
      x ∈ Submodule.span K (Set.range (y h)))
    {P : MvPolynomial (κ × ι) K} (hP : P ≠ 0) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : MvPolynomial.formIndex d M P ≤ ENNReal.ofReal t) :
    ∃ I : κ × ι →₀ ℕ, ∑ h, (∑ i, (I (h, i) : ℝ)) / d h ≤ t ∧
      MvPolynomial.linSubst y (MvPolynomial.hasseDeriv I P) ≠ 0 :=
  MvPolynomial.exists_linSubst_hasseDeriv_ne_zero_of_formIndex_le hd hM hy hP ht0 ht

/-- **Layer 5.6**, landed: **the height of `V(Q)` against the level, at every level**
(Bombieri–Gubler, the upper half of Lemma 7.5.21 without its hypothesis that `Q` be large). This
is what covers a bounded range of levels in the milestone. -/
example [LinearOrder ι] [Nonempty ι] {n : ℕ} {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Module.Dual K (ι → K)} {cf : AbsoluteValue K ℝ → ι → ℝ}
    (hLinf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLfin : ∀ w ∈ Sfin, LinearIndependent K (L w.1)) :
    ∃ C₆ : ℝ, ∀ Q : ℝ, 1 ≤ Q → Module.finrank K (NumberField.approxSpan Sfin L cf Q) = n →
      (NumberField.approxSpan Sfin L cf Q).logHeight
        ≤ (n : ℝ) * (∑ w : InfinitePlace K, (w.mult : ℝ) * NumberField.cMax cf w.1
            + ∑ w ∈ Sfin, NumberField.cMax cf w.1) * Real.log Q + C₆ :=
  NumberField.logHeight_approxSpan_le hLinf hLfin

/-- **Layer 5.6**, landed: **Steps IV and VI** (Bombieri–Gubler, 7.5.22 and 7.5.26). There is no
chain of `m + 1` levels of rank `n`, with `log Q` bounded below and growing at the rate `2 σ⁻¹`,
whose spans all have height at least a positive multiple of `ε log Q`. Everything in Layer 5 is
consumed here: 5.2 supplies the auxiliary polynomial at the multidegrees `d h ≈ D / log (Q h)`,
5.3 turns the heights into a small index, the bridge above and 5.5 turn that into a nonzero
value at an explicit point of small height, and the product formula against the local bounds
closes the contradiction as `D → ∞`. -/
example [DecidableEq ι] [LinearOrder ι] [Nonempty ι] {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card ι = n + 1) {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Module.Dual K (ι → K)} {cf : AbsoluteValue K ℝ → ι → ℝ}
    (hLinf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLfin : ∀ w ∈ Sfin, LinearIndependent K (L w.1))
    {ε : ℝ} (hε : 0 < ε) (hweight : NumberField.approxWeight Sfin cf ≤ -ε / 2) (C₅ : ℝ) :
    ∃ (m : ℕ) (σ Qlow : ℝ), 0 < σ ∧
      ∀ Q : Fin (m + 1) → ℝ, (∀ h, 1 < Q h) → (∀ h, Qlow ≤ Real.log (Q h)) →
        (∀ h : Fin m, 2 * σ⁻¹ * Real.log (Q h.castSucc) ≤ Real.log (Q h.succ)) →
        (∀ h, Module.finrank K (NumberField.approxSpan Sfin L cf (Q h)) = n) →
        (∀ h, ε * Real.log (Q h)
              / (4 * ((Fintype.card (InfinitePlace K) + Sfin.card : ℕ) : ℝ)) - C₅
            ≤ (NumberField.approxSpan Sfin L cf (Q h)).logHeight) → False :=
  NumberField.exists_forall_not_chain hn hcard hLinf hLfin hε hweight C₅

/-- **Layer 5.6**, landed: **the milestone**, the penultimate-minimum theorem
(Bombieri–Gubler, Theorem 7.5.13). For forms independent at every place of `S` and exponents of
weight at most `−ε/2`, the spans of the approximation domains of rank `n` are finite in number.
⚠ Levels above a threshold land in the finite set of exceptional subspaces of Layer 5.4
(`NumberField.exists_forall_approxSpan_mem`); the levels below it contribute finitely many spans
by the height bound above and Northcott for subspaces, which the book leaves to the reader. -/
example [DecidableEq ι] [LinearOrder ι] [Nonempty ι] {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card ι = n + 1) {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Module.Dual K (ι → K)} {cf : AbsoluteValue K ℝ → ι → ℝ}
    (hLinf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLfin : ∀ w ∈ Sfin, LinearIndependent K (L w.1))
    {ε : ℝ} (hε : 0 < ε) (hweight : NumberField.approxWeight Sfin cf ≤ -ε / 2) :
    {V : Submodule K (ι → K) | ∃ Q : ℝ, 1 ≤ Q ∧
      Module.finrank K (NumberField.approxSpan Sfin L cf Q) = n ∧
      V = NumberField.approxSpan Sfin L cf Q}.Finite :=
  NumberField.finite_setOf_approxSpan hn hcard hLinf hLfin hε hweight

/-! ### Layer 6.1 — landed

Discharged by `DiophantineApproximation/{WedgeRecovery,MinimaBounds,ExponentGrid,
WedgeExponentBound,ParametricSubspace}.lean`. The milestone below was prototyped here and
**survived verbatim**; everything else in this section is prototyped for the first time. ⚠ No
pigeonhole and no subsequence are needed, the penultimate rank is not a separate case, and the
minima have to be confined between two powers of `Q` — a bound Layer 4.2 does not give. See the
preamble. -/

/-- **Layer 6.1**, landed: **the minima of an approximation domain lie between two powers of the
level** (Bombieri–Gubler, Step IX). The lower bound is the product formula, not geometry of
numbers; the upper bound is then Minkowski's second theorem over `K` from above. -/
example [LinearOrder ι] [Nonempty ι] {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∃ Q₁ : ℝ, 1 ≤ Q₁ ∧ ∀ Q : ℝ, Q₁ ≤ Q → ∀ j < Fintype.card ι,
      Q ^ (-B) ≤ NumberField.successiveMinimum (NumberField.approxModule Sfin L c Q)
          (NumberField.approxBody L c Q) j ∧
        NumberField.successiveMinimum (NumberField.approxModule Sfin L c Q)
          (NumberField.approxBody L c Q) j ≤ Q ^ B :=
  NumberField.exists_pos_forall_rpow_le_successiveMinimum_le hLInf hLFin c

/-- **Layer 6.1**, landed: **the exponents of the wedge domain stay in a box** around the sums of
the original exponents over each `p`-subset, uniformly in the level, in the bijections of Evertse's
lemma and in `k`. This is what makes the grid finite. -/
example [LinearOrder ι] {c : AbsoluteValue K ℝ → ι → ℝ}
    {π : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι} {μ : ℕ → ℝ} {C Q B : ℝ} {k p : ℕ}
    (hQ : 1 < Q) (hCQ : C ≤ Q) (hQC : 1 ≤ C * Q) (hB : 0 ≤ B)
    (hk : k < Fintype.card ι) (hp : p ≤ Fintype.card ι)
    (hμlow : ∀ j, j < Fintype.card ι → Q ^ (-B) ≤ μ j)
    (hμhigh : ∀ j, j < Fintype.card ι → μ j ≤ Q ^ B)
    (v : AbsoluteValue K ℝ) (T : Set.powersetCard ι p) :
    |NumberField.wedgeExponent c π μ C Q k p v T - ∑ t ∈ (T : Finset ι), c v t|
      ≤ 1 + B * Fintype.card ι + 2 * B :=
  NumberField.abs_wedgeExponent_sub_sum_le hQ hCQ hQC hB hk hp hμlow hμhigh v T

/-- **Layer 6.1**, landed: **Lemma 7.5.33 as a function of the subspace**. The span of the first
`k` members of a basis is recovered from the span of the wedges that meet them by a map that does
not mention the basis, which is what carries finiteness from `⋀^p Kⁱ` back to `Kⁱ`. -/
example [LinearOrder ι] {x : Fin (Fintype.card ι) → ι → K} (hx : LinearIndependent K x)
    {k p : ℕ} (h : k + p = Fintype.card ι) :
    exteriorPower.recoverSpan p (exteriorPower.wedgeSpan k p x)
      = Submodule.span K (x '' {j | (j : ℕ) < k}) :=
  exteriorPower.recoverSpan_wedgeSpan hx h

/-- **Layer 6.1**, landed: **the milestone**, the parametric Subspace Theorem (Bombieri–Gubler
7.5.30–7.5.32, Steps VIII and IX; Evertse–Schlickewei for the formulation). For exponents of
negative weight, finitely many proper subspaces contain every approximation domain of large level.
This is the statement the quantitative theory strengthens by counting `T`. -/
example [Nontrivial ι] (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) (hc : approxWeight Sfin c < 0) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∃ Q₀ : ℝ, ∀ Q ≥ Q₀, ∃ W ∈ T, approxDomain Sfin L c Q ⊆ W :=
  NumberField.exists_finset_submodule_forall_approxDomain_subset hLInf hLFin hc

/-! ### Layer 6.2 — landed

Discharged by `DiophantineApproximation/SubspaceTheorem.lean`. Nothing of 6.2 was prototyped here
under its own name — it is Layer 6.3 at `F = K` and `w = id` — so both statements below are
prototyped for the first time. ⚠ The layer adds no analysis to Layers 5.1 and 6.1; all it
contributes is the kernels and, for the small heights, Northcott **on projective space**. See the
preamble. -/

/-- **Layer 6.2**, landed: **the Subspace Theorem with coefficients in `K`** (Schmidt 1972 for
`K = ℚ` and `S = {∞}`; Schlickewei 1977 with finite places; Bombieri–Gubler, Theorem 7.2.2 with
`F = K`). Finitely many proper subspaces of `Kⁱ` contain every nonzero solution of the fundamental
inequality. `[Nontrivial ι]` is `n ≥ 1`, without which the statement is false. -/
example [Nontrivial ι] (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (hLInf : ∀ v ∈ Sinf, LinearIndependent K (L v.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 →
        approxProd Sinf Sfin (fun v ↦ v) L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W :=
  NumberField.exists_finset_submodule_of_approxProd_le Sinf Sfin L hLInf hLFin hε

/-- **Layer 6.2**, landed: **the same as an inclusion**, the shape the literature states — the
solutions lie in a finite union of proper subspaces. -/
example [Nontrivial ι] (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (hLInf : ∀ v ∈ Sinf, LinearIndependent K (L v.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      {x : ι → K | x ≠ 0 ∧ approxProd Sinf Sfin (fun v ↦ v) L x ≤
          mulHeight x ^ (-(Fintype.card ι : ℝ) - ε)} ⊆ ⋃ W ∈ T, (W : Set (ι → K)) :=
  NumberField.exists_finset_submodule_setOf_approxProd_le_subset Sinf Sfin L hLInf hLFin hε

/-! ### Layer 6.3 — landed

Discharged by `DiophantineApproximation/{FormBaseChange,PlaceConjugation,ExtensionApproxProd,
SubspaceAlgebraic}.lean`. The milestone below was prototyped here and **survived verbatim**;
everything else in this section is prototyped for the first time. ⚠ The layer is the Galois
closure and nothing else, conjugation and base change are one operation, and Mathlib's
normalization of finite places is what forces the `(e f)`-th root. See the preamble. -/

/-- **Layer 6.3**, landed: **a linear form carried along a ring homomorphism**, which is at once
the base change of a system of forms to a larger field and its conjugation by an automorphism. -/
example {E : Type*} [Field E] [Algebra F E] [DecidableEq ι] (M : Dual F (ι → F)) (f : F →+* E)
    (y : ι → F) : M.compRingHom f (fun i ↦ f (y i)) = f (M y) :=
  Module.Dual.compRingHom_comp M f y

/-- **Layer 6.3**, landed: **every finite place of a Galois extension above `v` is a conjugate of
one chosen absolute value over `v`, raised to the local degree.** The exponent is the price of
Mathlib's normalization of finite places; at an infinite place there is none. -/
example [IsGalois K F] (v : FinitePlace K) (u : AbsoluteValue F ℝ) [u.LiesOver v.1]
    (V : FinitePlace F) (hV : V.LiesOver v) :
    ∃ σ : F ≃ₐ[K] F, ∀ z : F, V (σ z) = u z ^ V.localDegree K :=
  NumberField.FinitePlace.exists_algEquiv_apply_eq v u V hV

open scoped Classical in
/-- **Layer 6.3**, landed: **the transfer of the central quantity to the Galois closure**
(Bombieri–Gubler, Remark 7.2.3). At a point of `Kⁱ` it is an equality, because the point sees the
same local factor at every place above `v`. -/
example [IsGalois K F] [Nonempty ι] [DecidableEq ι] (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (u : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (huInf : ∀ v ∈ Sinf, (u v.1).LiesOver v.1) (huFin : ∀ v ∈ Sfin, (u v.1).LiesOver v.1)
    (x : ι → K) :
    approxProd (Sinf.biUnion (NumberField.InfinitePlace.placesOverFinset F))
        (Sfin.biUnion (NumberField.FinitePlace.placesOverFinset F)) (fun V ↦ V)
        (NumberField.conjSystem Sinf Sfin u L) (fun j ↦ algebraMap K F (x j))
      = approxProd Sinf Sfin u L x ^ Module.finrank K F :=
  NumberField.approxProd_conjSystem huInf huFin x

/-- **Layer 6.3**, landed (Schmidt; Schlickewei; Evertse; Bombieri–Gubler, Theorem 7.2.2 with
Remark 7.2.3). The Subspace Theorem: points in `K`, coefficients in a finite extension `F`. With
`F = K` and `w = id` it is the number-field form of Layer 6.2; with `K = ℚ` it is Schmidt's
theorem for forms with algebraic coefficients. `[Nontrivial ι]` is `n ≥ 1`, without which the
statement is false. -/
example [Nontrivial ι]
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLInf : ∀ v ∈ Sinf, LinearIndependent F (L v.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent F (L v.1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 →
        approxProd Sinf Sfin w L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W :=
  NumberField.exists_finset_submodule_of_approxProd_le_extension Sinf Sfin w hwInf hwFin
    L hLInf hLFin hε

/-! ### Layer 6.4 — landed

Discharged by `DiophantineApproximation/{AffineProd,SubspaceAffine}.lean`. The milestone below was
prototyped here and **survived verbatim**, display for display; its left-hand side has since been
given the name `NumberField.affineProd`, and the second example states it in both shapes at once.
⚠ The layer is Layer 6.3 plus the `S`-part of the height, `S`-integrality suffices in one
direction and not in the other, and the converse is proved as well, so that the library carries
one Subspace Theorem and not two. See the preamble. -/

open scoped Classical in
/-- **Layer 6.4**, landed: **the affine quantity is the projective one times the `S`-part of the
height, `#ι` times over**. This identity is the whole dictionary between Bombieri–Gubler's
Corollary 7.2.5 and their Theorem 7.2.2: the `#ι` local denominators that the affine form drops
are the `#ι` copies of the height that separate the two exponents. -/
example (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) {x : ι → K} (hx : x ≠ 0) :
    affineProd S w L x = approxProd Finset.univ (S.image FinitePlace.mk) w L x *
      ((∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) *
        ∏ v ∈ S, ⨆ i, FinitePlace.mk v (x i)) ^ Fintype.card ι :=
  NumberField.affineProd_eq_approxProd_mul S w L hx

/-- **Layer 6.4**, landed (Bombieri–Gubler, Corollary 7.2.5). **The affine form**, for points with
`S`-integral coordinates; `S` is Mathlib's carrier for `S`-integers, finite places only, and every
infinite place is present. The left-hand side is `NumberField.affineProd S w L x` written out,
which is how the milestone is stated in the library. -/
example [Nontrivial ι] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent F (L v.1))
    (hLFin : ∀ v ∈ S, LinearIndependent F (L (FinitePlace.mk v).1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 → (∀ j, x j ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
        (∏ v : InfinitePlace K,
            (∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j))) ^ v.mult) *
          ∏ v ∈ S, ∏ i, w (FinitePlace.mk v).1
            (L (FinitePlace.mk v).1 i fun j ↦ algebraMap K F (x j)) ≤ mulHeight x ^ (-ε) →
        ∃ W ∈ T, x ∈ W :=
  NumberField.exists_finset_submodule_of_integer_of_affineProd_le S w hwInf hwFin L hLInf hLFin hε

/-- **Layer 6.4**, landed (Bombieri–Gubler, Theorem 7.2.6): **the normalisation the converse runs
on**. Every finite set of finite places is contained in one over which every nonzero point has an
`S`-primitive scalar multiple — the point at which the `S`-part of the height *is* the height. -/
example (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S' : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S' ∧
      ∀ x : ι → K, x ≠ 0 → ∃ c : K, c ≠ 0 ∧
        (S' : Set (HeightOneSpectrum (𝓞 K))).IsPrimitive (c • x) :=
  NumberField.exists_finset_superset_forall_exists_isPrimitive_smul S

/-- **Layer 6.4**, landed: **the converse — the affine form catches every solution of the general
one**, so the two are equivalent and the library carries one theorem. The data is enlarged (every
infinite place, more finite places, an absolute value of `F` at each) and the solution is scaled
to be `S`-primitive; neither the subspaces nor the general inequality sees the scaling. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLInf : ∀ v ∈ Sinf, LinearIndependent F (L v.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent F (L v.1)) (ε : ℝ) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (w' : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
        (L' : AbsoluteValue K ℝ → ι → Dual F (ι → F)),
      (∀ v : InfinitePlace K, (w' v.1).LiesOver v.1) ∧
      (∀ v ∈ S, (w' (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1) ∧
      (∀ v : InfinitePlace K, LinearIndependent F (L' v.1)) ∧
      (∀ v ∈ S, LinearIndependent F (L' (FinitePlace.mk v).1)) ∧
      ∀ x : ι → K, x ≠ 0 →
        approxProd Sinf Sfin w L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ c : K, c ≠ 0 ∧ (S : Set (HeightOneSpectrum (𝓞 K))).IsPrimitive (c • x) ∧
          affineProd S w' L' (c • x) ≤ mulHeight (c • x) ^ (-ε) :=
  NumberField.exists_finset_forall_exists_smul_affineProd_le Sinf Sfin w hwInf hwFin
    L hLInf hLFin ε

/-! ### Layer 6.5 — landed

Discharged by `DiophantineApproximation/{GeneralPosition,SubspaceGeneralPosition}.lean`. Nothing
was prototyped here, so the statements below are the library's own, written out. ⚠ The layer is
Layer 6.3 plus one local observation and one partition; the families of forms may have any finite
sizes, general position is `Module.Dual.IsGeneralPosition`, and the last example is Layer 6.3
recovered as the case of equal sizes, so that the two are equivalent. See the preamble. -/

open scoped Classical in
/-- **Layer 6.5**, landed (Vojta 1987; Bombieri–Gubler, Theorem 7.2.9): **the Subspace Theorem
for forms in general position**, in the book's display. At every place the forms are indexed by a
finset `B v` of one carrier type, so their number varies from place to place; general position
asks that every `#ι` of them be linearly independent. -/
example {κ : Type*} [Finite κ] [Nontrivial ι] (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (B : AbsoluteValue K ℝ → Finset κ) (L : AbsoluteValue K ℝ → κ → Dual F (ι → F))
    (hLI : ∀ v ∈ Sinf, Module.Dual.IsGeneralPosition F (B v.1) (L v.1))
    (hLF : ∀ v ∈ Sfin, Module.Dual.IsGeneralPosition F (B v.1) (L v.1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 →
        (∏ v ∈ Sinf, (∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) /
              ⨆ j, v (x j)) ^ v.mult) *
          ∏ v ∈ Sfin, ∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)
          ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W :=
  NumberField.exists_finset_submodule_of_generalProd_le Sinf Sfin w hwI hwF B L hLI hLF hε

open scoped Classical in
/-- **Layer 6.5**, landed: **the same as an inclusion**, with the left-hand side under its own
name `NumberField.generalProd`. -/
example {κ : Type*} [Finite κ] [Nontrivial ι] (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (B : AbsoluteValue K ℝ → Finset κ) (L : AbsoluteValue K ℝ → κ → Dual F (ι → F))
    (hLI : ∀ v ∈ Sinf, Module.Dual.IsGeneralPosition F (B v.1) (L v.1))
    (hLF : ∀ v ∈ Sfin, Module.Dual.IsGeneralPosition F (B v.1) (L v.1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      {x : ι → K | x ≠ 0 ∧ NumberField.generalProd Sinf Sfin w B L x ≤
          mulHeight x ^ (-(Fintype.card ι : ℝ) - ε)} ⊆ ⋃ W ∈ T, (W : Set (ι → K)) :=
  NumberField.exists_finset_submodule_setOf_generalProd_le_subset Sinf Sfin w hwI hwF B L
    hLI hLF hε

/-- **Layer 6.5**, landed: **Layer 6.3 is the case of equal sizes**. With `#ι` forms at every
place, general position is linear independence and the two central quantities are the same
product — `NumberField.generalProd_univ_eq_approxProd` is `rfl` — so Vojta's refinement contains
the theorem it is proved from, and the two are equivalent. -/
example [Nontrivial ι] (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLI : ∀ v ∈ Sinf, LinearIndependent F (L v.1))
    (hLF : ∀ v ∈ Sfin, LinearIndependent F (L v.1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 →
        approxProd Sinf Sfin w L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W :=
  NumberField.exists_finset_submodule_of_generalProd_le Sinf Sfin w hwI hwF
    (fun _ ↦ Finset.univ) L (fun v hv ↦ .of_linearIndependent _ (hLI v hv))
    (fun v hv ↦ .of_linearIndependent _ (hLF v hv)) hε

/-! ### Layer 6.6 — landed

Discharged by `DiophantineApproximation/SubspaceConsistency.lean`. Nothing was prototyped here.
⚠ The milestone is an equation and not a translation: `Fintype.card ι = 2` supplies the
`[Nontrivial ι]` that Layer 6.3 asks for, and the two conclusions are then the *same*
proposition, so the converse needs nothing. The last example says so with `rfl`. See the
preamble. -/

/-- **Layer 6.6**, landed: **Layer 3.4 from Layer 6.3**. The Subspace Theorem with algebraic
coefficients at a two-element index type is Roth's theorem on the projective line — the statement
of Layer 3.4, hypothesis for hypothesis. -/
example (hcard : Fintype.card ι = 2) (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLI : ∀ v ∈ Sinf, LinearIndependent F (L v.1))
    (hLF : ∀ v ∈ Sfin, LinearIndependent F (L v.1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 →
        approxProd Sinf Sfin w L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ V ∈ T, x ∈ V :=
  NumberField.exists_finset_submodule_of_approxProd_le_card_two_of_extension hcard Sinf Sfin w
    hwI hwF L hLI hLF hε

/-- **Layer 6.6**, landed: **the projective reading**. On a two-element index type a proper
subspace is a point, so the conclusion is that finitely many points of `ℙ¹(K)` satisfy the
inequality — a count of solutions, with no subspace in the statement. -/
example (hcard : Fintype.card ι = 2) (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLI : ∀ v ∈ Sinf, LinearIndependent F (L v.1))
    (hLF : ∀ v ∈ Sfin, LinearIndependent F (L v.1)) {ε : ℝ} (hε : 0 < ε) :
    {P : Projectivization K (ι → K) | NumberField.approxProd Sinf Sfin w L P.rep
      ≤ Projectivization.mulHeight P ^ (-(Fintype.card ι : ℝ) - ε)}.Finite :=
  NumberField.finite_setOf_approxProd_le_card_two hcard Sinf Sfin w hwI hwF L hLI hLF hε

/-- **Layer 6.6**, landed: **Roth's theorem of Layer 3.2 from Layer 6.3**. Layer 3.4's converse
implication takes the Subspace Theorem as a hypothesis; discharging it from Layer 6 instead of
from Layer 3.3 gives a second proof of Roth's theorem over a number field. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ)}.Finite :=
  NumberField.finite_setOf_prod_min_one_le_of_extension Sinf Sfin w hwI hwF α hκ

/-- **Layer 6.6**, landed: **the two layers prove the same theorem, and `rfl` says so.** Proof
irrelevance is definitional, so an equality between two theorem constants is an equality between
their statements. The same holds for Layer 6.5's route and for the three proofs of Roth's theorem
the library now carries. -/
example : @NumberField.exists_finset_submodule_of_approxProd_le_card_two
    = @NumberField.exists_finset_submodule_of_approxProd_le_card_two_of_extension := rfl

/-! ### Layer 7.1 — landed

The statement prototyped here survived verbatim, display for display, and changed only its name:
`‖·‖` is a norm and not an absolute value, so the library calls it
`Complex.finite_setOf_norm_sum_mul_le_fin`. -/

/-- **Layer 7.1** (Bombieri–Gubler, Theorem 7.3.2), landed. One linear form with algebraic
coefficients, in integer points. The hypothesis is that the value is nonzero, not that the
coefficients are independent. -/
example {n : ℕ} (α : Fin (n + 1) → ℂ)
    (hα : ∀ i, IsAlgebraic ℚ (α i)) {ε : ℝ} (hε : 0 < ε) :
    {x : Fin (n + 1) → ℤ | 0 < ‖∑ i, α i * x i‖ ∧
      ‖∑ i, α i * x i‖ ≤ mulHeight (fun i ↦ (x i : ℚ)) ^ (-(n : ℝ) - ε)}.Finite :=
  Complex.finite_setOf_norm_sum_mul_le_fin hα hε

/-- **Layer 7.1**, landed, for an arbitrary finite index type: the form the induction proves,
with the exponent read off the cardinality. -/
example (α : ι → ℂ) (hα : ∀ i, IsAlgebraic ℚ (α i)) {ε : ℝ} (hε : 0 < ε) :
    {x : ι → ℤ | 0 < ‖∑ i, α i * (x i : ℂ)‖ ∧
      ‖∑ i, α i * (x i : ℂ)‖
        ≤ mulHeight (fun i ↦ (x i : ℚ)) ^ (-(Fintype.card ι - 1 : ℝ) - ε)}.Finite :=
  Complex.finite_setOf_norm_sum_mul_le hα hε

/-- **Layer 7.1**, landed: **the Subspace Theorem step**, which is all Layer 6 contributes. The
solutions lie in finitely many proper rational subspaces; eliminating one variable on each of
them is an induction that uses no further input. -/
example [Nontrivial ι] {α : ι → ℂ} (hα : ∀ i, IsAlgebraic ℚ (α i)) {j : ι} (hj : α j ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (ι → ℚ)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : ι → ℤ, (fun i ↦ (x i : ℚ)) ≠ 0 →
        ‖∑ k, α k * (x k : ℂ)‖
            ≤ mulHeight (fun i ↦ (x i : ℚ)) ^ (-(Fintype.card ι - 1 : ℝ) - ε) →
        ∃ V ∈ T, (fun i ↦ (x i : ℚ)) ∈ V :=
  Complex.exists_finset_submodule_of_norm_sum_le hα hj hε

/-- **Layer 7.1**, landed: **the nonvanishing hypothesis is not decoration.** The form `X 0 - X 1`
vanishes on the diagonal, so without it the set is infinite at *every* exponent, for coefficients
as algebraic as `1` and `-1`. -/
example (ε : ℝ) :
    {x : Fin 2 → ℤ | ‖∑ i, (![1, -1] : Fin 2 → ℂ) i * (x i : ℂ)‖
      ≤ mulHeight (fun i ↦ (x i : ℚ)) ^ (-(1 : ℝ) - ε)}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ ↦ (fun _ ↦ (m : ℤ) : Fin 2 → ℤ)) (fun m m' hmm ↦ ?_) fun m ↦ ?_
  · have h : ((m : ℤ)) = ((m' : ℤ)) := congrFun hmm 0
    exact_mod_cast h
  · have h0 : (∑ i, (![1, -1] : Fin 2 → ℂ) i * ((m : ℤ) : ℂ)) = 0 := by
      rw [Fin.sum_univ_two]
      simp
    rw [Set.mem_ofPred_eq, h0, norm_zero]
    positivity

/-! ### Layer 7.2 — landed

Discharged by `DiophantineApproximation/BoundedDegreeApproximation.lean`. Nothing was prototyped
here before the proof: `H(f_ξ)` names an object Mathlib does not have, so the shape had to be
chosen. The library quantifies over the minimal polynomial, and the rigidity lemma stated second
below is what makes that choice the book's. -/

/-- **Layer 7.2** (Schmidt; Bombieri–Gubler, Corollary 7.3.5), landed. **Approximation by
algebraic numbers of bounded degree.** For a complex algebraic `α`, a degree bound `D` and
`ε > 0`, only finitely many complex algebraic numbers `ξ` of degree at most `D` satisfy
`‖α - ξ‖ ≤ H(f_ξ) ^ (-D - 1 - ε)`. The approximant is carried by its primitive irreducible
integer minimal polynomial `f_ξ`, whose degree is the degree of `ξ` and whose naive height is the
`H(f_ξ)` of the statement. -/
example {α : ℂ} (hα : IsAlgebraic ℚ α) (D : ℕ) {ε : ℝ} (hε : 0 < ε) :
    {ξ : ℂ | ∃ P : ℤ[X], P.IsPrimitive ∧ Irreducible P ∧ aeval ξ P = 0 ∧ P.natDegree ≤ D ∧
      ‖α - ξ‖ ≤ P.supNorm ^ (-(D : ℝ) - 1 - ε)}.Finite :=
  Complex.finite_setOf_norm_sub_le hα D hε

/-- **Layer 7.2**, landed: **the height in the exponent depends on `ξ` alone.** Two primitive
irreducible integer polynomials with a common complex root are associated, hence equal up to
sign, so the existential above is Bombieri–Gubler's `H(f_ξ)` and not a choice. The lemma is
Layer 1.3's, generalized by Layer 7.2 from a real root to a root in any `ℚ`-algebra that is a
domain. -/
example {ξ : ℂ} {P Q : ℤ[X]} (hPp : P.IsPrimitive) (hPi : Irreducible P) (hPξ : aeval ξ P = 0)
    (hQp : Q.IsPrimitive) (hQi : Irreducible Q) (hQξ : aeval ξ Q = 0) : P.supNorm = Q.supNorm :=
  Polynomial.supNorm_eq_of_isPrimitive_of_irreducible hPp hPi hPξ hQp hQi hQξ

/-- **Layer 7.2**, landed, counted by minimal polynomials instead of by approximants: the shape
the proof produces, and the shape Layer 1.3's exponents consume. The approximants of the
statement above are the roots of these finitely many polynomials. -/
example {α : ℂ} (hα : IsAlgebraic ℚ α) (D : ℕ) {ε : ℝ} (hε : 0 < ε) :
    {P : ℤ[X] | P.natDegree ≤ D ∧ P.IsPrimitive ∧ Irreducible P ∧
      ∃ ξ : ℂ, aeval ξ P = 0 ∧ ‖α - ξ‖ ≤ P.supNorm ^ (-(D : ℝ) - 1 - ε)}.Finite :=
  Complex.finite_setOf_exists_root_norm_sub_le hα D hε

/-- **Layer 7.2 in the language of Layer 1.3**, landed, and one of the two upper bounds Layer 7.3
needs: Koksma's exponent of a real algebraic number is at most the degree bound. The other upper
bound, `w_n^* ≤ deg α - 1`, is Liouville's inequality and is Layer 1.3's. -/
example {α : ℝ} (hα : IsAlgebraic ℚ α) (n : ℕ) : Real.koksmaExponent n α ≤ (n : ℝ≥0∞) :=
  Real.koksmaExponent_le_of_isAlgebraic hα n

/-! ### Layer 7.3 — landed

Discharged by `DiophantineApproximation/{SchmidtExponents,SimultaneousSubspaces,
SimultaneousApproximation}.lean`. The exponents of a real algebraic number are computed above,
next to the Layer 1.3 statements they close; **Schmidt's two theorems on simultaneous
approximation** were never prototyped and are stated here for the first time. The distance to the
nearest integer is written as an existential over the numerator — `Real.abs_sub_round_le` says
the minimum is attained at `round`, so the two readings cut out the same set — and the hypothesis
that `1, α 1, …, α n` are linearly independent over `ℚ` is Mathlib's `LinearIndependent`, indexed
by `Option ι`. -/

/-- **Layer 7.3**, landed: **Schmidt's theorem on simultaneous approximation** (Schmidt 1970;
Bombieri–Gubler, Remark 7.3.4). For real algebraic `α 1, …, α n` with `1, α 1, …, α n` linearly
independent over `ℚ` and `ε > 0`, finitely many `q ≥ 1` satisfy
`q ^ (1 + ε) * ∏ i, ‖q * α i‖ < 1`. -/
example {ι : Type*} [Fintype ι] {α : ι → ℝ} (halg : ∀ i, IsAlgebraic ℚ (α i))
    (hind : LinearIndependent ℚ fun o : Option ι ↦ o.elim (1 : ℝ) α) {ε : ℝ} (hε : 0 < ε) :
    {q : ℤ | 1 ≤ q ∧ ∃ p : ι → ℤ,
      ((q : ℤ) : ℝ) ^ (1 + ε) * ∏ i, |((q : ℤ) : ℝ) * α i - ((p i : ℤ) : ℝ)| < 1}.Finite :=
  Real.finite_setOf_mul_prod_dist_lt halg hind hε

/-- **Layer 7.3**, landed: **Schmidt's theorem on the linear form `∑ i, q i * α i`** (Schmidt
1970; Bombieri–Gubler, Remark 7.3.4). The `q ∈ ℤⁿ` with no vanishing coordinate satisfying
`(∏ i, |q i|) ^ (1 + ε) * ‖∑ i, q i * α i‖ < 1` are finitely many. ⚠ The hypothesis that no
coordinate vanishes is not decoration: with one it the product is `0` and the inequality is
free. -/
example {ι : Type*} [Fintype ι] {α : ι → ℝ} (halg : ∀ i, IsAlgebraic ℚ (α i))
    (hind : LinearIndependent ℚ fun o : Option ι ↦ o.elim (1 : ℝ) α) {ε : ℝ} (hε : 0 < ε) :
    {q : ι → ℤ | (∀ i, q i ≠ 0) ∧ ∃ p : ℤ,
      (∏ i, |((q i : ℤ) : ℝ)|) ^ (1 + ε)
        * |∑ i, α i * ((q i : ℤ) : ℝ) - (p : ℝ)| < 1}.Finite :=
  Real.finite_setOf_prod_abs_mul_dist_lt halg hind hε

/-- **Layer 7.3**, landed, the theorem the statement above runs on and which is not in the
roadmap's prose: for algebraic `β 1, …, β n` independent with `1` over `ℚ`, the `q` with no
vanishing coordinate satisfying `(∏ i, |q i|) ^ (1 + ε) * |∑ i, β i * q i| < 1` are finitely
many. The difference from the statement above is that the value itself is small, not its distance
to `ℤ`. -/
example {ι : Type*} [Fintype ι] {β : ι → ℝ} (halg : ∀ i, IsAlgebraic ℚ (β i))
    (hind : LinearIndependent ℚ fun o : Option ι ↦ o.elim (1 : ℝ) β) {ε : ℝ} (hε : 0 < ε) :
    {x : ι → ℤ | (∀ i, x i ≠ 0) ∧
      (∏ i, |((x i : ℤ) : ℝ)|) ^ (1 + ε) * |∑ i, β i * ((x i : ℤ) : ℝ)| < 1}.Finite :=
  Real.finite_setOf_prod_abs_mul_abs_sum_lt halg hind hε

/-- **Layer 7.3**, landed, the Subspace Theorem step both theorems run on: a full system of
linearly independent forms with algebraic coefficients, with the hypothesis on the bare product
of the values of the forms and not on the sup norm. -/
example {ι : Type*} [Fintype ι] [Nontrivial ι] {c : ι → ι → ℂ}
    (hc : ∀ i k, IsAlgebraic ℚ (c i k)) (hind : LinearIndependent ℂ c) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (ι → ℚ)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : ι → ℤ, (fun i ↦ (x i : ℚ)) ≠ 0 →
        (∏ i, ‖∑ k, c i k * ((x k : ℤ) : ℂ)‖) ≤ (⨆ i, |((x i : ℤ) : ℝ)|) ^ (-ε) →
        ∃ V ∈ T, (fun i ↦ (x i : ℚ)) ∈ V :=
  Complex.exists_finset_submodule_of_prod_norm_le hc hind hε

/-! ### Layer 7.4 — landed

Discharged by `DiophantineApproximation/{StammeringWords,DigitExpansions,RepetitionSubspaces,
TranscendenceCriterion}.lean`. Nothing of 7.4 was prototyped; its definitions are stated here for
the first time, as the roadmap's prose gives them: `V ^ w` is `List.rpow`, and "`U k (V k) ^ w` is
a prefix of `a`" is written letter by letter with `getElem?`. The number is Mathlib's
`Real.ofDigits`. -/

/-- **Layer 7.4**, landed: **the combinatorial transcendence criterion** (Adamczewski–Bugeaud–Luca
2004; Adamczewski–Bugeaud 2007). For `b ≥ 2`, if `a` is stammering and not eventually periodic,
then `∑ k, a k / b ^ (k + 1)` is transcendental. -/
example {b : ℕ} (hb : 2 ≤ b) {a : ℕ → Fin b} (hst : Function.IsStammering a)
    (hper : ¬ Function.IsEventuallyPeriodic a) : Transcendental ℚ (Real.ofDigits a) :=
  Real.transcendental_ofDigits_of_isStammering hb hst hper

/-- **Layer 7.4**, landed: the definition, as the roadmap's prose gives it. -/
example {α : Type*} (w : ℝ) (a : ℕ → α) :
    Function.IsStammeringWith w a ↔ ∃ U V : ℕ → List α,
      (∀ k i, i < (U k ++ (V k).rpow w).length → (U k ++ (V k).rpow w)[i]? = some (a i)) ∧
      BddAbove (Set.range fun k ↦ ((U k).length : ℝ) / (V k).length) ∧
      StrictMono fun k ↦ (V k).length :=
  Iff.rfl

/-- **Layer 7.4**, landed: **the weaker criterion for `w > 2`** (Ferenczi–Mauduit 1997), the
consumer of Layer 3.3 that needs none of Layers 4–6. -/
example {b : ℕ} (hb : 2 ≤ b) {a : ℕ → Fin b} {w : ℝ} (hw : 2 < w)
    (hst : Function.IsStammeringWith w a) (hper : ¬ Function.IsEventuallyPeriodic a) :
    Transcendental ℚ (Real.ofDigits a) :=
  Real.transcendental_ofDigits_of_isStammeringWith_of_two_lt hb hw hst hper

/-- **Layer 7.4**, landed, the working form both criteria are proved in: periodic segments of the
digits, for any irrational value. -/
example {b : ℕ} (hb : 2 ≤ b) {a : ℕ → Fin b} (hirr : Irrational (Real.ofDigits a)) {w C : ℝ}
    (hw : 1 < w) (hC : 0 ≤ C) {r s : ℕ → ℕ} (hs : StrictMono s)
    (hrs : ∀ k, (r k : ℝ) ≤ C * s k)
    (hper : ∀ k i, r k ≤ i → i + s k < r k + ⌈w * s k⌉₊ → a (i + s k) = a i) :
    Transcendental ℚ (Real.ofDigits a) :=
  Real.transcendental_ofDigits_of_forall_periodic hb hirr hw hC hs hrs hper

/-- **Layer 7.4**, landed: a base-`b` expansion that is not eventually periodic has an irrational
value, whatever the other expansions of that value. -/
example {b : ℕ} {a : ℕ → Fin b} (hper : ¬ Function.IsEventuallyPeriodic a) :
    Irrational (Real.ofDigits a) :=
  Real.irrational_ofDigits hper

/-- **Layer 7.4**, landed, the Subspace Theorem step: `X 0`, `X 1`, `ξ X 0 - ξ X 1 - X 2` at `∞`
and the coordinate forms at a finite set of primes. -/
example {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) (S : Finset Nat.Primes) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (Fin 3 → ℚ)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : Fin 3 → ℤ, (fun i ↦ (x i : ℚ)) ≠ 0 →
        |((x 0 : ℤ) : ℝ)| * |((x 1 : ℤ) : ℝ)| * |ξ * (x 0 : ℝ) - ξ * (x 1 : ℝ) - (x 2 : ℝ)|
            * ∏ l ∈ S, ∏ i, ((padicNorm (l : ℕ) ((x i : ℤ) : ℚ) : ℚ) : ℝ)
          ≤ (⨆ i, |((x i : ℤ) : ℝ)|) ^ (-ε) →
        ∃ V ∈ T, (fun i ↦ (x i : ℚ)) ∈ V :=
  Real.exists_finset_submodule_of_repetition hξ S hε

/-! ### Layer 7.5 — landed

Discharged by `DiophantineApproximation/{FactorComplexity,ComplexityTranscendence}.lean`. Nothing
of 7.5 was prototyped. The complexity counts the words `List.ofFn fun j : Fin n ↦ a (i + j)`, the
factors of `a`; over a finite alphabet the set is finite and `Set.ncard` counts it. -/

/-- **Layer 7.5**, landed: **the complexity of an algebraic irrational** (Adamczewski–Bugeaud 2007,
Theorem 1). -/
example {b : ℕ} (hb : 2 ≤ b) {a : ℕ → Fin b} (hirr : Irrational (Real.ofDigits a))
    (halg : IsAlgebraic ℚ (Real.ofDigits a)) :
    Filter.Tendsto (fun n ↦ (Function.complexity a n : ℝ) / n) Filter.atTop Filter.atTop :=
  Real.tendsto_complexity_div_atTop hb hirr halg

/-- **Layer 7.5**, landed: the definition, as the roadmap's prose gives it. -/
example {α : Type*} (a : ℕ → α) (n : ℕ) :
    Function.complexity a n = (Set.range fun i ↦ List.ofFn fun j : Fin n ↦ a (i + j)).ncard :=
  rfl

/-- **Layer 7.5**, landed: **the combinatorial lemma**, for an arbitrary finite alphabet and with
no reference to a number. -/
example {α : Type*} [Finite α] {a : ℕ → α} {C : ℝ}
    (h : ∃ᶠ n in Filter.atTop, (Function.complexity a n : ℝ) ≤ C * n) : Function.IsStammering a :=
  Function.isStammering_of_frequently_complexity_le h

/-- **Layer 7.5**, landed: the complexity is nondecreasing. -/
example {α : Type*} [Finite α] (a : ℕ → α) : Monotone (Function.complexity a) :=
  Function.complexity_mono a

/-- **Layer 7.5**, landed: **Morse–Hedlund**. -/
example {α : Type*} [Finite α] (a : ℕ → α) :
    List.TFAE [Function.IsEventuallyPeriodic a, BddAbove (Set.range (Function.complexity a)),
      ∃ n, Function.complexity a n ≤ n] :=
  Function.isEventuallyPeriodic_tfae a

/-- **Layer 7.5**, landed: the value of a base-`b` expansion is irrational exactly when the
expansion is not eventually periodic. -/
example {b : ℕ} (hb : 2 ≤ b) {a : ℕ → Fin b} :
    Irrational (Real.ofDigits a) ↔ ¬ Function.IsEventuallyPeriodic a :=
  Real.irrational_ofDigits_iff hb

end Subspace

/-! ## Layer 8: unit equations -/

section UnitEquation

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- **Layer 8.1** (Siegel; Mahler; Lang), landed in `DiophantineApproximation/UnitEquation.lean`:
the unit equation in two variables. The prototype survived **verbatim**. -/
example (S : Finset (HeightOneSpectrum (𝓞 K))) (a b : Kˣ) :
    {p : Kˣ × Kˣ | p.1 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧
      p.2 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧
      (a : K) * p.1 + (b : K) * p.2 = 1}.Finite :=
  NumberField.finite_setOf_unit_add_unit_eq_one S a b

/-- **Layer 8.1**, landed: ⚠ **the route is Vojta's refinement, with no split by the largest
coordinate.** With the three forms `X₀`, `X₁`, `X₀ + X₁` at every place — in general position —
the central quantity of Layer 6.5 at a solution of `x + y = 1` is *exactly* `H(x, y) ^ (-3)`: the
numerators multiply to `1` by the `S`-product formula, the denominators to `H ^ 3` because the
equation itself makes the point `S`-primitive. -/
example (S : Finset (HeightOneSpectrum (𝓞 K))) {x y : Kˣ}
    (hx : x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (hy : y ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (hxy : (x : K) + y = 1) :
    open scoped Classical in
    generalProd Finset.univ (S.image FinitePlace.mk) (fun v ↦ v) (fun _ ↦ Finset.univ)
        (fun _ ↦ unitEquationForms) ![(x : K), y] = (mulHeight ![(x : K), y] ^ 3)⁻¹ :=
  NumberField.generalProd_unitEquationForms_eq S hx hy hxy

/-- **Layer 8.2** (Evertse; van der Poorten–Schlickewei; Bombieri–Gubler, Theorem 7.4.2), landed
in `DiophantineApproximation/UnitEquationSeveral.lean`: the unit equation in `n` variables, finitely
many solutions with no vanishing subsum. The prototype survived **verbatim**. The hypothesis is
not removable: `(u, −u, 1)` solves `x₁ + x₂ + x₃ = 1` for every unit `u`. -/
example (S : Finset (HeightOneSpectrum (𝓞 K))) (a : ι → Kˣ) :
    {x : ι → Kˣ | (∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) ∧
      ∑ i, (a i : K) * x i = 1 ∧
      ∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, (a i : K) * x i ≠ 0}.Finite :=
  NumberField.finite_setOf_sum_unit_eq_one S a

/-- **Layer 8.2**, landed: the same for a finitely generated subgroup of `Kˣ`, which lies in the
`S`-units for a finite `S`. The prototype survived **verbatim**. -/
example (Γ : Subgroup Kˣ) (hΓ : Γ.FG) (a : ι → Kˣ) :
    {x : ι → Kˣ | (∀ i, x i ∈ Γ) ∧ ∑ i, (a i : K) * x i = 1 ∧
      ∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, (a i : K) * x i ≠ 0}.Finite :=
  NumberField.finite_setOf_sum_mem_eq_one Γ hΓ a

/-- **Layer 8.2**, landed: Corollary 7.4.3, **vanishing subsums allowed** — every solution has a
term `a i * x i` in a fixed finite set. -/
example (S : Finset (HeightOneSpectrum (𝓞 K))) (a : ι → Kˣ) :
    ∃ Φ : Set K, Φ.Finite ∧ ∀ x : ι → Kˣ,
      (∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) →
      ∑ i, (a i : K) * x i = 1 → ∃ i, (a i : K) * x i ∈ Φ :=
  NumberField.exists_finite_forall_exists_mul_mem S a

/-- **Layer 8.2**, landed: ⚠ **the central quantity is `H ^ (-n - 1)` on the nose**, with the
`n + 1` forms `X i` and `∑ i, X i` at every place — 8.1's identity in `n` variables. -/
example (S : Finset (HeightOneSpectrum (𝓞 K))) {x : ι → Kˣ}
    (hx : ∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (hsum : ∑ i, (x i : K) = 1) :
    open scoped Classical in
    generalProd Finset.univ (S.image FinitePlace.mk) (fun v ↦ v) (fun _ ↦ Finset.univ)
        (fun _ ↦ NumberField.sumEquationForms) (fun i ↦ (x i : K)) =
      (mulHeight (fun i ↦ (x i : K)) ^ (Fintype.card ι + 1))⁻¹ :=
  NumberField.generalProd_sumEquationForms_eq S hx hsum

/-- **Layer 8.3** (Győry–Papp), landed in `DiophantineApproximation/DecomposableForm.lean` and
prototyped here for the first time: for a triangularly connected family of forms with common
kernel `0`, a decomposable form equation `c ∏ j, l j x ^ e j = m` has finitely many solutions in
`S`-integers. ⚠ **Pairwise non-proportionality is not a hypothesis**: the argument never uses it.
⚠ Only the split case — forms over `K` itself; the passage to an extension is made by 8.4, for
binary forms. -/
example {κ : Type*} [Fintype κ] (S : Finset (HeightOneSpectrum (𝓞 K)))
    {l : κ → Dual K (ι → K)} (hl : ⨅ j, LinearMap.ker (l j) = ⊥)
    (hc : Dual.IsTriangularlyConnected l) {e : κ → ℕ} (he : ∀ j, e j ≠ 0) (c : K) {m : K}
    (hm : m ≠ 0) :
    {x : ι → K | (∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
      c * ∏ j, l j x ^ e j = m}.Finite :=
  NumberField.finite_setOf_mul_prod_eq S hl hc he c hm

/-- **Layer 8.3**, landed: modulo `S`-units, finitely many `S`-integral points make the form an
`S`-unit, and the representatives can be taken among them. ⚠ **No discreteness of valuations**:
two solutions on one line differ by a scalar whose `E`-th power is an `S`-unit, hence by an
`S`-unit. -/
example {κ : Type*} [Fintype κ] (S : Finset (HeightOneSpectrum (𝓞 K)))
    {l : κ → Dual K (ι → K)} (hl : ⨅ j, LinearMap.ker (l j) = ⊥)
    (hc : Dual.IsTriangularlyConnected l) {e : κ → ℕ} (he : ∀ j, e j ≠ 0) (c : K) :
    ∃ F : Set (ι → K), F.Finite ∧
      F ⊆ {x | (∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
        ∃ w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, (w : K) = c * ∏ j, l j x ^ e j} ∧
      ∀ x : ι → K, (∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
        (∃ w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, (w : K) = c * ∏ j, l j x ^ e j) →
        ∃ u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, ∃ y ∈ F, x = (u : K) • y :=
  NumberField.exists_finite_forall_mul_prod_mem_unit S hl hc he c

/-- **Layer 8.3**, landed: the core, on any `K`-vector space — the points at which every form of a
triangularly connected family takes an `S`-unit value are `S`-unit multiples of finitely many. -/
example {κ V : Type*} [Finite κ] [AddCommGroup V] [Module K V]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {l : κ → Dual K V}
    (hl : ⨅ j, LinearMap.ker (l j) = ⊥) (hc : Dual.IsTriangularlyConnected l) :
    ∃ F : Set V, F.Finite ∧ ∀ x : V,
      (∀ j, ∃ u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, (u : K) = l j x) →
      ∃ u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, ∃ y ∈ F, x = (u : K) • y :=
  NumberField.exists_finite_forall_eq_smul S hl hc

/-- **Layer 8.4** (Thue 1909; Siegel), landed in `DiophantineApproximation/ThueMahler.lean` and
prototyped here for the first time: Thue's equation in the `S`-integers of a number field, under
Layer 3.6's hypothesis — `g` has at least three distinct roots in an algebraically closed field,
the point at infinity counting as one when `deg g < d`. ⚠ **Nothing above 8.3 is used**: the
equation is solved in the splitting field, over the primes above `S`
(`DiophantineApproximation/SIntegerExtension.lean`), where the form is decomposable and at least
three pairwise non-proportional binary forms are triangularly connected. -/
example {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [DecidableEq Ω]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {g : K[X]} {d : ℕ} (hd : g.natDegree ≤ d)
    (hroots : 3 ≤ (g.map (algebraMap K Ω)).roots.toFinset.card +
      if g.natDegree = d then 0 else 1)
    {m : K} (hm : m ≠ 0) :
    {z : Fin 2 → K | (∀ i, z i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
      MvPolynomial.eval z (g.homogenize d) = m}.Finite :=
  NumberField.finite_setOf_eval_homogenize_eq S hd hroots hm

/-- **Layer 8.4** (Mahler 1933), landed: modulo `S`-units, finitely many `S`-integral points make
the form an `S`-unit. ⚠ **The descent from the splitting field needs no degree and no norm**: two
`K`-solutions on one line of the extension differ by a scalar of `K` that is a unit above `S`,
hence an `S`-unit. -/
example {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [DecidableEq Ω]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {g : K[X]} {d : ℕ} (hd : g.natDegree ≤ d)
    (hroots : 3 ≤ (g.map (algebraMap K Ω)).roots.toFinset.card +
      if g.natDegree = d then 0 else 1) :
    ∃ F : Set (Fin 2 → K), F.Finite ∧
      F ⊆ {z | (∀ i, z i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
        ∃ w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
          (w : K) = MvPolynomial.eval z (g.homogenize d)} ∧
      ∀ z : Fin 2 → K, (∀ i, z i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
        (∃ w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
          (w : K) = MvPolynomial.eval z (g.homogenize d)) →
        ∃ u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, ∃ y ∈ F, z = (u : K) • y :=
  NumberField.exists_finite_forall_eval_homogenize_mem_unit S hd hroots

/-- **Layer 8.4**, landed: **the Thue–Mahler theorem over `ℚ`** — finitely many coprime integers
`x, y` and exponents `z` with `G(x, y) = ± p₁ ^ z₁ ⋯ pₛ ^ zₛ`. ⚠ Coprimality enters only at the
end: a line through the origin carries at most two coprime integer points. -/
example {g : ℤ[X]} {d : ℕ} (hd : g.natDegree ≤ d)
    (hroots : 3 ≤ (g.map (Int.castRingHom ℂ)).roots.toFinset.card +
      if g.natDegree = d then 0 else 1)
    {s : ℕ} (p : Fin s → Nat.Primes) :
    {t : (ℤ × ℤ) × (Fin s → ℕ) | IsCoprime t.1.1 t.1.2 ∧
      (MvPolynomial.eval ![t.1.1, t.1.2] (g.homogenize d)).natAbs =
        ∏ i, (p i : ℕ) ^ t.2 i}.Finite :=
  Polynomial.finite_setOf_natAbs_eval_homogenize_eq_prod_pow hd hroots p

end UnitEquation

end

end TauCetiRoadmap.DiophantineApproximation
