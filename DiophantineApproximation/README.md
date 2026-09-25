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
⚠ **3.3 took four, and the seam is not between the classical theorems but under them**:
`…/RationalPlaces.lean` is the dictionary between the finite places of `ℚ` and `padicNorm`, and
knows no Diophantine approximation at all; `…/RothInfinity.lean` is the target `∞` and the Möbius
change of variable that removes it, and is the only file of the layer that touches a general
number field; `…/RothRational.lean` is Roth's theorem over `ℚ` at the real place and the value of
the irrationality exponent; and `…/Ridout.lean` is the `ℚ`-workhorse — one target at the infinite
place and one at each prime of a finite set — with Ridout's theorem and the `p`-adic form as its
two instances. The two classical theorems share a file because they share that workhorse, and the
workhorse is what a fifth form would quote.
⚠ **3.4 took three, and the seam is the one the layer's own sentence predicted**:
`…/ProjectiveTarget.lean` is the local dictionary — the zero of `a X₀ + b X₁` as a point of
`OnePoint F`, the comparison between the value of the form and the approximation factor at that
zero, and Cramer's rule read at one absolute value — and knows nothing of number fields;
`…/ApproxProd.lean` defines the central quantity, proves it a function on projective space, and
carries the two facts about a two-element index type — the height of a pair is the height of the
ratio, and linear independence is a determinant; and `…/RothProjective.lean` is the two
directions. The split by which form is small at each place lives in the third file, with the
theorem it serves.
⚠ **3.5 took two, and the seam is between arithmetic and approximation**:
`…/PrimeProducts.lean` is the finite part of the product formula — the primes of an integer as a
`Finset Nat.Primes`, and the fact that a product of `p`-adic sizes over *the* primes of the
number itself is an identity rather than an estimate — and knows no Diophantine approximation at
all; `…/MahlerPowers.lean` is the theorem. The first file is the arithmetic input Layer 3.3 did
not have, and it is what the remaining applications of Ridout's theorem will quote.
⚠ **3.6 took two, and the seam is between algebra and approximation**: `…/BinaryForm.lean` is
the dictionary between a binary form and the complex roots of its dehomogenization — Mathlib's
`Polynomial.homogenize` supplies the form itself, and the file adds the degree bound, the value
on the line at infinity, the product over the roots and the multiplicity bound at an irrational
root — and knows no approximation at all; `…/ThueEquation.lean` is Roth's theorem for pairs of
integers, the exceptional set of one root, and the theorem. Layer 8.4 quotes one lemma of the
first file unchanged — the value on the line at infinity — since everything in it is about one
form and none of it about `S`.
⚠ **3.7 took two, and the seam is between a pair of solutions and a count**:
`…/GapPrinciple.lean` is the strong gap principle and the approximation class of one solution,
and counts nothing; `…/CountingApproximations.lean` is two combinatorial lemmas that know no
heights — points with a gap in a window, chains in a finite set — and the two counts. It also
restructured `…/RothTheorem.lean`, which now proves the core of Roth's proof as a statement of its
own.
⚠ **3.8 took one file, and the work went into the files it stands on**: `…/MovingTargets.lean` is
the theorem and its acceptance tests. The core of Roth's proof in `…/RothTheorem.lean` is now
stated for targets that change along the chain, Steps I to V in `…/RothAuxiliary.lean`,
`…/RothKeyInequality.lean` and `…/RothLocalBound.lean` take one target per coordinate, chains are
chosen by index in `…/IndependentHeights.lean`, and the one new fact — the size of a target
bounded by its height — went into `…/FundamentalInequality.lean`, beside the upper bound it reads
at one place.
⚠ **4.1 took four files, and the seam is between a lattice and a domain**:
`…/FinitePlaceValues.lean` is three facts about one finite place — its value group and the
largest value below a bound, approximation at finitely many places, the ultrametric Leibniz
bound — and knows no lattice; `…/ModuleCovolume.lean` is the covolume of any finitely generated
`𝓞 K`-module in `Kⁱ`, read from maximal determinants at the finite places, and knows no domain;
`…/ApproximationDomain.lean` is the domain, its lattice and its body, and the covolume;
`…/ApproximationVolume.lean` is the volume, the comparison with `Q` to the weight, and the
acceptance tests.
⚠ **4.2 took two files, and the seam is between the minima and their product**:
`…/FieldMinima.lean` is the minima over `K`, their attainment and their three comparisons with
the real minima, and knows no measure; `…/FieldMinkowski.lean` is Minkowski's second theorem over
`K`, its reading for approximation domains, and the acceptance tests.
4.3 took one, `…/ApproximationRank.lean`: the rank, read from the minima for any lattice and body
before it is read for approximation domains.
⚠ **4.4 took two, and the seam is the arithmetic**: `…/SIntegerApproximation.lean` is simultaneous
approximation by `S₀`-integers and knows no form; `…/EvertseLemma.lean` is the induction, run over
any field whose places admit such an approximation, then read over a number field.
⚠ **4.5 took two, and the seam is the number field**: `…/WedgeForm.lean` is the exterior algebra
of forms over any field — Laplace's identity, independence, Lemma 7.5.33 and two bounds for a
determinant at a place — and knows no domain; `…/WedgeDomain.lean` is Step VIII and Lemma 7.5.31.
⚠ **5.1 took two, and the seam is between a point and a family**: `…/UnitNormalization.lean`
normalizes one point — the primitive multiple, the unit multiple, the heights of the form values —
and knows no exponent system; `…/SubspaceReduction.lean` sorts the normalized solutions into
finitely many approximation domains.
⚠ **5.2 took three, and the seams are the field and the arithmetic**:
`…/MultiHomogeneous.lean` is the algebra of multidegrees and the block substitution over any
commutative ring, with the chain rule and the vanishing statement over a field of characteristic
zero; `…/MonomialDeviation.lean` is the counting, and is pure combinatorics and real analysis with
no polynomial in it; `…/SubspaceAuxiliary.lean` is the heights and Siegel's lemma.
⚠ **5.3 took three, and the seams are the same two**: `…/FormIndex.lean` is the index along the
forms and its valuation properties, over any field and with no height in it;
`…/FormSpecialization.lean` is the specialization and the dehomogenization, still with no
height; `…/GeneralizedRothLemma.lean` is the two height statements and the reduction to 2.7, and
is the only one of the three that needs a number field.
⚠ **5.4 took four, and the seams are three**: `…/LinearFormValue.lean` is Liouville's inequality
for the value of a linear form and knows no subspace; `…/SubspaceNormal.lean` is the normal
vector of a hyperplane and the transformed Plücker coordinates, over any field and with no height
in it; `…/SubspaceHeightBounds.lean` is the two bounds on the height of a domain basis;
`…/ExceptionalSubspace.lean` is the pattern, the exceptional set and the milestone.
⚠ **5.5 took two, and the seam is the oldest one**: `…/PolynomialGrid.lean` is the grid lemma,
which is about a polynomial over a field and knows nothing of blocks; `…/SmallPoint.lean` is the
block-wise parametrization and the milestone.
⚠ **5.6 took five, and the seams are the field, the place and the number field**:
`…/LogComparison.lean` is one elementary comparison of logarithms, shared out of
`…/RothTheorem.lean` because both Roth and the Subspace Theorem choose a degree against it;
`…/FormIndexSubspace.lean` is the bridge from Layer 5.3's index to Layer 5.5's non-vanishing
hypothesis, over any infinite field and with no height in it; `…/SubspaceValueBound.lean` is the
local estimate at one absolute value and knows no place; `…/SubspaceKeyInequality.lean` is Step
VI, the product formula against those estimates; `…/PenultimateMinimum.lean` is Steps IV and VI
together and the milestone.
⚠ **6.1 took five as well, and for once none of the seams is a new one**:
`…/WedgeRecovery.lean` is Lemma 7.5.33 read as a function of the subspace, linear algebra with no
height in it; `…/MinimaBounds.lean` is the one estimate on the minima that Layer 4 does not state,
and it is the product formula rather than geometry of numbers; `…/ExponentGrid.lean` is the
rounding device, stated for an arbitrary index type and an arbitrary system of exponents;
`…/WedgeExponentBound.lean` is the box and the negative weight of the wedge exponents, the one
file that knows what a wedge domain is; `…/ParametricSubspace.lean` is Steps VIII and IX and the
milestone.
⚠ **6.2 broke the pattern and took one**: `…/SubspaceTheorem.lean`, and there is no seam in it
because there is nothing to separate — the Subspace Theorem over `K` is Layer 5.1 and Layer 6.1
put together, with the kernels and Northcott on projective space for what those two leave over,
and every one of those four ingredients is imported. It is the shortest milestone of Layer 5 or 6
and the only file in either that introduces no object of its own.
⚠ **6.3 took four, and the seams are three different kinds at once**:
`…/FormBaseChange.lean` is linear algebra over a commutative ring — a linear form carried along a
ring homomorphism — with no place, no height and no number field in it; `…/PlaceConjugation.lean`
is Layer 0.2 restated for *typed* places, which is where Mathlib's normalization of finite places
has to be undone, and it knows nothing about linear forms; `…/ExtensionApproxProd.lean` is the one
file that knows both, and it is the transfer identity; `…/SubspaceAlgebraic.lean` is the Galois
closure and the milestone.
⚠ **6.4 took two, and the seam is between one point and all of them**: `…/AffineProd.lean` is the
affine quantity and its dictionary with the projective one, arithmetic at a single point with no
subspace anywhere in it; `…/SubspaceAffine.lean` is the milestone, four lines on 6.3, and its
converse, which is the rest of the file. It is the first milestone of Layer 6 whose proof is
shorter than its statement, and the only one whose converse is longer than its forward half.
⚠ **6.5 took two as well, and the seam is between linear algebra and arithmetic**:
`…/GeneralPosition.lean` is the local observation — which `n + 1` of the forms to keep at a point
and what keeping them costs — and has no place, no height and no number field in it;
`…/SubspaceGeneralPosition.lean` is the partition into finitely many classes and the appeal to
6.3. It is the only layer of 6 whose first file is pure linear algebra.
⚠ **6.6 took one, and it has no seam**: `…/SubspaceConsistency.lean` is the whole layer, and the
reason is that there was nothing to join — Layer 3.4 and Layer 6.3 at `card ι = 2` are the same
proposition, so the file is three specializations, one piece of plane linear algebra and four
`rfl`s. It is the shortest layer of 6 and the only one whose central claim is an equation between
theorems rather than a theorem.
⚠ **7.1 took two, and the seam is between the one appeal to the summit and the induction that
follows it**: `…/LinearFormSubspaces.lean` is the appeal — the system of forms, its linear
independence, the local estimate at the infinite place of `ℚ` and the number field the
coefficients are moved into — and it knows nothing about variables being eliminated one at a
time; `…/OneLinearForm.lean` is the induction, and it knows no place, no absolute value and no
number field, only that removing coordinates from a point does not raise its height. It is the
first milestone of the roadmap whose seam is neither algebraic nor an import one but a count: the
Subspace Theorem is used once, and the rest is bookkeeping in `ℂ` and `ℚ`.
⚠ **7.2 took one, and the summit is not in it**: `…/BoundedDegreeApproximation.lean` consumes
7.1 as a black box and adds the mean value theorem over `ℂ`, Northcott's theorem for integer
polynomials and the rigidity of a minimal polynomial. It names a place exactly twice, in the two
lines that compare the height of an integer point with its sup norm, and an absolute value, a
number field and the central quantity of the Subspace Theorem not at all: it is the first
milestone of the roadmap that stands on a summit result and speaks none of its vocabulary.
⚠ **7.3 took three, and had to go back to Layer 6 for one of them**:
`…/SimultaneousSubspaces.lean` returns to 6.3 for a second system of forms, because Schmidt's
exponents are read against the product `∏ |q_i|` and 7.1's appeal keeps only the sup norm;
`…/SimultaneousApproximation.lean` is the two inductions, and names no place in a single line of
its mathematics; and
`…/SchmidtExponents.lean` consumes 7.1 and 7.2 and Layer 1.3 and knows nothing else.
⚠ **7.4 took four, and only one of them knows the Subspace Theorem**:
`…/StammeringWords.lean` is words — `V ^ w`, prefixes, stammering — and knows no number;
`…/DigitExpansions.lean` is base-`b` expansions — the approximation a repetition gives and the
irrationality of a non-periodic expansion — and knows no subspace; `…/RepetitionSubspaces.lean`
is the third appeal to 6.3, the first with finite places in it; and
`…/TranscendenceCriterion.lean` is the two cases of one subspace, plus Ridout's route, which
knows no Layer above 3.
⚠ **7.5 took two, and neither knows the Subspace Theorem**: `…/FactorComplexity.lean` is words
again — the complexity, Morse–Hedlund and the pigeonhole — over any finite alphabet, and
`…/ComplexityTranscendence.lean` hands the pigeonhole's repetitions to 7.4's working form and is
thirty lines of proof.
⚠ **8.1 took one**: `…/UnitEquation.lean` is the first file of Layer 8, a single appeal to 6.5 with
three forms at every place.
⚠ **8.2 took one**: `…/UnitEquationSeveral.lean` is the same appeal with `n + 1` forms, and an
induction in two steps around it.
⚠ **8.3 took one**: `…/DecomposableForm.lean` quotes 8.1 once per triangle and nothing above it.
⚠ **8.4 took two, and the seam is between the extension and the form**: `…/SIntegerExtension.lean`
is the passage from `S` to the primes above it, in both directions, and knows no Diophantine
equation; `…/ThueMahler.lean` is the binary forms, 8.3 in the splitting field, the descent and
Thue–Mahler over `ℚ`. The first file is what 8.5 will quote.
Layers 0, 1.1, 1.2, 1.3, 2.1, 2.2, 2.3, 2.4, 2.5, 2.6, 2.7, 3.1–3.8, 4.1–4.5, 5.1–5.6, 6.1–6.6,
7.1–7.5 and 8.1–8.4 together stand at **one hundred and thirty** files,
and nothing suggests the pattern stops.

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
  coefficient shapes at once — and **the forms the applications quote, also landed**: the
  statement with targets in `OnePoint F`, so that the point at infinity is a target;
  **Roth's original theorem**, as the value `2` of the irrationality exponent of every real
  algebraic irrational; **Ridout's theorem**; and the **`p`-adic form**. And **Roth's theorem on
  the projective line — the Subspace Theorem in two variables — also landed**, in both
  directions: the finiteness of the exceptional set of lines for two linearly independent forms
  at each place of `S`, and the recovery of Roth's theorem from it for the forms `X₀` and
  `X₁ − α v X₀`. This is the interface Layers 8.1, 8.3, 8.4 and 8.6 consume, and the central
  quantity `NumberField.approxProd` that Layer 6.3 states the Subspace Theorem with lives
  here. And **Mahler's theorem** on the fractional parts of `(p/q)^k` — **also landed**, with
  the finite part of the product formula under it. And **Thue's theorem** over `ℤ`, the first
  Diophantine equation — **also landed**, from Roth's theorem over `ℚ` at one place, with the
  hypothesis "three pairwise non-proportional linear factors over `ℂ`" read literally. And the
  **strong gap principle** with the resulting **bound on the number of approximations** — **also
  landed**, the bound on the large solutions depending on `κ`, `|S|` and `[F : K]` alone, from the
  core of Roth's proof restated as a theorem of its own. And Roth's theorem with **moving
  targets** — **also landed**, the core of the proof restated once more for targets that change
  along the chain. Layer 3 is complete.
- The **geometry of numbers of a parallelepiped over a number field**: `S`-adic approximation
  domains as a lattice and a convex body — **landed**, with the covolume of the lattice exact and
  the volume of the body — successive minima counted over `K` and the two-sided Minkowski theorem
  for them — **landed** — the rank of a domain and its drop below `n + 1` for negative weight —
  **landed** — **Evertse's lemma** — **landed** — and the passage to **exterior powers**.
- The **Subspace Theorem** — the summit — for a number field and a finite set of places: the
  **parametric** form — **landed** — the projective form with coefficients in the field — **also
  landed** — the form with **algebraic coefficients**, points in `K` and coefficients in a
  finite extension, which is the form the applications quote — **also landed** — and the
  **affine** form for `S`-integral points, the form Layer 8 consumes, with the equivalence
  between it and the projective form proved in **both** directions — **also landed** — and
  **Vojta's general-position** form, for families of forms of any finite sizes, with Layer 6.3
  recovered from it as the case of equal sizes — **also landed** — and the **consistency with
  Layer 3**: on the projective line the Subspace Theorem is Roth's theorem, the two statements
  are one proposition, and Roth's theorem over a number field comes back out of Layer 6 —
  **also landed**. **Layer 6 is complete.**
- The **elementary half of the quantitative theory**: systems of inequalities, the **gap
  principle** for subspaces, the count of **small solutions**, and the reduction of a count of
  subspaces to an interval result.
- The applications that are theorems about numbers: **one linear form with algebraic
  coefficients, at integer points** — **landed**, and with it the first thing the Subspace
  Theorem says about numbers rather than about points — the approximation of algebraic numbers by
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
    ⚠ **5.1 consumed it and 2.4 together**: the affine height of the coefficient tuple of a form
    and `Height.logHeight₁_sum_mul_le` are what bound the height of a form's value, which is
    Corollary 7.5.5;
  - 1.1 and 1.3, Northcott on projective space and with varying degree — every "all but finitely
    many" below is an appeal to one of them; 3.7, Northcott for subspaces — Layer 5.6;
  - 1.2, height and Mahler measure — the base case of Roth's lemma and the comparison
    `H(f_ξ) ≍ H(ξ)^{deg ξ}` of Layer 7.2; ⚠ **7.2 landed without that comparison**: its exponent
    is read against `H(f_ξ)` itself, which is what the mean value theorem produces, so Remark
    7.3.6 has no consumer yet;
  - 2.1–2.3, heights of polynomials, the multivariate Gauss lemma and the upper half of Gelfond's
    inequality for `MvPolynomial` — the height bookkeeping of Layers 2 and 5; 2.4 and 2.5, heights
    of linear forms and matrices;
  - 3.1–3.5, the Plücker point, the height of a subspace, Cauchy–Binet and duality — `h(V(Q))` in
    Layer 5.4 is a subspace height, and Layer 4.5 works in the exterior power that 3.1 builds;
    ⚠ **5.4 is the first consumer of 3.5, and it consumes the coordinate statement, not the
    theorem**: `Submodule.exists_plucker_eq_plucker_compl` at the ranks `n` and `1` is exactly the
    dictionary between the Plücker coordinates of a basis of a hyperplane and the coordinates of
    its normal vector, signs and a common factor included, and 5.4 compares only their *supports*,
    so Schmidt's involution `τ` is harmless. It also consumes 3.2's
    `Submodule.mulHeight_span_range` — the height of a subspace is the height of the tuple of
    maximal minors of any basis — which is what turns `h(V(Q))` into a height of a point;
  - 4.1, 4.2 and 4.4, successive minima, Minkowski's second theorem and the extraction lemma —
    Layer 4.2 is assembled from these three and proves no geometry of numbers of its own, which
    held: ⚠ **4.2 consumed all three as stated**, Cassels' Lemma 1 in its gauge form, both halves
    of the real theorem, the regrouping `Finset.prod_pow_le_prod_range` and the packaged
    extraction lemma, and it spends the extraction twice — once for `μ l ≤ λ (d (l − 1) + 1)` and
    once to show that below `n + 1` the minima over `K` are finite at all; 4.3's
    number-field lattice and its covolume — Layer 4.1; ⚠ **4.1 consumed 4.3's tools and not its
    theorem**: the pseudo-basis `Submodule.exists_pseudoBasis`, the finite half
    `NumberField.FinitePlace.finprod_iSup_eq_inv_absNorm` and the real norm of the mixed space
    `NumberField.mixedEmbedding.norm_mixedSpace`, because the lattice of an approximation domain is
    cut out by local conditions and is not the integral points of a subspace;
  - 5.5, 5.6 and 5.7, Siegel's lemma with entry heights, its relative version and the
    auxiliary-polynomial form — the *only* source of auxiliary polynomials in Layers 2.5 and 5.2;
  - 6.4 and 6.5, heights of `S`-units and the `S`-unit theorem with the `S`-logarithmic lattice —
    Layers 5.1 and 8; ⚠ **5.1 consumed 6.5 as the full lattice it is**: the one thing Lemma 7.5.4
    needs is that every trace-zero vector is within a bounded distance of the `S`-logarithmic
    image, which is `IsZLattice` plus a fundamental domain, and the `S`-regulator itself is never
    named. It also needed one new lemma there, `NumberField.SUnit.mem_unitLattice_iff`, because
    the module system hides the body of `unitLattice`. And **Layer 0.3**, which is where the
    dependence on `ArithmeticHeights` begins: 6.4 *is* 0.3's membership dictionary, 6.5's product
    formula *is* 0.3's in logarithmic form, and 6.5's `NumberField.exists_mem_asIdeal_iff_eq` — a
    nonzero algebraic integer lying in one prime and in no other, the one use either layer makes
    of the finiteness of the class group — supplies the denominators that make `S.integer K` a
    localization.

⚠ **5.5 consumes nothing from `ArithmeticHeights`, and it is the only landed layer of 5 that
does not.** The grid lemma and the small point are statements about a polynomial over a field of
characteristic zero with no height, no place and no lattice in them; what they consume beyond
Mathlib is Layer 2.1 — the several-variable Hasse derivative and its substitution formula — and
Layer 5.2's multidegrees. Mathlib supplies the rest, and the one-variable case is `Polynomial`'s
own `roots`, `rootMultiplicity` and `taylor`.

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
  scope for want of exactly the approximation theorem built here. Layer 6.4 **is landed** and is
  stated so that either can consume it; the curve-side argument is not in this roadmap.
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
| the central quantity | `NumberField.approxProd S∞ S₀ w L x`, the product over `v ∈ S∞` of `(∏ i, w v (L v i x) / ⨆ j, v (x j)) ^ v.mult` times the product over `v ∈ S₀` of `∏ i, w v (L v i x) / ⨆ j, v (x j)`, where `L v i : Module.Dual F (ι → F)` and `x` is mapped into `F`. It is an object, not an abbreviation: it is invariant under scaling `x` by `Kˣ`, bounded above in terms of the forms alone, raised to `[K' : K]` under extension of `K`, and multiplicative in `S`. ⚠ **Landed in Layer 3.4** as `NumberField.approxProd`, and the invariance under scaling needs the `LiesOver` hypotheses (`NumberField.approxProd_smul`): the numerator of a local factor is measured in `F` and the denominator in `K`, and the two scale by the same number only because `w v` lies over `v`. The local sup norm `⨆ j, v (x j)` inside it is written out and has no name, as in `ArithmeticHeights`. The forms are indexed by the underlying `AbsoluteValue K ℝ` of a place, `L : AbsoluteValue K ℝ → ι → Module.Dual F (ι → F)`, so that one family serves both finsets; its values off `S∞` and `S₀` are irrelevant. |
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
  `MvPolynomial.IsHomogeneous`, `MvPolynomial.IsWeightedHomogeneous` — which Layer 5.2's
  multidegree is an instance of, for the weight `Pi.single h 1` — and `degreeOf`;
  `MvPolynomial.divMonomial` and `MvPolynomial.modMonomial`, which are Layer 5.3's "divide out
  the largest power of a variable"; `Polynomial.wronskian` for **two** polynomials
  (`Mathlib/RingTheory/Polynomial/Wronskian.lean`, built for Mason–Stothers);
  `Polynomial.rootMultiplicity`; `Polynomial.gaussNorm`.
- **Siegel's lemma over `ℤ`.** `Int.Matrix.exists_ne_zero_int_vec_norm_le`. Layers 2.5 and 5.2 do
  not use it directly; they use the number-field forms `ArithmeticHeights` builds on top of it.
- **Heights of products of tuples.** `Height.mulHeight_fun_prod_eq` — the height of the
  multiplication table of a family of tuples is the product of their heights — and
  `Height.mulHeight_comp_le`, monotonicity under re-indexing. Layer 5.3's `h(M̃) ≥ h(M)/n` is
  those two and nothing else.
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
`n ≤ w_n^*` and is what Layer 7.3 consumes — and does consume, since 7.3 is landed. **Wirsing's first two lower bounds on `w_n^*`, and
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

⚠ **Layer 3.3 is landed, and what it needed from Mathlib was a dictionary Mathlib has in two
halves that do not meet.** Mathlib has Ostrowski's theorem for `ℚ`
(`Rat.AbsoluteValue.equiv_padic_of_bounded`) and it has the finite places of a number field
(`NumberField.FinitePlace`), and nothing connects them: the first gives an absolute value
*equivalent* to `padicNorm p`, the second a normalized one, and the exponent between them is
exactly what Ridout's `2 + ε` cannot afford to lose. `Rat.exists_prime_padic_eq` is that missing
statement, and the argument that pins the exponent to `1` is a height computation, not a
valuation-theoretic one: the multiplicative height of `p⁻¹` is `p`, its infinite part is `1`, and
Ostrowski applied to every finite place at once says only one of them contributes. Beside it, the
layer adds the local factor at a target in `OnePoint F` and the bounded distortion of the Möbius
change of variable, neither of which has an analogue in Mathlib.

⚠ **Layer 3.4 is landed, and what it needed from Mathlib was one missing fact about places and
nothing else.** The two-variable Subspace Theorem is linear algebra over Roth's theorem: the
determinant of two forms, Cramer's rule read at one absolute value, and the chart
`[x₀ : x₁] ↦ x₁ / x₀`. Mathlib supplies all of that. What it does not supply is that an infinite
place and a finite place never have the same underlying absolute value — obvious, and needed the
moment a choice made on `S` has to be spread to every `AbsoluteValue K ℝ`, which is how Roth's
theorem indexes its targets. `NumberField.InfinitePlace.val_ne_finitePlace_val` is that fact, in
four lines from `v 2 = 2` against `v 2 ≤ 1`. Beside it, the layer adds the central quantity
`NumberField.approxProd` — the object Layer 6.3 states the Subspace Theorem with — and its
invariance under scaling, which is what makes the theorem a statement about subspaces.

⚠ **Layer 3.5 is landed, and what it needed from Mathlib is a piece of elementary arithmetic,
not of approximation theory.** Mahler's theorem is Ridout's theorem applied to one auxiliary
rational, and the only step that is not immediate is that a product of `p`-adic sizes over the
primes of a fixed integer is `1 / d` exactly — the finite part of the product formula, with the
hypothesis that no prime factor is missing. Mathlib has `padicNorm`, `Nat.primeFactors` and the
factorization of a natural number, and nothing that puts them together; `Nat.primesOf` and
`Rat.prod_padicNorm_natCast` are that, in thirty lines. ⚠ The identity fails in one direction
only — over a smaller set of primes the product is too *large* — and that is the direction every
application needs it not to fail in.

⚠ **Layer 3.6 is landed, and Mathlib already had the binary form.** `Polynomial.homogenize`
turns a polynomial in one variable into an element of `MvPolynomial (Fin 2)`, and
`Polynomial.homogenize_eq_of_isHomogeneous` says every homogeneous form is one, so the roadmap's
`G ∈ ℤ[X, Y]` needed no definition. What was missing is small and algebraic: the degree bound on
the dehomogenization `G(X, 1)` that the last lemma leaves to its caller, the value `G(x, 0)` on
the line at infinity, and — the one real input — that an **irrational** root of multiplicity `μ`
of an integer polynomial with three distinct complex roots has `2 μ < deg g`, from
`(minpoly ℚ r) ^ μ ∣ g`. Mathlib has no `rootMultiplicity_pow`, and the proof does not need one.

⚠ **Layer 3.7 is landed, and nothing it needed was missing from Mathlib.** The gap principle is
the fundamental inequality of Layer 0.4 against the triangle inequality at the places of `S`, and
the counts are `Set.ncard_le_ncard_of_injOn` into a product and
`Finset.card_eq_sum_card_fiberwise` over the classes. What was missing was in this repository:
the statement at the core of Roth's proof, which Layer 3.2 had proved only inside a proof by
contradiction.

⚠ **Layer 3.8 is landed, and what it needed from outside the proof was a bound Mathlib lacks.**
Mathlib bounds no single absolute value by the height: there is `Height.mulHeight₁_eq` and the
product formula, but not `max |x|_w 1 ≤ H(x)` for one place, let alone for an absolute value of an
extension lying over a place. The first is the fundamental inequality of Layer 0.4 at one place;
the second is that read through Layer 0.1's classification, where the exponent `t ≤ 1` of a root
of a finite place is exactly what it needs. Both are in `…/FundamentalInequality.lean`. Mathlib's
`Asymptotics.IsLittleO` states the growth condition, and is used once.

⚠ **Layer 4.1 is landed, and what it needed from outside was three facts and two instances.**
Mathlib has the adic valuation, a uniformizer and `Ideal.IsPrime.prod_mem_iff`, but not what they
say about a finite place: that its values on `Kˣ` are exactly the integer powers of `N 𝔭`, so that
there is a largest value below any bound; that an algebraic integer can be a unit at one place and
as small as prescribed at finitely many others; and a covolume for any `𝓞 K`-module of `Kⁱ` —
Mathlib's `covolume_idealLattice` is the case `#ι = 1`. The first two are in
`…/FinitePlaceValues.lean`, the third, from `ArithmeticHeights`' pseudo-basis, in
`…/ModuleCovolume.lean`. And Mathlib's instance search finds the Borel structure and the Haar
property of the volume on `mixedSpace K` but not on `ι → mixedSpace K`: the product instances ask
for a `∀ i`-family, which it does not assemble. Both are declared once, beside the covolume.

⚠ **Layer 4.2 is landed, and what it needed from outside was one fact Mathlib had and one
constant it had too.** That tuples of `Kⁱ` independent over `ℚ` have mixed embeddings independent
over `ℝ` is Mathlib's `linearIndependent_algebraMap_comp_iff` read in the coordinates of
`latticeBasis`, whose coordinates on the mixed embedding are those of `integralBasis`
(`latticeBasis_repr_apply`); `NumberField.mixedEmbedding.linearIndependent_pi` says so once. The
constant `c_K` is Mathlib's `NumberField.house` of the members of `integralBasis K`, and
`one_le_house_of_isIntegral` makes it at least `1`.

⚠ **Layer 4.3 is landed, and it needed nothing from outside.** That a spanning set contains a
basis of what it spans, indexed by `Fin` of the dimension, is Mathlib's
`Submodule.exists_fun_fin_finrank_span_eq`; that a bounded set holds finitely many points of an
`𝓞 K`-lattice was already proved for 4.2's attainment, and is now public as
`NumberField.finite_setOf_mem_of_isBounded`.

⚠ **Layer 4.4 is landed, and what it needed from outside was a fundamental domain Mathlib had.**
Simultaneous approximation by `S₀`-integers is not in Mathlib; it took one file, from 4.1's prime
avoidance (`NumberField.FinitePlace.exists_apply_eq_one_forall_apply_le`), Mathlib's
`Ideal.IsMaximal.exists_inv` and one geometric sum at the finite places, and Mathlib's
`ZSpan.fract` for `latticeBasis` at the infinite ones — no Chinese remainder theorem and no
localization. The induction needed only linear algebra Mathlib states:
`Matrix.mulVec_surjective_iff_isUnit` solves (7.40), and
`linearIndependent_of_top_le_span_of_card_eq_finrank` keeps the forms independent after one is
removed.

⚠ **Layer 4.5 is landed, and what it needed from outside was Cauchy–Binet and Cramer's rule.**
Laplace's identity is `ArithmeticHeights` 3.4's `exteriorPower.sum_plucker_mul_plucker` read for
forms; the second half of Lemma 7.5.33 is Mathlib's `Matrix.cramer_one`; the double count of the
weight is `Finset.card_filter_powersetCard_subset`. What Mathlib lacks and 4.5 adds is small: the
bounds `p!` and `1` for a determinant at an archimedean and a nonarchimedean place
(`AbsoluteValue.apply_det_le`, `AbsoluteValue.apply_det_le_of_isNonarchimedean`), and that an
infinite place is archimedean (`NumberField.InfinitePlace.not_isNonarchimedean`). ⚠ 4.5 consumed
`ArithmeticHeights` 3.1 and 3.4 as stated and **not** 3.5's duality: the pairing of `⋀^p` with
`⋀^k` that the book's proof of 7.5.33 uses never appears.

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
⚠ **The two missing bounds are optional, and 7.3 has now shown it.** Every later milestone that
names 1.3 — 7.3 above all — is served by what is landed, and 7.3 is landed: it consumes the
third inequality, Liouville's bound and the box principle, and neither of the first two. The one
consumer of the first two is 1.4, which is itself optional. A contributor may treat 1.3 as
complete and lose nothing outside this layer.

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
alone, it is landed, and 7.3 is landed too.

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

**3.1 Approximation classes** (Bombieri–Gubler 6.4.2–6.4.4) — **landed**. For a
finite index set `A` and a family of maps `φ a : X → [0, 1]` with `∑ a, φ a x ≤ 1`, the partition
of `X` by the cell of side `1/N` containing `(φ a x)_a`: the number of nonempty cells is at most
`(N + |A|).choose |A|` (Lemma 6.4.3) — `Set.ncard_image_cellIndex_le`, and the count of *labels*
is that number exactly, `Set.ncard_setOf_sum_le` — and an infinite `X` has an infinite cell for
every `N`, `Set.Infinite.exists_cellIndex_eq`. With it: `(L, M)`-**independent** sequences,
`h(β 0) ≥ L` and `h(β (j + 1)) ≥ M h(β j)`, exist inside every infinite subset of `K`, by
Northcott — `NumberField.exists_isHeightIndependent`, and the two reductions together are
`NumberField.exists_cellIndex_eq_and_isHeightIndependent`. Stated once, abstractly, because
Layers 3.2 and 3.7 each use it for a different family `φ`. ⚠ **5.1 does not use it**: its cells
are cells of a cube, not of the simplex; see 5.1. In
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
compare — `NumberField.roth_key_inequality`. ⚠ Since 3.7 the steps after the reduction are a
theorem of their own, `NumberField.roth_no_chain` — above a height `L`, no `(L, M)`-independent
chain of `m + 1` solutions in one class — with `ε`, `N`, `m` and `M` the definitions
`NumberField.rothEps`, `rothClassSize`, `rothChainLength` and `rothRatio` of `κ`, `|S|` and
`[F : K]`; the theorem is that statement fed by the reduction, and its statement did not change.
⚠ Since 3.8 that theorem is itself the constant case of `NumberField.roth_no_moving_chain`, in
which every member of the chain has its own targets: Steps I and II take the index at a target
*point* and one height constant per coordinate, Steps III to V one target and one size bound per
coordinate, and no statement consumed outside 3.2 changed.
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

**3.3 The forms applications quote — landed.** Each is 3.2 for a choice of data, and each is
stated. *Targets at infinity* (6.2.5): a target may be the point `∞`, with local factor
`min 1 (v β)⁻¹`; by a rational Möbius change of variable, under which `mulHeight₁` changes by a
bounded factor. State 3.2 with targets in `OnePoint F` so that every later form is an instance.
*Roth:* `irrationalityExponent α = 2` for every real algebraic irrational `α` — the value Layer
1.1 leaves open between `2` and `d`. *Ridout:* for real algebraic `α`, finite sets of primes
`S₁`, `S₂` and `ε > 0`, finitely many `p/q` in lowest terms with
`|α − p/q| · ∏_{ℓ ∈ S₁} |p|_ℓ · ∏_{ℓ ∈ S₂} |q|_ℓ ≤ max(|p|, |q|)^{−2−ε}`, with target `0` at
`S₁` and `∞` at `S₂`, after splitting the solutions by which of `p`, `q` a prime of `S₁ ∩ S₂`
divides. *`p`-adic* (6.2.6): for `α` in a number field `F`, `w` over `Rat.AbsoluteValue.padic p`
and `ε > 0`, finitely many `n ∈ ℤ` with `w (α − n) ≤ |n|^{−1−ε}`.
All four are proved, in `…/{RationalPlaces,RothInfinity,RothRational,Ridout}.lean`, as
`NumberField.finite_setOf_prod_onePointApprox_le`, `Real.irrationalityExponent_eq_two`,
`Rat.finite_setOf_ridout` and `Rat.finite_setOf_apply_intCast_sub_le`, with
`Rat.finite_setOf_onePointApprox_mul_prod_le` — one target at the infinite place of `ℚ` and one
at each prime of a finite set — as the shape the last two are instances of, and
`Real.finite_setOf_min_one_abs_sub_le` as the classical one-place statement over `ℚ` with the
naive height.

⚠ **The local factor at the target `∞` is `(max 1 |β|_v)⁻¹`, not the `min 1 (|β|_v)⁻¹` written
above.** The two are the same number for every `β ≠ 0`; at `β = 0` Lean's `(0 : ℝ)⁻¹ = 0` makes
the second `0`, where the factor's value is `1`. The reciprocal of a maximum needs no case
distinction and no hypothesis, and `AbsoluteValue.onePointApprox` is defined that way. This is
the roadmap's only wrong formula in Layer 3, and it is wrong only at one point.

⚠ **"A Möbius change of variable" is `β ↦ (β − c)⁻¹`, and `c` is not free.** Inverting alone
*exchanges* the targets `0` and `∞` rather than removing `∞`, so it cannot clear a configuration
that has both; the base point `c ∈ K` must avoid every finite target, which it can because `K` is
infinite and `S` is finite. The distortion is bounded at each place — that is
`AbsoluteValue.min_one_sub_onePointMobius_le`, and its finite-target case splits on whether `β`
is close to `c`, because when it is, the new factor is large but the old one is bounded below —
and the constant is absorbed by lowering `κ` to some `κ₁ ∈ (2, κ)` and collecting the finitely
many solutions of small height by Northcott. That is the only step of Layer 3.3 that uses
`κ > 2` with room to spare; everything else is uniform in `κ`.

⚠ **The dictionary is the milestone, and its content is the exponent.** Mathlib's Ostrowski gives
only that a finite place of `ℚ` is a positive *power* of some `padicNorm p`. A power `≠ 1` would
be fatal: Ridout's `2 + ε` would become `(2 + ε)/t`, and no choice of `ε` repairs that. The
exponent is pinned to `1` in `Rat.exists_prime_padic_eq` by a height computation — `H(p⁻¹) = p`,
its infinite part is `1`, and Ostrowski applied to *every* finite place at once says exactly one
of them contributes — and the converse, that every `padicNorm p` *is* a finite place, then falls
out of Layer 0.1's Ostrowski for a number field plus the forward half.

⚠ **The `p`-adic form gains its exponent at the infinite place, and this is why 3.3 cannot be
skipped.** With the `p`-adic place alone the best 3.2 gives is `w (α − n) ≤ |n|^{−2−ε}`; the
exponent `1 + ε` comes from putting the target `∞` at the infinite place, where a rational
*integer* has local factor exactly `H(n)⁻¹`. The `OnePoint` form is load-bearing, not
presentational — the `H(n)⁻¹` is an equality for integers and an inequality for everything else,
so no crude bound recovers it.

⚠ **A prime of `S₁ ∩ S₂` carries two factors and Roth's theorem carries one target per place**,
and the reconciliation is coprimality, not a strengthening of 3.2: such a prime divides at most
one of `p` and `q`, so on each of the `2^{|S₁ ∩ S₂|}` classes cut out by *which* it divides, one
of the two factors is `1` and a single target accounts for both. Ridout's solution set is the
union of those classes. This is the only statement of Layer 3.3 whose proof splits the solutions,
and the split is the roadmap's own, made precise.

⚠ **The two classical statements are about the *naive* height, and nothing is lost.** Over `ℚ`
the multiplicative height of `p/q` in lowest terms is `max (|p|, q)` exactly
(`Rat.mulHeight₁_eq_max`), so Ridout's `max(|p|, q)^{−2−ε}` is 3.2's `H(β)^{−κ}` with no
constant left over. The place where a constant *does* appear is the passage from Layer 1.1's
`LiouvilleWith`, which measures against the denominator alone: there the two differ by a bounded
factor, and the factor is absorbed by using two exponents `2 < κ' < κ` rather than one.

**3.4 Roth's theorem on the projective line** — **landed**, in
`DiophantineApproximation/ProjectiveTarget.lean`, `…/ApproxProd.lean` and
`…/RothProjective.lean`. The Subspace Theorem of Layer 6.3 for `Fintype.card ι = 2`, proved
*here*, from 3.3: at each place a solution `x` is close to the zero of at most one of the two
forms, so the solutions split into `2^{|S|}` sets according to which, and on each set
`approxProd` is comparable to the left side of 3.2 for that choice of targets, with
`β = x 1 / x 0`. Conversely 3.2 is this statement for `L v 0 = X 0`, `L v 1 = X 1 − α v X 0`
(Bombieri–Gubler, Example 7.2.7); both directions are proved. This is the interface Layers 8.1,
8.3, 8.4 and 8.6 consume, so that the two-variable unit equation and everything resting on it
are available without Layers 4–6.
`NumberField.approxProd` is the central quantity, `NumberField.approxProd_smul` its invariance
under scaling, `NumberField.exists_finset_submodule_of_approxProd_le_card_two` the theorem,
`NumberField.finite_setOf_prod_min_one_le_of_subspace` the converse as an implication and
`NumberField.finite_setOf_prod_min_one_le_card_two` the roundtrip;
`NumberField.finite_setOf_prod_onePointApprox_le_const` is 3.3 with a constant, which both
directions consume.

⚠ **The exceptional subspaces of `ℙ¹` are its points, and the point at infinity is one of them
by force.** For the coordinate forms, a point with `x 0 = 0` makes one factor of `approxProd`
vanish, so it satisfies the hypothesis for *every* `ε` and every height while lying on no line
`K ⬝ (1, β)`. The conclusion is therefore "finitely many points of `ℙ¹(K)`", never "finitely
many `β ∈ K`": the affine reading of the milestone above — "with `β = x 1 / x 0`" — is the right
reading of the *proof* and the wrong reading of the *statement*, and the line at infinity has to
be put into the finite set by hand.

⚠ **`approxProd` is a function on projective space only because the absolute values lie over the
places.** The numerator of a local factor is measured by `w v`, an absolute value of `F`, and the
denominator by `v`, an absolute value of `K`; under `x ↦ c ⬝ x` the first scales by
`|c|_{w v}` and the second by `|c|_v`, and these agree exactly under `LiesOver`. The conventions
table below claims the invariance with no hypothesis, and that is wrong: the hypothesis is free,
because every layer carries it, but it belongs in the statement.

⚠ **Linear independence enters exactly once, as a determinant.** The hypothesis
`LinearIndependent F (L v)` is used only through `a₀ b₁ − a₁ b₀ ≠ 0`, and everything local is
Cramer's rule read at one absolute value: `|det| · max(1, |β|) ≤ (∑ |coefficients|) · max_i |L_i|`
is what stops both normalized values from being small at the same point. This is the whole of the
linear algebra in the milestone, and it is why the general `n` of Layer 6.3 is a different
problem rather than a longer version of this one.

⚠ **The comparison between a form and a target needs a constant that grows with the target.** At
`β = t + 1` the truncated factor `min(1, |β − t|)` is `1` while the normalized value of the form
is `1 / max(1, |β|)`, so no absolute constant compares them; the working constant is
`(2 + 2|t|)/|b|` for the form `a X₀ + b X₁` with zero `t = −a/b`, and the proof splits at
`|β| = 2 + 2|t|`. Both directions therefore produce an inequality with a constant in front of the
height, and both are finished the way 3.3 finishes its Möbius change of variable — at an exponent
strictly between `2` and `κ`, with Northcott collecting the bounded-height remainder.

⚠ **The `2^{|S|}` split needs a choice function on *every* absolute value of `K`, not on `S`.**
Roth's theorem indexes its targets by an arbitrary `AbsoluteValue K ℝ`, so the choice of which
form is small must be extended off `S` — twice, with `Function.extend` — and the two extensions
compose only because no infinite place has the underlying absolute value of a finite place. That
last fact is `NumberField.InfinitePlace.val_ne_finitePlace_val`, which is not in Mathlib.

⚠ **The whole milestone is stated for an arbitrary index type with two elements, never `Fin 2`.**
`Fintype.card ι = 2` is unpacked to two distinct elements exhausting `ι`, and nothing is
transported along an equivalence with `Fin 2`: the transport would have to be carried through
`approxProd`, through `LinearIndependent` and through `Module.Dual`, where it buys nothing. The
only two places `Fin 2` appears are the supremum over the index type and the height of the
tuple, and both are one lemma. This is what makes Layer 6.6 — "for `card ι = 2`, 6.3 is 3.4" —
a matter of discharging one equation rather than a translation, and 6.6, now landed, is exactly
that: the two statements turned out to be the same proposition, checked by `rfl`.

**3.5 Mahler's theorem on `(p/q)^k`** (Mahler 1957; Bombieri–Gubler 6.2.7 for `3/2`) —
**landed**, in `DiophantineApproximation/{PrimeProducts,MahlerPowers}.lean`. For coprime
integers `p > q ≥ 2` and `ε > 0`, the distance from `(p/q)^k` to the nearest integer exceeds
`exp (−ε k)` for all but finitely many `k`. Route: 3.3 over `ℚ` — as Ridout's theorem, with `S₁`
the primes of `q`, `S₂` the primes of `p` and the target `1` at the infinite place — applied to
`β = N q^k / p^k` with `N` the nearest integer.
`Nat.eventually_exp_neg_lt_abs_sub_round` is the theorem,
`Nat.finite_setOf_exists_int_abs_sub_ratPow_le` the finiteness under it and
`Nat.finite_setOf_exists_int_abs_sub_ratPow_le_rpow` the form Ridout's theorem actually gives;
`Nat.primesOf` and `Rat.prod_padicNorm_natCast` are the arithmetic input. The acceptance test for
3.3, and the input to the formula `g(k) = 2^k + ⌊(3/2)^k⌋ − 2` in Waring's problem for large `k`,
which is not a target.

⚠ **The route above is the reciprocal of the one this section used to prescribe, and that is not
a matter of taste.** The prescription was `β = p^k / (N q^k)` with the target `0` at the primes
of `p` and `∞` at those of `q`. That is correct mathematics, but the denominator is then
`N q^k / gcd(N, p^k)`, whose prime factors need not divide `p q` at all: the product over the
primes of `q` is only an estimate, and the cancellation against the height has to be done by
naming the gcd. In the orientation used here the denominator divides `p^k`, so the product over
the primes of `p` is `1 / β.den` **exactly**, and the whole cancellation is the height bound
`max |β.num| β.den ≤ 2 β.den`. Both orientations prove the theorem; only one never mentions
`gcd(N, p^k)`. ⚠ The sentence above about "the factor `|N|_ℓ` that appears when `gcd(N, p) ≠ 1`"
described the other orientation, and in this one no such factor ever appears.

⚠ **Ridout's theorem is needed, and Roth's is not enough — concretely.** Without the two products
over the finite places the left-hand side of the inequality is smaller by `p^{−2k}` and no choice
of `ε` makes it hold. This is the sense in which 3.5 is the acceptance test of 3.3 rather than of
3.2: it is not that the finite places make the proof shorter, it is that the statement is out of
reach without them.

⚠ **The exceptional set is genuinely nonempty, so the conclusion is `∀ᶠ` and not `∀`.** At
`k = 0` the number `(p/q)^0` is the integer `1` and the distance is `0`, which fails the
inequality for every `ε`. ⚠ And **no bound on the exceptional set is asserted or available**:
that is Roth's ineffectivity, inherited unchanged, and it is the reason the milestone below
asks only for finiteness.

⚠ **The finiteness under the theorem quantifies over every integer, not over the nearest one.**
`Nat.finite_setOf_exists_int_abs_sub_ratPow_le` says that only finitely many `k` admit *some*
integer within `exp(−ε k)` of `(p/q)^k`; the `round` form is the special case, and the proof
therefore never uses the minimality of `round`. The two are equivalent, but only the first is
what Ridout's theorem produces.

⚠ **`q ≥ 2` and the coprimality are the same hypothesis twice, and both are needed.** If `q = 1`,
or if `q ∣ p`, then `(p/q)^k` is an integer and the distance is `0` for every `k`. The acceptance
criteria record both as rejection tests, at `(3, 1)` and at `(4, 2)`.

**3.6 Thue's equation** (Thue 1909; Bombieri–Gubler 6.2.1) — **landed**, in
`DiophantineApproximation/{BinaryForm,ThueEquation}.lean`. For `G ∈ ℤ[X, Y]` homogeneous with at
least three pairwise non-proportional linear factors over `ℂ` and `m ≠ 0`, the equation
`G(x, y) = m` has finitely many solutions `(x, y) ∈ ℤ²`. By the book's direct argument from the
classical case of 3.3; Layer 8.3 contains it, and it is here as the first Diophantine equation the
roadmap solves and the test that 3.3 is usable. The statement is
`MvPolynomial.IsHomogeneous.finite_setOf_eval_eq`, for `G : MvPolynomial (Fin 2) ℤ` with
`G.IsHomogeneous d` and three linear forms `l i 0 X + l i 1 Y` over `ℂ`, pairwise of nonzero
determinant, each dividing `G`; under it `Polynomial.finite_setOf_eval_homogenize_eq` is the
same theorem for `g.homogenize d` with the hypothesis counted on the complex roots of `g`, the
point at infinity counting once when `deg g < d`. The approximation input is
`Real.finite_setOf_pow_abs_sub_div_mul_pow_le` — Roth's theorem for pairs of integers,
`|ξ − x / y| ^ μ |y| ^ e ≤ C` finitely often when `e > 2 μ` — and the exceptional set of one
root is `Complex.finite_setOf_norm_div_sub_pow_mul_pow_le`.

⚠ **This is not the book's reduction, and the difference is the multiplicities.**
Bombieri–Gubler's proof of 6.2.1 factors `G` into irreducible forms over `ℤ`, changes coordinates
so that `Y ∤ G`, and uses the box principle over the divisors of `m` to show that only one
irreducible factor can carry infinitely many solutions — `x / y` accumulates at a zero of each —
so that the direct argument ("the other factors are bounded away from `0`") is only ever applied
to a separable form. Here the direct argument is run on `G` itself, with multiplicities, which
avoids the factorization in `ℤ[X, Y]` and the change of coordinates and pays with the exponent:
at the root `r` nearest to `x / y` it is `d / μ`, not `d`. For an irrational root `d / μ > 2`
still holds, and that is `Polynomial.two_mul_count_roots_lt_natDegree`: `(minpoly ℚ r) ^ μ ∣ g`,
the minimal polynomial has degree at least `2`, and in degree exactly `2` the third distinct root
has to come from the cofactor. For a rational root it does not: `X ^ 2 (X ^ 2 − 2 Y ^ 2)` has the
root `0` with `μ = 2` and `d = 4`, where the exponent is exactly `2` and Roth's theorem says
nothing. There **Liouville's inequality with exponent `1`** takes over —
`|x / y − c| ≥ 1 / (c.den |y|)` unless `x / y = c`, and `x / y = c` makes `G(x, y) = 0` — and
needs only `μ < d`. This milestone's "the book's direct argument" is the book's argument for an
irreducible form; for the theorem as stated, which allows repeated factors, either the reduction
or this repair is needed.

⚠ **The nearest root decides the case, and only one of three cases is approximation theory.**
A non-real root stays `|Im r|` away from every real `x / y`; a rational one is Liouville's
inequality above; only an **irrational real** nearest root goes to Roth's theorem. And the line
at infinity costs nothing: if `Y ∣ G` then `y ∣ m`, so `|y| ≤ |m|`, and `|x|` is bounded by the
size of the roots — the book changes coordinates instead.

⚠ **Only Roth's theorem over `ℚ` at the real place is used** —
`Real.finite_setOf_min_one_abs_sub_le` — and no finite place appears. "The test that 3.3 is
usable" is right in the sense that the input is 3.3's classical case; it is not a test of
Ridout's theorem, which 3.5 was.

⚠ **What the proof uses is three zeros, not three factors.** A linear form dividing `G` vanishes
at one point of `ℙ¹(ℂ)`, and two non-proportional forms at different points; the statement takes
the factors because this milestone does, and the converse — a zero gives a factor — is true and
not needed.

⚠ **`m ≠ 0` and "three" are both sharp**, and for different reasons. With two linear factors
Pell's equation `x ^ 2 − 2 y ^ 2 = 1` has infinitely many solutions; with three, of which one is
rational, `x ^ 3 − x y ^ 2 = 0` has the whole line `x = 0`. ⚠ **Nothing is effective**: the
solutions are finitely many and no bound on them is asserted or available, since each
exceptional set is finite only because Roth's is.

**3.7 Counting approximations** (Bombieri–Gubler, Theorem 6.5.4, Lemma 6.5.6 and 6.5.7; Davenport
and Roth 1955 for one place) — **landed**, in
`DiophantineApproximation/{GapPrinciple,CountingApproximations}.lean`, with the core of Roth's
proof exposed in `…/RothTheorem.lean`. *The strong gap principle:* if `β ≠ β'` are solutions of
3.2 in one approximation class of size `1/N` with `h(β) ≤ h(β')`, then
`h(β') ≥ ((1 − |S|/N) κ − 1) h(β) − log 4`. *The count in a window:* with
`c = (1 − |S|/N) κ − 1 > 1`, at most `⌈log A / log ((c + 1)/2)⌉ · (N + |S|).choose |S|` solutions
have `h(β) ∈ (X, A X]`, for `X ≥ log 16 / (c − 1)`. *The count of large solutions:* with `ε`,
`m`, `L`, `M`, `N` chosen as in 6.5.7, the solutions with `h(β) > L` number at most
`m ⌈log M / log ((c + 1)/2)⌉ (N + |S|).choose |S|` — a bound depending only on `κ`, `|S|` and
`[F : K]`, while `L` depends on the heights of the targets — and those with `h(β) ≤ L` are
counted by the window bound and by Northcott. Absolute logarithmic heights throughout. ⚠ This is
a bound on the **number** of solutions and gives no bound on their height; that asymmetry is the
ineffectivity of the method, and the docstring of the count says so.

The statements are `NumberField.mul_absLogHeight₁_sub_le_of_approxClass_eq` (the gap principle,
for two solutions with one `NumberField.approxClass`), `NumberField.ncard_setOf_absLogHeight₁_mem_Ioc_le`
(the window) and `NumberField.exists_ncard_setOf_lt_absLogHeight₁_le` (the large solutions,
bounded by `NumberField.rothLargeCount κ |S| [F : K]`, whose type shows that it sees nothing
else). Under the first, `NumberField.mul_absLogHeight₁_sub_le_of_localApprox_le` takes any vector
of exponents `λ ≥ 0` governing the local factors of both points. The combinatorics is in two
lemmas that know no heights: `Set.ncard_le_ceil_mul_ncard_of_gap`, points with a multiplicative
gap in a window, and `Finset.card_le_mul_of_not_exists_chain`, a finite set with small blocks and
no chain of `m + 1` points — the book's greedy grouping.

⚠ **The count needed Roth's proof restructured.** A finiteness theorem bounds no number; what
6.5.7 consumes is the statement inside 3.2's proof — above a height `L`, no `(L, M)`-independent
chain of `m + 1` solutions lies in one class — with `m`, `M` and `N` visibly independent of the
targets. 3.2 had proved it only inside one proof by contradiction, with `ε`, `N` and `m` drawn
from existentials. It is now `NumberField.roth_no_chain`, the parameters are the definitions
`NumberField.rothEps`, `rothClassSize`, `rothChainLength` and `rothRatio`, and Roth's theorem is
derived from it with its statement unchanged. 3.8 restructured it once more, for targets that
change along the chain: `roth_no_chain` is now the constant case of
`NumberField.roth_no_moving_chain`, with `L = [K : ℚ] (1 + ∑ v, h(α v)) / δ`.

⚠ **The window hypothesis is `X ≥ log 16 / (c − 1)`; the book's is `X >`.** Bombieri–Gubler
state Lemma 6.5.6 strictly and apply it in 6.5.7 (b) at equality; the proof needs only `≤`. The
count of small solutions that 6.5.7 (b) then writes, `⌈log L / log ((c + 1)/2)⌉ (N + |S|).choose
|S|`, has `log L` where the lemma — at `X = log 16 / (c − 1)` and `A = L / X` — gives
`log (L / X)`; the first bounds the second only when `X ≥ 1`, that is when `c ≤ 1 + log 16`. The
acceptance criteria state the count the lemma gives.

⚠ **A solution equal to a target lies in no class of the book, and the lemma counts it.** The
book classifies the non-trivial approximations by the profile `log Λ_v(β) / log Λ(β)`, which means
nothing when `Λ(β) = 0`; `NumberField.approxClass` puts such a `β = α v` in the corner `N e_v` of
the simplex, where the class bounds (6.9) and (6.10) still hold. The gap principle uses of the
class only those bounds, so the book's first step — shrinking `S` to the places where
`|β − α v| < 1` — is not needed either.

⚠ **The large-solution bound has one block per class fewer than the book's.** No chain of `m + 1`
solutions leaves at most `m` blocks in each class, and `m + 1` is the number of variables of the
auxiliary polynomial; the book's `m` is its number of variables.

**3.8 Moving targets** (Vojta; Bombieri–Gubler, Theorem 6.5.2) — **landed**, in
`DiophantineApproximation/MovingTargets.lean`, with the core of Roth's proof restated for moving
targets in `…/RothTheorem.lean`. For a sequence of pairs `(α_j, β_j)` with `α_j : S → F`,
`β_j ∈ K` and `1 + ∑ v, h(α_j v) = o(h(β_j))`, only finitely many `j` have `β_j` a solution of
the inequality of 3.2 with targets `α_j` — `NumberField.finite_setOf_prod_min_one_le_of_isLittleO`
— and in the book's form, no infinite sequence consists of solutions,
`NumberField.not_forall_prod_min_one_le_of_isLittleO`. Heights in the growth condition are
absolute, the `o` is Mathlib's `Asymptotics.IsLittleO` along `atTop`, and the inequality is 3.2's.
The proof is the book's five lines once 3.2 is structured for it, and it is: the core of 3.2 is
now `NumberField.roth_no_moving_chain` — there is a `δ > 0`, depending on `K`, `S`, `[F : ℚ]` and
`κ` and on no target, such that no chain of `m + 1` solutions in one class with heights growing
by the ratio `M`, each member with its own targets, has `1 + ∑ v, h(α_j v) ≤ δ h(β_j)`
throughout. The `o` supplies the `δ`; Mahler's reduction, run on the indices with each pair
classified at its own targets, supplies the chain.

⚠ **The targets enter Roth's proof in two places, and the book names one.** Its proof of 6.5.2
says that only (6.11), the height of the auxiliary polynomial, changes. The Taylor expansion at a
place of `S` carries the size of the target as well — the `log⁺ |α_v|_{v,K}` of (6.16), which is
the `2 |S| max log⁺ |α_v|` inside the `C₂` of (6.19) — and with moving targets that term must be
`o(D)` too. It is bounded by the height of the target, `max |x|_w 1 ≤ H(x)` for `w` over a place
of `K`, which is Layer 0.1's classification:
`NumberField.max_apply_one_le_mulHeight₁_of_liesOver_infinitePlace` and its finite twin. With that
fix the milestone's phrase is true of the whole proof: the targets enter only through
`∑ v, h(α_j v)`.

⚠ **3.2 was restructured, and nothing outside it had to change.** Steps I and II take the index at
a target point `(α_0 v, …, α_m v)` — Layer 2.6 always allowed one — and one height constant per
coordinate; Steps III to V take one target and one size bound per coordinate; 3.7's
`roth_no_chain` is the constant case of `roth_no_moving_chain`. Roth's theorem and everything its
consumers quote are unchanged; the only pinned shape that moved is the landed Steps I and II
example in `Suggested.lean`.

⚠ **The conclusion counts indices, and the `1 +` is load-bearing.** A sequence may repeat a pair,
and the statement bounds the set of `j`, not of values. Without the `1`, the constant pair
`(0, 0)` over `ℚ` at `S = {∞}` satisfies `0 = o(0)` and is a solution at every index; with it,
the growth condition forces `h(β_j) → ∞`.

⚠ **A solution equal to one of its own targets is classified, not discarded.** 3.2 throws away
the at most `|S|` values `β` equal to a target; with moving targets there may be infinitely many
such indices, and 3.7's `NumberField.approxClass` at the pair's own targets puts each in a corner
of the simplex, where (6.9) and (6.10) still hold. The proof therefore never needs that
`β_j = α_j v` forces `h(α_j v) = h(β_j)`, which is the invariance of the absolute height under
extension of the base field.

⚠ **`o` cannot be weakened to `O`.** With the targets equal to the approximations every index is
a solution and `1 + h(α_j) = O(h(β_j))`. The quantitative form, 6.5.3, replaces the `o` by
`δ(κ) h(β_j)` with an explicit `δ(κ)`; here `δ` is an existential and depends on `K`, `S` and
`[F : ℚ]` as well as on `κ`.

### Layer 4: parallelepipeds over a number field

Schmidt's proof is geometry of numbers applied to a family of parallelepipeds. Bombieri–Gubler
run it in the adèles (their 7.5.6 and Appendix C.2). This layer runs it in the **real**
formulation `ArithmeticHeights` pins — a `ZLattice` in a real vector space and a convex body —
and for forms with coefficients **in `K`**. Both choices are free: Layer 6.3 removes the
restriction on the coefficients by the book's own Remark 7.2.3, and the adelic second theorem is
recovered below from `ArithmeticHeights` 4.2 and 4.4. No adèle and no Haar measure on a local
field appears.

**4.1 Approximation domains** (Bombieri–Gubler 7.5.6, Lemma 7.5.7, Corollary 7.5.8) — **landed**,
in `…/{FinitePlaceValues,ModuleCovolume,ApproximationDomain,ApproximationVolume}.lean`. Throughout
Layers 4 and 5 and in 6.1 the set of places consists of **every** infinite place together with a
finite `S₀` — a domain with no condition at some infinite place is unbounded there, and 6.2 adds
the missing infinite places before it starts. For forms `L v i : Module.Dual K (ι → K)` linearly
independent for each such `v`, exponents `c v i : ℝ` and `Q ≥ 1`, the **approximation domain**
`NumberField.approxDomain S₀ L c Q : Set (ι → K)` is the set of `x` with
`v (L v i x) ≤ Q ^ c v i` for every infinite place `v`, every `v ∈ S₀` and all `i`, and
`v (x j) ≤ 1` for every finite place `v ∉ S₀` and all `j`. It is a set of points of `Kⁿ⁺¹` and
is defined as one. Its **weight** `NumberField.approxWeight` is
`∑ v : InfinitePlace K, v.mult * ∑ i, c v i + ∑ v ∈ S₀, ∑ i, c v i`, the exponent of `Q` in the
product of all local bounds in Mathlib's normalization; Bombieri–Gubler's `d ∑ c` is this number
after their `Q` is replaced by `Q^d`. The structure, `NumberField.approxDomain_eq`: the conditions
at the finite places cut out a full `𝓞 K`-submodule `Λ = NumberField.approxModule` of `Kⁿ⁺¹`, the
conditions at the infinite places a compact convex symmetric body `B = NumberField.approxBody` in
`(K ⊗ ℝ)ⁿ⁺¹ = ι → mixedSpace K` that is balanced over every completion
(`NumberField.mul_mem_approxBody`), and the domain is `Λ ∩ B`. The covolume and volume formulas
that replace Lemma 7.5.7: with `a v i` the largest value of `v` that is at most `Q ^ c v i`
(`NumberField.FinitePlace.floorValue`), the index of `Λ` in `(𝓞 K)ⁿ⁺¹` (a generalized index; `Λ`
need not be contained in it) is `∏ v ∈ S₀, v (det (L v)) * ∏ i, (a v i)⁻¹`
(`NumberField.covolume_approxLattice`), and the volume of `B` is the volume
`2 ^ (r₁ (n + 1)) π ^ (r₂ (n + 1))` of the unit body times
`∏ v : InfinitePlace K, (v (det (L v))⁻¹ * ∏ i, Q ^ c v i) ^ v.mult`
(`NumberField.volume_approxBody`). Hence `vol B / covol Λ` is `Q` to the weight up to a factor
between two constants depending only on `K`, `S₀`, `n` and the determinants: at most
`NumberField.approxConst S₀ L` and at least that divided by `∏ v ∈ S₀, N 𝔭_v ^ (n + 1)`
(`NumberField.volume_div_covolume_le`, `NumberField.le_volume_div_covolume`). ⚠ The book states
the finite-place volume as an equality in `Q ^ c v i`; it is an equality in `a v i` and an
inequality up to `∏ v ∈ S₀, (absNorm v) ^ (n + 1)` in `Q ^ c v i`, because `Q ^ c v i` need not
lie in the value group. **Confirmed**: at the `2`-adic place of `ℚ`, in one variable with `L = id`,
`c = 1` and `Q = 3/2`, the covolume is `1` where the book's formula gives `2/3`.

⚠ **The index is read from maximal determinants, and no quotient is ever formed.** For any finitely
generated `𝓞 K`-module `Λ ⊆ Kⁱ` spanning `Kⁱ`, `Submodule.covolume_mixedImage` gives
`covol Λ = (∏ᶠ_{v ∤ ∞} B v)⁻¹ covol (𝓞 K) ^ #ι` with `B v` the largest value of `v` on the
determinants of `#ι` vectors of `Λ`. Its proof takes a pseudo-basis `Λ = ⊕ J i • y i` —
`ArithmeticHeights`' `Submodule.exists_pseudoBasis`, normalized to integral ideals — computes the
covolume as `|N (det y)| ∏ N (J i)` from Mathlib's ideal lattices and one change of variables, and
reads both norms place by place. The approximation module is known only through local conditions,
and `B v` is computed from them: the ultrametric Leibniz bound applied to `L v · x` gives
`v (det L v)⁻¹ ∏ a v i` at a place of `S₀`, attained by `M⁻¹ (π k e_k)` with `v (π k) = a v k`
moved into `Λ` by one algebraic integer that is a unit at `v` and small where it has to be; off
`S₀` the maximum is `1`. No localization, no Smith normal form and no index of a quotient appears,
which is also why the class group never enters.

⚠ **The volume is one change of variables, not one per place.** `B` is the preimage of a product
of closed balls under the `mixedSpace K`-linear map whose matrix has at `w` the coefficients of
`L w` embedded by `w`; its real determinant is an algebra norm, `∏ v (det L v) ^ mult v`, by
`LinearMap.det_restrictScalars`. The book's place-by-place coordinate changes (the proof of 7.5.7)
never appear.

⚠ **Three choices of form.** The ambient is `ι → mixedSpace K`, where `normAtPlace` lives, not
`ArithmeticHeights`' euclidean `mixedPi K ι`; the geometry of numbers that 4.2 consumes is stated
for any normed space. The module is stated with `|Q|`, so that it is a submodule for every real
`Q`; it agrees with the domain for `Q ≥ 0`, where `NumberField.approxDomain_eq` is stated. And no
`DecidableEq ι` appears in any statement: the coefficients of a form are its values at
`Pi.basisFun K ι j`.

**4.2 Successive minima over `K`** (Bombieri–Gubler, Definition C.2.9, Theorem C.2.11) —
**landed**, in `…/{FieldMinima,FieldMinkowski}.lean`. For an `𝓞 K`-module `Λ` and a body `B` as
in 4.1, the `l`-th **`K`-minimum** `μ l` is the infimum of the `λ` for which `Λ ∩ λ B` contains
`l` vectors linearly independent over `K`, for `l = 1, …, n + 1`; it is
`NumberField.successiveMinimum Λ B (l - 1)`, indexed from `0` as `ZLattice.successiveMinimum`
is, and `0` above `n + 1`. The `K`-minima are attained, and vectors realizing them can be chosen
`K`-independent: one family of `n + 1` vectors of `Λ`, the `l`-th in `μ l B`
(`NumberField.exists_linearIndependent_mem_smul_successiveMinimum`). With `λ` the successive
minima of `ArithmeticHeights` 4.1 for `Λ` as a `ZLattice` of rank `d (n + 1)`,
`λ l ≤ μ l ≤ λ (d (l − 1) + 1)` (`NumberField.successiveMinimum_mixedImage_le`,
`NumberField.successiveMinimum_le_successiveMinimum_mixedImage`) — the right-hand inequality is
the extraction lemma, `ArithmeticHeights` 4.4 — and `λ (d l) ≤ c_K μ l`
(`NumberField.successiveMinimum_mixedImage_le_mul`), where `c_K` is the largest absolute value of
a conjugate of a member of a fixed integral basis `ω` of `𝓞 K` — the largest house of a member of
Mathlib's `integralBasis K`, `NumberField.integralBasisHouse K ≥ 1`: if `x 1, …, x l` are
`K`-independent in `Λ ∩ t B` then the `d l` vectors `ω j • x i` lie in `Λ`, because `Λ` is an
`𝓞 K`-module, are independent over `ℚ` and hence over `ℝ`, and lie in `c_K t B`, because `B` is
balanced over every completion (for approximation domains, `NumberField.mul_mem_approxBody`).
Deduce **Minkowski's second theorem over `K`**, two-sided:

```text
c_K^{−d(n+1)} · (2^{d(n+1)} / (d(n+1))!) · covol Λ / vol B  ≤  (μ 1 ⋯ μ (n+1))^d  ≤  2^{d(n+1)} · covol Λ / vol B,
```

from `ArithmeticHeights` 4.2 and the monotonicity of `λ` — stated multiplicatively, for any Haar
measure, as `NumberField.covolume_le_prod_successiveMinimum_pow_mul_measure` and
`NumberField.prod_successiveMinimum_pow_mul_measure_le`. This is the content of the adelic
theorem of Bombieri–Vaaler and McFeat (Bombieri–Gubler, Theorem C.2.11) in the only generality
the Subspace Theorem uses, and it is proved from the real one. With 4.1's comparison of
`vol B / covol Λ` with `Q` to the weight, for an approximation domain `(μ 1 ⋯ μ (n+1))^d` is
`Q ^ (−weight)` up to two constants depending on `K`, `S₀`, `n` and the determinants
(`NumberField.le_prod_successiveMinimum_approx`, `NumberField.prod_successiveMinimum_approx_le`);
the lower bound, which is the one 4.3 needs, uses the half of 4.1's comparison that carries no
loss.

⚠ **The lattice alone makes the `K`-minima finite, and the extraction lemma is spent twice.** That
`Λ ∩ λ B` holds `l ≤ n + 1` independent vectors for some `λ` needs `K`-independent vectors in `Λ`
at all; they come from the extraction lemma applied to the `d (n + 1)` vectors realizing the real
minima, which is the proof of `μ l ≤ λ (d (l − 1) + 1)` read qualitatively. So every statement
takes `Λ` only through `[DiscreteTopology Λ.mixedImage]` and `[IsZLattice ℝ Λ.mixedImage]`, and
none carries a hypothesis that `Λ` spans `Kⁿ⁺¹` or is finitely generated.

⚠ **Attainment needs no greedy minimality.** Cassels' Lemma 1, `ArithmeticHeights` 4.1, builds
the realizing family greedily and carries a minimality clause through the induction. Over `K`
each minimum is attained by finiteness alone — a dilate of a bounded body holds finitely many
points of `Λ`, and the body is closed — and the single family is assembled afterwards by the
selection step of the extraction lemma: `l` independent vectors realizing `μ l` contain one outside
the span of the `l − 1` already chosen.

⚠ **Only the lower bound sees the completions.** The upper bound of Minkowski's second theorem
over `K` holds for any bounded symmetric convex body with nonempty interior; `λ (d l) ≤ c_K μ l`,
and with it the lower bound, is the only statement that asks `B` to be balanced over every
completion, in the form `mul_mem_approxBody` states it. Over `ℚ` the integral basis is `± 1`, so
`c_ℚ = 1`, `d = 1`, and in one variable both bounds are equalities.

**4.3 The rank of an approximation domain** (Bombieri–Gubler, Definition 7.5.11, Lemma 7.5.12) —
**landed**, in `…/ApproximationRank.lean`. `V(Q)`, the `K`-span of the approximation domain, is
`NumberField.approxSpan S₀ L c Q`, and its **rank** `dim V(Q)` is the number of `K`-minima that
are at most `1` (`NumberField.finrank_approxSpan`); `V(Q)` is spanned by the vectors realizing
them, for any family realizing the minima (`NumberField.approxSpan_eq_span_image`). Both hold for
the points of any lattice in any closed bounded symmetric convex body, and are proved so first
(`NumberField.finrank_span_setOf_mem`, `NumberField.span_setOf_mem_eq_span_image`). If the weight
of the domain is negative then the rank is at most `n` for all sufficiently large `Q` —
`∀ᶠ Q in atTop`, `NumberField.eventually_finrank_approxSpan_lt`, and `V(Q) ≠ ⊤` in the form 6.1
consumes, `NumberField.eventually_approxSpan_ne_top` — from the lower bound of 4.2 with every
minimum replaced by the last: `μ (n+1) ^ {d (n+1)}` is at least a constant times `Q ^ (−weight)`
(`NumberField.le_successiveMinimum_approx_pow`). Also: for `Q` in `[Q₁, Q₂]` with `Q₁ > 0` the
domains all lie in one domain — of the exponents `|c|` at the level `max Q₂ Q₁⁻¹` — which holds
finitely many points of `Λ` (`NumberField.finite_approxDomain`,
`NumberField.finite_biUnion_approxDomain`), so only finitely many subspaces `V(Q)` arise from a
bounded range of `Q` (`NumberField.finite_image_approxSpan`). ⚠ `Q₁ > 0` is needed: as `Q → 0` the
bounds with negative exponent blow up.

⚠ **Lemma 7.5.12 is a statement about levels, not about solutions.** The book states
`1 ≤ rank ≤ n` along the heights `Q = H(x)` of the hypothetical infinite set of solutions of its
Lemma 7.5.9: the lower bound because each solution lies in its own domain, and "for all but
finitely many" by Northcott's theorem, which makes the heights large. Neither is a statement about
domains, and what the proof shows about domains is the parametric statement above. The rank of a
domain can be `0` — over `ℚ` with `c = −1` it is, at every level above `1` — and at the level `1`,
with the weight already negative, it is still full: the statement is eventual, not uniform.

⚠ **The rank is read from the minima through attainment, and the count is `≤ 1`.** That `μ l ≤ 1`
gives `l` independent points of the domain needs 4.2's attainment and `μ k B ⊆ B` for `μ k ≤ 1`,
which is balancedness; the converse needs nothing, since the dilation `1` is admissible. The
book's `rank = max {l | μ l ≤ 1}` and the count agree because the minima are monotone below
`n + 1`. Over `ℚ` with `c = 0` the domain is `ℤ ∩ [−1, 1]` and its one minimum is exactly `1`, so
a count of the minima below `1` would be wrong.

**4.4 Evertse's lemma** (Evertse 1996; Bombieri–Gubler, Lemma 7.5.29) — **landed**, in
`…/SIntegerApproximation.lean` and `…/EvertseLemma.lean`. Let `x 1, …, x (n+1)` be a basis of
`Kⁿ⁺¹`, and for each infinite place `v` and each `v ∈ S₀` let weights `ν v k > 0` and reals
`μ v 1 ≤ … ≤ μ v (n+1)` satisfy `v (L v k (x j)) ≤ ν v k μ v j` for all `k`, `j`. Then there are
vectors `y 1 = x 1`, `y i = x i + ∑ j < i, ξ i j • x j` with `ξ i j` in the `S₀`-integers, and
bijections `π v` between the vectors and the forms, such that
`v (L v (π v i) (y j)) ≤ C ν v (π v i) min (μ v i) (μ v j)` at the infinite places and
`≤ ν v (π v i) min (μ v i) (μ v j)` at the finite ones, `C` depending only on `K` and `n`
(`NumberField.exists_evertse`; the book's statement, `ν = 1`, is
`NumberField.exists_evertse_unweighted`). It is the step that replaces Mahler's theorem on
compound convex bodies and Davenport's lemma in Schmidt's original argument (7.5.27–7.5.28),
neither of which this roadmap builds. The proof is the book's induction, run once over any field
with a set of places that admits simultaneous approximation by a subring
(`AbsoluteValue.exists_evertse_of_approx`), with one estimate for both kinds of place: a sum of `m`
terms costs `m` at an archimedean place and `1` at a nonarchimedean one. Its arithmetic input is a
**simultaneous approximation property of `S`-integers**, proved first and stated without
completions: for every family `γ v ∈ K` indexed by the infinite places and `S₀` there is an
`S₀`-integer `ξ` with `v (ξ + γ v) ≤ 1` at each finite place of `S₀` and `v (ξ + γ v) ≤ A` at each
infinite place, `A` depending only on `K` (`NumberField.exists_forall_apply_add_le`). ⚠ Route, as
landed, with no Chinese remainder theorem: the principal part at one finite place `v₀` is
`−γ s a ∑_{i<N} p ^ i`, with `s` an algebraic integer that is a unit at `v₀` and cancels the poles
of `γ` elsewhere (4.1's prime avoidance) and `a s + p = 1` with `p` in the prime of `v₀`, so that
`1 − s a ∑_{i<N} p ^ i = p ^ N` is small at `v₀`
(`NumberField.FinitePlace.exists_apply_add_le_one`); the principal parts at the places of `S₀` are
summed; and an element of `𝓞 K` translates the sum into a fundamental domain of `𝓞 K` in `K ⊗ ℝ`,
which does not disturb the finite conditions
(`NumberField.exists_integer_forall_infinitePlace_add_le`, `A` the sum of the norms of the embedded
integral basis). With coefficients in `K`, the `γ v` of the book's (7.40) lie in `K`, which is why
the completion-free form suffices.

⚠ **The constant depends only on `K` and `n`, and it has to.** The book lets `C` depend on `K`,
`S` and the forms. Its proof gives more: the coefficients of (7.38) are at most `1` in the rescaled
sense, and the finite conditions of the approximation are met exactly, so the only constant that
enters is `A`, which is `K`'s. And 7.5.30 needs more: it applies the lemma to the forms
`Q ^ (−c v i) L v i`, which change with `Q`. So `C` is chosen before `S₀`, the forms and the
vectors.

⚠ **The forms carry weights, because over `K` they cannot be rescaled.** The forms
`Q ^ (−c v i) L v i` of 7.5.30 do not have coefficients in `K`, and at a finite place
`Q ^ (−c v i)` is in general not a value of `v`: rescaling there would lose the factor `N 𝔭` that
4.1 found in the covolume, and with it the exact finite bound of (7.43). So the lemma takes a
weight `ν v i > 0` per form — the removed form of (7.38) maximizes `v (α k) · ν v k`, the rescaled
choice without the rescaling — and 4.5 takes `ν v i = Q ^ c v i`.

⚠ **The constant at the infinite places is not `1`, even for real coefficients, and the vectors
must be sorted.** Over `ℚ` there are forms for which no real `ξ` meets the conclusion with `C = 1`:
the exact bound is a nonarchimedean privilege, and the triangle inequality in (7.38) costs a factor.
And if `μ v` is not nondecreasing no constant exists, because the first vector is never corrected.
The book's `0 < μ v j` is not needed; nonnegativity follows from the bounds.

**4.5 Exterior powers of a system of forms** (Bombieri–Gubler 7.5.2, (7.16)–(7.17), Lemma 7.5.33,
7.5.30–7.5.31) — **landed**, in `…/WedgeForm.lean` and `…/WedgeDomain.lean`. For `1 ≤ p ≤ n`: the
forms `L v I = L v (i 1) ∧ ⋯ ∧ L v (i p)`, read in the Plücker coordinates
`Set.powersetCard ι p → K` of `ArithmeticHeights` 3.1 and indexed by the `p`-subsets of `ι`
(`exteriorPower.wedgeForms`), satisfy **Laplace's identity**
`L v I (y J) = det (L v (i a) (y (j b)))` (`exteriorPower.wedgeForm_plucker`), and are linearly
independent when the `L v i` are
(`exteriorPower.linearIndependent_wedgeForms`); so are the wedges `x J` of the members of a basis
(`exteriorPower.linearIndependent_plucker_comp`). **Lemma 7.5.33**: for a basis `x` of `Kⁿ⁺¹` and
`k + p = n + 1`, the span of the wedges `x J` of the `p`-subsets `J` meeting `{0, …, k − 1}`
(`exteriorPower.wedgeSpan`) depends only on the span of `x 0, …, x (k − 1)` and determines it
(`exteriorPower.wedgeSpan_eq_wedgeSpan_iff`, and
`exteriorPower.mem_span_iff_forall_plucker_mem_wedgeSpan` for the reading back); it is the kernel of
the wedge of the last `p` coordinate forms of `x`, a hyperplane that misses the top wedge
(`exteriorPower.wedgeSpan_eq_ker`,
`exteriorPower.plucker_topBlock_notMem_wedgeSpan`, `exteriorPower.finrank_wedgeSpan_add_one`).
And **Lemma 7.5.31** in the language of 4.1–4.2, indexed from `0` as 4.2 is: for vectors `x`
realizing the `K`-minima `μ` of the domain of `L`, `c` and a level `Q > 1`, Evertse's lemma with the
weights `ν v i = Q ^ c v i` gives vectors `y` and bijections `π v` whose wedges `y J`, `J` meeting
the first `k` indices, lie in the approximation domain for the forms `L v I` with the exponents
`NumberField.wedgeExponent` — the book's `S(Q)`, with (7.44) and (7.45), and a constant depending
only on `K` and `n` (`NumberField.exists_plucker_mem_approxDomain_wedgeForms`). `Q` to the weight of
that domain is exactly `Q ^ (e w)` times `(C ^ M (∏ μ) ^ e μ (k − 1) / μ k) ^ d`, with
`e = n.choose (p − 1)` and `M` the number of `p`-subsets
(`NumberField.rpow_approxWeight_wedgeExponent`), hence at most a constant times
`(μ (k − 1) / μ k) ^ d` (`NumberField.rpow_approxWeight_wedgeExponent_le`); all of its `K`-minima
but the last are at most `1`, and the last is at least a constant times `μ k / μ (k − 1)`
(`NumberField.exists_successiveMinimum_wedge`). For a domain of rank `R`, `1 ≤ R ≤ n`, some `k` in
`[R, n]` has `(μ (k − 1) / μ k) ^ (n + 1 − R) ≤ μ n ⁻¹` (`NumberField.exists_div_pow_le_inv`, the
book's (7.41)), so the last minimum to the power `d (n + 1)(n + 1 − R)` is at least a constant times
`Q ^ (−weight)`, a positive power of `Q` for negative weight
(`NumberField.exists_successiveMinimum_wedge_pow`). What Step IX adds — the minima between
`Q ^ (−C)` and `Q ^ C`, rounding the wedge exponents to a grid, 5.6 in `⋀^p` — belongs to 6.1 and
is landed there. ⚠ 6.1 uses the *weight* of the wedge domain and not its last minimum, so of the
two conclusions of Lemma 7.5.31 only `rpow_approxWeight_wedgeExponent_le` is consumed; the
packaged `exists_successiveMinimum_wedge_pow` records the book's own form.

⚠ **The exterior power is read in coordinates, and its determinant is never computed.** 6.1 applies
4.2, 4.3 and 5.6 to domains in `⋀^p Kⁿ⁺¹`, and those live on `κ → K`, so the wedge of forms is a
form on the Plücker coordinates and Mathlib's pairing of `⋀^p M` with `⋀^p (Dual R M)` enters only
through Cauchy–Binet. The book records that the determinant of the wedges is a power of
`det (L v)` — the Sylvester–Franke theorem — but nothing uses its value: 4.1–4.3's constants may
depend on the forms and see them only through their determinants, so independence, which follows
from a biorthogonal family, is all that is needed.

⚠ **Lemma 7.5.33 needs no pairing between `⋀^{n+1−k}` and `⋀^k`.** The book identifies the span
with the annihilator of `x 1 ∧ ⋯ ∧ x k` under the perfect pairing into `⋀^{n+1}`. The dual route is
shorter: with `f` the coordinate forms of `x`, the wedges `x J` are a basis biorthogonal to the
wedges of the `f`, so the span is the kernel of the one form `f k ∧ ⋯ ∧ f n`; and `u` lies in the
span of the first `k` vectors exactly when every wedge through `u` lies in that kernel — if
`f j₀ u ≠ 0` with `j₀ ≥ k`, putting `u` in place of `x j₀` in the top block gives a wedge on which
the form is `f j₀ u`, by Cramer's rule.

⚠ **`S(Q)` is an approximation domain whose exponents move with `Q`, and the book's normalization
disappears.** The bound `C μ_I Q ^ c(π v I)` at an infinite place is written `Q ^ e` with
`e = c(π v I) + logb Q (C μ_I)` — for `Q > 1` the bound itself — so 4.2 and 4.3 apply to `S(Q)`
verbatim, with constants uniform in `Q`. The book's `μ v j = λ j ^ (ε v)` with
`∏_{v | ∞} μ v j = λ j`, (7.42), is not needed: in Mathlib's normalization a dilation multiplies
the bound at every infinite place, and `d` reappears as the exponent of Minkowski's theorem.

⚠ **(7.45) is one factor, and the weight is exact.** A subset `J` other than the top block contains
an index below `k`, so in every term of the determinant one factor is at most `μ (k − 1)` instead of
at least `μ k`; that alone is (7.45), with no ordering of `J`. And the book's chain after (7.46) is
an identity before it is an estimate: each index lies in `e` of the `p`-subsets and exactly one
wedge comes from the top block, so Minkowski's upper bound cancels everything but the jump. ⚠ The
weight of `S(Q)`, not its last minimum, is what 6.1 consumes: after rounding the exponents to a
grid, a negative weight is what makes the rank of the wedge domain eventually `M − 1`, by 4.3.

⚠ **The choice of `k` needs `R ≥ 1`, and any large jump will do.** The book takes the smallest
minimizer of `λ k / λ (k + 1)` in `[R, n]`; the proof uses only that some jump is at least the
geometric mean, which `λ R ≤ 1` (the book's indexing) makes at least `λ (n + 1) ^ (1/(n + 1 − R))`.
For rank `0` no `k` need exist.

### Layer 5: the Subspace machinery

Bombieri–Gubler's Theorem 7.5.13 — the Subspace Theorem under the extra hypothesis that the
penultimate minimum is small — by the Roth machinery of Layer 2 in multihomogeneous form.
Coefficients in `K` throughout, as in Layer 4.

**5.1 Reductions** (Bombieri–Gubler, Theorem 7.2.6, Lemma 7.5.4, Corollary 7.5.5, 7.5.6) —
**landed**, in `DiophantineApproximation/UnitNormalization.lean` and
`DiophantineApproximation/SubspaceReduction.lean`. *Projective to affine:* by 0.3, after enlarging
`S₀` every nonzero point has a **primitive** multiple — one whose local sup norms are `1` at every
finite place outside `S₀` — (`NumberField.exists_finset_superset_forall_exists_iSup_eq_one`), and
the height of a primitive point is the product of its local sup norms over the infinite places and
`S₀` (`NumberField.mulHeight_eq_prod_of_forall_iSup_eq_one`). *Unit normalization* (Lemma 7.5.4):
a primitive `x` has an `S₀`-unit multiple `u • x` whose **affine** height (`ArithmeticHeights` 0.5)
exceeds the projective height of `x` by at most a constant depending only on `K` and `S₀`
(`NumberField.exists_forall_logHeightAff_smul_le`), because the `S₀`-logarithmic image of the
`S₀`-units is a full lattice in the trace-zero hyperplane (`ArithmeticHeights` 6.5) —
`NumberField.SUnit.exists_forall_abs_log_sub_le`. Consequently (Corollary 7.5.5) the value of every
form at the normalized point has height `h(x) + O(1)`
(`NumberField.exists_forall_logHeight₁_apply_smul_le`), so by 0.4 at one place each
`log (v (L v i (u • x)))` is `O(h(x))`, the book's (7.19) —
`NumberField.InfinitePlace.abs_mult_mul_log_le_logHeight₁`. *Classes* (7.5.6): every solution of
the inequality of 6.2 with no `L v i x = 0`, so normalized, lies in
`approxDomain S₀ L c (mulHeight x)` for one of finitely many exponent systems `c` on a grid of
mesh `1/N`, each of weight at most `−ε/2` —
`NumberField.exists_finset_forall_exists_smul_mem_approxDomain`. The three together, with the
enlargement of the places and the coordinate forms at the added ones, are
`NumberField.exists_forall_approxProd_le_imp`, which is what 6.2 consumes.

⚠ **The unit normalization is balanced, and its constant does not depend on `n`.** The book picks
one nonzero coordinate `x 0` and asks the unit to make `|u x 0|_v` at least `e^(−C)` at every
`v ∈ S`; the target of the lattice approximation here is the trace-zero vector
`(mult v / D) h(x) − mult v log |x|_v`, with `D` the number of places of `S` counted with
multiplicity, so every place is handled at once, no coordinate and no distinguished infinite place
is chosen, and summing the positive parts gives `h_aff(u x) ≤ h(x) + R |S|` with no case
distinction. The constant is quantified **before** the index type, which is the book's "depending
only on `S` and `K`". ⚠ Without the unit the lemma is false for every constant: over `ℚ` with
`S₀` the `2`-adic place the one-point tuples `(2 ^ k)` are primitive, of projective height `1` and
affine height `2 ^ k`.

⚠ **Corollary 7.5.5 needs no independence of the forms.** The book compares `h_aff(L v (x))` with
`h_aff(x)` in both directions, which is where the independence of `L v` enters; only the upper
bound is needed, and it is the height of the single number `L v i x` against the affine height of
`x` (`ArithmeticHeights` 0.5, `Height.logHeight₁_sum_mul_le`). The two-sided bound on
`log v (L v i x)` is then the fundamental inequality of 0.4 applied at one place to that single
nonzero number, and it is sharp: at the `2`-adic place of `ℚ`, `|log |2|₂| = log H(2)`.

⚠ **The classes of 7.5.6 are cells of a cube, and reuse nothing from 3.1.** Layer 3.1's cells index
points of the unit **simplex**, because in Roth's theorem every local factor is at most `1`; the
exponents `log v (L v i y) / log H(x)` of 7.5.6 have both signs and are merely bounded, by
Corollary 7.5.5, so the classes are the cells of edge `1/N` of the cube `[−2, 2]`, as the book says
in 7.5.6 itself, and their finiteness is that of a set of functions supported on finitely many
places with values in a finite grid. The book's pigeonhole along an infinite sequence of solutions
is not needed either: the statement proved is parametric in the solution, as 4.3's was.

⚠ **A level `Q₀` is part of the statement, and the kernels are not avoided.** The weight of the
class is `log (approxProd y · H(x) ^ n) / log H(x) + n D / N ≤ −ε + ε/2`, and the exponents lie in
`[−2, 2]`, only once `log H(x)` exceeds the constant of Corollary 7.5.5; the solutions of small
height are 6.2's business, and — as 6.2 found — they are *not* finite in number, only finite in
number projectively, so what 6.2 adds for them is a line and not a point. A point on the kernel of some
`L v i` meets that condition of a domain at **every** exponent, so it could be given a very
negative one, but nothing then bounds the other exponents — `approxProd` vanishes and says nothing
— and, as in the book, those points are left to 6.2, which puts them in the kernels.

⚠ **The enlargement of `S₀` and the missing infinite places carry the coordinate forms.** Their
local factor `∏ᵢ |x i|_v / |x|_v` is at most `1`, so the inequality of 6.2 survives both
enlargements (`NumberField.approxProd_le_approxProd_of_subset`,
`NumberField.prod_proj_div_iSup_le_one`), and they are linearly independent, which is what 4.1's
domains and 6.1 need at every infinite place. This is the one place where an infinite place and a
finite place have to be told apart as absolute values.

⚠ **Three acceptance tests.** The unit is load-bearing (the `(2 ^ k)` above); the height identity
is load-bearing (over `ℚ` with `S₀ = ∅` the point `(2, 2)` has height `1` and sup-norm product `2`,
because it is not primitive at `2`); and the bound (7.19) is sharp.

**5.2 The multihomogeneous auxiliary polynomial** (Bombieri–Gubler 7.5.14, Lemma 7.5.15) —
**landed**, in `DiophantineApproximation/MultiHomogeneous.lean`,
`DiophantineApproximation/MonomialDeviation.lean` and
`DiophantineApproximation/SubspaceAuxiliary.lean`. For `m` blocks of variables `X h : ι → K` and a
multidegree `d : κ → ℕ`, the multihomogeneous polynomials of multidegree `d`
(`MvPolynomial.IsMultiHomogeneous`), whose monomials are `MvPolynomial.multiMons d`, a product
over the blocks of the monomials of one degree (`MvPolynomial.card_multiMons`), so of dimension
`∏ h, (d h + n).choose n`; the change of coordinates `X (h, j) ↦ ∑ i, A j i • X (h, i)`
(`MvPolynomial.blockSubst`), under which the expansion coefficients `a(L v; J; I)` of 7.5.14 are
the coefficients of `blockSubst (A v)⁻¹ (hasseDeriv I P)`; and the lemma
(`MvPolynomial.exists_ne_zero_isMultiHomogeneous_forall_coeff_blockSubst_hasseDeriv_eq_zero`):
for `0 < η` and `4 log (2 (n+1) |S|) < (n+1)(n+2) η² m` there are constants `C₂`, `C₃` and a
degree threshold `D₀` such that for every `d` with `D₀ ≤ d h` for all `h` there is a nonzero `P`
of multidegree `d` with `h(P) ≤ C₂ ∑ d h`, `h(a(L v; ·; I)) ≤ C₃ ∑ d h`, and `a(L v; J; I) = 0`
for every `v` whenever `∑ h, (∑ i, I h i) / d h ≤ m η` and some `i` has `∑ h, J h i / d h`
outside `(m/(n+1) − 2 m η, m/(n+1) + 2 n m η)`. Route: `ArithmeticHeights` 5.5 — Siegel's lemma in
height form — applied to the matrix whose rows are the conditions and whose columns are
`multiMons d`, with the counting of the omitted monomials supplied by a Chernoff bound over the
blocks. With coefficients in `K` the book's `r = [F : K]` is `1` and its relative Siegel lemma is
the absolute one.

⚠ **The book's volume computation is avoidable, and so is most of its "sufficiently large `d`".**
Bombieri–Gubler estimate the number of monomials whose exponent of one variable is small by the
volume of a region and then majorize the characteristic function by an exponential, truncating a
MacLaurin series, which forces `0 < λ ≤ n + 4`. The exponential moment is *exact* on the lattice:
the uniform distribution on the monomials of degree `N` in `n + 1` variables has `E[j i] = N/(n+1)`
and `E[binom (j i) 2] = N(N−1)/((n+1)(n+2))` — two binomial identities, proved here from an
upper-index Vandermonde convolution — and `exp (−t) ≤ 1 − t + t²/2`, valid for every `t ≥ 0`,
turns them into the book's bound with one explicit error term `λ²/(2N(n+1))`. The restriction on
`λ` disappears and `d` has to be large only to make that term small. `1 ≤ n` is load-bearing in the
moment identity: the convolution splits off the variable `i` and counts the remaining `n`, which
is the wrong thing at `n = 0`.

⚠ **The chain rule is the whole content of the vanishing statement.** The coefficient
`a(L v; J; I)` is *not* `binom (J + I) I · a(L v; J + I; 0)`: the book differentiates in the
original coordinates and expands in the transformed ones, so a coefficient of `∂_I P` is a
combination, over all orders with the same block degrees, of coefficients of `P` read in the
transformed coordinates. `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero` proves exactly what is
needed by induction on the order and never names the combination. It needs **characteristic
zero**, because `hasseDeriv_comp` produces a positive integer factor that has to be inverted.

⚠ **The conditions imposed are at order `0` only.** For each `v`, each coordinate `i` and each
monomial `N` of multidegree `d` with `∑ h, N (h, i) / d h ≤ m/(n+1) − m η`, the condition is
`(blockSubst (A v)⁻¹ P).coeff N = 0`. That this gives the vanishing at every small order `I` and
every `J` below `m/(n+1) − 2 m η` is where the factor `2` in the book's `2 m η` is spent:
`N = J + I'` moves the threshold by at most `m η`.

⚠ **The upper half of the book's interval is free.** A Hasse derivative of a multihomogeneous
polynomial is multihomogeneous of multidegree `d h − ∑ i, I (h, i)`
(`MvPolynomial.IsMultiHomogeneous.hasseDeriv`), so a nonzero coefficient has
`∑ i, ∑ h, J (h, i) / d h = m − ∑ h, (∑ i, I (h, i)) / d h`. If one exponent exceeds
`m/(n+1) + 2 n m η`, the remaining `n` average below `m/(n+1) − 2 m η`, and the lower half applies
to one of those. This is the second place `n ≥ 1` is load-bearing.

⚠ **The hypothesis on `m` is strict here.** The book's `m ≥ 4 log (2 (n+1) |S|) / ((n+1)(n+2) η²)`
leaves no room for the error term of the Chernoff bound, which is positive for every `d`; the
strict inequality creates a positive slack and `D₀` is chosen against it. Replacing `2 (n+1) |S|`
by `4 (n+1) |S|` and keeping `≥` would do the same. ⚠ **And `η ≤ 2/(n+1)` is not needed**: the
book uses it only to keep its interval inside `[0, m]`, and nothing in the proof does.

⚠ **`C₂` and `C₃` depend on `m`, `S` and `η` here.** The book claims they depend only on `K` and
the forms. That is true — the `m`-dependence is the `O(log d)` term `log #multiMons d`, which
could be absorbed into `D₀` — but Layer 5.6 fixes `m` before it uses `C₂`, so nothing downstream
needs the stronger form and the crude bound `log #multiMons d ≤ #ι · ∑ h, d h` keeps the height
estimate linear.

⚠ **Mathlib's finiteness of the nonarchimedean local factors is private.** `Height.mulHeight` is a
`finprod` over the nonarchimedean absolute values, and that the local factors of a nonzero tuple
differ from `1` at only finitely many of them is a `private lemma` there. It is reproved as
`Height.hasFiniteMulSupport_iSup`; `fun_prop` cannot be used for it across the module boundary,
because it would have to name the private lemma. ⚠ And only the `≤` direction of the height
transport is available: `Finsupp.mulHeight_le_of_forall_iSup_le` needs *equality* at the
nonarchimedean places, so the archimedean product and the nonarchimedean `finprod` are compared
separately (`Height.mulHeight_le_pow_mul_mul_pow`).

**5.3 The index along linear forms and the generalized Roth lemma** (Bombieri–Gubler, Definition
7.5.17, 7.5.18, Lemma 7.5.19) — **landed**, in `DiophantineApproximation/FormIndex.lean`,
`DiophantineApproximation/FormSpecialization.lean` and
`DiophantineApproximation/GeneralizedRothLemma.lean`. For nonzero linear forms `M h` in the
`h`-th block, the ideal `I(t; d; M)` generated by the products `∏ h, (M h (X h)) ^ (j h)` with
`∑ h, j h / d h ≥ t` (`MvPolynomial.formIdeal`), and
`ind(P; d; M) = sup {t | P ∈ I(t; d; M)}` (`MvPolynomial.formIndex`), with the valuation
properties of 2.3 (`MvPolynomial.formIndex_eq_top_iff`, `MvPolynomial.le_formIndex_add`,
`MvPolynomial.formIndex_mul`) and agreement with 2.3 for `n = 1`, `M h = X h 1 − α h X h 0`
(`MvPolynomial.formIndex_eq_index_deHom`). Then
(`MvPolynomial.formIndex_le_of_degree_ratio`): if `P` is multihomogeneous and nonzero of
multidegree at most `d`, `0 < σ ≤ 1/2`, `d (h+1)/d h ≤ σ`, and
`n σ⁻¹ (h(P) + 4 m d 0) ≤ d h · h(M h)` for all `h`, then
`ind(P; d; M) ≤ 2 m σ ^ ((1/2)^(m−1))`. Route: specialize all but two variables of each block to
`0` without killing `P` (`MvPolynomial.exists_elimination`), losing at most the factor `n` in
`h(M h)` (`Height.exists_logHeight_le_mul_logHeight₁_div`), dehomogenize
(`MvPolynomial.deHom`), and apply 2.7.

⚠ **The index along the forms is a weighted order, and the ideal is mentioned twice.** Choosing
in each block a coordinate `i₀ h` at which `M h` does not vanish and solving `M h = X (h, i₀ h)`
for that one variable (`MvPolynomial.substForm`, `MvPolynomial.substFormInv`) turns `I(t; d; M)`
into a **monomial** ideal, and membership in a monomial ideal is a condition on each monomial
separately. So the index along the forms is the weighted order of 2.3 in the transformed
coordinates, for the weights that see only the coordinates `i₀ h`, and every property of it is a
property of that order. A weight of `0` on the other variables is what makes this work: 2.3's
weighted order allows one and makes the variable invisible to the order rather than infinite.
The ideal stays in the *definition* because it is the book's, and because it is what makes the
index visibly independent of the choice of `i₀`.

⚠ **The change of coordinates is a row replacement, not a matrix.** 5.2's `blockSubst` applies
one matrix to every block, which is what the Subspace Theorem's forms need; here the forms
differ from block to block and only one row of each block is touched. Written directly as
substitutions, `substForm` and `substFormInv` are mutually inverse in four lines on the
generators — no family of matrices, no determinant and no matrix inverse.

⚠ **The variables have to be specialized one at a time, and the forms truncated with them.**
Dividing out the largest power of one variable and setting it to `0` is, on coefficients, a
single shift — Mathlib's `MvPolynomial.divMonomial` followed by `MvPolynomial.modMonomial` —
so the result has a *subfamily* of the coefficients of `P` and its height cannot go up. Taking
the componentwise minimum of the exponents and slicing once instead does not work: `X 1 + X 2`
has no monomial in which both exponents are minimal, and that slice is `0`. The composite of the
steps *is* a single slice, at an exponent no direct formula produces. And setting a variable to
zero commutes with the change of coordinates only after the coefficient of the form at that
variable has been set to zero as well (`MvPolynomial.evalZeroAt_substFormInv`); going through
the untruncated forms gives the inequality in the wrong direction.

⚠ **Only half of the book's specialization claim is proved, and it is the half that is needed.**
Bombieri–Gubler assert that the specialization leaves the index unchanged, which is true and
needs the uniqueness of the decomposition of a polynomial in powers of the forms. What Lemma
7.5.19 consumes is that the index does not *decrease*, and that needs nothing beyond the
monomial-by-monomial description of the ideal.

⚠ **"Partial degrees at most `d`" has to be read as multihomogeneity of multidegree at most
`d`.** The dehomogenization `X (h, i₀ h) ↦ X h`, `X (h, i₁ h) ↦ 1` is injective on monomials
only because the multidegree determines the second exponent from the first; without it the
height could drop by cancellation and the index could jump. In one block with variables `x₀`,
`x₁` and the form `M = x₁`, the polynomial `x₁ + x₀² − x₀` is not divisible by `M`, so its index
along `M` is `0`, while its dehomogenization at `x₀ = 1` is `t`, whose index at `0` is `1`.

⚠ **The second kept coordinate need not be one where the form survives.** The book arranges
`b_{j1} ≠ 0` so as to have a genuine point `ξ j = −b_{j0}/b_{j1}`; here the point is
`−M h (i₁ h)` whatever that is, and the hypothesis on the heights passes to 2.7 verbatim. The
case `M h (i₁ h) = 0` cannot occur under that hypothesis — it would force `h(M h) = 0` against
`h(P) + 4 m d 0 > 0` — but the proof never has to know it.

⚠ **The factor `n` in `h(M̃ h) ≥ h(M h)/n` is the multiplication table.** After normalizing one
nonvanishing coordinate to `1` (`MvPolynomial.formIndex_smul` says the index does not see the
normalization, and the projective height of a form does not either), each local factor of the
tuple is a maximum of numbers one of which is `1`, hence at most the product of the `n` local
factors of the pairs; and the product of the heights of the pairs is the height of the tuple of
all products of subsets, which is Mathlib's `Height.mulHeight_fun_prod_eq`. The tuple of ratios
is a re-indexing of that table, so `Height.mulHeight_comp_le` finishes and no local inequality
is transported by hand. ⚠ `n ≥ 1` is load-bearing and is used exactly once, as the nonemptiness
of the set of coordinates other than `i₀ h`.

**5.4 The height of `V(Q)` and the exceptional subspaces** (Bombieri–Gubler, Lemma 7.5.21) —
**landed**, in `DiophantineApproximation/LinearFormValue.lean`,
`DiophantineApproximation/SubspaceNormal.lean`,
`DiophantineApproximation/SubspaceHeightBounds.lean` and
`DiophantineApproximation/ExceptionalSubspace.lean`. For the domains of 4.1 with `c` of weight at
most `−ε/2` there are a **finite set** `𝒲` of subspaces of `Kⁿ⁺¹`, depending only on the forms
and on `S`, and constants `C₄`, `C₅`, `C₆` depending only on `K`, `S₀`, the forms and `c` and
**not on `Q`**, such that for every `Q ≥ 1` with `log Q ≥ C₄ ε⁻¹` at which the domain has rank
`n`, either `V(Q) ∈ 𝒲` or

```text
ε log Q / (4 |S|) − C₅  ≤  h(V(Q))  ≤  n (∑_{v ∈ S} d_v c_max(v)) log Q + C₆ ,
```

where `h(V(Q))` is the height of a subspace of `ArithmeticHeights` 3.2 and `|S|` counts the
places of `S` **without** multiplicity — `NumberField.exists_finite_forall_logHeight_approxSpan`.
The dichotomy is on the **pattern** of `V(Q)`: at each place of `S` the set `I v` of indices `i`
for which the wedge of the forms `L v i'`, `i' ≠ i`, does not vanish at the Plücker point of a
basis of `V(Q)` drawn from the domain; `k v` is the index of `I v` with the largest exponent, and
the two branches are `∑_{v ∈ S} d_v c v (k v) ≥ −ε/4` or `< −ε/4`
(`NumberField.weightAt`, `NumberField.cMax`).

*Liouville for the value of a linear form* (`…/LinearFormValue.lean`): for tuples `a`, `z` with
`∑ s, a s * z s ≠ 0`, at every place
`(⨆ |a s|_v)(⨆ |z s|_v) ≤ #ρ^{[K:ℚ]} H(a) H(z) |∑ a s z s|_v`
(`NumberField.InfinitePlace.iSup_mul_iSup_pow_mult_le`,
`NumberField.FinitePlace.iSup_mul_iSup_le`), proved by dividing the tuple by the value — which
leaves the height unchanged, and *that* invariance is the product formula — and reading off that
every local factor of the normalized tuple is at least `(#t)⁻¹` at an infinite place and at least
`1` at a finite one. With it: `NumberField.FinitePlace.hasFiniteMulSupport_iSup`, which Mathlib
proves only for the `nonarchAbsVal` indexing and privately, and the two comparisons
`NumberField.prod_le_finprod_of_one_le` and `NumberField.finprod_le_prod_of_le_one_outside`
between a `finprod` over the finite places and a subproduct.

*The normal vector* (`…/SubspaceNormal.lean`): a subspace of dimension `n` is the kernel of one
vector, and the Plücker coordinate of a basis at the `n`-subset omitting `i`
(`Set.powersetCard.omitOne`) vanishes exactly when the `i`-th coordinate of that vector does
(`Submodule.exists_normal`). Beside it `Submodule.exists_linearIndependent_fin`, the extraction of
a basis of a rank-`n` span from the set it is spanned by; `exteriorPower.plucker_pi_apply`, that
the Plücker coordinates of the family transformed by a system of forms are the values of the
wedges of the forms at the Plücker point — a transpose away from Laplace's identity;
`exteriorPower.wedgeFormCoeff` and `wedgeCoeff_ne_zero`; and `exteriorPower.apply_plucker_le` with its
transformed and nonarchimedean companions.

*The two bounds* (`…/SubspaceHeightBounds.lean`):
`NumberField.exists_one_le_forall_mulHeight_plucker_le` is the upper bound, through
`LinearMap.exists_inverse_forms` — an independent system of `#ι` forms is invertible — and
`NumberField.mulHeight_plucker_le_prod`, that the height of an `S`-integral tuple is at most the
product of its local factors over `S`. `NumberField.exists_pos_forall_prod_le` is the lower bound
over all of `S`, `NumberField.prod_apply_plucker_pi_le` the upper bound on the same product from
the domain. `Finset.exists_pos_forall_le` and `Finset.exists_one_le_forall_le` are the device
that makes every constant uniform over a finite family, and therefore independent of `Q`.

*The exceptional subspaces* (`…/ExceptionalSubspace.lean`): `NumberField.patternSpace`,
`NumberField.mem_span_vec_of_normal`, `NumberField.one_le_mul_rpow_weightAt` — the product formula
against the bounds at `S` — and `NumberField.exists_finite_forall_mem_of_weightAt_lt`. Two
elementary tools live there: `exists_smul_eq_of_forall_dotProduct_eq_zero`, that vectors with
nested kernels are proportional, and `NumberField.exists_smul_apply_le_one`, that every tuple has
a nonzero multiple integral at every finite place.

⚠ **The book's bound on the height of a wedge value is false as stated, and the true one is
stronger.** Bombieri–Gubler bound `h(D_{vi}) = h(L̂_{vi}(w))`, the height of a single number, by
`h(V(Q)) + C₇`. The left-hand side changes when `w` is rescaled and the right-hand side does not,
so no constant can repair it: over `ℚ` the vector `w = (N, 0)` has `h(V) = 0` and `h(w_0) = log N`.
What Step III needs is the product-formula inequality above, between the **local factor** of the
Plücker point and its **projective** height. It is also stronger than what the book extracts:
summing it over `S` costs `|S| − 1` powers of `h(V(Q))` and not `|S|`, because the local factors
of an `S`-integral tuple over the places of `S` multiply to at least its height. The statement is
recorded in the book's form because the constant is existential and `h(V(Q)) ≥ 0`.

⚠ **The counterexample is machine-checked.** `…/LinearFormValue.lean` ends with an acceptance
test over `ℚ`: the tuple `![N, 0]` has projective height `1` for every nonzero `N`, while the
value `N` of the first coordinate form has height `|N|`.

⚠ **There is one exceptional subspace per pattern, and the book's "a linear space `W`" is not
what its proof gives.** The system the book solves depends on the pattern `(I_v)`, and the
pattern moves with `Q`; its proof fixes one solution *per pattern*. There are finitely many
patterns — a function from the places of `S` to the subsets of `ι` — so finitely many exceptional
subspaces, which is all Step IV consumes. ⚠ Without the exceptional alternative the lower bound
is false.

⚠ **The exceptional system is an intersection of spans of coefficient vectors, and no star
operator appears.** Read in the original coordinates, `L̂_{vi}(w) = 0` for `i ∉ I_v` says exactly
that `w` lies in the span of the coefficient vectors of the forms `L v i` with `i ∈ I_v`. That
description is manifestly independent of `Q`, it hands the estimate its coefficients
(`w ⬝ᵥ x = ∑_{i ∈ I_v} β_i L v i (x)`, each term small because `x` is in the domain), and it needs
no Hodge star, no adjugate and no Laplace expansion of an `(n+1) × (n+1)` determinant. Nothing in
5.4 expands a cofactor.

⚠ **That the pattern of `V(Q)` is the pattern of its normal vector is `ArithmeticHeights` 3.5 at
the ranks `n` and `1`.** `Submodule.exists_normal` is Plücker duality read where the annihilator
is a line and its one Plücker coordinate is a coordinate. Applying it to the family transformed by
the forms at `v` turns "the wedge omitting `i` kills the Plücker point" into "the `i`-th
coordinate of the normal vector of the transformed subspace vanishes", and the two normal vectors
are proportional because their kernels agree — which is `exists_smul_eq_of_forall_dotProduct_eq_zero`
and not a dimension count of an annihilator.

⚠ **The chosen exceptional vector has to be scaled into the integers, and that is a scaling, not a
normalization.** Multiplying by a common denominator makes a vector integral at *every* finite
place, and only then is `|w ⬝ᵥ x|_v ≤ 1` outside `S`, which is what confines the product formula
to `S`. Scaling changes neither the kernel nor the pattern, so nothing else is re-proved; no unit
and no `S`-class group enters, unlike in 5.1.

⚠ **`n ≥ 1` is not needed.** In rank `0` the single `n`-subset is the empty one, every wedge is
the empty product `1`, the pattern is full, `k v` is the only index, the weight along `k` *is* the
weight of the exponents, and the hypothesis `weight ≤ −ε/2` puts every level in the exceptional
branch. The statement is then vacuously true there and the proof never divides by `n`.

⚠ **The constants are the book's in its absolute normalization and not in Mathlib's.** `|S|` here
counts the places of `S` without multiplicity, because the local degrees `d_v` sit inside the
local factors; correspondingly the upper bound reads `n ∑_{v ∈ S} d_v c_max(v)` where the book
reads `n c_max |S|`. What 5.6 uses is that the lower bound is a positive multiple of `ε log Q` and
that nothing depends on `Q`, and both survive the change of normalization.

**5.5 Non-vanishing at a small point** (Bombieri–Gubler, Lemmas 7.5.24 and 7.5.25) —
**landed**, in `DiophantineApproximation/PolynomialGrid.lean` and
`DiophantineApproximation/SmallPoint.lean`. *The grid lemma*
(`MvPolynomial.exists_eval_hasseDeriv_ne_zero`): a nonzero `f : MvPolynomial σ k` over a field of
characteristic zero, with `degreeOf j f ≤ e j`, and `B ≥ 1` — there are integers `z j` with
`|z j| ≤ B` and an order `i` with `B * i j ≤ e j` such that `(hasseDeriv i f)(z) ≠ 0`. *The small
point* (`MvPolynomial.exists_eval_hasseDeriv_add_ne_zero`): if `hasseDeriv I P` does not vanish
identically on the product of the spans of families `y h l` — one family per block, as many
vectors as one likes — then a further derivative `hasseDeriv (I + I') P`, with
`B * ∑ i, I' (h, i) ≤ n * d h` in every block, is nonzero at the point
`x h = ∑ l, z h l • y h l` with integers `|z h l| ≤ B`. With `B = 2 n / η` this is
Bombieri–Gubler's (7.37) — `MvPolynomial.exists_eval_hasseDeriv_ne_zero_of_sum_div_le`: a
derivative of weighted order at most `m η / 2` is replaced by one of weighted order at most `m η`
that does not vanish at an explicit point, which is the polynomial `T` of Lemma 7.5.25. Route:
one variable at a time, with the univariate case a count of roots.

Beside them: `MvPolynomial.toPolynomial`, the specialization of every variable but one, with
`MvPolynomial.natDegree_toPolynomial_le` and `MvPolynomial.eval_hasseDeriv_toPolynomial` — the
only bridge between `Polynomial.hasseDeriv` and `MvPolynomial.hasseDeriv` the induction needs;
`MvPolynomial.shift` and `MvPolynomial.coeff_shift`, the shift `X j ↦ X j + c j`, whose
coefficients are the Hasse derivatives at `c`; and `MvPolynomial.linSubst`, the block-wise linear
parametrization, with `MvPolynomial.eval_linSubst`, `MvPolynomial.shift_linSubst`,
`MvPolynomial.IsMultiHomogeneous.linSubst` and
`MvPolynomial.exists_coeff_ne_zero_of_coeff_linSubst_ne_zero`.

⚠ **The one-variable grid lemma is a count of roots, not a divisibility.** Bombieri–Gubler argue
that `f` cannot be divisible by `(∏_{|b| ≤ B} (x − b)) ^ (e/B + 1)`, whose degree exceeds `e`.
Inside an induction on the variables that argument runs over a polynomial ring in the remaining
variables, where what is known is that each factor `(x − b) ^ (e/B + 1)` divides `f` and what is
wanted is that their product does — a unique-factorization statement over that ring. Counting
roots **with multiplicity**, which
`Polynomial.roots` already carries and `Polynomial.card_roots'` bounds by the degree, needs
neither: each of the `2 B + 1` grid points is a root of multiplicity at least `e/B + 1`, and
`(2 B + 1) (e/B + 1) > e`.

⚠ **The induction on the variables never substitutes a variable.** What it carries is that the
derivative taken so far does not vanish *identically on the affine subspace* on which the
variables already handled sit at their grid values; the step specializes all the other variables,
at an arbitrary point of the field, and applies the one-variable lemma to what is left. Carrying
instead the substituted polynomial — the obvious formulation — would force a lemma commuting
`hasseDeriv` past a partial substitution, and that lemma is never needed.

⚠ **The chain rule is not needed either.** The book reads the derivative in the parameters back
through the parametrization by the chain rule, "∂_J R is a linear combination of derivatives
∂_{I'} P". What the argument consumes is only the *support* of that combination — that the orders
occurring have the block degrees of `J` — and that is multihomogeneity: the parametrization takes
a monomial of block degrees `(∑ i, μ (h, i))` to a polynomial multihomogeneous of the same
multidegree. This is the same economy as 5.2's, where the expansion coefficients `a(L v; J; I)`
were never written down.

⚠ **The bridge between the two derivatives is the shift.** `MvPolynomial.coeff_shift` turns "the
derivative of order `μ` does not vanish at `c`" into "the coefficient at `μ` of `P (X + c)` is
nonzero", and the shift commutes with the parametrization (`MvPolynomial.shift_linSubst`). The
two evaluations — one in the parameters, one in the original variables — thereby become two
coefficient extractions from the *same* polynomial, and the proof is that identity.

⚠ **Nothing in 5.5 knows about `V(Q)`, heights or places, and `n ≥ 1` is not needed.** The
hypothesis is that the derivative does not vanish identically on the product of the spans of the
*given* families, which is what `MvPolynomial.eval_linSubst` says the nonvanishing of the
parametrized polynomial means; that those spans are the `V(Q h)` and that the families lie in the
approximation domains is 5.6's business, and it is what turns `|z h l| ≤ B` into a height bound
for the point. Properties (b), (c) and (d) of Lemma 7.5.25 are 5.2's conclusions read at the new
order `I'` and are not restated. With no parameters at all the grid still has to contain a point,
which is why `B` is `⌈2 n / η⌉ ⊔ 1`; the rounding costs the book's `|z h l| ≤ 2 n / η` an additive
`1`, in a constant 5.6 does not look at.

⚠ **The hypothesis that the `x j` be algebraically independent over `k` is the hypothesis that
`f` lives in a polynomial ring**, and `B` is a natural number here where the book takes a positive
real: `B * i j ≤ e j` is `i j ≤ e j / B` without a floor, and a caller with a real bound takes its
ceiling.

**5.6 The penultimate-minimum theorem** (Bombieri–Gubler, Theorem 7.5.13, Steps IV and VI) —
**landed**, in `DiophantineApproximation/{LogComparison,FormIndexSubspace,SubspaceValueBound,
SubspaceKeyInequality,PenultimateMinimum}.lean`. For forms with coefficients in `K`, independent
at every place of `S`, and `c` of weight at most `−ε/2`, the set of subspaces
`{V(Q) | 1 ≤ Q, rank Π(Q) = n}` is finite: `NumberField.finite_setOf_approxSpan`. Beyond a
level every such `V(Q)` is one of 5.4's exceptional subspaces
(`NumberField.exists_forall_approxSpan_mem`), and the levels below contribute finitely many
spans by `NumberField.logHeight_approxSpan_le` — 5.4's upper bound restated without its
hypothesis that `Q` be large — and Northcott for subspaces (`ArithmeticHeights` 3.7).

The contradiction is `NumberField.exists_forall_not_chain`: there are `m`, `σ > 0` and `Qlow`
such that no `m + 1` levels with `log Q h ≥ Qlow`, growing at the rate `2 σ⁻¹`, can all have
rank `n` and height at least `ε log Q h / (4 |S|) − C₅`. Given such a chain, take
`d h ≈ D / log Q h` — so the multidegrees decrease at the rate `σ` — let `P` be 5.2's auxiliary
polynomial and `M h` the form cutting out `V(Q h)`, whose height 5.4 bounds below. Then 5.3 makes
the index of `P` along the `M h` at most `2 (m+1) σ^((1/2)^m) = (m+1) η / 2`;
`MvPolynomial.exists_linSubst_hasseDeriv_ne_zero_of_formIndex_le` turns that into a derivative
`∂_I P` of weighted order at most `(m+1) η / 2` not vanishing identically on `∏ V(Q h)`; 5.5
replaces it by `∂_{I'} P` of weighted order at most `(m+1) η` and a point
`X (h, i) = ∑ l, z h l · y h l i` with `y h l` in the domain and `|z h l| ≤ ⌈2 n/η + 1⌉` at which
it is nonzero. `NumberField.subspace_key_inequality` bounds that value above at every place of
`S` and below by the product formula, giving

```text
0 ≤ tw · log ((∏ (d h + 1))² (2 (n+1) n)^|d|) + h(P) + 2 |d| ∑_θ log H₁(β θ)
      + D (mean · w(c) + Δ · w(|c|)) + (∑ log Q h) · w(|c|),
```

with `mean = (m+1)/(n+1)` and `Δ = 2 n (m+1) η`; letting `D → ∞` against a fixed `m` closes it.

Beside them: `Submodule.exists_basis_subset`, a spanning set contains a `Fin n`-indexed basis;
`Submodule.logHeight_eq_logHeight_of_forall_dotProduct`, the height of a hyperplane is the height
of its normal vector (the book's (7.28)); `NumberField.formMatrix` and `NumberField.refFamily`,
the matrix of a system of forms and the family the product formula charges;
`NumberField.approxAbsWeight`, the weight of the absolute values of a system of exponents;
`MvPolynomial.zeroCoords` and `MvPolynomial.formCoordInv`, with
`MvPolynomial.substFormInv_eq_linSubst`; and the five arithmetic lemmas of
`NumberField.PenultimateMinimum`.

⚠ **The chain rule is not needed a third time.** 5.3 measures the index in the coordinates in
which the forms are the variables, and 5.5 wants a derivative in the original ones. The change of
coordinates **is** a block-wise linear substitution (`MvPolynomial.substFormInv_eq_linSubst`), so
5.5's own `MvPolynomial.shift_linSubst` and
`MvPolynomial.exists_coeff_ne_zero_of_coeff_linSubst_ne_zero` transport a surviving coefficient
between the two systems *with the same degree in every block*, which is exactly what makes the
two weighted orders agree. After 5.2 and 5.5, this is the third place where the book invokes the
chain rule and the third where only multihomogeneity is consumed.

⚠ **The transverse part of a monomial is its own derivative order.** To turn "the coefficient of
`substFormInv P` at `ν` is nonzero" into "some derivative does not vanish on the coordinate
subspace", differentiate to the order `J = ν` restricted to the transverse coordinates. The
binomial factor of `∂_J` is then a product of `choose k k` and `choose k 0`, hence `1`: no
characteristic hypothesis is needed, only that `K` be infinite, for `MvPolynomial.funext`.

⚠ **The vanishing pattern of 5.2 enters only as a two-sided bound.** Step VI consumes
`|ρ j − mean| ≤ Δ` for the exponents `ρ j = ∑_h J (h, j)/d h` of every monomial that survives in
every coordinate system; 5.2's interval `(m/(n+1) − 2 m η, m/(n+1) + 2 n m η)` is asymmetric, and
`n ≥ 1` absorbs it into `Δ = 2 n (m+1) η`. Which end is wider is the caller's business, which is
why 5.2 is not restated symmetrically.

⚠ **Two invariants of the system of exponents, not one.** Besides `approxWeight`, which is
negative, the estimate needs `approxAbsWeight = ∑_v d_v ∑_i |c v i| + ∑_{v ∈ S₀} ∑_i |c v i|`,
because the local bound at `v` is `Q^{mean ∑ c v i}` only up to `Q^{Δ ∑ |c v i|}`. It is the
quantity `η` is chosen against — `η ≤ ε / (8 (n+1)² (w(|c|) + 1))` — and it is the only place in
the development where the size of the exponents rather than their sum enters.

⚠ **`S` must contain every archimedean place, and that is where it is used.** Away from `S` the
local bound carries no constant and the point is integral, so the product formula is applied with
`Sinf = univ` (`NumberField.one_le_of_forall_apply_le`). This is the same convention as Layers 4
and 5.4, and it is what makes the reference family finite.

⚠ **The reference family is charged with exponent `2 |d|`.** The entries of the inverse matrices
`(L v)⁻¹` and the integers `z h l` of the grid are bounded by the *same* product of truncated
local factors `∏_θ max(v(β θ), 1)`, so one family `refFamily` carries both and the expansion of a
value of `∂_{I'} P` costs `H(β)^{2|d|}` rather than two separate heights.

⚠ **The heartbeat budget is per declaration, which is why the arithmetic is factored out.**
`exists_forall_not_chain` constructs a dozen parameters before it can even state 5.3's
hypothesis, and every `field_simp`, `positivity` and `linarith` on the way spends from the same
200 000 heartbeats. The five lemmas of `NumberField.PenultimateMinimum` carry every inequality
that has a division in it; inside the main proof only `linarith only` appears, on goals whose
atoms are already in normal form. Raising `maxHeartbeats` would have been the other way, and this
repository forbids `set_option` in library files.

⚠ **The milestone is stated for `1 ≤ Q`, and the bounded range is covered separately.** 5.4
states its dichotomy only for `log Q ≥ C₄/ε`, but its *upper* bound needs no such hypothesis;
restating it for every level and appealing to Northcott makes the levels below the threshold
contribute finitely many spans, which the book leaves to the reader. Layer 6.1, as landed, wants
neither: it is stated for `Q ≥ Q₀` and uses 5.6 only through the wedge domains. The large-`Q`
form, `NumberField.exists_forall_approxSpan_mem`, which names the finite set as 5.4's own `𝒲`, is
there for a consumer that wants the threshold named.

### Layer 6: the Subspace Theorem (the summit)

**6.1 The parametric Subspace Theorem** (Bombieri–Gubler 7.5.30–7.5.32, Steps VIII and IX;
Evertse–Schlickewei for the formulation) — **landed**, in
`…/{WedgeRecovery,MinimaBounds,ExponentGrid,WedgeExponentBound,ParametricSubspace}.lean`. For
forms with coefficients in `K`, linearly independent at every infinite place and at every place of
`S₀`, and exponents `c` of negative weight, there are a finite set `T` of proper subspaces of
`Kⁿ⁺¹` and a level `Q₀` such that for every `Q ≥ Q₀` the approximation domain
`approxDomain S₀ L c Q` is contained in a member of `T`
(`NumberField.exists_finset_submodule_forall_approxDomain_subset`). Route, at a level `Q` where
the domain has rank `R`, which is at most `n` for large `Q` by 4.3: for `R = 0` the domain spans
`⊥`; for `1 ≤ R ≤ n`, (7.41) chooses `k` in `[R, n]` where the jump of the minima is large, 4.4
and 4.5 move the wedges of the `p`-subsets meeting the first `k` minimal vectors, `k + p = n + 1`,
into a domain in `⋀^p Kⁿ⁺¹` whose exponents `NumberField.wedgeExponent` move with `Q`; those
exponents are rounded up to a grid of mesh `γ`, the rounded system has negative weight and is one
of finitely many, its domain has rank exactly `M − 1` because the wedges already span a
hyperplane and 4.3 caps the rank, 5.6 in `⋀^p` makes those spans finite in number, and Lemma
7.5.33 — read as the function `exteriorPower.recoverSpan` — recovers from each span the span of
the first `k` minimal vectors, which contains `V(Q)` and is proper because `k ≤ n`.
⚠ The book states its conclusion only along `Q = H(x_ν)` for a hypothetical sequence of solutions,
because it is proving 6.2 by contradiction; but 7.5.32 opens with "let `(Q_ν)` be an unbounded
family" and uses nothing else, and the statement above is what that argument proves. It is pinned
as the primary form because it is the one the quantitative theory strengthens: Layer 9 and every
quantitative Subspace Theorem in print count the members of `T`.

⚠ **No pigeonhole, no subsequence and no bounded range.** The book argues along an unbounded
family of levels and extracts a subfamily on which `k` and the rounded exponents are constant.
None of that is needed: the rounding is a **function** of the level
(`NumberField.roundExponent`), its range is finite because the exponents stay in a box, and the
finite set of subspaces is the union over that range — a union over a finite index set, not over a
subsequence. Layer 3.1's cells are not used. And because the conclusion is stated for `Q ≥ Q₀`
only, 4.3's finiteness over a bounded range of levels is not used either.

⚠ **The penultimate rank is not a separate case.** The book treats rank `n` by Theorem 7.5.13
directly and the lower ranks by the exterior power. Here rank `n` is the case `k = n`, `p = 1` of
the same construction — the wedge domain in `⋀^1 Kⁿ⁺¹` is the original domain re-indexed by the
one-element subsets, with the exponents shifted by the minima and a constant — so one mechanism
covers every rank from `1` to `n`, and 5.6 is applied only through it. This is the one place where
the formalization is visibly shorter than the book.

⚠ **The minima have to be confined between `Q^{−B}` and `Q^{B}`, and Layer 4.2 does not give
it.** Minkowski's second theorem over `K` bounds the *product* of the minima from both sides,
which bounds the first minimum from above and the last from below — the two directions that do not
confine anything. The missing bound is arithmetic, not geometry of numbers: a nonzero point of
`Λ ∩ t B` has height at least `1` by the product formula, and at most a constant times `t^d` times
`Q` to the sum of the largest exponents, so `t` is at least a fixed negative power of `Q`
(`NumberField.exists_pos_forall_rpow_le_successiveMinimum`); the upper bound is then Minkowski's,
with the others replaced by that lower bound
(`NumberField.exists_pos_forall_rpow_le_successiveMinimum_le`). Every constant is absorbed into
one extra unit of exponent above a threshold, which keeps the grid free of constants.

⚠ **The grid is indexed by the infinite places, not by absolute values.** A system of exponents is
a function on `AbsoluteValue K ℝ`, of which there are infinitely many, and a domain reads it at
the infinite places and at `S₀` only; rounding at *every* absolute value would leave infinitely
many systems. `NumberField.gridExponent` therefore carries an integer per infinite place and per
`p`-subset and selects with `∑ w, if w.1 = v then … else 0`. Nothing is rounded at the finite
places, where the exponent of the wedge domain is exact.

⚠ **`T` contains subspaces containing the spans, not the spans.** The wedge route recovers the
span of the first `k` minimal vectors, which contains `V(Q)`; whether the `V(Q)` themselves are
finite in number for `R < n` is not claimed and is not what 6.2 consumes. For `R = n` it is 5.6,
which does say so.

⚠ **Lemma 7.5.33 has to become a function.** Finiteness is transported from `⋀^p Kⁿ⁺¹` back to
`Kⁿ⁺¹` by taking an image, so the map has to be defined on subspaces and not on bases:
`exteriorPower.recoverSpan p U` is the span of the vectors all of whose wedges lie in `U`, and
`exteriorPower.recoverSpan_wedgeSpan` is Lemma 7.5.33 saying that it inverts `wedgeSpan`. It is
defined as a span rather than as a carrier because the carrier is a submodule only by
multilinearity of the Plücker coordinates, an API nothing else here wants.

**6.2 The Subspace Theorem, coefficients in `K`** (Schmidt 1972 for `K = ℚ`, `S = {∞}`;
Schlickewei 1977 with finite places; Bombieri–Gubler, Theorem 7.2.2 with `F = K`) — **landed**,
in `…/SubspaceTheorem.lean`. For `[Nontrivial ι]`, forms `L v i : Module.Dual K (ι → K)` linearly
independent for each `v` in `S∞` and `S₀`, and `ε > 0`, there is a finite set `T` of proper
subspaces of `Kⁿ⁺¹` containing every `x ≠ 0` with
`approxProd S∞ S₀ L x ≤ mulHeight x ^ (−(n+1) − ε)`
(`NumberField.exists_finset_submodule_of_approxProd_le`, with
`NumberField.exists_finset_submodule_setOf_approxProd_le_subset` the same read as an inclusion of
the solution set in a finite union of proper subspaces). From 6.1 and 5.1: an infinite place
missing from `S∞` is added with the coordinate forms, whose local factor is at most `1`, so the
hypothesis survives; the solutions with some `L v i x = 0` lie in the kernels; the others,
normalized, lie in finitely many parametric families, each covered by 6.1 once
`mulHeight x ≥ Q₀`; and the projective points of height below `Q₀` are finite in number by
Northcott (`ArithmeticHeights` 1.1) and lie on that many lines, which are proper because `n ≥ 1`.

⚠ **The route in print is the route that was formalized, and it needed nothing new.** 6.2 is the
only milestone of Layers 4, 5 and 6 whose file introduces no definition and proves no auxiliary
lemma: every ingredient — the enlargement of `S₀`, the exponent classes, the parametric theorem,
Northcott on projective space — is consumed from a layer below by name. What the book presents as
the last page of a forty-page proof really is one page.

⚠ **Northcott is a property of the projective height, so the small-height solutions are lines.**
The obvious reading of "the solutions of height below `Q₀` are finitely many, and finitely many
points lie on finitely many lines" is wrong as stated: `Height.mulHeight` is constant on a line,
so the solutions of bounded height are never finite in number. What is finite is the set of
points of `Projectivization K (ι → K)` of bounded height — this repository's
`Projectivization.finite_setOfPred_mulHeight_le` (`ArithmeticHeights` 1.1) — and each contributes
the line it spans. This is also the one step where `n ≥ 1` is used for more than bookkeeping: a
line is a proper subspace only when `n ≥ 1`, and at `n = 0` the theorem is false, the solutions
being the roots of unity of `K`, finite in number but spanning everything.

⚠ **The normalizing scalar never has to be undone.** 5.1 puts a multiple `t·x` in a domain and
6.1 puts `t·x` in a subspace; since a subspace is closed under `t⁻¹·−`, the conclusion is about
`x` although every intermediate statement is about a multiple of it. Nothing in 6.2 has to track
`t`, and in particular the exponent systems need not be made invariant under scaling.

⚠ **The two thresholds are combined by one `max` and no uniformity is needed.** 5.1 gives one
level above which every solution is classified; 6.1 gives, for each of the finitely many exponent
systems, a level above which its domains are covered, and those levels are not uniform in the
system. `Finset.exists_le` bounds finitely many reals, which is all that is wanted — a uniform
`Q₀` over the class of exponent systems is never needed and was not proved.

**6.3 Algebraic coefficients** (Bombieri–Gubler, Theorem 7.2.2 in full and Remark 7.2.3) —
**landed**, in
`…/{FormBaseChange,PlaceConjugation,ExtensionApproxProd,SubspaceAlgebraic}.lean`. The same with
`L v i : Module.Dual F (ι → F)` over a finite extension `F/K`, linearly independent over `F`,
measured by `w v` over `v`: the solutions `x ∈ Kⁿ⁺¹` lie in finitely many proper subspaces of
`Kⁿ⁺¹` (`NumberField.exists_finset_submodule_of_approxProd_le_extension`, with
`NumberField.exists_finset_submodule_setOf_approxProd_le_extension_subset` the inclusion form).
Route, exactly the book's: by 0.1 pass to the Galois closure `F'` of `F/K`; at each place `w'`
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

⚠ **The transfer is an equality, and that is the point of the conjugates.** The reason the book
conjugates the forms rather than leaving the other places above `v` empty is not bookkeeping: a
point of `Kⁿ⁺¹` is fixed by every element of `Gal(F'/K)`, so the conjugated system gives it the
*same* local factor at every place above `v`, and the local degrees there sum to `[F' : K]` —
which is the same degree by which the relative height grows. `NumberField.approxProd_conjSystem`
is therefore an identity, not an estimate, and the exponent `−n−1−ε` survives untouched. Putting
the coordinate forms at the other places, the device Layer 5.1 uses for the places it adds, would
not do: their local factor is at most `1`, which weakens the inequality in the wrong direction.

⚠ **Conjugation and base change are one operation.** A linear form on `Fⁿ⁺¹` is its vector of
coefficients, so a ring homomorphism `f : F → E` carries it: `Module.Dual.compRingHom`. The base
change to the Galois closure is `f = algebraMap`, the conjugation is `f = σ`, and a conjugated
base change is the single homomorphism `σ ∘ algebraMap`. Layer 6.3 needs no semilinear map and no
tensor product. ⚠ That linear independence survives the carrying is, however, **not** formal: it
is false for a general ring map and for a non-square family. Here the family is square, so
independence is invertibility of the coefficient matrix, and `RingHom.map_det` carries that along
any homomorphism of fields.

⚠ **Mathlib's finite places are normalized, so Layer 0.2 does not apply to them.** A finite place
of `F'` above a finite place `v` of `K` restricts to `v^{ef}` and not to `v`, so it is not an
absolute value over `v` and the orbit statement of 0.2 is not about it; its `(ef)`-th root is, and
that root exists as an absolute value only because a finite place is nonarchimedean (Layer 0.1's
`AbsoluteValue.nonarchRpow`, which is there for exactly this reason). The `ef` then cancels
against `NumberField.FinitePlace.sum_localDegree` precisely as `mult` cancels against
`NumberField.InfinitePlace.sum_mult` at the infinite places, which is why the two halves produce
the same exponent `[F' : K]` and the identity is uniform.

⚠ **The place of `K` under a place of `F'` is recovered from a relation, not from a map.** The
system of forms on `F'ⁿ⁺¹` must be a function of an *absolute value*, because that is what
`approxProd` reads; it is defined by choosing, for each absolute value, a triple (place of `K`,
place of `F'`, automorphism) with the right relation. That the place of `K` so chosen is the one
wanted is proved — both restrict the same absolute value to `K` — rather than built in. This
avoids a contraction map on finite places, which Mathlib does not have, and avoids needing that
distinct places of `K` are inequivalent, which nothing in this roadmap proves.

⚠ **Intersecting the subspaces back with `Kⁿ⁺¹` is a `comap`, and properness is the standard
basis.** `W ∩ Kⁿ⁺¹` is `(W.restrictScalars K).comap φ` for the `K`-linear `φ : Kⁿ⁺¹ → F'ⁿ⁺¹`; if
that is everything then `W` contains every `e_j`, which span `F'ⁿ⁺¹` over `F'`, so `W = ⊤`. The
degree plays no part in this step, and neither does `n ≥ 1`.

**6.4 The affine form** (Bombieri–Gubler, Corollary 7.2.5 and Theorem 7.2.6) — **landed**, in
`…/{AffineProd,SubspaceAffine}.lean`. For `S : Finset (HeightOneSpectrum (𝓞 K))`, forms as in 6.3
at every infinite place and every place of `S`, and `ε > 0`: the `x ≠ 0` with coordinates in
`S.integer K` and

```text
(∏ v : InfinitePlace K, (∏ i, w v (L v i x)) ^ v.mult) * ∏ v ∈ S, ∏ i, w v (L v i x)  ≤  mulHeight x ^ (−ε)
```

lie in finitely many proper subspaces of `Kⁿ⁺¹`
(`NumberField.exists_finset_submodule_of_integer_of_affineProd_le`, with
`NumberField.exists_finset_submodule_setOf_integer_of_affineProd_le_subset` the inclusion form).
The left-hand side is `NumberField.affineProd S w L x`, the affine quantity. **This is the form
every application in Layer 8 uses**, and the equivalence with 6.3 is proved in both directions:
forwards by `NumberField.approxProd_le_of_affineProd_le`, after which the milestone is four lines
on 6.3; backwards by `NumberField.exists_finset_forall_exists_smul_affineProd_le`, which produces
the enlarged data the affine form asks for and the scaling that makes a solution `S`-integral, and
which with the milestone recovers 6.3.

⚠ **The layer is one identity and no estimate.** The affine quantity drops the `n + 1` local
denominators `‖x‖_v` of `approxProd`; their product over the infinite places and `S` is exactly
the part of the height those places carry, so
`affineProd = approxProd · (that part)^{n+1}` (`NumberField.affineProd_eq_approxProd_mul`) and
the exponent `−ε` of Corollary 7.2.5 does the work of the `−n−1−ε` of Theorem 7.2.2. The `n + 1`
is the number of *forms*, not a dimension count: each local factor divides by `‖x‖_v` once per
form. Nothing anywhere in the passage is estimated.

⚠ **`S`-integrality suffices forwards and does not suffice backwards.** At an `S`-integral point
the `S`-part of the height can *exceed* the height — the factor lost at a place of `S` that the
coordinates do not fill — so the affine inequality is the **stronger** of the two, which is the
direction the milestone needs, and 0.3's inequality `H(x) ≤ Hs(x)` is all it uses. The converse
has to normalise to an `S`-**primitive** point, where 0.3 makes the two equal. That asymmetry is
why Bombieri–Gubler state Corollary 7.2.5 for `S`-integers and Theorem 7.2.6 for primitive points,
and it is the whole difference between the two statements.

⚠ **The converse enlarges three things at once, one per layer below it.** Every infinite place
must be present and every finite place outside `S` harmless, which is 5.1's coordinate forms,
whose local factor is at most `1` (`NumberField.prod_proj_div_iSup_le_one`, reused verbatim);
`S` must be large enough for a primitive multiple to exist, which is 0.3's localisation; and `w`
must be defined and lie over `v` at the added places, which is 0.1's fibre. The third is why the
converse returns a **new** family `w'` and does not reuse `w`: the affine statement asks for an
absolute value of `F` at *every* infinite place, and the projective one only on `S∞`.

⚠ **Scaling is invisible to both statements and not to the passage between them.** The projective
inequality and the subspaces are invariant under `x ↦ c·x`; the affine inequality is not, and a
point satisfies it only after being scaled to be primitive. So the converse hands back the
multiple, and the subspace it lands in is the subspace of the original point — the same
observation that made 6.2's normalizing scalar free.

⚠ **The two statements do not index their finite places by the same object.** The affine form
indexes them by height-one primes of `𝓞 K`, because that is Mathlib's carrier for `S`-integers
and `S`-units and therefore what Layer 8 will hold; the projective form indexes them by
`NumberField.FinitePlace`. The translation is `FinitePlace.mk`, and its injectivity is a small
Mathlib gap — Mathlib has `FinitePlace.maximalIdeal_injective`, the other direction of the same
equivalence — filled here as `NumberField.FinitePlace.mk_injective`.

**6.5 General position** (Vojta 1987; Bombieri–Gubler, Definition 7.2.8, Theorem 7.2.9) —
**landed**, in `DiophantineApproximation/GeneralPosition.lean` and
`DiophantineApproximation/SubspaceGeneralPosition.lean`. A family of linear forms is in **general
position** if every subfamily of at most `n + 1` of them is linearly independent
(`Module.Dual.IsGeneralPosition`). For families in general position, **of any finite sizes**, the
conclusion of 6.3 holds for the product over the whole family:

```text
(∏ v ∈ S∞, (∏ k ∈ B v, w v (L v k x) / ‖x‖_v) ^ v.mult) * ∏ v ∈ S₀, ∏ k ∈ B v, w v (L v k x) / ‖x‖_v
      ≤  mulHeight x ^ (−n−1−ε)
```

(`NumberField.exists_finset_submodule_of_generalProd_le`, with
`NumberField.exists_finset_submodule_setOf_generalProd_le_subset` the inclusion form). The
left-hand side is `NumberField.generalProd Sinf Sfin w B L x`.

⚠ **The layer is one local observation and one partition, and no new arithmetic.** At a place
where the forms are in general position, keep the `n + 1` *smallest* values `w v (L v k x)`:
general position makes the forms that produce them a basis, a basis bounds `⨆ j, v (x j)` from
above by the largest of those values, and so every *discarded* value is bounded **below** by
`‖x‖_v` over a constant. Dropping them therefore costs a constant, the chosen system is one of
finitely many, and 6.3 finishes — which is Bombieri–Gubler's proof, executed.

⚠ **The families of fewer than `n + 1` forms are the opposite case, and the two cannot be
merged.** There the family is linearly independent outright and is *completed* to a basis by
coordinate forms, whose local factors are at most `1`, so the completion costs nothing at all.
One cannot simply extend every family by the coordinate forms and select the smallest of the
extended family: the extension need not be in general position — one of the given forms may
already be a coordinate form — and the `n + 1` smallest of it need not be independent. So the
large case is the ordering argument and the small case is Steinitz, and neither covers the other.
`Module.Dual.exists_index_extendProj` is the Steinitz step, on Mathlib's `Basis.extendLe`.

⚠ **The number of forms varies by a `Finset`, not by a family of types.** The signature is
`L : AbsoluteValue K ℝ → κ → Module.Dual F (ι → F)` together with
`B : AbsoluteValue K ℝ → Finset κ`, one carrier type `κ` for all places and a finset per place for
which of its members are used. A family of index *types* `κ v` would be the book's phrasing, but
the chosen system at a place is an index map `ι → κ ⊕ ι` and those have to form **one** finite
type for the partition into classes to be finite. Nothing is lost — take `κ` large enough — and
`[Finite κ]` is required for this reason and no other.

⚠ **The constant is removed by halving `ε`, so Northcott reappears.** 6.3 is applied with `ε / 2`
and only above a height threshold; below it the solutions are finite in projective space and are
collected as the lines they span, exactly as in 6.2. That is the second and last appearance of
Northcott in the Subspace Theorem, and both are for the same reason: a constant in front of
`H(x)^{−n−1−ε}`.

⚠ **6.3 comes back out of 6.5, so the two are equivalent.** With `n + 1` forms at every place,
general position *is* linear independence (`Module.Dual.IsGeneralPosition.of_linearIndependent`)
and the two central quantities are literally the same product —
`NumberField.generalProd_univ_eq_approxProd` is `rfl`. So Vojta's refinement contains the theorem
it is proved from, and the library carries one Subspace Theorem here too.

**6.6 Consistency with Layer 3** — **landed**, in
`DiophantineApproximation/SubspaceConsistency.lean`. For `Fintype.card ι = 2`, 6.3 is 3.4 — not
"has the same content as" but *is*: the two conclusions are the same proposition, and the library
says so with `rfl`.

```text
@NumberField.exists_finset_submodule_of_approxProd_le_card_two
  = @NumberField.exists_finset_submodule_of_approxProd_le_card_two_of_extension  := rfl
```

`NumberField.exists_finset_submodule_of_approxProd_le_card_two_of_extension` is 3.4's statement
proved from 6.3 and
`NumberField.exists_finset_submodule_of_approxProd_le_card_two_of_generalPosition` is 3.4's
statement proved from 6.5; `NumberField.finite_setOf_approxProd_le_card_two` is the projective
reading — finitely many **points of `ℙ¹(K)`** — resting on
`Projectivization.subsingleton_setOf_rep_mem`, that a proper subspace of a plane holds at most one
point; and `NumberField.finite_setOf_prod_min_one_le_of_extension` is Roth's theorem of 3.2
recovered from 6.3.

⚠ **The converse needs nothing, and that is the milestone.** "6.3 at `card ι = 2` is no stronger
than 3.4" is not an implication to be proved. 3.4 was stated for an arbitrary index type with
`Fintype.card ι = 2` and with `approxProd`, the very quantity 6.3 uses, so the only difference
between the two statements is that 6.3 asks for `[Nontrivial ι]` where 3.4 asks for
`Fintype.card ι = 2` — and the second implies the first. The discharge of one equation is the
whole of the specialization, exactly as this section predicted, and the agreement is therefore an
equality of *statements*.

⚠ **`rfl` between two theorems is a real check, because proof irrelevance is definitional.** Two
proofs of one proposition are one term, so `@A = @B` for theorem constants `A` and `B` holds
exactly when they prove the same thing. The file uses it four times: 3.4 against 6.3, 6.5 against
6.3, and the two other proofs of Roth's theorem against the new one.

⚠ **Roth's theorem comes back out of Layer 6, and the library now carries three proofs of one
theorem.** 3.4's converse implication — `NumberField.finite_setOf_prod_min_one_le_of_subspace`,
which takes the Subspace Theorem as a hypothesis — uses nothing of Layer 3 besides Northcott, so
discharging it from 6.3 instead of from 3.3 is a second proof of Roth's theorem over a number
field. 3.2's own theorem, 3.4's roundtrip and this one are `rfl`-equal. ⚠ The independence is a
statement about the *proofs* and not about the imports: `SubspaceAlgebraic.lean` reaches
`RothTheorem.lean` through `ApproxProd.lean`, where the central quantity is defined, and the
module graph does not record it.

⚠ **On the projective line the theorem counts points, and it cannot count tuples.** For
`card ι = 2` a proper subspace of `K²` is a line and holds one point of `ℙ¹`, so the finitely many
exceptional subspaces pin finitely many solutions. The count cannot be moved down to tuples: both
sides of the inequality are invariant under scaling, so one solution has infinitely many nonzero
multiples, and the file records that as a rejection test.

⚠ **6.5 specializes exactly as 6.3 does.** General position for two forms in two variables is
linear independence, and `NumberField.generalProd` over `Finset.univ` is `approxProd` by `rfl`, so
Vojta's refinement also lands on 3.4 through the same one equation. Both of Layer 6's Subspace
Theorems contain Roth's theorem on the projective line.

### Layer 7: approximation of algebraic numbers, and transcendence

What the Subspace Theorem says about numbers. Every milestone is 6.3 over `K = ℚ` with an
algebraic coefficient, followed by an induction on the dimension that uses the finitely many
subspaces. ⚠ **Layer 7 is complete**: 7.1 is that pattern executed once, 7.2
consumes it and appeals to Layer 6 nowhere, 7.3 consumes both and returns to Layer 6 once, for a
second system of forms, 7.4 returns to Layer 6 a third time, for the finite places — and
needs no induction on the dimension at all: one subspace decides — and 7.5 is 7.4 behind a
pigeonhole.

**7.1 One linear form** (Bombieri–Gubler, Theorem 7.3.2) — **landed**, in
`DiophantineApproximation/LinearFormSubspaces.lean` and
`DiophantineApproximation/OneLinearForm.lean`. For complex algebraic `α 0, …, α n` and `ε > 0`,
finitely many `x ∈ ℤⁿ⁺¹` satisfy
`0 < ‖∑ i, α i * x i‖ ≤ mulHeight x ^ (−n − ε)`. The hypothesis is non-vanishing, not linear
independence of the `α i` (Remark 7.3.3), and the statement kept that shape.

```text
Complex.finite_setOf_norm_sum_mul_le_fin :
  (∀ i, IsAlgebraic ℚ (α i)) → 0 < ε →
    {x : Fin (n + 1) → ℤ | 0 < ‖∑ i, α i * x i‖ ∧
      ‖∑ i, α i * x i‖ ≤ mulHeight (fun i ↦ (x i : ℚ)) ^ (-(n : ℝ) - ε)}.Finite
```

`Complex.finite_setOf_norm_sum_mul_le` is the same for an arbitrary finite index type, with the
exponent `-(#ι - 1) - ε`, which is the form the induction proves;
`Complex.exists_finset_submodule_of_norm_sum_le` is the Subspace Theorem step, and
`Rat.exists_finset_submodule_of_sumForm_le` is that step with the coefficients in a named number
field carrying an absolute value over the infinite place of `ℚ`.

⚠ **The hypothesis is `α j ≠ 0` for one `j`, and that is exactly what the forms need.** The
system handed to 6.3 is `∑ i, α i X i` together with the coordinate forms `X i` for `i ≠ j`, at
the single place `∞`, and `Module.Dual.linearIndependent_projWithSum` proves it independent from
`α j ≠ 0` alone — whatever the other coefficients do. Linear independence of the `α i` over `ℚ`
is never used and would be strictly stronger; Remark 7.3.3 is visible in the proof and not only
in the statement.

⚠ **The exponent drops by one for free, and one inequality about integers is the whole of it.**
The `n` coordinate forms contribute at most `M ^ n` against the denominator `M ^ (n+1)` of the
central quantity, where `M = max |x i|`, so what is left of `approxProd` is `‖∑ α i x i‖ / M`.
The Subspace Theorem's own exponent `−(n+1) − ε` is then reached from `−n − ε` by
`Rat.mulHeight_intCast_le_iSup`: the height of an **integer** point is at most its sup norm,
because every local factor of the finite part is at most `1`.

⚠ **The statement proved is stronger than the book's.** Bombieri–Gubler read the exponent against
`|x| = max |x i|`; over `ℚ` the projective height of an integer point is `max |x i|` divided by
the gcd of the coordinates, so `mulHeight x ≤ |x|` and the set counted here *contains* the
classical one, by a factor `gcd(x) ^ (n + ε)`. The strengthening is free: 6.3 is a statement
about projective points, and it is the sup norm, not the height, that had to be introduced by
hand.

⚠ **The induction reserves no room, and that is why one `ε` serves.** A proper subspace of `ℚⁿ⁺¹`
lies in the kernel of a nonzero form `∑ i, c i X i`; dropping a coordinate `k` with `c k ≠ 0`
turns `∑ i, α i x i` into `∑ i ≠ k, (α i − α k c i / c k) x i`, whose coefficients are again
algebraic. The restriction is injective on the subspace — the relation determines `x k` — and it
does not raise the height, since removing coordinates lowers every local factor
(`Height.mulHeight_comp_le`). The exponent `−(#ι − 1) − ε` weakens by exactly one when `#ι` drops
by one, so the reduced point satisfies the reduced inequality with the **same** `ε`.

⚠ **The reduced index type is the subtype `{i // i ≠ k}`, and the recursion is on a bound.**
Writing the induction on `Fintype.card ι ≤ n` rather than on `Fintype.card ι = n` makes ordinary
induction suffice, and nothing has to be transported along an equivalence
`{i // i ≠ k} ≃ Fin (#ι − 1)` — the same decision Layer 3.4 made for two variables, for the same
reason.

⚠ **Three cases stand outside the induction.** If every `α i` vanishes the set is empty, and it
must be separated because the Subspace step needs some `α j ≠ 0`. If there are no variables the
value is `0`. If there is *one* variable 6.3 is unavailable — it asks for `[Nontrivial ι]` — and
unnecessary: the height of a one-coordinate point is `1` by the product formula, so the
inequality reads `‖α j‖ · |x j| ≤ 1` and bounds `x j` outright. That last case is where the
theorem degenerates to Liouville's inequality in its crudest form.

⚠ **The nonvanishing hypothesis cannot be dropped, at any exponent.** The form `X 0 − X 1` has
algebraic coefficients and vanishes on the diagonal, so `{x | ‖x 0 − x 1‖ ≤ H(x)^t}` is infinite
for every `t`; the file records that as a rejection test. The sharpness of the exponent itself —
that `−n − ε` cannot be improved to `−n` — is the box principle of Layer 1.3 and is not proved
here.

**7.2 Approximation by algebraic numbers of bounded degree** (Schmidt; Bombieri–Gubler, Corollary
7.3.5) — **landed**, in `DiophantineApproximation/BoundedDegreeApproximation.lean`. For complex
algebraic `α`, a degree bound `D` and `ε > 0`, only finitely many complex algebraic `ξ` of degree
at most `D` satisfy `‖α − ξ‖ ≤ H(f_ξ)^{−D−1−ε}`, with `f_ξ` the primitive integer minimal
polynomial of `ξ` and `H` its naive height. From 7.1 applied to the `D + 1` coefficients
`1, α, …, α^D` — algebraic because `α` is — and the mean value theorem.

```text
Complex.finite_setOf_norm_sub_le :
  IsAlgebraic ℚ α → ∀ (D : ℕ), 0 < ε →
    {ξ : ℂ | ∃ P : ℤ[X], P.IsPrimitive ∧ Irreducible P ∧ aeval ξ P = 0 ∧ P.natDegree ≤ D ∧
      ‖α - ξ‖ ≤ P.supNorm ^ (-(D : ℝ) - 1 - ε)}.Finite
```

`Complex.finite_setOf_exists_root_norm_sub_le` is the same count taken over the minimal
polynomials instead of over their roots, which is the shape the proof produces;
`Real.koksmaExponent_le_of_isAlgebraic` is the milestone in Layer 1.3's language, `w_D^*(α) ≤ D`;
and `Polynomial.norm_aeval_sub_aeval_le` is the mean value theorem the passage runs on.

⚠ **The statement quantifies over the minimal polynomial, because `H(f_ξ)` names an object
Mathlib does not have.** The primitive integer minimal polynomial is defined only up to sign, so
there is no function `ξ ↦ H(f_ξ)` to write the exponent against; the set counted is cut out by
the *existence* of a primitive irreducible `P` with `P ξ = 0`, `deg P ≤ D` and
`‖α − ξ‖ ≤ H(P)^{−D−1−ε}`. That reading is the book's because of one lemma:
`Polynomial.supNorm_eq_of_isPrimitive_of_irreducible` says two such polynomials have the same
naive height, so the existential is `H(f_ξ)` and the degree of the witness is the degree of `ξ`.
The lemma is Layer 1.3's, stated there for a real root; it is a statement about a root in any
`ℚ`-algebra that is a domain, and 7.2 generalized it in place rather than copying it.

⚠ **The mean value theorem had to be proved again over `ℂ`.** Layer 1.3's
`Polynomial.abs_aeval_sub_aeval_le` runs on `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`
over the unordered interval `Set.uIcc`, and there is no interval between two complex numbers.
The telescoping identity `z^k − w^k = z(z^{k−1} − w^{k−1}) + w^{k−1}(z − w)` gives the same
constant `(n+1)^2 H(P) max(1, |z|, |w|)^n` with no analysis in it at all, and the proof is
shorter than the real one.

⚠ **The milestone counts polynomials first, and it has to.** The constant of the mean value
theorem is removed by the exponent: `‖f_ξ(α)‖ ≤ C H^{−D−ε}` becomes `‖f_ξ(α)‖ ≤ H^{−D−ε/2}` as
soon as `H ≥ C^{2/ε}`, and *below* that height there is nothing to say about the numbers — a
bounded set of complex numbers is not finite. It is the polynomials that are finite there, by
bounded degree and bounded height (`Polynomial.finite_setOf_natDegree_le_supNorm_le`), and the
approximants are recovered as their roots at the very end. Bombieri–Gubler's "a familiar argument
already used at the end of Example 7.2.7" is that paragraph.

⚠ **The conjugates of `α` are the one family 7.1 cannot see.** 7.1 needs
`0 < ‖∑ α^i x_i‖`, which fails exactly when `f_ξ(α) = 0`, that is when `ξ` is a conjugate of `α`
— the book's "we may assume that `ξ` is not a conjugate of `α`". The rigidity lemma disposes of
them without a separate argument: a primitive irreducible polynomial vanishing at `α` is the
minimal polynomial of `α` up to sign, so all of those `ξ` are roots of *one* polynomial, whose
height the Northcott branch already carries as a bound.

⚠ **`mulHeight x ≤ H(P)` is where 7.1's projective height meets 1.2's naive one.** 7.1 counts
integer points by their height over `ℚ` and this exponent is read against the sup norm of the
coefficient vector; the inequality needed is `Rat.mulHeight_intCast_le_iSup` again, in the
direction that makes the hypothesis weaker. For the *primitive* minimal polynomial the two
agree, but primitivity is not what makes the step work.

⚠ **No hypothesis `D ≥ 1` is needed, and `D = 0` is vacuous.** A primitive irreducible integer
polynomial of degree `0` is a constant of content one, that is a unit, and units are not
irreducible; there are no algebraic numbers of degree `0` and the set is empty.

⚠ **Remark 7.3.6 is not needed, and is not proved.** The dictionary `H(f_ξ) ≍ H(ξ)^{deg ξ}`
(`ArithmeticHeights` 1.2 with 2.3) would restate the exponent against the absolute height of the
number rather than the naive height of its minimal polynomial. The milestone is the inequality
the mean value theorem produces, which is the one against `H(f_ξ)`, so the dictionary is left
where the book leaves it: in a remark.

**7.3 The exponents of an algebraic number, and simultaneous approximation** (Schmidt 1970) —
**landed**, in `DiophantineApproximation/{SchmidtExponents,SimultaneousSubspaces,
SimultaneousApproximation}.lean`. For real algebraic `α` of degree `D` and every `n`,
`mahlerExponent n α = koksmaExponent n α = min n (D − 1)`.

```text
Real.mahlerExponent_eq_of_isAlgebraic :
  IsAlgebraic ℚ α → ∀ (n : ℕ),
    mahlerExponent n α = ((min n ((minpoly ℚ α).natDegree - 1) : ℕ) : ℝ≥0∞)
Real.koksmaExponent_eq_of_isAlgebraic : the same for koksmaExponent
```

And Schmidt's two theorems on simultaneous approximation (Schmidt 1970; *Diophantine
Approximation*, Ch. VI; Bombieri–Gubler, Remark 7.3.4): for real algebraic `α 1, …, α n` with
`1, α 1, …, α n` linearly independent over `ℚ` and `ε > 0`, finitely many `q ≥ 1` have
`q^{1+ε} ∏ i, ‖q α i‖ < 1`, and finitely many `q ∈ ℤⁿ` with no zero coordinate have
`(∏ i, |q i|)^{1+ε} ‖∑ i, q i α i‖ < 1`, where `‖·‖` is the distance to the nearest integer.

```text
Real.finite_setOf_mul_prod_dist_lt :
  (∀ i, IsAlgebraic ℚ (α i)) → LinearIndependent ℚ (fun o : Option ι ↦ o.elim 1 α) → 0 < ε →
    {q : ℤ | 1 ≤ q ∧ ∃ p : ι → ℤ, (q : ℝ) ^ (1 + ε) * ∏ i, |(q : ℝ) * α i - p i| < 1}.Finite
Real.finite_setOf_prod_abs_mul_dist_lt :
  (∀ i, IsAlgebraic ℚ (α i)) → LinearIndependent ℚ (fun o : Option ι ↦ o.elim 1 α) → 0 < ε →
    {q : ι → ℤ | (∀ i, q i ≠ 0) ∧ ∃ p : ℤ,
      (∏ i, |(q i : ℝ)|) ^ (1 + ε) * |∑ i, α i * q i - p| < 1}.Finite
```

`Real.mahlerExponent_le_natCast_of_isAlgebraic` is the one bound Layer 1 could not supply,
`Complex.finite_setOf_norm_aeval_le` is its polynomial-level form,
`Real.finite_setOf_prod_abs_mul_abs_sum_lt` is the linear form theorem the second simultaneous
statement runs on, and `Rat.exists_finset_submodule_of_prod_le` is the Subspace Theorem step
both of them go through.

⚠ **`n ≥ 1` is not needed.** The prototype carried it because Wirsing's first two inequalities
need it; the milestone does not. At `n = 0` both exponents vanish and so does `min 0 (D − 1)`.

⚠ **The whole of the exponent identity is assembly except one bound.** `w_n(α) ≤ D − 1` is
Liouville's inequality of 1.3, the lower bounds are 1.3's box principle applied twice — at `n`
when `n < D`, at `D − 1` and then by monotonicity when `n ≥ D` — and Wirsing's third inequality
of 1.3 carries them from Mahler's exponent to Koksma's, because at the value `w_n = n` that the
box principle forces it reads `n ≤ w_n^*`. What was missing is `w_n(α) ≤ n`, and it is 7.1
applied to `1, α, …, α^n` and the coefficient vector of the polynomial directly, with no mean
value theorem between them: **7.2's proof with its first step deleted**.

⚠ **The conjugates of `α` cost nothing here.** 7.1 needs a nonzero value, and `Real.mahlerSet`
asks for one in its definition, so the polynomials that vanish at `α` are excluded by the
statement itself. With them go the rigidity lemma and the threshold height that 7.2's proof had
to carry; what survives of that proof is one height comparison and one application of 7.1.

⚠ **Schmidt's exponents are read against the product `∏ i, |q i|`, not the sup norm**, and that
is what forced new Subspace Theorem machinery. For a tuple with no vanishing coordinate the
product is at least the sup norm and can be very much smaller than its `n`-th power, so 7.1's
`Rat.approxProd_projWithSum_le` — which bounds the `n` coordinate forms by `M^n` and keeps only
the one nontrivial form — throws away exactly what these theorems are about.
`Rat.exists_finset_submodule_of_prod_le` keeps the product: with `S∞ = {∞}`, `S₀ = ∅` and the
multiplicity of the real place of `ℚ` equal to one, the central quantity of the Subspace Theorem
*is* `(∏ i ‖L_i x‖)/M^{n+1}`, and the hypothesis needed is `∏ i ‖L_i x‖ ≤ M^{−ε}`.

⚠ **The hypothesis "no zero coordinate" is unremovable**, and the file records it as a rejection
test: with a vanishing coordinate the product is `0` and the inequality holds for every `q`.

⚠ **Two theorems, two inductions, and one of them feeds the other.** The linear form theorem
eliminates one variable on each exceptional subspace and recurses. The theorem on `∑ q_i α_i`
has one variable more — the numerator — and its exceptional subspaces split in two: a relation
not involving the numerator eliminates one `q` and is the recursion, while a relation that does
involve it *determines* the numerator, and then the distance to `ℤ` becomes the linear form
`∑ q_i (α_i + c_i/c_0)` with algebraic coefficients, which the first theorem finishes.

⚠ **Simultaneous approximation needs no induction at all.** One exceptional subspace already
bounds `q`: its relation `c_0 q + ∑ c_i p_i = 0` together with `p_i = q α_i − θ_i`,
`|θ_i| ≤ 1/2`, gives `q(c_0 + ∑ c_i α_i) = ∑ c_i θ_i`, and the left factor is nonzero *because*
`1, α_1, …, α_n` are independent over `ℚ`. That is the one place where the independence
hypothesis is used as a nonvanishing statement rather than as an invariant of a recursion, and
it is why this half of 7.3 is the shorter one.

⚠ **A threshold is unavoidable exactly where the extra variable is.** The numerator is
controlled by the `α_i` and not by the product, so the sup norm of the extended point is only
`≤ C ∏ |q_i|` with `C = ∑ |α_i| + 2`; half of `ε` absorbs `C` once `∏ |q_i| ≥ C`, and below that
threshold `Int.finite_setOf_prod_abs_le` — Northcott for the product — counts the points. The
linear form theorem has no extra variable and needs no threshold at all.

⚠ **The distance to the nearest integer is written as an existential over the numerator.** The
numerator *is* a coordinate of the integer point the Subspace Theorem is applied to, so the
existential is what the proof produces; `Real.abs_sub_round_le` — the nearest integer is
nearest, which Mathlib does not state — says the two readings cut out the same set, and the
acceptance criteria record the reading with `round`.

⚠ **`1, α 1, …, α n` independent over `ℚ` is Mathlib's `LinearIndependent`, indexed by
`Option ι`.** No new predicate was introduced; the proofs run on the unfolded form, "no rational
relation `c₀ + ∑ c_i α_i = 0` is nontrivial", which `forall_eq_zero_of_linearIndependent_option`
produces, and both reductions — eliminating a variable, shifting the coefficients by rationals —
preserve it. An acceptance test records that the hypothesis has teeth: it forces every `α i` to
be irrational.

⚠ **At `n = 1` the exponent identity is Roth's theorem**, and the acceptance criteria check that
reading: a real algebraic irrational has `min 1 (D − 1) = 1`, so `w_1 = 1`, and 1.2's identity
`w_1 + 1 = irrationalityExponent` turns that into `irrationalityExponent α = 2`. Layer 3 is used
nowhere in the proof — the road runs through Layer 6 and 7.1 instead — so this is a second,
independent proof of Roth's theorem inside the same library.

**7.4 The combinatorial transcendence criterion** (Adamczewski–Bugeaud–Luca 2004;
Adamczewski–Bugeaud 2007; Ferenczi–Mauduit 1997) — **landed**, in
`DiophantineApproximation/StammeringWords.lean`, `DiophantineApproximation/DigitExpansions.lean`,
`DiophantineApproximation/RepetitionSubspaces.lean` and
`DiophantineApproximation/TranscendenceCriterion.lean`. For a finite word `V` and real `w ≥ 1`,
`V ^ w` is `V` repeated `⌊w⌋` times followed by the prefix of `V` of length
`⌈(w − ⌊w⌋) |V|⌉` (`List.rpow`, of length `⌈w |V|⌉`). A sequence `a` is **stammering**
(`Function.IsStammering`) if for some `w > 1` there are finite words `U k`, `V k` with
`U k (V k) ^ w` a prefix of `a`, `|U k| / |V k|` bounded, and `|V k|` strictly increasing
(`Function.IsStammeringWith w a`). For `b ≥ 2`:

```text
a : ℕ → Fin b stammering, not eventually periodic  ⟹  Real.ofDigits a transcendental
a : ℕ → Fin b satisfying (∗)_w with w > 2, not eventually periodic  ⟹  the same, from 3.3 alone
```

(`Real.transcendental_ofDigits_of_isStammering`,
`Real.transcendental_ofDigits_of_isStammeringWith_of_two_lt`). Both are proved in a working form
on periodic segments of the digits and for any irrational value
(`Real.transcendental_ofDigits_of_forall_periodic` and `…_of_two_lt`), to which
`Function.IsStammeringWith.exists_periodic` reduces the definition; its converse,
`Function.isStammeringWith_of_periodic`, is what the acceptance criteria use to exhibit a
stammering sequence. Route: a repetition of length `⌈w s⌉` with period `s` after position `r` puts
`(b ^ (r + s) − b ^ r) ξ` within `b ^ (−(w − 1) s)` of an integer `p`
(`Real.abs_mul_ofDigits_sub_le_rpow`); 6.3 over `ℚ` in three variables, with the forms
`X, Y, ξ X − ξ Y − Z` at `∞` and the coordinate forms at the primes of `b`
(`Real.exists_finset_submodule_of_repetition`), puts the points `(b ^ (r + s), b ^ r, p)` into
finitely many proper subspaces; one of them contains infinitely many, and its equation decides.

⚠ **There is no induction on the subspace.** The equation `z₀ X + z₁ Y + z₂ Z = 0` of a subspace
containing infinitely many of the points either does not involve `Z` — then it reads
`z₀ b ^ s + z₁ = 0`, which holds for at most one `s` — or it does, and then the approximation
becomes `|θ b ^ s + η| ≤ 1` with `θ = ξ + z₀ / z₂`, which forces `θ = 0` as `s` grows: `ξ` is
rational. Non-periodicity is used exactly once, as the irrationality of `ξ`.

⚠ **Irrationality needs no uniqueness of expansions.** A rational number may have two base-`b`
expansions, so "the expansion of a rational is eventually periodic" does not directly apply to an
arbitrary `a` with that value. `Real.irrational_ofDigits` works with the tails `T k` of `a`
itself: `b T k = a k + T (k + 1)`, `0 ≤ T k ≤ 1`; a tail `0` or `1` forces a constant run of
digits, and otherwise `a k = ⌊b T k⌋` and `T (k + 1)` is the fractional part of `b T k`, both
functions of `T k`, which for rational `ξ` takes finitely many values.

⚠ **The approximant is never written down.** The classical proof compares `ξ` with the rational
whose expansion is `U V V V ⋯`. Here the comparison is made on the linear form itself: by
`Real.pow_mul_ofDigits` it is the difference of the tails of `a` at `r + s` and at `r`, and
Mathlib's `Real.abs_ofDigits_sub_ofDigits_le` bounds it as soon as they share digits. The bound is
exact — no constant — so `ε = (w − 1) / (C + 1)` works at every point and no threshold is needed.

⚠ **The gain is at the primes, and the Subspace step had to be made again to see them.** At `∞`
alone the product of the three forms at `(b ^ (r + s), b ^ r, p)` is about
`b ^ (2 r + (2 − w) s)`, small only for `w > 2 + 2 r / s`; the factor `b ^ (−(2 r + s))` from the
`l`-adic sizes of the first two coordinates brings the threshold down to `w > 1`. 7.3's
`Rat.exists_finset_submodule_of_prod_le` lives at `∞` alone, so
`Rat.exists_finset_submodule_of_prod_mul_prod_padicNorm_le` adds the coordinate forms at a finite
set of primes; 7.3's step is its case `S = ∅`. The only new ingredient is that the height of an
integer point is at most its sup norms at `∞` and at `S` (`Rat.mulHeight_intCast_le_iSup_mul_prod`).

⚠ **This genuinely needs three variables**: the denominators have the special shape
`b ^ r (b ^ s − 1)`, the Subspace Theorem exploits both factors, and Ridout's theorem (3.3), which
sees only the factor `b ^ r`, gives the criterion only for `w > 2` (Ferenczi–Mauduit 1997). ⚠ **The
primes of `b` are Ridout's `S₂`, not `S₁`** — the factor `b ^ r` is on the denominator, whose
target is `∞`; this section formerly said "`S₁` the primes dividing `b` and `S₂` empty", which is
the wrong way round. ⚠ **Ridout's theorem sees the approximant in lowest terms**, and reducing may
remove primes of `b` from the denominator — the ones carrying the gain. What saves the argument is
that the part of the denominator prime to `b` does not grow along divisors
(`Rat.mul_prod_padicNorm_le_of_dvd`), so it stays below `b ^ s`, and that the approximant lies in
`[0, 1]`, so its height is its denominator (`Real.digitsPrefix_sub_mem`).

⚠ **`1 ≤ |V k|` is Ridout's hypothesis and not the Subspace Theorem's.** The three-variable route
never divides by `b ^ s − 1` and uses only that `|V k|` is strictly increasing; the `w > 2` route
needs `b ^ s − 1 ≠ 0`. `IsStammeringWith.exists_periodic` supplies both by dropping the first
repetition, which is also what turns the bounded ratio `|U k| / |V k|` — Lean's `x / 0 = 0` makes
it say nothing at `|V k| = 0` — into `|U k| ≤ C |V k|`.

Acceptance criteria: the lacunary number `∑ j, 10 ^ (−(2 ^ j + 1))` is transcendental, three ways
— through the milestone as stated, its digits being stammering with `w = 3`; through the `w > 2`
criterion; and through the working form. Rejection: the constant sequence `0` is stammering and
its value is algebraic, so non-periodicity is load-bearing; and Condition `(∗)_1` holds for every
sequence, so `w > 1` is.

**7.5 The complexity of an algebraic irrational** (Adamczewski–Bugeaud 2007, Theorem 1;
Morse–Hedlund 1938) — **landed**, in `DiophantineApproximation/FactorComplexity.lean` and
`DiophantineApproximation/ComplexityTranscendence.lean`. For `a : ℕ → α`, the **complexity**
`p n` (`Function.complexity`) is the number of distinct words `a i ⋯ a (i + n − 1)`
(`Function.factor`) occurring in `a`. Over a finite alphabet:

```text
p is nondecreasing; p 0 = 1
a eventually periodic  ⟺  p bounded  ⟺  p n ≤ n for some n          (Morse–Hedlund)
p n ≤ C n for infinitely many n  ⟹  a stammering                      (the combinatorial lemma)
b ≥ 2, ∑ a k / b ^ (k + 1) algebraic and irrational  ⟹  p n / n → ∞   (the theorem)
```

(`Function.complexity_mono`, `Function.isEventuallyPeriodic_tfae`, `Function.lt_complexity`,
`Function.isStammering_of_frequently_complexity_le`, `Real.tendsto_complexity_div_atTop`, and the
transcendence criterion it is proved as, `Real.transcendental_ofDigits_of_frequently_complexity_le`).
The lemma knows no number. The theorem also needed the converse of 7.4's irrationality statement,
`Real.irrational_ofDigits_iff`: for `b ≥ 2` the value is irrational exactly when the expansion is
not eventually periodic, since a period `p` from `N` on makes the tail at `N` the fixed point of
`T ↦ (P + T) / b ^ p`.

⚠ **The pigeonhole's repetition has to be re-cut, and then there is no case split.** Of the first
`p n + 1` positions two, `r < t ≤ C n`, carry the same factor of length `n`, so `a` has period
`s = t − r` on a segment of length `n + s`. For `s` small against `n` that is a high power of a
short word and `r / s` is unbounded — the classical proof splits into cases there. Taking instead
the period `P = (⌊n / 2 s⌋ + 1) s`, a multiple of `s` in `(n / 2, n / 2 + s]`, gives `r ≤ 2 C P`
and, since `s ≤ C n`, a segment of length at least `(1 + 1 / (1 + 2 C)) P`: one exponent for every
`n` (`Function.exists_periodic_of_frequently_complexity_le`).

⚠ **The theorem consumes 7.4's working form, not its definition.** The pigeonhole produces
positions and periods, which is the shape 7.4's criterion is proved in; the lemma's statement
"`a` is stammering" goes through `Function.isStammeringWith_of_periodic` and back, and the
theorem does not take that detour.

⚠ **Morse–Hedlund needs a single `m` with `p (m + 1) = p m`**, which `p 0 = 1` and `p n ≤ n` force
below `n`. Then `List.take m` maps the factors of length `m + 1` onto those of length `m` between
finite sets of the same size, hence injectively (`Set.injOn_of_ncard_image_eq`): every factor
has one right extension, the factor at `i + 1` is a function of the factor at `i`, and two equal
factors make `a` periodic from the first of them on.

⚠ **The alphabet must be finite, and `Set.ncard` says so silently.** Over `ℕ` the identity has
infinitely many factors of length `1`, which `Set.ncard` counts as `0`: `p 1 = 0 < 1 = p 0`
(`Function.complexity_id_one`).

Acceptance criteria: the binary digits of `∑ k, 2 ^ (−2 ^ k)` — `1` at the positions `2 ^ k − 1`
— have complexity at most `3 n + 1`, so the number is transcendental by 7.5, and read the other
way the theorem itself denies that it is an algebraic irrational; an algebraic irrational has more
than `1000 n` distinct blocks of `n` decimal digits for all large `n`; a constant sequence has
complexity `1` and is stammering by the lemma.
Rejection: the constant sequence `0` has an algebraic value and `p n / n → 0`, so irrationality
is load-bearing; and the identity of `ℕ` shows the finite alphabet is.

### Layer 8: unit equations and Diophantine equations

Throughout, `S : Finset (HeightOneSpectrum (𝓞 K))` and `S.unit K` is Mathlib's group of
`S`-units.

**8.1 The unit equation in two variables** (Siegel, Mahler, Lang) — **landed**, in
`DiophantineApproximation/UnitEquation.lean`. For `a, b ∈ Kˣ`, finitely many pairs of `S`-units
`(x, y)` satisfy `a x + b y = 1` (`NumberField.finite_setOf_unit_add_unit_eq_one`, the prototype
verbatim). Route: enlarge `S` until `a` and `b` are `S`-units (`NumberField.exists_finset_mem_unit`)
and absorb them, so the equation is `x + y = 1` (`NumberField.finite_setOf_add_eq_one`); apply
**6.5** with the three forms `X₀`, `X₁`, `X₀ + X₁` at every infinite place and every place of `S`,
which are in general position (`NumberField.isGeneralPosition_unitEquationForms`), and `ε = 1`;
the solutions lie on finitely many lines through the origin, and a proper subspace of `K²` meets
`X₀ + X₁ = 1` at most once (`NumberField.eq_of_mem_of_add_eq_one`).

⚠ **No split by the largest coordinate.** The route this section used to give — at every place
the form `X₀ + X₁` and the coordinate form of the smaller coordinate, one application of 6.4 (or
3.4) per choice — is Vojta's refinement done by hand. 6.5 does it: with all three forms, the
central quantity at a solution is **exactly** `H(x, y) ^ (-3) = H ^ (-#ι - 1)`
(`NumberField.generalProd_unitEquationForms_eq`), with no comparison of coordinates, no choice
function and no case split. The numerators multiply to `1` by the `S`-product formula (the value
of `X₀ + X₁` is `1` everywhere), and the denominators to `H ^ 3` because the point is `S`-primitive.

⚠ **Primitivity is the equation.** The height of `(x, y)` is its product of local sup norms over
`S∞ ∪ S` only for an `S`-primitive point, and `1 · x + 1 · y = 1` is the Bézout relation that
makes it one: nothing about units is needed for that step, only the equation.

⚠ **Neither the affine form (6.4) nor 3.4 is used.** The milestone rests on 6.5, and through it on
6.3; the cheap route through 3.4 recorded here before remains available and unneeded.

Acceptance criteria: `(2, −1), (3, −2), (4, −3), (9, −8)` solve `x + y = 1` in `{2, 3}`-units of
`ℚ`, with `S` given as the height-one primes of `𝓞 ℚ` over `2` and `3`, and that solution set is
finite; the completeness of the list is not asked for. Rejection: in `ℚˣ` the equation
`x + y = 1` has infinitely many solutions `(n + 2, −(n + 1))`, so the units are load-bearing.

**8.2 The unit equation in `n` variables** (Evertse; van der Poorten–Schlickewei;
Bombieri–Gubler, Theorem 7.4.2 and Corollary 7.4.3) — **landed**, in
`DiophantineApproximation/UnitEquationSeveral.lean`. For `a : ι → Kˣ`, finitely many
`x : ι → S.unit K` satisfy `∑ i, a i * x i = 1` with **no vanishing subsum**,
`∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, a i * x i ≠ 0` (`NumberField.finite_setOf_sum_unit_eq_one`,
the prototype verbatim). Without that condition (Corollary 7.4.3): there is a finite `Φ ⊆ K`
such that every solution has a coordinate with `a i * x i ∈ Φ`
(`NumberField.exists_finite_forall_exists_mul_mem`). And for a finitely generated subgroup
`Γ ≤ Kˣ`, the same with `x i ∈ Γ` (`NumberField.finite_setOf_sum_mem_eq_one`, the prototype
verbatim), since a finitely generated subgroup of `Kˣ` lies in `S.unit K` for a finite `S`
(`NumberField.exists_finset_le_unit`). Route, by induction on the number `n` of variables: absorb
the coefficients by enlarging `S`, as in 8.1; apply **6.5** with the `n + 1` forms `X i` and
`∑ i, X i` at every place (in general position, `NumberField.isGeneralPosition_sumEquationForms`)
and `ε = 1` — the central quantity at a solution is exactly `H(x) ^ (-n - 1)`
(`NumberField.generalProd_sumEquationForms_eq`) — so the solutions lie in finitely many proper
subspaces; on each, a relation `∑ i, c i * x i = 0` with `c j ≠ 0` turns the equation into
`∑ i, b i * x i = 1` with `b j = 0` (`NumberField.exists_sum_mul_eq_one_of_ne_top`).

⚠ **The induction takes two steps, and the roadmap's one-line route hid the second.** The shortened
equation `∑ i, b i * x i = 1` may have vanishing subsums, so the induction hypothesis does not
apply to it. A *minimal* subsum equal to `1` has none
(`NumberField.exists_subset_sum_eq_one_forall_ne_zero`) and fewer variables, but it controls only
its own coordinates, and which subsum depends on the solution: what comes out is that **some
coordinate `x k` of every solution lies in a fixed finite set**
(`NumberField.exists_finite_forall_exists_apply_eq`, which is also Corollary 7.4.3). The second
step fixes `x k = u`: the remaining coordinates solve `∑ i ≠ k, x i = 1 - u` in `n - 1` variables,
and `u ≠ 1` **because** the subsum over `i ≠ k` does not vanish
(`NumberField.finite_setOf_apply_eq`).

⚠ **No 6.4, again.** As in 8.1, Vojta's refinement makes the central quantity exact and no
coordinate is singled out; the step "6.4 with `ε = 1`" the route used to name is not taken.

⚠ **The induction runs over types.** The shortened equations live on subtypes — a minimal subsum
`J' : Finset ι` and the complement `{i // i ≠ k}` — so the statement is proved for every
`Fintype` of smaller cardinality in the same universe, by strong induction on `Fintype.card`,
and the coefficients are carried as nonzero elements of `K` (`NumberField.unitSolutions`) rather
than units, so that restriction needs no re-packaging.

Acceptance criteria: `1/2 + 1/3 + 1/6 = 1` is a solution in `{2, 3}`-units of `ℚ` with no
vanishing subsum, and that solution set is finite, also over the subgroup of `ℚˣ` generated by
`2` and `3`. Rejection: `(2 ^ k, −2 ^ k, 1)` solves `x₁ + x₂ + x₃ = 1` in `{2, 3}`-units for
every `k`, so the no-vanishing-subsum hypothesis is load-bearing.

**8.3 Triangularly connected decomposable forms** (Győry–Papp; Evertse–Győry, *Unit Equations in
Diophantine Number Theory*, Ch. 9) — **landed**, in `DiophantineApproximation/DecomposableForm.lean`.
For a finite family `l : κ → Module.Dual K V`, join `j` and `j'` when some `l k` equals
`a • l j + b • l j'` with `a, b ≠ 0` (`Module.Dual.TriangleAdj`), and call the family
**triangularly connected** when every two indices are joined by a path
(`Module.Dual.IsTriangularlyConnected`, a `Relation.ReflTransGen`). For such a family with common
kernel `0`, `⨅ j, LinearMap.ker (l j) = ⊥`:

* the points at which every `l j` takes an `S`-unit value are `S`-unit multiples of finitely many
  points (`NumberField.exists_finite_forall_eq_smul`, on any `K`-vector space);
* for `G = c * ∏ j, l j ^ e j` with every `e j ≠ 0` and `m ≠ 0`, finitely many `x : ι → K` with
  `S`-integral coordinates satisfy `G x = m` (`NumberField.finite_setOf_mul_prod_eq`);
* the `x` with `S`-integral coordinates and `G x ∈ S.unit K` are `S`-unit multiples of finitely
  many of them, which can be taken among the solutions
  (`NumberField.exists_finite_forall_mul_prod_mem_unit`).

Route: along a triangle `l k = a • l j + b • l j'`, at a point where all three forms take `S`-unit
values, `a (l j x / l k x) + b (l j' x / l k x) = 1` is **8.1** with coefficients `a, b`, so
`l j' x / l j x` takes finitely many values
(`NumberField.finite_setOf_div_of_triangleAdj`); along a path the ratios multiply
(`NumberField.finite_setOf_div_of_reflTransGen`); so every `l j x / l j₀ x` does, and since the
common kernel is `0`, `LinearMap.pi l` is injective and the vector of ratios, which is
`LinearMap.pi l ((l j₀ x)⁻¹ • x)`, determines the point up to the scalar `l j₀ x`. For `G`: enlarge
`S` until `c` is a unit and the coefficients of the forms are integral
(`NumberField.exists_finset_integer_coeff`); then every `l j x` is integral and their product of
positive powers is a unit, so every `l j x` is a unit
(`NumberField.exists_mem_unit_of_mul_prod`: at each place outside `S` the absolute values are at
most `1` with product `1`); and `G (u • y) = u ^ E * G y` with `E = ∑ j, e j`
(`NumberField.mul_prod_apply_smul`) leaves at most `E` values of `u` for each of the finitely many
`y`.

⚠ **Pairwise non-proportionality is not needed**, and is not a hypothesis: a triangle through
proportional or repeated forms is still a unit equation, and 8.1 asks nothing of its coefficients
beyond being nonzero. The triangle relation is also taken with `k` unrestricted, which makes the
connectivity hypothesis weaker and the theorem stronger.

⚠ **The unit version needs no discreteness of valuations.** Enlarging `S` loses the scaling by
`S`-units, and the obvious repair bounds the valuations of the scalar at the added places and
counts lattice points. Instead: two solutions `u • y` and `u' • y` on one line have
`(u / u') ^ E = G (u • y) / G (u' • y)`, an `S`-unit, and an absolute value whose `E`-th power is
`1` is `1`, so `u / u'` is an `S`-unit and **each line carries a single class** — the finite set is
one chosen solution per line.

⚠ **The split case only.** Forms whose linear factors are defined over a finite extension of `K`
are not included: passing to that extension with the places above `S` is moved to **8.4**, the
first consumer, where the factors of an irreducible binary form are never defined over `K`.

⚠ **Nothing above 8.1**: no 8.2, no Subspace Theorem, no heights — the file quotes
`finite_setOf_unit_add_unit_eq_one` once and is otherwise valuations and linear algebra.

Acceptance criteria: `x y (x + y) = 2` has the integer solution `(1, 1)` and finitely many
integer solutions (`S = ∅`); modulo `{2}`-units, finitely many `{2}`-integral points make
`x y (x + y)` a `{2}`-unit. Rejection: `X, Y` are not triangularly connected, and `x y = 1` has
the infinitely many `{2}`-integral solutions `(2 ^ k, 2 ^ (−k))`, so connectivity is
load-bearing.

**8.4 Thue and Thue–Mahler** (Thue 1909; Mahler 1933; Bombieri–Gubler 5.3.1–5.3.2) — **landed**,
in `DiophantineApproximation/{SIntegerExtension,ThueMahler}.lean`. For `g ∈ K[X]` of degree at
most `d` with at least three distinct roots in an algebraically closed `Ω ⊇ K`, the point at
infinity counting as one when `deg g < d` — Layer 3.6's hypothesis, which says that
`G = g.homogenize d` has at least three pairwise non-proportional linear factors over `Ω`:

* `G(x, y) = m` with `m ≠ 0` has finitely many solutions in `S.integer K`
  (`NumberField.finite_setOf_eval_homogenize_eq`);
* the `S`-integral `(x, y)` with `G(x, y) ∈ S.unit K` are `S`-unit multiples of finitely many of
  them, which can be taken among them (`NumberField.exists_finite_forall_eval_homogenize_mem_unit`);
* for `g ∈ ℤ[X]` with the hypothesis over `ℂ` and primes `p 1, …, p s`, finitely many coprime
  integers `x, y` and exponents `z` satisfy `|G(x, y)| = p 1 ^ z 1 ⋯ p s ^ z s`
  (`Polynomial.finite_setOf_natAbs_eval_homogenize_eq_prod_pow`).

Route: over the splitting field `L` of `g`, `G` is its leading coefficient times powers of
`X − r Y` for the distinct roots `r` and of `Y` when `deg g < d`, pairwise non-proportional
(`Polynomial.exists_eval_homogenize_eq_mul_prod_binary`); at least three pairwise
non-proportional binary forms are triangularly connected, since two of them span the dual of `L²`
and Cramer's rule writes a third with nonzero coefficients
(`Module.Dual.isTriangularlyConnected_binary`); so 8.3 applies over `L` with the primes of `𝓞 L`
above `S` (`NumberField.finite_setOf_eval_homogenize_eq_of_splits`). An element of `K` is an
`S`-integer (an `S`-unit) exactly when its image is one above `S`
(`NumberField.algebraMap_mem_integer_iff`, `NumberField.map_mem_unit_iff`: the place of `𝔓`
restricted to `K` is a positive power of the place below), and `K² → L²` is injective.

⚠ **The extension passage is the one owed by 8.3, and it costs one short file**:
`HeightOneSpectrum.under (𝓞 K) ⁻¹' S` is finite because the primes over a prime are, and both
directions of the dictionary are `FinitePlace.mk_algebraMap` with the exponent `e f` used only
through its positivity. The converse needs a prime above every prime and is the one the unit
version uses.

⚠ **The unit version descends without the degree, the norm or homogeneity.** Over `L` every
solution is `u • y` for one of finitely many `y`; two `K`-solutions on the line `L ⬝ y` differ by a
scalar that is a ratio of their coordinates, hence in `K`, and a unit above `S`, hence an `S`-unit
of `K`. One chosen `K`-solution per line is the finite set.

⚠ **Thue–Mahler over `ℚ` is the unit version plus two elementary facts**: a line through the
origin carries at most two coprime integer points, `c` and `−c` — Bézout for `c` makes the ratio
an integer and Bézout for the other point makes it a unit (`Int.finite_setOf_isCoprime_eq_mul`) —
and the exponents are bounded by `|G(x, y)|`. The sign is absorbed by stating `|G(x, y)|`; the
primes need not be distinct.

⚠ **Nothing above 8.3 is used**, and through it nothing above 8.1: Thue's theorem over `ℤ` was
proved in 3.6 by Roth's theorem, and here it follows from the unit equation instead.

Acceptance criteria: in every number field and for every finite `S`, `x³ − 2 y³ = 1` has finitely
many `S`-integral solutions and, modulo `S`-units, finitely many `S`-integral points make
`x³ − 2 y³` an `S`-unit; `x³ − 2 y³ = ± 2 ^ a 3 ^ b` has finitely many solutions in coprime `x, y`,
among them `(2, 1, 1, 1)`. Rejection: without coprimality `(2 ^ k, 0)` solves
`x³ − 2 y³ = 2 ^ (3 k)` for every `k`; and `x² − 2 y² = ± 1`, with two linear factors, has the
infinitely many coprime solutions of Pell's equation, so "three" cannot be lowered.

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
  could not be done here — Layer 1 gives only `[2, 3]` — and is **landed in 3.3**, where Roth's
  theorem gives the value `2`; it is the acceptance test of `…/RothRational.lean`.
- **1.2.** `koksmaExponent 1 ξ = mahlerExponent 1 ξ` and `mahlerExponent 1 ξ + 1 =
  irrationalityExponent ξ` for every real `ξ`; `mahlerExponent 1 q = 0` at a rational and
  `1 ≤ mahlerExponent 1 (√2)` — **landed**, together with the Möbius invariance of both exponents
  and Gelfond's inequality over `ℤ`. ⚠ The rejection tests that this list did not ask for are the
  ones that pin the *normalization*: `mahlerExponent 1` is not the irrationality exponent, and
  the constant `2^{deg}` in Gelfond's inequality cannot be dropped.
- **1.3, 7.3.** `mahlerExponent n (√2) = 1` for all `n ≥ 1` from Layer 1 alone;
  `mahlerExponent n (2 ^ (1/3 : ℝ)) = min n 2` only after 7.1. ⚠ **Both are now available**:
  7.2 landed the Koksma half of the upper bound, `koksmaExponent n α ≤ n`, and 7.3 landed the
  Mahler half `w_n ≤ n` — the same appeal to 7.1 without the mean value theorem — and with them
  `mahlerExponent n α = koksmaExponent n α = min n (deg α − 1)` at every algebraic `α` and every
  `n`, which contains both examples. ⚠ When this list was written neither was available: the
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
  asked for first, that **Roth's theorem is false with `κ = 2`**, could not be done here, and the
  reason was a boundary and not a difficulty: the witness is Dirichlet's theorem at an algebraic
  irrational, so it needs a chosen real place and the dictionary between
  `Real.irrationalityExponent` and the product over the places of `ℚ` — which is precisely
  **Layer 3.3**. It is **landed there**, in `…/RothRational.lean`, at `ξ = √2 − 1`. What was
  landed here instead is a **rejection test** that costs no places: at `κ = 0` the right-hand
  side is `1`, the truncated product is always at most `1`, and *every* element of `K` is a
  solution, so the hypothesis on `κ` is load-bearing. ⚠ The third item on this list, about two
  targets at one place, is not a statement of this milestone at all — Roth's theorem carries one
  target per place — and is answered in 3.3, where the target `∞` makes the question concrete:
  `∞` and `0` are different targets at the same place, and the acceptance criteria of
  `…/RothInfinity.lean` exhibit a `β` at which the two factors are `1/2` and `1`.
- **3.3.** This list asked for one thing under 3.2 and one under 1.1, and both are **landed**
  here: **Roth's theorem is false at `κ = 2`**, at `ξ = √2 − 1`, because Mathlib's infinite
  Dirichlet set `{q | |ξ − q| < 1/q.den²}` sits inside the set the theorem would have to bound —
  for `ξ ∈ (1/4, 3/4)` every such `q` has naive height exactly `q.den`; and
  `irrationalityExponent (2 ^ (1/3)) = 2`, the value Layer 1 left between `2` and `3`. ⚠ Three
  more earn their place. A **conformance** test, that Layer 3.2 is the case of the `OnePoint`
  statement in which every target is finite, so nothing was weakened to make room for `∞`; a
  **rejection** test, that `∞` and `0` are genuinely different targets — at a `β` of local size
  `2` the factors are `1/2` and `1` — so the `OnePoint` is not decoration; and a **sharpness**
  test for the `p`-adic form, that at `ε = 0` it is false, since with target `0` in `F = ℚ` the
  powers of `p` satisfy `|p^k|_p = |p^k|^{−1}` with equality. ⚠ One test is about Lean and not
  about mathematics, and it is the one that caught the roadmap's formula: the factor at the
  target `∞` is `1` at `β = 0`, while `min 1 (|β|_v)⁻¹` is `0` there.
- **3.4.** **Landed**, four tests. A **conformance** test, that the roundtrip lands on Layer
  3.2's own statement hypothesis for hypothesis, so the two statements are the same statement and
  not two shapes that happen to be true together. Two tests about the **point at infinity**: that
  for the coordinate forms `(0, 1)` makes `approxProd` vanish — so it is a solution for every
  `ε`, and the exceptional set must contain a line that no `β ∈ K` names — and that it lies on
  none of the lines `K ⬝ (1, β)`. And a **sharpness** test for the local comparison, that no
  constant independent of the target can bound `min(1, |β − t|) · max(1, |β|)` by `|β − t|`:
  at `β = t + 1` the first is `|t| + 1` and the second is `1`. ⚠ One more is about Lean and not
  about mathematics: the projective height of `[0 : 1]` is `1`, and so is `mulHeight₁` of Lean's
  junk ratio `1 / 0 = 0`, which is why the identity "the height of `x` is the height of
  `x 1 / x 0`" needs no hypothesis `x 0 ≠ 0` and is true where `β` is not defined.
- **3.5.** **Landed**, four tests. The one asked for here: `‖(3/2)^k‖ > exp (−k/10)` for all
  but finitely many `k`, with no value of the exceptional set asserted. Two **rejection** tests,
  that the conclusion is *false for every `ε`* at `(p, q) = (3, 1)` and at `(4, 2)` — so `q ≥ 2`
  and the coprimality are both load-bearing and for the same reason, that `(p/q)^k` is then an
  integer. And a test that **`k = 0` is in the exceptional set for every `ε`**, which is why the
  conclusion has to be `∀ᶠ` and cannot be `∀`. Under them, in `PrimeProducts.lean`, two more:
  that `d ≠ 0` is not removable from the product formula — the empty product is `1` and Lean's
  `(0 : ℚ)⁻¹` is `0` — and that over a set of primes missing a factor the product is too
  **large**, never too small.
- **3.6.** **Landed**, six tests. `x³ − 2 y³ = m` has finitely many solutions for every `m ≠ 0`,
  the three complex roots of `X³ − 2` being distinct because it is separable; `x² y − 2 y³ = m`
  likewise, through the branch where `Y` divides the form and no approximation is used; and
  `x y (x + y) = m`, entered through the headline statement with the three linear factors `X`,
  `Y`, `X + Y` supplied by hand. Two **rejection** tests: Pell's equation `x² − 2 y² = 1` has
  infinitely many solutions — so "three" cannot be lowered to two — and `x³ − x y² = 0` has the
  whole line `x = 0` while `X³ − X` has the three distinct roots `0, 1, −1`, so `m ≠ 0` is not
  removable. ⚠ The first and the Pell test are the two set for **8.4** below, over `ℤ`.
- **3.7.** **Landed**, six tests. Two **rejection** tests of the gap principle, over `ℚ` with
  `S = {∞, 2}` and the targets `3` at `∞` and `5` at `2`: both `3` and `5` are solutions for every
  `κ`, with the close heights `log 3` and `log 5`, and at `κ = 10`, `N = 4` the conclusion fails
  for the pair — so the theorem puts them in different classes, and without the class hypothesis
  it would be false — and fails for `3` against itself, so `β ≠ β'` is not removable. A
  **conformance** test that at one place every solution of height greater than `1` lies in one
  class, so that Davenport and Roth's gap principle needs no class hypothesis; the book's count
  of small solutions, at the endpoint `X = log 16 / (c − 1)` its own hypothesis excludes; the
  quantifier order of the large count, `∃ B, ∀ α, ∃ L`, with `B = rothLargeCount`; and the
  sharpness of the chain lemma — two points of heights `1` and `2` at ratio `3` form no chain and
  fill the bound `1 · 2`.
- **3.8.** **Landed**, three tests. A **conformance** test that constant targets give 3.2 back: an
  infinite solution set of 3.2 enumerates injectively, its heights tend to infinity by Northcott,
  a constant is `o` of them, and 3.8 bounds the indices. Two **rejection** tests over `ℚ` at
  `S = {∞}`: the constant pair `(0, 0)` satisfies the growth condition without its `1` and is a
  solution at every index, so the `1` is not removable; and the constant pair `(2, 2)` — targets
  equal to the approximations — satisfies it with `O` in place of `o` and is a solution at every
  index, so the `o` cannot be weakened.
- **4.1.** **Landed**, two tests. A **conformance** test: over `ℚ`, with `S₀ = ∅`, the coordinate
  forms and `c = 0`, the body is the cube `[−1, 1]ⁱ`, of volume `2 ^ #ι`, and the lattice is `ℤⁱ`,
  of covolume `1` — which pins the unit body and the normalization of the covolume at once. A
  **rejection** test of the book's finite-place volume: at the `2`-adic place of `ℚ`, in one
  variable with `L = id`, `c = 1` and `Q = 3/2`, the largest value of `|·|_2` at most `3/2` is `1`
  and the covolume is `1`, not `Q ^ (−c) = 2/3`.
- **4.2.** **Landed**, three tests. Two **conformance** tests over `ℚ`: the `K`-minima are the
  real minima, since `d = 1` closes `λ l ≤ μ l ≤ λ (d (l − 1) + 1)`; and in one variable both
  halves of Minkowski's second theorem over `K` are equalities, `μ 1 · vol B = 2 · covol Λ` — the
  classical `|β| / a` for the interval `[−a, a]` and the lattice `ℤ β` — which pins the
  normalization `2 ^ {d (n + 1)}` and the constant `c_ℚ = 1`, the house of the integral basis
  `± 1`. A **rejection** test: the minima vanish above `n + 1` and are positive below it, so they
  are not monotone on all of `ℕ` and every statement about them carries `l ≤ n + 1`.
- **4.3.** **Landed**, three tests. A **conformance** test over `ℚ`, in one variable, with
  `S₀ = ∅`, the coordinate form and `c = −1`, of weight `−1`: the rank is `1` exactly when `Q ≤ 1`,
  the domain being the integers of absolute value at most `Q⁻¹` — so the conclusion of Lemma
  7.5.12 holds at every level above `1` and fails at `1`, and is eventual, not uniform. Two
  **rejection** tests: with `c = 0` the domain is `ℤ ∩ [−1, 1]`, of rank `1` and with minimum
  exactly `1`, so the minima are counted at most `1` and not below it; and for the coordinate forms
  with `c = 0`, of weight `0`, every domain contains the standard basis and the rank is `n + 1` at
  every level, so the weight has to be negative, not merely nonpositive.
- **4.4.** **Landed**, four tests, over `ℚ` in two variables with the standard basis. A
  **conformance** test: for the forms `± (2/5) X₀ + X₁` at `∞` and `μ = (2/5, 1)`, `ξ = −2` meets
  the conclusion with `C = 9/5`. Three **rejection** tests: for the same data no `ξ`, rational or
  real, meets it with `C = 1`, so the best constant lies in `(1, 9/5]` and the infinite places are
  genuinely worse than the finite ones; for `X₀ ± ε X₁` and `μ = (1, ε)` decreasing, every other
  hypothesis holds and no `C` works for all `ε`, so the minima must be sorted; and at the `2`-adic
  place, for `4 X₀ + X₁`, `4 X₀ + 3 X₁` and `μ = (1/4, 1)`, no coefficient integral at `2` meets
  the bound `1/4`, so the coefficients are `S₀`-integers and not algebraic integers.
- **4.5.** **Landed**, four tests. Two **conformance** tests: in two variables the wedge of two
  forms on the wedge of two vectors is the `2 × 2` determinant with the forms along the rows, which
  pins the orientation of Laplace's identity; and in `ℚ³` with `k = 1`, `e₀ ∧ (e₁ + e₂)` lies in
  the span of the wedges meeting the first index and the top wedge `e₁ ∧ e₂` does not — the span of
  the wedges *contained in* the first `k` indices would be `0`. Two **rejection** tests on the
  choice of `k`: for the minima `1/2, 2, 2, 8` of a domain of rank `1` the jump at `k = 2` fails
  (7.41) and the jump at `k = 1` meets it, so the choice matters; and for the minima `4, 8` of a
  domain of rank `0` no `k` meets it, so the rank has to be positive.
- **5.1.** **Landed**, three tests. Two **rejection** tests: over `ℚ` with `S₀` the `2`-adic
  place the primitive one-point tuples `(2 ^ k)` have projective height `1` and affine height
  `2 ^ k`, so Lemma 7.5.4 fails for every constant without the unit multiple; and over `ℚ` with
  `S₀ = ∅` the point `(2, 2)`, which is not primitive at `2`, has height `1` while the product of
  its local sup norms over the infinite places and `S₀` is `2`, so the height identity needs
  primitivity. One **conformance** test: at the `2`-adic place of `ℚ`, `|log |2|₂| = log H(2)`,
  so the bound (7.19) is sharp.
- **6.3.** Schmidt's example that the conclusion cannot be finiteness of points: with
  `L 1 = X 1 + √2 X 2 + √3 X 3`, `L 2 = X 1 − √2 X 2 + √3 X 3`, `L 3 = X 1 − √2 X 2 − √3 X 3` at
  `∞`, every solution of `x 1 ² − 2 x 2 ² = 1`, `x 3 = 0` satisfies
  `|L 1 x · L 2 x · L 3 x| = (x 1 + √2 x 2)⁻¹ ≤ ‖x‖^{−ε}` for `ε ≤ 1`: infinitely many solutions,
  all in the plane `x 3 = 0`.
- **8.1, 8.2.** `(2, −1), (3, −2), (4, −3), (9, −8)` solve `x + y = 1` in `{2, 3}`-units of `ℚ`
  and the solution set is finite; the completeness of any list is not asked for. ⚠ **8.1's half is
  discharged**, in `…/UnitEquation.lean`. And
  `(u, −u, 1)` solves `x 1 + x 2 + x 3 = 1` for every unit `u`: the no-vanishing-subsum
  hypothesis is not removable. ⚠ **8.2's half is discharged**, in `…/UnitEquationSeveral.lean`,
  with `u = 2 ^ k` in `{2, 3}`-units, and with `1/2 + 1/3 + 1/6 = 1` as a solution that has no
  vanishing subsum.
- **8.3.** `x y (x + y) = 2` has finitely many integer solutions, among them `(1, 1)`; `x y = 1`
  has the infinitely many `{2}`-integral solutions `(2 ^ k, 2 ^ (−k))`, and `X, Y` make no
  triangle. ⚠ **Discharged**, in `…/DecomposableForm.lean`, with the unit version over `{2}` as
  well.
- **8.4.** `x³ − 2 y³ = 1` has finitely many integer solutions; `x² − 2 y² = 1` has infinitely
  many, and has two linear factors. ⚠ Over `ℤ` both are already discharged by 3.6's tests; what
  8.4 adds is the number field and the `S`-integers. ⚠ **Discharged**, in `…/ThueMahler.lean`, in
  every number field and for every finite `S`, with the unit version, Thue–Mahler for the primes
  `2, 3`, and two rejections: coprimality, and Pell's equation among coprime pairs.
- **7.5.** The characteristic sequence of the powers of `2` has `p(n) ≤ 3 n + 1` — a window of
  length `n` starting beyond `2 n` contains at most one `1` — so `∑ k, 2^{−2^k}` is
  transcendental by 7.5. ⚠ **7.4 already proves the same kind of number transcendental, without
  the complexity function**: its acceptance criteria take the characteristic sequence of the powers
  of `2` in base `10`, whose zeros after position `4 · 2 ^ k + 1` form a word `0 ^ (2 ^ k)` to the
  power `3`, and conclude through the milestone, through the `w > 2` criterion and through the
  working form. What 7.5's test adds is that the complexity route arrives at the same place.
  ⚠ **Discharged**, in `…/ComplexityTranscendence.lean`, with the count exactly as written here:
  `2 n` factors start before position `2 n`, and each later one is determined by where its one
  `1` is, if any — `n + 1` choices. The number is stated as `Real.ofDigits` of that digit
  sequence, which is `∑ k, 2 ^ (−2 ^ k)`; the identity of the two sums is not proved.

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
put it there, and Step IV does not use it. Its consumers are Layers 5 and 7, the gap principle
of 3.7 — and, since 3.8, the core of Roth's proof itself, which bounds the size of each target by
its height with the fundamental inequality read at one place. Step IV still does not use it.
Now that 3.2 stands,
**3.5–3.8, 8.1, 8.3, 8.4, 8.5 and
the `w > 2` criterion of 7.4 are all within reach** (and the last of these is landed) — every
classical application of
Thue–Siegel–Roth,
including Thue–Mahler and the two-variable unit equation, is available before any geometry of
numbers; and with **3.4 landed**, the interface those applications actually consume — the
Subspace Theorem in two variables — is in place.

⚠ **3.3 is landed, and the four classical forms are proved** (four files). What it taught is
that this section's prediction — "the forms applications quote, each 3.2 for a choice of data" —
was right about three of the four and wrong about the fourth: *targets at infinity* is not a
choice of data but a **theorem**, with its own change of variable, its own distortion estimate
and its own use of the room in `κ > 2`, and the other three are choices of data *given it*. The
second thing it cost, and this section did not predict either, is the dictionary between the
finite places of `ℚ` and `padicNorm`: Mathlib has both ends and nothing between them, and the
exponent Ostrowski leaves free is exactly what Ridout's `2 + ε` cannot afford. The third is
smaller and sharper: the roadmap's own formula for the factor at `∞` is wrong at one point, and
`(max 1 |β|_v)⁻¹` is the junk-free form. Against that, Ridout's `2^{|S₁ ∩ S₂|}` split cost
nothing — it is a `Finset.powerset` and a case analysis on divisibility.

⚠ **3.4 is landed, in three files, and it cost less than this section expected.** The prediction
here — that it "needs 3.3's `OnePoint` form to split the solutions by which form is small at each
place" — was exactly right, and that split is the cheap part: a choice function on
`↥Sinf ⊕ ↥Sfin` and two `Function.extend`s. What the milestone actually cost is the local
comparison between the value of a linear form and the approximation factor at its zero, where the
constant has to grow with the target; and what it did not predict is that the conclusion is about
**points of `ℙ¹(K)` and not about `β ∈ K`** — the line at infinity is a solution of the
inequality for every `ε`, so it is forced into the exceptional set by the statement rather than
by the proof. The milestone's own sentence "with `β = x 1 / x 0`" is the right reading of the
proof and the wrong reading of the theorem.

⚠ **3.5 is landed, and it cost two files rather than the one this section implied.** The
prediction — that it is 3.3 for a choice of data — was right, and the choice of data is four
lines. What it did not predict is that the arithmetic *under* the choice is the work: Ridout's
two products are estimates in general and identities exactly when the index set is the set of
primes of the number itself, and nothing in Mathlib says so. The second thing it got wrong is
the orientation of the auxiliary rational, which decides whether `gcd(N, p^k)` has to be named.
Against that, the passage from the power of `p` that Ridout's theorem gives to the `exp(−ε k)`
of the statement cost one initial segment of `k` and nothing else.

⚠ **3.6 is landed, and it cost two files and a detour around the book's reduction.** The
prediction — the book's direct argument from the classical case of 3.3 — was right for an
irreducible form, and the approximation side is the one-place rational Roth theorem read for
unreduced fractions. What it did not say is that the book reaches an irreducible form by
factoring over `ℤ` first; run without that step, the exponent at the nearest root is `d / μ`,
which stays above `2` at irrational roots by an argument through the minimal polynomial and
**drops to `2` at rational ones**, where Liouville's inequality with exponent `1` takes over. And
it did not predict that Mathlib already has the binary form — `Polynomial.homogenize` — so that
the statement cost no definition.

⚠ **3.7 is landed, and it cost a restructuring of 3.2 rather than new mathematics.** The gap
principle is the book's proof, and the two counts are combinatorics that `Set.ncard` makes short.
What this section did not predict is that the count of large solutions cannot quote Roth's
theorem: it needs the chain statement inside 3.2's proof, with the parameters as functions of `κ`,
`|S|` and `[F : K]`, and 3.2 had them only as existentials inside one proof by contradiction. It
also found the book's window hypothesis one inequality too strict for the book's own use of it.

⚠ **3.8 is landed, and Layer 3 with it.** It cost a second restructuring of 3.2, smaller than
3.7's — Steps I to V generalized from one target per place to one per coordinate — and one fact
the book uses without naming: the size of a target is bounded by its height. The book's claim
that only the height of the auxiliary polynomial sees the targets is half right; the Taylor
expansion sees their sizes, and Layer 0.1's classification is what turns those into heights.

⚠ **4.1 is landed, the first milestone on the path to the summit.** It cost four files, two of
them infrastructure the milestone's text does not mention: a covolume for `𝓞 K`-modules that are
not ideals, and the value group of a finite place. It confirmed the roadmap's warning about the
book's finite-place volume, and it found that the index needs neither localization nor a quotient
— the maximal determinants at each place determine it.

⚠ **4.2 is landed, and it proves no geometry of numbers of its own, as
*[Consumed](#consumed)* said it would.** It cost two files, one fact Mathlib had — independence
over `ℚ` survives the mixed embedding — and one constant it had too, the house. What the
milestone's text did not predict is that the extraction lemma is spent twice, the second time to
show the `K`-minima finite at all, and that attaining them needs finiteness rather than Cassels'
greedy argument.

⚠ **4.3 is landed, in one file, and its lemma had to leave the book's proof by contradiction.**
Bombieri–Gubler state 7.5.12 along the heights of hypothetical solutions; stated for domains it is
eventual in the level, the rank can be `0`, and a bounded range of levels needs no Northcott. The
rank is read from the minima for any lattice and any closed body, and 4.2's attainment is what
reads it.

⚠ **4.4 is landed, in two files, and its constant had to become uniform in the forms.** The book
lets `C` depend on the forms and then applies the lemma to forms that move with `Q`; the proof
gives a constant depending on `K` and `n` only, and the statement now says so. Over `K` the moving
forms are not forms over `K`, so they became weights. The arithmetic input, approximation by
`S₀`-integers, needed no Chinese remainder theorem.

⚠ **4.5 is landed, in two files, and Layer 4 is complete.** The exterior power had to be read in
coordinates, so that 6.1 can apply Layers 4.2–5.6 inside it; Lemma 7.5.33 took the dual route and
no pairing; and `S(Q)` became an approximation domain whose exponents move with `Q`, whose weight
is computed exactly — the form 6.1 consumes, rather than the last minimum the book states.

⚠ **5.1 is landed, in two files, and Layer 5 has begun.** Its three reductions cost less than
expected — the unit normalization is one lattice approximation in the trace-zero hyperplane, and
Corollary 7.5.5 needed no independence of the forms — and what the milestone did not say is where
the classes come from: they are cells of a cube, not of 3.1's simplex, and the statement is
parametric in the solution rather than taken along an infinite sequence.

⚠ **5.2 is landed, in three files, and it cost less analysis and more algebra than the book
suggests.** The counting lost its volume computation entirely: the exponential moment of the
exponent of one variable is exact on the lattice, two binomial identities give it, and the book's
restriction `0 < λ ≤ n + 4` and most of its "sufficiently large `d`" go with the volume. What cost
more is the vanishing: `a(L v; J; I)` is not a multiple of `a(L v; J + I; 0)`, because the
derivatives are taken in one coordinate system and the expansion is read in another, so the
statement has to be proved by an induction on the order through the chain rule — and that
induction is where characteristic zero enters. Two smaller corrections: the hypothesis on `m` has
to be strict, or its constant raised, because the Chernoff error term is positive at every `d`;
and `η ≤ 2/(n+1)` is never used.

⚠ **5.3 is landed, in three files, and it is shorter than 5.2 because it is not analysis.** The
index along the forms looked like a new object and is not one: solving `M h = X (h, i₀ h)` for a
single coordinate turns the book's ideal into a monomial ideal, and the index becomes the
weighted order of 2.3 with a weight of `0` on every other variable — after which the valuation
properties are 2.3's and nothing has to be proved twice. What did cost something is the
specialization: the variables have to be killed one at a time, because a single slice at the
componentwise minimum of the exponents can be zero, and the coefficients of the forms have to be
truncated in step with them, or the index inequality comes out backwards. Two corrections to the
book: only the inequality between the indices is needed, not the equality it asserts; and its
`b_{j1} ≠ 0` is unnecessary, because the hypothesis on the heights passes to 2.7 whatever the
second coordinate is.

⚠ **5.4 is landed, in four files, and the book's statement of it is wrong in two places.** The
first is the inequality Step III rests on: Bombieri–Gubler bound the height of the single number
`L̂_{vi}(w)` by `h(V(Q)) + C₇`, which compares a scale-dependent quantity with a scale-invariant
one and is false; what is true, and what the proof needs, is a product-formula inequality between
the local factor of the Plücker point and its projective height, and it is stronger than what the
book extracts, by one power of the height. The second is the exceptional subspace: the book writes
"a linear space `W`", and its proof fixes one solution per **pattern** of surviving indices, a
pattern that moves with `Q`; the true statement has finitely many exceptional subspaces, one per
pattern, which is all Step IV consumes. The rest of 5.4 is shorter than it looks: the exceptional
system, read in the original coordinates, is an intersection of spans of coefficient vectors of
the forms, so no Hodge star, no adjugate and no cofactor expansion appears anywhere, and the
dictionary between "the wedge omitting `i` kills the Plücker point" and "the `i`-th coordinate of
the normal vector vanishes" is `ArithmeticHeights` 3.5 read at the ranks `n` and `1`.

⚠ **5.5 is landed, in two files, and it is elementary as promised — but not by the book's
argument.** Its one-variable core is a count of roots with multiplicity, because the book's
divisibility by a product of `2 B + 1` linear factors is, inside an induction on the variables, a
unique-factorization statement over a polynomial ring. Two things the book spends and 5.5 does
not: the chain rule for the parametrization, of which only the block degrees of the surviving
orders are used, and any commutation of a Hasse derivative past a substitution, which disappears
once the induction carries "does not vanish identically on the affine subspace" instead of the
substituted polynomial. What is left is one identity between two coefficient extractions from the
same shifted polynomial.

⚠ **5.6 is landed, in five files, and it needed no chain rule either.** Steps IV and VI assemble
5.2, 5.3, 5.4 and 5.5 into the finiteness of `{V(Q)}`, and **Layer 5 is complete**. The seam
between 5.3, which measures the index in the coordinates where the forms are the variables, and
5.5, which wants a derivative in the original ones, turned out to be a block-wise linear
substitution and nothing more: the third time in Layer 5 that the book's chain rule is replaced
by multihomogeneity. Two things the estimate needs that the book does not name: a *second*
invariant of the system of exponents, the weight of the absolute values `|c v i|`, which is what
the parameter `η` is measured against; and a single reference family carrying both the inverse
matrices of the forms and the integers of the grid, charged at exponent `2 |d|`. Bounded ranges
of `Q` the book leaves to the reader; they are covered by 5.4's upper bound, restated without its
hypothesis that `Q` be large, and Northcott for subspaces.

⚠ **6.1 is landed, in five files, and it is shorter than the book.** Steps VIII and IX turn the
geometry of numbers of Layer 4 and the penultimate-minimum theorem of Layer 5 into finitely many
proper subspaces covering every domain of large level, and **Layer 6 is begun**. Three things the
book spends and 6.1 does not: the pigeonhole along an unbounded family of levels, which a rounding
*function* with finite range replaces; the separate treatment of rank `n`, which is the case
`p = 1` of the exterior-power construction; and the bounded range of levels, which the parametric
statement never mentions. One thing it needs that no earlier layer states: the minima of a domain
lie between two fixed powers of the level, which is the product formula and not geometry of
numbers — Layer 4.2 bounds their product, and that is exactly the wrong direction at both ends.
And Lemma 7.5.33 had to become a function of the subspace, since finiteness travels back from the
exterior power as an image.

⚠ **6.2 is landed, in one file, and it is the summit over `K`.** The Subspace Theorem with
coefficients in the field — Schmidt's theorem in the `S`-adic form of Schlickewei — is 5.1 and 6.1
put together and nothing else: one theorem, in `…/SubspaceTheorem.lean`, which defines no object
and proves no lemma of its own. It is worth recording how little is left at this point, because it
is the opposite of what the length of Chapter 7 suggests. Two things were not what the prose says:
Northcott has to be applied on *projective* space, since the height is constant on a line and the
small-height solutions are therefore never finitely many — they contribute the lines they span,
which is also the only place where `n ≥ 1` does real work; and the normalizing scalar of 5.1 never
has to be undone, because a subspace is closed under scaling. **The path to the summit over `K` is
complete.**

⚠ **6.3 is landed, in four files, and it is the Subspace Theorem in the form its consumers
apply.** Points in `K`, coefficients in any finite extension `F` — and with it **the summit is
reached**. The layer is Remark 7.2.3 and nothing else: the Galois closure, an extension of the
chosen absolute value, and the conjugated systems at the places above each `v`. Three things the
book does not say. The transfer is an **equality**, not an estimate, and that is the whole reason
for the conjugates: a point of `Kⁿ⁺¹` is fixed by the Galois group, so it sees the same local
factor at every place above `v`, and the local degrees there sum to the same `[F' : K]` by which
the height grows. Conjugation and base change are the **same operation**, a ring homomorphism
applied to the coefficients, so neither a semilinear map nor a tensor product is needed — though
the survival of linear independence is a determinant statement and not a formal one. And Mathlib's
normalization of finite places means Layer 0.2's orbit statement is about the `(ef)`-th **root** of
a finite place, not about the place; the `ef` cancels afterwards against 0.2's own
`sum_localDegree`, exactly as `mult` does at the infinite places.

⚠ **6.4 is landed, in two files, and it is the summit in the shape Layer 8 quotes.** The affine
form costs one identity and no estimate: the `n + 1` local denominators that the affine inequality
drops are the `n + 1` copies of the height separating its exponent `−ε` from 6.3's `−n−1−ε`, so
the milestone is four lines on 6.3 once the factorization is written down. What the layer teaches
is where the two statements are *not* interchangeable. `S`-integrality is enough in one direction
only — the `S`-part of the height can exceed the height, which makes the affine inequality the
stronger of the two — and the converse has to scale to an `S`-primitive point, where 0.3 makes
them equal. That converse is proved here as well, so the library carries one Subspace Theorem and
not two; it costs more than the milestone does, and it consumes one thing from each of the three
layers below: 5.1's coordinate forms, 0.3's localization and 0.1's fibre.

⚠ **6.5 is landed, in two files, and it is the summit in the shape the deepest applications
want.** Vojta's refinement asks nothing new of the arithmetic: at a place where the forms are in
general position the `n + 1` smallest values come from a basis, the discarded ones are bounded
below because a basis bounds the coordinates, and dropping them costs a constant that halving `ε`
absorbs. What the layer teaches is that the two directions of the reduction are genuinely
different arguments — the ordering argument for a family with at least `n + 1` members, Steinitz
for a family with fewer — and that neither covers the other, because a family extended by the
coordinate forms is no longer in general position. 6.3 comes back out of 6.5 as the case of equal
sizes, and the recovery is `rfl` on the central quantity.

⚠ **6.6 is landed, in one file, and with it Layer 6 is complete.** It is the smallest milestone
of the roadmap and the only one whose central claim is an equation between theorems: 3.4 and 6.3
at `card ι = 2` are the same proposition, so the "converse" the section asked for needed nothing
at all, and what the file adds around that is the projective reading — a proper subspace of a
plane holds one point, so on `ℙ¹` the theorem counts solutions — and Roth's theorem over a number
field recovered from Layer 6. The library now carries three proofs of Roth's theorem and one
theorem.

⚠ **7.1 is landed, in two files, and it is the first thing the summit says about numbers.** The
Subspace Theorem is used exactly once — with `∑ α i X i` and the coordinate forms at the single
place `∞` — and everything else is an induction that eliminates one variable per proper subspace.
Three things the layer taught. The exponent `−(n+1) − ε` that 6.3 wants is reached from the
`−n − ε` that the statement gives by one inequality about integers, that the height of an integer
point is at most its sup norm; the same inequality makes the statement proved here stronger than
the book's, which reads the exponent against the sup norm rather than against the height. The
induction reserves no room, because the exponent weakens by exactly one when a variable is
dropped and the height only falls, so a single `ε` serves at every step. And the hypothesis is
`α j ≠ 0` for one index and never independence of the coefficients — the system is independent
exactly when the displaced coefficient is nonzero — while the *nonvanishing of the value* is not
decoration at all: on the diagonal `X 0 − X 1` vanishes and the count is infinite at every
exponent.

⚠ **7.2 is landed, in one file, and Layer 6 is not in it.** It consumes 7.1 as a black box, and
what it adds is three things the summit knows nothing about: the mean value theorem over `ℂ`,
which had to be proved again because there is no interval between two complex numbers and the
telescoping identity needs no analysis; Northcott's theorem for integer polynomials, which is
what removes the constant, since below the threshold height it is the *polynomials* that are
finite and not the numbers they name; and the rigidity of a minimal polynomial, which both makes
`H(f_ξ)` a function of `ξ` — so that the existential the statement quantifies over is the book's
height — and disposes of the conjugates of `α`, the one family 7.1 cannot see. Read in Layer
1.3's language the milestone is `w_D^*(α) ≤ D`, so half of 7.3's upper bound came with it.

⚠ **7.3 is landed, in three files, and one of them is a second visit to Layer 6.** The exponent
identity `w_n = w_n^* = min n (deg α − 1)` cost almost nothing beyond 7.2 — the one missing
bound is 7.2's proof with its first step deleted, and the rest is 1.3 assembled — but Schmidt's
two theorems on simultaneous approximation did: their exponents are read against the product
`∏ |q_i|`, which 7.1's appeal to the Subspace Theorem throws away, so the appeal had to be made
again, with the hypothesis on the bare product of the values of a full system of forms. What
came back is a statement of Layer 6 that 7.1 never needed and that 7.4 wanted:
`Rat.exists_finset_submodule_of_prod_le`.

⚠ **7.4 is landed, in four files, and the Subspace Theorem is in one of them.** The criterion for
stammering sequences needed 7.3's step with finite places added — the primes of the base, where
the repetition's gain lives — and then no induction at all: one subspace containing infinitely
many points decides, and non-periodicity enters only as irrationality. The `w > 2` criterion came
with it, from Ridout's theorem and nothing above Layer 3.

⚠ **7.5 is landed, in two files, and Layer 7 is complete.** The complexity theorem is 7.4's
working form behind a pigeonhole on the factors of length `n`; the one new idea is to cut the
repetition at a multiple of its period near `n / 2`, which removes the classical case split.
Morse–Hedlund came with it, over any finite alphabet.

⚠ **8.1 is landed, in one file, and it rests on Vojta's refinement.** The two-variable unit
equation needed neither the split by largest coordinate nor the affine form: 6.5 with three forms
at every place gives the central quantity `H ^ (-3)` exactly.

⚠ **8.2 is landed, in one file, and it is 8.1 in `n` variables plus an induction.** With the
forms `X i` and `∑ i, X i` the central quantity is `H ^ (-n - 1)` exactly; the induction needs
two steps, a minimal subsum and then one fixed coordinate.

⚠ **8.3 is landed, in one file, and it is 8.1 once per triangle.** Connectivity makes every ratio
of two forms take finitely many values; the unit version keeps its `S`-unit scaling because an
`E`-th power that is a unit has a unit root, with no discreteness of valuations; the passage to
an extension is moved to 8.4. **Layers 6 and 7 are complete**, and of Layer 8, 8.1–8.4 are
landed.

⚠ **8.4 is landed, in two files, and it is 8.3 in the splitting field.** At least three pairwise
non-proportional binary forms are triangularly connected by Cramer's rule; the passage to the
primes above `S` is one short file; the unit version descends because a scalar relating two
`K`-points is itself in `K`; Thue–Mahler over `ℚ` adds only Bézout.

The path to the summit was Layer 4 → Layer 5 → 6.1 → 6.2 → 6.3 → 6.4 → 6.5 → 6.6, and **it is
walked to the end**; the first five steps down the other side are 7.1–7.5, and all five are
taken.
Layer 4 needed `ArithmeticHeights` 4.1–4.4, 3.1 and 3.4, and was independent of Layers 2 and 3
here. Within Layer 5, 5.2 and 5.3 were Layer 2 in multihomogeneous dress, 5.5 was elementary and
5.6 was bookkeeping over the four before it; **5.4 was the delicate one**, and its statement did
turn out to be easy to get wrong — the book's is, in two places (see 5.4). 6.1 was where Layers 4
and 5 met, and it cost five files of which only one knows what a wedge is; 6.2 cost one, and the
five layers below it carry all of its content; 6.3 cost four, of which two are about places and
one is about linear algebra, and only the last is about the Subspace Theorem; 6.4 cost two, and
the larger half of the second file is the converse that no consumer has to use; 6.5 cost two, of
which the first knows nothing about number fields at all; and 6.6 cost one, which proves no new
mathematics and checks that the two ends of the roadmap meet. 7.1 cost two, of which the second
knows nothing about places or heights beyond one monotonicity; 7.2 cost one, which names a place
in two lines and nowhere else; and 7.3 cost three, of which one is a second appeal to 6.3, one is
two inductions with no place in them and one is Layer 1.3 assembled; and 7.4 cost four, of
which one is words, one is digits, one is a third appeal to 6.3 and the first with finite places,
and one is a single subspace and two cases; and 7.5 cost two, of which one is words and the
other thirty lines; and 8.1 cost one, a single appeal to 6.5 with no case split; and 8.2 cost
one, the same appeal with `n + 1` forms and an induction around it; and 8.3 cost one, 8.1 once
per triangle and valuations for the rest; and 8.4 cost two, of which the first is the passage to
an extension and the second 8.3 in the splitting field. Remaining: 8.5–8.7 — 8.5, which stands on
8.1 and will quote 8.4's passage to an extension, 8.6, which stands on 8.2's Corollary 7.4.3, and
8.7 on the Subspace path.

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
of Layer 2 and all of Layer 3 — **Roth's theorem, the classical forms of it that the
applications quote, the Subspace Theorem in two variables, Mahler's theorem on `(p/q)^k`,
Thue's theorem, the count of approximations and Roth's theorem with moving targets** — and
the approximation domains, the successive minima over `K`, the rank, Evertse's lemma and the
exterior powers — all of Layer 4 — and the reductions of 5.1 are proved in this repository and
nothing else of Layers 5–9 is. What
exists elsewhere, in
[`rwst/lean-code`](https://github.com/rwst/lean-code)
(CC0), is the *other side* of the interface — statements of the Subspace Theorem recorded as
cited axioms, and sorry-free derivations of consequences from them — and it is useful in two
ways.

- As **consumers to test the pinned statements against**: `CITED/Ridout.lean`
  (`Ridout.finite_ratios` and its algebraic-multiplier form, a Ridout-type theorem derived from
  the two-variable Subspace Theorem — an instance of 3.3–3.4; ⚠ **3.4 is now landed here, and
  it is the theorem that file takes as an axiom**: `Ridout.finite_ratios` is the *projective*
  form, two linearly independent forms at each place and finiteness of the set of ratios, which
  is 3.4 and not 3.3 — its own docstring records that its `ℚ`-linear forms exclude the algebraic
  irrational targets 3.3 handles, and `finite_ratios_alg` is the `K`-linear form, which is 3.4
  over a general `F`. What still separates them is the **convention, not the mathematics**: that
  file quantifies over an untyped `S : Finset (AbsoluteValue ℚ ℝ)`, which the first example under
  *Conventions* above refutes, and it concludes with the finite set of *ratios* where 3.4
  concludes with the finite set of lines — the fifteen lines that pass between the two are in
  that file already), `CITED/CorvajaZannierProof.lean`
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
