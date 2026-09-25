# Subspace-Theorems

A working repository for **two roadmaps**, one standing on the other.

- The **`ArithmeticHeights` roadmap** — arithmetic heights of polynomials, matrices and linear
  subspaces, Northcott and Kronecker, successive minima, Siegel's lemma and Bombieri–Vaaler. The
  roadmap is [`ArithmeticHeights/README.md`](ArithmeticHeights/README.md); **all six of its layers
  are landed**.
- The **`DiophantineApproximation` roadmap** — approximation exponents, the Roth machinery, Roth's
  theorem, the geometry of numbers of parallelepipeds, the **Subspace Theorem**, and the unit and
  decomposable-form equations it exists to prove. The roadmap is
  [`DiophantineApproximation/README.md`](DiophantineApproximation/README.md); it consumes the first
  one by milestone number and rebuilds none of it.

The suggested Lean signatures for the milestones most likely to drift are
[`Roadmap/Suggested.lean`](Roadmap/Suggested.lean), which also indexes the milestones already
landed — each stated in its delivered form and discharged by the library declaration that carries
it. ⚠ As the tree stands `Suggested.lean` prototypes the **`DiophantineApproximation`** roadmap;
the `ArithmeticHeights` signatures it used to carry were retired when that roadmap finished.

The work is being done **here rather than in [Tau Ceti](https://github.com/TauCetiProject/TauCeti),
ahead of it, because nothing proceeds there.** The intent is nevertheless that what lands here is
Tau Ceti material: the implementation adheres to Tau Ceti's principles (see below), so that moving a
finished file into `TauCeti/NumberTheory/Height/` or
`TauCeti/NumberTheory/DiophantineApproximation/` is a path change and an import fix, not a
rewrite.
`ArithmeticHeights/Arakelov.lean` is written that way already — Apache header, `module`,
`public import`, module docstring with `## Main definitions` / `## Main results` /
`## Implementation notes` / `## References`, closing with its roadmap layer ("This is Layer 0.1 of
the `ArithmeticHeights` roadmap"), sorry-free.

## ⚠ The roadmap is preliminary

**Neither `ArithmeticHeights/README.md` nor `DiophantineApproximation/README.md` has finished
review.** Treat both as draft specifications:

- Milestone **names and shapes may still change**, including ones already implemented here.
  `Suggested.lean` says so itself: it "is not the roadmap and is not exhaustive", and exists
  precisely for the statements whose shapes are most likely to drift.
- Do not treat a signature in `Suggested.lean` as settled API. Open milestones there are stated
  with `sorry` and elaborate against the pinned Mathlib — 2 of them as the tree stands, Wirsing's
  first two inequalities of Layer 1.3 and Layers 1.4 to 8 of the `DiophantineApproximation`
  roadmap except the whole of Layers 2, 3, 4, 5, 6, 7 and 8, Wirsing's
  first two
  and 1.4 marked **optional** there because no later layer consumes them —
  and the sorry-free version is what has
  to be right. The landed ones are `example`s proved by the library, so they record what is true
  today rather than what will stay true: a rename upstream in this repo breaks them, which is the
  point.
- Expect re-shaping when review lands — especially in the layers that depend on choices review is
  most likely to touch: the Arakelov vs. sup-norm normalisation and the relative/absolute split
  (Layer 0), the Plücker indexing and the `Module.Grassmannian` question (Layer 3), and the
  constants in Layers 5.3–5.4.
- Anything built here should therefore keep the *mathematics* separable from the *naming*: prove
  the statement, keep the docstring citing the book (Bombieri–Gubler, Bombieri–Vaaler), and accept
  that the identifier may be renamed on the way into Tau Ceti.

## Tau Ceti principles this repo follows

From `~/math/TauCeti/AGENTS.md`, its `lakefile.toml`, and its CI. Everything marked ✅ is enforced
mechanically by `scripts/check.sh`, not by good intentions; the last three are judgement calls that
no script can make.

- ✅ **No `sorry`, and no axioms beyond `propext`, `Classical.choice`, `Quot.sound`** — hence no
  `native_decide` — in any file that is meant to become Tau Ceti code. `Roadmap/Suggested.lean`
  is exempt: it is a human-owned target file, not library code, and not a default build target.
- ✅ **No `set_option`** in library source: it is an escape hatch for `maxHeartbeats`, linters and
  `maxRecDepth`.
- ✅ **Mathlib's standard linter set with `warningAsError`** and a 1500-line file ceiling, plus the
  text-based and environment linters. (Upstream also holds a *newly added* file to 1000 lines, in a
  CI step that needs a diff; that one is not reproduced here.)
- ✅ **Every file opts into the Lean module system**: a leading `module`, `public import` for
  imports whose contents appear in the file's public API, plain `import` otherwise, and a
  `public section`.
- ✅ **Copyright header** in Mathlib's format (`Copyright (c) 2026 … Released under Apache 2.0
  license as described in the file LICENSE. / Authors: …`).
- ✅ **Fine-grained Mathlib imports, never `import Mathlib`.** And declarations go into
  Mathlib's root namespaces, never inside a `namespace ArithmeticHeights`.
- **Defer to Mathlib's design decisions**; consume Mathlib by name and rebuild nothing it already
  has. Track Mathlib `master`; bumps are forward-only.
- **No backwards-compatibility surface**: no aliases, forwarding modules, or deprecated shims. When
  something is renamed or superseded, update every use and delete the old name in the same change.
- **Improving existing code is always in scope**; adding *new* mathematics is gated by the roadmap.

## The gates, and the Tau Ceti machinery behind them

Seven gates run over both libraries — the build itself plus six scripts — nearly all adapted from
Tau
Ceti and living in `scripts/`. `scripts/check.sh` runs the lot in one round; `--quick` skips the
four that need a build. What each catches, what was changed in adapting it, and what was
deliberately **not** ported (upstream's 900-line `lint-env.sh`, its dot-notation lint, the
mathlib-shim expiry check) is recorded in [`scripts/PROVENANCE.md`](scripts/PROVENANCE.md).

Beside them sit two local, **gitignored** reference copies, taken from `~/math/TauCeti` at commit
`37ae92f8170796e94b66279ea66f8635d9ca2aa0` on 2026-09-15:

- the part of `scripts/` not yet adapted — `lean_source.py`, `lint-dot-notation.py` and its
  baseline, `lint-baseline.txt`, `lint-nolints-allowlist.txt`, `check-expired-mathlib-shims.py`
  (`.gitignore` names them one by one, so anything else added to `scripts/` is tracked by default);
- **`TauCeti/`** — the contract and configuration, for reading only: `AGENTS.md`, `lakefile.toml`,
  `formalization.yaml`, `mathlib-shims.json`, `.github/workflows/ci.yml`, `docbuild/`, at their
  upstream paths. See `TauCeti/PROVENANCE.md`.

A fresh clone has neither, so **nothing tracked may point into them**. Adopting a file means
adapting it — each hard-codes the single library root `TauCeti`, where this repository has two,
`ArithmeticHeights` and `DiophantineApproximation`, listed once in `scripts/source-modules.sh` —
un-ignoring it, and committing the result with a header saying what it came from.

## Layout and building

```
ArithmeticHeights/      a library: sorry-free Lean, Tau Ceti rules, a default build target
  Absolute.lean          Layer 0.4
  AdaptedBasis.lean      Layers 4.2 and 4.6 (infrastructure)
  Affine.lean            Layer 0.5
  Arakelov.lean          Layers 0.1 and 0.2
  AuxiliaryPolynomial.lean Layer 5.7
  BombieriVaaler.lean    Layer 5.2
  BombieriVaalerEntries.lean Layer 5.5
  BombieriVaalerField.lean Layer 5.3
  BombieriVaalerMaxNorm.lean Layer 5.4
  BombieriVaalerRelative.lean Layer 5.6
  CauchyBinet.lean       Layer 3.4
  CubeSlicing.lean       Layer 4.5
  Duality.lean           Layer 3.5
  Extension.lean         Layer 0.3
  Extraction.lean        Layer 4.4
  FinitePlaceIdeal.lean  Layer 4.3 (infrastructure)
  GaussLemma.lean        Layer 2.2
  GaussMeasure.lean      Layer 4.5 (infrastructure)
  Gelfond.lean           Layer 2.3
  GramCovolume.lean      Layer 4.3 (infrastructure)
  Hadamard.lean          Layer 3.4
  Kronecker.lean         Layer 1.4
  Laplace.lean           Layer 3.6
  LinearForm.lean        Layer 2.4
  LogConcave.lean        Layer 4.5 (infrastructure)
  LowerBound.lean        Layer 1.5
  MahlerMeasure.lean     Layer 1.2
  Matrix.lean            Layer 2.5
  MinimaBasis.lean       Layer 4.6
  MinkowskiSecond.lean   Layer 4.2
  MixedBall.lean         Layer 5.3 (infrastructure)
  MixedCube.lean         Layer 5.4 (infrastructure)
  MixedLattice.lean      Layer 4.3 (infrastructure)
  MonomialIndex.lean     Layer 5.7 (infrastructure)
  Nonarchimedean.lean    Layer 3.6
  NormProd.lean          Layer 4.3 (infrastructure)
  Northcott.lean         Layer 1.1
  NorthcottSubspace.lean Layer 3.7
  NorthcottTheorem.lean  Layer 1.3
  NumberFieldLattice.lean Layer 4.3 (over a number field)
  Plucker.lean           Layer 3.1
  Polynomial.lean        Layer 2.1
  PrekopaLeindler.lean   Layer 4.5 (infrastructure)
  ProductOfBalls.lean    Layer 4.5 (infrastructure)
  PseudoBasis.lean       Layer 4.3 (infrastructure)
  QuotientFubini.lean    Layer 4.2 (infrastructure)
  RationalLattice.lean   Layer 4.3 (over `ℚ`)
  Regulator.lean         Layer 6.3
  RestrictScalars.lean   Layer 5.6 (infrastructure)
  RowEntryHeight.lean    Layer 5.5 (infrastructure)
  RowSpace.lean          Layer 3.3
  Siegel.lean            Layer 5.1
  SliceBound.lean        Layer 4.5 (infrastructure)
  SRegulator.lean        Layer 6.5
  Submodular.lean        Layer 3.6
  Subspace.lean          Layer 3.2
  SuccessiveMinima.lean  Layer 4.1
  SUnit.lean             Layer 6.4
  SUnitTheorem.lean      Layer 6.5
  UnitHeight.lean        Layer 6.1
  UnitTorsion.lean       Layer 6.2
  README.md              the roadmap (prose)
DiophantineApproximation/  the second library, same rules, also a default build target
  ConjugatePlaces.lean   Layer 0.2 (the Galois action, transitive on each fibre)
  FundamentalInequality.lean Layer 0.4 (the local factors of one element of one field)
  IrreducibleExponent.lean Layer 1.2 (Gelfond over Z; w_n is unchanged by irreducibility)
  IrrationalityExponent.lean Layer 1.1 (the exponent; Dirichlet, Liouville numbers, Moebius)
  KoksmaMobius.lean      Layer 1.2 (Moebius invariance of Koksma's exponent)
  LiouvilleExponent.lean Layer 1.1 (Liouville's theorem as a bound on the exponent)
  LiouvilleInequality.lean Layer 0.4 (Liouville over an extension; Liouville's theorem over R)
  LocalExtension.lean    Layer 0.2 (the local extension formula, both halves)
  Nonarchimedean.lean    Layer 0.1 (infrastructure Mathlib lacks)
  PlacesOver.lean        Layer 0.1
  MahlerExponent.lean    Layer 1.2 (w_n and w_n*; degree one, primitive, Moebius)
  PlacesOverFinite.lean  Layer 0.1 (nonarchimedean half)
  PolynomialSupNorm.lean Layer 1.2 (the naive height; Northcott for integer polynomials)
  AlgebraicExponent.lean Layer 1.3 (Liouville for a polynomial value; w_n <= d - 1)
  BoxPrinciple.lean      Layer 1.3 (Dirichlet's box principle; n <= w_n)
  KoksmaComparison.lean  Layer 1.3 (w_n* <= w_n; the minimal polynomial is rigid)
  PolynomialEval.lean    Layer 1.3 (archimedean bounds on a polynomial and its increment)
  RootLocation.lean      Layer 1.3 (where the complex roots are; Mahler measure)
  SimultaneousBox.lean   Layer 1.3 (the box principle at several points at once)
  WirsingSystem.lean     Layer 1.3 (Wirsing's test points and the real root they carry)
  WirsingThird.lean      Layer 1.3 (Wirsing's third inequality; at w_n = n it is his conjecture)
  MvHasseDeriv.lean      Layer 2.1 (Hasse derivatives in several variables; Bombieri-Gubler 6.1)
  MvHasseDerivTaylor.lean Layer 2.1 (the substitution formula, Leibniz and Taylor)
  MvHasseDerivHeight.lean Layer 2.1 (the size of a derivative at one absolute value)
  DisjointVariables.lean Layer 2.2 (heights in disjoint variables; Bombieri-Gubler Prop. 1.6.2)
  WeightedOrder.lean     Layer 2.3 (the least weight of a monomial; additive on products)
  PolynomialIndex.lean   Layer 2.3 (the index at a point; Bombieri-Gubler 6.3.2)
  Wronskian.lean         Layer 2.4 (the Wronskian of n polynomials in one variable)
  GeneralizedWronskian.lean Layer 2.4 (the criterion in several variables; BG Prop. 6.3.10)
  CountingVolume.lean    Layer 2.5 (lattice points, volume and two exponential tails)
  BoxMonomial.lean       Layer 2.6 (coefficients on the box of bounded partial degrees)
  MonomialHeight.lean    Layer 2.6 (the height of one condition row)
  IndexConditions.lean   Layer 2.6 (the index as a finite linear system, and its count)
  AuxiliaryPolynomial.lean Layer 2.6 (the index theorem; Bombieri-Gubler Lemma 6.3.4)
  HeightTransport.lean   Layer 2.7 (local factors to heights, one-sided at the finite places)
  IndexRename.lean       Layer 2.7 (derivative, index and degree under an injective renaming)
  PolynomialDeterminantHeight.lean Layer 2.7 (the height of a determinant of polynomials)
  RothDecomposition.lean Layer 2.7 (the tensor decomposition and the two Wronskians)
  RothDeterminant.lean   Layer 2.7 (degree, height and index of the matrix of derivatives)
  RothBaseCase.lean      Layer 2.7 (Roth's lemma in one variable; BG Lemma 6.3.9)
  RothEstimates.lean     Layer 2.7 (the three elementary estimates behind the induction)
  RothLemma.lean         Layer 2.7 (Roth's lemma; Bombieri-Gubler Lemma 6.3.7)
  ApproximationClass.lean Layer 3.1 (Mahler's reduction: the cells of the unit simplex)
  IndependentHeights.lean Layer 3.1 ((L, M)-independent sequences, by Northcott)
  GlobalBound.lean       Layer 3.2 (the product formula against local upper bounds; Step IV)
  MvPolynomialEvalBound.lean Layer 3.2 (local bounds on a value, trivial and by Taylor)
  RothLocalBound.lean    Layer 3.2 (that bound in the base field, along LiesOver)
  RothClass.lean         Layer 3.2 (Step 0: Layer 3.1 in the form the proof quotes)
  RothKeyInequality.lean Layer 3.2 (Steps III-V at a fixed multidegree)
  RothAuxiliary.lean     Layer 3.2 (Steps I-II: the polynomial and its derivative)
  RothTheorem.lean       Layer 3.2 (Roth's theorem; Bombieri-Gubler Theorem 6.4.1)
  RationalPlaces.lean    Layer 3.3 (the places of Q: every finite one is a p-adic norm)
  RothInfinity.lean      Layer 3.3 (targets in OnePoint F; the Moebius change of variable)
  RothRational.lean      Layer 3.3 (Roth over Q; the irrationality exponent is 2)
  Ridout.lean            Layer 3.3 (Ridout's theorem and the p-adic form; BG 6.2.4, 6.2.6)
  ProjectiveTarget.lean  Layer 3.4 (the zero of a linear form as a target in OnePoint F)
  ApproxProd.lean        Layer 3.4 (the central quantity of the Subspace Theorem)
  RothProjective.lean    Layer 3.4 (Roth on the projective line; BG Thm 7.2.2 at n = 1)
  PrimeProducts.lean     Layer 3.5 (the primes of an integer; the finite product formula)
  MahlerPowers.lean      Layer 3.5 (Mahler's theorem on (p/q)^k; BG 6.2.7; Mahler 1957)
  BinaryForm.lean        Layer 3.6 (binary forms, their complex roots, the multiplicity bound)
  ThueEquation.lean      Layer 3.6 (Thue's theorem; BG 6.2.1; Thue 1909)
  GapPrinciple.lean      Layer 3.7 (the strong gap principle; approximation classes; BG 6.5.4)
  CountingApproximations.lean Layer 3.7 (the count in a window and of large solutions; BG 6.5.6-7)
  RothIntervals.lean     Layer 3.7 for N = 2 (Roth's large solutions in few height intervals)
  RothSubspaceCount.lean Layers 3.7 → 9.4 (2-variable normalized systems via Roth's intervals)
  MovingTargets.lean     Layer 3.8 (Roth's theorem with moving targets; BG 6.5.2; Vojta)
  FinitePlaceValues.lean Layer 4.1 (the value group of a finite place; approximation at places)
  ModuleCovolume.lean    Layer 4.1 (the covolume of an 𝓞 K-module, from maximal determinants)
  ApproximationDomain.lean Layer 4.1 (approximation domains as Λ ∩ B; the covolume; BG 7.5.6-7)
  ApproximationVolume.lean Layer 4.1 (the volume of the body; vol / covol against Q^weight; 7.5.8)
  FieldMinima.lean       Layer 4.2 (successive minima over K; attained; against the real minima)
  FieldMinkowski.lean    Layer 4.2 (Minkowski's second theorem over K; BG C.2.11; for domains)
  ApproximationRank.lean Layer 4.3 (V(Q) and its rank; the rank drops for large Q; BG 7.5.11-12)
  SIntegerApproximation.lean Layer 4.4 (simultaneous approximation by S-integers, no completions)
  EvertseLemma.lean      Layer 4.4 (Evertse's lemma, with weights; BG 7.5.29)
  WedgeForm.lean         Layer 4.5 (wedges of forms in Plücker coordinates; Laplace; BG 7.5.33)
  WedgeDomain.lean       Layer 4.5 (the wedge domain S(Q); its weight; BG 7.5.30-31)
  UnitNormalization.lean Layer 5.1 (primitive points, the unit multiple, (7.19); BG 7.2.6, 7.5.4-5)
  SubspaceReduction.lean Layer 5.1 (the approximation classes; the reduction whole; BG 7.5.6)
  MultiHomogeneous.lean  Layer 5.2 (multidegrees, the block substitution, the chain rule; BG 7.5.14)
  MonomialDeviation.lean Layer 5.2 (how many monomials have a small exponent; Chernoff over blocks)
  SubspaceAuxiliary.lean Layer 5.2 (heights and Siegel for the auxiliary polynomial; BG 7.5.15)
  FormIndex.lean         Layer 5.3 (the index along linear forms; BG Def. 7.5.17)
  FormSpecialization.lean Layer 5.3 (specializing a block to two coordinates; dehomogenization)
  GeneralizedRothLemma.lean Layer 5.3 (the generalized Roth lemma; BG 7.5.19)
  LinearFormValue.lean   Layer 5.4 (Liouville for the value of a linear form; BG (1.8))
  SubspaceNormal.lean    Layer 5.4 (the normal vector of a hyperplane; transformed minors)
  SubspaceHeightBounds.lean Layer 5.4 (the two bounds on the height of V(Q); BG 7.5.21)
  ExceptionalSubspace.lean Layer 5.4 (the patterns and the exceptional subspaces; BG 7.5.21)
  PolynomialGrid.lean    Layer 5.5 (the grid lemma, one variable at a time; BG 7.5.24)
  SmallPoint.lean        Layer 5.5 (the parametrization and the small point; BG 7.5.25)
  LogComparison.lean     Layer 5.6 (one elementary comparison of logarithms, shared with Roth)
  FormIndexSubspace.lean Layer 5.6 (from the index along the forms to a surviving derivative)
  SubspaceValueBound.lean Layer 5.6 (the local bound on a derivative at a small point)
  SubspaceKeyInequality.lean Layer 5.6 (Step VI: the product formula against the local bounds)
  PenultimateMinimum.lean Layer 5.6 (Steps IV and VI; the penultimate minimum; BG 7.5.13)
  WedgeRecovery.lean     Layer 6.1 (Lemma 7.5.33 as a function of the subspace)
  MinimaBounds.lean      Layer 6.1 (the minima between two powers of the level)
  ExponentGrid.lean      Layer 6.1 (systems of exponents on a grid)
  WedgeExponentBound.lean Layer 6.1 (the box and the negative weight of the wedge exponents)
  ParametricSubspace.lean Layer 6.1 (Steps VIII and IX; the parametric Subspace Theorem)
  SubspaceTheorem.lean   Layer 6.2 (the Subspace Theorem over K; BG 7.2.2 with F = K)
  FormBaseChange.lean    Layer 6.3 (a linear form carried along a ring homomorphism)
  PlaceConjugation.lean  Layer 6.3 (the places of a Galois extension as conjugates)
  ExtensionApproxProd.lean Layer 6.3 (the conjugated systems and the transfer identity)
  SubspaceAlgebraic.lean Layer 6.3 (the Subspace Theorem with algebraic coefficients)
  AffineProd.lean        Layer 6.4 (the affine quantity; its dictionary with approxProd)
  SubspaceAffine.lean    Layer 6.4 (the Subspace Theorem for S-integral points; BG 7.2.5)
  GeneralPosition.lean   Layer 6.5 (general position; which n+1 forms to keep at a point)
  SubspaceGeneralPosition.lean Layer 6.5 (Vojta's refinement; BG 7.2.9)
  SubspaceConsistency.lean Layer 6.6 (on P^1 the Subspace Theorem is Roth's theorem)
  LinearFormSubspaces.lean Layer 7.1 (one linear form: the exceptional subspaces)
  OneLinearForm.lean     Layer 7.1 (one linear form with algebraic coefficients; BG 7.3.2)
  BoundedDegreeApproximation.lean Layer 7.2 (algebraic numbers of bounded degree; BG Cor. 7.3.5)
  SchmidtExponents.lean  Layer 7.3 (the exponents of an algebraic number; Schmidt 1970)
  SimultaneousSubspaces.lean Layer 7.3 (two systems of forms: the exceptional subspaces)
  SimultaneousApproximation.lean Layer 7.3 (simultaneous approximation; BG Remark 7.3.4)
  StammeringWords.lean   Layer 7.4 (V^w for real w, stammering sequences)
  DigitExpansions.lean   Layer 7.4 (expansions in an integer base: repetitions, irrationality)
  RepetitionSubspaces.lean Layer 7.4 (the Subspace Theorem at the primes of the base)
  TranscendenceCriterion.lean Layer 7.4 (stammering ⟹ transcendental; ABL 2004, AB 2007, FM 1997)
  FactorComplexity.lean  Layer 7.5 (complexity, Morse–Hedlund, the pigeonhole lemma)
  ComplexityTranscendence.lean Layer 7.5 (algebraic irrational ⟹ p(n)/n → ∞; AB 2007 Thm 1)
  UnitEquation.lean      Layer 8.1 (a x + b y = 1 in S-units: finitely many; via Vojta 6.5)
  UnitEquationSeveral.lean Layer 8.2 (∑ a i x i = 1, no vanishing subsum: finitely many; BG 7.4.2–3)
  DecomposableForm.lean  Layer 8.3 (triangularly connected decomposable forms; Győry–Papp, via 8.1)
  SIntegerExtension.lean Layer 8.4 (S-integers and S-units above S in an extension)
  ThueMahler.lean        Layer 8.4 (Thue and Thue–Mahler over a number field, via 8.3)
  SIntegerSquares.lean   Layer 8.5 (S-units modulo squares; coprime factors of a square)
  Hyperelliptic.lean     Layer 8.5 (b y² = f(x): finitely many; Siegel 1926, via 8.1)
  NormForm.lean          Layer 8.6 (norm-form equations; Schmidt 1971–72, via 8.2's Cor. 7.4.3)
  GcdBound.lean          Layer 8.7 (gcd(u − 1, v − 1) for S-units; Corvaja–Zannier, via 6.4)
  SubspaceSystem.lean    Layer 9.1 (Evertse's systems of inequalities; Theorem A, via 6.4)
  SubspaceGap.lean       Layer 9.2 (Evertse's gap principle, Prop. 4.1; one determinant)
  DetPartition.lean      Layer 9.3 (Evertse's Lemma 4.3: classes of small determinant in ℂⁿ)
  SubspaceSmall.lean     Layer 9.3 (second gap principle, Prop. 4.2; small solutions, Thm 2.2)
  DetCount.lean          Layer 9.3 (Evertse's Lemmas 4.4–4.5: few subspaces for small dets over ℚ)
  SubspaceIntervals.lean Layer 9.4 (Evertse, proof of Thm 2.1: from intervals to subspaces)
  PlacesOverInfinite.lean Layer 0.1 (archimedean half)
  SAdicHeight.lean       Layer 0.3 (heights of S-integral and primitive points)
  SIntegerLocalization.lean Layer 0.3 (the S-integers as a localization; BG Prop. 5.3.6)
  README.md              the roadmap (prose)
Roadmap/
  Suggested.lean        the roadmap's target signatures: sorry-allowed, NOT a default target;
                        imports the library, so the landed milestones are checked against it
scripts/                the gates (see scripts/PROVENANCE.md); a few ignored reference copies;
                        make-challenge.py generates the comparator statements of record
Challenge.lean, Challenge/  comparator's statements of record, one module per owning module:
                        generated, sorry-proved, NOT a default target (see COMPARATOR.md)
ChallengeFlat.lean      the same statements in one Mathlib-only file, Palomar's shape
Solution.lean           the development re-exported for comparator
comparator/             theorems.txt (the certified list) and the two configs `lake test` runs
COMPARATOR.md           what `lake test` certifies, how to regenerate it, and why it looks so
formalization.yaml      Palomar's metadata for the std3-flat submission (draft)
TauCeti/                [gitignored] Tau Ceti's contract and configuration, verbatim, to read
*.pdf                   [gitignored] literature (Bombieri–Gubler)
```

```bash
lake exe cache get          # Mathlib oleans
scripts/check.sh            # every gate, in one round
scripts/check.sh --quick    # only the gates that need no build
lake build Roadmap          # optional: check the target signatures still elaborate, and that
                            # the landed milestones still match the library
lake test                   # optional: comparator certifies Siegel, Roth and the Subspace
                            # Theorem against Challenge and ChallengeFlat (see COMPARATOR.md)
```

`check.sh` runs, cheapest first: the four textual **guards**; **`lint-style.sh`** (copyright
headers + Mathlib's text-based linters); the **build**, which is itself a gate, since the library
target sets `warningAsError` over Mathlib's syntax linter set; **`lake exe axioms`**;
**`lake exe module-system`**; and **`lint-env.sh`** (`#lint`). A failing gate does not stop the
run, so one round shows everything that is wrong.

`lake build` never touches `Roadmap/`: that library is declared without `@[default_target]`
precisely so that any `sorry` it carries — the milestones not yet built — stays out of the
libraries' build and out of every gate. As the tree stands it carries **6**: Wirsing's first two
inequalities of Layer 1.3, the optional Layer 1.4, and the milestones prototyped from Layer 7.2
to Layer 8 of the `DiophantineApproximation` roadmap. Layer 0,
1.1–1.3, all of Layers 2, 3, 4, 5 and 6, and Layer 7.1 are landed and appear there as
`example`s
discharged by the library. The dependency runs one way only, `Roadmap` on the
libraries, and `guards.sh` fails the build if a library ever imports the roadmap.

Every gate was tested against a violation, not only against a clean tree — a `sorry`, a 101-column
line, trailing whitespace, a wrong licence line, an undocumented `def`, a home-rolled `axiom`, a
file without `module`, each caught by exactly one gate. Every gate reads both library roots; the
single list of them is `LIBRARY_ROOTS` in `scripts/source-modules.sh`, and adding a roadmap to this
repository means adding its directory there and to `lakefile.lean` and nothing else. On the tree as
it stands: 203 library files, 5048 declarations audited and all within the allowlist, 3114 judged
by 15 environment linters with no violations, headers and text linters clean.

