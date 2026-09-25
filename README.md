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
scripts/                the gates (see scripts/PROVENANCE.md); a few ignored reference copies
TauCeti/                [gitignored] Tau Ceti's contract and configuration, verbatim, to read
*.pdf                   [gitignored] literature (Bombieri–Gubler)
```

```bash
lake exe cache get          # Mathlib oleans
scripts/check.sh            # every gate, in one round
scripts/check.sh --quick    # only the gates that need no build
lake build Roadmap          # optional: check the target signatures still elaborate, and that
                            # the landed milestones still match the library
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

## Still to settle

1. **No `formalization.yaml`.** Tau Ceti's is copied in `TauCeti/` as the model; ours would say:
   source = Bombieri–Gubler plus the two roadmaps, single human author, `sorry_count: 0`, the three
   allowlisted axioms — all of it now machine-checked by the gates rather than asserted.
2. **The shim ledger.** `ArithmeticHeights` Layers 0.3 and 6.5 both deliberately shadow an open
   Mathlib PR (mathlib4#41606, mathlib4#40791), which is exactly what `mathlib-shims.json` and
   `check-expired-mathlib-shims.py` exist to track, so that the vendored copy is deleted when
   upstream lands rather than quietly diverging.
3. **Pins.** Toolchain `v4.35.0-rc3`, Mathlib `5e0c4e5239cb` on `master` (bumped on 2026-09-25 for
   Palomar) — ahead of Tau Ceti's
   `v4.34.0-rc1` / `653c36f019ec`, which is the allowed direction. Bumps stay forward-only.

Settled since: the Lean file headers all name "Ralf Stephan", `Arakelov.lean` included, so the
attribution question is closed.

Settled on 2026-09-25, the same day as Layer 9: `DiophantineApproximation` **Layer 3.7
restated for `N = 2`**, the interval result 9.4 names as its input, in
`DiophantineApproximation/RothIntervals.lean`:

- `NumberField.exists_forall_mem_interval_of_prod_min_one_le` — above any threshold `L' ≥ L`, the
  solutions of Roth's inequality have absolute height in at most `m (N + s).choose s` intervals
  `[Q, Q ^ M)` with `Q > exp L'`, Roth's parameters `m`, `M`, `N` depending on `κ`, `s`, `[F : K]`;
- `Finset.exists_subset_card_le_of_not_exists_chain` — the greedy grouping of 6.5.7 with its
  starting points kept: no chain of `m + 1` points means `m` windows cover.

What it taught: the interval result is the count with the gap principle removed — 6.5.7's blocks
are already intervals.

Then, the same day, **the link into 9.4**, in `DiophantineApproximation/RothSubspaceCount.lean`:

- `NumberField.exists_finset_submodule_of_card_eq_two` — the solutions of a normalized system in
  two variables above an ineffective height lie in at most
  `s + 1 + m (N + s).choose s · (1 + log (3 r s M) / log (1 + δ / 4))` proper subspaces, Roth's
  parameters at `2 + δ / 2`: uniform in the forms;
- `NumberField.exists_forall_mem_interval_of_prod_onePointApprox_le` — the interval result with
  targets at infinity, in log heights with a bounded shift;
- `NumberField.exists_finset_submodule_of_forall_mem_interval_of_mem` — 9.4 for any set of
  solutions, which the link needs.

What it taught: under Evertse's normalization the exponents pick the small form at each place,
so one Roth inequality serves every solution (no `2 ^ s` split as in 3.4), and the only new
estimate is that the affine height is a power of `H(x₁ / x₀)` — Liouville at one place against
the product of the small forms. The lines where a small form vanishes carry unboundedly high
solutions and are counted apart.

Settled on 2026-09-25, the same day as 8.3–8.7 and 9.1–9.3: `DiophantineApproximation`
**Layer 9.4**, **from intervals to subspaces** (Evertse, *On the Quantitative Subspace Theorem*,
2010, proof of Theorem 2.1), in `DiophantineApproximation/SubspaceIntervals.lean`:

- `NumberField.exists_finset_submodule_of_forall_mem_interval` — if the solutions outside `U₀`
  have height in `⋃_{i < m} [Q i, Q i ^ ω)` with `Q i ≥ n ^ (2 n / δ)` and `ω ≥ 1`, they lie in
  at most `m (1 + log ω / log (1 + δ / (2 n)))` proper subspaces;
- `NumberField.exists_finset_submodule_of_chain` — a chain of windows is covered by the union of
  their subspaces, moved from 9.3 into `SubspaceGap.lean` and now shared.

What it taught: nothing new was needed — an interval is a chain of 9.2's windows, and 9.3's chain
lemma counted them. The intervals are a hypothesis: Evertse's interval result, Theorem 3.1, is not
a milestone, so his Theorem 2.1 on the large solutions is not proved. **Layer 9 is complete.**

Settled on 2026-09-25, the same day as 8.3–8.7, 9.1 and 9.2: `DiophantineApproximation`
**Layer 9.3**, **the small solutions** (Evertse, *On the Quantitative Subspace Theorem*, 2010,
Proposition 4.2, Lemmas 4.3–4.5 and Theorem 2.2), in `DiophantineApproximation/DetPartition.lean`,
`DiophantineApproximation/DetCount.lean` and `DiophantineApproximation/SubspaceSmall.lean`:

- `Matrix.exists_det_partition` — Lemma 4.3: `ℂⁿ` in at most `(20 n) ^ n M²` classes with
  `|det| ≤ M⁻¹ ∏ ‖y i‖` inside each, on `Matrix.norm_det_le_card_rpow_mul_prod_norm`, Hadamard
  in the sup norm;
- `NumberField.exists_finset_submodule_of_window_two_mul` — the second gap principle: the window
  `[Q, 2 Q ^ (1 + δ / (2 n)))` needs at most `(90 n) ^ (n d)` proper subspaces;
- `NumberField.exists_finset_submodule_of_not_isLargeSolution` — Theorem 2.2: the solutions that
  are not large need at most `δ⁻¹ ((10³ n) ^ (n d) + 4 n log log (4 H))`;
- `NumberField.IsNormalizedSystem.two_le_card` — the normalization forces `n ≥ 2`;
- `Rat.exists_finset_submodule_of_det_le` — Lemma 4.5: `S`-integral points of `ℚⁿ` with every
  determinant at most `D v` at every place need at most `3 ^ n (4 n² + 2)² max (1, ∏ D v) ^
  (1 / (n - 1))` proper subspaces, and `Rat.exists_finset_submodule_of_abs_det_le` is Lemma 4.4;
- `Rat.exists_finset_submodule_of_window_two_mul` and
  `Rat.exists_finset_submodule_of_not_isLargeSolution` — over `ℚ`, `200 ^ n` per window and
  `δ⁻¹ (10 ^ (3 n) + 4 n log log (4 H))` for the small solutions, Evertse's refinement.

What it taught: **the second gap principle is the first plus a partition of `ℂⁿ`**, so 9.2's
assembly by the product formula was factored out and now serves both. The abstract places over
the infinite ones are complex embeddings by Layer 0.1, which is what lets Lemma 4.3 apply. The
source's intermediate count below `n ^ (2 n / δ)` was replaced by a cruder one that its final
constants still absorb. **The lattice-point lemma the source quotes for `ℚ` (Evertse 2000,
Lemma 5) is a pigeonhole on the minima of a Layer 4 approximation domain**: the dual of Evertse's
lattice is an approximation module at level `1`, so Minkowski's second theorem bounds the product
of the minima by the determinants with no loss. The source's `200 ^ n` per window drops a factor
`2 ^ (n - 1)` from the doubled window; the proof here gives a sharper constant in Lemma 4.5, which
recovers it.

Settled on 2026-09-25, the same day as 8.3–8.7 and 9.1: `DiophantineApproximation`
**Layer 9.2**, **the gap principle** (Evertse, *On the Quantitative Subspace Theorem*, 2010,
Proposition 4.1), in `DiophantineApproximation/SubspaceGap.lean`:

- `NumberField.exists_submodule_ne_top_of_window` — under (2.4) and for `Q ≥ n ^ (2 n / δ)`, the
  solutions whose absolute affine height lies in `[Q, Q ^ (1 + δ / (2 n)))` lie in one proper
  subspace;
- `NumberField.det_eq_zero_of_window` — any `n` of them have determinant `0`;
- `NumberField.one_le_prod_systemAbs_algebraMap` — the product formula for a nonzero `S`-integer
  over the places of a system;
- `AbsoluteValue.apply_det_le_factorial_mul_prod` and
  `AbsoluteValue.apply_det_le_prod_of_isNonarchimedean` — the Leibniz bounds for an abstract
  absolute value.

What it taught: **Hadamard is not needed.** The places are absolute values of `F` with no inner
product, and the Leibniz expansion's `n!` in place of `n ^ (n / 2)` is absorbed by Evertse's own
hypothesis `Q ≥ n ^ (2 n / δ)`, because `n! < n ^ n` for `n ≥ 2` and a nonempty window forces
`Q > 1` for `n = 1`. Only five of the ten fields of (2.4) are used. Nothing yet produces a
normalized system: 9.1's reduction does not give `c v i ≤ s(v)`, which needs an `S`-unit
rescaling of the point.

Settled on 2026-09-25, the same day as 8.3–8.7: `DiophantineApproximation` **Layer 9.1**,
**systems of inequalities** (Evertse, *On the Quantitative Subspace Theorem*, 2010, §2), in
`DiophantineApproximation/SubspaceSystem.lean`, the first file of Layer 9:

- `NumberField.systemSet`, `NumberField.systemWeight`, `NumberField.IsNormalizedSystem`,
  `NumberField.IsLargeSolution` — Evertse's system (2.3), its weight, his normalization (2.4) and
  the large solutions, with the places indexed by `InfinitePlace K ⊕ S`;
- `NumberField.affineProd_le_of_mem_systemSet` and `NumberField.affineProd_le_systemDet_mul_rpow`
  — a system implies the product inequality, and under (2.4) Schmidt's normalized one
  `|L₁(x) ⋯ Lₙ(x)| ≤ |det| · H(x) ^ (−δ)`;
- `NumberField.exists_finset_forall_exists_mem_systemSet` — the converse: finitely many exponent
  systems of weight at most `−δ/2` catch every large `S`-integral solution of
  `affineProd ≤ H(x) ^ (−δ)`, for any positive constants;
- `NumberField.exists_finset_submodule_of_systemWeight_neg` — **Evertse's Theorem A**, from 6.4;
- tests: (2.4) is satisfiable, by the coordinate forms of `ℚ²`; rejections: `n = 1` and weight `0`
  (the points `(2 ^ k, 1)` with `S = {2}`) break Theorem A.

What it taught: **against the affine height the reduction needs no unit.** Evertse's product
inequality has the affine height on the right, a coordinate is at most that height at every place,
so every exponent is at most `2` for large heights, with no fundamental inequality and no
independence of the forms; one clamp below disposes of vanishing forms. The exponents are the same
numbers in Evertse's normalization and Mathlib's, since both sides root by `[K : ℚ]`. The last
condition of (2.4), `max i, c v i = s(v)`, is a normalization of the representative — it fails for
`p ^ (−k) · y` at a finite place — and is left to 9.2, which uses it.

Settled on 2026-09-25, the same day as 8.3–8.6: `DiophantineApproximation` **Layer 8.7**, **the
Corvaja–Zannier gcd bound** (Corvaja–Zannier 2003, 2005; Bombieri–Gubler, Theorem 7.4.10), in
`DiophantineApproximation/GcdBound.lean`, which completes Layer 8:

- `Int.exists_forall_of_rpow_le_gcd_sub_one` — pairs of nonzero integers with prime factors in a
  finite set `P` and `gcd (u − 1) (v − 1) ≥ (max |u| |v|) ^ ε` are bounded or lie on one of
  finitely many curves `u ^ a * v ^ b = 1`, `(a, b) ≠ (0, 0)`;
- `Int.finite_setOf_rpow_le_gcd_sub_one` — finitely many of them are multiplicatively
  independent;
- `Nat.finite_setOf_primeFactors_subset` — the greatest prime factor of `(a b + 1)(a c + 1)`
  tends to infinity with `a`, for `a > b > c ≥ 1`;
- `Nat.finite_setOf_exp_le_gcd_pow_sub_one` — Bugeaud–Corvaja–Zannier,
  `gcd (a ^ n − 1) (b ^ n − 1) < exp (ε n)` for all large `n`;
- tests: `gcd (2 ^ n − 1) (3 ^ n − 1)`; rejections: the pairs `(2 ^ k, 2 ^ k)` show the curves
  are needed, and `b = c = 1` shows `c < b` is.

What it taught: **one application of 6.4 over `ℚ`, on a box of `(m + 2)²` monomials with
`m = ⌈4 / ε⌉`, and no filtration by order of vanishing.** The point is
`(u ^ (i + 1) v ^ j − 1) / d`, integral since `u ≡ v ≡ 1` modulo the gcd `d`; the forms are the coordinates at infinity and
`z i − z top`, `z top` at every prime, the same for every solution because the top monomial is the
smallest at every prime at once; the product formula for the monomials leaves `d` to the power of
the number of variables. At a prime of `P` dividing `d` the monomials are units, so the theorem
holds for the ordinary gcd. The subspace is a homogeneous unit equation, 8.6's Corollary 7.4.3
makes a monomial ratio take finitely many values, and a ratio `≠ 1` bounds `d` by a congruence —
no translate of a torus needs its own argument.

Settled on 2026-09-25, the same day as 8.3, 8.4 and 8.5: `DiophantineApproximation` **Layer 8.6**,
**norm-form equations** (Schmidt 1971–1972; Bombieri–Gubler §7.4), in
`DiophantineApproximation/NormForm.lean`:

- `NumberField.finite_setOf_norm_eq` — **Schmidt's theorem**, prototyped for the first time: if
  the `ℚ`-span of a finitely generated `ℤ`-submodule `M` of `K` is non-degenerate, then
  `N_{K/ℚ}(μ) = c` has finitely many solutions `μ ∈ M`;
- `NumberField.exists_finite_forall_mem_or_div_mem` — the general case: the solutions lie in a
  finite set or in finitely many sets `α F` inside the span, `F` a subfield with more than one
  infinite place;
- `NumberField.IsNondegenerate`, `NumberField.isNondegenerate_of_finrank_lt` — non-degeneracy,
  stated with embeddings, and the prime-degree criterion;
- `NumberField.exists_finite_forall_exists_div_mem` — Corollary 7.4.3 for homogeneous equations;
- tests: for `θ = 2 ^ (1/5)` the norm form of `ℤ + ℤ θ + ℤ θ ²` in three variables, with `θ` a
  solution of norm `2`; `x² + y² = c` in `ℤ[i]`, the imaginary quadratic exception; rejection:
  `x² − 2 y² = 1` in `ℤ[√2]`, infinitely many units.

What it taught: **the induction is on the dimension, not on the degree** — a dependent set of
pairwise non-proportional embeddings gives a homogeneous unit equation and a proper subspace, an
independent one forces the subspace to be a multiple `w₀ F` of a subfield by counting
embeddings, so everything happens inside `K` with one normal closure and no field changes type;
non-degeneracy is best stated as "one infinite place", read through embeddings; and the families
of the degenerate case, which need orders and their unit theorem, are located but not built.
`Suggested.lean` still carries 2 `sorry`s, both Wirsing's optional inequalities.

Settled on 2026-09-25, the same day as 8.3 and 8.4: `DiophantineApproximation` **Layer 8.5**,
**the hyperelliptic equation** (Siegel 1926; Bombieri–Gubler, Theorem 5.3.5), in
`DiophantineApproximation/{SIntegerSquares,Hyperelliptic}.lean`:

- `NumberField.finite_setOf_mul_sq_eq_eval` — **the milestone**, prototyped for the first time:
  for `f ∈ K[X]` with at least three distinct roots of odd multiplicity in an algebraically closed
  field and `b ≠ 0`, `b y² = f(x)` has finitely many solutions in `S`-integers;
- `NumberField.finite_setOf_mul_sq_eq_eval_of_squarefree` — the book's form, `f` squarefree of
  degree at least `3`; `NumberField.finite_setOf_mul_sq_eq_eval_of_splits` — the split case;
- `NumberField.exists_finset_forall_eq_mul_sq`, `NumberField.exists_eq_mul_sq_of_pow_mul_prod_eq`
  — the `S`-units modulo squares are finite, and over a principal ring of `S`-integers a coprime
  factor of a unit times a square is a unit times a square;
- tests: `y² = x³ − 2` in every number field and every `S`, with the solution `(3, 5)`;
  `y² = x³ (x² − 2)`, not squarefree; rejections: `y² = x² (x − 1)` (one root of odd
  multiplicity) and Pell's `y² = 2 x² + 1` (two roots).

What it taught: **8.1 once and nothing above it** — Siegel's identity is one unit equation, and
its ratio alone determines `x` by a rational function; the square classes need no ideal
factorization and no Selmer group, only the principal ring of `S`-integers from 0.3, the finite
generation of `S`-units from 6.5 and a Bézout identity; and the hypothesis is three roots of odd
multiplicity, strictly weaker than the book's squarefreeness at no cost. `Suggested.lean` still
carries 2 `sorry`s, both Wirsing's optional inequalities.

Settled on 2026-09-25, the same day as 8.3: `DiophantineApproximation` **Layer 8.4**, **Thue and
Thue–Mahler** (Thue 1909; Mahler 1933; Bombieri–Gubler 5.3.1–5.3.2), in
`DiophantineApproximation/{SIntegerExtension,ThueMahler}.lean`:

- `NumberField.finite_setOf_eval_homogenize_eq` — **the milestone**, prototyped for the first
  time: for `g ∈ K[X]` with at least three distinct roots in an algebraically closed field (the
  point at infinity counting), `G(x, y) = m ≠ 0` with `G = g.homogenize d` has finitely many
  solutions in `S`-integers;
- `NumberField.exists_finite_forall_eval_homogenize_mem_unit` — the unit version, modulo
  `S`-units, representatives among the solutions;
- `Polynomial.finite_setOf_natAbs_eval_homogenize_eq_prod_pow` — Thue–Mahler over `ℚ`: finitely
  many coprime `x, y` and exponents with `|G(x, y)| = ∏ p i ^ z i`;
- `NumberField.algebraMap_mem_integer_iff`, `NumberField.map_mem_unit_iff` — the passage to the
  primes above `S`, both directions;
- tests: `x³ − 2 y³ = 1` in every number field and every `S`, with the unit version;
  `x³ − 2 y³ = ± 2 ^ a 3 ^ b` over coprime integers, with the solution `(2, 1, 1, 1)`; rejections:
  coprimality (`(2 ^ k, 0)`) and Pell's equation among coprime pairs.

What it taught: **8.3 in the splitting field and nothing above it** — at least three pairwise
non-proportional binary forms are triangularly connected by Cramer's rule; the extension passage
8.3 moved here costs one short file, with the ramification exponent used only through its
positivity; the unit version descends with no degree, norm or homogeneity, since a scalar relating
two `K`-points on one line is a ratio of their coordinates; and Thue–Mahler over `ℚ` adds only
Bézout. `Suggested.lean` still carries 2 `sorry`s, both Wirsing's optional inequalities. The
same day's toolchain bump to `v4.35.0-rc3` cost three one-line ports outside 8.4:
`AlgHom.toRingHom_injective` (`ArithmeticHeights/Extension.lean`), `IsConcreteLE.not_le_iff_exists`
and `WithZero.log` (`…/FinitePlaceValues.lean`), and `Subgroup.fg_iff`, since `Subgroup.FG` is now
`IsMulFG` (`…/UnitEquationSeveral.lean`).

Settled on 2026-09-25: `DiophantineApproximation` **Layer 8.3**, **triangularly connected
decomposable forms** (Győry–Papp; Evertse–Győry, Ch. 9), in
`DiophantineApproximation/DecomposableForm.lean`:

- `NumberField.finite_setOf_mul_prod_eq` — **the milestone**, prototyped for the first time: for a
  triangularly connected family of forms with common kernel `0`, `c ∏ j, l j x ^ e j = m ≠ 0` has
  finitely many solutions in `S`-integers;
- `NumberField.exists_finite_forall_mul_prod_mem_unit` — the unit version: finitely many solutions
  of `G x ∈ S.unit K` modulo `S`-units, representatives among the solutions;
- `NumberField.exists_finite_forall_eq_smul` — the core, on any vector space: points where every
  form is an `S`-unit are `S`-unit multiples of finitely many;
- tests: `x y (x + y) = 2` over `ℤ`, with the solution `(1, 1)`; `x y = 1` has the infinitely
  many `{2}`-integral solutions `(2^k, 2^{−k})`, and `X, Y` are proved not triangularly connected.

What it taught: **8.1 once per triangle and nothing above it**; pairwise non-proportionality is
never used and is not a hypothesis; the unit version needs no discreteness of valuations, since
two solutions on one line differ by a scalar whose `E`-th power is an `S`-unit; and the passage to
a finite extension (non-split forms) is moved to 8.4, its first consumer. `Suggested.lean` still
carries 2 `sorry`s, both Wirsing's optional inequalities.

Settled on 2026-09-24, the same day as 6.1 to 8.1: `DiophantineApproximation` **Layer 8.2**,
**the unit equation in several variables** (Evertse; van der Poorten–Schlickewei;
Bombieri–Gubler, Theorem 7.4.2 and Corollary 7.4.3), in
`DiophantineApproximation/UnitEquationSeveral.lean`:

- `NumberField.finite_setOf_sum_unit_eq_one` and `NumberField.finite_setOf_sum_mem_eq_one` —
  **the milestones**, both `Suggested.lean` prototypes verbatim: finitely many `S`-unit (or
  finitely generated subgroup) solutions of `∑ i, a i x i = 1` with no vanishing subsum;
- `NumberField.exists_finite_forall_exists_mul_mem` — Corollary 7.4.3: with vanishing subsums
  allowed, some term `a i x i` lies in a fixed finite set;
- `NumberField.generalProd_sumEquationForms_eq` — 8.1's identity in `n` variables: with the forms
  `X i` and `∑ i, X i`, Vojta's central quantity is exactly `H(x)^{−n−1}`;
- tests: `1/2 + 1/3 + 1/6 = 1` in `{2, 3}`-units; `(2^k, −2^k, 1)` shows the no-vanishing-subsum
  hypothesis is load-bearing.

What it taught: **the induction takes two steps.** A proper subspace shortens the equation, but
the shortened one may have vanishing subsums; a minimal subsum equal to `1` has none and yields a
coordinate in a finite set, and fixing that coordinate leaves `n − 1` variables with right-hand
side `1 − u ≠ 0` — nonzero exactly because the complementary subsum does not vanish. `Suggested.lean`
now carries 2 `sorry`s, both Wirsing's optional inequalities.

Settled on 2026-09-24, the same day as 6.1 to 7.5: `DiophantineApproximation` **Layer 8.1**,
**the unit equation in two variables** (Siegel, Mahler, Lang), in
`DiophantineApproximation/UnitEquation.lean` — **the first milestone of Layer 8**:

- `NumberField.finite_setOf_unit_add_unit_eq_one` — **the milestone**, the `Suggested.lean`
  prototype verbatim: for `a, b ∈ Kˣ`, finitely many pairs of `S`-units satisfy `a x + b y = 1`;
- `NumberField.generalProd_unitEquationForms_eq` — with the forms `X₀, X₁, X₀ + X₁` at every
  place, Vojta's central quantity (Layer 6.5) at a solution is exactly `H(x, y)^{−3}`;
- the roadmap's test: `(2, −1), (3, −2), (4, −3), (9, −8)` are `{2, 3}`-unit solutions over `ℚ`.

What it taught: **no split by the largest coordinate** — the roadmap's route chooses a form per
place and applies 6.4 per choice, which is Vojta's refinement by hand; 6.5 with all three forms
needs no choice and gives `H^{−3}` on the nose. And the equation itself is the Bézout relation
that makes the point `S`-primitive, so its height is its product over `S∞ ∪ S`.

Settled on 2026-09-24, the same day as 6.1 to 7.4: `DiophantineApproximation` **Layer 7.5**,
**the complexity of an algebraic irrational** (Adamczewski–Bugeaud 2007, Theorem 1; Morse–Hedlund
1938), in `DiophantineApproximation/FactorComplexity.lean` and
`DiophantineApproximation/ComplexityTranscendence.lean` — **Layer 7 is complete**:

- `Real.tendsto_complexity_div_atTop` — **the milestone**: for `b ≥ 2`, if `∑ a k / b^(k+1)` is
  an algebraic irrational, the number `p n` of distinct blocks of `n` digits satisfies
  `p n / n → ∞`;
- `Function.isStammering_of_frequently_complexity_le` — **the combinatorial lemma**, over any
  finite alphabet and with no number in it: `p n ≤ C n` infinitely often makes `a` stammering;
- `Function.isEventuallyPeriodic_tfae` — **Morse–Hedlund**: eventually periodic, `p` bounded and
  `p n ≤ n` for some `n` are equivalent; with `Function.complexity_mono`;
- `Real.irrational_ofDigits_iff` — for `b ≥ 2`, irrational exactly when not eventually periodic;
- the roadmap's test: the binary digits of `∑ 2^{−2^k}` have complexity at most `3n + 1`, and the
  number is transcendental by 7.5.

What it taught: **the pigeonhole's repetition wants re-cutting, and then there is no case
split** — two equal factors of length `n` give a period `s` that may be tiny against `n`;
replacing it by its multiple in `(n/2, n/2 + s]` gives the bounded ratio and the exponent
`1 + 1/(1 + 2C)` uniformly. And the theorem feeds 7.4's working form, never its definition.

Settled on 2026-09-24, the same day as 6.1 to 6.6 and 7.1 to 7.3: `DiophantineApproximation`
**Layer 7.4**, **the combinatorial transcendence criterion** (Adamczewski–Bugeaud–Luca 2004;
Adamczewski–Bugeaud 2007; Ferenczi–Mauduit 1997), in
`DiophantineApproximation/StammeringWords.lean`, `DiophantineApproximation/DigitExpansions.lean`,
`DiophantineApproximation/RepetitionSubspaces.lean` and
`DiophantineApproximation/TranscendenceCriterion.lean` — **the first milestone of the roadmap
about words, and the first appeal to Layer 6 with finite places in it**:

- `Real.transcendental_ofDigits_of_isStammering` — **the milestone**: for `b ≥ 2`, a stammering
  sequence of digits that is not eventually periodic has a transcendental value;
- `Real.transcendental_ofDigits_of_isStammeringWith_of_two_lt` — **the Ferenczi–Mauduit
  criterion** for `w > 2`, from Ridout's theorem (Layer 3.3) and nothing above Layer 3;
- `List.rpow`, `Function.IsStammeringWith`, `Function.IsStammering`,
  `Function.IsEventuallyPeriodic` — the definitions, as the roadmap's prose gives them, with
  `Function.IsStammeringWith.exists_periodic` and its converse translating them to periodic
  segments of the digits;
- `Real.irrational_ofDigits` — a base-`b` expansion that is not eventually periodic has an
  irrational value, with no appeal to the uniqueness of expansions;
- `Rat.exists_finset_submodule_of_prod_mul_prod_padicNorm_le` — the Subspace Theorem over `ℚ` at
  `∞` and a finite set of primes, of which Layer 7.3's step is the case of no primes.

Three things it taught. **There is no induction on the subspace**: one subspace containing
infinitely many of the points `(b^{r+s}, b^r, p)` decides — its equation either fixes `b^s`, or it
makes the approximation `|θ b^s + η| ≤ 1` force `ξ` rational — and non-periodicity enters only as
the irrationality of `ξ`. **The gain is at the primes of the base**: at `∞` alone the product is
small only for `w > 2 + 2r/s`, and the `l`-adic sizes of `b^{r+s}` and `b^r` are what bring the
threshold down to `w > 1`; so the Subspace step had to be made a third time, with coordinate
forms at a finite set of primes. And **the roadmap had Ridout's two sets of primes the wrong way
round**: the primes of `b` sit on the denominator of the approximant, Ridout's `S₂`; and since
Ridout's theorem sees the approximant in lowest terms, what makes the `w > 2` route work is that
the part of the denominator prime to `b` does not grow along divisors.

Settled on 2026-09-24, the same day as 6.1 to 6.6, 7.1 and 7.2: `DiophantineApproximation`
**Layer 7.3**, **the exponents of an algebraic number and Schmidt's theorems on simultaneous
approximation** (Schmidt 1970; Bombieri–Gubler, Remark 7.3.4), in
`DiophantineApproximation/SchmidtExponents.lean`,
`DiophantineApproximation/SimultaneousSubspaces.lean` and
`DiophantineApproximation/SimultaneousApproximation.lean` — **the first milestone of Layer 7
that had to go back to Layer 6 for a second appeal**:

- `Real.mahlerExponent_eq_of_isAlgebraic` and `Real.koksmaExponent_eq_of_isAlgebraic` — **the
  milestone**: for a real algebraic `α` of degree `D` and every degree bound `n`, both exponents
  of Layer 1.2 equal `min n (D − 1)`, so Wirsing's conjecture holds with equality at every
  algebraic number;
- `Real.mahlerExponent_le_natCast_of_isAlgebraic` — the one bound Layer 1 could not supply,
  `w_n(α) ≤ n`, with `Complex.finite_setOf_norm_aeval_le` its polynomial-level form;
- `Real.finite_setOf_mul_prod_dist_lt` — **Schmidt's theorem on simultaneous approximation**:
  finitely many `q ≥ 1` satisfy `q^{1+ε} ∏ i, ‖q α i‖ < 1`;
- `Real.finite_setOf_prod_abs_mul_dist_lt` — **Schmidt's theorem on `∑ q i α i`**: finitely many
  `q ∈ ℤⁿ` with no vanishing coordinate satisfy `(∏ i, |q i|)^{1+ε} ‖∑ i, q i α i‖ < 1`, with
  `Real.finite_setOf_prod_abs_mul_abs_sum_lt` the linear form theorem it runs on;
- `Rat.exists_finset_submodule_of_prod_le` — the Subspace Theorem over `ℚ` with the hypothesis
  on the **bare product** of the values of a full system of forms, which Layer 7.1's appeal does
  not give and which Layer 7.4 may want.

Three things it taught. **Schmidt's exponents are read against the product `∏ |q i|`, not the
sup norm**, and that is what forced the second appeal to Layer 6: Layer 7.1's step bounds the
coordinate forms by `M^n` and keeps only the one nontrivial form, throwing away exactly what
these theorems are about — with the product intact the central quantity of the Subspace Theorem
*is* `(∏ ‖L_i x‖)/M^{n+1}`, and the hypothesis needed is `∏ ‖L_i x‖ ≤ M^{−ε}`. **Two inductions,
and one feeds the other**: the linear form theorem eliminates one variable per exceptional
subspace, while the theorem on `∑ q i α i` carries the numerator as an extra coordinate, and its
subspaces split into those that eliminate a `q` — the recursion — and those that determine the
numerator, which turn the distance to `ℤ` into a linear form and are finished by the first
theorem. And **simultaneous approximation needs no induction at all**: one exceptional subspace
already bounds `q`, because its relation together with `p i = q α i − θ i`, `|θ i| ≤ 1/2`, gives
`q (c₀ + ∑ c i α i) = ∑ c i θ i`, whose left factor is nonzero exactly because `1, α 1, …, α n`
are independent over `ℚ`.

Settled on 2026-09-24, the same day as 6.1 to 6.6 and 7.1: `DiophantineApproximation` **Layer
7.2**, **approximation by algebraic numbers of bounded degree** (Schmidt; Bombieri–Gubler,
Corollary 7.3.5), in `DiophantineApproximation/BoundedDegreeApproximation.lean` — **the first
milestone that stands on the summit and speaks none of its vocabulary**, naming a place in the
two lines that compare a height with a sup norm and an absolute value, a number field and
`approxProd` nowhere at all:

- `Complex.finite_setOf_norm_sub_le` — **the milestone**: for complex algebraic `α`, a degree
  bound `D` and `ε > 0`, only finitely many complex algebraic `ξ` of degree at most `D` satisfy
  `‖α − ξ‖ ≤ H(f_ξ) ^ (−D − 1 − ε)`, with `f_ξ` the primitive integer minimal polynomial of `ξ`;
- `Complex.finite_setOf_exists_root_norm_sub_le` — the same count taken over the minimal
  polynomials instead of over their roots, which is the shape the proof produces;
- `Real.koksmaExponent_le_of_isAlgebraic` — the milestone in Layer 1.3's language,
  `w_D^*(α) ≤ D`, which is half of Layer 7.3's upper bound;
- `Polynomial.norm_aeval_sub_aeval_le` — **the mean value theorem for an integer polynomial at
  two complex points**, `(n+1)^2 H(P) max(1, ‖z‖, ‖w‖)^n ‖z − w‖`;
- `Complex.exists_supNorm_le_of_aeval_eq_zero` and the generalization of
  `Polynomial.supNorm_eq_of_isPrimitive_of_irreducible` from a real root to a root in any
  `ℚ`-algebra that is a domain — the rigidity that makes `H(f_ξ)` a function of `ξ`.

Three things it taught. **The statement had to choose a shape**, because `H(f_ξ)` names an object
Mathlib does not have: the primitive integer minimal polynomial is defined only up to sign, so
the milestone quantifies over it, and it is the rigidity lemma — Layer 1.3's, generalized in
place from `ℝ` to any `ℚ`-algebra domain — that makes the existential the book's height. **The
count has to be taken over polynomials first**: the constant of the mean value theorem is removed
by the exponent only above the threshold `H ≥ C^{2/ε}`, and below it a bounded set of complex
numbers is not finite while the integer polynomials of bounded degree and bounded height are; the
approximants are recovered as their roots at the very end. And **the conjugates of `α` are the
one family Layer 7.1 cannot see** — it needs a nonzero value — but they need no separate
argument, since rigidity puts them all on one polynomial, whose height the Northcott branch
already carries.

Settled on 2026-09-24, the same day as 6.1 to 6.6: `DiophantineApproximation` **Layer 7.1**,
**one linear form with algebraic coefficients** (Bombieri–Gubler, Theorem 7.3.2), in
`DiophantineApproximation/LinearFormSubspaces.lean` and
`DiophantineApproximation/OneLinearForm.lean` — **the first thing the Subspace Theorem says about
numbers rather than about points**:

- `Complex.finite_setOf_norm_sum_mul_le_fin` — **the milestone**: for complex algebraic
  `α 0, …, α n` and `ε > 0`, only finitely many `x ∈ ℤⁿ⁺¹` satisfy
  `0 < ‖∑ i, α i * x i‖ ≤ H(x) ^ (−n − ε)`, and `Complex.finite_setOf_norm_sum_mul_le` is the
  same for an arbitrary finite index type, which is the form the induction proves;
- `Complex.exists_finset_submodule_of_norm_sum_le` — the **Subspace Theorem step**: the solutions
  lie in finitely many proper rational subspaces, which is all of Layer 6's contribution, with
  `Rat.exists_finset_submodule_of_sumForm_le` the same for coefficients in a named number field;
- `Module.Dual.projWithSum` and `Module.Dual.linearIndependent_projWithSum` — the system
  `∑ i, α i X i` together with the coordinate forms `X i` for `i ≠ j`, independent exactly when
  `α j ≠ 0`;
- `Rat.mulHeight_intCast_le_iSup` — the height of an integer point is at most its sup norm, the
  one inequality that turns the exponent `−n − ε` into the `−(n+1) − ε` Layer 6.3 wants;
- `Rat.approxProd_projWithSum_le` — the central quantity of the Subspace Theorem at an integer
  point is at most the value of the one nontrivial form, divided by the sup norm of the point.

Three things it taught. **The exponent drops by one for free**, and it is a statement about
*integers*: the coordinate forms contribute `M ^ n` against a denominator `M ^ (n+1)`, and the
height of an integer point is at most its sup norm `M` — which is also why the statement proved
is stronger than the book's, since Bombieri–Gubler read the exponent against `M` and not against
the height, a gain of `gcd(x) ^ (n + ε)`. **The induction reserves no room**: dropping a
coordinate from a proper subspace weakens the exponent by exactly one and lowers the height, so
one `ε` serves every step, and the reduced index type is the subtype `{i // i ≠ k}` with the
recursion on `Fintype.card ι ≤ n`, so nothing is transported along an equivalence. And **the
hypothesis is the nonvanishing of the value, never independence of the coefficients** — the
system is independent as soon as the displaced `α j` is nonzero — while the nonvanishing itself
is not decoration: `X 0 − X 1` vanishes on the diagonal, so without it the count is infinite at
every exponent, which the file records as a rejection test.

Settled on 2026-09-24, the same day as 6.1 to 6.5: `DiophantineApproximation` **Layer 6.6**,
**the consistency with Layer 3** (Bombieri–Gubler, Theorem 7.2.2 for `n = 1` and Example 7.2.7),
in `DiophantineApproximation/SubspaceConsistency.lean` — **with it Layer 6 is complete**:

- `NumberField.exists_finset_submodule_of_approxProd_le_card_two_of_extension` — **the
  milestone**: Layer 3.4's Subspace Theorem in two variables, proved from Layer 6.3, the whole of
  the specialization being that `Fintype.card ι = 2` supplies the `[Nontrivial ι]` Layer 6.3 asks
  for;
- `NumberField.exists_finset_submodule_of_approxProd_le_card_two_of_generalPosition` — the same
  from Vojta's refinement of Layer 6.5, general position for two forms in two variables being
  linear independence;
- `Projectivization.subsingleton_setOf_rep_mem` and
  `Projectivization.finite_setOf_exists_rep_mem` — a proper subspace of a plane holds at most one
  point of the projective line, and finitely many of them hold finitely many;
- `NumberField.finite_setOf_approxProd_le_card_two` — the projective reading: on `ℙ¹(K)` the
  Subspace Theorem is a **count of points**, with no subspace in the statement;
- `NumberField.finite_setOf_prod_min_one_le_of_extension` — **Roth's theorem over a number field
  recovered from Layer 6**, by discharging the hypothesis of Layer 3.4's converse implication
  from Layer 6.3 instead of from Layer 3.3.

Three things it taught. **The converse needed nothing, because the two statements are the same
proposition**: Layer 3.4 was stated for an arbitrary index type with `Fintype.card ι = 2` and
with `approxProd`, the very quantity Layer 6.3 uses, so "Layer 6.3 at `card ι = 2` is no
stronger" is not an implication at all. **`rfl` between two theorem constants is a real check**,
because proof irrelevance is definitional: an equality of proofs is an equality of statements,
and the file uses it four times — Layer 3.4 against Layer 6.3, Layer 6.5 against Layer 6.3, and
the two older proofs of Roth's theorem against the new one, so the library carries three proofs
of Roth's theorem and one theorem. And **the projective count cannot be moved down to tuples**:
both sides of the inequality are invariant under scaling, so one solution has infinitely many
nonzero multiples, which is why the finiteness has to be stated on `ℙ¹` and is recorded as a
rejection test.

Settled on 2026-09-24, the same day as 6.1 to 6.4: `DiophantineApproximation` **Layer 6.5**,
**the Subspace Theorem for forms in general position** (Vojta 1987; Bombieri–Gubler, Definition
7.2.8 and Theorem 7.2.9), in
`DiophantineApproximation/{GeneralPosition,SubspaceGeneralPosition}.lean` — the summit for
families of forms of **any finite sizes**:

- `Module.Dual.IsGeneralPosition` and `Module.Dual.IsGeneralPosition.of_linearIndependent` —
  every subfamily of at most `n + 1` forms linearly independent, and the observation that an
  independent family qualifies whatever its index finset;
- `Module.Dual.exists_index_extendProj` — Steinitz on Mathlib's `Basis.extendLe`, completing a
  short family to a basis by coordinate forms and reading the completion off an index map;
- `Finset.exists_powersetCard_forall_le` — a subset of given size whose members are the smallest,
  obtained by minimizing a sum rather than by sorting;
- `Module.Dual.exists_one_le_forall_exists_index_prod_le` — **the local step**: at every point,
  `n + 1` independent forms whose local factor is within a constant of the whole family's;
- `NumberField.generalProd` and `NumberField.approxProd_le_mul_generalProd` — the central
  quantity over families of any size, and the place-by-place comparison;
- `NumberField.exists_finset_submodule_of_generalProd_le` — **the milestone**, with
  `NumberField.exists_finset_submodule_setOf_generalProd_le_subset` the inclusion form and
  `NumberField.generalProd_univ_eq_approxProd` — which is `rfl` — recovering Layer 6.3 from it.

Three things it taught. **The two cases are different arguments and neither covers the other**:
for a family with at least `n + 1` members one keeps the smallest values, because general
position makes the forms behind them a basis and a basis bounds the coordinates from above, so
the discarded values are bounded below; for a shorter family one *completes* by coordinate forms,
whose factors are at most `1`. Extending every family by the coordinate forms and selecting the
smallest does not work — the extension need not be in general position. **The chosen system has
to range over a `Fintype`, and that fixes the signature**: the forms are indexed by one carrier
type with a `Finset` per place for their number, because the index maps `ι → κ ⊕ ι` chosen at the
places of `S` must form one finite type for the partition into classes to be finite. And **the
constant is removed by halving `ε`, so Northcott reappears** — the second and last time in the
Subspace Theorem, for the same reason as in 6.2.

Settled on 2026-09-24, the same day as 6.1, 6.2 and 6.3: `DiophantineApproximation` **Layer
6.4**, **the Subspace Theorem for `S`-integral points** (Bombieri–Gubler, Corollary 7.2.5 and
Theorem 7.2.6), in `DiophantineApproximation/{AffineProd,SubspaceAffine}.lean` — the summit in
the shape every application of Layer 8 quotes:

- `NumberField.affineProd` and `NumberField.affineProd_eq_approxProd_mul` — the affine quantity,
  with no local denominators, and the one identity that is the whole dictionary: it is the
  projective `approxProd` times the `S`-part of the height, `#ι` times over;
- `NumberField.approxProd_le_of_affineProd_le` and
  `NumberField.affineProd_le_iff_of_isPrimitive` — the affine inequality implies the projective
  one at an `S`-integral point, and the two are the same statement at an `S`-primitive one;
- `NumberField.exists_finset_submodule_of_integer_of_affineProd_le` — **the milestone**, with
  `NumberField.exists_finset_submodule_setOf_integer_of_affineProd_le_subset` the inclusion form;
- `NumberField.exists_finset_forall_exists_smul_affineProd_le` — the converse, Theorem 7.2.6: the
  enlarged data on which the affine form catches every solution of the projective one, so that
  the library carries one Subspace Theorem and not two.

Three things it taught. **The layer is one identity and no estimate**: the `n + 1` local
denominators the affine form drops are the `n + 1` copies of the height that separate `−ε` from
`−n−1−ε`, and the `n + 1` is the number of *forms*, not a dimension. **`S`-integrality is enough
in one direction only** — at an `S`-integral point the `S`-part of the height can exceed the
height, which makes the affine inequality the stronger one, and the converse has to scale to an
`S`-primitive point, where Layer 0.3 makes them equal; that asymmetry is exactly why the book
states the corollary for `S`-integers and the normalization for primitive points. And **the
converse enlarges three things at once, one per layer below it**: Layer 5.1's coordinate forms at
the added places, Layer 0.3's localization for the primitive multiple, and Layer 0.1's fibre for
an absolute value of `F` at every infinite place — which is why it must return a *new* family
`w'` rather than reuse the given one.

Settled on 2026-09-24, the same day as 6.1 and 6.2: `DiophantineApproximation` **Layer 6.3**,
**the Subspace Theorem with algebraic coefficients** (Bombieri–Gubler, Theorem 7.2.2 with Remark
7.2.3), in `DiophantineApproximation/{FormBaseChange,PlaceConjugation,ExtensionApproxProd,
SubspaceAlgebraic}.lean` — **the summit**, in the form its consumers quote: points in `K`,
coefficients in any finite extension `F`:

- `Module.Dual.compRingHom` and `Module.Dual.linearIndependent_compRingHom` — a linear form
  carried along a ring homomorphism, which is at once the base change and the conjugation, and
  the survival of independence under it;
- `NumberField.InfinitePlace.exists_algEquiv_apply_eq` and
  `NumberField.FinitePlace.exists_algEquiv_apply_eq` — every typed place of a Galois extension
  above `v` is a conjugate of one chosen absolute value over `v`, raised to the local degree;
- `NumberField.conjSystem` and `NumberField.approxProd_conjSystem` — the system of forms on the
  Galois closure, and the transfer of the central quantity, **an equality**;
- `NumberField.exists_finset_submodule_of_approxProd_le_of_isGalois` and
  `NumberField.exists_finset_submodule_of_approxProd_le_extension` — the Galois case and the
  milestone.

Three things it taught. **The transfer is an equality, and that is why the book conjugates**: a
point of `Kⁿ⁺¹` is fixed by the Galois group, so it sees the same local factor at every place
above `v`, and the local degrees there sum to the same degree by which the height grows. Filling
the other places with coordinate forms — Layer 5.1's device — would weaken the inequality in the
wrong direction. **Conjugation and base change are the same operation**, a ring homomorphism
applied to the coefficients, so no semilinear map and no tensor product appears; but the survival
of linear independence under it is a *determinant* statement, false for a non-square family.
And **Mathlib's normalization of finite places means Layer 0.2 is not about them**: a finite place
above `v` restricts to `v^{ef}`, so the orbit statement applies to its `(ef)`-th root, which is an
absolute value only because the place is nonarchimedean — and the `ef` then cancels against
`sum_localDegree` exactly as `mult` cancels against `sum_mult`.

Settled on 2026-09-24, the same day as 6.1: `DiophantineApproximation` **Layer 6.2**, **the
Subspace Theorem with coefficients in `K`** (Schmidt 1972 for `K = ℚ` and `S = {∞}`; Schlickewei
1977 with the finite places; Bombieri–Gubler, Theorem 7.2.2 with `F = K`), in
`DiophantineApproximation/SubspaceTheorem.lean` — **the summit over `K`**:

- `NumberField.exists_finset_submodule_of_approxProd_le` — finitely many proper subspaces of
  `Kⁿ⁺¹` contain every `x ≠ 0` with `approxProd S∞ S₀ L x ≤ H(x)^{−(n+1)−ε}`;
- `NumberField.exists_finset_submodule_setOf_approxProd_le_subset` — the same read as an
  inclusion of the solution set in a finite union of proper subspaces, the shape in print.

One file, one theorem, no new object and no auxiliary lemma: 6.2 is Layer 5.1 and Layer 6.1 put
together, and the five layers below it carry all of its content. Two things it taught.
**Northcott is a property of the projective height**, so "the solutions of small height are
finitely many" is false as stated — a line sits at one height — and what the argument really
needs is that the *projective* points of bounded height are finitely many, each contributing the
line it spans; that is also the only step where `n ≥ 1` does real work, and at `n = 0` the
theorem is false, the solutions being the roots of unity. And **the normalizing scalar never has
to be undone**: 5.1 puts a multiple `t·x` in a domain and 6.1 puts `t·x` in a subspace, which is
closed under `t⁻¹·−`, so no exponent system has to be made scale-invariant.

Settled on 2026-09-24: `DiophantineApproximation` **Layer 6.1**, **the parametric Subspace
Theorem** (Bombieri–Gubler 7.5.30–7.5.32, Steps VIII and IX; Evertse–Schlickewei for the
formulation), in `DiophantineApproximation/{WedgeRecovery,MinimaBounds,ExponentGrid,
WedgeExponentBound,ParametricSubspace}.lean` — where Layers 4 and 5 meet, and the first milestone
of **Layer 6**:

- `exteriorPower.recoverSpan` and `exteriorPower.recoverSpan_wedgeSpan` — Lemma 7.5.33 read as a
  *function* of the subspace, which is what carries finiteness from `⋀^p Kⁿ⁺¹` back to `Kⁿ⁺¹`;
- `NumberField.exists_pos_forall_rpow_le_successiveMinimum` and
  `NumberField.exists_pos_forall_rpow_le_successiveMinimum_le` — the minima of a domain lie
  between `Q^{−B}` and `Q^{B}`, from the product formula and then from Minkowski;
- `NumberField.gridExponent`, `NumberField.roundExponent` and
  `NumberField.finite_setOf_abs_le` — systems of exponents on a grid, the rounding, and the
  finiteness of the pool;
- `NumberField.abs_wedgeExponent_sub_sum_le` and
  `NumberField.exists_forall_approxWeight_wedgeExponent_le` — the exponents of the wedge domain
  stay in a box, and their weight is negative uniformly in the level;
- `NumberField.exists_finset_submodule_forall_approxDomain_subset` — the milestone: finitely many
  proper subspaces contain every approximation domain of large level.

Four things it taught. **The book's pigeonhole is avoidable**: rounding the moving exponents is a
function of the level with finite range, so the finite set of subspaces is a union over a finite
index set and no subsequence is extracted. **The penultimate rank is not a separate case**: it is
`p = 1` of the exterior-power construction, so one mechanism covers every rank and Layer 5.6 is
applied only through it. **Layer 4.2 bounds the wrong ends**: Minkowski's second theorem over `K`
bounds the product of the minima, which controls the first from above and the last from below,
while confining the exponents needs the opposite — and that bound is the product formula, `1 ≤ H`
against the local bounds of a dilated domain. And **an instance that is missing is not always a
missing import**: `NormedAddCommGroup (ι → mixedSpace K)` is unavailable until `Classical` is
open, because the mixed space is a product over subtypes of the infinite places whose `Fintype`
needs a decidable predicate.

Settled on 2026-09-23, the same day as 5.2, 5.3, 5.4 and 5.5: `DiophantineApproximation` **Layer
5.6**, **the penultimate-minimum theorem** (Bombieri–Gubler, Theorem 7.5.13, Steps IV and VI), in
`DiophantineApproximation/{LogComparison,FormIndexSubspace,SubspaceValueBound,
SubspaceKeyInequality,PenultimateMinimum}.lean` — with it **Layer 5 is complete**, and the path
to the Subspace Theorem stands at 6.1:

- `MvPolynomial.substFormInv_eq_linSubst` and
  `MvPolynomial.exists_linSubst_hasseDeriv_ne_zero_of_formIndex_le` — the bridge from Layer 5.3's
  index along the forms to Layer 5.5's hypothesis, a derivative of small weighted order that does
  not vanish identically on the product of the subspaces;
- `NumberField.formMatrix`, `NumberField.refFamily` and `NumberField.approxAbsWeight` — the
  matrix of a system of forms, the reference family the product formula charges, and the weight
  of the *absolute values* of a system of exponents;
- `MvPolynomial.apply_eval_hasseDeriv_le_place` and its nonarchimedean companions — the local
  bound on a derivative of the auxiliary polynomial at a point of the domain, at one place;
- `NumberField.subspace_key_inequality` — Step VI, the product formula against those bounds;
- `Submodule.exists_basis_subset` and `Submodule.logHeight_eq_logHeight_of_forall_dotProduct` — a
  spanning set contains a basis, and the height of a hyperplane is the height of its normal
  vector (the book's (7.28));
- `NumberField.exists_forall_not_chain` — Steps IV and VI: no chain of `m + 1` levels of rank `n`
  with `log Q` growing at the rate `2 σ⁻¹` can have all its spans of large height;
- `NumberField.logHeight_approxSpan_le`, `NumberField.exists_forall_approxSpan_mem` and
  `NumberField.finite_setOf_approxSpan` — the upper bound at every level, the large-level form,
  and Theorem 7.5.13 itself.

Four things it taught. **The chain rule is not needed a third time**: Layer 5.3 measures the
index in the coordinates in which the forms are the variables and Layer 5.5 wants a derivative in
the original ones, but the change of coordinates *is* a block-wise linear substitution, so 5.5's
own transport lemmas carry a surviving coefficient between the two systems with the same degree
in every block — which is exactly what makes the two weighted orders agree. **The system of
exponents has two invariants here, not one**: besides the (negative) `approxWeight`, the local
bound needs the weight of the `|c v i|`, and that is the quantity the parameter `η` is chosen
against. **One reference family carries both the inverse matrices of the forms and the integers
of the grid**, at exponent `2 |d|`, because both are bounded by the same product of truncated
local factors. And **the heartbeat budget is per declaration**, which is why every inequality
with a division in it was factored into five lemmas over `ℝ` alone: raising `maxHeartbeats` was
the alternative, and `set_option` is forbidden in library files here.

Settled on 2026-09-23, the same day as 5.2, 5.3 and 5.4: `DiophantineApproximation` **Layer
5.5**, **non-vanishing at a small point** (Bombieri–Gubler, Lemmas 7.5.24 and 7.5.25), in
`DiophantineApproximation/{PolynomialGrid,SmallPoint}.lean` — Step V of the proof of the Subspace
Theorem:

- `Polynomial.exists_eval_hasseDeriv_ne_zero` and `MvPolynomial.exists_eval_hasseDeriv_ne_zero` —
  the grid lemma: a nonzero polynomial of degree at most `e j` in `X j` has a Hasse derivative of
  order at most `e j / B` in each variable that does not vanish at a point of the grid of integers
  `|z j| ≤ B`;
- `MvPolynomial.toPolynomial` — the specialization of every variable but one, and the only bridge
  between Mathlib's one-variable Hasse derivative and the several-variable one that the induction
  needs;
- `MvPolynomial.shift` and `MvPolynomial.coeff_shift` — the shift `X j ↦ X j + c j`, whose
  coefficients are the Hasse derivatives at `c`;
- `MvPolynomial.linSubst` — the block-wise linear parametrization, with `eval_linSubst`
  (evaluating it is evaluating at the parametrized point), `shift_linSubst` and
  `IsMultiHomogeneous.linSubst`;
- `MvPolynomial.exists_eval_hasseDeriv_add_ne_zero` and
  `MvPolynomial.exists_eval_hasseDeriv_ne_zero_of_sum_div_le` — the small point, and the same with
  `B = 2 n / η`, which is the book's (7.37).

Three things it taught, none of them a correction to a statement and all three to a proof. **The
one-variable case is a count of roots with multiplicity, not a divisibility**: the book's product
of `2 B + 1` linear factors divides `f` only by unique factorization over the ring of the
remaining variables, while `Polynomial.roots` already carries multiplicities and
`Polynomial.card_roots'` bounds their number by the degree. **The induction on the variables must
not substitute**: carrying "the derivative does not vanish identically on the affine subspace
where the handled variables sit at their grid values" costs nothing, while carrying the
substituted polynomial would force a lemma commuting a Hasse derivative past a partial
substitution. And **the chain rule the book invokes to read the derivative back through the
parametrization is not needed**: only the block degrees of the orders that can occur are used, and
that is multihomogeneity — the two evaluations become two coefficient extractions from the same
shifted polynomial.

Settled on 2026-09-23, the same day as 5.2 and 5.3: `DiophantineApproximation` **Layer 5.4**,
**the height of `V(Q)` and the exceptional subspaces** (Bombieri–Gubler, Lemma 7.5.21), in
`DiophantineApproximation/{LinearFormValue,SubspaceNormal,SubspaceHeightBounds,
ExceptionalSubspace}.lean` — Step III of the proof of the Subspace Theorem:

- `NumberField.InfinitePlace.iSup_mul_iSup_pow_mult_le` — Liouville's inequality for the value of
  a linear form: the local factors of the coefficient tuple and of the point are bounded by their
  heights times the local value of the form;
- `Submodule.exists_normal` — a subspace of dimension `n` in `Kⁿ⁺¹` is the kernel of one vector,
  and the Plücker coordinate omitting `i` vanishes exactly when the `i`-th coordinate of that
  vector does;
- `NumberField.exists_one_le_forall_mulHeight_plucker_le` and
  `NumberField.exists_pos_forall_prod_le` — the upper and lower bounds on the height of the span
  of a basis of the domain;
- `NumberField.patternSpace` and `NumberField.mem_span_vec_of_normal` — the exceptional system,
  read in the original coordinates as an intersection of spans of coefficient vectors of the
  forms;
- `NumberField.exists_finite_forall_mem_of_weightAt_lt` — the exceptional alternative, one
  subspace per pattern;
- `NumberField.exists_finite_forall_logHeight_approxSpan` — Lemma 7.5.21 itself.

Three things it taught, two of them corrections. **The inequality Step III rests on is not the
book's, and the book's is false**: Bombieri–Gubler bound the height of the single number
`L̂_{vi}(w)` by `h(V(Q)) + C₇`, comparing a scale-dependent quantity with a scale-invariant one —
over `ℚ` the vector `(N, 0)` has `h(V) = 0` and `h(w_0) = log N`. What the proof needs is a
product-formula inequality between the *local factor* of the Plücker point and its *projective*
height, and it is stronger than what the book extracts, by one power of the height. **The
exceptional subspace is one per pattern**: the book writes "a linear space `W`", and its own
proof fixes one solution per pattern of surviving indices, a pattern that moves with `Q`; there
are finitely many patterns, which is all Step IV consumes. And **no Hodge star, no adjugate and no
cofactor expansion is needed anywhere**: read in the original coordinates the exceptional system
says that the normal vector lies in the span of the coefficient vectors of the surviving forms,
and the dictionary between the two descriptions is `ArithmeticHeights` 3.5 read at the ranks `n`
and `1`.

Settled on 2026-09-23, the same day as 5.2: `DiophantineApproximation` **Layer 5.3**, **the index
along linear forms and the generalized Roth lemma** (Bombieri–Gubler, Definition 7.5.17, 7.5.18
and Lemma 7.5.19), in
`DiophantineApproximation/{FormIndex,FormSpecialization,GeneralizedRothLemma}.lean` — Step II of
the proof of the Subspace Theorem:

- `MvPolynomial.formIdeal` and `MvPolynomial.formIndex` — the ideal generated by the products
  `∏ h, M h (X h) ^ (j h)` of weight at least `t`, and the index of `P` along the forms as the
  supremum of the `t` it lies in;
- `MvPolynomial.formIndex_eq_weightedOrder` — the index is the weighted order of Layer 2.3 in the
  coordinates in which the forms are variables, which is where the valuation properties come
  from;
- `MvPolynomial.exists_elimination` — the specialization of every block to two coordinates,
  losing no height and no index;
- `MvPolynomial.formIndex_eq_index_deHom` — 7.5.18, the agreement with Layer 2.3 after
  dehomogenization, in the generality Lemma 7.5.19 needs;
- `Height.exists_logHeight_le_mul_logHeight₁_div` — the height of a tuple against the heights of
  its ratios: one of the `n` ratios to a nonvanishing coordinate carries at least `1/n` of it;
- `MvPolynomial.formIndex_le_of_degree_ratio` — Lemma 7.5.19 itself.

Three things it taught. **The index along the forms is not a new object**: solving
`M h = X (h, i₀ h)` for one coordinate turns the book's ideal into a monomial ideal, and the
index becomes Layer 2.3's weighted order with a weight of `0` on every other variable — after
which nothing has to be proved twice. **The variables have to be specialized one at a time**, and
the coefficients of the forms truncated in step with them: a single slice at the componentwise
minimum of the exponents can be zero (`X 1 + X 2` has no monomial with both exponents minimal),
and going through the untruncated forms gives the index inequality backwards. And **two of the
book's precautions are unnecessary**: only the inequality between the indices before and after
the specialization is needed, not the equality it asserts, and its `b_{j1} ≠ 0` never enters,
because the hypothesis on the heights passes to Layer 2.7 whatever the second coordinate is.

Settled on 2026-09-23: `DiophantineApproximation` **Layer 5.2**, **the multihomogeneous auxiliary
polynomial** (Bombieri–Gubler 7.5.14 and Lemma 7.5.15), in
`DiophantineApproximation/{MultiHomogeneous,MonomialDeviation,SubspaceAuxiliary}.lean` — Step I of
the proof of the Subspace Theorem:

- `MvPolynomial.IsMultiHomogeneous`, `MvPolynomial.blockSubst` and `MvPolynomial.multiMons` — the
  multidegree, the change of coordinates `X (h, j) ↦ ∑ i, A j i • X (h, i)` inside every block,
  and the monomials of a fixed multidegree, with `MvPolynomial.card_multiMons` giving the
  dimension `∏ h, (d h + n).choose n` as a product over the blocks;
- `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero` — the chain rule in the only form the
  milestone uses: a coefficient of the expansion of `∂_I P` vanishes as soon as the coefficients
  of `P` in the transformed coordinates vanish at every order with the same block degrees;
- `Finset.card_le_of_subset_eta` — the Chernoff bound over the blocks: the monomials whose
  exponent of one variable is below `m/(n+1) − m η` are fewer than the total by
  `exp (−(n+1)(n+2) η² m / 4)`, with one explicit error term;
- `MvPolynomial.exists_ne_zero_isMultiHomogeneous_coeff_blockSubst_eq_zero` — Siegel's lemma in
  the multihomogeneous setting, from `ArithmeticHeights` 5.5 with the height of the condition
  matrix computed from its local factors;
- `MvPolynomial.exists_ne_zero_isMultiHomogeneous_forall_coeff_blockSubst_hasseDeriv_eq_zero` —
  Lemma 7.5.15 itself.

Three things it taught. **The book's volume computation is avoidable**: the exponential moment of
the exponent of one variable is exact on the lattice — `E[j i] = N/(n+1)` and
`E[binom (j i) 2] = N(N−1)/((n+1)(n+2))`, two binomial identities — and `exp(−t) ≤ 1 − t + t²/2`
finishes it, so the book's restriction `0 < λ ≤ n + 4` and most of its "sufficiently large `d`"
disappear. **The chain rule is the whole content of the vanishing statement**: `a(L v; J; I)` is
*not* `binom (J + I) I · a(L v; J + I; 0)`, because the derivatives are taken in one coordinate
system and the expansion is read in another; the induction on the order that replaces it needs
characteristic zero. And **the hypothesis on `m` has to be strict** — the Chernoff error term is
positive at every `d`, so `m ≥ 4 log (2 (n+1) |S|) / ((n+1)(n+2) η²)` leaves no slack for `D₀` to
be chosen against — while `η ≤ 2/(n+1)` is never used at all.

Settled on 2026-09-22, the same day as 3.3 to 4.5: `DiophantineApproximation` **Layer 5.1**,
**the reductions of the Subspace Theorem** (Bombieri–Gubler, Theorem 7.2.6, Lemma 7.5.4,
Corollary 7.5.5 and 7.5.6), in
`DiophantineApproximation/{UnitNormalization,SubspaceReduction}.lean` — the first milestone of
Layer 5:

- `NumberField.exists_finset_superset_forall_exists_iSup_eq_one` and
  `NumberField.mulHeight_eq_prod_of_forall_iSup_eq_one` — after enlarging `S₀` every point has a
  primitive multiple, whose height is the product of its local sup norms over the infinite places
  and `S₀`;
- `NumberField.exists_forall_logHeightAff_smul_le` — Lemma 7.5.4: an `S₀`-unit multiple whose
  affine height exceeds the projective height by a constant depending only on `K` and `S₀`;
- `NumberField.exists_forall_logHeight₁_apply_smul_le` with
  `NumberField.InfinitePlace.abs_mult_mul_log_le_logHeight₁` — Corollary 7.5.5 and the book's
  (7.19);
- `NumberField.exists_finset_forall_exists_smul_mem_approxDomain` and
  `NumberField.exists_forall_approxProd_le_imp` — 7.5.6: every solution of large height lies on
  the kernel of a form or has a multiple in one of finitely many approximation domains of weight
  at most `−ε/2`.

Two things it taught. **The unit normalization is one lattice approximation**, of the trace-zero
vector that balances the height over the places: no coordinate is singled out, no distinguished
infinite place appears, and the constant is independent of the number of variables — and the
Corollary needs no independence of the forms, only the height of a single number. And **the
approximation classes are cells of a cube, not of Layer 3.1's simplex**: the exponents have both
signs and are merely bounded, so 3.1 is not reused; the statement is parametric in the solution,
as Layer 4.3's is, and the book's pigeonhole along an infinite sequence never appears.

Settled on 2026-09-22, the same day as 3.3 to 4.4: `DiophantineApproximation` **Layer 4.5**,
**exterior powers of a system of forms** (Bombieri–Gubler 7.5.30–7.5.31, Lemma 7.5.33), in
`DiophantineApproximation/{WedgeForm,WedgeDomain}.lean` — and with it **all of Layer 4**:

- `exteriorPower.wedgeForm_plucker` and `exteriorPower.linearIndependent_wedgeForms` — Laplace's
  identity for the wedge of forms on the Plücker coordinates, and independence of the wedges;
- `exteriorPower.wedgeSpan_eq_wedgeSpan_iff` — Lemma 7.5.33: the span of the wedges of a basis
  meeting the first `k` indices determines, and is determined by, the span of the first `k`;
- `NumberField.exists_plucker_mem_approxDomain_wedgeForms`,
  `NumberField.rpow_approxWeight_wedgeExponent_le` and
  `NumberField.exists_successiveMinimum_wedge_pow` — Step VIII: the wedges of Evertse's vectors lie
  in the wedge domain `S(Q)`, whose weight is a constant times the jump of the minima, and whose
  last minimum is at least a positive power of `Q` for a suitable `k` — Lemma 7.5.31.

Two things it taught. **The exterior power had to be read in coordinates**, so that 6.1 can apply
Layers 4.2–5.6 inside it — and then the determinant of the wedges, which the book records, is
never needed, and Lemma 7.5.33 is the kernel of one wedge form rather than an annihilator under a
pairing of `⋀^p` with `⋀^k`. And **`S(Q)` is an approximation domain whose exponents move with
`Q`**, `logb Q` of the book's bounds: its weight is an exact identity before it is an estimate,
and the weight — not the last minimum the book states — is what 6.1 consumes after rounding the
exponents to a grid.

Settled on 2026-09-22, the same day as 3.3 to 4.3: `DiophantineApproximation` **Layer 4.4**,
**Evertse's lemma** (Evertse 1996; Bombieri–Gubler, Lemma 7.5.29), in
`DiophantineApproximation/{SIntegerApproximation,EvertseLemma}.lean`:

- `NumberField.exists_forall_apply_add_le` — simultaneous approximation by `S₀`-integers, stated
  without completions: targets `γ v ∈ K` at the infinite places and at `S₀` are met by one
  `S₀`-integer, exactly at `S₀` and within a constant depending on `K` alone at infinity;
- `AbsoluteValue.exists_evertse_of_approx` — the book's induction, for any field whose places admit
  such an approximation by a subring, one estimate serving both kinds of place;
- `NumberField.exists_evertse` — Evertse's lemma with a weight `ν v i` per form, and
  `NumberField.exists_evertse_unweighted`, the book's statement.

Two things it taught. **The constant has to be chosen before the forms**: the book lets it depend
on the forms and then applies the lemma to forms that move with `Q`, while its proof gives a
constant depending on `K` and `n` only — and the constant at the infinite places cannot be `1`,
even for real coefficients. And **over `K` the moving forms become weights**: `Q ^ (−c) L` has no
coefficients in `K`, and at a finite place rescaling would cost the factor `N 𝔭` and the exact
bound. The approximation needed no Chinese remainder theorem: prime avoidance and one geometric sum.

Settled on 2026-09-22, the same day as 3.3 to 4.2: `DiophantineApproximation` **Layer 4.3**, **the
rank of an approximation domain** (Bombieri–Gubler, Definition 7.5.11, Lemma 7.5.12), in
`DiophantineApproximation/ApproximationRank.lean`:

- `NumberField.approxSpan` — `V(Q)`, the span of the domain of level `Q`;
  `NumberField.finrank_approxSpan` and `NumberField.approxSpan_eq_span_image` — its dimension is
  the number of minima over `K` at most `1`, and it is spanned by the vectors realizing them, both
  first proved for any lattice in any closed bounded symmetric convex body;
- `NumberField.eventually_finrank_approxSpan_lt` and `NumberField.eventually_approxSpan_ne_top` —
  for negative weight, the rank is at most `n` and `V(Q)` proper at every large enough level, from
  `NumberField.le_successiveMinimum_approx_pow`, the last minimum at least a power of `Q`;
- `NumberField.finite_image_approxSpan` — a bounded range of levels, `[Q₁, Q₂]` with `Q₁ > 0`,
  contributes finitely many `V(Q)`, because all its domains lie in one finite domain.

Two things it taught. **Lemma 7.5.12 is about levels, not solutions**: the book states it along the
heights of hypothetical solutions, with Northcott for "all but finitely many"; for domains it is
`∀ᶠ Q in atTop`, the rank can be `0`, and at `Q = 1` it can still be full with the weight negative.
And **the rank is read from the minima through attainment**, counting the minima at most `1` — over
`ℚ` the domain `ℤ ∩ [−1, 1]` has its one minimum exactly `1`.

Settled on 2026-09-22, the same day as 3.3 to 4.1: `DiophantineApproximation` **Layer 4.2**,
**successive minima over `K`** and **Minkowski's second theorem over `K`** (Bombieri–Gubler,
Definition C.2.9, Theorem C.2.11), in `DiophantineApproximation/{FieldMinima,FieldMinkowski}.lean`:

- `NumberField.successiveMinimum` — the `l`-th minimum over `K`, the least dilation of `B` whose
  intersection with `Λ` holds `l` vectors independent over `K`, indexed from `0` as
  `ZLattice.successiveMinimum` is; `NumberField.exists_linearIndependent_mem_smul_successiveMinimum`
  — attained, by one family independent over `K`;
- `NumberField.successiveMinimum_mixedImage_le`,
  `NumberField.successiveMinimum_le_successiveMinimum_mixedImage` and
  `NumberField.successiveMinimum_mixedImage_le_mul` — `λ l ≤ μ l ≤ λ (d (l − 1) + 1)` and
  `λ (d l) ≤ c_K μ l`, with `c_K = NumberField.integralBasisHouse K` the largest house of the
  integral basis;
- `NumberField.covolume_le_prod_successiveMinimum_pow_mul_measure` and
  `NumberField.prod_successiveMinimum_pow_mul_measure_le` — both halves of Minkowski's second
  theorem over `K`, from the real one;
- `NumberField.le_prod_successiveMinimum_approx` and `NumberField.prod_successiveMinimum_approx_le`
  — for an approximation domain, `(μ 1 ⋯ μ (n + 1)) ^ d` is `Q ^ (−weight)` up to constants, the
  form Layer 4.3 consumes.

Three things it taught. **The extraction lemma is spent twice**: besides
`μ l ≤ λ (d (l − 1) + 1)`, it is what makes the minima over `K` finite at all, so `Λ` enters
every statement only as a lattice, with no hypothesis that it spans. **Attaining the minima over
`K` needs finiteness, not Cassels' greedy minimality**: each is attained separately, and one family
is assembled by the extraction lemma's selection step. And **Mathlib had both inputs**: that
independence over `ℚ` survives the mixed embedding is `linearIndependent_algebraMap_comp_iff` in
the coordinates of `latticeBasis`, and `c_K` is a `house`; over `ℚ` it is `1`, and in one variable
Minkowski's second theorem over `K` is an equality.

Settled on 2026-09-22, the same day as 3.3 to 3.8: `DiophantineApproximation` **Layer 4.1**,
**approximation domains** (Bombieri–Gubler 7.5.6, Lemma 7.5.7, Corollary 7.5.8), in
`DiophantineApproximation/{FinitePlaceValues,ModuleCovolume,ApproximationDomain,
ApproximationVolume}.lean` — the first milestone on the path to the summit:

- `NumberField.approxDomain_eq` — the approximation domain, prototyped in `Suggested.lean` and
  landed verbatim with its weight, is `Λ ∩ B`: an `𝓞 K`-submodule of `Kⁱ` cut out by the finite
  conditions, and a compact convex symmetric body in `ι → mixedSpace K`, balanced over every
  completion, cut out by the infinite ones;
- `NumberField.covolume_approxLattice` — `covol Λ = ∏ v ∈ S₀, v (det L v) ∏ i (a v i)⁻¹ ·
  covol (𝓞 K) ^ #ι`, exact, with `a v i` the largest value of `v` at most `Q ^ c v i`;
- `NumberField.volume_approxBody` — `vol B = 2 ^ (r₁ #ι) π ^ (r₂ #ι) ∏_{v | ∞}
  (v (det L v)⁻¹ ∏ i Q ^ c v i) ^ mult v`;
- `NumberField.volume_div_covolume_le` and `NumberField.le_volume_div_covolume` — `vol B / covol Λ`
  is `Q` to the weight up to `NumberField.approxConst`, which sees only `K`, `S₀`, `#ι` and the
  determinants; the upper bound carries no loss;
- `Submodule.covolume_mixedImage` — the covolume of any finitely generated `𝓞 K`-module spanning
  `Kⁱ` is `(∏ᶠ_{v ∤ ∞} B v)⁻¹ covol (𝓞 K) ^ #ι`, `B v` the largest value of `v` on its
  determinants. Mathlib has the case `#ι = 1`, the ideals.

Three things it taught. **Bombieri–Gubler's finite-place volume is not an equality in
`Q ^ c v i`**, as the roadmap warned: it is exact in the value group, and at the `2`-adic place of
`ℚ` with `Q ^ c = 3/2` the covolume is `1` where the book's formula gives `2/3`. **The index of a
lattice cut out by local conditions needs no quotient**: the maximal determinants at each place
determine it, and they are computed by the ultrametric Leibniz bound and attained after one
scaling by an algebraic integer that is a unit at the place — so no localization, no Smith normal
form and no class group. And **Mathlib's instance search does not find the Borel structure or the
Haar property of the volume on `ι → mixedSpace K`**, though it finds both on `mixedSpace K`; they
are declared once, from the factors'.

Settled on 2026-09-22, the same day as 3.3 to 3.7: `DiophantineApproximation` **Layer 3.8**,
**Roth's theorem with moving targets** (Vojta; Bombieri–Gubler, Theorem 6.5.2), in
`DiophantineApproximation/MovingTargets.lean`, with the core of Roth's proof restated in
`…/RothTheorem.lean`. It completes Layer 3:

- `NumberField.finite_setOf_prod_min_one_le_of_isLittleO` — if
  `1 + ∑ v ∈ S, h(α_j v) = o(h(β_j))`, only finitely many `j` are solutions of Roth's inequality
  with the targets `α_j`; `NumberField.not_forall_prod_min_one_le_of_isLittleO` is the book's
  form, that no infinite sequence of solutions exists;
- `NumberField.roth_no_moving_chain` — the core of Roth's proof for a chain whose members carry
  their own targets: a `δ > 0` that sees no target, such that no chain in one class has
  `1 + ∑ v, h(α_j v) ≤ δ h(β_j)` throughout. 3.7's `NumberField.roth_no_chain` is now its
  constant case;
- `NumberField.max_apply_one_le_mulHeight₁_of_liesOver_infinitePlace` and its finite twin — an
  absolute value of `F` over a place of `K` is at most the height, `max |x|_w 1 ≤ H(x)`, which
  Mathlib does not have.

Two things it taught. **The targets enter Roth's proof in two places, and the book names one**:
its proof of 6.5.2 changes only the height of the auxiliary polynomial, but the Taylor expansion
at a place of `S` carries the size `log⁺ |α_v|` of the target too, and with moving targets that
has to be bounded by the height — Layer 0.1's classification, not a triviality. And **the
conclusion counts indices**: a sequence may repeat a pair, and the `1 +` of the growth condition
is what excludes the constant pair `(0, 0)`, a solution at every index with `0 = o(0)`. The steps
under Roth's theorem were generalized to one target per coordinate; nothing that 3.2's consumers
quote changed.

Settled on 2026-09-22, the same day as 3.3 to 3.6: `DiophantineApproximation` **Layer 3.7**,
**counting approximations** (Bombieri–Gubler, Theorem 6.5.4, Lemma 6.5.6 and 6.5.7; Davenport and
Roth 1955 at one place), in `DiophantineApproximation/{GapPrinciple,CountingApproximations}.lean`
and a restructured `…/RothTheorem.lean`:

- `NumberField.mul_absLogHeight₁_sub_le_of_approxClass_eq` — the strong gap principle,
  `h(β') ≥ ((1 − |S|/N) κ − 1) h(β) − log 4` for two different solutions in one approximation
  class `NumberField.approxClass`, in absolute heights;
- `NumberField.ncard_setOf_absLogHeight₁_mem_Ioc_le` — at most
  `⌈log A / log ((c + 1)/2)⌉ (N + |S|).choose |S|` solutions with height in `(X, A X]`;
- `NumberField.exists_ncard_setOf_lt_absLogHeight₁_le` — above a height `L` there are at most
  `NumberField.rothLargeCount κ |S| [F : K]` solutions, a number depending on nothing else;
- `NumberField.roth_no_chain` — the core of Roth's proof as a theorem: above `L`, no
  `(L, M)`-independent chain of `m + 1` solutions in one class, with `m`, `M` and `N` definitions
  in `κ`, `|S|` and `[F : K]`. Roth's theorem is now derived from it.

Two things it taught. **A count cannot quote a finiteness theorem.** The large-solution bound needs
the statement inside Roth's proof with its parameters in view, and Layer 3.2 had it only inside
one proof by contradiction, with the parameters drawn from existentials; restructuring cost more
than the counting. And **the book's window hypothesis is one inequality too strict for its own
use**: Lemma 6.5.6 assumes `X > log 16/(c − 1)`, and 6.5.7 applies it at `X = log 16/(c − 1)`;
the proof needs only `≥`, which is what is stated. A solution equal to a target, which the book's
classes leave out, is put in a corner class, where the gap principle still holds.

Settled on 2026-09-22, the same day as 3.3 to 3.5: `DiophantineApproximation` **Layer 3.6**,
**Thue's theorem** (Thue 1909; Bombieri–Gubler 6.2.1), in
`DiophantineApproximation/{BinaryForm,ThueEquation}.lean`:

- `MvPolynomial.IsHomogeneous.finite_setOf_eval_eq` — a homogeneous `G ∈ ℤ[X, Y]` with three
  pairwise non-proportional linear factors over `ℂ` takes each value `m ≠ 0` at only finitely many
  `(x, y) ∈ ℤ²`, the hypothesis read literally as three linear forms of pairwise nonzero
  determinant each dividing `G`; under it `Polynomial.finite_setOf_eval_homogenize_eq`, the same
  for `g.homogenize d` with the hypothesis counted on the complex roots of `g`;
- `Real.finite_setOf_pow_abs_sub_div_mul_pow_le` — Roth's theorem for pairs of integers,
  `|ξ − x/y|^μ |y|^e ≤ C` finitely often when `e > 2μ`, the only approximation input;
- `Polynomial.two_mul_count_roots_lt_natDegree` — an irrational root of multiplicity `μ` of an
  integer polynomial with three distinct complex roots has `2μ < deg g`.

Two things it taught. **The route is not the book's, and the difference is the multiplicities.**
Bombieri–Gubler factor `G` into irreducible forms over `ℤ` and show that only one can carry
infinitely many solutions, so that the approximation argument only meets a separable form. Run
on `G` directly, the exponent at the nearest root is `d/μ`; it stays above `2` at an irrational
root, through `(minpoly ℚ r)^μ ∣ g`, and **drops to exactly `2` at a rational one** —
`X²(X² − 2Y²)` at `0` — where Liouville's inequality with exponent `1` replaces Roth's theorem.
And **Mathlib already had the binary form**: `Polynomial.homogenize` and
`homogenize_eq_of_isHomogeneous` make every homogeneous form in two variables the homogenization
of a polynomial in one, so the statement cost no definition. Only Roth's theorem over `ℚ` at one
place is used.

Settled on 2026-09-22, the same day as 3.3 and 3.4: `DiophantineApproximation` **Layer 3.5**,
**Mahler's theorem on the fractional parts of `(p/q)^k`** (Mahler 1957; Bombieri–Gubler 6.2.7
for `3/2`), in `DiophantineApproximation/{PrimeProducts,MahlerPowers}.lean`:

- `Nat.eventually_exp_neg_lt_abs_sub_round` — for coprime `p > q ≥ 2` and every `ε > 0`, the
  distance from `(p/q)^k` to the nearest integer exceeds `exp(−ε k)` for all but finitely many
  `k`; under it `Nat.finite_setOf_exists_int_abs_sub_ratPow_le`, which quantifies over *every*
  integer and so never uses the minimality of `round`;
- `Nat.primesOf` and `Rat.prod_padicNorm_natCast` — the primes of an integer as a
  `Finset Nat.Primes`, and the finite part of the product formula: over *the* primes of the
  number itself, `∏ |d|_l = 1/d` exactly.

Two things it taught. **The orientation of the auxiliary rational decides whether a gcd has to
be named.** The roadmap prescribed `β = p^k/(N q^k)`; its denominator is `N q^k/gcd(N, p^k)`,
whose prime factors need not divide `p q`, so the product over the primes of `q` is only an
estimate. With the reciprocal `β = N q^k/p^k` the denominator divides `p^k`, the product over
the primes of `p` is `1/β.den` exactly, and the whole cancellation is the height bound
`max |β.num| β.den ≤ 2 β.den`. And **Ridout's theorem is needed where Roth's is not enough**:
drop the two products over the finite places and the left-hand side is smaller by `p^{−2k}`, so
no `ε` makes the inequality hold. That is the concrete sense in which 3.5 is the acceptance test
of Layer 3.3 rather than of 3.2.

Settled on 2026-09-22, the same day as 3.3: `DiophantineApproximation` **Layer 3.4**, **Roth's
theorem on the projective line** — the Subspace Theorem for `Fintype.card ι = 2`
(Bombieri–Gubler Theorem 7.2.2 at `n = 1`, and Example 7.2.7) — in
`DiophantineApproximation/{ProjectiveTarget,ApproxProd,RothProjective}.lean`, in both
directions:

- `NumberField.approxProd` — the central quantity of the Subspace Theorem, the object Layer 6.3
  will be stated with, together with `NumberField.approxProd_smul`, its invariance under scaling,
  which is what makes the theorem a statement about subspaces;
- `NumberField.exists_finset_submodule_of_approxProd_le_card_two` — for two linearly independent
  forms at each place of `S` and `ε > 0`, the nonzero `x` with
  `approxProd x ≤ mulHeight x ^ (−2 − ε)` lie in finitely many proper subspaces of `K²`, that is,
  in finitely many points of `ℙ¹(K)`;
- `NumberField.finite_setOf_prod_min_one_le_card_two` — the converse: Roth's theorem of Layer 3.2
  for the forms `X₀` and `X₁ − α v X₀`, so that the two statements are the same statement.

Three things it taught. **The exceptional set is a set of points of `ℙ¹(K)`, and the point at
infinity is in it by force**: for the coordinate forms, `(0, 1)` makes one factor of `approxProd`
vanish, so it is a solution for every `ε` and every height while lying on no line `K ⬝ (1, β)`;
the roadmap's own "with `β = x 1 / x 0`" is the right reading of the proof and the wrong reading
of the theorem. **Linear independence enters exactly once, as a determinant**, and everything
local is Cramer's rule read at one absolute value — which is why the general `n` of Layer 6.3 is
a different problem and not a longer version of this one. And **the comparison between a form and
a target needs a constant that grows with the target**, since at `β = t + 1` the truncated factor
is `1` while the normalized value of the form is `1 / max(1, |β|)`; the constant is then paid for
the way Layer 3.3 pays for its Möbius map, by dropping the exponent into `(2, κ)` and letting
Northcott collect the rest.

⚠ One claim in the roadmap's conventions table was wrong: `approxProd` is invariant under scaling
only *given* the `LiesOver` hypotheses, since the numerator of a local factor is measured in `F`
and the denominator in `K`. And one fact Mathlib does not have turned out to be load-bearing —
that an infinite place and a finite place never have the same underlying absolute value
(`NumberField.InfinitePlace.val_ne_finitePlace_val`), needed the moment the `2^{|S|}` split has
to be extended off `S`, which is how Roth's theorem indexes its targets.

Settled on 2026-09-22, the day after 3.2: `DiophantineApproximation` **Layer 3.3**, **the
classical forms of Roth's theorem** (Bombieri–Gubler Remark 6.2.5, Theorems 6.2.3–6.2.4 and
Corollary 6.2.6; Roth 1955, Ridout 1958), in
`DiophantineApproximation/{RationalPlaces,RothInfinity,RothRational,Ridout}.lean`. Four
statements:

- `NumberField.finite_setOf_prod_onePointApprox_le` — Layer 3.2 with targets in `OnePoint F`, so
  that the point at infinity is a target, with local factor `(max 1 |β|_v)⁻¹`;
- `Real.irrationalityExponent_eq_two` — **Roth's theorem** as it is usually quoted: the
  irrationality exponent of a real algebraic irrational is `2`, whatever its degree;
- `Rat.finite_setOf_ridout` — **Ridout's theorem**: for real algebraic `ξ`, finite sets `S₁`,
  `S₂` of primes and `ε > 0`, finitely many `p/q` in lowest terms with
  `|ξ − p/q| ∏_{S₁}|p|_ℓ ∏_{S₂}|q|_ℓ ≤ max(|p|, q)^(−2−ε)`;
- `Rat.finite_setOf_apply_intCast_sub_le` — the **`p`-adic form**: finitely many `n ∈ ℤ` with
  `|α − n|_w ≤ |n|^(−1−ε)`.

Three things it taught. **Targets at infinity are a theorem, not a choice of data**: the roadmap
listed them beside the three classical forms, but `β ↦ β⁻¹` *exchanges* the targets `0` and `∞`
instead of removing `∞`, so a mixed configuration needs `β ↦ (β − c)⁻¹` with `c` off every
target, a distortion estimate at each place, and the room in `κ > 2` to absorb the constant —
and the other three forms are instances *given* it. The **`p`-adic form gains its exponent at the
infinite place**, where a rational integer has local factor exactly `H(n)⁻¹`; with the `p`-adic
place alone Roth's theorem gives only `2 + ε`, so `OnePoint` is load-bearing and not
presentational. And the layer's real cost was a **dictionary Mathlib has in two halves that do
not meet**: Ostrowski's theorem for `ℚ` gives an absolute value *equivalent* to `padicNorm p`,
`NumberField.FinitePlace` gives a normalized one, and the exponent between them is exactly what
Ridout's `2 + ε` cannot afford to lose. `Rat.exists_prime_padic_eq` pins it to `1`, by a height
computation rather than a valuation-theoretic one.

⚠ One formula in the roadmap was wrong, at one point: the factor at the target `∞` is
`(max 1 |β|_v)⁻¹`, and the `min 1 (|β|_v)⁻¹` the roadmap writes is Lean's junk `0` at `β = 0`
where the value is `1`. Two acceptance tests the roadmap had deferred are landed here: that
**Roth's theorem is false at `κ = 2`** (Dirichlet, at `ξ = √2 − 1`), which Layer 3.2 could not
state, and `irrationalityExponent (2^(1/3)) = 2`, which Layer 1.1 could only bound between `2`
and `3`.

Settled on 2026-09-21, after 3.1 the same day: `DiophantineApproximation` **Layer 3.2**,
**Roth's theorem** (Bombieri–Gubler Theorem 6.4.1; Roth 1955, Ridout 1958, Lang), in
`DiophantineApproximation/{GlobalBound,MvPolynomialEvalBound,RothLocalBound,RothClass,
RothKeyInequality,RothAuxiliary,RothTheorem}.lean`. For a number field `K`, a finite extension
`F/K`, two typed finsets of places of `K`, an absolute value `w v` of `F` over each and a target
`α v ∈ F`, and any `κ > 2`, the set of `β ∈ K` with

```text
(∏ v ∈ S∞, min 1 |β − α v|_v ^ mult v) * ∏ v ∈ S₀, min 1 |β − α v|_v ≤ H(β)^(−κ)
```

is finite: `NumberField.finite_setOf_prod_min_one_le`. The proof is the book's five steps, and
every input was already in the tree — the index theorem (2.6), Roth's lemma (2.7), the
Hasse–Taylor expansion (2.1), the approximation classes (3.1) and Northcott.

Two things it taught. **Step IV is the product formula over all the places, not the fundamental
inequality over `S`**: the roadmap's own route said "bound `Q(β)` below by 0.4", and that cuts the
product down to `S`, where the local factors of the coefficients of `Q` are not controlled by its
height; charging `h(Q)` and the `h(β j)` twice would have proved the theorem only for `κ > 4`.
The statement that is needed, `NumberField.one_le_of_forall_apply_le_sum`, is the one thing the
milestone had to add, and Layer 0.4 turns out not to be on the path to Roth's theorem at all.
And **nothing tends to infinity**: the book's `D → ∞` is replaced by one explicit `D`, because
every error term but `([K : ℚ] + 2 ∑ w_v) log (D + 2)` is `O(D/L)` and is killed by choosing `L`
before `D`. No filter, no `IsLittleO`, no `Tendsto`. What the milestone actually cost was the
parameter order — `ε`, `N`, the number of variables, `σ`, `L`, `M`, the solutions, `D`, each
depending on all the earlier ones — which is why the book states it as a list.

Settled on 2026-09-21, after 2.7 the same day: `DiophantineApproximation` **Layer 3.1**,
**approximation classes** (Bombieri–Gubler 6.4.2–6.4.4), in
`DiophantineApproximation/{ApproximationClass,IndependentHeights}.lean`. Mahler's reduction: for
a finite index set `A` and a family `φ a : X → [0, 1]` with `∑ a, φ a x ≤ 1`, the cells of side
`1/N` cutting the unit simplex classify the points of `X`; there are `(N + |A|).choose |A|`
labels — exactly, `Set.ncard_setOf_sum_le` — so an infinite `X` has an infinite class, and inside
any infinite subset of a number field Northcott's theorem produces an `(L, M)`-**independent**
sequence, `h(β 0) ≥ L` and `h(β (j+1)) ≥ M h(β j)`. The two reductions together are
`NumberField.exists_cellIndex_eq_and_isHeightIndependent`, which is what the proof of Roth's
theorem opens with.

The milestone's own abstraction is the load-bearing decision: nothing in 6.4.2–6.4.3 is about
places, heights or number fields, and over a number field the index set is not a set of places at
all but the disjoint union of the two typed finsets the conventions pin. Lemma 6.4.3 comes out as
an *equality* — adding one coordinate for the slack `N − ∑ a, c a` makes the labels the tuples on
`Option A` summing to `N`, which is Mathlib's `Finset.card_finsuppAntidiag_nat_eq_choose` — with
no induction and no hockey-stick identity. What the milestone did not name, and what the
consumers will actually quote, is the book's (6.9): the class traps each local factor between two
powers of the product, `Λ^((c a + 1)/N) < f a ≤ Λ^(c a / N)`, replacing `|A|` unrelated
quantities by one raised to `|A|` exponents known to within `1/N`; the upper half is attained, so
its exponent is not off by one. This is the first milestone of the roadmap that needed nothing
new from Mathlib.

Settled on 2026-09-21, after 2.6 the same day: `DiophantineApproximation` **Layer 2 is complete** —
Layer 2.7, **Roth's lemma** (Bombieri–Gubler's Lemma 6.3.7, with the base case 6.3.9), in
`DiophantineApproximation/{HeightTransport,IndexRename,PolynomialDeterminantHeight,
RothDecomposition,RothDeterminant,RothBaseCase,RothEstimates,RothLemma}.lean`. For a nonzero `P`
in `m` variables over a number field with `degreeOf j P ≤ d j`, degrees dropping by a factor at
least `σ ≤ 1/2` at every step, and a point `ξ` with `σ⁻¹ (h(P) + 4 m d 0) ≤ d j h(ξ j)`, the index
of `P` at `ξ` is at most `2 m σ^((1/2)^(m−1))` — `MvPolynomial.index_le_of_degree_ratio`, at the
book's constants, so that Layer 5.3 can quote it as the book does.

The induction is **not** on `σ`. Parameterised by `θ` with `σ = θ^(2^m)` the inductive step
replaces `θ` by `θ²` and leaves `σ` fixed, so every hypothesis carries over verbatim to the
recursive call and no `Real.rpow` occurs anywhere inside the proof; the book's exponent is one
change of variable made once at the end. The constant `2 m` is then uniform — including in one
variable, where the first attempt needed the sharper `1` — because at `θ ≥ 1/2` the conclusion is
free: a nonzero polynomial of partial degrees at most `d` has index at most the number of
variables. That reduction to `θ < 1/2` is what gives the two halves of the quadratic estimate
their margin.

Three things the milestone's route did not say. The separated variable is `X 0`, because
Mathlib's `finSuccEquiv` splits off the first variable and Roth's lemma splits off the one of
*smallest* degree, so the induction runs with the degrees increasing and the book's form is one
`rename Fin.rev` at the end. Both families of the decomposition `P = ∑ f_i g_i` are independent
not by minimality of the number of terms but because the first is chosen to be a *basis* of the
span of the coefficients — after which the independence of the second is a statement about a
linear functional, and the degrees of the two Wronskians are read off the determinant by
`degreeOf_mul_eq` rather than off the families. And the height of the determinant cannot be
assembled from projective bounds on its Leibniz expansion at all: `H(N X + 1) = N` while both
summands have height `1`, so the estimate is made at every absolute value and transported once —
which needed the transport with a **one-sided** nonarchimedean bound, the general form of the
lemma 2.6 wrote in one special case.

The arithmetic that has to fit is `log p! + 2 (∑ j, d j) p log 2 ≤ 4 p d`. It fits because the
local estimate for a product charges the *smaller* support count rather than the total degree —
the difference between `2^(D p)` and `2^(D p (p+1)/2)`, and `p` is as large as the smallest
degree — and because `log 2 < 0.694`; with only `log 2 ≤ 1` the milestone's constant `4` would be
wrong.

Settled on 2026-09-21, after 2.5 the same day: `DiophantineApproximation` Layer 2.6 landed —
**the auxiliary polynomial** (Bombieri–Gubler's Lemma 6.3.4, the index theorem), in
`DiophantineApproximation/{BoxMonomial,MonomialHeight,IndexConditions,AuxiliaryPolynomial}.lean`.
Given a finite extension `F/K` of degree `r`, points `α k ∈ F^m` and orders `t k > 0` with
`r ∑ k, V_m(t k) < 1`, every `δ > 0` has a `D₀` beyond which every multidegree `d` carries a
nonzero `P` over `K` with `degreeOf j P ≤ d j`, index at least `t k` at each `α k`, and
`h(P) ≤ r/(1 − r ∑ V_m(t k)) · ∑ k, ∑ j, V_m(t k)(h(α k j) + log 2 + δ) d j` in absolute
logarithmic heights. That `ε`–`D₀` form is the reading of the book's `o(1)` every application
uses.

The route the roadmap named was one layer off, and finding that out was most of the work.
`ArithmeticHeights` Layer 5.7 packages the relative Siegel lemma on the coefficients of a
polynomial of bounded **total** degree — a simplex of monomials — and Lemma 6.3.4 bounds the
**partial** degrees, which is a box. Neither shape contains the other usefully, so 2.6 applies
Layer **5.6**, `exists_ne_zero_mem_ker_absMulHeight_le_relative_rank`, which is stated for an
arbitrary finite index type, to the box `∀ j, Fin (d j + 1)` directly and carries its own
coefficient dictionary. 5.7 is a sibling of this milestone rather than an ancestor of it, and the
rank strengthening that 5.7 once sent 5.6 back for is invisible here: what Layer 2.5 counts is
the number of *conditions*, and `Matrix.rank_le_card_height` is all 2.6 says about the rank.

The height of one condition row costs nothing but the binomial coefficient. A row entry is
`(∏ j, (I j).choose (μ j)) ∏ j, α j ^ (I j − μ j)`, a multiplication table over the variables, so
Mathlib's Segre relation `Height.mulHeight_fun_prod_eq` gives the row's height as a product of
one-variable heights **exactly**; and the tuple of powers `α ^ k, k ≤ d`, has height `H(α)^d`
exactly, which Mathlib does not have and which is proved here by comparing it place by place with
the pair `(α^d, 1)`. The only estimate made anywhere is `(I j).choose (μ j) ≤ 2^{d j}`, and that
is the `+ log 2` of the milestone's bound — the `+ δ` pays for something else.

What `δ` pays for is three quantities of three different orders, and that is the whole content of
the book's `o(1)`: the lattice-point correction `(1+ρ)^m − 1` is `O(m²/D₀)`, the `√M` by which
Siegel's Arakelov normalisation exceeds the sup-norm one contributes `½ log M`, and the
discriminant of `K` contributes a constant. All three are `o(∑ j, d j)`. The transport from local
factors to the height that Layer 2.1 had recorded as missing from `ArithmeticHeights` turned out
to be three lines in the one-input form 2.6 needs, with `finprod_induction` doing the work one
would have expected a finite-support argument to do.

`m = 0` is excluded by the hypothesis rather than handled by the proof — `V₀(t) = 1`, so
feasibility reads `r N < 1` and forces `N = 0` — and that is right, since a nonzero polynomial in
no variables is a constant, of index `0` everywhere. It is recorded as a rejection test, beside
the one that says `r S < 1` does not imply `r(1+ε)S < 1`, which is why `ε` has to be chosen
before `D₀`.

Settled on 2026-09-21, after 2.4 the same day: `DiophantineApproximation` Layer 2.5 landed —
**counting and volume** (Bombieri–Gubler 6.3.3, the counting inside Lemma 6.3.4, Lemma 6.3.5 and
(7.23)–(7.25)), in `DiophantineApproximation/CountingVolume.lean`. Three estimates were asked
for; they turned out to be **one**. A single Chernoff bound in `m` coordinates —
`∫_{∑ x j ≤ s} ∏ j, g (x j) ≤ exp (λ s) (∫ exp (−λ x) g x)^m` for any nonnegative weight `g` —
proves both exponential tails, at the indicator of `[0,1]` and at the Beta`(1,n)` density of one
coordinate of the standard simplex, and what separates them is a single pointwise inequality
about `exp`.

Three of the four hypotheses the book carries turned out to be artefacts of its proof and came
out: `ε ≤ 1/2` in Lemma 6.3.5 is vacuous, and `0 < λ ≤ n + 4` and `η ≤ 2/(n+1)` in (7.24)–(7.25)
are the price of truncating an alternating series after three terms and pairing off the tail —
where the pointwise bound `exp(−u) ≤ 1 − u + u²/2`, three lines from Mathlib's
`Real.quadratic_le_exp_of_nonneg` and `(1+u+u²/2)(1−u+u²/2) = 1 + u⁴/4`, gives the same three
terms for every `u ≥ 0`. The one hypothesis that is load-bearing is `t > 0` in the upper
lattice-point bound, and it is recorded as a rejection test: at `t = 0` the origin is always an
admissible lattice point while the region has no volume.

The constant `6` in `V_m((1/2−ε)m) ≤ exp(−6 m ε²)` is `6^k k! ≤ (2k+1)!`, sharp at `k = 1`: the
termwise comparison of the series of `sinh u` with that of `exp(u²/6)`. Mathlib has no
inequalities for `Real.sinh` at all, so that one is new here, and it is the only place in the
layer where a power series is summed. The lattice-point comparison is one covering argument in
both directions — boxes of side `1/d j` cover the region, which gives the lower bound with no
disjointness, and the same boxes fit inside `(1 + ρ) 𝒱_m(t)`, which gives the upper bound from
Haar scaling. What could not be stated the book's way is the *multihomogeneous volume*: the
book's own reduction of it to a one-variable integral is the volume `r^k/k!` of a simplex, which
Mathlib does not have; against the normalised density the factor `(n!)^{−m}` cancels and the
estimate is the proportion the milestone asked for.

Settled on 2026-09-21, after 2.3 the same day: `DiophantineApproximation` Layer 2.4 landed —
**the generalized Wronskian criterion for linear independence** (Bombieri–Gubler's Proposition
6.3.10), in `DiophantineApproximation/{Wronskian,GeneralizedWronskian}.lean`. Over a field of
characteristic zero, polynomials in any number of variables are linearly independent over the
field exactly when some determinant `det (∂_{μ i} φ j)` of Hasse derivatives, with the `i`-th row
differentiating at total order at most `i`, is not the zero polynomial. It is what Roth's lemma
differentiates with, and the bound on the orders is part of the statement, because it is what
keeps the degrees of the Wronskian under control.

The milestone advertised one thing and cost another. It does reduce to a one-variable criterion
that Mathlib does not have — `Polynomial.wronskian` is the two-polynomial determinant, built for
Mason–Stothers — but that criterion is where the work is, and the reduction is cheap. The
one-variable half is proved by *leading coefficients*, not by the classical argument that
differentiates a relation over the field of rational functions: every term of the Leibniz
expansion of the Wronskian sits in the same degree, because differentiating `i` times lowers a
degree by `i` whichever column it happens in, so the top coefficient of the Wronskian of a family
with pairwise distinct degrees `d j` is the determinant of the binomial coefficients
`(d j).choose i`. That determinant is nonzero exactly because **a polynomial with `n` terms
cannot vanish to order `n` at `1`** — apply the Euler operator `p ↦ t p'`, which lowers the order
of vanishing at `1` by at most one and multiplies `t^d` by `d`, and read off a Vandermonde
determinant in the exponents. That lacunary statement is the only arithmetic in the milestone.

Three findings went back into the roadmap. **The chain rule is Layer 2.1's Taylor formula once
more, and the order bound is not imposed but produced**: substituting `x_s ↦ t^{e_s}` and then
expanding around `t = a` is the same as translating the variables to `a^e` and then substituting
`x_s ↦ (a + u)^{e_s} − a^{e_s}`, polynomials with zero constant term, so the coefficient of `u^i`
cannot see a derivative of total order above `i`. No Faà di Bruno formula appears anywhere.
**Nothing is assumed about the variables**: the Kronecker weights have only to separate the
finitely many exponent vectors that occur, and they are found by avoiding the roots of finitely
many nonzero integer polynomials — an argument that never enumerates the variables, where the
usual base-`B` digit construction would have to. And **the easy half is uniform**: a linear
relation over the field is a relation between the columns, so it kills the determinant at every
family of orders at once, in every characteristic, using no property of the derivative. The
rejection test is `1` and `X²` over `ZMod 2`: independent, and every admissible Wronskian
vanishes, in one variable and in several.

Settled on 2026-09-21, after 2.2 the same day: `DiophantineApproximation` Layer 2.3 landed —
**the index of a polynomial at a point is a valuation, in any characteristic**
(Bombieri–Gubler 6.3.2), in `DiophantineApproximation/{WeightedOrder,PolynomialIndex}.lean`. The
index counts a derivative in the variable `j` as `1 / d j` of a vanishing, and it is the quantity
Roth's lemma is a statement about.

The milestone is one identity about coefficients, and the identity is Layer 2.1's. Translating so
that the point becomes the origin turns the Hasse derivatives at the point into the coefficients
at `0` — `coeff μ (P (X + α)) = (∂_μ P)(α)`, the substitution formula of 2.1 read as a statement
about one polynomial instead of two — after which the index mentions neither a derivative nor a
point: it is the least weight of a monomial occurring in the translate. That is why the milestone
took two files rather than the one it asked for. `WeightedOrder.lean` proves the valuation
properties for the weighted order of a support, over any commutative semiring and with nothing
assumed about the variables at all; `PolynomialIndex.lean` is the translation and three lines of
rewriting per theorem.

Three findings went back into the roadmap. **Multiplicativity needs no monomial order**: the
textbook proof refines the weight by a term order so as to name a unique lowest term in each
factor, which would need the variables well-ordered — a hypothesis the statement does not have —
while the lowest weighted *homogeneous parts* are polynomials rather than terms and multiply
because Mathlib's weighted homogeneous components are a grading. **`0 < d j` is never used**; the
theorems ask only `0 ≤ d j`, and the reason to keep reading strict positivity is that Lean's
`k / 0 = 0` makes a variable of weight `0` invisible to the index rather than making the index
infinite, which is the opposite degeneration. And the agreement with `Polynomial.rootMultiplicity`
in one variable **needs no domain** — it is the trailing degree of the translate over any
commutative ring — while `P ≠ 0` cannot come out, since `rootMultiplicity a 0 = 0` where the
index is `⊤`. Two rejection tests pin the rest: over `ZMod 2` the square of a variable has index
`2` at the origin while its `pderiv` is zero, which is what Layer 2.1 exists for, and over
`ZMod 4` the square of `2 X` is `0`, whose index is `⊤`, while the two indices add up to `2`.

Settled on 2026-09-21, after 2.1 the same day: `DiophantineApproximation` Layer 2.2 landed —
**the height of a product of polynomials in disjoint sets of variables is the product of the
heights, exactly and at every absolute value** (Bombieri–Gubler's Proposition 1.6.2), in
`DiophantineApproximation/DisjointVariables.lean`. This is the identity `h(U · V) = h(U) + h(V)`
on which Roth's lemma turns; Gelfond's inequality would lose a constant there that the induction
cannot afford.

The milestone is not a height computation. It is one identity about coefficients — the
antidiagonal of an exponent of `σ ⊕ τ` meets the two supports in a single point, so each
coefficient of the product is a single product of coefficients, over any commutative semiring —
and after it the height statement is an instance of Mathlib's Segre relation
`Height.mulHeight_fun_mul_eq`. The bridge to that lemma is `Finsupp` and not `MvPolynomial`,
because it is stated for tuples over a *finite* index type while the exponents of a polynomial
are `σ →₀ ℕ`, which is not one; `ArithmeticHeights` 2.1's reindexing lemma on the supports is
what crosses the gap, and the general statement — a finitely supported family that is the
multiplication table of two others has the product of their heights — is written so that it can
move into that roadmap unchanged. Two findings went back into the roadmap. **No ultrametric
hypothesis appears anywhere**, where Gauss's lemma cannot do without one: with disjoint variables
the archimedean places behave exactly as the finite ones do, because there is no sum of several
terms to apply a triangle inequality to. And the *local* identity needs no hypothesis at all,
including `f = 0`, while the height identity needs both factors nonzero — purely because
`mulHeight 0 = 1` is a junk value, which a rejection test pins at `1` against `2`. Renaming the
variables injectively leaves the height alone, which came free and is the form Layer 2.7 will
call: two injections with disjoint ranges into one variable set.

Settled on 2026-09-21: `DiophantineApproximation` Layer 2.1 landed — **Hasse derivatives of
polynomials in several variables**, `MvPolynomial.hasseDeriv`, with the defining equation on a
monomial (Bombieri–Gubler's (6.1)), the coefficient formula, the composition law, the Leibniz
rule, the Taylor expansion, agreement with Mathlib's one-variable `Polynomial.hasseDeriv`, the
comparison with the iterated `pderiv`, the degree bounds, and the size estimate at one absolute
value — in `DiophantineApproximation/MvHasseDeriv.lean`, `…/MvHasseDerivTaylor.lean` and
`…/MvHasseDerivHeight.lean`. This is the first milestone of the Roth machinery, and Mathlib has
no multivariate Hasse derivative of any kind.

What the milestone turned on was the *order* of the proofs, not their difficulty. The Leibniz
rule cannot be reached by induction on the order `μ`: the composition law reads
`∂_(single j 1) ∘ ∂_ν = (ν j + 1) • ∂_(ν + single j 1)`, and inverting `ν j + 1` is not allowed
in a commutative semiring — and characteristic `p` is exactly where the Hasse derivative earns
its keep, as a rejection test in the first file records (over `ZMod 2`, `∂_(single j 2) (X j²) =
1` while `pderiv j (X j²) = 0`, which is why Layer 2.3's index is a valuation in every
characteristic). What works instead is the **substitution formula** `coeff μ (P (C X + X)) =
∂_μ P`, from which the Leibniz rule is `coeff_mul` applied to a ring homomorphism and the Taylor
expansion is one evaluation; and the substitution formula is proved by induction over `C`, `+`
and `· * X j`, so the only differentiation done by hand is against a single variable — which is
Pascal's rule. Three further corrections went back into the roadmap: the ring may be a
`CommSemiring`; the composition law cannot be written as a `Finsupp.prod` of single-variable
operators, because `Module.End` is not a commutative monoid; and the height constant is
`2 ^ totalDegree`, since the roadmap's `2 ^ (∑ j, degreeOf j P)` is undefined for an infinite
variable set. The height side stops at the local factor: carrying it to `mulHeight` needs a
one-input, one-sided transport that `ArithmeticHeights` does not have, since its Gauss-lemma
transport demands *equality* at the nonarchimedean places.

Settled on 2026-09-20: `DiophantineApproximation` Layer 1.3 landed **except for Wirsing's first
two inequalities** — `koksmaExponent n ξ ≤ mahlerExponent n ξ` for every real `ξ`, the box
principle `n ≤ mahlerExponent n ξ` for `ξ` not algebraic of degree at most `n`, `mahlerExponent
n ξ ≤ d − 1` at an algebraic `ξ` of degree `d` with Liouville's inequality for the value of an
integer polynomial underneath it, and **Wirsing's third inequality**
`mahlerExponent n ξ ≤ koksmaExponent n ξ (mahlerExponent n ξ + 1 − n)` — in
`PolynomialEval.lean`, `KoksmaComparison.lean`, `BoxPrinciple.lean`, `AlgebraicExponent.lean`,
`SimultaneousBox.lean`, `RootLocation.lean`, `WirsingSystem.lean` and `WirsingThird.lean`.
Five findings. `w_n^* ≤ w_n` needs **no** hypothesis on `ξ`: the only Koksma solution that is not
a Mahler solution is the minimal polynomial of `ξ` itself, and a primitive irreducible integer
polynomial with a given real root is unique up to sign. The exponent `d − 1` needs the **norm**
and not the height — Layer 0.4's fundamental inequality proves only `w_n ≤ d`, and the sharp
bound comes from `∏_w w(γ)^{mult w} = |N γ| ≥ 1` for an algebraic integer, with the real place
the one left unestimated. Wirsing's third inequality — the one that gives his conjecture
`n ≤ w_n^*` wherever `w_n = n` — needs **no root separation**: it builds its own polynomial, small
at `ξ` and bounded at `n − 1` further points, and a **counting** argument (one root per point,
`n` points, degree `n`) makes the root near `ξ` simple and therefore equal to its own conjugate,
hence real. Dirichlet's box principle at `n` points at once replaces Minkowski's linear forms
theorem there, at the cost of a constant. Wirsing's **first two** inequalities remain out of
reach, because they start from an arbitrary approximant whose nearest root need not be real: the
first needs `|ξ − α| ≤ c |P ξ| H(P)^{n−2}`, which is the product formula
`disc P = lc(P)^{2d−2} ∏_{i<j} (α_i − α_j)²` that Mathlib lacks, and in the range
`n ≤ w_n ≤ 2n − 3` it needs the second, which is Wirsing's generalized-resultant construction.
Both are also **false at `n = 0`**, where both exponents vanish; the roadmap's prototypes now
carry the missing `1 ≤ n`. Both are **optional**, and the roadmap now says so: their only
consumer is Layer 1.4, the coincidence of Mahler's and Koksma's classifications, which no later
layer consumes in turn — and 1.4 needs the second of them, not the first, since `w_n^* ≤ w_n`
with `w_n + 1 ≤ 2 w_n^*` gives `w/2 ≤ w^* ≤ w` and so matches the four classes one for one,
while `w − 1 ≤ w^* ≤ w` leaves the `A`-class open. Layer 7.3, the one milestone that names 1.3
by number, is served by the third alone.

Settled on 2026-09-20: `DiophantineApproximation` Layer 1.2 landed — Mahler's `w_n` and Koksma's
`w_n^*` as `ℝ≥0∞`-valued suprema over infinite sets of integer polynomials, with monotonicity in
the degree, `w_1 = w_1^* = irrationalityExponent − 1`, the invariance of both under the rational
Möbius group, and the restriction of `w_n` to primitive and to **irreducible** polynomials — in
`PolynomialSupNorm.lean`, `MahlerExponent.lean`, `IrreducibleExponent.lean` and
`KoksmaMobius.lean`. Mathlib already had the naive height (`Polynomial.supNorm`); what it lacked
is Northcott's theorem for integer polynomials, and the argument that keeps the solutions infinite
is a *height gap* — below a threshold, a nonzero value at `ξ` forces a tall polynomial — not a
count of fibres. Gelfond's inequality (`ArithmeticHeights` 2.3, archimedean half only) enters
twice: for irreducibility, and unavoidably for Koksma's Möbius invariance. Acceptance test:
`koksmaExponent 1 = mahlerExponent 1 = irrationalityExponent − 1`. The split is again by import:
four files, of which two know nothing about `ArithmeticHeights`.

Settled on 2026-09-20: `DiophantineApproximation` Layer 1.1 landed — the irrationality exponent
as an `ℝ≥0∞`-valued supremum over Mathlib's `LiouvilleWith`, with the value `1` at a rational,
Dirichlet's lower bound `2`, the characterization `= ⊤ ↔ Liouville`, invariance under the rational
Möbius group, two characterizations by the quality of approximations, and Liouville's bound by the
degree — in `IrrationalityExponent.lean` and `LiouvilleExponent.lean`. Two lemmas Mathlib lacks
carry it: Dirichlet's theorem in `LiouvilleWith`'s shape (where the gap is the *denominator*, not
the approximation) and `LiouvilleWith.inv`. Acceptance tests: `irrationalityExponent (√2) = 2`,
and Mathlib's `Liouville.transcendental` re-derived. The split is by import, not by mathematics:
the first file knows no number field.

Settled on 2026-09-20: `DiophantineApproximation` Layer 0.4 landed, and with it the whole of
Layer 0 — the fundamental inequality, Liouville's inequality over an extension of number fields,
and Liouville's theorem over `ℝ` with the constant named, in `FundamentalInequality.lean` and
`LiouvilleInequality.lean`. Mathlib's `Liouville.exists_pos_real_of_irrational_root` is derived
from the last of these as the milestone's acceptance test. 0.4 uses nothing from 0.2 and is the
first consumer of `ArithmeticHeights` 0.3 (`NumberField.mulHeight₁_pow_finrank`).

Settled on 2026-09-20: `DiophantineApproximation` Layer 0.3 landed — the `S`-integers as a
localization of `𝓞 K`, Bombieri–Gubler's Proposition 5.3.6, and the height of an `S`-integral or
primitive point — in `SIntegerLocalization.lean` and `SAdicHeight.lean`. It is the first file of
that roadmap to consume `ArithmeticHeights`, which is why `NumberField.exists_mem_asIdeal_iff_eq`
stopped being `private` in `ArithmeticHeights/SUnitTheorem.lean`.

Settled on 2026-09-20: the repository holds **two** libraries, one per roadmap, and every gate
reads both. `lakefile.lean` declares `DiophantineApproximation` beside `ArithmeticHeights` with
the same lean options; `scripts/source-modules.sh` carries the single list `LIBRARY_ROOTS` that
`guards.sh`, `lint-style.sh` and `lint-env.sh` read, and `Axioms.lean` and `ModuleSystem.lean`
carry the same list as `auditedRoots`. Adding a third roadmap is four lines.

Settled on 2026-09-15: every gate is wired and tested (`scripts/check.sh`); the Tau Ceti reference
copies are in place (`TauCeti/` and the unadapted part of `scripts/`, gitignored alongside the
Bombieri–Gubler PDF); the repo `LICENSE` is Apache-2.0, matching the Lean file headers and the
destination library; `Suggested.lean` moved out of the library glob into `Roadmap/`; the lakefile
carries Tau Ceti's lean options and the package is named `SubspaceTheorems`; the Mathlib require
pins `inputRev` to `master`.
