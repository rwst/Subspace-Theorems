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
  with `sorry` and elaborate against the pinned Mathlib — 13 of them as the tree stands, Wirsing's
  first two inequalities of Layer 1.3 and Layers 1.4 to 8 of the `DiophantineApproximation`
  roadmap except 2.1, 2.2, 2.3 and 2.4, the first two of those and 1.4 marked **optional** there
  because no later layer consumes them —
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
libraries' build and out of every gate. As the tree stands it carries **20**, Layers 1.2 to 8 of the
`DiophantineApproximation` roadmap; Layers 0.1, 0.2, 0.3, 0.4 — all of Layer 0 — and 1.1 are
landed and appear there as `example`s discharged by the library. The dependency runs one way only, `Roadmap` on the
libraries, and `guards.sh` fails the build if a library ever imports the roadmap.

Every gate was tested against a violation, not only against a clean tree — a `sorry`, a 101-column
line, trailing whitespace, a wrong licence line, an undocumented `def`, a home-rolled `axiom`, a
file without `module`, each caught by exactly one gate. Every gate reads both library roots; the
single list of them is `LIBRARY_ROOTS` in `scripts/source-modules.sh`, and adding a roadmap to this
repository means adding its directory there and to `lakefile.lean` and nothing else. On the tree as
it stands: 93 library files, 2536 declarations audited and all within the allowlist, 1762 judged by
15 environment linters with no violations, headers and text linters clean.

## Still to settle

1. **No `formalization.yaml`.** Tau Ceti's is copied in `TauCeti/` as the model; ours would say:
   source = Bombieri–Gubler plus the two roadmaps, single human author, `sorry_count: 0`, the three
   allowlisted axioms — all of it now machine-checked by the gates rather than asserted.
2. **The shim ledger.** `ArithmeticHeights` Layers 0.3 and 6.5 both deliberately shadow an open
   Mathlib PR (mathlib4#41606, mathlib4#40791), which is exactly what `mathlib-shims.json` and
   `check-expired-mathlib-shims.py` exist to track, so that the vendored copy is deleted when
   upstream lands rather than quietly diverging.
3. **Pins.** Toolchain `v4.34.0`, Mathlib `1e043bcd5646` on `master` — ahead of Tau Ceti's
   `v4.34.0-rc1` / `653c36f019ec`, which is the allowed direction. Bumps stay forward-only.

Settled since: the Lean file headers all name "Ralf Stephan", `Arakelov.lean` included, so the
attribution question is closed.

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
