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
whose *statements* need those objects (Roth's lemma, the index theorem, the height of `V(Q)`,
Minkowski's second theorem over `K`) are specified in `README.md` and deliberately not prototyped
here: a prototype would have to restate those objects behind stand-ins. The declarations elaborate
against the pinned Mathlib and are stated with `sorry` (allowed in this human-owned roadmap
library); what lands in `TauCeti/` must be proved.

Names here are unqualified inside `TauCetiRoadmap.DiophantineApproximation` so that the prototype
does not occupy Mathlib's root namespaces. In `TauCeti/` they take the names `README.md` pins:
`irrationalityExponent`, `mahlerExponent` and `koksmaExponent` sit in `Real`, `hasseDeriv` and
`index` in `MvPolynomial`, `approxProd` and `approxDomain` in `NumberField`.

**Landed milestones appear here as `example`s discharged by the library**, not as `sorry`s: a
milestone that `DiophantineApproximation/` proves is one whose signature has stopped drifting, and
the `example` is what certifies that the shape pinned here is the shape that was proved. Layers
0.1, 0.2, 0.3, 0.4, 1.1, 1.2, 2.1, 2.2, 2.3 and 2.4 are landed, and 1.3 is landed **except for
Wirsing's
first two inequalities, which are optional** — their only consumer is the optional Layer 1.4 — in
`DiophantineApproximation/{Nonarchimedean,PlacesOverFinite,PlacesOverInfinite,
PlacesOver,ConjugatePlaces,LocalExtension,SIntegerLocalization,SAdicHeight,FundamentalInequality,
LiouvilleInequality,IrrationalityExponent,LiouvilleExponent,PolynomialSupNorm,MahlerExponent,
IrreducibleExponent,KoksmaMobius,PolynomialEval,KoksmaComparison,BoxPrinciple,AlgebraicExponent,
SimultaneousBox,RootLocation,WirsingSystem,WirsingThird,MvHasseDeriv,MvHasseDerivTaylor,
MvHasseDerivHeight,DisjointVariables,WeightedOrder,PolynomialIndex,Wronskian,
GeneralizedWronskian}.lean`; 0.1's three signatures
below survived verbatim, 1.1's definition
survived verbatim and one of its five theorems lost a hypothesis, 1.2's two definitions survived
and its `naiveHeight` abbreviation did not, 1.3's two elementary signatures survived up to a
**name collision**, 2.1's definition survived verbatim and its one prototyped theorem survived
with `R` weakened to a `CommSemiring`, 2.2 had nothing prototyped here at all and is stated
below for the first time, 2.3's definition survived verbatim while all three of its theorems
lost hypotheses — twice the strict positivity of the weights, once `IsDomain` as well — 2.4's
one prototyped theorem survived verbatim, and 0.2,
0.3 and 0.4 had none to survive: they are prototyped here for the first time. What the proofs
taught:

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

/-- **Layer 7.3** (Schmidt 1970). The exponents of a real algebraic number. At `n = 1` this is
Roth's theorem. -/
theorem mahlerExponent_of_isAlgebraic {α : ℝ} (hα : IsAlgebraic ℚ α) {n : ℕ} (hn : 1 ≤ n) :
    Real.mahlerExponent n α = (min n ((minpoly ℚ α).natDegree - 1) : ℕ) ∧
      Real.koksmaExponent n α = (min n ((minpoly ℚ α).natDegree - 1) : ℕ) :=
  sorry

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

end Machinery

/-! ## Layers 3 and 6: Roth's theorem and the Subspace Theorem -/

section Subspace

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι]

/-- **The central quantity.** For finite sets `Sinf`, `Sfin` of places of `K`, an absolute value
`w v` of `F` over each, and linear forms `L v i` over `F`:
`∏_{v ∈ S} ∏ᵢ ‖L_{v,i}(x)‖_v / ‖x‖_v` in Mathlib's normalization, for a point `x` of `Kⁿ⁺¹`. The
forms and the absolute values are indexed by the underlying absolute value of a place, so that one
family serves both finsets. -/
def approxProd (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) (x : ι → K) : ℝ :=
  (∏ v ∈ Sinf, (∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ^ v.mult) *
    ∏ v ∈ Sfin, ∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)

/-- **Layer 3.2** (Roth; Ridout; Lang; Bombieri–Gubler, Theorem 6.4.1). Roth's theorem over a
number field with a finite set of places and targets in a finite extension, each measured by an
absolute value over the place. -/
theorem finite_setOf_prod_min_one_le (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ)}.Finite :=
  sorry

/-- **Layer 3.3.** Roth's theorem, 1955. -/
theorem irrationalityExponent_eq_two {α : ℝ} (hα : IsAlgebraic ℚ α) (hirr : Irrational α) :
    Real.irrationalityExponent α = 2 :=
  sorry

/-- **Layer 3.5** (Mahler 1957). The distance from `(p/q)^k` to the nearest integer. -/
theorem eventually_exp_neg_lt_abs_sub_round {p q : ℕ} (hq : 2 ≤ q) (hpq : q < p)
    (hcop : p.Coprime q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in Filter.atTop,
      Real.exp (-ε * k) < |((p : ℝ) / q) ^ k - round (((p : ℝ) / q) ^ k)| :=
  sorry

/-- **Layer 6.3** (Schmidt; Schlickewei; Evertse; Bombieri–Gubler, Theorem 7.2.2 with Remark
7.2.3). The Subspace Theorem: points in `K`, coefficients in a finite extension `F`. With `F = K`
and `w = id` it is the number-field form of Layer 6.2; with `K = ℚ` it is Schmidt's theorem for
forms with algebraic coefficients. `[Nontrivial ι]` is `n ≥ 1`, without which the statement is
false. -/
theorem exists_finset_submodule_of_approxProd_le [Nontrivial ι]
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
  sorry

/-- **Layer 6.4** (Bombieri–Gubler, Corollary 7.2.5). The affine form, for points with
`S`-integral coordinates; `S` is Mathlib's carrier for `S`-integers, finite places only, and every
infinite place is present. -/
theorem exists_finset_submodule_of_integer_of_prod_le [Nontrivial ι]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
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
  sorry

/-- **Layer 4.1.** The approximation domain of level `Q`: a set of points of `Kⁿ⁺¹`, with a
condition at every infinite place, at every place of `Sfin`, and integrality elsewhere. -/
def approxDomain (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) : Set (ι → K) :=
  {x | (∀ (v : InfinitePlace K) (i : ι), v (L v.1 i x) ≤ Q ^ c v.1 i) ∧
    (∀ v ∈ Sfin, ∀ i : ι, v (L v.1 i x) ≤ Q ^ c v.1 i) ∧
    ∀ v : FinitePlace K, v ∉ Sfin → ∀ j : ι, v (x j) ≤ 1}

/-- **Layer 4.1.** The weight of a system of exponents: the exponent of `Q` in the product of all
the local bounds, in Mathlib's normalization. -/
def approxWeight (Sfin : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ) : ℝ :=
  ∑ v : InfinitePlace K, v.mult * ∑ i, c v.1 i + ∑ v ∈ Sfin, ∑ i, c v.1 i

/-- **Layer 6.1.** The parametric Subspace Theorem: for exponents of negative weight, finitely
many proper subspaces contain every approximation domain of large level. This is the statement
the quantitative theory strengthens by counting `T`. -/
theorem exists_finset_submodule_forall_approxDomain_subset [Nontrivial ι]
    (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) (hc : approxWeight Sfin c < 0) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∃ Q₀ : ℝ, ∀ Q ≥ Q₀, ∃ W ∈ T, approxDomain Sfin L c Q ⊆ W :=
  sorry

/-- **Layer 7.1** (Bombieri–Gubler, Theorem 7.3.2). One linear form with algebraic coefficients,
in integer points. The hypothesis is that the value is nonzero, not that the coefficients are
independent. -/
theorem finite_setOf_abs_sum_mul_le {n : ℕ} (α : Fin (n + 1) → ℂ)
    (hα : ∀ i, IsAlgebraic ℚ (α i)) {ε : ℝ} (hε : 0 < ε) :
    {x : Fin (n + 1) → ℤ | 0 < ‖∑ i, α i * x i‖ ∧
      ‖∑ i, α i * x i‖ ≤ mulHeight (fun i ↦ (x i : ℚ)) ^ (-(n : ℝ) - ε)}.Finite :=
  sorry

end Subspace

/-! ## Layer 8: unit equations -/

section UnitEquation

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- **Layer 8.1** (Siegel; Mahler; Lang). The unit equation in two variables. -/
theorem finite_setOf_unit_add_unit_eq_one (S : Finset (HeightOneSpectrum (𝓞 K))) (a b : Kˣ) :
    {p : Kˣ × Kˣ | p.1 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧
      p.2 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧
      (a : K) * p.1 + (b : K) * p.2 = 1}.Finite :=
  sorry

/-- **Layer 8.2** (Evertse; van der Poorten–Schlickewei; Bombieri–Gubler, Theorem 7.4.2). The
unit equation in `n` variables: finitely many solutions with no vanishing subsum. The hypothesis
is not removable: `(u, −u, 1)` solves `x₁ + x₂ + x₃ = 1` for every unit `u`. -/
theorem finite_setOf_sum_unit_eq_one (S : Finset (HeightOneSpectrum (𝓞 K))) (a : ι → Kˣ) :
    {x : ι → Kˣ | (∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) ∧
      ∑ i, (a i : K) * x i = 1 ∧
      ∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, (a i : K) * x i ≠ 0}.Finite :=
  sorry

/-- **Layer 8.2.** The same for a finitely generated subgroup of `Kˣ`. -/
theorem finite_setOf_sum_mem_eq_one (Γ : Subgroup Kˣ) (hΓ : Γ.FG) (a : ι → Kˣ) :
    {x : ι → Kˣ | (∀ i, x i ∈ Γ) ∧ ∑ i, (a i : K) * x i = 1 ∧
      ∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, (a i : K) * x i ≠ 0}.Finite :=
  sorry

end UnitEquation

end

end TauCetiRoadmap.DiophantineApproximation
