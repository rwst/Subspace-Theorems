import Mathlib

-- The library, one module per milestone. `Roadmap` may import `ArithmeticHeights`; the converse is
-- forbidden and `scripts/guards.sh` enforces it, so that no `sorry` can reach the library.
import ArithmeticHeights.Arakelov        -- Layers 0.1, 0.2
import ArithmeticHeights.Extension       -- Layer 0.3
import ArithmeticHeights.Absolute        -- Layer 0.4
import ArithmeticHeights.Affine          -- Layer 0.5
import ArithmeticHeights.Northcott       -- Layer 1.1
import ArithmeticHeights.MahlerMeasure   -- Layer 1.2
import ArithmeticHeights.NorthcottTheorem -- Layer 1.3
import ArithmeticHeights.Kronecker       -- Layer 1.4
import ArithmeticHeights.LowerBound      -- Layer 1.5
import ArithmeticHeights.Polynomial      -- Layer 2.1
import ArithmeticHeights.GaussLemma      -- Layer 2.2
import ArithmeticHeights.Gelfond         -- Layer 2.3
import ArithmeticHeights.LinearForm      -- Layer 2.4
import ArithmeticHeights.Matrix          -- Layer 2.5
import ArithmeticHeights.Plucker         -- Layer 3.1
import ArithmeticHeights.Subspace        -- Layer 3.2
import ArithmeticHeights.RowSpace        -- Layer 3.3
import ArithmeticHeights.CauchyBinet     -- Layer 3.4
import ArithmeticHeights.Hadamard        -- Layer 3.4
import ArithmeticHeights.Duality         -- Layer 3.5

/-!
# Arithmetic heights and Siegel's lemma: target signatures

**This file is not the roadmap and is not exhaustive.** The definitive document is the
roadmap, `ArithmeticHeights/README.md`, which every `README.md` below refers to.
The statements here suggest Lean forms for the milestones whose names and shapes are most likely
to drift, so that contributors and reviewers converge on them; discharging all of them finishes
neither a layer nor the roadmap.

Everything below is stated against Mathlib's `Mathlib/NumberTheory/Height/` (M. Stoll): the
`Height.AdmissibleAbsValues` class, `Height.mulHeight₁`, `Height.mulHeight`,
`Projectivization.mulHeight`, `NumberField.absMulHeight₁`, and the `Northcott` typeclass. None of
that is restated here; this roadmap consumes it.

## The two halves of this file

**Landed milestones appear as `example`s discharged by the library.** This file imports
`ArithmeticHeights`, so a milestone that has been proved is recorded here as its delivered
statement with the delivered declaration as the proof — a machine-checked index from each finished
milestone to the name that carries it, and the reason `lake build Roadmap` is worth running: if a
name or a shape drifts, this file stops compiling. Definitions are pinned through the lemma that
characterizes them, since several of them deliberately leave their bodies unexposed.

**Open milestones remain `sorry`s**, stated in the vocabulary the finished layers actually
deliver. Their names are unqualified inside `TauCetiRoadmap.ArithmeticHeights` so that the
prototype does not occupy Mathlib's root namespaces: `successiveMinimum` is the roadmap's own name,
`minorGcd` and `unitBallVolume` are local to this file, and the theorems about the height of a
subspace belong in `Submodule` when they land. Every height is Mathlib's
**relative** height over the fixed field unless it carries the `abs` prefix; a constant
transcribed from the literature is an absolute-height constant, and in the relative height it is
raised to `Height.totalWeight K`, exactly as Mathlib's `mulHeight₁_sum_le` carries
`#s ^ totalWeight K`.

## What the landed layers changed about the shapes below

Four of the pinned shapes did not survive contact with the proofs, and the `example`s record the
delivered form rather than the suggested one. The findings are argued in the roadmap, under the
milestones concerned.

* **The rank left the subspace height.** `subspaceMulHeight k V hV` is `Submodule.mulHeight V`:
  the rank is read off `V`, so the height is a total function of the subspace and `mulHeight (V ⊓
  W)` in 3.6 is well formed with no rank supplied. Every Layer 3 and Layer 5 signature stated in
  terms of it loses its rank arguments.
* **`minorDet` is not a definition.** The maximal minors are `exteriorPower.plucker m A.row`, by
  `exteriorPower.plucker_apply`, and the column enumeration is Mathlib's `Finset.orderEmbOfFin`,
  not the `Set.powersetCard.orderIsoOfFin` the milestone named, which does not exist.
* **Cauchy–Binet is ring-generic, and so are its "archimedean specializations".** `det (A Aᵀ) = ∑ₛ
  (det Aₛ)²` needs no ordered field and no real numbers, and the complex form is the same identity
  over a commutative star ring; `NumberField.InfinitePlace.det_map_embedding_mul_conjTranspose_self`
  is the one statement Layers 5.3 and 5.4 consume, at either kind of infinite place.
* **Gelfond's lower half needs hypotheses.** `p ≠ 0`, `q ≠ 0` and a number field — see the ⚠ under
  Layer 2.3 below.
* **The annihilator has to be transported before it has a height.** `Submodule.mulHeight` is
  defined on subspaces of `ι → K`, and the annihilator lives in the dual, so
  `mulHeight V.dualAnnihilator` does not typecheck: the identification along the standard basis is
  part of the statement, not a remark about it.

## ⚠ The roadmap is still preliminary

Milestone names and shapes may change again, including ones already implemented. What is recorded
below as landed is what the library proves today, not a settled API; the `example`s make a later
rename visible here rather than silently leaving this file behind.

The Layer 0.3 signatures are those of
[mathlib4#41606](https://github.com/leanprover-community/mathlib4/pull/41606) and deliberately
carry its names, so that adopting Mathlib's version is a deletion plus an import. Likewise Layer
6.5 follows [mathlib4#40791](https://github.com/leanprover-community/mathlib4/pull/40791).
-/

namespace TauCetiRoadmap.ArithmeticHeights

open Height NumberField Real Module Pointwise IntermediateField

noncomputable section

/-! ## Layer 0: normalizations and the extension dictionary -/

section Arakelov

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- **Layer 0.1 — landed** as `NumberField.arakelovMulHeight` in `ArithmeticHeights/Arakelov.lean`:
the ℓ² norm at the archimedean places, weighted by `InfinitePlace.mult`, and the sup norm at the
finite places. This is the normalization in which the Bombieri–Vaaler constants of Layers 5.3 and
5.4 are stated; `Height.mulHeight` uses the sup norm everywhere. Both live in the library and every
bound says which one it is in.

The zero tuple takes the junk value `1`, as for `Height.mulHeight`: the displayed product is `0`
there, which would falsify `1 ≤ arakelovMulHeight` and both comparisons of Layer 0.2 below, which
are stated without a `x ≠ 0` hypothesis. The definition is pinned here by the displayed formula
away from that value. -/
example {x : ι → K} (hx : x ≠ 0) :
    arakelovMulHeight x =
      (∏ v : InfinitePlace K, (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ)) *
        ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) :=
  NumberField.arakelovMulHeight_eq hx

/-- **Layer 0.1.** The logarithmic Arakelov height. As everywhere in this development, the
logarithmic height is *defined* as the logarithm of the multiplicative one and never
independently. -/
example (x : ι → K) : arakelovLogHeight x = log (arakelovMulHeight x) := rfl

/-- **Layer 0.1.** The one-variable (affine) case: the Arakelov height of the point `(x : 1)` of
the projective line. Its archimedean local factor is `((v x) ^ 2 + 1) ^ (v.mult / 2)`, so — unlike
in the sup-norm normalization — this is **not** `Height.mulHeight₁ x`; the library refutes the
identification with `NumberField.arakelovMulHeight₁_one`. `Projectivization.arakelovMulHeight` and
its logarithmic companion are the descent to projective space. -/
example (x : K) : arakelovMulHeight₁ x = arakelovMulHeight ![x, 1] := rfl

/-- **Layer 0.1.** The Arakelov height is invariant under scaling, by the product formula, so it
descends to projective space exactly as `Height.mulHeight` does. -/
example (x : ι → K) {c : K} (hc : c ≠ 0) :
    arakelovMulHeight (c • x) = arakelovMulHeight x :=
  NumberField.arakelovMulHeight_smul_eq _ hc

/-- **Layer 0.2, lower comparison.** The sup norm is at most the ℓ² norm at every place. -/
example (x : ι → K) : Height.mulHeight x ≤ arakelovMulHeight x :=
  NumberField.mulHeight_le_arakelovMulHeight _

/-- **Layer 0.2, upper comparison — the lemma that transports the literature's constants into
Mathlib's normalization.** The exponent is `totalWeight K = finrank ℚ K`, the sum of the local
degrees at the archimedean places. `ι` must be nonempty: on the empty index type both heights
take the junk value `1` while the right-hand side is `0`. It is sharp — the library records the
all-ones tuple as attaining it. -/
example [Nonempty ι] (x : ι → K) :
    arakelovMulHeight x ≤ (Fintype.card ι : ℝ) ^ ((totalWeight K : ℝ) / 2) * Height.mulHeight x :=
  NumberField.arakelovMulHeight_le_mulHeight _

/-- **Layer 0.2.** On a subsingleton index type the two normalizations agree — both are `1`, by
the product formula. ⚠ This is *not* `arakelovMulHeight₁ = mulHeight₁`, which is false: already
`arakelovMulHeight₁ (1 : K) = 2 ^ (Height.totalWeight K / 2 : ℝ)` while `mulHeight₁ (1 : K) = 1`.
The one-variable heights are related only by the two comparisons above, applied to `![x, 1]`. -/
example [Subsingleton ι] (x : ι → K) : arakelovMulHeight x = Height.mulHeight x :=
  NumberField.arakelovMulHeight_eq_mulHeight_of_subsingleton _

end Arakelov

section Extension

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- **Layer 0.3 (mathlib4#41606) — landed** in `ArithmeticHeights/Extension.lean`. The relative
height over `L` is the `[L : K]`-th power of the relative height over `K`. This and the three
statements after it carry that PR's names. -/
example (x : K) : Height.mulHeight₁ x ^ finrank K L = Height.mulHeight₁ (algebraMap K L x) :=
  NumberField.mulHeight₁_pow_finrank _

/-- **Layer 0.3 (mathlib4#41606).** The tuple form. -/
example {ι : Type*} [Finite ι] (x : ι → K) :
    Height.mulHeight x ^ finrank K L = Height.mulHeight (algebraMap K L ∘ x) :=
  NumberField.mulHeight_pow_finrank _

/-- **Layer 0.3 (mathlib4#41606).** The logarithmic form. -/
example (x : K) : finrank K L • Height.logHeight₁ x = Height.logHeight₁ (algebraMap K L x) :=
  NumberField.finrank_nsmul_logHeight₁ _

/-- **Layer 0.3 (mathlib4#41606).** The logarithmic tuple form. -/
example {ι : Type*} [Finite ι] (x : ι → K) :
    finrank K L • Height.logHeight x = Height.logHeight (algebraMap K L ∘ x) :=
  NumberField.finrank_nsmul_logHeight _

end Extension

section Absolute

/-- **Layer 0.4 — landed** as `NumberField.absMulHeight` in `ArithmeticHeights/Absolute.lean`, with
`NumberField.absLogHeight` beside it: the relative height computed over the field generated by the
coordinates, normalized by the inverse of its degree. This is the tuple analogue of Mathlib's
`NumberField.absMulHeight₁`, which handles the one-variable case through `ℚ⟮x⟯`; the junk value `1`
off the algebraic numbers is inherited. The index type carries `Finite`, as `Height.mulHeight`
does, where the milestone asked for `Fintype`; nothing sums over it.

**Field-extension invariance, the statement the layer exists for.** Over *any* number field
containing the coordinates, the absolute height is the relative height taken to the power
`1 / [K : ℚ]`. With `mulHeight_pow_finrank`, this says the absolute height does not depend on the
field of definition. Mathlib's `NumberField.absMulHeight₁_eq` is the one-variable case. -/
example {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι] (x : ι → K) :
    absMulHeight x = Height.mulHeight x ^ ((finrank ℚ K : ℝ))⁻¹ :=
  NumberField.absMulHeight_eq _

/-- **Layer 0.4.** The absolute height of a tuple restricts to Mathlib's absolute height of an
element, so the two agree where both are defined. -/
example {K : Type*} [Field K] [CharZero K] (x : K) : absMulHeight ![x, 1] = absMulHeight₁ x :=
  NumberField.absMulHeight_eq_absMulHeight₁ _

/-- **Layer 0.4 — scaling invariance, for algebraic scalars.** The algebraicity hypothesis is not
decorative: for `c` transcendental and `x` a nonzero algebraic tuple, `c • x` has a transcendental
coordinate and `absMulHeight (c • x)` is the junk value `1`; the library refutes the unconditional
form. Consequently the descent to `Projectivization K (ι → K)` holds only over a field all of whose
elements are algebraic, `[Algebra.IsAlgebraic ℚ K]` (a number field, or `AlgebraicClosure ℚ`), and
is stated there. -/
example {K : Type*} [Field K] [CharZero K] {ι : Type*} [Finite ι] (x : ι → K) {c : K}
    (hc : c ≠ 0) (hc' : IsAlgebraic ℚ c) :
    absMulHeight (c • x) = absMulHeight x :=
  NumberField.absMulHeight_smul_eq _ hc hc'

end Absolute

section Affine

variable {K : Type*} [Field K] [Height.AdmissibleAbsValues K] {ι : Type*} [Finite ι]

/-- **Layer 0.5 — landed** as `Height.mulHeightAff` in `ArithmeticHeights/Affine.lean`, with
`Height.logHeightAff` beside it: the projective height of the tuple with a coordinate `1`
appended, the tuple analogue of Mathlib's `Height.mulHeight₁`. It is what a bound on a
non-homogeneous quantity — the value of a linear form (2.4), a determinant (2.5) — must be stated
in, since no scaling-invariant quantity can bound one. The appended coordinate is indexed by
`Option ι`, which needs no `Fintype` bookkeeping. -/
example (x : ι → K) : mulHeightAff x = Height.mulHeight fun o : Option ι ↦ o.elim 1 x := rfl

/-- **Layer 0.5.** The affine height dominates the projective height of the tuple, and — unlike
the projective height — the height of each single coordinate. That failure of scaling invariance
is the content of the definition: `Height.exists_mulHeightAff_smul_ne` records it as a theorem. -/
example (x : ι → K) : Height.mulHeight x ≤ mulHeightAff x :=
  Height.mulHeight_le_mulHeightAff _

example (x : ι → K) (i : ι) : Height.mulHeight₁ (x i) ≤ mulHeightAff x :=
  Height.mulHeight₁_le_mulHeightAff _ _

end Affine

/-! ## Layer 1: Northcott, Kronecker, and the Mahler-measure bridge -/

section Northcott

variable {K : Type*} [Field K] [NumberField K]

/-- **Layer 1.1 — landed** as `Projectivization.instNorthcottMulHeight` in
`ArithmeticHeights/Northcott.lean`, together with `Projectivization.instNorthcottLogHeight` and the
finiteness statements behind them, which `Mathlib/NumberTheory/Height/Northcott.lean` records as
its own TODO. They are stated over any field with `Northcott Height.mulHeight₁`, of which a number
field is the case that matters.

⚠ There is no such instance for `Height.mulHeight` on `ι → K`, and none is to be stated:
`mulHeight_smul_eq_mulHeight` puts the whole line `Kˣ • x` at one height, so
`{x | mulHeight x ≤ B}` is infinite for every `B ≥ 1`. Northcott is a property of the projective
height only, and the library refutes the tuple form. -/
example {ι : Type*} [Finite ι] : Northcott (Projectivization.mulHeight (K := K) (ι := ι)) :=
  Projectivization.instNorthcottMulHeight

/-- **Layer 1.2 — the bridge to Mathlib's Mahler measure, landed** as
`NumberField.absMulHeight₁_pow_natDegree` in `ArithmeticHeights/MahlerMeasure.lean`. For an
algebraic number `x` with primitive integer minimal polynomial `f`, the absolute height is the
`deg f`-th root of the Mahler measure of `f`. Stated as an equality of `deg`-th powers so that no
real exponentiation appears. The polynomial is pinned as the primitive `f : ℤ[X]` that is a nonzero
rational multiple of `minpoly ℚ x`; that determines `f` up to sign, and the Mahler measure ignores
the sign (for `x = 1/2`, `f = 2 X - 1`). The hypotheses force `x` algebraic, since `minpoly ℚ x = 0`
otherwise and `0` is not primitive. ⚠ It is **not** `minpoly ℤ x`, which Mathlib defines as `0` off
the algebraic integers, so a statement through `minpoly ℤ x` covers only integral `x` and cannot
feed Northcott's theorem 1.3. This identity is what makes Northcott's theorem and Kronecker's
theorem cheap. `NumberField.exists_isPrimitive_absMulHeight₁_pow_natDegree` is the existence form
the applications use, since no polynomial is given in advance. -/
example {x : ℂ} {f : Polynomial ℤ} (hf : f.IsPrimitive) {c : ℚ} (hc : c ≠ 0)
    (hfx : f.map (Int.castRingHom ℚ) = Polynomial.C c * minpoly ℚ x) :
    absMulHeight₁ x ^ f.natDegree = (f.map (Int.castRingHom ℂ)).mahlerMeasure :=
  NumberField.absMulHeight₁_pow_natDegree hf hc hfx

/-- **Layer 1.3 — Northcott's theorem, in the form with varying degree, landed** as
`NumberField.finite_setOfPred_absMulHeight₁_le_of_finrank_le` in
`ArithmeticHeights/NorthcottTheorem.lean`, over any field of characteristic zero rather than only
over `ℂ`. Mathlib's `NumberField.finite_setOfPred_mulHeight₁_le` fixes the field; this is the
statement that the literature calls Northcott's theorem, and it is what the elliptic-curve and
Diophantine applications need. -/
example (B : ℝ) (D : ℕ) :
    {x : ℂ | IsIntegral ℚ x ∧ absMulHeight₁ x ≤ B ∧ finrank ℚ ℚ⟮x⟯ ≤ D}.Finite :=
  NumberField.finite_setOfPred_absMulHeight₁_le_of_finrank_le _ _

/-- **Layer 1.4 — Kronecker's theorem, landed** as `NumberField.absMulHeight₁_eq_one_iff` in
`ArithmeticHeights/Kronecker.lean`. An algebraic number has absolute height one exactly when it is
zero or a root of unity. The algebraicity hypothesis is not decorative: `absMulHeight₁` takes the
junk value `1` on every transcendental, so the statement without it is false, and the library
refutes it. `Projectivization.absMulHeight_eq_one_iff` is the projective form. -/
example {x : ℂ} (hx : IsIntegral ℚ x) :
    absMulHeight₁ x = 1 ↔ x = 0 ∨ ∃ n, 0 < n ∧ x ^ n = 1 :=
  NumberField.absMulHeight₁_eq_one_iff hx

/-- **Layer 1.5 — landed** as `NumberField.exists_pos_forall_le_absLogHeight₁` in
`ArithmeticHeights/LowerBound.lean`: the lower bound away from one, in the shape Diophantine
arguments consume — for each degree bound there is a uniform positive gap. -/
example (D : ℕ) :
    ∃ c > 0, ∀ x : ℂ, IsIntegral ℚ x → x ≠ 0 → finrank ℚ ℚ⟮x⟯ ≤ D →
      (¬ ∃ n, 0 < n ∧ x ^ n = 1) → c ≤ absLogHeight₁ x :=
  NumberField.exists_pos_forall_le_absLogHeight₁ _

end Northcott

/-! ## Layer 2: heights of polynomials, linear forms, and matrices -/

section Polynomials

variable {K : Type*} [Field K] [Height.AdmissibleAbsValues K]

/-- **Layer 2.1 — landed** as `Polynomial.mulHeight` in `ArithmeticHeights/Polynomial.lean`, with
`Polynomial.logHeight` and the multivariate `MvPolynomial.mulHeight` beside it. The height of a
polynomial is the height of its coefficient `Finsupp`; `Polynomial.coeff` *is* that `Finsupp`, so
no new construction is made. -/
example (p : Polynomial K) : p.mulHeight = Finsupp.mulHeight p.coeff := rfl

/-- **Layer 2.1.** A constant polynomial has height `1`: its coefficient tuple has one entry, and
a one-entry tuple has height `1` by the product formula, with the zero polynomial at the junk
value. ⚠ Not `mulHeight₁ a`, which is the height of the *two*-entry tuple `![a, 1]`; the library
refutes the identification at `a = 2`. -/
example (a : K) : (Polynomial.C a).mulHeight = 1 := Polynomial.mulHeight_C _

/-- **Layer 2.1.** The compatibility with Mathlib's affine height: the linear polynomial with root
`a` has the height of `a`. -/
example (a : K) : (Polynomial.X - Polynomial.C a).mulHeight = Height.mulHeight₁ a :=
  Polynomial.mulHeight_X_sub_C _

/-- **Layer 2.2 — Gauss's lemma for heights, landed** as `Polynomial.iSup_coeff_mul` in
`ArithmeticHeights/GaussLemma.lean`, with a multivariate form beside it. At a nonarchimedean place
the local factor is exactly multiplicative. This is the only place where the ultrametric inequality
is used sharply, and it is what makes the loss in Gelfond's inequality purely archimedean. The
transport from local factors to heights is `Finsupp.mulHeight_le_of_forall_iSup_le` and its
companion, which are what Layer 2.3 instantiates. -/
example {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v) (p q : Polynomial K) :
    (⨆ n : ℕ, v ((p * q).coeff n)) = (⨆ n : ℕ, v (p.coeff n)) * ⨆ n : ℕ, v (q.coeff n) :=
  Polynomial.iSup_coeff_mul hv _ _

/-- **Layer 2.3 — Gelfond's inequality, upper half, landed** as `Polynomial.mulHeight_mul_le` in
`ArithmeticHeights/Gelfond.lean`. The literature's `2 ^ (deg p + deg q)` is the absolute-height
constant; the relative height picks it up once per archimedean place with multiplicity, hence the
exponent `totalWeight K`. `Polynomial.mulHeight_mul_le_min_natDegree` is the same bound with the
sharp elementary constant `min (natDegree p) (natDegree q) + 1`, which — unlike the power of two —
is attained, and `MvPolynomial.mulHeight_mul_le` is the multivariate form. -/
example (p q : Polynomial K) :
    (p * q).mulHeight ≤
      2 ^ ((p.natDegree + q.natDegree) * totalWeight K) * (p.mulHeight * q.mulHeight) :=
  Polynomial.mulHeight_mul_le _ _

end Polynomials

section GelfondLower

/-- **Layer 2.3 — Gelfond's inequality, lower half, landed** as
`Polynomial.mulHeight_mul_mulHeight_le` in `ArithmeticHeights/Gelfond.lean`. Together with the
upper half this bounds the height of a factor, which is the direction transcendence arguments use.

⚠ **Two hypotheses the milestone did not carry.** `p ≠ 0` and `q ≠ 0` cannot be dropped: the junk
value breaks the inequality at `p = 0`, where the left side is `mulHeight q` — unbounded — against
a right side of `2 ^ (natDegree q * totalWeight K) * mulHeight 0`; over `ℚ` with `q = X - C 100`
that reads `100 ≤ 2`. And the statement cannot be made over a general `[AdmissibleAbsValues K]` at
all: that class puts no condition on `archAbsVal`, so there is no embedding `K →+* ℂ` to run the
Mahler-measure argument through. Over a **number field** every archimedean absolute value is
`NumberField.place φ`, and that is where the lower half lives. The upper half has neither problem,
because it uses only the triangle inequality. -/
example {K : Type*} [Field K] [NumberField K] {p q : Polynomial K} (hp : p ≠ 0) (hq : q ≠ 0) :
    p.mulHeight * q.mulHeight ≤
      2 ^ ((p.natDegree + q.natDegree) * totalWeight K) * (p * q).mulHeight :=
  Polynomial.mulHeight_mul_mulHeight_le hp hq

end GelfondLower

section LinearForms

variable {K : Type*} [Field K] [Height.AdmissibleAbsValues K] {ι : Type*} [Fintype ι]

/-- **Layer 2.4 — landed** as `Height.mulHeight₁_sum_mul_le` in
`ArithmeticHeights/LinearForm.lean`: the value of a linear form against the affine heights of its
coefficients and of the point, with the constant `Nat.card ι ^ totalWeight K`. The affine height of
Layer 0.5 is what appears, and must: `Height.exists_not_mulHeight_add_le` records that the naive
tuple analogue of Mathlib's `mulHeight₁_sum_le` is false over `ℚ` for every constant.
`NumberField.arakelovMulHeight_linearMap_apply_le` is the same bound in the Arakelov
normalization, where the constant is `1`. -/
example [Nonempty ι] (a x : ι → K) :
    Height.mulHeight₁ (∑ i, a i * x i) ≤
      (Nat.card ι : ℝ) ^ totalWeight K * (mulHeightAff a * mulHeightAff x) :=
  Height.mulHeight₁_sum_mul_le _ _

end LinearForms

section Matrices

variable {K : Type*} [Field K] [Height.AdmissibleAbsValues K] {m n : Type*} [Fintype m] [Fintype n]

/-- **Layer 2.5 — landed** as `Matrix.mulHeight` in `ArithmeticHeights/Matrix.lean`, with
`Matrix.logHeight`, the affine `Matrix.mulHeightAff` and the Arakelov `Matrix.arakelovMulHeight`
beside it. The height of a matrix is the height of the tuple of its **entries**. The height of its
row space — the height of the tuple of maximal minors, `H(A)` in Bombieri–Vaaler — is
`(Submodule.span K (Set.range A.row)).mulHeight` and is never called the height of `A`. The
classical literature uses one symbol for both; this library does not. -/
example (A : Matrix m n K) : A.mulHeight = Height.mulHeight fun q : m × n ↦ A q.1 q.2 := rfl

/-- **Layer 2.5.** The height of a matrix is invariant under transpose. -/
example (A : Matrix m n K) : A.transpose.mulHeight = A.mulHeight := Matrix.mulHeight_transpose _

/-- **Layer 2.5.** The submatrix bound. -/
example {m' n' : Type*} [Fintype m'] [Fintype n'] (A : Matrix m n K) (f : m' → m) (g : n' → n) :
    (A.submatrix f g).mulHeight ≤ A.mulHeight :=
  Matrix.mulHeight_submatrix_le _ _ _

/-- **Layer 2.5.** The product bound. The archimedean loss at one place is the inner dimension
`card n` (the triangle inequality on a sum of `card n` terms), so in the relative height it is
`card n ^ totalWeight K`; over `ℚ(i)`, `A = ![![1, 1]]` and `B = ![![N, 0], ![N, 1]]` show the
exponent is needed. `n` must be nonempty: for `n` empty, `A * B = 0` has the junk height `1`
against a right-hand side of `0`. In the Arakelov normalization the constant disappears —
`Matrix.arakelovMulHeight_mul_le`. -/
example {p : Type*} [Fintype p] [Nonempty n] (A : Matrix m n K) (B : Matrix n p K) :
    (A * B).mulHeight ≤ (Fintype.card n : ℝ) ^ totalWeight K * (A.mulHeight * B.mulHeight) :=
  Matrix.mulHeight_mul_le _ _

/-- **Layer 2.5.** The determinant, against the affine heights of the columns. The affine height is
not decoration: `Matrix.exists_not_mulHeight₁_det_le` records that no constant bounds the height of
a determinant by the projective height of the matrix. -/
example [DecidableEq n] (A : Matrix n n K) :
    Height.mulHeight₁ A.det ≤
      ((Fintype.card n).factorial : ℝ) ^ totalWeight K * ∏ j, mulHeightAff fun i ↦ A i j :=
  Matrix.mulHeight₁_det_le _

end Matrices

/-! ## Layer 3: Plücker coordinates and the height of a subspace -/

section Plucker

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **Layer 3.1 — landed** as `exteriorPower.plucker` in `ArithmeticHeights/Plucker.lean`: the
coordinate tuple of the wedge `v 0 ∧ ⋯ ∧ v (k-1)` in the basis `(Pi.basisFun R ι).exteriorPower k`
of `⋀[R]^k (ι → R)`, indexed by `Set.powersetCard ι k`. Over a commutative ring, so that Layer 3.4
is the ring-generic Cauchy–Binet identity.

**The Plücker coordinates are the maximal minors by construction**, which is what makes 3.3's
`minorDet` unnecessary: the coordinate at `s` is the determinant of the `k × k` matrix cut out of
the rows `v` by the columns `s`, taken in the order of `ι`. The enumeration is
`Set.powersetCard.ofFinEmbEquiv`, Mathlib's, and `Matrix.plucker_row_eq_det_submatrix` of 3.3
restates it with `Finset.orderEmbOfFin`. ⚠ The `Set.powersetCard.orderIsoOfFin` the milestone named
does not exist; `Finset.orderIsoOfFin` does, and
`Matrix.plucker_row_eq_det_submatrix_orderIso` is the statement in that spelling. -/
example (k : ℕ) (v : Fin k → (ι → R)) (s : Set.powersetCard ι k) :
    exteriorPower.plucker k v s =
      (Matrix.of fun i j ↦ v i (Set.powersetCard.ofFinEmbEquiv.symm s j)).det :=
  exteriorPower.plucker_apply _ _ _

/-- **Layer 3.1.** The coordinate tuple vanishes exactly on a linearly dependent family, so a basis
of `V` produces a nonzero tuple — the nondegeneracy the Plücker point needs. -/
example {K : Type*} [Field K] (k : ℕ) (v : Fin k → (ι → K)) :
    exteriorPower.plucker k v = 0 ↔ ¬ LinearIndependent K v :=
  exteriorPower.plucker_eq_zero_iff _ _

end Plucker

section PluckerPoint

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}

/-- **Layer 3.1 — the Plücker point, landed** as `Submodule.pluckerPoint` in
`ArithmeticHeights/Plucker.lean`. The wedge of a basis of `V`, read in the basis
`(Pi.basisFun K ι).exteriorPower k`, is a nonzero tuple indexed by `Set.powersetCard ι k`; a change
of basis multiplies it by a determinant, hence a unit, so the induced point of projective space
depends only on `V`. `Submodule.pluckerPoint_eq_mk` is that basis-independence in the form actually
used — the value on *any* basis — and `Submodule.pluckerPoint_span_range` the same for a linearly
independent spanning family. The `[LinearOrder ι]` is what `Module.Basis.exteriorPower` needs to
order each wedge of basis vectors; a different order changes the coordinates by signs only, so the
height of 3.2 does not depend on it.

⚠ Unlike the milestone's sketch, the body is deliberately **exposed**: 3.3 has to see
`pluckerPoint` as the `Projectivization.mk` of a coordinate tuple. It is the four subspace *heights*
whose bodies stay unexposed. -/
example (V : Submodule K (ι → K)) (hV : finrank K V = k) (b : Basis (Fin k) K V)
    (hb : exteriorPower.plucker k (fun i ↦ ((b i : ι → K))) ≠ 0) :
    V.pluckerPoint hV = Projectivization.mk K (exteriorPower.plucker k fun i ↦ ((b i : ι → K))) hb :=
  Submodule.pluckerPoint_eq_mk hV b hb

/-- **Layer 3.1.** The Plücker map is injective on subspaces of a fixed rank — what entitles it to
be called an embedding, and the input to Northcott for subspaces (3.7). -/
example (k : ℕ) :
    Function.Injective fun V : {V : Submodule K (ι → K) // finrank K V = k} ↦
      V.1.pluckerPoint V.2 :=
  Submodule.pluckerPoint_injective _

variable [Height.AdmissibleAbsValues K]

/-- **Layer 3.2 — Schmidt's height of a subspace, landed** as `Submodule.mulHeight` in
`ArithmeticHeights/Subspace.lean`, with `Submodule.logHeight`, the Arakelov
`Submodule.arakelovMulHeight` (`H_Ar(V)`, Bombieri–Gubler 2.8.11 — the quantity on the right-hand
side of Bombieri–Vaaler) and the absolute `Submodule.absMulHeight` beside it.

⚠ **The rank does not belong in the definition.** The milestone's `subspaceMulHeight k V hV` takes
the rank and its proof as arguments, and every signature stated in terms of it then carries them
too — two rank hypotheses in 3.3 for one and the same subspace, one for `V` and one for its
annihilator in 3.5, and `mulHeight (V ⊓ W)` in 3.6 ill formed until a rank for `V ⊓ W` has been
produced. Instead the definition takes `k := finrank K V` and `hV := rfl`, so each of the six
subspace heights — three normalizations, multiplicative and logarithmic — is a total function of
`V` alone, and the lemma below re-types it along an arbitrary proof of the rank. That lemma, not
the definition, is what every proof enters through, so the six bodies are left unexposed, as
Mathlib leaves `Projectivization.mulHeight`'s. -/
example {V : Submodule K (ι → K)} (hV : finrank K V = k) :
    V.mulHeight = Projectivization.mulHeight (V.pluckerPoint hV) :=
  Submodule.mulHeight_eq_mulHeight_pluckerPoint hV

/-- **Layer 3.2.** The height of a subspace is at least one — unconditionally, the rank having left
the statement. -/
example (V : Submodule K (ι → K)) : 1 ≤ V.mulHeight := Submodule.one_le_mulHeight _

/-- **Layer 3.2 — the compatibility that makes the definition the right one.** The height of a
line is the projective height of the point it defines. The same holds for the Arakelov and absolute
variants, and `Submodule.mulHeight_span_range` is the general form: the height of the span of a
linearly independent family is the height of its tuple of Plücker coordinates. -/
example {x : ι → K} (hx : x ≠ 0) : (K ∙ x).mulHeight = Height.mulHeight x :=
  Submodule.mulHeight_span_singleton hx

end PluckerPoint

section RowSpace

variable {K : Type*} [Field K] [Height.AdmissibleAbsValues K] {ι : Type*} [Fintype ι]
  [LinearOrder ι] {m : ℕ}

/-- **Layer 3.3 — the matrix dictionary (Bombieri–Gubler, Remark 2.8.7), landed** in
`ArithmeticHeights/RowSpace.lean`. The height of the row space of a full-rank matrix is the height
of its tuple of maximal minors — `H(A)` of Bombieri–Vaaler, which is *not* `Matrix.mulHeight A`.
This is what lets Layer 5 pass between a subspace and a matrix cutting it out.

⚠ **Neither the row space nor the minors is a new definition.** The row space is
`Submodule.span K (Set.range A.row)`, which is `LinearMap.range A.vecMulLinear` by Mathlib's
`Matrix.range_vecMulLinear`, and the minors are `exteriorPower.plucker m A.row` of 3.1; a third
name for either would force every later statement to choose between three spellings of one object.
Full row rank is `LinearIndependent K A.row`, with
`Matrix.linearIndependent_row_iff_rank_eq` and
`Matrix.linearIndependent_row_iff_plucker_row_ne_zero` the other two forms. -/
example {A : Matrix (Fin m) ι K} (hA : LinearIndependent K A.row) :
    (Submodule.span K (Set.range A.row)).mulHeight =
      Height.mulHeight fun s : Set.powersetCard ι m ↦
        (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det :=
  Matrix.mulHeight_span_range_row hA

/-- **Layer 3.3.** The index identification, stated once and for all: the Plücker coordinate at `s`
is the minor on the columns `s`, enumerated by `Finset.orderEmbOfFin`. -/
example {R : Type*} [CommRing R] (A : Matrix (Fin m) ι R) (s : Set.powersetCard ι m) :
    exteriorPower.plucker m A.row s =
      (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det :=
  Matrix.plucker_row_eq_det_submatrix _ _

/-- **Layer 3.3 (Bombieri–Vaaler (2.5)) — the quantitative form of the invariance under row
operations**, over any commutative ring and for *every* square `U`, not only an invertible one. -/
example {R : Type*} [CommRing R] (U : Matrix (Fin m) (Fin m) R) (A : Matrix (Fin m) ι R) :
    exteriorPower.plucker m (U * A).row = U.det • exteriorPower.plucker m A.row :=
  Matrix.plucker_row_mul _ _

/-- **Layer 3.3 (Bombieri–Gubler, Remark 2.8.7).** Invariance of the height of the row space under
row operations. This is the invariance that the naïve Siegel bound of 5.1 lacks and that
Bombieri–Vaaler achieves. The Arakelov and absolute companions are stated beside it, and
`Matrix.span_range_row_mul` is the underlying statement that the row space itself is unchanged. -/
example {U : Matrix (Fin m) (Fin m) K} (hU : IsUnit U.det) (A : Matrix (Fin m) ι K) :
    (Submodule.span K (Set.range (U * A).row)).mulHeight =
      (Submodule.span K (Set.range A.row)).mulHeight :=
  Matrix.mulHeight_span_range_row_mul hU _

end RowSpace

section CauchyBinet

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

/-- **Layer 3.4 — the Cauchy–Binet identity** (Schmidt 1967, §2 Lemma 1; Bombieri–Gubler,
Proposition 2.8.8), **landed** in `ArithmeticHeights/CauchyBinet.lean`: the determinant of `A Bᵀ` is
the sum over the `m`-element column sets of the products of the corresponding maximal minors.
`Matrix.det_mul_eq_sum_plucker` is the general `det (A B) = ∑_S det A_S · det Bˢ` — what the name
refers to — and `Matrix.det_mul_transpose_eq_sum_det_submatrix` and
`Matrix.det_mul_eq_sum_det_submatrix` spell both with `Matrix.submatrix` in place of `plucker`.

The identity is not a determinant expansion: `exteriorPower.sum_plucker_mul_plucker` pairs two
wedges along `Basis.toDual` of the standard basis, which is the diagonal form on the induced basis
on one side and a determinant of dot products on the other. No permutation sum, no rank hypothesis,
no field. -/
example (A B : Matrix (Fin m) ι R) :
    (A * B.transpose).det =
      ∑ s : Set.powersetCard ι m, exteriorPower.plucker m A.row s * exteriorPower.plucker m B.row s :=
  Matrix.det_mul_transpose_eq_sum_plucker _ _

/-- **Layer 3.4 — Cauchy–Binet at a real place.** The ℓ² local factor of the minor vector is the
square root of the Gram determinant `det (A Aᵀ)`. This is exactly where the `√(det (A Aᵀ))` of the
Bombieri–Vaaler bound comes from, so it is a named milestone rather than a step inside a proof.

⚠ It is not a specialization to `ℝ`: the identity holds over any commutative ring, the "sum of
squares" being nothing but the diagonal of Cauchy–Binet. -/
example (A : Matrix (Fin m) ι R) :
    (A * A.transpose).det = ∑ s : Set.powersetCard ι m, exteriorPower.plucker m A.row s ^ 2 :=
  Matrix.det_mul_transpose_self_eq_sum_sq _

/-- **Layer 3.4 — Cauchy–Binet at a complex place.** The same identity with the conjugate
transpose: `∑ |det A_s|² = det (A A*)`, a real number cast to the field. Without this form the
Bombieri–Vaaler constant is only available for totally real fields.

⚠ Again not a specialization to `ℂ`: `Matrix.det_mul_conjTranspose_self_eq_sum` is the statement
over a commutative star ring, and `RCLike` enters only to write the summand as `‖·‖²`. -/
example {K : Type*} [RCLike K] (A : Matrix (Fin m) ι K) :
    (A * A.conjTranspose).det =
      ((∑ s : Set.powersetCard ι m, ‖exteriorPower.plucker m A.row s‖ ^ 2 : ℝ) : K) :=
  Matrix.det_mul_conjTranspose_self_eq_sum_sq_norm _

/-- **Layer 3.4 — the one statement Layers 5.3 and 5.4 consume.** At an infinite place of a number
field, real or complex, the Gram determinant read through `v.embedding` is `∑ₛ v (det Aₛ)²` — the
quantity Layer 0.1 raises to the power `mult v / 2`. The real place is not a separate case: there
the conjugate transpose *is* the transpose. -/
example {K : Type*} [Field K] (v : InfinitePlace K) (A : Matrix (Fin m) ι K) :
    ((A.map v.embedding) * (A.map v.embedding).conjTranspose).det =
      ((∑ s : Set.powersetCard ι m, v (exteriorPower.plucker m A.row s) ^ 2 : ℝ) : ℂ) :=
  NumberField.InfinitePlace.det_map_embedding_mul_conjTranspose_self _ _

/-- **Layer 3.4 — the Gram criterion**, which the milestone does not ask for and Layer 5 needs: over
an ordered field the Gram determinant of the rows detects full row rank. This is what makes
`√(det (A Aᵀ))` nonzero in the Bombieri–Vaaler bound, and a third form of full row rank beside
3.3's two. -/
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (A : Matrix (Fin m) ι K) :
    (A * A.transpose).det = 0 ↔ ¬ LinearIndependent K A.row :=
  Matrix.det_mul_transpose_self_eq_zero_iff _

/-- **Layer 3.4 — the generalized Hadamard inequality** (Schmidt 1967, §2 Lemma 2;
Bombieri–Vaaler (2.6); Bombieri–Gubler's Fischer inequality, Remark 2.8.9), **landed** in
`ArithmeticHeights/Hadamard.lean`, the companion the milestone asks to prove alongside the
identity. `Matrix.det_mul_transpose_self_le_mul` is the same for a matrix whose rows are indexed by
`Fin (p + q)` and cut at `p`.

⚠ It is a second theorem, not a corollary, and Mathlib has none of the three things the textbook
proof of Fischer's inequality runs through — determinant monotonicity on the positive-semidefinite
order, a block Laplace expansion of a maximal minor, the exterior power of a contraction. What
replaces the missing monotonicity is Cauchy–Binet over a doubled column index. Everything is over an
arbitrary ordered field; nothing here is analytic. -/
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {p q : ℕ}
    (A : Matrix (Fin p) ι K) (B : Matrix (Fin q) ι K) :
    ((A.fromRows B) * (A.fromRows B).transpose).det ≤
      (A * A.transpose).det * (B * B.transpose).det :=
  Matrix.det_mul_transpose_self_fromRows_le _ _

/-- **Layer 3.4 — Hadamard's inequality**, the fully split case, by induction from the two-block
form. This is the statement Layer 5.5 imports; `H_u(A) ≤ H_u(A₁) H_u(A₂)` at the finite places and
the assembly of the local bounds into `H_Ar^row(A) ≤ ∏ₘ H_Ar(A ₘ)` belong to 5.5 and are not
proved here. -/
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (A : Matrix (Fin m) ι K) :
    (A * A.transpose).det ≤ ∏ i, A.row i ⬝ᵥ A.row i :=
  Matrix.det_mul_transpose_self_le_prod _

end CauchyBinet

section Duality

variable {K : Type*} [Field K] [Height.AdmissibleAbsValues K] {ι : Type*} [Fintype ι]
  [LinearOrder ι]

/-- **Layer 3.5 — the duality theorem** (W. M. Schmidt 1967, §1, equations (2) and (4);
Bombieri–Gubler, Proposition 2.8.10) — **landed** as
`Submodule.mulHeight_comap_piEquiv_dualAnnihilator` in `ArithmeticHeights/Duality.lean`, with its
Arakelov and absolute companions and every logarithmic form. The height of a subspace equals the
height of its annihilator in the dual, identified with `ι → K` through the standard basis. No rank
hypothesis appears, the rank having left the height in 3.2.

The milestone's `map` along the inverse identification and the delivered `comap` along the
identification are the same subspace, by `Submodule.comap_piEquiv_dualAnnihilator_eq_map`; the
`comap` is the spelling in which the annihilator is visibly the orthogonal complement for the
standard bilinear form (`Submodule.mem_comap_piEquiv_dualAnnihilator`).

⚠ The route the milestone names — the complementation isomorphism
`⋀^k V ≅ ⋀^n V ⊗ ⋀^(n−k) V*` — is not the one taken, and the delivered proof uses no exterior
algebra at all: it needs neither a Laplace expansion along a block of rows nor Jacobi's identity
for complementary minors, neither of which Mathlib has. What it does need, and what Mathlib also
lacks, is that no height sees a change of sign in a coordinate; that is
`Height.mulHeight_eq_of_forall_eq_or_eq_neg` and its two companions, proved in the same file.
`Height.mulHeight_neg`, which the milestone's route names, does not exist and would not suffice:
the sign in Schmidt's involution `τ` depends on the index. -/
example (V : Submodule K (ι → K)) :
    (V.dualAnnihilator.map (Module.piEquiv ι K K).symm.toLinearMap).mulHeight = V.mulHeight := by
  rw [← Submodule.comap_piEquiv_dualAnnihilator_eq_map]
  exact Submodule.mulHeight_comap_piEquiv_dualAnnihilator V

/-- **Layer 3.5 (Bombieri–Gubler, Corollary 2.8.12) — landed** as
`Matrix.mulHeight_ker_mulVecLin`, with the same five companions: the height of a subspace is the
height of any matrix cutting it out. This is the form Layer 5 consumes, and it carries no
hypothesis on the rank of `A`.

`Submodule.exists_plucker_eq_plucker_compl` is the coordinate statement behind both — Schmidt's
involution itself: a subspace and its annihilator have bases whose Plücker coordinates agree at
complementary indices, up to a sign at each index and one common nonzero factor. -/
example {m : Type*} (A : Matrix m ι K) :
    (LinearMap.ker A.mulVecLin).mulHeight = (Submodule.span K (Set.range A.row)).mulHeight :=
  Matrix.mulHeight_ker_mulVecLin A

/-- **Layer 3.6 — submodularity (Bombieri–Gubler, Theorem 2.8.13; Schmidt, Struppeck–Vaaler).**
The height of a subspace is submodular in the subspace lattice. -/
theorem mulHeight_sup_mul_mulHeight_inf_le (V W : Submodule K (ι → K)) :
    (V ⊔ W).mulHeight * (V ⊓ W).mulHeight ≤ V.mulHeight * W.mulHeight :=
  sorry

/-- **Layer 3.6.** The corollary of submodularity and `1 ≤ H` for the intersection. ⚠ Subspace
heights are **not** monotone under inclusion: in `ℚ²`, `H(⊤) = 1` while
`H(span {![1, N]}) = N`. There is no statement bounding `H(W)` by `H(V)` for `W ≤ V`; these two
product bounds are what submodularity gives. -/
theorem mulHeight_inf_le_mul (V W : Submodule K (ι → K)) :
    (V ⊓ W).mulHeight ≤ V.mulHeight * W.mulHeight :=
  sorry

/-- **Layer 3.6.** The same for the sum. -/
theorem mulHeight_sup_le_mul (V W : Submodule K (ι → K)) :
    (V ⊔ W).mulHeight ≤ V.mulHeight * W.mulHeight :=
  sorry

end Duality

section NorthcottSubspace

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **Layer 3.7.** Northcott for subspaces over a number field, immediate from injectivity of the
Plücker map (3.1) and Northcott on projective space (1.1). The rank is a condition on `V` rather
than a parameter of the height. -/
theorem finite_setOf_mulHeight_le (k : ℕ) (B : ℝ) :
    {V : Submodule K (ι → K) | finrank K V = k ∧ V.mulHeight ≤ B}.Finite :=
  sorry

end NorthcottSubspace

/-! ## Layer 4: successive minima, Minkowski's second theorem, extraction, and cube slicing -/

section SuccessiveMinima

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Layer 4.1.** The `i`-th successive minimum of a convex body with respect to a lattice: the
least dilation of the body containing `i + 1` linearly independent lattice points. The `i = 0`
case is the quantity in Minkowski's convex-body theorem, which Mathlib has. For
`i ≥ finrank ℝ E` no such family exists and the value is `sInf ∅ = 0`; every statement about
the minima carries `i < finrank ℝ E`. No measure enters the definition or the statements of 4.1;
the measure-space instances appear only on the two halves of 4.2. -/
def successiveMinimum (L : Submodule ℤ E) (B : Set E) (i : ℕ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ ∃ v : Fin (i + 1) → E,
    (∀ j, v j ∈ (t • B) ∩ (L : Set E)) ∧ LinearIndependent ℝ v}

/-- **Layer 4.1.** The successive minima of a bounded symmetric convex set with nonempty interior
are positive: a bounded body meets the discrete lattice in finitely many points at each dilation.
Attainment (Cassels' Lemma 1) additionally needs `IsClosed B`, and monotonicity in `i` and the
scaling law in `B` belong to the same milestone. -/
theorem successiveMinimum_pos (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {B : Set E} (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty)
    (hB₃ : Bornology.IsBounded B) {i : ℕ} (hi : i < Module.finrank ℝ E) :
    0 < successiveMinimum L B i :=
  sorry

/-- **Layer 4.2 — Minkowski's second theorem, the easy half.** The measure is a Haar measure, the
one `ZLattice.covolume` is taken against, as in Mathlib's
`exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure`. -/
theorem measure_mul_prod_successiveMinimum_le [MeasureTheory.MeasureSpace E] [BorelSpace E]
    [MeasureTheory.Measure.IsAddHaarMeasure (MeasureTheory.volume : MeasureTheory.Measure E)]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {B : Set E} (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B) :
    (2 : ℝ) ^ Module.finrank ℝ E / (Nat.factorial (Module.finrank ℝ E)) *
        ZLattice.covolume L ≤
      (∏ i ∈ Finset.range (Module.finrank ℝ E), successiveMinimum L B i) *
        (MeasureTheory.volume B).toReal :=
  sorry

/-- **Layer 4.2 — Minkowski's second theorem, the substantial half.** This is the direction Layer
5 and 6.3 consume; the proof is the compression argument along a basis realizing the minima. -/
theorem prod_successiveMinimum_mul_measure_le [MeasureTheory.MeasureSpace E] [BorelSpace E]
    [MeasureTheory.Measure.IsAddHaarMeasure (MeasureTheory.volume : MeasureTheory.Measure E)]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {B : Set E} (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B) :
    (∏ i ∈ Finset.range (Module.finrank ℝ E), successiveMinimum L B i) *
        (MeasureTheory.volume B).toReal ≤
      (2 : ℝ) ^ Module.finrank ℝ E * ZLattice.covolume L :=
  sorry

/-- **Layer 4.6 — a basis from any independent family**, the form the proof gives. For
`ℝ`-independent lattice vectors `a 0, …, a (n − 1)` there is a `ℤ`-basis of `L` whose `j`-th member
has gauge at most `max (gauge B (a j)) (½ ∑_{i ≤ j} gauge B (a i))`: extend a basis of
`L ∩ span (a 0, …, a (j − 1))` by one vector and reduce its coefficients on the `a i` into
`[−½, ½]`. No measure enters. -/
theorem exists_basis_gauge_le (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {B : Set E} (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty)
    (a : Fin (Module.finrank ℝ E) → L) (ha : LinearIndependent ℝ (fun i ↦ (a i : E))) :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ E)) ℤ L, ∀ j,
      gauge B (b j : E) ≤
        max (gauge B (a j : E)) ((∑ i ∈ Finset.Iic j, gauge B (a i : E)) / 2) :=
  sorry

/-- **Layer 4.6 — a basis from the minima** (Cassels, p. 135, Lemma 8, as Bugeaud–Győry cite it).
The independent vectors realizing the minima need not be a basis of `L`; some basis has its `i`-th
member (zero-indexed) in `max 1 ((i + 1) / 2) · λ i` times `B`, a total loss of `n! / 2 ^ (n − 1)`
against 4.2. This is what 6.3 consumes. -/
theorem exists_basis_mem_smul_successiveMinimum (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] {B : Set E} (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B)
    (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B) (hB₄ : IsClosed B) :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ E)) ℤ L, ∀ i : Fin (Module.finrank ℝ E),
      (b i : E) ∈ (max 1 ((((i : ℕ) : ℝ) + 1) / 2) * successiveMinimum L B i) • B :=
  sorry

end SuccessiveMinima

section Extraction

variable {F K E V W : Type*}
variable [Field F] [Field K] [Field E]
variable [Algebra F K] [Algebra F E] [FiniteDimensional F K]
variable [AddCommGroup V] [Module F V] [Module K V] [IsScalarTower F K V]
variable [AddCommGroup W] [Module F W] [Module E W] [IsScalarTower F E W]

/-- **Layer 4.4 — the counting half of the extraction lemma.** A family of vectors of a
`K`-vector space whose image under an `F`-linear map is linearly independent over a field
`E ⊇ F` has size at most `[K : F]` times the `K`-dimension of its span. With `F = ℚ`, `E = ℝ`
and the mixed embedding as the map: `ℝ`-independent lattice vectors of a `K`-subspace span, over
`K`, a subspace of dimension at least their number divided by the degree. -/
theorem fintype_card_le_finrank_mul_finrank_span
    (f : V →ₗ[F] W) {ι : Type*} [Fintype ι] {u : ι → V}
    (h : LinearIndependent E (f ∘ u)) :
    Fintype.card ι ≤ finrank F K * finrank K (Submodule.span K (Set.range u)) :=
  sorry

/-- **Layer 4.4 — the selection half.** From `d · k` vectors with `E`-independent images, a
`K`-linearly independent subfamily of size `k` whose `j`-th member (zero-indexed) is among the
first `d · j + 1` — members of the family, never linear combinations, so each keeps the norm
bound of the successive minimum it realizes. -/
theorem exists_linearIndependent_comp_finrank_mul
    (f : V →ₗ[F] W) {k : ℕ} {u : Fin (finrank F K * k) → V}
    (h : LinearIndependent E (f ∘ u)) :
    ∃ s : Fin k → Fin (finrank F K * k), LinearIndependent K (u ∘ s) ∧
      ∀ j : Fin k, (s j).val ≤ finrank F K * j.val :=
  sorry

end Extraction

section CubeSlicing

/-- The volume `ω_n` of the unit ball of `ℝⁿ`: the archimedean slice volume of 5.3 and the
normalizing constant of the product-of-balls body below. -/
def unitBallVolume (n : ℕ) : ℝ :=
  (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal

/-- **Layer 4.5 — the product-of-balls theorem** (Bombieri–Gubler, Theorem C.3.8), the form
`README.md` pins. Partition the `N` coordinates into blocks by `blk : Fin N → Fin r`, and let `Q`
be the product over the blocks of the euclidean ball **of volume `1`** in the block's
coordinates, i.e. of radius `ω_m ^ (-1/m)` for a block of size `m`. Then every central slice of
`Q` by a subspace `V` has volume at least `1`, the volume on `V` being the canonical one of its
inner-product structure (Mathlib's `measureSpaceOfInnerProductSpace`). The blocks of size `1`
give the cube case below; blocks of size `2` are the complex places of Layer 5. -/
theorem one_le_volume_inter_prod_ball {N r : ℕ} (blk : Fin N → Fin r)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin N))) :
    1 ≤ MeasureTheory.volume {x : V | ∀ i : Fin r,
      ∑ j ∈ Finset.univ.filter (fun j ↦ blk j = i), (x : EuclideanSpace ℝ (Fin N)) j ^ 2 ≤
        unitBallVolume (Finset.univ.filter (fun j ↦ blk j = i)).card ^
          (-(2 / ((Finset.univ.filter (fun j ↦ blk j = i)).card : ℝ)))} :=
  sorry

/-- **Layer 4.5 — Vaaler's cube-slicing theorem** (Vaaler 1979), the case of blocks of size `1`,
rescaled: every central slice of the cube `[−1, 1]ᴺ` by a `k`-dimensional subspace has
`k`-volume at least `2 ^ k`. Coordinate subspaces give equality, so the bound is sharp. This is
what the `ℚ` spine 5.2 consumes. -/
theorem two_pow_finrank_le_volume_inter_cube {N : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin N))) :
    (2 : ENNReal) ^ finrank ℝ V ≤
      MeasureTheory.volume {x : V | ∀ i, |(x : EuclideanSpace ℝ (Fin N)) i| ≤ 1} :=
  sorry

/-- **Layer 4.5 — the inscribed-cube bound at a complex place.** A `k`-dimensional complex
subspace of `ℂⁿ`, viewed as a `2k`-dimensional real subspace of `ℝ^{2n}` with coordinates
`(Re, Im)`, meets the unit polydisc in volume at least `2 ^ k`: the polydisc contains the cube of
half-side `1 / √2`, of volume `(2/√2)^{2k} = 2^k` on the slice by the cube case. This is the
lemma that gives the first bound of 5.4 from the cube case alone; the product-of-balls form
gives `π ^ k` here and hence 5.4's sharper constant. Stated for a real subspace closed under the
complex structure `J`, `J (x, y) = (-y, x)`, expressed coordinatewise. -/
theorem two_pow_le_volume_inter_polydisc {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin 2)))
    (hJ : ∀ x ∈ V, ∃ y ∈ V, ∀ i : Fin n,
      (y : EuclideanSpace ℝ (Fin n × Fin 2)) (i, 0) = -(x : EuclideanSpace ℝ (Fin n × Fin 2)) (i, 1) ∧
      (y : EuclideanSpace ℝ (Fin n × Fin 2)) (i, 1) = (x : EuclideanSpace ℝ (Fin n × Fin 2)) (i, 0)) :
    (2 : ENNReal) ^ (finrank ℝ V / 2) ≤
      MeasureTheory.volume {x : V | ∀ i : Fin n,
        (x : EuclideanSpace ℝ (Fin n × Fin 2)) (i, 0) ^ 2 +
          (x : EuclideanSpace ℝ (Fin n × Fin 2)) (i, 1) ^ 2 ≤ 1} :=
  sorry

end CubeSlicing

/-! ## Layer 5: Siegel's lemma and Bombieri–Vaaler (the summit)

Every statement over a number field is in the **absolute** normalization on both sides: absolute
heights of the solutions on the left, and on the right the absolute Arakelov height of the row
space, i.e. `Submodule.arakelovMulHeight … ^ (finrank ℚ K)⁻¹`. Over `ℤ` the two normalizations
coincide.

The row space of `A` is `Submodule.span K (Set.range A.row)` and full row rank is
`LinearIndependent K A.row`, both as Layer 3.3 delivers them; `Submodule.arakelovMulHeight` is
Layer 3.2's `H_Ar`, which no longer takes a rank. -/

section Siegel

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-! ### Layer 5 over `ℤ`

Bombieri–Vaaler 1983, Theorems 1 and 2. The Gram matrix is `A * Aᵀ`, the `M × M` determinant of the
rows; `Aᵀ * A` is `N × N` and singular whenever `M < N`, and stating it that way is the standard
slip these signatures exist to prevent. Layer 3.4's Gram criterion,
`Matrix.det_mul_transpose_self_eq_zero_iff`, is what makes the left-hand side of the bound nonzero
under `hrank`. -/

section SiegelInt

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [LinearOrder n]

/-- The greatest common divisor of the maximal minors of `A` — the `D` of Bombieri–Vaaler. The
minors are Layer 3.1's Plücker coordinates of the rows, after the row index is put in the `Fin`
form they are stated in; there is no `minorDet`. -/
def minorGcd (A : Matrix m n ℤ) : ℤ :=
  (Finset.univ.image fun s : Set.powersetCard n (Fintype.card m) ↦
    exteriorPower.plucker (Fintype.card m)
      (A.submatrix (Fintype.equivFin m).symm id).row s).gcd id

/-- **Layer 5.2, Bombieri–Vaaler Theorem 1 — one small solution.** -/
theorem exists_ne_zero_mulVec_eq_zero_norm_le (A : Matrix m n ℤ) (hA : A ≠ 0)
    (hrank : A.rank = Fintype.card m) (hmn : Fintype.card m < Fintype.card n) :
    ∃ x : n → ℤ, x ≠ 0 ∧ A.mulVec x = 0 ∧
      (⨆ i, |(x i : ℝ)|) ≤
        (Real.sqrt |((A * A.transpose).det : ℝ)| / |(minorGcd A : ℝ)|) ^
          ((Fintype.card n - Fintype.card m : ℝ)⁻¹) :=
  sorry

/-- **Layer 5.2, Bombieri–Vaaler Theorem 2 — a small basis.** The statement Layers 5.3 and 5.4
generalize to a number field. Over `ℤ` the extraction 4.4 is vacuous — the minima vectors of 4.2
are already the basis — and the constant is 3.4's Cauchy–Binet determinant with 4.5's slice bound;
the adele-free assembly is written out in Aliev–Henk §6. -/
theorem exists_linearIndependent_mulVec_eq_zero_prod_norm_le (A : Matrix m n ℤ) (hA : A ≠ 0)
    (hrank : A.rank = Fintype.card m) (hmn : Fintype.card m < Fintype.card n) :
    ∃ x : Fin (Fintype.card n - Fintype.card m) → (n → ℤ),
      LinearIndependent ℤ x ∧ (∀ l, A.mulVec (x l) = 0) ∧
      (∏ l, ⨆ i, |((x l i : ℤ) : ℝ)|) ≤
        Real.sqrt |((A * A.transpose).det : ℝ)| / |(minorGcd A : ℝ)| :=
  sorry

end SiegelInt

/-- **Layer 5.3 — Bombieri–Vaaler over a number field, Hermitian form** (Bombieri–Vaaler 1983;
the inequality Vaaler 2003 quotes as (1.3)). For `A` an `M × N` matrix of rank `M` over a number
field `K` of degree `d` with `r₁` real and `r₂` complex places, the solution space of `A x = 0`
has a basis `x₁, …, x_{N−M}` with coordinates in `𝓞 K` and, for `k = N − M`,

`∏ l, H_Ar(x l) ≤ [(2^k / ω_k)^{r₁} (2^k / ω_{2k})^{r₂}]^{1/d} · |D_{K/ℚ}| ^ (k / (2 d)) · H_Ar(A)`,

absolute Arakelov heights on both sides, `H_Ar(A)` the Arakelov height of the row space. This
needs 4.1–4.4 and no cube slicing: the slices of the ℓ² balls are balls. -/
theorem exists_basis_prod_arakelovMulHeight_le {m : ℕ} (A : Matrix (Fin m) ι K)
    (hA : LinearIndependent K A.row)
    (k : ℕ) (hk : finrank K (LinearMap.ker A.mulVecLin) = k) :
    ∃ b : Basis (Fin k) K (LinearMap.ker A.mulVecLin),
      (∀ l j, IsIntegral ℤ ((b l : ι → K) j)) ∧
      (∏ l, arakelovMulHeight (fun j ↦ (b l : ι → K) j) ^ (finrank ℚ K : ℝ)⁻¹) ≤
        ((2 ^ k / unitBallVolume k) ^ NumberField.InfinitePlace.nrRealPlaces K *
            (2 ^ k / unitBallVolume (2 * k)) ^ NumberField.InfinitePlace.nrComplexPlaces K) ^
              (finrank ℚ K : ℝ)⁻¹ *
          |(NumberField.discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K)) *
          (Submodule.span K (Set.range A.row)).arakelovMulHeight ^ (finrank ℚ K : ℝ)⁻¹ :=
  sorry

/-- **Layer 5.4 — Bombieri–Vaaler over a number field: the summit** (Bombieri–Gubler, Theorem
2.9.4; Bombieri–Vaaler 1983).

For `A` an `M × N` matrix of rank `M` over a number field `K` of degree `d` and discriminant
`D_{K/ℚ}`, the solution space of `A x = 0` has a basis `x₁, …, x_{N−M}` with

`∏ l, H(x l) ≤ |D_{K/ℚ}| ^ ((N − M) / (2 d)) * H_Ar(A)`,

where `H` is the absolute multiplicative height and `H_Ar(A)` is the **absolute** Arakelov height
of the row space — the subspace height of Layer 3, not the height of the entries of `A`. The
basis has coordinates in `𝓞 K`, as the README states it. Stated here for the kernel of a matrix;
the equivalent subspace form follows from the duality theorem 3.5. -/
theorem exists_basis_prod_absMulHeight_le {m : ℕ} (A : Matrix (Fin m) ι K)
    (hA : LinearIndependent K A.row)
    (k : ℕ) (hk : finrank K (LinearMap.ker A.mulVecLin) = k) :
    ∃ b : Basis (Fin k) K (LinearMap.ker A.mulVecLin),
      (∀ l j, IsIntegral ℤ ((b l : ι → K) j)) ∧
      (∏ l, absMulHeight (fun j ↦ (b l : ι → K) j)) ≤
        |(NumberField.discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K)) *
          (Submodule.span K (Set.range A.row)).arakelovMulHeight ^ (finrank ℚ K : ℝ)⁻¹ :=
  sorry

/-- **Layer 5.4 — the same at Bombieri–Vaaler's own constant.** The product-of-balls form of 4.5
at the complex places gives the factor `(2 / π) ^ (k r₂ / d)`, which is `≤ 1`, so this implies
the statement above; it is the constant of Bombieri–Vaaler's Theorem 8 in the max-norm
normalization. -/
theorem exists_basis_prod_absMulHeight_le' {m : ℕ} (A : Matrix (Fin m) ι K)
    (hA : LinearIndependent K A.row)
    (k : ℕ) (hk : finrank K (LinearMap.ker A.mulVecLin) = k) :
    ∃ b : Basis (Fin k) K (LinearMap.ker A.mulVecLin),
      (∀ l j, IsIntegral ℤ ((b l : ι → K) j)) ∧
      (∏ l, absMulHeight (fun j ↦ (b l : ι → K) j)) ≤
        (2 / Real.pi) ^
            ((k * NumberField.InfinitePlace.nrComplexPlaces K : ℝ) / finrank ℚ K) *
          |(NumberField.discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K)) *
          (Submodule.span K (Set.range A.row)).arakelovMulHeight ^ (finrank ℚ K : ℝ)⁻¹ :=
  sorry

/-- **Layer 5.5 — the entry-height corollary** (Bombieri–Gubler, Corollary 2.9.9). Bounding the
absolute Arakelov height of the row space by the absolute height of the entries through
`H_Ar(Aₘ) ≤ √N · H(A)` gives the form applications actually quote, and over `ℚ` it improves the
`N` of the classical Siegel lemma (5.1) to `√N`. The row-by-row step is Layer 3.4's Hadamard
inequality at the archimedean places; the finite places and the assembly over all places are this
milestone's own work. -/
theorem exists_ne_zero_mem_ker_absMulHeight_le {m : ℕ} (A : Matrix (Fin m) ι K)
    (hA : LinearIndependent K A.row) (hm : m < Fintype.card ι) :
    ∃ x : ι → K, x ≠ 0 ∧ A.mulVec x = 0 ∧ (∀ j, IsIntegral ℤ (x j)) ∧
      absMulHeight x ≤
        |(NumberField.discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ *
          (Real.sqrt (Fintype.card ι) * A.mulHeight ^ (finrank ℚ K : ℝ)⁻¹) ^
            ((m : ℝ) / (Fintype.card ι - m)) :=
  sorry

/-- **Layer 5.6 — the relative version** (Bombieri–Gubler, Theorem 2.9.19): the entries lie in a
finite extension `F/K` of degree `r` while the solutions are required to lie in `K`. With
`M` rows and `r M < N`, there are `N − r M` `K`-linearly independent solutions with

`∏ l, H(x l) ≤ |D_{K/ℚ}| ^ ((N − r M) / (2 d)) · ∏ i, H_Ar(A i) ^ r`,

`H_Ar(A i)` the absolute Arakelov height of the `i`-th row, an element of `F ^ N`. This is the
form transcendence arguments use when the auxiliary construction and the field of definition
differ. -/
theorem exists_linearIndependent_mem_ker_prod_absMulHeight_le
    (F : Type*) [Field F] [NumberField F] [Algebra K F] {m : ℕ} (A : Matrix (Fin m) ι F)
    (hmn : finrank K F * m < Fintype.card ι) :
    ∃ x : Fin (Fintype.card ι - finrank K F * m) → (ι → K),
      LinearIndependent K x ∧ (∀ l, A.mulVec (fun j ↦ algebraMap K F (x l j)) = 0) ∧
      (∀ l j, IsIntegral ℤ (x l j)) ∧
      (∏ l, absMulHeight (x l)) ≤
        |(NumberField.discr K : ℝ)| ^
            ((Fintype.card ι - finrank K F * m : ℝ) / (2 * finrank ℚ K)) *
          ∏ i, (arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ finrank K F :=
  sorry

end Siegel

/-! ## Layer 6: heights and the unit group

Mathlib proves Dirichlet's unit theorem in full (`NumberField.Units.logEmbedding`, `unitLattice`,
`unitLattice_span_eq_top`, `rank`, `fundSystem`, `regulator`) and has `S`-integers and `S`-units
(`Set.integer`, `Set.unit` in `Mathlib/RingTheory/DedekindDomain/SInteger.lean`). This layer
builds the height-side dictionary around them and the `S`-unit theorem Mathlib does not have; it
re-proves none of the unit theorem and redefines none of the `S`-objects. -/

section Units

variable {K : Type*} [Field K] [NumberField K]

/-- **Layer 6.2 — units of height one.** The height-theoretic identification of the torsion
subgroup, from Kronecker (1.4) and Mathlib's `logEmbedding_ker`. -/
theorem absMulHeight₁_eq_one_iff_mem_torsion (u : (𝓞 K)ˣ) :
    NumberField.absMulHeight₁ ((u : 𝓞 K) : K) = 1 ↔ u ∈ NumberField.Units.torsion K :=
  sorry

/-- **Layer 6.3 — Hadamard's bound.** The regulator is at most `(2 d) ^ r` times the product of
the absolute logarithmic heights of Mathlib's fundamental system (and of any `r` independent
units): the regulator is the determinant of the `r × r` matrix of `logEmbedding`s, each row has
ℓ¹ norm at most `∑ w, |mult w · log (w ε)| = 2 · logHeight₁ ε = 2 d · h(ε)`, and Hadamard's
inequality — Layer 3.4's `Matrix.det_mul_transpose_self_le_prod`, in the ℓ² form, which is where
the `2 d` and not a `d` comes from — bounds a determinant by the product of the row norms. -/
theorem regulator_le_prod_absLogHeight₁ :
    NumberField.Units.regulator K ≤
      (2 * Module.finrank ℚ K : ℝ) ^ NumberField.Units.rank K *
        ∏ i, NumberField.absLogHeight₁ ((NumberField.Units.fundSystem K i : 𝓞 K) : K) :=
  sorry

/-- **Layer 6.3 — a fundamental system of small height exists** (Bugeaud–Győry 1996, Lemma 1,
the case `S = S_∞`). The converse of Hadamard's bound cannot hold for every fundamental system — a
unimodular change of basis makes the heights arbitrarily large at fixed regulator — but some
fundamental system, a reduced basis of the unit lattice, has `∏ h(ε i) ≤ c(r, d) · R` with the
explicit constant `c = (r!)² / (2 ^ (r − 1) d ^ r)`. Route, theirs: 4.2 for the ℓ¹ unit ball, of
volume `2 ^ r / r!`, on `unitLattice K`, of covolume `regulator K`, gives `∏ λ i ≤ r! · R`; the
basis of 4.6 costs `r! / 2 ^ (r − 1)`; and `h(ε) ≤ ‖logEmbedding ε‖₁ / d` by 6.1, which costs
`d ^ (-r)`. "Fundamental system" is what Mathlib's
`closure_fundSystem_sup_torsion_eq_top` says of `fundSystem`: `r` units generating the unit
group modulo torsion. -/
theorem exists_fundSystem_prod_absLogHeight₁_le :
    ∃ ε : Fin (NumberField.Units.rank K) → (𝓞 K)ˣ,
      Subgroup.closure (Set.range ε) ⊔ NumberField.Units.torsion K = ⊤ ∧
      ∏ i, NumberField.absLogHeight₁ ((ε i : 𝓞 K) : K) ≤
        ((NumberField.Units.rank K).factorial : ℝ) ^ 2 /
            (2 ^ (NumberField.Units.rank K - 1) *
              (Module.finrank ℚ K : ℝ) ^ NumberField.Units.rank K) *
          NumberField.Units.regulator K :=
  sorry

/-- **Layer 6.5 — the `S`-unit theorem, in the form and under the name of mathlib4#40791.** For a
finite set `S` of finite places, Mathlib's `S`-unit group `S.unit K` has `ℤ`-rank
`r₁ + r₂ − 1 + |S|`. `S = ∅` recovers Dirichlet's theorem, since `(∅ : Set _).unit K` is `(𝓞 K)ˣ`
through `Set.unitEquivUnitsInteger` and `integer_empty`. -/
theorem _root_.Set.unit_finrank_numberField
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    Module.finrank ℤ (Additive (S.unit K)) = NumberField.Units.rank K + Nat.card S :=
  sorry

/-- **Layer 6.5 — the `S`-unit theorem, in the shape of Mathlib's `exist_unique_eq_mul_prod`.**
The rank statement made usable: a fundamental system of `r₁ + r₂ − 1 + |S|` `S`-units such that
every `S`-unit is uniquely a root of unity times a product of their integer powers. -/
theorem exists_sUnit_fundSystem (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : S.Finite) :
    ∃ ε : Fin (NumberField.Units.rank K + Nat.card S) → S.unit K,
      ∀ x : S.unit K, ∃! e : Fin (NumberField.Units.rank K + Nat.card S) → ℤ,
        ∃ ζ ∈ CommGroup.torsion (S.unit K), x = ζ * ∏ i, ε i ^ e i :=
  sorry

end Units

/-! ## Worked examples (acceptance criteria)

The cheap checks that the definitions mean what they should. All five the roadmap lists are
discharged in the library, in the file of the layer they test, and are not restated here — an
`example` is anonymous, so repeating one would mean repeating its proof.

* `Height.mulHeight₁ (3 / 4 : ℚ) = 4`, the rational height from Mathlib's `Rat.mulHeight₁_eq_max`:
  `ArithmeticHeights/Absolute.lean`, where the absolute and relative heights are compared over `ℚ`.
  A definition that does not give `4` has numerator and denominator confused.
* `NumberField.arakelovMulHeight ![(1 : ℚ), 1] = √2` and `Height.mulHeight ![(1 : ℚ), 1] = 1`:
  `ArithmeticHeights/Arakelov.lean`. The two normalizations genuinely differ, so the `√N` of 5.5
  and the `H_Ar` on the right of 5.3 and 5.4 are not cosmetic.
* The rejection test for Layer 1.4 — a transcendental has absolute height one by the junk value,
  not by Kronecker: `ArithmeticHeights/Kronecker.lean`, stated for an arbitrary element that is not
  integral over `ℚ` rather than for `π`, which needs a transcendence proof to instantiate.
* The rejection test for Layer 2.1 — `(C (2 : ℚ)).mulHeight = 1` against
  `Height.mulHeight₁ (2 : ℚ) = 2`, refuting `mulHeight (C a) = mulHeight₁ a`:
  `ArithmeticHeights/Polynomial.lean`.

Every landed file carries acceptance, rejection and conformance examples of its own beyond these;
they are listed under *Worked examples* in the roadmap.
-/

end

end TauCetiRoadmap.ArithmeticHeights
