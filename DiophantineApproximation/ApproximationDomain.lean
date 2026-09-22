/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ModuleCovolume
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin

-- Used only inside proofs.
import ArithmeticHeights.FinitePlaceIdeal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Approximation domains

For a number field `K`, a finite set `Sfin` of finite places, forms `L v i` on `Kⁱ` at every
infinite place and at every place of `Sfin`, exponents `c v i` and a level `Q`, the
**approximation domain** is the set of `x ∈ Kⁱ` with

```text
v (L v i x) ≤ Q ^ c v i     at every infinite place and every place of Sfin,
v (x j) ≤ 1                at every other finite place,
```

and its **weight** is `∑_{v | ∞} mult v ∑ i c v i + ∑_{v ∈ Sfin} ∑ i c v i`, the exponent of `Q`
in the product of all the local bounds. This is Bombieri–Gubler's 7.5.6 in the real formulation of
the geometry of numbers: the finite conditions cut out an `𝓞 K`-submodule `Λ` of `Kⁱ`, the infinite
ones a compact convex symmetric body `B` in `(K ⊗ ℝ)ⁱ` that is balanced over every completion, and
the domain is `Λ ∩ B`. The covolume of `Λ` is computed exactly:

```text
covol Λ = ∏_{v ∈ Sfin} v (det L v) ∏ i (a v i)⁻¹ · covol (𝓞 K) ^ #ι,
```

with `a v i` the largest value of `v` that is at most `Q ^ c v i`. The volume of `B`, and the
comparison of the two with `Q` to the weight, are in `ApproximationVolume.lean`.

## Main definitions

* `NumberField.approxDomain`: the approximation domain, a set of points of `Kⁱ`.
* `NumberField.approxWeight`: its weight.
* `NumberField.approxModule`: its finite part `Λ`, an `𝓞 K`-submodule of `Kⁱ`.
* `NumberField.approxBody`: its infinite part `B`, a set in `ι → mixedSpace K`.
* `NumberField.approxLattice`: `Λ` read in `ι → mixedSpace K`.

## Main results

* `NumberField.approxDomain_eq`: the domain is `Λ ∩ B`.
* `NumberField.convex_approxBody`, `NumberField.neg_mem_approxBody`,
  `NumberField.isClosed_approxBody`, `NumberField.isBounded_approxBody` and
  `NumberField.approxBody_mem_nhds_zero`: `B` is a compact convex symmetric body.
* `NumberField.mul_mem_approxBody`: `B` is balanced over every completion.
* `NumberField.fg_approxModule`, `NumberField.span_approxModule`,
  `NumberField.discreteTopology_approxLattice` and `NumberField.isZLattice_approxLattice`: `Λ` is a
  lattice.
* `NumberField.covolume_approxLattice`: the covolume displayed above.

## Implementation notes

⚠ **The finite-place covolume is exact in the value group, and only approximate in `Q ^ c v i`.**
Bombieri–Gubler's Lemma 7.5.7(b) states the volume of the `v`-adic factor as `|Δ_v|⁻¹ Q ^ (d ∑ c)`
in their normalization; that is an equality only when every `Q ^ c v i` is a value of `v`. In
general the condition `v (L v i x) ≤ Q ^ c v i` is the condition `v (L v i x) ≤ a v i` with
`a v i` the largest value at most `Q ^ c v i`, and the covolume is exact in `a v i`. Since
`Q ^ c v i / N 𝔭 < a v i ≤ Q ^ c v i`, the error in `Q ^ c v i` is a factor at most
`∏_{v ∈ Sfin} N 𝔭_v ^ #ι`, which is a constant; the acceptance test at the `2`-adic place of `ℚ`
shows the equality failing.

⚠ **The index is computed from maximal determinants, never from a quotient.** At a place of
`Sfin` the determinants of `#ι` vectors of `Λ` are at most `v (det L v)⁻¹ ∏ a v i` by the
ultrametric Leibniz bound applied to `L v · x`, and the bound is attained by `M⁻¹ (π k e_k)`, `M`
the matrix of `L v` and `v (π k) = a v k`, moved into `Λ` by one algebraic integer that is a unit
at `v` and small at the other places where it matters. Off `Sfin` the maximum is `1`, attained by
a multiple of the standard basis. `Submodule.covolume_mixedImage` does the rest.

⚠ **Every infinite place carries a condition.** A domain with no condition at some infinite
place is unbounded there, and `NumberField.isBounded_approxBody` needs the forms independent at
every infinite place; Layer 6.2 adds the missing infinite places before it starts.

⚠ **The module is stated with `|Q|`.** `Q ^ c` is Mathlib's real power, which can be negative for
`Q < 0`; with `|Q|` the finite part is an `𝓞 K`-submodule for every real `Q`, and it agrees with
the domain's conditions for `Q ≥ 0`, which is where `NumberField.approxDomain_eq` is stated.

⚠ **No `DecidableEq ι` appears in any statement.** The coefficients of a form are its values at
`Pi.basisFun K ι j` rather than at `Pi.single j 1`, which is the same vector without the
decidability instance.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
7.5.6 and Lemma 7.5.7.

This is Layer 4.1 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Module NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Matrix Filter
  Topology
open scoped Pointwise

namespace LinearMap

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- The matrix of a family of forms has the values of the forms at the standard basis for its
rows. -/
theorem toMatrix'_pi_apply [DecidableEq ι] (l : ι → Dual K (ι → K)) (i j : ι) :
    LinearMap.toMatrix' (LinearMap.pi l) i j = l i (Pi.single j 1) := by
  simp [LinearMap.toMatrix'_apply]

omit [Fintype ι] in
/-- A linearly independent family of `#ι` forms on `Kⁱ` has nonzero determinant. -/
theorem det_pi_ne_zero [Finite ι] {l : ι → Dual K (ι → K)} (hl : LinearIndependent K l) :
    LinearMap.det (LinearMap.pi l) ≠ 0 := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  set ψ : Dual K (ι → K) →ₗ[K] (ι → K) :=
    LinearMap.pi fun j ↦ Module.Dual.eval K (ι → K) (Pi.single j 1) with hψ
  have hψinj : LinearMap.ker ψ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro ℓ hℓ
    refine LinearMap.pi_ext' fun j ↦ LinearMap.ext_ring ?_
    have := congrFun hℓ j
    simpa [hψ] using this
  have hrows : LinearIndependent K fun i ↦ (LinearMap.toMatrix' (LinearMap.pi l)) i := by
    have : (fun i ↦ (LinearMap.toMatrix' (LinearMap.pi l)) i) = ψ ∘ l := by
      funext i; funext j; simp [hψ]
    rw [this]
    exact hl.map' ψ hψinj
  rw [← LinearMap.det_toMatrix']
  exact (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hrows)
    |>.ne_zero

end LinearMap

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}


/-- **The approximation domain of level `Q`** (Bombieri–Gubler 7.5.6): a set of points of `Kⁱ`,
with a condition at every infinite place, at every place of `Sfin`, and integrality elsewhere. -/
def approxDomain (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) : Set (ι → K) :=
  {x | (∀ (v : InfinitePlace K) (i : ι), v (L v.1 i x) ≤ Q ^ c v.1 i) ∧
    (∀ v ∈ Sfin, ∀ i : ι, v (L v.1 i x) ≤ Q ^ c v.1 i) ∧
    ∀ v : FinitePlace K, v ∉ Sfin → ∀ j : ι, v (x j) ≤ 1}

/-- **The finite part of an approximation domain**: the conditions at the places of `Sfin` and
integrality at the other finite places, an `𝓞 K`-submodule of `Kⁱ`. It is stated with `|Q|` so
that it is a submodule for every real `Q`; for `Q ≥ 0`, the only levels that occur, the two
agree. -/
def approxModule (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) : Submodule (𝓞 K) (ι → K) where
  carrier := {x | (∀ v ∈ Sfin, ∀ i : ι, v (L v.1 i x) ≤ |Q| ^ c v.1 i) ∧
    ∀ v : FinitePlace K, v ∉ Sfin → ∀ j : ι, v (x j) ≤ 1}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨fun v hv i ↦ ?_, fun v hv j ↦ ?_⟩
    · rw [map_add]
      exact (v.add_le _ _).trans (max_le (hx v hv i) (hy v hv i))
    · exact (v.add_le _ _).trans (max_le (hx' v hv j) (hy' v hv j))
  zero_mem' := by
    refine ⟨fun v _ i ↦ ?_, fun v _ j ↦ ?_⟩
    · rw [map_zero, map_zero]; exact Real.rpow_nonneg (abs_nonneg Q) _
    · simp
  smul_mem' := by
    rintro a x ⟨hx, hx'⟩
    have ha : ∀ v : FinitePlace K, v (a : K) ≤ 1 := fun v ↦ FinitePlace.apply_le_one v a
    refine ⟨fun v hv i ↦ ?_, fun v hv j ↦ ?_⟩
    · rw [LinearMap.map_smul_of_tower, Algebra.smul_def, map_mul]
      exact (mul_le_of_le_one_left (apply_nonneg _ _) (ha v)).trans (hx v hv i)
    · rw [Pi.smul_apply, Algebra.smul_def, map_mul]
      exact (mul_le_of_le_one_left (apply_nonneg _ _) (ha v)).trans (hx' v hv j)

variable [Fintype ι]

/-- **The infinite part of an approximation domain**: the body in `(K ⊗ ℝ)ⁱ = ι → mixedSpace K`
cut out by the forms at the infinite places. The form `L w i` acts on the mixed space through its
coefficients, its values at the standard basis, and `normAtPlace w` reads only the coordinate at
`w`; so the body is a product over the infinite places. -/
def approxBody (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (Q : ℝ) : Set (ι → mixedSpace K) :=
  {z | ∀ (w : InfinitePlace K) (i : ι),
    normAtPlace w (∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * z j) ≤ Q ^ c w.1 i}

/-- **The lattice of an approximation domain**: its finite part, read in `(K ⊗ ℝ)ⁱ`. -/
noncomputable def approxLattice (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) :
    Submodule ℤ (ι → mixedSpace K) :=
  (approxModule Sfin L c Q).mixedImage

/-- The weight of a system of exponents: the exponent of `Q` in the product of all the local
bounds, in Mathlib's normalization. -/
noncomputable def approxWeight (Sfin : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ) :
    ℝ :=
  ∑ v : InfinitePlace K, v.mult * ∑ i, c v.1 i + ∑ v ∈ Sfin, ∑ i, c v.1 i

/-- **An approximation domain is the set of points of a lattice in a body**: `x` lies in it
exactly when it lies in the finite part and its mixed embedding lies in the infinite part. -/
theorem approxDomain_eq (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : 0 ≤ Q) :
    approxDomain Sfin L c Q =
      {x | x ∈ approxModule Sfin L c Q ∧ (fun j ↦ mixedEmbedding K (x j)) ∈ approxBody L c Q} := by
  have hform : ∀ (w : InfinitePlace K) (i : ι) (x : ι → K),
      normAtPlace w (∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * mixedEmbedding K (x j))
        = w (L w.1 i x) := by
    intro w i x
    rw [← normAtPlace_apply w]
    congr 1
    simp_rw [← map_mul, ← map_sum]
    congr 1
    conv_rhs => rw [← (Pi.basisFun K ι).sum_repr x]
    simp [map_sum, mul_comm]
  ext x
  simp only [approxDomain, Set.mem_ofPred_eq, approxBody, approxModule, Submodule.mem_mk,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, hform, abs_of_nonneg hQ]
  tauto


omit [NumberField K] in
private theorem sum_mixedEmbedding_mul_eq [DecidableEq ι] (l : Dual K (ι → K))
    (z : ι → mixedSpace K) (i : ι)
    (L' : ι → Dual K (ι → K)) (hl : L' i = l) :
    ∑ j, mixedEmbedding K (l (Pi.basisFun K ι j)) * z j
      = (((LinearMap.toMatrix' (LinearMap.pi L')).map (mixedEmbedding K)) *ᵥ z) i := by
  simp [Matrix.mulVec, dotProduct, hl, Pi.basisFun_apply]

omit [NumberField K] in
/-- The body of an approximation domain is convex. -/
theorem convex_approxBody (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) : Convex ℝ (approxBody L c Q) := by
  intro x hx y hy a b ha hb hab w i
  have hxy : ∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * (a • x + b • y) j
      = a • ∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * x j
        + b • ∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * y j := by
    simp only [Pi.add_apply, Pi.smul_apply, mul_add, mul_smul_comm, Finset.smul_sum,
      Finset.sum_add_distrib]
  rw [hxy]
  refine (normAtPlace_add_le _ _ _).trans ?_
  rw [normAtPlace_smul, normAtPlace_smul, abs_of_nonneg ha, abs_of_nonneg hb]
  have h1 : normAtPlace w (∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * x j) ≤
      Q ^ c w.1 i :=
    hx w i
  have h2 : normAtPlace w (∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * y j) ≤
      Q ^ c w.1 i :=
    hy w i
  have := mul_le_mul_of_nonneg_left h1 ha
  have := mul_le_mul_of_nonneg_left h2 hb
  have : a * Q ^ c w.1 i + b * Q ^ c w.1 i = Q ^ c w.1 i := by rw [← add_mul, hab, one_mul]
  linarith

omit [NumberField K] in
/-- The body of an approximation domain is symmetric. -/
theorem neg_mem_approxBody {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ} {z : ι → mixedSpace K} (hz : z ∈ approxBody L c Q) :
    -z ∈ approxBody L c Q := by
  intro w i
  simpa [Finset.sum_neg_distrib, normAtPlace_neg] using hz w i

omit [NumberField K] in
/-- The body of an approximation domain is closed. -/
theorem isClosed_approxBody (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) : IsClosed (approxBody L c Q) := by
  have : approxBody L c Q = ⋂ (w : InfinitePlace K) (i : ι),
      {z | normAtPlace w (∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * z j) ≤
        Q ^ c w.1 i} := by
    ext z; simp [approxBody]
  rw [this]
  refine isClosed_iInter fun w ↦ isClosed_iInter fun i ↦ isClosed_le ?_ continuous_const
  exact (continuous_normAtPlace w).comp (continuous_finsetSum _ fun j _ ↦
    continuous_const.mul (continuous_apply j))

/-- The body of an approximation domain of positive level is a neighbourhood of `0`. -/
theorem approxBody_mem_nhds_zero (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) : approxBody L c Q ∈ nhds 0 := by
  have h : ∀ (w : InfinitePlace K) (i : ι), ∀ᶠ z in nhds (0 : ι → mixedSpace K),
      normAtPlace w (∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * z j) < Q ^ c w.1 i := by
    intro w i
    have hcont : Continuous fun z : ι → mixedSpace K ↦
        normAtPlace w (∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * z j) :=
      (continuous_normAtPlace w).comp (continuous_finsetSum _ fun j _ ↦
        continuous_const.mul (continuous_apply j))
    refine hcont.continuousAt.eventually (gt_mem_nhds ?_)
    simpa using Real.rpow_pos_of_pos hQ _
  filter_upwards [Filter.eventually_all.2 fun w ↦ Filter.eventually_all.2 (h w)] with z hz
  exact fun w i ↦ (hz w i).le

omit [NumberField K] in
/-- **The body is balanced over every completion at once**: multiplying by an element of the
mixed space whose local norms are at most `1` keeps it. This is what makes `ω • x` lie in the
body for an algebraic integer `ω` of small conjugates. -/
theorem mul_mem_approxBody {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ} {z : ι → mixedSpace K} (hz : z ∈ approxBody L c Q)
    {a : mixedSpace K} (ha : ∀ w, normAtPlace w a ≤ 1) :
    (fun j ↦ a * z j) ∈ approxBody L c Q := by
  intro w i
  have : ∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * (a * z j)
      = a * ∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * z j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [this, map_mul]
  exact (mul_le_of_le_one_left (normAtPlace_nonneg _ _) (ha w)).trans (hz w i)

omit [NumberField K] in
/-- Membership in a dilate of the body. -/
theorem mem_smul_approxBody_iff {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    {c : AbsoluteValue K ℝ → ι → ℝ} {Q t : ℝ} (ht : 0 < t) {z : ι → mixedSpace K} :
    z ∈ t • approxBody L c Q ↔ ∀ (w : InfinitePlace K) (i : ι),
      normAtPlace w (∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * z j) ≤
        t * Q ^ c w.1 i := by
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne']
  refine forall_congr' fun w ↦ forall_congr' fun i ↦ ?_
  have : ∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * (t⁻¹ • z) j
      = t⁻¹ • ∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * z j := by
    simp only [Pi.smul_apply, mul_smul_comm, Finset.smul_sum]
  rw [this, normAtPlace_smul, abs_of_pos (inv_pos.2 ht), inv_mul_le_iff₀ ht]

open scoped Classical in
/-- **The body of an approximation domain is bounded**, when the forms are independent at every
infinite place: a domain with no condition at some infinite place would be unbounded there. -/
theorem isBounded_approxBody {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hL : ∀ w : InfinitePlace K, LinearIndependent K (L w.1)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (Q : ℝ) : Bornology.IsBounded (approxBody L c Q) := by
  set M : InfinitePlace K → Matrix ι ι K :=
    fun w ↦ LinearMap.toMatrix' (LinearMap.pi (L w.1)) with hM
  have hdet : ∀ w, (M w).det ≠ 0 := fun w ↦ by
    rw [hM, LinearMap.det_toMatrix']; exact LinearMap.det_pi_ne_zero (hL w)
  set R : ℝ := ∑ w : InfinitePlace K, ∑ j : ι, ∑ i : ι, w ((M w)⁻¹ j i) * |Q ^ c w.1 i| with hR
  have hloc : ∀ z ∈ approxBody L c Q, ∀ (w : InfinitePlace K) (j : ι),
      normAtPlace w (z j) ≤ ∑ i : ι, w ((M w)⁻¹ j i) * |Q ^ c w.1 i| := by
    intro z hz w j
    have hinv : (M w)⁻¹ * M w = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hdet w))
    have hz' : z = (((M w)⁻¹).map (mixedEmbedding K)) *ᵥ (((M w).map (mixedEmbedding K)) *ᵥ z) := by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hinv, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.one_mulVec]
    rw [hz']
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine (Finset.le_sum_of_subadditive (normAtPlace w) (map_zero _).le (normAtPlace_add_le w)
      _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [map_mul, normAtPlace_apply]
    refine mul_le_mul_of_nonneg_left ?_ (apply_nonneg _ _)
    have := hz w i
    rw [sum_mixedEmbedding_mul_eq _ z i (L w.1) rfl] at this
    exact this.trans (le_abs_self _)
  have hR0 : ∀ (w : InfinitePlace K) (j : ι), 0 ≤ ∑ i : ι, w ((M w)⁻¹ j i) * |Q ^ c w.1 i| :=
    fun w j ↦ Finset.sum_nonneg fun i _ ↦ mul_nonneg (apply_nonneg _ _) (abs_nonneg _)
  have hle : ∀ (w : InfinitePlace K) (j : ι), ∑ i : ι, w ((M w)⁻¹ j i) * |Q ^ c w.1 i| ≤ R := by
    intro w j
    rw [hR]
    refine (Finset.single_le_sum (f := fun j ↦ ∑ i : ι, w ((M w)⁻¹ j i) * |Q ^ c w.1 i|)
      (fun j _ ↦ hR0 w j) (Finset.mem_univ j)).trans ?_
    exact Finset.single_le_sum (f := fun w : InfinitePlace K ↦
      ∑ j, ∑ i : ι, w ((M w)⁻¹ j i) * |Q ^ c w.1 i|)
      (fun w _ ↦ Finset.sum_nonneg fun j _ ↦ hR0 w j) (Finset.mem_univ w)
  have hRnn : 0 ≤ R := Finset.sum_nonneg fun w _ ↦ Finset.sum_nonneg fun j _ ↦ hR0 w j
  refine (Metric.isBounded_closedBall (x := (0 : ι → mixedSpace K)) (r := R)).subset
    fun z hz ↦ ?_
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hRnn]
  intro j
  classical
  rw [norm_eq_sup'_normAtPlace]
  exact Finset.sup'_le _ _ fun w _ ↦ (hloc z hz w j).trans (hle w j)


omit [Fintype ι] in
/-- The finite part of an approximation domain is finitely generated: its coordinates have
bounded denominators at the places of `Sfin`. -/
theorem fg_approxModule [Finite ι] {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} (hL : ∀ v ∈ Sfin, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) : (approxModule Sfin L c Q).FG := by
  have : Fintype ι := Fintype.ofFinite ι
  classical
  set M : FinitePlace K → Matrix ι ι K :=
    fun v ↦ LinearMap.toMatrix' (LinearMap.pi (L v.1)) with hM
  set R : FinitePlace K → ℝ := fun v ↦ ∑ j, ∑ i, v ((M v)⁻¹ j i) * |Q| ^ c v.1 i with hR
  have hR0 : ∀ v : FinitePlace K, ∀ j, 0 ≤ ∑ i, v ((M v)⁻¹ j i) * |Q| ^ c v.1 i := fun v j ↦
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (apply_nonneg _ _) (Real.rpow_nonneg (abs_nonneg Q) _)
  have hbound : ∀ x ∈ approxModule Sfin L c Q, ∀ v ∈ Sfin, ∀ j, v (x j) ≤ R v := by
    intro x hx v hv j
    have hdet : (M v).det ≠ 0 := by
      rw [hM, LinearMap.det_toMatrix']; exact LinearMap.det_pi_ne_zero (hL v hv)
    have hinv : (M v)⁻¹ * M v = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)
    set y := M v *ᵥ x with hy
    have hx' : x = (M v)⁻¹ *ᵥ y := by rw [hy, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    have hyi : ∀ i, y i = L v.1 i x := fun i ↦ by
      rw [hy, hM, LinearMap.toMatrix'_mulVec]; rfl
    have hxj : x j = ∑ i, (M v)⁻¹ j i * y i := by
      conv_lhs => rw [hx']
      rfl
    rw [hxj]
    refine (AbsoluteValue.sum_le _ _ _).trans ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun j ↦ ∑ i, v ((M v)⁻¹ j i) * |Q| ^ c v.1 i)
      (fun j _ ↦ hR0 v j) (Finset.mem_univ j))
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [map_mul, hyi i]
    exact mul_le_mul_of_nonneg_left (hx.1 v hv i) (apply_nonneg _ _)
  have hRnn : ∀ v, 0 ≤ R v := fun v ↦ Finset.sum_nonneg fun j _ ↦ hR0 v j
  obtain ⟨d, hd0, hd⟩ := FinitePlace.exists_ne_zero_forall_apply_le Sfin
    (ε := fun v ↦ (1 + R v)⁻¹) fun v _ ↦ inv_pos.2 (by linarith [hRnn v])
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0
  have hle : approxModule Sfin L c Q ≤
      Submodule.span (𝓞 K) (Set.range fun j ↦ (d : K)⁻¹ • Pi.basisFun K ι j) := by
    intro x hx
    have hint : ∀ j, ∃ z : 𝓞 K, (z : K) = d * x j := fun j ↦
      FinitePlace.exists_eq_of_forall_apply_le_one fun v ↦ by
        rw [map_mul]
        by_cases hv : v ∈ Sfin
        · calc v (d : K) * v (x j) ≤ (1 + R v)⁻¹ * R v :=
                mul_le_mul (hd v hv) (hbound x hx v hv j) (apply_nonneg _ _)
                  (inv_nonneg.2 (by linarith [hRnn v]))
            _ ≤ 1 := by
                rw [inv_mul_le_iff₀ (by linarith [hRnn v])]; linarith
        · exact (mul_le_mul (FinitePlace.apply_le_one v d) (hx.2 v hv j) (apply_nonneg _ _)
            zero_le_one).trans_eq (one_mul 1)
    choose z hz using hint
    have hsum : x = ∑ j, z j • ((d : K)⁻¹ • Pi.basisFun K ι j) := by
      funext k
      classical
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · rw [Pi.smul_apply, Pi.smul_apply, Pi.basisFun_apply, Pi.single_eq_same, smul_eq_mul,
          mul_one, Algebra.smul_def]
        change x k = (z k : K) * (d : K)⁻¹
        rw [hz k]
        field_simp
      · intro j _ hj
        rw [Pi.smul_apply, Pi.smul_apply, Pi.basisFun_apply, Pi.single_eq_of_ne (Ne.symm hj),
          smul_zero, smul_zero]
      · simp
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have : IsNoetherian (𝓞 K)
      (Submodule.span (𝓞 K) (Set.range fun j ↦ (d : K)⁻¹ • Pi.basisFun K ι j)) :=
    isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range _))
  exact Submodule.FG.of_le_of_isNoetherian hle

omit [Fintype ι] in
/-- The finite part of an approximation domain of nonzero level spans `Kⁱ`. -/
theorem span_approxModule [Finite ι] (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : Q ≠ 0) : Submodule.span K (approxModule Sfin L c Q : Set (ι → K)) = ⊤ := by
  have : Fintype ι := Fintype.ofFinite ι
  set S : FinitePlace K → ℝ :=
    fun v ↦ ∑ i, ∑ j, v (L v.1 i (Pi.basisFun K ι j)) / |Q| ^ c v.1 i with hS
  have hQc : ∀ (v : FinitePlace K) i, 0 < |Q| ^ c v.1 i := fun v i ↦
    Real.rpow_pos_of_pos (abs_pos.2 hQ) _
  have hS0 : ∀ v : FinitePlace K, ∀ i, 0 ≤ ∑ j, v (L v.1 i (Pi.basisFun K ι j)) / |Q| ^ c v.1 i :=
    fun v i ↦ Finset.sum_nonneg fun j _ ↦ div_nonneg (apply_nonneg _ _) (hQc v i).le
  have hSnn : ∀ v, 0 ≤ S v := fun v ↦ Finset.sum_nonneg fun i _ ↦ hS0 v i
  obtain ⟨d, hd0, hd⟩ := FinitePlace.exists_ne_zero_forall_apply_le Sfin
    (ε := fun v ↦ (1 + S v)⁻¹) fun v _ ↦ inv_pos.2 (by linarith [hSnn v])
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0
  have hmem : ∀ j, (d : K) • Pi.basisFun K ι j ∈ approxModule Sfin L c Q := by
    intro j
    refine ⟨fun v hv i ↦ ?_, fun v hv k ↦ ?_⟩
    · rw [map_smul, smul_eq_mul, map_mul]
      have h1 : v (L v.1 i (Pi.basisFun K ι j)) / |Q| ^ c v.1 i ≤ S v :=
        (Finset.single_le_sum (f := fun j ↦ v (L v.1 i (Pi.basisFun K ι j)) / |Q| ^ c v.1 i)
          (fun j _ ↦ div_nonneg (apply_nonneg _ _) (hQc v i).le) (Finset.mem_univ j)).trans
          (Finset.single_le_sum (f := fun i ↦ ∑ j, v (L v.1 i (Pi.basisFun K ι j)) / |Q| ^ c v.1 i)
            (fun i _ ↦ hS0 v i) (Finset.mem_univ i))
      rw [div_le_iff₀ (hQc v i)] at h1
      calc v (d : K) * v (L v.1 i (Pi.basisFun K ι j))
          ≤ (1 + S v)⁻¹ * v (L v.1 i (Pi.basisFun K ι j)) :=
            mul_le_mul_of_nonneg_right (hd v hv) (apply_nonneg _ _)
        _ ≤ |Q| ^ c v.1 i := by
            rw [inv_mul_le_iff₀ (by linarith [hSnn v])]
            nlinarith [hQc v i]
    · rw [Pi.smul_apply, smul_eq_mul, map_mul]
      refine (mul_le_mul (FinitePlace.apply_le_one v d) ?_ (apply_nonneg _ _)
        zero_le_one).trans_eq (one_mul 1)
      classical
      rw [Pi.basisFun_apply, Pi.single_apply]
      split_ifs <;> simp
  rw [eq_top_iff, ← (Pi.basisFun K ι).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have : Pi.basisFun K ι j = (d : K)⁻¹ • ((d : K) • Pi.basisFun K ι j) := by
    rw [inv_smul_smul₀ hdK]
  rw [SetLike.mem_coe, this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem j))

open scoped Classical in
/-- The local factor of the covolume at a finite place. -/
private noncomputable def approxDetBound (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ)
    (v : FinitePlace K) : ℝ :=
  if v ∈ Sfin then (v (LinearMap.det (LinearMap.pi (L v.1))))⁻¹ * ∏ i, v.floorValue (Q ^ c v.1 i)
  else 1

omit [NumberField K] in
private theorem toMatrix'_mul_transpose [DecidableEq ι] (l : ι → Dual K (ι → K))
    (x : ι → ι → K) :
    LinearMap.toMatrix' (LinearMap.pi l) * (Matrix.of x)ᵀ = Matrix.of fun i k ↦ l i (x k) := by
  ext i k
  have := congrFun (LinearMap.toMatrix'_mulVec (LinearMap.pi l) (x k)) i
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this

private theorem apply_det_le_approxDetBound [DecidableEq ι] {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} (hL : ∀ v ∈ Sfin, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) (v : FinitePlace K)
    (x : ι → ι → K) (hx : ∀ k, x k ∈ approxModule Sfin L c Q) :
    v (Matrix.of x).det ≤ approxDetBound Sfin L c Q v := by
  classical
  unfold approxDetBound
  split_ifs with hv
  · set M := LinearMap.toMatrix' (LinearMap.pi (L v.1)) with hM
    have hdetM : M.det = LinearMap.det (LinearMap.pi (L v.1)) := LinearMap.det_toMatrix' _
    have hne : M.det ≠ 0 := hdetM ▸ LinearMap.det_pi_ne_zero (hL v hv)
    have hbound : v (M * (Matrix.of x)ᵀ).det ≤ ∏ i, v.floorValue (Q ^ c v.1 i) := by
      rw [hM, toMatrix'_mul_transpose]
      refine FinitePlace.apply_det_le_prod v _ (fun i ↦ (v.floorValue_pos _).le) fun i k ↦ ?_
      rw [Matrix.of_apply]
      exact v.apply_le_floorValue (((hx k).1 v hv i).trans_eq (by rw [abs_of_pos hQ]))
    rw [Matrix.det_mul, Matrix.det_transpose, map_mul] at hbound
    have hpos : 0 < v M.det := (FinitePlace.pos_iff).2 hne
    rw [← hdetM, inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
    exact hbound
  · refine (FinitePlace.apply_det_le_prod v _ (fun _ ↦ zero_le_one) fun k j ↦ ?_).trans_eq (by simp)
    exact (hx k).2 v hv j


omit [Fintype ι] in
/-- The scaling step: a family of vectors with a controlled value of `v` on its forms at `v` can
be moved into the module by one algebraic integer that is a unit at `v`. -/
private theorem exists_smul_mem_approxModule [Finite ι] {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : 0 < Q) (v : FinitePlace K) (u : ι → ι → K)
    (hv : v ∈ Sfin → ∀ i k, v (L v.1 i (u k)) ≤ Q ^ c v.1 i)
    (hv' : v ∉ Sfin → ∀ k j, v (u k j) ≤ 1) :
    ∃ s : 𝓞 K, v (s : K) = 1 ∧ ∀ k, (s : K) • u k ∈ approxModule Sfin L c Q := by
  have : Fintype ι := Fintype.ofFinite ι
  classical
  have hQc : ∀ (w : FinitePlace K) i, 0 < Q ^ c w.1 i := fun w i ↦ Real.rpow_pos_of_pos hQ _
  set S : FinitePlace K → ℝ := fun w ↦ ∑ i, ∑ k, w (L w.1 i (u k)) / Q ^ c w.1 i +
    ∑ k, ∑ j, w (u k j) with hS
  have hS0 : ∀ w, 0 ≤ S w := fun w ↦ add_nonneg
    (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun k _ ↦ div_nonneg (apply_nonneg _ _)
      (hQc w i).le)
    (Finset.sum_nonneg fun k _ ↦ Finset.sum_nonneg fun j _ ↦ apply_nonneg _ _)
  have hSL : ∀ w i k, w (L w.1 i (u k)) ≤ (1 + S w) * Q ^ c w.1 i := by
    intro w i k
    have h1 : w (L w.1 i (u k)) / Q ^ c w.1 i ≤ S w := by
      refine le_trans ?_ (le_add_of_nonneg_right (Finset.sum_nonneg fun k _ ↦
        Finset.sum_nonneg fun j _ ↦ apply_nonneg _ _))
      refine (Finset.single_le_sum (f := fun k ↦ w (L w.1 i (u k)) / Q ^ c w.1 i)
        (fun k _ ↦ div_nonneg (apply_nonneg _ _) (hQc w i).le) (Finset.mem_univ k)).trans ?_
      exact Finset.single_le_sum (f := fun i ↦ ∑ k, w (L w.1 i (u k)) / Q ^ c w.1 i)
        (fun i _ ↦ Finset.sum_nonneg fun k _ ↦ div_nonneg (apply_nonneg _ _) (hQc w i).le)
        (Finset.mem_univ i)
    rw [div_le_iff₀ (hQc w i)] at h1
    nlinarith [hQc w i]
  have hSu : ∀ w k j, w (u k j) ≤ 1 + S w := by
    intro w k j
    have : w (u k j) ≤ ∑ k, ∑ j, w (u k j) :=
      (Finset.single_le_sum (f := fun j ↦ w (u k j)) (fun j _ ↦ apply_nonneg _ _)
        (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun k ↦ ∑ j, w (u k j))
          (fun k _ ↦ Finset.sum_nonneg fun j _ ↦ apply_nonneg _ _) (Finset.mem_univ k))
    have : ∑ i, ∑ k, w (L w.1 i (u k)) / Q ^ c w.1 i ≥ 0 :=
      Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun k _ ↦ div_nonneg (apply_nonneg _ _)
        (hQc w i).le
    simp only [hS]
    linarith
  -- the places where some coordinate is not integral
  have hbad : {w : FinitePlace K | ∃ k j, u k j ≠ 0 ∧ w (u k j) ≠ 1}.Finite := by
    refine (Set.finite_iUnion (ι := {p : ι × ι // u p.1 p.2 ≠ 0})
      fun p ↦ FinitePlace.hasFiniteMulSupport p.2).subset ?_
    rintro w ⟨k, j, hkj, hw⟩
    exact Set.mem_iUnion.2 ⟨⟨(k, j), hkj⟩, hw⟩
  set T : Finset (FinitePlace K) := (Sfin ∪ hbad.toFinset).erase v with hT
  obtain ⟨s, hs1, hsT⟩ := FinitePlace.exists_apply_eq_one_forall_apply_le v T
    (Finset.notMem_erase v _) (ε := fun w ↦ (1 + S w)⁻¹)
    fun w _ ↦ inv_pos.2 (by linarith [hS0 w])
  refine ⟨s, hs1, fun k ↦ ⟨fun w hw i ↦ ?_, fun w hw j ↦ ?_⟩⟩
  · rw [abs_of_pos hQ, map_smul, smul_eq_mul, map_mul]
    by_cases hwv : w = v
    · subst hwv
      rw [hs1, one_mul]
      exact hv hw i k
    · have hwT : w ∈ T := by
        rw [hT, Finset.mem_erase]
        exact ⟨hwv, Finset.mem_union_left _ hw⟩
      calc w (s : K) * w (L w.1 i (u k)) ≤ (1 + S w)⁻¹ * ((1 + S w) * Q ^ c w.1 i) :=
            mul_le_mul (hsT w hwT) (hSL w i k) (apply_nonneg _ _)
              (inv_nonneg.2 (by linarith [hS0 w]))
        _ = Q ^ c w.1 i := by
            rw [← mul_assoc, inv_mul_cancel₀ (by linarith [hS0 w]), one_mul]
  · rw [Pi.smul_apply, smul_eq_mul, map_mul]
    by_cases hwv : w = v
    · subst hwv
      rw [hs1, one_mul]
      exact hv' hw k j
    by_cases hwT : w ∈ T
    · calc w (s : K) * w (u k j) ≤ (1 + S w)⁻¹ * (1 + S w) :=
            mul_le_mul (hsT w hwT) (hSu w k j) (apply_nonneg _ _)
              (inv_nonneg.2 (by linarith [hS0 w]))
        _ = 1 := inv_mul_cancel₀ (by linarith [hS0 w])
    · have hgood : w (u k j) ≤ 1 := by
        by_contra hcon
        push Not at hcon
        apply hwT
        rw [hT, Finset.mem_erase]
        refine ⟨hwv, Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 ⟨k, j, ?_, hcon.ne'⟩)⟩
        rintro h
        rw [h, map_zero] at hcon
        linarith
      exact (mul_le_mul (FinitePlace.apply_le_one w s) hgood (apply_nonneg _ _)
        zero_le_one).trans_eq (one_mul 1)


private theorem exists_det_eq_approxDetBound [DecidableEq ι] {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} (hL : ∀ v ∈ Sfin, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) (v : FinitePlace K) :
    ∃ x : ι → ι → K, (∀ k, x k ∈ approxModule Sfin L c Q) ∧
      v (Matrix.of x).det = approxDetBound Sfin L c Q v := by
  classical
  unfold approxDetBound
  split_ifs with hv
  · set M := LinearMap.toMatrix' (LinearMap.pi (L v.1)) with hM
    have hdetM : M.det = LinearMap.det (LinearMap.pi (L v.1)) := LinearMap.det_toMatrix' _
    have hne : M.det ≠ 0 := hdetM ▸ LinearMap.det_pi_ne_zero (hL v hv)
    choose π hπ using fun i ↦ v.exists_apply_eq_floorValue (Q ^ c v.1 i)
    set u : ι → ι → K := fun k ↦ M⁻¹ *ᵥ Pi.single k (π k) with hu
    have hMu : ∀ k, M *ᵥ u k = Pi.single k (π k) := fun k ↦ by
      rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hne),
        Matrix.one_mulVec]
    have hLu : ∀ i k, L v.1 i (u k) = (Pi.single k (π k) : ι → K) i := fun i k ↦ by
      rw [← hMu k, hM, LinearMap.toMatrix'_mulVec]
      rfl
    have hdiag : M * (Matrix.of u)ᵀ = Matrix.diagonal π := by
      rw [hM, toMatrix'_mul_transpose]
      ext i k
      rw [Matrix.of_apply, hLu, Matrix.diagonal_apply, Pi.single_apply]
      by_cases hik : i = k
      · subst hik; simp
      · simp [hik]
    obtain ⟨s, hs1, hsmem⟩ := exists_smul_mem_approxModule (Sfin := Sfin) (L := L) c hQ v u
      (fun _ i k ↦ by
        rw [hLu, Pi.single_apply]
        split_ifs with hik
        · subst hik
          rw [hπ]
          exact v.floorValue_le (Real.rpow_pos_of_pos hQ _)
        · rw [map_zero]
          exact (Real.rpow_pos_of_pos hQ _).le)
      fun h ↦ (h hv).elim
    refine ⟨fun k ↦ (s : K) • u k, hsmem, ?_⟩
    have hsU : Matrix.of (fun k ↦ (s : K) • u k) = (s : K) • Matrix.of u := by
      ext k j
      simp [Algebra.smul_def]
    have hU : M.det * (Matrix.of u).det = ∏ i, π i := by
      rw [← Matrix.det_transpose (Matrix.of u), ← Matrix.det_mul, hdiag, Matrix.det_diagonal]
    have hvU := congrArg v hU
    rw [map_mul, map_prod] at hvU
    simp_rw [hπ] at hvU
    have hpos : 0 < v M.det := (FinitePlace.pos_iff).2 hne
    rw [hsU, Matrix.det_smul, map_mul, map_pow, hs1, one_pow, one_mul, ← hdetM,
      eq_inv_mul_iff_mul_eq₀ hpos.ne']
    exact hvU
  · obtain ⟨s, hs1, hsmem⟩ := exists_smul_mem_approxModule (Sfin := Sfin) (L := L) c hQ v
      (fun k ↦ Pi.single k 1) (fun h ↦ (hv h).elim)
      (fun _ k j ↦ by
        rw [Pi.single_apply]
        split_ifs <;> simp)
    refine ⟨fun k ↦ (s : K) • Pi.single k 1, hsmem, ?_⟩
    have hsU : Matrix.of (fun k ↦ (s : K) • (Pi.single k 1 : ι → K)) = (s : K) • 1 := by
      ext k j
      simp [Matrix.one_apply, Pi.single_apply, eq_comm, Algebra.smul_def]
    rw [hsU, Matrix.det_smul, Matrix.det_one, mul_one, map_pow, hs1, one_pow]

omit [Fintype ι] in
/-- The lattice of an approximation domain of nonzero level is discrete. -/
theorem discreteTopology_approxLattice [Finite ι] {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} (hL : ∀ v ∈ Sfin, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : Q ≠ 0) :
    DiscreteTopology (approxLattice Sfin L c Q) :=
  (approxModule Sfin L c Q).discreteTopology_mixedImage (fg_approxModule hL c Q)
    (span_approxModule Sfin L c hQ)

open scoped Classical in
/-- The lattice of an approximation domain of nonzero level is a lattice. -/
theorem isZLattice_approxLattice {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} (hL : ∀ v ∈ Sfin, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : Q ≠ 0)
    [DiscreteTopology (approxLattice Sfin L c Q)] : IsZLattice ℝ (approxLattice Sfin L c Q) := by
  have : DiscreteTopology (approxModule Sfin L c Q).mixedImage :=
    ‹DiscreteTopology (approxLattice Sfin L c Q)›
  exact (approxModule Sfin L c Q).isZLattice_mixedImage (fg_approxModule hL c Q)
    (span_approxModule Sfin L c hQ)

open scoped Classical in
/-- **The covolume of the lattice of an approximation domain** (Bombieri–Gubler, Lemma 7.5.7(a),
(b), in the real formulation). It is the covolume of `(𝓞 K)ⁱ` times the generalized index
`∏ v ∈ Sfin, v (det L v) * ∏ i, (a v i)⁻¹`, with `a v i` the largest value of `v` that is at most
`Q ^ c v i`. -/
theorem covolume_approxLattice {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} (hL : ∀ v ∈ Sfin, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) :
    ZLattice.covolume (approxLattice Sfin L c Q) =
      (∏ v ∈ Sfin, v (LinearMap.det (LinearMap.pi (L v.1))) *
        ∏ i, (v.floorValue (Q ^ c v.1 i))⁻¹) *
      ZLattice.covolume (mixedEmbedding.integerLattice K) ^ Fintype.card ι := by
  rw [approxLattice, Submodule.covolume_mixedImage _ (fg_approxModule hL c Q)
    (span_approxModule Sfin L c hQ.ne') (B := approxDetBound Sfin L c Q)
    (apply_det_le_approxDetBound hL c hQ) (exists_det_eq_approxDetBound hL c hQ)]
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset (s := Sfin)]
  · rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v hv ↦ ?_
    simp only [approxDetBound, hv, ↓reduceIte]
    rw [mul_inv, inv_inv, Finset.prod_inv_distrib]
  · intro v hv
    by_contra hvS
    exact hv (by simp only [approxDetBound, Finset.mem_coe.not.1 hvS, ↓reduceIte])

end NumberField
