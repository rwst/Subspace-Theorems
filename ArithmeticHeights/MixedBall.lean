/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.CubeSlicing
public import ArithmeticHeights.NumberFieldLattice
public import Mathlib.Analysis.Matrix.LDL

/-!
# The ℓ² body of a number field and the volume of its slices

For a number field `K` and a finite index type `κ`, the euclidean tuple space `mixedPi K κ` of
Layer 4.3 carries the convex body

```text
mixedBall K κ  =  { x : ∀ v | ∞, ‖x_v‖₂ ≤ 1 },
```

the product over the infinite places of the unit balls of the ℓ² norms of the local coordinates.
This file computes the volume of its slice by the real span of a `K`-subspace `V ⊆ Kⁱ`:

```text
vol (mixedBall K ι ∩ V_ℝ)  =  ω_k ^ r₁ · ω_{2k} ^ r₂,      k = dim_K V,
```

`ω_n` the volume of the unit ball of `ℝⁿ`. **At each infinite place the slice of a euclidean ball
by a subspace is a euclidean ball of the smaller dimension**, which is why Layer 5.3 needs no
slicing inequality — unlike Layer 5.4, whose body is a product of cubes and polydiscs.

## Main definitions

* `NumberField.mixedEmbedding.mixedIndex`: the index type of the standard real coordinates of the
  euclidean tuple space, one block per infinite place.
* `NumberField.mixedEmbedding.toMixedTuple`, `NumberField.mixedEmbedding.mixedPiIsometry`: those
  coordinates, as a linear equivalence and as a linear isometry from a euclidean space.
* `NumberField.mixedEmbedding.realPart`, `NumberField.mixedEmbedding.complexPart`: the local
  coordinate tuple at a real, respectively complex, place.
* `NumberField.mixedEmbedding.mixedBall`: the body itself.
* `NumberField.mixedEmbedding.ofLocal`: the matrix over the mixed space assembled from a family
  of matrices over `ℝ` and `ℂ`, one per infinite place.

## Main results

* `NumberField.mixedEmbedding.volume_mixedBall`: the volume of the body is
  `ω_{#κ} ^ r₁ · ω_{2 #κ} ^ r₂`.
* `NumberField.mixedEmbedding.volume_preimage_mixedBall_mixedSpan`: **the slice bound**, the
  displayed identity above, with the slice measured inside the real span of `V`.
* `Matrix.exists_mul_conjTranspose_eq_one`: **local orthonormalization**, a matrix over `ℝ` or `ℂ`
  with nonzero Gram determinant becomes orthonormal after an invertible row operation.
* `NumberField.mixedEmbedding.exists_ofLocal_eq_mul`: the same over the mixed space, place by
  place, which is what produces an *isometry* onto the real span.
* `MeasureTheory.measurePreserving_uncurry`: a product measure over a product index type is the
  iterated product measure.
* `MeasureTheory.volume_prodSqBall`: the volume of a product of ℓ² unit balls.

## Implementation notes

⚠ **The slice is computed by moving the lattice's ambient space, not by slicing.** A `K`-basis `y`
of `V` gives a map `mixedPiMap Y` of euclidean tuple spaces whose range is the real span of `V`,
but which is not an isometry. Orthonormalizing `Y` *at each infinite place* — `LDL` over `ℝ` and
over `ℂ`, assembled by `ofLocal` — replaces it by `E = M Y` with `E Eᴴ = 1` locally, and then
`mixedPiMap E` is an isometry with the same range, carrying `mixedBall K (Fin k)` onto the slice.
The volume of the slice is therefore the volume of the *whole* body in a smaller tuple space,
where no subspace appears at all.

⚠ **The ranges are compared by dimension, so `M` never has to be inverted.** `E = M Y` gives
`range (mixedPiMap E) ≤ range (mixedPiMap Y)` for free, both maps are injective, and the real span
of `V` sits inside the second range because every element of `V` is a `K`-combination of the `y`'s.
All three subspaces have dimension `[K : ℚ] · k`, so all three coincide.

⚠ **The volume of the body is a product measure computation in coordinates.** The standard real
coordinates identify `mixedPi K κ` isometrically with `EuclideanSpace ℝ (mixedIndex K κ)`, and the
body becomes a product over the places of ℓ² unit balls in `κ`, respectively `κ ⊕ κ`, coordinates.
Turning that into `∏` of volumes needs the currying `Measure.pi (fun _ : α × β ↦ μ) =
Measure.pi (fun _ : α ↦ Measure.pi fun _ : β ↦ μ)`, which Mathlib has for sums of index types but
not for products; `MeasureTheory.measurePreserving_uncurry` supplies it.

⚠ **`Matrix.PosSemidef` has no square root in Mathlib**, so the local orthonormalization goes
through the `LDL` decomposition: `L S Lᴴ` is diagonal with positive entries, and a diagonal matrix
does have a square root. What is needed is only *some* `M` with `M S Mᴴ = 1`, not the symmetric
one.

## References

E. Bombieri and J. D. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), §I.

J. D. Vaaler, "The best constant in Siegel's lemma", *Monatshefte für Mathematik* **140** (2003),
71–89, where the inequality this file's slice bound feeds is quoted as (1.3).

This is Layer 5.3 (infrastructure) of the `ArithmeticHeights` roadmap.
-/

public section

namespace NumberField.mixedEmbedding

open Module MeasureTheory NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K] (κ : Type*)

/-- The index type of the standard real coordinates of the euclidean tuple space. -/
abbrev mixedIndex : Type _ :=
  ({w : InfinitePlace K // IsReal w} × κ) ⊕ ({w : InfinitePlace K // IsComplex w} × (κ ⊕ κ))

/-- Standard real coordinates on the tuples of mixed-space points. -/
@[expose] def toMixedTuple : (mixedIndex K κ → ℝ) ≃ₗ[ℝ] (κ → mixedSpace K) where
  toFun c := fun j ↦ (fun w ↦ c (.inl (w, j)),
    fun w ↦ ⟨c (.inr (w, .inl j)), c (.inr (w, .inr j))⟩)
  invFun u := Sum.elim (fun p ↦ (u p.2).1 p.1)
    (fun q ↦ Sum.elim (fun j ↦ ((u j).2 q.1).re) (fun j ↦ ((u j).2 q.1).im) q.2)
  map_add' _ _ := rfl
  map_smul' r c := by
    ext j
    · rfl
    · simp [Complex.ext_iff, Complex.real_smul]
  left_inv c := by
    ext idx
    rcases idx with p | ⟨w, j | j⟩ <;> rfl
  right_inv u := by
    ext j
    · rfl
    · rfl

variable {K κ}

open scoped Classical in
theorem mixedTrace_star_mul_toMixedTuple (c c' : mixedIndex K κ → ℝ) (j : κ) :
    mixedTrace K (star ((toMixedTuple K κ c) j) * ((toMixedTuple K κ c') j))
      = (∑ w : {w : InfinitePlace K // IsReal w}, c (.inl (w, j)) * c' (.inl (w, j)))
        + ∑ w : {w : InfinitePlace K // IsComplex w},
            (c (.inr (w, .inl j)) * c' (.inr (w, .inl j))
              + c (.inr (w, .inr j)) * c' (.inr (w, .inr j))) := by
  simp only [mixedTrace, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have h1 : (star ((toMixedTuple K κ) c j) * (toMixedTuple K κ) c' j).2 w
      = (starRingEnd ℂ) ⟨c (.inr (w, .inl j)), c (.inr (w, .inr j))⟩ *
        ⟨c' (.inr (w, .inl j)), c' (.inr (w, .inr j))⟩ := rfl
  rw [h1, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

variable [Fintype κ]

open scoped Classical in
theorem inner_toMixedPi_toMixedTuple (c c' : mixedIndex K κ → ℝ) :
    inner ℝ (toMixedPi K κ (toMixedTuple K κ c)) (toMixedPi K κ (toMixedTuple K κ c'))
      = ∑ idx, c idx * c' idx := by
  rw [inner_toMixedPi]
  simp only [mixedTrace_star_mul_toMixedTuple]
  rw [Finset.sum_add_distrib, Fintype.sum_sum_type]
  congr 1
  · rw [Fintype.sum_prod_type]; exact Finset.sum_comm
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [Fintype.sum_sum_type, Finset.sum_add_distrib]

variable (K κ)

open scoped Classical in
/-- The standard real coordinates identify the euclidean tuple space with a euclidean space. -/
@[expose] noncomputable def mixedPiIsometry :
    EuclideanSpace ℝ (mixedIndex K κ) ≃ₗᵢ[ℝ] mixedPi K κ :=
  LinearEquiv.isometryOfInner
    (((WithLp.linearEquiv 2 ℝ (mixedIndex K κ → ℝ)).trans (toMixedTuple K κ)).trans
      (toMixedPi K κ))
    (fun x y ↦ by
      rw [show (((WithLp.linearEquiv 2 ℝ (mixedIndex K κ → ℝ)).trans (toMixedTuple K κ)).trans
            (toMixedPi K κ)) x
          = toMixedPi K κ (toMixedTuple K κ (WithLp.ofLp x)) from rfl,
        show (((WithLp.linearEquiv 2 ℝ (mixedIndex K κ → ℝ)).trans (toMixedTuple K κ)).trans
            (toMixedPi K κ)) y
          = toMixedPi K κ (toMixedTuple K κ (WithLp.ofLp y)) from rfl,
        inner_toMixedPi_toMixedTuple, PiLp.inner_apply]
      exact Finset.sum_congr rfl fun i _ ↦ by
        change WithLp.ofLp x i * WithLp.ofLp y i = inner ℝ (WithLp.ofLp x i) (WithLp.ofLp y i)
        rw [RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm])

open scoped Classical in
@[simp] theorem mixedPiIsometry_apply (c : EuclideanSpace ℝ (mixedIndex K κ)) :
    mixedPiIsometry K κ c = toMixedPi K κ (toMixedTuple K κ (WithLp.ofLp c)) := rfl

open scoped Classical in
theorem measurePreserving_mixedPiIsometry :
    MeasurePreserving (mixedPiIsometry K κ) :=
  LinearIsometryEquiv.measurePreserving _

end NumberField.mixedEmbedding

namespace MeasureTheory

/-- The product measure over a product index type is the iterated product measure. -/
theorem measurePreserving_uncurry {α β X : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (fun f : α → β → X ↦ fun p : α × β ↦ f p.1 p.2)
      (Measure.pi fun _ : α ↦ Measure.pi fun _ : β ↦ μ) (Measure.pi fun _ : α × β ↦ μ) := by
  have hmeas : Measurable (fun f : α → β → X ↦ fun p : α × β ↦ f p.1 p.2) := by
    apply Measurable.of_eval
    intro p
    exact (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  refine ⟨hmeas, ?_⟩
  refine (Measure.pi_eq fun t ht ↦ ?_).symm
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi ht)]
  have hpre : (fun f : α → β → X ↦ fun p : α × β ↦ f p.1 p.2) ⁻¹' (Set.univ.pi t)
      = Set.univ.pi fun a ↦ Set.univ.pi fun b ↦ t (a, b) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_univ_pi, Prod.forall]
  rw [hpre, Measure.pi_pi]
  simp only [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

end MeasureTheory

namespace MeasureTheory

open Metric

theorem EuclideanSpace.sq_norm_toLp {α : Type*} [Fintype α] (a : α → ℝ) :
    ‖(WithLp.toLp 2 a : EuclideanSpace ℝ α)‖ ^ 2 = ∑ j, a j ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [Real.norm_eq_abs, sq_abs]

theorem EuclideanSpace.sq_norm_toLp_complex {α : Type*} [Fintype α] (z : α → ℂ) :
    ‖(WithLp.toLp 2 z : EuclideanSpace ℂ α)‖ ^ 2 = ∑ j, Complex.normSq (z j) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [Complex.sq_norm]

theorem volume_closedBall_euclideanSpace (α : Type*) [Fintype α] :
    volume (Metric.closedBall (0 : EuclideanSpace ℝ α) 1)
      = ENNReal.ofReal (unitBallVolume (Fintype.card α)) := by
  have h1 : volume (Metric.closedBall (0 : EuclideanSpace ℝ α) 1)
      = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Fintype.card α))) 1) := by
    rcases isEmpty_or_nonempty α with h | h
    · have hc : Fintype.card α = 0 := Fintype.card_eq_zero
      have he : IsEmpty (Fin (Fintype.card α)) := by rw [hc]; infer_instance
      rw [show (Metric.closedBall (0 : EuclideanSpace ℝ α) 1) = Set.univ from
          Set.eq_univ_of_forall fun x ↦ by simp [Subsingleton.elim x 0],
        show (Metric.ball (0 : EuclideanSpace ℝ (Fin (Fintype.card α))) 1) = Set.univ from
          Set.eq_univ_of_forall fun x ↦ by simp [Subsingleton.elim x 0]]
      rw [volume_euclideanSpace_eq_dirac, volume_euclideanSpace_eq_dirac]
      simp
    · have hne : Nonempty (Fin (Fintype.card α)) := by
        rw [← Fintype.card_pos_iff] at h ⊢
        simpa using h
      rw [EuclideanSpace.volume_closedBall, EuclideanSpace.volume_ball, Fintype.card_fin]
  rw [h1, unitBallVolume, ENNReal.ofReal_toReal measure_ball_lt_top.ne]

theorem volume_sqBall (α : Type*) [Fintype α] :
    volume {a : α → ℝ | ∑ j, a j ^ 2 ≤ 1} = ENNReal.ofReal (unitBallVolume (Fintype.card α)) := by
  have hpre : {a : α → ℝ | ∑ j, a j ^ 2 ≤ 1}
      = (WithLp.toLp 2 : (α → ℝ) → EuclideanSpace ℝ α) ⁻¹' (Metric.closedBall 0 1) := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, mem_closedBall_zero_iff,
      EuclideanSpace.norm_eq]
    rw [show (1 : ℝ) = Real.sqrt 1 by simp, Real.sqrt_le_sqrt_iff (by positivity)]
    simp [sq_abs]
  rw [hpre, (PiLp.volume_preserving_toLp α).measure_preimage
      measurableSet_closedBall.nullMeasurableSet, volume_closedBall_euclideanSpace]

theorem measurableSet_prodSqBall {ι α : Type*} [Finite ι] [Fintype α] :
    MeasurableSet {a : ι × α → ℝ | ∀ i, ∑ j, a (i, j) ^ 2 ≤ 1} := by
  have h : {a : ι × α → ℝ | ∀ i, ∑ j, a (i, j) ^ 2 ≤ 1}
      = ⋂ i : ι, {a : ι × α → ℝ | ∑ j, a (i, j) ^ 2 ≤ 1} := by ext a; simp
  rw [h]
  exact MeasurableSet.iInter fun i ↦ (isClosed_le (by fun_prop) continuous_const).measurableSet

/-- The volume of a product over `ι` of ℓ² unit balls in `α` coordinates. -/
theorem volume_prodSqBall {ι α : Type*} [Fintype ι] [Fintype α] :
    volume {a : ι × α → ℝ | ∀ i, ∑ j, a (i, j) ^ 2 ≤ 1}
      = ENNReal.ofReal (unitBallVolume (Fintype.card α)) ^ Fintype.card ι := by
  have hmp := MeasureTheory.measurePreserving_uncurry (α := ι) (β := α) (volume : Measure ℝ)
  have hpre : (fun f : ι → α → ℝ ↦ fun p : ι × α ↦ f p.1 p.2) ⁻¹'
      {a : ι × α → ℝ | ∀ i, ∑ j, a (i, j) ^ 2 ≤ 1}
      = Set.univ.pi fun _ : ι ↦ {a : α → ℝ | ∑ j, a j ^ 2 ≤ 1} := by
    ext f
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ_pi]
  rw [volume_pi, ← hmp.measure_preimage measurableSet_prodSqBall.nullMeasurableSet,
    hpre, Measure.pi_pi]
  simp only [← volume_pi, volume_sqBall, Finset.prod_const, Finset.card_univ]

end MeasureTheory

namespace NumberField.mixedEmbedding

open Module MeasureTheory NumberField NumberField.InfinitePlace
open scoped Pointwise

variable (K : Type*) [Field K] [NumberField K] (κ : Type*) [Fintype κ]

open scoped Classical in
/-- The tuple of coordinates of a point of the euclidean tuple space at a real place. -/
@[expose] noncomputable def realPart (w : {w : InfinitePlace K // IsReal w}) :
    mixedPi K κ →ₗ[ℝ] EuclideanSpace ℝ κ where
  toFun x := WithLp.toLp 2 (fun j ↦ (((toMixedPi K κ).symm x) j).1 w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open scoped Classical in
/-- The tuple of coordinates of a point of the euclidean tuple space at a complex place. -/
@[expose] noncomputable def complexPart (w : {w : InfinitePlace K // IsComplex w}) :
    mixedPi K κ →ₗ[ℝ] EuclideanSpace ℂ κ where
  toFun x := WithLp.toLp 2 (fun j ↦ (((toMixedPi K κ).symm x) j).2 w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype κ] in
open scoped Classical in
theorem realPart_apply (w : {w : InfinitePlace K // IsReal w}) (x : mixedPi K κ) :
    realPart K κ w x = WithLp.toLp 2 (fun j ↦ (((toMixedPi K κ).symm x) j).1 w) := rfl

omit [Fintype κ] in
open scoped Classical in
theorem complexPart_apply (w : {w : InfinitePlace K // IsComplex w}) (x : mixedPi K κ) :
    complexPart K κ w x = WithLp.toLp 2 (fun j ↦ (((toMixedPi K κ).symm x) j).2 w) := rfl

open scoped Classical in
/-- **The convex body of Layer 5.3**: the product over the infinite places of the unit balls of
the ℓ² norms of the local coordinates. -/
@[expose] def mixedBall : Set (mixedPi K κ) :=
  (⋂ w : {w : InfinitePlace K // IsReal w}, realPart K κ w ⁻¹' Metric.closedBall 0 1) ∩
    ⋂ w : {w : InfinitePlace K // IsComplex w}, complexPart K κ w ⁻¹' Metric.closedBall 0 1

variable {K κ}

open scoped Classical in
theorem mem_mixedBall {x : mixedPi K κ} :
    x ∈ mixedBall K κ ↔ (∀ w, ‖realPart K κ w x‖ ≤ 1) ∧ (∀ w, ‖complexPart K κ w x‖ ≤ 1) := by
  simp [mixedBall]

open scoped Classical in
theorem mem_smul_mixedBall {r : ℝ} (hr : 0 < r) {x : mixedPi K κ} :
    x ∈ r • mixedBall K κ ↔ (∀ w, ‖realPart K κ w x‖ ≤ r) ∧ (∀ w, ‖complexPart K κ w x‖ ≤ r) := by
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne', mem_mixedBall]
  simp only [map_smul, _root_.norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr,
    inv_mul_le_iff₀ hr, mul_one]

open scoped Classical in
theorem convex_mixedBall : Convex ℝ (mixedBall K κ) := by
  refine Convex.inter (convex_iInter fun w ↦ ?_) (convex_iInter fun w ↦ ?_)
  · exact (convex_closedBall _ _).linear_preimage (realPart K κ w)
  · exact (convex_closedBall _ _).linear_preimage (complexPart K κ w)

open scoped Classical in
theorem neg_mem_mixedBall {x : mixedPi K κ} (hx : x ∈ mixedBall K κ) :
    -x ∈ mixedBall K κ := by
  rw [mem_mixedBall] at hx ⊢
  simpa using hx


open scoped Classical in
theorem realPart_mixedPiIsometry (w : {w : InfinitePlace K // IsReal w})
    (c : EuclideanSpace ℝ (mixedIndex K κ)) :
    realPart K κ w (mixedPiIsometry K κ c)
      = WithLp.toLp 2 (fun j ↦ WithLp.ofLp c (.inl (w, j))) := rfl

open scoped Classical in
theorem complexPart_mixedPiIsometry (w : {w : InfinitePlace K // IsComplex w})
    (c : EuclideanSpace ℝ (mixedIndex K κ)) :
    complexPart K κ w (mixedPiIsometry K κ c)
      = WithLp.toLp 2 (fun j ↦ (⟨WithLp.ofLp c (.inr (w, .inl j)),
          WithLp.ofLp c (.inr (w, .inr j))⟩ : ℂ)) := rfl

open scoped Classical in
theorem norm_sq_mixedPi (x : mixedPi K κ) :
    ‖x‖ ^ 2 = (∑ w, ‖realPart K κ w x‖ ^ 2) + ∑ w, ‖complexPart K κ w x‖ ^ 2 := by
  obtain ⟨c, rfl⟩ := (mixedPiIsometry K κ).surjective x
  rw [(mixedPiIsometry K κ).norm_map]
  rw [show ‖c‖ ^ 2 = ∑ idx, (WithLp.ofLp c idx) ^ 2 by
    rw [← EuclideanSpace.sq_norm_toLp (WithLp.ofLp c), WithLp.toLp_ofLp]]
  simp only [realPart_mixedPiIsometry, complexPart_mixedPiIsometry,
    EuclideanSpace.sq_norm_toLp, EuclideanSpace.sq_norm_toLp_complex, Complex.normSq_mk]
  rw [Fintype.sum_sum_type]
  congr 1
  · rw [Fintype.sum_prod_type]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring

open scoped Classical in
theorem isClosed_mixedBall : IsClosed (mixedBall K κ) := by
  refine IsClosed.inter (isClosed_iInter fun w ↦ ?_) (isClosed_iInter fun w ↦ ?_)
  · exact Metric.isClosed_closedBall.preimage (realPart K κ w).continuous_of_finiteDimensional
  · exact Metric.isClosed_closedBall.preimage (complexPart K κ w).continuous_of_finiteDimensional

open scoped Classical in
theorem isBounded_mixedBall : Bornology.IsBounded (mixedBall K κ) := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨(nrRealPlaces K : ℝ) + nrComplexPlaces K + 1, fun x hx ↦ ?_⟩
  rw [mem_closedBall_zero_iff]
  rw [mem_mixedBall] at hx
  have hb : ‖x‖ ^ 2 ≤ (nrRealPlaces K : ℝ) + nrComplexPlaces K := by
    rw [norm_sq_mixedPi]
    gcongr with w _ w _
    · calc ∑ w, ‖realPart K κ w x‖ ^ 2 ≤ ∑ _w : {w : InfinitePlace K // IsReal w}, (1 : ℝ) :=
            Finset.sum_le_sum fun w _ ↦ by
              exact pow_le_one₀ (norm_nonneg _) (hx.1 w)
        _ = (nrRealPlaces K : ℝ) := by simp [nrRealPlaces]
    · calc ∑ w, ‖complexPart K κ w x‖ ^ 2 ≤ ∑ _w : {w : InfinitePlace K // IsComplex w}, (1 : ℝ) :=
            Finset.sum_le_sum fun w _ ↦ by
              exact pow_le_one₀ (norm_nonneg _) (hx.2 w)
        _ = (nrComplexPlaces K : ℝ) := by simp [nrComplexPlaces]
  nlinarith [norm_nonneg x, hb, Nat.cast_nonneg (α := ℝ) (nrRealPlaces K),
    Nat.cast_nonneg (α := ℝ) (nrComplexPlaces K)]

open scoped Classical in
theorem interior_mixedBall_nonempty : (interior (mixedBall K κ)).Nonempty := by
  refine ⟨0, ?_⟩
  rw [mem_interior_iff_mem_nhds]
  refine Filter.inter_mem (Filter.iInter_mem.2 fun w ↦ ?_) (Filter.iInter_mem.2 fun w ↦ ?_)
  · refine (realPart K κ w).continuous_of_finiteDimensional.continuousAt.preimage_mem_nhds ?_
    rw [map_zero]
    exact Metric.closedBall_mem_nhds (0 : EuclideanSpace ℝ κ) one_pos
  · refine (complexPart K κ w).continuous_of_finiteDimensional.continuousAt.preimage_mem_nhds ?_
    rw [map_zero]
    exact Metric.closedBall_mem_nhds (0 : EuclideanSpace ℂ κ) one_pos

open scoped Classical in
theorem norm_realPart_le_one_iff (w : {w : InfinitePlace K // IsReal w})
    (c : mixedIndex K κ → ℝ) :
    ‖realPart K κ w (mixedPiIsometry K κ (WithLp.toLp 2 c))‖ ≤ 1
      ↔ ∑ j, c (.inl (w, j)) ^ 2 ≤ 1 := by
  rw [← pow_le_one_iff_of_nonneg (norm_nonneg _) (two_ne_zero), realPart_mixedPiIsometry,
    EuclideanSpace.sq_norm_toLp]

open scoped Classical in
theorem norm_complexPart_le_one_iff (w : {w : InfinitePlace K // IsComplex w})
    (c : mixedIndex K κ → ℝ) :
    ‖complexPart K κ w (mixedPiIsometry K κ (WithLp.toLp 2 c))‖ ≤ 1
      ↔ ∑ p : κ ⊕ κ, c (.inr (w, p)) ^ 2 ≤ 1 := by
  rw [← pow_le_one_iff_of_nonneg (norm_nonneg _) (two_ne_zero), complexPart_mixedPiIsometry,
    EuclideanSpace.sq_norm_toLp_complex, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Iff.of_eq (congrArg (· ≤ 1) (Finset.sum_congr rfl fun j _ ↦ ?_))
  rw [Complex.normSq_mk]
  ring

open scoped Classical in
/-- **The volume of the body of Layer 5.3**: the product over the infinite places of the volumes
of the unit balls, `ω_k` at a real place and `ω_{2k}` at a complex one. -/
theorem volume_mixedBall :
    volume (mixedBall K κ)
      = ENNReal.ofReal (unitBallVolume (Fintype.card κ)) ^ nrRealPlaces K
        * ENNReal.ofReal (unitBallVolume (2 * Fintype.card κ)) ^ nrComplexPlaces K := by
  set A : Set (({w : InfinitePlace K // IsReal w} × κ) → ℝ) :=
    {a | ∀ w, ∑ j, a (w, j) ^ 2 ≤ 1} with hAdef
  set B : Set (({w : InfinitePlace K // IsComplex w} × (κ ⊕ κ)) → ℝ) :=
    {b | ∀ w, ∑ p, b (w, p) ^ 2 ≤ 1} with hBdef
  have hmp : MeasurePreserving
      (fun c : mixedIndex K κ → ℝ ↦ mixedPiIsometry K κ (WithLp.toLp 2 c)) :=
    (measurePreserving_mixedPiIsometry K κ).comp (PiLp.volume_preserving_toLp _)
  have hpre : (fun c : mixedIndex K κ → ℝ ↦ mixedPiIsometry K κ (WithLp.toLp 2 c)) ⁻¹'
      mixedBall K κ
      = (MeasurableEquiv.sumPiEquivProdPi (fun _ : mixedIndex K κ ↦ ℝ)) ⁻¹' (A ×ˢ B) := by
    ext c
    simp only [Set.mem_preimage, mem_mixedBall, norm_realPart_le_one_iff,
      norm_complexPart_le_one_iff, Set.mem_prod, hAdef, hBdef, Set.mem_ofPred_eq]
    rfl
  have hsum := measurePreserving_sumPiEquivProdPi (fun _ : mixedIndex K κ ↦ (volume : Measure ℝ))
  have hstep := hsum.measure_preimage
    ((measurableSet_prodSqBall.prod measurableSet_prodSqBall).nullMeasurableSet)
  rw [← hmp.measure_preimage isClosed_mixedBall.measurableSet.nullMeasurableSet, hpre, volume_pi,
    hstep, Measure.prod_prod, ← volume_pi, ← volume_pi, volume_prodSqBall,
    volume_prodSqBall, Fintype.card_sum, two_mul]

end NumberField.mixedEmbedding

namespace Matrix

open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {k : ℕ} {ι : Type*} [Fintype ι]

theorem vecMul_injective_of_det_gram_ne_zero (Y : Matrix (Fin k) ι 𝕜)
    (hY : (Y * Yᴴ).det ≠ 0) : Function.Injective (fun v ↦ v ᵥ* Y) := by
  intro a b hab
  simp only at hab
  have h : (a - b) ᵥ* Y = 0 := by rw [sub_vecMul, hab, sub_self]
  have h2 : (Y * Yᴴ)ᵀ *ᵥ (a - b) = (Y * Yᴴ)ᵀ *ᵥ 0 := by
    rw [mulVec_transpose, ← vecMul_vecMul, h, zero_vecMul, mulVec_zero]
  have hdet : ((Y * Yᴴ)ᵀ).det ≠ 0 := by rwa [det_transpose]
  exact sub_eq_zero.1 (Matrix.mulVec_injective_of_det_ne_zero hdet h2)

theorem posDef_mul_conjTranspose_self (Y : Matrix (Fin k) ι 𝕜) (hY : (Y * Yᴴ).det ≠ 0) :
    (Y * Yᴴ).PosDef :=
  Matrix.PosDef.mul_conjTranspose_self Y (vecMul_injective_of_det_gram_ne_zero Y hY)

/-- **Local orthonormalization.** A matrix whose rows are independent — equivalently, whose Gram
determinant is nonzero — becomes orthonormal after an invertible row operation. -/
theorem exists_mul_conjTranspose_eq_one (Y : Matrix (Fin k) ι 𝕜) (hY : (Y * Yᴴ).det ≠ 0) :
    ∃ M : Matrix (Fin k) (Fin k) 𝕜, M.det ≠ 0 ∧ (M * Y) * (M * Y)ᴴ = 1 := by
  classical
  have hPD : (Y * Yᴴ).PosDef := posDef_mul_conjTranspose_self Y hY
  set L := LDL.lowerInv hPD with hL
  have hLinv : Invertible L := LDL.invertibleLowerInv hPD
  have hdiag : LDL.diag hPD = L * (Y * Yᴴ) * Lᴴ := LDL.diag_eq_lowerInv_conj hPD
  have hLvec : Function.Injective (fun v ↦ v ᵥ* L) := by
    intro a b hab
    simp only at hab
    have : (a - b) ᵥ* L = 0 := by rw [sub_vecMul, hab, sub_self]
    have h2 : Lᵀ *ᵥ (a - b) = Lᵀ *ᵥ 0 := by rw [mulVec_transpose, this, mulVec_zero]
    have hdet : (Lᵀ).det ≠ 0 := by
      rw [det_transpose]
      exact (isUnit_iff_ne_zero).1 (isUnit_det_of_invertible L)
    exact sub_eq_zero.1 (Matrix.mulVec_injective_of_det_ne_zero hdet h2)
  have hDPD : (LDL.diag hPD).PosDef := by
    rw [hdiag]; exact hPD.mul_mul_conjTranspose_same hLvec
  have hd : ∀ i, 0 < LDL.diagEntries hPD i := Matrix.posDef_diagonal_iff.1 hDPD
  set r : Fin k → ℝ := fun i ↦ RCLike.re (LDL.diagEntries hPD i) with hr
  have hrpos : ∀ i, 0 < r i := fun i ↦ (RCLike.pos_iff.1 (hd i)).1
  have hdr : ∀ i, LDL.diagEntries hPD i = ((r i : ℝ) : 𝕜) := by
    intro i
    have := (RCLike.pos_iff.1 (hd i)).2
    exact (RCLike.ext (by simp [hr]) (by simp [this])).symm
  set D : Matrix (Fin k) (Fin k) 𝕜 := diagonal (fun i ↦ ((Real.sqrt (r i))⁻¹ : ℝ)) with hD
  refine ⟨D * L, ?_, ?_⟩
  · rw [det_mul, det_diagonal]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ ↦ ?_)
      ((isUnit_iff_ne_zero).1 (isUnit_det_of_invertible L))
    simp only [ne_eq, RCLike.ofReal_eq_zero, inv_eq_zero]
    exact (Real.sqrt_pos.2 (hrpos i)).ne'
  · have hstep : (D * L) * Y * ((D * L) * Y)ᴴ = D * (L * (Y * Yᴴ) * Lᴴ) * Dᴴ := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [hstep, ← hdiag, LDL.diag, hD, diagonal_conjTranspose, diagonal_mul_diagonal,
      diagonal_mul_diagonal, ← diagonal_one]
    refine congrArg _ (funext fun i ↦ ?_)
    simp only [Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal, hdr i]
    rw [← RCLike.ofReal_mul, ← RCLike.ofReal_mul]
    norm_cast
    field_simp
    rw [Real.sq_sqrt (hrpos i).le, div_self (hrpos i).ne']

/-- The ℓ² norm of a combination of the rows of an orthonormal matrix is the ℓ² norm of the
coefficients. -/
theorem sum_norm_sq_mulVec (B : Matrix (Fin k) ι 𝕜) (hB : B * Bᴴ = 1) (a : Fin k → 𝕜) :
    ∑ j, ‖∑ l, B l j * a l‖ ^ 2 = ∑ l, ‖a l‖ ^ 2 := by
  have hδ : ∀ l l' : Fin k, (∑ j, B l j * (starRingEnd 𝕜) (B l' j)) = if l = l' then 1 else 0 := by
    intro l l'
    have h := congrFun (congrFun hB l) l'
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ ↦ rfl
  have main : ∀ j : ι, ((‖∑ l, B l j * a l‖ ^ 2 : ℝ) : 𝕜)
      = ∑ l, ∑ l', (B l j * (starRingEnd 𝕜) (B l' j)) * (a l * (starRingEnd 𝕜) (a l')) := by
    intro j
    rw [RCLike.ofReal_pow, ← RCLike.mul_conj, map_sum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun l' _ ↦ by
      rw [map_mul]; ring
  have hcast : ((∑ j, ‖∑ l, B l j * a l‖ ^ 2 : ℝ) : 𝕜) = ((∑ l, ‖a l‖ ^ 2 : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_sum, RCLike.ofReal_sum]
    simp only [main]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [Finset.sum_comm, RCLike.ofReal_pow, ← RCLike.mul_conj]
    calc ∑ l', ∑ j, (B l j * (starRingEnd 𝕜) (B l' j)) * (a l * (starRingEnd 𝕜) (a l'))
        = ∑ l', (∑ j, B l j * (starRingEnd 𝕜) (B l' j)) * (a l * (starRingEnd 𝕜) (a l')) :=
          Finset.sum_congr rfl fun l' _ ↦ (Finset.sum_mul _ _ _).symm
      _ = a l * (starRingEnd 𝕜) (a l) := by
          rw [Finset.sum_eq_single l]
          · simp [hδ l l]
          · intro l' _ hne
            simp [hδ l l', Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ l) h
  exact_mod_cast hcast

end Matrix

namespace NumberField.mixedEmbedding

open Module MeasureTheory NumberField NumberField.InfinitePlace Matrix

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] {k : ℕ}

omit [Fintype ι] in
open scoped Classical in
theorem symm_mixedPiMap (Y : Matrix (Fin k) ι (mixedSpace K)) (u : mixedPi K (Fin k)) :
    (toMixedPi K ι).symm (mixedPiMap Y u) = Yᵀ *ᵥ ((toMixedPi K (Fin k)).symm u) := by
  rw [mixedPiMap]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.coe_restrictScalars, Matrix.toLin'_apply]
  exact (toMixedPi K ι).symm_apply_apply _

variable (K ι k) in
open scoped Classical in
/-- The matrix over the mixed space assembled from a family of local matrices. -/
@[expose] def ofLocal (A : {w : InfinitePlace K // IsReal w} → Matrix (Fin k) ι ℝ)
    (B : {w : InfinitePlace K // IsComplex w} → Matrix (Fin k) ι ℂ) :
    Matrix (Fin k) ι (mixedSpace K) :=
  Matrix.of fun l j ↦ (fun w ↦ A w l j, fun w ↦ B w l j)

omit [Fintype ι] in
open scoped Classical in
theorem realPart_mixedPiMap (A : {w : InfinitePlace K // IsReal w} → Matrix (Fin k) ι ℝ)
    (B : {w : InfinitePlace K // IsComplex w} → Matrix (Fin k) ι ℂ)
    (w : {w : InfinitePlace K // IsReal w}) (u : mixedPi K (Fin k)) :
    realPart K ι w (mixedPiMap (ofLocal K ι k A B) u)
      = WithLp.toLp 2 (fun j ↦ ∑ l, A w l j * ((toMixedPi K (Fin k)).symm u l).1 w) := by
  rw [realPart_apply, symm_mixedPiMap]
  congr 1
  funext j
  simp [Matrix.mulVec, dotProduct, ofLocal, Prod.fst_sum, Finset.sum_apply]

omit [Fintype ι] in
open scoped Classical in
theorem complexPart_mixedPiMap (A : {w : InfinitePlace K // IsReal w} → Matrix (Fin k) ι ℝ)
    (B : {w : InfinitePlace K // IsComplex w} → Matrix (Fin k) ι ℂ)
    (w : {w : InfinitePlace K // IsComplex w}) (u : mixedPi K (Fin k)) :
    complexPart K ι w (mixedPiMap (ofLocal K ι k A B) u)
      = WithLp.toLp 2 (fun j ↦ ∑ l, B w l j * ((toMixedPi K (Fin k)).symm u l).2 w) := by
  rw [complexPart_apply, symm_mixedPiMap]
  congr 1
  funext j
  simp [Matrix.mulVec, dotProduct, ofLocal, Prod.snd_sum, Finset.sum_apply]

open scoped Classical in
theorem norm_realPart_mixedPiMap
    {A : {w : InfinitePlace K // IsReal w} → Matrix (Fin k) ι ℝ}
    {B : {w : InfinitePlace K // IsComplex w} → Matrix (Fin k) ι ℂ}
    (hA : ∀ w, A w * (A w)ᴴ = 1) (w : {w : InfinitePlace K // IsReal w})
    (u : mixedPi K (Fin k)) :
    ‖realPart K ι w (mixedPiMap (ofLocal K ι k A B) u)‖ = ‖realPart K (Fin k) w u‖ := by
  have h1 : ‖realPart K ι w (mixedPiMap (ofLocal K ι k A B) u)‖ ^ 2
      = ‖realPart K (Fin k) w u‖ ^ 2 := by
    rw [realPart_mixedPiMap, EuclideanSpace.sq_norm_toLp, realPart_apply,
      EuclideanSpace.sq_norm_toLp]
    have h := sum_norm_sq_mulVec (A w) (hA w) (fun l ↦ ((toMixedPi K (Fin k)).symm u l).1 w)
    simpa only [Real.norm_eq_abs, sq_abs] using h
  rw [← Real.sqrt_sq (norm_nonneg (realPart K ι w (mixedPiMap (ofLocal K ι k A B) u))),
    ← Real.sqrt_sq (norm_nonneg (realPart K (Fin k) w u)), h1]

open scoped Classical in
theorem norm_complexPart_mixedPiMap
    {A : {w : InfinitePlace K // IsReal w} → Matrix (Fin k) ι ℝ}
    {B : {w : InfinitePlace K // IsComplex w} → Matrix (Fin k) ι ℂ}
    (hB : ∀ w, B w * (B w)ᴴ = 1) (w : {w : InfinitePlace K // IsComplex w})
    (u : mixedPi K (Fin k)) :
    ‖complexPart K ι w (mixedPiMap (ofLocal K ι k A B) u)‖ = ‖complexPart K (Fin k) w u‖ := by
  have h1 : ‖complexPart K ι w (mixedPiMap (ofLocal K ι k A B) u)‖ ^ 2
      = ‖complexPart K (Fin k) w u‖ ^ 2 := by
    rw [complexPart_mixedPiMap, EuclideanSpace.sq_norm_toLp_complex, complexPart_apply,
      EuclideanSpace.sq_norm_toLp_complex]
    have h := sum_norm_sq_mulVec (B w) (hB w) (fun l ↦ ((toMixedPi K (Fin k)).symm u l).2 w)
    simpa only [Complex.sq_norm] using h
  rw [← Real.sqrt_sq (norm_nonneg (complexPart K ι w (mixedPiMap (ofLocal K ι k A B) u))),
    ← Real.sqrt_sq (norm_nonneg (complexPart K (Fin k) w u)), h1]

open scoped Classical in
/-- **The map attached to a place-wise orthonormal matrix is an isometry.** -/
theorem norm_mixedPiMap_ofLocal
    {A : {w : InfinitePlace K // IsReal w} → Matrix (Fin k) ι ℝ}
    {B : {w : InfinitePlace K // IsComplex w} → Matrix (Fin k) ι ℂ}
    (hA : ∀ w, A w * (A w)ᴴ = 1) (hB : ∀ w, B w * (B w)ᴴ = 1) (u : mixedPi K (Fin k)) :
    ‖mixedPiMap (ofLocal K ι k A B) u‖ = ‖u‖ := by
  have h1 : ‖mixedPiMap (ofLocal K ι k A B) u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [norm_sq_mixedPi, norm_sq_mixedPi]
    congr 1
    · exact Finset.sum_congr rfl fun w _ ↦ by rw [norm_realPart_mixedPiMap hA]
    · exact Finset.sum_congr rfl fun w _ ↦ by rw [norm_complexPart_mixedPiMap hB]
  rw [← Real.sqrt_sq (norm_nonneg (mixedPiMap (ofLocal K ι k A B) u)),
    ← Real.sqrt_sq (norm_nonneg u), h1]

open scoped Classical in
/-- **The body is carried to the body.** -/
theorem preimage_mixedBall_mixedPiMap
    {A : {w : InfinitePlace K // IsReal w} → Matrix (Fin k) ι ℝ}
    {B : {w : InfinitePlace K // IsComplex w} → Matrix (Fin k) ι ℂ}
    (hA : ∀ w, A w * (A w)ᴴ = 1) (hB : ∀ w, B w * (B w)ᴴ = 1) :
    (mixedPiMap (ofLocal K ι k A B)) ⁻¹' mixedBall K ι = mixedBall K (Fin k) := by
  ext u
  simp only [Set.mem_preimage, mem_mixedBall, norm_realPart_mixedPiMap hA,
    norm_complexPart_mixedPiMap hB]

end NumberField.mixedEmbedding

namespace NumberField.mixedEmbedding

open Module MeasureTheory NumberField NumberField.InfinitePlace Matrix

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] {k : ℕ}

open scoped Classical in
/-- Evaluation of the mixed space at a real place. -/
@[expose] def evalReal (K : Type*) [Field K]
    (w : {w : InfinitePlace K // IsReal w}) : mixedSpace K →+* ℝ :=
  (Pi.evalRingHom _ w).comp (RingHom.fst _ _)

open scoped Classical in
/-- Evaluation of the mixed space at a complex place. -/
@[expose] def evalComplex (K : Type*) [Field K]
    (w : {w : InfinitePlace K // IsComplex w}) : mixedSpace K →+* ℂ :=
  (Pi.evalRingHom _ w).comp (RingHom.snd _ _)

omit [NumberField K] in
open scoped Classical in
@[simp] theorem evalReal_apply (w : {w : InfinitePlace K // IsReal w}) (z : mixedSpace K) :
    evalReal K w z = z.1 w := rfl

omit [NumberField K] in
open scoped Classical in
@[simp] theorem evalComplex_apply (w : {w : InfinitePlace K // IsComplex w}) (z : mixedSpace K) :
    evalComplex K w z = z.2 w := rfl

omit [Fintype ι] [NumberField K] in
open scoped Classical in
theorem map_conjTranspose_evalReal (w : {w : InfinitePlace K // IsReal w})
    (Z : Matrix (Fin k) ι (mixedSpace K)) :
    (Zᴴ).map (evalReal K w) = ((Z.map (evalReal K w))ᴴ) := by
  ext j l
  simp [Matrix.conjTranspose_apply]

omit [Fintype ι] [NumberField K] in
open scoped Classical in
theorem map_conjTranspose_evalComplex (w : {w : InfinitePlace K // IsComplex w})
    (Z : Matrix (Fin k) ι (mixedSpace K)) :
    (Zᴴ).map (evalComplex K w) = ((Z.map (evalComplex K w))ᴴ) := by
  ext j l
  simp [Matrix.conjTranspose_apply]

omit [NumberField K] in
open scoped Classical in
theorem det_gram_evalReal (w : {w : InfinitePlace K // IsReal w})
    (Z : Matrix (Fin k) ι (mixedSpace K)) :
    ((Z * Zᴴ).det).1 w
      = ((Z.map (evalReal K w)) * (Z.map (evalReal K w))ᴴ).det := by
  have h := RingHom.map_det (evalReal K w) (Z * Zᴴ)
  rw [evalReal_apply] at h
  rw [h]
  congr 1
  rw [RingHom.mapMatrix_apply, Matrix.map_mul, map_conjTranspose_evalReal]

omit [NumberField K] in
open scoped Classical in
theorem det_gram_evalComplex (w : {w : InfinitePlace K // IsComplex w})
    (Z : Matrix (Fin k) ι (mixedSpace K)) :
    ((Z * Zᴴ).det).2 w
      = ((Z.map (evalComplex K w)) * (Z.map (evalComplex K w))ᴴ).det := by
  have h := RingHom.map_det (evalComplex K w) (Z * Zᴴ)
  rw [evalComplex_apply] at h
  rw [h]
  congr 1
  rw [RingHom.mapMatrix_apply, Matrix.map_mul, map_conjTranspose_evalComplex]

open scoped Classical in
/-- **Place-wise orthonormalization.** A matrix over the mixed space with invertible Gram
endomorphism becomes orthonormal at every infinite place after a row operation over the mixed
space. -/
theorem exists_ofLocal_eq_mul (Z : Matrix (Fin k) ι (mixedSpace K))
    (hZ : LinearMap.det (mixedPiEnd Z) ≠ 0) :
    ∃ (A : {w : InfinitePlace K // IsReal w} → Matrix (Fin k) ι ℝ)
      (B : {w : InfinitePlace K // IsComplex w} → Matrix (Fin k) ι ℂ)
      (M : Matrix (Fin k) (Fin k) (mixedSpace K)),
      (∀ w, A w * (A w)ᴴ = 1) ∧ (∀ w, B w * (B w)ᴴ = 1) ∧ ofLocal K ι k A B = M * Z := by
  rw [det_mixedPiEnd, norm_mixedSpace] at hZ
  have hR : ∀ w : {w : InfinitePlace K // IsReal w},
      (((Z * Zᴴ).det).1 w) ≠ 0 := by
    intro w h
    exact hZ (by rw [Finset.prod_eq_zero (Finset.mem_univ w) h, zero_mul])
  have hC : ∀ w : {w : InfinitePlace K // IsComplex w},
      (((Z * Zᴴ).det).2 w) ≠ 0 := by
    intro w h
    refine hZ ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ w) (by rw [h, map_zero]), mul_zero]
  choose MR hMRdet hMR using fun w : {w : InfinitePlace K // IsReal w} ↦
    exists_mul_conjTranspose_eq_one (Z.map (evalReal K w))
      (by rw [← det_gram_evalReal]; exact hR w)
  choose MC hMCdet hMC using fun w : {w : InfinitePlace K // IsComplex w} ↦
    exists_mul_conjTranspose_eq_one (Z.map (evalComplex K w))
      (by rw [← det_gram_evalComplex]; exact hC w)
  refine ⟨fun w ↦ MR w * Z.map (evalReal K w), fun w ↦ MC w * Z.map (evalComplex K w),
    ofLocal K (Fin k) k MR MC, hMR, hMC, ?_⟩
  ext l j w
  · change (MR w * Z.map (evalReal K w)) l j = ((ofLocal K (Fin k) k MR MC * Z) l j).1 w
    rw [Matrix.mul_apply, Matrix.mul_apply, Prod.fst_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun l' _ ↦ rfl
  · change (MC w * Z.map (evalComplex K w)) l j = ((ofLocal K (Fin k) k MR MC * Z) l j).2 w
    rw [Matrix.mul_apply, Matrix.mul_apply, Prod.snd_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun l' _ ↦ rfl

omit [Fintype ι] in
open scoped Classical in
theorem mixedPiMap_mul (M : Matrix (Fin k) (Fin k) (mixedSpace K))
    (Y : Matrix (Fin k) ι (mixedSpace K)) (u : mixedPi K (Fin k)) :
    mixedPiMap (M * Y) u = mixedPiMap Y (mixedPiMap M u) := by
  refine (toMixedPi K ι).symm.injective ?_
  rw [symm_mixedPiMap, symm_mixedPiMap, symm_mixedPiMap, Matrix.transpose_mul,
    Matrix.mulVec_mulVec]

omit [Fintype ι] in
theorem exists_linearIndependent_span_eq [Finite ι] (V : Submodule K (ι → K)) :
    ∃ y : Fin (finrank K V) → (ι → K), LinearIndependent K y ∧
      Submodule.span K (Set.range y) = V := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  refine ⟨fun l ↦ ((Module.finBasis K V) l : ι → K), ?_, ?_⟩
  · exact (Module.finBasis K V).linearIndependent.map' V.subtype (by simp)
  · rw [show (Set.range fun l ↦ ((Module.finBasis K V) l : ι → K))
        = V.subtype '' (Set.range (Module.finBasis K V)) by rw [← Set.range_comp]; rfl,
      Submodule.span_image, (Module.finBasis K V).span_eq, Submodule.map_top,
      Submodule.range_subtype]

open scoped Classical in
theorem finrank_mixedPi (n : ℕ) : finrank ℝ (mixedPi K (Fin n)) = n * finrank ℚ K := by
  rw [LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ (∀ _ : Fin n, euclidean.mixedSpace K)),
    Module.finrank_pi_fintype ℝ]
  simp [euclidean.finrank]

open scoped Classical in
/-- **The slice of the body of Layer 5.3 by the real span of a subspace has volume
`ω_k^{r₁} · ω_{2k}^{r₂}`.** At each infinite place the slice of a euclidean ball by a subspace is
a euclidean ball of the smaller dimension, so no slicing inequality is needed. -/
theorem volume_preimage_mixedBall_mixedSpan [LinearOrder ι] (V : Submodule K (ι → K)) :
    volume ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedBall K ι)
      = ENNReal.ofReal (unitBallVolume (finrank K V)) ^ nrRealPlaces K
        * ENNReal.ofReal (unitBallVolume (2 * finrank K V)) ^ nrComplexPlaces K := by
  obtain ⟨y, hy, hspan⟩ := exists_linearIndependent_span_eq V
  have hYdet : LinearMap.det (mixedPiEnd ((Matrix.of y).map (mixedEmbedding K))) ≠ 0 :=
    (NumberField.det_mixedPiEnd_pos hy).ne'
  obtain ⟨A, B, M, hA, hB, hEM⟩ :=
    exists_ofLocal_eq_mul ((Matrix.of y).map (mixedEmbedding K)) hYdet
  have hiso : ∀ u, ‖mixedPiMap (ofLocal K ι (finrank K V) A B) u‖ = ‖u‖ :=
    norm_mixedPiMap_ofLocal hA hB
  have hEinj : Function.Injective (mixedPiMap (ofLocal K ι (finrank K V) A B)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h := hiso u
    rw [hu, norm_zero] at h
    exact norm_eq_zero.1 h.symm
  have hYinj : Function.Injective (mixedPiMap ((Matrix.of y).map (mixedEmbedding K))) :=
    NumberField.mixedPiMap_injective _ hYdet
  have hsubEY : LinearMap.range (mixedPiMap (ofLocal K ι (finrank K V) A B))
      ≤ LinearMap.range (mixedPiMap ((Matrix.of y).map (mixedEmbedding K))) := by
    rintro _ ⟨u, rfl⟩
    rw [hEM, mixedPiMap_mul]
    exact ⟨_, rfl⟩
  have hsubVY : V.mixedSpan
      ≤ LinearMap.range (mixedPiMap ((Matrix.of y).map (mixedEmbedding K))) := by
    rw [Submodule.mixedSpan, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hspan ▸ hx)
    exact ⟨toMixedPi K (Fin (finrank K V)) (fun l ↦ mixedEmbedding K (c l)),
      NumberField.mixedPiMap_emb y c⟩
  have hdimE : finrank ℝ ↥(LinearMap.range (mixedPiMap (ofLocal K ι (finrank K V) A B)))
      = finrank K V * finrank ℚ K := by
    rw [LinearMap.finrank_range_of_inj hEinj, finrank_mixedPi]
  have hdimY : finrank ℝ ↥(LinearMap.range (mixedPiMap ((Matrix.of y).map (mixedEmbedding K))))
      = finrank K V * finrank ℚ K := by
    rw [LinearMap.finrank_range_of_inj hYinj, finrank_mixedPi]
  have hdimV : finrank ℝ ↥V.mixedSpan = finrank K V * finrank ℚ K := by
    rw [V.finrank_mixedSpan, mul_comm]
  have hrange : LinearMap.range (mixedPiMap (ofLocal K ι (finrank K V) A B)) = V.mixedSpan := by
    rw [Submodule.eq_of_le_of_finrank_eq hsubEY (by rw [hdimE, hdimY]),
      Submodule.eq_of_le_of_finrank_eq hsubVY (by rw [hdimV, hdimY])]
  have hmem : ∀ u, mixedPiMap (ofLocal K ι (finrank K V) A B) u ∈ V.mixedSpan :=
    fun u ↦ hrange ▸ LinearMap.mem_range_self _ u
  have hgbij : Function.Bijective
      ((mixedPiMap (ofLocal K ι (finrank K V) A B)).codRestrict V.mixedSpan hmem) := by
    refine ⟨fun a b hab ↦ hEinj (congrArg Subtype.val hab), ?_⟩
    rintro ⟨z, hz⟩
    rw [← hrange] at hz
    obtain ⟨u, hu⟩ := hz
    exact ⟨u, Subtype.ext hu⟩
  let Φ : mixedPi K (Fin (finrank K V)) ≃ₗᵢ[ℝ] ↥V.mixedSpan :=
    { LinearEquiv.ofBijective _ hgbij with norm_map' := fun u ↦ hiso u }
  have hmp := LinearIsometryEquiv.measurePreserving (E := mixedPi K (Fin (finrank K V)))
    (F := ↥V.mixedSpan) Φ
  have hclosed : IsClosed ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedBall K ι) :=
    isClosed_mixedBall.preimage continuous_subtype_val
  have hpre : (Φ : mixedPi K (Fin (finrank K V)) → ↥V.mixedSpan) ⁻¹'
      ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedBall K ι)
      = mixedBall K (Fin (finrank K V)) := by
    rw [← Set.preimage_comp]
    exact preimage_mixedBall_mixedPiMap hA hB
  rw [← hmp.measure_preimage hclosed.measurableSet.nullMeasurableSet, hpre, volume_mixedBall,
    Fintype.card_fin]

end NumberField.mixedEmbedding
