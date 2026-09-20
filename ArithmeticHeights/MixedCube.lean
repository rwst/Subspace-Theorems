/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.CubeSlicing
public import ArithmeticHeights.MixedBall

/-!
# The sup-norm body of a number field and the slices of its dilates

**The convex body of Layer 5.4.** For a number field `K` and a finite index type `κ` it is the
product over the infinite places of `K` of the sup-norm balls of the local coordinates of a
`κ`-tuple — a cube of half-side `ρ(1) = 1/2` at a real place and a polydisc of radius
`ρ(2) = π^{-1/2}` at a complex one, so that every one-coordinate factor has volume one. In the
standard real coordinates of `MixedBall.lean` the body **is** a product of euclidean balls of
volume one, one per block of a partition with blocks of size one at the real places and size two
at the complex ones, so Vaaler's product-of-balls theorem of Layer 4.5 applies verbatim: every
central slice by a real subspace has volume at least one.

## Main definitions

* `NumberField.mixedEmbedding.mixedBlock`: the partition of the standard real coordinates into the
  blocks of the body, one per place and coordinate.
* `NumberField.mixedEmbedding.realCoord` and `NumberField.mixedEmbedding.complexCoord`: a single
  coordinate of a point of the euclidean tuple space at a real, respectively complex, place.
* `NumberField.mixedEmbedding.mixedCube`: the body.

## Main results

* `NumberField.mixedEmbedding.preimage_mixedCube_mixedPiIsometry`: in the standard real
  coordinates the body is `prodBall (mixedBlock K κ)`.
* `NumberField.mixedEmbedding.one_le_volume_preimage_mixedCube`: **the slice bound** — every
  central slice of the body by a real subspace has volume at least one — through
  `NumberField.mixedEmbedding.hasSliceBound_mixedCube`.
* `NumberField.mixedEmbedding.convex_mixedCube`, `NumberField.mixedEmbedding.neg_mem_mixedCube`,
  `NumberField.mixedEmbedding.isClosed_mixedCube`,
  `NumberField.mixedEmbedding.isBounded_mixedCube` and
  `NumberField.mixedEmbedding.interior_mixedCube_nonempty`: the four hypotheses the geometry of
  numbers carries, plus closedness.
* `NumberField.mixedEmbedding.mem_smul_mixedCube`: membership in a dilate, coordinate by
  coordinate.

## Implementation notes

⚠ **The factors are normalised to volume one, and the anisotropy is paid in the height, not in the
volume.** The body one would write down first is the unit cube at each real place and the unit
polydisc at each complex one; its slices cost `2 ^ k` and `π ^ k` respectively, by Layer 4.5.
Those two normalisations cannot be undone by a dilation, because the factor needed at a real place
(`2`) differs from the one needed at a complex place (`√π`), and an *anisotropic* dilation does not
preserve the subspace being sliced — the slice of the dilate is not the dilate of the slice. So the
body is defined with `ballRadius` in it, the slice bound is a clean `1`, and the two constants
reappear in `BombieriVaalerMaxNorm.lean` when a point of a dilate is converted into a height. This
is also why the body must be a product **over the places**: one bound on the whole tuple cannot be
split back per place without losing a constant.

⚠ **The slice bound is an inequality here, where Layer 5.3's was an identity.** The ℓ² body of
`MixedBall.lean` has an isometry group large enough to compute its slice exactly — orthonormalise
a `K`-basis of the subspace at each infinite place — and Layer 4.5 is not used there at all. The
sup-norm body has no such group, and the bound is Vaaler's cube-slicing theorem, used once. That
is the whole difference between the two milestones, and Vaaler says so: the Hermitian inequality
follows from the max-norm theorem, while the max-norm form "is more difficult because it requires
the cube-slicing inequality".

⚠ **`ω₂ = π` is the only ball volume needed beyond `ω₁ = 2`.** Both are proved in
`CubeSlicing.lean` (`unitBallVolume_one`, `unitBallVolume_two`), and `ballRadius_two` turns the
second into the radius `π ^ (-1/2)` the body is defined with. No other closed form for `ω_n` is
ever required, here or in Layer 4.5.

⚠ **`Fintype κ` is deliberately absent from the statements about the body.** The body is cut out
by individual coordinates, so its definition, and convexity, closedness, boundedness and its
interior, mention only the topology of `mixedPi K κ` — the product topology, which needs no
`Fintype`. The hypothesis is therefore `Finite κ`, and the proofs, which do sum over `κ`, obtain a
`Fintype` from `Fintype.ofFinite`. The ℓ² body of Layer 5.3 is genuinely different: its definition
names the norm of `EuclideanSpace ℝ κ`, so the `Fintype` instance occurs in its type.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem C.3.8; J. D. Vaaler, *A geometric inequality with applications to linear forms*, Pacific
Journal of Mathematics **83** (1979), 543–553.

This is Layer 5.4 (infrastructure) of the `ArithmeticHeights` roadmap.
-/

public section

open MeasureTheory Measure Set ENNReal Pointwise
open scoped Real

namespace NumberField.mixedEmbedding

open Module MeasureTheory NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K] (κ : Type*) [Fintype κ]

/-- The partition of the standard real coordinates into the blocks of the sup-norm body: one
coordinate at a real place, two at a complex one. -/
@[expose] def mixedBlock : mixedIndex K κ →
    ({w : InfinitePlace K // IsReal w} × κ) ⊕ ({w : InfinitePlace K // IsComplex w} × κ) :=
  Sum.elim Sum.inl fun q ↦ Sum.inr (q.1, Sum.elim id id q.2)

variable {K κ}

omit [Fintype κ] in
/-- A block at a real place is a single coordinate. -/
def realBlockEquiv (w : {w : InfinitePlace K // IsReal w}) (j : κ) :
    {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inl (w, j)} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨Sum.inl (w, j), rfl⟩
  left_inv := by
    rintro ⟨idx | idx, hidx⟩
    · refine Subtype.ext ?_
      simpa [mixedBlock] using hidx.symm
    · simp [mixedBlock] at hidx
  right_inv _ := rfl

omit [Fintype κ] in
/-- A block at a complex place is a pair of coordinates. -/
def complexBlockEquiv (w : {w : InfinitePlace K // IsComplex w}) (j : κ) :
    {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inr (w, j)} ≃ (Unit ⊕ Unit) where
  toFun a :=
    Sum.elim (fun _ ↦ Sum.inl ())
      (fun q ↦ Sum.elim (fun _ ↦ Sum.inl ()) (fun _ ↦ Sum.inr ()) q.2) a.1
  invFun := Sum.elim (fun _ ↦ ⟨Sum.inr (w, Sum.inl j), rfl⟩)
    fun _ ↦ ⟨Sum.inr (w, Sum.inr j), rfl⟩
  left_inv := by
    rintro ⟨idx | ⟨w', s | s⟩, hidx⟩
    · simp [mixedBlock] at hidx
    · refine Subtype.ext ?_
      simp only [mixedBlock, Sum.elim_inr, Sum.inr.injEq, Prod.mk.injEq, Sum.elim_inl,
        id_eq] at hidx
      simp [hidx.1, hidx.2]
    · refine Subtype.ext ?_
      simp only [mixedBlock, Sum.elim_inr, Sum.inr.injEq, Prod.mk.injEq, Sum.elim_inr,
        id_eq] at hidx
      simp [hidx.1, hidx.2]
  right_inv := by rintro (⟨⟩ | ⟨⟩) <;> rfl


open scoped Classical in
omit [Fintype κ] [NumberField K] in
theorem card_realBlock (w : {w : InfinitePlace K // IsReal w}) (j : κ)
    [Fintype {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inl (w, j)}] :
    Fintype.card {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inl (w, j)} = 1 := by
  rw [Fintype.card_congr (realBlockEquiv w j), Fintype.card_punit]

open scoped Classical in
omit [Fintype κ] [NumberField K] in
theorem card_complexBlock (w : {w : InfinitePlace K // IsComplex w}) (j : κ)
    [Fintype {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inr (w, j)}] :
    Fintype.card {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inr (w, j)} = 2 := by
  rw [Fintype.card_congr (complexBlockEquiv w j)]
  simp

open scoped Classical in
omit [Fintype κ] [NumberField K] in
theorem sum_realBlock (w : {w : InfinitePlace K // IsReal w}) (j : κ)
    [Fintype {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inl (w, j)}]
    (f : mixedIndex K κ → ℝ) :
    ∑ idx : {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inl (w, j)}, f idx
      = f (Sum.inl (w, j)) := by
  rw [← Equiv.sum_comp (realBlockEquiv w j).symm
    (fun idx : {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inl (w, j)} ↦ f idx)]
  simp [realBlockEquiv]

open scoped Classical in
omit [Fintype κ] [NumberField K] in
theorem sum_complexBlock (w : {w : InfinitePlace K // IsComplex w}) (j : κ)
    [Fintype {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inr (w, j)}]
    (f : mixedIndex K κ → ℝ) :
    ∑ idx : {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inr (w, j)}, f idx
      = f (Sum.inr (w, Sum.inl j)) + f (Sum.inr (w, Sum.inr j)) := by
  rw [← Equiv.sum_comp (complexBlockEquiv w j).symm
    (fun idx : {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inr (w, j)} ↦ f idx)]
  simp [complexBlockEquiv]

variable (K κ)

open scoped Classical in
/-- The coordinate of a point of the euclidean tuple space at a real place. -/
@[expose] noncomputable def realCoord (w : {w : InfinitePlace K // IsReal w}) (j : κ) :
    mixedPi K κ →ₗ[ℝ] ℝ where
  toFun x := realPart K κ w x j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open scoped Classical in
/-- The coordinate of a point of the euclidean tuple space at a complex place. -/
@[expose] noncomputable def complexCoord (w : {w : InfinitePlace K // IsComplex w}) (j : κ) :
    mixedPi K κ →ₗ[ℝ] ℂ where
  toFun x := complexPart K κ w x j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open scoped Classical in
/-- **The convex body of Layer 5.4**: the product over the infinite places of the sup-norm unit
balls of the local coordinates, scaled to make each factor of volume one. -/
@[expose] def mixedCube : Set (mixedPi K κ) :=
  (⋂ (w : {w : InfinitePlace K // IsReal w}) (j : κ),
      realCoord K κ w j ⁻¹' Metric.closedBall 0 (ballRadius 1)) ∩
    ⋂ (w : {w : InfinitePlace K // IsComplex w}) (j : κ),
      complexCoord K κ w j ⁻¹' Metric.closedBall 0 (ballRadius 2)

variable {K κ}

open scoped Classical in
omit [Fintype κ] in
theorem mem_mixedCube {x : mixedPi K κ} :
    x ∈ mixedCube K κ ↔ (∀ w j, |realCoord K κ w j x| ≤ ballRadius 1) ∧
      ∀ w j, ‖complexCoord K κ w j x‖ ≤ ballRadius 2 := by
  simp [mixedCube, Real.norm_eq_abs]

private theorem sq_norm_complex_mk (a b : ℝ) : ‖(⟨a, b⟩ : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_mk]; ring

open scoped Classical in
theorem preimage_mixedCube_mixedPiIsometry :
    (mixedPiIsometry K κ) ⁻¹' mixedCube K κ = prodBall (mixedBlock K κ) := by
  ext c
  have hR : ∀ (w : {w : InfinitePlace K // IsReal w}) (j : κ),
      (|realCoord K κ w j (mixedPiIsometry K κ c)| ≤ ballRadius 1)
        ↔ (∑ idx : {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inl (w, j)},
              WithLp.ofLp c ↑idx ^ 2
            ≤ ballRadius (Fintype.card
                {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inl (w, j)}) ^ 2) := by
    intro w j
    rw [card_realBlock, sum_realBlock w j (fun idx ↦ WithLp.ofLp c idx ^ 2),
      ← sq_le_sq_iff_abs_le (ballRadius_pos 1).le]
    rfl
  have hC : ∀ (w : {w : InfinitePlace K // IsComplex w}) (j : κ),
      (‖complexCoord K κ w j (mixedPiIsometry K κ c)‖ ≤ ballRadius 2)
        ↔ (∑ idx : {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inr (w, j)},
              WithLp.ofLp c ↑idx ^ 2
            ≤ ballRadius (Fintype.card
                {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inr (w, j)}) ^ 2) := by
    intro w j
    rw [card_complexBlock, sum_complexBlock w j (fun idx ↦ WithLp.ofLp c idx ^ 2),
      ← sq_norm_complex_mk, sq_le_sq_iff_abs_le (ballRadius_pos 2).le, abs_norm]
    rfl
  rw [Set.mem_preimage, mem_mixedCube]
  change _ ↔ ∀ k, _
  rw [Sum.forall]
  refine and_congr ?_ ?_
  · rw [Prod.forall]
    exact forall_congr' fun w ↦ forall_congr' fun j ↦ hR w j
  · rw [Prod.forall]
    exact forall_congr' fun w ↦ forall_congr' fun j ↦ hC w j


open scoped Classical in
theorem sq_norm_realPart (w : {w : InfinitePlace K // IsReal w}) (x : mixedPi K κ) :
    ‖realPart K κ w x‖ ^ 2 = ∑ j, realCoord K κ w j x ^ 2 := by
  rw [realPart_apply, EuclideanSpace.sq_norm_toLp]
  rfl

open scoped Classical in
theorem sq_norm_complexPart (w : {w : InfinitePlace K // IsComplex w}) (x : mixedPi K κ) :
    ‖complexPart K κ w x‖ ^ 2 = ∑ j, ‖complexCoord K κ w j x‖ ^ 2 := by
  rw [complexPart_apply, EuclideanSpace.sq_norm_toLp_complex]
  exact Finset.sum_congr rfl fun j _ ↦ (Complex.sq_norm _).symm

open scoped Classical in
omit [Fintype κ] in
theorem convex_mixedCube : Convex ℝ (mixedCube K κ) := by
  refine Convex.inter (convex_iInter fun w ↦ convex_iInter fun j ↦ ?_)
    (convex_iInter fun w ↦ convex_iInter fun j ↦ ?_)
  · exact (convex_closedBall _ _).linear_preimage (realCoord K κ w j)
  · exact (convex_closedBall _ _).linear_preimage (complexCoord K κ w j)

open scoped Classical in
omit [Fintype κ] in
theorem neg_mem_mixedCube {x : mixedPi K κ} (hx : x ∈ mixedCube K κ) : -x ∈ mixedCube K κ := by
  rw [mem_mixedCube] at hx ⊢
  simpa using hx

open scoped Classical in
omit [Fintype κ] in
theorem isClosed_mixedCube [Finite κ] : IsClosed (mixedCube K κ) := by
  let _i : Fintype κ := Fintype.ofFinite κ
  refine IsClosed.inter (isClosed_iInter fun w ↦ isClosed_iInter fun j ↦ ?_)
    (isClosed_iInter fun w ↦ isClosed_iInter fun j ↦ ?_)
  · exact Metric.isClosed_closedBall.preimage
      (realCoord K κ w j).continuous_of_finiteDimensional
  · exact Metric.isClosed_closedBall.preimage
      (complexCoord K κ w j).continuous_of_finiteDimensional

open scoped Classical in
omit [Fintype κ] in
theorem isBounded_mixedCube [Finite κ] : Bornology.IsBounded (mixedCube K κ) := by
  let _i : Fintype κ := Fintype.ofFinite κ
  rw [Metric.isBounded_iff_subset_closedBall 0]
  set c : ℝ := max (ballRadius 1) (ballRadius 2) with hc
  have hc0 : 0 ≤ c := le_trans (ballRadius_pos 1).le (le_max_left _ _)
  set R : ℝ := Real.sqrt
    (((nrRealPlaces K + nrComplexPlaces K : ℕ) : ℝ) * Fintype.card κ * c ^ 2) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hRsq : R ^ 2 = ((nrRealPlaces K + nrComplexPlaces K : ℕ) : ℝ) * Fintype.card κ * c ^ 2 :=
    Real.sq_sqrt (by positivity)
  refine ⟨R, fun x hx ↦ ?_⟩
  rw [mem_closedBall_zero_iff, ← abs_norm, ← sq_le_sq_iff_abs_le hR0]
  rw [mem_mixedCube] at hx
  have h1 : ∀ w, ‖realPart K κ w x‖ ^ 2 ≤ (Fintype.card κ : ℝ) * c ^ 2 := by
    intro w
    rw [sq_norm_realPart]
    calc ∑ j, realCoord K κ w j x ^ 2 ≤ ∑ _j : κ, c ^ 2 :=
          Finset.sum_le_sum fun j _ ↦ by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) ((hx.1 w j).trans (le_max_left _ _)) 2
      _ = (Fintype.card κ : ℝ) * c ^ 2 := by simp
  have h2 : ∀ w, ‖complexPart K κ w x‖ ^ 2 ≤ (Fintype.card κ : ℝ) * c ^ 2 := by
    intro w
    rw [sq_norm_complexPart]
    calc ∑ j, ‖complexCoord K κ w j x‖ ^ 2 ≤ ∑ _j : κ, c ^ 2 :=
          Finset.sum_le_sum fun j _ ↦
            pow_le_pow_left₀ (norm_nonneg _) ((hx.2 w j).trans (le_max_right _ _)) 2
      _ = (Fintype.card κ : ℝ) * c ^ 2 := by simp
  rw [hRsq, norm_sq_mixedPi]
  have e1 : ∑ w : {w : InfinitePlace K // IsReal w}, ‖realPart K κ w x‖ ^ 2
      ≤ (nrRealPlaces K : ℝ) * ((Fintype.card κ : ℝ) * c ^ 2) := by
    calc ∑ w : {w : InfinitePlace K // IsReal w}, ‖realPart K κ w x‖ ^ 2
        ≤ ∑ _w : {w : InfinitePlace K // IsReal w}, (Fintype.card κ : ℝ) * c ^ 2 :=
          Finset.sum_le_sum fun w _ ↦ h1 w
      _ = (nrRealPlaces K : ℝ) * ((Fintype.card κ : ℝ) * c ^ 2) := by
          simp [nrRealPlaces, mul_comm]
  have e2 : ∑ w : {w : InfinitePlace K // IsComplex w}, ‖complexPart K κ w x‖ ^ 2
      ≤ (nrComplexPlaces K : ℝ) * ((Fintype.card κ : ℝ) * c ^ 2) := by
    calc ∑ w : {w : InfinitePlace K // IsComplex w}, ‖complexPart K κ w x‖ ^ 2
        ≤ ∑ _w : {w : InfinitePlace K // IsComplex w}, (Fintype.card κ : ℝ) * c ^ 2 :=
          Finset.sum_le_sum fun w _ ↦ h2 w
      _ = (nrComplexPlaces K : ℝ) * ((Fintype.card κ : ℝ) * c ^ 2) := by
          simp [nrComplexPlaces, mul_comm]
  push_cast
  nlinarith [e1, e2]

open scoped Classical in
omit [Fintype κ] in
theorem interior_mixedCube_nonempty [Finite κ] : (interior (mixedCube K κ)).Nonempty := by
  let _i : Fintype κ := Fintype.ofFinite κ
  refine ⟨0, ?_⟩
  rw [mem_interior_iff_mem_nhds]
  refine Filter.inter_mem (Filter.iInter_mem.2 fun w ↦ Filter.iInter_mem.2 fun j ↦ ?_)
    (Filter.iInter_mem.2 fun w ↦ Filter.iInter_mem.2 fun j ↦ ?_)
  · refine (realCoord K κ w j).continuous_of_finiteDimensional.continuousAt.preimage_mem_nhds ?_
    rw [map_zero]
    exact Metric.closedBall_mem_nhds (0 : ℝ) (ballRadius_pos 1)
  · refine (complexCoord K κ w j).continuous_of_finiteDimensional.continuousAt.preimage_mem_nhds ?_
    rw [map_zero]
    exact Metric.closedBall_mem_nhds (0 : ℂ) (ballRadius_pos 2)



open scoped Classical in
/-- **Bombieri–Gubler's Theorem C.3.8 for the body of Layer 5.4.** -/
theorem hasSliceBound_mixedCube :
    HasSliceBound (volume : Measure (mixedPi K κ)) gaussDensity (mixedCube K κ) := by
  have hmp : MeasurePreserving ((mixedPiIsometry K κ).symm) (volume : Measure (mixedPi K κ))
      (volume : Measure (EuclideanSpace ℝ (mixedIndex K κ))) :=
    LinearIsometryEquiv.measurePreserving _
  have h := HasSliceBound.of_measurePreserving (mixedPiIsometry K κ).symm.toLinearEquiv hmp
    (mixedPiIsometry K κ).continuous.measurable measurable_gaussDensity
    (measurableSet_prodBall (mixedBlock K κ)) (hasSliceBound_prodBall (mixedBlock K κ))
  have hdens : (fun x : mixedPi K κ ↦ gaussDensity ((mixedPiIsometry K κ).symm.toLinearEquiv x))
      = gaussDensity := by
    funext x
    rw [gaussDensity_def, gaussDensity_def,
      show ((mixedPiIsometry K κ).symm.toLinearEquiv) x = (mixedPiIsometry K κ).symm x from rfl,
      (mixedPiIsometry K κ).symm.norm_map]
  have hset : ((mixedPiIsometry K κ).symm.toLinearEquiv) ⁻¹' prodBall (mixedBlock K κ)
      = mixedCube K κ := by
    rw [← preimage_mixedCube_mixedPiIsometry, Set.preimage_preimage]
    simp
  rw [hdens, hset] at h
  exact h

open scoped Classical in
/-- **The slice bound of Layer 5.4**: every central slice of the body has volume at least one. -/
theorem one_le_volume_preimage_mixedCube (V : Submodule ℝ (mixedPi K κ)) :
    1 ≤ volume {y : V | (y : mixedPi K κ) ∈ mixedCube K κ} :=
  one_le_volume_subtype_mem (E := mixedPi K κ) (Q := mixedCube K κ)
    isClosed_mixedCube.measurableSet convex_mixedCube
    (fun _ hx ↦ neg_mem_mixedCube hx) hasSliceBound_mixedCube V


open scoped Classical in
omit [Fintype κ] in
theorem mem_smul_mixedCube {r : ℝ} (hr : 0 < r) {x : mixedPi K κ} :
    x ∈ r • mixedCube K κ ↔ (∀ w j, |realCoord K κ w j x| ≤ r * ballRadius 1) ∧
      ∀ w j, ‖complexCoord K κ w j x‖ ≤ r * ballRadius 2 := by
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne', mem_mixedCube]
  simp only [map_smul, smul_eq_mul, abs_mul, abs_inv, _root_.norm_smul,
    norm_inv, Real.norm_eq_abs, abs_of_pos hr, inv_mul_le_iff₀ hr]
end NumberField.mixedEmbedding
