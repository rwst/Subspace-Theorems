/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.MinimaBasis
public import ArithmeticHeights.MinkowskiSecond
public import Mathlib.NumberTheory.NumberField.House
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
# A reduced integral basis

Every number field `K` of degree `d` has a `ℤ`-basis of its ring of integers whose members all have
house at most `d · 2 ^ d · √|D_K|` (`NumberField.exists_basis_house_le`). The proof reads `𝓞 K`
as a lattice in the mixed space and takes the basis Cassels builds from its successive minima with
respect to the unit ball (`ZLattice.exists_basis_mem_smul_successiveMinimum`). The first minimum is
at least `1`, because a nonzero algebraic integer has house at least `1`. Minkowski's second
theorem (`ZLattice.prod_successiveMinimum_mul_measure_le`) then bounds the last minimum by
`2 ^ d covol(𝓞 K) / vol(ball)`, where `covol(𝓞 K) = 2 ^ (-r₂) √|D_K|` and the ball holds the
product of discs of volume `2 ^ r₁ π ^ r₂ ≥ 1`.

This replaces the arbitrary integral basis of Mathlib in the constant `c_K` of Layer 4.1, so that
`c_K` is bounded in terms of the discriminant.

## Main results

* `NumberField.norm_mixedEmbedding_eq_house`: the norm of the mixed embedding is the house.
* `NumberField.exists_basis_house_le`: **a reduced integral basis**.

## References

J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer (1959), Chapter V,
Lemma 8 and Chapter VIII, Theorem V.

This is part of Q0.2e of the `QuantitativeSubspace` roadmap.
-/

@[expose] public section

open Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory

open scoped Pointwise

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- **The bound for the reduced integral basis**, `d · 2 ^ d · √|D_K|`. -/
noncomputable def reducedBasisBound : ℝ :=
  finrank ℚ K * 2 ^ finrank ℚ K * √|(discr K : ℝ)|

variable {K}

open scoped Classical in
/-- **The norm of the mixed embedding is the house**: both are the largest absolute value of a
conjugate. -/
theorem norm_mixedEmbedding_eq_house (x : K) : ‖mixedEmbedding K x‖ = house x := by
  classical
  rw [norm_eq_sup'_normAtPlace]
  refine le_antisymm (Finset.sup'_le _ _ fun w _ ↦ ?_) ?_
  · rw [normAtPlace_apply, ← w.norm_embedding_eq]
    exact norm_embedding_le_house x _
  · rw [house, canonicalEmbedding.norm_le_iff]
    intro φ
    rw [← InfinitePlace.apply, ← normAtPlace_apply]
    exact Finset.le_sup' (fun w ↦ normAtPlace w (mixedEmbedding K x)) (Finset.mem_univ _)

variable (K) in
open scoped Classical in
/-- **A reduced integral basis**: `𝓞 K` has a `ℤ`-basis whose members all have house at most
`d · 2 ^ d · √|D_K|`. -/
theorem exists_basis_house_le :
    ∃ b : Basis (Fin (finrank ℚ K)) ℤ (𝓞 K), ∀ r, house (b r : K) ≤ reducedBasisBound K := by
  classical
  set f : 𝓞 K →ₗ[ℤ] mixedSpace K :=
    ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)).toIntAlgHom.toLinearMap with hf
  set L := mixedEmbedding.integerLattice K with hL
  set B : Set (mixedSpace K) := Metric.closedBall 0 1 with hBdef
  set d := finrank ℚ K with hd
  have hE : finrank ℝ (mixedSpace K) = d := mixedEmbedding.finrank K
  have hd0 : 0 < d := finrank_pos
  have hB₀ : Convex ℝ B := convex_closedBall 0 1
  have hB₁ : ∀ x ∈ B, -x ∈ B := fun x hx ↦ by
    rw [hBdef, mem_closedBall_zero_iff, norm_neg] at *
    exact hx
  have hB₂ : (interior B).Nonempty :=
    ⟨0, by rw [hBdef, interior_closedBall _ one_ne_zero]; exact Metric.mem_ball_self one_pos⟩
  have hB₃ : Bornology.IsBounded B := Metric.isBounded_closedBall
  have hB₄ : IsClosed B := Metric.isClosed_closedBall
  have hmem : ∀ {t : ℝ}, 0 < t → ∀ x : K, mixedEmbedding K x ∈ t • B → house x ≤ t := by
    intro t ht x hx
    rw [hBdef, smul_closedBall _ _ zero_le_one, smul_zero, mem_closedBall_zero_iff,
      Real.norm_of_nonneg ht.le, mul_one, norm_mixedEmbedding_eq_house] at hx
    exact hx
  set lam : ℕ → ℝ := ZLattice.successiveMinimum L B with hlam
  -- the first minimum is at least `1`
  have hlam0 : 1 ≤ lam 0 := by
    refine ZLattice.le_successiveMinimum (by rw [hE]; exact hd0) hB₀ hB₁ hB₂
      fun t ht v hv hind ↦ ?_
    obtain ⟨hvB, α, hα⟩ := hv 0
    have hα' : mixedEmbedding K (α : K) = v 0 := hα
    have hα0 : (α : K) ≠ 0 := by
      intro h
      rw [h, map_zero] at hα'
      exact hind.ne_zero 0 hα'.symm
    refine (one_le_house_of_isIntegral α.isIntegral_coe hα0).trans (hmem ht _ ?_)
    rw [hα']
    exact hvB
  have hlam1 : ∀ i < d, 1 ≤ lam i := fun i hi ↦ hlam0.trans
    (ZLattice.successiveMinimum_le_of_le (Nat.zero_le i) (by rw [hE]; exact hi) hB₀ hB₁ hB₂)
  -- Minkowski's second theorem
  have hmink := ZLattice.prod_successiveMinimum_mul_measure_le L volume hB₀ hB₁ hB₂ hB₃
  rw [hE] at hmink
  have hvol : 1 ≤ (volume B).toReal := by
    have hsub : convexBodyLT K (fun _ ↦ 1) ⊆ B := by
      rintro ⟨x₁, x₂⟩ ⟨h₁, h₂⟩
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_ball, dist_zero_right,
        NNReal.coe_one] at h₁ h₂
      rw [hBdef, mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
      exact ⟨(pi_norm_le_iff_of_nonneg zero_le_one).2 fun w ↦ (h₁ w).le,
        (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w ↦ (h₂ w).le⟩
    have h1 : (1 : ENNReal) ≤ volume B := by
      refine le_trans ?_ (measure_mono hsub)
      rw [convexBodyLT_volume]
      simp only [one_pow, Finset.prod_const_one]
      rw [ENNReal.coe_one, mul_one]
      exact_mod_cast one_le_convexBodyLTFactor K
    have hfin : volume B ≠ ⊤ := hB₃.measure_lt_top.ne
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hfin h1
  have hcov : ZLattice.covolume L volume ≤ √|(discr K : ℝ)| := by
    rw [hL, covolume_integerLattice]
    refine mul_le_of_le_one_left (Real.sqrt_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))
  have hprod1 : 0 ≤ ∏ i ∈ Finset.range d, lam i :=
    Finset.prod_nonneg fun i hi ↦ zero_le_one.trans (hlam1 i (Finset.mem_range.1 hi))
  have hlast : lam (d - 1) ≤ 2 ^ d * √|(discr K : ℝ)| := by
    have hle : lam (d - 1) ≤ ∏ i ∈ Finset.range d, lam i := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 (Nat.sub_lt hd0 one_pos))]
      refine le_mul_of_one_le_right (zero_le_one.trans (hlam1 _ (Nat.sub_lt hd0 one_pos))) ?_
      exact Finset.one_le_prod₀ fun i hi ↦
        hlam1 i (Finset.mem_range.1 (Finset.mem_of_mem_erase hi))
    calc lam (d - 1) ≤ ∏ i ∈ Finset.range d, lam i := hle
      _ ≤ (∏ i ∈ Finset.range d, lam i) * (volume B).toReal := le_mul_of_one_le_right hprod1 hvol
      _ ≤ 2 ^ d * ZLattice.covolume L volume := hmink
      _ ≤ 2 ^ d * √|(discr K : ℝ)| := mul_le_mul_of_nonneg_left hcov (by positivity)
  -- the basis
  obtain ⟨b, hb⟩ := ZLattice.exists_basis_mem_smul_successiveMinimum L hB₀ hB₁ hB₂ hB₃ hB₄
  have hinj : Function.Injective f := fun x y hxy ↦
    RingOfIntegers.coe_injective (mixedEmbedding_injective K hxy)
  set e : 𝓞 K ≃ₗ[ℤ] L := LinearEquiv.ofInjective f hinj with he
  refine ⟨(b.map e.symm).reindex (finCongr hE), fun r ↦ ?_⟩
  set i : Fin (finrank ℝ (mixedSpace K)) := (finCongr hE).symm r with hi
  have hr : ((b.map e.symm).reindex (finCongr hE)) r = e.symm (b i) := by
    rw [Basis.reindex_apply, Basis.map_apply]
  have hfe : mixedEmbedding K (((b.map e.symm).reindex (finCongr hE)) r : K) = (b i : _) := by
    rw [hr]
    exact congrArg Subtype.val (e.apply_symm_apply (b i))
  have hpos : 0 < lam i :=
    ZLattice.successiveMinimum_pos L hB₀ hB₁ hB₂ hB₃ i.isLt
  have hiN : (i : ℕ) < d := by rw [← hE]; exact i.isLt
  have hfac : max 1 ((((i : ℕ) : ℝ) + 1) / 2) ≤ d := by
    have : ((i : ℕ) : ℝ) + 1 ≤ d := by exact_mod_cast hiN
    refine max_le (by exact_mod_cast hd0) (by linarith)
  have hlami : lam i ≤ lam (d - 1) :=
    ZLattice.successiveMinimum_le_of_le (by omega) (by rw [hE]; omega) hB₀ hB₁ hB₂
  refine (hmem (by positivity) _ (hfe ▸ hb i)).trans ?_
  calc max 1 ((((i : ℕ) : ℝ) + 1) / 2) * lam i ≤ d * lam (d - 1) :=
        mul_le_mul hfac hlami hpos.le (by positivity)
    _ ≤ d * (2 ^ d * √|(discr K : ℝ)|) := mul_le_mul_of_nonneg_left hlast (by positivity)
    _ = reducedBasisBound K := by rw [reducedBasisBound]; ring

end NumberField
