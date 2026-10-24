/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Additions.Count
public import Bugeaud2013.Additions.SubspaceInterval

-- Used only inside proofs.
import DiophantineApproximation.DoublingSequences

/-!
# The number of points, with the interval form

The count of `Bugeaud2013/Additions/Count.lean` with the interval form of the quantitative
Subspace Theorem (`Real.SubspaceInterval α`) in steps (i) and (iv):

* **the first application** (`Real.exists_cover_four_intervals`): in each of the `⌈8/ε⌉ + 1`
  cells of `ρ = log Q / log H` the points lie in one proper subspace of `ℚ⁴`, or have `log H` in
  one of `K ε⁻² (1 + log ε⁻¹)` intervals `[s, K ε⁻¹ s)`;
* **the application on `T₀`** (`Real.exists_planes_t0_intervals`): the points of `T₀` lie in one
  plane, or have `log H` in one of `K ε⁻² (1 + log ε⁻¹)` such intervals.

The heights double (`Real.Doubling`), so an interval holds `O(log (K ε⁻¹))` points
(`Real.card_le_of_forall_mem_window`); a proper subspace holds `O(log ε⁻¹)` points outside `T₀`
(`Real.card_mem_le_of_ne_top`) and a plane `O(log ε⁻¹)` points
(`Real.card_mem_le_of_finrank_le_two`). Hence `K ε⁻³ (1 + log ε⁻¹)²` points
(`Real.card_le_of_cfPoints_third`), one power of `ε⁻¹` fewer than `Real.card_le_of_cfPoints`
gives with Evertse–Ferretti's `δ⁻³`.

## Main results

* `Real.exists_cover_four_intervals`, `Real.exists_planes_t0_intervals`: steps (i) and (iv).
* `Real.card_le_of_cfPoints_third`: the count.
* `Real.cfCount_two`: the count in the shape `Real.CFCount α 2`.

## References

J.-H. Evertse, R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*, Ann.
of Math. **177** (2013), 513–590, Theorem 3.3.

R. Stephan, *The Evertse–Ferretti interval result for a set of weights, and the exponent `1/2` in
three complexity bounds* (2026), Remark 8.1.
-/

@[expose] public section

open Finset Module

namespace Real

variable {α A ε c : ℝ} {D : ℕ}

/-- **The first application, interval form**: the points with `log H ≥ K ε^{-K}` lie in one of at
most `10 ε⁻¹` proper subspaces of `ℚ⁴`, or have `log H` in one of at most `K ε⁻³ (1 + log ε⁻¹)`
intervals `[s, K ε⁻¹ s)`. -/
theorem exists_cover_four_intervals (hSI : SubspaceInterval α) (hA : 1 ≤ A) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ T : Finset (Submodule ℚ (Fin 4 → ℚ)), (#T : ℝ) ≤ 10 * ε⁻¹ ∧ (∀ U ∈ T, U ≠ ⊤) ∧
      ∃ 𝒯 : Finset ℝ, (#𝒯 : ℝ) ≤ K * ε⁻¹ ^ 3 * (1 + log ε⁻¹) ∧
        ∀ (v : Fin 4 → ℤ) (H Q : ℝ), CFPoint α A ε v H Q → 1 ≤ log H →
          K * ε⁻¹ ^ K ≤ log H →
          (∃ U ∈ T, ptQ v ∈ U) ∨ ∃ s ∈ 𝒯, s ≤ log H ∧ log H < K * ε⁻¹ * s := by
  classical
  obtain ⟨K₄, hK₄, h4⟩ := hSI 4 (by norm_num) le_rfl
  have hA4 : (1 : ℝ) ≤ (A + 1) ^ 4 := one_le_pow₀ (by linarith)
  set C : ℝ := 24 * (A + 1) ^ 4 with hCdef
  have hC1 : 1 ≤ C := by simp only [C]; linarith
  have hlC : 0 ≤ log C := Real.log_nonneg hC1
  have hlA : 0 ≤ log (A + 1) := Real.log_nonneg (by linarith)
  have hlCA : 4 * log (A + 1) ≤ log C := by
    have := Real.log_le_log (by positivity) (show (A + 1) ^ 4 ≤ C by simp only [C]; linarith)
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  set κ := K₄ * 2 ^ K₄ * (1 + log C) + 4 * log (A + 1)
  set K := max (max K₄ κ) (80 * K₄)
  have hKK : K₄ ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hκK : κ ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have h80 : 80 * K₄ ≤ K := le_max_right _ _
  refine ⟨K, hK₄.trans hKK, fun ε hε hε1 ↦ ?_⟩
  have hεi : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
  have hL0 : 0 ≤ log ε⁻¹ := Real.log_nonneg hεi
  have hdet : (1 : ℝ) ≤ |(Matrix.of fun i k ↦ quadVal α (formCoef i k)).det| := by
    rw [det_formCoef, abs_neg, abs_one]
  have hcell := fun j (hj : j < cells ε) ↦
    h4 formCoef 1 le_rfl (fun i k m ↦ by exact_mod_cast abs_formCoef_le i k m) 1 one_pos le_rfl
      hdet C hC1 (cellExp ε j) (ε / 2) (by positivity) (by linarith)
      (cellExp_le_one hε hj) ⟨3, rfl⟩ (sum_cellExp_le hε j)
  choose! U hUtop 𝒯 h𝒯 hmem using hcell
  have hδi : (ε / 2)⁻¹ = 2 * ε⁻¹ := by rw [inv_div, div_eq_mul_inv]
  refine ⟨(range (cells ε)).image U, ?_, ?_, (range (cells ε)).biUnion 𝒯, ?_, ?_⟩
  · calc (#((range (cells ε)).image U) : ℝ) ≤ cells ε := by
          exact_mod_cast card_image_le.trans (card_range _).le
      _ ≤ 10 * ε⁻¹ := cells_le hε hε1
  · intro W hW
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hW
    exact hUtop j (mem_range.1 hj)
  · have hl : 1 + log (ε / 2)⁻¹ ≤ 2 * (1 + log ε⁻¹) := by
      rw [hδi, Real.log_mul (by norm_num) (by positivity)]
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have hl0 : 0 ≤ 1 + log (ε / 2)⁻¹ := by rw [hδi, Real.log_mul (by norm_num) (by positivity)]
                                           have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
                                           linarith
    refine (Nat.cast_le.2 card_biUnion_le).trans ?_
    push_cast
    calc ∑ j ∈ range (cells ε), (#(𝒯 j) : ℝ)
        ≤ ∑ _j ∈ range (cells ε), K₄ * (ε / 2)⁻¹ ^ 2 * (1 + log (ε / 2)⁻¹) :=
          Finset.sum_le_sum fun j hj ↦ h𝒯 j (Finset.mem_range.1 hj)
      _ = cells ε * (K₄ * (ε / 2)⁻¹ ^ 2 * (1 + log (ε / 2)⁻¹)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (10 * ε⁻¹) * (K₄ * (2 * ε⁻¹) ^ 2 * (2 * (1 + log ε⁻¹))) := by
          rw [hδi] at hl0 ⊢
          gcongr
          · exact cells_le hε hε1
          · rwa [hδi] at hl
      _ = 80 * K₄ * ε⁻¹ ^ 3 * (1 + log ε⁻¹) := by ring
      _ ≤ K * ε⁻¹ ^ 3 * (1 + log ε⁻¹) := by gcongr
  intro v H Q hp hH hlate
  have hlogH : 0 < log H := by linarith
  have hQ1 := hp.one_le_Q
  have hρ0 : 0 ≤ log Q / log H := div_nonneg (Real.log_nonneg hQ1) hlogH.le
  have hρ1 : log Q / log H ≤ 1 / 2 := by
    have := Real.log_le_log (by positivity) hp.sq_le
    rw [Real.log_pow] at this
    rw [div_le_iff₀ hlogH]
    push_cast at this; linarith
  obtain ⟨j, hj, h0, h1, -, -⟩ := exists_cell hε hρ0 hρ1
  have hv0 : v ≠ 0 := fun h ↦ hp.v0_ne_zero (by simp [h])
  set X := ⨆ k, |(v k : ℝ)| with hXdef
  have hX1 : 1 ≤ X := one_le_iSup_abs_of_cfPoint hp
  have hX0 : 0 < X := by linarith
  have hHX : H ≤ (A + 1) ^ 4 * X := hp.head.trans (by gcongr; exact abs_le_iSup_abs v 0)
  have hXH : X ≤ H := ciSup_le fun k ↦ hp.abs_le k
  have hYlog : log H - 4 * log (A + 1) ≤ log X := by
    have := Real.log_le_log hp.H_pos hHX
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at this
    push_cast at this
    linarith
  have hthr : K₄ * (ε / 2)⁻¹ ^ K₄ * (1 + log 1 + log C + log 1⁻¹) ≤ log X := by
    rw [inv_one, Real.log_one, add_zero, add_zero]
    have he2 : (ε / 2)⁻¹ ^ K₄ = 2 ^ K₄ * ε⁻¹ ^ K₄ := by
      rw [inv_div, div_eq_mul_inv, Real.mul_rpow (by norm_num) (by positivity)]
    have hp1 : 1 ≤ ε⁻¹ ^ K₄ := Real.one_le_rpow hεi (by linarith)
    have hp2 : ε⁻¹ ^ K₄ ≤ ε⁻¹ ^ K := Real.rpow_le_rpow_of_exponent_le hεi hKK
    have h3 : κ * ε⁻¹ ^ K₄ ≤ K * ε⁻¹ ^ K :=
      mul_le_mul hκK hp2 (by positivity) ((zero_le_one.trans hK₄).trans hKK)
    have h5 : 4 * log (A + 1) ≤ 4 * log (A + 1) * ε⁻¹ ^ K₄ :=
      le_mul_of_one_le_right (by positivity) hp1
    rw [he2]
    have : K₄ * (2 ^ K₄ * ε⁻¹ ^ K₄) * (1 + log C) + 4 * log (A + 1) * ε⁻¹ ^ K₄ =
        κ * ε⁻¹ ^ K₄ := by simp only [κ]; ring
    linarith
  rcases hmem j hj v hv0 (fun i ↦ cell_ineq hA hε.le hp hlogH (by positivity) h0 h1 i) hthr with
    hvU | ⟨s, hs, hs1, hs2⟩
  · exact .inl ⟨U j, mem_image_of_mem _ (mem_range.2 hj), hvU⟩
  refine .inr ⟨s, mem_biUnion.2 ⟨j, mem_range.2 hj, hs⟩, hs1.trans (Real.log_le_log hX0 hXH), ?_⟩
  -- `log H ≤ log X + 4 log (A + 1) < 2 K₄ (ε/2)⁻¹ s`
  have hthr0 : log C ≤ K₄ * (ε / 2)⁻¹ ^ K₄ * (1 + log C) := by
    have h1 : 1 ≤ (ε / 2)⁻¹ ^ K₄ := Real.one_le_rpow (by rw [hδi]; linarith) (by linarith)
    have : 1 ≤ K₄ * (ε / 2)⁻¹ ^ K₄ := one_le_mul_of_one_le_of_one_le hK₄ h1
    nlinarith
  have hbig : 4 * log (A + 1) ≤ K₄ * (ε / 2)⁻¹ * s := by
    rw [inv_one, Real.log_one, add_zero, add_zero] at hthr
    linarith
  have hs0 : 0 ≤ s := by
    by_contra hs0
    push Not at hs0
    have : 0 < K₄ * (ε / 2)⁻¹ := by positivity
    nlinarith [Real.log_nonneg hX1]
  calc log H ≤ log X + 4 * log (A + 1) := by linarith
    _ < 2 * (K₄ * (ε / 2)⁻¹ * s) := by linarith
    _ = 4 * K₄ * ε⁻¹ * s := by rw [hδi]; ring
    _ ≤ K * ε⁻¹ * s := by
        have : 0 ≤ ε⁻¹ * s := by positivity
        nlinarith

/-- **The application on `T₀`, interval form**: the points of `T₀` above `K ε^{-K}` lie in one
plane, or have `log H` in one of at most `K ε⁻² (1 + log ε⁻¹)` intervals `[s, K ε⁻¹ s)`. -/
theorem exists_planes_t0_intervals (hSI : SubspaceInterval α) (hA : 1 ≤ A) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ P : Submodule ℚ (Fin 4 → ℚ), finrank ℚ P ≤ 2 ∧
      ∃ 𝒯 : Finset ℝ, (#𝒯 : ℝ) ≤ K * ε⁻¹ ^ 2 * (1 + log ε⁻¹) ∧
        ∀ (v : Fin 4 → ℤ) (H Q : ℝ), CFPoint α A ε v H Q → v 1 = v 2 →
          K * ε⁻¹ ^ K ≤ log H → ptQ v ∈ P ∨ ∃ s ∈ 𝒯, s ≤ log H ∧ log H < K * ε⁻¹ * s := by
  classical
  obtain ⟨K₃, hK₃, h3⟩ := hSI 3 (by norm_num) (by norm_num)
  have hlA : 0 ≤ log (A + 1) := Real.log_nonneg (by linarith)
  have hA4 : (1 : ℝ) ≤ (A + 1) ^ 4 := one_le_pow₀ (by linarith)
  have hC1 : (1 : ℝ) ≤ 24 * (A + 1) ^ 4 := by linarith
  have hlCA : 4 * log (A + 1) ≤ log (24 * (A + 1) ^ 4) := by
    have := Real.log_le_log (by positivity) (show (A + 1) ^ 4 ≤ 24 * (A + 1) ^ 4 by linarith)
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  set κ : ℝ := 1 + log 2 + log (24 * (A + 1) ^ 4)
  have hκ : 0 ≤ κ := by
    have : 0 ≤ log 2 := Real.log_nonneg (by norm_num)
    have : 0 ≤ log (24 * (A + 1) ^ 4) := Real.log_nonneg hC1
    positivity
  set K := max (max K₃ (K₃ * κ + 4 * log (A + 1))) (2 * K₃)
  have hKK : K₃ ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hK2 : 2 * K₃ ≤ K := le_max_right _ _
  refine ⟨K, hK₃.trans hKK, fun ε hε hε1 ↦ ?_⟩
  have hεi : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
  obtain ⟨U, hU, 𝒯, h𝒯, hmem⟩ := h3 t0Coef 2 (by norm_num)
    (fun i k m ↦ by exact_mod_cast abs_t0Coef_le i k m) 1 one_pos le_rfl
    (by rw [det_t0Coef, abs_one]) (24 * (A + 1) ^ 4) hC1 ![-1 - ε, 0, 1] ε hε hε1
    (fun i ↦ by
      fin_cases i
      · simp only [Fin.zero_eta, Matrix.cons_val_zero]; linarith
      · simp
      · simp) ⟨2, rfl⟩
    (by simp [Fin.sum_univ_three]; linarith)
  have hL0 : 0 ≤ 1 + log ε⁻¹ := by have := Real.log_nonneg hεi; linarith
  refine ⟨t0Sub ⊓ U.comap t0Proj,
    finrank_inf_comap_le_two (fun x hx h0 ↦ eq_zero_of_mem_t0Sub hx h0) hU, 𝒯,
    h𝒯.trans (by gcongr), ?_⟩
  intro v H Q hp hv hlate
  have hH1 := hp.one_le_H
  have hH0 := hp.H_pos
  have hy0 : t0Pt v ≠ 0 := fun h ↦ hp.v0_ne_zero (by simpa [t0Pt] using congrFun h 0)
  set Y := ⨆ k, |(t0Pt v k : ℝ)| with hYdef
  have hY1 : 1 ≤ Y := one_le_iSup_abs hy0
  have hY0 : 0 < Y := by linarith
  have hYH : Y ≤ H := ciSup_le fun k ↦ by
    fin_cases k
    · exact hp.abs_le 0
    · exact hp.abs_le 1
    · exact hp.abs_le 3
  have hv0 : |(v 0 : ℝ)| ≤ Y := abs_le_iSup_abs (t0Pt v) 0
  have hHY : H ≤ (A + 1) ^ 4 * Y := hp.head.trans (by gcongr)
  have hineq : ∀ i, |∑ k, quadVal α (t0Coef i k) * t0Pt v k| ≤
      24 * (A + 1) ^ 4 * Y ^ (![-1 - ε, 0, 1] : Fin 3 → ℝ) i := by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, sum_t0Coef_zero α hv, Matrix.cons_val_zero]
      have h1 : H ^ (-1 - ε) ≤ Y ^ (-1 - ε) :=
        Real.rpow_le_rpow_of_nonpos hY0 hYH (by linarith)
      have h2 : 0 ≤ Y ^ (-1 - ε) := by positivity
      calc |formL1 α v| ≤ 24 * H ^ (-1 - ε) := hp.L1_le
        _ ≤ 24 * Y ^ (-1 - ε) := by gcongr
        _ ≤ 24 * (A + 1) ^ 4 * Y ^ (-1 - ε) := by nlinarith
    · simp only [Fin.mk_one, sum_t0Coef_one, Matrix.cons_val_one, Matrix.cons_val_zero,
        Real.rpow_zero, mul_one]
      have hQ1 := hp.one_le_Q
      calc |formL2 α v| ≤ 2 * Q ^ 2 / H := hp.L2_le
        _ ≤ 2 := by rw [div_le_iff₀ hH0]; nlinarith [hp.sq_le]
        _ ≤ 24 * (A + 1) ^ 4 := by linarith
    · simp only [Fin.reduceFinMk, sum_t0Coef_two, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, Real.rpow_one]
      nlinarith
  have hYlog : log H - 4 * log (A + 1) ≤ log Y := by
    have := Real.log_le_log hH0 hHY
    rw [Real.log_mul (by positivity) hY0.ne', Real.log_pow] at this
    push_cast at this
    linarith
  have hthr : K₃ * ε⁻¹ ^ K₃ * (1 + log 2 + log (24 * (A + 1) ^ 4) + log 1⁻¹) ≤ log Y := by
    rw [inv_one, Real.log_one, add_zero]
    have h1 : 1 ≤ ε⁻¹ ^ K₃ := Real.one_le_rpow hεi (by linarith)
    have h2 : ε⁻¹ ^ K₃ ≤ ε⁻¹ ^ K := Real.rpow_le_rpow_of_exponent_le hεi hKK
    have h3 : K₃ * κ + 4 * log (A + 1) ≤ K := (le_max_right _ _).trans (le_max_left _ _)
    have h4 : (K₃ * κ + 4 * log (A + 1)) * ε⁻¹ ^ K₃ ≤ K * ε⁻¹ ^ K :=
      mul_le_mul h3 h2 (by positivity) ((zero_le_one.trans hK₃).trans hKK)
    have h5 : 4 * log (A + 1) ≤ 4 * log (A + 1) * ε⁻¹ ^ K₃ :=
      le_mul_of_one_le_right (by positivity) h1
    nlinarith
  rcases hmem _ hy0 hineq hthr with hyU | ⟨s, hs, hs1, hs2⟩
  · refine .inl (Submodule.mem_inf.2 ⟨ptQ_mem_t0Sub hv, ?_⟩)
    rw [Submodule.mem_comap, t0Proj_ptQ]
    exact hyU
  refine .inr ⟨s, hs, hs1.trans (Real.log_le_log hY0 hYH), ?_⟩
  -- `log H ≤ log Y + 4 log (A + 1) < 2 K₃ ε⁻¹ s`
  have hthr0 : 4 * log (A + 1) ≤ K₃ * ε⁻¹ ^ K₃ * (1 + log 2 + log (24 * (A + 1) ^ 4)) := by
    have h1 : 1 ≤ ε⁻¹ ^ K₃ := Real.one_le_rpow hεi (by linarith)
    have : 1 ≤ K₃ * ε⁻¹ ^ K₃ := one_le_mul_of_one_le_of_one_le hK₃ h1
    have : 0 ≤ log (2 : ℝ) := Real.log_nonneg (by norm_num)
    nlinarith
  have hbig : 4 * log (A + 1) ≤ K₃ * ε⁻¹ * s := by
    rw [inv_one, Real.log_one, add_zero] at hthr
    linarith
  have hs0 : 0 ≤ s := by
    by_contra hs0
    push Not at hs0
    have : 0 < K₃ * ε⁻¹ := by positivity
    nlinarith [Real.log_nonneg hY1]
  calc log H ≤ log Y + 4 * log (A + 1) := by linarith
    _ < 2 * (K₃ * ε⁻¹ * s) := by linarith
    _ ≤ K * ε⁻¹ * s := by
        have : 0 ≤ ε⁻¹ * s := by positivity
        nlinarith

variable {Hs Qs : ℕ → ℝ} {vs : ℕ → Fin 4 → ℤ}

/-- **The count of the points, with the interval form.** If the interval form
`Real.SubspaceInterval α` and some `Real.SubspaceBound α a` hold, then a family of points of §3
with exponent `ε`, doubling heights and `log H ≥ K ε^{-K}` has at most
`K ε⁻³ (1 + log ε⁻¹)²` members. -/
theorem card_le_of_cfPoints_third {a : ℝ} (hSI : SubspaceInterval α) (hSB : SubspaceBound α a)
    (hA : 1 ≤ A) (hc : 0 < c) (hL : LiouvilleQuad α c D) (hα : |α| ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (Hs Qs : ℕ → ℝ) (vs : ℕ → Fin 4 → ℤ)
      (I : Finset ℕ), Doubling Hs → (∀ k ∈ I, CFPoint α A ε (vs k) (Hs k) (Qs k)) →
      (∀ k ∈ I, K * ε⁻¹ ^ K ≤ log (Hs k)) →
      (#I : ℝ) ≤ K * ε⁻¹ ^ 3 * (1 + log ε⁻¹) ^ 2 := by
  classical
  obtain ⟨K4, hK4, hcov4⟩ := exists_cover_four_intervals hSI hA
  obtain ⟨Kt, hKt, hcovt⟩ := exists_planes_t0_intervals hSI hA
  obtain ⟨KE, NT, hNT, hcovE⟩ := exists_planeCover hSB hA hc hL
  set cP := 4 * log (log (twoConst c D) + 4 * D + 4) + 6
  have hcP : 0 ≤ cP := by
    have : 0 ≤ log (log (twoConst c D) + 4 * D + 4) := by
      have := Real.log_nonneg (one_le_twoConst hc D)
      have : (0 : ℝ) ≤ D := Nat.cast_nonneg _
      exact Real.log_nonneg (by linarith)
    simp only [cP]; linarith
  set ME := max 1 (9 * KE)
  have hlME : 0 ≤ logb 2 ME := Real.logb_nonneg (by norm_num) (le_max_left _ _)
  set cH := (NT + 1) * cP + logb 2 ME + 1
  have hcH : 0 ≤ cH := by positivity
  have hlK4 := Real.log_nonneg hK4
  have hlKt := Real.log_nonneg hKt
  set Kc := cP + 10 * cH + K4 * (2 * log K4 + 3) + Kt * (2 * log Kt + 3)
  have hKc0 : 0 ≤ Kc := by positivity
  set K := max 1 (max (max K4 Kt) Kc)
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK4K : K4 ≤ K := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hKtK : Kt ≤ K := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hKcK : Kc ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K, by linarith, fun ε hε hε1 Hs Qs vs I hdbl hpt hthr ↦ ?_⟩
  have hεi : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
  set L := log ε⁻¹ with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg hεi
  -- the thresholds
  have hthr' (K' : ℝ) (hK' : K' ≤ K) (hK'0 : 0 ≤ K') (k : ℕ) (hk : k ∈ I) :
      K' * ε⁻¹ ^ K' ≤ log (Hs k) :=
    (mul_le_mul hK' (Real.rpow_le_rpow_of_exponent_le hεi hK') (by positivity)
      (by linarith)).trans (hthr k hk)
  -- the covers
  obtain ⟨T4, hT4, hT4top, 𝒯4, h𝒯4, hT4mem⟩ := hcov4 ε hε hε1
  obtain ⟨P0, hP0, 𝒯0, h𝒯0, hP0mem⟩ := hcovt ε hε hε1
  -- the heights double
  set g : ℕ → ℝ := fun k ↦ log (Hs k) with hg
  have hg0 : ∀ k, 0 < g k := fun k ↦ by have := hdbl.one_le_log k; simp only [hg]; linarith
  have hgq : ∀ k, 2 * g k ≤ g (k + 1) := hdbl.two_mul_log_le
  have hKX : ∀ K' : ℝ, 1 ≤ K' → 1 ≤ K' * ε⁻¹ := fun K' hK' ↦
    one_le_mul_of_one_le_of_one_le hK' hεi
  -- the points of `T₀` and the others
  set J0 := I.filter fun k ↦ vs k 1 = vs k 2 with hJ0
  set J1 := I.filter fun k ↦ vs k 1 ≠ vs k 2 with hJ1
  have hIJ : (#I : ℝ) = #J0 + #J1 := by
    have h := card_filter_add_card_filter_not (s := I) fun k ↦ vs k 1 = vs k 2
    rw [← Nat.cast_add]
    exact congrArg Nat.cast h.symm
  -- `T₀`: one plane, and windows
  set J0a := J0.filter fun k ↦ ptQ (vs k) ∈ P0 with hJ0a
  set J0b := J0.filter fun k ↦ ptQ (vs k) ∉ P0 with hJ0b
  have hJ0s : (#J0 : ℝ) = #J0a + #J0b := by
    have h := card_filter_add_card_filter_not (s := J0) fun k ↦ ptQ (vs k) ∈ P0
    rw [← Nat.cast_add]
    exact congrArg Nat.cast h.symm
  have hJ0a : (#J0a : ℝ) ≤ planeBound c D ε := by
    refine le_trans ?_ (card_mem_le_of_finrank_le_two hc hL hα hε hε1 hdbl I hpt P0 hP0)
    refine Nat.cast_le.2 (card_le_card fun k hk ↦ ?_)
    obtain ⟨hk0, hkP⟩ := mem_filter.1 hk
    exact mem_filter.2 ⟨(mem_filter.1 hk0).1, hkP⟩
  have hJ0b : (#J0b : ℝ) ≤ #𝒯0 * (log (Kt * ε⁻¹) / log 2 + 1) :=
    card_le_of_forall_mem_window (by norm_num) hg0 hgq (hKX Kt hKt) 𝒯0 fun k hk ↦ by
      obtain ⟨hk0, hkP⟩ := mem_filter.1 hk
      obtain ⟨hkI, hk12⟩ := mem_filter.1 hk0
      exact (hP0mem (vs k) (Hs k) (Qs k) (hpt k hkI) hk12
        (hthr' Kt hKtK (by linarith) k hkI)).resolve_left hkP
  -- the others: the subspaces of the cells, and windows
  set J1a := J1.filter fun k ↦ ∃ S ∈ T4, ptQ (vs k) ∈ S with hJ1a
  set J1b := J1.filter fun k ↦ ¬ ∃ S ∈ T4, ptQ (vs k) ∈ S with hJ1b
  have hJ1s : (#J1 : ℝ) = #J1a + #J1b := by
    have h := card_filter_add_card_filter_not (s := J1) fun k ↦ ∃ S ∈ T4, ptQ (vs k) ∈ S
    rw [← Nat.cast_add]
    exact congrArg Nat.cast h.symm
  set HB := (NT + 1) * planeBound c D ε + logb 2 ME + 1 with hHBdef
  have hJ1a : (#J1a : ℝ) ≤ #T4 * HB := by
    have hsub : J1a ⊆ T4.biUnion fun S ↦ {k ∈ I | ptQ (vs k) ∈ S ∧ vs k 1 ≠ vs k 2} := by
      intro k hk
      obtain ⟨hk1, S, hS, hkS⟩ := mem_filter.1 hk
      obtain ⟨hkI, hk12⟩ := mem_filter.1 hk1
      exact mem_biUnion.2 ⟨S, hS, mem_filter.2 ⟨hkI, hkS, hk12⟩⟩
    refine (Nat.cast_le.2 ((card_le_card hsub).trans card_biUnion_le)).trans ?_
    push_cast
    calc ∑ S ∈ T4, (#{k ∈ I | ptQ (vs k) ∈ S ∧ vs k 1 ≠ vs k 2} : ℝ) ≤ ∑ _S ∈ T4, HB :=
          Finset.sum_le_sum fun S hS ↦
            card_mem_le_of_ne_top hc hL hα hε hε1 hdbl I hpt hNT hcovE S (hT4top S hS)
      _ = #T4 * HB := by rw [Finset.sum_const, nsmul_eq_mul]
  have hJ1b : (#J1b : ℝ) ≤ #𝒯4 * (log (K4 * ε⁻¹) / log 2 + 1) :=
    card_le_of_forall_mem_window (by norm_num) hg0 hgq (hKX K4 hK4) 𝒯4 fun k hk ↦ by
      obtain ⟨hk1, hkS⟩ := mem_filter.1 hk
      have hkI := (mem_filter.1 hk1).1
      exact (hT4mem (vs k) (Hs k) (Qs k) (hpt k hkI) (hdbl.one_le_log k)
        (hthr' K4 hK4K (by linarith) k hkI)).resolve_left hkS
  -- the sizes
  have hB := planeBound_le hc D hε hε1
  have hHB : HB ≤ cH * (1 + L) := by
    have h1 : (NT + 1) * planeBound c D ε ≤ (NT + 1) * (cP * (1 + L)) :=
      mul_le_mul_of_nonneg_left hB (by linarith)
    have h2 : logb 2 ME + 1 ≤ (logb 2 ME + 1) * (1 + L) := le_mul_of_one_le_right
      (by positivity) (by linarith)
    simp only [HB, cH]
    nlinarith
  have hHB0 : 0 ≤ HB := by
    have := planeBound_nonneg hc D hε hε1
    simp only [HB]
    positivity
  have hW4 := log_div_log_two_le hK4 hεi
  have hWt := log_div_log_two_le hKt hεi
  have hT4c := hT4
  clear_value J0a J0b J1a J1b J0 J1 g
  clear hT4mem hP0mem
  set X := ε⁻¹ with hX
  set Λ := 1 + L with hΛ
  have hΛ1 : 1 ≤ Λ := by rw [hΛ]; linarith
  set W4 := log (K4 * X) / log 2 + 1 with hW4def
  set Wt := log (Kt * X) / log 2 + 1 with hWtdef
  have hW40 : 0 ≤ W4 := by
    rw [hW4def]
    have := Real.log_nonneg (hKX K4 hK4)
    have : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hWt0 : 0 ≤ Wt := by
    rw [hWtdef]
    have := Real.log_nonneg (hKX Kt hKt)
    have : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hB' : planeBound c D ε ≤ cP * Λ := hB
  have hHB' : HB ≤ cH * Λ := hHB
  clear_value X Λ W4 Wt HB
  have hX3 : X ≤ X ^ 3 := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ 3 := pow_le_pow_right₀ hεi (by norm_num)
  have hX23 : X ^ 2 ≤ X ^ 3 := pow_le_pow_right₀ hεi (by norm_num)
  have h1X : 1 ≤ X ^ 3 := one_le_pow₀ hεi
  have hΛ2 : Λ ≤ Λ ^ 2 := by
    calc Λ = Λ ^ 1 := (pow_one Λ).symm
      _ ≤ Λ ^ 2 := pow_le_pow_right₀ hΛ1 (by norm_num)
  have h1 : 1 ≤ X ^ 3 * Λ ^ 2 := one_le_mul_of_one_le_of_one_le h1X (one_le_pow₀ hΛ1)
  have hc0a : (#J0a : ℝ) ≤ cP * (X ^ 3 * Λ ^ 2) := by
    calc (#J0a : ℝ) ≤ cP * Λ := hJ0a.trans hB'
      _ ≤ cP * (X ^ 3 * Λ ^ 2) := by
          gcongr
          calc Λ = 1 * Λ := (one_mul Λ).symm
            _ ≤ X ^ 3 * Λ ^ 2 := mul_le_mul h1X hΛ2 (by linarith) (by linarith)
  have hc0b : (#J0b : ℝ) ≤ Kt * (2 * log Kt + 3) * (X ^ 3 * Λ ^ 2) := by
    have hK : 0 ≤ Kt * Λ * ((2 * log Kt + 3) * Λ) := by positivity
    calc (#J0b : ℝ) ≤ #𝒯0 * Wt := hJ0b
      _ ≤ Kt * X ^ 2 * Λ * ((2 * log Kt + 3) * Λ) := by gcongr
      _ = X ^ 2 * (Kt * Λ * ((2 * log Kt + 3) * Λ)) := by ring
      _ ≤ X ^ 3 * (Kt * Λ * ((2 * log Kt + 3) * Λ)) := mul_le_mul_of_nonneg_right hX23 hK
      _ = Kt * (2 * log Kt + 3) * (X ^ 3 * Λ ^ 2) := by ring
  have hc1a : (#J1a : ℝ) ≤ 10 * cH * (X ^ 3 * Λ ^ 2) := by
    calc (#J1a : ℝ) ≤ #T4 * HB := hJ1a
      _ ≤ 10 * X * (cH * Λ) := by gcongr
      _ = 10 * cH * (X * Λ) := by ring
      _ ≤ 10 * cH * (X ^ 3 * Λ ^ 2) := by gcongr
  have hc1b : (#J1b : ℝ) ≤ K4 * (2 * log K4 + 3) * (X ^ 3 * Λ ^ 2) := by
    calc (#J1b : ℝ) ≤ #𝒯4 * W4 := hJ1b
      _ ≤ K4 * X ^ 3 * Λ * ((2 * log K4 + 3) * Λ) := by gcongr
      _ = K4 * (2 * log K4 + 3) * (X ^ 3 * Λ ^ 2) := by ring
  have hP : 0 ≤ X ^ 3 * Λ ^ 2 := by linarith
  have hsum : (#I : ℝ) ≤ Kc * (X ^ 3 * Λ ^ 2) := by
    rw [hIJ, hJ0s, hJ1s]
    have e : Kc * (X ^ 3 * Λ ^ 2) = cP * (X ^ 3 * Λ ^ 2) +
        Kt * (2 * log Kt + 3) * (X ^ 3 * Λ ^ 2) + 10 * cH * (X ^ 3 * Λ ^ 2) +
        K4 * (2 * log K4 + 3) * (X ^ 3 * Λ ^ 2) := by simp only [Kc]; ring
    rw [e]
    linarith
  calc (#I : ℝ) ≤ Kc * (X ^ 3 * Λ ^ 2) := hsum
    _ ≤ K * (X ^ 3 * Λ ^ 2) := mul_le_mul_of_nonneg_right hKcK hP
    _ = K * X ^ 3 * Λ ^ 2 := by ring

/-- **The count with the interval form, in the shape of (6.1)**: `Real.CFCount α 2`, since
`ε⁻³ (1 + log ε⁻¹)² ≤ ε^{-(2+1)} (1 + log ε⁻¹)³`. -/
theorem cfCount_two {a : ℝ} (hSI : SubspaceInterval α) (hSB : SubspaceBound α a) (hc : 0 < c)
    (hL : LiouvilleQuad α c D) (hα : |α| ≤ 1) : CFCount α 2 := by
  intro A hA
  obtain ⟨K, hK, hcnt⟩ := card_le_of_cfPoints_third hSI hSB hA hc hL hα
  refine ⟨K, hK, fun ε hε hε1 Hs Qs vs I hdbl hpt hthr ↦ (hcnt ε hε hε1 Hs Qs vs I hdbl hpt
    hthr).trans ?_⟩
  have hεi : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
  have hΛ : 1 ≤ 1 + log ε⁻¹ := by have := Real.log_nonneg hεi; linarith
  rw [show (2 : ℝ) + 1 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have : (1 + log ε⁻¹) ^ 2 ≤ (1 + log ε⁻¹) ^ 3 := pow_le_pow_right₀ hΛ (by norm_num)
  have : 0 ≤ K * ε⁻¹ ^ 3 := by positivity
  gcongr

end Real
