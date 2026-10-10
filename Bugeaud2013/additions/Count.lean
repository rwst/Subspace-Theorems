/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.additions.Subspaces

/-!
# The number of points

**The count** (`Real.card_le_of_cfPoints`): a family of points of §3 with exponent `ε`, doubly
exponential heights and `log H ≥ K ε^{-K}` has at most `K ε^{-(a+1)} (1 + log ε⁻¹)³` members, when
the Subspace Theorem holds with `δ^{-a}` subspaces (`Real.SubspaceBound α a`).

* **The first application** (`Real.exists_cover_four`): with `ρ = log Q / log H ∈ [0, 1/2]` in one
  of `⌈8/ε⌉ + 1` cells `[ρ⁻, ρ⁺]`, the forms `L₁, L₂, L₃, X₀` are at most `24 (A + 1)⁴ X^{e}` with
  `e = (-1-ε, 2ρ⁺-1, 1-2ρ⁻, 1)` of sum `≤ -ε/2` (`Real.cell_ineq`), so all points lie in
  `O(ε^{-(a+1)} log² ε⁻¹)` proper subspaces.
* each proper subspace holds `O(log ε⁻¹)` points outside `T₀` (`Real.card_mem_le_of_ne_top`), and
  the points of `T₀` lie in `O(ε^{-a} log² ε⁻¹)` planes (`Real.exists_planes_t0`), each holding
  `O(log ε⁻¹)` points (`Real.card_mem_le_of_finrank_le_two`).
-/

@[expose] public section

open Finset Module

namespace Real

variable {α A ε c : ℝ} {D : ℕ} {v : Fin 4 → ℤ} {H Q : ℝ}

/-! ### The grid -/

/-- The number of `ρ`-cells: `⌈8/ε⌉ + 1`. -/
noncomputable def cells (ε : ℝ) : ℕ := ⌈8 / ε⌉₊ + 1

/-- **The grid.** Every `ρ ∈ [0, 1/2]` lies in a cell `[j/2k, (j+1)/2k]`, `j < cells ε`,
`k = ⌈8/ε⌉`, whose exponents `(-1-ε, 2ρ⁺-1, 1-2ρ⁻, 1)` have maximum `1` and sum `≤ -ε/2`. -/
theorem exists_cell {ε ρ : ℝ} (hε : 0 < ε) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1 / 2) :
    ∃ j < cells ε,
      (j : ℝ) / (2 * ⌈8 / ε⌉₊) ≤ ρ ∧ ρ ≤ ((j : ℝ) + 1) / (2 * ⌈8 / ε⌉₊) ∧
      2 * (((j : ℝ) + 1) / (2 * ⌈8 / ε⌉₊)) - 1 ≤ 1 ∧
      (-1 - ε) + (2 * (((j : ℝ) + 1) / (2 * ⌈8 / ε⌉₊)) - 1) +
        (1 - 2 * ((j : ℝ) / (2 * ⌈8 / ε⌉₊))) + 1 ≤ -(ε / 2) := by
  set k : ℕ := ⌈8 / ε⌉₊ with hkdef
  have hk8 : 8 / ε ≤ (k : ℝ) := Nat.le_ceil _
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hk8
  have h2k : (0 : ℝ) < 2 * k := by positivity
  have hk1 : (1 : ℝ) ≤ k := by
    have : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (by rintro h; simp [h] at hk0)
    exact_mod_cast this
  refine ⟨⌊2 * k * ρ⌋₊, ?_, ?_, ?_, ?_, ?_⟩
  · have : ⌊2 * (k : ℝ) * ρ⌋₊ ≤ k := by
      apply Nat.floor_le_of_le
      nlinarith
    unfold cells; omega
  · rw [div_le_iff₀ h2k]
    have := Nat.floor_le (by positivity : 0 ≤ 2 * (k : ℝ) * ρ)
    linarith
  · rw [le_div_iff₀ h2k]
    have := Nat.lt_floor_add_one (2 * (k : ℝ) * ρ)
    linarith
  · have hj : (⌊2 * (k : ℝ) * ρ⌋₊ : ℝ) ≤ k := by
      have : ⌊2 * (k : ℝ) * ρ⌋₊ ≤ k := Nat.floor_le_of_le (by nlinarith)
      exact_mod_cast this
    have : ((⌊2 * (k : ℝ) * ρ⌋₊ : ℝ) + 1) / (2 * k) ≤ 1 := by
      rw [div_le_one h2k]; nlinarith
    linarith
  · have hinv : 1 / (k : ℝ) ≤ ε / 8 := by
      rw [div_le_iff₀ hk0]
      have := (div_le_iff₀ hε).1 hk8
      nlinarith
    have e1 : (-1 - ε) + (2 * (((⌊2 * (k : ℝ) * ρ⌋₊ : ℝ) + 1) / (2 * k)) - 1) +
        (1 - 2 * ((⌊2 * (k : ℝ) * ρ⌋₊ : ℝ) / (2 * k))) + 1 = -ε + 1 / k := by
      field_simp; ring
    rw [e1]; linarith

theorem cells_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : (cells ε : ℝ) ≤ 10 * ε⁻¹ := by
  have h1 := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 8 / ε)
  have h2 : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
  have h3 : 8 / ε = 8 * ε⁻¹ := div_eq_mul_inv _ _
  unfold cells
  push_cast
  linarith

/-! ### The first application -/

theorem one_le_iSup_abs_of_cfPoint (hp : CFPoint α A ε v H Q) : 1 ≤ ⨆ k, |(v k : ℝ)| :=
  one_le_iSup_abs fun h ↦ hp.v0_ne_zero (by simp [h])

/-- **The inequalities of one cell**: with `ρ = log Q / log H ∈ [ρ⁻, ρ⁺]`, the forms
`L₁, L₂, L₃, X₀` are at most `24 (A + 1)⁴ X^{e}`, `e = (-1-ε, 2ρ⁺-1, 1-2ρ⁻, 1)`. -/
theorem cell_ineq (hA : 1 ≤ A) (hε : 0 ≤ ε) (hp : CFPoint α A ε v H Q) (hlogH : 0 < log H)
    {r₀ r₁ : ℝ} (hr₀ : 0 ≤ r₀) (h0 : r₀ ≤ log Q / log H) (h1 : log Q / log H ≤ r₁)
    (i : Fin 4) :
    |∑ k, quadVal α (formCoef i k) * v k| ≤
      24 * (A + 1) ^ 4 * (⨆ k, |(v k : ℝ)|) ^ (![-1 - ε, 2 * r₁ - 1, 1 - 2 * r₀, 1] : Fin 4 → ℝ) i
    := by
  have hH0 := hp.H_pos
  have hQ1 := hp.one_le_Q
  set X := ⨆ k, |(v k : ℝ)|
  have hX1 : 1 ≤ X := one_le_iSup_abs_of_cfPoint hp
  have hX0 : 0 < X := by linarith
  have hXH : X ≤ H := ciSup_le hp.abs_le
  have hHX : H ≤ (A + 1) ^ 4 * X := hp.head.trans (by gcongr; exact abs_le_iSup_abs v 0)
  have hA4 : (1 : ℝ) ≤ (A + 1) ^ 4 := one_le_pow₀ (by linarith)
  set ρ := log Q / log H
  have hQρ : Q = H ^ ρ := by
    rw [Real.rpow_def_of_pos hH0, show log H * ρ = log Q by
      simp only [ρ]; field_simp, Real.exp_log (by linarith)]
  have hρ2 : 2 * ρ ≤ 1 := by
    have := Real.log_le_log (by positivity) hp.sq_le
    rw [Real.log_pow] at this
    simp only [ρ]
    rw [mul_div_assoc', div_le_one hlogH]
    push_cast at this; linarith
  have hQ2 : Q ^ 2 = H ^ (2 * ρ) := by
    rw [hQρ, ← Real.rpow_natCast, ← Real.rpow_mul hH0.le]; ring_nf
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    have : ∑ k, quadVal α (formCoef 0 k) * v k = formL1 α v := formVal_zero α v
    rw [this]
    have h1 : H ^ (-1 - ε) ≤ X ^ (-1 - ε) := Real.rpow_le_rpow_of_nonpos hX0 hXH (by linarith)
    have h2 : 0 ≤ X ^ (-1 - ε) := by positivity
    calc |formL1 α v| ≤ 24 * H ^ (-1 - ε) := hp.L1_le
      _ ≤ 24 * X ^ (-1 - ε) := by gcongr
      _ ≤ 24 * (A + 1) ^ 4 * X ^ (-1 - ε) := by nlinarith
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    have : ∑ k, quadVal α (formCoef 1 k) * v k = formL2 α v := formVal_one α v
    rw [this]
    have e1 : 2 * Q ^ 2 / H = 2 * H ^ (2 * ρ - 1) := by
      rw [hQ2, Real.rpow_sub_one hH0.ne']; ring
    have h1 : H ^ (2 * ρ - 1) ≤ X ^ (2 * ρ - 1) :=
      Real.rpow_le_rpow_of_nonpos hX0 hXH (by linarith)
    have h2 : X ^ (2 * ρ - 1) ≤ X ^ (2 * r₁ - 1) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    have h3 : 0 ≤ X ^ (2 * r₁ - 1) := by positivity
    calc |formL2 α v| ≤ 2 * Q ^ 2 / H := hp.L2_le
      _ = 2 * H ^ (2 * ρ - 1) := e1
      _ ≤ 2 * X ^ (2 * r₁ - 1) := by linarith
      _ ≤ 24 * (A + 1) ^ 4 * X ^ (2 * r₁ - 1) := by nlinarith
  · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    have : ∑ k, quadVal α (formCoef 2 k) * v k = formL3 α v := formVal_two α v
    rw [this]
    have hρ0 : 0 ≤ ρ := div_nonneg (Real.log_nonneg hQ1) hlogH.le
    have e1 : 2 * H / Q ^ 2 = 2 * H ^ (1 - 2 * ρ) := by
      rw [hQ2, Real.rpow_sub hH0, Real.rpow_one]; ring
    have h1 : H ^ (1 - 2 * ρ) ≤ ((A + 1) ^ 4 * X) ^ (1 - 2 * ρ) :=
      Real.rpow_le_rpow hH0.le hHX (by linarith)
    have h2 : ((A + 1) ^ 4 * X) ^ (1 - 2 * ρ) =
        ((A + 1) ^ 4) ^ (1 - 2 * ρ) * X ^ (1 - 2 * ρ) := Real.mul_rpow (by positivity) hX0.le
    have h3 : ((A + 1) ^ 4 : ℝ) ^ (1 - 2 * ρ) ≤ (A + 1) ^ 4 := by
      calc ((A + 1) ^ 4 : ℝ) ^ (1 - 2 * ρ) ≤ ((A + 1) ^ 4 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hA4 (by linarith)
        _ = (A + 1) ^ 4 := Real.rpow_one _
    have h4 : X ^ (1 - 2 * ρ) ≤ X ^ (1 - 2 * r₀) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    have h5 : 0 ≤ X ^ (1 - 2 * ρ) := by positivity
    have h6 : 0 ≤ ((A + 1) ^ 4 : ℝ) ^ (1 - 2 * ρ) := by positivity
    calc |formL3 α v| ≤ 2 * H / Q ^ 2 := hp.L3_le
      _ = 2 * H ^ (1 - 2 * ρ) := e1
      _ ≤ 2 * (((A + 1) ^ 4) ^ (1 - 2 * ρ) * X ^ (1 - 2 * ρ)) := by rw [← h2]; linarith
      _ ≤ 2 * ((A + 1) ^ 4 * X ^ (1 - 2 * r₀)) := by gcongr
      _ ≤ 24 * (A + 1) ^ 4 * X ^ (1 - 2 * r₀) := by
          have : 0 ≤ (A + 1) ^ 4 * X ^ (1 - 2 * r₀) := by positivity
          nlinarith
  · simp only [Fin.reduceFinMk, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons,
      Real.rpow_one]
    have : ∑ k, quadVal α (formCoef 3 k) * v k = v 0 := formVal_three α v
    rw [this]
    have := abs_le_iSup_abs v 0
    nlinarith


/-- The exponents of the cell `j`, `k = ⌈8/ε⌉`. -/
noncomputable def cellExp (ε : ℝ) (j : ℕ) : Fin 4 → ℝ :=
  ![-1 - ε, 2 * (((j : ℝ) + 1) / (2 * ⌈8 / ε⌉₊)) - 1, 1 - 2 * ((j : ℝ) / (2 * ⌈8 / ε⌉₊)), 1]

theorem cellExp_le_one {ε : ℝ} (hε : 0 < ε) {j : ℕ} (hj : j < cells ε) (i : Fin 4) :
    cellExp ε j i ≤ 1 := by
  set k : ℕ := ⌈8 / ε⌉₊
  have hk8 : 8 / ε ≤ (k : ℝ) := Nat.le_ceil _
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hk8
  have hk1 : (1 : ℝ) ≤ k := by
    have : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (by rintro h; simp [h] at hk0)
    exact_mod_cast this
  have hjk : (j : ℝ) ≤ k := by
    have : j ≤ k := by unfold cells at hj; omega
    exact_mod_cast this
  fin_cases i
  · simp only [cellExp, Fin.zero_eta, Matrix.cons_val_zero]; linarith
  · simp only [cellExp, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    have : ((j : ℝ) + 1) / (2 * k) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  · simp only [cellExp, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    have : 0 ≤ (j : ℝ) / (2 * k) := by positivity
    linarith
  · simp [cellExp]

theorem sum_cellExp_le {ε : ℝ} (hε : 0 < ε) (j : ℕ) : ∑ i, cellExp ε j i ≤ -(ε / 2) := by
  set k : ℕ := ⌈8 / ε⌉₊
  have hk8 : 8 / ε ≤ (k : ℝ) := Nat.le_ceil _
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hk8
  have hinv : 1 / (k : ℝ) ≤ ε / 8 := by
    rw [div_le_iff₀ hk0]
    have := (div_le_iff₀ hε).1 hk8
    nlinarith
  have e1 : ∑ i, cellExp ε j i = -ε + 1 / k := by
    simp only [cellExp, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    field_simp; ring
  rw [e1]; linarith

/-- **The first application**: the points with `log H ≥ K ε^{-K}` lie in at most
`cells ε · K (ε/2)^{-a} (1 + log (2/ε))²` proper subspaces of `ℚ⁴`. -/
theorem exists_cover_four {a : ℝ} (hSB : SubspaceBound α a) (hA : 1 ≤ A) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ T : Finset (Submodule ℚ (Fin 4 → ℚ)),
        (#T : ℝ) ≤ cells ε * (K * (ε / 2)⁻¹ ^ a * (1 + log (ε / 2)⁻¹) ^ 2) ∧
        (∀ U ∈ T, U ≠ ⊤) ∧
        ∀ (v : Fin 4 → ℤ) (H Q : ℝ), CFPoint α A ε v H Q → 1 ≤ log H →
          K * ε⁻¹ ^ K ≤ log H → ∃ U ∈ T, ptQ v ∈ U := by
  classical
  obtain ⟨K₄, hK₄, h4⟩ := hSB 4 (by norm_num) le_rfl
  have hA4 : (1 : ℝ) ≤ (A + 1) ^ 4 := one_le_pow₀ (by linarith)
  set C : ℝ := 24 * (A + 1) ^ 4
  have hC1 : 1 ≤ C := by simp only [C]; linarith
  have hlC : 0 ≤ log C := Real.log_nonneg hC1
  have hlA : 0 ≤ log (A + 1) := Real.log_nonneg (by linarith)
  set κ := K₄ * 2 ^ K₄ * (1 + log C) + 4 * log (A + 1)
  set K := max K₄ κ
  have hKK : K₄ ≤ K := le_max_left _ _
  refine ⟨K, hK₄.trans_le hKK, fun ε hε hε1 ↦ ?_⟩
  have hεi : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
  have hdet : (1 : ℝ) ≤ |(Matrix.of fun i k ↦ quadVal α (formCoef i k)).det| := by
    rw [det_formCoef, abs_neg, abs_one]
  have hcell : ∀ j, j < cells ε → ∃ T : Finset (Submodule ℚ (Fin 4 → ℚ)),
      (#T : ℝ) ≤ K₄ * (ε / 2)⁻¹ ^ a * (1 + log (ε / 2)⁻¹) ^ 2 ∧ (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x : Fin 4 → ℤ, x ≠ 0 →
        (∀ i, |∑ k, quadVal α (formCoef i k) * x k| ≤ C * (⨆ k, |(x k : ℝ)|) ^ cellExp ε j i) →
        K₄ * (ε / 2)⁻¹ ^ K₄ * (1 + log 1 + log C + log 1⁻¹) ≤ log (⨆ k, |(x k : ℝ)|) →
        ∃ U ∈ T, (fun k ↦ (x k : ℚ)) ∈ U := fun j hj ↦
    h4 formCoef 1 le_rfl (fun i k m ↦ by exact_mod_cast abs_formCoef_le i k m) 1 one_pos le_rfl
      hdet C hC1 (cellExp ε j) (ε / 2) (by positivity) (by linarith)
      (cellExp_le_one hε hj) ⟨3, rfl⟩ (sum_cellExp_le hε j)
  choose! T hT htop hmem using hcell
  refine ⟨(range (cells ε)).biUnion T, ?_, ?_, ?_⟩
  · refine (Nat.cast_le.2 card_biUnion_le).trans ?_
    push_cast
    calc ∑ j ∈ range (cells ε), (#(T j) : ℝ)
        ≤ ∑ _j ∈ range (cells ε), K₄ * (ε / 2)⁻¹ ^ a * (1 + log (ε / 2)⁻¹) ^ 2 :=
          Finset.sum_le_sum fun j hj ↦ hT j (Finset.mem_range.1 hj)
      _ = cells ε * (K₄ * (ε / 2)⁻¹ ^ a * (1 + log (ε / 2)⁻¹) ^ 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ cells ε * (K * (ε / 2)⁻¹ ^ a * (1 + log (ε / 2)⁻¹) ^ 2) := by gcongr
  · intro U hU
    obtain ⟨j, hj, hU⟩ := Finset.mem_biUnion.1 hU
    exact htop j (Finset.mem_range.1 hj) U hU
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
  set X := ⨆ k, |(v k : ℝ)|
  have hX1 : 1 ≤ X := one_le_iSup_abs_of_cfPoint hp
  have hHX : H ≤ (A + 1) ^ 4 * X := hp.head.trans (by gcongr; exact abs_le_iSup_abs v 0)
  have hthr : K₄ * (ε / 2)⁻¹ ^ K₄ * (1 + log 1 + log C + log 1⁻¹) ≤ log X := by
    rw [inv_one, Real.log_one, add_zero, add_zero]
    have hYlog : log H - 4 * log (A + 1) ≤ log X := by
      have := Real.log_le_log hp.H_pos hHX
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at this
      push_cast at this
      linarith
    have he2 : (ε / 2)⁻¹ ^ K₄ = 2 ^ K₄ * ε⁻¹ ^ K₄ := by
      rw [inv_div, div_eq_mul_inv, Real.mul_rpow (by norm_num) (by positivity)]
    have hp1 : 1 ≤ ε⁻¹ ^ K₄ := Real.one_le_rpow hεi hK₄.le
    have hp2 : ε⁻¹ ^ K₄ ≤ ε⁻¹ ^ K := Real.rpow_le_rpow_of_exponent_le hεi hKK
    have hκK : κ ≤ K := le_max_right _ _
    have h3 : κ * ε⁻¹ ^ K₄ ≤ K * ε⁻¹ ^ K :=
      mul_le_mul hκK hp2 (by positivity) (hK₄.le.trans hKK)
    have h5 : 4 * log (A + 1) ≤ 4 * log (A + 1) * ε⁻¹ ^ K₄ :=
      le_mul_of_one_le_right (by positivity) hp1
    rw [he2]
    have : K₄ * (2 ^ K₄ * ε⁻¹ ^ K₄) * (1 + log C) + 4 * log (A + 1) * ε⁻¹ ^ K₄ =
        κ * ε⁻¹ ^ K₄ := by simp only [κ]; ring
    linarith
  obtain ⟨U, hU, hvU⟩ := hmem j hj v hv0
    (fun i ↦ cell_ineq hA hε.le hp hlogH (by positivity) h0 h1 i) hthr
  exact ⟨U, Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj, hU⟩, hvU⟩

/-! ### The count -/

theorem planeBound_le {c : ℝ} (hc : 0 < c) (D : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    planeBound c D ε ≤ (4 * log (log (twoConst c D) + 4 * D + 4) + 6) * (1 + log ε⁻¹) := by
  set R := log (twoConst c D) + 4 * D + 4
  have hR : 4 ≤ R := by
    have := Real.log_nonneg (one_le_twoConst hc D)
    have : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    simp only [R]; linarith
  have hlR : 0 ≤ log R := Real.log_nonneg (by linarith)
  have hL : 0 ≤ log ε⁻¹ := Real.log_nonneg ((one_le_inv₀ hε).2 hε1)
  have hl2 := Real.log_two_gt_d9
  have hlog : log (planeRatio c D ε) = log R + log ε⁻¹ := by
    rw [planeRatio, div_eq_mul_inv, Real.log_mul (by linarith) (by positivity)]
  have hlogb : logb 2 (planeRatio c D ε) ≤ 2 * (log R + log ε⁻¹) := by
    rw [Real.logb, hlog, div_le_iff₀ (by linarith)]
    nlinarith
  rw [planeBound]
  nlinarith

variable {a : ℝ}

/-- **The count of the points.** -/
theorem card_le_of_cfPoints (hSB : SubspaceBound α a) (hA : 1 ≤ A) (hc : 0 < c)
    (hL : LiouvilleQuad α c D) (hα : |α| ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (Hs Qs : ℕ → ℝ) (vs : ℕ → Fin 4 → ℤ)
      (I : Finset ℕ), Doubling Hs → (∀ k ∈ I, CFPoint α A ε (vs k) (Hs k) (Qs k)) →
      (∀ k ∈ I, K * ε⁻¹ ^ K ≤ log (Hs k)) →
      (#I : ℝ) ≤ K * ε⁻¹ ^ (a + 1) * (1 + log ε⁻¹) ^ 3 := by
  classical
  obtain ⟨K4, hK4, hcov4⟩ := exists_cover_four hSB hA
  obtain ⟨Kt, hKt, hcovt⟩ := exists_planes_t0 hSB hA
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
  have hl2 : 0 ≤ log 2 := Real.log_nonneg (by norm_num)
  set Kc := 10 * K4 * 2 ^ a * (1 + log 2) ^ 2 * cH + Kt * cP
  set K := max 1 (max (max K4 Kt) Kc)
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK4K : K4 ≤ K := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hKtK : Kt ≤ K := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hKcK : Kc ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K, by linarith, fun ε hε hε1 Hs Qs vs I hdbl hpt hthr ↦ ?_⟩
  have hεi : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
  set L := log ε⁻¹
  have hL0 : 0 ≤ L := Real.log_nonneg hεi
  -- the thresholds
  have hthr' (K' : ℝ) (hK' : K' ≤ K) (hK'0 : 0 ≤ K') (k : ℕ) (hk : k ∈ I) :
      K' * ε⁻¹ ^ K' ≤ log (Hs k) :=
    (mul_le_mul hK' (Real.rpow_le_rpow_of_exponent_le hεi hK') (by positivity)
      (by linarith)).trans (hthr k hk)
  -- the covers
  obtain ⟨T4, hT4, hT4top, hT4mem⟩ := hcov4 ε hε hε1
  obtain ⟨T0, hT0, hT0r, hT0mem⟩ := hcovt ε hε hε1
  set B := planeBound c D ε
  have hB0 := planeBound_nonneg hc D hε hε1
  have hB := planeBound_le hc D hε hε1
  set HB := (NT + 1) * B + logb 2 ME + 1
  have hHB : HB ≤ cH * (1 + L) := by
    have h1 : (NT + 1) * B ≤ (NT + 1) * (cP * (1 + L)) :=
      mul_le_mul_of_nonneg_left hB (by linarith)
    have h2 : logb 2 ME + 1 ≤ (logb 2 ME + 1) * (1 + L) := le_mul_of_one_le_right
      (by positivity) (by linarith)
    simp only [HB, cH]
    nlinarith
  have hsplit : I ⊆ T0.biUnion (fun U ↦ {k ∈ I | ptQ (vs k) ∈ U}) ∪
      T4.biUnion fun S ↦ {k ∈ I | ptQ (vs k) ∈ S ∧ vs k 1 ≠ vs k 2} := by
    intro k hk
    have hp := hpt k hk
    by_cases h12 : vs k 1 = vs k 2
    · obtain ⟨U, hU, hkU⟩ := hT0mem (vs k) (Hs k) (Qs k) hp h12
        (hthr' Kt hKtK hKt.le k hk)
      exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨U, hU, Finset.mem_filter.2
        ⟨hk, hkU⟩⟩)
    · obtain ⟨S, hS, hkS⟩ := hT4mem (vs k) (Hs k) (Qs k) hp (hdbl.one_le_log k)
        (hthr' K4 hK4K hK4.le k hk)
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨S, hS, Finset.mem_filter.2
        ⟨hk, hkS, h12⟩⟩)
  have hc0 : (#(T0.biUnion fun U ↦ {k ∈ I | ptQ (vs k) ∈ U}) : ℝ) ≤ #T0 * B := by
    refine (Nat.cast_le.2 card_biUnion_le).trans ?_
    push_cast
    calc ∑ U ∈ T0, (#{k ∈ I | ptQ (vs k) ∈ U} : ℝ) ≤ ∑ _U ∈ T0, B :=
          Finset.sum_le_sum fun U hU ↦
            card_mem_le_of_finrank_le_two hc hL hα hε hε1 hdbl I hpt U (hT0r U hU)
      _ = #T0 * B := by rw [Finset.sum_const, nsmul_eq_mul]
  have hc4 : (#(T4.biUnion fun S ↦ {k ∈ I | ptQ (vs k) ∈ S ∧ vs k 1 ≠ vs k 2}) : ℝ) ≤
      #T4 * HB := by
    refine (Nat.cast_le.2 card_biUnion_le).trans ?_
    push_cast
    calc ∑ S ∈ T4, (#{k ∈ I | ptQ (vs k) ∈ S ∧ vs k 1 ≠ vs k 2} : ℝ) ≤ ∑ _S ∈ T4, HB :=
          Finset.sum_le_sum fun S hS ↦
            card_mem_le_of_ne_top hc hL hα hε hε1 hdbl I hpt hNT hcovE S (hT4top S hS)
      _ = #T4 * HB := by rw [Finset.sum_const, nsmul_eq_mul]
  -- the sizes of the covers
  have hpa : ε⁻¹ ^ a ≤ ε⁻¹ ^ (a + 1) := Real.rpow_le_rpow_of_exponent_le hεi (by linarith)
  have hpa1 : ε⁻¹ ^ (a + 1) = ε⁻¹ ^ a * ε⁻¹ := by
    rw [Real.rpow_add (by positivity), Real.rpow_one]
  have hT4' : (#T4 : ℝ) ≤ 10 * K4 * 2 ^ a * (1 + log 2) ^ 2 * (ε⁻¹ ^ (a + 1) * (1 + L) ^ 2) := by
    refine hT4.trans ?_
    have he2 : (ε / 2)⁻¹ ^ a = 2 ^ a * ε⁻¹ ^ a := by
      rw [inv_div, div_eq_mul_inv, Real.mul_rpow (by norm_num) (by positivity)]
    have hl : 1 + log (ε / 2)⁻¹ ≤ (1 + log 2) * (1 + L) := by
      rw [inv_div, div_eq_mul_inv, Real.log_mul (by norm_num) (by positivity)]
      nlinarith
    have hl' : (1 + log (ε / 2)⁻¹) ^ 2 ≤ ((1 + log 2) * (1 + L)) ^ 2 := by
      have : 0 ≤ 1 + log (ε / 2)⁻¹ := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ (ε / 2)⁻¹ by
          rw [inv_div, le_div_iff₀ hε]; linarith)
        linarith
      exact pow_le_pow_left₀ this hl 2
    have hcells := cells_le hε hε1
    calc (cells ε : ℝ) * (K4 * (ε / 2)⁻¹ ^ a * (1 + log (ε / 2)⁻¹) ^ 2)
        ≤ (10 * ε⁻¹) * (K4 * (2 ^ a * ε⁻¹ ^ a) * ((1 + log 2) * (1 + L)) ^ 2) := by
          rw [he2]
          gcongr
      _ = 10 * K4 * 2 ^ a * (1 + log 2) ^ 2 * (ε⁻¹ ^ (a + 1) * (1 + L) ^ 2) := by
          rw [hpa1]; ring
  have hT0' : (#T0 : ℝ) ≤ Kt * (ε⁻¹ ^ (a + 1) * (1 + L) ^ 2) := by
    refine hT0.trans ?_
    rw [mul_assoc]
    gcongr
  -- the total
  have hE : 0 ≤ ε⁻¹ ^ (a + 1) * (1 + L) ^ 2 := by positivity
  calc (#I : ℝ)
      ≤ #(T0.biUnion (fun U ↦ {k ∈ I | ptQ (vs k) ∈ U}) ∪
          T4.biUnion fun S ↦ {k ∈ I | ptQ (vs k) ∈ S ∧ vs k 1 ≠ vs k 2}) :=
        Nat.cast_le.2 (card_le_card hsplit)
    _ ≤ #(T0.biUnion fun U ↦ {k ∈ I | ptQ (vs k) ∈ U}) +
          #(T4.biUnion fun S ↦ {k ∈ I | ptQ (vs k) ∈ S ∧ vs k 1 ≠ vs k 2}) := by
        exact_mod_cast card_union_le _ _
    _ ≤ #T0 * B + #T4 * HB := add_le_add hc0 hc4
    _ ≤ Kt * (ε⁻¹ ^ (a + 1) * (1 + L) ^ 2) * (cP * (1 + L)) +
          10 * K4 * 2 ^ a * (1 + log 2) ^ 2 * (ε⁻¹ ^ (a + 1) * (1 + L) ^ 2) * (cH * (1 + L)) := by
        gcongr
    _ = Kc * ε⁻¹ ^ (a + 1) * (1 + L) ^ 3 := by simp only [Kc]; ring
    _ ≤ K * ε⁻¹ ^ (a + 1) * (1 + L) ^ 3 := by gcongr

end Real
