/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Additions.Forms
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The two Subspace applications in three variables

* **On a hyperplane `z^⊥`** with `Λ = z₀ + (z₁ + z₂) α + z₃ α² ≠ 0`
  (`Real.exists_planes_of_lamCoef_ne_zero`): the points with `log H ≥ K (1 + log |z|)` satisfy
  Bugeaud's Claim in the form `Q ≤ |z|^{O(1)}`, hence `Q² ≤ H^{1/4}`, and the projected forms
  `z_j L₁, z_j L₂, z_j L₃` with exponents `(-1, -3/4, 1)`. The Subspace Theorem at `δ = 3/4` puts
  them in `O(1)` planes.
* **On `T₀ = {X₁ = X₂}`** (`Real.exists_planes_t0`): the forms `L₁, L₂, L₄` in `(X₀, X₁, X₃)`
  with exponents `(-1-ε, 0, 1)`; the Subspace Theorem at `δ = ε` gives `O(ε^{-a} log² ε⁻¹)` planes.

The subspaces of `ℚ³` are pulled back to planes of `ℚ⁴` (`Real.finrank_inf_comap_le_two`).
Finally, a proper subspace of `ℚ⁴` holds `O(log ε⁻¹)` points outside `T₀`
(`Real.card_mem_le_of_ne_top`): the first three independent ones span it, their cross product
`z` has `Λ ≠ 0` (they are not in `T₀`) and `|z| ≤ 6 H_c³`, so all but `O(1)` later points are
large enough for the first application.
-/

@[expose] public section

open Finset Module

namespace Real

/-- A subspace of `ℚ³` pulled back to `W ⊆ ℚ⁴`, on which the projection is injective, has
dimension at most `2`. -/
theorem finrank_inf_comap_le_two {p : (Fin 4 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ)}
    {W : Submodule ℚ (Fin 4 → ℚ)} (hp : ∀ x ∈ W, p x = 0 → x = 0)
    {U : Submodule ℚ (Fin 3 → ℚ)} (hU : U ≠ ⊤) : finrank ℚ ↥(W ⊓ U.comap p) ≤ 2 := by
  set V := W ⊓ U.comap p
  let f : V →ₗ[ℚ] U := (p.comp V.subtype).codRestrict U fun x ↦ (Submodule.mem_inf.1 x.2).2
  have hf : Function.Injective f := by
    intro x y hxy
    have hpxy : p x = p y := congrArg Subtype.val hxy
    have h := hp ((x : Fin 4 → ℚ) - y)
      (W.sub_mem (Submodule.mem_inf.1 x.2).1 (Submodule.mem_inf.1 y.2).1)
      (by rw [map_sub, hpxy, sub_self])
    exact Subtype.ext (sub_eq_zero.1 h)
  have h1 := LinearMap.finrank_le_finrank_of_injective hf
  have h2 := Submodule.finrank_lt hU
  rw [Module.finrank_fin_fun] at h2
  omega

/-- `1 ≤ ⨆ |y_k|` for a nonzero integer point. -/
theorem one_le_iSup_abs {n : ℕ} {y : Fin n → ℤ} (hy : y ≠ 0) : 1 ≤ ⨆ k, |(y k : ℝ)| := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hy
  have : (1 : ℤ) ≤ |y k| := Int.one_le_abs hk
  exact Finite.le_ciSup_of_le k (by exact_mod_cast this)

theorem abs_le_iSup_abs {n : ℕ} (y : Fin n → ℤ) (k : Fin n) : |(y k : ℝ)| ≤ ⨆ k, |(y k : ℝ)| :=
  Finite.le_ciSup_of_le k le_rfl

variable {α A ε c : ℝ} {D : ℕ}

/-! ### On a hyperplane -/

/-- The orthogonal of `z` in `ℚ⁴`. -/
noncomputable def perpZ (z : Fin 4 → ℤ) : Submodule ℚ (Fin 4 → ℚ) :=
  LinearMap.ker (Module.Dual.sumForm fun i ↦ (z i : ℚ))

theorem mem_perpZ {z : Fin 4 → ℤ} {x : Fin 4 → ℚ} : x ∈ perpZ z ↔ ∑ i, (z i : ℚ) * x i = 0 := by
  simp [perpZ, Module.Dual.sumForm_apply]

theorem ptQ_mem_perpZ {z v : Fin 4 → ℤ} (h : ∑ i, z i * v i = 0) : ptQ v ∈ perpZ z := by
  rw [mem_perpZ]
  simp only [ptQ]
  exact_mod_cast h

/-- Dropping the coordinate `j` is injective on `z^⊥` when `z_j ≠ 0`. -/
theorem eq_zero_of_mem_perpZ {z : Fin 4 → ℤ} {j : Fin 4} (hj : z j ≠ 0) {x : Fin 4 → ℚ}
    (hx : x ∈ perpZ z) (h0 : LinearMap.funLeft ℚ ℚ j.succAbove x = 0) : x = 0 := by
  rw [mem_perpZ, Fin.sum_univ_succAbove _ j] at hx
  have hs (k : Fin 3) : x (j.succAbove k) = 0 := by
    have := congrFun h0 k
    rwa [LinearMap.funLeft_apply] at this
  simp only [hs, mul_zero, Finset.sum_const_zero, add_zero] at hx
  have hxj : x j = 0 := by
    rcases mul_eq_zero.1 hx with h | h
    · exact absurd (by exact_mod_cast h) hj
    · exact h
  funext i
  rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨k, rfl⟩
  · exact hxj
  · exact hs k

section Hyper

variable {z : Fin 4 → ℤ} {Z : ℝ} {j : Fin 4} {v : Fin 4 → ℤ} {H Q : ℝ}

/-- `z_j v_j = -∑_{k} z_{j.succAbove k} v_{j.succAbove k}` for `v ⊥ z`. -/
theorem mul_eq_neg_sum_succAbove (hzv : ∑ i, z i * v i = 0) :
    (z j : ℝ) * v j = -∑ k, (z (j.succAbove k) : ℝ) * v (j.succAbove k) := by
  have h := Fin.sum_univ_succAbove (fun i ↦ (z i : ℝ) * v i) j
  have h0 : ∑ i, (z i : ℝ) * v i = 0 := by exact_mod_cast hzv
  rw [h0] at h
  linarith

/-- **The projected point**: `y = (v_{j.succAbove k})_k` is not `0`, and its height `Y` satisfies
`1 ≤ Y ≤ H ≤ 3 Z (A + 1)⁴ Y`. -/
theorem hyp_point (hj : z j ≠ 0) (hz : ∀ i, |(z i : ℝ)| ≤ Z) (hp : CFPoint α A ε v H Q)
    (hzv : ∑ i, z i * v i = 0) :
    (fun k ↦ v (j.succAbove k)) ≠ 0 ∧ 1 ≤ ⨆ k, |(v (j.succAbove k) : ℝ)| ∧
      (⨆ k, |(v (j.succAbove k) : ℝ)|) ≤ H ∧
      H ≤ 3 * Z * (A + 1) ^ 4 * ⨆ k, |(v (j.succAbove k) : ℝ)| := by
  set y : Fin 3 → ℤ := fun k ↦ v (j.succAbove k)
  have hzv' := mul_eq_neg_sum_succAbove (j := j) hzv
  have hzj1 : (1 : ℝ) ≤ |(z j : ℝ)| := by
    have : (1 : ℤ) ≤ |z j| := Int.one_le_abs hj
    exact_mod_cast this
  have hy0 : y ≠ 0 := by
    intro h
    have hyk (k : Fin 3) : (v (j.succAbove k) : ℝ) = 0 := by
      have := congrFun h k
      simp only [y, Pi.zero_apply] at this
      exact_mod_cast this
    simp only [hyk, mul_zero, Finset.sum_const_zero, neg_zero] at hzv'
    have hvj : (v j : ℝ) = 0 := by
      rcases mul_eq_zero.1 hzv' with h1 | h1
      · exact absurd (by exact_mod_cast h1) hj
      · exact h1
    have hv : v = 0 := by
      funext i
      rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨k, rfl⟩
      · exact_mod_cast hvj
      · exact_mod_cast hyk k
    exact hp.v0_ne_zero (by simp [hv])
  set Y := ⨆ k, |(y k : ℝ)|
  have hY1 : 1 ≤ Y := one_le_iSup_abs hy0
  have hZ1 : 1 ≤ Z := hzj1.trans (hz j)
  have hv3 : ∀ i, |(v i : ℝ)| ≤ 3 * Z * Y := by
    intro i
    rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨k, rfl⟩
    · have h1 : |∑ k, (z (i.succAbove k) : ℝ) * y k| ≤ 3 * Z * Y := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ k, |(z (i.succAbove k) : ℝ) * y k| ≤ ∑ _k : Fin 3, Z * Y :=
              Finset.sum_le_sum fun k _ ↦ by
                rw [abs_mul]
                exact mul_le_mul (hz _) (abs_le_iSup_abs y k) (abs_nonneg _) (by linarith)
          _ = 3 * Z * Y := by simp; ring
      have h2 : |(z i : ℝ)| * |(v i : ℝ)| ≤ 3 * Z * Y := by
        rw [← abs_mul, hzv', abs_neg]; exact h1
      have h3 : |(v i : ℝ)| ≤ |(z i : ℝ)| * |(v i : ℝ)| :=
        le_mul_of_one_le_left (abs_nonneg _) hzj1
      linarith
    · have h1 := abs_le_iSup_abs y k
      have h2 : Y ≤ 3 * Z * Y := by nlinarith
      exact h1.trans h2
  refine ⟨hy0, hY1, ciSup_le fun k ↦ hp.abs_le _, ?_⟩
  have h1 := hp.head
  have h2 := hv3 0
  calc H ≤ (A + 1) ^ 4 * |(v 0 : ℝ)| := h1
    _ ≤ (A + 1) ^ 4 * (3 * Z * Y) := by gcongr
    _ = 3 * Z * (A + 1) ^ 4 * Y := by ring

/-- **Bugeaud's Claim on `z^⊥`**: `Q ≤ 48 (A + 1)² Z (2 Z)^D / c`. -/
theorem hyp_Q_le (hc : 0 < c) (hZ : 1 ≤ Z) (hz : ∀ i, |(z i : ℝ)| ≤ Z)
    (hΛL : c ≤ |quadVal α (lamCoef z)| * (2 * Z) ^ D) (hp : CFPoint α A ε v H Q)
    (hzv : ∑ i, z i * v i = 0) : Q ≤ 48 * (A + 1) ^ 2 * Z * (2 * Z) ^ D / c := by
  have h := hp.claim (fun i ↦ (z i : ℝ)) (by exact_mod_cast hzv)
  have hΛeq : (z 0 : ℝ) + ((z 1 : ℝ) + z 2) * α + z 3 * α ^ 2 = quadVal α (lamCoef z) := by
    simp only [quadVal, lamCoef, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  rw [hΛeq] at h
  have hsum : ∑ i, |(z i : ℝ)| ≤ 4 * Z := by
    calc ∑ i, |(z i : ℝ)| ≤ ∑ _i : Fin 4, Z := Finset.sum_le_sum fun i _ ↦ hz i
      _ = 4 * Z := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hA2 : 0 ≤ 12 * (A + 1) ^ 2 := by positivity
  have h1 : Q * |quadVal α (lamCoef z)| ≤ 48 * (A + 1) ^ 2 * Z :=
    h.trans (by nlinarith [mul_le_mul_of_nonneg_left hsum hA2])
  have hQ0 : 0 ≤ Q := by linarith [hp.one_le_Q]
  have h2Z : (0 : ℝ) ≤ (2 * Z) ^ D := by positivity
  rw [le_div_iff₀ hc]
  calc Q * c ≤ Q * (|quadVal α (lamCoef z)| * (2 * Z) ^ D) := mul_le_mul_of_nonneg_left hΛL hQ0
    _ = Q * |quadVal α (lamCoef z)| * (2 * Z) ^ D := by ring
    _ ≤ 48 * (A + 1) ^ 2 * Z * (2 * Z) ^ D := mul_le_mul_of_nonneg_right h1 h2Z

/-- **The projected inequalities** `|z_j L_i(v)| ≤ 6 Z² (A + 1)⁴ Y^{e_i}`, `e = (-1, -3/4, 1)`,
once `Q² ≤ H^{1/4}`. -/
theorem hyp_ineq (hA : 1 ≤ A) (hε : 0 ≤ ε) (hZ1 : 1 ≤ Z) (hz : ∀ i, |(z i : ℝ)| ≤ Z)
    (hp : CFPoint α A ε v H Q) (hzv : ∑ i, z i * v i = 0) (hQ2 : Q ^ 2 ≤ H ^ (1 / 4 : ℝ))
    {Y : ℝ} (hY1 : 1 ≤ Y) (hYH : Y ≤ H) (hHY : H ≤ 3 * Z * (A + 1) ^ 4 * Y) (i : Fin 3) :
    |∑ k, quadVal α (projCoef z j i k) * v (j.succAbove k)| ≤
      6 * Z ^ 2 * (A + 1) ^ 4 * Y ^ (![-1, -(3 / 4), 1] : Fin 3 → ℝ) i := by
  have hH1 := hp.one_le_H
  have hH0 := hp.H_pos
  have hY0 : 0 < Y := by linarith
  have hA4 : (16 : ℝ) ≤ (A + 1) ^ 4 := by
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ (A + 1) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
  have hC : 24 * Z ≤ 6 * Z ^ 2 * (A + 1) ^ 4 := by nlinarith
  have hzZ : |(z j : ℝ)| ≤ Z := hz j
  rw [sum_projCoef α hzv j i, abs_mul]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.castSucc_zero, formVal_zero, Matrix.cons_val_zero]
    have h1 : |formL1 α v| ≤ 24 * H⁻¹ := by
      refine hp.L1_le.trans ?_
      rw [← Real.rpow_neg_one]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith))
        (by norm_num)
    have h2 : H⁻¹ ≤ Y ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one]; exact inv_anti₀ hY0 hYH
    have h3 : 0 ≤ Y ^ (-1 : ℝ) := by positivity
    calc |(z j : ℝ)| * |formL1 α v| ≤ Z * (24 * Y ^ (-1 : ℝ)) :=
          mul_le_mul hzZ (h1.trans (by linarith)) (abs_nonneg _) (by linarith)
      _ = 24 * Z * Y ^ (-1 : ℝ) := by ring
      _ ≤ 6 * Z ^ 2 * (A + 1) ^ 4 * Y ^ (-1 : ℝ) := mul_le_mul_of_nonneg_right hC h3
  · simp only [Fin.mk_one, Fin.castSucc_one, formVal_one, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    have h1 : |formL2 α v| ≤ 2 * H ^ (-(3 / 4) : ℝ) := by
      refine hp.L2_le.trans ?_
      rw [div_le_iff₀ hH0]
      have : H ^ (-(3 / 4) : ℝ) * H = H ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_add_one hH0.ne']; norm_num
      nlinarith
    have h2 : H ^ (-(3 / 4) : ℝ) ≤ Y ^ (-(3 / 4) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hY0 hYH (by norm_num)
    have h3 : 0 ≤ Y ^ (-(3 / 4) : ℝ) := by positivity
    calc |(z j : ℝ)| * |formL2 α v| ≤ Z * (2 * Y ^ (-(3 / 4) : ℝ)) :=
          mul_le_mul hzZ (h1.trans (by linarith)) (abs_nonneg _) (by linarith)
      _ = 2 * Z * Y ^ (-(3 / 4) : ℝ) := by ring
      _ ≤ 6 * Z ^ 2 * (A + 1) ^ 4 * Y ^ (-(3 / 4) : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) h3
  · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Real.rpow_one]
    rw [show (Fin.castSucc (2 : Fin 3) : Fin 4) = 2 from rfl, formVal_two]
    have hQ1 := hp.one_le_Q
    have h1 : |formL3 α v| ≤ 2 * H := by
      refine hp.L3_le.trans ?_
      rw [div_le_iff₀ (by positivity)]
      calc 2 * H = 2 * H * 1 := by ring
        _ ≤ 2 * H * Q ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hQ1) (by linarith)
    calc |(z j : ℝ)| * |formL3 α v| ≤ Z * (2 * H) :=
          mul_le_mul hzZ h1 (abs_nonneg _) (by linarith)
      _ ≤ Z * (2 * (3 * Z * (A + 1) ^ 4 * Y)) := by gcongr
      _ = 6 * Z ^ 2 * (A + 1) ^ 4 * Y := by ring

end Hyper

/-- The constants of `Real.exists_planes_of_lamCoef_ne_zero`. -/
noncomputable def hypConst (A c : ℝ) (D : ℕ) (K₃ : ℝ) : ℝ :=
  8 * (|log (48 * (A + 1) ^ 2 * 2 ^ D / c)| + D + 1) +
    K₃ * (3 / 4 : ℝ)⁻¹ ^ K₃ *
      (1 + log 2 + log 6 + 4 * log (A + 1) + |log c| + D * log 2 + D + 3) +
    log 3 + 4 * log (A + 1) + 1

theorem hypConst_split {A c : ℝ} (D : ℕ) (K₃ Z : ℝ) : hypConst A c D K₃ * (1 + log Z) =
    8 * (|log (48 * (A + 1) ^ 2 * 2 ^ D / c)| + D + 1) * (1 + log Z) +
    K₃ * (3 / 4 : ℝ)⁻¹ ^ K₃ *
      ((1 + log 2 + log 6 + 4 * log (A + 1) + |log c| + D * log 2 + D + 3) * (1 + log Z)) +
    (log 3 + 4 * log (A + 1) + 1) * (1 + log Z) := by
  simp only [hypConst]; ring

/-- **Late points have `Q² ≤ H^{1/4}`.** -/
theorem hyp_Q2 (hA : 1 ≤ A) (hc : 0 < c) {K₃ : ℝ} (hK₃ : 0 ≤ K₃) {Z H Q : ℝ} (hZ : 1 ≤ Z)
    (hH : 1 ≤ H) (hQ1 : 1 ≤ Q) (hQ : Q ≤ 48 * (A + 1) ^ 2 * Z * (2 * Z) ^ D / c)
    (hlate : hypConst A c D K₃ * (1 + log Z) ≤ log H) : Q ^ 2 ≤ H ^ (1 / 4 : ℝ) := by
  have hlogZ : 0 ≤ log Z := Real.log_nonneg hZ
  have hlA : 0 ≤ log (A + 1) := Real.log_nonneg (by linarith)
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  set Qmax := 48 * (A + 1) ^ 2 * Z * (2 * Z) ^ D / c
  have hQm : Qmax = 48 * (A + 1) ^ 2 * 2 ^ D / c * Z ^ (D + 1) := by
    simp only [Qmax]; rw [mul_pow, pow_succ]; field_simp; ring
  have hlog : log Qmax = log (48 * (A + 1) ^ 2 * 2 ^ D / c) + (D + 1) * log Z := by
    rw [hQm, Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
  have hκ : 8 * log Qmax ≤ 8 * (|log (48 * (A + 1) ^ 2 * 2 ^ D / c)| + D + 1) * (1 + log Z) := by
    rw [hlog]
    have := le_abs_self (log (48 * (A + 1) ^ 2 * 2 ^ D / c))
    have : 0 ≤ |log (48 * (A + 1) ^ 2 * 2 ^ D / c)| * log Z := by positivity
    nlinarith
  have hsplit := hypConst_split (A := A) (c := c) D K₃ Z
  have p2 : 0 ≤ K₃ * (3 / 4 : ℝ)⁻¹ ^ K₃ *
      ((1 + log 2 + log 6 + 4 * log (A + 1) + |log c| + D * log 2 + D + 3) * (1 + log Z)) := by
    have : 0 ≤ log 2 := Real.log_nonneg (by norm_num)
    have : 0 ≤ log 6 := Real.log_nonneg (by norm_num)
    positivity
  have p3 : 0 ≤ (log 3 + 4 * log (A + 1) + 1) * (1 + log Z) := by
    have : 0 ≤ log 3 := Real.log_nonneg (by norm_num)
    positivity
  have h8 : 8 * log Qmax ≤ log H := by linarith
  have hQm1 : 0 < Qmax := lt_of_lt_of_le (by linarith) hQ
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow,
    Real.log_rpow (by linarith)]
  have := Real.log_le_log (by linarith) hQ
  push_cast
  linarith

/-- **Late points are above the threshold** of the Subspace Theorem at `δ = 3/4`. -/
theorem hyp_thr (hA : 1 ≤ A) (hc : 0 < c) {K₃ : ℝ} (hK₃ : 0 ≤ K₃) {Z H Y : ℝ} (hZ : 1 ≤ Z)
    (hH : 1 ≤ H) (hY0 : 0 < Y) (hHY : H ≤ 3 * Z * (A + 1) ^ 4 * Y)
    (hlate : hypConst A c D K₃ * (1 + log Z) ≤ log H) :
    K₃ * (3 / 4 : ℝ)⁻¹ ^ K₃ * (1 + log (2 * Z) + log (6 * Z ^ 2 * (A + 1) ^ 4) +
      log (min 1 (c / (2 * Z) ^ D))⁻¹) ≤ log Y := by
  have hlogZ : 0 ≤ log Z := Real.log_nonneg hZ
  have hlA : 0 ≤ log (A + 1) := Real.log_nonneg (by linarith)
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hl2 : 0 ≤ log 2 := Real.log_nonneg (by norm_num)
  have hl6 : 0 ≤ log 6 := Real.log_nonneg (by norm_num)
  have hl3 : 0 ≤ log 3 := Real.log_nonneg (by norm_num)
  have h2Z : (0 : ℝ) < (2 * Z) ^ D := by positivity
  set g := c / (2 * Z) ^ D with hg
  have hγi : log (min 1 g)⁻¹ ≤ |log c| + D * log 2 + D * log Z := by
    rcases le_total 1 g with h | h
    · rw [min_eq_left h, inv_one, Real.log_one]; positivity
    · rw [min_eq_right h, hg, inv_div, Real.log_div h2Z.ne' hc.ne', Real.log_pow,
        Real.log_mul (by norm_num) (by linarith)]
      have := neg_abs_le (log c)
      nlinarith
  have hlC : log (6 * Z ^ 2 * (A + 1) ^ 4) = log 6 + 2 * log Z + 4 * log (A + 1) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num)
      (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
  have hl2Z : log (2 * Z) = log 2 + log Z := Real.log_mul (by norm_num) (by linarith)
  set κ3 : ℝ := 1 + log 2 + log 6 + 4 * log (A + 1) + |log c| + D * log 2 + D + 3
  have hsum : 1 + log (2 * Z) + log (6 * Z ^ 2 * (A + 1) ^ 4) + log (min 1 g)⁻¹ ≤
      κ3 * (1 + log Z) := by
    rw [hlC, hl2Z]
    have : 0 ≤ (1 + log 2 + log 6 + 4 * log (A + 1) + |log c| + D * log 2) * log Z := by
      positivity
    simp only [κ3]; nlinarith
  have hYlog : log H - log (3 * Z * (A + 1) ^ 4) ≤ log Y := by
    rw [sub_le_iff_le_add, ← Real.log_mul hY0.ne' (by positivity)]
    exact Real.log_le_log (by linarith) (by linarith [mul_comm Y (3 * Z * (A + 1) ^ 4)])
  have h3Z : log (3 * Z * (A + 1) ^ 4) ≤ (log 3 + 4 * log (A + 1) + 1) * (1 + log Z) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num)
      (by linarith), Real.log_pow]
    push_cast
    nlinarith
  have hsplit := hypConst_split (A := A) (c := c) D K₃ Z
  have p1 : 0 ≤ 8 * (|log (48 * (A + 1) ^ 2 * 2 ^ D / c)| + D + 1) * (1 + log Z) := by
    positivity
  have hK : 0 ≤ K₃ * (3 / 4 : ℝ)⁻¹ ^ K₃ := by positivity
  have := mul_le_mul_of_nonneg_left hsum hK
  linarith

/-- **The first application in three variables.** For `z` with `Λ ≠ 0` and `|zᵢ| ≤ Z`, the points
`v ⊥ z` with `log H ≥ K (1 + log Z)` lie in at most `NT` planes. -/
theorem exists_planes_of_lamCoef_ne_zero {a : ℝ} (hSB : SubspaceBound α a) (hA : 1 ≤ A)
    (hc : 0 < c) (hL : LiouvilleQuad α c D) :
    ∃ K NT : ℝ, 0 ≤ NT ∧ ∀ (z : Fin 4 → ℤ) (Z : ℝ), 1 ≤ Z → (∀ i, |(z i : ℝ)| ≤ Z) →
      quadVal α (lamCoef z) ≠ 0 →
      ∃ T : Finset (Submodule ℚ (Fin 4 → ℚ)), (#T : ℝ) ≤ NT ∧ (∀ U ∈ T, finrank ℚ U ≤ 2) ∧
        ∀ (ε : ℝ) (v : Fin 4 → ℤ) (H Q : ℝ), 0 ≤ ε → CFPoint α A ε v H Q →
          ∑ i, z i * v i = 0 → K * (1 + log Z) ≤ log H → ∃ U ∈ T, ptQ v ∈ U := by
  classical
  obtain ⟨K₃, hK₃, h3⟩ := hSB 3 (by norm_num) (by norm_num)
  refine ⟨hypConst A c D K₃, K₃ * (3 / 4 : ℝ)⁻¹ ^ a * (1 + log (3 / 4 : ℝ)⁻¹) ^ 2,
    by positivity, fun z Z hZ hz hΛ ↦ ?_⟩
  have hz0 : z ≠ 0 := fun h ↦ hΛ (by simp [h, lamCoef, quadVal])
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hz0
  have hj' : z j ≠ 0 := hj
  -- Liouville at `Λ`
  have hlam0 : lamCoef z ≠ 0 := fun h ↦ hΛ (by simp [h, quadVal])
  have hlamb : ∀ i, |(lamCoef z i : ℝ)| ≤ 2 * Z := by
    intro i
    fin_cases i
    · simp only [lamCoef, Fin.zero_eta, Matrix.cons_val_zero]; linarith [hz 0]
    · simp only [lamCoef, Fin.mk_one, Matrix.cons_val_one]
      push_cast
      exact (abs_add_le _ _).trans (by linarith [hz 1, hz 2])
    · simp only [lamCoef, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons]
      linarith [hz 3]
  have hΛL := hL _ _ hlam0 hlamb
  have h2Z : (0 : ℝ) < (2 * Z) ^ D := by positivity
  have hg0 : 0 < c / (2 * Z) ^ D := by positivity
  have hzj1 : (1 : ℝ) ≤ |(z j : ℝ)| := by
    have : (1 : ℤ) ≤ |z j| := Int.one_le_abs hj'
    exact_mod_cast this
  have hγdet : min 1 (c / (2 * Z) ^ D) ≤
      |(Matrix.of fun i k ↦ quadVal α (projCoef z j i k)).det| := by
    rw [det_projCoef, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow]
    refine (min_le_right _ _).trans ?_
    rw [div_le_iff₀ h2Z]
    have : (1 : ℝ) ≤ |(z j : ℝ)| ^ 2 := one_le_pow₀ hzj1
    have h0 : 0 ≤ |quadVal α (lamCoef z)| * (2 * Z) ^ D := by positivity
    nlinarith
  have hC1 : 1 ≤ 6 * Z ^ 2 * (A + 1) ^ 4 := by
    have : (1 : ℝ) ≤ (A + 1) ^ 4 := one_le_pow₀ (by linarith)
    have : (1 : ℝ) ≤ Z ^ 2 := one_le_pow₀ hZ
    nlinarith
  obtain ⟨T₃, hT₃, htop, hmem⟩ := h3 (projCoef z j) (2 * Z) (by linarith)
    (fun i k m ↦ abs_projCoef_le hz j i k m) _ (lt_min one_pos hg0) (min_le_left _ _) hγdet
    _ hC1 ![-1, -(3 / 4), 1] (3 / 4) (by norm_num) (by norm_num)
    (fun i ↦ by fin_cases i <;> norm_num) ⟨2, rfl⟩
    (by norm_num [Fin.sum_univ_three])
  refine ⟨T₃.image fun U ↦ perpZ z ⊓ U.comap (LinearMap.funLeft ℚ ℚ (Fin.succAbove j)), ?_, ?_,
    ?_⟩
  · exact (Nat.cast_le.2 Finset.card_image_le).trans hT₃
  · intro U hU
    obtain ⟨U', hU', rfl⟩ := Finset.mem_image.1 hU
    exact finrank_inf_comap_le_two (fun x hx h0 ↦ eq_zero_of_mem_perpZ hj' hx h0) (htop U' hU')
  -- the late points
  intro ε v H Q hε hp hzv hlate
  obtain ⟨hy0, hY1, hYH, hHY⟩ := hyp_point hj' hz hp hzv
  have hQ := hyp_Q_le hc hZ hz hΛL hp hzv
  have hQ2 := hyp_Q2 hA hc hK₃.le hZ hp.one_le_H hp.one_le_Q hQ hlate
  have hthr := hyp_thr hA hc hK₃.le hZ hp.one_le_H (by linarith) hHY hlate
  obtain ⟨U, hU, hyU⟩ := hmem _ hy0 (hyp_ineq hA hε hZ hz hp hzv hQ2 hY1 hYH hHY) hthr
  refine ⟨perpZ z ⊓ U.comap (LinearMap.funLeft ℚ ℚ (Fin.succAbove j)),
    Finset.mem_image.2 ⟨U, hU, rfl⟩, Submodule.mem_inf.2 ⟨ptQ_mem_perpZ hzv, ?_⟩⟩
  rw [Submodule.mem_comap]
  convert hyU using 1
  funext k
  simp [LinearMap.funLeft_apply, ptQ]


/-! ### On `T₀` -/

/-- The subspace `T₀ = {X₁ = X₂}`. -/
noncomputable def t0Sub : Submodule ℚ (Fin 4 → ℚ) := perpZ ![0, 1, -1, 0]

theorem ptQ_mem_t0Sub {v : Fin 4 → ℤ} (h : v 1 = v 2) : ptQ v ∈ t0Sub :=
  ptQ_mem_perpZ (by simp [Fin.sum_univ_four, h])

/-- The coordinates `(X₀, X₁, X₃)`. -/
noncomputable def t0Proj : (Fin 4 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ) := LinearMap.funLeft ℚ ℚ ![0, 1, 3]

theorem eq_zero_of_mem_t0Sub {x : Fin 4 → ℚ} (hx : x ∈ t0Sub) (h0 : t0Proj x = 0) : x = 0 := by
  rw [t0Sub, mem_perpZ] at hx
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hx
  push_cast at hx
  have hx' : x 1 = x 2 := by linarith
  have h (k : Fin 3) : x (![0, 1, 3] k) = 0 := by
    have := congrFun h0 k
    rwa [t0Proj, LinearMap.funLeft_apply] at this
  have h0' := h 0
  have h1' := h 1
  have h3' := h 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h0' h1' h3'
  funext i
  fin_cases i
  · exact h0'
  · exact h1'
  · simp only [Fin.reduceFinMk, Pi.zero_apply]; rw [← hx']; exact h1'
  · exact h3'

theorem t0Proj_ptQ (v : Fin 4 → ℤ) : t0Proj (ptQ v) = ptQ (t0Pt v) := by
  funext k
  fin_cases k <;> rfl

/-- **The application on `T₀`**: the points of `T₀` above `K ε^{-K}` lie in at most
`K ε^{-a} (1 + log ε⁻¹)²` planes. -/
theorem exists_planes_t0 {a : ℝ} (hSB : SubspaceBound α a) (hA : 1 ≤ A) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ T : Finset (Submodule ℚ (Fin 4 → ℚ)), (#T : ℝ) ≤ K * ε⁻¹ ^ a * (1 + log ε⁻¹) ^ 2 ∧
        (∀ U ∈ T, finrank ℚ U ≤ 2) ∧
        ∀ (v : Fin 4 → ℤ) (H Q : ℝ), CFPoint α A ε v H Q → v 1 = v 2 →
          K * ε⁻¹ ^ K ≤ log H → ∃ U ∈ T, ptQ v ∈ U := by
  classical
  obtain ⟨K₃, hK₃, h3⟩ := hSB 3 (by norm_num) (by norm_num)
  have hlA : 0 ≤ log (A + 1) := Real.log_nonneg (by linarith)
  set κ : ℝ := 1 + log 2 + log (24 * (A + 1) ^ 4)
  have hκ : 0 ≤ κ := by
    have : 0 ≤ log 2 := Real.log_nonneg (by norm_num)
    have : 0 ≤ log (24 * (A + 1) ^ 4) :=
      Real.log_nonneg (by nlinarith [one_le_pow₀ (M₀ := ℝ) (n := 4) (by linarith : 1 ≤ A + 1)])
    positivity
  set K := max K₃ (K₃ * κ + 4 * log (A + 1))
  have hKK : K₃ ≤ K := le_max_left _ _
  refine ⟨K, hK₃.trans_le hKK, fun ε hε hε1 ↦ ?_⟩
  have hεi : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
  have hA4 : (1 : ℝ) ≤ (A + 1) ^ 4 := one_le_pow₀ (by linarith)
  have hC1 : (1 : ℝ) ≤ 24 * (A + 1) ^ 4 := by linarith
  obtain ⟨T₃, hT₃, htop, hmem⟩ := h3 t0Coef 2 (by norm_num)
    (fun i k m ↦ by exact_mod_cast abs_t0Coef_le i k m) 1 one_pos le_rfl
    (by rw [det_t0Coef, abs_one]) (24 * (A + 1) ^ 4) hC1 ![-1 - ε, 0, 1] ε hε hε1
    (fun i ↦ by
      fin_cases i
      · simp only [Fin.zero_eta, Matrix.cons_val_zero]; linarith
      · simp
      · simp) ⟨2, rfl⟩
    (by simp [Fin.sum_univ_three]; linarith)
  refine ⟨T₃.image fun U ↦ t0Sub ⊓ U.comap t0Proj, ?_, ?_, ?_⟩
  · refine (Nat.cast_le.2 Finset.card_image_le).trans (hT₃.trans ?_)
    gcongr
  · intro U hU
    obtain ⟨U', hU', rfl⟩ := Finset.mem_image.1 hU
    exact finrank_inf_comap_le_two (fun x hx h0 ↦ eq_zero_of_mem_t0Sub hx h0) (htop U' hU')
  intro v H Q hp hv hlate
  have hH1 := hp.one_le_H
  have hH0 := hp.H_pos
  have hy0 : t0Pt v ≠ 0 := fun h ↦ hp.v0_ne_zero (by simpa [t0Pt] using congrFun h 0)
  set Y := ⨆ k, |(t0Pt v k : ℝ)|
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
  have hthr : K₃ * ε⁻¹ ^ K₃ * (1 + log 2 + log (24 * (A + 1) ^ 4) + log 1⁻¹) ≤ log Y := by
    rw [inv_one, Real.log_one, add_zero]
    have hYlog : log H - 4 * log (A + 1) ≤ log Y := by
      have := Real.log_le_log hH0 hHY
      rw [Real.log_mul (by positivity) hY0.ne', Real.log_pow] at this
      push_cast at this
      linarith
    have h1 : 1 ≤ ε⁻¹ ^ K₃ := Real.one_le_rpow hεi hK₃.le
    have h2 : ε⁻¹ ^ K₃ ≤ ε⁻¹ ^ K := Real.rpow_le_rpow_of_exponent_le hεi hKK
    have h3 : K₃ * κ + 4 * log (A + 1) ≤ K := le_max_right _ _
    have h4 : (K₃ * κ + 4 * log (A + 1)) * ε⁻¹ ^ K₃ ≤ K * ε⁻¹ ^ K :=
      mul_le_mul h3 h2 (by positivity) (hK₃.le.trans hKK)
    have h5 : 4 * log (A + 1) ≤ 4 * log (A + 1) * ε⁻¹ ^ K₃ :=
      le_mul_of_one_le_right (by positivity) h1
    nlinarith
  obtain ⟨U, hU, hyU⟩ := hmem _ hy0 hineq hthr
  refine ⟨t0Sub ⊓ U.comap t0Proj, Finset.mem_image.2 ⟨U, hU, rfl⟩,
    Submodule.mem_inf.2 ⟨ptQ_mem_t0Sub hv, ?_⟩⟩
  rw [Submodule.mem_comap, t0Proj_ptQ]
  exact hyU

end Real
