/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The lengths and the exponent `ε` of the proof of `δ < 1/(a+1)`

* `Nat.lenSeq E k = E^(k+1) (k+1)^(2(k+1))`: the lengths `ℓ_k` at which the complexity bound is
  used. They grow fast enough that the heights double (`Nat.mul_lenSeq_le_lenSeq_succ`), and
  slowly enough that `log ℓ_k ≍ k log k` (`Nat.log_lenSeq`).
* `Real.epsInv c₀ C δ L x = c₀ (2 C λ^δ + 2)` with `λ = x L + 2 x log x`: the inverse of the
  exponent `ε` at `x = 2 N + 1`, where `λ = log ℓ_{2N}`.
* `Real.eventually_le_two_pow`: `K ε^{-K} ≤ 2^N` for large `N`;
* `Real.eventually_lt_half`: `K ε^{-(b+1)} (1 + log ε⁻¹)³ < N` for large `N` when
  `(b + 1) δ < 1`.
-/

@[expose] public section

open Real Filter Asymptotics

namespace Nat

/-- The lengths `ℓ_k = E^(k+1) (k+1)^(2(k+1))`. -/
def lenSeq (E k : ℕ) : ℕ := E ^ (k + 1) * (k + 1) ^ (2 * (k + 1))

variable {E : ℕ}

theorem le_lenSeq (k : ℕ) : E ≤ lenSeq E k := by
  unfold lenSeq
  calc E ≤ E ^ (k + 1) := Nat.le_self_pow (by omega) E
    _ ≤ _ := Nat.le_mul_of_pos_right _ (by positivity)

theorem two_pow_le_lenSeq (hE : 2 ≤ E) (k : ℕ) : 2 ^ (k + 1) ≤ lenSeq E k := by
  unfold lenSeq
  calc 2 ^ (k + 1) ≤ E ^ (k + 1) := Nat.pow_le_pow_left hE _
    _ ≤ _ := Nat.le_mul_of_pos_right _ (by positivity)

/-- `E (k + 2)² ℓ_k ≤ ℓ_{k+1}`. -/
theorem mul_lenSeq_le_succ (k : ℕ) : E * (k + 2) ^ 2 * lenSeq E k ≤ lenSeq E (k + 1) := by
  unfold lenSeq
  have h : (k + 1) ^ (2 * (k + 1)) ≤ (k + 2) ^ (2 * (k + 1)) := Nat.pow_le_pow_left (by omega) _
  calc E * (k + 2) ^ 2 * (E ^ (k + 1) * (k + 1) ^ (2 * (k + 1)))
      ≤ E * (k + 2) ^ 2 * (E ^ (k + 1) * (k + 2) ^ (2 * (k + 1))) := by gcongr
    _ = E ^ (k + 1 + 1) * (k + 1 + 1) ^ (2 * (k + 1 + 1)) := by ring

theorem lenSeq_mono (hE : 1 ≤ E) : Monotone (lenSeq E) := by
  refine monotone_nat_of_le_succ fun k ↦ (le_trans ?_ (mul_lenSeq_le_succ k))
  exact Nat.le_mul_of_pos_left _ (Nat.mul_pos hE (by positivity))

theorem log_lenSeq (hE : 1 ≤ E) (k : ℕ) :
    Real.log (lenSeq E k) =
      ((k : ℝ) + 1) * Real.log E + 2 * ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1) := by
  have hE' : (E : ℝ) ≠ 0 := by positivity
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  push_cast [lenSeq]
  rw [Real.log_mul (pow_ne_zero _ hE') (pow_ne_zero _ hk), Real.log_pow, Real.log_pow]
  push_cast; ring

/-- **The lengths grow fast enough:** `B ℓ_k log ℓ_k ≤ ℓ_{k+1}` for `E = n²`, `4 B ≤ n`. -/
theorem mul_log_lenSeq_le {B : ℝ} (hB : 0 ≤ B) {n : ℕ} (hn : 1 ≤ n) (hBn : 4 * B ≤ n) (k : ℕ) :
    B * lenSeq (n ^ 2) k * Real.log (lenSeq (n ^ 2) k) ≤ lenSeq (n ^ 2) (k + 1) := by
  have hE : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
  have hstep : ((n ^ 2 * (k + 2) ^ 2 * lenSeq (n ^ 2) k : ℕ) : ℝ) ≤ lenSeq (n ^ 2) (k + 1) := by
    exact_mod_cast mul_lenSeq_le_succ k
  push_cast at hstep
  set s : ℝ := (k : ℝ) + 1
  have hs : 1 ≤ s := by simp [s]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : Real.log (lenSeq (n ^ 2) k) ≤ 4 * n * s ^ 2 := by
    rw [log_lenSeq hE]
    push_cast
    rw [Real.log_pow]
    have h1 : Real.log (n : ℝ) ≤ n := Real.log_le_self (by positivity)
    have h2 : Real.log s ≤ s := Real.log_le_self (by positivity)
    have h3 : 0 ≤ Real.log s := Real.log_nonneg hs
    have h4 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn'
    have h5 : s * ((2 : ℕ) * Real.log (n : ℝ)) ≤ s * (2 * n) := by
      push_cast; nlinarith
    have h6 : 2 * s * Real.log s ≤ 2 * s * s := by nlinarith
    have hss : s ≤ s ^ 2 := by nlinarith
    have h7 : s * (2 * n) ≤ 2 * n * s ^ 2 := by
      have := mul_le_mul_of_nonneg_left hss (by positivity : (0 : ℝ) ≤ 2 * n)
      linarith
    have h8 : 2 * s * s ≤ 2 * n * s ^ 2 := by
      have := mul_le_mul_of_nonneg_right hn' (by positivity : (0 : ℝ) ≤ 2 * s ^ 2)
      nlinarith
    linarith
  have hL : (0 : ℝ) ≤ lenSeq (n ^ 2) k := Nat.cast_nonneg _
  have hks : ((k : ℝ) + 2) = s + 1 := by simp [s]; ring
  rw [hks] at hstep
  have h1 : B * Real.log (lenSeq (n ^ 2) k) ≤ B * (4 * n * s ^ 2) :=
    mul_le_mul_of_nonneg_left hlog hB
  have h2 : B * (4 * n * s ^ 2) ≤ (n : ℝ) ^ 2 * (s + 1) ^ 2 := by
    have : 4 * B * n * s ^ 2 ≤ n * n * s ^ 2 := by
      have := mul_le_mul_of_nonneg_right hBn (by positivity : (0 : ℝ) ≤ n * s ^ 2)
      nlinarith
    nlinarith
  calc B * lenSeq (n ^ 2) k * Real.log (lenSeq (n ^ 2) k)
      = lenSeq (n ^ 2) k * (B * Real.log (lenSeq (n ^ 2) k)) := by ring
    _ ≤ lenSeq (n ^ 2) k * ((n : ℝ) ^ 2 * (s + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hL
    _ = (n : ℝ) ^ 2 * (s + 1) ^ 2 * lenSeq (n ^ 2) k := by ring
    _ ≤ _ := hstep

end Nat

namespace Real

/-- The inverse `ε⁻¹ = c₀ (2 C λ^δ + 2)` of the exponent, with `λ = x L + 2 x log x`. -/
noncomputable def epsInv (c₀ C δ L x : ℝ) : ℝ := c₀ * (2 * C * (x * L + 2 * x * log x) ^ δ + 2)

variable {c₀ C δ L x : ℝ}

theorem one_le_lam (hL : 1 ≤ L) (hx : 1 ≤ x) : 1 ≤ x * L + 2 * x * log x := by
  have h1 : 1 ≤ x * L := one_le_mul_of_one_le_of_one_le hx hL
  have h2 : 0 ≤ 2 * x * log x := by have := Real.log_nonneg hx; positivity
  linarith

theorem two_mul_le_epsInv (hc₀ : 0 ≤ c₀) (hC : 0 ≤ C) (hL : 1 ≤ L) (hx : 1 ≤ x) :
    2 * c₀ ≤ epsInv c₀ C δ L x := by
  have : 0 ≤ (x * L + 2 * x * log x) ^ δ :=
    Real.rpow_nonneg (by linarith [one_le_lam hL hx]) _
  unfold epsInv
  nlinarith [mul_nonneg hC this]

theorem epsInv_le_mul_rpow (hc₀ : 0 ≤ c₀) (hδ : 0 ≤ δ) (hL : 1 ≤ L) (hx : 1 ≤ x) :
    epsInv c₀ C δ L x ≤ c₀ * (2 * C + 2) * (x * L + 2 * x * log x) ^ δ := by
  have h1 : 1 ≤ (x * L + 2 * x * log x) ^ δ := Real.one_le_rpow (one_le_lam hL hx) hδ
  unfold epsInv
  have : 2 * C * (x * L + 2 * x * log x) ^ δ + 2 ≤ (2 * C + 2) * (x * L + 2 * x * log x) ^ δ := by
    nlinarith
  calc c₀ * (2 * C * (x * L + 2 * x * log x) ^ δ + 2)
      ≤ c₀ * ((2 * C + 2) * (x * L + 2 * x * log x) ^ δ) := mul_le_mul_of_nonneg_left this hc₀
    _ = _ := by ring

/-- The crude bound `ε⁻¹ ≤ c x²` for `δ ≤ 1`. -/
theorem epsInv_le_sq (hc₀ : 0 ≤ c₀) (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hL : 1 ≤ L)
    (hx : 1 ≤ x) : epsInv c₀ C δ L x ≤ c₀ * (2 * C + 2) * (L + 2) * x ^ 2 := by
  have hlam := one_le_lam hL hx
  have h1 : (x * L + 2 * x * log x) ^ δ ≤ x * L + 2 * x * log x :=
    Real.rpow_le_self_of_one_le hlam hδ1
  have h2 : x * L + 2 * x * log x ≤ (L + 2) * x ^ 2 := by
    have hlx := Real.log_le_self (by linarith : 0 ≤ x)
    have h3 : x * L ≤ x * x * L :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by linarith : 0 ≤ L)
    have h4 : 2 * x * log x ≤ 2 * x * x := mul_le_mul_of_nonneg_left hlx (by linarith)
    have h5 : (L + 2) * x ^ 2 = x * x * L + 2 * x * x := by ring
    linarith
  have h0 : 0 ≤ c₀ * (2 * C + 2) := by positivity
  calc epsInv c₀ C δ L x ≤ c₀ * (2 * C + 2) * (x * L + 2 * x * log x) ^ δ :=
        epsInv_le_mul_rpow hc₀ hδ hL hx
    _ ≤ c₀ * (2 * C + 2) * ((L + 2) * x ^ 2) := mul_le_mul_of_nonneg_left (h1.trans h2) h0
    _ = _ := by ring

/-- **The threshold:** `K ε^{-K} ≤ 2^N` for large `N`. -/
theorem eventually_le_two_pow {K : ℝ} (hK : 0 < K) (hc₀ : 0 ≤ c₀) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hL : 1 ≤ L) :
    ∀ᶠ N : ℕ in atTop, K * epsInv c₀ C δ L (2 * N + 1) ^ K ≤ 2 ^ N := by
  set c := max (c₀ * (2 * C + 2) * (L + 2)) 1
  have hc : 1 ≤ c := le_max_right _ _
  set k := ⌈K⌉₊
  have hO := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) (2 * k) one_lt_two).bound
    (c := (K * c ^ k * 9 ^ k)⁻¹) (by positivity)
  filter_upwards [hO, eventually_ge_atTop 1] with N hN hN1
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hN
  set x : ℝ := 2 * N + 1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hx : 1 ≤ x := by simp only [x]; linarith
  have he0 : 0 ≤ epsInv c₀ C δ L x := by
    have := two_mul_le_epsInv (δ := δ) hc₀ hC hL hx; linarith
  have h1 : epsInv c₀ C δ L x ≤ c * x ^ 2 :=
    (epsInv_le_sq hc₀ hC hδ hδ1 hL hx).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hcx : 1 ≤ c * x ^ 2 := one_le_mul_of_one_le_of_one_le hc (one_le_pow₀ hx)
  have h2 : epsInv c₀ C δ L x ^ K ≤ (c * x ^ 2) ^ (k : ℝ) :=
    (Real.rpow_le_rpow he0 h1 hK.le).trans
      (Real.rpow_le_rpow_of_exponent_le hcx (Nat.le_ceil K))
  rw [Real.rpow_natCast] at h2
  have h3 : (c * x ^ 2) ^ k ≤ c ^ k * 9 ^ k * (N : ℝ) ^ (2 * k) := by
    have : x ^ 2 ≤ 9 * (N : ℝ) ^ 2 := by simp only [x]; nlinarith
    calc (c * x ^ 2) ^ k ≤ (c * (9 * (N : ℝ) ^ 2)) ^ k := by gcongr
      _ = _ := by ring
  calc K * epsInv c₀ C δ L x ^ K ≤ K * (c ^ k * 9 ^ k * (N : ℝ) ^ (2 * k)) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) hK.le
    _ = (K * c ^ k * 9 ^ k) * (N : ℝ) ^ (2 * k) := by ring
    _ ≤ (K * c ^ k * 9 ^ k) * ((K * c ^ k * 9 ^ k)⁻¹ * 2 ^ N) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
    _ = 2 ^ N := by field_simp

/-- `λ ≤ (L + 2/η) x^(1+η)`. -/
theorem lam_le_rpow {η : ℝ} (hη : 0 < η) (hL : 1 ≤ L) (hx : 1 ≤ x) :
    x * L + 2 * x * log x ≤ (L + 2 / η) * x ^ (1 + η) := by
  have hx0 : 0 < x := by linarith
  have hxη : x ^ (1 + η) = x * x ^ η := by rw [Real.rpow_add hx0, Real.rpow_one]
  have h1 : x ≤ x ^ (1 + η) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (by linarith : (1 : ℝ) ≤ 1 + η)
  have h2 : log x ≤ x ^ η / η := Real.log_le_rpow_div hx0.le hη
  have h3 : 2 * x * log x ≤ 2 / η * x ^ (1 + η) := by
    rw [hxη]
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * x)
    calc 2 * x * log x ≤ 2 * x * (x ^ η / η) := this
      _ = 2 / η * (x * x ^ η) := by field_simp
  have h4 : x * L ≤ L * x ^ (1 + η) := by nlinarith
  nlinarith

/-- `ε⁻¹ ≤ c₃ x^ρ` with `ρ = δ (1 + η)`. -/
theorem epsInv_le_rpow {η : ℝ} (hη : 0 < η) (hc₀ : 0 ≤ c₀) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hL : 1 ≤ L) (hx : 1 ≤ x) :
    epsInv c₀ C δ L x ≤ c₀ * (2 * C + 2) * (L + 2 / η) ^ δ * x ^ (δ * (1 + η)) := by
  have hlam := one_le_lam hL hx
  have h1 : (x * L + 2 * x * log x) ^ δ ≤ ((L + 2 / η) * x ^ (1 + η)) ^ δ :=
    Real.rpow_le_rpow (by linarith) (lam_le_rpow hη hL hx) hδ
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by linarith),
    mul_comm (1 + η)] at h1
  have h0 : 0 ≤ c₀ * (2 * C + 2) := by positivity
  calc epsInv c₀ C δ L x ≤ c₀ * (2 * C + 2) * (x * L + 2 * x * log x) ^ δ :=
        epsInv_le_mul_rpow hc₀ hδ hL hx
    _ ≤ c₀ * (2 * C + 2) * ((L + 2 / η) ^ δ * x ^ (δ * (1 + η))) :=
        mul_le_mul_of_nonneg_left h1 h0
    _ = _ := by ring

/-- The pointwise bound `K ε^{-(b+1)} (1 + log ε⁻¹)³ ≤ c₅ x^γ`, `γ = ρ (b + 1) + 3 η`. -/
theorem count_le_rpow {K b η : ℝ} (hK : 0 < K) (hb : 0 ≤ b) (hη : 0 < η) (hc₀ : 1 ≤ c₀)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hL : 1 ≤ L) (hx : 1 ≤ x) :
    K * epsInv c₀ C δ L x ^ (b + 1) * (1 + log (epsInv c₀ C δ L x)) ^ 3 ≤
      K * (c₀ * (2 * C + 2) * (L + 2 / η) ^ δ) ^ (b + 1) *
        (1 + |log (c₀ * (2 * C + 2) * (L + 2 / η) ^ δ)| + δ * (1 + η) / η) ^ 3 *
        x ^ (δ * (1 + η) * (b + 1) + 3 * η) := by
  set c₃ := c₀ * (2 * C + 2) * (L + 2 / η) ^ δ
  set ρ := δ * (1 + η)
  set e := epsInv c₀ C δ L x
  have hx0 : 0 < x := by linarith
  have hc₃ : 0 < c₃ := by positivity
  have he1 : 1 ≤ e := by
    have := two_mul_le_epsInv (c₀ := c₀) (δ := δ) (by linarith) hC hL hx; linarith
  have he : e ≤ c₃ * x ^ ρ := epsInv_le_rpow hη (by linarith) hC hδ hL hx
  have hρ : 0 ≤ ρ := by positivity
  -- the power
  have hp : e ^ (b + 1) ≤ c₃ ^ (b + 1) * x ^ (ρ * (b + 1)) := by
    calc e ^ (b + 1) ≤ (c₃ * x ^ ρ) ^ (b + 1) := Real.rpow_le_rpow (by linarith) he (by linarith)
      _ = _ := by rw [Real.mul_rpow hc₃.le (by positivity), ← Real.rpow_mul hx0.le]
  -- the logarithm
  have hxη : 1 ≤ x ^ η := Real.one_le_rpow hx hη.le
  have hl : 1 + log e ≤ (1 + |log c₃| + ρ / η) * x ^ η := by
    have h1 : log e ≤ log c₃ + ρ * log x := by
      calc log e ≤ log (c₃ * x ^ ρ) := Real.log_le_log (by linarith) he
        _ = _ := by rw [Real.log_mul hc₃.ne' (by positivity), Real.log_rpow hx0]
    have h2 : ρ * log x ≤ ρ / η * x ^ η := by
      have := mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hx0.le hη) hρ
      calc ρ * log x ≤ ρ * (x ^ η / η) := this
        _ = _ := by ring
    have h3 : log c₃ ≤ |log c₃| := le_abs_self _
    have h4 : (1 + |log c₃|) * 1 ≤ (1 + |log c₃|) * x ^ η :=
      mul_le_mul_of_nonneg_left hxη (by positivity)
    have h5 : (1 + |log c₃| + ρ / η) * x ^ η = (1 + |log c₃|) * x ^ η + ρ / η * x ^ η := by ring
    rw [h5]; linarith
  have hl0 : 0 ≤ 1 + log e := by have := Real.log_nonneg he1; linarith
  have hl3 : (1 + log e) ^ 3 ≤ (1 + |log c₃| + ρ / η) ^ 3 * x ^ (3 * η) := by
    calc (1 + log e) ^ 3 ≤ ((1 + |log c₃| + ρ / η) * x ^ η) ^ 3 := pow_le_pow_left₀ hl0 hl 3
      _ = _ := by
        rw [mul_pow, ← Real.rpow_natCast (x ^ η), ← Real.rpow_mul hx0.le]
        norm_num [mul_comm]
  have hpow : x ^ (ρ * (b + 1) + 3 * η) = x ^ (ρ * (b + 1)) * x ^ (3 * η) :=
    Real.rpow_add hx0 _ _
  rw [hpow]
  have hA : 0 ≤ e ^ (b + 1) := by positivity
  calc K * e ^ (b + 1) * (1 + log e) ^ 3
      ≤ K * (c₃ ^ (b + 1) * x ^ (ρ * (b + 1))) * ((1 + |log c₃| + ρ / η) ^ 3 * x ^ (3 * η)) := by
        gcongr
    _ = _ := by ring

/-- **The final count is too small:** if `(b + 1) δ < 1` then
`K ε^{-(b+1)} (1 + log ε⁻¹)³ < (x - 1)/2` for large `x`. -/
theorem eventually_lt_half {K b : ℝ} (hK : 0 < K) (hc₀ : 1 ≤ c₀) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hδ : 0 ≤ δ) (hbδ : (b + 1) * δ < 1) (hL : 1 ≤ L) :
    ∀ᶠ x : ℝ in atTop,
      K * epsInv c₀ C δ L x ^ (b + 1) * (1 + log (epsInv c₀ C δ L x)) ^ 3 < (x - 1) / 2 := by
  set θ := (b + 1) * δ
  have hθ : 0 ≤ θ := by positivity
  set η := (1 - θ) / (2 * (θ + 3))
  have hη : 0 < η := div_pos (by linarith) (by positivity)
  set γ := δ * (1 + η) * (b + 1) + 3 * η
  have hηθ : η * (θ + 3) = (1 - θ) / 2 := by
    simp only [η]; field_simp
  have hγ : γ < 1 := by
    have : γ = θ + η * (θ + 3) := by simp only [γ, θ]; ring
    rw [this, hηθ]; linarith
  have hγ0 : 0 ≤ γ := by positivity
  set c₅ := K * (c₀ * (2 * C + 2) * (L + 2 / η) ^ δ) ^ (b + 1) *
    (1 + |log (c₀ * (2 * C + 2) * (L + 2 / η) ^ δ)| + δ * (1 + η) / η) ^ 3
  have hc₅ : 0 ≤ c₅ := by positivity
  have ht := (tendsto_rpow_atTop (by linarith : 0 < 1 - γ)).eventually_gt_atTop (4 * c₅ + 1)
  filter_upwards [ht, eventually_ge_atTop 2] with x hx1 hx2
  have hx : 1 ≤ x := by linarith
  have hpt := count_le_rpow (c₀ := c₀) (C := C) (δ := δ) (L := L) hK hb hη hc₀ hC hδ hL hx
  have hxx : x ^ γ * x ^ (1 - γ) = x := by
    rw [← Real.rpow_add (by linarith)]; simp
  have hxγ : 1 ≤ x ^ γ := Real.one_le_rpow hx hγ0
  have h1 : x ^ γ * (4 * c₅ + 1) < x ^ γ * x ^ (1 - γ) :=
    mul_lt_mul_of_pos_left hx1 (by linarith)
  rw [hxx] at h1
  have h2 : c₅ * x ^ γ < (x - 1) / 2 := by nlinarith
  exact lt_of_le_of_lt hpt h2

end Real
