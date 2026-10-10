/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Claim
public import Bugeaud2013.additions.Points

/-!
# The points of §3 satisfy the inequalities of `Real.CFPoint`

For partial quotients `1 ≤ a_ℓ ≤ A`, a repetition of length `u` at distance `r ≥ max u 2` after
`w = j + 1`, which cannot be slid to the left when `w ≥ 2`, gives the point
`v = Nat.spadeVec a j r` with `H = q_w q_{w+r}`, `Q = q_w`. If `H^ε ≤ 2^u`, it satisfies the
inequalities of `Real.CFPoint` (`Nat.cfPoint_spadeVec`):

* **the head** `H ≤ (A + 1)⁴ |v₀|` (`Nat.head_le`): `v₀ = q_{w-1} q_{w+r} - q_w q_{w+r-1}`, and
  `q_ℓ = a_ℓ q_{ℓ-1} + q_{ℓ-2}` with `a_w ≠ a_{w+r}` leaves a term of size `q q'` with
  `q q' ≥ H / (A + 1)³`; for `w = 1` the same holds since `q₀ = 1`;
* `|L₂(v)| ≥ q_w / 2 q_{w+r}` (`Nat.le_abs_formL2`): `L₂(v) = q_{w-1} e_{w+r} - q_w e_{w+r-1}` with
  `e_ℓ = q_ℓ α - p_ℓ` of alternating signs, and `q_{ℓ+1} |e_ℓ| ≥ 1/2`;
* the upper bounds are (3.2)–(3.4) of the paper (`Nat.abs_spadeL1_le` and its neighbours), and
  the Claim is `Nat.abs_claim_le` for `w ≥ 3` and trivial for `w ≤ 2`.
-/

@[expose] public section

open Real

namespace Nat

variable {a : ℕ → ℕ} {A : ℕ}

section Bounded

variable (ha : ∀ n, 1 ≤ a (n + 1)) (hA : ∀ n, a (n + 1) ≤ A)
include ha hA

/-- `q_{ℓ+1} ≤ (A + 1) q_ℓ`. -/
theorem contDen_succ_le (n : ℕ) : (contDen a (n + 1) : ℝ) ≤ (A + 1) * contDen a n := by
  rcases n with _ | n
  · simp only [contDen_one, zero_add]
    have := hA 0
    simp only [zero_add] at this
    have h0 : contDen a 0 = 1 := rfl
    rw [h0]; push_cast
    have : (a 1 : ℝ) ≤ A := by exact_mod_cast this
    linarith
  · rw [contDen_add_two]
    push_cast
    have h1 : (a (n + 2) : ℝ) ≤ A := by exact_mod_cast hA (n + 1)
    have h2 : (contDen a n : ℝ) ≤ contDen a (n + 1) := contDen_mono_real ha (by omega)
    have h3 : (0 : ℝ) ≤ contDen a (n + 1) := Nat.cast_nonneg _
    nlinarith

/-- `q_ℓ ≤ (A + 1)^ℓ`. -/
theorem contDen_le_pow (n : ℕ) : (contDen a n : ℝ) ≤ (A + 1) ^ n := by
  induction n with
  | zero => simp [contDen]
  | succ n ih =>
    have := contDen_succ_le ha hA n
    rw [pow_succ]
    have hA0 : (0 : ℝ) ≤ A + 1 := by positivity
    nlinarith

omit ha hA in
/-- The arithmetic of the head for `w = 1`. -/
theorem head_aux_one {q0 q1 a1 b2 b3 A : ℝ} (hA1 : 1 ≤ A) (ha1' : a1 ≤ A)
    (hb2 : 1 ≤ b2) (hb2' : b2 ≤ A) (hb3 : 1 ≤ b3) (hb3' : b3 ≤ A) (hq0 : 1 ≤ q0)
    (hq01 : q0 ≤ q1) (hq1 : q1 ≤ (A + 1) * q0) (hab : a1 ≤ b3 ∨ b3 + 1 ≤ a1) :
    a1 * (b3 * (b2 * q1 + q0) + q1) ≤
      (A + 1) ^ 4 * |1 * (b3 * (b2 * q1 + q0) + q1) - a1 * (b2 * q1 + q0)| := by
  set Q2 := b2 * q1 + q0
  have hq1' : 1 ≤ q1 := hq0.trans hq01
  have hQ2 : Q2 ≤ (A + 1) * q1 := by simp only [Q2]; nlinarith
  have hQ2' : q1 + q0 ≤ Q2 := by simp only [Q2]; nlinarith
  have hH : a1 * (b3 * Q2 + q1) ≤ A * ((A + 1) * Q2) := by
    have : b3 * Q2 + q1 ≤ (A + 1) * Q2 := by nlinarith
    exact mul_le_mul ha1' this (by positivity) (by linarith)
  have hA0 : (0 : ℝ) < A + 1 := by linarith
  rcases hab with h | h
  · have hv : q1 ≤ 1 * (b3 * Q2 + q1) - a1 * Q2 := by nlinarith
    rw [abs_of_nonneg (by linarith)]
    calc a1 * (b3 * Q2 + q1) ≤ A * ((A + 1) * Q2) := hH
      _ ≤ A * ((A + 1) * ((A + 1) * q1)) := by gcongr
      _ ≤ (A + 1) * ((A + 1) * ((A + 1) * q1)) := by gcongr; linarith
      _ ≤ (A + 1) ^ 4 * q1 := by
          have : (A + 1) ^ 3 ≤ (A + 1) ^ 4 := pow_le_pow_right₀ (by linarith) (by omega)
          nlinarith
      _ ≤ (A + 1) ^ 4 * (1 * (b3 * Q2 + q1) - a1 * Q2) := by gcongr
  · have hv : q0 ≤ -(1 * (b3 * Q2 + q1) - a1 * Q2) := by nlinarith
    rw [abs_of_neg (by linarith)]
    calc a1 * (b3 * Q2 + q1) ≤ A * ((A + 1) * Q2) := hH
      _ ≤ A * ((A + 1) * ((A + 1) * ((A + 1) * q0))) := by gcongr; nlinarith
      _ ≤ (A + 1) * ((A + 1) * ((A + 1) * ((A + 1) * q0))) := by gcongr; linarith
      _ = (A + 1) ^ 4 * q0 := by ring
      _ ≤ (A + 1) ^ 4 * -(1 * (b3 * Q2 + q1) - a1 * Q2) := by gcongr

omit ha hA in
/-- The arithmetic of the head for `w ≥ 2`. -/
theorem head_aux_two {Q0 Q1 R0 R1 a1 a2 A : ℝ} (hA1 : 1 ≤ A) (ha1' : a1 ≤ A)
    (ha2 : 1 ≤ a2) (ha2' : a2 ≤ A) (hQ0 : 1 ≤ Q0) (hR0 : 1 ≤ R0) (hQ01 : Q0 ≤ Q1)
    (hR01 : R0 ≤ R1) (hQ1 : Q1 ≤ (A + 1) * Q0) (hR1 : R1 ≤ (A + 1) * R0)
    (hab : a1 + 1 ≤ a2 ∨ a2 + 1 ≤ a1) :
    (a1 * Q1 + Q0) * (a2 * R1 + R0) ≤
      (A + 1) ^ 4 * |Q1 * (a2 * R1 + R0) - (a1 * Q1 + Q0) * R1| := by
  have hW : a1 * Q1 + Q0 ≤ (A + 1) * Q1 := by nlinarith
  have hM : a2 * R1 + R0 ≤ (A + 1) * R1 := by nlinarith
  have hA0 : (0 : ℝ) < A + 1 := by linarith
  have h34 : (A + 1 : ℝ) ^ 3 ≤ (A + 1) ^ 4 := pow_le_pow_right₀ (by linarith) (by omega)
  have hQ1p : 0 < Q1 := by linarith
  have hR1p : 0 < R1 := by linarith
  have hQR : 0 ≤ Q1 * R1 := by positivity
  rcases hab with h | h
  · have hv : Q1 * R0 ≤ Q1 * (a2 * R1 + R0) - (a1 * Q1 + Q0) * R1 := by
      have : Q1 * R1 ≤ (a2 - a1) * Q1 * R1 := by
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ a2 - a1 - 1) hQR
        linarith
      nlinarith
    have hQR0 : 0 ≤ Q1 * R0 := by positivity
    rw [abs_of_nonneg (by linarith)]
    calc (a1 * Q1 + Q0) * (a2 * R1 + R0) ≤ ((A + 1) * Q1) * ((A + 1) * R1) :=
          mul_le_mul hW hM (by positivity) (by positivity)
      _ ≤ ((A + 1) * Q1) * ((A + 1) * ((A + 1) * R0)) := by gcongr
      _ = (A + 1) ^ 3 * (Q1 * R0) := by ring
      _ ≤ (A + 1) ^ 4 * (Q1 * R0) := mul_le_mul_of_nonneg_right h34 hQR0
      _ ≤ (A + 1) ^ 4 * (Q1 * (a2 * R1 + R0) - (a1 * Q1 + Q0) * R1) := by gcongr
  · have hv : Q0 * R1 ≤ -(Q1 * (a2 * R1 + R0) - (a1 * Q1 + Q0) * R1) := by
      have : Q1 * R1 ≤ (a1 - a2) * Q1 * R1 := by
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ a1 - a2 - 1) hQR
        linarith
      nlinarith
    have hQR0 : 0 ≤ Q0 * R1 := by positivity
    have hQR1 : 0 < Q0 * R1 := mul_pos (by linarith) hR1p
    rw [abs_of_neg (by linarith)]
    calc (a1 * Q1 + Q0) * (a2 * R1 + R0) ≤ ((A + 1) * Q1) * ((A + 1) * R1) :=
          mul_le_mul hW hM (by positivity) (by positivity)
      _ ≤ ((A + 1) * ((A + 1) * Q0)) * ((A + 1) * R1) := by gcongr
      _ = (A + 1) ^ 3 * (Q0 * R1) := by ring
      _ ≤ (A + 1) ^ 4 * (Q0 * R1) := mul_le_mul_of_nonneg_right h34 hQR0
      _ ≤ (A + 1) ^ 4 * -(Q1 * (a2 * R1 + R0) - (a1 * Q1 + Q0) * R1) := by gcongr

/-- **The head of `v₀`**: `H ≤ (A + 1)⁴ |v₀|` for `H = q_w q_{w+r}`, `w = j + 1`, `r ≥ 2`, if
`a_w ≠ a_{w+r}` when `w ≥ 2`. -/
theorem head_le {j r : ℕ} (hr : 2 ≤ r) (hne : 1 ≤ j → a (j + 1) ≠ a (j + 1 + r)) :
    (contDen a (j + 1) : ℝ) * contDen a (j + 1 + r) ≤ (A + 1) ^ 4 * |(spadeVec a j r 0 : ℝ)| := by
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast (ha 0).trans (hA 0)
  have hsucc := contDen_succ_le ha hA
  have hpos (n : ℕ) : (1 : ℝ) ≤ contDen a n := by exact_mod_cast one_le_contDen ha n
  have hlo (n : ℕ) : (1 : ℝ) ≤ a (n + 1) := by exact_mod_cast ha n
  have hhi (n : ℕ) : (a (n + 1) : ℝ) ≤ A := by exact_mod_cast hA n
  rw [spadeVec_zero]
  push_cast
  rcases j with _ | i
  · -- `w = 1`
    obtain ⟨t, rfl⟩ : ∃ t, r = t + 2 := ⟨r - 2, by omega⟩
    have e3 : contDen a (0 + 1 + (t + 2)) =
        a (t + 3) * (a (t + 2) * contDen a (t + 1) + contDen a t) + contDen a (t + 1) := by
      rw [show 0 + 1 + (t + 2) = (t + 1) + 2 by ring, contDen_add_two, contDen_add_two]
    have e2 : contDen a (0 + (t + 2)) = a (t + 2) * contDen a (t + 1) + contDen a t := by
      rw [zero_add]; exact contDen_add_two a t
    have e0 : contDen a 0 = 1 := rfl
    have e1 : contDen a (0 + 1) = a 1 := rfl
    rw [e3, e2, e0, e1]
    push_cast
    have hab : (a 1 : ℝ) ≤ a (t + 3) ∨ (a (t + 3) : ℝ) + 1 ≤ a 1 := by
      rcases le_or_gt (a 1) (a (t + 3)) with h | h
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (by exact_mod_cast h)
    exact head_aux_one hA1 (hhi 0) (hlo (t + 1)) (hhi (t + 1)) (hlo (t + 2)) (hhi (t + 2))
      (hpos t)
      (contDen_mono_real ha (by omega)) (hsucc t) hab
  · -- `w = i + 2 ≥ 2`
    have hne' := hne (by omega)
    have ew : contDen a (i + 1 + 1) = a (i + 2) * contDen a (i + 1) + contDen a i :=
      contDen_add_two a i
    have em : contDen a (i + 1 + 1 + r) =
        a (i + r + 2) * contDen a (i + r + 1) + contDen a (i + r) := by
      rw [show i + 1 + 1 + r = (i + r) + 2 by ring, contDen_add_two]
    rw [ew, em, show i + 1 + r = i + r + 1 by ring]
    push_cast
    have hne'' : a (i + 2) ≠ a (i + r + 2) := by
      rw [show i + r + 2 = i + 1 + 1 + r by ring]; exact hne'
    have hab : (a (i + 2) : ℝ) + 1 ≤ a (i + r + 2) ∨ (a (i + r + 2) : ℝ) + 1 ≤ a (i + 2) := by
      rcases Nat.lt_or_gt_of_ne hne'' with h | h
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (by exact_mod_cast h)
    exact head_aux_two hA1 (hhi (i + 1)) (hlo (i + r + 1)) (hhi (i + r + 1))
      (hpos i) (hpos (i + r)) (contDen_mono_real ha (by omega)) (contDen_mono_real ha (by omega))
      (hsucc i) (hsucc (i + r)) hab

end Bounded

/-! ### The lower bound for `L₂` -/

/-- `y |g| ≤ |x f - y g|` for `x, y ≥ 0` and `f g < 0`. -/
theorem le_abs_sub_of_mul_neg {x y f g : ℝ} (hx : 0 ≤ x) (hfg : f * g < 0) :
    y * |g| ≤ |x * f - y * g| := by
  rcases lt_or_gt_of_ne (show g ≠ 0 by rintro rfl; simp at hfg) with hg | hg
  · have hf : 0 < f := by
      by_contra h
      push Not at h
      nlinarith
    rw [abs_of_neg hg]
    refine le_trans ?_ (le_abs_self _)
    nlinarith [mul_nonneg hx hf.le]
  · have hf : f < 0 := by
      by_contra h
      push Not at h
      nlinarith
    rw [abs_of_pos hg]
    refine le_trans ?_ (neg_le_abs _)
    nlinarith [mul_nonneg hx (neg_nonneg.2 hf.le)]

section Positive

variable (ha : ∀ n, 1 ≤ a (n + 1))
include ha

/-- `e_ℓ = q_ℓ α - p_ℓ` alternates in sign. -/
theorem mul_err_succ_neg (n : ℕ) :
    ((contDen a n : ℝ) * contFrac a - contNum a n) *
      ((contDen a (n + 1) : ℝ) * contFrac a - contNum a (n + 1)) < 0 := by
  have hq (m : ℕ) : (contDen a m : ℝ) * contFrac a - contNum a m =
      contDen a m * (contFrac a - contConv a m) := by
    have := contDen_pos_real ha m
    rw [contConv]; field_simp
  rw [hq, hq]
  have q0 := contDen_pos_real ha n
  have q1 := contDen_pos_real ha (n + 1)
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h1 := contConv_two_mul_lt_contFrac ha k
    have h2 := contFrac_lt_contConv_odd ha k
    rw [show k + k = 2 * k by ring] at *
    have d0 : 0 < contFrac a - contConv a (2 * k) := by linarith
    have d1 : contFrac a - contConv a (2 * k + 1) < 0 := by linarith
    have p0 : 0 < (contDen a (2 * k) : ℝ) * (contFrac a - contConv a (2 * k)) := by positivity
    have p1 : (contDen a (2 * k + 1) : ℝ) * (contFrac a - contConv a (2 * k + 1)) < 0 :=
      mul_neg_of_pos_of_neg q1 d1
    exact mul_neg_of_pos_of_neg p0 p1
  · have h1 := contFrac_lt_contConv_odd ha k
    have h2 := contConv_two_mul_lt_contFrac ha (k + 1)
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
    have d0 : contFrac a - contConv a (2 * k + 1) < 0 := by linarith
    have d1 : 0 < contFrac a - contConv a (2 * (k + 1)) := by linarith
    have q1' := contDen_pos_real ha (2 * (k + 1))
    have p0 : (contDen a (2 * k + 1) : ℝ) * (contFrac a - contConv a (2 * k + 1)) < 0 :=
      mul_neg_of_pos_of_neg q0 d0
    have p1 : 0 < (contDen a (2 * (k + 1)) : ℝ) * (contFrac a - contConv a (2 * (k + 1))) :=
      mul_pos q1' d1
    exact mul_neg_of_neg_of_pos p0 p1

/-- `q_{ℓ+1} |q_ℓ α - p_ℓ| ≥ 1/2`. -/
theorem le_abs_err (n : ℕ) :
    1 / (2 * contDen a (n + 1)) ≤ |(contDen a n : ℝ) * contFrac a - contNum a n| := by
  set e0 := (contDen a n : ℝ) * contFrac a - contNum a n
  set e1 := (contDen a (n + 1) : ℝ) * contFrac a - contNum a (n + 1)
  have hid : (contDen a (n + 1) : ℝ) * e0 - contDen a n * e1 = (-1) ^ n := by
    have := contNum_mul_contDen_sub a n
    have h : ((contNum a (n + 1) : ℤ) * contDen a n - contNum a n * contDen a (n + 1) : ℝ) =
        (-1) ^ n := by exact_mod_cast this
    simp only [e0, e1]
    push_cast at h
    linear_combination h
  have habs : |(contDen a (n + 1) : ℝ) * e0 - contDen a n * e1| = 1 := by
    rw [hid, abs_pow, abs_neg, abs_one, one_pow]
  have he1 : |e1| ≤ 1 / contDen a (n + 2) := abs_contDen_mul_contFrac_sub_le ha (n + 1)
  have h2 : (2 : ℝ) * contDen a n ≤ contDen a (n + 2) := by
    exact_mod_cast two_mul_contDen_le ha n
  have q0 := contDen_pos_real ha n
  have q1 := contDen_pos_real ha (n + 1)
  have q2 := contDen_pos_real ha (n + 2)
  have h3 : (contDen a n : ℝ) * |e1| ≤ 1 / 2 := by
    calc (contDen a n : ℝ) * |e1| ≤ contDen a n * (1 / contDen a (n + 2)) :=
          mul_le_mul_of_nonneg_left he1 q0.le
      _ ≤ 1 / 2 := by rw [mul_one_div, div_le_iff₀ q2]; linarith
  have h4 : 1 ≤ (contDen a (n + 1) : ℝ) * |e0| + contDen a n * |e1| := by
    rw [← habs]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **The lower bound for `L₂`**: `q_w / 2 q_{w+r} ≤ |α v₀ - v₁|`. -/
theorem le_abs_formL2 (j r : ℕ) :
    (contDen a (j + 1) : ℝ) / (2 * contDen a (j + 1 + r)) ≤
      |formL2 (contFrac a) (spadeVec a j r)| := by
  set α := contFrac a
  have key : formL2 α (spadeVec a j r) =
      contDen a j * ((contDen a (j + 1 + r) : ℝ) * α - contNum a (j + 1 + r)) -
        contDen a (j + 1) * ((contDen a (j + r) : ℝ) * α - contNum a (j + r)) := by
    simp only [formL2, spadeVec_zero, spadeVec_one]
    push_cast; ring
  have hsign := mul_err_succ_neg ha (j + r)
  rw [show j + r + 1 = j + 1 + r by ring] at hsign
  have h1 := le_abs_sub_of_mul_neg (x := contDen a j) (y := contDen a (j + 1)) (Nat.cast_nonneg _)
    (by rw [mul_comm] at hsign; exact hsign)
  rw [key]
  refine le_trans ?_ h1
  have h2 := le_abs_err ha (j + r)
  rw [show j + r + 1 = j + 1 + r by ring] at h2
  have q1 := contDen_pos_real ha (j + 1)
  calc (contDen a (j + 1) : ℝ) / (2 * contDen a (j + 1 + r)) =
        contDen a (j + 1) * (1 / (2 * contDen a (j + 1 + r))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 q1.le

end Positive

/-! ### The point -/

/-- **The points of §3 satisfy the inequalities of `Real.CFPoint`.** -/
theorem cfPoint_spadeVec (ha : ∀ n, 1 ≤ a (n + 1)) (hA : ∀ n, a (n + 1) ≤ A) {j r u : ℕ}
    (hu : 1 ≤ u) (hur : u ≤ r) (hr : 2 ≤ r)
    (hrep : ∀ m, j + 1 < m → m ≤ j + 1 + u → a (m + r) = a m)
    (hne : 1 ≤ j → a (j + 1) ≠ a (j + 1 + r)) {ε : ℝ}
    (hεu : ((contDen a (j + 1) : ℝ) * contDen a (j + 1 + r)) ^ ε ≤ 2 ^ u) :
    CFPoint (contFrac a) A ε (spadeVec a j r) ((contDen a (j + 1) : ℝ) * contDen a (j + 1 + r))
      (contDen a (j + 1)) := by
  set α := contFrac a
  set Qw : ℝ := (contDen a (j + 1) : ℝ)
  set Qm : ℝ := (contDen a (j + 1 + r) : ℝ)
  set H := Qw * Qm
  have hQw := contDen_pos_real ha (j + 1)
  have hQm := contDen_pos_real ha (j + 1 + r)
  have hQw1 : (1 : ℝ) ≤ Qw := by simp only [Qw]; exact_mod_cast one_le_contDen ha (j + 1)
  have hwm : Qw ≤ Qm := contDen_mono_real ha (by omega)
  have hH0 : 0 < H := by positivity
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast (ha 0).trans (hA 0)
  set E := H ^ ε
  have hE0 : 0 < E := Real.rpow_pos_of_pos hH0 ε
  have hEu : E ≤ 2 ^ u := hεu
  have hα0 : 0 < α := contFrac_pos ha
  have hα1 : α < 1 := contFrac_lt_one ha
  refine
    { abs_le := abs_spadeVec_le ha j r
      head := head_le ha hA hr hne
      one_le_Q := hQw1
      sq_le := by rw [sq]; exact mul_le_mul_of_nonneg_left hwm hQw.le
      L1_le := ?_
      L2_le := ?_
      L2_le_eps := ?_
      le_L2 := ?_
      L3_le := ?_
      claim := ?_ }
  · -- (3.4)
    have h1 := abs_spadeL1_le ha hu hur hrep
    have h2 := contDen_sq_div_le ha (j + 1 + r) hu
    set QN : ℝ := (contDen a (j + 1 + r + u) : ℝ)
    have hQN := contDen_pos_real ha (j + 1 + r + u)
    have hpow : H ^ (-1 - ε) = 1 / (H * E) := by
      rw [show -1 - ε = -(1 + ε) by ring, Real.rpow_neg hH0.le, Real.rpow_add hH0,
        Real.rpow_one]; ring
    rw [hpow]
    refine h1.trans ?_
    have e1 : 12 * (Qm / Qw) / QN ^ 2 = 12 / H * (Qm ^ 2 / QN ^ 2) := by
      simp only [H]; field_simp
    rw [e1]
    calc 12 / H * (Qm ^ 2 / QN ^ 2) ≤ 12 / H * (2 / 2 ^ u) := by gcongr
      _ ≤ 12 / H * (2 / E) := by gcongr
      _ = 24 * (1 / (H * E)) := by field_simp; ring
  · -- (3.2)
    have h := abs_spadeL2_le ha j r
    have e : formL2 α (spadeVec a j r) = α * ((contDen a j * contDen a (j + 1 + r) -
        contDen a (j + 1) * contDen a (j + r) : ℤ) : ℝ) -
        ((contDen a j * contNum a (j + 1 + r) - contDen a (j + 1) * contNum a (j + r) : ℤ) :
          ℝ) := rfl
    rw [e]
    refine h.trans (le_of_eq ?_)
    simp only [H, Qw, Qm]; field_simp
  · -- `|L₂| ≤ 3 H^{-ε/2}`
    have h := abs_spadeL2_le ha j r
    have e : formL2 α (spadeVec a j r) = α * ((contDen a j * contDen a (j + 1 + r) -
        contDen a (j + 1) * contDen a (j + r) : ℤ) : ℝ) -
        ((contDen a j * contNum a (j + 1 + r) - contDen a (j + 1) * contNum a (j + r) : ℤ) :
          ℝ) := rfl
    rw [e]
    refine h.trans ?_
    have hgr := contDen_mul_sqrt_two_pow_le ha (j + 1) (h := r) (by omega)
    have hs1 : (1 : ℝ) ≤ √2 := by rw [Real.one_le_sqrt]; norm_num
    have hs0 : (0 : ℝ) < √2 := by positivity
    set s := √2 ^ u
    have hs : s ^ 2 = 2 ^ u := by
      simp only [s]; rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
    have hsr : √2 * √2 ^ (r - 1) ≥ s := by
      simp only [s]
      calc √2 * √2 ^ (r - 1) = √2 ^ (r - 1 + 1) := by ring
        _ ≥ √2 ^ u := pow_le_pow_right₀ hs1 (by omega)
    set F := H ^ (ε / 2)
    have hF0 : 0 < F := Real.rpow_pos_of_pos hH0 _
    have hFE : F ^ 2 = E := by
      simp only [F, E]; rw [← Real.rpow_natCast, ← Real.rpow_mul hH0.le]; norm_num
    have hFs : F ≤ s := by
      have : F ^ 2 ≤ s ^ 2 := by rw [hFE, hs]; exact hEu
      exact (pow_le_pow_iff_left₀ hF0.le (by positivity) two_ne_zero).1 this
    have hneg : H ^ (-(ε / 2)) = 1 / F := by
      rw [Real.rpow_neg hH0.le]; simp [F]
    rw [hneg]
    have h22 : 2 * √2 ≤ 3 := by
      have : (2 * √2) ^ 2 = 8 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
      nlinarith [sq_nonneg (2 * √2 - 3)]
    -- `2 q_w / q_{w+r} ≤ 2 √2 / s ≤ 3 / F`
    have hpos : 0 < √2 ^ (r - 1) := by positivity
    rw [div_le_iff₀ hQm]
    calc 2 * Qw = 2 * √2 * (Qw * √2 ^ (r - 1)) / (√2 * √2 ^ (r - 1)) := by
          field_simp
      _ ≤ 2 * √2 * Qm / s := by
          gcongr
      _ ≤ 3 * Qm / F := by
          rw [div_le_div_iff₀ (by positivity) hF0]
          have : 2 * √2 * Qm * F ≤ 3 * Qm * s := by
            have := mul_le_mul h22 hFs hF0.le (by norm_num)
            nlinarith
          linarith
      _ = 3 * (1 / F) * Qm := by ring
  · -- the lower bound
    have h := le_abs_formL2 ha j r
    refine le_trans (le_of_eq ?_) h
    rw [div_eq_div_iff (by positivity) (by positivity)]
    simp only [H]; ring
  · -- (3.3)
    have h := abs_spadeL3_le ha j r
    have e : formL3 α (spadeVec a j r) = α * ((contDen a j * contDen a (j + 1 + r) -
        contDen a (j + 1) * contDen a (j + r) : ℤ) : ℝ) -
        ((contNum a j * contDen a (j + 1 + r) - contNum a (j + 1) * contDen a (j + r) : ℤ) :
          ℝ) := rfl
    rw [e]
    refine h.trans (le_of_eq ?_)
    simp only [H, Qw, Qm]; field_simp
  · -- the Claim
    intro z hz
    have hsum0 : 0 ≤ ∑ i, |z i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
    have hA2 : (1 : ℝ) ≤ (A + 1) ^ 2 := one_le_pow₀ (by linarith)
    have hsucc := contDen_succ_le ha hA
    rcases le_or_gt 2 j with hj | hj
    · have h := abs_claim_le ha hj (hne (by omega)) z hz
      have hqj := contDen_pos_real ha j
      have hQ : Qw ≤ (A + 1) * contDen a j := hsucc j
      have h3 : |z 1| + |z 2| + |z 3| ≤ ∑ i, |z i| := by
        rw [Fin.sum_univ_four]; linarith [abs_nonneg (z 0)]
      calc Qw * |z 0 + (z 1 + z 2) * α + z 3 * α ^ 2|
          ≤ ((A + 1) * contDen a j) * (12 * (|z 1| + |z 2| + |z 3|) / contDen a j) :=
            mul_le_mul hQ h (abs_nonneg _) (by positivity)
        _ = 12 * (A + 1) * (|z 1| + |z 2| + |z 3|) := by field_simp
        _ ≤ 12 * (A + 1) ^ 2 * ∑ i, |z i| := by
            have : (A + 1 : ℝ) ≤ (A + 1) ^ 2 := by nlinarith
            have : 0 ≤ |z 1| + |z 2| + |z 3| := by positivity
            nlinarith
    · -- `w ≤ 2`: `q_w ≤ (A + 1)²`
      have hQ : Qw ≤ (A + 1) ^ 2 :=
        (contDen_le_pow ha hA (j + 1)).trans (pow_le_pow_right₀ (by linarith) (by omega))
      have hΛ : |z 0 + (z 1 + z 2) * α + z 3 * α ^ 2| ≤ ∑ i, |z i| := by
        rw [Fin.sum_univ_four]
        have hαa : |α| ≤ 1 := by rw [abs_of_pos hα0]; linarith
        have hα2 : |α ^ 2| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hαa
        calc |z 0 + (z 1 + z 2) * α + z 3 * α ^ 2|
            ≤ |z 0 + (z 1 + z 2) * α| + |z 3 * α ^ 2| := abs_add_le _ _
          _ ≤ |z 0| + |(z 1 + z 2) * α| + |z 3 * α ^ 2| := by
              linarith [abs_add_le (z 0) ((z 1 + z 2) * α)]
          _ = |z 0| + |z 1 + z 2| * |α| + |z 3| * |α ^ 2| := by rw [abs_mul, abs_mul]
          _ ≤ |z 0| + (|z 1| + |z 2|) * 1 + |z 3| * 1 := by
              gcongr
              exact abs_add_le _ _
          _ = |z 0| + |z 1| + |z 2| + |z 3| := by ring
      calc Qw * |z 0 + (z 1 + z 2) * α + z 3 * α ^ 2| ≤ (A + 1) ^ 2 * ∑ i, |z i| :=
            mul_le_mul hQ hΛ (abs_nonneg _) (by positivity)
        _ ≤ 12 * (A + 1) ^ 2 * ∑ i, |z i| := by nlinarith

end Nat
