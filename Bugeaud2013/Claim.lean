/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Estimates
public import Bugeaud2013.Spade

-- Used only inside proofs.
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The Claim in the proof of Bugeaud 2013, Theorem 3.1

In the second case of the proof, the preperiods `w_n` tend to infinity and the repetition cannot
be slid to the left (`a_{w_n} ≠ a_{w_n + r_n}`). The **Claim** is that an integer relation
`x₁ A + x₂ B₂ + x₃ B₃ + x₄ C = 0` holding at the points `v_n` forces
`x₁ + (x₂ + x₃) α + x₄ α² = 0`.

The paper argues with `Q_n = q_{w-1} q_{w+r} / (q_w q_{w+r-1}) = 1 + A / (q_w q_{w+r-1})` and the
mirror formula. Here the same computation is done on the integer `A` itself:

* **rigidity** (`Nat.contDen_le_abs_spadeVec_zero`): `a_w ≠ a_{w+r}` gives `|A| ≥ q_{w+r-1}`
  (for `w ≥ 3`), which is the paper's `|Q_n - 1| ≫ a_w⁻¹ q_{w-1}⁻¹`;
* combined with the trivial case `Q_n ≥ 2`, `q_{w-1} q_{w+r} ≤ 2 q_w |A|`
  (`Nat.contDen_mul_le_two_mul_abs`);
* writing `p_ℓ = q_ℓ α - e_ℓ`, the relation reads `A (x₁ + (x₂ + x₃) α + x₄ α²) = -E` with
  `|E| ≤ 6 (|x₂| + |x₃| + |x₄|) q_{w+r} / q_w` by (2.2);
* hence `|x₁ + (x₂ + x₃) α + x₄ α²| ≤ 12 (|x₂| + |x₃| + |x₄|) / q_{w-1}` (`Nat.abs_claim_le`), which
  tends to `0` as `w → ∞`.

## Main results

* `Nat.abs_claim_le`: the estimate at one `n`.
* `Nat.eq_zero_of_frequently_abs_le_div`: a real number bounded by `L / f n` for infinitely many
  `n`, with `f n → ∞`, is `0`.
* `Nat.tendsto_contDen_comp`: `q_{f n} → ∞` when `f n → ∞`.
* `Nat.claim`: **the Claim**.
-/

@[expose] public section

open Filter

namespace Nat

/-- A real number with `|c| ≤ L / f n` for infinitely many `n`, where `f n → ∞`, is `0`. -/
theorem eq_zero_of_frequently_abs_le_div {c L : ℝ} {f : ℕ → ℝ} (hf : Tendsto f atTop atTop)
    (h : ∃ᶠ n in atTop, |c| ≤ L / f n) : c = 0 := by
  by_contra hc
  have hc' : 0 < |c| := abs_pos.2 hc
  obtain ⟨n, hn, hfn⟩ := (h.and_eventually
    (hf.eventually_gt_atTop (max (L / |c|) 0))).exists
  have hf0 : 0 < f n := lt_of_le_of_lt (le_max_right _ _) hfn
  have hL : L / |c| < f n := lt_of_le_of_lt (le_max_left _ _) hfn
  rw [div_lt_iff₀ hc'] at hL
  rw [le_div_iff₀ hf0] at hn
  linarith [mul_comm (f n) |c|]

variable {a : ℕ → ℕ}

section Positive

variable (ha : ∀ n, 1 ≤ a (n + 1))
include ha

/-- **Rigidity.** If `a_w ≠ a_{w+r}` with `w = j + 1 ≥ 3`, then `|A| ≥ q_{w+r-1}`. -/
theorem contDen_le_abs_spadeVec_zero {j r : ℕ} (hj : 2 ≤ j)
    (hne : a (j + 1) ≠ a (j + 1 + r)) :
    (contDen a (j + r) : ℝ) ≤ |(spadeVec a j r 0 : ℝ)| := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have e1 : contDen a (k + 1 + 1) = a (k + 2) * contDen a (k + 1) + contDen a k :=
    contDen_add_two a k
  have e2 : contDen a (k + 1 + 1 + r) =
      a (k + 2 + r) * contDen a (k + 1 + r) + contDen a (k + r) := by
    rw [show k + 1 + 1 + r = k + r + 2 by ring, contDen_add_two,
      show k + r + 2 = k + 2 + r by ring, show k + r + 1 = k + 1 + r by ring]
  have hlt : contDen a k < contDen a (k + 1) := contDen_lt_contDen_succ ha (by omega)
  have hle : contDen a (k + r) ≤ contDen a (k + 1 + r) := by
    rw [show k + 1 + r = k + r + 1 by ring]; exact contDen_le_contDen_succ ha _
  have hk1 : 1 ≤ contDen a k := one_le_contDen ha k
  rw [spadeVec_zero]
  push_cast
  rw [e1, e2, show k + 1 + r = k + r + 1 by ring] at *
  rw [show k + r + 1 = k + 1 + r by ring]
  set Qk : ℝ := (contDen a k : ℝ)
  set Q1 : ℝ := (contDen a (k + 1) : ℝ)
  set R0 : ℝ := (contDen a (k + r) : ℝ)
  set R1 : ℝ := (contDen a (k + 1 + r) : ℝ)
  have hQ : Qk + 1 ≤ Q1 := by simp only [Qk, Q1]; exact_mod_cast hlt
  have hR : R0 ≤ R1 := by
    simp only [R0, R1]; rw [show k + 1 + r = k + r + 1 by ring]; exact_mod_cast hle
  have hQk : 1 ≤ Qk := by simp only [Qk]; exact_mod_cast hk1
  have hR0 : 0 ≤ R0 := Nat.cast_nonneg _
  push_cast
  have key : Q1 * ((a (k + 2 + r) : ℝ) * R1 + R0) - ((a (k + 2) : ℝ) * Q1 + Qk) * R1 =
      ((a (k + 2 + r) : ℝ) - a (k + 2)) * Q1 * R1 + Q1 * R0 - Qk * R1 := by ring
  rw [key]
  rcases Nat.lt_or_gt_of_ne (show a (k + 2) ≠ a (k + 2 + r) from hne) with h | h
  · have h' : (a (k + 2) : ℝ) + 1 ≤ a (k + 2 + r) := by exact_mod_cast h
    have : Q1 * R1 ≤ ((a (k + 2 + r) : ℝ) - a (k + 2)) * Q1 * R1 := by
      have : 0 ≤ Q1 * R1 := by positivity
      nlinarith
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith
  · have h' : (a (k + 2 + r) : ℝ) + 1 ≤ a (k + 2) := by exact_mod_cast h
    have : ((a (k + 2 + r) : ℝ) - a (k + 2)) * Q1 * R1 ≤ -(Q1 * R1) := by
      have : 0 ≤ Q1 * R1 := by positivity
      nlinarith
    rw [abs_of_nonpos (by nlinarith)]
    nlinarith

/-- `q_{w-1} q_{w+r} ≤ 2 q_w |A|` when `a_w ≠ a_{w+r}`, `w = j + 1 ≥ 3`. -/
theorem contDen_mul_le_two_mul_abs {j r : ℕ} (hj : 2 ≤ j)
    (hne : a (j + 1) ≠ a (j + 1 + r)) :
    (contDen a j : ℝ) * contDen a (j + 1 + r) ≤
      2 * contDen a (j + 1) * |(spadeVec a j r 0 : ℝ)| := by
  have hrig := contDen_le_abs_spadeVec_zero ha hj hne
  have q1 : (1 : ℝ) ≤ contDen a (j + 1) := by exact_mod_cast one_le_contDen ha (j + 1)
  have hA : (spadeVec a j r 0 : ℝ) = (contDen a j : ℝ) * contDen a (j + 1 + r) -
      contDen a (j + 1) * contDen a (j + r) := by rw [spadeVec_zero]; push_cast; ring
  by_cases hQ : 2 * ((contDen a (j + 1) : ℝ) * contDen a (j + r)) ≤
      (contDen a j : ℝ) * contDen a (j + 1 + r)
  · have hpos : (contDen a j : ℝ) * contDen a (j + 1 + r) ≤ 2 * (spadeVec a j r 0 : ℝ) := by
      rw [hA]; linarith
    have : (spadeVec a j r 0 : ℝ) ≤ |(spadeVec a j r 0 : ℝ)| := le_abs_self _
    have : 0 ≤ |(spadeVec a j r 0 : ℝ)| := abs_nonneg _
    nlinarith
  · push Not at hQ
    have : (contDen a (j + 1) : ℝ) * contDen a (j + r) ≤
        contDen a (j + 1) * |(spadeVec a j r 0 : ℝ)| :=
      mul_le_mul_of_nonneg_left hrig (by positivity)
    linarith

/-- **The estimate of the Claim at one `n`**: if `∑ x_i (v_n)_i = 0`, `w = j + 1 ≥ 3` and
`a_w ≠ a_{w+r}`, then `|x₁ + (x₂ + x₃) α + x₄ α²| ≤ 12 (|x₂| + |x₃| + |x₄|) / q_{w-1}`. -/
theorem abs_claim_le {j r : ℕ} (hj : 2 ≤ j) (hne : a (j + 1) ≠ a (j + 1 + r))
    (x : Fin 4 → ℝ) (hrel : ∑ i, x i * (spadeVec a j r i : ℝ) = 0) :
    |x 0 + (x 1 + x 2) * contFrac a + x 3 * contFrac a ^ 2| ≤
      12 * (|x 1| + |x 2| + |x 3|) / contDen a j := by
  set α := contFrac a
  set S := x 0 + (x 1 + x 2) * α + x 3 * α ^ 2
  set A : ℝ := (spadeVec a j r 0 : ℝ)
  -- the errors `e_ℓ = q_ℓ α - p_ℓ`
  set e : ℕ → ℝ := fun ℓ ↦ (contDen a ℓ : ℝ) * α - contNum a ℓ with he
  have he_le (ℓ : ℕ) : |e ℓ| ≤ 1 / contDen a (ℓ + 1) := abs_contDen_mul_contFrac_sub_le ha ℓ
  have he1 (ℓ : ℕ) : |e ℓ| ≤ 1 := by
    refine (he_le ℓ).trans ?_
    rw [div_le_one (contDen_pos_real ha _)]
    exact_mod_cast one_le_contDen ha (ℓ + 1)
  set Qj : ℝ := (contDen a j : ℝ)
  set Q1 : ℝ := (contDen a (j + 1) : ℝ)
  set R0 : ℝ := (contDen a (j + r) : ℝ)
  set R1 : ℝ := (contDen a (j + 1 + r) : ℝ)
  have qj := contDen_pos_real ha j
  have q1 := contDen_pos_real ha (j + 1)
  have r1 := contDen_pos_real ha (j + 1 + r)
  have hjr1 : Q1 ≤ R1 := contDen_mono_real ha (by omega)
  have hjj1 : Qj ≤ Q1 := contDen_mono_real ha (by omega)
  set ρ := R1 / Q1
  have hρ : 1 ≤ ρ := (one_le_div q1).2 hjr1
  have hα0 : 0 < α := contFrac_pos ha
  have hα1 : α < 1 := contFrac_lt_one ha
  have hαabs : |α| ≤ 1 := by rw [abs_of_pos hα0]; exact hα1.le
  -- `|q_m e_ℓ| ≤ q_m / q_{ℓ+1}`
  have hT (m ℓ : ℕ) : |(contDen a m : ℝ) * e ℓ| ≤ contDen a m / contDen a (ℓ + 1) := by
    rw [abs_mul, Nat.abs_cast, ← mul_one_div]
    exact mul_le_mul_of_nonneg_left (he_le ℓ) (Nat.cast_nonneg _)
  have hT1 (m ℓ : ℕ) (h : m ≤ ℓ + 1) : |(contDen a m : ℝ) * e ℓ| ≤ ρ := by
    refine (hT m ℓ).trans (le_trans ?_ hρ)
    rw [div_le_one (contDen_pos_real ha _)]
    exact contDen_mono_real ha h
  set T1 := Qj * e (j + 1 + r)
  set T2 := Q1 * e (j + r)
  set T3 := R1 * e j
  set T4 := R0 * e (j + 1)
  set T5 := e j * e (j + 1 + r)
  set T6 := e (j + 1) * e (j + r)
  have bT1 : |T1| ≤ ρ := hT1 _ _ (by omega)
  have bT2 : |T2| ≤ ρ := hT1 _ _ (by omega)
  have bT3 : |T3| ≤ ρ := hT _ _
  have bT4 : |T4| ≤ ρ := (hT _ _).trans (div_le_div₀ r1.le (contDen_mono_real ha (by omega)) q1
    (contDen_mono_real ha (by omega)))
  have bT5 : |T5| ≤ ρ := by
    rw [abs_mul]; nlinarith [he1 j, he1 (j + 1 + r), abs_nonneg (e j), abs_nonneg (e (j + 1 + r))]
  have bT6 : |T6| ≤ ρ := by
    rw [abs_mul]; nlinarith [he1 (j + 1), he1 (j + r), abs_nonneg (e (j + 1)),
      abs_nonneg (e (j + r))]
  set D1 := -T1 + T2
  set D2 := -T3 + T4
  set D3 := -α * (T1 + T3 - T2 - T4) + T5 - T6
  have bD1 : |D1| ≤ 2 * ρ := by
    refine (abs_add_le _ _).trans ?_; rw [abs_neg]; linarith
  have bD2 : |D2| ≤ 2 * ρ := by
    refine (abs_add_le _ _).trans ?_; rw [abs_neg]; linarith
  have bD3 : |D3| ≤ 6 * ρ := by
    have h4 : |T1 + T3 - T2 - T4| ≤ 4 * ρ := by
      refine (abs_sub _ _).trans ?_
      have := abs_sub (T1 + T3) T2
      have := abs_add_le T1 T3
      linarith
    have h5 : |-α * (T1 + T3 - T2 - T4)| ≤ 4 * ρ := by
      rw [abs_mul, abs_neg]
      calc |α| * |T1 + T3 - T2 - T4| ≤ 1 * (4 * ρ) :=
            mul_le_mul hαabs h4 (abs_nonneg _) zero_le_one
        _ = 4 * ρ := one_mul _
    refine (abs_sub _ _).trans ?_
    have := (abs_add_le (-α * (T1 + T3 - T2 - T4)) T5)
    linarith
  -- the relation is `A S + E = 0`
  have hrel' : A * S + (x 1 * D1 + x 2 * D2 + x 3 * D3) = 0 := by
    rw [← hrel, Fin.sum_univ_four]
    simp only [A, S, D1, D2, D3, T1, T2, T3, T4, T5, T6, Qj, Q1, R0, R1, he, spadeVec_zero,
      spadeVec_one, spadeVec_two, spadeVec_three]
    push_cast
    ring
  have hE : |x 1 * D1 + x 2 * D2 + x 3 * D3| ≤ 6 * ρ * (|x 1| + |x 2| + |x 3|) := by
    have e1 := (abs_add_le (x 1 * D1 + x 2 * D2) (x 3 * D3))
    have e2 := (abs_add_le (x 1 * D1) (x 2 * D2))
    rw [abs_mul, abs_mul] at e2
    rw [abs_mul] at e1
    have m1 : |x 1| * |D1| ≤ |x 1| * (2 * ρ) := mul_le_mul_of_nonneg_left bD1 (abs_nonneg _)
    have m2 : |x 2| * |D2| ≤ |x 2| * (2 * ρ) := mul_le_mul_of_nonneg_left bD2 (abs_nonneg _)
    have m3 : |x 3| * |D3| ≤ |x 3| * (6 * ρ) := mul_le_mul_of_nonneg_left bD3 (abs_nonneg _)
    nlinarith [abs_nonneg (x 1), abs_nonneg (x 2), abs_nonneg (x 3)]
  have hAS : |A| * |S| ≤ 6 * ρ * (|x 1| + |x 2| + |x 3|) := by
    rw [← abs_mul, show A * S = -(x 1 * D1 + x 2 * D2 + x 3 * D3) by linarith, abs_neg]
    exact hE
  -- `ρ ≤ 2 |A| / q_{w-1}`
  have hmain := contDen_mul_le_two_mul_abs ha hj hne
  have hA0 : 0 < |A| := by
    have := contDen_le_abs_spadeVec_zero ha hj hne
    have : (0 : ℝ) < contDen a (j + r) := contDen_pos_real ha _
    linarith
  have hρA : ρ * Qj ≤ 2 * |A| := by
    simp only [ρ]
    rw [div_mul_eq_mul_div, div_le_iff₀ q1]
    linarith
  set X := |x 1| + |x 2| + |x 3|
  have hX : 0 ≤ X := by positivity
  rw [le_div_iff₀ qj]
  -- `|A| |S| q_{w-1} ≤ 6 ρ X q_{w-1} ≤ 12 |A| X`
  have h1 : |A| * (|S| * Qj) ≤ |A| * (12 * X) := by
    calc |A| * (|S| * Qj) = (|A| * |S|) * Qj := by ring
      _ ≤ (6 * ρ * X) * Qj := mul_le_mul_of_nonneg_right hAS qj.le
      _ = 6 * X * (ρ * Qj) := by ring
      _ ≤ 6 * X * (2 * |A|) := mul_le_mul_of_nonneg_left hρA (by positivity)
      _ = |A| * (12 * X) := by ring
  exact le_of_mul_le_mul_left h1 hA0

/-- `q_{f n} → ∞` when `f n → ∞`. -/
theorem tendsto_contDen_comp {f : ℕ → ℕ} (hf : Tendsto f atTop atTop) :
    Tendsto (fun n ↦ (contDen a (f n) : ℝ)) atTop atTop :=
  tendsto_atTop_mono
    (fun n ↦ by simp only [Function.comp_apply]; exact_mod_cast le_contDen ha (f n))
    (tendsto_natCast_atTop_atTop.comp hf)

/-- **The Claim** (Bugeaud 2013, p. 1014). Along normalized lengths with `w_n → ∞`, a relation
`x₁ A + x₂ B₂ + x₃ B₃ + x₄ C = 0` holding at `v_n` for infinitely many `n` forces
`x₁ + (x₂ + x₃) α + x₄ α² = 0`. -/
theorem claim {w u v : ℕ → ℕ} {C : ℕ} (hd : SpadeData a w u v C) (hw : Tendsto w atTop atTop)
    {x : Fin 4 → ℝ}
    (hrel : ∃ᶠ n in atTop, ∑ i, x i * (spadeVec a (w n - 1) (u n + v n) i : ℝ) = 0) :
    x 0 + (x 1 + x 2) * contFrac a + x 3 * contFrac a ^ 2 = 0 := by
  refine eq_zero_of_frequently_abs_le_div (L := 12 * (|x 1| + |x 2| + |x 3|))
    (tendsto_contDen_comp ha ((tendsto_sub_atTop_nat 1).comp hw)) ?_
  refine (hrel.and_eventually (hw.eventually_ge_atTop 3)).mono fun n ⟨h, hw3⟩ ↦ ?_
  have hne := hd.ne n (by omega)
  rw [show w n = w n - 1 + 1 by omega] at hne
  exact abs_claim_le ha (j := w n - 1) (by omega) hne x h

end Positive

end Nat
