/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Stephan2026a.QuantitativePlanes

-- Used only inside proofs.
import DiophantineApproximation.DoublingSequences
import Stephan2026a.SubspaceStep

/-!
# Few kernel points on one plane

**Problem 5.2, step 3.** The kernel points of a doubling sequence of pairs that lie on one plane
`w₀ X₀ + w₁ X₁ + w₂ X₂ = 0` are few: `O(1 + log ε⁻¹)`, uniformly in the plane. Everything here is
integer arithmetic with absolute constants; no approximation property of the points is used,
only `|N| < 2^c` and that `N` is odd.

* If `w₂ = 0`, then `w₀ 3^s + w₁ 2^s = 0`, so the gap `s = s₀` is constant on the plane. A point
  with a large gap `ε c / 4 < s₀` has `c < 4 s₀ / ε`, so the points lie in a window
  `τ ≤ (4/ε) τ₁` of the doubling sequence: `O(log ε⁻¹)` of them.
* If `w₂ ≠ 0`, eliminating `X₂` gives `N = β₁ 3^c + β₂ 2^s 3^a` with constant `β₁, β₂ ∈ ℚ`.
  * **Same gap** (`SteeringWord.seven_mul_lt_of_same_gap`): two points with the same gap have
    `N₂ 3^{a₁} = N₁ 3^{a₂}`, so `3^{c₂ - c₁} ≤ |N₂| < 2^{c₂}`, and `2^19 < 3^12` gives
    `7 c₂ < 19 c₁`.
  * **Distinct gaps** (`SteeringWord.lt_of_ne_gap`): two points with different gaps determine
    `β₁, β₂`, and a third point satisfies `N D = 3^a (3^s n₁ - 2^s n₂)` with `D, n₁ ≠ 0` by
    parity at `2`. A three-term `S`-unit estimate (`SteeringWord.three_pow_le_of_ne_zero`) then
    gives `3^c ≤ 250 · 648^{c₁ + c₂} 2^c`, so `c < 18 (c₁ + c₂) + 18`.

  So the points with the gap of the first point lie in a window of ratio `8` at the first point,
  and the others in a window of ratio `128` at the first point with another gap.

## Main results

* `SteeringWord.seven_mul_lt_of_same_gap`: **the same-gap principle**.
* `SteeringWord.lt_of_ne_gap`: **the distinct-gap principle**.
* `SteeringWord.card_mem_plane_le`: **at most `12 (1 + log ε⁻¹)` points on a plane**.

## References

R. Stephan, *Superlinear complexity of the `(3/2)^n` steering word*, arXiv:2607.11648, Problem 5.2;
Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250, §7.
-/

@[expose] public section

open Finset Real

namespace SteeringWord

/-- **Parity at `2`**: `2^i u ≠ 2^j v` for odd `u, v` and `i < j`. -/
theorem two_pow_mul_ne {i j : ℕ} {u v : ℤ} (hu : Odd u) (hij : i < j) :
    2 ^ i * u ≠ 2 ^ j * v := by
  intro h
  have hj : (2 : ℤ) ^ j = 2 ^ i * (2 * 2 ^ (j - i - 1)) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  have h' : 2 ^ i * u = 2 ^ i * (2 * (2 ^ (j - i - 1) * v)) := by rw [h, hj]; ring
  have := mul_left_cancel₀ (by positivity) h'
  rw [this] at hu
  exact (Int.not_even_iff_odd.mpr hu) (even_two_mul _)

/-- **Parity at `2`**: `2^i u ≠ 2^j v` for odd `u, v` and `i ≠ j`. -/
theorem two_pow_mul_ne_of_ne {i j : ℕ} {u v : ℤ} (hu : Odd u) (hv : Odd v) (hij : i ≠ j) :
    2 ^ i * u ≠ 2 ^ j * v := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact two_pow_mul_ne hu h
  · exact fun e ↦ two_pow_mul_ne hv h e.symm

/-- **The same-gap principle.** Two kernel points with the same gap `s` on the plane
`N = β₁ 3^c + β₂ 2^s 3^a` have `7 c₂ < 19 c₁`: they satisfy `N₂ 3^{a₁} = N₁ 3^{a₂}`, so
`3^{c₂ - c₁} ≤ |N₂| < 2^{c₂}`, against `2^19 < 3^12` when `7 c₂ ≥ 19 c₁`. -/
theorem seven_mul_lt_of_same_gap {β₁ β₂ : ℚ} {a₁ c₁ a₂ c₂ : ℕ} (h₁ : a₁ < c₁) (h₂ : a₂ < c₂)
    (hs : c₁ - a₁ = c₂ - a₂)
    (hp₁ : (kernelNum a₁ c₁ : ℚ) = β₁ * 3 ^ c₁ + β₂ * (2 ^ (c₁ - a₁) * 3 ^ a₁))
    (hp₂ : (kernelNum a₂ c₂ : ℚ) = β₁ * 3 ^ c₂ + β₂ * (2 ^ (c₂ - a₂) * 3 ^ a₂)) :
    7 * c₂ < 19 * c₁ := by
  rcases le_or_gt a₂ a₁ with ha | ha
  · omega
  obtain ⟨d, rfl⟩ : ∃ d, a₂ = a₁ + d := ⟨a₂ - a₁, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, c₁ = a₁ + s := ⟨c₁ - a₁, by omega⟩
  obtain rfl : c₂ = a₁ + d + s := by omega
  rw [show a₁ + s - a₁ = s by omega] at hp₁
  rw [show a₁ + d + s - (a₁ + d) = s by omega] at hp₂
  -- `N₂ = N₁ 3^d`
  have hq : (kernelNum (a₁ + d) (a₁ + d + s) : ℚ) = kernelNum a₁ (a₁ + s) * 3 ^ d := by
    rw [hp₁, hp₂]
    ring
  have hz : kernelNum (a₁ + d) (a₁ + d + s) = kernelNum a₁ (a₁ + s) * 3 ^ d := by
    exact_mod_cast hq
  have hN₁ : kernelNum a₁ (a₁ + s) ≠ 0 := fun e ↦ by
    have := odd_kernelNum h₁
    rw [e] at this
    exact (Int.not_even_iff_odd.mpr this) ⟨0, rfl⟩
  have hlt := abs_kernelNum_lt h₂.le
  rw [hz, abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 3 ^ d)] at hlt
  have h1 : (1 : ℤ) ≤ |kernelNum a₁ (a₁ + s)| := Int.one_le_abs hN₁
  have h3 : (3 : ℤ) ^ d < 2 ^ (a₁ + d + s) := by
    nlinarith [pow_pos (by norm_num : (0 : ℤ) < 3) d]
  have h3' : 3 ^ d < 2 ^ (a₁ + d + s) := by exact_mod_cast h3
  by_contra hcon
  have e1 : 3 ^ (12 * (a₁ + d + s)) ≤ 3 ^ (19 * d) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e2 : 3 ^ (19 * d) < 2 ^ (19 * (a₁ + d + s)) := by
    rw [pow_mul', pow_mul' 2]
    exact Nat.pow_lt_pow_left h3' (by norm_num)
  have e3 : 2 ^ (19 * (a₁ + d + s)) ≤ 3 ^ (12 * (a₁ + d + s)) := by
    rw [pow_mul, pow_mul 3]
    exact Nat.pow_le_pow_left (by norm_num) _
  exact lt_irrefl _ ((e1.trans_lt e2).trans_le e3)

/-- **A three-term `S`-unit estimate.** If `n₁ ≠ 0`, `|n₂| ≤ m` and `z = 3^s n₁ - 2^s n₂ ≠ 0`,
then `3^s ≤ 2 (2m + 1)^3 |z|`: either `2^{s+1} m ≤ 3^s` and `|z| ≥ 3^s / 2`, or
`(3/2)^s < 2m + 1`, and then `3^s ≤ (27/8)^s < (2m + 1)^3`. -/
theorem three_pow_le_of_ne_zero {s : ℕ} {n₁ n₂ m : ℤ} (hn₁ : n₁ ≠ 0)
    (hz : 3 ^ s * n₁ - 2 ^ s * n₂ ≠ 0) (hm : |n₂| ≤ m) :
    (3 : ℤ) ^ s ≤ 2 * (2 * m + 1) ^ 3 * |3 ^ s * n₁ - 2 ^ s * n₂| := by
  have hm0 : 0 ≤ m := (abs_nonneg _).trans hm
  have hz1 : 1 ≤ |3 ^ s * n₁ - 2 ^ s * n₂| := Int.one_le_abs hz
  have hcube : 1 ≤ (2 * m + 1) ^ 3 := one_le_pow₀ (by linarith)
  have h3 : (0 : ℤ) < 3 ^ s := by positivity
  have h2 : (0 : ℤ) < 2 ^ s := by positivity
  rcases le_or_gt (2 * 2 ^ s * m) (3 ^ s) with hA | hB
  · have habs : |3 ^ s * n₁| - |2 ^ s * n₂| ≤ |3 ^ s * n₁ - 2 ^ s * n₂| :=
      abs_sub_abs_le_abs_sub _ _
    rw [abs_mul, abs_mul, abs_of_pos h3, abs_of_pos h2] at habs
    have hn : 1 ≤ |n₁| := Int.one_le_abs hn₁
    have : 3 ^ s ≤ 2 * |3 ^ s * n₁ - 2 ^ s * n₂| := by nlinarith
    nlinarith
  · have hB' : (3 : ℤ) ^ s < (2 * m + 1) * 2 ^ s := by nlinarith
    have hc : ((3 : ℤ) ^ s) ^ 3 < ((2 * m + 1) * 2 ^ s) ^ 3 :=
      pow_lt_pow_left₀ hB' h3.le (by norm_num)
    have e1 : (3 : ℤ) ^ s * 8 ^ s ≤ (3 ^ s) ^ 3 := by
      rw [← mul_pow, ← pow_mul, mul_comm s 3, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) s
    have e2 : ((2 * m + 1) * 2 ^ s) ^ 3 = (2 * m + 1) ^ 3 * 8 ^ s := by
      rw [mul_pow, ← pow_mul, mul_comm s 3, pow_mul]
      norm_num
    have h8 : (0 : ℤ) < 8 ^ s := by positivity
    have : (3 : ℤ) ^ s < (2 * m + 1) ^ 3 :=
      lt_of_mul_lt_mul_right (lt_of_le_of_lt e1 (hc.trans_eq e2)) h8.le
    nlinarith

/-- **The distinct-gap principle.** If two kernel points with different gaps lie on the plane
`N = β₁ 3^c + β₂ 2^s 3^a`, every kernel point on it has `c < 18 (c₁ + c₂) + 18`. The two points
determine `β₁, β₂`, and a third point satisfies `N D = 3^a (3^s n₁ - 2^s n₂)` with
`D = X₁ Y₂ - X₂ Y₁`, `n₁ = N₁ Y₂ - N₂ Y₁`, `n₂ = N₁ X₂ - N₂ X₁` (`X = 3^c`, `Y = 2^s 3^a`);
`D` and `n₁` are nonzero by parity at `2`, and the three-term estimate gives
`3^c ≤ 250 · 648^{c₁ + c₂} 2^c`. -/
theorem lt_of_ne_gap {β₁ β₂ : ℚ} {a₁ c₁ a₂ c₂ a c : ℕ} (h₁ : a₁ < c₁) (h₂ : a₂ < c₂)
    (h : a < c) (hs : c₁ - a₁ ≠ c₂ - a₂)
    (hp₁ : (kernelNum a₁ c₁ : ℚ) = β₁ * 3 ^ c₁ + β₂ * (2 ^ (c₁ - a₁) * 3 ^ a₁))
    (hp₂ : (kernelNum a₂ c₂ : ℚ) = β₁ * 3 ^ c₂ + β₂ * (2 ^ (c₂ - a₂) * 3 ^ a₂))
    (hp : (kernelNum a c : ℚ) = β₁ * 3 ^ c + β₂ * (2 ^ (c - a) * 3 ^ a)) :
    c < 18 * (c₁ + c₂) + 18 := by
  set s₁ := c₁ - a₁ with hs₁
  set s₂ := c₂ - a₂ with hs₂
  set s := c - a with hsdef
  set N₁ := kernelNum a₁ c₁ with hN₁def
  set N₂ := kernelNum a₂ c₂ with hN₂def
  set N := kernelNum a c with hNdef
  set X₁ : ℤ := 3 ^ c₁ with hX₁
  set X₂ : ℤ := 3 ^ c₂ with hX₂
  set Y₁ : ℤ := 2 ^ s₁ * 3 ^ a₁ with hY₁
  set Y₂ : ℤ := 2 ^ s₂ * 3 ^ a₂ with hY₂
  set D := X₁ * Y₂ - X₂ * Y₁ with hD
  set n₁ := N₁ * Y₂ - N₂ * Y₁ with hn₁
  set n₂ := N₁ * X₂ - N₂ * X₁ with hn₂
  -- the elimination of `β₁, β₂`
  have hkeyQ : (N : ℚ) * D = n₁ * 3 ^ c - n₂ * (2 ^ s * 3 ^ a) := by
    simp only [hD, hn₁, hn₂, hX₁, hX₂, hY₁, hY₂]
    push_cast
    linear_combination ((3 : ℚ) ^ c₁ * (2 ^ s₂ * 3 ^ a₂) - 3 ^ c₂ * (2 ^ s₁ * 3 ^ a₁)) * hp
      - (3 : ℚ) ^ c * ((2 ^ s₂ * 3 ^ a₂) * hp₁ - (2 ^ s₁ * 3 ^ a₁) * hp₂)
      + (2 ^ s * 3 ^ a : ℚ) * (3 ^ c₂ * hp₁ - 3 ^ c₁ * hp₂)
  have hkey : N * D = n₁ * 3 ^ c - n₂ * (2 ^ s * 3 ^ a) := by exact_mod_cast hkeyQ
  have hc : (3 : ℤ) ^ c = 3 ^ s * 3 ^ a := by rw [← pow_add, hsdef, Nat.sub_add_cancel h.le]
  have hkey' : N * D = 3 ^ a * (3 ^ s * n₁ - 2 ^ s * n₂) := by rw [hkey, hc]; ring
  -- `N`, `D`, `n₁` are nonzero
  have hodd : ∀ {a c : ℕ}, a < c → kernelNum a c ≠ 0 := fun hac e ↦ by
    have := odd_kernelNum hac
    rw [e] at this
    exact (Int.not_even_iff_odd.mpr this) ⟨0, rfl⟩
  have h3odd : ∀ k : ℕ, Odd ((3 : ℤ) ^ k) := fun k ↦ Odd.pow ⟨1, by norm_num⟩
  have hD0 : D ≠ 0 := by
    rw [hD, sub_ne_zero]
    have := two_pow_mul_ne_of_ne (h3odd (c₁ + a₂)) (h3odd (c₂ + a₁)) (Ne.symm hs)
    intro e
    apply this
    rw [hX₁, hX₂, hY₁, hY₂] at e
    rw [pow_add, pow_add]
    linear_combination e
  have hn₁0 : n₁ ≠ 0 := by
    rw [hn₁, sub_ne_zero]
    have := two_pow_mul_ne_of_ne ((odd_kernelNum h₁).mul (h3odd a₂))
      ((odd_kernelNum h₂).mul (h3odd a₁)) (Ne.symm hs)
    intro e
    apply this
    rw [hY₁, hY₂] at e
    linear_combination e
  have hz : 3 ^ s * n₁ - 2 ^ s * n₂ ≠ 0 := by
    intro e
    rw [e, mul_zero] at hkey'
    exact mul_ne_zero (hodd h) hD0 hkey'
  -- the sizes
  set C := c₁ + c₂ with hC
  have hb₁ := two_pow_le_two_pow_sub_mul_three_pow h₁.le
  have hb₂ := two_pow_le_two_pow_sub_mul_three_pow h₂.le
  have hN₁ := abs_kernelNum_lt h₁.le
  have hN₂ := abs_kernelNum_lt h₂.le
  have hN := abs_kernelNum_lt h.le
  have h3C : (3 : ℤ) ^ C = 3 ^ c₁ * 3 ^ c₂ := pow_add _ _ _
  have hDle : |D| ≤ 3 ^ C := by
    have hp1 : 0 < X₁ * Y₂ := by positivity
    have hp2 : 0 < X₂ * Y₁ := by positivity
    have hq1 : X₁ * Y₂ ≤ 3 ^ C := by
      rw [h3C]; exact mul_le_mul_of_nonneg_left hb₂.2 (by positivity)
    have hq2 : X₂ * Y₁ ≤ 3 ^ C := by
      rw [h3C, mul_comm ((3 : ℤ) ^ c₁)]; exact mul_le_mul_of_nonneg_left hb₁.2 (by positivity)
    rw [abs_le]
    constructor <;> linarith
  have h6 : ∀ i j : ℕ, (2 : ℤ) ^ i * 3 ^ j ≤ 6 ^ (i + j) := fun i j ↦ by
    rw [pow_add]
    exact mul_le_mul (pow_le_pow_left₀ (by norm_num) (by norm_num) i)
      (pow_le_pow_left₀ (by norm_num) (by norm_num) j) (by positivity) (by positivity)
  have hn₂le : |n₂| ≤ 2 * 6 ^ C := by
    have e1 : |N₁ * X₂| ≤ 6 ^ C := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < X₂)]
      exact (mul_le_mul_of_nonneg_right hN₁.le (by positivity)).trans (h6 c₁ c₂)
    have e2 : |N₂ * X₁| ≤ 6 ^ C := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < X₁), hC, add_comm]
      exact (mul_le_mul_of_nonneg_right hN₂.le (by positivity)).trans (h6 c₂ c₁)
    calc |n₂| ≤ |N₁ * X₂| + |N₂ * X₁| := abs_sub _ _
      _ ≤ 2 * 6 ^ C := by linarith
  have hest := three_pow_le_of_ne_zero hn₁0 hz hn₂le
  -- `3^c < 250 · 648^C 2^c`
  have hm : 2 * (2 * 6 ^ C) + 1 ≤ (5 : ℤ) * 6 ^ C := by
    have : (1 : ℤ) ≤ 6 ^ C := one_le_pow₀ (by norm_num)
    linarith
  have hcube : (2 * (2 * 6 ^ C) + 1) ^ 3 ≤ (125 : ℤ) * 216 ^ C := by
    calc (2 * (2 * 6 ^ C) + 1) ^ 3 ≤ ((5 : ℤ) * 6 ^ C) ^ 3 :=
          pow_le_pow_left₀ (by positivity) hm 3
      _ = 125 * 216 ^ C := by rw [mul_pow, ← pow_mul, mul_comm C 3, pow_mul]; norm_num
  have hbig : (3 : ℤ) ^ c < 250 * 648 ^ C * 2 ^ c := by
    have hND : |N * D| = 3 ^ a * |3 ^ s * n₁ - 2 ^ s * n₂| := by
      rw [hkey', abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 3 ^ a)]
    have hND' : |N * D| < 2 ^ c * 3 ^ C := by
      rw [abs_mul]
      have : 0 ≤ |D| := abs_nonneg _
      calc |N| * |D| ≤ |N| * 3 ^ C := mul_le_mul_of_nonneg_left hDle (abs_nonneg _)
        _ < 2 ^ c * 3 ^ C := mul_lt_mul_of_pos_right hN (by positivity)
    have e648 : (250 : ℤ) * 648 ^ C = 2 * (125 * 216 ^ C) * 3 ^ C := by
      rw [show (648 : ℤ) = 216 * 3 by norm_num, mul_pow]; ring
    calc (3 : ℤ) ^ c = 3 ^ s * 3 ^ a := hc
      _ ≤ 2 * (2 * (2 * 6 ^ C) + 1) ^ 3 * |3 ^ s * n₁ - 2 ^ s * n₂| * 3 ^ a :=
          mul_le_mul_of_nonneg_right hest (by positivity)
      _ = 2 * (2 * (2 * 6 ^ C) + 1) ^ 3 * |N * D| := by rw [hND]; ring
      _ ≤ 2 * (125 * 216 ^ C) * |N * D| := by
          gcongr
      _ < 2 * (125 * 216 ^ C) * (2 ^ c * 3 ^ C) :=
          mul_lt_mul_of_pos_left hND' (by positivity)
      _ = 250 * 648 ^ C * 2 ^ c := by rw [e648]; ring
  -- `c ≥ 18 C + 18` contradicts `3^18 ≥ 648 · 2^18` and `3^18 ≥ 250 · 2^18`
  by_contra hcon
  obtain ⟨r, hr⟩ : ∃ r, c = 18 * C + 18 + r := ⟨c - (18 * C + 18), by omega⟩
  have hbig' : (3 : ℕ) ^ c < 250 * 648 ^ C * 2 ^ c := by exact_mod_cast hbig
  have e1 : 250 * 648 ^ C * 2 ^ c ≤ 3 ^ c := by
    have h2c : 2 ^ c = (2 ^ 18) ^ C * 2 ^ 18 * 2 ^ r := by rw [hr, pow_add, pow_add, pow_mul]
    have h3c : 3 ^ c = (3 ^ 18) ^ C * 3 ^ 18 * 3 ^ r := by rw [hr, pow_add, pow_add, pow_mul]
    rw [h2c, h3c]
    have f1 : 648 ^ C * (2 ^ 18) ^ C ≤ (3 ^ 18) ^ C := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by norm_num) _
    have f2 : 250 * 2 ^ 18 ≤ 3 ^ 18 := by norm_num
    have f3 : 2 ^ r ≤ 3 ^ r := Nat.pow_le_pow_left (by norm_num) _
    calc 250 * 648 ^ C * ((2 ^ 18) ^ C * 2 ^ 18 * 2 ^ r)
        = (648 ^ C * (2 ^ 18) ^ C) * (250 * 2 ^ 18) * 2 ^ r := by ring
      _ ≤ (3 ^ 18) ^ C * 3 ^ 18 * 3 ^ r := by gcongr
  exact lt_irrefl _ (hbig'.trans_le e1)

/-- **Few kernel points on one plane.** Let `2 τ_n < τ_{n+1}` and `ρ_n < τ_n`. The indices `n`
whose kernel point at `(ρ_n + 2, τ_n + 2)` lies on a proper subspace `U` of `ℚ³` and whose gap is
large, `ε (τ_n + 2) / 4 < τ_n - ρ_n`, number at most `12 (1 + log ε⁻¹)`. -/
theorem card_mem_plane_le {U : Submodule ℚ (Fin 3 → ℚ)} (hU : U ≠ ⊤) {ρ τ : ℕ → ℕ}
    (hτ : ∀ n, 2 * τ n < τ (n + 1)) (hρτ : ∀ n, ρ n < τ n) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (J : Finset ℕ)
    (hJ : ∀ n ∈ J, (fun i ↦ (kernelPoint (ρ n + 2) (τ n + 2) i : ℚ)) ∈ U ∧
      ε / 4 * ((τ n : ℝ) + 2) < (τ n : ℝ) - ρ n) :
    (#J : ℝ) ≤ 12 * (1 + log ε⁻¹) := by
  classical
  obtain ⟨w, hw0, hwU⟩ := exists_ne_zero_forall_sum_mul_eq_zero hU
  have hεinv : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr hε1
  have hlogε : 0 ≤ log ε⁻¹ := log_nonneg hεinv
  rcases J.eq_empty_or_nonempty with rfl | hJne
  · simp only [card_empty, Nat.cast_zero]
    positivity
  have hmono : StrictMono τ := strictMono_nat_of_lt_succ fun n ↦ by have := hτ n; omega
  have hτpos : ∀ n, 0 < τ n := fun n ↦ by have := hρτ n; omega
  have hl2 : 0 < log 2 := log_pos one_lt_two
  have h3odd : ∀ k : ℕ, Odd ((3 : ℤ) ^ k) := fun k ↦ Odd.pow ⟨1, by norm_num⟩
  -- the plane relation at the members
  have hrel : ∀ n ∈ J, w 0 * 3 ^ (τ n + 2) + w 1 * (2 ^ (τ n - ρ n) * 3 ^ (ρ n + 2))
      + w 2 * (2 ^ (τ n + 2) * ((m (τ n + 2) : ℚ) - m (ρ n + 2))) = 0 := fun n hn ↦ by
    have h := hwU _ (hJ n hn).1
    rw [Fin.sum_univ_three] at h
    have hs : τ n + 2 - (ρ n + 2) = τ n - ρ n := by omega
    simpa [kernelPoint, hs] using h
  set n₁ := J.min' hJne with hn₁
  have hn₁J : n₁ ∈ J := J.min'_mem hJne
  have hn₁le : ∀ n ∈ J, n₁ ≤ n := fun n hn ↦ J.min'_le n hn
  -- a window of ratio `2^k` holds at most `k + 1` members
  have hwin : ∀ (J' : Finset ℕ) (n₀ k : ℕ), (∀ n ∈ J', n₀ ≤ n ∧ τ n ≤ 2 ^ k * τ n₀) →
      (#J' : ℝ) ≤ k + 1 := fun J' n₀ k h ↦ by
    have := Nat.card_le_of_doubling_window hτ (hτpos n₀) (R := 2 ^ k)
      (one_le_pow₀ one_le_two) fun n hn ↦ ⟨(h n hn).1, by exact_mod_cast (h n hn).2⟩
    rwa [log_pow, mul_div_assoc, div_self hl2.ne', mul_one] at this
  by_cases hw2 : w 2 = 0
  · -- `w₂ = 0`: the gap is constant on the plane
    have hw1 : w 1 ≠ 0 := by
      intro h1
      have h := hrel n₁ hn₁J
      rw [h1, hw2] at h
      have h0 : w 0 = 0 := by simpa using h
      exact hw0 (by ext i; fin_cases i <;> simp [h0, h1, hw2])
    have hgap : ∀ n ∈ J, w 0 * 3 ^ (τ n - ρ n) + w 1 * 2 ^ (τ n - ρ n) = 0 := fun n hn ↦ by
      have h := hrel n hn
      rw [hw2, zero_mul, add_zero] at h
      have hc : (3 : ℚ) ^ (τ n + 2) = 3 ^ (τ n - ρ n) * 3 ^ (ρ n + 2) := by
        rw [← pow_add]
        congr 1
        have := hρτ n
        omega
      rw [hc] at h
      have : (3 : ℚ) ^ (ρ n + 2) * (w 0 * 3 ^ (τ n - ρ n) + w 1 * 2 ^ (τ n - ρ n)) = 0 := by
        linear_combination h
      exact (mul_eq_zero.mp this).resolve_left (by positivity)
    have hconst : ∀ n ∈ J, τ n - ρ n = τ n₁ - ρ n₁ := fun n hn ↦ by
      by_contra hne
      have h1 := hgap n hn
      have h2 := hgap n₁ hn₁J
      have hw00 : w 0 ≠ 0 := by
        intro h0
        rw [h0, zero_mul, zero_add] at h1
        exact hw1 ((mul_eq_zero.mp h1).resolve_right (by positivity))
      have h3 : w 0 * (2 ^ (τ n₁ - ρ n₁) * 3 ^ (τ n - ρ n)
          - 2 ^ (τ n - ρ n) * 3 ^ (τ n₁ - ρ n₁)) = 0 := by
        linear_combination 2 ^ (τ n₁ - ρ n₁) * h1 - 2 ^ (τ n - ρ n) * h2
      apply two_pow_mul_ne_of_ne (h3odd (τ n - ρ n)) (h3odd (τ n₁ - ρ n₁)) (Ne.symm hne)
      have hq := sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hw00)
      exact_mod_cast hq
    -- the members lie in the window `τ_n ≤ (4/ε) τ_{n₁}`
    have hR : ∀ n ∈ J, n₁ ≤ n ∧ (τ n : ℝ) ≤ 4 / ε * τ n₁ := fun n hn ↦ by
      refine ⟨hn₁le n hn, ?_⟩
      have hb := (hJ n hn).2
      have hs : (τ n : ℝ) - ρ n = τ n₁ - ρ n₁ := by
        have e1 : ((τ n - ρ n : ℕ) : ℝ) = τ n - ρ n := Nat.cast_sub (hρτ n).le
        have e2 : ((τ n₁ - ρ n₁ : ℕ) : ℝ) = τ n₁ - ρ n₁ := Nat.cast_sub (hρτ n₁).le
        rw [← e1, ← e2, hconst n hn]
      rw [hs] at hb
      have hρ0 : (0 : ℝ) ≤ ρ n₁ := (ρ n₁).cast_nonneg
      rw [div_mul_eq_mul_div, le_div_iff₀ hε]
      nlinarith
    have hc := Nat.card_le_of_doubling_window hτ (hτpos n₁) (R := 4 / ε)
      (by rw [le_div_iff₀ hε]; linarith) hR
    have hlog4 : log (4 / ε) = 2 * log 2 + log ε⁻¹ := by
      rw [div_eq_mul_inv, log_mul (by norm_num) (by positivity),
        show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
      push_cast
      ring
    have hl2' : 1 / 2 < log 2 := by have := Real.log_two_gt_d9; linarith
    refine hc.trans ?_
    rw [hlog4, add_div, mul_div_assoc, div_self hl2.ne']
    have : log ε⁻¹ / log 2 ≤ 2 * log ε⁻¹ := by rw [div_le_iff₀ hl2]; nlinarith
    linarith
  · -- `w₂ ≠ 0`: `N = β₁ 3^c + β₂ 2^s 3^a` on the plane
    set β₁ : ℚ := 1 + w 0 / w 2 with hβ₁
    set β₂ : ℚ := w 1 / w 2 - 1 with hβ₂
    have hβ : ∀ n ∈ J, (kernelNum (ρ n + 2) (τ n + 2) : ℚ) = β₁ * 3 ^ (τ n + 2)
        + β₂ * (2 ^ (τ n + 2 - (ρ n + 2)) * 3 ^ (ρ n + 2)) := fun n hn ↦ by
      have h := hrel n hn
      have hs : τ n + 2 - (ρ n + 2) = τ n - ρ n := by omega
      have hN : (kernelNum (ρ n + 2) (τ n + 2) : ℚ) = 3 ^ (τ n + 2)
          - 2 ^ (τ n - ρ n) * 3 ^ (ρ n + 2)
          - 2 ^ (τ n + 2) * ((m (τ n + 2) : ℚ) - m (ρ n + 2)) := by
        simp [kernelNum, hs]
      have hZ : (2 : ℚ) ^ (τ n + 2) * ((m (τ n + 2) : ℚ) - m (ρ n + 2))
          = -(w 0 * 3 ^ (τ n + 2) + w 1 * (2 ^ (τ n - ρ n) * 3 ^ (ρ n + 2))) / w 2 := by
        rw [eq_div_iff hw2]
        linear_combination h
      rw [hs, hN, hZ, hβ₁, hβ₂]
      ring
    -- the members with the gap of `n₁`, and the others
    set J₁ := J.filter fun n ↦ τ n - ρ n = τ n₁ - ρ n₁ with hJ₁
    set J₂ := J.filter fun n ↦ ¬ τ n - ρ n = τ n₁ - ρ n₁ with hJ₂
    have hsplit : (#J : ℝ) = #J₁ + #J₂ := by
      exact_mod_cast (card_filter_add_card_filter_not _).symm
    have hc₁ : (#J₁ : ℝ) ≤ 3 + 1 := hwin J₁ n₁ 3 fun n hn ↦ by
      obtain ⟨hnJ, hsn⟩ := mem_filter.mp hn
      refine ⟨hn₁le n hnJ, ?_⟩
      have := hρτ n
      have := hρτ n₁
      have h7 := seven_mul_lt_of_same_gap (by omega) (by omega) (by omega) (hβ n₁ hn₁J) (hβ n hnJ)
      have := hτpos n₁
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
      omega
    have hc₂ : (#J₂ : ℝ) ≤ 7 + 1 := by
      rcases J₂.eq_empty_or_nonempty with h0 | hne
      · rw [h0, card_empty, Nat.cast_zero]
        norm_num
      have hn'J₂ := J₂.min'_mem hne
      obtain ⟨hn'J, hsn'⟩ := mem_filter.mp hn'J₂
      refine hwin J₂ (J₂.min' hne) 7 fun n hn ↦ ?_
      obtain ⟨hnJ, -⟩ := mem_filter.mp hn
      refine ⟨J₂.min'_le n hn, ?_⟩
      have := hρτ n
      have := hρτ n₁
      have := hρτ (J₂.min' hne)
      have hb := lt_of_ne_gap (by omega) (by omega) (by omega) (by omega) (hβ n₁ hn₁J)
        (hβ _ hn'J) (hβ n hnJ)
      have h1 : τ n₁ ≤ τ (J₂.min' hne) := hmono.monotone (hn₁le _ hn'J)
      have := hτpos (J₂.min' hne)
      rw [show (2 : ℕ) ^ 7 = 128 by norm_num]
      omega
    rw [hsplit]
    nlinarith

end SteeringWord
