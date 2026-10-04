/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormIntervalResult

-- Used only inside proofs.
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A closed form for the number of intervals

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, Theorem 2.3, (2.22).

The number of intervals of Theorem 2.3 (`NumberField.FormSystem.intervalCount`) is the cut count
`⌊log θ / log ω₀⌋ + 1`, `ω₀ = δ⁻¹ log 3R`, of the threshold ratio `intervalBound`, plus the
largest over the quotients of the cut counts of the ratios `2 ω` of Theorem 8.1, weighted by
Theorem 8.1's numbers of intervals. With `mb = 64000 n⁸ 4ⁿ δ⁻² log(64 n R / δ) + 2`
(`chainBound`), a bound for the number of blocks `m` of Theorem 8.1 for every quotient, and
`μ = log(640 n³ 2ⁿ mb / δ)` (`countLog`):

```text
intervalCount n R δ ≤ (n + 3) mb (μ / log ω₀ + 1) ≤ 60 n (n + 3) mb,
```

that is `O(n¹⁰ 4ⁿ δ⁻² log(nR/δ))`: EF13's `m₀ = 10⁵ 2^{2n} n^{10} δ⁻² log(3δ⁻¹R)` up to the
constant. The second step is EF13's at the end of §18: `μ ≤ log c + 4 log ω₀` with
`c = 2744320000 n¹² 8ⁿ` (`countBase_le`), so `μ / log ω₀ = O(n)`.

## Main definitions

* `NumberField.FormSystem.chainBound`: `mb`.
* `NumberField.FormSystem.countLog`: `μ`.
* `NumberField.FormSystem.countConst`: `c = 2744320000 n¹² 8ⁿ`.

## Main results

* `Real.cutCount_le_div`: `cutCount θ ω ≤ log θ / log ω + 1`.
* `NumberField.FormSystem.half_le_log_cutRatio`: `log ω₀ ≥ 1/2`.
* `NumberField.FormSystem.gapBlocks_le_chainBound`: `m ≤ mb` for every quotient.
* `NumberField.FormSystem.gapThreshold_le`: Theorem 8.1's threshold is at most
  `200 n⁷ 8ⁿ R^{2n} m³ (m/ε)^m / (ε δ) · (1 + ℓ)`.
* `NumberField.FormSystem.gapThreshold_quot_le`: for a quotient, `≤ 600 Y^{15} Y^{M} B^{3n²}`,
  `B = 64 n R / δ`.
* `NumberField.FormSystem.log_intervalBound_le`: `log intervalBound ≤ 3 M μ`.
* `NumberField.FormSystem.gapIntervals_mul_cutCount_le`: Theorem 8.1's intervals for one
  quotient, cut, are at most `n M (μ / log ω₀ + 1)`.
* `NumberField.FormSystem.countBase_le`: `Y ≤ c ω₀⁴`.
* `NumberField.FormSystem.intervalCount_le_div`, `NumberField.FormSystem.intervalCount_le`: the
  closed forms.

## Implementation notes

⚠ **Where `μ` goes.** `log C` carries `(m/ε)^m` from the auxiliary polynomial (EF13 Prop. 12.1),
so `log(log C / log C₀) ≍ m μ`, and each interval of Theorem 8.1 has ratio `2ω = 8m/ε ≤ Y`. Cut
into intervals of ratio `ω₀`, both give `μ / log ω₀` pieces per block, and `Y` is polynomial in
`ω₀` with a coefficient `c^{O(1)}`, `log c = O(n)`: EF13's
`log m* / log(δ⁻¹ log 3R) ≤ 2n log 50 / log log 6 + 3`.

This is milestone Q4.2d of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Finset

namespace Real

/-- **The cut count is at most `2 log θ + 1`** once `log ω ≥ 1/2`. -/
theorem cutCount_le {θ ω : ℝ} (hθ : 1 ≤ θ) (hω : 1 / 2 ≤ Real.log ω) :
    (cutCount θ ω : ℝ) ≤ 2 * Real.log θ + 1 := by
  unfold cutCount
  push_cast
  have hl := Real.log_nonneg hθ
  have h1 : (⌊Real.log θ / Real.log ω⌋₊ : ℝ) ≤ Real.log θ / Real.log ω :=
    Nat.floor_le (div_nonneg hl (by linarith))
  have h2 : Real.log θ / Real.log ω ≤ 2 * Real.log θ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- **The cut count is at most `log θ / log ω + 1`.** -/
theorem cutCount_le_div {θ ω : ℝ} (hθ : 1 ≤ θ) (hω : 1 < ω) :
    (cutCount θ ω : ℝ) ≤ Real.log θ / Real.log ω + 1 := by
  unfold cutCount
  push_cast
  have := Nat.floor_le (div_nonneg (Real.log_nonneg hθ) (Real.log_pos hω).le)
  linarith

end Real

namespace NumberField.FormSystem

/-- **`log ω₀ ≥ 1/2`**: `ω₀ = δ⁻¹ log 3R ≥ log 6 > 5/3 > e^{1/2}`. -/
theorem half_le_log_cutRatio {R : ℕ} (hR : 2 ≤ R) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 / 2 ≤ Real.log (cutRatio R δ) := by
  have h6 : (6 : ℝ) ≤ 3 * R := by
    have : (2 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have he := Real.exp_one_lt_d9
  have h53 : (5 : ℝ) / 3 < Real.log 6 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have hcube : Real.exp (5 / 3) ^ 3 = Real.exp 1 ^ 5 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      norm_num
    have h5 : Real.exp 1 ^ 5 < 216 :=
      (pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)).trans (by norm_num)
    by_contra h
    have := pow_le_pow_left₀ (by norm_num) (not_lt.1 h) 3
    linarith
  have hhalf : Real.exp (1 / 2) ≤ 5 / 3 := by
    have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have hl6 : Real.log 6 ≤ cutRatio R δ := by
    rw [cutRatio, le_div_iff₀ hδ]
    have := Real.log_le_log (by norm_num) h6
    have h0 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    nlinarith
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith

/-! ### The number of blocks -/

/-- **`mb = 64000 n⁸ 4ⁿ δ⁻² log(64 n R / δ) + 2`**, a bound for the number of blocks `m` of
Theorem 8.1 for every quotient (`gapBlocks_le_chainBound`). -/
noncomputable def chainBound (n R : ℕ) (δ : ℝ) : ℝ :=
  64000 * n ^ 8 * 4 ^ n / δ ^ 2 * Real.log (64 * n * R / δ) + 2

/-- `ε` of Theorem 8.1 for a quotient with `p` variables. -/
theorem gapEps_eq (p n : ℕ) (δ : ℝ) :
    gapEps p (δ / (2 * n)) = δ / (80 * n * p ^ 2 * 2 ^ p) := by
  rw [gapEps, div_div]
  ring_nf

theorem four_pow_eq (p : ℕ) : ((2 : ℝ) ^ p) ^ 2 = 4 ^ p := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-- **The number of blocks of Theorem 8.1** for a quotient with `p ≤ n` variables, `Rⁿ` forms and
`δ / 2n` is at most `mb`. -/
theorem gapBlocks_le_chainBound {n R p : ℕ} (hn : 2 ≤ n) (hp : 1 ≤ p) (hpn : p ≤ n) (hR : 1 ≤ R)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (gapBlocks p (R ^ n) (δ / (2 * n)) : ℝ) ≤ chainBound n R δ := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpn' : (p : ℝ) ≤ n := by exact_mod_cast hpn
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  set B : ℝ := 64 * n * R / δ with hB
  have hδ' : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hBR : (R : ℝ) ≤ B := by
    rw [hB, le_div_iff₀ hδ]
    nlinarith
  have hB4 : 4 ≤ B := by
    rw [hB, le_div_iff₀ hδ]
    nlinarith
  have hB1 : 1 ≤ B := by linarith
  set ε := gapEps p (δ / (2 * n)) with hε
  have hεeq : ε = δ / (80 * n * p ^ 2 * 2 ^ p) := gapEps_eq p n δ
  have hε0 : 0 < ε := by rw [hεeq]; positivity
  -- `2 / ε² ≤ 12800 n⁶ 4ⁿ / δ²`
  have h1 : 2 / ε ^ 2 ≤ 12800 * n ^ 6 * 4 ^ n / δ ^ 2 := by
    have he : 2 / ε ^ 2 = 12800 * n ^ 2 * p ^ 4 * 4 ^ p / δ ^ 2 := by
      rw [hεeq, ← four_pow_eq]
      field_simp
      ring
    rw [he]
    have h4p : (4 : ℝ) ^ p ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hpn
    have hnum : 12800 * (n : ℝ) ^ 2 * (p : ℝ) ^ 4 * (4 : ℝ) ^ p ≤ 12800 * (n : ℝ) ^ 6 * 4 ^ n := by
      calc 12800 * (n : ℝ) ^ 2 * (p : ℝ) ^ 4 * (4 : ℝ) ^ p
          ≤ 12800 * (n : ℝ) ^ 2 * (n : ℝ) ^ 4 * (4 : ℝ) ^ n := by gcongr
        _ = 12800 * (n : ℝ) ^ 6 * 4 ^ n := by ring
    exact div_le_div_of_nonneg_right hnum (by positivity)
  -- the logarithm
  set X : ℝ := ((R ^ n : ℕ) : ℝ) ^ p with hX
  set Y : ℝ := ((p : ℝ) / ε + 2) ^ p with hY
  have hX1 : 1 ≤ X := one_le_pow₀ (by exact_mod_cast Nat.one_le_pow _ _ (by omega))
  have hpε0 : 0 ≤ (p : ℝ) / ε := by positivity
  have hY1 : 1 ≤ Y := one_le_pow₀ (by linarith)
  have hXB : X ≤ B ^ (n ^ 2) := by
    rw [hX, Nat.cast_pow, ← pow_mul, sq]
    calc (R : ℝ) ^ (n * p) ≤ R ^ (n * n) := pow_le_pow_right₀ hR1 (Nat.mul_le_mul_left _ hpn)
      _ ≤ B ^ (n * n) := pow_le_pow_left₀ (by linarith) hBR _
  have hpε : (p : ℝ) / ε + 2 ≤ B ^ (n + 4) := by
    have he : (p : ℝ) / ε = 80 * n * p ^ 3 * 2 ^ p / δ := by
      rw [hεeq]
      field_simp
    have h2n : (2 : ℝ) ^ p ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hpn
    have hp3 : (p : ℝ) ^ 3 ≤ n ^ 3 := by gcongr
    have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have hn1 : (1 : ℝ) ≤ n := by linarith
    calc (p : ℝ) / ε + 2 ≤ 82 * n ^ 4 * 2 ^ n / δ := by
          rw [he, le_div_iff₀ hδ, add_mul, div_mul_cancel₀ _ hδ.ne']
          have h3 : 80 * (n : ℝ) * p ^ 3 * 2 ^ p ≤ 80 * n * n ^ 3 * 2 ^ n := by gcongr
          have h4 : 2 * δ ≤ 2 * n ^ 4 * 2 ^ n := by
            have : (1 : ℝ) ≤ n ^ 4 := one_le_pow₀ hn1
            nlinarith
          nlinarith
      _ ≤ B ^ n * B ^ 4 := by
          rw [div_le_iff₀ hδ]
          have hBn : (2 : ℝ) ^ n ≤ B ^ n := pow_le_pow_left₀ (by norm_num) (by linarith) _
          have hB4' : 82 * (n : ℝ) ^ 4 ≤ B ^ 4 * δ := by
            have hd4 : δ ^ 4 ≤ δ := pow_le_of_le_one hδ.le hδ1 (by norm_num)
            have hBδ : B ^ 4 * δ ^ 4 = 64 ^ 4 * n ^ 4 * R ^ 4 := by
              rw [hB, div_pow]
              field_simp
            have hR4 : (1 : ℝ) ≤ R ^ 4 := one_le_pow₀ hR1
            have hB40 : 0 ≤ B ^ 4 := by positivity
            have h44 := mul_le_mul_of_nonneg_left hd4 hB40
            have hn4 : (0 : ℝ) ≤ n ^ 4 := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hR4 hn4]
          calc 82 * (n : ℝ) ^ 4 * 2 ^ n = 82 * n ^ 4 * 2 ^ n := rfl
            _ ≤ B ^ 4 * δ * B ^ n := by
                have := mul_le_mul hB4' hBn (by positivity) (by positivity)
                linarith
            _ = B ^ n * B ^ 4 * δ := by ring
      _ = B ^ (n + 4) := (pow_add _ _ _).symm
  have hYB : Y ≤ B ^ ((n + 4) * n) := by
    rw [hY, pow_mul]
    calc ((p : ℝ) / ε + 2) ^ p ≤ (B ^ (n + 4)) ^ p :=
          pow_le_pow_left₀ (by positivity) hpε _
      _ ≤ (B ^ (n + 4)) ^ n := pow_le_pow_right₀ (one_le_pow₀ hB1) hpn
  have hinner : 2 * (X * Y + 1) ≤ B ^ (5 * n ^ 2) := by
    calc 2 * (X * Y + 1) ≤ B * (X * Y) := by nlinarith [one_le_mul_of_one_le_of_one_le hX1 hY1]
      _ ≤ B * (B ^ (n ^ 2) * B ^ ((n + 4) * n)) := by gcongr
      _ = B ^ (1 + n ^ 2 + (n + 4) * n) := by ring
      _ ≤ B ^ (5 * n ^ 2) := pow_le_pow_right₀ hB1 (by nlinarith)
  have h2 : Real.log (2 * (X * Y + 1)) ≤ 5 * n ^ 2 * Real.log B := by
    calc Real.log (2 * (X * Y + 1)) ≤ Real.log (B ^ (5 * n ^ 2)) :=
          Real.log_le_log (by positivity) hinner
      _ = 5 * n ^ 2 * Real.log B := by rw [Real.log_pow]; push_cast; ring
  have hΛ0 : 0 ≤ Real.log (2 * (X * Y + 1)) :=
    Real.log_nonneg (by nlinarith [one_le_mul_of_one_le_of_one_le hX1 hY1])
  have h3 : (gapBlocks p (R ^ n) (δ / (2 * n)) : ℝ) ≤
      2 / ε ^ 2 * Real.log (2 * (X * Y + 1)) + 2 := by
    rw [gapBlocks, gapChain]
    push_cast
    have := Nat.ceil_lt_add_one (show 0 ≤ 2 / ε ^ 2 * Real.log (2 * (X * Y + 1)) by positivity)
    rw [hX, hY, hε] at this ⊢
    push_cast at this ⊢
    linarith
  calc (gapBlocks p (R ^ n) (δ / (2 * n)) : ℝ) ≤ 2 / ε ^ 2 * Real.log (2 * (X * Y + 1)) + 2 := h3
    _ ≤ 12800 * n ^ 6 * 4 ^ n / δ ^ 2 * (5 * n ^ 2 * Real.log B) + 2 := by
        gcongr
    _ = chainBound n R δ := by rw [chainBound, hB]; ring

/-! ### The threshold of Theorem 8.1 -/

section Terms

variable {N G X M P E D ℓ : ℝ}

private theorem le_mul_of_one_le {a b : ℝ} (ha : 0 ≤ a) (hb : 1 ≤ b) : a ≤ a * b :=
  le_mul_of_one_le_right ha hb

private theorem one_le_mul {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
  one_le_mul_of_one_le_of_one_le ha hb

private theorem gapTerm₁ (hN : 1 ≤ N) (hX : 1 ≤ X) (hD : 1 ≤ D) (hℓ : 0 ≤ ℓ) :
    (N ^ 2 + X * ℓ) * D ≤ 2 * (N ^ 2 * X * D * (1 + ℓ)) := by
  have h1 : N ^ 2 * D ≤ N ^ 2 * X * D * (1 + ℓ) := by
    have := le_mul_of_one_le (a := N ^ 2 * D) (by positivity)
      (one_le_mul hX (show (1 : ℝ) ≤ 1 + ℓ by linarith))
    linarith [show N ^ 2 * D * (X * (1 + ℓ)) = N ^ 2 * X * D * (1 + ℓ) by ring]
  have h2 : X * ℓ * D ≤ N ^ 2 * X * D * (1 + ℓ) := by
    have h := mul_le_mul (le_mul_of_one_le (a := X * D) (by positivity) (one_le_pow₀ (n := 2) hN))
      (show ℓ ≤ 1 + ℓ by linarith) hℓ (by positivity)
    linarith [show X * D * N ^ 2 * (1 + ℓ) = N ^ 2 * X * D * (1 + ℓ) by ring,
      show X * D * ℓ = X * ℓ * D by ring]
  linarith [show (N ^ 2 + X * ℓ) * D = N ^ 2 * D + X * ℓ * D by ring]

private theorem gapTerm₂ (hN : 1 ≤ N) (hX : 1 ≤ X) (hD : 1 ≤ D) (hℓ : 0 ≤ ℓ) :
    3 * N ^ 2 + 3 * N * X * ℓ ≤ 6 * (N ^ 2 * X * D * (1 + ℓ)) := by
  have hW : 1 ≤ X * D := one_le_mul hX hD
  have h1 : N ^ 2 ≤ N ^ 2 * X * D * (1 + ℓ) := by
    have := le_mul_of_one_le (a := N ^ 2) (by positivity)
      (one_le_mul hW (show (1 : ℝ) ≤ 1 + ℓ by linarith))
    linarith [show N ^ 2 * (X * D * (1 + ℓ)) = N ^ 2 * X * D * (1 + ℓ) by ring]
  have h2 : N * X * ℓ ≤ N ^ 2 * X * D * (1 + ℓ) := by
    have hNN : N ≤ N ^ 2 := by nlinarith
    have hND : N * X ≤ N ^ 2 * X * D := by
      have := le_mul_of_one_le (a := N * X) (by positivity) (one_le_mul (show 1 ≤ N by linarith) hD)
      nlinarith
    have := mul_le_mul hND (show ℓ ≤ 1 + ℓ by linarith) hℓ (by positivity)
    linarith
  linarith

private theorem gapTerm₃ (hN : 1 ≤ N) (hX : 1 ≤ X) (hD : 1 ≤ D) (hℓ : 0 ≤ ℓ) :
    3 * N ^ 2 + 6 * ℓ ≤ 9 * (N ^ 2 * X * D * (1 + ℓ)) := by
  have hW : 1 ≤ N ^ 2 * X * D := one_le_mul (one_le_mul (one_le_pow₀ hN) hX) hD
  have h1 : N ^ 2 ≤ N ^ 2 * X * D * (1 + ℓ) := by
    have := le_mul_of_one_le (a := N ^ 2) (by positivity)
      (one_le_mul (one_le_mul hX hD) (show 1 ≤ 1 + ℓ by linarith))
    linarith [show N ^ 2 * (X * D * (1 + ℓ)) = N ^ 2 * X * D * (1 + ℓ) by ring]
  have h2 : ℓ ≤ N ^ 2 * X * D * (1 + ℓ) := by
    have := mul_le_mul hW (show ℓ ≤ 1 + ℓ by linarith) hℓ (by positivity)
    linarith
  linarith

private theorem gapTerm₄ (hN : 1 ≤ N) (hD : 1 ≤ D) (hℓ : 0 ≤ ℓ) :
    4 * N ^ 3 ≤ 4 * (N ^ 3 * D * (1 + ℓ)) := by
  have := le_mul_of_one_le (a := N ^ 3) (by positivity) (one_le_mul hD (show 1 ≤ 1 + ℓ by linarith))
  linarith [show N ^ 3 * (D * (1 + ℓ)) = N ^ 3 * D * (1 + ℓ) by ring]

private theorem gapTerm₅ (hN : 1 ≤ N) (hG : 1 ≤ G) (hD : 1 ≤ D) (hℓ : 0 ≤ ℓ) :
    N ^ 2 * G * (3 * N ^ 3 + ℓ) * D ≤ 4 * (N ^ 5 * G * D * (1 + ℓ)) := by
  have h0 : 1 ≤ N ^ 3 := one_le_pow₀ hN
  have h1 : 3 * N ^ 3 + ℓ ≤ 4 * N ^ 3 * (1 + ℓ) := by nlinarith
  have h2 : 0 ≤ N ^ 2 * G * D := by positivity
  calc N ^ 2 * G * (3 * N ^ 3 + ℓ) * D = N ^ 2 * G * D * (3 * N ^ 3 + ℓ) := by ring
    _ ≤ N ^ 2 * G * D * (4 * N ^ 3 * (1 + ℓ)) := mul_le_mul_of_nonneg_left h1 h2
    _ = 4 * (N ^ 5 * G * D * (1 + ℓ)) := by ring

private theorem gapTerm₆ (hN : 1 ≤ N) (hX : 1 ≤ X) (hD : 1 ≤ D) (hℓ : 0 ≤ ℓ) :
    3 * N * X * (3 * N ^ 2 + ℓ) * D ≤ 12 * (N ^ 3 * X * D * (1 + ℓ)) := by
  have h0 : 1 ≤ N ^ 2 := one_le_pow₀ hN
  have h1 : 3 * N ^ 2 + ℓ ≤ 4 * N ^ 2 * (1 + ℓ) := by nlinarith
  have h2 : 0 ≤ 3 * N * X * D := by positivity
  calc 3 * N * X * (3 * N ^ 2 + ℓ) * D = 3 * N * X * D * (3 * N ^ 2 + ℓ) := by ring
    _ ≤ 3 * N * X * D * (4 * N ^ 2 * (1 + ℓ)) := mul_le_mul_of_nonneg_left h1 h2
    _ = 12 * (N ^ 3 * X * D * (1 + ℓ)) := by ring

private theorem gapTerm₇ (hN : 1 ≤ N) (hG : 1 ≤ G) (hX : 1 ≤ X) (hM : 1 ≤ M) (hP : 1 ≤ P)
    (hD : 1 ≤ D) (hℓ : 0 ≤ ℓ) :
    3 * X * D * (G + G * P * (20 * M ^ 3 + M + 2 * M ^ 2 * (2 * G + N ^ 2)) +
      G * P * (2 * M ^ 2 * (2 * N * X)) * ℓ + 1) ≤
      99 * (N ^ 2 * G ^ 2 * X ^ 2 * M ^ 3 * P * D * (1 + ℓ)) := by
  set Q := G ^ 2 * N ^ 2 * X * M ^ 3 * P with hQ
  have hN2 := one_le_pow₀ (n := 2) hN
  have hG2 := one_le_pow₀ (n := 2) hG
  have hM2 := one_le_pow₀ (n := 2) hM
  have hM3 := one_le_pow₀ (n := 3) hM
  have q1 : G ≤ Q := by
    have := le_mul_of_one_le (a := G) (by positivity)
      (one_le_mul (one_le_mul (one_le_mul (one_le_mul hG hN2) hX) hM3) hP)
    linarith [show G * (G * N ^ 2 * X * M ^ 3 * P) = Q by rw [hQ]; ring]
  have q2 : G * P * M ^ 3 ≤ Q := by
    have := le_mul_of_one_le (a := G * P * M ^ 3) (by positivity)
      (one_le_mul (one_le_mul hG hN2) hX)
    linarith [show G * P * M ^ 3 * (G * N ^ 2 * X) = Q by rw [hQ]; ring]
  have q3 : G * P * M ≤ Q := by
    have := le_mul_of_one_le (a := G * P * M) (by positivity)
      (one_le_mul (one_le_mul (one_le_mul hG hN2) hX) hM2)
    linarith [show G * P * M * (G * N ^ 2 * X * M ^ 2) = Q by rw [hQ]; ring]
  have q4 : G ^ 2 * P * M ^ 2 ≤ Q := by
    have := le_mul_of_one_le (a := G ^ 2 * P * M ^ 2) (by positivity)
      (one_le_mul (one_le_mul hN2 hX) hM)
    linarith [show G ^ 2 * P * M ^ 2 * (N ^ 2 * X * M) = Q by rw [hQ]; ring]
  have q5 : G * P * M ^ 2 * N ^ 2 ≤ Q := by
    have := le_mul_of_one_le (a := G * P * M ^ 2 * N ^ 2) (by positivity)
      (one_le_mul (one_le_mul hG hX) hM)
    linarith [show G * P * M ^ 2 * N ^ 2 * (G * X * M) = Q by rw [hQ]; ring]
  have q6 : G * P * M ^ 2 * N * X ≤ Q := by
    have := le_mul_of_one_le (a := G * P * M ^ 2 * N * X) (by positivity)
      (one_le_mul (one_le_mul hG hN) hM)
    linarith [show G * P * M ^ 2 * N * X * (G * N * M) = Q by rw [hQ]; ring]
  have q7 : 1 ≤ Q := hG.trans q1
  have h6 : G * P * M ^ 2 * N * X * ℓ ≤ Q * ℓ := mul_le_mul_of_nonneg_right q6 hℓ
  have hQℓ : 0 ≤ Q * ℓ := by positivity
  have inner : G + G * P * (20 * M ^ 3 + M + 2 * M ^ 2 * (2 * G + N ^ 2)) +
      G * P * (2 * M ^ 2 * (2 * N * X)) * ℓ + 1 ≤ 33 * (Q * (1 + ℓ)) := by
    have e : G + G * P * (20 * M ^ 3 + M + 2 * M ^ 2 * (2 * G + N ^ 2)) +
        G * P * (2 * M ^ 2 * (2 * N * X)) * ℓ + 1 =
        G + 20 * (G * P * M ^ 3) + G * P * M + 4 * (G ^ 2 * P * M ^ 2) +
          2 * (G * P * M ^ 2 * N ^ 2) + 4 * (G * P * M ^ 2 * N * X * ℓ) + 1 := by ring
    rw [e, mul_add, mul_one]
    linarith
  have h2 : 0 ≤ 3 * X * D := by positivity
  calc _ ≤ 3 * X * D * (33 * (Q * (1 + ℓ))) := mul_le_mul_of_nonneg_left inner h2
    _ = 99 * (N ^ 2 * G ^ 2 * X ^ 2 * M ^ 3 * P * D * (1 + ℓ)) := by rw [hQ]; ring

private theorem gapTerm₈ (hN : 1 ≤ N) (hG : 1 ≤ G) (hX : 1 ≤ X) (hE : 1 ≤ E) (hD : 1 ≤ D)
    (hℓ : 0 ≤ ℓ) :
    2 * N * G * D * (1 + 2 * (5 * G + 2 * N ^ 2 + 1 + G * (G * E + 1)) + 2 * (4 * N * X) * ℓ) ≤
      58 * (N ^ 3 * G ^ 3 * X * E * D * (1 + ℓ)) := by
  set Q := G ^ 2 * N ^ 2 * X * E with hQ
  have hN2 := one_le_pow₀ (n := 2) hN
  have hG2 := one_le_pow₀ (n := 2) hG
  have r1 : G ≤ Q := by
    have := le_mul_of_one_le (a := G) (by positivity)
      (one_le_mul (one_le_mul (one_le_mul hG hN2) hX) hE)
    linarith [show G * (G * N ^ 2 * X * E) = Q by rw [hQ]; ring]
  have r2 : N ^ 2 ≤ Q := by
    have := le_mul_of_one_le (a := N ^ 2) (by positivity) (one_le_mul (one_le_mul hG2 hX) hE)
    linarith [show N ^ 2 * (G ^ 2 * X * E) = Q by rw [hQ]; ring]
  have r3 : G ^ 2 * E ≤ Q := by
    have := le_mul_of_one_le (a := G ^ 2 * E) (by positivity) (one_le_mul hN2 hX)
    linarith [show G ^ 2 * E * (N ^ 2 * X) = Q by rw [hQ]; ring]
  have r4 : N * X ≤ Q := by
    have := le_mul_of_one_le (a := N * X) (by positivity) (one_le_mul (one_le_mul hG2 hN) hE)
    linarith [show N * X * (G ^ 2 * N * E) = Q by rw [hQ]; ring]
  have r5 : 1 ≤ Q := hG.trans r1
  have h6 : N * X * ℓ ≤ Q * ℓ := mul_le_mul_of_nonneg_right r4 hℓ
  have hQℓ : 0 ≤ Q * ℓ := by positivity
  have inner : 1 + 2 * (5 * G + 2 * N ^ 2 + 1 + G * (G * E + 1)) + 2 * (4 * N * X) * ℓ ≤
      29 * (Q * (1 + ℓ)) := by
    have e : 1 + 2 * (5 * G + 2 * N ^ 2 + 1 + G * (G * E + 1)) + 2 * (4 * N * X) * ℓ =
        3 + 12 * G + 4 * N ^ 2 + 2 * (G ^ 2 * E) + 8 * (N * X * ℓ) := by ring
    rw [e, mul_add, mul_one]
    linarith
  have h2 : 0 ≤ 2 * N * G * D := by positivity
  calc _ ≤ 2 * N * G * D * (29 * (Q * (1 + ℓ))) := mul_le_mul_of_nonneg_left inner h2
    _ = 58 * (N ^ 3 * G ^ 3 * X * E * D * (1 + ℓ)) := by rw [hQ]; ring

end Terms

/-- **A product bound for the threshold of Theorem 8.1**:
`log C₂ ≤ 200 n⁷ 8ⁿ R^{2n} m³ (m/ε)^m / (ε δ) · (1 + ℓ)`, `m` the number of blocks and `ε` of
(14.1). -/
theorem gapThreshold_le {n R : ℕ} {δ ℓ : ℝ} (hn : 1 ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hℓ : 0 ≤ ℓ) :
    gapThreshold n R δ ℓ ≤ 200 * ((n : ℝ) ^ 7 * ((2 : ℝ) ^ n) ^ 3 * ((R : ℝ) ^ n) ^ 2 *
      (gapBlocks n R δ : ℝ) ^ 3 * ((gapBlocks n R δ : ℝ) * (gapEps n δ)⁻¹) ^ gapBlocks n R δ *
      (gapEps n δ)⁻¹ * δ⁻¹) * (1 + ℓ) := by
  have hε0 := gapEps_pos hn hδ
  have hε1 := gapEps_le_one hn hδ1
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hM : (1 : ℝ) ≤ gapBlocks n R δ := by
    have : 1 ≤ gapBlocks n R δ := Nat.le_add_left 1 _
    exact_mod_cast this
  rw [gapThreshold]
  unfold thetaOneA thetaOneB thetaTwoA thetaTwoB
  simp only [div_eq_mul_inv]
  set m := gapBlocks n R δ with hm
  set ε := gapEps n δ
  set N : ℝ := (n : ℝ)
  set G : ℝ := 2 ^ n
  set X : ℝ := (R : ℝ) ^ n
  set M : ℝ := (m : ℝ)
  set E : ℝ := ε⁻¹
  set D : ℝ := δ⁻¹
  set P : ℝ := (M * E) ^ m
  have hG : 1 ≤ G := one_le_pow₀ (by norm_num)
  have hX : 1 ≤ X := one_le_pow₀ (by exact_mod_cast hR)
  have hE : 1 ≤ E := (one_le_inv₀ hε0).2 hε1
  have hD : 1 ≤ D := (one_le_inv₀ hδ).2 hδ1
  have hP : 1 ≤ P := one_le_pow₀ (one_le_mul hM hE)
  have hu : 0 ≤ 1 + ℓ := by linarith
  set Z := N ^ 7 * G ^ 3 * X ^ 2 * M ^ 3 * P * E * D with hZ
  have hN2 := one_le_pow₀ (n := 2) hN
  have hN4 := one_le_pow₀ (n := 4) hN
  have hG2 := one_le_pow₀ (n := 2) hG
  have hG3 := one_le_pow₀ (n := 3) hG
  have hX2 := one_le_pow₀ (n := 2) hX
  have hM3 := one_le_pow₀ (n := 3) hM
  -- every monomial is at most `Z`
  have k1 : N ^ 2 * X * D ≤ Z := by
    have := le_mul_of_one_le (a := N ^ 2 * X * D) (by positivity)
      (one_le_mul (one_le_mul (one_le_mul (one_le_mul (one_le_mul (one_le_pow₀ (n := 5) hN) hG3) hX)
        hM3) hP) hE)
    linarith [show N ^ 2 * X * D * (N ^ 5 * G ^ 3 * X * M ^ 3 * P * E) = Z by rw [hZ]; ring]
  have k2 : N ^ 3 * D ≤ Z := by
    have := le_mul_of_one_le (a := N ^ 3 * D) (by positivity)
      (one_le_mul (one_le_mul (one_le_mul (one_le_mul (one_le_mul hN4 hG3) hX2) hM3) hP) hE)
    linarith [show N ^ 3 * D * (N ^ 4 * G ^ 3 * X ^ 2 * M ^ 3 * P * E) = Z by rw [hZ]; ring]
  have k3 : N ^ 5 * G * D ≤ Z := by
    have := le_mul_of_one_le (a := N ^ 5 * G * D) (by positivity)
      (one_le_mul (one_le_mul (one_le_mul (one_le_mul (one_le_mul hN2 hG2) hX2) hM3) hP) hE)
    linarith [show N ^ 5 * G * D * (N ^ 2 * G ^ 2 * X ^ 2 * M ^ 3 * P * E) = Z by rw [hZ]; ring]
  have k4 : N ^ 3 * X * D ≤ Z := by
    have := le_mul_of_one_le (a := N ^ 3 * X * D) (by positivity)
      (one_le_mul (one_le_mul (one_le_mul (one_le_mul (one_le_mul hN4 hG3) hX) hM3) hP) hE)
    linarith [show N ^ 3 * X * D * (N ^ 4 * G ^ 3 * X * M ^ 3 * P * E) = Z by rw [hZ]; ring]
  have k5 : N ^ 2 * G ^ 2 * X ^ 2 * M ^ 3 * P * D ≤ Z := by
    have := le_mul_of_one_le (a := N ^ 2 * G ^ 2 * X ^ 2 * M ^ 3 * P * D) (by positivity)
      (one_le_mul (one_le_mul (one_le_pow₀ (n := 5) hN) hG) hE)
    linarith [show N ^ 2 * G ^ 2 * X ^ 2 * M ^ 3 * P * D * (N ^ 5 * G * E) = Z by rw [hZ]; ring]
  have k6 : N ^ 3 * G ^ 3 * X * E * D ≤ Z := by
    have := le_mul_of_one_le (a := N ^ 3 * G ^ 3 * X * E * D) (by positivity)
      (one_le_mul (one_le_mul (one_le_mul hN4 hX) hM3) hP)
    linarith [show N ^ 3 * G ^ 3 * X * E * D * (N ^ 4 * X * M ^ 3 * P) = Z by rw [hZ]; ring]
  have z := fun (a : ℝ) (h : a ≤ Z) ↦ mul_le_mul_of_nonneg_right h hu
  have hZu : 0 ≤ Z * (1 + ℓ) := by positivity
  calc _ ≤ 2 * (N ^ 2 * X * D * (1 + ℓ)) + 6 * (N ^ 2 * X * D * (1 + ℓ)) +
          9 * (N ^ 2 * X * D * (1 + ℓ)) + 4 * (N ^ 3 * D * (1 + ℓ)) +
          4 * (N ^ 5 * G * D * (1 + ℓ)) + 12 * (N ^ 3 * X * D * (1 + ℓ)) +
          99 * (N ^ 2 * G ^ 2 * X ^ 2 * M ^ 3 * P * D * (1 + ℓ)) +
          58 * (N ^ 3 * G ^ 3 * X * E * D * (1 + ℓ)) :=
        add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
          (gapTerm₁ hN hX hD hℓ) (gapTerm₂ hN hX hD hℓ)) (gapTerm₃ hN hX hD hℓ))
          (gapTerm₄ hN hD hℓ)) (gapTerm₅ hN hG hD hℓ)) (gapTerm₆ hN hX hD hℓ))
          (gapTerm₇ hN hG hX hM hP hD hℓ)) (gapTerm₈ hN hG hX hE hD hℓ)
    _ ≤ 200 * Z * (1 + ℓ) := by
        have := z _ k1; have := z _ k2; have := z _ k3; have := z _ k4; have := z _ k5
        have := z _ k6
        nlinarith

/-! ### The bases `Y` and `B` -/

/-- **`Y = 640 n³ 2ⁿ mb / δ`**, the base of the count; `μ = log Y` (`countLog`). -/
noncomputable def countBase (n R : ℕ) (δ : ℝ) : ℝ := 640 * n ^ 3 * 2 ^ n * chainBound n R δ / δ

/-- **`μ = log(640 n³ 2ⁿ mb / δ)`**. -/
noncomputable def countLog (n R : ℕ) (δ : ℝ) : ℝ := Real.log (countBase n R δ)

section Bases

variable {n R : ℕ} {δ : ℝ}

theorem one_le_heightBase (hn : 1 ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ 64 * (n : ℝ) * R / δ := by
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (1 : ℝ) ≤ R := by exact_mod_cast hR
  rw [le_div_iff₀ hδ]
  nlinarith

theorem log_heightBase_nonneg (hn : 1 ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ Real.log (64 * (n : ℝ) * R / δ) :=
  Real.log_nonneg (one_le_heightBase hn hR hδ hδ1)

theorem two_le_chainBound (hn : 1 ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    2 ≤ chainBound n R δ := by
  have := log_heightBase_nonneg hn hR hδ hδ1
  rw [chainBound]
  have : 0 ≤ 64000 * (n : ℝ) ^ 8 * 4 ^ n / δ ^ 2 := by positivity
  nlinarith

/-- `4 n² log B ≤ mb`. -/
theorem sq_mul_log_le_chainBound (hn : 1 ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    4 * n ^ 2 * Real.log (64 * (n : ℝ) * R / δ) ≤ chainBound n R δ := by
  have hl := log_heightBase_nonneg hn hR hδ hδ1
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 4 * (n : ℝ) ^ 2 ≤ 64000 * n ^ 8 * 4 ^ n / δ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have hd2 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
    have h4 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    have h6 : (n : ℝ) ^ 2 ≤ n ^ 8 := pow_le_pow_right₀ hN (by norm_num)
    have h8 : (n : ℝ) ^ 2 * 1 ≤ n ^ 8 * 4 ^ n := mul_le_mul h6 h4 zero_le_one (by positivity)
    nlinarith
  rw [chainBound]
  nlinarith

theorem one_le_countBase (hn : 1 ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ countBase n R δ := by
  have hm := two_le_chainBound hn hR hδ hδ1
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [countBase, le_div_iff₀ hδ]
  have : (1 : ℝ) ≤ n ^ 3 * 2 ^ n := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN)
    (one_le_pow₀ (by norm_num))
  nlinarith

/-- `Y ≥ (80 n³ 2ⁿ / δ) mb`, and `80 n³ 2ⁿ / δ ≥ 1`. -/
theorem le_countBase (hn : 1 ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    80 * n ^ 3 * 2 ^ n / δ * chainBound n R δ ≤ countBase n R δ := by
  have hm := two_le_chainBound hn hR hδ hδ1
  rw [countBase]
  have : 0 ≤ (n : ℝ) ^ 3 * 2 ^ n * chainBound n R δ / δ := by positivity
  have e : 640 * (n : ℝ) ^ 3 * 2 ^ n * chainBound n R δ / δ =
      8 * (80 * n ^ 3 * 2 ^ n / δ * chainBound n R δ) := by ring
  rw [e]
  have : 0 ≤ 80 * (n : ℝ) ^ 3 * 2 ^ n / δ * chainBound n R δ := by positivity
  linarith

theorem one_le_countLog (hn : 1 ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ countLog n R δ := by
  rw [countLog, Real.le_log_iff_exp_le (zero_lt_one.trans_le (one_le_countBase hn hR hδ hδ1))]
  have hm := two_le_chainBound hn hR hδ hδ1
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h3 : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9).le.trans (by norm_num)
  refine h3.trans ?_
  rw [countBase, le_div_iff₀ hδ]
  have : (1 : ℝ) ≤ n ^ 3 * 2 ^ n := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN)
    (one_le_pow₀ (by norm_num))
  nlinarith

end Bases

/-! ### The threshold for the quotients -/

section Quotients

variable {n R p : ℕ} {δ : ℝ}

/-- `K = 80 n³ 2ⁿ / δ ≤ Y`. -/
theorem le_countBase' (hn : 1 ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    80 * (n : ℝ) ^ 3 * 2 ^ n / δ ≤ countBase n R δ := by
  have h := le_countBase hn hR hδ hδ1
  have hm := two_le_chainBound hn hR hδ hδ1
  have : 0 ≤ 80 * (n : ℝ) ^ 3 * 2 ^ n / δ := by positivity
  nlinarith

theorem one_le_K (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 1 ≤ 80 * (n : ℝ) ^ 3 * 2 ^ n / δ := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (1 : ℝ) ≤ n ^ 3 * 2 ^ n :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN) (one_le_pow₀ (by norm_num))
  rw [le_div_iff₀ hδ]
  nlinarith

theorem chainBound_le_countBase (hn : 1 ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    chainBound n R δ ≤ countBase n R δ := by
  have h := le_countBase hn hR hδ hδ1
  have hK := one_le_K hn hδ hδ1
  have hm := two_le_chainBound hn hR hδ hδ1
  nlinarith

theorem cast_le_countBase (hn : 1 ≤ n) (hpn : p ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (p : ℝ) ≤ countBase n R δ := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpn' : (p : ℝ) ≤ n := by exact_mod_cast hpn
  have h1 : (n : ℝ) ≤ n ^ 3 := le_self_pow₀ hN (by norm_num)
  have h2 : (n : ℝ) ^ 3 ≤ 80 * n ^ 3 * 2 ^ n / δ := by
    rw [le_div_iff₀ hδ]
    have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have : 0 ≤ (n : ℝ) ^ 3 := by positivity
    nlinarith
  linarith [le_countBase' hn hR hδ hδ1]

theorem two_pow_le_countBase (hn : 1 ≤ n) (hpn : p ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) : (2 : ℝ) ^ p ≤ countBase n R δ := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (2 : ℝ) ^ p ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hpn
  have h2 : (2 : ℝ) ^ n ≤ 80 * n ^ 3 * 2 ^ n / δ := by
    rw [le_div_iff₀ hδ]
    have : (1 : ℝ) ≤ n ^ 3 := one_le_pow₀ hN
    have : 0 ≤ (2 : ℝ) ^ n := by positivity
    nlinarith
  linarith [le_countBase' hn hR hδ hδ1]

theorem inv_gapEps_le (hn : 1 ≤ n) (hp : 1 ≤ p) (hpn : p ≤ n) (hδ : 0 < δ) :
    (gapEps p (δ / (2 * n)))⁻¹ ≤ 80 * (n : ℝ) ^ 3 * 2 ^ n / δ := by
  have hpn' : (p : ℝ) ≤ n := by exact_mod_cast hpn
  rw [gapEps_eq, inv_div]
  refine div_le_div_of_nonneg_right ?_ hδ.le
  calc 80 * (n : ℝ) * (p : ℝ) ^ 2 * (2 : ℝ) ^ p ≤ 80 * (n : ℝ) * (n : ℝ) ^ 2 * (2 : ℝ) ^ n := by
        gcongr
        exact one_le_two
    _ = 80 * (n : ℝ) ^ 3 * 2 ^ n := by ring

theorem inv_div_le_countBase (hn : 1 ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (δ / (2 * n))⁻¹ ≤ countBase n R δ := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [inv_div]
  have h : 2 * (n : ℝ) / δ ≤ 80 * n ^ 3 * 2 ^ n / δ := by
    refine div_le_div_of_nonneg_right ?_ hδ.le
    have h1 : (n : ℝ) ≤ n ^ 3 := le_self_pow₀ hN (by norm_num)
    have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have : 0 ≤ (n : ℝ) ^ 3 := by positivity
    nlinarith
  linarith [le_countBase' hn hR hδ hδ1]

theorem pow_gapBlocks_le (hn : 2 ≤ n) (hp : 1 ≤ p) (hpn : p ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    ((gapBlocks p (R ^ n) (δ / (2 * n)) : ℝ) * (gapEps p (δ / (2 * n)))⁻¹) ^
      gapBlocks p (R ^ n) (δ / (2 * n)) ≤ countBase n R δ ^ chainBound n R δ := by
  have hn1 : 1 ≤ n := by omega
  have hm := gapBlocks_le_chainBound hn hp hpn hR hδ hδ1
  have hε := inv_gapEps_le hn1 hp hpn hδ
  have hε0 : 0 < gapEps p (δ / (2 * n)) := gapEps_pos hp (by positivity)
  have hY := le_countBase hn1 hR hδ hδ1
  have hY1 := one_le_countBase hn1 hR hδ hδ1
  have hb : (gapBlocks p (R ^ n) (δ / (2 * n)) : ℝ) * (gapEps p (δ / (2 * n)))⁻¹ ≤
      countBase n R δ := by
    have : (gapBlocks p (R ^ n) (δ / (2 * n)) : ℝ) * (gapEps p (δ / (2 * n)))⁻¹ ≤
        chainBound n R δ * (80 * (n : ℝ) ^ 3 * 2 ^ n / δ) :=
      mul_le_mul hm hε (by positivity) (by linarith [two_le_chainBound hn1 hR hδ hδ1])
    linarith
  calc _ ≤ countBase n R δ ^ gapBlocks p (R ^ n) (δ / (2 * n)) :=
        pow_le_pow_left₀ (by positivity) hb _
    _ = countBase n R δ ^ ((gapBlocks p (R ^ n) (δ / (2 * n)) : ℕ) : ℝ) :=
        (Real.rpow_natCast _ _).symm
    _ ≤ countBase n R δ ^ chainBound n R δ := Real.rpow_le_rpow_of_exponent_le hY1 hm

theorem cast_pow_le_heightBase (hn : 1 ≤ n) (hpn : p ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) : (((R ^ n : ℕ) : ℝ)) ^ p ≤ (64 * (n : ℝ) * R / δ) ^ (n ^ 2) := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hBR : (R : ℝ) ≤ 64 * n * R / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith
  rw [Nat.cast_pow, ← pow_mul, sq]
  calc (R : ℝ) ^ (n * p) ≤ R ^ (n * n) := pow_le_pow_right₀ hR1 (Nat.mul_le_mul_left _ hpn)
    _ ≤ (64 * (n : ℝ) * R / δ) ^ (n * n) := pow_le_pow_left₀ (by linarith) hBR _

theorem one_add_le_heightBase (hn : 1 ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 + (8 * (R : ℝ)) ^ n * (Real.log 2 + 1) ≤ 3 * (64 * (n : ℝ) * R / δ) ^ (n ^ 2) := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hB1 := one_le_heightBase hn hR hδ hδ1
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have h8 : 8 * (R : ℝ) ≤ 64 * n * R / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith
  have hnn : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
  have h8n : (8 * (R : ℝ)) ^ n ≤ (64 * (n : ℝ) * R / δ) ^ (n ^ 2) :=
    (pow_le_pow_left₀ (by positivity) h8 n).trans (pow_le_pow_right₀ hB1 hnn)
  have h1 : (1 : ℝ) ≤ (8 * R) ^ n := one_le_pow₀ (by linarith)
  nlinarith

private theorem prod_le_of_le {a g X m P E D u Y W B : ℝ} (ha : 0 ≤ a) (hg : 0 ≤ g)
    (hX : 0 ≤ X) (hm : 0 ≤ m) (hP : 0 ≤ P) (hE : 0 ≤ E) (hD : 0 ≤ D) (hu : 0 ≤ u)
    (h1 : a ≤ Y) (h2 : g ≤ Y) (h3 : X ≤ B) (h4 : m ≤ Y) (h5 : P ≤ W) (h6 : E ≤ Y) (h7 : D ≤ Y)
    (h8 : u ≤ 3 * B) :
    200 * (a ^ 7 * g ^ 3 * X ^ 2 * m ^ 3 * P * E * D) * u ≤ 600 * (Y ^ 15 * W * B ^ 3) := by
  have hY0 : 0 ≤ Y := ha.trans h1
  have hW0 : 0 ≤ W := hP.trans h5
  have hB0 : 0 ≤ B := hX.trans h3
  calc 200 * (a ^ 7 * g ^ 3 * X ^ 2 * m ^ 3 * P * E * D) * u
      ≤ 200 * (Y ^ 7 * Y ^ 3 * B ^ 2 * Y ^ 3 * W * Y * Y) * (3 * B) := by
        gcongr
    _ = 600 * (Y ^ 15 * W * B ^ 3) := by ring

/-- **The threshold of Theorem 8.1 for a quotient** with `p ≤ n` variables, `Rⁿ` forms, `δ / 2n`
and `ℓ = (8R)ⁿ (log 2 + 1)`: at most `600 Y^{15} Y^{M} B^{3n²}`. -/
theorem gapThreshold_quot_le (hn : 2 ≤ n) (hp : 1 ≤ p) (hpn : p ≤ n) (hR : 1 ≤ R)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    gapThreshold p (R ^ n) (δ / (2 * n)) ((8 * R) ^ n * (Real.log 2 + 1)) ≤
      600 * (countBase n R δ ^ 15 * countBase n R δ ^ chainBound n R δ *
        ((64 * (n : ℝ) * R / δ) ^ (n ^ 2)) ^ 3) := by
  have hn1 : 1 ≤ n := by omega
  have hδ' : 0 < δ / (2 * n) := by positivity
  have hδ'1 : δ / (2 * n) ≤ 1 := by
    have : (2 : ℝ) ≤ 2 * n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      linarith
    rw [div_le_one (by positivity)]
    linarith
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hℓ : 0 ≤ (8 * (R : ℝ)) ^ n * (Real.log 2 + 1) := by positivity
  have hε0 : 0 < gapEps p (δ / (2 * n)) := gapEps_pos hp hδ'
  refine (gapThreshold_le (n := p) (R := R ^ n) hp (Nat.one_le_pow _ _ hR) hδ' hδ'1 hℓ).trans ?_
  refine prod_le_of_le (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (cast_le_countBase hn1 hpn hR hδ hδ1) (two_pow_le_countBase hn1 hpn hR hδ hδ1)
    (cast_pow_le_heightBase hn1 hpn hR hδ hδ1)
    ((gapBlocks_le_chainBound hn hp hpn hR hδ hδ1).trans (chainBound_le_countBase hn1 hR hδ hδ1))
    (pow_gapBlocks_le hn hp hpn hR hδ hδ1)
    ((inv_gapEps_le hn1 hp hpn hδ).trans (le_countBase' hn1 hR hδ hδ1))
    (inv_div_le_countBase hn1 hR hδ hδ1) (one_add_le_heightBase hn1 hR hδ hδ1)

end Quotients

/-! ### The threshold ratio -/

section Bound

variable {n R : ℕ} {δ : ℝ}

/-- `V = Y^{15} Y^{M} (B^{n²})³ ≥ 1`. -/
theorem one_le_quotBase (hn : 1 ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ countBase n R δ ^ 15 * countBase n R δ ^ chainBound n R δ *
      ((64 * (n : ℝ) * R / δ) ^ (n ^ 2)) ^ 3 := by
  have hY := one_le_countBase hn hR hδ hδ1
  have hB := one_le_heightBase hn hR hδ hδ1
  have hm : 0 ≤ chainBound n R δ := by linarith [two_le_chainBound hn hR hδ hδ1]
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hY)
    (Real.one_le_rpow hY hm)) (one_le_pow₀ (one_le_pow₀ hB))

theorem quotTerm₂_le (hn : 1 ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    2 * n / δ * (Real.log n + (4 * R) ^ n * (Real.log 2 + 1) + 1) ≤
      4 * (countBase n R δ * (64 * (n : ℝ) * R / δ) ^ (n ^ 2)) := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hB1 := one_le_heightBase hn hR hδ hδ1
  have hY := inv_div_le_countBase hn hR hδ hδ1
  rw [inv_div] at hY
  set B : ℝ := 64 * n * R / δ
  have hnn : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
  have hBn : B ≤ B ^ (n ^ 2) := le_self_pow₀ hB1 (by positivity)
  have hnB : (n : ℝ) ≤ B := by
    simp only [B]
    rw [le_div_iff₀ hδ]
    nlinarith
  have h4 : (4 * (R : ℝ)) ^ n ≤ B ^ (n ^ 2) := by
    have : 4 * (R : ℝ) ≤ B := by
      simp only [B]
      rw [le_div_iff₀ hδ]
      nlinarith
    exact (pow_le_pow_left₀ (by positivity) this n).trans (pow_le_pow_right₀ hB1 hnn)
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hlogn : Real.log n ≤ n := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hln0 : 0 ≤ Real.log n := Real.log_nonneg hN
  have hinner : Real.log n + (4 * R) ^ n * (Real.log 2 + 1) + 1 ≤ 4 * B ^ (n ^ 2) := by
    have : (4 * (R : ℝ)) ^ n * (Real.log 2 + 1) ≤ 2 * B ^ (n ^ 2) := by nlinarith
    have : (1 : ℝ) ≤ B ^ (n ^ 2) := one_le_pow₀ hB1
    linarith
  have h2n : 0 ≤ 2 * (n : ℝ) / δ := by positivity
  calc 2 * n / δ * (Real.log n + (4 * R) ^ n * (Real.log 2 + 1) + 1)
      ≤ countBase n R δ * (4 * B ^ (n ^ 2)) := mul_le_mul hY hinner (by positivity)
        (zero_le_one.trans (one_le_countBase hn hR hδ hδ1))
    _ = 4 * (countBase n R δ * B ^ (n ^ 2)) := by ring

theorem quotTerm₃_le (hn : 1 ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    2 * n / δ * ((8 * R) ^ n * R ^ n * (Real.log 2 + 1)) ≤
      2 * (countBase n R δ * ((64 * (n : ℝ) * R / δ) ^ (n ^ 2)) ^ 2) := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hB1 := one_le_heightBase hn hR hδ hδ1
  have hY := inv_div_le_countBase hn hR hδ hδ1
  rw [inv_div] at hY
  set B : ℝ := 64 * n * R / δ
  have hnn : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
  have h8 : (8 * (R : ℝ)) ^ n * R ^ n ≤ (B ^ (n ^ 2)) ^ 2 := by
    have hRB : 8 * (R : ℝ) ≤ B := by
      simp only [B]
      rw [le_div_iff₀ hδ]
      nlinarith
    have hRB' : (R : ℝ) ≤ B := by linarith
    have hBn : B ^ n ≤ B ^ (n ^ 2) := pow_le_pow_right₀ hB1 hnn
    calc (8 * (R : ℝ)) ^ n * R ^ n ≤ B ^ n * B ^ n :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hRB n)
            (pow_le_pow_left₀ (by positivity) hRB' n) (by positivity) (by positivity)
      _ ≤ B ^ (n ^ 2) * B ^ (n ^ 2) := mul_le_mul hBn hBn (by positivity) (by positivity)
      _ = (B ^ (n ^ 2)) ^ 2 := by ring
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hinner : (8 * (R : ℝ)) ^ n * R ^ n * (Real.log 2 + 1) ≤ 2 * (B ^ (n ^ 2)) ^ 2 := by
    have : 0 ≤ (8 * (R : ℝ)) ^ n * R ^ n := by positivity
    nlinarith
  calc 2 * n / δ * ((8 * R) ^ n * R ^ n * (Real.log 2 + 1))
      ≤ countBase n R δ * (2 * (B ^ (n ^ 2)) ^ 2) := mul_le_mul hY hinner (by positivity)
        (zero_le_one.trans (one_le_countBase hn hR hδ hδ1))
    _ = 2 * (countBase n R δ * (B ^ (n ^ 2)) ^ 2) := by ring

/-- **The threshold at `ℓ = 1`** is at most `(600 n + 7) V`. -/
theorem quotThreshold_one_le (hn : 2 ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    quotThreshold n R δ 1 ≤ (600 * n + 7) * (countBase n R δ ^ 15 *
      countBase n R δ ^ chainBound n R δ * ((64 * (n : ℝ) * R / δ) ^ (n ^ 2)) ^ 3) := by
  have hn1 : 1 ≤ n := by omega
  set V := countBase n R δ ^ 15 * countBase n R δ ^ chainBound n R δ *
    ((64 * (n : ℝ) * R / δ) ^ (n ^ 2)) ^ 3 with hV
  set Y := countBase n R δ
  set B := (64 * (n : ℝ) * R / δ) ^ (n ^ 2)
  have hY1 : 1 ≤ Y := one_le_countBase hn1 hR hδ hδ1
  have hB1 : 1 ≤ B := one_le_pow₀ (one_le_heightBase hn1 hR hδ hδ1)
  have hW1 : 1 ≤ Y ^ chainBound n R δ :=
    Real.one_le_rpow hY1 (by linarith [two_le_chainBound hn1 hR hδ hδ1])
  have hV1 : 1 ≤ V := one_le_quotBase hn1 hR hδ hδ1
  have hYV : Y * B ≤ V := by
    have h1 : Y ≤ Y ^ 15 := le_self_pow₀ hY1 (by norm_num)
    have h2 : B ≤ B ^ 3 := le_self_pow₀ hB1 (by norm_num)
    calc Y * B = Y * 1 * B := by ring
      _ ≤ Y ^ 15 * Y ^ chainBound n R δ * B ^ 3 := by gcongr
  have hYV2 : Y * B ^ 2 ≤ V := by
    have h1 : Y ≤ Y ^ 15 := le_self_pow₀ hY1 (by norm_num)
    have h2 : B ^ 2 ≤ B ^ 3 := pow_le_pow_right₀ hB1 (by norm_num)
    calc Y * B ^ 2 = Y * 1 * B ^ 2 := by ring
      _ ≤ Y ^ 15 * Y ^ chainBound n R δ * B ^ 3 := by gcongr
  have hsum : ∑ p ∈ Icc 1 n, gapThreshold p (R ^ n) (δ / (2 * n)) ((8 * R) ^ n *
      (Real.log 2 + 1)) ≤ n * (600 * V) := by
    calc _ ≤ ∑ _p ∈ Icc 1 n, 600 * V := sum_le_sum fun p hp ↦
          gapThreshold_quot_le hn (mem_Icc.1 hp).1 (mem_Icc.1 hp).2 hR hδ hδ1
      _ = n * (600 * V) := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
  have h2 := quotTerm₂_le hn1 hR hδ hδ1
  have h3 := quotTerm₃_le hn1 hR hδ hδ1
  rw [quotThreshold]
  nlinarith

/-- `δ / log 2 ≤ 2`. -/
theorem div_log_two_le (hδ1 : δ ≤ 1) : δ / Real.log 2 ≤ 2 := by
  have h := Real.log_two_gt_d9
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **`intervalBound ≤ (R + 2) · quotThreshold n R δ 1`**, and it is at least `1`. -/
theorem intervalBound_le (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    intervalBound n R δ ≤ (R + 2) * quotThreshold n R δ 1 := by
  have h0 := quotThreshold_pos (R := R) hn hδ (le_refl (0 : ℝ))
  have hmono := quotThreshold_mono (R := R) hn hδ (zero_le_one : (0 : ℝ) ≤ 1)
  have hd := div_log_two_le hδ1
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  rw [intervalBound, mul_div_assoc]
  nlinarith

theorem one_le_intervalBound (hn : 1 ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ) :
    1 ≤ intervalBound n R δ := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have h3 := (terms_le_quotThreshold (R := R) hn le_rfl hδ (le_refl (0 : ℝ))).2.2
  have hmono := quotThreshold_mono (R := R) hn hδ (zero_le_one : (0 : ℝ) ≤ 1)
  have hl2 := Real.log_two_gt_d9
  have h8 : (1 : ℝ) ≤ (8 * R) ^ n * R ^ n :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ hR1)
  rw [intervalBound]
  have hR2 : 0 ≤ (R : ℝ) * (quotThreshold n R δ 1 - quotThreshold n R δ 0) :=
    mul_nonneg (by linarith) (by linarith)
  have hq : 2 * n / δ * Real.log 2 ≤ quotThreshold n R δ 0 := by
    refine le_trans ?_ h3.le
    rw [add_zero]
    have hpos : 0 ≤ 2 * n / δ * Real.log 2 := by positivity
    calc 2 * n / δ * Real.log 2 = 2 * n / δ * (1 * Real.log 2) := by ring
      _ ≤ 2 * n / δ * ((8 * R) ^ n * R ^ n * Real.log 2) := by gcongr
  have : 1 ≤ quotThreshold n R δ 0 * δ / Real.log 2 := by
    rw [le_div_iff₀ (by linarith), one_mul]
    have e : 2 * n / δ * Real.log 2 * δ = 2 * n * Real.log 2 := by field_simp
    have := mul_le_mul_of_nonneg_right hq hδ.le
    nlinarith
  linarith

end Bound

/-! ### The closed form -/

section ClosedForm

variable {n R : ℕ} {δ : ℝ}

theorem one_le_log_heightBase (hn : 2 ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ Real.log (64 * (n : ℝ) * R / δ) := by
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  rw [Real.le_log_iff_exp_le (by positivity)]
  have he := Real.exp_one_lt_d9
  have : (3 : ℝ) ≤ 64 * n * R / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith
  linarith

theorem sixteen_le_chainBound (hn : 2 ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    16 ≤ chainBound n R δ := by
  have h := sq_mul_log_le_chainBound (by omega : 1 ≤ n) hR hδ hδ1
  have hl := one_le_log_heightBase hn hR hδ hδ1
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : (16 : ℝ) ≤ 4 * n ^ 2 := by nlinarith
  nlinarith

/-- **`log intervalBound ≤ 3 M μ`**. -/
theorem log_intervalBound_le (hn : 2 ≤ n) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.log (intervalBound n R δ) ≤ 3 * chainBound n R δ * countLog n R δ := by
  have hn1 : 1 ≤ n := by omega
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  set Y := countBase n R δ with hY
  set B : ℝ := 64 * n * R / δ with hB
  set mb := chainBound n R δ with hmb
  have hY1 : 1 ≤ Y := one_le_countBase hn1 hR hδ hδ1
  have hB1 : 1 ≤ B := one_le_heightBase hn1 hR hδ hδ1
  have hmb16 : 16 ≤ mb := sixteen_le_chainBound hn hR hδ hδ1
  have hμ : 1 ≤ countLog n R δ := one_le_countLog hn1 hR hδ hδ1
  have hlam := sq_mul_log_le_chainBound hn1 hR hδ hδ1
  have hlam0 : 0 ≤ Real.log B := Real.log_nonneg hB1
  -- `intervalBound ≤ B Y V`
  have hRB : (R : ℝ) + 2 ≤ B := by
    rw [hB, le_div_iff₀ hδ]
    nlinarith
  have hnY : 600 * (n : ℝ) + 7 ≤ Y := by
    have h := le_countBase' hn1 hR hδ hδ1
    have h8 : (8 : ℝ) ≤ n ^ 3 := by nlinarith
    have h4 : (4 : ℝ) ≤ 2 ^ n := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have hK : 80 * (n : ℝ) ^ 3 * 2 ^ n ≤ 80 * n ^ 3 * 2 ^ n / δ := by
      rw [le_div_iff₀ hδ]
      have : 0 ≤ 80 * (n : ℝ) ^ 3 * 2 ^ n := by positivity
      nlinarith
    have : 600 * (n : ℝ) + 7 ≤ 80 * n ^ 3 * 2 ^ n := by nlinarith
    linarith
  have hV1 := one_le_quotBase hn1 hR hδ hδ1
  have hq := quotThreshold_one_le hn hR hδ hδ1
  have hib := intervalBound_le (R := R) hn1 hδ hδ1
  have hib1 := one_le_intervalBound hn1 hR hδ
  have hq0 : 0 ≤ quotThreshold n R δ 1 := (quotThreshold_pos hn1 hδ zero_le_one).le
  have hbound : intervalBound n R δ ≤
      B * Y * (Y ^ 15 * Y ^ mb * (B ^ (n ^ 2)) ^ 3) := by
    calc intervalBound n R δ ≤ (R + 2) * quotThreshold n R δ 1 := hib
      _ ≤ B * ((600 * n + 7) * (Y ^ 15 * Y ^ mb * (B ^ (n ^ 2)) ^ 3)) :=
          mul_le_mul hRB hq hq0 (by positivity)
      _ ≤ B * (Y * (Y ^ 15 * Y ^ mb * (B ^ (n ^ 2)) ^ 3)) := by gcongr
      _ = B * Y * (Y ^ 15 * Y ^ mb * (B ^ (n ^ 2)) ^ 3) := by ring
  have hY0 : 0 < Y := zero_lt_one.trans_le hY1
  have hB0 : 0 < B := zero_lt_one.trans_le hB1
  have hlog : Real.log (B * Y * (Y ^ 15 * Y ^ mb * (B ^ (n ^ 2)) ^ 3)) =
      (3 * n ^ 2 + 1) * Real.log B + (16 + mb) * Real.log Y := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_rpow hY0, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlY : Real.log Y = countLog n R δ := rfl
  calc Real.log (intervalBound n R δ)
      ≤ Real.log (B * Y * (Y ^ 15 * Y ^ mb * (B ^ (n ^ 2)) ^ 3)) :=
        Real.log_le_log (by linarith) hbound
    _ = (3 * n ^ 2 + 1) * Real.log B + (16 + mb) * countLog n R δ := by rw [hlog, hlY]
    _ ≤ 3 * mb * countLog n R δ := by
        have h1 : (3 * (n : ℝ) ^ 2 + 1) * Real.log B ≤ mb := by
          have : (1 : ℝ) ≤ n ^ 2 := by nlinarith
          nlinarith
        have h2 : mb ≤ mb * countLog n R δ := le_mul_of_one_le_right (by linarith) hμ
        nlinarith

/-- `2 ω = 8 m / ε ≤ Y` for every quotient. -/
theorem two_gapRatio_le (hn : 2 ≤ n) {p : ℕ} (hp : 1 ≤ p) (hpn : p ≤ n) (hR : 1 ≤ R)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    2 * gapRatio p (R ^ n) (δ / (2 * n)) ≤ countBase n R δ := by
  have hn1 : 1 ≤ n := by omega
  have hm := gapBlocks_le_chainBound hn hp hpn hR hδ hδ1
  have hε := inv_gapEps_le hn1 hp hpn hδ
  have hε0 : 0 < gapEps p (δ / (2 * n)) := gapEps_pos hp (by positivity)
  have e : countBase n R δ = 8 * (chainBound n R δ * (80 * (n : ℝ) ^ 3 * 2 ^ n / δ)) := by
    rw [countBase]
    ring
  rw [gapRatio, e, div_eq_mul_inv]
  have : (gapBlocks p (R ^ n) (δ / (2 * n)) : ℝ) * (gapEps p (δ / (2 * n)))⁻¹ ≤
      chainBound n R δ * (80 * (n : ℝ) ^ 3 * 2 ^ n / δ) :=
    mul_le_mul hm hε (by positivity) (by linarith [two_le_chainBound hn1 hR hδ hδ1])
  nlinarith

/-- **The intervals of Theorem 8.1 for one quotient**, cut: at most `n M (μ / log ω₀ + 1)`. -/
theorem gapIntervals_mul_cutCount_le (hn : 2 ≤ n) {p : ℕ} (hp : 1 ≤ p) (hpn : p ≤ n)
    (hR : 2 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((gapIntervals p (R ^ n) (δ / (2 * n)) *
        Real.cutCount (2 * gapRatio p (R ^ n) (δ / (2 * n))) (cutRatio R δ) : ℕ) : ℝ) ≤
      n * chainBound n R δ * (countLog n R δ / Real.log (cutRatio R δ) + 1) := by
  have hn1 : 1 ≤ n := by omega
  have hR1 : 1 ≤ R := by omega
  have hm := gapBlocks_le_chainBound hn hp hpn hR1 hδ hδ1
  have hgi : (gapIntervals p (R ^ n) (δ / (2 * n)) : ℝ) ≤ n * chainBound n R δ := by
    have hle : gapIntervals p (R ^ n) (δ / (2 * n)) ≤ n * gapBlocks p (R ^ n) (δ / (2 * n)) := by
      rw [gapIntervals, gapBlocks]
      exact Nat.mul_le_mul (by omega) (Nat.le_succ _)
    calc (gapIntervals p (R ^ n) (δ / (2 * n)) : ℝ)
        ≤ ((n * gapBlocks p (R ^ n) (δ / (2 * n)) : ℕ) : ℝ) := by exact_mod_cast hle
      _ = n * (gapBlocks p (R ^ n) (δ / (2 * n)) : ℝ) := by push_cast; ring
      _ ≤ n * chainBound n R δ := by gcongr
  have hratio := two_gapRatio_le hn hp hpn hR1 hδ hδ1
  have hm1 : (1 : ℝ) ≤ gapBlocks p (R ^ n) (δ / (2 * n)) := by
    have : 1 ≤ gapBlocks p (R ^ n) (δ / (2 * n)) := Nat.le_add_left 1 _
    exact_mod_cast this
  have hε0 : 0 < gapEps p (δ / (2 * n)) := gapEps_pos hp (by positivity)
  have hε1 : gapEps p (δ / (2 * n)) ≤ 1 := gapEps_le_one hp (by
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith)
  have hr1 : 1 ≤ 2 * gapRatio p (R ^ n) (δ / (2 * n)) := by
    rw [gapRatio]
    have : (gapBlocks p (R ^ n) (δ / (2 * n)) : ℝ) ≤
        4 * (gapBlocks p (R ^ n) (δ / (2 * n)) : ℝ) / gapEps p (δ / (2 * n)) := by
      rw [le_div_iff₀ hε0]
      nlinarith
    linarith
  have hω := one_lt_cutRatio hR hδ hδ1
  have hlω := Real.log_pos hω
  have hcut := Real.cutCount_le_div hr1 hω
  have hcut' : (Real.cutCount (2 * gapRatio p (R ^ n) (δ / (2 * n))) (cutRatio R δ) : ℝ) ≤
      countLog n R δ / Real.log (cutRatio R δ) + 1 := by
    have : Real.log (2 * gapRatio p (R ^ n) (δ / (2 * n))) ≤ countLog n R δ :=
      Real.log_le_log (by linarith) hratio
    have := div_le_div_of_nonneg_right this hlω.le
    linarith
  have hμ0 : 0 ≤ countLog n R δ / Real.log (cutRatio R δ) :=
    div_nonneg (by linarith [one_le_countLog hn1 hR1 hδ hδ1]) hlω.le
  push_cast
  exact mul_le_mul hgi hcut' (Nat.cast_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (by linarith [two_le_chainBound hn1 hR1 hδ hδ1]))

/-- **The closed form for the number of intervals of Theorem 2.3, with `log ω₀`**:
`intervalCount n R δ ≤ (n + 3) M (μ / log ω₀ + 1)` with `M = 64000 n⁸ 4ⁿ δ⁻² log(64 n R / δ) + 2`,
`μ = log(640 n³ 2ⁿ M / δ)` and `ω₀ = δ⁻¹ log 3R`. -/
theorem intervalCount_le_div (hn : 2 ≤ n) (hR : 2 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (intervalCount n R δ : ℝ) ≤
      (n + 3) * chainBound n R δ * (countLog n R δ / Real.log (cutRatio R δ) + 1) := by
  have hn1 : 1 ≤ n := by omega
  have hR1 : 1 ≤ R := by omega
  have hmb := two_le_chainBound hn1 hR1 hδ hδ1
  have hμ := one_le_countLog hn1 hR1 hδ hδ1
  have hω := one_lt_cutRatio hR hδ hδ1
  have hlω := Real.log_pos hω
  set lam := Real.log (cutRatio R δ) with hlam
  set x := countLog n R δ / lam with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hlω.le
  have hcut := Real.cutCount_le_div (one_le_intervalBound hn1 hR1 hδ) hω
  have hlog := log_intervalBound_le hn hR1 hδ hδ1
  have hcut' : (Real.cutCount (intervalBound n R δ) (cutRatio R δ) : ℝ) ≤
      3 * chainBound n R δ * x + 1 := by
    have h := div_le_div_of_nonneg_right hlog hlω.le
    have e : 3 * chainBound n R δ * countLog n R δ / lam = 3 * chainBound n R δ * x := by
      rw [hx, mul_div_assoc]
    linarith
  obtain ⟨p, hp, hpeq⟩ := exists_mem_eq_sup (Icc 1 n) (nonempty_Icc.2 hn1)
    fun p ↦ gapIntervals p (R ^ n) (δ / (2 * n)) *
      Real.cutCount (2 * gapRatio p (R ^ n) (δ / (2 * n))) (cutRatio R δ)
  have hsup := gapIntervals_mul_cutCount_le hn (mem_Icc.1 hp).1 (mem_Icc.1 hp).2 hR hδ hδ1
  rw [intervalCount, Nat.cast_add, hpeq]
  rw [← hx] at hsup
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith

/-- **The constant `2744320000 n¹² 8ⁿ`** with `Y ≤ c ω₀⁴` (`countBase_le`). -/
noncomputable def countConst (n : ℕ) : ℝ := 2744320000 * n ^ 12 * 8 ^ n

/-- `log(64 n R / δ) ≤ 66 n ω₀`. -/
theorem log_heightBase_le (hn : 1 ≤ n) (hR : 2 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.log (64 * (n : ℝ) * R / δ) ≤ 66 * n * cutRatio R δ := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR2 : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hL3 : 1 ≤ Real.log (3 * R) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    linarith [Real.exp_one_lt_d9]
  have hD : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hω : 1 / δ ≤ cutRatio R δ := by
    rw [cutRatio, div_le_div_iff_of_pos_right hδ]; exact hL3
  have hL3ω : Real.log (3 * R) ≤ cutRatio R δ := by
    rw [cutRatio, le_div_iff₀ hδ]; nlinarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 3 * R)]
  have e : 64 * (n : ℝ) * R / δ = (64 * n / 3) * (3 * R) * (1 / δ) := by field_simp
  rw [e, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have h1 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 64 * n / 3)
  have h3 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 / δ)
  have hω1 : 1 ≤ cutRatio R δ := hD.trans hω
  nlinarith

/-- `Y ≤ 2744320000 n¹² 8ⁿ ω₀⁴`, over abstract reals. -/
private theorem countBase_le_aux {a P Q D ω ℓ : ℝ} (ha : 1 ≤ a) (hP : 1 ≤ P) (hQ : 1 ≤ Q)
    (hD : 1 ≤ D) (hDω : D ≤ ω) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 66 * a * ω) :
    640 * a ^ 3 * Q * (64000 * a ^ 8 * P * D ^ 2 * ℓ + 2) * D ≤
      2744320000 * a ^ 12 * (Q * P) * ω ^ 4 := by
  have hω1 : 1 ≤ ω := hD.trans hDω
  have hD2 : D ^ 2 ≤ ω ^ 2 := pow_le_pow_left₀ (by linarith) hDω 2
  have hDℓ : D ^ 2 * ℓ ≤ 66 * a * ω ^ 3 := by
    calc D ^ 2 * ℓ ≤ ω ^ 2 * (66 * a * ω) := mul_le_mul hD2 hℓ hℓ0 (by positivity)
      _ = 66 * a * ω ^ 3 := by ring
  have ha9 : 1 ≤ a ^ 9 := one_le_pow₀ ha
  have hω3 : 1 ≤ ω ^ 3 := one_le_pow₀ hω1
  have h1 : 64000 * a ^ 8 * P * D ^ 2 * ℓ + 2 ≤ 64000 * 67 * a ^ 9 * P * ω ^ 3 := by
    have e : 64000 * a ^ 8 * P * D ^ 2 * ℓ = 64000 * a ^ 8 * P * (D ^ 2 * ℓ) := by ring
    have h2 : 64000 * a ^ 8 * P * (D ^ 2 * ℓ) ≤ 64000 * a ^ 8 * P * (66 * a * ω ^ 3) :=
      mul_le_mul_of_nonneg_left hDℓ (by positivity)
    have h3 : (2 : ℝ) ≤ 64000 * a ^ 9 * P * ω ^ 3 := by
      have : (1 : ℝ) ≤ a ^ 9 * P * ω ^ 3 :=
        one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ha9 hP) hω3
      nlinarith
    have e2 : 64000 * a ^ 8 * P * (66 * a * ω ^ 3) = 64000 * 66 * a ^ 9 * P * ω ^ 3 := by ring
    nlinarith
  calc 640 * a ^ 3 * Q * (64000 * a ^ 8 * P * D ^ 2 * ℓ + 2) * D
      ≤ 640 * a ^ 3 * Q * (64000 * 67 * a ^ 9 * P * ω ^ 3) * ω := by
        gcongr
    _ = 2744320000 * a ^ 12 * (Q * P) * ω ^ 4 := by ring

/-- **`Y ≤ 2744320000 n¹² 8ⁿ ω₀⁴`**: the base of the count is polynomial in `ω₀ = δ⁻¹ log 3R`
with a coefficient depending on `n` only. -/
theorem countBase_le (hn : 1 ≤ n) (hR : 2 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    countBase n R δ ≤ countConst n * cutRatio R δ ^ 4 := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hR2 : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hL3 : 1 ≤ Real.log (3 * R) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    linarith [Real.exp_one_lt_d9]
  have hω : 1 / δ ≤ cutRatio R δ := by
    rw [cutRatio, div_le_div_iff_of_pos_right hδ]; exact hL3
  have h := countBase_le_aux (P := (4 : ℝ) ^ n) (Q := (2 : ℝ) ^ n) hN
    (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num)) hD hω
    (log_heightBase_nonneg hn (by omega) hδ hδ1)
    (log_heightBase_le hn hR hδ hδ1)
  have e1 : countBase n R δ = 640 * (n : ℝ) ^ 3 * 2 ^ n * (64000 * n ^ 8 * 4 ^ n * (1 / δ) ^ 2 *
      Real.log (64 * n * R / δ) + 2) * (1 / δ) := by
    rw [countBase, chainBound]
    field_simp
  have e2 : countConst n * cutRatio R δ ^ 4 =
      2744320000 * (n : ℝ) ^ 12 * (2 ^ n * 4 ^ n) * cutRatio R δ ^ 4 := by
    rw [countConst, ← mul_pow]
    norm_num
  rw [e1, e2]
  exact h

theorem one_le_countConst (hn : 1 ≤ n) : 1 ≤ countConst n := by
  rw [countConst]
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (1 : ℝ) ≤ n ^ 12 * 8 ^ n :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN) (one_le_pow₀ (by norm_num))
  nlinarith

/-- **`μ / log ω₀ + 1 ≤ 2 log c + 5`**, `c = 2744320000 n¹² 8ⁿ`: the factor that EF13 bound by
`log m* / log(δ⁻¹ log 3R) ≤ O(n)` in §18. -/
theorem countLog_div_add_one_le (hn : 1 ≤ n) (hR : 2 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    countLog n R δ / Real.log (cutRatio R δ) + 1 ≤ 2 * Real.log (countConst n) + 5 := by
  have hω := one_lt_cutRatio hR hδ hδ1
  have hlω := half_le_log_cutRatio hR hδ hδ1
  have hc := one_le_countConst hn
  have hlc := Real.log_nonneg hc
  have hY := countBase_le hn hR hδ hδ1
  have hμ : countLog n R δ ≤ Real.log (countConst n) + 4 * Real.log (cutRatio R δ) := by
    rw [countLog]
    calc Real.log (countBase n R δ) ≤ Real.log (countConst n * cutRatio R δ ^ 4) :=
          Real.log_le_log (zero_lt_one.trans_le (one_le_countBase hn (by omega) hδ hδ1)) hY
      _ = _ := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
          push_cast
          ring
  have hl0 : 0 < Real.log (cutRatio R δ) := by linarith
  rw [div_add_one hl0.ne', div_le_iff₀ hl0]
  nlinarith

/-- `2 log(2744320000 n¹² 8ⁿ) + 5 ≤ 60 n`. -/
theorem two_log_countConst_add_five_le (hn : 1 ≤ n) :
    2 * Real.log (countConst n) + 5 ≤ 60 * n := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 := Real.log_two_lt_d9
  have hlog : Real.log (countConst n) =
      Real.log 2744320000 + 12 * Real.log n + n * (3 * Real.log 2) := by
    rw [countConst, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    rw [this]
    push_cast
    ring
  have hc : Real.log 2744320000 ≤ 32 * Real.log 2 := by
    calc Real.log 2744320000 ≤ Real.log (2 ^ 32) := Real.log_le_log (by norm_num) (by norm_num)
      _ = 32 * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
  have hn' := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hN)
  rw [hlog]
  nlinarith

/-- **The closed form for the number of intervals of Theorem 2.3**:
`intervalCount n R δ ≤ 60 n (n + 3) M` with `M = 64000 n⁸ 4ⁿ δ⁻² log(64 n R / δ) + 2`, i.e.
`O(n¹⁰ 4ⁿ δ⁻² log(nR/δ))`: EF13's `m₀ = 10⁵ 2^{2n} n^{10} δ⁻² log(3δ⁻¹R)` up to the constant. -/
theorem intervalCount_le (hn : 2 ≤ n) (hR : 2 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (intervalCount n R δ : ℝ) ≤ 60 * n * (n + 3) * chainBound n R δ := by
  have h := intervalCount_le_div hn hR hδ hδ1
  have h2 := (countLog_div_add_one_le (by omega) hR hδ hδ1).trans
    (two_log_countConst_add_five_le (n := n) (by omega))
  have hm := two_le_chainBound (n := n) (R := R) (by omega) (by omega) hδ hδ1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  calc (intervalCount n R δ : ℝ)
      ≤ (n + 3) * chainBound n R δ * (countLog n R δ / Real.log (cutRatio R δ) + 1) := h
    _ ≤ (n + 3) * chainBound n R δ * (60 * n) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg (by positivity) (by linarith))
    _ = 60 * n * (n + 3) * chainBound n R δ := by ring

end ClosedForm

end NumberField.FormSystem
