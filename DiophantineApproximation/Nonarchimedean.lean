/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Used only inside proofs.
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# When an absolute value is nonarchimedean, and what follows

Three facts about a real absolute value `w` of a field `F` that Layer 0.1 runs on and Mathlib
does not have:

* an absolute value **bounded by `1` on the natural numbers is nonarchimedean** — the binomial
  theorem and `n ^ (1 / n) → 1`, which is the one implication of Ostrowski's dichotomy that is
  not specific to `ℚ`;
* a nonarchimedean absolute value that is at most `1` on `ℤ` is at most `1` on every element
  **integral over `ℤ`**, so on the whole ring of integers of a number field;
* every **positive real power** of a nonarchimedean absolute value is again an absolute value.

The last is false for archimedean absolute values above the exponent `1` (`|·|^2` on `ℚ` fails the
triangle inequality at `1 + 1`), and the restriction is not cosmetic: the exponent that Layer 0.1
produces at a finite place is `(e f)⁻¹ ≤ 1`, but the route that produces it goes through an
equivalence whose exponent is not yet known to be at most `1`, so the construction has to be
available at every positive exponent.

## Main results

* `AbsoluteValue.isNonarchimedean_of_natCast_le_one`: bounded on `ℕ` implies nonarchimedean.
* `AbsoluteValue.le_one_of_isIntegral`: a nonarchimedean absolute value bounded by `1` on `ℤ` is
  bounded by `1` on the integral elements.
* `AbsoluteValue.nonarchRpow`: the `t`-th power of a nonarchimedean absolute value, `0 < t`.

## Implementation notes

`IsNonarchimedean` is stated for a bare function `α → R`, so it is applied here to the coercion
`(w : F → ℝ)` rather than to `w` itself; Mathlib's own `NumberField.FinitePlace` lemmas do the
same.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.2 and §1.3.

This is part of Layer 0.1 of the `DiophantineApproximation` roadmap.
-/

public section

open Filter

namespace AbsoluteValue

variable {F : Type*} [Field F]

/-- An absolute value that is at most `1` on every natural number is nonarchimedean.

The binomial theorem gives `w (x + y) ^ n ≤ (n + 1) * max (w x) (w y) ^ n`, because every binomial
coefficient is a natural number and so has absolute value at most `1`; the factor `n + 1` is
killed by letting `n` tend to infinity. -/
theorem isNonarchimedean_of_natCast_le_one {w : AbsoluteValue F ℝ}
    (h : ∀ n : ℕ, w (n : F) ≤ 1) : IsNonarchimedean (w : F → ℝ) := by
  intro x y
  set M := max (w x) (w y) with hM
  have hM0 : (0 : ℝ) ≤ M := le_trans (w.nonneg x) (le_max_left _ _)
  have key : ∀ n : ℕ, w (x + y) ^ (n + 1) ≤ (n + 2 : ℝ) * M ^ (n + 1) := by
    intro n
    rw [← map_pow, add_pow]
    refine le_trans (w.sum_le _ _) ?_
    have hb : ∀ k ∈ Finset.range (n + 2),
        w (x ^ k * y ^ (n + 1 - k) * ((n + 1).choose k : F)) ≤ M ^ (n + 1) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [map_mul, map_mul, map_pow, map_pow]
      have h1 : w x ^ k ≤ M ^ k := pow_le_pow_left₀ (w.nonneg x) (le_max_left _ _) k
      have h2 : w y ^ (n + 1 - k) ≤ M ^ (n + 1 - k) :=
        pow_le_pow_left₀ (w.nonneg y) (le_max_right _ _) _
      calc w x ^ k * w y ^ (n + 1 - k) * w ((n + 1).choose k : F)
          ≤ M ^ k * M ^ (n + 1 - k) * 1 :=
            mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity))
              (h _) (w.nonneg _) (by positivity)
        _ = M ^ (n + 1) := by rw [mul_one, ← pow_add]; congr 1; omega
    calc ∑ k ∈ Finset.range (n + 2), w (x ^ k * y ^ (n + 1 - k) * ((n + 1).choose k : F))
        ≤ ∑ _k ∈ Finset.range (n + 2), M ^ (n + 1) := Finset.sum_le_sum hb
      _ = (n + 2 : ℝ) * M ^ (n + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  by_contra hcon
  rw [not_le] at hcon
  have ha : 0 < w (x + y) := lt_of_le_of_lt hM0 hcon
  set q : ℝ := M / w (x + y) with hq
  have hq0 : 0 ≤ q := div_nonneg hM0 ha.le
  have hq1 : q < 1 := (div_lt_one ha).mpr hcon
  have hone : ∀ n : ℕ, (1 : ℝ) ≤ (n + 2 : ℝ) * q ^ (n + 1) := by
    intro n
    rw [hq, div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos ha _), one_mul]
    exact key n
  have habs : |q| < 1 := by rwa [abs_of_nonneg hq0]
  have hlim : Tendsto (fun n : ℕ => (n + 2 : ℝ) * q ^ (n + 1)) atTop (nhds 0) := by
    have h0 := ((tendsto_self_mul_const_pow_of_abs_lt_one habs).add
      ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs).const_mul 2)).mul_const q
    simp only [mul_zero, zero_add, zero_mul] at h0
    refine h0.congr fun n => ?_
    rw [pow_succ]
    ring
  linarith [ge_of_tendsto' hlim hone]

/-- A nonarchimedean absolute value that is at most `1` on the integers is at most `1` on every
element integral over `ℤ`.

If `w y > 1` then the leading term of a monic equation for `y` strictly dominates every other, so
the ultrametric inequality makes the sum nonzero. -/
theorem le_one_of_isIntegral {w : AbsoluteValue F ℝ} (hna : IsNonarchimedean (w : F → ℝ))
    (h : ∀ n : ℤ, w (n : F) ≤ 1) {y : F} (hy : IsIntegral ℤ y) : w y ≤ 1 := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨p, hmonic, hp⟩ := hy
  set n := p.natDegree with hn
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [Polynomial.eq_one_of_monic_natDegree_zero hmonic h0] at hp
      simp at hp
    · exact h0
  have hsum : (0 : F) = ∑ i ∈ Finset.range (n + 1), (p.coeff i : F) * y ^ i := by
    rw [← hp, Polynomial.eval₂_eq_sum_range]
    simp [hn]
  rw [Finset.sum_range_succ, hmonic.coeff_natDegree] at hsum
  have hpow : y ^ n = -∑ i ∈ Finset.range n, (p.coeff i : F) * y ^ i := by
    rw [Int.cast_one, one_mul] at hsum
    linear_combination -hsum
  obtain ⟨b, hb, hble⟩ := hna.finset_image_add_of_nonempty
    (fun i => (p.coeff i : F) * y ^ i) (Finset.nonempty_range_iff.mpr hn0.ne')
  have hle : w y ^ n ≤ w y ^ b := by
    rw [← map_pow, hpow, w.map_neg]
    refine hble.trans ?_
    rw [map_mul, map_pow]
    exact mul_le_of_le_one_left (by positivity) (h _)
  have hbn : b + 1 ≤ n := Finset.mem_range.mp hb
  have : w y ^ b < w y ^ n := pow_lt_pow_right₀ hcon (by omega)
  linarith

/-- The `t`-th power of a nonarchimedean absolute value, for `0 < t`. The ultrametric inequality
is what makes this an absolute value at every positive exponent; an archimedean absolute value
admits only the exponents `t ≤ 1`. -/
@[expose] noncomputable def nonarchRpow {w : AbsoluteValue F ℝ} (hna : IsNonarchimedean (w : F → ℝ))
    {t : ℝ} (ht : 0 < t) : AbsoluteValue F ℝ where
  toFun x := w x ^ t
  map_mul' x y := by rw [map_mul, Real.mul_rpow (w.nonneg x) (w.nonneg y)]
  nonneg' x := Real.rpow_nonneg (w.nonneg x) t
  eq_zero' x := by
    rw [Real.rpow_eq_zero_iff_of_nonneg (w.nonneg x)]
    simp [ht.ne', w.eq_zero]
  add_le' x y := by
    have h1 : w (x + y) ^ t ≤ max (w x) (w y) ^ t :=
      Real.rpow_le_rpow (w.nonneg _) (hna x y) ht.le
    have h2 : max (w x) (w y) ^ t = max (w x ^ t) (w y ^ t) := by
      rcases max_cases (w x) (w y) with ⟨he, hle⟩ | ⟨he, hlt⟩
      · rw [he, max_eq_left (Real.rpow_le_rpow (w.nonneg y) hle ht.le)]
      · rw [he, max_eq_right (Real.rpow_le_rpow (w.nonneg x) hlt.le ht.le)]
    rw [h2] at h1
    exact h1.trans (max_le_add_of_nonneg (Real.rpow_nonneg (w.nonneg x) t)
      (Real.rpow_nonneg (w.nonneg y) t))

@[simp] theorem nonarchRpow_apply {w : AbsoluteValue F ℝ} (hna : IsNonarchimedean (w : F → ℝ))
    {t : ℝ} (ht : 0 < t) (x : F) : nonarchRpow hna ht x = w x ^ t := rfl

end AbsoluteValue

section Examples

/-! ### Acceptance criteria -/

/-- **Rejection test for `AbsoluteValue.nonarchRpow`.** The hypothesis that the absolute value is
nonarchimedean cannot be dropped: the square of the usual absolute value of `ℚ` is not an absolute
value, because `4 = |1 + 1| ^ 2 > |1| ^ 2 + |1| ^ 2 = 2`. -/
example : ¬ ∃ N : AbsoluteValue ℚ ℝ, ∀ x : ℚ, N x = |(x : ℝ)| ^ (2 : ℕ) := by
  rintro ⟨N, hN⟩
  have h1 := N.add_le 1 1
  rw [hN] at h1
  norm_num at h1

/-- The other half of the same test: at exponent `1` there is nothing to prove, and at every
exponent below `1` the subadditivity does hold, which is why an archimedean absolute value admits
exactly the exponents `0 < t ≤ 1`. -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (a + b) ^ t ≤ a ^ t + b ^ t :=
  Real.rpow_add_le_add_rpow ha hb ht.le ht1

end Examples
