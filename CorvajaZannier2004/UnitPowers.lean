/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import CorvajaZannier2004.QuadraticIrrational

-- Used only inside proofs.
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Theorem 2 (c) of Corvaja–Zannier: the powers of a quadratic unit

**Theorem 2 (c)** (Corvaja–Zannier 2004, p. 1). If `α > 0` is a unit of a real quadratic field,
the period of the continued fraction of `αⁿ` is bounded.

The proof (p. 9) computes the expansions: for `αⁿ > 1` of norm `-1`, `αⁿ = [tₙ; tₙ, tₙ, …]`; for
`αⁿ > 2` of norm `1`, `αⁿ = [tₙ - 1; 1, tₙ - 2, 1, tₙ - 2, …]`, where `tₙ = αⁿ + α'ⁿ`.

## Main results

* `Real.cfPeriod_pow_le_two`: the period of `βⁿ` is at most `2` once `βⁿ > 2`, for a unit
  `β > 1`.
* `Real.bddAbove_cfPeriod_pow`: Theorem 2 (c).

## References

P. Corvaja and U. Zannier, Acta Math. **193** (2004), 175–191, Theorem 2 and p. 9.
-/

@[expose] public section

namespace Real

variable {β : ℝ}

/-- A real number whose powers and inverse are algebraic integers is irrational once it exceeds
`1`: a rational algebraic integer with integral inverse is `±1`. -/
theorem irrational_of_isIntegral {x : ℝ} (h1 : 1 < x) (hint : IsIntegral ℤ x)
    (hint' : IsIntegral ℤ x⁻¹) : Irrational x := by
  rintro ⟨r, rfl⟩
  have hinj : Function.Injective ((Algebra.ofId ℚ ℝ).restrictScalars ℤ) :=
    (algebraMap ℚ ℝ).injective
  have hr : IsIntegral ℤ r := by
    rw [← isIntegral_algHom_iff _ hinj]
    simpa using hint
  have hr' : IsIntegral ℤ r⁻¹ := by
    rw [← isIntegral_algHom_iff _ hinj]
    simpa using hint'
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hr
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.mp hr'
  have hr0 : r ≠ 0 := by rintro rfl; norm_num at h1
  have hmk : m * k = 1 := by
    have : ((m * k : ℤ) : ℚ) = 1 := by
      push_cast
      rw [show (m : ℚ) = algebraMap ℤ ℚ m by simp, show (k : ℚ) = algebraMap ℤ ℚ k by simp, hm, hk,
        mul_inv_cancel₀ hr0]
    exact_mod_cast this
  have hrm : r = m := by rw [← hm]; simp
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hmk with h | h <;>
  · rw [hrm, h] at h1
    norm_num at h1

/-- **The powers of a quadratic unit `β > 1`**: once `βⁿ > 2`, the period of `βⁿ` is at most
`2`. -/
theorem cfPeriod_pow_le_two (hβ : IsQuadraticIrrational β) (h1 : 1 < β) (hint : IsIntegral ℤ β)
    (hint' : IsIntegral ℤ β⁻¹) {n : ℕ} (hn : 2 < β ^ n) : cfPeriod (β ^ n) ≤ 2 := by
  obtain ⟨b, c, hbc⟩ := hβ.exists_monic_of_isIntegral hint
  have hβ0 : β ≠ 0 := (zero_lt_one.trans h1).ne'
  have hc0 : c ≠ 0 := by
    rintro rfl
    have : β * (β + b) = 0 := by linear_combination hbc
    rcases mul_eq_zero.mp this with h | h
    · exact hβ0 h
    · exact hβ.1 ⟨-b, by push_cast; linarith⟩
  -- the norm `c = ββ'` is `±1`
  have hinvq : IsQuadraticIrrational β⁻¹ := hβ.inv.1
  obtain ⟨b₁, c₁, h₁⟩ := hinvq.exists_monic_of_isIntegral hint'
  have hcc : c₁ * c = 1 := by
    have e1 : ((c : ℚ) : ℝ) * β⁻¹ ^ 2 + ((b : ℚ) : ℝ) * β⁻¹ + ((1 : ℚ) : ℝ) = 0 := by
      push_cast
      field_simp
      linear_combination hbc
    have e2 : ((1 : ℚ) : ℝ) * β⁻¹ ^ 2 + ((b₁ : ℚ) : ℝ) * β⁻¹ + ((c₁ : ℚ) : ℝ) = 0 := by
      push_cast
      linear_combination h₁
    have := (div_eq_div_of_root hinvq.1 (by exact_mod_cast hc0) one_ne_zero e1 e2).2
    rw [div_one, div_eq_iff (by exact_mod_cast hc0)] at this
    exact_mod_cast this.symm
  -- the conjugate and the power sums
  set β' := -(b : ℝ) - β with hβ'
  have hprod : β * β' = c := by rw [hβ']; linear_combination -hbc
  have hsum : ∀ m : ℕ, ∃ t : ℤ, β ^ m + β' ^ m = t := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      match m with
      | 0 => exact ⟨2, by norm_num⟩
      | 1 => exact ⟨-b, by rw [hβ']; push_cast; ring⟩
      | m + 2 =>
        obtain ⟨t₁, e₁⟩ := ih (m + 1) (by omega)
        obtain ⟨t₀, e₀⟩ := ih m (by omega)
        refine ⟨-b * t₁ - c * t₀, ?_⟩
        push_cast
        rw [← e₁, ← e₀, ← hprod]
        rw [hβ']
        ring
  obtain ⟨t, ht⟩ := hsum n
  set x := β ^ n with hx
  set x' := β' ^ n with hx'
  have hxx' : x * x' = (c : ℝ) ^ n := by rw [hx, hx', ← mul_pow, hprod]
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hxirr : Irrational x := irrational_of_isIntegral hx1 (hint.pow n)
    (by rw [hx, ← inv_pow]; exact hint'.pow n)
  have hxq : IsQuadraticIrrational x := ⟨hxirr, 1, -t, c ^ n, one_ne_zero, by
    push_cast
    rw [← ht, ← hxx']
    ring⟩
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hcc with hc | hc
  · -- hmm: `c₁ = 1` forces `c = 1`
    have hc1 : c = 1 := by rw [hc, one_mul] at hcc; exact hcc
    -- norm `1`: `x' = 1 / x ∈ (0, 1/2)`, period `2` from index `1`
    have hx'eq : x' = x⁻¹ := by
      exact eq_inv_of_mul_eq_one_right (by rw [hxx', hc1]; simp)
    have hx'0 : 0 < x' := by rw [hx'eq]; positivity
    have hx'2 : x' < 1 / 2 := by
      rw [hx'eq, inv_lt_comm₀ hx0 (by norm_num)]
      linarith
    have hfx : Int.fract x = 1 - x' := by
      have : x = t + -x' := by linarith
      rw [this, Int.fract_intCast_add, Int.fract_neg, Int.fract_eq_self.mpr ⟨hx'0.le, by linarith⟩]
      rw [Int.fract_eq_self.mpr ⟨hx'0.le, by linarith⟩]
      exact hx'0.ne'
    have h1' : cfTail x 1 = (1 - x')⁻¹ := by rw [cfTail_one, hfx]
    have hy1 : 1 < (1 - x')⁻¹ := (one_lt_inv₀ (by linarith)).mpr (by linarith)
    have hy2 : (1 - x')⁻¹ < 2 :=
      (inv_lt_comm₀ (a := 1 - x') (b := 2) (by linarith) (by norm_num)).mpr (by linarith)
    have h2' : cfTail x 2 = x - 1 := by
      rw [cfTail_succ, h1', (Int.fract_eq_iff (b := (1 - x')⁻¹ - 1)).mpr
        ⟨by linarith, by linarith, 1, by push_cast; ring⟩]
      rw [hx'eq]
      have : x - 1 ≠ 0 := by linarith
      field_simp
      ring
    have h3' : cfTail x 3 = cfTail x 1 := by
      rw [cfTail_succ, h2', Int.fract_sub_one, hfx, h1']
    exact hxq.cfPeriod_le ((isCFPeriod_iff hxirr 2).mpr ⟨two_pos, 1, h3'⟩)
  · have hc1 : c = -1 := by
      rw [hc] at hcc
      linarith
    -- norm `-1`: for odd `n`, `x = t + 1 / x`; for even `n`, as above
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hcn : (c : ℝ) ^ n = 1 := by rw [hc1, hk]; push_cast; rw [← two_mul, pow_mul]; norm_num
      have hx'eq : x' = x⁻¹ := by
        exact eq_inv_of_mul_eq_one_right (by rw [hxx', hcn])
      have hx'0 : 0 < x' := by rw [hx'eq]; positivity
      have hx'2 : x' < 1 / 2 := by
        rw [hx'eq, inv_lt_comm₀ hx0 (by norm_num)]
        linarith
      have hfx : Int.fract x = 1 - x' := by
        have : x = t + -x' := by linarith
        rw [this, Int.fract_intCast_add, Int.fract_neg,
          Int.fract_eq_self.mpr ⟨hx'0.le, by linarith⟩]
        rw [Int.fract_eq_self.mpr ⟨hx'0.le, by linarith⟩]
        exact hx'0.ne'
      have h1' : cfTail x 1 = (1 - x')⁻¹ := by rw [cfTail_one, hfx]
      have hy1 : 1 < (1 - x')⁻¹ := (one_lt_inv₀ (by linarith)).mpr (by linarith)
      have hy2 : (1 - x')⁻¹ < 2 :=
        (inv_lt_comm₀ (a := 1 - x') (b := 2) (by linarith) (by norm_num)).mpr (by linarith)
      have h2' : cfTail x 2 = x - 1 := by
        rw [cfTail_succ, h1', (Int.fract_eq_iff (b := (1 - x')⁻¹ - 1)).mpr
        ⟨by linarith, by linarith, 1, by push_cast; ring⟩]
        rw [hx'eq]
        have : x - 1 ≠ 0 := by linarith
        field_simp
        ring
      have h3' : cfTail x 3 = cfTail x 1 := by
        rw [cfTail_succ, h2', Int.fract_sub_one, hfx, h1']
      exact hxq.cfPeriod_le ((isCFPeriod_iff hxirr 2).mpr ⟨two_pos, 1, h3'⟩)
    · have hcn : (c : ℝ) ^ n = -1 := by
        rw [hc1, hk]
        push_cast
        rw [pow_succ, pow_mul]
        norm_num
      have hx'eq : x' = -x⁻¹ := by
        rw [eq_neg_iff_add_eq_zero, ← mul_left_inj' hx0.ne', add_mul, inv_mul_cancel₀ hx0.ne',
          mul_comm, hxx', hcn]
        ring
      have hfx : Int.fract x = x⁻¹ := by
        have : x = t + x⁻¹ := by rw [hx'eq] at ht; linarith
        rw [this, Int.fract_intCast_add, Int.fract_eq_self.mpr
          ⟨inv_nonneg.mpr hx0.le, inv_lt_one_of_one_lt₀ hx1⟩]
        rw [← this]
      have h1' : cfTail x 1 = cfTail x 0 := by rw [cfTail_one, hfx, inv_inv, cfTail_zero]
      exact (hxq.cfPeriod_le ((isCFPeriod_iff hxirr 1).mpr ⟨one_pos, 0, h1'⟩)).trans
        (by norm_num)

/-- **Theorem 2 (c) of Corvaja–Zannier** (p. 1): if `α > 0` is a unit of a real quadratic field,
the period of the continued fraction of `αⁿ` is bounded. -/
theorem bddAbove_cfPeriod_pow {α : ℝ} (hα : IsQuadraticIrrational α) (h0 : 0 < α)
    (hunit : IsIntegral ℤ α ∧ IsIntegral ℤ α⁻¹) :
    BddAbove (Set.range fun n : ℕ ↦ cfPeriod (α ^ n)) := by
  -- pass to `β = max (α, 1/α) > 1`
  obtain ⟨β, hβ, h1, hint, hint', hper⟩ : ∃ β : ℝ, IsQuadraticIrrational β ∧ 1 < β ∧
      IsIntegral ℤ β ∧ IsIntegral ℤ β⁻¹ ∧ ∀ n, 0 < n → 2 < β ^ n →
        cfPeriod (α ^ n) = cfPeriod (β ^ n) := by
    have hne : α ≠ 1 := fun h ↦ hα.1 ⟨1, by rw [h]; norm_num⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine ⟨α⁻¹, hα.inv.1, one_lt_inv₀ h0 |>.mpr hlt, hunit.2, by simpa using hunit.1,
        fun n hn h2 ↦ ?_⟩
      have hirr : Irrational (α⁻¹ ^ n) := irrational_of_isIntegral (by linarith)
        (hunit.2.pow n) (by rw [inv_pow, inv_inv]; exact hunit.1.pow n)
      rw [show α ^ n = (α⁻¹ ^ n)⁻¹ by rw [inv_pow, inv_inv]]
      exact cfPeriod_eq_of_tailEquiv hirr.inv hirr (tailEquiv_inv hirr)
    · exact ⟨α, hα, hgt, hunit.1, hunit.2, fun _ _ _ ↦ rfl⟩
  -- only finitely many `n` have `βⁿ ≤ 2`
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → 2 < β ^ n := by
    obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt 2 h1
    exact ⟨n₀, fun n hn ↦ hn₀.trans_le (pow_le_pow_right₀ h1.le hn)⟩
  refine ⟨max 2 ((Finset.range (n₀ + 1)).sup fun n ↦ cfPeriod (α ^ n)), ?_⟩
  rintro _ ⟨n, rfl⟩
  by_cases hn : n ≤ n₀
  · exact le_max_of_le_right (Finset.le_sup (f := fun n ↦ cfPeriod (α ^ n))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))
  · push Not at hn
    have h2 := hn₀ n hn.le
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn
    change cfPeriod (α ^ n) ≤ _
    rw [hper n hn0 h2]
    exact le_max_of_le_left (cfPeriod_pow_le_two hβ h1 hint hint' h2)

end Real
