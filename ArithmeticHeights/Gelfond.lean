/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.GaussLemma
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Gelfond's inequality

The height of a product of polynomials differs from the product of the heights by a factor that is
*purely archimedean*: Gauss's lemma, Layer 2.2, makes the nonarchimedean local factors exactly
multiplicative, so all that is left is a local estimate at the archimedean absolute values. This
file supplies that estimate, in both directions, and transports it.

Upwards the estimate is elementary. It is the triangle inequality applied to the convolution
`(p * q).coeff n = ∑_{i + j = n} p_i q_j`, and it holds at *every* absolute value, so the resulting
bound on the height holds over every field with `Height.AdmissibleAbsValues`, with no hypothesis at
all — not even `p ≠ 0`, since there the junk value sits on the side being bounded.

Downwards it is Gelfond's inequality proper, and it is not elementary: the proof runs through the
Mahler measure, which lives on `ℂ[X]`. `Height.AdmissibleAbsValues` records *no* structure on the
archimedean absolute values — `archAbsVal` is an arbitrary multiset, and only the nonarchimedean
ones are required to be nonarchimedean — so over a general field there is no complex embedding to
run the argument through and the lower half is simply unavailable. It is proved here for number
fields, where every member of `archAbsVal` is `NumberField.place φ` for a complex embedding `φ`.

## Main results

* `Polynomial.mulHeight_mul_le` and `Polynomial.logHeight_mul_le`: **Gelfond's inequality, upper
  half**, `mulHeight (p * q) ≤ 2 ^ ((natDegree p + natDegree q) * totalWeight K) * mulHeight p *
  mulHeight q`, over any field with `AdmissibleAbsValues`.
* `Polynomial.mulHeight_mul_le_min_natDegree`: the same bound with the sharp elementary constant
  `min (natDegree p) (natDegree q) + 1`, the number of terms of the convolution that can be
  nonzero. It is attained, which `2 ^ (natDegree p + natDegree q)` is not.
* `Polynomial.mulHeight_mul_mulHeight_le` and `Polynomial.logHeight_add_logHeight_le`: **Gelfond's
  inequality, lower half**, over a number field and for `p ≠ 0`, `q ≠ 0`.
* `MvPolynomial.mulHeight_mul_le` and `MvPolynomial.logHeight_mul_le`: the upper half in several
  variables, with the total degree in the exponent and no finiteness assumption on `σ`.
* `Polynomial.supNorm_mul_supNorm_le_two_pow`: the local archimedean statement, on `ℂ[X]`.
* `Polynomial.iSup_coeff_mul_le_card_support`, `Polynomial.iSup_coeff_mul_le_min_natDegree`,
  `Polynomial.iSup_coeff_mul_le_two_pow` and their `MvPolynomial` forms: the local upper estimates
  at an arbitrary absolute value.
* `Nat.choose_middle_mul_sqrt_le_two_pow`: `n.choose (n / 2) * √(n + 1) ≤ 2 ^ n`, the combinatorial
  input that makes the constant of the lower half a power of two on the nose.

Every multiplicative statement is accompanied by its logarithmic form.

## Implementation notes

The local upper estimate is proved once, for a convolution of two `Finsupp`s over any additive
cancellative index monoid with an antidiagonal, and used for `Polynomial` and `MvPolynomial`
alike. Two counts of the antidiagonal are needed, and they are not interchangeable: bounding the
number of nonzero terms by `#p.support` gives the sharp constant for a univariate polynomial, where
`#p.support ≤ natDegree p + 1`, but says nothing about the total degree in several variables, since
that comparison needs `σ` finite. Bounding instead by `#(antidiagonal m) ≤ ∏ i, (m i + 1) ≤ 2 ^ |m|`
gives the total-degree constant for every `σ`.

The lower half over `ℂ` is assembled from three Mathlib lemmas — `mahlerMeasure_mul`,
`supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure` and
`mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm` — and what they give directly is the constant
`2 ^ (natDegree p + natDegree q) * √(natDegree p + natDegree q + 1)`, not the literature's power of
two. The square root is removed by `Nat.choose_middle_mul_sqrt_le_two_pow`, proved here because
Mathlib has only `Nat.centralBinom_le_four_pow`, which is too weak; the content is the central
binomial estimate `centralBinom n ^ 2 * (3 * n + 1) ≤ 16 ^ n`, an induction whose step is the
inequality `(2 * n + 1) ^ 2 * (3 * n + 4) ≤ 4 * (n + 1) ^ 2 * (3 * n + 1)`.

Several variables are out of reach downwards: Mathlib's Mahler measure is univariate, and there is
no multivariate Gelfond inequality to transport. `MvPolynomial` therefore gets the upper half only.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 1.6.11. M. Hindry and J. H. Silverman, *Diophantine Geometry: An Introduction*, Springer
(2000), Proposition B.7.3, where the name is spelled *Gelfand's inequality*; the attribution is to
A. O. Gelfond and both spellings are in print. Their Proposition B.7.2 is the elementary converse.

This is Layer 2.3 of the `ArithmeticHeights` roadmap.
-/

public section

namespace Nat

/-!
### A central binomial estimate

`Nat.choose_middle_mul_sqrt_le_two_pow` is what makes the constant of Gelfond's inequality a power
of two rather than a power of two times a square root. Mathlib has the two-sided crude bounds on
`Nat.centralBinom` but not this one.
-/

private lemma centralBinom_sq_mul_le (n : ℕ) : n.centralBinom ^ 2 * (3 * n + 1) ≤ 16 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hkey : (n + 1) ^ 2 * Nat.centralBinom (n + 1) ^ 2
        = 4 * (2 * n + 1) ^ 2 * n.centralBinom ^ 2 := by
      have h := Nat.succ_mul_centralBinom_succ n
      calc (n + 1) ^ 2 * Nat.centralBinom (n + 1) ^ 2
          = ((n + 1) * Nat.centralBinom (n + 1)) ^ 2 := by ring
        _ = (2 * (2 * n + 1) * n.centralBinom) ^ 2 := by rw [h]
        _ = 4 * (2 * n + 1) ^ 2 * n.centralBinom ^ 2 := by ring
    have h4 : 4 * (2 * n + 1) ^ 2 * (3 * n + 4) ≤ 16 * ((n + 1) ^ 2 * (3 * n + 1)) := by nlinarith
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < (n + 1) ^ 2 * (3 * n + 1) by positivity)
    calc (n + 1) ^ 2 * (3 * n + 1) * (Nat.centralBinom (n + 1) ^ 2 * (3 * (n + 1) + 1))
        = ((n + 1) ^ 2 * Nat.centralBinom (n + 1) ^ 2) * ((3 * n + 1) * (3 * n + 4)) := by ring
      _ = 4 * (2 * n + 1) ^ 2 * (3 * n + 4) * (n.centralBinom ^ 2 * (3 * n + 1)) := by
          rw [hkey]; ring
      _ ≤ 4 * (2 * n + 1) ^ 2 * (3 * n + 4) * 16 ^ n := Nat.mul_le_mul_left _ ih
      _ ≤ 16 * ((n + 1) ^ 2 * (3 * n + 1)) * 16 ^ n := Nat.mul_le_mul_right _ h4
      _ = (n + 1) ^ 2 * (3 * n + 1) * 16 ^ (n + 1) := by ring

private lemma two_mul_choose_eq_centralBinom (m : ℕ) :
    2 * (2 * m + 1).choose m = Nat.centralBinom (m + 1) := by
  have hsymm : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := by
    rw [← Nat.choose_symm (by omega)]
    congr 1
    omega
  rw [Nat.centralBinom, show 2 * (m + 1) = 2 * m + 2 by ring,
    Nat.choose_succ_succ (2 * m + 1) m, hsymm]
  ring

/-- The square of the largest binomial coefficient of order `n`, times `n + 1`, is at most `4 ^ n`.
Equivalently `n.choose (n / 2) ≤ 2 ^ n / √(n + 1)`: the trivial bound `n.choose k ≤ 2 ^ n` loses
exactly this square root. -/
theorem choose_middle_sq_mul_le (n : ℕ) : n.choose (n / 2) ^ 2 * (n + 1) ≤ 4 ^ n := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show (m + m) / 2 = m by omega, show m + m = 2 * m by ring, ← Nat.centralBinom]
    calc Nat.centralBinom m ^ 2 * (2 * m + 1)
        ≤ Nat.centralBinom m ^ 2 * (3 * m + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 16 ^ m := centralBinom_sq_mul_le m
      _ = 4 ^ (2 * m) := by rw [pow_mul]; norm_num
  · subst hm
    rw [show (2 * m + 1) / 2 = m by omega]
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 4 by norm_num)
    calc 4 * ((2 * m + 1).choose m ^ 2 * (2 * m + 1 + 1))
        = Nat.centralBinom (m + 1) ^ 2 * (2 * m + 2) := by
          rw [← two_mul_choose_eq_centralBinom m]; ring
      _ ≤ Nat.centralBinom (m + 1) ^ 2 * (3 * (m + 1) + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 16 ^ (m + 1) := centralBinom_sq_mul_le (m + 1)
      _ = 4 * 4 ^ (2 * m + 1) := by
          have h16 : (16 : ℕ) ^ (m + 1) = 4 ^ (2 * (m + 1)) := by rw [pow_mul]; norm_num
          rw [h16, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ]
          ring

/-- The real form of `Nat.choose_middle_sq_mul_le`: `n.choose (n / 2) * √(n + 1) ≤ 2 ^ n`. This is
what turns the constant `2 ^ (deg p + deg q) * √(deg p + deg q + 1)` that Mathlib's Mahler measure
lemmas produce into the classical `2 ^ (deg p + deg q)`. -/
theorem choose_middle_mul_sqrt_le_two_pow (n : ℕ) :
    (n.choose (n / 2) : ℝ) * Real.sqrt (n + 1) ≤ 2 ^ n := by
  have hnn : (0 : ℝ) ≤ (n.choose (n / 2) : ℝ) * Real.sqrt (n + 1) := by positivity
  have hsq : ((n.choose (n / 2) : ℝ) * Real.sqrt (n + 1)) ^ 2 ≤ ((2 : ℝ) ^ n) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, mul_comm n 2, pow_mul,
      show ((2 : ℝ) ^ 2) = 4 by norm_num]
    exact_mod_cast choose_middle_sq_mul_le n
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hnn, Real.sqrt_sq (by positivity)] at h

end Nat

namespace Finsupp

open Finset

variable {K : Type*} [Field K]

/-!
### The convolution bound

Both polynomial local estimates come from one bound on `v (∑_{a + b = m} x a * y b)`, proved for
`Finsupp`s over any index monoid with an antidiagonal. The two versions differ only in how the
antidiagonal is counted.
-/

private lemma sum_antidiagonal_le {α : Type*} [AddCommMonoid α] [IsCancelAdd α]
    [HasAntidiagonal α] (v : AbsoluteValue K ℝ) (x y : α →₀ K) (m : α) :
    v (∑ a ∈ antidiagonal m, x a.1 * y a.2)
      ≤ x.support.card * ((⨆ i : α, v (x i)) * ⨆ i : α, v (y i)) := by
  classical
  calc v (∑ a ∈ antidiagonal m, x a.1 * y a.2)
      ≤ ∑ a ∈ antidiagonal m, v (x a.1 * y a.2) := v.sum_le _ _
    _ = ∑ a ∈ (antidiagonal m).filter (fun a ↦ a.1 ∈ x.support), v (x a.1 * y a.2) :=
        (Finset.sum_filter_of_ne fun a _ ha ↦ by
          refine Finsupp.mem_support_iff.mpr fun hc ↦ ha ?_
          rw [hc, zero_mul, map_zero]).symm
    _ ≤ ∑ _a ∈ (antidiagonal m).filter (fun a ↦ a.1 ∈ x.support),
          (⨆ i : α, v (x i)) * ⨆ i : α, v (y i) := by
        refine Finset.sum_le_sum fun a _ ↦ ?_
        rw [map_mul]
        exact mul_le_mul (le_ciSup (bddAbove_range_apply x v) a.1)
          (le_ciSup (bddAbove_range_apply y v) a.2) (v.nonneg _)
          (Real.iSup_nonneg fun _ ↦ v.nonneg _)
    _ ≤ x.support.card * ((⨆ i : α, v (x i)) * ⨆ i : α, v (y i)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        · exact mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _)
            (Real.iSup_nonneg fun _ ↦ v.nonneg _)
        · exact_mod_cast Finset.card_le_card_of_injOn Prod.fst
            (fun a ha ↦ (Finset.mem_filter.mp ha).2)
            (fun a ha b hb hab ↦ Prod.ext hab (by
              have ha' := Finset.mem_antidiagonal.mp (Finset.mem_filter.mp ha).1
              have hb' := Finset.mem_antidiagonal.mp (Finset.mem_filter.mp hb).1
              rw [← hab] at hb'
              exact add_left_cancel (ha'.trans hb'.symm)))

private lemma sum_antidiagonal_card_le {α : Type*} [AddCommMonoid α] [HasAntidiagonal α]
    (v : AbsoluteValue K ℝ) (x y : α →₀ K) (m : α) :
    v (∑ a ∈ antidiagonal m, x a.1 * y a.2)
      ≤ (antidiagonal m).card * ((⨆ i : α, v (x i)) * ⨆ i : α, v (y i)) := by
  refine (v.sum_le _ _).trans ?_
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun a _ ↦ ?_
  rw [map_mul]
  exact mul_le_mul (le_ciSup (bddAbove_range_apply x v) a.1)
    (le_ciSup (bddAbove_range_apply y v) a.2) (v.nonneg _)
    (Real.iSup_nonneg fun _ ↦ v.nonneg _)

end Finsupp

namespace Polynomial

open Height AdmissibleAbsValues Finset

section LocalFactor

variable {K : Type*} [Field K]

/-!
### The local estimate, upper half

At *any* absolute value the local factor of a product is at most the number of terms of the
convolution that can be nonzero times the product of the local factors. Nothing archimedean is
used — only the triangle inequality — so these hold at the nonarchimedean places too, where
Gauss's lemma gives the better constant `1`.
-/

/-- The sharpest elementary bound on the local factor of a product: the constant is the number of
terms of the convolution that can be nonzero. -/
theorem iSup_coeff_mul_le_card_support (v : AbsoluteValue K ℝ) (p q : K[X]) :
    (⨆ n : ℕ, v ((p * q).coeff n))
      ≤ (min #p.support #q.support : ℕ)
        * ((⨆ n : ℕ, v (p.coeff n)) * ⨆ n : ℕ, v (q.coeff n)) := by
  have hnn : (0 : ℝ) ≤ (⨆ n : ℕ, v (p.coeff n)) * ⨆ n : ℕ, v (q.coeff n) :=
    mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _) (Real.iSup_nonneg fun _ ↦ v.nonneg _)
  refine Real.iSup_le (fun n ↦ ?_) (by positivity)
  rw [Nat.cast_min, min_mul_of_nonneg _ _ hnn]
  refine le_min ?_ ?_
  · rw [coeff_mul]
    exact Finsupp.sum_antidiagonal_le v p.coeff q.coeff n
  · rw [mul_comm p q, coeff_mul, mul_comm (⨆ n : ℕ, v (p.coeff n))]
    exact Finsupp.sum_antidiagonal_le v q.coeff p.coeff n

/-- The local estimate in terms of the degrees: the constant `min (natDegree p) (natDegree q) + 1`
is the length of the shorter side of the convolution. -/
theorem iSup_coeff_mul_le_min_natDegree (v : AbsoluteValue K ℝ) (p q : K[X]) :
    (⨆ n : ℕ, v ((p * q).coeff n))
      ≤ (min p.natDegree q.natDegree + 1 : ℕ)
        * ((⨆ n : ℕ, v (p.coeff n)) * ⨆ n : ℕ, v (q.coeff n)) := by
  refine (iSup_coeff_mul_le_card_support v p q).trans ?_
  gcongr
  · exact mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _) (Real.iSup_nonneg fun _ ↦ v.nonneg _)
  · have hp := p.card_supp_le_succ_natDegree
    have hq := q.card_supp_le_succ_natDegree
    have h : min #p.support #q.support ≤ min p.natDegree q.natDegree + 1 := by omega
    exact_mod_cast h

/-- The local estimate with the constant of the literature. It is weaker than
`Polynomial.iSup_coeff_mul_le_min_natDegree` — already at degrees `1` and `1` it reads `4` where
the truth is `2` — but it is the shape that matches the multivariate statement. -/
theorem iSup_coeff_mul_le_two_pow (v : AbsoluteValue K ℝ) (p q : K[X]) :
    (⨆ n : ℕ, v ((p * q).coeff n))
      ≤ 2 ^ (p.natDegree + q.natDegree)
        * ((⨆ n : ℕ, v (p.coeff n)) * ⨆ n : ℕ, v (q.coeff n)) := by
  refine (iSup_coeff_mul_le_min_natDegree v p q).trans ?_
  gcongr
  · exact mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _) (Real.iSup_nonneg fun _ ↦ v.nonneg _)
  · have h : min p.natDegree q.natDegree + 1 ≤ 2 ^ (p.natDegree + q.natDegree) :=
      Nat.succ_le_of_lt (lt_of_le_of_lt ((Nat.min_le_left _ _).trans (Nat.le_add_right _ _))
        Nat.lt_two_pow_self)
    exact_mod_cast h

end LocalFactor

section Complex

/-!
### The local estimate, lower half

Over `ℂ` the supremum of the absolute values of the coefficients is `Polynomial.supNorm`, and the
lower estimate is Gelfond's inequality at one archimedean place. It is not elementary: the Mahler
measure is what is multiplicative, and the two comparisons between it and the sup norm — each a
factor `2 ^ deg` in effect — are what the constant pays for.
-/

/-- **Gelfond's inequality at a complex place**, with the constant that Mathlib's comparisons
between the sup norm and the Mahler measure give directly. -/
theorem supNorm_mul_supNorm_le (p q : ℂ[X]) :
    p.supNorm * q.supNorm
      ≤ (p.natDegree.choose (p.natDegree / 2) * q.natDegree.choose (q.natDegree / 2)
          * Real.sqrt ((p * q).natDegree + 1)) * (p * q).supNorm := by
  calc p.supNorm * q.supNorm
      ≤ (p.natDegree.choose (p.natDegree / 2) * p.mahlerMeasure)
          * (q.natDegree.choose (q.natDegree / 2) * q.mahlerMeasure) :=
        mul_le_mul p.supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure
          q.supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure q.supNorm_nonneg
          (mul_nonneg (by positivity) p.mahlerMeasure_nonneg)
    _ = (p.natDegree.choose (p.natDegree / 2) * q.natDegree.choose (q.natDegree / 2))
          * (p * q).mahlerMeasure := by rw [mahlerMeasure_mul]; ring
    _ ≤ (p.natDegree.choose (p.natDegree / 2) * q.natDegree.choose (q.natDegree / 2))
          * (Real.sqrt ((p * q).natDegree + 1) * (p * q).supNorm) := by
        gcongr
        exact mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm _
    _ = _ := by ring

/-- **Gelfond's inequality at a complex place**, with the classical constant. The square root of
`Polynomial.supNorm_mul_supNorm_le` is absorbed by `Nat.choose_middle_mul_sqrt_le_two_pow`, after
splitting it as `√(d₁ + d₂ + 1) ≤ √(d₁ + 1) * √(d₂ + 1)`. -/
theorem supNorm_mul_supNorm_le_two_pow (p q : ℂ[X]) :
    p.supNorm * q.supNorm ≤ 2 ^ (p.natDegree + q.natDegree) * (p * q).supNorm := by
  refine (supNorm_mul_supNorm_le p q).trans (mul_le_mul_of_nonneg_right ?_ (supNorm_nonneg _))
  have hs : Real.sqrt ((p * q).natDegree + 1)
      ≤ Real.sqrt (p.natDegree + 1) * Real.sqrt (q.natDegree + 1) := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have hd : ((p * q).natDegree : ℝ) ≤ p.natDegree + q.natDegree := by
      exact_mod_cast natDegree_mul_le (p := p) (q := q)
    nlinarith [Nat.cast_nonneg (α := ℝ) p.natDegree, Nat.cast_nonneg (α := ℝ) q.natDegree]
  calc (p.natDegree.choose (p.natDegree / 2) : ℝ) * q.natDegree.choose (q.natDegree / 2)
        * Real.sqrt ((p * q).natDegree + 1)
      ≤ (p.natDegree.choose (p.natDegree / 2) : ℝ) * q.natDegree.choose (q.natDegree / 2)
        * (Real.sqrt (p.natDegree + 1) * Real.sqrt (q.natDegree + 1)) := by gcongr
    _ = ((p.natDegree.choose (p.natDegree / 2) : ℝ) * Real.sqrt (p.natDegree + 1))
        * ((q.natDegree.choose (q.natDegree / 2) : ℝ) * Real.sqrt (q.natDegree + 1)) := by ring
    _ ≤ 2 ^ p.natDegree * 2 ^ q.natDegree :=
        mul_le_mul (Nat.choose_middle_mul_sqrt_le_two_pow _)
          (Nat.choose_middle_mul_sqrt_le_two_pow _) (by positivity) (by positivity)
    _ = 2 ^ (p.natDegree + q.natDegree) := (pow_add 2 _ _).symm

end Complex

section Heights

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

/-!
### The height of a product, upper half

Gauss's lemma discharges the nonarchimedean places, the local estimate above the archimedean ones,
and `Polynomial.mulHeight_mul_le_of_forall_iSup_le` puts the two together. No hypothesis on `p` or
`q` is needed.
-/

/-- **The height of a product is at most `(min (deg p) (deg q) + 1) ^ totalWeight K` times the
product of the heights.** This is sharp: over `ℚ`, `p = q = X + 1` attains it. -/
theorem mulHeight_mul_le_min_natDegree (p q : K[X]) :
    (p * q).mulHeight
      ≤ ((min p.natDegree q.natDegree + 1 : ℕ) : ℝ) ^ totalWeight K
        * (p.mulHeight * q.mulHeight) :=
  mulHeight_mul_le_of_forall_iSup_le (by exact_mod_cast Nat.le_add_left 1 _)
    fun v _ ↦ iSup_coeff_mul_le_min_natDegree v p q

/-- The logarithmic form of `Polynomial.mulHeight_mul_le_min_natDegree`. -/
theorem logHeight_mul_le_min_natDegree (p q : K[X]) :
    (p * q).logHeight
      ≤ totalWeight K * Real.log ((min p.natDegree q.natDegree + 1 : ℕ) : ℝ)
        + (p.logHeight + q.logHeight) :=
  logHeight_mul_le_of_forall_iSup_le (by exact_mod_cast Nat.le_add_left 1 _)
    fun v _ ↦ iSup_coeff_mul_le_min_natDegree v p q

/-- **Gelfond's inequality, upper half** (Bombieri–Gubler, Lemma 1.6.11; Hindry–Silverman,
Proposition B.7.3). In Mathlib's relative height the constant of the absolute statement,
`2 ^ (deg p + deg q)`, is raised to the power `totalWeight K`. No nonvanishing hypothesis is
needed: at `p = 0` the junk value sits on the side being bounded. -/
theorem mulHeight_mul_le (p q : K[X]) :
    (p * q).mulHeight
      ≤ 2 ^ ((p.natDegree + q.natDegree) * totalWeight K) * (p.mulHeight * q.mulHeight) := by
  rw [pow_mul]
  exact mulHeight_mul_le_of_forall_iSup_le (one_le_pow₀ one_le_two)
    fun v _ ↦ iSup_coeff_mul_le_two_pow v p q

/-- The logarithmic form of `Polynomial.mulHeight_mul_le`. -/
theorem logHeight_mul_le (p q : K[X]) :
    (p * q).logHeight
      ≤ (p.natDegree + q.natDegree) * totalWeight K * Real.log 2
        + (p.logHeight + q.logHeight) := by
  refine (logHeight_mul_le_of_forall_iSup_le (one_le_pow₀ one_le_two)
    fun v _ ↦ iSup_coeff_mul_le_two_pow v p q).trans_eq ?_
  rw [Real.log_pow]
  push_cast
  ring

end Heights

section NumberField

variable {K : Type*} [Field K] [NumberField K]

/-!
### The height of a product, lower half

Here the archimedean places must be more than a list of absolute values: the local estimate is a
statement about the Mahler measure of a complex polynomial, and it is reached by pushing `p` and
`q` through the complex embedding that defines the place. Over a number field every member of
`archAbsVal` is such a place, and that is all this section uses.
-/

omit [NumberField K] in
/-- The local factor of `p` at the place attached to a complex embedding `φ` is the sup norm of
the image of `p` under `φ`. This is the bridge between `Height.mulHeight` and Mathlib's Mahler
measure theory, which lives on `ℂ[X]`. -/
theorem iSup_coeff_place_eq_supNorm (φ : K →+* ℂ) (p : K[X]) :
    (⨆ n : ℕ, NumberField.place φ (p.coeff n)) = (p.map φ).supNorm := by
  rw [supNorm_eq_iSup]
  exact iSup_congr fun n ↦ by rw [NumberField.place_apply, coeff_map]

/-- **Gelfond's inequality, lower half** (Bombieri–Gubler, Lemma 1.6.11; Hindry–Silverman,
Proposition B.7.3). The nonvanishing hypotheses are not removable: the junk value
`mulHeight 0 = 1` breaks the statement at `p = 0`, where the left side is `mulHeight q`, which is
unbounded, and the right side is a constant.

Unlike the upper half this is stated for a number field, not for an arbitrary field with
`AdmissibleAbsValues`: that class puts no condition on `archAbsVal` beyond its members being
absolute values, so in general there is no complex embedding to run the Mahler measure through. -/
theorem mulHeight_mul_mulHeight_le {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    p.mulHeight * q.mulHeight
      ≤ 2 ^ ((p.natDegree + q.natDegree) * totalWeight K) * (p * q).mulHeight := by
  rw [pow_mul]
  refine mulHeight_mul_mulHeight_le_of_forall_le_iSup hp hq fun v hv ↦ ?_
  obtain ⟨φ, rfl⟩ := NumberField.mem_multisetInfinitePlace.mp hv
  have hdp : (p.map φ).natDegree = p.natDegree := natDegree_map_eq_of_injective φ.injective p
  have hdq : (q.map φ).natDegree = q.natDegree := natDegree_map_eq_of_injective φ.injective q
  rw [iSup_coeff_place_eq_supNorm, iSup_coeff_place_eq_supNorm, iSup_coeff_place_eq_supNorm,
    Polynomial.map_mul]
  have h := supNorm_mul_supNorm_le_two_pow (p.map φ) (q.map φ)
  rwa [hdp, hdq] at h

/-- The logarithmic form of `Polynomial.mulHeight_mul_mulHeight_le`. -/
theorem logHeight_add_logHeight_le {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    p.logHeight + q.logHeight
      ≤ (p.natDegree + q.natDegree) * totalWeight K * Real.log 2 + (p * q).logHeight := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight,
    ← Real.log_mul (mulHeight_ne_zero p) (mulHeight_ne_zero q)]
  have hlog : (p.natDegree + q.natDegree : ℝ) * totalWeight K * Real.log 2
      = Real.log (2 ^ ((p.natDegree + q.natDegree) * totalWeight K)) := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [hlog, ← Real.log_mul (by positivity) (mulHeight_ne_zero (p * q))]
  exact Real.log_le_log (mul_pos (mulHeight_pos p) (mulHeight_pos q))
    (mulHeight_mul_mulHeight_le hp hq)

end NumberField

end Polynomial

namespace MvPolynomial

open Height AdmissibleAbsValues Finset

section LocalFactor

variable {K : Type*} [Field K] {σ : Type*}

/-!
### The local estimate in several variables

The support count still gives the sharpest constant, but it no longer converts into a statement
about degrees: the number of monomials of total degree at most `d` in `σ` variables is finite only
when `σ` is. The antidiagonal count does convert, for every `σ`, because the antidiagonal of an
exponent `m` has `∏ i, (m i + 1) ≤ 2 ^ |m|` elements.
-/

/-- The multivariate form of `Polynomial.iSup_coeff_mul_le_card_support`. -/
theorem iSup_coeff_mul_le_card_support (v : AbsoluteValue K ℝ) (p q : MvPolynomial σ K) :
    (⨆ m : σ →₀ ℕ, v ((p * q).coeff m))
      ≤ (min #p.support #q.support : ℕ)
        * ((⨆ m : σ →₀ ℕ, v (p.coeff m)) * ⨆ m : σ →₀ ℕ, v (q.coeff m)) := by
  classical
  have hnn : (0 : ℝ) ≤ (⨆ m : σ →₀ ℕ, v (p.coeff m)) * ⨆ m : σ →₀ ℕ, v (q.coeff m) :=
    mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _) (Real.iSup_nonneg fun _ ↦ v.nonneg _)
  refine Real.iSup_le (fun m ↦ ?_) (by positivity)
  rw [Nat.cast_min, min_mul_of_nonneg _ _ hnn]
  refine le_min ?_ ?_
  · rw [coeff_mul]
    exact Finsupp.sum_antidiagonal_le v p.coeff q.coeff m
  · rw [mul_comm p q, coeff_mul, mul_comm (⨆ m : σ →₀ ℕ, v (p.coeff m))]
    exact Finsupp.sum_antidiagonal_le v q.coeff p.coeff m

/-- The multivariate form of `Polynomial.iSup_coeff_mul_le_two_pow`, with the total degree in the
exponent. The index type `σ` is arbitrary. -/
theorem iSup_coeff_mul_le_two_pow (v : AbsoluteValue K ℝ) (p q : MvPolynomial σ K) :
    (⨆ m : σ →₀ ℕ, v ((p * q).coeff m))
      ≤ 2 ^ (p.totalDegree + q.totalDegree)
        * ((⨆ m : σ →₀ ℕ, v (p.coeff m)) * ⨆ m : σ →₀ ℕ, v (q.coeff m)) := by
  classical
  have hnn : (0 : ℝ) ≤ (⨆ m : σ →₀ ℕ, v (p.coeff m)) * ⨆ m : σ →₀ ℕ, v (q.coeff m) :=
    mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _) (Real.iSup_nonneg fun _ ↦ v.nonneg _)
  refine Real.iSup_le (fun m ↦ ?_) (by positivity)
  rcases eq_or_ne ((p * q).coeff m) 0 with h | h
  · rw [h, map_zero]
    positivity
  have hdeg : (∑ i ∈ m.support, m i) ≤ p.totalDegree + q.totalDegree :=
    (MvPolynomial.le_totalDegree (Finsupp.mem_support_iff.mpr h)).trans
      (MvPolynomial.totalDegree_mul p q)
  rw [coeff_mul]
  refine (Finsupp.sum_antidiagonal_card_le v p.coeff q.coeff m).trans ?_
  gcongr
  · have hcard : #(antidiagonal m) ≤ 2 ^ (p.totalDegree + q.totalDegree) := by
      refine le_trans (Finset.card_le_card_of_injOn (t := Finset.Iic m) Prod.fst
        (fun a ha ↦ Finset.mem_Iic.mpr ?_) (fun a ha b hb hab ↦ Prod.ext hab ?_)) ?_
      · rw [← Finset.mem_antidiagonal.mp ha]
        exact le_self_add
      · have ha' := Finset.mem_antidiagonal.mp ha
        have hb' := Finset.mem_antidiagonal.mp hb
        rw [← hab] at hb'
        exact add_left_cancel (ha'.trans hb'.symm)
      · rw [Finsupp.card_Iic]
        calc ∏ i ∈ m.support, #(Finset.Iic (m i))
            = ∏ i ∈ m.support, (m i + 1) := by simp
          _ ≤ ∏ i ∈ m.support, 2 ^ (m i) := by
              gcongr with i hi
              exact Nat.lt_two_pow_self
          _ = 2 ^ (∑ i ∈ m.support, m i) := Finset.prod_pow_eq_pow_sum _ _ _
          _ ≤ 2 ^ (p.totalDegree + q.totalDegree) := Nat.pow_le_pow_right (by norm_num) hdeg
    exact_mod_cast hcard

end LocalFactor

section Heights

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {σ : Type*}

/-- **Gelfond's inequality, upper half, in several variables**, with the total degree in the
exponent. The lower half has no multivariate counterpart here: Mathlib's Mahler measure is
univariate. -/
theorem mulHeight_mul_le (p q : MvPolynomial σ K) :
    (p * q).mulHeight
      ≤ 2 ^ ((p.totalDegree + q.totalDegree) * totalWeight K) * (p.mulHeight * q.mulHeight) := by
  rw [pow_mul]
  exact mulHeight_mul_le_of_forall_iSup_le (one_le_pow₀ one_le_two)
    fun v _ ↦ iSup_coeff_mul_le_two_pow v p q

/-- The logarithmic form of `MvPolynomial.mulHeight_mul_le`. -/
theorem logHeight_mul_le (p q : MvPolynomial σ K) :
    (p * q).logHeight
      ≤ (p.totalDegree + q.totalDegree) * totalWeight K * Real.log 2
        + (p.logHeight + q.logHeight) := by
  refine (logHeight_mul_le_of_forall_iSup_le (one_le_pow₀ one_le_two)
    fun v _ ↦ iSup_coeff_mul_le_two_pow v p q).trans_eq ?_
  rw [Real.log_pow]
  push_cast
  ring

end Heights

end MvPolynomial

/-!
### Examples

The tests that fix the constants: that the elementary constant of the upper half is attained and
the classical one is not, and that over `ℚ` the two halves read as the inequalities of the book.
-/

section Examples

open Height Polynomial

/-- **Sharpness.** Over `ℚ`, `X + 1` has height `1` and `(X + 1) ^ 2` has height `2`, so the bound
`Polynomial.mulHeight_mul_le_min_natDegree` — here `(min 1 1 + 1) ^ totalWeight ℚ = 2` — is an
equality, while `Polynomial.mulHeight_mul_le` gives `2 ^ ((1 + 1) * totalWeight ℚ) = 4`. The height
is not multiplicative, and the loss is exactly a factor `2`. -/
example : ((X : ℚ[X]) + 1).mulHeight = 1
    ∧ (((X : ℚ[X]) + 1) * ((X : ℚ[X]) + 1)).mulHeight = 2
    ∧ ((min ((X : ℚ[X]) + 1).natDegree ((X : ℚ[X]) + 1).natDegree + 1 : ℕ) : ℝ)
        ^ totalWeight ℚ = 2 := by
  have hexp : ((X : ℚ[X]) + 1) * ((X : ℚ[X]) + 1) = X ^ 2 + C 2 * X + C 1 := by
    rw [map_ofNat, map_one]; ring
  have hdeg : (((X : ℚ[X]) + 1) * ((X : ℚ[X]) + 1)).natDegree = 2 := by
    rw [← C_1, natDegree_mul (X_add_C_ne_zero 1) (X_add_C_ne_zero 1), natDegree_X_add_C]
  have hcoeff : (fun i : Fin 3 ↦ (((X : ℚ[X]) + 1) * ((X : ℚ[X]) + 1)).coeff i.val)
      = (Int.cast : ℤ → ℚ) ∘ (![1, 2, 1] : Fin 3 → ℤ) := by
    funext i
    fin_cases i <;> simp [hexp, coeff_one]
  have hcov : ∀ m ∈ (((X : ℚ[X]) + 1) * ((X : ℚ[X]) + 1)).coeff.support,
      m ∈ Set.range (Fin.val : Fin 3 → ℕ) := by
    intro m hm
    have hm2 : m ∈ (((X : ℚ[X]) + 1) * ((X : ℚ[X]) + 1)).support := hm
    have h1 := le_natDegree_of_mem_supp m hm2
    rw [hdeg] at h1
    exact ⟨⟨m, by omega⟩, rfl⟩
  have hsup : (⨆ i : Fin 3, |(![1, 2, 1] : Fin 3 → ℤ) i|) = 2 := by
    refine le_antisymm (ciSup_le fun i ↦ ?_) (Finite.le_ciSup_of_le 1 (by decide))
    fin_cases i <;> decide
  refine ⟨by rw [show ((X : ℚ[X]) + 1) = X - C (-1) by simp, mulHeight_X_sub_C,
    Height.mulHeight₁_neg, Height.mulHeight₁_one], ?_, ?_⟩
  · rw [Polynomial.mulHeight, Finsupp.mulHeight_eq_mulHeight_comp _ _ Fin.val_injective hcov,
      hcoeff, Rat.mulHeight_eq_max_abs_of_gcd_eq_one (by decide), hsup]
    norm_num
  · have hd1 : ((X : ℚ[X]) + 1).natDegree = 1 := by rw [← C_1, natDegree_X_add_C]
    rw [hd1, NumberField.totalWeight_eq_finrank, Module.finrank_self]
    norm_num

/-- **Conformance.** Over `ℚ` the two halves are the inequalities of the book, since
`totalWeight ℚ = 1`: the height of a product is within a factor `2 ^ (deg p + deg q)` of the
product of the heights, in both directions. -/
example {p q : ℚ[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).mulHeight ≤ 2 ^ (p.natDegree + q.natDegree) * (p.mulHeight * q.mulHeight)
      ∧ p.mulHeight * q.mulHeight
          ≤ 2 ^ (p.natDegree + q.natDegree) * (p * q).mulHeight := by
  have hw : totalWeight ℚ = 1 := by
    rw [NumberField.totalWeight_eq_finrank, Module.finrank_self]
  exact ⟨by simpa [hw] using Polynomial.mulHeight_mul_le p q,
    by simpa [hw] using Polynomial.mulHeight_mul_mulHeight_le hp hq⟩

end Examples
