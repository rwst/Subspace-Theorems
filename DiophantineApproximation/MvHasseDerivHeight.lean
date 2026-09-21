/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Polynomial
public import DiophantineApproximation.MvHasseDeriv

-- Used only inside proofs.
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Data.Nat.Choose.Bounds

/-!
# The size of a Hasse derivative

Roth's machinery differentiates an auxiliary polynomial many times and then needs to know that the
result is not much larger than what it started from. This file is that estimate, at the level of
the **local factor** `⨆ m, v (coeff m P)` of the height at a single absolute value `v`: a Hasse
derivative does not increase it at a nonarchimedean absolute value, and multiplies it by at most
`2 ^ (total degree)` at any absolute value at all.

Everything rests on one arithmetic fact: the binomial factor `∏ j, (m j).choose (μ j)` of
`MvPolynomial.hasseDeriv_coeff` is a natural number at most `2 ^ (∑ j, m j)`, and the monomials
`m` that occur are the ones in the support of `P`.

## Main results

* `MvPolynomial.prod_choose_le_two_pow`: the binomial factor is at most `2 ^ (deg m)`.
* `MvPolynomial.iSup_coeff_hasseDeriv_le`: **at any absolute value**, differentiating multiplies
  the local factor by at most `2 ^ P.totalDegree`.
* `MvPolynomial.iSup_coeff_hasseDeriv_le_of_isNonarchimedean`: **at a nonarchimedean absolute
  value it does not increase the local factor at all**, because a rational integer has absolute
  value at most `1` there.

## Implementation notes

⚠ **The constant is `2 ^ P.totalDegree`, not `2 ^ (∑ j, degreeOf j P)` as the roadmap writes
it.** The sum over `j` is not defined when `σ` is infinite, which it is allowed to be here, and
`totalDegree` is the sharper of the two whenever both make sense — the binomial factor is bounded
monomial by monomial, and a monomial of `P` has degree at most `P.totalDegree`.

⚠ **No hypothesis on the order `μ` is needed and none on `P`.** The zero polynomial is covered
because its local factor is `0`, and an order `μ` exceeding the degree is covered because the
binomial factor then vanishes; the estimate is stated for every `μ` and every `P`.

⚠ **This stops at the local factor and does not produce a height.** Passing from a bound at every
absolute value to a bound on `Finsupp.mulHeight` needs a transport lemma with **one** input and a
**one-sided** nonarchimedean hypothesis; `ArithmeticHeights`'s
`Finsupp.mulHeight_le_of_forall_iSup_le` has two inputs and demands *equality* at the
nonarchimedean places, which is what Gauss's lemma supplies for a product and what a Hasse
derivative does not supply. Writing that transport means a monotonicity step for the `finprod`
over the nonarchimedean places, and it belongs in that roadmap, not this one.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§6.3 — the estimate is the last sentence of 6.3.1.

This is part of Layer 2.1 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Nat

noncomputable section

namespace AbsoluteValue

variable {K : Type*} [Field K]

/-- An absolute value of a rational integer is at most that integer: the triangle inequality,
`|K| + 1` times. -/
theorem apply_natCast_le (v : AbsoluteValue K ℝ) (n : ℕ) : v (n : K) ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : ((n + 1 : ℕ) : K) = (n : K) + 1 := by push_cast; ring
      have h2 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [h1, h2]
      calc v ((n : K) + 1) ≤ v (n : K) + v 1 := v.add_le _ _
        _ ≤ (n : ℝ) + 1 := by rw [v.map_one]; linarith

end AbsoluteValue

namespace MvPolynomial

variable {σ K : Type*} [Field K]

/-- **The binomial factor of a Hasse derivative is at most `2 ^ (deg m)`.** -/
theorem prod_choose_le_two_pow (μ m : σ →₀ ℕ) :
    (μ.prod fun j k ↦ (m j).choose k) ≤ 2 ^ (m.sum fun _ k ↦ k) := by
  classical
  calc (μ.prod fun j k ↦ (m j).choose k) ≤ ∏ j ∈ μ.support, 2 ^ m j :=
        Finset.prod_le_prod fun j _ ↦ Nat.choose_le_two_pow (m j) (μ j)
    _ = 2 ^ ∑ j ∈ μ.support, m j := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ 2 ^ ∑ j ∈ μ.support ∪ m.support, m j :=
        Nat.pow_le_pow_right (by norm_num)
          (Finset.sum_le_sum_of_subset Finset.subset_union_left)
    _ = 2 ^ (m.sum fun _ k ↦ k) := by
        rw [Finsupp.sum]
        congr 1
        exact (Finset.sum_subset Finset.subset_union_right fun j _ hj ↦
          Finsupp.notMem_support_iff.mp hj).symm

/-- The degree of a monomial occurring in `P` is at most the total degree of `P`. -/
theorem sum_le_totalDegree_of_coeff_ne_zero {P : MvPolynomial σ K} {m : σ →₀ ℕ}
    (h : P.coeff m ≠ 0) : (m.sum fun _ k ↦ k) ≤ P.totalDegree :=
  le_totalDegree (mem_support_iff.mpr h)

/-- **At any absolute value, differentiating multiplies the local factor by at most
`2 ^ P.totalDegree`.** -/
theorem iSup_coeff_hasseDeriv_le (v : AbsoluteValue K ℝ) (μ : σ →₀ ℕ) (P : MvPolynomial σ K) :
    (⨆ n : σ →₀ ℕ, v ((hasseDeriv μ P).coeff n))
      ≤ 2 ^ P.totalDegree * ⨆ n : σ →₀ ℕ, v (P.coeff n) := by
  have hnn : (0 : ℝ) ≤ ⨆ n : σ →₀ ℕ, v (P.coeff n) := Real.iSup_nonneg fun _ ↦ v.nonneg _
  refine Real.iSup_le (fun n ↦ ?_) (by positivity)
  rw [hasseDeriv_coeff, map_mul]
  rcases eq_or_ne (P.coeff (n + μ)) 0 with h | h
  · rw [h, map_zero, mul_zero]
    positivity
  · have hc : v ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : K) ≤ 2 ^ P.totalDegree := by
      refine (v.apply_natCast_le _).trans ?_
      have h1 : (μ.prod fun j k ↦ (n j + k).choose k) ≤ 2 ^ ((n + μ).sum fun _ k ↦ k) := by
        refine le_trans (le_of_eq ?_) (prod_choose_le_two_pow μ (n + μ))
        exact Finsupp.prod_congr fun j _ ↦ by rw [Finsupp.add_apply]
      have h2 : ((n + μ).sum fun _ k ↦ k) ≤ P.totalDegree := sum_le_totalDegree_of_coeff_ne_zero h
      calc ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : ℝ)
          ≤ ((2 ^ ((n + μ).sum fun _ k ↦ k) : ℕ) : ℝ) := by exact_mod_cast h1
        _ ≤ ((2 ^ P.totalDegree : ℕ) : ℝ) := by
            exact_mod_cast Nat.pow_le_pow_right (by norm_num) h2
        _ = 2 ^ P.totalDegree := by push_cast; ring
    exact mul_le_mul hc (le_ciSup (Finsupp.bddAbove_range_apply P.coeff v) (n + μ))
      (v.nonneg _) (by positivity)

/-- **At a nonarchimedean absolute value a Hasse derivative does not increase the local factor.**
The binomial factor is a rational integer, and a rational integer has absolute value at most `1`
at a nonarchimedean absolute value. -/
theorem iSup_coeff_hasseDeriv_le_of_isNonarchimedean {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) (μ : σ →₀ ℕ) (P : MvPolynomial σ K) :
    (⨆ n : σ →₀ ℕ, v ((hasseDeriv μ P).coeff n)) ≤ ⨆ n : σ →₀ ℕ, v (P.coeff n) := by
  have hnn : (0 : ℝ) ≤ ⨆ n : σ →₀ ℕ, v (P.coeff n) := Real.iSup_nonneg fun _ ↦ v.nonneg _
  refine Real.iSup_le (fun n ↦ ?_) hnn
  rw [hasseDeriv_coeff, map_mul]
  have hc : v ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : K) ≤ 1 :=
    hv.apply_natCast_le_one (by simp) (by simp)
  calc v ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : K) * v (P.coeff (n + μ))
      ≤ 1 * v (P.coeff (n + μ)) := by gcongr
    _ = v (P.coeff (n + μ)) := one_mul _
    _ ≤ ⨆ n : σ →₀ ℕ, v (P.coeff n) :=
        le_ciSup (Finsupp.bddAbove_range_apply P.coeff v) (n + μ)

/-! ### Acceptance criteria -/

/-- **Acceptance test: the archimedean estimate.** -/
example (v : AbsoluteValue K ℝ) (μ : σ →₀ ℕ) (P : MvPolynomial σ K) :
    (⨆ n : σ →₀ ℕ, v ((hasseDeriv μ P).coeff n))
      ≤ 2 ^ P.totalDegree * ⨆ n : σ →₀ ℕ, v (P.coeff n) :=
  iSup_coeff_hasseDeriv_le v μ P

/-- **Acceptance test: the nonarchimedean estimate, with no constant.** -/
example {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v) (μ : σ →₀ ℕ) (P : MvPolynomial σ K) :
    (⨆ n : σ →₀ ℕ, v ((hasseDeriv μ P).coeff n)) ≤ ⨆ n : σ →₀ ℕ, v (P.coeff n) :=
  iSup_coeff_hasseDeriv_le_of_isNonarchimedean hv μ P

end MvPolynomial
