/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

-- Used only inside proofs.
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Set.Infinite

/-!
# The size of the value of a polynomial under an absolute value

For an absolute value `v` on a field `K`, a point `P : σ → K` and `‖P‖_v = max (1, max_s |P_s|_v)`
(written `⨆ o : Option σ, v (o.elim 1 P)`, the local factor of the affine height),
`|q(P)|_v ≤ (∑_m |c_m|_v) ‖P‖_v ^ e` for every `e ≥ deg q` (`MvPolynomial.abv_eval_le`). The
triangle inequality suffices, so the bound holds at archimedean and ultrametric places alike.
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {σ K : Type*} [Field K] [Finite σ] (v : AbsoluteValue K ℝ) (P : σ → K)

/-- `‖P‖_v ≥ 1`. -/
theorem one_le_iSup_abv_optionElim : 1 ≤ ⨆ o : Option σ, v (o.elim 1 P) :=
  le_ciSup_of_le ((Set.finite_range _).bddAbove) none (by simp)

/-- `|P_s|_v ≤ ‖P‖_v`. -/
theorem abv_le_iSup_abv_optionElim (s : σ) : v (P s) ≤ ⨆ o : Option σ, v (o.elim 1 P) :=
  le_ciSup_of_le ((Set.finite_range _).bddAbove) (some s) le_rfl

/-- **`|q(P)|_v ≤ (∑_m |c_m|_v) ‖P‖_v ^ e` for `e ≥ deg q`.** -/
theorem abv_eval_le (q : MvPolynomial σ K) {e : ℕ} (he : q.totalDegree ≤ e) :
    v (eval P q) ≤ (∑ m ∈ q.support, v (q.coeff m)) * (⨆ o : Option σ, v (o.elim 1 P)) ^ e := by
  set n := ⨆ o : Option σ, v (o.elim 1 P)
  have hn : 1 ≤ n := one_le_iSup_abv_optionElim v P
  rw [eval_eq, sum_mul]
  refine (v.sum_le _ _).trans (sum_le_sum fun m hm ↦ ?_)
  rw [map_mul, map_prod]
  refine mul_le_mul_of_nonneg_left ?_ (v.nonneg _)
  calc ∏ i ∈ m.support, v (P i ^ m i) ≤ ∏ i ∈ m.support, n ^ m i :=
        prod_le_prod₀ (fun _ _ ↦ v.nonneg _) fun i _ ↦ by
          rw [map_pow]; exact pow_le_pow_left₀ (v.nonneg _) (abv_le_iSup_abv_optionElim v P i) _
    _ = n ^ ∑ i ∈ m.support, m i := prod_pow_eq_pow_sum _ _ _
    _ ≤ n ^ e := pow_le_pow_right₀ hn ((le_totalDegree hm).trans he)

/-- A monomial: `|P^m|_v ≤ ‖P‖_v ^ e` for `e ≥ deg m`. -/
theorem abv_eval_monomial_le (m : σ →₀ ℕ) {e : ℕ} (he : (monomial m (1 : K)).totalDegree ≤ e) :
    v (eval P (monomial m 1)) ≤ (⨆ o : Option σ, v (o.elim 1 P)) ^ e := by
  classical
  simpa [support_monomial, coeff_monomial] using abv_eval_le v P (monomial m (1 : K)) he

end MvPolynomial
