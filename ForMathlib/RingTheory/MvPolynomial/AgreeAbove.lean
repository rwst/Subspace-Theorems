/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Finsupp.Weight

-- Used only inside proofs.
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Polynomials agreeing in high degrees

`MvPolynomial.AgreeAbove n P Q` says that `P` and `Q` have the same coefficients in every total
degree `≥ n`. For polynomials of total degree `≤ n` it says that they have the same top form. The
relation is compatible with sums, and with products under degree bounds, and substituting
`X i + (constant)` for the variables preserves it (`MvPolynomial.agreeAbove_aeval`). This is the
calculus behind the leading coefficients of Hilbert polynomials.

## Main statements

* `MvPolynomial.AgreeAbove.mul`, `MvPolynomial.AgreeAbove.prod`: products of polynomials of
  bounded degree.
* `MvPolynomial.agreeAbove_aeval`: substitutions `X i ↦ X i + c i` keep the top form.
* `MvPolynomial.coeff_sum_of_agreeAbove`, `MvPolynomial.totalDegree_sum_of_agreeAbove`: the top
  coefficients and the total degree of a sum of polynomials, each with a monomial as its top form
  and all coefficients of these monomials positive.
-/

@[expose] public section

open Finset

variable {ι R : Type*}

namespace MvPolynomial

section CommRing

variable [CommRing R]

/-- `P` and `Q` have the same coefficients in every total degree `≥ n`. -/
def AgreeAbove (n : ℕ) (P Q : MvPolynomial ι R) : Prop :=
  ∀ α : ι →₀ ℕ, n ≤ α.degree → P.coeff α = Q.coeff α

namespace AgreeAbove

variable {n m : ℕ} {P P' Q Q' : MvPolynomial ι R}

@[refl] theorem refl (n : ℕ) (P : MvPolynomial ι R) : AgreeAbove n P P := fun _ _ ↦ rfl

theorem symm (h : AgreeAbove n P Q) : AgreeAbove n Q P := fun α hα ↦ (h α hα).symm

theorem trans (h : AgreeAbove n P Q) (h' : AgreeAbove n Q Q') : AgreeAbove n P Q' :=
  fun α hα ↦ (h α hα).trans (h' α hα)

theorem mono (h : AgreeAbove n P Q) (hnm : n ≤ m) : AgreeAbove m P Q :=
  fun α hα ↦ h α (hnm.trans hα)

theorem add (h : AgreeAbove n P P') (h' : AgreeAbove n Q Q') :
    AgreeAbove n (P + Q) (P' + Q') := fun α hα ↦ by
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h α hα, h' α hα]

theorem sub (h : AgreeAbove n P P') (h' : AgreeAbove n Q Q') :
    AgreeAbove n (P - Q) (P' - Q') := fun α hα ↦ by rw [coeff_sub, coeff_sub, h α hα, h' α hα]

theorem C_mul (h : AgreeAbove n P P') (a : R) : AgreeAbove n (C a * P) (C a * P') :=
  fun α hα ↦ by rw [coeff_C_mul, coeff_C_mul, h α hα]

theorem smul (h : AgreeAbove n P P') (a : R) : AgreeAbove n (a • P) (a • P') :=
  fun α hα ↦ by rw [coeff_smul, coeff_smul, h α hα]

/-- Agreeing in every degree `≥ 0` is equality. -/
theorem eq_of_zero (h : AgreeAbove 0 P Q) : P = Q :=
  MvPolynomial.ext _ _ fun α ↦ h α (Nat.zero_le _)

theorem sum {τ : Type*} {s : Finset τ} {f f' : τ → MvPolynomial ι R}
    (h : ∀ t ∈ s, AgreeAbove n (f t) (f' t)) : AgreeAbove n (∑ t ∈ s, f t) (∑ t ∈ s, f' t) :=
  fun α hα ↦ by
    rw [coeff_sum, coeff_sum]
    exact Finset.sum_congr rfl fun t ht ↦ h t ht α hα

end AgreeAbove

theorem coeff_eq_zero_of_totalDegree_lt_degree {P : MvPolynomial ι R} {α : ι →₀ ℕ}
    (h : P.totalDegree < α.degree) : P.coeff α = 0 :=
  coeff_eq_zero_of_totalDegree_lt (by rwa [← Finsupp.degree_apply])

theorem totalDegree_le_of_forall_coeff_eq_zero {n : ℕ} {P : MvPolynomial ι R}
    (h : ∀ α : ι →₀ ℕ, n < α.degree → P.coeff α = 0) : P.totalDegree ≤ n := by
  refine Finset.sup_le fun v hv ↦ ?_
  by_contra hlt
  refine mem_support_iff.mp hv (h v ?_)
  rw [Finsupp.degree_apply]
  exact lt_of_not_ge hlt

/-- A polynomial agreeing above `n` with one of total degree `≤ n` has total degree `≤ n`. -/
theorem AgreeAbove.totalDegree_le {n : ℕ} {P Q : MvPolynomial ι R} (h : AgreeAbove n P Q)
    (hQ : Q.totalDegree ≤ n) : P.totalDegree ≤ n :=
  totalDegree_le_of_forall_coeff_eq_zero fun α hα ↦ by
    rw [h α hα.le, coeff_eq_zero_of_totalDegree_lt_degree (hQ.trans_lt hα)]

theorem AgreeAbove.mul {n m : ℕ} {P P' Q Q' : MvPolynomial ι R} (h : AgreeAbove n P P')
    (h' : AgreeAbove m Q Q') (hP : P.totalDegree ≤ n) (hP' : P'.totalDegree ≤ n)
    (hQ : Q.totalDegree ≤ m) (hQ' : Q'.totalDegree ≤ m) :
    AgreeAbove (n + m) (P * Q) (P' * Q') := fun α hα ↦ by
  classical
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hx
  have hdeg : x.1.degree + x.2.degree = α.degree := by rw [← map_add, hx]
  rcases lt_trichotomy x.1.degree n with h1 | h1 | h1
  · have h2 : m < x.2.degree := by omega
    rw [coeff_eq_zero_of_totalDegree_lt_degree (hQ.trans_lt h2),
      coeff_eq_zero_of_totalDegree_lt_degree (hQ'.trans_lt h2), mul_zero, mul_zero]
  · rw [h x.1 h1.ge, h' x.2 (by omega)]
  · rw [coeff_eq_zero_of_totalDegree_lt_degree (hP.trans_lt h1),
      coeff_eq_zero_of_totalDegree_lt_degree (hP'.trans_lt h1), zero_mul, zero_mul]

theorem AgreeAbove.prod {τ : Type*} {s : Finset τ} {n : τ → ℕ} {f f' : τ → MvPolynomial ι R}
    (h : ∀ t ∈ s, AgreeAbove (n t) (f t) (f' t)) (hf : ∀ t ∈ s, (f t).totalDegree ≤ n t)
    (hf' : ∀ t ∈ s, (f' t).totalDegree ≤ n t) :
    AgreeAbove (∑ t ∈ s, n t) (∏ t ∈ s, f t) (∏ t ∈ s, f' t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using AgreeAbove.refl 0 (1 : MvPolynomial ι R)
  | insert t s ht ih =>
    rw [Finset.sum_insert ht, Finset.prod_insert ht, Finset.prod_insert ht]
    refine (h t (mem_insert_self t s)).mul
      (ih (fun u hu ↦ h u (mem_insert_of_mem hu)) (fun u hu ↦ hf u (mem_insert_of_mem hu))
        fun u hu ↦ hf' u (mem_insert_of_mem hu))
      (hf t (mem_insert_self t s)) (hf' t (mem_insert_self t s)) ?_ ?_
    · exact (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun u hu ↦
        hf u (mem_insert_of_mem hu))
    · exact (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun u hu ↦
        hf' u (mem_insert_of_mem hu))

theorem AgreeAbove.pow {P P' : MvPolynomial ι R} (h : AgreeAbove 1 P P')
    (hP : P.totalDegree ≤ 1) (hP' : P'.totalDegree ≤ 1) (k : ℕ) :
    AgreeAbove k (P ^ k) (P' ^ k) := by
  simpa using AgreeAbove.prod (s := Finset.range k) (n := fun _ ↦ 1) (fun _ _ ↦ h)
    (fun _ _ ↦ hP) (fun _ _ ↦ hP')

theorem totalDegree_X_le_one (i : ι) : (X i : MvPolynomial ι R).totalDegree ≤ 1 := by
  refine (totalDegree_monomial_le _ _).trans ?_
  simp

theorem totalDegree_X_add_C_le_one (i : ι) (c : R) : (X i + C c).totalDegree ≤ 1 :=
  (totalDegree_add _ _).trans (max_le (totalDegree_X_le_one i) (by simp))

theorem totalDegree_C_mul_le (a : R) (P : MvPolynomial ι R) :
    (C a * P).totalDegree ≤ P.totalDegree :=
  (totalDegree_mul _ _).trans (by simp)

theorem totalDegree_pow_le_of_le_one {P : MvPolynomial ι R} (hP : P.totalDegree ≤ 1) (k : ℕ) :
    (P ^ k).totalDegree ≤ k :=
  (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left k hP)

theorem agreeAbove_X_add_C (i : ι) (c : R) : AgreeAbove 1 (X i + C c) (X i) := fun α hα ↦ by
  classical
  have : α ≠ 0 := by
    rintro rfl
    simp at hα
  simp [AddMonoidAlgebra.coeff_add, coeff_C, Ne.symm this]

/-- Substituting for each variable `X i` a polynomial of degree `≤ 1` does not raise the total
degree. -/
theorem totalDegree_aeval_le {f : ι → MvPolynomial ι R} (hf : ∀ i, (f i).totalDegree ≤ 1)
    (P : MvPolynomial ι R) : (aeval f P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [P.as_sum, map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun v hv ↦ ?_)
  rw [aeval_monomial, algebraMap_eq]
  refine (totalDegree_C_mul_le _ _).trans ((totalDegree_finsetProd _ _).trans ?_)
  exact (Finset.sum_le_sum fun i _ ↦ totalDegree_pow_le_of_le_one (hf i) _).trans
    (le_totalDegree hv)

/-- Substituting for each variable `X i` a polynomial of degree `≤ 1` that agrees with `X i` in
degree `1` does not change the coefficients of top degree. -/
theorem agreeAbove_aeval {f : ι → MvPolynomial ι R} (hf : ∀ i, AgreeAbove 1 (f i) (X i))
    (hf' : ∀ i, (f i).totalDegree ≤ 1) (P : MvPolynomial ι R) :
    AgreeAbove P.totalDegree (aeval f P) P := by
  have key : ∀ v ∈ P.support, AgreeAbove P.totalDegree (aeval f (monomial v (P.coeff v)))
      (monomial v (P.coeff v)) := by
    intro v hv
    rw [aeval_monomial, monomial_eq, algebraMap_eq]
    refine AgreeAbove.C_mul ?_ _
    have hv' : ∑ i ∈ v.support, v i ≤ P.totalDegree := le_totalDegree hv
    refine AgreeAbove.mono ?_ hv'
    exact AgreeAbove.prod (fun i _ ↦ (hf i).pow (hf' i) (totalDegree_X_le_one i) _)
      (fun i _ ↦ totalDegree_pow_le_of_le_one (hf' i) _)
      fun i _ ↦ totalDegree_pow_le_of_le_one (totalDegree_X_le_one i) _
  have := AgreeAbove.sum key
  rwa [← map_sum, ← P.as_sum] at this

/-- **Top coefficients of a sum.** If each `Q t` has total degree `≤ |m t|` and top form the
monomial `c t · T^{m t}`, then in every degree `≥ max |m t|` the coefficient of `T^α` in `∑ Q t` is
the sum of the `c t` with `m t = α`. -/
theorem coeff_sum_of_agreeAbove [DecidableEq ι] {τ : Type*} {s : Finset τ}
    {Q : τ → MvPolynomial ι R} {m : τ → ι →₀ ℕ} {c : τ → R}
    (hQ : ∀ t ∈ s, AgreeAbove (m t).degree (Q t) (monomial (m t) (c t)))
    {α : ι →₀ ℕ} (hα : ∀ t ∈ s, (m t).degree ≤ α.degree) :
    (∑ t ∈ s, Q t).coeff α = ∑ t ∈ s with m t = α, c t := by
  classical
  rw [coeff_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  rw [hQ t ht α (hα t ht), coeff_monomial]

end CommRing

section Ordered

variable [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]

/-- **Total degree of a sum.** If each `Q t` has total degree `≤ |m t|` and top form the monomial
`c t · T^{m t}` with `c t > 0`, then no cancellation occurs among the top forms, and
`∑ Q t` has total degree `max |m t|`. -/
theorem totalDegree_sum_of_agreeAbove {τ : Type*} {s : Finset τ} {Q : τ → MvPolynomial ι R}
    {m : τ → ι →₀ ℕ} {c : τ → R}
    (hQ : ∀ t ∈ s, AgreeAbove (m t).degree (Q t) (monomial (m t) (c t)))
    (hdeg : ∀ t ∈ s, (Q t).totalDegree ≤ (m t).degree) (hc : ∀ t ∈ s, 0 < c t) :
    (∑ t ∈ s, Q t).totalDegree = s.sup fun t ↦ (m t).degree := by
  classical
  refine le_antisymm ((totalDegree_finsetSum _ _).trans (Finset.sup_mono_fun hdeg)) ?_
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  obtain ⟨t₀, ht₀, hmax⟩ := s.exists_max_image (fun t ↦ (m t).degree) hs
  rw [Finset.sup_le_iff.mpr hmax |>.antisymm (Finset.le_sup (f := fun t ↦ (m t).degree) ht₀)]
  have hcoeff := coeff_sum_of_agreeAbove hQ (α := m t₀) hmax
  have hpos : 0 < ∑ t ∈ s with m t = m t₀, c t :=
    Finset.sum_pos (fun t ht ↦ hc t (Finset.mem_filter.mp ht).1) ⟨t₀, by simp [ht₀]⟩
  have hmem : m t₀ ∈ (∑ t ∈ s, Q t).support := by
    rw [mem_support_iff, hcoeff]
    exact hpos.ne'
  rw [Finsupp.degree_apply]
  exact le_totalDegree hmem

end Ordered

end MvPolynomial
