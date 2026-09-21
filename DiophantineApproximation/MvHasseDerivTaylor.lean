/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.MvHasseDeriv
public import Mathlib.Data.Finsupp.Antidiagonal

/-!
# The Taylor expansion and the Leibniz rule for Hasse derivatives

The Hasse derivatives of `P` are the coefficients of `P (X + Y)` read as a polynomial in the
second family of variables: substituting `X j + Y j` for `X j` turns `P` into
`∑ μ, (∂_μ P)(X) Y^μ`. This file proves that, and reads three consequences off it — the Leibniz
rule, which is what the ring homomorphism property of the substitution says about coefficients;
the Taylor expansion at a point; and the product rule against a single variable, which is
actually the *input* to the substitution formula rather than a corollary of it.

The route matters. Differentiating `P X j` by hand costs one application of Pascal's rule; the
substitution formula then follows by an induction over `C`, `+` and `· * X j`, and the Leibniz
rule is `coeff_mul` applied to `Φ (P Q) = Φ P · Φ Q`. Proving the Leibniz rule directly would
mean reindexing a double sum over two antidiagonals, and proving the substitution formula
directly would mean the multivariate binomial theorem; neither is needed.

## Main results

* `MvPolynomial.hasseDeriv_mul_X`: the product rule against a variable,
  `∂_μ (P X j) = (∂_μ P) X j + ∂_(μ - single j 1) P`, the second term present only when
  `μ j ≠ 0`. This is Pascal's rule.
* `MvPolynomial.coeff_taylor`: **the substitution formula**, `coeff μ (P (C X + X)) = ∂_μ P`,
  inside `MvPolynomial σ (MvPolynomial σ R)`.
* `MvPolynomial.hasseDeriv_mul`: **the Leibniz rule**,
  `∂_μ (P Q) = ∑_(ν + ρ = μ) (∂_ν P) (∂_ρ Q)`, the several-variable form of
  `Polynomial.hasseDeriv_mul`.
* `MvPolynomial.eval_add_eq_sum_hasseDeriv`: **the Taylor expansion**,
  `P (x + y) = ∑ μ, (∂_μ P)(x) y^μ`.

## Implementation notes

⚠ **The Leibniz rule cannot be reached by induction on `μ` from the one-variable case.** The
composition law `∂_(single j 1) ∘ ∂_ν = (ν j + 1) • ∂_(ν + single j 1)` would have to be divided
by `ν j + 1`, which is not invertible in a general commutative semiring — and it is exactly in
characteristic `p` that the Hasse derivative is worth having. The substitution formula avoids the
division because it is an identity between ring homomorphisms.

⚠ **The Taylor expansion is stated over an arbitrary finset `s` carrying the orders at which the
derivative survives**, rather than over a canonical one. There is no `LocallyFiniteOrderBot`
instance on `σ →₀ ℕ`, so `Finset.Iic m` does not exist, and the support of the substituted
polynomial — the honest index set — is not available to a caller who has only `P` in hand. The
hypothesis `∀ μ, ∂_μ P ≠ 0 → μ ∈ s` is what every caller can supply and is all the proof needs.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§6.3.

This is part of Layer 2.1 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Nat

noncomputable section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-! ### Pascal's rule -/

/-- Pascal's rule in the shape the binomial factor needs it. -/
theorem choose_pascal_aux {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a + b).choose b = (a - 1 + b).choose b + (a + (b - 1)).choose (b - 1) := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [show a + 1 + (b + 1) = a + b + 1 + 1 by ring, Nat.choose_succ_succ,
    show a + (b + 1) = a + b + 1 by ring, show a + 1 + b = a + b + 1 by ring]
  exact add_comm _ _

/-- Off `j`, subtracting `single j 1` changes nothing. -/
theorem sub_single_apply_of_ne (n : σ →₀ ℕ) {j i : σ} (h : i ≠ j) :
    (n - (Finsupp.single j 1 : σ →₀ ℕ)) i = n i := by
  rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne h, Nat.sub_zero]

/-- Moving `single j 1` past a summand on the left. -/
theorem add_sub_single_left {n μ : σ →₀ ℕ} {j : σ} (h : n j ≠ 0) :
    n + μ - (Finsupp.single j 1 : σ →₀ ℕ) = n - (Finsupp.single j 1 : σ →₀ ℕ) + μ := by
  ext i
  rcases eq_or_ne i j with rfl | hij
  · simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  · have h1 : (Finsupp.single j 1 : σ →₀ ℕ) i = 0 := Finsupp.single_eq_of_ne hij
    simp only [Finsupp.tsub_apply, Finsupp.add_apply, h1]
    omega

/-- Moving `single j 1` past a summand on the right. -/
theorem add_sub_single_right {n μ : σ →₀ ℕ} {j : σ} (h : μ j ≠ 0) :
    n + μ - (Finsupp.single j 1 : σ →₀ ℕ) = n + (μ - (Finsupp.single j 1 : σ →₀ ℕ)) := by
  ext i
  rcases eq_or_ne i j with rfl | hij
  · simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  · have h1 : (Finsupp.single j 1 : σ →₀ ℕ) i = 0 := Finsupp.single_eq_of_ne hij
    simp only [Finsupp.tsub_apply, Finsupp.add_apply, h1]
    omega

/-- When the order does not touch `j`, the binomial factor does not see `single j 1` either. -/
theorem prod_choose_sub_single_left {μ n : σ →₀ ℕ} {j : σ} (hm : μ j = 0) :
    (μ.prod fun i k ↦ (n i + k).choose k)
      = μ.prod fun i k ↦ ((n - (Finsupp.single j 1 : σ →₀ ℕ)) i + k).choose k :=
  Finsupp.prod_congr fun i hi ↦ by
    have hij : i ≠ j := by
      rintro rfl
      exact (Finsupp.mem_support_iff.mp hi) hm
    rw [sub_single_apply_of_ne n hij]

/-- At an order that does touch `j` but a monomial that does not, the binomial factor does not
notice the step down either: both `j`-factors are `1`. -/
theorem prod_choose_sub_single_right {μ n : σ →₀ ℕ} {j : σ} (hn : n j = 0) (hμ : μ j ≠ 0) :
    (μ.prod fun i k ↦ (n i + k).choose k)
      = (μ - (Finsupp.single j 1 : σ →₀ ℕ)).prod fun i k ↦ (n i + k).choose k := by
  classical
  have hjs : j ∈ μ.support := Finsupp.mem_support_iff.mpr hμ
  have hsub : (μ - (Finsupp.single j 1 : σ →₀ ℕ)).support ⊆ μ.support := by
    intro i hi
    rw [Finsupp.mem_support_iff] at hi ⊢
    rw [Finsupp.tsub_apply] at hi
    omega
  rw [Finsupp.prod_of_support_subset _ hsub _ (by simp),
    show (μ.prod fun i k ↦ (n i + k).choose k)
      = (n j + μ j).choose (μ j) * ∏ i ∈ μ.support.erase j, (n i + μ i).choose (μ i) from
      (Finset.mul_prod_erase _ _ hjs).symm,
    ← Finset.mul_prod_erase _ _ hjs, Finsupp.tsub_apply, Finsupp.single_eq_same, hn]
  congr 1
  · rw [Nat.zero_add, Nat.zero_add, Nat.choose_self, Nat.choose_self]
  · exact Finset.prod_congr rfl fun i hi ↦ by
      rw [sub_single_apply_of_ne μ (Finset.ne_of_mem_erase hi)]

/-- **Pascal's rule for the binomial factor of a Hasse derivative.** -/
theorem prod_choose_pascal {μ n : σ →₀ ℕ} {j : σ} (hn : n j ≠ 0) (hμ : μ j ≠ 0) :
    (μ.prod fun i k ↦ (n i + k).choose k)
      = (μ.prod fun i k ↦ ((n - (Finsupp.single j 1 : σ →₀ ℕ)) i + k).choose k)
        + ((μ - (Finsupp.single j 1 : σ →₀ ℕ)).prod fun i k ↦ (n i + k).choose k) := by
  classical
  have hjs : j ∈ μ.support := Finsupp.mem_support_iff.mpr hμ
  have hA : (μ.prod fun i k ↦ (n i + k).choose k)
      = (n j + μ j).choose (μ j) * ∏ i ∈ μ.support.erase j, (n i + μ i).choose (μ i) :=
    (Finset.mul_prod_erase _ _ hjs).symm
  have hB : (μ.prod fun i k ↦ ((n - (Finsupp.single j 1 : σ →₀ ℕ)) i + k).choose k)
      = (n j - 1 + μ j).choose (μ j) * ∏ i ∈ μ.support.erase j, (n i + μ i).choose (μ i) := by
    have h0 : (μ.prod fun i k ↦ ((n - (Finsupp.single j 1 : σ →₀ ℕ)) i + k).choose k)
        = ((n - (Finsupp.single j 1 : σ →₀ ℕ)) j + μ j).choose (μ j)
          * ∏ i ∈ μ.support.erase j,
              ((n - (Finsupp.single j 1 : σ →₀ ℕ)) i + μ i).choose (μ i) :=
      (Finset.mul_prod_erase _ _ hjs).symm
    rw [h0, Finsupp.tsub_apply, Finsupp.single_eq_same]
    congr 1
    exact Finset.prod_congr rfl fun i hi ↦ by
      rw [sub_single_apply_of_ne n (Finset.ne_of_mem_erase hi)]
  have hsub : (μ - (Finsupp.single j 1 : σ →₀ ℕ)).support ⊆ μ.support := by
    intro i hi
    rw [Finsupp.mem_support_iff] at hi ⊢
    rw [Finsupp.tsub_apply] at hi
    omega
  have hC : ((μ - (Finsupp.single j 1 : σ →₀ ℕ)).prod fun i k ↦ (n i + k).choose k)
      = (n j + (μ j - 1)).choose (μ j - 1)
        * ∏ i ∈ μ.support.erase j, (n i + μ i).choose (μ i) := by
    rw [Finsupp.prod_of_support_subset _ hsub _ (by simp),
      ← Finset.mul_prod_erase _ _ hjs, Finsupp.tsub_apply, Finsupp.single_eq_same]
    congr 1
    exact Finset.prod_congr rfl fun i hi ↦ by
      rw [sub_single_apply_of_ne μ (Finset.ne_of_mem_erase hi)]
  rw [hA, hB, hC, ← add_mul, choose_pascal_aux hn hμ]

/-! ### The product rule against a variable -/

/-- Coefficients of a sum, in the form the rewrites below want. -/
theorem coeff_add_apply (p q : MvPolynomial σ R) (n : σ →₀ ℕ) :
    (p + q).coeff n = p.coeff n + q.coeff n := by simp

/-- **The product rule against a variable**: `∂_μ (P X j)` is `(∂_μ P) X j`, with the extra term
`∂_(μ - single j 1) P` when `μ j ≠ 0`. It is Pascal's rule, and it is the only differentiation
the substitution formula below needs. -/
theorem hasseDeriv_mul_X (μ : σ →₀ ℕ) (P : MvPolynomial σ R) (j : σ) :
    hasseDeriv μ (P * X j)
      = hasseDeriv μ P * X j
        + if μ j = 0 then 0 else hasseDeriv (μ - (Finsupp.single j 1 : σ →₀ ℕ)) P := by
  classical
  by_cases hm : μ j = 0
  · rw [ite_eq_left hm, add_zero]
    ext n
    rw [hasseDeriv_coeff, coeff_mul_X', coeff_mul_X']
    by_cases hn : n j = 0
    · have h1 : j ∉ (n + μ).support := by
        simp [Finsupp.mem_support_iff, Finsupp.add_apply, hn, hm]
      rw [ite_eq_right h1, ite_eq_right (by simpa using hn), mul_zero]
    · have h1 : j ∈ (n + μ).support := by
        rw [Finsupp.mem_support_iff, Finsupp.add_apply]; omega
      rw [ite_eq_left h1, ite_eq_left (by simpa using hn), hasseDeriv_coeff,
        add_sub_single_left hn, prod_choose_sub_single_left (n := n) hm]
  · rw [ite_eq_right hm]
    ext n
    have h1 : j ∈ (n + μ).support := by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply]; omega
    rw [coeff_add_apply, hasseDeriv_coeff, coeff_mul_X', coeff_mul_X', ite_eq_left h1]
    by_cases hn : n j = 0
    · rw [ite_eq_right (by simpa using hn), zero_add, hasseDeriv_coeff,
        add_sub_single_right hm, prod_choose_sub_single_right hn hm]
    · rw [ite_eq_left (by simpa using hn), hasseDeriv_coeff, hasseDeriv_coeff,
        prod_choose_pascal hn hm, Nat.cast_add, add_mul]
      congr 1
      · rw [add_sub_single_left hn]
      · rw [add_sub_single_right hm]

/-! ### The substitution formula -/

/-- **The substitution formula.** Inside `MvPolynomial σ (MvPolynomial σ R)`, substituting
`C (X j) + X j` for `X j` produces the polynomial whose coefficient at `μ` is the `μ`-th Hasse
derivative: `P (X + Y) = ∑ μ, (∂_μ P)(X) Y^μ`. -/
theorem coeff_taylor (P : MvPolynomial σ R) (μ : σ →₀ ℕ) :
    (aeval (fun j ↦ C (X j) + X j) P : MvPolynomial σ (MvPolynomial σ R)).coeff μ
      = hasseDeriv μ P := by
  classical
  induction P using MvPolynomial.induction_on generalizing μ with
  | C a =>
      rw [aeval_C, show algebraMap R (MvPolynomial σ (MvPolynomial σ R)) a = C (C a) from rfl,
        coeff_C, ← monomial_zero', hasseDeriv_monomial]
      by_cases h : μ = 0
      · subst h; simp
      · rw [ite_eq_right (fun hz ↦ h hz.symm),
          prod_choose_eq_zero (m := 0) (by simpa using h),
          Nat.cast_zero, zero_mul, monomial_zero]
  | add p q hp hq => rw [map_add, coeff_add_apply, hp, hq, map_add]
  | mul_X p j hp =>
      rw [map_mul, aeval_X, mul_add, coeff_add_apply, mul_comm (aeval _ p) (C (X j)),
        coeff_C_mul, coeff_mul_X', hp, hasseDeriv_mul_X, mul_comm (X j) (hasseDeriv μ p)]
      congr 1
      by_cases h : μ j = 0
      · rw [ite_eq_right (by simpa using h), ite_eq_left h]
      · rw [ite_eq_left (Finsupp.mem_support_iff.mpr h), ite_eq_right h, hp]

/-! ### The Leibniz rule -/

/-- **The Leibniz rule**, `∂_μ (P Q) = ∑_(ν + ρ = μ) (∂_ν P) (∂_ρ Q)`, the several-variable form
of `Polynomial.hasseDeriv_mul`. It is the substitution formula together with the fact that the
substitution is a ring homomorphism. -/
theorem hasseDeriv_mul [DecidableEq σ] (μ : σ →₀ ℕ) (P Q : MvPolynomial σ R) :
    hasseDeriv μ (P * Q)
      = ∑ x ∈ Finset.antidiagonal μ, hasseDeriv x.1 P * hasseDeriv x.2 Q := by
  classical
  rw [← coeff_taylor, map_mul, coeff_mul]
  exact Finset.sum_congr rfl fun x _ ↦ by rw [coeff_taylor, coeff_taylor]

/-! ### The Taylor expansion at a point -/

/-- **The Taylor expansion**, `P (x + y) = ∑ μ, (∂_μ P)(x) y^μ`. The finset `s` may be any one
containing every order at which the Hasse derivative survives. -/
theorem eval_add_eq_sum_hasseDeriv (P : MvPolynomial σ R) (x y : σ → R)
    {s : Finset (σ →₀ ℕ)} (hs : ∀ μ, hasseDeriv μ P ≠ 0 → μ ∈ s) :
    eval (x + y) P = ∑ μ ∈ s, eval x (hasseDeriv μ P) * μ.prod fun j k ↦ y j ^ k := by
  classical
  have hev : ∀ Q : MvPolynomial σ R,
      eval₂ (eval x) y (aeval (fun j ↦ C (X j) + X j) Q : MvPolynomial σ (MvPolynomial σ R))
        = eval (x + y) Q := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add, eval₂_add, hp, hq, map_add]
    | mul_X p j hp =>
        rw [map_mul, aeval_X, eval₂_mul, hp, map_mul, eval_X]
        simp [Pi.add_apply]
  have hsub : (aeval (fun j ↦ C (X j) + X j) P :
      MvPolynomial σ (MvPolynomial σ R)).support ⊆ s := fun μ hμ ↦
    hs μ (by rw [← coeff_taylor]; exact mem_support_iff.mp hμ)
  rw [← hev P, eval₂_eq]
  refine Eq.trans (Finset.sum_subset hsub fun μ _ hμ ↦ ?_) (Finset.sum_congr rfl fun μ _ ↦ ?_)
  · rw [notMem_support_iff.mp hμ, map_zero, zero_mul]
  · rw [coeff_taylor]
    rfl

/-! ### Acceptance criteria -/

/-- **Acceptance test: the Leibniz rule.** -/
example [DecidableEq σ] (μ : σ →₀ ℕ) (P Q : MvPolynomial σ R) :
    hasseDeriv μ (P * Q)
      = ∑ x ∈ Finset.antidiagonal μ, hasseDeriv x.1 P * hasseDeriv x.2 Q :=
  hasseDeriv_mul μ P Q

/-- **Acceptance test: the Taylor expansion.** -/
example (P : MvPolynomial σ R) (x y : σ → R) {s : Finset (σ →₀ ℕ)}
    (hs : ∀ μ, hasseDeriv μ P ≠ 0 → μ ∈ s) :
    eval (x + y) P = ∑ μ ∈ s, eval x (hasseDeriv μ P) * μ.prod fun j k ↦ y j ^ k :=
  eval_add_eq_sum_hasseDeriv P x y hs

end MvPolynomial
