/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.RingTheory.MvPolynomial.Basic

-- Used only by the acceptance criteria.
import Mathlib.Data.ZMod.Basic

/-!
# Hasse derivatives in several variables

The `μ`-th Hasse derivative of `∑ a_m X^m` is `∑ (∏ j, (m j).choose (μ j)) a_m X^(m - μ)`, the
divided derivative `(1 / μ!) ∂^μ` written so that it makes sense in every characteristic. It is
Bombieri–Gubler's (6.1), and it is what Roth's machinery differentiates with: the index of a
polynomial at a point, Layer 2.3, is defined by the orders `μ` at which a Hasse derivative fails
to vanish, and with `pderiv` in its place that definition is wrong in characteristic `p`.

Mathlib has the one-variable Hasse derivative, `Polynomial.hasseDeriv`, and this file is its
several-variable companion, with the same API: the value on a monomial, the coefficients, the
composition law, and the comparison with the iterated `pderiv`.

## Main definitions

* `MvPolynomial.hasseDeriv`: the `μ`-th Hasse derivative, as an `R`-linear map.

## Main results

* `MvPolynomial.hasseDeriv_monomial` and `MvPolynomial.hasseDeriv_coeff`: the two computation
  rules, on a monomial and on a coefficient.
* `MvPolynomial.hasseDeriv_comp`: the composition law
  `∂_μ ∘ ∂_ν = (∏ j, (μ j + ν j).choose (μ j)) • ∂_(μ + ν)`, and with it
  `MvPolynomial.hasseDeriv_commute` and the exact form
  `MvPolynomial.hasseDeriv_comp_of_disjoint` at monomials with disjoint supports.
* `MvPolynomial.hasseDeriv_single_one`: `∂_(single j 1)` is `pderiv j`, and
  `MvPolynomial.factorial_smul_hasseDeriv_single`: `k ! • ∂_(single j k)` is the `k`-th iterate
  of `pderiv j`.
* `MvPolynomial.uniqueAlgEquiv_hasseDeriv`: agreement with `Polynomial.hasseDeriv` in one
  variable.
* `MvPolynomial.degreeOf_hasseDeriv_le` and `MvPolynomial.totalDegree_hasseDeriv_le`: a Hasse
  derivative of order `μ` drops the degree in the variable `j` by at least `μ j`, and the total
  degree by at least the degree of `μ`.

## Implementation notes

⚠ **The truncated subtraction `m - μ` in the definition is harmless, and no hypothesis `μ ≤ m` is
needed.** A binomial coefficient `(m j).choose (μ j)` with `μ j > m j` vanishes, so every monomial
the subtraction would misplace carries the coefficient `0`; `MvPolynomial.prod_choose_eq_zero` is
that observation, and it is what makes `MvPolynomial.hasseDeriv_coeff` an equality with no side
condition.

⚠ **The binomial factor is a `Finsupp.prod` over `μ.support`, not a product over `σ`**, which is
not assumed finite. The two agree, because `(m j).choose 0 = 1`, and
`Finsupp.prod_of_support_subset` is what moves between products over different supports — it is
the only tool the composition law needs beyond the trinomial identity
`MvPolynomial.choose_add_mul_choose`.

⚠ **The composition law is not stated as a `Finsupp.prod` of single-variable operators.** It would
have to be a product in `Module.End R (MvPolynomial σ R)`, which is a monoid and not a commutative
one, so `Finsupp.prod` does not typecheck there; `MvPolynomial.hasseDeriv_comp_of_disjoint` is the
usable form, and it is exact — the binomial factor is `1` precisely when the supports are
disjoint.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§6.3 — the definition is (6.1) and the composition law is used without comment throughout §6.4.

This is part of Layer 2.1 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Nat

noncomputable section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-! ### The trinomial identity -/

/-- The trinomial revision `(a + b)!/(a! b!) · (a + b + c)!/((a+b)! c!) = (a+b+c)!/(a! b! c!)`,
written without division: both sides count the ways of splitting `a + b + c` objects into
groups of sizes `a`, `b` and `c`. This is the one arithmetic fact behind the composition law. -/
theorem choose_add_mul_choose (a b c : ℕ) :
    (a + b).choose b * (a + b + c).choose c
      = (b + c).choose b * (a + (b + c)).choose (b + c) := by
  have e1 : (a + b).choose b * a ! * b ! = (a + b)! :=
    Nat.add_choose_mul_factorial_mul_factorial a b
  have e2 : (a + b + c).choose c * (a + b)! * c ! = (a + b + c)! :=
    Nat.add_choose_mul_factorial_mul_factorial (a + b) c
  have e3 : (b + c).choose c * b ! * c ! = (b + c)! :=
    Nat.add_choose_mul_factorial_mul_factorial b c
  have e4 : (a + (b + c)).choose (b + c) * a ! * (b + c)! = (a + (b + c))! :=
    Nat.add_choose_mul_factorial_mul_factorial a (b + c)
  refine Nat.eq_of_mul_eq_mul_right (m := a ! * b ! * c !)
    (Nat.mul_pos (Nat.mul_pos a.factorial_pos b.factorial_pos) c.factorial_pos) ?_
  calc (a + b).choose b * (a + b + c).choose c * (a ! * b ! * c !)
      = ((a + b).choose b * a ! * b !) * ((a + b + c).choose c * c !) := by ring
    _ = (a + b + c).choose c * (a + b)! * c ! := by rw [e1]; ring
    _ = (a + b + c)! := e2
    _ = (a + (b + c))! := by rw [add_assoc]
    _ = (a + (b + c)).choose (b + c) * a ! * (b + c)! := e4.symm
    _ = (a + (b + c)).choose (b + c) * a ! * ((b + c).choose c * b ! * c !) := by rw [e3]
    _ = (b + c).choose c * (a + (b + c)).choose (b + c) * (a ! * b ! * c !) := by ring
    _ = (b + c).choose b * (a + (b + c)).choose (b + c) * (a ! * b ! * c !) := by
        rw [Nat.choose_symm_add]

/-- The binomial factor vanishes unless `μ ≤ m`: one variable in which `μ` exceeds `m` sends one
factor, and so the whole product, to zero. -/
theorem prod_choose_eq_zero {μ m : σ →₀ ℕ} (h : ¬ μ ≤ m) :
    (μ.prod fun j k ↦ (m j).choose k) = 0 := by
  rw [Finsupp.le_def] at h
  push Not at h
  obtain ⟨j, hj⟩ := h
  exact Finset.prod_eq_zero (i := j) (Finsupp.mem_support_iff.mpr (by omega))
    (Nat.choose_eq_zero_of_lt hj)

/-! ### The definition and its two computation rules -/

/-- The `μ`-th **Hasse derivative** `∂_μ = (1 / μ!) ∂^μ` of a polynomial in several variables,
defined on monomials by Bombieri–Gubler's (6.1),
`∂_μ (a X^m) = (∏ j, (m j).choose (μ j)) a X^(m - μ)`. The truncated subtraction is harmless: a
binomial coefficient `(m j).choose (μ j)` with `μ j > m j` vanishes. -/
def hasseDeriv (μ : σ →₀ ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (basisMonomials σ R).constr R fun m ↦
    monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) : R)

/-- The Hasse derivative as a sum over the support. -/
theorem hasseDeriv_apply (μ : σ →₀ ℕ) (P : MvPolynomial σ R) :
    hasseDeriv μ P = ∑ m ∈ P.support,
      monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * P.coeff m) := by
  rw [hasseDeriv, Module.Basis.constr_apply]
  rw [show (basisMonomials σ R).repr P = AddMonoidAlgebra.coeff P from rfl, sum_def]
  exact Finset.sum_congr rfl fun m _ ↦ by rw [smul_monomial, smul_eq_mul, mul_comm]

/-- **The value on a monomial**, Bombieri–Gubler's (6.1). -/
@[simp]
theorem hasseDeriv_monomial (μ m : σ →₀ ℕ) (a : R) :
    hasseDeriv μ (monomial m a) = monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * a) := by
  classical
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [hasseDeriv_apply]
    simp [support_monomial, ha, coeff_monomial]

/-- **The coefficients of a Hasse derivative**, the several-variable form of
`Polynomial.hasseDeriv_coeff`. -/
theorem hasseDeriv_coeff (μ : σ →₀ ℕ) (P : MvPolynomial σ R) (n : σ →₀ ℕ) :
    (hasseDeriv μ P).coeff n
      = ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : R) * P.coeff (n + μ) := by
  classical
  rw [hasseDeriv_apply, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single (n + μ)]
  · rw [ite_eq_left (add_tsub_cancel_right n μ)]
    have h : (μ.prod fun j k ↦ ((n + μ) j).choose k) = μ.prod fun j k ↦ (n j + k).choose k :=
      Finsupp.prod_congr fun j _ ↦ by rw [Finsupp.add_apply]
    rw [h]
  · intro m _ hne
    by_cases h : m - μ = n
    · rw [ite_eq_left h]
      have hle : ¬ μ ≤ m := fun hle ↦ hne (by rw [← h, tsub_add_cancel_of_le hle])
      rw [prod_choose_eq_zero hle]
      simp
    · rw [ite_eq_right h]
  · intro h
    rw [notMem_support_iff.mp h]
    simp

/-- The zeroth Hasse derivative is the identity. -/
@[simp]
theorem hasseDeriv_zero : (hasseDeriv 0 : MvPolynomial σ R →ₗ[R] MvPolynomial σ R) = .id := by
  ext P n
  simp [hasseDeriv_coeff]

/-- The zeroth Hasse derivative is the identity, applied form. -/
theorem hasseDeriv_zero_apply (P : MvPolynomial σ R) : hasseDeriv 0 P = P := by
  rw [hasseDeriv_zero]; rfl

/-! ### The composition law -/

/-- The binomial factors of two Hasse derivatives, recombined. This is the trinomial identity
`MvPolynomial.choose_add_mul_choose` one variable at a time, with all four products moved onto
the common index set `μ.support ∪ ν.support`. -/
theorem prod_choose_comp (μ ν n : σ →₀ ℕ) :
    (μ.prod fun j k ↦ (n j + k).choose k) * (ν.prod fun j k ↦ ((n + μ) j + k).choose k)
      = (μ.prod fun j k ↦ (k + ν j).choose k) * ((μ + ν).prod fun j k ↦ (n j + k).choose k) := by
  classical
  set s : Finset σ := μ.support ∪ ν.support with hs
  have h1 : (μ.prod fun j k ↦ (n j + k).choose k) = ∏ j ∈ s, (n j + μ j).choose (μ j) :=
    Finsupp.prod_of_support_subset _ Finset.subset_union_left _ (by simp)
  have h2 : (ν.prod fun j k ↦ ((n + μ) j + k).choose k)
      = ∏ j ∈ s, (n j + μ j + ν j).choose (ν j) :=
    Finsupp.prod_of_support_subset _ Finset.subset_union_right _ (by simp)
  have h3 : (μ.prod fun j k ↦ (k + ν j).choose k) = ∏ j ∈ s, (μ j + ν j).choose (μ j) :=
    Finsupp.prod_of_support_subset _ Finset.subset_union_left _ (by simp)
  have h4 : ((μ + ν).prod fun j k ↦ (n j + k).choose k)
      = ∏ j ∈ s, (n j + (μ j + ν j)).choose (μ j + ν j) :=
    Finsupp.prod_of_support_subset _
      (Finsupp.support_add.trans (Finset.union_subset_union subset_rfl subset_rfl)) _ (by simp)
  rw [h1, h2, h3, h4, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ ↦ choose_add_mul_choose (n j) (μ j) (ν j)

/-- **The composition law**, `∂_μ ∘ ∂_ν = (∏ j, (μ j + ν j).choose (μ j)) • ∂_(μ + ν)`, the
several-variable form of `Polynomial.hasseDeriv_comp`. The scalar is written as a `Finsupp.prod`
over `μ.support`, where the omitted factors are `(ν j).choose 0 = 1`. -/
theorem hasseDeriv_comp (μ ν : σ →₀ ℕ) (P : MvPolynomial σ R) :
    hasseDeriv μ (hasseDeriv ν P)
      = (μ.prod fun j k ↦ (k + ν j).choose k) • hasseDeriv (μ + ν) P := by
  ext n
  rw [coeff_smul, hasseDeriv_coeff, hasseDeriv_coeff, hasseDeriv_coeff, nsmul_eq_mul,
    ← add_assoc, ← mul_assoc, ← mul_assoc, ← Nat.cast_mul, ← Nat.cast_mul,
    prod_choose_comp μ ν n]

/-- **Hasse derivatives commute.** -/
theorem hasseDeriv_commute (μ ν : σ →₀ ℕ) (P : MvPolynomial σ R) :
    hasseDeriv μ (hasseDeriv ν P) = hasseDeriv ν (hasseDeriv μ P) := by
  classical
  have key : (μ.prod fun j k ↦ (k + ν j).choose k) = ν.prod fun j k ↦ (k + μ j).choose k := by
    set s : Finset σ := μ.support ∪ ν.support with hs
    have h1 : (μ.prod fun j k ↦ (k + ν j).choose k) = ∏ j ∈ s, (μ j + ν j).choose (μ j) :=
      Finsupp.prod_of_support_subset _ Finset.subset_union_left _ (by simp)
    have h2 : (ν.prod fun j k ↦ (k + μ j).choose k) = ∏ j ∈ s, (ν j + μ j).choose (ν j) :=
      Finsupp.prod_of_support_subset _ Finset.subset_union_right _ (by simp)
    rw [h1, h2]
    exact Finset.prod_congr rfl fun j _ ↦ by rw [add_comm (ν j) (μ j), Nat.choose_symm_add]
  rw [hasseDeriv_comp, hasseDeriv_comp, add_comm ν μ, key]

/-- **The composition law is exact when the orders use disjoint variables**: every binomial
factor is then `k.choose k = 1`. -/
theorem hasseDeriv_comp_of_disjoint {μ ν : σ →₀ ℕ} (h : Disjoint μ.support ν.support)
    (P : MvPolynomial σ R) :
    hasseDeriv μ (hasseDeriv ν P) = hasseDeriv (μ + ν) P := by
  rw [hasseDeriv_comp]
  have : (μ.prod fun j k ↦ (k + ν j).choose k) = 1 := by
    refine Finset.prod_eq_one fun j hj ↦ ?_
    have hν : ν j = 0 := Finsupp.notMem_support_iff.mp (Finset.disjoint_left.mp h hj)
    simp only [hν, add_zero, Nat.choose_self]
  rw [this, one_smul]

/-! ### One variable at a time -/

/-- The first Hasse derivative in one variable is the partial derivative. -/
theorem hasseDeriv_single_one (j : σ) (P : MvPolynomial σ R) :
    hasseDeriv (Finsupp.single j 1) P = pderiv j P := by
  induction P using MvPolynomial.induction_on' with
  | monomial m a =>
      rw [hasseDeriv_monomial, pderiv_monomial]
      rw [Finsupp.prod_single_index (by simp)]
      rw [Nat.choose_one_right, mul_comm]
  | add p q hp hq => rw [map_add, map_add, hp, hq]

/-- **`k ! • ∂_(single j k)` is the `k`-th iterate of `pderiv j`**, the several-variable form of
`Polynomial.factorial_smul_hasseDeriv`. -/
theorem factorial_smul_hasseDeriv_single (j : σ) (k : ℕ) (P : MvPolynomial σ R) :
    (k ! : ℕ) • hasseDeriv (Finsupp.single j k) P = (pderiv j)^[k] P := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ← ih, ← hasseDeriv_single_one, map_nsmul,
        hasseDeriv_comp, Finsupp.prod_single_index (by simp), Finsupp.single_eq_same,
        ← Finsupp.single_add, smul_smul, Nat.choose_one_right, Nat.factorial_succ,
        add_comm 1 k, Nat.mul_comm]

/-! ### Agreement with the one-variable Hasse derivative -/

/-- **Agreement with `Polynomial.hasseDeriv`** along `MvPolynomial.uniqueAlgEquiv`, the
identification of a polynomial ring in one variable with `R[X]`. -/
theorem uniqueAlgEquiv_hasseDeriv [Unique σ] (k : ℕ) (P : MvPolynomial σ R) :
    uniqueAlgEquiv R σ (hasseDeriv (Finsupp.single default k) P) =
      Polynomial.hasseDeriv k (uniqueAlgEquiv R σ P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial m a =>
      rw [hasseDeriv_monomial, uniqueAlgEquiv_monomial, uniqueAlgEquiv_monomial,
        Polynomial.hasseDeriv_monomial, Finsupp.prod_single_index (by simp),
        Finsupp.tsub_apply, Finsupp.single_eq_same]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]

/-! ### Degrees -/

/-- A Hasse derivative of order `μ` drops the degree in the variable `j` by at least `μ j`. -/
theorem degreeOf_hasseDeriv_le (μ : σ →₀ ℕ) (P : MvPolynomial σ R) (j : σ) :
    (hasseDeriv μ P).degreeOf j ≤ P.degreeOf j - μ j := by
  classical
  rw [degreeOf_le_iff]
  intro m hm
  have hne : P.coeff (m + μ) ≠ 0 := by
    intro h
    rw [mem_support_iff, hasseDeriv_coeff, h, mul_zero] at hm
    exact hm rfl
  have := (degreeOf_le_iff).mp (le_refl (P.degreeOf j)) (m + μ) (mem_support_iff.mpr hne)
  rw [Finsupp.add_apply] at this
  omega

/-- A Hasse derivative of order `μ` drops the total degree by at least the degree of `μ`. -/
theorem totalDegree_hasseDeriv_le (μ : σ →₀ ℕ) (P : MvPolynomial σ R) :
    (hasseDeriv μ P).totalDegree ≤ P.totalDegree - μ.sum fun _ k ↦ k := by
  classical
  refine Finset.sup_le fun m hm ↦ ?_
  have hne : P.coeff (m + μ) ≠ 0 := by
    intro h
    rw [mem_support_iff, hasseDeriv_coeff, h, mul_zero] at hm
    exact hm rfl
  have hle : ((m + μ).sum fun _ k ↦ k) ≤ P.totalDegree :=
    le_totalDegree (mem_support_iff.mpr hne)
  rw [Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)] at hle
  omega

/-! ### Acceptance criteria -/

/-- **Acceptance test: the value on a monomial is Bombieri–Gubler's (6.1).** -/
example (μ m : σ →₀ ℕ) (a : R) :
    hasseDeriv μ (monomial m a) = monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * a) :=
  hasseDeriv_monomial μ m a

/-- **Acceptance test: the composition law.** -/
example (μ ν : σ →₀ ℕ) (P : MvPolynomial σ R) :
    hasseDeriv μ (hasseDeriv ν P)
      = (μ.prod fun j k ↦ (k + ν j).choose k) • hasseDeriv (μ + ν) P :=
  hasseDeriv_comp μ ν P

/-- **Rejection test: the iterated `pderiv` is not the Hasse derivative, and in characteristic
`p` it is not even a substitute.** Over `ZMod 2` the second Hasse derivative of `X ^ 2` is `1`
— so the index of `X ^ 2` at `0` is `2` and not `⊤` — while the second iterate of `pderiv`
vanishes. This is why Layer 2.3 is a valuation in every characteristic. -/
example : hasseDeriv (Finsupp.single () 2) ((X () : MvPolynomial Unit (ZMod 2)) ^ 2) = 1 := by
  rw [X_pow_eq_monomial, hasseDeriv_monomial, Finsupp.prod_single_index (by simp),
    Finsupp.single_eq_same, Nat.choose_self]
  simp

/-- **Rejection test**, the other half: `pderiv` already kills `X ^ 2` over `ZMod 2`, so every
iterate of it does. -/
example : pderiv () ((X () : MvPolynomial Unit (ZMod 2)) ^ 2) = 0 := by
  rw [X_pow_eq_monomial, pderiv_monomial, Finsupp.single_eq_same]
  simp only [cast_ofNat, one_mul, monomial_eq_zero]
  decide

end MvPolynomial
