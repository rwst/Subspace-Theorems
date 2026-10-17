/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Data.Finsupp.Option
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
-- Used only inside proofs.
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Homogenization of multivariate polynomials

For `p : K[X_s | s ∈ σ]` and `N : ℕ`, `MvPolynomial.homogenize N p` is the polynomial in the
variables `X_o`, `o : Option σ`, obtained by multiplying each monomial `X^d` of `p` by
`X_none ^ (N - deg d)`. For `deg p ≤ N` it is homogeneous of degree `N`, and setting `X_none = 1`
(`MvPolynomial.dehomogenize`) gives `p` back. Mathlib has the one-variable version
`Polynomial.homogenize` only.

## Main definitions

* `MvPolynomial.homogenize N`: the homogenization in degree `N`, a linear map.
* `MvPolynomial.dehomogenize`: the algebra map `X_none ↦ 1`, `X_(some s) ↦ X_s`.

## Main statements

* `MvPolynomial.isHomogeneous_homogenize`: homogeneous of degree `N` when `deg p ≤ N`.
* `MvPolynomial.dehomogenize_homogenize`: `dehomogenize (homogenize N p) = p`.
* `MvPolynomial.homogenize_dehomogenize`: a form of degree `N` is the homogenization of its
  dehomogenization.
* `MvPolynomial.homogenize_mul`, `MvPolynomial.homogenize_prod_pow`,
  `MvPolynomial.homogenize_prod`, `MvPolynomial.homogenize_add_eq_X_pow_mul`: multiplicativity
  and the shift of the degree; `MvPolynomial.homogenize_one`: `1 ↦ X_none ^ N`.
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- The exponent of the homogenization of `X ^ d` in degree `N`: `d` with `N - deg d` at
`none`. -/
noncomputable def homogenizeExp (N : ℕ) (d : σ →₀ ℕ) : Option σ →₀ ℕ :=
  d.optionElim (N - d.degree)

theorem some_homogenizeExp (N : ℕ) (d : σ →₀ ℕ) : (homogenizeExp N d).some = d :=
  Finsupp.some_optionElim _ _

theorem degree_optionElim (y : ℕ) (f : σ →₀ ℕ) : (f.optionElim y).degree = y + f.degree := by
  classical
  have h : f.optionElim y = Finsupp.single none y + f.mapDomain some := by
    ext o
    cases o with
    | none =>
      simp [Finsupp.mapDomain_of_notMem_range _ _ (by simp : (none : Option σ) ∉ Set.range some)]
    | some a =>
      simp [Finsupp.mapDomain_apply_of_injective (Option.some_injective σ)]
  rw [h, map_add, Finsupp.degree_single, Finsupp.degree_mapDomain]

theorem degree_homogenizeExp {N : ℕ} {d : σ →₀ ℕ} (hd : d.degree ≤ N) :
    (homogenizeExp N d).degree = N := by
  rw [homogenizeExp, degree_optionElim]
  omega

theorem degree_eq_apply_none_add (c : Option σ →₀ ℕ) : c.degree = c none + c.some.degree := by
  conv_lhs => rw [← Finsupp.optionElim_some c]
  rw [degree_optionElim]

theorem homogenizeExp_some {N : ℕ} {c : Option σ →₀ ℕ} (hc : c.degree = N) :
    homogenizeExp N c.some = c := by
  rw [homogenizeExp, show N - c.some.degree = c none by rw [← hc, degree_eq_apply_none_add]; omega,
    Finsupp.optionElim_some]

/-- The homogenization of a polynomial in degree `N`, as a function. -/
noncomputable def homogenizeFun (N : ℕ) (p : MvPolynomial σ R) : MvPolynomial (Option σ) R :=
  ∑ d ∈ p.support, monomial (homogenizeExp N d) (p.coeff d)

open Classical in
theorem coeff_homogenizeFun (N : ℕ) (p : MvPolynomial σ R) (c : Option σ →₀ ℕ) :
    (homogenizeFun N p).coeff c = if homogenizeExp N c.some = c then p.coeff c.some else 0 := by
  simp only [homogenizeFun, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, coeff_monomial]
  by_cases h : homogenizeExp N c.some = c
  · have hiff : ∀ d, homogenizeExp N d = c ↔ d = c.some := fun d ↦
      ⟨fun hd ↦ by rw [← hd, some_homogenizeExp], fun hd ↦ hd ▸ h⟩
    simp_rw [hiff]
    rw [sum_ite_eq', ite_true]
    split_ifs with hm
    · rfl
    · exact (notMem_support_iff.mp hm).symm
  · simp only [h, ↓reduceIte]
    refine sum_eq_zero fun d _ ↦ ?_
    rw [ite_eq_right_iff]
    rintro rfl
    exact absurd (by rw [some_homogenizeExp]) h

/-- **Homogenization** in degree `N`: `X ^ d ↦ X_none ^ (N - deg d) X ^ d`. -/
noncomputable def homogenize (N : ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial (Option σ) R where
  toFun := homogenizeFun N
  map_add' p q := by
    ext c
    simp only [coeff_homogenizeFun, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    split_ifs <;> simp
  map_smul' a p := by
    ext c
    simp only [coeff_smul, coeff_homogenizeFun, RingHom.id_apply]
    split_ifs <;> simp

open Classical in
theorem coeff_homogenize (N : ℕ) (p : MvPolynomial σ R) (c : Option σ →₀ ℕ) :
    (homogenize N p).coeff c = if homogenizeExp N c.some = c then p.coeff c.some else 0 :=
  coeff_homogenizeFun N p c

theorem homogenize_monomial (N : ℕ) (d : σ →₀ ℕ) (a : R) :
    homogenize N (monomial d a) = monomial (homogenizeExp N d) a := by
  classical
  ext c
  rw [coeff_homogenize, coeff_monomial, coeff_monomial]
  by_cases h : homogenizeExp N d = c
  · subst h
    simp [some_homogenizeExp]
  · simp only [h, ↓reduceIte]
    split_ifs with h₁ h₂
    · exact absurd (h₂ ▸ h₁) h
    · rfl
    · rfl

/-- The homogenization in degree `N` of a polynomial of degree `≤ N` is homogeneous of degree
`N`. -/
theorem isHomogeneous_homogenize {N : ℕ} {p : MvPolynomial σ R} (hp : p.totalDegree ≤ N) :
    (homogenize N p).IsHomogeneous N := by
  classical
  intro c hc
  rw [coeff_homogenize] at hc
  split_ifs at hc with h
  · change Finsupp.weight (fun _ ↦ 1) c = N
    rw [← Finsupp.degree_eq_weight_one, ← h]
    refine degree_homogenizeExp ((?_ : c.some.degree ≤ p.totalDegree).trans hp)
    exact le_totalDegree (mem_support_iff.mpr hc)
  · exact absurd rfl hc

/-- **Dehomogenization**: `X_none ↦ 1`, `X_(some s) ↦ X_s`. -/
noncomputable def dehomogenize : MvPolynomial (Option σ) R →ₐ[R] MvPolynomial σ R :=
  aeval fun o ↦ o.elim 1 X

theorem dehomogenize_monomial (c : Option σ →₀ ℕ) (a : R) :
    dehomogenize (monomial c a) = monomial c.some a := by
  rw [dehomogenize, aeval_monomial, Finsupp.prod_option_index _ _ (fun _ ↦ pow_zero _)
    (fun _ _ _ ↦ pow_add _ _ _), monomial_eq]
  simp [algebraMap_eq]

theorem dehomogenize_X_none : dehomogenize (X none : MvPolynomial (Option σ) R) = 1 := by
  simp [dehomogenize]

theorem dehomogenize_X_some (s : σ) :
    dehomogenize (X (some s) : MvPolynomial (Option σ) R) = X s := by
  simp [dehomogenize]

theorem dehomogenize_homogenize (N : ℕ) (p : MvPolynomial σ R) :
    dehomogenize (homogenize N p) = p := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a => rw [homogenize_monomial, dehomogenize_monomial, some_homogenizeExp]
  | add p q hp hq => rw [map_add, map_add, hp, hq]

/-- A form of degree `N` is the homogenization in degree `N` of its dehomogenization. -/
theorem homogenize_dehomogenize {N : ℕ} {F : MvPolynomial (Option σ) R} (hF : F.IsHomogeneous N) :
    homogenize N (dehomogenize F) = F := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, map_sum]
  refine sum_congr rfl fun c hc ↦ ?_
  have hdeg : c.degree = N := by
    rw [Finsupp.degree_eq_weight_one]
    exact hF (mem_support_iff.mp hc)
  rw [dehomogenize_monomial, homogenize_monomial, homogenizeExp_some hdeg]

theorem totalDegree_dehomogenize_le {N : ℕ} {F : MvPolynomial (Option σ) R}
    (hF : F.IsHomogeneous N) : (dehomogenize F).totalDegree ≤ N := by
  rw [F.as_sum, map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun c hc ↦ ?_)
  rw [dehomogenize_monomial]
  refine (totalDegree_monomial_le _ _).trans ?_
  have hdeg : c.degree = N := by
    rw [Finsupp.degree_eq_weight_one]
    exact hF (mem_support_iff.mp hc)
  have := degree_eq_apply_none_add c
  change c.some.degree ≤ N
  omega

/-- Homogenization is multiplicative. -/
theorem homogenize_mul {m n : ℕ} {p q : MvPolynomial σ R} (hp : p.totalDegree ≤ m)
    (hq : q.totalDegree ≤ n) :
    homogenize (m + n) (p * q) = homogenize m p * homogenize n q := by
  have h := ((isHomogeneous_homogenize hp).mul (isHomogeneous_homogenize hq))
  rw [← homogenize_dehomogenize h, map_mul dehomogenize, dehomogenize_homogenize,
    dehomogenize_homogenize]

/-- Raising the degree of the homogenization multiplies by a power of `X_none`. -/
theorem homogenize_add_eq_X_pow_mul {N : ℕ} {p : MvPolynomial σ R} (hp : p.totalDegree ≤ N)
    (k : ℕ) : homogenize (N + k) p = homogenize N p * X none ^ k := by
  have h := (isHomogeneous_homogenize hp).mul (isHomogeneous_X_pow (R := R) none k)
  rw [← homogenize_dehomogenize h, map_mul dehomogenize, map_pow dehomogenize,
    dehomogenize_X_none, one_pow, mul_one,
    dehomogenize_homogenize]

/-- A form of degree `N`, times `X_none ^ k`, is the homogenization of its dehomogenization in
degree `N + k`. -/
theorem homogenize_add_dehomogenize {N : ℕ} {F : MvPolynomial (Option σ) R}
    (hF : F.IsHomogeneous N) (k : ℕ) :
    homogenize (N + k) (dehomogenize F) = F * X none ^ k := by
  rw [homogenize_add_eq_X_pow_mul (totalDegree_dehomogenize_le hF), homogenize_dehomogenize hF]

theorem homogenize_zero_one : homogenize 0 (1 : MvPolynomial σ R) = 1 := by
  simpa using homogenize_dehomogenize (isHomogeneous_one (Option σ) R)

/-- The constant `1`, homogenized in degree `N`, is `X_none ^ N`. -/
theorem homogenize_one (N : ℕ) : homogenize N (1 : MvPolynomial σ R) = X none ^ N := by
  simpa [homogenize_zero_one] using
    homogenize_add_eq_X_pow_mul (p := (1 : MvPolynomial σ R)) (N := 0) (by simp) N

/-- Homogenization commutes with powers. -/
theorem homogenize_pow {m : ℕ} {p : MvPolynomial σ R} (hp : p.totalDegree ≤ m) (n : ℕ) :
    homogenize (m * n) (p ^ n) = homogenize m p ^ n := by
  induction n with
  | zero => simpa using homogenize_zero_one
  | succ n ih =>
    rw [pow_succ, pow_succ, mul_add, mul_one,
      homogenize_mul ((totalDegree_pow p n).trans (by rw [mul_comm]; gcongr)) hp, ih]

/-- Homogenization commutes with products of powers. -/
theorem homogenize_prod_pow {ι : Type*} (s : Finset ι) {m : ℕ} {p : ι → MvPolynomial σ R}
    (hp : ∀ i, (p i).totalDegree ≤ m) (e : ι → ℕ) :
    homogenize (m * ∑ i ∈ s, e i) (∏ i ∈ s, p i ^ e i) = ∏ i ∈ s, homogenize m (p i) ^ e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using homogenize_zero_one
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, mul_add,
      homogenize_mul ((totalDegree_pow _ _).trans (by rw [mul_comm]; gcongr; exact hp a))
        ((totalDegree_finsetProd _ _).trans ?_), homogenize_pow (hp a), ih]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ (totalDegree_pow _ _).trans
      (by rw [mul_comm]; gcongr; exact hp i)

/-- Homogenization of a product, each factor homogenized in its own degree. -/
theorem homogenize_prod {ι : Type*} (s : Finset ι) {p : ι → MvPolynomial σ R} {d : ι → ℕ}
    (hp : ∀ i, (p i).totalDegree ≤ d i) :
    homogenize (∑ i ∈ s, d i) (∏ i ∈ s, p i) = ∏ i ∈ s, homogenize (d i) (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using homogenize_zero_one
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.prod_insert ha,
      homogenize_mul (hp a)
        ((totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ ↦ hp i)), ih]

end MvPolynomial
