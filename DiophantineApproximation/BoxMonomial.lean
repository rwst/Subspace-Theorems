/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Absolute
public import ArithmeticHeights.Polynomial
public import DiophantineApproximation.MvHasseDeriv

/-!
# Polynomials of bounded partial degrees

Roth's auxiliary polynomial is bounded **one variable at a time**: `degreeOf j P ≤ d j`, not
`totalDegree P ≤ D`. Its coefficients therefore sit on the box `∏ j, {0, …, d j}` rather than on
the simplex of monomials of bounded total degree, and this file is the dictionary between the
two descriptions — the box analogue of `ArithmeticHeights/MonomialIndex.lean`, which does the
same work for the simplex.

The index type is `∀ j, Fin (d j + 1)`, so that its cardinality is `∏ j, (d j + 1)` by
`Fintype.card_pi` and no separate counting lemma is needed, and so that a vector indexed by it is
literally a multiplication table — which is what makes the height of a row of the condition
matrix a product of one-variable heights in
`DiophantineApproximation/MonomialHeight.lean`.

## Main results

* `MvPolynomial.boxMonomial`: the exponent named by a point of the box, and
  `MvPolynomial.boxMonomial_injective` and `MvPolynomial.exists_boxMonomial_eq`, which say it
  names each exponent of the box exactly once.
* `MvPolynomial.ofBox`: the polynomial named by a coefficient vector, with
  `MvPolynomial.coeff_ofBox`, `MvPolynomial.degreeOf_ofBox_le`, `MvPolynomial.ofBox_coeff` and
  `MvPolynomial.ofBox_injective`.
* `MvPolynomial.mulHeight_eq_mulHeight_coeff_box` and
  `MvPolynomial.absMulHeight_coeff_box`: the height of such a polynomial is the height of its
  coefficient vector on the box.
* `MvPolynomial.hasseDeriv_eq_zero_of_lt`: a Hasse derivative of an order that leaves the box in
  some variable vanishes — the reason the conditions imposed outside the box are free.

## Implementation notes

⚠ **The index type is a `Pi` type and not a subtype, and that is the whole point.** The obvious
choice, `{ν : σ →₀ ℕ // ∀ j, ν j ≤ d j}`, needs a separate `Fintype` instance, a separate
cardinality computation, and then an equivalence with `∀ j, Fin (d j + 1)` anyway before the
Segre relation `Height.mulHeight_fun_prod_eq` can be applied to a row. Naming the box by
`∀ j, Fin (d j + 1)` from the start removes all three, at the cost of one injection
`MvPolynomial.boxMonomial` into the exponents, which is what every statement here is about.

⚠ **`Fintype (∀ j, Fin (d j + 1))` needs `DecidableEq σ`**, so the variables carry it from
`MvPolynomial.ofBox` on; the statements about `MvPolynomial.boxMonomial` alone do not.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 6.3.4.

This is part of Layer 2.6 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace MvPolynomial

/-! ### The exponents of the box -/

section Monomials

variable {σ : Type*} [Fintype σ] {d : σ → ℕ}

/-- **The exponent named by a point of the box** `∀ j, Fin (d j + 1)`. -/
def boxMonomial (d : σ → ℕ) (I : ∀ j, Fin (d j + 1)) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j ↦ (I j : ℕ)

@[simp]
theorem boxMonomial_apply (d : σ → ℕ) (I : ∀ j, Fin (d j + 1)) (j : σ) :
    boxMonomial d I j = (I j : ℕ) := rfl

/-- Every exponent named by the box lies in the box. -/
theorem boxMonomial_le (d : σ → ℕ) (I : ∀ j, Fin (d j + 1)) (j : σ) :
    boxMonomial d I j ≤ d j := by
  simpa using Nat.lt_succ_iff.mp (I j).isLt

/-- Distinct points of the box name distinct exponents. -/
theorem boxMonomial_injective : Function.Injective (boxMonomial d) := by
  intro I J h
  funext j
  exact Fin.ext (by simpa using congrFun (congrArg (⇑) h) j)

/-- Every exponent of the box is named by the box. -/
theorem exists_boxMonomial_eq {ν : σ →₀ ℕ} (h : ∀ j, ν j ≤ d j) :
    ∃ I : ∀ j, Fin (d j + 1), boxMonomial d I = ν := by
  refine ⟨fun j ↦ ⟨ν j, Nat.lt_succ_of_le (h j)⟩, ?_⟩
  ext j
  simp

/-- The support of a polynomial with the partial degrees of the box is named by the box. -/
theorem mem_range_boxMonomial_of_mem_support {R : Type*} [CommSemiring R] {P : MvPolynomial σ R}
    (hP : ∀ j, P.degreeOf j ≤ d j) {ν : σ →₀ ℕ} (hν : ν ∈ P.support) :
    ν ∈ Set.range (boxMonomial d) :=
  exists_boxMonomial_eq fun j ↦ le_trans (degreeOf_le_iff.mp le_rfl ν hν) (hP j)

omit [Fintype σ] in
/-- **A Hasse derivative of an order that leaves the box vanishes** on a polynomial of bounded
partial degrees: the binomial factor `(m j).choose (μ j)` of `MvPolynomial.hasseDeriv_monomial`
is zero at every monomial `m` that occurs. -/
theorem hasseDeriv_eq_zero_of_lt {R : Type*} [CommSemiring R] {P : MvPolynomial σ R} {j : σ}
    {μ : σ →₀ ℕ} (h : P.degreeOf j < μ j) : hasseDeriv μ P = 0 := by
  classical
  rw [hasseDeriv_apply]
  refine Finset.sum_eq_zero fun m hm ↦ ?_
  have hmj : m j < μ j := lt_of_le_of_lt (degreeOf_le_iff.mp le_rfl m hm) h
  rw [prod_choose_eq_zero (fun hle ↦ absurd (hle j) (by omega))]
  simp

end Monomials

/-! ### The coefficient vector of a polynomial with bounded partial degrees -/

section OfBox

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type*} [Field K] {d : σ → ℕ}

/-- **The polynomial named by a coefficient vector on the box.** -/
def ofBox (d : σ → ℕ) : ((∀ j, Fin (d j + 1)) → K) →ₗ[K] MvPolynomial σ K :=
  ∑ I : (∀ j, Fin (d j + 1)), (monomial (boxMonomial d I)).comp (LinearMap.proj I)

/-- `MvPolynomial.ofBox` as a sum of monomials. -/
theorem ofBox_apply (x : (∀ j, Fin (d j + 1)) → K) :
    ofBox d x = ∑ I : (∀ j, Fin (d j + 1)), monomial (boxMonomial d I) (x I) := by
  simp [ofBox, LinearMap.sum_apply]

@[simp]
theorem coeff_ofBox (x : (∀ j, Fin (d j + 1)) → K) (I : ∀ j, Fin (d j + 1)) :
    (ofBox d x).coeff (boxMonomial d I) = x I := by
  classical
  rw [ofBox_apply, MvPolynomial.coeff_sum, Finset.sum_eq_single I ?_ (by simp)]
  · simp [coeff_monomial]
  · intro J _ hJ
    rw [coeff_monomial]
    exact ite_eq_right fun h ↦ absurd (boxMonomial_injective h) hJ

/-- Outside the box the polynomial named by a coefficient vector has no coefficients. -/
theorem coeff_ofBox_of_not_le (x : (∀ j, Fin (d j + 1)) → K) {ν : σ →₀ ℕ}
    (hν : ¬ ∀ j, ν j ≤ d j) : (ofBox d x).coeff ν = 0 := by
  classical
  rw [ofBox_apply, MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun I _ ↦ ?_
  have hne : boxMonomial d I ≠ ν := fun h ↦ hν (h ▸ boxMonomial_le d I)
  simp [coeff_monomial, hne]

/-- The polynomial named by a coefficient vector on the box has the partial degrees of the box. -/
theorem degreeOf_ofBox_le (x : (∀ j, Fin (d j + 1)) → K) (j : σ) :
    (ofBox d x).degreeOf j ≤ d j := by
  rw [degreeOf_le_iff]
  intro ν hν
  by_contra h
  exact (mem_support_iff.mp hν) (coeff_ofBox_of_not_le x fun hle ↦ h (hle j))

/-- A polynomial with the partial degrees of the box is the one named by its own coefficient
vector. -/
theorem ofBox_coeff (P : MvPolynomial σ K) (hP : ∀ j, P.degreeOf j ≤ d j) :
    ofBox d (fun I ↦ P.coeff (boxMonomial d I)) = P := by
  refine MvPolynomial.ext _ _ fun ν ↦ ?_
  by_cases hν : ∀ j, ν j ≤ d j
  · obtain ⟨I, rfl⟩ := exists_boxMonomial_eq hν
    exact coeff_ofBox _ I
  · rw [coeff_ofBox_of_not_le _ hν]
    by_contra h
    exact hν fun j ↦
      le_trans (degreeOf_le_iff.mp le_rfl ν (mem_support_iff.mpr (Ne.symm h))) (hP j)

/-- Distinct coefficient vectors name distinct polynomials. -/
theorem ofBox_injective : Function.Injective (ofBox (K := K) (σ := σ) d) := by
  intro x y h
  funext I
  rw [← coeff_ofBox x I, h, coeff_ofBox]

end OfBox

/-! ### The row of a condition -/

section Row

variable {σ : Type*} [Fintype σ] {R : Type*} [CommSemiring R]

/-- **The row of the condition matrix** attached to the Hasse derivative of order `μ` at `α`:
the linear form in the coefficients of a polynomial of the box whose vanishing says that
`∂_μ P` vanishes at `α`. -/
def hasseDerivRow (d : σ → ℕ) (α : σ → R) (μ : σ →₀ ℕ) : (∀ j, Fin (d j + 1)) → R :=
  fun I ↦ ((μ.prod fun j k ↦ (I j : ℕ).choose k : ℕ) : R) * ∏ j, α j ^ ((I j : ℕ) - μ j)

/-- **The row is a multiplication table** over the variables: both the binomial factor and the
monomial factor are products over `σ`. -/
theorem hasseDerivRow_eq_prod (d : σ → ℕ) (α : σ → R) (μ : σ →₀ ℕ) (I : ∀ j, Fin (d j + 1)) :
    hasseDerivRow d α μ I
      = ∏ j, (((I j : ℕ).choose (μ j) : ℕ) : R) * α j ^ ((I j : ℕ) - μ j) := by
  classical
  rw [hasseDerivRow, Finset.prod_mul_distrib]
  congr 1
  rw [← Nat.cast_prod]
  congr 1
  exact Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _ (by simp)

end Row

/-! ### The height of a polynomial with bounded partial degrees -/

section Height

variable {σ : Type*} [Fintype σ] {K : Type*} [Field K] [Height.AdmissibleAbsValues K]
  {d : σ → ℕ}

/-- **The height of a polynomial with the partial degrees of the box is the height of its
coefficient vector** on the box. -/
theorem mulHeight_eq_mulHeight_coeff_box (P : MvPolynomial σ K) (hP : ∀ j, P.degreeOf j ≤ d j) :
    P.mulHeight = Height.mulHeight fun I : (∀ j, Fin (d j + 1)) ↦ P.coeff (boxMonomial d I) :=
  Finsupp.mulHeight_eq_mulHeight_comp _ (boxMonomial d) boxMonomial_injective
    fun _ ha ↦ mem_range_boxMonomial_of_mem_support hP ha

end Height

section Absolute

variable {σ : Type*} [Fintype σ] {K : Type*} [Field K] [NumberField K] {d : σ → ℕ}

/-- The absolute form of `MvPolynomial.mulHeight_eq_mulHeight_coeff_box`: the translation Layer
2.6 makes between the vector Siegel's lemma produces and the polynomial the milestone is
about. -/
theorem absMulHeight_coeff_box (P : MvPolynomial σ K) (hP : ∀ j, P.degreeOf j ≤ d j) :
    NumberField.absMulHeight (fun I : (∀ j, Fin (d j + 1)) ↦ P.coeff (boxMonomial d I))
      = P.mulHeight ^ ((Module.finrank ℚ K : ℝ))⁻¹ := by
  rw [NumberField.absMulHeight_eq, mulHeight_eq_mulHeight_coeff_box P hP]

end Absolute

/-! ### Acceptance criteria -/

section Acceptance

/-- **Acceptance test: the box has `∏ j, (d j + 1)` monomials**, which is what makes the
coefficient count of Lemma 6.3.4 a product and not a binomial coefficient. -/
example {σ : Type*} [Fintype σ] [DecidableEq σ] (d : σ → ℕ) :
    Fintype.card (∀ j, Fin (d j + 1)) = ∏ j, (d j + 1) := by simp

/-- **Acceptance test: at order `0` the row is the tuple of monomials at `α`**, so that the
condition of order `0` is the vanishing of `P` at `α` itself. -/
example {σ : Type*} [Fintype σ] {R : Type*} [CommSemiring R] (d : σ → ℕ) (α : σ → R)
    (I : ∀ j, Fin (d j + 1)) : hasseDerivRow d α 0 I = ∏ j, α j ^ (I j : ℕ) := by
  simp [hasseDerivRow]

/-- **Rejection test: `MvPolynomial.hasseDeriv_eq_zero_of_lt` needs the strict inequality.** At
`μ j = degreeOf j P` the derivative survives: `∂_(X 0) (X 0) = 1`. -/
example : hasseDeriv (Finsupp.single (0 : Fin 1) 1) (X 0 : MvPolynomial (Fin 1) ℚ) = 1 := by
  rw [X, hasseDeriv_monomial]
  simp

end Acceptance

end MvPolynomial

end
