/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Absolute
public import ArithmeticHeights.Polynomial
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Data.Finsupp.Fin
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The monomials of bounded degree, and the coefficient vector of a polynomial

A polynomial in `r` variables of total degree at most `D` is a vector of coefficients indexed by
the monomials of degree at most `D`, of which there are `(D + r).choose r`. This file makes that
sentence usable: it gives the index type

`{m : σ →₀ ℕ // m.degree ≤ D}`

its finiteness and its cardinality, and it gives the dictionary between such a coefficient vector
and the polynomial it names, as a `K`-linear map with a two-sided inverse on polynomials of total
degree at most `D`. Layer 5.7 applies Siegel's lemma to that index type, so the height of the
solution *vector* has to be the height of the resulting *polynomial*; the last section is that
identification.

## Main definitions

* `MvPolynomial.ofDegreeLE`: the `K`-linear map from coefficient vectors indexed by the monomials
  of degree at most `D` to polynomials.

## Main results

* `Finsupp.card_subtype_degree_le`: there are `(D + r).choose r` monomials of degree at most `D`
  in `r` variables. The route is the classical slack variable: `Finsupp.degreeLEEquivDegreeEq`
  turns degree `≤ D` in `r` variables into degree `= D` in `r + 1`, which is Mathlib's
  `Finset.finsuppAntidiag`, counted by stars and bars.
* `MvPolynomial.ofDegreeLE_coeff` and `MvPolynomial.ofDegreeLE_injective`: the dictionary is a
  bijection onto the polynomials of total degree at most `D`.
* `MvPolynomial.mulHeight_eq_mulHeight_coeff_degreeLE` and
  `MvPolynomial.absMulHeight_coeff_degreeLE`: the height of a polynomial of total degree at most
  `D` is the height of its coefficient vector on that index type, in the relative and in the
  absolute normalization.

## Implementation notes

⚠ **The `Fintype` instance is noncomputable.** Mathlib proves `Finsupp.finite_of_degree_le`, a
`Set.Finite`, and everything in this development is noncomputable already, so the instance is
`Fintype.ofFinite` rather than an explicit enumeration through `Finset.finsuppAntidiag`. Only the
cardinality is ever used, and `Finsupp.card_subtype_degree_le` computes it.

⚠ **`MvPolynomial.ofDegreeLE` is a linear map, not a function**, because Layer 5.7 has to carry
linear independence of a family of solution vectors over to linear independence of the
polynomials they name, and that is `LinearIndependent.map'` on an injective linear map.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Section 2.9. M. Hindry and J. H. Silverman, *Diophantine Geometry: An Introduction*, Springer
GTM 201 (2000), Section D.4.

This is Layer 5.7 (infrastructure) of the `ArithmeticHeights` roadmap.
-/

public section

open Finsupp Height Module

namespace Finsupp

variable {σ : Type*}

/-! ### The monomials of degree at most `D` -/

instance instFiniteSubtypeDegreeLE [Finite σ] (D : ℕ) : Finite {m : σ →₀ ℕ // m.degree ≤ D} :=
  (Finsupp.finite_of_degree_le D).to_subtype

noncomputable instance instFintypeSubtypeDegreeLE [Finite σ] (D : ℕ) :
    Fintype {m : σ →₀ ℕ // m.degree ≤ D} :=
  Fintype.ofFinite _

/-- The degree of a tuple with one more entry in front is the entry plus the degree. -/
theorem degree_cons {n : ℕ} (y : ℕ) (s : Fin n →₀ ℕ) :
    (Finsupp.cons y s).degree = y + s.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fin.sum_univ_succ]
  simp

/-- **The slack variable.** A tuple of degree at most `D` in `r` variables is a tuple of degree
exactly `D` in `r + 1` variables, the extra entry taking up the slack. -/
noncomputable def degreeLEEquivDegreeEq (r D : ℕ) :
    {m : Fin r →₀ ℕ // m.degree ≤ D} ≃ {m : Fin (r + 1) →₀ ℕ // m.degree = D} where
  toFun m := ⟨Finsupp.cons (D - m.1.degree) m.1, by rw [degree_cons]; omega⟩
  invFun n := ⟨Finsupp.tail n.1, by
    have h : (Finsupp.cons (n.1 0) (Finsupp.tail n.1)).degree = D := by
      rw [Finsupp.cons_tail]; exact n.2
    rw [degree_cons] at h; omega⟩
  left_inv m := by ext1; simp
  right_inv n := by
    have h : (Finsupp.cons (n.1 0) (Finsupp.tail n.1)).degree = D := by
      rw [Finsupp.cons_tail]; exact n.2
    rw [degree_cons] at h
    have h2 : D - (Finsupp.tail n.1).degree = n.1 0 := by omega
    ext1
    change Finsupp.cons (D - (Finsupp.tail n.1).degree) (Finsupp.tail n.1) = n.1
    rw [h2, Finsupp.cons_tail]

/-- **Stars and bars**, in `r` named variables: there are `(D + r).choose r` monomials of degree
at most `D`. -/
theorem card_subtype_degree_le_fin (r D : ℕ) :
    Fintype.card {m : Fin r →₀ ℕ // m.degree ≤ D} = (D + r).choose r := by
  classical
  have e : {m : Fin r →₀ ℕ // m.degree ≤ D}
      ≃ ((Finset.univ : Finset (Fin (r + 1))).finsuppAntidiag D) :=
    (degreeLEEquivDegreeEq r D).trans (Equiv.subtypeEquivRight fun m ↦ by
      simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum, eq_comm])
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [show r + 1 + D - 1 = D + r by omega]
  exact Nat.choose_symm_add

/-- **Stars and bars.** The number of monomials of degree at most `D` in the variables `σ` is
`(D + #σ).choose #σ`; reindexing along a bijection of the variables does not move the degree. -/
theorem card_subtype_degree_le [Fintype σ] (D : ℕ) :
    Fintype.card {m : σ →₀ ℕ // m.degree ≤ D}
      = (D + Fintype.card σ).choose (Fintype.card σ) := by
  classical
  obtain ⟨e⟩ := Fintype.truncEquivFin σ
  rw [← card_subtype_degree_le_fin (Fintype.card σ) D]
  refine Fintype.card_congr (Equiv.subtypeEquiv (Finsupp.equivCongrLeft e) fun m ↦ ?_)
  rw [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain, Finsupp.degree_mapDomain]

end Finsupp

namespace MvPolynomial

/-! ### The coefficient vector of a polynomial of bounded degree -/

section Dictionary

variable {K : Type*} [Field K] {σ : Type*} [Finite σ] {D : ℕ}

/-- **The polynomial named by a coefficient vector.** The coefficients are indexed by the
monomials of degree at most `D`, so the result has total degree at most `D`, and every polynomial
of total degree at most `D` arises exactly once. -/
@[expose] noncomputable def ofDegreeLE (D : ℕ) :
    ({m : σ →₀ ℕ // m.degree ≤ D} → K) →ₗ[K] MvPolynomial σ K :=
  ∑ m : {m : σ →₀ ℕ // m.degree ≤ D}, (monomial (m : σ →₀ ℕ)).comp (LinearMap.proj m)

theorem ofDegreeLE_apply (x : {m : σ →₀ ℕ // m.degree ≤ D} → K) :
    ofDegreeLE D x = ∑ m : {m : σ →₀ ℕ // m.degree ≤ D}, monomial (m : σ →₀ ℕ) (x m) := by
  simp [ofDegreeLE, LinearMap.sum_apply]

@[simp]
theorem coeff_ofDegreeLE (x : {m : σ →₀ ℕ // m.degree ≤ D} → K)
    (m : {m : σ →₀ ℕ // m.degree ≤ D}) :
    (ofDegreeLE D x).coeff (m : σ →₀ ℕ) = x m := by
  classical
  rw [ofDegreeLE_apply]
  simp [coeff_monomial, Subtype.coe_inj]

theorem coeff_ofDegreeLE_of_not_le (x : {m : σ →₀ ℕ // m.degree ≤ D} → K)
    {m : σ →₀ ℕ} (hm : ¬ m.degree ≤ D) : (ofDegreeLE D x).coeff m = 0 := by
  classical
  rw [ofDegreeLE_apply, MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  have hne : (a : σ →₀ ℕ) ≠ m := by rintro rfl; exact hm a.2
  simp [coeff_monomial, hne]

theorem totalDegree_ofDegreeLE_le (x : {m : σ →₀ ℕ // m.degree ≤ D} → K) :
    (ofDegreeLE D x).totalDegree ≤ D := by
  refine (mem_restrictTotalDegree σ D _).mp fun m hm ↦ ?_
  by_contra h
  exact (MvPolynomial.mem_support_iff.mp hm) (coeff_ofDegreeLE_of_not_le x h)

/-- A polynomial of total degree at most `D` is the one named by its own coefficient vector. -/
theorem ofDegreeLE_coeff (P : MvPolynomial σ K) (hP : P.totalDegree ≤ D) :
    ofDegreeLE D (fun m : {m : σ →₀ ℕ // m.degree ≤ D} ↦ P.coeff (m : σ →₀ ℕ)) = P := by
  refine MvPolynomial.ext _ _ fun m ↦ ?_
  by_cases hm : m.degree ≤ D
  · exact coeff_ofDegreeLE _ ⟨m, hm⟩
  · rw [coeff_ofDegreeLE_of_not_le _ hm]
    by_contra h
    exact hm (le_trans (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr (Ne.symm h)))
      hP)

theorem ofDegreeLE_injective : Function.Injective (ofDegreeLE (K := K) (σ := σ) D) := by
  intro x y h
  funext m
  rw [← coeff_ofDegreeLE x m, h, coeff_ofDegreeLE]

end Dictionary

/-! ### The height of a polynomial is the height of its coefficient vector -/

section Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {σ : Type*} [Finite σ] {D : ℕ}

/-- **Layer 2.1's height of a polynomial is the height of its coefficient vector** on the
monomials of degree at most `D`, as soon as the polynomial has total degree at most `D`. The
height of a `Finsupp` is the height of any finite tuple whose index set covers its support. -/
theorem mulHeight_eq_mulHeight_coeff_degreeLE (P : MvPolynomial σ K) (hP : P.totalDegree ≤ D) :
    P.mulHeight
      = Height.mulHeight fun m : {m : σ →₀ ℕ // m.degree ≤ D} ↦ P.coeff (m : σ →₀ ℕ) :=
  Finsupp.mulHeight_eq_mulHeight_comp _ Subtype.val Subtype.val_injective fun a ha ↦
    ⟨⟨a, (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr
      (Finsupp.mem_support_iff.mp ha))).trans hP⟩, rfl⟩

end Height

section Absolute

variable {K : Type*} [Field K] [NumberField K] {σ : Type*} [Finite σ] {D : ℕ}

/-- The absolute form: the absolute height of the coefficient vector of a polynomial of total
degree at most `D` is `H(P) ^ (1 / d)`, `H(P)` the relative height of Layer 2.1. This is the
translation Layer 5.7 makes between the vector Siegel's lemma produces and the polynomial the
milestone is about. -/
theorem absMulHeight_coeff_degreeLE (P : MvPolynomial σ K) (hP : P.totalDegree ≤ D) :
    NumberField.absMulHeight (fun m : {m : σ →₀ ℕ // m.degree ≤ D} ↦ P.coeff (m : σ →₀ ℕ))
      = P.mulHeight ^ ((Module.finrank ℚ K : ℝ))⁻¹ := by
  rw [NumberField.absMulHeight_eq, mulHeight_eq_mulHeight_coeff_degreeLE P hP]

end Absolute

end MvPolynomial
