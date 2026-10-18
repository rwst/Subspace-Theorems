/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

-- Used only inside proofs.
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.StdBasis

/-!
# The Veronese map and forms of degree `t` as linear forms

The monomials of degree `t` in the variables `ι` are the finsupps in
`Finset.finsuppAntidiag univ t` (`MvPolynomial.degreeMonomials`). The **Veronese map** of
degree `t` sends `x : ι → R` to the vector `x^{(t)}` of its monomials of degree `t`. A form `p`
of degree `t` is the linear form `λ_p(y) = ∑_μ coeff_μ(p) y_μ` on `R^{monomials}`, and
`λ_p(x^{(t)}) = p(x)`. Conversely every linear form `λ` is `λ_q` for the form
`q = ∑_μ λ(e_μ) X^μ` of degree `t`. So a hyperplane through the Veronese image of a set of points
is a form of degree `t` vanishing on it.

## Main definitions

* `MvPolynomial.degreeMonomials`: the monomials of degree `t`.
* `MvPolynomial.veronese`: the Veronese map `x ↦ x^{(t)}`.
* `MvPolynomial.coeffForm`: `λ_p`.
* `MvPolynomial.ofDual`: the form of degree `t` of a linear form.
* `MvPolynomial.homogeneousEquivDual`: the forms of degree `t` are the linear forms on the
  Veronese space.

## Main results

* `MvPolynomial.coeffForm_veronese`: `λ_p(x^{(t)}) = p(x)` for a form `p` of degree `t`.
* `MvPolynomial.coeffForm_ofDual`, `MvPolynomial.eval_ofDual`: the converse.
* `MvPolynomial.veronese_comp`: the Veronese map commutes with ring homomorphisms.
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {ι R S : Type*} [Fintype ι] [CommRing R] [CommRing S]

variable (ι) in
/-- **The monomials of degree `t`**, `Finset.finsuppAntidiag univ t` with the decidability of
equality on `ι` fixed once. -/
noncomputable def degreeMonomials (t : ℕ) : Finset (ι →₀ ℕ) := by
  classical exact (univ : Finset ι).finsuppAntidiag t

/-- The monomials of degree `t` are the `μ` with `μ.degree = t`. -/
theorem mem_degreeMonomials {μ : ι →₀ ℕ} {t : ℕ} :
    μ ∈ degreeMonomials ι t ↔ μ.degree = t := by
  classical
  simp [degreeMonomials, Finsupp.degree_eq_sum]

/-- The pure power `X_j^t` is a monomial of degree `t`. -/
theorem single_mem_degreeMonomials (j : ι) (t : ℕ) :
    Finsupp.single j t ∈ degreeMonomials ι t := by
  rw [mem_degreeMonomials, Finsupp.degree_single]

/-- **The Veronese map** of degree `t`: the monomials `x^μ` of degree `t`. -/
def veronese (t : ℕ) (x : ι → R) : degreeMonomials ι t → R :=
  fun μ ↦ μ.1.prod fun j n ↦ x j ^ n

theorem veronese_apply (t : ℕ) (x : ι → R) (μ : degreeMonomials ι t) :
    veronese t x μ = μ.1.prod fun j n ↦ x j ^ n :=
  rfl

/-- The pure power coordinate of the Veronese map. -/
theorem veronese_single (t : ℕ) (x : ι → R) (j : ι) :
    veronese t x ⟨Finsupp.single j t, single_mem_degreeMonomials j t⟩ = x j ^ t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [veronese]
  · simp [veronese, Finsupp.prod_single_index]

/-- **The Veronese map commutes with ring homomorphisms.** -/
theorem veronese_comp (f : R →+* S) (t : ℕ) (x : ι → R) :
    veronese t (f ∘ x) = f ∘ veronese t x := by
  funext μ
  simp [veronese]

/-- A nonzero point has a nonzero Veronese image. -/
theorem veronese_ne_zero [IsDomain R] (t : ℕ) {x : ι → R} (hx : x ≠ 0) : veronese t x ≠ 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
  intro h
  have := congrFun h ⟨Finsupp.single j t, single_mem_degreeMonomials j t⟩
  rw [veronese_single] at this
  exact pow_ne_zero t hj this

/-- **The linear form of a polynomial**: `λ_p(y) = ∑_μ coeff_μ(p) y_μ` over the monomials of
degree `t`. -/
noncomputable def coeffForm (t : ℕ) (p : MvPolynomial ι R) :
    Module.Dual R (degreeMonomials ι t → R) :=
  ∑ μ, p.coeff μ.1 • LinearMap.proj μ

theorem coeffForm_apply (t : ℕ) (p : MvPolynomial ι R)
    (y : degreeMonomials ι t → R) :
    coeffForm t p y = ∑ μ, p.coeff μ.1 * y μ := by
  simp [coeffForm]

/-- **`λ_p(x^{(t)}) = p(x)`** for a form `p` of degree `t`. -/
theorem coeffForm_veronese {t : ℕ} {p : MvPolynomial ι R} (hp : p.IsHomogeneous t)
    (x : ι → R) : coeffForm t p (veronese t x) = eval x p := by
  classical
  rw [coeffForm_apply, eval_eq]
  have hsub : p.support ⊆ degreeMonomials ι t := fun d hd ↦
    mem_degreeMonomials.2 (by
      by_contra h
      exact (mem_support_iff.1 hd) (hp.coeff_eq_zero h))
  rw [Finset.sum_subset hsub fun d _ hd ↦ by simp [notMem_support_iff.1 hd],
    ← Finset.sum_coe_sort (degreeMonomials ι t)]
  rfl

/-- **The form of degree `t` of a linear form**: `q = ∑_μ λ(e_μ) X^μ`. -/
noncomputable def ofDual (t : ℕ) (l : Module.Dual R (degreeMonomials ι t → R)) :
    MvPolynomial ι R :=
  ∑ μ, monomial μ.1 (l (Pi.basisFun R _ μ))

/-- The form of a linear form is homogeneous of degree `t`. -/
theorem isHomogeneous_ofDual (t : ℕ)
    (l : Module.Dual R (degreeMonomials ι t → R)) :
    (ofDual t l).IsHomogeneous t :=
  IsHomogeneous.sum _ _ _ fun μ _ ↦
    isHomogeneous_monomial _ (mem_degreeMonomials.1 μ.2)

/-- The coefficients of the form of `λ` are the values of `λ` at the unit vectors. -/
theorem coeff_ofDual (t : ℕ) (l : Module.Dual R (degreeMonomials ι t → R))
    (μ : degreeMonomials ι t) : (ofDual t l).coeff μ.1 = l (Pi.basisFun R _ μ) := by
  classical
  rw [ofDual, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single μ (fun ν _ hν ↦ by simp [hν])
    (fun h ↦ absurd (Finset.mem_univ μ) h)]
  simp

/-- **Every linear form is `λ_q`** for its form `q` of degree `t`. -/
theorem coeffForm_ofDual (t : ℕ) (l : Module.Dual R (degreeMonomials ι t → R)) :
    coeffForm t (ofDual t l) = l := by
  classical
  refine LinearMap.ext fun y ↦ ?_
  have hl : l y = ∑ μ, l (Pi.basisFun R _ μ) * y μ := by
    conv_lhs => rw [← (Pi.basisFun R _).sum_repr y]
    simp [map_sum, mul_comm]
  rw [coeffForm_apply, hl]
  simp only [coeff_ofDual]

/-- **The form of `λ` evaluates as `λ` on the Veronese image.** -/
theorem eval_ofDual (t : ℕ) (l : Module.Dual R (degreeMonomials ι t → R))
    (x : ι → R) : eval x (ofDual t l) = l (veronese t x) := by
  rw [← coeffForm_veronese (isHomogeneous_ofDual t l), coeffForm_ofDual]

/-- `λ_p` at a unit vector is a coefficient of `p`. -/
theorem coeffForm_basisFun (t : ℕ) (p : MvPolynomial ι R) (μ : degreeMonomials ι t) :
    coeffForm t p (Pi.basisFun R _ μ) = p.coeff μ.1 := by
  classical
  simp [coeffForm_apply, Pi.single_apply]

/-- **A form of degree `t` is the form of its linear form.** -/
theorem ofDual_coeffForm {t : ℕ} {p : MvPolynomial ι R} (hp : p.IsHomogeneous t) :
    ofDual t (coeffForm t p) = p := by
  ext ν
  by_cases hν : ν ∈ degreeMonomials ι t
  · rw [coeff_ofDual t _ ⟨ν, hν⟩, coeffForm_basisFun]
  · rw [(isHomogeneous_ofDual t _).coeff_eq_zero (mt mem_degreeMonomials.2 hν),
      hp.coeff_eq_zero (mt mem_degreeMonomials.2 hν)]

variable (ι R) in
/-- **The forms of degree `t` are the linear forms on the Veronese space**, `p ↦ λ_p`. -/
noncomputable def homogeneousEquivDual (t : ℕ) :
    homogeneousSubmodule ι R t ≃ₗ[R] Module.Dual R (degreeMonomials ι t → R) where
  toFun p := coeffForm t p.1
  invFun l := ⟨ofDual t l, isHomogeneous_ofDual t l⟩
  map_add' p q := LinearMap.ext fun y ↦ by
    simp [coeffForm_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a p := LinearMap.ext fun y ↦ by
    simp [coeffForm_apply, Finset.mul_sum, mul_assoc]
  left_inv p := Subtype.ext (ofDual_coeffForm p.2)
  right_inv l := coeffForm_ofDual t l

theorem homogeneousEquivDual_apply (t : ℕ) (p : homogeneousSubmodule ι R t) :
    homogeneousEquivDual ι R t p = coeffForm t p.1 :=
  rfl

end MvPolynomial
