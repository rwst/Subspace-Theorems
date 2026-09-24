/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

-- Used only inside proofs.
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Pi

/-!
# Linear forms carried along a ring homomorphism

A linear form on `Fⁱ` is determined by its `#ι` coefficients `M (Pi.single j 1)`, so a ring
homomorphism `f : F →+* E` carries it to a linear form on `Eⁱ`: `Module.Dual.compRingHom M f` is
the form with the coefficients `f (M (Pi.single j 1))`. Two operations the Subspace Theorem with
algebraic coefficients needs are this one map:

* the **base change** of a system of forms along `algebraMap F E`, which is how forms with
  coefficients in `F` become forms over a larger field;
* the **conjugation** of a system of forms by a field automorphism `σ`, which is how the forms at
  one place above `v` produce forms at every other place above `v`.

That both are the same construction is what makes the composite `σ ∘ algebraMap F E` — the only
homomorphism that actually appears downstream — a single application of it.

## Main results

* `Module.Dual.compRingHom` and `Module.Dual.compRingHom_apply`: the construction.
* `Module.Dual.compRingHom_comp`: the evaluation identity `(M.compRingHom f) (f ∘ x) = f (M x)`,
  which is the only property of it a local factor sees.
* `Module.Dual.compRingHom_compRingHom`: it is functorial, so a conjugated base change is a single
  `compRingHom`.
* `Module.Dual.linearIndependent_compRingHom`: a linearly independent system stays linearly
  independent, over the larger field.
* `Module.Dual.linearIndependent_iff_isUnit_coeffMatrix`: what that rests on — a system of `#ι`
  forms on `Fⁱ` is independent exactly when its coefficient matrix is invertible.

## Implementation notes

⚠ **Independence over the larger field is a determinant statement, not a formal one.** That a
family stays independent under base change is false for a general ring map and for a family that
is not square; here the family has exactly `#ι` members and `Dual F (ι → F)` has dimension `#ι`,
so independence is invertibility of the coefficient matrix, and `RingHom.map_det` carries
invertibility along any homomorphism of fields. The direct argument — pull a dependence back
along `f` — works for an automorphism but not for an extension, so both cases are routed through
the matrix.

This is part of Layer 6.3 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Matrix Module

namespace Module.Dual

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F E : Type*} [CommRing F] [CommRing E]

/-- **A linear form is its vector of coefficients**: `M x = ∑ j, M (Pi.single j 1) * x j`. -/
theorem eq_sum_coeff (M : Dual F (ι → F)) (x : ι → F) :
    M x = ∑ j, M (Pi.single j 1) * x j := by
  rw [LinearMap.pi_apply_eq_sum_univ M x]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [smul_eq_mul, mul_comm]
  congr 2
  funext k
  simp [Pi.single_apply, eq_comm]

/-- **A linear form on `Fⁱ` carried along a ring homomorphism `f : F →+* E`**: the form on `Eⁱ`
whose coefficients are the images of the coefficients of `M`. -/
def compRingHom (M : Dual F (ι → F)) (f : F →+* E) : Dual E (ι → E) :=
  ∑ j, f (M (Pi.single j 1)) • (LinearMap.proj j : Dual E (ι → E))

theorem compRingHom_apply (M : Dual F (ι → F)) (f : F →+* E) (z : ι → E) :
    M.compRingHom f z = ∑ j, f (M (Pi.single j 1)) * z j := by
  simp [compRingHom]

@[simp] theorem compRingHom_single (M : Dual F (ι → F)) (f : F →+* E) (j : ι) :
    M.compRingHom f (Pi.single j 1) = f (M (Pi.single j 1)) := by
  rw [compRingHom_apply, Finset.sum_eq_single j (fun b _ hb ↦ by
    rw [Pi.single_eq_of_ne hb, mul_zero]) (fun h ↦ absurd (Finset.mem_univ j) h),
    Pi.single_eq_same, mul_one]

/-- **The evaluation identity.** On a point of `Fⁱ` carried along `f`, the carried form takes the
carried value. This is the whole of what a local factor of the Subspace Theorem uses. -/
theorem compRingHom_comp (M : Dual F (ι → F)) (f : F →+* E) (x : ι → F) :
    M.compRingHom f (fun i ↦ f (x i)) = f (M x) := by
  rw [compRingHom_apply, eq_sum_coeff M x, map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [map_mul]

/-- **Functoriality**: a base change followed by a conjugation is a single `compRingHom`. -/
theorem compRingHom_compRingHom {E' : Type*} [CommRing E'] (M : Dual F (ι → F)) (f : F →+* E)
    (g : E →+* E') : (M.compRingHom f).compRingHom g = M.compRingHom (g.comp f) := by
  refine LinearMap.ext fun z ↦ ?_
  rw [compRingHom_apply, compRingHom_apply]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [compRingHom_single]; rfl

section Field

variable {F E : Type*} [Field F] [Field E]

/-- **The coefficient matrix of a family of linear forms on `Fⁱ`**, the `i`-th row being the
coefficients of the `i`-th form. -/
def coeffMatrix (L : ι → Dual F (ι → F)) : Matrix ι ι F :=
  Matrix.of fun i j ↦ L i (Pi.single j 1)

/-- A linear combination of forms vanishes exactly when the same combination of the rows of the
coefficient matrix does. -/
theorem sum_smul_eq_zero_iff (L : ι → Dual F (ι → F)) (c : ι → F) :
    ∑ i, c i • L i = 0 ↔ ∑ i, c i • coeffMatrix L i = 0 := by
  constructor
  · intro h
    funext j
    have := congrFun (congrArg (fun (M : Dual F (ι → F)) ↦ (M : (ι → F) → F)) h) (Pi.single j 1)
    simpa [coeffMatrix, Finset.sum_apply] using this
  · intro h
    refine LinearMap.ext fun z ↦ ?_
    have hz : ∀ j, ∑ i, c i * L i (Pi.single j 1) = 0 := fun j ↦ by
      have := congrFun h j
      simpa [coeffMatrix, Finset.sum_apply] using this
    simp only [LinearMap.zero_apply]
    calc (∑ i, c i • L i) z = ∑ i, c i * L i z := by simp [Finset.sum_apply]
      _ = ∑ i, c i * ∑ j, L i (Pi.single j 1) * z j := by
          exact Finset.sum_congr rfl fun i _ ↦ by rw [eq_sum_coeff (L i) z]
      _ = ∑ j, (∑ i, c i * L i (Pi.single j 1)) * z j := by
          simp_rw [Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
          exact Finset.sum_comm
      _ = 0 := by simp [hz]

/-- **A square system of linear forms is independent exactly when its coefficient matrix is
invertible.** -/
theorem linearIndependent_iff_isUnit_coeffMatrix (L : ι → Dual F (ι → F)) :
    LinearIndependent F L ↔ IsUnit (coeffMatrix L) := by
  rw [← Matrix.linearIndependent_rows_iff_isUnit, Fintype.linearIndependent_iff,
    Fintype.linearIndependent_iff]
  exact forall_congr' fun c ↦ imp_congr_left (sum_smul_eq_zero_iff L c)

/-- **Independence survives a homomorphism of fields.** A system of `#ι` linearly independent
forms on `Fⁱ` carries to a linearly independent system on `Eⁱ`, for the base change and for a
conjugation alike. -/
theorem linearIndependent_compRingHom {L : ι → Dual F (ι → F)} (hL : LinearIndependent F L)
    (f : F →+* E) : LinearIndependent E fun i ↦ (L i).compRingHom f := by
  rw [linearIndependent_iff_isUnit_coeffMatrix] at hL ⊢
  have hmap : coeffMatrix (fun i ↦ (L i).compRingHom f) = (coeffMatrix L).map f := by
    ext i j
    simp [coeffMatrix, compRingHom_single]
  have hdet : ((coeffMatrix L).map f).det = f (coeffMatrix L).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [hmap, Matrix.isUnit_iff_isUnit_det, hdet]
  rw [Matrix.isUnit_iff_isUnit_det] at hL
  exact hL.map f

end Field

end Module.Dual
