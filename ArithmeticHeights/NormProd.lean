/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The algebra norm of a product and of a tuple

The norm of an element of a product algebra is the product of the norms of its components, and the
norm of a tuple in `η → A` is the product of the norms of its entries. Both are the statement that
the matrix of multiplication is block diagonal in a basis adapted to the decomposition.

These are what compute `Algebra.norm ℝ` on the mixed space `ℝ^{r₁} × ℂ^{r₂}` of a number field,
where the answer is `∏_{w real} z_w · ∏_{w complex} |z_w|²` — the archimedean local factor of a
height, and the determinant of the realification of a `K ⊗ ℝ`-linear map.

## Main results

* `Algebra.norm_prod`: `N(x, y) = N x · N y`.
* `Algebra.norm_pi`: `N x = ∏ i, N (x i)` for `x : η → A`.

## Implementation notes

`Algebra.norm_prod` is `LinearMap.det_prodMap` read through `Algebra.norm_apply`: multiplication
by `(x, y)` *is* the product map of multiplication by `x` and by `y`, so no basis is chosen. There
is no `LinearMap.det_pi`, so `Algebra.norm_pi` goes through `Algebra.norm_eq_matrix_det` on
`Pi.basis` instead, where the multiplication matrix is `Matrix.blockDiagonal` after the reindexing
`(Σ _ : η, κ) ≃ κ × η` that `Matrix.blockDiagonal`'s index convention asks for.

Both are stated for a commutative `A`; nothing below needs more, and the algebra norm of a
noncommutative algebra is not what the mixed space calls for.

This is Layer 4.3 of the `ArithmeticHeights` roadmap, infrastructure for the number-field case.
-/

public section

open Module Matrix

/-- **The algebra norm of a pair is the product of the norms.** -/
theorem Algebra.norm_prod {R : Type*} [CommRing R] {A B : Type*} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Free R A] [Module.Finite R A] [Module.Free R B]
    [Module.Finite R B] (x : A × B) :
    Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by
  have h : (LinearMap.mul R (A × B)) x
      = LinearMap.prodMap (LinearMap.mul R A x.1) (LinearMap.mul R B x.2) :=
    LinearMap.ext fun _ ↦ rfl
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, show
    (Algebra.lmul R (A × B)) x = (LinearMap.mul R (A × B)) x from rfl, h, LinearMap.det_prodMap]
  rfl

/-- **The algebra norm of a tuple is the product of the norms of its entries.** -/
theorem Algebra.norm_pi {R : Type*} [CommRing R] {η : Type*} [Fintype η]
    {A : Type*} [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A]
    (x : η → A) : Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by
  classical
  set b := Module.Free.chooseBasis R A with hb
  set B := Pi.basis (fun _ : η ↦ b) with hB
  set e : ((_ : η) × Module.Free.ChooseBasisIndex R A) ≃
      (Module.Free.ChooseBasisIndex R A × η) :=
    (Equiv.sigmaEquivProd η _).trans (Equiv.prodComm η _) with he
  have key : Algebra.leftMulMatrix B x
      = (Matrix.blockDiagonal (fun i ↦ Algebra.leftMulMatrix b (x i))).submatrix e e := by
    ext ⟨i, k⟩ ⟨j, l⟩
    rw [Algebra.leftMulMatrix_apply, Algebra.toMatrix_lmul' B x]
    simp only [Matrix.submatrix_apply, he, Equiv.trans_apply, Equiv.sigmaEquivProd_apply,
      Equiv.prodComm_apply, Prod.swap_prod_mk, Matrix.blockDiagonal_apply]
    rw [hB, Pi.basis_apply, Pi.basis_repr]
    by_cases h : i = j
    · subst h
      simp only [Pi.mul_apply, Pi.single_eq_same, Algebra.leftMulMatrix_apply,
        Algebra.toMatrix_lmul', ite_true]
    · simp [h]
  rw [Algebra.norm_eq_matrix_det B, key, Matrix.det_submatrix_equiv_self,
    Matrix.det_blockDiagonal]
  exact Finset.prod_congr rfl fun i _ ↦ (Algebra.norm_eq_matrix_det b (x i)).symm

end
