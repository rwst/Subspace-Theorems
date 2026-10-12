/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Hadamard's inequality

`|det A| ≤ ∏_i ‖A_i‖₂` for a square matrix over `ℝ` or `ℂ` (`Matrix.norm_det_le_prod_sqrt`). The
rows are written in the orthonormal basis that Gram–Schmidt makes from them, in which their
matrix is triangular; the change from the standard basis has a determinant of absolute value `1`.
-/

@[expose] public section

open Finset InnerProductSpace

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Hadamard's inequality**: `|det A| ≤ ∏_i (∑_j |a_{ij}|²)^{1/2}`. -/
theorem norm_det_le_prod_sqrt {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) :
    ‖A.det‖ ≤ ∏ i, √(∑ j, ‖A i j‖ ^ 2) := by
  set v : Fin N → EuclideanSpace 𝕜 (Fin N) := fun i ↦ WithLp.toLp 2 (A i)
  set e := EuclideanSpace.basisFun (Fin N) 𝕜
  have h : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin N)) = Fintype.card (Fin N) := by simp
  set b := gramSchmidtOrthonormalBasis h v
  have hdet : e.toBasis.det v = A.det := by
    rw [Module.Basis.det_apply, ← det_transpose]
    congr 1
  have hb : e.toBasis.det v = e.toBasis.det b * b.toBasis.det v := by
    conv_lhs => rw [e.toBasis.det.eq_smul_basis_det b.toBasis]
    rfl
  rw [← hdet, hb, norm_mul, e.det_to_matrix_orthonormalBasis b,
    one_mul, gramSchmidtOrthonormalBasis_det, norm_prod]
  gcongr with i
  calc ‖inner 𝕜 (b i) (v i)‖ ≤ ‖b i‖ * ‖v i‖ := norm_inner_le_norm _ _
    _ = √(∑ j, ‖A i j‖ ^ 2) := by
      rw [b.orthonormal.1 i, one_mul, EuclideanSpace.norm_eq]

end Matrix
