/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.additions.Points
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# The forms of the three Subspace applications

The forms `L₁, L₂, L₃, L₄ = X₀` of §3 have coefficients `b₀ + b₁ α + b₂ α²` with `bᵢ ∈ {-1, 0, 1}`
(`Real.formCoef`); their determinant is `-1`. Two further systems of three forms in three
variables are used:

* **on a hyperplane `z^⊥`** (`Real.projCoef`): with `z_j ≠ 0`, the coordinate `x_j` is eliminated
  and the forms `z_j L_i` (`i = 1, 2, 3`) are written in the other three coordinates. Their
  determinant is `(-1)^j z_j² Λ` with `Λ = z₀ + (z₁ + z₂) α + z₃ α²` (`Real.det_projCoef`).
* **on `T₀ = {X₁ = X₂}`** (`Real.t0Coef`): the forms `L₁, L₂, L₄` in `(X₀, X₁, X₃)`, of
  determinant `1`.

The hyperplane through three integer points is given by their cross product (`Real.crossZ`),
whose entries are `3 × 3` minors, at most `6 H³`.
-/

@[expose] public section

open Finset Module

namespace Real

/-- The coefficients of `L₁, L₂, L₃, L₄`: `formCoef i k` is the coefficient of `X_k` in the
`i`-th form, as `(b₀, b₁, b₂)` for `b₀ + b₁ α + b₂ α²`. -/
def formCoef : Fin 4 → Fin 4 → Fin 3 → ℤ :=
  ![![![0, 0, 1], ![0, -1, 0], ![0, -1, 0], ![1, 0, 0]],
    ![![0, 1, 0], ![-1, 0, 0], 0, 0],
    ![![0, 1, 0], 0, ![-1, 0, 0], 0],
    ![![1, 0, 0], 0, 0, 0]]

theorem abs_formCoef_le (i k : Fin 4) (m : Fin 3) : |formCoef i k m| ≤ 1 := by
  fin_cases i <;> fin_cases k <;> fin_cases m <;> decide

/-- The value of the `i`-th form at `v`. -/
noncomputable def formVal (α : ℝ) (i : Fin 4) (v : Fin 4 → ℤ) : ℝ :=
  ∑ k, quadVal α (formCoef i k) * v k

theorem formVal_zero (α : ℝ) (v : Fin 4 → ℤ) : formVal α 0 v = formL1 α v := by
  simp [formVal, formCoef, formL1, quadVal, Fin.sum_univ_four]; ring

theorem formVal_one (α : ℝ) (v : Fin 4 → ℤ) : formVal α 1 v = formL2 α v := by
  simp [formVal, formCoef, formL2, quadVal, Fin.sum_univ_four]; ring

theorem formVal_two (α : ℝ) (v : Fin 4 → ℤ) : formVal α 2 v = formL3 α v := by
  simp [formVal, formCoef, formL3, quadVal, Fin.sum_univ_four]; ring

theorem formVal_three (α : ℝ) (v : Fin 4 → ℤ) : formVal α 3 v = v 0 := by
  simp [formVal, formCoef, quadVal, Fin.sum_univ_four]

theorem det_formCoef (α : ℝ) : (Matrix.of fun i k ↦ quadVal α (formCoef i k)).det = -1 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, formCoef, quadVal, Fin.succAbove]
  ring

/-! ### On a hyperplane -/

/-- `b₀ + b₁ α + b₂ α²` is linear in `b`. -/
theorem quadVal_mul_sub (α : ℝ) (a d : ℤ) (b c : Fin 3 → ℤ) :
    quadVal α (fun m ↦ a * b m - c m * d) = a * quadVal α b - quadVal α c * d := by
  simp only [quadVal]; push_cast; ring

/-- **The forms on `z^⊥`**: `z_j L_i` with `X_j = -(∑_{k ≠ j} z_k X_k) / z_j` eliminated, in the
coordinates `X_{j.succAbove k}`, for `i = 1, 2, 3`. -/
def projCoef (z : Fin 4 → ℤ) (j : Fin 4) (i k : Fin 3) : Fin 3 → ℤ :=
  fun m ↦ z j * formCoef i.castSucc (j.succAbove k) m - formCoef i.castSucc j m * z (j.succAbove k)

theorem abs_projCoef_le {z : Fin 4 → ℤ} {Z : ℝ} (hz : ∀ i, |(z i : ℝ)| ≤ Z) (j : Fin 4)
    (i k : Fin 3) (m : Fin 3) : |(projCoef z j i k m : ℝ)| ≤ 2 * Z := by
  have h1 : |(formCoef i.castSucc (j.succAbove k) m : ℝ)| ≤ 1 := by
    exact_mod_cast abs_formCoef_le _ _ _
  have h2 : |(formCoef i.castSucc j m : ℝ)| ≤ 1 := by exact_mod_cast abs_formCoef_le _ _ _
  change |((z j * formCoef i.castSucc (j.succAbove k) m -
    formCoef i.castSucc j m * z (j.succAbove k) : ℤ) : ℝ)| ≤ 2 * Z
  push_cast
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul]
  have := hz j
  have := hz (j.succAbove k)
  nlinarith [abs_nonneg (z j : ℝ), abs_nonneg (z (j.succAbove k) : ℝ),
    abs_nonneg (formCoef i.castSucc (j.succAbove k) m : ℝ),
    abs_nonneg (formCoef i.castSucc j m : ℝ)]

theorem quadVal_projCoef (α : ℝ) (z : Fin 4 → ℤ) (j : Fin 4) (i k : Fin 3) :
    quadVal α (projCoef z j i k) = z j * quadVal α (formCoef i.castSucc (j.succAbove k)) -
      quadVal α (formCoef i.castSucc j) * z (j.succAbove k) :=
  quadVal_mul_sub _ _ _ _ _

/-- **The value of the projected forms**: `z_j L_i(v)` for `v ⊥ z`. -/
theorem sum_projCoef (α : ℝ) {z v : Fin 4 → ℤ} (hzv : ∑ i, z i * v i = 0) (j : Fin 4)
    (i : Fin 3) :
    ∑ k, quadVal α (projCoef z j i k) * v (j.succAbove k) = z j * formVal α i.castSucc v := by
  simp only [quadVal_projCoef]
  have h1 := Fin.sum_univ_succAbove (fun k ↦ quadVal α (formCoef i.castSucc k) * v k) j
  have h2 := Fin.sum_univ_succAbove (fun k ↦ (z k : ℝ) * v k) j
  have h0 : ∑ k, (z k : ℝ) * v k = 0 := by exact_mod_cast hzv
  rw [formVal, h1]
  have e : ∑ k : Fin 3, ((z j : ℝ) * quadVal α (formCoef i.castSucc (j.succAbove k)) -
      quadVal α (formCoef i.castSucc j) * z (j.succAbove k)) * v (j.succAbove k) =
      z j * ∑ k : Fin 3, quadVal α (formCoef i.castSucc (j.succAbove k)) * v (j.succAbove k) -
      quadVal α (formCoef i.castSucc j) * ∑ k : Fin 3, (z (j.succAbove k) : ℝ) *
        v (j.succAbove k) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  rw [e]
  rw [h0] at h2
  linear_combination (quadVal α (formCoef i.castSucc j)) * h2

/-- `Λ = z₀ + (z₁ + z₂) α + z₃ α²`. -/
def lamCoef (z : Fin 4 → ℤ) : Fin 3 → ℤ := ![z 0, z 1 + z 2, z 3]

/-- **The determinant of the projected forms** is `(-1)^j z_j² Λ`. -/
theorem det_projCoef (α : ℝ) (z : Fin 4 → ℤ) (j : Fin 4) :
    (Matrix.of fun i k ↦ quadVal α (projCoef z j i k)).det =
      (-1) ^ (j : ℕ) * (z j : ℝ) ^ 2 * quadVal α (lamCoef z) := by
  rw [Matrix.det_fin_three]
  fin_cases j <;>
  · simp [projCoef, formCoef, quadVal, lamCoef, Fin.succAbove, Fin.lt_def]
    ring

/-! ### On `T₀` -/

/-- **The forms on `T₀ = {X₁ = X₂}`**: `L₁, L₂, L₄` in the coordinates `(X₀, X₁, X₃)`. -/
def t0Coef : Fin 3 → Fin 3 → Fin 3 → ℤ :=
  ![![![0, 0, 1], ![0, -2, 0], ![1, 0, 0]],
    ![![0, 1, 0], ![-1, 0, 0], 0],
    ![![1, 0, 0], 0, 0]]

theorem abs_t0Coef_le (i k m : Fin 3) : |t0Coef i k m| ≤ 2 := by
  fin_cases i <;> fin_cases k <;> fin_cases m <;> decide

/-- The coordinates `(X₀, X₁, X₃)`. -/
def t0Pt (v : Fin 4 → ℤ) : Fin 3 → ℤ := ![v 0, v 1, v 3]

theorem det_t0Coef (α : ℝ) : (Matrix.of fun i k ↦ quadVal α (t0Coef i k)).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [t0Coef, quadVal]

theorem sum_t0Coef_zero (α : ℝ) {v : Fin 4 → ℤ} (hv : v 1 = v 2) :
    ∑ k, quadVal α (t0Coef 0 k) * t0Pt v k = formL1 α v := by
  simp [t0Coef, t0Pt, quadVal, formL1, Fin.sum_univ_three, hv]; ring

theorem sum_t0Coef_one (α : ℝ) (v : Fin 4 → ℤ) :
    ∑ k, quadVal α (t0Coef 1 k) * t0Pt v k = formL2 α v := by
  simp [t0Coef, t0Pt, quadVal, formL2, Fin.sum_univ_three]; ring

theorem sum_t0Coef_two (α : ℝ) (v : Fin 4 → ℤ) :
    ∑ k, quadVal α (t0Coef 2 k) * t0Pt v k = v 0 := by
  simp [t0Coef, t0Pt, quadVal, Fin.sum_univ_three]

/-! ### The cross product -/

/-- **The cross product** of three points of `ℤ⁴`: `(-1)^i` times the minor without column `i`. -/
def crossZ (x y w : Fin 4 → ℤ) (i : Fin 4) : ℤ :=
  (-1) ^ (i : ℕ) * (Matrix.of fun r k ↦ ![x, y, w] r (i.succAbove k)).det

/-- **Laplace's expansion**: `∑ uᵢ (x × y × w)ᵢ = det (u, x, y, w)`. -/
theorem sum_mul_crossZ (u x y w : Fin 4 → ℤ) :
    ∑ i, u i * crossZ x y w i = (Matrix.of ![u, x, y, w]).det := by
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [crossZ, Matrix.of_apply, Matrix.cons_val_zero]
  rw [show (Matrix.of ![u, x, y, w]).submatrix Fin.succ i.succAbove =
    Matrix.of fun r k ↦ ![x, y, w] r (i.succAbove k) from by
      ext r k; simp [Matrix.submatrix]]
  ring

theorem sum_crossZ_mul_left (x y w : Fin 4 → ℤ) : ∑ i, crossZ x y w i * x i = 0 := by
  have := sum_mul_crossZ x x y w
  rw [Matrix.det_zero_of_row_eq (show (0 : Fin 4) ≠ 1 by decide) rfl] at this
  rw [← this]; exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

theorem sum_crossZ_mul_mid (x y w : Fin 4 → ℤ) : ∑ i, crossZ x y w i * y i = 0 := by
  have := sum_mul_crossZ y x y w
  rw [Matrix.det_zero_of_row_eq (show (0 : Fin 4) ≠ 2 by decide) rfl] at this
  rw [← this]; exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

theorem sum_crossZ_mul_right (x y w : Fin 4 → ℤ) : ∑ i, crossZ x y w i * w i = 0 := by
  have := sum_mul_crossZ w x y w
  rw [Matrix.det_zero_of_row_eq (show (0 : Fin 4) ≠ 3 by decide) rfl] at this
  rw [← this]; exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- The entries of the cross product are at most `6 H³`. -/
theorem abs_crossZ_le {x y w : Fin 4 → ℤ} {H : ℝ} (hx : ∀ i, |(x i : ℝ)| ≤ H)
    (hy : ∀ i, |(y i : ℝ)| ≤ H) (hw : ∀ i, |(w i : ℝ)| ≤ H) (i : Fin 4) :
    |(crossZ x y w i : ℝ)| ≤ 6 * H ^ 3 := by
  have hdet := Matrix.det_le (abv := AbsoluteValue.abs)
    (A := (Matrix.of fun r k ↦ ((![x, y, w] r (i.succAbove k) : ℤ) : ℝ))) (x := H)
    fun r k ↦ by
      fin_cases r
      · exact hx _
      · exact hy _
      · exact hw _
  simp only [Fintype.card_fin, AbsoluteValue.abs_apply, nsmul_eq_mul] at hdet
  have hmap : ((Matrix.of fun r k ↦ ![x, y, w] r (i.succAbove k)).map fun a : ℤ ↦ (a : ℝ)) =
      Matrix.of fun r k ↦ ((![x, y, w] r (i.succAbove k) : ℤ) : ℝ) := by
    ext r k; rfl
  rw [crossZ]
  push_cast
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, hmap]
  refine hdet.trans (le_of_eq ?_)
  norm_num [Nat.factorial]

/-- **The cross product of independent points is not `0`**: some unit vector completes them to
a basis, and then the determinant is not `0`. -/
theorem crossZ_ne_zero {x y w : Fin 4 → ℤ}
    (hli : LinearIndependent ℚ ![ptQ x, ptQ y, ptQ w]) : crossZ x y w ≠ 0 := by
  intro h0
  set W := Submodule.span ℚ (Set.range ![ptQ x, ptQ y, ptQ w])
  have hW : finrank ℚ W = 3 := by rw [finrank_span_eq_card hli, Fintype.card_fin]
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, Pi.single i (1 : ℚ) ∉ W := by
    by_contra! hall
    have htop : W = ⊤ := by
      refine eq_top_iff.2 fun u _ ↦ ?_
      rw [← Finset.univ_sum_single u]
      refine Submodule.sum_mem _ fun i _ ↦ ?_
      rw [show Pi.single i (u i) = u i • Pi.single i (1 : ℚ) by
        ext k; by_cases h : k = i <;> simp [h]]
      exact Submodule.smul_mem _ _ (hall i)
    rw [htop, finrank_top, Module.finrank_fin_fun] at hW
    omega
  have hli4 : LinearIndependent ℚ ![Pi.single i (1 : ℚ), ptQ x, ptQ y, ptQ w] :=
    linearIndependent_finCons.2 ⟨hli, hi⟩
  have hunit := (Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of
    ![Pi.single i (1 : ℚ), ptQ x, ptQ y, ptQ w])).1 hli4
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hunit
  apply hunit
  -- the determinant is the `i`-th entry of the cross product
  have hcast : (Matrix.of ![Pi.single i (1 : ℚ), ptQ x, ptQ y, ptQ w]) =
      (Matrix.of ![Pi.single i (1 : ℤ), x, y, w]).map (Int.castRingHom ℚ) := by
    ext r k
    fin_cases r <;> simp [ptQ, Pi.single_apply]
  rw [hcast]
  change ((Int.castRingHom ℚ).mapMatrix (Matrix.of ![Pi.single i (1 : ℤ), x, y, w])).det = 0
  rw [← RingHom.map_det, ← sum_mul_crossZ, h0]
  simp

end Real
