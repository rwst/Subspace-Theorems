/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Additions.SubspaceCount
public import DiophantineApproximation.AlgebraicExponent

/-!
# Liouville's inequality for `b₀ + b₁ α + b₂ α²`

For a real algebraic `α` of degree at least `3`, the numbers `1, α, α²` are linearly independent
over `ℚ`, and an integer combination `b₀ + b₁ α + b₂ α²` with `|bᵢ| ≤ M` that is not `0` is at
least `c M^{-D}`, for constants `c > 0` and `D` depending on `α` only. This is the repository's
`Real.exists_pos_le_abs_aeval` at degree `2`.

## Main results

* `Real.quadVal_ne_zero`: `b₀ + b₁ α + b₂ α² ≠ 0` for `b ≠ 0`.
* `Real.exists_pos_le_abs_quadVal`: **Liouville's inequality**, `c ≤ |b₀ + b₁ α + b₂ α²| M ^ D`.
-/

@[expose] public section

open Polynomial

namespace Real

/-- The integer polynomial `b₂ X² + b₁ X + b₀`. -/
noncomputable def quadPoly (b : Fin 3 → ℤ) : ℤ[X] := C (b 2) * X ^ 2 + C (b 1) * X + C (b 0)

theorem aeval_quadPoly (α : ℝ) (b : Fin 3 → ℤ) : aeval α (quadPoly b) = quadVal α b := by
  simp [quadPoly, quadVal]
  ring

theorem natDegree_quadPoly_le (b : Fin 3 → ℤ) : (quadPoly b).natDegree ≤ 2 :=
  natDegree_quadratic_le

theorem coeff_quadPoly_zero (b : Fin 3 → ℤ) : (quadPoly b).coeff 0 = b 0 := by
  rw [quadPoly, coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp

theorem coeff_quadPoly_one (b : Fin 3 → ℤ) : (quadPoly b).coeff 1 = b 1 := by
  rw [quadPoly, coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp

theorem coeff_quadPoly_two (b : Fin 3 → ℤ) : (quadPoly b).coeff 2 = b 2 := by
  rw [quadPoly, coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp

theorem coeff_quadPoly_of_three_le (b : Fin 3 → ℤ) {i : ℕ} (hi : 3 ≤ i) :
    (quadPoly b).coeff i = 0 := by
  have : (quadPoly b).natDegree < i := (natDegree_quadPoly_le b).trans_lt (by omega)
  exact coeff_eq_zero_of_natDegree_lt this

theorem quadPoly_ne_zero {b : Fin 3 → ℤ} (hb : b ≠ 0) : quadPoly b ≠ 0 := by
  intro h
  refine hb (funext fun i ↦ ?_)
  fin_cases i
  · have := congrArg (coeff · 0) h
    simp only [coeff_quadPoly_zero, coeff_zero] at this
    simpa using this
  · have := congrArg (coeff · 1) h
    simp only [coeff_quadPoly_one, coeff_zero] at this
    simpa using this
  · have := congrArg (coeff · 2) h
    simp only [coeff_quadPoly_two, coeff_zero] at this
    simpa using this

variable {α : ℝ}

/-- **`1, α, α²` are linearly independent over `ℚ`** when `α` has degree at least `3`. -/
theorem quadVal_ne_zero (hdeg : 3 ≤ (minpoly ℚ α).natDegree) {b : Fin 3 → ℤ} (hb : b ≠ 0) :
    quadVal α b ≠ 0 := by
  intro h0
  set P : ℚ[X] := (quadPoly b).map (Int.castRingHom ℚ)
  have hP : P ≠ 0 := by
    intro hP
    refine quadPoly_ne_zero hb (Polynomial.ext fun i ↦ ?_)
    have := congrArg (coeff · i) hP
    simp only [P, coeff_map, eq_intCast, coeff_zero, Int.cast_eq_zero] at this
    simpa using this
  have hev : aeval α P = 0 := by
    rw [show P = (quadPoly b).map (algebraMap ℤ ℚ) from rfl, aeval_map_algebraMap,
      aeval_quadPoly, h0]
  have hdeg' := minpoly.degree_le_of_ne_zero ℚ α hP hev
  have h2 : P.natDegree ≤ 2 := (natDegree_map_le).trans (natDegree_quadPoly_le b)
  have := natDegree_le_natDegree hdeg'
  omega

/-- **Liouville's inequality for `b₀ + b₁ α + b₂ α²`**: for `α` algebraic of degree at least `3`
there are `c > 0` and `D` with `c ≤ |b₀ + b₁ α + b₂ α²| M ^ D` for every integer `b ≠ 0` with
`|bᵢ| ≤ M`. -/
theorem exists_pos_le_abs_quadVal (hα : IsAlgebraic ℚ α) (hdeg : 3 ≤ (minpoly ℚ α).natDegree) :
    ∃ c : ℝ, 0 < c ∧ ∃ D : ℕ, ∀ (b : Fin 3 → ℤ) (M : ℝ), b ≠ 0 → (∀ i, |(b i : ℝ)| ≤ M) →
      c ≤ |quadVal α b| * M ^ D := by
  obtain ⟨c, hc, h⟩ := exists_pos_le_abs_aeval hα 2
  set D := (minpoly ℚ α).natDegree - 1
  refine ⟨c, hc, D, fun b M hb hM ↦ ?_⟩
  set P := quadPoly b
  have hP := quadPoly_ne_zero hb
  have hS1 : 1 ≤ P.supNorm := one_le_supNorm hP
  have hSM : P.supNorm ≤ M := by
    refine supNorm_le_of_forall fun i ↦ ?_
    rw [Int.norm_eq_abs]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | rfl | hi
    · rw [coeff_quadPoly_zero]; exact_mod_cast hM 0
    · rw [coeff_quadPoly_one]; exact_mod_cast hM 1
    · rw [coeff_quadPoly_two]; exact_mod_cast hM 2
    · rw [coeff_quadPoly_of_three_le b hi]
      simpa using (abs_nonneg _).trans (hM 0)
  have hval := h P (natDegree_quadPoly_le b) (by rw [aeval_quadPoly]; exact quadVal_ne_zero hdeg hb)
  rw [aeval_quadPoly, Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv,
    div_le_iff₀ (by positivity)] at hval
  exact hval.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hSM D)
    (abs_nonneg _))

end Real
