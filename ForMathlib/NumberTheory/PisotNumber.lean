/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.NumberTheory.Real.GoldenRatio

-- Used only inside proofs.
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination

/-!
# Pisot and Salem numbers

A **Pisot number** (Pisot–Vijayaraghavan number) is a real algebraic integer `θ > 1` whose Galois
conjugates other than `θ` lie in the open unit disc. A **Salem number** is a real algebraic
integer `τ > 1` whose other conjugates lie in the closed unit disc, at least one of them on the
unit circle. Mathlib has neither.

The conjugates are the complex roots of `minpoly ℚ θ`.

## Main definitions

* `IsPisot`: a real number is a Pisot number.
* `IsSalem`: a real number is a Salem number.

## Main results

* `isPisot_goldenRatio`: the golden ratio is a Pisot number.

## Implementation notes

⚠ **The number itself is excluded through the cast.** "Every conjugate other than `θ`" is
`z ≠ (θ : ℂ)`. Since `minpoly ℚ θ` is separable, `θ` occurs once among the roots, so this
excludes exactly one root.

⚠ **Rational integers `b ≥ 2` are Pisot numbers**, vacuously: `minpoly ℚ b = X - b` has no other
root. They are not Salem numbers, which need a conjugate on the unit circle.

## References

M. J. Bertin, A. Decomps-Guilloux, M. Grandet-Hugot, M. Pathiaux-Delefosse and J.-P. Schreiber,
*Pisot and Salem numbers*, Birkhäuser, 1992. Ported from `ForMathlib/NumberTheory/PisotNumber.lean`
of the author's `lean-code` corpus; the definition of `IsPisot` was first used here by
`CorvajaZannier2004/`.
-/

@[expose] public section

open Polynomial

/-- A **Pisot number**: a real algebraic integer `α > 1` whose conjugates other than `α` lie in
the open unit disc. Rational integers `> 1` are Pisot numbers. -/
def IsPisot (α : ℝ) : Prop :=
  1 < α ∧ IsIntegral ℤ α ∧ ∀ z ∈ (minpoly ℚ α).aroots ℂ, z ≠ (α : ℂ) → ‖z‖ < 1

/-- A **Salem number**: a real algebraic integer `τ > 1` whose conjugates other than `τ` lie in the
closed unit disc, at least one of them on the unit circle. -/
def IsSalem (τ : ℝ) : Prop :=
  1 < τ ∧ IsIntegral ℤ τ ∧ (∀ z ∈ (minpoly ℚ τ).aroots ℂ, z ≠ (τ : ℂ) → ‖z‖ ≤ 1) ∧
    ∃ z ∈ (minpoly ℚ τ).aroots ℂ, z ≠ (τ : ℂ) ∧ ‖z‖ = 1

/-- A Pisot number is an algebraic integer `> 1` whose other conjugates lie in the closed unit
disc, the property shared with Salem numbers. -/
theorem IsPisot.norm_le_one {θ : ℝ} (h : IsPisot θ) :
    ∀ z ∈ (minpoly ℚ θ).aroots ℂ, z ≠ (θ : ℂ) → ‖z‖ ≤ 1 :=
  fun z hz hne ↦ (h.2.2 z hz hne).le

open Real in
/-- **The golden ratio is a Pisot number.** Its minimal polynomial divides `X ^ 2 - X - 1`, whose
other root `ψ = (1 - √5) / 2` has modulus `(√5 - 1) / 2 < 1`. -/
theorem isPisot_goldenRatio : IsPisot goldenRatio := by
  refine ⟨one_lt_goldenRatio, ?_, ?_⟩
  · refine ⟨X ^ 2 - X - 1, by monicity!, ?_⟩
    rw [← aeval_def]
    simp only [map_sub, map_pow, map_one, aeval_X]
    linarith [goldenRatio_sq]
  · intro z hz hzφ
    rw [Polynomial.mem_aroots'] at hz
    have hdvd : minpoly ℚ goldenRatio ∣ (X ^ 2 - X - 1 : ℚ[X]) := by
      apply minpoly.dvd
      simp only [map_sub, map_pow, map_one, aeval_X]
      linarith [goldenRatio_sq]
    obtain ⟨g, hg⟩ := hdvd
    have hquad : z ^ 2 - z - 1 = 0 := by
      have hz1 : (aeval z) (X ^ 2 - X - 1 : ℚ[X]) = 0 := by
        rw [hg, map_mul, hz.2, zero_mul]
      simpa only [map_sub, map_pow, map_one, aeval_X] using hz1
    -- `X ^ 2 - X - 1 = (X - φ)(X - ψ)`, from `φ + ψ = 1` and `φ ψ = -1`
    have hsum : (goldenRatio : ℂ) + (goldenConj : ℂ) = 1 := by
      rw [← Complex.ofReal_add, goldenRatio_add_goldenConj]; norm_num
    have hprod : (goldenRatio : ℂ) * (goldenConj : ℂ) = -1 := by
      rw [← Complex.ofReal_mul, goldenRatio_mul_goldenConj]; norm_num
    have hfac : (z - (goldenRatio : ℂ)) * (z - (goldenConj : ℂ)) = 0 := by
      linear_combination hquad - z * hsum + hprod
    have hzψ : z = (goldenConj : ℂ) := by
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd (sub_eq_zero.mp h) hzφ
      · exact sub_eq_zero.mp h
    rw [hzψ, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    exact ⟨neg_one_lt_goldenConj, by linarith [goldenConj_neg]⟩
