/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.IndexConditions
public import DiophantineApproximation.MvPolynomialEvalBound
public import Mathlib.Analysis.Normed.Ring.WithAbs

/-!
# The local bound at a place of `S`, in the base field

`DiophantineApproximation/MvPolynomialEvalBound.lean` bounds `|Q(β)|_W` for a polynomial and a
point over one field. Roth's theorem has the coefficients of `Q` and the point `β` in `K` and the
target `α` in a finite extension `F`, measured by an absolute value `W` of `F` lying over `v`.
This file is the one-step translation: since `W` restricted to `K` is `v`, the value, the local
factor of the coefficients and the local factors of the coordinates are all computed by `v`, and
the only thing that stays in `F` is the distance `|β j − α|_W` to the target.

The statement is arranged in exactly the shape
`DiophantineApproximation/GlobalBound.lean` consumes: a constant, the local factor of the
coefficient vector, the local factors of the `β j`, and one factor that the approximation class
will make small.

## Main results

* `MvPolynomial.exists_apply_eval_le_of_liesOver`: the local bound at a place carrying a target,
  for a polynomial over the base field.

## Implementation notes

⚠ **`AbsoluteValue.LiesOver` is used through `under_eq` and nothing else.** No place of `F` is
named, no ramification index appears, and the extension is not assumed separable or Galois: the
inequality compares one chosen absolute value above `v` with `v` itself, which is Layer 0.1's
minimal interface.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§6.4.8.

This is part of Layer 3.2 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

namespace MvPolynomial

variable {σ : Type*} [Fintype σ] {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- **The local bound at a place carrying a target**, for a polynomial over the base field: the
trivial bound times a factor that the approximation class will make small. -/
theorem exists_apply_eval_le_of_liesOver {v : AbsoluteValue K ℝ} {W : AbsoluteValue F ℝ}
    (hW : W.LiesOver v) {d : σ → ℕ} {Q : MvPolynomial σ K} (hQ : ∀ j, Q.degreeOf j ≤ d j)
    (α : F) {β : σ → K} (hβ : eval β Q ≠ 0) :
    ∃ ν : σ →₀ ℕ, (∀ j, ν j ≤ d j) ∧
      eval (fun _ ↦ α) (hasseDeriv ν (Q.map (algebraMap K F))) ≠ 0 ∧
      v (eval β Q) ≤ (∏ j, ((d j : ℝ) + 1)) * (⨆ μ, v (Q.coeff μ))
          * (∏ j, max (v (β j)) 1 ^ d j)
        * ((∏ j, ((d j : ℝ) + 1)) * 4 ^ (∑ j, d j) * max (W α) 1 ^ (2 * ∑ j, d j)
          * ∏ j, min 1 (W (algebraMap K F (β j) - α)) ^ ν j) := by
  have hWv : ∀ z : K, W (algebraMap K F z) = v z := fun z ↦ by
    rw [show W (algebraMap K F z) = (W.under K) z from rfl, AbsoluteValue.LiesOver.under_eq W v]
  have hQFdeg : ∀ j, (Q.map (algebraMap K F)).degreeOf j ≤ d j := fun j ↦
    le_trans (degreeOf_map_le _ Q j) (hQ j)
  have hkey : ∀ P : MvPolynomial σ K,
      eval₂ (algebraMap K F) (fun j ↦ algebraMap K F (β j)) P = algebraMap K F (eval β P) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp => simp [hp]
  have hevalb : eval (fun j ↦ algebraMap K F (β j)) (Q.map (algebraMap K F))
      = algebraMap K F (eval β Q) := by
    rw [eval_map]
    exact hkey Q
  have hbne : eval (fun j ↦ algebraMap K F (β j)) (Q.map (algebraMap K F)) ≠ 0 := by
    rw [hevalb]
    exact fun h ↦ hβ ((map_eq_zero_iff _ (algebraMap K F).injective).mp h)
  obtain ⟨ν, hν, hνne, hbound⟩ :=
    exists_apply_eval_le_of_sub W hQFdeg (fun _ ↦ α) (fun j ↦ algebraMap K F (β j)) hbne
  refine ⟨ν, hν, hνne, ?_⟩
  have hcoeff : (⨆ μ, W ((Q.map (algebraMap K F)).coeff μ)) = ⨆ μ, v (Q.coeff μ) := by
    refine iSup_congr fun μ ↦ ?_
    rw [coeff_map, hWv]
  have hb : ∀ j, max (W (algebraMap K F (β j))) 1 = max (v (β j)) 1 := fun j ↦ by rw [hWv]
  have halpha : (∏ _j : σ, max (W α) 1 ^ d _j) = max (W α) 1 ^ (∑ j, d j) :=
    Finset.prod_pow_eq_pow_sum _ _ _
  rw [hevalb, hWv] at hbound
  rw [hcoeff] at hbound
  simp only [hb] at hbound
  rw [halpha, ← pow_mul, Nat.mul_comm] at hbound
  refine le_trans hbound (le_of_eq ?_)
  ring

end MvPolynomial

end
