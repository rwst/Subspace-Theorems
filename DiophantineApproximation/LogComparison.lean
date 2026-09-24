/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A logarithm against a linear function

Both Roth's theorem and the penultimate-minimum theorem end with a degree parameter `D` sent to
infinity, and in both the inequality that has to fail for large `D` is of the shape

```text
B * log (D + 2) + E < c * D,      B ≥ 0,  c > 0.
```

This one-line fact is what replaces the book's `D → ∞`: no limit is taken anywhere, and the
proof produces one explicit `D` above any prescribed threshold.

## Main results

* `Real.exists_le_and_mul_log_add_lt`: **a logarithm is eventually beaten by any positive
  multiple of the identity**, at an explicit point above a prescribed threshold.

## Implementation notes

⚠ **The statement is an existence above a threshold, not a limit.** Every caller needs `D` large
enough for several unrelated reasons at once — feasibility of Siegel's lemma, a ratio of
multidegrees, a lower bound on a height — and `D₁` collects them; the conclusion is what closes
the argument.

This is part of Layers 3.2 and 5.6 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

/-- **A logarithm is eventually beaten by any positive multiple of the identity.** -/
theorem Real.exists_le_and_mul_log_add_lt {B E c D₁ : ℝ} (hB : 0 ≤ B) (hc : 0 < c) :
    ∃ D : ℝ, D₁ ≤ D ∧ 0 < D ∧ B * Real.log (D + 2) + E < c * D := by
  set t : ℝ := 4 * B / c + 1 with htdef
  have ht0 : (0 : ℝ) < t := by positivity
  have hBt : B / t ≤ c / 4 := by
    rw [div_le_div_iff₀ ht0 (by norm_num), htdef]
    field_simp
    nlinarith
  set D : ℝ := max (max D₁ 1) ((c / 2 + B * Real.log t + E + 1) * 4 / (3 * c)) with hDdef
  have hD1 : D₁ ≤ D := le_trans (le_max_left _ _) (le_max_left _ _)
  have hD0 : (1 : ℝ) ≤ D := le_trans (le_max_right _ _) (le_max_left _ _)
  have hDbig : (c / 2 + B * Real.log t + E + 1) * 4 / (3 * c) ≤ D := le_max_right _ _
  refine ⟨D, hD1, by linarith, ?_⟩
  have hlog : Real.log (D + 2) ≤ (D + 2) / t + Real.log t - 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (D + 2) / t) (by positivity)
    rw [Real.log_div (by linarith) ht0.ne'] at h
    linarith
  have hstep : B * Real.log (D + 2) ≤ (c / 4) * (D + 2) + B * Real.log t := by
    calc B * Real.log (D + 2) ≤ B * ((D + 2) / t + Real.log t - 1) := by
          exact mul_le_mul_of_nonneg_left hlog hB
      _ = (B / t) * (D + 2) + B * Real.log t - B := by field_simp
      _ ≤ (c / 4) * (D + 2) + B * Real.log t - B := by
          have : (B / t) * (D + 2) ≤ (c / 4) * (D + 2) :=
            mul_le_mul_of_nonneg_right hBt (by linarith)
          linarith
      _ ≤ (c / 4) * (D + 2) + B * Real.log t := by linarith
  have hfin : (c / 2 + B * Real.log t + E + 1) ≤ (3 * c / 4) * D := by
    rw [div_le_iff₀ (by positivity)] at hDbig
    nlinarith
  nlinarith

end
