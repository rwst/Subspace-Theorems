/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Challenge.ArithmeticHeights.BombieriVaalerRelative
public import Challenge.ArithmeticHeights.MonomialIndex

public section
open Finsupp Matrix Module MvPolynomial NumberField Real
namespace MvPolynomial
section Absolute
variable {K : Type*} [Field K] [NumberField K] {σ : Type*} [Finite σ] {N D : ℕ}
theorem exists_ne_zero_mem_ker_mulHeight_rpow_le
    (A : Matrix (Fin N) {m : σ →₀ ℕ // m.degree ≤ D} K)
    (hA : A.rank < Fintype.card {m : σ →₀ ℕ // m.degree ≤ D}) :
    ∃ P : MvPolynomial σ K, P ≠ 0 ∧ P.totalDegree ≤ D ∧
      (∀ m, IsIntegral ℤ (P.coeff m)) ∧
      A.mulVec (fun m ↦ P.coeff (m : σ →₀ ℕ)) = 0 ∧
      P.mulHeight ^ ((finrank ℚ K : ℝ))⁻¹ ≤
        |(NumberField.discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ *
          (Real.sqrt (Fintype.card {m : σ →₀ ℕ // m.degree ≤ D}) *
              A.mulHeight ^ ((finrank ℚ K : ℝ))⁻¹) ^
            ((A.rank : ℝ) / (Fintype.card {m : σ →₀ ℕ // m.degree ≤ D} - A.rank)) := by
  sorry
end Absolute
end MvPolynomial
end
