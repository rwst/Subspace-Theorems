/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.NumberTheory.Height.Basic
public import STForMathlib.RingTheory.MvPolynomial.Veronese

-- Used only inside proofs.
import Mathlib.Data.Fintype.Order

/-!
# The height of the Veronese image

At every absolute value `v`, the largest monomial of degree `t` in `x` is the `t`-th power of
the largest coordinate: `⨆_μ v(x^μ) = (⨆_j v(x_j))^t`. Every `x^μ` is a product of `t`
coordinates, and the pure power of a largest coordinate attains the bound. So the Veronese map
of degree `t` raises the multiplicative height to the `t`-th power exactly.

## Main results

* `AbsoluteValue.iSup_veronese`: the local identity.
* `Height.mulHeight_veronese`: `H(x^{(t)}) = H(x)^t`.
-/

@[expose] public section

open Finset MvPolynomial

variable {K ι : Type*} [Field K] [Fintype ι]

/-- **The local identity** `⨆_μ v(x^μ) = (⨆_j v(x_j))^t` over the monomials of degree `t`. -/
theorem AbsoluteValue.iSup_veronese [Nonempty ι] (v : AbsoluteValue K ℝ) (t : ℕ) (x : ι → K) :
    ⨆ μ, v (veronese t x μ) = (⨆ j, v (x j)) ^ t := by
  obtain ⟨j₀, hj₀⟩ := exists_eq_ciSup_of_finite (f := fun j ↦ v (x j))
  have : Nonempty (degreeMonomials ι t) := ⟨⟨_, single_mem_degreeMonomials j₀ t⟩⟩
  refine le_antisymm (ciSup_le fun μ ↦ ?_) ?_
  · rw [veronese_apply, Finsupp.prod, map_prod]
    simp only [map_pow]
    have hdeg : ∑ j ∈ μ.1.support, μ.1 j = t := mem_degreeMonomials.1 μ.2
    rw [show (⨆ j, v (x j)) ^ t = ∏ j ∈ μ.1.support, (⨆ j, v (x j)) ^ μ.1 j by
      rw [Finset.prod_pow_eq_pow_sum, hdeg]]
    exact Finset.prod_le_prod₀ (fun j _ ↦ pow_nonneg (v.nonneg _) _) fun j _ ↦
      pow_le_pow_left₀ (v.nonneg _) (le_ciSup (f := fun j ↦ v (x j)) (Finite.bddAbove_range _) j) _
  · rw [← hj₀, ← map_pow, ← veronese_single t x j₀]
    exact le_ciSup (f := fun μ ↦ v (veronese t x μ)) (Finite.bddAbove_range _) _

namespace Height

variable [AdmissibleAbsValues K]

open AdmissibleAbsValues in
/-- **The Veronese map raises the height to the `t`-th power**: `H(x^{(t)}) = H(x)^t`. It has
the local factors of the coordinate-wise power `x^t`, whose height is Mathlib's
`Height.mulHeight_pow`. -/
theorem mulHeight_veronese (t : ℕ) {x : ι → K} (hx : x ≠ 0) :
    mulHeight (veronese t x) = mulHeight x ^ t := by
  have : Nonempty ι := (Function.ne_iff.mp hx).nonempty
  have hy := veronese_ne_zero t hx
  have hxt : x ^ t ≠ 0 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
    exact Function.ne_iff.2 ⟨j, by simpa using pow_ne_zero t hj⟩
  have H (v : AbsoluteValue K ℝ) : ⨆ i : ι, v ((x ^ t) i) = (⨆ i, v (x i)) ^ t := by
    obtain ⟨j₀, hj₀⟩ := exists_eq_ciSup_of_finite (f := fun j ↦ v (x j))
    refine le_antisymm ?_ ?_
    · refine ciSup_le fun i ↦ ?_
      rw [Pi.pow_apply, map_pow]
      exact pow_le_pow_left₀ (v.nonneg _)
        (le_ciSup (f := fun j ↦ v (x j)) (Finite.bddAbove_range _) i) _
    · rw [← hj₀, ← map_pow, ← Pi.pow_apply]
      exact le_ciSup (f := fun i ↦ v ((x ^ t) i)) (Finite.bddAbove_range _) j₀
  rw [← mulHeight_pow, mulHeight_eq hy, mulHeight_eq hxt]
  simp only [AbsoluteValue.iSup_veronese, H]

end Height
