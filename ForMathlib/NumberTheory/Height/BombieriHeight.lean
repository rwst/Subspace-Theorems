/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.BlockMultinomial
public import Mathlib.NumberTheory.Height.Basic

/-!
# The polynomial height `h_m`

The height `h_m` of LNM 1752 (G. Rémond, *Géométrie diophantienne multiprojective*, Chapter 7 of
Nesterenko–Philippon (eds.), *Introduction to algebraic independence theory*), Ch. 7, §3.2: the
maximum of the coefficients at the finite places, and the norm
`(∑_m |p_m|_v² / C(δ, m))^{1/2}` at the infinite ones, with the multinomial coefficients
`C(δ, m) = ∏_i δ_i! / ∏_s m_s!` (`MvPolynomial.blockMultinomial`). Heights are relative to `K`,
in Mathlib's normalization (`Height.AdmissibleAbsValues`).

## Main definitions

* `MvPolynomial.bombieriNorm`, `MvPolynomial.bombieriLogHeight`: the polynomial height `h_m`.
-/

@[expose] public section

open Height Height.AdmissibleAbsValues

namespace MvPolynomial

variable {σ ι K : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] [Field K]

/-- The local norm `‖P‖_{v,2} = (∑_m |p_m|_v² / C(δ, m))^{1/2}` at an archimedean place (LNM 1752,
Ch. 7, §3.2). -/
noncomputable def bombieriNorm (b : σ → ι) (v : AbsoluteValue K ℝ) (P : MvPolynomial σ K) : ℝ :=
  √(∑ m ∈ P.support, v (P.coeff m) ^ 2 / blockMultinomial b m)

open Classical in
/-- **The polynomial height `h_m(P)`** of LNM 1752, Ch. 7, §3.2, relative to `K`: the logarithm of
`∏_{v | ∞} ‖P‖_{v,2} · ∏_{v ∤ ∞} max_m |p_m|_v`, and `0` for `P = 0`. -/
noncomputable def bombieriLogHeight [AdmissibleAbsValues K] (b : σ → ι) (P : MvPolynomial σ K) :
    ℝ :=
  if P = 0 then 0 else
    Real.log ((archAbsVal.map fun v ↦ bombieriNorm b v P).prod *
      ∏ᶠ v : nonarchAbsVal, ⨆ m : P.support, v.val (P.coeff m))

theorem bombieriNorm_pos (b : σ → ι) (v : AbsoluteValue K ℝ) {P : MvPolynomial σ K} (hP : P ≠ 0) :
    0 < bombieriNorm b v P :=
  Real.sqrt_pos.2 <| Finset.sum_pos (fun m hm ↦ div_pos (pow_pos (v.pos (mem_support_iff.1 hm)) _)
    (Nat.cast_pos.2 (blockMultinomial_pos b m))) (support_nonempty.2 hP)

@[simp]
theorem bombieriLogHeight_zero [AdmissibleAbsValues K] (b : σ → ι) :
    bombieriLogHeight b (0 : MvPolynomial σ K) = 0 := by
  simp [bombieriLogHeight]

theorem bombieriLogHeight_of_ne_zero [AdmissibleAbsValues K] (b : σ → ι) {P : MvPolynomial σ K}
    (hP : P ≠ 0) :
    bombieriLogHeight b P = Real.log ((archAbsVal.map fun v ↦ bombieriNorm b v P).prod *
      ∏ᶠ v : nonarchAbsVal, ⨆ m : P.support, v.val (P.coeff m)) := by
  simp [bombieriLogHeight, hP]

end MvPolynomial
