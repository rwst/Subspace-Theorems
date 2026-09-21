/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.PolynomialSupNorm
public import Mathlib.Algebra.Polynomial.Derivative

-- Used only inside proofs and in the acceptance criteria.
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.ComputeDegree

/-!
# Archimedean bounds on an integer polynomial

`DiophantineApproximation/PolynomialSupNorm.lean` proved everything Layer 1.2 needed about the
naive height `Polynomial.supNorm`, and never had to evaluate a polynomial anywhere: the value
`aeval ξ P` entered its statements only through the hypothesis that it is small. Layer 1.3 has to
*produce* small values, and for that the trivial upper bound on an evaluation and its mean value
form are the two steps every argument begins with:

```text
|P x|  ≤ (n + 1) * H(P) * max 1 |x| ^ n,
|P y - P x| ≤ (n + 1) ^ 2 * H(P) * max 1 (max |x| |y|) ^ n * |y - x|.
```

Both are stated with `n` a bound on the degree rather than the degree itself, because that is how
every consumer has them — the degree of a solution varies inside a set of solutions, the bound
does not — and both carry the factor `max 1 |x| ^ n`, without which they are false.

## Main results

* `Polynomial.abs_aeval_le`: the triangle inequality for an evaluation.
* `Polynomial.supNorm_derivative_le`: differentiating multiplies the naive height by at most
  `n + 1`.
* `Polynomial.abs_aeval_derivative_le`: the two combined, the bound Layer 1.3 uses on `P'`.
* `Polynomial.abs_aeval_sub_aeval_le`: **the mean value theorem for an integer polynomial**, with
  a constant that depends only on the degree bound, the naive height and the interval.

## Implementation notes

⚠ **The derivative is bounded by `n + 1`, not by `n`.** The sharp factor is `n`, from
`(derivative P).coeff i = (i + 1) * P.coeff (i + 1)` with `i + 1 ≤ n`; the sharp form is useless
here because it degenerates at `n = 0`, where every constant a consumer builds out of it — and
every consumer builds one — would be zero. `n + 1` keeps the constants positive at every degree
bound, which is what `Real.le_mahlerExponent_of_infinite` asks for.

⚠ **The mean value theorem is `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` on
`Set.uIcc`.** Nothing is assumed about the order of `x` and `y`, so the interval has to be the
unordered one; `Set.uIcc` is convex and contains both endpoints, and those three facts are the
whole interface. The alternative — the algebraic identity `x ^ k - y ^ k = (x - y) * ∑ …` summed
against the coefficients — proves the same bound with no analysis at all, and is longer.

⚠ **`aeval` over `ℤ` and `eval` over `ℝ` have to be reconciled once.** Mathlib's derivative API is
about `eval` on `ℝ[X]`, the naive height is about `ℤ[X]`, and `Polynomial.derivative_map` is what
lets the two be used in the same calculation; the map is applied to `P`, never to the height.

## References

Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), Appendix A.

This is part of Layer 1.3 of the `DiophantineApproximation` roadmap.
-/

public section

namespace Polynomial

variable {P : ℤ[X]} {n : ℕ}

/-! ### The value and the derivative at a real point -/

/-- **The triangle inequality for an evaluation.** An integer polynomial of degree at most `n`
takes at `x` a value of absolute value at most `(n + 1) * H(P) * max 1 |x| ^ n`. -/
theorem abs_aeval_le (hP : P.natDegree ≤ n) (x : ℝ) :
    |aeval x P| ≤ ((n : ℝ) + 1) * (P.supNorm * max 1 |x| ^ n) := by
  have hM1 : (1 : ℝ) ≤ max 1 |x| := le_max_left _ _
  have hlt : P.natDegree < n + 1 := by omega
  rw [aeval_eq_sum_range' hlt]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hbound : ∀ i ∈ Finset.range (n + 1),
      |(P.coeff i) • (x : ℝ) ^ i| ≤ P.supNorm * max 1 |x| ^ n := by
    intro i hi
    rw [zsmul_eq_mul, abs_mul, abs_pow]
    have h1 : |((P.coeff i : ℤ) : ℝ)| ≤ P.supNorm := P.abs_coeff_le_supNorm i
    have h2 : |x| ^ i ≤ max 1 |x| ^ n :=
      (pow_le_pow_left₀ (abs_nonneg x) (le_max_right 1 |x|) i).trans
        (pow_le_pow_right₀ hM1 (Finset.mem_range_succ_iff.1 hi))
    exact mul_le_mul h1 h2 (by positivity) P.supNorm_nonneg
  calc ∑ i ∈ Finset.range (n + 1), |(P.coeff i) • (x : ℝ) ^ i|
      ≤ ∑ _i ∈ Finset.range (n + 1), P.supNorm * max 1 |x| ^ n := Finset.sum_le_sum hbound
    _ = ((n : ℝ) + 1) * (P.supNorm * max 1 |x| ^ n) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- **Differentiating multiplies the naive height by at most `n + 1`.** -/
theorem supNorm_derivative_le (hP : P.natDegree ≤ n) :
    (derivative P).supNorm ≤ ((n : ℝ) + 1) * P.supNorm := by
  refine supNorm_le_of_forall fun i ↦ ?_
  have hi0 : (0 : ℝ) ≤ (i : ℝ) + 1 := by positivity
  rw [Int.norm_eq_abs, coeff_derivative]
  push_cast
  rw [abs_mul, abs_of_nonneg hi0]
  rcases le_or_gt (i + 1) n with h | h
  · have h1 : |((P.coeff (i + 1) : ℤ) : ℝ)| ≤ P.supNorm := P.abs_coeff_le_supNorm _
    have h2 : (i : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_of_succ_le h
      linarith
    calc |((P.coeff (i + 1) : ℤ) : ℝ)| * ((i : ℝ) + 1)
        ≤ P.supNorm * ((n : ℝ) + 1) := by
          exact mul_le_mul h1 h2 hi0 P.supNorm_nonneg
      _ = ((n : ℝ) + 1) * P.supNorm := by ring
  · have hz : P.coeff (i + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz]
    simpa using mul_nonneg (by positivity) P.supNorm_nonneg

/-- **The bound on the derivative at a real point**, the one Layer 1.3 consumes. -/
theorem abs_aeval_derivative_le (hP : P.natDegree ≤ n) (x : ℝ) :
    |aeval x (derivative P)| ≤ ((n : ℝ) + 1) ^ 2 * (P.supNorm * max 1 |x| ^ n) := by
  have hM1 : (1 : ℝ) ≤ max 1 |x| := le_max_left _ _
  have hd : (derivative P).natDegree ≤ n := (natDegree_derivative_le P).trans (by omega)
  calc |aeval x (derivative P)|
      ≤ ((n : ℝ) + 1) * ((derivative P).supNorm * max 1 |x| ^ n) := abs_aeval_le hd x
    _ ≤ ((n : ℝ) + 1) * ((((n : ℝ) + 1) * P.supNorm) * max 1 |x| ^ n) := by
        have := supNorm_derivative_le hP
        have hpow : (0 : ℝ) ≤ max 1 |x| ^ n := by positivity
        have : (derivative P).supNorm * max 1 |x| ^ n
            ≤ (((n : ℝ) + 1) * P.supNorm) * max 1 |x| ^ n := by gcongr
        exact mul_le_mul_of_nonneg_left this (by positivity)
    _ = ((n : ℝ) + 1) ^ 2 * (P.supNorm * max 1 |x| ^ n) := by ring

/-! ### The mean value theorem -/

/-- A point of the unordered interval is no larger in absolute value than its endpoints. -/
private theorem abs_le_max_abs_of_mem_uIcc {x y z : ℝ} (hz : z ∈ Set.uIcc x y) :
    |z| ≤ max |x| |y| := by
  have h1 : |x| ≤ max |x| |y| := le_max_left _ _
  have h2 : |y| ≤ max |x| |y| := le_max_right _ _
  have hx1 : x ≤ |x| := le_abs_self x
  have hx2 : -|x| ≤ x := neg_abs_le x
  have hy1 : y ≤ |y| := le_abs_self y
  have hy2 : -|y| ≤ y := neg_abs_le y
  rcases Set.mem_uIcc.1 hz with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [abs_le] <;> constructor <;> linarith

/-- **The mean value theorem for an integer polynomial.** The increment of `P` between two real
points is at most `(n + 1) ^ 2 * H(P) * max 1 (max |x| |y|) ^ n` times their distance. This is
the step that turns "`α` is a root of `P` near `ξ`" into "`P` is small at `ξ`", which is the whole
of `Real.koksmaExponent_le_mahlerExponent`. -/
theorem abs_aeval_sub_aeval_le (hP : P.natDegree ≤ n) (x y : ℝ) :
    |aeval y P - aeval x P|
      ≤ ((n : ℝ) + 1) ^ 2 * (P.supNorm * max 1 (max |x| |y|) ^ n) * |y - x| := by
  set M : ℝ := max 1 (max |x| |y|) with hM
  set Q : ℝ[X] := P.map (Int.castRingHom ℝ) with hQdef
  have hev : ∀ z : ℝ, aeval z P = eval z Q := by
    intro z
    rw [hQdef, aeval_def, eval₂_eq_eval_map]
    rfl
  have hdev : ∀ z : ℝ, eval z (derivative Q) = aeval z (derivative P) := by
    intro z
    rw [hQdef, derivative_map, aeval_def, eval₂_eq_eval_map]
    rfl
  have hderiv : ∀ z ∈ Set.uIcc x y,
      HasDerivWithinAt (fun z ↦ eval z Q) (eval z (derivative Q)) (Set.uIcc x y) z :=
    fun z _ ↦ (Q.hasDerivAt z).hasDerivWithinAt
  have hbnd : ∀ z ∈ Set.uIcc x y,
      ‖eval z (derivative Q)‖ ≤ ((n : ℝ) + 1) ^ 2 * (P.supNorm * M ^ n) := by
    intro z hz
    rw [Real.norm_eq_abs, hdev z]
    refine (abs_aeval_derivative_le hP z).trans ?_
    have hle : max 1 |z| ≤ M := max_le_max le_rfl (abs_le_max_abs_of_mem_uIcc hz)
    have h1 : (0 : ℝ) ≤ max 1 |z| := le_trans zero_le_one (le_max_left _ _)
    gcongr
    exact P.supNorm_nonneg
  have hkey := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbnd
    (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, ← hev x, ← hev y] at hkey
  exact hkey

/-! ### Acceptance criteria -/

/-- **Acceptance test: the bound on the value.** At `x = 3` the polynomial `X ^ 2 - 2` has value
`7`, and the bound reads `3 * 1 * 3 ^ 2 = 27`. -/
example : |aeval (3 : ℝ) (X ^ 2 - C 2 : ℤ[X])| ≤ ((2 : ℝ) + 1) * ((X ^ 2 - C 2 : ℤ[X]).supNorm
    * max 1 |(3 : ℝ)| ^ 2) :=
  abs_aeval_le (by compute_degree) 3

/-- **Acceptance test: the mean value theorem.** -/
example (x y : ℝ) : |aeval y (X ^ 2 - C 2 : ℤ[X]) - aeval x (X ^ 2 - C 2 : ℤ[X])|
    ≤ ((2 : ℝ) + 1) ^ 2 * ((X ^ 2 - C 2 : ℤ[X]).supNorm * max 1 (max |x| |y|) ^ 2) * |y - x| :=
  abs_aeval_sub_aeval_le (by compute_degree) x y

/-- **Rejection test: the factor `max 1 |x| ^ n` cannot be dropped.** The bound
`|P x| ≤ (n + 1) * H(P)` fails already at `P = X ^ 2` and `x = 10`, where the value is `100` and
the right-hand side is `3`. -/
example : ¬ |aeval (10 : ℝ) (X ^ 2 : ℤ[X])| ≤ ((2 : ℝ) + 1) * (X ^ 2 : ℤ[X]).supNorm := by
  have hs : (X ^ 2 : ℤ[X]).supNorm = 1 := by
    rw [← monomial_one_right_eq_X_pow, supNorm_monomial]
    simp
  rw [hs]
  norm_num

/-- **Rejection test: the factor `n + 1` cannot be dropped either.** At `P = X + 1` and `x = 1`
the value is `2` while `H(P) * max 1 |x| ^ 1 = 1`. -/
example : ¬ |aeval (1 : ℝ) (C 1 * X + C 1 : ℤ[X])|
    ≤ (C 1 * X + C 1 : ℤ[X]).supNorm * max 1 |(1 : ℝ)| ^ 1 := by
  rw [supNorm_linear]
  norm_num

end Polynomial
