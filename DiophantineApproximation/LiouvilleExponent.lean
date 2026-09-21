/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.IrrationalityExponent
public import Mathlib.FieldTheory.Minpoly.Field

-- Used only inside proofs.
import DiophantineApproximation.LiouvilleInequality

/-!
# Liouville's theorem as a statement about the irrationality exponent

Liouville's inequality over a number field (Layer 0.4) says that a real algebraic number `ξ` of
degree `d` keeps every rational `a / q` at distance at least `1 / (A q ^ d)`, for a constant `A`
that `DiophantineApproximation/LiouvilleInequality.lean` exhibits. Read through the definition of
`Real.irrationalityExponent`, that is the bound

```text
irrationalityExponent ξ ≤ d.
```

Together with Dirichlet's lower bound `2 ≤ irrationalityExponent ξ` it pins the exponent of a
quadratic irrational at exactly `2`, and it re-proves Mathlib's `Liouville.transcendental`: a
Liouville number has exponent `⊤`, and no algebraic number does.

## Main results

* `Real.irrationalityExponent_le_natDegree`: Liouville's theorem, as a statement about the
  exponent.
* `Real.irrationalityExponent_eq_two_of_natDegree_eq_two`: the exponent of a real quadratic
  irrational is exactly `2`.

## Implementation notes

⚠ **The hypothesis `Irrational ξ` is not needed.** The roadmap's suggested signature carries it,
and Liouville's argument does need it — it compares `ξ` with a rational it must know to be
different — but the *statement* holds without it: a rational `ξ` has exponent `1` and minimal
polynomial of degree `1`, so the bound is an equality there. The proof splits on
`Irrational ξ` and the rational branch is `minpoly.natDegree_pos`.

⚠ **All the arithmetic is Layer 0.4's; Layer 1 supplies only the limit.** The passage from "no
rational is closer than `A⁻¹ q ^ (-d)`" to "the exponent is at most `d`" is the incompatibility of
a `Filter.Frequently` with a `Filter.Eventually`: for `p > d` the quantity `q ^ (p - d)` tends to
infinity, so it eventually exceeds `C * A`, while `LiouvilleWith p ξ` asks for approximations of
quality `C / q ^ p` infinitely often. One `Filter.Frequently.exists` closes it.

⚠ **`DiophantineApproximation/LiouvilleInequality.lean` grew a named theorem for this.** Layer
0.4 delivered its real-number consequence only as the acceptance-test `example` that derives
`Liouville.exists_pos_real_of_irrational_root`. Layer 1.1 needs the same statement with the
*minimal polynomial's* degree in place of an arbitrary annihilating polynomial's, so
`Real.exists_pos_one_le_pow_natDegree_mul_abs_sub_div` was added there and 0.4's acceptance test
now derives from it — the `ℚ⟮ξ⟯ ⊆ ℝ` scaffolding is built once.

⚠ **The bound is `d`, not `d - 1`.** Liouville's inequality is `|ξ - a / q| > c q ^ (-d)`, so the
exponent bound it produces is `d`; the rejection test at the end of this file shows that `d - 1`
is false already at `d = 2`. Replacing `d` by `2` is Roth's theorem, Layer 3, and is a different
statement — not a sharpening of the constant but of the exponent.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 1.5.21; Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press
(2004), Theorem 1.1.

This is the second half of Layer 1.1 of the `DiophantineApproximation` roadmap.
-/

public section

open Filter
open scoped ENNReal NNReal

namespace Real

/-- **Liouville's theorem.** The irrationality exponent of a real algebraic number is at most its
degree over `ℚ`. -/
theorem irrationalityExponent_le_natDegree {ξ : ℝ} (halg : IsAlgebraic ℚ ξ) :
    irrationalityExponent ξ ≤ ((minpoly ℚ ξ).natDegree : ℝ≥0∞) := by
  rcases em (Irrational ξ) with hirr | hirr
  · obtain ⟨A, hA0, hA⟩ := Real.exists_pos_one_le_pow_natDegree_mul_abs_sub_div hirr halg
    set d := (minpoly ℚ ξ).natDegree with hd
    rw [irrationalityExponent_le_iff]
    intro p hp
    by_contra hcon
    have hdp : (d : ℝ) < (p : ℝ) := by exact_mod_cast lt_of_not_ge hcon
    obtain ⟨C, hC0, hC⟩ := hp.exists_pos
    have htend : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ ((p : ℝ) - d)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    obtain ⟨n, hCA, hn1, m, hne, hlt⟩ :=
      ((htend.eventually_gt_atTop (C * A)).and_frequently hC).exists
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hn0 : (0 : ℝ) < n := by linarith
    have hb : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      rw [Nat.cast_sub hn1]
      ring
    have hkey := hA m (n - 1)
    rw [hb] at hkey
    have hnd0 : (0 : ℝ) < (n : ℝ) ^ d := by positivity
    have hnpd0 : (0 : ℝ) < (n : ℝ) ^ ((p : ℝ) - d) := Real.rpow_pos_of_pos hn0 _
    have hsplit : (n : ℝ) ^ d * ((C / (n : ℝ) ^ (p : ℝ)) * A)
        = C * A / (n : ℝ) ^ ((p : ℝ) - d) := by
      rw [Real.rpow_sub hn0, ← Real.rpow_natCast (n : ℝ) d]
      field_simp
    have h1 : (1 : ℝ) < (n : ℝ) ^ d * ((C / (n : ℝ) ^ (p : ℝ)) * A) := by
      refine lt_of_le_of_lt hkey ?_
      gcongr
    rw [hsplit, lt_div_iff₀ hnpd0, one_mul] at h1
    linarith
  · rw [irrationalityExponent_eq_one_of_not_irrational hirr]
    have h1 : 1 ≤ (minpoly ℚ ξ).natDegree := minpoly.natDegree_pos halg.isIntegral
    exact_mod_cast h1

/-- A real quadratic irrational has irrationality exponent exactly `2`: Dirichlet's bound is
attained. -/
theorem irrationalityExponent_eq_two_of_natDegree_eq_two {ξ : ℝ} (halg : IsAlgebraic ℚ ξ)
    (hirr : Irrational ξ) (h2 : (minpoly ℚ ξ).natDegree = 2) : irrationalityExponent ξ = 2 := by
  refine le_antisymm ?_ (two_le_irrationalityExponent hirr)
  have h := irrationalityExponent_le_natDegree halg
  rw [h2] at h
  exact_mod_cast h

/-! ### Acceptance criteria -/

/-- **Acceptance test: Mathlib's `Liouville.transcendental` follows.** A Liouville number has
exponent `⊤`, which no algebraic number has. -/
example {ξ : ℝ} (h : Liouville ξ) : Transcendental ℚ ξ := by
  intro halg
  have h1 := irrationalityExponent_le_natDegree halg
  rw [irrationalityExponent_eq_top_iff.2 h] at h1
  exact ENNReal.natCast_ne_top _ (top_le_iff.1 h1)

open _root_.Polynomial in
/-- **Acceptance test: `irrationalityExponent (√2) = 2`**, a value, not a bound: Dirichlet gives
`2 ≤`, Liouville gives `≤ 2` because the degree is `2`. -/
example : irrationalityExponent (√2) = 2 := by
  have hp : (X ^ 2 - C 2 : ℚ[X]) ≠ 0 := X_pow_sub_C_ne_zero (by norm_num) 2
  have hsq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have haeval : aeval (√2 : ℝ) (X ^ 2 - C 2 : ℚ[X]) = 0 := by simp [hsq]
  have halg : IsAlgebraic ℚ (√2 : ℝ) := ⟨X ^ 2 - C 2, hp, haeval⟩
  refine irrationalityExponent_eq_two_of_natDegree_eq_two halg irrational_sqrt_two ?_
  have hle : (minpoly ℚ (√2 : ℝ)).natDegree ≤ 2 := by
    have h := Polynomial.natDegree_le_natDegree
      (minpoly.degree_le_of_ne_zero ℚ (√2 : ℝ) hp haeval)
    rwa [natDegree_X_pow_sub_C] at h
  have hge : 2 ≤ (minpoly ℚ (√2 : ℝ)).natDegree := by
    rw [minpoly.two_le_natDegree_iff halg.isIntegral]
    rintro ⟨q, hq⟩
    exact irrational_sqrt_two ⟨q, by rw [← hq]; exact eq_ratCast (algebraMap ℚ ℝ) q⟩
  omega

open _root_.Polynomial in
/-- **Rejection test: the degree cannot be replaced by the degree minus one at this layer.**
Liouville's inequality gives the exponent bound `d`, and `d - 1` is false at `d = 2`: a quadratic
irrational has exponent `2`, not `1`. (Roth's theorem — Layer 3 — does replace `d` by `2`, which
is a different statement.) -/
example : ¬ ∀ ξ : ℝ, IsAlgebraic ℚ ξ → Irrational ξ →
    irrationalityExponent ξ ≤ (((minpoly ℚ ξ).natDegree - 1 : ℕ) : ℝ≥0∞) := by
  intro h
  have hp : (X ^ 2 - C 2 : ℚ[X]) ≠ 0 := X_pow_sub_C_ne_zero (by norm_num) 2
  have hsq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have haeval : aeval (√2 : ℝ) (X ^ 2 - C 2 : ℚ[X]) = 0 := by simp [hsq]
  have halg : IsAlgebraic ℚ (√2 : ℝ) := ⟨X ^ 2 - C 2, hp, haeval⟩
  have hle : (minpoly ℚ (√2 : ℝ)).natDegree ≤ 2 := by
    have h' := Polynomial.natDegree_le_natDegree
      (minpoly.degree_le_of_ne_zero ℚ (√2 : ℝ) hp haeval)
    rwa [natDegree_X_pow_sub_C] at h'
  have hge : 2 ≤ (minpoly ℚ (√2 : ℝ)).natDegree := by
    rw [minpoly.two_le_natDegree_iff halg.isIntegral]
    rintro ⟨q, hq⟩
    exact irrational_sqrt_two ⟨q, by rw [← hq]; exact eq_ratCast (algebraMap ℚ ℝ) q⟩
  have h2 : (minpoly ℚ (√2 : ℝ)).natDegree = 2 := le_antisymm hle hge
  have hbad := h (√2) halg irrational_sqrt_two
  rw [h2] at hbad
  have hcon : (2 : ℝ≥0∞) ≤ ((2 - 1 : ℕ) : ℝ≥0∞) :=
    le_trans (two_le_irrationalityExponent irrational_sqrt_two) hbad
  norm_num at hcon

end Real
