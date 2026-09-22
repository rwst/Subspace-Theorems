/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.RothInfinity

/-!
# The zero of a linear form, as a target on the projective line

**Layer 3.4, the local dictionary.** The Subspace Theorem in two variables and Roth's theorem
speak about the same thing in two languages. The Subspace Theorem measures a point
`x = (x 0, x 1)` of `K²` by the values `|L v i x| v` of two linear forms at each place `v`; Roth's
theorem measures the single number `β = x 1 / x 0` by its distance to a target. The dictionary is
that the linear form `a X₀ + b X₁` vanishes at one point of the projective line — at `-a / b`, or
at `∞` when `b = 0` — and that, after dividing by the local sup norm of `x`, its value is that
distance up to a constant:

```text
|a x₀ + b x₁| v / ‖x‖ v  ≍  Λ v β      with      Λ = onePointApprox (formRoot a b).
```

This file proves the one inequality of that comparison which Layer 3.4 consumes, together with
the two elementary bounds that turn a pair of linearly independent forms into a pair of numbers
bounded above and below.

## Main results

* `OnePoint.formRoot`: the zero of `a X₀ + b X₁` in `OnePoint F`.
* `AbsoluteValue.onePointApprox_formRoot_le`: the local factor at that zero is at most a constant
  times the normalized value of the form.
* `AbsoluteValue.min_one_sub_mul_max_one_le`: the elementary inequality behind it.
* `AbsoluteValue.apply_add_mul_le`: the normalized value of a form is bounded above by the sum of
  the absolute values of its coefficients.
* `AbsoluteValue.le_max_apply_add_mul`: two forms with nonzero determinant cannot both be small.

## Implementation notes

⚠ **The constant is not the naive one.** The comparison `|a + b β| / max 1 |β| ≍ min 1 |β - t|`
fails with any constant that does not see the target: at `β` far away both sides are of size `1`,
but the left one only after dividing by `max 1 |β|`, and the ratio of the two sides at
intermediate `β` is governed by `|t|`. The constant used, `(2 + 2 |t|) / |b|`, is the smallest
shape that survives both regimes, and the proof splits at `|β| = 2 + 2 |t|`.

⚠ **The lower bound is a determinant, not a norm.** Two linear forms are "independent enough" at
a place exactly when `a₀ b₁ - a₁ b₀ ≠ 0`; the bound
`|a₀ b₁ - a₁ b₀| max 1 |β| ≤ (|a₀| + |a₁| + |b₀| + |b₁|) max i |a i + b i β|` is Cramer's rule
read at one absolute value, and it is what prevents both normalized values from being small at
once. Linear independence of the *forms* is converted to `a₀ b₁ - a₁ b₀ ≠ 0` in
`DiophantineApproximation/ApproxProd.lean`, where the index type is available.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Example 7.2.7.

This is part of Layer 3.4 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open OnePoint

namespace OnePoint

variable {F : Type*} [Field F]

open scoped Classical in
/-- **The zero of the linear form `a X₀ + b X₁`**, read in the chart `[x₀ : x₁] ↦ x₁ / x₀` of the
projective line: the point `-(a / b)`, and the point at infinity when `b = 0`. -/
noncomputable def formRoot (a b : F) : OnePoint F :=
  if b = 0 then ∞ else ((-(a / b) : F) : OnePoint F)

theorem formRoot_of_eq_zero (a : F) : formRoot a (0 : F) = ∞ := by
  rw [formRoot, ite_eq_left rfl]

theorem formRoot_of_ne_zero (a : F) {b : F} (hb : b ≠ 0) :
    formRoot a b = ((-(a / b) : F) : OnePoint F) := by
  rw [formRoot, ite_eq_right hb]

end OnePoint

/-- If neither of two nonnegative reals is small — their maximum is at least `D⁻¹` — then their
minimum is at most `D` times their product. This is how a lower bound on one local value of a
pair of linear forms turns the product of the Subspace Theorem into the single factor of Roth's
theorem. -/
theorem min_le_mul_of_inv_le_max {u v D : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hD : 0 < D)
    (h : D⁻¹ ≤ max u v) : min u v ≤ D * (u * v) := by
  have hmm : min u v * max u v = u * v := by
    rcases le_total u v with huv | huv
    · rw [min_eq_left huv, max_eq_right huv]
    · rw [min_eq_right huv, max_eq_left huv, mul_comm]
  have hmin : (0 : ℝ) ≤ min u v := le_min hu hv
  have hstep : min u v * D⁻¹ ≤ min u v * max u v := mul_le_mul_of_nonneg_left h hmin
  rw [hmm] at hstep
  have hmul : min u v * D⁻¹ * D ≤ u * v * D := mul_le_mul_of_nonneg_right hstep hD.le
  calc min u v = min u v * D⁻¹ * D := by field_simp
    _ ≤ u * v * D := hmul
    _ = D * (u * v) := by ring

namespace AbsoluteValue

variable {F : Type*} [Field F] (W : AbsoluteValue F ℝ)

open scoped Classical in
/-- The constant of `AbsoluteValue.onePointApprox_formRoot_le`, attached to the linear form
`a X₀ + b X₁`. -/
noncomputable def formConst (a b : F) : ℝ :=
  if b = 0 then (W a)⁻¹ else (2 + 2 * W (a / b)) / W b

theorem formConst_of_eq_zero (a : F) : W.formConst a (0 : F) = (W a)⁻¹ := by
  rw [formConst, ite_eq_left rfl]

theorem formConst_of_ne_zero (a : F) {b : F} (hb : b ≠ 0) :
    W.formConst a b = (2 + 2 * W (a / b)) / W b := by
  rw [formConst, ite_eq_right hb]

/-- The constant is positive as soon as the form is not the zero form. -/
theorem formConst_pos {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) : 0 < W.formConst a b := by
  rcases eq_or_ne b 0 with rfl | hb
  · have ha : a ≠ 0 := hab.resolve_right fun h ↦ h rfl
    rw [W.formConst_of_eq_zero]
    exact inv_pos.mpr (W.pos ha)
  · rw [W.formConst_of_ne_zero a hb]
    have : (0 : ℝ) ≤ W (a / b) := W.nonneg _
    exact div_pos (by linarith) (W.pos hb)

/-- The constant is never negative, whatever the form. -/
theorem formConst_nonneg (a b : F) : 0 ≤ W.formConst a b := by
  rcases eq_or_ne b 0 with rfl | hb
  · rw [W.formConst_of_eq_zero]
    exact inv_nonneg.mpr (W.nonneg a)
  · rw [W.formConst_of_ne_zero a hb]
    exact div_nonneg (by linarith [W.nonneg (a / b)]) (W.nonneg b)

/-- **The elementary inequality behind the comparison.** Truncating at `1` costs a factor
`2 + 2 |t|`, and no less: the two sides change places at `|β| = 2 + 2 |t|`. -/
theorem min_one_sub_mul_max_one_le (t β : F) :
    min 1 (W (β - t)) * max 1 (W β) ≤ (2 + 2 * W t) * W (β - t) := by
  have hT : (0 : ℝ) ≤ W t := W.nonneg t
  have hX : (0 : ℝ) ≤ W (β - t) := W.nonneg _
  have hB : (0 : ℝ) ≤ W β := W.nonneg β
  have hlow : W β ≤ W (β - t) + W t := by
    calc W β = W (β - t + t) := by ring_nf
      _ ≤ W (β - t) + W t := W.add_le _ _
  rcases le_or_gt (W β) (2 + 2 * W t) with hcase | hcase
  · have h1 : max 1 (W β) ≤ 2 + 2 * W t := max_le (by linarith) hcase
    have h2 : min 1 (W (β - t)) ≤ W (β - t) := min_le_right _ _
    have h3 : (0 : ℝ) ≤ min 1 (W (β - t)) := le_min zero_le_one hX
    nlinarith
  · have hXbig : 1 < W (β - t) := by linarith
    rw [min_eq_left hXbig.le, one_mul, max_eq_right (by linarith)]
    nlinarith

/-- **The comparison.** The local approximation factor at the zero of the linear form
`a X₀ + b X₁` is at most a constant times the value of the form at `(1, β)`, normalized by the
local sup norm `max 1 |β|` of that point. -/
theorem onePointApprox_formRoot_le {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) (β : F) :
    W.onePointApprox (OnePoint.formRoot a b) β
      ≤ W.formConst a b * (W (a + b * β) / max 1 (W β)) := by
  have hA : (0 : ℝ) < max 1 (W β) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rcases eq_or_ne b 0 with rfl | hb
  · have ha : a ≠ 0 := hab.resolve_right fun h ↦ h rfl
    have ha0 : W a ≠ 0 := (W.pos ha).ne'
    rw [OnePoint.formRoot_of_eq_zero, W.formConst_of_eq_zero, onePointApprox_infty, zero_mul,
      add_zero, show (W a)⁻¹ * (W a / max 1 (W β)) = (max 1 (W β))⁻¹ by field_simp]
  · have hb0 : W b ≠ 0 := (W.pos hb).ne'
    rw [OnePoint.formRoot_of_ne_zero a hb, W.formConst_of_ne_zero a hb, onePointApprox_coe]
    have hfac : a + b * β = b * (β - -(a / b)) := by field_simp; ring
    rw [hfac, map_mul, show (2 + 2 * W (a / b)) / W b * (W b * W (β - -(a / b)) / max 1 (W β))
      = (2 + 2 * W (a / b)) * W (β - -(a / b)) / max 1 (W β) by field_simp, le_div_iff₀ hA]
    have key := W.min_one_sub_mul_max_one_le (-(a / b)) β
    rw [AbsoluteValue.map_neg] at key
    exact key

/-- The normalized value of a linear form at `(1, β)` is at most the sum of the absolute values
of its coefficients. This is the bound that keeps the *other* factor of the local product of the
Subspace Theorem from being large. -/
theorem apply_add_mul_div_le (a b β : F) : W (a + b * β) / max 1 (W β) ≤ W a + W b := by
  have hA : (0 : ℝ) < max 1 (W β) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have h1 : (1 : ℝ) ≤ max 1 (W β) := le_max_left _ _
  have h2 : W β ≤ max 1 (W β) := le_max_right _ _
  have ha : (0 : ℝ) ≤ W a := W.nonneg a
  have hb : (0 : ℝ) ≤ W b := W.nonneg b
  rw [div_le_iff₀ hA]
  calc W (a + b * β) ≤ W a + W (b * β) := W.add_le _ _
    _ = W a + W b * W β := by rw [map_mul]
    _ ≤ (W a + W b) * max 1 (W β) := by nlinarith

/-- **Cramer's rule at one absolute value.** Two linear forms whose determinant does not vanish
cannot both take a small value at `(1, β)`: the determinant, measured against the local sup norm
of `(1, β)`, is at most the size of the coefficients times the larger of the two values. -/
theorem le_max_apply_add_mul (a₀ b₀ a₁ b₁ β : F) :
    W (a₀ * b₁ - a₁ * b₀) * max 1 (W β)
      ≤ (W a₀ + W a₁ + W b₀ + W b₁) * max (W (a₀ + b₀ * β)) (W (a₁ + b₁ * β)) := by
  set u₀ : F := a₀ + b₀ * β with hu₀
  set u₁ : F := a₁ + b₁ * β with hu₁
  set M : ℝ := max (W u₀) (W u₁) with hM
  have hM₀ : W u₀ ≤ M := le_max_left _ _
  have hM₁ : W u₁ ≤ M := le_max_right _ _
  have hMnn : (0 : ℝ) ≤ M := le_trans (W.nonneg _) hM₀
  have ha₀ : (0 : ℝ) ≤ W a₀ := W.nonneg _
  have ha₁ : (0 : ℝ) ≤ W a₁ := W.nonneg _
  have hb₀ : (0 : ℝ) ≤ W b₀ := W.nonneg _
  have hb₁ : (0 : ℝ) ≤ W b₁ := W.nonneg _
  have hd : (0 : ℝ) ≤ W (a₀ * b₁ - a₁ * b₀) := W.nonneg _
  -- the two Cramer identities
  have e₀ : a₀ * b₁ - a₁ * b₀ = b₁ * u₀ - b₀ * u₁ := by rw [hu₀, hu₁]; ring
  have e₁ : (a₀ * b₁ - a₁ * b₀) * β = a₀ * u₁ - a₁ * u₀ := by rw [hu₀, hu₁]; ring
  have h₀ : W (a₀ * b₁ - a₁ * b₀) ≤ (W b₀ + W b₁) * M := by
    calc W (a₀ * b₁ - a₁ * b₀) = W (b₁ * u₀ - b₀ * u₁) := by rw [e₀]
      _ ≤ W (b₁ * u₀) + W (b₀ * u₁) := W.sub_le_add _ _
      _ = W b₁ * W u₀ + W b₀ * W u₁ := by rw [map_mul, map_mul]
      _ ≤ (W b₀ + W b₁) * M := by nlinarith
  have h₁ : W (a₀ * b₁ - a₁ * b₀) * W β ≤ (W a₀ + W a₁) * M := by
    calc W (a₀ * b₁ - a₁ * b₀) * W β = W ((a₀ * b₁ - a₁ * b₀) * β) := (map_mul _ _ _).symm
      _ = W (a₀ * u₁ - a₁ * u₀) := by rw [e₁]
      _ ≤ W (a₀ * u₁) + W (a₁ * u₀) := W.sub_le_add _ _
      _ = W a₀ * W u₁ + W a₁ * W u₀ := by rw [map_mul, map_mul]
      _ ≤ (W a₀ + W a₁) * M := by nlinarith
  rcases le_or_gt (W β) 1 with hβ | hβ
  · rw [max_eq_left hβ, mul_one]
    nlinarith
  · rw [max_eq_right hβ.le]
    nlinarith

/-- **The local comparison, for a pair of forms.** At one absolute value, the smaller of the two
local approximation factors at the zeros of two linear forms with nonvanishing determinant is at
most a constant — depending on the forms alone — times the *product* of the two normalized values.
This is the local statement Layer 3.4 needs: it converts the product of the Subspace Theorem into
the single factor of Roth's theorem, at the cost of not knowing which of the two targets is the
relevant one. -/
theorem onePointApprox_min_le {a₀ b₀ a₁ b₁ : F} (hd : a₀ * b₁ - a₁ * b₀ ≠ 0) (β : F) :
    min (W.onePointApprox (OnePoint.formRoot a₀ b₀) β)
        (W.onePointApprox (OnePoint.formRoot a₁ b₁) β)
      ≤ (W.formConst a₀ b₀ + W.formConst a₁ b₁)
          * ((W a₀ + W a₁ + W b₀ + W b₁) / W (a₀ * b₁ - a₁ * b₀))
          * (W (a₀ + b₀ * β) / max 1 (W β) * (W (a₁ + b₁ * β) / max 1 (W β))) := by
  have hA : (0 : ℝ) < max 1 (W β) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hab₀ : a₀ ≠ 0 ∨ b₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hd (by rw [hcon.1, hcon.2]; ring)
  have hab₁ : a₁ ≠ 0 ∨ b₁ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hd (by rw [hcon.1, hcon.2]; ring)
  set u₀ : ℝ := W (a₀ + b₀ * β) / max 1 (W β) with hu₀
  set u₁ : ℝ := W (a₁ + b₁ * β) / max 1 (W β) with hu₁
  have hu₀nn : (0 : ℝ) ≤ u₀ := div_nonneg (W.nonneg _) hA.le
  have hu₁nn : (0 : ℝ) ≤ u₁ := div_nonneg (W.nonneg _) hA.le
  set C₀ : ℝ := W.formConst a₀ b₀ with hC₀
  set C₁ : ℝ := W.formConst a₁ b₁ with hC₁
  have hC₀pos : 0 < C₀ := W.formConst_pos hab₀
  have hC₁pos : 0 < C₁ := W.formConst_pos hab₁
  set Sc : ℝ := W a₀ + W a₁ + W b₀ + W b₁ with hSc
  have hScpos : 0 < Sc := by
    have h₁ : (0 : ℝ) ≤ W a₁ := W.nonneg _
    have h₂ : (0 : ℝ) ≤ W b₁ := W.nonneg _
    have h₃ : (0 : ℝ) ≤ W a₀ := W.nonneg _
    have h₄ : (0 : ℝ) ≤ W b₀ := W.nonneg _
    rcases hab₀ with h | h
    · have := W.pos h; rw [hSc]; linarith
    · have := W.pos h; rw [hSc]; linarith
  have hdpos : 0 < W (a₀ * b₁ - a₁ * b₀) := W.pos hd
  -- neither normalized value is small
  have hmax : (Sc / W (a₀ * b₁ - a₁ * b₀))⁻¹ ≤ max u₀ u₁ := by
    have key := W.le_max_apply_add_mul a₀ b₀ a₁ b₁ β
    have hdiv : max u₀ u₁ = max (W (a₀ + b₀ * β)) (W (a₁ + b₁ * β)) / max 1 (W β) := by
      rw [hu₀, hu₁, max_div_div_right hA.le]
    rw [hdiv, inv_div, le_div_iff₀ hA, div_mul_eq_mul_div, div_le_iff₀ hScpos]
    calc W (a₀ * b₁ - a₁ * b₀) * max 1 (W β)
        ≤ Sc * max (W (a₀ + b₀ * β)) (W (a₁ + b₁ * β)) := key
      _ = max (W (a₀ + b₀ * β)) (W (a₁ + b₁ * β)) * Sc := by ring
  have hminuv : min u₀ u₁ ≤ Sc / W (a₀ * b₁ - a₁ * b₀) * (u₀ * u₁) :=
    min_le_mul_of_inv_le_max hu₀nn hu₁nn (div_pos hScpos hdpos) hmax
  -- the two comparisons, and the choice of the smaller one
  have hstep₀ : W.onePointApprox (OnePoint.formRoot a₀ b₀) β ≤ C₀ * u₀ :=
    W.onePointApprox_formRoot_le hab₀ β
  have hstep₁ : W.onePointApprox (OnePoint.formRoot a₁ b₁) β ≤ C₁ * u₁ :=
    W.onePointApprox_formRoot_le hab₁ β
  have hmin : min (C₀ * u₀) (C₁ * u₁) ≤ (C₀ + C₁) * min u₀ u₁ := by
    rcases le_total u₀ u₁ with h | h
    · rw [min_eq_left h]
      exact le_trans (min_le_left _ _) (by nlinarith)
    · rw [min_eq_right h]
      exact le_trans (min_le_right _ _) (by nlinarith)
  calc min (W.onePointApprox (OnePoint.formRoot a₀ b₀) β)
        (W.onePointApprox (OnePoint.formRoot a₁ b₁) β)
      ≤ min (C₀ * u₀) (C₁ * u₁) := min_le_min hstep₀ hstep₁
    _ ≤ (C₀ + C₁) * min u₀ u₁ := hmin
    _ ≤ (C₀ + C₁) * (Sc / W (a₀ * b₁ - a₁ * b₀) * (u₀ * u₁)) := by
        exact mul_le_mul_of_nonneg_left hminuv (by linarith)
    _ = (C₀ + C₁) * (Sc / W (a₀ * b₁ - a₁ * b₀)) * (u₀ * u₁) := by ring

end AbsoluteValue

/-! ### Acceptance criteria -/

/-- **The zero of the form `a X₀` is the point at infinity.** This is the bridge to Layer 3.3:
the form that does not involve `X₁` vanishes only at `[0 : 1]`, whose image in the chart
`[x₀ : x₁] ↦ x₁ / x₀` is `∞`, and the local factor there is `(max 1 |β|)⁻¹`. -/
example {F : Type*} [Field F] (a : F) : OnePoint.formRoot a (0 : F) = ∞ :=
  OnePoint.formRoot_of_eq_zero a

/-- **The zero of the form `X₁ - t X₀` is `t`.** This is the other end of the bridge: the forms
of Roth's theorem are `X₀` and `X₁ - α v X₀`, and their zeros are `∞` and `α v`. -/
example {F : Type*} [Field F] (t : F) : OnePoint.formRoot (-t) (1 : F) = (t : OnePoint F) := by
  rw [OnePoint.formRoot_of_ne_zero _ one_ne_zero, div_one, neg_neg]

/-- **The comparison is an equality at the target `∞`.** No truncation happens there, so the
constant is exactly `|a|⁻¹`; the two branches of `formConst` are different in kind, and only the
finite one pays for the truncation. -/
example {F : Type*} [Field F] (W : AbsoluteValue F ℝ) {a : F} (ha : a ≠ 0) (β : F) :
    W.onePointApprox (OnePoint.formRoot a 0) β
      = W.formConst a 0 * (W (a + 0 * β) / max 1 (W β)) := by
  have hA : (0 : ℝ) < max 1 (W β) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have ha0 : W a ≠ 0 := (W.pos ha).ne'
  rw [OnePoint.formRoot_of_eq_zero, W.formConst_of_eq_zero,
    AbsoluteValue.onePointApprox_infty, zero_mul, add_zero]
  field_simp

/-- **Sharpness: the constant of the comparison must depend on the target.** At `β = t + 1` the
truncated factor is `1` while the untruncated one is `1 / max 1 |β|`, so no constant independent
of `t` can bound the first by the second. This is why `formConst` carries `2 + 2 |t|` and not a
numeral, and it is what forces Layer 3.4 to absorb a constant by lowering the exponent. -/
example (c : ℝ) : ∃ t β : ℝ, ¬(min 1 |β - t| * max 1 |β| ≤ c * |β - t|) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max c 0)
  have hn0 : (0 : ℝ) ≤ n := le_trans (le_max_right c 0) hn.le
  have hnc : c < n := lt_of_le_of_lt (le_max_left c 0) hn
  refine ⟨(n : ℝ), (n : ℝ) + 1, ?_⟩
  rw [show ((n : ℝ) + 1 - n) = 1 by ring, abs_one, min_self,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1), max_eq_right (by linarith), one_mul,
    mul_one]
  linarith
