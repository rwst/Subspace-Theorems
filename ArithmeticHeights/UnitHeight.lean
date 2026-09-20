/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Extension
public import ArithmeticHeights.FinitePlaceIdeal
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# The height of a unit, and Dirichlet's logarithmic embedding

A unit of the ring of integers of a number field `K` has absolute value `1` at every finite
place, so its height is carried entirely by the infinite ones:

```text
logHeight₁ u = ∑ w | ∞, mult w * log⁺ (w u),   2 * logHeight₁ u = ∑ w | ∞, |mult w * log (w u)|,
```

the second because the same vector of weighted logarithms sums to `0` by the product formula.
That vector is exactly Mathlib's `NumberField.Units.logEmbedding`, except that `logEmbedding`
**drops the coordinate at a distinguished place** `w₀`: its codomain is `{w // w ≠ w₀} → ℝ`. This
file writes the height in terms of the coordinates `logEmbedding` keeps, recovering the missing
one as minus their sum, and reads off the two-sided comparison between the height and the
ℓ¹ norm of the embedding. The last section deduces that a set of units of bounded height is
finite, and records that Mathlib's discreteness of the unit lattice is that same statement read
the other way.

## Main results

* `NumberField.FinitePlace.apply_units_eq_one`: a unit has absolute value `1` at every finite
  place, and hence `NumberField.Units.mulHeight₁_eq_prod_infinitePlace` and
  `NumberField.Units.logHeight₁_eq_sum_infinitePlace`, the height of a unit as a product or sum
  over the infinite places alone, the latter also as
  `NumberField.Units.logHeight₁_eq_sum_posPart`.
* `NumberField.Units.two_mul_logHeight₁_eq_sum_abs`: `2 h(u)` is the ℓ¹ norm of the **full**
  vector of weighted logarithms, over all infinite places.
* `NumberField.Units.logHeight₁_eq_sum_posPart_logEmbedding`: the height in the coordinates
  Mathlib's `logEmbedding` keeps — the positive parts of those coordinates, plus the positive
  part of minus their sum, which is the dropped coordinate at `w₀`.
* `NumberField.Units.two_mul_logHeight₁_eq_sum_abs_logEmbedding_add_abs_sum`: the same
  bookkeeping for the ℓ¹ norm, and with it
  `NumberField.Units.sum_abs_logEmbedding_le_two_mul_logHeight₁` and
  `NumberField.Units.logHeight₁_le_sum_abs_logEmbedding`: the height and the ℓ¹ norm of the
  embedding differ by a factor of at most `2`.
* `NumberField.Units.absLogHeight₁_le_sum_abs_logEmbedding_div` and
  `NumberField.Units.sum_abs_logEmbedding_le_two_mul_finrank_mul_absLogHeight₁`: the same
  comparison in the absolute logarithmic height, which is the relative one divided by the degree.
  This is the form Layer 6.3 consumes.
* `NumberField.Units.finite_setOf_logHeight₁_le`: a set of units of bounded height is finite.

## Implementation notes

⚠ **The two identities that suggest themselves are both false**, and the file states exactly how.
Neither `logHeight₁ u = ∑ (logEmbedding u w)⁺` nor `2 logHeight₁ u = ∑ |logEmbedding u w|` holds:
both sums run over `{w ≠ w₀}` while the height runs over every infinite place, and the term the
embedding drops is not zero. `NumberField.Units.logHeight₁_eq_sum_posPart_logEmbedding_iff` and
`NumberField.Units.two_mul_logHeight₁_eq_sum_abs_logEmbedding_iff` say precisely when each does
hold — when `w₀ u ≤ 1`, respectively `w₀ u = 1` — so a unit whose only large conjugate sits at
the distinguished place refutes both. What survives unconditionally is the two-sided comparison,
and the factor `2` in it is not slack that a sharper argument removes.

⚠ **The ℓ¹ norm here is written as a sum, not as `‖·‖`.** `logSpace K` is a `Pi` type, whose
`norm` in Mathlib is the supremum norm; `NumberField.Units.norm_logEmbedding_le_two_mul_logHeight₁`
and `NumberField.Units.logHeight₁_le_rank_mul_norm_logEmbedding` are the supremum-norm forms, and
the second pays `Units.rank K` for the conversion. The supremum form is what meets Mathlib's
`unitLattice_inter_ball_finite`, whose ball is a ball for that norm.

⚠ **Sums over `{w : InfinitePlace K // w ≠ w₀}` need a `Fintype` instance that only `Classical`
supplies**, since `InfinitePlace K` has no `DecidableEq`; the statements below carry
`open scoped Classical in` for the same reason Mathlib's `sum_logEmbedding_component` does.

⚠ **Finiteness of the units of bounded height is Northcott's theorem restricted along an
injection**, and that is the whole of the proof here. The example at the end of the file runs the
implication in the other direction: it proves Mathlib's `unitLattice_inter_ball_finite`, the
discreteness of the unit lattice that Dirichlet's theorem rests on, from Northcott's theorem and
the comparison above. The two are one fact, which is why this file proves the easy direction and
does not restate Mathlib's.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.5; the comparison between the height of a unit and its logarithmic embedding is their
Proposition 1.5.12, and the finiteness of units of bounded height is the case of Northcott's
theorem (Theorem 1.6.8) that Dirichlet's unit theorem consumes.

This is Layer 6.1 of the `ArithmeticHeights` roadmap.
-/

public section

open Height Module NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem Real

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-!
### A unit is a unit at every finite place
-/

/-- **A unit of `𝓞 K` has absolute value `1` at every finite place.** Both `u` and `u⁻¹` are
algebraic integers, so both absolute values are at most `1` by
`NumberField.FinitePlace.apply_le_one`, and their product is `1`. -/
theorem FinitePlace.apply_units_eq_one (v : FinitePlace K) (u : (𝓞 K)ˣ) :
    v ((u : 𝓞 K) : K) = 1 := by
  have hmul : v ((u : 𝓞 K) : K) * v (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) = 1 := by
    rw [← map_mul]; norm_num
  have hu := FinitePlace.apply_le_one v (u : 𝓞 K)
  have hu' := FinitePlace.apply_le_one v ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)
  nlinarith [v.pos_iff.mpr (Units.coe_ne_zero u), v.pos_iff.mpr (Units.coe_ne_zero u⁻¹)]

namespace Units

/-- The multiplicative height of a unit is a product over the infinite places alone. -/
theorem mulHeight₁_eq_prod_infinitePlace (u : (𝓞 K)ˣ) :
    mulHeight₁ ((u : 𝓞 K) : K)
      = ∏ w : InfinitePlace K, max (w ((u : 𝓞 K) : K)) 1 ^ w.mult := by
  rw [NumberField.mulHeight₁_eq]
  simp [FinitePlace.apply_units_eq_one]

/-- The logarithmic height of a unit is a sum over the infinite places alone. -/
theorem logHeight₁_eq_sum_infinitePlace (u : (𝓞 K)ˣ) :
    logHeight₁ ((u : 𝓞 K) : K)
      = ∑ w : InfinitePlace K, w.mult * log⁺ (w ((u : 𝓞 K) : K)) := by
  rw [NumberField.logHeight₁_eq]
  simp [FinitePlace.apply_units_eq_one]

/-- **The height of a unit is the sum of the positive parts of its weighted logarithms**, over
all infinite places. This is `logHeight₁_eq_sum_infinitePlace` with the weight moved inside the
positive part, which it may be because the weight is nonnegative. -/
theorem logHeight₁_eq_sum_posPart (u : (𝓞 K)ˣ) :
    logHeight₁ ((u : 𝓞 K) : K)
      = ∑ w : InfinitePlace K, ((w.mult : ℝ) * log (w ((u : 𝓞 K) : K)))⁺ := by
  refine (logHeight₁_eq_sum_infinitePlace u).trans (Finset.sum_congr rfl fun w _ ↦ ?_)
  rw [posLog_apply, posPart_def, mul_max_of_nonneg _ _ (Nat.cast_nonneg w.mult), mul_zero,
    max_comm]

/-- `2 * max 0 a = |a| + a`, weighted by a nonnegative scalar. -/
private theorem two_mul_mul_max_eq (c a : ℝ) (hc : 0 ≤ c) :
    2 * (c * max 0 a) = |c * a| + c * a := by
  rw [mul_max_of_nonneg _ _ hc, mul_zero, abs_mul, abs_of_nonneg hc]
  rcases le_or_gt 0 a with h | h
  · rw [abs_of_nonneg h, max_eq_right (mul_nonneg hc h)]; ring
  · rw [abs_of_neg h, max_eq_left (by nlinarith)]; ring

/-- **Twice the height of a unit is the ℓ¹ norm of its vector of weighted logarithms**, taken
over *all* infinite places. The positive parts alone give the height; the product formula, in the
form `NumberField.Units.sum_mult_mul_log`, says the vector sums to `0`, so the negative parts
repeat them. -/
theorem two_mul_logHeight₁_eq_sum_abs (u : (𝓞 K)ˣ) :
    2 * logHeight₁ ((u : 𝓞 K) : K)
      = ∑ w : InfinitePlace K, |(w.mult : ℝ) * log (w ((u : 𝓞 K) : K))| := by
  have key : ∀ w : InfinitePlace K,
      2 * ((w.mult : ℝ) * log⁺ (w ((u : 𝓞 K) : K)))
        = |(w.mult : ℝ) * log (w ((u : 𝓞 K) : K))| + (w.mult : ℝ) * log (w ((u : 𝓞 K) : K)) :=
    fun w ↦ by rw [posLog_apply]; exact two_mul_mul_max_eq _ _ (Nat.cast_nonneg _)
  rw [logHeight₁_eq_sum_infinitePlace, Finset.mul_sum, Finset.sum_congr rfl fun w _ ↦ key w,
    Finset.sum_add_distrib, sum_mult_mul_log u, add_zero]

/-!
### The height in the coordinates of `logEmbedding`

`logEmbedding` omits the coordinate at the distinguished place `w₀`; by the product formula that
coordinate is minus the sum of the others, which is how it re-enters every statement below.
-/

open scoped Classical in
/-- The coordinate `logEmbedding` drops, recovered from the ones it keeps. This is Mathlib's
`sum_logEmbedding_component` with the sign moved. -/
private theorem mult_w₀_mul_log_eq (u : (𝓞 K)ˣ) :
    ((w₀ : InfinitePlace K).mult : ℝ) * log (w₀ ((u : 𝓞 K) : K))
      = -∑ w : {w : InfinitePlace K // w ≠ w₀}, logEmbedding K (Additive.ofMul u) w := by
  rw [sum_logEmbedding_component u]; ring

open scoped Classical in
/-- **The height of a unit through Dirichlet's logarithmic embedding.** The sum of the positive
parts of the coordinates `logEmbedding` keeps, plus the positive part of the coordinate it drops,
which is minus their sum. ⚠ The second summand is not zero in general; see
`NumberField.Units.logHeight₁_eq_sum_posPart_logEmbedding_iff`. -/
theorem logHeight₁_eq_sum_posPart_logEmbedding (u : (𝓞 K)ˣ) :
    logHeight₁ ((u : 𝓞 K) : K)
      = (∑ w : {w : InfinitePlace K // w ≠ w₀}, (logEmbedding K (Additive.ofMul u) w)⁺)
        + (-∑ w : {w : InfinitePlace K // w ≠ w₀}, logEmbedding K (Additive.ofMul u) w)⁺ := by
  rw [logHeight₁_eq_sum_posPart, Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace K),
    mult_w₀_mul_log_eq u, add_comm]
  rfl

open scoped Classical in
/-- **Twice the height of a unit, through Dirichlet's logarithmic embedding.** The ℓ¹ norm of the
coordinates `logEmbedding` keeps, plus the absolute value of their sum — which is the size of the
coordinate it drops. ⚠ The second summand is not zero in general; see
`NumberField.Units.two_mul_logHeight₁_eq_sum_abs_logEmbedding_iff`. -/
theorem two_mul_logHeight₁_eq_sum_abs_logEmbedding_add_abs_sum (u : (𝓞 K)ˣ) :
    2 * logHeight₁ ((u : 𝓞 K) : K)
      = (∑ w : {w : InfinitePlace K // w ≠ w₀}, |logEmbedding K (Additive.ofMul u) w|)
        + |∑ w : {w : InfinitePlace K // w ≠ w₀}, logEmbedding K (Additive.ofMul u) w| := by
  rw [two_mul_logHeight₁_eq_sum_abs,
    Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace K), mult_w₀_mul_log_eq u, abs_neg,
    add_comm]
  rfl

open scoped Classical in
/-- Half of the two-sided comparison: the ℓ¹ norm of the logarithmic embedding is at most twice
the height. -/
theorem sum_abs_logEmbedding_le_two_mul_logHeight₁ (u : (𝓞 K)ˣ) :
    (∑ w : {w : InfinitePlace K // w ≠ w₀}, |logEmbedding K (Additive.ofMul u) w|)
      ≤ 2 * logHeight₁ ((u : 𝓞 K) : K) := by
  rw [two_mul_logHeight₁_eq_sum_abs_logEmbedding_add_abs_sum]
  linarith [abs_nonneg
    (∑ w : {w : InfinitePlace K // w ≠ w₀}, logEmbedding K (Additive.ofMul u) w)]

open scoped Classical in
/-- The other half: the height is at most the ℓ¹ norm of the logarithmic embedding. The dropped
coordinate is bounded by the triangle inequality against the ones that are kept. -/
theorem logHeight₁_le_sum_abs_logEmbedding (u : (𝓞 K)ˣ) :
    logHeight₁ ((u : 𝓞 K) : K)
      ≤ ∑ w : {w : InfinitePlace K // w ≠ w₀}, |logEmbedding K (Additive.ofMul u) w| := by
  have htri := Finset.abs_sum_le_sum_abs
    (fun w : {w : InfinitePlace K // w ≠ w₀} ↦ logEmbedding K (Additive.ofMul u) w) Finset.univ
  have h := two_mul_logHeight₁_eq_sum_abs_logEmbedding_add_abs_sum u
  linarith

/-!
### The two identities that fail, and exactly when they hold
-/

open scoped Classical in
/-- ⚠ **`logHeight₁ u` is the sum of the positive parts of `logEmbedding u` only when the
distinguished place is not the large one.** -/
theorem logHeight₁_eq_sum_posPart_logEmbedding_iff (u : (𝓞 K)ˣ) :
    logHeight₁ ((u : 𝓞 K) : K)
        = ∑ w : {w : InfinitePlace K // w ≠ w₀}, (logEmbedding K (Additive.ofMul u) w)⁺
      ↔ w₀ ((u : 𝓞 K) : K) ≤ 1 := by
  have hm : (0 : ℝ) < ((w₀ : InfinitePlace K).mult : ℝ) := by
    exact_mod_cast (w₀ : InfinitePlace K).mult_pos
  have hlog : log (w₀ ((u : 𝓞 K) : K)) ≤ 0 ↔ w₀ ((u : 𝓞 K) : K) ≤ 1 := by
    rw [← Real.log_one]
    exact Real.log_le_log_iff (pos_at_place u w₀) one_pos
  rw [logHeight₁_eq_sum_posPart_logEmbedding u, add_eq_left, posPart_eq_zero,
    ← mult_w₀_mul_log_eq u, ← hlog]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

open scoped Classical in
/-- ⚠ **`2 * logHeight₁ u` is the ℓ¹ norm of `logEmbedding u` only when the distinguished place
is trivial on `u`.** -/
theorem two_mul_logHeight₁_eq_sum_abs_logEmbedding_iff (u : (𝓞 K)ˣ) :
    2 * logHeight₁ ((u : 𝓞 K) : K)
        = ∑ w : {w : InfinitePlace K // w ≠ w₀}, |logEmbedding K (Additive.ofMul u) w|
      ↔ w₀ ((u : 𝓞 K) : K) = 1 := by
  rw [two_mul_logHeight₁_eq_sum_abs_logEmbedding_add_abs_sum u, add_eq_left, abs_eq_zero,
    ← neg_eq_zero, ← mult_w₀_mul_log_eq u, mult_log_place_eq_zero]

/-!
### The supremum norm, and finiteness
-/

open scoped Classical in
/-- The supremum norm of `logEmbedding u` — the norm of `logSpace K` as a `Pi` type, and the one
whose balls Mathlib's `unitLattice_inter_ball_finite` uses — is at most twice the height. -/
theorem norm_logEmbedding_le_two_mul_logHeight₁ (u : (𝓞 K)ˣ) :
    ‖logEmbedding K (Additive.ofMul u)‖ ≤ 2 * logHeight₁ ((u : 𝓞 K) : K) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w ↦ ?_
  refine le_trans ?_ (sum_abs_logEmbedding_le_two_mul_logHeight₁ u)
  exact Finset.single_le_sum (f := fun w : {w : InfinitePlace K // w ≠ w₀} ↦
    |logEmbedding K (Additive.ofMul u) w|) (fun i _ ↦ abs_nonneg _) (Finset.mem_univ w)

open scoped Classical in
private theorem card_ne_w₀ : Fintype.card {w : InfinitePlace K // w ≠ w₀} = rank K := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, rank]

open scoped Classical in
/-- Conversely the height is at most `Units.rank K` times the supremum norm of the logarithmic
embedding: the conversion from the supremum norm back to the ℓ¹ norm costs the number of
coordinates, which is the unit rank. -/
theorem logHeight₁_le_rank_mul_norm_logEmbedding (u : (𝓞 K)ˣ) :
    logHeight₁ ((u : 𝓞 K) : K) ≤ rank K * ‖logEmbedding K (Additive.ofMul u)‖ := by
  refine (logHeight₁_le_sum_abs_logEmbedding u).trans ?_
  have h := Finset.sum_le_card_nsmul (Finset.univ : Finset {w : InfinitePlace K // w ≠ w₀})
    (fun w ↦ |logEmbedding K (Additive.ofMul u) w|) ‖logEmbedding K (Additive.ofMul u)‖
    fun w _ ↦ by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (logEmbedding K (Additive.ofMul u)) w
  rwa [Finset.card_univ, card_ne_w₀, nsmul_eq_mul] at h

/-- **A set of units of bounded height is finite.** This is Northcott's theorem for `K`
restricted along the injection of `(𝓞 K)ˣ` into `K`; the example at the end of this file runs the
same comparison the other way, and gets Mathlib's `unitLattice_inter_ball_finite` out of it. -/
theorem finite_setOf_logHeight₁_le (B : ℝ) :
    {u : (𝓞 K)ˣ | logHeight₁ ((u : 𝓞 K) : K) ≤ B}.Finite := by
  refine Set.Finite.of_finite_image (f := fun u : (𝓞 K)ˣ ↦ ((u : 𝓞 K) : K)) ?_ ?_
  · exact (NumberField.finite_setOfPred_logHeight₁_le K B).subset
      (by rintro _ ⟨u, hu, rfl⟩; exact hu)
  · exact Set.injOn_of_injective (Units.coe_injective K)

/-!
### The absolute height

The absolute logarithmic height is the relative one divided by the degree, so the comparison
above transfers verbatim. This is the form Layer 6.3 consumes: a fundamental system of units
whose logarithmic embeddings are short has small absolute height.
-/

open scoped Classical in
/-- The absolute logarithmic height of a unit, against the ℓ¹ norm of its logarithmic
embedding. -/
theorem absLogHeight₁_le_sum_abs_logEmbedding_div (u : (𝓞 K)ˣ) :
    absLogHeight₁ ((u : 𝓞 K) : K)
      ≤ (∑ w : {w : InfinitePlace K // w ≠ w₀}, |logEmbedding K (Additive.ofMul u) w|)
          / finrank ℚ K := by
  have hd : (0 : ℝ) < finrank ℚ K := Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K))
  rw [absLogHeight₁_eq]
  gcongr
  exact logHeight₁_le_sum_abs_logEmbedding u

open scoped Classical in
/-- The converse comparison in the absolute height. -/
theorem sum_abs_logEmbedding_le_two_mul_finrank_mul_absLogHeight₁ (u : (𝓞 K)ˣ) :
    (∑ w : {w : InfinitePlace K // w ≠ w₀}, |logEmbedding K (Additive.ofMul u) w|)
      ≤ 2 * finrank ℚ K * absLogHeight₁ ((u : 𝓞 K) : K) := by
  have hd : (finrank ℚ K : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hcancel : 2 * (finrank ℚ K : ℝ) * (logHeight₁ ((u : 𝓞 K) : K) / finrank ℚ K)
      = 2 * logHeight₁ ((u : 𝓞 K) : K) := by field_simp
  rw [absLogHeight₁_eq, hcancel]
  exact sum_abs_logEmbedding_le_two_mul_logHeight₁ u

/-!
### Acceptance criteria
-/

section Examples

open scoped Classical in
/-- **Mathlib's `unitLattice_inter_ball_finite` is Northcott's theorem.** The discreteness of the
unit lattice, on which Dirichlet's unit theorem rests, follows from the finiteness of the units
of bounded height and the comparison `logHeight₁_le_rank_mul_norm_logEmbedding`. Mathlib proves
it directly, from `Embeddings.finite_of_norm_le`; this is the same fact read through the
height. -/
example (r : ℝ) : ((unitLattice K : Set (logSpace K)) ∩ Metric.closedBall 0 r).Finite := by
  refine ((finite_setOf_logHeight₁_le (K := K) (rank K * r)).image
    (fun u ↦ logEmbedding K (Additive.ofMul u))).subset ?_
  rintro x ⟨hx, hball⟩
  obtain ⟨y, -, rfl⟩ := hx
  refine ⟨y.toMul, ?_, rfl⟩
  have hle := logHeight₁_le_rank_mul_norm_logEmbedding (K := K) y.toMul
  have hnorm : ‖logEmbedding K (Additive.ofMul y.toMul)‖ ≤ r := by
    simpa using mem_closedBall_zero_iff.mp hball
  have hrank : (0 : ℝ) ≤ rank K := Nat.cast_nonneg _
  simp only [Set.mem_ofPred_eq]
  nlinarith

end Examples

end Units

end NumberField
