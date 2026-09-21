/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Basic.ENNReal.BigOperators

/-!
# The weighted order of a multivariate polynomial

Give each variable a weight `w j : ℝ≥0∞` and the monomial `X^μ` the weight `∑ j, μ j * w j`. The
**weighted order** of a polynomial is the least weight of a monomial occurring in it, and `⊤` for
the zero polynomial, which has no monomials at all — the empty infimum. It is the exact dual of
Mathlib's `MvPolynomial.weightedTotalDegree`, and it is what the index of Layer 2.3 becomes once
the polynomial has been translated so that the point in question is the origin.

The content of the file is one theorem: the weighted order is **additive on products** over a
ring with no zero divisors. The usual proof picks a monomial order refining the weight, so as to
name a unique lowest term in each factor; that needs a well-order on the variables, which the
statement does not mention. The proof here does not order anything. The lowest weighted
homogeneous parts `P₀` and `Q₀` of the two factors are polynomials, not terms, and the identity
`coeff μ (P * Q) = coeff μ (P₀ * Q₀)` at every `μ` of the lowest weight holds because a pair from
the antidiagonal with both coefficients nonzero cannot have either weight above its minimum
without pushing the other below it. Then `P₀ * Q₀ ≠ 0` is all that is left, and that is where the
hypothesis on the ring enters — the one place it is used.

## Main results

* `MvPolynomial.weightedOrder`: the definition, as a `Finset.inf` over the support, so that the
  zero polynomial gets `⊤` from `Finset.inf_empty` and not from a special case.
* `MvPolynomial.weightedOrder_eq_top_iff`: `⊤` exactly at the zero polynomial, provided no
  variable has infinite weight.
* `MvPolynomial.le_weightedOrder_add`: the ultrametric inequality, with no hypothesis at all.
* `MvPolynomial.weightedOrder_mul`: **additivity on products**, and `weightedOrder_pow` with it.
* `MvPolynomial.weightedOrder_map`: a ring homomorphism that is injective changes nothing.

## Implementation notes

⚠ **The weights are `ℝ≥0∞`, and `⊤` is a real value, not a junk one.** A variable of weight `⊤`
is one that the order is unwilling to see: every polynomial in which it occurs at all has order
`⊤`. That is the only reason `weightedOrder_eq_top_iff` and `weightedOrder_mul` carry the
hypothesis `∀ j, w j ≠ ⊤`, and it is the only hypothesis either of them carries. Layer 2.3
supplies weights of the form `ENNReal.ofReal _`, which are never `⊤`, so the hypothesis
disappears there.

⚠ **Nothing is assumed about `σ`.** In particular the variables are not ordered, not well-ordered
and not finite in number, and the weights are not assumed positive, injective or anything else. A
weight of `0` is allowed and makes its variable invisible to the order.

⚠ **`NoZeroDivisors` is used once**, to know `P₀ * Q₀ ≠ 0`. Everything else in the file, the
inequality `weightedOrder P + weightedOrder Q ≤ weightedOrder (P * Q)` included, holds over any
commutative semiring, and a rejection test below shows that the missing inequality really does
fail without it.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§6.3 — the index of 6.3.2 is the weighted order of the translated polynomial, and its
multiplicativity is the first of the valuation properties collected there.

This is Layer 2.3 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Finsupp

/-- The weight of an exponent is finite as soon as the weight of every variable is. -/
theorem weight_ne_top {σ : Type*} {w : σ → ℝ≥0∞} (hw : ∀ j, w j ≠ ⊤) (μ : σ →₀ ℕ) :
    Finsupp.weight w μ ≠ ⊤ := by
  rw [Finsupp.weight_apply, Finsupp.sum, ← lt_top_iff_ne_top, ENNReal.sum_lt_top]
  exact fun j _ ↦ lt_top_iff_ne_top.mpr
    (by rw [nsmul_eq_mul]; exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (hw j))

end Finsupp

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] {w : σ → ℝ≥0∞} {μ : σ →₀ ℕ} {P Q : MvPolynomial σ R}

/-- **The weighted order** of `P`: the least weight `∑ j, μ j * w j` of a monomial `X^μ`
occurring in `P`, and `⊤` for `P = 0`. -/
def weightedOrder (w : σ → ℝ≥0∞) (P : MvPolynomial σ R) : ℝ≥0∞ :=
  P.support.inf (Finsupp.weight w)

/-- A monomial occurring in `P` has weight at least the weighted order. -/
theorem weightedOrder_le_of_coeff_ne_zero (h : P.coeff μ ≠ 0) :
    weightedOrder w P ≤ Finsupp.weight w μ :=
  Finset.inf_le (mem_support_iff.mpr h)

/-- The weighted order is the greatest lower bound: to bound it from below, bound every monomial
that occurs. -/
theorem le_weightedOrder {c : ℝ≥0∞} (h : ∀ μ, P.coeff μ ≠ 0 → c ≤ Finsupp.weight w μ) :
    c ≤ weightedOrder w P :=
  Finset.le_inf fun _ hμ ↦ h _ (mem_support_iff.mp hμ)

/-- The weighted order of a nonzero polynomial is the weight of one of its monomials. -/
theorem exists_coeff_ne_zero_weightedOrder_eq (w : σ → ℝ≥0∞) (hP : P ≠ 0) :
    ∃ μ, P.coeff μ ≠ 0 ∧ weightedOrder w P = Finsupp.weight w μ := by
  obtain ⟨μ, hμ, h⟩ :=
    Finset.exists_mem_eq_inf P.support (support_nonempty.mpr hP) (Finsupp.weight w)
  exact ⟨μ, mem_support_iff.mp hμ, h⟩

@[simp]
theorem weightedOrder_zero : weightedOrder w (0 : MvPolynomial σ R) = ⊤ := by
  rw [weightedOrder, support_zero, Finset.inf_empty]

/-- **The weighted order is `⊤` exactly at the zero polynomial**, provided no variable is given
infinite weight. -/
theorem weightedOrder_eq_top_iff (hw : ∀ j, w j ≠ ⊤) : weightedOrder w P = ⊤ ↔ P = 0 := by
  refine ⟨fun h ↦ by_contra fun hP ↦ ?_, fun h ↦ by rw [h, weightedOrder_zero]⟩
  obtain ⟨μ, _, hval⟩ := exists_coeff_ne_zero_weightedOrder_eq w hP
  exact Finsupp.weight_ne_top hw μ (hval ▸ h)

/-- The weight of a monomial is its weighted order. -/
theorem weightedOrder_monomial {a : R} (ha : a ≠ 0) :
    weightedOrder w (monomial μ a) = Finsupp.weight w μ := by
  classical
  rw [weightedOrder, support_monomial, ite_eq_right ha, Finset.inf_singleton]

@[simp]
theorem weightedOrder_one [Nontrivial R] : weightedOrder w (1 : MvPolynomial σ R) = 0 := by
  have h1 : (1 : MvPolynomial σ R) = monomial 0 1 := by rw [monomial_zero', C_1]
  rw [h1, weightedOrder_monomial (one_ne_zero (α := R)), map_zero]

/-- **The ultrametric inequality.** No hypothesis: at `P + Q = 0` the left side is at most `⊤`. -/
theorem le_weightedOrder_add (w : σ → ℝ≥0∞) (P Q : MvPolynomial σ R) :
    min (weightedOrder w P) (weightedOrder w Q) ≤ weightedOrder w (P + Q) := by
  refine le_weightedOrder fun μ hμ ↦ ?_
  have hor : P.coeff μ ≠ 0 ∨ Q.coeff μ ≠ 0 := by
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    exact hμ (by simp [hc.1, hc.2])
  rcases hor with h | h
  · exact le_trans (min_le_left _ _) (weightedOrder_le_of_coeff_ne_zero h)
  · exact le_trans (min_le_right _ _) (weightedOrder_le_of_coeff_ne_zero h)

/-- A bound below on `weightedOrder w Q + c` is a bound on the weight of every monomial of `Q`
raised by `c`; the zero polynomial is the case where there are none. -/
theorem le_weightedOrder_add_const {c A : ℝ≥0∞}
    (h : ∀ μ, Q.coeff μ ≠ 0 → A ≤ Finsupp.weight w μ + c) : A ≤ weightedOrder w Q + c := by
  rcases eq_or_ne Q 0 with rfl | hQ
  · rw [weightedOrder_zero, top_add]; exact le_top
  · obtain ⟨μ, hμ, hval⟩ := exists_coeff_ne_zero_weightedOrder_eq w hQ
    rw [hval]
    exact h μ hμ

/-- **Half of multiplicativity**, and the half that needs nothing: every monomial of a product is
a sum of a monomial of each factor. -/
theorem add_le_weightedOrder_mul (w : σ → ℝ≥0∞) (P Q : MvPolynomial σ R) :
    weightedOrder w P + weightedOrder w Q ≤ weightedOrder w (P * Q) := by
  classical
  refine le_weightedOrder fun μ hμ ↦ ?_
  rw [coeff_mul] at hμ
  obtain ⟨⟨a, b⟩, hab, H⟩ := Finset.exists_ne_zero_of_sum_ne_zero hμ
  rw [Finset.mem_antidiagonal] at hab
  calc weightedOrder w P + weightedOrder w Q
      ≤ Finsupp.weight w a + Finsupp.weight w b :=
        add_le_add (weightedOrder_le_of_coeff_ne_zero (left_ne_zero_of_mul H))
          (weightedOrder_le_of_coeff_ne_zero (right_ne_zero_of_mul H))
    _ = Finsupp.weight w μ := by rw [← map_add, hab]

/-- **The weighted order is additive on products.** The hypothesis on the ring is used once, to
know that the product of the two lowest weighted homogeneous parts is not zero. -/
theorem weightedOrder_mul [NoZeroDivisors R] (hw : ∀ j, w j ≠ ⊤) (P Q : MvPolynomial σ R) :
    weightedOrder w (P * Q) = weightedOrder w P + weightedOrder w Q := by
  classical
  rcases eq_or_ne P 0 with rfl | hP
  · rw [zero_mul, weightedOrder_zero, top_add]
  rcases eq_or_ne Q 0 with rfl | hQ
  · rw [mul_zero, weightedOrder_zero, add_top]
  refine le_antisymm ?_ (add_le_weightedOrder_mul w P Q)
  obtain ⟨ν, hν, hmν⟩ := exists_coeff_ne_zero_weightedOrder_eq w hP
  obtain ⟨ρ, hρ, hmρ⟩ := exists_coeff_ne_zero_weightedOrder_eq w hQ
  set m := weightedOrder w P with hm
  set n := weightedOrder w Q with hn
  have hmtop : m ≠ ⊤ := hmν ▸ Finsupp.weight_ne_top hw ν
  have hntop : n ≠ ⊤ := hmρ ▸ Finsupp.weight_ne_top hw ρ
  have hP₀ : weightedHomogeneousComponent w m P ≠ 0 := fun h ↦ hν <| by
    have h2 := coeff_weightedHomogeneousComponent (w := w) m P ν
    rw [h, ite_eq_left hmν.symm] at h2
    simpa using h2.symm
  have hQ₀ : weightedHomogeneousComponent w n Q ≠ 0 := fun h ↦ hρ <| by
    have h2 := coeff_weightedHomogeneousComponent (w := w) n Q ρ
    rw [h, ite_eq_left hmρ.symm] at h2
    simpa using h2.symm
  obtain ⟨μ, hμ⟩ := ne_zero_iff.mp (mul_ne_zero hP₀ hQ₀)
  have hdeg : Finsupp.weight w μ = m + n :=
    IsWeightedHomogeneous.mul (weightedHomogeneousComponent_isWeightedHomogeneous m P)
      (weightedHomogeneousComponent_isWeightedHomogeneous n Q) hμ
  have key : ∀ p : (σ →₀ ℕ) × (σ →₀ ℕ), p.1 + p.2 = μ → P.coeff p.1 ≠ 0 → Q.coeff p.2 ≠ 0 →
      Finsupp.weight w p.1 = m ∧ Finsupp.weight w p.2 = n := by
    intro p hp h1 h2
    have e1 : m ≤ Finsupp.weight w p.1 := weightedOrder_le_of_coeff_ne_zero h1
    have e2 : n ≤ Finsupp.weight w p.2 := weightedOrder_le_of_coeff_ne_zero h2
    have esum : Finsupp.weight w p.1 + Finsupp.weight w p.2 = m + n := by
      rw [← map_add, hp, hdeg]
    exact ⟨(ENNReal.add_left_inj hntop).mp (le_antisymm
        (le_trans (add_le_add le_rfl e2) (le_of_eq esum)) (add_le_add e1 le_rfl)),
      (ENNReal.add_right_inj hmtop).mp (le_antisymm
        (le_trans (add_le_add e1 le_rfl) (le_of_eq esum)) (add_le_add le_rfl e2))⟩
  have hcoeff : (P * Q).coeff μ = (weightedHomogeneousComponent w m P *
      weightedHomogeneousComponent w n Q).coeff μ := by
    rw [coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent]
    by_cases h1 : P.coeff p.1 = 0
    · rw [h1]; simp
    by_cases h2 : Q.coeff p.2 = 0
    · rw [h2]; simp
    obtain ⟨e1, e2⟩ := key p hp h1 h2
    rw [ite_eq_left e1, ite_eq_left e2]
  calc weightedOrder w (P * Q)
      ≤ Finsupp.weight w μ := weightedOrder_le_of_coeff_ne_zero (hcoeff ▸ hμ)
    _ = m + n := hdeg

/-- **The weighted order of a power.** At `n = 0` both sides are `0`, including at `P = 0`. -/
theorem weightedOrder_pow [NoZeroDivisors R] [Nontrivial R] (hw : ∀ j, w j ≠ ⊤)
    (P : MvPolynomial σ R) (k : ℕ) : weightedOrder w (P ^ k) = k * weightedOrder w P := by
  induction k with
  | zero => rw [pow_zero, weightedOrder_one, Nat.cast_zero, zero_mul]
  | succ k ih =>
      rw [pow_succ, weightedOrder_mul hw, ih, Nat.cast_succ, add_mul, one_mul]

/-- Renaming the coefficients along an injective ring homomorphism changes nothing: the support
is the same. -/
theorem weightedOrder_map {S : Type*} [CommSemiring S] {f : R →+* S}
    (hf : Function.Injective f) (P : MvPolynomial σ R) :
    weightedOrder w (map f P) = weightedOrder w P := by
  rw [weightedOrder, weightedOrder, support_map_of_injective P hf]

/-- **Homogeneity in the weights.** The hypothesis is needed only at `P = 0`, where the right
side is `c * ⊤`. -/
theorem weightedOrder_const_mul {c : ℝ≥0∞} (hc : c ≠ 0) (w : σ → ℝ≥0∞) (P : MvPolynomial σ R) :
    weightedOrder (fun j ↦ c * w j) P = c * weightedOrder w P := by
  have hweight : ∀ μ : σ →₀ ℕ,
      Finsupp.weight (fun j ↦ c * w j) μ = c * Finsupp.weight w μ := by
    intro μ
    rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [nsmul_eq_mul, nsmul_eq_mul, mul_left_comm]
  rcases eq_or_ne P 0 with rfl | hP
  · rw [weightedOrder_zero, weightedOrder_zero, ENNReal.mul_top hc]
  obtain ⟨μ, hμ, hval⟩ := exists_coeff_ne_zero_weightedOrder_eq w hP
  refine le_antisymm ?_ (le_weightedOrder fun ν hν ↦ ?_)
  · rw [hval, ← hweight μ]
    exact weightedOrder_le_of_coeff_ne_zero hμ
  · rw [hweight ν]
    gcongr
    exact weightedOrder_le_of_coeff_ne_zero hν

/-! ### Acceptance criteria -/

/-- **Acceptance test: the order of a monomial is the weight of its exponent.** -/
example {a : R} (ha : a ≠ 0) : weightedOrder w (monomial μ a) = Finsupp.weight w μ :=
  weightedOrder_monomial ha

/-- **Acceptance test: additivity on products.** -/
example [NoZeroDivisors R] (hw : ∀ j, w j ≠ ⊤) (P Q : MvPolynomial σ R) :
    weightedOrder w (P * Q) = weightedOrder w P + weightedOrder w Q :=
  weightedOrder_mul hw P Q

/-- **Rejection test: `NoZeroDivisors` is not decoration.** Over `ZMod 4` the product of
`2 X` with itself is `0`, whose order is `⊤`, while the two orders add up to `2`. -/
example : weightedOrder (fun _ ↦ (1 : ℝ≥0∞))
      ((C 2 * X () : MvPolynomial Unit (ZMod 4)) * (C 2 * X ())) = ⊤ ∧
    weightedOrder (fun _ ↦ (1 : ℝ≥0∞)) (C 2 * X () : MvPolynomial Unit (ZMod 4))
      + weightedOrder (fun _ ↦ (1 : ℝ≥0∞)) (C 2 * X () : MvPolynomial Unit (ZMod 4)) = 2 := by
  have h2 : (2 : ZMod 4) ≠ 0 := by decide
  have horder : weightedOrder (fun _ ↦ (1 : ℝ≥0∞))
      (C 2 * X () : MvPolynomial Unit (ZMod 4)) = 1 := by
    rw [C_mul_X_eq_monomial, weightedOrder_monomial h2]
    simp [Finsupp.weight_single]
  refine ⟨?_, by rw [horder]; norm_num⟩
  rw [C_mul_X_eq_monomial, monomial_mul_monomial, show (2 : ZMod 4) * 2 = 0 from by decide,
    monomial_zero, weightedOrder_zero]

/-- **Rejection test: a variable of infinite weight.** Then `weightedOrder w P = ⊤` no longer
says that `P` is zero, which is why `weightedOrder_eq_top_iff` asks for finite weights. -/
example : weightedOrder (fun _ ↦ (⊤ : ℝ≥0∞)) (X () : MvPolynomial Unit ℚ) = ⊤ ∧
    (X () : MvPolynomial Unit ℚ) ≠ 0 := by
  refine ⟨?_, X_ne_zero ()⟩
  have hX : (X () : MvPolynomial Unit ℚ) = monomial (Finsupp.single () 1) 1 := by
    rw [← C_mul_X_eq_monomial, C_1, one_mul]
  rw [hX, weightedOrder_monomial (one_ne_zero (α := ℚ))]
  simp [Finsupp.weight_single]

end MvPolynomial

end

end
