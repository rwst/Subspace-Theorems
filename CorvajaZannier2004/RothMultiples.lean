/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Algebraic.Defs

-- Used only inside proofs.
import DiophantineApproximation.RothRational
import Mathlib.NumberTheory.Height.NumberField

/-!
# Roth's theorem for the integer multiples of an algebraic number

Corvaja and Zannier open the proof of their Lemma 3 with "by Roth's theorem, in any infinite
sequence of solutions `u` cannot be fixed" (p. 4). For a fixed `u` the inequality (2.1) says that
`q (δ u)` is within `c |q| ^ (-1 - ε)` of an integer, without being one; this file shows that only
finitely many `q` can do that.

## Main results

* `Real.finite_setOf_abs_mul_sub_lt`: for a real algebraic `α`, `c` and `ε > 0`, only finitely
  many `q ∈ ℤ` have `0 < |α q - m| < c |q| ^ (-1 - ε)` for some `m ∈ ℤ`.

## Implementation notes

⚠ **Rational `α` is not an exception, and Roth's theorem is stated so that it need not be.** The
repository's `Real.finite_setOf_min_one_abs_sub_le` holds for every real algebraic `ξ`, rational
or not. The approximations `m / q` fall into two kinds: finitely many distinct values, each
reached by finitely many `q` because `|α - β| > 0` is fixed; and values of large height, which
Roth's theorem bounds in number. No case split on the rationality of `α` is needed.

## References

P. Corvaja and U. Zannier, Acta Math. **193** (2004), 175–191, proof of Lemma 3.
-/

@[expose] public section

open Height

namespace Real

/-- **Roth's theorem along the multiples of `α`.** For a real algebraic `α`, `c` and `ε > 0`, only
finitely many integers `q` bring `α q` within `c |q| ^ (-1 - ε)` of an integer `m ≠ α q`. -/
theorem finite_setOf_abs_mul_sub_lt {α : ℝ} (hα : IsAlgebraic ℚ α) (c : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    {q : ℤ | ∃ m : ℤ, 0 < |α * q - m| ∧ |α * q - m| < c * |(q : ℝ)| ^ (-1 - ε)}.Finite := by
  classical
  set Q := {q : ℤ | ∃ m : ℤ, 0 < |α * q - m| ∧ |α * q - m| < c * |(q : ℝ)| ^ (-1 - ε)} with hQ
  -- `q = 0` is not a solution, since then `0 < |m| < 0`
  have hq0 : ∀ q ∈ Q, q ≠ 0 := by
    rintro q ⟨m, hm0, hm⟩ rfl
    simp only [Int.cast_zero, mul_zero, abs_zero] at hm hm0
    rw [Real.zero_rpow (by linarith), mul_zero] at hm
    linarith
  rcases le_or_gt c 0 with hc | hc
  · -- no solutions at all
    convert Set.finite_empty
    refine Set.eq_empty_of_forall_notMem fun q ⟨m, hm0, hm⟩ ↦ ?_
    have : c * |(q : ℝ)| ^ (-1 - ε) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc (Real.rpow_nonneg (abs_nonneg _) _)
    linarith
  choose! m hm using fun q (hq : q ∈ Q) ↦ hq
  -- the approximation `m / q`, written with a positive denominator
  set f : ℤ → ℚ := fun q ↦ ((q.sign * m q : ℤ) : ℚ) / (q.natAbs : ℚ) with hf
  have hqR : ∀ q ∈ Q, (1 : ℝ) ≤ |(q : ℝ)| := fun q hq ↦ by
    exact_mod_cast Int.one_le_abs (hq0 q hq)
  have hfR : ∀ q ∈ Q, ((f q : ℚ) : ℝ) = (m q : ℝ) / q := fun q hq ↦ by
    have hq := hq0 q hq
    simp only [hf, Rat.cast_div, Int.cast_mul,
      Nat.cast_natAbs, Int.cast_abs]
    rcases lt_or_gt_of_ne hq with h | h
    · rw [Int.sign_eq_neg_one_of_neg h, abs_of_neg (by exact_mod_cast h)]
      push_cast
      field_simp
    · rw [Int.sign_eq_one_of_pos h, abs_of_pos (by exact_mod_cast h)]
      push_cast
      ring
  -- `|α - m / q| = |α q - m| / |q|`
  have hdist : ∀ q ∈ Q, |α - (f q : ℝ)| = |α * q - m q| / |(q : ℝ)| := fun q hq ↦ by
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq0 q hq
    rw [hfR q hq, ← abs_div]
    congr 1
    field_simp
  have hpos : ∀ q ∈ Q, 0 < |α - (f q : ℝ)| := fun q hq ↦ by
    rw [hdist q hq]
    exact div_pos (hm q hq).1 (by linarith [hqR q hq])
  have hlt : ∀ q ∈ Q, |α - (f q : ℝ)| < c * |(q : ℝ)| ^ (-2 - ε) := fun q hq ↦ by
    have h1 := hqR q hq
    rw [hdist q hq, div_lt_iff₀ (by linarith), mul_assoc, ← Real.rpow_add_one (by linarith),
      show -2 - ε + 1 = -1 - ε by ring]
    exact (hm q hq).2
  -- the height of `m / q` is at most `A |q|`
  set A : ℝ := |α| + c + 1 with hA
  have hA1 : 1 ≤ A := by rw [hA]; linarith [abs_nonneg α]
  have hH : ∀ q ∈ Q, (max (f q).num.natAbs (f q).den : ℝ) ≤ A * |(q : ℝ)| := fun q hq ↦ by
    have h1 := hqR q hq
    have hq₀ := hq0 q hq
    have hred := Rat.max_num_den_le_of_div (m := q.sign * m q) (Int.natAbs_pos.mpr hq₀)
    have hred' : (max (f q).num.natAbs (f q).den : ℝ) ≤
        max ((q.sign * m q).natAbs : ℝ) (q.natAbs : ℝ) := by exact_mod_cast hred
    refine hred'.trans (max_le ?_ ?_)
    · rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hq₀, one_mul, Nat.cast_natAbs, Int.cast_abs]
      -- `|m| ≤ |α q| + |α q - m| ≤ |α| |q| + c`
      have hle : |(m q : ℝ)| ≤ |α| * |(q : ℝ)| + c := by
        have htri : |(m q : ℝ)| ≤ |α * q| + |α * q - m q| := by
          have := abs_sub (α * q) (α * q - m q)
          simpa using this
        have hsmall : |α * q - m q| ≤ c := by
          refine (hm q hq).2.le.trans ?_
          calc c * |(q : ℝ)| ^ (-1 - ε) ≤ c * 1 := mul_le_mul_of_nonneg_left
                (Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)) hc.le
            _ = c := mul_one c
        rw [abs_mul] at htri
        linarith
      nlinarith [abs_nonneg α]
    · rw [Nat.cast_natAbs, Int.cast_abs]
      nlinarith [abs_nonneg α]
  -- Roth's theorem, with `κ = 2 + ε / 2`
  have hRoth := finite_setOf_min_one_abs_sub_le hα (κ := 2 + ε / 2) (by linarith)
  set B₀ : ℝ := (c * A ^ (2 + ε)) ^ (2 / ε) with hB₀
  have hlow : {β : ℚ | (max β.num.natAbs β.den : ℝ) ≤ max B₀ 1}.Finite := by
    refine (NumberField.finite_setOfPred_mulHeight₁_le (K := ℚ) (max B₀ 1)).subset fun β hβ ↦ ?_
    simp only [Set.mem_ofPred_eq] at hβ ⊢
    rw [Rat.mulHeight₁_eq_max]
    exact_mod_cast hβ
  -- so the approximations take only finitely many values
  have himage : (f '' Q).Finite := by
    refine (hRoth.union hlow).subset ?_
    rintro _ ⟨q, hq, rfl⟩
    by_cases hB : (max (f q).num.natAbs (f q).den : ℝ) ≤ max B₀ 1
    · exact Or.inr hB
    left
    push Not at hB
    set H : ℝ := max (f q).num.natAbs (f q).den
    have hH1 : 1 < H := (le_max_right _ _).trans_lt hB
    have hH0 : 0 < H := zero_lt_one.trans hH1
    have hq1 := hqR q hq
    have hq' : H / A ≤ |(q : ℝ)| := by
      rw [div_le_iff₀ (by linarith)]
      linarith [hH q hq]
    have hcA : c * A ^ (2 + ε) ≤ H ^ (ε / 2) := by
      have h := Real.rpow_le_rpow (by positivity) ((le_max_left _ _).trans hB.le)
        (by positivity : 0 ≤ ε / 2)
      rwa [hB₀, ← Real.rpow_mul (by positivity), div_mul_div_comm, mul_comm 2 ε,
        div_self (by positivity), Real.rpow_one] at h
    change min 1 |α - (f q : ℝ)| ≤ H ^ (-(2 + ε / 2))
    refine (min_le_right _ _).trans ((hlt q hq).le.trans ?_)
    calc c * |(q : ℝ)| ^ (-2 - ε)
        ≤ c * (H / A) ^ (-2 - ε) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) hq'
            (by linarith)) hc.le
      _ = c * A ^ (2 + ε) * H ^ (-2 - ε) := by
          rw [Real.div_rpow hH0.le (by linarith), div_eq_mul_inv, ← Real.rpow_neg (by linarith),
            show -(-2 - ε) = 2 + ε by ring]
          ring
      _ ≤ H ^ (ε / 2) * H ^ (-2 - ε) :=
          mul_le_mul_of_nonneg_right hcA (Real.rpow_nonneg hH0.le _)
      _ = H ^ (-(2 + ε / 2)) := by
          rw [← Real.rpow_add hH0]
          ring_nf
  -- and each value is taken by finitely many `q`
  have hfibre : ∀ β ∈ f '' Q, {q ∈ Q | f q = β}.Finite := by
    rintro _ ⟨q₀, hq₀, rfl⟩
    set r : ℝ := |α - (f q₀ : ℝ)|
    have hr : 0 < r := hpos q₀ hq₀
    -- `r < c |q| ^ (-2 - ε)` bounds `|q|`
    set N : ℕ := ⌈(c / r) ^ (1 / (2 + ε))⌉₊
    refine (Set.finite_Icc (-(N : ℤ)) N).subset fun q ⟨hq, hfq⟩ ↦ ?_
    have h := hlt q hq
    rw [hfq] at h
    have hq1 := hqR q hq
    have hbound : |(q : ℝ)| ≤ (c / r) ^ (1 / (2 + ε)) := by
      have h2 : |(q : ℝ)| ^ (2 + ε) < c / r := by
        have hQp : 0 < |(q : ℝ)| ^ (2 + ε) := by positivity
        rw [show (-2 - ε) = -(2 + ε) by ring, Real.rpow_neg (abs_nonneg _), ← div_eq_mul_inv,
          lt_div_iff₀ hQp] at h
        rw [lt_div_iff₀ hr, mul_comm]
        exact h
      have h3 := Real.rpow_le_rpow (by positivity) h2.le (by positivity : 0 ≤ 1 / (2 + ε))
      rwa [← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel (by linarith),
        Real.rpow_one] at h3
    have hN : |(q : ℝ)| ≤ N := hbound.trans (Nat.le_ceil _)
    rw [abs_le] at hN
    constructor <;> [exact_mod_cast hN.1; exact_mod_cast hN.2]
  exact (himage.biUnion hfibre).subset fun q hq ↦ Set.mem_biUnion ⟨q, hq, rfl⟩ ⟨hq, rfl⟩

end Real
