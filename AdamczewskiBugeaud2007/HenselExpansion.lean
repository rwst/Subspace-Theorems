/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.StammeringWords
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

-- Used only inside proofs.
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Hensel expansions

Every `p`-adic number has a **Hensel expansion** `∑_{k ≥ -m} a k p ^ k` with digits in
`{0, …, p - 1}`. Section 6 of Adamczewski–Bugeaud 2007 transfers the results of the paper from
real numbers to `p`-adic ones through these expansions. This file defines the `p`-adic number of
a sequence of digits, the counterpart of Mathlib's `Real.ofDigits`, and records the two facts
the transcendence criterion needs: the approximation that a repetition in the digits provides,
and the irrationality of the number when the digits are not eventually periodic.

## Main definitions

* `Padic.ofDigits`: the `p`-adic number `∑ n, a n p ^ n` of digits `a : ℕ → Fin p`.

## Main results

* `Padic.summable_ofDigits`: the series converges.
* `Padic.ofDigits_eq_sum_add`: the first `n` digits split off, `α = P_n + p ^ n T_n`.
* `Padic.norm_ofDigits_sub_le`: two expansions sharing `t` digits are `p ^ (-t)`-close.
* `Padic.norm_mul_ofDigits_sub_le`: **the approximation by a repetition** — if the `t` digits
  after position `r + s` repeat those after position `r`, then `(p ^ s - 1) α` is within
  `p ^ (-(r + s + t))` of the integer `p ^ s P_r - P_(r+s)`.
* `Padic.ofDigits_mem_range_ratCast_iff`: **the value is rational if and only if the digits are
  eventually periodic**.

## Implementation notes

⚠ **Only the integral part is defined.** The paper's expansion starts at `k = -m`; that number is
`p ^ (-m)` times the value of the shifted digits, and multiplying by a nonzero rational changes
neither algebraicity nor irrationality. Condition `(∗)_w` is imposed on `(a k)_{k ≥ 1}` in the
paper, so the statements here are about `Padic.ofDigits` of that sequence.

⚠ **The digit `a n` sits at `p ^ n`, not at `b ^ (-(n + 1))`.** `Real.ofDigits` is a number in
`[0, 1]`, read from the most significant digit; a Hensel expansion is read from the least
significant one. What converges is the tail in both cases.

⚠ **Irrationality needs no carries and no coprimality.** The tails `T k` satisfy
`T k = a k + p T (k + 1)`, and `‖T k‖ ≤ 1`, so the digit `a k` is the only one in `{0, …, p - 1}`
within `p⁻¹` of `T k`: equal tails have equal digits and equal successors. If `α = u / v`, then
`v T k` is an integer for every `k` (`p` divides `v T k - v a k`, since that is `p v T (k + 1)`),
and these integers stay in `[-max |u| v, max |u| v]`, so two tails agree.

## References

B. Adamczewski and Y. Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer
bases*, Annals of Mathematics **165** (2007), 547–565, Section 6. Ported from
`AB/HenselExpansions.lean` of the author's `lean-code` corpus.
-/

@[expose] public section

namespace Padic

variable {p : ℕ} [Fact p.Prime]

/-- The `p`-adic number with **Hensel expansion** `a`: `∑ n, a n p ^ n`. -/
noncomputable def ofDigits (a : ℕ → Fin p) : ℚ_[p] :=
  ∑' n, ((a n : ℕ) : ℚ_[p]) * (p : ℚ_[p]) ^ n

/-- **A Hensel expansion converges**: its terms tend to `0`, which is enough in `ℚ_[p]`. -/
theorem summable_ofDigits (a : ℕ → Fin p) :
    Summable fun n ↦ ((a n : ℕ) : ℚ_[p]) * (p : ℚ_[p]) ^ n := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)))
  rw [norm_mul, norm_p_pow, zpow_neg, zpow_natCast, inv_pow]
  exact mul_le_of_le_one_left (by positivity) (by simpa using norm_int_le_one (p := p) (a n : ℕ))

/-- A digit has norm at most `1`. -/
theorem norm_digit_le_one (d : Fin p) : ‖((d : ℕ) : ℚ_[p])‖ ≤ 1 := by
  simpa using norm_int_le_one (p := p) (d : ℕ)

/-- **A Hensel expansion is a `p`-adic integer**: `‖α‖ ≤ 1`. -/
theorem norm_ofDigits_le_one (a : ℕ → Fin p) : ‖ofDigits a‖ ≤ 1 :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun n ↦ by
    rw [norm_mul, norm_pow]
    exact (mul_le_of_le_one_left (by positivity) (norm_digit_le_one _)).trans
      (pow_le_one₀ (norm_nonneg _) norm_p_lt_one.le)

/-- **The first `n` digits split off**: `α = ∑ i < n, a i p ^ i + p ^ n T_n`, where `T_n` is the
value of the digits from position `n` on. -/
theorem ofDigits_eq_sum_add (a : ℕ → Fin p) (n : ℕ) :
    ofDigits a = ((∑ i ∈ Finset.range n, (a i : ℕ) * p ^ i : ℕ) : ℚ_[p])
      + (p : ℚ_[p]) ^ n * ofDigits (fun i ↦ a (i + n)) := by
  rw [ofDigits, ← (summable_ofDigits a).sum_add_tsum_nat_add n, ofDigits, ← tsum_mul_left]
  push_cast
  congr 1
  exact tsum_congr fun i ↦ by rw [pow_add]; ring

/-- **One digit at a time**: `α = a 0 + p T_1`. -/
theorem ofDigits_eq_add_mul (a : ℕ → Fin p) :
    ofDigits a = ((a 0 : ℕ) : ℚ_[p]) + p * ofDigits (fun i ↦ a (i + 1)) := by
  simpa using ofDigits_eq_sum_add a 1

/-- **Two expansions that share their first `t` digits are `p ^ (-t)`-close.** -/
theorem norm_ofDigits_sub_le {a a' : ℕ → Fin p} {t : ℕ} (h : ∀ i < t, a i = a' i) :
    ‖ofDigits a - ofDigits a'‖ ≤ ((p : ℝ) ^ t)⁻¹ := by
  have hs : ∑ i ∈ Finset.range t, (a i : ℕ) * p ^ i
      = ∑ i ∈ Finset.range t, (a' i : ℕ) * p ^ i :=
    Finset.sum_congr rfl fun i hi ↦ by rw [h i (Finset.mem_range.mp hi)]
  rw [ofDigits_eq_sum_add a t, ofDigits_eq_sum_add a' t, hs, add_sub_add_left_eq_sub, ← mul_sub,
    norm_mul, norm_p_pow, zpow_neg, zpow_natCast]
  refine mul_le_of_le_one_right (by positivity) ?_
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (norm_ofDigits_le_one _) (by rw [norm_neg]; exact norm_ofDigits_le_one _))

omit [Fact p.Prime] in
/-- The number formed by the first `n` digits is less than `p ^ n`. -/
theorem sum_digits_lt (a : ℕ → Fin p) (n : ℕ) :
    ∑ i ∈ Finset.range n, (a i : ℕ) * p ^ i < p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h := Nat.mul_le_mul_left (p ^ n) (a n).isLt
    nlinarith

/-- **The approximation by a repetition.** If the `t` digits after position `r + s` repeat those
after position `r`, then `(p ^ s - 1) α` is within `p ^ (-(r + s + t))` of the integer
`p ^ s P_r - P_(r+s)`, where `P_n` is the number formed by the first `n` digits. -/
theorem norm_mul_ofDigits_sub_le (a : ℕ → Fin p) {r s t : ℕ}
    (h : ∀ i < t, a (i + (r + s)) = a (i + r)) :
    ‖((p : ℚ_[p]) ^ s - 1) * ofDigits a
        - ((p : ℚ_[p]) ^ s * ((∑ i ∈ Finset.range r, (a i : ℕ) * p ^ i : ℕ) : ℚ_[p])
          - ((∑ i ∈ Finset.range (r + s), (a i : ℕ) * p ^ i : ℕ) : ℚ_[p]))‖
      ≤ ((p : ℝ) ^ (r + s + t))⁻¹ := by
  have e1 := ofDigits_eq_sum_add a r
  have e2 := ofDigits_eq_sum_add a (r + s)
  have hid : ((p : ℚ_[p]) ^ s - 1) * ofDigits a
        - ((p : ℚ_[p]) ^ s * ((∑ i ∈ Finset.range r, (a i : ℕ) * p ^ i : ℕ) : ℚ_[p])
          - ((∑ i ∈ Finset.range (r + s), (a i : ℕ) * p ^ i : ℕ) : ℚ_[p]))
      = (p : ℚ_[p]) ^ (r + s)
        * (ofDigits (fun i ↦ a (i + r)) - ofDigits (fun i ↦ a (i + (r + s)))) := by
    rw [pow_add] at e2 ⊢
    linear_combination (p : ℚ_[p]) ^ s * e1 - e2
  rw [hid, norm_mul, norm_p_pow, zpow_neg, zpow_natCast, pow_add _ (r + s) t, mul_inv]
  exact mul_le_mul_of_nonneg_left (norm_ofDigits_sub_le fun i hi ↦ (h i hi).symm)
    (by positivity)

/-- **An eventually periodic expansion has a rational value.** -/
theorem ofDigits_mem_range_ratCast {a : ℕ → Fin p} (ha : Function.IsEventuallyPeriodic a) :
    ofDigits a ∈ Set.range ((↑) : ℚ → ℚ_[p]) := by
  obtain ⟨N, s, hs, h⟩ := ha
  have e := ofDigits_eq_sum_add (fun i ↦ a (i + N)) s
  have hshift : (fun i ↦ a (i + s + N)) = fun i ↦ a (i + N) := funext fun i ↦ by
    rw [show i + s + N = i + N + s by ring]
    exact h _ (Nat.le_add_left _ _)
  rw [hshift] at e
  set T := ofDigits (fun i ↦ a (i + N))
  set P : ℕ := ∑ i ∈ Finset.range s, (a (i + N) : ℕ) * p ^ i
  have hp1 : (1 : ℚ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hne : (1 : ℚ) - (p : ℚ) ^ s ≠ 0 := sub_ne_zero.mpr (one_lt_pow₀ hp1 hs.ne').ne
  have hne' : (1 : ℚ_[p]) - (p : ℚ_[p]) ^ s ≠ 0 := by exact_mod_cast hne
  have hT : T = (P : ℚ_[p]) / (1 - (p : ℚ_[p]) ^ s) := by
    rw [eq_div_iff hne']
    linear_combination e
  refine ⟨(∑ i ∈ Finset.range N, (a i : ℕ) * p ^ i : ℕ) + (p : ℚ) ^ N * (P / (1 - (p : ℚ) ^ s)),
    ?_⟩
  rw [ofDigits_eq_sum_add a N]
  change _ = _ + _ * T
  rw [hT]
  push_cast
  ring

/-- **A Hensel expansion that is not eventually periodic has an irrational value.** -/
theorem ofDigits_notMem_range_ratCast {a : ℕ → Fin p}
    (ha : ¬ Function.IsEventuallyPeriodic a) : ofDigits a ∉ Set.range ((↑) : ℚ → ℚ_[p]) := by
  set T : ℕ → ℚ_[p] := fun k ↦ ofDigits (fun i ↦ a (i + k)) with hT
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hrec : ∀ k, T k = ((a k : ℕ) : ℚ_[p]) + p * T (k + 1) := fun k ↦ by
    have e := ofDigits_eq_add_mul (fun i ↦ a (i + k))
    have hsh : (fun i ↦ a (i + 1 + k)) = fun i ↦ a (i + (k + 1)) :=
      funext fun i ↦ by rw [add_assoc, add_comm 1 k]
    simp only [zero_add, hsh] at e
    exact e
  have hTT : ∀ i j, ‖T i - T j‖ ≤ 1 := fun i j ↦ by
    simpa using norm_ofDigits_sub_le (a := fun n ↦ a (n + i)) (a' := fun n ↦ a (n + j)) (t := 0)
      (fun _ h ↦ absurd h (Nat.not_lt_zero _))
  -- an integer that is `p` times a `p`-adic integer is divisible by `p`
  have hdvd : ∀ d : ℤ, ∀ y : ℚ_[p], ‖y‖ ≤ 1 → (d : ℚ_[p]) = p * y → (p : ℤ) ∣ d := by
    intro d y hy hd
    have hn : ‖(d : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
      rw [hd, norm_mul, norm_p, Nat.cast_one, zpow_neg, zpow_one]
      exact mul_le_of_le_one_right (by positivity) hy
    simpa using (norm_int_le_pow_iff_dvd d 1).mp hn
  -- equal tails have equal digits and equal successors
  have hdig : ∀ i j, T i = T j → a i = a j ∧ T (i + 1) = T (j + 1) := by
    intro i j hij
    have hd : ((((a i : ℕ) : ℤ) - (a j : ℕ) : ℤ) : ℚ_[p]) = p * (T (j + 1) - T (i + 1)) := by
      push_cast
      linear_combination hij + hrec j - hrec i
    have h0 : ((a i : ℕ) : ℤ) - (a j : ℕ) = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd (hdvd _ _ (hTT _ _) hd) (abs_sub_lt_iff.mpr ?_)
      have := (a i).isLt
      have := (a j).isLt
      constructor <;> omega
    have haij : a i = a j := Fin.ext (by omega)
    have hc : ((a i : ℕ) : ℚ_[p]) = (a j : ℕ) := by rw [haij]
    exact ⟨haij, mul_left_cancel₀ hp0 (by linear_combination hrec j - hrec i + hij - hc)⟩
  rintro ⟨q, hq⟩
  -- the tails are rationals with denominator `q.den` and bounded numerators
  set M : ℤ := max |q.num| q.den with hM
  have hM0 : 0 ≤ M := le_max_of_le_left (abs_nonneg _)
  have hnum : ∀ k, ∃ c : ℤ, |c| ≤ M ∧ (q.den : ℚ_[p]) * T k = c := by
    intro k
    induction k with
    | zero =>
      refine ⟨q.num, le_max_left _ _, ?_⟩
      have hT0 : T 0 = ofDigits a := rfl
      rw [hT0, ← hq]
      exact_mod_cast Rat.den_mul_eq_num q
    | succ k ih =>
      obtain ⟨c, hcM, hc⟩ := ih
      have hd : ((c - q.den * (a k : ℕ) : ℤ) : ℚ_[p]) = p * (q.den * T (k + 1)) := by
        push_cast
        rw [← hc, hrec k]
        ring
      have hy : ‖(q.den : ℚ_[p]) * T (k + 1)‖ ≤ 1 := by
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _)
          (by simpa using norm_int_le_one (p := p) q.den)).trans (norm_ofDigits_le_one _)
      obtain ⟨e, he⟩ := hdvd _ _ hy hd
      refine ⟨e, ?_, mul_left_cancel₀ hp0 ?_⟩
      · have hv : (q.den : ℤ) ≤ M := le_max_right _ _
        have hak : ((a k : ℕ) : ℤ) + 1 ≤ p := by have := (a k).isLt; omega
        have hak0 : (0 : ℤ) ≤ (a k : ℕ) := by positivity
        have hvd : (0 : ℤ) ≤ q.den := by positivity
        have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
        have h1 : (q.den : ℤ) * (a k : ℕ) ≤ M * (p - 1) := by
          have := mul_le_mul hv (by linarith : ((a k : ℕ) : ℤ) ≤ p - 1) hak0 hM0
          linarith
        obtain ⟨hc1, hc2⟩ := abs_le.mp hcM
        refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith
      · rw [← hd, he]
        push_cast
        ring
  choose c hcM hc using hnum
  have hmem : ∀ k, c k ∈ Finset.Icc (-M) M := fun k ↦ Finset.mem_Icc.mpr (abs_le.mp (hcM k))
  obtain ⟨i, j, hne, hij⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k ↦ (⟨c k, hmem k⟩ : Finset.Icc (-M) M))
  have hden : (q.den : ℚ_[p]) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hTeq : T i = T j := by
    have h : c i = c j := congrArg Subtype.val hij
    refine mul_left_cancel₀ hden ?_
    rw [hc, hc, h]
  have key : ∀ i j, i < j → T i = T j → False := by
    intro i j hlt hTij
    have hshift : ∀ t, T (i + t) = T (j + t) := by
      intro t
      induction t with
      | zero => simpa using hTij
      | succ t ih => exact (hdig _ _ ih).2
    refine ha ⟨i, j - i, by omega, fun n hn ↦ ?_⟩
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [show i + t + (j - i) = j + t by omega]
    exact ((hdig _ _ (hshift t)).1).symm
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key i j h hTeq
  · exact key j i h hTeq.symm

/-- **The value of a Hensel expansion is rational if and only if the digits are eventually
periodic.** -/
theorem ofDigits_mem_range_ratCast_iff {a : ℕ → Fin p} :
    ofDigits a ∈ Set.range ((↑) : ℚ → ℚ_[p]) ↔ Function.IsEventuallyPeriodic a :=
  ⟨fun h ↦ by_contra fun ha ↦ ofDigits_notMem_range_ratCast ha h, ofDigits_mem_range_ratCast⟩

end Padic
