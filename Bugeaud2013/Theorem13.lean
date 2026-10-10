/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Palindromic

/-!
# Theorem 1.3 (Bugeaud 2013, §1)

A sequence `a = a₁ a₂ …` satisfies **Condition `(∗)`** if it is not eventually periodic and
there are finite words `W_n`, `U_n`, `V_n` with

1. for every `n`, `W_n U_n V_n U_n` or `W_n U_n V_n Ū_n` a prefix of `a`;
2. `|V_n| / |U_n|` bounded;
3. `|W_n| / |U_n|` bounded;
4. `|U_n|` increasing.

**Theorem 1.3**: if `(q_ℓ^{1/ℓ})` is bounded and `a` satisfies `(∗)`, then
`[0; a₁, a₂, …]` is transcendental. It is the union of Theorem 3.1 (infinitely many `n` of the
first kind, Condition `(♠)`) and Theorem 5.1 (infinitely many of the second kind, `(♣)`).

## Main definitions

* `Function.IsStar s`: Condition `(∗)`.

## Main results

* `Nat.transcendental_contFrac_of_isStar`: **Theorem 1.3**.
-/

@[expose] public section

open Filter

namespace Function

variable {α : Type*}

/-- **Condition `(∗)`** (Bugeaud 2013, §1): `s` is not eventually periodic and has, for every
`n`, the repetition `W U V U` or the quasi-palindrome `W U V Ū` as a prefix, with `|V| / |U|`
and `|W| / |U|` bounded and `|U|` strictly increasing. -/
def IsStar (s : ℕ → α) : Prop :=
  ¬ IsEventuallyPeriodic s ∧ ∃ W U V : ℕ → List α,
    (∀ n, (∀ i, i < (W n ++ U n ++ V n ++ U n).length →
        (W n ++ U n ++ V n ++ U n)[i]? = some (s i)) ∨
      (∀ i, i < (W n ++ U n ++ V n ++ (U n).reverse).length →
        (W n ++ U n ++ V n ++ (U n).reverse)[i]? = some (s i))) ∧
    BddAbove (Set.range fun n ↦ ((V n).length : ℝ) / (U n).length) ∧
    BddAbove (Set.range fun n ↦ ((W n).length : ℝ) / (U n).length) ∧
    StrictMono fun n ↦ (U n).length

/-- Bounded ratios stay bounded along a subsequence. -/
theorem bddAbove_range_comp {f : ℕ → ℝ} (h : BddAbove (Set.range f)) (g : ℕ → ℕ) :
    BddAbove (Set.range (f ∘ g)) :=
  h.mono (Set.range_comp_subset_range g f)

end Function

namespace Nat

variable {a : ℕ → ℕ}

/-- **Bugeaud 2013, Theorem 1.3.** Let `a₁, a₂, …` be positive integers with `(q_ℓ^{1/ℓ})`
bounded. If `(a_ℓ)_{ℓ ≥ 1}` satisfies Condition `(∗)`, then `[0; a₁, a₂, …]` is transcendental. -/
theorem transcendental_contFrac_of_isStar (ha : ∀ n, 1 ≤ a (n + 1))
    (hq : BddAbove (Set.range fun ℓ : ℕ ↦ (contDen a ℓ : ℝ) ^ (1 / (ℓ : ℝ))))
    (hs : Function.IsStar fun k ↦ a (k + 1)) : Transcendental ℚ (contFrac a) := by
  obtain ⟨hnp, W, U, V, hpre, hV, hW, hU⟩ := hs
  by_cases hfr : ∃ᶠ n in atTop, ∀ i, i < (W n ++ U n ++ V n ++ U n).length →
      (W n ++ U n ++ V n ++ U n)[i]? = some (a (i + 1))
  · -- infinitely many repetitions: Theorem 3.1
    obtain ⟨g, hg, hgP⟩ := extraction_of_frequently_atTop hfr
    exact transcendental_contFrac_of_isSpade ha hq ⟨hnp, W ∘ g, U ∘ g, V ∘ g, fun n ↦ hgP n,
      Function.bddAbove_range_comp hV g, Function.bddAbove_range_comp hW g, hU.comp hg⟩
  · -- otherwise infinitely many quasi-palindromes: Theorem 5.1
    have hfr' : ∃ᶠ n in atTop, ∀ i, i < (W n ++ U n ++ V n ++ (U n).reverse).length →
        (W n ++ U n ++ V n ++ (U n).reverse)[i]? = some (a (i + 1)) :=
      ((not_frequently.mp hfr).mono fun n hn ↦ (hpre n).resolve_left hn).frequently
    obtain ⟨g, hg, hgP⟩ := extraction_of_frequently_atTop hfr'
    exact transcendental_contFrac_of_isClub ha hq ⟨hnp, W ∘ g, U ∘ g, V ∘ g, fun n ↦ hgP n,
      Function.bddAbove_range_comp hV g, Function.bddAbove_range_comp hW g, hU.comp hg⟩

end Nat
