/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.StammeringWords
public import Mathlib.Order.Filter.AtTopBot.Basic

-- Used only inside proofs.
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Filter.AtTopBot.Monoid

/-!
# Condition `(♣)` (Bugeaud 2013, §5)

A sequence `a = a₁ a₂ …` satisfies **Condition `(♣)`** if it is not eventually periodic and there
are finite words `W_n`, `U_n`, `V_n` with

1. `W_n U_n V_n Ū_n` a prefix of `a`, where `Ū` is the mirror image of `U`;
2. `|V_n| / |U_n|` bounded;
3. `|W_n| / |U_n|` bounded;
4. `|U_n|` increasing.

The proof of Theorem 5.1 only uses the lengths `w_n`, `u_n`, `v_n` and the symmetry
`a_{w+u+v+1+j} = a_{w+u-j}` for `j < u`. As for `(♠)` (`Spade.lean`), the lengths are normalized
once: the first letter of `U` is moved into `W` (`W U V Ū = (W x) U' V Ū' x` for `U = x U'`), so
that `w_n ≥ 1`. Adamczewski–Bugeaud (2007) treat `w_n = 0` separately (their Theorem 2); the shift
makes that unnecessary.

## Main definitions

* `Function.HasClubRepetitions s`: the quasi-palindromes of `(♣)` (items 1–4), for a sequence
  `s` indexed from `0`.
* `Function.IsClub s`: Condition `(♣)`.
* `Nat.ClubData a w u v C`: the normalized lengths, for `a` indexed from `1`.

## Main results

* `Nat.exists_clubData`: Condition `(♣)` for `(a_{k+1})_k` gives normalized lengths.
* `Nat.ClubData.comp`: the normalized lengths pass to subsequences.
-/

@[expose] public section

open Filter

namespace Function

variable {α : Type*}

/-- **The quasi-palindromes of Condition `(♣)`**: words `W n`, `U n`, `V n` with `W U V Ū` a
prefix of `s`, `|V| / |U|` and `|W| / |U|` bounded, and `|U|` strictly increasing. -/
def HasClubRepetitions (s : ℕ → α) : Prop :=
  ∃ W U V : ℕ → List α,
    (∀ n i, i < (W n ++ U n ++ V n ++ (U n).reverse).length →
      (W n ++ U n ++ V n ++ (U n).reverse)[i]? = some (s i)) ∧
    BddAbove (Set.range fun n ↦ ((V n).length : ℝ) / (U n).length) ∧
    BddAbove (Set.range fun n ↦ ((W n).length : ℝ) / (U n).length) ∧
    StrictMono fun n ↦ (U n).length

/-- **Condition `(♣)`** (Bugeaud 2013, §5): `s` is not eventually periodic and has the
quasi-palindromes `W_n U_n V_n Ū_n`. -/
def IsClub (s : ℕ → α) : Prop := ¬ IsEventuallyPeriodic s ∧ HasClubRepetitions s

end Function

namespace Nat

/-- **The normalized lengths of Condition `(♣)`** for `a = a₁ a₂ …`: for every `n`, the word
`a_{w+u+v+1} … a_{w+2u+v}` is the mirror image of `a_{w+1} … a_{w+u}` (`w = w n`, `u = u n`,
`v = v n`); `w ≥ 1`; `w + v ≤ C u`; `u → ∞`. -/
structure ClubData (a : ℕ → ℕ) (w u v : ℕ → ℕ) (C : ℕ) : Prop where
  rep : ∀ n j, j < u n → a (w n + u n + v n + 1 + j) = a (w n + u n - j)
  one_le : ∀ n, 1 ≤ w n
  le : ∀ n, w n + v n ≤ C * u n
  tendsto : Tendsto u atTop atTop

variable {a : ℕ → ℕ} {w u v : ℕ → ℕ} {C : ℕ}

/-- The normalized lengths pass to subsequences. -/
theorem ClubData.comp (h : ClubData a w u v C) {g : ℕ → ℕ} (hg : StrictMono g) :
    ClubData a (w ∘ g) (u ∘ g) (v ∘ g) C where
  rep n := h.rep (g n)
  one_le n := h.one_le (g n)
  le n := h.le (g n)
  tendsto := h.tendsto.comp hg.tendsto_atTop

/-- The symmetry read off the prefix `W U V Ū`: `s_{|W|+|U|+|V|+i} = s_{|W|+|U|-1-i}` for
`i < |U|`. -/
theorem _root_.List.getElem?_club {β : Type*} {s : ℕ → β} {W U V : List β}
    (h : ∀ i, i < (W ++ U ++ V ++ U.reverse).length →
      (W ++ U ++ V ++ U.reverse)[i]? = some (s i)) {i : ℕ} (hi : i < U.length) :
    s (W.length + U.length + V.length + i) = s (W.length + (U.length - 1 - i)) := by
  have hl : (W ++ U ++ V ++ U.reverse).length = W.length + U.length + V.length + U.length := by
    simp only [List.length_append, List.length_reverse]
  have h1 := h (W.length + (U.length - 1 - i)) (by omega)
  have h2 := h (W.length + U.length + V.length + i) (by omega)
  rw [List.append_assoc, List.append_assoc, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_append_left (by omega)] at h1
  rw [List.getElem?_append_right (by simp only [List.length_append]; omega)] at h2
  simp only [List.length_append, Nat.add_sub_cancel_left] at h2
  rw [List.getElem?_reverse hi, h1] at h2
  exact (Option.some_injective _ h2).symm

/-- **Condition `(♣)` gives normalized lengths.** -/
theorem exists_clubData (h : Function.HasClubRepetitions fun k ↦ a (k + 1)) :
    ∃ w u v : ℕ → ℕ, ∃ C : ℕ, ClubData a w u v C := by
  obtain ⟨W, U, V, hpre, ⟨B, hB⟩, ⟨B', hB'⟩, hmono⟩ := h
  set w0 : ℕ → ℕ := fun n ↦ (W n).length
  set u0 : ℕ → ℕ := fun n ↦ (U n).length
  set v0 : ℕ → ℕ := fun n ↦ (V n).length
  have hu0 (n : ℕ) : n ≤ u0 n := hmono.le_apply
  -- the symmetry in the indexing `a₁ a₂ …`
  have rep0 (n j : ℕ) (hj : j < u0 n) :
      a (w0 n + u0 n + v0 n + 1 + j) = a (w0 n + u0 n - j) := by
    have := List.getElem?_club (s := fun k ↦ a (k + 1)) (hpre n) (i := j) hj
    rw [show (W n).length + (U n).length + (V n).length + j + 1 =
        w0 n + u0 n + v0 n + 1 + j by simp only [w0, u0, v0]; omega,
      show (W n).length + ((U n).length - 1 - j) + 1 = w0 n + u0 n - j by
        simp only [w0, u0] at hj ⊢; omega] at this
    exact this
  -- the linear bound `w₀ + v₀ ≤ C₀ u₀` for `n ≥ 1`
  set C0 : ℕ := ⌈B + B'⌉₊
  have hbd (n : ℕ) (hn : 1 ≤ n) : w0 n + v0 n ≤ C0 * u0 n := by
    have hpos : (0 : ℝ) < u0 n := by exact_mod_cast (show 0 < u0 n by have := hu0 n; omega)
    have h1 := hB ⟨n, rfl⟩
    have h2 := hB' ⟨n, rfl⟩
    simp only at h1 h2
    rw [div_le_iff₀ hpos] at h1 h2
    have h3 : ((w0 n + v0 n : ℕ) : ℝ) ≤ (C0 : ℝ) * u0 n := by
      push_cast
      have : B + B' ≤ (C0 : ℝ) := Nat.le_ceil _
      nlinarith
    exact_mod_cast h3
  -- move the first letter of `U` into `W`, on the indices `n + 2`
  refine ⟨fun n ↦ w0 (n + 2) + 1, fun n ↦ u0 (n + 2) - 1, fun n ↦ v0 (n + 2), 2 * C0 + 1,
    fun n j hj ↦ ?_, fun n ↦ by omega, fun n ↦ ?_, ?_⟩
  · have := hu0 (n + 2)
    have h := rep0 (n + 2) j (by omega)
    rw [show w0 (n + 2) + u0 (n + 2) + v0 (n + 2) + 1 + j =
        w0 (n + 2) + 1 + (u0 (n + 2) - 1) + v0 (n + 2) + 1 + j by omega,
      show w0 (n + 2) + u0 (n + 2) - j = w0 (n + 2) + 1 + (u0 (n + 2) - 1) - j by omega] at h
    exact h
  · have hb := hbd (n + 2) (by omega)
    have := hu0 (n + 2)
    -- `w₀ + v₀ + 1 ≤ C₀ u₀ + 1 ≤ (2 C₀ + 1) (u₀ - 1)` as `u₀ ≥ 2`
    have h3 : C0 * u0 (n + 2) ≤ 2 * C0 * (u0 (n + 2) - 1) :=
      calc C0 * u0 (n + 2) ≤ C0 * (2 * (u0 (n + 2) - 1)) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * C0 * (u0 (n + 2) - 1) := by ring
    have h4 : (2 * C0 + 1) * (u0 (n + 2) - 1) = 2 * C0 * (u0 (n + 2) - 1) +
        (u0 (n + 2) - 1) := by ring
    omega
  · refine tendsto_atTop_atTop.2 fun b ↦ ⟨b, fun n hn ↦ ?_⟩
    have := hu0 (n + 2)
    omega

end Nat
