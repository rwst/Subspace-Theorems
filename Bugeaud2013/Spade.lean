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
# Condition `(♠)` (Bugeaud 2013, §3)

A sequence `a = a₁ a₂ …` satisfies **Condition `(♠)`** if it is not eventually periodic and there
are finite words `W_n`, `U_n`, `V_n` with

1. `W_n U_n V_n U_n` a prefix of `a`;
2. `|V_n| / |U_n|` bounded;
3. `|W_n| / |U_n|` bounded;
4. `|U_n|` increasing.

The proof of Theorem 3.1 only uses the lengths `w_n = |W_n|`, `u_n = |U_n|`, `v_n = |V_n|` and the
fact that `a_m = a_{m + u_n + v_n}` for `w_n < m ≤ w_n + u_n`. This file passes to the lengths and
normalizes them, as in the paper (p. 1013), by sliding the repetition to the left: we may assume
that `w_n ≥ 1` and that `a_{w_n} ≠ a_{w_n + u_n + v_n}` whenever `w_n ≥ 2`. The paper slides only
in its second case; doing it once at the start serves both cases and also removes the case
`w_n = 0`, where the formulas of §3 need `p_{-1}`, `q_{-1}`.

## Main definitions

* `Function.HasSpadeRepetitions s`: the repetitions of `(♠)` (items 1–4), for a sequence `s`
  indexed from `0`.
* `Function.IsSpade s`: Condition `(♠)`.
* `Nat.SpadeData a w u v C`: the normalized lengths, for `a` indexed from `1`.

## Main results

* `Nat.exists_spadeData`: Condition `(♠)` for `(a_{k+1})_k` gives normalized lengths.
* `Nat.SpadeData.comp`: the normalized lengths pass to subsequences.
-/

@[expose] public section

open Filter

namespace Function

variable {α : Type*}

/-- **The repetitions of Condition `(♠)`**: words `W n`, `U n`, `V n` with `W U V U` a prefix of
`s`, `|V| / |U|` and `|W| / |U|` bounded, and `|U|` strictly increasing. -/
def HasSpadeRepetitions (s : ℕ → α) : Prop :=
  ∃ W U V : ℕ → List α,
    (∀ n i, i < (W n ++ U n ++ V n ++ U n).length →
      (W n ++ U n ++ V n ++ U n)[i]? = some (s i)) ∧
    BddAbove (Set.range fun n ↦ ((V n).length : ℝ) / (U n).length) ∧
    BddAbove (Set.range fun n ↦ ((W n).length : ℝ) / (U n).length) ∧
    StrictMono fun n ↦ (U n).length

/-- **Condition `(♠)`** (Bugeaud 2013, §3): `s` is not eventually periodic and has the
repetitions `W_n U_n V_n U_n`. -/
def IsSpade (s : ℕ → α) : Prop := ¬ IsEventuallyPeriodic s ∧ HasSpadeRepetitions s

end Function

namespace Nat

/-- **The normalized lengths of Condition `(♠)`** for `a = a₁ a₂ …`: for every `n`, the word
`a_{w+1} … a_{w+u}` recurs at distance `u + v` (`w = w n`, `u = u n`, `v = v n`); `w ≥ 1`;
`w + v ≤ C u`; `u → ∞`; and the repetition cannot be slid further to the left:
`a_w ≠ a_{w+u+v}` when `w ≥ 2`. -/
structure SpadeData (a : ℕ → ℕ) (w u v : ℕ → ℕ) (C : ℕ) : Prop where
  rep : ∀ n m, w n < m → m ≤ w n + u n → a (m + (u n + v n)) = a m
  one_le : ∀ n, 1 ≤ w n
  le : ∀ n, w n + v n ≤ C * u n
  tendsto : Tendsto u atTop atTop
  ne : ∀ n, 2 ≤ w n → a (w n) ≠ a (w n + (u n + v n))

variable {a : ℕ → ℕ} {w u v : ℕ → ℕ} {C : ℕ}

/-- The normalized lengths pass to subsequences. -/
theorem SpadeData.comp (h : SpadeData a w u v C) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    SpadeData a (w ∘ φ) (u ∘ φ) (v ∘ φ) C where
  rep n := h.rep (φ n)
  one_le n := h.one_le (φ n)
  le n := h.le (φ n)
  tendsto := h.tendsto.comp hφ.tendsto_atTop
  ne n := h.ne (φ n)

/-- The period `u + v` is at least `u`, so it tends to infinity too. -/
theorem SpadeData.tendsto_add (h : SpadeData a w u v C) :
    Tendsto (fun n ↦ u n + v n) atTop atTop :=
  tendsto_atTop_mono (fun _ ↦ Nat.le_add_right _ _) h.tendsto

/-- The repetition read off the prefix `W U V U`: `s_{|W| + i} = s_{|W| + |U| + |V| + i}` for
`i < |U|`. -/
theorem _root_.List.getElem?_spade {β : Type*} {s : ℕ → β} {W U V : List β}
    (h : ∀ i, i < (W ++ U ++ V ++ U).length → (W ++ U ++ V ++ U)[i]? = some (s i)) {i : ℕ}
    (hi : i < U.length) : s (W.length + i) = s (W.length + U.length + V.length + i) := by
  have h1 := h (W.length + i) (by simp only [List.length_append]; omega)
  have h2 := h (W.length + U.length + V.length + i) (by simp only [List.length_append]; omega)
  rw [List.append_assoc, List.append_assoc, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_append_left hi] at h1
  rw [List.getElem?_append_right (by simp only [List.length_append]; omega)] at h2
  simp only [List.length_append, Nat.add_sub_cancel_left] at h2
  rw [h1] at h2
  exact Option.some_injective _ h2

/-- **Condition `(♠)` gives normalized lengths.** -/
theorem exists_spadeData (h : Function.HasSpadeRepetitions fun k ↦ a (k + 1)) :
    ∃ w u v : ℕ → ℕ, ∃ C : ℕ, SpadeData a w u v C := by
  classical
  obtain ⟨W, U, V, hpre, ⟨B, hB⟩, ⟨B', hB'⟩, hmono⟩ := h
  set w0 : ℕ → ℕ := fun n ↦ (W n).length
  set u0 : ℕ → ℕ := fun n ↦ (U n).length
  set v0 : ℕ → ℕ := fun n ↦ (V n).length
  have hu0 (n : ℕ) : n ≤ u0 n := hmono.le_apply
  -- the repetition in the indexing `a₁ a₂ …`
  have rep0 (n m : ℕ) (h1 : w0 n < m) (h2 : m ≤ w0 n + u0 n) :
      a (m + (u0 n + v0 n)) = a m := by
    have := List.getElem?_spade (s := fun k ↦ a (k + 1)) (hpre n) (i := m - w0 n - 1)
      (by simp only [u0] at h2 ⊢; omega)
    rw [show (W n).length + (m - w0 n - 1) + 1 = m by simp only [w0] at h1 ⊢; omega,
      show (W n).length + (U n).length + (V n).length + (m - w0 n - 1) + 1 = m + (u0 n + v0 n) by
        simp only [w0, u0, v0] at h1 ⊢; omega] at this
    exact this.symm
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
  -- slide the repetition to the left as far as possible
  have hex (n : ℕ) : ∃ k, ∀ m, k < m → m ≤ k + u0 n → a (m + (u0 n + v0 n)) = a m :=
    ⟨w0 n, rep0 n⟩
  set k : ℕ → ℕ := fun n ↦ Nat.find (hex n)
  have hk (n : ℕ) : ∀ m, k n < m → m ≤ k n + u0 n → a (m + (u0 n + v0 n)) = a m :=
    Nat.find_spec (hex n)
  have hkw (n : ℕ) : k n ≤ w0 n := Nat.find_min' (hex n) (rep0 n)
  have hkne (n : ℕ) (h1 : 1 ≤ k n) : a (k n) ≠ a (k n + (u0 n + v0 n)) := by
    intro heq
    refine Nat.find_min (hex n) (show k n - 1 < k n by omega) fun m hm1 hm2 ↦ ?_
    rcases (show m = k n ∨ k n < m by omega) with rfl | hm
    · exact heq.symm
    · exact hk n m hm (by omega)
  -- the normalized lengths, on the indices `n + 2`
  refine ⟨fun n ↦ if k (n + 2) = 0 then 1 else k (n + 2),
    fun n ↦ if k (n + 2) = 0 then u0 (n + 2) - 1 else u0 (n + 2),
    fun n ↦ if k (n + 2) = 0 then v0 (n + 2) + 1 else v0 (n + 2), 2 * C0 + 2,
    fun n m h1 h2 ↦ ?_, fun n ↦ ?_, fun n ↦ ?_, ?_, fun n h2 ↦ ?_⟩
  · have := hu0 (n + 2)
    split_ifs at h1 h2 ⊢ with h0
    · rw [show u0 (n + 2) - 1 + (v0 (n + 2) + 1) = u0 (n + 2) + v0 (n + 2) by omega]
      exact hk (n + 2) m (by omega) (by omega)
    · exact hk (n + 2) m h1 h2
  · split_ifs with h0 <;> omega
  · have hb := hbd (n + 2) (by omega)
    have := hu0 (n + 2)
    have hkw' := hkw (n + 2)
    split_ifs with h0
    · -- `v₀ + 2 ≤ C₀ u₀ + 2 ≤ (2 C₀ + 2) (u₀ - 1)` as `u₀ ≥ 2`
      have h3 : C0 * u0 (n + 2) ≤ 2 * C0 * (u0 (n + 2) - 1) :=
        calc C0 * u0 (n + 2) ≤ C0 * (2 * (u0 (n + 2) - 1)) := Nat.mul_le_mul_left _ (by omega)
          _ = 2 * C0 * (u0 (n + 2) - 1) := by ring
      have h4 : (2 * C0 + 2) * (u0 (n + 2) - 1) = 2 * C0 * (u0 (n + 2) - 1) +
          2 * (u0 (n + 2) - 1) := by ring
      omega
    · have h3 : C0 * u0 (n + 2) ≤ (2 * C0 + 2) * u0 (n + 2) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
  · refine tendsto_atTop_atTop.2 fun b ↦ ⟨b + 1, fun n hn ↦ ?_⟩
    have := hu0 (n + 2)
    split_ifs <;> omega
  · split_ifs at h2 ⊢ with h0
    · omega
    · exact hkne (n + 2) (by omega)

end Nat
