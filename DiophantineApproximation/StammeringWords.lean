/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Data.List.Infix
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Bounds.Defs

/-!
# Stammering sequences

**Layer 7.4, the words** (Adamczewski–Bugeaud–Luca 2004; Adamczewski–Bugeaud 2007, §4). For a
finite word `V` and real `w ≥ 1`, the word `V ^ w` is `V` repeated `⌊w⌋` times followed by the
prefix of `V` of length `⌈(w - ⌊w⌋) |V|⌉`. A sequence `a` is **stammering** if for some `w > 1`
there are finite words `U k`, `V k` with `U k (V k) ^ w` a prefix of `a`, `|U k| / |V k|` bounded
and `|V k|` strictly increasing. This file states the definitions and converts them into the
statement about periods that the transcendence proofs use.

## Main definitions

* `List.rpow`: `V ^ w` for a finite word `V` and real `w`.
* `Function.IsEventuallyPeriodic`: a sequence with a period from some index on.
* `Function.IsStammeringWith`: Condition `(∗)_w`.
* `Function.IsStammering`: Condition `(∗)_w` for some `w > 1`.

## Main results

* `List.length_rpow`: `|V ^ w| = ⌈w |V|⌉`.
* `List.rpow_prefix_append`: `V ^ w` is a prefix of `V ++ V ^ w`.
* `List.getElem?_rpow`: the `j`-th letter of `V ^ w` is the `(j mod |V|)`-th letter of `V`.
* `Function.IsStammeringWith.exists_periodic`: the segment of `a` of length `⌈w |V k|⌉` after
  position `|U k|` has period `|V k|`.
* `Function.isStammeringWith_of_periodic`: the converse.

## Implementation notes

⚠ **Only the lengths survive.** Once `U k (V k) ^ w` is known to be a prefix of `a`, the words are
determined by their lengths and by `a`; everything the transcendence criteria use is the pair
`r k = |U k|`, `s k = |V k|` and the periodicity of `a` on `[r k, r k + ⌈w s k⌉)`. That is
`IsStammeringWith.exists_periodic`, and it is the shape of Condition `(∗)_w` in which the
criterion is proved.

⚠ **The fractional power has the expected length, and no more.** `⌈(w - ⌊w⌋) |V|⌉ ≤ |V|` because
`w - ⌊w⌋ < 1`, so the `List.take` never runs out and `|V ^ w| = ⌊w⌋ |V| + ⌈(w - ⌊w⌋) |V|⌉ =
⌈w |V|⌉`.

## References

B. Adamczewski, Y. Bugeaud and F. Luca, *Sur la complexité des nombres algébriques*, C. R. Acad.
Sci. Paris **339** (2004), 11–14; B. Adamczewski and Y. Bugeaud, *On the complexity of algebraic
numbers I. Expansions in integer bases*, Annals of Mathematics **165** (2007), 547–565.

This is part of Layer 7.4 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

namespace List

variable {α : Type*}

/-- **The `w`-th power of a finite word**, for real `w ≥ 0`: `V` repeated `⌊w⌋` times, followed
by the prefix of `V` of length `⌈(w - ⌊w⌋) |V|⌉`. Its length is `⌈w |V|⌉`
(`List.length_rpow`). -/
noncomputable def rpow (V : List α) (w : ℝ) : List α :=
  (replicate ⌊w⌋₊ V).flatten ++ V.take ⌈(w - ⌊w⌋₊) * V.length⌉₊

/-- The length of `V ^ w` is `⌈w |V|⌉`: the fractional part of `w` never asks for more than one
copy of `V`. -/
theorem length_rpow (V : List α) {w : ℝ} (hw : 0 ≤ w) :
    (V.rpow w).length = ⌈w * V.length⌉₊ := by
  have hfrac : w - ⌊w⌋₊ < 1 := by linarith [Nat.lt_floor_add_one w]
  have hfrac0 : 0 ≤ w - ⌊w⌋₊ := by linarith [Nat.floor_le hw]
  have hle : ⌈(w - ⌊w⌋₊) * V.length⌉₊ ≤ V.length :=
    Nat.ceil_le.mpr (by nlinarith [(Nat.cast_nonneg V.length : (0 : ℝ) ≤ V.length)])
  have hsplit : w * V.length = (w - ⌊w⌋₊) * V.length + ((⌊w⌋₊ * V.length : ℕ) : ℝ) := by
    push_cast; ring
  rw [rpow, length_append, length_take, min_eq_left hle, hsplit,
    Nat.ceil_add_natCast (mul_nonneg hfrac0 (Nat.cast_nonneg _))]
  simp [length_flatten, add_comm]

/-- **`V ^ w` has period `|V|`**, in the form the proofs use: it is a prefix of `V ++ V ^ w`. -/
theorem rpow_prefix_append (V : List α) (w : ℝ) : V.rpow w <+: V ++ V.rpow w := by
  have hcomm : V ++ (replicate ⌊w⌋₊ V).flatten = (replicate ⌊w⌋₊ V).flatten ++ V := by
    rw [← flatten_cons, ← replicate_succ, replicate_succ', flatten_append, flatten_singleton]
  rw [rpow, ← append_assoc, hcomm, append_assoc]
  exact prefix_append_right_inj _ |>.mpr ((take_prefix _ _).trans (prefix_append _ _))

/-- **The letters of `V ^ w`**: the `j`-th letter is the `(j mod |V|)`-th letter of `V`. -/
theorem getElem?_rpow (V : List α) (w : ℝ) :
    ∀ j < (V.rpow w).length, (V.rpow w)[j]? = V[j % V.length]? := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    obtain ⟨t, ht⟩ := rpow_prefix_append V w
    have hpre : (V.rpow w)[j]? = (V ++ V.rpow w)[j]? := by
      rw [← ht, getElem?_append_left hj]
    have hV0 : 0 < V.length := by
      rcases Nat.eq_zero_or_pos V.length with h | h
      · rw [length_eq_zero_iff.mp h] at hj
        simp [rpow] at hj
      · exact h
    rw [hpre]
    by_cases hjV : j < V.length
    · rw [getElem?_append_left hjV, Nat.mod_eq_of_lt hjV]
    · push Not at hjV
      rw [getElem?_append_right hjV, ih (j - V.length) (by omega) (by omega),
        Nat.mod_eq_sub_mod hjV]

end List

namespace Function

variable {α : Type*}

/-- A sequence is **eventually periodic** if it has a period `p > 0` from some index `N` on. -/
def IsEventuallyPeriodic (a : ℕ → α) : Prop :=
  ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n → a (n + p) = a n

/-- **Condition `(∗)_w`** (Adamczewski–Bugeaud 2007, §4). There are finite words `U k`, `V k`
with `U k (V k)^w` a prefix of `a`, the ratio `|U k| / |V k|` bounded, and `|V k|` strictly
increasing. -/
def IsStammeringWith (w : ℝ) (a : ℕ → α) : Prop :=
  ∃ U V : ℕ → List α,
    (∀ k i, i < (U k ++ (V k).rpow w).length → (U k ++ (V k).rpow w)[i]? = some (a i)) ∧
    BddAbove (Set.range fun k ↦ ((U k).length : ℝ) / (V k).length) ∧
    StrictMono fun k ↦ (V k).length

/-- A sequence is **stammering** if it satisfies Condition `(∗)_w` for some `w > 1`. -/
def IsStammering (a : ℕ → α) : Prop := ∃ w : ℝ, 1 < w ∧ IsStammeringWith w a

/-- **The working form of Condition `(∗)_w`.** A repetition `U V^w` at the start of `a` says that
the segment of `a` of length `⌈w |V|⌉` starting at position `|U|` has period `|V|`. The sequences
are reindexed from `k + 1` so that `|V k| ≥ 1`, which turns the bounded ratio into
`|U k| ≤ C |V k|`. -/
theorem IsStammeringWith.exists_periodic {w : ℝ} {a : ℕ → α} (hw : 0 ≤ w)
    (h : IsStammeringWith w a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r s : ℕ → ℕ, StrictMono s ∧ (∀ k, 1 ≤ s k) ∧
      (∀ k, (r k : ℝ) ≤ C * s k) ∧
      ∀ k i, r k ≤ i → i + s k < r k + ⌈w * s k⌉₊ → a (i + s k) = a i := by
  obtain ⟨U, V, hpre, ⟨C, hC⟩, hmono⟩ := h
  refine ⟨max C 0, le_max_right _ _, fun k ↦ (U (k + 1)).length, fun k ↦ (V (k + 1)).length,
    fun i j hij ↦ hmono (Nat.succ_lt_succ hij), fun k ↦ ?_, fun k ↦ ?_, fun k i hi hi' ↦ ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
      (lt_of_le_of_lt (Nat.zero_le _) (hmono (Nat.succ_pos k))))
  · have hs : (0 : ℝ) < (V (k + 1)).length := by
      exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) (hmono (Nat.succ_pos k))
    have hk := hC ⟨k + 1, rfl⟩
    rw [div_le_iff₀ hs] at hk
    exact hk.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hs.le)
  · beta_reduce at hi hi' ⊢
    have hp := hpre (k + 1)
    set Uk := U (k + 1)
    set Vk := V (k + 1)
    set W := Vk.rpow w
    have hlen : W.length = ⌈w * Vk.length⌉₊ := List.length_rpow Vk hw
    have h1 : (Uk ++ W)[i + Vk.length]? = some (a (i + Vk.length)) :=
      hp (i + Vk.length) (by rw [List.length_append]; omega)
    have h2 : (Uk ++ W)[i]? = some (a i) := hp i (by rw [List.length_append]; omega)
    rw [List.getElem?_append_right (by omega)] at h1 h2
    have hidx : i + Vk.length - Uk.length < W.length := by omega
    have hW := (List.rpow_prefix_append Vk w)
    obtain ⟨t, ht⟩ := hW
    have h3 : W[i + Vk.length - Uk.length]? = (Vk ++ W)[i + Vk.length - Uk.length]? := by
      rw [← ht, List.getElem?_append_left hidx]
    rw [List.getElem?_append_right (by omega),
      show i + Vk.length - Uk.length - Vk.length = i - Uk.length by omega] at h3
    rw [h3] at h1
    rw [h1] at h2
    exact Option.some_injective _ h2

/-- **The converse of `IsStammeringWith.exists_periodic`**: periodic segments of lengths
`⌈w s k⌉` after positions `r k`, with `s` strictly increasing, positive, and `r k ≤ C s k`, give
Condition `(∗)_w`, with `U k` the first `r k` letters of `a` and `V k` the next `s k`. -/
theorem isStammeringWith_of_periodic {w C : ℝ} (hw : 0 ≤ w) {a : ℕ → α} {r s : ℕ → ℕ}
    (hs : StrictMono s) (hs1 : ∀ k, 1 ≤ s k) (hrs : ∀ k, (r k : ℝ) ≤ C * s k)
    (hper : ∀ k i, r k ≤ i → i + s k < r k + ⌈w * s k⌉₊ → a (i + s k) = a i) :
    IsStammeringWith w a := by
  set U : ℕ → List α := fun k ↦ (List.range (r k)).map a with hU
  set V : ℕ → List α := fun k ↦ (List.range (s k)).map (fun i ↦ a (r k + i)) with hV
  have hUl : ∀ k, (U k).length = r k := fun k ↦ by simp [hU]
  have hVl : ∀ k, (V k).length = s k := fun k ↦ by simp [hV]
  refine ⟨U, V, fun k i hi ↦ ?_, ⟨C, ?_⟩, ?_⟩
  · rw [List.length_append, List.length_rpow _ hw, hUl, hVl] at hi
    by_cases hir : i < r k
    · rw [List.getElem?_append_left (by rwa [hUl])]
      simp [hU, hir]
    · push Not at hir
      rw [List.getElem?_append_right (by rwa [hUl]), hUl,
        List.getElem?_rpow _ _ _ (by rw [List.length_rpow _ hw, hVl]; omega), hVl]
      have hmod : (i - r k) % s k < s k := Nat.mod_lt _ (hs1 k)
      simp only [hV, List.getElem?_map, List.getElem?_range hmod, Option.map_some]
      -- the periodicity, one period at a time
      have key : ∀ j, j < ⌈w * s k⌉₊ → a (r k + j % s k) = a (r k + j) := by
        intro j
        induction j using Nat.strong_induction_on with
        | _ j ih =>
          intro hj
          by_cases hjs : j < s k
          · rw [Nat.mod_eq_of_lt hjs]
          · push Not at hjs
            rw [Nat.mod_eq_sub_mod hjs, ih (j - s k) (by have := hs1 k; omega) (by omega),
              ← hper k (r k + (j - s k)) (by omega) (by omega)]
            congr 1
            omega
      rw [key (i - r k) (by omega)]
      congr 2
      omega
  · rintro _ ⟨k, rfl⟩
    have hs0 : (0 : ℝ) < s k := by exact_mod_cast hs1 k
    simp only [hUl, hVl]
    rw [div_le_iff₀ hs0]
    exact hrs k
  · simpa [hVl] using hs

end Function

/-! ### Acceptance criteria -/

/-- **Conformance: `(1 2 3) ^ (5 / 3) = 1 2 3 1 2`**, the example of a fractional power of a word
in Adamczewski–Bugeaud. -/
example : [1, 2, 3].rpow (5 / 3 : ℝ) = [1, 2, 3, 1, 2] := by
  have h1 : ⌊(5 / 3 : ℝ)⌋₊ = 1 := by rw [Nat.floor_eq_iff (by norm_num)]; norm_num
  have h2 : ⌈((5 / 3 : ℝ) - ((1 : ℕ) : ℝ)) * (([1, 2, 3] : List ℕ).length : ℝ)⌉₊ = 2 := by
    rw [show ((5 / 3 : ℝ) - ((1 : ℕ) : ℝ)) * (([1, 2, 3] : List ℕ).length : ℝ) = ((2 : ℕ) : ℝ) by
      norm_num, Nat.ceil_natCast]
  rw [List.rpow, h1, h2]
  rfl

/-- **Conformance: the length of `V ^ w` is `⌈w |V|⌉`**, here `⌈(5 / 3) · 3⌉ = 5`. -/
example : ([1, 2, 3].rpow (5 / 3 : ℝ)).length = 5 := by
  rw [List.length_rpow _ (by norm_num)]
  rw [show (5 / 3 : ℝ) * (([1, 2, 3] : List ℕ).length : ℝ) = ((5 : ℕ) : ℝ) by norm_num,
    Nat.ceil_natCast]

