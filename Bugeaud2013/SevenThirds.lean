/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Theorem11

/-!
# `7/3`-powers in two-letter continued fractions (Bugeaud 2013, §6)

§6 of the paper remarks: "combining the arguments of [11] with Theorem 1.3, it is easy to prove
that if `1 ≤ m < M` are integers and `a = a₁ a₂ …` is a word over `{m, M}` such that
`[0; a₁, a₂, …]` is algebraic, then there are arbitrarily large (finite) blocks `U` such that
`U^{7/3}` occurs in `a`." Here [11] is Adamczewski–Rampersad, *On patterns occurring in binary
algebraic numbers*, Proc. AMS 136 (2008), whose theorem is that the binary expansion of an
algebraic number contains infinitely many occurrences of `7/3`-powers.

A `7/3`-power of period `p` is a word `U U U'` with `|U| = p` and `U'` the prefix of `U` of length
`⌈p/3⌉`, i.e. a factor of length `p + ⌈4p/3⌉ ≥ 7p/3` with period `p`.

The argument of [11], for a two-letter word `s` with no `7/3`-power at all:

1. `s` has no cube `xxx`, no `ababa`, and (by the cube and the power `baabaab`) no `aabaa`
   preceded by a letter. Hence the positions `i ≥ 1` with `s_i = s_{i+1}` all have the same
   parity, and `s = u μ(y)` with `|u| ≤ 5`, `μ` the Thue–Morse morphism `0 ↦ 01`, `1 ↦ 10`, and
   `y` again `7/3`-power-free (Restivo–Salemi, Karhumäki–Shallit; here `|u| ≤ 5` instead of
   `|u| ≤ 2`, which is all the argument needs).
2. Iterating, `s = u₀ μ(u₁) ⋯ μ^{k-1}(u_{k-1}) μ^k(y_k)`, and the first four letters of `y_k`
   contain a square `xx` with `|x| ∈ {1, 2}`. So `s` has a square `μ^k(x) μ^k(x)` of period
   `P ∈ [2^k, 2^{k+1}]` at a position `≤ 9 P`: Condition `(♠)` with `V` empty.
3. A word with no `7/3`-power is not eventually periodic, so Theorem 3.1 applies.

## Main definitions

* `Function.HasSevenThirdsPowerAt s i p`: `s` has a `7/3`-power of period `p` at position `i`.
* `Function.HasOverlapAt s i p`: `s` has an overlap `xXxXx` with `|xX| = p` at position `i`.
* `Function.IsSevenThirdsPowerFree s`: `s` has no `7/3`-power.

## Main results

* `Function.IsSevenThirdsPowerFree.exists_square`: a two-letter word with no `7/3`-power has, for
  every `k`, a square of period `P ≥ 2^k` at a position `≤ 9 P`.
* `Nat.transcendental_contFrac_of_eventually_sevenThirdsPowerFree`: if `a₁ a₂ …` takes two
  positive values and has only finitely many occurrences of `7/3`-powers, then `[0; a₁, a₂, …]`
  is transcendental.
* `Nat.frequently_hasSevenThirdsPowerAt`: **§6, the `7/3`-power remark**: if `a₁ a₂ …` takes
  two positive values and `[0; a₁, a₂, …]` is algebraic, then `7/3`-powers occur in `a` at
  infinitely many positions.
* `Nat.frequently_hasOverlapAt`: the same for overlaps.

## Implementation notes

⚠ **"Arbitrarily large blocks `U`" is weakened to "infinitely many occurrences".** The paper's
wording asks for `7/3`-powers `U^{7/3}` with `|U|` unbounded. The argument of [11] only rules out
a suffix with no `7/3`-power at all: step 1 uses the short powers `xxx`, `ababa`, `baabaab`, so it
says nothing about a word whose `7/3`-powers all have bounded period. The statement proved here
is the one of [11]: `7/3`-powers occur at infinitely many positions.

⚠ **Theorem 3.1 suffices.** The squares of step 2 are repetitions `W U U`, so only Condition
`(♠)` of Theorem 1.3 is used. The hypothesis `m < M` is not needed: for `m = M` the word is
constant.

The other remarks of §6 are not formalized: [17] (transcendence measures) is only cited, and the
bound (6.1) is announced without proof ("it seems to be possible"); it is proved in
`Bugeaud2013/Additions/`.
-/

@[expose] public section

open Filter

namespace Function

variable {α : Type*}

/-- `s` has a **`7/3`-power** of period `p` at position `i`: `s_{i+j} = s_{i+j+p}` for
`3 j < 4 p`, i.e. the factor of length `p + ⌈4p/3⌉ ≥ 7p/3` at `i` has period `p`. -/
def HasSevenThirdsPowerAt (s : ℕ → α) (i p : ℕ) : Prop :=
  1 ≤ p ∧ ∀ j, 3 * j < 4 * p → s (i + j) = s (i + j + p)

/-- `s` has an **overlap** `xXxXx` with `|xX| = p` at position `i`. -/
def HasOverlapAt (s : ℕ → α) (i p : ℕ) : Prop :=
  1 ≤ p ∧ ∀ j, j ≤ p → s (i + j) = s (i + j + p)

/-- `s` has no `7/3`-power. -/
def IsSevenThirdsPowerFree (s : ℕ → α) : Prop := ∀ i p, ¬ HasSevenThirdsPowerAt s i p

/-- A `7/3`-power contains an overlap. -/
theorem HasSevenThirdsPowerAt.hasOverlapAt {s : ℕ → α} {i p : ℕ}
    (h : HasSevenThirdsPowerAt s i p) : HasOverlapAt s i p :=
  ⟨h.1, fun j hj ↦ h.2 j (by have := h.1; omega)⟩

/-- An eventually periodic word has `7/3`-powers arbitrarily far out. -/
theorem IsEventuallyPeriodic.exists_hasSevenThirdsPowerAt {s : ℕ → α}
    (h : IsEventuallyPeriodic s) (N : ℕ) : ∃ i, N ≤ i ∧ ∃ p, HasSevenThirdsPowerAt s i p := by
  obtain ⟨N', p, hp, hper⟩ := h
  exact ⟨max N N', le_max_left _ _, p, hp, fun j _ ↦ (hper _ (by omega)).symm⟩

section Binary

variable {s : ℕ → Bool}

private theorem bool_eq_of_ne_of_ne {x y z : Bool} (h₁ : x ≠ y) (h₂ : y ≠ z) : x = z := by
  revert x y z
  decide

private theorem bool_eq_of_ne_of_ne_of_eq {x y x' y' : Bool} (h : x ≠ y) (h' : x' ≠ y')
    (he : x = x') : y = y' := by
  revert x y x' y'
  decide

variable (hs : IsSevenThirdsPowerFree s)
include hs

/-- No cube `xxx`. -/
theorem IsSevenThirdsPowerFree.not_cube (i : ℕ) (h₁ : s i = s (i + 1))
    (h₂ : s (i + 1) = s (i + 2)) : False :=
  hs i 1 ⟨le_rfl, fun j hj ↦ by
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · exact h₁
    · exact h₂⟩

/-- No `ababa`. -/
theorem IsSevenThirdsPowerFree.not_alternating (i : ℕ) (h₁ : s i ≠ s (i + 1))
    (h₂ : s (i + 1) ≠ s (i + 2)) (h₃ : s (i + 2) ≠ s (i + 3)) (h₄ : s (i + 3) ≠ s (i + 4)) :
    False :=
  hs i 2 ⟨by norm_num, fun j hj ↦ by
    obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    · exact bool_eq_of_ne_of_ne h₁ h₂
    · exact bool_eq_of_ne_of_ne h₂ h₃
    · exact bool_eq_of_ne_of_ne h₃ h₄⟩

/-- No `aabaa` preceded by a letter: `xaabaay` contains `aaa` or the `7/3`-power `baabaab`. -/
theorem IsSevenThirdsPowerFree.not_sq_three (i : ℕ) (h₁ : s (i + 1) = s (i + 2))
    (h₂ : s (i + 4) = s (i + 5)) : False := by
  have key : ∀ x₀ x₁ x₂ x₃ x₄ x₅ x₆ : Bool, x₁ = x₂ → x₄ = x₅ → ¬ (x₀ = x₁ ∧ x₁ = x₂) →
      ¬ (x₁ = x₂ ∧ x₂ = x₃) → ¬ (x₂ = x₃ ∧ x₃ = x₄) → ¬ (x₃ = x₄ ∧ x₄ = x₅) →
      ¬ (x₄ = x₅ ∧ x₅ = x₆) → ¬ (x₀ = x₃ ∧ x₁ = x₄ ∧ x₂ = x₅ ∧ x₃ = x₆) → False := by
    intro x₀ x₁ x₂ x₃ x₄ x₅ x₆
    cases x₀ <;> cases x₁ <;> cases x₂ <;> cases x₃ <;> cases x₄ <;> cases x₅ <;> cases x₆ <;>
      simp
  refine key (s i) (s (i + 1)) (s (i + 2)) (s (i + 3)) (s (i + 4)) (s (i + 5)) (s (i + 6)) h₁ h₂
    (fun h ↦ hs.not_cube i h.1 h.2) (fun h ↦ hs.not_cube (i + 1) h.1 h.2)
    (fun h ↦ hs.not_cube (i + 2) h.1 h.2) (fun h ↦ hs.not_cube (i + 3) h.1 h.2)
    (fun h ↦ hs.not_cube (i + 4) h.1 h.2) fun h ↦ hs i 3 ⟨by norm_num, fun j hj ↦ ?_⟩
  obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  exacts [h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- **The squares `s_i = s_{i+1}` at positions `i ≥ 1` all have the same parity.** -/
theorem IsSevenThirdsPowerFree.even_of_sq (d : ℕ) :
    ∀ i, s (i + 1) = s (i + 2) → s (i + 1 + d) = s (i + 2 + d) → d % 2 = 0 := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro i h₁ h₂
  by_contra hd
  rcases (show d = 1 ∨ d = 3 ∨ 5 ≤ d by omega) with rfl | rfl | h5
  · exact hs.not_cube (i + 1) h₁ h₂
  · exact hs.not_sq_three i h₁ h₂
  · -- the next square, at `i + 1 + l` with `1 ≤ l ≤ 4`, splits `d` into two shorter distances
    obtain ⟨l, hl1, hl4, hl⟩ : ∃ l, 1 ≤ l ∧ l ≤ 4 ∧ s (i + 1 + l) = s (i + 2 + l) := by
      by_contra hne
      push Not at hne
      exact hs.not_alternating (i + 2) (hne 1 le_rfl (by norm_num))
        (hne 2 (by norm_num) (by norm_num)) (hne 3 (by norm_num) (by norm_num))
        (hne 4 (by norm_num) le_rfl)
    by_cases hl2 : l % 2 = 0
    · have := ih (d - l) (by omega) (i + l)
        (by rw [show i + l + 1 = i + 1 + l by omega, show i + l + 2 = i + 2 + l by omega]; exact hl)
        (by
          rw [show i + l + 1 + (d - l) = i + 1 + d by omega,
            show i + l + 2 + (d - l) = i + 2 + d by omega]
          exact h₂)
      omega
    · exact hl2 (ih l (by omega) i h₁ hl)

/-- **Desubstitution**: `s = u μ(y)` with `|u| ≤ 5`, i.e. the blocks `s_{c+2k} s_{c+2k+1}` are
`01` or `10`. -/
theorem IsSevenThirdsPowerFree.exists_desubst :
    ∃ c, c ≤ 5 ∧ ∀ k, s (c + 2 * k) ≠ s (c + 2 * k + 1) := by
  obtain ⟨l, hl, hsq⟩ : ∃ l, l ≤ 3 ∧ s (l + 1) = s (l + 2) := by
    by_contra hne
    push Not at hne
    exact hs.not_alternating 1 (hne 0 (by norm_num)) (hne 1 (by norm_num)) (hne 2 (by norm_num))
      (hne 3 le_rfl)
  refine ⟨l + 2, by omega, fun k hk ↦ ?_⟩
  have := hs.even_of_sq (2 * k + 1) l hsq (by
    rw [show l + 1 + (2 * k + 1) = l + 2 + 2 * k by omega,
      show l + 2 + (2 * k + 1) = l + 2 + 2 * k + 1 by omega]
    exact hk)
  omega

/-- **The desubstituted word `y` has no `7/3`-power**: a `7/3`-power of period `p` in `y` is one
of period `2p` in `μ(y)`. -/
theorem IsSevenThirdsPowerFree.desubst {c : ℕ} (hc : ∀ k, s (c + 2 * k) ≠ s (c + 2 * k + 1)) :
    IsSevenThirdsPowerFree fun k ↦ s (c + 2 * k) := by
  rintro i p ⟨hp, h⟩
  refine hs (c + 2 * i) (2 * p) ⟨by omega, fun j hj ↦ ?_⟩
  obtain ⟨q, rfl | rfl⟩ : ∃ q, j = 2 * q ∨ j = 2 * q + 1 := ⟨j / 2, by omega⟩
  · have : s (c + 2 * (i + q)) = s (c + 2 * (i + q + p)) := h q (by omega)
    rw [show c + 2 * i + 2 * q = c + 2 * (i + q) by ring,
      show c + 2 * (i + q) + 2 * p = c + 2 * (i + q + p) by ring]
    exact this
  · have : s (c + 2 * (i + q)) = s (c + 2 * (i + q + p)) := h q (by omega)
    rw [show c + 2 * i + (2 * q + 1) = c + 2 * (i + q) + 1 by ring,
      show c + 2 * (i + q) + 1 + 2 * p = c + 2 * (i + q + p) + 1 by ring]
    exact bool_eq_of_ne_of_ne_of_eq (hc _) (hc _) this

/-- **Iterated desubstitution**: `s = u₀ μ(u₁) ⋯ μ^{k-1}(u_{k-1}) μ^k(t)` with `t` free of
`7/3`-powers; equal letters of `t` give equal blocks of length `2^k` in `s`. -/
theorem IsSevenThirdsPowerFree.exists_blocks (k : ℕ) :
    ∃ T, T ≤ 5 * 2 ^ k ∧ ∃ t : ℕ → Bool, IsSevenThirdsPowerFree t ∧
      ∀ i i', t i = t i' → ∀ r, r < 2 ^ k → s (T + 2 ^ k * i + r) = s (T + 2 ^ k * i' + r) := by
  induction k with
  | zero =>
    refine ⟨0, by norm_num, s, hs, fun i i' h r hr ↦ ?_⟩
    obtain rfl : r = 0 := by omega
    simpa using h
  | succ k ih =>
    obtain ⟨T, hT, t, ht, hblk⟩ := ih
    obtain ⟨c, hc5, hc⟩ := ht.exists_desubst
    refine ⟨T + 2 ^ k * c, ?_, fun i ↦ t (c + 2 * i), ht.desubst hc, fun i i' h r hr ↦ ?_⟩
    · rw [pow_succ]
      nlinarith [Nat.mul_le_mul_left (2 ^ k) hc5]
    · have h2k : 0 < 2 ^ k := by positivity
      obtain ⟨e, r₀, hr₀, he, rfl⟩ : ∃ e r₀, r₀ < 2 ^ k ∧ e < 2 ∧ r = 2 ^ k * e + r₀ := by
        refine ⟨r / 2 ^ k, r % 2 ^ k, Nat.mod_lt _ h2k, ?_, (Nat.div_add_mod r _).symm⟩
        rw [Nat.div_lt_iff_lt_mul h2k]
        rw [pow_succ] at hr
        linarith
      have hte : t (c + 2 * i + e) = t (c + 2 * i' + e) := by
        obtain rfl | rfl : e = 0 ∨ e = 1 := by omega
        · exact h
        · exact bool_eq_of_ne_of_ne_of_eq (hc i) (hc i') h
      have := hblk _ _ hte r₀ hr₀
      rw [show T + 2 ^ k * c + 2 ^ (k + 1) * i + (2 ^ k * e + r₀) =
          T + 2 ^ k * (c + 2 * i + e) + r₀ by ring,
        show T + 2 ^ k * c + 2 ^ (k + 1) * i' + (2 ^ k * e + r₀) =
          T + 2 ^ k * (c + 2 * i' + e) + r₀ by ring]
      exact this

/-- **Squares from desubstitution**: for every `k`, `s` has a square of period `P ≥ 2^k` at a
position `R ≤ 9 P`. -/
theorem IsSevenThirdsPowerFree.exists_square (k : ℕ) :
    ∃ R P, 2 ^ k ≤ P ∧ R ≤ 9 * P ∧ ∀ x, R ≤ x → x < R + P → s (x + P) = s x := by
  obtain ⟨T, hT, t, -, hblk⟩ := hs.exists_blocks k
  -- a square of period `p ∈ {1, 2}` among the first four letters of `t`
  obtain ⟨i₀, p, hp, hip, hsq⟩ : ∃ i₀ p, 1 ≤ p ∧ i₀ + 2 * p ≤ 4 ∧
      ∀ j, j < p → t (i₀ + j + p) = t (i₀ + j) := by
    by_cases h₀ : t 0 = t 1
    · exact ⟨0, 1, le_rfl, by norm_num, fun j hj ↦ by
        obtain rfl : j = 0 := by omega
        exact h₀.symm⟩
    by_cases h₁ : t 1 = t 2
    · exact ⟨1, 1, le_rfl, by norm_num, fun j hj ↦ by
        obtain rfl : j = 0 := by omega
        exact h₁.symm⟩
    by_cases h₂ : t 2 = t 3
    · exact ⟨2, 1, le_rfl, by norm_num, fun j hj ↦ by
        obtain rfl : j = 0 := by omega
        exact h₂.symm⟩
    refine ⟨0, 2, by norm_num, by norm_num, fun j hj ↦ ?_⟩
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · exact (bool_eq_of_ne_of_ne h₀ h₁).symm
    · exact (bool_eq_of_ne_of_ne h₁ h₂).symm
  have h2k : 0 < 2 ^ k := by positivity
  refine ⟨T + 2 ^ k * i₀, 2 ^ k * p, Nat.le_mul_of_pos_right _ hp, ?_, fun x hx₁ hx₂ ↦ ?_⟩
  · nlinarith [Nat.mul_le_mul_left (2 ^ k) hp, Nat.mul_le_mul_left (2 ^ k) hip]
  · obtain ⟨y, rfl⟩ : ∃ y, x = T + 2 ^ k * i₀ + y := ⟨x - (T + 2 ^ k * i₀), by omega⟩
    have hy : y < p * 2 ^ k := by linarith
    have hq : y / 2 ^ k < p := (Nat.div_lt_iff_lt_mul h2k).mpr hy
    have := hblk _ _ (hsq _ hq) (y % 2 ^ k) (Nat.mod_lt _ h2k)
    rw [← Nat.div_add_mod y (2 ^ k)]
    rw [show T + 2 ^ k * i₀ + (2 ^ k * (y / 2 ^ k) + y % 2 ^ k) + 2 ^ k * p =
        T + 2 ^ k * (i₀ + y / 2 ^ k + p) + y % 2 ^ k by ring,
      show T + 2 ^ k * i₀ + (2 ^ k * (y / 2 ^ k) + y % 2 ^ k) =
        T + 2 ^ k * (i₀ + y / 2 ^ k) + y % 2 ^ k by ring]
    exact this

end Binary

end Function

namespace Nat

variable {a : ℕ → ℕ}

section Positive

variable (ha : ∀ n, 1 ≤ a (n + 1))
include ha

/-- **Two-letter continued fractions with finitely many `7/3`-powers are transcendental**
(Adamczewski–Rampersad 2008, for continued fractions; Bugeaud 2013, §6). If `a₁ a₂ …` takes the
two positive values `m`, `M` and has `7/3`-powers at only finitely many positions, then
`[0; a₁, a₂, …]` is transcendental. -/
theorem transcendental_contFrac_of_eventually_sevenThirdsPowerFree {m M : ℕ}
    (hmM : ∀ n, a (n + 1) = m ∨ a (n + 1) = M)
    (hfree : ∀ᶠ i in atTop, ∀ p, ¬ Function.HasSevenThirdsPowerAt (fun k ↦ a (k + 1)) i p) :
    Transcendental ℚ (contFrac a) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfree
  -- two letters: `a_x = a_y` iff both are `M` or both are not
  have hval (x y : ℕ) (h : decide (a (x + 1) = M) = decide (a (y + 1) = M)) :
      a (x + 1) = a (y + 1) := by
    rcases hmM x with hx | hx <;> rcases hmM y with hy | hy <;> simp_all
  -- the suffix `a_{N+1} a_{N+2} …` as a word over `Bool`
  set s : ℕ → Bool := fun k ↦ decide (a (N + k + 1) = M) with hs_def
  have hs : Function.IsSevenThirdsPowerFree s := by
    rintro i p ⟨hp, h⟩
    refine hN (N + i) (Nat.le_add_right _ _) p ⟨hp, fun j hj ↦ ?_⟩
    have := hval (N + (i + j)) (N + (i + j + p)) (h j hj)
    change a (N + i + j + 1) = a (N + i + j + p + 1)
    rw [show N + i + j = N + (i + j) by ring, show N + (i + j) + p = N + (i + j + p) by ring]
    exact this
  choose R P hP hR hper using hs.exists_square
  have hP1 (k : ℕ) : 1 ≤ P k := Nat.one_le_two_pow.trans (hP k)
  have hspade : Function.HasSpadeRepetitions fun k ↦ a (k + 1) := by
    refine Function.hasSpadeRepetitions_of_periodic (w := 2) (C' := N + 9)
      (r := fun k ↦ N + R k) (s := P) one_lt_two ?_ hP1 (fun k ↦ ?_) (fun k i h₁ h₂ ↦ ?_)
    · exact tendsto_atTop_mono (fun k ↦ (Nat.lt_two_pow_self).le.trans (hP k)) tendsto_id
    · have h : N + R k ≤ (N + 9) * P k := by nlinarith [hR k, hP1 k]
      exact_mod_cast h
    · have hc : ⌈(2 : ℝ) * (P k : ℝ)⌉₊ = 2 * P k := by
        rw [show (2 : ℝ) * (P k : ℝ) = ((2 * P k : ℕ) : ℝ) by push_cast; ring, Nat.ceil_natCast]
      rw [hc] at h₂
      obtain ⟨y, rfl⟩ : ∃ y, i = N + y := ⟨i - N, by omega⟩
      have := hval (N + (y + P k)) (N + y) (hper k y (by omega) (by omega))
      change a (N + y + P k + 1) = a (N + y + 1)
      rw [show N + y + P k = N + (y + P k) by ring]
      exact this
  have hnp : ¬ Function.IsEventuallyPeriodic fun k ↦ a (k + 1) := fun hp ↦ by
    obtain ⟨i, hi, p, hpw⟩ := hp.exists_hasSevenThirdsPowerAt N
    exact hN i hi p hpw
  have hM (n : ℕ) : a (n + 1) ≤ max m M := by
    rcases hmM n with h | h <;> simp [h]
  exact transcendental_contFrac_of_isSpade ha (bddAbove_contDen_rpow ha hM) ⟨hnp, hspade⟩

/-- **Bugeaud 2013, §6 (the `7/3`-power remark).** If `a₁ a₂ …` takes the two positive values
`m`, `M` and `[0; a₁, a₂, …]` is algebraic, then `7/3`-powers occur in `a` at infinitely many
positions. -/
theorem frequently_hasSevenThirdsPowerAt {m M : ℕ} (hmM : ∀ n, a (n + 1) = m ∨ a (n + 1) = M)
    (halg : IsAlgebraic ℚ (contFrac a)) :
    ∃ᶠ i in atTop, ∃ p, Function.HasSevenThirdsPowerAt (fun k ↦ a (k + 1)) i p := by
  by_contra hfr
  refine transcendental_contFrac_of_eventually_sevenThirdsPowerFree ha hmM ?_ halg
  exact (not_frequently.mp hfr).mono fun i hi p hp ↦ hi ⟨p, hp⟩

/-- **Overlaps** (Adamczewski–Rampersad 2008, for continued fractions): if `a₁ a₂ …` takes the two
positive values `m`, `M` and `[0; a₁, a₂, …]` is algebraic, then overlaps occur in `a` at
infinitely many positions. -/
theorem frequently_hasOverlapAt {m M : ℕ} (hmM : ∀ n, a (n + 1) = m ∨ a (n + 1) = M)
    (halg : IsAlgebraic ℚ (contFrac a)) :
    ∃ᶠ i in atTop, ∃ p, Function.HasOverlapAt (fun k ↦ a (k + 1)) i p :=
  (frequently_hasSevenThirdsPowerAt ha hmM halg).mono fun _ ⟨p, hp⟩ ↦ ⟨p, hp.hasOverlapAt⟩

end Positive

end Nat
