/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.StammeringWords
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic

-- Used only inside proofs.
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.TFAE

/-!
# The factor complexity of a sequence

**Layer 7.5, the combinatorics** (Morse–Hedlund 1938; Adamczewski–Bugeaud 2007, §4). For a
sequence `a` over a finite alphabet, the **complexity** `p n` is the number of distinct words of
length `n` occurring in `a`. It is nondecreasing, and `a` is eventually periodic if and only if
`p` is bounded, if and only if `p n ≤ n` for some `n` (Morse–Hedlund). And if `p n ≤ C n` for
infinitely many `n`, then `a` is stammering: of the `p n + 1` factors of length `n` at the first
`p n + 1` positions two coincide, and the repetition they make is long enough. Nothing here refers
to a number; Layer 7.4's criterion turns the last statement into the complexity of an algebraic
irrational, in `DiophantineApproximation/ComplexityTranscendence.lean`.

## Main definitions

* `Function.factor a i n`: the word `a i, …, a (i + n - 1)`.
* `Function.factors a n`: the set of words of length `n` occurring in `a`.
* `Function.complexity a n`: their number.

## Main results

* `Function.complexity_mono`: `p` is nondecreasing.
* `Function.isEventuallyPeriodic_tfae`: **Morse–Hedlund** — eventually periodic, `p` bounded, and
  `p n ≤ n` for some `n` are equivalent.
* `Function.lt_complexity`: a sequence that is not eventually periodic has `p n ≥ n + 1`.
* `Function.isStammering_of_frequently_complexity_le`: **the combinatorial lemma** — `p n ≤ C n`
  for infinitely many `n` makes `a` stammering.
* `Function.exists_periodic_of_frequently_complexity_le`: the same, with the repetitions in the
  working form of Layer 7.4 and `w = 1 + 1 / (1 + 2 ⌈C⌉)`.

## Implementation notes

⚠ **The repetition the pigeonhole gives has to be re-cut.** Two equal factors of length `n` at
positions `r < t ≤ C n` say that `a` has period `s = t - r` on a segment of length `n + s`. When
`s` is small against `n` that is a large power of a short word, and `|U| / |V| = r / s` is
unbounded; the classical proof splits into cases. Here the period is always replaced by the
multiple `P = (⌊n / 2 s⌋ + 1) s`, which lies in `(n / 2, n / 2 + s]`: then `|U| / |V| ≤ 2 C`, and
`s ≤ C n` makes the segment of length `n + s` at least `(1 + 1 / (1 + 2 C)) P`, uniformly.

⚠ **Morse–Hedlund needs a single `m` with `p (m + 1) = p m`**, which `p n ≤ n` and `p 0 = 1`
force below `n`. Then every factor of length `m` has exactly one extension to the right
(`Set.injOn_of_ncard_image_eq`: `List.take m` maps the factors of length `m + 1` onto those of
length `m`), so the factor at `i + 1` is a function of the factor at `i`, and two equal factors
make the sequence periodic from the first of them on.

⚠ **The alphabet must be finite.** Over `ℕ` the identity has infinitely many factors of length
`1`, and `Set.ncard` of an infinite set is `0`: then `p 1 = 0 < 1 = p 0`
(`complexity_id_one`, below).

## References

M. Morse and G. A. Hedlund, *Symbolic dynamics*, Amer. J. Math. **60** (1938), 815–866;
B. Adamczewski and Y. Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer
bases*, Annals of Mathematics **165** (2007), 547–565.

This is part of Layer 7.5 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Filter

namespace Function

variable {α : Type*}

/-- The **factor** of `a` of length `n` at position `i`: the word `a i, …, a (i + n - 1)`. -/
def factor (a : ℕ → α) (i n : ℕ) : List α := List.ofFn fun j : Fin n ↦ a (i + j)

/-- The set of words of length `n` occurring in `a`. -/
def factors (a : ℕ → α) (n : ℕ) : Set (List α) := Set.range fun i ↦ factor a i n

/-- The **complexity** `p n` of `a`: the number of distinct words of length `n` occurring in `a`.
It is meaningful for a finite alphabet (`Function.finite_factors`); over an infinite one `Set.ncard`
may return its junk value `0`. -/
noncomputable def complexity (a : ℕ → α) (n : ℕ) : ℕ := (factors a n).ncard

@[simp] theorem length_factor (a : ℕ → α) (i n : ℕ) : (factor a i n).length = n := by
  simp [factor]

/-- A factor of length `n + 1` is its first letter followed by a factor of length `n`. -/
theorem factor_succ (a : ℕ → α) (i n : ℕ) : factor a i (n + 1) = a i :: factor a (i + 1) n := by
  simp only [factor, List.ofFn_succ, Fin.val_zero, add_zero, Fin.val_succ, List.cons.injEq,
    true_and]
  congr 1; funext j; congr 1; omega

/-- A factor of length `n + 1` is a factor of length `n` followed by one letter. -/
theorem factor_succ' (a : ℕ → α) (i n : ℕ) : factor a i (n + 1) = factor a i n ++ [a (i + n)] := by
  simp only [factor, List.ofFn_succ', List.concat_eq_append, Fin.val_castSucc, Fin.val_last]

/-- The prefix of length `n` of the factor of length `n + 1` at `i` is the factor of length `n`
at `i`. -/
theorem take_factor (a : ℕ → α) (i n : ℕ) : (factor a i (n + 1)).take n = factor a i n := by
  rw [factor_succ', List.take_left' (length_factor a i n)]

/-- Two factors of length `n` agree if and only if the letters do. -/
theorem factor_eq_factor_iff {a : ℕ → α} {i i' n : ℕ} :
    factor a i n = factor a i' n ↔ ∀ j < n, a (i + j) = a (i' + j) := by
  simp only [factor, List.ofFn_inj, funext_iff, Fin.forall_iff]

/-- Over a finite alphabet there are finitely many factors of each length. -/
theorem finite_factors [Finite α] (a : ℕ → α) (n : ℕ) : (factors a n).Finite :=
  (Set.finite_range (List.ofFn : (Fin n → α) → List α)).subset
    (Set.range_subset_iff.mpr fun _ ↦ ⟨_, rfl⟩)

/-- There is one word of length `0`. -/
theorem complexity_zero (a : ℕ → α) : complexity a 0 = 1 := by
  have : factors a 0 = {[]} := by
    ext w; simp [factors, factor]
  simp [complexity, this]

/-- Every factor of length `n` extends to a factor of length `n + 1`. -/
theorem image_take_factors (a : ℕ → α) (n : ℕ) :
    List.take n '' factors a (n + 1) = factors a n := by
  rw [factors, ← Set.range_comp]; congr 1; funext i; exact take_factor a i n

/-- **The complexity is nondecreasing**, over a finite alphabet. -/
theorem complexity_mono [Finite α] (a : ℕ → α) : Monotone (complexity a) := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rw [complexity, ← image_take_factors]
  exact Set.ncard_image_le (finite_factors a _)

/-- Over a finite alphabet the complexity is at least `1`. -/
theorem one_le_complexity [Finite α] (a : ℕ → α) (n : ℕ) : 1 ≤ complexity a n :=
  complexity_zero a ▸ complexity_mono a (Nat.zero_le n)

/-- **Unique right extensions.** If `p (m + 1) = p m`, a factor of length `m` determines the factor
of length `m + 1` at the same position. -/
theorem factor_succ_eq_of_complexity_eq [Finite α] {a : ℕ → α} {m : ℕ}
    (h : complexity a (m + 1) = complexity a m) {i i' : ℕ}
    (hii' : factor a i m = factor a i' m) : factor a i (m + 1) = factor a i' (m + 1) := by
  have hinj : Set.InjOn (List.take m) (factors a (m + 1)) :=
    Set.injOn_of_ncard_image_eq (by rw [image_take_factors]; exact h.symm) (finite_factors a _)
  exact hinj ⟨i, rfl⟩ ⟨i', rfl⟩ (by rw [take_factor, take_factor, hii'])

/-- An eventually periodic sequence, with period `p` from `N` on, has at most `N + p` factors of
each length. -/
theorem IsEventuallyPeriodic.bddAbove_complexity {a : ℕ → α} (h : IsEventuallyPeriodic a) :
    BddAbove (Set.range (complexity a)) := by
  obtain ⟨N, p, hp, hper⟩ := h
  have hmul : ∀ c x, N ≤ x → a (x + c * p) = a x := by
    intro c; induction c with
    | zero => simp
    | succ c ih => intro x hx; rw [add_mul, one_mul, ← add_assoc, hper _ (by omega), ih x hx]
  refine ⟨N + p, Set.forall_mem_range.mpr fun n ↦ ?_⟩
  have hsub : factors a n ⊆ (fun i ↦ factor a i n) '' ↑(Finset.range (N + p)) := by
    rintro _ ⟨i, rfl⟩
    by_cases hi : i < N
    · exact ⟨i, by simp; omega, rfl⟩
    · refine ⟨N + (i - N) % p, by simp; have := Nat.mod_lt (i - N) hp; omega, ?_⟩
      refine factor_eq_factor_iff.mpr fun j _ ↦ ?_
      have hi' : i + j = N + (i - N) % p + j + (i - N) / p * p := by
        have := Nat.mod_add_div (i - N) p; rw [mul_comm] at this; omega
      rw [hi', hmul _ _ (by omega)]
  calc complexity a n ≤ ((fun i ↦ factor a i n) '' ↑(Finset.range (N + p))).ncard :=
        Set.ncard_le_ncard hsub ((Finset.finite_toSet _).image _)
    _ ≤ (↑(Finset.range (N + p)) : Set ℕ).ncard := Set.ncard_image_le (Finset.finite_toSet _)
    _ = N + p := by rw [Set.ncard_coe_finset, Finset.card_range]

/-- **Morse–Hedlund**, the hard direction: if `p n ≤ n` for one `n`, the sequence is eventually
periodic. -/
theorem isEventuallyPeriodic_of_complexity_le [Finite α] {a : ℕ → α} {n : ℕ}
    (hn : complexity a n ≤ n) : IsEventuallyPeriodic a := by
  -- some `m < n` with `p (m + 1) = p m`
  obtain ⟨m, -, hm⟩ : ∃ m < n, complexity a (m + 1) = complexity a m := by
    by_contra! hlt
    have : ∀ k ≤ n, k + 1 ≤ complexity a k := by
      intro k; induction k with
      | zero => intro; rw [complexity_zero]
      | succ k ih =>
        intro hk
        have h1 := ih (by omega)
        have h2 := complexity_mono a (k.le_add_right 1)
        have h3 := hlt k (by omega)
        omega
    have := this n le_rfl; omega
  -- two positions with the same factor of length `m`
  have : Finite (factors a m) := (finite_factors a m).to_subtype
  obtain ⟨i, j, hij, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun i : ℕ ↦ (⟨factor a i m, i, rfl⟩ : factors a m))
  replace heq := congrArg Subtype.val heq
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm heq.symm (by omega)
  have hall : ∀ k, factor a (i + k) m = factor a (j + k) m := by
    intro k; induction k with
    | zero => simpa using heq
    | succ k ih =>
      have := factor_succ_eq_of_complexity_eq hm ih
      rw [factor_succ, factor_succ] at this
      simpa [add_assoc] using (List.cons.inj this).2
  refine ⟨i, j - i, by omega, fun x hx ↦ ?_⟩
  have := factor_succ_eq_of_complexity_eq hm (hall (x - i))
  rw [factor_succ, factor_succ] at this
  have h := (List.cons.inj this).1
  rw [show i + (x - i) = x by omega, show j + (x - i) = x + (j - i) by omega] at h
  exact h.symm

/-- **The theorem of Morse and Hedlund.** Over a finite alphabet, a sequence is eventually periodic
if and only if its complexity is bounded, if and only if `p n ≤ n` for some `n`. -/
theorem isEventuallyPeriodic_tfae [Finite α] (a : ℕ → α) :
    List.TFAE [IsEventuallyPeriodic a, BddAbove (Set.range (complexity a)),
      ∃ n, complexity a n ≤ n] := by
  tfae_have 1 → 2 := IsEventuallyPeriodic.bddAbove_complexity
  tfae_have 2 → 3 := fun ⟨B, hB⟩ ↦ ⟨B, hB ⟨B, rfl⟩⟩
  tfae_have 3 → 1 := fun ⟨_, hn⟩ ↦ isEventuallyPeriodic_of_complexity_le hn
  tfae_finish

/-- A constant sequence has one factor of each length. -/
theorem complexity_const (x : α) (n : ℕ) : complexity (fun _ ↦ x) n = 1 := by
  have : factors (fun _ ↦ x) n = {factor (fun _ ↦ x) 0 n} := by
    ext w; simp [factors, factor]
  rw [complexity, this, Set.ncard_singleton]

/-- **Morse–Hedlund, the classical form**: a sequence over a finite alphabet that is not eventually
periodic has at least `n + 1` factors of length `n`. -/
theorem lt_complexity [Finite α] {a : ℕ → α} (ha : ¬ IsEventuallyPeriodic a) (n : ℕ) :
    n < complexity a n :=
  lt_of_not_ge fun hn ↦ ha (isEventuallyPeriodic_of_complexity_le hn)


/-- A period `s` on a segment is a period `c s` on the same segment. -/
theorem forall_add_mul_eq_of_forall_add_eq {a : ℕ → α} {r L s : ℕ}
    (h : ∀ i, r ≤ i → i + s < L → a (i + s) = a i) :
    ∀ c i, r ≤ i → i + c * s < L → a (i + c * s) = a i := by
  intro c; induction c with
  | zero => simp
  | succ c ih =>
    intro i hi hiL
    have hle : i + s ≤ i + (c + 1) * s := by nlinarith
    rw [show i + (c + 1) * s = i + s + c * s by ring, ih (i + s) (by omega) (by linarith),
      h i hi (by omega)]

/-- **The combinatorial lemma, in the working form of Layer 7.4.** If `p n ≤ C n` for infinitely
many `n`, then `a` has period `s k` on the segment of length `⌈w s k⌉` after position `r k`, with
`w = 1 + 1 / (1 + 2 ⌈C⌉) > 1`, `r k ≤ 2 ⌈C⌉ s k` and `s k` strictly increasing. -/
theorem exists_periodic_of_frequently_complexity_le [Finite α] {a : ℕ → α} {C : ℝ}
    (h : ∃ᶠ n in atTop, (complexity a n : ℝ) ≤ C * n) :
    ∃ w C' : ℝ, 1 < w ∧ 0 ≤ C' ∧ ∃ r s : ℕ → ℕ, StrictMono s ∧ (∀ k, 1 ≤ s k) ∧
      (∀ k, (r k : ℝ) ≤ C' * s k) ∧
      ∀ k i, r k ≤ i → i + s k < r k + ⌈w * s k⌉₊ → a (i + s k) = a i := by
  set κ : ℕ := ⌈C⌉₊ with hκ
  set w : ℝ := 1 + 1 / (1 + 2 * κ) with hw
  have hκ0 : (0 : ℝ) < 1 + 2 * κ := by positivity
  have key : ∀ N, ∃ r P : ℕ, N ≤ P ∧ 1 ≤ P ∧ r ≤ 2 * κ * P ∧
      ∀ i, r ≤ i → i + P < r + ⌈w * P⌉₊ → a (i + P) = a i := by
    intro N
    obtain ⟨n, hn, hpn⟩ := (frequently_atTop.mp h) (2 * N + 1)
    have hpn : complexity a n ≤ κ * n := by
      have : (complexity a n : ℝ) ≤ κ * n :=
        hpn.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (Nat.cast_nonneg n))
      exact_mod_cast this
    -- two of the first `p n + 1` positions carry the same factor of length `n`
    have hcard : (finite_factors a n).toFinset.card < (Finset.range (complexity a n + 1)).card := by
      rw [Finset.card_range, ← Set.ncard_eq_toFinset_card _ (finite_factors a n)]
      exact Nat.lt_succ_self _
    obtain ⟨x, hx, y, hy, hxy, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := fun i ↦ factor a i n) (fun i _ ↦ by simp [factors])
    wlog hlt : x < y generalizing x y
    · exact this y hy x hx hxy.symm heq.symm (by omega)
    simp only [Finset.mem_range] at hx hy
    set s := y - x with hs
    have hbase : ∀ i, x ≤ i → i + s < x + n + s → a (i + s) = a i := by
      intro i hi hiL
      have := factor_eq_factor_iff.mp heq (i - x) (by omega)
      rw [show x + (i - x) = i by omega, show y + (i - x) = i + s by omega] at this
      exact this.symm
    set q := n / (2 * s) with hq
    have hdm := Nat.div_add_mod n (2 * s)
    have hmod := Nat.mod_lt n (show 0 < 2 * s by omega)
    rw [← hq] at hdm
    set P := (q + 1) * s with hP
    have hP1 : n < 2 * P := by rw [hP]; nlinarith
    have h2q : 2 * s * q ≤ n := by rw [hq]; exact Nat.mul_div_le n (2 * s)
    have hP2 : 2 * P ≤ n + 2 * s := by rw [hP]; linarith
    have hsκ : s ≤ κ * n := by omega
    have hceil : ⌈w * P⌉₊ ≤ n + s := by
      refine Nat.ceil_le.mpr ?_
      have hP2' : (2 * P : ℝ) ≤ n + 2 * s := by exact_mod_cast hP2
      have hsκ' : (s : ℝ) ≤ κ * n := by exact_mod_cast hsκ
      have : (P : ℝ) / (1 + 2 * κ) ≤ n / 2 := by
        rw [div_le_iff₀ hκ0]; nlinarith
      push_cast; rw [hw]; linarith [show (1 + 1 / (1 + 2 * (κ : ℝ))) * P = P + P / (1 + 2 * κ) by
        ring]
    refine ⟨x, P, by omega, by rw [hP]; nlinarith, ?_, fun i hi hiP ↦ ?_⟩
    · have : κ * n ≤ κ * (2 * P) := Nat.mul_le_mul_left κ hP1.le
      nlinarith
    · exact forall_add_mul_eq_of_forall_add_eq hbase (q + 1) i hi (by omega)
  choose R Pf hNP hP1 hRP hper using key
  let Ns : ℕ → ℕ := fun k ↦ Nat.rec 0 (fun _ M ↦ Pf M + 1) k
  have hNs : ∀ k, Ns (k + 1) = Pf (Ns k) + 1 := fun _ ↦ rfl
  refine ⟨w, 2 * κ, by rw [hw]; have := one_div_pos.mpr hκ0; linarith, by positivity,
    fun k ↦ R (Ns k), fun k ↦ Pf (Ns k), strictMono_nat_of_lt_succ fun k ↦ ?_,
    fun k ↦ hP1 _, fun k ↦ ?_, fun k ↦ hper _⟩
  · have := hNP (Ns (k + 1)); change Pf (Ns k) < Pf (Ns (k + 1)); rw [hNs] at this ⊢; omega
  · have := hRP (Ns k); exact_mod_cast this

/-- **The combinatorial lemma** (Adamczewski–Bugeaud 2007, §4). Over a finite alphabet, if
`p n ≤ C n` for infinitely many `n`, then `a` is stammering. -/
theorem isStammering_of_frequently_complexity_le [Finite α] {a : ℕ → α} {C : ℝ}
    (h : ∃ᶠ n in atTop, (complexity a n : ℝ) ≤ C * n) : IsStammering a := by
  obtain ⟨w, C', hw, -, r, s, hs, hs1, hrs, hper⟩ := exists_periodic_of_frequently_complexity_le h
  exact ⟨w, hw, isStammeringWith_of_periodic (by linarith) hs hs1 hrs hper⟩


/-! ### Acceptance criteria -/

/-- The combinatorial lemma at work: a constant sequence has `p n = 1 ≤ n` for `n ≥ 1`, so it is
stammering. -/
example : IsStammering (fun _ ↦ (0 : Fin 2)) :=
  isStammering_of_frequently_complexity_le (C := 1) <| frequently_atTop.mpr fun N ↦
    ⟨N + 1, Nat.le_succ N, by rw [complexity_const]; push_cast; linarith⟩

/-- Rejection: over an infinite alphabet `p` need not be monotone — the identity of `ℕ` has
infinitely many factors of length `1`, which `Set.ncard` counts as `0`. -/
theorem complexity_id_one : complexity (id : ℕ → ℕ) 1 = 0 := by
  refine Set.Infinite.ncard (Set.infinite_range_of_injective fun i j h ↦ ?_)
  simpa [factor] using h

example : complexity (id : ℕ → ℕ) 1 < complexity (id : ℕ → ℕ) 0 := by
  rw [complexity_id_one, complexity_zero]; exact Nat.one_pos

end Function
