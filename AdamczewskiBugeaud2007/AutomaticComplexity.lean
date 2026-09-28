/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import AdamczewskiBugeaud2007.AutomaticSequence
public import DiophantineApproximation.ComplexityTranscendence

-- Used only inside proofs.
import Mathlib.Data.Nat.Log

/-!
# Automatic sequences have linear complexity; irrational automatic numbers are transcendental

**Theorem 2** of Adamczewski–Bugeaud 2007: for `b ≥ 2`, the base-`b` expansion of an irrational
algebraic number is not automatic. In the paper it follows from Theorem 1 (`p(n) / n → ∞` for an
algebraic irrational, `Real.tendsto_complexity_div_atTop`) and Cobham's bound `p(n) = O(n)` for
an automatic sequence. This file proves Cobham's bound from the definition by the kernel and
deduces Theorem 2, and the fact, used in the paper's proof of Theorem 2B, that an automatic
sequence is stammering.

## Main results

* `Function.IsAutomatic.exists_complexity_le`: **Cobham's bound**, `p(n) ≤ C n` for `n ≥ 1`.
* `Function.IsAutomatic.isStammering`: an automatic sequence over a finite alphabet is
  stammering.
* `Real.transcendental_ofDigits_of_isAutomatic`: **Theorem 2**, irrational automatic numbers are
  transcendental.

## Implementation notes

⚠ **No automaton and no uniform morphism.** Cobham derives the bound from the representation of
an automatic sequence as a coding of a fixed point of a uniform morphism. From the kernel it is
shorter. Let `K` be the `k`-kernel and `v n = (s n)_{s ∈ K}`, a vector in the finite set
`K → range a`. The block `a (k ^ m q), …, a (k ^ m q + k ^ m - 1)` of level `m` at `q` is
`(s q)_s` for the kernel members `s = (n ↦ a (k ^ m n + c))`, so it is determined by `v q`. A
factor of length `L ≤ k ^ m` starting at `k ^ m q + r` lies in the blocks at `q` and `q + 1`,
so it is determined by `r < k ^ m`, `v q` and `v (q + 1)`. With `k ^ m ≤ k L` this is
`p(L) ≤ k |K → range a| ^ 2 L`.

⚠ **Non-periodicity is not a hypothesis of the stammering statement.** Condition `(∗)_w` of the
paper includes it; `Function.IsStammering` does not, and the transcendence criteria take it
separately.

## References

B. Adamczewski and Y. Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer
bases*, Annals of Mathematics **165** (2007), 547–565, Theorem 2 and its proof in §5;
A. Cobham, *Uniform tag sequences*, Math. Systems Theory **6** (1972), 164–192.
-/

@[expose] public section

open Filter

namespace Function

variable {α : Type*}

/-- **Cobham's bound**: an automatic sequence has at most `C n` factors of length `n ≥ 1`. -/
theorem IsAutomatic.exists_complexity_le {a : ℕ → α} (h : IsAutomatic a) :
    ∃ C : ℕ, ∀ n, 1 ≤ n → complexity a n ≤ C * n := by
  classical
  have hA := h.finite_range
  obtain ⟨k, hk, hK⟩ := h
  have := hK.to_subtype
  have := hA.to_subtype
  let v : ℕ → (kKernel k a → Set.range a) := fun n s ↦
    ⟨s.1 n, range_subset_of_mem_kKernel s.2 ⟨n, rfl⟩⟩
  -- the block of level `m` at `q` is a function of `v q`
  have hv : ∀ m c, c < k ^ m → ∀ q q', v q = v q' → a (k ^ m * q + c) = a (k ^ m * q' + c) :=
    fun m c hc q q' hq ↦
      congrArg Subtype.val (congrFun hq ⟨fun n ↦ a (k ^ m * n + c), m, c, hc, rfl⟩)
  refine ⟨k * Nat.card (kKernel k a → Set.range a) ^ 2, fun L hL ↦ ?_⟩
  set m := Nat.log k L + 1
  set B := k ^ m with hB
  have hLB : L < B := Nat.lt_pow_succ_log_self (by omega) L
  have hBL : B ≤ k * L := by
    rw [hB, pow_succ, mul_comm]
    exact Nat.mul_le_mul_left k (Nat.pow_log_le_self k (by omega))
  have hB0 : 0 < B := by positivity
  let F : ℕ → Fin B × (kKernel k a → Set.range a) × (kKernel k a → Set.range a) :=
    fun i ↦ (⟨i % B, Nat.mod_lt _ hB0⟩, v (i / B), v (i / B + 1))
  -- a factor of length `L` is a function of its offset and of the two blocks it meets
  have hF : ∀ i j, F i = F j → factor a i L = factor a j L := by
    intro i j hij
    simp only [F, Prod.mk.injEq, Fin.mk.injEq] at hij
    obtain ⟨hr, h0, h1⟩ := hij
    refine factor_eq_factor_iff.mpr fun t ht ↦ ?_
    have hi := Nat.div_add_mod i B
    have hj := Nat.div_add_mod j B
    rw [← hr] at hj
    have hrB := Nat.mod_lt i hB0
    generalize i % B = r at *
    generalize i / B = q at *
    generalize j / B = q' at *
    by_cases hc : r + t < B
    · have e := hv m (r + t) hc _ _ h0
      rw [show k ^ m * q + (r + t) = i + t by rw [← hB]; omega,
        show k ^ m * q' + (r + t) = j + t by rw [← hB]; omega] at e
      exact e
    · obtain ⟨c, hc'⟩ : ∃ c, r + t = B + c := ⟨r + t - B, by omega⟩
      have e := hv m c (by omega) _ _ h1
      rw [show k ^ m * (q + 1) + c = i + t by rw [← hB, mul_add, mul_one]; omega,
        show k ^ m * (q' + 1) + c = j + t by rw [← hB, mul_add, mul_one]; omega] at e
      exact e
  let g : Fin B × (kKernel k a → Set.range a) × (kKernel k a → Set.range a) → List α :=
    fun y ↦ if hy : ∃ i, F i = y then factor a hy.choose L else []
  have hsub : factors a L ⊆ Set.range g := by
    rintro _ ⟨i, rfl⟩
    have hy : ∃ i', F i' = F i := ⟨i, rfl⟩
    exact ⟨F i, by simp only [g, dite_eq_left hy]; exact hF _ _ hy.choose_spec⟩
  calc complexity a L ≤ (Set.range g).ncard := Set.ncard_le_ncard hsub (Set.finite_range g)
    _ ≤ (Set.univ : Set (Fin B × (kKernel k a → Set.range a) × (kKernel k a → Set.range a))).ncard
        := by rw [← Set.image_univ]; exact Set.ncard_image_le Set.finite_univ
    _ = B * Nat.card (kKernel k a → Set.range a) ^ 2 := by
        rw [Set.ncard_univ, Nat.card_prod, Nat.card_prod, Nat.card_fin, sq]
    _ ≤ k * L * Nat.card (kKernel k a → Set.range a) ^ 2 := Nat.mul_le_mul_right _ hBL
    _ = k * Nat.card (kKernel k a → Set.range a) ^ 2 * L := by ring

/-- Cobham's bound in the form the criteria consume: `p(n) ≤ C n` for infinitely many `n`. -/
theorem IsAutomatic.frequently_complexity_le {a : ℕ → α} (h : IsAutomatic a) :
    ∃ C : ℝ, ∃ᶠ n in atTop, (complexity a n : ℝ) ≤ C * n := by
  obtain ⟨C, hC⟩ := h.exists_complexity_le
  refine ⟨C, (eventually_ge_atTop 1).frequently.mono fun n hn ↦ ?_⟩
  exact_mod_cast hC n hn

/-- **An automatic sequence is stammering** (Adamczewski–Bugeaud 2007, proof of Theorem 2). -/
theorem IsAutomatic.isStammering [Finite α] {a : ℕ → α} (h : IsAutomatic a) : IsStammering a :=
  let ⟨_, hC⟩ := h.frequently_complexity_le
  isStammering_of_frequently_complexity_le hC

end Function

namespace Real

/-- **Theorem 2 (Adamczewski–Bugeaud 2007): irrational automatic numbers are transcendental.**
For `b ≥ 2`, if the digits `a` are automatic and `∑ k, a k / b ^ (k + 1)` is irrational, it is
transcendental. -/
theorem transcendental_ofDigits_of_isAutomatic {b : ℕ} (hb : 2 ≤ b) {a : ℕ → Fin b}
    (hauto : Function.IsAutomatic a) (hirr : Irrational (ofDigits a)) :
    Transcendental ℚ (ofDigits a) :=
  let ⟨_, hC⟩ := hauto.frequently_complexity_le
  transcendental_ofDigits_of_frequently_complexity_le hb ((irrational_ofDigits_iff hb).mp hirr) hC

end Real

/-! ### Acceptance criteria -/

/-- **Conformance: Cobham's bound for a constant sequence**, which is automatic. -/
example : ∃ C : ℕ, ∀ n, 1 ≤ n → Function.complexity (fun _ : ℕ ↦ (0 : Fin 2)) n ≤ C * n :=
  (Function.isAutomatic_const _).exists_complexity_le

/-- **Rejection: irrationality is load-bearing in Theorem 2.** The constant digit `0` is
automatic, and its value `0` is algebraic. -/
example : Function.IsAutomatic (fun _ : ℕ ↦ (0 : Fin 10)) ∧
    ¬ Transcendental ℚ (Real.ofDigits fun _ : ℕ ↦ (0 : Fin 10)) := by
  refine ⟨Function.isAutomatic_const _, fun h ↦ h ?_⟩
  have h0 : Real.ofDigits (fun _ : ℕ ↦ (0 : Fin 10)) = 0 := by
    simp [Real.ofDigits, Real.ofDigitsTerm]
  rw [h0]
  exact isAlgebraic_zero
