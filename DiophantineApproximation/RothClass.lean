/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.IndependentHeights

/-!
# One approximation class, in the form Roth's proof consumes

Layer 3.1 partitions an infinite set into approximation classes and finds an `(L, M)`-independent
sequence inside one of them. What Roth's proof uses is the *consequence*: a family of exponents
`λ a ≥ 0`, one for each place of `S`, with `∑ a, λ a ≥ 1 − |S| / N`, such that every term of the
sequence satisfies

```text
f a (β j) ≤ H(β j) ^ (−κ λ a)
```

at every place — the local approximation factors of all the `β j` are governed by *one* vector of
exponents and by the height of the term alone. That is the book's (6.9) and (6.10) read together
against the hypothesis `Λ(β) ≤ H(β)^{−κ}`, and it is the only thing Steps I to V ever quote.

The statement is proved for an arbitrary finite index type and an arbitrary family
`f : A → K → ℝ`, as in Layer 3.1: nothing here is about places. The arithmetic is Northcott's
theorem, inside Layer 3.1.

## Main results

* `NumberField.exists_isHeightIndependent_forall_le_rpow`: **Step 0 of Roth's proof**
  (Bombieri–Gubler 6.4.2–6.4.4) in the form the rest of the proof consumes.

## Implementation notes

⚠ **The hypotheses force `Λ(β) < 1`, and that is where `0 < κ` and `1 < H(β)` are used.** A
member of `X` with height `1` would have `Λ(β) ≤ 1` with no room, the logarithmic profile would
divide by `log 1 = 0`, and the classification would be vacuous. The consumer discards the finitely
many elements of height at most `1` by Northcott before applying this lemma.

⚠ **`λ a` is `c a / N`, not the profile itself.** The profile varies inside a class; the *label*
`c a` does not, and it is the label that (6.10) bounds from below. The exponents are therefore
rational with denominator `N`, which is what lets `N → ∞` recover the full strength.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§6.4.2 to §6.4.4.

This is part of Layer 3.2 of the `DiophantineApproximation` roadmap, and consumes Layer 3.1.
-/

@[expose] public section

open Height

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {A : Type*} [Fintype A]

/-- **Step 0 of Roth's proof** (Bombieri–Gubler 6.4.2–6.4.4), in the form the rest of the proof
consumes. -/
theorem exists_isHeightIndependent_forall_le_rpow (f : A → K → ℝ) {X : Set K} (hX : X.Infinite)
    (hpos : ∀ a, ∀ β ∈ X, 0 < f a β) (hle : ∀ a, ∀ β ∈ X, f a β ≤ 1)
    {κ : ℝ} (hκ : 0 < κ)
    (happrox : ∀ β ∈ X, (∏ a, f a β) ≤ mulHeight₁ β ^ (-κ))
    (hheight : ∀ β ∈ X, 1 < mulHeight₁ β)
    {N : ℕ} (hN : 0 < N) (L M : ℝ) :
    ∃ lam : A → ℝ, (∀ a, 0 ≤ lam a) ∧ 1 - (Fintype.card A : ℝ) / N ≤ ∑ a, lam a ∧
      ∃ β : ℕ → K, (∀ j, β j ∈ X) ∧ IsHeightIndependent L M β ∧
        ∀ j a, f a (β j) ≤ mulHeight₁ (β j) ^ (-κ * lam a) := by
  -- every member of `X` is a non-trivial approximation
  have hprod : ∀ β ∈ X, (∏ a, f a β) < 1 := fun β hβ ↦
    lt_of_le_of_lt (happrox β hβ) (Real.rpow_lt_one_of_one_lt_of_neg (hheight β hβ) (by linarith))
  set φ : A → K → ℝ := fun a β ↦ Real.logProfile (fun b ↦ f b β) a with hφdef
  have hφ0 : ∀ a, ∀ β ∈ X, 0 ≤ φ a β := fun a β hβ ↦
    Real.logProfile_nonneg (fun b ↦ hpos b β hβ) (fun b ↦ hle b β hβ) (hprod β hβ) a
  have hφsum : ∀ β ∈ X, ∑ a, φ a β = 1 := fun β hβ ↦
    Real.sum_logProfile (fun b ↦ hpos b β hβ) (hprod β hβ)
  obtain ⟨c, _, β, hβX, hβc, hβind⟩ :=
    exists_cellIndex_eq_and_isHeightIndependent φ hX hφ0
      (fun β hβ ↦ le_of_eq (hφsum β hβ)) N L M
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨fun a ↦ (c a : ℝ) / N, fun a ↦ by positivity, ?_, β, hβX, hβind, fun j a ↦ ?_⟩
  · have h610 := Real.one_sub_card_div_lt_sum_cellIndex_div (y := fun a ↦ φ a (β 0)) hN
      (hφsum (β 0) (hβX 0))
    rw [hβc 0] at h610
    exact h610.le
  · have hβj := hβX j
    have hpos' : ∀ b, 0 < f b (β j) := fun b ↦ hpos b (β j) hβj
    have hprod0 : (0 : ℝ) < ∏ b, f b (β j) := Finset.prod_pos fun b _ ↦ hpos' b
    have hcell := Real.le_rpow_cellIndex_div (f := fun b ↦ f b (β j)) hN hpos'
      (fun b ↦ hle b (β j) hβj) (hprod (β j) hβj) a
    rw [show Real.logProfile (fun b ↦ f b (β j)) = fun a ↦ φ a (β j) from rfl, hβc j] at hcell
    refine le_trans hcell ?_
    calc (∏ b, f b (β j)) ^ ((c a : ℝ) / N)
        ≤ (mulHeight₁ (β j) ^ (-κ)) ^ ((c a : ℝ) / N) :=
          Real.rpow_le_rpow hprod0.le (happrox (β j) hβj) (by positivity)
      _ = mulHeight₁ (β j) ^ (-κ * ((c a : ℝ) / N)) := by
          rw [← Real.rpow_mul (le_of_lt (lt_trans zero_lt_one (hheight (β j) hβj)))]

end NumberField

end
