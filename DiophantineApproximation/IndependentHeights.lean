/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ApproximationClass
public import Mathlib.NumberTheory.Height.NumberField

/-!
# `(L, M)`-independent sequences

The second half of Mahler's reduction (Bombieri–Gubler 6.4.4). Roth's theorem is proved by
contradiction from an infinite set of solutions, and the proof needs from that set not one
solution but a whole tuple, with the heights spread out: `h (β 0) ≥ L`, so that the auxiliary
polynomial's error terms are small against every `h (β j)`, and `h (β (j + 1)) ≥ M h (β j)`, so
that the degrees `d j ≈ D / h (β j)` drop fast enough for Roth's lemma. Such a tuple exists
inside *every* infinite subset of a number field, and the only thing that makes it exist is
**Northcott's theorem**: a set of bounded height is finite, so an infinite set contains an
element of height above any bound at all.

Put together with `DiophantineApproximation/ApproximationClass.lean`, this is the reduction the
proof of Roth's theorem opens with: an infinite set of solutions contains an `(L, M)`-independent
sequence *all of whose terms lie in one approximation class*.

## Main results

* `NumberField.IsHeightIndependent`: the property, for a sequence.
* `NumberField.exists_isHeightIndependent`: every infinite subset of a number field contains an
  `(L, M)`-independent sequence, for every `L` and `M`.
* `NumberField.exists_isHeightIndependent_comp`: the same for a family of points indexed by an
  arbitrary set of unbounded height, choosing indices rather than points.
* `NumberField.IsHeightIndependent.injective`: with `0 < L` and `1 < M` the terms are distinct,
  their heights being strictly increasing.
* `NumberField.exists_cellIndex_eq_and_isHeightIndependent`: **6.4.4**, the two reductions at
  once.

## Implementation notes

⚠ **The heights are Mathlib's relative `logHeight₁`, not the book's absolute `h`**, and the two
differ by the factor `totalWeight K`. Nothing is lost: `M` is a ratio of two heights, so it reads
the same in both normalizations, and `L` is universally quantified, so the statement with a
relative `L` and the statement with an absolute one are the same statement. A consumer that
mixes this bound with an absolute one has to put the factor back, as everywhere else in this
roadmap.

⚠ **The sequence is indexed by `ℕ`, not by `Fin m`.** The book takes an infinite subsequence and
then uses its first `m` terms; an infinite sequence is the stronger statement and the `Fin m`
form is `fun j : Fin m ↦ β j`, so it is what is proved here.

⚠ **`1 < M` is not needed for existence**, only for distinctness: at `M ≤ 1` the sequence may
repeat a value and the conclusion is still true, and it is the consumer of 3.2 — where `M` is
large — that needs the terms to differ.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
6.4.4 and Theorem 1.6.8.

This is part of Layer 3.1 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **`(L, M)`-independence** (Bombieri–Gubler 6.4.4): the first term has height at least `L`, and
each term has height at least `M` times the height of its predecessor. -/
def IsHeightIndependent (L M : ℝ) (β : ℕ → K) : Prop :=
  L ≤ logHeight₁ (β 0) ∧ ∀ j, M * logHeight₁ (β j) ≤ logHeight₁ (β (j + 1))

/-- **An infinite set contains elements of arbitrarily large height**, by Northcott's theorem. -/
theorem exists_mem_lt_logHeight₁ {X : Set K} (hX : X.Infinite) (C : ℝ) :
    ∃ x ∈ X, C < logHeight₁ x := by
  by_contra h
  push Not at h
  exact hX ((NumberField.finite_setOfPred_logHeight₁_le K C).subset fun x hx ↦ h x hx)

/-- **A family of points of unbounded height on `X` has an `(L, M)`-independent subsequence.**
What is chosen is a sequence of *indices* `x j ∈ X`, and the terms are the points `g (x j)`: two
indices may carry the same point. That is the form Layer 3.8 needs, where every index is a pair
of a point and its own targets. -/
theorem exists_isHeightIndependent_comp {ι : Type*} (g : ι → K) {X : Set ι}
    (hX : ∀ C : ℝ, ∃ x ∈ X, C < logHeight₁ (g x)) (L M : ℝ) :
    ∃ x : ℕ → ι, (∀ j, x j ∈ X) ∧ IsHeightIndependent L M fun j ↦ g (x j) := by
  choose y hyX hy using hX
  refine ⟨fun j ↦ Nat.rec (motive := fun _ ↦ ι) (y L)
    (fun _ prev ↦ y (M * logHeight₁ (g prev))) j, fun j ↦ ?_, (hy L).le, fun j ↦ (hy _).le⟩
  cases j with
  | zero => exact hyX L
  | succ j => exact hyX _

/-- **Every infinite subset of a number field contains an `(L, M)`-independent sequence.** -/
theorem exists_isHeightIndependent {X : Set K} (hX : X.Infinite) (L M : ℝ) :
    ∃ β : ℕ → K, (∀ j, β j ∈ X) ∧ IsHeightIndependent L M β :=
  exists_isHeightIndependent_comp id (exists_mem_lt_logHeight₁ hX) L M

/-- The heights of an `(L, M)`-independent sequence are strictly increasing, once `L` is positive
and `M` exceeds `1`. -/
theorem IsHeightIndependent.strictMono_logHeight₁ {L M : ℝ} {β : ℕ → K}
    (hβ : IsHeightIndependent L M β) (hL : 0 < L) (hM : 1 < M) :
    StrictMono fun j ↦ logHeight₁ (β j) := by
  have hpos : ∀ j, 0 < logHeight₁ (β j) := by
    intro j
    induction j with
    | zero => exact lt_of_lt_of_le hL hβ.1
    | succ j ih => exact lt_of_lt_of_le (by nlinarith) (hβ.2 j)
  exact strictMono_nat_of_lt_succ fun j ↦
    lt_of_lt_of_le (by nlinarith [hpos j]) (hβ.2 j)

/-- **The terms of an `(L, M)`-independent sequence are distinct**, once `0 < L` and `1 < M`. -/
theorem IsHeightIndependent.injective {L M : ℝ} {β : ℕ → K} (hβ : IsHeightIndependent L M β)
    (hL : 0 < L) (hM : 1 < M) : Function.Injective β :=
  fun _ _ hij ↦ (hβ.strictMono_logHeight₁ hL hM).injective (congrArg logHeight₁ hij)

/-- **Bombieri–Gubler 6.4.4**, the two reductions at once: an infinite set of points of a number
field contains an `(L, M)`-independent sequence all of whose terms lie in one approximation class
of size `1/N`. -/
theorem exists_cellIndex_eq_and_isHeightIndependent {A : Type*} [Fintype A] (φ : A → K → ℝ)
    {X : Set K} (hX : X.Infinite) (hφ0 : ∀ a, ∀ x ∈ X, 0 ≤ φ a x) (hφ1 : ∀ x ∈ X, ∑ a, φ a x ≤ 1)
    (N : ℕ) (L M : ℝ) :
    ∃ c : A → ℕ, (∑ a, c a ≤ N) ∧ ∃ β : ℕ → K, (∀ j, β j ∈ X) ∧
      (∀ j, Real.cellIndex N (fun a ↦ φ a (β j)) = c) ∧ IsHeightIndependent L M β := by
  obtain ⟨c, hc, hinf⟩ := hX.exists_cellIndex_eq φ hφ0 hφ1 N
  obtain ⟨β, hβX, hβ⟩ := exists_isHeightIndependent hinf L M
  exact ⟨c, hc, β, fun j ↦ (hβX j).1, fun j ↦ (hβX j).2, hβ⟩

/-- The `Fin (m + 1)`-indexed form: a tuple whose heights start above `L` and grow by a factor
`M` at each step, which is the shape the auxiliary polynomial and Roth's lemma consume. -/
theorem exists_fin_le_logHeight₁ {X : Set K} (hX : X.Infinite) (L M : ℝ) (m : ℕ) :
    ∃ β : Fin (m + 1) → K, (∀ j, β j ∈ X) ∧ L ≤ logHeight₁ (β 0) ∧
      ∀ j : Fin m, M * logHeight₁ (β j.castSucc) ≤ logHeight₁ (β j.succ) := by
  obtain ⟨β, hβX, hβ0, hβs⟩ := exists_isHeightIndependent hX L M
  refine ⟨fun j ↦ β j, fun j ↦ hβX _, hβ0, fun j ↦ ?_⟩
  simpa [Fin.val_succ] using hβs j

/-!
### Acceptance criteria

The sequence the existence theorem produces is checked to be genuinely infinite, and the
hypothesis that `X` is infinite is checked to be load-bearing.
-/

/-- **Acceptance test: the terms are distinct and their heights are unbounded.** -/
example : ∃ β : ℕ → ℚ, StrictMono fun j ↦ logHeight₁ (β j) := by
  obtain ⟨β, -, hβ⟩ := exists_isHeightIndependent (X := (Set.univ : Set ℚ)) Set.infinite_univ 1 2
  exact ⟨β, hβ.strictMono_logHeight₁ one_pos one_lt_two⟩

/-- **Rejection test: `X.Infinite` is load-bearing**, and not merely a convenience. The set
`{0, 1}` of rationals is nonempty and every element of it has height `1`, so no sequence in it is
`(1, 2)`-independent: Northcott's theorem is used at full strength, on a set that has to be
infinite before it can contain an element of height above a given bound. -/
example : ¬ ∃ β : ℕ → ℚ, (∀ j, β j ∈ ({0, 1} : Set ℚ)) ∧ IsHeightIndependent 1 2 β := by
  rintro ⟨β, hβX, hβ0, -⟩
  have hzero : logHeight₁ (β 0) = 0 := by
    rcases hβX 0 with h | h <;> rw [h]
    · exact logHeight₁_zero
    · exact logHeight₁_one
  rw [hzero] at hβ0
  norm_num at hβ0

end NumberField
