/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.RingTheory.DedekindDomain.SInteger
public import ArithmeticHeights.NorthcottTheorem

-- Used only inside proofs.
import ArithmeticHeights.Northcott

/-!
# The small solutions (Lemmas 5.1 and 5.2)

The solutions `y = α x` of `∑ αᵢ xᵢ = 0` (in `S`-units) whose height lies below the windows of
the gap principle (`GapPrinciple.lean`, which starts above `(n!) ^ (2 [K : ℚ])`) are put into
proper subspaces one by one: each `y' = (y₁, …, yₙ)` spans a line, and there are few lines,
because there are few points of `ℙ^{n−1}(K)` of bounded height.

Schlickewei counts those points by Schmidt's lecture notes (Lemma 5.1). Here the count is
`ArithmeticHeights`' `Projectivization.ncard_setOfPred_mulHeight_le`, Northcott's theorem with the
roots of the integer polynomials of bounded Mahler measure counted. Like Lemma 5.1 it sees `K`
only through its degree `d`, which is what the theorems of record need; the constant is
`northcottCount d (max B 1) ^ n`, not `n · 36^{n−1} 2^{2d(n−1)} B^{2(n−1)}`. Lemma 5.2's range
`H(y') < n^{9ns(d!)²}` is not needed: the gap principle here starts at `(n!)^{2d}` for every `α`
(`README.md`, the S90.3 check, item 4).

## Main results

* `NumberField.exists_finset_submodule_of_mulHeight_lt`: for `n ≥ 2`, the solutions with
  `H(y) < B` have `y'` in one of at most `northcottCount [K : ℚ] (max B 1) ^ n` proper subspaces.

## Implementation notes

The subspaces are the lines `K y'`, so `n ≥ 2` is needed for them to be proper. For `n = 1` the
equation `α₁ x₁ + α₂ x₂ = 0` has one projective solution, and the induction of §7 (S90.6) treats
it apart. Neither the equation nor `S` is used beyond `y' ≠ 0`.
-/

@[expose] public section

open IsDedekindDomain Height Module Finset

namespace NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- **The small solutions (Lemmas 5.1 and 5.2).** For `n ≥ 2` and any `B`, the solutions
`y = α x` in `S`-units with `H(y) < B` have `y' = (y₁, …, yₙ)` in one of at most
`northcottCount [K : ℚ] (max B 1) ^ n` proper subspaces of `Kⁿ`, a count that sees `K` only
through its degree. -/
theorem exists_finset_submodule_of_mulHeight_lt (hι : 2 ≤ Fintype.card ι)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {α : Option ι → K} (hα0 : ∀ o, α o ≠ 0) (B : ℝ) :
    ∃ T : Finset (Submodule K (ι → K)),
      #T ≤ northcottCount (finrank ℚ K) (max B 1).toNNReal ^ Fintype.card ι ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x : Option ι → Kˣ, (∀ o, x o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) →
        mulHeight (fun o ↦ α o * (x o : K)) < B →
        ∃ U ∈ T, (fun i ↦ α (some i) * (x (some i) : K)) ∈ U := by
  classical
  have hfin := Projectivization.finite_setOfPred_mulHeight_le (K := K) (ι := ι) B
  refine ⟨hfin.toFinset.image Projectivization.submodule, ?_, ?_, ?_⟩
  · refine card_image_le.trans ?_
    rw [← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_eq_fintype_card]
    exact Projectivization.ncard_setOfPred_mulHeight_le B
  · simp only [mem_image, Set.Finite.mem_toFinset, forall_exists_index, and_imp]
    rintro _ P - rfl htop
    have h := P.finrank_submodule
    rw [htop, finrank_top, finrank_pi] at h
    omega
  · intro x _ hB
    obtain ⟨i⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    have hy : (fun i ↦ α (some i) * (x (some i) : K)) ≠ 0 :=
      Function.ne_iff.2 ⟨i, mul_ne_zero (hα0 _) (x (some i)).ne_zero⟩
    refine ⟨(Projectivization.mk K _ hy).submodule,
      mem_image_of_mem _ (hfin.mem_toFinset.2 ?_), ?_⟩
    · rw [Set.mem_ofPred, Projectivization.mulHeight_mk]
      exact ((mulHeight_comp_le some fun o ↦ α o * (x o : K))).trans hB.le
    · rw [Projectivization.submodule_mk]
      exact Submodule.mem_span_singleton_self _

end NumberField
