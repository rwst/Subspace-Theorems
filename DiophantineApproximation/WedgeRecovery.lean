/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.WedgeForm

/-!
# Recovering a subspace from the span of its wedges

For a basis `x` of `Kⁱ` and `k + p = #ι`, Lemma 7.5.33 of Bombieri–Gubler says that the span
`wedgeSpan k p x` of the wedges of the `p`-subsets meeting `x 0, …, x (k - 1)` determines the span
of those `k` vectors (`WedgeForm.lean`). Layer 6.1 needs that as a **function** of the subspace:
finitely many subspaces of `⋀^p Kⁱ` must yield finitely many subspaces of `Kⁱ`, and the map that
does it cannot mention the basis. `exteriorPower.recoverSpan` is that map — the span of the vectors
all of whose wedges lie in the given subspace — and it inverts `wedgeSpan`.

The file also carries the two facts about a **unitriangular change** of a family that Layer 6.1
needs beside it: it does not change the span of an initial segment, and that span is proper when
the segment is.

## Main results

* `exteriorPower.recoverSpan`: the subspace of `Kⁱ` recovered from a subspace of `⋀^p Kⁱ`.
* `exteriorPower.recoverSpan_wedgeSpan`: **Lemma 7.5.33 as a function** — it recovers the span of
  the first `k` members of a basis from the span of the wedges that meet them.
* `Submodule.span_image_add_sum_smul_eq`: a unitriangular change of a family does not change the
  span of an initial segment.
* `Submodule.span_image_setOf_lt_ne_top`: the span of a proper initial segment is proper.

## Implementation notes

⚠ **The recovered subspace is a span, not a carrier.** `recoverSpan` is defined as the span of the
set of vectors whose wedges all lie in `U`, and not as that set made into a submodule: the set is
one — the wedge is multilinear in each argument — but proving so needs an API for the Plücker
coordinates that nothing else in this development wants, while the span is a submodule for free and
is the same subspace whenever `U` is a `wedgeSpan`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 7.5.33.

This is part of Layer 6.1 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset Module

namespace Submodule

variable {K : Type*} [Field K] {ι : Type*} {N : ℕ}

/-- The image of an initial segment of `Fin N` is a range. -/
theorem image_setOf_lt_eq_range {α : Type*} (x : Fin N → α) {k : ℕ} (hk : k ≤ N) :
    x '' {j : Fin N | (j : ℕ) < k} = Set.range fun i : Fin k ↦ x (Fin.castLE hk i) := by
  ext u
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, by simp⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.castLE hk i, by simp, rfl⟩

/-- **The span of an initial segment of a family has rank at most its length.** -/
theorem finrank_span_image_setOf_lt_le (x : Fin N → ι → K) {k : ℕ} (hk : k ≤ N) :
    finrank K (span K (x '' {j : Fin N | (j : ℕ) < k})) ≤ k := by
  rw [image_setOf_lt_eq_range x hk]
  simpa [Set.finrank] using finrank_range_le_card (R := K) fun i : Fin k ↦ x (Fin.castLE hk i)

/-- **The span of a proper initial segment of a family is a proper subspace.** -/
theorem span_image_setOf_lt_ne_top [Fintype ι] (x : Fin (Fintype.card ι) → ι → K) {k : ℕ}
    (hk : k < Fintype.card ι) : span K (x '' {j | (j : ℕ) < k}) ≠ ⊤ := by
  intro htop
  have h := finrank_span_image_setOf_lt_le x hk.le
  rw [htop, finrank_top, finrank_fintype_fun_eq_card] at h
  omega

/-- **A unitriangular change of a family does not change the span of an initial segment.** -/
theorem span_image_add_sum_smul_eq (x : Fin N → ι → K) (ξ : Fin N → Fin N → K) (k : ℕ) :
    span K ((fun j ↦ x j + ∑ l ∈ Finset.Iio j, ξ j l • x l) '' {j | (j : ℕ) < k})
      = span K (x '' {j | (j : ℕ) < k}) := by
  set y := fun j ↦ x j + ∑ l ∈ Finset.Iio j, ξ j l • x l with hy
  refine le_antisymm (span_le.2 ?_) (span_le.2 ?_)
  · rintro _ ⟨j, hj, rfl⟩
    refine add_mem (subset_span ⟨j, hj, rfl⟩) (sum_mem fun l hl ↦ ?_)
    rw [Finset.mem_Iio] at hl
    have hlk : (l : ℕ) < k := lt_trans (Fin.lt_def.1 hl) hj
    exact smul_mem _ _ (subset_span ⟨l, hlk, rfl⟩)
  · have key : ∀ m : ℕ, ∀ j : Fin N, (j : ℕ) < m → (j : ℕ) < k →
        x j ∈ span K (y '' {j | (j : ℕ) < k}) := by
      intro m
      induction m with
      | zero => intro j hj; omega
      | succ m ih =>
        intro j hjm hjk
        have hxj : x j = y j - ∑ l ∈ Finset.Iio j, ξ j l • x l := by simp [hy]
        rw [hxj]
        refine sub_mem (subset_span ⟨j, hjk, rfl⟩) (sum_mem fun l hl ↦ ?_)
        rw [Finset.mem_Iio] at hl
        have hlj : (l : ℕ) < (j : ℕ) := Fin.lt_def.1 hl
        exact smul_mem _ _ (ih l (by omega) (by omega))
    rintro _ ⟨j, hj, rfl⟩
    exact key (j + 1) j (by omega) hj

end Submodule

namespace exteriorPower

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **The span of `Kⁱ` recovered from a subspace of the Plücker coordinates** (Bombieri–Gubler,
Lemma 7.5.33, read as a function of the subspace): the span of the vectors every one of whose
wedges lies in `U`. -/
noncomputable def recoverSpan (p : ℕ) (U : Submodule K (Set.powersetCard ι p → K)) :
    Submodule K (ι → K) :=
  Submodule.span K {u : ι → K | ∀ (ω : Fin p → ι → K) (b : Fin p), ω b = u → plucker p ω ∈ U}

/-- **Lemma 7.5.33 as a function**: the span of the first `k` members of a basis is recovered from
the span of the wedges that meet them. -/
theorem recoverSpan_wedgeSpan {x : Fin (Fintype.card ι) → ι → K} (hx : LinearIndependent K x)
    {k p : ℕ} (h : k + p = Fintype.card ι) :
    recoverSpan p (wedgeSpan k p x) = Submodule.span K (x '' {j | (j : ℕ) < k}) := by
  have hset : {u : ι → K | ∀ (ω : Fin p → ι → K) (b : Fin p), ω b = u →
        plucker p ω ∈ wedgeSpan k p x}
      = (Submodule.span K (x '' {j | (j : ℕ) < k}) : Set (ι → K)) :=
    Set.ext fun u ↦ (mem_span_iff_forall_plucker_mem_wedgeSpan hx h u).symm
  rw [recoverSpan, hset, Submodule.span_eq]

end exteriorPower
