/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Basic.Real.Basic

-- Used only inside proofs.
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# The greedy choice of a basis among weighted vectors

Let `g_i` (`i ∈ S`) be finitely many vectors carrying weights `e_i`. Among the subsets `I ⊆ S`
indexing a basis of their span, take one with the largest `∑_{i ∈ I} e_i`. Then for every
threshold set `T` closed upwards in the weights, `I ∩ T` has as many elements as the rank of the
`g_i` with `i ∈ S ∩ T`: otherwise some `j ∈ S ∩ T` is independent of `I ∩ T`, and an exchange
replaces an element of `I ∖ T`, of smaller weight, by `j`. So the best sum is read off the ranks of
the filtration `F^p = span {g_i : e_i ≥ p}`:
`∑_{i ∈ I} e_i = ∑_p p · (rank F^p − rank F^{>p})`, the weighted sum of the dimensions of the
graded pieces. This is the greedy algorithm for a linear matroid.

## Main results

* `finrank_span_image_eq_card`: an independent finite subfamily has its cardinality as rank.
* `card_filter_eq_finrank_span_of_isMax`: **the exchange step**.
* `sum_eq_sum_finrank_span_of_isMax`: **the best sum is the weighted sum of the graded ranks**.
-/

@[expose] public section

open Finset Module Submodule

variable {F α M : Type*} [Field F] [AddCommGroup M] [Module F M] {g : α → M}

/-- An independent finite subfamily spans a space of dimension its cardinality. -/
theorem finrank_span_image_eq_card {I : Finset α} (hI : LinearIndepOn F g (I : Set α)) :
    finrank F (span F (g '' I)) = #I := by
  rw [Set.image_eq_range]
  simpa using finrank_span_eq_card hI

variable {S I : Finset α} {e : α → ℝ}

/-- **The exchange step.** For a basis `I ⊆ S` of the span of the `g_i`, `i ∈ S`, with the largest
sum of weights, and an upward closed set `P` of indices, `#(I ∩ P)` is the rank of the `g_i` with
`i ∈ S ∩ P`. -/
theorem card_filter_eq_finrank_span_of_isMax (hIS : I ⊆ S) (hI : LinearIndepOn F g (I : Set α))
    (hcard : #I = finrank F (span F (g '' S)))
    (hmax : ∀ J ⊆ S, LinearIndepOn F g (J : Set α) → #J = finrank F (span F (g '' S)) →
      ∑ j ∈ J, e j ≤ ∑ i ∈ I, e i)
    (P : α → Prop) [DecidablePred P] (hP : ∀ i j, P i → e i ≤ e j → P j) :
    #(I.filter P) = finrank F (span F (g '' (S.filter P))) := by
  classical
  have hIP : LinearIndepOn F g ((I.filter P : Finset α) : Set α) :=
    hI.mono (Finset.coe_subset.2 (filter_subset _ _))
  have hfin : ∀ T : Finset α, FiniteDimensional F (span F (g '' T)) := fun T ↦
    FiniteDimensional.span_of_finite F (T.finite_toSet.image g)
  have hle : #(I.filter P) ≤ finrank F (span F (g '' (S.filter P))) := by
    rw [← finrank_span_image_eq_card hIP]
    exact Submodule.finrank_mono (span_mono (Set.image_mono
      (Finset.coe_subset.2 (filter_subset_filter _ hIS))))
  refine le_antisymm hle (not_lt.1 fun hlt ↦ ?_)
  obtain ⟨j, hjS, hjI⟩ : ∃ j ∈ S.filter P, g j ∉ span F (g '' (I.filter P)) := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have hsp : span F (g '' (S.filter P)) ≤ span F (g '' (I.filter P)) :=
      span_le.2 (by rintro _ ⟨j, hj, rfl⟩; exact h j hj)
    have := Submodule.finrank_mono hsp
    rw [finrank_span_image_eq_card hIP] at this
    omega
  have hjP : P j := (mem_filter.1 hjS).2
  have hjS' : j ∈ S := (mem_filter.1 hjS).1
  have hjnI : j ∉ I := fun h ↦
    hjI (subset_span (Set.mem_image_of_mem g (Finset.mem_coe.2 (mem_filter.2 ⟨h, hjP⟩))))
  have hind : LinearIndepOn F g (insert j ((I.filter P : Finset α) : Set α)) := hIP.insert hjI
  obtain ⟨b, hbt, hsb, hspan, hb⟩ := exists_linearIndepOn_extension hind
    (t := insert j (I : Set α)) (Set.insert_subset_insert
      (Finset.coe_subset.2 (filter_subset _ _)))
  set J : Finset α := (insert j I).filter (· ∈ b) with hJdef
  have hJb : (J : Set α) = b := by
    ext i
    simp only [hJdef, coe_filter, Finset.mem_insert, Set.mem_ofPred_eq]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨by simpa using hbt h, h⟩⟩
  have hJ : LinearIndepOn F g (J : Set α) := hJb ▸ hb
  have hJS : J ⊆ S := fun i hi ↦ by
    rcases Finset.mem_insert.1 (mem_filter.1 hi).1 with rfl | hi
    · exact hjS'
    · exact hIS hi
  have hJcard : #J = finrank F (span F (g '' S)) := by
    refine le_antisymm ?_ ?_
    · rw [← finrank_span_image_eq_card hJ]
      exact Submodule.finrank_mono (span_mono (Set.image_mono (Finset.coe_subset.2 hJS)))
    · rw [← hcard, ← finrank_span_image_eq_card hI, ← finrank_span_image_eq_card hJ]
      refine Submodule.finrank_mono (span_le.2 ?_)
      rw [hJb]
      exact (Set.image_mono (Set.subset_insert _ _)).trans hspan
  have hjJ : j ∈ J := mem_filter.2 ⟨Finset.mem_insert_self _ _, hsb (Set.mem_insert _ _)⟩
  obtain ⟨i, hiI, hiJ⟩ : ∃ i ∈ I, i ∉ J := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have : insert j I ⊆ J := Finset.insert_subset hjJ h
    have := Finset.card_le_card this
    rw [Finset.card_insert_of_notMem hjnI] at this
    omega
  have hiP : ¬ P i := fun h ↦
    hiJ (mem_filter.2 ⟨Finset.mem_insert_of_mem hiI, hsb (Set.mem_insert_of_mem _
      (Finset.mem_coe.2 (mem_filter.2 ⟨hiI, h⟩)))⟩)
  have hei : e i < e j := lt_of_not_ge fun h ↦ hiP (hP j i hjP h)
  have hJeq : J = insert j (I.erase i) := by
    refine Finset.eq_of_subset_of_card_le (fun k hk ↦ ?_) ?_
    · rcases Finset.mem_insert.1 (mem_filter.1 hk).1 with rfl | hk'
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨fun h ↦ hiJ (h ▸ hk), hk'⟩)
    · rw [Finset.card_insert_of_notMem (fun h ↦ hjnI (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem hiI, hJcard, ← hcard]
      have := Finset.card_pos.2 ⟨i, hiI⟩
      omega
  have hsum := hmax J hJS hJ hJcard
  rw [hJeq, Finset.sum_insert (fun h ↦ hjnI (Finset.mem_of_mem_erase h)),
    Finset.sum_erase_eq_sub hiI] at hsum
  linarith

/-- **The best sum is the weighted sum of the graded ranks**:
`∑_{i ∈ I} e_i = ∑_p p · (rank F^p − rank F^{>p})` over the weights `p` that occur, where
`F^p` is spanned by the `g_i` with `e_i ≥ p` and `F^{>p}` by those with `e_i > p`. -/
theorem sum_eq_sum_finrank_span_of_isMax (hIS : I ⊆ S) (hI : LinearIndepOn F g (I : Set α))
    (hcard : #I = finrank F (span F (g '' S)))
    (hmax : ∀ J ⊆ S, LinearIndepOn F g (J : Set α) → #J = finrank F (span F (g '' S)) →
      ∑ j ∈ J, e j ≤ ∑ i ∈ I, e i) :
    ∑ i ∈ I, e i = ∑ p ∈ S.image e, p *
      ((finrank F (span F (g '' (S.filter (p ≤ e ·)))) : ℝ) -
        finrank F (span F (g '' (S.filter (p < e ·))))) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := e) (t := S.image e)
    (fun i hi ↦ Finset.mem_image_of_mem e (hIS hi))]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [← card_filter_eq_finrank_span_of_isMax hIS hI hcard hmax _
      (fun _ _ h h' ↦ h.trans h'),
    ← card_filter_eq_finrank_span_of_isMax hIS hI hcard hmax _
      (fun _ _ h h' ↦ h.trans_le h')]
  have hsplit : I.filter (p ≤ e ·) = I.filter (p < e ·) ∪ I.filter (e · = p) := by
    ext i
    simp only [mem_filter, mem_union, le_iff_lt_or_eq, eq_comm (a := p)]
    tauto
  have hdisj : Disjoint (I.filter (p < e ·)) (I.filter (e · = p)) :=
    Finset.disjoint_filter.2 fun _ _ h h' ↦ h.ne' h'
  rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.sum_congr rfl fun i hi ↦
    (mem_filter.1 hi).2, Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

