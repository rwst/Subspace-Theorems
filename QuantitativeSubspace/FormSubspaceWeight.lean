/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.LinearAlgebra.WeightFiltration
public import QuantitativeSubspace.FormSuccessiveInfima

-- Used only inside proofs.
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The weight of a subspace

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, (2.19)–(2.21), Lemma 7.3 (ii), (iii) and §15.

For linear forms `ℓ_1, …, ℓ_n` on a vector space `V` with `⋂ ker ℓ_i = 0` and reals `c_i`, the
weight of a subspace `U` is the least `Σ_{i ∈ I} c_i` over the sets `I` of `dim U` indices with
`(ℓ_i|_U)_{i ∈ I}` linearly independent (EF13 (2.19)). For a system of forms `L` and exponents
`c` over a number field `K`, the weight `w_{L,c}(U)` of a subspace `U ⊆ Ωⁿ` is the sum of these
over all places of `K` (EF13 (2.20)).

Ordering the indices so that `c` increases, with `U_j = ker ℓ_1 ∩ ⋯ ∩ ker ℓ_j`, the greedy choice
of `I` is optimal and

```text
w(U) = Σ_j c_j (dim (U ∩ U_{j-1}) - dim (U ∩ U_j))
     = c_1 dim U + Σ_j (c_{j+1} - c_j) dim (U ∩ U_j)          (EF13 (15.3), (15.4)).
```

The second form is a combination with nonnegative coefficients of `dim U`, which is modular, and
of the `dim (U ∩ U_j)`, which are supermodular; so `w` is supermodular (EF13 Lemma 15.1), and the
destabilizing subspace and the filtration of `ForMathlib/LinearAlgebra/WeightFiltration.lean`
exist for it. Both are invariant under Galois conjugation, which preserves dimensions and the
kernels of the forms, hence they are defined over `K` (ES02 Lemma 4.2).

## Main definitions

* `Submodule.formWeight ℓ c U`: the local weight (2.19), with `Submodule.IsFormBasis`.
* `Submodule.formChain ℓ e j`: the spaces `U_j` for an ordering `e` of the indices.
* `NumberField.galoisIso σ`: Galois conjugation of the subspaces of `Ωⁿ`.
* `NumberField.FormSystem.matrixForms A`: the rows of a matrix over `K` as forms on `Ωⁿ`.
* `NumberField.FormSystem.subspaceWeight L c U`: EF13's `w_{L,c}(U)` (2.20).

## Main results

* `Submodule.isLeast_formWeight`, `Submodule.formWeight_eq_sum`,
  `Submodule.formWeight_eq_sum_range`: EF13 (15.3), (15.4).
* `Submodule.isSupermodularWeight_formWeight`,
  `NumberField.FormSystem.isSupermodularWeight_subspaceWeight`: EF13 Lemma 15.1.
* `NumberField.FormSystem.finite_range_subspaceWeight`: `w` takes finitely many values.
* `Submodule.formWeight_orderIso`: transport of the weight along lattice isomorphisms.
* `NumberField.FormSystem.subspaceWeight_galoisIso`: Galois invariance.
* `NumberField.FormSystem.isDefinedOver_of_isDestabilizing`,
  `NumberField.FormSystem.isDefinedOver_of_isWeightFiltration`,
  `NumberField.FormSystem.exists_isDestabilizing_top`,
  `NumberField.FormSystem.exists_isWeightFiltration_top`: EF13 Lemmas 15.2 (i) and 15.4 for
  `w_{L,c}`, with the subspaces defined over `K`; the first is `T(L, c)` of (2.21).
* `NumberField.FormSystem.subspaceWeight_comp`,
  `NumberField.FormSystem.isDestabilizing_comap_comp`: EF13 Lemma 7.3 (ii), (iii).

## Implementation notes

The weight is defined by EF13's minimum (2.19) and identified with (15.4) through the greedy
basis for any increasing ordering (`Submodule.greedy`, by ranks of initial spans of the
restricted forms), with a summation by parts (`Submodule.sum_le_sum_of_card_filter_le`) for the
optimality. The weight of a place where all `c_iv = 0` is `0`, so the sum over the finite places
is a finite sum.

This is milestone Q3.2 of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Module Finset

namespace Submodule

/-! ### The greedy basis of a sequence of forms -/

section Greedy

variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  (f : ℕ → Module.Dual k W)

/-- The span of the first `j` forms. -/
noncomputable def spanFirst (j : ℕ) : Submodule k (Module.Dual k W) := span k (f '' Set.Iio j)

omit [FiniteDimensional k W] in
theorem spanFirst_succ (j : ℕ) : spanFirst f (j + 1) = k ∙ f j ⊔ spanFirst f j := by
  rw [spanFirst, spanFirst, ← span_insert, ← Set.image_insert_eq, Set.Iio_insert]
  congr 2
  ext i
  simp

open scoped Classical in
/-- **The greedy basis** among the first `j` forms: the indices `i < j` with `f i` not in the span
of the earlier forms. -/
noncomputable def greedy (j : ℕ) : Finset ℕ := (range j).filter fun i ↦ f i ∉ spanFirst f i

omit [FiniteDimensional k W] in
open scoped Classical in
theorem greedy_succ (j : ℕ) :
    greedy f (j + 1) = if f j ∈ spanFirst f j then greedy f j else insert j (greedy f j) := by
  rw [greedy, greedy, range_add_one, filter_insert]
  split_ifs <;> rfl

omit [FiniteDimensional k W] in
theorem notMem_greedy_self (j : ℕ) : j ∉ greedy f j := by
  simp [greedy]

omit [FiniteDimensional k W] in
theorem greedy_subset_range (j : ℕ) : greedy f j ⊆ range j := by
  classical
  intro i hi
  rw [greedy, mem_filter] at hi
  exact hi.1

theorem card_greedy (j : ℕ) : #(greedy f j) = finrank k (spanFirst f j) := by
  classical
  induction j with
  | zero =>
    have : Set.Iio (0 : ℕ) = ∅ := Set.eq_empty_of_forall_notMem fun x hx ↦ Nat.not_lt_zero x hx
    have h0 : greedy f 0 = ∅ := by
      ext i
      simp [greedy]
    rw [h0, card_empty, spanFirst, this, Set.image_empty, span_empty, finrank_bot]
  | succ j ih =>
    rw [greedy_succ, spanFirst_succ]
    split_ifs with h
    · rw [ih, sup_eq_right.2 ((span_singleton_le_iff_mem _ _).2 h)]
    · have h0 : f j ≠ 0 := fun h0 ↦ h (h0 ▸ zero_mem _)
      have hd : Disjoint (spanFirst f j) (k ∙ f j) := (disjoint_span_singleton' h0).2 h
      have := finrank_sup_add_finrank_inf_eq (k ∙ f j) (spanFirst f j)
      rw [inf_comm, hd.eq_bot, finrank_bot, finrank_span_singleton h0] at this
      rw [card_insert_of_notMem (notMem_greedy_self f j), ih]
      omega

omit [FiniteDimensional k W] in
theorem linearIndepOn_greedy (j : ℕ) : LinearIndepOn k f (greedy f j : Set ℕ) := by
  classical
  induction j with
  | zero => simp [greedy]
  | succ j ih =>
    rw [greedy_succ]
    split_ifs with h
    · exact ih
    · rw [coe_insert, linearIndepOn_insert (by exact_mod_cast notMem_greedy_self f j)]
      refine ⟨ih, fun hs ↦ h (span_mono ?_ hs)⟩
      refine Set.image_mono fun i hi ↦ ?_
      exact Set.mem_Iio.2 (mem_range.1 (greedy_subset_range f j hi))

omit [FiniteDimensional k W] in
theorem filter_greedy {j n : ℕ} (h : j ≤ n) : (greedy f n).filter (· < j) = greedy f j := by
  ext i
  simp only [greedy, mem_filter, mem_range]
  constructor
  · rintro ⟨⟨-, hi⟩, hij⟩
    exact ⟨hij, hi⟩
  · rintro ⟨hij, hi⟩
    exact ⟨⟨by omega, hi⟩, hij⟩

/-- Independent forms among the first `j` number at most the rank of these forms. -/
theorem card_filter_le_finrank {I : Finset ℕ} (hI : LinearIndepOn k f (I : Set ℕ)) (j : ℕ) :
    #(I.filter (· < j)) ≤ finrank k (spanFirst f j) := by
  set S := I.filter (· < j)
  have hS : LinearIndependent k (fun i : S ↦ f i) := hI.mono fun x hx ↦ (mem_filter.1 hx).1
  have h1 := linearIndependent_iff_card_eq_finrank_span.1 hS
  rw [Fintype.card_coe] at h1
  rw [h1, Set.finrank]
  refine finrank_mono (span_mono ?_)
  rintro _ ⟨i, rfl⟩
  exact ⟨i, Set.mem_Iio.2 (mem_filter.1 i.2).2, rfl⟩

/-- `dim (⋂_{i < j} ker f_i) + dim span (f_i)_{i < j} = dim W`. -/
theorem finrank_iInf_ker_add (j : ℕ) :
    finrank k ↥(⨅ (i : ℕ) (_ : i < j), LinearMap.ker (f i)) + finrank k (spanFirst f j) =
      finrank k W := by
  have h := Subspace.finrank_add_finrank_dualCoannihilator_eq (spanFirst f j)
  have he : (spanFirst f j).dualCoannihilator = ⨅ (i : ℕ) (_ : i < j), LinearMap.ker (f i) := by
    refine SetLike.coe_injective ?_
    rw [spanFirst, coe_dualCoannihilator_span]
    ext x
    simp
  rw [he] at h
  omega

end Greedy

/-! ### Sums by parts -/

/-- Summation by parts. -/
theorem sum_range_mul_sub_eq (c a : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ range (m + 1), c j * (a (j + 1) - a j) =
      c m * a (m + 1) - c 0 * a 0 - ∑ j ∈ range m, (c (j + 1) - c j) * a (j + 1) := by
  induction m with
  | zero => simp; ring
  | succ m ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    ring

/-- `∑_{i ∈ A} c_i` through the counts `#{i ∈ A : i < j}`. -/
theorem sum_eq_sum_range_mul_card {A : Finset ℕ} {n : ℕ} (hA : A ⊆ range n) (c : ℕ → ℝ) :
    ∑ i ∈ A, c i =
      ∑ j ∈ range n, c j * ((#(A.filter (· < j + 1)) : ℝ) - #(A.filter (· < j))) := by
  classical
  have h : ∀ j, (#(A.filter (· < j + 1)) : ℝ) - #(A.filter (· < j)) = if j ∈ A then 1 else 0 := by
    intro j
    have : A.filter (· < j + 1) = (A.filter (· < j)) ∪ A.filter (· = j) := by
      ext i
      simp only [mem_filter, mem_union]
      constructor
      · rintro ⟨hi, hij⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
        · exact Or.inl ⟨hi, h⟩
        · exact Or.inr ⟨hi, h⟩
      · rintro (⟨hi, h⟩ | ⟨hi, h⟩) <;> exact ⟨hi, by omega⟩
    rw [this, card_union_of_disjoint (disjoint_filter.2 fun _ _ h h' ↦ by omega),
      filter_eq' A j]
    split_ifs <;> simp
  simp only [h, mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  exact ⟨fun hi ↦ ⟨mem_range.1 (hA hi), hi⟩, fun hi ↦ hi.2⟩

/-- If `I` and `J` have the same size, inside `[0, n)`, and every initial segment `[0, j)` meets
`I` in at most as many points as `J`, then `∑_J c ≤ ∑_I c` for `c` increasing on `[0, n)`. -/
theorem sum_le_sum_of_card_filter_le {I J : Finset ℕ} {n : ℕ} (hI : I ⊆ range n)
    (hJ : J ⊆ range n) (hcard : #I = #J) (hle : ∀ j, #(I.filter (· < j)) ≤ #(J.filter (· < j)))
    {c : ℕ → ℝ} (hc : ∀ j, j + 1 < n → c j ≤ c (j + 1)) :
    ∑ i ∈ J, c i ≤ ∑ i ∈ I, c i := by
  rw [sum_eq_sum_range_mul_card hI, sum_eq_sum_range_mul_card hJ]
  rcases n with _ | m
  · simp
  have hfull : ∀ A : Finset ℕ, A ⊆ range (m + 1) → A.filter (· < m + 1) = A := fun A hA ↦
    filter_true_of_mem fun i hi ↦ mem_range.1 (hA hi)
  have hI' := sum_range_mul_sub_eq c (fun j ↦ (#(I.filter (· < j)) : ℝ)) m
  have hJ' := sum_range_mul_sub_eq c (fun j ↦ (#(J.filter (· < j)) : ℝ)) m
  rw [hI', hJ']
  have h0 : ∀ A : Finset ℕ, A.filter (· < 0) = ∅ := fun A ↦ filter_false_of_mem fun i _ ↦
    Nat.not_lt_zero i
  simp only [hfull I hI, hfull J hJ, hcard, h0, card_empty, Nat.cast_zero, mul_zero, sub_zero]
  rw [sub_le_sub_iff_left]
  refine sum_le_sum fun j hj ↦ mul_le_mul_of_nonneg_left (Nat.cast_le.2 (hle _)) ?_
  exact sub_nonneg.2 (hc j (by simpa using hj))

/-! ### The weight of a subspace with respect to a family of forms -/

section FormWeight

variable {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [Finite ι] (ℓ : ι → Module.Dual k V) (c : ι → ℝ)

/-- `I` indexes a basis of the dual of `U` among the restrictions `ℓ_i|_U`: `#I = dim U` and the
`ℓ_i|_U`, `i ∈ I`, are linearly independent. -/
def IsFormBasis (U : Submodule k V) (I : Finset ι) : Prop :=
  #I = finrank k U ∧ LinearIndepOn k (fun i ↦ (ℓ i).domRestrict U) (I : Set ι)

/-- **The local weight** of EF13 (2.19): the least `Σ_{i ∈ I} c_i` over the `I` with
`(ℓ_i|_U)_{i ∈ I}` a basis of the dual of `U`. -/
noncomputable def formWeight (U : Submodule k V) : ℝ :=
  sInf ((fun I : Finset ι ↦ ∑ i ∈ I, c i) '' {I | IsFormBasis ℓ U I})

/-- The common kernel `U_j` of the first `j` forms in the order `e` (EF13 §15). -/
noncomputable def formChain {n : ℕ} (e : Fin n ≃ ι) (j : ℕ) : Submodule k V :=
  ⨅ (i : Fin n) (_ : (i : ℕ) < j), LinearMap.ker (ℓ (e i))

omit [FiniteDimensional k V] [Finite ι] in
/-- The indices can be ordered so that `c` increases (EF13 (15.1)). -/
theorem exists_monotone_equiv [Fintype ι] : ∃ e : Fin (Fintype.card ι) ≃ ι, Monotone (c ∘ e) :=
  ⟨(Tuple.sort (c ∘ (Fintype.equivFin ι).symm)).trans (Fintype.equivFin ι).symm,
    Tuple.monotone_sort (c ∘ (Fintype.equivFin ι).symm)⟩

omit [FiniteDimensional k V] [Finite ι] in
theorem formChain_zero {n : ℕ} (e : Fin n ≃ ι) : formChain ℓ e 0 = ⊤ := by
  simp [formChain]

omit [FiniteDimensional k V] [Finite ι] in
theorem formChain_eq_bot (hℓ : ⨅ i, LinearMap.ker (ℓ i) = ⊥) {n : ℕ} (e : Fin n ≃ ι) {j : ℕ}
    (hj : n ≤ j) : formChain ℓ e j = ⊥ := by
  rw [← hℓ, ← e.iInf_comp, formChain]
  congr 1
  ext i
  simp [show (i : ℕ) < j by omega]

/-- **EF13 (15.3), (15.4)**, as the least element: if `e` orders the indices so that `c`
increases, then `Σ_j c_{e j} (dim (U ∩ U_j) - dim (U ∩ U_{j+1}))` is the least sum over a basis,
attained by the greedy basis. -/
theorem isLeast_formWeight (hℓ : ⨅ i, LinearMap.ker (ℓ i) = ⊥) {n : ℕ} (e : Fin n ≃ ι)
    (he : Monotone (c ∘ e)) (U : Submodule k V) :
    IsLeast ((fun I : Finset ι ↦ ∑ i ∈ I, c i) '' {I | IsFormBasis ℓ U I})
      (∑ j : Fin n, c (e j) *
        ((finrank k ↥(U ⊓ formChain ℓ e j) : ℝ) - finrank k ↥(U ⊓ formChain ℓ e (j + 1)))) := by
  classical
  have := Fintype.ofFinite ι
  set F : ℕ → Module.Dual k U :=
    fun j ↦ if h : j < n then (ℓ (e ⟨j, h⟩)).domRestrict U else 0 with hF
  set C : ℕ → ℝ := fun j ↦ if h : j < n then c (e ⟨j, h⟩) else 0 with hC
  have hCm : ∀ j, j + 1 < n → C j ≤ C (j + 1) := fun j hj ↦ by
    simp only [hC, hj, show j < n by omega, dite_true]
    exact he (Fin.mk_le_mk.2 (Nat.le_succ j))
  -- The chain inside `U` and its dimensions.
  have hchain : ∀ j ≤ n,
      finrank k ↥(U ⊓ formChain ℓ e j) + finrank k (spanFirst F j) = finrank k U := by
    intro j hj
    rw [← finrank_iInf_ker_add F j]
    congr 1
    have h1 : (⨅ (i : ℕ) (_ : i < j), LinearMap.ker (F i)) =
        comap U.subtype (U ⊓ formChain ℓ e j) := by
      ext x
      simp only [mem_iInf, LinearMap.mem_ker, mem_comap, subtype_apply, mem_inf,
        SetLike.coe_mem, true_and, formChain]
      constructor
      · intro h i hi
        simpa [hF, show (i : ℕ) < n from i.2] using h i hi
      · intro h i hi
        simpa [hF, show i < n by omega] using h ⟨i, by omega⟩ hi
    rw [h1]
    exact (comapSubtypeEquivOfLe inf_le_left).finrank_eq.symm
  have hspan : finrank k (spanFirst F n) = finrank k U := by
    have := hchain n le_rfl
    rw [formChain_eq_bot ℓ hℓ e le_rfl, inf_bot_eq, finrank_bot, zero_add] at this
    exact this
  -- Finite sets of indices, transported to `ℕ`.
  set φ : ι ↪ ℕ := e.symm.toEmbedding.trans Fin.valEmbedding with hφ
  have hφn : ∀ i, φ i < n := fun i ↦ (e.symm i).2
  have hFφ : F ∘ φ = fun i ↦ (ℓ i).domRestrict U := by
    funext i
    simp [hF, hφ, (e.symm i).2]
  have hCφ : ∀ i, C (φ i) = c i := fun i ↦ by simp [hC, hφ, (e.symm i).2]
  have hbasis : ∀ I : Finset ι,
      IsFormBasis ℓ U I ↔ #(I.map φ) = finrank k U ∧ LinearIndepOn k F ↑(I.map φ) := by
    intro I
    rw [IsFormBasis, card_map, coe_map, ← hFφ]
    refine and_congr Iff.rfl ⟨LinearIndepOn.image_of_comp _ _, fun h ↦ ?_⟩
    exact h.comp_of_image φ.injective.injOn
  have hsum : ∀ I : Finset ι, ∑ i ∈ I, c i = ∑ j ∈ I.map φ, C j := fun I ↦ by
    simp [sum_map, hCφ]
  -- The greedy basis and its sum.
  set G : Finset ι := univ.filter fun i ↦ φ i ∈ greedy F n
  have hG : G.map φ = greedy F n := by
    ext j
    simp only [Finset.mem_map, mem_filter, mem_univ, true_and, G]
    refine ⟨fun ⟨i, hi, hij⟩ ↦ hij ▸ hi, fun hj ↦ ?_⟩
    have hjn := mem_range.1 (greedy_subset_range F n hj)
    exact ⟨e ⟨j, hjn⟩, by simpa [hφ] using hj, by simp [hφ]⟩
  have hval : ∑ j ∈ greedy F n, C j = ∑ j : Fin n, c (e j) *
      ((finrank k ↥(U ⊓ formChain ℓ e j) : ℝ) - finrank k ↥(U ⊓ formChain ℓ e (j + 1))) := by
    rw [sum_eq_sum_range_mul_card (greedy_subset_range F n),
      ← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun j _ ↦ ?_
    have hj := j.2
    rw [filter_greedy F (show (j : ℕ) + 1 ≤ n by omega), filter_greedy F hj.le, card_greedy,
      card_greedy]
    have h1 := hchain j hj.le
    have h2 := hchain (j + 1) (by omega)
    simp only [hC, hj, dite_true, Fin.eta]
    congr 1
    have h1' : ((finrank k ↥(U ⊓ formChain ℓ e j) : ℕ) : ℝ) + finrank k (spanFirst F j) =
        finrank k U := by exact_mod_cast h1
    have h2' : ((finrank k ↥(U ⊓ formChain ℓ e (j + 1)) : ℕ) : ℝ) +
        finrank k (spanFirst F (j + 1)) = finrank k U := by exact_mod_cast h2
    linarith
  -- Every basis has at least this sum.
  have hlow : ∀ I, IsFormBasis ℓ U I → ∑ i ∈ greedy F n, C i ≤ ∑ i ∈ I, c i := by
    intro I hI
    obtain ⟨hcard, hli⟩ := (hbasis I).1 hI
    rw [hsum]
    have hsub : I.map φ ⊆ range n := fun j hj ↦ by
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
      exact mem_range.2 (hφn i)
    have hcard' : #(I.map φ) = #(greedy F n) := by rw [hcard, card_greedy, hspan]
    refine sum_le_sum_of_card_filter_le hsub (greedy_subset_range F n) hcard' (fun j ↦ ?_) hCm
    rcases le_or_gt j n with hj | hj
    · rw [filter_greedy F hj, card_greedy]
      exact card_filter_le_finrank F hli j
    · rw [filter_true_of_mem fun i hi ↦ (mem_range.1 (greedy_subset_range F n hi)).trans hj]
      exact (card_filter_le _ _).trans hcard'.le
  have hmem : ∑ i ∈ greedy F n, C i ∈
      (fun I : Finset ι ↦ ∑ i ∈ I, c i) '' {I | IsFormBasis ℓ U I} := by
    refine ⟨G, (hbasis G).2 ⟨by rw [hG, card_greedy, hspan], ?_⟩, ?_⟩
    · rw [hG]
      exact linearIndepOn_greedy F n
    change ∑ i ∈ G, c i = _
    rw [hsum, hG]
  rw [← hval]
  exact ⟨hmem, by rintro _ ⟨I, hI, rfl⟩; exact hlow I hI⟩

/-- **EF13 (15.3), (15.4)**: if `e` orders the indices so that `c` increases, then the weight is
`Σ_j c_{e j} (dim (U ∩ U_j) - dim (U ∩ U_{j+1}))`. -/
theorem formWeight_eq_sum (hℓ : ⨅ i, LinearMap.ker (ℓ i) = ⊥) {n : ℕ} (e : Fin n ≃ ι)
    (he : Monotone (c ∘ e)) (U : Submodule k V) :
    formWeight ℓ c U = ∑ j : Fin n, c (e j) *
      ((finrank k ↥(U ⊓ formChain ℓ e j) : ℝ) - finrank k ↥(U ⊓ formChain ℓ e (j + 1))) :=
  (isLeast_formWeight ℓ c hℓ e he U).csInf_eq

/-- The minimum in the definition of the weight is attained. -/
theorem formWeight_mem (hℓ : ⨅ i, LinearMap.ker (ℓ i) = ⊥) (U : Submodule k V) :
    formWeight ℓ c U ∈ (fun I : Finset ι ↦ ∑ i ∈ I, c i) '' {I | IsFormBasis ℓ U I} := by
  have := Fintype.ofFinite ι
  obtain ⟨e, he⟩ := exists_monotone_equiv c
  rw [formWeight_eq_sum ℓ c hℓ e he]
  exact (isLeast_formWeight ℓ c hℓ e he U).1

/-- With all `c_i = 0` the weight is `0`. -/
theorem formWeight_zero (hℓ : ⨅ i, LinearMap.ker (ℓ i) = ⊥) (U : Submodule k V) :
    formWeight ℓ 0 U = 0 := by
  obtain ⟨I, -, hI⟩ := formWeight_mem ℓ 0 hℓ U
  rw [← hI]
  simp

/-- The weight after summation by parts:
`c_{e 0} dim U + Σ_{j < m} (c_{e (j+1)} - c_{e j}) dim (U ∩ U_{j+1})`, for `n = m + 1` forms. -/
theorem formWeight_eq_sum_range (hℓ : ⨅ i, LinearMap.ker (ℓ i) = ⊥) {m : ℕ}
    (e : Fin (m + 1) ≃ ι) (he : Monotone (c ∘ e)) {C : ℕ → ℝ}
    (hC : ∀ j (h : j < m + 1), C j = c (e ⟨j, h⟩)) (U : Submodule k V) :
    formWeight ℓ c U = C 0 * finrank k U +
      ∑ j ∈ range m, (C (j + 1) - C j) * finrank k ↥(U ⊓ formChain ℓ e (j + 1)) := by
  rw [formWeight_eq_sum ℓ c hℓ e he]
  set g : ℕ → ℝ := fun j ↦ finrank k ↥(U ⊓ formChain ℓ e j)
  have h1 : ∑ j : Fin (m + 1), c (e j) *
      ((finrank k ↥(U ⊓ formChain ℓ e j) : ℝ) - finrank k ↥(U ⊓ formChain ℓ e (j + 1))) =
      ∑ j ∈ range (m + 1), C j * ((fun j ↦ -g j) (j + 1) - (fun j ↦ -g j) j) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [hC j j.2]
    simp only [g, Fin.eta]
    ring
  rw [h1, sum_range_mul_sub_eq C (fun j ↦ -g j) m]
  have hg0 : g 0 = finrank k U := by simp only [g]; rw [formChain_zero, inf_top_eq]
  have hgm : g (m + 1) = 0 := by simp [g, formChain_eq_bot ℓ hℓ e le_rfl]
  simp only [hg0, hgm, g]
  simp only [mul_neg, sum_neg_distrib, neg_zero, mul_zero]
  ring

omit [FiniteDimensional k V] [Finite ι] in
/-- `U ↦ dim (U ∩ X)` is supermodular. -/
theorem finrank_inf_add_finrank_inf_le [FiniteDimensional k V] (X U₁ U₂ : Submodule k V) :
    finrank k ↥(U₁ ⊓ X) + finrank k ↥(U₂ ⊓ X) ≤
      finrank k ↥(U₁ ⊓ U₂ ⊓ X) + finrank k ↥((U₁ ⊔ U₂) ⊓ X) := by
  have h := finrank_sup_add_finrank_inf_eq (U₁ ⊓ X) (U₂ ⊓ X)
  have h1 : U₁ ⊓ X ⊓ (U₂ ⊓ X) = U₁ ⊓ U₂ ⊓ X := by
    rw [inf_inf_inf_comm, inf_idem]
  have h2 : U₁ ⊓ X ⊔ U₂ ⊓ X ≤ (U₁ ⊔ U₂) ⊓ X :=
    sup_le (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right)
  rw [h1] at h
  have := finrank_mono h2
  omega

/-- **EF13 Lemma 15.1**, local form: the weight is supermodular. -/
theorem isSupermodularWeight_formWeight (hℓ : ⨅ i, LinearMap.ker (ℓ i) = ⊥) :
    IsSupermodularWeight (formWeight ℓ c) := by
  intro U₁ U₂
  have := Fintype.ofFinite ι
  obtain ⟨e, he⟩ := exists_monotone_equiv c
  generalize Fintype.card ι = n at e
  rcases n with _ | m
  · simp [formWeight_eq_sum ℓ c hℓ e he]
  set C : ℕ → ℝ := fun j ↦ if h : j < m + 1 then c (e ⟨j, h⟩) else 0
  have hC : ∀ j (h : j < m + 1), C j = c (e ⟨j, h⟩) := fun j h ↦ by simp [C, Nat.le_of_lt_succ h]
  simp only [formWeight_eq_sum_range ℓ c hℓ e he hC]
  have h0 : (finrank k U₁ : ℝ) + finrank k U₂ = finrank k ↥(U₁ ⊓ U₂) + finrank k ↥(U₁ ⊔ U₂) := by
    have := finrank_sup_add_finrank_inf_eq U₁ U₂
    exact_mod_cast (by omega : finrank k U₁ + finrank k U₂ =
      finrank k ↥(U₁ ⊓ U₂) + finrank k ↥(U₁ ⊔ U₂))
  have hj : ∀ j ∈ range m,
      (C (j + 1) - C j) * finrank k ↥(U₁ ⊓ formChain ℓ e (j + 1)) +
        (C (j + 1) - C j) * finrank k ↥(U₂ ⊓ formChain ℓ e (j + 1)) ≤
      (C (j + 1) - C j) * finrank k ↥(U₁ ⊓ U₂ ⊓ formChain ℓ e (j + 1)) +
        (C (j + 1) - C j) * finrank k ↥((U₁ ⊔ U₂) ⊓ formChain ℓ e (j + 1)) := by
    intro j hj
    have hd : 0 ≤ C (j + 1) - C j := by
      have hj := mem_range.1 hj
      rw [hC j (by omega), hC (j + 1) (by omega), sub_nonneg]
      exact he (Fin.mk_le_mk.2 (Nat.le_succ j))
    rw [← mul_add, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ hd
    exact_mod_cast finrank_inf_add_finrank_inf_le _ U₁ U₂
  have := sum_le_sum hj
  rw [sum_add_distrib, sum_add_distrib] at this
  have h0' := congrArg (C 0 * ·) h0
  simp only [mul_add] at h0'
  linarith

/-- The weight takes finitely many values. -/
theorem finite_range_formWeight (hℓ : ⨅ i, LinearMap.ker (ℓ i) = ⊥) :
    (Set.range (formWeight ℓ c)).Finite := by
  refine (Set.finite_range fun I : Finset ι ↦ ∑ i ∈ I, c i).subset ?_
  rintro _ ⟨U, rfl⟩
  obtain ⟨I, -, hI⟩ := formWeight_mem ℓ c hℓ U
  exact ⟨I, hI⟩

/-- **Transport of the weight** (EF13 Lemma 7.3 (ii), and Galois invariance): an isomorphism of
the lattices of subspaces that preserves dimensions and maps each `ker ℓ_i` to `ker ℓ'_i`
preserves the weight. -/
theorem formWeight_orderIso {V' : Type*} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    (ℓ' : ι → Module.Dual k V') (hℓ : ⨅ i, LinearMap.ker (ℓ i) = ⊥)
    (hℓ' : ⨅ i, LinearMap.ker (ℓ' i) = ⊥) (E : Submodule k V ≃o Submodule k V')
    (hE : ∀ W, finrank k ↥(E W) = finrank k W)
    (hker : ∀ i, E (LinearMap.ker (ℓ i)) = LinearMap.ker (ℓ' i)) (U : Submodule k V) :
    formWeight ℓ' c (E U) = formWeight ℓ c U := by
  have := Fintype.ofFinite ι
  obtain ⟨e, he⟩ := exists_monotone_equiv c
  rw [formWeight_eq_sum ℓ c hℓ e he, formWeight_eq_sum ℓ' c hℓ' e he]
  have hch : ∀ j, E (formChain ℓ e j) = formChain ℓ' e j := fun j ↦ by
    simp only [formChain, OrderIso.map_iInf, hker]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [← hch, ← hch, ← E.map_inf, ← E.map_inf, hE, hE]

end FormWeight

end Submodule

namespace NumberField

open Submodule

/-! ### Galois conjugation of subspaces -/

section Galois

variable {Ω ι : Type*} [Field Ω]

/-- Coordinatewise application of a ring endomorphism of `Ω`, a semilinear map of `Ωⁿ`. -/
def galoisLin (τ : Ω →+* Ω) : (ι → Ω) →ₛₗ[τ] (ι → Ω) where
  toFun x := τ ∘ x
  map_add' _ _ := funext fun _ ↦ map_add τ _ _
  map_smul' _ _ := funext fun _ ↦ map_mul τ _ _

/-- **Galois conjugation of subspaces**: `σ(U) = {σ ∘ x : x ∈ U}`, an automorphism of the lattice
of subspaces of `Ωⁿ`. -/
def galoisIso (σ : Ω ≃+* Ω) : Submodule Ω (ι → Ω) ≃o Submodule Ω (ι → Ω) where
  toFun U := U.comap (galoisLin (σ.symm : Ω →+* Ω))
  invFun U := U.comap (galoisLin (σ : Ω →+* Ω))
  left_inv U := by
    ext x
    simp [galoisLin, Function.comp_def]
  right_inv U := by
    ext x
    simp [galoisLin, Function.comp_def]
  map_rel_iff' {U U'} := by
    refine ⟨fun h x hx ↦ ?_, fun h ↦ comap_mono h⟩
    have := h (show (σ : Ω → Ω) ∘ x ∈ U.comap (galoisLin (σ.symm : Ω →+* Ω)) by
      simpa [galoisLin, Function.comp_def] using hx)
    simpa [galoisLin, Function.comp_def] using this

theorem mem_galoisIso {σ : Ω ≃+* Ω} {U : Submodule Ω (ι → Ω)} {x : ι → Ω} :
    x ∈ galoisIso σ U ↔ (σ.symm : Ω → Ω) ∘ x ∈ U :=
  Iff.rfl

theorem comp_mem_galoisIso {σ : Ω ≃+* Ω} {U : Submodule Ω (ι → Ω)} {x : ι → Ω} :
    (σ : Ω → Ω) ∘ x ∈ galoisIso σ U ↔ x ∈ U := by
  simp [mem_galoisIso, Function.comp_def]

/-- Galois conjugation preserves dimensions. -/
theorem finrank_galoisIso (σ : Ω ≃+* Ω) (U : Submodule Ω (ι → Ω)) :
    finrank Ω ↥(galoisIso σ U) = finrank Ω U := by
  let j : U ≃+ galoisIso σ U :=
    { toFun x := ⟨(σ : Ω → Ω) ∘ x, comp_mem_galoisIso.2 x.2⟩
      invFun y := ⟨(σ.symm : Ω → Ω) ∘ y, y.2⟩
      left_inv _ := by ext; simp
      right_inv _ := by ext; simp
      map_add' _ _ := by ext; simp }
  have := rank_eq_of_equiv_equiv σ j σ.bijective fun a x ↦ by ext; simp [j]
  simp only [finrank, this]

end Galois

/-! ### The weight of a subspace -/

namespace FormSystem

variable {K ι : Type*} [Field K] [NumberField K] [Fintype ι] [DecidableEq ι]
  (L : FormSystem K ι) (c : FormExponent K ι)
variable {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- The rows of a matrix over `K` as linear forms on `Ωⁿ`. -/
noncomputable def matrixForms (A : Matrix ι ι K) (i : ι) : Module.Dual Ω (ι → Ω) :=
  (LinearMap.proj i).comp (A.map (algebraMap K Ω)).mulVecLin

omit [NumberField K] [DecidableEq ι] in
theorem matrixForms_apply (A : Matrix ι ι K) (i : ι) (x : ι → Ω) :
    matrixForms A i x = (A.map (algebraMap K Ω)).mulVec x i :=
  rfl

omit [NumberField K] in
theorem iInf_ker_matrixForms {A : Matrix ι ι K} (hA : A.det ≠ 0) :
    ⨅ i, LinearMap.ker (matrixForms (Ω := Ω) A i) = ⊥ := by
  refine eq_bot_iff.2 fun x hx ↦ ?_
  have h : (A.map (algebraMap K Ω)).mulVec x = 0 := funext fun i ↦ by
    simpa [matrixForms_apply] using (mem_iInf _).1 hx i
  have hd : (A.map (algebraMap K Ω)).det ≠ 0 := by
    have := (algebraMap K Ω).map_det A
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (map_ne_zero _).2 hA
  exact (mem_bot Ω).2 (Matrix.eq_zero_of_mulVec_eq_zero hd h)

/-- **The weight `w_{L,c}(U)`** of a subspace `U ⊆ Ωⁿ` (EF13 (2.19), (2.20)): the sum over all
places `v` of `K` of the least `Σ_{i ∈ I} c_iv` over the `I` with `(L_i^{(v)}|_U)_{i ∈ I}` a
basis of the dual of `U`. -/
noncomputable def subspaceWeight (U : Submodule Ω (ι → Ω)) : ℝ :=
  ∑ v, formWeight (matrixForms (L.arch v)) (c.arch v) U +
    ∑ᶠ v, formWeight (matrixForms (L.fin v)) (c.fin v) U

/-- The sum over the finite places runs over the places with `c_v ≠ 0`. -/
theorem subspaceWeight_eq_sum (U : Submodule Ω (ι → Ω)) :
    L.subspaceWeight c U = ∑ v, formWeight (matrixForms (L.arch v)) (c.arch v) U +
      ∑ v ∈ c.finite_setOf_fin_ne_zero.toFinset,
        formWeight (matrixForms (L.fin v)) (c.fin v) U := by
  rw [subspaceWeight, finsum_eq_sum_of_support_subset]
  intro v hv
  rw [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
  intro h
  refine hv ?_
  change formWeight _ (c.fin v) U = 0
  rw [h]
  exact formWeight_zero _ (iInf_ker_matrixForms (L.fin_det_ne_zero v)) U

/-- **EF13 Lemma 15.1**: the weight is supermodular. -/
theorem isSupermodularWeight_subspaceWeight :
    IsSupermodularWeight (L.subspaceWeight (Ω := Ω) c) := by
  have h : L.subspaceWeight (Ω := Ω) c = fun U ↦
      ∑ v, formWeight (matrixForms (L.arch v)) (c.arch v) U +
        ∑ v ∈ c.finite_setOf_fin_ne_zero.toFinset,
          formWeight (matrixForms (L.fin v)) (c.fin v) U :=
    funext (L.subspaceWeight_eq_sum c)
  rw [h]
  exact (IsSupermodularWeight.sum _ fun v _ ↦ isSupermodularWeight_formWeight _ _
    (iInf_ker_matrixForms (L.arch_det_ne_zero v))).add
    (IsSupermodularWeight.sum _ fun v _ ↦ isSupermodularWeight_formWeight _ _
      (iInf_ker_matrixForms (L.fin_det_ne_zero v)))

/-- The weight takes finitely many values. -/
theorem finite_range_subspaceWeight : (Set.range (L.subspaceWeight (Ω := Ω) c)).Finite := by
  set S := c.finite_setOf_fin_ne_zero.toFinset
  set Φ : (InfinitePlace K → Finset ι) × (S → Finset ι) → ℝ := fun p ↦
    ∑ v, ∑ i ∈ p.1 v, c.arch v i + ∑ v : S, ∑ i ∈ p.2 v, c.fin v i
  refine (Set.finite_range Φ).subset ?_
  rintro _ ⟨U, rfl⟩
  have ha : ∀ v, ∃ I : Finset ι,
      ∑ i ∈ I, c.arch v i = formWeight (matrixForms (L.arch v)) (c.arch v) U := fun v ↦ by
    obtain ⟨I, -, hI⟩ :=
      formWeight_mem _ (c.arch v) (iInf_ker_matrixForms (L.arch_det_ne_zero v)) U
    exact ⟨I, hI⟩
  have hf : ∀ v : S, ∃ I : Finset ι,
      ∑ i ∈ I, c.fin v i = formWeight (matrixForms (L.fin v)) (c.fin v) U := fun v ↦ by
    obtain ⟨I, -, hI⟩ :=
      formWeight_mem _ (c.fin v) (iInf_ker_matrixForms (L.fin_det_ne_zero v)) U
    exact ⟨I, hI⟩
  choose Ia hIa using ha
  choose If hIf using hf
  refine ⟨(Ia, If), ?_⟩
  have h1 : Φ (Ia, If) = ∑ v, formWeight (matrixForms (L.arch v)) (c.arch v) U +
      ∑ v : S, formWeight (matrixForms (L.fin v)) (c.fin v) U := by
    simp only [Φ, hIa, hIf]
  rw [h1, L.subspaceWeight_eq_sum c U,
    sum_coe_sort S fun v ↦ formWeight (matrixForms (L.fin v)) (c.fin v) U]

section Galois

omit [NumberField K] [DecidableEq ι] in
/-- A `K`-automorphism of `Ω` maps the kernels of the forms to themselves. -/
theorem galoisIso_ker_matrixForms (σ : Ω ≃ₐ[K] Ω) (A : Matrix ι ι K) (i : ι) :
    galoisIso σ.toRingEquiv (LinearMap.ker (matrixForms A i)) =
      LinearMap.ker (matrixForms A i) := by
  ext x
  rw [mem_galoisIso, LinearMap.mem_ker, LinearMap.mem_ker, matrixForms_apply, matrixForms_apply]
  have : (A.map (algebraMap K Ω)).mulVec ((σ.toRingEquiv.symm : Ω → Ω) ∘ x) i =
      σ.symm ((A.map (algebraMap K Ω)).mulVec x i) := by
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [this, map_eq_zero_iff _ σ.symm.injective]

/-- **Galois invariance of the weight**. -/
theorem subspaceWeight_galoisIso (σ : Ω ≃ₐ[K] Ω) (U : Submodule Ω (ι → Ω)) :
    L.subspaceWeight c (galoisIso σ.toRingEquiv U) = L.subspaceWeight c U := by
  classical
  simp only [subspaceWeight]
  congr 1
  · refine sum_congr rfl fun v _ ↦ formWeight_orderIso _ _ _
      (iInf_ker_matrixForms (L.arch_det_ne_zero v)) (iInf_ker_matrixForms (L.arch_det_ne_zero v))
      _ (finrank_galoisIso _) (galoisIso_ker_matrixForms σ _) U
  · refine finsum_congr fun v ↦ formWeight_orderIso _ _ _
      (iInf_ker_matrixForms (L.fin_det_ne_zero v)) (iInf_ker_matrixForms (L.fin_det_ne_zero v))
      _ (finrank_galoisIso _) (galoisIso_ker_matrixForms σ _) U

omit [NumberField K] [Fintype ι] [DecidableEq ι] in
/-- A subspace defined over `K` is stable under the `K`-endomorphisms of `Ω`. -/
theorem _root_.Submodule.IsDefinedOver.comp_mem {V : Submodule Ω (ι → Ω)}
    (hV : V.IsDefinedOver K) (σ : Ω →ₐ[K] Ω) {x : ι → Ω} (hx : x ∈ V) :
    (σ : Ω → Ω) ∘ x ∈ V := by
  obtain ⟨s, rfl⟩ := hV
  refine algHom_comp_mem_span σ ?_ hx
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, hy, funext fun i ↦ by simp⟩

omit [NumberField K] [Fintype ι] [DecidableEq ι] in
theorem galoisIso_eq_of_isDefinedOver {V : Submodule Ω (ι → Ω)} (hV : V.IsDefinedOver K)
    (σ : Ω ≃ₐ[K] Ω) : galoisIso σ.toRingEquiv V = V := by
  ext x
  rw [mem_galoisIso]
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · have := hV.comp_mem (σ : Ω →ₐ[K] Ω) hx
    simpa [Function.comp_def] using this
  · simpa using hV.comp_mem (σ.symm : Ω →ₐ[K] Ω) hx

variable [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]

omit [Fintype ι] [DecidableEq ι] in
/-- A subspace fixed by Galois conjugation under all `K`-automorphisms is defined over `K`. -/
theorem isDefinedOver_of_galoisIso_eq [Finite ι] {T : Submodule Ω (ι → Ω)}
    (hT : ∀ σ : Ω ≃ₐ[K] Ω, galoisIso σ.toRingEquiv T = T) : T.IsDefinedOver K := by
  refine isDefinedOver_of_forall_algHom fun σ x hx ↦ ?_
  set τ := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have : (τ.toRingEquiv : Ω → Ω) ∘ x ∈ galoisIso τ.toRingEquiv T := comp_mem_galoisIso.2 hx
  rw [hT τ] at this
  exact this

/-- **EF13 Lemma 15.2 (i)**, last part: the destabilizing subspace of a subspace defined over `K`
is defined over `K`. -/
theorem isDefinedOver_of_isDestabilizing {V T : Submodule Ω (ι → Ω)}
    (h : IsDestabilizing (L.subspaceWeight c) V T) (hV : V.IsDefinedOver K) :
    T.IsDefinedOver K :=
  isDefinedOver_of_galoisIso_eq fun σ ↦ h.map_eq _ (finrank_galoisIso _)
    (L.subspaceWeight_galoisIso c σ) (galoisIso_eq_of_isDefinedOver hV σ)

/-- **EF13 Lemma 15.4**, last part: the filtration of a subspace defined over `K` consists of
subspaces defined over `K`. -/
theorem isDefinedOver_of_isWeightFiltration {V : Submodule Ω (ι → Ω)} {r : ℕ}
    {T : ℕ → Submodule Ω (ι → Ω)} (h : IsWeightFiltration (L.subspaceWeight c) V r T)
    (hV : V.IsDefinedOver K) {l : ℕ} (hl : l ≤ r) : (T l).IsDefinedOver K :=
  isDefinedOver_of_galoisIso_eq fun σ ↦ h.map_eq (L.isSupermodularWeight_subspaceWeight c) _
    (finrank_galoisIso _) (L.subspaceWeight_galoisIso c σ) (galoisIso_eq_of_isDefinedOver hV σ) hl

end Galois

/-! ### Change of coordinates (EF13 Lemma 7.3 (ii), (iii)) -/

section Comp

variable (P : Matrix ι ι K) (hP : P.det ≠ 0)

/-- `P` as an automorphism of `Ωⁿ`. -/
noncomputable def compEquiv : (ι → Ω) ≃ₗ[Ω] (ι → Ω) :=
  (P.map (algebraMap K Ω)).toLinearEquiv' <| Matrix.invertibleOfIsUnitDet _ <| by
    have := (algebraMap K Ω).map_det P
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact ((map_ne_zero _).2 hP).isUnit

omit [NumberField K] in
theorem compEquiv_apply (x : ι → Ω) : compEquiv P hP x = (P.map (algebraMap K Ω)).mulVec x :=
  rfl

omit [NumberField K] in
theorem map_ker_matrixForms_mul (A : Matrix ι ι K) (i : ι) :
    (LinearMap.ker (matrixForms (Ω := Ω) (A * P) i)).map (compEquiv P hP).toLinearMap =
      LinearMap.ker (matrixForms A i) := by
  have : matrixForms (Ω := Ω) (A * P) i = (matrixForms A i).comp (compEquiv P hP).toLinearMap := by
    refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, matrixForms_apply, compEquiv_apply,
      Matrix.map_mul, Matrix.mulVec_mulVec]
  rw [this, LinearMap.ker_comp, map_comap_eq_of_surjective (compEquiv P hP).surjective]

/-- **EF13 Lemma 7.3 (ii)**: `w_{L ∘ P, c}(U) = w_{L, c}(P U)`. -/
theorem subspaceWeight_comp (U : Submodule Ω (ι → Ω)) :
    (L.comp P hP).subspaceWeight c U =
      L.subspaceWeight c (U.map (compEquiv (Ω := Ω) P hP).toLinearMap) := by
  set E := orderIsoMapComap (compEquiv (Ω := Ω) P hP)
  have hE : ∀ W, finrank Ω ↥(E W) = finrank Ω W := fun W ↦ (compEquiv P hP).finrank_map_eq W
  simp only [subspaceWeight]
  congr 1
  · refine sum_congr rfl fun v _ ↦ (formWeight_orderIso _ _ _
      (iInf_ker_matrixForms ((L.comp P hP).arch_det_ne_zero v))
      (iInf_ker_matrixForms (L.arch_det_ne_zero v)) E hE
      (fun i ↦ map_ker_matrixForms_mul P hP _ i) U).symm
  · refine finsum_congr fun v ↦ (formWeight_orderIso _ _ _
      (iInf_ker_matrixForms ((L.comp P hP).fin_det_ne_zero v))
      (iInf_ker_matrixForms (L.fin_det_ne_zero v)) E hE
      (fun i ↦ map_ker_matrixForms_mul P hP _ i) U).symm

/-- **EF13 Lemma 7.3 (iii)**: the destabilizing subspace for `L ∘ P` is `P⁻¹ T` for the
destabilizing subspace `T` for `L`. -/
theorem isDestabilizing_comap_comp {V T : Submodule Ω (ι → Ω)}
    (h : IsDestabilizing (L.subspaceWeight c) V T) :
    IsDestabilizing ((L.comp P hP).subspaceWeight c) (V.comap (compEquiv (Ω := Ω) P hP).toLinearMap)
      (T.comap (compEquiv (Ω := Ω) P hP).toLinearMap) := by
  set E := orderIsoMapComap (compEquiv (Ω := Ω) P hP).symm
  have hE : ∀ W, finrank Ω ↥(E W) = finrank Ω W := fun W ↦ (compEquiv P hP).symm.finrank_map_eq W
  have hw : ∀ U, (L.comp P hP).subspaceWeight c (E U) = L.subspaceWeight c U := fun U ↦ by
    rw [subspaceWeight_comp]
    congr 1
    ext x
    simp [E]
  have := h.orderIso E hE hw
  simpa [E, map_equiv_eq_comap_symm] using this

end Comp

/-! ### The exceptional subspace -/

omit [NumberField K] [Fintype ι] [DecidableEq ι] in
theorem _root_.Submodule.isDefinedOver_top [Finite ι] :
    (⊤ : Submodule Ω (ι → Ω)).IsDefinedOver K := by
  classical
  refine ⟨Set.univ, eq_top_iff.2 ?_⟩
  rw [← (Pi.basisFun Ω ι).span_eq]
  refine span_mono ?_
  rintro _ ⟨i, rfl⟩
  refine ⟨Pi.single i 1, trivial, funext fun j ↦ ?_⟩
  by_cases h : j = i <;> simp [h]

/-- **The exceptional subspace `T(L, c)`** of EF13 (2.21) exists and is defined over `K` (EF13
Lemma 15.2 (i) with `V = Ωⁿ`; unique by `Submodule.IsDestabilizing.unique`). -/
theorem exists_isDestabilizing_top [Nonempty ι] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] :
    ∃ T, IsDestabilizing (L.subspaceWeight (Ω := Ω) c) ⊤ T ∧ T.IsDefinedOver K := by
  obtain ⟨T, hT⟩ := exists_isDestabilizing (L.isSupermodularWeight_subspaceWeight c)
    (L.finite_range_subspaceWeight c) (top_ne_bot (α := Submodule Ω (ι → Ω)))
  exact ⟨T, hT, L.isDefinedOver_of_isDestabilizing c hT isDefinedOver_top⟩

/-- **The filtration of `Ωⁿ` with respect to `(L, c)`** (EF13 Lemma 15.4 with `V = Ωⁿ`) exists and
consists of subspaces defined over `K`; it is unique by `Submodule.IsWeightFiltration.unique`. -/
theorem exists_isWeightFiltration_top [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] :
    ∃ r T, IsWeightFiltration (L.subspaceWeight (Ω := Ω) c) ⊤ r T ∧
      ∀ l ≤ r, (T l).IsDefinedOver K := by
  obtain ⟨r, T, hT⟩ := exists_isWeightFiltration (L.isSupermodularWeight_subspaceWeight c)
    (L.finite_range_subspaceWeight c) (⊤ : Submodule Ω (ι → Ω))
  exact ⟨r, T, hT, fun l hl ↦ L.isDefinedOver_of_isWeightFiltration c hT isDefinedOver_top hl⟩

end FormSystem

end NumberField
