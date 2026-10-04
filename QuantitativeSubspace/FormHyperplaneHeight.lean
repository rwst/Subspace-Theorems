/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Subspace
public import QuantitativeSubspace.FormWeightExchange

-- Used only inside proofs.
import ArithmeticHeights.Duality
import ArithmeticHeights.RowEntryHeight
import ArithmeticHeights.Submodular
import QuantitativeSubspace.FormInducedSystem
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# The height of a destabilizing hyperplane

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, Lemma 17.4.

Let `(L, c)` be a system on `Ω^N` whose destabilizing subspace `T` (the space preceding `Ω^N` in
its filtration) is a hyperplane, and `H₂` the largest Arakelov height of a form of `L`. Then
`H₂(T) ≤ H₂^{(N-1)²}`. EF13's proof: `T` is the unique hyperplane of largest weight; at each place
`v` the space `U_v` cut out by the forms with `c_{iv}` at most the weight-relevant exponent lies in
`T`, and any hyperplane containing all `U_v` has weight at least `w(T)`, so `T = Σ_v U_v`. Each
`U_v` has height at most `H₂^{N-1}`, and the height is submultiplicative on sums.

Here the weight of a hyperplane `ker φ` at a place comes from the coordinates of `φ` in the basis
`L_1^{(v)}, …, L_N^{(v)}` of the dual: `univ \ {j}` is a basis of `ker φ` in the sense of (2.19)
exactly when the `j`-th coordinate is nonzero (`Submodule.isFormBasis_ker_erase`,
`Submodule.exists_eq_erase_of_isFormBasis_ker`). EF13's ordering of the `c_{iv}` is not needed.

Heights of subspaces are those of `ArithmeticHeights` for subspaces of `K^N`, relative to `K` and
with the ℓ² norm at the infinite places (EF13's `H₂` raised to `[K:ℚ]`). A subspace `T ⊆ Ω^N`
defined over `K` is `V.extendPi Ω` for a subspace `V ⊆ K^N` determined by `T`
(`Submodule.extendPi_injective`).

## Main definitions

* `Submodule.extendPi Ω V`: the subspace of `Ωⁿ` spanned by a subspace `V ⊆ Kⁿ`.
* `NumberField.FormSystem.arakelovFormHeight L`: the largest Arakelov height of a form of `L`.

## Main results

* `Submodule.finrank_extendPi`, `Submodule.extendPi_injective`, `Submodule.exists_extendPi_eq`.
* `Submodule.formWeight_ker_le`, `Submodule.le_formWeight_ker`: the weight of a hyperplane.
* `Submodule.arakelovMulHeight_finset_sup_le`: `H(U_1 + ⋯ + U_s) ≤ B^{dim}` if all `H(U_i) ≤ B`.
* `NumberField.FormSystem.arakelovMulHeight_le_of_isDestabilizing`: EF13 Lemma 17.4.

This is part of milestone Q3.6 of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Module Finset Submodule

namespace Submodule

/-! ### Subspaces of `Kⁿ` read in `Ωⁿ` -/

section Extend

variable (Ω : Type*) {K ι : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- The coordinatewise inclusion `Kⁿ → Ωⁿ`, as a `K`-linear map. -/
def extendLin : (ι → K) →ₗ[K] (ι → Ω) :=
  LinearMap.compLeft (Algebra.linearMap K Ω) ι

/-- **The subspace of `Ωⁿ` spanned by a subspace `V ⊆ Kⁿ`.** -/
def extendPi (V : Submodule K (ι → K)) : Submodule Ω (ι → Ω) :=
  span Ω (extendLin Ω '' (V : Set (ι → K)))

variable {Ω}

omit [Field K] [Field Ω] [Algebra K Ω] in
theorem extendLin_apply [Field K] [Field Ω] [Algebra K Ω] (y : ι → K) :
    extendLin Ω y = algebraMap K Ω ∘ y :=
  rfl

theorem extendLin_mem_extendPi {V : Submodule K (ι → K)} {y : ι → K} (hy : y ∈ V) :
    extendLin Ω y ∈ V.extendPi Ω :=
  subset_span ⟨y, hy, rfl⟩

theorem extendPi_mono {V W : Submodule K (ι → K)} (h : V ≤ W) : V.extendPi Ω ≤ W.extendPi Ω :=
  span_mono (Set.image_mono h)

theorem extendPi_span (s : Set (ι → K)) :
    (span K s).extendPi Ω = span Ω (extendLin Ω '' s) := by
  refine le_antisymm (span_le.2 ?_) (span_mono (Set.image_mono subset_span))
  have h : (extendLin Ω '' (span K s : Set (ι → K))) = (span K (extendLin Ω '' s) : Set _) := by
    rw [← map_coe, map_span]
  rw [h]
  exact span_le_restrictScalars K Ω _

/-- A subspace defined over `K` is the extension of a subspace of `Kⁿ`. -/
theorem exists_extendPi_eq {T : Submodule Ω (ι → Ω)} (hT : T.IsDefinedOver K) :
    ∃ V : Submodule K (ι → K), V.extendPi Ω = T := by
  obtain ⟨s, hs⟩ := hT
  exact ⟨span K s, by rw [extendPi_span]; exact hs⟩

theorem isDefinedOver_extendPi (V : Submodule K (ι → K)) : (V.extendPi Ω).IsDefinedOver K :=
  ⟨V, rfl⟩

theorem extendPi_sup (V W : Submodule K (ι → K)) :
    (V ⊔ W).extendPi Ω = V.extendPi Ω ⊔ W.extendPi Ω := by
  have h : V ⊔ W = span K ((V : Set (ι → K)) ∪ W) := by rw [span_union, span_eq, span_eq]
  rw [h, extendPi_span, Set.image_union, span_union]
  rfl

theorem extendPi_bot : (⊥ : Submodule K (ι → K)).extendPi Ω = ⊥ := by
  rw [← span_empty, extendPi_span, Set.image_empty, span_empty]

theorem extendPi_finset_sup {α : Type*} (s : Finset α) (U : α → Submodule K (ι → K)) :
    (s.sup U).extendPi Ω = s.sup fun a ↦ (U a).extendPi Ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [extendPi_bot]
  | insert a s _ ih => rw [sup_insert, sup_insert, extendPi_sup, ih]

variable [Finite ι]

/-- **Extending scalars preserves dimensions.** -/
theorem finrank_extendPi (V : Submodule K (ι → K)) : finrank Ω (V.extendPi Ω) = finrank K V := by
  set b := Module.finBasis K V
  set v : Fin (finrank K V) → ι → K := fun i ↦ b i
  have hv : LinearIndependent K v := b.linearIndependent.map' V.subtype V.ker_subtype
  have hspan : span K (Set.range v) = V := by
    rw [show Set.range v = V.subtype '' Set.range b from Set.range_comp _ _, ← map_span,
      b.span_eq, map_subtype_top]
  have hv' : LinearIndependent Ω (fun i ↦ algebraMap K Ω ∘ v i) :=
    linearIndependent_algebraMap_comp_iff.2 hv
  have hext : V.extendPi Ω = span Ω (Set.range fun i ↦ algebraMap K Ω ∘ v i) := by
    conv_lhs => rw [← hspan]
    rw [extendPi_span, ← Set.range_comp]
    rfl
  rw [hext, finrank_span_eq_card hv', Fintype.card_fin]

/-- **Extending scalars is injective on subspaces**: it reflects inclusions. -/
theorem extendPi_le_extendPi_iff {V W : Submodule K (ι → K)} :
    V.extendPi Ω ≤ W.extendPi Ω ↔ V ≤ W := by
  refine ⟨fun h ↦ ?_, extendPi_mono⟩
  have hsup : (V ⊔ W).extendPi Ω = W.extendPi Ω := by rw [extendPi_sup, sup_eq_right.2 h]
  have hrank : finrank K ↥(V ⊔ W) = finrank K W := by
    rw [← finrank_extendPi (Ω := Ω), hsup, finrank_extendPi]
  exact sup_eq_right.1 (eq_of_le_of_finrank_eq le_sup_right hrank.symm).symm

theorem extendPi_injective : Function.Injective (extendPi (K := K) (ι := ι) Ω) :=
  fun _ _ h ↦ le_antisymm (extendPi_le_extendPi_iff.1 h.le) (extendPi_le_extendPi_iff.1 h.ge)

end Extend

/-! ### The weight of a hyperplane -/

section Hyperplane

variable {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [Fintype ι] [DecidableEq ι] (b : Basis ι k (Module.Dual k V))

omit [FiniteDimensional k V] [DecidableEq ι] in
include b in
theorem card_eq_finrank_of_basis_dual : Fintype.card ι = finrank k V := by
  rw [← finrank_eq_card_basis b, Subspace.dual_finrank_eq]

omit [FiniteDimensional k V] [Fintype ι] [DecidableEq ι] in
/-- A form vanishing on `ker φ` is a multiple of `φ`. -/
theorem exists_eq_smul_of_ker_le {φ f : Module.Dual k V} (h : LinearMap.ker φ ≤ LinearMap.ker f) :
    ∃ t : k, f = t • φ := by
  have h' : ⨅ _i : Unit, LinearMap.ker φ ≤ LinearMap.ker f := by rwa [iInf_const]
  have hf := mem_span_of_iInf_ker_le_ker h'
  rw [Set.range_const, mem_span_singleton] at hf
  obtain ⟨t, ht⟩ := hf
  exact ⟨t, ht.symm⟩

omit [FiniteDimensional k V] [Fintype ι] [DecidableEq ι] in
theorem ne_zero_of_repr_ne_zero {φ : Module.Dual k V} {j : ι} (hj : b.repr φ j ≠ 0) : φ ≠ 0 := by
  rintro rfl
  simp at hj

omit [FiniteDimensional k V] [Fintype ι] [DecidableEq ι] in
theorem exists_repr_ne_zero {φ : Module.Dual k V} (hφ : φ ≠ 0) : ∃ j, b.repr φ j ≠ 0 := by
  by_contra h
  push Not at h
  exact hφ (b.repr.injective (Finsupp.ext fun j ↦ by simpa using h j))

/-- **`univ \ {j}` is a basis of `ker φ` in the sense of (2.19)** when the `j`-th coordinate of
`φ` is nonzero. -/
theorem isFormBasis_ker_erase {φ : Module.Dual k V} {j : ι} (hj : b.repr φ j ≠ 0) :
    IsFormBasis b (LinearMap.ker φ) (univ.erase j) := by
  have hφ := ne_zero_of_repr_ne_zero b hj
  refine ⟨?_, ?_⟩
  · have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
    have h2 := card_eq_finrank_of_basis_dual b
    rw [card_erase_of_mem (mem_univ j), card_univ]
    omega
  rw [linearIndepOn_finset_iff]
  intro g hg i hi
  set f : Module.Dual k V := ∑ i ∈ univ.erase j, g i • b i
  have hker : LinearMap.ker φ ≤ LinearMap.ker f := fun x hx ↦ by
    have := LinearMap.congr_fun hg ⟨x, hx⟩
    simpa [f, LinearMap.sum_apply] using this
  obtain ⟨t, ht⟩ := exists_eq_smul_of_ker_le hker
  have hrepr : b.repr f j = 0 := by
    simp only [f, map_sum, map_smul, Basis.repr_self, Finsupp.coe_finsetSum,
      Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact sum_eq_zero fun i hi ↦ by
      rw [Finsupp.single_apply, ite_eq_right (ne_of_mem_erase hi), mul_zero]
  have ht0 : t = 0 := by
    rw [ht, map_smul, Finsupp.smul_apply, smul_eq_mul] at hrepr
    exact (mul_eq_zero.1 hrepr).resolve_right hj
  have hf0 : f = 0 := by rw [ht, ht0, zero_smul]
  exact linearIndepOn_finset_iff.1 (b.linearIndependent.linearIndepOn (s := (univ.erase j : Set ι)))
    g hf0 i hi

/-- **A basis of `ker φ` in the sense of (2.19) is `univ \ {j}`** with the `j`-th coordinate of `φ`
nonzero. -/
theorem exists_eq_erase_of_isFormBasis_ker {φ : Module.Dual k V} (hφ : φ ≠ 0) {I : Finset ι}
    (hI : IsFormBasis b (LinearMap.ker φ) I) : ∃ j, I = univ.erase j ∧ b.repr φ j ≠ 0 := by
  have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
  have h2 := card_eq_finrank_of_basis_dual b
  have hIc : #I + 1 = Fintype.card ι := by have := hI.1; omega
  obtain ⟨j, -, hjI⟩ := exists_mem_notMem_of_card_lt_card (s := I) (t := univ)
    (by rw [card_univ]; omega)
  have hIe : I = univ.erase j := eq_of_subset_of_card_le
    (fun i hi ↦ mem_erase.2 ⟨fun h ↦ hjI (h ▸ hi), mem_univ i⟩)
    (by rw [card_erase_of_mem (mem_univ j), card_univ]; omega)
  refine ⟨j, hIe, fun hj ↦ hφ ?_⟩
  have hsum : ∑ i ∈ I, b.repr φ i • b i = φ := by
    conv_rhs => rw [← b.sum_repr φ]
    rw [hIe, ← sum_erase_add _ _ (mem_univ j), hj, zero_smul, add_zero]
  have hres : ∑ i ∈ I, b.repr φ i • (b i).domRestrict (LinearMap.ker φ) = 0 := by
    refine LinearMap.ext fun x ↦ ?_
    have := LinearMap.congr_fun hsum x
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at this
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.domRestrict_apply, smul_eq_mul,
      LinearMap.zero_apply]
    rw [this]
    exact x.2
  have hzero := linearIndepOn_finset_iff.1 hI.2 _ hres
  rw [← hsum]
  exact sum_eq_zero fun i hi ↦ by rw [hzero i hi, zero_smul]

variable (c : ι → ℝ)

omit [DecidableEq ι] in
/-- **The weight of `ker φ` is at most `Σ c - c_j`** for every `j` with `φ_j ≠ 0`. -/
theorem formWeight_ker_le {φ : Module.Dual k V} {j : ι} (hj : b.repr φ j ≠ 0) :
    formWeight b c (LinearMap.ker φ) ≤ ∑ i, c i - c j := by
  classical
  have h := formWeight_le_sum b c (isFormBasis_ker_erase b hj)
  rwa [sum_erase_eq_sub (mem_univ j)] at h

omit [DecidableEq ι] in
/-- **The weight of `ker φ` is at least `Σ c - t`** if `c_j ≤ t` whenever `φ_j ≠ 0`. -/
theorem le_formWeight_ker {φ : Module.Dual k V} (hφ : φ ≠ 0) {t : ℝ}
    (ht : ∀ j, b.repr φ j ≠ 0 → c j ≤ t) : ∑ i, c i - t ≤ formWeight b c (LinearMap.ker φ) := by
  classical
  obtain ⟨j, hj⟩ := exists_repr_ne_zero b hφ
  refine le_formWeight b c ⟨_, isFormBasis_ker_erase b hj⟩ fun I hI ↦ ?_
  obtain ⟨j', rfl, hj'⟩ := exists_eq_erase_of_isFormBasis_ker b hφ hI
  rw [sum_erase_eq_sub (mem_univ j')]
  linarith [ht j' hj']

end Hyperplane

/-! ### Heights of sums of subspaces -/

section Height

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **A sum of subspaces of height at most `B ≥ 1` has height at most `B^{dim}`**: by
`H(U + W) ≤ H(U) H(W)`, counting only the summands that raise the dimension. -/
theorem arakelovMulHeight_finset_sup_le (s : Finset (Submodule K (ι → K))) {B : ℝ} (hB : 1 ≤ B)
    (h : ∀ U ∈ s, U.arakelovMulHeight ≤ B) :
    (s.sup id).arakelovMulHeight ≤ B ^ finrank K ↥(s.sup id) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_le_pow₀ hB
  | insert U s _ ih =>
    have ih := ih fun W hW ↦ h W (mem_insert_of_mem hW)
    rw [sup_insert, id]
    set W := s.sup id
    by_cases hUW : U ≤ W
    · rwa [sup_eq_right.2 hUW]
    have hlt : finrank K W < finrank K ↥(U ⊔ W) :=
      finrank_lt_finrank_of_lt (lt_of_le_of_ne le_sup_right fun h' ↦ hUW (h' ▸ le_sup_left))
    calc (U ⊔ W).arakelovMulHeight ≤ U.arakelovMulHeight * W.arakelovMulHeight :=
          arakelovMulHeight_sup_le_mul U W
      _ ≤ B * B ^ finrank K W :=
          mul_le_mul (h U (mem_insert_self U s)) ih (arakelovMulHeight_pos _).le
            (zero_le_one.trans hB)
      _ = B ^ (finrank K W + 1) := by rw [pow_succ, mul_comm]
      _ ≤ B ^ finrank K ↥(U ⊔ W) := pow_le_pow_right₀ hB hlt

end Height

end Submodule

namespace NumberField.FormSystem

/-! ### Forms over `K` read over `Ω` -/

section DualExtend

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] {Ω : Type*} [Field Ω]
  [Algebra K Ω]

/-- A linear form on `Kⁿ` read as a linear form on `Ωⁿ`. -/
noncomputable def dualExtend (f : Module.Dual K (ι → K)) : Module.Dual Ω (ι → Ω) :=
  ∑ j, algebraMap K Ω (f (Pi.single j 1)) • LinearMap.proj j

theorem dualExtend_apply (f : Module.Dual K (ι → K)) (x : ι → Ω) :
    dualExtend f x = ∑ j, algebraMap K Ω (f (Pi.single j 1)) * x j := by
  simp [dualExtend, LinearMap.sum_apply, Algebra.smul_def]

theorem apply_eq_sum_single (f : Module.Dual K (ι → K)) (y : ι → K) :
    f y = ∑ j, y j * f (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single y]
  rw [map_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [show Pi.single j (y j) = y j • (Pi.single j 1 : ι → K) by ext k; simp [Pi.single_apply],
    map_smul, smul_eq_mul]

theorem dualExtend_extendLin (f : Module.Dual K (ι → K)) (y : ι → K) :
    dualExtend (Ω := Ω) f (extendLin Ω y) = algebraMap K Ω (f y) := by
  rw [dualExtend_apply, apply_eq_sum_single f y, map_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [extendLin_apply, Function.comp_apply, map_mul, mul_comm]

theorem dualExtend_matrixForms (A : Matrix ι ι K) (i : ι) :
    dualExtend (Ω := Ω) (matrixForms (Ω := K) A i) = matrixForms A i := by
  refine LinearMap.ext fun x ↦ ?_
  rw [dualExtend_apply]
  simp only [matrixForms_apply, Matrix.mulVec_single_one, Algebra.algebraMap_self]
  simp [Matrix.mulVec, dotProduct]

theorem dualExtend_sum_smul {κ : Type*} [Fintype κ] (t : κ → K)
    (g : κ → Module.Dual K (ι → K)) :
    dualExtend (Ω := Ω) (∑ a, t a • g a) = ∑ a, algebraMap K Ω (t a) • dualExtend (g a) := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [dualExtend_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    map_sum, map_mul, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring

end DualExtend

/-! ### EF13 Lemma 17.4 -/

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **EF13's `H₂`** for a system: the largest Arakelov height of one of its forms, relative to
`K`. -/
noncomputable def arakelovFormHeight (L : FormSystem K ι) : ℝ :=
  ⨆ f : L.forms, NumberField.arakelovMulHeight (f : ι → K)

theorem arakelovMulHeight_le_arakelovFormHeight (L : FormSystem K ι) {f : ι → K}
    (hf : f ∈ L.forms) : NumberField.arakelovMulHeight f ≤ L.arakelovFormHeight :=
  le_ciSup (f := fun g : L.forms ↦ NumberField.arakelovMulHeight (g : ι → K))
    (Finite.bddAbove_range _) ⟨f, hf⟩

theorem one_le_arakelovFormHeight [Nonempty ι] (L : FormSystem K ι) :
    1 ≤ L.arakelovFormHeight := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  obtain ⟨i⟩ : Nonempty ι := inferInstance
  exact (NumberField.one_le_arakelovMulHeight _).trans
    (L.arakelovMulHeight_le_arakelovFormHeight (L.arch_mem_forms v i))

variable {N : ℕ} {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- The common kernel in `K^N` of the forms of `A` indexed by `S`. -/
noncomputable def kerForms (A : Matrix (Fin N) (Fin N) K) (S : Finset (Fin N)) :
    Submodule K (Fin N → K) :=
  ⨅ i ∈ S, LinearMap.ker (matrixForms (Ω := K) A i)

omit [NumberField K] in
/-- **The local step of EF13 Lemma 17.4.** For `T = ker φ`, the forms `L_i^{(v)}` with `c_{iv}`
at most the largest `c_{jv}` with `φ_j ≠ 0` cut out a subspace `U_v ⊆ T` (EF13 (17.9)), and every
hyperplane `ker ψ ⊇ U_v` has local weight at least that of `T`. -/
theorem exists_kerForms (A : Matrix (Fin N) (Fin N) K) (hA : A.det ≠ 0) (e : Fin N → ℝ)
    {φ : Module.Dual Ω (Fin N → Ω)} (hφ : φ ≠ 0) :
    ∃ S : Finset (Fin N), (kerForms A S).extendPi Ω ≤ LinearMap.ker φ ∧
      ∀ f : Module.Dual K (Fin N → K), kerForms A S ≤ LinearMap.ker f →
        dualExtend (Ω := Ω) f ≠ 0 →
        formWeight (matrixForms A) e (LinearMap.ker φ) ≤
          formWeight (matrixForms A) e (LinearMap.ker (dualExtend (Ω := Ω) f)) := by
  classical
  have : Nonempty (Fin N) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hφ (LinearMap.ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply])
  have hli := Splitting.linearIndependent_matrixForms (Ω := Ω) hA
  have hcard : Fintype.card (Fin N) = finrank Ω (Module.Dual Ω (Fin N → Ω)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_fin_fun, Fintype.card_fin]
  set b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ⇑b = matrixForms A := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  obtain ⟨j₀, hj₀⟩ := exists_repr_ne_zero b hφ
  set J := univ.filter fun j ↦ b.repr φ j ≠ 0
  obtain ⟨jm, hjmJ, hjm⟩ := J.exists_max_image e ⟨j₀, by simp [J, hj₀]⟩
  have hjm0 : b.repr φ jm ≠ 0 := (mem_filter.1 hjmJ).2
  set S := univ.filter fun i ↦ e i ≤ e jm
  have hsupp : ∀ ψ : Module.Dual Ω (Fin N → Ω), ψ ∈ span Ω (matrixForms A '' (S : Set _)) →
      ∀ j, b.repr ψ j ≠ 0 → e j ≤ e jm := by
    intro ψ hψ j hj
    rw [← hb, Basis.mem_span_image] at hψ
    have := hψ (Finsupp.mem_support_iff.2 hj)
    simpa [S] using this
  refine ⟨S, ?_, fun f hf hψ ↦ ?_⟩
  · rw [extendPi, span_le]
    rintro _ ⟨y, hy, rfl⟩
    have hy' : ∀ i ∈ S, matrixForms (Ω := K) A i y = 0 := fun i hi ↦ by
      have := (mem_iInf _).1 ((mem_iInf _).1 hy i) hi
      simpa using this
    have hφS : φ ∈ span Ω (matrixForms A '' (S : Set _)) := by
      rw [← hb, Basis.mem_span_image]
      intro j hj
      have hjJ : j ∈ J := by simpa [J] using hj
      simpa [S] using hjm j hjJ
    refine apply_eq_zero_of_mem_span hφS ?_
    rintro _ ⟨i, hi, rfl⟩
    rw [← dualExtend_matrixForms, dualExtend_extendLin, hy' i hi, map_zero]
  · have hf' : ⨅ i : (S : Set (Fin N)), LinearMap.ker (matrixForms (Ω := K) A i) ≤
        LinearMap.ker f := by
      refine le_trans (le_of_eq ?_) hf
      rw [kerForms, iInf_subtype']
      rfl
    obtain ⟨t, ht⟩ := (mem_span_range_iff_exists_fun K).1 (mem_span_of_iInf_ker_le_ker hf')
    have hψS : dualExtend (Ω := Ω) f ∈ span Ω (matrixForms A '' (S : Set _)) := by
      rw [← ht, dualExtend_sum_smul]
      refine sum_mem fun i _ ↦ smul_mem _ _ (subset_span ⟨i, i.2, ?_⟩)
      rw [dualExtend_matrixForms]
    rw [← hb]
    exact (formWeight_ker_le b e hjm0).trans (le_formWeight_ker b e hψ (hsupp _ hψS))

/-- **EF13 (6.11), (6.13) for `U_v`**: the common kernel of forms of `L` has height at most
`H₂^{N-1}`. -/
theorem arakelovMulHeight_kerForms_le (L : FormSystem K (Fin N)) {A : Matrix (Fin N) (Fin N) K}
    (hA : A.det ≠ 0) (hAL : ∀ i, A i ∈ L.forms) (S : Finset (Fin N)) :
    (kerForms A S).arakelovMulHeight ≤ L.arakelovFormHeight ^ (N - 1) := by
  classical
  by_cases hS : S = univ
  · have hbot : kerForms A S = ⊥ := by
      have h := iInf_ker_matrixForms (Ω := K) hA
      rw [kerForms, hS]
      simpa using h
    rw [hbot, arakelovMulHeight_bot]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    exact one_le_pow₀ L.one_le_arakelovFormHeight
  have hcard : #S ≤ N - 1 := by
    have := card_lt_card (ssubset_univ_iff.2 hS)
    rw [card_univ, Fintype.card_fin] at this
    omega
  set B : Matrix S (Fin N) K := A.submatrix Subtype.val id
  have hker : kerForms A S = LinearMap.ker B.mulVecLin := by
    ext x
    simp [kerForms, mem_iInf, matrixForms_apply, B, Matrix.mulVec, dotProduct, funext_iff]
  have hH1 : 1 ≤ L.arakelovFormHeight := by
    have : Nonempty (Fin N) := by
      by_contra h
      rw [not_nonempty_iff] at h
      exact hS (eq_univ_of_forall fun i ↦ (IsEmpty.false i).elim)
    exact L.one_le_arakelovFormHeight
  rw [hker, Matrix.arakelovMulHeight_ker_mulVecLin]
  calc (span K (Set.range B.row)).arakelovMulHeight
        ≤ ∏ i : S, NumberField.arakelovMulHeight (B i) :=
        arakelovMulHeight_span_range_le_prod _
    _ ≤ ∏ _i : S, L.arakelovFormHeight :=
        prod_le_prod₀ (fun i _ ↦ (NumberField.arakelovMulHeight_pos _).le) fun i _ ↦
          L.arakelovMulHeight_le_arakelovFormHeight (hAL i)
    _ = L.arakelovFormHeight ^ #S := by rw [prod_const, card_univ, Fintype.card_coe]
    _ ≤ L.arakelovFormHeight ^ (N - 1) := pow_le_pow_right₀ hH1 hcard

/-- **EF13 Lemma 17.4.** Let `T`, the destabilizing subspace of `Ω^N` for `(L, c)`, be a hyperplane,
and `T = V ⊗ Ω` with `V ⊆ K^N`. Then `H₂(V) ≤ H₂^{(N-1)²}`, `H₂` the largest Arakelov height of a
form of `L`. -/
theorem arakelovMulHeight_le_of_isDestabilizing (L : FormSystem K (Fin N))
    (c : FormExponent K (Fin N)) {T : Submodule Ω (Fin N → Ω)}
    (hT : IsDestabilizing (L.subspaceWeight c) ⊤ T) (hdim : finrank Ω T + 1 = N)
    {V : Submodule K (Fin N → K)} (hV : V.extendPi Ω = T) :
    V.arakelovMulHeight ≤ L.arakelovFormHeight ^ ((N - 1) * (N - 1)) := by
  classical
  have hN : finrank Ω (Fin N → Ω) = N := by rw [Module.finrank_fin_fun]
  have : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  obtain ⟨φ, hφ0, hφT⟩ := exists_dual_map_eq_bot_of_lt_top hT.lt inferInstance
  have hTφ : T = LinearMap.ker φ := by
    refine eq_of_le_of_finrank_eq (fun x hx ↦ ?_) ?_
    · have : φ x ∈ T.map φ := mem_map_of_mem hx
      rw [hφT] at this
      exact LinearMap.mem_ker.2 ((mem_bot Ω).1 this)
    · have := Module.Dual.finrank_ker_add_one_of_ne_zero hφ0
      omega
  choose Sa hSa₁ hSa₂ using fun v : InfinitePlace K ↦
    exists_kerForms (Ω := Ω) (L.arch v) (L.arch_det_ne_zero v) (c.arch v) hφ0
  choose Sf hSf₁ hSf₂ using fun v : FinitePlace K ↦
    exists_kerForms (Ω := Ω) (L.fin v) (L.fin_det_ne_zero v) (c.fin v) hφ0
  set 𝒰 : Set (Submodule K (Fin N → K)) := Set.range (fun v ↦ kerForms (L.arch v) (Sa v)) ∪
    Set.range (fun v ↦ kerForms (L.fin v) (Sf v))
  have h𝒰 : 𝒰.Finite := by
    refine (Set.finite_range _).union (((L.finite_range_fin.prod
      (Set.finite_univ (α := Finset (Fin N)))).image fun p ↦ kerForms p.1 p.2).subset ?_)
    rintro _ ⟨v, rfl⟩
    exact ⟨(L.fin v, Sf v), ⟨⟨v, rfl⟩, trivial⟩, rfl⟩
  have hmem : ∀ U ∈ 𝒰, U.extendPi Ω ≤ T ∧
      U.arakelovMulHeight ≤ L.arakelovFormHeight ^ (N - 1) := by
    rintro U (⟨v, rfl⟩ | ⟨v, rfl⟩)
    · exact ⟨hTφ ▸ hSa₁ v, L.arakelovMulHeight_kerForms_le (L.arch_det_ne_zero v)
        (fun i ↦ L.arch_mem_forms v i) _⟩
    · exact ⟨hTφ ▸ hSf₁ v, L.arakelovMulHeight_kerForms_le (L.fin_det_ne_zero v)
        (fun i ↦ L.fin_mem_forms v i) _⟩
  set W := h𝒰.toFinset.sup id
  have hWV : W = V := by
    have hle : W ≤ V := by
      rw [← extendPi_le_extendPi_iff (Ω := Ω), hV, extendPi_finset_sup]
      exact Finset.sup_le fun U hU ↦ (hmem U (h𝒰.mem_toFinset.1 hU)).1
    by_contra hne
    obtain ⟨y, hyV, hyW⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hle hne)
    obtain ⟨f, hfy, hfW⟩ := exists_dual_map_eq_bot_of_notMem hyW inferInstance
    have hWf : W ≤ LinearMap.ker f := fun x hx ↦ by
      have : f x ∈ W.map f := mem_map_of_mem hx
      rw [hfW] at this
      exact LinearMap.mem_ker.2 ((mem_bot K).1 this)
    set ψ := dualExtend (Ω := Ω) f
    have hψy : ψ (extendLin Ω y) ≠ 0 := by
      rw [dualExtend_extendLin]
      exact (map_ne_zero _).2 hfy
    have hψ0 : ψ ≠ 0 := fun h ↦ hψy (by rw [h, LinearMap.zero_apply])
    have hUf : ∀ U ∈ 𝒰, U ≤ LinearMap.ker f := fun U hU ↦
      (Finset.le_sup (f := id) (h𝒰.mem_toFinset.2 hU)).trans hWf
    have hw : L.subspaceWeight c T ≤ L.subspaceWeight c (LinearMap.ker ψ) := by
      rw [subspaceWeight_eq_sum, subspaceWeight_eq_sum]
      refine add_le_add (sum_le_sum fun v _ ↦ ?_) (sum_le_sum fun v _ ↦ ?_)
      · rw [hTφ]
        exact hSa₂ v f (hUf _ (Or.inl ⟨v, rfl⟩)) hψ0
      · rw [hTφ]
        exact hSf₂ v f (hUf _ (Or.inr ⟨v, rfl⟩)) hψ0
    have hψlt : LinearMap.ker ψ < ⊤ :=
      lt_top_iff_ne_top.2 fun h ↦ hψ0 (LinearMap.ker_eq_top.1 h)
    have hfrψ := Module.Dual.finrank_ker_add_one_of_ne_zero hψ0
    have hslope : ∀ U : Submodule Ω (Fin N → Ω), finrank Ω U + 1 = N →
        weightSlope (L.subspaceWeight c) U ⊤ =
          L.subspaceWeight (Ω := Ω) c ⊤ - L.subspaceWeight c U := by
      intro U hU
      have h1 : ((finrank Ω ↥(⊤ : Submodule Ω (Fin N → Ω)) : ℝ) - finrank Ω U) = 1 := by
        rw [finrank_top, hN]
        have : (N : ℝ) = finrank Ω U + 1 := by exact_mod_cast hU.symm
        rw [this]
        ring
      rw [weightSlope, h1, div_one]
    have h1 := hT.le _ hψlt
    have heq : weightSlope (L.subspaceWeight c) (LinearMap.ker ψ) ⊤ =
        weightSlope (L.subspaceWeight c) T ⊤ := by
      rw [hslope T hdim, hslope _ (by omega)] at h1 ⊢
      linarith
    exact hψy (hT.least _ hψlt heq (hV ▸ extendLin_mem_extendPi hyV))
  have hdimW : finrank K W = N - 1 := by
    rw [hWV, ← finrank_extendPi (Ω := Ω), hV]
    omega
  rw [← hWV]
  calc W.arakelovMulHeight ≤ (L.arakelovFormHeight ^ (N - 1)) ^ finrank K W :=
        arakelovMulHeight_finset_sup_le _ (one_le_pow₀ L.one_le_arakelovFormHeight)
          fun U hU ↦ (hmem U (h𝒰.mem_toFinset.1 hU)).2
    _ = L.arakelovFormHeight ^ ((N - 1) * (N - 1)) := by rw [hdimW, ← pow_mul]

end NumberField.FormSystem
