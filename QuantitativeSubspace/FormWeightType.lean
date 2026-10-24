/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormAuxiliaryPolynomial
public import QuantitativeSubspace.FormSubspaceWeight

/-!
# Weight types and the destabilizing subspaces of a set of exponents

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, (2.19)–(2.21) and Lemma 15.2.

The weight `w_{L,c}(U)` of (2.19), (2.20) at a place `v` is the least `Σ_{i ∈ I} c_iv` over the
index sets `I` for which the restrictions `L_i^{(v)}|_U`, `i ∈ I`, form a basis of the dual of `U`.
If all exponents of a set `𝒞` vanish outside a finite set `S₁` of places, then `w_{L,c}(U)` depends
only on `c` and on the **weight type** of `U`: its dimension and these index sets at the places of
`S₁`. Two subspaces of the same type have the same slope for every `c ∈ 𝒞`, so by the uniqueness of
the destabilizing subspace (EF13 Lemma 15.2 (i)) the subspaces `T(L, c)` of (2.21), `c ∈ 𝒞`, are
determined by their types. There are at most `(n + 1) (2^{2ⁿ})^{#S₁}` of them, however large `𝒞`
is.

* `NumberField.FormSystem.weightType`: the type of a subspace.
* `NumberField.FormSystem.subspaceWeight_eq_of_weightType_eq`: the weight depends only on the type.
* `NumberField.FormSystem.eq_of_isDestabilizing_of_weightType_eq`: `T(L, c₁) = T(L, c₂)` when the
  two have the same type.
* `NumberField.FormSystem.exists_finset_isDestabilizing`: all `T(L, c)`, `c ∈ 𝒞`, lie in one finite
  set of at most `(n + 1) (2^{2ⁿ})^{#S₁}` subspaces.
-/

@[expose] public section

open Finset Module

namespace NumberField.FormSystem

variable {K : Type*} [Field K] [NumberField K] {n : ℕ} (L : FormSystem K (Fin n))
  {Ω : Type*} [Field Ω] [Algebra K Ω] (S₁ : Finset (InfinitePlace K ⊕ FinitePlace K))

open scoped Classical in
/-- **The weight type** of a subspace `U ⊆ Ωⁿ` on the places of `S₁`: its dimension and, at every
`v ∈ S₁`, the index sets `I` with `(L_i^{(v)}|_U)_{i ∈ I}` a basis of the dual of `U`. -/
noncomputable def weightType (U : Submodule Ω (Fin n → Ω)) :
    ℕ × (S₁ → Finset (Finset (Fin n))) :=
  (finrank Ω U, fun v ↦ univ.filter fun I ↦ Submodule.IsFormBasis (matrixForms (L.mat v.1)) U I)

omit [NumberField K] in
/-- The local weight depends only on the index sets of the bases. -/
theorem formWeight_congr {A : Matrix (Fin n) (Fin n) K} (c : Fin n → ℝ)
    {U U' : Submodule Ω (Fin n → Ω)}
    (h : {I | Submodule.IsFormBasis (matrixForms A) U I} =
      {I | Submodule.IsFormBasis (matrixForms A) U' I}) :
    Submodule.formWeight (matrixForms A) c U = Submodule.formWeight (matrixForms A) c U' := by
  unfold Submodule.formWeight
  rw [h]

variable {L S₁}

/-- **The weight depends only on the type**: if `c` vanishes outside `S₁` and `U`, `U'` have the
same weight type, then `w_{L,c}(U) = w_{L,c}(U')`. -/
theorem subspaceWeight_eq_of_weightType_eq {c : FormExponent K (Fin n)}
    (hc : ∀ v ∉ S₁, c.vec v = 0) {U U' : Submodule Ω (Fin n → Ω)}
    (h : L.weightType S₁ U = L.weightType S₁ U') :
    L.subspaceWeight c U = L.subspaceWeight c U' := by
  classical
  have key : ∀ v, Submodule.formWeight (matrixForms (L.mat v)) (c.vec v) U =
      Submodule.formWeight (matrixForms (L.mat v)) (c.vec v) U' := by
    intro v
    by_cases hv : v ∈ S₁
    · refine formWeight_congr _ (Set.ext fun I ↦ ?_)
      have := Finset.ext_iff.1 (congrFun (congrArg Prod.snd h) ⟨v, hv⟩) I
      simpa [weightType] using this
    · have hker := iInf_ker_matrixForms (Ω := Ω)
        (det_ne_zero_of_mem_matSet (L.mat_mem_matSet v))
      rw [hc v hv, Submodule.formWeight_zero _ hker, Submodule.formWeight_zero _ hker]
  unfold subspaceWeight
  congr 1
  · exact sum_congr rfl fun v _ ↦ key (.inl v)
  · exact finsum_congr fun v ↦ key (.inr v)

/-- **EF13 Lemma 15.2 (i) for two exponents**: if `c₁`, `c₂` vanish outside `S₁` and their
destabilizing subspaces `T₁ = T(L, c₁)`, `T₂ = T(L, c₂)` have the same weight type, then
`T₁ = T₂`. Both have the same slope for `c₁` and for `c₂`, so each contains the other. -/
theorem eq_of_isDestabilizing_of_weightType_eq {c₁ c₂ : FormExponent K (Fin n)}
    (hc₁ : ∀ v ∉ S₁, c₁.vec v = 0) (hc₂ : ∀ v ∉ S₁, c₂.vec v = 0)
    {T₁ T₂ : Submodule Ω (Fin n → Ω)}
    (hT₁ : Submodule.IsDestabilizing (L.subspaceWeight c₁) ⊤ T₁)
    (hT₂ : Submodule.IsDestabilizing (L.subspaceWeight c₂) ⊤ T₂)
    (h : L.weightType S₁ T₁ = L.weightType S₁ T₂) : T₁ = T₂ := by
  have hd : finrank Ω T₁ = finrank Ω T₂ := congrArg Prod.fst h
  have hs : ∀ c : FormExponent K (Fin n), (∀ v ∉ S₁, c.vec v = 0) →
      Submodule.weightSlope (L.subspaceWeight c) T₂ ⊤ =
        Submodule.weightSlope (L.subspaceWeight c) T₁ ⊤ := by
    intro c hc
    unfold Submodule.weightSlope
    rw [subspaceWeight_eq_of_weightType_eq hc h, hd]
  exact le_antisymm (hT₁.least T₂ hT₂.lt (hs c₁ hc₁)) (hT₂.least T₁ hT₁.lt (hs c₂ hc₂).symm)

/-- **The destabilizing subspaces of a set of exponents**: if every `c ∈ 𝒞` vanishes outside `S₁`,
then all `T(L, c)`, `c ∈ 𝒞`, lie in one finite set of at most `(n + 1) (2^{2ⁿ})^{#S₁}` subspaces,
independently of `𝒞`. -/
theorem exists_finset_isDestabilizing (𝒞 : Set (FormExponent K (Fin n)))
    (h𝒞 : ∀ c ∈ 𝒞, ∀ v ∉ S₁, c.vec v = 0) :
    ∃ 𝒯 : Finset (Submodule Ω (Fin n → Ω)), #𝒯 ≤ (n + 1) * (2 ^ 2 ^ n) ^ #S₁ ∧
      ∀ c ∈ 𝒞, ∀ T, Submodule.IsDestabilizing (L.subspaceWeight c) ⊤ T → T ∈ 𝒯 := by
  classical
  set 𝒮 : Set (Submodule Ω (Fin n → Ω)) :=
    {T | ∃ c ∈ 𝒞, Submodule.IsDestabilizing (L.subspaceWeight c) ⊤ T} with h𝒮
  have hinj : Set.InjOn (L.weightType S₁) 𝒮 := by
    rintro T₁ ⟨c₁, hc₁, hT₁⟩ T₂ ⟨c₂, hc₂, hT₂⟩ h
    exact eq_of_isDestabilizing_of_weightType_eq (h𝒞 c₁ hc₁) (h𝒞 c₂ hc₂) hT₁ hT₂ h
  set B : Finset (ℕ × (S₁ → Finset (Finset (Fin n)))) := range (n + 1) ×ˢ univ with hB
  have hsub : L.weightType S₁ '' 𝒮 ⊆ (B : Set _) := by
    rintro _ ⟨T, -, rfl⟩
    refine mem_coe.2 (mem_product.2 ⟨mem_range.2 (Nat.lt_succ_of_le ?_), mem_univ _⟩)
    change finrank Ω T ≤ n
    simpa using Submodule.finrank_le T
  have hfin : 𝒮.Finite := Set.Finite.of_finite_image (B.finite_toSet.subset hsub) hinj
  refine ⟨hfin.toFinset, ?_, fun c hc T hT ↦ hfin.mem_toFinset.2 ⟨c, hc, hT⟩⟩
  have hcard : #B = (n + 1) * (2 ^ 2 ^ n) ^ #S₁ := by
    simp [hB, card_product, Fintype.card_finset]
  rw [← hcard, ← Set.ncard_eq_toFinset_card _ hfin, ← hinj.ncard_image,
    ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hsub B.finite_toSet

end NumberField.FormSystem
