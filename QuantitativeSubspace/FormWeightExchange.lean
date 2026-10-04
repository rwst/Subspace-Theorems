/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormSubspaceWeight

/-!
# Exchange arguments for the weight of a subspace

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, §16 (the proof of Lemma 16.2).

The local weight `Submodule.formWeight ℓ c U` is the least `Σ_{i ∈ I} c_i` over the sets `I` with
`(ℓ_i|_U)_{i ∈ I}` a basis of the dual of `U`. This file collects the matroid facts about it that
EF13 §16 uses for the systems induced on a subspace `T` and on the quotient by `T`.

## Main results

* `Submodule.formWeight_le_sum`, `Submodule.formWeight_bot`, `Submodule.formWeight_top`: the
  weight is below every admissible sum; it is `0` on `0` and `Σ_i c_i` on the whole space.
* `Submodule.formWeight_sub_const`, `Submodule.formWeight_div_const`: shifting and scaling `c`.
* `Submodule.formWeight_comp_embedding`: if every form is a combination of forms `ℓ_{g j}` with
  `c_{g j} ≤ c_i`, then only the forms `ℓ_{g j}` matter (an exchange argument).
* `Submodule.formWeight_eq_of_mem_span`: two families that are triangular with respect to `c` in
  both directions have the same weights.
* `Submodule.formWeight_map`: the weight of the image of `U` under an injective map.
* `Submodule.formWeight_comap`: the weight of `π⁻¹(U)` for a surjection `π` with kernel `T`, when
  the forms are those of a basis of the dual of `T` together with forms vanishing on `T`
  (EF13 Lemma 16.2 (ii), locally).

This is part of milestone Q3.5 of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Module Finset

namespace Submodule

variable {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [Finite ι] (ℓ : ι → Module.Dual k V) (c : ι → ℝ)

omit [FiniteDimensional k V] in
theorem bddBelow_formWeightSet (U : Submodule k V) :
    BddBelow ((fun I : Finset ι ↦ ∑ i ∈ I, c i) '' {I | IsFormBasis ℓ U I}) :=
  (Set.toFinite _).bddBelow

omit [FiniteDimensional k V] in
/-- The weight is at most the sum over any basis. -/
theorem formWeight_le_sum {U : Submodule k V} {I : Finset ι} (hI : IsFormBasis ℓ U I) :
    formWeight ℓ c U ≤ ∑ i ∈ I, c i :=
  csInf_le (bddBelow_formWeightSet ℓ c U) ⟨I, hI, rfl⟩

omit [FiniteDimensional k V] [Finite ι] in
/-- The weight is at least any lower bound of the sums over the bases, if there is a basis. -/
theorem le_formWeight {U : Submodule k V} {t : ℝ} (hne : ∃ I, IsFormBasis ℓ U I)
    (h : ∀ I, IsFormBasis ℓ U I → t ≤ ∑ i ∈ I, c i) : t ≤ formWeight ℓ c U := by
  obtain ⟨I, hI⟩ := hne
  exact le_csInf ⟨_, I, hI, rfl⟩ (by rintro _ ⟨J, hJ, rfl⟩; exact h J hJ)

theorem exists_isFormBasis (hℓ : ⨅ i, LinearMap.ker (ℓ i) = ⊥) (U : Submodule k V) :
    ∃ I, IsFormBasis ℓ U I := by
  obtain ⟨I, hI, -⟩ := formWeight_mem ℓ 0 hℓ U
  exact ⟨I, hI⟩

omit [FiniteDimensional k V] in
/-- The weight of `0` is `0`. -/
theorem formWeight_bot : formWeight ℓ c ⊥ = 0 := by
  have h0 : IsFormBasis ℓ ⊥ ∅ := ⟨by simp, by simp⟩
  refine le_antisymm (by simpa using formWeight_le_sum ℓ c h0) (le_formWeight ℓ c ⟨_, h0⟩ ?_)
  intro I hI
  have : I = ∅ := card_eq_zero.1 (by rw [hI.1, finrank_bot])
  simp [this]

/-- The weight of the whole space is `Σ_i c_i` when there are `dim V` forms. -/
theorem formWeight_top [Fintype ι] (hℓ : ⨅ i, LinearMap.ker (ℓ i) = ⊥)
    (hcard : Fintype.card ι = finrank k V) : formWeight ℓ c ⊤ = ∑ i, c i := by
  obtain ⟨I, hI, hIc⟩ := formWeight_mem ℓ c hℓ ⊤
  have : I = univ := eq_univ_of_card I (by rw [hI.1, finrank_top, hcard])
  rw [← hIc, this]

/-- **Shifting `c` by a constant** shifts the weight by the constant times `dim U`. -/
theorem formWeight_sub_const (hℓ : ⨅ i, LinearMap.ker (ℓ i) = ⊥) (t : ℝ) (U : Submodule k V) :
    formWeight ℓ (fun i ↦ c i - t) U = formWeight ℓ c U - t * finrank k U := by
  have hs : ∀ I, IsFormBasis ℓ U I →
      ∑ i ∈ I, (c i - t) = ∑ i ∈ I, c i - t * finrank k U := fun I hI ↦ by
    rw [sum_sub_distrib, sum_const, hI.1, nsmul_eq_mul, mul_comm]
  obtain ⟨I, hI, hIc⟩ := formWeight_mem ℓ c hℓ U
  obtain ⟨J, hJ, hJc⟩ := formWeight_mem ℓ (fun i ↦ c i - t) hℓ U
  dsimp only at hIc hJc
  refine le_antisymm ?_ ?_
  · rw [← hIc, ← hs I hI]
    exact formWeight_le_sum _ _ hI
  · rw [← hJc, hs J hJ]
    linarith [formWeight_le_sum ℓ c hJ]

/-- **Scaling `c` by `s > 0`** scales the weight. -/
theorem formWeight_div_const (hℓ : ⨅ i, LinearMap.ker (ℓ i) = ⊥) {s : ℝ} (hs : 0 < s)
    (U : Submodule k V) : formWeight ℓ (fun i ↦ c i / s) U = formWeight ℓ c U / s := by
  obtain ⟨I, hI, hIc⟩ := formWeight_mem ℓ c hℓ U
  obtain ⟨J, hJ, hJc⟩ := formWeight_mem ℓ (fun i ↦ c i / s) hℓ U
  dsimp only at hIc hJc
  refine le_antisymm ?_ ?_
  · rw [← hIc, sum_div]
    exact formWeight_le_sum _ _ hI
  · rw [← hJc, ← sum_div]
    exact div_le_div_of_nonneg_right (formWeight_le_sum ℓ c hJ) hs.le

omit [FiniteDimensional k V] [Finite ι] in
/-- A form in the span of forms vanishing at `x` vanishes at `x`. -/
theorem apply_eq_zero_of_mem_span {S : Set (Module.Dual k V)} {f : Module.Dual k V}
    (hf : f ∈ span k S) {x : V} (hS : ∀ g ∈ S, g x = 0) : f x = 0 := by
  have : span k S ≤ LinearMap.ker (Module.Dual.eval k V x) :=
    span_le.2 fun g hg ↦ by simpa using hS g hg
  simpa using this hf

omit [FiniteDimensional k V] [Finite ι] in
/-- Span membership of forms restricts to a subspace. -/
theorem domRestrict_mem_span {S : Set ι} {f : Module.Dual k V} (hf : f ∈ span k (ℓ '' S))
    (U : Submodule k V) :
    f.domRestrict U ∈ span k ((fun i ↦ (ℓ i).domRestrict U) '' S) := by
  have := mem_map_of_mem (f := U.subtype.dualMap) hf
  rwa [← span_image, ← Set.image_comp] at this

/-- **Restriction to a subfamily** (an exchange argument): if every `ℓ_i` is a combination of
forms `ℓ_{g j}` with `c_{g j} ≤ c_i`, the weight only depends on the forms `ℓ_{g j}`. -/
theorem formWeight_comp_embedding (hℓ : ⨅ i, LinearMap.ker (ℓ i) = ⊥) {ι₀ : Type*} [Finite ι₀]
    (g : ι₀ ↪ ι) (hg : ∀ i, ℓ i ∈ span k ((ℓ ∘ g) '' {j | c (g j) ≤ c i}))
    (U : Submodule k V) : formWeight (ℓ ∘ g) (c ∘ g) U = formWeight ℓ c U := by
  classical
  have hℓ₀ : ⨅ j, LinearMap.ker ((ℓ ∘ g) j) = ⊥ := by
    refine eq_bot_iff.2 fun x hx ↦ ?_
    rw [← hℓ]
    simp only [mem_iInf, LinearMap.mem_ker, Function.comp_apply] at hx ⊢
    exact fun i ↦ apply_eq_zero_of_mem_span (hg i) (by rintro _ ⟨j, -, rfl⟩; exact hx j)
  set F : ι → Module.Dual k U := fun i ↦ (ℓ i).domRestrict U
  refine le_antisymm ?_ ?_
  · -- Every basis can be moved into the image of `g` without increasing the sum.
    have key0 : ∀ J : Finset ι, IsFormBasis ℓ U J → (∀ i ∈ J, i ∈ Set.range g) →
        formWeight (ℓ ∘ g) (c ∘ g) U ≤ ∑ i ∈ J, c i := by
      intro J hJ hsub
      set J₀ := J.preimage g g.injective.injOn
      have hJmap : J₀.map g = J := by
        ext i
        simp only [Finset.mem_map, mem_preimage, J₀]
        refine ⟨fun ⟨j, hj, hji⟩ ↦ hji ▸ hj, fun hi ↦ ?_⟩
        obtain ⟨j, rfl⟩ := hsub i hi
        exact ⟨j, hi, rfl⟩
      have hJ₀ : IsFormBasis (ℓ ∘ g) U J₀ := by
        refine ⟨by rw [← hJ.1, ← hJmap, card_map], ?_⟩
        have h := hJ.2
        rw [← hJmap, coe_map] at h
        exact h.comp_of_image g.injective.injOn
      calc formWeight (ℓ ∘ g) (c ∘ g) U ≤ ∑ j ∈ J₀, (c ∘ g) j := formWeight_le_sum _ _ hJ₀
        _ = ∑ i ∈ J, c i := by rw [← hJmap, sum_map]; rfl
    have step : ∀ J : Finset ι, IsFormBasis ℓ U J → ∀ j ∈ J, j ∉ Set.range g →
        ∃ J', IsFormBasis ℓ U J' ∧ ∑ i ∈ J', c i ≤ ∑ i ∈ J, c i ∧
          #(J'.filter (· ∉ Set.range g)) < #(J.filter (· ∉ Set.range g)) := by
      intro J hJ j hj hjg
      have hspan := domRestrict_mem_span (ℓ ∘ g) (hg j) U
      have hJ' : LinearIndepOn k F (insert j ↑(J.erase j)) := by
        rw [← coe_insert, insert_erase hj]
        exact hJ.2
      have hnot : F j ∉ span k (F '' ↑(J.erase j)) :=
        ((linearIndepOn_insert (by simp)).1 hJ').2
      obtain ⟨s, hs, hsn⟩ : ∃ s, c (g s) ≤ c j ∧ F (g s) ∉ span k (F '' ↑(J.erase j)) := by
        by_contra hall
        push Not at hall
        refine hnot (span_le.2 ?_ hspan)
        rintro _ ⟨s, hs, rfl⟩
        exact hall s hs
      have hgs : g s ∉ J.erase j := fun h ↦ hsn (subset_span ⟨g s, h, rfl⟩)
      refine ⟨insert (g s) (J.erase j), ⟨?_, ?_⟩, ?_, ?_⟩
      · rw [card_insert_of_notMem hgs, card_erase_of_mem hj,
          Nat.sub_add_cancel (card_pos.2 ⟨j, hj⟩), hJ.1]
      · rw [coe_insert]
        exact (linearIndepOn_insert (by exact_mod_cast hgs)).2
          ⟨hJ.2.mono (coe_subset.2 (erase_subset j J)), hsn⟩
      · rw [sum_insert hgs, sum_erase_eq_sub hj]
        linarith
      · simp only [filter_insert, Set.mem_range_self, not_true_eq_false, ↓reduceIte,
          filter_erase]
        exact card_erase_lt_of_mem (mem_filter.2 ⟨hj, hjg⟩)
    have key : ∀ N (J : Finset ι), IsFormBasis ℓ U J →
        #(J.filter (· ∉ Set.range g)) = N → formWeight (ℓ ∘ g) (c ∘ g) U ≤ ∑ i ∈ J, c i := by
      intro N
      induction N using Nat.strong_induction_on with
      | _ N ih =>
        intro J hJ hN
        by_cases hsub : ∀ i ∈ J, i ∈ Set.range g
        · exact key0 J hJ hsub
        push Not at hsub
        obtain ⟨j, hj, hjg⟩ := hsub
        obtain ⟨J', hJ', hle, hlt⟩ := step J hJ j hj hjg
        exact (ih _ (hN ▸ hlt) J' hJ' rfl).trans hle
    obtain ⟨J, hJ, hJc⟩ := formWeight_mem ℓ c hℓ U
    rw [← hJc]
    exact key _ J hJ rfl
  · obtain ⟨J₀, hJ₀, hJ₀c⟩ := formWeight_mem (ℓ ∘ g) (c ∘ g) hℓ₀ U
    rw [← hJ₀c]
    have hJ : IsFormBasis ℓ U (J₀.map g) := by
      refine ⟨by rw [card_map, hJ₀.1], ?_⟩
      rw [coe_map]
      exact LinearIndepOn.image_of_comp (s := (J₀ : Set ι₀)) g F hJ₀.2
    calc formWeight ℓ c U ≤ ∑ i ∈ J₀.map g, c i := formWeight_le_sum _ _ hJ
      _ = _ := by rw [sum_map]; rfl

/-- **Triangular changes of the forms**: if each `ℓ'_i` is a combination of forms `ℓ_j` with
`c_j ≤ c_i` and vice versa, the two families have the same weights. -/
theorem formWeight_eq_of_mem_span (ℓ' : ι → Module.Dual k V) (hℓ : ⨅ i, LinearMap.ker (ℓ i) = ⊥)
    (h₁ : ∀ i, ℓ' i ∈ span k (ℓ '' {j | c j ≤ c i}))
    (h₂ : ∀ i, ℓ i ∈ span k (ℓ' '' {j | c j ≤ c i})) (U : Submodule k V) :
    formWeight ℓ' c U = formWeight ℓ c U := by
  set F : ι ⊕ ι → Module.Dual k V := Sum.elim ℓ ℓ'
  set cF : ι ⊕ ι → ℝ := Sum.elim c c
  have hF : ⨅ i, LinearMap.ker (F i) = ⊥ := by
    refine eq_bot_iff.2 fun x hx ↦ ?_
    rw [← hℓ]
    simp only [mem_iInf, LinearMap.mem_ker] at hx ⊢
    exact fun i ↦ hx (Sum.inl i)
  have hℓ' : ⨅ i, LinearMap.ker (ℓ' i) = ⊥ := by
    refine eq_bot_iff.2 fun x hx ↦ ?_
    rw [← hℓ]
    simp only [mem_iInf, LinearMap.mem_ker] at hx ⊢
    exact fun i ↦ apply_eq_zero_of_mem_span (h₂ i) (by rintro _ ⟨j, -, rfl⟩; exact hx j)
  have hinl := formWeight_comp_embedding F cF hF Function.Embedding.inl (by
    rintro (i | i)
    · exact subset_span ⟨i, le_refl (c i), rfl⟩
    · exact h₁ i) U
  have hinr := formWeight_comp_embedding F cF hF Function.Embedding.inr (by
    rintro (i | i)
    · exact h₂ i
    · exact subset_span ⟨i, le_refl (c i), rfl⟩) U
  exact hinr.trans hinl.symm

omit [FiniteDimensional k V] [Finite ι] in
/-- **The weight of an image** under an injective linear map. -/
theorem formWeight_map {V₀ : Type*} [AddCommGroup V₀] [Module k V₀] (φ : V₀ →ₗ[k] V)
    (hφ : Function.Injective φ) (U : Submodule k V₀) :
    formWeight ℓ c (U.map φ) = formWeight (fun i ↦ (ℓ i).comp φ) c U := by
  set e := Submodule.equivMapOfInjective φ hφ U
  have hfam : (fun i ↦ ((ℓ i).comp φ).domRestrict U) =
      e.toLinearMap.dualMap ∘ fun i ↦ (ℓ i).domRestrict (U.map φ) := by
    funext i
    ext x
    rfl
  have hinj : Function.Injective e.toLinearMap.dualMap :=
    LinearMap.dualMap_injective_of_surjective e.surjective
  have hiff : ∀ I, IsFormBasis ℓ (U.map φ) I ↔ IsFormBasis (fun i ↦ (ℓ i).comp φ) U I := by
    intro I
    rw [IsFormBasis, IsFormBasis, ← e.finrank_eq, hfam]
    refine and_congr Iff.rfl ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · exact h.map' _ (LinearMap.ker_eq_bot.2 hinj)
    · exact LinearIndependent.of_comp _ h
  simp only [formWeight, hiff]

section Comap

variable {V'' : Type*} [AddCommGroup V''] [Module k V''] [FiniteDimensional k V'']
  (π : V →ₗ[k] V'') (U : Submodule k V'')

/-- `π` from `π⁻¹(U)` onto `U`. -/
noncomputable def comapRestrict : U.comap π →ₗ[k] U := π.restrict fun _ hx ↦ hx

omit [FiniteDimensional k V] [FiniteDimensional k V''] in
theorem comapRestrict_surjective (hπ : Function.Surjective π) :
    Function.Surjective (comapRestrict π U) := fun u ↦ by
  obtain ⟨x, hx⟩ := hπ u
  exact ⟨⟨x, show π x ∈ U from hx ▸ u.2⟩, Subtype.ext hx⟩

omit [FiniteDimensional k V''] in
/-- `dim π⁻¹(U) = dim U + dim ker π`. -/
theorem finrank_comap_eq (hπ : Function.Surjective π) :
    finrank k (U.comap π) = finrank k U + finrank k (LinearMap.ker π) := by
  have h := LinearMap.finrank_range_add_finrank_ker (comapRestrict π U)
  rw [LinearMap.range_eq_top.2 (comapRestrict_surjective π U hπ), finrank_top] at h
  have hker : LinearMap.ker (comapRestrict π U) = (LinearMap.ker π).comap (U.comap π).subtype := by
    ext x
    simp [comapRestrict, LinearMap.restrict_apply, Subtype.ext_iff]
  have hle : LinearMap.ker π ≤ U.comap π := fun x hx ↦ by
    simp only [mem_comap, LinearMap.mem_ker.1 hx, zero_mem]
  rw [hker, (comapSubtypeEquivOfLe hle).finrank_eq] at h
  omega

omit [FiniteDimensional k V] [Finite ι] in
theorem _root_.LinearIndepOn.map_of_injective {M M' κ : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup M'] [Module k M'] {v : κ → M} {s : Set κ} (h : LinearIndepOn k v s)
    (f : M →ₗ[k] M') (hf : Function.Injective f) : LinearIndepOn k (f ∘ v) s :=
  LinearIndependent.map' h f (LinearMap.ker_eq_bot.2 hf)

omit [FiniteDimensional k V] [Finite ι] in
theorem _root_.LinearIndepOn.of_comp_linearMap {M M' κ : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup M'] [Module k M'] {v : κ → M} {s : Set κ} (f : M →ₗ[k] M')
    (h : LinearIndepOn k (f ∘ v) s) : LinearIndepOn k v s :=
  LinearIndependent.of_comp f h

/-- **The weight of a preimage** (EF13 Lemma 16.2 (ii), locally): let `π` be surjective with
kernel `T`, let the `ℓ_i`, `i ∈ I`, restrict to a basis of the dual of `T`, and let the other
forms be `ℓ_{g s} = h_s ∘ π`. Then `w(π⁻¹ U) = Σ_{i ∈ I} c_i + w_h(U)`. -/
theorem formWeight_comap (hℓ : ⨅ i, LinearMap.ker (ℓ i) = ⊥) (hπ : Function.Surjective π)
    (I : Finset ι)
    (hI : LinearIndepOn k (fun i ↦ (ℓ i).domRestrict (LinearMap.ker π)) I)
    (hIcard : #I = finrank k (LinearMap.ker π)) {ι'' : Type*} [Finite ι''] (g : ι'' ↪ ι)
    (hg : ∀ i, i ∉ I ↔ i ∈ Set.range g) (h : ι'' → Module.Dual k V'')
    (hh : ∀ s, ℓ (g s) = (h s).comp π) (hh0 : ⨅ s, LinearMap.ker (h s) = ⊥) :
    formWeight ℓ c (U.comap π) = ∑ i ∈ I, c i + formWeight h (c ∘ g) U := by
  classical
  set W := U.comap π
  set F : ι → Module.Dual k W := fun i ↦ (ℓ i).domRestrict W
  set hU : ι'' → Module.Dual k U := fun s ↦ (h s).domRestrict U
  set P := (comapRestrict π U).dualMap
  have hP : Function.Injective P :=
    LinearMap.dualMap_injective_of_surjective (comapRestrict_surjective π U hπ)
  have hFg : F ∘ g = P ∘ hU := by
    funext s
    ext x
    simp [F, hU, P, comapRestrict, LinearMap.restrict_apply, hh s]
  have hle : LinearMap.ker π ≤ W := fun x hx ↦ by
    simp only [W, mem_comap, LinearMap.mem_ker.1 hx, zero_mem]
  set Rk := (inclusion hle).dualMap
  have hRF : Rk ∘ F = fun i ↦ (ℓ i).domRestrict (LinearMap.ker π) := by
    funext i
    ext x
    rfl
  have hRg : ∀ s, Rk (F (g s)) = 0 := fun s ↦ by
    ext x
    simp [Rk, F, hh s, LinearMap.mem_ker.1 x.2]
  have hIW : LinearIndepOn k F I := LinearIndepOn.of_comp_linearMap Rk (hRF ▸ hI)
  have hdim := finrank_comap_eq π U hπ
  have hdisjI : ∀ s, g s ∉ I := fun s ↦ (hg (g s)).2 ⟨s, rfl⟩
  refine le_antisymm ?_ ?_
  · obtain ⟨J'', hJ'', hJc⟩ := formWeight_mem h (c ∘ g) hh0 U
    dsimp only at hJc
    have hd : Disjoint I (J''.map g) := disjoint_left.2 fun i hi hi' ↦ by
      obtain ⟨s, -, rfl⟩ := Finset.mem_map.1 hi'
      exact hdisjI s hi
    have hJ''W : LinearIndepOn k F (g '' J'') := by
      refine LinearIndepOn.image_of_comp g F ?_
      rw [hFg]
      exact LinearIndepOn.map_of_injective hJ''.2 P hP
    have hspan : Disjoint (span k (F '' I)) (span k (F '' (g '' J''))) := by
      refine disjoint_def.2 fun x hx hx' ↦ ?_
      have h0 : Rk x = 0 := by
        have : span k (F '' (g '' J'')) ≤ LinearMap.ker Rk :=
          span_le.2 (by rintro _ ⟨_, ⟨s, -, rfl⟩, rfl⟩; exact hRg s)
        exact this hx'
      obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination k).1 hx
      rw [Finsupp.apply_linearCombination, hRF] at h0
      rw [linearIndepOn_iff.1 hI l hl h0, map_zero]
    have hJ : IsFormBasis ℓ W (I ∪ J''.map g) := by
      refine ⟨?_, ?_⟩
      · rw [card_union_of_disjoint hd, card_map, hJ''.1, hIcard, hdim]
        ring
      · rw [coe_union, coe_map]
        exact hIW.union hJ''W hspan
    calc formWeight ℓ c W ≤ ∑ i ∈ I ∪ J''.map g, c i := formWeight_le_sum _ _ hJ
      _ = _ := by rw [sum_union hd, sum_map, ← hJc]; rfl
  · obtain ⟨J, hJ, hJc⟩ := formWeight_mem ℓ c hℓ W
    dsimp only at hJc
    rw [← hJc]
    set J'' := J.preimage g g.injective.injOn
    set JI := J.filter (· ∈ I)
    have hsplit : J = JI ∪ J''.map g := by
      ext i
      simp only [mem_union, mem_filter, Finset.mem_map, mem_preimage, JI, J'']
      constructor
      · intro hi
        by_cases hiI : i ∈ I
        · exact Or.inl ⟨hi, hiI⟩
        · obtain ⟨s, rfl⟩ := (hg i).1 hiI
          exact Or.inr ⟨s, hi, rfl⟩
      · rintro (⟨hi, -⟩ | ⟨s, hs, rfl⟩) <;> assumption
    have hd : Disjoint JI (J''.map g) := disjoint_left.2 fun i hi hi' ↦ by
      obtain ⟨s, -, rfl⟩ := Finset.mem_map.1 hi'
      exact hdisjI s (mem_filter.1 hi).2
    have hJ''ind : LinearIndepOn k hU J'' := by
      refine LinearIndepOn.of_comp_linearMap P ?_
      rw [← hFg]
      refine (hJ.2.mono ?_).comp_of_image g.injective.injOn
      rintro _ ⟨s, hs, rfl⟩
      exact mem_preimage.1 hs
    have hcard'' : #J'' ≤ finrank k U := by
      have := LinearIndependent.fintype_card_le_finrank hJ''ind
      simpa only [coe_sort_coe, Fintype.card_coe, Subspace.dual_finrank_eq] using this
    have hcardI : #JI ≤ #I := card_le_card fun i hi ↦ (mem_filter.1 hi).2
    have htot : #JI + #J'' = #I + finrank k U := by
      have := hJ.1
      rw [hsplit, card_union_of_disjoint hd, card_map, hdim, ← hIcard] at this
      omega
    have hJI : JI = I := eq_of_subset_of_card_le (fun i hi ↦ (mem_filter.1 hi).2) (by omega)
    have hJ''b : IsFormBasis h U J'' := ⟨by omega, hJ''ind⟩
    calc ∑ i ∈ I, c i + formWeight h (c ∘ g) U ≤ ∑ i ∈ I, c i + ∑ s ∈ J'', (c ∘ g) s :=
          (add_le_add_iff_left _).2 (formWeight_le_sum _ _ hJ''b)
      _ = ∑ i ∈ J, c i := by rw [hsplit, sum_union hd, sum_map, hJI]; rfl

end Comap

end Submodule
