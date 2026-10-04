/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormSubspaceWeight

-- Used only inside proofs.
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The exceptional subspace for coordinate forms and their sum

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, Lemma 15.3 and the remark after (2.21).

If every form of `L` is one of `X_1, …, X_n, X_1 + ⋯ + X_n` (EF13 (15.7)), the exceptional subspace
`T = T(L, c)` of (2.21) is cut out by sums over disjoint blocks of coordinates:
`T = {x : Σ_{j ∈ I_l} x_j = 0 for l = 1, …, p}` for nonempty pairwise disjoint `I_1, …, I_p`.

The proof follows EF13. The space `H` of the `u ∈ Ω^{n+1}` such that
`Σ_j u_j X_j - u_0 Σ_j X_j` vanishes on `T` contains `1`. For `b ∈ H` with no zero coordinate, the
diagonal map `x ↦ (b_j x_j)` changes each form of `L` on `T` by a nonzero factor, so it preserves
the weight of `T`. By the uniqueness of `T` it maps `T` to itself, and then `H` is closed under
coordinatewise products. A subalgebra of `Ω^{n+1}` contains the indicator of each class of
coordinates on which all its elements agree; the classes not containing the coordinate `0` are the
blocks.

## Main definitions

* `NumberField.FormSystem.HasCoordSumForms L`: EF13 (15.7).
* `NumberField.FormSystem.sumSpace T`: EF13's space `H`, with `u_0` the coordinate `none`.

## Main results

* `Submodule.formWeight_eq_of_linearEquiv`: an isomorphism changing each form by a nonzero
  factor preserves the local weight.
* `Subalgebra.exists_indicator_mem`: a subalgebra of `kˢ` contains the indicators of the classes of
  coordinates on which its elements agree.
* `NumberField.FormSystem.mul_mem_sumSpace`: `H` is closed under products.
* `NumberField.FormSystem.exists_blockSums_of_isDestabilizing`: EF13 Lemma 15.3.

This is milestone Q3.2b of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Module Finset

namespace Submodule

variable {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [Finite ι] (ℓ : ι → Module.Dual k V) (c : ι → ℝ)

omit [FiniteDimensional k V] [Finite ι] in
/-- An isomorphism `U ≃ U'` that multiplies each form by a nonzero factor preserves the local
weight (2.19). -/
theorem formWeight_eq_of_linearEquiv {U U' : Submodule k V} (e : U ≃ₗ[k] U') (β : ι → kˣ)
    (h : ∀ i (x : U), ℓ i (e x) = β i * ℓ i x) : formWeight ℓ c U' = formWeight ℓ c U := by
  have hf : ∀ i, e.dualMap ((ℓ i).domRestrict U') = β i • (ℓ i).domRestrict U := fun i ↦
    LinearMap.ext fun x ↦ by simp [h, Units.smul_def]
  have key : ∀ I, IsFormBasis ℓ U' I ↔ IsFormBasis ℓ U I := fun I ↦ by
    rw [IsFormBasis, IsFormBasis, ← e.finrank_eq]
    refine and_congr_right fun _ ↦ ⟨fun hI ↦ ?_, fun hI ↦ ?_⟩ <;> unfold LinearIndepOn at hI ⊢
    · have := (hI.map' e.dualMap.toLinearMap e.dualMap.ker).units_smul fun i ↦ (β i)⁻¹
      convert this using 1
      ext i : 1
      simp [hf, Function.comp_def]
    · have := (hI.units_smul fun i ↦ β i).map' e.dualMap.symm.toLinearMap e.dualMap.symm.ker
      convert this using 1
      ext i : 1
      change _ = e.dualMap.symm (β i • (ℓ i).domRestrict U)
      rw [← hf, LinearEquiv.symm_apply_apply]
  simp only [formWeight, key]

end Submodule

namespace Subalgebra

/-- A subalgebra `S` of `kˢ` contains the indicator of the class of `i`, the coordinates `j` with
`a j = a i` for all `a ∈ S`. -/
theorem exists_indicator_mem {k σ : Type*} [Field k] [Finite σ] (S : Subalgebra k (σ → k))
    (i : σ) : ∃ e ∈ S, (∀ j, (∀ a ∈ S, a j = a i) → e j = 1) ∧
      ∀ j, ¬(∀ a ∈ S, a j = a i) → e j = 0 := by
  classical
  have := Fintype.ofFinite σ
  have hsep : ∀ j, ¬(∀ a ∈ S, a j = a i) → ∃ e ∈ S, e i = 1 ∧ e j = 0 := fun j hj ↦ by
    simp only [not_forall] at hj
    obtain ⟨a, ha, hne⟩ := hj
    have hd : a i - a j ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    refine ⟨(a i - a j)⁻¹ • (a - algebraMap k _ (a j)),
      S.smul_mem (S.sub_mem ha (S.algebraMap_mem _)) _, ?_, ?_⟩
    · simp [inv_mul_cancel₀ hd]
    · simp
  choose! e heS hei hej using hsep
  refine ⟨∏ j ∈ univ.filter (fun j ↦ ¬∀ a ∈ S, a j = a i), e j,
    S.prod_mem fun j hj ↦ heS j (mem_filter.1 hj).2, fun j hj ↦ ?_, fun j hj ↦ ?_⟩
  · rw [Finset.prod_apply]
    refine prod_eq_one fun j' hj' ↦ ?_
    rw [hj _ (heS j' (mem_filter.1 hj').2), hei j' (mem_filter.1 hj').2]
  · rw [Finset.prod_apply]
    exact prod_eq_zero (mem_filter.2 ⟨mem_univ _, hj⟩) (hej j hj)

end Subalgebra

namespace NumberField

open Submodule

namespace FormSystem

variable {K ι : Type*} [Field K] [NumberField K] [Fintype ι] [DecidableEq ι]
  (L : FormSystem K ι) (c : FormExponent K ι)
variable {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- The coefficient vector of `X_j` for some `j`, or of `X_1 + ⋯ + X_n`. -/
def IsCoordOrSum (r : ι → K) : Prop :=
  (∃ j, r = Pi.single j 1) ∨ r = fun _ ↦ 1

/-- **EF13 (15.7)**: every form of `L` is one of `X_1, …, X_n, X_1 + ⋯ + X_n`. -/
def HasCoordSumForms : Prop :=
  ∀ f ∈ L.forms, IsCoordOrSum f

/-- **EF13's space `H`** in the proof of Lemma 15.3: the `u ∈ Ω^{n+1}` such that
`Σ_j u_j X_j - u_0 Σ_j X_j` vanishes on `T`. The coordinate `u_0` is `u none`. -/
def sumSpace (T : Submodule Ω (ι → Ω)) : Submodule Ω (Option ι → Ω) where
  carrier := {u | ∀ x ∈ T, ∑ j, (u (some j) - u none) * x j = 0}
  add_mem' {u u'} hu hu' x hx := by
    simp only [Pi.add_apply, add_sub_add_comm, add_mul, sum_add_distrib, hu x hx, hu' x hx,
      add_zero]
  zero_mem' x _ := by simp
  smul_mem' a u hu x hx := by
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, mul_assoc, ← mul_sum, hu x hx, mul_zero]

omit [DecidableEq ι] in
theorem one_mem_sumSpace (T : Submodule Ω (ι → Ω)) : (1 : Option ι → Ω) ∈ sumSpace T :=
  fun x _ ↦ by simp

/-- The diagonal automorphism `x ↦ (b_j x_j)` of `Ωⁿ`. -/
noncomputable def diagEquiv (b : ι → Ω) (hb : ∀ j, b j ≠ 0) : (ι → Ω) ≃ₗ[Ω] (ι → Ω) :=
  LinearEquiv.piCongrRight fun j ↦ LinearEquiv.smulOfNeZero Ω Ω (b j) (hb j)

omit [Fintype ι] [DecidableEq ι] in
theorem diagEquiv_apply (b : ι → Ω) (hb : ∀ j, b j ≠ 0) (x : ι → Ω) :
    diagEquiv b hb x = fun j ↦ b j * x j :=
  rfl

omit [NumberField K] [Fintype ι] in
/-- On `T`, the diagonal map by `b ∈ H` multiplies `X_j` by `b_j` and `X_1 + ⋯ + X_n` by `b_0`. -/
theorem exists_matrixForms_diag {A : Matrix ι ι K} {i : ι} (hA : IsCoordOrSum (A i))
    [Fintype ι] {T : Submodule Ω (ι → Ω)} {b : Option ι → Ω} (hb : b ∈ sumSpace T) :
    ∃ β ∈ Set.range b, ∀ x ∈ T,
      matrixForms A i (fun j ↦ b (some j) * x j) = β * matrixForms A i x := by
  rcases hA with ⟨j, hj⟩ | h1
  · refine ⟨b (some j), ⟨_, rfl⟩, fun x _ ↦ ?_⟩
    simp [matrixForms_apply, Matrix.mulVec, dotProduct, hj, Pi.single_apply]
  · refine ⟨b none, ⟨_, rfl⟩, fun x hx ↦ ?_⟩
    have := hb x hx
    simp only [sub_mul, sum_sub_distrib, ← mul_sum] at this
    simp only [matrixForms_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, h1, map_one,
      one_mul]
    linear_combination this

omit [NumberField K] in
/-- On `T`, the diagonal map by `b ∈ H` preserves the local weight for forms as in (15.7). -/
theorem formWeight_map_diagEquiv {A : Matrix ι ι K} (hA : ∀ i, IsCoordOrSum (A i)) (e : ι → ℝ)
    {T : Submodule Ω (ι → Ω)} {b : Option ι → Ω} (hb : b ∈ sumSpace T) (hb0 : ∀ o, b o ≠ 0) :
    formWeight (matrixForms A) e
        (T.map (diagEquiv (fun j ↦ b (some j)) fun _ ↦ hb0 _).toLinearMap) =
      formWeight (matrixForms A) e T := by
  choose β hβ hβx using fun i ↦ exists_matrixForms_diag (hA i) hb
  have hβ0 : ∀ i, β i ≠ 0 := fun i ↦ by
    obtain ⟨o, ho⟩ := hβ i
    exact ho ▸ hb0 o
  exact formWeight_eq_of_linearEquiv _ _ ((diagEquiv _ _).submoduleMap T)
    (fun i ↦ Units.mk0 (β i) (hβ0 i)) fun i x ↦ hβx i x x.2

/-- On `T`, the diagonal map by `b ∈ H` preserves the weight `w_{L,c}`. -/
theorem subspaceWeight_map_diagEquiv (hL : L.HasCoordSumForms) {T : Submodule Ω (ι → Ω)}
    {b : Option ι → Ω} (hb : b ∈ sumSpace T) (hb0 : ∀ o, b o ≠ 0) :
    L.subspaceWeight c (T.map (diagEquiv (fun j ↦ b (some j)) fun _ ↦ hb0 _).toLinearMap) =
      L.subspaceWeight c T := by
  simp only [subspaceWeight]
  congr 1
  · exact sum_congr rfl fun v _ ↦ formWeight_map_diagEquiv
      (fun i ↦ hL _ (L.arch_mem_forms v i)) _ hb hb0
  · exact finsum_congr fun v ↦ formWeight_map_diagEquiv
      (fun i ↦ hL _ (L.fin_mem_forms v i)) _ hb hb0

/-- The diagonal map by `b ∈ H` with no zero coordinate maps the exceptional subspace `T` to
itself. -/
theorem diag_mem_of_isDestabilizing (hL : L.HasCoordSumForms) {T : Submodule Ω (ι → Ω)}
    (hT : IsDestabilizing (L.subspaceWeight c) ⊤ T) {b : Option ι → Ω} (hb : b ∈ sumSpace T)
    (hb0 : ∀ o, b o ≠ 0) {x : ι → Ω} (hx : x ∈ T) : (fun j ↦ b (some j) * x j) ∈ T := by
  set D := diagEquiv (fun j ↦ b (some j)) fun _ ↦ hb0 _
  have hfin : finrank Ω ↥(T.map D.toLinearMap) = finrank Ω T := D.finrank_map_eq T
  have hw : L.subspaceWeight c (T.map D.toLinearMap) = L.subspaceWeight c T :=
    L.subspaceWeight_map_diagEquiv c hL hb hb0
  have hlt : T.map D.toLinearMap < ⊤ := by
    have := (Submodule.orderIsoMapComap D).strictMono hT.lt
    simpa using this
  have hle := hT.least _ hlt (by simp only [weightSlope, hw, hfin])
  rw [Submodule.eq_of_le_of_finrank_eq hle hfin.symm]
  exact ⟨x, hx, rfl⟩

/-- **EF13 Lemma 15.3**, main step: `H` is closed under coordinatewise products. -/
theorem mul_mem_sumSpace (hL : L.HasCoordSumForms) {T : Submodule Ω (ι → Ω)}
    (hT : IsDestabilizing (L.subspaceWeight c) ⊤ T) {a u : Option ι → Ω} (ha : a ∈ sumSpace T)
    (hu : u ∈ sumSpace T) : a * u ∈ sumSpace T := by
  classical
  have : Infinite Ω := Infinite.of_injective (algebraMap K Ω) (algebraMap K Ω).injective
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (univ.image fun o ↦ -a o)
  set b := a + t • (1 : Option ι → Ω)
  have hb : b ∈ sumSpace T := add_mem ha (Submodule.smul_mem _ t (one_mem_sumSpace T))
  have hb0 : ∀ o, b o ≠ 0 := fun o h ↦ ht <| mem_image.2 ⟨o, mem_univ _, by
    simp only [b, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at h
    linear_combination -h⟩
  have hbu : b * u ∈ sumSpace T := fun x hx ↦ by
    have h1 := hu _ (L.diag_mem_of_isDestabilizing c hL hT hb hb0 hx)
    have h2 := hb x hx
    have : ∑ j, ((b * u) (some j) - (b * u) none) * x j =
        ∑ j, (u (some j) - u none) * (b (some j) * x j) +
          u none * ∑ j, (b (some j) - b none) * x j := by
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun j _ ↦ ?_
      simp only [Pi.mul_apply]
      ring
    rw [this, h1, h2, mul_zero, add_zero]
  have : a * u = b * u - t • u := by
    ext o
    simp only [b, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul]
    ring
  rw [this]
  exact sub_mem hbu (Submodule.smul_mem _ t hu)

/-- **EF13 Lemma 15.3**: if every form of `L` is one of `X_1, …, X_n, X_1 + ⋯ + X_n`, the
exceptional subspace `T = T(L, c)` is `{x : Σ_{j ∈ I} x_j = 0 for I ∈ 𝓘}` for a set `𝓘` of
nonempty pairwise disjoint blocks of coordinates. -/
theorem exists_blockSums_of_isDestabilizing (hL : L.HasCoordSumForms) {T : Submodule Ω (ι → Ω)}
    (hT : IsDestabilizing (L.subspaceWeight c) ⊤ T) :
    ∃ 𝓘 : Finset (Finset ι), (∀ I ∈ 𝓘, I.Nonempty) ∧ (𝓘 : Set (Finset ι)).PairwiseDisjoint id ∧
      ∀ x, x ∈ T ↔ ∀ I ∈ 𝓘, ∑ j ∈ I, x j = 0 := by
  classical
  set S := (sumSpace T).toSubalgebra (one_mem_sumSpace T) fun _ _ ↦ L.mul_mem_sumSpace c hL hT
  set R : Option ι → Option ι → Prop := fun o o' ↦ ∀ u ∈ sumSpace T, u o = u o'
  set g : ι → Finset ι := fun j ↦ univ.filter fun k ↦ R (some k) (some j)
  set s := univ.filter fun j ↦ ¬R (some j) none
  have hg : ∀ {j k}, k ∈ g j ↔ R (some k) (some j) := by simp [g]
  have hgg : ∀ {j j'}, R (some j) (some j') → g j = g j' := fun h ↦ by
    ext k
    rw [hg, hg]
    exact ⟨fun h' u hu ↦ (h' u hu).trans (h u hu), fun h' u hu ↦ (h' u hu).trans (h u hu).symm⟩
  refine ⟨s.image g, ?_, ?_, fun x ↦ ⟨fun hx I hI ↦ ?_, fun hx ↦ ?_⟩⟩
  · rintro _ hI
    obtain ⟨j, -, rfl⟩ := mem_image.1 hI
    exact ⟨j, hg.2 fun _ _ ↦ rfl⟩
  · rintro _ hI _ hI' hne
    obtain ⟨j, -, rfl⟩ := mem_image.1 hI
    obtain ⟨j', -, rfl⟩ := mem_image.1 hI'
    refine Finset.disjoint_left.2 fun k hk hk' ↦ hne ?_
    rw [id, hg] at hk hk'
    exact hgg fun u hu ↦ (hk u hu).symm.trans (hk' u hu)
  · obtain ⟨j, hj, rfl⟩ := mem_image.1 hI
    obtain ⟨e, he, he1, he0⟩ := S.exists_indicator_mem (some j)
    have hS : ∀ {a}, a ∈ S ↔ a ∈ sumSpace T := Submodule.mem_toSubalgebra
    have hn : e none = 0 :=
      he0 none fun h ↦ (mem_filter.1 hj).2 fun u hu ↦ (h u (hS.2 hu)).symm
    calc ∑ k ∈ g j, x k = ∑ k, (e (some k) - e none) * x k := by
          rw [sum_filter]
          refine sum_congr rfl fun k _ ↦ ?_
          split_ifs with hk
          · rw [he1 _ fun a ha ↦ hk a (hS.1 ha), hn, sub_zero, one_mul]
          · rw [he0 _ fun h ↦ hk fun a ha ↦ h a (hS.2 ha), hn, sub_zero, zero_mul]
      _ = 0 := hS.1 he x hx
  · by_contra hxT
    obtain ⟨f, hfx, hfT⟩ := T.exists_dual_map_eq_bot_of_notMem hxT inferInstance
    set u : Option ι → Ω := fun o ↦ o.elim 0 fun i ↦ f fun j ↦ if i = j then 1 else 0
    have hfy : ∀ y, f y = ∑ j, (u (some j) - u none) * y j := fun y ↦ by
      rw [LinearMap.pi_apply_eq_sum_univ f y]
      simp [u, mul_comm]
    have hu : u ∈ sumSpace T := fun y hy ↦ by
      rw [← hfy]
      have : f y ∈ T.map f := mem_map_of_mem hy
      rwa [hfT, Submodule.mem_bot] at this
    have h0 : ∀ j ∉ s, (u (some j) - u none) * x j = 0 := fun j hj ↦ by
      rw [mem_filter, not_and, not_not] at hj
      rw [hj (mem_univ _) u hu, sub_self, zero_mul]
    refine hfx ?_
    rw [hfy, ← sum_subset (subset_univ s) fun j _ hj ↦ h0 j hj,
      ← sum_fiberwise_of_maps_to (t := s.image g) fun j hj ↦ mem_image_of_mem g hj]
    refine sum_eq_zero fun I hI ↦ ?_
    obtain ⟨j₀, hj₀, rfl⟩ := mem_image.1 hI
    have hfib : s.filter (fun j ↦ g j = g j₀) = g j₀ := by
      ext j
      rw [mem_filter, hg]
      refine ⟨fun ⟨_, h⟩ ↦ hg.1 (h ▸ hg.2 fun _ _ ↦ rfl), fun h ↦ ⟨?_, hgg h⟩⟩
      refine mem_filter.2 ⟨mem_univ _, fun h' ↦ (mem_filter.1 hj₀).2 fun v hv ↦ ?_⟩
      exact (h v hv).symm.trans (h' v hv)
    rw [hfib, sum_congr rfl fun j hj ↦ by rw [hg.1 hj u hu], ← mul_sum,
      hx _ (mem_image_of_mem g hj₀), mul_zero]

end FormSystem

end NumberField
