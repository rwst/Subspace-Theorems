/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

-- Used only inside proofs.
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Bases adapted to a filtration

Let `S a` be finite-dimensional subspaces of a vector space, indexed by a finite subset `T` of a
linearly ordered type, and `W_{≥ a} = ⨆_{e ∈ T, e ≥ a} S e`, `W_{> a} = ⨆_{e ∈ T, e > a} S e` the
filtration they generate. Then `⨆_{e ∈ T} S e` has a basis `b` with labels `ℓ`, `b x ∈ S (ℓ x)`,
and exactly `dim W_{≥ a} - dim W_{> a}` elements labelled `a`
(`Submodule.exists_adapted_family`). This is the basis of Corvaja–Zannier, *On a general Thue's
equation*, Amer. J. Math. 126 (2004), §3, chosen from the last `W_{(i)}` back to the first.

The dimensions of the quotients are computed with
`Submodule.finrank_map_sup_add_finrank_inf_comap`:
`dim (f P + W) + dim (P ∩ f⁻¹ W) = dim W + dim P`.
-/

@[expose] public section

open Module

namespace Submodule

variable {k U V : Type*} [Field k] [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]

/-- Rank–nullity on a subspace: `dim f(Q) + dim (Q ∩ ker f) = dim Q`. -/
theorem finrank_map_add_finrank_inf_ker (f : U →ₗ[k] V) (Q : Submodule k U)
    [FiniteDimensional k Q] : finrank k (Q.map f) + finrank k ↥(Q ⊓ LinearMap.ker f) =
      finrank k Q := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict Q)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  rwa [← map_comap_subtype, finrank_map_subtype_eq]

/-- `dim (f P + W) + dim (P ∩ f⁻¹ W) = dim W + dim P`. -/
theorem finrank_map_sup_add_finrank_inf_comap (f : U →ₗ[k] V) (P : Submodule k U)
    [FiniteDimensional k P] (W : Submodule k V) [FiniteDimensional k W] :
    finrank k ↥(P.map f ⊔ W) + finrank k ↥(P ⊓ W.comap f) = finrank k W + finrank k P := by
  have h1 := finrank_sup_add_finrank_inf_eq (P.map f) W
  have h2 := finrank_map_add_finrank_inf_ker f P
  have h3 := finrank_map_add_finrank_inf_ker f (P ⊓ W.comap f)
  have h4 : (P ⊓ W.comap f).map f = P.map f ⊓ W := by
    ext y
    simp only [mem_map, mem_inf, mem_comap]
    constructor
    · rintro ⟨x, ⟨hxP, hxW⟩, rfl⟩
      exact ⟨⟨x, hxP, rfl⟩, hxW⟩
    · rintro ⟨⟨x, hxP, rfl⟩, hxW⟩
      exact ⟨x, ⟨hxP, hxW⟩, rfl⟩
  have h5 : P ⊓ W.comap f ⊓ LinearMap.ker f = P ⊓ LinearMap.ker f := by
    rw [inf_assoc, show W.comap f ⊓ LinearMap.ker f = LinearMap.ker f from
      inf_eq_right.mpr fun x hx ↦ by simp [mem_comap, LinearMap.mem_ker.mp hx]]
  rw [h4, h5] at h3
  omega

variable {α : Type*} [LinearOrder α]

/-- **A basis adapted to a filtration.** For finite-dimensional `S a`, `a ∈ T`, the space
`⨆_{a ∈ T} S a` has a basis `b` with labels `ℓ x ∈ T`, `b x ∈ S (ℓ x)`, and as many elements
labelled `a` as `dim (S a + W_{> a}) - dim W_{> a}`, where `W_{> a} = ⨆_{e ∈ T, e > a} S e`. -/
theorem exists_adapted_family (S : α → Submodule k V) [∀ a, FiniteDimensional k (S a)]
    (T : Finset α) :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → V) (ℓ : ι → α), (∀ x, ℓ x ∈ T) ∧
      (∀ x, b x ∈ S (ℓ x)) ∧ LinearIndependent k b ∧ span k (Set.range b) = T.sup S ∧
      ∀ a ∈ T, (Finset.univ.filter (ℓ · = a)).card +
          finrank k ↥((T.filter (a < ·)).sup S) =
        finrank k ↥(S a ⊔ (T.filter (a < ·)).sup S) := by
  classical
  induction T using Finset.induction_on_min with
  | empty =>
    exact ⟨Empty, inferInstance, Empty.elim, Empty.elim, fun x ↦ x.elim, fun x ↦ x.elim,
      linearIndependent_empty_type, by simp, by simp⟩
  | insert a T ha ih =>
  obtain ⟨ι, _, b, ℓ, hℓ, hb, hli, hspan, hcount⟩ := ih
  have haT : a ∉ T := fun h ↦ lt_irrefl a (ha a h)
  set W := T.sup S
  -- A complement `C` of `S a ⊓ W` in `S a`.
  obtain ⟨C₀, hC₀⟩ := exists_isCompl (comap (S a).subtype W)
  set C := C₀.map (S a).subtype
  have hCS : C ≤ S a := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hCW : Disjoint C W := by
    rw [disjoint_iff, eq_bot_iff]
    rintro _ ⟨⟨x, hxC, rfl⟩, hxW⟩
    have : x ∈ comap (S a).subtype W := hxW
    have := hC₀.disjoint.le_bot ⟨this, hxC⟩
    simp only [mem_bot] at this
    simp [this]
  have hCsup : C ⊔ W = S a ⊔ W := by
    refine le_antisymm (sup_le_sup_right hCS W) (sup_le (fun y hy ↦ ?_) le_sup_right)
    have hmem : (⟨y, hy⟩ : S a) ∈ comap (S a).subtype W ⊔ C₀ := hC₀.sup_eq_top ▸ mem_top
    obtain ⟨v, hv, u, hu, huv⟩ := mem_sup.mp hmem
    have : y = u.1 + v.1 := by rw [← coe_add, add_comm, huv]
    rw [this]
    exact add_mem (mem_sup_left ⟨u, hu, rfl⟩) (mem_sup_right hv)
  have : FiniteDimensional k C := Submodule.finiteDimensional_of_le hCS
  set c := Module.finBasis k C
  have hc : span k (Set.range fun x ↦ (c x : V)) = C := by
    rw [show (Set.range fun x ↦ (c x : V)) = C.subtype '' Set.range c by
      rw [← Set.range_comp]; rfl, ← Submodule.map_span, c.span_eq, Submodule.map_top,
      range_subtype]
  refine ⟨ι ⊕ Fin (finrank k C), inferInstance, Sum.elim b (fun x ↦ (c x : V)),
    Sum.elim ℓ (fun _ ↦ a), ?_, ?_, ?_, ?_, ?_⟩
  · rintro (x | x)
    · exact Finset.mem_insert_of_mem (hℓ x)
    · exact Finset.mem_insert_self a T
  · rintro (x | x)
    · exact hb x
    · exact hCS (c x).2
  · refine hli.sum_type (c.linearIndependent.map' C.subtype C.ker_subtype) ?_
    rw [hspan, hc]
    exact hCW.symm
  · rw [Set.Sum.elim_range, span_union, hspan, hc, Finset.sup_insert, ← hCsup, sup_comm]
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · have hfil : (insert e T).filter (e < ·) = T := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hx, hlt⟩
          · exact absurd hlt (lt_irrefl _)
          · exact hx
        · intro hx
          exact ⟨Or.inr hx, ha x hx⟩
      have hcard : (Finset.univ.filter fun x : ι ⊕ Fin (finrank k C) ↦
          Sum.elim ℓ (fun _ ↦ e) x = e).card =
          finrank k C := by
        rw [show (Finset.univ.filter fun x : ι ⊕ Fin (finrank k C) ↦
            Sum.elim ℓ (fun _ ↦ e) x = e) =
            (Finset.univ.map Function.Embedding.inr) by
          ext x
          rcases x with x | x
          · simp only [Finset.mem_filter, Finset.mem_univ, Sum.elim_inl, true_and,
              Finset.mem_map, Function.Embedding.inr_apply, reduceCtorEq, and_false, exists_false,
              iff_false]
            exact fun h ↦ haT (h ▸ hℓ x)
          · simp]
        simp
      rw [hfil, hcard, ← hCsup, ← finrank_sup_add_finrank_inf_eq C W, hCW.eq_bot, finrank_bot,
        add_zero]
    · have hea : ¬ e < a := fun h ↦ lt_asymm h (ha e he)
      have hfil : (insert a T).filter (e < ·) = T.filter (e < ·) := by
        simp only [Finset.filter_insert, hea, ↓reduceIte]
      have hcard : (Finset.univ.filter fun x : ι ⊕ Fin (finrank k C) ↦
          Sum.elim ℓ (fun _ ↦ a) x = e).card =
          (Finset.univ.filter (ℓ · = e)).card := by
        rw [show (Finset.univ.filter fun x : ι ⊕ Fin (finrank k C) ↦
            Sum.elim ℓ (fun _ ↦ a) x = e) =
            (Finset.univ.filter (ℓ · = e)).map Function.Embedding.inl by
          ext x
          rcases x with x | x
          · simp
          · simp only [Finset.mem_filter, Finset.mem_univ, Sum.elim_inr, true_and,
              Finset.mem_map, Function.Embedding.inl_apply, reduceCtorEq, and_false, exists_false,
              iff_false]
            rintro rfl
            exact haT he]
        simp
      rw [hfil, hcard]
      exact hcount e he

end Submodule
