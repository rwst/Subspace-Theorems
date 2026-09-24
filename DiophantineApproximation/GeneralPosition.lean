/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SubspaceHeightBounds

/-!
# Linear forms in general position, and the `#ι` smallest of them

**Layer 6.5, first half.** A family of linear forms on `Fⁿ⁺¹` is in **general position** when
every subfamily of at most `n + 1` of them is linearly independent (Bombieri–Gubler, Definition
7.2.8). Vojta's refinement of the Subspace Theorem replaces the `n + 1` independent forms at a
place by a family in general position *of any size*, and its proof is one local observation,
which is what this file proves:

> at every point `y ≠ 0`, some `n + 1` of the forms are linearly independent and their local
> factor is at most a constant — depending on the family and not on `y` — times the local factor
> of the whole family.

There are two cases and they pull in opposite directions. If the family has at least `n + 1`
members, keep the `n + 1` *smallest* values: general position makes them a basis, and a basis
bounds the coordinates of `y`, so each discarded value is bounded **below** by a constant
multiple of `‖y‖`; the discarded factors are therefore bounded below, and dropping them costs a
constant. If the family has fewer than `n + 1` members it is linearly independent outright, and
it is *completed* to a basis by coordinate forms; the added factors are bounded **above** by `1`,
so the completion costs nothing at all.

Both cases produce the chosen system as an index map `f : ι → κ ⊕ ι` into the family extended by
the coordinate forms, and that is what makes the choice range over a finite set: the global
argument of `SubspaceGeneralPosition.lean` partitions the solutions according to it.

## Main definitions

* `Module.Dual.IsGeneralPosition`: Bombieri–Gubler's Definition 7.2.8.
* `Module.Dual.IsGeneralPosition.of_linearIndependent`: an independent family is in general
  position.
* `Module.Dual.extendProj`: a family of forms extended by the coordinate forms.

## Main results

* `Finset.exists_powersetCard_forall_le`: a subset of given size whose members are the smallest.
* `Module.Dual.exists_index_extendProj`: Steinitz, in the form the small case needs.
* `Module.Dual.exists_one_le_forall_exists_index_prod_le`: **the local step**.

## Implementation notes

⚠ **The `n + 1` smallest are selected by minimising a sum, not by sorting.** A subset `T` of
given size that minimises `∑_{k ∈ T} t k` has every member at most every non-member: exchanging
one for the other would lower the sum. That is the whole of the ordering argument, and it needs
no linear order on the index type and no sorting API.

⚠ **The lower bound on a discarded value is the inverse of a basis.** The chosen forms are a
basis of the dual, so the coordinates of `y` are bounded by the values of the forms at `y`
(`NumberField.exists_one_le_forall_apply_le`, from Layer 4.4); hence the largest chosen value is
at least `‖y‖` over a constant, and every discarded value is at least that. The constant depends
on the chosen subset, of which there are finitely many.

⚠ **The two cases cannot be merged by extending the family once and for all.** The family
extended by the coordinate forms is *not* in general position — a member of it may already be a
coordinate form — so the `n + 1` smallest of the extended family need not be independent. The
extension is used in the small case only, where Steinitz keeps it a basis.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Definition 7.2.8 and Theorem 7.2.9.

P. Vojta, *Diophantine Approximations and Value Distribution Theory*, Lecture Notes in
Mathematics **1239**, Springer (1987).

This is Layer 6.5 (first half) of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset Module Set

namespace Finset

variable {κ : Type*}

/-- **A subset of given size whose members are the smallest.** Among the subsets of `B` with `n`
elements, one minimising `∑ k ∈ T, t k` has every member at most every non-member: exchanging the
two would lower the sum. This is the ordering step of Vojta's refinement, and it needs neither a
linear order on the index type nor a sorting of the values. -/
theorem exists_powersetCard_forall_le (B : Finset κ) (n : ℕ) (hn : n ≤ B.card) (t : κ → ℝ) :
    ∃ T ∈ B.powersetCard n, ∀ k ∈ B, k ∉ T → ∀ i ∈ T, t i ≤ t k := by
  classical
  obtain ⟨T, hT, hmin⟩ := (B.powersetCard n).exists_min_image (fun T ↦ ∑ k ∈ T, t k)
    (Finset.powersetCard_nonempty.2 hn)
  refine ⟨T, hT, fun k hkB hkT i hiT ↦ ?_⟩
  obtain ⟨hTB, hTc⟩ := Finset.mem_powersetCard.1 hT
  have hkerase : k ∉ T.erase i := fun h ↦ hkT (Finset.mem_of_mem_erase h)
  have hn1 : 1 ≤ n := by
    rw [← hTc]
    exact Finset.card_pos.2 ⟨i, hiT⟩
  have hT' : insert k (T.erase i) ∈ B.powersetCard n := by
    refine Finset.mem_powersetCard.2 ⟨Finset.insert_subset hkB
      ((Finset.erase_subset _ _).trans hTB), ?_⟩
    rw [Finset.card_insert_of_notMem hkerase, Finset.card_erase_of_mem hiT, hTc]
    omega
  have hsum := hmin _ hT'
  rw [Finset.sum_insert hkerase, Finset.sum_erase_eq_sub hiT] at hsum
  linarith

end Finset

namespace Module.Dual

variable {F : Type*} [Field F] {ι κ : Type*}

/-- **General position** (Bombieri–Gubler, Definition 7.2.8): every subfamily of at most `#ι` of
the forms indexed by `B` is linearly independent over `F`. For a family of at most `#ι` members
this says exactly that the family itself is independent. -/
def IsGeneralPosition (F : Type*) [Field F] {ι κ : Type*} (B : Finset κ)
    (M : κ → Dual F (ι → F)) : Prop :=
  ∀ s ⊆ B, s.card ≤ Nat.card ι → LinearIndependent F fun k : s ↦ M k

/-- **A linearly independent family is in general position**, whatever the index finset: every
subfamily of a linearly independent family is again linearly independent. This is how the
Subspace Theorem of Layer 6.3 sits inside Vojta's refinement. -/
theorem IsGeneralPosition.of_linearIndependent (B : Finset κ) {M : κ → Dual F (ι → F)}
    (hM : LinearIndependent F M) : IsGeneralPosition F B M :=
  fun _ _ _ ↦ hM.comp _ Subtype.val_injective

/-- **A family of forms extended by the coordinate forms.** The chosen systems of Layer 6.5 are
index maps `ι → κ ⊕ ι` into this family: the left summand selects a given form, the right one a
coordinate form. -/
def extendProj (M : κ → Dual F (ι → F)) : κ ⊕ ι → Dual F (ι → F) :=
  Sum.elim M fun j ↦ LinearMap.proj j

/-- The extended family is the given one on the left summand. -/
@[simp] theorem extendProj_inl (M : κ → Dual F (ι → F)) (k : κ) :
    extendProj M (Sum.inl k) = M k := rfl

/-- The extended family is the coordinate forms on the right summand. -/
@[simp] theorem extendProj_inr (M : κ → Dual F (ι → F)) (j : ι) :
    extendProj M (Sum.inr j) = LinearMap.proj j := rfl

/-- The coordinate forms span the dual space: a form is the linear combination of them given by
its values at the standard basis. -/
theorem span_range_proj_eq_top [Finite ι] :
    Submodule.span F (Set.range fun j : ι ↦ (LinearMap.proj j : Dual F (ι → F))) = ⊤ := by
  have _i : Fintype ι := Fintype.ofFinite ι
  classical
  refine top_unique fun f _ ↦ ?_
  have hf : f = ∑ k, f (Pi.single k 1) • (LinearMap.proj k : Dual F (ι → F)) := by
    refine LinearMap.ext fun x ↦ ?_
    rw [Module.Dual.apply_eq_sum f x]
    simp [mul_comm]
  rw [hf]
  exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- **Steinitz for the coordinate forms.** A linearly independent family indexed by `B` is
completed to a basis of the dual by coordinate forms, and the completion is read off an index map
`ι → κ ⊕ ι` which hits every member of `B` and no other member of `κ`. -/
theorem exists_index_extendProj [Finite ι] (B : Finset κ)
    (M : κ → Dual F (ι → F)) (hind : LinearIndependent F fun k : B ↦ M k) :
    ∃ f : ι → κ ⊕ ι, (∀ k ∈ B, ∃ i, f i = Sum.inl k) ∧ (∀ i k, f i = Sum.inl k → k ∈ B) ∧
      LinearIndependent F fun i ↦ extendProj M (f i) := by
  have _i : Fintype ι := Fintype.ofFinite ι
  classical
  set s : Set (Dual F (ι → F)) := Set.range fun k : B ↦ M k with hs_def
  set r : Set (Dual F (ι → F)) := Set.range fun j : ι ↦ (LinearMap.proj j : Dual F (ι → F))
    with hr_def
  have hs : LinearIndepOn F id s := hind.linearIndepOn_id
  have hst : s ⊆ s ∪ r := Set.subset_union_left
  have ht : ⊤ ≤ Submodule.span F (s ∪ r) := by
    rw [← span_range_proj_eq_top (F := F) (ι := ι)]
    exact Submodule.span_mono Set.subset_union_right
  set bs : Set (Dual F (ι → F)) := hs.extend hst with hbs_def
  have hsub : s ⊆ bs := hs.subset_extend hst
  have hsupset : bs ⊆ s ∪ r := hs.extend_subset hst
  set b : Module.Basis bs F (Dual F (ι → F)) := Module.Basis.extendLe hs hst ht with hb_def
  have hbcoe : ⇑b = ((↑) : bs → Dual F (ι → F)) := Module.Basis.coe_extendLe hs hst ht
  have e : (bs : Type _) ≃ ι := b.indexEquiv (Pi.basisFun F ι).dualBasis
  have hpick : ∀ z : bs, ∃ p : κ ⊕ ι, extendProj M p = (z : Dual F (ι → F)) ∧
      (∀ k, p = Sum.inl k → k ∈ B) ∧ ((z : Dual F (ι → F)) ∈ s → ∃ k, p = Sum.inl k) := by
    intro z
    by_cases hzs : (z : Dual F (ι → F)) ∈ s
    · obtain ⟨k, hk⟩ := hzs
      exact ⟨Sum.inl k.1, hk, fun k' hk' ↦ by
        rw [Sum.inl.injEq] at hk'; exact hk' ▸ k.2, fun _ ↦ ⟨k.1, rfl⟩⟩
    · rcases hsupset z.2 with h | h
      · exact absurd h hzs
      · obtain ⟨j, hj⟩ := h
        exact ⟨Sum.inr j, hj, fun k' hk' ↦ by simp at hk', fun h' ↦ absurd h' hzs⟩
  choose φ hφ1 hφ2 hφ3 using hpick
  refine ⟨fun i ↦ φ (e.symm i), ?_, fun i k hik ↦ hφ2 _ k hik, ?_⟩
  · intro k hk
    have hks : M k ∈ s := ⟨⟨k, hk⟩, rfl⟩
    set z : bs := ⟨M k, hsub hks⟩ with hz_def
    obtain ⟨k', hk'⟩ := hφ3 z (by rw [hz_def]; exact hks)
    have hMk : M k' = M k := by
      have := hφ1 z
      rw [hk'] at this
      simpa [hz_def] using this
    have hk'B : k' ∈ B := hφ2 z k' hk'
    have : (⟨k', hk'B⟩ : B) = ⟨k, hk⟩ := hind.injective hMk
    refine ⟨e z, ?_⟩
    simp only [Equiv.symm_apply_apply]
    rw [hk']
    exact congrArg Sum.inl (congrArg Subtype.val this)
  · have hval : (fun i ↦ extendProj M (φ (e.symm i)))
        = (fun z : bs ↦ (z : Dual F (ι → F))) ∘ e.symm := by
      funext i
      exact hφ1 _
    rw [hval]
    exact (hbcoe ▸ b.linearIndependent).comp _ e.symm.injective

/-- **Completing a family by coordinate forms costs nothing.** If an injective index map hits
every member of `B` and nothing outside it, its product is at most the product over `B` whenever
the factors are nonnegative and those of the coordinate forms are at most `1`. -/
theorem prod_comp_le_prod_inl [Fintype ι] (B : Finset κ) {f : ι → κ ⊕ ι}
    (hinj : Function.Injective f) (h1 : ∀ k ∈ B, ∃ i, f i = Sum.inl k)
    (h2 : ∀ i k, f i = Sum.inl k → k ∈ B) (t : κ ⊕ ι → ℝ) (hnn : ∀ p, 0 ≤ t p)
    (hle : ∀ j, t (Sum.inr j) ≤ 1) :
    ∏ i, t (f i) ≤ ∏ k ∈ B, t (Sum.inl k) := by
  classical
  have hEq : ∏ i, t (f i) = ∏ p ∈ (Finset.univ : Finset ι).image f, t p :=
    (Finset.prod_image fun a _ b _ h ↦ hinj h).symm
  have hsub : B.image Sum.inl ⊆ (Finset.univ : Finset ι).image f := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨i, hi⟩ := h1 k hk
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ i, hi⟩
  have hrest : ∏ p ∈ ((Finset.univ : Finset ι).image f) \ (B.image Sum.inl), t p ≤ 1 := by
    refine Finset.prod_le_one₀ (fun p _ ↦ hnn p) fun p hp ↦ ?_
    obtain ⟨hp1, hp2⟩ := Finset.mem_sdiff.1 hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp1
    rcases hd : f i with k | j
    · exact absurd (Finset.mem_image.2 ⟨k, h2 i k hd, rfl⟩) (hd ▸ hp2)
    · exact hle j
  have hfin : ∏ k ∈ B, t (Sum.inl k) = ∏ p ∈ B.image Sum.inl, t p :=
    (Finset.prod_image fun a _ b _ h ↦ Sum.inl_injective h).symm
  have h0 : 0 ≤ ∏ p ∈ B.image Sum.inl, t p := Finset.prod_nonneg fun p _ ↦ hnn p
  rw [hEq, hfin, ← Finset.prod_sdiff hsub]
  have := mul_le_mul_of_nonneg_right hrest h0
  rwa [one_mul] at this

/-- **The local step of Vojta's refinement** (Bombieri–Gubler, inside the proof of Theorem
7.2.9). For a family of forms in general position there is a constant `C` such that at every
point `y ≠ 0` some `#ι` of the forms — read off an index map into the family extended by the
coordinate forms — are linearly independent and have local factor at most `C` times the local
factor of the whole family.

The constant does not depend on `y`, and the index map ranges over a finite type; that is what
lets the global argument split the solutions into finitely many classes. -/
theorem exists_one_le_forall_exists_index_prod_le [Fintype ι] [Nonempty ι]
    (W : AbsoluteValue F ℝ) (B : Finset κ) (M : κ → Dual F (ι → F))
    (hgp : IsGeneralPosition F B M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ y : ι → F, y ≠ 0 → ∃ f : ι → κ ⊕ ι,
      LinearIndependent F (fun i ↦ extendProj M (f i)) ∧
      (∏ i, W (extendProj M (f i) y) / ⨆ j, W (y j))
        ≤ C * ∏ k ∈ B, W (M k y) / ⨆ j, W (y j) := by
  classical
  by_cases hcard : Fintype.card ι ≤ B.card
  · have hex : ∀ T : Finset κ, ∃ c : ℝ, 1 ≤ c ∧ (T ⊆ B → T.card = Fintype.card ι →
        ∀ (z : ι → F) (a : ℝ), 0 ≤ a → (∀ k ∈ T, W (M k z) ≤ a) → ∀ j, W (z j) ≤ c * a) := by
      intro T
      by_cases hT : T ⊆ B ∧ T.card = Fintype.card ι
      · obtain ⟨hTB, hTc⟩ := hT
        have hcardT : Fintype.card ι = Fintype.card T := by rw [Fintype.card_coe, hTc]
        set eT := Fintype.equivOfCardEq hcardT with heT
        have hli : LinearIndependent F fun i : ι ↦ M (eT i : κ) :=
          (hgp T hTB (by rw [Nat.card_eq_fintype_card]; exact hTc.le)).comp _ eT.injective
        obtain ⟨c, hc1, hc⟩ := NumberField.exists_one_le_forall_apply_le W hli
        exact ⟨c, hc1, fun _ _ z a ha hle j ↦ hc z a ha (fun i ↦ hle _ (eT i).2) j⟩
      · exact ⟨1, le_refl 1, fun h1 h2 ↦ absurd ⟨h1, h2⟩ hT⟩
    choose BT hBT1 hBT using hex
    obtain ⟨C, hC1, hC⟩ := Finset.exists_one_le_forall_le (B.powersetCard (Fintype.card ι))
      fun T ↦ BT T ^ B.card
    refine ⟨C, hC1, fun y hy ↦ ?_⟩
    set d : ℝ := ⨆ j, W (y j) with hd_def
    have hdpos : 0 < d := by
      obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hy
      exact lt_of_lt_of_le (W.pos hj₀) (Finite.le_ciSup_of_le j₀ le_rfl)
    obtain ⟨T, hTmem, hTmin⟩ := Finset.exists_powersetCard_forall_le B (Fintype.card ι) hcard
      fun k ↦ W (M k y) / d
    obtain ⟨hTB, hTc⟩ := Finset.mem_powersetCard.1 hTmem
    have hcardT : Fintype.card ι = Fintype.card T := by rw [Fintype.card_coe, hTc]
    set eT := Fintype.equivOfCardEq hcardT with heT
    refine ⟨fun i ↦ Sum.inl (eT i : κ),
      (hgp T hTB (by rw [Nat.card_eq_fintype_card]; exact hTc.le)).comp _ eT.injective, ?_⟩
    have hTne : T.Nonempty := Finset.card_pos.1 (by rw [hTc]; exact Fintype.card_pos)
    obtain ⟨k₀, hk₀T, hk₀⟩ := T.exists_max_image (fun k ↦ W (M k y)) hTne
    have hBTpos : (0 : ℝ) < BT T := lt_of_lt_of_le zero_lt_one (hBT1 T)
    have hdle : d ≤ BT T * W (M k₀ y) :=
      Real.iSup_le (hBT T hTB hTc y (W (M k₀ y)) (W.nonneg _) fun k hk ↦ hk₀ k hk)
        (by positivity)
    have hk₀lb : 1 / BT T ≤ W (M k₀ y) / d := by
      rw [div_le_div_iff₀ hBTpos hdpos, one_mul, mul_comm]
      exact hdle
    have hlow : ∀ k ∈ B \ T, 1 / BT T ≤ W (M k y) / d := by
      intro k hk
      obtain ⟨hkB, hkT⟩ := Finset.mem_sdiff.1 hk
      exact le_trans hk₀lb (hTmin k hkB hkT k₀ hk₀T)
    have hinv1 : 1 / BT T ≤ 1 := by
      rw [div_le_one hBTpos]; exact hBT1 T
    have hprodBT : (1 / BT T) ^ B.card ≤ ∏ k ∈ B \ T, W (M k y) / d := by
      calc (1 / BT T) ^ B.card ≤ (1 / BT T) ^ (B \ T).card :=
            pow_le_pow_of_le_one (by positivity) hinv1 (Finset.card_le_card Finset.sdiff_subset)
        _ = ∏ _k ∈ B \ T, (1 / BT T) := (Finset.prod_const _).symm
        _ ≤ ∏ k ∈ B \ T, W (M k y) / d := Finset.prod_le_prod₀ (fun k _ ↦ by positivity) hlow
    have hlhs : ∏ i, W (extendProj M (Sum.inl (eT i : κ)) y) / d = ∏ k ∈ T, W (M k y) / d := by
      rw [← Finset.prod_coe_sort T fun k ↦ W (M k y) / d]
      exact Fintype.prod_equiv eT _ _ fun i ↦ rfl
    have hTnn : 0 ≤ ∏ k ∈ T, W (M k y) / d := Finset.prod_nonneg fun k _ ↦ by positivity
    have hone : 1 ≤ C * ∏ k ∈ B \ T, W (M k y) / d := by
      have h2 : BT T ^ B.card * (1 / BT T) ^ B.card = 1 := by
        rw [← mul_pow, mul_one_div, div_self hBTpos.ne', one_pow]
      calc (1 : ℝ) = BT T ^ B.card * (1 / BT T) ^ B.card := h2.symm
        _ ≤ C * ∏ k ∈ B \ T, W (M k y) / d :=
            mul_le_mul (hC T hTmem) hprodBT (by positivity) (by linarith)
    rw [hlhs, ← Finset.prod_sdiff hTB]
    calc ∏ k ∈ T, W (M k y) / d = 1 * ∏ k ∈ T, W (M k y) / d := (one_mul _).symm
      _ ≤ (C * ∏ k ∈ B \ T, W (M k y) / d) * ∏ k ∈ T, W (M k y) / d :=
          mul_le_mul_of_nonneg_right hone hTnn
      _ = C * ((∏ k ∈ B \ T, W (M k y) / d) * ∏ k ∈ T, W (M k y) / d) := by ring
  · have hcard' : B.card < Fintype.card ι := Nat.lt_of_not_le hcard
    obtain ⟨f, hf1, hf2, hf3⟩ := exists_index_extendProj B M
      (hgp B (Finset.Subset.refl B) (by rw [Nat.card_eq_fintype_card]; exact hcard'.le))
    refine ⟨1, le_refl 1, fun y hy ↦ ⟨f, hf3, ?_⟩⟩
    rw [one_mul]
    have hinj : Function.Injective f := fun i i' h ↦ hf3.injective (congrArg (extendProj M) h)
    refine prod_comp_le_prod_inl B hinj hf1 hf2 (fun p ↦ W (extendProj M p y) / ⨆ j, W (y j))
      (fun p ↦ div_nonneg (W.nonneg _) (Real.iSup_nonneg fun j ↦ W.nonneg _)) fun j ↦ ?_
    rw [extendProj_inr, LinearMap.proj_apply]
    exact div_le_one_of_le₀ (Finite.le_ciSup_of_le j le_rfl)
      (Real.iSup_nonneg fun j ↦ W.nonneg _)

end Module.Dual
