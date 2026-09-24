/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.WedgeExponentBound
public import DiophantineApproximation.WedgeRecovery
public import DiophantineApproximation.ExponentGrid
public import DiophantineApproximation.PenultimateMinimum

/-!
# The parametric Subspace Theorem

For a number field `K`, forms `L v i : Module.Dual K (Kⁱ)` linearly independent at every infinite
place and at every place of a finite set `Sfin`, and exponents `c` of **negative weight**, there
are a finite set `T` of proper subspaces of `Kⁱ` and a level `Q₀` such that every approximation
domain `approxDomain Sfin L c Q` with `Q ≥ Q₀` is contained in a member of `T`. This is
Bombieri–Gubler's 7.5.32 — Steps VIII and IX of the proof of the Subspace Theorem — and it is the
statement the quantitative theory strengthens by counting `T`.

The route, for a level `Q` at which the domain has rank `R`:

* `R = 0`. The domain spans `⊥`, which is proper.
* `1 ≤ R < #ι`. Layer 4.3 makes the rank less than `#ι` at every large level. The choice (7.41) of
  Layer 4.5 gives a `k` in `[R, #ι)` at which the jump of the minima is large; Evertse's lemma
  (Layer 4.4), applied to vectors realizing the minima, produces vectors `y` whose wedges of the
  `p`-subsets meeting `y 0, …, y (k - 1)`, `k + p = #ι`, lie in a domain in `⋀^p Kⁱ` whose
  exponents `wedgeExponent` move with `Q` (Layer 4.5). Those exponents stay in a box
  (`WedgeExponentBound.lean`), so rounding them up to a grid of mesh `γ`
  (`ExponentGrid.lean`) leaves finitely many systems of exponents, each still of negative weight;
  the wedge domain is contained in the domain of the rounded system, whose rank is at most
  `M - 1 = #(⋀^p) - 1` at every large level by Layer 4.3 and is therefore **exactly** `M - 1`,
  since the wedges already span a hyperplane. Layer 5.6 in `⋀^p Kⁱ` makes those spans finite in
  number, and Lemma 7.5.33, read as the function `recoverSpan` (`WedgeRecovery.lean`), recovers
  from each the span of `y 0, …, y (k - 1)` — which contains `V(Q)` and is proper because
  `k < #ι`.

## Main results

* `NumberField.exists_finite_forall_approxSpan_le`: the spans of the domains of a fixed rank,
  along one choice of `k`, lie in a finite set of proper subspaces.
* `NumberField.exists_finset_submodule_forall_approxDomain_subset`: **the milestone**.

## Implementation notes

⚠ **The rank `#ι - 1` needs no separate argument.** Bombieri–Gubler treat the penultimate case by
Theorem 7.5.13 directly. Here it is the case `k = #ι - 1`, `p = 1` of the same construction: the
wedge domain in `⋀^1 Kⁱ` is the original domain re-indexed by the one-element subsets, with the
exponents shifted by the minima, and Layer 5.6 applies to it exactly as it does in higher `p`. One
mechanism covers every rank from `1` to `#ι - 1`.

⚠ **No pigeonhole and no subsequence.** The book argues along an unbounded family of levels and
extracts a subfamily on which `k` and the rounded exponents are constant. That is not needed: the
rounding is a *function* of the level, its range is finite, and the finite set of subspaces is the
union over that range. What the book's pigeonhole buys — finitely many classes — is bought here by
the box bound alone.

⚠ **The finite set is not the set of spans.** `T` collects subspaces *containing* the domains, not
the spans `V(Q)` themselves: the wedge route recovers the span of the first `k` minimal vectors,
which contains `V(Q)` and is what Lemma 7.5.33 determines. Whether the `V(Q)` themselves are
finite in number is not claimed and is not needed by Layer 6.2.

⚠ **The order on `ι` is internal.** The milestone is stated without `[LinearOrder ι]`: the wedge
construction needs an order to index the Plücker coordinates, but the statement does not mention
one, so the proof chooses one by transport from `Fin (#ι)`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
7.5.30–7.5.32.

J.-H. Evertse and H. P. Schlickewei, "A quantitative version of the absolute subspace theorem",
*Journal für die reine und angewandte Mathematik* **548** (2002), 21–127, for the parametric
formulation.

This is Layer 6.1 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Filter Finset Module NumberField NumberField.mixedEmbedding exteriorPower

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
  {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}

section Wedge

variable [LinearOrder ι] [Nonempty ι]

open scoped Classical in
/-- **The spans of the domains of a fixed rank, along one choice of `k`, lie in a finite set of
proper subspaces** (Bombieri–Gubler, 7.5.32, Steps VIII and IX). -/
theorem exists_finite_forall_approxSpan_le
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {c : AbsoluteValue K ℝ → ι → ℝ}
    (hc : approxWeight Sfin c < 0) {k p : ℕ} (hkp : k + p = Fintype.card ι) (hk : 0 < k)
    (hp : 0 < p) :
    ∃ 𝒮 : Set (Submodule K (ι → K)), 𝒮.Finite ∧ ∀ᶠ Q in atTop,
      ∀ R : ℕ, finrank K (approxSpan Sfin L c Q) = R → 1 ≤ R → R ≤ k →
        (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) (k - 1) /
            successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) k) ^
              (Fintype.card ι - R)
          ≤ (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)
              (Fintype.card ι - 1))⁻¹ →
        ∃ Z ∈ 𝒮, Z ≠ ⊤ ∧ approxSpan Sfin L c Q ≤ Z := by
  set N := Fintype.card ι with hN
  set d := finrank ℚ K with hd
  set W := approxWeight Sfin c with hW
  set M := Fintype.card (Set.powersetCard ι p) with hM
  have hNpos : 0 < N := Fintype.card_pos
  have hkN : k < N := by omega
  have hpN : p ≤ N := by omega
  have hd0 : 0 < d := finrank_pos
  -- the wedge forms and the reference exponents
  set L' : AbsoluteValue K ℝ → Set.powersetCard ι p → Dual K (Set.powersetCard ι p → K) :=
    fun v ↦ wedgeForms (L v) p with hL'
  have hL'Inf : ∀ w : InfinitePlace K, LinearIndependent K (L' w.1) :=
    fun w ↦ linearIndependent_wedgeForms (hLInf w) p
  have hL'Fin : ∀ v ∈ Sfin, LinearIndependent K (L' v.1) :=
    fun v hv ↦ linearIndependent_wedgeForms (hLFin v hv) p
  set cT : AbsoluteValue K ℝ → Set.powersetCard ι p → ℝ :=
    fun v T ↦ ∑ t ∈ (T : Finset ι), c v t with hcT
  -- the constants
  obtain ⟨C, hC, hplucker⟩ := exists_plucker_mem_approxDomain_wedgeForms K ι
  obtain ⟨B, hB, Q₁, hQ₁, hminima⟩ := exists_pos_forall_rpow_le_successiveMinimum_le hLInf hLFin c
  obtain ⟨Q₂, hQ₂1, hwt⟩ :=
    exists_forall_approxWeight_wedgeExponent_le hLInf hLFin hc hC hkp hp
  have hM2 : 2 ≤ M := by
    have h1 : Nontrivial (Set.powersetCard ι p) := by
      rw [← not_subsingleton_iff_nontrivial, Set.powersetCard.subsingleton_iff]
      push Not
      exact ⟨by omega, by rw [Nat.card_eq_fintype_card]; omega⟩
    exact Fintype.one_lt_card
  have hMpos : 0 < M := by omega
  set δ : ℝ := -(W / (2 * (N : ℝ) ^ 2)) with hδ
  have hN0' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hδ0 : 0 < δ := by
    rw [hδ, neg_pos]
    exact div_neg_of_neg_of_pos hc (by positivity)
  have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
  have hM0' : (0 : ℝ) < M := by exact_mod_cast hMpos
  set γ : ℝ := δ / (2 * ((d : ℝ) * (M : ℝ))) with hγ
  have hγ0 : 0 < γ := by
    rw [hγ]
    exact div_pos hδ0 (mul_pos two_pos (mul_pos hd0' hM0'))
  set G : ℝ := 1 + B * N + 2 * B with hG
  set m : ℤ := ⌈G / γ⌉ with hm
  -- the finite pool of grids
  set pool : Set (InfinitePlace K → Set.powersetCard ι p → ℤ) :=
    {g | (∀ w T, |g w T| ≤ m) ∧ approxWeight Sfin (gridExponent cT γ g) ≤ -δ / 2} with hpool
  have hpoolfin : pool.Finite :=
    Set.Finite.subset (finite_setOf_abs_le (Set.powersetCard ι p) m) fun g hg ↦ hg.1
  -- the candidate subspaces
  set 𝒮 : Set (Submodule K (ι → K)) := ⋃ g ∈ pool, recoverSpan p ''
    {V : Submodule K (Set.powersetCard ι p → K) | ∃ Q : ℝ, 1 ≤ Q ∧
      finrank K (approxSpan Sfin L' (gridExponent cT γ g) Q) = M - 1 ∧
      V = approxSpan Sfin L' (gridExponent cT γ g) Q} with h𝒮
  have hne : Nonempty (Set.powersetCard ι p) := Fintype.card_pos_iff.1 hMpos
  let _ : LinearOrder (Set.powersetCard ι p) :=
    LinearOrder.lift' (Fintype.equivFin _) (Equiv.injective _)
  have h𝒮fin : 𝒮.Finite := by
    refine Set.Finite.biUnion hpoolfin fun g hg ↦ Set.Finite.image _ ?_
    exact finite_setOf_approxSpan (n := M - 1) (by omega) (by omega) hL'Inf hL'Fin hδ0 hg.2
  refine ⟨𝒮, h𝒮fin, ?_⟩
  have hrankev : ∀ᶠ Q in atTop, ∀ g ∈ hpoolfin.toFinset,
      finrank K (approxSpan Sfin L' (gridExponent cT γ g) Q) < M := by
    rw [eventually_all_finset]
    intro g hg
    rw [Set.Finite.mem_toFinset] at hg
    exact eventually_finrank_approxSpan_lt hL'Inf hL'Fin (lt_of_le_of_lt hg.2 (by linarith))
  filter_upwards [hrankev, eventually_ge_atTop Q₁, eventually_ge_atTop Q₂,
    eventually_gt_atTop (1 : ℝ), eventually_ge_atTop C, eventually_ge_atTop C⁻¹] with
    Q hrank' hQQ₁ hQQ₂ hQ1 hQC hQC'
  intro R hrank hR1 hRk hjump
  have hQ0 : (0 : ℝ) < Q := lt_trans one_pos hQ1
  have hna : ∀ v : FinitePlace K, IsNonarchimedean v.1 := fun v a b ↦ v.add_le a b
  have hDt : DiscreteTopology (approxLattice Sfin L c Q) :=
    discreteTopology_approxLattice hLFin c hQ0.ne'
  have : DiscreteTopology (approxModule Sfin L c Q).mixedImage := hDt
  have hZl : IsZLattice ℝ (approxLattice Sfin L c Q) := isZLattice_approxLattice hLFin c hQ0.ne'
  have : IsZLattice ℝ (approxModule Sfin L c Q).mixedImage := hZl
  have hB₂ : (interior (approxBody L c Q)).Nonempty :=
    ⟨0, mem_interior_iff_mem_nhds.2 (approxBody_mem_nhds_zero L c hQ0)⟩
  set μ := successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) with hμ
  have hμpos : ∀ j, j < N → 0 < μ j := fun j hj ↦
    successiveMinimum_pos _ (convex_approxBody L c Q) (fun z hz ↦ neg_mem_approxBody hz) hB₂
      (isBounded_approxBody hLInf c Q) hj
  have hmono : MonotoneOn μ (Set.Iio N) := fun i _ j hj hij ↦
    successiveMinimum_le_of_le _ (convex_approxBody L c Q) (fun z hz ↦ neg_mem_approxBody hz)
      hB₂ (isBounded_approxBody hLInf c Q) hij (Set.mem_Iio.1 hj)
  obtain ⟨x, hxind, hx⟩ := exists_linearIndependent_mem_smul_successiveMinimum
    (approxModule Sfin L c Q) (convex_approxBody L c Q) (fun z hz ↦ neg_mem_approxBody hz) hB₂
    (isBounded_approxBody hLInf c Q) (isClosed_approxBody L c Q)
  obtain ⟨ξ, hξ, π, hmem⟩ := hplucker Sfin L hLInf hLFin c Q hQ1 x hxind μ hmono hμpos hx
  set y : Fin N → ι → K := fun j ↦ x j + ∑ l ∈ Finset.Iio j, ξ j l • x l with hy
  have hyind : LinearIndependent K y := linearIndependent_add_sum_smul hxind ξ
  set cw := wedgeExponent c π μ C Q k p with hcw
  set g := roundExponent cT cw γ with hg
  set c' := gridExponent cT γ g with hc'
  -- the exponents of the wedge domain stay in the box, and are exact at the finite places
  have hCQ1 : (1 : ℝ) ≤ C * Q := by
    have h := mul_le_mul_of_nonneg_left hQC' hC.le
    rwa [mul_inv_cancel₀ hC.ne'] at h
  have hbox : ∀ (w : InfinitePlace K) (T : Set.powersetCard ι p), |cw w.1 T - cT w.1 T| ≤ G :=
    fun w T ↦ abs_wedgeExponent_sub_sum_le hQ1 hQC hCQ1 hB.le hkN hpN
      (fun j hj ↦ (hminima Q hQQ₁ j hj).1) (fun j hj ↦ (hminima Q hQQ₁ j hj).2) w.1 T
  have hfinex : ∀ v ∈ Sfin, ∀ T : Set.powersetCard ι p, cw v.1 T = cT v.1 T := by
    intro v _ T
    rw [hcw, wedgeExponent]
    simp only [hna v, ↓reduceIte, add_zero]
    rfl
  have hgridfin : ∀ v ∈ Sfin, ∀ T : Set.powersetCard ι p, c' v.1 T = cT v.1 T := by
    intro v _ T
    exact gridExponent_of_forall_ne cT g
      (fun w hcc ↦ InfinitePlace.not_isNonarchimedean w (by rw [hcc]; exact hna v)) T
  -- the rounded exponents are one of the finitely many grids
  have hgpool : g ∈ pool := by
    refine ⟨fun w T ↦ abs_roundExponent_le hγ0 hbox w T, ?_⟩
    have h1 : approxWeight Sfin c' ≤ approxWeight Sfin cw + γ * ((d : ℝ) * (M : ℝ)) :=
      approxWeight_le_of_le (fun w T ↦ gridExponent_roundExponent_le hγ0 w T)
        (fun v hv T ↦ le_of_eq ((hgridfin v hv T).trans (hfinex v hv T).symm))
    have h2 : approxWeight Sfin cw ≤ -δ := by
      have h := hwt Q hQQ₂ R hR1 hRk hjump π
      rwa [hδ, neg_neg]
    have h3 : γ * ((d : ℝ) * (M : ℝ)) = δ / 2 := by
      rw [hγ]
      field_simp
    linarith
  -- the wedges of Evertse's vectors lie in the grid domain
  have hsub : approxDomain Sfin L' cw Q ⊆ approxDomain Sfin L' c' Q :=
    approxDomain_subset_of_le hQ1.le (fun w T ↦ le_gridExponent_roundExponent hγ0 w T)
      (fun v hv T ↦ le_of_eq ((hfinex v hv T).trans (hgridfin v hv T).symm))
  have hwedgele : wedgeSpan k p y ≤ approxSpan Sfin L' c' Q := by
    rw [wedgeSpan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨J, hJ, rfl⟩
    exact Submodule.subset_span (hsub (hmem k p J hJ))
  have hrk : finrank K (wedgeSpan k p y) + 1 = M := finrank_wedgeSpan_add_one hyind hkp
  have hlt : finrank K (approxSpan Sfin L' c' Q) < M := hrank' g (hpoolfin.mem_toFinset.2 hgpool)
  have heq : wedgeSpan k p y = approxSpan Sfin L' c' Q :=
    Submodule.eq_of_le_of_finrank_le hwedgele (by omega)
  have hrankM : finrank K (approxSpan Sfin L' c' Q) = M - 1 := by rw [← heq]; omega
  have hZ : recoverSpan p (approxSpan Sfin L' c' Q)
      = Submodule.span K (x '' {j | (j : ℕ) < k}) := by
    rw [← heq, recoverSpan_wedgeSpan hyind hkp, hy, Submodule.span_image_add_sum_smul_eq]
  refine ⟨recoverSpan p (approxSpan Sfin L' c' Q), ?_, ?_, ?_⟩
  · exact Set.mem_biUnion hgpool ⟨_, ⟨Q, hQ1.le, hrankM, rfl⟩, rfl⟩
  · rw [hZ]
    exact Submodule.span_image_setOf_lt_ne_top x hkN
  · rw [hZ, approxSpan_eq_span_image hLInf hLFin c hQ0 hxind hx]
    refine Submodule.span_mono (Set.image_mono fun j hj ↦ ?_)
    have hjR : (j : ℕ) < finrank K (approxSpan Sfin L c Q) :=
      (successiveMinimum_approx_le_one_iff hLInf hLFin c hQ0 j.2).1 hj
    rw [hrank] at hjR
    exact lt_of_lt_of_le hjR hRk

end Wedge

open scoped Classical in
/-- **Layer 6.1, the parametric Subspace Theorem** (Bombieri–Gubler 7.5.30–7.5.32, Steps VIII and
IX; Evertse–Schlickewei for the formulation). For forms with coefficients in `K`, linearly
independent at every infinite place and at every place of `Sfin`, and exponents of negative
weight, there are a finite set `T` of proper subspaces of `Kⁱ` and a level `Q₀` such that every
approximation domain of level at least `Q₀` is contained in a member of `T`. -/
theorem exists_finset_submodule_forall_approxDomain_subset [Nontrivial ι]
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {c : AbsoluteValue K ℝ → ι → ℝ}
    (hc : approxWeight Sfin c < 0) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∃ Q₀ : ℝ, ∀ Q ≥ Q₀, ∃ W ∈ T, approxDomain Sfin L c Q ⊆ W := by
  have hne : Nonempty ι := ⟨Classical.arbitrary ι⟩
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Equiv.injective _)
  set N := Fintype.card ι with hN
  have hN2 : 2 ≤ N := Fintype.one_lt_card
  -- for every `k` in `[1, #ι)` a finite family, by the theorem above
  have hfam : ∀ k : ℕ, ∃ 𝒮 : Set (Submodule K (ι → K)), 𝒮.Finite ∧ (0 < k → k < N →
      ∀ᶠ Q in atTop, ∀ R : ℕ, finrank K (approxSpan Sfin L c Q) = R → 1 ≤ R → R ≤ k →
        (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) (k - 1) /
            successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) k) ^ (N - R)
          ≤ (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) (N - 1))⁻¹ →
        ∃ Z ∈ 𝒮, Z ≠ ⊤ ∧ approxSpan Sfin L c Q ≤ Z) := by
    intro k
    by_cases hk : 0 < k ∧ k < N
    · obtain ⟨𝒮, hfin, hev⟩ := exists_finite_forall_approxSpan_le hLInf hLFin hc
        (k := k) (p := N - k) (by omega) hk.1 (by omega)
      exact ⟨𝒮, hfin, fun _ _ ↦ hev⟩
    · exact ⟨∅, Set.finite_empty, fun h1 h2 ↦ absurd ⟨h1, h2⟩ hk⟩
  choose 𝒮 h𝒮fin h𝒮ev using hfam
  set 𝒯 : Set (Submodule K (ι → K)) := insert ⊥ (⋃ k ∈ Finset.range N, 𝒮 k) with h𝒯
  have h𝒯fin : 𝒯.Finite :=
    Set.Finite.insert _ (Set.Finite.biUnion (Finset.range N).finite_toSet fun k _ ↦ h𝒮fin k)
  refine ⟨h𝒯fin.toFinset.filter (· ≠ ⊤), fun W hW ↦ (Finset.mem_filter.1 hW).2, ?_⟩
  rw [← Filter.eventually_atTop]
  have hall : ∀ᶠ Q in atTop, ∀ k ∈ Finset.range N, 0 < k → k < N →
      ∀ R : ℕ, finrank K (approxSpan Sfin L c Q) = R → 1 ≤ R → R ≤ k →
        (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) (k - 1) /
            successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) k) ^ (N - R)
          ≤ (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) (N - 1))⁻¹ →
        ∃ Z ∈ 𝒮 k, Z ≠ ⊤ ∧ approxSpan Sfin L c Q ≤ Z := by
    rw [eventually_all_finset]
    intro k _
    by_cases hk : 0 < k ∧ k < N
    · filter_upwards [h𝒮ev k hk.1 hk.2] with Q hQ _ _
      exact hQ
    · filter_upwards with Q h1 h2
      exact absurd ⟨h1, h2⟩ hk
  filter_upwards [hall, eventually_finrank_approxSpan_lt hLInf hLFin hc,
    eventually_gt_atTop (1 : ℝ)] with Q hk hrank hQ1
  have hQ0 : (0 : ℝ) < Q := lt_trans one_pos hQ1
  have hDt : DiscreteTopology (approxLattice Sfin L c Q) :=
    discreteTopology_approxLattice hLFin c hQ0.ne'
  have : DiscreteTopology (approxModule Sfin L c Q).mixedImage := hDt
  have hZl : IsZLattice ℝ (approxLattice Sfin L c Q) := isZLattice_approxLattice hLFin c hQ0.ne'
  have : IsZLattice ℝ (approxModule Sfin L c Q).mixedImage := hZl
  have hB₂ : (interior (approxBody L c Q)).Nonempty :=
    ⟨0, mem_interior_iff_mem_nhds.2 (approxBody_mem_nhds_zero L c hQ0)⟩
  set μ := successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) with hμ
  have hμpos : ∀ j, j < N → 0 < μ j := fun j hj ↦
    successiveMinimum_pos _ (convex_approxBody L c Q) (fun z hz ↦ neg_mem_approxBody hz) hB₂
      (isBounded_approxBody hLInf c Q) hj
  rcases Nat.eq_zero_or_pos (finrank K (approxSpan Sfin L c Q)) with hR0 | hR1
  · refine ⟨⊥, ?_, ?_⟩
    · rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨Set.mem_insert _ _, bot_ne_top⟩
    · have hbot : approxSpan Sfin L c Q = ⊥ := Submodule.finrank_eq_zero.1 hR0
      intro z hz
      have hmem : z ∈ approxSpan Sfin L c Q := Submodule.subset_span hz
      rw [hbot] at hmem
      exact hmem
  · obtain ⟨k, hkR, hkN, hjump⟩ := exists_div_pow_le_inv (μ := μ)
      (R := finrank K (approxSpan Sfin L c Q)) (N := N) hR1 hrank hμpos
      ((successiveMinimum_approx_le_one_iff hLInf hLFin c hQ0 (by omega)).2 (by omega))
    obtain ⟨Z, hZ𝒮, hZtop, hZle⟩ := hk k (Finset.mem_range.2 hkN) (by omega) hkN _ rfl hR1 hkR
      hjump
    refine ⟨Z, ?_, ?_⟩
    · rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨Set.mem_insert_of_mem _ (Set.mem_biUnion (Finset.mem_coe.2
        (Finset.mem_range.2 hkN)) hZ𝒮), hZtop⟩
    · exact Submodule.span_le.1 hZle

end NumberField
