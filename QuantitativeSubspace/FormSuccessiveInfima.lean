/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormHeight

/-!
# Successive infima of a twisted height

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, start of §9, and J.-H. Evertse and H. P. Schlickewei,
*A quantitative version of the Absolute Subspace Theorem*, J. reine angew. Math. **548** (2002),
21–127, Lemma 4.2 and Cor. 7.5.

For a twisted height `H = H_{L,A}` on `Ωⁿ` (`NumberField.FormSystem.absMulHeight`), EF13 puts

```text
T(λ) = span {x ∈ Ωⁿ : H(x) ≤ λ},   λ_i = inf {λ ≥ 0 : dim T(λ) ≥ i},   T_i = ⋂_{λ > λ_i} T(λ).
```

Over an algebraic closure the `λ_i` are infima, not minima. EF13 Lemma 9.1: the `T_i` are
defined over `K`, and at a jump `λ_k < λ_{k+1}` the space `T(λ)` is `T_k`, of dimension `k`, for
every `λ` strictly in between. "Defined over `K`" is ES02 Lemma 4.2, proved here for any
subspace of `Ωⁿ` stable under the `K`-endomorphisms of `Ω`: such a subspace is spanned by its
points in `Kⁿ`. The proof is ES02's, with the trace dual basis of `K(x)` in place of the inverse
of the matrix `(σ_i(ω_j))`.

## Main definitions

* `Submodule.IsDefinedOver K T`: `T ⊆ Ωⁿ` is spanned by points of `Kⁿ`.
* `NumberField.heightSpace`, `NumberField.heightInf`, `NumberField.heightFlag`: `T(λ)`, `λ_i`, `T_i`
  for any height function on `Ωⁿ`.
* `NumberField.FormSystem.infSpace`, `NumberField.FormSystem.successiveInf`,
  `NumberField.FormSystem.infFlag`: the same for the twisted height `H_{L,A}`.

## Main results

* `Submodule.mem_span_algebraMap_of_forall_algHom`, `Submodule.isDefinedOver_of_forall_algHom`:
  ES02 Lemma 4.2, for `Ω` algebraically closed and algebraic over `K`.
* `NumberField.FormSystem.infSpace_isDefinedOver`, `NumberField.FormSystem.infFlag_isDefinedOver`:
  EF13 Lemma 9.1 (i), from the Galois invariance of the height.
* `NumberField.finrank_heightSpace_of_lt`, `NumberField.heightSpace_eq_heightFlag`,
  `NumberField.finrank_heightFlag`: EF13 Lemma 9.1 (ii), ES02 Cor. 7.5.
* `NumberField.heightInf_le_of_linearIndependent`,
  `NumberField.exists_linearIndependent_of_heightInf_lt`: `λ_i` through independent points, as for
  RT96's minima.
* `NumberField.heightInf_le_mul`: `h₁ ≤ c h₂` gives `λ_i(h₁) ≤ c λ_i(h₂)`.

This is milestone Q2.4b of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Module Submodule

namespace Submodule

section Descent

variable (K : Type*) {Ω ι : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- **A subspace of `Ωⁿ` defined over `K`**: it is spanned by points of `Kⁿ`. -/
def IsDefinedOver (T : Submodule Ω (ι → Ω)) : Prop :=
  ∃ s : Set (ι → K), span Ω ((fun y ↦ algebraMap K Ω ∘ y) '' s) = T

variable {K}

/-- The span of a set stable under a `K`-endomorphism `σ` of `Ω` is stable under `σ`. -/
theorem algHom_comp_mem_span {M : Set (ι → Ω)} (σ : Ω →ₐ[K] Ω)
    (hM : ∀ x ∈ M, (σ : Ω → Ω) ∘ x ∈ M) {x : ι → Ω} (hx : x ∈ span Ω M) :
    (σ : Ω → Ω) ∘ x ∈ span Ω M := by
  induction hx using Submodule.span_induction with
  | mem x h => exact subset_span (hM x h)
  | zero =>
    have : (σ : Ω → Ω) ∘ (0 : ι → Ω) = 0 := funext fun _ ↦ map_zero σ
    rw [this]
    exact zero_mem _
  | add x y _ _ hx hy =>
    have : (σ : Ω → Ω) ∘ (x + y) = (σ : Ω → Ω) ∘ x + (σ : Ω → Ω) ∘ y :=
      funext fun _ ↦ map_add σ _ _
    rw [this]
    exact add_mem hx hy
  | smul c x _ hx =>
    have : (σ : Ω → Ω) ∘ (c • x) = σ c • ((σ : Ω → Ω) ∘ x) := funext fun _ ↦ map_mul σ _ _
    rw [this]
    exact smul_mem _ _ hx

variable [Finite ι] [CharZero K] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]

/-- **ES02 Lemma 4.2.** A point of a subspace `T ⊆ Ωⁿ` stable under all `K`-endomorphisms of `Ω`
is an `Ω`-combination of points of `T ∩ Kⁿ`: with `ω_j`, `ω_j^*` dual bases of `G = K(x)` for the
trace form, `x = Σ_j ω_j^* y_j` with `y_j = Tr_{G/K}(ω_j x) = Σ_σ σ(ω_j) σ(x) ∈ T`. -/
theorem mem_span_algebraMap_of_forall_algHom {T : Submodule Ω (ι → Ω)}
    (hT : ∀ σ : Ω →ₐ[K] Ω, ∀ x ∈ T, (σ : Ω → Ω) ∘ x ∈ T) {x : ι → Ω} (hx : x ∈ T) :
    x ∈ span Ω ((fun y ↦ algebraMap K Ω ∘ y) '' {y : ι → K | algebraMap K Ω ∘ y ∈ T}) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have : IsAlgClosure K Ω := ⟨‹_›, ‹_›⟩
  set G := IntermediateField.adjoin K (Set.range x)
  have : FiniteDimensional K G := IntermediateField.finiteDimensional_adjoin fun y _ ↦
    (Algebra.IsAlgebraic.isAlgebraic (R := K) y).isIntegral
  let g : ι → G := fun i ↦ ⟨x i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  let b := Module.finBasis K G
  let bd := (Algebra.traceForm K G).dualBasis (traceForm_nondegenerate K G) b
  let y : Fin (finrank K G) → ι → K := fun j i ↦ Algebra.trace K G (g i * b j)
  have hy : ∀ j, algebraMap K Ω ∘ y j ∈ T := by
    intro j
    have : algebraMap K Ω ∘ y j =
        ∑ σ : G →ₐ[K] Ω, σ (b j) • ((σ.liftNormal Ω : Ω → Ω) ∘ x) := by
      ext i
      simp only [Function.comp_apply, y, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [trace_eq_sum_embeddings]
      refine Finset.sum_congr rfl fun σ _ ↦ ?_
      have hσ : σ.liftNormal Ω (x i) = σ (g i) := σ.liftNormal_commutes Ω (g i)
      rw [hσ, map_mul, mul_comm]
    rw [this]
    exact sum_mem fun σ _ ↦ smul_mem _ _ (hT _ x hx)
  have hx' : x = ∑ j, ((bd j : G) : Ω) • (algebraMap K Ω ∘ y j) := by
    ext i
    have h := congrArg (fun z : G ↦ (z : Ω)) (bd.sum_repr (g i))
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h
    change ((g i : G) : Ω) = _
    rw [← h]
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, Algebra.smul_def,
      mul_comm]
  rw [hx']
  exact sum_mem fun j _ ↦ smul_mem _ _ (subset_span ⟨y j, hy j, rfl⟩)

/-- **ES02 Lemma 4.2**: a subspace of `Ωⁿ` stable under all `K`-endomorphisms of `Ω` is defined
over `K`. -/
theorem isDefinedOver_of_forall_algHom {T : Submodule Ω (ι → Ω)}
    (hT : ∀ σ : Ω →ₐ[K] Ω, ∀ x ∈ T, (σ : Ω → Ω) ∘ x ∈ T) : T.IsDefinedOver K := by
  refine ⟨{y | algebraMap K Ω ∘ y ∈ T}, le_antisymm ?_ fun x hx ↦
    mem_span_algebraMap_of_forall_algHom hT hx⟩
  rw [span_le]
  rintro _ ⟨y, hy, rfl⟩
  exact hy

end Descent

end Submodule

namespace NumberField

/-! ### Successive infima of any height function -/

section Generic

variable {ι : Type*} (Ω : Type*) [Field Ω] (h : (ι → Ω) → ℝ)

/-- **`T(λ)`** for a height function `h` on `Ωⁿ`: the span of the points of height at most `λ`. -/
noncomputable def heightSpace (lam : ℝ) : Submodule Ω (ι → Ω) :=
  span Ω {x | h x ≤ lam}

/-- **The `i`-th successive infimum** `inf {λ ≥ 0 : dim T(λ) ≥ i}` of a height function. It is junk
`0` for `i > n`. -/
noncomputable def heightInf (i : ℕ) : ℝ :=
  sInf {lam | 0 ≤ lam ∧ i ≤ finrank Ω (heightSpace Ω h lam)}

/-- **`T_i = ⋂_{λ > λ_i} T(λ)`** for a height function. -/
noncomputable def heightFlag (i : ℕ) : Submodule Ω (ι → Ω) :=
  ⨅ (lam : ℝ) (_ : heightInf Ω h i < lam), heightSpace Ω h lam

variable {Ω h}

theorem mem_heightSpace {x : ι → Ω} {lam : ℝ} (hx : h x ≤ lam) : x ∈ heightSpace Ω h lam :=
  subset_span hx

theorem heightSpace_mono {lam mu : ℝ} (hle : lam ≤ mu) :
    heightSpace Ω h lam ≤ heightSpace Ω h mu :=
  span_mono fun _ hx ↦ le_trans hx hle

variable (Ω h) in
/-- For `λ` beyond the heights of the unit vectors, `T(λ) = Ωⁿ`. -/
theorem exists_heightSpace_eq_top [Finite ι] :
    ∃ M, 0 ≤ M ∧ ∀ lam, M ≤ lam → heightSpace Ω h lam = ⊤ := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  refine ⟨∑ i, |h (Pi.single i (1 : Ω))|, Finset.sum_nonneg fun i _ ↦ abs_nonneg _,
    fun lam hlam ↦ ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun Ω ι).span_eq, span_le]
  rintro _ ⟨i, rfl⟩
  refine mem_heightSpace (le_trans ?_ hlam)
  rw [Pi.basisFun_apply]
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i ↦ |h (Pi.single i (1 : Ω))|)
    (fun i _ ↦ abs_nonneg _) (Finset.mem_univ i))

theorem heightInf_nonneg (i : ℕ) : 0 ≤ heightInf Ω h i :=
  Real.sInf_nonneg fun _ hl ↦ hl.1

private theorem bddBelow_heightSet (i : ℕ) :
    BddBelow {lam | 0 ≤ lam ∧ i ≤ finrank Ω (heightSpace Ω h lam)} :=
  ⟨0, fun _ hl ↦ hl.1⟩

private theorem nonempty_heightSet [Fintype ι] {i : ℕ} (hi : i ≤ Fintype.card ι) :
    {lam | 0 ≤ lam ∧ i ≤ finrank Ω (heightSpace Ω h lam)}.Nonempty := by
  obtain ⟨M, hM, hT⟩ := exists_heightSpace_eq_top Ω h
  refine ⟨M, hM, ?_⟩
  rwa [hT M le_rfl, finrank_top, Module.finrank_fintype_fun_eq_card]

/-- `λ_i ≤ λ` as soon as `dim T(λ) ≥ i`. -/
theorem heightInf_le {i : ℕ} {lam : ℝ} (h0 : 0 ≤ lam)
    (hi : i ≤ finrank Ω (heightSpace Ω h lam)) : heightInf Ω h i ≤ lam :=
  csInf_le (bddBelow_heightSet i) ⟨h0, hi⟩

/-- `dim T(λ) ≥ i` for every `λ > λ_i`. -/
theorem le_finrank_heightSpace [Fintype ι] {i : ℕ} (hi : i ≤ Fintype.card ι) {lam : ℝ}
    (hlt : heightInf Ω h i < lam) : i ≤ finrank Ω (heightSpace Ω h lam) := by
  obtain ⟨mu, ⟨_, hmu⟩, hlt'⟩ := exists_lt_of_csInf_lt (nonempty_heightSet hi) hlt
  exact hmu.trans (Submodule.finrank_mono (heightSpace_mono hlt'.le))

/-- `λ_1 ≤ λ_2 ≤ ⋯ ≤ λ_n`. -/
theorem heightInf_mono [Fintype ι] {i j : ℕ} (hij : i ≤ j) (hj : j ≤ Fintype.card ι) :
    heightInf Ω h i ≤ heightInf Ω h j :=
  csInf_le_csInf (bddBelow_heightSet i) (nonempty_heightSet hj)
    fun _ hl ↦ ⟨hl.1, hij.trans hl.2⟩

/-- `λ_i ≤ μ` when there are `i` independent points of height at most `μ ≥ 0`. -/
theorem heightInf_le_of_linearIndependent [Finite ι] {i : ℕ} {x : Fin i → ι → Ω}
    (hx : LinearIndependent Ω x) {mu : ℝ} (h0 : 0 ≤ mu) (hle : ∀ j, h (x j) ≤ mu) :
    heightInf Ω h i ≤ mu := by
  refine heightInf_le h0 ?_
  have hsub : span Ω (Set.range x) ≤ heightSpace Ω h mu :=
    span_le.mpr (by rintro _ ⟨j, rfl⟩; exact mem_heightSpace (hle j))
  calc i = finrank Ω (span Ω (Set.range x)) := by rw [finrank_span_eq_card hx, Fintype.card_fin]
    _ ≤ _ := Submodule.finrank_mono hsub

/-- For `μ > λ_i` there are `i` independent points of height at most `μ`. -/
theorem exists_linearIndependent_of_heightInf_lt [Fintype ι] {i : ℕ} (hi : i ≤ Fintype.card ι)
    {mu : ℝ} (hlt : heightInf Ω h i < mu) :
    ∃ x : Fin i → ι → Ω, LinearIndependent Ω x ∧ ∀ j, h (x j) ≤ mu := by
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent Ω {x : ι → Ω | h x ≤ mu}
  have : Finite b := hli.finite
  have : Fintype b := Fintype.ofFinite b
  have hcard : i ≤ Fintype.card b := by
    have := le_finrank_heightSpace (h := h) hi hlt
    rwa [heightSpace, ← hspan, finrank_span_set_eq_card hli, Set.toFinset_card] at this
  let e : Fin i ↪ b := (Fin.castLEEmb hcard).trans (Fintype.equivFin b).symm.toEmbedding
  exact ⟨(↑) ∘ e, hli.comp e e.injective, fun j ↦ hb (e j).2⟩

/-- **Comparing successive infima**: `h₁ ≤ c h₂` gives `λ_i(h₁) ≤ c λ_i(h₂)`. -/
theorem heightInf_le_mul [Fintype ι] {h₁ h₂ : (ι → Ω) → ℝ} {c : ℝ} (hc : 0 < c)
    (hle : ∀ x, h₁ x ≤ c * h₂ x) {i : ℕ} (hi : i ≤ Fintype.card ι) :
    heightInf Ω h₁ i ≤ c * heightInf Ω h₂ i := by
  rw [← div_le_iff₀' hc]
  refine le_of_forall_gt_imp_ge_of_dense fun mu hmu ↦ ?_
  have hmu0 : 0 ≤ mu := (heightInf_nonneg i).trans hmu.le
  rw [div_le_iff₀' hc]
  refine heightInf_le (mul_nonneg hc.le hmu0) ((le_finrank_heightSpace hi hmu).trans
    (Submodule.finrank_mono (span_mono fun x (hx : h₂ x ≤ mu) ↦ ?_)))
  exact (hle x).trans (mul_le_mul_of_nonneg_left hx hc.le)

/-- **EF13 Lemma 9.1 (ii), dimension**: `dim T(λ) = k` for `λ_k < λ < λ_{k+1}`. -/
theorem finrank_heightSpace_of_lt [Fintype ι] {k : ℕ} (hk : k < Fintype.card ι) {lam : ℝ}
    (h₁ : heightInf Ω h k < lam) (h₂ : lam < heightInf Ω h (k + 1)) :
    finrank Ω (heightSpace Ω h lam) = k := by
  refine le_antisymm ?_ (le_finrank_heightSpace hk.le h₁)
  by_contra! hlt
  exact h₂.not_ge (heightInf_le ((heightInf_nonneg k).trans h₁.le) hlt)

/-- **EF13 Lemma 9.1 (ii), ES02 Cor. 7.5**: `T(λ) = T_k` for `λ_k < λ < λ_{k+1}`. -/
theorem heightSpace_eq_heightFlag [Fintype ι] {k : ℕ} (hk : k < Fintype.card ι) {lam : ℝ}
    (h₁ : heightInf Ω h k < lam) (h₂ : lam < heightInf Ω h (k + 1)) :
    heightSpace Ω h lam = heightFlag Ω h k := by
  refine le_antisymm (le_iInf₂ fun mu hmu ↦ ?_) (iInf₂_le lam h₁)
  rcases le_total lam mu with hle | hle
  · exact heightSpace_mono hle
  · refine (eq_of_le_of_finrank_eq (heightSpace_mono hle) ?_).ge
    rw [finrank_heightSpace_of_lt hk hmu (hle.trans_lt h₂), finrank_heightSpace_of_lt hk h₁ h₂]

/-- **EF13 Lemma 9.1 (ii)**: `dim T_k = k` at a jump `λ_k < λ_{k+1}`. -/
theorem finrank_heightFlag [Fintype ι] {k : ℕ} (hk : k < Fintype.card ι)
    (hlt : heightInf Ω h k < heightInf Ω h (k + 1)) : finrank Ω (heightFlag Ω h k) = k := by
  obtain ⟨lam, h₁, h₂⟩ := exists_between hlt
  rw [← heightSpace_eq_heightFlag hk h₁ h₂, finrank_heightSpace_of_lt hk h₁ h₂]

variable {K : Type*} [Field K] [Algebra K Ω]

/-- For a height invariant under the `K`-endomorphisms of `Ω`, `T(λ)` is stable under them. -/
theorem algHom_comp_mem_heightSpace (hσ : ∀ σ : Ω →ₐ[K] Ω, ∀ x, h ((σ : Ω → Ω) ∘ x) = h x)
    (σ : Ω →ₐ[K] Ω) {lam : ℝ} {x : ι → Ω} (hx : x ∈ heightSpace Ω h lam) :
    (σ : Ω → Ω) ∘ x ∈ heightSpace Ω h lam :=
  algHom_comp_mem_span σ (fun y (hy : h y ≤ lam) ↦
    show h (σ ∘ y) ≤ lam by rwa [hσ]) hx

theorem algHom_comp_mem_heightFlag (hσ : ∀ σ : Ω →ₐ[K] Ω, ∀ x, h ((σ : Ω → Ω) ∘ x) = h x)
    (σ : Ω →ₐ[K] Ω) {i : ℕ} {x : ι → Ω} (hx : x ∈ heightFlag Ω h i) :
    (σ : Ω → Ω) ∘ x ∈ heightFlag Ω h i := by
  simp only [heightFlag, mem_iInf] at hx ⊢
  exact fun lam hl ↦ algHom_comp_mem_heightSpace hσ σ (hx lam hl)

end Generic

namespace FormSystem

variable {K ι : Type*} [Field K] [NumberField K] [Fintype ι] [DecidableEq ι]
  (L : FormSystem K ι) (a : FormWeight K ι)
  (Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

/-- **`T(λ)`** (EF13 §9): the subspace of `Ωⁿ` spanned by the points of height at most `λ`. -/
noncomputable abbrev infSpace (lam : ℝ) : Submodule Ω (ι → Ω) :=
  heightSpace Ω (L.absMulHeight a) lam

/-- **The `i`-th successive infimum** `λ_i = inf {λ ≥ 0 : dim T(λ) ≥ i}` (EF13 §9). It is junk
`0` for `i > n`. -/
noncomputable abbrev successiveInf (i : ℕ) : ℝ :=
  heightInf Ω (L.absMulHeight a) i

/-- **`T_i = ⋂_{λ > λ_i} T(λ)`** (EF13 §9). -/
noncomputable abbrev infFlag (i : ℕ) : Submodule Ω (ι → Ω) :=
  heightFlag Ω (L.absMulHeight a) i

variable {Ω}

/-- `T(λ)` is stable under the `K`-endomorphisms of `Ω`, by the Galois invariance of the
height. -/
theorem algHom_comp_mem_infSpace (σ : Ω →ₐ[K] Ω) {lam : ℝ} {x : ι → Ω}
    (hx : x ∈ L.infSpace a Ω lam) : (σ : Ω → Ω) ∘ x ∈ L.infSpace a Ω lam :=
  algHom_comp_mem_heightSpace (L.absMulHeight_comp_algHom a) σ hx

theorem algHom_comp_mem_infFlag (σ : Ω →ₐ[K] Ω) {i : ℕ} {x : ι → Ω}
    (hx : x ∈ L.infFlag a Ω i) : (σ : Ω → Ω) ∘ x ∈ L.infFlag a Ω i :=
  algHom_comp_mem_heightFlag (L.absMulHeight_comp_algHom a) σ hx

variable [IsAlgClosed Ω]

/-- **`T(λ)` is defined over `K`** (EF13 Lemma 9.1 (i), ES02 Cor. 7.5). -/
theorem infSpace_isDefinedOver (lam : ℝ) : (L.infSpace a Ω lam).IsDefinedOver K :=
  isDefinedOver_of_forall_algHom fun σ _ hx ↦ L.algHom_comp_mem_infSpace a σ hx

/-- **EF13 Lemma 9.1 (i)**: `T_i` is defined over `K`. -/
theorem infFlag_isDefinedOver (i : ℕ) : (L.infFlag a Ω i).IsDefinedOver K :=
  isDefinedOver_of_forall_algHom fun σ _ hx ↦ L.algHom_comp_mem_infFlag a σ hx

end FormSystem

end NumberField
