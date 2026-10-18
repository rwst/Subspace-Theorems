/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import FaltingsWustholz1994.LinearForms

-- Used only inside proofs.
import STForMathlib.LinearAlgebra.GreedyBasis

/-!
# The see-saw and joint semistability

G. Faltings and G. Wüstholz, *Diophantine approximations on projective spaces*, Invent. Math.
**116** (1994), §4 and Theorem 8.1.

At a place, the forms `ℓ_k` (`k ∈ B`) with exponents `c_k` and the coordinate forms with exponent
`0` filter the space `V` of linear forms over `F`: `F^p V` is spanned by those of exponent `≥ p`,
so `F^p V = V` for `p ≤ 0` (FW's `F^0 = V`). A subspace `X ⊆ V` carries the induced filtration
`F^p X = F^p V ∩ X`, and FW's `dim X · μ(X)` is `∑_p p · dim gr^p X`, the **degree** of `X`. For a
`K`-subspace `U` of points, `U^⊥ ⊆ V` is the kernel of the restriction `V → U_F^*`, whose image
`U^*` carries the quotient filtration.

* **The greedy identification.** The local weight `W_v(U)` of `Weight.lean` (the best basis of
  `U^*` among the restricted forms) is the degree of `U^*` for the quotient filtration
  (`STForMathlib/LinearAlgebra/GreedyBasis.lean`).
* **The see-saw** for `0 → U^⊥ → V → U^* → 0`: `deg V = deg U^⊥ + W_v(U)`.
* **Joint semistability**, FW's: `∑_v μ_v(W) ≤ ∑_v μ_v(V)` for the `K`-rational subspaces
  `0 ≠ W ⊊ V`. These are the `U^⊥` for `0 ≠ U ⊊ K^ι`, so the definition quantifies over `U`.
  With FW's `∑_v μ_v(V) > 1` (normalized as in Finding 5 of the README) it gives
  `W(U) > dim U` for every `U ≠ 0`: `μ_v(U^⊥)` is at most `μ_v(V)` on average and the see-saw
  puts the rest on `U^*`. That is the hypothesis of FW.3, so FW's Theorem 8.1 in FW's own form
  follows.

## Main definitions

* `NumberField.restrictForms`: the restriction of forms to the `K`-points of `U`.
* `NumberField.vanishingForms`: `U^⊥`.
* `NumberField.filtration`, `NumberField.filtrationGt`: `F^p V` and `F^{>p} V`.
* `NumberField.degree`, `NumberField.slope`: FW's `dim X · μ(X)` and `μ(X)`.
* `NumberField.totalSlope`: `∑_{S∞} mult v · μ_v(X) + ∑_{S₀} μ_v(X)`.
* `NumberField.IsJointlySemistable`.

## Main results

* `NumberField.finrank_span_restrictForms`: the restricted forms span a space of dimension
  `dim U`.
* `NumberField.localMaxWeight_eq_sum`: **the greedy identification**.
* `NumberField.degree_top_eq_degree_add_localMaxWeight`: **the see-saw**.
* `NumberField.lt_maxWeight_of_isJointlySemistable`: semistability gives `W(U) > dim U`.
* `NumberField.finite_setOf_isSystemSolution_of_isJointlySemistable`: **FW Theorem 8.1** in FW's
  form.

## Implementation notes

⚠ **The sum runs over the exponents that occur.** FW sum over the jumps `p_j` of the
filtration. The degree sums over all exponents of the family and `0`; where the filtration does
not jump, `gr^p = 0` and the term vanishes. Negative exponents give no jump, as `F^p V = V` for
`p ≤ 0`.

This is milestone FW.2 of `FaltingsWustholz1994/README.md`.
-/

@[expose] public section

open Finset Module Module.Dual Submodule

namespace NumberField

section Local

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {ι κ : Type*} [Fintype ι]

/-- The restriction of forms to the `K`-points of `U`, as `F`-valued functions. -/
noncomputable def restrictForms (U : Submodule K (ι → K)) : Dual F (ι → F) →ₗ[F] (U → F) :=
  LinearMap.pi fun x : U ↦ Dual.eval F (ι → F) fun j ↦ algebraMap K F ((x : ι → K) j)

omit [Fintype ι] in
@[simp] theorem restrictForms_apply (U : Submodule K (ι → K)) (φ : Dual F (ι → F)) (x : U) :
    restrictForms U φ x = φ fun j ↦ algebraMap K F ((x : ι → K) j) :=
  rfl

/-- **`U^⊥`**: the forms vanishing on the `K`-points of `U`. -/
noncomputable def vanishingForms (U : Submodule K (ι → K)) : Submodule F (Dual F (ι → F)) :=
  LinearMap.ker (restrictForms U)

variable (B : Finset κ) (ℓ : κ → Dual F (ι → F)) (c : κ → ℝ)

/-- **`F^p V`**: the span of the forms of exponent `≥ p`, the coordinate forms counted with `0`. -/
noncomputable def filtration (p : ℝ) : Submodule F (Dual F (ι → F)) :=
  span F (extendProj ℓ ''
    (((B.disjSum (univ : Finset ι)).filter (p ≤ extendExp c ·) : Finset (κ ⊕ ι)) : Set (κ ⊕ ι)))

/-- **`F^{>p} V`**: the span of the forms of exponent `> p`. -/
noncomputable def filtrationGt (p : ℝ) : Submodule F (Dual F (ι → F)) :=
  span F (extendProj ℓ ''
    (((B.disjSum (univ : Finset ι)).filter (p < extendExp c ·) : Finset (κ ⊕ ι)) : Set (κ ⊕ ι)))

/-- **FW's `dim X · μ(X)`**: `∑_p p · dim gr^p X` for the induced filtration on `X`. -/
noncomputable def degree (X : Submodule F (Dual F (ι → F))) : ℝ :=
  ∑ p ∈ (B.disjSum (univ : Finset ι)).image (extendExp c), p *
    ((finrank F ↥(filtration B ℓ c p ⊓ X) : ℝ) - finrank F ↥(filtrationGt B ℓ c p ⊓ X))

/-- **FW's slope** `μ(X) = deg X / dim X`. -/
noncomputable def slope (X : Submodule F (Dual F (ι → F))) : ℝ :=
  degree B ℓ c X / finrank F X

/-- `F^p V = V` for `p ≤ 0`: FW's `F^0 = V`. -/
theorem filtration_eq_top {p : ℝ} (hp : p ≤ 0) : filtration B ℓ c p = ⊤ := by
  refine top_unique ((span_range_proj_eq_top (F := F) (ι := ι)).symm.le.trans (span_mono ?_))
  rintro _ ⟨j, rfl⟩
  exact ⟨Sum.inr j, by simp [hp], rfl⟩

/-- The zero subspace has degree `0`. -/
theorem degree_bot : degree B ℓ c ⊥ = 0 := by
  refine sum_eq_zero fun p _ ↦ ?_
  rw [Submodule.finrank_eq_zero.2 (le_bot_iff.1 inf_le_right),
    Submodule.finrank_eq_zero.2 (le_bot_iff.1 inf_le_right)]
  simp

variable (U : Submodule K (ι → K))

omit [Fintype ι] in
/-- The restricted extended family, the vectors of the greedy choice. -/
theorem restrictForms_comp_extendProj :
    (restrictForms U ∘ extendProj ℓ) =
      fun i (x : U) ↦ extendProj ℓ i fun j ↦ algebraMap K F ((x : ι → K) j) :=
  rfl

/-- **The restricted forms span a space of dimension `dim U`.** -/
theorem finrank_span_restrictForms :
    finrank F (span F (restrictForms U ∘ extendProj ℓ ''
      ((B.disjSum (univ : Finset ι) : Finset (κ ⊕ ι)) : Set (κ ⊕ ι)))) = finrank K U := by
  classical
  have hmem : ∀ φ : Dual F (ι → F),
      restrictForms U φ ∈ span F (Set.range fun m (x : U) ↦
        algebraMap K F ((Module.finBasis K U).repr x m)) := by
    intro φ
    set b := Module.finBasis K U
    let ψ : U →ₗ[K] F := (φ.restrictScalars K) ∘ₗ
      ((Algebra.linearMap K F).compLeft ι) ∘ₗ U.subtype
    have hψ : ∀ x, restrictForms U φ x = ψ x := fun x ↦ rfl
    have hsum : restrictForms U φ =
        ∑ m, ψ (b m) • fun x : U ↦ algebraMap K F (b.repr x m) := by
      funext x
      rw [hψ, ← b.sum_repr x, map_sum]
      simp [Finset.sum_apply, Algebra.smul_def, mul_comm]
    rw [hsum]
    exact sum_mem fun m _ ↦ smul_mem _ _ (subset_span ⟨m, rfl⟩)
  refine le_antisymm ?_ ?_
  · have hle : span F (restrictForms U ∘ extendProj ℓ ''
        ((B.disjSum (univ : Finset ι) : Finset (κ ⊕ ι)) : Set (κ ⊕ ι))) ≤
        span F (Set.range fun m (x : U) ↦ algebraMap K F ((Module.finBasis K U).repr x m)) :=
      span_le.2 (by rintro _ ⟨i, -, rfl⟩; exact hmem _)
    have := FiniteDimensional.span_of_finite F (Set.finite_range fun m (x : U) ↦
      algebraMap K F ((Module.finBasis K U).repr x m))
    exact (Submodule.finrank_mono hle).trans ((finrank_range_le_card (R := F) fun m (x : U) ↦
      algebraMap K F ((Module.finBasis K U).repr x m)).trans_eq (by simp))
  · obtain ⟨I, hIS, hIcard, hI⟩ := exists_isWeightBasis B ℓ U
    have := FiniteDimensional.span_of_finite F
      ((B.disjSum (univ : Finset ι)).finite_toSet.image (restrictForms U ∘ extendProj ℓ))
    rw [← hIcard, ← finrank_span_image_eq_card (g := restrictForms U ∘ extendProj ℓ) hI]
    exact Submodule.finrank_mono (span_mono (Set.image_mono (Finset.coe_subset.2 hIS)))

/-- **The greedy identification**: the local weight is the degree of `U^*` for the quotient
filtration, whose pieces are the images of the `F^p V`. -/
theorem localMaxWeight_eq_sum :
    localMaxWeight B ℓ c U = ∑ p ∈ (B.disjSum (univ : Finset ι)).image (extendExp c), p *
      ((finrank F ↥((filtration B ℓ c p).map (restrictForms U)) : ℝ) -
        finrank F ↥((filtrationGt B ℓ c p).map (restrictForms U))) := by
  classical
  obtain ⟨I, hI, hsum⟩ := localMaxWeight_mem B ℓ c U
  replace hsum : ∑ i ∈ I, extendExp c i = localMaxWeight B ℓ c U := hsum
  have hrk := finrank_span_restrictForms B ℓ U
  have hli : LinearIndepOn F (restrictForms U ∘ extendProj ℓ) (I : Set (κ ⊕ ι)) := by
    rw [restrictForms_comp_extendProj]; exact hI.2.2
  have key := sum_eq_sum_finrank_span_of_isMax (g := restrictForms U ∘ extendProj ℓ)
    (e := extendExp c) hI.1 hli (hI.2.1.trans hrk.symm) fun J hJS hJ hJcard ↦ by
      refine (le_localMaxWeight B ℓ c U ⟨hJS, hJcard.trans hrk, ?_⟩).trans_eq hsum.symm
      rw [← restrictForms_comp_extendProj]; exact hJ
  have hmap : ∀ T : Finset (κ ⊕ ι), (span F (extendProj ℓ '' (T : Set (κ ⊕ ι)))).map
      (restrictForms U) = span F (restrictForms U ∘ extendProj ℓ '' (T : Set (κ ⊕ ι))) :=
    fun T ↦ by rw [Submodule.map_span, ← Set.image_comp]
  rw [← hsum, key]
  refine sum_congr rfl fun p _ ↦ ?_
  rw [filtration, filtrationGt, hmap, hmap]

/-- Rank–nullity on a subspace: `dim X = dim f(X) + dim (X ∩ ker f)`. -/
theorem finrank_map_add_finrank_inf_ker {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (f : V →ₗ[F] W) (X : Submodule F V) [FiniteDimensional F X] :
    finrank F (X.map f) + finrank F ↥(X ⊓ LinearMap.ker f) = finrank F X := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict X)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have hc : (LinearMap.ker f).comap X.subtype = (X ⊓ LinearMap.ker f).comap X.subtype := by
    ext; simp
  rwa [hc, (comapSubtypeEquivOfLe inf_le_left).finrank_eq] at h

/-- **The see-saw** for `0 → U^⊥ → V → U^* → 0`: `deg V = deg U^⊥ + W_v(U)`. -/
theorem degree_top_eq_degree_add_localMaxWeight :
    degree B ℓ c ⊤ = degree B ℓ c (vanishingForms U) + localMaxWeight B ℓ c U := by
  rw [localMaxWeight_eq_sum, degree, degree, ← sum_add_distrib]
  refine sum_congr rfl fun p _ ↦ ?_
  have h1 := finrank_map_add_finrank_inf_ker (restrictForms U) (filtration B ℓ c p)
  have h2 := finrank_map_add_finrank_inf_ker (restrictForms U) (filtrationGt B ℓ c p)
  rw [inf_top_eq, inf_top_eq, ← h1, ← h2, vanishingForms]
  push_cast
  ring

end Local

section Global

variable {K F : Type*} [Field K] [NumberField K] [Field F] [Algebra K F] {ι κ : Type*} [Fintype ι]
  (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
  (B : AbsoluteValue K ℝ → Finset κ) (ℓ : AbsoluteValue K ℝ → κ → Dual F (ι → F))
  (c : AbsoluteValue K ℝ → κ → ℝ)

/-- FW's `∑_w μ_w(X)`, normalized as `∑_{S∞} mult v · μ_v(X) + ∑_{S₀} μ_v(X)`. -/
noncomputable def totalSlope (X : Submodule F (Dual F (ι → F))) : ℝ :=
  ∑ v ∈ Sinf, (v.mult : ℝ) * slope (B v.1) (ℓ v.1) (c v.1) X +
    ∑ v ∈ Sfin, slope (B v.1) (ℓ v.1) (c v.1) X

/-- **FW's joint semistability**: `∑_w μ_w(W) ≤ ∑_w μ_w(V)` for the `K`-rational subspaces
`0 ≠ W ⊊ V`, which are the `U^⊥` for `0 ≠ U ⊊ K^ι`. -/
def IsJointlySemistable : Prop :=
  ∀ U : Submodule K (ι → K), U ≠ ⊥ → U ≠ ⊤ →
    totalSlope Sinf Sfin B ℓ c (vanishingForms U) ≤ totalSlope Sinf Sfin B ℓ c ⊤

omit [Algebra K F] in
/-- The weighted degree sum, `totalSlope` times the dimension. -/
theorem totalSlope_mul_finrank (X : Submodule F (Dual F (ι → F))) (hX : finrank F X ≠ 0) :
    totalSlope Sinf Sfin B ℓ c X * finrank F X =
      ∑ v ∈ Sinf, (v.mult : ℝ) * degree (B v.1) (ℓ v.1) (c v.1) X +
        ∑ v ∈ Sfin, degree (B v.1) (ℓ v.1) (c v.1) X := by
  have h' : (finrank F X : ℝ) ≠ 0 := by exact_mod_cast hX
  simp only [totalSlope, slope, add_mul, sum_mul]
  congr 1 <;> refine sum_congr rfl fun v _ ↦ by field_simp

/-- **Joint semistability with `∑_w μ_w(V) > 1` gives `W(U) > dim U`** for every `U ≠ 0`, the
hypothesis of FW.3. -/
theorem lt_maxWeight_of_isJointlySemistable (hss : IsJointlySemistable Sinf Sfin B ℓ c)
    (h1 : 1 < totalSlope Sinf Sfin B ℓ c ⊤) (U : Submodule K (ι → K)) (hU : U ≠ ⊥) :
    (finrank K U : ℝ) < maxWeight Sinf Sfin B ℓ c U := by
  classical
  set D : Submodule F (Dual F (ι → F)) → ℝ := fun X ↦
    ∑ v ∈ Sinf, (v.mult : ℝ) * degree (B v.1) (ℓ v.1) (c v.1) X +
      ∑ v ∈ Sfin, degree (B v.1) (ℓ v.1) (c v.1) X with hD
  set M := totalSlope Sinf Sfin B ℓ c ⊤
  set n := finrank F (Dual F (ι → F))
  set m := finrank F (vanishingForms (F := F) U)
  set d := finrank K U
  have hd : 0 < d := Nat.pos_of_ne_zero fun h ↦ hU (Submodule.finrank_eq_zero.1 h)
  -- `dim U^⊥ ≤ n − d`, from the `d` independent restrictions.
  have hrank : d + m ≤ n := by
    obtain ⟨I, hIS, hIcard, hI⟩ := exists_isWeightBasis (∅ : Finset κ) (0 : κ → Dual F (ι → F)) U
    have h : finrank F (LinearMap.range (restrictForms (F := F) U)) + m = n :=
      LinearMap.finrank_range_add_finrank_ker (restrictForms (F := F) U)
    have hle : span F (restrictForms U ∘ extendProj (0 : κ → Dual F (ι → F)) ''
        (I : Set (κ ⊕ ι))) ≤ LinearMap.range (restrictForms U) :=
      span_le.2 (by rintro _ ⟨i, -, rfl⟩; exact ⟨_, rfl⟩)
    have := Submodule.finrank_mono hle
    rw [finrank_span_image_eq_card (by rw [restrictForms_comp_extendProj]; exact hI),
      hIcard] at this
    omega
  -- The see-saw at every place.
  have hW : maxWeight Sinf Sfin B ℓ c U = D ⊤ - D (vanishingForms U) := by
    simp only [maxWeight, hD]
    have := fun v : AbsoluteValue K ℝ ↦
      degree_top_eq_degree_add_localMaxWeight (B v) (ℓ v) (c v) U
    simp only [this]
    simp only [mul_add, sum_add_distrib]
    ring
  have hDtop : D ⊤ = M * n := by
    have hn : finrank F (⊤ : Submodule F (Dual F (ι → F))) ≠ 0 := by
      rw [finrank_top]; omega
    have := totalSlope_mul_finrank Sinf Sfin B ℓ c ⊤ hn
    rw [finrank_top] at this
    exact this.symm
  have hM0 : 0 ≤ M := by linarith
  have hDperp : D (vanishingForms U) ≤ M * m := by
    by_cases hm : m = 0
    · have : vanishingForms (F := F) U = ⊥ := Submodule.finrank_eq_zero.1 hm
      simp [hD, this, degree_bot, hm]
    · have hUtop : U ≠ ⊤ := by
        rintro rfl
        have : d = n := by
          simp only [d, n, finrank_top, Subspace.dual_finrank_eq,
            Module.finrank_fintype_fun_eq_card]
        omega
      have hs := hss U hU hUtop
      exact (totalSlope_mul_finrank Sinf Sfin B ℓ c (vanishingForms U) hm).symm.trans_le
        (mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _))
  rw [hW, hDtop]
  have hnm : (d : ℝ) ≤ n - m := by
    have : ((d + m : ℕ) : ℝ) ≤ n := by exact_mod_cast hrank
    push_cast at this
    linarith
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith

end Global

section Finiteness

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  {ι κ : Type*} [Fintype ι]

/-- **FW Theorem 8.1** in FW's form: for a jointly semistable system with `∑_w μ_w(V) > 1`, the
solutions are finitely many projective points. -/
theorem finite_setOf_isSystemSolution_of_isJointlySemistable (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (B : AbsoluteValue K ℝ → Finset κ) (ℓ : AbsoluteValue K ℝ → κ → Dual F (ι → F))
    (c : AbsoluteValue K ℝ → κ → ℝ) (hss : IsJointlySemistable Sinf Sfin B ℓ c)
    (h1 : 1 < totalSlope Sinf Sfin B ℓ c ⊤) :
    {Q : Projectivization K (ι → K) |
      ∃ (x : ι → K) (hx : x ≠ 0), Projectivization.mk K x hx = Q ∧
        IsSystemSolution Sinf Sfin w B ℓ c x}.Finite :=
  finite_setOf_isSystemSolution Sinf Sfin w hwI hwF B ℓ c
    (lt_maxWeight_of_isJointlySemistable Sinf Sfin B ℓ c hss h1)

end Finiteness

end NumberField
