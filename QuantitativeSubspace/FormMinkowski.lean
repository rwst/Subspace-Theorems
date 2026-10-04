/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormSuccessiveInfima
public import QuantitativeSubspace.TwistedSuccessiveMinimaFinite

-- Used only inside proofs.
import ArithmeticHeights.Extension
import DiophantineApproximation.FinitePlaceValues

/-!
# Absolute Minkowski for twisted heights from systems of forms

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, Prop. 9.2, which is J.-H. Evertse and H. P. Schlickewei,
*A quantitative version of the Absolute Subspace Theorem*, J. reine angew. Math. **548** (2002),
21–127, Prop. 7.1 and Cor. 7.2: for a system `L` of forms in `n` variables over `K` and weights
`A_iv`, the successive infima of `H_{L,A}` on `Ωⁿ` (`Ω` algebraically closed) satisfy

```text
n^{-n/2} Δ_L / ∏_v ∏_i A_iv ≤ λ₁ ⋯ λₙ ≤ 2^{n(n-1)/2} Δ_L / ∏_v ∏_i A_iv,
```

and for EF13's weights `Q ^ c_iv` the product of the weights is `Q ^ α`, `α = Σ_v Σ_i c_iv`.

## Proof

ES02's. When every finite weight is a value `A_iv = ‖α_iv‖_v` (ES02 (7.4)), the system is a
`NumberField.Twist` (`FormSystem.toTwist`): `diag(1/A_iv) L^{(v)}` through each complex embedding,
`diag(1/α_iv) L^{(v)}` at the finitely many finite places where something is not integral or a
weight is not `1`, and the identity elsewhere. Its height is between `H_{L,A}` and
`n^{1/2} H_{L,A}` (max norm against ℓ² norm, ES02 (7.8)), its determinant is `Δ_L / ∏ A_iv`, and
RT96 Thm 6.3 (`Twist.absDet_le_prod_absMinimum`, `Twist.prod_absMinimum_le`, milestone Q2.2e)
gives Prop. 7.1. For real weights (Cor. 7.2), fix `β_v` with `|β_v|_v > 1` at the finitely many
places where `a ≠ 1`, round `log A_iv / log |β_v|_v` to `k_iv / N`, and pass to `E = K(β_v^{1/N})`
with the weights `|β_v^{k_iv / N}|`: by `FormSystem.baseChange`, the monotonicity of the height in
the weights and EF13 Lemma 7.2, heights and weight products change by at most
`(1 + ε) ^ {s / [K:ℚ]}`. Then `ε → 0`.

## Main definitions

* `NumberField.FormWeight.absProd`: `∏_v ∏_i A_iv`.
* `NumberField.FormSystem.baseChange`, `NumberField.FormWeight.baseChange`: the system and weights
  over an extension, with the same height (`absMulHeight_baseChange`) and `Δ_L`
  (`absDet_baseChange`).
* `NumberField.FormWeight.scale`: weights rescaled place by place at the finite places.
* `NumberField.FormSystem.toTwist`: the twist of a system with weights `‖α_iv‖_v`.

## Main results

* `NumberField.FormSystem.prod_successiveInf_le`, `NumberField.FormSystem.le_prod_successiveInf`:
  ES02 Cor. 7.2.
* `NumberField.FormSystem.prod_successiveInf_weight_le`,
  `NumberField.FormSystem.le_prod_successiveInf_weight`: EF13 Prop. 9.2.
* `NumberField.FormSystem.prod_successiveInf_le_of_eq_apply`,
  `NumberField.FormSystem.le_prod_successiveInf_of_eq_apply`: ES02 Prop. 7.1.
* `NumberField.FormSystem.exists_eq_apply_weight`: the approximation of ES02 (7.11)–(7.17).
* `NumberField.FormWeight.absProd_weight`: `∏_v ∏_i Q ^ c_iv = Q ^ α`.

This is milestone Q2.4c of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Finset Function Module Matrix IsDedekindDomain

namespace NumberField

/-- A finite product of nonnegative reals is monotone in the factors. -/
private theorem finprod_le_finprod_of_nonneg {α : Type*} {f g : α → ℝ}
    (hf : f.HasFiniteMulSupport) (hg : g.HasFiniteMulSupport) (h0 : ∀ v, 0 ≤ f v)
    (hle : ∀ v, f v ≤ g v) : ∏ᶠ v, f v ≤ ∏ᶠ v, g v := by
  classical
  have hS := Set.Finite.union hf hg
  rw [finprod_eq_prod_of_mulSupport_subset f (s := hS.toFinset)
      (by rw [Set.Finite.coe_toFinset]; exact Set.subset_union_left),
    finprod_eq_prod_of_mulSupport_subset g (s := hS.toFinset)
      (by rw [Set.Finite.coe_toFinset]; exact Set.subset_union_right)]
  exact Finset.prod_le_prod₀ (fun v _ ↦ h0 v) fun v _ ↦ hle v

variable {K ι : Type*} [Field K] [NumberField K] [Fintype ι]

/-! ### The product of the weights -/

namespace FormWeight

variable (a : FormWeight K ι)

theorem hasFiniteMulSupport_prod_fin : (fun v ↦ ∏ i, a.fin v i).HasFiniteMulSupport :=
  a.finite_setOf_fin_ne_one.subset fun v hv h ↦ hv <| by
    change ∏ i, a.fin v i = 1
    rw [h]
    simp

/-- The product of all weights, relative to `K`: `∏_v ∏_i a_iv` in the relative
normalization. -/
noncomputable def mulProd : ℝ :=
  (∏ v : InfinitePlace K, (∏ i, a.arch v i) ^ v.mult) * ∏ᶠ v : FinitePlace K, ∏ i, a.fin v i

/-- **The product of all weights**, `∏_v ∏_i A_iv`; for EF13's weights `Q ^ c_iv` it is
`Q ^ {Σ_v Σ_i c_iv}` (`FormExponent.absProd_weight`). -/
noncomputable def absProd : ℝ :=
  a.mulProd ^ ((finrank ℚ K : ℝ))⁻¹

theorem mulProd_pos : 0 < a.mulProd := by
  refine mul_pos (Finset.prod_pos fun v _ ↦ pow_pos (Finset.prod_pos fun i _ ↦
    a.arch_pos v i) _) ?_
  rw [finprod_eq_prod _ a.hasFiniteMulSupport_prod_fin]
  exact Finset.prod_pos fun v _ ↦ Finset.prod_pos fun i _ ↦ a.fin_pos v i

theorem absProd_pos : 0 < a.absProd :=
  Real.rpow_pos_of_pos a.mulProd_pos _

/-- The product of the weights is monotone in the weights. -/
theorem mulProd_le_of_le {b : FormWeight K ι} (harch : ∀ v i, a.arch v i ≤ b.arch v i)
    (hfin : ∀ v i, a.fin v i ≤ b.fin v i) : a.mulProd ≤ b.mulProd := by
  refine mul_le_mul (Finset.prod_le_prod₀ (fun v _ ↦ pow_nonneg (Finset.prod_nonneg fun i _ ↦
    (a.arch_pos v i).le) _) fun v _ ↦ pow_le_pow_left₀ (Finset.prod_nonneg fun i _ ↦
    (a.arch_pos v i).le) (Finset.prod_le_prod₀ (fun i _ ↦ (a.arch_pos v i).le)
    fun i _ ↦ harch v i) _) (finprod_le_finprod_of_nonneg a.hasFiniteMulSupport_prod_fin
    b.hasFiniteMulSupport_prod_fin (fun v ↦ Finset.prod_nonneg fun i _ ↦ (a.fin_pos v i).le)
    fun v ↦ Finset.prod_le_prod₀ (fun i _ ↦ (a.fin_pos v i).le) fun i _ ↦ hfin v i) ?_ ?_
  · rw [finprod_eq_prod _ a.hasFiniteMulSupport_prod_fin]
    exact Finset.prod_nonneg fun v _ ↦ Finset.prod_nonneg fun i _ ↦ (a.fin_pos v i).le
  · exact Finset.prod_nonneg fun v _ ↦ pow_nonneg (Finset.prod_nonneg fun i _ ↦
      (b.arch_pos v i).le) _

theorem absProd_le_of_le {b : FormWeight K ι} (harch : ∀ v i, a.arch v i ≤ b.arch v i)
    (hfin : ∀ v i, a.fin v i ≤ b.fin v i) : a.absProd ≤ b.absProd :=
  Real.rpow_le_rpow a.mulProd_pos.le (a.mulProd_le_of_le harch hfin) (by positivity)

/-- **Rescaling the finite weights place by place** multiplies the product of the weights by the
`n`-th power of the product of the factors. -/
theorem mulProd_of_scale {b : FormWeight K ι} {r : FinitePlace K → ℝ}
    (hrf : r.HasFiniteMulSupport) (harch : ∀ v i, b.arch v i = a.arch v i)
    (hfin : ∀ v i, b.fin v i = a.fin v i * r v) :
    b.mulProd = a.mulProd * (∏ᶠ v, r v) ^ Fintype.card ι := by
  classical
  have hS := Set.Finite.union a.hasFiniteMulSupport_prod_fin hrf
  have hb : (fun v ↦ ∏ i, b.fin v i).mulSupport ⊆ hS.toFinset := fun v hv ↦ by
    rw [Set.Finite.coe_toFinset]
    by_contra hcon
    simp only [Set.mem_union, mem_mulSupport, not_or, not_not] at hcon
    exact hv (by simp_rw [hfin, Finset.prod_mul_distrib, hcon.2, hcon.1]; simp)
  rw [mulProd, mulProd, finprod_eq_prod_of_mulSupport_subset _ hb,
    finprod_eq_prod_of_mulSupport_subset _ (s := hS.toFinset)
      (by rw [Set.Finite.coe_toFinset]; exact Set.subset_union_left),
    finprod_eq_prod_of_mulSupport_subset _ (s := hS.toFinset)
      (by rw [Set.Finite.coe_toFinset]; exact Set.subset_union_right)]
  simp_rw [harch, hfin, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Finset.prod_pow]
  ring

end FormWeight

namespace FormExponent

variable (c : FormExponent K ι)

/-- EF13's `α = Σ_v Σ_i c_iv` (Prop. 9.2). -/
noncomputable def sum : ℝ :=
  ∑ v, ∑ i, c.arch v i + ∑ᶠ v, ∑ i, c.fin v i

/-- **The product of EF13's weights**: `∏_v ∏_i Q ^ c_iv = Q ^ α`. -/
theorem absProd_weight {Q : ℝ} (hQ : 0 < Q) : (c.weight hQ).absProd = Q ^ c.sum := by
  have hdK : (finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  have hsupp : (fun v ↦ ∑ i, c.fin v i).support ⊆ c.finite_setOf_fin_ne_zero.toFinset := by
    intro v hv
    rw [Set.Finite.coe_toFinset]
    exact fun h ↦ hv (by simp [h])
  have hv : ∀ v : InfinitePlace K, (∏ i, (c.weight hQ).arch v i) ^ v.mult =
      Q ^ ((∑ i, c.arch v i) * finrank ℚ K) := fun v ↦ by
    have hm : (v.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr v.mult_ne_zero
    simp only [weight]
    rw [← Real.rpow_sum_of_pos hQ, ← Real.rpow_mul_natCast hQ.le, ← Finset.sum_div,
      ← Finset.sum_mul, div_mul_cancel₀ _ hm]
  have hA : ∏ v : InfinitePlace K, (∏ i, (c.weight hQ).arch v i) ^ v.mult =
      Q ^ ((∑ v, ∑ i, c.arch v i) * finrank ℚ K) := by
    rw [Finset.prod_congr rfl fun v _ ↦ hv v, ← Real.rpow_sum_of_pos hQ, Finset.sum_mul]
  have hB : ∏ᶠ v : FinitePlace K, ∏ i, (c.weight hQ).fin v i =
      Q ^ ((∑ᶠ v, ∑ i, c.fin v i) * finrank ℚ K) := by
    simp only [weight]
    simp_rw [← Real.rpow_sum_of_pos hQ, ← Finset.sum_mul]
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := c.finite_setOf_fin_ne_zero.toFinset)
        (fun v hv ↦ hsupp fun h ↦ hv (by simp [h])),
      finsum_eq_sum_of_support_subset _ hsupp, ← Real.rpow_sum_of_pos hQ, Finset.sum_mul]
  rw [FormWeight.absProd, FormWeight.mulProd, hA, hB, ← Real.rpow_add hQ, ← Real.rpow_mul hQ.le,
    ← add_mul, mul_inv_cancel_right₀ hdK]
  rfl

end FormExponent

/-! ### Base change to an extension -/

section BaseChange

variable (E : Type*) [Field E] [NumberField E] [Algebra K E]

omit [Fintype ι] in
theorem _root_.Matrix.det_map_algebraMap [Fintype ι] [DecidableEq ι] {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (M : Matrix ι ι R) :
    (M.map (algebraMap R S)).det = algebraMap R S M.det :=
  (RingHom.map_det _ _).symm

/-- **The system of forms over an extension** `E`: at a place of `E`, the forms at the place of
`K` below it. -/
noncomputable def FormSystem.baseChange [DecidableEq ι] (L : FormSystem K ι) : FormSystem E ι where
  arch w := (L.arch (w.comap (algebraMap K E))).map (algebraMap K E)
  arch_det_ne_zero w := by
    rw [det_map_algebraMap]
    exact (map_ne_zero _).mpr (L.arch_det_ne_zero _)
  fin w := (L.fin (w.under K)).map (algebraMap K E)
  fin_det_ne_zero w := by
    rw [det_map_algebraMap]
    exact (map_ne_zero _).mpr (L.fin_det_ne_zero _)
  finite_range_fin := (L.finite_range_fin.image fun M ↦ M.map (algebraMap K E)).subset <| by
    rintro _ ⟨w, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, rfl⟩

/-- **The weights over an extension** `E`: `a_iv` at an infinite place of `E` above `v`, and
`a_iv ^ (local degree)` at a finite one, so that the height does not change
(`FormSystem.absMulHeight_baseChange`). -/
noncomputable def FormWeight.baseChange (a : FormWeight K ι) : FormWeight E ι where
  arch w i := a.arch (w.comap (algebraMap K E)) i
  arch_pos _ _ := a.arch_pos _ _
  fin w i := a.fin (w.under K) i ^ w.localDegree K
  fin_pos _ _ := pow_pos (a.fin_pos _ _) _
  finite_setOf_fin_ne_one := by
    refine (a.finite_setOf_fin_ne_one.biUnion fun v _ ↦ FinitePlace.finite_placesOver E v).subset
      fun w hw ↦ Set.mem_biUnion (x := w.under K) (fun h ↦ hw ?_)
        (FinitePlace.mem_placesOver.mpr (FinitePlace.liesOver_under (K := K) w))
    funext i
    simp [h]

namespace FormSystem

variable [DecidableEq ι] {E} (L : FormSystem K ι) (a : FormWeight K ι)
variable {F : Type*} [Field F] [NumberField F] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

/-- **Base change does not change the relative height.** -/
theorem mulHeight_baseChange (x : ι → F) :
    (L.baseChange E).mulHeight (a.baseChange E) x = L.mulHeight a x := by
  rw [mulHeight, mulHeight]
  congr 1
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    have hc : (w.comap (algebraMap E F)).comap (algebraMap K E) = w.comap (algebraMap K F) := by
      rw [← InfinitePlace.comap_comp, ← IsScalarTower.algebraMap_eq]
    simp only [archFactor, baseChange, FormWeight.baseChange, hc, Matrix.map_map,
      ← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
  · refine finprod_congr fun w ↦ ?_
    simp only [finFactor, baseChange, FormWeight.baseChange, FinitePlace.under_under,
      Matrix.map_map, ← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, ← pow_mul,
      Nat.mul_comm _ (w.localDegree E), ← FinitePlace.localDegree_tower]

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra E Ω] [IsScalarTower K E Ω]
  [Algebra.IsAlgebraic K Ω] [Algebra.IsAlgebraic E Ω]

/-- **Base change does not change the absolute height.** -/
theorem absMulHeight_baseChange (x : ι → Ω) :
    (L.baseChange E).absMulHeight (a.baseChange E) x = L.absMulHeight a x := by
  have := Twist.numberField_adjoin_range (K := E) x
  set G := IntermediateField.adjoin E (Set.range x)
  have : IsScalarTower K G Ω := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  let y : ι → G := fun i ↦ ⟨x i, IntermediateField.subset_adjoin E _ ⟨i, rfl⟩⟩
  have h := L.absMulHeight_algHom a (IsScalarTower.toAlgHom K G Ω) y
  rw [show (⇑(IsScalarTower.toAlgHom K G Ω) ∘ y) = x from rfl] at h
  rw [h, absMulHeight, mulHeight_baseChange]

/-- Base change raises the relative determinant to the `[E : K]`-th power. -/
theorem mulDet_baseChange : (L.baseChange E).mulDet = L.mulDet ^ finrank K E := by
  rw [mulDet, mulDet, mul_pow]
  congr 1
  · refine prod_infinitePlace_pow_mult_eq _ _ fun φ ↦ ?_
    simp only [baseChange, InfinitePlace.comap_mk, det_map_algebraMap]
    rfl
  · simp only [baseChange, det_map_algebraMap]
    rw [finprod_congr fun w : FinitePlace E ↦ FinitePlace.apply_algebraMap w (w.under K) _]
    exact FinitePlace.finprod_under_pow_localDegree _ L.hasFiniteMulSupport_det_fin

/-- **Base change does not change `Δ_L`.** -/
theorem absDet_baseChange : (L.baseChange E).absDet = L.absDet := by
  rw [absDet, absDet, mulDet_baseChange, rpow_finrank_inv L.mulDet_pos]

end FormSystem

namespace FormWeight

variable {E} (a : FormWeight K ι)

theorem mulProd_baseChange : (a.baseChange E).mulProd = a.mulProd ^ finrank K E := by
  rw [mulProd, mulProd, mul_pow]
  congr 1
  · refine prod_infinitePlace_pow_mult_eq _ _ fun φ ↦ ?_
    simp only [baseChange, InfinitePlace.comap_mk]
  · simp only [baseChange, Finset.prod_pow]
    exact FinitePlace.finprod_under_pow_localDegree _ a.hasFiniteMulSupport_prod_fin

theorem absProd_baseChange : (a.baseChange E).absProd = a.absProd := by
  rw [absProd, absProd, mulProd_baseChange, FormSystem.rpow_finrank_inv a.mulProd_pos]

end FormWeight

end BaseChange

/-! ### Monotonicity in the weights -/

namespace FormSystem

variable [DecidableEq ι] (L : FormSystem K ι) {a b : FormWeight K ι}
variable {E : Type*} [Field E] [NumberField E] [Algebra K E]

/-- **Larger weights give a smaller height.** -/
theorem mulHeight_le_of_le (harch : ∀ v i, a.arch v i ≤ b.arch v i)
    (hfin : ∀ v i, a.fin v i ≤ b.fin v i) (x : ι → E) : L.mulHeight b x ≤ L.mulHeight a x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have harch' : ∀ w, L.archFactor b w x ≤ L.archFactor a w x := fun w ↦
    ciSup_mono (Finite.bddAbove_range _) fun i ↦
      div_le_div_of_nonneg_left (apply_nonneg _ _) (a.arch_pos _ i) (harch _ i)
  have hfin' : ∀ w, L.finFactor b w x ≤ L.finFactor a w x := fun w ↦
    ciSup_mono (Finite.bddAbove_range _) fun i ↦
      div_le_div_of_nonneg_left (apply_nonneg _ _) (pow_pos (a.fin_pos _ i) _)
        (pow_le_pow_left₀ (a.fin_pos _ i).le (hfin _ i) _)
  refine mul_le_mul (Finset.prod_le_prod₀ (fun w _ ↦ pow_nonneg (L.archFactor_nonneg b w x) _)
    fun w _ ↦ pow_le_pow_left₀ (L.archFactor_nonneg b w x) (harch' w) _)
    (finprod_le_finprod_of_nonneg (L.hasFiniteMulSupport_finFactor b hx)
      (L.hasFiniteMulSupport_finFactor a hx) (fun w ↦ L.finFactor_nonneg b w x) hfin') ?_ ?_
  · rw [finprod_eq_prod _ (L.hasFiniteMulSupport_finFactor b hx)]
    exact Finset.prod_nonneg fun w _ ↦ L.finFactor_nonneg b w x
  · exact Finset.prod_nonneg fun w _ ↦ pow_nonneg (L.archFactor_nonneg a w x) _

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

theorem absMulHeight_le_of_le (harch : ∀ v i, a.arch v i ≤ b.arch v i)
    (hfin : ∀ v i, a.fin v i ≤ b.fin v i) (x : ι → Ω) :
    L.absMulHeight b x ≤ L.absMulHeight a x := by
  have := Twist.numberField_adjoin_range (K := K) x
  exact Real.rpow_le_rpow (L.mulHeight_nonneg b _) (L.mulHeight_le_of_le harch hfin _)
    (by positivity)

end FormSystem

/-! ### The max norm against the ℓ² norm -/

theorem iSup_norm_le_norm_toLp {κ : Type*} [Fintype κ] (u : κ → ℂ) :
    ⨆ i, ‖u i‖ ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℂ κ)‖ := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp
  exact ciSup_le fun i ↦ PiLp.norm_apply_le (WithLp.toLp 2 u : EuclideanSpace ℂ κ) i

theorem norm_toLp_le_sqrt_card_mul_iSup {κ : Type*} [Fintype κ] (u : κ → ℂ) :
    ‖(WithLp.toLp 2 u : EuclideanSpace ℂ κ)‖ ≤ √(Fintype.card κ) * ⨆ i, ‖u i‖ := by
  have hM : 0 ≤ ⨆ i, ‖u i‖ := Real.iSup_nonneg fun _ ↦ norm_nonneg _
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq hM, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖(WithLp.toLp 2 u : EuclideanSpace ℂ κ) i‖ ^ 2 ≤ ∑ _i : κ, (⨆ i, ‖u i‖) ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _)
          (Finite.le_ciSup_of_le (f := fun i ↦ ‖u i‖) i le_rfl) 2
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ### Rational weights: a twist (ES02 Prop. 7.1) -/

omit [Fintype ι] in
theorem FormWeight.ne_zero_of_eq_apply {a : FormWeight K ι} {α : FinitePlace K → ι → K}
    (hα : ∀ v i, a.fin v i = v (α v i)) (v : FinitePlace K) (i : ι) : α v i ≠ 0 := fun h ↦
  (a.fin_pos v i).ne' (by rw [hα, h, map_zero])

namespace FormSystem

variable [DecidableEq ι] (L : FormSystem K ι) (a : FormWeight K ι)

/-- The finite places where the weights are not `1` or some form at that place is not integral
with integral inverse. Off them, the factor of the height is the plain max norm. -/
def badPlaces : Set (FinitePlace K) :=
  {v | a.fin v ≠ 1} ∪ {v | ∃ i j, 1 < v (L.fin v i j) ∨ 1 < v ((L.fin v)⁻¹ i j)}

private theorem finite_setOf_one_lt (z : K) : {v : FinitePlace K | 1 < v z}.Finite := by
  rcases eq_or_ne z 0 with rfl | hz
  · exact Set.finite_empty.subset fun v (hv : 1 < v 0) ↦ by rw [map_zero] at hv; linarith
  · exact (FinitePlace.hasFiniteMulSupport hz).subset fun v hv ↦ ne_of_gt hv

theorem finite_badPlaces : (L.badPlaces a).Finite := by
  refine a.finite_setOf_fin_ne_one.union ?_
  have : Finite (Set.range L.fin) := L.finite_range_fin
  refine (Set.finite_iUnion fun M : Set.range L.fin ↦ Set.finite_iUnion fun i ↦
    Set.finite_iUnion fun j ↦ (finite_setOf_one_lt (M.1 i j)).union
      (finite_setOf_one_lt (M.1⁻¹ i j))).subset fun v ⟨i, j, hv⟩ ↦ ?_
  exact Set.mem_iUnion.mpr ⟨⟨_, v, rfl⟩, Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hv⟩⟩⟩

variable {α : FinitePlace K → ι → K} (hα : ∀ v i, a.fin v i = v (α v i))
include hα

open scoped Classical in
/-- **The twist of a system with weights `a_iv = v(α_iv)`** (ES02 (7.4)): `diag(1/a_iv) L^{(v)}`
read through each complex embedding, `diag(1/α_iv) L^{(v)}` at the finitely many bad finite
places, and the identity elsewhere. -/
noncomputable def toTwist : Twist K ι where
  arch φ := diagonal (fun i ↦ (((a.arch (InfinitePlace.mk φ) i)⁻¹ : ℝ) : ℂ)) *
    (L.arch (InfinitePlace.mk φ)).map φ
  arch_det_ne_zero φ := by
    rw [det_mul, det_diagonal, show (L.arch (InfinitePlace.mk φ)).map φ =
      φ.mapMatrix (L.arch (InfinitePlace.mk φ)) from rfl, ← RingHom.map_det]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_)
      ((map_ne_zero _).mpr (L.arch_det_ne_zero _))
    exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (a.arch_pos _ i).ne')
  arch_conjugate φ := by
    rw [InfinitePlace.mk_conjugate_eq]
    ext i j
    simp [diagonal_mul, ComplexEmbedding.conjugate_coe_eq]
  fin v := if v ∈ L.badPlaces a then diagonal (fun i ↦ (α v i)⁻¹) * L.fin v else 1
  fin_det_ne_zero v := by
    split_ifs
    · rw [det_mul, det_diagonal]
      exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ ↦
        inv_ne_zero (FormWeight.ne_zero_of_eq_apply hα v i)) (L.fin_det_ne_zero v)
    · simp
  finite_setOf_fin_ne_one := (L.finite_badPlaces a).subset fun v hv ↦ by
    by_contra h
    exact hv (by simp [h])

end FormSystem

namespace FormSystem

variable [DecidableEq ι] (L : FormSystem K ι) (a : FormWeight K ι)
  {α : FinitePlace K → ι → K} (hα : ∀ v i, a.fin v i = v (α v i))
include hα

theorem toTwist_arch (φ : K →+* ℂ) : (L.toTwist a hα).arch φ =
    diagonal (fun i ↦ (((a.arch (InfinitePlace.mk φ) i)⁻¹ : ℝ) : ℂ)) *
      (L.arch (InfinitePlace.mk φ)).map φ :=
  rfl

theorem toTwist_fin_of_mem {v : FinitePlace K} (hv : v ∈ L.badPlaces a) :
    (L.toTwist a hα).fin v = diagonal (fun i ↦ (α v i)⁻¹) * L.fin v := by
  simp [toTwist, hv]

theorem toTwist_fin_of_notMem {v : FinitePlace K} (hv : v ∉ L.badPlaces a) :
    (L.toTwist a hα).fin v = 1 := by
  simp [toTwist, hv]

omit hα in
theorem fin_eq_one_of_notMem {v : FinitePlace K} (hv : v ∉ L.badPlaces a) : a.fin v = 1 := by
  by_contra h
  exact hv (Or.inl h)

omit hα in
theorem apply_le_one_of_notMem {v : FinitePlace K} (hv : v ∉ L.badPlaces a) (i j : ι) :
    v (L.fin v i j) ≤ 1 ∧ v ((L.fin v)⁻¹ i j) ≤ 1 := by
  by_contra h
  rw [not_and_or, not_le, not_le] at h
  exact hv (Or.inr ⟨i, j, h⟩)

variable {F : Type*} [Field F] [NumberField F] [Algebra K F]

/-- At a finite place the twist and the system have the same factor. -/
theorem finFactor_toTwist (w : FinitePlace F) (x : ι → F) :
    (L.toTwist a hα).finFactor w x = L.finFactor a w x := by
  rw [Twist.finFactor, finFactor]
  by_cases hv : w.under K ∈ L.badPlaces a
  · rw [L.toTwist_fin_of_mem a hα hv]
    refine iSup_congr fun i ↦ ?_
    rw [Matrix.map_mul, diagonal_map (map_zero _), ← mulVec_mulVec, mulVec_diagonal, map_mul,
      map_inv₀, map_inv₀, FinitePlace.apply_algebraMap w (w.under K), ← hα, inv_mul_eq_div]
  · rw [L.toTwist_fin_of_notMem a hα hv, Matrix.map_one _ (map_zero _) (map_one _), one_mulVec]
    simp only [L.fin_eq_one_of_notMem a hv, Pi.one_apply, one_pow, div_one]
    have hw : IsNonarchimedean w.1 := fun a b ↦ FinitePlace.add_le w a b
    have hint : ∀ z : K, (w.under K) z ≤ 1 → w.1 (algebraMap K F z) ≤ 1 := fun z hz ↦ by
      change w (algebraMap K F z) ≤ 1
      rw [FinitePlace.apply_algebraMap w (w.under K)]
      exact pow_le_one₀ (apply_nonneg _ _) hz
    refine (Matrix.iSup_mulVec_eq_of_mul_eq_one hw
      (V := (L.fin (w.under K)).map (algebraMap K F))
      (W := ((L.fin (w.under K))⁻¹).map (algebraMap K F)) ?_
      (fun i j ↦ hint _ (L.apply_le_one_of_notMem a hv i j).1)
      (fun i j ↦ hint _ (L.apply_le_one_of_notMem a hv i j).2) x).symm
    rw [← Matrix.map_mul, nonsing_inv_mul _ (Ne.isUnit (L.fin_det_ne_zero _)),
      Matrix.map_one _ (map_zero _) (map_one _)]

/-- The twisted point at a complex embedding `ψ` of `F`: the coordinates of
`diag(1/a) L^{(v)} x` read through `ψ`. -/
noncomputable def twistPoint (ψ : F →+* ℂ) (x : ι → F) : ι → ℂ := fun i ↦
  (((a.arch (InfinitePlace.mk (ψ.comp (algebraMap K F))) i)⁻¹ : ℝ) : ℂ) *
    ψ (((L.arch (InfinitePlace.mk (ψ.comp (algebraMap K F)))).map (algebraMap K F) *ᵥ x) i)

omit hα [NumberField F] in
theorem archFactor_mk_eq (ψ : F →+* ℂ) (x : ι → F) :
    L.archFactor a (InfinitePlace.mk ψ) x = ⨆ i, ‖L.twistPoint a ψ x i‖ := by
  rw [archFactor, InfinitePlace.comap_mk]
  refine iSup_congr fun i ↦ ?_
  rw [twistPoint, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr
    (a.arch_pos _ i).le), InfinitePlace.apply, inv_mul_eq_div]

omit [NumberField F] in
theorem toTwist_archFactor_eq (ψ : F →+* ℂ) (x : ι → F) :
    (L.toTwist a hα).archFactor ψ x =
      ‖(WithLp.toLp 2 (L.twistPoint a ψ x) : EuclideanSpace ℂ ι)‖ := by
  rw [Twist.archFactor]
  congr 2
  ext i
  rw [toTwist_arch, ← mulVec_mulVec, mulVec_diagonal, twistPoint, RingHom.map_mulVec,
    Matrix.map_map]
  rfl

omit [NumberField F] in
theorem archFactor_le_toTwist (ψ : F →+* ℂ) (x : ι → F) :
    L.archFactor a (InfinitePlace.mk ψ) x ≤ (L.toTwist a hα).archFactor ψ x := by
  rw [L.archFactor_mk_eq a, L.toTwist_archFactor_eq a hα]
  exact iSup_norm_le_norm_toLp _

omit [NumberField F] in
theorem toTwist_archFactor_le (ψ : F →+* ℂ) (x : ι → F) :
    (L.toTwist a hα).archFactor ψ x ≤
      √(Fintype.card ι) * L.archFactor a (InfinitePlace.mk ψ) x := by
  rw [L.archFactor_mk_eq a, L.toTwist_archFactor_eq a hα]
  exact norm_toLp_le_sqrt_card_mul_iSup _

theorem mulHeight_le_toTwist (x : ι → F) : L.mulHeight a x ≤ (L.toTwist a hα).mulHeight x := by
  rw [mulHeight, Twist.mulHeight,
    ← prod_embeddings_eq (fun w : InfinitePlace F ↦ L.archFactor a w x),
    finprod_congr (L.finFactor_toTwist a hα · x)]
  exact mul_le_mul_of_nonneg_right (Finset.prod_le_prod₀
    (fun ψ _ ↦ L.archFactor_nonneg a _ x) fun ψ _ ↦ L.archFactor_le_toTwist a hα ψ x)
    (finprod_nonneg fun w ↦ L.finFactor_nonneg a w x)

theorem toTwist_mulHeight_le (x : ι → F) :
    (L.toTwist a hα).mulHeight x ≤ √(Fintype.card ι) ^ finrank ℚ F * L.mulHeight a x := by
  rw [mulHeight, Twist.mulHeight,
    ← prod_embeddings_eq (fun w : InfinitePlace F ↦ L.archFactor a w x),
    finprod_congr (L.finFactor_toTwist a hα · x), ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (finprod_nonneg fun w ↦ L.finFactor_nonneg a w x)
  calc ∏ ψ : F →+* ℂ, (L.toTwist a hα).archFactor ψ x
      ≤ ∏ ψ : F →+* ℂ, √(Fintype.card ι) * L.archFactor a (InfinitePlace.mk ψ) x :=
        Finset.prod_le_prod₀ (fun ψ _ ↦ Twist.archFactor_nonneg _ ψ x)
          fun ψ _ ↦ L.toTwist_archFactor_le a hα ψ x
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Embeddings.card]

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

/-- **The twist bounds the height from above**: `H_{L,A} ≤ H_T`. -/
theorem absMulHeight_le_toTwist (x : ι → Ω) :
    L.absMulHeight a x ≤ (L.toTwist a hα).absMulHeight x := by
  have := Twist.numberField_adjoin_range (K := K) x
  rw [absMulHeight, Twist.absMulHeight]
  exact Real.rpow_le_rpow (L.mulHeight_nonneg a _) (L.mulHeight_le_toTwist a hα _)
    (by positivity)

/-- **ES02 (7.8)**: `H_T ≤ n^{1/2} H_{L,A}`. -/
theorem toTwist_absMulHeight_le (x : ι → Ω) :
    (L.toTwist a hα).absMulHeight x ≤ √(Fintype.card ι) * L.absMulHeight a x := by
  have := Twist.numberField_adjoin_range (K := K) x
  rw [absMulHeight, Twist.absMulHeight]
  refine (Real.rpow_le_rpow (Twist.mulHeight_nonneg _ _) (L.toTwist_mulHeight_le a hα _)
    (by positivity)).trans_eq ?_
  rw [Real.mul_rpow (pow_nonneg (Real.sqrt_nonneg _) _) (L.mulHeight_nonneg a _),
    Real.pow_rpow_inv_natCast (Real.sqrt_nonneg _) finrank_pos.ne']

end FormSystem

section Det

variable {ι : Type*} [Fintype ι] [LinearOrder ι] (L : FormSystem K ι) (a : FormWeight K ι)
  {α : FinitePlace K → ι → K} (hα : ∀ v i, a.fin v i = v (α v i))

namespace FormSystem

/-- **The determinant of the twist**: `|det T|_𝔸 = Δ_L / ∏_v ∏_i A_iv`. -/
theorem absDet_toTwist : (L.toTwist a hα).absDet = L.absDet / a.absProd := by
  have harch : ∀ φ : K →+* ℂ, ‖((L.toTwist a hα).arch φ).det‖ =
      (fun v : InfinitePlace K ↦ v (L.arch v).det / ∏ i, a.arch v i) (InfinitePlace.mk φ) := by
    intro φ
    rw [toTwist_arch, det_mul, det_diagonal, show (L.arch (InfinitePlace.mk φ)).map φ =
      φ.mapMatrix (L.arch (InfinitePlace.mk φ)) from rfl, ← RingHom.map_det, norm_mul,
      norm_prod]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_inv, InfinitePlace.apply]
    rw [Finset.prod_inv_distrib, inv_mul_eq_div]
    congr 1
    exact Finset.prod_congr rfl fun i _ ↦ abs_of_pos (a.arch_pos _ i)
  have hfin : ∀ v : FinitePlace K, v ((L.toTwist a hα).fin v).det =
      v (L.fin v).det / ∏ i, a.fin v i := by
    intro v
    by_cases hv : v ∈ L.badPlaces a
    · rw [L.toTwist_fin_of_mem a hα hv, det_mul, det_diagonal, map_mul, map_prod]
      simp_rw [map_inv₀, ← hα]
      rw [Finset.prod_inv_distrib, inv_mul_eq_div]
    · have hnv : IsNonarchimedean v.1 := fun a b ↦ FinitePlace.add_le v a b
      have hdet : v (L.fin v).det = 1 := Matrix.apply_det_eq_one_of_mul_eq_one hnv
        (mul_nonsing_inv _ (Ne.isUnit (L.fin_det_ne_zero v)))
        (fun i j ↦ (L.apply_le_one_of_notMem a hv i j).1)
        (fun i j ↦ (L.apply_le_one_of_notMem a hv i j).2)
      rw [L.toTwist_fin_of_notMem a hα hv, det_one, map_one, hdet,
        L.fin_eq_one_of_notMem a hv]
      simp
  have hmul : (∏ φ : K →+* ℂ, ‖((L.toTwist a hα).arch φ).det‖) *
      ∏ᶠ v : FinitePlace K, v ((L.toTwist a hα).fin v).det = L.mulDet / a.mulProd := by
    rw [Finset.prod_congr rfl fun φ _ ↦ harch φ,
      prod_embeddings_eq (fun v : InfinitePlace K ↦ v (L.arch v).det / ∏ i, a.arch v i),
      finprod_congr hfin,
      finprod_div_distrib L.hasFiniteMulSupport_det_fin a.hasFiniteMulSupport_prod_fin,
      mulDet, FormWeight.mulProd]
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, mul_div_mul_comm]
  rw [Twist.absDet, hmul, Real.div_rpow L.mulDet_pos.le a.mulProd_pos.le, absDet,
    FormWeight.absProd]

end FormSystem

end Det

/-! ### Successive infima against the minima of a twist -/

namespace Twist

variable [DecidableEq ι] (A : Twist K ι) {Ω : Type*} [Field Ω] [Algebra K Ω]
  [Algebra.IsAlgebraic K Ω] {h : (ι → Ω) → ℝ}

/-- A height below the twisted height has smaller successive infima. -/
theorem heightInf_le_absMinimum (hle : ∀ x, h x ≤ A.absMulHeight x) {i : ℕ} (hi0 : 0 < i)
    (hi : i ≤ Fintype.card ι) : heightInf Ω h i ≤ A.absMinimum Ω i := by
  refine le_csInf (A.absMinimumSet_nonempty hi) fun μ ⟨x, hx, hxμ⟩ ↦ ?_
  exact heightInf_le_of_linearIndependent hx
    ((A.absMulHeight_nonneg _).trans (hxμ ⟨0, hi0⟩)) fun j ↦ (hle _).trans (hxμ j)

/-- A twisted height below `c h` has minima below `c` times the successive infima of `h`. -/
theorem absMinimum_le_mul_heightInf {c : ℝ} (hc : 0 < c) (hle : ∀ x, A.absMulHeight x ≤ c * h x)
    {i : ℕ} (hi0 : 0 < i) (hi : i ≤ Fintype.card ι) :
    A.absMinimum Ω i ≤ c * heightInf Ω h i := by
  rw [← div_le_iff₀' hc]
  refine le_of_forall_gt_imp_ge_of_dense fun μ hμ ↦ ?_
  obtain ⟨x, hx, hxμ⟩ := exists_linearIndependent_of_heightInf_lt hi hμ
  rw [div_le_iff₀' hc]
  exact A.absMinimum_le hi0 hx fun j ↦ (hle _).trans (mul_le_mul_of_nonneg_left (hxμ j) hc.le)

end Twist

/-! ### ES02 Prop. 7.1: rational weights -/

namespace FormSystem

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]
  {n : ℕ} (L : FormSystem K (Fin n)) (a : FormWeight K (Fin n))
  {α : FinitePlace K → Fin n → K} (hα : ∀ v i, a.fin v i = v (α v i))
include hα

/-- **ES02 Prop. 7.1, upper bound**, for weights `A_iv = ‖α_iv‖_v`:
`λ₁ ⋯ λₙ ≤ 2^{n(n-1)/2} Δ_L / ∏_v ∏_i A_iv`. -/
theorem prod_successiveInf_le_of_eq_apply (hn : 0 < n) :
    ∏ i : Fin n, L.successiveInf a Ω (i + 1) ≤ √2 ^ (n * (n - 1)) * (L.absDet / a.absProd) := by
  calc ∏ i : Fin n, L.successiveInf a Ω (i + 1)
      ≤ ∏ i : Fin n, (L.toTwist a hα).absMinimum Ω (i + 1) :=
        Finset.prod_le_prod₀ (fun i _ ↦ heightInf_nonneg _) fun i _ ↦
          (L.toTwist a hα).heightInf_le_absMinimum (L.absMulHeight_le_toTwist a hα)
            (Nat.succ_pos _) (by simp [Nat.succ_le_of_lt i.2])
    _ ≤ √2 ^ (n * (n - 1)) * (L.toTwist a hα).absDet := Twist.prod_absMinimum_le hn _
    _ = _ := by rw [absDet_toTwist]

omit [IsAlgClosed Ω] in
/-- **ES02 Prop. 7.1, lower bound**, for weights `A_iv = ‖α_iv‖_v`:
`Δ_L / ∏_v ∏_i A_iv ≤ n^{n/2} λ₁ ⋯ λₙ`. -/
theorem le_prod_successiveInf_of_eq_apply :
    L.absDet / a.absProd ≤ √n ^ n * ∏ i : Fin n, L.successiveInf a Ω (i + 1) := by
  rw [← L.absDet_toTwist a hα]
  calc (L.toTwist a hα).absDet ≤ ∏ i : Fin n, (L.toTwist a hα).absMinimum Ω (i + 1) :=
        (L.toTwist a hα).absDet_le_prod_absMinimum (Fintype.card_fin n)
    _ ≤ ∏ i : Fin n, (√n * L.successiveInf a Ω (i + 1)) :=
        Finset.prod_le_prod₀ (fun i _ ↦ Twist.absMinimum_nonneg _ _) fun i _ ↦
          (L.toTwist a hα).absMinimum_le_mul_heightInf
            (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.2)))
            (fun x ↦ by simpa using L.toTwist_absMulHeight_le a hα x)
            (Nat.succ_pos _) (by simp [Nat.succ_le_of_lt i.2])
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]

end FormSystem

/-! ### Rescaled weights -/

namespace FormWeight

/-- **The weights rescaled at each finite place `v` by `r v > 0`**, `r = 1` almost everywhere. -/
noncomputable def scale (a : FormWeight K ι) (r : FinitePlace K → ℝ) (hr : ∀ v, 0 < r v)
    (hrf : r.HasFiniteMulSupport) : FormWeight K ι where
  arch := a.arch
  arch_pos := a.arch_pos
  fin v i := a.fin v i * r v
  fin_pos v i := mul_pos (a.fin_pos v i) (hr v)
  finite_setOf_fin_ne_one := (a.finite_setOf_fin_ne_one.union hrf).subset fun v hv ↦ by
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, mem_mulSupport, not_or, not_not] at h
    exact hv (funext fun i ↦ by simp [h.1, h.2])

variable (a : FormWeight K ι) {r : FinitePlace K → ℝ} (hr : ∀ v, 0 < r v)
  (hrf : r.HasFiniteMulSupport)

omit [Fintype ι] in
private theorem finprod_pos {r : FinitePlace K → ℝ} (hr : ∀ v, 0 < r v)
    (hrf : r.HasFiniteMulSupport) : 0 < ∏ᶠ v, r v := by
  rw [finprod_eq_prod _ hrf]
  exact Finset.prod_pos fun v _ ↦ hr v

theorem absProd_scale : (a.scale r hr hrf).absProd =
    a.absProd * ((∏ᶠ v, r v) ^ ((finrank ℚ K : ℝ))⁻¹) ^ Fintype.card ι := by
  have hP := finprod_pos hr hrf
  rw [absProd, absProd, a.mulProd_of_scale (b := a.scale r hr hrf) hrf (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl),
    Real.mul_rpow a.mulProd_pos.le (pow_nonneg hP.le _), ← Real.rpow_natCast,
    ← Real.rpow_natCast, ← Real.rpow_mul hP.le, ← Real.rpow_mul hP.le,
    mul_comm (Fintype.card ι : ℝ)]

end FormWeight

namespace FormSystem

variable [DecidableEq ι] (L : FormSystem K ι) (a : FormWeight K ι) {r : FinitePlace K → ℝ}
  (hr : ∀ v, 0 < r v) (hrf : r.HasFiniteMulSupport)
  {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

theorem absMulHeight_scale (x : ι → Ω) : L.absMulHeight (a.scale r hr hrf) x =
    L.absMulHeight a x / (∏ᶠ v, r v) ^ ((finrank ℚ K : ℝ))⁻¹ := by
  rw [L.absMulHeight_of_scale (a := a) (b := a.scale r hr hrf) (s := fun _ ↦ 1)
    (fun _ ↦ one_pos) hr hrf
    (fun _ _ ↦ (mul_one _).symm) (fun _ _ ↦ rfl)]
  simp

end FormSystem

/-! ### Real weights: approximation over an extension (ES02 Cor. 7.2) -/

private theorem le_mul_pow_of_abs_log_sub_le {x y ε : ℝ} (hx : 0 < x) (hy : 0 < y) (hε : 0 < ε)
    {m : ℕ} (h : |Real.log x - Real.log y| ≤ m * Real.log (1 + ε)) : x ≤ y * (1 + ε) ^ m := by
  rw [← Real.log_le_log_iff hx (by positivity), Real.log_mul hy.ne' (by positivity),
    Real.log_pow]
  linarith [le_abs_self (Real.log x - Real.log y)]

private theorem abs_round_mul_sub_le {t y δ : ℝ} (ht : 0 < t) {N : ℕ} (hN : 0 < N)
    (htN : t ≤ N * δ) : |(round (y * N / t) : ℝ) * t / N - y| ≤ δ := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h := abs_sub_round (y * N / t)
  have heq : (round (y * N / t) : ℝ) * t / N - y = -(t / N) * (y * N / t - round (y * N / t)) := by
    field_simp
    ring
  have htN' : t / N ≤ δ := (div_le_iff₀ hN').mpr (by linarith)
  rw [heq, abs_mul, abs_neg, abs_of_pos (div_pos ht hN')]
  nlinarith [div_pos ht hN', abs_nonneg (y * N / t - round (y * N / t))]

namespace FormSystem

variable [DecidableEq ι] (L : FormSystem K ι) (a : FormWeight K ι)
  {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]

/-- **ES02 Cor. 7.2, the approximation.** For `ε > 0` there are an extension `E ⊆ Ω` of `K` and
weights `b` over `E` of the form `‖α_iq‖_q` (ES02 (7.11)–(7.12)) whose height and weight product
are within the factor `R = (1 + ε) ^ {s / [K:ℚ]}` of those of `a`, `s` the number of finite places
where `a` is not `1`. -/
theorem exists_eq_apply_weight {ε : ℝ} (hε : 0 < ε) :
    ∃ (E : IntermediateField K Ω) (_ : NumberField E) (b : FormWeight E ι)
      (α : FinitePlace E → ι → E), (∀ q i, b.fin q i = q (α q i)) ∧
      (∀ x : ι → Ω, (L.baseChange E).absMulHeight b x ≤
        ((1 + ε) ^ a.finite_setOf_fin_ne_one.toFinset.card) ^ ((finrank ℚ K : ℝ))⁻¹ *
          L.absMulHeight a x) ∧
      (∀ x : ι → Ω, L.absMulHeight a x ≤
        ((1 + ε) ^ a.finite_setOf_fin_ne_one.toFinset.card) ^ ((finrank ℚ K : ℝ))⁻¹ *
          (L.baseChange E).absMulHeight b x) ∧
      b.absProd ≤ (((1 + ε) ^ a.finite_setOf_fin_ne_one.toFinset.card) ^
        ((finrank ℚ K : ℝ))⁻¹) ^ Fintype.card ι * a.absProd ∧
      a.absProd ≤ (((1 + ε) ^ a.finite_setOf_fin_ne_one.toFinset.card) ^
        ((finrank ℚ K : ℝ))⁻¹) ^ Fintype.card ι * b.absProd := by
  classical
  set S := a.finite_setOf_fin_ne_one.toFinset with hS
  have hmemS : ∀ v, v ∈ S ↔ a.fin v ≠ 1 := fun v ↦ by simp [S]
  set R := ((1 + ε) ^ S.card) ^ ((finrank ℚ K : ℝ))⁻¹ with hR
  have hR0 : 0 < R := by positivity
  -- An element `β_v` with `|β_v|_v > 1` at every finite place.
  have hβ : ∀ v : FinitePlace K, ∃ β : K, 1 < v β := fun v ↦ by
    obtain ⟨β, hβ⟩ := FinitePlace.zpow_mem_range v 1
    refine ⟨β, ?_⟩
    rw [hβ, zpow_one]
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.maximalIdeal
  choose β hβ using hβ
  set t : FinitePlace K → ℝ := fun v ↦ Real.log (v (β v))
  have ht : ∀ v, 0 < t v := fun v ↦ Real.log_pos (hβ v)
  set δ := Real.log (1 + ε)
  have hδ : 0 < δ := Real.log_pos (by linarith)
  set N := ⌈(∑ v ∈ S, t v) / δ⌉₊ + 1
  have hN : 0 < N := Nat.succ_pos _
  have htN : ∀ v ∈ S, t v ≤ N * δ := fun v hv ↦ by
    have h1 : t v ≤ ∑ v ∈ S, t v := Finset.single_le_sum (fun v _ ↦ (ht v).le) hv
    have h2 : (∑ v ∈ S, t v) / δ ≤ N := (Nat.le_ceil _).trans (by simp [N])
    rw [div_le_iff₀ hδ] at h2
    linarith
  set k : FinitePlace K → ι → ℤ := fun v i ↦ round (Real.log (a.fin v i) * N / t v)
  have hk : ∀ v ∈ S, ∀ i, |(k v i : ℝ) * t v / N - Real.log (a.fin v i)| ≤ δ := fun v hv i ↦
    abs_round_mul_sub_le (ht v) hN (htN v hv)
  -- `N`-th roots `γ_v` of the `β_v`, and the field `E = K(γ_v : v ∈ S)`.
  have hγ : ∀ v : FinitePlace K, ∃ γ : Ω, γ ^ N = algebraMap K Ω (β v) := fun v ↦
    IsAlgClosed.exists_pow_nat_eq _ hN
  choose γ hγ using hγ
  set E := IntermediateField.adjoin K (γ '' S)
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have : Finite (γ '' S) := (S.finite_toSet.image γ).to_subtype
  have : FiniteDimensional K E := IntermediateField.finiteDimensional_adjoin fun y _ ↦
    (Algebra.IsAlgebraic.isAlgebraic (R := K) y).isIntegral
  have : NumberField E := { to_finiteDimensional := Module.Finite.trans K _ }
  have hγE : ∀ v ∈ S, γ v ∈ E := fun v hv ↦ IntermediateField.subset_adjoin K _ ⟨v, hv, rfl⟩
  have hβ0 : ∀ v, β v ≠ 0 := fun v h ↦ by
    have := hβ v
    rw [h, map_zero] at this
    linarith
  have hγ0 : ∀ v, γ v ≠ 0 := fun v h ↦ hβ0 v (by
    have := hγ v
    rw [h, zero_pow hN.ne'] at this
    exact (map_eq_zero _).mp this.symm)
  set αE : FinitePlace E → ι → E := fun q i ↦
    if h : q.under K ∈ S then (⟨γ (q.under K), hγE _ h⟩ : E) ^ k (q.under K) i else 1
  have hαE0 : ∀ q i, αE q i ≠ 0 := fun q i ↦ by
    simp only [αE]
    split_ifs with h
    · exact zpow_ne_zero _ fun h' ↦ hγ0 _ (congrArg Subtype.val h')
    · exact one_ne_zero
  have hαE1 : ∀ q i, q.under K ∉ S → αE q i = 1 := fun q i h ↦ by simp [αE, h]
  let b : FormWeight E ι :=
    { arch := (a.baseChange E).arch
      arch_pos := (a.baseChange E).arch_pos
      fin := fun q i ↦ q (αE q i)
      fin_pos := fun q i ↦ FinitePlace.pos_iff.mpr (hαE0 q i)
      finite_setOf_fin_ne_one := by
        refine (S.finite_toSet.biUnion fun v _ ↦ FinitePlace.finite_placesOver E v).subset
          fun q hq ↦ Set.mem_biUnion (x := q.under K) ?_
            (FinitePlace.mem_placesOver.mpr (FinitePlace.liesOver_under (K := K) q))
        by_contra h
        exact hq (funext fun i ↦ by simp [hαE1 q i h]) }
  -- The rescaling factors `ρ_q = (1 + ε) ^ {d(q|v)}` above `S`.
  set f : FinitePlace K → ℝ := fun v ↦ if v ∈ S then 1 + ε else 1
  have hf : f.HasFiniteMulSupport := S.finite_toSet.subset fun v hv ↦ by
    by_contra h
    have h' : v ∉ S := by simpa using h
    exact hv (by simp [f, h'])
  set ρ : FinitePlace E → ℝ := fun q ↦ f (q.under K) ^ q.localDegree K
  have hρ : ∀ q, 0 < ρ q := fun q ↦ pow_pos (by simp only [f]; split_ifs <;> linarith) _
  have hρf : ρ.HasFiniteMulSupport := FinitePlace.hasFiniteMulSupport_comp_under hf _
  have hprodf : ∏ᶠ v, f v = (1 + ε) ^ S.card := by
    rw [finprod_eq_prod_of_mulSupport_subset f (s := S) fun v hv ↦ by
      by_contra h
      have h' : v ∉ S := by simpa using h
      exact hv (by simp [f, h'])]
    simp [f]
  have hprodρ : (∏ᶠ q, ρ q) ^ ((finrank ℚ E : ℝ))⁻¹ = R := by
    rw [FinitePlace.finprod_under_pow_localDegree f hf, hprodf,
      rpow_finrank_inv (by positivity)]
  -- The key estimate at each finite place of `E`.
  have hkey : ∀ q i, b.fin q i ≤ (a.baseChange E).fin q i * ρ q ∧
      (a.baseChange E).fin q i ≤ b.fin q i * ρ q := by
    intro q i
    change q (αE q i) ≤ a.fin (q.under K) i ^ q.localDegree K * ρ q ∧
      a.fin (q.under K) i ^ q.localDegree K ≤ q (αE q i) * ρ q
    by_cases hv : q.under K ∈ S
    · set v := q.under K
      set γq : E := ⟨γ v, hγE v hv⟩
      have hαq : αE q i = γq ^ k v i := by simp [αE, hv, γq, v]
      have hγq : q γq ^ N = v (β v) ^ q.localDegree K := by
        rw [← map_pow, ← FinitePlace.apply_algebraMap q v]
        congr 1
        exact Subtype.ext (hγ v)
      have hγq0 : 0 < q γq := FinitePlace.pos_iff.mpr fun h ↦ hγ0 v (congrArg Subtype.val h)
      have hlogγ : Real.log (q γq) = q.localDegree K * t v / N := by
        have := congrArg Real.log hγq
        rw [Real.log_pow, Real.log_pow] at this
        field_simp
        linarith
      have hρq : ρ q = (1 + ε) ^ q.localDegree K := by simp [ρ, f, hv, v]
      have hpos : 0 < a.fin v i := a.fin_pos v i
      have habs : |Real.log (q (αE q i)) - Real.log (a.fin v i ^ q.localDegree K)| ≤
          q.localDegree K * δ := by
        rw [hαq, map_zpow₀, Real.log_zpow, hlogγ, Real.log_pow]
        have : (k v i : ℝ) * (q.localDegree K * t v / N) - q.localDegree K * Real.log (a.fin v i)
            = q.localDegree K * ((k v i : ℝ) * t v / N - Real.log (a.fin v i)) := by ring
        rw [this, abs_mul, Nat.abs_cast]
        exact mul_le_mul_of_nonneg_left (hk v hv i) (Nat.cast_nonneg _)
      have hb0 : 0 < q (αE q i) := FinitePlace.pos_iff.mpr (hαE0 q i)
      rw [hρq]
      exact ⟨le_mul_pow_of_abs_log_sub_le hb0 (pow_pos hpos _) hε habs,
        le_mul_pow_of_abs_log_sub_le (pow_pos hpos _) hb0 hε (by rwa [abs_sub_comm])⟩
    · have ha1 : a.fin (q.under K) = 1 := by
        by_contra h
        exact hv ((hmemS _).mpr h)
      have hρq : ρ q = 1 := by simp [ρ, f, hv]
      simp [hαE1 q i hv, ha1, hρq]
  -- Heights and products.
  have hscale := fun (c : FormWeight E ι) ↦ (L.baseChange E).absMulHeight_scale c hρ hρf (Ω := Ω)
  refine ⟨E, inferInstance, b, αE, fun _ _ ↦ rfl, fun x ↦ ?_, fun x ↦ ?_, ?_, ?_⟩
  · have h := (L.baseChange E).absMulHeight_le_of_le (a := a.baseChange E) (b := b.scale ρ hρ hρf)
      (fun _ _ ↦ le_rfl) (fun q i ↦ (hkey q i).2) x
    rw [hscale, hprodρ, L.absMulHeight_baseChange, div_le_iff₀ hR0] at h
    linarith
  · have h := (L.baseChange E).absMulHeight_le_of_le (a := b) (b := (a.baseChange E).scale ρ hρ hρf)
      (fun _ _ ↦ le_rfl) (fun q i ↦ (hkey q i).1) x
    rw [hscale, hprodρ, L.absMulHeight_baseChange, div_le_iff₀ hR0] at h
    linarith
  · have h := b.absProd_le_of_le (b := (a.baseChange E).scale ρ hρ hρf) (fun _ _ ↦ le_rfl)
      fun q i ↦ (hkey q i).1
    rwa [FormWeight.absProd_scale, hprodρ, FormWeight.absProd_baseChange, mul_comm] at h
  · have h := (a.baseChange E).absProd_le_of_le (b := b.scale ρ hρ hρf) (fun _ _ ↦ le_rfl)
      fun q i ↦ (hkey q i).2
    rwa [FormWeight.absProd_scale, hprodρ, FormWeight.absProd_baseChange, mul_comm] at h

end FormSystem

/-! ### EF13 Prop. 9.2 -/

private theorem le_of_forall_le_one_add_pow_mul {X Y : ℝ} {m : ℕ}
    (h : ∀ ε > 0, X ≤ (1 + ε) ^ m * Y) : X ≤ Y := by
  have hc : Continuous fun ε : ℝ ↦ (1 + ε) ^ m * Y := by fun_prop
  have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simp only [add_zero, one_pow, one_mul] at ht
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall h)

private theorem rpow_inv_finrank_le {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    ((1 + ε) ^ m) ^ ((finrank ℚ K : ℝ))⁻¹ ≤ (1 + ε) ^ m := by
  calc ((1 + ε) ^ m) ^ ((finrank ℚ K : ℝ))⁻¹ ≤ ((1 + ε) ^ m) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by linarith))
          (inv_le_one_of_one_le₀ (by exact_mod_cast finrank_pos))
    _ = _ := Real.rpow_one _

namespace FormSystem

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]
  {n : ℕ} (L : FormSystem K (Fin n)) (a : FormWeight K (Fin n))

/-- **The absolute Minkowski theorem for twisted heights, upper bound** (ES02 Cor. 7.2, EF13
Prop. 9.2): `λ₁ ⋯ λₙ ≤ 2^{n(n-1)/2} Δ_L / ∏_v ∏_i A_iv`, for any real weights. -/
theorem prod_successiveInf_le (hn : 0 < n) :
    ∏ i : Fin n, L.successiveInf a Ω (i + 1) ≤ √2 ^ (n * (n - 1)) * (L.absDet / a.absProd) := by
  set c := a.finite_setOf_fin_ne_one.toFinset.card
  refine le_of_forall_le_one_add_pow_mul (m := 2 * (c * n)) fun ε hε ↦ ?_
  obtain ⟨E, _, b, α, hα, -, h2, -, h4⟩ := L.exists_eq_apply_weight a (Ω := Ω) hε
  simp only [Fintype.card_fin] at h4
  set R := ((1 + ε) ^ c) ^ ((finrank ℚ K : ℝ))⁻¹
  have hR0 : 0 < R := by positivity
  have hRn : R ^ n ≤ (1 + ε) ^ (c * n) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ hR0.le (rpow_inv_finrank_le (K := K) hε c) n
  have hE := (L.baseChange E).prod_successiveInf_le_of_eq_apply b hα (Ω := Ω) hn
  rw [absDet_baseChange] at hE
  have hY : 0 ≤ L.absDet / a.absProd := (div_pos L.absDet_pos a.absProd_pos).le
  have hb : L.absDet / b.absProd ≤ R ^ n * (L.absDet / a.absProd) := by
    rw [div_le_iff₀ b.absProd_pos]
    calc L.absDet = L.absDet / a.absProd * a.absProd :=
          (div_mul_cancel₀ _ a.absProd_pos.ne').symm
      _ ≤ L.absDet / a.absProd * (R ^ n * b.absProd) := mul_le_mul_of_nonneg_left h4 hY
      _ = _ := by ring
  calc ∏ i : Fin n, L.successiveInf a Ω (i + 1)
      ≤ ∏ i : Fin n, (R * (L.baseChange E).successiveInf b Ω (i + 1)) :=
        Finset.prod_le_prod₀ (fun i _ ↦ heightInf_nonneg _) fun i _ ↦
          heightInf_le_mul hR0 h2 (by simp [Nat.succ_le_of_lt i.2])
    _ = R ^ n * ∏ i : Fin n, (L.baseChange E).successiveInf b Ω (i + 1) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ R ^ n * (√2 ^ (n * (n - 1)) * (R ^ n * (L.absDet / a.absProd))) := by
        gcongr
        exact hE.trans (mul_le_mul_of_nonneg_left hb (by positivity))
    _ ≤ (1 + ε) ^ (c * n) * (√2 ^ (n * (n - 1)) * ((1 + ε) ^ (c * n) * (L.absDet / a.absProd))) :=
        by gcongr
    _ = _ := by ring

/-- **The absolute Minkowski theorem for twisted heights, lower bound** (ES02 Cor. 7.2, EF13
Prop. 9.2): `Δ_L / ∏_v ∏_i A_iv ≤ n^{n/2} λ₁ ⋯ λₙ`, for any real weights. -/
theorem le_prod_successiveInf :
    L.absDet / a.absProd ≤ √n ^ n * ∏ i : Fin n, L.successiveInf a Ω (i + 1) := by
  set c := a.finite_setOf_fin_ne_one.toFinset.card
  refine le_of_forall_le_one_add_pow_mul (m := 2 * (c * n)) fun ε hε ↦ ?_
  obtain ⟨E, _, b, α, hα, h1, -, h3, -⟩ := L.exists_eq_apply_weight a (Ω := Ω) hε
  simp only [Fintype.card_fin] at h3
  set R := ((1 + ε) ^ c) ^ ((finrank ℚ K : ℝ))⁻¹
  have hR0 : 0 < R := by positivity
  have hRn : R ^ n ≤ (1 + ε) ^ (c * n) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ hR0.le (rpow_inv_finrank_le (K := K) hε c) n
  have hE := (L.baseChange E).le_prod_successiveInf_of_eq_apply b hα (Ω := Ω)
  rw [absDet_baseChange] at hE
  have hb : L.absDet / a.absProd ≤ R ^ n * (L.absDet / b.absProd) := by
    rw [div_le_iff₀ a.absProd_pos]
    calc L.absDet = L.absDet / b.absProd * b.absProd :=
          (div_mul_cancel₀ _ b.absProd_pos.ne').symm
      _ ≤ L.absDet / b.absProd * (R ^ n * a.absProd) :=
          mul_le_mul_of_nonneg_left h3 (div_pos L.absDet_pos b.absProd_pos).le
      _ = _ := by ring
  have hP : 0 ≤ ∏ i : Fin n, L.successiveInf a Ω (i + 1) :=
    Finset.prod_nonneg fun i _ ↦ heightInf_nonneg _
  calc L.absDet / a.absProd ≤ R ^ n * (L.absDet / b.absProd) := hb
    _ ≤ R ^ n * (√n ^ n * ∏ i : Fin n, (L.baseChange E).successiveInf b Ω (i + 1)) := by
        gcongr
    _ ≤ R ^ n * (√n ^ n * ∏ i : Fin n, (R * L.successiveInf a Ω (i + 1))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
          (by positivity)
        exact Finset.prod_le_prod₀ (fun i _ ↦ heightInf_nonneg _) fun i _ ↦
          heightInf_le_mul hR0 h1 (by simp [Nat.succ_le_of_lt i.2])
    _ = R ^ n * R ^ n * (√n ^ n * ∏ i : Fin n, L.successiveInf a Ω (i + 1)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring
    _ ≤ (1 + ε) ^ (c * n) * (1 + ε) ^ (c * n) *
          (√n ^ n * ∏ i : Fin n, L.successiveInf a Ω (i + 1)) := by gcongr
    _ = _ := by ring

/-- **EF13 Prop. 9.2, upper bound**: `λ₁(Q) ⋯ λₙ(Q) ≤ 2^{n(n-1)/2} Δ_L Q^{-α}`,
`α = Σ_v Σ_i c_iv`. -/
theorem prod_successiveInf_weight_le (hn : 0 < n) (c : FormExponent K (Fin n)) {Q : ℝ}
    (hQ : 0 < Q) : ∏ i : Fin n, L.successiveInf (c.weight hQ) Ω (i + 1) ≤
      √2 ^ (n * (n - 1)) * (L.absDet * Q ^ (-c.sum)) := by
  rw [Real.rpow_neg hQ.le, ← div_eq_mul_inv, ← c.absProd_weight hQ]
  exact L.prod_successiveInf_le _ hn

/-- **EF13 Prop. 9.2, lower bound**: `n^{-n/2} Δ_L Q^{-α} ≤ λ₁(Q) ⋯ λₙ(Q)`,
`α = Σ_v Σ_i c_iv`. -/
theorem le_prod_successiveInf_weight (hn : 0 < n) (c : FormExponent K (Fin n)) {Q : ℝ}
    (hQ : 0 < Q) : (√n ^ n)⁻¹ * (L.absDet * Q ^ (-c.sum)) ≤
      ∏ i : Fin n, L.successiveInf (c.weight hQ) Ω (i + 1) := by
  rw [Real.rpow_neg hQ.le, ← div_eq_mul_inv, ← c.absProd_weight hQ,
    inv_mul_le_iff₀ (pow_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)) n)]
  exact L.le_prod_successiveInf _

end FormSystem

end NumberField
