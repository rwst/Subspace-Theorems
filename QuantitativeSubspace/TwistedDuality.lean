/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.TwistedCalculus

-- Used only inside proofs.
import ArithmeticHeights.Duality

/-!
# Twisted duality

D. Roy and J. L. Thunder, *An absolute Siegel's lemma*, J. reine angew. Math. **476** (1996),
1–26, Theorem 1.1 (quoted there from Thunder 1993): for a twist `A` and its dual twist
`A* = (Aᵀ)⁻¹`, every subspace `V` of `Ωⁿ` satisfies

```text
H_{A*}(V^⊥) = |det A|_𝔸⁻¹ · H_A(V),
```

`V^⊥` the orthogonal complement for the standard bilinear form. The proof is the one of
`ArithmeticHeights/Duality.lean` with a twist at each place: take dual bases, the rows of `C` and
`D` with `C Dᵀ = 1`, the first block of `C` spanning `V` and the second block of `D` spanning
`V^⊥`. At each place, the rows of `C Mᵀ` and `D M⁻¹` are again dual, so the complementary-minor
identity relates the Plücker coordinates of `M V` and `M⁻ᵀ V^⊥` with the factor
`det C · det M` up to sign at each coordinate. The norms then differ by `|det C| · |det M|`, and
the product formula removes `det C`.

## Main definitions

* `NumberField.Twist.dual A`: the dual twist `A*`, with components `(A_v⁻¹)ᵀ`.

## Main results

* `NumberField.Twist.absSubspaceHeight_eq_absDet_mul`: `H_A(V) = |det A|_𝔸 · H_{A*}(V^⊥)`.
* `NumberField.Twist.absSubspaceHeight_dual`: RT96 Theorem 1.1 in their form.
* `NumberField.Twist.absDet_dual`, `NumberField.Twist.dual_dual`: `|det A*|_𝔸 = |det A|_𝔸⁻¹` and
  `A** = A`.

This is milestone Q2.2a of `QuantitativeSubspace/README.md` (its second part).
-/

@[expose] public section

open Finset Function Module Matrix exteriorPower IntermediateField

namespace Matrix

variable {L L' : Type*} [Field L] [Field L'] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_inv_transpose (M : Matrix ι ι L) : (M⁻¹ᵀ).det = M.det⁻¹ := by
  rw [det_transpose, det_nonsing_inv, Ring.inverse_eq_inv']

/-- The inverse of an invertible matrix commutes with a ring homomorphism. -/
theorem inv_map_of_det_ne_zero (f : L →+* L') {M : Matrix ι ι L} (hM : M.det ≠ 0) :
    (M.map f)⁻¹ = M⁻¹.map f :=
  inv_eq_left_inv <| by
    rw [← Matrix.map_mul, nonsing_inv_mul _ hM.isUnit, Matrix.map_one _ (map_zero f) (map_one f)]

end Matrix

namespace Matrix

variable {L : Type*} [Field L] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **The complementary-minor identity, twisted.** If the rows of `C` and of `D` are dual, so are
the rows of `C Mᵀ` and `D M⁻¹`: the Plücker coordinates of the images of the first block of `C`
under `M` and of the second block of `D` under `M⁻ᵀ` agree at complementary indices, up to sign,
with the factor `det C · det M`. -/
theorem plucker_mulVec_inl_eq_or_eq_neg {k l : ℕ}
    (C D : Matrix (Fin k ⊕ Fin l) ι L) (hCD : C * Dᵀ = 1) (hlk : l + k = Fintype.card ι)
    (e : Fin k ⊕ Fin l ≃ ι) {M : Matrix ι ι L} (hM : M.det ≠ 0) (s : Set.powersetCard ι k) :
    plucker k (fun i ↦ M *ᵥ (C.submatrix Sum.inl id).row i) s = (C.submatrix id e).det * M.det *
        plucker l (fun j ↦ M⁻¹ᵀ *ᵥ (D.submatrix Sum.inr id).row j)
          (Set.powersetCard.compl hlk s) ∨
      plucker k (fun i ↦ M *ᵥ (C.submatrix Sum.inl id).row i) s =
        -((C.submatrix id e).det * M.det * plucker l
          (fun j ↦ M⁻¹ᵀ *ᵥ (D.submatrix Sum.inr id).row j) (Set.powersetCard.compl hlk s)) := by
  have hCD' : (C * Mᵀ) * (D * M⁻¹)ᵀ = 1 := by
    rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Mᵀ, ← transpose_mul,
      nonsing_inv_mul _ hM.isUnit, transpose_one, Matrix.one_mul, hCD]
  have hC : (fun i ↦ M *ᵥ (C.submatrix Sum.inl id).row i) =
      ((C * Mᵀ).submatrix Sum.inl id).row := by
    funext i j
    simp only [mulVec, dotProduct, row, submatrix_apply, id_eq, mul_apply, transpose_apply]
    exact sum_congr rfl fun _ _ ↦ mul_comm _ _
  have hD : (fun j ↦ M⁻¹ᵀ *ᵥ (D.submatrix Sum.inr id).row j) =
      ((D * M⁻¹).submatrix Sum.inr id).row := by
    funext i j
    simp only [mulVec, dotProduct, row, submatrix_apply, id_eq, mul_apply, transpose_apply]
    exact sum_congr rfl fun _ _ ↦ mul_comm _ _
  have hdet : ((C * Mᵀ).submatrix id e).det = (C.submatrix id e).det * M.det := by
    rw [← Matrix.submatrix_mul_equiv C Mᵀ id e e, det_mul, det_submatrix_equiv_self,
      det_transpose]
  rw [hC, hD, ← hdet]
  exact Matrix.plucker_inl_eq_or_eq_neg _ _ hCD' hlk e s

end Matrix

namespace NumberField.Twist

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (A : Twist K ι)

/-! ### The dual twist -/

/-- **The dual twist** `A*` (RT96 §1): the inverse transpose of every component. -/
noncomputable def dual : Twist K ι where
  arch φ := (A.arch φ)⁻¹ᵀ
  arch_det_ne_zero φ := by
    rw [det_transpose]
    exact (isUnit_nonsing_inv_det _ (A.arch_det_ne_zero φ).isUnit).ne_zero
  arch_conjugate φ := by
    rw [A.arch_conjugate, inv_map_of_det_ne_zero _ (A.arch_det_ne_zero φ), transpose_map]
  fin v := (A.fin v)⁻¹ᵀ
  fin_det_ne_zero v := by
    rw [det_transpose]
    exact (isUnit_nonsing_inv_det _ (A.fin_det_ne_zero v).isUnit).ne_zero
  finite_setOf_fin_ne_one := A.finite_setOf_fin_ne_one.subset fun v hv h ↦ hv (by simp [h])

@[simp] theorem dual_arch (φ : K →+* ℂ) : A.dual.arch φ = (A.arch φ)⁻¹ᵀ := rfl

@[simp] theorem dual_fin (v : FinitePlace K) : A.dual.fin v = (A.fin v)⁻¹ᵀ := rfl

private theorem inv_transpose_inv_transpose {R : Type*} [Field R] {M : Matrix ι ι R}
    (hM : M.det ≠ 0) : (M⁻¹ᵀ)⁻¹ᵀ = M := by
  rw [transpose_nonsing_inv, transpose_transpose, nonsing_inv_nonsing_inv _ hM.isUnit]

/-- **The dual of the dual is the twist itself.** -/
theorem dual_dual : A.dual.dual = A :=
  ext (fun φ ↦ inv_transpose_inv_transpose (A.arch_det_ne_zero φ))
    fun v ↦ inv_transpose_inv_transpose (A.fin_det_ne_zero v)

theorem dual_baseChange (E : Type*) [Field E] [NumberField E] [Algebra K E] :
    (A.baseChange E).dual = A.dual.baseChange E :=
  ext (fun _ ↦ rfl) fun w ↦ by
    rw [dual_fin, baseChange_fin, baseChange_fin, dual_fin,
      inv_map_of_det_ne_zero _ (A.fin_det_ne_zero _), transpose_map]

/-! ### The local identities -/

section Local

variable {ι : Type*} [Fintype ι] [LinearOrder ι] (A : Twist K ι)

/-- **`|det A*|_𝔸 = |det A|_𝔸⁻¹`.** -/
theorem absDet_dual : A.dual.absDet = A.absDet⁻¹ := by
  have hf : (fun v : FinitePlace K ↦ v (A.fin v).det).HasFiniteMulSupport :=
    A.finite_setOf_fin_ne_one.subset fun v hv h ↦ hv (by simp [h])
  simp only [absDet, dual_arch, dual_fin, det_inv_transpose, norm_inv, map_inv₀]
  rw [prod_inv_distrib, finprod_inv_distrib, ← mul_inv, Real.inv_rpow]
  exact mul_nonneg (prod_nonneg fun _ _ ↦ norm_nonneg _) (finprod_nonneg fun _ ↦ apply_nonneg _ _)

variable {E : Type*} [Field E] [NumberField E] [Algebra K E] {k l : ℕ}
  (C D : Matrix (Fin k ⊕ Fin l) ι E) (hCD : C * Dᵀ = 1) (hlk : l + k = Fintype.card ι)
  (e : Fin k ⊕ Fin l ≃ ι)
include hCD hlk e

omit [NumberField E] in
/-- **Twisted duality at a complex embedding.** -/
theorem archFactor_plucker_inl (φ : E →+* ℂ) :
    (A.exteriorPower k).archFactor φ (plucker k (C.submatrix Sum.inl id).row) =
      ‖(A.arch (φ.comp (algebraMap K E))).det‖ * (A.dual.exteriorPower l).archFactor φ
        ((C.submatrix id e).det • plucker l (D.submatrix Sum.inr id).row) := by
  set M := A.arch (φ.comp (algebraMap K E))
  have hM : M.det ≠ 0 := A.arch_det_ne_zero _
  have hCDφ : C.map φ * (D.map φ)ᵀ = 1 := by
    rw [← transpose_map, ← Matrix.map_mul, hCD, Matrix.map_one _ (map_zero φ) (map_one φ)]
  set P := plucker k (fun i ↦ M *ᵥ ((C.map φ).submatrix Sum.inl id).row i) with hPdef
  set Q := plucker l (fun j ↦ M⁻¹ᵀ *ᵥ ((D.map φ).submatrix Sum.inr id).row j) with hQdef
  have hP : (A.exteriorPower k).archFactor φ (plucker k (C.submatrix Sum.inl id).row) =
      ‖(WithLp.toLp 2 P : EuclideanSpace ℂ _)‖ := by
    rw [archFactor, exteriorPower_arch, ← plucker_comp_ringHom, compound_mulVec_plucker]
    rfl
  have hQ : (A.dual.exteriorPower l).archFactor φ (plucker l (D.submatrix Sum.inr id).row) =
      ‖(WithLp.toLp 2 Q : EuclideanSpace ℂ _)‖ := by
    rw [archFactor, exteriorPower_arch, ← plucker_comp_ringHom, compound_mulVec_plucker]
    rfl
  have hc : (C.map φ).submatrix id e = ((C.submatrix id e).map φ) := rfl
  have hrel (s : Set.powersetCard ι k) :
      ‖P s‖ = ‖φ (C.submatrix id e).det‖ * ‖M.det‖ * ‖Q (Set.powersetCard.compl hlk s)‖ := by
    rcases Matrix.plucker_mulVec_inl_eq_or_eq_neg _ _ hCDφ hlk e hM s with h | h <;>
      rw [hPdef, hQdef, h, hc, ← RingHom.mapMatrix_apply, ← RingHom.map_det] <;> simp
  rw [archFactor_smul, hP, hQ]
  refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [mul_pow, mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, mul_sum, mul_sum]
  simp_rw [hrel]
  conv_rhs => rw [← Equiv.sum_comp (Set.powersetCard.compl hlk)]
  exact sum_congr rfl fun t _ ↦ by ring

/-- **Twisted duality at a finite place.** -/
theorem finFactor_plucker_inl (w : FinitePlace E) :
    (A.exteriorPower k).finFactor w (plucker k (C.submatrix Sum.inl id).row) =
      w ((A.fin (w.under K)).map (algebraMap K E)).det * (A.dual.exteriorPower l).finFactor w
        ((C.submatrix id e).det • plucker l (D.submatrix Sum.inr id).row) := by
  set M := (A.fin (w.under K)).map (algebraMap K E)
  have hM : M.det ≠ 0 := (A.baseChange E).fin_det_ne_zero w
  have hdual : (A.dual.fin (w.under K)).map (algebraMap K E) = M⁻¹ᵀ := by
    rw [dual_fin, transpose_map, ← inv_map_of_det_ne_zero _ (A.fin_det_ne_zero _)]
  have hrel (s : Set.powersetCard ι k) :
      w (plucker k (fun i ↦ M *ᵥ (C.submatrix Sum.inl id).row i) s) =
        w (C.submatrix id e).det * w M.det * w (plucker l
          (fun j ↦ M⁻¹ᵀ *ᵥ (D.submatrix Sum.inr id).row j) (Set.powersetCard.compl hlk s)) := by
    have hneg : ∀ x : E, w (-x) = w x := fun x ↦ w.1.map_neg x
    rcases Matrix.plucker_mulVec_inl_eq_or_eq_neg _ _ hCD hlk e hM s with h | h <;>
      rw [h] <;> simp only [hneg, map_mul]
  rw [finFactor_smul, finFactor, finFactor, exteriorPower_fin, exteriorPower_fin, ← compound_map,
    ← compound_map, hdual, compound_mulVec_plucker, compound_mulVec_plucker]
  refine (iSup_congr hrel).trans ?_
  rw [← Real.mul_iSup_of_nonneg (by positivity),
    ← (Set.powersetCard.compl hlk).iSup_comp (g := fun t ↦
      w (plucker l (fun j ↦ M⁻¹ᵀ *ᵥ (D.submatrix Sum.inr id).row j) t))]
  ring_nf

/-- **Twisted duality relative to a number field**: the twisted height of `V` is the twisted
height of `V^⊥` for the dual twist, times the local determinants of `A`. -/
theorem mulHeight_plucker_inl :
    (A.exteriorPower k).mulHeight (plucker k (C.submatrix Sum.inl id).row) =
      ((∏ φ : E →+* ℂ, ‖(A.arch (φ.comp (algebraMap K E))).det‖) *
        ∏ᶠ w : FinitePlace E, w ((A.fin (w.under K)).map (algebraMap K E)).det) *
      (A.dual.exteriorPower l).mulHeight (plucker l (D.submatrix Sum.inr id).row) := by
  have hc : (C.submatrix id e).det ≠ 0 :=
    (Matrix.isUnit_det_submatrix_of_mul_transpose_eq_one hCD e).ne_zero
  have hDC : D * Cᵀ = 1 := by
    have h := congrArg Matrix.transpose hCD
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h
  have hq : plucker l (D.submatrix Sum.inr id).row ≠ 0 :=
    plucker_ne_zero ((Matrix.linearIndependent_row_of_mul_transpose_eq_one hDC).comp _
      Sum.inr_injective)
  have hcq : (C.submatrix id e).det • plucker l (D.submatrix Sum.inr id).row ≠ 0 :=
    smul_ne_zero hc hq
  have hdet : (fun w : FinitePlace E ↦
      w ((A.fin (w.under K)).map (algebraMap K E)).det).HasFiniteMulSupport :=
    (A.baseChange E).finite_setOf_fin_ne_one.subset fun w hw h ↦ hw (by
      simp only [baseChange_fin] at h
      simp [h])
  rw [← (A.dual.exteriorPower l).mulHeight_smul _ hc, mulHeight, mulHeight]
  simp_rw [A.archFactor_plucker_inl C D hCD hlk e, A.finFactor_plucker_inl C D hCD hlk e]
  rw [prod_mul_distrib,
    finprod_mul_distrib hdet ((A.dual.exteriorPower l).hasFiniteMulSupport_finFactor hcq)]
  ring

end Local

/-! ### The duality theorem -/

section Absolute

variable {ι : Type*} [Fintype ι] [LinearOrder ι] (A : Twist K ι)
  {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

/-- **Twisted duality** (RT96 Theorem 1.1, in product form): the height of a subspace is
`|det A|_𝔸` times the height of its orthogonal complement for the dual twist. -/
theorem absSubspaceHeight_eq_absDet_mul (V : Submodule Ω (ι → Ω)) :
    A.absSubspaceHeight V = A.absDet *
      A.dual.absSubspaceHeight (V.dualAnnihilator.comap (Module.piEquiv ι Ω Ω).toLinearMap) := by
  obtain ⟨k, hk⟩ : ∃ k, finrank Ω V = k := ⟨_, rfl⟩
  have hle : k ≤ Fintype.card ι := by
    have h := V.finrank_le
    rwa [Module.finrank_pi, hk] at h
  obtain ⟨l, hlk⟩ : ∃ l, l + k = Fintype.card ι := ⟨Fintype.card ι - k, by omega⟩
  obtain ⟨C, D, hCD, hV⟩ := Submodule.exists_dual_matrices V hk hlk
  have hW := Submodule.span_range_inr_row_eq hCD hlk hV
  have hcard : Fintype.card (Fin k ⊕ Fin l) = Fintype.card ι := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨e⟩ := Fintype.truncEquivOfCardEq hcard
  have hDC : D * Cᵀ = 1 := by
    have h := congrArg Matrix.transpose hCD
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h
  have hCli : LinearIndependent Ω (C.submatrix Sum.inl id).row :=
    (Matrix.linearIndependent_row_of_mul_transpose_eq_one hCD).comp _ Sum.inl_injective
  have hDli : LinearIndependent Ω (D.submatrix Sum.inr id).row :=
    (Matrix.linearIndependent_row_of_mul_transpose_eq_one hDC).comp _ Sum.inr_injective
  -- A number field containing all the entries.
  set g : ((Fin k ⊕ Fin l) × ι) ⊕ ((Fin k ⊕ Fin l) × ι) → Ω :=
    Sum.elim (fun p ↦ C p.1 p.2) (fun p ↦ D p.1 p.2)
  have := numberField_adjoin_range (K := K) g
  set F := adjoin K (Set.range g)
  set CF : Matrix (Fin k ⊕ Fin l) ι F := Matrix.of fun r i ↦
    ⟨C r i, subset_adjoin K _ ⟨Sum.inl (r, i), rfl⟩⟩
  set DF : Matrix (Fin k ⊕ Fin l) ι F := Matrix.of fun r i ↦
    ⟨D r i, subset_adjoin K _ ⟨Sum.inr (r, i), rfl⟩⟩
  have hCDF : CF * DFᵀ = 1 := by
    refine Matrix.map_injective (f := ((F.val : F →+* Ω) : F → Ω)) Subtype.val_injective ?_
    beta_reduce
    rw [Matrix.map_mul, transpose_map, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hCD
  have hCp : plucker k (C.submatrix Sum.inl id).row =
      F.val ∘ plucker k (CF.submatrix Sum.inl id).row :=
    plucker_comp_ringHom (F.val : F →+* Ω) k (CF.submatrix Sum.inl id).row
  have hDp : plucker l (D.submatrix Sum.inr id).row =
      F.val ∘ plucker l (DF.submatrix Sum.inr id).row :=
    plucker_comp_ringHom (F.val : F →+* Ω) l (DF.submatrix Sum.inr id).row
  have h1 : A.absSubspaceHeight V = (A.exteriorPower k).mulHeight
      (plucker k (CF.submatrix Sum.inl id).row) ^ ((finrank ℚ F : ℝ))⁻¹ := by
    rw [← hV, absSubspaceHeight_span_range _ hCli, hCp, absMulHeight_algHom]
  have h2 : A.dual.absSubspaceHeight
      (V.dualAnnihilator.comap (Module.piEquiv ι Ω Ω).toLinearMap) =
      (A.dual.exteriorPower l).mulHeight
        (plucker l (DF.submatrix Sum.inr id).row) ^ ((finrank ℚ F : ℝ))⁻¹ := by
    rw [← hW, absSubspaceHeight_span_range _ hDli, hDp, absMulHeight_algHom]
  have h3 : A.absDet = ((∏ φ : F →+* ℂ, ‖(A.arch (φ.comp (algebraMap K F))).det‖) *
      ∏ᶠ w : FinitePlace F, w ((A.fin (w.under K)).map (algebraMap K F)).det) ^
        ((finrank ℚ F : ℝ))⁻¹ := by
    rw [← A.absDet_baseChange F]
    rfl
  rw [h1, h2, h3, A.mulHeight_plucker_inl CF DF hCDF hlk e, Real.mul_rpow (mul_nonneg
    (prod_nonneg fun _ _ ↦ norm_nonneg _) (finprod_nonneg fun _ ↦ apply_nonneg _ _))
    ((A.dual.exteriorPower l).mulHeight_nonneg _)]

/-- **The duality theorem for twisted heights** (RT96 Theorem 1.1):
`H_{A*}(V^⊥) = |det A|_𝔸⁻¹ · H_A(V)`. -/
theorem absSubspaceHeight_dual (V : Submodule Ω (ι → Ω)) :
    A.dual.absSubspaceHeight (V.dualAnnihilator.comap (Module.piEquiv ι Ω Ω).toLinearMap) =
      A.absDet⁻¹ * A.absSubspaceHeight V := by
  rw [A.absSubspaceHeight_eq_absDet_mul V, inv_mul_cancel_left₀ A.absDet_pos.ne']

end Absolute

end NumberField.Twist
