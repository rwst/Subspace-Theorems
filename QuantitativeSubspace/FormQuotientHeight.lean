/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormMinorRatio

/-!
# The system induced on the quotient by the exceptional subspace

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, Lemmas 18.2–18.4.

The system `L''` induced on `Ωⁿ / T` (`FormSystem.quotSystem`, Q3.5) has the forms
`L_i - Σ_{j ∈ I_v} α_ijv L_j`, `i ∉ I_v(T)`. By Cramer's rule each `α_ijv` is a quotient of two
minors `θ` of EF13 (18.1), so `‖α_ijv‖_v ≤ M_v / m_v` (EF13 (18.7)), and Lemma 18.1 makes the
constants of EF13 Lemma 16.3 (ii) explicit.

EF13 normalizes coordinates (18.8), (18.9) and passes through the full system of forms (18.4). Here
the splitting `P` of Q3.5 is arbitrary, and Lemma 18.4 comes from a block determinant instead:
for `m` forms `ℓ'_t` vanishing on `T` and a fixed `k`-tuple `B₀` of forms independent on `T`,
`det(ℓ' φ'') det(B₀ φ') = det(ℓ', B₀) det P'` (`det_mul_det_eq`), and `det(ℓ', B₀)` expands into
`(k + 1)^n` determinants of `n` forms of `L` with coefficients at most `(M_v / m_v)^n`. The factor
`det P' / det(B₀ φ')` disappears by the product formula.

## Main results

* `NumberField.FormSystem.apply_quotCoeff_le`: EF13 (18.7).
* `NumberField.FormSystem.absMulHeight_quotSystem_le`,
  `absMulHeight_quotSystem_le_of_isWeightFiltration`: EF13 (18.5),
  `H_{L'',c'',Q}(φ'' x) ≤ n (2 H_L)^{(4R)ⁿ} H_{L,c,Q}(x)`.
* `NumberField.FormSystem.card_forms_quotSystem_le`: EF13 (18.15), `L''` has at most
  `R^{k+1}` forms.
* `NumberField.FormSystem.sum_iSup_quotNormExp_le`, `subspaceWeight_quotNormExp_nonpos`: EF13
  (18.14) and (18.16) for the normalized exponents `d` of (18.12) (`quotNormExp`).
* `NumberField.FormSystem.mulFormHeight_quotSystem_le`, `absFormHeight_quotSystem_le_of_ratio`,
  `absFormHeight_quotSystem_le`: EF13 Lemma 18.4, `H_{L''} ≤ (2 H_L)^{(8R)ⁿ}`.

This is milestone Q3.7 of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Module Finset Matrix

namespace NumberField.FormSystem

variable {K : Type*} [Field K] [NumberField K] {n k m : ℕ} (L : FormSystem K (Fin n))

/-! ### The coefficients `α_ij` by Cramer's rule (EF13 (18.7)) -/

section Cramer

variable {G : Matrix (Fin n) (Fin k) K}

/-- The coordinates `β` of `ℓ|_T` in the basis `B_1|_T, …, B_k|_T`, `T` spanned by the columns of
`G`: `ℓ G = β (B G)`. -/
noncomputable def cramerCoeff (G : Matrix (Fin n) (Fin k) K) (ℓ : Fin n → K)
    (B : Fin k → Fin n → K) : Fin k → K :=
  (ℓ ᵥ* G) ᵥ* (Matrix.of B * G)⁻¹

omit [NumberField K] in
theorem vecMul_cramerCoeff {ℓ : Fin n → K} {B : Fin k → Fin n → K}
    (hB : (Matrix.of B * G).det ≠ 0) : cramerCoeff G ℓ B ᵥ* (Matrix.of B * G) = ℓ ᵥ* G := by
  rw [cramerCoeff, vecMul_vecMul, nonsing_inv_mul _ (Ne.isUnit hB), vecMul_one]

omit [NumberField K] in
/-- **Cramer's rule**: `β_s det(B G) = det(B' G)`, `B'` the tuple `B` with `ℓ` in place `s`. -/
theorem det_update_eq {ℓ : Fin n → K} {B : Fin k → Fin n → K} (hB : (Matrix.of B * G).det ≠ 0)
    (s : Fin k) :
    (Matrix.of (Function.update B s ℓ) * G).det = cramerCoeff G ℓ B s * (Matrix.of B * G).det := by
  set M := Matrix.of B * G
  have hrow : Matrix.of (Function.update B s ℓ) * G =
      M.updateRow s (∑ t, cramerCoeff G ℓ B t • M t) := by
    ext i j
    by_cases hi : i = s
    · subst hi
      have h := congrFun (vecMul_cramerCoeff (ℓ := ℓ) hB) j
      simp only [vecMul, dotProduct] at h
      simp only [updateRow_self, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, M]
      rw [h]
      simp [Matrix.mul_apply]
    · simp [updateRow_ne hi, Function.update_of_ne hi, M, Matrix.mul_apply]
  rw [hrow, det_updateRow_sum, smul_eq_mul]

theorem apply_cramerCoeff_le (f : AbsoluteValue K ℝ) {ℓ : Fin n → K} (hℓ : ℓ ∈ L.forms)
    {B : Fin k → Fin n → K} (hB : ∀ s, B s ∈ L.forms) (hdet : (Matrix.of B * G).det ≠ 0)
    (s : Fin k) : f (cramerCoeff G ℓ B s) ≤ localRatio (L.minorSet G) f := by
  classical
  have hB' : ∀ t, Function.update B s ℓ t ∈ L.forms := fun t ↦ by
    by_cases ht : t = s
    · subst ht
      simpa using hℓ
    · simpa [Function.update_of_ne ht] using hB t
  have hcoef : cramerCoeff G ℓ B s =
      (Matrix.of (Function.update B s ℓ) * G).det / (Matrix.of B * G).det := by
    rw [det_update_eq hdet, mul_div_cancel_right₀ _ hdet]
  rw [hcoef, map_div₀]
  by_cases h0 : (Matrix.of (Function.update B s ℓ) * G).det = 0
  · rw [h0, map_zero, zero_div]
    exact localRatio_nonneg f
  · exact div_le_localRatio L.zero_notMem_minorSet f (L.det_mem_minorSet hB' h0)
      (L.det_mem_minorSet hB hdet)

end Cramer

/-! ### The matrices `M_v` of `L'' φ'' = M_v L` (EF13 (18.4), (18.7)) -/

section Splitting

variable (S : Splitting K n k m) {A : Matrix (Fin n) (Fin n) K} (c : Fin n → ℝ)

omit [NumberField K] in
theorem linearIndependent_incl : LinearIndependent K S.incl.col := by
  rw [← Matrix.mulVec_injective_iff]
  intro x y h
  have := congrArg (S.coproj *ᵥ ·) h
  simpa [mulVec_mulVec, S.coproj_mul_incl] using this

omit [NumberField K] in
theorem restrictMat_eq : S.restrictMat A c = Matrix.of (fun s ↦ A (S.sel A c s)) * S.incl := by
  rw [Splitting.restrictMat, Splitting.submatrix_mul_left]
  rfl

omit [NumberField K] in
theorem coeffMat_row (i : Fin n) :
    S.coeffMat A c i = cramerCoeff S.incl (A i) fun s ↦ A (S.sel A c s) := by
  rw [cramerCoeff, ← restrictMat_eq]
  rfl

theorem apply_coeffMat_le (hA : A.det ≠ 0) (hAf : ∀ i, A i ∈ L.forms) (f : AbsoluteValue K ℝ)
    (i : Fin n) (s : Fin k) : f (S.coeffMat A c i s) ≤ localRatio (L.minorSet S.incl) f := by
  rw [coeffMat_row]
  exact L.apply_cramerCoeff_le f (hAf i) (fun _ ↦ hAf _)
    (restrictMat_eq S c ▸ S.restrictMat_det_ne_zero c hA) s

/-- The entries of `M_v` are at most `M_v / m_v` (EF13 (18.7)). -/
theorem apply_quotCoeff_le (hA : A.det ≠ 0) (hAf : ∀ i, A i ∈ L.forms) (f : AbsoluteValue K ℝ)
    (t : Fin m) (i : Fin n) : f (S.quotCoeff A c t i) ≤ localRatio (L.minorSet S.incl) f := by
  classical
  have h1 : 1 ≤ localRatio (L.minorSet S.incl) f :=
    one_le_localRatio (L.minorSet_nonempty (linearIndependent_incl S)) L.zero_notMem_minorSet f
  have hsel : ∀ {p : ℕ} (σ : Fin p ↪ Fin n) (s : Fin p) (i : Fin n),
      Splitting.selMat (K := K) σ s i = (1 : Matrix (Fin n) (Fin n) K) (σ s) i :=
    fun _ _ _ ↦ rfl
  simp only [Splitting.quotCoeff, Matrix.sub_apply, Matrix.mul_apply, submatrix_apply, id_eq,
    hsel]
  by_cases hi : i ∈ Set.range (S.sel A c)
  · obtain ⟨s₀, rfl⟩ := hi
    have hsum : ∑ s, S.coeffMat A c (S.compSel A c t) s *
        (1 : Matrix (Fin n) (Fin n) K) (S.sel A c s) (S.sel A c s₀) =
          S.coeffMat A c (S.compSel A c t) s₀ := by
      rw [sum_eq_single s₀ (fun s _ hs ↦ by
        rw [one_apply_ne ((S.sel A c).injective.ne hs), mul_zero]) (by simp), one_apply_eq,
        mul_one]
    rw [hsum, one_apply_ne (S.sel_ne_compSel A c s₀ t).symm, zero_sub, AbsoluteValue.map_neg]
    exact L.apply_coeffMat_le S c hA hAf f _ _
  · have hsum : ∑ s, S.coeffMat A c (S.compSel A c t) s *
        (1 : Matrix (Fin n) (Fin n) K) (S.sel A c s) i = 0 :=
      sum_eq_zero fun s _ ↦ by rw [one_apply_ne fun h ↦ hi ⟨s, h⟩, mul_zero]
    rw [hsum, sub_zero]
    refine le_trans ?_ h1
    by_cases h : S.compSel A c t = i
    · rw [h, one_apply_eq, map_one]
    · rw [one_apply_ne h, map_zero]
      exact zero_le_one

end Splitting

/-! ### EF13 Lemma 18.2: the height on the quotient -/

section Lemma182

variable (S : Splitting K n k m) (c : FormExponent K (Fin n))

theorem hasFiniteMulSupport_localRatio_minorSet :
    (fun v : FinitePlace K ↦ localRatio (L.minorSet S.incl) fun x ↦ v x).HasFiniteMulSupport :=
  hasFiniteMulSupport_localRatio (L.minorSet_nonempty (linearIndependent_incl S))
    L.zero_notMem_minorSet

/-- **EF13 (18.5)**, with the explicit constant of Lemma 18.2:
`H_{L'',c'',Q}(φ'' x) ≤ n (∏_v M_v / m_v)^{1/[K:ℚ]} H_{L,c,Q}(x)` for `Q ≥ 1`. With Lemma 18.1
the constant is at most `n (2 H_L)^{(4R)ⁿ}`. -/
theorem absMulHeight_quotSystem_le {Ω : Type*} [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] {Q : ℝ} (hQ : 1 ≤ Q) (x : Fin n → Ω) :
    (L.quotSystem S c).absMulHeight ((L.quotExp S c).weight (zero_lt_one.trans_le hQ))
        (S.projLin Ω x) ≤
      n * mulRatioProd (L.minorSet S.incl) ^ ((finrank ℚ K : ℝ))⁻¹ *
        L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x := by
  have hne := L.minorSet_nonempty (linearIndependent_incl S)
  have h := absMulHeight_le_of_mul_eq (L₂ := L.quotSystem S c) (L₁ := L)
    (a₂ := (L.quotExp S c).weight (zero_lt_one.trans_le hQ))
    (a₁ := c.weight (zero_lt_one.trans_le hQ)) (Φ₂ := S.proj) (Φ₁ := 1)
    (Ma := fun v ↦ S.quotCoeff (L.arch v) (c.arch v))
    (Mf := fun v ↦ S.quotCoeff (L.fin v) (c.fin v))
    (B := fun v ↦ localRatio (L.minorSet S.incl) fun x ↦ v x)
    (B' := fun v ↦ localRatio (L.minorSet S.incl) fun x ↦ v x)
    (fun v ↦ by rw [Matrix.mul_one]; exact (S.quotCoeff_mul _ (L.arch_det_ne_zero v)).symm)
    (fun v ↦ by rw [Matrix.mul_one]; exact (S.quotCoeff_mul _ (L.fin_det_ne_zero v)).symm)
    (fun v i j hij ↦ weight_arch_le hQ (S.le_of_quotCoeff_ne_zero _ (L.arch_det_ne_zero v) hij))
    (fun v i j hij ↦ weight_fin_le hQ (S.le_of_quotCoeff_ne_zero _ (L.fin_det_ne_zero v) hij))
    (fun v ↦ zero_lt_one.trans_le (one_le_localRatio hne L.zero_notMem_minorSet v.1))
    (fun v ↦ zero_lt_one.trans_le (one_le_localRatio hne L.zero_notMem_minorSet v.1))
    (fun v i j ↦ L.apply_quotCoeff_le S _ (L.arch_det_ne_zero v) (L.arch_mem_forms v) v.1 i j)
    (fun v i j ↦ L.apply_quotCoeff_le S _ (L.fin_det_ne_zero v) (L.fin_mem_forms v) v.1 i j)
    (L.hasFiniteMulSupport_localRatio_minorSet S) x
  rwa [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec, Fintype.card_fin] at h

end Lemma182

/-! ### EF13 (18.15): the forms of `L''` -/

section Count

variable (S : Splitting K n k m)

/-- The form `L''` coming from the form `ℓ` and the basis `B` of the forms on `T`:
`(ℓ - Σ_s β_s B_s) φ'`, `β = cramerCoeff`, read on `Ωⁿ / T` through the complement. -/
noncomputable def quotRow (ℓ : Fin n → K) (B : Fin k → Fin n → K) : Fin m → K :=
  (ℓ - cramerCoeff S.incl ℓ B ᵥ* Matrix.of B) ᵥ* S.compl

omit [NumberField K] in
theorem quotMat_row (A : Matrix (Fin n) (Fin n) K) (c : Fin n → ℝ) (t : Fin m) :
    S.quotMat A c t = quotRow S (A (S.compSel A c t)) fun s ↦ A (S.sel A c s) := by
  rw [quotRow, sub_vecMul, vecMul_vecMul, ← coeffMat_row]
  rfl

theorem exists_of_mem_forms_quotSystem (c : FormExponent K (Fin n)) {f : Fin m → K}
    (hf : f ∈ (L.quotSystem S c).forms) :
    ∃ ℓ ∈ L.forms, ∃ B : Fin k → Fin n → K, (∀ s, B s ∈ L.forms) ∧
      (Matrix.of B * S.incl).det ≠ 0 ∧ f = quotRow S ℓ B := by
  rcases (L.quotSystem S c).finite_formSet.mem_toFinset.1 hf with ⟨v, t, rfl⟩ | ⟨v, t, rfl⟩
  · refine ⟨_, L.arch_mem_forms v _, _, fun s ↦ L.arch_mem_forms v _, ?_, quotMat_row S _ _ t⟩
    rw [← restrictMat_eq]
    exact S.restrictMat_det_ne_zero _ (L.arch_det_ne_zero v)
  · refine ⟨_, L.fin_mem_forms v _, _, fun s ↦ L.fin_mem_forms v _, ?_, quotMat_row S _ _ t⟩
    rw [← restrictMat_eq]
    exact S.restrictMat_det_ne_zero _ (L.fin_det_ne_zero v)

/-- **EF13 (18.15)**, sharpened: `L''` has at most `R^{k+1} ≤ Rⁿ` distinct forms (EF13: `n Rⁿ`),
`R` the number of forms of `L`. A form of `L''` is determined by a form of `L` and a `k`-tuple of
forms of `L`. -/
theorem card_forms_quotSystem_le (c : FormExponent K (Fin n)) :
    #(L.quotSystem S c).forms ≤ #L.forms ^ (k + 1) := by
  classical
  have hsub : (L.quotSystem S c).forms ⊆ (L.forms ×ˢ Fintype.piFinset fun _ : Fin k ↦ L.forms).image
      fun p ↦ quotRow S p.1 p.2 := fun f hf ↦ by
    obtain ⟨ℓ, hℓ, B, hB, -, rfl⟩ := L.exists_of_mem_forms_quotSystem S c hf
    exact mem_image.2 ⟨(ℓ, B), mem_product.2 ⟨hℓ, Fintype.mem_piFinset.2 hB⟩, rfl⟩
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  rw [card_product, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, pow_succ']

end Count

/-! ### EF13 Lemma 18.4: the height of `L''` -/

section Lemma184

variable (S : Splitting K n k m)

omit [NumberField K] in
/-- The form `ℓ - Σ_s β_s B_s` vanishes on `T`. -/
theorem vecMul_incl_eq_zero {ℓ : Fin n → K} {B : Fin k → Fin n → K}
    (hB : (Matrix.of B * S.incl).det ≠ 0) :
    (ℓ - cramerCoeff S.incl ℓ B ᵥ* Matrix.of B) ᵥ* S.incl = 0 := by
  rw [sub_vecMul, vecMul_vecMul, vecMul_cramerCoeff hB, sub_self]

/-- The index equivalence `Fin m ⊕ Fin k ≃ Fin n`. -/
def sumEquiv : Fin m ⊕ Fin k ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (by have := S.card_eq; omega))

omit [NumberField K] in
theorem det_submatrix_P_ne_zero :
    (S.P.submatrix (sumEquiv S) (Equiv.sumComm (Fin m) (Fin k))).det ≠ 0 := by
  have h : S.P.submatrix (sumEquiv S) (Equiv.sumComm (Fin m) (Fin k)) *
      S.Q.submatrix (Equiv.sumComm (Fin m) (Fin k)) (sumEquiv S) = 1 := by
    rw [submatrix_mul_equiv, S.P_mul_Q, submatrix_one_equiv]
  intro h0
  have := congrArg det h
  rw [det_mul, h0, zero_mul, det_one] at this
  exact zero_ne_one this

omit [NumberField K] in
/-- **The block determinant behind EF13 Lemma 18.4**: for forms `ℓ'_t` vanishing on `T` and `k`
forms `B₀`, `det(ℓ' φ'') det(B₀ φ') = det(ℓ', B₀) det P'`, `P'` the matrix `P` with permuted rows
and columns. -/
theorem det_mul_det_eq (ℓ' : Fin m → Fin n → K) (h : ∀ t, ℓ' t ᵥ* S.incl = 0)
    (B₀ : Fin k → Fin n → K) :
    (Matrix.of fun t ↦ ℓ' t ᵥ* S.compl).det * (Matrix.of B₀ * S.incl).det =
      (Matrix.of fun i ↦ Sum.elim ℓ' B₀ ((sumEquiv S).symm i)).det *
        (S.P.submatrix (sumEquiv S) (Equiv.sumComm (Fin m) (Fin k))).det := by
  set e := sumEquiv S
  set N₀ : Matrix (Fin m ⊕ Fin k) (Fin n) K := Matrix.of (Sum.elim ℓ' B₀)
  set P₁ := S.P.submatrix id (Equiv.sumComm (Fin m) (Fin k))
  have hX : N₀ * P₁ = fromBlocks (Matrix.of fun t ↦ ℓ' t ᵥ* S.compl) 0
      (Matrix.of B₀ * S.compl) (Matrix.of B₀ * S.incl) := by
    ext (t | s) (t' | s')
    · simp [N₀, P₁, Matrix.mul_apply, vecMul, dotProduct, Splitting.compl]
    · have := congrFun (h t) s'
      simpa [N₀, P₁, Matrix.mul_apply, vecMul, dotProduct, Splitting.incl] using this
    · simp [N₀, P₁, Matrix.mul_apply, Splitting.compl]
    · simp [N₀, P₁, Matrix.mul_apply, Splitting.incl]
  have hsplit : N₀ * P₁ = N₀.submatrix id e * P₁.submatrix e id := by
    rw [submatrix_mul_equiv, submatrix_id_id]
  have hN : N₀.submatrix id e = (Matrix.of fun i ↦ Sum.elim ℓ' B₀ (e.symm i)).submatrix e e := by
    ext a b
    simp [N₀]
  rw [← det_fromBlocks_zero₁₂, ← hX, hsplit, det_mul, hN, det_submatrix_equiv_self]
  rfl

omit [NumberField K] in
/-- The multilinear expansion of a determinant whose rows are combinations of other rows. -/
theorem det_sum_smul {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] (γ : ι → α → K)
    (ψ : ι → α → ι → K) :
    (Matrix.of fun i ↦ ∑ a, γ i a • ψ i a).det =
      ∑ r : ι → α, (∏ i, γ i (r i)) * (Matrix.of fun i ↦ ψ i (r i)).det := by
  have h := (Matrix.detRowAlternating (n := ι) (R := K)).toMultilinearMap.map_sum
    (fun i a ↦ γ i a • ψ i a)
  refine h.trans (sum_congr rfl fun r _ ↦ ?_)
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

open scoped Classical in
/-- **The determinants of `L''`** (proof of EF13 Lemma 18.4): with `κ = det P' / det(B₀ φ')` for a
fixed `k`-tuple `B₀` of forms independent on `T`, every determinant of `m` forms of `L''` is
`κ Σ_r x_r d_r` with `d_r` determinants of `n` forms of `L` and `‖x_r‖ ≤ (M/m)^n` at every place,
over `(k + 1)^n` indices `r`. -/
theorem exists_detSet_quotSystem (c : FormExponent K (Fin n)) :
    ∃ κ : K, κ ≠ 0 ∧ ∀ e ∈ (L.quotSystem S c).detSet,
      ∃ x d : (Fin n → Option (Fin k)) → K, (∀ r, d r ∈ L.detSet) ∧
        (∀ (f : AbsoluteValue K ℝ) r, f (x r) ≤ localRatio (L.minorSet S.incl) f ^ n) ∧
        e = (∑ r, x r * d r) * κ := by
  obtain ⟨θ₀, hθ₀⟩ := L.minorSet_nonempty (linearIndependent_incl S)
  obtain ⟨B₀, hB₀, hθB⟩ := L.exists_of_mem_minorSet hθ₀
  have hθ0 : θ₀ ≠ 0 := fun h ↦ L.zero_notMem_minorSet (h ▸ hθ₀)
  set D := (S.P.submatrix (sumEquiv S) (Equiv.sumComm (Fin m) (Fin k))).det
  refine ⟨D / θ₀, div_ne_zero (det_submatrix_P_ne_zero S) hθ0, fun e he ↦ ?_⟩
  obtain ⟨F, hF, rfl⟩ := mem_image.1 he
  have hF' : ∀ t, ∃ ℓ ∈ L.forms, ∃ B : Fin k → Fin n → K, (∀ s, B s ∈ L.forms) ∧
      (Matrix.of B * S.incl).det ≠ 0 ∧ F t = quotRow S ℓ B := fun t ↦
    L.exists_of_mem_forms_quotSystem S c (Fintype.mem_piFinset.1 hF t)
  choose ℓ hℓ B hB hBdet hFt using hF'
  set β : Fin m → Fin k → K := fun t ↦ cramerCoeff S.incl (ℓ t) (B t)
  set ℓ' : Fin m → Fin n → K := fun t ↦ ℓ t - β t ᵥ* Matrix.of (B t)
  have hF'' : Matrix.of F = Matrix.of fun t ↦ ℓ' t ᵥ* S.compl := by
    ext t j
    rw [of_apply, hFt t]
    rfl
  have hkey := det_mul_det_eq S ℓ' (fun t ↦ vecMul_incl_eq_zero S (hBdet t)) B₀
  rw [hθB, ← hF''] at hkey
  set ε := (sumEquiv S).symm
  set γ : Fin m ⊕ Fin k → Option (Fin k) → K := Sum.elim
    (fun t a ↦ Option.elim a 1 fun s ↦ -β t s) (fun _ a ↦ Option.elim a 1 fun _ ↦ 0)
  set ψ : Fin m ⊕ Fin k → Option (Fin k) → Fin n → K := Sum.elim
    (fun t a ↦ Option.elim a (ℓ t) fun s ↦ B t s) (fun s₀ _ ↦ B₀ s₀)
  have hsum : ∀ x, Sum.elim ℓ' B₀ x = ∑ a, γ x a • ψ x a := by
    rintro (t | s₀)
    · simp only [γ, ψ, ℓ', Sum.elim_inl, Fintype.sum_option, Option.elim, one_smul, neg_smul,
        sum_neg_distrib, vecMul_eq_sum, sub_eq_add_neg]
      rfl
    · simp [γ, ψ]
  have hdet : (Matrix.of fun i ↦ Sum.elim ℓ' B₀ (ε i)).det =
      ∑ r : Fin n → Option (Fin k), (∏ i, γ (ε i) (r i)) *
        (Matrix.of fun i ↦ ψ (ε i) (r i)).det := by
    rw [show (fun i ↦ Sum.elim ℓ' B₀ (ε i)) = fun i ↦ ∑ a, γ (ε i) a • ψ (ε i) a from
      funext fun i ↦ hsum _]
    exact det_sum_smul _ _
  have hψ : ∀ x a, ψ x a ∈ L.forms := by
    rintro (t | s₀) (_ | s)
    · exact hℓ t
    · exact hB t s
    · exact hB₀ s₀
    · exact hB₀ s₀
  have hγ : ∀ (f : AbsoluteValue K ℝ) x a, f (γ x a) ≤ localRatio (L.minorSet S.incl) f := by
    intro f x a
    have h1 : 1 ≤ localRatio (L.minorSet S.incl) f :=
      one_le_localRatio ⟨θ₀, hθ₀⟩ L.zero_notMem_minorSet f
    rcases x with t | s₀ <;> rcases a with _ | s
    · simpa [γ] using h1
    · simp only [γ, Sum.elim_inl, Option.elim, AbsoluteValue.map_neg]
      exact L.apply_cramerCoeff_le f (hℓ t) (hB t) (hBdet t) s
    · simpa [γ] using h1
    · simpa [γ] using zero_le_one.trans h1
  refine ⟨fun r ↦ ∏ i, γ (ε i) (r i), fun r ↦ (Matrix.of fun i ↦ ψ (ε i) (r i)).det,
    fun r ↦ mem_image.2 ⟨_, Fintype.mem_piFinset.2 fun i ↦ hψ _ _, rfl⟩, fun f r ↦ ?_, ?_⟩
  · rw [map_prod]
    calc ∏ i, f (γ (ε i) (r i)) ≤ ∏ _i : Fin n, localRatio (L.minorSet S.incl) f :=
          prod_le_prod₀ (fun _ _ ↦ apply_nonneg _ _) fun i _ ↦ hγ f _ _
      _ = _ := by rw [prod_const, card_univ, Fintype.card_fin]
  · rw [← hdet, mul_div_assoc', eq_div_iff hθ0, hkey]

/-- **EF13 Lemma 18.4**, relative to `K`:
`H_{L''} ≤ (k + 1)^{n [K:ℚ]} (∏_v M_v / m_v)^n H_L`. With Lemma 18.1 this is at most
`(2 H_L)^{(8R)ⁿ}` after the `[K:ℚ]`-th root (`absFormHeight_quotSystem_le`). -/
theorem mulFormHeight_quotSystem_le (c : FormExponent K (Fin n)) :
    (L.quotSystem S c).mulFormHeight ≤
      (((k + 1) ^ n : ℕ) : ℝ) ^ finrank ℚ K * mulRatioProd (L.minorSet S.incl) ^ n *
        L.mulFormHeight := by
  classical
  obtain ⟨κ, hκ, hdet⟩ := L.exists_detSet_quotSystem S c
  have hne := L.minorSet_nonempty (linearIndependent_incl S)
  set N : ℝ := (((k + 1) ^ n : ℕ) : ℝ)
  have hN : Fintype.card (Fin n → Option (Fin k)) = (k + 1) ^ n := by simp
  have harch : ∀ f : AbsoluteValue K ℝ, (⨆ e : (L.quotSystem S c).detSet, f e) ≤
      N * localRatio (L.minorSet S.incl) f ^ n * (⨆ e : L.detSet, f e) * f κ := fun f ↦ by
    have hρ := localRatio_nonneg (s := L.minorSet S.incl) f
    have hD := L.iSup_detSet_nonneg f
    refine Real.iSup_le (fun e ↦ ?_) (by positivity)
    obtain ⟨x, d, hd, hx, he⟩ := hdet e e.2
    rw [he, map_mul]
    refine mul_le_mul_of_nonneg_right ?_ (apply_nonneg _ _)
    calc f (∑ r, x r * d r) ≤ ∑ r, f (x r * d r) := AbsoluteValue.sum_le _ _ _
      _ ≤ ∑ _r : Fin n → Option (Fin k),
            localRatio (L.minorSet S.incl) f ^ n * ⨆ e : L.detSet, f e :=
          sum_le_sum fun r _ ↦ by
            rw [map_mul]
            exact mul_le_mul (hx f r) (L.le_iSup_detSet _ (hd r)) (apply_nonneg _ _)
              (pow_nonneg hρ _)
      _ = _ := by rw [sum_const, card_univ, hN, nsmul_eq_mul, mul_assoc]
  have hfin : ∀ v : FinitePlace K, (⨆ e : (L.quotSystem S c).detSet, v e) ≤
      localRatio (L.minorSet S.incl) (fun x ↦ v x) ^ n * (⨆ e : L.detSet, v e) * v κ :=
    fun v ↦ by
    have hρ := localRatio_nonneg (s := L.minorSet S.incl) v.1
    have hD : 0 ≤ ⨆ e : L.detSet, v e := L.iSup_detSet_nonneg v.1
    refine Real.iSup_le (fun e ↦ ?_) (by positivity)
    obtain ⟨x, d, hd, hx, he⟩ := hdet e e.2
    rw [he, map_mul]
    refine mul_le_mul_of_nonneg_right ?_ (apply_nonneg _ _)
    have hna : IsNonarchimedean (v ·) := FinitePlace.add_le v
    obtain ⟨r, -, hr⟩ := hna.finset_image_add_of_nonempty (fun r ↦ x r * d r) univ_nonempty
    refine hr.trans ?_
    rw [map_mul]
    exact mul_le_mul (hx v.1 r) (L.le_iSup_detSet _ (hd r)) (apply_nonneg _ _) (pow_nonneg hρ _)
  have hρf := L.hasFiniteMulSupport_localRatio_minorSet S
  have hρnf : (fun v : FinitePlace K ↦
      localRatio (L.minorSet S.incl) (fun x ↦ v x) ^ n).HasFiniteMulSupport :=
    hρf.subset fun v hv h ↦ hv (by simp only [h, one_pow])
  have hDf := L.hasFiniteMulSupport_iSup_detSet
  have hκf := FinitePlace.hasFiniteMulSupport hκ
  have hρD := (hρnf.union hDf).subset (Function.mulSupport_mul _ _)
  have h := prod_places_le
    (f := fun v : InfinitePlace K ↦ ⨆ e : (L.quotSystem S c).detSet, v e)
    (g := fun v : InfinitePlace K ↦
      N * localRatio (L.minorSet S.incl) (fun x ↦ v x) ^ n * (⨆ e : L.detSet, v e) * v κ)
    (f' := fun v : FinitePlace K ↦ ⨆ e : (L.quotSystem S c).detSet, v e)
    (g' := fun v : FinitePlace K ↦
      localRatio (L.minorSet S.incl) (fun x ↦ v x) ^ n * (⨆ e : L.detSet, v e) * v κ)
    (fun v ↦ (L.quotSystem S c).iSup_detSet_nonneg v.1)
    (fun v ↦ (L.quotSystem S c).iSup_detSet_nonneg v.1)
    (L.quotSystem S c).hasFiniteMulSupport_iSup_detSet
    ((hρD.union hκf).subset (Function.mulSupport_mul _ _)) (fun v ↦ harch v.1) hfin
  refine h.trans_eq ?_
  have hprod := prod_abs_eq_one hκ
  rw [finprod_mul_distrib hρD hκf, finprod_mul_distrib hρnf hDf, ← finprod_pow hρf,
    mulFormHeight, mulRatioProd]
  have hpow : ∏ v : InfinitePlace K,
      (localRatio (L.minorSet S.incl) (fun x ↦ v x) ^ n) ^ v.mult =
        (∏ v : InfinitePlace K, localRatio (L.minorSet S.incl) (fun x ↦ v x) ^ v.mult) ^ n := by
    rw [← prod_pow]
    exact prod_congr rfl fun v _ ↦ by ring
  simp only [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, hpow]
  calc _ = N ^ finrank ℚ K * ((∏ v : InfinitePlace K,
        localRatio (L.minorSet S.incl) (fun x ↦ v x) ^ v.mult) *
          ∏ᶠ v : FinitePlace K, localRatio (L.minorSet S.incl) (fun x ↦ v x)) ^ n *
        ((∏ v : InfinitePlace K, (⨆ e : L.detSet, v e) ^ v.mult) *
          ∏ᶠ v : FinitePlace K, ⨆ e : L.detSet, v e) *
        ((∏ w : InfinitePlace K, w κ ^ w.mult) * ∏ᶠ w : FinitePlace K, w κ) := by ring
    _ = _ := by rw [hprod, mul_one, mul_pow]

end Lemma184

/-! ### The bounds in terms of `H_L` -/

section Bounds

variable (S : Splitting K n k m) (c : FormExponent K (Fin n))

/-- The exponent count of EF13 Lemma 18.4: `(k+1)^n ((2H)^{(4R)ⁿ})^n H ≤ (2H)^{(8R)ⁿ}`. -/
theorem quot_pow_le {n k R : ℕ} {H : ℝ} (hH : 1 ≤ H) (hkn : k < n) (hnR : n ≤ R) :
    (((k + 1) ^ n : ℕ) : ℝ) * ((2 * H) ^ ((4 * R) ^ n)) ^ n * H ≤ (2 * H) ^ ((8 * R) ^ n) := by
  set Y := 2 * H
  have hY : 2 ≤ Y := by simp only [Y]; linarith
  have hY1 : 1 ≤ Y := one_le_two.trans hY
  have h1 : (((k + 1) ^ n : ℕ) : ℝ) ≤ Y ^ (n * n) := by
    calc (((k + 1) ^ n : ℕ) : ℝ) ≤ ((2 ^ n) ^ n : ℕ) := by
          exact_mod_cast Nat.pow_le_pow_left ((by omega : k + 1 ≤ n).trans
            n.lt_two_pow_self.le) n
      _ = (2 : ℝ) ^ (n * n) := by push_cast; rw [← pow_mul]
      _ ≤ Y ^ (n * n) := pow_le_pow_left₀ zero_le_two hY _
  have h2 : H ≤ Y ^ 1 := by simp only [Y, pow_one]; linarith
  have hR : 1 ≤ R := by omega
  have hexp : n * n + (4 * R) ^ n * n + 1 ≤ (8 * R) ^ n := by
    have hsq : n * n + 1 ≤ 4 ^ n := by
      have := n.lt_two_pow_self
      have : n * n < 2 ^ n * 2 ^ n := Nat.mul_lt_mul'' this this
      rw [← mul_pow, show (2 : ℕ) * 2 = 4 by norm_num] at this
      omega
    have h4 : 4 ^ n ≤ (4 * R) ^ n := Nat.pow_le_pow_left (by omega) n
    have h8 : (8 * R) ^ n = 2 ^ n * (4 * R) ^ n := by rw [← mul_pow]; ring_nf
    have h2n : n + 1 ≤ 2 ^ n := n.lt_two_pow_self
    have : (n + 1) * (4 * R) ^ n ≤ 2 ^ n * (4 * R) ^ n := Nat.mul_le_mul_right _ h2n
    rw [h8]
    nlinarith
  calc (((k + 1) ^ n : ℕ) : ℝ) * (Y ^ ((4 * R) ^ n)) ^ n * H
      ≤ Y ^ (n * n) * (Y ^ ((4 * R) ^ n)) ^ n * Y ^ 1 := by gcongr
    _ = Y ^ (n * n + (4 * R) ^ n * n + 1) := by rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ Y ^ ((8 * R) ^ n) := pow_le_pow_right₀ hY1 hexp

/-- **EF13 Lemma 18.4** from Lemma 18.1: `H_{L''} ≤ (2 H_L)^{(8R)ⁿ}`, `R` the number of forms of
`L`, once `(∏_v M_v / m_v)^{1/[K:ℚ]} ≤ (2 H_L)^{(4R)ⁿ}`. -/
theorem absFormHeight_quotSystem_le_of_ratio (hkn : k < n)
    (h181 : mulRatioProd (L.minorSet S.incl) ^ ((finrank ℚ K : ℝ))⁻¹ ≤
      (2 * L.absFormHeight) ^ ((4 * #L.forms) ^ n)) :
    (L.quotSystem S c).absFormHeight ≤ (2 * L.absFormHeight) ^ ((8 * #L.forms) ^ n) := by
  have hd : finrank ℚ K ≠ 0 := Module.finrank_pos.ne'
  have hdi : (0 : ℝ) ≤ ((finrank ℚ K : ℝ))⁻¹ := by positivity
  have hne := L.minorSet_nonempty (linearIndependent_incl S)
  have hρ0 : 0 ≤ mulRatioProd (L.minorSet S.incl) :=
    zero_le_one.trans (one_le_mulRatioProd hne L.zero_notMem_minorSet)
  have hH0 : 0 ≤ L.mulFormHeight := zero_le_one.trans L.one_le_mulFormHeight
  have hHa : 1 ≤ L.absFormHeight := Real.one_le_rpow L.one_le_mulFormHeight hdi
  have h := Real.rpow_le_rpow ((L.quotSystem S c).one_le_mulFormHeight.trans' zero_le_one)
    (L.mulFormHeight_quotSystem_le S c) hdi
  refine h.trans ?_
  rw [Real.mul_rpow (by positivity) hH0, Real.mul_rpow (by positivity) (pow_nonneg hρ0 _),
    Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) hd, ← Real.rpow_natCast
      (mulRatioProd (L.minorSet S.incl)), ← Real.rpow_mul hρ0, mul_comm (n : ℝ),
    Real.rpow_mul hρ0, Real.rpow_natCast, ← absFormHeight]
  calc (((k + 1) ^ n : ℕ) : ℝ) * (mulRatioProd (L.minorSet S.incl) ^ ((finrank ℚ K : ℝ))⁻¹) ^ n *
        L.absFormHeight
      ≤ (((k + 1) ^ n : ℕ) : ℝ) * ((2 * L.absFormHeight) ^ ((4 * #L.forms) ^ n)) ^ n *
          L.absFormHeight := by gcongr
    _ ≤ _ := quot_pow_le hHa hkn L.le_card_forms

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]

/-- **EF13 Lemma 18.4**: `H_{L''} ≤ (2 H_L)^{(8R)ⁿ}`, `R` the number of forms of `L`, when `T` is
a member `T_l`, `0 < l < r`, of the filtration of `(L, c)` (EF13: `T = T(L, c)`, the member
`T_{r-1}`). Conditional on `SemistableGap K Ω` through Lemma 18.1. -/
theorem absFormHeight_quotSystem_le (hgap : SemistableGap K Ω) {r : ℕ}
    {T : ℕ → Submodule Ω (Fin n → Ω)}
    (hT : Submodule.IsWeightFiltration (L.subspaceWeight c) ⊤ r T) {l : ℕ} (hl0 : 0 < l)
    (hlr : l < r) (hST : (Submodule.span K (Set.range S.incl.col)).extendPi Ω = T l) :
    (L.quotSystem S c).absFormHeight ≤ (2 * L.absFormHeight) ^ ((8 * #L.forms) ^ n) := by
  -- `k < n` from the dimensions
  have hk : finrank Ω (T l) = k := by
    rw [← hST, Submodule.finrank_extendPi, finrank_span_eq_card (linearIndependent_incl S),
      Fintype.card_fin]
  have hkn : k < n := by
    have h1 := Submodule.finrank_lt_finrank_of_lt (hT.lt l hlr)
    have h2 := Submodule.finrank_le (T (l + 1))
    rw [Module.finrank_fin_fun] at h2
    omega
  exact L.absFormHeight_quotSystem_le_of_ratio S c hkn
    (L.mulRatioProd_minorSet_rpow_le hgap c hT hl0 hlr (linearIndependent_incl S) hST)

/-- **EF13 (18.5)** in terms of `H_L`: `H_{L'',c'',Q}(φ'' x) ≤ n (2 H_L)^{(4R)ⁿ} H_{L,c,Q}(x)`
for `Q ≥ 1`, under the hypotheses of `absFormHeight_quotSystem_le`. -/
theorem absMulHeight_quotSystem_le_of_isWeightFiltration (hgap : SemistableGap K Ω) {r : ℕ}
    {T : ℕ → Submodule Ω (Fin n → Ω)}
    (hT : Submodule.IsWeightFiltration (L.subspaceWeight c) ⊤ r T) {l : ℕ} (hl0 : 0 < l)
    (hlr : l < r) (hST : (Submodule.span K (Set.range S.incl.col)).extendPi Ω = T l) {Q : ℝ}
    (hQ : 1 ≤ Q) (x : Fin n → Ω) :
    (L.quotSystem S c).absMulHeight ((L.quotExp S c).weight (zero_lt_one.trans_le hQ))
        (S.projLin Ω x) ≤
      n * (2 * L.absFormHeight) ^ ((4 * #L.forms) ^ n) *
        L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x := by
  refine (L.absMulHeight_quotSystem_le S c hQ x).trans ?_
  gcongr
  · exact L.absMulHeight_nonneg _ _
  · exact L.mulRatioProd_minorSet_rpow_le hgap c hT hl0 hlr (linearIndependent_incl S) hST

end Bounds

/-! ### EF13 Lemma 18.3: the normalized exponents on the quotient -/

section Lemma183

variable (S : Splitting K n k m) (c : FormExponent K (Fin n))

/-- **The exponents `d` of EF13 (18.12)**: `d_iv = ((n - k) / n) (c_iv - θ_v)`, `i ∉ I_v(T)`, with
`θ_v` the mean of these `c_iv`. -/
noncomputable def quotNormExp : FormExponent K (Fin m) :=
  (L.quotExp S c).center.divConst ((n : ℝ) / m)

omit [NumberField K] in
/-- The local inequality behind (18.14): `(m/n)(x_t - mean_{t'} x_{t'}) ≤ max x - mean x`. -/
theorem le_iSup_sub_mean (x : Fin n → ℝ) (τ : Fin m → Fin n) (σ : Fin k → Fin n) (hm : 0 < m)
    (hkmn : k + m = n) (hsum : ∑ i, x i = ∑ s, x (σ s) + ∑ t, x (τ t)) (t : Fin m) :
    (x (τ t) - (∑ t', x (τ t')) / m) / ((n : ℝ) / m) ≤ (⨆ i, x i) - (∑ i, x i) / n := by
  have hle : ∀ i, x i ≤ ⨆ i, x i := fun i ↦ le_ciSup (Finite.bddAbove_range _) i
  have hσ : ∑ s, x (σ s) ≤ k * ⨆ i, x i := by
    calc ∑ s, x (σ s) ≤ ∑ _s : Fin k, ⨆ i, x i := sum_le_sum fun s _ ↦ hle _
      _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkmn' : (k : ℝ) + m = n := by exact_mod_cast hkmn
  have ht := hle (τ t)
  rw [div_div_eq_mul_div, div_le_iff₀ hn', hsum]
  field_simp
  have := mul_le_mul_of_nonneg_left ht hm'.le
  rw [← hkmn']
  linarith

theorem quotNormExp_arch (v : InfinitePlace K) (t : Fin m) :
    (L.quotNormExp S c).arch v t =
      (c.arch v (S.compSel (L.arch v) (c.arch v) t) -
        (∑ t', c.arch v (S.compSel (L.arch v) (c.arch v) t')) / m) / ((n : ℝ) / m) := by
  simp [quotNormExp, FormExponent.divConst, FormExponent.center, quotExp]

theorem quotNormExp_fin (v : FinitePlace K) (t : Fin m) :
    (L.quotNormExp S c).fin v t =
      (c.fin v (S.compSel (L.fin v) (c.fin v) t) -
        (∑ t', c.fin v (S.compSel (L.fin v) (c.fin v) t')) / m) / ((n : ℝ) / m) := by
  simp [quotNormExp, FormExponent.divConst, FormExponent.center, quotExp]

omit [NumberField K] in
theorem sum_selEquiv (A : Matrix (Fin n) (Fin n) K) (c : Fin n → ℝ) :
    ∑ i, c i = ∑ s, c (S.sel A c s) + ∑ t, c (S.compSel A c t) := by
  rw [← (S.selEquiv A c).sum_comp, Fintype.sum_sum_type]
  rfl

/-- **EF13 (18.14)**: `Σ_v max_i d_iv ≤ Σ_v max_i c_iv - α / n`, `α = Σ_v Σ_i c_iv`; so `≤ 1`
under (2.8) `α = 0` and (2.9) `Σ_v max_i c_iv ≤ 1`. -/
theorem sum_iSup_quotNormExp_le (hm : 0 < m) :
    (∑ v, ⨆ t, (L.quotNormExp S c).arch v t) + ∑ᶠ v, ⨆ t, (L.quotNormExp S c).fin v t ≤
      (∑ v, ⨆ i, c.arch v i) + (∑ᶠ v, ⨆ i, c.fin v i) - c.sum / n := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hkmn := S.card_eq
  have hs' : ∀ v, (L.quotNormExp S c).fin v ≠ 0 → v ∈ c.finSupport := fun v hv ↦
    c.mem_finSupport fun h ↦ hv (by funext t; rw [quotNormExp_fin]; simp [h])
  rw [(L.quotNormExp S c).finsum_eq_sum (fun f ↦ ⨆ t, f t) (by simp) hs',
    c.finsum_eq_sum (fun f ↦ ⨆ i, f i) (by simp) fun v hv ↦ c.mem_finSupport hv,
    FormExponent.sum, c.finsum_eq_sum (fun f ↦ ∑ i, f i) (by simp)
      fun v hv ↦ c.mem_finSupport hv]
  have ha : ∀ v, ⨆ t, (L.quotNormExp S c).arch v t ≤
      (⨆ i, c.arch v i) - (∑ i, c.arch v i) / n := fun v ↦ ciSup_le fun t ↦ by
    rw [quotNormExp_arch]
    exact le_iSup_sub_mean _ _ _ hm hkmn (sum_selEquiv S (L.arch v) (c.arch v)) t
  have hf : ∀ v, ⨆ t, (L.quotNormExp S c).fin v t ≤
      (⨆ i, c.fin v i) - (∑ i, c.fin v i) / n := fun v ↦ ciSup_le fun t ↦ by
    rw [quotNormExp_fin]
    exact le_iSup_sub_mean _ _ _ hm hkmn (sum_selEquiv S (L.fin v) (c.fin v)) t
  have h1 := sum_le_sum fun v (_ : v ∈ univ) ↦ ha v
  have h2 := sum_le_sum fun v (_ : v ∈ c.finSupport) ↦ hf v
  rw [sum_sub_distrib, ← sum_div] at h1 h2
  rw [add_div]
  linarith

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- **EF13 (18.16)**: if `T = ker φ''` is the destabilizing subspace of `Ωⁿ` with respect to
`(L, c)` (EF13 (2.21)), then `w_{L'',d}(U) ≤ 0` for every proper subspace `U` of `Ω^m`. -/
theorem subspaceWeight_quotNormExp_nonpos (hm : 0 < m)
    (hT : Submodule.IsDestabilizing (L.subspaceWeight (Ω := Ω) c) ⊤
      (LinearMap.ker (S.projLin Ω)))
    {U : Submodule Ω (Fin m → Ω)} (hU : U ≠ ⊤) :
    (L.quotSystem S c).subspaceWeight (L.quotNormExp S c) U ≤ 0 := by
  set T := LinearMap.ker (S.projLin Ω)
  set w := L.subspaceWeight (Ω := Ω) c
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := S.card_eq; omega)
  rw [quotNormExp, subspaceWeight_divConst _ _ (by positivity), subspaceWeight_center,
    subspaceWeight_quotSystem]
  have hsum : (L.quotExp S c).sum = w ⊤ - w T := by
    rw [← subspaceWeight_top (L.quotSystem S c) (L.quotExp S c) (Ω := Ω),
      subspaceWeight_quotSystem, Submodule.comap_top]
  rw [hsum]
  set W := U.comap (S.projLin Ω)
  have hW : W < ⊤ := lt_top_iff_ne_top.2 fun h ↦ hU <| by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := S.projLin_surjective Ω y
    have : x ∈ W := h ▸ Submodule.mem_top
    exact this
  have hdimW : (finrank Ω W : ℝ) = finrank Ω U + k := by
    rw [Submodule.finrank_comap_eq _ U (S.projLin_surjective Ω), S.finrank_ker_projLin]
    push_cast
    ring
  have hdimT : (finrank Ω T : ℝ) = k := by rw [S.finrank_ker_projLin]
  have hdimtop : (finrank Ω (⊤ : Submodule Ω (Fin n → Ω)) : ℝ) = k + m := by
    rw [finrank_top, Module.finrank_fin_fun]
    exact_mod_cast S.card_eq.symm
  have hle := hT.le W hW
  rw [Submodule.weightSlope_le_iff hT.lt, hdimtop, hdimT] at hle
  have hmul := Submodule.weightSlope_mul (w := w) hW
  rw [hdimtop, hdimW] at hmul
  -- `μ(T, ⊤) (m - dim U) ≤ w ⊤ - w W`
  have hμ := Submodule.weightSlope_mul (w := w) hT.lt
  rw [hdimtop, hdimT] at hμ
  have hUm : (finrank Ω U : ℝ) ≤ m := by
    have := Submodule.finrank_le U
    rw [Module.finrank_fin_fun] at this
    exact_mod_cast this
  refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
  have key : w W - w T ≤ (finrank Ω U : ℝ) * ((w ⊤ - w T) / m) := by
    rw [mul_div_assoc', le_div_iff₀ hm']
    nlinarith
  linarith

end Lemma183

end NumberField.FormSystem
