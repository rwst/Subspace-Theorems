/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormWeightExchange

-- Used only inside proofs.
import ArithmeticHeights.Extension
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The systems induced on a subspace and on a quotient

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, §16, (16.4)–(16.10), Lemmas 16.2, 16.3.

Let `T ⊆ Ωⁿ` be a subspace of dimension `k` defined over `K`. EF13 chooses `φ' : Ω^k → Ωⁿ` with
image `T` and `φ'' : Ωⁿ → Ω^{n-k}` with kernel `T`, both over `K`, and builds from a system
`(L, c)` a system `(L', c')` on `Ω^k` (the forms `L_i^{(v)} ∘ φ'`, `i ∈ I_v(T)`) and a system
`(L'', c'')` on `Ω^{n-k}` (the forms `L_i^{(v)} - Σ_{j ∈ I_v(T), j < i} α_ijv L_j^{(v)}`,
`i ∉ I_v(T)`, which vanish on `T`, read through `φ''`). Then

* `w_{L',c'}(U) = w_{L,c}(φ' U)` and `w_{L'',c''}(U) = w_{L,c}(φ''⁻¹ U) - w_{L,c}(T)`
  (Lemma 16.2);
* `H_{L',c',Q}(x) ≍ H_{L,c,Q}(φ' x)` and `H_{L'',c'',Q}(φ'' x) ≪ H_{L,c,Q}(x)` for `Q ≥ 1`
  (Lemma 16.3).

## Main definitions

* `NumberField.Splitting K n k m`: an invertible `n × (k + m)` matrix over `K`, giving
  `φ' = Splitting.incl` (its first `k` columns) and `φ'' = Splitting.proj` (the last `m` rows of
  the inverse).
* `Matrix.selectRows M c`: `k` rows of an `n × k` matrix of rank `k` forming an invertible
  matrix with the least `Σ c`; this is EF13's `I_v(T)` (a basis of least weight, so that every
  other row is a combination of selected rows of smaller or equal `c`).
* `NumberField.FormSystem.restrictSystem`, `NumberField.FormExponent.restrictExp`: `(L', c')`.
* `NumberField.FormSystem.quotSystem`, `NumberField.FormExponent.quotExp`: `(L'', c'')`.

## Main results

* `Matrix.le_of_mul_inv_ne_zero`: the exchange property of `selectRows`.
* `NumberField.FormSystem.subspaceWeight_restrictSystem`,
  `NumberField.FormSystem.subspaceWeight_quotSystem`: EF13 Lemma 16.2.
* `NumberField.FormSystem.absMulHeight_restrictSystem_le`,
  `NumberField.FormSystem.absMulHeight_le_restrictSystem`,
  `NumberField.FormSystem.absMulHeight_quotSystem_le`: EF13 Lemma 16.3.

## Implementation notes

EF13 orders the forms at each place so that `c` increases (15.1) and takes for `I_v(T)` the
greedy indices. Here `I_v(T)` is any set of `k` rows of `L^{(v)} φ'` forming an invertible matrix
with the least `Σ c`. The exchange property (`Matrix.le_of_mul_inv_ne_zero`) replaces the order:
row `i` is `Σ_s α_is (row σ(s))` with `α_is ≠ 0 → c_{σ s} ≤ c_i`, by Cramer's rule and the
minimality. The weights are then compared through `Submodule.formWeight_comp_embedding` and
`Submodule.formWeight_comap`, and the heights through one comparison lemma for systems related
by matrices `M_v` with `L₂^{(v)} Φ₂ = M_v L₁^{(v)} Φ₁` (`absMulHeight_le_of_mul_eq`).

This is part of milestone Q3.5 of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Module Finset Matrix

namespace Matrix

variable {K : Type*} [Field K] {n k : ℕ}

/-- A matrix with independent columns has an invertible square submatrix of full size. -/
theorem exists_submatrix_det_ne_zero (M : Matrix (Fin n) (Fin k) K)
    (hM : Function.Injective M.mulVec) : ∃ σ : Fin k ↪ Fin n, (M.submatrix σ id).det ≠ 0 := by
  classical
  have hrank : M.rank = k := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hM, Module.finrank_fin_fun]
  have htop : Submodule.span K (Set.range M.row) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [← rank_eq_finrank_span_row, hrank, Module.finrank_fin_fun]
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent K (Set.range M.row)
  have : Finite b := hli.finite
  have : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = k := by
    have h := (linearIndependent_iff_card_eq_finrank_span (b := (Subtype.val : b → _))).1 hli
    rw [Set.finrank, Subtype.range_coe, hspan, htop, finrank_top, Module.finrank_fin_fun] at h
    exact h
  choose f hf using fun x : b ↦ hb x.2
  have hfinj : Function.Injective f := fun x y hxy ↦ Subtype.ext <| by
    rw [← hf x, ← hf y, hxy]
  set e := Fintype.equivFinOfCardEq hcard
  refine ⟨e.symm.toEmbedding.trans ⟨f, hfinj⟩, ?_⟩
  have hrows : (M.submatrix (e.symm.toEmbedding.trans ⟨f, hfinj⟩) id).row =
      Subtype.val ∘ e.symm := by
    funext s
    exact hf (e.symm s)
  have hli' : LinearIndependent K (M.submatrix (e.symm.toEmbedding.trans ⟨f, hfinj⟩) id).row := by
    rw [hrows]
    exact hli.comp _ e.symm.injective
  exact (isUnit_iff_isUnit_det _).1 (linearIndependent_rows_iff_isUnit.1 hli') |>.ne_zero

open Classical in
/-- **A basis of least weight among the rows**: `k` rows of `M` forming an invertible matrix with
the least `Σ c` (EF13's `I_v(T)`), or `σ₀` if there are none. -/
noncomputable def selectRows (M : Matrix (Fin n) (Fin k) K) (c : Fin n → ℝ)
    (σ₀ : Fin k ↪ Fin n) : Fin k ↪ Fin n :=
  if h : ∃ σ : Fin k ↪ Fin n, (M.submatrix σ id).det ≠ 0 then
    (exists_min_image (univ.filter fun σ : Fin k ↪ Fin n ↦ (M.submatrix σ id).det ≠ 0)
      (fun σ ↦ ∑ s, c (σ s)) (by obtain ⟨σ, hσ⟩ := h; exact ⟨σ, by simpa using hσ⟩)).choose
  else σ₀

variable (M : Matrix (Fin n) (Fin k) K) (c : Fin n → ℝ) (σ₀ : Fin k ↪ Fin n)

theorem selectRows_det_ne_zero (h : ∃ σ : Fin k ↪ Fin n, (M.submatrix σ id).det ≠ 0) :
    (M.submatrix (selectRows M c σ₀) id).det ≠ 0 := by
  classical
  rw [selectRows, dite_eq_left_of_eq_true (eq_true h)]
  have := (exists_min_image (univ.filter fun σ : Fin k ↪ Fin n ↦ (M.submatrix σ id).det ≠ 0)
    (fun σ ↦ ∑ s, c (σ s)) (by obtain ⟨σ, hσ⟩ := h; exact ⟨σ, by simpa using hσ⟩)).choose_spec.1
  simpa using this

theorem sum_selectRows_le (h : ∃ σ : Fin k ↪ Fin n, (M.submatrix σ id).det ≠ 0)
    (τ : Fin k ↪ Fin n) (hτ : (M.submatrix τ id).det ≠ 0) :
    ∑ s, c (selectRows M c σ₀ s) ≤ ∑ s, c (τ s) := by
  classical
  rw [selectRows, dite_eq_left_of_eq_true (eq_true h)]
  exact (exists_min_image (univ.filter fun σ : Fin k ↪ Fin n ↦ (M.submatrix σ id).det ≠ 0)
    (fun σ ↦ ∑ s, c (σ s)) (by obtain ⟨σ, hσ⟩ := h; exact ⟨σ, by simpa using hσ⟩)).choose_spec.2
    τ (by simpa using hτ)

/-- **The exchange property** of a basis of least weight among the rows: in
`row i = Σ_s α_is (row σ(s))`, `α = M (M_σ)⁻¹`, only rows with `c_{σ s} ≤ c_i` occur. -/
theorem le_of_mul_inv_ne_zero {σ : Fin k ↪ Fin n} (hσ : (M.submatrix σ id).det ≠ 0)
    (hmin : ∀ τ : Fin k ↪ Fin n, (M.submatrix τ id).det ≠ 0 → ∑ s, c (σ s) ≤ ∑ s, c (τ s))
    {i : Fin n} {s : Fin k} (h : (M * (M.submatrix σ id)⁻¹) i s ≠ 0) : c (σ s) ≤ c i := by
  classical
  set Mσ := M.submatrix σ id
  set α := M * Mσ⁻¹
  have hM : M = α * Mσ := by
    rw [nonsing_inv_mul_cancel_right _ _ (Ne.isUnit hσ)]
  have hrow : M i = ∑ t, α i t • Mσ t := by
    funext j
    conv_lhs => rw [hM]
    simp [mul_apply, Finset.sum_apply]
  have hdet : (Mσ.updateRow s (M i)).det = α i s * Mσ.det := by
    rw [hrow, det_updateRow_sum, smul_eq_mul]
  have hdet0 : (Mσ.updateRow s (M i)).det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero h hσ
  by_cases hi : i ∈ Set.range σ
  · obtain ⟨s', rfl⟩ := hi
    by_cases hss : s' = s
    · rw [hss]
    · exfalso
      refine hdet0 (det_zero_of_row_eq (Ne.symm hss) ?_)
      rw [updateRow_self, updateRow_ne hss]
      rfl
  · have hinj : Function.Injective (Function.update σ s i) := by
      intro x y hxy
      by_cases hx : x = s <;> by_cases hy : y = s
      · rw [hx, hy]
      · simp only [hx, Function.update_self, Function.update_of_ne hy] at hxy
        exact (hi ⟨y, hxy.symm⟩).elim
      · simp only [hy, Function.update_self, Function.update_of_ne hx] at hxy
        exact (hi ⟨x, hxy⟩).elim
      · simp only [Function.update_of_ne hx, Function.update_of_ne hy] at hxy
        exact σ.injective hxy
    set τ : Fin k ↪ Fin n := ⟨Function.update σ s i, hinj⟩
    have hτ : M.submatrix τ id = Mσ.updateRow s (M i) := by
      ext t j
      by_cases ht : t = s
      · subst ht
        simp [τ]
      · simp [τ, ht, Mσ]
    have := hmin τ (hτ ▸ hdet0)
    have hsum : ∑ t, c (τ t) = c i + ∑ t ∈ univ \ {s}, c (σ t) := by
      change ∑ t, (c ∘ Function.update σ s i) t = _
      rw [Function.comp_update, sum_update_of_mem (mem_univ s)]
      rfl
    have hsum' : ∑ t, c (σ t) = c (σ s) + ∑ t ∈ univ \ {s}, c (σ t) := by
      rw [← sum_sdiff (singleton_subset_iff.2 (mem_univ s)), sum_singleton, add_comm]
    linarith

end Matrix

namespace NumberField

/-- **A splitting of `Kⁿ`**: an invertible `n × (k + m)` matrix `P` over `K` with inverse `Q`.
Its first `k` columns `φ'` span a subspace `T` of `Ωⁿ`, and the last `m` rows `φ''` of `Q` cut
it out. -/
structure Splitting (K : Type*) [Field K] (n k m : ℕ) where
  /-- The matrix. -/
  P : Matrix (Fin n) (Fin k ⊕ Fin m) K
  /-- Its inverse. -/
  Q : Matrix (Fin k ⊕ Fin m) (Fin n) K
  P_mul_Q : P * Q = 1
  Q_mul_P : Q * P = 1
  card_eq : k + m = n

namespace Splitting

variable {K : Type*} [Field K] {n k m : ℕ} (S : Splitting K n k m)

/-- `φ'`: the first `k` columns. -/
def incl : Matrix (Fin n) (Fin k) K := S.P.submatrix id Sum.inl

/-- The last `m` columns. -/
def compl : Matrix (Fin n) (Fin m) K := S.P.submatrix id Sum.inr

/-- The first `k` rows of the inverse. -/
def coproj : Matrix (Fin k) (Fin n) K := S.Q.submatrix Sum.inl id

/-- `φ''`: the last `m` rows of the inverse. -/
def proj : Matrix (Fin m) (Fin n) K := S.Q.submatrix Sum.inr id

theorem coproj_mul_incl : S.coproj * S.incl = 1 := by
  ext i j
  have := congrFun (congrFun S.Q_mul_P (Sum.inl i)) (Sum.inl j)
  simpa [Matrix.mul_apply, Matrix.one_apply, coproj, incl] using this

theorem proj_mul_incl : S.proj * S.incl = 0 := by
  ext i j
  have := congrFun (congrFun S.Q_mul_P (Sum.inr i)) (Sum.inl j)
  simpa [Matrix.mul_apply, Matrix.one_apply, proj, incl] using this

theorem proj_mul_compl : S.proj * S.compl = 1 := by
  ext i j
  have := congrFun (congrFun S.Q_mul_P (Sum.inr i)) (Sum.inr j)
  simpa [Matrix.mul_apply, Matrix.one_apply, proj, compl] using this

theorem incl_mul_coproj_add : S.incl * S.coproj + S.compl * S.proj = 1 := by
  ext i j
  have := congrFun (congrFun S.P_mul_Q i) j
  simpa [Matrix.mul_apply, Fintype.sum_sum_type, incl, coproj, compl, proj] using this

/-! ### The construction at one place -/

/-- A default choice of `k` rows. -/
def defaultEmb : Fin k ↪ Fin n := Fin.castLEEmb (by have := S.card_eq; omega)

variable (A : Matrix (Fin n) (Fin n) K) (c : Fin n → ℝ)

/-- `I_v(T)`: the rows of `A φ'` selected by `Matrix.selectRows`. -/
noncomputable def sel : Fin k ↪ Fin n := (A * S.incl).selectRows c S.defaultEmb

/-- `L'^{(v)}`: the selected rows of `A φ'`. -/
noncomputable def restrictMat : Matrix (Fin k) (Fin k) K := (A * S.incl).submatrix (S.sel A c) id

/-- The coefficients `α`: row `i` of `A φ'` is `Σ_s α_is (row s of L'^{(v)})`. -/
noncomputable def coeffMat : Matrix (Fin n) (Fin k) K := (A * S.incl) * (S.restrictMat A c)⁻¹

/-- The rows not selected. -/
noncomputable def complSet : Finset (Fin n) := univ.filter (· ∉ Set.range (S.sel A c))

theorem card_complSet : #(S.complSet A c) = m := by
  classical
  have h := card_filter_add_card_filter_not (s := univ) (· ∈ Set.range (S.sel A c))
  have h1 : #(univ.filter (· ∈ Set.range (S.sel A c))) = k := by
    rw [show univ.filter (· ∈ Set.range (S.sel A c)) = univ.map (S.sel A c) by
      ext i; simp, card_map, card_univ, Fintype.card_fin]
  rw [h1, card_univ, Fintype.card_fin] at h
  have := S.card_eq
  simp only [complSet]
  omega

/-- The indices `i ∉ I_v(T)`, in increasing order. -/
noncomputable def compSel : Fin m ↪ Fin n :=
  ((S.complSet A c).orderEmbOfFin (S.card_complSet A c)).toEmbedding

theorem range_compSel : Set.range (S.compSel A c) = (Set.range (S.sel A c))ᶜ := by
  rw [compSel, RelEmbedding.coe_toEmbedding, range_orderEmbOfFin]
  ext i
  simp [complSet]

theorem sel_ne_compSel (s : Fin k) (t : Fin m) : S.sel A c s ≠ S.compSel A c t := by
  intro h
  have : S.compSel A c t ∈ Set.range (S.compSel A c) := ⟨t, rfl⟩
  rw [range_compSel] at this
  exact this ⟨s, h⟩

/-- The indices `Fin k ⊕ Fin m ≃ Fin n`: selected rows first. -/
noncomputable def selEquiv : Fin k ⊕ Fin m ≃ Fin n :=
  Equiv.ofBijective (Sum.elim (S.sel A c) (S.compSel A c)) <| by
    refine ⟨(S.sel A c).injective.sumElim (S.compSel A c).injective (S.sel_ne_compSel A c),
      fun i ↦ ?_⟩
    by_cases hi : i ∈ Set.range (S.sel A c)
    · obtain ⟨s, rfl⟩ := hi
      exact ⟨Sum.inl s, rfl⟩
    · obtain ⟨t, rfl⟩ : i ∈ Set.range (S.compSel A c) := by rw [range_compSel]; exact hi
      exact ⟨Sum.inr t, rfl⟩

@[simp] theorem selEquiv_inl (s : Fin k) : S.selEquiv A c (Sum.inl s) = S.sel A c s := rfl

@[simp] theorem selEquiv_inr (t : Fin m) : S.selEquiv A c (Sum.inr t) = S.compSel A c t := rfl

/-- `L''^{(v)}`: the forms `L_i - Σ_s α_is L_{σ s}`, `i ∉ I_v(T)`, which vanish on `T`, read on
`Ωⁿ / T` through `φ''`. -/
noncomputable def quotMat : Matrix (Fin m) (Fin m) K :=
  (A * S.compl).submatrix (S.compSel A c) id -
    (S.coeffMat A c).submatrix (S.compSel A c) id * (A * S.compl).submatrix (S.sel A c) id

variable {A}

theorem mulVec_inj (hA : A.det ≠ 0) : Function.Injective (A * S.incl).mulVec := by
  intro x y hxy
  have hA' : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.2
    ((Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hA))
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hxy
  have h := congrArg S.coproj.mulVec (hA' hxy)
  simpa [Matrix.mulVec_mulVec, coproj_mul_incl] using h

theorem exists_det_ne_zero (hA : A.det ≠ 0) :
    ∃ σ : Fin k ↪ Fin n, ((A * S.incl).submatrix σ id).det ≠ 0 :=
  Matrix.exists_submatrix_det_ne_zero _ (S.mulVec_inj hA)

theorem restrictMat_det_ne_zero (hA : A.det ≠ 0) : (S.restrictMat A c).det ≠ 0 :=
  Matrix.selectRows_det_ne_zero _ c _ (S.exists_det_ne_zero hA)

theorem mul_incl_eq (hA : A.det ≠ 0) : A * S.incl = S.coeffMat A c * S.restrictMat A c := by
  rw [coeffMat, Matrix.nonsing_inv_mul_cancel_right _ _
    (Ne.isUnit (S.restrictMat_det_ne_zero c hA))]

/-- **The exchange property**: `α_is ≠ 0` only if `c_{σ s} ≤ c_i`. -/
theorem le_of_coeffMat_ne_zero (hA : A.det ≠ 0) {i : Fin n} {s : Fin k}
    (h : S.coeffMat A c i s ≠ 0) : c (S.sel A c s) ≤ c i :=
  Matrix.le_of_mul_inv_ne_zero _ c (S.restrictMat_det_ne_zero c hA)
    (fun τ hτ ↦ Matrix.sum_selectRows_le _ c _ (S.exists_det_ne_zero hA) τ hτ) h

theorem submatrix_mul_left {l l' o p : Type*} [Fintype o] (M : Matrix l o K) (N : Matrix o p K)
    (f : l' → l) : (M * N).submatrix f id = M.submatrix f id * N := by
  ext
  rfl

/-- `L'' φ'' = (L_i - Σ_s α_is L_{σ s})_{i ∉ I_v(T)}`. -/
theorem quotMat_mul_proj (hA : A.det ≠ 0) :
    S.quotMat A c * S.proj = A.submatrix (S.compSel A c) id -
      (S.coeffMat A c).submatrix (S.compSel A c) id * A.submatrix (S.sel A c) id := by
  have hA1 : A = A * S.incl * S.coproj + A * S.compl * S.proj := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, incl_mul_coproj_add,
      Matrix.mul_one]
  have hsub : ∀ {p : ℕ} (f : Fin p → Fin n), A.submatrix f id =
      (A * S.incl).submatrix f id * S.coproj + (A * S.compl).submatrix f id * S.proj := by
    intro p f
    conv_lhs => rw [hA1]
    ext i j
    rfl
  have hτ : (A * S.incl).submatrix (S.compSel A c) id =
      (S.coeffMat A c).submatrix (S.compSel A c) id * S.restrictMat A c := by
    rw [S.mul_incl_eq c hA, submatrix_mul_left]
  rw [hsub, hsub, hτ, quotMat]
  change _ = _ * S.restrictMat A c * S.coproj + _ - _ * (S.restrictMat A c * S.coproj + _)
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_assoc]
  abel

theorem quotMat_det_ne_zero (hA : A.det ≠ 0) : (S.quotMat A c).det ≠ 0 := by
  classical
  set e := S.selEquiv A c
  set R := S.restrictMat A c
  have hR := S.restrictMat_det_ne_zero c hA
  let : Invertible R := Matrix.invertibleOfIsUnitDet _ (Ne.isUnit hR)
  set B := (A * S.P).submatrix e id
  have hB : B = Matrix.fromBlocks R ((A * S.compl).submatrix (S.sel A c) id)
      ((A * S.incl).submatrix (S.compSel A c) id) ((A * S.compl).submatrix (S.compSel A c) id) := by
    ext (i | i) (j | j) <;> rfl
  have hPdet : (S.P.submatrix e id).det ≠ 0 := by
    have h : S.P.submatrix e id * S.Q.submatrix id e = 1 := by
      have h' := Matrix.submatrix_mul_equiv S.P S.Q e (Equiv.refl _) e
      simp only [Equiv.coe_refl] at h'
      rw [h', S.P_mul_Q, Matrix.submatrix_one_equiv]
    intro h0
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hBdet : B.det ≠ 0 := by
    have : B = A.submatrix e e * S.P.submatrix e id := by
      rw [Matrix.submatrix_mul_equiv]
    rw [this, Matrix.det_mul, Matrix.det_submatrix_equiv_self]
    exact mul_ne_zero hA hPdet
  have hC : (A * S.incl).submatrix (S.compSel A c) id * ⅟R =
      (S.coeffMat A c).submatrix (S.compSel A c) id := by
    rw [S.mul_incl_eq c hA, submatrix_mul_left, Matrix.invOf_eq_nonsing_inv, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (Ne.isUnit hR), Matrix.mul_one]
  rw [hB, Matrix.det_fromBlocks₁₁, hC] at hBdet
  exact right_ne_zero_of_mul hBdet

/-! ### The maps over `Ω` -/

variable (Ω : Type*) [Field Ω] [Algebra K Ω]

/-- `φ' : Ω^k → Ωⁿ`. -/
noncomputable def inclLin : (Fin k → Ω) →ₗ[Ω] (Fin n → Ω) :=
  (S.incl.map (algebraMap K Ω)).mulVecLin

/-- `φ'' : Ωⁿ → Ω^m`. -/
noncomputable def projLin : (Fin n → Ω) →ₗ[Ω] (Fin m → Ω) :=
  (S.proj.map (algebraMap K Ω)).mulVecLin

theorem inclLin_apply (x : Fin k → Ω) : S.inclLin Ω x = S.incl.map (algebraMap K Ω) *ᵥ x := rfl

theorem projLin_apply (x : Fin n → Ω) : S.projLin Ω x = S.proj.map (algebraMap K Ω) *ᵥ x := rfl

theorem coproj_inclLin (x : Fin k → Ω) : S.coproj.map (algebraMap K Ω) *ᵥ S.inclLin Ω x = x := by
  rw [inclLin_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul, coproj_mul_incl, Matrix.map_one _
    (map_zero _) (map_one _), Matrix.one_mulVec]

theorem inclLin_injective : Function.Injective (S.inclLin Ω) := fun x y h ↦ by
  rw [← S.coproj_inclLin Ω x, h, S.coproj_inclLin]

theorem projLin_compl (x : Fin m → Ω) : S.projLin Ω (S.compl.map (algebraMap K Ω) *ᵥ x) = x := by
  rw [projLin_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul, proj_mul_compl, Matrix.map_one _
    (map_zero _) (map_one _), Matrix.one_mulVec]

theorem projLin_surjective : Function.Surjective (S.projLin Ω) := fun x ↦ ⟨_, S.projLin_compl Ω x⟩

theorem eq_inclLin_add (x : Fin n → Ω) : x = S.inclLin Ω (S.coproj.map (algebraMap K Ω) *ᵥ x) +
    S.compl.map (algebraMap K Ω) *ᵥ S.projLin Ω x := by
  rw [inclLin_apply, projLin_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec,
    ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add _), incl_mul_coproj_add,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

/-- `T = φ'(Ω^k) = ker φ''`. -/
theorem ker_projLin : LinearMap.ker (S.projLin Ω) = LinearMap.range (S.inclLin Ω) := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    refine ⟨S.coproj.map (algebraMap K Ω) *ᵥ x, ?_⟩
    conv_rhs => rw [S.eq_inclLin_add Ω x, hx, Matrix.mulVec_zero, add_zero]
  · rintro ⟨y, rfl⟩
    rw [LinearMap.mem_ker, projLin_apply, inclLin_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul,
      proj_mul_incl, Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec]

theorem finrank_ker_projLin : finrank Ω (LinearMap.ker (S.projLin Ω)) = k := by
  rw [ker_projLin, LinearMap.finrank_range_of_inj (S.inclLin_injective Ω), Module.finrank_fin_fun]

end Splitting

/-! ### Rows of a matrix as forms -/

/-- The rows of a (rectangular) matrix over `K` as linear forms on `Ω^κ`. -/
noncomputable def rowForms {K : Type*} [Field K] {ι κ : Type*} [Fintype κ] {Ω : Type*} [Field Ω]
    [Algebra K Ω] (M : Matrix ι κ K) (i : ι) : Module.Dual Ω (κ → Ω) :=
  (LinearMap.proj i).comp (M.map (algebraMap K Ω)).mulVecLin

theorem rowForms_apply {K : Type*} [Field K] {ι κ : Type*} [Fintype κ] {Ω : Type*} [Field Ω]
    [Algebra K Ω] (M : Matrix ι κ K) (i : ι) (x : κ → Ω) :
    rowForms (Ω := Ω) M i x = (M.map (algebraMap K Ω) *ᵥ x) i := rfl

/-- A combination with coefficients supported on `S` lies in the span of the image of `S`. -/
theorem mem_span_of_eq_sum {R M ι : Type*} [Field R] [AddCommGroup M] [Module R M] [Fintype ι]
    {f : M} {g : ι → M} {a : ι → R} {S : Set ι} (hf : f = ∑ i, a i • g i)
    (ha : ∀ i, a i ≠ 0 → i ∈ S) : f ∈ Submodule.span R (g '' S) := by
  rw [hf]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  by_cases hi : a i = 0
  · rw [hi, zero_smul]
    exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, ha i hi, rfl⟩)

/-! ### The local weights (EF13 Lemma 16.2, at one place) -/

namespace Splitting

variable {K : Type*} [Field K] {n k m : ℕ} (S : Splitting K n k m) {A : Matrix (Fin n) (Fin n) K}
  (c : Fin n → ℝ) {Ω : Type*} [Field Ω] [Algebra K Ω]

theorem rowForms_eq_sum (hA : A.det ≠ 0) (i : Fin n) :
    rowForms (Ω := Ω) (A * S.incl) i =
      ∑ s, algebraMap K Ω (S.coeffMat A c i s) • rowForms (S.restrictMat A c) s := by
  refine LinearMap.ext fun x ↦ ?_
  rw [rowForms_apply, S.mul_incl_eq c hA, Matrix.map_mul, ← Matrix.mulVec_mulVec]
  simp [rowForms_apply, Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def]

/-- **EF13 Lemma 16.2 (i), locally**: `w_{L'^{(v)}, c'}(U) = w_{L^{(v)}, c}(φ' U)`. -/
theorem formWeight_restrictMat (hA : A.det ≠ 0) (U : Submodule Ω (Fin k → Ω)) :
    Submodule.formWeight (FormSystem.matrixForms (S.restrictMat A c)) (c ∘ S.sel A c) U =
      Submodule.formWeight (FormSystem.matrixForms A) c (U.map (S.inclLin Ω)) := by
  rw [Submodule.formWeight_map _ _ _ (S.inclLin_injective Ω)]
  have hcomp : (fun i ↦ (FormSystem.matrixForms (Ω := Ω) A i).comp (S.inclLin Ω)) =
      rowForms (A * S.incl) := by
    funext i
    refine LinearMap.ext fun x ↦ ?_
    simp [FormSystem.matrixForms_apply, rowForms_apply, Splitting.inclLin_apply, Matrix.map_mul,
      Matrix.mulVec_mulVec]
  have hsel : rowForms (Ω := Ω) (A * S.incl) ∘ S.sel A c =
      FormSystem.matrixForms (S.restrictMat A c) := by
    funext s
    rfl
  rw [hcomp, ← hsel]
  refine Submodule.formWeight_comp_embedding _ _ ?_ _ (fun i ↦ ?_) U
  · refine eq_bot_iff.2 fun x hx ↦ ?_
    rw [← FormSystem.iInf_ker_matrixForms (S.restrictMat_det_ne_zero c hA)]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
    exact fun s ↦ hx (S.sel A c s)
  · rw [Function.comp_def]
    exact mem_span_of_eq_sum (S.rowForms_eq_sum c hA i) fun s hs ↦
      S.le_of_coeffMat_ne_zero c hA fun h ↦ hs (by rw [h, map_zero])

omit S in
theorem linearIndependent_matrixForms {B : Matrix (Fin k) (Fin k) K} (hB : B.det ≠ 0) :
    LinearIndependent Ω (FormSystem.matrixForms (Ω := Ω) B) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hB' : IsUnit (B.map (algebraMap K Ω)) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have := (algebraMap K Ω).map_det B
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact ((map_ne_zero _).2 hB).isUnit
  have hv : g ᵥ* B.map (algebraMap K Ω) = 0 := by
    funext j
    have := LinearMap.congr_fun hg (Pi.single j 1)
    simpa [FormSystem.matrixForms_apply, Matrix.mulVec, dotProduct, Matrix.vecMul,
      Pi.single_apply, mul_comm] using this
  have hinj := Matrix.vecMul_injective_iff_isUnit.2 hB'
  have := hinj (hv.trans (Matrix.zero_vecMul _).symm)
  exact fun s ↦ congrFun this s

/-- `L''^{(v)} φ''` as forms: `L_{τ t} - Σ_s α_{τ t, s} L_{σ s}`. -/
theorem matrixForms_quotMat_comp (hA : A.det ≠ 0) (t : Fin m) :
    (FormSystem.matrixForms (Ω := Ω) (S.quotMat A c) t).comp (S.projLin Ω) =
      FormSystem.matrixForms A (S.compSel A c t) - ∑ s, algebraMap K Ω
        (S.coeffMat A c (S.compSel A c t) s) • FormSystem.matrixForms A (S.sel A c s) := by
  refine LinearMap.ext fun x ↦ ?_
  rw [LinearMap.comp_apply, FormSystem.matrixForms_apply, projLin_apply, Matrix.mulVec_mulVec,
    ← Matrix.map_mul, S.quotMat_mul_proj c hA]
  simp only [FormSystem.matrixForms_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Matrix.sub_apply, Matrix.submatrix_apply, Matrix.mul_apply, LinearMap.sub_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, Algebra.smul_def, map_sub,
    map_sum, map_mul, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum, id,
    mul_assoc,
    Algebra.algebraMap_self, RingHom.id_apply]
  rw [Finset.sum_comm]

/-- **EF13 Lemma 16.2 (ii), locally**:
`w_{L^{(v)}, c}(φ''⁻¹ U) = Σ_{i ∈ I_v(T)} c_i + w_{L''^{(v)}, c''}(U)`. -/
theorem formWeight_quotMat (hA : A.det ≠ 0) (U : Submodule Ω (Fin m → Ω)) :
    Submodule.formWeight (FormSystem.matrixForms A) c (U.comap (S.projLin Ω)) =
      ∑ s, c (S.sel A c s) +
        Submodule.formWeight (FormSystem.matrixForms (S.quotMat A c)) (c ∘ S.compSel A c) U := by
  classical
  set e := S.selEquiv A c
  set ℓ : Fin n → Module.Dual Ω (Fin n → Ω) := FormSystem.matrixForms A
  set F : Fin k ⊕ Fin m → Module.Dual Ω (Fin n → Ω) := Sum.elim (fun s ↦ ℓ (S.sel A c s))
    fun t ↦ (FormSystem.matrixForms (S.quotMat A c) t).comp (S.projLin Ω)
  have hℓ : ⨅ i, LinearMap.ker (ℓ i) = ⊥ := FormSystem.iInf_ker_matrixForms hA
  have hℓe : ⨅ y, LinearMap.ker ((ℓ ∘ e) y) = ⊥ := by
    refine eq_bot_iff.2 fun x hx ↦ ?_
    rw [← hℓ]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, Function.comp_apply] at hx ⊢
    exact fun i ↦ by simpa using hx (e.symm i)
  have hsum : ∀ t, ∑ s, algebraMap K Ω (S.coeffMat A c (S.compSel A c t) s) • ℓ (S.sel A c s) ∈
      Submodule.span Ω ((ℓ ∘ e) '' {z | (c ∘ e) z ≤ (c ∘ e) (Sum.inr t)}) := fun t ↦ by
    refine Submodule.span_mono ?_ (mem_span_of_eq_sum (S := {s | c (S.sel A c s) ≤
      c (S.compSel A c t)}) (g := fun s ↦ (ℓ ∘ e) (Sum.inl s)) rfl fun s hs ↦
        S.le_of_coeffMat_ne_zero c hA fun h ↦ hs (by rw [h, map_zero]))
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨Sum.inl s, hs, rfl⟩
  have hsum' : ∀ t, ∑ s, algebraMap K Ω (S.coeffMat A c (S.compSel A c t) s) • ℓ (S.sel A c s) ∈
      Submodule.span Ω (F '' {z | (c ∘ e) z ≤ (c ∘ e) (Sum.inr t)}) := fun t ↦ by
    refine Submodule.span_mono ?_ (mem_span_of_eq_sum (S := {s | c (S.sel A c s) ≤
      c (S.compSel A c t)}) (g := fun s ↦ F (Sum.inl s)) rfl fun s hs ↦
        S.le_of_coeffMat_ne_zero c hA fun h ↦ hs (by rw [h, map_zero]))
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨Sum.inl s, hs, rfl⟩
  have h₁ : ∀ y, F y ∈ Submodule.span Ω ((ℓ ∘ e) '' {z | (c ∘ e) z ≤ (c ∘ e) y}) := by
    rintro (s | t)
    · exact Submodule.subset_span ⟨Sum.inl s, le_refl ((c ∘ e) (Sum.inl s)), rfl⟩
    · change (FormSystem.matrixForms (S.quotMat A c) t).comp (S.projLin Ω) ∈ _
      rw [S.matrixForms_quotMat_comp c hA]
      exact Submodule.sub_mem _
        (Submodule.subset_span ⟨Sum.inr t, le_refl ((c ∘ e) (Sum.inr t)), rfl⟩) (hsum t)
  have h₂ : ∀ y, (ℓ ∘ e) y ∈ Submodule.span Ω (F '' {z | (c ∘ e) z ≤ (c ∘ e) y}) := by
    rintro (s | t)
    · exact Submodule.subset_span ⟨Sum.inl s, le_refl ((c ∘ e) (Sum.inl s)), rfl⟩
    · have : (ℓ ∘ e) (Sum.inr t) = F (Sum.inr t) + ∑ s, algebraMap K Ω
          (S.coeffMat A c (S.compSel A c t) s) • ℓ (S.sel A c s) := by
        change ℓ (S.compSel A c t) = (FormSystem.matrixForms (S.quotMat A c) t).comp
          (S.projLin Ω) + _
        rw [S.matrixForms_quotMat_comp c hA, sub_add_cancel]
      rw [this]
      exact Submodule.add_mem _
        (Submodule.subset_span ⟨Sum.inr t, le_refl ((c ∘ e) (Sum.inr t)), rfl⟩) (hsum' t)
  have hF : ⨅ y, LinearMap.ker (F y) = ⊥ := by
    refine eq_bot_iff.2 fun x hx ↦ ?_
    rw [← hℓe]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
    exact fun y ↦ Submodule.apply_eq_zero_of_mem_span (h₂ y) (by rintro _ ⟨z, -, rfl⟩; exact hx z)
  -- The selected forms restrict to a basis of the dual of `T`.
  set ψ : (Fin k → Ω) →ₗ[Ω] LinearMap.ker (S.projLin Ω) := (S.inclLin Ω).codRestrict _
    fun y ↦ by rw [ker_projLin]; exact ⟨y, rfl⟩
  have hψ : ∀ s, ψ.dualMap ((F (Sum.inl s)).domRestrict (LinearMap.ker (S.projLin Ω))) =
      FormSystem.matrixForms (S.restrictMat A c) s := fun s ↦ by
    refine LinearMap.ext fun y ↦ ?_
    simp [ψ, F, ℓ, FormSystem.matrixForms_apply, inclLin_apply, Matrix.mulVec_mulVec,
      ← Matrix.map_mul]
    rfl
  have hI : LinearIndepOn Ω (fun y ↦ (F y).domRestrict (LinearMap.ker (S.projLin Ω)))
      ↑(univ.map (Function.Embedding.inl : Fin k ↪ Fin k ⊕ Fin m)) := by
    rw [coe_map, coe_univ]
    refine LinearIndepOn.image_of_comp Sum.inl _ (linearIndepOn_univ_iff.2 ?_)
    refine LinearIndependent.of_comp ψ.dualMap ?_
    have : ψ.dualMap ∘ ((fun y ↦ (F y).domRestrict (LinearMap.ker (S.projLin Ω))) ∘ Sum.inl) =
        FormSystem.matrixForms (S.restrictMat A c) := funext hψ
    rw [this]
    exact linearIndependent_matrixForms (S.restrictMat_det_ne_zero c hA)
  have hcomap := Submodule.formWeight_comap F (c ∘ e) (S.projLin Ω) U hF (S.projLin_surjective Ω)
    (univ.map Function.Embedding.inl) hI (by rw [card_map, card_univ, Fintype.card_fin,
      finrank_ker_projLin]) Function.Embedding.inr
    (by rintro (s | t) <;> simp) (FormSystem.matrixForms (S.quotMat A c)) (fun t ↦ rfl)
    (FormSystem.iInf_ker_matrixForms (S.quotMat_det_ne_zero c hA))
  have h1 := (Submodule.formWeight_comp_embedding ℓ c hℓ e.toEmbedding
    (fun i ↦ Submodule.subset_span ⟨e.symm i, by simp, by simp⟩) (U.comap (S.projLin Ω))).symm
  have h2 := Submodule.formWeight_eq_of_mem_span (ℓ ∘ e) (c ∘ e) F hℓe h₁ h₂
    (U.comap (S.projLin Ω))
  rw [h1]
  change Submodule.formWeight (ℓ ∘ e) (c ∘ e) _ = _
  rw [← h2, hcomap, sum_map]
  rfl

theorem formWeight_quotMat_ker (hA : A.det ≠ 0) :
    Submodule.formWeight (FormSystem.matrixForms A) c (LinearMap.ker (S.projLin Ω)) =
      ∑ s, c (S.sel A c s) := by
  have := S.formWeight_quotMat c hA (⊥ : Submodule Ω (Fin m → Ω))
  rwa [Submodule.comap_bot, Submodule.formWeight_bot, add_zero] at this

end Splitting

namespace Splitting

variable {K : Type*} [Field K] {n k m : ℕ} (S : Splitting K n k m)

/-- The rows `σ` of the identity matrix. -/
def selMat {p : ℕ} (σ : Fin p ↪ Fin n) : Matrix (Fin p) (Fin n) K :=
  (1 : Matrix (Fin n) (Fin n) K).submatrix σ id

theorem selMat_mul {p : ℕ} (σ : Fin p ↪ Fin n) {κ : Type*} (M : Matrix (Fin n) κ K) :
    selMat σ * M = M.submatrix σ id := by
  rw [selMat, ← submatrix_mul_left, Matrix.one_mul]

theorem le_of_selMat_ne_zero {p : ℕ} {σ : Fin p ↪ Fin n} {s : Fin p} {i : Fin n}
    (h : selMat (K := K) σ s i ≠ 0) : σ s = i := by
  by_contra hne
  exact h (Matrix.one_apply_ne hne)

variable (A : Matrix (Fin n) (Fin n) K) (c : Fin n → ℝ)

/-- The matrix `M` with `L'' φ'' = M L`: rows `e_{τ t} - Σ_s α_{τ t, s} e_{σ s}`. -/
noncomputable def quotCoeff : Matrix (Fin m) (Fin n) K :=
  selMat (S.compSel A c) - (S.coeffMat A c).submatrix (S.compSel A c) id * selMat (S.sel A c)

variable {A}

theorem quotCoeff_mul (hA : A.det ≠ 0) : S.quotCoeff A c * A = S.quotMat A c * S.proj := by
  rw [S.quotMat_mul_proj c hA, quotCoeff, Matrix.sub_mul, Matrix.mul_assoc, selMat_mul,
    selMat_mul]

theorem le_of_quotCoeff_ne_zero (hA : A.det ≠ 0) {t : Fin m} {i : Fin n}
    (h : S.quotCoeff A c t i ≠ 0) : c i ≤ c (S.compSel A c t) := by
  classical
  by_cases hi : i = S.compSel A c t
  · rw [hi]
  have h0 : selMat (K := K) (S.compSel A c) t i = 0 := by
    exact Matrix.one_apply_ne (Ne.symm hi)
  rw [quotCoeff, Matrix.sub_apply, h0, zero_sub, neg_ne_zero, Matrix.mul_apply] at h
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hσ := le_of_selMat_ne_zero (right_ne_zero_of_mul hs)
  rw [← hσ]
  exact S.le_of_coeffMat_ne_zero c hA (left_ne_zero_of_mul hs)

end Splitting

namespace Splitting

variable {K : Type*} [Field K] {n : ℕ} {Ω : Type*} [Field Ω] [Algebra K Ω]

theorem _root_.Module.Basis.sumExtend_inl {V ι : Type*} [AddCommGroup V] [Module K V]
    {v : ι → V} (hs : LinearIndependent K v) (i : ι) : Basis.sumExtend hs (Sum.inl i) = v i := by
  simp only [Basis.sumExtend, Basis.extend, Basis.reindex_apply, Basis.mk_apply]
  rfl

/-- **A splitting adapted to a subspace defined over `K`**: `φ'(Ω^k) = T`, `k = dim T`. -/
theorem exists_range_inclLin {T : Submodule Ω (Fin n → Ω)} (hT : T.IsDefinedOver K) :
    ∃ S : Splitting K n (finrank Ω T) (n - finrank Ω T), LinearMap.range (S.inclLin Ω) = T := by
  classical
  set k := finrank Ω T
  obtain ⟨s, hs⟩ := hT
  set ι : (Fin n → K) → Fin n → Ω := fun y ↦ algebraMap K Ω ∘ y
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent Ω (ι '' s)
  have : Finite b := hli.finite
  have : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = k := by
    have h := (linearIndependent_iff_card_eq_finrank_span (b := (Subtype.val : b → _))).1 hli
    rw [Set.finrank, Subtype.range_coe, hspan, hs] at h
    exact h
  choose g hgs hg using fun x : b ↦ hb x.2
  set e := Fintype.equivFinOfCardEq hcard
  set u : Fin k → Fin n → K := fun i ↦ g (e.symm i)
  have hιu : ι ∘ u = Subtype.val ∘ e.symm := funext fun i ↦ hg (e.symm i)
  have hliΩ : LinearIndependent Ω (ι ∘ u) := by
    rw [hιu]
    exact hli.comp _ e.symm.injective
  have hu : LinearIndependent K u := by
    rw [Fintype.linearIndependent_iff] at hliΩ ⊢
    intro a ha i
    have h0 : ∑ i, algebraMap K Ω (a i) • (ι ∘ u) i = 0 := by
      funext j
      have := congrFun ha j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, ι,
        Pi.zero_apply, ← map_mul, ← map_sum, this, map_zero]
    exact (map_eq_zero_iff _ (algebraMap K Ω).injective).1 (hliΩ _ h0 i)
  set bas := Basis.sumExtend hu
  have : Fintype (Basis.sumExtendIndex hu) := by
    have : Finite (Fin k ⊕ Basis.sumExtendIndex hu) := Module.Finite.finite_basis bas
    have : Finite (Basis.sumExtendIndex hu) :=
      Finite.of_injective (Sum.inr (α := Fin k)) Sum.inr_injective
    exact Fintype.ofFinite _
  have hkn : k ≤ n := by
    have := Submodule.finrank_le T
    rwa [Module.finrank_fin_fun] at this
  have hX : Fintype.card (Basis.sumExtendIndex hu) = n - k := by
    have := Module.finrank_eq_card_basis bas
    rw [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at this
    omega
  set bas' := bas.reindex (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFinOfCardEq hX))
  have hinl : ∀ i, bas' (Sum.inl i) = u i := fun i ↦ by
    simp [bas', Basis.reindex_apply, bas, Basis.sumExtend_inl]
  set P := (Pi.basisFun K (Fin n)).toMatrix bas'
  set Q := bas'.toMatrix (Pi.basisFun K (Fin n))
  let S : Splitting K n k (n - k) :=
    { P := P, Q := Q,
      P_mul_Q := Basis.toMatrix_mul_toMatrix_flip _ _,
      Q_mul_P := Basis.toMatrix_mul_toMatrix_flip _ _,
      card_eq := by omega }
  refine ⟨S, ?_⟩
  have hincl : ∀ y : Fin k → Ω, S.inclLin Ω y = ∑ i, y i • (ι ∘ u) i := fun y ↦ by
    funext j
    simp [S, inclLin_apply, incl, P, Matrix.mulVec, dotProduct, Basis.toMatrix_apply, hinl, ι,
      Finset.sum_apply, mul_comm]
  ext x
  rw [LinearMap.mem_range, ← hs, ← hspan]
  have : b = Set.range (ι ∘ u) := by
    rw [hιu, Set.range_comp, Set.range_eq_univ.2 e.symm.surjective, Set.image_univ,
      Subtype.range_coe]
  rw [this, Submodule.mem_span_range_iff_exists_fun]
  simp only [hincl]
end Splitting

/-! ### The induced systems -/

namespace FormSystem

variable {K : Type*} [Field K] [NumberField K] {n k m : ℕ} (S : Splitting K n k m)
  (L : FormSystem K (Fin n)) (c : FormExponent K (Fin n))

/-- The pairs `(L^{(v)}, c_v)` at the finite places are finitely many. -/
theorem finite_range_fin_exp : (Set.range fun v : FinitePlace K ↦ (L.fin v, c.fin v)).Finite := by
  refine (L.finite_range_fin.prod ((c.finite_setOf_fin_ne_zero.image c.fin).insert 0)).subset ?_
  rintro _ ⟨v, rfl⟩
  refine Set.mk_mem_prod ⟨v, rfl⟩ ?_
  by_cases h : c.fin v = 0
  · exact Or.inl h
  · exact Or.inr ⟨v, h, rfl⟩

/-- **The system `L'` induced on `T`** (EF13 (16.4)): at each place the forms
`L_i^{(v)} ∘ φ'`, `i ∈ I_v(T)`. -/
noncomputable def restrictSystem : FormSystem K (Fin k) where
  arch v := S.restrictMat (L.arch v) (c.arch v)
  arch_det_ne_zero v := S.restrictMat_det_ne_zero _ (L.arch_det_ne_zero v)
  fin v := S.restrictMat (L.fin v) (c.fin v)
  fin_det_ne_zero v := S.restrictMat_det_ne_zero _ (L.fin_det_ne_zero v)
  finite_range_fin := ((L.finite_range_fin_exp c).image fun p ↦ S.restrictMat p.1 p.2).subset <| by
    rintro _ ⟨v, rfl⟩
    exact ⟨_, ⟨v, rfl⟩, rfl⟩

/-- **The exponents `c'` induced on `T`** (EF13 (16.4)): `c_iv`, `i ∈ I_v(T)`. -/
noncomputable def restrictExp : FormExponent K (Fin k) where
  arch v := c.arch v ∘ S.sel (L.arch v) (c.arch v)
  fin v := c.fin v ∘ S.sel (L.fin v) (c.fin v)
  finite_setOf_fin_ne_zero := c.finite_setOf_fin_ne_zero.subset fun v hv h ↦ hv <| by
    funext s
    simp [h]

/-- **The system `L''` induced on `Ωⁿ / T`** (EF13 (16.5), (16.6)): at each place the forms
`L_i^{(v)} - Σ_{j ∈ I_v(T)} α_ijv L_j^{(v)}`, `i ∉ I_v(T)`, read through `φ''`. -/
noncomputable def quotSystem : FormSystem K (Fin m) where
  arch v := S.quotMat (L.arch v) (c.arch v)
  arch_det_ne_zero v := S.quotMat_det_ne_zero _ (L.arch_det_ne_zero v)
  fin v := S.quotMat (L.fin v) (c.fin v)
  fin_det_ne_zero v := S.quotMat_det_ne_zero _ (L.fin_det_ne_zero v)
  finite_range_fin := ((L.finite_range_fin_exp c).image fun p ↦ S.quotMat p.1 p.2).subset <| by
    rintro _ ⟨v, rfl⟩
    exact ⟨_, ⟨v, rfl⟩, rfl⟩

/-- **The exponents `c''` induced on `Ωⁿ / T`** (EF13 (16.6)): `c_iv`, `i ∉ I_v(T)`. -/
noncomputable def quotExp : FormExponent K (Fin m) where
  arch v := c.arch v ∘ S.compSel (L.arch v) (c.arch v)
  fin v := c.fin v ∘ S.compSel (L.fin v) (c.fin v)
  finite_setOf_fin_ne_zero := c.finite_setOf_fin_ne_zero.subset fun v hv h ↦ hv <| by
    funext s
    simp [h]

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- The weight as a finite sum over any set of finite places containing those with `c_v ≠ 0`. -/
theorem subspaceWeight_eq_sum_of_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : FormSystem K ι) (c : FormExponent K ι) (s : Finset (FinitePlace K))
    (hs : ∀ v, c.fin v ≠ 0 → v ∈ s) (U : Submodule Ω (ι → Ω)) :
    L.subspaceWeight c U = ∑ v, Submodule.formWeight (matrixForms (L.arch v)) (c.arch v) U +
      ∑ v ∈ s, Submodule.formWeight (matrixForms (L.fin v)) (c.fin v) U := by
  rw [subspaceWeight, finsum_eq_sum_of_support_subset]
  intro v hv
  refine hs v fun h ↦ hv ?_
  change Submodule.formWeight _ (c.fin v) U = 0
  rw [h]
  exact Submodule.formWeight_zero _ (iInf_ker_matrixForms (L.fin_det_ne_zero v)) U

/-- **EF13 Lemma 16.2 (i)**: `w_{L',c'}(U) = w_{L,c}(φ' U)`. -/
theorem subspaceWeight_restrictSystem (U : Submodule Ω (Fin k → Ω)) :
    (L.restrictSystem S c).subspaceWeight (L.restrictExp S c) U =
      L.subspaceWeight c (U.map (S.inclLin Ω)) := by
  simp only [subspaceWeight]
  congr 1
  · exact sum_congr rfl fun v _ ↦ S.formWeight_restrictMat _ (L.arch_det_ne_zero v) U
  · exact finsum_congr fun v ↦ S.formWeight_restrictMat _ (L.fin_det_ne_zero v) U

/-- **EF13 Lemma 16.2 (ii)**: `w_{L'',c''}(U) = w_{L,c}(φ''⁻¹ U) - w_{L,c}(T)`. -/
theorem subspaceWeight_quotSystem (U : Submodule Ω (Fin m → Ω)) :
    (L.quotSystem S c).subspaceWeight (L.quotExp S c) U =
      L.subspaceWeight c (U.comap (S.projLin Ω)) -
        L.subspaceWeight c (LinearMap.ker (S.projLin Ω)) := by
  set s := c.finite_setOf_fin_ne_zero.toFinset
  have hs : ∀ v, c.fin v ≠ 0 → v ∈ s := fun v hv ↦ by simpa [s] using hv
  have hs' : ∀ v, (L.quotExp S c).fin v ≠ 0 → v ∈ s := fun v hv ↦ hs v fun h ↦ hv <| by
    funext t
    simp [quotExp, h]
  rw [subspaceWeight_eq_sum_of_subset _ _ s hs', subspaceWeight_eq_sum_of_subset _ _ s hs,
    subspaceWeight_eq_sum_of_subset _ _ s hs]
  have ha : ∀ v, Submodule.formWeight (matrixForms ((L.quotSystem S c).arch v))
      ((L.quotExp S c).arch v) U =
      Submodule.formWeight (matrixForms (L.arch v)) (c.arch v) (U.comap (S.projLin Ω)) -
        Submodule.formWeight (matrixForms (L.arch v)) (c.arch v) (LinearMap.ker (S.projLin Ω)) :=
    fun v ↦ by
      rw [S.formWeight_quotMat _ (L.arch_det_ne_zero v), S.formWeight_quotMat_ker _
        (L.arch_det_ne_zero v), add_sub_cancel_left]
      rfl
  have hf : ∀ v, Submodule.formWeight (matrixForms ((L.quotSystem S c).fin v))
      ((L.quotExp S c).fin v) U =
      Submodule.formWeight (matrixForms (L.fin v)) (c.fin v) (U.comap (S.projLin Ω)) -
        Submodule.formWeight (matrixForms (L.fin v)) (c.fin v) (LinearMap.ker (S.projLin Ω)) :=
    fun v ↦ by
      rw [S.formWeight_quotMat _ (L.fin_det_ne_zero v), S.formWeight_quotMat_ker _
        (L.fin_det_ne_zero v), add_sub_cancel_left]
      rfl
  simp only [ha, hf, sum_sub_distrib]
  ring

/-! ### Comparing twisted heights through matrices -/

section Compare

variable {ι₀ ι₁ ι₂ : Type*} [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁]
  [DecidableEq ι₂] {L₁ : FormSystem K ι₁} {a₁ : FormWeight K ι₁} {L₂ : FormSystem K ι₂}
  {a₂ : FormWeight K ι₂} {Φ₁ : Matrix ι₁ ι₀ K} {Φ₂ : Matrix ι₂ ι₀ K}
  {Ma : InfinitePlace K → Matrix ι₂ ι₁ K} {Mf : FinitePlace K → Matrix ι₂ ι₁ K}
  {B : InfinitePlace K → ℝ} {B' : FinitePlace K → ℝ}
  (harch : ∀ v, L₂.arch v * Φ₂ = Ma v * (L₁.arch v * Φ₁))
  (hfin : ∀ v, L₂.fin v * Φ₂ = Mf v * (L₁.fin v * Φ₁))
  (harch_le : ∀ v i j, Ma v i j ≠ 0 → a₁.arch v j ≤ a₂.arch v i)
  (hfin_le : ∀ v i j, Mf v i j ≠ 0 → a₁.fin v j ≤ a₂.fin v i)
  (hB : ∀ v, 0 < B v) (hB' : ∀ v, 0 < B' v) (hMa : ∀ v i j, v (Ma v i j) ≤ B v)
  (hMf : ∀ v i j, v (Mf v i j) ≤ B' v) (hB'f : B'.HasFiniteMulSupport)
variable {E : Type*} [Field E] [NumberField E] [Algebra K E]

omit [NumberField E] in
include harch harch_le hB hMa in
theorem archFactor_le_of_mul_eq (w : InfinitePlace E) (x : ι₀ → E) :
    L₂.archFactor a₂ w (Φ₂.map (algebraMap K E) *ᵥ x) ≤
      Fintype.card ι₁ * B (w.comap (algebraMap K E)) *
        L₁.archFactor a₁ w (Φ₁.map (algebraMap K E) *ᵥ x) := by
  set v := w.comap (algebraMap K E)
  set y := (L₁.arch v).map (algebraMap K E) *ᵥ (Φ₁.map (algebraMap K E) *ᵥ x)
  have hy : (L₂.arch v).map (algebraMap K E) *ᵥ (Φ₂.map (algebraMap K E) *ᵥ x) =
      (Ma v).map (algebraMap K E) *ᵥ y := by
    simp only [y, Matrix.mulVec_mulVec, ← Matrix.map_mul, harch v]
  have hF := L₁.archFactor_nonneg a₁ w (Φ₁.map (algebraMap K E) *ᵥ x)
  have hyj : ∀ j, w (y j) ≤ a₁.arch v j * L₁.archFactor a₁ w (Φ₁.map (algebraMap K E) *ᵥ x) :=
    fun j ↦ by
      rw [← div_le_iff₀' (a₁.arch_pos v j)]
      exact Finite.le_ciSup_of_le (f := fun j ↦ w (y j) / a₁.arch v j) j le_rfl
  refine Real.iSup_le (fun i ↦ ?_) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB v).le) hF)
  change w (((L₂.arch v).map (algebraMap K E) *ᵥ (Φ₂.map (algebraMap K E) *ᵥ x)) i) /
    a₂.arch v i ≤ _
  rw [hy, div_le_iff₀ (a₂.arch_pos v i)]
  calc w (((Ma v).map (algebraMap K E) *ᵥ y) i)
      ≤ ∑ j, w ((Ma v).map (algebraMap K E) i j) * w (y j) := by
        simp only [Matrix.mulVec, dotProduct, ← map_mul]
        exact AbsoluteValue.sum_le _ _ _
    _ ≤ ∑ _j : ι₁, B v * (L₁.archFactor a₁ w (Φ₁.map (algebraMap K E) *ᵥ x) * a₂.arch v i) := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        rw [Matrix.map_apply, ← InfinitePlace.comap_apply]
        by_cases hM : Ma v i j = 0
        · rw [hM, map_zero, zero_mul]
          exact mul_nonneg (hB v).le (mul_nonneg hF (a₂.arch_pos v i).le)
        · refine mul_le_mul (hMa v i j) ((hyj j).trans ?_) (apply_nonneg _ _) (hB v).le
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (harch_le v i j hM) hF
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

include hfin hfin_le hB' hMf in
theorem finFactor_le_of_mul_eq (w : FinitePlace E) (x : ι₀ → E) :
    L₂.finFactor a₂ w (Φ₂.map (algebraMap K E) *ᵥ x) ≤
      B' (w.under K) ^ w.localDegree K * L₁.finFactor a₁ w (Φ₁.map (algebraMap K E) *ᵥ x) := by
  set v := w.under K
  set e := w.localDegree K
  set y := (L₁.fin v).map (algebraMap K E) *ᵥ (Φ₁.map (algebraMap K E) *ᵥ x)
  have hy : (L₂.fin v).map (algebraMap K E) *ᵥ (Φ₂.map (algebraMap K E) *ᵥ x) =
      (Mf v).map (algebraMap K E) *ᵥ y := by
    simp only [y, Matrix.mulVec_mulVec, ← Matrix.map_mul, hfin v]
  have hF := L₁.finFactor_nonneg a₁ w (Φ₁.map (algebraMap K E) *ᵥ x)
  have hyj : ∀ j, w (y j) ≤ a₁.fin v j ^ e * L₁.finFactor a₁ w (Φ₁.map (algebraMap K E) *ᵥ x) :=
    fun j ↦ by
      rw [← div_le_iff₀' (pow_pos (a₁.fin_pos v j) e)]
      exact Finite.le_ciSup_of_le (f := fun j ↦ w (y j) / a₁.fin v j ^ e) j le_rfl
  have hna : IsNonarchimedean (w ·) := FinitePlace.add_le w
  refine Real.iSup_le (fun i ↦ ?_) (mul_nonneg (pow_nonneg (hB' v).le _) hF)
  change w (((L₂.fin v).map (algebraMap K E) *ᵥ (Φ₂.map (algebraMap K E) *ᵥ x)) i) /
    a₂.fin v i ^ e ≤ _
  rw [hy, div_le_iff₀ (pow_pos (a₂.fin_pos v i) e)]
  have hterm : ∀ j, w ((Mf v).map (algebraMap K E) i j * y j) ≤
      B' v ^ e * L₁.finFactor a₁ w (Φ₁.map (algebraMap K E) *ᵥ x) * a₂.fin v i ^ e := fun j ↦ by
    rw [map_mul, Matrix.map_apply, FinitePlace.apply_algebraMap w v]
    by_cases hM : Mf v i j = 0
    · rw [hM, map_zero, zero_pow (FinitePlace.localDegree_pos w).ne', zero_mul]
      exact mul_nonneg (mul_nonneg (pow_nonneg (hB' v).le _) hF) (pow_nonneg (a₂.fin_pos v i).le _)
    · rw [mul_assoc]
      refine mul_le_mul (pow_le_pow_left₀ (apply_nonneg _ _) (hMf v i j) _) ((hyj j).trans ?_)
        (apply_nonneg _ _) (pow_nonneg (hB' v).le _)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (a₁.fin_pos v j).le (hfin_le v i j hM) _) hF
  rcases isEmpty_or_nonempty ι₁ with hι | hι
  · simp only [Matrix.mulVec, dotProduct, Finset.univ_eq_empty, Finset.sum_empty, map_zero]
    exact mul_nonneg (mul_nonneg (pow_nonneg (hB' v).le _) hF) (pow_nonneg (a₂.fin_pos v i).le _)
  obtain ⟨j, -, hj⟩ := hna.finset_image_add_of_nonempty
    (fun j ↦ (Mf v).map (algebraMap K E) i j * y j) Finset.univ_nonempty
  exact hj.trans (hterm j)

private theorem prod_places_le {F : Type*} [Field F] [NumberField F] {f g : InfinitePlace F → ℝ}
    {f' g' : FinitePlace F → ℝ}
    (hf : ∀ v, 0 ≤ f v) (hf' : ∀ v, 0 ≤ f' v) (hfs : f'.HasFiniteMulSupport)
    (hgs : g'.HasFiniteMulSupport) (h : ∀ v, f v ≤ g v) (h' : ∀ v, f' v ≤ g' v) :
    (∏ v, f v ^ v.mult) * ∏ᶠ v, f' v ≤ (∏ v, g v ^ v.mult) * ∏ᶠ v, g' v :=
  mul_le_mul (Finset.prod_le_prod₀ (fun v _ ↦ pow_nonneg (hf v) _)
      fun v _ ↦ pow_le_pow_left₀ (hf v) (h v) _)
    (Twist.finprod_le_finprod_of_nonneg hfs hgs hf' h')
    (finprod_nonneg hf') (Finset.prod_nonneg fun v _ ↦ pow_nonneg ((hf v).trans (h v)) _)

include harch hfin harch_le hfin_le hB hB' hMa hMf hB'f in
/-- **Comparing twisted heights**, relative to `E`: if `L₂^{(v)} Φ₂ = M_v L₁^{(v)} Φ₁` with
`M_v` supported where the weights increase, then
`H₂(Φ₂ x) ≤ |ι₁|^{[E:ℚ]} (∏_v B_v^{mult v} ∏_v B'_v)^{[E:K]} H₁(Φ₁ x)`, `B`, `B'` bounds for the
entries of `M`. -/
theorem mulHeight_le_of_mul_eq (x : ι₀ → E) :
    L₂.mulHeight a₂ (Φ₂.map (algebraMap K E) *ᵥ x) ≤
      (Fintype.card ι₁ : ℝ) ^ finrank ℚ E * ((∏ v, B v ^ v.mult) * ∏ᶠ v, B' v) ^ finrank K E *
        L₁.mulHeight a₁ (Φ₁.map (algebraMap K E) *ᵥ x) := by
  have hR : 0 < (∏ v, B v ^ v.mult) * ∏ᶠ v, B' v :=
    mul_pos (Finset.prod_pos fun v _ ↦ pow_pos (hB v) _)
      (by rw [finprod_eq_prod _ hB'f]; exact Finset.prod_pos fun v _ ↦ hB' v)
  by_cases h₂ : Φ₂.map (algebraMap K E) *ᵥ x = 0
  · rw [h₂, mulHeight_zero]
    exact mul_nonneg (by positivity) (L₁.mulHeight_nonneg a₁ _)
  have h₁ : Φ₁.map (algebraMap K E) *ᵥ x ≠ 0 := by
    intro h
    obtain ⟨v₀⟩ : Nonempty (InfinitePlace K) := inferInstance
    refine mulVec_ne_zero_of_det_ne_zero (L₂.arch_det_ne_zero v₀) h₂ ?_
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, harch v₀, Matrix.map_mul, Matrix.map_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hF₂ := L₂.hasFiniteMulSupport_finFactor a₂ h₂
  have hF₁ := L₁.hasFiniteMulSupport_finFactor a₁ h₁
  have hFB : (fun w : FinitePlace E ↦ B' (w.under K) ^ w.localDegree K).HasFiniteMulSupport :=
    FinitePlace.hasFiniteMulSupport_comp_under hB'f _
  calc L₂.mulHeight a₂ (Φ₂.map (algebraMap K E) *ᵥ x)
      ≤ (∏ w : InfinitePlace E, ((Fintype.card ι₁ : ℝ) * B (w.comap (algebraMap K E)) *
            L₁.archFactor a₁ w (Φ₁.map (algebraMap K E) *ᵥ x)) ^ w.mult) *
        ∏ᶠ w : FinitePlace E, B' (w.under K) ^ w.localDegree K *
            L₁.finFactor a₁ w (Φ₁.map (algebraMap K E) *ᵥ x) :=
        prod_places_le (fun _ ↦ L₂.archFactor_nonneg a₂ _ _) (fun _ ↦ L₂.finFactor_nonneg a₂ _ _)
          hF₂ ((hFB.union hF₁).subset (Function.mulSupport_mul _ _))
          (fun w ↦ archFactor_le_of_mul_eq harch harch_le hB hMa w x)
          fun w ↦ finFactor_le_of_mul_eq hfin hfin_le hB' hMf w x
    _ = _ := by
        have h1 : ∏ w : InfinitePlace E, (Fintype.card ι₁ : ℝ) ^ w.mult =
            (Fintype.card ι₁ : ℝ) ^ finrank ℚ E := by
          rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
        have h2 : ∏ w : InfinitePlace E, B (w.comap (algebraMap K E)) ^ w.mult =
            (∏ v, B v ^ v.mult) ^ finrank K E :=
          prod_infinitePlace_pow_mult_eq _ (fun w ↦ B (w.comap (algebraMap K E))) fun _ ↦ rfl
        have h3 : ∏ᶠ w : FinitePlace E, B' (w.under K) ^ w.localDegree K =
            (∏ᶠ v, B' v) ^ finrank K E :=
          FinitePlace.finprod_under_pow_localDegree _ hB'f
        simp only [mul_pow, Finset.prod_mul_distrib]
        rw [finprod_mul_distrib hFB hF₁, h1, h2, h3, mulHeight]
        ring

include harch hfin harch_le hfin_le hB hB' hMa hMf hB'f in
/-- **Comparing absolute twisted heights**: `H₂(Φ₂ x) ≤ |ι₁| (∏_v B_v^{mult v} ∏_v B'_v)^{1/[K:ℚ]}
H₁(Φ₁ x)`. -/
theorem absMulHeight_le_of_mul_eq {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (x : ι₀ → Ω) :
    L₂.absMulHeight a₂ (Φ₂.map (algebraMap K Ω) *ᵥ x) ≤
      Fintype.card ι₁ * ((∏ v, B v ^ v.mult) * ∏ᶠ v, B' v) ^ ((finrank ℚ K : ℝ))⁻¹ *
        L₁.absMulHeight a₁ (Φ₁.map (algebraMap K Ω) *ᵥ x) := by
  have := Twist.numberField_adjoin_range (K := K) x
  set F := IntermediateField.adjoin K (Set.range x)
  have : Module.Finite K F := Module.Finite.of_restrictScalars_finite ℚ K _
  set y : ι₀ → F := fun i ↦ ⟨x i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have hR : 0 < (∏ v, B v ^ v.mult) * ∏ᶠ v, B' v :=
    mul_pos (Finset.prod_pos fun v _ ↦ pow_pos (hB v) _)
      (by rw [finprod_eq_prod _ hB'f]; exact Finset.prod_pos fun v _ ↦ hB' v)
  have hval₁ : Φ₁.map (algebraMap K Ω) *ᵥ x = F.val ∘ (Φ₁.map (algebraMap K F) *ᵥ y) := by
    funext i
    simp [Matrix.mulVec, dotProduct, y]
  have hval₂ : Φ₂.map (algebraMap K Ω) *ᵥ x = F.val ∘ (Φ₂.map (algebraMap K F) *ᵥ y) := by
    funext i
    simp [Matrix.mulVec, dotProduct, y]
  rw [hval₁, hval₂, absMulHeight_algHom, absMulHeight_algHom]
  have hn : (0 : ℝ) ≤ Fintype.card ι₁ := Nat.cast_nonneg _
  have hdF : finrank ℚ F ≠ 0 := Module.finrank_pos.ne'
  have h := mulHeight_le_of_mul_eq harch hfin harch_le hfin_le hB hB' hMa hMf hB'f (E := F) y
  have h' := Real.rpow_le_rpow (L₂.mulHeight_nonneg a₂ _) h
    (inv_nonneg.mpr (Nat.cast_nonneg (finrank ℚ F)))
  rwa [Real.mul_rpow (by positivity) (L₁.mulHeight_nonneg a₁ _),
    Real.mul_rpow (pow_nonneg hn _) (pow_nonneg hR.le _), Real.pow_rpow_inv_natCast hn hdF,
    rpow_finrank_inv hR] at h'

omit [DecidableEq ι₁] [DecidableEq ι₂] in
/-- `∏_{i,j} max 1 v(M_v i j)` is `1` at all but finitely many places when the `M_v` are
finitely many. -/
theorem hasFiniteMulSupport_prod_max (Mf : FinitePlace K → Matrix ι₂ ι₁ K)
    (hM : (Set.range Mf).Finite) :
    (fun v : FinitePlace K ↦ ∏ i, ∏ j, max 1 (v (Mf v i j))).HasFiniteMulSupport := by
  classical
  have hfin : ∀ N : Matrix ι₂ ι₁ K, ∀ i j, {v : FinitePlace K | 1 < v (N i j)}.Finite := by
    intro N i j
    by_cases hN : N i j = 0
    · exact Set.finite_empty.subset fun v hv ↦ by
        simp only [Set.mem_ofPred_eq, hN, map_zero] at hv
        linarith
    · exact (FinitePlace.hasFiniteMulSupport hN).subset fun v hv ↦ by
        simp only [Set.mem_ofPred_eq] at hv
        exact hv.ne'
  refine (hM.biUnion fun N _ ↦ Set.finite_iUnion fun i ↦ Set.finite_iUnion fun j ↦
    hfin N i j).subset fun v hv ↦ ?_
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_one_of_prod_ne_one hv
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_one_of_prod_ne_one hi
  have : 1 < v (Mf v i j) := by
    by_contra h
    exact hj (max_eq_left (not_lt.1 h))
  exact Set.mem_biUnion ⟨v, rfl⟩ (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, this⟩⟩)

omit [DecidableEq ι₁] [DecidableEq ι₂] in
private theorem single_le_prod_of_one_le {κ : Type*} [Fintype κ] {f : κ → ℝ}
    (hf : ∀ i, 1 ≤ f i) (a : κ) : f a ≤ ∏ i, f i := by
  classical
  rw [← Finset.mul_prod_erase _ f (Finset.mem_univ a)]
  exact le_mul_of_one_le_right (zero_le_one.trans (hf a)) (Finset.one_le_prod₀ fun i _ ↦ hf i)

omit [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] in
/-- The exponents `Q ^ c` increase with `c` for `Q ≥ 1`. -/
theorem weight_arch_le {c₁ : FormExponent K ι₁} {c₂ : FormExponent K ι₂} {Q : ℝ} (hQ : 1 ≤ Q)
    {v : InfinitePlace K} {i : ι₂} {j : ι₁} (h : c₁.arch v j ≤ c₂.arch v i) :
    (c₁.weight (zero_lt_one.trans_le hQ)).arch v j ≤
      (c₂.weight (zero_lt_one.trans_le hQ)).arch v i :=
  Real.rpow_le_rpow_of_exponent_le hQ (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)) (Nat.cast_nonneg _))

omit [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] in
theorem weight_fin_le {c₁ : FormExponent K ι₁} {c₂ : FormExponent K ι₂} {Q : ℝ} (hQ : 1 ≤ Q)
    {v : FinitePlace K} {i : ι₂} {j : ι₁} (h : c₁.fin v j ≤ c₂.fin v i) :
    (c₁.weight (zero_lt_one.trans_le hQ)).fin v j ≤
      (c₂.weight (zero_lt_one.trans_le hQ)).fin v i :=
  Real.rpow_le_rpow_of_exponent_le hQ (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _))

/-- **Comparing the heights `H_{L,c,Q}`**: if `L₂^{(v)} Φ₂ = M_v L₁^{(v)} Φ₁` with `M_v`
supported where `c₁ ≤ c₂`, and the `M_v` at the finite places are finitely many, then
`H_{L₂,c₂,Q}(Φ₂ x) ≤ C H_{L₁,c₁,Q}(Φ₁ x)` for all `Q ≥ 1`, with `C` independent of `Q`. -/
theorem exists_absMulHeight_weight_le {c₁ : FormExponent K ι₁} {c₂ : FormExponent K ι₂}
    (harch : ∀ v, L₂.arch v * Φ₂ = Ma v * (L₁.arch v * Φ₁))
    (hfin : ∀ v, L₂.fin v * Φ₂ = Mf v * (L₁.fin v * Φ₁))
    (harch_le : ∀ v i j, Ma v i j ≠ 0 → c₁.arch v j ≤ c₂.arch v i)
    (hfin_le : ∀ v i j, Mf v i j ≠ 0 → c₁.fin v j ≤ c₂.fin v i) (hM : (Set.range Mf).Finite)
    {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] :
    ∃ C, 0 < C ∧ ∀ Q (hQ : 1 ≤ Q) (x : ι₀ → Ω),
      L₂.absMulHeight (c₂.weight (zero_lt_one.trans_le hQ)) (Φ₂.map (algebraMap K Ω) *ᵥ x) ≤
        C * L₁.absMulHeight (c₁.weight (zero_lt_one.trans_le hQ))
          (Φ₁.map (algebraMap K Ω) *ᵥ x) := by
  set B : InfinitePlace K → ℝ := fun v ↦ ∏ i, ∏ j, max 1 (v (Ma v i j))
  set B' : FinitePlace K → ℝ := fun v ↦ ∏ i, ∏ j, max 1 (v (Mf v i j))
  have hle : ∀ (f : ι₂ → ι₁ → K) (g : K → ℝ) i j,
      g (f i j) ≤ ∏ i, ∏ j, max 1 (g (f i j)) := by
    intro f g i j
    refine (le_max_right 1 _).trans ?_
    refine (single_le_prod_of_one_le (f := fun i ↦ ∏ j, max 1 (g (f i j)))
      (fun i ↦ Finset.one_le_prod₀ fun j _ ↦ le_max_left _ _) i).trans' ?_
    exact single_le_prod_of_one_le (f := fun j ↦ max 1 (g (f i j))) (fun j ↦ le_max_left _ _) j
  have hpos : ∀ (f : ι₂ → ι₁ → K) (g : K → ℝ), 0 < ∏ i, ∏ j, max 1 (g (f i j)) :=
    fun f g ↦ Finset.prod_pos fun i _ ↦ Finset.prod_pos fun j _ ↦
      zero_lt_one.trans_le (le_max_left _ _)
  have hB'f : B'.HasFiniteMulSupport := hasFiniteMulSupport_prod_max Mf hM
  have hR : 0 < (∏ v, B v ^ v.mult) * ∏ᶠ v, B' v :=
    mul_pos (Finset.prod_pos fun v _ ↦ pow_pos (hpos _ _) _)
      (by rw [finprod_eq_prod _ hB'f]; exact Finset.prod_pos fun v _ ↦ hpos _ _)
  refine ⟨(Fintype.card ι₁ + 1) * ((∏ v, B v ^ v.mult) * ∏ᶠ v, B' v) ^ ((finrank ℚ K : ℝ))⁻¹,
    mul_pos (Nat.cast_add_one_pos _) (Real.rpow_pos_of_pos hR _), fun Q hQ x ↦ ?_⟩
  refine (absMulHeight_le_of_mul_eq harch hfin (fun v i j h ↦ weight_arch_le hQ (harch_le v i j h))
    (fun v i j h ↦ weight_fin_le hQ (hfin_le v i j h)) (fun v ↦ hpos _ _) (fun v ↦ hpos _ _)
    (fun v i j ↦ hle (Ma v) (fun a ↦ v a) i j) (fun v i j ↦ hle (Mf v) (fun a ↦ v a) i j) hB'f
    x).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
    (Real.rpow_pos_of_pos hR _).le) (L₁.absMulHeight_nonneg _ _)

end Compare

/-! ### EF13 Lemma 16.3 -/

section Lemma163

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

theorem finite_range_comp_fin_exp {β : Type*} (f : Matrix (Fin n) (Fin n) K → (Fin n → ℝ) → β) :
    (Set.range fun v : FinitePlace K ↦ f (L.fin v) (c.fin v)).Finite :=
  ((L.finite_range_fin_exp c).image fun p ↦ f p.1 p.2).subset <| by
    rintro _ ⟨v, rfl⟩
    exact ⟨_, ⟨v, rfl⟩, rfl⟩

/-- **EF13 Lemma 16.3 (i)**, first half: `H_{L',c',Q}(y) ≪ H_{L,c,Q}(φ' y)` for `Q ≥ 1`. -/
theorem exists_absMulHeight_restrictSystem_le :
    ∃ C, 0 < C ∧ ∀ Q (hQ : 1 ≤ Q) (y : Fin k → Ω),
      (L.restrictSystem S c).absMulHeight ((L.restrictExp S c).weight (zero_lt_one.trans_le hQ))
        y ≤ C * L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) (S.inclLin Ω y) := by
  obtain ⟨C, hC, h⟩ := exists_absMulHeight_weight_le (L₂ := L.restrictSystem S c)
    (L₁ := L) (Φ₂ := 1) (Φ₁ := S.incl) (c₂ := L.restrictExp S c) (c₁ := c)
    (Ma := fun v ↦ Splitting.selMat (S.sel (L.arch v) (c.arch v)))
    (Mf := fun v ↦ Splitting.selMat (S.sel (L.fin v) (c.fin v)))
    (fun v ↦ by rw [Matrix.mul_one, Splitting.selMat_mul]; rfl)
    (fun v ↦ by rw [Matrix.mul_one, Splitting.selMat_mul]; rfl)
    (fun v i j hij ↦ by rw [← Splitting.le_of_selMat_ne_zero hij]; rfl)
    (fun v i j hij ↦ by rw [← Splitting.le_of_selMat_ne_zero hij]; rfl)
    (L.finite_range_comp_fin_exp c fun A c ↦ Splitting.selMat (S.sel A c)) (Ω := Ω)
  refine ⟨C, hC, fun Q hQ y ↦ ?_⟩
  have := h Q hQ y
  rwa [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec] at this

/-- **EF13 Lemma 16.3 (i)**, second half: `H_{L,c,Q}(φ' y) ≪ H_{L',c',Q}(y)` for `Q ≥ 1`. -/
theorem exists_absMulHeight_le_restrictSystem :
    ∃ C, 0 < C ∧ ∀ Q (hQ : 1 ≤ Q) (y : Fin k → Ω),
      L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) (S.inclLin Ω y) ≤
        C * (L.restrictSystem S c).absMulHeight
          ((L.restrictExp S c).weight (zero_lt_one.trans_le hQ)) y := by
  obtain ⟨C, hC, h⟩ := exists_absMulHeight_weight_le (L₂ := L) (L₁ := L.restrictSystem S c)
    (Φ₂ := S.incl) (Φ₁ := 1) (c₂ := c) (c₁ := L.restrictExp S c)
    (Ma := fun v ↦ S.coeffMat (L.arch v) (c.arch v))
    (Mf := fun v ↦ S.coeffMat (L.fin v) (c.fin v))
    (fun v ↦ by rw [Matrix.mul_one]; exact S.mul_incl_eq _ (L.arch_det_ne_zero v))
    (fun v ↦ by rw [Matrix.mul_one]; exact S.mul_incl_eq _ (L.fin_det_ne_zero v))
    (fun v i j hij ↦ S.le_of_coeffMat_ne_zero _ (L.arch_det_ne_zero v) hij)
    (fun v i j hij ↦ S.le_of_coeffMat_ne_zero _ (L.fin_det_ne_zero v) hij)
    (L.finite_range_comp_fin_exp c fun A c ↦ S.coeffMat A c) (Ω := Ω)
  refine ⟨C, hC, fun Q hQ y ↦ ?_⟩
  have := h Q hQ y
  rwa [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec] at this

/-- **EF13 Lemma 16.3 (ii)**: `H_{L'',c'',Q}(φ'' x) ≪ H_{L,c,Q}(x)` for `Q ≥ 1`. -/
theorem exists_absMulHeight_quotSystem_le :
    ∃ C, 0 < C ∧ ∀ Q (hQ : 1 ≤ Q) (x : Fin n → Ω),
      (L.quotSystem S c).absMulHeight ((L.quotExp S c).weight (zero_lt_one.trans_le hQ))
        (S.projLin Ω x) ≤ C * L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x := by
  obtain ⟨C, hC, h⟩ := exists_absMulHeight_weight_le (L₂ := L.quotSystem S c) (L₁ := L)
    (Φ₂ := S.proj) (Φ₁ := 1) (c₂ := L.quotExp S c) (c₁ := c)
    (Ma := fun v ↦ S.quotCoeff (L.arch v) (c.arch v))
    (Mf := fun v ↦ S.quotCoeff (L.fin v) (c.fin v))
    (fun v ↦ by rw [Matrix.mul_one]; exact (S.quotCoeff_mul _ (L.arch_det_ne_zero v)).symm)
    (fun v ↦ by rw [Matrix.mul_one]; exact (S.quotCoeff_mul _ (L.fin_det_ne_zero v)).symm)
    (fun v i j hij ↦ S.le_of_quotCoeff_ne_zero _ (L.arch_det_ne_zero v) hij)
    (fun v i j hij ↦ S.le_of_quotCoeff_ne_zero _ (L.fin_det_ne_zero v) hij)
    (L.finite_range_comp_fin_exp c fun A c ↦ S.quotCoeff A c) (Ω := Ω)
  refine ⟨C, hC, fun Q hQ x ↦ ?_⟩
  have := h Q hQ x
  rwa [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec] at this

end Lemma163

end FormSystem

end NumberField
