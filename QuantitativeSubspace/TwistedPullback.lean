/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.TwistedCalculus
public import Mathlib.Analysis.Matrix.Order

-- Used only inside proofs.
import ArithmeticHeights.RowSpace
import ArithmeticHeights.CauchyBinet

/-!
# Pulling a twisted height back along an injective map

D. Roy and J. L. Thunder, *An absolute Siegel's lemma*, J. reine angew. Math. **476** (1996),
1–26, Lemma 3.2 and Proposition 4.2 with the determinant identity of Corollary 4.3: for a twist
`A` of `Kⁿ` and an injective `K`-linear map `P : Kᵐ → Kⁿ` there is a twist `B` of `Kᵐ` with

```text
H_A(P y) = H_B(y)   for every y ∈ Ωᵐ,      |det B|_𝔸 = H_A(P Ωᵐ).
```

RT build `B` from Lemma 3.2(i), a norm-preserving reparametrization of `A_v P` at each place.
In the carrier of Q2.0 a finite component must be `K`-rational, so we do not orthonormalize there
but read the max norm off a **maximal minor**: if the `m × m` minor `N` of `M = A_v P` on the rows
`s` has the largest absolute value, Cramer's rule writes every row of `M` as a combination of the
rows of `N` with coefficients of absolute value at most `1`, so `‖M y‖ = ‖N y‖` for every `y`,
over every extension. At an infinite place `B_φ` is the positive square root of the Gram matrix
`(A_φ P)ᴴ (A_φ P)`; its uniqueness makes the conjugation condition automatic.

## Main definitions

* `NumberField.Twist.pullback A P hP`: the twist `B`, for `P : Matrix ι (Fin m) K` with linearly
  independent columns.

## Main results

* `Matrix.iSup_mulVec_eq_of_isMaxMinor`: the maximal-minor identity at a nonarchimedean
  absolute value.
* `NumberField.Twist.absMulHeight_pullback`: `H_B(y) = H_A(P y)` (RT96 (4.1)).
* `NumberField.Twist.absDet_pullback`: `|det B|_𝔸 = H_A(P Ωᵐ)` (RT96 Cor. 4.3).

This is milestone Q2.2a of `QuantitativeSubspace/README.md` (its third part).
-/

@[expose] public section

open Finset Function Module Matrix exteriorPower IntermediateField

namespace Matrix

/-! ### Ultrametric linear algebra -/

section Nonarch

variable {L : Type*} [Field L] {v : AbsoluteValue L ℝ}

private theorem apply_sum_le (hv : IsNonarchimedean v) {α : Type*} (s : Finset α) (f : α → L)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ a ∈ s, v (f a) ≤ c) : v (∑ a ∈ s, f a) ≤ c := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simpa using hc
  · exact (hv.apply_sum_le_sup hne).trans (Finset.sup'_le _ _ h)

/-- The ultrametric bound for a matrix acting on a vector. -/
theorem apply_mulVec_le (hv : IsNonarchimedean v) {ι κ : Type*} [Fintype κ] (M : Matrix ι κ L)
    (y : κ → L) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hM : ∀ i j, v (M i j) ≤ a)
    (hy : ∀ j, v (y j) ≤ c) (i : ι) : v ((M *ᵥ y) i) ≤ a * c :=
  apply_sum_le hv _ _ (mul_nonneg ha hc) fun j _ ↦ by
    rw [map_mul]
    exact mul_le_mul (hM i j) (hy j) (v.nonneg _) ha

/-- An integral square matrix has an integral determinant. -/
theorem apply_det_le_one (hv : IsNonarchimedean v) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (N : Matrix κ κ L) (hN : ∀ i j, v (N i j) ≤ 1) : v N.det ≤ 1 := by
  rw [det_apply']
  refine apply_sum_le hv _ _ zero_le_one fun σ _ ↦ ?_
  have h1 : v ((Equiv.Perm.sign σ : ℤ) : L) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  rw [map_mul, h1, one_mul, map_prod]
  exact Finset.prod_le_one₀ (fun _ _ ↦ v.nonneg _) fun i _ ↦ hN _ _

private theorem iSup_nonneg' {κ : Type*} (f : κ → L) : 0 ≤ ⨆ j, v (f j) :=
  Real.iSup_nonneg fun _ ↦ v.nonneg _

private theorem le_iSup' {κ : Type*} [Finite κ] (f : κ → L) (j : κ) : v (f j) ≤ ⨆ j, v (f j) :=
  Finite.le_ciSup_of_le j le_rfl

/-- **An integral matrix with a unit determinant preserves the max norm.** -/
theorem iSup_mulVec_eq_of_det (hv : IsNonarchimedean v) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (N : Matrix κ κ L) (hN : ∀ i j, v (N i j) ≤ 1) (hdet : v N.det = 1) (y : κ → L) :
    ⨆ i, v ((N *ᵥ y) i) = ⨆ j, v (y j) := by
  have hdet0 : N.det ≠ 0 := fun h ↦ by simp [h] at hdet
  refine le_antisymm (Real.iSup_le (fun i ↦ ?_) (iSup_nonneg' y)) (Real.iSup_le (fun j ↦ ?_)
    (iSup_nonneg' _))
  · simpa using apply_mulVec_le hv N y zero_le_one (iSup_nonneg' y) hN (le_iSup' y) i
  · have hinv : ∀ i j, v (N⁻¹ i j) ≤ 1 := fun i j ↦ by
      rw [inv_def, smul_apply, smul_eq_mul, map_mul, Ring.inverse_eq_inv', map_inv₀, hdet,
        inv_one, one_mul, adjugate_apply]
      refine apply_det_le_one hv _ fun a b ↦ ?_
      rcases eq_or_ne a j with rfl | ha
      · rw [updateRow_self]
        rcases eq_or_ne b i with rfl | hb <;> simp [*]
      · rw [updateRow_ne ha]
        exact hN a b
    have hy : N⁻¹ *ᵥ (N *ᵥ y) = y := by
      rw [mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet0), one_mulVec]
    conv_lhs => rw [← hy]
    simpa using apply_mulVec_le hv N⁻¹ (N *ᵥ y) zero_le_one (iSup_nonneg' _) hinv
      (le_iSup' _) j

/-- **The maximal-minor identity.** If the minor of `M` on the rows `s` is nonzero and has the
largest absolute value among all `m × m` minors, then `M` and that minor give the same max norm
to every vector: by Cramer's rule each row of `M` is a combination of the rows `s` with
coefficients of absolute value at most `1`. -/
theorem iSup_mulVec_eq_of_isMaxMinor (hv : IsNonarchimedean v) {ι κ : Type*} [Finite ι]
    [Fintype κ] [DecidableEq κ] (M : Matrix ι κ L) (s : κ → ι) (hs : (M.submatrix s id).det ≠ 0)
    (hmax : ∀ s' : κ → ι, v (M.submatrix s' id).det ≤ v (M.submatrix s id).det) (y : κ → L) :
    ⨆ i, v ((M *ᵥ y) i) = ⨆ j, v ((M.submatrix s id *ᵥ y) j) := by
  set N := M.submatrix s id
  refine le_antisymm (Real.iSup_le (fun i ↦ ?_) (iSup_nonneg' _))
    (Real.iSup_le (fun j ↦ le_iSup' (M *ᵥ y) (s j)) (iSup_nonneg' _))
  set c := M i ᵥ* N⁻¹
  have hMy : (M *ᵥ y) i = c ⬝ᵥ (N *ᵥ y) := by
    rw [dotProduct_mulVec, vecMul_vecMul, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hs),
      vecMul_one]
    rfl
  have hc : ∀ j, v (c j) ≤ 1 := fun j ↦ by
    have hcj : c j = N.det⁻¹ * (M.submatrix (Function.update s j i) id).det := by
      have hrow : N.updateRow j (M i) = M.submatrix (Function.update s j i) id := by
        ext a b
        rcases eq_or_ne a j with rfl | ha
        · simp [N]
        · simp [N, updateRow_ne ha, Function.update_of_ne ha]
      rw [← hrow, show c j = (M i ᵥ* N⁻¹) j from rfl, inv_def, vecMul_smul, Pi.smul_apply,
        smul_eq_mul, Ring.inverse_eq_inv', ← mulVec_transpose, adjugate_transpose,
        ← cramer_eq_adjugate_mulVec, cramer_apply, updateCol_transpose, det_transpose]
    rw [hcj, map_mul, map_inv₀, inv_mul_le_iff₀ ((v.pos_iff).mpr hs), mul_one]
    exact hmax _
  rw [hMy]
  refine apply_sum_le hv _ _ (iSup_nonneg' _) fun j _ ↦ ?_
  rw [map_mul]
  calc v (c j) * v ((N *ᵥ y) j) ≤ 1 * ⨆ j, v ((N *ᵥ y) j) :=
        mul_le_mul (hc j) (le_iSup' _ j) (v.nonneg _) zero_le_one
    _ = _ := one_mul _

end Nonarch

/-! ### Maximal minors and Plücker coordinates -/

section Minors

variable {L : Type*} [Field L] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

/-- The Plücker coordinates of the columns of `P` are its maximal minors on increasing rows. -/
theorem plucker_col_eq_det (P : Matrix ι (Fin m) L) (t : Set.powersetCard ι m) :
    plucker m P.col t =
      (P.submatrix ((t : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq t)) id).det := by
  rw [show P.col = Pᵀ.row from rfl, plucker_row_eq_det_submatrix, ← transpose_submatrix,
    det_transpose]

omit [Fintype ι] in
/-- **A matrix with linearly independent columns has a nonzero maximal minor.** -/
theorem exists_det_submatrix_ne_zero [Finite ι] {P : Matrix ι (Fin m) L}
    (hP : LinearIndependent L P.col) :
    ∃ s : Fin m → ι, (P.submatrix s id).det ≠ 0 := by
  have := Fintype.ofFinite ι
  obtain ⟨t, ht⟩ := Function.ne_iff.mp (plucker_ne_zero hP)
  exact ⟨_, by rwa [← plucker_col_eq_det]⟩

/-- **Every maximal minor is a Plücker coordinate up to sign**, or zero: on rows `s` that repeat
an index it vanishes, and otherwise sorting `s` permutes the rows. -/
theorem det_submatrix_eq_zero_or (P : Matrix ι (Fin m) L) (s : Fin m → ι) :
    (P.submatrix s id).det = 0 ∨ ∃ t : Set.powersetCard ι m,
      (P.submatrix s id).det = plucker m P.col t ∨
        (P.submatrix s id).det = -plucker m P.col t := by
  by_cases hs : Function.Injective s
  · right
    set σ := Tuple.sort s
    have hmono : StrictMono (s ∘ σ) :=
      (Tuple.monotone_sort s).strictMono_of_injective (hs.comp σ.injective)
    have hcard : (univ.image s).card = m := by
      rw [card_image_of_injective _ hs, card_univ, Fintype.card_fin]
    set t : Set.powersetCard ι m := ⟨univ.image s, hcard⟩
    have hemb : s ∘ σ = (univ.image s).orderEmbOfFin hcard :=
      Finset.orderEmbOfFin_unique hcard (fun x ↦ mem_image_of_mem s (mem_univ _)) hmono
    have hdet : plucker m P.col t = Equiv.Perm.sign σ * (P.submatrix s id).det := by
      rw [plucker_col_eq_det, ← det_permute, submatrix_submatrix, comp_id]
      exact congrArg (fun f ↦ (P.submatrix f id).det) hemb.symm
    refine ⟨t, ?_⟩
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] at hdet
    · left
      simpa using hdet.symm
    · right
      rw [hdet]
      simp
  · left
    obtain ⟨a, b, hab, hne⟩ : ∃ a b, s a = s b ∧ a ≠ b := by
      simpa [Function.Injective, not_forall] using hs
    exact det_zero_of_row_eq hne (by ext j; simp [hab])

variable {v : AbsoluteValue L ℝ}

/-- Every maximal minor is bounded by the largest Plücker coordinate. -/
theorem apply_det_submatrix_le_iSup (P : Matrix ι (Fin m) L) (s : Fin m → ι) :
    v (P.submatrix s id).det ≤ ⨆ t, v (plucker m P.col t) := by
  rcases det_submatrix_eq_zero_or P s with h | ⟨t, h | h⟩
  · rw [h, map_zero]
    exact Real.iSup_nonneg fun _ ↦ v.nonneg _
  · rw [h]
    exact Finite.le_ciSup_of_le t le_rfl
  · rw [h, map_neg_eq_map]
    exact Finite.le_ciSup_of_le t le_rfl

/-- At a maximal minor the largest Plücker coordinate is attained. -/
theorem iSup_plucker_col_eq (P : Matrix ι (Fin m) L) (s : Fin m → ι)
    (hmax : ∀ s' : Fin m → ι, v (P.submatrix s' id).det ≤ v (P.submatrix s id).det) :
    ⨆ t, v (plucker m P.col t) = v (P.submatrix s id).det :=
  le_antisymm (Real.iSup_le (fun t ↦ by rw [plucker_col_eq_det]; exact hmax _) (v.nonneg _))
    (apply_det_submatrix_le_iSup P s)

end Minors

/-! ### Gram matrices -/

section Gram

open scoped MatrixOrder ComplexOrder

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The square of the ℓ² norm of `M z` is read off the Gram matrix `Mᴴ M`. -/
theorem norm_toLp_mulVec_sq (M : Matrix ι κ ℂ) (z : κ → ℂ) :
    ‖(WithLp.toLp 2 (M *ᵥ z) : EuclideanSpace ℂ ι)‖ ^ 2 = (star z ⬝ᵥ ((Mᴴ * M) *ᵥ z)).re := by
  rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, EuclideanSpace.norm_sq_eq, dotProduct,
    Complex.re_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  norm_cast

/-- Two matrices with the same Gram matrix give the same ℓ² norms. -/
theorem norm_toLp_mulVec_eq_of_gram {M : Matrix ι κ ℂ} {B : Matrix κ κ ℂ} (h : Bᴴ * B = Mᴴ * M)
    (z : κ → ℂ) : ‖(WithLp.toLp 2 (B *ᵥ z) : EuclideanSpace ℂ κ)‖ =
      ‖(WithLp.toLp 2 (M *ᵥ z) : EuclideanSpace ℂ ι)‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp <| by
    rw [norm_toLp_mulVec_sq, norm_toLp_mulVec_sq, h]

omit [Fintype κ] in
private theorem map_star_eq_transpose {X : Matrix κ κ ℂ} (hX : X.IsHermitian) :
    X.map (starRingEnd ℂ) = Xᵀ := by
  ext i j
  simpa using hX.apply j i

variable [DecidableEq κ]

/-- **The positive square root of the Gram matrix** of `M`: a square matrix with the same Gram
matrix, so the same ℓ² norms (RT96 Lemma 3.2(i) at an infinite place). -/
noncomputable def gramSqrt (M : Matrix ι κ ℂ) : Matrix κ κ ℂ := CFC.sqrt (Mᴴ * M)

theorem gramSqrt_conjTranspose_mul_self (M : Matrix ι κ ℂ) :
    (gramSqrt M)ᴴ * gramSqrt M = Mᴴ * M := by
  have hG : 0 ≤ Mᴴ * M := (posSemidef_conjTranspose_mul_self M).nonneg
  rw [gramSqrt, (CFC.sqrt_nonneg (Mᴴ * M)).posSemidef.isHermitian.eq, CFC.sqrt_mul_sqrt_self _ hG]

theorem norm_toLp_gramSqrt_mulVec (M : Matrix ι κ ℂ) (z : κ → ℂ) :
    ‖(WithLp.toLp 2 (gramSqrt M *ᵥ z) : EuclideanSpace ℂ κ)‖ =
      ‖(WithLp.toLp 2 (M *ᵥ z) : EuclideanSpace ℂ ι)‖ :=
  norm_toLp_mulVec_eq_of_gram (gramSqrt_conjTranspose_mul_self M) z

theorem det_gramSqrt_ne_zero {M : Matrix ι κ ℂ} (hM : ∀ z, M *ᵥ z = 0 → z = 0) :
    (gramSqrt M).det ≠ 0 := by
  intro h0
  obtain ⟨z, hz, hBz⟩ := (exists_mulVec_eq_zero_iff (M := gramSqrt M)).mpr h0
  refine hz (hM z ?_)
  have h := norm_toLp_gramSqrt_mulVec M z
  rw [hBz, WithLp.toLp_zero, norm_zero, eq_comm, norm_eq_zero] at h
  exact (WithLp.toLp_eq_zero 2).mp h

/-- **The square root of the Gram matrix commutes with complex conjugation.** -/
theorem gramSqrt_map_conj (M : Matrix ι κ ℂ) :
    gramSqrt (M.map (starRingEnd ℂ)) = (gramSqrt M).map (starRingEnd ℂ) := by
  have hG := posSemidef_conjTranspose_mul_self M
  have hB := (CFC.sqrt_nonneg (Mᴴ * M)).posSemidef
  have hGc : (M.map (starRingEnd ℂ))ᴴ * M.map (starRingEnd ℂ) = (Mᴴ * M).map (starRingEnd ℂ) := by
    rw [Matrix.map_mul, conjTranspose_map (starRingEnd ℂ) (fun _ ↦ rfl)]
  have h1 : 0 ≤ (Mᴴ * M).map (starRingEnd ℂ) := by
    rw [map_star_eq_transpose hG.isHermitian]
    exact hG.transpose.nonneg
  have h2 : 0 ≤ (CFC.sqrt (Mᴴ * M)).map (starRingEnd ℂ) := by
    rw [map_star_eq_transpose hB.isHermitian]
    exact hB.transpose.nonneg
  simp only [gramSqrt]
  rw [hGc, CFC.sqrt_eq_iff _ _ h1 h2, ← Matrix.map_mul, CFC.sqrt_mul_sqrt_self _ hG.nonneg]

end Gram

end Matrix

namespace Matrix

variable {L : Type*} [Field L] {ι κ : Type*} [Fintype κ]

/-- A matrix with linearly independent columns is injective. -/
theorem eq_zero_of_mulVec_eq_zero_of_linearIndependent {Q : Matrix ι κ L}
    (hQ : LinearIndependent L Q.col) {z : κ → L} (h : Q *ᵥ z = 0) : z = 0 :=
  funext <| Fintype.linearIndependent_iff.mp hQ z <| funext fun i ↦ by
    simpa [mulVec, dotProduct, mul_comm] using congrFun h i

variable [Fintype ι] [DecidableEq ι]

omit [Fintype κ] in
/-- An invertible matrix keeps columns linearly independent. -/
theorem linearIndependent_col_mul {M : Matrix ι ι L} (hM : M.det ≠ 0) {Q : Matrix ι κ L}
    (hQ : LinearIndependent L Q.col) : LinearIndependent L (M * Q).col := by
  have hinj : Function.Injective M.mulVecLin :=
    mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det M).mpr hM.isUnit)
  have h : (M * Q).col = M.mulVecLin ∘ Q.col := by
    funext j i
    simp [Matrix.mul_apply, mulVec, dotProduct, col_apply]
  rw [h]
  exact hQ.map' M.mulVecLin (LinearMap.ker_eq_bot.mpr hinj)

end Matrix

namespace NumberField.Twist

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]
  (A : Twist K ι) {m : ℕ} (P : Matrix ι (Fin m) K) (hP : LinearIndependent K P.col)

/-! ### The finite components -/

/-- The rows of a fixed nonzero maximal minor of `P`. -/
noncomputable def baseRows : Fin m → ι := (exists_det_submatrix_ne_zero hP).choose

omit [NumberField K] in
theorem det_baseRows_ne_zero : (P.submatrix (baseRows P hP) id).det ≠ 0 :=
  (exists_det_submatrix_ne_zero hP).choose_spec

/-- The rows of a maximal minor of `A_v P` at the finite place `v`. -/
noncomputable def maxRows (v : FinitePlace K) : Fin m → ι :=
  haveI : Nonempty (Fin m → ι) := ⟨baseRows P hP⟩
  (Finite.exists_max fun s : Fin m → ι ↦ v ((A.fin v * P).submatrix s id).det).choose

theorem le_maxRows (v : FinitePlace K) (s : Fin m → ι) :
    v ((A.fin v * P).submatrix s id).det ≤
      v ((A.fin v * P).submatrix (A.maxRows P hP v) id).det :=
  haveI : Nonempty (Fin m → ι) := ⟨baseRows P hP⟩
  (Finite.exists_max fun s : Fin m → ι ↦ v ((A.fin v * P).submatrix s id).det).choose_spec s

theorem det_maxRows_ne_zero (v : FinitePlace K) :
    ((A.fin v * P).submatrix (A.maxRows P hP v) id).det ≠ 0 := by
  obtain ⟨s, hs⟩ :=
    exists_det_submatrix_ne_zero (linearIndependent_col_mul (A.fin_det_ne_zero v) hP)
  refine (FinitePlace.pos_iff (w := v)).mp ?_
  exact (FinitePlace.pos_iff.mpr hs).trans_le (A.le_maxRows P hP v s)

/-- The finite places where the pullback is not trivially the identity: where `A` is not, where
`P` is not integral, or where the fixed maximal minor of `P` is not a unit. -/
def badPlaces : Set (FinitePlace K) :=
  {v | A.fin v ≠ 1} ∪ {v | ∃ i j, 1 < v (P i j)} ∪
    {v | v (P.submatrix (baseRows P hP) id).det ≠ 1}

private theorem finite_setOf_one_lt (x : K) : {v : FinitePlace K | 1 < v x}.Finite := by
  rcases eq_or_ne x 0 with rfl | hx
  · convert Set.finite_empty
    ext v
    simp
  · exact (FinitePlace.hasFiniteMulSupport hx).subset fun v hv ↦
      (show 1 < v x from hv).ne'

theorem finite_badPlaces : (A.badPlaces P hP).Finite :=
  (A.finite_setOf_fin_ne_one.union (Set.Finite.subset (Set.finite_iUnion fun i ↦
    Set.finite_iUnion fun j ↦ finite_setOf_one_lt (P i j)) fun v hv ↦ by
      obtain ⟨i, j, h⟩ := hv
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, h⟩⟩)).union
    ((FinitePlace.hasFiniteMulSupport (det_baseRows_ne_zero P hP)).subset fun _ hv ↦ hv)

/-! ### The pullback -/

/-- **The pullback of a twist along an injective map** (RT96 Prop. 4.2): at a complex embedding
the positive square root of the Gram matrix of `A_φ P`; at a finite place a maximal minor of
`A_v P`, or the identity where nothing needs correcting. -/
noncomputable def pullback : Twist K (Fin m) where
  arch φ := gramSqrt (A.arch φ * P.map φ)
  arch_det_ne_zero φ := by
    refine det_gramSqrt_ne_zero fun z hz ↦ ?_
    have hφ : LinearIndependent ℂ (P.map φ).col := by
      rw [← not_not (a := LinearIndependent ℂ _), ← plucker_eq_zero_iff]
      intro h0
      rw [show (P.map φ).col = fun j ↦ φ ∘ P.col j from rfl, plucker_comp_ringHom] at h0
      exact plucker_ne_zero hP (funext fun t ↦ φ.injective (by simpa using congrFun h0 t))
    rw [← mulVec_mulVec] at hz
    exact eq_zero_of_mulVec_eq_zero_of_linearIndependent hφ
      (eq_zero_of_mulVec_eq_zero (A.arch_det_ne_zero φ) hz)
  arch_conjugate φ := by
    have h : A.arch (ComplexEmbedding.conjugate φ) * P.map (ComplexEmbedding.conjugate φ) =
        (A.arch φ * P.map φ).map (starRingEnd ℂ) := by
      rw [Matrix.map_mul, A.arch_conjugate, Matrix.map_map]
      rfl
    rw [h, gramSqrt_map_conj]
  fin v := by
    classical
    exact if v ∈ A.badPlaces P hP then (A.fin v * P).submatrix (A.maxRows P hP v) id else 1
  fin_det_ne_zero v := by
    classical
    split_ifs
    · exact A.det_maxRows_ne_zero P hP v
    · simp
  finite_setOf_fin_ne_one := (A.finite_badPlaces P hP).subset fun v hv ↦ by
    classical
    by_contra h
    simp [h] at hv

@[simp] theorem pullback_arch (φ : K →+* ℂ) :
    (A.pullback P hP).arch φ = gramSqrt (A.arch φ * P.map φ) := rfl

theorem pullback_fin_of_mem {v : FinitePlace K} (hv : v ∈ A.badPlaces P hP) :
    (A.pullback P hP).fin v = (A.fin v * P).submatrix (A.maxRows P hP v) id := by
  simp [pullback, hv]

theorem pullback_fin_of_notMem {v : FinitePlace K} (hv : v ∉ A.badPlaces P hP) :
    (A.pullback P hP).fin v = 1 := by
  simp [pullback, hv]

private theorem fin_eq_one_of_notMem {v : FinitePlace K} (hv : v ∉ A.badPlaces P hP) :
    A.fin v = 1 := by
  by_contra h
  exact hv (Or.inl (Or.inl h))

private theorem integral_of_notMem {v : FinitePlace K} (hv : v ∉ A.badPlaces P hP) (i : ι)
    (j : Fin m) : v (P i j) ≤ 1 := by
  by_contra h
  exact hv (Or.inl (Or.inr ⟨i, j, lt_of_not_ge h⟩))

private theorem det_baseRows_of_notMem {v : FinitePlace K} (hv : v ∉ A.badPlaces P hP) :
    v (P.submatrix (baseRows P hP) id).det = 1 := by
  by_contra h
  exact hv (Or.inr h)

/-- Away from the bad places every maximal minor of `P` is integral, so the fixed one, a unit, is
maximal. -/
private theorem le_det_baseRows_of_notMem {v : FinitePlace K} (hv : v ∉ A.badPlaces P hP)
    (s : Fin m → ι) : v (P.submatrix s id).det ≤ v (P.submatrix (baseRows P hP) id).det := by
  rw [A.det_baseRows_of_notMem P hP hv]
  exact apply_det_le_one (v := v.1) (fun a b ↦ FinitePlace.add_le v a b) _
    fun a b ↦ A.integral_of_notMem P hP hv _ _

/-! ### The local identities -/

variable {E : Type*} [Field E] [NumberField E] [Algebra K E]

omit [NumberField E] in
/-- At a complex embedding the pullback is a reparametrization with the same Gram matrix. -/
theorem archFactor_pullback (φ : E →+* ℂ) (y : Fin m → E) :
    (A.pullback P hP).archFactor φ y = A.archFactor φ (P.map (algebraMap K E) *ᵥ y) := by
  have h : φ ∘ (P.map (algebraMap K E) *ᵥ y) = P.map (φ.comp (algebraMap K E)) *ᵥ (φ ∘ y) := by
    funext i
    rw [Function.comp_apply, RingHom.map_mulVec, Matrix.map_map]
    rfl
  rw [archFactor, archFactor, h, mulVec_mulVec, pullback_arch]
  exact norm_toLp_gramSqrt_mulVec _ _

/-- At a finite place the pullback is a maximal minor, which gives the same max norm. -/
theorem finFactor_pullback (w : FinitePlace E) (y : Fin m → E) :
    (A.pullback P hP).finFactor w y = A.finFactor w (P.map (algebraMap K E) *ᵥ y) := by
  set u := w.under K
  have hw : IsNonarchimedean w.1 := fun a b ↦ FinitePlace.add_le w a b
  have hpow (x : K) : w (algebraMap K E x) = u x ^ w.localDegree K :=
    FinitePlace.apply_algebraMap w u x
  have hdet (X : Matrix (Fin m) (Fin m) K) :
      w (X.map (algebraMap K E)).det = u X.det ^ w.localDegree K := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hpow]
  rw [finFactor, finFactor, mulVec_mulVec, ← Matrix.map_mul]
  by_cases hv : u ∈ A.badPlaces P hP
  · set M := (A.fin u * P).map (algebraMap K E)
    set s := A.maxRows P hP u
    have hs : (M.submatrix s id).det ≠ 0 := by
      rw [submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero_iff _ (algebraMap K E).injective).mpr (A.det_maxRows_ne_zero P hP u)
    have hmax (s' : Fin m → ι) : w (M.submatrix s' id).det ≤ w (M.submatrix s id).det := by
      rw [submatrix_map, submatrix_map, hdet, hdet]
      exact pow_le_pow_left₀ (apply_nonneg _ _) (A.le_maxRows P hP u s') _
    rw [A.pullback_fin_of_mem P hP hv, ← submatrix_map]
    exact (iSup_mulVec_eq_of_isMaxMinor hw M s hs hmax y).symm
  · rw [A.pullback_fin_of_notMem P hP hv, A.fin_eq_one_of_notMem P hP hv, Matrix.one_mul,
      Matrix.map_one _ (map_zero _) (map_one _), one_mulVec]
    set M := P.map (algebraMap K E)
    set s := baseRows P hP
    have hs : (M.submatrix s id).det ≠ 0 := by
      rw [submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero_iff _ (algebraMap K E).injective).mpr (det_baseRows_ne_zero P hP)
    have hmax (s' : Fin m → ι) : w (M.submatrix s' id).det ≤ w (M.submatrix s id).det := by
      rw [submatrix_map, submatrix_map, hdet, hdet]
      exact pow_le_pow_left₀ (apply_nonneg _ _) (A.le_det_baseRows_of_notMem P hP hv s') _
    have hint (a b : Fin m) : w (M.submatrix s id a b) ≤ 1 := by
      rw [show M.submatrix s id a b = algebraMap K E (P (s a) b) from rfl, hpow]
      exact pow_le_one₀ (apply_nonneg _ _) (A.integral_of_notMem P hP hv _ _)
    have hunit : w (M.submatrix s id).det = 1 := by
      rw [submatrix_map, hdet, A.det_baseRows_of_notMem P hP hv, one_pow]
    exact ((iSup_mulVec_eq_of_det hw _ hint hunit y).symm.trans
      (iSup_mulVec_eq_of_isMaxMinor hw M s hs hmax y).symm)

/-- **Pulling back the twisted height** (RT96 (4.1)) relative to a number field. -/
theorem mulHeight_pullback (y : Fin m → E) :
    (A.pullback P hP).mulHeight y = A.mulHeight (P.map (algebraMap K E) *ᵥ y) := by
  simp only [mulHeight, archFactor_pullback, finFactor_pullback]

/-! ### The determinant identity -/

omit [NumberField K] [LinearOrder ι] in
private theorem map_algebraMap_self {κ : Type*} (X : Matrix κ κ K) :
    X.map (algebraMap K K) = X := by
  ext
  simp

omit [NumberField K] [Fintype ι] [LinearOrder ι] in
private theorem comp_algebraMap_self (φ : K →+* ℂ) : φ.comp (algebraMap K K) = φ := by
  rw [Algebra.algebraMap_self, RingHom.comp_id]

/-- At a complex embedding the norm of the Plücker coordinates of `A_φ P` is `|det B_φ|`: both
squares are the Gram determinant, by Cauchy–Binet. -/
theorem archFactor_exteriorPower_pullback (φ : K →+* ℂ) :
    (A.exteriorPower m).archFactor φ (plucker m P.col) = ‖((A.pullback P hP).arch φ).det‖ := by
  set M := A.arch φ * P.map φ
  have hcol : (fun j ↦ A.arch φ *ᵥ (φ ∘ P.col j)) = M.col := by
    funext j i
    simp [M, Matrix.mul_apply, mulVec, dotProduct, col_apply]
  have hp : (A.exteriorPower m).archFactor φ (plucker m P.col) =
      ‖(WithLp.toLp 2 (plucker m M.col) : EuclideanSpace ℂ _)‖ := by
    rw [archFactor, comp_algebraMap_self, exteriorPower_arch, ← plucker_comp_ringHom,
      compound_mulVec_plucker, hcol]
  have hcb : (Mᴴ * M).det = ∑ t, star (plucker m M.col t) * plucker m M.col t := by
    rw [det_mul_eq_sum_plucker]
    refine sum_congr rfl fun t _ ↦ ?_
    rw [show Mᴴ.row = fun j ↦ starRingEnd ℂ ∘ M.col j from rfl, plucker_comp_ringHom]
    rfl
  have hsum : ∑ t, star (plucker m M.col t) * plucker m M.col t =
      ((∑ t, ‖plucker m M.col t‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact sum_congr rfl fun t _ ↦ by rw [Complex.star_def, Complex.conj_mul']
  have hB : ‖(gramSqrt M).det‖ ^ 2 = ‖(Mᴴ * M).det‖ := by
    rw [← gramSqrt_conjTranspose_mul_self, det_mul, det_conjTranspose, norm_mul, norm_star, sq]
  rw [hp, pullback_arch]
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [hB, hcb, hsum, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    EuclideanSpace.norm_sq_eq]

/-- At a finite place the largest Plücker coordinate of `A_v P` is `|det B_v|_v`. -/
theorem finFactor_exteriorPower_pullback (v : FinitePlace K) :
    (A.exteriorPower m).finFactor v (plucker m P.col) = v ((A.pullback P hP).fin v).det := by
  have hcol : (fun j ↦ A.fin v *ᵥ P.col j) = (A.fin v * P).col := by
    funext j i
    simp [Matrix.mul_apply, mulVec, dotProduct, col_apply]
  rw [finFactor, FinitePlace.under_self, exteriorPower_fin, map_algebraMap_self,
    compound_mulVec_plucker, hcol]
  by_cases hv : v ∈ A.badPlaces P hP
  · rw [A.pullback_fin_of_mem P hP hv]
    exact iSup_plucker_col_eq (v := v.1) _ _ (A.le_maxRows P hP v)
  · rw [A.pullback_fin_of_notMem P hP hv, A.fin_eq_one_of_notMem P hP hv, Matrix.one_mul,
      det_one, map_one, ← A.det_baseRows_of_notMem P hP hv]
    exact iSup_plucker_col_eq (v := v.1) _ _ (A.le_det_baseRows_of_notMem P hP hv)

theorem mulHeight_exteriorPower_pullback :
    (A.exteriorPower m).mulHeight (plucker m P.col) =
      (∏ φ : K →+* ℂ, ‖((A.pullback P hP).arch φ).det‖) *
        ∏ᶠ v : FinitePlace K, v ((A.pullback P hP).fin v).det := by
  rw [mulHeight]
  congr 1
  · exact prod_congr rfl fun φ _ ↦ A.archFactor_exteriorPower_pullback P hP φ
  · exact finprod_congr fun v ↦ A.finFactor_exteriorPower_pullback P hP v

/-! ### The absolute statements -/

section Absolute

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

/-- **Pulling back the absolute twisted height** (RT96 Prop. 4.2, (4.1)):
`H_B(x) = H_A(P x)` for every `x ∈ Ωᵐ`. -/
theorem absMulHeight_pullback (x : Fin m → Ω) :
    (A.pullback P hP).absMulHeight x = A.absMulHeight (P.map (algebraMap K Ω) *ᵥ x) := by
  have := numberField_adjoin_range (K := K) x
  set F := adjoin K (Set.range x)
  set y : Fin m → F := fun i ↦ ⟨x i, subset_adjoin K _ ⟨i, rfl⟩⟩
  have hmap : (P.map (algebraMap K F)).map (F.val : F →+* Ω) = P.map (algebraMap K Ω) := by
    ext
    rfl
  have hy : (F.val : F →+* Ω) ∘ y = x := rfl
  have hPy : P.map (algebraMap K Ω) *ᵥ x = F.val ∘ (P.map (algebraMap K F) *ᵥ y) := by
    funext i
    have h := RingHom.map_mulVec (F.val : F →+* Ω) (P.map (algebraMap K F)) y i
    rw [hmap, hy] at h
    exact h.symm
  rw [hPy, absMulHeight_algHom, ← mulHeight_pullback]
  exact (A.pullback P hP).absMulHeight_algHom F.val y

/-- **The determinant of the pullback** (RT96 Cor. 4.3): `|det B|_𝔸` is the twisted height of
the image of `P`. -/
theorem absDet_pullback :
    (A.pullback P hP).absDet =
      A.absSubspaceHeight (Submodule.span Ω (Set.range fun j ↦ algebraMap K Ω ∘ P.col j)) := by
  have hli : LinearIndependent Ω (fun j ↦ algebraMap K Ω ∘ P.col j) := by
    rw [← not_not (a := LinearIndependent Ω _), ← plucker_eq_zero_iff, plucker_comp_ringHom]
    intro h0
    exact plucker_ne_zero hP
      (funext fun t ↦ (algebraMap K Ω).injective (by simpa using congrFun h0 t))
  rw [absSubspaceHeight_span_range _ hli, plucker_comp_ringHom, absMulHeight_algebraMap,
    mulHeight_exteriorPower_pullback]
  rfl

end Absolute

end NumberField.Twist
