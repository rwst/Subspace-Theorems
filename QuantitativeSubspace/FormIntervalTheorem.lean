/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormEvalBound
public import QuantitativeSubspace.FormWedgePoints
public import QuantitativeSubspace.FormNonVanishing

/-!
# EF13 Theorem 8.1 (§14)

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, §14.

This file assembles the proof of EF13 Theorem 8.1 from the wedge points (§11,
`QuantitativeSubspace.FormWedgePoints`), the auxiliary polynomial (Prop. 13.6), the non-vanishing
result (Prop. 12.1, `QuantitativeSubspace.FormNonVanishing`) and the local bounds with the product
formula (`QuantitativeSubspace.FormEvalBound`).

* Transport of the bounds of the wedge points from their field `E_h` to a number field `F ⊇ E_h`
  containing all of them: `FormSystem.apply_mulVec_le_arch_of_le`,
  `FormSystem.apply_mulVec_le_fin_of_le`, and `FinitePlace.apply_inclusion_le` of
  `QuantitativeSubspace.FormDavenport`.
* The bounds for the integer combinations of the grid (14.7): `apply_mulVec_sum_le`,
  `apply_mulVec_sum_le_of_isNonarchimedean`.
* The hyperplane `M_h = 0` of Prop. 12.1: `Submodule.mem_extendPi_of_sum_eq_zero`.

This is milestone Q4.1d of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Finset Module Matrix Real

/-! ### Integer combinations -/

section Combination

variable {F : Type*} [Field F]

/-- An absolute value of an integer is at most its absolute value. -/
theorem AbsoluteValue.apply_intCast_le_natAbs (w : AbsoluteValue F ℝ) (z : ℤ) :
    w (z : F) ≤ z.natAbs := by
  have hn : ∀ n : ℕ, w (n : F) ≤ n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      push_cast
      calc w ((k : F) + 1) ≤ w (k : F) + w 1 := w.add_le _ _
        _ ≤ k + 1 := by rw [w.map_one]; linarith
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · rw [Int.cast_natCast, Int.natAbs_natCast]
    exact hn n
  · rw [Int.cast_neg, Int.cast_natCast, AbsoluteValue.map_neg, Int.natAbs_neg,
      Int.natAbs_natCast]
    exact hn n

/-- A sum at a nonarchimedean absolute value is bounded by a bound for its terms. -/
theorem AbsoluteValue.apply_sum_le_of_isNonarchimedean {w : AbsoluteValue F ℝ}
    (hw : IsNonarchimedean w) {α : Type*} (s : Finset α) (f : α → F) {b : ℝ} (hb : 0 ≤ b)
    (hf : ∀ i ∈ s, w (f i) ≤ b) : w (∑ i ∈ s, f i) ≤ b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hb
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (hw _ _).trans (max_le (hf a (mem_insert_self a s))
      (ih fun i hi ↦ hf i (mem_insert_of_mem hi)))

variable {σ ι' : Type*} [Fintype σ] [Fintype ι']

/-- **The grid (14.7) at an absolute value**: if `w((A u_l)_s) ≤ b` and `|z_l| ≤ B`, then
`w((A Σ_l z_l u_l)_s) ≤ #ι' B b`. -/
theorem apply_mulVec_sum_le (w : AbsoluteValue F ℝ) (A : Matrix σ σ F) (z : ι' → ℤ)
    (u : ι' → σ → F) (s : σ) {b B : ℝ} (hb : ∀ l, w ((A *ᵥ u l) s) ≤ b)
    (hz : ∀ l, ((z l).natAbs : ℝ) ≤ B) :
    w ((A *ᵥ ∑ l, (z l : F) • u l) s) ≤ Fintype.card ι' * B * b := by
  rw [mulVec_sum, Finset.sum_apply]
  calc w (∑ l, (A *ᵥ (z l : F) • u l) s) ≤ ∑ l, w ((A *ᵥ (z l : F) • u l) s) := w.sum_le _ _
    _ ≤ ∑ _l : ι', B * b := sum_le_sum fun l _ ↦ by
        rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul]
        exact mul_le_mul ((w.apply_intCast_le_natAbs _).trans (hz l)) (hb l) (w.nonneg _)
          ((Nat.cast_nonneg _).trans (hz l))
    _ = Fintype.card ι' * B * b := by rw [sum_const, card_univ, nsmul_eq_mul, mul_assoc]

/-- **The grid (14.7) at a nonarchimedean absolute value**: the integers do not count. -/
theorem apply_mulVec_sum_le_of_isNonarchimedean {w : AbsoluteValue F ℝ} (hw : IsNonarchimedean w)
    (hw1 : ∀ z : ℤ, w (z : F) ≤ 1) (A : Matrix σ σ F) (z : ι' → ℤ) (u : ι' → σ → F) (s : σ)
    {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ l, w ((A *ᵥ u l) s) ≤ b) :
    w ((A *ᵥ ∑ l, (z l : F) • u l) s) ≤ b := by
  rw [mulVec_sum, Finset.sum_apply]
  refine AbsoluteValue.apply_sum_le_of_isNonarchimedean hw _ _ hb0 fun l _ ↦ ?_
  rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  exact (mul_le_mul (hw1 _) (hb l) (w.nonneg _) zero_le_one).trans_eq (one_mul b)

end Combination

/-! ### The hyperplane of Prop. 12.1 -/

namespace Submodule

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- If `W ⊆ Kⁿ` is the hyperplane `Σ_i M_i x_i = 0`, its extension to `Ωⁿ` is the hyperplane
`Σ_i M_i x_i = 0` of `Ωⁿ`. -/
theorem mem_extendPi_of_sum_eq_zero {W : Submodule K (ι → K)} {M : ι → K} (hM : M ≠ 0)
    (hW : ∀ x, x ∈ W ↔ ∑ i, M i * x i = 0) (hdim : finrank K W + 1 = Fintype.card ι)
    {x : ι → Ω} (hx : ∑ i, algebraMap K Ω (M i) * x i = 0) : x ∈ W.extendPi Ω := by
  classical
  set f : (ι → Ω) →ₗ[Ω] Ω :=
    ∑ i, algebraMap K Ω (M i) • (LinearMap.proj i : (ι → Ω) →ₗ[Ω] Ω) with hf_def
  have hf : ∀ y, f y = ∑ i, algebraMap K Ω (M i) * y i := fun y ↦ by
    rw [hf_def, LinearMap.sum_apply]
    rfl
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hM
  have hsurj : Function.Surjective f := fun t ↦
    ⟨Pi.single i₀ ((algebraMap K Ω (M i₀))⁻¹ * t), by
      rw [hf, sum_eq_single i₀ (fun i _ hi ↦ by simp [hi]) (by simp)]
      simp [mul_inv_cancel_left₀ ((map_ne_zero _).mpr hi₀)]⟩
  have hker : finrank Ω (LinearMap.ker f) + 1 = Fintype.card ι := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
      Module.finrank_fintype_fun_eq_card] at this
    omega
  have hle : W.extendPi Ω ≤ LinearMap.ker f := by
    refine span_le.mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hf]
    have h0 := (hW y).mp hy
    have := congrArg (algebraMap K Ω) h0
    simpa [extendLin, map_sum] using this
  have heq : W.extendPi Ω = LinearMap.ker f :=
    eq_of_le_of_finrank_eq hle (by rw [finrank_extendPi]; omega)
  rw [heq, LinearMap.mem_ker, hf]
  exact hx

end Submodule

/-! ### Transport to a larger number field -/

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {Ω : Type*} [Field Ω] [Algebra K Ω]
  {E F : IntermediateField K Ω} [NumberField E] [NumberField F]

namespace FormSystem

variable {σ : Type*} [Fintype σ] [DecidableEq σ] (L : FormSystem K σ) (a : FormWeight K σ)

omit [NumberField E] [NumberField F] in
/-- An archimedean local factor `≤ 1` over `E` bounds the coordinates over `F ⊇ E`:
`‖L_s^{(v)}(x)‖_w ≤ a_{sv}`. -/
theorem apply_mulVec_le_arch_of_le (hEF : E ≤ F) {x : σ → E}
    (hx : ∀ w : InfinitePlace E, L.archFactor a w x ≤ 1) (w : InfinitePlace F) (s : σ) :
    w (((L.arch (w.comap (algebraMap K F))).map (algebraMap K F) *ᵥ
      (IntermediateField.inclusion hEF ∘ x)) s) ≤ a.arch (w.comap (algebraMap K F)) s := by
  let : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  have : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have h1 : L.archFactor a w (algebraMap E F ∘ x) ≤ 1 := by
    rw [L.archFactor_algebraMap a w x]
    exact hx _
  have h2 := (le_ciSup (Finite.bddAbove_range _) s).trans h1
  rwa [div_le_one (a.arch_pos _ s)] at h2

/-- A nonarchimedean local factor `≤ 1` over `E` off `v₀` bounds the coordinates over `F ⊇ E`:
`‖L_s^{(v)}(x)‖_w ≤ a_{sv}^{e_w}`. -/
theorem apply_mulVec_le_fin_of_le (hEF : E ≤ F) {v₀ : FinitePlace K} {x : σ → E}
    (hx : ∀ w : FinitePlace E, w.under K ≠ v₀ → L.finFactor a w x ≤ 1) (w : FinitePlace F)
    (hw : w.under K ≠ v₀) (s : σ) :
    w (((L.fin (w.under K)).map (algebraMap K F) *ᵥ (IntermediateField.inclusion hEF ∘ x)) s) ≤
      a.fin (w.under K) s ^ w.localDegree K := by
  let : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  have : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have h1 : L.finFactor a w (algebraMap E F ∘ x) ≤ 1 := by
    rw [L.finFactor_algebraMap a w x]
    exact pow_le_one₀ (L.finFactor_nonneg a _ x)
      (hx _ (by rwa [FinitePlace.under_under]))
  have h2 := (le_ciSup (Finite.bddAbove_range _) s).trans h1
  rwa [div_le_one (pow_pos (a.fin_pos _ s) _)] at h2

end FormSystem

/-- The matrices `L^{(v)}` have rows among the forms: `#matSet ≤ #forms ^ n`. -/
theorem FormSystem.card_matSet_le {ι : Type*} [Fintype ι] [LinearOrder ι] (L : FormSystem K ι) :
    #L.matSet ≤ #L.forms ^ Fintype.card ι := by
  classical
  have hsub : L.matSet ⊆ Fintype.piFinset fun _ : ι ↦ L.forms := fun B hB ↦
    Fintype.mem_piFinset.mpr fun i ↦ L.mem_forms_of_mem_matSet hB i
  have hcard : #(Fintype.piFinset fun _ : ι ↦ L.forms) = #L.forms ^ Fintype.card ι := by
    rw [Fintype.card_piFinset, prod_const, card_univ]
  exact (card_le_card hsub).trans hcard.le

end NumberField

/-! ### The degrees `r_h` (EF13 (14.8)) -/

/-- **EF13 (14.8).** For `1 < Q_0 ≤ ⋯ ≤ Q_{m-1}` (in the sense of `log`) and `0 < ε`, there
are `Λ ≥ max(1, D₀) log Q_0` and positive integers `r_h`, decreasing in `h`, with
`Λ ≤ r_h log Q_h ≤ (1 + ε) Λ` and `r_h ≤ 2 Λ / log Q_0`. -/
theorem exists_blockDegrees {m : ℕ} (hm : 0 < m) {Q : Fin m → ℝ} (hQ : ∀ h, 1 < Q h)
    (hmono : Monotone fun h ↦ Real.log (Q h)) {ε : ℝ} (hε : 0 < ε) (D₀ : ℝ) :
    ∃ (Λ : ℝ) (r : Fin m → ℕ), max 1 D₀ * Real.log (Q ⟨0, hm⟩) ≤ Λ ∧ (∀ h, 0 < r h) ∧
      Antitone r ∧ (∀ h, Λ ≤ r h * Real.log (Q h) ∧ r h * Real.log (Q h) ≤ (1 + ε) * Λ) ∧
      ∀ h, (r h : ℝ) ≤ 2 * Λ / Real.log (Q ⟨0, hm⟩) := by
  set h₀ : Fin m := ⟨0, hm⟩
  set h₁ : Fin m := ⟨m - 1, by omega⟩
  have hlog : ∀ h, 0 < Real.log (Q h) := fun h ↦ Real.log_pos (hQ h)
  have hle₀ : ∀ h, Real.log (Q h₀) ≤ Real.log (Q h) := fun h ↦
    hmono (Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
  have hle₁ : ∀ h, Real.log (Q h) ≤ Real.log (Q h₁) := fun h ↦
    hmono (Fin.le_iff_val_le_val.mpr (by simp [h₁]; omega))
  set Λ := max (Real.log (Q h₁) / ε) (max 1 D₀ * Real.log (Q h₀)) with hΛ
  have hΛ1 : max 1 D₀ * Real.log (Q h₀) ≤ Λ := le_max_right _ _
  have hΛ0 : Real.log (Q h₀) ≤ Λ :=
    (le_mul_of_one_le_left (hlog h₀).le (le_max_left _ _)).trans hΛ1
  have hΛpos : 0 < Λ := (hlog h₀).trans_le hΛ0
  have hΛε : ∀ h, Real.log (Q h) ≤ ε * Λ := fun h ↦ by
    have : Real.log (Q h₁) / ε ≤ Λ := le_max_left _ _
    rw [div_le_iff₀ hε] at this
    linarith [hle₁ h]
  set r : Fin m → ℕ := fun h ↦ ⌈Λ / Real.log (Q h)⌉₊ with hr
  have hrge : ∀ h, Λ / Real.log (Q h) ≤ r h := fun h ↦ Nat.le_ceil _
  have hrlt : ∀ h, (r h : ℝ) < Λ / Real.log (Q h) + 1 := fun h ↦
    Nat.ceil_lt_add_one (div_pos hΛpos (hlog h)).le
  refine ⟨Λ, r, hΛ1, fun h ↦ Nat.ceil_pos.mpr (div_pos hΛpos (hlog h)), fun i j hij ↦ ?_,
    fun h ↦ ⟨?_, ?_⟩, fun h ↦ ?_⟩
  · exact Nat.ceil_mono (div_le_div_of_nonneg_left hΛpos.le (hlog i) (hmono hij))
  · have := mul_le_mul_of_nonneg_right (hrge h) (hlog h).le
    rwa [div_mul_cancel₀ _ (hlog h).ne'] at this
  · have := mul_lt_mul_of_pos_right (hrlt h) (hlog h)
    rw [add_mul, div_mul_cancel₀ _ (hlog h).ne', one_mul] at this
    linarith [hΛε h]
  · have h1 : Λ / Real.log (Q h) ≤ Λ / Real.log (Q h₀) :=
      div_le_div_of_nonneg_left hΛpos.le (hlog h₀) (hle₀ h)
    have h2 : 1 ≤ Λ / Real.log (Q h₀) := (one_le_div (hlog h₀)).mpr hΛ0
    have := hrlt h
    rw [mul_div_assoc]
    linarith

/-- The ratio condition of Prop. 12.1 from (14.8) and `log Q_j ≥ (4m/ε) log Q_i`. -/
theorem div_lt_div_of_blockDegrees {Λ ε m qi qj ri rj : ℝ} (hε1 : ε ≤ 1)
    (hqi : 0 < qi) (hrj : 0 < rj) (hΛ : 0 < Λ) (h1 : rj * qj ≤ (1 + ε) * Λ)
    (h2 : 4 * m / ε * qi ≤ qj) (h3 : Λ ≤ ri * qi) : m / ε < ri / rj := by
  rw [lt_div_iff₀ hrj]
  have h5 : m / ε * rj * qi ≤ 1 / 4 * (rj * qj) := by
    have := mul_le_mul_of_nonneg_left h2 hrj.le
    have e : m / ε * rj * qi = 1 / 4 * (rj * (4 * m / ε * qi)) := by ring
    rw [e]
    linarith
  have h6 : m / ε * rj * qi < ri * qi := by
    have : 1 / 4 * (rj * qj) ≤ 1 / 4 * ((1 + ε) * Λ) := by linarith
    have : 1 / 4 * ((1 + ε) * Λ) < Λ := by nlinarith
    linarith
  exact lt_of_mul_lt_mul_right h6 hqi.le

/-- The hyperplane `M = 0` of `Ω^σ` is spanned by the points `u_J`, `J ∈ S`, if `W ⊆ K^N` is
`M = 0` and its extension is spanned by the `u_J` read through `σ ≃ Fin N`. -/
theorem Submodule.mem_span_image_of_sum_eq_zero {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    {σ ι' : Type*} [Fintype σ] {W : Submodule K (Fin (Fintype.card σ) → K)}
    {M : Fin (Fintype.card σ) → K} (hM0 : M ≠ 0) (hMW : ∀ x, x ∈ W ↔ ∑ i, M i * x i = 0)
    (hWdim : finrank K W + 1 = Fintype.card σ) (u : ι' → σ → Ω) (S : Set ι')
    (hWspan : W.extendPi Ω = span Ω ((fun J ↦ u J ∘ (Fintype.equivFin σ).symm) '' S))
    {x0 : σ → Ω} (hx0 : ∑ s, algebraMap K Ω (M (Fintype.equivFin σ s)) * x0 s = 0) :
    x0 ∈ span Ω (u '' S) := by
  set eσ := Fintype.equivFin σ
  set x1 : Fin (Fintype.card σ) → Ω := x0 ∘ eσ.symm
  have hx1 : ∑ i, algebraMap K Ω (M i) * x1 i = 0 := by
    rw [← hx0, ← Equiv.sum_comp eσ]
    simp [x1]
  have hmem := mem_extendPi_of_sum_eq_zero hM0 hMW (by rw [Fintype.card_fin]; exact hWdim) hx1
  rw [hWspan] at hmem
  have := apply_mem_span_image_of_mem_span (LinearMap.funLeft Ω Ω eσ) hmem
  have hx : LinearMap.funLeft Ω Ω eσ x1 = x0 := by
    funext s
    simp [x1, LinearMap.funLeft_apply]
  have hset : LinearMap.funLeft Ω Ω eσ '' ((fun J ↦ u J ∘ eσ.symm) '' S) = u '' S := by
    rw [Set.image_image]
    refine Set.image_congr fun J _ ↦ ?_
    funext s
    simp [LinearMap.funLeft_apply]
  rwa [hx, hset] at this

/-- The arithmetic of the height condition (12.4) of Prop. 12.1 in §14: with
`Σ r ≤ 2mΛ/log Q_0`, `r_h ≤ 2Λ/log Q_0`, `r_h log Q_h ≥ Λ`, `h(P) ≤ ½ D + Y Σ r`,
`D ≤ Λ / log Q_0` and `h(M_h) ≥ d δ/(3R) log Q_h - d/2 log N`. -/
theorem lt_mul_logHeight_aux {N' μ m d δ R Λ L₀ S hp D Y rh qh lM lN : ℝ} (hN' : 0 ≤ N')
    (hμ : 0 ≤ μ) (hm : 0 ≤ m) (hd : 0 ≤ d) (hδR : 0 ≤ δ / (3 * R)) (hΛ : 0 < Λ) (hL₀ : 0 < L₀)
    (hY : 0 ≤ Y) (hlN : 0 ≤ lN) (hS : S ≤ m * (2 * Λ / L₀)) (hP : hp ≤ 1 / 2 * D + Y * S)
    (hD : D ≤ Λ / L₀) (hrh : rh ≤ 2 * Λ / L₀) (hrq : Λ ≤ rh * qh) (hrh0 : 0 ≤ rh)
    (hlM : d * (δ / (3 * R)) * qh - d / 2 * lN ≤ lM)
    (hΘ : d * lN + N' * μ * (20 * m ^ 3 * d + m / 2 + 2 * m ^ 2 * Y) < L₀ * (d * δ / (3 * R))) :
    N' * μ * (10 * m ^ 2 * d * S + m * hp) < rh * lM := by
  set t := Λ / L₀ with ht
  have ht0 : 0 < t := div_pos hΛ hL₀
  have hS' : S ≤ 2 * m * t := by
    rw [ht]
    linarith [show m * (2 * Λ / L₀) = 2 * m * (Λ / L₀) by ring]
  have hrh' : rh ≤ 2 * t := by rw [ht]; linarith [show 2 * Λ / L₀ = 2 * (Λ / L₀) by ring]
  have hL : 10 * m ^ 2 * d * S + m * hp ≤ t * (20 * m ^ 3 * d + m / 2 + 2 * m ^ 2 * Y) := by
    have h1 : 10 * m ^ 2 * d * S ≤ 10 * m ^ 2 * d * (2 * m * t) :=
      mul_le_mul_of_nonneg_left hS' (by positivity)
    have h2 : Y * S ≤ Y * (2 * m * t) := mul_le_mul_of_nonneg_left hS' hY
    have h3 : m * hp ≤ m * (1 / 2 * t + Y * (2 * m * t)) :=
      mul_le_mul_of_nonneg_left (by linarith) hm
    nlinarith
  have hLHS : N' * μ * (10 * m ^ 2 * d * S + m * hp) ≤
      t * (N' * μ * (20 * m ^ 3 * d + m / 2 + 2 * m ^ 2 * Y)) := by
    have := mul_le_mul_of_nonneg_left hL (mul_nonneg hN' hμ)
    linarith [show N' * μ * (t * (20 * m ^ 3 * d + m / 2 + 2 * m ^ 2 * Y)) =
      t * (N' * μ * (20 * m ^ 3 * d + m / 2 + 2 * m ^ 2 * Y)) by ring]
  have hRHS : Λ * (d * (δ / (3 * R))) - t * (d * lN) ≤ rh * lM := by
    have h1 : rh * (d * (δ / (3 * R)) * qh - d / 2 * lN) ≤ rh * lM :=
      mul_le_mul_of_nonneg_left hlM hrh0
    have h2 : Λ * (d * (δ / (3 * R))) ≤ rh * qh * (d * (δ / (3 * R))) :=
      mul_le_mul_of_nonneg_right hrq (mul_nonneg hd hδR)
    have h3 : rh * (d / 2 * lN) ≤ 2 * t * (d / 2 * lN) :=
      mul_le_mul_of_nonneg_right hrh' (by positivity)
    nlinarith
  have hkey : t * (N' * μ * (20 * m ^ 3 * d + m / 2 + 2 * m ^ 2 * Y)) <
      Λ * (d * (δ / (3 * R))) - t * (d * lN) := by
    have := mul_lt_mul_of_pos_left hΘ ht0
    have e : t * (L₀ * (d * δ / (3 * R))) = Λ * (d * (δ / (3 * R))) := by
      rw [ht]
      field_simp
    nlinarith
  linarith

/-- The logarithms of (14.14)–(14.17): from `1 ≤ A_P C^d e^{dΛW}` (the product formula),
`A_P ≤ (s₀ 2^S N^S)^d H(P) H(y)^S` (Prop. 13.6 (iv)), `s₀ ≤ 2^{NS}`, `C = 2^{NS} G^S`,
`log H(P) ≤ ½ D + Y S` and `log H(y) ≤ Y₂`. -/
theorem neg_le_of_one_le_evalBound_aux {Ap s₀ G HP Hy D Y Y₂ Λ W : ℝ} {N S d : ℕ}
    (hN : 1 ≤ N) (hs₀ : 0 < s₀) (hs₀N : s₀ ≤ 2 ^ (N * S)) (hG : 1 ≤ G) (hHP : 0 < HP)
    (hHy : 0 < Hy) (h1 : 1 ≤ Ap * (2 ^ (N * S) * G ^ S) ^ d * Real.exp (d * Λ * W))
    (h2 : Ap ≤ (s₀ * 2 ^ S * N ^ S) ^ d * HP * Hy ^ S)
    (hP : Real.log HP ≤ 1 / 2 * D + Y * S) (hy : Real.log Hy ≤ Y₂) :
    -(d * Λ * W) ≤ 1 / 2 * D + S * (Y + Y₂ + d * (2 * N * Real.log 2 + Real.log 2 +
      Real.log N + Real.log G)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hG0 : 0 < G := zero_lt_one.trans_le hG
  set B := (s₀ * 2 ^ S * N ^ S) ^ d * HP * Hy ^ S with hB
  set C := (2 ^ (N * S) * G ^ S : ℝ) ^ d with hC
  have hB0 : 0 < B := by positivity
  have hC0 : 0 < C := by positivity
  have h3 : 1 ≤ B * C * Real.exp (d * Λ * W) := h1.trans (by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hC0.le) (Real.exp_pos _).le)
  have h4 := Real.log_nonneg h3
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul hB0.ne' hC0.ne',
    Real.log_exp, hB, hC, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_pow] at h4
  have h5 : Real.log s₀ ≤ (N * S : ℕ) * Real.log 2 := by
    rw [← Real.log_pow]
    exact Real.log_le_log hs₀ (by exact_mod_cast hs₀N)
  have h6 : (S : ℝ) * Real.log Hy ≤ S * Y₂ := mul_le_mul_of_nonneg_left hy (Nat.cast_nonneg _)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have h7 := mul_le_mul_of_nonneg_left h5 hd0
  push_cast at h4 h7
  nlinarith

/-- The final contradiction of §14 from the logarithmic inequality and `hΘ₂`. -/
theorem false_of_le_aux {Λ L₀ D S Z X m : ℝ} (hΛ : 0 < Λ) (hL₀ : 0 < L₀) (hZ : 0 ≤ Z)
    (hS : S ≤ m * (2 * Λ / L₀)) (hD : D ≤ Λ / L₀) (hle : Λ * X ≤ 1 / 2 * D + S * Z)
    (hΘ : 1 / 2 + 2 * m * Z < L₀ * X) : False := by
  set t := Λ / L₀ with ht
  have ht0 : 0 < t := div_pos hΛ hL₀
  have h1 : S * Z ≤ m * (2 * Λ / L₀) * Z := mul_le_mul_of_nonneg_right hS hZ
  have h2 : m * (2 * Λ / L₀) * Z = t * (2 * m * Z) := by rw [ht]; ring
  have h3 := mul_lt_mul_of_pos_left hΘ ht0
  have h4 : t * (L₀ * X) = Λ * X := by rw [ht]; field_simp
  nlinarith

/-! ### The chain (EF13 §14) -/

namespace NumberField.FormSystem

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {Ω : Type*} [Field Ω] [Algebra K Ω]
  [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] (L : FormSystem K (Fin n)) (c : FormExponent K (Fin n))

open MvPolynomial

/-- **EF13 §14: no chain of exceptional `Q`.** Let `(L, c)` satisfy (8.3), (8.4), (8.8) at `v₀`,
(8.9), and let `Q_0, …, Q_{m-1}` share the gap of Lemma 9.4 at the same `0 < k < n`, with
`log Q_{h+1} ≥ (4m/ε) log Q_h`, the size conditions of `exists_wedgePoints`, and `Q_0` so large
that Prop. 12.1 applies (`hΘ₁`) and the product formula fails (`hΘ₂`). Then this is impossible.
Here `N = C(n, n-k)`, `Y` is the coefficient of `Σ r` in Prop. 13.6 (iii), `Y₂` bounds the height
of `invTuple`, `G` bounds the grid (14.7) and `Z` collects the logarithms of (14.14)–(14.16). -/
theorem false_of_chain (hLs : L.IsNormalSemistable c Ω) {v₀ : FinitePlace K}
    (hL₀ : L.fin v₀ = 1) (hc₀ : c.fin v₀ = 0) (hn : 2 ≤ n) {R : ℕ} (hR : #L.forms ≤ R)
    (hnR : n ≤ R) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε ≤ 1) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : 2 * (#L.matSet * (n / ε + 2) ^ n + 1) ≤ Real.exp (m * ε ^ 2 / 2))
    (k : Fin n) (hk : 0 < (k : ℕ)) {Q : Fin m → ℝ} (hQ : ∀ h, 1 < Q h)
    (hω : ∀ i j : Fin m, (i : ℕ) + 1 = j → 4 * m / ε * Real.log (Q i) ≤ Real.log (Q j))
    (hgap : ∀ h, L.successiveInf (c.weight (zero_lt_one.trans (hQ h))) Ω k ≤
      Q h ^ (-(δ / (n - 1))) * L.successiveInf (c.weight (zero_lt_one.trans (hQ h))) Ω (k + 1))
    (hQ₁ : ∀ h, n * L.absFormHeight ^ ((L.forms.card.choose n : ℕ) : ℝ) ≤
      Q h ^ (1 / (3 * n) : ℝ))
    (hQ₂ : ∀ h, √2 ^ (n * (n - 1)) * L.absDet ≤ Q h ^ (1 / 6 : ℝ))
    (hQ₃ : ∀ h, (3 : ℝ) ^ (n ^ 3) ≤ Q h ^ (1 / 2 : ℝ))
    (hQ₄ : ∀ h, (3 ^ (n ^ 3) * (√2 ^ (n * (n - 1)) * L.absFormHeight)) ^ (2 ^ n) ≤
      Q h ^ (δ / (n * (n - 1))))
    (hbig : ∀ h, (2 ^ (3 * n ^ 2) * L.absFormHeight) ^ (3 * n * R ^ n) ≤ Q h ^ δ)
    {N d Y Y₂ G Z : ℝ} (hN : N = Fintype.card (Set.powersetCard (Fin n) (n - k)))
    (hd : d = finrank ℚ K)
    (hY : Y = d / 2 * N + d * Real.log N + d * Real.log (n - k : ℕ).factorial +
      2 * (n - k : ℕ) * #L.matSet * Real.log L.mulFormHeight)
    (hY₂ : Y₂ = d * Real.log (n - k : ℕ).factorial +
      2 * (n - k : ℕ) * #L.matSet * Real.log L.mulFormHeight)
    (hG : G = (N - 1) * ((N - 1) / ε + 1))
    (hZ : Z = Y + Y₂ + d * (2 * N * Real.log 2 + Real.log 2 + Real.log N + Real.log G))
    (hΘ₁ : d * Real.log N + (N - 1) * (m / ε) ^ m * (20 * m ^ 3 * d + m / 2 + 2 * m ^ 2 * Y) <
      Real.log (Q ⟨0, hm1⟩) * (d * δ / (3 * R ^ n)))
    (hΘ₂ : 1 / 2 + 2 * m * Z < Real.log (Q ⟨0, hm1⟩) * (d * m * (δ / (n * N) - 10 * n * ε))) :
    False := by
  classical
  subst hN hd hY hY₂ hG hZ
  have hn0 : 0 < n := by omega
  have hm0 : 0 < m := hm1
  have hp1 : 1 ≤ n - (k : ℕ) := by have := k.2; omega
  have hpn : n - (k : ℕ) < n := by omega
  have hNσ : Fintype.card (Set.powersetCard (Fin n) (n - k)) = n.choose (n - k) := by
    rw [← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hN2 : 2 ≤ Fintype.card (Set.powersetCard (Fin n) (n - k)) :=
    hNσ ▸ Nat.two_le_choose (by omega) (by omega)
  -- `log Q_h` is increasing
  have hlogpos : ∀ h, 0 < Real.log (Q h) := fun h ↦ Real.log_pos (hQ h)
  have hω1 : 1 ≤ 4 * m / ε := by
    rw [le_div_iff₀ hε]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  have hstep : ∀ i j : Fin m, (i : ℕ) + 1 = j → Real.log (Q i) ≤ Real.log (Q j) :=
    fun i j hij ↦ (le_mul_of_one_le_left (hlogpos i).le hω1).trans (hω i j hij)
  have hmono' : ∀ t : ℕ, ∀ i j : Fin m, (j : ℕ) = i + t → Real.log (Q i) ≤ Real.log (Q j) := by
    intro t
    induction t with
    | zero =>
      intro i j hij
      rw [show i = j from Fin.ext (by omega)]
    | succ t ih =>
      intro i j hij
      have hj' : (i : ℕ) + t < m := by omega
      exact (ih i ⟨i + t, hj'⟩ rfl).trans (hstep _ _ (by simp only; omega))
  have hmono : Monotone fun h ↦ Real.log (Q h) := fun i j hij ↦
    hmono' (j - i) i j (by have := Fin.le_iff_val_le_val.mp hij; omega)
  -- the wedge points (§11) for every `Q_h`
  have hW := fun h ↦ L.exists_wedgePoints c hLs hL₀ hc₀ hn hR hnR (hQ h) hδ k hk (hgap h)
    (hQ₁ h) (hQ₂ h) (hQ₃ h) (hQ₄ h) (hbig h)
  choose E hE e x he hes harch hfin hv0 hli W hWspan hWdim hWH using hW
  -- the compositum `F`
  have hfd : ∀ h, FiniteDimensional K (E h) := fun h ↦
    have := hE h
    Module.Finite.of_restrictScalars_finite ℚ K (E h)
  set F : IntermediateField K Ω := ⨆ h, E h with hF
  have : FiniteDimensional K F := IntermediateField.finiteDimensional_iSup_of_finite
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have : NumberField F := { to_finiteDimensional := Module.Finite.trans K _ }
  have hEF : ∀ h, E h ≤ F := fun h ↦ le_iSup E h
  -- the normal vectors of the `W_h`
  have hMex := fun h ↦ Submodule.exists_normal_logHeight_le (W := W h)
    (by rw [Fintype.card_fin]; exact hWdim h)
  choose M hM0 hMW hMh using hMex
  set eσ := Fintype.equivFin (Set.powersetCard (Fin n) (n - k))
  set M' : Fin m → Set.powersetCard (Fin n) (n - k) → K := fun h s ↦ M h (eσ s) with hM'
  -- the degrees (14.8)
  obtain ⟨Λ, r, hΛ0, hr, hanti, ht, hrle⟩ :=
    exists_blockDegrees hm0 hQ hmono hε (Real.log |(NumberField.discr K : ℝ)|)
  -- Prop. 13.6
  have hc0 : ∀ v, ∑ i, c.vec v i = 0 := by
    rintro (v | v)
    exacts [hLs.sum_arch v, hLs.sum_fin v]
  obtain ⟨P, hP0, hPh, hPi, hPii, hPht⟩ := L.exists_auxiliaryPolynomial_hasseDeriv
    (κ := Fin m) hL₀ hc0 hp1 (by simpa using hpn) (fun h ↦ (hr h).ne') hε
    (by simpa using hm) e (by simpa using he) (by simpa using hes)
  -- Prop. 12.1
  set N' := Fintype.card (Set.powersetCard (Fin n) (n - k)) - 1 with hN'
  have hcard : Fintype.card (Set.powersetCard (Fin n) (n - k)) = N' + 1 := by omega
  have hN'1 : 1 ≤ N' := by omega
  have hcardne : Fintype.card {J : Set.powersetCard (Fin n) (n - k) // J ≠ topSet k} = N' := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  set enum : Fin N' ≃ {J : Set.powersetCard (Fin n) (n - k) // J ≠ topSet k} :=
    (Fintype.equivFinOfCardEq hcardne).symm
  set y : Fin m → Fin N' → Set.powersetCard (Fin n) (n - k) → Ω :=
    fun h l s ↦ (x h (enum l) s : Ω) with hy_def
  have hΛpos : 0 < Λ := lt_of_lt_of_le (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    (hlogpos ⟨0, hm0⟩)) hΛ0
  have hratio : ∀ i j : Fin m, (i : ℕ) + 1 = j → (m : ℝ) / ε < r i / r j := fun i j hij ↦
    div_lt_div_of_blockDegrees hε1 (hlogpos i) (by exact_mod_cast hr j) hΛpos (ht j).2
      (hω i j hij) (ht i).1
  have hM'0 : ∀ h, M' h ≠ 0 := fun h hM ↦ hM0 h <| funext fun i ↦ by
    simpa [hM'] using congrFun hM (eσ.symm i)
  have hyspan : ∀ (h : Fin m) (x0 : Set.powersetCard (Fin n) (n - k) → Ω),
      ∑ s, algebraMap K Ω (M' h s) * x0 s = 0 → x0 ∈ Submodule.span Ω (Set.range (y h)) := by
    intro h x0 hx0
    have hrange : Set.range (y h) =
        (fun J s ↦ (x h J s : Ω)) '' {J | J ≠ topSet k} := by
      ext v
      simp only [Set.mem_range, Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨l, rfl⟩
        exact ⟨(enum l).1, (enum l).2, rfl⟩
      · rintro ⟨J, hJ, rfl⟩
        exact ⟨enum.symm ⟨J, hJ⟩, by simp [y]⟩
    rw [hrange]
    exact Submodule.mem_span_image_of_sum_eq_zero (hM0 h) (hMW h) (hWdim h) _ _
      (hWspan h) hx0
  have hheight : ∀ h, ((N' : ℕ) : ℝ) * max 1 ((m : ℝ) / ε) ^ m *
      (10 * m ^ 2 * finrank ℚ K * (∑ i, r i : ℕ) + m * P.logHeight) <
        r h * Height.logHeight (M' h) := by
    intro h
    have hL₀ := hlogpos ⟨0, hm0⟩
    have hd1 : (1 : ℝ) ≤ finrank ℚ K := by exact_mod_cast Module.finrank_pos
    have hlM : (finrank ℚ K : ℝ) * (δ / (3 * R ^ n)) * Real.log (Q h) - finrank ℚ K / 2 *
        Real.log (Fintype.card (Set.powersetCard (Fin n) (n - k))) ≤
          Height.logHeight (M' h) := by
      rw [show M' h = M h ∘ eσ from rfl, Height.logHeight_comp_equiv]
      have h1 := hMh h
      rw [Fintype.card_fin] at h1
      have hH := (W h).arakelovMulHeight_pos
      have h2 := Real.log_le_log (Real.rpow_pos_of_pos (zero_lt_one.trans (hQ h)) _) (hWH h)
      rw [Real.log_rpow (zero_lt_one.trans (hQ h)), Real.log_rpow hH] at h2
      have h3 : (finrank ℚ K : ℝ) * (δ / (3 * R ^ n) * Real.log (Q h)) ≤
          (W h).arakelovLogHeight := by
        rw [Submodule.arakelovLogHeight_eq_log_arakelovMulHeight]
        have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ finrank ℚ K)
        rwa [mul_inv_cancel_left₀ (by positivity : (finrank ℚ K : ℝ) ≠ 0)] at this
      linarith
    have hmax : max 1 ((m : ℝ) / ε) = m / ε := max_eq_right (by
      rw [le_div_iff₀ hε]
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      linarith)
    have hN'R : ((N' : ℕ) : ℝ) = Fintype.card (Set.powersetCard (Fin n) (n - k)) - 1 := by
      rw [hN', Nat.cast_sub (by omega), Nat.cast_one]
    have hY0 : 0 ≤ (finrank ℚ K : ℝ) / 2 * Fintype.card (Set.powersetCard (Fin n) (n - k)) +
        finrank ℚ K * Real.log (Fintype.card (Set.powersetCard (Fin n) (n - k))) +
        finrank ℚ K * Real.log (n - k : ℕ).factorial +
        2 * (n - k : ℕ) * #L.matSet * Real.log L.mulFormHeight := by
      have ha := Real.log_nonneg (show (1 : ℝ) ≤ Fintype.card (Set.powersetCard (Fin n) (n - k))
        by exact_mod_cast (show 1 ≤ 2 by norm_num).trans hN2)
      have hb := Real.log_nonneg (show (1 : ℝ) ≤ (n - k : ℕ).factorial by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
      have hc := Real.log_nonneg L.one_le_mulFormHeight
      have h0 : (0 : ℝ) ≤ finrank ℚ K := Nat.cast_nonneg _
      refine add_nonneg (add_nonneg (add_nonneg
        (mul_nonneg (div_nonneg h0 zero_le_two) (Nat.cast_nonneg _)) (mul_nonneg h0 ha))
        (mul_nonneg h0 hb)) (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _))
          (Nat.cast_nonneg _)) hc)
    have hD : Real.log |(NumberField.discr K : ℝ)| ≤ Λ / Real.log (Q ⟨0, hm0⟩) := by
      rw [le_div_iff₀ hL₀]
      exact (mul_le_mul_of_nonneg_right (le_max_right _ _) hL₀.le).trans hΛ0
    have hS : ((∑ i, r i : ℕ) : ℝ) ≤ m * (2 * Λ / Real.log (Q ⟨0, hm0⟩)) := by
      push_cast
      calc ∑ i, (r i : ℝ) ≤ ∑ _i : Fin m, 2 * Λ / Real.log (Q ⟨0, hm0⟩) :=
            sum_le_sum fun i _ ↦ hrle i
        _ = m * (2 * Λ / Real.log (Q ⟨0, hm0⟩)) := by simp
    have hPht' : P.logHeight ≤ 1 / 2 * Real.log |(NumberField.discr K : ℝ)| +
        ((finrank ℚ K : ℝ) / 2 * Fintype.card (Set.powersetCard (Fin n) (n - k)) +
          finrank ℚ K * Real.log (Fintype.card (Set.powersetCard (Fin n) (n - k))) +
          finrank ℚ K * Real.log (n - k : ℕ).factorial +
          2 * (n - k : ℕ) * #L.matSet * Real.log L.mulFormHeight) * ((∑ i, r i : ℕ) : ℝ) := by
      have e : ((∑ i, r i : ℕ) : ℝ) = ∑ i, (r i : ℝ) := by push_cast; rfl
      rw [e, one_div]
      exact hPht
    rw [hmax]
    refine lt_mul_logHeight_aux (Nat.cast_nonneg _) (by positivity) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (by positivity) (lt_of_lt_of_le (mul_pos one_pos hL₀)
        ((mul_le_mul_of_nonneg_right (le_max_left _ _) hL₀.le).trans hΛ0)) hL₀ hY0
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 by norm_num).trans hN2)) hS hPht' hD
      (hrle h) (ht h).1 (Nat.cast_nonneg _) hlM ?_
    rw [hN'R]
    exact hΘ₁
  obtain ⟨z, hz, I, hI, hne⟩ := MvPolynomial.exists_eval_hasseDeriv_ne_zero_of_logHeight
    (E := Ω) hm1 hN'1 hcard hr hanti hε hratio hP0 hPh hM'0 hheight hyspan
  -- the points `x_h = Σ_l z_{hl} ĥ_{hl}` in `F` (EF13 (14.7))
  have hN'R : ((N' : ℕ) : ℝ) = Fintype.card (Set.powersetCard (Fin n) (n - k)) - 1 := by
    rw [hN', Nat.cast_sub (by omega), Nat.cast_one]
  set u : Fin m → Fin N' → Set.powersetCard (Fin n) (n - k) → F :=
    fun h l s ↦ IntermediateField.inclusion (hEF h) (x h (enum l) s) with hu
  set yF : Fin m → Set.powersetCard (Fin n) (n - k) → F :=
    fun h ↦ ∑ l, ((z h l : ℤ) : F) • u h l with hyF
  have hneF : eval (fun t ↦ yF t.1 t.2) (map (algebraMap K F) (hasseDeriv I P)) ≠ 0 := by
    intro h0
    apply hne
    have key : algebraMap F Ω (eval (fun t ↦ yF t.1 t.2) (map (algebraMap K F) (hasseDeriv I P)))
        = eval (fun t ↦ ∑ l, (z t.1 l : Ω) * y t.1 l t.2)
          (hasseDeriv I (P.map (algebraMap K Ω))) := by
      rw [← map_hasseDeriv, eval_map, eval_map, eval₂_comp_left,
        ← IsScalarTower.algebraMap_eq]
      congr 1
      funext t
      simp [yF, u, y, Finset.sum_apply]
    rw [← key, h0, map_zero]
  -- the local bounds (14.15)
  have hG1 : (1 : ℝ) ≤ (Fintype.card (Set.powersetCard (Fin n) (n - k)) - 1) *
      ((Fintype.card (Set.powersetCard (Fin n) (n - k)) - 1) / ε + 1) := by
    have h1 : (1 : ℝ) ≤ Fintype.card (Set.powersetCard (Fin n) (n - k)) - 1 := by
      rw [← hN'R]; exact_mod_cast hN'1
    have h2 : (0 : ℝ) ≤ (Fintype.card (Set.powersetCard (Fin n) (n - k)) - 1) / ε :=
      div_nonneg (by linarith) hε.le
    nlinarith
  have harch' : ∀ h (w : InfinitePlace F) s,
      w ((((L.arch (w.comap (algebraMap K F))).compound (n - k)).map (algebraMap K F) *ᵥ
        yF h) s) ≤ (Fintype.card (Set.powersetCard (Fin n) (n - k)) - 1) *
          ((Fintype.card (Set.powersetCard (Fin n) (n - k)) - 1) / ε + 1) *
          Q h ^ ((c.exteriorPower (n - k)).arch (w.comap (algebraMap K F)) s * finrank ℚ K /
            (w.comap (algebraMap K F)).mult) := by
    intro h w s
    have hb : ∀ l, w ((((L.arch (w.comap (algebraMap K F))).compound (n - k)).map
        (algebraMap K F) *ᵥ u h l) s) ≤ ((c.exteriorPower (n - k)).weight
          (zero_lt_one.trans (hQ h))).arch (w.comap (algebraMap K F)) s := fun l ↦ by
      rw [FormExponent.weight_exteriorPower]
      exact FormSystem.apply_mulVec_le_arch_of_le (L.exteriorPower (n - k)) _ (hEF h)
        (harch h (enum l) (enum l).2) w s
    have := apply_mulVec_sum_le w.1 _ (z h) (u h) s hb (fun l ↦ hz h l)
    rw [Fintype.card_fin, hN'R] at this
    exact this
  have hfin' : ∀ h (w : FinitePlace F), w.under K ≠ v₀ → ∀ s,
      w ((((L.fin (w.under K)).compound (n - k)).map (algebraMap K F) *ᵥ yF h) s) ≤
        (Q h ^ ((c.exteriorPower (n - k)).fin (w.under K) s * finrank ℚ K)) ^
          w.localDegree K := by
    intro h w hw s
    have hb : ∀ l, w ((((L.fin (w.under K)).compound (n - k)).map
        (algebraMap K F) *ᵥ u h l) s) ≤ ((c.exteriorPower (n - k)).weight
          (zero_lt_one.trans (hQ h))).fin (w.under K) s ^ w.localDegree K := fun l ↦ by
      rw [FormExponent.weight_exteriorPower]
      exact FormSystem.apply_mulVec_le_fin_of_le (L.exteriorPower (n - k)) _ (hEF h)
        (hfin h (enum l) (enum l).2) w hw s
    exact apply_mulVec_sum_le_of_isNonarchimedean (fun a b ↦ FinitePlace.add_le w a b)
      (FinitePlace.apply_intCast_le_one w) _ (z h) (u h) s
      (pow_nonneg (Real.rpow_nonneg (zero_lt_one.trans (hQ h)).le _) _) hb
  have hv₀' : ∀ h (w : FinitePlace F), w.under K = v₀ → ∀ s,
      w (yF h s) ≤ (Q h ^ (e h s * finrank ℚ K)) ^ w.localDegree K := by
    intro h w hw s
    have hb : ∀ l, w ((1 *ᵥ u h l) s) ≤ (Q h ^ (e h s * finrank ℚ K)) ^ w.localDegree K :=
      fun l ↦ by
        rw [one_mulVec, Real.rpow_mul_natCast (zero_lt_one.trans (hQ h)).le]
        exact FinitePlace.apply_inclusion_le (hEF h) w _ fun u' hu' ↦
          hv0 h (enum l) (enum l).2 s u' (hu'.trans hw)
    have := apply_mulVec_sum_le_of_isNonarchimedean (fun a b ↦ FinitePlace.add_le w a b)
      (FinitePlace.apply_intCast_le_one w) 1 (z h) (u h) s
      (pow_nonneg (Real.rpow_nonneg (zero_lt_one.trans (hQ h)).le _) _) hb
    rwa [one_mulVec] at this
  -- the product formula and Prop. 13.6 (iv)
  have hI' : blockAvg r I 1 ≤ 2 * Fintype.card (Fin m) * ε := by
    simpa [blockAvg] using hI
  have h1 := one_le_evalBound (L := L) (F := F) hp1 (by simpa using hpn) hc0 hLs.sum_iSup_le
    hL₀ hc₀ hr hPh I (fun h ↦ zero_lt_one.trans (hQ h))
    (hΛpos.le) hε.le hG1 ht e (by simpa using he) (fun v J hJ ↦ hPi v I J hI' hJ)
    (fun J hJ ↦ hPii I J hI' hJ) yF harch' hfin' hv₀' hneF
  have h2 := L.prod_iSup_coeff_blockSubst_hasseDeriv_le (by simp) hPh hP0 I
  -- the logarithms
  have hlQ₀ := hlogpos ⟨0, hm0⟩
  have hD : Real.log |(NumberField.discr K : ℝ)| ≤ Λ / Real.log (Q ⟨0, hm0⟩) := by
    rw [le_div_iff₀ hlQ₀]
    exact (mul_le_mul_of_nonneg_right (le_max_right _ _) hlQ₀.le).trans hΛ0
  have hS : ((∑ i, r i : ℕ) : ℝ) ≤ m * (2 * Λ / Real.log (Q ⟨0, hm0⟩)) := by
    push_cast
    calc ∑ i, (r i : ℝ) ≤ ∑ _i : Fin m, 2 * Λ / Real.log (Q ⟨0, hm0⟩) :=
          sum_le_sum fun i _ ↦ hrle i
      _ = m * (2 * Λ / Real.log (Q ⟨0, hm0⟩)) := by simp
  have hs₀ : (0 : ℝ) < #P.support := by
    exact_mod_cast Finset.card_pos.mpr (support_nonempty.mpr hP0)
  have hPh' : Real.log P.mulHeight ≤ 1 / 2 * Real.log |(NumberField.discr K : ℝ)| +
      ((finrank ℚ K : ℝ) / 2 * Fintype.card (Set.powersetCard (Fin n) (n - k)) +
        finrank ℚ K * Real.log (Fintype.card (Set.powersetCard (Fin n) (n - k))) +
        finrank ℚ K * Real.log (n - k : ℕ).factorial +
        2 * (n - k : ℕ) * #L.matSet * Real.log L.mulFormHeight) * ((∑ i, r i : ℕ) : ℝ) := by
    have e : ((∑ i, r i : ℕ) : ℝ) = ∑ i, (r i : ℝ) := by push_cast; rfl
    rw [e, one_div]
    exact hPht
  have hy : Real.log (Height.mulHeight (L.invTuple (n - k))) ≤
      finrank ℚ K * Real.log (n - k : ℕ).factorial +
        2 * (n - k : ℕ) * #L.matSet * Real.log L.mulFormHeight := by
    have h := L.mulHeight_invTuple_le (L.one_mem_forms hL₀) (n - k)
    refine (Real.log_le_log (Height.mulHeight_pos _) h).trans_eq ?_
    have := L.one_le_mulFormHeight
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h3 := neg_le_of_one_le_evalBound_aux (by omega) hs₀
    (card_support_le_of_isMultiHomogeneous hPh fun _ ↦ le_rfl) hG1 P.mulHeight_pos
    (Height.mulHeight_pos _) h1 h2 hPh' hy
  have hZ0 : 0 ≤ ((finrank ℚ K : ℝ) / 2 * Fintype.card (Set.powersetCard (Fin n) (n - k)) +
        finrank ℚ K * Real.log (Fintype.card (Set.powersetCard (Fin n) (n - k))) +
        finrank ℚ K * Real.log (n - k : ℕ).factorial +
        2 * (n - k : ℕ) * #L.matSet * Real.log L.mulFormHeight) +
      (finrank ℚ K * Real.log (n - k : ℕ).factorial +
        2 * (n - k : ℕ) * #L.matSet * Real.log L.mulFormHeight) +
      finrank ℚ K * (2 * Fintype.card (Set.powersetCard (Fin n) (n - k)) * Real.log 2 +
        Real.log 2 + Real.log (Fintype.card (Set.powersetCard (Fin n) (n - k))) +
        Real.log ((Fintype.card (Set.powersetCard (Fin n) (n - k)) - 1) *
          ((Fintype.card (Set.powersetCard (Fin n) (n - k)) - 1) / ε + 1))) := by
    have ha := Real.log_nonneg (show (1 : ℝ) ≤ Fintype.card (Set.powersetCard (Fin n) (n - k))
      by exact_mod_cast (show 1 ≤ 2 by norm_num).trans hN2)
    have hb := Real.log_nonneg (show (1 : ℝ) ≤ (n - k : ℕ).factorial by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
    have hc := Real.log_nonneg L.one_le_mulFormHeight
    have hg := Real.log_nonneg hG1
    have h2' := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    have h0 : (0 : ℝ) ≤ finrank ℚ K := Nat.cast_nonneg _
    have hN0 : (0 : ℝ) ≤ Fintype.card (Set.powersetCard (Fin n) (n - k)) := Nat.cast_nonneg _
    have hmat : (0 : ℝ) ≤ 2 * (n - k : ℕ) * #L.matSet :=
      mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have t1 := mul_nonneg h0 ha
    have t2 := mul_nonneg h0 hb
    have t3 := mul_nonneg hmat hc
    have t4 := mul_nonneg (div_nonneg h0 zero_le_two) hN0
    have t5 := mul_nonneg (mul_nonneg zero_le_two hN0) h2'
    have t6 := mul_nonneg h0 (add_nonneg (add_nonneg (add_nonneg t5 h2') ha) hg)
    linarith
  refine false_of_le_aux hΛpos hlQ₀ hZ0 hS hD ?_ hΘ₂
  simp only [Fintype.card_fin] at h3
  linarith [show -(↑(finrank ℚ K) * Λ * (↑m * (10 * ↑n * ε - δ / (↑n *
      ↑(Fintype.card (Set.powersetCard (Fin n) (n - k))))))) = Λ * (↑(finrank ℚ K) * ↑m *
        (δ / (↑n * ↑(Fintype.card (Set.powersetCard (Fin n) (n - k)))) - 10 * ↑n * ε)) by ring]

end NumberField.FormSystem
