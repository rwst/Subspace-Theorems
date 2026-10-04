/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormAuxiliaryPolynomial
public import DiophantineApproximation.SubspaceValueBound

-- Used only inside proofs.
import Mathlib.Algebra.FiniteSupport.Basic

/-!
# The value of the auxiliary polynomial at the wedge points (EF13 (14.10)–(14.17))

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, §14.

EF13 finish the proof of Theorem 8.1 by bounding `‖P_I(x_1, …, x_m)‖_w` at every place `w` of a
number field `F` containing the points, and by the product formula. This file proves those
bounds and the resulting inequality.

* `MvPolynomial.map_blockSubst`: a change of coefficients commutes with `blockSubst`.
* `MvPolynomial.card_support_le_of_isMultiHomogeneous`: at most `2^{N Σ r}` monomials.
* `MvPolynomial.sum_log_mul_le`: the exponent count of (14.16), (14.17), with
  `Λ ≤ r_h log Q_h ≤ (1 + ε) Λ` (14.8).
* `MvPolynomial.prod_apply_pow_le`: the bound on one monomial at the point, at any absolute
  value.
* `NumberField.FormSystem.one_le_evalBound`: (14.16), (14.17) and the product formula. The
  output is the inequality
  `1 ≤ (∏_v A_v) (2^{N Σ r} G^{Σ r})^{[K:ℚ]} e^{[K:ℚ] Λ m (10 n ε - δ/nN)}`, with `A_v`
  EF13's `max_J |d^{(v)}_{I,J}(a_P)|_v`, to be combined with Prop. 13.6 (iv).

## Implementation notes

The point `x_h` enters only through bounds for `L̂_l^{(v)}(x_h)`: at the infinite places
`G Q_h^{ĉ_{lv} [K:ℚ] / mult v}` (`G` absorbs the grid of (14.7)), at the finite places off `v₀`
`(Q_h^{ĉ_{lv} [K:ℚ]})^{e_w}`, and above `v₀`, where `L^{(v₀)}` is the identity,
`(Q_h^{e_{hl} [K:ℚ]})^{e_w}`, `e_w` the local degree. These are the local factors of
`FormSystem.archFactor` and `FormSystem.finFactor` for the exterior power, in the normalization
of `QuantitativeSubspace.FormHeight`.

This is part of milestone Q4.1d of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Finset Module Matrix Real

namespace MvPolynomial

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

/-! ### Polynomial lemmas -/

omit [Fintype κ] in
/-- A change of coefficient ring commutes with the block substitution. -/
theorem map_blockSubst {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (A : Matrix ι ι R)
    (P : MvPolynomial (κ × ι) R) :
    map f (blockSubst A P) = blockSubst (A.map f) (map f P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [blockSubst, algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p t hp =>
    obtain ⟨h, j⟩ := t
    simp [hp, blockSubst_X, map_sum]

/-- A multihomogeneous polynomial of multidegree at most `r` has at most `2^{#ι Σ r}` monomials. -/
theorem card_support_le_of_isMultiHomogeneous {R : Type*} [CommRing R] {d r : κ → ℕ}
    {P : MvPolynomial (κ × ι) R} (hP : IsMultiHomogeneous d P) (hdr : ∀ h, d h ≤ r h) :
    (#P.support : ℝ) ≤ 2 ^ (Fintype.card ι * ∑ h, r h) := by
  classical
  have hsub : P.support ⊆ multiMons (ι := ι) d := fun ν hν ↦
    mem_multiMons.mpr fun h ↦ hP (mem_support_iff.mp hν) h
  have h1 : #P.support ≤ ∏ t : κ × ι, (d t.1 + 1) :=
    (card_le_card hsub).trans (card_multiMons_le d)
  have h2 : ∏ t : κ × ι, (d t.1 + 1) ≤ ∏ t : κ × ι, 2 ^ r t.1 :=
    prod_le_prod fun t _ ↦ (Nat.succ_le_of_lt (Nat.lt_two_pow_self)).trans
      (Nat.pow_le_pow_right two_pos (hdr t.1))
  have h3 : ∏ t : κ × ι, 2 ^ r t.1 = 2 ^ (Fintype.card ι * ∑ h, r h) := by
    rw [prod_pow_eq_pow_sum, Fintype.sum_prod_type]
    simp [sum_const, card_univ, sum_mul, mul_comm]
  exact_mod_cast (h1.trans h2).trans_eq h3

omit [Fintype ι] in
/-- **The exponent count of EF13 (14.16), (14.17).** If `Λ ≤ r_h log Q_h ≤ (1 + ε) Λ` (14.8),
`Σ_l J_{hl} ≤ r_h` and `|f_{hl}| ≤ F₀`, then
`Σ_h log Q_h Σ_l J_{hl} f_{hl} ≤ Λ Σ_h r_h⁻¹ Σ_l J_{hl} f_{hl} + ε Λ m F₀`. -/
theorem sum_log_mul_le [Fintype ι] {r : κ → ℕ} (hr : ∀ h, 0 < r h) {Q : κ → ℝ} {Λ ε F₀ : ℝ}
    (hΛ : 0 ≤ Λ) (hε : 0 ≤ ε) (hF₀ : 0 ≤ F₀)
    (ht : ∀ h, Λ ≤ r h * Real.log (Q h) ∧ r h * Real.log (Q h) ≤ (1 + ε) * Λ)
    (J : κ × ι →₀ ℕ) (hJ : ∀ h, ∑ l, J (h, l) ≤ r h) (f : κ → ι → ℝ)
    (hf : ∀ h l, |f h l| ≤ F₀) :
    ∑ h, Real.log (Q h) * ∑ l, (J (h, l) : ℝ) * f h l ≤
      Λ * blockAvg r J f + ε * Λ * Fintype.card κ * F₀ := by
  rw [blockAvg, mul_sum, show ε * Λ * Fintype.card κ * F₀ = ∑ _h : κ, ε * Λ * F₀ by
    rw [sum_const, card_univ, nsmul_eq_mul]; ring, ← sum_add_distrib]
  refine sum_le_sum fun h _ ↦ ?_
  set S := ∑ l, (J (h, l) : ℝ) * f h l
  have hr0 : (0 : ℝ) < r h := by exact_mod_cast hr h
  have hS : |S| ≤ F₀ * r h := by
    calc |S| ≤ ∑ l, |(J (h, l) : ℝ) * f h l| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ l, (J (h, l) : ℝ) * F₀ := sum_le_sum fun l _ ↦ by
          rw [abs_mul, Nat.abs_cast]
          exact mul_le_mul_of_nonneg_left (hf h l) (Nat.cast_nonneg _)
      _ = F₀ * ∑ l, (J (h, l) : ℝ) := by rw [← sum_mul, mul_comm]
      _ ≤ F₀ * r h := mul_le_mul_of_nonneg_left (by exact_mod_cast hJ h) hF₀
  set a := (r h : ℝ) * Real.log (Q h)
  have hlog : Real.log (Q h) = a / r h := by
    rw [mul_div_cancel_left₀ _ hr0.ne']
  obtain ⟨h1, h2⟩ := ht h
  have key : (a - Λ) * S ≤ ε * Λ * F₀ * r h := by
    calc (a - Λ) * S ≤ (a - Λ) * |S| :=
          mul_le_mul_of_nonneg_left (le_abs_self S) (by linarith)
      _ ≤ (ε * Λ) * (F₀ * r h) :=
          mul_le_mul (by linarith) hS (abs_nonneg S) (mul_nonneg hε hΛ)
      _ = ε * Λ * F₀ * r h := by ring
  have hsplit : a / r h * S = Λ * S / r h + (a - Λ) * S / r h := by
    field_simp
    ring
  rw [hlog, hsplit, mul_div_assoc]
  have : (a - Λ) * S / r h ≤ ε * Λ * F₀ := by
    rw [div_le_iff₀ hr0]
    exact key
  linarith

/-- **One monomial at the point, at any absolute value** (EF13 (14.16), (14.17)). If
`w(u_{hl}) ≤ G Q_h^{ρ f_{hl}}` with `G ≥ 1`, `ρ ≥ 0`, `|f| ≤ F₀`, and `J` has block degrees at most
`r` and `Σ_h r_h⁻¹ Σ_l J_{hl} f_{hl} ≤ T`, then under (14.8)
`∏ w(u_t)^{J_t} ≤ G^{Σ r} e^{ρ Λ (T + ε m F₀)}`. -/
theorem prod_apply_pow_le {F : Type*} [Field F] (w : AbsoluteValue F ℝ) {r : κ → ℕ}
    (hr : ∀ h, 0 < r h) {Q : κ → ℝ} (hQ : ∀ h, 0 < Q h) {Λ ε F₀ G ρ T : ℝ} (hΛ : 0 ≤ Λ)
    (hε : 0 ≤ ε) (hF₀ : 0 ≤ F₀) (hG : 1 ≤ G) (hρ : 0 ≤ ρ)
    (ht : ∀ h, Λ ≤ r h * Real.log (Q h) ∧ r h * Real.log (Q h) ≤ (1 + ε) * Λ)
    (f : κ → ι → ℝ) (hf : ∀ h l, |f h l| ≤ F₀) (u : κ × ι → F)
    (hu : ∀ t, w (u t) ≤ G * Q t.1 ^ (ρ * f t.1 t.2)) (J : κ × ι →₀ ℕ)
    (hJ : ∀ h, ∑ l, J (h, l) ≤ r h) (hT : blockAvg r J f ≤ T) :
    ∏ t, w (u t) ^ J t ≤ G ^ (∑ h, r h) * Real.exp (ρ * Λ * (T + ε * Fintype.card κ * F₀)) := by
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hexp : ∀ t : κ × ι, (Q t.1 ^ (ρ * f t.1 t.2)) ^ J t =
      Real.exp (J t * (Real.log (Q t.1) * (ρ * f t.1 t.2))) := fun t ↦ by
    rw [Real.rpow_def_of_pos (hQ t.1), ← Real.exp_nat_mul]
  have hsumJ : ∑ t, J t ≤ ∑ h, r h := by
    rw [Fintype.sum_prod_type]
    exact sum_le_sum fun h _ ↦ hJ h
  have hsum : ∑ t : κ × ι, (J t : ℝ) * (Real.log (Q t.1) * (ρ * f t.1 t.2)) =
      ρ * ∑ h, Real.log (Q h) * ∑ l, (J (h, l) : ℝ) * f h l := by
    rw [Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun h _ ↦ ?_
    rw [mul_sum, mul_sum]
    exact sum_congr rfl fun l _ ↦ by ring
  have hlog := sum_log_mul_le hr hΛ hε hF₀ ht J hJ f hf
  calc ∏ t, w (u t) ^ J t ≤ ∏ t, (G * Q t.1 ^ (ρ * f t.1 t.2)) ^ J t :=
        prod_le_prod₀ (fun t _ ↦ pow_nonneg (w.nonneg _) _)
          fun t _ ↦ pow_le_pow_left₀ (w.nonneg _) (hu t) _
    _ = G ^ (∑ t, J t) * Real.exp (ρ * ∑ h, Real.log (Q h) * ∑ l, (J (h, l) : ℝ) * f h l) := by
        rw [← hsum, Real.exp_sum, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
        exact prod_congr rfl fun t _ ↦ by rw [mul_pow, hexp]
    _ ≤ G ^ (∑ h, r h) * Real.exp (ρ * Λ * (T + ε * Fintype.card κ * F₀)) := by
        refine mul_le_mul (pow_le_pow_right₀ hG hsumJ) (Real.exp_le_exp.mpr ?_)
          (Real.exp_pos _).le (pow_nonneg hG0 _)
        calc ρ * ∑ h, Real.log (Q h) * ∑ l, (J (h, l) : ℝ) * f h l
            ≤ ρ * (Λ * blockAvg r J f + ε * Λ * Fintype.card κ * F₀) :=
              mul_le_mul_of_nonneg_left hlog hρ
          _ ≤ ρ * (Λ * T + ε * Λ * Fintype.card κ * F₀) := by gcongr
          _ = ρ * Λ * (T + ε * Fintype.card κ * F₀) := by ring

end MvPolynomial

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]

open MvPolynomial

namespace FormSystem

variable {L : FormSystem K ι} {κ : Type*} [Fintype κ] {F : Type*} [Field F] [Algebra K F]
  {p : ℕ} {r : κ → ℕ} {P : MvPolynomial (κ × Set.powersetCard ι p) K} {Q : κ → ℝ} {Λ ε : ℝ}

/-! ### The local bounds (14.16), (14.17) -/

omit [NumberField K] [Fintype ι] [Fintype κ] in
/-- `P_I(x)` read in the coordinates `B x_h`: EF13 (14.11). -/
private theorem eval_map_hasseDeriv_eq [Fintype ι]
    {B : Matrix (Set.powersetCard ι p) (Set.powersetCard ι p) K} (hB : B.det ≠ 0)
    (I : κ × Set.powersetCard ι p →₀ ℕ) (y : κ → Set.powersetCard ι p → F) :
    eval (fun t ↦ y t.1 t.2) (map (algebraMap K F) (hasseDeriv I P)) =
      eval (fun t ↦ (B.map (algebraMap K F) *ᵥ y t.1) t.2)
        (map (algebraMap K F) (blockSubst B⁻¹ (hasseDeriv I P))) := by
  have hMA : B⁻¹.map (algebraMap K F) * B.map (algebraMap K F) = 1 := by
    rw [← Matrix.map_mul, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB),
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [eval_eq_eval_blockSubst hMA, map_blockSubst]
  rfl

omit [NumberField K] [LinearOrder ι] [Fintype κ] in
private theorem isMultiHomogeneous_map_blockSubst [Finite κ] (hP : IsMultiHomogeneous r P)
    (B : Matrix (Set.powersetCard ι p) (Set.powersetCard ι p) K)
    (I : κ × Set.powersetCard ι p →₀ ℕ) :
    IsMultiHomogeneous (fun h ↦ r h - ∑ s, I (h, s))
      (map (algebraMap K F) (blockSubst B (hasseDeriv I P))) := fun _ hν ↦
  (hP.hasseDeriv I).blockSubst B fun h ↦ hν (by rw [coeff_map, h, map_zero])

/-- **EF13 (14.16) at an infinite place `w` of `F`.** If the coefficients of `∂_I P` read in the
coordinates `L̂^{(v)}` vanish beyond `T` (Prop. 13.6 (i)), and
`|L̂_s^{(v)}(x_h)|_w ≤ G Q_h^{ĉ_{sv} [K:ℚ] / mult v}`, then
`|P_I(x)|_w ≤ 2^{N Σ r} A_v G^{Σ r} e^{([K:ℚ]/mult v) Λ (T + ε m n γ_v)}`. -/
theorem apply_eval_le_arch (hp : 1 ≤ p) (hpn : p < Fintype.card ι) {c : FormExponent K ι}
    {v : InfinitePlace K} (hc0 : ∑ i, c.arch v i = 0) (hr : ∀ h, 0 < r h)
    (hP : IsMultiHomogeneous r P) (I : κ × Set.powersetCard ι p →₀ ℕ) (hQ : ∀ h, 0 < Q h)
    {G T : ℝ} (hΛ : 0 ≤ Λ) (hε : 0 ≤ ε) (hG : 1 ≤ G)
    (ht : ∀ h, Λ ≤ r h * Real.log (Q h) ∧ r h * Real.log (Q h) ≤ (1 + ε) * Λ)
    {w : InfinitePlace F} (hv : w.comap (algebraMap K F) = v)
    (hPi : ∀ J, T < blockAvg r J (fun _ s ↦ (c.exteriorPower p).arch v s) →
      (blockSubst ((L.arch v).compound p)⁻¹ (hasseDeriv I P)).coeff J = 0)
    (y : κ → Set.powersetCard ι p → F)
    (hy : ∀ h s, w ((((L.arch v).compound p).map (algebraMap K F) *ᵥ y h) s) ≤
      G * Q h ^ ((c.exteriorPower p).arch v s * finrank ℚ K / v.mult)) :
    w (eval (fun t ↦ y t.1 t.2) (map (algebraMap K F) (hasseDeriv I P))) ≤
      2 ^ (Fintype.card (Set.powersetCard ι p) * ∑ h, r h) *
        (⨆ J, v ((blockSubst ((L.arch v).compound p)⁻¹ (hasseDeriv I P)).coeff J)) *
        (G ^ (∑ h, r h) * Real.exp (finrank ℚ K / v.mult * Λ *
          (T + ε * Fintype.card κ * (Fintype.card ι * ⨆ i, c.arch v i)))) := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt hpn)
  set B := (L.arch v).compound p
  have hB : B.det ≠ 0 := det_compound_ne_zero p (L.arch_det_ne_zero v)
  rw [eval_map_hasseDeriv_eq hB]
  have hR := isMultiHomogeneous_map_blockSubst (F := F) hP B⁻¹ I
  have hγ : 0 ≤ ⨆ i, c.arch v i := FormExponent.iSup_vec_nonneg (c := c) (v := Sum.inl v) hc0
  have hF₀ : 0 ≤ (Fintype.card ι : ℝ) * ⨆ i, c.arch v i := mul_nonneg (Nat.cast_nonneg _) hγ
  have hf : ∀ (_ : κ) s, |(c.exteriorPower p).arch v s| ≤ Fintype.card ι * ⨆ i, c.arch v i :=
    fun _ s ↦ (c.abs_exteriorPower_arch_le hp hpn hc0 s).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le _ _) hγ)
  have hcoeff : (⨆ J, v ((blockSubst B⁻¹ (hasseDeriv I P)).coeff J)) =
      ⨆ J, w ((map (algebraMap K F) (blockSubst B⁻¹ (hasseDeriv I P))).coeff J) := by
    refine iSup_congr fun J ↦ ?_
    rw [coeff_map, ← hv, InfinitePlace.comap_apply]
  rw [hcoeff]
  refine apply_eval_le_of_forall_support w.1 _ (by positivity) (fun J hJ ↦ ?_)
    (card_support_le_of_isMultiHomogeneous hR fun h ↦ Nat.sub_le _ _)
  have hJ0 := mem_support_iff.mp hJ
  have hJ0' : (blockSubst B⁻¹ (hasseDeriv I P)).coeff J ≠ 0 := fun h ↦
    hJ0 (by rw [coeff_map, h, map_zero])
  refine prod_apply_pow_le w.1 hr hQ hΛ hε hF₀ hG (by positivity) ht _ hf _ (fun t ↦ ?_) J
    (fun h ↦ ?_) (not_lt.mp fun h ↦ hJ0' (hPi J h))
  · have := hy t.1 t.2
    rwa [show (c.exteriorPower p).arch v t.2 * finrank ℚ K / v.mult =
      finrank ℚ K / v.mult * (c.exteriorPower p).arch v t.2 by ring] at this
  · rw [hR hJ0 h]
    exact Nat.sub_le _ _

/-- **EF13 (14.16), (14.17) at a finite place `w` of `F`**, for any invertible `B` (`L̂^{(v)}`, or
the identity above `v₀`). If the coefficients of `∂_I P` read in the coordinates `B` vanish
beyond `T` for the exponents `f`, and `|(B x_h)_s|_w ≤ (Q_h^{f_{hs} [K:ℚ]})^{e_w}`, then
`|P_I(x)|_w ≤ (A_v e^{[K:ℚ] Λ (T + ε m F₀)})^{e_w}`. -/
theorem apply_eval_le_fin [NumberField F]
    {B : Matrix (Set.powersetCard ι p) (Set.powersetCard ι p) K} (hB : B.det ≠ 0)
    (hr : ∀ h, 0 < r h) (hP : IsMultiHomogeneous r P) (I : κ × Set.powersetCard ι p →₀ ℕ)
    (hQ : ∀ h, 0 < Q h) {T F₀ : ℝ} (hΛ : 0 ≤ Λ) (hε : 0 ≤ ε) (hF₀ : 0 ≤ F₀)
    (ht : ∀ h, Λ ≤ r h * Real.log (Q h) ∧ r h * Real.log (Q h) ≤ (1 + ε) * Λ)
    {w : FinitePlace F} {v : FinitePlace K} (hv : w.under K = v)
    (f : κ → Set.powersetCard ι p → ℝ) (hf : ∀ h s, |f h s| ≤ F₀)
    (hPi : ∀ J, T < blockAvg r J f → (blockSubst B⁻¹ (hasseDeriv I P)).coeff J = 0)
    (y : κ → Set.powersetCard ι p → F)
    (hy : ∀ h s, w ((B.map (algebraMap K F) *ᵥ y h) s) ≤
      (Q h ^ (f h s * finrank ℚ K)) ^ w.localDegree K) :
    w (eval (fun t ↦ y t.1 t.2) (map (algebraMap K F) (hasseDeriv I P))) ≤
      ((⨆ J, v ((blockSubst B⁻¹ (hasseDeriv I P)).coeff J)) *
        Real.exp (finrank ℚ K * Λ * (T + ε * Fintype.card κ * F₀))) ^ w.localDegree K := by
  subst hv
  rw [eval_map_hasseDeriv_eq hB]
  have hR := isMultiHomogeneous_map_blockSubst (F := F) hP B⁻¹ I
  have hna : IsNonarchimedean w.1 := fun a b ↦ FinitePlace.add_le w a b
  set e := w.localDegree K
  refine (apply_eval_le_of_forall_support_of_isNonarchimedean hna _
    (G := 1 ^ (∑ h, r h) * Real.exp ((finrank ℚ K * e) * Λ * (T + ε * Fintype.card κ * F₀)))
    (by positivity) (fun J hJ ↦ ?_)).trans ?_
  · have hJ0 := mem_support_iff.mp hJ
    have hJ0' : (blockSubst B⁻¹ (hasseDeriv I P)).coeff J ≠ 0 := fun h ↦
      hJ0 (by rw [coeff_map, h, map_zero])
    refine prod_apply_pow_le w.1 hr hQ hΛ hε hF₀ le_rfl (by positivity) ht f hf _ (fun t ↦ ?_) J
      (fun h ↦ ?_) (not_lt.mp fun h ↦ hJ0' (hPi J h))
    · have := hy t.1 t.2
      rw [← Real.rpow_mul_natCast (hQ t.1).le] at this
      rw [one_mul]
      refine this.trans_eq ?_
      congr 1
      ring
    · rw [hR hJ0 h]
      exact Nat.sub_le _ _
  · set R := blockSubst B⁻¹ (hasseDeriv I P)
    have hA0 : 0 ≤ ⨆ J, (w.under K) (R.coeff J) := Real.iSup_nonneg fun _ ↦ apply_nonneg _ _
    have hsup : (⨆ J, w.1 ((map (algebraMap K F) R).coeff J)) ≤
        (⨆ J, (w.under K) (R.coeff J)) ^ e := by
      refine ciSup_le fun J ↦ ?_
      rw [coeff_map]
      change w (algebraMap K F (R.coeff J)) ≤ _
      rw [FinitePlace.apply_algebraMap w (w.under K)]
      exact pow_le_pow_left₀ (apply_nonneg _ _)
        (le_ciSup (Finsupp.bddAbove_range_apply R.coeff (w.under K).1) J) _
    rw [one_pow, one_mul, mul_pow, ← Real.exp_nat_mul]
    refine mul_le_mul hsup (le_of_eq ?_) (Real.exp_pos _).le (pow_nonneg hA0 _)
    congr 1
    ring

/-! ### The product formula -/

omit [NumberField K] in
/-- A finite product of exponentials is the exponential of the finite sum. -/
private theorem finprod_exp {α : Type*} {g : α → ℝ} (hg : (Function.support g).Finite) :
    ∏ᶠ a, Real.exp (g a) = Real.exp (∑ᶠ a, g a) := by
  classical
  rw [finsum_eq_sum_of_support_subset g (s := hg.toFinset) (by simp),
    finprod_eq_prod_of_mulSupport_subset _ (s := hg.toFinset) fun a ha ↦ by
      rw [Set.Finite.coe_toFinset]
      intro h
      exact ha (by simp [h]),
    Real.exp_sum]

/-- **EF13 (14.10)–(14.17) and the product formula.** Let `x_h ∈ F^N` (`N = C(n, p)`) satisfy the
local bounds of (14.15), `P` the polynomial of Prop. 13.6 with (i), (ii) for the order `I`, and
`P_I(x) ≠ 0`. Then, with `A_v = max_J |d^{(v)}_{I,J}(a_P)|_v`,
`1 ≤ (∏_v A_v) (2^{N Σ r} G^{Σ r})^{[K:ℚ]} e^{[K:ℚ] Λ m (10 n ε - δ/(nN))}`. -/
theorem one_le_evalBound [NumberField F] (hp : 1 ≤ p) (hpn : p < Fintype.card ι)
    {c : FormExponent K ι} (hc0 : ∀ v, ∑ i, c.vec v i = 0)
    (hγ : (∑ v, ⨆ i, c.arch v i) + ∑ᶠ v, ⨆ i, c.fin v i ≤ 1) {v₀ : FinitePlace K}
    (hL : L.fin v₀ = 1) (hc₀ : c.fin v₀ = 0) (hr : ∀ h, 0 < r h) (hP : IsMultiHomogeneous r P)
    (I : κ × Set.powersetCard ι p →₀ ℕ) (hQ : ∀ h, 0 < Q h) {G δ : ℝ} (hΛ : 0 ≤ Λ)
    (hε : 0 ≤ ε) (hG : 1 ≤ G)
    (ht : ∀ h, Λ ≤ r h * Real.log (Q h) ∧ r h * Real.log (Q h) ≤ (1 + ε) * Λ)
    (e : κ → Set.powersetCard ι p → ℝ) (he : ∀ h s, |e h s| ≤ Fintype.card ι)
    (hPi : ∀ v J, 4 * Fintype.card κ * Fintype.card ι * ε * (⨆ i, c.vec v i) <
        blockAvg r J (fun _ s ↦ (c.exteriorPower p).vec v s) →
      (blockSubst ((L.mat v).compound p)⁻¹ (hasseDeriv I P)).coeff J = 0)
    (hPii : ∀ J, -(Fintype.card κ * δ / (Fintype.card ι * Fintype.card (Set.powersetCard ι p))) +
        4 * Fintype.card κ * Fintype.card ι * ε < blockAvg r J e → (hasseDeriv I P).coeff J = 0)
    (y : κ → Set.powersetCard ι p → F)
    (harch : ∀ h (w : InfinitePlace F) s,
      w ((((L.arch (w.comap (algebraMap K F))).compound p).map (algebraMap K F) *ᵥ y h) s) ≤
        G * Q h ^ ((c.exteriorPower p).arch (w.comap (algebraMap K F)) s * finrank ℚ K /
          (w.comap (algebraMap K F)).mult))
    (hfin : ∀ h (w : FinitePlace F), w.under K ≠ v₀ → ∀ s,
      w ((((L.fin (w.under K)).compound p).map (algebraMap K F) *ᵥ y h) s) ≤
        (Q h ^ ((c.exteriorPower p).fin (w.under K) s * finrank ℚ K)) ^ w.localDegree K)
    (hv₀ : ∀ h (w : FinitePlace F), w.under K = v₀ → ∀ s,
      w (y h s) ≤ (Q h ^ (e h s * finrank ℚ K)) ^ w.localDegree K)
    (hne : eval (fun t ↦ y t.1 t.2) (map (algebraMap K F) (hasseDeriv I P)) ≠ 0) :
    1 ≤ ((∏ v : InfinitePlace K,
        (⨆ J, v ((blockSubst ((L.arch v).compound p)⁻¹ (hasseDeriv I P)).coeff J)) ^ v.mult) *
      ∏ᶠ v : FinitePlace K,
        ⨆ J, v ((blockSubst ((L.fin v).compound p)⁻¹ (hasseDeriv I P)).coeff J)) *
      (2 ^ (Fintype.card (Set.powersetCard ι p) * ∑ h, r h) * G ^ (∑ h, r h)) ^ finrank ℚ K *
      Real.exp (finrank ℚ K * Λ * (Fintype.card κ * (10 * Fintype.card ι * ε -
        δ / (Fintype.card ι * Fintype.card (Set.powersetCard ι p))))) := by
  classical
  have : Nonempty ι := Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt hpn)
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  set m : ℝ := (Fintype.card κ : ℝ) with hm_def
  set N : ℝ := (Fintype.card (Set.powersetCard ι p) : ℝ) with hN_def
  set d : ℝ := (finrank ℚ K : ℝ) with hd_def
  set D := ∑ h, r h
  set φ := algebraMap K F
  set x := eval (fun t ↦ y t.1 t.2) (map φ (hasseDeriv I P))
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  set Aa : InfinitePlace K → ℝ :=
    fun v ↦ ⨆ J, v ((blockSubst ((L.arch v).compound p)⁻¹ (hasseDeriv I P)).coeff J) with hAa
  set Af : FinitePlace K → ℝ :=
    fun v ↦ ⨆ J, v ((blockSubst ((L.fin v).compound p)⁻¹ (hasseDeriv I P)).coeff J) with hAf
  set γa : InfinitePlace K → ℝ := fun v ↦ ⨆ i, c.arch v i with hγa
  set γf : FinitePlace K → ℝ := fun v ↦ ⨆ i, c.fin v i with hγf
  set C : ℝ := 2 ^ (Fintype.card (Set.powersetCard ι p) * D) * G ^ D with hC
  set ga : InfinitePlace K → ℝ :=
    fun v ↦ C * Aa v * Real.exp (d / v.mult * Λ * (5 * m * n * ε * γa v)) with hga
  set ψ : FinitePlace K → ℝ := fun v ↦ 5 * m * n * ε * γf v +
    if v = v₀ then -(m * δ / (n * N)) + 5 * m * n * ε else 0 with hψ
  set gf : FinitePlace K → ℝ := fun v ↦ Af v * Real.exp (d * Λ * ψ v) with hgf
  have hγa0 : ∀ v, 0 ≤ γa v := fun v ↦ FormExponent.iSup_vec_nonneg (v := Sum.inl v) (hc0 _)
  have hγf0 : ∀ v, 0 ≤ γf v := fun v ↦ FormExponent.iSup_vec_nonneg (v := Sum.inr v) (hc0 _)
  have hAa0 : ∀ v, 0 ≤ Aa v := fun v ↦ Real.iSup_nonneg fun _ ↦ apply_nonneg _ _
  have hAf0 : ∀ v, 0 ≤ Af v := fun v ↦ Real.iSup_nonneg fun _ ↦ apply_nonneg _ _
  have hC0 : 0 ≤ C := by positivity
  -- the local bounds
  have hloca : ∀ w : InfinitePlace F, w x ≤ ga (w.comap φ) := by
    intro w
    set v := w.comap φ
    have h := apply_eval_le_arch (L := L) hp hpn (c := c) (v := v) (hc0 (Sum.inl v)) hr hP I hQ
      (T := 4 * m * n * ε * γa v) hΛ hε hG ht rfl (fun J hJ ↦ hPi (Sum.inl v) J hJ) y
      (fun h s ↦ harch h w s)
    simp only [← hm_def, ← hn_def, ← hd_def] at h
    rw [show (⨆ i, c.arch v i) = γa v from rfl] at h
    refine h.trans (le_of_eq ?_)
    rw [show 4 * m * n * ε * γa v + ε * m * (n * γa v) = 5 * m * n * ε * γa v by ring]
    simp only [hga, hC]
    ring
  have hlocf : ∀ w : FinitePlace F, w x ≤ gf (w.under K) ^ w.localDegree K := by
    intro w
    by_cases hw : w.under K = v₀
    · have hB : (L.fin v₀).compound p = 1 := by rw [hL, compound_one]
      have h := apply_eval_le_fin (B := (L.fin v₀).compound p)
        (det_compound_ne_zero p (L.fin_det_ne_zero v₀)) hr hP I hQ
        (T := -(m * δ / (n * N)) + 4 * m * n * ε) (F₀ := n) hΛ hε hn0 ht hw e he
        (fun J hJ ↦ by rw [hB, inv_one, blockSubst_one]; exact hPii J hJ) y
        (fun h s ↦ by
          rw [hB, Matrix.map_one _ (map_zero _) (map_one _), one_mulVec]
          exact hv₀ h w hw s)
      have hγv₀ : γf v₀ = 0 := by simp [hγf, hc₀]
      have hgv₀ : gf v₀ = Af v₀ *
          Real.exp (d * Λ * (-(m * δ / (n * N)) + 4 * m * n * ε + ε * m * n)) := by
        simp only [hgf, hψ, hγv₀, ↓reduceIte]
        congr 3
        ring
      refine h.trans (le_of_eq ?_)
      rw [hw, hgv₀]
    · set v := w.under K
      have hf : ∀ (_ : κ) s, |(c.exteriorPower p).fin v s| ≤ n * γf v :=
        fun _ s ↦ (c.abs_exteriorPower_fin_le hp hpn (hc0 (Sum.inr v)) s).trans
          (mul_le_mul_of_nonneg_right (by rw [hn_def]; exact_mod_cast Nat.sub_le _ _) (hγf0 v))
      have h := apply_eval_le_fin (B := (L.fin v).compound p)
        (det_compound_ne_zero p (L.fin_det_ne_zero v)) hr hP I hQ
        (T := 4 * m * n * ε * γf v) (F₀ := n * γf v) hΛ hε (mul_nonneg hn0 (hγf0 v)) ht rfl
        (fun _ s ↦ (c.exteriorPower p).fin v s) hf (fun J hJ ↦ hPi (Sum.inr v) J hJ) y
        (fun h s ↦ hfin h w hw s)
      have hgv : gf v = Af v * Real.exp (d * Λ * (4 * m * n * ε * γf v + ε * m * (n * γf v))) := by
        simp only [hgf, hψ, hw, ↓reduceIte, add_zero]
        congr 3
        ring
      refine h.trans (le_of_eq ?_)
      rw [hgv]
  -- the finite supports
  have hΔ : hasseDeriv I P ≠ 0 := fun h ↦ hne (by simp [x, h])
  have hQne : ∀ B ∈ L.matSet, blockSubst (B.compound p)⁻¹ (hasseDeriv I P) ≠ 0 := by
    intro B hB h
    have hdet : (B.compound p).det ≠ 0 := det_compound_ne_zero p (det_ne_zero_of_mem_matSet hB)
    have hMA : (B.compound p)⁻¹ * B.compound p = 1 :=
      nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
    refine hΔ ?_
    rw [← blockSubst_blockSubst hMA (hasseDeriv I P), h, map_zero]
  have hAfs : Af.HasFiniteMulSupport := by
    refine (L.matSet.finite_toSet.biUnion fun B hB ↦
      hasFiniteMulSupport_iSup_coeff (hQne B hB)).subset fun v hv ↦ ?_
    refine Set.mem_biUnion (x := L.fin v) (L.fin_mem_matSet v) ?_
    rw [Function.mem_mulSupport] at hv ⊢
    exact hv
  have hγfs : (Function.support γf).Finite :=
    c.finite_setOf_fin_ne_zero.subset fun v hv ↦ by
      by_contra hcon
      exact hv (by simp [hγf, show c.fin v = 0 from not_not.mp hcon])
  have hψs : (Function.support (fun v ↦ d * Λ * ψ v)).Finite :=
    (hγfs.union (Set.finite_singleton v₀)).subset fun v hv ↦ by
      by_contra hcon
      simp only [Set.mem_union, Function.mem_support, Set.mem_singleton_iff, not_or,
        not_not] at hcon
      exact hv (by simp [hψ, hcon.1, hcon.2])
  have hEs : (fun v ↦ Real.exp (d * Λ * ψ v)).HasFiniteMulSupport :=
    hψs.subset fun v hv h ↦ hv (by
      change Real.exp (d * Λ * ψ v) = 1
      rw [show d * Λ * ψ v = 0 from h, Real.exp_zero])
  have hgfs : gf.HasFiniteMulSupport := Function.HasFiniteMulSupport.mul hAfs hEs
  have hga0 : ∀ v, 0 ≤ ga v := fun v ↦ by have := hAa0 v; positivity
  have hgf0 : ∀ v, 0 ≤ gf v := fun v ↦ by have := hAf0 v; positivity
  -- the product formula
  have hpf := NumberField.prod_abs_eq_one hne
  have hk : 0 < finrank K F := Module.finrank_pos
  have harch_le : ∏ w : InfinitePlace F, w x ^ w.mult ≤ (∏ v, ga v ^ v.mult) ^ finrank K F := by
    rw [← prod_infinitePlace_pow_mult_eq ga (fun w ↦ ga (w.comap φ)) fun _ ↦ rfl]
    exact prod_le_prod₀ (fun w _ ↦ pow_nonneg (apply_nonneg _ _) _)
      fun w _ ↦ pow_le_pow_left₀ (apply_nonneg _ _) (hloca w) _
  have hfin_le : ∏ᶠ w : FinitePlace F, w x ≤ (∏ᶠ v, gf v) ^ finrank K F := by
    rw [← FinitePlace.finprod_under_pow_localDegree (F := F) gf hgfs]
    exact Twist.finprod_le_finprod_of_nonneg (FinitePlace.hasFiniteMulSupport hne)
      (FinitePlace.hasFiniteMulSupport_comp_under hgfs _) (fun w ↦ apply_nonneg _ _) hlocf
  have hX : 1 ≤ (∏ v, ga v ^ v.mult) * ∏ᶠ v, gf v := by
    refine not_lt.mp fun hlt ↦ ?_
    have h0 : 0 ≤ (∏ v, ga v ^ v.mult) * ∏ᶠ v, gf v :=
      mul_nonneg (prod_nonneg fun v _ ↦ pow_nonneg (hga0 v) _) (finprod_nonneg hgf0)
    have h1 := pow_lt_one₀ h0 hlt hk.ne'
    rw [mul_pow] at h1
    have h2 := mul_le_mul harch_le hfin_le (finprod_nonneg fun w ↦ apply_nonneg _ _)
      (pow_nonneg (prod_nonneg fun v _ ↦ pow_nonneg (hga0 v) _) _)
    linarith
  -- the two products
  have hga_eq : ∏ v, ga v ^ v.mult = (∏ v, Aa v ^ v.mult) * C ^ finrank ℚ K *
      Real.exp (d * Λ * (5 * m * n * ε * ∑ v, γa v)) := by
    have hexp : ∀ v : InfinitePlace K,
        Real.exp (d / v.mult * Λ * (5 * m * n * ε * γa v)) ^ v.mult =
          Real.exp (d * Λ * (5 * m * n * ε * γa v)) := fun v ↦ by
      rw [← Real.exp_nat_mul]
      congr 1
      have : (v.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr v.mult_ne_zero
      field_simp
    simp only [hga, mul_pow, prod_mul_distrib]
    rw [prod_congr rfl fun v _ ↦ hexp v, ← Real.exp_sum, prod_pow_eq_pow_sum,
      InfinitePlace.sum_mult_eq, mul_sum, mul_sum]
    ring
  have hgf_eq : ∏ᶠ v, gf v = (∏ᶠ v, Af v) *
      Real.exp (d * Λ * (5 * m * n * ε * (∑ᶠ v, γf v) + (-(m * δ / (n * N)) + 5 * m * n * ε))) := by
    rw [finprod_mul_distrib hAfs hEs, finprod_exp hψs]
    congr 2
    rw [← mul_finsum, show (fun v ↦ ψ v) = (fun v ↦ 5 * m * n * ε * γf v +
      (if v = v₀ then -(m * δ / (n * N)) + 5 * m * n * ε else 0)) from rfl,
      finsum_add_distrib (hγfs.subset fun v hv h ↦ hv (by simp [h]))
        ((Set.finite_singleton v₀).subset fun v hv ↦ by
          by_contra h
          exact hv (by simp [show v ≠ v₀ from h])),
      ← mul_finsum, finsum_eq_single (fun v ↦ if v = v₀ then -(m * δ / (n * N)) +
        5 * m * n * ε else 0) v₀ fun v hv ↦ by simp [hv]]
    simp
  refine hX.trans ?_
  rw [hga_eq, hgf_eq]
  have hsum : (∑ v, γa v) + ∑ᶠ v, γf v ≤ 1 := hγ
  have hexp : Real.exp (d * Λ * (5 * m * n * ε * ∑ v, γa v)) *
      Real.exp (d * Λ * (5 * m * n * ε * (∑ᶠ v, γf v) + (-(m * δ / (n * N)) + 5 * m * n * ε))) ≤
      Real.exp (d * Λ * (m * (10 * n * ε - δ / (n * N)))) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have h5 : 0 ≤ d * Λ * (5 * m * n * ε) := by positivity
    have h6 := mul_le_mul_of_nonneg_left hsum h5
    have e1 : d * Λ * (5 * m * n * ε * ∑ v, γa v) + d * Λ * (5 * m * n * ε * (∑ᶠ v, γf v) +
        (-(m * δ / (n * N)) + 5 * m * n * ε)) = d * Λ * (5 * m * n * ε) *
          ((∑ v, γa v) + ∑ᶠ v, γf v) + d * Λ * (-(m * δ / (n * N)) + 5 * m * n * ε) := by ring
    have e2 : d * Λ * (m * (10 * n * ε - δ / (n * N))) = d * Λ * (5 * m * n * ε) * 1 +
        d * Λ * (-(m * δ / (n * N)) + 5 * m * n * ε) := by ring
    rw [e1, e2]
    linarith
  have hP0 : 0 ≤ (∏ v, Aa v ^ v.mult) * ∏ᶠ v, Af v * C ^ finrank ℚ K :=
    mul_nonneg (prod_nonneg fun v _ ↦ pow_nonneg (hAa0 v) _)
      (finprod_nonneg fun v ↦ mul_nonneg (hAf0 v) (pow_nonneg hC0 _))
  calc (∏ v, Aa v ^ v.mult) * C ^ finrank ℚ K * Real.exp (d * Λ * (5 * m * n * ε * ∑ v, γa v)) *
        ((∏ᶠ v, Af v) * Real.exp (d * Λ * (5 * m * n * ε * (∑ᶠ v, γf v) +
          (-(m * δ / (n * N)) + 5 * m * n * ε))))
      = ((∏ v, Aa v ^ v.mult) * (∏ᶠ v, Af v)) * C ^ finrank ℚ K *
          (Real.exp (d * Λ * (5 * m * n * ε * ∑ v, γa v)) *
            Real.exp (d * Λ * (5 * m * n * ε * (∑ᶠ v, γf v) +
              (-(m * δ / (n * N)) + 5 * m * n * ε)))) := by ring
    _ ≤ ((∏ v, Aa v ^ v.mult) * (∏ᶠ v, Af v)) * C ^ finrank ℚ K *
          Real.exp (d * Λ * (m * (10 * n * ε - δ / (n * N)))) := by
        refine mul_le_mul_of_nonneg_left hexp (mul_nonneg (mul_nonneg
          (prod_nonneg fun v _ ↦ pow_nonneg (hAa0 v) _) (finprod_nonneg hAf0))
          (pow_nonneg hC0 _))

end FormSystem

end NumberField
