/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.GeneralizedRothLemma
public import DiophantineApproximation.FormIndexSubspace
public import DiophantineApproximation.SmallPoint

public import ArithmeticHeights.Subspace

-- Used only inside proofs.
import ArithmeticHeights.Arakelov
import ArithmeticHeights.Duality
import QuantitativeSubspace.ResultantHeights
import DiophantineApproximation.MvPolynomialEvalBound

/-!
# EF13's non-vanishing result

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, Proposition 12.1 (= Evertse 1996, Lemma 26).

Let `P ≠ 0` over a number field `K` be multihomogeneous of degree `r_h` in the block `h` of
`n + 1` variables, `h < m`, with `r_h / r_{h+1} > m / ε`, and let `T_h` be the hyperplanes
`M_h(x) = 0`, `M_h ∈ K^{n+1}`, with `r_h h(M_h)` large against `h(P)` and `Σ r`. Let `y_h` be
`n` points spanning `T_h` over a field `E ⊇ K` of characteristic zero. Then there are integers
`|z_{hl}| ≤ n/ε + 1` and a derivative `P_i`, `Σ_h (Σ_l i_hl)/r_h ≤ 2mε`, that does not vanish at
the point `(Σ_l z_{hl} y_{hl})_h` of the grid.

This assembles Evertse's generalized Roth lemma (Q1.5, `formIndex_le_of_sq_lt_ratio`, applied over
`K` with Rémond's heights `resultantHeight`) with Bombieri–Gubler's passage from the index along
the forms to a non-vanishing derivative at a grid point (DA 5.5–5.6). The grid points live over
`E`, the forms over `K`: the index along the forms does not change under the extension
(`MvPolynomial.formIndex_map`).

EF13's hyperplanes are given by their Euclidean heights `H₂(T_h)`; by the duality theorem these
are the heights `H₂(M_h)` of their normal vectors (`Submodule.exists_normal_logHeight_le`, with
the comparison `h(M) ≥ h₂(M) - [K:ℚ] log √(n+1)` of the max and Euclidean norms).

## Main results

* `MvPolynomial.substFormInv_map`, `MvPolynomial.formIndex_map`: the index along the forms under a
  field extension.
* `MvPolynomial.exists_eval_hasseDeriv_ne_zero_of_logHeight`: EF13 Prop. 12.1.
* `Submodule.exists_normal_logHeight_le`: a hyperplane of `Kⁿ` as the kernel of a form whose
  height is at least that of the hyperplane, up to `[K:ℚ] log √n`.

This is milestone Q4.1c of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Finset Height AdmissibleAbsValues Module

namespace MvPolynomial

/-! ### The index along the forms under a field extension -/

section Map

variable {K E : Type*} [Field K] [Field E] (f : K →+* E) {κ ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-- The change of coordinates solving `M_h = X_{h,i₀(h)}` commutes with extending the scalars. -/
theorem substFormInv_map (i₀ : κ → ι) (M : κ → ι → K) (P : MvPolynomial (κ × ι) K) :
    substFormInv i₀ (fun h i ↦ f (M h i)) (P.map f) = (substFormInv i₀ M P).map f := by
  have key : (substFormInv i₀ (fun h i ↦ f (M h i))).toRingHom.comp (map f) =
      (map f).comp (substFormInv i₀ M).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) fun p ↦ ?_
    · simp
    · obtain ⟨h, i⟩ := p
      by_cases hi : i = i₀ h
      · subst hi
        simp [map_sub, map_sum, map_inv₀]
      · simp [substFormInv_X_of_ne _ _ hi]
  exact congrArg (· P) key

variable [Fintype κ]

omit [DecidableEq ι] in
/-- **The index along the forms does not change under a field extension.** -/
theorem formIndex_map {d : κ → ℝ} (hd : ∀ h, 0 ≤ d h) {M : κ → ι → K} (hM : ∀ h, M h ≠ 0)
    (P : MvPolynomial (κ × ι) K) :
    formIndex d (fun h i ↦ f (M h i)) (P.map f) = formIndex d M P := by
  classical
  have hex : ∀ h, ∃ i, M h i ≠ 0 := fun h ↦ Function.ne_iff.mp (hM h)
  choose i₀ hi₀ using hex
  have hi₀' : ∀ h, f (M h (i₀ h)) ≠ 0 := fun h ↦ (_root_.map_ne_zero f).2 (hi₀ h)
  have h1 := formIndex_eq_weightedOrder (d := d) hd hi₀ P
  have h2 := formIndex_eq_weightedOrder (d := d) (M := fun h i ↦ f (M h i)) hd hi₀' (P.map f)
  rw [h1, h2, substFormInv_map]
  simp only [weightedOrder, support_map_of_injective _ f.injective]

end Map

/-! ### EF13 Proposition 12.1 -/

section NonVanishing

variable {K : Type} [Field K] [NumberField K] {E : Type*} [Field E] [CharZero E] [Algebra K E]
  {ι : Type*} [Fintype ι]

/-- **EF13 Proposition 12.1** (Evertse 1996, Lemma 26). Let `P ≠ 0` over a number field `K` be
multihomogeneous of degree `r` in `m ≥ 1` blocks of `n + 1 ≥ 2` variables, `r` decreasing with
`r_h / r_{h+1} > m / ε`, and let `M_h ≠ 0` be forms over `K` with
`n max(1, m/ε)^m (10 m² [K:ℚ] Σ r + m h(P)) < r_h h(M_h)`. Let `y_{h1}, …, y_{hn} ∈ E^{n+1}` span
the hyperplane `M_h = 0` over `E`. Then for integers `|z_{hl}| ≤ n/ε + 1` and a derivative of
weighted order `Σ_h (Σ_i I_{hi})/r_h ≤ 2mε`, `P_I` does not vanish at `(Σ_l z_{hl} y_{hl})_h`. -/
theorem exists_eval_hasseDeriv_ne_zero_of_logHeight {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hcard : Fintype.card ι = n + 1) {r : Fin m → ℕ} (hr : ∀ h, 0 < r h) (hanti : Antitone r)
    {ε : ℝ} (hε : 0 < ε) (hratio : ∀ i j : Fin m, (i : ℕ) + 1 = j → (m : ℝ) / ε < r i / r j)
    {P : MvPolynomial (Fin m × ι) K} (hP0 : P ≠ 0) (hP : IsMultiHomogeneous r P)
    {M : Fin m → ι → K} (hM : ∀ h, M h ≠ 0)
    (hheight : ∀ h, (n : ℝ) * max 1 ((m : ℝ) / ε) ^ m *
      (10 * m ^ 2 * finrank ℚ K * (∑ i, r i : ℕ) + m * P.logHeight) <
        r h * Height.logHeight (M h))
    {y : Fin m → Fin n → ι → E}
    (hy : ∀ (h : Fin m) (x : ι → E), ∑ i, algebraMap K E (M h i) * x i = 0 →
      x ∈ Submodule.span E (Set.range (y h))) :
    ∃ z : Fin m → Fin n → ℤ, (∀ h l, ((z h l).natAbs : ℝ) ≤ n / ε + 1) ∧
      ∃ I : Fin m × ι →₀ ℕ, ∑ h, (∑ i, (I (h, i) : ℝ)) / r h ≤ 2 * m * ε ∧
        eval (fun p : Fin m × ι ↦ ∑ l, (z p.1 l : E) * y p.1 l p.2)
          (hasseDeriv I (P.map (algebraMap K E))) ≠ 0 := by
  classical
  set θ : ℝ := m * ε
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hθ : 0 < θ := mul_pos hm0 hε
  have hratio' : ∀ i j : Fin m, (i : ℕ) + 1 = j → (m : ℝ) ^ 2 < θ * (r i / r j) := by
    intro i j hij
    have h := hratio i j hij
    have : (m : ℝ) ^ 2 = θ * (m / ε) := by simp only [θ]; field_simp
    rw [this]
    exact mul_lt_mul_of_pos_left h hθ
  -- Rémond's heights over `K`
  have hb : Function.Surjective (Prod.fst : Fin m × Fin 2 → Fin m) :=
    fun h ↦ ⟨(h, 0), rfl⟩
  set H := resultantHeight (archEmbedded_of_numberField K) hb
  have hbot : max (H.botBound 1) 0 ≤ 7 := by
    refine max_le ((resultantHeight_botBound_le _ hb 1).trans ?_) (by norm_num)
    have h4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      linarith
    norm_num
    linarith
  set D : ℕ := ∑ i, r i
  have hD : 1 ≤ D := (hr ⟨0, hm⟩).trans_le (single_le_sum (f := r) (fun _ _ ↦ Nat.zero_le _)
    (mem_univ (⟨0, hm⟩ : Fin m)))
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hw : totalWeight K = finrank ℚ K := NumberField.totalWeight_eq_finrank K
  have hheight' : ∀ h, (n : ℝ) * (max 1 ((m : ℝ) ^ 2 / θ) ^ m *
      (totalWeight K * max (H.botBound 1) 0 * D + m * (P.logHeight +
        totalWeight K * (D * Real.log 2 + m * Real.log D + m)))) <
          r h * Height.logHeight (M h) := by
    intro h
    refine lt_of_le_of_lt ?_ (hheight h)
    have hmθ : (m : ℝ) ^ 2 / θ = m / ε := by simp only [θ]; field_simp
    rw [hmθ, hw, ← mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hd : (0 : ℝ) ≤ finrank ℚ K := Nat.cast_nonneg _
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hlogD : Real.log D ≤ D := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have key : max (H.botBound 1) 0 * D + m * (D * Real.log 2 + m * Real.log D + m) ≤
        10 * m ^ 2 * D := by
      have h1 : max (H.botBound 1) 0 * D ≤ 7 * D := mul_le_mul_of_nonneg_right hbot (by linarith)
      have h2 : D * Real.log 2 + m * Real.log D + m ≤ D + m * D + m * D := by
        have := mul_le_mul_of_nonneg_left hlogD hm0.le
        nlinarith
      have h3 := mul_le_mul_of_nonneg_left h2 hm0.le
      have h4 : (D : ℝ) ≤ m ^ 2 * D := le_mul_of_one_le_left (by linarith) (by nlinarith)
      have h5 : (m : ℝ) * D ≤ m ^ 2 * D := by nlinarith
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left key hd]
  have hidx := formIndex_le_of_sq_lt_ratio H hn hcard hr hanti hθ hratio' hP0 hP
    (fun _ ↦ le_rfl) hM hheight'
  -- pass to `E`
  set f := algebraMap K E
  set P' := P.map f
  set M' : Fin m → ι → E := fun h i ↦ f (M h i)
  have hd : ∀ h, (0 : ℝ) ≤ r h := fun h ↦ Nat.cast_nonneg _
  have hM' : ∀ h, M' h ≠ 0 := fun h hc ↦ hM h (by
    ext i
    have := congrFun hc i
    simpa [M'] using this)
  have hP'0 : P' ≠ 0 := fun hc ↦ hP0 (map_injective f f.injective (by rw [map_zero]; exact hc))
  have hP' : IsMultiHomogeneous r P' := fun ν hν h ↦ hP (by
    rw [coeff_map] at hν
    exact fun hc ↦ hν (by rw [hc, map_zero])) h
  have hidx' : formIndex (fun h ↦ (r h : ℝ)) M' P' ≤ ENNReal.ofReal θ := by
    rw [formIndex_map f hd hM P]
    exact hidx
  obtain ⟨I, hI, hne⟩ := exists_linSubst_hasseDeriv_ne_zero_of_formIndex_le hd hM' hy hP'0
    hθ.le hidx'
  have hη : (0 : ℝ) < 2 * ε := by positivity
  have hI' : ∑ h, (∑ i, (I (h, i) : ℝ)) / (r h : ℝ) ≤ Fintype.card (Fin m) * (2 * ε) / 2 := by
    rw [Fintype.card_fin]
    convert hI using 1
    simp only [θ]
    ring
  obtain ⟨z, hz, I', -, hI'', hval⟩ :=
    exists_eval_hasseDeriv_ne_zero_of_sum_div_le hP' y hη I hI' hne
  refine ⟨z, fun h l ↦ (hz h l).trans_eq ?_, I', ?_, hval⟩
  · rw [Fintype.card_fin]
    field_simp
  · rw [Fintype.card_fin] at hI''
    linarith

end NonVanishing

end MvPolynomial

namespace Submodule

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **A hyperplane is the kernel of a form of about its height**: a subspace `W ⊆ Kⁿ` of
dimension `n - 1` is `{x : M ⬝ x = 0}` for some `M ≠ 0` with
`h₂(W) ≤ [K:ℚ]/2 log n + h(M)`, by the duality theorem and the comparison of the Euclidean and
max norms. -/
theorem exists_normal_logHeight_le {W : Submodule K (ι → K)}
    (hW : finrank K W + 1 = Fintype.card ι) :
    ∃ M : ι → K, M ≠ 0 ∧ (∀ x, x ∈ W ↔ ∑ i, M i * x i = 0) ∧
      W.arakelovLogHeight ≤ (finrank ℚ K : ℝ) / 2 * Real.log (Fintype.card ι) +
        Height.logHeight M := by
  set perp : Submodule K (ι → K) → Submodule K (ι → K) :=
    fun V ↦ V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap
  have hfin : ∀ V : Submodule K (ι → K), finrank K V + finrank K (perp V) = Fintype.card ι :=
    fun V ↦ by
    have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq V
    have h2 : finrank K (perp V) = finrank K V.dualAnnihilator := by
      change finrank K (V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap) = _
      rw [comap_piEquiv_dualAnnihilator_eq_map V]
      exact LinearEquiv.finrank_map_eq _ _
    rw [h2, h1, Module.finrank_fintype_fun_eq_card]
  have hV1 : finrank K (perp W) = 1 := by have := hfin W; omega
  obtain ⟨⟨M, hMV⟩, hM0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (hV1 ▸ one_pos)
  have hM0' : M ≠ 0 := fun h ↦ hM0 (Subtype.ext h)
  have hVeq := eq_span_singleton_of_mem_of_finrank_eq_one hV1 hMV hM0'
  have hW' : W = perp (span K {M}) := by
    refine eq_of_le_of_finrank_eq (fun x hx ↦ ?_) ?_
    · refine mem_comap_piEquiv_dualAnnihilator.2 fun v hv ↦ ?_
      obtain ⟨c, rfl⟩ := mem_span_singleton.1 hv
      have := mem_comap_piEquiv_dualAnnihilator.1 hMV x hx
      rw [smul_dotProduct, dotProduct_comm, this, smul_zero]
    · have h1 := hfin (span K {M})
      rw [finrank_span_singleton hM0'] at h1
      omega
  refine ⟨M, hM0', fun x ↦ ?_, ?_⟩
  · rw [hW', mem_comap_piEquiv_dualAnnihilator]
    constructor
    · intro h
      simpa [dotProduct] using h M (mem_span_singleton_self M)
    · intro h v hv
      obtain ⟨c, rfl⟩ := mem_span_singleton.1 hv
      rw [smul_dotProduct]
      simp [dotProduct, h]
  · have : Nonempty ι := by
      by_contra hι
      rw [not_nonempty_iff] at hι
      exact hM0' (funext fun i ↦ hι.elim i)
    rw [hW', arakelovLogHeight_comap_piEquiv_dualAnnihilator, arakelovLogHeight_span_singleton hM0',
      ← NumberField.totalWeight_eq_finrank]
    exact NumberField.arakelovLogHeight_le_logHeight M

end Submodule
