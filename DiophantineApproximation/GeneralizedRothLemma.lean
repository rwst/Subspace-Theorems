/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.FormSpecialization
public import DiophantineApproximation.RothLemma

/-!
# The generalized Roth lemma

**Bombieri–Gubler, Lemma 7.5.19.** Let `P` be a nonzero multihomogeneous polynomial in `m + 1`
blocks of `n + 1` variables over a number field, of multidegree at most `d`, let `M h` be a
nonzero linear form on the `h`-th block, and let `0 < σ ≤ 1 / 2`. If the degrees drop,
`d (h + 1) ≤ σ d h`, and the forms have large height,
`n σ⁻¹ (h(P) + 4 (m + 1) d 0) ≤ d h · h(M h)` for every `h`, then the index of `P` along the
forms is at most `2 (m + 1) σ ^ ((1 / 2) ^ m)`.

This is Layer 2.7 in multihomogeneous dress, and the proof is the reduction to it:
`DiophantineApproximation/FormSpecialization.lean` specializes every block to two coordinates
without raising the height or lowering the index and then dehomogenizes to one variable per
block, and what is left is the height statement that picks the second coordinate — the height of
a tuple is at most the product of the heights of its ratios to one nonvanishing coordinate, so
one of the `n` ratios carries at least `1 / n` of it.

## Main results

* `Height.mulHeight_le_prod_mulHeight₁_div` and
  `Height.exists_logHeight_le_mul_logHeight₁_div`: **the height of a tuple against the heights
  of its ratios**, in multiplicative and logarithmic form. The second is the book's
  `h(b) ≤ n max_i h((b 0, b i))`.
* `MvPolynomial.mulHeight_le_of_coeff_subfamily` and
  `MvPolynomial.logHeight_le_of_coeff_subfamily`: a polynomial whose coefficients are
  coefficients of another has at most its height.
* `MvPolynomial.formIndex_le_of_degree_ratio`: **the generalized Roth lemma**.

## Implementation notes

⚠ **The factor `n` in the book's bound for the restricted form is the multiplication table.**
After normalizing one nonvanishing coordinate to `1`, each local factor of the tuple is a maximum
of numbers one of which is `1`, hence at most the product of the `n` local factors of the pairs;
and the product of the heights of the pairs is the height of the tuple of all products of subsets,
by Mathlib's `Height.mulHeight_fun_prod_eq`. No inequality between local factors has to be
transported by hand: the tuple of ratios is a re-indexing of that multiplication table, and
`Height.mulHeight_comp_le` finishes.

⚠ **`1 ≤ n` is load-bearing, and it is the only place it is used.** With `n = 0` there is no
second coordinate to keep, the block has one variable, and the dehomogenization has nothing to
dehomogenize. It enters as the nonemptiness of `Finset.univ.erase (i₀ h)`.

⚠ **The second kept coordinate need not be one where the form survives.** The book arranges
`b (j 1) ≠ 0` so as to have a genuine point `ξ j = -b (j 0) / b (j 1)`; here the point is
`-M h (i₁ h)` whatever that is, and the hypothesis on the heights is passed to Layer 2.7
verbatim. The case `M h (i₁ h) = 0` cannot occur under that hypothesis — it would force
`h(M h) = 0` against `h(P) + 4 (m + 1) d 0 > 0` — but the proof never has to know that.

⚠ **The book's "partial degrees at most `d`" is multihomogeneity of multidegree at most `d`.**
The dehomogenization needs a multidegree, not just a degree bound: it is the multidegree that
makes the map injective on monomials. The statement therefore carries an explicit multidegree
`r` with `r h ≤ d h`, which is what Layer 5.2's auxiliary polynomial supplies.

⚠ **Heights are Mathlib's relative ones**, so the constant term `4 (m + 1) d 0` of the
hypothesis carries the factor `totalWeight K`, exactly as in Layer 2.7; dividing every height by
`totalWeight K = [K : ℚ]` gives the book's statement in absolute logarithmic heights.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 7.5.19.

This is Layer 5.3 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

noncomputable section

open Finset Height AdmissibleAbsValues

open scoped ENNReal

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The height of a tuple is at most the product of the heights of its ratios** to one
nonvanishing coordinate. The ratios normalize that coordinate to `1`, and then each local factor
is a maximum of numbers at least one of which is `1`, hence at most the product. -/
theorem mulHeight_le_prod_mulHeight₁_div (b : ι → K) (i₀ : ι) (hb : b i₀ ≠ 0) :
    mulHeight b ≤ ∏ i ∈ univ.erase i₀, mulHeight₁ (b i / b i₀) := by
  classical
  have hci₀ : b i₀ / b i₀ = 1 := div_self hb
  have hbc : mulHeight (fun i ↦ b i / b i₀) = mulHeight b := by
    have hsmul : (fun i ↦ b i / b i₀) = (b i₀)⁻¹ • b := by
      funext i
      simp [div_eq_inv_mul, mul_comm]
    rw [hsmul, mulHeight_smul_eq_mulHeight b (inv_ne_zero hb)]
  have hx : ∀ a : {i : ι // i ∈ univ.erase i₀},
      (![b a.val / b i₀, 1] : Fin 2 → K) ≠ 0 := by
    intro a hc0
    have h1 := congrFun hc0 1
    simp at h1
  have htab := mulHeight_fun_prod_eq (x := fun a : {i : ι // i ∈ univ.erase i₀} ↦
    (![b a.val / b i₀, 1] : Fin 2 → K)) hx
  have hcomp : (fun i ↦ b i / b i₀)
      = (fun I : {i : ι // i ∈ univ.erase i₀} → Fin 2 ↦
          ∏ a, (![b a.val / b i₀, 1] : Fin 2 → K) (I a)) ∘
        (fun i ↦ fun a : {i : ι // i ∈ univ.erase i₀} ↦ if a.val = i then 0 else 1) := by
    funext i
    simp only [Function.comp_apply]
    by_cases hi : i = i₀
    · rw [hi, hci₀]
      refine (Finset.prod_eq_one fun a _ ↦ ?_).symm
      have hane : a.val ≠ i₀ := (Finset.mem_erase.mp a.prop).1
      simp [hane]
    · have hmem : i ∈ univ.erase i₀ := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
      rw [Finset.prod_eq_single_of_mem (⟨i, hmem⟩ : {i : ι // i ∈ univ.erase i₀})
        (Finset.mem_univ _) (fun a _ ha ↦ ?_)]
      · simp
      · have hav : a.val ≠ i := fun hc2 ↦ ha (Subtype.ext hc2)
        simp [hav]
  rw [← hbc, hcomp]
  refine le_trans (mulHeight_comp_le _ _) ?_
  rw [htab, ← Finset.prod_coe_sort (univ.erase i₀) (fun i ↦ mulHeight₁ (b i / b i₀))]
  exact le_of_eq (Finset.prod_congr rfl fun a _ ↦ (mulHeight₁_eq_mulHeight _).symm)

/-- **The logarithmic form**: some ratio to a nonvanishing coordinate carries at least the
fraction `1 / (card ι - 1)` of the height of the tuple. -/
theorem exists_logHeight_le_mul_logHeight₁_div (b : ι → K) (i₀ : ι) (hb : b i₀ ≠ 0)
    (hne : (univ.erase i₀).Nonempty) :
    ∃ i₁, i₁ ≠ i₀ ∧
      logHeight b ≤ (#(univ.erase i₀) : ℝ) * logHeight₁ (b i₁ / b i₀) := by
  classical
  obtain ⟨i₁, hi₁, hmax⟩ :=
    Finset.exists_max_image (univ.erase i₀) (fun i ↦ logHeight₁ (b i / b i₀)) hne
  refine ⟨i₁, (Finset.mem_erase.mp hi₁).1, ?_⟩
  have h1 : logHeight b ≤ ∑ i ∈ univ.erase i₀, logHeight₁ (b i / b i₀) := by
    simp only [logHeight_eq_log_mulHeight, logHeight₁_eq_log_mulHeight₁]
    rw [← Real.log_prod (fun i (_ : i ∈ univ.erase i₀) ↦ (mulHeight₁_pos (b i / b i₀)).ne')]
    exact Real.log_le_log (mulHeight_pos b) (mulHeight_le_prod_mulHeight₁_div b i₀ hb)
  refine h1.trans ?_
  have h2 := Finset.sum_le_card_nsmul (univ.erase i₀) (fun i ↦ logHeight₁ (b i / b i₀))
    (logHeight₁ (b i₁ / b i₀)) hmax
  rwa [nsmul_eq_mul] at h2

end Height


namespace MvPolynomial

/-! ### The height of a polynomial whose coefficients are coefficients of another -/

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

theorem mulHeight_le_of_coeff_subfamily {σ τ : Type*} {P : MvPolynomial σ K}
    {Q : MvPolynomial τ K} (h : ∀ ν ∈ P.support, ∃ μ ∈ Q.support, P.coeff ν = Q.coeff μ) :
    P.mulHeight ≤ Q.mulHeight := by
  classical
  choose f hf hval using h
  rw [MvPolynomial.mulHeight, MvPolynomial.mulHeight,
    Finsupp.mulHeight_eq_mulHeight_subtype P.coeff (le_of_eq rfl),
    Finsupp.mulHeight_eq_mulHeight_subtype Q.coeff (le_of_eq rfl)]
  have key := Height.mulHeight_comp_le
      (fun ν : {ν // ν ∈ P.coeff.support} ↦ (⟨f ν.val ν.prop, hf ν.val ν.prop⟩ :
        {μ // μ ∈ Q.coeff.support}))
      (fun μ : {μ // μ ∈ Q.coeff.support} ↦ Q.coeff μ.val)
  refine le_trans (le_of_eq ?_) key
  exact congrArg Height.mulHeight (funext fun ν ↦ hval ν.val ν.prop)

theorem logHeight_le_of_coeff_subfamily {σ τ : Type*} {P : MvPolynomial σ K}
    {Q : MvPolynomial τ K} (h : ∀ ν ∈ P.support, ∃ μ ∈ Q.support, P.coeff ν = Q.coeff μ) :
    P.logHeight ≤ Q.logHeight :=
  Real.log_le_log (Finsupp.mulHeight_pos _) (mulHeight_le_of_coeff_subfamily h)


/-! ### The generalized Roth lemma -/

section Main

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Layer 5.3. The generalized Roth lemma** (Bombieri–Gubler, Lemma 7.5.19): a nonzero
multihomogeneous polynomial of multidegree at most `d`, with degrees dropping by a factor `σ` at
every step and linear forms whose heights are large against the height of the polynomial, has
index at most `2 (m + 1) σ ^ ((1 / 2) ^ m)` along those forms. -/
theorem formIndex_le_of_degree_ratio {n m : ℕ} (hn : 1 ≤ n) (hcard : Fintype.card ι = n + 1)
    {d : Fin (m + 1) → ℕ} (hd1 : ∀ h, 1 ≤ d h)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 2)
    (hratio : ∀ h : Fin m, (d h.succ : ℝ) ≤ σ * d h.castSucc)
    {r : Fin (m + 1) → ℕ} {P : MvPolynomial (Fin (m + 1) × ι) K} (hP0 : P ≠ 0)
    (hP : IsMultiHomogeneous r P) (hrd : ∀ h, r h ≤ d h)
    {M : Fin (m + 1) → ι → K} (hM : ∀ h, M h ≠ 0)
    (hheight : ∀ h, (n : ℝ) * σ⁻¹ * (P.logHeight + 4 * (m + 1) * d 0 * totalWeight K)
      ≤ d h * Height.logHeight (M h)) :
    formIndex (fun h ↦ (d h : ℝ)) M P
      ≤ ENNReal.ofReal (2 * ((m : ℝ) + 1) * σ ^ ((1 / 2 : ℝ) ^ m)) := by
  classical
  obtain ⟨i₀, hi₀⟩ := exists_forall_apply_ne_zero hM
  obtain ⟨N, hNeq, hN1, hNH⟩ : ∃ N : Fin (m + 1) → ι → K,
      formIndex (fun h ↦ (d h : ℝ)) N P = formIndex (fun h ↦ (d h : ℝ)) M P ∧
        (∀ h, N h (i₀ h) = 1) ∧ (∀ h, Height.logHeight (N h) = Height.logHeight (M h)) :=
    ⟨fun h i ↦ (M h (i₀ h))⁻¹ * M h i, formIndex_smul (fun h ↦ inv_ne_zero (hi₀ h)) P,
      fun h ↦ inv_mul_cancel₀ (hi₀ h),
      fun h ↦ Height.logHeight_smul_eq_logHeight (M h) (inv_ne_zero (hi₀ h))⟩
  have hN0 : ∀ h, N h (i₀ h) ≠ 0 := fun h ↦ by rw [hN1 h]; exact one_ne_zero
  have hchoice : ∀ h, ∃ i₁, i₁ ≠ i₀ h ∧
      Height.logHeight (N h) ≤ (n : ℝ) * Height.logHeight₁ (N h i₁) := by
    intro h
    have hcarde : #(univ.erase (i₀ h)) = n := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard]
      omega
    have hnee : (univ.erase (i₀ h)).Nonempty := by
      rw [← Finset.card_pos, hcarde]
      omega
    obtain ⟨i₁, hi₁ne, hi₁le⟩ :=
      Height.exists_logHeight_le_mul_logHeight₁_div (N h) (i₀ h) (hN0 h) hnee
    exact ⟨i₁, hi₁ne, by rwa [hcarde, hN1 h, div_one] at hi₁le⟩
  choose i₁ hi₁ne hi₁le using hchoice
  obtain ⟨T, hTmem⟩ : ∃ T : Finset (Fin (m + 1) × ι),
      ∀ t : Fin (m + 1) × ι, t ∈ T ↔ (t.2 ≠ i₀ t.1 ∧ t.2 ≠ i₁ t.1) :=
    ⟨univ.filter (fun t ↦ t.2 ≠ i₀ t.1 ∧ t.2 ≠ i₁ t.1), fun t ↦ by simp⟩
  obtain ⟨k, Q, hkzero, hQ0, hQcoeff, hQsupp, ⟨r', hr', hQhom⟩, hidx⟩ :=
    exists_elimination (d := fun h ↦ (d h : ℝ)) (fun _ ↦ Nat.cast_nonneg _) (i₀ := i₀) T
      (fun t htT ↦ ((hTmem t).mp htT).1) N hN0 r P hP0 hP
  have hM1 : ∀ h, zeroOut T N h (i₀ h) = 1 := fun h ↦ by
    rw [zeroOut_apply_of_notMem N (fun hc ↦ ((hTmem _).mp hc).1 rfl), hN1 h]
  have hMi₁ : ∀ h, zeroOut T N h (i₁ h) = N h (i₁ h) := fun h ↦
    zeroOut_apply_of_notMem N (fun hc ↦ ((hTmem _).mp hc).2 rfl)
  have hMdrop : ∀ h i, i ≠ i₀ h → i ≠ i₁ h → zeroOut T N h i = 0 := fun h i h0 h1 ↦
    zeroOut_apply_of_mem N ((hTmem _).mpr ⟨h0, h1⟩)
  have hQdrop : ∀ (h : Fin (m + 1)) (i : ι), i ≠ i₀ h → i ≠ i₁ h →
      ∀ ν ∈ Q.support, ν (h, i) = 0 :=
    fun h i h0 h1 ν hν ↦ hQsupp (h, i) ((hTmem _).mpr ⟨h0, h1⟩) ν hν
  have heq := formIndex_eq_index_deHom i₀ i₁ (d := fun h ↦ (d h : ℝ))
    (fun _ ↦ Nat.cast_nonneg _) hi₁ne hM1 hMdrop hQhom hQdrop
  obtain ⟨hcorr, hsurj⟩ := deHom_coeff_correspondence i₀ i₁ hi₁ne hQhom hQdrop
  have hQ'0 : deHom i₀ i₁ Q ≠ 0 := by
    obtain ⟨ν₀, hν₀⟩ : Q.support.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr fun hc ↦ hQ0 (support_eq_empty.mp hc)
    intro hc
    refine (mem_support_iff.mp hν₀) ?_
    rw [← hcorr ν₀ hν₀, hc]
    simp
  have hQ'deg : ∀ h, (deHom i₀ i₁ Q).degreeOf h ≤ d h := by
    intro h
    rw [degreeOf_le_iff]
    intro l hl
    obtain ⟨ν, hν, rfl⟩ := hsurj l (mem_support_iff.mp hl)
    rw [blockProj_apply]
    calc ν (h, i₀ h) ≤ ∑ i, ν (h, i) :=
          Finset.single_le_sum (f := fun i ↦ ν (h, i)) (fun _ _ ↦ Nat.zero_le _) (mem_univ _)
      _ = r' h := hQhom (mem_support_iff.mp hν) h
      _ ≤ r h := hr' h
      _ ≤ d h := hrd h
  have hlh : (deHom i₀ i₁ Q).logHeight ≤ P.logHeight := by
    refine logHeight_le_of_coeff_subfamily fun l hl ↦ ?_
    obtain ⟨ν, hν, rfl⟩ := hsurj l (mem_support_iff.mp hl)
    refine ⟨ν + k, ?_, ?_⟩
    · rw [mem_support_iff, ← hQcoeff ν (mem_support_iff.mp hν)]
      exact mem_support_iff.mp hν
    · rw [hcorr ν hν, hQcoeff ν (mem_support_iff.mp hν)]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hrothheight : ∀ h, (deHom i₀ i₁ Q).logHeight + 4 * (m + 1) * d 0 * totalWeight K
      ≤ σ * (d h * Height.logHeight₁ (-(zeroOut T N h (i₁ h)))) := by
    intro h
    rw [hMi₁ h, Height.logHeight₁_neg]
    have hstep : (n : ℝ) * σ⁻¹ * (P.logHeight + 4 * (m + 1) * d 0 * totalWeight K)
        ≤ (d h : ℝ) * ((n : ℝ) * Height.logHeight₁ (N h (i₁ h))) := by
      refine le_trans (hheight h) ?_
      rw [← hNH h]
      exact mul_le_mul_of_nonneg_left (hi₁le h) (Nat.cast_nonneg _)
    have hA : P.logHeight + 4 * (m + 1) * d 0 * totalWeight K
        ≤ σ * ((d h : ℝ) * Height.logHeight₁ (N h (i₁ h))) := by
      have hfac : (0 : ℝ) < σ / (n : ℝ) := div_pos hσ0 hnpos
      have h3 := mul_le_mul_of_nonneg_left hstep hfac.le
      calc P.logHeight + 4 * (m + 1) * d 0 * totalWeight K
          = (σ / (n : ℝ)) * ((n : ℝ) * σ⁻¹ *
              (P.logHeight + 4 * (m + 1) * d 0 * totalWeight K)) := by
            field_simp
        _ ≤ (σ / (n : ℝ)) * ((d h : ℝ) * ((n : ℝ) * Height.logHeight₁ (N h (i₁ h)))) := h3
        _ = σ * ((d h : ℝ) * Height.logHeight₁ (N h (i₁ h))) := by
            field_simp
    linarith
  have hroth := index_le_of_degree_ratio hd1 hσ0 hσ1 hratio hQ'0 hQ'deg
    (fun h ↦ -(zeroOut T N h (i₁ h))) hrothheight
  rw [← hNeq]
  exact le_trans hidx (le_trans (le_of_eq heq) hroth)

end Main

/-! ### Acceptance criteria -/

section Acceptance

/-- **Bombieri–Gubler 7.5.18**: for `n = 1` and the forms `M h = X (h, 1) - α h * X (h, 0)` the
index along the forms is the index of Layer 2.3 at the point `α` of the dehomogenization. -/
example {K : Type*} [Field K] {m : ℕ} (α : Fin (m + 1) → K) {d : Fin (m + 1) → ℝ}
    (hd : ∀ h, 0 ≤ d h) {r : Fin (m + 1) → ℕ} {Q : MvPolynomial (Fin (m + 1) × Fin 2) K}
    (hQ : IsMultiHomogeneous r Q) :
    formIndex d (fun h ↦ ![-(α h), 1]) Q
      = index d α (deHom (fun _ ↦ 1) (fun _ ↦ 0) Q) := by
  have hvac : ∀ i : Fin 2, i ≠ 1 → i ≠ 0 → False := by decide
  have key := formIndex_eq_index_deHom (M := fun h ↦ ![-(α h), (1 : K)])
    (fun _ : Fin (m + 1) ↦ (1 : Fin 2)) (fun _ ↦ (0 : Fin 2)) hd (fun _ ↦ by decide)
    (fun _ ↦ by simp) (fun _ i h0 h1 ↦ (hvac i h0 h1).elim) hQ
    (fun _ i h0 h1 ↦ (hvac i h0 h1).elim)
  have hα : (fun h ↦ -((![-(α h), (1 : K)] : Fin 2 → K) 0)) = α := by
    funext h
    simp
  rw [hα] at key
  exact key

/-- **The index of a power of one form is its weight.** This is the test that the definition
measures divisibility by the forms and nothing else. -/
example {K : Type*} [Field K] {κ ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {d : κ → ℝ} (hd : ∀ h, 0 ≤ d h) {i₀ : κ → ι} {M : κ → ι → K}
    (hM : ∀ h, M h (i₀ h) ≠ 0) (h₀ : κ) (j : ℕ) :
    formIndex d M (blockForm M h₀ ^ j) = ENNReal.ofReal (j / d h₀) := by
  rw [formIndex_eq_weightedOrder hd hM, map_pow, substFormInv_blockForm hM,
    X_pow_eq_monomial, weightedOrder_monomial one_ne_zero, Finsupp.weight_apply,
    Finsupp.sum_single_index (by simp)]
  simp only [formWeight, ite_true]
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    div_eq_mul_inv]

end Acceptance

end MvPolynomial
