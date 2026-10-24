/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormIntervalFamily
public import QuantitativeSubspace.FormSystemCount
public import DiophantineApproximation.SystemSubspaceFamily

/-!
# EF13's interval result for a set of approximation domains with the same forms

EF13's Theorem 3.3 (`NumberField.exists_forall_mem_interval_approxDomain_ef`) for a set `𝒞` of
exponents with the same forms `L` and places: the domains of every `c ∈ 𝒞` at the levels
`log Q ≥ X₀` lie in one of at most `J = (n + 1) (2^{2ⁿ})^t` proper subspaces of `Kⁱ`, or `log Q`
lies in one of at most `J (nⁿ)^t intervalCount n R δ'` intervals `[s, ω₀ s)`, where `t` is the
number of places. Neither count depends on `𝒞`. It is EF13's Theorem 2.3 for a set of exponents
(`NumberField.FormSystem.exists_intervals_cover_family`) applied to the centered exponents of
EF13 (5.2), with one normalization `κ = 2A` for the whole set: `A` bounds `t` times the absolute
weight of every `c ∈ 𝒞`, so that the centered exponents are at most `1 / t` at every place.

## Main definitions

* `NumberField.FormSystem.familyCount n t`: the number `(n + 1) (2^{2ⁿ})^t` of subspaces.

## Main results

* `NumberField.domainExponent_vec_sum`, `NumberField.domainExponent_vec_le`: the centered
  exponents sum to `0` at every place and are at most `2 A / κ`, `A` the absolute weight.
* `NumberField.exists_forall_mem_interval_approxDomain_ef_family`: the interval result for a set
  of exponents.

## References

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, Theorems 2.3 and 3.3, §5.
-/

@[expose] public section

open Finset Module IsDedekindDomain Height

namespace NumberField

/-- **The number of subspaces of EF13's Theorem 2.3 for a set of exponents** vanishing outside
`t` places: `(n + 1) (2^{2ⁿ})^t`, a bound for the number of weight types. -/
def FormSystem.familyCount (n t : ℕ) : ℕ := (n + 1) * (2 ^ 2 ^ n) ^ t

/-- **The number of intervals of EF13's Theorem 2.3 for a set of exponents** vanishing outside
`t` places: `familyCount n t · (nⁿ)^t · intervalCount n R δ`. -/
noncomputable def FormSystem.familyIntervalCount (n t R : ℕ) (δ : ℝ) : ℕ :=
  familyCount n t * ((n ^ n) ^ t * intervalCount n R δ)

variable {K : Type} [Field K] {ι : Type*} [Fintype ι] {n : ℕ}

section Exponent

variable [NumberField K] (Sfin : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ)
  (e : ι ≃ Fin n) (κ : ℝ)

/-- **EF13 (2.8) at every place**: the centered exponents sum to `0` at each place. -/
theorem domainExponent_vec_sum (v : InfinitePlace K ⊕ FinitePlace K) :
    ∑ i, (domainExponent Sfin c e κ).vec v i = 0 := by
  classical
  rcases v with w | v
  · simp only [FormExponent.vec, Sum.elim_inl, domainExponent, ← sum_div, ← sum_mul,
      sum_sub_mean, zero_mul, zero_div]
  · by_cases hv : v ∈ Sfin
    · simp only [FormExponent.vec, Sum.elim_inr, domainExponent, hv, ite_true, ← sum_div,
        sum_sub_mean, zero_div]
    · simp [FormExponent.vec, domainExponent, hv]

/-- **The centered exponents are small at every place**: at most `2 A / κ`, `A` the absolute
weight of `c`. -/
theorem domainExponent_vec_le (hκ : 0 < κ) (v : InfinitePlace K ⊕ FinitePlace K) (i : Fin n) :
    (domainExponent Sfin c e κ).vec v i ≤ 2 * approxAbsWeight Sfin c / κ := by
  classical
  have hA := approxAbsWeight_nonneg Sfin c
  rcases v with w | v
  · have h := iSup_sub_mean_mul_le (c w.1) e (t := w.mult / κ) (by positivity)
    have hi : (c w.1 (e.symm i) - (∑ j, c w.1 j) / n) * (w.mult / κ) ≤
        ⨆ i : Fin n, (c w.1 (e.symm i) - (∑ j, c w.1 j) / n) * (w.mult / κ) :=
      le_ciSup (f := fun i : Fin n ↦ (c w.1 (e.symm i) - (∑ j, c w.1 j) / n) * (w.mult / κ))
        (Set.finite_range _).bddAbove i
    have hw : (w.mult : ℝ) * ∑ j, |c w.1 j| ≤ approxAbsWeight Sfin c := by
      rw [approxAbsWeight]
      refine le_add_of_le_of_nonneg ?_ (sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _)
      exact single_le_sum (f := fun w : InfinitePlace K ↦ (w.mult : ℝ) * ∑ j, |c w.1 j|)
        (fun _ _ ↦ by positivity) (mem_univ w)
    change (c w.1 (e.symm i) - (∑ j, c w.1 j) / n) * w.mult / κ ≤ _
    rw [mul_div_assoc]
    refine (hi.trans h).trans ?_
    rw [mul_div_assoc', div_mul_eq_mul_div, mul_assoc]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by norm_num)) hκ.le
  · by_cases hv : v ∈ Sfin
    · have h := iSup_sub_mean_mul_le (c v.1) e (t := κ⁻¹) (by positivity)
      have hi : (c v.1 (e.symm i) - (∑ j, c v.1 j) / n) * κ⁻¹ ≤
          ⨆ i : Fin n, (c v.1 (e.symm i) - (∑ j, c v.1 j) / n) * κ⁻¹ :=
        le_ciSup (f := fun i : Fin n ↦ (c v.1 (e.symm i) - (∑ j, c v.1 j) / n) * κ⁻¹)
          (Set.finite_range _).bddAbove i
      have hw : ∑ j, |c v.1 j| ≤ approxAbsWeight Sfin c := by
        rw [approxAbsWeight]
        refine le_add_of_nonneg_of_le
          (sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _)
            (sum_nonneg fun _ _ ↦ abs_nonneg _)) ?_
        exact single_le_sum (f := fun v : FinitePlace K ↦ ∑ j, |c v.1 j|)
          (fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _) hv
      change (if v ∈ Sfin then (c v.1 (e.symm i) - (∑ j, c v.1 j) / n) / κ else 0) ≤ _
      simp only [hv, ↓reduceIte, div_eq_mul_inv]
      refine (hi.trans h).trans ?_
      rw [mul_right_comm]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by norm_num))
        (by positivity)
    · change (if v ∈ Sfin then (c v.1 (e.symm i) - (∑ j, c v.1 j) / n) / κ else 0) ≤ _
      simp only [hv, ↓reduceIte]
      positivity

end Exponent

section Interval

open scoped Classical in
/-- **EF13 Theorem 3.3 for a set of approximation domains with the same forms.** Let `L` be forms
on `Kⁱ`, `#ι = n ≥ 2`, independent at the `t = #∞ + #Sfin` places, with at most `s` distinct
forms, let `𝒞` be a set of exponents of weight `≤ -ε`, and let `A ≥ ε / 4n` bound `t` times the
absolute weight of every `c ∈ 𝒞`. For `R ≥ s + n` with `t ≤ Rⁿ` there are at most
`J = familyCount n t` proper subspaces `W` and at most `J (nⁿ)^t intervalCount n R δ'` reals
`x ≥ X₀`, `δ' = ε / 4nA`, such that for every `c ∈ 𝒞` and every level `Q` with `log Q ≥ X₀` the
domain of `c` at level `Q` lies in one of the `W`, or `log Q` lies in one of the intervals
`[x, ω₀ x)`, `ω₀ = cutRatio R δ'`. -/
theorem exists_forall_mem_interval_approxDomain_ef_family [Nontrivial ι] [DecidableEq ι]
    [NumberField K] {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (𝒞 : Set (AbsoluteValue K ℝ → ι → ℝ))
    {ε : ℝ} (hε : 0 < ε) (hc : ∀ c ∈ 𝒞, approxWeight Sfin c ≤ -ε) {A : ℝ}
    (hεA : ε ≤ 4 * Fintype.card ι * A)
    (hA : ∀ c ∈ 𝒞, (Fintype.card (InfinitePlace K) + #Sfin) * approxAbsWeight Sfin c ≤ A)
    {s : ℕ} (hs : formCount Sfin L ≤ s) {R : ℕ} (hsR : s + Fintype.card ι ≤ R)
    (htR : Fintype.card (InfinitePlace K) + #Sfin ≤ R ^ Fintype.card ι) {X₀ : ℝ}
    (hX₀ : domainThreshold (Fintype.card ι) (finrank ℚ K) s ε A (formLogHeight Sfin L) ≤ X₀) :
    ∃ T : Finset (Submodule K (ι → K)),
      #T ≤ FormSystem.familyCount (Fintype.card ι) (Fintype.card (InfinitePlace K) + #Sfin) ∧
      (∀ W ∈ T, W ≠ ⊤) ∧ ∃ 𝒯 : Finset ℝ,
        #𝒯 ≤ FormSystem.familyIntervalCount (Fintype.card ι)
          (Fintype.card (InfinitePlace K) + #Sfin) R (domainDelta (Fintype.card ι) ε A) ∧
        (∀ x ∈ 𝒯, X₀ ≤ x) ∧ ∀ c ∈ 𝒞, ∀ Q : ℝ, 1 < Q → X₀ ≤ Real.log Q →
          (∃ W ∈ T, approxDomain Sfin L c Q ⊆ W) ∨
            ∃ x ∈ 𝒯, x ≤ Real.log Q ∧ Real.log Q <
              FormSystem.cutRatio R (domainDelta (Fintype.card ι) ε A) * x := by
  set n := Fintype.card ι with hn
  have hn2 : 2 ≤ n := Fintype.one_lt_card
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set e := Fintype.equivFin ι
  set t := Fintype.card (InfinitePlace K) + #Sfin with ht
  have ht1 : 1 ≤ t := by
    have := Fintype.card_pos (α := InfinitePlace K)
    omega
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hA0 : 0 < A := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hn0.le h]
  have hκ0 : 0 < 2 * A := by positivity
  set L' := domainSystem L e Sfin hLInf hLFin
  set δ' := domainDelta n ε A with hδ'
  have hδ'0 : 0 < δ' := by rw [hδ', domainDelta]; positivity
  have hδ'1 : δ' ≤ 1 := by
    rw [hδ', domainDelta, div_le_one (by positivity)]
    linarith
  have hR : #L'.forms ≤ R := (card_forms_domainSystem_le e hLInf hLFin).trans (by omega)
  -- the places and the common bound `1 / t`
  set S₁ : Finset (InfinitePlace K ⊕ FinitePlace K) :=
    (univ : Finset (InfinitePlace K)).disjSum Sfin with hS₁
  have hS₁card : #S₁ = t := by rw [hS₁, card_disjSum, card_univ]
  obtain ⟨γ, hγin, hγout⟩ : ∃ γ : InfinitePlace K ⊕ FinitePlace K → ℝ,
      (∀ v ∈ S₁, γ v = (t : ℝ)⁻¹) ∧ ∀ v ∉ S₁, γ v = 0 :=
    ⟨fun v ↦ if v ∈ S₁ then (t : ℝ)⁻¹ else 0, fun v hv ↦ by simp [hv], fun v hv ↦ by simp [hv]⟩
  set 𝒞' : Set (FormExponent K (Fin n)) := (fun c ↦ domainExponent Sfin c e (2 * A)) '' 𝒞
  have hle : ∀ c ∈ 𝒞, 2 * approxAbsWeight Sfin c / (2 * A) ≤ (t : ℝ)⁻¹ := by
    intro c hc
    rw [mul_div_mul_left _ _ (two_ne_zero), div_le_iff₀ hA0, ← div_eq_inv_mul,
      le_div_iff₀ ht0, mul_comm, ht]
    push_cast
    exact hA c hc
  have hvec0 : ∀ c, ∀ v ∉ S₁, (domainExponent Sfin c e (2 * A)).vec v = 0 := by
    intro c v hv
    rcases v with w | v
    · exact absurd (mem_disjSum.2 (Or.inl ⟨w, mem_univ _, rfl⟩)) hv
    · have hv' : v ∉ Sfin := fun h ↦ hv (mem_disjSum.2 (Or.inr ⟨v, h, rfl⟩))
      funext i
      simp [FormExponent.vec, domainExponent, hv']
  obtain ⟨𝒯, h𝒯card, h𝒯top, b, hbcard, hbge, hcov⟩ := L'.exists_intervals_cover_family
    (Ω := AlgebraicClosure K) hn2 𝒞'
    (by rintro _ ⟨c, -, rfl⟩ v; exact domainExponent_vec_sum Sfin c e _ v)
    (by
      rintro _ ⟨c, hc, rfl⟩
      exact (domainExponent_sup_le Sfin c e _ hκ0).trans ((hle c hc).trans
        (inv_le_one_of_one_le₀ (by exact_mod_cast ht1))))
    (γ := γ)
    (by
      rintro _ ⟨c, hc, rfl⟩ v i
      by_cases hv : v ∈ S₁
      · rw [hγin v hv]
        exact (domainExponent_vec_le Sfin c e _ hκ0 v i).trans (hle c hc)
      · rw [hvec0 c v hv, hγout v hv]; rfl)
    (fun v ↦ by
      by_cases hv : v ∈ S₁
      · rw [hγin v hv]; positivity
      · rw [hγout v hv])
    (by
      have hfin : ∑ᶠ v, γ (.inr v) = ∑ v ∈ Sfin, (t : ℝ)⁻¹ := by
        rw [finsum_eq_sum_of_support_subset _ (s := Sfin) ?_]
        · refine sum_congr rfl fun v hv ↦ ?_
          rw [hγin _ (mem_disjSum.2 (Or.inr ⟨v, hv, rfl⟩))]
        · intro v hv
          by_contra h
          exact hv (hγout _ fun h' ↦ h (by simpa [hS₁] using h'))
      have hinf : ∑ w, γ (.inl w) = ∑ _w : InfinitePlace K, (t : ℝ)⁻¹ :=
        sum_congr rfl fun w _ ↦ hγin _ (mem_disjSum.2 (Or.inl ⟨w, mem_univ _, rfl⟩))
      rw [hfin, hinf, sum_const, sum_const, card_univ, nsmul_eq_mul, nsmul_eq_mul, ← add_mul,
]
      have htc : ((Fintype.card (InfinitePlace K) : ℝ) + #Sfin) = t := by rw [ht]; push_cast; rfl
      rw [htc, mul_inv_cancel₀ ht0.ne'])
    S₁ (by rintro _ ⟨c, -, rfl⟩ v hv; exact hvec0 c v hv)
    hγout hR (by rw [hS₁card]; exact htR) hδ'0 hδ'1
  rw [hS₁card] at h𝒯card hbcard
  refine ⟨𝒯.image (domainComap K e), card_image_le.trans h𝒯card, ?_,
    b.image fun b' ↦ max X₀ (Real.log b' / (2 * A / finrank ℚ K)), card_image_le.trans hbcard,
    fun x hx ↦ ?_, fun c hc𝒞 Q hQ hXQ ↦ ?_⟩
  · intro W hW
    obtain ⟨T, hT, rfl⟩ := mem_image.1 hW
    exact domainComap_ne_top K e (h𝒯top T hT)
  · obtain ⟨b', -, rfl⟩ := mem_image.1 hx
    exact le_max_left _ _
  obtain ⟨T, hT, -, hTcov⟩ := hcov _ ⟨c, hc𝒞, rfl⟩
  by_cases hsub : approxDomain Sfin L c Q ⊆ domainComap K e T
  · exact Or.inl ⟨_, mem_image_of_mem _ hT, hsub⟩
  exact Or.inr (exists_interval_of_not_subset_approxDomain K e hLInf hLFin hε (hc c hc𝒞) hεA hs
    hsR hX₀ hbge hTcov hQ hXQ hsub)

end Interval

/-! ### Sets of systems -/

section Systems

/-- `domainThreshold` is antitone in `A`. -/
theorem domainThreshold_anti {n d s : ℕ} {ε A A' F : ℝ} (hn : 0 < n) (hd : 0 < d) (hε : 0 < ε)
    (hA : 0 < A) (hAA : A ≤ A') (hF : 0 ≤ F) :
    domainThreshold n d s ε A' F ≤ domainThreshold n d s ε A F := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have key : ∀ B : ℝ, 0 < B → domainThreshold n d s ε B F =
      d * (Real.log n.factorial + n * F / d) / (2 * B) + 2 * d * n * Real.log n / ε +
        2 * d * ((s + n).choose n : ℝ) * (Real.log n.factorial + n * F / d) / ε := by
    intro B hB
    rw [domainThreshold, domainDelta]
    field_simp
    ring
  rw [key A' (hA.trans_le hAA), key A hA]
  have hℓ : 0 ≤ Real.log n.factorial + n * F / d := by
    have := Real.log_nonneg (Nat.one_le_cast.2 n.factorial_pos : (1 : ℝ) ≤ n.factorial)
    positivity
  gcongr

variable {E : Type} [NumberField K] [Field E] [NumberField E] [Algebra K E]

variable (E) in
open scoped Classical in
/-- **The number of places of the conjugated forms over `E`**: the infinite places of `E` and the
places of `E` above `S`. -/
noncomputable def efFamilyPlaces (S : Finset (HeightOneSpectrum (𝓞 K))) : ℕ :=
  Fintype.card (InfinitePlace E) + #(systemPlacesOver E S)

/-- **The number of forms** of the interval result for a set of systems: `r [E : K] + n + t`, the
`R' = r [E : K] + n` of `NumberField.efSystemDelta`'s count plus the `t` places, so that `t ≤ R'ⁿ`
as Theorem 2.3 for a set of exponents asks. -/
def efFamilyForms (r e n t : ℕ) : ℕ := r * e + n + t

/-- **The `δ` of Theorem 2.3 for a set of systems**, `δ / (16 n (n + 1) t)`: the `ε / 4nA` of
`NumberField.exists_forall_mem_interval_approxDomain_ef_family` at `ε = [E : K] δ / 2` and
`A = t · systemAbsBound`. -/
noncomputable def efFamilyDelta (n t : ℕ) (δ : ℝ) : ℝ := δ / (16 * n * (n + 1) * t)

theorem domainDelta_efEps_family {n e t : ℕ} (hn : 0 < n) (he : 0 < e) (ht : 0 < t) (δ : ℝ) :
    domainDelta n (efEps e δ) (t * systemAbsBound e n) = efFamilyDelta n t δ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  rw [domainDelta, efEps, systemAbsBound, efFamilyDelta]
  field_simp
  ring

open scoped Classical in
/-- **EF13's interval result for the conjugated forms of a system, for a set of exponents**: the
interval result of `NumberField.forall_interval_approxDomain_of_isNormalizedSystem_ef` for every set
`𝒞'` of exponents over `E` of weight `-[E : K] δ / 2` and absolute weight at most
`systemAbsBound [E : K] n`, with one set of at most `J = familyCount n t` proper subspaces of `Eⁿ`
and one set of at most `familyIntervalCount n t R' δ'` intervals `[s, ω₀ s)` for all of `𝒞'`;
here `t = efFamilyPlaces E S`, `R' = efFamilyForms R [E : K] n t`, `δ' = efFamilyDelta n t δ` and
`ω₀ = cutRatio R' δ'`. -/
theorem forall_interval_approxDomain_of_isNormalizedSystem_ef_family [IsGalois K E]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    ∀ 𝒞' : Set (AbsoluteValue E ℝ → ι → ℝ),
      (∀ c' ∈ 𝒞', approxWeight (systemPlacesOver E S) c' ≤ -systemEps (finrank K E) δ) →
      (∀ c' ∈ 𝒞', approxAbsWeight (systemPlacesOver E S) c' ≤
        systemAbsBound (finrank K E) (Fintype.card ι)) →
      (∀ c' ∈ 𝒞', approxWeight (systemPlacesOver E S) c' = -(finrank K E * δ / 2)) →
      (∀ c' ∈ 𝒞', approxSupWeight (systemPlacesOver E S) c' ≤
        finrank K E * (1 + δ / (2 * Fintype.card ι))) →
      ∃ T : Finset (Submodule E (ι → E)),
        #T ≤ FormSystem.familyCount (Fintype.card ι) (efFamilyPlaces E S) ∧ (∀ W ∈ T, W ≠ ⊤) ∧
        ∃ 𝒯 : Finset ℝ, #𝒯 ≤ FormSystem.familyIntervalCount (Fintype.card ι)
            (efFamilyPlaces E S) (efFamilyForms R (finrank K E) (Fintype.card ι)
              (efFamilyPlaces E S)) (efFamilyDelta (Fintype.card ι) (efFamilyPlaces E S) δ) ∧
          (∀ s ∈ 𝒯, efSystemThreshold E S w L R H δ ≤ s) ∧
          ∀ c' ∈ 𝒞', ∀ Q : ℝ, 1 < Q → efSystemThreshold E S w L R H δ ≤ Real.log Q →
            (∃ W ∈ T, approxDomain (systemPlacesOver E S)
              (conjSystem univ (S.image FinitePlace.mk) w L) c' Q ⊆ W) ∨
              ∃ s ∈ 𝒯, s ≤ Real.log Q ∧ Real.log Q <
                FormSystem.cutRatio (efFamilyForms R (finrank K E) (Fintype.card ι)
                  (efFamilyPlaces E S)) (efFamilyDelta (Fintype.card ι) (efFamilyPlaces E S) δ) *
                  s := by
  set n := Fintype.card ι with hn
  have hn2 : 2 ≤ n := hN.two_le_card
  have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have hδ := hN.delta_pos
  have hδ1 := hN.delta_le_one
  set e := finrank K E with he
  have he0 : 0 < e := finrank_pos
  set Sfin' := systemPlacesOver E S with hSfin'
  set L' := conjSystem univ (S.image FinitePlace.mk) w L with hL'
  set t := efFamilyPlaces E S with ht
  have ht1 : 1 ≤ t := by
    have := Fintype.card_pos (α := InfinitePlace E)
    rw [ht, efFamilyPlaces]
    omega
  set ε := efEps e δ with hε
  set A := (t : ℝ) * systemAbsBound e n with hA
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have he0' : (0 : ℝ) < e := by exact_mod_cast he0
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have ht1' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have hε0 : 0 < ε := by rw [hε, efEps]; positivity
  have hB : e ≤ systemAbsBound e n := by
    rw [systemAbsBound]
    nlinarith
  have hetA : (e : ℝ) ≤ A := by
    rw [hA]
    have : (0 : ℝ) ≤ systemAbsBound e n := he0'.le.trans hB
    nlinarith
  have hεA : ε ≤ 4 * n * A := by
    rw [hε, efEps]
    have h2 : (e : ℝ) * δ / 2 ≤ e := by nlinarith
    have hn1 : (1 : ℝ) ≤ 4 * n := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      linarith
    calc (e : ℝ) * δ / 2 ≤ A := h2.trans hetA
      _ ≤ 4 * n * A := le_mul_of_one_le_left (he0'.le.trans hetA) hn1
  have hspread : efSpread e n δ ≤ A := by
    rw [efSpread]
    have h1 : δ / n ≤ 1 := by
      rw [div_le_one hn0]
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      linarith
    have h2 : (e : ℝ) * (1 + δ / n) / 2 ≤ e := by nlinarith
    exact h2.trans hetA
  have hsE : formCount Sfin' L' ≤ R * e := formCount_conjSystem_le hwInf hwFin hN.ncard_le
  have hLI : ∀ v : InfinitePlace K, LinearIndependent E (L v.1) := fun v ↦
    hN.linearIndependent (.inl v)
  have hLF : ∀ p ∈ S, LinearIndependent E (L (FinitePlace.mk p).1) := fun p hp ↦
    hN.linearIndependent (.inr ⟨p, hp⟩)
  set X₀ := efSystemThreshold E S w L R H δ with hX₀
  have hX₀le : domainThreshold n (finrank ℚ E) (R * e) ε A (formLogHeight Sfin' L') ≤ X₀ :=
    (domainThreshold_anti (by omega) finrank_pos hε0 (by rw [efSpread]; positivity) hspread
      (formLogHeight_nonneg _ _)).trans (le_max_left _ _)
  have hδ' : domainDelta n ε A = efFamilyDelta n t δ :=
    domainDelta_efEps_family (by omega) he0 (by omega) δ
  intro 𝒞' _ hAbs hwe _
  have h := exists_forall_mem_interval_approxDomain_ef_family (K := E) (Sfin := Sfin') (L := L')
    (linearIndependent_conjSystem_infinitePlace hwInf hLI)
    (fun V hV ↦ linearIndependent_conjSystem_systemPlacesOver hwFin hLF hV) 𝒞' hε0
    (fun c' hc' ↦ by rw [hwe c' hc', hε, efEps]) hεA
    (fun c' hc' ↦ by
      have : ((Fintype.card (InfinitePlace E) : ℝ) + #Sfin') = t := by
        rw [ht, efFamilyPlaces]; push_cast; rfl
      rw [this, hA]
      exact mul_le_mul_of_nonneg_left (hAbs c' hc') ht0.le)
    hsE (R := efFamilyForms R e n t) (by rw [efFamilyForms]; omega)
    (by
      change t ≤ efFamilyForms R e n t ^ n
      refine le_trans ?_ (Nat.le_self_pow (by omega) _)
      rw [efFamilyForms]
      omega)
    hX₀le
  rwa [hδ'] at h

open scoped Classical in
/-- **The large solutions of a set of systems with the same forms lie in few subspaces or in few
height intervals, at Evertse–Ferretti strength.** Under the normalization (2.4), with forms over
a Galois extension `E / K`, let `𝒩` be a set of exponents of normalized systems with common forms,
constants and normalization. There are at most `familyCount n t` proper subspaces of `Kⁿ` and at
most `familyIntervalCount n t R' δ'` reals `s ≥ X₀ = efSystemThreshold` such that for every
`c ∈ 𝒩` every solution `x` with `log H(x) ≥ X₀` lies in one of the subspaces or has
`s ≤ log H(x) < ω₀ s` for one of the reals; here `t = efFamilyPlaces E S`,
`R' = efFamilyForms R [E : K] n t`, `δ' = efFamilyDelta n t δ` and `ω₀ = cutRatio R' δ'`. Neither
count depends on `𝒩`. -/
theorem exists_forall_mem_interval_of_efSystemThreshold_le_family [IsGalois K E]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ} {H : ℝ}
    {D R : ℕ} {δ : ℝ} (𝒩 : Set (InfinitePlace K ⊕ S → ι → ℝ))
    (hN : ∀ c ∈ 𝒩, IsNormalizedSystem S w L C c H D R δ) :
    ∃ T : Finset (Submodule K (ι → K)),
      #T ≤ FormSystem.familyCount (Fintype.card ι) (efFamilyPlaces E S) ∧ (∀ U ∈ T, U ≠ ⊤) ∧
      ∃ 𝒯 : Finset ℝ, #𝒯 ≤ FormSystem.familyIntervalCount (Fintype.card ι)
          (efFamilyPlaces E S) (efFamilyForms R (finrank K E) (Fintype.card ι)
            (efFamilyPlaces E S)) (efFamilyDelta (Fintype.card ι) (efFamilyPlaces E S) δ) ∧
        (∀ s ∈ 𝒯, efSystemThreshold E S w L R H δ ≤ s) ∧
        ∀ c ∈ 𝒩, ∀ x ∈ systemSet S w L C c,
          efSystemThreshold E S w L R H δ ≤ Real.log (mulHeightAff x) →
          (∃ U ∈ T, x ∈ U) ∨ ∃ s ∈ 𝒯, s ≤ Real.log (mulHeightAff x) ∧
            Real.log (mulHeightAff x) < FormSystem.cutRatio (efFamilyForms R (finrank K E)
              (Fintype.card ι) (efFamilyPlaces E S))
              (efFamilyDelta (Fintype.card ι) (efFamilyPlaces E S) δ) * s := by
  rcases 𝒩.eq_empty_or_nonempty with rfl | ⟨c₀, hc₀⟩
  · exact ⟨∅, by simp, by simp, ∅, by simp, by simp, by simp⟩
  exact exists_forall_mem_interval_systemSet_family S w hwInf hwFin 𝒩 hN
    ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))
    (forall_interval_approxDomain_of_isNormalizedSystem_ef_family S w hwInf hwFin (hN c₀ hc₀))

end Systems

end NumberField
