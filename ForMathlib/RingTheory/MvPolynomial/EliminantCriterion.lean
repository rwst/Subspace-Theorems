/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.PartialDegree
public import ForMathlib.RingTheory.MvPolynomial.Splitting

/-!
# When the eliminant ideal vanishes

G. Rémond's criterion for the vanishing of the eliminant ideal (*Élimination multihomogène*,
Chapter 5 of Nesterenko–Philippon (eds.), *Introduction to algebraic independence theory*,
LNM 1752 (2001), Theorem 2.13 (1)): for a multihomogeneous prime `𝔭` of `K[X]` and multidegrees
`d = (d_l)_{l ∈ κ}`, `𝔈_d(𝔭) = 0` if and only if `𝔪 ⊄ 𝔭` and `e_J(𝔭) ≥ r_J(d)` for every set `J` of
blocks, where `r_J(d)` (`MvPolynomial.numForms`) counts the `l` with `supp d_l ⊆ J`
(`MvPolynomial.elimIdeal_eq_bot_iff`).

Both directions are inductions on the number of forms (`Fintype.induction_empty_option`) through
the generic hypersurface section `𝔮 = 𝔄_{(d₀)}(𝔭) L[X]` of Lemma 2.12, with `𝔈_{d'}(𝔮) = 𝔈_d(𝔭)
L[d']` and `H_𝔮 = Δ_{d₀} H_𝔭`. Rémond's specializations and prime avoidance (which need `K`
infinite and the principal ideal theorem) are replaced by the partial degrees of the Hilbert
polynomial (`MvPolynomial.exists_coeff_hilbertPoly_ne_zero_blockRank`):

* the monomials of `Δ_e P = P(T) - P(T - e)` lie strictly below monomials of `P` and agree with
  them outside `supp e` (`MvPolynomial.exists_of_coeff_sub_shiftPoly_ne_zero`), so the partial
  degrees drop by one exactly for the `J ⊇ supp e`;
* a top monomial `T^α` of `H_𝔭` with `α_i > 0`, `e_i > 0` gives the monomial `T^{α - ε_i}` of
  `Δ_e H_𝔭`, by positivity of the top coefficients
  (`MvPolynomial.coeff_hilbertPoly_sub_shiftPoly_ne_zero`); so `𝔈_{(e)}(𝔭) = 0` as soon as
  `e_{supp e}(𝔭) ≥ 1`, since otherwise `𝔮 = L[X]` and `Δ_e H_𝔭 = 0`;
* in the remaining case Rémond's last assertion of Lemma 2.12 is
  `MvPolynomial.blockRank_add_blockRank_le`.

## Main statements

* `MvPolynomial.numForms`: `r_J(d)`.
* `MvPolynomial.exists_of_coeff_sub_shiftPoly_ne_zero`,
  `MvPolynomial.coeff_hilbertPoly_sub_shiftPoly_ne_zero`: monomials of `Δ_e P`.
* `MvPolynomial.numForms_add_card_le_blockRank`,
  `MvPolynomial.elimIdeal_eq_bot_of_numForms_add_card_le`, `MvPolynomial.elimIdeal_eq_bot_iff`:
  Theorem 2.13 (1).
-/

@[expose] public section

open Finset

namespace MvPolynomial

section Shift

variable {ι : Type*} [Fintype ι]

/-- The expansion `∏_i (X_i - c_i)^{α_i} = ∑_{p ≤ α} ∏_i C(α_i, p_i) (-c_i)^{α_i - p_i} X^p`. -/
theorem prod_X_sub_C_pow_eq_sum [DecidableEq ι] (c : ι → ℚ) (α : ι → ℕ) :
    (∏ i, (X i - C (c i)) ^ α i : MvPolynomial ι ℚ) =
      ∑ p ∈ Fintype.piFinset fun i ↦ range (α i + 1),
        monomial (∑ i, Finsupp.single i (p i))
          (∏ i, ((α i).choose (p i) : ℚ) * (-c i) ^ (α i - p i)) := by
  have h : ∀ i, (X i - C (c i)) ^ α i = ∑ m ∈ range (α i + 1),
      (monomial (Finsupp.single i m) (((α i).choose m : ℚ) * (-c i) ^ (α i - m)) :
        MvPolynomial ι ℚ) := by
    intro i
    rw [sub_eq_add_neg, add_pow]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [X_pow_eq_monomial, ← map_neg, ← map_pow, ← map_natCast (C : ℚ →+* MvPolynomial ι ℚ),
      mul_assoc, ← map_mul, mul_comm, C_mul_monomial, mul_one, mul_comm]
  rw [Finset.prod_congr rfl fun i _ ↦ h i, Finset.prod_univ_sum]
  exact Finset.sum_congr rfl fun p _ ↦ (monomial_sum_prod _ _ _).symm

theorem coeff_prod_X_sub_C_pow (c : ι → ℚ) (α : ι → ℕ) (β : ι →₀ ℕ) :
    (∏ i, (X i - C (c i)) ^ α i : MvPolynomial ι ℚ).coeff β =
      if ∀ i, β i ≤ α i then ∏ i, ((α i).choose (β i) : ℚ) * (-c i) ^ (α i - β i) else 0 := by
  classical
  have key : ∀ p : ι → ℕ, (∑ i, Finsupp.single i (p i) = β ↔ p = ⇑β) := by
    intro p
    constructor
    · rintro rfl
      funext j
      simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
    · rintro rfl
      ext j
      simp
  rw [prod_X_sub_C_pow_eq_sum, coeff_sum]
  simp only [coeff_monomial, key]
  rw [Finset.sum_ite_eq']
  congr 1
  simp

theorem le_of_coeff_prod_X_sub_C_pow_ne_zero {c : ι → ℚ} {α : ι → ℕ} {β : ι →₀ ℕ}
    (h : (∏ i, (X i - C (c i)) ^ α i : MvPolynomial ι ℚ).coeff β ≠ 0) :
    (∀ i, β i ≤ α i) ∧ ∀ i, c i = 0 → β i = α i := by
  rw [coeff_prod_X_sub_C_pow] at h
  split_ifs at h with hle
  · refine ⟨hle, fun i hi ↦ ?_⟩
    have := (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ i)
    rw [hi, neg_zero] at this
    have h0 : α i - β i = 0 := by
      by_contra h0
      exact this (by rw [zero_pow h0, mul_zero])
    have := hle i
    omega
  · exact absurd rfl h

theorem coeff_prod_X_sub_C_pow_self (c : ι → ℚ) (α : ι →₀ ℕ) :
    (∏ i, (X i - C (c i)) ^ α i : MvPolynomial ι ℚ).coeff α = 1 := by
  rw [coeff_prod_X_sub_C_pow]
  simp

theorem shiftPoly_eq_sum (e : ι → ℕ) (P : MvPolynomial ι ℚ) :
    shiftPoly e P = ∑ α ∈ P.support, C (P.coeff α) * ∏ i, (X i - C (e i : ℚ)) ^ α i := by
  conv_lhs => rw [P.as_sum]
  rw [shiftPoly, map_sum]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [aeval_monomial, Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _, algebraMap_eq]

/-- **The monomials of `P(T) - P(T - e)`** lie strictly below monomials of `P`, and agree with
them outside the support of `e`. -/
theorem exists_of_coeff_sub_shiftPoly_ne_zero {ι : Type*} [Finite ι] (e : ι → ℕ)
    (P : MvPolynomial ι ℚ) {β : ι →₀ ℕ}
    (h : (P - shiftPoly e P).coeff β ≠ 0) :
    ∃ α : ι →₀ ℕ, P.coeff α ≠ 0 ∧ β ≤ α ∧ β ≠ α ∧ ∀ i, e i = 0 → β i = α i := by
  classical
  have := Fintype.ofFinite ι
  have hsum : P - shiftPoly e P = ∑ α ∈ P.support,
      C (P.coeff α) * (monomial α 1 - ∏ i, (X i - C (e i : ℚ)) ^ α i) := by
    rw [shiftPoly_eq_sum]
    simp only [mul_sub, C_mul_monomial, mul_one, Finset.sum_sub_distrib]
    rw [← P.as_sum]
  rw [hsum, coeff_sum] at h
  obtain ⟨α, hα, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [coeff_C_mul, coeff_sub, coeff_monomial] at hne
  have hαP := mem_support_iff.mp hα
  by_cases hβα : β = α
  · subst hβα
    simp only [↓reduceIte, coeff_prod_X_sub_C_pow_self, sub_self, mul_zero] at hne
    exact absurd rfl hne
  simp only [Ne.symm hβα, ↓reduceIte, zero_sub] at hne
  have h2 : (∏ i, (X i - C (e i : ℚ)) ^ α i : MvPolynomial ι ℚ).coeff β ≠ 0 := fun h0 ↦
    hne (by rw [h0, neg_zero, mul_zero])
  obtain ⟨hle, heq⟩ := le_of_coeff_prod_X_sub_C_pow_ne_zero h2
  exact ⟨α, hαP, hle, hβα, fun i hi ↦ heq i (by exact_mod_cast hi)⟩

end Shift

section Count

variable {ι κ : Type*}

/-- `r_J(d)`: the number of forms whose multidegree `d l` is supported in the blocks `J`. -/
noncomputable def numForms (d : κ → ι → ℕ) (J : Set ι) : ℕ :=
  Nat.card {l : κ // ∀ i, d l i ≠ 0 → i ∈ J}

theorem numForms_comp_equiv {κ' : Type*} (f : κ' ≃ κ) (d : κ → ι → ℕ) (J : Set ι) :
    numForms (d ∘ f) J = numForms d J :=
  Nat.card_congr (f.subtypeEquiv fun _ ↦ Iff.rfl)

theorem numForms_of_isEmpty [IsEmpty κ] (d : κ → ι → ℕ) (J : Set ι) : numForms d J = 0 :=
  Nat.card_eq_zero.mpr (Or.inl ⟨fun x ↦ isEmptyElim x.1⟩)

theorem numForms_option [Finite κ] (d : Option κ → ι → ℕ) (J : Set ι) :
    numForms d J = numForms (fun l ↦ d (some l)) J + Set.indicator
      {_u : Unit | ∀ i, d none i ≠ 0 → i ∈ J} 1 () := by
  classical
  have := Fintype.ofFinite κ
  rw [numForms, numForms, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Fintype.card_subtype, Finset.card_filter, Finset.card_filter,
    Fintype.sum_option, add_comm, Set.indicator_apply]
  rfl

theorem numForms_option_of_subset [Finite κ] (d : Option κ → ι → ℕ) {J : Set ι}
    (h : ∀ i, d none i ≠ 0 → i ∈ J) :
    numForms d J = numForms (fun l ↦ d (some l)) J + 1 := by
  rw [numForms_option, Set.indicator_of_mem (by exact h)]
  rfl

theorem numForms_option_of_not_subset [Finite κ] (d : Option κ → ι → ℕ) {J : Set ι}
    (h : ¬∀ i, d none i ≠ 0 → i ∈ J) :
    numForms d J = numForms (fun l ↦ d (some l)) J := by
  rw [numForms_option, Set.indicator_of_notMem (by exact h), add_zero]

theorem numForms_mono [Finite κ] (d : κ → ι → ℕ) {J J₁ : Set ι} (h : J ⊆ J₁) :
    numForms d J ≤ numForms d J₁ :=
  Nat.card_le_card_of_injective (fun x ↦ ⟨x.1, fun i hi ↦ h (x.2 i hi)⟩)
    fun _ _ hxy ↦ Subtype.ext (by simpa using congrArg Subtype.val hxy)

/-- `J ↦ r_J(d)` is supermodular. -/
theorem numForms_add_numForms_le [Finite κ] (d : κ → ι → ℕ) (J J' : Set ι) :
    numForms d J + numForms d J' ≤ numForms d (J ∪ J') + numForms d (J ∩ J') := by
  classical
  have := Fintype.ofFinite κ
  set S : Set ι → Finset κ := fun J ↦ Finset.univ.filter fun l ↦ ∀ i, d l i ≠ 0 → i ∈ J
  have hS : ∀ J, numForms d J = (S J).card := fun J ↦ by
    rw [numForms, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hinter : S (J ∩ J') = S J ∩ S J' := by
    ext l
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
      Set.mem_inter_iff]
    exact ⟨fun h ↦ ⟨fun i hi ↦ (h i hi).1, fun i hi ↦ (h i hi).2⟩,
      fun h i hi ↦ ⟨h.1 i hi, h.2 i hi⟩⟩
  have hunion : S J ∪ S J' ⊆ S (J ∪ J') := by
    intro l
    simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_union]
    rintro (h | h) i hi
    exacts [Or.inl (h i hi), Or.inr (h i hi)]
  rw [hS, hS, hS, hS, hinter, ← Finset.card_union_add_card_inter]
  exact Nat.add_le_add_right (Finset.card_le_card hunion) _

end Count

section Positivity

variable {σ ι K : Type*} [Finite σ] [Finite ι] [DecidableEq ι] {b : σ → ι} [Field K]

/-- **`Δ_e H_I` keeps the top monomials with a variable in `supp e`**: if `T^α` is a monomial of
top degree of `H_I` with `α_i > 0` and `e_i > 0`, then `T^{α - ε_i}` is a monomial of
`H_I(T) - H_I(T - e)`; all contributions to its coefficient are nonnegative. -/
theorem coeff_hilbertPoly_sub_shiftPoly_ne_zero (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    {α : ι →₀ ℕ} (hα : (hilbertPoly b I).coeff α ≠ 0)
    (hdeg : α.degree = (hilbertPoly b I).totalDegree) {e : ι → ℕ} {i : ι} (hei : e i ≠ 0)
    (hαi : α i ≠ 0) :
    (hilbertPoly b I - shiftPoly e (hilbertPoly b I)).coeff (α - Finsupp.single i 1) ≠ 0 := by
  have := Fintype.ofFinite ι
  set H := hilbertPoly b I
  set β := α - Finsupp.single i 1
  have hle : Finsupp.single i 1 ≤ α := fun j ↦ by
    rw [Finsupp.single_apply]
    split_ifs with h
    · subst h
      omega
    · exact Nat.zero_le _
  have hβα : β + Finsupp.single i 1 = α := tsub_add_cancel_of_le hle
  have hβdeg : β.degree + 1 = α.degree := by
    rw [← hβα, map_add, Finsupp.degree_single]
  have hβ : H.totalDegree - 1 ≤ β.degree := by omega
  rw [coeff_sub_shiftPoly e H hβ]
  refine ne_of_gt (Finset.sum_pos' (fun j _ ↦ ?_) ⟨i, Finset.mem_univ i, ?_⟩)
  · have hj : H.totalDegree ≤ (β + Finsupp.single j 1).degree := by
      rw [map_add, Finsupp.degree_single]
      omega
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (coeff_hilbertPoly_nonneg hb hI hj)
      (by positivity))
  · rw [hβα]
    have hpos : 0 < H.coeff α :=
      lt_of_le_of_ne (coeff_hilbertPoly_nonneg hb hI hdeg.ge) (Ne.symm hα)
    exact mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hei)) (mul_pos hpos (by positivity))

end Positivity

section Helpers

variable {σ ι K : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι} [Field K]

omit [Fintype σ] [Fintype ι] [DecidableEq ι] in
theorem sum_tsub_single_add {ι : Type*} [DecidableEq ι] (α : ι →₀ ℕ) {i : ι} (hi : α i ≠ 0)
    (J : Finset ι) :
    ∑ j ∈ J, (α - Finsupp.single i 1 : ι →₀ ℕ) j + (if i ∈ J then 1 else 0) =
      ∑ j ∈ J, α j := by
  have hle : Finsupp.single i 1 ≤ α := fun j ↦ by
    rw [Finsupp.single_apply]
    split_ifs with h
    · subst h
      omega
    · exact Nat.zero_le _
  conv_rhs => rw [← tsub_add_cancel_of_le hle]
  simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, Finsupp.single_apply,
    Finset.sum_ite_eq]

/-- A multihomogeneous prime with `H_𝔭 ≠ 0` does not contain the irrelevant ideal. -/
theorem not_le_of_hilbertPoly_ne_zero (hb : Function.Surjective b)
    {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime] (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b))
    (hne : hilbertPoly b 𝔭 ≠ 0) : ¬irrelevantIdeal K b ≤ 𝔭 := by
  choose t ht hX using exists_X_notMem_of_hilbertPoly_ne_zero hb h𝔭 hne
  intro hle
  have hmem := hle (monomial_mem_irrelevantIdeal (S := K)
    (mem_blockMonomials.mpr (weight_sum_single_one ht)))
  have hprod : (monomial (∑ i, Finsupp.single (t i) 1) 1 : MvPolynomial σ K) =
      ∏ i, X (t i) := by
    simpa using monomial_sum_single_eq_prod (S := K) t fun _ ↦ 1
  rw [hprod] at hmem
  obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
  exact hX i hi

/-- `𝔈_d(𝔭) = 0` for no forms at all, when `𝔪 ⊄ 𝔭`. -/
theorem elimIdeal_eq_bot_of_isEmpty {κ : Type*} [IsEmpty κ] (d : κ → ι → ℕ)
    {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime] (hm : ¬irrelevantIdeal K b ≤ 𝔭) :
    elimIdeal K b d 𝔭 = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Ideal.mem_bot]
  by_contra hc0
  have hC : c = C (c.coeff 0) := eq_C_of_isEmpty c
  have h0 : c.coeff 0 ≠ 0 := fun h ↦ hc0 (by rw [hC, h, map_zero])
  have hc' : (C c : MvPolynomial σ (MvPolynomial (GenericVar b d) K)) ∈ charIdeal K b d 𝔭 := hc
  have htop : charIdeal K b d 𝔭 = ⊤ := Ideal.eq_top_of_isUnit_mem _ hc'
    (by rw [hC]; exact ((isUnit_iff_ne_zero.mpr h0).map C).map C)
  have := comap_map_C_charIdeal (d := d) hm
  rw [htop, Ideal.comap_top] at this
  exact Ideal.IsPrime.ne_top inferInstance this.symm

/-- If `𝔈_d(𝔭) ≠ 0`, the extension of `𝔄_d(𝔭)` to `L[X]` is the whole ring. -/
theorem map_charIdeal_eq_top {κ : Type*} {d : κ → ι → ℕ} {𝔭 : Ideal (MvPolynomial σ K)}
    (h : elimIdeal K b d 𝔭 ≠ ⊥) :
    (charIdeal K b d 𝔭).map (map (algebraMap (MvPolynomial (GenericVar b d) K)
      (FractionRing (MvPolynomial (GenericVar b d) K)))) = ⊤ := by
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (show C c ∈ charIdeal K b d 𝔭
    from hc)) ?_
  rw [map_C]
  exact (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _
    (IsFractionRing.injective _ (FractionRing (MvPolynomial (GenericVar b d) K)))).mpr hc0)).map C

omit [Fintype σ] [Fintype ι] in
theorem hilbertPoly_top' [Finite σ] [Finite ι] (hb : Function.Surjective b) :
    hilbertPoly b (⊤ : Ideal (MvPolynomial σ K)) = 0 := by
  classical
  refine hilbertPoly_eq_of_forall_le hb (isWeightedHomogeneous_top _) (d₀ := 0) fun d _ ↦ ?_
  rw [hilbertFunction, Submodule.restrictScalars_top, top_inf_eq, Nat.sub_self]
  simp

end Helpers

section Criterion

universe u

variable {σ ι : Type u} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}

/-- **Rémond's Thm 2.13 (1), direct sense**: if `𝔈_d(𝔭) = 0`, then for every set `J` of blocks
`e_J(𝔭) ≥ r_J(d)`, where `r_J(d)` counts the forms supported in `J`; in terms of ranks,
`r_J(d) + |J| ≤ blockRank 𝔭 b J`. By induction on the number of forms, through the generic
hypersurface section `𝔮 = 𝔄_{(d₀)}(𝔭) L[X]` (Lemma 2.12): `𝔈_{d'}(𝔮) = 0`, and the partial
degrees of `H_𝔮 = Δ_{d₀} H_𝔭` drop by one exactly in the `J ⊇ supp d₀`. -/
theorem numForms_add_card_le_blockRank (hb : Function.Surjective b) (κ : Type u) [Finite κ] :
    ∀ (K : Type u) [Field K] (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime],
      𝔭.IsWeightedHomogeneous (multiWeight b) → ∀ d : κ → ι → ℕ, elimIdeal K b d 𝔭 = ⊥ →
        ∀ J : Finset ι, numForms d J + #J ≤ blockRank 𝔭 b J := by
  have := Fintype.ofFinite κ
  refine Fintype.induction_empty_option (P := fun κ _ ↦ ∀ (K : Type u) [Field K]
    (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime], 𝔭.IsWeightedHomogeneous (multiWeight b) →
      ∀ d : κ → ι → ℕ, elimIdeal K b d 𝔭 = ⊥ →
        ∀ J : Finset ι, numForms d J + #J ≤ blockRank 𝔭 b J) ?_ ?_ ?_ κ
  · intro α β _ e IH K _ 𝔭 _ h𝔭 d hd J
    have := IH K 𝔭 h𝔭 (d ∘ e) ((elimIdeal_comp_eq_bot_iff e d 𝔭).mpr hd) J
    rwa [numForms_comp_equiv] at this
  · intro K _ 𝔭 _ h𝔭 d hd J
    rw [numForms_of_isEmpty, zero_add]
    exact card_le_blockRank hb h𝔭
      (hilbertPoly_ne_zero_of_not_le hb h𝔭 (not_le_of_elimIdeal_eq_bot hd)) J
  · intro α _ IH K _ 𝔭 _ h𝔭 d hd J
    set e := d none
    have h1 : elimIdeal K b (fun _ : Unit ↦ e) 𝔭 = ⊥ := elimIdeal_none_eq_bot d hd
    have hm := not_le_of_elimIdeal_eq_bot h1
    set L := FractionRing (GenericRing K b e)
    set q := (charIdeal K b (fun _ : Unit ↦ e) 𝔭).map (map (algebraMap (GenericRing K b e) L))
    have : q.IsPrime := isPrime_map_charIdeal h1
    have hqh : q.IsWeightedHomogeneous (multiWeight b) := isWeightedHomogeneous_map_charIdeal h𝔭
    have hqd : elimIdeal L b (fun l : α ↦ d (some l)) q = ⊥ := by
      rw [elimIdeal_map_charIdeal, hd, Ideal.map_bot, Ideal.map_bot]
    have IHq := IH L q hqh _ hqd J
    have hqne : hilbertPoly b q ≠ 0 :=
      hilbertPoly_ne_zero_of_not_le hb hqh (not_le_of_elimIdeal_eq_bot hqd)
    obtain ⟨β, hβ, -, hβJ, -⟩ :=
      exists_coeff_hilbertPoly_ne_zero_blockRank hb hqh hqne (subset_refl J)
    rw [hilbertPoly_map_charIdeal hb h𝔭 hm e] at hβ
    obtain ⟨γ, hγ, hβγ, hne, hagree⟩ := exists_of_coeff_sub_shiftPoly_ne_zero e _ hβ
    have hγJ := sum_add_card_le_blockRank hb h𝔭 hγ J
    have hsum : ∑ i ∈ J, β i ≤ ∑ i ∈ J, γ i := Finset.sum_le_sum fun i _ ↦ hβγ i
    by_cases hS : ∀ i, e i ≠ 0 → i ∈ (J : Set ι)
    · rw [numForms_option_of_subset d hS]
      have hlt : ∑ i ∈ J, β i < ∑ i ∈ J, γ i := by
        obtain ⟨i, hi⟩ : ∃ i, β i ≠ γ i := by
          by_contra h
          push Not at h
          exact hne (Finsupp.ext h)
        have hei : e i ≠ 0 := fun h0 ↦ hi (hagree i h0)
        exact Finset.sum_lt_sum (fun j _ ↦ hβγ j) ⟨i, hS i hei, lt_of_le_of_ne (hβγ i) hi⟩
      omega
    · rw [numForms_option_of_not_subset d hS]
      omega

/-- **Rémond's Thm 2.13 (1), converse**: if `𝔪 ⊄ 𝔭` and `e_J(𝔭) ≥ r_J(d)` for every set `J` of
blocks, then `𝔈_d(𝔭) = 0`. By induction on the number of forms through Lemma 2.12; the case
`supp d₀ ⊄ J` with `e_{J ∪ supp d₀}(𝔭) = e_J(𝔭)` uses the transfer of ranks along
`𝔮 ∩ K[X] = 𝔭` (`MvPolynomial.blockRank_add_blockRank_le`). -/
theorem elimIdeal_eq_bot_of_numForms_add_card_le (hb : Function.Surjective b) (κ : Type u)
    [Finite κ] : ∀ (K : Type u) [Field K] (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime],
      𝔭.IsWeightedHomogeneous (multiWeight b) → ¬irrelevantIdeal K b ≤ 𝔭 →
        ∀ d : κ → ι → ℕ, (∀ J : Finset ι, numForms d J + #J ≤ blockRank 𝔭 b J) →
          elimIdeal K b d 𝔭 = ⊥ := by
  have := Fintype.ofFinite κ
  refine Fintype.induction_empty_option (P := fun κ _ ↦ ∀ (K : Type u) [Field K]
    (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime], 𝔭.IsWeightedHomogeneous (multiWeight b) →
      ¬irrelevantIdeal K b ≤ 𝔭 → ∀ d : κ → ι → ℕ,
        (∀ J : Finset ι, numForms d J + #J ≤ blockRank 𝔭 b J) → elimIdeal K b d 𝔭 = ⊥)
    ?_ ?_ ?_ κ
  · intro α β _ e IH K _ 𝔭 _ h𝔭 hm d hd
    refine (elimIdeal_comp_eq_bot_iff e d 𝔭).mp (IH K 𝔭 h𝔭 hm (d ∘ e) fun J ↦ ?_)
    rw [numForms_comp_equiv]
    exact hd J
  · intro K _ 𝔭 _ h𝔭 hm d _
    exact elimIdeal_eq_bot_of_isEmpty d hm
  · intro α _ IH K _ 𝔭 _ h𝔭 hm d hd
    set e := d none
    set S : Finset ι := Finset.univ.filter fun i ↦ e i ≠ 0
    have hS : ∀ i, e i ≠ 0 → i ∈ (S : Set ι) := fun i hi ↦ by simp [S, hi]
    have hH𝔭 := hilbertPoly_ne_zero_of_not_le hb h𝔭 hm
    -- A top monomial of `H_𝔭` with a variable in `supp e`, for each `J ⊇ supp e`.
    have hpos : ∀ J : Finset ι, S ⊆ J → ∃ α' : ι →₀ ℕ, (hilbertPoly b 𝔭).coeff α' ≠ 0 ∧
        α'.degree = (hilbertPoly b 𝔭).totalDegree ∧ ∑ i ∈ J, α' i + #J = blockRank 𝔭 b J ∧
          ∃ i ∈ S, α' i ≠ 0 := by
      intro J hSJ
      obtain ⟨α', hα', hdeg, hS', hJ'⟩ :=
        exists_coeff_hilbertPoly_ne_zero_blockRank hb h𝔭 hH𝔭 hSJ
      refine ⟨α', hα', hdeg, hJ', ?_⟩
      have h1 := hd S
      rw [numForms_option_of_subset d hS] at h1
      have h2 : ∑ i ∈ S, α' i ≠ 0 := by omega
      obtain ⟨i, hi, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
      exact ⟨i, hi, hi0⟩
    have hei : ∀ i ∈ S, e i ≠ 0 := fun i hi ↦ (Finset.mem_filter.mp hi).2
    -- Step 1: `𝔈_{(e)}(𝔭) = 0`.
    have h1 : elimIdeal K b (fun _ : Unit ↦ e) 𝔭 = ⊥ := by
      by_contra hne
      have htop := map_charIdeal_eq_top hne
      have hH := hilbertPoly_map_charIdeal hb h𝔭 hm e
      rw [htop, hilbertPoly_top' hb] at hH
      obtain ⟨α', hα', hdeg, -, i, hi, hi0⟩ := hpos S subset_rfl
      exact coeff_hilbertPoly_sub_shiftPoly_ne_zero hb h𝔭 hα' hdeg (hei i hi) hi0
        (by simp [← hH])
    set L := FractionRing (GenericRing K b e)
    set q := (charIdeal K b (fun _ : Unit ↦ e) 𝔭).map (map (algebraMap (GenericRing K b e) L))
    have : q.IsPrime := isPrime_map_charIdeal h1
    have hqh : q.IsWeightedHomogeneous (multiWeight b) := isWeightedHomogeneous_map_charIdeal h𝔭
    have hHq : hilbertPoly b q = hilbertPoly b 𝔭 - shiftPoly e (hilbertPoly b 𝔭) :=
      hilbertPoly_map_charIdeal hb h𝔭 hm e
    have hcomap : q.comap (map (algebraMap K L)) = 𝔭 := comap_map_charIdeal h1
    -- The first case: `supp e ⊆ J`.
    have hcase1 : ∀ J : Finset ι, S ⊆ J → blockRank 𝔭 b J ≤ blockRank q b J + 1 := by
      intro J hSJ
      obtain ⟨α', hα', hdeg, hJ', i, hi, hi0⟩ := hpos J hSJ
      have hβ := coeff_hilbertPoly_sub_shiftPoly_ne_zero hb h𝔭 hα' hdeg (hei i hi) hi0
      rw [← hHq] at hβ
      have h2 := sum_add_card_le_blockRank hb hqh hβ J
      have h3 := sum_tsub_single_add α' hi0 J
      simp only [hSJ hi, ↓reduceIte] at h3
      omega
    have hqne : hilbertPoly b q ≠ 0 := by
      obtain ⟨α', hα', hdeg, -, i, hi, hi0⟩ := hpos S subset_rfl
      intro h0
      have hβ := coeff_hilbertPoly_sub_shiftPoly_ne_zero hb h𝔭 hα' hdeg (hei i hi) hi0
      rw [← hHq, h0] at hβ
      exact hβ (by simp)
    have hqm : ¬irrelevantIdeal L b ≤ q := not_le_of_hilbertPoly_ne_zero hb hqh hqne
    -- Step 2: the conditions for `𝔮` and `d'`.
    have hqd : ∀ J : Finset ι, numForms (fun l : α ↦ d (some l)) J + #J ≤ blockRank q b J := by
      intro J
      by_cases hSJ : S ⊆ J
      · have h1 := hd J
        rw [numForms_option_of_subset d fun i hi ↦ hSJ (hS i hi)] at h1
        have := hcase1 J hSJ
        omega
      · have hnot : ¬∀ i, e i ≠ 0 → i ∈ (J : Set ι) := fun h ↦ hSJ fun i hi ↦
          h i (hei i hi)
        rw [← numForms_option_of_not_subset d hnot]
        obtain ⟨J₁, hJ₁⟩ : ∃ J₁, J₁ = J ∪ S := ⟨_, rfl⟩
        have hJJ₁ : J ⊆ J₁ := hJ₁ ▸ Finset.subset_union_left
        have hSJ₁ : S ⊆ J₁ := hJ₁ ▸ Finset.subset_union_right
        obtain ⟨α', hα', hdeg, hJ', hJ₁'⟩ :=
          exists_coeff_hilbertPoly_ne_zero_blockRank hb h𝔭 hH𝔭 hJJ₁
        by_cases hex : ∃ i ∈ S, i ∉ J ∧ α' i ≠ 0
        · obtain ⟨i, hi, hiJ, hi0⟩ := hex
          have hβ := coeff_hilbertPoly_sub_shiftPoly_ne_zero hb h𝔭 hα' hdeg (hei i hi) hi0
          rw [← hHq] at hβ
          have h2 := sum_add_card_le_blockRank hb hqh hβ J
          have h3 := sum_tsub_single_add α' hi0 J
          simp only [hiJ, ↓reduceIte, add_zero] at h3
          have := hd J
          omega
        · push Not at hex
          have hsum : ∑ i ∈ J₁, α' i = ∑ i ∈ J, α' i := by
            refine (Finset.sum_subset hJJ₁ fun i hi hiJ ↦ ?_).symm
            have hiS : i ∈ S := by
              rcases Finset.mem_union.mp (hJ₁ ▸ hi) with h | h
              · exact absurd h hiJ
              · exact h
            exact hex i hiS hiJ
          have htr := blockRank_add_blockRank_le (algebraMap K L) hcomap b
            (Finset.coe_subset.mpr hJJ₁)
          have hc1 := hcase1 J₁ hSJ₁
          have hdJ₁ := hd J₁
          rw [numForms_option_of_subset d fun i hi ↦ hSJ₁ (hS i hi)] at hdJ₁
          have hmono := numForms_mono (fun l : α ↦ d (some l))
            (Finset.coe_subset.mpr hJJ₁)
          have hcard := Finset.card_le_card hJJ₁
          rw [numForms_option_of_not_subset d hnot]
          omega
    have hqd' := IH L q hqh hqm _ hqd
    rw [elimIdeal_map_charIdeal] at hqd'
    have hinj : Function.Injective (map (algebraMap (GenericRing K b e) L) :
        MvPolynomial (GenericVar b fun l : α ↦ d (some l)) (GenericRing K b e) →+* _) :=
      map_injective _ (IsFractionRing.injective _ _)
    rw [Ideal.map_eq_bot_iff_of_injective hinj,
      Ideal.map_eq_bot_iff_of_injective (f := (splitEquiv b K d).toRingHom)
        (splitEquiv b K d).injective] at hqd'
    exact hqd'

/-- **Rémond's Theorem 2.13 (1)** (LNM 1752, Ch. 5): for a multihomogeneous prime `𝔭` over any
field, `𝔈_d(𝔭) = 0` if and only if `𝔪 ⊄ 𝔭` and `e_J(𝔭) ≥ r_J(d)` for every set of blocks `J`,
i.e. `ht 𝔭_J ≤ n_J - r_J(d)`. Here `e_J(𝔭) = blockRank 𝔭 b J - |J|` and `r_J(d)` is the number of
forms whose multidegree is supported in `J`. -/
theorem elimIdeal_eq_bot_iff (hb : Function.Surjective b) {κ : Type u} [Finite κ] {K : Type u}
    [Field K] {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime]
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (d : κ → ι → ℕ) :
    elimIdeal K b d 𝔭 = ⊥ ↔ ¬irrelevantIdeal K b ≤ 𝔭 ∧
      ∀ J : Finset ι, numForms d J + #J ≤ blockRank 𝔭 b J :=
  ⟨fun h ↦ ⟨not_le_of_elimIdeal_eq_bot h, numForms_add_card_le_blockRank hb κ K 𝔭 h𝔭 d h⟩,
    fun ⟨hm, h⟩ ↦ elimIdeal_eq_bot_of_numForms_add_card_le hb κ K 𝔭 h𝔭 hm d h⟩

end Criterion

end MvPolynomial

end
