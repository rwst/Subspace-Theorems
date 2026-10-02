/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.NumberTheory.Height.PointHeight
public import ForMathlib.NumberTheory.Height.SectionHeight
public import ForMathlib.NumberTheory.Height.SpaceHeight
public import QuantitativeSubspace.MultiprojectiveHeight

/-!
# Heights of resultant forms satisfy the interface

The heights `h_β(𝔮)` of LNM 1752, Ch. 7, §2.3, with the Gaussian Mahler measure at the
archimedean places (`MvPolynomial.gaussHeight`): `h_β(𝔮)` is the height of `α res(𝔮)`, the
resultant form of `𝔮` in `|β|` generic linear forms, `β_i` of them in the block `i`
(`MvPolynomial.resHeight`). They form a `MvPolynomial.MultiprojectiveHeight`
(`MvPolynomial.resultantHeight`) over every field whose archimedean absolute values come from
complex embeddings, e.g. number fields (`MvPolynomial.archEmbedded_of_numberField`):

* nonnegativity is the product formula and `|f_m| ≤ M(f)` (`MvPolynomial.gaussHeight_nonneg`);
* `h(ℙ) ≤ [K : ℚ] log M(det_{n_l + 1})` (`MvPolynomial.gaussHeight_resForm_bot_le`), so
  `botBound n = log M(det_{n + 1}) ≤ (n + 1)(log (2(n + 1)) / 2 + 2)`
  (`MvPolynomial.resultantHeight_botBound_le`);
* the intersection inequality is `MvPolynomial.gaussHeight_resForm_sup_le` (Rémond's Thm 3.4 with
  Cor. 3.6, via Thm 2.2), split over the components by Thm 3.3
  (`MvPolynomial.resHeight_eq_cycleHeight`). The degree in the first form is the multidegree
  (`MvPolynomial.exists_isWeightedHomogeneous_resForm_leftIndex_linIndex`);
* the point bound is `MvPolynomial.logHeight_mul_le_gaussHeight_resForm`, transported to the
  heights `h_β` by the same reindexing (`MvPolynomial.logHeight_mul_le_cycleHeight`).
-/

@[expose] public section

open Finset Height Height.AdmissibleAbsValues

namespace MvPolynomial

variable {σ ι K : Type} [Fintype σ] [Fintype ι] [DecidableEq ι] [Field K]

/-- The `|β|` generic linear forms of the heights of index `β`: `β_i` forms in the block `i`. -/
abbrev LinForms (β : ι →₀ ℕ) : Type := Σ i, Fin (β i)

omit [DecidableEq ι] in
theorem formCount_linForms (β : ι →₀ ℕ) :
    formCount (Sigma.fst : LinForms β → ι) univ = β := by
  ext i
  classical
  simp [formCount, Fintype.sum_sigma]

omit [DecidableEq ι] in
theorem card_linForms (β : ι →₀ ℕ) : Fintype.card (LinForms β) = β.degree := by
  rw [Fintype.card_sigma, Finsupp.degree_eq_sum]
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem formCount_option {κ : Type*} [Fintype κ] (τ : κ → ι) (i : ι) :
    formCount (fun y : Option κ ↦ y.elim i τ) univ = formCount τ univ + Finsupp.single i 1 := by
  simp [formCount, Fintype.sum_option, add_comm]

omit [Fintype σ] [Fintype ι] in
theorem leftIndex_single_linIndex {κ : Type*} (τ : κ → ι) (i : ι) :
    leftIndex (Pi.single i 1) (linIndex τ) = linIndex fun y : Option κ ↦ y.elim i τ := by
  funext y
  cases y <;> rfl

variable [AdmissibleAbsValues K]

variable (b : σ → ι) in
/-- **The height `h_β(𝔮)`** of LNM 1752, Ch. 7, §2.3: the height of `α res(𝔮)`, the resultant form
of `𝔮` in `|β|` generic linear forms, `β_i` of them in the block `i`. -/
noncomputable def resHeight (𝔮 : Ideal (MvPolynomial σ K)) (β : ι →₀ ℕ) : ℝ :=
  gaussHeight remodelWeight (resForm b K (linIndex (Sigma.fst : LinForms β → ι)) 𝔮)

variable {b : σ → ι}

/-- **The height of a cycle is that of its resultant form** (Rémond's Thm 3.3): for
`dim V(J) < |β|`, `h(α res_β(J)) = ∑_𝔮 ℓ_𝔮(J) h_β(𝔮)` over the components of dimension
`|β| - 1`. -/
theorem resHeight_eq_cycleHeight (hK : ArchEmbedded K) (hb : Function.Surjective b)
    {J : Ideal (MvPolynomial σ K)} (hJ : J.IsWeightedHomogeneous (multiWeight b)) {β : ι →₀ ℕ}
    (hdim : (hilbertPoly b J).totalDegree + 1 ≤ β.degree) :
    resHeight b J β = cycleHeight b (resHeight b) J β := by
  have hcard : Nat.card (LinForms β) = β.degree := by
    rw [Nat.card_eq_fintype_card, card_linForms]
  obtain ⟨S, ℓ, hS, hℓ, hsum⟩ := exists_gaussHeight_resForm_eq_sum hK
    (linIndex (Sigma.fst : LinForms β → ι)) hb hJ (hcard ▸ hdim)
  rw [hcard] at hS
  have hSc : S = components b J (β.degree - 1) := by
    ext 𝔭
    rw [hS, mem_components]
    constructor
    · rintro ⟨h𝔭p, h𝔭h, hJ𝔭, hm, hdeg⟩
      have hne := hilbertPoly_ne_zero_of_not_le hb h𝔭h hm
      refine ⟨⟨⟨h𝔭p, hJ𝔭⟩, fun 𝔮 h𝔮 h𝔮𝔭 ↦ ?_⟩, hne, by omega⟩
      have := h𝔮.1
      obtain ⟨𝔮', h𝔮', h𝔮'𝔮⟩ := Ideal.exists_minimalPrimes_le h𝔮.2
      have := h𝔮'.1.1
      have h𝔮'h := hJ.of_mem_minimalPrimes h𝔮'
      by_cases heq : 𝔮' = 𝔭
      · exact heq ▸ h𝔮'𝔮
      have hlt : 𝔮' < 𝔭 := lt_of_le_of_ne (h𝔮'𝔮.trans h𝔮𝔭) heq
      have h1 := totalDegree_hilbertPoly_lt_of_lt hb h𝔮'h h𝔭h hlt hne
      have h2 := totalDegree_hilbertPoly_le_of_le hb hJ h𝔮'h h𝔮'.1.2
      omega
    · rintro ⟨h𝔭J, hne, hdeg⟩
      have := h𝔭J.1.1
      have h𝔭h := hJ.of_mem_minimalPrimes h𝔭J
      exact ⟨this, h𝔭h, h𝔭J.1.2, fun hm ↦ hne (hilbertPoly_eq_zero_of_le hb h𝔭h hm),
        by omega⟩
  rw [resHeight, hsum, cycleHeight, ← hSc]
  refine sum_congr rfl fun 𝔭 h𝔭 ↦ ?_
  have : 𝔭.IsPrime := ((hS 𝔭).1 h𝔭).1
  rw [primeMult_eq, hℓ 𝔭 h𝔭, ENat.toNat_natCast, resHeight]

omit [DecidableEq ι] [AdmissibleAbsValues K] in
theorem bombieriNorm_C [DecidableEq ι] (b : σ → ι) (v : AbsoluteValue K ℝ) {c : K} (hc : c ≠ 0) :
    bombieriNorm b v (C c : MvPolynomial σ K) = v c := by
  classical
  simp only [bombieriNorm, support_C, hc, ↓reduceIte, sum_singleton, coeff_zero_C]
  simp [blockMultinomial, Nat.multinomial, Real.sqrt_sq (v.nonneg c)]

/-- The polynomial height of a nonzero constant is `0` (the product formula). -/
theorem bombieriLogHeight_C (b : σ → ι) {c : K} (hc : c ≠ 0) :
    bombieriLogHeight b (C c : MvPolynomial σ K) = 0 := by
  have h : ∀ v : nonarchAbsVal (K := K), (⨆ m : (C c : MvPolynomial σ K).support,
      v.val ((C c : MvPolynomial σ K).coeff m)) = v.val c := fun v ↦ maxNorm_C (v := v.val) c
  rw [bombieriLogHeight_of_ne_zero b (C_ne_zero.2 hc),
    Multiset.map_congr rfl fun v _ ↦ bombieriNorm_C b v hc, finprod_congr h,
    product_formula hc, Real.log_one]

omit [Fintype σ] [Fintype ι] [AdmissibleAbsValues K] in
/-- A form of multidegree `0` is a constant. -/
theorem eq_C_of_isWeightedHomogeneous_zero {p : MvPolynomial σ K}
    (hp : IsWeightedHomogeneous (multiWeight b) p 0) : p = C (p.coeff 0) := by
  have hw : ∀ s, multiWeight b s ≠ 0 := fun s h ↦ by
    simpa [multiWeight] using congrFun h (b s)
  calc p = weightedHomogeneousComponent (multiWeight b) 0 p :=
        hp.weightedHomogeneousComponent_same.symm
    _ = C (p.coeff 0) := weightedHomogeneousComponent_zero p hw

/-- **The arithmetic intersection inequality for the heights `h_β`** (Rémond, LNM 1752, Ch. 7,
Thm 3.4 with Cor. 3.6): for a form `p` of multidegree `δ`, not a zero divisor modulo `J`, and
`|β| = dim V(J) ≥ 1`, `h_β(V(J) · div p) ≤ ∑_i δ_i h_{β + ε_i}(V(J)) + d_β(J) h_m(p)`. -/
theorem cycleHeight_resHeight_sup_le (hK : ArchEmbedded K) (hb : Function.Surjective b)
    {J : Ideal (MvPolynomial σ K)} (p : MvPolynomial σ K) (δ : ι → ℕ)
    (hJ : J.IsWeightedHomogeneous (multiWeight b)) (hp : IsWeightedHomogeneous (multiWeight b) p δ)
    (hcol : J.colon {p} = J) (β : ι →₀ ℕ) (h1 : 1 ≤ β.degree)
    (hβ : β.degree = (hilbertPoly b J).totalDegree) :
    cycleHeight b (resHeight b) (J ⊔ Ideal.span {p}) β ≤
      ∑ i, (δ i : ℝ) * cycleHeight b (resHeight b) J (β + Finsupp.single i 1) +
        (multidegree b J β : ℝ) * bombieriLogHeight b p := by
  have hnn : ∀ γ, 0 ≤ cycleHeight b (resHeight b) J γ := fun γ ↦
    sum_nonneg fun 𝔮 _ ↦ mul_nonneg (Nat.cast_nonneg _) (gaussHeight_resForm_nonneg hK _ _)
  have hp0 : p ≠ 0 := by
    rintro rfl
    have hJt : J = ⊤ := (Ideal.eq_top_iff_one J).2
      (hcol ▸ Submodule.mem_colon_singleton.2 (by simp))
    rw [hJt, hilbertPoly_top hb] at hβ
    simp at hβ
    omega
  obtain ⟨D, hD, hhom⟩ := exists_isWeightedHomogeneous_resForm_leftIndex_linIndex hb hJ
    (Sigma.fst : LinForms β → ι) (by rw [card_linForms]; omega) δ
  rw [formCount_linForms] at hD
  have hDnn : (0 : ℝ) ≤ multidegree b J β := by
    rw [← hD]
    positivity
  rcases eq_or_ne δ 0 with rfl | hδ
  · -- `p` is a nonzero constant, so `J + (p) = (1)`.
    have hpC := eq_C_of_isWeightedHomogeneous_zero hp
    have hc : p.coeff 0 ≠ 0 := fun h ↦ hp0 (by rw [hpC, h, map_zero])
    have hu : IsUnit p := hpC ▸ (isUnit_iff_ne_zero.2 hc).map C
    have htop : J ⊔ Ideal.span {p} = ⊤ :=
      eq_top_iff.2 ((Ideal.span_singleton_eq_top.2 hu).ge.trans le_sup_right)
    rw [htop, cycleHeight, components_top, sum_empty, hpC, bombieriLogHeight_C b hc]
    simp
  -- The main case: Thm 3.4 with Cor. 3.6 for the resultant forms, split over the components.
  have hne : Nonempty (LinForms β) :=
    Fintype.card_pos_iff.1 (by rw [card_linForms]; omega)
  have hdimJ : (hilbertPoly b J).totalDegree ≤ Fintype.card (LinForms β) := by
    rw [card_linForms]
    omega
  have key := gaussHeight_resForm_sup_le hK hb hJ hdimJ hδ hp hp0 hcol hhom
  have hJp : (J ⊔ Ideal.span {p}).IsWeightedHomogeneous (multiWeight b) :=
    hJ.sup (isWeightedHomogeneous_span fun x hx ↦ ⟨δ, (Set.mem_singleton_iff.mp hx) ▸ hp⟩)
  have hdimJp : (hilbertPoly b (J ⊔ Ideal.span {p})).totalDegree + 1 ≤ β.degree := by
    rw [hilbertPoly_sup_span_singleton_of_colon_eq hb hJ hp hp0 hcol]
    have := totalDegree_sub_shiftPoly_le δ (hilbertPoly b J)
    omega
  have hterm : ∀ i, gaussHeight remodelWeight (resForm b K
      (leftIndex (Pi.single i 1) (linIndex (Sigma.fst : LinForms β → ι))) J) =
        cycleHeight b (resHeight b) J (β + Finsupp.single i 1) := fun i ↦ by
    have hdeg : (hilbertPoly b J).totalDegree + 1 ≤ (β + Finsupp.single i 1).degree := by
      rw [map_add, Finsupp.degree_single]
      omega
    rw [leftIndex_single_linIndex, gaussHeight_resForm_linIndex_congr hK
      (τ := (Sigma.fst : LinForms (β + Finsupp.single i 1) → ι))
      (by rw [formCount_linForms, formCount_option, formCount_linForms]) hb hJ
      (by rw [card_linForms]; exact hdeg)]
    exact resHeight_eq_cycleHeight hK hb hJ hdeg
  rw [← resHeight_eq_cycleHeight hK hb hJp hdimJp]
  refine key.trans (le_of_eq ?_)
  rw [Finset.sum_congr rfl fun i _ ↦ by rw [hterm i]]
  congr 2
  exact_mod_cast hD

/-- **The point bound** (Evertse 1995, §5, p. 247) for the heights `h_β`: if `V(J)` projects to
the point `P` in the block `h`, i.e. `J` contains the `P_s X_t - P_t X_s` (`b s = b t = h`), then
`h_{β + ε_h}(V(J)) ≥ d_β(V(J)) log H(P)`. -/
theorem logHeight_mul_le_cycleHeight (hK : ArchEmbedded K) (hb : Function.Surjective b)
    {J : Ideal (MvPolynomial σ K)} (hJ : J.IsWeightedHomogeneous (multiWeight b)) {h : ι}
    (P : σ → K) {s₀ : σ} (hs₀ : b s₀ = h) (hP₀ : P s₀ ≠ 0)
    (hPJ : ∀ s t, b s = h → b t = h → C (P s) * X t - C (P t) * X s ∈ J) (β : ι →₀ ℕ)
    (hβ : (hilbertPoly b J).totalDegree ≤ β.degree) :
    (multidegree b J β : ℝ) * Height.logHeight (fun t : {t // b t = h} ↦ P t) ≤
      cycleHeight b (resHeight b) J (β + Finsupp.single h 1) := by
  obtain ⟨D, hD, hhom⟩ := exists_isWeightedHomogeneous_resForm_leftIndex_linIndex hb hJ
    (Sigma.fst : LinForms β → ι) (by rw [card_linForms]; exact hβ) (Pi.single h 1)
  rw [formCount_linForms] at hD
  have hdeg : (hilbertPoly b J).totalDegree + 1 ≤ (β + Finsupp.single h 1).degree := by
    rw [map_add, Finsupp.degree_single]
    omega
  have hcard : (hilbertPoly b J).totalDegree + 1 ≤ Nat.card (Option (LinForms β)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_option, card_linForms]
    omega
  have key := logHeight_mul_le_gaussHeight_resForm hK hb hJ hcard rfl P hs₀ hP₀ hPJ hhom
  rw [leftIndex_single_linIndex, gaussHeight_resForm_linIndex_congr hK
    (τ := (Sigma.fst : LinForms (β + Finsupp.single h 1) → ι))
    (by rw [formCount_linForms, formCount_option, formCount_linForms]) hb hJ
    (by rw [card_linForms]; exact hdeg)] at key
  rw [← resHeight_eq_cycleHeight hK hb hJ hdeg]
  have hDR : (multidegree b J β : ℝ) = D := by
    rw [← hD]
    push_cast
    rfl
  rw [hDR]
  exact key

omit [Fintype ι] [Field K] [AdmissibleAbsValues K] in
theorem card_block [Finite ι] (hb : Function.Surjective b) (i : ι) :
    #{s | b s = i} = bottomType b i + 1 := by
  obtain ⟨s, hs⟩ := hb i
  have hpos : 0 < #{s | b s = i} := card_pos.2 ⟨s, by simp [hs]⟩
  have : bottomType b i = Nat.card {s // b s = i} - 1 := rfl
  rw [this, Nat.card_eq_fintype_card, Fintype.card_subtype]
  omega

omit [Fintype σ] in
theorem card_linForms_fiber (β : ι →₀ ℕ) (i : ι) :
    #{x : LinForms β | x.1 = i} = β i := by
  rw [← formCount_apply, formCount_linForms]

/-- **The height of `ℙ`** in the index `n + ε_l`: `h(ℙ) ≤ [K : ℚ] log M(det_{n_l + 1})`. -/
theorem resHeight_bot_single_le (hK : ArchEmbedded K) (hb : Function.Surjective b) (l : ι) :
    resHeight b (⊥ : Ideal (MvPolynomial σ K)) (bottomType b + Finsupp.single l 1) ≤
      totalWeight K * detLogMahler (bottomType b l + 1) := by
  classical
  set β := bottomType b + Finsupp.single l 1
  have hcl : Fintype.card {s // b s = l} = bottomType b l + 1 := by
    rw [Fintype.card_subtype, card_block hb]
  have hfib : ∀ i, #{x : LinForms β | x.1 = i} = bottomType b i + if i = l then 1 else 0 :=
    fun i ↦ by
      rw [card_linForms_fiber]
      by_cases hi : i = l <;> simp [β, hi]
  have e : {s // b s = l} ≃ {x : LinForms β // x.1 = l} := Fintype.equivOfCardEq (by
    rw [hcl, Fintype.card_subtype, hfib]
    simp)
  have h := gaussHeight_resForm_bot_le (K := K) hK hb (d := linIndex (Sigma.fst : LinForms β → ι))
    (fun _ ↦ rfl) e fun i hi ↦ by simp [hfib, card_block hb, hi]
  rwa [hcl] at h

/-- The other heights of `ℙ` vanish. -/
theorem resHeight_bot_of_ne (hK : ArchEmbedded K) (hb : Function.Surjective b) {β : ι →₀ ℕ}
    (hβ : β.degree = (bottomType b).degree + 1)
    (hne : ∀ l, β ≠ bottomType b + Finsupp.single l 1) :
    resHeight b (⊥ : Ideal (MvPolynomial σ K)) β = 0 := by
  have hsum : (bottomType b).degree = ∑ i, (#{s | b s = i} - 1) := by
    rw [Finsupp.degree_eq_sum]
    exact sum_congr rfl fun i _ ↦ by rw [card_block hb, Nat.add_sub_cancel]
  refine gaussHeight_resForm_bot_eq_zero hK hb (fun _ ↦ rfl)
    (by rw [card_linForms, hβ, hsum]) fun l₀ ↦ ?_
  by_contra! h
  have hle : ∀ i, β i ≤ (bottomType b + Finsupp.single l₀.1 1 : ι →₀ ℕ) i := fun i ↦ by
    have hi := h i
    rw [filter_erase] at hi
    rw [card_block hb] at hi
    have hf := card_linForms_fiber β i
    simp only [Finsupp.coe_add, Pi.add_apply]
    by_cases h0 : l₀.1 = i
    · rw [card_erase_of_mem (by simp [h0])] at hi
      have hi' : #{x : LinForms β | x.1 = i} - 1 < bottomType b i + 1 := by convert hi
      have : 0 < #{x : LinForms β | x.1 = i} := card_pos.2 ⟨l₀, by simp [h0]⟩
      rw [h0, Finsupp.single_eq_same]
      omega
    · rw [erase_eq_of_notMem (by simp [h0])] at hi
      have hi' : #{x : LinForms β | x.1 = i} < bottomType b i + 1 := by convert hi
      rw [Finsupp.single_eq_of_ne (Ne.symm h0)]
      omega
  have hdeg : β.degree = (bottomType b + Finsupp.single l₀.1 1).degree := by
    rw [hβ, map_add, Finsupp.degree_single]
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum] at hdeg
  have heq := (sum_eq_sum_iff_of_le fun i _ ↦ hle i).1 hdeg
  exact hne l₀.1 (Finsupp.ext fun i ↦ heq i (mem_univ i))

/-- **Rémond's heights**, with the Gaussian Mahler measure at the archimedean places, **form a
multiprojective height theory**, over every field whose archimedean absolute values come from
complex embeddings (e.g. number fields, `MvPolynomial.archEmbedded_of_numberField`). The bound
for `h(ℙ^n)` is `log M(det_{n + 1})`, the Gaussian Mahler measure of the generic
`(n + 1) × (n + 1)` determinant. -/
noncomputable def resultantHeight (hK : ArchEmbedded K) (hb : Function.Surjective b) :
    MultiprojectiveHeight (K := K) b where
  height := resHeight b
  height_nonneg _ _ _ _ _ := gaussHeight_resForm_nonneg hK _ _
  botBound n := detLogMahler (n + 1)
  height_bot_single_le l := resHeight_bot_single_le hK hb l
  height_bot_of_ne _ hβ hne := resHeight_bot_of_ne hK hb hβ hne
  cycleHeight_sup_le _ p δ hJ hp hcol β h1 hβ :=
    cycleHeight_resHeight_sup_le hK hb p δ hJ hp hcol β h1 hβ
  logHeight_mul_le_cycleHeight _ _ P _ hJ hs₀ hP₀ hPJ β hβ :=
    logHeight_mul_le_cycleHeight hK hb hJ P hs₀ hP₀ hPJ β hβ

/-- The bound for `h(ℙ^n)` is at most `(n + 1)(log (2(n + 1)) / 2 + 2)`. -/
theorem resultantHeight_botBound_le (hK : ArchEmbedded K) (hb : Function.Surjective b) (n : ℕ) :
    (resultantHeight hK hb).botBound n ≤ (n + 1 : ℕ) * (Real.log (2 * (n + 1 : ℕ)) / 2 + 2) :=
  detLogMahler_le (n + 1)

end MvPolynomial
