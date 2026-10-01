/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.Analysis.Polynomial.GaussianMahlerLowerBound
public import ForMathlib.Analysis.Polynomial.ResultantMahler
public import ForMathlib.RingTheory.MvPolynomial.ResultantGauss
public import Mathlib.NumberTheory.Height.NumberField

-- Used only inside proofs.
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Heights of resultant forms

The height of a polynomial `F` over a field `K` with admissible absolute values
(`Height.AdmissibleAbsValues`), as in Rémond (LNM 1752, Ch. 7, §2.1): the Mahler measure at the
archimedean places and the Gauss norm (the maximum of the coefficients) at the nonarchimedean
ones,
`h(F) = ∑_{v | ∞} log M(φ_v(F)) + ∑_{v ∤ ∞} log max_m |f_m|_v`.
The Mahler measure is the Gaussian one (`MvPolynomial.gaussLogMahler`), after scaling the
variables by weights `w` (Rémond's remodeling `α_d`, with `w = MvPolynomial.remodelWeight`), and
`φ_v : K → ℂ` is an embedding with `v = |φ_v(·)|`. Rémond also applies `α_d` at the finite places,
over an extension of `K`; here it is not, which does not change his arguments.

Heights are relative to `K`, in Mathlib's normalization.

## Main definitions

* `MvPolynomial.ArchEmbedded`: every archimedean absolute value comes from an embedding into `ℂ`
  (`MvPolynomial.archEmbedded_of_numberField`).
* `MvPolynomial.archMahler`: the local Mahler measure `M(α φ_v(F))`.
* `MvPolynomial.gaussHeight`: the height `h(α F)`; it does not change under nonzero scalars
  (`MvPolynomial.gaussHeight_C_mul`) and is nonnegative (`MvPolynomial.gaussHeight_nonneg`).

## Main results

* `MvPolynomial.gaussHeight_resForm_sumIndex`: **Rémond's Theorem 2.2**, two factors:
  `h(α res_{(e + e', d')}(I)) = h(α res_{(e, d')}(I)) + h(α res_{(e', d')}(I))`.
* `MvPolynomial.gaussHeight_resForm_leftIndex`: **Rémond's Theorem 2.2**:
  `h(α res_{(δ, d')}(I)) = ∑_i δ_i h(α res_{(ε_i, d')}(I))`.
-/

@[expose] public section

open Height Height.AdmissibleAbsValues Real

namespace MvPolynomial

section Height

variable (K : Type*) [Field K] [AdmissibleAbsValues K]

/-- The archimedean absolute values of `K` come from embeddings `K → ℂ`. -/
def ArchEmbedded : Prop :=
  ∀ v ∈ archAbsVal (K := K), ∃ φ : K →+* ℂ, ∀ x, v x = ‖φ x‖

variable {K} {τ : Type*} [Fintype τ]

open Classical in
/-- The local Mahler measure `M(α φ_v(F))` at an absolute value `v = |φ_v(·)|`, with the variables
scaled by `w`, and `1` if `v` does not come from an embedding into `ℂ`. -/
noncomputable def archMahler (w : τ → ℂ) (v : AbsoluteValue K ℝ) (F : MvPolynomial τ K) : ℝ :=
  if h : ∃ φ : K →+* ℂ, ∀ x, v x = ‖φ x‖ then exp (gaussLogMahler (scaleVars w (map h.choose F)))
  else 1

omit [AdmissibleAbsValues K] in
theorem archMahler_of {w : τ → ℂ} {v : AbsoluteValue K ℝ} (h : ∃ φ : K →+* ℂ, ∀ x, v x = ‖φ x‖)
    (F : MvPolynomial τ K) :
    archMahler w v F = exp (gaussLogMahler (scaleVars w (map h.choose F))) := by
  unfold archMahler
  split_ifs
  rfl

omit [AdmissibleAbsValues K] in
theorem archMahler_pos (w : τ → ℂ) (v : AbsoluteValue K ℝ) (F : MvPolynomial τ K) :
    0 < archMahler w v F := by
  unfold archMahler
  split_ifs
  exacts [exp_pos _, one_pos]

open Classical in
/-- **The height** `h(α F)` of a polynomial: `∑_{v | ∞} log M(α φ_v(F)) +
∑_{v ∤ ∞} log max_m |f_m|_v`, and `0` for `F = 0`. -/
noncomputable def gaussHeight (w : τ → ℂ) (F : MvPolynomial τ K) : ℝ :=
  if F = 0 then 0 else
    log ((archAbsVal.map fun v ↦ archMahler w v F).prod *
      ∏ᶠ v : nonarchAbsVal, maxNorm v.val F)

omit [Fintype τ] in
theorem hasFiniteMulSupport_maxNorm {F : MvPolynomial τ K} (hF : F ≠ 0) :
    Function.HasFiniteMulSupport fun v : nonarchAbsVal (K := K) ↦ maxNorm v.val F := by
  refine Set.Finite.subset (Set.Finite.biUnion F.support.finite_toSet fun m hm ↦
    hasFiniteMulSupport (mem_support_iff.1 hm)) fun v hv ↦ ?_
  simp only [Set.mem_iUnion]
  by_contra! h
  refine hv (maxNorm_eq_of (fun m ↦ ?_) ?_)
  · by_cases hm : m ∈ F.support
    · exact (Function.notMem_mulSupport.1 (h m hm)).le
    · rw [notMem_support_iff.1 hm, map_zero]
      exact zero_le_one
  · obtain ⟨m, hm⟩ := support_nonempty.2 hF
    exact ⟨m, Function.notMem_mulSupport.1 (h m hm)⟩

omit [Fintype τ] in
theorem finprod_maxNorm_pos {F : MvPolynomial τ K} (hF : F ≠ 0) :
    0 < ∏ᶠ v : nonarchAbsVal (K := K), maxNorm v.val F := by
  classical
  rw [finprod_def]
  split_ifs
  · exact Finset.prod_pos fun v _ ↦ maxNorm_pos hF
  · exact one_pos

omit [Fintype τ] in
theorem finprod_maxNorm_C_mul {c : K} (hc : c ≠ 0) {F : MvPolynomial τ K} (hF : F ≠ 0) :
    ∏ᶠ v : nonarchAbsVal (K := K), maxNorm v.val (C c * F) =
      (∏ᶠ v : nonarchAbsVal (K := K), v.val c) *
        ∏ᶠ v : nonarchAbsVal (K := K), maxNorm v.val F := by
  simp_rw [maxNorm_C_mul]
  exact finprod_mul_distrib (hasFiniteMulSupport hc) (hasFiniteMulSupport_maxNorm hF)

/-- **Heights do not change under nonzero scalars** (the product formula). -/
theorem gaussHeight_C_mul (hK : ArchEmbedded K) {w : τ → ℂ} (hw : ∀ t, w t ≠ 0) {c : K}
    (hc : c ≠ 0) (F : MvPolynomial τ K) : gaussHeight w (C c * F) = gaussHeight w F := by
  rcases eq_or_ne F 0 with rfl | hF
  · simp
  have hcF : C c * F ≠ 0 := mul_ne_zero (C_ne_zero.2 hc) hF
  have harch : ∀ v ∈ archAbsVal (K := K), archMahler w v (C c * F) = v c * archMahler w v F :=
    fun v hv ↦ by
      have h := hK v hv
      have hne : scaleVars w (map h.choose F) ≠ 0 := scaleVars_ne_zero hw fun h0 ↦
        hF (map_injective _ h.choose.injective (by rw [h0, map_zero]))
      rw [archMahler_of h, archMahler_of h, map_mul, map_C, map_mul,
        show scaleVars w (C (h.choose c)) = C (h.choose c) from aeval_C _ _,
        gaussLogMahler_C_mul ((map_ne_zero _).2 hc) hne, exp_add,
        exp_log (norm_pos_iff.2 ((map_ne_zero _).2 hc)), ← h.choose_spec c]
  simp only [gaussHeight, hcF, hF, ↓reduceIte]
  rw [Multiset.map_congr rfl harch, Multiset.prod_map_mul, finprod_maxNorm_C_mul hc hF]
  congr 1
  linear_combination ((archAbsVal.map fun v ↦ archMahler w v F).prod *
    ∏ᶠ v : nonarchAbsVal (K := K), maxNorm v.val F) * product_formula (K := K) hc

omit [AdmissibleAbsValues K] in
theorem archMahler_mul {w : τ → ℂ} (hw : ∀ t, w t ≠ 0) {v : AbsoluteValue K ℝ}
    (h : ∃ φ : K →+* ℂ, ∀ x, v x = ‖φ x‖) {F G : MvPolynomial τ K} (hF : F ≠ 0) (hG : G ≠ 0) :
    archMahler w v (F * G) = archMahler w v F * archMahler w v G := by
  have hne : ∀ {P : MvPolynomial τ K}, P ≠ 0 → scaleVars w (map h.choose P) ≠ 0 :=
    fun {P} hP ↦ scaleVars_ne_zero hw fun h0 ↦
      hP (map_injective _ h.choose.injective (by rw [h0, map_zero]))
  rw [archMahler_of h, archMahler_of h, archMahler_of h, map_mul, map_mul,
    gaussLogMahler_mul (hne hF) (hne hG), exp_add]

omit [AdmissibleAbsValues K] in
theorem archMahler_one (w : τ → ℂ) (v : AbsoluteValue K ℝ) :
    archMahler w v (1 : MvPolynomial τ K) = 1 := by
  unfold archMahler
  split_ifs
  · rw [map_one, map_one, ← C_1, gaussLogMahler_C, norm_one, log_one, exp_zero]
  · rfl

theorem prod_archMahler_pos (w : τ → ℂ) (F : MvPolynomial τ K) :
    0 < (archAbsVal.map fun v ↦ archMahler w v F).prod :=
  Multiset.prod_pos fun _ hx ↦ by
    obtain ⟨v, -, rfl⟩ := Multiset.mem_map.1 hx
    exact archMahler_pos _ _ _

/-- **Heights are additive** on products. -/
theorem gaussHeight_mul (hK : ArchEmbedded K) {w : τ → ℂ} (hw : ∀ t, w t ≠ 0)
    {F G : MvPolynomial τ K} (hF : F ≠ 0) (hG : G ≠ 0) :
    gaussHeight w (F * G) = gaussHeight w F + gaussHeight w G := by
  simp only [gaussHeight, hF, hG, mul_ne_zero hF hG, ↓reduceIte]
  rw [← log_mul (mul_pos (prod_archMahler_pos w F) (finprod_maxNorm_pos hF)).ne'
      (mul_pos (prod_archMahler_pos w G) (finprod_maxNorm_pos hG)).ne',
    Multiset.map_congr rfl fun v hv ↦ archMahler_mul hw (hK v hv) hF hG, Multiset.prod_map_mul,
    finprod_congr fun v : nonarchAbsVal (K := K) ↦ maxNorm_mul (isNonarchimedean _ v.2) F G,
    finprod_mul_distrib (hasFiniteMulSupport_maxNorm hF) (hasFiniteMulSupport_maxNorm hG)]
  ring_nf

theorem gaussHeight_one (w : τ → ℂ) : gaussHeight w (1 : MvPolynomial τ K) = 0 := by
  simp [gaussHeight, archMahler_one, maxNorm_one]

theorem gaussHeight_C (hK : ArchEmbedded K) {w : τ → ℂ} (hw : ∀ t, w t ≠ 0) {c : K}
    (hc : c ≠ 0) : gaussHeight w (C c : MvPolynomial τ K) = 0 := by
  simpa [gaussHeight_one] using gaussHeight_C_mul hK hw hc (1 : MvPolynomial τ K)

/-- Heights only depend on polynomials up to units. -/
theorem gaussHeight_of_associated (hK : ArchEmbedded K) {w : τ → ℂ} (hw : ∀ t, w t ≠ 0)
    {F G : MvPolynomial τ K} (h : Associated F G) : gaussHeight w F = gaussHeight w G := by
  obtain ⟨u, rfl⟩ := h
  obtain ⟨c, hc, hu⟩ := isUnit_iff_eq_C_of_isReduced.1 u.isUnit
  rw [hu, mul_comm, gaussHeight_C_mul hK hw hc.ne_zero]

theorem gaussHeight_prod (hK : ArchEmbedded K) {w : τ → ℂ} (hw : ∀ t, w t ≠ 0) {α : Type*}
    (s : Finset α) {F : α → MvPolynomial τ K} (hF : ∀ a ∈ s, F a ≠ 0) :
    gaussHeight w (∏ a ∈ s, F a) = ∑ a ∈ s, gaussHeight w (F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, gaussHeight_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, gaussHeight_mul hK hw
      (hF a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.2 fun b hb ↦ hF b
      (Finset.mem_insert_of_mem hb)), ih fun b hb ↦ hF b (Finset.mem_insert_of_mem hb)]

theorem gaussHeight_pow (hK : ArchEmbedded K) {w : τ → ℂ} (hw : ∀ t, w t ≠ 0)
    {F : MvPolynomial τ K} (hF : F ≠ 0) (n : ℕ) : gaussHeight w (F ^ n) = n * gaussHeight w F := by
  simpa using gaussHeight_prod hK hw (Finset.range n) (F := fun _ ↦ F) fun _ _ ↦ hF

omit [AdmissibleAbsValues K] [Fintype τ] in
theorem scaleVars_rename {τ' : Type*} (e : τ → τ') {w : τ → ℂ} {w' : τ' → ℂ}
    (hw : ∀ t, w' (e t) = w t) (P : MvPolynomial τ ℂ) :
    scaleVars w' (rename e P) = rename e (scaleVars w P) := by
  have : (scaleVars w').comp (rename e) = (rename e).comp (scaleVars w) :=
    algHom_ext fun t ↦ by simp [scaleVars, hw]
  exact AlgHom.congr_fun this P

/-- Heights do not change under renaming the variables along an equivalence preserving the
weights. -/
theorem gaussHeight_rename {τ' : Type*} [Fintype τ'] (e : τ ≃ τ') {w : τ → ℂ} {w' : τ' → ℂ}
    (hw : ∀ t, w' (e t) = w t) (F : MvPolynomial τ K) :
    gaussHeight w' (rename e F) = gaussHeight w F := by
  rcases eq_or_ne F 0 with rfl | hF
  · simp [gaussHeight]
  have hF' : rename e F ≠ 0 := fun h ↦ hF (rename_injective _ e.injective (by rw [h, map_zero]))
  have harch : ∀ v : AbsoluteValue K ℝ, archMahler w' v (rename e F) = archMahler w v F := by
    intro v
    unfold archMahler
    split_ifs with h
    · rw [map_rename, scaleVars_rename e hw, gaussLogMahler_rename e.injective]
    · rfl
  simp only [gaussHeight, hF, hF', ↓reduceIte, harch, maxNorm_rename e.injective]

/-- **Heights are nonnegative** for weights of norm at least `1`: by the product formula
applied to a suitable coefficient `f_m`, using `|f_m| ≤ M(F)` at the archimedean places
(`MvPolynomial.exists_mem_log_norm_coeff_le`). -/
theorem gaussHeight_nonneg (hK : ArchEmbedded K) {w : τ → ℂ} (hw : ∀ t, 1 ≤ ‖w t‖)
    (F : MvPolynomial τ K) : 0 ≤ gaussHeight w F := by
  classical
  rcases eq_or_ne F 0 with rfl | hF
  · simp [gaussHeight]
  obtain ⟨m, hm, hmF⟩ := exists_mem_log_norm_coeff_le F.support (support_nonempty.2 hF)
  have hc : F.coeff m ≠ 0 := mem_support_iff.1 hm
  have hpow : ∀ n : τ →₀ ℕ, 1 ≤ ‖n.prod fun t k ↦ w t ^ k‖ := fun n ↦ by
    rw [Finsupp.prod, norm_prod]
    exact Finset.one_le_prod₀ fun t _ ↦ by rw [norm_pow]; exact one_le_pow₀ (hw t)
  have harch : ∀ v ∈ archAbsVal (K := K), v (F.coeff m) ≤ archMahler w v F := fun v hv ↦ by
    have h := hK v hv
    have hG : (scaleVars w (map h.choose F)).support = F.support := by
      ext n
      simp only [mem_support_iff, coeff_scaleVars, coeff_map, ne_eq, mul_eq_zero,
        map_eq_zero_iff _ h.choose.injective, not_or, and_iff_right_iff_imp]
      exact fun _ ↦ norm_ne_zero_iff.1 (zero_lt_one.trans_le (hpow n)).ne'
    have h1 := hmF _ hG
    rw [coeff_scaleVars, coeff_map] at h1
    rw [archMahler_of h, h.choose_spec]
    have hpos : 0 < ‖h.choose (F.coeff m)‖ := norm_pos_iff.2 ((map_ne_zero _).2 hc)
    calc ‖h.choose (F.coeff m)‖
        ≤ ‖(m.prod fun t k ↦ w t ^ k) * h.choose (F.coeff m)‖ := by
          rw [norm_mul]
          exact le_mul_of_one_le_left hpos.le (hpow m)
      _ ≤ _ := by
          rw [← exp_log (norm_pos_iff.2 (mul_ne_zero (norm_ne_zero_iff.1
            (zero_lt_one.trans_le (hpow m)).ne') (norm_ne_zero_iff.1 hpos.ne')))]
          exact exp_le_exp.2 h1
  have hnon : ∀ v : nonarchAbsVal (K := K), v.val (F.coeff m) ≤ maxNorm v.val F :=
    fun v ↦ le_maxNorm F m
  simp only [gaussHeight, hF, ↓reduceIte]
  refine log_nonneg ((product_formula (K := K) hc).symm.le.trans (mul_le_mul
    (Multiset.prod_map_le_prod_map₀ _ _ (fun v _ ↦ v.nonneg _) harch)
    (finprod_le_finprod₀ (hasFiniteMulSupport hc) (fun v ↦ v.val.nonneg _)
      (hasFiniteMulSupport_maxNorm hF) hnon)
    (finprod_nonneg fun v ↦ v.val.nonneg _) (Multiset.prod_nonneg fun x hx ↦ ?_)))
  obtain ⟨v, -, rfl⟩ := Multiset.mem_map.1 hx
  exact (archMahler_pos _ _ _).le

end Height

/-- The archimedean absolute values of a number field come from its complex embeddings. -/
theorem archEmbedded_of_numberField (K : Type*) [Field K] [NumberField K] : ArchEmbedded K :=
  fun v hv ↦ by
    obtain ⟨φ, rfl⟩ := NumberField.mem_multisetInfinitePlace.1 hv
    exact ⟨φ, fun x ↦ rfl⟩

section Theorem22

variable {σ ι : Type} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι} {K : Type} [Field K]
  [AdmissibleAbsValues K] {κ : Type} [Fintype κ] {e e' : ι → ℕ} {d' : κ → ι → ℕ}

/-- **Rémond's Theorem 2.2**, two factors (LNM 1752, Ch. 7): for `deg H_I ≤ r - 1`,
`h(α res_{(e + e', d')}(I)) = h(α res_{(e, d')}(I)) + h(α res_{(e', d')}(I))`. -/
theorem gaussHeight_resForm_sumIndex (hK : ArchEmbedded K) (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree ≤ Fintype.card κ) :
    gaussHeight remodelWeight (resForm b K (sumIndex e e' d') I) =
      gaussHeight remodelWeight (resForm b K (leftIndex e d') I) +
        gaussHeight remodelWeight (resForm b K (leftIndex e' d') I) := by
  have hcard : (hilbertPoly b I).totalDegree + 1 ≤ Nat.card (Option κ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_option]
    omega
  have hne : ∀ f : Option κ → ι → ℕ, resForm b K f I ≠ 0 := fun f ↦
    resForm_ne_zero hb hI hcard
  obtain ⟨c, hc0, hc⟩ := exists_productMap_resForm_eq (e := e) (e' := e') (d' := d') hb hI hdim
  set F := resForm b K (sumIndex e e' d') I
  set F₁ := resForm b K (leftIndex e d') I
  set F₂ := resForm b K (leftIndex e' d') I
  have harch : ∀ v ∈ archAbsVal (K := K), archMahler remodelWeight v F =
      v c * (archMahler remodelWeight v F₁ * archMahler remodelWeight v F₂) := fun v hv ↦ by
    have h := hK v hv
    rw [archMahler_of h, archMahler_of h, archMahler_of h,
      gaussLogMahler_resForm_sumIndex_of_eq hb hI hdim hc0 hc, exp_add, exp_add,
      exp_log (norm_pos_iff.2 ((map_ne_zero _).2 hc0)), ← h.choose_spec c, mul_assoc]
  have hnon : ∀ v : nonarchAbsVal (K := K), maxNorm v.val F =
      v.val c * (maxNorm v.val F₁ * maxNorm v.val F₂) := fun v ↦ by
    rw [maxNorm_resForm_sumIndex_of_eq hb hI hdim hc (isNonarchimedean _ v.2), mul_assoc]
  have hprod := product_formula (K := K) hc0
  have hF : F ≠ 0 := hne _
  have hF₁ : F₁ ≠ 0 := hne _
  have hF₂ : F₂ ≠ 0 := hne _
  simp only [gaussHeight, hF, hF₁, hF₂, ↓reduceIte]
  rw [← log_mul (mul_pos (Multiset.prod_pos fun _ hx ↦ by
      obtain ⟨v, -, rfl⟩ := Multiset.mem_map.1 hx; exact archMahler_pos _ _ _)
      (finprod_maxNorm_pos (hne _))).ne'
    (mul_pos (Multiset.prod_pos fun _ hx ↦ by
      obtain ⟨v, -, rfl⟩ := Multiset.mem_map.1 hx; exact archMahler_pos _ _ _)
      (finprod_maxNorm_pos (hne _))).ne',
    Multiset.map_congr rfl harch, Multiset.prod_map_mul, Multiset.prod_map_mul,
    finprod_congr hnon,
    finprod_mul_distrib (f := fun v : nonarchAbsVal (K := K) ↦ v.val c)
      (g := fun v ↦ maxNorm v.val F₁ * maxNorm v.val F₂) (hasFiniteMulSupport hc0)
      (Function.HasFiniteMulSupport.mul (hasFiniteMulSupport_maxNorm hF₁)
        (hasFiniteMulSupport_maxNorm hF₂)),
    finprod_mul_distrib (f := fun v : nonarchAbsVal (K := K) ↦ maxNorm v.val F₁)
      (g := fun v ↦ maxNorm v.val F₂) (hasFiniteMulSupport_maxNorm hF₁)
      (hasFiniteMulSupport_maxNorm hF₂)]
  congr 1
  linear_combination (((archAbsVal.map fun v ↦ archMahler remodelWeight v F₁).prod *
      (archAbsVal.map fun v ↦ archMahler remodelWeight v F₂).prod) *
    ((∏ᶠ v : nonarchAbsVal (K := K), maxNorm v.val F₁) *
      ∏ᶠ v : nonarchAbsVal (K := K), maxNorm v.val F₂)) * hprod

/-- Heights of resultant forms are nonnegative. -/
theorem gaussHeight_resForm_nonneg (hK : ArchEmbedded K) (d : κ → ι → ℕ)
    (I : Ideal (MvPolynomial σ K)) : 0 ≤ gaussHeight remodelWeight (resForm b K d I) :=
  gaussHeight_nonneg hK one_le_norm_remodelWeight _

omit [Fintype σ] [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem sumIndex_eq_leftIndex : sumIndex e e' d' = leftIndex (e + e') d' :=
  rfl

/-- **Rémond's Theorem 2.2** (LNM 1752, Ch. 7): for `deg H_I ≤ r - 1` and `δ ≠ 0`,
`h(α res_{(δ, d')}(I)) = ∑_i δ_i h(res_{(ε_i, d')}(I))`. -/
theorem gaussHeight_resForm_leftIndex (hK : ArchEmbedded K) (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree ≤ Fintype.card κ) {δ : ι → ℕ} (hδ : δ ≠ 0) :
    gaussHeight remodelWeight (resForm b K (leftIndex δ d') I) =
      ∑ i, (δ i : ℝ) *
        gaussHeight remodelWeight (resForm b K (leftIndex (Pi.single i 1) d') I) := by
  obtain ⟨n, hn⟩ : ∃ n, ∑ i, δ i = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing δ with
  | _ n ih =>
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hδ
  by_cases h1 : δ = Pi.single i 1
  · subst h1
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
    simp
  set δ' := δ - Pi.single i 1
  have hδδ' : δ = Pi.single i 1 + δ' := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [δ', Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
      have : δ j ≠ 0 := hi
      omega
    · simp [δ', hj]
  have hδ' : δ' ≠ 0 := fun h0 ↦ h1 (by rw [hδδ', h0, add_zero])
  have hsum : ∑ j, δ j = ∑ j, δ' j + 1 := by
    conv_lhs => rw [hδδ']
    simp [Finset.sum_add_distrib, add_comm]
  have key := gaussHeight_resForm_sumIndex (e := Pi.single i 1) (e' := δ') (d' := d') hK hb hI hdim
  rw [sumIndex_eq_leftIndex, ← hδδ'] at key
  rw [key, ih _ (by omega) hδ' rfl]
  conv_rhs => rw [hδδ']
  simp only [Pi.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  have hs : ∀ H : ι → ℝ, ∑ x, (((Pi.single i 1 : ι → ℕ) x : ℕ) : ℝ) * H x = H i := fun H ↦ by
    simp [Pi.single_apply]
  rw [hs]

end Theorem22

end MvPolynomial
