/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormFiltrationHeight

-- Used only inside proofs.
import ArithmeticHeights.CauchyBinet
import ArithmeticHeights.RowSpace

/-!
# The ratio of the largest to the smallest minor

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, Lemmas 10.1, 10.2 and 18.1.

Let `T ⊆ Ωⁿ` be spanned by the independent columns `g_1, …, g_k ∈ Kⁿ` of `G`, and let `θ` run
through the nonzero minors `det(L_{i_l}(g_j))_{l,j}` of `k` forms of `L` (EF13 (18.1)). Lemma 18.1
bounds `∏_v M_v / m_v`, `M_v` and `m_v` the largest and the smallest `‖θ‖_v`: these are the bounds
for the coefficients `α_ijv` of the induced system on `Ωⁿ / T` (Cramer's rule, EF13 (18.7)).

EF13's proof, followed here: change coordinates so that `L` contains `X_1, …, X_n` (the minors do
not change). Then every maximal minor of `k` forms is a determinant of `n` forms (Lemma 10.1), so
by Cauchy–Binet `∏_v M_v ≤ C(n,k) H_L H₂(T)` (Lemma 10.2), and `∏_v m_v ≥ (∏_v M_v)^{1 - #θ}` by
the product formula. Prop. 17.5 bounds `H₂(T)` by `(√n H_L)^{4ⁿ}`.

Heights are relative to `K` unless named `abs…`. Lemma 18.1 is stated for any member `T_l`,
`0 < l < r`, of the filtration of `(L, c)` (EF13: `T = T(L, c) = T_{r-1}`); it is conditional on
`NumberField.SemistableGap K Ω`, through Prop. 17.5.

## Main results

* `NumberField.mulRatioProd_le`: `∏_v M_v / m_v ≤ (∏_v M_v)^{#θ}` (from EF13 (10.2)).
* `NumberField.FormSystem.plucker_mem_detSet`, `apply_mem_detSet`: EF13 Lemma 10.1.
* `NumberField.FormSystem.mulSupProd_minorSet_le`: EF13 Lemma 10.2, (10.1).
* `NumberField.FormSystem.arakelovFormHeight_le`: `H₂(L_i) ≤ √n H_L` when `L` contains
  `X_1, …, X_n`.
* `NumberField.FormSystem.mulFormHeight_comp_le`, `minorSet_comp`, `isWeightFiltration_comp`:
  the change of coordinates.
* `NumberField.FormSystem.mulRatioProd_minorSet_le`, `mulRatioProd_minorSet_rpow_le`: EF13
  Lemma 18.1, `∏_v M_v / m_v ≤ (2 H_L)^{(4R)ⁿ}`.

This is milestone Q3.7 of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Module Finset Matrix
open exteriorPower (plucker)

namespace NumberField

section Finset

variable {α : Type*} {s : Finset α}

theorem le_iSup_finset (f : α → ℝ) {a : α} (ha : a ∈ s) : f a ≤ ⨆ e : s, f e :=
  Finite.le_ciSup_of_le (f := fun e : s ↦ f e) ⟨a, ha⟩ le_rfl

theorem iInf_finset_le (f : α → ℝ) {a : α} (ha : a ∈ s) : ⨅ e : s, f e ≤ f a :=
  ciInf_le (Finite.bddBelow_range _) (⟨a, ha⟩ : s)

theorem exists_eq_iInf_finset (hs : s.Nonempty) (f : α → ℝ) : ∃ b ∈ s, f b = ⨅ e : s, f e := by
  have : Nonempty s := hs.coe_sort
  obtain ⟨b, hb⟩ := exists_eq_ciInf_of_finite (f := fun e : s ↦ f e)
  exact ⟨b, b.2, hb⟩

theorem iSup_finset_eq_one (hs : s.Nonempty) {f : α → ℝ} (h : ∀ e ∈ s, f e = 1) :
    ⨆ e : s, f e = 1 := by
  have : Nonempty s := hs.coe_sort
  rw [show (fun e : s ↦ f e) = fun _ ↦ 1 from funext fun e ↦ h e e.2, ciSup_const]

theorem iInf_finset_eq_one (hs : s.Nonempty) {f : α → ℝ} (h : ∀ e ∈ s, f e = 1) :
    ⨅ e : s, f e = 1 := by
  have : Nonempty s := hs.coe_sort
  rw [show (fun e : s ↦ f e) = fun _ ↦ 1 from funext fun e ↦ h e e.2, ciInf_const]

end Finset

variable {K : Type*} [Field K] [NumberField K]

/-! ### The ratio `max / min` of a finite set of numbers -/

section Ratio

/-- `max_{θ ∈ s} f(θ) / min_{θ ∈ s} f(θ)`. -/
noncomputable def localRatio (s : Finset K) (f : K → ℝ) : ℝ := (⨆ e : s, f e) / ⨅ e : s, f e

/-- `∏_v max_{θ ∈ s} ‖θ‖_v`, relative to `K`. -/
noncomputable def mulSupProd (s : Finset K) : ℝ :=
  (∏ v : InfinitePlace K, (⨆ e : s, v e) ^ v.mult) * ∏ᶠ v : FinitePlace K, ⨆ e : s, v e

/-- `∏_v M_v / m_v`, `M_v` and `m_v` the largest and the smallest `‖θ‖_v`, `θ ∈ s`, relative to
`K`. -/
noncomputable def mulRatioProd (s : Finset K) : ℝ :=
  (∏ v : InfinitePlace K, localRatio s (fun x ↦ v x) ^ v.mult) *
    ∏ᶠ v : FinitePlace K, localRatio s fun x ↦ v x

variable {s : Finset K}

omit [NumberField K] in
theorem iSup_finset_nonneg (f : AbsoluteValue K ℝ) : 0 ≤ ⨆ e : s, f e :=
  Real.iSup_nonneg fun _ ↦ apply_nonneg _ _

omit [NumberField K] in
theorem iInf_finset_pos (hs : s.Nonempty) (h0 : 0 ∉ s) (f : AbsoluteValue K ℝ) :
    0 < ⨅ e : s, f e := by
  obtain ⟨b, hb, hbe⟩ := exists_eq_iInf_finset hs f
  rw [← hbe]
  exact f.pos fun h ↦ h0 (h ▸ hb)

omit [NumberField K] in
theorem div_le_localRatio (h0 : 0 ∉ s) (f : AbsoluteValue K ℝ) {a b : K} (ha : a ∈ s)
    (hb : b ∈ s) : f a / f b ≤ localRatio s f :=
  div_le_div₀ (iSup_finset_nonneg f) (le_iSup_finset f ha) (iInf_finset_pos ⟨b, hb⟩ h0 f)
    (iInf_finset_le f hb)

omit [NumberField K] in
theorem one_le_localRatio (hs : s.Nonempty) (h0 : 0 ∉ s) (f : AbsoluteValue K ℝ) :
    1 ≤ localRatio s f := by
  obtain ⟨b, hb⟩ := hs
  have := div_le_localRatio h0 f hb hb
  rwa [div_self (f.pos fun h ↦ h0 (h ▸ hb)).ne'] at this

omit [NumberField K] in
theorem localRatio_nonneg (f : AbsoluteValue K ℝ) : 0 ≤ localRatio s f :=
  div_nonneg (iSup_finset_nonneg f) (Real.iInf_nonneg fun _ ↦ apply_nonneg _ _)

omit [NumberField K] in
/-- **The local bound behind EF13 (10.2)**: `M / m ≤ M^{#s} / ‖∏_{θ ∈ s} θ‖`, since
`‖∏ θ‖ ≤ m M^{#s - 1}`. -/
theorem localRatio_le (hs : s.Nonempty) (h0 : 0 ∉ s) (f : AbsoluteValue K ℝ) :
    localRatio s f ≤ (⨆ e : s, f e) ^ #s * f (∏ e ∈ s, e)⁻¹ := by
  classical
  obtain ⟨b, hb, hbe⟩ := exists_eq_iInf_finset hs f
  set M := ⨆ e : s, f e
  have hM : 0 ≤ M := iSup_finset_nonneg f
  have hb0 : 0 < f b := f.pos fun h ↦ h0 (h ▸ hb)
  have hP : (∏ e ∈ s, e) ≠ 0 := prod_ne_zero_iff.2 fun e he h ↦ h0 (h ▸ he)
  have hprod : f (∏ e ∈ s, e) ≤ f b * M ^ (#s - 1) := by
    rw [map_prod, ← mul_prod_erase s _ hb]
    refine mul_le_mul_of_nonneg_left ?_ hb0.le
    rw [← card_erase_of_mem hb, ← prod_const]
    exact prod_le_prod₀ (fun _ _ ↦ apply_nonneg _ _) fun e he ↦
      le_iSup_finset f (mem_of_mem_erase he)
  have hs1 : #s = #s - 1 + 1 := (Nat.sub_add_cancel (card_pos.2 hs)).symm
  rw [localRatio, ← hbe, map_inv₀, ← div_eq_mul_inv, div_le_div_iff₀ hb0 (f.pos hP)]
  calc M * f (∏ e ∈ s, e) ≤ M * (f b * M ^ (#s - 1)) := mul_le_mul_of_nonneg_left hprod hM
    _ = M ^ #s * f b := by
      conv_rhs => rw [hs1, pow_succ']
      ring

/-- At almost all finite places every `θ ∈ s` has absolute value `1`. -/
theorem finite_setOf_exists_ne_one (h0 : 0 ∉ s) :
    {v : FinitePlace K | ∃ e ∈ s, v e ≠ 1}.Finite := by
  refine (s.finite_toSet.biUnion fun e he ↦ FinitePlace.hasFiniteMulSupport
    (fun h ↦ h0 (h ▸ he))).subset fun v ⟨e, he, hv⟩ ↦ Set.mem_biUnion he hv

theorem hasFiniteMulSupport_iSup_finset (hs : s.Nonempty) (h0 : 0 ∉ s) :
    (fun v : FinitePlace K ↦ ⨆ e : s, v e).HasFiniteMulSupport :=
  (finite_setOf_exists_ne_one h0).subset fun v hv ↦ by
    by_contra h
    simp only [Set.mem_ofPred_eq, not_exists, not_and, not_not] at h
    exact hv (iSup_finset_eq_one hs h)

theorem hasFiniteMulSupport_localRatio (hs : s.Nonempty) (h0 : 0 ∉ s) :
    (fun v : FinitePlace K ↦ localRatio s fun x ↦ v x).HasFiniteMulSupport :=
  (finite_setOf_exists_ne_one h0).subset fun v hv ↦ by
    by_contra h
    simp only [Set.mem_ofPred_eq, not_exists, not_and, not_not] at h
    refine hv ?_
    change localRatio s (fun x ↦ v x) = 1
    rw [localRatio, iSup_finset_eq_one hs h, iInf_finset_eq_one hs h, div_one]

/-- A product over all places of local bounds `f_v ≤ g_v`. -/
theorem prod_places_le {f g : InfinitePlace K → ℝ} {f' g' : FinitePlace K → ℝ}
    (hf : ∀ v, 0 ≤ f v) (hf' : ∀ v, 0 ≤ f' v) (hfs : f'.HasFiniteMulSupport)
    (hgs : g'.HasFiniteMulSupport) (h : ∀ v, f v ≤ g v) (h' : ∀ v, f' v ≤ g' v) :
    (∏ v, f v ^ v.mult) * ∏ᶠ v, f' v ≤ (∏ v, g v ^ v.mult) * ∏ᶠ v, g' v :=
  mul_le_mul (Finset.prod_le_prod₀ (fun v _ ↦ pow_nonneg (hf v) _)
      fun v _ ↦ pow_le_pow_left₀ (hf v) (h v) _)
    (Twist.finprod_le_finprod_of_nonneg hfs hgs hf' h')
    (finprod_nonneg hf') (Finset.prod_nonneg fun v _ ↦ pow_nonneg ((hf v).trans (h v)) _)

theorem one_le_mulRatioProd (hs : s.Nonempty) (h0 : 0 ∉ s) : 1 ≤ mulRatioProd s := by
  have h := prod_places_le (f := fun _ ↦ 1) (f' := fun _ ↦ 1)
    (g := fun v : InfinitePlace K ↦ localRatio s fun x ↦ v x)
    (g' := fun v : FinitePlace K ↦ localRatio s fun x ↦ v x) (fun _ ↦ zero_le_one)
    (fun _ ↦ zero_le_one) (by simp [Function.HasFiniteMulSupport])
    (hasFiniteMulSupport_localRatio hs h0) (fun v ↦ one_le_localRatio hs h0 v.1)
    (fun v ↦ one_le_localRatio hs h0 v.1)
  rw [mulRatioProd]
  simpa using h

/-- **EF13 (10.2)**, in the form used for Lemma 18.1: `∏_v M_v / m_v ≤ (∏_v M_v)^{#s}`, by the
product formula for `∏_{θ ∈ s} θ`. -/
theorem mulRatioProd_le (hs : s.Nonempty) (h0 : 0 ∉ s) :
    mulRatioProd s ≤ mulSupProd s ^ #s := by
  set P := ∏ e ∈ s, e
  have hP : P ≠ 0 := prod_ne_zero_iff.2 fun e he h ↦ h0 (h ▸ he)
  have hprod := prod_abs_eq_one (inv_ne_zero hP)
  have hM := hasFiniteMulSupport_iSup_finset hs h0
  have hPs := FinitePlace.hasFiniteMulSupport (inv_ne_zero hP)
  have hMp : (fun v : FinitePlace K ↦ (⨆ e : s, v e) ^ #s).HasFiniteMulSupport :=
    hM.subset fun v hv h ↦ hv (by simp only [h, one_pow])
  have hMP : (fun v : FinitePlace K ↦ (⨆ e : s, v e) ^ #s * v P⁻¹).HasFiniteMulSupport :=
    (hMp.union hPs).subset (Function.mulSupport_mul _ _)
  calc mulRatioProd s
      ≤ (∏ v : InfinitePlace K, ((⨆ e : s, v e) ^ #s * v P⁻¹) ^ v.mult) *
          ∏ᶠ v : FinitePlace K, (⨆ e : s, v e) ^ #s * v P⁻¹ :=
        prod_places_le (fun v ↦ localRatio_nonneg v.1) (fun v ↦ localRatio_nonneg v.1)
          (hasFiniteMulSupport_localRatio hs h0)
          hMP (fun v ↦ localRatio_le hs h0 v.1)
          (fun v ↦ localRatio_le hs h0 v.1)
    _ = mulSupProd s ^ #s * ((∏ w : InfinitePlace K, w P⁻¹ ^ w.mult) *
          ∏ᶠ w : FinitePlace K, w P⁻¹) := by
        have h1 : ∏ v : InfinitePlace K, ((⨆ e : s, v e) ^ #s * v P⁻¹) ^ v.mult =
            (∏ v : InfinitePlace K, (⨆ e : s, v e) ^ v.mult) ^ #s *
              ∏ v : InfinitePlace K, v P⁻¹ ^ v.mult := by
          rw [← prod_pow, ← prod_mul_distrib]
          refine prod_congr rfl fun v _ ↦ ?_
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm #s]
        rw [mulSupProd, h1, finprod_mul_distrib hMp hPs,
          ← finprod_pow hM]
        ring
    _ = mulSupProd s ^ #s := by rw [hprod, mul_one]

/-- `v ↦ max_t ‖c_t‖_v` is `1` at almost all finite places. -/
theorem hasFiniteMulSupport_iSup_apply {τ : Type*} [Finite τ] {c : τ → K} (hc : c ≠ 0) :
    (fun v : FinitePlace K ↦ ⨆ t, v (c t)).HasFiniteMulSupport := by
  refine (Set.finite_iUnion fun j : {j // c j ≠ 0} ↦
    FinitePlace.hasFiniteMulSupport j.2).subset fun v hv ↦ ?_
  by_contra hni
  simp only [Set.mem_iUnion, not_exists, Function.mem_mulSupport, not_not] at hni
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hc
  have : Nonempty τ := ⟨i⟩
  refine hv (le_antisymm (ciSup_le fun j ↦ ?_) ?_)
  · rcases eq_or_ne (c j) 0 with h | h
    · rw [h, map_zero]
      exact zero_le_one
    · exact (hni ⟨j, h⟩).le
  · exact (hni ⟨i, hi⟩).symm.le.trans (Finite.le_ciSup_of_le (f := fun t ↦ v (c t)) i le_rfl)

end Ratio

/-! ### The minors `θ` (EF13 Lemmas 10.1, 10.2) -/

namespace FormSystem

variable {n : ℕ} (L : FormSystem K (Fin n))

/-- **`L` contains `X_1, …, X_n`** (EF13 §10): every coordinate form is a form of `L`. -/
def HasUnitForms : Prop := ∀ i, (Pi.single i 1 : Fin n → K) ∈ L.forms

open scoped Classical in
/-- **The nonzero minors `θ` of EF13 (18.1)**: `det(L_{i_l}(g_j))_{l,j}` over the `k`-tuples
`L_{i_1}, …, L_{i_k}` of forms of `L`, `g_1, …, g_k` the columns of `G`. -/
noncomputable def minorSet {k : ℕ} (G : Matrix (Fin n) (Fin k) K) : Finset K :=
  ((Fintype.piFinset fun _ : Fin k ↦ L.forms).image fun B ↦ (Matrix.of B * G).det).filter (· ≠ 0)

variable {k : ℕ} {G : Matrix (Fin n) (Fin k) K}

theorem zero_notMem_minorSet : 0 ∉ L.minorSet G := by
  classical
  intro h
  exact (mem_filter.1 h).2 rfl

theorem det_mem_minorSet {B : Fin k → Fin n → K} (hB : ∀ s, B s ∈ L.forms)
    (h : (Matrix.of B * G).det ≠ 0) : (Matrix.of B * G).det ∈ L.minorSet G := by
  classical
  exact mem_filter.2 ⟨mem_image.2 ⟨B, Fintype.mem_piFinset.2 hB, rfl⟩, h⟩

theorem exists_of_mem_minorSet {θ : K} (h : θ ∈ L.minorSet G) :
    ∃ B : Fin k → Fin n → K, (∀ s, B s ∈ L.forms) ∧ (Matrix.of B * G).det = θ := by
  classical
  obtain ⟨B, hB, rfl⟩ := mem_image.1 (mem_filter.1 h).1
  exact ⟨B, Fintype.mem_piFinset.1 hB, rfl⟩

theorem minorSet_nonempty (hG : LinearIndependent K G.col) : (L.minorSet G).Nonempty := by
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hA : Function.Injective (L.arch v₀).mulVec := Matrix.mulVec_injective_iff_isUnit.2
    ((Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit (L.arch_det_ne_zero v₀)))
  have hM : Function.Injective (L.arch v₀ * G).mulVec := fun x y hxy ↦ by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hxy
    exact Matrix.mulVec_injective_iff.2 hG (hA hxy)
  obtain ⟨σ, hσ⟩ := Matrix.exists_submatrix_det_ne_zero _ hM
  rw [Splitting.submatrix_mul_left] at hσ
  exact ⟨_, L.det_mem_minorSet (B := fun s ↦ L.arch v₀ (σ s)) (fun s ↦ L.arch_mem_forms v₀ _) hσ⟩

/-- **EF13 Lemma 10.1**: if `L` contains `X_1, …, X_n`, every maximal minor of `k` forms of `L`
is a determinant of `n` forms of `L`. -/
theorem plucker_mem_detSet (hL : L.HasUnitForms) {B : Fin k → Fin n → K}
    (hB : ∀ s, B s ∈ L.forms) (J : Set.powersetCard (Fin n) k) : plucker k B J ∈ L.detSet := by
  classical
  have hJ := Set.powersetCard.card_eq J
  have hc : #(J : Finset (Fin n))ᶜ = n - k := by rw [card_compl, Fintype.card_fin, hJ]
  set σ := finSumEquivOfFinset hJ hc
  set N : Fin n → Fin n → K := fun i ↦ Sum.elim B (fun t ↦ Pi.single (σ (Sum.inr t)) 1) (σ.symm i)
  have hN : N ∈ Fintype.piFinset fun _ ↦ L.forms := Fintype.mem_piFinset.2 fun i ↦ by
    simp only [N]
    rcases σ.symm i with s | t
    · exact hB s
    · exact hL _
  have hblk : (Matrix.of N).submatrix σ σ = fromBlocks
      ((Matrix.of B).submatrix id ((J : Finset (Fin n)).orderEmbOfFin hJ))
      (Matrix.of fun s t ↦ B s (σ (Sum.inr t))) 0 1 := by
    ext (s | t) (s' | t')
    · simp only [N, submatrix_apply, of_apply, Equiv.symm_apply_apply, Sum.elim_inl,
        fromBlocks_apply₁₁, id]
      rfl
    · simp [N]
    · simp only [submatrix_apply, of_apply, N, Equiv.symm_apply_apply, Sum.elim_inr,
        fromBlocks_apply₂₁, Matrix.zero_apply]
      exact Pi.single_eq_of_ne (fun h ↦ by simpa using σ.injective h) _
    · simp only [submatrix_apply, of_apply, N, Equiv.symm_apply_apply, Sum.elim_inr,
        fromBlocks_apply₂₂, one_apply, Pi.single_apply, σ.injective.eq_iff, Sum.inr.injEq,
        eq_comm (a := t)]
  have hdet : (Matrix.of N).det = plucker k B J := by
    rw [← det_submatrix_equiv_self σ, hblk, det_fromBlocks_zero₂₁, det_one, mul_one,
      ← Matrix.plucker_row_eq_det_submatrix]
    rfl
  exact hdet ▸ mem_image.2 ⟨N, hN, rfl⟩

/-- **EF13 Lemma 10.1** for the coefficients: if `L` contains `X_1, …, X_n`, every coefficient of
a form of `L` is a determinant of `n` forms of `L`. -/
theorem apply_mem_detSet (hL : L.HasUnitForms) {f : Fin n → K} (hf : f ∈ L.forms) (j : Fin n) :
    f j ∈ L.detSet := by
  have h := L.plucker_mem_detSet hL (B := ![f]) (fun _ ↦ by simpa using hf)
    (Set.powersetCard.ofFinEmbEquiv (OrderEmbedding.ofStrictMono (fun _ : Fin 1 ↦ j)
      fun a b h ↦ absurd h (by rw [Subsingleton.elim a b]; exact lt_irrefl b)))
  rw [exteriorPower.plucker_apply] at h
  simp only [Equiv.symm_apply_apply, det_unique, Fin.default_eq_zero] at h
  exact h

theorem rpow_mult_div_two {x : ℝ} (hx : 0 ≤ x) (m : ℕ) : x ^ ((m : ℝ) / 2) = √x ^ m := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  ring_nf

/-- The Arakelov height of a form of a system containing `X_1, …, X_n` is at most
`√n^{[K:ℚ]} H_L`, relative to `K` (EF13 §18: `H₂(L_i) ≤ √n H_L`). -/
theorem arakelovFormHeight_le (hn : 0 < n) (hL : L.HasUnitForms) :
    L.arakelovFormHeight ≤ √n ^ finrank ℚ K * L.mulFormHeight := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hH := L.one_le_mulFormHeight
  have hsn : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.2 (by exact_mod_cast hn)
  have hR : 1 ≤ √n ^ finrank ℚ K * L.mulFormHeight :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hsn) hH
  refine Real.iSup_le (fun f ↦ ?_) (zero_le_one.trans hR)
  by_cases hf : (f : Fin n → K) = 0
  · rw [hf, NumberField.arakelovMulHeight_zero]
    exact hR
  rw [NumberField.arakelovMulHeight_eq hf]
  have hmem : ∀ j, (f : Fin n → K) j ∈ L.detSet := L.apply_mem_detSet hL f.2
  have harch : ∀ v : InfinitePlace K,
      √(∑ i, v ((f : Fin n → K) i) ^ 2) ≤ √n * ⨆ e : L.detSet, v e := fun v ↦ by
    have hD : 0 ≤ ⨆ e : L.detSet, v e := L.iSup_detSet_nonneg v.1
    rw [← Real.sqrt_sq hD, ← Real.sqrt_mul (Nat.cast_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, v ((f : Fin n → K) i) ^ 2 ≤ ∑ _i : Fin n, (⨆ e : L.detSet, v e) ^ 2 :=
          sum_le_sum fun i _ ↦ pow_le_pow_left₀ (apply_nonneg _ _)
            (L.le_iSup_detSet _ (hmem i)) 2
      _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hfin : ∀ v : FinitePlace K, (⨆ i, v ((f : Fin n → K) i)) ≤ ⨆ e : L.detSet, v e :=
    fun v ↦ ciSup_le fun i ↦ L.le_iSup_detSet _ (hmem i)
  have h := prod_places_le (fun v ↦ Real.sqrt_nonneg _)
    (fun v ↦ Real.iSup_nonneg fun i ↦ apply_nonneg _ _)
    (hasFiniteMulSupport_iSup_apply hf) L.hasFiniteMulSupport_iSup_detSet harch hfin
  simp only [← rpow_mult_div_two (sum_nonneg fun i _ ↦ sq_nonneg _)] at h
  refine h.trans_eq ?_
  rw [mulFormHeight]
  simp only [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  ring

open scoped Classical in
/-- **EF13 Lemma 10.2, (10.1)**, relative to `K`: if `L` contains `X_1, …, X_n` and the columns
of `G` are independent, `∏_v max_θ ‖θ‖_v ≤ C(n,k)^{[K:ℚ]} H_L H₂(V)`, `V` the span of the
columns. -/
theorem mulSupProd_minorSet_le (hL : L.HasUnitForms) (hk : k ≤ n)
    (hG : LinearIndependent K G.col) :
    mulSupProd (L.minorSet G) ≤ (n.choose k : ℝ) ^ finrank ℚ K * L.mulFormHeight *
      (Submodule.span K (Set.range G.col)).arakelovMulHeight := by
  set p := plucker k G.col
  have hp : p ≠ 0 := exteriorPower.plucker_ne_zero hG
  have hJ : Fintype.card (Set.powersetCard (Fin n) k) = n.choose k := by
    rw [← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hJne : Nonempty (Set.powersetCard (Fin n) k) :=
    Fintype.card_pos_iff.1 (hJ ▸ Nat.choose_pos hk)
  have hθ : ∀ θ ∈ L.minorSet G, ∃ B : Fin k → Fin n → K, (∀ s, B s ∈ L.forms) ∧
      θ = ∑ J, plucker k B J * p J := fun θ hθ ↦ by
    obtain ⟨B, hB, rfl⟩ := L.exists_of_mem_minorSet hθ
    exact ⟨B, hB, Matrix.det_mul_eq_sum_plucker _ _⟩
  have harch : ∀ v : InfinitePlace K, (⨆ e : L.minorSet G, v e) ≤
      n.choose k * (⨆ e : L.detSet, v e) * √(∑ J, v (p J) ^ 2) := fun v ↦ by
    have hD : 0 ≤ ⨆ e : L.detSet, v e := L.iSup_detSet_nonneg v.1
    refine Real.iSup_le (fun θ ↦ ?_) (by positivity)
    obtain ⟨B, hB, hθB⟩ := hθ θ θ.2
    rw [hθB]
    have hle : ∀ J, v (p J) ≤ √(∑ J, v (p J) ^ 2) := fun J ↦
      Real.le_sqrt_of_sq_le (single_le_sum (f := fun J ↦ v (p J) ^ 2)
        (fun _ _ ↦ sq_nonneg _) (mem_univ J))
    calc v (∑ J, plucker k B J * p J) ≤ ∑ J, v (plucker k B J * p J) := AbsoluteValue.sum_le _ _ _
      _ ≤ ∑ _J : Set.powersetCard (Fin n) k, (⨆ e : L.detSet, v e) * √(∑ J, v (p J) ^ 2) :=
          sum_le_sum fun J _ ↦ by
            rw [map_mul]
            exact mul_le_mul (L.le_iSup_detSet _ (L.plucker_mem_detSet hL hB J)) (hle J)
              (apply_nonneg _ _) hD
      _ = _ := by rw [sum_const, card_univ, hJ, nsmul_eq_mul, mul_assoc]
  have hfin : ∀ v : FinitePlace K, (⨆ e : L.minorSet G, v e) ≤
      (⨆ e : L.detSet, v e) * ⨆ J, v (p J) := fun v ↦ by
    have hD : 0 ≤ ⨆ e : L.detSet, v e := L.iSup_detSet_nonneg v.1
    refine Real.iSup_le (fun θ ↦ ?_)
      (mul_nonneg hD (Real.iSup_nonneg fun _ ↦ apply_nonneg _ _))
    obtain ⟨B, hB, hθB⟩ := hθ θ θ.2
    rw [hθB]
    have hna : IsNonarchimedean (v ·) := FinitePlace.add_le v
    obtain ⟨J, -, hJ'⟩ := hna.finset_image_add_of_nonempty
      (fun J ↦ plucker k B J * p J) univ_nonempty
    refine hJ'.trans ?_
    rw [map_mul]
    exact mul_le_mul (L.le_iSup_detSet _ (L.plucker_mem_detSet hL hB J))
      (Finite.le_ciSup_of_le (f := fun J ↦ v (p J)) J le_rfl) (apply_nonneg _ _) hD
  have hMf := hasFiniteMulSupport_iSup_apply hp
  have hDf := L.hasFiniteMulSupport_iSup_detSet
  have h := prod_places_le (fun v ↦ Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)
    (fun v ↦ Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)
    (hasFiniteMulSupport_iSup_finset (L.minorSet_nonempty hG) L.zero_notMem_minorSet)
    ((hDf.union hMf).subset (Function.mulSupport_mul _ _)) harch hfin
  refine h.trans_eq ?_
  rw [Submodule.arakelovMulHeight_span_range hG, NumberField.arakelovMulHeight_eq hp,
    mulFormHeight, finprod_mul_distrib hDf hMf]
  simp only [← rpow_mult_div_two (sum_nonneg fun i _ ↦ sq_nonneg _), mul_pow, prod_mul_distrib,
    prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  ring

/-! ### Change of coordinates -/

section Comp

variable (P : Matrix (Fin n) (Fin n) K) (hP : P.det ≠ 0)

omit [NumberField K] in
theorem row_mul_apply (A : Matrix (Fin n) (Fin n) K) (i : Fin n) : (A * P) i = A i ᵥ* P := by
  funext j
  simp [Matrix.mul_apply, vecMul, dotProduct]

theorem exists_of_mem_forms_comp {f : Fin n → K} (hf : f ∈ (L.comp P hP).forms) :
    ∃ g ∈ L.forms, f = g ᵥ* P := by
  rcases (L.comp P hP).finite_formSet.mem_toFinset.1 hf with ⟨v, i, rfl⟩ | ⟨v, i, rfl⟩
  · exact ⟨_, L.arch_mem_forms v i, row_mul_apply P (L.arch v) i⟩
  · exact ⟨_, L.fin_mem_forms v i, row_mul_apply P (L.fin v) i⟩

theorem vecMul_mem_forms_comp {g : Fin n → K} (hg : g ∈ L.forms) :
    g ᵥ* P ∈ (L.comp P hP).forms := by
  rcases L.finite_formSet.mem_toFinset.1 hg with ⟨v, i, rfl⟩ | ⟨v, i, rfl⟩
  · rw [← row_mul_apply]
    exact (L.comp P hP).arch_mem_forms v i
  · rw [← row_mul_apply]
    exact (L.comp P hP).fin_mem_forms v i

omit [NumberField K] in
theorem of_vecMul {k : ℕ} (B : Fin k → Fin n → K) :
    Matrix.of (fun s ↦ B s ᵥ* P) = Matrix.of B * P := by
  ext s j
  simp [Matrix.mul_apply, vecMul, dotProduct]

/-- `H_{L ∘ P} ≤ H_L` (in fact `=`, EF13 Lemma 7.3 (iv)), by the product formula for `det P`. -/
theorem mulFormHeight_comp_le : (L.comp P hP).mulFormHeight ≤ L.mulFormHeight := by
  classical
  have hdet : ∀ e ∈ (L.comp P hP).detSet, ∃ d ∈ L.detSet, e = d * P.det := fun e he ↦ by
    obtain ⟨M, hM, rfl⟩ := mem_image.1 he
    have hM' : ∀ i, ∃ g ∈ L.forms, M i = g ᵥ* P := fun i ↦
      L.exists_of_mem_forms_comp P hP (Fintype.mem_piFinset.1 hM i)
    choose g hg hgM using hM'
    refine ⟨(Matrix.of g).det, mem_image.2 ⟨g, Fintype.mem_piFinset.2 hg, rfl⟩, ?_⟩
    rw [show M = fun i ↦ g i ᵥ* P from funext hgM, of_vecMul, det_mul]
  have hloc : ∀ f : AbsoluteValue K ℝ, (⨆ e : (L.comp P hP).detSet, f e) ≤
      (⨆ e : L.detSet, f e) * f P.det := fun f ↦ by
    refine Real.iSup_le (fun e ↦ ?_) (mul_nonneg (L.iSup_detSet_nonneg f) (apply_nonneg _ _))
    obtain ⟨d, hd, hde⟩ := hdet e e.2
    rw [hde, map_mul]
    exact mul_le_mul_of_nonneg_right (L.le_iSup_detSet _ hd) (apply_nonneg _ _)
  have hDf := L.hasFiniteMulSupport_iSup_detSet
  have hPf := FinitePlace.hasFiniteMulSupport hP
  have h := prod_places_le (f := fun v : InfinitePlace K ↦ ⨆ e : (L.comp P hP).detSet, v e)
    (g := fun v : InfinitePlace K ↦ (⨆ e : L.detSet, v e) * v P.det)
    (f' := fun v : FinitePlace K ↦ ⨆ e : (L.comp P hP).detSet, v e)
    (g' := fun v : FinitePlace K ↦ (⨆ e : L.detSet, v e) * v P.det)
    (fun v ↦ (L.comp P hP).iSup_detSet_nonneg v.1)
    (fun v ↦ (L.comp P hP).iSup_detSet_nonneg v.1)
    (L.comp P hP).hasFiniteMulSupport_iSup_detSet
    ((hDf.union hPf).subset (Function.mulSupport_mul _ _)) (fun v ↦ hloc v.1) fun v ↦ hloc v.1
  refine h.trans_eq ?_
  rw [mulFormHeight, finprod_mul_distrib hDf hPf]
  simp only [mul_pow, prod_mul_distrib]
  have := prod_abs_eq_one hP
  calc _ = ((∏ v : InfinitePlace K, (⨆ e : L.detSet, v e) ^ v.mult) *
        ∏ᶠ v : FinitePlace K, ⨆ e : L.detSet, v e) *
        ((∏ w : InfinitePlace K, w P.det ^ w.mult) * ∏ᶠ w : FinitePlace K, w P.det) := by ring
    _ = _ := by rw [this, mul_one]

theorem minorSet_comp {k : ℕ} (G : Matrix (Fin n) (Fin k) K) :
    (L.comp P hP).minorSet (P⁻¹ * G) = L.minorSet G := by
  have hPP : P * P⁻¹ = 1 := mul_nonsing_inv P (Ne.isUnit hP)
  have hmul : ∀ B : Fin k → Fin n → K,
      Matrix.of (fun s ↦ B s ᵥ* P) * (P⁻¹ * G) = Matrix.of B * G := fun B ↦ by
    rw [of_vecMul, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP, Matrix.one_mul]
  ext θ
  constructor
  · intro h
    obtain ⟨B', hB', hθ⟩ := (L.comp P hP).exists_of_mem_minorSet h
    have hB'' : ∀ s, ∃ g ∈ L.forms, B' s = g ᵥ* P := fun s ↦
      L.exists_of_mem_forms_comp P hP (hB' s)
    choose g hg hgB using hB''
    rw [show B' = fun s ↦ g s ᵥ* P from funext hgB, hmul] at hθ
    have hθ0 : θ ≠ 0 := fun h0 ↦ (L.comp P hP).zero_notMem_minorSet (h0 ▸ h)
    rw [← hθ]
    exact L.det_mem_minorSet hg (hθ ▸ hθ0)
  · intro h
    obtain ⟨B, hB, hθ⟩ := L.exists_of_mem_minorSet h
    have := (L.comp P hP).det_mem_minorSet (G := P⁻¹ * G) (B := fun s ↦ B s ᵥ* P)
      (fun s ↦ L.vecMul_mem_forms_comp P hP (hB s))
      (by rw [hmul, hθ]; exact fun h0 ↦ L.zero_notMem_minorSet (h0 ▸ h))
    rwa [hmul, hθ] at this

section Filtration

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

omit [NumberField K] in
theorem map_mulVec_extendLin (M : Matrix (Fin n) (Fin n) K) (y : Fin n → K) :
    M.map (algebraMap K Ω) *ᵥ Submodule.extendLin Ω y = Submodule.extendLin Ω (M *ᵥ y) := by
  funext i
  simp [Submodule.extendLin_apply, mulVec, dotProduct]

omit [NumberField K] in
theorem symm_compEquiv_extendLin (y : Fin n → K) :
    (compEquiv (Ω := Ω) P hP).symm (Submodule.extendLin Ω y) =
      Submodule.extendLin Ω (P⁻¹ *ᵥ y) := by
  rw [LinearEquiv.symm_apply_eq, compEquiv_apply, map_mulVec_extendLin, mulVec_mulVec,
    mul_nonsing_inv P (Ne.isUnit hP), one_mulVec]

omit [NumberField K] in
theorem col_mul_eq {k : ℕ} (M : Matrix (Fin n) (Fin n) K) (G : Matrix (Fin n) (Fin k) K)
    (j : Fin k) : (M * G).col j = M *ᵥ G.col j := by
  funext i
  simp [Matrix.mul_apply, mulVec, dotProduct]

omit [NumberField K] in
/-- The columns of `P⁻¹ G` span `P⁻¹ (V ⊗ Ω)`. -/
theorem extendPi_span_col_inv_mul {k : ℕ} (G : Matrix (Fin n) (Fin k) K) :
    (Submodule.span K (Set.range (P⁻¹ * G).col)).extendPi Ω =
      ((Submodule.span K (Set.range G.col)).extendPi Ω).map
        (compEquiv (Ω := Ω) P hP).symm.toLinearMap := by
  rw [Submodule.extendPi_span, Submodule.extendPi_span, Submodule.map_span]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, LinearEquiv.coe_coe,
    symm_compEquiv_extendLin, col_mul_eq]

omit [NumberField K] in
include hP in
theorem linearIndependent_col_inv_mul {k : ℕ} {G : Matrix (Fin n) (Fin k) K}
    (hG : LinearIndependent K G.col) : LinearIndependent K (P⁻¹ * G).col := by
  rw [← Matrix.mulVec_injective_iff] at hG ⊢
  have hP' : Function.Injective P⁻¹.mulVec := Matrix.mulVec_injective_iff_isUnit.2
    ((Matrix.isUnit_iff_isUnit_det _).2
      (by rw [det_nonsing_inv, Ring.inverse_eq_inv']; exact (Ne.isUnit hP).inv))
  intro x y hxy
  rw [← mulVec_mulVec, ← mulVec_mulVec] at hxy
  exact hG (hP' hxy)

/-- The filtration of `L ∘ P` is `P⁻¹` applied to that of `L` (EF13 Lemma 7.3 (iii)). -/
theorem isWeightFiltration_comp (c : FormExponent K (Fin n)) {r : ℕ}
    {T : ℕ → Submodule Ω (Fin n → Ω)}
    (hT : Submodule.IsWeightFiltration (L.subspaceWeight c) ⊤ r T) :
    Submodule.IsWeightFiltration ((L.comp P hP).subspaceWeight c) ⊤ r
      fun l ↦ (T l).map (compEquiv (Ω := Ω) P hP).symm.toLinearMap := by
  set E := Submodule.orderIsoMapComap (compEquiv (Ω := Ω) P hP).symm
  have hE : ∀ U, finrank Ω ↥(E U) = finrank Ω U := fun U ↦
    (compEquiv P hP).symm.finrank_map_eq U
  have hw : ∀ U, (L.comp P hP).subspaceWeight c (E U) = L.subspaceWeight c U := fun U ↦ by
    rw [subspaceWeight_comp]
    congr 1
    ext x
    simp [E]
  have htop : E ⊤ = ⊤ := by simp [E]
  have := hT.orderIso E hE hw
  rw [htop] at this
  exact this

end Filtration

theorem card_minorSet_le {k : ℕ} (G : Matrix (Fin n) (Fin k) K) :
    #(L.minorSet G) ≤ #L.forms ^ k := by
  classical
  refine (card_filter_le _ _).trans (card_image_le.trans ?_)
  rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]

theorem le_card_forms : n ≤ #L.forms := by
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hinj : Function.Injective (L.arch v₀) :=
    (linearIndependent_rows_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2
      (Ne.isUnit (L.arch_det_ne_zero v₀)))).injective
  have := card_le_card_of_injOn (s := univ) (L.arch v₀) (fun i _ ↦ L.arch_mem_forms v₀ i)
    hinj.injOn
  simpa using this

theorem hasUnitForms_comp_inv (v₀ : InfinitePlace K) (hP : (L.arch v₀)⁻¹.det ≠ 0) :
    (L.comp (L.arch v₀)⁻¹ hP).HasUnitForms := fun i ↦ by
  have h := (L.comp (L.arch v₀)⁻¹ hP).arch_mem_forms v₀ i
  have h1 : (L.comp (L.arch v₀)⁻¹ hP).arch v₀ = 1 :=
    mul_nonsing_inv _ (Ne.isUnit (L.arch_det_ne_zero v₀))
  rw [h1] at h
  convert h using 1
  funext j
  simp [one_apply, Pi.single_apply, eq_comm]

end Comp

/-! ### EF13 Lemma 18.1 -/

section Lemma181

/-- The exponent count of EF13 Lemma 18.1:
`(C(n,k)^d H (√n^d H)^{4ⁿ})^{R^k} ≤ (2^d H)^{(4R)ⁿ}` for `0 < k < n ≤ R` and `H ≥ 1`. -/
theorem minorRatio_pow_le {d n k R : ℕ} {H : ℝ} (hH : 1 ≤ H) (hk0 : 0 < k) (hkn : k < n)
    (hnR : n ≤ R) :
    ((n.choose k : ℝ) ^ d * H * (√n ^ d * H) ^ (4 ^ n)) ^ (R ^ k) ≤
      (2 ^ d * H) ^ ((4 * R) ^ n) := by
  set Y : ℝ := 2 ^ d * H
  have hY : 1 ≤ Y := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hH
  set m := 2 * 4 ^ (n - 1)
  have hm : 1 ≤ m := by
    have := Nat.one_le_pow (n - 1) 4 (by norm_num)
    omega
  have h4 : 4 ^ n = 2 * m := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    simp only [m, Nat.add_sub_cancel, pow_succ]
    ring
  have hc : (n.choose k : ℝ) ^ d ≤ (2 ^ d) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.choose_le_two_pow n k) d
  have hs : (√(n : ℝ) ^ d) ^ (4 ^ n) ≤ (2 ^ d) ^ (n * m) := by
    rw [← pow_mul, h4, mul_comm d, pow_mul, pow_mul √(n : ℝ), Real.sq_sqrt (Nat.cast_nonneg _),
      show ((2 : ℝ) ^ d) ^ (n * m) = (((2 : ℝ) ^ n) ^ m) ^ d by ring]
    gcongr
    exact_mod_cast n.lt_two_pow_self.le
  have hH4 : H ^ (4 ^ n + 1) ≤ H ^ (n * 4 ^ n) := pow_le_pow_right₀ hH (by
    have : 2 * 4 ^ n ≤ n * 4 ^ n := Nat.mul_le_mul_right _ (by omega)
    have : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
    omega)
  have h2 : ((2 : ℝ) ^ d) ^ n * (2 ^ d) ^ (n * m) ≤ (2 ^ d) ^ (n * 4 ^ n) := by
    rw [← pow_add]
    refine pow_le_pow_right₀ (one_le_pow₀ one_le_two) ?_
    rw [h4]
    nlinarith
  have hX : (n.choose k : ℝ) ^ d * H * (√n ^ d * H) ^ (4 ^ n) ≤ Y ^ (n * 4 ^ n) := by
    calc (n.choose k : ℝ) ^ d * H * (√n ^ d * H) ^ (4 ^ n)
        = (n.choose k : ℝ) ^ d * (√n ^ d) ^ (4 ^ n) * H ^ (4 ^ n + 1) := by ring
      _ ≤ (2 ^ d) ^ n * (2 ^ d) ^ (n * m) * H ^ (n * 4 ^ n) := by
          gcongr
      _ ≤ (2 ^ d) ^ (n * 4 ^ n) * H ^ (n * 4 ^ n) :=
          mul_le_mul_of_nonneg_right h2 (pow_nonneg (zero_le_one.trans hH) _)
      _ = Y ^ (n * 4 ^ n) := by rw [mul_pow]
  have hR1 : 1 ≤ R := by omega
  have hexp : n * 4 ^ n * R ^ k ≤ (4 * R) ^ n := by
    have h1 : n * R ^ k ≤ R ^ n :=
      calc n * R ^ k ≤ R * R ^ k := Nat.mul_le_mul_right _ hnR
        _ = R ^ (k + 1) := by ring
        _ ≤ R ^ n := Nat.pow_le_pow_right hR1 (by omega)
    calc n * 4 ^ n * R ^ k = 4 ^ n * (n * R ^ k) := by ring
      _ ≤ 4 ^ n * R ^ n := Nat.mul_le_mul_left _ h1
      _ = (4 * R) ^ n := by ring
  calc _ ≤ (Y ^ (n * 4 ^ n)) ^ (R ^ k) := pow_le_pow_left₀ (by positivity) hX _
    _ = Y ^ (n * 4 ^ n * R ^ k) := (pow_mul _ _ _).symm
    _ ≤ Y ^ ((4 * R) ^ n) := pow_le_pow_right₀ hY hexp

theorem mulSupProd_nonneg (s : Finset K) : 0 ≤ mulSupProd s :=
  mul_nonneg (prod_nonneg fun v _ ↦ pow_nonneg (iSup_finset_nonneg v.1) _)
    (finprod_nonneg fun v ↦ iSup_finset_nonneg v.1)

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]

/-- **EF13 Lemma 18.1**, relative to `K`: let `T_l`, `0 < l < r`, be a member of the filtration of
`(L, c)`, spanned by the independent columns `g_1, …, g_k ∈ Kⁿ` of `G`, and `M_v`, `m_v` the
largest and the smallest `‖θ‖_v` of the nonzero minors `θ = det(L_{i_l}(g_j))`. Then
`∏_v M_v / m_v ≤ (2^{[K:ℚ]} H_L)^{(4R)ⁿ}`, `R` the number of forms of `L` (EF13 states it for
`T = T(L, c)`, the member `T_{r-1}`). The hypothesis `SemistableGap K Ω` (EF13 Theorem 8.1) comes
from Prop. 17.5. -/
theorem mulRatioProd_minorSet_le (hgap : SemistableGap K Ω) (c : FormExponent K (Fin n))
    {r : ℕ} {T : ℕ → Submodule Ω (Fin n → Ω)}
    (hT : Submodule.IsWeightFiltration (L.subspaceWeight c) ⊤ r T) {l : ℕ} (hl0 : 0 < l)
    (hlr : l < r) (hG : LinearIndependent K G.col)
    (hGT : (Submodule.span K (Set.range G.col)).extendPi Ω = T l) :
    mulRatioProd (L.minorSet G) ≤ (2 ^ finrank ℚ K * L.mulFormHeight) ^ ((4 * #L.forms) ^ n) := by
  classical
  -- the dimensions
  have hk : finrank Ω (T l) = k := by
    rw [← hGT, Submodule.finrank_extendPi, finrank_span_eq_card hG, Fintype.card_fin]
  obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
  have hk0 : 0 < k := hk ▸ (Nat.zero_le _).trans_lt
    (Submodule.finrank_lt_finrank_of_lt (hT.lt j (by omega)))
  have hkn : k < n := by
    have h1 := Submodule.finrank_lt_finrank_of_lt (hT.lt (j + 1) hlr)
    have h2 := Submodule.finrank_le (T (j + 1 + 1))
    rw [Module.finrank_fin_fun] at h2
    omega
  -- the change of coordinates making `L` contain `X_1, …, X_n`
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  set P := (L.arch v₀)⁻¹
  have hP : P.det ≠ 0 := by
    rw [det_nonsing_inv, Ring.inverse_eq_inv']
    exact inv_ne_zero (L.arch_det_ne_zero v₀)
  set L' := L.comp P hP
  have hL' : L'.HasUnitForms := L.hasUnitForms_comp_inv v₀ hP
  have hT' := L.isWeightFiltration_comp P hP c hT
  have hV' : (Submodule.span K (Set.range (P⁻¹ * G).col)).extendPi Ω =
      ((T (j + 1)).map (compEquiv (Ω := Ω) P hP).symm.toLinearMap) := by
    rw [extendPi_span_col_inv_mul, hGT]
  have h175 := L'.arakelovMulHeight_le_of_isWeightFiltration hgap c hT' hl0 hlr hV'
  have h102 := L'.mulSupProd_minorSet_le hL' hkn.le (linearIndependent_col_inv_mul P hP hG)
  rw [minorSet_comp] at h102
  -- the heights
  have hH := L.one_le_mulFormHeight
  have hH' : L'.mulFormHeight ≤ L.mulFormHeight := L.mulFormHeight_comp_le P hP
  have hH'0 : 0 ≤ L'.mulFormHeight := zero_le_one.trans L'.one_le_mulFormHeight
  have hF : L'.arakelovFormHeight ≤ √n ^ finrank ℚ K * L.mulFormHeight :=
    (L'.arakelovFormHeight_le (by omega) hL').trans
      (mul_le_mul_of_nonneg_left hH' (by positivity))
  have hF0 : 0 ≤ L'.arakelovFormHeight :=
    Real.iSup_nonneg fun _ ↦ (NumberField.arakelovMulHeight_pos _).le
  have hV0 : 0 ≤ (Submodule.span K (Set.range (P⁻¹ * G).col)).arakelovMulHeight :=
    (Submodule.arakelovMulHeight_pos _).le
  set X : ℝ := (n.choose k : ℝ) ^ finrank ℚ K * L.mulFormHeight *
    (√n ^ finrank ℚ K * L.mulFormHeight) ^ (4 ^ n)
  have hsup : mulSupProd (L.minorSet G) ≤ X := by
    refine h102.trans (mul_le_mul (mul_le_mul_of_nonneg_left hH' (by positivity))
      (h175.trans (pow_le_pow_left₀ hF0 hF _)) hV0 (by positivity))
  have hX : 1 ≤ X := by
    have h1 : (1 : ℝ) ≤ n.choose k := by exact_mod_cast Nat.choose_pos hkn.le
    have h2 : (1 : ℝ) ≤ √n := Real.one_le_sqrt.2 (by exact_mod_cast (by omega : 1 ≤ n))
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ h1) hH)
      (one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ h2) hH))
  calc mulRatioProd (L.minorSet G)
      ≤ mulSupProd (L.minorSet G) ^ #(L.minorSet G) :=
        mulRatioProd_le (L.minorSet_nonempty hG) L.zero_notMem_minorSet
    _ ≤ X ^ #(L.minorSet G) := pow_le_pow_left₀ (mulSupProd_nonneg _) hsup _
    _ ≤ X ^ (#L.forms ^ k) := pow_le_pow_right₀ hX (L.card_minorSet_le G)
    _ ≤ _ := minorRatio_pow_le hH hk0 hkn L.le_card_forms

/-- **EF13 Lemma 18.1**, absolute form: `(∏_v M_v / m_v)^{1/[K:ℚ]} ≤ (2 H_L)^{(4R)ⁿ}`. -/
theorem mulRatioProd_minorSet_rpow_le (hgap : SemistableGap K Ω) (c : FormExponent K (Fin n))
    {r : ℕ} {T : ℕ → Submodule Ω (Fin n → Ω)}
    (hT : Submodule.IsWeightFiltration (L.subspaceWeight c) ⊤ r T) {l : ℕ} (hl0 : 0 < l)
    (hlr : l < r) (hG : LinearIndependent K G.col)
    (hGT : (Submodule.span K (Set.range G.col)).extendPi Ω = T l) :
    mulRatioProd (L.minorSet G) ^ ((finrank ℚ K : ℝ))⁻¹ ≤
      (2 * L.absFormHeight) ^ ((4 * #L.forms) ^ n) := by
  have hd : finrank ℚ K ≠ 0 := Module.finrank_pos.ne'
  have hH0 : 0 ≤ L.mulFormHeight := zero_le_one.trans L.one_le_mulFormHeight
  have h0 : 0 ≤ mulRatioProd (L.minorSet G) :=
    zero_le_one.trans (one_le_mulRatioProd (L.minorSet_nonempty hG) L.zero_notMem_minorSet)
  refine (Real.rpow_le_rpow h0 (L.mulRatioProd_minorSet_le hgap c hT hl0 hlr hG hGT)
    (by positivity)).trans_eq ?_
  have hY : (0 : ℝ) ≤ 2 ^ finrank ℚ K * L.mulFormHeight := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hY, mul_comm (((4 * #L.forms) ^ n : ℕ) : ℝ),
    Real.rpow_mul hY, Real.rpow_natCast, Real.mul_rpow (by positivity) hH0,
    Real.pow_rpow_inv_natCast zero_le_two hd, absFormHeight]

end Lemma181

end FormSystem

end NumberField
