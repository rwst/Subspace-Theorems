/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SubspaceAuxiliary
public import QuantitativeSubspace.FormExteriorPower

/-!
# The joint height of the inverses of the exterior powers (EF13 Lemma 11.5)

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, Lemma 11.5.

EF13's Lemma 11.5 bounds the joint height `H*(Â_1⁻¹, …, Â_s⁻¹)` of the inverses of the distinct
matrices `Â_v` of the exterior power `L̂` by `H_L^{R^n}`. Lemma 13.5 uses it through Siegel's
lemma: one place `w` has to dominate the entries of *all* the inverse matrices at once, whatever
the place `v` they come from. The per-place bound of `QuantitativeSubspace.FormExteriorPower`
(`apply_inv_exteriorPower_arch_le`, `v = w`) is not enough for that.

Here the joint bound is stated in the form the multihomogeneous Siegel lemma of
`DiophantineApproximation.SubspaceAuxiliary` consumes: a *reference tuple* `L.invTuple p`, made of
the entries of all the `((L^{(v)})^{∧p})⁻¹` together with `1`, whose local factor at every
absolute value dominates each matrix (`le_iSup_invTuple`), and whose height is bounded
(`mulHeight_invTuple_le`):

`H(invTuple) ≤ p!^{[K:ℚ]} H_L^{2 p s}`, relative to `K`, `s = #matSet` the number of distinct
matrices `L^{(v)}`.

## Main results

* `NumberField.FormSystem.matSet`: the finitely many matrices `L^{(v)}`.
* `NumberField.FormSystem.apply_inv_compound_le` and `apply_inv_compound_le_of_isNonarchimedean`:
  the local bounds of Lemma 11.5 at any absolute value `w`, for any of the matrices.
* `NumberField.FormSystem.mulHeight_invTuple_le`: **the joint form of Lemma 11.5.**

## Implementation notes

⚠ **The constant is not EF13's.** EF13 bound `max_v ‖det L^{(v)}‖_w⁻¹` through Lemma 10.1 and
get the exponent `1 + N' (C(r, n) - 1) ≤ R^n`. Here every inverse determinant is cleared with the
product `δ = ∏_{B ∈ matSet} det B`: `1 / |det B|_w ≤ m_w^{s-1} / |δ|_w` with
`m_w = max_{e ∈ detSet} |e|_w`, and `H(δ) ≤ H_L^s`. This gives `p!^{[K:ℚ]} H_L^{2ps}`, with
`s ≤ R^n` (ordered `n`-tuples of forms). The factor `p!` at the infinite places is Hadamard's,
which EF13 hide in their `‖·‖_{v,1}`-normalization.
-/

@[expose] public section

open Finset Module Matrix
open exteriorPower (plucker plucker_apply)

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [IsDomain R]

/-- **The ultrametric Hadamard bound** at a nonarchimedean absolute value: if the entries of the
`j`-th column are at most `b j`, the determinant is at most `∏_j b j`. -/
theorem abv_det_le_of_col_of_isNonarchimedean {f : AbsoluteValue R ℝ} (hf : IsNonarchimedean f)
    (M : Matrix n n R) {b : n → ℝ} (hb : ∀ i j, f (M i j) ≤ b j) : f M.det ≤ ∏ j, b j := by
  have hle (σ : Equiv.Perm n) : f (Equiv.Perm.sign σ • ∏ i, M (σ i) i) ≤ ∏ j, b j := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    · simp only [h, Units.smul_def, one_smul, Units.val_neg, Units.val_one, neg_smul,
        AbsoluteValue.map_neg, map_prod]
      exact prod_le_prod₀ (fun _ _ ↦ apply_nonneg _ _) fun i _ ↦ hb _ _
  rw [det_apply]
  exact (hf.apply_sum_le_sup univ_nonempty).trans (Finset.sup'_le _ _ fun σ _ ↦ hle σ)

end Matrix

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]

namespace FormSystem

variable (L : FormSystem K ι)

/-- **The matrices `L^{(v)}`** of the system, over all places: a finite set (EF13's
`A_1, …, A_s`). -/
noncomputable def matSet : Finset (Matrix ι ι K) :=
  ((Set.finite_range L.arch).union L.finite_range_fin).toFinset

theorem arch_mem_matSet (v : InfinitePlace K) : L.arch v ∈ L.matSet := by
  simp [matSet]

theorem fin_mem_matSet (v : FinitePlace K) : L.fin v ∈ L.matSet := by
  simp [matSet]

variable {L}

theorem mem_forms_of_mem_matSet {B : Matrix ι ι K} (hB : B ∈ L.matSet) (i : ι) :
    B i ∈ L.forms := by
  simp only [matSet, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_range] at hB
  rcases hB with ⟨v, rfl⟩ | ⟨v, rfl⟩
  exacts [L.arch_mem_forms v i, L.fin_mem_forms v i]

open scoped Classical in
theorem det_mem_detSet_of_mem_matSet {B : Matrix ι ι K} (hB : B ∈ L.matSet) :
    B.det ∈ L.detSet :=
  Finset.mem_image.mpr ⟨B, Fintype.mem_piFinset.mpr (mem_forms_of_mem_matSet hB), rfl⟩

theorem det_ne_zero_of_mem_matSet {B : Matrix ι ι K} (hB : B ∈ L.matSet) : B.det ≠ 0 := by
  simp only [matSet, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_range] at hB
  rcases hB with ⟨v, rfl⟩ | ⟨v, rfl⟩
  exacts [L.arch_det_ne_zero v, L.fin_det_ne_zero v]

variable (L)

theorem matSet_nonempty : L.matSet.Nonempty :=
  ⟨_, L.arch_mem_matSet (Classical.arbitrary _)⟩

/-- If the coordinate forms belong to the system, `1 ∈ detSet`. -/
theorem one_mem_detSet (h1 : ∀ i, (1 : Matrix ι ι K) i ∈ L.forms) : (1 : K) ∈ L.detSet := by
  classical
  exact Finset.mem_image.mpr ⟨fun i ↦ (1 : Matrix ι ι K) i, Fintype.mem_piFinset.mpr h1,
    Matrix.det_one⟩

variable {L}

/-- The local factor `max_{e ∈ detSet} |e|_w` is at least `1` once `1 ∈ detSet`. -/
theorem one_le_iSup_detSet (h1 : ∀ i, (1 : Matrix ι ι K) i ∈ L.forms) (w : AbsoluteValue K ℝ) :
    1 ≤ ⨆ e : L.detSet, w e := by
  simpa using L.le_iSup_detSet w (L.one_mem_detSet h1)

/-! ### The local bounds of Lemma 11.5 at any absolute value -/

/-- **EF13 Lemma 11.5, local form, archimedean type**: at any absolute value `w`, the entries of
`(B^{∧p})⁻¹` for `B ∈ matSet` are at most `p! (max_{e ∈ detSet} |e|_w / |det B|_w)^p`. -/
theorem apply_inv_compound_le (h1 : ∀ i, (1 : Matrix ι ι K) i ∈ L.forms) {B : Matrix ι ι K}
    (hB : B ∈ L.matSet) (w : AbsoluteValue K ℝ) (p : ℕ) (s t : Set.powersetCard ι p) :
    w ((B.compound p)⁻¹ s t) ≤ p.factorial * ((⨆ e : L.detSet, w e) / w B.det) ^ p := by
  rw [inv_compound p (det_ne_zero_of_mem_matSet hB), compound_apply, plucker_apply]
  refine (abv_det_le_of_col w _ (b := fun _ ↦ (⨆ e : L.detSet, w e) / w B.det)
    fun r q ↦ apply_inv_le w h1 (mem_forms_of_mem_matSet hB) _ _).trans_eq ?_
  simp [prod_const, div_pow]

/-- **EF13 Lemma 11.5, local form, nonarchimedean type**: at a nonarchimedean absolute value the
factor `p!` drops out. -/
theorem apply_inv_compound_le_of_isNonarchimedean (h1 : ∀ i, (1 : Matrix ι ι K) i ∈ L.forms)
    {B : Matrix ι ι K} (hB : B ∈ L.matSet) {w : AbsoluteValue K ℝ} (hw : IsNonarchimedean w)
    (p : ℕ) (s t : Set.powersetCard ι p) :
    w ((B.compound p)⁻¹ s t) ≤ ((⨆ e : L.detSet, w e) / w B.det) ^ p := by
  rw [inv_compound p (det_ne_zero_of_mem_matSet hB), compound_apply, plucker_apply]
  refine (abv_det_le_of_col_of_isNonarchimedean hw _
    (b := fun _ ↦ (⨆ e : L.detSet, w e) / w B.det)
    fun r q ↦ apply_inv_le w h1 (mem_forms_of_mem_matSet hB) _ _).trans_eq ?_
  simp [prod_const, div_pow]

variable (L)

/-- The product `δ = ∏_{B ∈ matSet} det B` that clears all the inverse determinants. -/
noncomputable def detProd : K := ∏ B ∈ L.matSet, B.det

theorem detProd_ne_zero : L.detProd ≠ 0 :=
  prod_ne_zero_iff.mpr fun _ hB ↦ det_ne_zero_of_mem_matSet hB

variable {L}

/-- `max_e |e|_w / |det B|_w ≤ max_e |e|_w ^ s / |δ|_w` with `s = #matSet`. -/
theorem iSup_detSet_div_le (h1 : ∀ i, (1 : Matrix ι ι K) i ∈ L.forms) {B : Matrix ι ι K}
    (hB : B ∈ L.matSet) (w : AbsoluteValue K ℝ) :
    (⨆ e : L.detSet, w e) / w B.det ≤
      (⨆ e : L.detSet, w e) ^ #L.matSet * w L.detProd⁻¹ := by
  classical
  set m := ⨆ e : L.detSet, w e
  have hm1 : 1 ≤ m := one_le_iSup_detSet h1 w
  have hdB : 0 < w B.det := w.pos (det_ne_zero_of_mem_matSet hB)
  have hδ : 0 < w L.detProd := w.pos L.detProd_ne_zero
  have hsplit : w L.detProd = w B.det * ∏ B' ∈ L.matSet.erase B, w B'.det := by
    rw [detProd, ← mul_prod_erase _ _ hB, map_mul, map_prod]
  have hle : ∏ B' ∈ L.matSet.erase B, w B'.det ≤ m ^ (#L.matSet - 1) := by
    rw [← card_erase_of_mem hB, ← prod_const]
    exact prod_le_prod₀ (fun _ _ ↦ apply_nonneg _ _) fun B' hB' ↦
      L.le_iSup_detSet w (det_mem_detSet_of_mem_matSet (mem_of_mem_erase hB'))
  have hP : 0 < ∏ B' ∈ L.matSet.erase B, w B'.det :=
    prod_pos fun B' hB' ↦ w.pos (det_ne_zero_of_mem_matSet (mem_of_mem_erase hB'))
  have hcard : #L.matSet = (#L.matSet - 1) + 1 := by
    have := card_pos.mpr ⟨B, hB⟩
    omega
  calc m / w B.det = m * (∏ B' ∈ L.matSet.erase B, w B'.det) / w L.detProd := by
        rw [hsplit, mul_div_mul_right _ _ hP.ne']
    _ ≤ m * m ^ (#L.matSet - 1) / w L.detProd :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle (zero_le_one.trans hm1)) hδ.le
    _ = m ^ #L.matSet * w L.detProd⁻¹ := by
        rw [map_inv₀, ← pow_succ', ← hcard, div_eq_mul_inv]

/-! ### The reference tuple -/

variable (L) in
/-- **The reference tuple of Lemma 11.5**: `1` and the entries of the inverses of the `p`-th
compounds of all the matrices `L^{(v)}`. -/
noncomputable def invTuple (p : ℕ) :
    Option (L.matSet × Set.powersetCard ι p × Set.powersetCard ι p) → K :=
  fun q ↦ q.elim 1 fun q ↦ ((q.1 : Matrix ι ι K).compound p)⁻¹ q.2.1 q.2.2

/-- **The reference tuple dominates every inverse matrix**, at every absolute value: the hypothesis
`hMy` of the multihomogeneous Siegel lemma. -/
theorem le_iSup_invTuple {p : ℕ} {B : Matrix ι ι K} (hB : B ∈ L.matSet)
    (w : AbsoluteValue K ℝ) :
    (⨆ q : Set.powersetCard ι p × Set.powersetCard ι p, w ((B.compound p)⁻¹ q.1 q.2)) ⊔ 1 ≤
      ⨆ s, w (L.invTuple p s) := by
  have hbdd : BddAbove (Set.range fun s ↦ w (L.invTuple p s)) := Finite.bddAbove_range _
  have h1 : 1 ≤ ⨆ s, w (L.invTuple p s) :=
    le_ciSup_of_le hbdd none (by simp [invTuple])
  refine sup_le (Real.iSup_le (fun q ↦ le_ciSup_of_le hbdd (some (⟨B, hB⟩, q)) le_rfl)
    (zero_le_one.trans h1)) h1

theorem invTuple_ne_zero (p : ℕ) : L.invTuple p ≠ 0 := fun h ↦ by
  simpa [invTuple] using congrFun h none

/-- The local factor of `invTuple` at any absolute value, against the local factors of `δ⁻¹ ^ p`
(with `1`) and of `detSet`. -/
theorem iSup_invTuple_le (h1 : ∀ i, (1 : Matrix ι ι K) i ∈ L.forms) (p : ℕ)
    (w : AbsoluteValue K ℝ) {C : ℝ} (hC : 1 ≤ C)
    (hloc : ∀ B ∈ L.matSet, ∀ s t : Set.powersetCard ι p,
      w ((B.compound p)⁻¹ s t) ≤ C * ((⨆ e : L.detSet, w e) / w B.det) ^ p) :
    (⨆ q, w (L.invTuple p q)) ≤
      C * ((⨆ i, w (![L.detProd⁻¹ ^ p, 1] i)) *
        (⨆ e : L.detSet, w e) ^ (p * #L.matSet)) := by
  set m := ⨆ e : L.detSet, w e
  have hm1 : 1 ≤ m := one_le_iSup_detSet h1 w
  have hz : ∀ i, w (![L.detProd⁻¹ ^ p, 1] i) ≤ ⨆ i, w (![L.detProd⁻¹ ^ p, 1] i) :=
    fun i ↦ le_ciSup (f := fun i ↦ w (![L.detProd⁻¹ ^ p, 1] i)) (Finite.bddAbove_range _) i
  have hz0 := hz 0
  have hz1 := hz 1
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, map_one] at hz0 hz1
  have hmp : 1 ≤ m ^ (p * #L.matSet) := one_le_pow₀ hm1
  refine Real.iSup_le (fun q ↦ ?_) (by positivity)
  rcases q with _ | ⟨⟨B, hB⟩, s, t⟩
  · simp only [invTuple, Option.elim_none, map_one]
    calc (1 : ℝ) ≤ C * (1 * 1) := by simpa using hC
      _ ≤ _ := by gcongr
  · simp only [invTuple, Option.elim_some]
    refine (hloc B hB s t).trans ?_
    gcongr
    calc (m / w B.det) ^ p ≤ (m ^ #L.matSet * w L.detProd⁻¹) ^ p := by
          exact pow_le_pow_left₀ (div_nonneg (zero_le_one.trans hm1) (apply_nonneg _ _))
            (iSup_detSet_div_le h1 hB w) p
      _ = w (L.detProd⁻¹ ^ p) * m ^ (p * #L.matSet) := by
          rw [mul_pow, ← pow_mul, map_pow, mul_comm, mul_comm (#L.matSet)]
      _ ≤ _ := by gcongr

variable (L) in
/-- `H(det B) ≤ H_L` for a determinant of the system, relative to `K`. -/
theorem mulHeight₁_le_mulFormHeight (h1 : ∀ i, (1 : Matrix ι ι K) i ∈ L.forms) {d : K}
    (hd : d ∈ L.detSet) : Height.mulHeight₁ d ≤ L.mulFormHeight := by
  have hy : (fun e : L.detSet ↦ (e : K)) ≠ 0 := fun h ↦ by
    simpa using congrFun h ⟨1, L.one_mem_detSet h1⟩
  have hloc (w : AbsoluteValue K ℝ) : (⨆ i, w (![d, 1] i)) ≤ (⨆ e : L.detSet, w e) := by
    refine ciSup_le fun i ↦ ?_
    fin_cases i
    · exact L.le_iSup_detSet w hd
    · simpa using one_le_iSup_detSet h1 w
  have := Height.mulHeight_le_pow_mul_pow (C := 1) (D := 1) le_rfl hy
    (fun w _ ↦ by simpa using hloc w) fun w _ ↦ by simpa using hloc w
  rw [Height.mulHeight₁_eq_mulHeight]
  refine this.trans_eq ?_
  rw [one_pow, one_mul, pow_one, NumberField.mulHeight_eq hy]
  rfl

variable (L) in
/-- **EF13 Lemma 11.5, joint form**: the reference tuple has height at most
`p!^{[K:ℚ]} H_L^{2 p s}`, relative to `K`, `s = #matSet`. -/
theorem mulHeight_invTuple_le (h1 : ∀ i, (1 : Matrix ι ι K) i ∈ L.forms) (p : ℕ) :
    Height.mulHeight (L.invTuple p) ≤
      (p.factorial : ℝ) ^ finrank ℚ K * L.mulFormHeight ^ (2 * p * #L.matSet) := by
  have hy : (fun e : L.detSet ↦ (e : K)) ≠ 0 := fun h ↦ by
    simpa using congrFun h ⟨1, L.one_mem_detSet h1⟩
  have hz : ![L.detProd⁻¹ ^ p, 1] ≠ 0 := fun h ↦ by simpa using congrFun h 1
  have hC : (1 : ℝ) ≤ p.factorial := by exact_mod_cast p.factorial_pos
  have key := Height.mulHeight_le_pow_mul_mul_pow (x := L.invTuple p)
    (D := p * #L.matSet) hC hz hy
    (fun w _ ↦ iSup_invTuple_le h1 p w hC fun B hB s t ↦ apply_inv_compound_le h1 hB w p s t)
    fun w hw ↦ by
      simpa using iSup_invTuple_le h1 p w le_rfl fun B hB s t ↦ by
        simpa using apply_inv_compound_le_of_isNonarchimedean h1 hB
          (Height.AdmissibleAbsValues.isNonarchimedean w hw) p s t
  have hY : Height.mulHeight (fun e : L.detSet ↦ (e : K)) = L.mulFormHeight := by
    rw [NumberField.mulHeight_eq hy]
    rfl
  have hZ : Height.mulHeight ![L.detProd⁻¹ ^ p, 1] ≤ L.mulFormHeight ^ (p * #L.matSet) := by
    rw [← Height.mulHeight₁_eq_mulHeight, Height.mulHeight₁_pow, Height.mulHeight₁_inv,
      pow_mul', detProd]
    gcongr
    refine (Height.mulHeight₁_prod_le _ _).trans ?_
    rw [← prod_const]
    exact prod_le_prod₀ (fun _ _ ↦ (zero_le_one.trans (Height.one_le_mulHeight₁ _)))
      fun B hB ↦ L.mulHeight₁_le_mulFormHeight h1
        (det_mem_detSet_of_mem_matSet hB)
  rw [NumberField.totalWeight_eq_finrank, hY] at key
  refine key.trans ?_
  have hH1 := L.one_le_mulFormHeight
  rw [show 2 * p * #L.matSet = p * #L.matSet + p * #L.matSet by ring, pow_add]
  gcongr

end FormSystem

end NumberField
