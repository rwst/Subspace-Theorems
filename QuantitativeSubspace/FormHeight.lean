/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.TwistedHeight

-- Used only inside proofs.
import ArithmeticHeights.Extension

/-!
# Twisted heights from systems of linear forms

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, §2.2, after J.-H. Evertse and H. P. Schlickewei, *A
quantitative version of the Absolute Subspace Theorem*, J. reine angew. Math. **548** (2002),
21–127, (7.3). For a number field `K`, a system `L = (L_i^{(v)})` of linear forms with
coefficients in `K`, linearly independent at every place `v` and finitely many distinct overall,
and positive weights `A_iv`, almost all `1`, the twisted height of an algebraic point `x` is

```text
H_{L,A}(x) = ∏_{w ∈ M_E} max_i ‖L_i^{(w)}(x)‖_w / A_iw,   A_iw = A_iv ^ d(w|v),
```

with `E ⊇ K` any number field containing the coordinates, `‖·‖_w` normalized, the **max norm at
every place** (RT96's ℓ² norm at the infinite places is `NumberField.Twist`), and `L^{(w)}` the
system at the place of `K` below `w`. EF13's `H_{L,c,Q}` (2.13)–(2.15) is the case
`A_iv = Q ^ c_iv`.

## Normalization

Everything is first relative to `E`, in Mathlib's normalization of places: the factor at an
infinite place `w` is raised to its multiplicity, a finite place `w` is Mathlib's absolute value
(already of local degree over `ℚ`), and the absolute height is the `[E : ℚ]`-th root, as for
`NumberField.Twist.absMulHeight`. In that normalization the weight of `(L, A)` at a place `v` of
`K` is recorded **relatively** too: `NumberField.FormWeight.arch v i` is the size `a_iv` with
`‖·‖_v`-weight `A_iv = a_iv ^ {mult v / [K : ℚ]}`, and `NumberField.FormWeight.fin v i` is `a_iv`
with `A_iv = a_iv ^ {1 / [K : ℚ]}`. So ES02's hypothesis (7.4), `A_iv = ‖α_iv‖_v`, is
`a_iv = v α_iv` read with Mathlib's absolute values. Above `v`, the weight at a finite place `w` of
`E` is `a_iv ^ (local degree of w over K)`, at an infinite place `w` it is `a_iv` with the
exponent `mult w` of the whole factor.

## Main definitions

* `NumberField.FormSystem K ι`: the forms, a matrix over `K` for each infinite and each finite
  place of `K`, invertible, finitely many distinct ones (EF13 (2.4)–(2.6)).
* `NumberField.FormWeight K ι`: positive weights, `1` at all but finitely many finite places
  (EF13 (2.7)).
* `NumberField.FormSystem.mulHeight`, `NumberField.FormSystem.absMulHeight`: the twisted height,
  relative to a number field and absolute on `Ωⁿ` for `Ω` algebraic over `K`.
* `NumberField.FormExponent K ι`, `NumberField.FormExponent.weight`: EF13's exponents `c_iv` and
  the weights `Q ^ c_iv`; `L.absMulHeight (c.weight hQ)` is EF13's `H_{L,c,Q}`.
* `NumberField.FormSystem.comp L P`: the system `L ∘ P` for `P ∈ GLₙ(K)`.
* `NumberField.FormSystem.absDet`: `Δ_L` of EF13 (2.11).
* `NumberField.FormSystem.forms`, `NumberField.FormSystem.absFormHeight`: the distinct forms
  `L_1, …, L_r` and `H_L` of EF13 (2.12).

## Main results

* `NumberField.FinitePlace.localDegree_tower`: local degrees multiply in towers.
* `NumberField.FormSystem.mulHeight_algebraMap`: over `F ⊇ E` the height is raised to `[F : E]`,
  EF13's "independent of the choice of `E`".
* `NumberField.FormSystem.mulHeight_smul`, `NumberField.FormSystem.absMulHeight_smul`: invariance
  under scaling, by the product formula.
* `NumberField.FormSystem.absMulHeight_algHom`, `NumberField.FormSystem.absMulHeight_algEquiv`:
  the absolute height is computed in any field of definition, and it is invariant under
  `Gal(Ω / K)` (EF13 Lemma 4.1, ES02 Lemma 4.1).
* `NumberField.FormSystem.absMulHeight_of_scale`,
  `NumberField.FormSystem.absMulHeight_weight_of_sub`: EF13 Lemma 7.2 (i), rescaling the weights
  place by place.
* `NumberField.FormSystem.absMulHeight_comp`, `NumberField.FormSystem.absDet_comp`: EF13 Lemma 7.3
  (i), (iv).
* `NumberField.FormSystem.absDet_le_absFormHeight`,
  `NumberField.FormSystem.absFormHeight_rpow_le_absDet`: EF13 (7.4),
  `H_L ^ {1 - C(r, n)} ≤ Δ_L ≤ H_L`. The count `C(r, n)` comes from the squared determinants,
  which depend only on the set of rows (`card_detSq_le`).
* `NumberField.FormSystem.one_le_absMulHeight` (general weights) and
  `NumberField.FormSystem.le_absMulHeight_weight` (EF13 Lemma 7.1):
  `H_{L,c,Q}(x) ≥ n⁻¹ H_L ^ {-C(r, n)} Q ^ {-θ}`, by Cramer's rule in row form
  (`mul_adjugate_apply_eq_det_updateRow`) and the product formula.

This is milestone Q2.4a of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Finset Function Module Matrix IsDedekindDomain

namespace NumberField

namespace FinitePlace

variable {K E F : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
  [Field F] [NumberField F] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

omit [NumberField K] in
/-- **Local degrees multiply in towers**: `[F_w : K_v] = [F_w : E_u] [E_u : K_v]`. -/
theorem localDegree_tower (w : FinitePlace F) :
    w.localDegree K = w.localDegree E * (w.under E).localDegree K := by
  have : IsScalarTower (𝓞 K) (𝓞 E) (𝓞 F) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ RingOfIntegers.ext <| by
      exact IsScalarTower.algebraMap_apply K E F (x : K)
  have : w.maximalIdeal.asIdeal.LiesOver (w.under E).maximalIdeal.asIdeal := liesOver_under w
  unfold localDegree
  rw [Ideal.ramificationIdx_tower (r := w.maximalIdeal.asIdeal)
      (q := (w.under E).maximalIdeal.asIdeal),
    Ideal.inertiaDeg_tower (r := w.maximalIdeal.asIdeal) (q := (w.under E).maximalIdeal.asIdeal)]
  ring

end FinitePlace

variable (K : Type*) [Field K] [NumberField K] (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- **A system of linear forms** over `K` in the sense of EF13 (2.4)–(2.6): at each place of `K`
a matrix over `K` whose rows are the forms `L_1^{(v)}, …, L_n^{(v)}`, invertible, with finitely
many distinct matrices at the finite places (the infinite places are finitely many anyway). -/
structure FormSystem where
  /-- The forms at the infinite places. -/
  arch : InfinitePlace K → Matrix ι ι K
  arch_det_ne_zero : ∀ v, (arch v).det ≠ 0
  /-- The forms at the finite places. -/
  fin : FinitePlace K → Matrix ι ι K
  fin_det_ne_zero : ∀ v, (fin v).det ≠ 0
  finite_range_fin : (Set.range fin).Finite

/-- **Weights** for a system of linear forms, in the relative normalization of the module doc:
positive reals at every place of `K` and for every index, `1` at all but finitely many finite
places (EF13 (2.7)). -/
structure FormWeight where
  /-- The weights at the infinite places. -/
  arch : InfinitePlace K → ι → ℝ
  arch_pos : ∀ v i, 0 < arch v i
  /-- The weights at the finite places. -/
  fin : FinitePlace K → ι → ℝ
  fin_pos : ∀ v i, 0 < fin v i
  finite_setOf_fin_ne_one : {v | fin v ≠ 1}.Finite

namespace FormSystem

variable {K ι} (L : FormSystem K ι) (a : FormWeight K ι)
variable {E F : Type*} [Field E] [NumberField E] [Algebra K E]
  [Field F] [NumberField F] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

/-- The local factor at an infinite place `w` of `E`, before raising to `mult w`: the largest
`|L_i^{(v)}(x)|_w / a_iv`, `v` the place of `K` below `w`. -/
noncomputable def archFactor (w : InfinitePlace E) (x : ι → E) : ℝ :=
  ⨆ i, w ((((L.arch (w.comap (algebraMap K E))).map (algebraMap K E)) *ᵥ x) i) /
    a.arch (w.comap (algebraMap K E)) i

/-- The local factor at a finite place `w` of `E`: the largest `w (L_i^{(v)}(x)) / a_iv ^ e`,
`v` the place of `K` below `w` and `e` the local degree of `w` over `K`. -/
noncomputable def finFactor (w : FinitePlace E) (x : ι → E) : ℝ :=
  ⨆ i, w ((((L.fin (w.under K)).map (algebraMap K E)) *ᵥ x) i) /
    a.fin (w.under K) i ^ w.localDegree K

/-- **The twisted height** of `x : ι → E` relative to `E`. -/
noncomputable def mulHeight (x : ι → E) : ℝ :=
  (∏ w : InfinitePlace E, L.archFactor a w x ^ w.mult) * ∏ᶠ w : FinitePlace E, L.finFactor a w x

omit [NumberField E] in
theorem archFactor_nonneg (w : InfinitePlace E) (x : ι → E) : 0 ≤ L.archFactor a w x :=
  Real.iSup_nonneg fun i ↦ div_nonneg (apply_nonneg _ _) (a.arch_pos _ i).le

theorem finFactor_nonneg (w : FinitePlace E) (x : ι → E) : 0 ≤ L.finFactor a w x :=
  Real.iSup_nonneg fun i ↦ div_nonneg (apply_nonneg _ _) (pow_nonneg (a.fin_pos _ i).le _)

omit [NumberField E] in
@[simp] theorem archFactor_zero (w : InfinitePlace E) : L.archFactor a w (0 : ι → E) = 0 := by
  simp only [archFactor, Matrix.mulVec_zero, Pi.zero_apply, map_zero, zero_div,
    Real.iSup_const_zero]

@[simp] theorem mulHeight_zero : L.mulHeight a (0 : ι → E) = 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  rw [mulHeight, Finset.prod_eq_zero (mem_univ w) (by simp [InfinitePlace.mult_ne_zero]),
    zero_mul]

/-! ### Reading a point over a larger field -/

omit [NumberField E] [NumberField F] in
theorem archFactor_algebraMap (w : InfinitePlace F) (x : ι → E) :
    L.archFactor a w (algebraMap E F ∘ x) = L.archFactor a (w.comap (algebraMap E F)) x := by
  have hc : (w.comap (algebraMap E F)).comap (algebraMap K E) = w.comap (algebraMap K F) := by
    rw [← InfinitePlace.comap_comp, ← IsScalarTower.algebraMap_eq]
  rw [archFactor, archFactor, hc]
  refine iSup_congr fun i ↦ ?_
  have hmap : (L.arch (w.comap (algebraMap K F))).map (algebraMap K F) =
      ((L.arch (w.comap (algebraMap K F))).map (algebraMap K E)).map (algebraMap E F) := by
    rw [Matrix.map_map, IsScalarTower.algebraMap_eq K E F]
    rfl
  rw [hmap, ← RingHom.map_mulVec, InfinitePlace.comap_apply]

private theorem iSup_pow {κ : Type*} [Finite κ] {f : κ → ℝ} (hf : ∀ i, 0 ≤ f i) {k : ℕ}
    (hk : 0 < k) : (⨆ i, f i) ^ k = ⨆ i, f i ^ k := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp [zero_pow hk.ne']
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := f)
  refine le_antisymm ?_ (ciSup_le fun j ↦ ?_)
  · rw [← hi]
    exact Finite.le_ciSup_of_le i le_rfl
  · exact pow_le_pow_left₀ (hf j) (Finite.le_ciSup_of_le j le_rfl) k

theorem finFactor_algebraMap (w : FinitePlace F) (x : ι → E) :
    L.finFactor a w (algebraMap E F ∘ x) = L.finFactor a (w.under E) x ^ w.localDegree E := by
  rw [finFactor, finFactor,
    iSup_pow (fun i ↦ div_nonneg (apply_nonneg _ _) (pow_nonneg (a.fin_pos _ i).le _))
      (w.localDegree_pos (K := E)),
    ← FinitePlace.under_under (K := K) (E := E) w]
  refine iSup_congr fun i ↦ ?_
  have hmap : (L.fin ((w.under E).under K)).map (algebraMap K F) =
      ((L.fin ((w.under E).under K)).map (algebraMap K E)).map (algebraMap E F) := by
    rw [Matrix.map_map, IsScalarTower.algebraMap_eq K E F]
    rfl
  rw [hmap, ← RingHom.map_mulVec, FinitePlace.apply_algebraMap w (w.under E), div_pow,
    ← pow_mul, FinitePlace.localDegree_tower (K := K) (E := E) w,
    Nat.mul_comm (w.localDegree E)]

/-- At a finite place where the weights are `1` and every nonzero coordinate of the transformed
point is a unit, the local factor is `1`. -/
private theorem finFactor_eq_one {w : FinitePlace E} {x : ι → E}
    (hne : ((L.fin (w.under K)).map (algebraMap K E)) *ᵥ x ≠ 0)
    (ha : a.fin (w.under K) = 1)
    (hw : ∀ i, (((L.fin (w.under K)).map (algebraMap K E)) *ᵥ x) i ≠ 0 →
      w ((((L.fin (w.under K)).map (algebraMap K E)) *ᵥ x) i) = 1) :
    L.finFactor a w x = 1 := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hne
  have : Nonempty ι := ⟨i₀⟩
  rw [finFactor, ha]
  simp only [Pi.one_apply, one_pow, div_one]
  refine le_antisymm (ciSup_le fun i ↦ ?_) (Finite.le_ciSup_of_le i₀ (hw i₀ hi₀).ge)
  rcases eq_or_ne ((((L.fin (w.under K)).map (algebraMap K E)) *ᵥ x) i) 0 with h | h
  · simp [h]
  · exact (hw i h).le

omit [NumberField K] [NumberField E] in
theorem mulVec_ne_zero_of_det_ne_zero {M : Matrix ι ι K} (hM : M.det ≠ 0) {x : ι → E}
    (hx : x ≠ 0) : M.map (algebraMap K E) *ᵥ x ≠ 0 := by
  have hdet : (M.map (algebraMap K E)).det ≠ 0 := by
    rw [show (M.map (algebraMap K E)).det = algebraMap K E M.det from (RingHom.map_det _ _).symm]
    exact (map_ne_zero _).mpr hM
  exact fun h ↦ hx (Matrix.eq_zero_of_mulVec_eq_zero hdet h)

theorem hasFiniteMulSupport_finFactor {x : ι → E} (hx : x ≠ 0) :
    (fun w : FinitePlace E ↦ L.finFactor a w x).HasFiniteMulSupport := by
  classical
  have hbad : {w : FinitePlace E | a.fin (w.under K) ≠ 1}.Finite := by
    refine (a.finite_setOf_fin_ne_one.biUnion fun v _ ↦ FinitePlace.finite_placesOver E v).subset
      fun w hw ↦ Set.mem_biUnion hw ?_
    exact FinitePlace.mem_placesOver.mpr (FinitePlace.liesOver_under (K := K) w)
  have hcoord : ∀ (M : Set.range L.fin) (i : ι),
      {w : FinitePlace E | ((M.1.map (algebraMap K E)) *ᵥ x) i ≠ 0 ∧
        w (((M.1.map (algebraMap K E)) *ᵥ x) i) ≠ 1}.Finite := by
    intro M i
    by_cases h : ((M.1.map (algebraMap K E)) *ᵥ x) i = 0
    · simp [h]
    · exact (FinitePlace.hasFiniteMulSupport h).subset fun w hw ↦ hw.2
  have : Finite (Set.range L.fin) := L.finite_range_fin
  refine (hbad.union (Set.finite_iUnion fun M : Set.range L.fin ↦
    Set.finite_iUnion fun i ↦ hcoord M i)).subset fun w hw ↦ ?_
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_not, not_exists,
    not_and] at hcon
  exact hw (L.finFactor_eq_one a
    (mulVec_ne_zero_of_det_ne_zero (L.fin_det_ne_zero _) hx) hcon.1
    fun i hi ↦ hcon.2 ⟨_, w.under K, rfl⟩ i hi)

/-- **The twisted height over `F` is the `[F : E]`-th power of the twisted height over `E`.** -/
theorem mulHeight_algebraMap (x : ι → E) :
    L.mulHeight a (algebraMap E F ∘ x) = L.mulHeight a x ^ finrank E F := by
  rcases eq_or_ne x 0 with rfl | hx
  · have hz : (algebraMap E F ∘ (0 : ι → E)) = 0 := funext fun _ ↦ by simp
    rw [hz, mulHeight_zero, mulHeight_zero, zero_pow finrank_pos.ne']
  rw [mulHeight, mulHeight, mul_pow]
  congr 1
  · exact prod_infinitePlace_pow_mult_eq (fun v ↦ L.archFactor a v x)
      (fun w ↦ L.archFactor a w (algebraMap E F ∘ x))
      fun φ ↦ by rw [archFactor_algebraMap]; rfl
  · simp_rw [finFactor_algebraMap]
    exact FinitePlace.finprod_under_pow_localDegree _ (L.hasFiniteMulSupport_finFactor a hx)

/-! ### Scaling and positivity -/

omit [NumberField E] in
theorem archFactor_smul (w : InfinitePlace E) (c : E) (x : ι → E) :
    L.archFactor a w (c • x) = w c * L.archFactor a w x := by
  rw [archFactor, archFactor, Matrix.mulVec_smul,
    Real.mul_iSup_of_nonneg (apply_nonneg _ _)]
  simp [mul_div_assoc]

theorem finFactor_smul (w : FinitePlace E) (c : E) (x : ι → E) :
    L.finFactor a w (c • x) = w c * L.finFactor a w x := by
  rw [finFactor, finFactor, Matrix.mulVec_smul, Real.mul_iSup_of_nonneg (apply_nonneg _ _)]
  simp [mul_div_assoc]

/-- **The twisted height is invariant under scaling**, by the product formula. -/
theorem mulHeight_smul (x : ι → E) {c : E} (hc : c ≠ 0) :
    L.mulHeight a (c • x) = L.mulHeight a x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [smul_zero]
  have hprod := prod_abs_eq_one hc
  rw [mulHeight, mulHeight]
  simp_rw [archFactor_smul, finFactor_smul, mul_pow]
  rw [Finset.prod_mul_distrib,
    finprod_mul_distrib (FinitePlace.hasFiniteMulSupport hc) (L.hasFiniteMulSupport_finFactor a hx)]
  calc (∏ w : InfinitePlace E, w c ^ w.mult) * (∏ w, L.archFactor a w x ^ w.mult) *
        ((∏ᶠ w : FinitePlace E, w c) * ∏ᶠ w, L.finFactor a w x)
      = ((∏ w : InfinitePlace E, w c ^ w.mult) * ∏ᶠ w : FinitePlace E, w c) *
        ((∏ w, L.archFactor a w x ^ w.mult) * ∏ᶠ w, L.finFactor a w x) := by ring
    _ = _ := by rw [hprod, one_mul]

omit [NumberField E] in
theorem archFactor_pos {x : ι → E} (hx : x ≠ 0) (w : InfinitePlace E) :
    0 < L.archFactor a w x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (mulVec_ne_zero_of_det_ne_zero (L.arch_det_ne_zero
    (w.comap (algebraMap K E))) hx)
  simp only [Pi.zero_apply] at hi
  unfold archFactor
  exact (div_pos (InfinitePlace.pos_iff.mpr hi) (a.arch_pos _ i)).trans_le
    (Finite.le_ciSup_of_le i le_rfl)

theorem finFactor_pos {x : ι → E} (hx : x ≠ 0) (w : FinitePlace E) : 0 < L.finFactor a w x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (mulVec_ne_zero_of_det_ne_zero (L.fin_det_ne_zero
    (w.under K)) hx)
  simp only [Pi.zero_apply] at hi
  unfold finFactor
  exact (div_pos (FinitePlace.pos_iff.mpr hi) (pow_pos (a.fin_pos _ i) _)).trans_le
    (Finite.le_ciSup_of_le i le_rfl)

/-- **The twisted height of a nonzero point is positive.** -/
theorem mulHeight_pos {x : ι → E} (hx : x ≠ 0) : 0 < L.mulHeight a x := by
  refine mul_pos (Finset.prod_pos fun w _ ↦ pow_pos (L.archFactor_pos a hx w) _) ?_
  rw [finprod_eq_prod_of_mulSupport_subset _
    (Set.Finite.coe_toFinset (L.hasFiniteMulSupport_finFactor a hx)).symm.subset]
  exact Finset.prod_pos fun w _ ↦ L.finFactor_pos a hx w

theorem mulHeight_nonneg (x : ι → E) : 0 ≤ L.mulHeight a x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [mulHeight_zero]
  · exact (L.mulHeight_pos a hx).le

/-! ### The absolute twisted height -/

section Absolute

open IntermediateField

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

/-- **The absolute twisted height** of `x : ι → Ω`: the twisted height relative to
`K(x₀, x₁, …)`, taken to the power `1 / [K(x₀, x₁, …) : ℚ]`. -/
noncomputable def absMulHeight (x : ι → Ω) : ℝ :=
  haveI := Twist.numberField_adjoin_range (K := K) x
  L.mulHeight a (fun i ↦ (⟨x i, subset_adjoin K _ ⟨i, rfl⟩⟩ : adjoin K (Set.range x))) ^
    ((finrank ℚ (adjoin K (Set.range x)) : ℝ))⁻¹

private theorem rpow_inv_natCast_mul {b : ℝ} (hb : 0 ≤ b) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    (b ^ n) ^ (((m * n : ℕ) : ℝ))⁻¹ = b ^ ((m : ℝ))⁻¹ := by
  rw [← Real.rpow_natCast b n, ← Real.rpow_mul hb]
  congr 1
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  push_cast
  field_simp

/-- **The absolute twisted height computed in a field of definition.** -/
theorem absMulHeight_eq_of_mem {E : IntermediateField K Ω} [NumberField E] {x : ι → Ω}
    (hx : ∀ i, x i ∈ E) :
    L.absMulHeight a x = L.mulHeight a (fun i ↦ (⟨x i, hx i⟩ : E)) ^ ((finrank ℚ E : ℝ))⁻¹ := by
  have hFE : adjoin K (Set.range x) ≤ E := adjoin_le_iff.mpr (by rintro _ ⟨i, rfl⟩; exact hx i)
  have := Twist.numberField_adjoin_range (K := K) x
  let : Algebra (adjoin K (Set.range x)) E := (inclusion hFE).toAlgebra
  have : IsScalarTower K (adjoin K (Set.range x)) E :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((inclusion hFE).commutes r).symm
  have : IsScalarTower ℚ (adjoin K (Set.range x)) E :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (map_ratCast (inclusion hFE) r).symm
  have : Module.Finite (adjoin K (Set.range x)) E :=
    Module.Finite.of_restrictScalars_finite ℚ _ E
  have hcomp : (algebraMap (adjoin K (Set.range x)) E) ∘
      (fun i ↦ (⟨x i, subset_adjoin K _ ⟨i, rfl⟩⟩ : adjoin K (Set.range x)))
      = fun i ↦ (⟨x i, hx i⟩ : E) := rfl
  rw [absMulHeight, ← hcomp, mulHeight_algebraMap,
    ← Module.finrank_mul_finrank ℚ (adjoin K (Set.range x)) E,
    rpow_inv_natCast_mul (L.mulHeight_nonneg a _)
      (Module.finrank_pos (R := ℚ) (M := adjoin K (Set.range x))).ne'
      (Module.finrank_pos (R := adjoin K (Set.range x)) (M := E)).ne']

/-- **The absolute twisted height through any `K`-embedding** of a number field into `Ω`. -/
theorem absMulHeight_algHom {F : Type*} [Field F] [NumberField F] [Algebra K F] (f : F →ₐ[K] Ω)
    (y : ι → F) : L.absMulHeight a (f ∘ y) = L.mulHeight a y ^ ((finrank ℚ F : ℝ))⁻¹ := by
  set G := f.fieldRange
  let e : F ≃ₐ[K] G := f.equivFieldRange
  have : FiniteDimensional K G := e.toLinearEquiv.finiteDimensional
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have : NumberField G := { to_finiteDimensional := Module.Finite.trans K _ }
  let : Algebra F G := e.toRingEquiv.toRingHom.toAlgebra
  have : IsScalarTower K F G := IsScalarTower.of_algebraMap_eq fun r ↦ (e.commutes r).symm
  have hx : ∀ i, (f ∘ y) i ∈ G := fun i ↦ ⟨y i, rfl⟩
  have hcomp : (fun i ↦ (⟨(f ∘ y) i, hx i⟩ : G)) = algebraMap F G ∘ y := rfl
  have hKF := Module.finrank_mul_finrank ℚ K F
  have hKG := Module.finrank_mul_finrank ℚ K G
  have hFG : finrank K F = finrank K G := e.toLinearEquiv.finrank_eq
  have h1 : finrank F G = 1 := by
    have hFG' := Module.finrank_mul_finrank K F G
    have hpos : 0 < finrank K F := finrank_pos
    rw [← hFG] at hFG'
    nlinarith
  rw [L.absMulHeight_eq_of_mem a hx, hcomp, mulHeight_algebraMap, h1, pow_one, ← hKF, ← hKG, hFG]

/-- **The absolute twisted height of a point of `Kⁿ`.** -/
theorem absMulHeight_algebraMap (y : ι → K) :
    L.absMulHeight a (algebraMap K Ω ∘ y) = L.mulHeight a y ^ ((finrank ℚ K : ℝ))⁻¹ :=
  L.absMulHeight_algHom a (Algebra.ofId K Ω) y

/-- **Invariance under `K`-endomorphisms of `Ω`**: `H(σ x) = H(x)`. -/
theorem absMulHeight_comp_algHom (σ : Ω →ₐ[K] Ω) (x : ι → Ω) :
    L.absMulHeight a (σ ∘ x) = L.absMulHeight a x := by
  have := Twist.numberField_adjoin_range (K := K) x
  set y : ι → adjoin K (Set.range x) := fun i ↦ ⟨x i, subset_adjoin K _ ⟨i, rfl⟩⟩
  have hσ : (σ : Ω → Ω) ∘ x = (σ.comp (adjoin K (Set.range x)).val) ∘ y := rfl
  rw [hσ, absMulHeight_algHom, absMulHeight]

/-- **Galois invariance** (EF13 Lemma 4.1, ES02 Lemma 4.1): `H(σ x) = H(x)` for every
`K`-automorphism `σ` of `Ω`. -/
theorem absMulHeight_algEquiv (σ : Ω ≃ₐ[K] Ω) (x : ι → Ω) :
    L.absMulHeight a (σ ∘ x) = L.absMulHeight a x :=
  L.absMulHeight_comp_algHom a (σ : Ω →ₐ[K] Ω) x

/-- The absolute twisted height of a nonzero point is positive. -/
theorem absMulHeight_pos {x : ι → Ω} (hx : x ≠ 0) : 0 < L.absMulHeight a x := by
  have := Twist.numberField_adjoin_range (K := K) x
  refine Real.rpow_pos_of_pos (L.mulHeight_pos a fun h ↦ hx (funext fun i ↦ ?_)) _
  simpa using congrArg Subtype.val (congrFun h i)

theorem absMulHeight_nonneg (x : ι → Ω) : 0 ≤ L.absMulHeight a x := by
  have := Twist.numberField_adjoin_range (K := K) x
  exact Real.rpow_nonneg (L.mulHeight_nonneg a _) _

/-- **The absolute twisted height is invariant under scaling.** -/
theorem absMulHeight_smul (x : ι → Ω) {c : Ω} (hc : c ≠ 0) :
    L.absMulHeight a (c • x) = L.absMulHeight a x := by
  set E := adjoin K (insert c (Set.range x))
  have : NumberField E := by
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
    have : FiniteDimensional K E :=
      finiteDimensional_adjoin fun y _ ↦ (Algebra.IsAlgebraic.isAlgebraic (R := K) y).isIntegral
    exact { to_finiteDimensional := Module.Finite.trans K _ }
  have hcE : c ∈ E := subset_adjoin K _ (Set.mem_insert _ _)
  have hxE : ∀ i, x i ∈ E := fun i ↦ subset_adjoin K _ (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  have hcxE : ∀ i, (c • x) i ∈ E := fun i ↦ E.mul_mem hcE (hxE i)
  rw [L.absMulHeight_eq_of_mem a hcxE, L.absMulHeight_eq_of_mem a hxE]
  have : (fun i ↦ (⟨(c • x) i, hcxE i⟩ : E)) = (⟨c, hcE⟩ : E) • fun i ↦ ⟨x i, hxE i⟩ := rfl
  rw [this, L.mulHeight_smul a _ fun h ↦ hc (congrArg Subtype.val h)]

end Absolute

/-! ### Rescaling the weights place by place (EF13 Lemma 7.2) -/

section Rescale

open IntermediateField

variable {a b : FormWeight K ι} {s : InfinitePlace K → ℝ} {r : FinitePlace K → ℝ}

private theorem iSup_div_const {κ : Type*} (f : κ → ℝ) {t : ℝ} (ht : 0 < t) :
    (⨆ i, f i / t) = (⨆ i, f i) / t := by
  rw [div_eq_inv_mul, Real.mul_iSup_of_nonneg (inv_nonneg.mpr ht.le)]
  simp [div_eq_inv_mul]

omit [NumberField E] in
theorem archFactor_of_scale (hs : ∀ v, 0 < s v) (harch : ∀ v i, b.arch v i = a.arch v i * s v)
    (w : InfinitePlace E) (x : ι → E) :
    L.archFactor b w x = L.archFactor a w x / s (w.comap (algebraMap K E)) := by
  rw [archFactor, archFactor, ← iSup_div_const _ (hs _)]
  simp_rw [harch, div_div]

theorem finFactor_of_scale (hr : ∀ v, 0 < r v) (hfin : ∀ v i, b.fin v i = a.fin v i * r v)
    (w : FinitePlace E) (x : ι → E) :
    L.finFactor b w x = L.finFactor a w x / r (w.under K) ^ w.localDegree K := by
  rw [finFactor, finFactor, ← iSup_div_const _ (pow_pos (hr _) _)]
  simp_rw [hfin, mul_pow, div_div]

/-- **Rescaling the weights at each place by a common factor** divides the relative height by
the `[E : K]`-th power of the product of the factors. With `s_v = Q ^ {-θ_v [K:ℚ] / mult v}` and
`r_v = Q ^ {-θ_v [K:ℚ]}` this is EF13 Lemma 7.2 (i). -/
theorem mulHeight_of_scale (hs : ∀ v, 0 < s v) (hr : ∀ v, 0 < r v)
    (hrf : r.HasFiniteMulSupport) (harch : ∀ v i, b.arch v i = a.arch v i * s v)
    (hfin : ∀ v i, b.fin v i = a.fin v i * r v) (x : ι → E) :
    L.mulHeight b x =
      L.mulHeight a x / ((∏ v, s v ^ v.mult) * ∏ᶠ v, r v) ^ finrank K E := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hS : ∏ w : InfinitePlace E, s (w.comap (algebraMap K E)) ^ w.mult =
      (∏ v, s v ^ v.mult) ^ finrank K E :=
    prod_infinitePlace_pow_mult_eq s (fun w ↦ s (w.comap (algebraMap K E))) fun _ ↦ rfl
  have hR : ∏ᶠ w : FinitePlace E, r (w.under K) ^ w.localDegree K = (∏ᶠ v, r v) ^ finrank K E :=
    FinitePlace.finprod_under_pow_localDegree r hrf
  rw [mulHeight, mulHeight, mul_pow, ← hS, ← hR]
  simp_rw [L.archFactor_of_scale hs harch, L.finFactor_of_scale hr hfin, div_pow]
  rw [Finset.prod_div_distrib, finprod_div_distrib (L.hasFiniteMulSupport_finFactor a hx)
    (FinitePlace.hasFiniteMulSupport_comp_under hrf _)]
  ring

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

/-- `(t ^ [E:K]) ^ {1/[E:ℚ]} = t ^ {1/[K:ℚ]}`. -/
theorem rpow_finrank_inv {E : Type*} [Field E] [NumberField E] [Algebra K E] {t : ℝ}
    (ht : 0 < t) : (t ^ finrank K E) ^ ((finrank ℚ E : ℝ))⁻¹ = t ^ ((finrank ℚ K : ℝ))⁻¹ := by
  have : Module.Finite K E := Module.Finite.of_restrictScalars_finite ℚ K E
  rw [← Module.finrank_mul_finrank ℚ K E, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  congr 1
  have h1 : (finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  have h2 : (finrank K E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  push_cast
  field_simp

/-- **EF13 Lemma 7.2 (i)**, absolute form: rescaling the weights divides the absolute height by
the `[K : ℚ]`-th root of the product of the factors. -/
theorem absMulHeight_of_scale (hs : ∀ v, 0 < s v) (hr : ∀ v, 0 < r v)
    (hrf : r.HasFiniteMulSupport) (harch : ∀ v i, b.arch v i = a.arch v i * s v)
    (hfin : ∀ v i, b.fin v i = a.fin v i * r v) (x : ι → Ω) :
    L.absMulHeight b x = L.absMulHeight a x /
      ((∏ v, s v ^ v.mult) * ∏ᶠ v, r v) ^ ((finrank ℚ K : ℝ))⁻¹ := by
  have := Twist.numberField_adjoin_range (K := K) x
  have : Module.Finite K (adjoin K (Set.range x)) :=
    Module.Finite.of_restrictScalars_finite ℚ K _
  have hT : 0 < (∏ v, s v ^ v.mult) * ∏ᶠ v, r v :=
    mul_pos (Finset.prod_pos fun v _ ↦ pow_pos (hs v) _)
      (by rw [finprod_eq_prod _ hrf]; exact Finset.prod_pos fun v _ ↦ hr v)
  rw [absMulHeight, absMulHeight, L.mulHeight_of_scale hs hr hrf harch hfin,
    Real.div_rpow (L.mulHeight_nonneg a _) (pow_nonneg hT.le _), rpow_finrank_inv hT]

end Rescale

/-! ### Change of coordinates (EF13 Lemma 7.3) -/

section Comp

open IntermediateField

/-- **The system `L ∘ P`** for an invertible matrix `P` over `K`: the forms `L_i^{(v)}(P X)`. -/
noncomputable def comp (P : Matrix ι ι K) (hP : P.det ≠ 0) : FormSystem K ι where
  arch v := L.arch v * P
  arch_det_ne_zero v := by rw [det_mul]; exact mul_ne_zero (L.arch_det_ne_zero v) hP
  fin v := L.fin v * P
  fin_det_ne_zero v := by rw [det_mul]; exact mul_ne_zero (L.fin_det_ne_zero v) hP
  finite_range_fin := (L.finite_range_fin.image (· * P)).subset <| by
    rintro _ ⟨v, rfl⟩
    exact ⟨_, ⟨v, rfl⟩, rfl⟩

variable (P : Matrix ι ι K) (hP : P.det ≠ 0)

/-- **EF13 Lemma 7.3 (i)**, relative form: `H_{L ∘ P}(x) = H_L(P x)`. -/
theorem mulHeight_comp (x : ι → E) :
    (L.comp P hP).mulHeight a x = L.mulHeight a (P.map (algebraMap K E) *ᵥ x) := by
  simp only [mulHeight, archFactor, finFactor, comp, Matrix.map_mul, ← Matrix.mulVec_mulVec]

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

/-- **EF13 Lemma 7.3 (i)**: `H_{L ∘ P}(x) = H_L(P x)` on `Ωⁿ`. -/
theorem absMulHeight_comp (x : ι → Ω) :
    (L.comp P hP).absMulHeight a x = L.absMulHeight a (P.map (algebraMap K Ω) *ᵥ x) := by
  have := Twist.numberField_adjoin_range (K := K) x
  set G := adjoin K (Set.range x)
  set y : ι → G := fun i ↦ ⟨x i, subset_adjoin K _ ⟨i, rfl⟩⟩
  have hx : x = G.val ∘ y := rfl
  have hPx : P.map (algebraMap K Ω) *ᵥ x = G.val ∘ (P.map (algebraMap K G) *ᵥ y) := by
    funext i
    simp [hx, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [hPx, absMulHeight_algHom, hx, absMulHeight_algHom, mulHeight_comp]

end Comp

/-! ### The determinant `Δ_L` -/

section Det

/-- The determinants of the system at the finite places have finite multiplicative support. -/
theorem hasFiniteMulSupport_det_fin :
    (fun v : FinitePlace K ↦ v (L.fin v).det).HasFiniteMulSupport := by
  have hfin : (Set.range fun v ↦ (L.fin v).det).Finite :=
    (L.finite_range_fin.image Matrix.det).subset <| by
      rintro _ ⟨v, rfl⟩
      exact ⟨_, ⟨v, rfl⟩, rfl⟩
  have : Finite (Set.range fun v ↦ (L.fin v).det) := hfin
  refine (Set.finite_iUnion fun d : Set.range (fun v ↦ (L.fin v).det) ↦
    (FinitePlace.hasFiniteMulSupport (K := K) (x := d.1) ?_)).subset fun v hv ↦
      Set.mem_iUnion.mpr ⟨⟨_, v, rfl⟩, hv⟩
  obtain ⟨v, hv⟩ := d.2
  rw [← hv]
  exact L.fin_det_ne_zero v

/-- The determinant of the system relative to `K`: `∏_v |det L^{(v)}|_v`, in the relative
normalization. -/
noncomputable def mulDet : ℝ :=
  (∏ v : InfinitePlace K, v (L.arch v).det ^ v.mult) * ∏ᶠ v : FinitePlace K, v (L.fin v).det

/-- **`Δ_L`** of EF13 (2.11): `∏_{v ∈ M_K} ‖det(L_1^{(v)}, …, L_n^{(v)})‖_v`. -/
noncomputable def absDet : ℝ :=
  L.mulDet ^ ((finrank ℚ K : ℝ))⁻¹

theorem mulDet_pos : 0 < L.mulDet := by
  refine mul_pos (Finset.prod_pos fun v _ ↦ pow_pos
    (InfinitePlace.pos_iff.mpr (L.arch_det_ne_zero v)) _) ?_
  rw [finprod_eq_prod _ L.hasFiniteMulSupport_det_fin]
  exact Finset.prod_pos fun v _ ↦ FinitePlace.pos_iff.mpr (L.fin_det_ne_zero v)

theorem absDet_pos : 0 < L.absDet :=
  Real.rpow_pos_of_pos L.mulDet_pos _

/-- **EF13 Lemma 7.3 (iv)**: `Δ_{L ∘ P} = Δ_L`, by the product formula for `det P`. -/
theorem mulDet_comp (P : Matrix ι ι K) (hP : P.det ≠ 0) : (L.comp P hP).mulDet = L.mulDet := by
  have hprod := prod_abs_eq_one hP
  simp only [mulDet, comp, det_mul, map_mul, mul_pow]
  rw [Finset.prod_mul_distrib, finprod_mul_distrib L.hasFiniteMulSupport_det_fin
    (FinitePlace.hasFiniteMulSupport hP)]
  calc (∏ v : InfinitePlace K, v (L.arch v).det ^ v.mult) *
        (∏ v : InfinitePlace K, v P.det ^ v.mult) *
        ((∏ᶠ v : FinitePlace K, v (L.fin v).det) * ∏ᶠ v : FinitePlace K, v P.det)
      = L.mulDet *
        ((∏ v : InfinitePlace K, v P.det ^ v.mult) * ∏ᶠ v : FinitePlace K, v P.det) := by
        rw [mulDet]; ring
    _ = L.mulDet := by rw [hprod, mul_one]

theorem absDet_comp (P : Matrix ι ι K) (hP : P.det ≠ 0) : (L.comp P hP).absDet = L.absDet := by
  rw [absDet, absDet, mulDet_comp]

end Det

/-! ### The forms of the system and `H_L` (EF13 (2.6), (2.12), (7.4)) -/

section Forms

/-- The set of all forms of the system, `{L_1, …, L_r}` of EF13 (2.6). -/
def formSet : Set (ι → K) := {f | ∃ v i, L.arch v i = f} ∪ {f | ∃ v i, L.fin v i = f}

theorem finite_formSet : L.formSet.Finite := by
  -- `rintro`, not `fun f ⟨v, i, h⟩ ↦ …`: `forms` carries this proof in its value, and a pattern
  -- lambda mints a `private` matcher that comparator cannot compare (`COMPARATOR.md`).
  refine Set.Finite.union ?_ ?_
  · refine (Set.finite_range fun p : InfinitePlace K × ι ↦ L.arch p.1 p.2).subset ?_
    rintro f ⟨v, i, h⟩
    exact ⟨(v, i), h⟩
  · have : Finite (Set.range L.fin) := L.finite_range_fin
    refine (Set.finite_iUnion fun M : Set.range L.fin ↦ Set.finite_range M.1).subset ?_
    rintro f ⟨v, i, h⟩
    exact Set.mem_iUnion.mpr ⟨⟨_, v, rfl⟩, i, h⟩

/-- The forms `L_1, …, L_r` as a finset. -/
noncomputable def forms : Finset (ι → K) := L.finite_formSet.toFinset

theorem arch_mem_forms (v : InfinitePlace K) (i : ι) : L.arch v i ∈ L.forms :=
  L.finite_formSet.mem_toFinset.mpr (Or.inl ⟨v, i, rfl⟩)

theorem fin_mem_forms (v : FinitePlace K) (i : ι) : L.fin v i ∈ L.forms :=
  L.finite_formSet.mem_toFinset.mpr (Or.inr ⟨v, i, rfl⟩)

open scoped Classical in
/-- The determinants `det(L_{i_1}, …, L_{i_n})` of `n`-tuples of forms of the system. -/
noncomputable def detSet : Finset K :=
  (Fintype.piFinset fun _ : ι ↦ L.forms).image fun M ↦ (Matrix.of M).det

open scoped Classical in
theorem det_arch_mem_detSet (v : InfinitePlace K) : (L.arch v).det ∈ L.detSet :=
  Finset.mem_image.mpr ⟨L.arch v, Fintype.mem_piFinset.mpr (L.arch_mem_forms v), rfl⟩

open scoped Classical in
theorem det_fin_mem_detSet (v : FinitePlace K) : (L.fin v).det ∈ L.detSet :=
  Finset.mem_image.mpr ⟨L.fin v, Fintype.mem_piFinset.mpr (L.fin_mem_forms v), rfl⟩

theorem le_iSup_detSet (f : K → ℝ) {d : K} (hd : d ∈ L.detSet) : f d ≤ ⨆ e : L.detSet, f e :=
  Finite.le_ciSup_of_le (f := fun e : L.detSet ↦ f e) ⟨d, hd⟩ le_rfl

theorem iSup_detSet_nonneg (f : AbsoluteValue K ℝ) : 0 ≤ ⨆ e : L.detSet, f e :=
  Real.iSup_nonneg fun _ ↦ apply_nonneg _ _

theorem hasFiniteMulSupport_iSup_detSet :
    (fun v : FinitePlace K ↦ ⨆ e : L.detSet, v e).HasFiniteMulSupport := by
  have hfin : ∀ e : {e // e ∈ L.detSet ∧ e ≠ 0},
      (fun v : FinitePlace K ↦ v e.1).HasFiniteMulSupport :=
    fun e ↦ FinitePlace.hasFiniteMulSupport e.2.2
  have : Finite {e // e ∈ L.detSet ∧ e ≠ 0} :=
    Finite.of_injective (fun e ↦ (⟨e.1, e.2.1⟩ : L.detSet)) fun a b h ↦
      Subtype.ext (by simpa using congrArg Subtype.val h)
  refine (Set.finite_iUnion fun e ↦ hfin e).subset fun v hv ↦ ?_
  by_contra hcon
  simp only [Set.mem_iUnion, not_exists, mem_mulSupport, not_not] at hcon
  have : Nonempty L.detSet := ⟨⟨_, L.det_fin_mem_detSet v⟩⟩
  refine hv (le_antisymm (ciSup_le fun e ↦ ?_) ?_)
  · rcases eq_or_ne e.1 0 with h | h
    · simp [h]
    · exact (hcon ⟨e.1, e.2, h⟩).le
  · rw [← hcon ⟨_, L.det_fin_mem_detSet v, L.fin_det_ne_zero v⟩]
    exact L.le_iSup_detSet _ (L.det_fin_mem_detSet v)

/-- `H_L` of EF13 (2.12), relative to `K`. -/
noncomputable def mulFormHeight : ℝ :=
  (∏ v : InfinitePlace K, (⨆ e : L.detSet, v e) ^ v.mult) *
    ∏ᶠ v : FinitePlace K, ⨆ e : L.detSet, v e

/-- **`H_L`** of EF13 (2.12): `∏_v max ‖det(L_{i_1}, …, L_{i_n})‖_v` over the `n`-tuples of
forms of the system. -/
noncomputable def absFormHeight : ℝ :=
  L.mulFormHeight ^ ((finrank ℚ K : ℝ))⁻¹

/-- A product over all places of local bounds `f_v ≤ g_v`. -/
private theorem prod_places_le {F : Type*} [Field F] [NumberField F] {f g : InfinitePlace F → ℝ}
    {f' g' : FinitePlace F → ℝ}
    (hf : ∀ v, 0 ≤ f v) (hf' : ∀ v, 0 ≤ f' v) (hfs : f'.HasFiniteMulSupport)
    (hgs : g'.HasFiniteMulSupport) (h : ∀ v, f v ≤ g v) (h' : ∀ v, f' v ≤ g' v) :
    (∏ v, f v ^ v.mult) * ∏ᶠ v, f' v ≤ (∏ v, g v ^ v.mult) * ∏ᶠ v, g' v :=
  mul_le_mul (Finset.prod_le_prod₀ (fun v _ ↦ pow_nonneg (hf v) _)
      fun v _ ↦ pow_le_pow_left₀ (hf v) (h v) _)
    (Twist.finprod_le_finprod_of_nonneg hfs hgs hf' h')
    (finprod_nonneg hf') (Finset.prod_nonneg fun v _ ↦ pow_nonneg ((hf v).trans (h v)) _)

/-- `Δ_L ≤ H_L`, relative form. -/
theorem mulDet_le_mulFormHeight : L.mulDet ≤ L.mulFormHeight :=
  prod_places_le (fun _ ↦ apply_nonneg _ _) (fun _ ↦ apply_nonneg _ _)
    L.hasFiniteMulSupport_det_fin L.hasFiniteMulSupport_iSup_detSet
    (fun v ↦ L.le_iSup_detSet _ (L.det_arch_mem_detSet v))
    fun v ↦ L.le_iSup_detSet _ (L.det_fin_mem_detSet v)

/-- **EF13 (7.4), upper half**: `Δ_L ≤ H_L`. -/
theorem absDet_le_absFormHeight : L.absDet ≤ L.absFormHeight :=
  Real.rpow_le_rpow L.mulDet_pos.le L.mulDet_le_mulFormHeight (by positivity)

/-- `H_L ≥ 1`, relative form: the product formula for one nonzero determinant. -/
theorem one_le_mulFormHeight : 1 ≤ L.mulFormHeight := by
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hd := L.det_arch_mem_detSet v₀
  have hne := L.arch_det_ne_zero v₀
  rw [← prod_abs_eq_one hne]
  exact prod_places_le (fun _ ↦ apply_nonneg _ _) (fun _ ↦ apply_nonneg _ _)
    (FinitePlace.hasFiniteMulSupport hne) L.hasFiniteMulSupport_iSup_detSet
    (fun v ↦ L.le_iSup_detSet _ hd) fun v ↦ L.le_iSup_detSet _ hd

omit [NumberField K] in
open scoped Classical in
/-- Two injective `n`-tuples of rows with the same set of rows have the same squared
determinant. -/
theorem det_sq_eq_of_image_eq {M N : ι → ι → K} (hN : Function.Injective N)
    (h : Finset.univ.image M = Finset.univ.image N) :
    (Matrix.of N).det ^ 2 = (Matrix.of M).det ^ 2 := by
  classical
  have hex : ∀ i, ∃ j, M j = N i := fun i ↦ by
    have : N i ∈ Finset.univ.image M := h ▸ Finset.mem_image_of_mem N (Finset.mem_univ i)
    simpa using this
  choose τ hτ using hex
  have hτinj : Function.Injective τ := fun i j hij ↦ hN (by rw [← hτ, ← hτ, hij])
  set σ := Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτinj)
  have hNM : Matrix.of N = (Matrix.of M).submatrix σ id := by
    ext i j
    simp [σ, ← hτ]
  rw [hNM, det_permute, mul_pow, ← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq]
  simp

open scoped Classical in
/-- The number of distinct squared nonzero determinants is at most `C(r, n)`. -/
theorem card_detSq_le :
    ((L.detSet.filter (· ≠ 0)).image (· ^ 2)).card ≤ L.forms.card.choose (Fintype.card ι) := by
  classical
  rw [← Finset.card_powersetCard]
  have hex : ∀ e : K, ∃ M : ι → ι → K, e ∈ (L.detSet.filter (· ≠ 0)).image (· ^ 2) →
      M ∈ Fintype.piFinset (fun _ : ι ↦ L.forms) ∧ (Matrix.of M).det ≠ 0 ∧
        (Matrix.of M).det ^ 2 = e := fun e ↦ by
    by_cases he : e ∈ (L.detSet.filter (· ≠ 0)).image (· ^ 2)
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hd, hd0⟩ := Finset.mem_filter.mp hd
      obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hd
      exact ⟨M, fun _ ↦ ⟨hM, hd0, rfl⟩⟩
    · exact ⟨0, fun h ↦ absurd h he⟩
  choose M hM using hex
  have hinj : ∀ {e}, e ∈ (L.detSet.filter (· ≠ 0)).image (· ^ 2) → Function.Injective (M e) :=
    fun he i j hij ↦ by
      by_contra hne
      exact (hM _ he).2.1 (Matrix.det_zero_of_row_eq hne hij)
  refine Finset.card_le_card_of_injOn (fun e ↦ Finset.univ.image (M e)) (fun e he ↦ ?_)
    fun e he e' he' hee' ↦ ?_
  · refine Finset.mem_powersetCard.mpr ⟨fun f hf ↦ ?_, ?_⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hf
      exact Fintype.mem_piFinset.mp (hM _ he).1 i
    · rw [Finset.card_image_of_injective _ (hinj he), Finset.card_univ]
  · rw [← (hM _ he).2.2, ← (hM _ he').2.2]
    exact det_sq_eq_of_image_eq (hinj he) hee'.symm

/-- **EF13 (7.4), lower half**, relative form: `H_L ^ {1 - C(r, n)} ≤ Δ_L`. -/
theorem mulFormHeight_rpow_le_mulDet :
    L.mulFormHeight ^ ((1 : ℝ) - L.forms.card.choose (Fintype.card ι)) ≤ L.mulDet := by
  classical
  set D := (L.detSet.filter (· ≠ 0)).image (· ^ 2)
  set t := D.card
  have hD0 : ∀ e ∈ D, e ≠ 0 := fun e he ↦ by
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    exact pow_ne_zero 2 (Finset.mem_filter.mp hd).2
  have hDle : ∀ (f : AbsoluteValue K ℝ), ∀ e ∈ D, f e ≤ (⨆ e : L.detSet, f e) ^ 2 :=
    fun f e he ↦ by
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
      rw [map_pow]
      exact pow_le_pow_left₀ (apply_nonneg _ _)
        (L.le_iSup_detSet _ (Finset.mem_filter.mp hd).1) 2
  have hmem : ∀ d, d ∈ L.detSet → d ≠ 0 → d ^ 2 ∈ D := fun d hd hd0 ↦
    Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨hd, hd0⟩, rfl⟩
  -- the local inequality `|p| ≤ |d|² · max^{2(t-1)}` for `p = ∏ D` and `d ∈ D`
  have hloc : ∀ (f : AbsoluteValue K ℝ) {d : K}, d ∈ L.detSet → d ≠ 0 →
      f (∏ e ∈ D, e) ≤ f d ^ 2 * ((⨆ e : L.detSet, f e) ^ 2) ^ (t - 1) := fun f d hd hd0 ↦ by
    rw [← Finset.mul_prod_erase D (fun e ↦ e) (hmem d hd hd0), map_mul, map_prod, map_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∏ e ∈ D.erase (d ^ 2), f e ≤ ∏ _e ∈ D.erase (d ^ 2), (⨆ e : L.detSet, f e) ^ 2 :=
          Finset.prod_le_prod₀ (fun _ _ ↦ apply_nonneg _ _)
            fun e he ↦ hDle f e (Finset.mem_of_mem_erase he)
      _ = _ := by rw [Finset.prod_const, Finset.card_erase_of_mem (hmem d hd hd0)]
  have hp : (∏ e ∈ D, e) ≠ 0 := Finset.prod_ne_zero_iff.mpr hD0
  set H := L.mulFormHeight
  have hH : 1 ≤ H := L.one_le_mulFormHeight
  have hm := L.mulDet_pos
  -- the product over the places
  have hb := L.hasFiniteMulSupport_det_fin
  have hN := L.hasFiniteMulSupport_iSup_detSet
  set S := hb.toFinset ∪ hN.toFinset
  have hS : ∀ {g : FinitePlace K → ℝ}, (∀ v, v ∉ S → g v = 1) → ∏ᶠ v, g v = ∏ v ∈ S, g v :=
    fun {g} hg ↦ finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ by
      by_contra h
      exact hv (hg v h)
  have hbS : ∀ v, v ∉ S → v (L.fin v).det = 1 := fun v hv ↦ by
    by_contra h
    exact hv (Finset.mem_union_left _ (hb.mem_toFinset.mpr h))
  have hNS : ∀ v, v ∉ S → (⨆ e : L.detSet, v e) = 1 := fun v hv ↦ by
    by_contra h
    exact hv (Finset.mem_union_right _ (hN.mem_toFinset.mpr h))
  have hprod : 1 ≤ (L.mulDet * H ^ (t - 1)) ^ 2 := by
    rw [← prod_abs_eq_one hp]
    calc (∏ v : InfinitePlace K, v (∏ e ∈ D, e) ^ v.mult) * ∏ᶠ v : FinitePlace K, v (∏ e ∈ D, e)
        ≤ (∏ v : InfinitePlace K, (v (L.arch v).det ^ 2 *
            ((⨆ e : L.detSet, v e) ^ 2) ^ (t - 1)) ^ v.mult) *
          ∏ᶠ v : FinitePlace K, (v (L.fin v).det ^ 2 * ((⨆ e : L.detSet, v e) ^ 2) ^ (t - 1)) :=
          prod_places_le (fun _ ↦ apply_nonneg _ _) (fun _ ↦ apply_nonneg _ _)
            (FinitePlace.hasFiniteMulSupport hp)
            (Set.Finite.subset S.finite_toSet fun v hv ↦ by
              by_contra h
              exact hv (by simp [hbS v h, hNS v h]))
            (fun v ↦ hloc v.1 (L.det_arch_mem_detSet v) (L.arch_det_ne_zero v))
            fun v ↦ hloc v.1 (L.det_fin_mem_detSet v) (L.fin_det_ne_zero v)
      _ = (L.mulDet * H ^ (t - 1)) ^ 2 := by
          rw [hS fun v hv ↦ by simp [hbS v hv, hNS v hv]]
          simp only [H, mulFormHeight, mulDet]
          rw [hS fun v hv ↦ hbS v hv, hS fun v hv ↦ hNS v hv]
          have harch : ∀ v : InfinitePlace K, (v (L.arch v).det ^ 2 *
              ((⨆ e : L.detSet, v e) ^ 2) ^ (t - 1)) ^ v.mult =
              (v (L.arch v).det ^ v.mult) ^ 2 * ((⨆ e : L.detSet, v e) ^ v.mult) ^ (2 * (t - 1)) :=
            fun v ↦ by ring
          rw [Finset.prod_congr rfl fun v _ ↦ harch v]
          simp only [Finset.prod_mul_distrib, Finset.prod_pow]
          ring
  have h1 : 1 ≤ L.mulDet * H ^ (t - 1) := by
    by_contra hlt
    push Not at hlt
    have := pow_lt_one₀ (by positivity) hlt (two_ne_zero)
    linarith
  have ht : t ≤ L.forms.card.choose (Fintype.card ι) := L.card_detSq_le
  have ht1 : 1 ≤ t := Finset.card_pos.mpr
    ⟨_, hmem _ (L.det_arch_mem_detSet (Classical.arbitrary _)) (L.arch_det_ne_zero _)⟩
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  calc H ^ ((1 : ℝ) - L.forms.card.choose (Fintype.card ι)) ≤ H ^ ((1 : ℝ) - t) :=
        Real.rpow_le_rpow_of_exponent_le hH (by
          have : (t : ℝ) ≤ ((L.forms.card.choose (Fintype.card ι) : ℕ) : ℝ) := by exact_mod_cast ht
          linarith)
    _ = (H ^ (t - 1))⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_neg hH0.le, Nat.cast_sub ht1]
        congr 1
        push_cast
        ring
    _ ≤ L.mulDet := by
        rw [inv_le_iff_one_le_mul₀ (pow_pos hH0 _)]
        exact h1

/-- **EF13 (7.4)**, lower half: `H_L ^ {1 - C(r, n)} ≤ Δ_L`, `r` the number of distinct forms. -/
theorem absFormHeight_rpow_le_absDet :
    L.absFormHeight ^ ((1 : ℝ) - L.forms.card.choose (Fintype.card ι)) ≤ L.absDet := by
  have hH0 : 0 ≤ L.mulFormHeight := zero_le_one.trans L.one_le_mulFormHeight
  rw [absFormHeight, absDet, ← Real.rpow_mul hH0, mul_comm, Real.rpow_mul hH0]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hH0 _) L.mulFormHeight_rpow_le_mulDet (by positivity)

end Forms

/-! ### A lower bound for the twisted height (EF13 Lemma 7.1) -/

section LowerBound

omit [NumberField K] in
/-- **Cramer's rule, row form**: `(P adj B)_{ij} = det(B with row j replaced by P_i)`. -/
theorem mul_adjugate_apply_eq_det_updateRow (P B : Matrix ι ι K) (i j : ι) :
    (P * B.adjugate) i j = (B.updateRow j (P i)).det := by
  rw [← cramer_transpose_apply, cramer_eq_adjugate_mulVec, ← adjugate_transpose]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

open scoped Classical in
/-- The entries of `P B⁻¹`, for `P`, `B` with rows among the forms of the system, are
quotients of elements of `detSet` by `det B`. -/
theorem apply_mul_inv_le (f : AbsoluteValue K ℝ) {B P : Matrix ι ι K}
    (hB : ∀ i, B i ∈ L.forms) (hP : ∀ i, P i ∈ L.forms) (i j : ι) :
    f ((P * B⁻¹) i j) ≤ (⨆ e : L.detSet, f e) / f B.det := by
  have hmem : (B.updateRow j (P i)).det ∈ L.detSet := by
    refine Finset.mem_image.mpr ⟨B.updateRow j (P i), Fintype.mem_piFinset.mpr fun k ↦ ?_, rfl⟩
    rcases eq_or_ne k j with rfl | hk
    · simpa using hP i
    · simpa [hk] using hB k
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul, Matrix.smul_apply,
    mul_adjugate_apply_eq_det_updateRow, smul_eq_mul, map_mul, map_inv₀, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (L.le_iSup_detSet _ hmem) (apply_nonneg _ _)

/-- The largest weight at each place, and their product `A` over the places of `K`. -/
noncomputable def _root_.NumberField.FormWeight.mulMax (a : FormWeight K ι) : ℝ :=
  (∏ v : InfinitePlace K, (⨆ i, a.arch v i) ^ v.mult) * ∏ᶠ v : FinitePlace K, ⨆ i, a.fin v i

/-- The local constant at an infinite place of `K`. -/
noncomputable def archBound (v : InfinitePlace K) : ℝ :=
  (⨆ e : L.detSet, v e) / v (L.arch v).det * ⨆ i, a.arch v i

/-- The local constant at a finite place of `K`. -/
noncomputable def finBound (v : FinitePlace K) : ℝ :=
  (⨆ e : L.detSet, v e) / v (L.fin v).det * ⨆ i, a.fin v i

variable [Nonempty ι]

omit [Fintype ι] [DecidableEq ι] in
theorem hasFiniteMulSupport_iSup_fin :
    (fun v : FinitePlace K ↦ ⨆ i, a.fin v i).HasFiniteMulSupport :=
  a.finite_setOf_fin_ne_one.subset fun v hv h ↦ hv (by simp [h])

omit [Fintype ι] [DecidableEq ι] in
theorem mulMax_pos [Finite ι] : 0 < a.mulMax := by
  refine mul_pos (Finset.prod_pos fun v _ ↦ pow_pos ?_ _) ?_
  · exact (a.arch_pos v (Classical.arbitrary ι)).trans_le
      (Finite.le_ciSup_of_le (Classical.arbitrary ι) le_rfl)
  · rw [finprod_eq_prod _ (hasFiniteMulSupport_iSup_fin a)]
    exact Finset.prod_pos fun v _ ↦ (a.fin_pos v (Classical.arbitrary ι)).trans_le
      (Finite.le_ciSup_of_le (Classical.arbitrary ι) le_rfl)

theorem hasFiniteMulSupport_finBound : (L.finBound a).HasFiniteMulSupport :=
  ((L.hasFiniteMulSupport_iSup_detSet.union L.hasFiniteMulSupport_det_fin).union
    (hasFiniteMulSupport_iSup_fin a)).subset fun v hv ↦ by
      by_contra h
      simp only [Set.mem_union, mem_mulSupport, not_or, not_not] at h
      exact hv (by simp [finBound, h.1.1, h.1.2, h.2])

omit [NumberField E] in
/-- The local bound at an infinite place of `E`. -/
theorem iSup_arch_le (v₀ : InfinitePlace K) (w : InfinitePlace E) (x : ι → E) :
    ⨆ i, w (((L.arch v₀).map (algebraMap K E) *ᵥ x) i) ≤
      Fintype.card ι * (L.archBound a (w.comap (algebraMap K E)) * L.archFactor a w x) := by
  set v := w.comap (algebraMap K E)
  set B := L.arch v
  set C := L.arch v₀ * B⁻¹
  have hy : (L.arch v₀).map (algebraMap K E) *ᵥ x =
      C.map (algebraMap K E) *ᵥ (B.map (algebraMap K E) *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul,
      Matrix.nonsing_inv_mul_cancel_right _ _ (L.arch_det_ne_zero v).isUnit]
  have hC : ∀ i j, w ((C.map (algebraMap K E)) i j) ≤ (⨆ e : L.detSet, v e) / v B.det :=
    fun i j ↦ by
      rw [Matrix.map_apply, ← InfinitePlace.comap_apply]
      exact L.apply_mul_inv_le v.1 (L.arch_mem_forms v) (L.arch_mem_forms v₀) i j
  have hBx : ∀ j, w ((B.map (algebraMap K E) *ᵥ x) j) ≤
      L.archFactor a w x * ⨆ i, a.arch v i := fun j ↦ by
    have hpos := a.arch_pos v j
    calc w ((B.map (algebraMap K E) *ᵥ x) j)
        = w ((B.map (algebraMap K E) *ᵥ x) j) / a.arch v j * a.arch v j := by field_simp
      _ ≤ L.archFactor a w x * ⨆ i, a.arch v i :=
          mul_le_mul (Finite.le_ciSup_of_le j le_rfl) (Finite.le_ciSup_of_le j le_rfl)
            hpos.le (L.archFactor_nonneg a w x)
  rw [hy]
  refine ciSup_le fun i ↦ ?_
  calc w ((C.map (algebraMap K E) *ᵥ (B.map (algebraMap K E) *ᵥ x)) i)
      ≤ ∑ j, w ((C.map (algebraMap K E)) i j) * w ((B.map (algebraMap K E) *ᵥ x) j) := by
        simp only [Matrix.mulVec, dotProduct, ← map_mul]
        exact AbsoluteValue.sum_le _ _ _
    _ ≤ ∑ _j : ι, (⨆ e : L.detSet, v e) / v B.det *
          (L.archFactor a w x * ⨆ i, a.arch v i) :=
        Finset.sum_le_sum fun j _ ↦ mul_le_mul (hC i j) (hBx j) (apply_nonneg _ _)
          (div_nonneg (L.iSup_detSet_nonneg v.1) (apply_nonneg _ _))
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, archBound]
        ring

/-- The local bound at a finite place of `E`. -/
theorem iSup_fin_le (v₀ : InfinitePlace K) (w : FinitePlace E) (x : ι → E) :
    ⨆ i, w (((L.arch v₀).map (algebraMap K E) *ᵥ x) i) ≤
      L.finBound a (w.under K) ^ w.localDegree K * L.finFactor a w x := by
  set v := w.under K
  set e := w.localDegree K
  set B := L.fin v
  set C := L.arch v₀ * B⁻¹
  have hy : (L.arch v₀).map (algebraMap K E) *ᵥ x =
      C.map (algebraMap K E) *ᵥ (B.map (algebraMap K E) *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul,
      Matrix.nonsing_inv_mul_cancel_right _ _ (L.fin_det_ne_zero v).isUnit]
  have hC : ∀ i j, w ((C.map (algebraMap K E)) i j) ≤ ((⨆ e : L.detSet, v e) / v B.det) ^ e :=
    fun i j ↦ by
      rw [Matrix.map_apply, FinitePlace.apply_algebraMap w v]
      exact pow_le_pow_left₀ (apply_nonneg _ _) (L.apply_mul_inv_le v.1 (L.fin_mem_forms v)
        (L.arch_mem_forms v₀) i j) _
  have hBx : ∀ j, w ((B.map (algebraMap K E) *ᵥ x) j) ≤
      L.finFactor a w x * (⨆ i, a.fin v i) ^ e := fun j ↦ by
    have hpos := pow_pos (a.fin_pos v j) e
    calc w ((B.map (algebraMap K E) *ᵥ x) j)
        = w ((B.map (algebraMap K E) *ᵥ x) j) / a.fin v j ^ e * a.fin v j ^ e := by field_simp
      _ ≤ L.finFactor a w x * (⨆ i, a.fin v i) ^ e :=
          mul_le_mul (Finite.le_ciSup_of_le j le_rfl)
            (pow_le_pow_left₀ (a.fin_pos v j).le (Finite.le_ciSup_of_le j le_rfl) _)
            hpos.le (L.finFactor_nonneg a w x)
  have hna : IsNonarchimedean (w ·) := FinitePlace.add_le w
  rw [hy]
  refine ciSup_le fun i ↦ ?_
  obtain ⟨j, -, hj⟩ := hna.finset_image_add_of_nonempty
    (fun j ↦ (C.map (algebraMap K E)) i j * (B.map (algebraMap K E) *ᵥ x) j)
    (univ_nonempty (α := ι))
  refine hj.trans ?_
  rw [map_mul, finBound, mul_pow]
  calc w ((C.map (algebraMap K E)) i j) * w ((B.map (algebraMap K E) *ᵥ x) j)
      ≤ ((⨆ e : L.detSet, v e) / v B.det) ^ e * (L.finFactor a w x * (⨆ i, a.fin v i) ^ e) :=
        mul_le_mul (hC i j) (hBx j) (apply_nonneg _ _)
          (pow_nonneg (div_nonneg (L.iSup_detSet_nonneg v.1) (apply_nonneg _ _)) _)
    _ = _ := by ring

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- The max norm of a nonzero point is `1` at all but finitely many finite places. -/
theorem hasFiniteMulSupport_iSup_apply [Finite ι] {y : ι → E} (hy : y ≠ 0) :
    (fun w : FinitePlace E ↦ ⨆ i, w (y i)).HasFiniteMulSupport := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hy
  have : Nonempty ι := ⟨i₀⟩
  have hfin : ∀ i : {i // y i ≠ 0}, (fun w : FinitePlace E ↦ w (y i)).HasFiniteMulSupport :=
    fun i ↦ FinitePlace.hasFiniteMulSupport i.2
  refine (Set.finite_iUnion fun i ↦ hfin i).subset fun w hw ↦ ?_
  by_contra hcon
  simp only [Set.mem_iUnion, not_exists, mem_mulSupport, not_not] at hcon
  refine hw (le_antisymm (ciSup_le fun i ↦ ?_) ?_)
  · rcases eq_or_ne (y i) 0 with h | h
    · simp [h]
    · exact (hcon ⟨i, h⟩).le
  · exact (hcon ⟨i₀, hi₀⟩).ge.trans (Finite.le_ciSup_of_le i₀ le_rfl)

/-- **The lower bound for the twisted height**, relative to `E`: with
`R = ∏_v archBound_v ^ {mult v} · ∏_v finBound_v`, `1 ≤ n ^ {[E:ℚ]} R ^ {[E:K]} H_{L,a}(x)`. -/
theorem one_le_mulHeight {x : ι → E} (hx : x ≠ 0) :
    1 ≤ (Fintype.card ι : ℝ) ^ finrank ℚ E *
      ((∏ v, L.archBound a v ^ v.mult) * ∏ᶠ v, L.finBound a v) ^ finrank K E *
        L.mulHeight a x := by
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  set y := (L.arch v₀).map (algebraMap K E) *ᵥ x
  have hy : y ≠ 0 := mulVec_ne_zero_of_det_ne_zero (L.arch_det_ne_zero v₀) hx
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hy
  have hFF := L.hasFiniteMulSupport_finFactor a hx
  have hFB : (fun w : FinitePlace E ↦
      L.finBound a (w.under K) ^ w.localDegree K).HasFiniteMulSupport :=
    FinitePlace.hasFiniteMulSupport_comp_under (L.hasFiniteMulSupport_finBound a) _
  have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hAB : ∀ v, 0 ≤ L.archBound a v := fun v ↦
    mul_nonneg (div_nonneg (L.iSup_detSet_nonneg v.1) (apply_nonneg _ _))
      (Real.iSup_nonneg fun i ↦ (a.arch_pos v i).le)
  calc (1 : ℝ) = (∏ w : InfinitePlace E, w (y i₀) ^ w.mult) * ∏ᶠ w : FinitePlace E, w (y i₀) :=
        (prod_abs_eq_one hi₀).symm
    _ ≤ (∏ w : InfinitePlace E, (⨆ i, w (y i)) ^ w.mult) * ∏ᶠ w : FinitePlace E, ⨆ i, w (y i) :=
        prod_places_le (fun _ ↦ apply_nonneg _ _) (fun _ ↦ apply_nonneg _ _)
          (FinitePlace.hasFiniteMulSupport hi₀) (hasFiniteMulSupport_iSup_apply hy)
          (fun w ↦ Finite.le_ciSup_of_le (f := fun i ↦ w (y i)) i₀ le_rfl)
          fun w ↦ Finite.le_ciSup_of_le (f := fun i ↦ w (y i)) i₀ le_rfl
    _ ≤ (∏ w : InfinitePlace E, ((Fintype.card ι : ℝ) *
          (L.archBound a (w.comap (algebraMap K E)) * L.archFactor a w x)) ^ w.mult) *
        ∏ᶠ w : FinitePlace E, L.finBound a (w.under K) ^ w.localDegree K * L.finFactor a w x :=
        prod_places_le (fun _ ↦ Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)
          (fun _ ↦ Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)
          (hasFiniteMulSupport_iSup_apply hy)
          ((hFB.union hFF).subset (Function.mulSupport_mul _ _))
          (fun w ↦ L.iSup_arch_le a v₀ w x) fun w ↦ L.iSup_fin_le a v₀ w x
    _ = _ := by
        have h1 : ∏ w : InfinitePlace E, (Fintype.card ι : ℝ) ^ w.mult =
            (Fintype.card ι : ℝ) ^ finrank ℚ E := by
          rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
        have h2 : ∏ w : InfinitePlace E, L.archBound a (w.comap (algebraMap K E)) ^ w.mult =
            (∏ v, L.archBound a v ^ v.mult) ^ finrank K E :=
          prod_infinitePlace_pow_mult_eq _ (fun w ↦ L.archBound a (w.comap (algebraMap K E)))
            fun _ ↦ rfl
        have h3 : ∏ᶠ w : FinitePlace E, L.finBound a (w.under K) ^ w.localDegree K =
            (∏ᶠ v, L.finBound a v) ^ finrank K E :=
          FinitePlace.finprod_under_pow_localDegree _ (L.hasFiniteMulSupport_finBound a)
        simp only [mul_pow, Finset.prod_mul_distrib]
        rw [finprod_mul_distrib hFB hFF, h1, h2, h3, mulHeight]
        ring

/-- The product of the local constants is `(H_L / Δ_L) · A`, relative to `K`. -/
theorem prod_bound_eq :
    (∏ v, L.archBound a v ^ v.mult) * ∏ᶠ v, L.finBound a v =
      L.mulFormHeight / L.mulDet * a.mulMax := by
  have hM := L.hasFiniteMulSupport_iSup_detSet
  have hD := L.hasFiniteMulSupport_det_fin
  have hA := hasFiniteMulSupport_iSup_fin a
  have hMD : (fun v : FinitePlace K ↦
      (⨆ e : L.detSet, v e) / v (L.fin v).det).HasFiniteMulSupport :=
    (hM.union hD).subset (Function.mulSupport_div _ _)
  simp only [archBound, finBound, mul_pow, div_pow, Finset.prod_mul_distrib,
    Finset.prod_div_distrib]
  rw [finprod_mul_distrib hMD hA, finprod_div_distrib hM hD, mulFormHeight, mulDet,
    FormWeight.mulMax]
  ring

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

/-- **The lower bound for the absolute twisted height** (EF13 Lemma 7.1, general weights):
`1 ≤ n ((H_L / Δ_L) · A) ^ {1 / [K:ℚ]} · H_{L,a}(x)` for `x ≠ 0`, `A` the product over the places
of the largest weights. -/
theorem one_le_absMulHeight {x : ι → Ω} (hx : x ≠ 0) :
    1 ≤ Fintype.card ι * (L.mulFormHeight / L.mulDet * a.mulMax) ^ ((finrank ℚ K : ℝ))⁻¹ *
      L.absMulHeight a x := by
  have := Twist.numberField_adjoin_range (K := K) x
  have : Module.Finite K (IntermediateField.adjoin K (Set.range x)) :=
    Module.Finite.of_restrictScalars_finite ℚ K _
  set F := IntermediateField.adjoin K (Set.range x)
  set y : ι → F := fun i ↦ ⟨x i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have hy : y ≠ 0 := fun h ↦ hx (funext fun i ↦ by
    have := congrArg Subtype.val (congrFun h i)
    simpa [y] using this)
  have h := L.one_le_mulHeight a hy
  rw [prod_bound_eq] at h
  have hR : 0 < L.mulFormHeight / L.mulDet * a.mulMax :=
    mul_pos (div_pos (zero_lt_one.trans_le L.one_le_mulFormHeight) L.mulDet_pos) (mulMax_pos a)
  have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hdF : finrank ℚ F ≠ 0 := finrank_pos.ne'
  have hH := L.mulHeight_nonneg a y
  have h' := Real.rpow_le_rpow zero_le_one h (inv_nonneg.mpr (Nat.cast_nonneg (finrank ℚ F)))
  rwa [Real.one_rpow, Real.mul_rpow (by positivity) hH,
    Real.mul_rpow (pow_nonneg hn _) (pow_nonneg hR.le _), Real.pow_rpow_inv_natCast hn hdF,
    rpow_finrank_inv hR, ← absMulHeight] at h'

end LowerBound

end FormSystem

/-! ### EF13's weights `Q ^ c_iv` -/

/-- **Exponents** `c = (c_iv)` of EF13 (2.7): reals at every place and index, `0` at all but
finitely many finite places. -/
structure FormExponent where
  /-- The exponents at the infinite places. -/
  arch : InfinitePlace K → ι → ℝ
  /-- The exponents at the finite places. -/
  fin : FinitePlace K → ι → ℝ
  finite_setOf_fin_ne_zero : {v | fin v ≠ 0}.Finite

namespace FormExponent

variable {K ι} (c : FormExponent K ι) {Q : ℝ} (hQ : 0 < Q)

/-- **The weights `Q ^ c_iv`** of EF13 (2.13), in the relative normalization of the module doc:
`Q ^ {c_iv [K:ℚ] / mult v}` at an infinite place, `Q ^ {c_iv [K:ℚ]}` at a finite one. Then
`FormSystem.absMulHeight L (c.weight hQ)` is EF13's `H_{L,c,Q}`. -/
noncomputable def weight : FormWeight K ι where
  arch v i := Q ^ (c.arch v i * finrank ℚ K / v.mult)
  arch_pos _ _ := Real.rpow_pos_of_pos hQ _
  fin v i := Q ^ (c.fin v i * finrank ℚ K)
  fin_pos _ _ := Real.rpow_pos_of_pos hQ _
  finite_setOf_fin_ne_one := c.finite_setOf_fin_ne_zero.subset fun v hv h ↦ hv <| by
    funext i
    simp [h]

end FormExponent

namespace FormSystem

variable {K ι} (L : FormSystem K ι)
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

/-- **EF13 Lemma 7.2 (i)**: shifting the exponents at each place by `θ_v` multiplies
`H_{L,c,Q}` by `Q ^ Θ`, `Θ = Σ_v θ_v`. -/
theorem absMulHeight_weight_of_sub {c d : FormExponent K ι} {θa : InfinitePlace K → ℝ}
    {θf : FinitePlace K → ℝ} (hθ : (Function.support θf).Finite)
    (harch : ∀ v i, d.arch v i = c.arch v i - θa v) (hfin : ∀ v i, d.fin v i = c.fin v i - θf v)
    {Q : ℝ} (hQ : 0 < Q) (x : ι → Ω) :
    L.absMulHeight (d.weight hQ) x =
      Q ^ (∑ v, θa v + ∑ᶠ v, θf v) * L.absMulHeight (c.weight hQ) x := by
  have hdK : (finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  have hrf : (fun v ↦ Q ^ (-θf v * finrank ℚ K)).HasFiniteMulSupport :=
    hθ.subset fun v hv h ↦ hv (by simp [h])
  rw [L.absMulHeight_of_scale (a := c.weight hQ) (b := d.weight hQ)
    (s := fun v ↦ Q ^ (-θa v * finrank ℚ K / v.mult))
    (r := fun v ↦ Q ^ (-θf v * finrank ℚ K)) (fun _ ↦ Real.rpow_pos_of_pos hQ _)
    (fun _ ↦ Real.rpow_pos_of_pos hQ _) hrf
    (fun v i ↦ by
      change Q ^ _ = Q ^ _ * Q ^ _
      rw [harch, ← Real.rpow_add hQ]
      congr 1
      ring)
    (fun v i ↦ by
      change Q ^ _ = Q ^ _ * Q ^ _
      rw [hfin, ← Real.rpow_add hQ]
      congr 1
      ring)]
  have hA : ∏ v : InfinitePlace K, (Q ^ (-θa v * finrank ℚ K / v.mult)) ^ v.mult =
      Q ^ (-(∑ v, θa v) * finrank ℚ K) := by
    calc ∏ v : InfinitePlace K, (Q ^ (-θa v * finrank ℚ K / v.mult)) ^ v.mult
        = ∏ v : InfinitePlace K, Q ^ (-θa v * finrank ℚ K) :=
          Finset.prod_congr rfl fun v _ ↦ by
            rw [← Real.rpow_mul_natCast hQ.le]
            congr 1
            field_simp
      _ = _ := by
          rw [← Real.rpow_sum_of_pos hQ, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
          simp only [neg_mul]
  have hB : ∏ᶠ v : FinitePlace K, Q ^ (-θf v * finrank ℚ K) =
      Q ^ (-(∑ᶠ v, θf v) * finrank ℚ K) := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := hθ.toFinset)
        (fun v hv ↦ by simpa using fun h ↦ hv (by simp [h])),
      finsum_eq_sum_of_support_subset _ (s := hθ.toFinset) (by simp),
      ← Real.rpow_sum_of_pos hQ, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    simp only [neg_mul]
  rw [hA, hB, ← Real.rpow_add hQ, ← Real.rpow_mul hQ.le, div_eq_mul_inv, mul_comm,
    ← Real.rpow_neg hQ.le]
  congr 2
  field_simp
  ring


section LowerBoundWeight

variable [Nonempty ι]

/-- `max_i Q ^ {f_i} = Q ^ {max_i f_i}` for `Q ≥ 1`. -/
private theorem iSup_rpow_eq {κ : Type*} [Finite κ] [Nonempty κ] {Q : ℝ} (hQ : 1 ≤ Q)
    (f : κ → ℝ) : ⨆ i, Q ^ f i = Q ^ ⨆ i, f i := by
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := f)
  refine le_antisymm (ciSup_le fun j ↦ Real.rpow_le_rpow_of_exponent_le hQ ?_) ?_
  · exact Finite.le_ciSup_of_le j le_rfl
  · rw [← hi₀]
    exact Finite.le_ciSup_of_le (f := fun i ↦ Q ^ f i) i₀ le_rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The largest exponents at the finite places vanish at all but finitely many places. -/
theorem _root_.NumberField.FormExponent.finite_support_iSup_fin (c : FormExponent K ι) :
    (Function.support fun v : FinitePlace K ↦ ⨆ i, c.fin v i).Finite :=
  c.finite_setOf_fin_ne_zero.subset fun v hv h ↦ hv (by simp [h])

omit [Fintype ι] [DecidableEq ι] in
/-- **The product of the largest weights `Q ^ c_iv`** is `Q ^ {θ [K:ℚ]}`, `θ = Σ_v max_i c_iv`. -/
theorem mulMax_weight [Finite ι] (c : FormExponent K ι) {Q : ℝ} (hQ : 1 ≤ Q) :
    (c.weight (zero_lt_one.trans_le hQ)).mulMax =
      Q ^ (((∑ v, ⨆ i, c.arch v i) + (∑ᶠ v, ⨆ i, c.fin v i)) * finrank ℚ K) := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hθ := c.finite_support_iSup_fin
  have hA : ∀ v : InfinitePlace K,
      (⨆ i, (c.weight hQ0).arch v i) ^ v.mult = Q ^ ((⨆ i, c.arch v i) * finrank ℚ K) := fun v ↦ by
    simp only [FormExponent.weight]
    rw [iSup_rpow_eq hQ, ← Real.rpow_mul_natCast hQ0.le]
    congr 1
    have hm : (0 : ℝ) < v.mult := Nat.cast_pos.mpr InfinitePlace.mult_pos
    simp_rw [mul_div_assoc]
    rw [← Real.iSup_mul_of_nonneg (by positivity)]
    field_simp
  have hF : ∀ v : FinitePlace K,
      ⨆ i, (c.weight hQ0).fin v i = Q ^ ((⨆ i, c.fin v i) * finrank ℚ K) := fun v ↦ by
    simp only [FormExponent.weight]
    rw [iSup_rpow_eq hQ, Real.iSup_mul_of_nonneg (by positivity)]
  rw [FormWeight.mulMax, Finset.prod_congr rfl fun v _ ↦ hA v, finprod_congr hF,
    ← Real.rpow_sum_of_pos hQ0,
    finprod_eq_prod_of_mulSupport_subset _ (s := hθ.toFinset)
      (fun v hv ↦ by simpa using fun h ↦ hv (by simp [h])),
    finsum_eq_sum_of_support_subset _ (s := hθ.toFinset) (by simp),
    ← Real.rpow_sum_of_pos hQ0, ← Real.rpow_add hQ0, add_mul, Finset.sum_mul, Finset.sum_mul]

/-- **EF13 Lemma 7.1**: `H_{L,c,Q}(x) ≥ n⁻¹ H_L ^ {-C(r, n)} Q ^ {-θ}` for `x ≠ 0` and `Q ≥ 1`,
`θ = Σ_v max_i c_iv`, `r` the number of distinct forms. -/
theorem le_absMulHeight_weight (c : FormExponent K ι) {Q : ℝ} (hQ : 1 ≤ Q) {x : ι → Ω}
    (hx : x ≠ 0) :
    (Fintype.card ι : ℝ)⁻¹ * L.absFormHeight ^ (-((L.forms.card.choose (Fintype.card ι) : ℕ) : ℝ)) *
        Q ^ (-((∑ v, ⨆ i, c.arch v i) + (∑ᶠ v, ⨆ i, c.fin v i))) ≤
      L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  set a := c.weight hQ0
  set C : ℝ := ((L.forms.card.choose (Fintype.card ι) : ℕ) : ℝ)
  set θ := (∑ v, ⨆ i, c.arch v i) + (∑ᶠ v, ⨆ i, c.fin v i)
  have hdK : (finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  have h := L.one_le_absMulHeight a hx
  have hHpos : 0 < L.mulFormHeight := zero_lt_one.trans_le L.one_le_mulFormHeight
  have hH1 : 1 ≤ L.absFormHeight := Real.one_le_rpow L.one_le_mulFormHeight (by positivity)
  -- `(H_L / Δ_L · A) ^ {1/[K:ℚ]} = (H_L / Δ_L) Q ^ θ ≤ H_L ^ C Q ^ θ`
  have hsplit : (L.mulFormHeight / L.mulDet * a.mulMax) ^ ((finrank ℚ K : ℝ))⁻¹ =
      L.absFormHeight / L.absDet * Q ^ θ := by
    rw [Real.mul_rpow (div_pos hHpos L.mulDet_pos).le (mulMax_pos a).le,
      Real.div_rpow hHpos.le L.mulDet_pos.le, mulMax_weight c hQ, ← Real.rpow_mul hQ0.le,
      mul_inv_cancel_right₀ hdK]
    rfl
  have hHD : L.absFormHeight / L.absDet ≤ L.absFormHeight ^ C := by
    rw [div_le_iff₀ L.absDet_pos]
    calc L.absFormHeight = L.absFormHeight ^ C * L.absFormHeight ^ ((1 : ℝ) - C) := by
          rw [← Real.rpow_add (zero_lt_one.trans_le hH1)]
          simp
      _ ≤ L.absFormHeight ^ C * L.absDet :=
          mul_le_mul_of_nonneg_left L.absFormHeight_rpow_le_absDet (by positivity)
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hX := L.absMulHeight_nonneg a x
  have h2 : 1 ≤ Fintype.card ι * (L.absFormHeight ^ C * Q ^ θ) * L.absMulHeight a x := by
    rw [hsplit] at h
    refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hn.le) hX)
    exact mul_le_mul_of_nonneg_right hHD (by positivity)
  have hpos : 0 < Fintype.card ι * (L.absFormHeight ^ C * Q ^ θ) := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_neg hQ0.le,
    show (Fintype.card ι : ℝ)⁻¹ * (L.absFormHeight ^ C)⁻¹ * (Q ^ θ)⁻¹ =
      (Fintype.card ι * (L.absFormHeight ^ C * Q ^ θ))⁻¹ by rw [mul_inv, mul_inv]; ring,
    inv_le_iff_one_le_mul₀ hpos, mul_comm]
  exact h2


end LowerBoundWeight

end FormSystem

end NumberField
