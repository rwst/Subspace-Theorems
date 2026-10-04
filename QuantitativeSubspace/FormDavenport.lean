/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormMinkowski
public import QuantitativeSubspace.FormParallelepiped
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
# Davenport's lemma

EF13 Lemma 11.3 = ES02 Lemma 9.2 with EF13's modifications: from linearly independent points
`g_1, …, g_n` close to the successive infima `λ_1 ≤ … ≤ λ_n` of `H_{L,c,Q}`, points `h_j` of
`Eⁿ` spanning the same flag whose coordinates at the places above the distinguished finite place
`v₀` are at most `3^{n²} min(λ_i, λ_j)` in a suitable order `π`, while the local factors stay
`≤ 1/n` at the infinite places and `≤ 1` at the other finite places.

The proof follows ES02 §9 in three parts.

1. **ES02 Lemma 9.1** (`exists_approx`): simultaneous approximation at `v₀`. For `ϑ ∈ Ω^r` there
   are `γ ∈ E^r`, `γ₀ ∈ E^*` with `|γ_j + ϑ_j γ₀|_w ≤ 1` above `v₀` and `|γ₀|_w ≤ D` there, small
   elsewhere. It is EF13 Prop. 9.2 (`prod_successiveInf_le`, Q2.4c) over `F = K(ϑ)` for the forms
   `X_j + ϑ_j X₀`, `X₀` (`approxMatrix`) with weight `D` on `X₀` above `v₀`: the product of the
   infima is below `1`, so `λ₁ < 1`, and Lemma 7.3 (`exists_locallyLe_smul`, Q2.4d) scales a point
   of height `< 1` into the local bounds. `γ₀ ≠ 0` by the product formula.
2. **The permutation** (ES02 (9.24)–(9.33), `exists_perm_hasIntegralEchelon`): the spaces
   `W_r = span(g_j : j < r)` at the block starts `r` (`blockStart`, ES02 (9.14)) are defined over
   `K` (ES02 Cor. 7.5 = EF13 Lemma 9.1, Q2.4b), and one permutation `π` gives each a reduced
   echelon basis in `Kⁿ` with pivots `π 0, …, π (r-1)` and `v₀`-integral entries
   (`HasIntegralEchelon`). ES02 choose `π` from the top, by relations on `W_{n-1}, W_{n-2}, …`;
   here it comes from the bottom, by row reduction with the largest pivot
   (`HasIntegralEchelon.exists_sup`), which keeps the earlier pivots. That `v₀` is
   nonarchimedean makes the reduced vectors integral. Then every point of `W_r` is the graph over
   the coordinates `π k`, `k < r`, of the integral matrix `(N_k(π i))` (`apply_eq`).
3. **The construction** (ES02 (9.35)–(9.48), `exists_davenport_step`,
   `exists_davenport_of_graph`): `h_q = γ₀ g_q + Σ_{j < r} γ_j h_j`, `r` the start of the block of
   `q`, with `γ` from Lemma 9.1 for the coefficients `θ_j` of the point `z = Σ θ_j h_j ∈ W_r` that
   agrees with `g_q` at the coordinates `π k`, `k < r`. Writing
   `h_q = γ₀ (g_q - z) + Σ_j (γ_j + θ_j γ₀) h_j` gives both of ES02's estimates (9.47), (9.48) at
   once: `g_q - z` vanishes at `π k`, `k < r`, and equals `g_q - A g_q` with `|A|_{v₀} ≤ 1`
   elsewhere. The bounds of all points are carried over a common field
   (`FormSystem.DavenportLe`, which passes to larger fields).

`exists_davenport` assembles EF13's statement from EF13 Lemma 11.2 (`exists_smul_le_of_lt`) with
`B = n (1+ε)`, `D = (1+ε) n^n 2^{n(n-1)/2}`, and `D B ≤ (1+ε)^{n+1} n 2^{n²} ≤ 3^{n²}`
(`pow_mul_sqrt_two_pow_le`).

## Main results

* `NumberField.exists_approx`: ES02 Lemma 9.1.
* `NumberField.HasIntegralEchelon`, `NumberField.exists_perm_hasIntegralEchelon`: the integral
  graphs and the permutation of ES02 (9.24)–(9.33).
* `NumberField.FormSystem.DavenportLe`: the bounds (11.6), (11.7) over a field `E ⊆ Ω`.
* `NumberField.FormSystem.exists_davenport_of_graph`: ES02 Lemma 9.2 given the pivots, for any
  forms and weights and any nondecreasing `λ`.
* `NumberField.FormSystem.exists_davenport`: **EF13 Lemma 11.3**.

## Implementation notes

⚠ **`AbsoluteValue.exists_evertse_of_approx` is not reused.** Evertse's lemma (Layer 4.4) changes
`x_j` by `R`-combinations of the earlier vectors over one fixed field, with per-place
permutations. Davenport's lemma rescales `g_q` itself (`γ₀`), needs extensions of the field at
every step, and has one permutation for the places above `v₀`; Lemma 9.1 is a `t`-dimensional
Minkowski problem, not an approximation of one scalar.

⚠ **Normalization.** As in `FormParallelepiped.lean`: EF13's `‖x‖_w ≤ C^{d(w|v₀)}` is
`|x|_w ≤ (C ^ [K:ℚ]) ^ {e f}` with Mathlib's `FinitePlace` and `e f` the local degree over `K`,
and `n^{-s(w)}` at an infinite place is a local factor `≤ 1/n`.

⚠ **Constants.** ES02's `(1+ε)^t 2^{t²}` in Lemma 9.1 is `t^t 2^{t(t-1)/2}` here (any `D` above
it), from Q2.4c's `2^{n(n-1)/2}`. EF13 (11.1) is used with `≤` in place of `<`.

## References

J.-H. Evertse and H. P. Schlickewei, "A quantitative version of the absolute subspace theorem",
*J. reine angew. Math.* **548** (2002), 21–127, §9.

J.-H. Evertse and R. G. Ferretti, "A further improvement of the Quantitative Subspace Theorem",
*Ann. of Math.* **177** (2013), 513–590, Lemma 11.3.

This is milestone Q2.4e of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Finset Function Module Matrix

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- A finite place is nonarchimedean: a sum of terms at most `M ≥ 0` is at most `M`. -/
theorem FinitePlace.apply_sum_le {E : Type*} [Field E] [NumberField E] (w : FinitePlace E)
    {κ : Type*} (s : Finset κ) {f : κ → E} {M : ℝ} (hM : 0 ≤ M) (h : ∀ j ∈ s, w (f j) ≤ M) :
    w (∑ j ∈ s, f j) ≤ M := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hM
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (FinitePlace.add_le w _ _).trans
      (max_le (h j (mem_insert_self _ _)) (ih fun k hk ↦ h k (mem_insert_of_mem hk)))

/-- A `finprod` of reals in `[0, 1]` is at most `1` (also without finite support). -/
theorem finprod_le_one_of_le {α : Type*} {f : α → ℝ} (h0 : ∀ a, 0 ≤ f a) (h1 : ∀ a, f a ≤ 1) :
    ∏ᶠ a, f a ≤ 1 := by
  by_cases H : f.HasFiniteMulSupport
  · exact (finprod_le_finprod₀ H h0 (by simp [Function.HasFiniteMulSupport]) h1).trans
      finprod_one.le
  · rw [finprod_of_not_hasFiniteMulSupport H]

/-- A bound `b ^ {e f}` at the places above `w.under K` passes up an inclusion of fields. -/
theorem FinitePlace.apply_inclusion_le {Ω : Type*} [Field Ω] [Algebra K Ω]
    {E E' : IntermediateField K Ω} [NumberField E] [NumberField E'] (hEE : E ≤ E')
    (w : FinitePlace E') (z : E) {b : ℝ}
    (h : ∀ u : FinitePlace E, u.under K = w.under K → u z ≤ b ^ u.localDegree K) :
    w (IntermediateField.inclusion hEE z) ≤ b ^ w.localDegree K := by
  let : Algebra E E' := (IntermediateField.inclusion hEE).toAlgebra
  have : IsScalarTower K E E' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hz : IntermediateField.inclusion hEE z = algebraMap E E' z := rfl
  rw [hz, FinitePlace.apply_algebraMap w (w.under E),
    FinitePlace.localDegree_tower (K := K) (E := E) w, mul_comm, pow_mul]
  exact pow_le_pow_left₀ (by positivity)
    (h _ (FinitePlace.under_under (K := K) (E := E) w)) _

/-- Replacing `y` by `x` with `x - c y ∈ U`, `c ≠ 0`, does not change `U ⊔ span {y}`. -/
theorem _root_.Submodule.sup_span_singleton_eq_of_sub_smul_mem {R V : Type*} [Field R]
    [AddCommGroup V] [Module R V] {U : Submodule R V} {x y : V} {c : R} (hc : c ≠ 0)
    (h : x - c • y ∈ U) : U ⊔ Submodule.span R {x} = U ⊔ Submodule.span R {y} := by
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_) <;>
    rw [Submodule.span_singleton_le_iff_mem]
  · have : x = (x - c • y) + c • y := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left h)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)))
  · have : y = c⁻¹ • x - c⁻¹ • (x - c • y) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hc, one_smul]
      abel
    rw [this]
    exact Submodule.sub_mem _
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)))
      (Submodule.mem_sup_left (Submodule.smul_mem _ _ h))

/-! ### ES02 Lemma 9.1 -/

section Approx

variable (Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]

/-- The matrix of the forms `X_i + ϑ_i X_t` (`i < t`), `X_t` of ES02 (9.7). -/
private noncomputable def approxMatrix {F : Type*} [Field F] {r : ℕ} (ϑ : Fin r → F) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) F :=
  1 + Matrix.of fun i j ↦ if j = Fin.last r then Fin.snoc (α := fun _ ↦ F) ϑ 0 i else 0

private theorem approxMatrix_map_mulVec {F E : Type*} [Field F] [Field E] [Algebra F E] {r : ℕ}
    (ϑ : Fin r → F) (x : Fin (r + 1) → E) (i : Fin (r + 1)) :
    (((approxMatrix ϑ).map (algebraMap F E)) *ᵥ x) i =
      x i + algebraMap F E (Fin.snoc (α := fun _ ↦ F) ϑ 0 i) * x (Fin.last r) := by
  simp [approxMatrix, Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib,
    Matrix.one_apply, apply_ite (algebraMap F E)]

private theorem det_approxMatrix {F : Type*} [Field F] {r : ℕ} (ϑ : Fin r → F) :
    (approxMatrix ϑ).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ ↦ ?_
    by_cases hi : i = Fin.last r
    · subst hi
      simp [approxMatrix]
    · simp [approxMatrix, hi]
  · intro i j hji
    have hj : j ≠ Fin.last r := ne_of_lt (lt_of_lt_of_le hji (Fin.le_last i))
    have hij : i ≠ j := fun h ↦ by simp [h] at hji
    simp [approxMatrix, hj, Matrix.one_apply_ne hij]

/-- **ES02 Lemma 9.1**, simultaneous approximation at `v₀`: for `ϑ ∈ Ω^r` and
`D > (r+1)^{r+1} 2^{r(r+1)/2}` there are an extension `E ⊆ Ω` containing the `ϑ_j` and `γ ∈ E^r`,
`γ₀ ∈ E^*`, with `|γ|_w ≤ 1/(r+1)` at the infinite places, `|γ|_w ≤ 1` at the finite places not
above `v₀`, and `|γ_j + ϑ_j γ₀|_w ≤ 1`, `|γ₀|_w ≤ (D ^ [K:ℚ]) ^ {e f}` above `v₀`. The proof is
EF13 Prop. 9.2 (Q2.4c) over `F = K(ϑ)` for the forms `X_j + ϑ_j X₀`, `X₀` above `v₀` with the
weight `D` on `X₀`, which gives `λ₁ < 1`, and Lemma 7.3 (Q2.4d) for a point of height `< 1`. -/
theorem exists_approx_fin (v₀ : FinitePlace K) {r : ℕ} (ϑ : Fin r → Ω) {D : ℝ}
    (hD : ((r : ℝ) + 1) ^ (r + 1) * √2 ^ ((r + 1) * r) < D) :
    ∃ (E : IntermediateField K Ω) (_ : NumberField E) (ϑE γ : Fin r → E) (γ₀ : E),
      (∀ j, (ϑE j : Ω) = ϑ j) ∧ γ₀ ≠ 0 ∧
      (∀ w : InfinitePlace E, w γ₀ ≤ ((r : ℝ) + 1)⁻¹ ∧ ∀ j, w (γ j) ≤ ((r : ℝ) + 1)⁻¹) ∧
      (∀ w : FinitePlace E, w.under K ≠ v₀ → w γ₀ ≤ 1 ∧ ∀ j, w (γ j) ≤ 1) ∧
      ∀ w : FinitePlace E, w.under K = v₀ →
        w γ₀ ≤ (D ^ finrank ℚ K) ^ w.localDegree K ∧ ∀ j, w (γ j + ϑE j * γ₀) ≤ 1 := by
  classical
  have hD0 : 0 < D := lt_of_le_of_lt (by positivity) hD
  set t : ℝ := (r : ℝ) + 1 with ht
  have ht0 : 0 < t := by positivity
  set F := IntermediateField.adjoin K (Set.range ϑ)
  have : NumberField F := Twist.numberField_adjoin_range (K := K) ϑ
  have : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := K) F
  have hϑF : ∀ j, ϑ j ∈ F := fun j ↦ IntermediateField.subset_adjoin K _ ⟨j, rfl⟩
  set ϑF : Fin r → F := fun j ↦ ⟨ϑ j, hϑF j⟩
  set M := approxMatrix ϑF
  have hpb : ∀ v, 0 < FormSystem.paraBudget v₀ D v := fun v ↦ by
    unfold FormSystem.paraBudget
    split_ifs
    · positivity
    · exact one_pos
  let L : FormSystem F (Fin (r + 1)) :=
    { arch := fun _ ↦ 1
      arch_det_ne_zero := fun _ ↦ by simp
      fin := fun w ↦ if w.under K = v₀ then M else 1
      fin_det_ne_zero := fun w ↦ by split_ifs <;> simp [M, det_approxMatrix]
      finite_range_fin := ((Set.finite_singleton 1).insert M).subset <| by
        rintro _ ⟨w, rfl⟩
        dsimp only
        split_ifs <;> simp }
  let a : FormWeight F (Fin (r + 1)) :=
    { arch := fun _ _ ↦ t⁻¹
      arch_pos := fun _ _ ↦ inv_pos.mpr ht0
      fin := fun w i ↦
        if i = Fin.last r then FormSystem.paraBudget v₀ D (w.under K) ^ w.localDegree K else 1
      fin_pos := fun w i ↦ by
        split_ifs
        · exact pow_pos (hpb _) _
        · exact one_pos
      finite_setOf_fin_ne_one :=
        (FinitePlace.hasFiniteMulSupport_comp_under
          (FormSystem.hasFiniteMulSupport_paraBudget v₀ D)
          (fun w : FinitePlace F ↦ w.localDegree K)).subset fun w hw ↦ by
            refine fun h1 ↦ hw (funext fun i ↦ ?_)
            simp only at h1
            split_ifs <;> simp [h1] }
  -- `Δ_L = 1` and `∏ A = D / (r+1)^{r+1}`.
  have hdet : L.absDet = 1 := by
    have hfin : ∀ w : FinitePlace F, w (L.fin w).det = 1 := fun w ↦ by
      dsimp only [L]
      split_ifs <;> simp [M, det_approxMatrix]
    simp [FormSystem.absDet, FormSystem.mulDet, L, hfin]
  have hprod : a.absProd = (t⁻¹) ^ (r + 1) * D := by
    have hfin : ∀ w : FinitePlace F, ∏ i, a.fin w i =
        FormSystem.paraBudget v₀ D (w.under K) ^ w.localDegree K := fun w ↦ by
      simp [a]
    have hmul : a.mulProd = ((t⁻¹) ^ (r + 1) * D) ^ finrank ℚ F := by
      rw [FormWeight.mulProd, funext hfin,
        FinitePlace.finprod_under_pow_localDegree _
          (FormSystem.hasFiniteMulSupport_paraBudget v₀ D),
        FormSystem.finprod_paraBudget, ← pow_mul, Module.finrank_mul_finrank ℚ K F, mul_pow]
      congr 1
      simp only [a, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
    rw [FormWeight.absProd, hmul, Real.pow_rpow_inv_natCast (by positivity) finrank_pos.ne']
  -- Minkowski: `λ₁ < 1`.
  have hmin := L.prod_successiveInf_le a (Ω := Ω) (n := r + 1) (Nat.succ_pos r)
  rw [hdet, hprod] at hmin
  have hRHS : √2 ^ ((r + 1) * (r + 1 - 1)) * (1 / ((t⁻¹) ^ (r + 1) * D)) < 1 := by
    rw [Nat.add_sub_cancel, one_div, mul_inv, inv_pow, inv_inv, ← mul_assoc,
      mul_comm (√2 ^ _), mul_inv_lt_iff₀ hD0, one_mul]
    exact hD
  set lam1 := L.successiveInf a Ω 1
  have hle : lam1 ^ (r + 1) ≤ ∏ i : Fin (r + 1), L.successiveInf a Ω (i + 1) := by
    rw [← Fin.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ ↦ heightInf_nonneg _) fun i _ ↦
      heightInf_mono (by omega) (by simp [Nat.succ_le_of_lt i.2])
  have hlam1 : lam1 < 1 := (pow_lt_one_iff_of_nonneg (heightInf_nonneg 1)
    (Nat.succ_ne_zero r)).1 (hle.trans_lt (hmin.trans_lt hRHS))
  obtain ⟨μ, hμ1, hμ2⟩ := exists_between hlam1
  obtain ⟨x, hxli, hxμ⟩ := exists_linearIndependent_of_heightInf_lt (Ω := Ω)
    (h := L.absMulHeight a) (i := 1) (by simp) hμ1
  have hx0 : x 0 ≠ 0 := hxli.ne_zero 0
  -- A multiple of `x` with local factors `≤ 1`.
  obtain ⟨E, hE, y, hy, hloc⟩ := L.exists_locallyLe_smul a (κ := Unit) (x := fun _ ↦ x 0)
    (fun _ ↦ hx0) (ρa := fun _ _ ↦ 1) (ρf := fun _ _ ↦ 1) (fun _ _ ↦ one_pos)
    (fun _ _ ↦ one_pos) (fun _ ↦ by simp [Function.HasFiniteMulSupport]) fun _ ↦ by
      simp only [one_pow, Finset.prod_const_one, finprod_one, mul_one, Real.one_rpow]
      exact (hxμ 0).trans_lt hμ2
  set Y := y ()
  have harch : ∀ (w : InfinitePlace E) i, w (Y i) ≤ t⁻¹ := fun w i ↦ by
    have h2 : w (Y i) / t⁻¹ ≤ L.archFactor a w Y := by
      unfold FormSystem.archFactor
      refine Finite.le_ciSup_of_le i (le_of_eq ?_)
      simp [L, a]
    have := h2.trans ((hloc ()).1 w)
    rwa [div_le_one (inv_pos.mpr ht0)] at this
  have hfin : ∀ (w : FinitePlace E) i,
      w (((L.fin (w.under F)).map (algebraMap F E) *ᵥ Y) i) /
        a.fin (w.under F) i ^ w.localDegree F ≤ 1 := fun w i ↦ by
    refine (Finite.le_ciSup_of_le (f := fun i ↦ w (((L.fin (w.under F)).map (algebraMap F E) *ᵥ
      Y) i) / a.fin (w.under F) i ^ w.localDegree F) i le_rfl).trans
      (((hloc ()).2 w).trans (by simp))
  have hunder : ∀ w : FinitePlace E, (w.under F).under K = w.under K := fun w ↦
    FinitePlace.under_under (K := K) (E := F) w
  have hoff : ∀ w : FinitePlace E, w.under K ≠ v₀ → ∀ i, w (Y i) ≤ 1 := fun w hw i ↦ by
    have := hfin w i
    simpa [L, a, hunder, hw, FormSystem.paraBudget] using this
  have hcast : ∀ w : FinitePlace E, w.under K = v₀ → ∀ j,
      w (Y j.castSucc + algebraMap F E (ϑF j) * Y (Fin.last r)) ≤ 1 := fun w hw j ↦ by
    have := hfin w j.castSucc
    simpa [L, a, hunder, hw, M, approxMatrix_map_mulVec, Fin.castSucc_ne_last] using this
  have hlast : ∀ w : FinitePlace E, w.under K = v₀ →
      w (Y (Fin.last r)) ≤ (D ^ finrank ℚ K) ^ w.localDegree K := fun w hw ↦ by
    have := hfin w (Fin.last r)
    simp only [L, a, hunder, hw, M, approxMatrix_map_mulVec, ite_true] at this
    rw [Fin.snoc_last, map_zero, zero_mul, add_zero, ← pow_mul, mul_comm,
      ← FinitePlace.localDegree_tower (K := K) (E := F) w] at this
    have hpv : FormSystem.paraBudget v₀ D v₀ = D ^ finrank ℚ K := by
      simp [FormSystem.paraBudget]
    rwa [hpv, div_le_one (by positivity)] at this
  -- `γ₀ ≠ 0`, by the product formula.
  have hY0 : Y ≠ 0 := by
    obtain ⟨β, hβ, hβx⟩ := hy ()
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
    intro h0
    have := hβx i
    rw [show y () i = 0 from congrFun h0 i, IntermediateField.coe_zero, eq_comm,
      mul_eq_zero] at this
    exact this.elim hβ hi
  have hγ₀ : Y (Fin.last r) ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hY0
    have hi' : Y i ≠ 0 := hi
    obtain ⟨j, rfl⟩ : ∃ j : Fin r, j.castSucc = i := by
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact ⟨j, rfl⟩
      · exact absurd h0 hi'
    have ht2 : 1 < t := by
      rw [ht, lt_add_iff_pos_left]
      exact_mod_cast j.pos
    have h1 : ∏ w : InfinitePlace E, w (Y j.castSucc) ^ w.mult ≤ t⁻¹ ^ finrank ℚ E := by
      rw [← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_le_prod₀ (fun w _ ↦ by positivity) fun w _ ↦
        pow_le_pow_left₀ (by positivity) (harch w _) _
    have h2 : ∏ᶠ w : FinitePlace E, w (Y j.castSucc) ≤ 1 :=
      finprod_le_one_of_le (fun w ↦ by positivity) fun w ↦ by
        by_cases hw : w.under K = v₀
        · have := hcast w hw j
          rwa [h0, mul_zero, add_zero] at this
        · exact hoff w hw _
    have h3 : t⁻¹ ^ finrank ℚ E < 1 :=
      pow_lt_one₀ (inv_nonneg.mpr ht0.le) (inv_lt_one_of_one_lt₀ ht2) finrank_pos.ne'
    have hpf := NumberField.prod_abs_eq_one hi'
    have : (1 : ℝ) < 1 := calc
      (1 : ℝ) = _ := hpf.symm
      _ ≤ t⁻¹ ^ finrank ℚ E * 1 := mul_le_mul h1 h2 (finprod_nonneg fun w ↦ by positivity)
          (by positivity)
      _ < 1 := by rwa [mul_one]
    exact lt_irrefl _ this
  exact ⟨E.restrictScalars K, hE, fun j ↦ algebraMap F E (ϑF j), fun j ↦ Y j.castSucc,
    Y (Fin.last r), fun j ↦ rfl, hγ₀, fun w ↦ ⟨harch w _, fun j ↦ harch w _⟩,
    fun w hw ↦ ⟨hoff w hw _, fun j ↦ hoff w hw _⟩, fun w hw ↦ ⟨hlast w hw, hcast w hw⟩⟩

/-- ES02 Lemma 9.1 with the `ϑ_j` indexed by any finite type `κ`, `r = #κ`. -/
theorem exists_approx (v₀ : FinitePlace K) {κ : Type*} [Fintype κ] (ϑ : κ → Ω) {D : ℝ}
    (hD : ((Fintype.card κ : ℝ) + 1) ^ (Fintype.card κ + 1) *
      √2 ^ ((Fintype.card κ + 1) * Fintype.card κ) < D) :
    ∃ (E : IntermediateField K Ω) (_ : NumberField E) (ϑE γ : κ → E) (γ₀ : E),
      (∀ j, (ϑE j : Ω) = ϑ j) ∧ γ₀ ≠ 0 ∧
      (∀ w : InfinitePlace E, w γ₀ ≤ ((Fintype.card κ : ℝ) + 1)⁻¹ ∧
        ∀ j, w (γ j) ≤ ((Fintype.card κ : ℝ) + 1)⁻¹) ∧
      (∀ w : FinitePlace E, w.under K ≠ v₀ → w γ₀ ≤ 1 ∧ ∀ j, w (γ j) ≤ 1) ∧
      ∀ w : FinitePlace E, w.under K = v₀ →
        w γ₀ ≤ (D ^ finrank ℚ K) ^ w.localDegree K ∧ ∀ j, w (γ j + ϑE j * γ₀) ≤ 1 := by
  set e := Fintype.equivFin κ
  obtain ⟨E, hE, ϑE, γ, γ₀, h1, h2, h3, h4, h5⟩ := exists_approx_fin Ω v₀ (ϑ ∘ e.symm) hD
  refine ⟨E, hE, ϑE ∘ e, γ ∘ e, γ₀, fun j ↦ by simp [h1], h2, fun w ↦ ⟨(h3 w).1, fun j ↦
    (h3 w).2 _⟩, fun w hw ↦ ⟨(h4 w hw).1, fun j ↦ (h4 w hw).2 _⟩, fun w hw ↦
    ⟨(h5 w hw).1, fun j ↦ (h5 w hw).2 _⟩⟩

end Approx

/-! ### Local factors of linear combinations -/

/-! ### Blocks of equal infima -/

section Blocks

variable {n : ℕ} (lam : Fin n → ℝ)

/-- **The start of the block of `q`** (ES02 (9.14)): the number of `j` with `λ_j < λ_q`; for
nondecreasing `λ` these are the `j` below it. -/
noncomputable def blockStart (q : Fin n) : ℕ := (Finset.univ.filter fun j ↦ lam j < lam q).card

variable {lam} (hmono : Monotone lam)
include hmono

theorem blockStart_le (q : Fin n) : blockStart lam q ≤ q := by
  calc blockStart lam q ≤ (Finset.univ.filter fun j : Fin n ↦ (j : ℕ) < q).card := by
        refine Finset.card_le_card fun j hj ↦ ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        by_contra! h
        exact (hmono (Fin.le_iff_val_le_val.mpr h)).not_gt hj
    _ = q := by
        rw [Fin.card_filter_val_lt]
        omega

theorem le_of_blockStart_le {q i : Fin n} (hi : blockStart lam q ≤ i) : lam q ≤ lam i := by
  by_contra! h
  have hsub : Finset.Iic i ⊆ Finset.univ.filter fun j ↦ lam j < lam q := fun j hj ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hmono (Finset.mem_Iic.mp hj)).trans_lt h
  have := Finset.card_le_card hsub
  rw [Fin.card_Iic] at this
  exact absurd (hi.trans_lt this) (lt_irrefl _)

/-- A block start other than `0` is a jump `λ_{r-1} < λ_r`. -/
theorem lt_of_blockStart {q : Fin n} (h0 : 0 < blockStart lam q) :
    lam ⟨blockStart lam q - 1, by have := blockStart_le hmono q; omega⟩ <
      lam ⟨blockStart lam q, by have := blockStart_le hmono q; omega⟩ := by
  set r := blockStart lam q
  have hrq : r ≤ q := blockStart_le hmono q
  refine lt_of_lt_of_le ?_ (le_of_blockStart_le hmono (le_refl r))
  by_contra! h
  have hsub : (Finset.univ.filter fun j ↦ lam j < lam q) ⊆
      Finset.univ.filter fun j : Fin n ↦ (j : ℕ) < r - 1 := fun j hj ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    by_contra! hj'
    exact (h.trans (hmono (Fin.le_iff_val_le_val.mpr hj'))).not_gt hj
  have := Finset.card_le_card hsub
  rw [Fin.card_filter_val_lt] at this
  change r ≤ min n (r - 1) at this
  omega

end Blocks

/-! ### The permutation of ES02 (9.24)–(9.33) -/

section Echelon

variable {Ω : Type*} [Field Ω] [Algebra K Ω] {n : ℕ}

/-- **An integral reduced echelon basis**: `W ⊆ Ωⁿ` is spanned by vectors `N_k ∈ Kⁿ`, `k < r`,
with `N_k(π m) = δ_km` for `k, m < r` and all entries of `v`-absolute value at most `1`. -/
def HasIntegralEchelon (v : FinitePlace K) (π : Equiv.Perm (Fin n)) (r : ℕ)
    (W : Submodule Ω (Fin n → Ω)) : Prop :=
  ∃ N : Fin n → Fin n → K,
    (∀ k m : Fin n, (k : ℕ) < r → (m : ℕ) < r → N k (π m) = if k = m then 1 else 0) ∧
    (∀ k c, v (N k c) ≤ 1) ∧
    W = Submodule.span Ω ((fun k ↦ algebraMap K Ω ∘ N k) '' {k | (k : ℕ) < r})

variable {v : FinitePlace K} {π : Equiv.Perm (Fin n)} {r : ℕ} {W : Submodule Ω (Fin n → Ω)}

/-- An echelon basis only depends on the first `r` pivots. -/
theorem HasIntegralEchelon.congr {π' : Equiv.Perm (Fin n)}
    (hπ : ∀ m : Fin n, (m : ℕ) < r → π' m = π m) (h : HasIntegralEchelon v π r W) :
    HasIntegralEchelon v π' r W := by
  obtain ⟨N, h1, h2, h3⟩ := h
  exact ⟨N, fun k m hk hm ↦ by rw [hπ m hm]; exact h1 k m hk hm, h2, h3⟩

omit [NumberField K] in
/-- **The graph relation** (ES02 (9.32)): a point of `W` is determined by its coordinates
`π k`, `k < r`, through the `N_k`. -/
theorem HasIntegralEchelon.apply_eq {N : Fin n → Fin n → K}
    (h1 : ∀ k m : Fin n, (k : ℕ) < r → (m : ℕ) < r → N k (π m) = if k = m then 1 else 0)
    {z : Fin n → Ω}
    (hz : z ∈ Submodule.span Ω ((fun k ↦ algebraMap K Ω ∘ N k) '' {k | (k : ℕ) < r}))
    (c : Fin n) :
    z c = ∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ (k : ℕ) < r),
      z (π k) * algebraMap K Ω (N k c) := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k₀, hk₀, rfl⟩ := hx
    have hmem : k₀ ∈ Finset.univ.filter (fun k : Fin n ↦ (k : ℕ) < r) := by simpa using hk₀
    rw [Finset.sum_eq_single_of_mem k₀ hmem]
    · simp [h1 k₀ k₀ hk₀ hk₀]
    · intro k hk hne
      have hk' : (k : ℕ) < r := (Finset.mem_filter.mp hk).2
      simp [h1 k₀ k hk₀ hk', Ne.symm hne]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy, add_mul, Finset.sum_add_distrib]
  | smul c' x _ hx => simp [hx, Finset.mul_sum, mul_assoc]

/-- The echelon vectors are linearly independent, so `dim W = r`. -/
theorem HasIntegralEchelon.finrank_eq (h : HasIntegralEchelon v π r W) :
    finrank Ω W = Fintype.card {k : Fin n // (k : ℕ) < r} := by
  obtain ⟨N, h1, -, rfl⟩ := h
  set u : {k : Fin n // (k : ℕ) < r} → Fin n → Ω := fun k ↦ algebraMap K Ω ∘ N k
  have hli : LinearIndependent Ω u := by
    let f : (Fin n → Ω) →ₗ[Ω] ({k : Fin n // (k : ℕ) < r} → Ω) :=
      LinearMap.pi fun m ↦ LinearMap.proj (π m)
    refine LinearIndependent.of_comp f ?_
    have hfu : f ∘ u = fun k ↦ Pi.basisFun Ω _ k := by
      funext k m
      simp only [Function.comp_apply, f, u, LinearMap.pi_apply, LinearMap.proj_apply,
        Pi.basisFun_apply, h1 k m k.2 m.2, Pi.single_apply, Subtype.ext_iff]
      split_ifs <;> simp_all [eq_comm]
    rw [hfu]
    exact (Pi.basisFun Ω _).linearIndependent
  rw [Set.image_eq_range]
  exact finrank_span_eq_card hli

/-- **One pivot step** (ES02 (9.24)–(9.31)): a vector `y ∈ Kⁿ` outside `W` extends an integral
echelon basis of `W` to one of `W + Ω y`, keeping the first `r` pivots. The new pivot is a
coordinate where `y` reduced by the `N_k` is largest, so the new vector is integral after
normalization, and the old ones stay integral after reduction because `v` is nonarchimedean. -/
theorem HasIntegralEchelon.exists_sup (h : HasIntegralEchelon v π r W) (hr : r < n)
    {y : Fin n → K} (hy : algebraMap K Ω ∘ y ∉ W) :
    ∃ π' : Equiv.Perm (Fin n), (∀ m : Fin n, (m : ℕ) < r → π' m = π m) ∧
      HasIntegralEchelon v π' (r + 1) (W ⊔ Submodule.span Ω {algebraMap K Ω ∘ y}) := by
  classical
  obtain ⟨N, h1, h2, rfl⟩ := h
  set Sr := Finset.univ.filter (fun k : Fin n ↦ (k : ℕ) < r)
  have hSr : ∀ k, k ∈ Sr ↔ (k : ℕ) < r := fun k ↦ by simp [Sr]
  set φ : Fin n → Fin n → Ω := fun k ↦ algebraMap K Ω ∘ N k
  set z : Fin n → K := y - ∑ k ∈ Sr, y (π k) • N k
  have hz0 : ∀ m : Fin n, (m : ℕ) < r → z (π m) = 0 := by
    intro m hm
    simp only [z, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single_of_mem m ((hSr m).mpr hm), h1 m m hm hm]
    · simp
    intro k hk hne
    rw [h1 k m ((hSr k).mp hk) hm]
    simp [hne]
  have hY : algebraMap K Ω ∘ y = algebraMap K Ω ∘ z + ∑ k ∈ Sr, algebraMap K Ω (y (π k)) • φ k := by
    funext c
    simp [z, φ, Finset.sum_apply, Algebra.smul_def]
  have hφW : ∀ k ∈ Sr, φ k ∈ Submodule.span Ω (φ '' {k | (k : ℕ) < r}) := fun k hk ↦
    Submodule.subset_span ⟨k, (hSr k).mp hk, rfl⟩
  have hsumW : ∑ k ∈ Sr, algebraMap K Ω (y (π k)) • φ k ∈
      Submodule.span Ω (φ '' {k | (k : ℕ) < r}) :=
    Submodule.sum_mem _ fun k hk ↦ Submodule.smul_mem _ _ (hφW k hk)
  have hzne : z ≠ 0 := by
    intro hz
    apply hy
    rw [hY, hz]
    simpa using hsumW
  have : Nonempty (Fin n) := ⟨⟨r, hr⟩⟩
  obtain ⟨c₀, -, hc₀⟩ := Finset.exists_max_image Finset.univ (fun c ↦ v (z c))
    Finset.univ_nonempty
  have hzc₀ : z c₀ ≠ 0 := by
    obtain ⟨c, hc⟩ := Function.ne_iff.mp hzne
    intro h0
    have := hc₀ c (Finset.mem_univ _)
    rw [h0, map_zero] at this
    exact hc (by simpa using le_antisymm this (by positivity))
  have hvc₀ : 0 < v (z c₀) :=
    lt_of_le_of_ne (by positivity) fun h ↦ hzc₀ (by simpa using h.symm)
  have hc₀π : ∀ m : Fin n, (m : ℕ) < r → π m ≠ c₀ := fun m hm h ↦ hzc₀ (h ▸ hz0 m hm)
  set p : Fin n := ⟨r, hr⟩
  have hmp : ∀ m : Fin n, (m : ℕ) < r → m ≠ p := fun m hm h ↦ by
    rw [h] at hm
    exact lt_irrefl r hm
  set π' : Equiv.Perm (Fin n) := π.trans (Equiv.swap (π p) c₀)
  have hπ'm : ∀ m : Fin n, (m : ℕ) < r → π' m = π m := fun m hm ↦
    Equiv.swap_apply_of_ne_of_ne (π.injective.ne (hmp m hm)) (hc₀π m hm)
  have hπ'p : π' p = c₀ := Equiv.swap_apply_left _ _
  set z' : Fin n → K := (z c₀)⁻¹ • z
  have hz'c₀ : z' c₀ = 1 := by simp [z', hzc₀]
  have hz'π : ∀ m : Fin n, (m : ℕ) < r → z' (π m) = 0 := fun m hm ↦ by simp [z', hz0 m hm]
  have hz'v : ∀ c, v (z' c) ≤ 1 := fun c ↦ by
    simp only [z', Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ hvc₀, mul_one]
    exact hc₀ c (Finset.mem_univ _)
  set N' : Fin n → Fin n → K := fun k ↦ if k = p then z' else N k - N k c₀ • z'
  set φ' : Fin n → Fin n → Ω := fun k ↦ algebraMap K Ω ∘ N' k
  have hφ'p : φ' p = (algebraMap K Ω (z c₀))⁻¹ • algebraMap K Ω ∘ z := by
    funext c
    simp [φ', N', z']
  have hφ'k : ∀ k, k ≠ p → φ' k = φ k - algebraMap K Ω (N k c₀) • φ' p := fun k hk ↦ by
    funext c
    simp [φ', N', φ, hk, Algebra.smul_def]
  refine ⟨π', hπ'm, N', fun k m hk hm ↦ ?_, fun k c ↦ ?_, ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk <;>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | hm
    · simp [N', hmp k hk, hπ'm m hm, h1 k m hk hm, hz'π m hm]
    · rw [show m = p from Fin.ext hm]
      simp [N', hmp k hk, hπ'p, hz'c₀]
    · rw [show k = p from Fin.ext hk]
      simp [N', hπ'm m hm, hz'π m hm, (hmp m hm).symm]
    · rw [show k = p from Fin.ext hk, show m = p from Fin.ext hm]
      simp [N', hπ'p, hz'c₀]
  · by_cases hk : k = p
    · simpa [N', hk] using hz'v c
    · simp only [N', hk, ite_false]
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg]
      refine (FinitePlace.add_le v _ _).trans (max_le (h2 k c) ?_)
      rw [map_neg_eq_map, map_mul]
      exact (mul_le_mul (h2 k c₀) (hz'v c) (by positivity) zero_le_one).trans_eq (one_mul 1)
  · change _ = Submodule.span Ω (φ' '' {k | (k : ℕ) < r + 1})
    have hp : (p : ℕ) < r + 1 := Nat.lt_succ_self r
    have hφ'mem : ∀ k : Fin n, (k : ℕ) < r + 1 →
        φ' k ∈ Submodule.span Ω (φ' '' {k | (k : ℕ) < r + 1}) := fun k hk ↦
      Submodule.subset_span ⟨k, hk, rfl⟩
    have hφin : ∀ k ∈ Sr, φ k ∈ Submodule.span Ω (φ' '' {k | (k : ℕ) < r + 1}) := by
      intro k hk
      have hk' := (hSr k).mp hk
      have : φ k = φ' k + algebraMap K Ω (N k c₀) • φ' p := by
        rw [hφ'k k (hmp k hk')]
        abel
      rw [this]
      exact Submodule.add_mem _ (hφ'mem k (by omega)) (Submodule.smul_mem _ _ (hφ'mem p hp))
    have hzφ : algebraMap K Ω ∘ z = algebraMap K Ω (z c₀) • φ' p := by
      rw [hφ'p, smul_smul, mul_inv_cancel₀ (by simpa using hzc₀), one_smul]
    apply le_antisymm
    · refine sup_le (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
      · rintro _ ⟨k, hk, rfl⟩
        exact hφin k ((hSr k).mpr hk)
      · rintro _ rfl
        rw [SetLike.mem_coe, hY, hzφ]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hφ'mem p hp))
          (Submodule.sum_mem _ fun k hk ↦ Submodule.smul_mem _ _ (hφin k hk))
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, hk, rfl⟩
      have hpmem : φ' p ∈ Submodule.span Ω (φ '' {k | (k : ℕ) < r}) ⊔
          Submodule.span Ω {algebraMap K Ω ∘ y} := by
        have : algebraMap K Ω ∘ z = algebraMap K Ω ∘ y -
            ∑ k ∈ Sr, algebraMap K Ω (y (π k)) • φ k := by
          rw [hY]
          abel
        rw [hφ'p, this]
        exact Submodule.smul_mem _ _ (Submodule.sub_mem _
          (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
          (Submodule.mem_sup_left hsumW))
      by_cases hkp : k = p
      · rw [hkp]
        exact hpmem
      · have hk' : (k : ℕ) < r := by
          have : (k : ℕ) ≠ r := fun h ↦ hkp (Fin.ext h)
          have hk2 : (k : ℕ) < r + 1 := hk
          omega
        rw [SetLike.mem_coe, hφ'k k hkp]
        exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨k, hk', rfl⟩))
          (Submodule.smul_mem _ _ hpmem)

theorem _root_.Fin.card_subtype_val_lt {n r : ℕ} (hr : r ≤ n) :
    Fintype.card {k : Fin n // (k : ℕ) < r} = r := by
  rw [Fintype.card_subtype]
  simp [Fin.card_filter_val_lt, hr]

/-- **Several pivot steps**: an integral echelon basis of `W ⊆ W'`, `W'` defined over `K`, extends
to one of `W'`, keeping the first `r` pivots. -/
theorem HasIntegralEchelon.exists_of_le {W' : Submodule Ω (Fin n → Ω)}
    (hdef : W'.IsDefinedOver K) : ∀ (d r : ℕ) (π : Equiv.Perm (Fin n))
      (W : Submodule Ω (Fin n → Ω)), finrank Ω W' = r + d → r ≤ n →
      HasIntegralEchelon v π r W → W ≤ W' →
      ∃ π' : Equiv.Perm (Fin n), (∀ m : Fin n, (m : ℕ) < r → π' m = π m) ∧
        HasIntegralEchelon v π' (finrank Ω W') W' := by
  intro d
  induction d with
  | zero =>
    intro r π W hd hr h hWW
    have hfr : finrank Ω W = r := h.finrank_eq.trans (Fin.card_subtype_val_lt hr)
    obtain rfl : W = W' := Submodule.eq_of_le_of_finrank_eq hWW (by omega)
    exact ⟨π, fun _ _ ↦ rfl, by rwa [hfr]⟩
  | succ d ih =>
    intro r π W hd hr h hWW
    obtain ⟨s, hs⟩ := hdef
    have hfr : finrank Ω W = r := h.finrank_eq.trans (Fin.card_subtype_val_lt hr)
    obtain ⟨y, hys, hyW⟩ : ∃ y ∈ s, algebraMap K Ω ∘ y ∉ W := by
      by_contra! hall
      have hle : W' ≤ W := by
        rw [← hs]
        exact Submodule.span_le.mpr fun _ ⟨y, hy, hyx⟩ ↦ hyx ▸ hall y hy
      have := Submodule.finrank_mono hle
      omega
    have hrn : r < n := by
      have := Submodule.finrank_le W'
      rw [Module.finrank_fin_fun] at this
      omega
    obtain ⟨π₁, hπ₁, h₁⟩ := h.exists_sup hrn hyW
    have hle : W ⊔ Submodule.span Ω {algebraMap K Ω ∘ y} ≤ W' := by
      refine sup_le hWW (Submodule.span_le.mpr ?_)
      rintro _ rfl
      rw [← hs]
      exact Submodule.subset_span ⟨y, hys, rfl⟩
    obtain ⟨π', hπ', h'⟩ := ih (r + 1) π₁ _ (by omega) hrn h₁ hle
    exact ⟨π', fun m hm ↦ (hπ' m (by omega)).trans (hπ₁ m hm), h'⟩

/-- `⊥` has the empty echelon basis. -/
theorem hasIntegralEchelon_bot (v : FinitePlace K) (π : Equiv.Perm (Fin n)) :
    HasIntegralEchelon (Ω := Ω) v π 0 ⊥ :=
  ⟨0, fun _ _ h ↦ absurd h (Nat.not_lt_zero _), fun _ _ ↦ by simp, by simp⟩

/-- **The permutation of ES02 (9.24)–(9.33)**: for nested subspaces `W_r ⊆ Ωⁿ` of dimension `r`
defined over `K`, `r` in a finite set `R`, one permutation `π` gives each `W_r` an integral echelon
basis with pivots `π 0, …, π (r-1)`. ES02 build `π` from the top with relations; here it is built
from the bottom by row reduction with the largest pivot. -/
theorem exists_perm_hasIntegralEchelon (v : FinitePlace K) (R : Finset ℕ)
    (W : ℕ → Submodule Ω (Fin n → Ω)) (hdef : ∀ r ∈ R, (W r).IsDefinedOver K)
    (hdim : ∀ r ∈ R, finrank Ω (W r) = r) (hmono : ∀ r ∈ R, ∀ r' ∈ R, r ≤ r' → W r ≤ W r') :
    ∃ π : Equiv.Perm (Fin n), ∀ r ∈ R, HasIntegralEchelon v π r (W r) := by
  classical
  have hrn : ∀ r ∈ R, r ≤ n := fun r hr ↦ by
    have := Submodule.finrank_le (W r)
    rwa [Module.finrank_fin_fun, hdim r hr] at this
  have key : ∀ r, r ∈ R → ∃ π : Equiv.Perm (Fin n), ∀ r' ∈ R, r' ≤ r →
      HasIntegralEchelon v π r' (W r') := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hr
      set R' := R.filter (· < r)
      -- the previous level `r₀` (or `0` with `⊥`), and its permutation
      obtain ⟨r₀, π₀, W₀, hr₀, hW₀, h₀, hprev⟩ : ∃ (r₀ : ℕ) (π₀ : Equiv.Perm (Fin n))
          (W₀ : Submodule Ω (Fin n → Ω)), r₀ ≤ r ∧ W₀ ≤ W r ∧ HasIntegralEchelon v π₀ r₀ W₀ ∧
          ∀ r' ∈ R, r' < r → r' ≤ r₀ ∧ HasIntegralEchelon v π₀ r' (W r') := by
        by_cases hR' : R'.Nonempty
        · set r₀ := R'.max' hR'
          have hr₀ : r₀ ∈ R ∧ r₀ < r := Finset.mem_filter.mp (R'.max'_mem hR')
          obtain ⟨π₀, h₀⟩ := ih r₀ hr₀.2 hr₀.1
          exact ⟨r₀, π₀, W r₀, hr₀.2.le, hmono _ hr₀.1 _ hr hr₀.2.le, h₀ r₀ hr₀.1 le_rfl,
            fun r' hr' hlt ↦ have hle := R'.le_max' r' (Finset.mem_filter.mpr ⟨hr', hlt⟩)
              ⟨hle, h₀ r' hr' hle⟩⟩
        · refine ⟨0, 1, ⊥, Nat.zero_le _, bot_le, hasIntegralEchelon_bot v 1,
            fun r' hr' hlt ↦ absurd ⟨r', Finset.mem_filter.mpr ⟨hr', hlt⟩⟩ hR'⟩
      obtain ⟨π, hπ, h⟩ := HasIntegralEchelon.exists_of_le (hdef r hr) (r - r₀) r₀ π₀ W₀
        (by rw [hdim r hr]; omega) (hr₀.trans (hrn r hr)) h₀ hW₀
      rw [hdim r hr] at h
      refine ⟨π, fun r' hr' hle ↦ ?_⟩
      rcases hle.lt_or_eq with hlt | rfl
      · obtain ⟨hle', h'⟩ := hprev r' hr' hlt
        exact h'.congr fun m hm ↦ hπ m (lt_of_lt_of_le hm hle')
      · exact h
  by_cases hR : R.Nonempty
  · obtain ⟨π, hπ⟩ := key _ (R.max'_mem hR)
    exact ⟨π, fun r hr ↦ hπ r hr (R.le_max' r hr)⟩
  · exact ⟨1, fun r hr ↦ absurd ⟨r, hr⟩ hR⟩

end Echelon

namespace FormSystem

section Combination

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (L : FormSystem K ι) (a : FormWeight K ι)
  {E : Type*} [Field E] [NumberField E] [Algebra K E]

omit [NumberField E] in
/-- The triangle inequality for the local factor at an infinite place. -/
theorem archFactor_sum_smul_le {κ : Type*} (s : Finset κ) (w : InfinitePlace E) (c : κ → E)
    (x : κ → ι → E) :
    L.archFactor a w (∑ j ∈ s, c j • x j) ≤ ∑ j ∈ s, w (c j) * L.archFactor a w (x j) := by
  refine Real.iSup_le (fun i ↦ ?_) (Finset.sum_nonneg fun j _ ↦
    mul_nonneg (by positivity) (L.archFactor_nonneg a w _))
  set M := (L.arch (w.comap (algebraMap K E))).map (algebraMap K E)
  have hA := a.arch_pos (w.comap (algebraMap K E)) i
  rw [Matrix.mulVec_sum, Finset.sum_apply, div_le_iff₀ hA, Finset.sum_mul]
  refine (AbsoluteValue.sum_le _ _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  have h1 : w ((M *ᵥ x j) i) ≤ L.archFactor a w (x j) * a.arch (w.comap (algebraMap K E)) i := by
    rw [← div_le_iff₀ hA]
    exact Finite.le_ciSup_of_le i le_rfl
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- The ultrametric inequality for the local factor at a finite place. -/
theorem finFactor_sum_smul_le {κ : Type*} (s : Finset κ) (w : FinitePlace E) (c : κ → E)
    (x : κ → ι → E) {M : ℝ} (hM : 0 ≤ M) (h : ∀ j ∈ s, w (c j) * L.finFactor a w (x j) ≤ M) :
    L.finFactor a w (∑ j ∈ s, c j • x j) ≤ M := by
  refine Real.iSup_le (fun i ↦ ?_) hM
  set P := (L.fin (w.under K)).map (algebraMap K E)
  have hA : 0 < a.fin (w.under K) i ^ w.localDegree K := pow_pos (a.fin_pos _ i) _
  rw [Matrix.mulVec_sum, Finset.sum_apply, div_le_iff₀ hA]
  refine w.apply_sum_le s (by positivity) fun j hj ↦ ?_
  have h1 : w ((P *ᵥ x j) i) ≤ L.finFactor a w (x j) * a.fin (w.under K) i ^ w.localDegree K := by
    rw [← div_le_iff₀ hA]
    exact Finite.le_ciSup_of_le i le_rfl
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  calc w (c j) * w ((P *ᵥ x j) i)
      ≤ w (c j) * (L.finFactor a w (x j) * a.fin (w.under K) i ^ w.localDegree K) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = w (c j) * L.finFactor a w (x j) * a.fin (w.under K) i ^ w.localDegree K := by ring
    _ ≤ M * a.fin (w.under K) i ^ w.localDegree K := mul_le_mul_of_nonneg_right (h j hj) hA.le

end Combination

/-! ### Davenport bounds -/

section Bounds

variable {Ω : Type*} [Field Ω] [Algebra K Ω] {n : ℕ} (L : FormSystem K (Fin n))
  (a : FormWeight K (Fin n)) (v₀ : FinitePlace K)

/-- **The bounds of EF13 (11.6), (11.7)** for `x ∈ Ωⁿ` over a finite extension `E ⊆ Ω`
containing its coordinates: the local factors are at most `1/n` at the infinite places and at most
`1` at the finite places not above `v₀`, and the coordinates satisfy `|x_i|_w ≤ (b_i ^ [K:ℚ]) ^
{e f}` at the places above `v₀` (`‖x_i‖_w ≤ b_i ^ {d(w|v₀)}` absolutely). -/
def DavenportLe (E : IntermediateField K Ω) [NumberField E] (b : Fin n → ℝ) (x : Fin n → Ω) :
    Prop :=
  ∃ hx : ∀ i, x i ∈ E,
    (∀ w : InfinitePlace E, L.archFactor a w (fun i ↦ ⟨x i, hx i⟩) ≤ (n : ℝ)⁻¹) ∧
    (∀ w : FinitePlace E, w.under K ≠ v₀ → L.finFactor a w (fun i ↦ ⟨x i, hx i⟩) ≤ 1) ∧
    ∀ w : FinitePlace E, w.under K = v₀ → ∀ i,
      w ⟨x i, hx i⟩ ≤ (b i ^ finrank ℚ K) ^ w.localDegree K

variable {L a v₀}

/-- The bounds pass to larger fields. -/
theorem DavenportLe.mono {E E' : IntermediateField K Ω} [NumberField E] [NumberField E']
    (hEE : E ≤ E') {b : Fin n → ℝ} {x : Fin n → Ω}
    (h : L.DavenportLe a v₀ E b x) : L.DavenportLe a v₀ E' b x := by
  obtain ⟨hx, h1, h2, h3⟩ := h
  let : Algebra E E' := (IntermediateField.inclusion hEE).toAlgebra
  have : IsScalarTower K E E' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hy : (fun i ↦ (⟨x i, hEE (hx i)⟩ : E')) = algebraMap E E' ∘ fun i ↦ ⟨x i, hx i⟩ := rfl
  refine ⟨fun i ↦ hEE (hx i), fun w ↦ ?_, fun w hw ↦ ?_, fun w hw i ↦ ?_⟩
  · rw [hy, archFactor_algebraMap]
    exact h1 _
  · rw [hy, finFactor_algebraMap]
    exact pow_le_one₀ (L.finFactor_nonneg a _ _)
      (h2 _ (by rwa [FinitePlace.under_under (K := K) (E := E) w]))
  · have hy' : (⟨x i, hEE (hx i)⟩ : E') = algebraMap E E' ⟨x i, hx i⟩ := rfl
    rw [hy', FinitePlace.apply_algebraMap w (w.under E),
      FinitePlace.localDegree_tower (K := K) (E := E) w, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by positivity)
      (h3 _ (by rwa [FinitePlace.under_under (K := K) (E := E) w]) i) _

variable [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]

/-- **One step of Davenport's construction** (ES02 (9.35)–(9.48), EF13 Lemma 11.3). Let `g_q`
satisfy the bounds with `B λ_q` above `v₀`, let `h_j` (`j < r ≤ q`) satisfy them with
`D B min(λ_i, λ_j)` at the coordinate `π i` and span the same space `W` as the `g_j`, `j < r`,
and let `W` be the graph over the coordinates `π k`, `k < r`, of a matrix `A` over `K` with
`|A|_{v₀} ≤ 1`. If `λ_q ≤ λ_i` for `i ≥ r`, then `h_q = γ₀ g_q + Σ_j γ_j h_j` satisfies the bounds
with `D B min(λ_i, λ_q)`, the `γ` from ES02 Lemma 9.1 for the coefficients `ϑ_j` of the point of
`W` agreeing with `g_q` at the coordinates `π k`, `k < r`. -/
theorem exists_davenport_step {lam : Fin n → ℝ} (hlam0 : ∀ j, 0 ≤ lam j) (hmono : Monotone lam)
    {B D : ℝ} (hB : 0 ≤ B) (hD : ∀ r < n, ((r : ℝ) + 1) ^ (r + 1) * √2 ^ ((r + 1) * r) < D)
    (π : Equiv.Perm (Fin n)) {g : Fin n → Fin n → Ω} (hgli : LinearIndependent Ω g) (q : Fin n)
    {r : ℕ} (hrq : r ≤ q) (hlamq : ∀ i : Fin n, r ≤ i → lam q ≤ lam i)
    (A : Fin n → Fin n → K) (hA0 : ∀ i k : Fin n, r ≤ k → A i k = 0)
    (hA1 : ∀ i k, v₀ (A i k) ≤ 1)
    (hAW : ∀ z ∈ Submodule.span Ω (g '' {j | (j : ℕ) < r}), ∀ i : Fin n, r ≤ i →
      z (π i) = ∑ k, algebraMap K Ω (A i k) * z (π k))
    {E : IntermediateField K Ω} [NumberField E]
    (hgE : L.DavenportLe a v₀ E (fun _ ↦ B * lam q) (g q)) {h : Fin n → Fin n → Ω}
    (hhE : ∀ j : Fin n, (j : ℕ) < r →
      L.DavenportLe a v₀ E (fun c ↦ D * B * min (lam (π.symm c)) (lam j)) (h j))
    (hspan : Submodule.span Ω (h '' {j | (j : ℕ) < r}) =
      Submodule.span Ω (g '' {j | (j : ℕ) < r})) :
    ∃ (E' : IntermediateField K Ω) (_ : NumberField E'), E ≤ E' ∧ ∃ x : Fin n → Ω,
      L.DavenportLe a v₀ E' (fun c ↦ D * B * min (lam (π.symm c)) (lam q)) x ∧
      ∃ c : Ω, c ≠ 0 ∧ x - c • g q ∈ Submodule.span Ω (h '' {j | (j : ℕ) < r}) := by
  classical
  set S : Set (Fin n) := {j | (j : ℕ) < r}
  set W := Submodule.span Ω (g '' S) with hWdef
  -- The coordinates `π k`, `k < r`, determine the points of `W`.
  have hinj : ∀ z ∈ W, (∀ k : Fin n, (k : ℕ) < r → z (π k) = 0) → z = 0 := by
    intro z hz h0
    funext c
    obtain ⟨i, rfl⟩ := π.surjective c
    by_cases hi : (i : ℕ) < r
    · exact h0 i hi
    · rw [hAW z hz i (not_lt.mp hi), Pi.zero_apply]
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      by_cases hk : (k : ℕ) < r
      · rw [h0 k hk, mul_zero]
      · rw [hA0 i k (not_lt.mp hk), map_zero, zero_mul]
  -- So, by dimension, some `z ∈ W` agrees with `g_q` there.
  obtain ⟨z, hzW, hzg⟩ : ∃ z ∈ W, ∀ k : Fin n, (k : ℕ) < r → z (π k) = g q (π k) := by
    let P : W →ₗ[Ω] (S → Ω) :=
      (LinearMap.pi fun k : S ↦ LinearMap.proj (π k)) ∘ₗ W.subtype
    have hPinj : Function.Injective P := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro z hz
      exact Subtype.ext (hinj z z.2 fun k hk ↦ congrFun hz ⟨k, hk⟩)
    have hdim : finrank Ω W = finrank Ω (S → Ω) := by
      rw [Module.finrank_fintype_fun_eq_card, hWdef, Set.image_eq_range]
      exact finrank_span_eq_card (hgli.comp _ Subtype.val_injective)
    obtain ⟨z, hz⟩ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hPinj
        (fun k ↦ g q (π k))
    exact ⟨z, z.2, fun k hk ↦ congrFun hz ⟨k, hk⟩⟩
  have hzh : z ∈ Submodule.span Ω (Set.range fun j : S ↦ h j) := by
    rw [← Set.image_eq_range]
    exact hspan ▸ hzW
  obtain ⟨θ, hθ⟩ := Submodule.mem_span_range_iff_exists_fun Ω |>.mp hzh
  -- ES02 Lemma 9.1 for the `θ_j`.
  have hcard : Fintype.card S < n := by
    refine (Fintype.card_subtype_lt (p := (· ∈ S)) (x := q) ?_).trans_eq (Fintype.card_fin n)
    simpa [S] using hrq
  obtain ⟨Eγ, hEγ, ϑE, γ, γ₀, hϑE, hγ₀, hγa, hγf, hγv⟩ := exists_approx Ω v₀ θ (hD _ hcard)
  -- The common field `E' = E ⊔ E_γ`.
  have : FiniteDimensional K E := Module.Finite.of_restrictScalars_finite ℚ K E
  have : FiniteDimensional K Eγ := Module.Finite.of_restrictScalars_finite ℚ K Eγ
  set E' := E ⊔ Eγ
  have : FiniteDimensional K E' := IntermediateField.finiteDimensional_sup E Eγ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have : NumberField E' := { to_finiteDimensional := Module.Finite.trans K _ }
  have hE1 : E ≤ E' := le_sup_left
  have hE2 : Eγ ≤ E' := le_sup_right
  obtain ⟨hgx, hg1, hg2, hg3⟩ := hgE.mono hE1
  choose hhx hh1 hh2 hh3 using fun j : S ↦ (hhE j j.2).mono hE1
  set ι' := IntermediateField.inclusion hE2
  -- Bounds for the coefficients over `E'`.
  have hca : ∀ w : InfinitePlace E', w (ι' γ₀) ≤ ((Fintype.card S : ℝ) + 1)⁻¹ ∧
      ∀ j, w (ι' (γ j)) ≤ ((Fintype.card S : ℝ) + 1)⁻¹ := fun w ↦
    hγa (w.comap (ι' : Eγ →+* E'))
  have hcf : ∀ w : FinitePlace E', w.under K ≠ v₀ → w (ι' γ₀) ≤ 1 ∧ ∀ j, w (ι' (γ j)) ≤ 1 := by
    intro w hw
    have key : ∀ z : Eγ, (∀ u : FinitePlace Eγ, u.under K ≠ v₀ → u z ≤ 1) → w (ι' z) ≤ 1 := by
      intro z hz
      have := FinitePlace.apply_inclusion_le hE2 w z (b := 1) fun u hu ↦ by
        rw [one_pow]
        exact hz u (by rw [hu]; exact hw)
      rwa [one_pow] at this
    exact ⟨key _ fun u hu ↦ (hγf u hu).1, fun j ↦ key _ fun u hu ↦ (hγf u hu).2 j⟩
  have hcv : ∀ w : FinitePlace E', w.under K = v₀ →
      w (ι' γ₀) ≤ (D ^ finrank ℚ K) ^ w.localDegree K ∧
        ∀ j, w (ι' (γ j) + ι' (ϑE j) * ι' γ₀) ≤ 1 := by
    intro w hw
    refine ⟨FinitePlace.apply_inclusion_le hE2 w γ₀ fun u hu ↦ (hγv u (hu.trans hw)).1,
      fun j ↦ ?_⟩
    have := FinitePlace.apply_inclusion_le hE2 w (γ j + ϑE j * γ₀) (b := 1) fun u hu ↦ by
      rw [one_pow]
      exact (hγv u (hu.trans hw)).2 j
    rwa [one_pow, map_add, map_mul] at this
  -- The new point `y = γ₀ g_q + Σ_j γ_j h_j`.
  set gq : Fin n → E' := fun i ↦ ⟨g q i, hgx i⟩
  set hj : S → Fin n → E' := fun j i ↦ ⟨h j i, hhx j i⟩
  set cc : Option S → E' := fun o ↦ o.elim (ι' γ₀) fun j ↦ ι' (γ j)
  set xx : Option S → Fin n → E' := fun o ↦ o.elim gq hj
  set y : Fin n → E' := ∑ o, cc o • xx o
  have hy : ∀ i, (y i : Ω) = (γ₀ : Ω) * g q i + ∑ j : S, (γ j : Ω) * h j i := by
    intro i
    simp [y, cc, xx, gq, hj, Fintype.sum_option, ι']
  refine ⟨E', inferInstance, hE1, fun i ↦ y i, ⟨fun i ↦ (y i).2, fun w ↦ ?_, fun w hw ↦ ?_, ?_⟩,
    γ₀, fun h0 ↦ hγ₀ (Subtype.ext h0), ?_⟩
  · change L.archFactor a w y ≤ _
    refine (L.archFactor_sum_smul_le a _ w cc xx).trans ?_
    have hterm : ∀ o, w (cc o) * L.archFactor a w (xx o) ≤
        ((Fintype.card S : ℝ) + 1)⁻¹ * (n : ℝ)⁻¹ := by
      rintro (_ | j)
      · exact mul_le_mul (hca w).1 (hg1 w) (L.archFactor_nonneg a w _) (by positivity)
      · exact mul_le_mul ((hca w).2 j) (hh1 j w) (L.archFactor_nonneg a w _) (by positivity)
    calc ∑ o, w (cc o) * L.archFactor a w (xx o)
        ≤ ∑ _o : Option S, ((Fintype.card S : ℝ) + 1)⁻¹ * (n : ℝ)⁻¹ :=
          Finset.sum_le_sum fun o _ ↦ hterm o
      _ = (n : ℝ)⁻¹ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_option, nsmul_eq_mul,
            ← mul_assoc, Nat.cast_add, Nat.cast_one, mul_inv_cancel₀ (by positivity), one_mul]
  · change L.finFactor a w y ≤ 1
    refine L.finFactor_sum_smul_le a _ w cc xx zero_le_one fun o _ ↦ ?_
    rcases o with _ | j
    · exact (mul_le_mul (hcf w hw).1 (hg2 w hw) (L.finFactor_nonneg a w _)
        zero_le_one).trans_eq (one_mul 1)
    · exact (mul_le_mul ((hcf w hw).2 j) (hh2 j w hw) (L.finFactor_nonneg a w _)
        zero_le_one).trans_eq (one_mul 1)
  · intro w hw c
    obtain ⟨i, rfl⟩ := π.surjective c
    change w (y (π i)) ≤
      ((D * B * min (lam (π.symm (π i))) (lam q)) ^ finrank ℚ K) ^ w.localDegree K
    rw [Equiv.symm_apply_apply]
    have hD0 : 0 ≤ D := zero_le_one.trans (by simpa using (hD 0 q.pos).le)
    have hDB : 0 ≤ D * B := mul_nonneg hD0 hB
    set G := ((B * lam q) ^ finrank ℚ K) ^ w.localDegree K
    set T := ((D * B * min (lam i) (lam q)) ^ finrank ℚ K) ^ w.localDegree K
    have hT : 0 ≤ T := pow_nonneg (pow_nonneg (mul_nonneg hDB (le_min (hlam0 i) (hlam0 q))) _) _
    -- `y_{π i} = γ₀ e + Σ_j (γ_j + θ_j γ₀) h_{j, π i}`, `e = g_{q, π i} - Σ_j θ_j h_{j, π i}`.
    set θ' : S → E' := fun j ↦ ι' (ϑE j)
    set e : E' := gq (π i) - ∑ j, θ' j * hj j (π i) with he
    have hdec : y (π i) = ι' γ₀ * e + ∑ j, (ι' (γ j) + θ' j * ι' γ₀) * hj j (π i) := by
      have h1 : y (π i) = ι' γ₀ * gq (π i) + ∑ j, ι' (γ j) * hj j (π i) := by
        simp [y, cc, xx, Fintype.sum_option, Finset.sum_apply]
      have h2 : ∑ j, θ' j * ι' γ₀ * hj j (π i) = ι' γ₀ * ∑ j, θ' j * hj j (π i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [h1, he]
      simp only [add_mul, Finset.sum_add_distrib, h2]
      ring
    -- `e = 0` at the coordinates `π i`, `i < r`, and `e = g_{q, π i} - Σ_k A_ik g_{q, π k}`
    -- otherwise, since `z = Σ_j θ_j h_j ∈ W` agrees with `g_q` at the `π k`, `k < r`.
    have hecoe : (e : Ω) = g q (π i) - z (π i) := by
      rw [← hθ]
      simp [he, θ', gq, hj, hϑE, Finset.sum_apply, ι']
    have hG : 0 ≤ G := pow_nonneg (pow_nonneg (mul_nonneg hB (hlam0 q)) _) _
    have hgq : ∀ c, w (gq c) ≤ G := fun c ↦ hg3 w hw c
    have hwA : ∀ k, w (algebraMap K E' (A i k)) ≤ 1 := fun k ↦ by
      rw [FinitePlace.apply_algebraMap w (w.under K), hw]
      exact pow_le_one₀ (by positivity) (hA1 i k)
    have hterm1 : w (ι' γ₀ * e) ≤ T := by
      by_cases hi : (i : ℕ) < r
      · have he0 : e = 0 := Subtype.ext (by rw [hecoe, hzg i hi, sub_self]; rfl)
        rw [he0, mul_zero, map_zero]
        exact hT
      have hri : r ≤ i := not_lt.mp hi
      have he' : e = gq (π i) - ∑ k, algebraMap K E' (A i k) * gq (π k) := by
        apply Subtype.ext
        have hs : ∑ k, algebraMap K Ω (A i k) * z (π k) =
            ∑ k, algebraMap K Ω (A i k) * g q (π k) := by
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          by_cases hk : (k : ℕ) < r
          · rw [hzg k hk]
          · rw [hA0 i k (not_lt.mp hk), map_zero, zero_mul, zero_mul]
        rw [hecoe, hAW z hzW i hri, hs]
        simp [gq]
      have hwe : w e ≤ G := by
        rw [he', sub_eq_add_neg]
        refine (FinitePlace.add_le w _ _).trans (max_le (hgq _) ?_)
        rw [map_neg_eq_map]
        refine w.apply_sum_le _ hG fun k _ ↦ ?_
        rw [map_mul]
        exact (mul_le_mul (hwA k) (hgq _) (by positivity) zero_le_one).trans_eq (one_mul _)
      rw [map_mul]
      calc w (ι' γ₀) * w e ≤ (D ^ finrank ℚ K) ^ w.localDegree K * G :=
            mul_le_mul (hcv w hw).1 hwe (by positivity) (by positivity)
        _ = T := by
            change (D ^ finrank ℚ K) ^ w.localDegree K * ((B * lam q) ^ finrank ℚ K) ^
              w.localDegree K = ((D * B * min (lam i) (lam q)) ^ finrank ℚ K) ^ w.localDegree K
            rw [min_eq_right (hlamq i hri), ← mul_pow, ← mul_pow, mul_assoc]
    have hterm2 : ∀ j : S, w ((ι' (γ j) + θ' j * ι' γ₀) * hj j (π i)) ≤ T := fun j ↦ by
      rw [map_mul]
      have hjq : lam j ≤ lam q := hmono (Fin.le_iff_val_le_val.mpr (j.2.le.trans hrq))
      have h3 := hh3 j w hw (π i)
      simp only [Equiv.symm_apply_apply] at h3
      calc _ ≤ 1 * ((D * B * min (lam i) (lam j)) ^ finrank ℚ K) ^ w.localDegree K :=
            mul_le_mul ((hcv w hw).2 j) h3 (by positivity) zero_le_one
        _ ≤ T := by
            rw [one_mul]
            have h0 : 0 ≤ D * B * min (lam i) (lam j) :=
              mul_nonneg hDB (le_min (hlam0 i) (hlam0 j))
            exact pow_le_pow_left₀ (pow_nonneg h0 _) (pow_le_pow_left₀ h0
              (mul_le_mul_of_nonneg_left (min_le_min_left _ hjq) hDB) _) _
    rw [hdec]
    exact (FinitePlace.add_le w _ _).trans
      (max_le hterm1 (w.apply_sum_le _ hT fun j _ ↦ hterm2 j))
  · have hx : (fun i ↦ (y i : Ω)) - (γ₀ : Ω) • g q = ∑ j : S, (γ j : Ω) • h j := by
      funext i
      simp [hy, Finset.sum_apply]
    rw [hx]
    exact Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, j.2, rfl⟩)

/-- **ES02 Lemma 9.2, EF13 Lemma 11.3, given the pivots.** Let `g_1, …, g_n` be linearly
independent with the bounds `B λ_j` above `v₀`, `λ` nonnegative and nondecreasing, and for each
`q` let `r_q ≤ q` start a block (`λ_q ≤ λ_i` for `i ≥ r_q`) such that `span(g_j : j < r_q)` is the
graph over the coordinates `π k`, `k < r_q`, of a matrix over `K` with `|·|_{v₀} ≤ 1`. Then there
are `h_1, …, h_n` over one finite extension with `span(h_j : j < k) = span(g_j : j < k)` for all
`k`, the bounds `1/n` and `1` off `v₀`, and `|h_{j, π i}|_w ≤ ((D B min(λ_i, λ_j)) ^ [K:ℚ]) ^ {e f}`
above `v₀` (EF13 (11.5)–(11.7)), `D` beating the constants of ES02 Lemma 9.1. -/
theorem exists_davenport_of_graph {lam : Fin n → ℝ} (hlam0 : ∀ j, 0 ≤ lam j)
    (hmono : Monotone lam) {B D : ℝ} (hB : 0 ≤ B)
    (hD : ∀ r < n, ((r : ℝ) + 1) ^ (r + 1) * √2 ^ ((r + 1) * r) < D) (π : Equiv.Perm (Fin n))
    {g : Fin n → Fin n → Ω} (hgli : LinearIndependent Ω g) (rq : Fin n → ℕ)
    (hrq : ∀ q : Fin n, rq q ≤ q) (hlamq : ∀ q i : Fin n, rq q ≤ i → lam q ≤ lam i)
    (A : Fin n → Fin n → Fin n → K) (hA0 : ∀ q i k : Fin n, rq q ≤ k → A q i k = 0)
    (hA1 : ∀ q i k, v₀ (A q i k) ≤ 1)
    (hAW : ∀ q, ∀ z ∈ Submodule.span Ω (g '' {j | (j : ℕ) < rq q}), ∀ i : Fin n, rq q ≤ i →
      z (π i) = ∑ k, algebraMap K Ω (A q i k) * z (π k))
    {E₀ : IntermediateField K Ω} [NumberField E₀]
    (hgE : ∀ q, L.DavenportLe a v₀ E₀ (fun _ ↦ B * lam q) (g q)) :
    ∃ (E : IntermediateField K Ω) (_ : NumberField E) (h : Fin n → Fin n → Ω),
      (∀ j, L.DavenportLe a v₀ E (fun c ↦ D * B * min (lam (π.symm c)) (lam j)) (h j)) ∧
      ∀ k ≤ n, Submodule.span Ω (h '' {j | (j : ℕ) < k}) =
        Submodule.span Ω (g '' {j | (j : ℕ) < k}) := by
  suffices H : ∀ m ≤ n, ∃ (E : IntermediateField K Ω) (_ : NumberField E), E₀ ≤ E ∧
      ∃ h : Fin n → Fin n → Ω, (∀ j : Fin n, (j : ℕ) < m →
        L.DavenportLe a v₀ E (fun c ↦ D * B * min (lam (π.symm c)) (lam j)) (h j)) ∧
      ∀ k ≤ m, Submodule.span Ω (h '' {j | (j : ℕ) < k}) =
        Submodule.span Ω (g '' {j | (j : ℕ) < k}) by
    obtain ⟨E, hE, -, h, h1, h2⟩ := H n le_rfl
    exact ⟨E, hE, h, fun j ↦ h1 j j.2, h2⟩
  intro m hm
  induction m with
  | zero =>
    exact ⟨E₀, inferInstance, le_rfl, g, fun j hj ↦ absurd hj (Nat.not_lt_zero _),
      fun k hk ↦ by obtain rfl := Nat.le_zero.mp hk; rfl⟩
  | succ m ih =>
    obtain ⟨E, hE, hE₀, h, h1, h2⟩ := ih (Nat.le_of_succ_le hm)
    set q : Fin n := ⟨m, hm⟩
    obtain ⟨E', hE', hEE', x, hx, c, hc, hxc⟩ := L.exists_davenport_step (a := a) (v₀ := v₀)
      hlam0 hmono hB hD π hgli q (hrq q) (hlamq q) (A q) (hA0 q) (hA1 q) (hAW q)
      ((hgE q).mono hE₀) (h := h) (fun j hj ↦ h1 j (lt_of_lt_of_le hj (hrq q)))
      (h2 _ (hrq q))
    set T : Set (Fin n) := {j | (j : ℕ) < m}
    have hTq : ∀ j ∈ T, j ≠ q := fun j hj hjq ↦ by
      rw [hjq] at hj
      exact lt_irrefl m hj
    have hTimg : Function.update h q x '' T = h '' T :=
      Set.image_congr fun j hj ↦ Function.update_of_ne (hTq j hj) _ _
    refine ⟨E', hE', hE₀.trans hEE', Function.update h q x, fun j hj ↦ ?_, fun k hk ↦ ?_⟩
    · rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | hj
      · rw [Function.update_of_ne (hTq j hj)]
        exact (h1 j hj).mono hEE'
      · obtain rfl : j = q := Fin.ext hj
        rw [Function.update_self]
        exact hx
    · rcases lt_or_eq_of_le hk with hk | rfl
      · have hk' : k ≤ m := Nat.le_of_lt_succ hk
        rw [← h2 k hk']
        congr 1
        exact Set.image_congr fun j hj ↦
          Function.update_of_ne (hTq j (lt_of_lt_of_le (show (j : ℕ) < k from hj) hk')) _ _
      · have hset : {j : Fin n | (j : ℕ) < m + 1} = insert q T := by
          ext j
          simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, T, q, Fin.ext_iff]
          omega
        rw [hset, Set.image_insert_eq, Set.image_insert_eq, Submodule.span_insert,
          Submodule.span_insert, Function.update_self, hTimg, ← h2 m le_rfl, sup_comm,
          sup_comm (Submodule.span Ω {g q})]
        have hsub : h '' {j : Fin n | (j : ℕ) < rq q} ⊆ h '' T :=
          Set.image_mono fun j (hj : (j : ℕ) < rq q) ↦ lt_of_lt_of_le hj (hrq q)
        exact Submodule.sup_span_singleton_eq_of_sub_smul_mem
          (U := Submodule.span Ω (h '' T)) hc (Submodule.span_mono hsub hxc)

end Bounds

end FormSystem

/-! ### EF13 Lemma 11.3 -/

/-- `n^n 2^{n(n-1)/2} ≤ 2^{n²}`, from `n² ≤ 2^{n+1}`. -/
theorem pow_mul_sqrt_two_pow_le (n : ℕ) : (n : ℝ) ^ n * √2 ^ (n * (n - 1)) ≤ 2 ^ (n ^ 2) := by
  have h1 : n ^ 2 ≤ 2 ^ (n + 1) := by
    induction n with
    | zero => simp
    | succ m ih =>
      have := Nat.lt_two_pow_self (n := m)
      have h2 : 2 ^ (m + 1 + 1) = 2 * 2 * 2 ^ m := by ring
      have h3 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      rw [h2]
      nlinarith
  have h1' : ((n : ℝ) ^ 2) ≤ 2 ^ (n + 1) := by exact_mod_cast h1
  have hs : √2 ^ (n * (n - 1) * 2) = (2 : ℝ) ^ (n * (n - 1)) := by
    rw [mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
  have key : ((n : ℝ) ^ n * √2 ^ (n * (n - 1))) ^ 2 ≤ ((2 : ℝ) ^ (n ^ 2)) ^ 2 := by
    calc ((n : ℝ) ^ n * √2 ^ (n * (n - 1))) ^ 2
        = ((n : ℝ) ^ 2) ^ n * 2 ^ (n * (n - 1)) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, hs, mul_comm n 2, pow_mul]
      _ ≤ ((2 : ℝ) ^ (n + 1)) ^ n * 2 ^ (n * (n - 1)) := by gcongr
      _ = ((2 : ℝ) ^ (n ^ 2)) ^ 2 := by
          rw [← pow_mul, ← pow_add, ← pow_mul]
          congr 1
          cases n with
          | zero => simp
          | succ m => simp only [Nat.add_sub_cancel]; ring
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp key

namespace FormSystem

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]
  {n : ℕ} (L : FormSystem K (Fin n)) (a : FormWeight K (Fin n))

/-- The successive infima are positive (EF13 Prop. 9.2, lower bound). -/
theorem successiveInf_pos (i : Fin n) : 0 < L.successiveInf a Ω (i + 1) := by
  have h := L.le_prod_successiveInf a (Ω := Ω)
  have hpos : 0 < L.absDet / a.absProd := div_pos L.absDet_pos a.absProd_pos
  by_contra h0
  have h0' : L.successiveInf a Ω (i + 1) = 0 :=
    le_antisymm (not_lt.mp h0) (heightInf_nonneg _)
  rw [Finset.prod_eq_zero (Finset.mem_univ i) h0', mul_zero] at h
  exact absurd h (not_le.mpr hpos)

variable {v₀ : FinitePlace K}

/-- **EF13 Lemma 11.3 (Davenport's lemma)**, ES02 Lemma 9.2 with EF13's modifications. Let `v₀`
be a finite place where the forms are the coordinates and the weights are `1` (EF13 (8.7),
(8.8)), `λ_i` the successive infima, `ε > 0` with EF13 (11.1) (`(1+ε)² λ_i < λ_{i+1}` at every
jump, `(1+ε)^{n+1} n 2^{n²} ≤ 3^{n²}`), and `g_1, …, g_n` linearly independent with
`H(g_j) ≤ (1 + ε/2) λ_j` (11.2). Then there are a finite extension `E ⊆ Ω`, a permutation `π` and
`h_1, …, h_n ∈ Eⁿ` with (11.5) `span(h_1, …, h_k) = span(g_1, …, g_k)`, (11.6) local factors at
most `1/n` at the infinite places and at most `1` at the finite places off `v₀`, and (11.7)
`|h_{j, π(i)}|_w ≤ ((3^{n²} min(λ_i, λ_j)) ^ [K:ℚ]) ^ {e f}` above `v₀`. -/
theorem exists_davenport (hL : L.fin v₀ = 1) (ha : a.fin v₀ = 1) (hn : 0 < n) {ε : ℝ}
    (hε : 0 < ε)
    (hgap : ∀ i : ℕ, i + 1 < n → L.successiveInf a Ω (i + 1) < L.successiveInf a Ω (i + 2) →
      (1 + ε) ^ 2 * L.successiveInf a Ω (i + 1) < L.successiveInf a Ω (i + 2))
    (hε3 : (1 + ε) ^ (n + 1) * n * 2 ^ (n ^ 2) ≤ 3 ^ (n ^ 2))
    {g : Fin n → Fin n → Ω} (hgli : LinearIndependent Ω g)
    (hg : ∀ j : Fin n, L.absMulHeight a (g j) ≤ (1 + ε / 2) * L.successiveInf a Ω (j + 1)) :
    ∃ (E : IntermediateField K Ω) (_ : NumberField E) (π : Equiv.Perm (Fin n))
      (h : Fin n → Fin n → E),
      (∀ k ≤ n, Submodule.span Ω ((fun j i ↦ (h j i : Ω)) '' {j | (j : ℕ) < k}) =
        Submodule.span Ω (g '' {j | (j : ℕ) < k})) ∧
      (∀ j (w : InfinitePlace E), L.archFactor a w (h j) ≤ (n : ℝ)⁻¹) ∧
      (∀ j (w : FinitePlace E), w.under K ≠ v₀ → L.finFactor a w (h j) ≤ 1) ∧
      ∀ i j (w : FinitePlace E), w.under K = v₀ →
        w (h j (π i)) ≤ ((3 ^ (n ^ 2) * min (L.successiveInf a Ω (i + 1))
          (L.successiveInf a Ω (j + 1))) ^ finrank ℚ K) ^ w.localDegree K := by
  classical
  set lam : Fin n → ℝ := fun j ↦ L.successiveInf a Ω (j + 1) with hlam
  have hlampos : ∀ j, 0 < lam j := L.successiveInf_pos a
  have hmono : Monotone lam := fun i j hij ↦
    heightInf_mono (by simpa using hij) (by simp [Nat.succ_le_of_lt j.2])
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- EF13 Lemma 11.2: scalar multiples `g'_j` with the local bounds.
  obtain ⟨E₀, hE₀, y, hy, hya, hyf, hyv⟩ := exists_smul_le_of_lt (L := L) (a := a)
    (fun j ↦ hgli.ne_zero j) v₀ (μ := fun j ↦ (1 + ε) * lam j)
    fun j ↦ (hg j).trans_lt (by nlinarith [hlampos j])
  choose β hβ0 hβ using hy
  set g' : Fin n → Fin n → Ω := fun j i ↦ (y j i : Ω)
  have hg' : ∀ j, g' j = β j • g j := fun j ↦ funext fun i ↦ hβ j i
  have hg'li : LinearIndependent Ω g' := by
    have := hgli.units_smul fun j ↦ Units.mk0 (β j) (hβ0 j)
    convert this using 1
    funext j
    rw [hg' j]
    rfl
  have hspan' : ∀ k : ℕ, Submodule.span Ω (g' '' {j | (j : ℕ) < k}) =
      Submodule.span Ω (g '' {j | (j : ℕ) < k}) := fun k ↦ by
    refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
    · rintro _ ⟨j, hj, rfl⟩
      rw [SetLike.mem_coe, hg' j]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · rintro _ ⟨j, hj, rfl⟩
      have : g j = (β j)⁻¹ • g' j := by rw [hg' j, smul_smul, inv_mul_cancel₀ (hβ0 j), one_smul]
      rw [SetLike.mem_coe, this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  -- The bounds for the `g'_j`, with `B = n (1 + ε)`.
  set B : ℝ := n * (1 + ε)
  have hgE : ∀ q, L.DavenportLe a v₀ E₀ (fun _ ↦ B * lam q) (g' q) := fun q ↦ by
    refine ⟨fun i ↦ (y q i).2, fun w ↦ ?_, fun w hw ↦ hyf q w hw, fun w hw i ↦ ?_⟩
    · simpa using hya q w
    · have h1 : w (y q i) ≤ L.finFactor a w (y q) := by
        unfold finFactor
        refine Finite.le_ciSup_of_le i (le_of_eq ?_)
        simp [hw, hL, ha]
      have h2 := h1.trans (hyv q w hw)
      simp only [Fintype.card_fin] at h2
      convert h2 using 3
      simp only [B]
      ring
  -- The spaces `W_r` at the block starts are defined over `K` (ES02 Cor. 7.5).
  set rq := blockStart lam
  have hrq_lt : ∀ q : Fin n, rq q < n := fun q ↦ (blockStart_le hmono q).trans_lt q.2
  set R : Finset ℕ := Finset.univ.image rq
  set W : ℕ → Submodule Ω (Fin n → Ω) := fun r ↦ Submodule.span Ω (g' '' {j | (j : ℕ) < r})
  have hWrank : ∀ r ≤ n, finrank Ω (W r) = r := fun r hr ↦ by
    change finrank Ω (Submodule.span Ω (g' '' {j : Fin n | (j : ℕ) < r})) = r
    rw [Set.image_eq_range]
    exact (finrank_span_eq_card (hg'li.comp _ Subtype.val_injective)).trans
      (Fin.card_subtype_val_lt hr)
  have hdef : ∀ r ∈ R, (W r).IsDefinedOver K := by
    intro r hr
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hr
    rcases Nat.eq_zero_or_pos (rq q) with h0 | h0
    · refine ⟨∅, ?_⟩
      simp [W, h0]
    · set r := rq q
      have hrn : r < n := hrq_lt q
      have hjump := lt_of_blockStart hmono h0
      have hlr1 : lam ⟨r - 1, by omega⟩ = L.successiveInf a Ω r := by
        simp only [lam]
        congr 1
        omega
      have hlr : lam ⟨r, hrn⟩ = L.successiveInf a Ω (r - 1 + 2) := by
        simp only [lam]
        congr 1
        omega
      have hj' : L.successiveInf a Ω (r - 1 + 1) < L.successiveInf a Ω (r - 1 + 2) := by
        rw [Nat.sub_add_cancel h0, ← hlr1, ← hlr]
        exact hjump
      have hgap' := hgap (r - 1) (by omega) hj'
      rw [← hlr, Nat.sub_add_cancel h0, ← hlr1] at hgap'
      have h0r := (hlampos ⟨r - 1, by omega⟩).le
      have hle1 : (1 + ε / 2) * lam ⟨r - 1, by omega⟩ ≤ (1 + ε) ^ 2 * lam ⟨r - 1, by omega⟩ :=
        mul_le_mul_of_nonneg_right (by nlinarith) h0r
      obtain ⟨μ, hμ1, hμ2⟩ : ∃ μ, (1 + ε / 2) * lam ⟨r - 1, by omega⟩ < μ ∧
          μ < lam ⟨r, hrn⟩ := exists_between (lt_of_le_of_lt hle1 hgap')
      have hle : W r ≤ L.infSpace a Ω μ := Submodule.span_le.mpr fun _ ⟨j, hj, hjx⟩ ↦ by
        rw [← hjx, hg' j]
        refine mem_heightSpace ?_
        rw [L.absMulHeight_smul a _ (hβ0 j)]
        refine (hg j).trans (lt_of_le_of_lt ?_ hμ1).le
        exact mul_le_mul_of_nonneg_left (hmono (Fin.le_iff_val_le_val.mpr
          (by have : (j : ℕ) < r := hj; simp only; omega))) (by positivity)
      have hfin : finrank Ω (L.infSpace a Ω μ) = r :=
        finrank_heightSpace_of_lt (by simpa using hrn)
          (by
            change L.successiveInf a Ω r < μ
            rw [← hlr1]
            exact lt_of_le_of_lt (le_mul_of_one_le_left h0r (by linarith)) hμ1)
          (by simpa [lam] using hμ2)
      rw [Submodule.eq_of_le_of_finrank_eq hle (by rw [hWrank r hrn.le, hfin])]
      exact L.infSpace_isDefinedOver a μ
  have hdim : ∀ r ∈ R, finrank Ω (W r) = r := fun r hr ↦ by
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hr
    exact hWrank _ (hrq_lt q).le
  have hWmono : ∀ r ∈ R, ∀ r' ∈ R, r ≤ r' → W r ≤ W r' := fun r _ r' _ hrr ↦
    Submodule.span_mono (Set.image_mono fun j (hj : (j : ℕ) < r) ↦ lt_of_lt_of_le hj hrr)
  -- The permutation and the graph matrices.
  obtain ⟨π, hπ⟩ := exists_perm_hasIntegralEchelon v₀ R W hdef hdim hWmono
  choose N hN1 hN2 hNW using fun q ↦ hπ (rq q) (Finset.mem_image_of_mem rq (Finset.mem_univ q))
  set A : Fin n → Fin n → Fin n → K := fun q i k ↦ if (k : ℕ) < rq q then N q k (π i) else 0
  have hA0 : ∀ q i k : Fin n, rq q ≤ k → A q i k = 0 := fun q i k hk ↦ by
    simp [A, not_lt.mpr hk]
  have hA1 : ∀ q i k, v₀ (A q i k) ≤ 1 := fun q i k ↦ by
    simp only [A]
    split_ifs
    · exact hN2 q k (π i)
    · simp
  have hAW : ∀ q, ∀ z ∈ Submodule.span Ω (g' '' {j | (j : ℕ) < rq q}), ∀ i : Fin n,
      rq q ≤ i → z (π i) = ∑ k, algebraMap K Ω (A q i k) * z (π k) := by
    intro q z hz i _
    have hz' : z ∈ Submodule.span Ω ((fun k ↦ algebraMap K Ω ∘ N q k) ''
        {k | (k : ℕ) < rq q}) := hNW q ▸ hz
    rw [HasIntegralEchelon.apply_eq (hN1 q) hz' (π i), Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [A]
    split_ifs <;> simp [mul_comm]
  -- The constant of ES02 Lemma 9.1.
  set D : ℝ := (1 + ε) * ((n : ℝ) ^ n * √2 ^ (n * (n - 1)))
  have hD : ∀ r < n, ((r : ℝ) + 1) ^ (r + 1) * √2 ^ ((r + 1) * r) < D := fun r hr ↦ by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : ((r : ℝ) + 1) ^ (r + 1) ≤ (n : ℝ) ^ n :=
      (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hr) _).trans
        (pow_le_pow_right₀ hn1 hr)
    have h2 : √2 ^ ((r + 1) * r) ≤ √2 ^ (n * (n - 1)) :=
      pow_le_pow_right₀ (Real.one_le_sqrt.mpr one_le_two)
        (Nat.mul_le_mul hr (by omega))
    have hpos : 0 < (n : ℝ) ^ n * √2 ^ (n * (n - 1)) := by positivity
    calc ((r : ℝ) + 1) ^ (r + 1) * √2 ^ ((r + 1) * r) ≤ (n : ℝ) ^ n * √2 ^ (n * (n - 1)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ < D := by simp only [D]; nlinarith
  -- ES02 Lemma 9.2.
  obtain ⟨E, hE, h, h1, h2⟩ := exists_davenport_of_graph (L := L) (a := a) (v₀ := v₀)
    (fun j ↦ (hlampos j).le) hmono
    (B := B) (D := D) (by positivity) hD π hg'li rq (blockStart_le hmono)
    (fun q i hi ↦ le_of_blockStart_le hmono hi) A hA0 hA1 hAW hgE
  have hC : D * B ≤ 3 ^ (n ^ 2) := by
    have h3 := pow_mul_sqrt_two_pow_le n
    have h4 : (1 + ε) ^ 2 ≤ (1 + ε) ^ (n + 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    calc D * B = (1 + ε) ^ 2 * n * ((n : ℝ) ^ n * √2 ^ (n * (n - 1))) := by
          simp only [D, B]
          ring
      _ ≤ (1 + ε) ^ (n + 1) * n * 2 ^ (n ^ 2) := by gcongr
      _ ≤ 3 ^ (n ^ 2) := hε3
  choose hx hxa hxf hxv using h1
  refine ⟨E, hE, π, fun j i ↦ ⟨h j i, hx j i⟩, fun k hk ↦ (h2 k hk).trans (hspan' k),
    hxa, hxf, fun i j w hw ↦ ?_⟩
  refine (hxv j w hw (π i)).trans ?_
  simp only [Equiv.symm_apply_apply]
  have hmin : 0 ≤ min (lam i) (lam j) := le_min (hlampos i).le (hlampos j).le
  exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_right hC hmin) _) _

end FormSystem

end NumberField
