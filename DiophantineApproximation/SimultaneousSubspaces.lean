/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.LinearFormSubspaces

/-!
# Two systems of linear forms: the exceptional subspaces

**Layer 7.3, the Subspace Theorem steps** (Schmidt 1970; Bombieri–Gubler, Remark 7.3.4).
Schmidt's two theorems on simultaneous approximation are applications of the Subspace Theorem
over `ℚ` at the single infinite place, to two systems of `n + 1` linear forms in `n + 1`
variables:

```text
X j,                 a k X k  summed over k        (the linear form system)
X j,                 α i X j - X i    for i ≠ j    (the simultaneous system)
```

This file feeds both systems to Layer 6.3 and records what comes back: the integer points at
which the product of the values of the forms is small compared with the sup norm of the point
lie in finitely many proper rational subspaces of `ℚⁿ⁺¹`. The inductions that turn those
subspaces into the finiteness statements are
`DiophantineApproximation/SimultaneousApproximation.lean`.

## Main results

* `Rat.exists_finset_submodule_of_prod_le`: **the Subspace Theorem over `ℚ` for an arbitrary
  system of linearly independent forms** with coefficients in a number field, in the shape the
  applications use — the hypothesis is on the bare product of the values of the forms.
* `Module.Dual.linearIndependent_sumForm`: independent coefficient vectors give independent
  forms.
* `Complex.exists_finset_submodule_of_prod_norm_le`: the same for a matrix of complex algebraic
  coefficients.
* `Complex.exists_finset_submodule_of_norm_sum_mul_prod_le`: the step for the **linear form
  system**, `X i` for `i ≠ j` together with `∑ k, a k X k`.
* `Complex.exists_finset_submodule_of_abs_mul_prod_norm_le`: the step for the **simultaneous
  system**, `X j` together with `α i X j - X i`.

## Implementation notes

⚠ **The product, not the sup norm, is what had to be kept.** Layer 7.1's
`Rat.approxProd_projWithSum_le` bounds the `n` coordinate forms by `M ^ n` with `M` the sup norm
of the point and keeps only the one nontrivial form. Schmidt's theorems are about the *product*
`|q 1 ⋯ q n|`, which can be far smaller than `M ^ n`, so that bound throws away exactly what they
are about. The lemma proved here keeps the product intact: with `Sinf = {∞}`, `Sfin = ∅` and the
multiplicity of the real place of `ℚ` equal to one, the central quantity of the Subspace Theorem
*is* `(∏ i, ‖L i x‖) / M ^ (n + 1)`, and the hypothesis needed is `∏ i, ‖L i x‖ ≤ M ^ (-ε)`.

⚠ **A system of forms is a matrix, and linear independence is checked there.** Rather than
building each system as a family of `Module.Dual` elements, the systems are given as matrices of
complex numbers and turned into forms by `Module.Dual.sumForm`; `linearIndependent_sumForm` says
that step preserves independence, and independence over `ℂ` of the rows implies independence over
the number field they generate, because a relation over that field is a relation over `ℂ`. Both
systems are then triangular, and their independence is two lines of case analysis.

⚠ **Only the infinite place appears.** Schmidt's theorems are archimedean statements over `ℚ`,
so `Sfin` is empty and `Sinf` is the single place `∞`; the finite places enter only through
`Rat.mulHeight_intCast_le_iSup`, which says that the finite part of the height of an integer
point is at most `1` and is what converts the sup norm of the point into its projective height.

## References

W.M. Schmidt, *Simultaneous approximation to algebraic numbers by elements of a number field*,
Monatshefte für Mathematik **79** (1970), 55–66. E. Bombieri and W. Gubler, *Heights in
Diophantine Geometry*, Cambridge University Press (2006), Remark 7.3.4.

This is part of Layer 7.3 of the `DiophantineApproximation` roadmap.
-/

public section

open Module Finset Height NumberField

namespace Rat

variable {F : Type*} [Field F] [NumberField F] {ι : Type*} [Fintype ι]

/-- **The Subspace Theorem over `ℚ` for a full system of linear forms at the infinite place.**
If the product of the values of the `Fintype.card ι` linearly independent forms at an integer
point is at most the sup norm of the point to the power `-ε`, the point lies in one of finitely
many proper rational subspaces. -/
theorem exists_finset_submodule_of_prod_le [Nontrivial ι]
    (W : AbsoluteValue F ℝ) (hW : W.LiesOver Rat.infinitePlace.1)
    (L : ι → Dual F (ι → F)) (hL : LinearIndependent F L) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (ι → ℚ)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : ι → ℤ, (fun i ↦ (x i : ℚ)) ≠ 0 →
        (∏ i, W (L i fun k ↦ algebraMap ℚ F ((x k : ℚ))))
            ≤ (⨆ i, |((x i : ℤ) : ℝ)|) ^ (-ε) →
        ∃ V ∈ T, (fun i ↦ (x i : ℚ)) ∈ V := by
  classical
  obtain ⟨T, hTproper, hTmem⟩ := NumberField.exists_finset_submodule_of_approxProd_le_extension
    (K := ℚ) (F := F) {Rat.infinitePlace} ∅ (fun _ ↦ W)
    (fun v hv ↦ by rw [Finset.mem_singleton.mp hv]; exact hW)
    (fun v hv ↦ absurd hv (Finset.notMem_empty v))
    (fun _ ↦ L) (fun _ _ ↦ hL) (fun _ _ ↦ hL) hε
  refine ⟨T, hTproper, fun x hx hle ↦ hTmem _ hx ?_⟩
  set M : ℝ := ⨆ i, Rat.infinitePlace ((x i : ℚ)) with hM
  have hMeq : M = ⨆ i, |((x i : ℤ) : ℝ)| := by
    simp only [hM, Rat.infinitePlace_apply, Rat.cast_abs, Rat.cast_intCast]
  have hMpos : 0 < M := by
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
    exact lt_of_lt_of_le (AbsoluteValue.pos _ hi₀) (Finite.le_ciSup_of_le i₀ le_rfl)
  have hH : mulHeight (fun i ↦ ((x i : ℤ) : ℚ)) ≤ M :=
    mulHeight_intCast_le_iSup Rat.infinitePlace hx
  have hHpos : 0 < mulHeight (fun i ↦ ((x i : ℤ) : ℚ)) := mulHeight_pos _
  have hcard : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  have hexp : (-(Fintype.card ι : ℝ) - ε) ≤ 0 := by linarith
  refine le_trans ?_ (Real.rpow_le_rpow_of_nonpos hHpos hH hexp)
  rw [approxProd, Finset.prod_singleton, Finset.prod_empty, mul_one,
    NumberField.InfinitePlace.IsReal.mult_eq_one Rat.isReal_infinitePlace, pow_one,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, ← hM,
    show (M ^ Fintype.card ι) = M ^ (Fintype.card ι : ℝ) from (Real.rpow_natCast M _).symm,
    div_le_iff₀ (Real.rpow_pos_of_pos hMpos _), ← Real.rpow_add hMpos,
    show (-(Fintype.card ι : ℝ) - ε) + (Fintype.card ι : ℝ) = -ε by ring, hMeq]
  exact hle

end Rat

namespace Module.Dual

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A linearly independent family of coefficient vectors gives a linearly independent family of
linear forms. -/
theorem linearIndependent_sumForm {a : ι → (ι → F)}
    (ha : LinearIndependent F a) : LinearIndependent F fun i ↦ sumForm (a i) := by
  classical
  rw [Fintype.linearIndependent_iff] at ha ⊢
  intro g hg
  refine ha g (funext fun k ↦ ?_)
  have h : (∑ i, g i • sumForm (a i)) (Pi.single k 1) = 0 := by rw [hg]; simp
  rw [LinearMap.sum_apply] at h
  simp only [LinearMap.smul_apply, sumForm_apply, smul_eq_mul, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  simpa [Finset.sum_apply] using h

end Module.Dual

namespace Complex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The Subspace Theorem over `ℚ` for a full system of linear forms with algebraic
coefficients.** The system is given as the matrix `c` of its coefficients; the hypothesis is
that the rows are linearly independent over `ℂ`. -/
theorem exists_finset_submodule_of_prod_norm_le [Nontrivial ι]
    {c : ι → ι → ℂ} (hc : ∀ i k, IsAlgebraic ℚ (c i k)) (hind : LinearIndependent ℂ c)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (ι → ℚ)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : ι → ℤ, (fun i ↦ (x i : ℚ)) ≠ 0 →
        (∏ i, ‖∑ k, c i k * ((x k : ℤ) : ℂ)‖) ≤ (⨆ i, |((x i : ℤ) : ℝ)|) ^ (-ε) →
        ∃ V ∈ T, (fun i ↦ (x i : ℚ)) ∈ V := by
  classical
  have hfin : Finite (Set.range (fun p : ι × ι ↦ c p.1 p.2)) := (Set.finite_range _).to_subtype
  set F := IntermediateField.adjoin ℚ (Set.range (fun p : ι × ι ↦ c p.1 p.2)) with hFdef
  have hFD : FiniteDimensional ℚ F :=
    IntermediateField.finiteDimensional_adjoin
      (fun z hz ↦ by obtain ⟨p, rfl⟩ := hz; exact (hc p.1 p.2).isIntegral)
  have : NumberField F := {}
  have hmem : ∀ i k, c i k ∈ F := fun i k ↦
    IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self ((i, k) : ι × ι))
  set a : ι → ι → F := fun i k ↦ ⟨c i k, hmem i k⟩ with ha
  set W : AbsoluteValue F ℝ :=
    (NormedField.toAbsoluteValue ℂ).comp (algebraMap F ℂ).injective with hWdef
  have hWapply : ∀ z : F, W z = ‖(algebraMap F ℂ) z‖ := fun z ↦ rfl
  have hW : W.LiesOver Rat.infinitePlace.1 := by
    refine ⟨AbsoluteValue.ext fun q ↦ ?_⟩
    rw [AbsoluteValue.under_def, AbsoluteValue.comp_apply, hWapply,
      ← IsScalarTower.algebraMap_apply ℚ F ℂ, ← NumberField.InfinitePlace.coe_apply,
      Rat.infinitePlace_apply]
    simp
  have haind : LinearIndependent F a := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hgC : ∀ i, (algebraMap F ℂ) (g i) = 0 := by
      rw [Fintype.linearIndependent_iff] at hind
      refine hind (fun i ↦ algebraMap F ℂ (g i)) (funext fun k ↦ ?_)
      have h := congrFun hg k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
      have h2 := congrArg (algebraMap F ℂ) h
      simpa [map_sum, ha] using h2
    intro i
    exact (map_eq_zero_iff _ (algebraMap F ℂ).injective).1 (hgC i)
  obtain ⟨T, hT, hmemT⟩ := Rat.exists_finset_submodule_of_prod_le W hW
    (fun i ↦ Module.Dual.sumForm (a i)) (Module.Dual.linearIndependent_sumForm haind) hε
  refine ⟨T, hT, fun x hx hle ↦ hmemT x hx (le_trans (le_of_eq ?_) hle)⟩
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Module.Dual.sumForm_apply, hWapply, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun k _ ↦ ?_)
  rw [map_mul, ← IsScalarTower.algebraMap_apply ℚ F ℂ]
  simp [ha]

/-- **The Subspace Theorem step for the linear form system.** The integer points at which
`‖∑ k, a k x k‖ * ∏ i ≠ j, |x i|` is at most the sup norm to the power `-ε` lie in finitely many
proper rational subspaces. -/
theorem exists_finset_submodule_of_norm_sum_mul_prod_le [Nontrivial ι]
    {a : ι → ℂ} (ha : ∀ i, IsAlgebraic ℚ (a i)) {j : ι} (hj : a j ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (ι → ℚ)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : ι → ℤ, (fun i ↦ (x i : ℚ)) ≠ 0 →
        ‖∑ k, a k * ((x k : ℤ) : ℂ)‖ * ∏ i ∈ Finset.univ.erase j, |((x i : ℤ) : ℝ)|
            ≤ (⨆ i, |((x i : ℤ) : ℝ)|) ^ (-ε) →
        ∃ V ∈ T, (fun i ↦ (x i : ℚ)) ∈ V := by
  classical
  set c : ι → ι → ℂ := fun i ↦ if i = j then a else Pi.single i (1 : ℂ) with hc
  have hcj : c j = a := by simp [hc]
  have hci : ∀ i, i ≠ j → c i = Pi.single i (1 : ℂ) := fun i hi ↦ by simp [hc, hi]
  have halg : ∀ i k, IsAlgebraic ℚ (c i k) := by
    intro i k
    by_cases hij : i = j
    · rw [hij, hcj]
      exact ha k
    · rw [hci i hij]
      by_cases hki : k = i
      · simpa [Pi.single_apply, hki] using isAlgebraic_one (R := ℚ) (A := ℂ)
      · simpa [Pi.single_apply, hki] using isAlgebraic_zero (R := ℚ) (A := ℂ)
  have hrows : LinearIndependent ℂ c := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hco : ∀ k, ∑ i, g i * c i k = 0 := by
      intro k
      have h := congrFun hg k
      rw [Finset.sum_apply] at h
      simpa only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h
    have hgj : g j = 0 := by
      have h := hco j
      rw [Finset.sum_eq_single j] at h
      · rw [hcj] at h
        exact (mul_eq_zero.mp h).resolve_right hj
      · intro i _ hij
        rw [hci i hij, Pi.single_eq_of_ne (Ne.symm hij), mul_zero]
      · intro hj'; exact absurd (Finset.mem_univ j) hj'
    intro i
    by_cases hij : i = j
    · rw [hij]; exact hgj
    · have h := hco i
      rw [Finset.sum_eq_single i] at h
      · rw [hci i hij, Pi.single_eq_same, mul_one] at h
        exact h
      · intro t _ hti
        by_cases htj : t = j
        · rw [htj, hgj, zero_mul]
        · rw [hci t htj, Pi.single_eq_of_ne (Ne.symm hti), mul_zero]
      · intro hi'; exact absurd (Finset.mem_univ i) hi'
  obtain ⟨T, hT, hmemT⟩ := exists_finset_submodule_of_prod_norm_le halg hrows hε
  refine ⟨T, hT, fun x hx hle ↦ hmemT x hx (le_trans (le_of_eq ?_) hle)⟩
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  refine congrArg₂ _ ?_ (Finset.prod_congr rfl fun i hi ↦ ?_)
  · rw [hcj]
  · rw [hci i (Finset.mem_erase.mp hi).1]
    simp [Pi.single_apply, Finset.sum_ite_eq']

/-- **The Subspace Theorem step for the simultaneous system.** The integer points at which
`|x j| * ∏ i ≠ j, ‖α i * x j - x i‖` is at most the sup norm to the power `-ε` lie in finitely
many proper rational subspaces. -/
theorem exists_finset_submodule_of_abs_mul_prod_norm_le [Nontrivial ι]
    {α : ι → ℂ} (hα : ∀ i, IsAlgebraic ℚ (α i)) (j : ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (ι → ℚ)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : ι → ℤ, (fun i ↦ (x i : ℚ)) ≠ 0 →
        |((x j : ℤ) : ℝ)| * ∏ i ∈ Finset.univ.erase j,
              ‖α i * ((x j : ℤ) : ℂ) - ((x i : ℤ) : ℂ)‖
            ≤ (⨆ i, |((x i : ℤ) : ℝ)|) ^ (-ε) →
        ∃ V ∈ T, (fun i ↦ (x i : ℚ)) ∈ V := by
  classical
  set c : ι → ι → ℂ := fun i ↦ if i = j then Pi.single j (1 : ℂ)
    else α i • Pi.single j (1 : ℂ) - Pi.single i (1 : ℂ) with hc
  have hcj : c j = Pi.single j (1 : ℂ) := by simp [hc]
  have hci : ∀ i, i ≠ j → c i = α i • Pi.single j (1 : ℂ) - Pi.single i (1 : ℂ) :=
    fun i hi ↦ by simp [hc, hi]
  have halg : ∀ i k, IsAlgebraic ℚ (c i k) := by
    intro i k
    by_cases hij : i = j
    · rw [hij, hcj]
      by_cases hkj : k = j
      · simpa [hkj] using isAlgebraic_one (R := ℚ) (A := ℂ)
      · simpa [Pi.single_apply, hkj] using isAlgebraic_zero (R := ℚ) (A := ℂ)
    · rw [hci i hij]
      by_cases hkj : k = j
      · simpa [Pi.single_apply, hkj, Ne.symm hij] using hα i
      · by_cases hki : k = i
        · simpa [Pi.single_apply, hkj, hki, hij] using (isAlgebraic_one (R := ℚ) (A := ℂ)).neg
        · simpa [Pi.single_apply, hkj, hki] using isAlgebraic_zero (R := ℚ) (A := ℂ)
  have hrows : LinearIndependent ℂ c := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hco : ∀ k, ∑ i, g i * c i k = 0 := by
      intro k
      have h := congrFun hg k
      rw [Finset.sum_apply] at h
      simpa only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h
    have hne : ∀ k, k ≠ j → g k = 0 := by
      intro k hkj
      have h := hco k
      rw [Finset.sum_eq_single k] at h
      · rw [hci k hkj] at h
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hkj,
          smul_eq_mul, mul_zero, zero_sub, mul_neg, neg_eq_zero] at h
        simpa using h
      · intro t _ htk
        by_cases htj : t = j
        · rw [htj, hcj, Pi.single_eq_of_ne hkj, mul_zero]
        · rw [hci t htj, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hkj,
            Pi.single_eq_of_ne (Ne.symm htk), smul_zero, sub_zero, mul_zero]
      · intro hk'; exact absurd (Finset.mem_univ k) hk'
    intro i
    by_cases hij : i = j
    · subst hij
      have h := hco i
      rw [Finset.sum_eq_single i] at h
      · rw [hcj, Pi.single_eq_same, mul_one] at h
        exact h
      · intro t _ hti
        rw [hne t hti, zero_mul]
      · intro hi'; exact absurd (Finset.mem_univ i) hi'
    · exact hne i hij
  obtain ⟨T, hT, hmemT⟩ := exists_finset_submodule_of_prod_norm_le halg hrows hε
  refine ⟨T, hT, fun x hx hle ↦ hmemT x hx (le_trans (le_of_eq ?_) hle)⟩
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  refine congrArg₂ _ ?_ (Finset.prod_congr rfl fun i hi ↦ ?_)
  · rw [hcj]
    simp [Pi.single_apply, Finset.sum_ite_eq']
  · rw [hci i (Finset.mem_erase.mp hi).1]
    simp [Pi.single_apply, Finset.sum_ite_eq', sub_mul, Finset.sum_sub_distrib]

end Complex
