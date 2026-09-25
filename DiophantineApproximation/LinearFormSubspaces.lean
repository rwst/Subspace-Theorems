/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SubspaceAlgebraic
public import DiophantineApproximation.RationalPlaces
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# One linear form with algebraic coefficients: the exceptional subspaces

**Layer 7.1, the Subspace Theorem step** (Bombieri–Gubler, Theorem 7.3.2). Let
`α 0, …, α n` be complex algebraic numbers, not all zero, and let `ε > 0`. This file proves that
the integer points `x` of `ℤⁿ⁺¹` with

```text
‖∑ i, α i * x i‖ ≤ mulHeight x ^ (-n - ε)
```

all lie in finitely many **proper rational subspaces** of `ℚⁿ⁺¹`. That is the whole of the
Subspace Theorem's contribution to Layer 7.1; what remains of Bombieri–Gubler's Theorem 7.3.2 is
an induction on the number of variables, which is `DiophantineApproximation/OneLinearForm.lean`.

The system of forms fed to Layer 6.3 is `∑ i, α i X i` together with the coordinate forms
`X i` for `i ≠ j`, at the single place `∞` of `ℚ`, where `j` is an index with `α j ≠ 0`.

## Main results

* `Rat.mulHeight_intCast_le_iSup`: the height of a nonzero integer tuple is at most its sup norm
  at the infinite place — the finite part of the height of an integer tuple is at most `1`.
* `Module.Dual.sumForm` and `Module.Dual.projWithSum`: the linear form `y ↦ ∑ i, a i * y i` and
  the system of coordinate forms with the `j`-th one replaced by it.
* `Module.Dual.linearIndependent_projWithSum`: that system is linearly independent as soon as
  `a j ≠ 0`.
* `Rat.approxProd_projWithSum_le`: the central quantity of the Subspace Theorem at an integer
  point is at most the value of the one nontrivial form, divided by the sup norm of the point.
* `Rat.exists_finset_submodule_of_sumForm_le`: the Subspace Theorem step, for coefficients in a
  number field carrying an absolute value over the infinite place of `ℚ`.
* `Complex.exists_finset_submodule_of_norm_sum_le`: the same for complex algebraic coefficients.

## Implementation notes

⚠ **The hypothesis is `α j ≠ 0`, not independence of the coefficients.** Bombieri–Gubler's
Remark 7.3.3 insists on this, and it is visible here: the system `∑ i, α i X i, X i (i ≠ j)` is
linearly independent exactly when the coefficient `α j` that was displaced is nonzero, whatever
the other coefficients do. Linear independence of the `α i` over `ℚ` is never used and would be
a strictly stronger hypothesis.

⚠ **The exponent drops by one for free, and that is where `-n - ε` becomes `-(n+1) - ε`.** The
central quantity of the Subspace Theorem is `∏ i, ‖L i x‖ / ‖x‖` over the `n + 1` forms, so the
`n` coordinate forms contribute at most `M ^ n` against a denominator `M ^ (n+1)`, where `M` is
the sup norm of `x`: what is left is `‖∑ α i x i‖ / M`. The Subspace Theorem's own exponent
`-(n+1) - ε` is therefore reached from `-n - ε` by the single inequality `mulHeight x ≤ M`.

⚠ **`mulHeight x ≤ M` is a statement about *integer* points and is false for rational ones.**
Over `ℚ` the height of a tuple is `max |x i|` divided by the greatest common divisor of the
coordinates, so for an integer tuple it is at most the sup norm, while for `x = (1/2, 1/3)` it is
the height of `(3, 2)`, namely `3`, against a sup norm of `1/2`. The proof is that every local
factor of the finite part of the height of an integer tuple is at most `1`; Mathlib's
`Rat.mulHeight_eq_max_abs_of_gcd_eq_one` computes that part only for a *coprime* tuple, which
the points here are not.

⚠ **The coefficients are moved into a number field, and the absolute value comes from the
embedding.** Layer 6.3 takes its coefficients in a number field `F` with an absolute value over
the place of `K` in play; here `F = ℚ⟮α 0, …, α n⟯ ⊆ ℂ`, finite over `ℚ` because each `α i` is
algebraic, and the absolute value is `‖·‖` transported along `F ↪ ℂ`. The `LiesOver` hypothesis
is then the single equation `‖(q : ℂ)‖ = |q|` for rational `q`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 7.3.2 and Remark 7.3.3.

This is part of Layer 7.1 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Module Finset Height NumberField

namespace Rat

/-- The height of a nonzero integer tuple is at most its sup norm at the infinite place. -/
theorem mulHeight_intCast_le_iSup {ι : Type*} (v : InfinitePlace ℚ) {x : ι → ℤ}
    (hx : (fun i ↦ (x i : ℚ)) ≠ 0) :
    mulHeight (fun i ↦ (x i : ℚ)) ≤ ⨆ i, v ((x i : ℚ)) := by
  have harch : (∏ u : InfinitePlace ℚ, (⨆ i, u ((x i : ℚ))) ^ u.mult) = ⨆ i, v ((x i : ℚ)) := by
    rw [Fintype.prod_unique]
    have hd : (default : InfinitePlace ℚ) = Rat.infinitePlace := Subsingleton.elim _ _
    rw [hd, NumberField.InfinitePlace.IsReal.mult_eq_one Rat.isReal_infinitePlace, pow_one]
    exact congrArg _ (funext fun i ↦ by rw [Subsingleton.elim Rat.infinitePlace v])
  have hfin : (∏ᶠ u : FinitePlace ℚ, ⨆ i, u ((x i : ℚ))) ≤ 1 := by
    by_cases H : Function.HasFiniteMulSupport fun u : FinitePlace ℚ ↦ ⨆ i, u ((x i : ℚ))
    · calc (∏ᶠ u : FinitePlace ℚ, ⨆ i, u ((x i : ℚ))) ≤ ∏ᶠ _ : FinitePlace ℚ, (1 : ℝ) :=
            finprod_le_finprod₀ H
              (fun u ↦ Real.iSup_nonneg fun i ↦ AbsoluteValue.nonneg _ _) (by fun_prop)
              fun u ↦ Real.iSup_le (fun i ↦ u.apply_intCast_le_one (x i)) zero_le_one
        _ = 1 := finprod_one
    · rw [finprod_of_not_hasFiniteMulSupport H]
  rw [NumberField.mulHeight_eq hx, harch]
  calc (⨆ i, v ((x i : ℚ))) * ∏ᶠ u : FinitePlace ℚ, ⨆ i, u ((x i : ℚ))
      ≤ (⨆ i, v ((x i : ℚ))) * 1 :=
        mul_le_mul_of_nonneg_left hfin (Real.iSup_nonneg fun i ↦ AbsoluteValue.nonneg _ _)
    _ = _ := mul_one _

end Rat

namespace Module.Dual

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The linear form `y ↦ ∑ i, a i * y i` with coefficients `a`. -/
noncomputable def sumForm (a : ι → F) : Dual F (ι → F) := ∑ k, a k • LinearMap.proj k

omit [DecidableEq ι] in
@[simp] theorem sumForm_apply (a y : ι → F) : sumForm a y = ∑ k, a k * y k := by
  simp [sumForm, LinearMap.sum_apply]

/-- The system of coordinate forms with the `j`-th one replaced by `∑ i, a i * y i`. -/
noncomputable def projWithSum (a : ι → F) (j : ι) : ι → Dual F (ι → F) :=
  fun i ↦ if i = j then sumForm a else LinearMap.proj i

@[simp] theorem projWithSum_self (a : ι → F) (j : ι) : projWithSum a j j = sumForm a := by
  simp [projWithSum]

theorem projWithSum_of_ne {a : ι → F} {j i : ι} (h : i ≠ j) :
    projWithSum a j i = LinearMap.proj i := by
  simp [projWithSum, h]

/-- The system is linearly independent as soon as the replaced coefficient is nonzero. -/
theorem linearIndependent_projWithSum {a : ι → F} {j : ι} (hj : a j ≠ 0) :
    LinearIndependent F (projWithSum a j) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hterm : ∀ k i : ι, g i • (projWithSum a j i) (Pi.single k 1)
      = if i = j then g j * a k else if i = k then g i else 0 := by
    intro k i
    by_cases hij : i = j
    · subst hij
      simp [Pi.single_apply, eq_comm]
    · simp [projWithSum_of_ne hij, hij, Pi.single_apply, eq_comm]
  have hev : ∀ k : ι, (∑ i, if i = j then g j * a k else if i = k then g i else 0) = 0 := by
    intro k
    have h : (∑ i, g i • projWithSum a j i) (Pi.single k 1) = 0 := by rw [hg]; simp
    rw [LinearMap.sum_apply] at h
    simp only [LinearMap.smul_apply] at h
    refine Eq.trans ?_ h
    exact Finset.sum_congr rfl fun i _ ↦ (hterm k i).symm
  have hj0 : g j = 0 := by
    have h := hev j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at h
    rw [ite_eq_left rfl, Finset.sum_eq_zero (fun i hi ↦ by
      rw [ite_eq_right (Finset.mem_erase.mp hi).1, ite_eq_right (Finset.mem_erase.mp hi).1]),
      add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hj
  intro k
  by_cases hk : k = j
  · rw [hk]; exact hj0
  · have h := hev k
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at h
    rw [ite_eq_left rfl, hj0, zero_mul, zero_add] at h
    rw [Finset.sum_congr rfl (fun i hi ↦ by
      rw [ite_eq_right (Finset.mem_erase.mp hi).1]), Finset.sum_ite_eq' (Finset.univ.erase j) k g,
      ite_eq_left (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)] at h
    exact h

end Module.Dual

namespace Rat

variable {F : Type*} [Field F] [NumberField F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The central quantity of the Subspace Theorem at an integer point of `ℚⁿ⁺¹`**, for the
system of coordinate forms with one of them replaced by `∑ i, a i * y i`: it is at most the
value of that one form, divided by the sup norm of the point. -/
theorem approxProd_projWithSum_le (W : AbsoluteValue F ℝ) (hW : W.LiesOver Rat.infinitePlace.1)
    (a : ι → F) (j : ι) {x : ι → ℤ} (hx : (fun i ↦ (x i : ℚ)) ≠ 0) :
    approxProd {Rat.infinitePlace} (∅ : Finset (FinitePlace ℚ)) (fun _ ↦ W)
        (fun _ ↦ Module.Dual.projWithSum a j) (fun i ↦ (x i : ℚ))
      ≤ W (∑ k, a k * algebraMap ℚ F (x k)) / ⨆ i, Rat.infinitePlace ((x i : ℚ)) := by
  set M : ℝ := ⨆ i, Rat.infinitePlace ((x i : ℚ)) with hM
  have hMnn : 0 ≤ M := Real.iSup_nonneg fun i ↦ AbsoluteValue.nonneg _ _
  have hMpos : 0 < M := by
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
    exact lt_of_lt_of_le (AbsoluteValue.pos _ hi₀) (Finite.le_ciSup_of_le i₀ le_rfl)
  have hval : ∀ i : ι, W (algebraMap ℚ F ((x i : ℚ))) = Rat.infinitePlace ((x i : ℚ)) := by
    intro i
    have : W.LiesOver Rat.infinitePlace.1 := hW
    rw [AbsoluteValue.apply_algebraMap_of_liesOver (v := Rat.infinitePlace.1) W ((x i : ℚ))]
    rfl
  have hne : Nonempty ι := ⟨(Function.ne_iff.mp hx).choose⟩
  rw [approxProd, Finset.prod_singleton, Finset.prod_empty, mul_one,
    NumberField.InfinitePlace.IsReal.mult_eq_one Rat.isReal_infinitePlace, pow_one]
  have hdiv : (∏ i, W ((Module.Dual.projWithSum a j i) fun k ↦ algebraMap ℚ F ((x k : ℚ))) /
        ⨆ k, Rat.infinitePlace ((x k : ℚ)))
      = (∏ i, W ((Module.Dual.projWithSum a j i) fun k ↦ algebraMap ℚ F ((x k : ℚ))))
          / M ^ Fintype.card ι := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  rw [hdiv]
  have hsplit : (∏ i, W ((Module.Dual.projWithSum a j i) fun k ↦ algebraMap ℚ F ((x k : ℚ))))
      = W (∑ k, a k * algebraMap ℚ F ((x k : ℚ)))
        * ∏ i ∈ Finset.univ.erase j, W (algebraMap ℚ F ((x i : ℚ))) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Module.Dual.projWithSum_self,
      Module.Dual.sumForm_apply]
    refine congrArg _ (Finset.prod_congr rfl fun i hi ↦ ?_)
    rw [Module.Dual.projWithSum_of_ne (Finset.mem_erase.mp hi).1]
    rfl
  rw [hsplit]
  have hprodle : (∏ i ∈ Finset.univ.erase j, W (algebraMap ℚ F ((x i : ℚ))))
      ≤ M ^ (Fintype.card ι - 1) := by
    calc (∏ i ∈ Finset.univ.erase j, W (algebraMap ℚ F ((x i : ℚ))))
        ≤ ∏ _i ∈ Finset.univ.erase j, M := by
          refine Finset.prod_le_prod₀ (fun i _ ↦ W.nonneg _) fun i _ ↦ ?_
          rw [hval i]
          exact Finite.le_ciSup_of_le i le_rfl
      _ = M ^ (Fintype.card ι - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hpow : M ^ Fintype.card ι = M ^ (Fintype.card ι - 1) * M := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow]
  calc (W (∑ k, a k * algebraMap ℚ F ((x k : ℚ)))
        * ∏ i ∈ Finset.univ.erase j, W (algebraMap ℚ F ((x i : ℚ))))
          / (M ^ (Fintype.card ι - 1) * M)
      ≤ (W (∑ k, a k * algebraMap ℚ F ((x k : ℚ))) * M ^ (Fintype.card ι - 1))
          / (M ^ (Fintype.card ι - 1) * M) := by gcongr
    _ = W (∑ k, a k * algebraMap ℚ F ((x k : ℚ))) / M := by
        rw [mul_comm (M ^ (Fintype.card ι - 1)) M,
          mul_div_mul_right _ _ (by positivity : M ^ (Fintype.card ι - 1) ≠ 0)]

omit [DecidableEq ι] in
/-- **One linear form with coefficients in a number field: the Subspace Theorem step.** The
integer points at which a linear form with coefficients in `F` is smaller than
`H(x) ^ (-(n) - ε)`, with `n + 1` the number of variables, lie in finitely many proper rational
subspaces. -/
theorem exists_finset_submodule_of_sumForm_le [Nontrivial ι]
    (W : AbsoluteValue F ℝ) (hW : W.LiesOver Rat.infinitePlace.1)
    (a : ι → F) {j : ι} (hj : a j ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (ι → ℚ)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : ι → ℤ, (fun i ↦ (x i : ℚ)) ≠ 0 →
        W (∑ k, a k * algebraMap ℚ F (x k))
            ≤ mulHeight (fun i ↦ (x i : ℚ)) ^ (-(Fintype.card ι - 1 : ℝ) - ε) →
        ∃ V ∈ T, (fun i ↦ (x i : ℚ)) ∈ V := by
  classical
  obtain ⟨T, hTproper, hTmem⟩ := NumberField.exists_finset_submodule_of_approxProd_le_extension
    (K := ℚ) (F := F) {Rat.infinitePlace} ∅ (fun _ ↦ W)
    (fun v hv ↦ by rw [Finset.mem_singleton.mp hv]; exact hW)
    (fun v hv ↦ absurd hv (Finset.notMem_empty v))
    (fun _ ↦ Module.Dual.projWithSum a j)
    (fun _ _ ↦ Module.Dual.linearIndependent_projWithSum hj)
    (fun _ _ ↦ Module.Dual.linearIndependent_projWithSum hj) hε
  refine ⟨T, hTproper, fun x hx hle ↦ hTmem _ hx ?_⟩
  set H : ℝ := mulHeight (fun i ↦ (x i : ℚ)) with hH
  set M : ℝ := ⨆ i, Rat.infinitePlace ((x i : ℚ)) with hM
  have hHpos : 0 < H := mulHeight_pos _
  have hMnn : 0 ≤ M := Real.iSup_nonneg fun i ↦ AbsoluteValue.nonneg _ _
  have hHM : H ≤ M := mulHeight_intCast_le_iSup Rat.infinitePlace hx
  have hexp : (-(Fintype.card ι - 1 : ℝ) - ε) = (-(Fintype.card ι : ℝ) - ε) + 1 := by ring
  rw [hexp, Real.rpow_add hHpos, Real.rpow_one] at hle
  calc approxProd {Rat.infinitePlace} (∅ : Finset (FinitePlace ℚ)) (fun _ ↦ W)
        (fun _ ↦ Module.Dual.projWithSum a j) (fun i ↦ (x i : ℚ))
      ≤ W (∑ k, a k * algebraMap ℚ F (x k)) / M := approxProd_projWithSum_le W hW a j hx
    _ ≤ (H ^ (-(Fintype.card ι : ℝ) - ε) * H) / M := by gcongr
    _ ≤ (H ^ (-(Fintype.card ι : ℝ) - ε) * H) / H := by gcongr
    _ = H ^ (-(Fintype.card ι : ℝ) - ε) := mul_div_cancel_right₀ _ hHpos.ne'

end Rat

namespace Complex

/-- **One linear form with algebraic coefficients: the Subspace Theorem step.** -/
theorem exists_finset_submodule_of_norm_sum_le {ι : Type*} [Fintype ι]
    [Nontrivial ι] {α : ι → ℂ} (hα : ∀ i, IsAlgebraic ℚ (α i)) {j : ι} (hj : α j ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (ι → ℚ)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : ι → ℤ, (fun i ↦ (x i : ℚ)) ≠ 0 →
        ‖∑ k, α k * (x k : ℂ)‖
            ≤ mulHeight (fun i ↦ (x i : ℚ)) ^ (-(Fintype.card ι - 1 : ℝ) - ε) →
        ∃ V ∈ T, (fun i ↦ (x i : ℚ)) ∈ V := by
  classical
  have hfin : Finite (Set.range α) := (Set.finite_range α).to_subtype
  set F := IntermediateField.adjoin ℚ (Set.range α) with hFdef
  have hFD : FiniteDimensional ℚ F :=
    IntermediateField.finiteDimensional_adjoin
      (fun z hz ↦ by obtain ⟨i, rfl⟩ := hz; exact (hα i).isIntegral)
  have : NumberField F := {}
  have hmem : ∀ i, α i ∈ F := fun i ↦
    IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)
  set a : ι → F := fun i ↦ ⟨α i, hmem i⟩ with ha
  set W : AbsoluteValue F ℝ :=
    (NormedField.toAbsoluteValue ℂ).comp (algebraMap F ℂ).injective with hWdef
  have hWapply : ∀ z : F, W z = ‖(algebraMap F ℂ) z‖ := fun z ↦ rfl
  have hW : W.LiesOver Rat.infinitePlace.1 := by
    refine ⟨AbsoluteValue.ext fun q ↦ ?_⟩
    rw [AbsoluteValue.under_def, AbsoluteValue.comp_apply, hWapply,
      ← IsScalarTower.algebraMap_apply ℚ F ℂ, ← NumberField.InfinitePlace.coe_apply,
      Rat.infinitePlace_apply]
    simp
  obtain ⟨T, hT, hmemT⟩ := Rat.exists_finset_submodule_of_sumForm_le W hW a (j := j)
    (by simpa [ha, Subtype.ext_iff] using hj) hε
  refine ⟨T, hT, fun x hx hle ↦ hmemT x hx ?_⟩
  have hvalue : W (∑ k, a k * algebraMap ℚ F (x k)) = ‖∑ k, α k * (x k : ℂ)‖ := by
    rw [hWapply, map_sum]
    refine congrArg _ (Finset.sum_congr rfl fun k _ ↦ ?_)
    rw [map_mul, ← IsScalarTower.algebraMap_apply ℚ F ℂ]
    simp [ha]
  rw [hvalue]
  exact hle

end Complex
