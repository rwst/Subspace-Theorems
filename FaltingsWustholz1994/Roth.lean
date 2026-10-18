/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import FaltingsWustholz1994.LinearForms
public import Mathlib.NumberTheory.Real.Irrational

-- Used only inside proofs.
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Roth's theorem from Theorem 8.1

G. Faltings and G. Wüstholz, *Diophantine approximations on projective spaces*, Invent. Math.
**116** (1994), §9, "Let us explain how Theorem 8.1 implies Roth's theorem".

For a real irrational algebraic `ξ`, FW take the one form `f = T₀ − ξ T₁` with an exponent
`c > 2` at the real place. Over `K = ℚ` there is one infinite place and no conjugates are needed:
the form lives over `F = ℚ⟮ξ⟯`, measured by the absolute value of its real embedding. The weight
of every point subspace `U ≠ 0` is `c`: on a line the restriction of `f` is nonzero because `ξ` is
irrational, and on the plane `f` and `T₁` form a basis. So `W(U) = c > 2 ≥ dim U`, Theorem 8.1
(`NumberField.finite_setOf_isSystemSolution`) applies, and `β ↦ (β : 1)` is injective.

This is the paper's test of Theorem 8.1, and the statement is DA 3.3's
`Real.finite_setOf_min_one_abs_sub_le` for irrational `ξ`, there proved through DA 3.2.

## Main results

* `NumberField.finite_setOf_min_one_abs_sub_le_of_irrational`: **Roth's theorem from FW
  Theorem 8.1**.

## Implementation notes

⚠ **The exponent `c` sits strictly between `2` and `κ`.** FW's system bounds
`|f(x)| / ‖x‖_∞`, Roth's `|ξ − β|`, and `‖(β, 1)‖_∞ ≥ 1` only helps. What `c < κ` buys is the
room `H^{−κ} ≤ H^{−c}`; any `c ∈ (2, κ]` works, and the midpoint is taken.

This is milestone FW.3 of `FaltingsWustholz1994/README.md`.
-/

@[expose] public section

open Finset Height Module Module.Dual IntermediateField

namespace NumberField

/-- **Roth's theorem from FW Theorem 8.1.** For a real irrational algebraic number `ξ` and
`κ > 2` there are only finitely many rationals `β` with `min 1 |ξ − β| ≤ H(β) ^ (−κ)`, where
`H(p / q) = max |p| q` is the naive height. -/
theorem finite_setOf_min_one_abs_sub_le_of_irrational {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ)
    (hirr : Irrational ξ) {κ : ℝ} (hκ : 2 < κ) :
    {β : ℚ | min 1 |ξ - (β : ℝ)| ≤ (max β.num.natAbs β.den : ℝ) ^ (-κ)}.Finite := by
  classical
  have hint : IsIntegral ℚ ξ := hξ.isIntegral
  have : FiniteDimensional ℚ ℚ⟮ξ⟯ := adjoin.finiteDimensional hint
  have : NumberField ℚ⟮ξ⟯ := {}
  set w : AbsoluteValue ℚ⟮ξ⟯ ℝ := AbsoluteValue.abs.comp (algebraMap ℚ⟮ξ⟯ ℝ).injective with hwdef
  have hwapply : ∀ x : ℚ⟮ξ⟯, w x = |(algebraMap ℚ⟮ξ⟯ ℝ) x| := fun x ↦ rfl
  have hw : w.LiesOver (Rat.infinitePlace.1) := by
    refine ⟨AbsoluteValue.ext fun q ↦ ?_⟩
    rw [AbsoluteValue.under_def]
    simp only [AbsoluteValue.comp_apply]
    rw [hwapply, ← IsScalarTower.algebraMap_apply ℚ ℚ⟮ξ⟯ ℝ,
      ← NumberField.InfinitePlace.coe_apply, Rat.infinitePlace_apply]
    simp
  set a : ℚ⟮ξ⟯ := ⟨ξ, mem_adjoin_simple_self ℚ ξ⟩ with hadef
  have ha : (algebraMap ℚ⟮ξ⟯ ℝ) a = ξ := rfl
  have hval : ∀ β : ℚ, w ((algebraMap ℚ ℚ⟮ξ⟯) β - a) = |ξ - (β : ℝ)| := fun β ↦ by
    rw [hwapply, map_sub, ha, ← IsScalarTower.algebraMap_apply ℚ ℚ⟮ξ⟯ ℝ, abs_sub_comm]
    simp
  -- The system: one form `T₀ − ξ T₁` with exponent `c` at the real place.
  set c : ℝ := (2 + κ) / 2 with hcdef
  have hc2 : 2 < c := by rw [hcdef]; linarith
  have hcκ : c < κ := by rw [hcdef]; linarith
  set f : Dual ℚ⟮ξ⟯ (Fin 2 → ℚ⟮ξ⟯) := LinearMap.proj 0 - a • LinearMap.proj 1 with hfdef
  set B : AbsoluteValue ℚ ℝ → Finset Unit := fun _ ↦ {()}
  set ℓ : AbsoluteValue ℚ ℝ → Unit → Dual ℚ⟮ξ⟯ (Fin 2 → ℚ⟮ξ⟯) := fun _ _ ↦ f
  set cc : AbsoluteValue ℚ ℝ → Unit → ℝ := fun _ _ ↦ c
  have hf : ∀ x : Fin 2 → ℚ, f (fun j ↦ algebraMap ℚ ℚ⟮ξ⟯ (x j)) =
      algebraMap ℚ ℚ⟮ξ⟯ (x 0) - a * algebraMap ℚ ℚ⟮ξ⟯ (x 1) := fun x ↦ by
    simp [hfdef]
  -- The weight of every `U ≠ 0` is at least `c`.
  have hW : ∀ U : Submodule ℚ (Fin 2 → ℚ), U ≠ ⊥ →
      (finrank ℚ U : ℝ) < maxWeight {Rat.infinitePlace} ∅ B ℓ cc U := by
    intro U hU
    have hmult : (Rat.infinitePlace.mult : ℝ) = 1 := by
      rw [NumberField.InfinitePlace.IsReal.mult_eq_one Rat.isReal_infinitePlace]; simp
    simp only [maxWeight, sum_singleton, hmult, one_mul, sum_empty, add_zero]
    have hd2 : finrank ℚ U ≤ 2 := (Submodule.finrank_le U).trans_eq (by simp)
    have hd0 : finrank ℚ U ≠ 0 := fun h ↦ hU (Submodule.finrank_eq_zero.1 h)
    suffices hcW : c ≤ localMaxWeight (B Rat.infinitePlace.1) (ℓ Rat.infinitePlace.1)
        (cc Rat.infinitePlace.1) U by
      have : (finrank ℚ U : ℝ) ≤ 2 := by exact_mod_cast hd2
      linarith
    have hmem : ∀ i, i ∈ ({()} : Finset Unit).disjSum (univ : Finset (Fin 2)) := by
      rintro (u | j) <;> simp
    rcases (by omega : finrank ℚ U = 1 ∨ finrank ℚ U = 2) with h1 | h2
    · -- a line: `f` alone, nonzero on `U` since `ξ` is irrational
      refine (le_localMaxWeight _ _ _ U (I := {Sum.inl ()}) ⟨fun i _ ↦ hmem i, by simp [h1],
        ?_⟩).trans_eq' (by simp [cc])
      rw [Finset.coe_singleton]
      refine LinearIndepOn.singleton fun h0 ↦ ?_
      obtain ⟨x, hxU, hx0⟩ := (Submodule.ne_bot_iff U).1 hU
      have hx := congrFun h0 ⟨x, hxU⟩
      simp only [extendProj_inl, ℓ, hf, Pi.zero_apply, sub_eq_zero] at hx
      have hxR := congrArg (algebraMap ℚ⟮ξ⟯ ℝ) hx
      rw [map_mul, ha, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        at hxR
      simp only [eq_ratCast] at hxR
      by_cases hx1 : x 1 = 0
      · apply hx0
        funext j
        fin_cases j
        · simpa [hx1] using hxR
        · simpa using hx1
      · apply hirr.ne_rat (x 0 / x 1)
        push_cast
        rw [hxR]
        field_simp
    · -- the plane: `f` and `T₁`
      obtain rfl : U = ⊤ := Submodule.eq_top_of_finrank_eq (h2.trans (by simp))
      refine (le_localMaxWeight _ _ _ ⊤ (I := {Sum.inl (), Sum.inr 1})
        ⟨fun i _ ↦ hmem i, by simp [h2], ?_⟩).trans_eq' (by simp [cc])
      rw [Finset.coe_insert, Finset.coe_singleton]
      refine LinearIndepOn.insert (LinearIndepOn.singleton fun h0 ↦ ?_) ?_
      · have := congrFun h0 ⟨![0, 1], Submodule.mem_top⟩
        simp at this
      · rw [Set.image_singleton, Submodule.mem_span_singleton]
        rintro ⟨t, ht⟩
        have := congrFun ht ⟨![1, 0], Submodule.mem_top⟩
        simp only [extendProj_inl, extendProj_inr, ℓ, hf, Pi.smul_apply, LinearMap.proj_apply,
          smul_eq_mul] at this
        simp at this
  have hfin := finite_setOf_isSystemSolution {Rat.infinitePlace} ∅ (fun _ ↦ w)
    (fun v hv ↦ by rwa [Finset.mem_singleton.mp hv]) (fun v hv ↦ absurd hv (Finset.notMem_empty v))
    B ℓ cc hW
  -- `β ↦ (β : 1)` is injective, and the solutions of height `> 1` solve the system.
  have hne : ∀ β : ℚ, (![β, 1] : Fin 2 → ℚ) ≠ 0 := fun β h ↦ by
    simpa using congrFun h 1
  have hinj : Set.InjOn (fun β : ℚ ↦ Projectivization.mk ℚ ![β, 1] (hne β)) Set.univ := by
    intro β _ β' _ h
    obtain ⟨u, hu⟩ := (Projectivization.mk_eq_mk_iff _ _ _ _ _).1 h
    have h1 := congrFun hu 1
    have h0 := congrFun hu 0
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.smul_apply, Units.smul_def,
      smul_eq_mul, mul_one] at h1 h0
    simp only [h1] at h0
    simpa using h0.symm
  refine ((hfin.preimage (hinj.mono (Set.subset_univ _))).union
    (finite_setOfPred_mulHeight₁_le (K := ℚ) 1)).subset ?_
  intro β hβ
  rw [Set.mem_ofPred_eq] at hβ
  rw [← Nat.cast_max, ← Rat.mulHeight₁_eq_max] at hβ
  by_cases hH : mulHeight₁ β ≤ 1
  · exact Or.inr hH
  refine Or.inl ⟨![β, 1], hne β, rfl, ⟨fun v hv k hk ↦ ?_, fun v hv ↦ absurd hv
    (Finset.notMem_empty v)⟩⟩
  rw [Finset.mem_singleton.mp hv]
  have hH1 : 1 < mulHeight₁ β := lt_of_not_ge hH
  have hlt : mulHeight₁ β ^ (-κ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hH1 (by linarith)
  have hd : |ξ - (β : ℝ)| ≤ mulHeight₁ β ^ (-κ) := by
    rcases min_le_iff.1 hβ with h | h
    · linarith
    · exact h
  have hsup : 1 ≤ ⨆ j, Rat.infinitePlace.1 ((![β, 1] : Fin 2 → ℚ) j) :=
    (le_ciSup (Set.finite_range _).bddAbove (1 : Fin 2)).trans_eq' (by simp)
  have hnum : w (ℓ Rat.infinitePlace.1 k fun j ↦ algebraMap ℚ ℚ⟮ξ⟯ ((![β, 1] : Fin 2 → ℚ) j)) =
      |ξ - (β : ℝ)| := by
    simp only [ℓ, hf]
    simpa using hval β
  rw [hnum, ← mulHeight₁_eq_mulHeight]
  calc |ξ - (β : ℝ)| / ⨆ j, Rat.infinitePlace.1 ((![β, 1] : Fin 2 → ℚ) j)
      ≤ |ξ - (β : ℝ)| := div_le_self (abs_nonneg _) hsup
    _ ≤ mulHeight₁ β ^ (-κ) := hd
    _ ≤ mulHeight₁ β ^ (-c) := Real.rpow_le_rpow_of_exponent_le hH1.le (by linarith)

end NumberField
