/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Northcott
public import ArithmeticHeights.Subspace

/-!
# The Northcott property for subspaces

The subspaces of `ι → K` of bounded height are finite in number. This is Northcott's theorem on
projective space, transported along the Plücker embedding: a subspace is determined by its Plücker
point (Layer 3.1) and its height *is* the height of that point (Layer 3.2), so the statement is
Layer 1.1 read through an injection.

## Main results

* `Submodule.finite_setOf_finrank_eq_and_mulHeight_le`: the roadmap's form — for a fixed rank `k`
  and a bound `B`, the subspaces of `ι → K` of rank `k` and height at most `B` are finite in
  number.
* `Submodule.finite_setOf_mulHeight_le`: the same **without the rank condition**. A subspace of
  `ι → K` has rank at most `Fintype.card ι`, so the rank-free set is a finite union of the sets
  above; the rank is not a second parameter that has to be bounded.
* `Submodule.instNorthcottMulHeight` and the five instances beside it: the `Northcott` typeclass
  for each of the six subspace heights — sup-norm, Arakelov and absolute, multiplicative and
  logarithmic. These are what `Northcott.exists_min_image` needs, so a nonempty set of subspaces
  has one of least height.
* `Submodule.mulHeight_le_arakelovMulHeight` of Layer 3.2 is what carries the property to the
  Arakelov normalization, and `Submodule.absMulHeight_eq` to the absolute one. Neither needs the
  Plücker embedding again.

## Implementation notes

The rank-free statement is the stronger one and the instances are stated in terms of it, so the
milestone's rank-fixed form is the one that is proved first and the rank-free one the corollary.
The rank enters only through the index type `Set.powersetCard ι k` of the Plücker coordinates,
which is why the two cannot be merged: the Plücker points of subspaces of different ranks live in
different projective spaces.

⚠ **`Northcott` is a property of the height, not of the ambient space**, so the six instances
above are six separate statements and not one. The multiplicative ones are proved from the
projective height and the logarithmic ones deduced from them by `Northcott.comp_of_bddAbove`,
exactly as Mathlib deduces `Northcott (Height.logHeight₁ (K := K))` from
`Northcott (Height.mulHeight₁ (K := K))` and as `Projectivization.instNorthcottLogHeight` of
Layer 1.1 does.

The hypothesis is `Northcott (Height.mulHeight₁ (K := K))` rather than `NumberField K`, following
Layer 1.1: nothing in the sup-norm half of this file needs a number field. The Arakelov and
absolute halves do, since those heights are only defined there.

## References

M. Hindry and J. H. Silverman, *Diophantine Geometry: An Introduction*, Springer GTM 201 (2000),
Theorem B.2.3, and E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge
University Press (2006), Theorem 2.4.9: the finiteness on projective space that is transported
here. The transport is the Plücker embedding of Bombieri–Gubler 2.8.4, and using it this way —
finiteness of the subspaces of bounded height — is how W. M. Schmidt, "On heights of algebraic
subspaces and diophantine approximations", *Annals of Mathematics* **85** (1967), 430–472, §1
reads his height.

This is Layer 3.7 of the `ArithmeticHeights` roadmap.
-/

public section

open Module

namespace Submodule

/-- The preimage of a set bounded above under `Real.log` is bounded above, by its exponential.
This is the hypothesis of `Northcott.comp_of_bddAbove` for every logarithmic height below. -/
private lemma bddAbove_log_preimage (c : ℝ) : BddAbove (Real.log ⁻¹' {x : ℝ | x ≤ c}) :=
  bddAbove_def.mpr ⟨Real.exp c, fun _ ↦ Real.le_exp_of_log_le⟩

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-!
### The sup-norm height
-/

section Relative

variable [Height.AdmissibleAbsValues K] [Northcott (Height.mulHeight₁ (K := K))]

/-- **Northcott for subspaces of a fixed rank.** The subspaces of `ι → K` of rank `k` and height
at most `B` are finite in number.

The Plücker map is injective on subspaces of rank `k` (`Submodule.pluckerPoint_injective`) and the
height of a subspace is by definition the height of its Plücker point, so this set injects into a
set of bounded height in `Projectivization K (Set.powersetCard ι k → K)`, finite by Layer 1.1. -/
theorem finite_setOf_finrank_eq_and_mulHeight_le (k : ℕ) (B : ℝ) :
    {V : Submodule K (ι → K) | finrank K V = k ∧ V.mulHeight ≤ B}.Finite := by
  have hfin : ((fun V : {V : Submodule K (ι → K) // finrank K V = k} ↦ V.1.pluckerPoint V.2) ⁻¹'
      {x : Projectivization K (Set.powersetCard ι k → K) |
        Projectivization.mulHeight x ≤ B}).Finite :=
    (Projectivization.finite_setOfPred_mulHeight_le B).preimage (pluckerPoint_injective k).injOn
  refine (hfin.image Subtype.val).subset ?_
  rintro V ⟨hV, hB⟩
  refine ⟨⟨V, hV⟩, ?_, rfl⟩
  have : Projectivization.mulHeight (V.pluckerPoint hV) ≤ B := by
    rwa [← mulHeight_eq_mulHeight_pluckerPoint hV]
  exact this

/-- **Northcott for subspaces**, with no condition on the rank: a subspace of `ι → K` has rank at
most `Fintype.card ι`, so the set is the union of the finitely many sets of
`Submodule.finite_setOf_finrank_eq_and_mulHeight_le`. -/
theorem finite_setOf_mulHeight_le (B : ℝ) :
    {V : Submodule K (ι → K) | V.mulHeight ≤ B}.Finite := by
  refine ((Set.finite_Iic (Fintype.card ι)).biUnion
    fun k _ ↦ finite_setOf_finrank_eq_and_mulHeight_le k B).subset fun V hV ↦ ?_
  have hle : finrank K V ≤ Fintype.card ι := by
    simpa [Module.finrank_fintype_fun_eq_card] using Submodule.finrank_le V
  exact Set.mem_biUnion (Set.mem_Iic.2 hle) ⟨rfl, hV⟩

/-- The `Northcott` instance for the height of a subspace. -/
instance instNorthcottMulHeight : Northcott (mulHeight (K := K) (ι := ι)) where
  finite_le := finite_setOf_mulHeight_le

/-- The `Northcott` instance for the logarithmic height of a subspace. -/
instance instNorthcottLogHeight : Northcott (logHeight (K := K) (ι := ι)) := by
  rw [show logHeight (K := K) (ι := ι) = Real.log ∘ mulHeight from
    funext logHeight_eq_log_mulHeight]
  exact Northcott.comp_of_bddAbove _ _ bddAbove_log_preimage

/-- The logarithmic form of `Submodule.finite_setOf_mulHeight_le`. -/
theorem finite_setOf_logHeight_le (B : ℝ) :
    {V : Submodule K (ι → K) | V.logHeight ≤ B}.Finite :=
  Northcott.finite_le B

end Relative

/-!
### The Arakelov height

No second Plücker argument: `Submodule.mulHeight_le_arakelovMulHeight` bounds the sup-norm height
by the Arakelov height with no constant, so a set of bounded Arakelov height is a subset of one of
bounded height.
-/

section Arakelov

variable [NumberField K]

/-- **Northcott for the Arakelov height of a subspace.** -/
theorem finite_setOf_arakelovMulHeight_le (B : ℝ) :
    {V : Submodule K (ι → K) | V.arakelovMulHeight ≤ B}.Finite :=
  (finite_setOf_mulHeight_le B).subset fun V hV ↦ (mulHeight_le_arakelovMulHeight V).trans hV

/-- The `Northcott` instance for the Arakelov height of a subspace. -/
instance instNorthcottArakelovMulHeight : Northcott (arakelovMulHeight (K := K) (ι := ι)) where
  finite_le := finite_setOf_arakelovMulHeight_le

/-- The `Northcott` instance for the logarithmic Arakelov height of a subspace. -/
instance instNorthcottArakelovLogHeight : Northcott (arakelovLogHeight (K := K) (ι := ι)) := by
  rw [show arakelovLogHeight (K := K) (ι := ι) = Real.log ∘ arakelovMulHeight from
    funext arakelovLogHeight_eq_log_arakelovMulHeight]
  exact Northcott.comp_of_bddAbove _ _ bddAbove_log_preimage

/-- The logarithmic form of `Submodule.finite_setOf_arakelovMulHeight_le`. -/
theorem finite_setOf_arakelovLogHeight_le (B : ℝ) :
    {V : Submodule K (ι → K) | V.arakelovLogHeight ≤ B}.Finite :=
  Northcott.finite_le B

end Arakelov

/-!
### The absolute height

The absolute height is the relative one raised to the power `1 / [K : ℚ]`
(`Submodule.absMulHeight_eq`), so a bound `B` on it is the bound `B ^ [K : ℚ]` on the relative one.
-/

section Absolute

variable [NumberField K]

/-- **Northcott for the absolute height of a subspace.** -/
theorem finite_setOf_absMulHeight_le (B : ℝ) :
    {V : Submodule K (ι → K) | V.absMulHeight ≤ B}.Finite := by
  refine (finite_setOf_mulHeight_le (B ^ (finrank ℚ K : ℝ))).subset fun V hV ↦ ?_
  simp only [Set.mem_ofPred_eq, absMulHeight_eq] at hV ⊢
  have hd : (0 : ℝ) < (finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hH : (0 : ℝ) < V.mulHeight := mulHeight_pos V
  have key := Real.rpow_le_rpow (Real.rpow_nonneg hH.le _) hV hd.le
  rwa [← Real.rpow_mul hH.le, inv_mul_cancel₀ hd.ne', Real.rpow_one] at key

/-- The `Northcott` instance for the absolute height of a subspace. -/
instance instNorthcottAbsMulHeight : Northcott (absMulHeight (K := K) (ι := ι)) where
  finite_le := finite_setOf_absMulHeight_le

/-- The `Northcott` instance for the absolute logarithmic height of a subspace. -/
instance instNorthcottAbsLogHeight : Northcott (absLogHeight (K := K) (ι := ι)) := by
  rw [show absLogHeight (K := K) (ι := ι) = Real.log ∘ absMulHeight from
    funext absLogHeight_eq_log_absMulHeight]
  exact Northcott.comp_of_bddAbove _ _ bddAbove_log_preimage

/-- The logarithmic form of `Submodule.finite_setOf_absMulHeight_le`. -/
theorem finite_setOf_absLogHeight_le (B : ℝ) :
    {V : Submodule K (ι → K) | V.absLogHeight ≤ B}.Finite :=
  Northcott.finite_le B

end Absolute

end Submodule

/-!
### Worked examples

The acceptance criteria the roadmap attaches to this layer: that the height bound is what makes
the set finite, that the instance form is usable, and that the milestone is stated over a number
field.
-/

section Examples

open Submodule

/-- The lines `ℚ · (1, n)` of `ℚ²` are pairwise distinct. -/
private lemma span_pair_injective {m n : ℕ}
    (h : span ℚ {![(1 : ℚ), (m : ℚ)]} = span ℚ {![(1 : ℚ), (n : ℚ)]}) : m = n := by
  have hm : ![(1 : ℚ), (m : ℚ)] ∈ span ℚ {![(1 : ℚ), (n : ℚ)]} := by
    rw [← h]
    exact mem_span_singleton_self _
  rw [mem_span_singleton] at hm
  obtain ⟨c, hc⟩ := hm
  have h0 : c = 1 := by simpa using congrFun hc 0
  have h1 : (n : ℚ) = m := by simpa [h0] using congrFun hc 1
  exact_mod_cast h1.symm

/-- **Rejection test.** The height bound is what makes the set finite, not the rank condition:
there are infinitely many lines in `ℚ²`. -/
example : {V : Submodule ℚ (Fin 2 → ℚ) | finrank ℚ V = 1}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ ↦ span ℚ {![(1 : ℚ), (n : ℚ)]}) (fun m n h ↦ span_pair_injective h) fun n ↦ ?_
  exact finrank_span_singleton fun h ↦ by simpa using congrFun h 0

/-- **Acceptance test.** The instance form, not merely the finiteness statement, is what gives the
minimum principle: every nonempty set of subspaces contains one of least height. -/
example {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]
    (s : Set (Submodule K (ι → K))) (hs : s.Nonempty) :
    ∃ V ∈ s, ∀ W ∈ s, V.mulHeight ≤ W.mulHeight :=
  Northcott.exists_min_image _ s hs

/-- **Conformance.** The milestone as the roadmap pins it, over a number field, together with the
rank-free strengthening and the same statement in the other two normalizations. -/
example {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]
    (k : ℕ) (B : ℝ) :
    {V : Submodule K (ι → K) | finrank K V = k ∧ V.mulHeight ≤ B}.Finite ∧
      {V : Submodule K (ι → K) | V.mulHeight ≤ B}.Finite ∧
        {V : Submodule K (ι → K) | V.arakelovMulHeight ≤ B}.Finite ∧
          {V : Submodule K (ι → K) | V.absMulHeight ≤ B}.Finite :=
  ⟨finite_setOf_finrank_eq_and_mulHeight_le k B, finite_setOf_mulHeight_le B,
    finite_setOf_arakelovMulHeight_le B, finite_setOf_absMulHeight_le B⟩

end Examples

end
