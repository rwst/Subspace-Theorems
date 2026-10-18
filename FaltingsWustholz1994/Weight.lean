/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.GeneralPosition
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

-- Used only inside proofs.
import QuantitativeSubspace.FormSubspaceWeight
import STForMathlib.LinearAlgebra.DualScalarExtension

/-!
# The weight of a subspace of points

G. Faltings and G. Wüstholz, *Diophantine approximations on projective spaces*, Invent. Math.
**116** (1994), §4 and §8.

At a place `v`, forms `ℓ_k` over `F` (`k ∈ B`) carry exponents `c_k`, and the coordinate forms
carry the exponent `0` (FW's `p₀ = 0`). For a `K`-subspace `U` of points, the **local weight**
`W_v(U)` is the largest `∑_{i ∈ I} c_i` over the sets `I` of `dim U` of these forms whose
restrictions to `U` are linearly independent. It is FW's `dim U · μ_v(U)` for the filtration that
`U^* = V/U^⊥` inherits as a quotient: the greedy choice of a basis of `U^*` along decreasing
exponents is optimal. With the signs of EF13, `W_v(U)` is `Submodule.formWeight` for the
exponents `−c` (`QuantitativeSubspace/FormSubspaceWeight.lean`).

The **weight** of `U` is `W(U) = ∑_{v ∈ S∞} mult v · W_v(U) + ∑_{v ∈ S₀} W_v(U)`, in the
normalization of DA's `approxProd`, where FW's condition `∑_w μ_w > [L : ℚ]` reads
`W(U) > dim U`.

## Main definitions

* `NumberField.IsWeightBasis`: a basis of `U^*` among the restricted forms.
* `NumberField.localMaxWeight`: the local weight `W_v(U)`.
* `NumberField.maxWeight`: the weight `W(U)`.

## Main results

* `NumberField.exists_isWeightBasis`: the coordinate forms alone contain a basis.
* `NumberField.localMaxWeight_mem`: the local weight is attained.
* `NumberField.le_localMaxWeight`: every basis gives at most the local weight.

## Implementation notes

⚠ **Independence on `U` is independence of functions on `U`.** As in
`DiophantineApproximation/SubspaceSubmodule.lean`, the restrictions are the functions
`x ↦ ℓ_i(x)` on the `K`-points of `U` with values in `F`. That a basis exists at all is a base
change statement: a basis of `U^*` among the coordinate forms over `K`
(`Submodule.formWeight_mem`) stays independent with values in `F`
(`Module.Dual.linearIndependent_algebraMap_comp`).

⚠ **The candidate sets are finite without `Finite κ`.** A basis `I` is a subset of the finset
`B.disjSum univ`, so the candidates form a subset of its powerset, and the supremum is a maximum.

This is milestone FW.2 of `FaltingsWustholz1994/README.md`.
-/

@[expose] public section

open Finset Module Module.Dual

namespace NumberField

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {ι κ : Type*} [Fintype ι]

/-- `I` indexes a basis of the dual of `U` among the forms `ℓ k`, `k ∈ B`, and the coordinate
forms: `I ⊆ B ⊕ ι`, `#I = dim U`, and the restrictions to `U` are linearly independent. -/
def IsWeightBasis (B : Finset κ) (ℓ : κ → Dual F (ι → F)) (U : Submodule K (ι → K))
    (I : Finset (κ ⊕ ι)) : Prop :=
  I ⊆ B.disjSum univ ∧ #I = finrank K U ∧
    LinearIndepOn F (fun i (x : U) ↦ extendProj ℓ i fun j ↦ algebraMap K F ((x : ι → K) j))
      (I : Set (κ ⊕ ι))

/-- The exponents extended by `0` on the coordinate forms. -/
def extendExp (c : κ → ℝ) : κ ⊕ ι → ℝ :=
  Sum.elim c 0

omit [Fintype ι] in
@[simp] theorem extendExp_inl (c : κ → ℝ) (k : κ) : extendExp (ι := ι) c (Sum.inl k) = c k :=
  rfl

omit [Fintype ι] in
@[simp] theorem extendExp_inr (c : κ → ℝ) (j : ι) : extendExp (ι := ι) c (Sum.inr j) = 0 :=
  rfl

/-- **The local weight** `W_v(U)`: the largest sum of exponents over the bases of `U^*` among the
restricted forms. -/
noncomputable def localMaxWeight (B : Finset κ) (ℓ : κ → Dual F (ι → F)) (c : κ → ℝ)
    (U : Submodule K (ι → K)) : ℝ :=
  sSup ((fun I : Finset (κ ⊕ ι) ↦ ∑ i ∈ I, extendExp c i) '' {I | IsWeightBasis B ℓ U I})

/-- **The weight** `W(U) = ∑_{v ∈ S∞} mult v · W_v(U) + ∑_{v ∈ S₀} W_v(U)`. -/
noncomputable def maxWeight [NumberField K] (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K))
    (B : AbsoluteValue K ℝ → Finset κ) (ℓ : AbsoluteValue K ℝ → κ → Dual F (ι → F))
    (c : AbsoluteValue K ℝ → κ → ℝ) (U : Submodule K (ι → K)) : ℝ :=
  ∑ v ∈ Sinf, (v.mult : ℝ) * localMaxWeight (B v.1) (ℓ v.1) (c v.1) U +
    ∑ v ∈ Sfin, localMaxWeight (B v.1) (ℓ v.1) (c v.1) U

variable (B : Finset κ) (ℓ : κ → Dual F (ι → F)) (c : κ → ℝ) (U : Submodule K (ι → K))

/-- **A basis exists**, among the coordinate forms alone. -/
theorem exists_isWeightBasis : ∃ I, IsWeightBasis B ℓ U I := by
  classical
  have hker : ⨅ j, LinearMap.ker (LinearMap.proj (R := K) (φ := fun _ : ι ↦ K) j) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply] at hx
    exact (Submodule.mem_bot K).2 (funext hx)
  obtain ⟨J, ⟨hJcard, hJind⟩, -⟩ :=
    Submodule.formWeight_mem (fun j : ι ↦ LinearMap.proj (R := K) (φ := fun _ : ι ↦ K) j)
      (0 : ι → ℝ) hker U
  refine ⟨J.map ⟨Sum.inr, Sum.inr_injective⟩, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hi
    simp
  · rw [Finset.card_map, hJcard]
  · have h := linearIndependent_algebraMap_comp F (LinearIndepOn.linearIndependent hJind)
    have hmap : ((J.map ⟨Sum.inr, Sum.inr_injective⟩ : Finset (κ ⊕ ι)) : Set (κ ⊕ ι)) =
        Sum.inr '' (J : Set ι) := by
      simp
    rw [hmap]
    exact LinearIndepOn.image_of_comp _ _ h

/-- The candidate sums form a finite nonempty set. -/
theorem finite_isWeightBasis : {I | IsWeightBasis B ℓ U I}.Finite :=
  (B.disjSum univ).powerset.finite_toSet.subset fun _ hI ↦ Finset.mem_powerset.2 hI.1

/-- **The local weight is attained.** -/
theorem localMaxWeight_mem :
    localMaxWeight B ℓ c U ∈
      (fun I : Finset (κ ⊕ ι) ↦ ∑ i ∈ I, extendExp c i) '' {I | IsWeightBasis B ℓ U I} := by
  obtain ⟨I, hI⟩ := exists_isWeightBasis B ℓ U
  exact Set.Nonempty.csSup_mem ⟨_, I, hI, rfl⟩ ((finite_isWeightBasis B ℓ U).image _)

/-- Every basis gives at most the local weight. -/
theorem le_localMaxWeight {I : Finset (κ ⊕ ι)} (hI : IsWeightBasis B ℓ U I) :
    ∑ i ∈ I, extendExp c i ≤ localMaxWeight B ℓ c U :=
  le_csSup ((finite_isWeightBasis B ℓ U).image _).bddAbove ⟨I, hI, rfl⟩

end NumberField
