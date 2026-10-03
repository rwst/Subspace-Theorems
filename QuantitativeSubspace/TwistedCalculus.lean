/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.TwistedSubspaceHeight

-- Used only inside proofs.
import ArithmeticHeights.Hadamard
import ArithmeticHeights.RowEntryHeight

/-!
# The global calculus of twisted heights

D. Roy and J. L. Thunder, *An absolute Siegel's lemma*, J. reine angew. Math. **476** (1996),
1–26, §1 and §4. Three pieces of bookkeeping that the absolute Minkowski theorem (RT96 Thm 6.3)
uses on every page:

* **Base change.** A twist of `Kⁿ` is a twist of `Eⁿ` for every finite extension `E` of `K`, and
  the two give the same absolute height on `Ωⁿ`. RT96 §1 says this in one sentence (`K_𝔸 ⊆ E_𝔸`);
  their §6 uses it whenever a construction needs a larger field of definition.
* **Lines.** The height of the line `Ω x` is the height of the point `x` (RT96 §1), which is how
  the minima, defined through points, meet the duality theorem, stated for subspaces.
* **The lower bound** (RT96 Lemma 4.7): `H_A(V) ≤ H_A(x₁) ⋯ H_A(x_m)` for any basis of `V`, from
  Hadamard's inequality at each place.

## Main definitions

* `NumberField.Twist.baseChange A E`: the twist `A` read over a finite extension `E` of `K`.

## Main results

* `NumberField.Twist.absMulHeight_algHom`: the absolute twisted height of a point is computed in
  any number field it is defined over, through any `K`-embedding into `Ω`.
* `NumberField.Twist.absMulHeight_baseChange`, `NumberField.Twist.absSubspaceHeight_baseChange`,
  `NumberField.Twist.absDet_baseChange`: base change changes no absolute quantity.
* `NumberField.Twist.absSubspaceHeight_span_singleton`: `H_A(Ω x) = H_A(x)`.
* `NumberField.Twist.absSubspaceHeight_span_range_le_prod`: RT96 Lemma 4.7.

This is milestone Q2.2a of `QuantitativeSubspace/README.md` (its first part).
-/

@[expose] public section

open Finset Function Module Matrix exteriorPower IntermediateField

namespace NumberField.Twist

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Two twists with the same components are equal. -/
theorem ext {A B : Twist K ι} (harch : ∀ φ, A.arch φ = B.arch φ)
    (hfin : ∀ v, A.fin v = B.fin v) : A = B := by
  obtain ⟨a, _, _, f, _, _⟩ := A
  obtain ⟨b, _, _, g, _, _⟩ := B
  obtain rfl : a = b := funext harch
  obtain rfl : f = g := funext hfin
  rfl

/-! ### Base change -/

section BaseChange

variable (A : Twist K ι) (E : Type*) [Field E] [NumberField E] [Algebra K E]

/-- **The base change of a twist** to a finite extension `E` of `K`: at a complex embedding of `E`
the component at the embedding of `K` below it, at a finite place of `E` the component at the
place of `K` below it, read in `E`. -/
noncomputable def baseChange : Twist E ι where
  arch ψ := A.arch (ψ.comp (algebraMap K E))
  arch_det_ne_zero ψ := A.arch_det_ne_zero _
  arch_conjugate ψ := by
    rw [ComplexEmbedding.conjugate_comp, A.arch_conjugate]
  fin w := (A.fin (w.under K)).map (algebraMap K E)
  fin_det_ne_zero w := fun h ↦ A.fin_det_ne_zero (w.under K)
    ((map_eq_zero_iff _ (algebraMap K E).injective).mp ((RingHom.map_det _ _).trans h))
  finite_setOf_fin_ne_one :=
    (A.finite_setOf_fin_ne_one.biUnion fun v _ ↦ FinitePlace.finite_placesOver E v).subset
      fun w hw ↦ Set.mem_biUnion (x := w.under K) (fun h ↦ hw (by simp [h]))
        (FinitePlace.mem_placesOver.mpr (FinitePlace.liesOver_under w))

@[simp] theorem baseChange_arch (ψ : E →+* ℂ) :
    (A.baseChange E).arch ψ = A.arch (ψ.comp (algebraMap K E)) := rfl

@[simp] theorem baseChange_fin (w : FinitePlace E) :
    (A.baseChange E).fin w = (A.fin (w.under K)).map (algebraMap K E) := rfl

variable {E} {F : Type*} [Field F] [NumberField F] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

/-- **Base change does not change the twisted height** relative to a field containing `E`. -/
theorem mulHeight_baseChange (x : ι → F) : (A.baseChange E).mulHeight x = A.mulHeight x := by
  rw [mulHeight, mulHeight]
  congr 1
  · refine prod_congr rfl fun φ _ ↦ ?_
    rw [archFactor, archFactor, baseChange_arch, RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq]
  · refine finprod_congr fun w ↦ ?_
    rw [finFactor, finFactor, baseChange_fin, FinitePlace.under_under, Matrix.map_map,
      ← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]

end BaseChange

/-! ### Computing the absolute height in a field of definition -/

section Absolute

variable (A : Twist K ι) {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

/-- **The absolute twisted height in any field of definition**: for a point `f ∘ y` with `y` over
a number field `F` and `f` a `K`-embedding of `F` into `Ω`, it is `H_{A,F}(y) ^ {1/[F:ℚ]}`. -/
theorem absMulHeight_algHom {F : Type*} [Field F] [NumberField F] [Algebra K F] (f : F →ₐ[K] Ω)
    (y : ι → F) : A.absMulHeight (f ∘ y) = A.mulHeight y ^ ((finrank ℚ F : ℝ))⁻¹ := by
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
  rw [A.absMulHeight_eq_of_mem hx, hcomp, mulHeight_algebraMap, h1, pow_one, ← hKF, ← hKG, hFG]

variable (E : Type*) [Field E] [NumberField E] [Algebra K E] [Algebra E Ω] [IsScalarTower K E Ω]
  [Algebra.IsAlgebraic E Ω]

/-- **Base change does not change the absolute twisted height.** -/
theorem absMulHeight_baseChange (x : ι → Ω) :
    (A.baseChange E).absMulHeight x = A.absMulHeight x := by
  have := numberField_adjoin_range (K := E) x
  have : IsScalarTower K (adjoin E (Set.range x)) Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  set y : ι → adjoin E (Set.range x) := fun i ↦ ⟨x i, subset_adjoin E _ ⟨i, rfl⟩⟩
  have hxy : x = IsScalarTower.toAlgHom K (adjoin E (Set.range x)) Ω ∘ y := rfl
  rw [absMulHeight, mulHeight_baseChange]
  conv_rhs => rw [hxy, absMulHeight_algHom]

end Absolute

/-! ### Exterior powers -/

section Exterior

variable {ι : Type*} [Fintype ι] [LinearOrder ι] (A : Twist K ι)

theorem exteriorPower_baseChange (E : Type*) [Field E] [NumberField E] [Algebra K E] (k : ℕ) :
    (A.baseChange E).exteriorPower k = (A.exteriorPower k).baseChange E :=
  ext (fun _ ↦ by rfl) fun w ↦ by
    rw [exteriorPower_fin, baseChange_fin, baseChange_fin, exteriorPower_fin, compound_map]

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

/-- **Base change does not change the absolute height of a subspace.** -/
theorem absSubspaceHeight_baseChange (E : Type*) [Field E] [NumberField E] [Algebra K E]
    [Algebra E Ω] [IsScalarTower K E Ω] [Algebra.IsAlgebraic E Ω] (V : Submodule Ω (ι → Ω)) :
    (A.baseChange E).absSubspaceHeight V = A.absSubspaceHeight V := by
  rw [absSubspaceHeight, absSubspaceHeight, exteriorPower_baseChange, absMulHeight_baseChange]

/-- **Base change does not change `|det A|_𝔸`.** -/
theorem absDet_baseChange (E : Type*) [Field E] [NumberField E] [Algebra K E] :
    (A.baseChange E).absDet = A.absDet := by
  have : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  rw [← absSubspaceHeight_top (Ω := E), ← absSubspaceHeight_top (Ω := E),
    absSubspaceHeight_baseChange]

/-! ### Lines -/

theorem plucker_one_eq_comp {R : Type*} [CommRing R] (x : ι → R) :
    plucker 1 ![x] = x ∘ Set.powersetCard.ofSingleton.symm := by
  funext s
  rw [Function.comp_apply, ← plucker_one_ofSingleton x, Equiv.apply_symm_apply]

variable {E : Type*} [Field E] [NumberField E] [Algebra K E]

omit [NumberField E] in
theorem archFactor_exteriorPower_one (φ : E →+* ℂ) (x : ι → E) :
    (A.exteriorPower 1).archFactor φ (plucker 1 ![x]) = A.archFactor φ x := by
  have h1 : (φ ∘ plucker 1 ![x]) = plucker 1 ![φ ∘ x] := by
    rw [plucker_one_eq_comp, plucker_one_eq_comp]
    rfl
  rw [archFactor, archFactor, exteriorPower_arch, h1, compound_mulVec_plucker]
  have h2 : (plucker 1 fun i ↦ A.arch (φ.comp (algebraMap K E)) *ᵥ ![φ ∘ x] i) =
      plucker 1 ![A.arch (φ.comp (algebraMap K E)) *ᵥ (φ ∘ x)] := by
    congr 1
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  rw [h2, plucker_one_eq_comp, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact Equiv.sum_comp Set.powersetCard.ofSingleton.symm
    fun i ↦ ‖(A.arch (φ.comp (algebraMap K E)) *ᵥ (φ ∘ x)) i‖ ^ 2

theorem finFactor_exteriorPower_one (w : FinitePlace E) (x : ι → E) :
    (A.exteriorPower 1).finFactor w (plucker 1 ![x]) = A.finFactor w x := by
  rw [finFactor, finFactor, exteriorPower_fin, ← compound_map, compound_mulVec_plucker]
  have h2 : (plucker 1 fun i ↦ (A.fin (w.under K)).map (algebraMap K E) *ᵥ ![x] i) =
      plucker 1 ![(A.fin (w.under K)).map (algebraMap K E) *ᵥ x] := by
    congr 1
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  rw [h2, plucker_one_eq_comp]
  exact Equiv.iSup_comp (g := fun i ↦ w (((A.fin (w.under K)).map (algebraMap K E) *ᵥ x) i))
    Set.powersetCard.ofSingleton.symm

theorem mulHeight_exteriorPower_one (x : ι → E) :
    (A.exteriorPower 1).mulHeight (plucker 1 ![x]) = A.mulHeight x := by
  simp only [mulHeight, archFactor_exteriorPower_one, finFactor_exteriorPower_one]

/-- **The height of a line is the height of a point spanning it** (RT96 §1). -/
theorem absSubspaceHeight_span_singleton {x : ι → Ω} (hx : x ≠ 0) :
    A.absSubspaceHeight (Submodule.span Ω {x}) = A.absMulHeight x := by
  have hli : LinearIndependent Ω ![x] := linearIndependent_unique_iff.mpr (by simpa using hx)
  have hspan : Submodule.span Ω (Set.range ![x]) = Submodule.span Ω {x} := by
    rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty]
  have := numberField_adjoin_range (K := K) x
  set y : ι → adjoin K (Set.range x) := fun i ↦ ⟨x i, subset_adjoin K _ ⟨i, rfl⟩⟩
  have hxy : x = (adjoin K (Set.range x)).val ∘ y := rfl
  have hpl : plucker 1 ![x] = (adjoin K (Set.range x)).val ∘ plucker 1 ![y] := by
    rw [plucker_one_eq_comp, plucker_one_eq_comp]
    rfl
  rw [← hspan, absSubspaceHeight_span_range _ hli, hpl, absMulHeight_algHom,
    mulHeight_exteriorPower_one]
  exact (A.absMulHeight_algHom (adjoin K (Set.range x)).val y).symm

/-! ### The lower bound -/

omit [NumberField E] in
/-- **Hadamard's inequality at a complex embedding**, for the twisted local factors. -/
theorem archFactor_exteriorPower_le {k : ℕ} (φ : E →+* ℂ) (y : Fin k → ι → E) :
    (A.exteriorPower k).archFactor φ (plucker k y) ≤ ∏ i, A.archFactor φ (y i) := by
  set M := A.arch (φ.comp (algebraMap K E))
  set B : Matrix (Fin k) ι ℂ := Matrix.of fun i ↦ M *ᵥ (φ ∘ y i)
  have hB : (A.exteriorPower k).archFactor φ (plucker k y) =
      ‖(WithLp.toLp 2 (plucker k B.row) : EuclideanSpace ℂ _)‖ := by
    rw [archFactor, exteriorPower_arch, ← plucker_comp_ringHom, compound_mulVec_plucker]
    rfl
  rw [hB]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _)
    (prod_nonneg fun i _ ↦ A.archFactor_nonneg φ (y i)) two_ne_zero).mp ?_
  rw [EuclideanSpace.norm_sq_eq, ← prod_pow]
  refine (Matrix.sum_sq_norm_plucker_row_le_prod B).trans_eq (prod_congr rfl fun i _ ↦ ?_)
  rw [archFactor, EuclideanSpace.norm_sq_eq]
  rfl

/-- **Hadamard's inequality at a finite place**, for the twisted local factors. -/
theorem finFactor_exteriorPower_le {k : ℕ} (w : FinitePlace E) (y : Fin k → ι → E) :
    (A.exteriorPower k).finFactor w (plucker k y) ≤ ∏ i, A.finFactor w (y i) := by
  rw [finFactor, exteriorPower_fin, ← compound_map, compound_mulVec_plucker]
  exact iSup_plucker_le_prod (v := w.1) (fun a b ↦ FinitePlace.add_le w a b) _

/-- RT96 Lemma 4.7 relative to a number field: the twisted height of the Plücker coordinates of
`k` points is at most the product of their twisted heights. -/
theorem mulHeight_plucker_le_prod {k : ℕ} {y : Fin k → ι → E} (hy : ∀ i, y i ≠ 0) :
    (A.exteriorPower k).mulHeight (plucker k y) ≤ ∏ i, A.mulHeight (y i) := by
  rcases eq_or_ne (plucker k y) 0 with h0 | h0
  · rw [h0, mulHeight_zero]
    exact prod_nonneg fun i _ ↦ A.mulHeight_nonneg _
  have hfin := fun i ↦ A.hasFiniteMulSupport_finFactor (hy i)
  simp only [mulHeight]
  rw [prod_mul_distrib, prod_comm, prod_finprod_comm _ _ fun i _ ↦ hfin i]
  refine mul_le_mul (prod_le_prod₀ (fun φ _ ↦ archFactor_nonneg _ φ _)
    fun φ _ ↦ A.archFactor_exteriorPower_le φ y) ?_
    (finprod_nonneg fun w ↦ finFactor_nonneg _ w _)
    (prod_nonneg fun φ _ ↦ prod_nonneg fun i _ ↦ A.archFactor_nonneg φ _)
  exact finprod_le_finprod_of_nonneg ((A.exteriorPower k).hasFiniteMulSupport_finFactor h0)
    ((univ.finite_toSet.biUnion fun i _ ↦ hfin i).subset
      (univ.mulSupport_prod fun i w ↦ A.finFactor w (y i))) (fun w ↦ finFactor_nonneg _ w _)
    fun w ↦ A.finFactor_exteriorPower_le w y

/-- **The lower bound** (RT96 Lemma 4.7): the absolute twisted height of the span of `k` linearly
independent points is at most the product of their absolute twisted heights. -/
theorem absSubspaceHeight_span_range_le_prod {k : ℕ} {x : Fin k → ι → Ω}
    (hx : LinearIndependent Ω x) :
    A.absSubspaceHeight (Submodule.span Ω (Set.range x)) ≤ ∏ i, A.absMulHeight (x i) := by
  have := numberField_adjoin_range (K := K) (fun p : Fin k × ι ↦ x p.1 p.2)
  set L := adjoin K (Set.range fun p : Fin k × ι ↦ x p.1 p.2)
  set y : Fin k → ι → L := fun i j ↦ ⟨x i j, subset_adjoin K _ ⟨(i, j), rfl⟩⟩
  have hxy : ∀ i, x i = L.val ∘ y i := fun i ↦ rfl
  have hpl : plucker k x = L.val ∘ plucker k y := plucker_comp_ringHom (L.val : L →+* Ω) k y
  have hy : ∀ i, y i ≠ 0 := fun i h ↦ hx.ne_zero i (by rw [hxy i, h]; rfl)
  rw [absSubspaceHeight_span_range _ hx, hpl, absMulHeight_algHom]
  simp_rw [hxy, absMulHeight_algHom]
  rw [Real.finsetProd_rpow _ _ fun i _ ↦ A.mulHeight_nonneg _]
  exact Real.rpow_le_rpow (mulHeight_nonneg _ _) (A.mulHeight_plucker_le_prod hy)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

end Exterior

end NumberField.Twist
