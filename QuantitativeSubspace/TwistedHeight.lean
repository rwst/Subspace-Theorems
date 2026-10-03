/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Arakelov
public import DiophantineApproximation.LocalExtension
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.NumberTheory.NumberField.ProductFormula

-- Used only inside proofs.
import ArithmeticHeights.Extension
import ArithmeticHeights.Northcott

/-!
# Twisted heights

D. Roy and J. L. Thunder, *An absolute Siegel's lemma*, J. reine angew. Math. **476** (1996),
1–26, §1: for a number field `K` and `A ∈ GLₙ(K_𝔸)`, the **twisted height** of a point `x` with
coordinates in a finite extension `E` of `K` is

```text
H_A(x) = ∏_{w | ∞} ‖A_w x‖_w ^ {n_w} · ∏_{w ∤ ∞} ‖A_w x‖_w,
```

the ℓ² norm at the infinite places and the max norm at the finite ones, `A_w` the component of `A`
at the place of `K` below `w`. This file builds it in the carrier fixed by the Q2.0 decision of
`QuantitativeSubspace/README.md`, and proves that it is a height on the points of an algebraic
closure of `K`: read over a larger field it is raised to the relative degree, and it is invariant
under scaling. `NumberField.Twist.absMulHeight` is the resulting absolute twisted height.

**The carrier.** At a finite place a twist matters only through the lattice it defines, and every
lattice of `K_vⁿ` has a basis in `Kⁿ`, so a finite twist is a matrix over `K` itself, the identity
at all but finitely many places, and `‖A_w x‖_w` is read with the absolute value of `E` directly,
with no completion. At the infinite places a twist is a complex matrix for each complex embedding
`φ` of `K`, conjugate embeddings carrying conjugate matrices; a real embedding then carries a real
matrix. ES02's twisted heights (7.3) are the special case of diagonal weights composed with
`K`-rational systems of forms.

## Main definitions

* `NumberField.Twist K ι`: the data of a twist.
* `NumberField.FinitePlace.under`: the finite place of `K` below a finite place of `E`, from
  Mathlib's `HeightOneSpectrum.under`.
* `NumberField.Twist.archFactor`, `NumberField.Twist.finFactor`: the local factors, at a complex
  embedding of `E` and at a finite place of `E`.
* `NumberField.Twist.mulHeight`: the twisted height of `x : ι → E`, relative to `E`.
* `NumberField.Twist.compConst A B`: the comparison constant of RT96 Prop. 4.1, the product over
  `K` of the operator norms of `A_φ B_φ⁻¹` and the largest entries of `A_v B_v⁻¹`.
* `1 : NumberField.Twist K ι`: the trivial twist, whose height is the untwisted `H_1`.
* `NumberField.Twist.absMinimum A Ω i`: the `i`-th absolute minimum `μ_i(A)` of RT96 Def. 6.1,
  an infimum over `i` points of `Ωⁿ` linearly independent over `Ω`.

## Main results

* `NumberField.Twist.mulHeight_algebraMap`: over a finite extension `F / E` the twisted height is
  raised to the power `[F : E]` — so `H_A(x) ^ (1 / [E : ℚ])` does not depend on `E`.
* `NumberField.Twist.mulHeight_smul`: the product formula makes it invariant under scaling.
* `NumberField.Twist.mulHeight_pos`: it is positive at every nonzero point.
* `NumberField.FinitePlace.finprod_under_pow_localDegree`: the finite half of every extension
  formula for a height, the counterpart of `NumberField.prod_infinitePlace_pow_mult_eq`.
* `NumberField.Twist.mulHeight_le_compConst_pow_mul` and its absolute form
  `NumberField.Twist.absMulHeight_le_compConst_rpow_mul`: RT96 Prop. 4.1, `H_A ≤ c · H_B`.
* `NumberField.Twist.mulHeight_one_eq`: `H_1` is `NumberField.arakelovMulHeight`.
* `NumberField.Twist.compConst_rpow_neg_le_absMulHeight`: the absolute twisted height is bounded
  below by a positive constant on nonzero points.
* `NumberField.Twist.finite_setOf_mulHeight_rep_le`: Northcott's theorem over a fixed `E`.
* `NumberField.Twist.absMinimum_le_absMinimum`, `NumberField.Twist.absMinimum_pos`,
  `NumberField.Twist.exists_linearIndependent_absMulHeight_lt`: the minima increase, are positive,
  and are approached from above by independent points.

## Implementation notes

⚠ **The archimedean product is over complex embeddings, not over infinite places.** Each complex
place is counted twice, once per embedding, which is its multiplicity `2`, so the product is
RT's `∏_{w | ∞} ‖A_w x‖_w ^ {n_w}`; and the extension formula is then the count of extensions of
an embedding, `NumberField.prod_comp_eq_prod_pow`, with no choice of an embedding per place. The
compatibility `arch_conjugate` is not used by the definition; it is what makes the archimedean
factor a function of the place.

⚠ **The height of `0` is `0`**, not Mathlib's junk value `1`: every archimedean factor vanishes.
The extension formula holds there too, and every later statement is about nonzero points.

This is milestone Q2.1 of `QuantitativeSubspace/README.md` (Q2.1a, the height of a point;
Q2.1b, the comparison with the untwisted height; Q2.1c, the absolute minima).
-/

@[expose] public section

open Finset Function Module Matrix IsDedekindDomain

namespace NumberField

/-! ### The place below a finite place -/

namespace FinitePlace

variable {K E F : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
  [Field F] [NumberField F] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

variable (K) in
/-- The finite place of `K` below a finite place of `E`. -/
noncomputable def under (w : FinitePlace E) : FinitePlace K :=
  FinitePlace.mk (w.maximalIdeal.under (𝓞 K))

@[simp] theorem maximalIdeal_under (w : FinitePlace E) :
    (w.under K).maximalIdeal = w.maximalIdeal.under (𝓞 K) :=
  FinitePlace.maximalIdeal_mk _

instance liesOver_under (w : FinitePlace E) : w.LiesOver (w.under K) :=
  ⟨by rw [maximalIdeal_under]; rfl⟩

/-- A finite place of `E` lies over exactly one finite place of `K`. -/
theorem eq_under {w : FinitePlace E} {v : FinitePlace K} [h : w.LiesOver v] : v = w.under K := by
  refine FinitePlace.maximalIdeal_injective (HeightOneSpectrum.ext ?_)
  change v.maximalIdeal.asIdeal = (w.under K).maximalIdeal.asIdeal
  rw [maximalIdeal_under]
  exact h.over

theorem liesOver_iff_eq_under {w : FinitePlace E} {v : FinitePlace K} :
    w.LiesOver v ↔ v = w.under K :=
  ⟨fun _ ↦ eq_under, fun h ↦ h ▸ liesOver_under w⟩

/-- The place of `K` below a place of `K` is the place itself. -/
@[simp] theorem under_self (w : FinitePlace K) : w.under K = w := by
  refine FinitePlace.maximalIdeal_injective (HeightOneSpectrum.ext ?_)
  simp only [maximalIdeal_under, HeightOneSpectrum.under_asIdeal]
  ext x
  rw [Ideal.under, Ideal.mem_comap]
  convert Iff.rfl using 2
  exact RingOfIntegers.ext rfl

omit [NumberField K] [NumberField E] [NumberField F] in
private theorem isScalarTower_ringOfIntegers : IsScalarTower (𝓞 K) (𝓞 E) (𝓞 F) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ RingOfIntegers.ext <| by
    exact IsScalarTower.algebraMap_apply K E F (x : K)

theorem under_under (w : FinitePlace F) : (w.under E).under K = w.under K := by
  have := isScalarTower_ringOfIntegers (K := K) (E := E) (F := F)
  refine FinitePlace.maximalIdeal_injective (HeightOneSpectrum.ext ?_)
  simp only [maximalIdeal_under, HeightOneSpectrum.under_asIdeal]
  exact Ideal.under_under _

/-- **The finite half of every extension formula for a height.** A product over the finite places
of `F` of a local factor that reads a place `w` only through the place below it in `E`, raised to
the local degree of `w`, is the `[F : E]`-th power of the corresponding product over `E`. -/
theorem finprod_under_pow_localDegree (f : FinitePlace E → ℝ) (hf : f.HasFiniteMulSupport) :
    ∏ᶠ w : FinitePlace F, f (w.under E) ^ w.localDegree E = (∏ᶠ v, f v) ^ finrank E F := by
  classical
  set S := hf.toFinset
  set T := S.biUnion (placesOverFinset F)
  have hsub : mulSupport (fun w : FinitePlace F ↦ f (w.under E) ^ w.localDegree E) ⊆ T := by
    intro w hw
    have hS : w.under E ∈ S :=
      (Set.Finite.mem_toFinset hf).mpr fun h ↦ hw (by simp [h])
    exact Finset.mem_biUnion.mpr ⟨_, hS, mem_placesOverFinset.mpr (liesOver_under w)⟩
  have hdisj : (S : Set (FinitePlace E)).PairwiseDisjoint (placesOverFinset F) := by
    intro v₁ _ v₂ _ hne
    refine Finset.disjoint_left.mpr fun w h₁ h₂ ↦ hne ?_
    rw [mem_placesOverFinset, liesOver_iff_eq_under] at h₁ h₂
    rw [h₁, h₂]
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub,
    finprod_eq_prod_of_mulSupport_subset f (Set.Finite.coe_toFinset hf).symm.subset,
    Finset.prod_biUnion hdisj, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [Finset.prod_congr rfl fun w hw ↦ by
      rw [← eq_under (h := mem_placesOverFinset.mp hw)],
    Finset.prod_pow_eq_pow_sum, sum_localDegree]

/-- A local factor read through the place below has finite multiplicative support when the
factor below has. -/
theorem hasFiniteMulSupport_comp_under {f : FinitePlace E → ℝ} (hf : f.HasFiniteMulSupport)
    (g : FinitePlace F → ℕ) :
    (fun w : FinitePlace F ↦ f (w.under E) ^ g w).HasFiniteMulSupport :=
  (hf.biUnion fun v _ ↦ finite_placesOver F v).subset fun w hw ↦
    Set.mem_biUnion (x := w.under E) (fun h ↦ hw (by simp [h]))
      (mem_placesOver.mpr (liesOver_under w))

end FinitePlace

/-! ### Twists -/

variable (K : Type*) [Field K] [NumberField K] (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- **A twist** of `Kⁿ` in the sense of Roy–Thunder, in the carrier of the Q2.0 decision: a
complex matrix for each complex embedding of `K`, conjugate embeddings carrying conjugate
matrices, and a matrix over `K` for each finite place, the identity at all but finitely many;
all of them invertible. -/
structure Twist where
  /-- The archimedean components, one for each complex embedding. -/
  arch : (K →+* ℂ) → Matrix ι ι ℂ
  arch_det_ne_zero : ∀ φ, (arch φ).det ≠ 0
  arch_conjugate : ∀ φ, arch (ComplexEmbedding.conjugate φ) = (arch φ).map (starRingEnd ℂ)
  /-- The nonarchimedean components, one for each finite place. -/
  fin : FinitePlace K → Matrix ι ι K
  fin_det_ne_zero : ∀ v, (fin v).det ≠ 0
  finite_setOf_fin_ne_one : {v | fin v ≠ 1}.Finite

namespace Twist

variable {K ι} (A : Twist K ι)
variable {E F : Type*} [Field E] [NumberField E] [Algebra K E]
  [Field F] [NumberField F] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

/-- The archimedean local factor at a complex embedding `φ` of `E`: the ℓ² norm of the point read
through `φ` and twisted by the component at the embedding of `K` below `φ`. -/
noncomputable def archFactor (φ : E →+* ℂ) (x : ι → E) : ℝ :=
  ‖(WithLp.toLp 2 (A.arch (φ.comp (algebraMap K E)) *ᵥ (φ ∘ x)) : EuclideanSpace ℂ ι)‖

/-- The nonarchimedean local factor at a finite place `w` of `E`: the max norm of the point
twisted by the component at the place of `K` below `w`. -/
noncomputable def finFactor (w : FinitePlace E) (x : ι → E) : ℝ :=
  ⨆ i, w ((((A.fin (w.under K)).map (algebraMap K E)) *ᵥ x) i)

/-- **The twisted height** of `x : ι → E`, relative to `E`: the product of the archimedean factors
over the complex embeddings of `E` and of the nonarchimedean factors over its finite places. -/
noncomputable def mulHeight (x : ι → E) : ℝ :=
  (∏ φ : E →+* ℂ, A.archFactor φ x) * ∏ᶠ w : FinitePlace E, A.finFactor w x

omit [NumberField E] in
theorem archFactor_nonneg (φ : E →+* ℂ) (x : ι → E) : 0 ≤ A.archFactor φ x := norm_nonneg _

theorem finFactor_nonneg (w : FinitePlace E) (x : ι → E) : 0 ≤ A.finFactor w x :=
  Real.iSup_nonneg fun _ ↦ apply_nonneg _ _

omit [NumberField E] in
@[simp] theorem archFactor_zero (φ : E →+* ℂ) : A.archFactor φ (0 : ι → E) = 0 := by
  have : (φ ∘ (0 : ι → E)) = 0 := funext fun _ ↦ map_zero φ
  rw [archFactor, this, Matrix.mulVec_zero]
  simp

/-! ### Reading a point over a larger field -/

omit [NumberField E] [NumberField F] in
theorem archFactor_algebraMap (φ : F →+* ℂ) (x : ι → E) :
    A.archFactor φ (algebraMap E F ∘ x) = A.archFactor (φ.comp (algebraMap E F)) x := by
  simp only [archFactor, IsScalarTower.algebraMap_eq K E F, ← RingHom.comp_assoc]
  rfl

private theorem iSup_pow {κ : Type*} [Finite κ] {a : κ → ℝ} (ha : ∀ i, 0 ≤ a i) {k : ℕ}
    (hk : 0 < k) : (⨆ i, a i) ^ k = ⨆ i, a i ^ k := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp [zero_pow hk.ne']
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := a)
  refine le_antisymm ?_ (ciSup_le fun j ↦ ?_)
  · rw [← hi]
    exact Finite.le_ciSup_of_le i le_rfl
  · exact pow_le_pow_left₀ (ha j) (Finite.le_ciSup_of_le j le_rfl) k

theorem finFactor_algebraMap (w : FinitePlace F) (x : ι → E) :
    A.finFactor w (algebraMap E F ∘ x) = A.finFactor (w.under E) x ^ w.localDegree E := by
  rw [finFactor, finFactor, iSup_pow (fun _ ↦ apply_nonneg _ _) (w.localDegree_pos (K := E)),
    ← FinitePlace.under_under (K := K) (E := E) w]
  refine iSup_congr fun i ↦ ?_
  have hmap : (A.fin ((w.under E).under K)).map (algebraMap K F) =
      ((A.fin ((w.under E).under K)).map (algebraMap K E)).map (algebraMap E F) := by
    rw [Matrix.map_map, IsScalarTower.algebraMap_eq K E F]
    rfl
  rw [hmap, ← RingHom.map_mulVec]
  exact FinitePlace.apply_algebraMap w (w.under E) _

/-! ### Finiteness of the nonarchimedean support -/

/-- At a finite place of `E` where the twist is trivial and every nonzero coordinate is a unit,
the nonarchimedean factor is `1`. -/
private theorem finFactor_eq_one {w : FinitePlace E} {x : ι → E} (hx : x ≠ 0)
    (hA : A.fin (w.under K) = 1) (hw : ∀ i, x i ≠ 0 → w (x i) = 1) : A.finFactor w x = 1 := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  have : Nonempty ι := ⟨i₀⟩
  rw [finFactor, hA, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  refine le_antisymm (ciSup_le fun i ↦ ?_) ?_
  · rcases eq_or_ne (x i) 0 with h | h
    · simp [h]
    · exact (hw i h).le
  · exact Finite.le_ciSup_of_le i₀ (hw i₀ hi₀).ge

theorem hasFiniteMulSupport_finFactor {x : ι → E} (hx : x ≠ 0) :
    (fun w : FinitePlace E ↦ A.finFactor w x).HasFiniteMulSupport := by
  classical
  have hbad : {w : FinitePlace E | A.fin (w.under K) ≠ 1}.Finite := by
    refine (A.finite_setOf_fin_ne_one.biUnion fun v _ ↦ FinitePlace.finite_placesOver E v).subset
      fun w hw ↦ Set.mem_biUnion hw ?_
    exact FinitePlace.mem_placesOver.mpr (FinitePlace.liesOver_under (K := K) w)
  have hcoord : ∀ i, x i ≠ 0 → (fun w : FinitePlace E ↦ w (x i)).HasFiniteMulSupport :=
    fun i h ↦ FinitePlace.hasFiniteMulSupport h
  refine (hbad.union (Set.finite_iUnion fun i : {i // x i ≠ 0} ↦ hcoord i i.2)).subset
    fun w hw ↦ ?_
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, mem_mulSupport, not_or, not_not,
    not_exists] at hcon
  exact hw (A.finFactor_eq_one hx hcon.1 fun i hi ↦ hcon.2 ⟨i, hi⟩)

/-- **The twisted height over `F` is the `[F : E]`-th power of the twisted height over `E`.** -/
theorem mulHeight_algebraMap (x : ι → E) :
    A.mulHeight (algebraMap E F ∘ x) = A.mulHeight x ^ finrank E F := by
  rcases eq_or_ne x 0 with rfl | hx
  · have hz : (algebraMap E F ∘ (0 : ι → E)) = 0 := funext fun _ ↦ by simp
    have hpos : 0 < finrank E F := finrank_pos
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    obtain ⟨ψ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [hz, mulHeight, mulHeight, Finset.prod_eq_zero (mem_univ φ) (A.archFactor_zero φ),
      Finset.prod_eq_zero (mem_univ ψ) (A.archFactor_zero ψ), zero_mul, zero_mul, zero_pow hpos.ne']
  rw [mulHeight, mulHeight, mul_pow]
  congr 1
  · simp_rw [archFactor_algebraMap]
    exact prod_comp_eq_prod_pow (fun ψ ↦ A.archFactor ψ x)
  · simp_rw [finFactor_algebraMap]
    exact FinitePlace.finprod_under_pow_localDegree _ (A.hasFiniteMulSupport_finFactor hx)

/-! ### Scaling and positivity -/

omit [NumberField E] in
theorem archFactor_smul (φ : E →+* ℂ) (c : E) (x : ι → E) :
    A.archFactor φ (c • x) = ‖φ c‖ * A.archFactor φ x := by
  have : (φ ∘ (c • x)) = φ c • (φ ∘ x) := funext fun i ↦ by simp
  rw [archFactor, archFactor, this, Matrix.mulVec_smul, WithLp.toLp_smul, norm_smul]

theorem finFactor_smul (w : FinitePlace E) (c : E) (x : ι → E) :
    A.finFactor w (c • x) = w c * A.finFactor w x := by
  rw [finFactor, finFactor, Matrix.mulVec_smul, Real.mul_iSup_of_nonneg (apply_nonneg _ _)]
  simp

/-- **The twisted height is invariant under scaling**, by the product formula. -/
theorem mulHeight_smul (x : ι → E) {c : E} (hc : c ≠ 0) : A.mulHeight (c • x) = A.mulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [smul_zero]
  have hprod := prod_abs_eq_one hc
  rw [← prod_embeddings_eq (fun w : InfinitePlace E ↦ w c)] at hprod
  simp only [InfinitePlace.apply] at hprod
  rw [mulHeight, mulHeight]
  simp_rw [archFactor_smul, finFactor_smul]
  rw [Finset.prod_mul_distrib,
    finprod_mul_distrib (FinitePlace.hasFiniteMulSupport hc) (A.hasFiniteMulSupport_finFactor hx)]
  calc (∏ φ : E →+* ℂ, ‖φ c‖) * (∏ φ, A.archFactor φ x) *
        ((∏ᶠ w : FinitePlace E, w c) * ∏ᶠ w, A.finFactor w x)
      = ((∏ φ : E →+* ℂ, ‖φ c‖) * ∏ᶠ w : FinitePlace E, w c) *
        ((∏ φ, A.archFactor φ x) * ∏ᶠ w, A.finFactor w x) := by ring
    _ = _ := by rw [hprod, one_mul]

omit [NumberField E] in
theorem archFactor_pos {x : ι → E} (hx : x ≠ 0) (φ : E →+* ℂ) : 0 < A.archFactor φ x := by
  refine norm_pos_iff.mpr fun h ↦ ?_
  have h' : A.arch (φ.comp (algebraMap K E)) *ᵥ (φ ∘ x) = 0 := by
    simpa using congrArg WithLp.ofLp h
  have := Matrix.eq_zero_of_mulVec_eq_zero (A.arch_det_ne_zero _) h'
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact hi (φ.injective (by simpa using congrFun this i))

theorem finFactor_pos {x : ι → E} (hx : x ≠ 0) (w : FinitePlace E) : 0 < A.finFactor w x := by
  have hdet : ((A.fin (w.under K)).map (algebraMap K E)).det ≠ 0 := by
    rw [show ((A.fin (w.under K)).map (algebraMap K E)).det = algebraMap K E (A.fin _).det from
      (RingHom.map_det _ _).symm]
    exact (map_ne_zero _).mpr (A.fin_det_ne_zero _)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp
    (fun h ↦ hx (Matrix.eq_zero_of_mulVec_eq_zero hdet h) :
      ((A.fin (w.under K)).map (algebraMap K E)) *ᵥ x ≠ 0)
  exact (FinitePlace.pos_iff.mpr hi).trans_le (Finite.le_ciSup_of_le i le_rfl)

/-- **The twisted height of a nonzero point is positive.** -/
theorem mulHeight_pos {x : ι → E} (hx : x ≠ 0) : 0 < A.mulHeight x := by
  refine mul_pos (Finset.prod_pos fun φ _ ↦ A.archFactor_pos hx φ) ?_
  rw [finprod_eq_prod_of_mulSupport_subset _
    (Set.Finite.coe_toFinset (A.hasFiniteMulSupport_finFactor hx)).symm.subset]
  exact Finset.prod_pos fun w _ ↦ A.finFactor_pos hx w

theorem mulHeight_nonneg (x : ι → E) : 0 ≤ A.mulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [mulHeight, Finset.prod_eq_zero (mem_univ φ) (A.archFactor_zero φ), zero_mul]
  · exact (A.mulHeight_pos hx).le

@[simp] theorem mulHeight_zero : A.mulHeight (0 : ι → E) = 0 := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  rw [mulHeight, Finset.prod_eq_zero (mem_univ φ) (A.archFactor_zero φ), zero_mul]

/-! ### Comparison of two twists

RT96 Prop. 4.1: any two twists give comparable heights. At every place the local factor of `A` is
at most that of `B` times the size of `A_v B_v⁻¹` — its ℓ² operator norm at an archimedean place,
the largest absolute value of an entry at a finite one — and the product of these sizes over `K`,
`compConst A B`, bounds `H_A` by `H_B`. With `B = 1` this is RT's `H_A ≤ c_A H_1`, with `A = 1` it
is `H_1 ≤ c_{A⁻¹} H_A`.
-/

variable (B : Twist K ι)

/-- The archimedean comparison factor at a complex embedding `φ` of `K`: the ℓ² operator norm of
`A_φ B_φ⁻¹`. -/
noncomputable def archConst (φ : K →+* ℂ) : ℝ :=
  ‖toEuclideanCLM (𝕜 := ℂ) (A.arch φ * (B.arch φ)⁻¹)‖

/-- The nonarchimedean comparison factor at a finite place `v` of `K`: the largest absolute value
of an entry of `A_v B_v⁻¹`. -/
noncomputable def finConst (v : FinitePlace K) : ℝ :=
  ⨆ p : ι × ι, v ((A.fin v * (B.fin v)⁻¹) p.1 p.2)

/-- **The comparison constant** of RT96 Prop. 4.1, relative to `K`: `H_A ≤ c ^ [E : K] · H_B`
over every finite extension `E` of `K`. -/
noncomputable def compConst : ℝ :=
  (∏ φ : K →+* ℂ, A.archConst B φ) * ∏ᶠ v : FinitePlace K, A.finConst B v

theorem archConst_nonneg (φ : K →+* ℂ) : 0 ≤ A.archConst B φ := norm_nonneg _

theorem finConst_nonneg (v : FinitePlace K) : 0 ≤ A.finConst B v :=
  Real.iSup_nonneg fun _ ↦ apply_nonneg _ _

theorem compConst_nonneg : 0 ≤ A.compConst B :=
  mul_nonneg (prod_nonneg fun φ _ ↦ A.archConst_nonneg B φ)
    (finprod_nonneg fun v ↦ A.finConst_nonneg B v)

theorem finConst_eq_one [Nonempty ι] {v : FinitePlace K} (hA : A.fin v = 1) (hB : B.fin v = 1) :
    A.finConst B v = 1 := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  rw [finConst, hA, hB, inv_one, mul_one]
  refine le_antisymm (ciSup_le fun p ↦ ?_) (Finite.le_ciSup_of_le (i, i) (by simp))
  rcases eq_or_ne p.1 p.2 with h | h <;> simp [Matrix.one_apply, h]

theorem hasFiniteMulSupport_finConst [Nonempty ι] : (A.finConst B).HasFiniteMulSupport :=
  (A.finite_setOf_fin_ne_one.union B.finite_setOf_fin_ne_one).subset fun v hv ↦ by
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    exact hv (A.finConst_eq_one B h.1 h.2)

private theorem det_mul_inv_ne_zero {R : Type*} [Field R] {M N : Matrix ι ι R} (hM : M.det ≠ 0)
    (hN : N.det ≠ 0) : (M * N⁻¹).det ≠ 0 := by
  rw [det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
  exact mul_ne_zero hM (inv_ne_zero hN)

theorem archConst_pos [Nonempty ι] (φ : K →+* ℂ) : 0 < A.archConst B φ := by
  refine norm_pos_iff.mpr fun h ↦ ?_
  have h0 : A.arch φ * (B.arch φ)⁻¹ = 0 :=
    toEuclideanCLM.injective (h.trans (map_zero _).symm)
  exact det_mul_inv_ne_zero (A.arch_det_ne_zero φ) (B.arch_det_ne_zero φ)
    (by rw [h0, det_zero])

theorem finConst_pos [Nonempty ι] (v : FinitePlace K) : 0 < A.finConst B v := by
  have hC : A.fin v * (B.fin v)⁻¹ ≠ 0 := fun h ↦
    det_mul_inv_ne_zero (A.fin_det_ne_zero v) (B.fin_det_ne_zero v) (by rw [h, det_zero])
  obtain ⟨i, j, hij⟩ : ∃ i j, (A.fin v * (B.fin v)⁻¹) i j ≠ 0 := by
    by_contra! h
    exact hC (Matrix.ext fun i j ↦ h i j)
  exact (FinitePlace.pos_iff.mpr hij).trans_le (Finite.le_ciSup_of_le (i, j) le_rfl)

theorem compConst_pos [Nonempty ι] : 0 < A.compConst B := by
  refine mul_pos (prod_pos fun φ _ ↦ A.archConst_pos B φ) ?_
  rw [finprod_eq_prod_of_mulSupport_subset _
    (Set.Finite.coe_toFinset (A.hasFiniteMulSupport_finConst B)).symm.subset]
  exact prod_pos fun v _ ↦ A.finConst_pos B v

omit [NumberField E] in
/-- The local comparison at a complex embedding. -/
theorem archFactor_le (φ : E →+* ℂ) (x : ι → E) :
    A.archFactor φ x ≤ A.archConst B (φ.comp (algebraMap K E)) * B.archFactor φ x := by
  have h : A.arch (φ.comp (algebraMap K E)) *ᵥ (φ ∘ x) =
      (A.arch (φ.comp (algebraMap K E)) * (B.arch (φ.comp (algebraMap K E)))⁻¹) *ᵥ
        (B.arch (φ.comp (algebraMap K E)) *ᵥ (φ ∘ x)) := by
    rw [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul_cancel_right _ _ (B.arch_det_ne_zero _).isUnit]
  rw [archFactor, archFactor, h]
  exact ContinuousLinearMap.le_opNorm
    (toEuclideanCLM (𝕜 := ℂ) (A.arch (φ.comp (algebraMap K E)) *
      (B.arch (φ.comp (algebraMap K E)))⁻¹))
    (WithLp.toLp 2 (B.arch (φ.comp (algebraMap K E)) *ᵥ (φ ∘ x)))

omit [DecidableEq ι] in
/-- The ultrametric bound for a matrix acting on a vector, at a finite place. -/
private theorem iSup_mulVec_le [Nonempty ι] (w : FinitePlace E) (M : Matrix ι ι E) (y : ι → E) :
    ⨆ i, w ((M *ᵥ y) i) ≤ (⨆ p : ι × ι, w (M p.1 p.2)) * ⨆ j, w (y j) := by
  refine ciSup_le fun i ↦ ?_
  have hna : IsNonarchimedean (w ·) := FinitePlace.add_le w
  obtain ⟨j, -, hj⟩ := hna.finset_image_add_of_nonempty (fun j ↦ M i j * y j)
    (univ_nonempty (α := ι))
  refine hj.trans ?_
  rw [map_mul]
  exact mul_le_mul (Finite.le_ciSup_of_le (i, j) le_rfl) (Finite.le_ciSup_of_le j le_rfl)
    (apply_nonneg _ _) (Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)

/-- The local comparison at a finite place. -/
theorem finFactor_le [Nonempty ι] (w : FinitePlace E) (x : ι → E) :
    A.finFactor w x ≤ A.finConst B (w.under K) ^ w.localDegree K * B.finFactor w x := by
  have hC : (A.fin (w.under K)).map (algebraMap K E) =
      (A.fin (w.under K) * (B.fin (w.under K))⁻¹).map (algebraMap K E) *
        (B.fin (w.under K)).map (algebraMap K E) := by
    rw [← Matrix.map_mul,
      Matrix.nonsing_inv_mul_cancel_right _ _ (B.fin_det_ne_zero _).isUnit]
  have hconst : A.finConst B (w.under K) ^ w.localDegree K = ⨆ p : ι × ι,
      w (((A.fin (w.under K) * (B.fin (w.under K))⁻¹).map (algebraMap K E)) p.1 p.2) := by
    rw [finConst, iSup_pow (fun _ ↦ apply_nonneg _ _) (w.localDegree_pos (K := K))]
    exact iSup_congr fun p ↦ (FinitePlace.apply_algebraMap w (w.under K) _).symm
  rw [finFactor, finFactor, hC, ← Matrix.mulVec_mulVec, hconst]
  exact iSup_mulVec_le w _ _

/-- Comparison of finite products of nonnegative real functions with finite support. -/
theorem finprod_le_finprod_of_nonneg {α : Type*} {f g : α → ℝ}
    (hf : f.HasFiniteMulSupport) (hg : g.HasFiniteMulSupport) (h0 : ∀ a, 0 ≤ f a)
    (h : ∀ a, f a ≤ g a) : ∏ᶠ a, f a ≤ ∏ᶠ a, g a := by
  classical
  rw [finprod_eq_prod_of_mulSupport_subset f (s := hf.toFinset ∪ hg.toFinset)
      fun a ha ↦ Finset.mem_union_left _ ((Set.Finite.mem_toFinset hf).mpr ha),
    finprod_eq_prod_of_mulSupport_subset g (s := hf.toFinset ∪ hg.toFinset)
      fun a ha ↦ Finset.mem_union_right _ ((Set.Finite.mem_toFinset hg).mpr ha)]
  exact Finset.prod_le_prod₀ (fun a _ ↦ h0 a) fun a _ ↦ h a

/-- **Comparison of twisted heights** (RT96 Prop. 4.1), relative to a finite extension `E` of
`K`: `H_A(x) ≤ c ^ [E : K] · H_B(x)` with `c = compConst A B`. -/
theorem mulHeight_le_compConst_pow_mul (x : ι → E) :
    A.mulHeight x ≤ A.compConst B ^ finrank K E * B.mulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [mulHeight_zero, mulHeight_zero, mul_zero]
  have : Nonempty ι := (Function.ne_iff.mp hx).nonempty
  have hc := A.hasFiniteMulSupport_finConst B
  have hs := FinitePlace.hasFiniteMulSupport_comp_under (F := E) hc (fun w ↦ w.localDegree K)
  calc A.mulHeight x
      ≤ (∏ φ : E →+* ℂ, A.archConst B (φ.comp (algebraMap K E)) * B.archFactor φ x) *
        ∏ᶠ w : FinitePlace E, A.finConst B (w.under K) ^ w.localDegree K * B.finFactor w x := by
        refine mul_le_mul (prod_le_prod₀ (fun φ _ ↦ A.archFactor_nonneg φ x)
          fun φ _ ↦ A.archFactor_le B φ x) ?_ (finprod_nonneg fun w ↦ A.finFactor_nonneg w x)
          (prod_nonneg fun φ _ ↦ mul_nonneg (A.archConst_nonneg B _) (B.archFactor_nonneg φ x))
        exact finprod_le_finprod_of_nonneg (A.hasFiniteMulSupport_finFactor hx)
          ((hs.union (B.hasFiniteMulSupport_finFactor hx)).subset (mulSupport_mul _ _))
          (fun w ↦ A.finFactor_nonneg w x)
          fun w ↦ A.finFactor_le B w x
    _ = A.compConst B ^ finrank K E * B.mulHeight x := by
        rw [prod_mul_distrib, finprod_mul_distrib hs (B.hasFiniteMulSupport_finFactor hx),
          prod_comp_eq_prod_pow (A.archConst B),
          FinitePlace.finprod_under_pow_localDegree _ hc, compConst, mul_pow, mulHeight]
        ring

/-! ### The trivial twist and the Arakelov height -/

/-- The trivial twist, all of whose components are the identity: its height is the untwisted
height `H_1` of RT96, the Arakelov height of `ArithmeticHeights`. -/
instance : One (Twist K ι) :=
  ⟨{ arch := fun _ ↦ 1
     arch_det_ne_zero := fun _ ↦ by simp
     arch_conjugate := fun _ ↦ by simp
     fin := fun _ ↦ 1
     fin_det_ne_zero := fun _ ↦ by simp
     finite_setOf_fin_ne_one := by simp }⟩

@[simp] theorem one_arch (φ : K →+* ℂ) : (1 : Twist K ι).arch φ = 1 := rfl

@[simp] theorem one_fin (v : FinitePlace K) : (1 : Twist K ι).fin v = 1 := rfl

omit [NumberField E] in
theorem one_archFactor (φ : E →+* ℂ) (x : ι → E) :
    (1 : Twist K ι).archFactor φ x = √(∑ i, ‖φ (x i)‖ ^ 2) := by
  simp [archFactor, EuclideanSpace.norm_eq]

theorem one_finFactor (w : FinitePlace E) (x : ι → E) :
    (1 : Twist K ι).finFactor w x = ⨆ i, w (x i) := by
  simp [finFactor]

/-- **The untwisted height is the Arakelov height**: at a nonzero point, the twisted height of the
trivial twist is `NumberField.arakelovMulHeight`. -/
theorem mulHeight_one_eq {x : ι → E} (hx : x ≠ 0) :
    (1 : Twist K ι).mulHeight x = arakelovMulHeight x := by
  rw [mulHeight, arakelovMulHeight_eq hx]
  congr 1
  · simp_rw [one_archFactor]
    have h := prod_embeddings_eq (K := E) fun v : InfinitePlace E ↦ √(∑ i, v (x i) ^ 2)
    simp only [InfinitePlace.apply] at h
    rw [h]
    refine prod_congr rfl fun v _ ↦ ?_
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  · simp_rw [one_finFactor]

/-- **Northcott's theorem for a twisted height**, over a fixed number field `E`: there are only
finitely many points of `ℙ(Eⁿ)` of bounded twisted height. -/
theorem finite_setOf_mulHeight_rep_le (b : ℝ) :
    {P : Projectivization E (ι → E) | A.mulHeight P.rep ≤ b}.Finite := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Set.finite_empty.subset fun P _ ↦ P.rep_nonzero (Subsingleton.elim _ _)
  refine (Projectivization.finite_setOfPred_mulHeight_le
    ((1 : Twist K ι).compConst A ^ finrank K E * b)).subset fun P hP ↦ ?_
  have h := (1 : Twist K ι).mulHeight_le_compConst_pow_mul A P.rep
  rw [mulHeight_one_eq P.rep_nonzero] at h
  have hmk := Projectivization.mulHeight_mk P.rep_nonzero
  rw [P.mk_rep] at hmk
  change Projectivization.mulHeight P ≤ _
  rw [hmk]
  exact (mulHeight_le_arakelovMulHeight _).trans (h.trans
    (mul_le_mul_of_nonneg_left hP (pow_nonneg ((1 : Twist K ι).compConst_nonneg A) _)))

/-! ### The absolute twisted height

For a field `Ω` algebraic over `K` — `AlgebraicClosure K`, or a number field containing `K` — the
twisted height of `x : ι → Ω` is computed over the field `K(x₀, x₁, …)` the coordinates generate,
and normalized by its degree over `ℚ`. By `mulHeight_algebraMap` any finite extension of `K`
inside `Ω` containing the coordinates gives the same value.
-/

section Absolute

open IntermediateField

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

omit [Fintype ι] [DecidableEq ι] in
/-- The field a tuple of `Ω` generates over `K` is a number field. -/
theorem numberField_adjoin_range [Finite ι] (x : ι → Ω) : NumberField (adjoin K (Set.range x)) :=
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have : FiniteDimensional K (adjoin K (Set.range x)) :=
    finiteDimensional_adjoin fun y _ ↦ (Algebra.IsAlgebraic.isAlgebraic (R := K) y).isIntegral
  { to_finiteDimensional := Module.Finite.trans K _ }

/-- **The absolute twisted height** of `x : ι → Ω`: the twisted height relative to
`K(x₀, x₁, …)`, taken to the power `1 / [K(x₀, x₁, …) : ℚ]`. -/
noncomputable def absMulHeight (x : ι → Ω) : ℝ :=
  haveI := numberField_adjoin_range (K := K) x
  A.mulHeight (fun i ↦ (⟨x i, subset_adjoin K _ ⟨i, rfl⟩⟩ : adjoin K (Set.range x))) ^
    ((finrank ℚ (adjoin K (Set.range x)) : ℝ))⁻¹

private theorem rpow_inv_natCast_mul {a : ℝ} (ha : 0 ≤ a) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    (a ^ n) ^ (((m * n : ℕ) : ℝ))⁻¹ = a ^ ((m : ℝ))⁻¹ := by
  rw [← Real.rpow_natCast a n, ← Real.rpow_mul ha]
  congr 1
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  push_cast
  field_simp

/-- **The absolute twisted height computed in a field of definition.** Any finite extension of
`K` inside `Ω` that contains the coordinates gives the same value. -/
theorem absMulHeight_eq_of_mem {E : IntermediateField K Ω} [NumberField E] {x : ι → Ω}
    (hx : ∀ i, x i ∈ E) :
    A.absMulHeight x = A.mulHeight (fun i ↦ (⟨x i, hx i⟩ : E)) ^ ((finrank ℚ E : ℝ))⁻¹ := by
  have hFE : adjoin K (Set.range x) ≤ E := adjoin_le_iff.mpr (by rintro _ ⟨i, rfl⟩; exact hx i)
  have := numberField_adjoin_range (K := K) x
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
    rpow_inv_natCast_mul (A.mulHeight_nonneg _)
      (Module.finrank_pos (R := ℚ) (M := adjoin K (Set.range x))).ne'
      (Module.finrank_pos (R := adjoin K (Set.range x)) (M := E)).ne']

/-- **The absolute twisted height of a point of `Kⁿ`** is its twisted height relative to `K`,
normalized by `[K : ℚ]`. -/
theorem absMulHeight_algebraMap (y : ι → K) :
    A.absMulHeight (algebraMap K Ω ∘ y) = A.mulHeight y ^ ((finrank ℚ K : ℝ))⁻¹ := by
  have := numberField_adjoin_range (K := K) (algebraMap K Ω ∘ y)
  have hx : ∀ i, (algebraMap K Ω ∘ y) i ∈ adjoin K (Set.range (algebraMap K Ω ∘ y)) :=
    fun i ↦ subset_adjoin K _ ⟨i, rfl⟩
  have : Module.Finite K (adjoin K (Set.range (algebraMap K Ω ∘ y))) :=
    Module.Finite.of_restrictScalars_finite ℚ _ _
  have hcomp : (fun i ↦ (⟨(algebraMap K Ω ∘ y) i, hx i⟩ :
      adjoin K (Set.range (algebraMap K Ω ∘ y)))) =
      algebraMap K (adjoin K (Set.range (algebraMap K Ω ∘ y))) ∘ y := rfl
  rw [A.absMulHeight_eq_of_mem hx, hcomp, mulHeight_algebraMap,
    ← Module.finrank_mul_finrank ℚ K (adjoin K (Set.range (algebraMap K Ω ∘ y))),
    rpow_inv_natCast_mul (A.mulHeight_nonneg _) (Module.finrank_pos (R := ℚ) (M := K)).ne'
      (Module.finrank_pos (R := K) (M := adjoin K (Set.range (algebraMap K Ω ∘ y)))).ne']

/-- The absolute twisted height of a nonzero point is positive. -/
theorem absMulHeight_pos {x : ι → Ω} (hx : x ≠ 0) : 0 < A.absMulHeight x := by
  have := numberField_adjoin_range (K := K) x
  refine Real.rpow_pos_of_pos (A.mulHeight_pos fun h ↦ hx (funext fun i ↦ ?_)) _
  simpa using congrArg Subtype.val (congrFun h i)

/-- **The absolute twisted height is invariant under scaling.** -/
theorem absMulHeight_smul (x : ι → Ω) {c : Ω} (hc : c ≠ 0) :
    A.absMulHeight (c • x) = A.absMulHeight x := by
  set E := adjoin K (insert c (Set.range x))
  have : NumberField E := by
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
    have : FiniteDimensional K E :=
      finiteDimensional_adjoin fun y _ ↦ (Algebra.IsAlgebraic.isAlgebraic (R := K) y).isIntegral
    exact { to_finiteDimensional := Module.Finite.trans K _ }
  have hcE : c ∈ E := subset_adjoin K _ (Set.mem_insert _ _)
  have hxE : ∀ i, x i ∈ E := fun i ↦ subset_adjoin K _ (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  have hcxE : ∀ i, (c • x) i ∈ E := fun i ↦ E.mul_mem hcE (hxE i)
  rw [A.absMulHeight_eq_of_mem hcxE, A.absMulHeight_eq_of_mem hxE]
  have : (fun i ↦ (⟨(c • x) i, hcxE i⟩ : E)) = (⟨c, hcE⟩ : E) • fun i ↦ ⟨x i, hxE i⟩ := rfl
  rw [this, A.mulHeight_smul _ fun h ↦ hc (congrArg Subtype.val h)]

/-- **Comparison of absolute twisted heights** (RT96 Prop. 4.1):
`H_A(x) ≤ c ^ {1 / [K : ℚ]} · H_B(x)` with `c = compConst A B`, for every point of `Ωⁿ`. -/
theorem absMulHeight_le_compConst_rpow_mul (B : Twist K ι) (x : ι → Ω) :
    A.absMulHeight x ≤ A.compConst B ^ ((finrank ℚ K : ℝ))⁻¹ * B.absMulHeight x := by
  have := numberField_adjoin_range (K := K) x
  have hx : ∀ i, x i ∈ adjoin K (Set.range x) := fun i ↦ subset_adjoin K _ ⟨i, rfl⟩
  have : Module.Finite K (adjoin K (Set.range x)) := Module.Finite.of_restrictScalars_finite ℚ _ _
  rw [A.absMulHeight_eq_of_mem hx, B.absMulHeight_eq_of_mem hx,
    ← Module.finrank_mul_finrank ℚ K (adjoin K (Set.range x)),
    ← rpow_inv_natCast_mul (A.compConst_nonneg B) (Module.finrank_pos (R := ℚ) (M := K)).ne'
      (Module.finrank_pos (R := K) (M := adjoin K (Set.range x))).ne',
    ← Real.mul_rpow (pow_nonneg (A.compConst_nonneg B) _) (B.mulHeight_nonneg _)]
  exact Real.rpow_le_rpow (A.mulHeight_nonneg _) (A.mulHeight_le_compConst_pow_mul B _)
    (by positivity)

/-- The untwisted absolute height of a nonzero point is at least `1`. -/
theorem one_le_absMulHeight_one {x : ι → Ω} (hx : x ≠ 0) : 1 ≤ (1 : Twist K ι).absMulHeight x := by
  have := numberField_adjoin_range (K := K) x
  have hxE : ∀ i, x i ∈ adjoin K (Set.range x) := fun i ↦ subset_adjoin K _ ⟨i, rfl⟩
  have hy : (fun i ↦ (⟨x i, hxE i⟩ : adjoin K (Set.range x))) ≠ 0 := fun h ↦
    hx (funext fun i ↦ by simpa using congrArg Subtype.val (congrFun h i))
  rw [absMulHeight_eq_of_mem _ hxE, mulHeight_one_eq hy]
  exact Real.one_le_rpow (one_le_arakelovMulHeight _) (by positivity)

/-- **A uniform lower bound for the absolute twisted height** (RT96 Prop. 4.1 with RT's `H_1 ≥ 1`):
`H_A(x) ≥ c ^ {-1 / [K : ℚ]}` at every nonzero point, with `c = compConst 1 A`. -/
theorem compConst_rpow_neg_le_absMulHeight {x : ι → Ω} (hx : x ≠ 0) :
    (1 : Twist K ι).compConst A ^ (-((finrank ℚ K : ℝ))⁻¹) ≤ A.absMulHeight x := by
  have : Nonempty ι := (Function.ne_iff.mp hx).nonempty
  have hc := Real.rpow_pos_of_pos ((1 : Twist K ι).compConst_pos A) ((finrank ℚ K : ℝ))⁻¹
  rw [Real.rpow_neg ((1 : Twist K ι).compConst_nonneg A), inv_le_iff_one_le_mul₀' hc]
  exact (one_le_absMulHeight_one hx).trans
    ((1 : Twist K ι).absMulHeight_le_compConst_rpow_mul A x)

theorem absMulHeight_nonneg (x : ι → Ω) : 0 ≤ A.absMulHeight x := by
  have := numberField_adjoin_range (K := K) x
  unfold absMulHeight
  exact Real.rpow_nonneg (mulHeight_nonneg _ _) _

/-! ### The absolute minima

RT96 Def. 6.1: `μ_i(A)` is the infimum of the `μ` for which there are `i` points with algebraic
coordinates, linearly independent over the algebraic closure of `K`, of twisted height at most `μ`.
Over the algebraic closure the infimum need not be attained —
Northcott's theorem needs a bound on the degree — so the minima are infima, and what replaces
attainment is `exists_linearIndependent_absMulHeight_lt`.
-/

variable (Ω) in
/-- The set whose infimum is the `i`-th absolute minimum: the `μ` for which there are `i` points of
`Ωⁿ`, linearly independent over `Ω`, of absolute twisted height at most `μ`. -/
def absMinimumSet (i : ℕ) : Set ℝ :=
  {μ | ∃ x : Fin i → ι → Ω, LinearIndependent Ω x ∧ ∀ j, A.absMulHeight (x j) ≤ μ}

variable (Ω) in
/-- **The `i`-th absolute minimum** of a twist (RT96 Def. 6.1), over `Ω`; for
`Ω = AlgebraicClosure K` this is RT's `μ_i(A)`. It is meaningful for `1 ≤ i ≤ n`: for `i = 0` the
set is all of `ℝ` and for `i > n` it is empty, and the value is the junk `0` in both cases. -/
noncomputable def absMinimum (i : ℕ) : ℝ :=
  sInf (A.absMinimumSet Ω i)

theorem mem_absMinimumSet {i : ℕ} {μ : ℝ} : μ ∈ A.absMinimumSet Ω i ↔
    ∃ x : Fin i → ι → Ω, LinearIndependent Ω x ∧ ∀ j, A.absMulHeight (x j) ≤ μ :=
  Iff.rfl

/-- Up to `i = n` there are `i` independent points: the standard basis vectors. -/
theorem absMinimumSet_nonempty {i : ℕ} (hi : i ≤ Fintype.card ι) :
    (A.absMinimumSet Ω i).Nonempty := by
  let e : Fin i ↪ ι := (Fin.castLEEmb hi).trans (Fintype.equivFin ι).symm.toEmbedding
  let x : Fin i → ι → Ω := Pi.basisFun Ω ι ∘ e
  exact ⟨∑ j, A.absMulHeight (x j), x, (Pi.basisFun Ω ι).linearIndependent.comp e e.injective,
    fun j ↦ single_le_sum (f := fun j ↦ A.absMulHeight (x j))
      (fun k _ ↦ A.absMulHeight_nonneg _) (mem_univ j)⟩

/-- Every height bound for `i ≥ 1` independent points is at least the lower bound of
`compConst_rpow_neg_le_absMulHeight`. -/
theorem compConst_rpow_neg_le_of_mem {i : ℕ} (hi : 0 < i) {μ : ℝ}
    (hμ : μ ∈ A.absMinimumSet Ω i) :
    (1 : Twist K ι).compConst A ^ (-((finrank ℚ K : ℝ))⁻¹) ≤ μ := by
  obtain ⟨x, hx, hμ⟩ := A.mem_absMinimumSet.mp hμ
  have h0 : x ⟨0, hi⟩ ≠ 0 := LinearIndependent.ne_zero ⟨0, hi⟩ hx
  exact (A.compConst_rpow_neg_le_absMulHeight h0).trans (hμ ⟨0, hi⟩)

theorem bddBelow_absMinimumSet {i : ℕ} (hi : 0 < i) : BddBelow (A.absMinimumSet Ω i) :=
  ⟨_, fun _ hμ ↦ A.compConst_rpow_neg_le_of_mem hi hμ⟩

/-- `i` independent points of height at most `μ` bound the `i`-th absolute minimum by `μ`. -/
theorem absMinimum_le {i : ℕ} (hi : 0 < i) {x : Fin i → ι → Ω} (hx : LinearIndependent Ω x)
    {μ : ℝ} (h : ∀ j, A.absMulHeight (x j) ≤ μ) : A.absMinimum Ω i ≤ μ :=
  csInf_le (A.bddBelow_absMinimumSet hi) ⟨x, hx, h⟩

/-- The first absolute minimum is at most the height of any nonzero point. -/
theorem absMinimum_one_le {x : ι → Ω} (hx : x ≠ 0) : A.absMinimum Ω 1 ≤ A.absMulHeight x :=
  A.absMinimum_le one_pos (x := fun _ ↦ x) (linearIndependent_unique_iff.mpr hx) fun _ ↦ le_rfl

/-- **Near-attainment of the absolute minima.** Above the `i`-th absolute minimum there are `i`
linearly independent points of smaller height. -/
theorem exists_linearIndependent_absMulHeight_lt {i : ℕ} (hi : i ≤ Fintype.card ι) {μ : ℝ}
    (hμ : A.absMinimum Ω i < μ) :
    ∃ x : Fin i → ι → Ω, LinearIndependent Ω x ∧ ∀ j, A.absMulHeight (x j) < μ := by
  obtain ⟨ν, ⟨x, hx, hν⟩, hνμ⟩ := exists_lt_of_csInf_lt (A.absMinimumSet_nonempty hi) hμ
  exact ⟨x, hx, fun j ↦ (hν j).trans_lt hνμ⟩

/-- **The absolute minima increase**: `μ_i(A) ≤ μ_j(A)` for `1 ≤ i ≤ j ≤ n`. -/
theorem absMinimum_le_absMinimum {i j : ℕ} (hi : 0 < i) (hij : i ≤ j)
    (hj : j ≤ Fintype.card ι) : A.absMinimum Ω i ≤ A.absMinimum Ω j := by
  refine csInf_le_csInf (A.bddBelow_absMinimumSet hi) (A.absMinimumSet_nonempty hj) ?_
  rintro μ ⟨x, hx, hμ⟩
  exact ⟨x ∘ Fin.castLE hij, hx.comp _ (Fin.castLE_injective hij), fun k ↦ hμ _⟩

/-- **A lower bound for the absolute minima**, uniform in `i`: `μ_i(A) ≥ c ^ {-1/[K:ℚ]}` with
`c = compConst 1 A`. -/
theorem compConst_rpow_neg_le_absMinimum {i : ℕ} (hi0 : 0 < i) (hi : i ≤ Fintype.card ι) :
    (1 : Twist K ι).compConst A ^ (-((finrank ℚ K : ℝ))⁻¹) ≤ A.absMinimum Ω i :=
  le_csInf (A.absMinimumSet_nonempty hi) fun _ hμ ↦ A.compConst_rpow_neg_le_of_mem hi0 hμ

/-- **The absolute minima are positive.** -/
theorem absMinimum_pos {i : ℕ} (hi0 : 0 < i) (hi : i ≤ Fintype.card ι) :
    0 < A.absMinimum Ω i :=
  have : Nonempty ι := Fintype.card_pos_iff.mp (hi0.trans_le hi)
  (Real.rpow_pos_of_pos ((1 : Twist K ι).compConst_pos A) _).trans_le
    (A.compConst_rpow_neg_le_absMinimum hi0 hi)

end Absolute

end Twist

end NumberField
