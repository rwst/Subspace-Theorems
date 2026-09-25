/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.SInteger
public import Mathlib.RingTheory.Norm.Defs

-- Used only inside proofs.
import DiophantineApproximation.SIntegerSquares
import DiophantineApproximation.UnitEquationSeveral
import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Norm-form equations

**Layer 8.6** (Schmidt 1971–1972; Bombieri–Gubler 7.4.4–7.4.6). For a finitely generated
`ℤ`-submodule `M` of a number field `K` and `c ∈ ℚ`, the solutions of `N_{K/ℚ}(μ) = c` in `M` lie
in a finite set or in finitely many sets `α F ⊆ ℚ M`, where `F` is a subfield with more than one
infinite place. So if the `ℚ`-span of `M` is **non-degenerate** — it contains no nonzero multiple
of a subfield other than `ℚ` and the imaginary quadratic fields — the equation has finitely many
solutions.

Route, by induction on the dimension of a subspace `V` of the span. Every solution has
`S`-unit conjugates in the normal closure `G` of `K`, for one finite `S`: a common denominator
`D` makes `D μ` integral, its cofactor `N(D μ) / (D μ)` is the product of the other conjugates,
and the two multiply to `D ^ d c`. Choose a maximal set `R` of embeddings `K → G` that are pairwise
non-proportional on `V`.

* If they are linearly dependent on `V`, a relation `∑ r, g r * r μ = 0` is a homogeneous unit
  equation, and Corollary 7.4.3 (Layer 8.2) gives `r μ = γ r₀ μ` with `r ≠ r₀` and `γ` in a finite
  set; each such equation cuts out a proper subspace of `V`.
* If they are independent, `#R ≤ dim V`. The ratios `v / w₀` generate a subfield `F` whose
  embeddings are the restrictions of those in `R`, and `V ⊆ w₀ F`; so
  `[F : ℚ] ≤ #R ≤ dim V ≤ [F : ℚ]` and `V = w₀ F`. If `F` has one infinite place, all conjugates
  of `μ / w₀` have the same absolute value, which the norm fixes, and there are finitely many
  solutions; otherwise `w₀ F` is one of the exceptional sets.

## Main results

* `NumberField.finite_setOf_norm_eq`: **Schmidt's theorem**, the non-degenerate case.
* `NumberField.exists_finite_forall_mem_or_div_mem`: the general case, up to the degenerate sets.
* `NumberField.isNondegenerate_of_finrank_lt`: in a field of prime degree every subspace of
  smaller dimension is non-degenerate.
* `NumberField.exists_finite_forall_exists_div_mem`: Corollary 7.4.3 for homogeneous equations.

## Implementation notes

⚠ **Non-degeneracy is stated with embeddings, not with a list of fields.** A subfield `F` has one
infinite place exactly when all embeddings of `K` into `ℂ` have the same absolute value on `F`, and
that is the property the proof uses; the fields with one infinite place are `ℚ` and the imaginary
quadratic fields.

⚠ **Everything happens inside `K`.** The book's induction on `[K : ℚ]` passes to the subfield `F`
and its own normal closure. Here the degenerate case is detected as `V = w₀ F` for a subfield of
`K`, the embeddings of `F` are counted as restrictions, and one normal closure serves every step.

⚠ **The families are not built.** The book describes the solutions in `α F` as finitely many orbits
of the units of norm `1` of an order of `F`, which needs orders of full modules and their unit
theorem. Here the degenerate part is only located: it lies in finitely many sets `α F`.

## References

W. M. Schmidt, *Diophantine Approximation*, Lecture Notes in Mathematics 785, Springer (1980),
Chapter VII; E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University
Press (2006), §7.4; J.-H. Evertse and K. Győry, *Unit Equations in Diophantine Number Theory*,
Cambridge University Press (2015), Chapter 9.

This is Layer 8.6 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset IsDedekindDomain Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- A `ℚ`-subspace `V` of `K` is **non-degenerate** when every subfield `F` with a nonzero
multiple `α F ⊆ V` has a single infinite place: all embeddings of `K` into `ℂ` have the same
absolute value on `F`. The fields with a single infinite place are `ℚ` and the imaginary quadratic
fields. -/
def IsNondegenerate (V : Submodule ℚ K) : Prop :=
  ∀ α : K, α ≠ 0 → ∀ F : IntermediateField ℚ K, (∀ x ∈ F, α * x ∈ V) →
    ∀ φ ψ : K →+* ℂ, ∀ x ∈ F, ‖φ x‖ = ‖ψ x‖

section Homogeneous

variable {G : Type*} [Field G] [NumberField G] {ι : Type*} [Fintype ι]

/-- **Corollary 7.4.3, homogeneous.** For `a : ι → G` with `a i₀ ≠ 0`, there is a finite set `Φ`
such that every `S`-unit solution of `∑ i, a i * y i = 0` has a ratio `y i / y i₀ ∈ Φ` with
`i ≠ i₀` and `a i ≠ 0`. -/
theorem exists_finite_forall_exists_div_mem (S : Finset (HeightOneSpectrum (𝓞 G))) (a : ι → G)
    {i₀ : ι} (hi₀ : a i₀ ≠ 0) :
    ∃ Φ : Set G, Φ.Finite ∧ ∀ y : ι → Gˣ,
      (∀ i, y i ∈ (S : Set (HeightOneSpectrum (𝓞 G))).unit G) → ∑ i, a i * y i = 0 →
      ∃ i ≠ i₀, a i ≠ 0 ∧ (y i : G) / y i₀ ∈ Φ := by
  classical
  let J := {i // i ≠ i₀ ∧ a i ≠ 0}
  let b : J → Gˣ := fun j ↦ Units.mk0 (-a j / a i₀) (div_ne_zero (neg_ne_zero.mpr j.2.2) hi₀)
  obtain ⟨Φ, hΦ, h⟩ := exists_finite_forall_exists_mul_mem S b
  refine ⟨(fun p : J × G ↦ p.2 / b p.1) '' (Set.univ ×ˢ Φ), (Set.finite_univ.prod hΦ).image _,
    fun y hy hsum ↦ ?_⟩
  have hJ : ∑ j : J, a j * y j = -(a i₀ * y i₀) := by
    have hs : ∑ i ∈ (univ.erase i₀).filter (a · ≠ 0), a i * y i = ∑ j : J, a j * y j :=
      Finset.sum_subtype _ (fun i ↦ by simp [and_comm]) _
    rw [← hs, Finset.sum_filter_of_ne fun i _ h ↦ left_ne_zero_of_mul h,
      Finset.sum_erase_eq_sub (mem_univ _), hsum, zero_sub]
  have h0 : a i₀ * y i₀ ≠ 0 := mul_ne_zero hi₀ (y i₀).ne_zero
  have h1 : ∑ j, (b j : G) * ↑(y j / y i₀) = 1 :=
    calc ∑ j, (b j : G) * ↑(y j / y i₀) = (∑ j : J, a j * y j) * (-1 / (a i₀ * y i₀)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          simp only [b, Units.val_mk0, Units.val_div_eq_div_val]
          field_simp
      _ = 1 := by rw [hJ]; field_simp
  obtain ⟨j, hj⟩ := h (fun j ↦ y j / y i₀) (fun j ↦ div_mem (hy j) (hy i₀)) h1
  refine ⟨j, j.2.1, j.2.2, (j, _), ⟨trivial, hj⟩, ?_⟩
  simp only [Units.val_div_eq_div_val]
  rw [mul_div_cancel_left₀ _ (b j).ne_zero]

end Homogeneous

/-- The image of a finitely generated subgroup is finitely generated. -/
private theorem fg_map {A B : Type*} [Group A] [Group B] {Γ : Subgroup A} (hΓ : Γ.FG)
    (f : A →* B) : (Γ.map f).FG := by
  obtain ⟨s, rfl, hs⟩ := (Subgroup.fg_iff _).mp hΓ
  exact (Subgroup.fg_iff _).mpr ⟨f '' s, (MonoidHom.map_closure f s).symm, hs.image f⟩

/-- **A finitely generated `ℤ`-submodule of `K` has a common denominator.** -/
theorem exists_forall_isIntegral_mul {M : Submodule ℤ K} (hM : M.FG) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ μ ∈ M, IsIntegral ℤ ((D : K) * μ) := by
  classical
  obtain ⟨s, rfl⟩ := hM
  obtain ⟨D, hD, h⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨D, hD, fun μ hμ ↦ ?_⟩
  induction hμ using Submodule.span_induction with
  | mem x hx => simpa [zsmul_eq_mul] using h x hx
  | zero => simpa using isIntegral_zero
  | add x y _ _ hx hy => simpa [mul_add] using hx.add hy
  | smul n x _ hx =>
    rw [zsmul_eq_mul, mul_left_comm]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := n)).mul hx

/-- **An algebraic integer is an `S`-integer** for every `S`. -/
theorem mem_integer_of_isIntegral {S : Set (HeightOneSpectrum (𝓞 K))} {x : K}
    (hx : IsIntegral ℤ x) : x ∈ S.integer K :=
  mem_integer_of_subset (Set.empty_subset S) (Set.mem_integer_empty_iff.mpr ⟨⟨x, hx⟩, rfl⟩)

/-- **The cofactor `N(x) / x` of an algebraic integer is an algebraic integer**: it is the
product of the other conjugates of `x`. -/
theorem isIntegral_norm_div {x : K} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (algebraMap ℚ K (Algebra.norm ℚ x) / x) := by
  classical
  rcases eq_or_ne x 0 with rfl | hx0
  · simpa using isIntegral_zero
  let σ₀ : K →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  refine (isIntegral_algHom_iff ((σ₀ : K →+* AlgebraicClosure ℚ).toIntAlgHom)
    σ₀.injective).mp ?_
  have h := Algebra.norm_eq_prod_embeddings ℚ (AlgebraicClosure ℚ) x
  rw [← Finset.mul_prod_erase _ _ (mem_univ σ₀)] at h
  change IsIntegral ℤ (σ₀ (algebraMap ℚ K (Algebra.norm ℚ x) / x))
  rw [map_div₀, AlgHom.commutes, h, mul_div_cancel_left₀ _ ((map_ne_zero σ₀).mpr hx0)]
  exact IsIntegral.prod _ fun σ _ ↦ hx.map ((σ : K →+* AlgebraicClosure ℚ).toIntAlgHom)

/-- **Solutions of a norm equation with a common denominator are `S`-units** for one finite `S`:
if `D μ` is integral and `N(μ) = c ≠ 0`, then `D μ` and its cofactor `N(D μ) / (D μ)` are
integral with product `D ^ d c`. -/
theorem exists_finset_forall_mem_unit {D : ℤ} (hD : D ≠ 0) {T : Set K}
    (hT : ∀ μ ∈ T, IsIntegral ℤ ((D : K) * μ)) {c : ℚ} (hc : c ≠ 0)
    (hTc : ∀ μ ∈ T, Algebra.norm ℚ μ = c) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      ∀ μ ∈ T, ∃ u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, (u : K) = μ := by
  classical
  have hD' : (D : K) ≠ 0 := Int.cast_ne_zero.mpr hD
  set w : K := (D : K) ^ finrank ℚ K * algebraMap ℚ K c with hw_def
  have hw : w ≠ 0 := mul_ne_zero (pow_ne_zero _ hD') ((map_ne_zero _).mpr hc)
  obtain ⟨S₁, hS₁⟩ := exists_finset_mem_unit (Units.mk0 w hw)
  obtain ⟨S₂, hS₂⟩ := exists_finset_mem_unit (Units.mk0 _ hD')
  refine ⟨S₁ ∪ S₂, fun μ hμ ↦ ?_⟩
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hc ((hTc 0 hμ).symm.trans (Algebra.norm_zero))
  have hnorm : algebraMap ℚ K (Algebra.norm ℚ ((D : K) * μ)) = w := by
    rw [← map_intCast (algebraMap ℚ K) D, map_mul, Algebra.norm_algebraMap, hTc μ hμ, map_mul,
      map_pow, map_intCast]
  obtain ⟨u, hu, hu'⟩ := exists_mem_unit_of_mul_eq
    (S := ((S₁ ∪ S₂ : Finset (HeightOneSpectrum (𝓞 K))) : Set (HeightOneSpectrum (𝓞 K))))
    (mem_integer_of_isIntegral (hT μ hμ)) (mem_integer_of_isIntegral (isIntegral_norm_div
      (hT μ hμ))) (w := Units.mk0 w hw)
    (mem_unit_of_subset (by rw [Finset.coe_union]; exact Set.subset_union_left) hS₁)
    (by rw [hnorm, Units.val_mk0, mul_div_cancel₀ _ (mul_ne_zero hD' hμ0)])
  refine ⟨u * (Units.mk0 _ hD')⁻¹, mul_mem hu (inv_mem (mem_unit_of_subset
    (by rw [Finset.coe_union]; exact Set.subset_union_right) hS₂)), ?_⟩
  rw [Units.val_mul, hu', Units.val_inv_eq_inv_val, Units.val_mk0, mul_comm, ← mul_assoc,
    inv_mul_cancel₀ hD', one_mul]

/-- **A norm equation over a field with one infinite place.** If all embeddings of `K` into `ℂ`
have the same absolute value on the subfield `F`, then finitely many `μ` with `D μ` integral,
`μ / w₀ ∈ F` and `N(μ) = c`: the absolute values of `μ / w₀` are all equal, so their common
value is fixed by the norm, and `μ` has bounded conjugates. -/
theorem finite_setOf_norm_eq_of_forall_norm_eq {F : IntermediateField ℚ K}
    (hF : ∀ φ ψ : K →+* ℂ, ∀ x ∈ F, ‖φ x‖ = ‖ψ x‖) {w₀ : K} (hw₀ : w₀ ≠ 0) {D : ℤ}
    (hD : D ≠ 0) (c : ℚ) :
    {μ : K | IsIntegral ℤ ((D : K) * μ) ∧ μ / w₀ ∈ F ∧ Algebra.norm ℚ μ = c}.Finite := by
  classical
  set P : ℝ := ∏ σ : K →ₐ[ℚ] ℂ, ‖σ w₀‖
  have hP : 0 < P := Finset.prod_pos fun σ _ ↦ norm_pos_iff.mpr ((map_ne_zero σ).mpr hw₀)
  set B : ℝ := (∑ σ : K →ₐ[ℚ] ℂ, ‖σ w₀‖) * max 1 (|(c : ℝ)| / P)
  have hbound : ∀ μ : K, μ / w₀ ∈ F → Algebra.norm ℚ μ = c → ∀ φ : K →+* ℂ, ‖φ μ‖ ≤ B := by
    intro μ hμ hc φ
    set t := ‖φ (μ / w₀)‖
    have hμw : w₀ * (μ / w₀) = μ := by field_simp
    have ht : ∀ σ : K →ₐ[ℚ] ℂ, ‖σ μ‖ = ‖σ w₀‖ * t := fun σ ↦ by
      have := hF (σ : K →+* ℂ) φ _ hμ
      rw [AlgHom.coe_toRingHom] at this
      rw [← hμw, map_mul, norm_mul, this]
    have hnorm : |(c : ℝ)| = P * t ^ finrank ℚ K := by
      have h := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ μ)
      rw [norm_prod, Finset.prod_congr rfl fun σ _ ↦ ht σ, Finset.prod_mul_distrib,
        Finset.prod_const, card_univ, AlgHom.card, hc] at h
      simpa using h
    have ht_le : t ≤ max 1 (|(c : ℝ)| / P) := by
      rcases le_or_gt t 1 with h | h
      · exact le_max_of_le_left h
      · refine le_max_of_le_right ?_
        rw [le_div_iff₀ hP, hnorm, mul_comm]
        exact mul_le_mul_of_nonneg_left (le_self_pow₀ h.le finrank_pos.ne') hP.le
    calc ‖φ μ‖ = ‖φ.toRatAlgHom w₀‖ * t := ht φ.toRatAlgHom
      _ ≤ B := mul_le_mul (single_le_sum (f := fun σ : K →ₐ[ℚ] ℂ ↦ ‖σ w₀‖)
          (fun σ _ ↦ norm_nonneg _) (mem_univ φ.toRatAlgHom)) ht_le
          (norm_nonneg _) (sum_nonneg fun σ _ ↦ norm_nonneg _)
  have hD' : (D : K) ≠ 0 := Int.cast_ne_zero.mpr hD
  refine (Set.Finite.preimage (mul_right_injective₀ hD').injOn
    (Embeddings.finite_of_norm_le K ℂ (|(D : ℝ)| * B))).subset ?_
  rintro μ ⟨hi, hμ, hc⟩
  refine ⟨hi, fun φ ↦ ?_⟩
  rw [map_mul, norm_mul, map_intCast, Complex.norm_intCast]
  exact mul_le_mul_of_nonneg_left (hbound μ hμ hc φ) (abs_nonneg _)

section Core

variable {G : Type*} [Field G] [Algebra ℚ G]

/-- Two embeddings are **proportional on `V`** when one is a constant multiple of the other
there. -/
def IsProportional (V : Submodule ℚ K) (i j : K →ₐ[ℚ] G) : Prop :=
  ∃ γ : G, ∀ v ∈ V, i v = γ * j v

/-- **A maximal set of pairwise non-proportional embeddings.** -/
theorem exists_finset_pairwise_not_isProportional (V : Submodule ℚ K) :
    ∃ R : Finset (K →ₐ[ℚ] G), (∀ i ∈ R, ∀ j ∈ R, i ≠ j → ¬ IsProportional V i j) ∧
      ∀ i, ∃ j ∈ R, IsProportional V i j ∨ IsProportional V j i := by
  classical
  obtain ⟨R, hR, hmax⟩ := (univ.powerset.filter fun R : Finset (K →ₐ[ℚ] G) ↦
    ∀ i ∈ R, ∀ j ∈ R, i ≠ j → ¬ IsProportional V i j).exists_max_image card ⟨∅, by simp⟩
  simp only [mem_filter, mem_powerset, subset_univ, true_and] at hR hmax
  refine ⟨R, hR, fun i ↦ ?_⟩
  by_cases hi : i ∈ R
  · exact ⟨i, hi, Or.inl ⟨1, fun v _ ↦ (one_mul _).symm⟩⟩
  by_contra h
  push Not at h
  have := hmax (insert i R) fun a ha b hb hab ↦ by
    rw [mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact (h b hb).1
    · exact (h a ha).2
    · exact hR a ha b hb hab
  rw [card_insert_of_notMem hi] at this
  omega

variable (hG : ∀ x : K, ((minpoly ℚ x).map (algebraMap ℚ G)).Splits)
include hG

/-- **The leaf.** If a maximal set `R` of pairwise non-proportional embeddings has at most
`dim V` elements, then `V` is a multiple `w₀ F` of a subfield: `F` is generated by the ratios
`v / w₀`, its embeddings are the restrictions of those in `R`, and so
`[F : ℚ] ≤ #R ≤ dim V ≤ [F : ℚ]`. -/
theorem exists_eq_mul_intermediateField {V : Submodule ℚ K} (hV : V ≠ ⊥)
    {R : Finset (K →ₐ[ℚ] G)} (hmax : ∀ i, ∃ j ∈ R, IsProportional V i j ∨ IsProportional V j i)
    (hR : R.card ≤ finrank ℚ V) :
    ∃ w₀ : K, w₀ ≠ 0 ∧ ∃ F : IntermediateField ℚ K, (∀ x ∈ F, w₀ * x ∈ V) ∧
      ∀ μ ∈ V, μ / w₀ ∈ F := by
  classical
  obtain ⟨w₀, hw₀V, hw₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
  set F := IntermediateField.adjoin ℚ ((· / w₀) '' (V : Set K))
  have hsub : ∀ μ ∈ V, μ / w₀ ∈ F := fun μ hμ ↦ IntermediateField.subset_adjoin _ _ ⟨μ, hμ, rfl⟩
  refine ⟨w₀, hw₀, F, ?_, hsub⟩
  have hres : ∀ i j : K →ₐ[ℚ] G, IsProportional V i j → i.comp F.val = j.comp F.val := by
    rintro i j ⟨γ, hγ⟩
    apply IntermediateField.adjoin_algHom_ext
    rintro _ ⟨v, hv, rfl⟩
    have hγ0 : γ ≠ 0 := by
      rintro rfl
      exact (map_ne_zero i).mpr hw₀ (by rw [hγ w₀ hw₀V, zero_mul])
    simp only [AlgHom.comp_apply, IntermediateField.val_mk, map_div₀, hγ v hv, hγ w₀ hw₀V]
    exact mul_div_mul_left _ _ hγ0
  have hcard : finrank ℚ F ≤ R.card := by
    rw [← AlgHom.card_of_splits ℚ F G fun x ↦ by rw [IntermediateField.minpoly_eq]; exact hG x]
    refine (Fintype.card_le_of_surjective (fun r : R ↦ (r : K →ₐ[ℚ] G).comp F.val)
      fun φ ↦ ?_).trans (Fintype.card_coe R).le
    obtain ⟨σ, hσ⟩ := IntermediateField.exists_algHom_of_splits
      (fun s : K ↦ ⟨Algebra.IsIntegral.isIntegral s, hG s⟩) φ
    obtain ⟨r, hr, h⟩ := hmax σ
    refine ⟨⟨r, hr⟩, ?_⟩
    rcases h with h | h
    · exact (hres σ r h).symm.trans hσ
    · exact (hres r σ h).trans hσ
  set f : K →ₗ[ℚ] K := LinearMap.mulLeft ℚ w₀⁻¹
  have hf : Function.Injective f := mul_right_injective₀ (inv_ne_zero hw₀)
  have hle : V.map f ≤ Subalgebra.toSubmodule F.toSubalgebra := by
    rintro _ ⟨v, hv, rfl⟩
    change w₀⁻¹ * v ∈ F
    rw [inv_mul_eq_div]
    exact hsub v hv
  have heq := Submodule.eq_of_le_of_finrank_le hle (by
    rw [Subalgebra.finrank_toSubmodule, IntermediateField.finrank_eq_finrank_subalgebra,
      ← (Submodule.equivMapOfInjective f hf V).finrank_eq]
    exact hcard.trans hR)
  intro x hx
  obtain ⟨v, hv, hvx⟩ := (heq.symm ▸ hx : x ∈ V.map f)
  rw [← hvx]
  change w₀ * (w₀⁻¹ * v) ∈ V
  rwa [mul_inv_cancel_left₀ hw₀]

omit hG in
/-- **The step.** If a set `R` of pairwise non-proportional embeddings is linearly dependent on
`V`, the solutions in `V` lie in finitely many proper subspaces: a relation
`∑ r, g r * r μ = 0` among `S`-units gives, by Corollary 7.4.3, `r μ = γ r₀ μ` with `r ≠ r₀` and
`γ` in a finite set, and each of these equations cuts `V` properly. -/
theorem exists_finite_forall_exists_mem_lt [NumberField G]
    (S : Finset (HeightOneSpectrum (𝓞 G))) {T : Set K}
    (hT : ∀ μ ∈ T, ∀ i : K →ₐ[ℚ] G,
      ∃ u ∈ (S : Set (HeightOneSpectrum (𝓞 G))).unit G, (u : G) = i μ)
    {V : Submodule ℚ K} {R : Finset (K →ₐ[ℚ] G)}
    (hR : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → ¬ IsProportional V i j)
    (hdep : ¬ LinearIndependent G fun r : R ↦ fun k ↦ (r : K →ₐ[ℚ] G) (finBasis ℚ V k)) :
    ∃ 𝒲 : Set (Submodule ℚ K), 𝒲.Finite ∧ (∀ W ∈ 𝒲, W < V) ∧
      ∀ μ ∈ T, μ ∈ V → ∃ W ∈ 𝒲, μ ∈ W := by
  classical
  set b := finBasis ℚ V
  obtain ⟨g, hg, r₀, hr₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hk : ∀ k, ∑ r : R, g r * (r : K →ₐ[ℚ] G) (b k) = 0 := fun k ↦ by
    simpa using congrFun hg k
  have hrel : ∀ v ∈ V, ∑ r : R, g r * (r : K →ₐ[ℚ] G) v = 0 := by
    intro v hv
    have hv' : v = ∑ k, b.repr ⟨v, hv⟩ k • (b k : K) := by
      have := congrArg ((↑) : V → K) (b.sum_repr ⟨v, hv⟩)
      rw [Submodule.coe_sum] at this
      exact this.symm
    rw [hv']
    have hsmul : ∀ (i : K →ₐ[ℚ] G) (q : ℚ) (y : K), i (q • y) = algebraMap ℚ G q * i y :=
      fun i q y ↦ by rw [Algebra.smul_def, map_mul, AlgHom.commutes]
    simp_rw [map_sum]
    rw [Finset.sum_congr rfl fun r _ ↦ by rw [Finset.sum_congr rfl fun k _ ↦ hsmul _ _ _]]
    simp_rw [Finset.mul_sum, mul_left_comm (g _)]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hk, mul_zero, Finset.sum_const_zero]
  obtain ⟨Φ, hΦ, hΦ'⟩ := exists_finite_forall_exists_div_mem S g hr₀
  let W : R → G → Submodule ℚ K := fun r γ ↦ V ⊓ LinearMap.eqLocus
    (r : K →ₐ[ℚ] G).toLinearMap ((LinearMap.mulLeft ℚ γ).comp (r₀ : K →ₐ[ℚ] G).toLinearMap)
  refine ⟨(fun p : R × G ↦ W p.1 p.2) '' {p | p.1 ≠ r₀ ∧ p.2 ∈ Φ},
    ((Set.finite_univ.prod hΦ).subset fun p hp ↦ ⟨trivial, hp.2⟩).image _, ?_, ?_⟩
  · rintro _ ⟨⟨r, γ⟩, ⟨hr, -⟩, rfl⟩
    refine lt_of_le_of_ne inf_le_left fun h ↦
      hR r r.2 r₀ r₀.2 (Subtype.coe_injective.ne hr) ⟨γ, fun v hv ↦ ?_⟩
    have h' : W r γ = V := h
    have : v ∈ W r γ := h'.symm ▸ hv
    exact this.2
  · intro μ hμ hμV
    choose y hy hyμ using hT μ hμ
    obtain ⟨r, hr, -, hmem⟩ := hΦ' (fun r ↦ y r) (fun r ↦ hy r) (by
      simpa [hyμ] using hrel μ hμV)
    refine ⟨W r (y r / y r₀), ⟨(r, _), ⟨hr, hmem⟩, rfl⟩, hμV, ?_⟩
    change (r : K →ₐ[ℚ] G) μ = (y r : G) / y r₀ * (r₀ : K →ₐ[ℚ] G) μ
    rw [← hyμ r, ← hyμ r₀, div_mul_cancel₀ _ (y r₀).ne_zero]

/-- **The induction on the dimension.** For a set `T` of solutions of `N(μ) = c` with a common
denominator `D` whose conjugates are `S`-units of `G`, and every subspace `V ≤ V₀` of dimension
at most `n`: the solutions in `V` lie in a finite set or in finitely many sets `α F ⊆ V₀`, with
`F` a subfield with more than one infinite place. -/
theorem exists_finite_forall_mem_or_of_splits [NumberField G]
    (S : Finset (HeightOneSpectrum (𝓞 G))) {V₀ : Submodule ℚ K} {T : Set K} {D : ℤ}
    (hD : D ≠ 0) {c : ℚ}
    (hTc : ∀ μ ∈ T, IsIntegral ℤ ((D : K) * μ) ∧ Algebra.norm ℚ μ = c)
    (hT : ∀ μ ∈ T, ∀ i : K →ₐ[ℚ] G,
      ∃ u ∈ (S : Set (HeightOneSpectrum (𝓞 G))).unit G, (u : G) = i μ) (n : ℕ) :
    ∀ V ≤ V₀, finrank ℚ V ≤ n → ∃ Φ : Set K, Φ.Finite ∧
      ∃ P : Set (K × IntermediateField ℚ K), P.Finite ∧
      (∀ p ∈ P, p.1 ≠ 0 ∧ (∀ x ∈ p.2, p.1 * x ∈ V₀) ∧
        ∃ φ ψ : K →+* ℂ, ∃ x ∈ p.2, ‖φ x‖ ≠ ‖ψ x‖) ∧
      ∀ μ ∈ T, μ ∈ V → μ ∈ Φ ∨ ∃ p ∈ P, μ / p.1 ∈ p.2 := by
  classical
  induction n with
  | zero =>
    intro V _ hV
    rw [Nat.le_zero, Submodule.finrank_eq_zero] at hV
    refine ⟨{0}, Set.finite_singleton 0, ∅, Set.finite_empty, by simp, fun μ _ hμ ↦ Or.inl ?_⟩
    rw [hV, Submodule.mem_bot] at hμ
    exact hμ
  | succ n ih =>
    intro V hV₀ hn
    by_cases hbot : V = ⊥
    · refine ⟨{0}, Set.finite_singleton 0, ∅, Set.finite_empty, by simp, fun μ _ hμ ↦ Or.inl ?_⟩
      rw [hbot, Submodule.mem_bot] at hμ
      exact hμ
    obtain ⟨R, hR, hmax⟩ := exists_finset_pairwise_not_isProportional (G := G) V
    by_cases hli : LinearIndependent G fun r : R ↦ fun k ↦ (r : K →ₐ[ℚ] G) (finBasis ℚ V k)
    · have hcard : R.card ≤ finrank ℚ V := by
        simpa using hli.fintype_card_le_finrank
      obtain ⟨w₀, hw₀, F, hFV, hVF⟩ := exists_eq_mul_intermediateField hG hbot hmax hcard
      by_cases hF : ∀ φ ψ : K →+* ℂ, ∀ x ∈ F, ‖φ x‖ = ‖ψ x‖
      · exact ⟨_, finite_setOf_norm_eq_of_forall_norm_eq hF hw₀ hD c, ∅, Set.finite_empty,
          by simp, fun μ hμ hμV ↦ Or.inl ⟨(hTc μ hμ).1, hVF μ hμV, (hTc μ hμ).2⟩⟩
      · push Not at hF
        exact ⟨∅, Set.finite_empty, {(w₀, F)}, Set.finite_singleton _,
          fun p hp ↦ by
            rw [Set.mem_singleton_iff] at hp
            subst hp
            exact ⟨hw₀, fun x hx ↦ hV₀ (hFV x hx), hF⟩,
          fun μ _ hμV ↦ Or.inr ⟨_, rfl, hVF μ hμV⟩⟩
    · obtain ⟨𝒲, h𝒲, hlt, hcover⟩ := exists_finite_forall_exists_mem_lt S hT hR hli
      have h𝒲' : ∀ W ∈ 𝒲, W ≤ V₀ ∧ finrank ℚ W ≤ n := fun W hW ↦
        ⟨(hlt W hW).le.trans hV₀,
          Nat.lt_succ_iff.mp ((Submodule.finrank_lt_finrank_of_lt (hlt W hW)).trans_le hn)⟩
      choose Φ hΦ P hP hPp hPc using fun W (hW : W ∈ 𝒲) ↦ ih W (h𝒲' W hW).1 (h𝒲' W hW).2
      refine ⟨⋃ W ∈ 𝒲, Φ W ‹_›, h𝒲.biUnion' hΦ, ⋃ W ∈ 𝒲, P W ‹_›, h𝒲.biUnion' hP, ?_, ?_⟩
      · intro p hp
        simp only [Set.mem_iUnion] at hp
        obtain ⟨W, hW, hp⟩ := hp
        exact hPp W hW p hp
      · intro μ hμ hμV
        obtain ⟨W, hW, hμW⟩ := hcover μ hμ hμV
        rcases hPc W hW μ hμ hμW with h | ⟨p, hp, h⟩
        · exact Or.inl (Set.mem_iUnion₂.mpr ⟨W, hW, h⟩)
        · exact Or.inr ⟨p, Set.mem_iUnion₂.mpr ⟨W, hW, hp⟩, h⟩

end Core

/-- **Schmidt's theorem on norm-form equations, the structure.** For a finitely generated
`ℤ`-submodule `M` of `K` and `c ∈ ℚ`, the solutions of `N_{K/ℚ}(μ) = c` in `M` lie in a finite set
or in finitely many sets `α F`, where `F` is a subfield with more than one infinite place — not
`ℚ` and not imaginary quadratic — and `α F` lies in the `ℚ`-span of `M`. -/
theorem exists_finite_forall_mem_or_div_mem (M : Submodule ℤ K) (hM : M.FG) (c : ℚ) :
    ∃ Φ : Set K, Φ.Finite ∧ ∃ P : Set (K × IntermediateField ℚ K), P.Finite ∧
      (∀ p ∈ P, p.1 ≠ 0 ∧ (∀ x ∈ p.2, p.1 * x ∈ Submodule.span ℚ (M : Set K)) ∧
        ∃ φ ψ : K →+* ℂ, ∃ x ∈ p.2, ‖φ x‖ ≠ ‖ψ x‖) ∧
      ∀ μ ∈ M, Algebra.norm ℚ μ = c → μ ∈ Φ ∨ ∃ p ∈ P, μ / p.1 ∈ p.2 := by
  classical
  rcases eq_or_ne c 0 with rfl | hc
  · exact ⟨{0}, Set.finite_singleton 0, ∅, Set.finite_empty, by simp,
      fun μ _ h ↦ Or.inl (Algebra.norm_eq_zero_iff.mp h)⟩
  obtain ⟨D, hD, hDM⟩ := exists_forall_isIntegral_mul hM
  set T := {μ | μ ∈ M ∧ Algebra.norm ℚ μ = c}
  obtain ⟨S, hS⟩ := exists_finset_forall_mem_unit hD (T := T) (fun μ hμ ↦ hDM μ hμ.1) hc
    fun μ hμ ↦ hμ.2
  let G := IntermediateField.normalClosure ℚ K (AlgebraicClosure ℚ)
  have : NumberField G := NumberField.of_module_finite ℚ G
  have : Nonempty (K →ₐ[ℚ] AlgebraicClosure ℚ) := ⟨IsAlgClosed.lift⟩
  have hG : ∀ x : K, ((minpoly ℚ x).map (algebraMap ℚ G)).Splits :=
    (isNormalClosure_normalClosure ℚ K (AlgebraicClosure ℚ)).splits
  have hSK : ((S : Set (HeightOneSpectrum (𝓞 K))).unit K).FG := (Group.fg_iff_subgroup_fg _).mp
    ((S : Set (HeightOneSpectrum (𝓞 K))).unit_fg S.finite_toSet)
  choose U hU using fun i : K →ₐ[ℚ] G ↦
    exists_finset_le_unit (fg_map hSK (Units.map (i : K →* G)))
  obtain ⟨Φ, hΦ, P, hP, hPp, hPc⟩ := exists_finite_forall_mem_or_of_splits hG
    (univ.biUnion U) hD (T := T) (fun μ hμ ↦ ⟨hDM μ hμ.1, hμ.2⟩) (fun μ hμ i ↦ by
      obtain ⟨u, hu, rfl⟩ := hS μ hμ
      exact ⟨Units.map (i : K →* G) u, mem_unit_of_subset
        (Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem U (mem_univ i)))
        (hU i (Subgroup.mem_map_of_mem _ hu)), rfl⟩)
    _ (Submodule.span ℚ (M : Set K)) le_rfl le_rfl
  exact ⟨Φ, hΦ, P, hP, hPp, fun μ hμ hc ↦ hPc μ ⟨hμ, hc⟩ (Submodule.subset_span hμ)⟩

/-- **Schmidt's theorem on norm-form equations** (Schmidt 1971–1972; Bombieri–Gubler, §7.4):
if the `ℚ`-span of a finitely generated `ℤ`-submodule `M` of `K` is non-degenerate, then for every
`c ∈ ℚ` the equation `N_{K/ℚ}(μ) = c` has finitely many solutions `μ ∈ M`. -/
theorem finite_setOf_norm_eq (M : Submodule ℤ K) (hM : M.FG)
    (hnd : IsNondegenerate (Submodule.span ℚ (M : Set K))) (c : ℚ) :
    {μ : K | μ ∈ M ∧ Algebra.norm ℚ μ = c}.Finite := by
  obtain ⟨Φ, hΦ, P, -, hP, hcover⟩ := exists_finite_forall_mem_or_div_mem M hM c
  refine hΦ.subset fun μ ⟨hμ, hc⟩ ↦ (hcover μ hμ hc).resolve_right ?_
  rintro ⟨p, hp, -⟩
  obtain ⟨h0, hsub, φ, ψ, x, hx, hne⟩ := hP p hp
  exact hne (hnd p.1 h0 p.2 hsub φ ψ x hx)

/-- **Only `ℚ` inside**: a subspace containing no nonzero multiple of a subfield other than `ℚ`
is non-degenerate. -/
theorem isNondegenerate_of_forall_eq_bot {V : Submodule ℚ K}
    (h : ∀ α : K, α ≠ 0 → ∀ F : IntermediateField ℚ K, (∀ x ∈ F, α * x ∈ V) → F = ⊥) :
    IsNondegenerate V := by
  intro α hα F hF φ ψ x hx
  rw [h α hα F hF, IntermediateField.mem_bot] at hx
  obtain ⟨q, rfl⟩ := hx
  simp

/-- **Fields of prime degree.** If `[K : ℚ]` is prime, every subspace of smaller dimension is
non-degenerate: the only subfields are `ℚ` and `K`, and `α K` has dimension `[K : ℚ]`. -/
theorem isNondegenerate_of_finrank_lt (hK : (finrank ℚ K).Prime) {V : Submodule ℚ K}
    (hV : finrank ℚ V < finrank ℚ K) : IsNondegenerate V := by
  refine isNondegenerate_of_forall_eq_bot fun α hα F hF ↦ ?_
  have hdvd : finrank ℚ F ∣ finrank ℚ K := ⟨_, (Module.finrank_mul_finrank ℚ F K).symm⟩
  rcases hK.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact IntermediateField.finrank_eq_one_iff.mp h
  · exfalso
    let f : F →ₗ[ℚ] V := LinearMap.codRestrict V
      ((LinearMap.mulLeft ℚ α).comp F.val.toLinearMap) fun x ↦ hF x x.2
    have hf : Function.Injective f := fun x y hxy ↦ Subtype.ext
      (mul_right_injective₀ hα (congrArg Subtype.val hxy :))
    exact (LinearMap.finrank_le_finrank_of_injective hf).not_gt (h ▸ hV)

end NumberField

/-! ### Acceptance criteria -/

section Tests

open NumberField Polynomial

/-- `2` is not a `p`-th power in `ℚ` for `p ≥ 2`: a rational root of `X ^ p - 2` is an integer. -/
private theorem pow_ne_two {p : ℕ} (hp : 2 ≤ p) (b : ℚ) : b ^ p ≠ 2 := by
  intro hb
  have hint : IsIntegral ℤ b := ⟨X ^ p - C 2, monic_X_pow_sub_C _ (by omega), by simp [hb]⟩
  obtain ⟨n, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hn : n ^ p = 2 := by
    rw [algebraMap_int_eq, eq_intCast] at hb
    exact_mod_cast hb
  have hm : n.natAbs ^ p = 2 := by rw [← Int.natAbs_pow, hn]; rfl
  rcases Nat.lt_or_ge n.natAbs 2 with h | h
  · have : n.natAbs ^ p ≤ 1 := pow_le_one₀ (Nat.zero_le _) (by omega)
    omega
  · have : 2 ^ 2 ≤ n.natAbs ^ p :=
      (Nat.pow_le_pow_right (by norm_num) hp).trans (Nat.pow_le_pow_left h p)
    omega

private instance : Fact (Irreducible (X ^ 5 - C 2 : ℚ[X])) :=
  ⟨X_pow_sub_C_irreducible_of_prime Nat.prime_five (pow_ne_two (by norm_num))⟩

private instance : Fact (Irreducible (X ^ 2 - C 2 : ℚ[X])) :=
  ⟨X_pow_sub_C_irreducible_of_prime Nat.prime_two (pow_ne_two le_rfl)⟩

private theorem finrank_adjoinRoot {p : ℕ} (hp : 0 < p) :
    finrank ℚ (AdjoinRoot (X ^ p - C 2 : ℚ[X])) = p := by
  rw [(AdjoinRoot.powerBasis (X_pow_sub_C_ne_zero hp 2)).finrank, AdjoinRoot.powerBasis_dim,
    natDegree_X_pow_sub_C]

/-- **A norm form in three variables.** For `θ = 2 ^ (1/5)`, the norm from `ℚ(θ)` takes every
value finitely often on `ℤ + ℤ θ + ℤ θ ^ 2` — Schmidt's theorem beyond Thue's two variables. The
module is non-degenerate because `5` is prime and `3 < 5`. -/
example (c : ℚ) :
    {μ : AdjoinRoot (X ^ 5 - C 2 : ℚ[X]) | μ ∈ Submodule.span ℤ
      {1, AdjoinRoot.root _, AdjoinRoot.root _ ^ 2} ∧ Algebra.norm ℚ μ = c}.Finite := by
  classical
  set θ := AdjoinRoot.root (X ^ 5 - C 2 : ℚ[X])
  refine finite_setOf_norm_eq _ (Submodule.fg_span (Set.toFinite _))
    (isNondegenerate_of_finrank_lt ?_ ?_) c
  · rw [finrank_adjoinRoot (by norm_num)]
    exact Nat.prime_five
  · rw [Submodule.span_span_of_tower, finrank_adjoinRoot (by norm_num),
      show ({1, θ, θ ^ 2} : Set _) = Set.range ![1, θ, θ ^ 2] by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Matrix.range_cons,
          Matrix.range_empty, Set.union_empty, Set.mem_union]]
    exact (finrank_range_le_card _).trans_lt (by simp)

/-- `θ = 2 ^ (1/5)` itself is a solution, of norm `2`. -/
example : AdjoinRoot.root (X ^ 5 - C 2 : ℚ[X]) ∈ Submodule.span ℤ
      {1, AdjoinRoot.root _, AdjoinRoot.root _ ^ 2} ∧
    Algebra.norm ℚ (AdjoinRoot.root (X ^ 5 - C 2 : ℚ[X])) = 2 := by
  refine ⟨Submodule.subset_span (by simp), ?_⟩
  have hf := X_pow_sub_C_ne_zero (show 0 < 5 by norm_num) (2 : ℚ)
  have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (AdjoinRoot.powerBasis hf)
  rw [AdjoinRoot.powerBasis_gen, AdjoinRoot.powerBasis_dim, AdjoinRoot.minpoly_root hf,
    natDegree_X_pow_sub_C, leadingCoeff_X_pow_sub_C (by norm_num)] at this
  exact this.trans (by norm_num)

/-- **Non-degeneracy is load-bearing.** In `ℚ(√2)` the full module `ℤ + ℤ √2` is degenerate, and
its norm form `x ^ 2 - 2 y ^ 2` takes the value `1` at the infinitely many units
`(1 + √2) ^ (2 k)`. -/
example : ¬ {μ : AdjoinRoot (X ^ 2 - C 2 : ℚ[X]) | μ ∈ Submodule.span ℤ
    {1, AdjoinRoot.root _} ∧ Algebra.norm ℚ μ = 1}.Finite := by
  set θ := AdjoinRoot.root (X ^ 2 - C 2 : ℚ[X])
  have hθ : θ ^ 2 = 2 := by
    have := AdjoinRoot.eval₂_root (X ^ 2 - C 2 : ℚ[X])
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at this
    rw [sub_eq_zero] at this
    rw [this]
    simp
  have hθi : IsIntegral ℤ θ := ⟨X ^ 2 - C 2, monic_X_pow_sub_C _ two_ne_zero, by simp [hθ]⟩
  set u := 1 + θ
  have hint : ∀ x : AdjoinRoot (X ^ 2 - C 2 : ℚ[X]), IsIntegral ℤ x →
      ∃ n : ℤ, (n : ℚ) = Algebra.norm ℚ x := fun x hx ↦ by
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm ℚ hx)
    exact ⟨n, by simpa using hn⟩
  obtain ⟨n, hn⟩ := hint u (isIntegral_one.add hθi)
  obtain ⟨m, hm⟩ := hint (θ - 1) (hθi.sub isIntegral_one)
  have hnm : n * m = 1 := by
    have := congrArg (Algebra.norm ℚ) (show u * (θ - 1) = 1 by linear_combination hθ)
    rw [map_mul, map_one, ← hn, ← hm] at this
    exact_mod_cast this
  have hN : Algebra.norm ℚ u ^ 2 = 1 := by
    rw [← hn]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hnm with h | h <;> simp [h]
  have hmem : ∀ k : ℕ, u ^ (2 * k) ∈ Submodule.span ℤ ({1, θ} : Set _) := by
    have : ∀ k : ℕ, ∃ a b : ℤ, u ^ (2 * k) = a + b * θ := by
      intro k
      induction k with
      | zero => exact ⟨1, 0, by simp⟩
      | succ k ih =>
        obtain ⟨a, b, h⟩ := ih
        refine ⟨3 * a + 4 * b, 2 * a + 3 * b, ?_⟩
        rw [mul_add, mul_one, pow_add, h]
        push_cast
        linear_combination (a + 2 * b + b * θ) * hθ
    intro k
    obtain ⟨a, b, h⟩ := this k
    rw [h]
    refine Submodule.add_mem _ ?_ ?_
    · simpa using Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_insert 1 {θ}))
    · simpa using Submodule.smul_mem _ b
        (Submodule.subset_span (Set.mem_insert_of_mem 1 (Set.mem_singleton θ)))
  let φ : AdjoinRoot (X ^ 2 - C 2 : ℚ[X]) →+* ℝ := AdjoinRoot.lift (algebraMap ℚ ℝ) √2 (by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C]
    simp)
  have hφ : φ θ = √2 := AdjoinRoot.lift_root _
  have hinj : Function.Injective fun k : ℕ ↦ u ^ (2 * k) := by
    intro k l hkl
    have h := congrArg φ hkl
    simp only [map_pow, u, map_add, map_one, hφ] at h
    have h1 : (1 : ℝ) < 1 + √2 := by
      have := Real.sqrt_pos.mpr (two_pos (α := ℝ))
      linarith
    have := pow_right_injective₀ (by linarith) h1.ne' h
    omega
  refine Set.infinite_of_injective_forall_mem hinj fun k ↦ ⟨hmem k, ?_⟩
  rw [pow_mul, map_pow, map_pow, hN, one_pow]

private instance : Fact (Irreducible (X ^ 2 - C (-1) : ℚ[X])) :=
  ⟨X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b h ↦ by nlinarith [sq_nonneg b]⟩

/-- In `ℚ(i)` all embeddings into `ℂ` have the same absolute value: they are `i ↦ ± i`, and the
second is the complex conjugate of the first. -/
private theorem norm_eq_of_gaussian (φ ψ : AdjoinRoot (X ^ 2 - C (-1) : ℚ[X]) →+* ℂ)
    (x : AdjoinRoot (X ^ 2 - C (-1) : ℚ[X])) : ‖φ x‖ = ‖ψ x‖ := by
  set θ := AdjoinRoot.root (X ^ 2 - C (-1) : ℚ[X])
  have hθ : θ ^ 2 = -1 := by
    have := AdjoinRoot.eval₂_root (X ^ 2 - C (-1) : ℚ[X])
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at this
    rw [sub_eq_zero] at this
    rw [this]
    simp
  have hsq : ∀ χ : AdjoinRoot (X ^ 2 - C (-1) : ℚ[X]) →+* ℂ, χ θ ^ 2 = Complex.I ^ 2 := fun χ ↦ by
    rw [← map_pow, hθ, map_neg, map_one, Complex.I_sq]
  have hext : ∀ χ χ' : AdjoinRoot (X ^ 2 - C (-1) : ℚ[X]) →+* ℂ, χ θ = χ' θ → χ x = χ' x :=
    fun χ χ' h ↦ DFunLike.congr_fun (AdjoinRoot.algHom_ext (g₁ := χ.toRatAlgHom)
      (g₂ := χ'.toRatAlgHom) h) x
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp ((hsq ψ).trans (hsq φ).symm) with h | h
  · rw [hext ψ φ h]
  · have hconj : ((starRingEnd ℂ).comp φ) θ = ψ θ := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsq φ) with h' | h' <;>
        simp [h, h', Complex.conj_I]
    rw [← hext _ _ hconj, RingHom.comp_apply, Complex.norm_conj]

/-- **The imaginary quadratic exception.** In `ℚ(i)` the full module `ℤ + ℤ i` is
non-degenerate, and `x ^ 2 + y ^ 2 = c` has finitely many solutions: the units of `ℤ[i]` are
finite. -/
example (c : ℚ) :
    {μ : AdjoinRoot (X ^ 2 - C (-1) : ℚ[X]) | μ ∈ Submodule.span ℤ {1, AdjoinRoot.root _} ∧
      Algebra.norm ℚ μ = c}.Finite :=
  finite_setOf_norm_eq _ (Submodule.fg_span (Set.toFinite _))
    (fun _ _ _ _ φ ψ x _ ↦ norm_eq_of_gaussian φ ψ x) c

end Tests
