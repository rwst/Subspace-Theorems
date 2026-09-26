/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import CorvajaZannier2004.SubfieldDescent

-- Used only inside proofs.
import ArithmeticHeights.Absolute
import ArithmeticHeights.Extension
import CorvajaZannier2004.GaloisSetting
import DiophantineApproximation.UnitEquationSeveral
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.PrimitiveElement

/-!
# The Main Theorem of Corvaja–Zannier

**Main Theorem** (Corvaja–Zannier 2004, p. 2). Let `Γ ≤ ℝˣ` be a finitely generated group of
algebraic numbers, `δ` a nonzero real algebraic number and `ε > 0`. Then there are only finitely
many pairs `(q, u) ∈ ℤ × Γ` with `|δ q u| > 1`, `δ q u` not pseudo-Pisot and
`0 < ‖δ q u‖ < H(u) ^ (-ε) |q| ^ (-d - ε)`, where `d = [ℚ(u) : ℚ]`.

## Main results

* `NumberField.finite_of_finrank_le`: the descent through the subfields of a Galois number field,
  by strong induction on the degree, with Lemma 3 as the step.
* `NumberField.finite_setOf_not_isPseudoPisot`: the Main Theorem inside a Galois number field.
* `finite_setOf_not_isPseudoPisot`: the Main Theorem as printed, for real `Γ` and `δ`.

## Implementation notes

⚠ **The step of the induction.** Lemma 3 gives a proper subfield `k' < k` and a member `u₀` of the
family with `u / u₀ ∈ k'` infinitely often. The family `(q, u / u₀)` then satisfies the hypotheses
at `k'` with `δ u₀` for `δ` and `C H(u₀) ^ ε` for `C`, since `H(u / u₀) ≤ H(u) H(u₀)`; the exponent
`d` stays fixed, which is why the descent carries `[k : ℚ] ≤ d` rather than `d = [k : ℚ]`.

⚠ **`d = [ℚ(u) : ℚ]`.** The descent starts at the field `ℚ(u)` shared by infinitely many members,
which exists because a number field has only finitely many subfields.

## References

P. Corvaja and U. Zannier, Acta Math. **193** (2004), 175–191, Main Theorem and its proof, p. 7.
-/

@[expose] public section

open IsDedekindDomain Height Module IntermediateField

/-- A proper intermediate field has smaller degree. -/
theorem IntermediateField.finrank_lt_finrank_of_lt {F L : Type*} [Field F] [Field L]
    [Algebra F L] [FiniteDimensional F L] {E₁ E₂ : IntermediateField F L} (h : E₁ < E₂) :
    finrank F E₁ < finrank F E₂ := by
  have hlt := IntermediateField.finrank_lt_of_gt h
  have h₁ := Module.finrank_mul_finrank F E₁ L
  have h₂ := Module.finrank_mul_finrank F E₂ L
  have hpos : 0 < finrank F E₂ := Module.finrank_pos
  by_contra hle
  push Not at hle
  nlinarith

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Submultiplicativity of the absolute height**, from that of the relative one. -/
theorem absMulHeight₁_mul_le (x y : K) :
    absMulHeight₁ (x * y) ≤ absMulHeight₁ x * absMulHeight₁ y := by
  have hn : finrank ℚ K ≠ 0 := Module.finrank_pos.ne'
  refine le_of_pow_le_pow_left₀ hn (mul_nonneg (zero_le_one.trans (one_le_absMulHeight₁ x))
    (zero_le_one.trans (one_le_absMulHeight₁ y))) ?_
  rw [mul_pow, absMulHeight₁_pow_finrank, absMulHeight₁_pow_finrank, absMulHeight₁_pow_finrank]
  exact mulHeight₁_mul_le x y

/-- The absolute height of an inverse. -/
theorem absMulHeight₁_inv (x : K) : absMulHeight₁ x⁻¹ = absMulHeight₁ x := by
  have hn : finrank ℚ K ≠ 0 := Module.finrank_pos.ne'
  refine (pow_left_inj₀ (zero_le_one.trans (one_le_absMulHeight₁ _))
    (zero_le_one.trans (one_le_absMulHeight₁ _)) hn).mp ?_
  rw [absMulHeight₁_pow_finrank, absMulHeight₁_pow_finrank, mulHeight₁_inv]

/-- The elements of `K` that are real under `φ`, an intermediate field. -/
noncomputable def realField (φ : K →+* ℂ) : IntermediateField ℚ K :=
  (φ.eqLocusField ((starRingEnd ℂ).comp φ)).toIntermediateField fun r ↦ by simp

theorem mem_realField {φ : K →+* ℂ} {x : K} : x ∈ realField φ ↔ (φ x).im = 0 := by
  change φ x = starRingEnd ℂ (φ x) ↔ _
  rw [eq_comm, Complex.conj_eq_iff_im]

section Galois

variable [IsGalois ℚ K]

/-- **The descent of the Main Theorem** (p. 7): the family of Lemma 3, with the exponent `d` any
bound for `[k : ℚ]`, is finite. By strong induction on `[k : ℚ]`: were it infinite, Lemma 3 would
give `k' < k` and `u₀` with `u / u₀ ∈ k'` infinitely often, and the family `(q, u / u₀)`, with
`δ u₀` and `C H(u₀) ^ ε`, would be an infinite family at `k'`. -/
theorem finite_of_finrank_le (S : Finset (HeightOneSpectrum (𝓞 K))) (φ : K →+* ℂ) {d : ℕ}
    (k : IntermediateField ℚ K) (hkd : finrank ℚ k ≤ d) (hk : ∀ x ∈ k, (φ x).im = 0) {δ : K}
    (hδ0 : δ ≠ 0) (hδ : (φ δ).im = 0) {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
    {Z : Set (ℤ × Kˣ)} (hZk : ∀ x ∈ Z, (x.2 : K) ∈ k)
    (hS : ∀ x ∈ Z, ∀ τ : K ≃ₐ[ℚ] K,
      Units.map (τ : K →* K) x.2 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (h1 : ∀ x ∈ Z, 1 < ‖φ (δ * x.1 * x.2)‖)
    (hPP : ∀ x ∈ Z, ¬ IsPseudoPisot (φ (δ * x.1 * x.2)).re)
    (happrox : ∀ x ∈ Z, ∃ m : ℤ, ‖(m : ℂ) - φ (δ * x.1 * x.2)‖ <
      C * absMulHeight₁ (x.2 : K) ^ (-ε) * |(x.1 : ℝ)| ^ (-(d : ℝ) - ε)) :
    Z.Finite := by
  obtain ⟨n, hn⟩ : ∃ n, finrank ℚ k = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing k δ C Z with
  | _ n ih =>
  by_contra hZ
  have hq : ∀ x ∈ Z, x.1 ≠ 0 := fun x hx h0 ↦ by
    have := h1 x hx
    simp [h0] at this
    linarith
  have happrox' : ∀ x ∈ Z, ∃ m : ℤ, ‖(m : ℂ) - φ (δ * x.1 * x.2)‖ <
      C * absMulHeight₁ (x.2 : K) ^ (-ε) * |(x.1 : ℝ)| ^ (-(finrank ℚ k : ℝ) - ε) := by
    intro x hx
    obtain ⟨m, hm⟩ := happrox x hx
    refine ⟨m, hm.trans_le (mul_le_mul_of_nonneg_left ?_ ?_)⟩
    · have h1q : (1 : ℝ) ≤ |(x.1 : ℝ)| := by exact_mod_cast Int.one_le_abs (hq x hx)
      have hkd' : (finrank ℚ k : ℝ) ≤ d := by exact_mod_cast hkd
      exact Real.rpow_le_rpow_of_exponent_le h1q (by linarith)
    · exact mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans (one_le_absMulHeight₁ _)) _)
  obtain ⟨k', hk', x₀, hx₀, hinf⟩ := exists_lt_exists_mem_infinite_setOf_div_mem S φ k hk hδ0
    hδ hC hε hZ hZk hS h1 hPP happrox'
  set u₀ := x₀.2 with hu₀
  have hu₀k : (u₀ : K) ∈ k := hZk x₀ hx₀
  set f : ℤ × Kˣ → ℤ × Kˣ := fun x ↦ (x.1, x.2 / u₀) with hf
  have hfinj : f.Injective := fun x y h ↦ by
    simp only [hf, Prod.mk.injEq, div_left_inj] at h
    exact Prod.ext h.1 h.2
  set Z' := {x ∈ Z | (x.2 : K) / u₀ ∈ k'} with hZ'
  have hkey : ∀ x : ℤ × Kˣ,
      δ * u₀ * ((f x).1 : K) * ((f x).2 : K) = δ * x.1 * x.2 := fun x ↦ by
    simp only [hf, Units.val_div_eq_div_val]
    field_simp
  have hH : ∀ x : ℤ × Kˣ, absMulHeight₁ (x.2 : K) ^ (-ε) ≤
      absMulHeight₁ (u₀ : K) ^ ε * absMulHeight₁ ((f x).2 : K) ^ (-ε) := fun x ↦ by
    have hu : 0 < absMulHeight₁ (x.2 : K) := zero_lt_one.trans_le (one_le_absMulHeight₁ _)
    have hu0 : 0 < absMulHeight₁ (u₀ : K) := zero_lt_one.trans_le (one_le_absMulHeight₁ _)
    have hv : 0 < absMulHeight₁ ((f x).2 : K) := zero_lt_one.trans_le (one_le_absMulHeight₁ _)
    have hle : absMulHeight₁ ((f x).2 : K) ≤
        absMulHeight₁ (x.2 : K) * absMulHeight₁ (u₀ : K) := by
      change absMulHeight₁ ((x.2 / u₀ : Kˣ) : K) ≤ _
      rw [Units.val_div_eq_div_val, div_eq_mul_inv]
      exact (absMulHeight₁_mul_le _ _).trans_eq (congrArg _ (absMulHeight₁_inv (u₀ : K)))
    calc absMulHeight₁ (x.2 : K) ^ (-ε)
        = absMulHeight₁ (u₀ : K) ^ ε *
            (absMulHeight₁ (x.2 : K) * absMulHeight₁ (u₀ : K)) ^ (-ε) := by
          rw [Real.mul_rpow hu.le hu0.le, Real.rpow_neg hu0.le, mul_left_comm,
            mul_inv_cancel₀ (Real.rpow_pos_of_pos hu0 ε).ne', mul_one]
      _ ≤ absMulHeight₁ (u₀ : K) ^ ε * absMulHeight₁ ((f x).2 : K) ^ (-ε) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hv hle (neg_nonpos.mpr hε.le)) (Real.rpow_nonneg hu0.le _)
  have hk'k : finrank ℚ k' < n := hn ▸ IntermediateField.finrank_lt_finrank_of_lt hk'
  refine hinf (Set.Finite.of_finite_image (ih _ hk'k k' (hk'k.le.trans (hn ▸ hkd))
    (fun x hx ↦ hk x (hk'.le hx)) (δ := δ * u₀) ?_ ?_ (C := C * absMulHeight₁ (u₀ : K) ^ ε) ?_
    ?_ ?_ ?_ ?_ ?_ rfl) hfinj.injOn)
  · exact mul_ne_zero hδ0 u₀.ne_zero
  · rw [map_mul, Complex.mul_im, hδ, hk _ hu₀k]
    ring
  · exact mul_pos hC (Real.rpow_pos_of_pos (zero_lt_one.trans_le (one_le_absMulHeight₁ _)) _)
  · rintro _ ⟨x, hx, rfl⟩
    simpa only [hf, Units.val_div_eq_div_val] using hx.2
  · rintro _ ⟨x, hx, rfl⟩ τ
    simp only [hf, map_div]
    exact Subgroup.div_mem _ (hS x hx.1 τ) (hS x₀ hx₀ τ)
  · rintro _ ⟨x, hx, rfl⟩
    rw [hkey]
    exact h1 x hx.1
  · rintro _ ⟨x, hx, rfl⟩
    rw [hkey]
    exact hPP x hx.1
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨m, hm⟩ := happrox x hx.1
    refine ⟨m, ?_⟩
    rw [hkey]
    refine hm.trans_le ?_
    have hQ : 0 ≤ |((f x).1 : ℝ)| ^ (-(d : ℝ) - ε) := Real.rpow_nonneg (abs_nonneg _) _
    calc C * absMulHeight₁ (x.2 : K) ^ (-ε) * |(x.1 : ℝ)| ^ (-(d : ℝ) - ε)
        ≤ C * (absMulHeight₁ (u₀ : K) ^ ε * absMulHeight₁ ((f x).2 : K) ^ (-ε)) *
            |((f x).1 : ℝ)| ^ (-(d : ℝ) - ε) := by
          gcongr
          exact hH x
      _ = _ := by ring

/-- **The Main Theorem of Corvaja–Zannier inside a Galois number field** (p. 2), with a
constant `C`. Let `φ : K → ℂ`, `δ ≠ 0` real, and `Z` a set of pairs `(q, u)`, `u` real, with all
conjugates of `u` `S`-units, `|δ q u| > 1`, `δ q u` not pseudo-Pisot and
`‖δ q u - m‖ < C H(u) ^ (-ε) |q| ^ (-[ℚ(u):ℚ] - ε)` for some `m ∈ ℤ`. Then `Z` is finite. -/
theorem finite_setOf_not_isPseudoPisot (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : K →+* ℂ) {δ : K} (hδ0 : δ ≠ 0) (hδ : (φ δ).im = 0) {C ε : ℝ} (hC : 0 < C)
    (hε : 0 < ε) {Z : Set (ℤ × Kˣ)} (hreal : ∀ x ∈ Z, (φ x.2).im = 0)
    (hS : ∀ x ∈ Z, ∀ τ : K ≃ₐ[ℚ] K,
      Units.map (τ : K →* K) x.2 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (h1 : ∀ x ∈ Z, 1 < ‖φ (δ * x.1 * x.2)‖)
    (hPP : ∀ x ∈ Z, ¬ IsPseudoPisot (φ (δ * x.1 * x.2)).re)
    (happrox : ∀ x ∈ Z, ∃ m : ℤ, ‖(m : ℂ) - φ (δ * x.1 * x.2)‖ <
      C * absMulHeight₁ (x.2 : K) ^ (-ε) *
        |(x.1 : ℝ)| ^ (-(finrank ℚ ℚ⟮(x.2 : K)⟯ : ℝ) - ε)) :
    Z.Finite := by
  have : Finite (IntermediateField ℚ K) :=
    Field.finite_intermediateField_of_exists_primitive_element ℚ K
      (Field.exists_primitive_element ℚ K)
  by_contra hZ
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : IntermediateField ℚ K,
      {x ∈ Z | ℚ⟮(x.2 : K)⟯ = k₀}.Infinite := by
    by_contra h
    push Not at h
    exact hZ ((Set.finite_iUnion h).subset fun x hx ↦ Set.mem_iUnion.mpr ⟨_, hx, rfl⟩)
  obtain ⟨x₀, hx₀⟩ := hk₀.nonempty
  refine hk₀ (finite_of_finrank_le S φ k₀ le_rfl ?_ hδ0 hδ hC hε ?_
    (fun x hx ↦ hS x hx.1) (fun x hx ↦ h1 x hx.1) (fun x hx ↦ hPP x hx.1) ?_)
  · intro x hx
    rw [← hx₀.2] at hx
    exact mem_realField.mp ((adjoin_simple_le_iff.mpr (mem_realField.mpr (hreal x₀ hx₀.1))) hx)
  · intro x hx
    rw [← hx.2]
    exact mem_adjoin_simple_self ℚ _
  · intro x hx
    rw [← hx.2]
    exact happrox x hx.1

end Galois

end NumberField

open NumberField

/-- The absolute height is invariant under a `ℚ`-embedding of fields of characteristic zero,
for an algebraic element. -/
theorem NumberField.absMulHeight₁_map {L L' : Type*} [Field L] [CharZero L] [Field L']
    [CharZero L'] (f : L →ₐ[ℚ] L') {x : L} (hx : IsIntegral ℚ x) :
    absMulHeight₁ (f x) = absMulHeight₁ x := by
  have : FiniteDimensional ℚ ℚ⟮x⟯ := adjoin.finiteDimensional hx
  have : NumberField ℚ⟮x⟯ := {}
  have h₁ := absMulHeight₁_comp (IntermediateField.val ℚ⟮x⟯) (AdjoinSimple.gen ℚ x)
  have h₂ := absMulHeight₁_comp (f.comp (IntermediateField.val ℚ⟮x⟯)) (AdjoinSimple.gen ℚ x)
  simp only [AlgHom.comp_apply, IntermediateField.coe_val, AdjoinSimple.coe_gen] at h₁ h₂
  rw [h₂, h₁]

/-- **The Main Theorem of Corvaja–Zannier** (p. 2), for real `Γ` and `δ`. Let `Γ ≤ ℝˣ` be a
finitely generated group of algebraic numbers, `δ ≠ 0` real algebraic and `ε > 0`. Then only
finitely many `(q, u) ∈ ℤ × Γ` have `|δ q u| > 1`, `δ q u` not pseudo-Pisot and
`0 < ‖δ q u‖ < H(u) ^ (-ε) |q| ^ (-[ℚ(u):ℚ] - ε)`. -/
theorem finite_setOf_not_isPseudoPisot {Γ : Subgroup ℝˣ} (hΓ : Γ.FG)
    (hΓalg : ∀ u ∈ Γ, IsAlgebraic ℚ (u : ℝ)) {δ : ℝ} (hδ : IsAlgebraic ℚ δ) (hδ0 : δ ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    {p : ℤ × Γ | 1 < |δ * p.1 * ((p.2 : ℝˣ) : ℝ)| ∧
      ¬ IsPseudoPisot (δ * p.1 * ((p.2 : ℝˣ) : ℝ)) ∧
      0 < |δ * p.1 * ((p.2 : ℝˣ) : ℝ) - round (δ * p.1 * ((p.2 : ℝˣ) : ℝ))| ∧
      |δ * p.1 * ((p.2 : ℝˣ) : ℝ) - round (δ * p.1 * ((p.2 : ℝˣ) : ℝ))| <
        absMulHeight₁ ((p.2 : ℝˣ) : ℝ) ^ (-ε) *
          |(p.1 : ℝ)| ^ (-(finrank ℚ ℚ⟮((p.2 : ℝˣ) : ℝ)⟯ : ℝ) - ε)}.Finite := by
  classical
  obtain ⟨s, hs, hsfin⟩ := (Subgroup.fg_iff Γ).mp hΓ
  have hsΓ : ∀ g ∈ s, g ∈ Γ := fun g hg ↦ hs ▸ Subgroup.subset_closure hg
  have : Finite s := hsfin.to_subtype
  -- a Galois number field `K ⊆ ℂ` containing `δ` and the generators
  set ι : ℝ →ₐ[ℚ] ℂ := Complex.ofRealHom.toRatAlgHom with hι
  have hιinj : Function.Injective ι := Complex.ofReal_injective
  obtain ⟨K, _, _, _, φ, hφ⟩ := exists_isGalois_ringHom_mem_range
    (insert (δ : ℂ) (hsfin.toFinset.image fun g : ℝˣ ↦ ((g : ℝ) : ℂ))) (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hδ.algHom ι
      · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
        exact (hΓalg g (hsΓ g (hsfin.mem_toFinset.mp hg))).algHom ι)
  obtain ⟨δK, hδK⟩ := hφ _ (Finset.mem_insert_self _ _)
  have hgK : ∀ g ∈ s, ∃ w : Kˣ, φ w = ((g : ℝ) : ℂ) := fun g hg ↦ by
    obtain ⟨w, hw⟩ := hφ _ (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (hsfin.mem_toFinset.mpr hg)))
    have hw0 : w ≠ 0 := by
      rintro rfl
      rw [map_zero] at hw
      exact g.ne_zero (Complex.ofReal_eq_zero.mp hw.symm)
    exact ⟨Units.mk0 w hw0, hw⟩
  choose! W hW using hgK
  -- a finite `S` for the conjugates of the generators
  obtain ⟨S, hSΓ⟩ := exists_finset_le_unit (K := K)
    (Γ := Subgroup.closure (Set.range fun p : (K ≃ₐ[ℚ] K) × s ↦
      Units.map (p.1 : K →* K) (W p.2))) ((Subgroup.fg_iff _).mpr ⟨_, rfl, Set.finite_range _⟩)
  set T : Subgroup Kˣ := ⨅ τ : K ≃ₐ[ℚ] K,
    ((S : Set (HeightOneSpectrum (𝓞 K))).unit K).comap (Units.map (τ : K →* K)) with hT
  have hmemT : ∀ w : Kˣ, w ∈ T ↔ ∀ τ : K ≃ₐ[ℚ] K,
      Units.map (τ : K →* K) w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K := fun w ↦ by
    simp only [hT, Subgroup.mem_iInf, Subgroup.mem_comap]
  -- every `u ∈ Γ` is `φ w` for some `w` all of whose conjugates are `S`-units
  have hΓK : ∀ u ∈ Γ, ∃ w ∈ T, φ w = ((u : ℝ) : ℂ) := by
    intro u hu
    rw [← hs] at hu
    induction hu using Subgroup.closure_induction with
    | mem g hg =>
      exact ⟨W g, (hmemT _).mpr fun τ ↦ hSΓ (Subgroup.subset_closure ⟨(τ, ⟨g, hg⟩), rfl⟩),
        hW g hg⟩
    | one => exact ⟨1, T.one_mem, by simp⟩
    | mul u v _ _ hu hv =>
      obtain ⟨w₁, hw₁, h₁⟩ := hu
      obtain ⟨w₂, hw₂, h₂⟩ := hv
      exact ⟨w₁ * w₂, T.mul_mem hw₁ hw₂, by simp [h₁, h₂]⟩
    | inv u _ hu =>
      obtain ⟨w, hw, h⟩ := hu
      exact ⟨w⁻¹, T.inv_mem hw, by simp [h]⟩
  choose! V hVT hVφ using hΓK
  -- heights and degrees agree
  have hint : ∀ u ∈ Γ, IsIntegral ℚ (u : ℝ) := fun u hu ↦ (hΓalg u hu).isIntegral
  have hH : ∀ u ∈ Γ, absMulHeight₁ (u : ℝ) = absMulHeight₁ (V u : K) := fun u hu ↦ by
    rw [← absMulHeight₁_map ι (hint u hu), ← absMulHeight₁_comp φ.toRatAlgHom]
    exact congrArg _ (hVφ u hu).symm
  have hd : ∀ u ∈ Γ, finrank ℚ ℚ⟮(u : ℝ)⟯ = finrank ℚ ℚ⟮(V u : K)⟯ := fun u hu ↦ by
    rw [adjoin.finrank (hint u hu), adjoin.finrank (Algebra.IsIntegral.isIntegral _),
      ← minpoly.algHom_eq ι hιinj, ← minpoly.algHom_eq φ.toRatAlgHom φ.injective]
    exact congrArg (fun x ↦ (minpoly ℚ x).natDegree) (hVφ u hu).symm
  have hkey : ∀ p : ℤ × Γ, φ (δK * p.1 * V p.2) = ((δ * p.1 * ((p.2 : ℝˣ) : ℝ) : ℝ) : ℂ) :=
    fun p ↦ by
      rw [map_mul, map_mul, hδK, hVφ _ p.2.2, map_intCast]
      push_cast
      ring
  -- the transfer
  set F : ℤ × Γ → ℤ × Kˣ := fun p ↦ (p.1, V p.2) with hF
  have hFinj : F.Injective := fun p p' h ↦ by
    simp only [hF, Prod.mk.injEq] at h
    refine Prod.ext h.1 (Subtype.ext (Units.ext (Complex.ofReal_injective ?_)))
    rw [← hVφ _ p.2.2, ← hVφ _ p'.2.2, h.2]
  refine Set.Finite.of_finite_image ?_ hFinj.injOn
  refine NumberField.finite_setOf_not_isPseudoPisot S φ (δ := δK) (C := 1) ?_ ?_ one_pos hε
    ?_ ?_ ?_ ?_ ?_
  · rintro rfl
    simp only [map_zero] at hδK
    exact hδ0 (Complex.ofReal_injective hδK.symm)
  · rw [hδK, Complex.ofReal_im]
  · rintro _ ⟨p, -, rfl⟩
    rw [hVφ _ p.2.2, Complex.ofReal_im]
  · rintro _ ⟨p, -, rfl⟩
    exact (hmemT _).mp (hVT _ p.2.2)
  · rintro _ ⟨p, hp, rfl⟩
    rw [hkey, Complex.norm_real, Real.norm_eq_abs]
    exact hp.1
  · rintro _ ⟨p, hp, rfl⟩
    rw [hkey, Complex.ofReal_re]
    exact hp.2.1
  · rintro _ ⟨p, hp, rfl⟩
    refine ⟨round (δ * p.1 * ((p.2 : ℝˣ) : ℝ)), ?_⟩
    rw [hkey, ← Complex.ofReal_intCast, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_sub_comm, one_mul]
    change _ < absMulHeight₁ (V p.2 : K) ^ (-ε) *
      |(p.1 : ℝ)| ^ (-(finrank ℚ ℚ⟮(V p.2 : K)⟯ : ℝ) - ε)
    rw [← hH _ p.2.2, ← hd _ p.2.2]
    exact hp.2.2.2
