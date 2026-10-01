/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.GaussNorm
public import ForMathlib.RingTheory.MvPolynomial.ResultantPair
public import ForMathlib.RingTheory.MvPolynomial.ResultantSpecialization
public import Mathlib.RingTheory.Valuation.ValuationSubring

-- Used only inside proofs.
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Resultant forms at the nonarchimedean places

Rémond's Theorem 2.2 (LNM 1752, Ch. 7) at a nonarchimedean place, two-factor form: the
product specialization `ω : U₀ ↦ V W` of Prop. 3.5 does not change the maximum of the
coefficients of a resultant form. One inequality is the ultrametric inequality. For the other,
normalize `f` to have coefficients in the valuation ring `O`, one of them a unit; then `ω(f)` has
a unit coefficient too.

Rémond averages over specializations whose reductions avoid a hypersurface. Here we specialize
the forms `U_l` at the generic point instead, into an algebraic closure `L` of `K(u)`, and use a
valuation ring `W` of `L` dominating `O[u]_{𝔪 O[u]}` (Chevalley). By Prop. 2.16, `f` becomes
`c ∏_j U(x_j)` over `L`; normalizing the points into `W` and reducing modulo the maximal ideal of
`W` (Gauss's lemma) shows that `c` is a unit, and then that `ω(f) = c ∏_j V(x_j) W(x_j)` has a
unit coefficient.

## Main results

* `MvPolynomial.exists_isUnit_coeff_productMap`: the unit-coefficient statement, for any `F`
  whose specializations are products of point forms.
* `MvPolynomial.exists_map_eq_productMap`: `ω` preserves `O`-integrality.
* `MvPolynomial.valuation_coeff_productMap_resForm`: `max_m v(ω(f)_m) = max_m v(f_m)` for
  `f = res_{(e + e', d')}(I)` and every valuation `v` of `K`.
* `MvPolynomial.maxNorm_productMap_resForm`: the same for a nonarchimedean absolute value.
* `MvPolynomial.maxNorm_resForm_sumIndex_of_eq`: Thm 2.2, two factors, with Prop. 3.5 and Gauss's
  lemma.
-/

@[expose] public section

open Finset

namespace MvPolynomial

section Normalize

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}

/-- Scaling each block of the point scales `U(x)` by `∏_i μ_i^{e_i}`. -/
theorem pointForm_mul_block {L : Type*} [Field L] (e : ι → ℕ) (μ : ι → L) (x : σ → L) :
    pointForm b e (fun s ↦ μ (b s) * x s) = C (∏ i, μ i ^ e i) * pointForm b e x := by
  classical
  rw [pointForm_eq, pointForm_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [← mul_assoc, ← C_mul]
  congr 2
  have hm := mem_blockMonomials.1 m.2
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_fiberwise univ b]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Finset.prod_congr rfl fun s hs ↦ by rw [(mem_filter.1 hs).2], Finset.prod_pow_eq_pow_sum,
    ← congrFun hm i, weight_multiWeight_apply]

omit [Fintype σ] [Fintype ι] [DecidableEq ι] in
/-- **Normalizing a point into a valuation ring**: block by block, divide by a coordinate of
largest valuation. -/
theorem exists_normalize [Finite σ] {L : Type*} [Field L] (W : ValuationSubring L) {x : σ → L}
    (hx : ∀ i, ∃ s, b s = i ∧ x s ≠ 0) :
    ∃ (μ : ι → L) (x' : σ → W), (∀ i, μ i ≠ 0) ∧ (∀ i, ∃ s, b s = i ∧ x' s = 1) ∧
      ∀ s, x s = μ (b s) * x' s := by
  classical
  have := Fintype.ofFinite σ
  have hmax : ∀ i, ∃ s ∈ ({s | b s = i} : Finset σ), ∀ t ∈ ({s | b s = i} : Finset σ),
      W.valuation (x t) ≤ W.valuation (x s) := fun i ↦ by
    obtain ⟨s, hs, -⟩ := hx i
    exact Finset.exists_max_image _ _ ⟨s, by simpa using hs⟩
  choose t ht htmax using hmax
  have hne : ∀ i, x (t i) ≠ 0 := fun i ↦ by
    obtain ⟨s, hs, hxs⟩ := hx i
    have := htmax i s (by simpa using hs)
    intro h0
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact hxs this
  have hbt : ∀ i, b (t i) = i := fun i ↦ by simpa using ht i
  have hmem : ∀ s, x s / x (t (b s)) ∈ W := fun s ↦ by
    rw [← ValuationSubring.valuation_le_one_iff, map_div₀,
      div_le_one₀ ((Valuation.pos_iff _).2 (hne _))]
    exact htmax (b s) s (by simp)
  refine ⟨fun i ↦ x (t i), fun s ↦ ⟨_, hmem s⟩, hne, fun i ↦ ⟨t i, hbt i, ?_⟩, fun s ↦ ?_⟩
  · ext
    simp [hbt, div_self (hne i)]
  · simp [mul_div_cancel₀ _ (hne _)]

variable (b) in
/-- The point form `U(x) = ∑_m x^m u_m` over a commutative ring. -/
noncomputable def pointFormR {R : Type*} [CommRing R] (e : ι → ℕ) (x : σ → R) :
    MvPolynomial (GenericVar b fun _ : Unit ↦ e) R :=
  ∑ m : blockMonomials b e, C (∏ s, x s ^ (m : σ →₀ ℕ) s) * X ⟨(), m⟩

theorem map_pointFormR {R L : Type*} [CommRing R] [Field L] (f : R →+* L) (e : ι → ℕ)
    (x : σ → R) : map f (pointFormR b e x) = pointForm b e (f ∘ x) := by
  simp [pointFormR, pointForm_eq, map_prod]

end Normalize

section Main

universe u

variable {σ ι : Type u} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι} {K : Type u}
  [Field K] {κ : Type u} {e e' : ι → ℕ} {d' : κ → ι → ℕ}

/-- **Rémond's Theorem 2.2 at a nonarchimedean place**, two factors: if every specialization of
the forms `U_l` sends `F` to a product of point forms, and `F` has coefficients in a valuation
ring `O`, one of them a unit, then so does its image under the product specialization `ω` of
Prop. 3.5. -/
theorem exists_isUnit_coeff_productMap {F : MvPolynomial (GenericVar b (sumIndex e e' d')) K}
    (hF : ∀ (L : Type u) [Field L] [IsAlgClosed L] (φ : K →+* L) (y : GenericVar b d' → L),
      specEval (d := sumIndex e e' d') b φ y F ∈ pointSubmonoid b L (e + e'))
    (O : ValuationSubring K) {G₀ : MvPolynomial (GenericVar b (sumIndex e e' d')) O}
    (hG₀ : map O.subtype G₀ = F) (hunit : ∃ m, IsUnit (G₀.coeff m))
    {H₀ : MvPolynomial (GenericVar b (pairIndex e e' d')) O}
    (hH₀ : map O.subtype H₀ = productMap b K e e' d' F) :
    ∃ m, IsUnit (H₀.coeff m) := by
  classical
  -- the local ring `R = O[u]_{𝔪 O[u]}`
  obtain ⟨P, hPdef⟩ : ∃ P : Ideal (MvPolynomial (GenericVar b d') O),
      P = RingHom.ker (map (IsLocalRing.residue O)) := ⟨_, rfl⟩
  have hP : P.IsPrime := hPdef ▸ RingHom.ker_isPrime _
  -- the field `L`, an algebraic closure of `K(u)`
  set Lf := FractionRing (MvPolynomial (GenericVar b d') K)
  set L := AlgebraicClosure Lf
  set κK : MvPolynomial (GenericVar b d') K →+* L := (algebraMap Lf L).comp (algebraMap _ Lf)
  have hκK : Function.Injective κK :=
    (algebraMap Lf L).injective.comp (IsFractionRing.injective _ _)
  set ι0 : MvPolynomial (GenericVar b d') O →+* L := κK.comp (map O.subtype)
  have hι0 : Function.Injective ι0 := hκK.comp (map_injective _ Subtype.val_injective)
  have hunitR : ∀ a : P.primeCompl, IsUnit (ι0 a) := fun a ↦ by
    refine isUnit_iff_ne_zero.2 fun h0 ↦ a.2 ?_
    rw [(map_eq_zero_iff ι0 hι0).1 h0]
    exact P.zero_mem
  obtain ⟨ιR, hιR⟩ : ∃ ιR : Localization.AtPrime P →+* L,
      ιR = IsLocalization.lift (M := P.primeCompl) hunitR := ⟨_, rfl⟩
  have hR : IsLocalRing (Localization.AtPrime P) := inferInstance
  obtain ⟨W, hW, hloc⟩ := IsLocalRing.exists_factor_valuationRing (R := Localization.AtPrime P) ιR
  obtain ⟨jW, hjWdef⟩ : ∃ jW : Localization.AtPrime P →+* W,
      jW = ιR.codRestrict W.toSubring hW := ⟨_, rfl⟩
  have hjW : IsLocalHom jW := hjWdef ▸ hloc
  have hjWv : ∀ r, (jW r : L) = ιR r := fun r ↦ by rw [hjWdef]; rfl
  have hιRv : ∀ a : MvPolynomial (GenericVar b d') O,
      ιR (algebraMap (MvPolynomial (GenericVar b d') O) (Localization.AtPrime P) a) = ι0 a :=
    fun a ↦ by rw [hιR, IsLocalization.lift_eq]
  -- the maps `O → W`, `K → L` and the generic point
  set jO : O →+* W :=
    jW.comp ((algebraMap (MvPolynomial (GenericVar b d') O) (Localization.AtPrime P)).comp C)
  have hjO : IsLocalHom jO := by
    refine ⟨fun a ha ↦ ?_⟩
    by_contra hna
    have hPa : C a ∈ P := by
      rw [hPdef, RingHom.mem_ker, map_C, (IsLocalRing.residue_eq_zero_iff a).2 hna, map_zero]
    have hR := (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P (C a)).not.2
      (by simpa [Ideal.primeCompl] using hPa)
    exact hR (hjW.map_nonunit _ ha)
  set φ : K →+* L := κK.comp C
  have hjOv : ∀ a : O, (jO a : L) = φ a := fun a ↦ by
    simp [jO, hjWv, hιRv, ι0, φ]
  set yW : GenericVar b d' → W := fun s ↦
    jW (algebraMap (MvPolynomial (GenericVar b d') O) (Localization.AtPrime P) (X s))
  set y : GenericVar b d' → L := fun s ↦ κK (X s)
  have hyW : ∀ s, (yW s : L) = y s := fun s ↦ by simp [yW, hjWv, hιRv, ι0, y]
  -- residue fields
  set ρW := IsLocalRing.residue W
  set τ0 := IsLocalRing.ResidueField.map jO
  set ρO := IsLocalRing.residue O
  -- the specialization of `G₀` at the generic point
  set θA : MvPolynomial (GenericVar b (sumIndex e e' d')) O →+*
      MvPolynomial (GenericVar b fun _ : Unit ↦ e + e') W :=
    eval₂Hom (C.comp jO) fun v ↦ (splitSum e e' d' v).elim X fun l ↦ C (yW l)
  have hθA : (map W.subtype).comp θA = (eval₂Hom (C.comp φ) fun v ↦
      (splitSum e e' d' v).elim X fun l ↦ C (y l)).comp (map O.subtype) := by
    refine ringHom_ext (fun a ↦ ?_) fun v ↦ ?_
    · simp [θA, hjOv]
    · rcases v with ⟨_ | l, m⟩
      · simp [θA, splitSum]
      · simp [θA, splitSum, hyW]
  obtain ⟨c, Z, hZ, hcZ⟩ := hF L φ y
  choose! μ x' hμ hx' hzx using fun z hz ↦ exists_normalize W (hZ z hz)
  set c'' : L := c * (Z.map fun z ↦ ∏ i, μ z i ^ (e + e') i).prod
  have hpf : ∀ f : ι → ℕ, ∀ z ∈ Z,
      pointForm b f z = C (∏ i, μ z i ^ f i) * map W.subtype (pointFormR b f (x' z)) := by
    intro f z hz
    rw [map_pointFormR, ← pointForm_mul_block]
    congr 1
    funext s
    exact hzx z hz s
  have hprod : ∀ {T : Type u} (F : (σ → L) → MvPolynomial T L) (Q : (σ → L) → MvPolynomial T W),
      (∀ z ∈ Z, F z = C (∏ i, μ z i ^ (e + e') i) * map W.subtype (Q z)) →
      C c * (Z.map F).prod = C c'' * map W.subtype (Z.map Q).prod := by
    intro T F Q hF
    rw [Multiset.map_congr rfl hF, Multiset.prod_map_mul, map_multiset_prod, Multiset.map_map]
    simp only [c'', C_mul, map_multiset_prod C, Multiset.map_map]
    rw [mul_assoc]
    rfl
  have hpfne : ∀ f : ι → ℕ, ∀ z ∈ Z, map ρW (pointFormR b f (x' z)) ≠ 0 := by
    intro f z hz
    rw [map_pointFormR]
    refine (irreducible_pointForm f fun i ↦ ?_).ne_zero
    obtain ⟨s, hs, h1⟩ := hx' z hz i
    exact ⟨s, hs, by simp [h1]⟩
  -- the `A` side: `θA G₀ = c'' ∏_j U(x'_j)` with `c''` a unit of `W`
  set QA := (Z.map fun z ↦ pointFormR b (e + e') (x' z)).prod
  have hA : map W.subtype (θA G₀) = C c'' * map W.subtype QA :=
    (RingHom.congr_fun hθA G₀).trans <| by
      rw [RingHom.comp_apply, hG₀]
      exact (RingHom.congr_fun (specEval_sumIndex (e := e) (e' := e') φ y) _).symm.trans
        (hcZ.trans (hprod _ _ (hpf (e + e'))))
  have hQA : map ρW QA ≠ 0 := by
    rw [map_multiset_prod, Multiset.map_map]
    refine Multiset.prod_ne_zero fun h0 ↦ ?_
    obtain ⟨z, hz, hz0⟩ := Multiset.mem_map.1 h0
    exact hpfne _ z hz hz0
  obtain ⟨m₀, u, hu⟩ := exists_isUnit_coeff_of_map_residue_ne_zero hQA
  set cW : W := (θA G₀).coeff m₀ * ↑u⁻¹
  have hcW : (cW : L) = c'' := by
    have h := congrArg (fun Q ↦ Q.coeff m₀) hA
    simp only [coeff_map, coeff_C_mul] at h
    have h1 : ((QA.coeff m₀ * ↑u⁻¹ : W) : L) = 1 := by rw [← hu, Units.mul_inv]; rfl
    calc (cW : L) = ((θA G₀).coeff m₀ : L) * ((↑u⁻¹ : W) : L) := rfl
      _ = c'' * ((QA.coeff m₀ * ↑u⁻¹ : W) : L) := by
        rw [show ((θA G₀).coeff m₀ : L) = W.subtype ((θA G₀).coeff m₀) from rfl, h]
        simp [mul_assoc]
      _ = c'' := by rw [h1, mul_one]
  have hAW : θA G₀ = C cW * QA := by
    refine map_injective W.subtype Subtype.val_injective ?_
    rw [map_mul, map_C, hA]
    congr 2
    exact hcW.symm
  -- reduction modulo the maximal ideals: the `U_l` stay algebraically independent
  set τ : MvPolynomial (GenericVar b d') (IsLocalRing.ResidueField O) →+*
      IsLocalRing.ResidueField W := eval₂Hom τ0 fun s ↦ ρW (yW s)
  have hτρ : τ.comp (map ρO) =
      ρW.comp (jW.comp (algebraMap (MvPolynomial (GenericVar b d') O) _)) := by
    refine ringHom_ext (fun a ↦ ?_) fun s ↦ ?_
    · simp [τ, τ0, jO, ρO, ρW, IsLocalRing.ResidueField.map_residue]
    · simp [τ, yW]
  have hτ : Function.Injective τ := by
    refine (injective_iff_map_eq_zero τ).2 fun p hp ↦ ?_
    obtain ⟨q, rfl⟩ := map_surjective ρO IsLocalRing.residue_surjective p
    by_contra hq
    have hqP : q ∈ P.primeCompl := by
      change q ∉ P
      rw [hPdef]
      exact hq
    have hu := (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P q).2 hqP
    refine (IsLocalRing.residue_ne_zero_iff_isUnit _).2 (hu.map jW) ?_
    exact (RingHom.congr_fun hτρ q).symm.trans hp
  set ΘA : MvPolynomial (GenericVar b (sumIndex e e' d')) (IsLocalRing.ResidueField O) →+*
      MvPolynomial (GenericVar b fun _ : Unit ↦ e + e') (IsLocalRing.ResidueField W) :=
    (map τ).comp ((sumAlgEquiv (IsLocalRing.ResidueField O) (GenericVar b fun _ : Unit ↦ e + e')
      (GenericVar b d')).toRingEquiv.toRingHom.comp (rename (splitSum e e' d')).toRingHom)
  have hΘA : (map ρW).comp θA = ΘA.comp (map ρO) := by
    refine ringHom_ext (fun a ↦ ?_) fun v ↦ ?_
    · simp [θA, ΘA, τ, τ0, jO, ρO, ρW, IsLocalRing.ResidueField.map_residue]
    · rcases v with ⟨_ | l, m⟩
      · simp [θA, ΘA, splitSum]
      · simp [θA, ΘA, splitSum, τ]
  have hΘinj : Function.Injective ΘA :=
    (map_injective τ hτ).comp ((sumAlgEquiv _ _ _).injective.comp
      (rename_injective _ (splitSum e e' d').injective))
  have hcWres : ρW cW ≠ 0 := by
    intro h0
    have h1 : map ρW (θA G₀) = 0 := by rw [hAW, map_mul, map_C, h0, C_0, zero_mul]
    obtain ⟨m, hm⟩ := hunit
    refine map_residue_ne_zero_of_isUnit_coeff hm (hΘinj ?_)
    rw [map_zero, ← RingHom.comp_apply, ← hΘA, RingHom.comp_apply, h1]
  -- the `B` side: `θB H₀ = c'' ∏_j V(x'_j) W(x'_j)`
  set θB : MvPolynomial (GenericVar b (pairIndex e e' d')) O →+*
      MvPolynomial (GenericVar b (fun _ : Unit ↦ e) ⊕ GenericVar b (fun _ : Unit ↦ e')) W :=
    eval₂Hom (C.comp jO) fun v ↦ (splitPair e e' d' v).elim X fun l ↦ C (yW l)
  have hθB : (map W.subtype).comp θB = (specPair φ e e' d' y).comp (map O.subtype) := by
    refine ringHom_ext (fun a ↦ ?_) fun v ↦ ?_
    · simp [θB, specPair, hjOv]
    · rcases v with ⟨_ | _ | l, m⟩
      · simp [θB, specPair, splitPair]
      · simp [θB, specPair, splitPair]
      · simp [θB, specPair, splitPair, hyW]
  set QB := (Z.map fun z ↦ rename Sum.inl (pointFormR b e (x' z)) *
    rename Sum.inr (pointFormR b e' (x' z))).prod
  have hB : map W.subtype (θB H₀) = C c'' * map W.subtype QB :=
    (RingHom.congr_fun hθB H₀).trans <| by
      rw [RingHom.comp_apply, hH₀]
      refine (specPair_productMap φ y _ hcZ).trans (hprod _ _ fun z hz ↦ ?_)
      rw [hpf e z hz, hpf e' z hz]
      simp only [map_mul, map_rename, rename_C, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
      ring
  have hQB : map ρW QB ≠ 0 := by
    rw [map_multiset_prod, Multiset.map_map]
    refine Multiset.prod_ne_zero fun h0 ↦ ?_
    obtain ⟨z, hz, hz0⟩ := Multiset.mem_map.1 h0
    simp only [Function.comp_apply, map_mul, map_rename] at hz0
    rcases mul_eq_zero.1 hz0 with h | h
    · exact hpfne e z hz (rename_injective _ Sum.inl_injective (h.trans (map_zero _).symm))
    · exact hpfne e' z hz (rename_injective _ Sum.inr_injective (h.trans (map_zero _).symm))
  have hBW : θB H₀ = C cW * QB := by
    refine map_injective W.subtype Subtype.val_injective ?_
    rw [map_mul, map_C, hB]
    congr 2
    exact hcW.symm
  -- if `H₀` had no unit coefficient, it would vanish modulo `𝔪_O`
  refine exists_isUnit_coeff_of_map_residue_ne_zero fun h0 ↦ ?_
  set ΘB : MvPolynomial (GenericVar b (pairIndex e e' d')) (IsLocalRing.ResidueField O) →+*
      MvPolynomial (GenericVar b (fun _ : Unit ↦ e) ⊕ GenericVar b (fun _ : Unit ↦ e'))
        (IsLocalRing.ResidueField W) :=
    eval₂Hom (C.comp τ0) fun v ↦ (splitPair e e' d' v).elim X fun l ↦ C (ρW (yW l))
  have hΘB : (map ρW).comp θB = ΘB.comp (map ρO) := by
    refine ringHom_ext (fun a ↦ ?_) fun v ↦ ?_
    · simp [θB, ΘB, τ0, jO, ρO, ρW, IsLocalRing.ResidueField.map_residue]
    · rcases v with ⟨_ | _ | l, m⟩
      · simp [θB, ΘB, splitPair]
      · simp [θB, ΘB, splitPair]
      · simp [θB, ΘB, splitPair]
  have h1 : map ρW (θB H₀) = 0 := by
    rw [← RingHom.comp_apply, hΘB, RingHom.comp_apply, h0, map_zero]
  rw [hBW, map_mul, map_C] at h1
  exact mul_ne_zero (by simpa using hcWres) hQB h1

/-- `ω` sends polynomials with coefficients in `O` to polynomials with coefficients in `O`. -/
theorem exists_map_eq_productMap (O : ValuationSubring K)
    (G₀ : MvPolynomial (GenericVar b (sumIndex e e' d')) O) :
    ∃ H₀ : MvPolynomial (GenericVar b (pairIndex e e' d')) O,
      map O.subtype H₀ = productMap b K e e' d' (map O.subtype G₀) := by
  set ωO : MvPolynomial (GenericVar b (sumIndex e e' d')) O →+*
      MvPolynomial (GenericVar b (pairIndex e e' d')) O := eval₂Hom C fun v ↦ match v with
    | ⟨none, m⟩ => (genericForm O b (pairIndex e e' d') (some none) *
        genericForm O b (pairIndex e e' d') none).coeff (m : σ →₀ ℕ)
    | ⟨some l, m⟩ => X ⟨some (some l), m⟩
  have h : (map O.subtype).comp ωO = (productMap b K e e' d').comp (map O.subtype) := by
    refine ringHom_ext (fun a ↦ by simp [ωO, productMap]) fun v ↦ ?_
    rcases v with ⟨_ | l, m⟩
    · simp only [RingHom.comp_apply, ωO, coe_eval₂Hom, eval₂_X, map_X]
      rw [← coeff_map, map_mul, map_map_genericForm, map_map_genericForm]
      simp [productMap]
    · simp [ωO, productMap]
  exact ⟨ωO G₀, RingHom.congr_fun h G₀⟩

variable [Fintype κ]

/-- **Rémond's Theorem 2.2 at a nonarchimedean place**, two factors, for a valuation `v` of `K`:
if `c f` has `v`-integral coefficients, one of them a `v`-unit, where `f = res_{(e + e', d')}(I)`,
then so does `c ω(f)`. In other words, `max_m v(ω(f)_m) = max_m v(f_m)`. -/
theorem valuation_coeff_productMap_resForm (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree ≤ Fintype.card κ) (O : ValuationSubring K) {c : K}
    (h1 : ∀ m, O.valuation (c * (resForm b K (sumIndex e e' d') I).coeff m) ≤ 1)
    (h2 : ∃ m, O.valuation (c * (resForm b K (sumIndex e e' d') I).coeff m) = 1) :
    (∀ m, O.valuation (c * (productMap b K e e' d' (resForm b K (sumIndex e e' d') I)).coeff m)
      ≤ 1) ∧
    ∃ m, O.valuation (c * (productMap b K e e' d' (resForm b K (sumIndex e e' d') I)).coeff m)
      = 1 := by
  set f := resForm b K (sumIndex e e' d') I
  have hcard : (hilbertPoly b I).totalDegree + 1 ≤ Nat.card (Option κ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_option]
    omega
  have hF : ∀ (L : Type u) [Field L] [IsAlgClosed L] (φ : K →+* L) (y : GenericVar b d' → L),
      specEval (d := sumIndex e e' d') b φ y (C c * f) ∈ pointSubmonoid b L (e + e') := by
    intro L _ _ φ y
    have h := exists_specEval_resForm_eq (κ := κ) (d := sumIndex e e' d') hb hI hcard φ y
    have hC : specEval (d := sumIndex e e' d') b φ y (C c) = C (φ c) :=
      (RingHom.congr_fun (specEval_sumIndex (e := e) (e' := e') φ y) (C c)).trans
        (eval₂_C _ _ _)
    have hmul := map_mul (specEval (d := sumIndex e e' d') b φ y) (C c) f
    exact hmul ▸ Submonoid.mul_mem _ (hC ▸ C_mem_pointSubmonoid _) h
  obtain ⟨G₀, hG₀⟩ := exists_map_subtype_eq O (F := C c * f) fun m ↦ by
    rw [coeff_C_mul, ← O.valuation_le_one_iff]
    exact h1 m
  obtain ⟨H₀, hH₀⟩ := exists_map_eq_productMap O G₀
  have hH₀' : map O.subtype H₀ = productMap b K e e' d' (C c * f) := hH₀.trans (by rw [hG₀])
  have hωC : productMap b K e e' d' (C c * f) = C c * productMap b K e e' d' f := by
    rw [map_mul]
    simp [productMap]
  have hG : ∀ m, (G₀.coeff m : K) = c * f.coeff m := fun m ↦ by
    simpa [coeff_map, coeff_C_mul] using congrArg (fun P ↦ P.coeff m) hG₀
  have hH : ∀ m, (H₀.coeff m : K) = c * (productMap b K e e' d' f).coeff m := fun m ↦ by
    simpa [coeff_map, coeff_C_mul] using congrArg (fun P ↦ P.coeff m) (hH₀'.trans hωC)
  refine ⟨fun m ↦ ?_, ?_⟩
  · rw [← hH, O.valuation_le_one_iff]
    exact (H₀.coeff m).2
  · obtain ⟨m, hm⟩ := h2
    obtain ⟨m', hm'⟩ := exists_isUnit_coeff_productMap hF O hG₀
      ⟨m, (O.valuation_eq_one_iff _).2 (by rw [hG]; exact hm)⟩ hH₀'
    exact ⟨m', by rw [← hH]; exact (O.valuation_eq_one_iff _).1 hm'⟩

/-- **Rémond's Theorem 2.2 at a nonarchimedean place**, comparison step: `ω` does not change the
Gauss norm of `f = res_{(e + e', d')}(I)`. -/
theorem maxNorm_productMap_resForm (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree ≤ Fintype.card κ) {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) :
    maxNorm v (productMap b K e e' d' (resForm b K (sumIndex e e' d') I)) =
      maxNorm v (resForm b K (sumIndex e e' d') I) := by
  set f := resForm b K (sumIndex e e' d') I
  rcases eq_or_ne f 0 with h0 | hf
  · rw [h0, map_zero, maxNorm_zero, maxNorm_zero]
  obtain ⟨a, ha, hva, hfa⟩ := exists_maxNorm_C_mul_eq_one (v := v) hf
  set O := v.valuationSubring hv
  have hle : ∀ x : K, O.valuation x ≤ 1 ↔ v x ≤ 1 := fun x ↦ O.valuation_le_one_iff x
  have heq : ∀ x : K, O.valuation x = 1 ↔ v x = 1 := fun x ↦ by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have hx : x ∈ O := (O.valuation_le_one_iff x).1 h.le
      exact (AbsoluteValue.isUnit_valuationSubring_iff hv ⟨x, hx⟩).1
        ((O.valuation_eq_one_iff ⟨x, hx⟩).2 h)
    · have hx : x ∈ O := (AbsoluteValue.mem_valuationSubring hv).2 h.le
      exact (O.valuation_eq_one_iff ⟨x, hx⟩).1
        ((AbsoluteValue.isUnit_valuationSubring_iff hv ⟨x, hx⟩).2 h)
  have hfa0 : C a⁻¹ * f ≠ 0 := mul_ne_zero (by simpa using ha) hf
  obtain ⟨m₀, -, hm₀⟩ := exists_maxNorm_eq (v := v) hfa0
  obtain ⟨h1, m, h2⟩ := valuation_coeff_productMap_resForm (e := e) (e' := e') (d' := d') hb hI
    hdim O (c := a⁻¹)
    (fun m ↦ (hle _).2 (by rw [← coeff_C_mul, ← hfa]; exact le_maxNorm _ m))
    ⟨m₀, (heq _).2 (by rw [← coeff_C_mul, hm₀, hfa])⟩
  have hω : maxNorm v (C a⁻¹ * productMap b K e e' d' f) = 1 :=
    maxNorm_eq_of (fun m ↦ by rw [coeff_C_mul]; exact (hle _).1 (h1 m))
      ⟨m, by rw [coeff_C_mul]; exact (heq _).1 h2⟩
  rw [maxNorm_C_mul, map_inv₀, inv_mul_eq_one₀ (v.pos ha).ne'] at hω
  rw [← hω, hva]

/-- **Rémond's Theorem 2.2 at a nonarchimedean place**, two factors: if
`ω(res_{(e + e', d')}(I)) = c res_{(e, d')}(I) res_{(e', d')}(I)`, then the Gauss norms satisfy
`‖res_{(e + e', d')}(I)‖_v = |c|_v ‖res_{(e, d')}(I)‖_v ‖res_{(e', d')}(I)‖_v`. -/
theorem maxNorm_resForm_sumIndex_of_eq (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree ≤ Fintype.card κ) {c : K}
    (hc : productMap b K e e' d' (resForm b K (sumIndex e e' d') I) =
      C c * (rename (leftVar (b := b) e e' d') (resForm b K (leftIndex e d') I) *
        rename (rightVar (b := b) e e' d') (resForm b K (leftIndex e' d') I)))
    {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v) :
    maxNorm v (resForm b K (sumIndex e e' d') I) =
      v c * maxNorm v (resForm b K (leftIndex e d') I) *
        maxNorm v (resForm b K (leftIndex e' d') I) := by
  rw [← maxNorm_productMap_resForm hb hI hdim hv, hc, maxNorm_C_mul, maxNorm_mul hv,
    maxNorm_rename (leftVar_injective e e' d'), maxNorm_rename (rightVar_injective e e' d'),
    mul_assoc]

end Main

end MvPolynomial
