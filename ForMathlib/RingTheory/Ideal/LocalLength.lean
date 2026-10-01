/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic

-- Used only inside proofs.
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Lengths of localized quotients

For a prime `𝔭` of a commutative ring `A` and an ideal `I`, `Ideal.localLength 𝔭 I` is the length
`ℓ(A_𝔭 / I A_𝔭)` of the localized quotient over the local ring `A_𝔭`. These lengths are the
multiplicities in the associativity formula for degrees.

The basic identity is the exact sequence `0 → A/(I : f) → A/I → A/(I + (f)) → 0`, whose first
map is multiplication by `f`. It survives localization, since colon ideals by one element commute
with localization (`Ideal.map_colon_singleton`).

## Main definitions

* `Ideal.colonMulMap I f`: multiplication by `f`, as a map `A/(I : f) → A/I`.
* `Ideal.localLength 𝔭 I`: the length of `A_𝔭 / I A_𝔭` over `A_𝔭`.

## Main statements

* `Ideal.exact_colonMulMap`: the exact sequence `0 → A/(I : f) → A/I → A/(I + (f)) → 0`.
* `Ideal.length_quotient_eq_add_colon`: `ℓ(A/I) = ℓ(A/(I : f)) + ℓ(A/(I + (f)))`.
* `Ideal.localLength_eq_add_colon`: the same for localized quotients.
* `Ideal.localLength_self`, `Ideal.localLength_of_not_le`, `Ideal.localLength_top`: the values
  `1` and `0` on the prime itself, on ideals not inside it, and on the unit ideal.
-/

@[expose] public section

variable {A : Type*} [CommRing A]

namespace Ideal

/-- Multiplication by `f`, as a map `A/(I : f) → A/I`. -/
noncomputable def colonMulMap (I : Ideal A) (f : A) : (A ⧸ I.colon {f}) →ₗ[A] A ⧸ I :=
  (I.colon {f}).liftQ (I.mkQ ∘ₗ LinearMap.mulRight A f) fun x hx ↦ by
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hx
    exact (Submodule.Quotient.mk_eq_zero I).mpr hx

theorem colonMulMap_mk (I : Ideal A) (f x : A) :
    colonMulMap I f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (x * f) :=
  rfl

theorem colonMulMap_injective (I : Ideal A) (f : A) : Function.Injective (colonMulMap I f) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  rw [LinearMap.mem_ker, Submodule.mkQ_apply, colonMulMap_mk, Submodule.Quotient.mk_eq_zero] at hx
  rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_colon_singleton, smul_eq_mul]
  exact hx

/-- **The exact sequence of a colon ideal.** `0 → A/(I : f) → A/I → A/(I + (f)) → 0`, the first
map being multiplication by `f`. -/
theorem exact_colonMulMap (I : Ideal A) (f : A) :
    Function.Exact (colonMulMap I f) (Submodule.factor (le_sup_left : I ≤ I ⊔ span {f})) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  have hh : Submodule.factor (le_sup_left : I ≤ I ⊔ span {f}) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk y := rfl
  rw [Submodule.mkQ_apply, hh, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hy
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨c, rfl⟩ := mem_span_singleton'.mp hc
    refine ⟨Submodule.Quotient.mk c, ?_⟩
    rw [colonMulMap_mk, Submodule.Quotient.eq]
    simpa using I.neg_mem ha
  · rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [Submodule.mkQ_apply, colonMulMap_mk, Submodule.Quotient.eq] at hx
    have : y = x * f - (x * f - y) := by ring
    rw [this]
    exact Submodule.sub_mem _ (mem_sup_right (mem_span_singleton'.mpr ⟨x, rfl⟩))
      (mem_sup_left hx)

/-- The lengths along the exact sequence of a colon ideal:
`ℓ(A/I) = ℓ(A/(I : f)) + ℓ(A/(I + (f)))`. -/
theorem length_quotient_eq_add_colon (I : Ideal A) (f : A) :
    Module.length A (A ⧸ I) =
      Module.length A (A ⧸ I.colon {f}) + Module.length A (A ⧸ (I ⊔ span {f})) :=
  Module.length_eq_add_of_exact _ _ (colonMulMap_injective I f) (Submodule.factor_surjective _)
    (exact_colonMulMap I f)

/-- Colon ideals by one element commute with localization. -/
theorem map_colon_singleton (M : Submonoid A) {S : Type*} [CommRing S] [Algebra A S]
    [IsLocalization M S] (I : Ideal A) (f : A) :
    (I.colon {f}).map (algebraMap A S) = (I.map (algebraMap A S)).colon {algebraMap A S f} := by
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    intro x hx
    rw [mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul]
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hx
    exact mem_map_of_mem _ hx
  · intro y hy
    obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective M y
    rw [Submodule.mem_colon_singleton, smul_eq_mul, ← IsLocalization.mk'_one (M := M) S f,
      ← IsLocalization.mk'_mul, mul_one, IsLocalization.mk'_mem_map_algebraMap_iff] at hy
    obtain ⟨m, hm, hmx⟩ := hy
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    refine ⟨m, hm, ?_⟩
    rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_assoc]
    exact hmx

variable (𝔭 : Ideal A) [𝔭.IsPrime]

/-- The length `ℓ(A_𝔭 / I A_𝔭)` over the local ring `A_𝔭`. -/
noncomputable def localLength (I : Ideal A) : ℕ∞ :=
  Module.length (Localization.AtPrime 𝔭)
    (Localization.AtPrime 𝔭 ⧸ I.map (algebraMap A (Localization.AtPrime 𝔭)))

/-- **Localized lengths along a colon ideal.**
`ℓ(A_𝔭/I_𝔭) = ℓ(A_𝔭/(I : f)_𝔭) + ℓ(A_𝔭/(I + (f))_𝔭)`. -/
theorem localLength_eq_add_colon (I : Ideal A) (f : A) :
    localLength 𝔭 I = localLength 𝔭 (I.colon {f}) + localLength 𝔭 (I ⊔ span {f}) := by
  rw [localLength, localLength, localLength, map_colon_singleton 𝔭.primeCompl, map_sup,
    map_span, Set.image_singleton]
  exact length_quotient_eq_add_colon _ _

variable {𝔭} in
/-- A larger ideal has a smaller localized length. -/
theorem localLength_le_of_le {I J : Ideal A} (h : I ≤ J) : localLength 𝔭 J ≤ localLength 𝔭 I :=
  Module.length_le_of_surjective (Submodule.factor (map_mono h)) (Submodule.factor_surjective _)

theorem localLength_top : localLength 𝔭 ⊤ = 0 := by
  rw [localLength, map_top, Module.length_eq_zero_iff]
  infer_instance

variable {𝔭} in
theorem localLength_of_not_le {I : Ideal A} (h : ¬ I ≤ 𝔭) : localLength 𝔭 I = 0 := by
  obtain ⟨x, hxI, hx𝔭⟩ := Set.not_subset.mp h
  have : I.map (algebraMap A (Localization.AtPrime 𝔭)) = ⊤ :=
    eq_top_of_isUnit_mem _ (mem_map_of_mem _ hxI)
      (IsLocalization.map_units (Localization.AtPrime 𝔭) (⟨x, hx𝔭⟩ : 𝔭.primeCompl))
  rw [localLength, this, Module.length_eq_zero_iff]
  infer_instance

theorem localLength_self : localLength 𝔭 𝔭 = 1 := by
  rw [localLength, Localization.AtPrime.map_eq_maximalIdeal]
  have : IsSimpleModule (Localization.AtPrime 𝔭)
      (Localization.AtPrime 𝔭 ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭)) :=
    isSimpleModule_iff_isCoatom.mpr (isMaximal_def.mp inferInstance)
  exact Module.length_eq_one _ _

variable {𝔭} in
theorem localLength_ne_zero {I : Ideal A} (h : I ≤ 𝔭) : localLength 𝔭 I ≠ 0 := by
  rw [localLength, ne_eq, Module.length_eq_zero_iff, not_subsingleton_iff_nontrivial,
    Quotient.nontrivial_iff, ← lt_top_iff_ne_top]
  refine lt_of_le_of_lt (map_mono h) ?_
  rw [Localization.AtPrime.map_eq_maximalIdeal, lt_top_iff_ne_top]
  exact IsPrime.ne_top inferInstance

end Ideal
