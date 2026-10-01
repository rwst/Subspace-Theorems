/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.LinearAlgebra.Matrix.DetIdeal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.IsTensorProduct

-- Used only inside proofs.
import ForMathlib.RingTheory.TensorProduct.IsBaseChangeQuotient
import ForMathlib.RingTheory.UniqueFactorizationDomain.LocalizationAtPrime
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite

/-!
# The characteristic form of a torsion module over a factorial ring

Let `A` be a unique factorization domain and `M` a finitely generated `A`-module. For a prime
ideal `P`, `Module.primeLength P M` is the length of the localization `M_P` over `A_P`.

* `Module.primeLength_le_iff`: for a prime element `p` and a presentation
  `M = (ι → A) ⧸ N`, `n ≤ ℓ_{(p)}(M)` iff `p ^ n` divides all maximal minors of `N`.
  This is Rémond's Lemma 3.1, via `Submodule.length_quotient_detIdeal` over the discrete
  valuation ring `A_(p)`.

G. Rémond, *Élimination multihomogène*, Chapter 5 of Nesterenko–Philippon (eds.),
*Introduction to algebraic independence theory*, LNM 1752 (2001), §3.1.
-/

@[expose] public section

open Ideal

namespace Module

section Length

variable {A : Type*} [CommRing A] (P : Ideal A) (M : Type*) [AddCommGroup M] [Module A M]

open scoped Classical in
/-- The length of the localization `M_P` over `A_P` (`0` if `P` is not prime). -/
noncomputable def primeLength : ℕ∞ :=
  if _h : P.IsPrime then length (Localization.AtPrime P) (LocalizedModule P.primeCompl M) else 0

variable {P M}

/-- `primeLength` may be computed in any localization of `M` at `P`. -/
theorem primeLength_eq_length [P.IsPrime] {M' : Type*} [AddCommGroup M'] [Module A M']
    [Module (Localization.AtPrime P) M'] [IsScalarTower A (Localization.AtPrime P) M']
    (f : M →ₗ[A] M') [IsLocalizedModule P.primeCompl f] :
    primeLength P M = length (Localization.AtPrime P) M' := by
  rw [primeLength, dite_eq_left ‹_›]
  exact ((IsLocalizedModule.linearEquiv P.primeCompl (LocalizedModule.mkLinearMap _ M) f
    ).extendScalarsOfIsLocalization P.primeCompl (Localization.AtPrime P)).length_eq

theorem primeLength_congr {M' : Type*} [AddCommGroup M'] [Module A M'] (e : M ≃ₗ[A] M') :
    primeLength P M = primeLength P M' := by
  by_cases hP : P.IsPrime
  · rw [primeLength_eq_length (P := P) (LocalizedModule.mkLinearMap P.primeCompl M' ∘ₗ
      (e : M →ₗ[A] M')), primeLength, dite_eq_left hP]
  · simp [primeLength, hP]

/-- `primeLength` is additive in short exact sequences. -/
theorem primeLength_eq_add {N Q : Type*} [AddCommGroup N] [Module A N] [AddCommGroup Q]
    [Module A Q] (f : N →ₗ[A] M) (g : M →ₗ[A] Q) (hf : Function.Injective f)
    (hg : Function.Surjective g) (H : Function.Exact f g) :
    primeLength P M = primeLength P N + primeLength P Q := by
  by_cases hP : P.IsPrime
  · simp only [primeLength, dite_eq_left hP]
    let S := P.primeCompl
    let L := Localization.AtPrime P
    let f' := (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S N)
      (LocalizedModule.mkLinearMap S M) f).extendScalarsOfIsLocalization S L
    let g' := (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap S Q) g).extendScalarsOfIsLocalization S L
    exact length_eq_add_of_exact f' g' (IsLocalizedModule.map_injective _ _ _ _ hf)
      (IsLocalizedModule.map_surjective _ _ _ _ hg) (LocalizedModule.map_exact S f g H)
  · simp [primeLength, hP]

end Length

section Presentation

variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Lengths from maximal minors** (Rémond, Lemma 3.1). For a prime element `p` of a unique
factorization domain and `N ≤ ι → A`, the cokernel `(ι → A) ⧸ N` localized at `(p)` has length
at least `n` iff `p ^ n` divides every maximal minor of `N`. -/
theorem primeLength_le_iff (N : Submodule A (ι → A)) {p : A} (hp : Prime p) (n : ℕ) :
    (n : ℕ∞) ≤ primeLength (span {p}) ((ι → A) ⧸ N) ↔ ∀ g ∈ N.detIdeal, p ^ n ∣ g := by
  have hP : (span {p}).IsPrime := (span_singleton_prime hp.ne_zero).mpr hp
  let L := Localization.AtPrime (span {p})
  have hL : IsDiscreteValuationRing L :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_prime hp rfl L
  let f : (ι → A) →ₗ[A] ι → L := .pi fun i ↦ Algebra.linearMap A L ∘ₗ .proj i
  rw [primeLength_eq_length (N.toLocalizedQuotient' L (span {p}).primeCompl f),
    (Submodule.quotEquivOfEq _ _ (Submodule.localized'_eq_span L _ f N)).length_eq,
    ← Submodule.length_quotient_detIdeal,
    ← IsDiscreteValuationRing.le_pow_maximalIdeal_iff,
    show f '' N = (fun w ↦ algebraMap A L ∘ w) '' N from rfl, Submodule.detIdeal_span_image,
    IsLocalization.AtPrime.maximalIdeal_eq_span (p := p) rfl L, span_singleton_pow,
    map_le_iff_le_comap]
  refine ⟨fun h g hg ↦ ?_, fun h g hg ↦ ?_⟩
  · exact (IsLocalization.AtPrime.algebraMap_mem_span_pow_iff hp rfl L g n).mp (h hg)
  · exact (IsLocalization.AtPrime.algebraMap_mem_span_pow_iff hp rfl L g n).mpr (h g hg)

omit [Fintype ι] [DecidableEq ι] in
/-- Without torsion, every localization has infinite length. -/
theorem primeLength_quotient_eq_top [Finite ι] (N : Submodule A (ι → A)) {p : A} (hp : Prime p)
    (h : annihilator A ((ι → A) ⧸ N) = ⊥) : primeLength (span {p}) ((ι → A) ⧸ N) = ⊤ := by
  classical
  have := Fintype.ofFinite ι
  refine top_le_iff.mp (ENat.forall_natCast_le_iff_le.mp fun n _ ↦ ?_)
  refine (primeLength_le_iff N hp n).mpr fun g hg ↦ ?_
  have : g = 0 := by simpa [h] using N.detIdeal_le_annihilator hg
  simp [this]

omit [DecidableEq ι] in
theorem primeLength_quotient_le (N : Submodule A (ι → A)) {p : A} (hp : Prime p) {a : A}
    (ha : a ∈ annihilator A ((ι → A) ⧸ N)) :
    primeLength (span {p}) ((ι → A) ⧸ N) ≤ emultiplicity p (a ^ Fintype.card ι) :=
  ENat.forall_natCast_le_iff_le.mp fun n hn ↦ by
    classical
    exact pow_dvd_iff_le_emultiplicity.mp
      ((primeLength_le_iff N hp n).mp hn _ (Submodule.pow_card_mem_detIdeal ha))

end Presentation

section Finite

variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
  {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]

omit [IsDomain A] [UniqueFactorizationMonoid A] in
theorem exists_linearEquiv_quotient :
    ∃ (n : ℕ) (N : Submodule A (Fin n → A)), Nonempty (M ≃ₗ[A] (Fin n → A) ⧸ N) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  exact ⟨n, LinearMap.ker f, ⟨(f.quotKerEquivOfSurjective hf).symm⟩⟩

theorem primeLength_eq_top {p : A} (hp : Prime p) (h : annihilator A M = ⊥) :
    primeLength (span {p}) M = ⊤ := by
  obtain ⟨n, N, ⟨e⟩⟩ := exists_linearEquiv_quotient (A := A) (M := M)
  rw [primeLength_congr e]
  exact primeLength_quotient_eq_top N hp (e.annihilator_eq ▸ h)

theorem exists_primeLength_le {p : A} (hp : Prime p) {a : A} (ha : a ∈ annihilator A M) :
    ∃ k : ℕ, primeLength (span {p}) M ≤ emultiplicity p (a ^ k) := by
  obtain ⟨n, N, ⟨e⟩⟩ := exists_linearEquiv_quotient (A := A) (M := M)
  rw [primeLength_congr e]
  exact ⟨_, primeLength_quotient_le N hp (e.annihilator_eq ▸ ha)⟩

/-- A torsion module has finite length at every prime. -/
theorem primeLength_ne_top {p : A} (hp : Prime p) (h : annihilator A M ≠ ⊥) :
    primeLength (span {p}) M ≠ ⊤ := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨k, hk⟩ := exists_primeLength_le hp ha
  exact (hk.trans_lt (emultiplicity_lt_top.mpr
    (FiniteMultiplicity.of_prime_left hp (pow_ne_zero k ha0)))).ne

/-- `M_(p) = 0` unless `p` divides every annihilator. -/
theorem primeLength_eq_zero {p : A} (hp : Prime p) {a : A} (ha : a ∈ annihilator A M)
    (hpa : ¬p ∣ a) : primeLength (span {p}) M = 0 := by
  obtain ⟨k, hk⟩ := exists_primeLength_le hp ha
  rwa [emultiplicity_eq_zero.mpr fun h ↦ hpa (hp.dvd_of_dvd_pow h), nonpos_iff_eq_zero] at hk

end Finite

section CharForm

variable (A : Type*) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
  (M : Type*) [AddCommGroup M] [Module A M]

open scoped Classical in
/-- **The characteristic form** `χ(M) = ∏_π π ^ ℓ(M_(π))` of Rémond (§3.1), over the prime
elements `π` up to association; `χ(M) = 0` if `M` is not torsion. It is defined up to a unit,
through a choice of representatives. -/
noncomputable def charForm : A :=
  if annihilator A M = ⊥ then 0 else
    ∏ᶠ q : Associates A,
      if Prime (Quot.out q) then Quot.out q ^ (primeLength (span {Quot.out q}) M).toNat else 1

variable {A M}

omit [IsDomain A] [UniqueFactorizationMonoid A] in
theorem charForm_of_annihilator_eq_bot (h : annihilator A M = ⊥) : charForm A M = 0 := by
  simp [charForm, h]

omit [IsDomain A] [UniqueFactorizationMonoid A] in
theorem charForm_congr {M' : Type*} [AddCommGroup M'] [Module A M'] (e : M ≃ₗ[A] M') :
    charForm A M = charForm A M' := by
  simp only [charForm, e.annihilator_eq, primeLength_congr e]

variable [Module.Finite A M]

open scoped Classical in
theorem mulSupport_charForm_subset {a : A} (ha : a ∈ annihilator A M) :
    Function.mulSupport (fun q : Associates A ↦
      if Prime (Quot.out q) then Quot.out q ^ (primeLength (span {Quot.out q}) M).toNat else 1) ⊆
      {q | q ∣ Associates.mk a} := by
  intro q hq
  by_contra hqa
  refine hq ?_
  by_cases hpr : Prime (Quot.out q)
  · have hdvd : ¬Quot.out q ∣ a := by
      rwa [← Associates.mk_dvd_mk, Associates.quot_out]
    simp [hpr, primeLength_eq_zero hpr ha hdvd]
  · simp [hpr]

omit [IsDomain A] in
theorem finite_setOf_dvd {a : A} (ha : a ≠ 0) : {q : Associates A | q ∣ Associates.mk a}.Finite :=
  have := UniqueFactorizationMonoid.fintypeSubtypeDvd _ (Associates.mk_ne_zero.mpr ha)
  Set.finite_coe_iff.mp (Finite.of_fintype {q // q ∣ Associates.mk a})

theorem charForm_ne_zero (h : annihilator A M ≠ ⊥) : charForm A M ≠ 0 := by
  classical
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  rw [charForm, ite_eq_right h, finprod_eq_prod_of_mulSupport_subset _
    (s := (finite_setOf_dvd ha0).toFinset) (by simpa using mulSupport_charForm_subset ha)]
  refine Finset.prod_ne_zero_iff.mpr fun q _ ↦ ?_
  split_ifs with hpr
  · exact pow_ne_zero _ hpr.ne_zero
  · exact one_ne_zero

theorem charForm_eq_zero_iff : charForm A M = 0 ↔ annihilator A M = ⊥ :=
  ⟨fun h ↦ by_contra fun h' ↦ charForm_ne_zero h' h, charForm_of_annihilator_eq_bot⟩

/-- **The multiplicity of a prime `p` in `χ(M)` is the length of `M_(p)`.** -/
theorem emultiplicity_charForm (h : annihilator A M ≠ ⊥) {p : A} (hp : Prime p) :
    emultiplicity p (charForm A M) = primeLength (span {p}) M := by
  classical
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  rw [charForm, ite_eq_right h, finprod_eq_prod_of_mulSupport_subset _
    (s := (finite_setOf_dvd ha0).toFinset) (by simpa using mulSupport_charForm_subset ha),
    Finset.emultiplicity_prod hp]
  have hassoc : Associated (Quot.out (Associates.mk p)) p := Associates.mk_quot_out p
  have hpr : Prime (Quot.out (Associates.mk p)) := hassoc.symm.prime hp
  have hspan : span {Quot.out (Associates.mk p)} = span {p} :=
    span_singleton_eq_span_singleton.mpr hassoc
  have h1 : emultiplicity p p = 1 := by simpa using emultiplicity_pow_self_of_prime hp 1
  rw [Finset.sum_eq_single (Associates.mk p)]
  · rw [ite_eq_left hpr, emultiplicity_pow hp, emultiplicity_eq_of_associated_right hassoc, h1,
      hspan, mul_one,
      ENat.natCast_toNat (primeLength_ne_top hp h)]
  · intro q _ hq
    split_ifs with hq'
    · rw [emultiplicity_pow hp, emultiplicity_eq_zero.mpr, mul_zero]
      intro hdvd
      exact hq (by rw [← Associates.quot_out q,
        Associates.mk_eq_mk_iff_associated.mpr (hp.associated_of_dvd hq' hdvd)])
    · exact emultiplicity_of_one_right hp.not_isUnit
  · intro hp'
    have hpa : ¬p ∣ a := fun hpa ↦ hp' (by simpa using Associates.mk_dvd_mk.mpr hpa)
    rw [ite_eq_left hpr, hspan, primeLength_eq_zero hp ha hpa, ENat.toNat_zero, pow_zero,
      emultiplicity_of_one_right hp.not_isUnit]

/-- `χ(M)` is a unit when every prime avoids some annihilator. -/
theorem isUnit_charForm (h : annihilator A M ≠ ⊥)
    (hπ : ∀ π : A, Prime π → ∃ a ∈ annihilator A M, ¬π ∣ a) : IsUnit (charForm A M) := by
  refine isUnit_of_dvd_one ((UniqueFactorizationMonoid.dvd_iff_emultiplicity_le
    (charForm_ne_zero h)).mpr fun π hp ↦ ?_)
  obtain ⟨a, ha, hπa⟩ := hπ π hp
  rw [emultiplicity_charForm h hp, primeLength_eq_zero hp ha hπa]
  exact zero_le

theorem isUnit_charForm_of_subsingleton [Subsingleton M] : IsUnit (charForm A M) := by
  have htop : annihilator A M = ⊤ := by
    rw [eq_top_iff]
    exact fun a _ ↦ Module.mem_annihilator.mpr fun m ↦ Subsingleton.elim _ _
  exact isUnit_charForm (by simp [htop]) fun π hπ ↦ ⟨1, htop ▸ trivial, hπ.not_dvd_one⟩

/-- **`χ` is multiplicative in short exact sequences** (up to a unit). -/
theorem associated_charForm_of_exact {N Q : Type*} [AddCommGroup N] [Module A N]
    [Module.Finite A N] [AddCommGroup Q] [Module A Q] (f : N →ₗ[A] M) (g : M →ₗ[A] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    Associated (charForm A M) (charForm A N * charForm A Q) := by
  have : Module.Finite A Q := Module.Finite.of_surjective g hg
  by_cases hM : annihilator A M = ⊥
  · have : annihilator A N = ⊥ ∨ annihilator A Q = ⊥ := by
      by_contra! hc
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc.1
      obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc.2
      refine mul_ne_zero ha0 hb0 (hM ▸ Module.mem_annihilator.mpr fun m ↦ ?_ : a * b ∈ ⊥)
      obtain ⟨n, hn⟩ := (H (b • m)).mp (by rw [map_smul, Module.mem_annihilator.mp hb])
      rw [mul_smul, ← hn, ← map_smul, Module.mem_annihilator.mp ha, map_zero]
    rcases this with h | h <;> simp [charForm_of_annihilator_eq_bot hM,
      charForm_of_annihilator_eq_bot h]
  have hN : annihilator A N ≠ ⊥ := ne_bot_of_le_ne_bot hM (f.annihilator_le_of_injective hf)
  have hQ : annihilator A Q ≠ ⊥ := ne_bot_of_le_ne_bot hM (g.annihilator_le_of_surjective hg)
  have key : ∀ p : A, Prime p → emultiplicity p (charForm A M) =
      emultiplicity p (charForm A N * charForm A Q) := fun p hp ↦ by
    rw [emultiplicity_mul hp, emultiplicity_charForm hM hp, emultiplicity_charForm hN hp,
      emultiplicity_charForm hQ hp, primeLength_eq_add f g hf hg H]
  refine associated_of_dvd_dvd ?_ ?_
  · exact (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le (charForm_ne_zero hM)).mpr
      fun p hp ↦ (key p hp).le
  · exact (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le
      (mul_ne_zero (charForm_ne_zero hN) (charForm_ne_zero hQ))).mpr fun p hp ↦ (key p hp).ge


/-- **`χ` of a quotient divides `χ`**, for finite modules over a Noetherian ring. -/
theorem charForm_dvd_of_surjective [IsNoetherianRing A] {Q : Type*} [AddCommGroup Q]
    [Module A Q] (g : M →ₗ[A] Q) (hg : Function.Surjective g) : charForm A Q ∣ charForm A M := by
  have := associated_charForm_of_exact (LinearMap.ker g).subtype g Subtype.val_injective hg
    (LinearMap.exact_subtype_ker_map g)
  exact (Dvd.intro_left _ rfl).trans this.symm.dvd

end CharForm

section Gcd

variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {N : Submodule A (ι → A)}

/-- `χ` divides every maximal minor of a presentation. -/
theorem charForm_dvd_of_mem_detIdeal {g : A} (hg : g ∈ N.detIdeal) :
    charForm A ((ι → A) ⧸ N) ∣ g := by
  by_cases hM : annihilator A ((ι → A) ⧸ N) = ⊥
  · have : g = 0 := by simpa [hM] using N.detIdeal_le_annihilator hg
    simp [this]
  refine (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le (charForm_ne_zero hM)).mpr
    fun p hp ↦ ?_
  rw [emultiplicity_charForm hM hp]
  exact ENat.forall_natCast_le_iff_le.mp fun n hn ↦
    pow_dvd_iff_le_emultiplicity.mp ((primeLength_le_iff N hp n).mp hn g hg)

/-- **`χ` is the greatest common divisor of the maximal minors of a presentation.** -/
theorem dvd_charForm_of_forall {c : A} (h : ∀ g ∈ N.detIdeal, c ∣ g) :
    c ∣ charForm A ((ι → A) ⧸ N) := by
  by_cases hM : annihilator A ((ι → A) ⧸ N) = ⊥
  · simp [charForm_of_annihilator_eq_bot hM]
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
  have hc : c ≠ 0 := by
    rintro rfl
    exact pow_ne_zero _ ha0 (zero_dvd_iff.mp (h _ (Submodule.pow_card_mem_detIdeal ha)))
  refine (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hc).mpr fun p hp ↦ ?_
  rw [emultiplicity_charForm hM hp,
    (FiniteMultiplicity.of_prime_left hp hc).emultiplicity_eq_multiplicity]
  exact (primeLength_le_iff N hp _).mpr fun g hg ↦ (pow_multiplicity_dvd p c).trans (h g hg)

omit [Fintype ι] [DecidableEq ι] in
/-- **`χ` divides a power of every annihilator.** -/
theorem exists_charForm_dvd_pow {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {a : A} (ha : a ∈ annihilator A M) : ∃ k : ℕ, charForm A M ∣ a ^ k := by
  obtain ⟨n, N, ⟨e⟩⟩ := exists_linearEquiv_quotient (A := A) (M := M)
  rw [charForm_congr e]
  exact ⟨_, charForm_dvd_of_mem_detIdeal (Submodule.pow_card_mem_detIdeal (e.annihilator_eq ▸ ha))⟩

end Gcd

section Square

variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For the rows of a square matrix, `χ` of the cokernel is the determinant. -/
theorem associated_charForm_quotient_span_range (v : ι → ι → A) :
    Associated (charForm A ((ι → A) ⧸ Submodule.span A (Set.range v))) (Matrix.of v).det :=
  associated_of_dvd_dvd
    (charForm_dvd_of_mem_detIdeal (Submodule.det_mem_detIdeal fun j ↦
      Submodule.subset_span ⟨j, rfl⟩))
    (dvd_charForm_of_forall fun g hg ↦ by
      rwa [Submodule.detIdeal_span_range, mem_span_singleton] at hg)

/-- **`χ` of the cokernel of a map of free modules of the same rank is its determinant.** -/
theorem associated_charForm_quotient_range {F F' : Type*} [AddCommGroup F] [Module A F]
    [AddCommGroup F'] [Module A F'] (bF : Basis ι A F) (bF' : Basis ι A F')
    (φ : F →ₗ[A] F') :
    Associated (charForm A (F' ⧸ LinearMap.range φ)) (LinearMap.toMatrix bF bF' φ).det := by
  have hrange : (LinearMap.range φ).map (bF'.equivFun : F' →ₗ[A] ι → A) =
      Submodule.span A (Set.range fun j ↦ bF'.equivFun (φ (bF j))) := by
    rw [LinearMap.range_eq_map, ← bF.span_eq, Submodule.map_span, Submodule.map_span,
      ← Set.range_comp, ← Set.range_comp]
    rfl
  rw [charForm_congr (Submodule.Quotient.equiv _ _ bF'.equivFun hrange)]
  refine (associated_charForm_quotient_span_range _).trans (Associated.of_eq ?_)
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply]

end Square

section Localization

variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
  {A' : Type*} [CommRing A'] [IsDomain A'] [UniqueFactorizationMonoid A'] [Algebra A A']
  (S : Submonoid A) [IsLocalization S A']

include S in
omit [UniqueFactorizationMonoid A] [IsDomain A'] [UniqueFactorizationMonoid A'] in
/-- `p ^ n ∣ g` can be tested in a localization at a submonoid prime to `p`. -/
theorem _root_.IsLocalization.pow_dvd_algebraMap_iff {p : A} (hp : Prime p)
    (hpS : ∀ s ∈ S, ¬p ∣ s) (g : A) (n : ℕ) :
    algebraMap A A' p ^ n ∣ algebraMap A A' g ↔ p ^ n ∣ g := by
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun h ↦ by simpa [map_pow] using map_dvd (algebraMap A A') h⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S y
  have h' : algebraMap A A' (g * s) = algebraMap A A' (p ^ n * a) := by
    rw [map_mul, hy, map_mul, map_pow, mul_assoc, IsLocalization.mk'_spec]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists S A').mp h'
  refine hp.pow_dvd_of_dvd_mul_left n (hpS _ (S.mul_mem c.2 s.2)) ⟨c * a, ?_⟩
  linear_combination hc

include S in
omit [IsDomain A] [UniqueFactorizationMonoid A] [IsDomain A'] [UniqueFactorizationMonoid A'] in
/-- A prime prime to the submonoid stays prime in the localization. -/
theorem _root_.IsLocalization.prime_algebraMap (hS : S ≤ nonZeroDivisors A) {p : A}
    (hp : Prime p) (hpS : ∀ s ∈ S, ¬p ∣ s) : Prime (algebraMap A A' p) := by
  have hprime : (span {p}).IsPrime := (span_singleton_prime hp.ne_zero).mpr hp
  have hdisj : Disjoint (S : Set A) (span {p}) :=
    Set.disjoint_left.mpr fun s hs hsp ↦ hpS s hs (mem_span_singleton.mp hsp)
  have := IsLocalization.isPrime_of_isPrime_disjoint S A' _ hprime hdisj
  rw [Ideal.map_span, Set.image_singleton] at this
  refine (span_singleton_prime ?_).mp this
  exact (map_ne_zero_iff _ (IsLocalization.injective A' hS)).mpr hp.ne_zero

include S in
omit [IsDomain A] [UniqueFactorizationMonoid A'] in
/-- Every prime of the localization is, up to a unit, the image of a prime of `A` prime to the
submonoid. -/
theorem _root_.IsLocalization.exists_associated_algebraMap (hS : S ≤ nonZeroDivisors A)
    {p' : A'} (hp' : Prime p') :
    ∃ p : A, Prime p ∧ (∀ s ∈ S, ¬p ∣ s) ∧ Associated (algebraMap A A' p) p' := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S p'
  have hassoc : Associated (IsLocalization.mk' A' a s) (algebraMap A A' a) := by
    rw [← IsLocalization.mk'_spec A' a s]
    exact associated_mul_unit_right _ _ (IsLocalization.map_units A' s)
  have hq := hassoc.prime hp'
  have ha : a ≠ 0 := by
    rintro rfl
    exact hq.ne_zero (map_zero _)
  have hdvd : algebraMap A A' a ∣
      ((UniqueFactorizationMonoid.factors a).map (algebraMap A A')).prod := by
    rw [← map_multiset_prod]
    exact ((UniqueFactorizationMonoid.factors_prod ha).map (algebraMap A A')).symm.dvd
  obtain ⟨p, hpf, hpd⟩ := hq.exists_mem_multiset_map_dvd hdvd
  have hp := UniqueFactorizationMonoid.prime_of_factor p hpf
  have hpS : ∀ s ∈ S, ¬p ∣ s := fun t ht hpt ↦ hq.not_isUnit (isUnit_of_dvd_unit
    (hpd.trans (map_dvd _ hpt)) (IsLocalization.map_units A' ⟨t, ht⟩))
  exact ⟨p, hp, hpS, (hassoc.trans (hq.associated_of_dvd
    (IsLocalization.prime_algebraMap S hS hp hpS) hpd)).symm⟩

include S in
/-- **`χ` commutes with localization**, for a presentation. -/
theorem associated_charForm_quotient_map (hS : S ≤ nonZeroDivisors A) {ι : Type*} [Finite ι]
    (N : Submodule A (ι → A)) (h : annihilator A ((ι → A) ⧸ N) ≠ ⊥) :
    Associated (charForm A' ((ι → A') ⧸
        Submodule.span A' ((fun w ↦ algebraMap A A' ∘ w) '' (N : Set (ι → A)))))
      (algebraMap A A' (charForm A ((ι → A) ⧸ N))) := by
  classical
  have := Fintype.ofFinite ι
  set ρ := algebraMap A A'
  set N' := Submodule.span A' ((fun w ↦ ρ ∘ w) '' (N : Set (ι → A)))
  have hinj : Function.Injective ρ := IsLocalization.injective A' hS
  have hD : N'.detIdeal = N.detIdeal.map ρ := Submodule.detIdeal_span_image ρ N
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have h' : annihilator A' ((ι → A') ⧸ N') ≠ ⊥ := by
    refine ne_bot_of_le_ne_bot (fun h0 ↦ ?_) N'.detIdeal_le_annihilator
    have := Ideal.mem_map_of_mem ρ (Submodule.pow_card_mem_detIdeal ha)
    rw [← hD, h0, Ideal.mem_bot] at this
    exact pow_ne_zero _ ha0 ((map_eq_zero_iff ρ hinj).mp this)
  have hlen : ∀ p : A, Prime p → (∀ s ∈ S, ¬p ∣ s) →
      primeLength (span {ρ p}) ((ι → A') ⧸ N') = primeLength (span {p}) ((ι → A) ⧸ N) := by
    intro p hp hpS
    refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ?_
    rw [primeLength_le_iff N' (IsLocalization.prime_algebraMap S hS hp hpS) n,
      primeLength_le_iff N hp n, hD]
    refine ⟨fun H g hg ↦ (IsLocalization.pow_dvd_algebraMap_iff S hp hpS g n).mp
      (H _ (Ideal.mem_map_of_mem ρ hg)), fun H g' hg' ↦ ?_⟩
    have : N.detIdeal.map ρ ≤ span {ρ p ^ n} := Ideal.map_le_iff_le_comap.mpr fun g hg ↦ by
      rw [Ideal.mem_comap, mem_span_singleton]
      simpa [map_pow] using map_dvd ρ (H g hg)
    exact mem_span_singleton.mp (this hg')
  have key : ∀ p' : A', Prime p' → emultiplicity p' (charForm A' ((ι → A') ⧸ N')) =
      emultiplicity p' (ρ (charForm A ((ι → A) ⧸ N))) := by
    intro p' hp'
    obtain ⟨p, hp, hpS, hassoc⟩ := IsLocalization.exists_associated_algebraMap S hS hp'
    rw [emultiplicity_eq_of_associated_left hassoc, emultiplicity_eq_of_associated_left hassoc,
      emultiplicity_charForm h' (IsLocalization.prime_algebraMap S hS hp hpS), hlen p hp hpS,
      ← emultiplicity_charForm h hp]
    exact (emultiplicity_eq_emultiplicity_iff.mpr fun n ↦
      IsLocalization.pow_dvd_algebraMap_iff S hp hpS _ n).symm
  have hχ : ρ (charForm A ((ι → A) ⧸ N)) ≠ 0 := (map_ne_zero_iff ρ hinj).mpr (charForm_ne_zero h)
  exact associated_of_dvd_dvd
    ((UniqueFactorizationMonoid.dvd_iff_emultiplicity_le (charForm_ne_zero h')).mpr
      fun p' hp' ↦ (key p' hp').le)
    ((UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hχ).mpr fun p' hp' ↦ (key p' hp').ge)

include S in
/-- **`χ` commutes with localization**: for a base change `M → M'` along a localization
`A → A' = S⁻¹A` of factorial rings and a finite torsion module `M`, `χ(M') = χ(M)` up to a
unit of `A'`. -/
theorem associated_charForm_of_isBaseChange (hS : S ≤ nonZeroDivisors A) {M M' : Type*}
    [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup M'] [Module A M']
    [Module A' M'] [IsScalarTower A A' M'] {f : M →ₗ[A] M'} (hf : IsBaseChange A' f)
    (h : annihilator A M ≠ ⊥) :
    Associated (charForm A' M') (algebraMap A A' (charForm A M)) := by
  obtain ⟨n, N, ⟨e⟩⟩ := exists_linearEquiv_quotient (A := A) (M := M)
  have hq := (IsBaseChange.finitePow (Fin n) (IsBaseChange.linearMap A A')).quotient N
  let e' := hf.equiv.symm ≪≫ₗ LinearEquiv.baseChange A A' _ _ e ≪≫ₗ hq.equiv
  rw [charForm_congr e', charForm_congr e]
  exact associated_charForm_quotient_map S hS N (e.annihilator_eq ▸ h)

end Localization

section BaseChange

variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
  {A' : Type*} [CommRing A'] [IsDomain A'] [UniqueFactorizationMonoid A']

/-- **`χ` divides under any base change**, for a presentation: `ρ(χ(M)) ∣ χ(M ⊗ A')`. -/
theorem map_charForm_dvd_quotient_map (ρ : A →+* A') {ι : Type*} [Finite ι]
    (N : Submodule A (ι → A)) :
    ρ (charForm A ((ι → A) ⧸ N)) ∣
      charForm A' ((ι → A') ⧸ Submodule.span A' ((fun w ↦ ρ ∘ w) '' (N : Set (ι → A)))) := by
  classical
  have := Fintype.ofFinite ι
  refine dvd_charForm_of_forall fun g hg ↦ ?_
  rw [Submodule.detIdeal_span_image] at hg
  have hle : N.detIdeal.map ρ ≤ span {ρ (charForm A ((ι → A) ⧸ N))} :=
    Ideal.map_le_iff_le_comap.mpr fun g hg ↦ by
      rw [Ideal.mem_comap, mem_span_singleton]
      exact map_dvd ρ (charForm_dvd_of_mem_detIdeal hg)
  exact mem_span_singleton.mp (hle hg)

/-- **`χ` divides under any base change**: for a base change `M → M'` along `A → A'` of
factorial domains and a finite `A`-module `M`, `χ(M) ∣ χ(M')` in `A'`. -/
theorem algebraMap_charForm_dvd_of_isBaseChange [Algebra A A'] {M M' : Type*}
    [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup M'] [Module A M']
    [Module A' M'] [IsScalarTower A A' M'] {f : M →ₗ[A] M'} (hf : IsBaseChange A' f) :
    algebraMap A A' (charForm A M) ∣ charForm A' M' := by
  obtain ⟨n, N, ⟨e⟩⟩ := exists_linearEquiv_quotient (A := A) (M := M)
  have hq := (IsBaseChange.finitePow (Fin n) (IsBaseChange.linearMap A A')).quotient N
  let e' := hf.equiv.symm ≪≫ₗ LinearEquiv.baseChange A A' _ _ e ≪≫ₗ hq.equiv
  rw [charForm_congr e', charForm_congr e]
  exact map_charForm_dvd_quotient_map (algebraMap A A') N

/-- **`χ` commutes with extensions that keep divisors**: if `ρ : A → A'` has a retraction and
every divisor of `ρ(a)`, `a ≠ 0`, lies in the image of `ρ` (e.g. adjoining variables), then
`χ(M ⊗ A') = ρ(χ(M))` up to a unit, for a presentation. -/
theorem associated_charForm_quotient_map_of_retraction (ρ : A →+* A') (r : A' →+* A)
    (hr : ∀ a, r (ρ a) = a) (hcl : ∀ a : A, a ≠ 0 → ∀ c' : A', c' ∣ ρ a → ∃ c, c' = ρ c)
    {ι : Type*} [Finite ι] (N : Submodule A (ι → A)) :
    Associated
      (charForm A' ((ι → A') ⧸ Submodule.span A' ((fun w ↦ ρ ∘ w) '' (N : Set (ι → A)))))
      (ρ (charForm A ((ι → A) ⧸ N))) := by
  classical
  have := Fintype.ofFinite ι
  set N' := Submodule.span A' ((fun w ↦ ρ ∘ w) '' (N : Set (ι → A)))
  have hD : N'.detIdeal = N.detIdeal.map ρ := Submodule.detIdeal_span_image ρ N
  have hdvd := map_charForm_dvd_quotient_map ρ N
  by_cases h0 : charForm A ((ι → A) ⧸ N) = 0
  · rw [h0, map_zero] at hdvd ⊢
    rw [zero_dvd_iff.mp hdvd]
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (mt charForm_eq_zero_iff.mpr h0)
  have hg0 := Submodule.pow_card_mem_detIdeal ha
  obtain ⟨c, hc⟩ := hcl _ (pow_ne_zero _ ha0) _ (charForm_dvd_of_mem_detIdeal
    (hD ▸ Ideal.mem_map_of_mem ρ hg0))
  have hcN : ∀ g ∈ N.detIdeal, c ∣ g := fun g hg ↦ by
    obtain ⟨q, hq⟩ : ρ c ∣ ρ g := hc ▸ charForm_dvd_of_mem_detIdeal (hD ▸ Ideal.mem_map_of_mem ρ hg)
    exact ⟨r q, by rw [← hr g, hq, map_mul, hr]⟩
  rw [hc] at hdvd ⊢
  exact associated_of_dvd_dvd (map_dvd ρ (dvd_charForm_of_forall hcN)) hdvd

/-- **`χ` commutes with extensions that keep divisors** (see
`associated_charForm_quotient_map_of_retraction`), for any base change. -/
theorem associated_charForm_of_isBaseChange_of_retraction [Algebra A A'] (r : A' →+* A)
    (hr : ∀ a, r (algebraMap A A' a) = a)
    (hcl : ∀ a : A, a ≠ 0 → ∀ c' : A', c' ∣ algebraMap A A' a → ∃ c, c' = algebraMap A A' c)
    {M M' : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup M']
    [Module A M'] [Module A' M'] [IsScalarTower A A' M'] {f : M →ₗ[A] M'}
    (hf : IsBaseChange A' f) :
    Associated (charForm A' M') (algebraMap A A' (charForm A M)) := by
  obtain ⟨n, N, ⟨e⟩⟩ := exists_linearEquiv_quotient (A := A) (M := M)
  have hq := (IsBaseChange.finitePow (Fin n) (IsBaseChange.linearMap A A')).quotient N
  let e' := hf.equiv.symm ≪≫ₗ LinearEquiv.baseChange A A' _ _ e ≪≫ₗ hq.equiv
  rw [charForm_congr e', charForm_congr e]
  exact associated_charForm_quotient_map_of_retraction _ r hr hcl N

end BaseChange

end Module
