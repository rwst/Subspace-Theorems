/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

-- Used only inside proofs.
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.Basic
import STForMathlib.RingTheory.MvPolynomial.ExcessBezout
import STForMathlib.RingTheory.MvPolynomial.HomogeneousRegular

/-!
# Generic linear forms

Cutting by a generic linear form lowers the dimension by one, in two senses, with no catenarity:

* **height**: if `ρ` avoids the minimal primes of `I` that do not contain all the variables `X_v`,
  `v ∈ V`, then `ht (I + (ρ)) ≥ min (ht I + 1, |V|)`, since every prime containing the `X_v` has
  height `≥ |V|`;
* **dimension at the origin**: `originDim J`, the Krull dimension of `K[X]_𝔪 / J` with
  `𝔪 = ker constantCoeff`, drops by one when `ρ` avoids the minimal primes of `J K[X]_𝔪`, by
  Mathlib's `Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes`. It is at most the
  number of elements of `𝔪` that make `J` primary to `𝔪` (Krull), and for a homogeneous `J` it is
  `≤ 0` exactly when every variable has a power in `J`.

Over an infinite field one linear form in the span of the `X_v` does both for finitely many ideals
at once (`MvPolynomial.exists_mem_span_forall`), by prime avoidance in a vector space
(`MvPolynomial.exists_mem_span_forall_notMem`). This is the padding of Corvaja–Zannier 2004,
proof of Theorem 2: `fᵢ ρᵢ^(δ - δᵢ)` with "hyperplanes `ρᵢ = 0` in general position".

Iterated, this gives `m` linear forms raising a height by `m`
(`MvPolynomial.exists_le_height_sup_span_range`), and the padding of a family of forms of the
right height by linear forms, `fⱼ ρⱼ^{aⱼ}`, keeping the height for every `a`
(`MvPolynomial.exists_le_height_span_mul_pow`).

Also here: a sequence of nonzerodivisors modulo the earlier terms generates an ideal of height
at least its length (`Ideal.natCast_le_height_span_range_of_colon_eq`), so subfamilies of a
homogeneous family of the right height have the right height
(`MvPolynomial.card_le_height_span_image`); heights compare through the primes containing an
ideal (`Ideal.height_le_height_of_forall_isPrime`), so a generator may be replaced by a power
(`Ideal.height_span_insert_pow`).

## Main statements

* `Ideal.natCast_le_height_span_range_of_colon_eq`: regular sequences have height `≥` length.
* `MvPolynomial.card_le_height_span_image`: subfamilies of forms of height `|C|`.
* `MvPolynomial.ncard_le_height_of_image_X_subset`: primes containing `X_v`, `v ∈ V`, have height
  `≥ |V|`.
* `MvPolynomial.two_le_height_span_pair`: `ht (G, p) ≥ 2` for `G` prime and `p ∉ (G)`.
* `MvPolynomial.constantCoeff_eq_zero_of_mem`: homogeneous proper ideals lie in `𝔪`.
* `MvPolynomial.originDim_le_card`, `MvPolynomial.pow_mem_of_originDim_nonpos`: the dimension at
  the origin and primary ideals.
* `MvPolynomial.exists_mem_span_forall`: **the generic linear form**.
* `MvPolynomial.exists_le_height_sup_span_range`, `MvPolynomial.exists_le_height_span_mul_pow`:
  generic linear forms added, and padding.
* `MvPolynomial.height_span_le_ncard_of_isHomogeneous`: Krull's bound for forms.
-/

@[expose] public section

open Finset

namespace Ideal

variable {R : Type*} [CommRing R]

/-- **Regular sequences have height at least their length.** If each `φ j` is a nonzerodivisor
modulo `(φ i | i < j)`, then `(φ)` has height `≥ m`. -/
theorem natCast_le_height_span_range_of_colon_eq : ∀ {m : ℕ} {φ : Fin m → R},
    (∀ j, (Ideal.span (φ '' Set.Iio j)).colon {φ j} = Ideal.span (φ '' Set.Iio j)) →
    (m : ℕ∞) ≤ (Ideal.span (Set.range φ)).height
  | 0, _, _ => by simp
  | m + 1, φ, hc => by
    have hinit : ∀ j : Fin m, φ '' Set.Iio j.castSucc = Fin.init φ '' Set.Iio j := fun j ↦ by
      ext x
      simp only [Set.mem_image, Set.mem_Iio]
      constructor
      · rintro ⟨i, hi, rfl⟩
        have hi' : (i : ℕ) < m := by
          have := j.isLt
          rw [Fin.lt_def, Fin.val_castSucc] at hi
          omega
        exact ⟨⟨i, hi'⟩, by rw [Fin.lt_def] at hi ⊢; exact hi, by simp [Fin.init]⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i.castSucc, Fin.castSucc_lt_castSucc_iff.mpr hi, rfl⟩
    have IH := natCast_le_height_span_range_of_colon_eq (φ := Fin.init φ) fun j ↦ by
      rw [← hinit]
      exact hc j.castSucc
    set I := Ideal.span (Set.range (Fin.init φ))
    have hlast : Ideal.span (φ '' Set.Iio (Fin.last m)) = I := by
      congr 1
      ext x
      simp only [Set.mem_image, Set.mem_Iio, Set.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, by simp [Fin.init]⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i.castSucc, Fin.castSucc_lt_last i, rfl⟩
    have hreg := hc (Fin.last m)
    rw [hlast] at hreg
    have hrange : Ideal.span (Set.range φ) = I ⊔ Ideal.span {φ (Fin.last m)} := by
      have : Set.range φ = insert (φ (Fin.last m)) (Set.range (Fin.init φ)) := by
        rw [← Fin.range_snoc, Fin.snoc_init_self]
      rw [this, Ideal.span_insert, sup_comm]
    rw [hrange, Ideal.height_eq_inf_minimalPrimes]
    refine le_iInf₂ fun Q hQ ↦ ?_
    have := hQ.1.1
    obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hQ.1.2)
    have := hP.1.1
    have hnot : φ (Fin.last m) ∉ P := fun hx ↦ by
      obtain ⟨y, hy, hxy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hP hx
      exact hy (hreg ▸ Submodule.mem_colon_singleton.mpr (by rw [smul_eq_mul, mul_comm]; exact hxy))
    have hlt : P < Q := lt_of_le_of_ne hPQ fun h ↦
      hnot (h ▸ hQ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    calc ((m + 1 : ℕ) : ℕ∞) = (m : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ P.height + 1 := by gcongr; exact IH.trans (Ideal.height_mono hP.1.2)
      _ ≤ Q.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt

/-- **Heights compare through primes**: if every prime containing `J` contains `I`, then
`ht I ≤ ht J`. -/
theorem height_le_height_of_forall_isPrime {I J : Ideal R}
    (h : ∀ Q : Ideal R, Q.IsPrime → J ≤ Q → I ≤ Q) : I.height ≤ J.height := by
  rw [J.height_eq_inf_minimalPrimes]
  exact le_iInf₂ fun Q hQ ↦ Ideal.height_mono (h Q hQ.1.1 hQ.1.2)

/-- A generator and a positive power of it give ideals of the same height. -/
theorem height_span_insert_pow {x : R} {n : ℕ} (hn : 0 < n) (s : Set R) :
    (Ideal.span (insert (x ^ n) s)).height = (Ideal.span (insert x s)).height := by
  refine le_antisymm (Ideal.height_mono (Ideal.span_le.mpr ?_))
    (height_le_height_of_forall_isPrime fun Q hQ hle ↦ Ideal.span_le.mpr ?_)
  · rintro _ (rfl | hr)
    · exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_insert _ _)) _ hn
    · exact Ideal.subset_span (Set.mem_insert_of_mem _ hr)
  · rintro _ (rfl | hr)
    · exact hQ.mem_of_pow_mem n (hle (Ideal.subset_span (Set.mem_insert _ _)))
    · exact hle (Ideal.subset_span (Set.mem_insert_of_mem _ hr))

end Ideal

namespace MvPolynomial

variable {τ K : Type*} [Field K]

section Heights

variable [Finite τ]

/-- **The head of a family of forms of the right height has the right height.** If homogeneous
`g₀, …, g_{s-1}, h₀, …, h_{t-1}` generate an ideal of height `s + t`, then `(g)` has height
`≥ s`. -/
theorem le_height_span_range_of_height_append_eq {s t : ℕ} {g : Fin s → MvPolynomial τ K}
    {h : Fin t → MvPolynomial τ K} (hg : ∀ j, ∃ n, (g j).IsHomogeneous n)
    (hh : ∀ j, ∃ n, (h j).IsHomogeneous n)
    (hht : (Ideal.span (Set.range (Fin.append g h))).height = (s + t : ℕ)) :
    (s : ℕ∞) ≤ (Ideal.span (Set.range g)).height := by
  have hφ : ∀ j, ∃ n, (Fin.append g h j).IsHomogeneous n := fun j ↦ by
    induction j using Fin.addCases with
    | left l => simpa using hg l
    | right l => simpa using hh l
  refine Ideal.natCast_le_height_span_range_of_colon_eq fun j ↦ ?_
  have hc := colon_eq_of_height_eq hφ hht (Fin.castAdd t j)
  have himg : Fin.append g h '' Set.Iio (Fin.castAdd t j) = g '' Set.Iio j := by
    ext x
    simp only [Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨l, hl, rfl⟩
      induction l using Fin.addCases with
      | left l => exact ⟨l, by rw [Fin.lt_def] at hl ⊢; simpa using hl, by simp⟩
      | right l =>
        rw [Fin.lt_def] at hl
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hl
        omega
    · rintro ⟨l, hl, rfl⟩
      exact ⟨Fin.castAdd t l, by rw [Fin.lt_def] at hl ⊢; simpa using hl, by simp⟩
  rwa [himg, Fin.append_left] at hc

/-- **Subfamilies of forms of the right height have the right height.** If homogeneous `u i`,
`i ∈ C`, generate an ideal of height `|C|`, then for `A ⊆ C` the `u i`, `i ∈ A`, generate an ideal
of height `≥ |A|`. -/
theorem card_le_height_span_image {ι : Type*} {u : ι → MvPolynomial τ K}
    (hu : ∀ i, ∃ n, (u i).IsHomogeneous n) {A C : Finset ι} (hAC : A ⊆ C)
    (hC : (Ideal.span (u '' C)).height = C.card) :
    (A.card : ℕ∞) ≤ (Ideal.span (u '' A)).height := by
  classical
  set D := C \ A
  set g : Fin A.card → MvPolynomial τ K := fun i ↦ u (A.equivFin.symm i)
  set h : Fin D.card → MvPolynomial τ K := fun i ↦ u (D.equivFin.symm i)
  have hrg : Set.range g = u '' A := by
    ext x
    simp only [Set.mem_range, Set.mem_image, g]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, (A.equivFin.symm i).2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨A.equivFin ⟨a, ha⟩, by simp⟩
  have hrh : Set.range h = u '' D := by
    ext x
    simp only [Set.mem_range, Set.mem_image, h]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, (D.equivFin.symm i).2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨D.equivFin ⟨a, ha⟩, by simp⟩
  have hcard : A.card + D.card = C.card := by
    rw [add_comm]
    exact card_sdiff_add_card_eq_card hAC
  have hrange : Set.range (Fin.append g h) = u '' C := by
    rw [range_append, hrg, hrh, ← Set.image_union, ← coe_union, union_sdiff_of_subset hAC]
  rw [← hrg]
  exact le_height_span_range_of_height_append_eq (fun j ↦ hu _) (fun j ↦ hu _)
    (by rw [hrange, hC, hcard])

/-- **Primes containing `|V|` variables have height `≥ |V|`.** -/
theorem ncard_le_height_of_image_X_subset (V : Set τ) {P : Ideal (MvPolynomial τ K)}
    (hP : (X '' V : Set (MvPolynomial τ K)) ⊆ P) : (V.ncard : ℕ∞) ≤ P.height := by
  classical
  have := Fintype.ofFinite τ
  set S := V.toFinset
  set φ : Fin S.card → MvPolynomial τ K := fun i ↦ X (S.equivFin.symm i)
  have hrange : Set.range φ = X '' V := by
    ext x
    simp only [Set.mem_range, Set.mem_image, φ]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, Set.mem_toFinset.mp (S.equivFin.symm i).2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨S.equivFin ⟨a, by simpa [S] using ha⟩, by simp⟩
  have hreg : ∀ j, (Ideal.span (φ '' Set.Iio j)).colon {φ j} = Ideal.span (φ '' Set.Iio j) := by
    intro j
    refine le_antisymm (fun y hy ↦ ?_) fun y hy ↦
      Submodule.mem_colon_singleton.mpr (by rw [smul_eq_mul]; exact Ideal.mul_mem_right _ _ hy)
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hy
    set A : Set τ := (fun i ↦ (S.equivFin.symm i : τ)) '' Set.Iio j
    have himg : φ '' Set.Iio j = X '' A := by
      rw [Set.image_image]
    have hv : (S.equivFin.symm j : τ) ∉ A := by
      rintro ⟨i, hi, heq⟩
      have := S.equivFin.symm.injective (Subtype.ext heq)
      subst this
      exact lt_irrefl _ (Set.mem_Iio.mp hi)
    rw [himg, mem_ideal_span_X_image] at hy ⊢
    intro m hm
    obtain ⟨i, hiA, hi⟩ := hy (Finsupp.single (S.equivFin.symm j : τ) 1 + m) (by
      rw [mul_comm, support_X_mul]
      exact Finset.mem_map_of_mem _ hm)
    refine ⟨i, hiA, fun h0 ↦ hi ?_⟩
    have hne : (S.equivFin.symm j : τ) ≠ i := fun h ↦ hv (h ▸ hiA)
    simp [h0, hne]
  have h1 := Ideal.natCast_le_height_span_range_of_colon_eq hreg
  rw [hrange] at h1
  calc (V.ncard : ℕ∞) = S.card := by rw [Set.ncard_eq_toFinset_card']
    _ ≤ _ := h1
    _ ≤ P.height := Ideal.height_mono (Ideal.span_le.mpr hP)

omit [Finite τ] in
/-- **A prime and an element outside it**: `p` is a nonzerodivisor modulo the prime `(G)` when
`p ∉ (G)`, so `(G, p)` has height `≥ 2`. -/
theorem two_le_height_span_pair {G p : MvPolynomial τ K}
    (hG : Prime G) (hp : p ∉ Ideal.span {G}) : (2 : ℕ∞) ≤ (Ideal.span {G, p}).height := by
  set φ : Fin 2 → MvPolynomial τ K := ![G, p]
  have hrange : Set.range φ = {G, p} := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty]
    rfl
  have h := Ideal.natCast_le_height_span_range_of_colon_eq (φ := φ) fun j ↦ by
    refine le_antisymm (fun y hy ↦ ?_) fun y hy ↦
      Submodule.mem_colon_singleton.mpr (by rw [smul_eq_mul]; exact Ideal.mul_mem_right _ _ hy)
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hy
    fin_cases j
    · have : φ '' Set.Iio 0 = ∅ := by simp
      simp only [Fin.zero_eta, this, Ideal.span_empty, Submodule.mem_bot] at hy ⊢
      exact (mul_eq_zero.mp hy).resolve_right hG.ne_zero
    · have : φ '' Set.Iio 1 = {G} := by
        ext x
        simp only [Set.mem_image, Set.mem_Iio, Set.mem_singleton_iff]
        constructor
        · rintro ⟨i, hi, rfl⟩
          fin_cases i
          · rfl
          · exact absurd hi (lt_irrefl _)
        · rintro rfl
          exact ⟨0, by decide, rfl⟩
      simp only [Fin.mk_one, this] at hy ⊢
      have hprime := (Ideal.span_singleton_prime hG.ne_zero).mpr hG
      exact (hprime.mem_or_mem hy).resolve_right hp
  rw [hrange] at h
  exact_mod_cast h

/-- **Krull's bound for forms**: finitely many forms of positive degree generate an ideal of
height at most their number. -/
theorem height_span_le_ncard_of_isHomogeneous {s : Set (MvPolynomial τ K)} (hs : s.Finite)
    (h : ∀ x ∈ s, ∃ n, 0 < n ∧ x.IsHomogeneous n) : (Ideal.span s).height ≤ s.ncard := by
  refine Ideal.height_span_le_ncard_of_span_ne_top hs fun htop ↦ ?_
  have hle : Ideal.span s ≤ RingHom.ker (constantCoeff : MvPolynomial τ K →+* K) := by
    rw [Ideal.span_le]
    intro x hx
    obtain ⟨n, hn, hxn⟩ := h x hx
    rw [SetLike.mem_coe, RingHom.mem_ker, constantCoeff_eq]
    exact hxn.coeff_eq_zero (by simp; omega)
  exact (RingHom.ker_ne_top _) (top_le_iff.mp (htop ▸ hle))

/-- **Elements of a homogeneous proper ideal have no constant term.** -/
theorem constantCoeff_eq_zero_of_mem {R : Set (MvPolynomial τ K)}
    (hR : ∀ r ∈ R, ∃ n, r.IsHomogeneous n) (htop : Ideal.span R ≠ ⊤) {y : MvPolynomial τ K}
    (hy : y ∈ Ideal.span R) : constantCoeff y = 0 := by
  by_contra h0
  refine htop ((Ideal.eq_top_iff_one _).mpr ?_)
  refine mem_of_mul_mem_of_constantCoeff_ne_zero (isWeightedHomogeneous_span fun r hr ↦ ?_) h0
    (by rwa [mul_one])
  obtain ⟨n, hn⟩ := hR r hr
  exact ⟨_, isWeightedHomogeneous_oneBlock hn⟩

end Heights

section OriginDim

instance isMaximal_ker_constantCoeff :
    (RingHom.ker (constantCoeff : MvPolynomial τ K →+* K)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨C c, constantCoeff_C _ _⟩

/-- The local ring of `K[X]` at the origin. -/
local notation "B" τ => Localization.AtPrime (RingHom.ker (constantCoeff : MvPolynomial τ K →+* K))

/-- **The dimension at the origin** of `V(J)`: the Krull dimension of `K[X]_𝔪 / J K[X]_𝔪`,
`𝔪 = ker constantCoeff`, as the Krull dimension of the zero locus of `J K[X]_𝔪`. -/
noncomputable def originDim (J : Ideal (MvPolynomial τ K)) : WithBot ℕ∞ :=
  Order.krullDim (PrimeSpectrum.zeroLocus (R := B τ)
    (J.map (algebraMap (MvPolynomial τ K) (B τ)) : Set (B τ)))

private theorem krullDim_congr {α : Type*} [Preorder α] {s t : Set α} (h : s = t) :
    Order.krullDim s = Order.krullDim t := by
  subst h
  rfl

private theorem supportDim_quotient_eq (I : Ideal (B τ)) :
    Module.supportDim (B τ) ((B τ) ⧸ I) =
      Order.krullDim (PrimeSpectrum.zeroLocus (R := B τ) (I : Set (B τ))) := by
  rw [Module.supportDim]
  exact krullDim_congr (by rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient])

private theorem supportDim_quotSMulTop_eq (I : Ideal (B τ)) (x : B τ) :
    Module.supportDim (B τ) (QuotSMulTop x ((B τ) ⧸ I)) =
      Order.krullDim (PrimeSpectrum.zeroLocus (R := B τ) ((I ⊔ Ideal.span {x} : Ideal (B τ)) :
        Set (B τ))) := by
  rw [Module.supportDim]
  refine krullDim_congr ?_
  rw [Module.support_quotSMulTop, Module.support_eq_zeroLocus, Ideal.annihilator_quotient,
    PrimeSpectrum.zeroLocus_sup, PrimeSpectrum.zeroLocus_span]

private theorem map_sup_span_singleton (J : Ideal (MvPolynomial τ K)) (x : MvPolynomial τ K) :
    (J ⊔ Ideal.span {x}).map (algebraMap (MvPolynomial τ K) (B τ)) =
      J.map (algebraMap _ (B τ)) ⊔ Ideal.span {algebraMap _ (B τ) x} := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]

theorem originDim_mono {J J' : Ideal (MvPolynomial τ K)} (h : J ≤ J') :
    originDim J' ≤ originDim J :=
  Order.krullDim_le_of_strictMono (Set.inclusion (PrimeSpectrum.zeroLocus_anti_mono
    (Ideal.map_mono h))) fun _ _ h ↦ h

private theorem ker_le_span_range_X :
    RingHom.ker (constantCoeff : MvPolynomial τ K →+* K) ≤ Ideal.span (Set.range X) := by
  intro p hp
  rw [← Set.image_univ, mem_ideal_span_X_image]
  intro m hm
  by_contra! h
  have hm0 : m = 0 := Finsupp.ext fun i ↦ h i (Set.mem_univ i)
  subst hm0
  rw [RingHom.mem_ker, constantCoeff_eq] at hp
  exact (mem_support_iff.mp hm) hp

/-- A prime of `K[X]_𝔪` containing the image of every variable is the maximal ideal. -/
private theorem eq_maximalIdeal_of_X_mem {Q : Ideal (B τ)} (hQ : Q.IsPrime)
    (hX : ∀ y, algebraMap (MvPolynomial τ K) (B τ) (X y) ∈ Q) :
    Q = IsLocalRing.maximalIdeal (B τ) := by
  refine le_antisymm (IsLocalRing.le_maximalIdeal hQ.ne_top) ?_
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
  refine ker_le_span_range_X.trans (Ideal.span_le.mpr ?_)
  rintro _ ⟨y, rfl⟩
  exact hX y

/-- If the maximal ideal is minimal over `J K[X]_𝔪`, the dimension at the origin is `≤ 0`. -/
private theorem originDim_nonpos_of_forall {J : Ideal (MvPolynomial τ K)}
    (h : ∀ Q : Ideal (B τ), Q.IsPrime → J.map (algebraMap _ (B τ)) ≤ Q →
      Q = IsLocalRing.maximalIdeal (B τ)) : originDim J ≤ 0 := by
  rw [originDim, Order.krullDim_nonpos_iff_forall_isMax]
  rintro ⟨P, hP⟩ ⟨P', hP'⟩ -
  have h1 := h P.asIdeal P.2 hP
  have h2 := h P'.asIdeal P'.2 hP'
  change P' ≤ P
  rw [← PrimeSpectrum.asIdeal_le_asIdeal, h1, h2]

/-- **Cutting by an element outside the minimal primes lowers the dimension at the origin.** -/
theorem originDim_sup_add_one_le (J : Ideal (MvPolynomial τ K)) {x : MvPolynomial τ K}
    (hx : ∀ Q ∈ (J.map (algebraMap _ (B τ))).minimalPrimes, algebraMap _ (B τ) x ∉ Q) :
    originDim (J ⊔ Ideal.span {x}) + 1 ≤ originDim J := by
  have := Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes
    (M := (B τ) ⧸ J.map (algebraMap _ _)) (x := algebraMap _ (B τ) x)
    (by rwa [Ideal.annihilator_quotient])
  rwa [supportDim_quotient_eq, supportDim_quotSMulTop_eq, ← map_sup_span_singleton] at this

/-- An ideal containing a power of every variable has dimension `≤ 0` at the origin. -/
theorem originDim_nonpos_of_pow_mem {J : Ideal (MvPolynomial τ K)}
    (h : ∀ y, ∃ M, X y ^ M ∈ J) : originDim J ≤ 0 := by
  refine originDim_nonpos_of_forall fun Q hQ hJQ ↦ eq_maximalIdeal_of_X_mem hQ fun y ↦ ?_
  obtain ⟨M, hM⟩ := h y
  exact hQ.mem_of_pow_mem M (by rw [← map_pow]; exact hJQ (Ideal.mem_map_of_mem _ hM))

variable [Finite τ]

/-- **Cutting by an element of `𝔪` lowers the dimension at the origin by at most one.** -/
theorem originDim_le_sup_add_one (J : Ideal (MvPolynomial τ K)) {x : MvPolynomial τ K}
    (hx : constantCoeff x = 0) : originDim J ≤ originDim (J ⊔ Ideal.span {x}) + 1 := by
  have hx' : algebraMap _ (B τ) x ∈ IsLocalRing.maximalIdeal (B τ) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hx
  have := Module.supportDim_le_supportDim_quotSMulTop_succ
    (M := (B τ) ⧸ J.map (algebraMap (MvPolynomial τ K) (B τ))) hx'
  rwa [supportDim_quotient_eq, supportDim_quotSMulTop_eq, ← map_sup_span_singleton] at this

/-- **Krull's bound at the origin.** If `J + (T)` contains a power of every variable, with
`T ⊆ 𝔪`, the dimension of `J` at the origin is at most `|T|`. -/
theorem originDim_le_card : ∀ (T : Finset (MvPolynomial τ K)) {J : Ideal (MvPolynomial τ K)},
    (∀ x ∈ T, constantCoeff x = 0) → (∀ y, ∃ M, X y ^ M ∈ J ⊔ Ideal.span (T : Set _)) →
    originDim J ≤ T.card := by
  classical
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro J _ h
    simpa using originDim_nonpos_of_pow_mem (by simpa using h)
  | insert a T ha IH =>
    intro J hT h
    have h1 := originDim_le_sup_add_one J (hT a (mem_insert_self a T))
    have h2 := IH (J := J ⊔ Ideal.span {a}) (fun x hx ↦ hT x (mem_insert_of_mem hx)) (by
      intro y
      obtain ⟨M, hM⟩ := h y
      refine ⟨M, ?_⟩
      rwa [coe_insert, Ideal.span_insert, ← sup_assoc] at hM)
    calc originDim J ≤ originDim (J ⊔ Ideal.span {a}) + 1 := h1
      _ ≤ (T.card : WithBot ℕ∞) + 1 := by gcongr
      _ = ((insert a T).card : WithBot ℕ∞) := by rw [card_insert_of_notMem ha]; push_cast; rfl

/-- **Homogeneous ideals of dimension `≤ 0` at the origin are primary to `𝔪`**: every variable
has a power in them. -/
theorem pow_mem_of_originDim_nonpos {R : Set (MvPolynomial τ K)}
    (hR : ∀ r ∈ R, ∃ n, r.IsHomogeneous n) (h : originDim (Ideal.span R) ≤ 0) (y : τ) :
    ∃ M, X y ^ M ∈ Ideal.span R := by
  set ψ := algebraMap (MvPolynomial τ K) (B τ)
  set 𝔪 := RingHom.ker (constantCoeff : MvPolynomial τ K →+* K)
  have hrad : ψ (X y) ∈ ((Ideal.span R).map ψ).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro Q ⟨hJQ, hQ⟩
    have hmax : (Ideal.span R).map ψ ≤ IsLocalRing.maximalIdeal (B τ) :=
      hJQ.trans (IsLocalRing.le_maximalIdeal hQ.ne_top)
    have hQmax : Q = IsLocalRing.maximalIdeal (B τ) := by
      rw [originDim, Order.krullDim_nonpos_iff_forall_isMax] at h
      have := h ⟨⟨Q, hQ⟩, hJQ⟩
        (b := ⟨⟨_, (IsLocalRing.maximalIdeal.isMaximal (B τ)).isPrime⟩, hmax⟩)
        (show Q ≤ IsLocalRing.maximalIdeal (B τ) from IsLocalRing.le_maximalIdeal hQ.ne_top)
      exact le_antisymm (IsLocalRing.le_maximalIdeal hQ.ne_top) this
    rw [hQmax, ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (by simp [𝔪, RingHom.mem_ker] : X y ∈ 𝔪)
  obtain ⟨M, hM⟩ := hrad
  rw [← map_pow, IsLocalization.algebraMap_mem_map_algebraMap_iff 𝔪.primeCompl] at hM
  obtain ⟨s, hs, hsy⟩ := hM
  refine ⟨M, mem_of_mul_mem_of_constantCoeff_ne_zero (isWeightedHomogeneous_span fun r hr ↦ ?_)
    (by simpa [𝔪, RingHom.mem_ker] using hs) hsy⟩
  obtain ⟨n, hn⟩ := hR r hr
  exact ⟨_, isWeightedHomogeneous_oneBlock hn⟩

private theorem le_of_add_one_le {a : WithBot ℕ∞} {k : ℕ} (h : a + 1 ≤ ((k + 1 : ℕ) : WithBot ℕ∞)) :
    a ≤ k := by
  induction a with
  | bot => exact bot_le
  | coe a =>
    have h' : a + 1 ≤ ((k + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
    have : a ≤ k := by
      rw [Nat.cast_add, Nat.cast_one] at h'
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h'
    exact_mod_cast this

/-- **The generic linear form.** Over an infinite field, for finitely many ideals `I a` there is
one `ρ` in the span of the `X_v`, `v ∈ V`, that cuts each of them properly:
* `ht (I a + (ρ)) ≥ k + 1` whenever `ht (I a) ≥ k` and `k < |V|`;
* if `I a` contains the variables outside `V`, its dimension at the origin drops by one. -/
theorem exists_mem_span_forall [Infinite K] {α : Type*} [Finite α] (V : Set τ)
    (I : α → Ideal (MvPolynomial τ K)) :
    ∃ ρ ∈ Submodule.span K (X '' V : Set (MvPolynomial τ K)), ∀ a,
      (∀ k : ℕ, (k : ℕ∞) ≤ (I a).height → k < V.ncard →
        ((k + 1 : ℕ) : ℕ∞) ≤ (I a ⊔ Ideal.span {ρ}).height) ∧
      ((∀ y ∉ V, X y ∈ I a) → ∀ k : ℕ, originDim (I a) ≤ (k + 1 : ℕ) →
        originDim (I a ⊔ Ideal.span {ρ}) ≤ k) := by
  set ψ := algebraMap (MvPolynomial τ K) (B τ)
  set XV : Set (MvPolynomial τ K) := X '' V
  set SA : α → Set (Ideal (MvPolynomial τ K)) := fun a ↦ {P ∈ (I a).minimalPrimes | ¬ XV ⊆ P}
  set SB : α → Set (Ideal (MvPolynomial τ K)) := fun a ↦
    (fun Q ↦ Q.comap ψ) '' {Q ∈ ((I a).map ψ).minimalPrimes | ¬ XV ⊆ Q.comap ψ}
  have hfin : (⋃ a, SA a ∪ SB a).Finite := by
    refine Set.finite_iUnion fun a ↦ Set.Finite.union ?_ ?_
    · exact (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (I a)).subset fun _ h ↦ h.1
    · exact ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun _ h ↦ h.1).image _
  obtain ⟨ρ, hρV, hρ⟩ := exists_mem_span_forall_notMem hfin (R := XV) (by
    simp only [Set.mem_iUnion, Set.mem_union]
    rintro Q ⟨a, (h | ⟨Q', h, rfl⟩)⟩
    exacts [h.2, h.2])
  refine ⟨ρ, hρV, fun a ↦ ⟨fun k hk hkV ↦ ?_, fun hX k hk ↦ ?_⟩⟩
  · rw [Ideal.height_eq_inf_minimalPrimes]
    refine le_iInf₂ fun Q hQ ↦ ?_
    have := hQ.1.1
    obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hQ.1.2)
    have := hP.1.1
    by_cases hXP : XV ⊆ P
    · calc ((k + 1 : ℕ) : ℕ∞) ≤ V.ncard := by exact_mod_cast hkV
        _ ≤ P.height := ncard_le_height_of_image_X_subset V hXP
        _ ≤ Q.height := Ideal.height_mono hPQ
    · have hρP : ρ ∉ P := fun h ↦ hρ P (Set.mem_iUnion.mpr ⟨a, Or.inl ⟨hP, hXP⟩⟩) h
      have hlt : P < Q := lt_of_le_of_ne hPQ fun h ↦
        hρP (h ▸ hQ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
      calc ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 := by push_cast; rfl
        _ ≤ P.height + 1 := by gcongr; exact hk.trans (Ideal.height_mono hP.1.2)
        _ ≤ Q.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  · by_cases hcase : ∃ Q ∈ ((I a).map ψ).minimalPrimes, XV ⊆ Q.comap ψ
    · obtain ⟨Q, hQ, hXQ⟩ := hcase
      have := hQ.1.1
      have hQmax : Q = IsLocalRing.maximalIdeal (B τ) := by
        refine eq_maximalIdeal_of_X_mem this fun y ↦ ?_
        by_cases hy : y ∈ V
        · exact hXQ ⟨y, hy, rfl⟩
        · exact hQ.1.2 (Ideal.mem_map_of_mem _ (hX y hy))
      have h0 : originDim (I a) ≤ 0 := originDim_nonpos_of_forall fun Q' hQ' hIQ' ↦ by
        refine le_antisymm (IsLocalRing.le_maximalIdeal hQ'.ne_top) ?_
        rw [← hQmax]
        exact hQ.2 ⟨hQ', hIQ'⟩ (hQmax ▸ IsLocalRing.le_maximalIdeal hQ'.ne_top)
      exact (originDim_mono le_sup_left).trans (h0.trans (by exact_mod_cast Nat.zero_le k))
    · push Not at hcase
      have h1 := originDim_sup_add_one_le (I a) (x := ρ) fun Q hQ hρQ ↦
        hρ (Q.comap ψ) (Set.mem_iUnion.mpr ⟨a, Or.inr ⟨Q, ⟨hQ, hcase Q hQ⟩, rfl⟩⟩) hρQ
      exact le_of_add_one_le (h1.trans hk)

end OriginDim

/-- Linear combinations of variables are forms of degree `1`. -/
theorem isHomogeneous_of_mem_span_X {V : Set τ} {ρ : MvPolynomial τ K}
    (h : ρ ∈ Submodule.span K (X '' V : Set (MvPolynomial τ K))) : ρ.IsHomogeneous 1 := by
  have : Submodule.span K (X '' V : Set (MvPolynomial τ K)) ≤ homogeneousSubmodule τ K 1 :=
    Submodule.span_le.mpr (by rintro _ ⟨y, -, rfl⟩; exact isHomogeneous_X K y)
  exact this h

section Padding

variable [Finite τ] [Infinite K]

/-- **Generic linear forms raise the height**: if `ht I ≥ k` and `k + m ≤ |V|`, there are `m`
linear forms in the span of the `X_v`, `v ∈ V`, with `ht (I + (ρ)) ≥ k + m`. -/
theorem exists_le_height_sup_span_range (V : Set τ) (I : Ideal (MvPolynomial τ K)) {k : ℕ}
    (hk : (k : ℕ∞) ≤ I.height) : ∀ m, k + m ≤ V.ncard →
      ∃ ρ : Fin m → MvPolynomial τ K,
        (∀ j, ρ j ∈ Submodule.span K (X '' V : Set (MvPolynomial τ K))) ∧
        ((k + m : ℕ) : ℕ∞) ≤ (I ⊔ Ideal.span (Set.range ρ)).height
  | 0, _ => ⟨Fin.elim0, fun j ↦ j.elim0, by simpa [Set.range_eq_empty] using hk⟩
  | m + 1, hm => by
    obtain ⟨ρ, hρV, hρ⟩ := exists_le_height_sup_span_range V I hk m (by omega)
    obtain ⟨ρ', hρ'V, hρ'⟩ := exists_mem_span_forall V
      (fun _ : Unit ↦ I ⊔ Ideal.span (Set.range ρ))
    refine ⟨Fin.cons ρ' ρ, fun j ↦ Fin.cases hρ'V hρV j, ?_⟩
    rw [Fin.range_cons, Ideal.span_insert, sup_left_comm, sup_comm (Ideal.span {ρ'})]
    exact (hρ' ()).1 (k + m) hρ (by omega)

/-- **Padding by generic linear forms** (Corvaja–Zannier 2004, proof of Theorem 2). If forms
`G₁, …, G_b, f₁, …, f_t` generate an ideal of height `b + t ≤ |V|`, there are linear forms `ρ_j`
in the span of the `X_v`, `v ∈ V`, such that `G, f₁ ρ₁^{a₁}, …, f_t ρ_t^{a_t}` generate an ideal
of height `≥ b + t` for every `a`: a prime containing them contains, for each `j`, `f_j` or
`ρ_j`, and the `ρ_j` are chosen one at a time so that every such mixed family has the right
height. -/
theorem exists_le_height_span_mul_pow (V : Set τ) {b t : ℕ} {G : Fin b → MvPolynomial τ K}
    {f : Fin t → MvPolynomial τ K} (hG : ∀ l, ∃ n, (G l).IsHomogeneous n)
    (hf : ∀ j, ∃ n, (f j).IsHomogeneous n) (hV : b + t ≤ V.ncard)
    (hht : (Ideal.span (Set.range G ∪ Set.range f)).height = (b + t : ℕ)) :
    ∃ ρ : Fin t → MvPolynomial τ K,
      (∀ j, ρ j ∈ Submodule.span K (X '' V : Set (MvPolynomial τ K))) ∧
      ∀ a : Fin t → ℕ, ((b + t : ℕ) : ℕ∞) ≤
        (Ideal.span (Set.range G ∪ Set.range fun j ↦ f j * ρ j ^ a j)).height := by
  classical
  set I : Finset (Fin t) → Finset (Fin t) → (Fin t → MvPolynomial τ K) →
      Ideal (MvPolynomial τ K) :=
    fun F H ρ ↦ Ideal.span (Set.range G ∪ f '' F ∪ ρ '' H) with hIdef
  -- The base case: subfamilies have the right height (Lemma 2.1).
  have hA0 : ∀ F : Finset (Fin t),
      ((b + F.card : ℕ) : ℕ∞) ≤ (Ideal.span (Set.range G ∪ f '' F)).height := by
    intro F
    set u : Fin b ⊕ Fin t → MvPolynomial τ K := Sum.elim G f
    have himg : ∀ A : Finset (Fin t),
        u '' ((univ.disjSum A : Finset (Fin b ⊕ Fin t)) : Set (Fin b ⊕ Fin t)) =
          Set.range G ∪ f '' A := by
      intro A
      ext x
      simp only [Set.mem_image, mem_coe, mem_disjSum, mem_univ, true_and, Set.mem_union,
        Set.mem_range]
      constructor
      · rintro ⟨_, (⟨l, rfl⟩ | ⟨j, hj, rfl⟩), rfl⟩
        exacts [Or.inl ⟨l, rfl⟩, Or.inr ⟨j, hj, rfl⟩]
      · rintro (⟨l, rfl⟩ | ⟨j, hj, rfl⟩)
        exacts [⟨_, Or.inl ⟨l, rfl⟩, rfl⟩, ⟨_, Or.inr ⟨j, hj, rfl⟩, rfl⟩]
    have hu : ∀ i, ∃ n, (u i).IsHomogeneous n := fun i ↦ by
      cases i with
      | inl l => exact hG l
      | inr j => exact hf j
    have := card_le_height_span_image hu (A := univ.disjSum F) (C := univ.disjSum univ)
      (disjSum_mono subset_rfl (subset_univ F))
      (by rw [himg, coe_univ, Set.image_univ, hht, card_disjSum, card_univ, card_univ,
        Fintype.card_fin, Fintype.card_fin])
    rwa [himg, card_disjSum, card_univ, Fintype.card_fin] at this
  -- The linear forms, one after the other.
  have hstep : ∀ m ≤ t, ∃ ρ : Fin t → MvPolynomial τ K,
      (∀ j, ρ j ∈ Submodule.span K (X '' V : Set (MvPolynomial τ K))) ∧
      ∀ F H : Finset (Fin t), Disjoint F H → (∀ j ∈ H, (j : ℕ) < m) →
        ((b + F.card + H.card : ℕ) : ℕ∞) ≤ (I F H ρ).height := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨0, fun _ ↦ zero_mem _, fun F H _ hH ↦ ?_⟩
      have : H = ∅ := eq_empty_of_forall_notMem fun i hi ↦ by simpa using hH i hi
      subst this
      simpa [I] using hA0 F
    | succ m IH =>
      intro hm
      obtain ⟨ρ, hρV, hρ⟩ := IH (by omega)
      obtain ⟨ρ', hρ'V, hρ'⟩ := exists_mem_span_forall V
        (fun x : Finset (Fin t) × Finset (Fin t) ↦ I x.1 x.2 ρ)
      set i₀ : Fin t := ⟨m, hm⟩
      refine ⟨Function.update ρ i₀ ρ', fun i ↦ ?_, fun F H hFH hH ↦ ?_⟩
      · by_cases hi : i = i₀
        · rw [hi, Function.update_self]
          exact hρ'V
        · rw [Function.update_of_ne hi]
          exact hρV i
      by_cases hi₀ : i₀ ∈ H
      · set H' := H.erase i₀
        have hH' : ∀ i ∈ H', (i : ℕ) < m := fun i hi ↦ by
          obtain ⟨hne, hiH⟩ := mem_erase.mp hi
          have h1 := hH i hiH
          have h2 : (i : ℕ) ≠ m := fun h ↦ hne (Fin.ext h)
          omega
        have hFH' : Disjoint F H' := disjoint_of_subset_right (erase_subset _ _) hFH
        have hcardH : H.card = H'.card + 1 := (card_erase_add_one hi₀).symm
        have himg : Function.update ρ i₀ ρ' '' ↑H = insert ρ' (ρ '' ↑H') := by
          rw [← insert_erase hi₀, coe_insert, Set.image_insert_eq, Function.update_self]
          congr 1
          refine Set.image_congr fun i hi ↦ Function.update_of_ne ?_ _ _
          exact (mem_erase.mp hi).1
        have hI : I F H (Function.update ρ i₀ ρ') = I F H' ρ ⊔ Ideal.span {ρ'} := by
          simp only [I]
          rw [himg, Set.union_insert, Ideal.span_insert, sup_comm]
        have hcard : F.card + H.card ≤ t := by
          rw [← card_union_of_disjoint hFH]
          simpa using card_le_univ (F ∪ H)
        rw [hI]
        have := (hρ' (F, H')).1 (b + F.card + H'.card) (hρ F H' hFH' hH') (by omega)
        rwa [hcardH, ← add_assoc]
      · have hH' : ∀ i ∈ H, (i : ℕ) < m := fun i hi ↦ by
          have h1 := hH i hi
          have h2 : (i : ℕ) ≠ m := fun h ↦ hi₀ (by rwa [show i₀ = i from Fin.ext h.symm])
          omega
        have himg : Function.update ρ i₀ ρ' '' ↑H = ρ '' ↑H :=
          Set.image_congr fun i hi ↦ Function.update_of_ne (by rintro rfl; exact hi₀ hi) _ _
        simp only [I, himg]
        exact hρ F H hFH hH'
  obtain ⟨ρ, hρV, hρ⟩ := hstep t le_rfl
  refine ⟨ρ, hρV, fun a ↦ ?_⟩
  -- A prime containing the padded forms contains `f_j` or `ρ_j` for each `j`.
  rw [Ideal.height_eq_inf_minimalPrimes]
  refine le_iInf₂ fun Q hQ ↦ ?_
  have hQp := hQ.1.1
  set F := univ.filter (fun j ↦ f j ∈ Q)
  set H := univ.filter (fun j ↦ f j ∉ Q)
  have hFH : F.card + H.card = t := by
    rw [card_filter_add_card_filter_not, card_univ, Fintype.card_fin]
  have hle : I F H ρ ≤ Q := by
    rw [Ideal.span_le]
    rintro _ ((⟨l, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩)
    · exact hQ.1.2 (Ideal.subset_span (Or.inl ⟨l, rfl⟩))
    · exact (mem_filter.mp hj).2
    · have hmem : f j * ρ j ^ a j ∈ Q := hQ.1.2 (Ideal.subset_span (Or.inr ⟨j, rfl⟩))
      exact hQp.mem_of_pow_mem _ ((hQp.mem_or_mem hmem).resolve_left (mem_filter.mp hj).2)
  have := hρ F H (disjoint_filter_filter_not _ _ _) fun j _ ↦ j.isLt
  rw [add_assoc, hFH] at this
  exact this.trans (Ideal.height_mono hle)

end Padding

end MvPolynomial
