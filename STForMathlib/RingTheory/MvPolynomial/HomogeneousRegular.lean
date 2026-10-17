/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import STForMathlib.RingTheory.MvPolynomial.CompleteIntersection
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

-- Used only inside proofs.
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import STForMathlib.RingTheory.MvPolynomial.ExcessBezout
import STForMathlib.RingTheory.RegularLocalRing.HeightRegular
import STForMathlib.RingTheory.RegularLocalRing.RegularSequence

/-!
# Forms of the right height are a regular sequence

Let `φ₀, …, φ_{m-1}` be homogeneous polynomials in `K[X_s | s ∈ σ]`, `σ` finite, generating an
ideal of height `m` (they cut the projective space in dimension `|σ| - 1 - m`). Then they form a
regular sequence, in this order: each `φ j` is a nonzerodivisor modulo `(φ i | i < j)`.

This is Corvaja–Zannier, *On a general Thue's equation*, Amer. J. Math. 126 (2004), Lemma 2.1,
"a well-known fact from the theory of Cohen–Macaulay rings". The proof localizes at the irrelevant
ideal `𝔪 = (X_s | s ∈ σ)`: `K[X]_𝔪` is a regular local ring (Mathlib), so its maximal ideal holds
a regular sequence of length `dim K[X]_𝔪`, and there a sequence of height `m` is regular
(`IsLocalRing.isSMulRegular_of_le_height`). Back in `K[X]`, homogeneous ideals are saturated with
respect to the elements outside `𝔪`, because their associated primes are homogeneous
(`MvPolynomial.isWeightedHomogeneous_of_mem_associatedPrimes`), hence inside `𝔪`.

Only the height of the whole sequence is assumed; the heights of its initial segments follow.

## Main statements

* `MvPolynomial.mem_of_mul_mem_of_constantCoeff_ne_zero`: homogeneous ideals are saturated with
  respect to the polynomials with nonzero constant term.
* `MvPolynomial.colon_eq_of_height_eq`: **forms of height `m` are a regular sequence**
  (Corvaja–Zannier 2004, Lemma 2.1).
* `MvPolynomial.isRegularSeq_of_height_eq`: the same as `IsRegularSeq m ⊥ φ`.
* `MvPolynomial.colon_eq_of_height_insert_eq`: the last element, for `(G, p)` of height `t + 1`.
* `MvPolynomial.isRegularSeq_append_of_height_eq`: the tail `h` of `(g, h)` is regular modulo
  `(g)`.
-/

@[expose] public section

namespace MvPolynomial

variable {σ K : Type*} [Field K]

/-- The standard grading as the one-block multigrading. -/
theorem isWeightedHomogeneous_oneBlock_iff [Finite σ] {φ : MvPolynomial σ K} {n : ℕ} :
    IsWeightedHomogeneous (multiWeight (oneBlock σ)) φ (fun _ ↦ n) ↔ φ.IsHomogeneous n := by
  have := Fintype.ofFinite σ
  have hw : ∀ d : σ →₀ ℕ, Finsupp.weight (multiWeight (oneBlock σ)) d = fun _ ↦ d.degree := by
    intro d
    ext u
    rw [weight_multiWeight_apply, Finsupp.degree_eq_sum]
    simp
  constructor
  · intro h d hd
    have := congrFun ((hw d).symm.trans (h hd)) ()
    change Finsupp.weight (fun _ ↦ 1) d = n
    rw [← Finsupp.degree_eq_weight_one]
    exact this
  · intro h d hd
    rw [hw d]
    have : d.degree = n := by rw [Finsupp.degree_eq_weight_one]; exact h hd
    rw [this]

theorem isWeightedHomogeneous_oneBlock [Finite σ] {φ : MvPolynomial σ K} {n : ℕ}
    (hφ : φ.IsHomogeneous n) :
    IsWeightedHomogeneous (multiWeight (oneBlock σ)) φ (fun _ ↦ n) :=
  isWeightedHomogeneous_oneBlock_iff.mpr hφ

/-- **Homogeneous ideals are saturated** with respect to the polynomials with nonzero constant
term: their associated primes are homogeneous, hence contain no such polynomial. -/
theorem mem_of_mul_mem_of_constantCoeff_ne_zero [Finite σ] {J : Ideal (MvPolynomial σ K)}
    (hJ : J.IsWeightedHomogeneous (multiWeight (oneBlock σ))) {s y : MvPolynomial σ K}
    (hs : constantCoeff s ≠ 0) (h : s * y ∈ J) : y ∈ J := by
  classical
  have := Fintype.ofFinite σ
  by_contra hy
  have hy0 : (Submodule.Quotient.mk y : MvPolynomial σ K ⧸ J) ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing (MvPolynomial σ K) _ hy0
  have hsP : s ∈ P := hle (by
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact h)
  have h0 := isWeightedHomogeneous_of_mem_associatedPrimes hJ hP hsP 0
  have hC : weightedHomogeneousComponent (multiWeight (oneBlock σ)) 0 s = C (constantCoeff s) := by
    ext d
    rw [coeff_weightedHomogeneousComponent, coeff_C]
    by_cases hd : d = 0
    · subst hd
      simp [constantCoeff_eq]
    · have : Finsupp.weight (multiWeight (oneBlock σ)) d ≠ 0 := by
        intro h0
        apply hd
        ext i
        have := congrFun h0 ()
        rw [weight_multiWeight_apply] at this
        simp only [Pi.zero_apply] at this
        exact (Finset.sum_eq_zero_iff.mp this) i (by simp)
      simp [this, Ne.symm hd]
  rw [hC] at h0
  exact hP.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 ((Ne.isUnit hs).map C))

/-- **Forms of height `m` are a regular sequence** (Corvaja–Zannier 2004, Lemma 2.1). If
homogeneous `φ₀, …, φ_{m-1}` generate an ideal of height `m`, each `φ j` is a nonzerodivisor
modulo `(φ i | i < j)`. -/
theorem colon_eq_of_height_eq [Finite σ] {m : ℕ} {φ : Fin m → MvPolynomial σ K}
    (hφ : ∀ j, ∃ n, (φ j).IsHomogeneous n) (hht : (Ideal.span (Set.range φ)).height = m)
    (j : Fin m) :
    (Ideal.span (φ '' Set.Iio j)).colon {φ j} = Ideal.span (φ '' Set.Iio j) := by
  set 𝔪 := RingHom.ker (constantCoeff : MvPolynomial σ K →+* K)
  have : 𝔪.IsMaximal := RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨C c, constantCoeff_C _ _⟩
  set A := Localization.AtPrime 𝔪
  set ψ := algebraMap (MvPolynomial σ K) A
  have hhom : ∀ S : Set (Fin m), (Ideal.span (φ '' S)).IsWeightedHomogeneous
      (multiWeight (oneBlock σ)) := fun S ↦ isWeightedHomogeneous_span fun _ ⟨l, _, hl⟩ ↦ by
    obtain ⟨n, hn⟩ := hφ l
    exact ⟨_, hl ▸ isWeightedHomogeneous_oneBlock hn⟩
  -- The forms lie in `𝔪`: otherwise they generate the unit ideal.
  have hφ𝔪 : ∀ l, φ l ∈ 𝔪 := by
    intro l
    by_contra hl
    have h1 : (1 : MvPolynomial σ K) ∈ Ideal.span (Set.range φ) := by
      refine mem_of_mul_mem_of_constantCoeff_ne_zero (s := φ l)
        (by rw [← Set.image_univ]; exact hhom Set.univ) hl ?_
      rw [mul_one]
      exact Ideal.subset_span ⟨l, rfl⟩
    rw [(Ideal.eq_top_iff_one _).mpr h1, Ideal.height_top] at hht
    exact ENat.top_ne_natCast m hht
  have hmax : 𝔪.map ψ = IsLocalRing.maximalIdeal A := Localization.AtPrime.map_eq_maximalIdeal
  have hx : ∀ l, ψ (φ l) ∈ IsLocalRing.maximalIdeal A := fun l ↦
    hmax ▸ Ideal.mem_map_of_mem ψ (hφ𝔪 l)
  have hht' : (m : ℕ∞) ≤ (Ideal.span (Set.range (ψ ∘ φ))).height := by
    rw [Set.range_comp, ← Ideal.map_span, ← IsLocalization.height_under 𝔪.primeCompl, ← hht]
    exact Ideal.height_mono (Ideal.le_comap_map)
  obtain ⟨rs, hlen, hmem, hrs⟩ := IsRegularLocalRing.exists_isRegular (R := A)
  have hdim : ringKrullDim A = (IsLocalRing.maximalIdeal A).spanFinrank :=
    ((isRegularLocalRing_iff A).mp inferInstance).symm
  have hreg := IsLocalRing.isSMulRegular_of_le_height hdim hlen hmem hrs hx hht' j
  rw [show Ideal.span ((fun j ↦ ψ (φ j)) '' Set.Iio j) = (Ideal.span (φ '' Set.Iio j)).map ψ by
    rw [Ideal.map_span, Set.image_image]] at hreg
  refine le_antisymm (fun y hy ↦ ?_) (le_colon_singleton _ _)
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hy
  set L := Ideal.span (φ '' Set.Iio j)
  have h1 : (Ideal.Quotient.mk (L.map ψ) (ψ y)) = 0 := by
    refine hreg ?_
    change Ideal.Quotient.mk _ (ψ (φ j) * ψ y) = ψ (φ j) • 0
    rw [smul_zero]
    rw [Ideal.Quotient.eq_zero_iff_mem, ← map_mul, mul_comm]
    exact Ideal.mem_map_of_mem ψ hy
  rw [Ideal.Quotient.eq_zero_iff_mem,
    IsLocalization.algebraMap_mem_map_algebraMap_iff 𝔪.primeCompl] at h1
  obtain ⟨s, hs, hsy⟩ := h1
  exact mem_of_mul_mem_of_constantCoeff_ne_zero (hhom _) hs hsy

/-- The forms of `colon_eq_of_height_eq` are nonzero. -/
theorem ne_zero_of_height_eq [Finite σ] {m : ℕ} {φ : Fin m → MvPolynomial σ K}
    (hφ : ∀ j, ∃ n, (φ j).IsHomogeneous n) (hht : (Ideal.span (Set.range φ)).height = m)
    (j : Fin m) : φ j ≠ 0 := by
  intro h0
  have hc := colon_eq_of_height_eq hφ hht j
  rw [h0] at hc
  have htop : Ideal.span (φ '' Set.Iio j) = ⊤ := by
    rw [← hc, eq_top_iff]
    intro y _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact zero_mem _
  have : Ideal.span (Set.range φ) = ⊤ :=
    top_unique (htop ▸ Ideal.span_mono (Set.image_subset_range _ _))
  rw [this, Ideal.height_top] at hht
  exact ENat.top_ne_natCast m hht

/-- A sequence with each element nonzero and a nonzerodivisor modulo `J` and the earlier ones is
a regular sequence modulo `J`. -/
theorem isRegularSeq_of_forall_colon_eq : ∀ {t : ℕ} {J : Ideal (MvPolynomial σ K)}
    {g : Fin t → MvPolynomial σ K}, (∀ i, g i ≠ 0) →
    (∀ i, (J ⊔ Ideal.span (g '' Set.Iio i)).colon {g i} = J ⊔ Ideal.span (g '' Set.Iio i)) →
    IsRegularSeq t J g
  | 0, _, _, _, _ => trivial
  | t + 1, J, g, h0, hc => by
    refine ⟨h0 0, by simpa using hc 0, isRegularSeq_of_forall_colon_eq (fun i ↦ h0 i.succ)
      fun i ↦ ?_⟩
    have hI : Set.Iio i.succ = insert 0 (Fin.succ '' Set.Iio i) := by
      ext l
      cases l using Fin.cases <;> simp [Fin.succ_pos]
    have := hc i.succ
    rw [hI, Set.image_insert_eq, Set.image_image, Ideal.span_insert, ← sup_assoc] at this
    exact this

/-- **Forms of height `m` are a regular sequence**, as `IsRegularSeq` (Corvaja–Zannier 2004,
Lemma 2.1). -/
theorem isRegularSeq_of_height_eq [Finite σ] {m : ℕ} {φ : Fin m → MvPolynomial σ K}
    (hφ : ∀ j, ∃ n, (φ j).IsHomogeneous n) (hht : (Ideal.span (Set.range φ)).height = m) :
    IsRegularSeq m ⊥ φ :=
  isRegularSeq_of_forall_colon_eq (ne_zero_of_height_eq hφ hht) fun i ↦ by
    simpa using colon_eq_of_height_eq hφ hht i

/-- **The last form is a nonzerodivisor.** If homogeneous `g₀, …, g_{t-1}, p` generate an ideal
of height `t + 1`, then `p` is a nonzerodivisor modulo `(g)`. For `p = X₀` this is the hypothesis
of `MvPolynomial.mem_span_homogenization_of_dehomogenize_mem`. -/
theorem colon_eq_of_height_insert_eq [Finite σ] {t : ℕ} {g : Fin t → MvPolynomial σ K}
    {p : MvPolynomial σ K} (hg : ∀ j, ∃ n, (g j).IsHomogeneous n) (hp : ∃ n, p.IsHomogeneous n)
    (hht : (Ideal.span (insert p (Set.range g))).height = t + 1) :
    (Ideal.span (Set.range g)).colon {p} = Ideal.span (Set.range g) := by
  set φ : Fin (t + 1) → MvPolynomial σ K := Fin.snoc g p
  have hφ : ∀ j, ∃ n, (φ j).IsHomogeneous n := fun j ↦ by
    induction j using Fin.lastCases with
    | last => simpa [φ] using hp
    | cast i => simpa [φ] using hg i
  have himg : φ '' Set.Iio (Fin.last t) = Set.range g := by
    ext x
    simp only [Set.mem_image, Set.mem_Iio, Set.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      induction i using Fin.lastCases with
      | last => exact absurd hi (lt_irrefl _)
      | cast i => exact ⟨i, by simp [φ]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.castSucc, Fin.castSucc_lt_last i, by simp [φ]⟩
  have := colon_eq_of_height_eq hφ (by rw [Fin.range_snoc, hht]; norm_cast) (Fin.last t)
  rwa [himg, show φ (Fin.last t) = p by simp [φ]] at this

theorem range_append {s t : ℕ} {α : Type*} (g : Fin s → α) (h : Fin t → α) :
    Set.range (Fin.append g h) = Set.range g ∪ Set.range h := by
  ext x
  simp only [Set.mem_range, Set.mem_union]
  constructor
  · rintro ⟨l, rfl⟩
    induction l using Fin.addCases with
    | left l => exact Or.inl ⟨l, by simp⟩
    | right l => exact Or.inr ⟨l, by simp⟩
  · rintro (⟨l, rfl⟩ | ⟨l, rfl⟩)
    exacts [⟨Fin.castAdd t l, by simp⟩, ⟨Fin.natAdd s l, by simp⟩]

/-- **A tail of forms of the right height is regular modulo the head.** If homogeneous
`g₀, …, g_{s-1}, h₀, …, h_{t-1}` generate an ideal of height `s + t`, then `h` is a regular
sequence modulo `(g)`. -/
theorem isRegularSeq_append_of_height_eq [Finite σ] {s t : ℕ} {g : Fin s → MvPolynomial σ K}
    {h : Fin t → MvPolynomial σ K} (hg : ∀ j, ∃ n, (g j).IsHomogeneous n)
    (hh : ∀ j, ∃ n, (h j).IsHomogeneous n)
    (hht : (Ideal.span (Set.range (Fin.append g h))).height = (s + t : ℕ)) :
    IsRegularSeq t (Ideal.span (Set.range g)) h := by
  have hφ : ∀ j, ∃ n, (Fin.append g h j).IsHomogeneous n := fun j ↦ by
    induction j using Fin.addCases with
    | left l => simpa using hg l
    | right l => simpa using hh l
  refine isRegularSeq_of_forall_colon_eq
    (fun i ↦ by simpa using ne_zero_of_height_eq hφ hht (Fin.natAdd s i)) fun i ↦ ?_
  have himg : Fin.append g h '' Set.Iio (Fin.natAdd s i) = Set.range g ∪ h '' Set.Iio i := by
    ext x
    simp only [Set.mem_image, Set.mem_Iio, Set.mem_union, Set.mem_range]
    constructor
    · rintro ⟨l, hl, rfl⟩
      induction l using Fin.addCases with
      | left l => exact Or.inl ⟨l, by simp⟩
      | right l =>
        refine Or.inr ⟨l, ?_, by simp⟩
        rw [Fin.lt_def] at hl ⊢
        simp only [Fin.val_natAdd] at hl
        omega
    · rintro (⟨l, rfl⟩ | ⟨l, hl, rfl⟩)
      · exact ⟨Fin.castAdd t l, by rw [Fin.lt_def]; simp; omega, by simp⟩
      · exact ⟨Fin.natAdd s l, by rw [Fin.lt_def] at hl ⊢; simpa using hl, by simp⟩
  have := colon_eq_of_height_eq hφ hht (Fin.natAdd s i)
  rwa [himg, Ideal.span_union, Fin.append_right] at this

end MvPolynomial
