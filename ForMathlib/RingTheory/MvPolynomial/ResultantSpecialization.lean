/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.ResultantForm
public import ForMathlib.RingTheory.MvPolynomial.Specialization

-- Used only inside proofs.
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal

/-!
# Specializations of resultant forms

Rémond's Proposition 2.16 (LNM 1752, Ch. 5) for **resultant** forms: when all forms but the
first are specialized into an algebraically closed field, `res_d(I)` becomes a product
`c ∏_j U(z_j)` of specializations of the first generic form at points. Rémond uses it in this
form in the proof of Ch. 7, Thm 2.2 ("car `f` est produit de puissances de formes
`elim_d(𝔭)`").

## Main results

* `MvPolynomial.exists_associated_resForm_elimForm_pow`: for a prime `𝔭` of the right
  dimension, `res_d(𝔭) ~ elim_d(𝔭)^m`. The eliminant ideal annihilates the graded pieces, so
  `res_d(𝔭)` divides a power of every element of the prime `𝔈_d(𝔭)`. If `res_d(𝔭)` is not a
  unit, its prime factor generates `𝔈_d(𝔭)`.
* `MvPolynomial.exists_specEval_resForm_eq`: the product formula, from Thm 3.3.
-/

@[expose] public section

namespace MvPolynomial

section PointProduct

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] (b : σ → ι)
  (L : Type*) [Field L] (e : ι → ℕ)

/-- The products `c ∏_j U(z_j)` of point forms of multidegree `e`, with every `z_j` nonzero in
every block. -/
def pointSubmonoid : Submonoid (MvPolynomial (GenericVar b fun _ : Unit ↦ e) L) where
  carrier := {P | ∃ (c : L) (Z : Multiset (σ → L)), (∀ z ∈ Z, ∀ i, ∃ s, b s = i ∧ z s ≠ 0) ∧
    P = C c * (Z.map (pointForm b e)).prod}
  one_mem' := ⟨1, 0, by simp, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨c, Z, hZ, rfl⟩ ⟨c', Z', hZ', rfl⟩
    refine ⟨c * c', Z + Z', fun z hz ↦ ?_, ?_⟩
    · rcases Multiset.mem_add.1 hz with hz | hz
      exacts [hZ z hz, hZ' z hz]
    · rw [Multiset.map_add, Multiset.prod_add, C_mul]
      ring

variable {b L e}

theorem C_mem_pointSubmonoid (c : L) : C c ∈ pointSubmonoid b L e :=
  ⟨c, 0, by simp, by simp⟩

end PointProduct

section Resultant

universe u

variable {σ ι : Type u} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
  {K : Type u} [Field K]

/-- **`res_d(𝔭)` is a power of `elim_d(𝔭)`** for a multihomogeneous prime `𝔭 ⊉ 𝔪` with
`deg H_𝔭 ≤ r - 1`. -/
theorem exists_associated_resForm_elimForm_pow {κ : Type u} [Finite κ] {d : κ → ι → ℕ}
    (hb : Function.Surjective b) {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime]
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (hm : ¬irrelevantIdeal K b ≤ 𝔭)
    (hdim : (hilbertPoly b 𝔭).totalDegree + 1 ≤ Nat.card κ) :
    ∃ m : ℕ, Associated (resForm b K d 𝔭) (elimForm K b d 𝔭 ^ m) := by
  obtain ⟨⟨k₀, hk₀⟩, -⟩ := associated_resForm_prod (d := d) hb h𝔭 hdim
  obtain ⟨k₁, hk₁⟩ := exists_elimIdeal_le_annihilator (d := d) 𝔭
  have hdvd : ∀ g ∈ elimIdeal K b d 𝔭, ∃ N : ℕ, resForm b K d 𝔭 ∣ g ^ N := fun g hg ↦ by
    obtain ⟨N, hN⟩ := Module.exists_charForm_dvd_pow (hk₁ (k₀ ⊔ k₁) le_sup_right hg)
    exact ⟨N, (hk₀ (k₀ ⊔ k₁) le_sup_left).symm.dvd.trans hN⟩
  have hE := isPrime_elimIdeal (d := d) hm
  obtain ⟨p, hpE, hp⟩ :=
    hE.exists_mem_prime_of_ne_bot (elimIdeal_ne_bot_of_totalDegree hb h𝔭 hdim)
  obtain ⟨N, hN⟩ := hdvd p hpE
  obtain ⟨m, -, hres⟩ := (dvd_prime_pow hp N).mp hN
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · exact ⟨0, by simpa using hres⟩
  have hpres : p ∣ resForm b K d 𝔭 := (dvd_pow_self p hm0.ne').trans hres.symm.dvd
  have hspan : elimIdeal K b d 𝔭 = Ideal.span {p} := by
    refine le_antisymm (fun g hg ↦ ?_) ((Ideal.span_singleton_le_iff_mem _).2 hpE)
    obtain ⟨N', hN'⟩ := hdvd g hg
    exact Ideal.mem_span_singleton.2 (hp.dvd_of_dvd_pow (hpres.trans hN'))
  have hprinc : (elimIdeal K b d 𝔭).IsPrincipal := by
    rw [hspan]
    exact ⟨⟨p, rfl⟩⟩
  have hel := span_elimForm_of_isPrincipal hprinc
  rw [hspan, Ideal.span_singleton_eq_span_singleton] at hel
  exact ⟨m, hres.trans (hel.symm.pow_pow)⟩

variable {L : Type u} [Field L] [IsAlgClosed L] {κ : Type u} [Finite κ]
  {d : Option κ → ι → ℕ}

/-- **Prop. 2.16 for resultant forms**: specializing all forms but the first, `res_d(I)` becomes
`c ∏_j U(z_j)`. -/
theorem exists_specEval_resForm_eq (hb : Function.Surjective b) {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree + 1 ≤ Nat.card (Option κ))
    (φ : K →+* L) (y : GenericVar b (fun l : κ ↦ d (some l)) → L) :
    specEval b φ y (resForm b K d I) ∈ pointSubmonoid b L (d none) := by
  obtain ⟨-, S, ℓ, hS, -, hassoc⟩ := associated_resForm_prod (d := d) hb hI hdim
  obtain ⟨v, hv⟩ := hassoc.symm
  rw [← hv, map_mul]
  obtain ⟨c, -, hc⟩ := isUnit_iff_eq_C_of_isReduced.1 v.isUnit
  refine Submonoid.mul_mem _ ?_ (by rw [hc, specEval]; simpa using C_mem_pointSubmonoid _)
  rw [map_prod]
  refine Submonoid.prod_mem _ fun 𝔭 h𝔭 ↦ ?_
  obtain ⟨h𝔭p, h𝔭h, -, hm, h𝔭d⟩ := (hS 𝔭).mp h𝔭
  obtain ⟨m, hm'⟩ := exists_associated_resForm_elimForm_pow (d := d) hb h𝔭h hm h𝔭d.le
  obtain ⟨w, hw⟩ := hm'.symm
  rw [map_pow, ← hw, map_mul, map_pow]
  obtain ⟨c', -, hc'⟩ := isUnit_iff_eq_C_of_isReduced.1 w.isUnit
  refine Submonoid.pow_mem _ (Submonoid.mul_mem _ (Submonoid.pow_mem _ ?_ _)
    (by rw [hc', specEval]; simpa using C_mem_pointSubmonoid _)) _
  obtain ⟨c'', Z, hZ, he⟩ := exists_specEval_elimForm_eq hb h𝔭h d φ y
  exact ⟨c'', Z, hZ, he⟩

end Resultant

end MvPolynomial
