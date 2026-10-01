/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.Ideal.LengthPow
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Basic.Real.Basic

-- Used only inside proofs.
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

/-!
# The multiplicity estimate of the product theorem

This file proves the multiplicity side of the product theorem, Rémond 2001 (*Sur le théorème du
produit*), Prop. 3.1 and Lemma 3.1, in one inequality between lengths and without Samuel
multiplicities.

Let `B = R[X_σ]`, let `𝔭` be a prime of `B`, and let `Q_1, …, Q_d ∈ 𝔭` and variables
`X_{v_1}, …, X_{v_d}` be such that `∂Q_β/∂X_{v_α} ∈ 𝔭` exactly when `α ≠ β`. Rémond obtains these
from the exact sequences of Kähler differentials, with `d = ht 𝔭`; they make the completion of
`B_𝔭` a power series ring in the `Q_α`. Give the direction `v_α` the weight `1/δ_α`. If every
`P ∈ I` vanishes at the generic point of `𝔭` to weighted order `> ε` in the directions `v_α`, then
for any `x_1, …, x_d ∈ I`
`ε^d ∏_α δ_α ≤ ℓ(B_𝔭/(x_1, …, x_d)B_𝔭)`.

With `d = ht 𝔭` this is Rémond's `e_{I B_𝔭}(B_𝔭) ≥ ε^{ht 𝔭} ∏ δ` combined with his Lemma 3.1
`e_{I B_𝔭}(B_𝔭) ≤ ℓ(B_𝔭/(x)B_𝔭)`, which is how the two are used.

## The Taylor map

The vanishing is expressed through the **Taylor map at the generic point of `𝔭`**,
`taylorAtPrime 𝔭 v : B → (B/𝔭)[Z_1, …, Z_d]`, `X_s ↦ (X_s mod 𝔭) + ∑_{v_α = s} Z_α`. This is a
ring homomorphism, so Leibniz rules come for free. The coefficient of `Z^μ` in
`taylorAtPrime 𝔭 v P` is the Hasse derivative `Δ^{v μ} P = ∂^{v μ} P / μ!` modulo `𝔭` (compare
`MvPolynomial.coeff_taylorAt` in `DiophantineApproximation.PolynomialIndex`, the translation to a
point of `R^σ`). Only degrees `≤ 1` are needed here:
the constant term is `P mod 𝔭` (`constantCoeff_taylorAtPrime`) and the coefficient of `Z_α` is
`∂P/∂X_{v_α} mod 𝔭` (`coeff_single_taylorAtPrime`). The hypothesis on `I` reads
`taylorAtPrime 𝔭 v (I) ⊆ (Z^μ : ∑ μ_α/δ_α > ε)`.

## The argument

* **Upper bound** (`Ideal.localLength_span_range_pow_le`): `ℓ(B_𝔭/(x)^n) ≤ C(n - 1 + d, d) ℓ`.
* **Lower bound.** `I^n` maps into the monomials of weight `> nε`. The monomials `Q^γ` with
  `∑ γ_α/δ_α ≤ nε`, taken in order of decreasing degree, form a chain with colon ideals in `𝔭`:
  the coefficient of `Z^γ` in `taylorAtPrime 𝔭 v (y Q^γ)` is `y ∏ (∂Q_α/∂X_{v_α})^{γ_α} ≠ 0`
  modulo `𝔭` for `y ∉ 𝔭`, and it vanishes on everything earlier in the chain
  (`card_le_localLength_comap_weightIdeal`). There are at least `C(K + d, d) ∏ δ_α` such `γ`,
  `K = ⌊nε⌋ - d` (`exists_finset_weight_le`).
* Comparing and letting `n → ∞` gives `ε^d ∏ δ_α ≤ ℓ` (`prod_mul_pow_le_localLength`).

Nothing uses the characteristic: in characteristic `0` Rémond's hypothesis `∂^κ P ∈ 𝔭` is the
same as the vanishing of the Hasse derivatives, and the characteristic enters only through the
existence of the `Q_α` (Kähler differentials), which is not formalized here.

## Main definitions

* `MvPolynomial.monomialSpan T`: the ideal spanned by the monomials with exponents in `T`.
* `MvPolynomial.degIdeal t`, `MvPolynomial.weightIdeal c a`: the monomials of degree `≥ t`, and
  of `c`-weight `> a`.
* `MvPolynomial.taylorAtPrime 𝔭 v`: the Taylor map at the generic point of `𝔭`.

## Main statements

* `MvPolynomial.card_le_localLength_comap_weightIdeal`: the chain bound.
* `MvPolynomial.prod_mul_pow_le_localLength`: `ε^d ∏ δ_α ≤ ℓ(B_𝔭/(x)B_𝔭)`.
-/

@[expose] public section

open Finset Set

namespace MvPolynomial

section MonomialIdeal

variable {τ S : Type*} [CommRing S]

/-- The ideal spanned by the monomials `Z^μ` with `μ ∈ T`. -/
noncomputable def monomialSpan (T : Set (τ →₀ ℕ)) : Ideal (MvPolynomial τ S) :=
  Ideal.span ((fun μ ↦ monomial μ (1 : S)) '' T)

theorem monomial_mem_monomialSpan {T : Set (τ →₀ ℕ)} {μ : τ →₀ ℕ} (hμ : μ ∈ T) (a : S) :
    monomial μ a ∈ (monomialSpan T : Ideal (MvPolynomial τ S)) := by
  have : monomial μ a = C a * monomial μ 1 := by rw [C_mul_monomial, mul_one]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨μ, hμ, rfl⟩)

theorem monomialSpan_mul_le {T U V : Set (τ →₀ ℕ)} (h : ∀ μ ∈ T, ∀ ν ∈ U, μ + ν ∈ V) :
    monomialSpan T * monomialSpan U ≤ (monomialSpan V : Ideal (MvPolynomial τ S)) := by
  rw [monomialSpan, monomialSpan, Ideal.span_mul_span, Ideal.span_le]
  rintro _ ⟨_, ⟨μ, hμ, rfl⟩, _, ⟨ν, hν, rfl⟩, rfl⟩
  exact Ideal.subset_span ⟨μ + ν, h μ hμ ν hν, by simp [monomial_mul_monomial]⟩

theorem monomialSpan_mono {T U : Set (τ →₀ ℕ)} (h : T ⊆ U) :
    (monomialSpan T : Ideal (MvPolynomial τ S)) ≤ monomialSpan U :=
  Ideal.span_mono (image_mono h)

theorem coeff_eq_zero_of_mem_monomialSpan {T : Set (τ →₀ ℕ)} {F : MvPolynomial τ S}
    (hF : F ∈ monomialSpan T) {μ : τ →₀ ℕ} (hμ : ∀ ν ∈ T, ¬ ν ≤ μ) : F.coeff μ = 0 := by
  by_contra h
  obtain ⟨ν, hν, hle⟩ := mem_ideal_span_monomial_image.mp hF μ (mem_support_iff.mpr h)
  exact hμ ν hν hle

/-- The ideal of the monomials of degree `≥ t`, i.e. `(Z_1, …, Z_d)^t`. -/
noncomputable abbrev degIdeal (t : ℕ) : Ideal (MvPolynomial τ S) :=
  monomialSpan {μ | t ≤ μ.degree}

theorem degIdeal_mul_le (a b : ℕ) :
    degIdeal a * degIdeal b ≤ (degIdeal (a + b) : Ideal (MvPolynomial τ S)) :=
  monomialSpan_mul_le fun μ hμ ν hν ↦ by
    simp only [mem_ofPred_eq, map_add] at hμ hν ⊢
    omega

theorem degIdeal_anti {a b : ℕ} (h : a ≤ b) :
    (degIdeal b : Ideal (MvPolynomial τ S)) ≤ degIdeal a :=
  monomialSpan_mono fun _ hμ ↦ h.trans hμ

theorem degIdeal_zero : (degIdeal 0 : Ideal (MvPolynomial τ S)) = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← C_1, C_apply]
  exact monomial_mem_monomialSpan (by simp) 1

theorem sub_C_constantCoeff_mem_degIdeal_one (F : MvPolynomial τ S) :
    F - C (constantCoeff F) ∈ (degIdeal 1 : Ideal (MvPolynomial τ S)) := by
  classical
  refine mem_ideal_span_monomial_image.mpr fun μ hμ ↦ ⟨μ, ?_, le_rfl⟩
  rw [mem_ofPred_eq, Nat.one_le_iff_ne_zero]
  intro h0
  rw [(Finsupp.degree_eq_zero_iff μ).mp h0, mem_support_iff, coeff_sub, coeff_zero_C,
    ← constantCoeff_eq, sub_self] at hμ
  exact hμ rfl

theorem mem_degIdeal_one_of_constantCoeff {F : MvPolynomial τ S} (hF : constantCoeff F = 0) :
    F ∈ (degIdeal 1 : Ideal (MvPolynomial τ S)) := by
  simpa [hF] using sub_C_constantCoeff_mem_degIdeal_one F

/-- A nonzero exponent of degree `≤ 1` is a unit vector. -/
theorem eq_single_of_degree_le_one {μ : τ →₀ ℕ} (h : μ.degree ≤ 1) (h0 : μ ≠ 0) :
    ∃ β, μ = Finsupp.single β 1 := by
  obtain ⟨β, hβ⟩ := Finsupp.ne_iff.mp h0
  refine ⟨β, ?_⟩
  have hle : Finsupp.single β 1 ≤ μ := by
    intro i
    by_cases hi : i = β
    · subst hi
      simp only [Finsupp.single_eq_same, Finsupp.coe_zero, Pi.zero_apply] at hβ ⊢
      omega
    · simp [Finsupp.single_eq_of_ne hi]
  have hdeg : (μ - Finsupp.single β 1).degree = 0 := by
    have := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
    rw [map_add, Finsupp.degree_single] at this
    omega
  rw [Finsupp.degree_eq_zero_iff, tsub_eq_zero_iff_le] at hdeg
  exact le_antisymm hdeg hle

/-- A polynomial with no constant term whose linear part is `u Z_α` agrees with `u Z_α` up to
degree `≥ 2`. -/
theorem sub_C_mul_X_mem_degIdeal_two [DecidableEq τ] {F : MvPolynomial τ S} {α : τ} {u : S}
    (h0 : constantCoeff F = 0)
    (h1 : ∀ β, F.coeff (Finsupp.single β 1) = if β = α then u else 0) :
    F - C u * X α ∈ (degIdeal 2 : Ideal (MvPolynomial τ S)) := by
  refine mem_ideal_span_monomial_image.mpr fun μ hμ ↦ ⟨μ, ?_, le_rfl⟩
  rw [mem_ofPred_eq]
  by_contra hlt
  rw [mem_support_iff] at hμ
  apply hμ
  by_cases hμ0 : μ = 0
  · subst hμ0
    rw [coeff_sub, ← constantCoeff_eq, h0, ← constantCoeff_eq]
    simp
  · obtain ⟨β, rfl⟩ := eq_single_of_degree_le_one (by omega) hμ0
    rw [coeff_sub, h1, coeff_C_mul, coeff_X]
    by_cases hβ : β = α
    · subst hβ
      simp
    · simp [hβ, Finsupp.single_left_inj one_ne_zero, Ne.symm hβ]

/-- `A` and `B` agree to order `t`: both lie in `(Z)^t` and their difference in `(Z)^{t+1}`. -/
def AgreeToOrder (t : ℕ) (A B : MvPolynomial τ S) : Prop :=
  A ∈ (degIdeal t : Ideal (MvPolynomial τ S)) ∧ B ∈ (degIdeal t : Ideal (MvPolynomial τ S)) ∧
    A - B ∈ (degIdeal (t + 1) : Ideal (MvPolynomial τ S))

theorem AgreeToOrder.mul {a b : ℕ} {A B A' B' : MvPolynomial τ S} (h : AgreeToOrder a A B)
    (h' : AgreeToOrder b A' B') : AgreeToOrder (a + b) (A * A') (B * B') := by
  refine ⟨degIdeal_mul_le a b (Ideal.mul_mem_mul h.1 h'.1),
    degIdeal_mul_le a b (Ideal.mul_mem_mul h.2.1 h'.2.1), ?_⟩
  have : A * A' - B * B' = A * (A' - B') + (A - B) * B' := by ring
  rw [this]
  refine Ideal.add_mem _ ?_ ?_
  · have := degIdeal_mul_le (S := S) a (b + 1) (Ideal.mul_mem_mul h.1 h'.2.2)
    rwa [← add_assoc] at this
  · have := degIdeal_mul_le (S := S) (a + 1) b (Ideal.mul_mem_mul h.2.2 h'.2.1)
    rwa [add_right_comm] at this

theorem AgreeToOrder.pow {a : ℕ} {A B : MvPolynomial τ S} (h : AgreeToOrder a A B) (n : ℕ) :
    AgreeToOrder (n * a) (A ^ n) (B ^ n) := by
  induction n with
  | zero =>
    simp only [zero_mul, pow_zero]
    exact ⟨by simp [degIdeal_zero], by simp [degIdeal_zero], by simp⟩
  | succ n ih =>
    rw [pow_succ, pow_succ, add_mul, one_mul]
    exact ih.mul h

theorem AgreeToOrder.prod {ι : Type*} (s : Finset ι) {t : ι → ℕ} {A B : ι → MvPolynomial τ S}
    (h : ∀ i ∈ s, AgreeToOrder (t i) (A i) (B i)) :
    AgreeToOrder (∑ i ∈ s, t i) (∏ i ∈ s, A i) (∏ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    exact ⟨by simp [degIdeal_zero], by simp [degIdeal_zero], by simp⟩
  | insert i s hi ih =>
    rw [sum_insert hi, prod_insert hi, prod_insert hi]
    exact (h i (mem_insert_self i s)).mul (ih fun j hj ↦ h j (mem_insert_of_mem hj))

/-- The largest ideal on which the coefficient of `Z^γ` vanishes. -/
noncomputable def annCoeff (γ : τ →₀ ℕ) : Ideal (MvPolynomial τ S) where
  carrier := {H | ∀ G, (G * H).coeff γ = 0}
  add_mem' {a b} ha hb G := by
    rw [mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ha, hb, add_zero]
  zero_mem' G := by simp
  smul_mem' c H hH G := by rw [smul_eq_mul, ← mul_assoc]; exact hH _

theorem coeff_eq_zero_of_mem_annCoeff {γ : τ →₀ ℕ} {H : MvPolynomial τ S}
    (hH : H ∈ (annCoeff γ : Ideal (MvPolynomial τ S))) : H.coeff γ = 0 := by
  simpa using (hH : ∀ G, (G * H).coeff γ = 0) 1

theorem monomialSpan_le_annCoeff {T : Set (τ →₀ ℕ)} {γ : τ →₀ ℕ} (h : ∀ ν ∈ T, ¬ ν ≤ γ) :
    (monomialSpan T : Ideal (MvPolynomial τ S)) ≤ annCoeff γ := fun _ hH ↦ by
  change ∀ G, _
  exact fun G ↦ coeff_eq_zero_of_mem_monomialSpan (Ideal.mul_mem_left _ G hH) h

theorem degIdeal_le_annCoeff {t : ℕ} {γ : τ →₀ ℕ} (h : γ.degree < t) :
    (degIdeal t : Ideal (MvPolynomial τ S)) ≤ annCoeff γ :=
  monomialSpan_le_annCoeff fun ν hν hle ↦ by
    have := Finsupp.degree_mono hle
    simp only [mem_ofPred_eq] at hν
    omega

theorem monomial_mem_annCoeff {γ μ : τ →₀ ℕ} (h : ¬ μ ≤ γ) (a : S) :
    monomial μ a ∈ (annCoeff γ : Ideal (MvPolynomial τ S)) := by
  change ∀ G, _
  intro G
  simp [coeff_mul_monomial', h]

/-- The ideal of the monomials of weight `> a` for the weights `c`. -/
noncomputable abbrev weightIdeal (c : τ → ℝ) (a : ℝ) : Ideal (MvPolynomial τ S) :=
  monomialSpan {μ | a < Finsupp.weight c μ}

theorem weightIdeal_mul_le (c : τ → ℝ) (a b : ℝ) :
    weightIdeal c a * weightIdeal c b ≤ (weightIdeal c (a + b) : Ideal (MvPolynomial τ S)) :=
  monomialSpan_mul_le fun μ hμ ν hν ↦ by
    simp only [mem_ofPred_eq, map_add] at hμ hν ⊢
    linarith

theorem weight_mono_of_nonneg {c : τ → ℝ} (hc : ∀ i, 0 ≤ c i) {μ ν : τ →₀ ℕ} (h : μ ≤ ν) :
    Finsupp.weight c μ ≤ Finsupp.weight c ν := by
  rw [← tsub_add_cancel_of_le h, map_add, le_add_iff_nonneg_left, Finsupp.weight_apply]
  exact Finsupp.sum_nonneg fun i _ ↦ smul_nonneg (Nat.zero_le _) (hc i)

theorem weightIdeal_le_annCoeff {c : τ → ℝ} (hc : ∀ i, 0 ≤ c i) {a : ℝ} {γ : τ →₀ ℕ}
    (h : Finsupp.weight c γ ≤ a) :
    (weightIdeal c a : Ideal (MvPolynomial τ S)) ≤ annCoeff γ :=
  monomialSpan_le_annCoeff fun ν hν hle ↦ by
    have := weight_mono_of_nonneg hc hle
    simp only [mem_ofPred_eq] at hν
    linarith

theorem pow_succ_le_weightIdeal (c : τ → ℝ) {a : ℝ} {J : Ideal (MvPolynomial τ S)}
    (hJ : J ≤ weightIdeal c a) (n : ℕ) : J ^ (n + 1) ≤ weightIdeal c ((n + 1) * a) := by
  induction n with
  | zero => simpa using hJ
  | succ n ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono ih hJ).trans ((weightIdeal_mul_le c _ _).trans ?_)
    refine monomialSpan_mono fun μ hμ ↦ ?_
    simp only [mem_ofPred_eq, Nat.cast_add, Nat.cast_one] at hμ ⊢
    linarith

end MonomialIdeal

section Taylor

variable {σ R : Type*} [CommRing R] [DecidableEq σ] {d : ℕ}

/-- **The Taylor map at the generic point of `𝔭`** in the directions `v_1, …, v_d`:
`X_s ↦ (X_s mod 𝔭) + ∑_{v_α = s} Z_α`, into polynomials in `Z_1, …, Z_d` over `B/𝔭`. The
coefficient of `Z^μ` in the image of `P` is the Hasse derivative `Δ^{v μ} P` modulo `𝔭`. -/
noncomputable def taylorAtPrime (𝔭 : Ideal (MvPolynomial σ R)) (v : Fin d → σ) :
    MvPolynomial σ R →ₐ[R] MvPolynomial (Fin d) (MvPolynomial σ R ⧸ 𝔭) :=
  aeval fun s ↦ C (Ideal.Quotient.mk 𝔭 (X s)) + ∑ α with v α = s, X α

variable (𝔭 : Ideal (MvPolynomial σ R)) (v : Fin d → σ)

theorem taylorAtPrime_X (s : σ) :
    taylorAtPrime 𝔭 v (X s) = C (Ideal.Quotient.mk 𝔭 (X s)) + ∑ α with v α = s, X α :=
  aeval_X _ _

/-- The constant term of the Taylor map is reduction modulo `𝔭`. -/
theorem constantCoeff_taylorAtPrime (P : MvPolynomial σ R) :
    constantCoeff (taylorAtPrime 𝔭 v P) = Ideal.Quotient.mk 𝔭 P := by
  induction P using MvPolynomial.induction_on with
  | C r =>
    rw [taylorAtPrime, aeval_C, MvPolynomial.algebraMap_apply, constantCoeff_C]
    rfl
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p s hp =>
    rw [map_mul, map_mul, hp, taylorAtPrime_X, map_add, constantCoeff_C, map_sum]
    simp

omit [DecidableEq σ] in
theorem coeff_single_one_mul (α : Fin d) (F G : MvPolynomial (Fin d) (MvPolynomial σ R ⧸ 𝔭)) :
    (F * G).coeff (Finsupp.single α 1) =
      constantCoeff F * G.coeff (Finsupp.single α 1) +
        F.coeff (Finsupp.single α 1) * constantCoeff G := by
  rw [coeff_mul, Finsupp.antidiagonal_single, sum_map]
  simp [Finset.Nat.antidiagonal_succ, constantCoeff_eq]

/-- The linear part of the Taylor map is the gradient modulo `𝔭`. -/
theorem coeff_single_taylorAtPrime (α : Fin d) (P : MvPolynomial σ R) :
    (taylorAtPrime 𝔭 v P).coeff (Finsupp.single α 1) =
      Ideal.Quotient.mk 𝔭 (pderiv (v α) P) := by
  induction P using MvPolynomial.induction_on with
  | C r =>
    rw [taylorAtPrime, aeval_C, MvPolynomial.algebraMap_apply,
      coeff_C_of_ne_zero (Finsupp.single_ne_zero.mpr one_ne_zero), pderiv_C, map_zero]
  | add p q hp hq =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, map_add, map_add]
  | mul_X p s hp =>
    rw [show taylorAtPrime 𝔭 v (p * X s) = taylorAtPrime 𝔭 v p * taylorAtPrime 𝔭 v (X s) from
        map_mul _ _ _, coeff_single_one_mul, hp, constantCoeff_taylorAtPrime,
      constantCoeff_taylorAtPrime, taylorAtPrime_X, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply,
      coeff_C_of_ne_zero (Finsupp.single_ne_zero.mpr one_ne_zero), zero_add, coeff_sum,
      Derivation.leibniz, pderiv_X]
    simp only [coeff_X, Finsupp.single_left_inj one_ne_zero, sum_ite_eq', mem_filter,
      smul_eq_mul, map_add, map_mul, Pi.single_apply]
    by_cases h : v α = s
    · subst h
      simp [mul_comm]
    · simp [h, Ne.symm h, mul_comm]

variable {𝔭 v}

/-- `taylorAtPrime 𝔭 v (Q)` agrees with `u Z_α` to first order, where `u = ∂Q/∂X_{v_α} mod 𝔭`,
when `Q ∈ 𝔭` and `∂Q/∂X_{v_β} ∈ 𝔭` for `β ≠ α`. -/
theorem agreeToOrder_taylorAtPrime {Q : MvPolynomial σ R} {α : Fin d} (hQ : Q ∈ 𝔭)
    (hoff : ∀ β, β ≠ α → pderiv (v β) Q ∈ 𝔭) :
    AgreeToOrder 1 (taylorAtPrime 𝔭 v Q)
      (C (Ideal.Quotient.mk 𝔭 (pderiv (v α) Q)) * X α) := by
  refine ⟨mem_degIdeal_one_of_constantCoeff ?_, ?_, sub_C_mul_X_mem_degIdeal_two ?_ fun β ↦ ?_⟩
  · rw [constantCoeff_taylorAtPrime, Ideal.Quotient.eq_zero_iff_mem]
    exact hQ
  · rw [X, C_mul_monomial, mul_one]
    exact monomial_mem_monomialSpan (by simp) _
  · rw [constantCoeff_taylorAtPrime, Ideal.Quotient.eq_zero_iff_mem]
    exact hQ
  · rw [coeff_single_taylorAtPrime]
    split_ifs with h
    · rw [h]
    · rw [Ideal.Quotient.eq_zero_iff_mem]
      exact hoff β h

end Taylor

section Chain

variable {σ R : Type*} [CommRing R] [DecidableEq σ] {d : ℕ}
  {𝔭 : Ideal (MvPolynomial σ R)} [𝔭.IsPrime] {v : Fin d → σ} {Q : Fin d → MvPolynomial σ R}

omit [𝔭.IsPrime] in
/-- The image of a monomial `Q^γ` agrees with `(∏ u_α^{γ_α}) Z^γ` to order `|γ|`, where
`u_α = ∂Q_α/∂X_{v_α} mod 𝔭`. -/
theorem agreeToOrder_taylorAtPrime_prod (hQ : ∀ α, Q α ∈ 𝔭)
    (hoff : ∀ α β, α ≠ β → pderiv (v α) (Q β) ∈ 𝔭) (γ : Fin d →₀ ℕ) :
    AgreeToOrder γ.degree (taylorAtPrime 𝔭 v (∏ α, Q α ^ γ α))
      (C (∏ α, Ideal.Quotient.mk 𝔭 (pderiv (v α) (Q α)) ^ γ α) * monomial γ 1) := by
  have h := AgreeToOrder.prod (univ : Finset (Fin d)) (t := fun α ↦ γ α * 1)
    (A := fun α ↦ taylorAtPrime 𝔭 v (Q α) ^ γ α)
    (B := fun α ↦ (C (Ideal.Quotient.mk 𝔭 (pderiv (v α) (Q α))) * X α) ^ γ α)
    fun α _ ↦ (agreeToOrder_taylorAtPrime (hQ α) fun β hβ ↦ hoff β α hβ).pow (γ α)
  simp only [mul_one] at h
  rw [Finsupp.degree_eq_sum, map_prod]
  simp only [map_pow]
  convert h using 2
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _, map_prod,
    ← prod_mul_distrib]
  simp only [map_pow, mul_pow]

theorem eq_of_le_of_degree_le {τ : Type*} {μ ν : τ →₀ ℕ} (h : μ ≤ ν) (hd : ν.degree ≤ μ.degree) :
    μ = ν := by
  have := congrArg Finsupp.degree (tsub_add_cancel_of_le h)
  rw [map_add] at this
  have h0 : (ν - μ).degree = 0 := by omega
  rw [Finsupp.degree_eq_zero_iff, tsub_eq_zero_iff_le] at h0
  exact le_antisymm h h0

/-- **The chain bound.** Suppose `Q_α ∈ 𝔭`, with `∂Q_β/∂X_{v_α} ∈ 𝔭` exactly when `α ≠ β`. For
nonnegative weights `c` and any finite set `T` of exponents of weight `≤ N`, the ideal of the
polynomials whose Taylor expansion at `𝔭` has only terms of weight `> N` has localized length
`≥ #T`. -/
theorem card_le_localLength_comap_weightIdeal (hQ : ∀ α, Q α ∈ 𝔭)
    (hoff : ∀ α β, α ≠ β → pderiv (v α) (Q β) ∈ 𝔭) (hdiag : ∀ α, pderiv (v α) (Q α) ∉ 𝔭)
    {c : Fin d → ℝ} (hc : ∀ α, 0 ≤ c α) {N : ℝ} (T : Finset (Fin d →₀ ℕ))
    (hT : ∀ γ ∈ T, Finsupp.weight c γ ≤ N) :
    (T.card : ℕ∞) ≤ Ideal.localLength 𝔭 ((weightIdeal c N).comap (taylorAtPrime 𝔭 v)) := by
  classical
  set Ψ := taylorAtPrime 𝔭 v
  set u : Fin d → MvPolynomial σ R ⧸ 𝔭 := fun α ↦ Ideal.Quotient.mk 𝔭 (pderiv (v α) (Q α))
  set l := T.toList.mergeSort fun a b ↦ decide (b.degree ≤ a.degree)
  have hperm : l.Perm T.toList := List.mergeSort_perm _ _
  have hsort : l.Pairwise fun a b ↦ decide (b.degree ≤ a.degree) := List.pairwise_mergeSort
    (fun a b c hab hbc ↦ by simp only [decide_eq_true_eq] at *; omega)
    (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _
  have hnodup : l.Nodup := hperm.nodup_iff.mpr (nodup_toList T)
  have hlen : l.length = T.card := hperm.length_eq.trans (length_toList T)
  have hmem : ∀ k (hk : k < l.length), l[k] ∈ T := fun k hk ↦
    mem_toList.mp (hperm.mem_iff.mp (List.getElem_mem hk))
  let f : ℕ → MvPolynomial σ R := fun k ↦ ∏ α, Q α ^ (l.getD k 0) α
  rw [← hlen]
  refine Ideal.le_localLength_of_colon_le _ f l.length fun k hk y hy ↦ ?_
  by_contra hy𝔭
  set γ := l[k]
  have hfk : f k = ∏ α, Q α ^ γ α := by
    simp [f, γ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  -- Everything before `f k` in the chain lies in the ideal where the coefficient of `Z^γ`
  -- vanishes.
  have hZ : (weightIdeal c N).comap Ψ ⊔ Ideal.span (f '' Set.Iio k) ≤
      (annCoeff γ).comap Ψ := by
    refine sup_le (Ideal.comap_mono (weightIdeal_le_annCoeff hc (hT γ (hmem k hk))))
      (Ideal.span_le.mpr ?_)
    rintro _ ⟨j, hj, rfl⟩
    have hjk : j < l.length := (Set.mem_Iio.mp hj).trans hk
    have hj' : f j = ∏ α, Q α ^ l[j] α := by
      simp [f, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjk]
    have hdeg : γ.degree ≤ (l[j]).degree := by
      have := List.pairwise_iff_getElem.mp hsort j k hjk hk (Set.mem_Iio.mp hj)
      simpa using this
    have hne : l[j] ≠ γ := fun h ↦ (Set.mem_Iio.mp hj).ne
      ((List.Nodup.getElem_inj_iff hnodup).mp h)
    obtain ⟨-, -, hdiff⟩ := agreeToOrder_taylorAtPrime_prod hQ hoff l[j]
    rw [SetLike.mem_coe, Ideal.mem_comap, hj']
    have hsplit : Ψ (∏ α, Q α ^ l[j] α) =
        (Ψ (∏ α, Q α ^ l[j] α) - C (∏ α, u α ^ l[j] α) * monomial l[j] 1) +
          monomial l[j] (∏ α, u α ^ l[j] α) := by
      rw [C_mul_monomial, mul_one, sub_add_cancel]
    rw [hsplit]
    refine Ideal.add_mem _ (degIdeal_le_annCoeff (t := (l[j]).degree + 1) (by omega) hdiff)
      (monomial_mem_annCoeff (fun hle ↦ hne (eq_of_le_of_degree_le hle hdeg)) _)
  have hyf := hZ (Submodule.mem_colon_singleton.mp hy)
  rw [Ideal.mem_comap, smul_eq_mul, map_mul, hfk] at hyf
  have hcoeff := coeff_eq_zero_of_mem_annCoeff hyf
  -- On the other hand the coefficient of `Z^γ` in `Ψ (y Q^γ)` is `y ∏ u^γ ≠ 0` modulo `𝔭`.
  obtain ⟨hΨ, -, hdiff⟩ := agreeToOrder_taylorAtPrime_prod hQ hoff γ
  have hsplit : Ψ y * Ψ (∏ α, Q α ^ γ α) =
      C (Ideal.Quotient.mk 𝔭 y) * (C (∏ α, u α ^ γ α) * monomial γ 1) +
        (C (Ideal.Quotient.mk 𝔭 y) *
            (Ψ (∏ α, Q α ^ γ α) - C (∏ α, u α ^ γ α) * monomial γ 1) +
          (Ψ y - C (constantCoeff (Ψ y))) * Ψ (∏ α, Q α ^ γ α)) := by
    rw [constantCoeff_taylorAtPrime]
    ring
  have hrest : C (Ideal.Quotient.mk 𝔭 y) *
        (Ψ (∏ α, Q α ^ γ α) - C (∏ α, u α ^ γ α) * monomial γ 1) +
      (Ψ y - C (constantCoeff (Ψ y))) * Ψ (∏ α, Q α ^ γ α) ∈
        (degIdeal (γ.degree + 1) : Ideal (MvPolynomial (Fin d) (MvPolynomial σ R ⧸ 𝔭))) := by
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hdiff) ?_
    have := degIdeal_mul_le (S := MvPolynomial σ R ⧸ 𝔭) 1 γ.degree
      (Ideal.mul_mem_mul (sub_C_constantCoeff_mem_degIdeal_one (Ψ y)) hΨ)
    rwa [add_comm] at this
  rw [hsplit, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_eq_zero_of_mem_annCoeff
    (degIdeal_le_annCoeff (Nat.lt_succ_self _) hrest), add_zero, ← mul_assoc, ← map_mul,
    coeff_C_mul, coeff_monomial, ite_eq_left_iff.mpr (fun h ↦ absurd rfl h), mul_one] at hcoeff
  refine mul_ne_zero ?_ (prod_ne_zero_iff.mpr fun α _ ↦ pow_ne_zero _ ?_) hcoeff
  · rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  · rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hdiag α

end Chain

section Count

/-- **Counting exponents of bounded weight.** For positive integers `δ_α` there are at least
`C(K + d, d) ∏ δ_α` exponents `γ ∈ ℕ^d` with `∑ γ_α/δ_α ≤ K + d`: write `γ_α = δ_α q_α + r_α`
with `|q| ≤ K` and `0 ≤ r_α < δ_α`. -/
theorem exists_finset_weight_le {d : ℕ} (δ : Fin d → ℕ) (hδ : ∀ α, 0 < δ α) (K : ℕ) :
    ∃ T : Finset (Fin d →₀ ℕ), T.card = (K + d).choose d * ∏ α, δ α ∧
      ∀ γ ∈ T, Finsupp.weight (fun α ↦ ((δ α : ℝ))⁻¹) γ ≤ K + d := by
  classical
  let M : Finset (Multiset (Fin d)) := (range (K + 1)).biUnion fun i ↦
    (univ : Finset (Sym (Fin d) i)).map ⟨fun m ↦ m.1, Sym.coe_injective⟩
  have hM : ∀ m ∈ M, Multiset.card m ≤ K := by
    intro m hm
    simp only [M, Finset.mem_biUnion, Finset.mem_range, Finset.mem_map, Finset.mem_univ,
      true_and] at hm
    obtain ⟨i, hi, s, rfl⟩ := hm
    change Multiset.card s.1 ≤ K
    rw [s.2]
    omega
  have hMcard : M.card = (K + d).choose d := by
    rw [card_biUnion]
    · simp only [card_map, card_univ, Sym.card_sym_eq_multichoose, Fintype.card_fin]
      exact Nat.sum_range_multichoose K d
    · intro i _ j _ hij
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro m hi hj
      simp only [Finset.mem_map, Finset.mem_univ, true_and] at hi hj
      obtain ⟨s, rfl⟩ := hi
      obtain ⟨t, ht⟩ := hj
      have : Multiset.card t.1 = Multiset.card s.1 := congrArg Multiset.card ht
      rw [s.2, t.2] at this
      exact hij this.symm
  let g : Multiset (Fin d) × (Fin d → ℕ) → Fin d →₀ ℕ := fun p ↦
    Finsupp.equivFunOnFinite.symm fun α ↦ δ α * p.1.count α + p.2 α
  let D := M ×ˢ Fintype.piFinset fun α ↦ range (δ α)
  refine ⟨D.image g, ?_, ?_⟩
  · rw [card_image_of_injOn, card_product, hMcard, Fintype.card_piFinset]
    · simp
    rintro ⟨m, r⟩ hmr ⟨m', r'⟩ hmr' h
    simp only [D, coe_product, Set.mem_prod, mem_coe, Fintype.mem_piFinset, Finset.mem_range]
      at hmr hmr'
    have hα : ∀ α, δ α * m.count α + r α = δ α * m'.count α + r' α := fun α ↦ by
      simpa [g] using congrArg (· α) h
    have hdiv : ∀ α, m.count α = m'.count α ∧ r α = r' α := fun α ↦ by
      have h1 := congrArg (· / δ α) (hα α)
      have h2 := congrArg (· % δ α) (hα α)
      simp only [Nat.mul_add_div (hδ α), Nat.div_eq_of_lt (hmr.2 α),
        Nat.div_eq_of_lt (hmr'.2 α), Nat.mul_add_mod, Nat.mod_eq_of_lt (hmr.2 α),
        Nat.mod_eq_of_lt (hmr'.2 α), add_zero] at h1 h2
      exact ⟨h1, h2⟩
    simp only [Prod.mk.injEq]
    exact ⟨Multiset.ext.mpr fun α ↦ (hdiv α).1, funext fun α ↦ (hdiv α).2⟩
  · simp only [Finset.mem_image, Prod.exists]
    rintro _ ⟨m, r, hmr, rfl⟩
    simp only [D, mem_product, Fintype.mem_piFinset, Finset.mem_range] at hmr
    rw [Finsupp.weight_eq_sum]
    have hterm : ∀ α, (g (m, r)) α • ((δ α : ℝ))⁻¹ ≤ m.count α + 1 := fun α ↦ by
      have hδα : (0 : ℝ) < δ α := Nat.cast_pos.mpr (hδ α)
      have e : ((g (m, r) α : ℕ) : ℝ) = δ α * m.count α + r α := by simp [g]
      have h2 : (r α : ℝ) * (δ α : ℝ)⁻¹ ≤ 1 := by
        rw [mul_inv_le_iff₀ hδα, one_mul]
        exact_mod_cast (hmr.2 α).le
      rw [nsmul_eq_mul, e, add_mul, mul_comm (δ α : ℝ), mul_assoc, mul_inv_cancel₀ hδα.ne',
        mul_one]
      exact add_le_add_right h2 _
    refine (sum_le_sum fun α _ ↦ hterm α).trans ?_
    rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hsum : ∑ α, (m.count α : ℝ) = Multiset.card m := by
      rw [← Nat.cast_sum, Multiset.sum_count_eq_card (fun a _ ↦ mem_univ a)]
    rw [hsum]
    have := hM m hmr.1
    linarith [(Nat.cast_le (α := ℝ)).mpr this]

end Count

section Main

variable {σ R : Type*} [CommRing R] [DecidableEq σ] {d : ℕ}
  {𝔭 : Ideal (MvPolynomial σ R)} [𝔭.IsPrime] {v : Fin d → σ} {Q : Fin d → MvPolynomial σ R}

/-- **The multiplicity estimate** (Rémond 2001, Prop. 3.1 with Lemma 3.1). Let `Q_α ∈ 𝔭` with
`∂Q_β/∂X_{v_α} ∈ 𝔭` exactly when `α ≠ β`, and give the direction `v_α` the weight `1/δ_α`. If the
Taylor expansion at `𝔭` of every element of `I` has only terms of weight `> ε`, then for any
`x_1, …, x_d ∈ I`, `ε^d ∏_α δ_α ≤ ℓ(B_𝔭/(x_1, …, x_d)B_𝔭)`. -/
theorem prod_mul_pow_le_localLength (hQ : ∀ α, Q α ∈ 𝔭)
    (hoff : ∀ α β, α ≠ β → pderiv (v α) (Q β) ∈ 𝔭) (hdiag : ∀ α, pderiv (v α) (Q α) ∉ 𝔭)
    {δ : Fin d → ℕ} (hδ : ∀ α, 0 < δ α) {ε : ℝ} (hε : 0 < ε) {I : Ideal (MvPolynomial σ R)}
    (hI : I ≤ (weightIdeal (fun α ↦ ((δ α : ℝ))⁻¹) ε).comap (taylorAtPrime 𝔭 v))
    {x : Fin d → MvPolynomial σ R} (hx : ∀ α, x α ∈ I) {ℓ : ℕ}
    (hℓ : Ideal.localLength 𝔭 (Ideal.span (Set.range x)) = ℓ) :
    (∏ α, (δ α : ℝ)) * ε ^ d ≤ ℓ := by
  set c : Fin d → ℝ := fun α ↦ ((δ α : ℝ))⁻¹
  have hc : ∀ α, 0 ≤ c α := fun α ↦ inv_nonneg.mpr (Nat.cast_nonneg _)
  -- The comparison for one exponent `n + 1` with `d ≤ (n + 1) ε`.
  have key : ∀ n : ℕ, (d : ℝ) ≤ (n + 1) * ε →
      (∏ α, (δ α : ℝ)) * ((n + 1) * ε - d) ^ d ≤ ℓ * ((n : ℝ) + d) ^ d := by
    intro n hn
    set N : ℝ := (n + 1) * ε
    have hfloor : d ≤ ⌊N⌋₊ := Nat.le_floor hn
    obtain ⟨T, hTcard, hTw⟩ := exists_finset_weight_le δ hδ (⌊N⌋₊ - d)
    have hTw' : ∀ γ ∈ T, Finsupp.weight c γ ≤ N := fun γ hγ ↦ by
      refine (hTw γ hγ).trans ?_
      rw [← Nat.cast_add, Nat.sub_add_cancel hfloor]
      exact Nat.floor_le (mul_nonneg (by positivity) hε.le)
    have hchain := card_le_localLength_comap_weightIdeal hQ hoff hdiag hc T hTw'
    have hpow : I ^ (n + 1) ≤ (weightIdeal c N).comap (taylorAtPrime 𝔭 v) := by
      have := pow_succ_le_weightIdeal c (Ideal.map_le_iff_le_comap.mpr hI) n
      rw [← Ideal.map_pow] at this
      exact Ideal.map_le_iff_le_comap.mp this
    have hJ : Ideal.span (Set.range x) ^ (n + 1) ≤ I ^ (n + 1) :=
      Ideal.pow_right_mono (Ideal.span_le.mpr (Set.range_subset_iff.mpr hx)) _
    have hup := Ideal.localLength_span_range_pow_le 𝔭 x (n + 1)
    rw [hℓ, Nat.sum_range_multichoose n d] at hup
    have hall := hchain.trans ((Ideal.localLength_le_of_le hpow).trans
      ((Ideal.localLength_le_of_le hJ).trans hup))
    rw [hTcard] at hall
    have hnat : (⌊N⌋₊ - d + d).choose d * ∏ α, δ α ≤ (n + d).choose d * ℓ := by
      exact_mod_cast hall
    have hreal : ((⌊N⌋₊ - d + d).choose d : ℝ) * ∏ α, (δ α : ℝ) ≤ ((n + d).choose d) * ℓ := by
      exact_mod_cast hnat
    have hlow : ((⌊N⌋₊ - d + 1 : ℕ) : ℝ) ^ d / d.factorial ≤ (⌊N⌋₊ - d + d).choose d := by
      have := Nat.pow_le_choose (α := ℝ) d (⌊N⌋₊ - d + d)
      rwa [show ⌊N⌋₊ - d + d + 1 - d = ⌊N⌋₊ - d + 1 by omega] at this
    have hupc : ((n + d).choose d : ℝ) ≤ ((n + d : ℕ) : ℝ) ^ d / d.factorial :=
      Nat.choose_le_pow_div d (n + d)
    have hfac : (0 : ℝ) < d.factorial := by positivity
    have hK : N - d ≤ ((⌊N⌋₊ - d + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_add, Nat.cast_sub hfloor, Nat.cast_one]
      linarith [Nat.lt_floor_add_one N]
    have hNd : 0 ≤ N - d := by linarith
    have hprod : (0 : ℝ) ≤ ∏ α, (δ α : ℝ) := by positivity
    calc (∏ α, (δ α : ℝ)) * (N - d) ^ d
        ≤ (∏ α, (δ α : ℝ)) * ((⌊N⌋₊ - d + 1 : ℕ) : ℝ) ^ d := by gcongr
      _ = d.factorial * (((⌊N⌋₊ - d + 1 : ℕ) : ℝ) ^ d / d.factorial * ∏ α, (δ α : ℝ)) := by
        field_simp
      _ ≤ d.factorial * (((n + d).choose d) * ℓ) :=
        mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hlow hprod).trans hreal)
          hfac.le
      _ ≤ d.factorial * ((((n + d : ℕ) : ℝ) ^ d / d.factorial) * ℓ) := by gcongr
      _ = ℓ * ((n : ℝ) + d) ^ d := by
        push_cast
        field_simp
  -- Divide by `(n + 1)^d` and let `n → ∞`.
  have h0 := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (d : ℝ)
  have hlim1 : Filter.Tendsto (fun n : ℕ ↦ (∏ α, (δ α : ℝ)) * (ε - d * (1 / ((n : ℝ) + 1))) ^ d)
      Filter.atTop (nhds ((∏ α, (δ α : ℝ)) * (ε - d * 0) ^ d)) :=
    ((tendsto_const_nhds.sub h0).pow d).const_mul _
  have hlim2 : Filter.Tendsto (fun n : ℕ ↦ (ℓ : ℝ) * (1 + d * (1 / ((n : ℝ) + 1))) ^ d)
      Filter.atTop (nhds ((ℓ : ℝ) * (1 + d * 0) ^ d)) :=
    ((tendsto_const_nhds.add h0).pow d).const_mul _
  simp only [mul_zero, sub_zero, add_zero, one_pow, mul_one] at hlim1 hlim2
  refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt ((d : ℝ) / ε)
  refine Filter.eventually_atTop.mpr ⟨n₀, fun n hn ↦ ?_⟩
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hdn : (d : ℝ) ≤ (n + 1) * ε := by
    rw [div_lt_iff₀ hε] at hn₀
    have : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have h := key n hdn
  have e1 : (n + 1) * ε - d = (n + 1) * (ε - d * (1 / ((n : ℝ) + 1))) := by field_simp
  have e2 : ((n : ℝ) + d) ≤ (n + 1) * (1 + d * (1 / ((n : ℝ) + 1))) := by
    field_simp
    linarith
  rw [e1, mul_pow] at h
  have h2 : (ℓ : ℝ) * ((n : ℝ) + d) ^ d ≤
      ℓ * (((n : ℝ) + 1) ^ d * (1 + d * (1 / ((n : ℝ) + 1))) ^ d) := by
    rw [← mul_pow]
    gcongr
  have h3 := h.trans h2
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ d := by positivity
  nlinarith [h3, hpos]

theorem weight_one_eq_degree {τ : Type*} (γ : τ →₀ ℕ) :
    Finsupp.weight (fun _ ↦ (1 : ℝ)) γ = γ.degree := by
  simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum]

omit [DecidableEq σ] in
/-- **At most `ht 𝔭` transversal equations.** If `Q_1, …, Q_d ∈ 𝔭` and directions `v_α` satisfy
`∂Q_β/∂X_{v_α} ∈ 𝔭` exactly when `α ≠ β`, and `x_1, …, x_e ∈ 𝔭` have `ℓ(B_𝔭/(x)B_𝔭)` finite, then
`d ≤ e`: the chain of the monomials `Q^γ` of degree `≤ n` gives `ℓ(B_𝔭/(x)^{2(n+d)+2}B_𝔭)` at least
`C(n + d, d)`, which grows like `n^d`, while it is at most `ℓ · C(2(n+d)+1+e, e)`. -/
theorem le_of_localLength_eq (hQ : ∀ α, Q α ∈ 𝔭)
    (hoff : ∀ α β, α ≠ β → pderiv (v α) (Q β) ∈ 𝔭) (hdiag : ∀ α, pderiv (v α) (Q α) ∉ 𝔭)
    {e : ℕ} {x : Fin e → MvPolynomial σ R} (hx : ∀ α, x α ∈ 𝔭) {ℓ : ℕ}
    (hℓ : Ideal.localLength 𝔭 (Ideal.span (Set.range x)) = ℓ) : d ≤ e := by
  classical
  set c : Fin d → ℝ := fun _ ↦ 1
  have hc : ∀ α, 0 ≤ c α := fun _ ↦ zero_le_one
  have hJ : (Ideal.span (Set.range x)).map (taylorAtPrime 𝔭 v) ≤ weightIdeal c (1 / 2) := by
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le, Set.range_subset_iff]
    intro α
    have h1 := mem_degIdeal_one_of_constantCoeff (F := taylorAtPrime 𝔭 v (x α))
      (by rw [constantCoeff_taylorAtPrime, Ideal.Quotient.eq_zero_iff_mem]; exact hx α)
    refine monomialSpan_mono (fun μ (hμ : 1 ≤ μ.degree) ↦ ?_) h1
    change (1 / 2 : ℝ) < Finsupp.weight c μ
    rw [weight_one_eq_degree]
    have : (1 : ℝ) ≤ μ.degree := by exact_mod_cast hμ
    linarith
  -- The comparison for one `n`.
  have key : ∀ n : ℕ, (n + d).choose d ≤ (2 * (n + d) + 1 + e).choose e * ℓ := by
    intro n
    obtain ⟨T, hTcard, hTw⟩ := exists_finset_weight_le (fun _ : Fin d ↦ 1) (fun _ ↦ one_pos) n
    have hTw' : ∀ γ ∈ T, Finsupp.weight c γ ≤
        (((2 * (n + d) + 1 : ℕ) : ℝ) + 1) * (1 / 2) := by
      intro γ hγ
      have := hTw γ hγ
      simp only [Nat.cast_one, inv_one] at this
      refine this.trans ?_
      push_cast
      linarith
    have hchain := card_le_localLength_comap_weightIdeal hQ hoff hdiag hc T hTw'
    have hpow := pow_succ_le_weightIdeal c hJ (2 * (n + d) + 1)
    rw [← Ideal.map_pow] at hpow
    have hup := Ideal.localLength_span_range_pow_le 𝔭 x (2 * (n + d) + 1 + 1)
    rw [hℓ, Nat.sum_range_multichoose] at hup
    have hall := hchain.trans
      ((Ideal.localLength_le_of_le (Ideal.map_le_iff_le_comap.mp hpow)).trans hup)
    rw [hTcard] at hall
    simp only [Finset.prod_const_one, mul_one] at hall
    exact_mod_cast hall
  by_contra hlt
  push Not at hlt
  set M := d.factorial * ℓ * (2 * d + e + 2) ^ e
  have hlow : (M + 1) ^ d ≤ d.factorial * (M + d).choose d := by
    rw [← Nat.ascFactorial_eq_factorial_mul_choose]
    exact Nat.pow_succ_le_ascFactorial _ _
  have hle : 2 * (M + d) + 1 + e ≤ (2 * d + e + 2) * (M + 1) := by nlinarith
  have hup : (2 * (M + d) + 1 + e).choose e ≤ ((2 * d + e + 2) * (M + 1)) ^ e :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hle _)
  have hmain : (M + 1) ^ d ≤ M * (M + 1) ^ e :=
    calc (M + 1) ^ d ≤ d.factorial * (M + d).choose d := hlow
      _ ≤ d.factorial * ((2 * (M + d) + 1 + e).choose e * ℓ) := Nat.mul_le_mul_left _ (key M)
      _ ≤ d.factorial * (((2 * d + e + 2) * (M + 1)) ^ e * ℓ) := by gcongr
      _ = M * (M + 1) ^ e := by rw [mul_pow]; ring
  have hpow : (M + 1) ^ (e + 1) ≤ (M + 1) ^ d := Nat.pow_le_pow_right (Nat.succ_pos _) hlt
  rw [pow_succ] at hpow
  have hpos : 0 < (M + 1) ^ e := by positivity
  nlinarith

end Main

end MvPolynomial
