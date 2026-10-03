/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.MvHasseDerivTaylor
public import ForMathlib.RingTheory.MvPolynomial.MultiplicityBezout
public import ForMathlib.RingTheory.MvPolynomial.Projection

-- Used only inside proofs.
import ForMathlib.RingTheory.MvPolynomial.Product

/-!
# The Taylor map at the generic point of a prime, by Hasse derivatives

`ForMathlib`'s multiplicity estimate (`MvPolynomial.prod_mul_pow_le_localLength`) and its
combination with the excess Bézout inequality (`MvPolynomial.prod_mul_pow_mul_multidegree_le`)
state their vanishing hypothesis through the Taylor map at the generic point of `𝔭`,
`taylorAtPrime 𝔭 v : B → (B/𝔭)[Z_1, …, Z_d]`, `X_s ↦ (X_s mod 𝔭) + ∑_{v_α = s} Z_α`. This file
reads its coefficients as Hasse derivatives: for injective `v`, the coefficient of `Z^γ` is
`∂_{v_* γ} P mod 𝔭`, where `v_* γ` is `γ` moved to the variables `v_α`. The hypothesis of the
product theorem, *every `P ∈ I` has vanishing Hasse derivatives modulo `𝔭` in the directions `v_α`
up to weighted order `ε`*, then becomes Rémond's (Rémond 2001, §3), and it is enough to ask it of
the generators of `I`.

The directions `v_α` in the multiplicity estimate are automatically distinct: `∂Q_α/∂X_{v_α} ∉ 𝔭`
while `∂Q_β/∂X_{v_α} ∈ 𝔭` for `β ≠ α`.

The file lives here rather than in `ForMathlib` because the Hasse calculus
(`DiophantineApproximation/MvHasseDeriv.lean`, `.../MvHasseDerivTaylor.lean`) does.

## Main statements

* `MvPolynomial.coeff_taylorAtPrime`: the coefficient of `Z^γ` is `∂_{v_* γ} P mod 𝔭`.
* `MvPolynomial.taylorAtPrime_mem_weightIdeal_iff`: vanishing to weighted order `> a` is the
  vanishing modulo `𝔭` of the Hasse derivatives of weight `≤ a`.
* `MvPolynomial.prod_mul_pow_mul_multidegree_le_of_hasseDeriv`: the degree inequality of the
  product theorem with the vanishing hypothesis on Hasse derivatives of generators.
* `MvPolynomial.prod_pow_mul_pow_mul_multidegree_le`: the same in characteristic `0` with the
  transversal equations supplied (`MvPolynomial.exists_transversal_fin_of_hilbertPoly_ne_zero`):
  the hypothesis is Rémond's, vanishing of all Hasse derivatives of weight `≤ ε` for the weights
  `1/δ_i` on the factors, and the product is `∏_i δ_i^{c_i}` with `c_i` the number of variables
  of factor `i` outside an adapted transcendence basis.
* `MvPolynomial.prod_pow_mul_pow_le`: with `β` the type of that basis, `d_β(𝔭) ≥ 1`
  (`MvPolynomial.totalDegree_hilbertPoly_eq_and_one_le_multidegree`), so
  `ε^t ∏_i δ_i^{c_i}` is at most the Bézout number.

This is part of Layer Q1.1e of the `QuantitativeSubspace` roadmap.
-/

@[expose] public section

open Finset

namespace MvPolynomial

section Taylor

variable {σ R : Type*} [CommRing R] [DecidableEq σ] {d : ℕ} (𝔭 : Ideal (MvPolynomial σ R))
  {v : Fin d → σ}

/-- For injective `v`, the Taylor map at the generic point is the substitution `X ↦ X + Y`
(`MvPolynomial.coeff_taylor`), followed by reduction modulo `𝔭` and by `Y_{v_α} ↦ Z_α`,
`Y_s ↦ 0` off the range of `v`. -/
theorem taylorAtPrime_eq_killCompl (hv : Function.Injective v) (P : MvPolynomial σ R) :
    taylorAtPrime 𝔭 v P = killCompl hv (map (Ideal.Quotient.mk 𝔭)
      (aeval (fun j ↦ C (X j) + X j) P : MvPolynomial σ (MvPolynomial σ R))) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [taylorAtPrime]; rfl
  | add p q hp hq => rw [map_add, hp, hq, map_add, map_add, map_add]
  | mul_X p j hp =>
    rw [map_mul, hp, map_mul, map_mul, map_mul, taylorAtPrime_X, aeval_X, map_add, map_C, map_X,
      map_add, killCompl_C]
    congr 2
    by_cases hj : j ∈ Set.range v
    · obtain ⟨α, rfl⟩ := hj
      have hs : ({β | v β = v α} : Finset (Fin d)) = {α} := by
        ext β
        simp [hv.eq_iff]
      rw [hs, Finset.sum_singleton, killCompl, aeval_X, dite_eq_left ⟨α, rfl⟩]
      congr 1
      exact ((Equiv.ofInjective v hv).symm_apply_apply α).symm
    · have hs : ({β | v β = j} : Finset (Fin d)) = ∅ := by
        ext β
        simpa using fun h ↦ hj ⟨β, h⟩
      rw [hs, Finset.sum_empty, killCompl, aeval_X, dite_eq_right hj]

/-- **The Hasse-derivative bridge.** For injective `v`, the coefficient of `Z^γ` in the Taylor map
at the generic point is the Hasse derivative `∂_{v_* γ} P` modulo `𝔭`. -/
theorem coeff_taylorAtPrime (hv : Function.Injective v) (P : MvPolynomial σ R)
    (γ : Fin d →₀ ℕ) :
    (taylorAtPrime 𝔭 v P).coeff γ = Ideal.Quotient.mk 𝔭 (hasseDeriv (γ.mapDomain v) P) := by
  rw [taylorAtPrime_eq_killCompl 𝔭 hv, coeff_killCompl, coeff_map, coeff_taylor]

/-- **Vanishing to weighted order by Hasse derivatives.** For injective `v` and nonnegative
weights `c`, `taylorAtPrime 𝔭 v P` has only monomials of weight `> a` exactly when every Hasse
derivative of `P` in the directions `v_α` of weight `≤ a` lies in `𝔭`. -/
theorem taylorAtPrime_mem_weightIdeal_iff (hv : Function.Injective v) {c : Fin d → ℝ}
    (hc : ∀ α, 0 ≤ c α) {a : ℝ} (P : MvPolynomial σ R) :
    taylorAtPrime 𝔭 v P ∈ (weightIdeal c a : Ideal (MvPolynomial (Fin d) _)) ↔
      ∀ γ : Fin d →₀ ℕ, Finsupp.weight c γ ≤ a → hasseDeriv (γ.mapDomain v) P ∈ 𝔭 := by
  rw [weightIdeal, monomialSpan, mem_ideal_span_monomial_image]
  constructor
  · intro h γ hγ
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_taylorAtPrime 𝔭 hv]
    by_contra hne
    obtain ⟨μ, hμ, hle⟩ := h γ (mem_support_iff.mpr hne)
    exact (not_lt.mpr hγ) (hμ.trans_le (weight_mono_of_nonneg hc hle))
  · intro h γ hγ
    refine ⟨γ, ?_, le_rfl⟩
    change a < Finsupp.weight c γ
    refine not_le.mp fun hle ↦ ?_
    rw [mem_support_iff, coeff_taylorAtPrime 𝔭 hv, Ne, Ideal.Quotient.eq_zero_iff_mem] at hγ
    exact hγ (h γ hle)

omit [DecidableEq σ] in
/-- The directions of a transversal family are distinct. -/
theorem injective_of_pderiv_mem {Q : Fin d → MvPolynomial σ R}
    (hoff : ∀ α β, α ≠ β → pderiv (v α) (Q β) ∈ 𝔭) (hdiag : ∀ α, pderiv (v α) (Q α) ∉ 𝔭) :
    Function.Injective v := by
  intro α β h
  by_contra hne
  exact hdiag β (h ▸ hoff α β hne)

end Taylor

section Bezout

variable {σ ι K : Type*} [Field K] [DecidableEq ι] {b : σ → ι} [Finite σ] [Fintype ι]
  {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime]

/-- **Multiplicity against degree, with Hasse derivatives** (Rémond 2001, proof of Prop. 2.1,
degree part). Let `I` be generated by multihomogeneous polynomials `R` of multidegree `e`, and `𝔭`
a multihomogeneous minimal prime of `I` of height `t`, with transversal `Q_α ∈ 𝔭` in the
directions `v_α`. If `I` lies in the ideal generated by a set `R'` (for instance `R' = R`) every
element of which has `∂_{v_* γ} P ∈ 𝔭` whenever `∑ γ_α / δ_α ≤ ε`, then `ε^t (∏ δ_α) d_β(𝔭)` is
at most the Bézout number. -/
theorem prod_mul_pow_mul_multidegree_le_of_hasseDeriv [Infinite K] (hb : Function.Surjective b)
    {e : ι → ℕ} {R : Set (MvPolynomial σ K)}
    (hR : ∀ r ∈ R, IsWeightedHomogeneous (multiWeight b) r e)
    (h𝔭R : 𝔭 ∈ (Ideal.span R).minimalPrimes) (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b))
    (hne : hilbertPoly b 𝔭 ≠ 0) {t : ℕ} (ht : 𝔭.height = t) {v : Fin t → σ}
    {Q : Fin t → MvPolynomial σ K} (hQ : ∀ α, Q α ∈ 𝔭)
    (hoff : ∀ α β, α ≠ β → pderiv (v α) (Q β) ∈ 𝔭) (hdiag : ∀ α, pderiv (v α) (Q α) ∉ 𝔭)
    {δ : Fin t → ℕ} (hδ : ∀ α, 0 < δ α) {ε : ℝ} (hε : 0 < ε) {R' : Set (MvPolynomial σ K)}
    (hRR' : Ideal.span R ≤ Ideal.span R')
    (hI : ∀ P ∈ R', ∀ γ : Fin t →₀ ℕ, Finsupp.weight (fun α ↦ ((δ α : ℝ))⁻¹) γ ≤ ε →
      hasseDeriv (γ.mapDomain v) P ∈ 𝔭)
    (β : ι →₀ ℕ) (hβ : (bottomType b).degree - t ≤ β.degree) :
    (∏ α, (δ α : ℝ)) * ε ^ t * multidegree b 𝔭 β ≤
      ∑ f : Fin t → ι with β + ∑ j, Finsupp.single (f j) 1 = bottomType b,
        ∏ j, (e (f j) : ℝ) := by
  classical
  have hv := injective_of_pderiv_mem 𝔭 hoff hdiag
  refine prod_mul_pow_mul_multidegree_le hb hR h𝔭R h𝔭 hne ht hQ hoff hdiag hδ hε
    (hRR'.trans (Ideal.span_le.mpr fun P hP ↦ ?_)) β hβ
  exact (taylorAtPrime_mem_weightIdeal_iff 𝔭 hv (fun α ↦ inv_nonneg.mpr (Nat.cast_nonneg _))
    P).mpr (hI P hP)

omit [DecidableEq ι] [Finite σ] [𝔭.IsPrime] in
/-- Regrouping `∏_α δ_{b(v_α)}` by factors, for `v` a bijection onto the complement of `T`. -/
theorem prod_comp_eq_prod_pow {T : Finset σ} {t : ℕ} {v : Fin t → σ}
    (hv : Function.Injective v) (hrange : Set.range v = (T : Set σ)ᶜ) (δ : ι → ℕ) :
    ∏ α, (δ (b (v α)) : ℝ) = ∏ i, (δ i : ℝ) ^ {s | s ∉ T ∧ b s = i}.ncard := by
  classical
  have hcount : ∀ i, (Finset.univ.filter fun α ↦ b (v α) = i).card =
      {s | s ∉ T ∧ b s = i}.ncard := by
    intro i
    rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ hv]
    congr 1
    ext s
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨α, hα, rfl⟩
      refine ⟨fun h ↦ ?_, hα⟩
      have : v α ∈ Set.range v := ⟨α, rfl⟩
      rw [hrange] at this
      exact this h
    · rintro ⟨hs, hbs⟩
      have : s ∈ Set.range v := by
        rw [hrange]
        exact hs
      obtain ⟨α, rfl⟩ := this
      exact ⟨α, hbs, rfl⟩
  rw [← Finset.prod_fiberwise' Finset.univ (fun α ↦ b (v α)) (fun i ↦ (δ i : ℝ))]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Finset.prod_const, hcount]

/-- **Multiplicity against degree in characteristic `0`** (Rémond 2001, proof of Prop. 2.1,
degree part). Let `I` be generated by multihomogeneous polynomials `R` of multidegree `e`, and `𝔭`
a multihomogeneous minimal prime of `I` of height `t`. Give the variables of factor `i` the
weight `1/δ_i`, and suppose `I` lies in the ideal generated by a set `R'` (for instance `R' = R`)
every element of which has `∂_κ P ∈ 𝔭` for all `κ` of weight `≤ ε`. Then
for a transcendence basis `(x_t)_{t ∈ T}` of `B/𝔭` adapted to the factors (each `x_s`, `s ∉ T`,
algebraic over the `x_t`, `t ∈ T`, of factor `≥` that of `s`), with `c_i` the number of variables
of factor `i` outside `T` (so `∑ c_i = t`),
`ε^t (∏_i δ_i^{c_i}) d_β(𝔭) ≤ ∑_{f : β + ∑ ε_{f j} = n} ∏ e(f j)`. The basis meets every factor,
and `t + |T| = |σ|`. -/
theorem prod_pow_mul_pow_mul_multidegree_le [CharZero K] [LinearOrder ι]
    (hb : Function.Surjective b) {e : ι → ℕ}
    {R : Set (MvPolynomial σ K)} (hR : ∀ r ∈ R, IsWeightedHomogeneous (multiWeight b) r e)
    (h𝔭R : 𝔭 ∈ (Ideal.span R).minimalPrimes) (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b))
    (hne : hilbertPoly b 𝔭 ≠ 0) {t : ℕ} (ht : 𝔭.height = t)
    {δ : ι → ℕ} (hδ : ∀ i, 0 < δ i) {ε : ℝ} (hε : 0 < ε) {R' : Set (MvPolynomial σ K)}
    (hRR' : Ideal.span R ≤ Ideal.span R')
    (hI : ∀ P ∈ R', ∀ κ : σ →₀ ℕ, Finsupp.weight (fun s ↦ ((δ (b s) : ℝ))⁻¹) κ ≤ ε →
      hasseDeriv κ P ∈ 𝔭) :
    ∃ T : Finset σ,
      IsTranscendenceBasis K (fun t : (T : Set σ) ↦ Ideal.Quotient.mk 𝔭 (X (t : σ))) ∧
      (∀ s ∉ T, IsAlgebraic (Algebra.adjoin K
        ((fun t ↦ Ideal.Quotient.mk 𝔭 (X t)) '' {t | t ∈ T ∧ b s ≤ b t}))
          (Ideal.Quotient.mk 𝔭 (X s))) ∧
      (∀ i, ∃ s ∈ T, b s = i) ∧ t + #T = Nat.card σ ∧
      ∀ β : ι →₀ ℕ, (bottomType b).degree - t ≤ β.degree →
        (∏ i, (δ i : ℝ) ^ {s | s ∉ T ∧ b s = i}.ncard) * ε ^ t * multidegree b 𝔭 β ≤
          ∑ f : Fin t → ι with β + ∑ j, Finsupp.single (f j) 1 = bottomType b,
            ∏ j, (e (f j) : ℝ) := by
  have : Infinite K := Infinite.of_injective _ Nat.cast_injective
  obtain ⟨T, hB, hadapt, hTb, hcard, v, hv, hrange, Q, hQ, hoff, hdiag⟩ :=
    exists_transversal_fin_of_hilbertPoly_ne_zero hb 𝔭 h𝔭 hne ht
  refine ⟨T, hB, hadapt, hTb, hcard, fun β hβ ↦ ?_⟩
  rw [← prod_comp_eq_prod_pow hv hrange δ]
  exact prod_mul_pow_mul_multidegree_le_of_hasseDeriv (δ := fun α ↦ δ (b (v α))) hb hR
    h𝔭R h𝔭 hne ht hQ hoff hdiag (fun α ↦ hδ _) hε hRR'
    (fun P hP γ hγ ↦ hI P hP _
      (by rwa [weight_mapDomain (w := fun α ↦ ((δ (b (v α)) : ℝ))⁻¹)
        (w' := fun s ↦ ((δ (b s) : ℝ))⁻¹) (AddMonoidHom.id ℝ) (f := v) (fun _ ↦ rfl)])) β hβ

/-- **Rémond's multiplicity estimate against the Bézout number** (Rémond 2001, Prop. 2.1, degree
part, in characteristic `0`). Under the hypotheses of
`MvPolynomial.prod_pow_mul_pow_mul_multidegree_le`, take `β` the type of the adapted transcendence
basis `T`, `β_i = |T ∩ factor i| - 1`. Then `|β| = deg H_𝔭` and `d_β(𝔭)` is a positive integer,
so
`ε^t ∏_i δ_i^{c_i} ≤ ∑_{f : β + ∑ ε_{f j} = n} ∏ e(f j)`, `c_i = |factor i \ T|`. -/
theorem prod_pow_mul_pow_le [CharZero K] [LinearOrder ι]
    (hb : Function.Surjective b) {e : ι → ℕ}
    {R : Set (MvPolynomial σ K)} (hR : ∀ r ∈ R, IsWeightedHomogeneous (multiWeight b) r e)
    (h𝔭R : 𝔭 ∈ (Ideal.span R).minimalPrimes) (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b))
    (hne : hilbertPoly b 𝔭 ≠ 0) {t : ℕ} (ht : 𝔭.height = t)
    {δ : ι → ℕ} (hδ : ∀ i, 0 < δ i) {ε : ℝ} (hε : 0 < ε) {R' : Set (MvPolynomial σ K)}
    (hRR' : Ideal.span R ≤ Ideal.span R')
    (hI : ∀ P ∈ R', ∀ κ : σ →₀ ℕ, Finsupp.weight (fun s ↦ ((δ (b s) : ℝ))⁻¹) κ ≤ ε →
      hasseDeriv κ P ∈ 𝔭) :
    ∃ T : Finset σ,
      IsTranscendenceBasis K (fun t : (T : Set σ) ↦ Ideal.Quotient.mk 𝔭 (X (t : σ))) ∧
      (∀ s ∉ T, IsAlgebraic (Algebra.adjoin K
        ((fun t ↦ Ideal.Quotient.mk 𝔭 (X t)) '' {t | t ∈ T ∧ b s ≤ b t}))
          (Ideal.Quotient.mk 𝔭 (X s))) ∧
      (hilbertPoly b 𝔭).totalDegree = (coneType b T).degree ∧
      1 ≤ multidegree b 𝔭 (coneType b T) ∧
      (∏ i, (δ i : ℝ) ^ {s | s ∉ T ∧ b s = i}.ncard) * ε ^ t ≤
        ∑ f : Fin t → ι with coneType b T + ∑ j, Finsupp.single (f j) 1 = bottomType b,
          ∏ j, (e (f j) : ℝ) := by
  have := Fintype.ofFinite σ
  obtain ⟨T, hB, hadapt, hTb, hcard, h⟩ :=
    prod_pow_mul_pow_mul_multidegree_le hb hR h𝔭R h𝔭 hne ht hδ hε hRR' hI
  obtain ⟨hdeg, hpos⟩ := totalDegree_hilbertPoly_eq_and_one_le_multidegree hb h𝔭 hB hTb
  refine ⟨T, hB, hadapt, hdeg, hpos, ?_⟩
  have hβ : (bottomType b).degree - t ≤ (coneType b T).degree := by
    have h1 := degree_coneType_add_card b hTb
    have h2 := degree_coneType_add_card b (V := univ) fun i ↦
      (hb i).imp fun s hs ↦ ⟨mem_univ s, hs⟩
    rw [bottomType_eq_coneType]
    rw [Nat.card_eq_fintype_card] at hcard
    rw [Finset.card_univ] at h2
    omega
  have hpos' : (1 : ℝ) ≤ multidegree b 𝔭 (coneType b T) := by exact_mod_cast hpos
  refine le_trans ?_ (h _ hβ)
  exact le_mul_of_one_le_right (mul_nonneg (Finset.prod_induction _ (0 ≤ ·)
    (fun _ _ ↦ mul_nonneg) zero_le_one fun _ _ ↦ by positivity) (by positivity)) hpos'

end Bezout

end MvPolynomial
