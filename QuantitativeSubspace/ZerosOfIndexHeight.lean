/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.ProductTheoremHeight
public import QuantitativeSubspace.ZerosOfIndex

-- Used only inside proofs.
import Mathlib.Data.Finsupp.Interval

/-!
# The product theorem for the zeros of index `σ`, with heights (Rémond 2001, Thm. 1.1)

`MvPolynomial.productTheorem_indexIdeal_height` is the height part of G. Rémond, *Sur le théorème
du produit*, J. Théor. Nombres Bordeaux **13** (2001), Thm. 1.1, for a component `𝔭` of both
`Z_a(P)` and `Z_{a+ε}(P)`, relative to a multiprojective height theory
(`MvPolynomial.MultiprojectiveHeight`). As in `MvPolynomial.productTheorem_indexIdeal`, the
generators are the Hasse derivatives `∂_κ P` padded to multidegree `δ` by a monomial; there are
finitely many nonzero ones, and their coefficients are `c · P_ν` with `c = ∏_s C(n_s + κ_s, κ_s)`
at most `2^{|δ|}` (`MvPolynomial.exists_coeff_hasseDeriv_mul_monomial`). So the height of the
family of generators is at most `h(P) + [K : ℚ] |δ| log 2`, which with
`MvPolynomial.productTheorem_height_coeff` and Rémond's Lemma 5.2
(`MvPolynomial.log_sqrt_sum_inv_blockMultinomial_le`) gives the error term
`∑_{j < t} max(h(P) + [K : ℚ] (|δ| log 2 + j log |δ| + |√n|), 0)`, `|√n| = ∑_i √n_i` with `n_i + 1`
the number of variables in block `i`. Here `h(P)` is the height of the tuple of coefficients of
`P`. `MvPolynomial.exists_productTheorem_indexIdeal_height` is the
same bound for the components of Rémond's Cor. 1.1, at `ε / N`.

This is part of Layer Q1.3 of the `QuantitativeSubspace` roadmap.
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {σ ι K : Type*} [Field K] [Finite σ] [DecidableEq ι]
  {b : σ → ι} {δ : ι → ℕ} {P : MvPolynomial σ K}

omit [Finite σ] in
/-- The total degree `|ν|` of a monomial of multidegree `δ` is `|δ| = ∑_i δ_i`. -/
theorem sum_eq_sum_of_weight_multiWeight [Fintype σ] [Fintype ι] {ν : σ →₀ ℕ}
    (h : Finsupp.weight (multiWeight b) ν = δ) : ∑ s, ν s = ∑ i, δ i := by
  classical
  rw [← h]
  simp_rw [weight_multiWeight_apply]
  exact (Finset.sum_fiberwise _ _ _).symm

/-- **The coefficients of a padded Hasse derivative.** A nonzero coefficient of
`∂_κ P · X^j` is `c · P_ν` for a natural number `c ≤ 2^{|δ|}`, when `P` has multidegree `δ`. -/
theorem exists_coeff_hasseDeriv_mul_monomial [Fintype ι]
    (hP : IsWeightedHomogeneous (multiWeight b) P δ) (κ j μ : σ →₀ ℕ)
    (h0 : (hasseDeriv κ P * monomial j 1).coeff μ ≠ 0) :
    ∃ ν, ∃ c : ℕ, c ≤ 2 ^ (∑ i, δ i) ∧
      (hasseDeriv κ P * monomial j 1).coeff μ = c * P.coeff ν := by
  classical
  have := Fintype.ofFinite σ
  rw [coeff_mul_monomial'] at h0 ⊢
  split_ifs at h0 ⊢ with hj
  · rw [mul_one, hasseDeriv_coeff] at h0 ⊢
    refine ⟨μ - j + κ, _, ?_, rfl⟩
    have hν := hP (right_ne_zero_of_mul h0)
    rw [← sum_eq_sum_of_weight_multiWeight hν, ← Finset.prod_pow_eq_pow_sum, Finsupp.prod]
    refine (Finset.prod_le_prod fun s _ ↦ ?_).trans
      (Finset.prod_le_prod_of_subset_of_one_le (subset_univ _)
        fun _ _ _ ↦ Nat.one_le_two_pow)
    rw [Finsupp.add_apply]
    exact Nat.choose_le_two_pow _ _
  · exact absurd rfl h0

/-- A nonzero Hasse derivative of a polynomial of multidegree `δ` has `κ_s ≤ δ_{b s}`. -/
theorem le_of_hasseDeriv_ne_zero (hP : IsWeightedHomogeneous (multiWeight b) P δ)
    {κ : σ →₀ ℕ} (h0 : hasseDeriv κ P ≠ 0) (s : σ) : κ s ≤ δ (b s) := by
  classical
  have := Fintype.ofFinite σ
  have h := weight_le_of_hasseDeriv_ne_zero hP h0 (b s)
  rw [weight_multiWeight_apply] at h
  exact (Finset.single_le_sum (f := fun s' ↦ κ s') (fun _ _ ↦ Nat.zero_le _)
    (by simp)).trans h

variable {m : ℕ} {b : σ → Fin m} {δ : Fin m → ℕ}

omit [Finite σ] in
/-- **Rémond's product theorem for the zeros of index `a`, with heights** (Rémond 2001, Thm. 1.1).
Under the hypotheses of `MvPolynomial.productTheorem_indexIdeal`, for a multiprojective height
theory `H`: `V(𝔭)` is a component of the product of its projections, of type `β` with
`ε^t d_β(𝔭) ≤ #F ≤ m^t`, and for every `k` with `β_k < n_k`,
`ε^t δ_k h_{β + ε_k}(𝔭) ≤ ∑_l h(ℙ^{n_l}) δ_l #F_l + S · #G_k` with
`S = ∑_{j < t} max(h(P) + [K : ℚ] (|δ| log 2 + j log |δ| + log c(δ)^{1/2}), 0)`,
`h(P)` the height of the coefficients of `P` and `c(δ) = ∑_μ 1/C(δ, μ)` over the monomials of
multidegree `δ`. -/
theorem productTheorem_indexIdeal_height [Fintype σ] [CharZero K] [Height.AdmissibleAbsValues K]
    (hb : Function.Surjective b) (H : MultiprojectiveHeight b) (hδ : ∀ i, 0 < δ i)
    (hP : IsWeightedHomogeneous (multiWeight b) P δ) {a ε : ℝ} (hε : 0 < ε)
    {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime] (hU : IsUnmixedRing (Localization.AtPrime 𝔭))
    (h𝔭a : 𝔭 ∈ (indexIdeal b δ P a).minimalPrimes) (h𝔭ε : indexIdeal b δ P (a + ε) ≤ 𝔭)
    (hne : hilbertPoly b 𝔭 ≠ 0) {t : ℕ} (ht : 𝔭.height = t) (hanti : Antitone δ)
    (hratio : ∀ i j : Fin m, (i : ℕ) + 1 = j → (m : ℝ) ^ t < ε ^ t * (δ i / δ j)) :
    𝔭 ∈ (Ideal.span {f | f ∈ 𝔭 ∧ ∃ i, f ∈ supported K {s | b s = i}}).minimalPrimes ∧
      ∃ β : Fin m →₀ ℕ, (∀ i, (β i : ℕ∞) + 1 = (varMatroid 𝔭).eRk {s | b s = i}) ∧
        1 ≤ multidegree b 𝔭 β ∧
        ε ^ t * multidegree b 𝔭 β ≤
          #(univ.filter fun f : Fin t → Fin m ↦
            β + ∑ j, Finsupp.single (f j) 1 = bottomType b) ∧
        #(univ.filter fun f : Fin t → Fin m ↦
          β + ∑ j, Finsupp.single (f j) 1 = bottomType b) ≤ m ^ t ∧
        ∀ k, β k < bottomType b k →
          ε ^ t * δ k * H.height 𝔭 (β + Finsupp.single k 1) ≤
            ∑ l, Height.totalWeight K * stollNumber (bottomType b l) * δ l *
                #(univ.filter fun f : Fin t → Fin m ↦ β + Finsupp.single k 1 +
                  ∑ j, Finsupp.single (f j) 1 = bottomType b + Finsupp.single l 1) +
              (∑ j ∈ range t, max (Height.logHeight (fun ν : P.support ↦ P.coeff ν) +
                Height.totalWeight K * ((∑ i, δ i : ℕ) * Real.log 2 +
                  j * Real.log (∑ i, δ i : ℕ) +
                  ∑ i, √((#({s | b s = i} : Finset σ) : ℝ) - 1))) 0) *
                #(univ.filter fun g : Fin (t - 1) → Fin m ↦ β + Finsupp.single k 1 +
                  ∑ j, Finsupp.single (g j) 1 = bottomType b) := by
  classical
  have h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b) :=
    (isWeightedHomogeneous_indexIdeal hP a).of_mem_minimalPrimes h𝔭a
  -- One variable outside `𝔭` in each block.
  choose rep hrep hrep𝔭 using exists_X_notMem_of_hilbertPoly_ne_zero hb h𝔭 hne
  -- The finitely many orders `κ ≤ δ` of weight `≤ a`, and the padded derivatives.
  set D : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun s ↦ δ (b s)
  set κs : Finset (σ →₀ ℕ) :=
    (Finset.Iic D).filter fun κ ↦ Finsupp.weight (fun s ↦ ((δ (b s) : ℝ))⁻¹) κ ≤ a
  set R : Finset (MvPolynomial σ K) :=
    κs.image fun κ ↦ hasseDeriv κ P * monomial (κ.mapDomain fun s ↦ rep (b s)) 1
  set R' : Set (MvPolynomial σ K) := {Q | ∃ κ : σ →₀ ℕ,
    Finsupp.weight (fun s ↦ ((δ (b s) : ℝ))⁻¹) κ ≤ a ∧ hasseDeriv κ P = Q}
  have hmemR : ∀ r ∈ R, ∃ κ ∈ κs,
      hasseDeriv κ P * monomial (κ.mapDomain fun s ↦ rep (b s)) 1 = r := fun r hr ↦
    Finset.mem_image.mp hr
  have hRR' : Ideal.span (R : Set (MvPolynomial σ K)) ≤ Ideal.span R' := by
    refine Ideal.span_le.mpr fun r hr ↦ ?_
    obtain ⟨κ, hκ, rfl⟩ := hmemR r hr
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨κ, (Finset.mem_filter.mp hκ).2, rfl⟩)
  have hR : ∀ r ∈ R, IsWeightedHomogeneous (multiWeight b) r δ := by
    intro r hr
    obtain ⟨κ, -, rfl⟩ := hmemR r hr
    exact isWeightedHomogeneous_hasseDeriv_mul_monomial hrep hP κ
  -- `𝔭` stays minimal over the padded generators: the padding monomials are outside `𝔭`, and
  -- the other derivatives vanish.
  have h𝔭R : 𝔭 ∈ (Ideal.span (R : Set (MvPolynomial σ K))).minimalPrimes := by
    refine ⟨⟨‹_›, hRR'.trans h𝔭a.1.2⟩, fun q ⟨hq, hRq⟩ hq𝔭 ↦ h𝔭a.2 ⟨hq, ?_⟩ hq𝔭⟩
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨κ, hκ, rfl⟩
    by_cases h0 : hasseDeriv κ P = 0
    · rw [h0]
      exact q.zero_mem
    have hκs : κ ∈ κs := Finset.mem_filter.mpr
      ⟨Finset.mem_Iic.mpr fun s ↦ le_of_hasseDeriv_ne_zero hP h0 s, hκ⟩
    have hmem : hasseDeriv κ P * monomial (κ.mapDomain fun s ↦ rep (b s)) 1 ∈ q :=
      hRq (Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hκs)))
    refine (hq.mem_or_mem hmem).resolve_right (monomial_one_notMem fun s hs ↦ ?_)
    obtain ⟨s', -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hs)
    exact fun h ↦ hrep𝔭 _ (hq𝔭 h)
  -- The derivatives of order `≤ ε` of the generators of `Z_a(P)` vanish on `Z_{a+ε}(P)`.
  have hI : ∀ Q ∈ R', ∀ κ : σ →₀ ℕ, Finsupp.weight (fun s ↦ ((δ (b s) : ℝ))⁻¹) κ ≤ ε →
      hasseDeriv κ Q ∈ 𝔭 := by
    rintro _ ⟨μ, hμ, rfl⟩ κ hκ
    rw [hasseDeriv_comp]
    refine nsmul_mem (h𝔭ε (hasseDeriv_mem_indexIdeal ?_)) _
    rw [map_add]
    linarith
  have hM : ∀ r ∈ R, r.support ⊆ blockMonomials b δ := fun r hr μ hμ ↦
    mem_blockMonomials.mpr (hR r hr (mem_support_iff.mp hμ))
  -- The height of the generators.
  have hh : Height.logHeight (coeffTuple R (blockMonomials b δ)) ≤
      Height.logHeight (fun ν : P.support ↦ P.coeff ν) +
        Height.totalWeight K * ((∑ i, δ i : ℕ) * Real.log 2) := by
    have h := logHeight_le_of_forall_eq_natCast_mul (x := coeffTuple R (blockMonomials b δ))
      (y := fun ν : P.support ↦ P.coeff ν) (N := 2 ^ (∑ i, δ i)) Nat.one_le_two_pow ?_
    · rwa [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at h
    rintro ⟨⟨r, hr⟩, μ⟩ hx
    obtain ⟨κ, -, rfl⟩ := hmemR r hr
    obtain ⟨ν, c, hc, hcoeff⟩ := exists_coeff_hasseDeriv_mul_monomial hP κ _ μ hx
    by_cases hν : P.coeff ν = 0
    · exact absurd (by rw [coeffTuple, hcoeff, hν, mul_zero]) hx
    exact ⟨⟨ν, mem_support_iff.mpr hν⟩, c, hc, hcoeff⟩
  obtain ⟨hmin, β, hrk, hpos, hle, hcount, hheight⟩ := productTheorem_height_coeff hb H hU hR
    h𝔭R h𝔭 hne ht hδ hε hRR' hI hanti hratio hM
  refine ⟨hmin, β, hrk, hpos, hle, hcount, fun k hk ↦ (hheight k hk).trans ?_⟩
  -- Rémond's Lemma 5.2: `log c(δ)^{1/2} ≤ |√n|`.
  have h52 := mul_le_mul_of_nonneg_left (log_sqrt_sum_inv_blockMultinomial_le b δ)
    (Nat.cast_nonneg (Height.totalWeight K))
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (sum_le_sum fun j _ ↦ max_le_max ?_ le_rfl) (Nat.cast_nonneg _))
  linear_combination hh + h52

omit [Finite σ] in
/-- **Rémond's corollary of the product theorem, with heights** (Rémond 2001, Cor. 1.1). Under
the hypotheses of `MvPolynomial.exists_productTheorem_indexIdeal`, every irreducible subvariety
`V(𝔮)` of `Z_ε(P)` lies in a product `Z = V(𝔭) ≠ ℙ` as there, and the heights of `𝔭` satisfy the
bound of `MvPolynomial.productTheorem_indexIdeal_height` at `ε / N`. -/
theorem exists_productTheorem_indexIdeal_height [Fintype σ] [CharZero K]
    [Height.AdmissibleAbsValues K] (hb : Function.Surjective b) (H : MultiprojectiveHeight b)
    (hδ : ∀ i, 0 < δ i) (hP : IsWeightedHomogeneous (multiWeight b) P δ) (hP0 : P ≠ 0)
    (hCM : ∀ (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime], IsUnmixedRing (Localization.AtPrime 𝔭))
    (hanti : Antitone δ) {N : ℕ} (hN : N + m = Nat.card σ) {ε : ℝ} (hε : 0 < ε)
    (hratio : ∀ i j : Fin m, (i : ℕ) + 1 = j → max 1 ((m * N / ε) ^ N) < δ i / δ j)
    {𝔮 : Ideal (MvPolynomial σ K)} [𝔮.IsPrime] (h𝔮 : 𝔮.IsWeightedHomogeneous (multiWeight b))
    (hne : hilbertPoly b 𝔮 ≠ 0) (h𝔮ε : indexIdeal b δ P ε ≤ 𝔮) :
    ∃ (𝔭 : Ideal (MvPolynomial σ K)) (_ : 𝔭.IsPrime), 𝔭 ≤ 𝔮 ∧
      Ideal.span {f | f ∈ 𝔭 ∧ ∃ i, f ∈ supported K {s | b s = i}} ≠ ⊥ ∧
      𝔭 ∈ (Ideal.span {f | f ∈ 𝔭 ∧ ∃ i, f ∈ supported K {s | b s = i}}).minimalPrimes ∧
      ∃ t : ℕ, 𝔭.height = t ∧
        ∃ β : Fin m →₀ ℕ, (∀ i, (β i : ℕ∞) + 1 = (varMatroid 𝔭).eRk {s | b s = i}) ∧
          1 ≤ multidegree b 𝔭 β ∧
          (ε / N) ^ t * multidegree b 𝔭 β ≤
            #(univ.filter fun f : Fin t → Fin m ↦
              β + ∑ j, Finsupp.single (f j) 1 = bottomType b) ∧
          #(univ.filter fun f : Fin t → Fin m ↦
            β + ∑ j, Finsupp.single (f j) 1 = bottomType b) ≤ m ^ t ∧
          ∀ k, β k < bottomType b k →
            (ε / N) ^ t * δ k * H.height 𝔭 (β + Finsupp.single k 1) ≤
              ∑ l, Height.totalWeight K * stollNumber (bottomType b l) * δ l *
                  #(univ.filter fun f : Fin t → Fin m ↦ β + Finsupp.single k 1 +
                    ∑ j, Finsupp.single (f j) 1 = bottomType b + Finsupp.single l 1) +
                (∑ j ∈ range t, max (Height.logHeight (fun ν : P.support ↦ P.coeff ν) +
                  Height.totalWeight K * ((∑ i, δ i : ℕ) * Real.log 2 +
                    j * Real.log (∑ i, δ i : ℕ) +
                    ∑ i, √((#({s | b s = i} : Finset σ) : ℝ) - 1))) 0) *
                  #(univ.filter fun g : Fin (t - 1) → Fin m ↦ β + Finsupp.single k 1 +
                    ∑ j, Finsupp.single (g j) 1 = bottomType b) := by
  obtain ⟨𝔭, h𝔭p, h𝔭𝔮, hne𝔭, hP𝔭, j, h𝔭min, h𝔭next, hε', t, ht, hratio'⟩ :=
    exists_component_indexIdeal hb hP hP0 hN hε hratio h𝔮 hne h𝔮ε
  obtain ⟨hmin, β, hβ, hpos, hdeg, hcardF, hheight⟩ := productTheorem_indexIdeal_height hb H hδ
    hP hε' (hCM 𝔭) h𝔭min h𝔭next hne𝔭 ht hanti hratio'
  exact ⟨𝔭, h𝔭p, h𝔭𝔮, span_traces_ne_bot hP0 hP𝔭 hmin, hmin, t, ht, β, hβ, hpos, hdeg, hcardF,
    hheight⟩

end MvPolynomial
