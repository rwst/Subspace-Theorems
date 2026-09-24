/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import DiophantineApproximation.MultiHomogeneous
public import DiophantineApproximation.MvHasseDerivTaylor
public import DiophantineApproximation.PolynomialGrid

/-!
# Non-vanishing at a small point

After Layer 5.3 the auxiliary polynomial of Layer 5.2 is known to have a Hasse derivative of
small order that does not vanish *identically* on a product of subspaces
`V(Q 1) × ⋯ × V(Q m)`. What the proof of the Subspace Theorem needs is a **point** of that
product, of controlled height, at which a derivative of small order does not vanish. This file is
that step, Bombieri–Gubler's 7.5.23 and Lemma 7.5.25 (a): parametrize each subspace by a family
spanning it, apply the grid lemma of `DiophantineApproximation/PolynomialGrid.lean` to the
parametrized polynomial, and read the result back through the parametrization.

Reading it back is where the work is. The grid lemma produces a derivative in the *parameters*,
and what is wanted is a derivative in the original variables; the dictionary between the two is
the chain rule, which is not proved here and not needed. All the argument consumes is which
orders can occur, and that is multihomogeneity: the parametrization takes a monomial of block
degrees `(∑ i, μ (h, i))` to a polynomial multihomogeneous of the same multidegree, so a
coefficient of the parametrized polynomial at `J` sees only orders `μ` with
`∑ i, μ (h, i) = ∑ l, J (h, l)`.

## Main results

* `MvPolynomial.shift` and `MvPolynomial.coeff_shift`: the shift `X j ↦ X j + c j`, whose
  coefficients are the Hasse derivatives at `c`.
* `MvPolynomial.linSubst`: the **block-wise linear parametrization**
  `X (h, i) ↦ ∑ l, y h l i • X (h, l)`, with `MvPolynomial.eval_linSubst` — evaluating it is
  evaluating at the parametrized point — `MvPolynomial.shift_linSubst`,
  `MvPolynomial.IsMultiHomogeneous.linSubst` and
  `MvPolynomial.exists_coeff_ne_zero_of_coeff_linSubst_ne_zero`.
* `MvPolynomial.exists_eval_hasseDeriv_add_ne_zero`: **non-vanishing at a small point**. If
  `∂_I P` does not vanish identically on the product of the spans, then for every `B ≥ 1` a
  further derivative, of order at most `(card ρ) d h / B` in each block, does not vanish at a
  point whose coordinates in the given families are integers bounded by `B`.
* `MvPolynomial.exists_eval_hasseDeriv_ne_zero_of_sum_div_le`: the same with `B = 2 n / η`, which
  is Bombieri–Gubler's (7.37) — an order of weighted order at most `m η / 2` is replaced by one
  of weighted order at most `m η`.

## Implementation notes

⚠ **The chain rule is neither needed nor proved.** Bombieri–Gubler write that `∂_J R` is a linear
combination of derivatives `∂_{I'} P` evaluated at the point, which is the chain rule for a linear
substitution together with the composition law for Hasse derivatives. What the argument consumes
is only the *support* of that combination — that the orders occurring have the block degrees of
`J` — and that is multihomogeneity. The combination is never named, exactly as in Layer 5.2, where
`MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero` replaced the expansion coefficients
`a(L v; J; I)` by an induction that never writes them down.

⚠ **The bridge is the shift, not the Taylor evaluation.** `MvPolynomial.coeff_shift` turns "the
derivative of order `μ` does not vanish at `c`" into "the coefficient at `μ` of `P (X + c)` is
nonzero", and the shift commutes with the parametrization: shifting the parameters by `z` is
shifting the point by the parametrized point of `z`. The two evaluations — one in the parameters,
one in the original variables — thereby become two coefficient extractions from *the same*
polynomial, and the proof is that identity and nothing else.

⚠ **The order gained is measured per block, and `card ρ` enters exactly once.** The grid lemma
bounds the new order in each parameter separately, `B * J (h, l) ≤ d h`; summing over the
parameters of a block gives Bombieri–Gubler's `|i*_h| ≤ n d_h / B`. Nothing else in the file
counts parameters.

⚠ **`B` is rounded up, and `⊔ 1` is what allows an empty family.** The coefficients of the point
are bounded by `2 n / η + 1` rather than the book's `2 n / η`; the rounding is absorbed in 5.6 by
constants that do not depend on it. With no parameters at all the grid still has to contain a
point, and `⊔ 1` supplies it.

⚠ **Multihomogeneity is used only for the degree in each block.** A multihomogeneous `P` of
multidegree `d` has `degreeOf (h, i) P ≤ d h`, and that — after differentiating and
parametrizing, neither of which raises it — is the only thing the grid lemma consumes about `P`.

⚠ **Nothing here knows about `V(Q)`, heights or places.** The hypothesis is that the derivative
does not vanish identically on the product of the spans of the *given* families, which is what
`MvPolynomial.eval_linSubst` says the nonvanishing of the parametrized polynomial means. That
those spans are the `V(Q h)` and that the families lie in the approximation domains is Layer 5.6's
business, and it is what turns `|z h l| ≤ B` into a height bound for the point. Properties (b),
(c) and (d) of Lemma 7.5.25 are Layer 5.2's conclusions read at the new order `I'`, and are not
restated here.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
7.5.23 and Lemma 7.5.25.

This is part of Layer 5.5 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset

noncomputable section

namespace MvPolynomial

/-! ### The shift by a point -/

section Shift

variable {σ R : Type*} [CommRing R]

/-- **The shift by a point**, `X j ↦ X j + c j`. -/
def shift (c : σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun j ↦ C (c j) + X j

@[simp]
theorem shift_X (c : σ → R) (j : σ) : shift c (X j) = C (c j) + X j := by simp [shift]

/-- **The coefficients of a shifted polynomial are its Hasse derivatives at the point.** This is
the substitution formula of Layer 2.1 with the second family of variables evaluated at `c`. -/
theorem coeff_shift (c : σ → R) (P : MvPolynomial σ R) (μ : σ →₀ ℕ) :
    (shift c P).coeff μ = eval c (hasseDeriv μ P) := by
  have hmap : (MvPolynomial.map (eval c)).comp
      ((aeval (fun j ↦ C (X j) + X j) :
          MvPolynomial σ R →ₐ[R] MvPolynomial σ (MvPolynomial σ R)) :
        MvPolynomial σ R →+* MvPolynomial σ (MvPolynomial σ R))
      = (shift c : MvPolynomial σ R →+* MvPolynomial σ R) := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun j ↦ ?_)
    · simp [shift]
    · simp [shift]
  have h := congrArg (fun f ↦ (f P).coeff μ) hmap
  simp only [RingHom.coe_comp, Function.comp_apply, coeff_map, RingHom.coe_coe] at h
  rw [← h, coeff_taylor]

end Shift

/-! ### Multihomogeneity of a monomial -/

section Homogeneous

variable {κ ι R : Type*} [CommRing R] [Fintype ι]

/-- A monomial is multihomogeneous, of the multidegree given by its own block degrees. -/
theorem isMultiHomogeneous_monomial (μ : κ × ι →₀ ℕ) (c : R) :
    IsMultiHomogeneous (fun h ↦ ∑ i, μ (h, i)) (monomial μ c) := by
  classical
  intro ν hν h
  rcases eq_or_ne μ ν with rfl | hne
  · rfl
  · rw [coeff_monomial, ite_eq_right hne] at hν
    exact absurd rfl hν

/-- Every exponent of a multihomogeneous polynomial is at most the degree of its block. -/
theorem IsMultiHomogeneous.degreeOf_le {d : κ → ℕ} {P : MvPolynomial (κ × ι) R}
    (hP : IsMultiHomogeneous d P) (h : κ) (i : ι) : P.degreeOf (h, i) ≤ d h := by
  classical
  rw [degreeOf_le_iff]
  intro m hm
  rw [← hP (mem_support_iff.mp hm) h]
  exact Finset.single_le_sum (f := fun i ↦ m (h, i)) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)

end Homogeneous

/-! ### The block-wise linear parametrization -/

section LinSubst

variable {κ ι ρ R : Type*} [CommRing R] [Fintype ι] [Fintype ρ]

/-- The **block-wise linear parametrization** `X (h, i) ↦ ∑ l, y h l i • X (h, l)`: in each
block, the coordinates of the general point of the span of the family `y h`. -/
def linSubst (y : κ → ρ → ι → R) :
    MvPolynomial (κ × ι) R →ₐ[R] MvPolynomial (κ × ρ) R :=
  aeval fun p : κ × ι ↦ ∑ l, C (y p.1 l p.2) * X (p.1, l)

omit [Fintype ι] in
@[simp]
theorem linSubst_X (y : κ → ρ → ι → R) (h : κ) (i : ι) :
    linSubst y (X (h, i)) = ∑ l, C (y h l i) * X ((h, l) : κ × ρ) := by
  simp [linSubst]

omit [Fintype ι] in
/-- **Evaluating a parametrized polynomial is evaluating it at the parametrized point.** This is
what "vanishes identically on the product of the spans" means. -/
theorem eval_linSubst (y : κ → ρ → ι → R) (u : κ × ρ → R) (P : MvPolynomial (κ × ι) R) :
    eval u (linSubst y P) = eval (fun p : κ × ι ↦ ∑ l, u (p.1, l) * y p.1 l p.2) P := by
  have h : ((aeval u : MvPolynomial (κ × ρ) R →ₐ[R] R).comp (linSubst y))
      = aeval (fun p : κ × ι ↦ ∑ l, u (p.1, l) * y p.1 l p.2) := by
    refine MvPolynomial.algHom_ext fun p ↦ ?_
    obtain ⟨h, i⟩ := p
    rw [AlgHom.comp_apply, linSubst_X, map_sum, aeval_X]
    exact Finset.sum_congr rfl fun l _ ↦ by rw [map_mul, aeval_C, aeval_X, mul_comm]; simp
  have h2 := congrArg (fun f ↦ f P) h
  simpa [aeval_eq_eval] using h2

omit [Fintype ι] in
/-- **The shift and the parametrization commute**: shifting the parameters by `z` is shifting the
point by the parametrized point of `z`. -/
theorem shift_linSubst (y : κ → ρ → ι → R) (z : κ × ρ → R) (P : MvPolynomial (κ × ι) R) :
    shift z (linSubst y P)
      = linSubst y (shift (fun p : κ × ι ↦ ∑ l, z (p.1, l) * y p.1 l p.2) P) := by
  have h : (shift z).comp (linSubst y)
      = (linSubst y).comp (shift (fun p : κ × ι ↦ ∑ l, z (p.1, l) * y p.1 l p.2)) := by
    refine MvPolynomial.algHom_ext fun p ↦ ?_
    obtain ⟨h, i⟩ := p
    have hL : shift z (linSubst y (X ((h, i) : κ × ι)))
        = ∑ l, (C (y h l i) * C (z (h, l)) + C (y h l i) * X ((h, l) : κ × ρ)) := by
      rw [linSubst_X, map_sum]
      exact Finset.sum_congr rfl fun l _ ↦ by
        rw [map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, shift_X, mul_add]
    have hR : linSubst y
          (shift (fun p : κ × ι ↦ ∑ l, z (p.1, l) * y p.1 l p.2) (X ((h, i) : κ × ι)))
        = (∑ l, C (y h l i) * C (z (h, l))) + ∑ l, C (y h l i) * X ((h, l) : κ × ρ) := by
      rw [shift_X, map_add, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, linSubst_X]
      refine congrArg (fun q ↦ q + ∑ l, C (y h l i) * X ((h, l) : κ × ρ)) ?_
      rw [map_sum]
      exact Finset.sum_congr rfl fun l _ ↦ by rw [map_mul, mul_comm]
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hL, hR, Finset.sum_add_distrib]
  exact congrArg (fun f ↦ f P) h

variable [Finite κ]

/-- **The parametrization preserves multihomogeneity**: each new variable carries the degree of
the block it parametrizes. -/
theorem IsMultiHomogeneous.linSubst {d : κ → ℕ} {P : MvPolynomial (κ × ι) R}
    (hP : IsMultiHomogeneous d P) (y : κ → ρ → ι → R) :
    IsMultiHomogeneous d (MvPolynomial.linSubst y P) := by
  classical
  rw [isMultiHomogeneous_iff] at hP ⊢
  refine IsWeightedHomogeneous.aeval (fun p ↦ ?_) hP
  obtain ⟨h, i⟩ := p
  refine IsWeightedHomogeneous.finset_sum fun l _ ↦ ?_
  have hX : IsWeightedHomogeneous (blockWeight κ ρ)
      (X ((h, l) : κ × ρ) : MvPolynomial (κ × ρ) R) (blockWeight κ ρ (h, l)) :=
    isWeightedHomogeneous_X R (blockWeight κ ρ) (h, l)
  simpa [blockWeight] using hX.C_mul (y h l i)

/-- **The parametrization mixes only monomials of equal block degrees**: a surviving coefficient
of `linSubst y Q` at `J` comes from a coefficient of `Q` at an order with the same degree in
every block. -/
theorem exists_coeff_ne_zero_of_coeff_linSubst_ne_zero (y : κ → ρ → ι → R)
    (Q : MvPolynomial (κ × ι) R) {J : κ × ρ →₀ ℕ} (hJ : (linSubst y Q).coeff J ≠ 0) :
    ∃ μ : κ × ι →₀ ℕ, Q.coeff μ ≠ 0 ∧ ∀ h, ∑ l, J (h, l) = ∑ i, μ (h, i) := by
  classical
  have hsum : (linSubst y Q).coeff J
      = ∑ μ ∈ Q.support, (linSubst y (monomial μ (Q.coeff μ))).coeff J := by
    conv_lhs => rw [Q.as_sum]
    rw [map_sum, coeff_sum]
  rw [hsum] at hJ
  obtain ⟨μ, hμsupp, hμ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hJ
  exact ⟨μ, mem_support_iff.mp hμsupp,
    fun h ↦ ((isMultiHomogeneous_monomial μ (Q.coeff μ)).linSubst y) hμ h⟩

end LinSubst

/-! ### The small point -/

section SmallPoint

variable {k : Type*} [Field k] [CharZero k] {κ ι ρ : Type*} [Fintype ι] [Fintype ρ]
  [Finite κ]

/-- **Non-vanishing at a small point**, Bombieri–Gubler, Lemma 7.5.25 (a). If a Hasse derivative
of order `I` of a multihomogeneous `P` does not vanish identically on the product of the spans of
the families `y h`, then, for every `B ≥ 1`, a further derivative, of order at most
`(card ρ) * d h / B` in each block, does not vanish at a point of the product whose coordinates
in the given families are integers bounded by `B`. -/
theorem exists_eval_hasseDeriv_add_ne_zero {d : κ → ℕ} {P : MvPolynomial (κ × ι) k}
    (hP : IsMultiHomogeneous d P) (y : κ → ρ → ι → k) (I : κ × ι →₀ ℕ)
    (hne : linSubst y (hasseDeriv I P) ≠ 0) {B : ℕ} (hB : 0 < B) :
    ∃ z : κ → ρ → ℤ, (∀ h l, (z h l).natAbs ≤ B) ∧ ∃ I' : κ × ι →₀ ℕ,
      (∀ h, B * ∑ i, I' (h, i) ≤ Fintype.card ρ * d h) ∧
      eval (fun p : κ × ι ↦ ∑ l, (z p.1 l : k) * y p.1 l p.2) (hasseDeriv (I + I') P) ≠ 0 := by
  classical
  have hRmh : IsMultiHomogeneous (fun h ↦ d h - ∑ i, I (h, i))
      (linSubst y (hasseDeriv I P)) := (hP.hasseDeriv I).linSubst y
  have hdeg : ∀ p : κ × ρ, (linSubst y (hasseDeriv I P)).degreeOf p ≤ d p.1 := by
    intro p
    obtain ⟨h, l⟩ := p
    exact le_trans (hRmh.degreeOf_le h l) (Nat.sub_le _ _)
  obtain ⟨Z, hZ, J, hJ, hval⟩ := exists_eval_hasseDeriv_ne_zero hne hdeg hB
  have h1 : (shift (fun p ↦ ((Z p : k))) (linSubst y (hasseDeriv I P))).coeff J ≠ 0 := by
    rw [coeff_shift]
    exact hval
  rw [shift_linSubst] at h1
  obtain ⟨μ, hμ, hdegs⟩ := exists_coeff_ne_zero_of_coeff_linSubst_ne_zero y _ h1
  rw [coeff_shift, hasseDeriv_comp] at hμ
  refine ⟨fun h l ↦ Z (h, l), fun h l ↦ hZ (h, l), μ, fun h ↦ ?_, ?_⟩
  · calc B * ∑ i, μ (h, i) = B * ∑ l, J (h, l) := by rw [hdegs h]
      _ = ∑ l, B * J (h, l) := Finset.mul_sum _ _ _
      _ ≤ ∑ _l : ρ, d h := Finset.sum_le_sum fun l _ ↦ hJ (h, l)
      _ = Fintype.card ρ * d h := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  · rw [add_comm I μ]
    refine right_ne_zero_of_mul (a := ((μ.prod fun j m ↦ (m + I j).choose m : ℕ) : k)) ?_
    rw [← nsmul_eq_mul, ← map_nsmul]
    exact hμ

variable [Fintype κ]

/-- **The order of the new derivative**, Bombieri–Gubler's (7.37). Taking the grid `B = 2 n / η`
of Lemma 7.5.25, where `n` is the number of parameters in each block, the further differentiation
costs at most `card κ * η / 2` in the weighted order `∑ h, (∑ i, I (h, i)) / d h`, so a derivative
of weighted order at most `card κ * η / 2` that does not vanish identically on the product of the
spans is replaced by one of weighted order at most `card κ * η` that does not vanish at an
explicit point of the product. -/
theorem exists_eval_hasseDeriv_ne_zero_of_sum_div_le {d : κ → ℕ} {P : MvPolynomial (κ × ι) k}
    (hP : IsMultiHomogeneous d P) (y : κ → ρ → ι → k) {η : ℝ} (hη : 0 < η) (I : κ × ι →₀ ℕ)
    (hI : ∑ h, (∑ i, (I (h, i) : ℝ)) / (d h : ℝ) ≤ Fintype.card κ * η / 2)
    (hne : linSubst y (hasseDeriv I P) ≠ 0) :
    ∃ z : κ → ρ → ℤ, (∀ h l, ((z h l).natAbs : ℝ) ≤ 2 * Fintype.card ρ / η + 1) ∧
      ∃ I' : κ × ι →₀ ℕ, I ≤ I' ∧
        ∑ h, (∑ i, (I' (h, i) : ℝ)) / (d h : ℝ) ≤ Fintype.card κ * η ∧
        eval (fun p : κ × ι ↦ ∑ l, (z p.1 l : k) * y p.1 l p.2) (hasseDeriv I' P) ≠ 0 := by
  classical
  set B : ℕ := max ⌈2 * (Fintype.card ρ : ℝ) / η⌉₊ 1 with hBdef
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hnn : (0 : ℝ) ≤ 2 * (Fintype.card ρ : ℝ) / η := by positivity
  have hBge : 2 * (Fintype.card ρ : ℝ) / η ≤ B := by
    rw [hBdef, Nat.cast_max]
    exact le_max_of_le_left (Nat.le_ceil _)
  have hBle : (B : ℝ) ≤ 2 * Fintype.card ρ / η + 1 := by
    rw [hBdef, Nat.cast_max]
    exact max_le (le_of_lt (Nat.ceil_lt_add_one hnn)) (by linarith)
  obtain ⟨z, hz, I₀, hI₀, hval⟩ := exists_eval_hasseDeriv_add_ne_zero hP y I hne hB
  have hcardρ : (Fintype.card ρ : ℝ) ≤ η / 2 * B := by
    rw [div_le_iff₀ hη] at hBge
    linarith
  have hterm : ∀ h, (∑ i, (I₀ (h, i) : ℝ)) / (d h : ℝ) ≤ η / 2 := by
    intro h
    have hcast : (B : ℝ) * ∑ i, (I₀ (h, i) : ℝ) ≤ (Fintype.card ρ : ℝ) * (d h : ℝ) := by
      have h0 : ((B * ∑ i, I₀ (h, i) : ℕ) : ℝ) ≤ ((Fintype.card ρ * d h : ℕ) : ℝ) := by
        exact_mod_cast hI₀ h
      push_cast at h0
      exact h0
    rcases Nat.eq_zero_or_pos (d h) with hd | hd
    · rw [hd, Nat.cast_zero, div_zero]
      linarith
    · have hdR : (0 : ℝ) < d h := by exact_mod_cast hd
      rw [div_le_iff₀ hdR]
      refine le_of_mul_le_mul_left ?_ hBR
      calc (B : ℝ) * ∑ i, (I₀ (h, i) : ℝ) ≤ (Fintype.card ρ : ℝ) * (d h : ℝ) := hcast
        _ ≤ (η / 2 * B) * (d h : ℝ) := mul_le_mul_of_nonneg_right hcardρ (le_of_lt hdR)
        _ = B * (η / 2 * (d h : ℝ)) := by ring
  have hI₀sum : ∑ h, (∑ i, (I₀ (h, i) : ℝ)) / (d h : ℝ) ≤ Fintype.card κ * η / 2 := by
    calc ∑ h, (∑ i, (I₀ (h, i) : ℝ)) / (d h : ℝ) ≤ ∑ _h : κ, η / 2 :=
          Finset.sum_le_sum fun h _ ↦ hterm h
      _ = Fintype.card κ * η / 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  have hsplit : ∑ h, (∑ i, (((I + I₀) (h, i) : ℕ) : ℝ)) / (d h : ℝ)
      = (∑ h, (∑ i, (I (h, i) : ℝ)) / (d h : ℝ))
        + ∑ h, (∑ i, (I₀ (h, i) : ℝ)) / (d h : ℝ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    rw [← add_div, ← Finset.sum_add_distrib]
    exact congrArg (fun q ↦ q / (d h : ℝ))
      (Finset.sum_congr rfl fun i _ ↦ by rw [Finsupp.add_apply]; push_cast; ring)
  refine ⟨z, fun h l ↦ le_trans (by exact_mod_cast hz h l) hBle, I + I₀, le_self_add, ?_, hval⟩
  rw [hsplit]
  linarith

end SmallPoint

/-! ### Acceptance criteria -/

section Acceptance

/-- **Acceptance test: the hypothesis is not automatic.** A nonzero polynomial can vanish
identically on the product of the spans: over `ℚ`, in one block of two variables parametrized by
the single direction `(1, 1)`, the form `X 0 - X 1` restricts to `0`. This is why Layer 5.3 has
to produce a derivative that survives the restriction. -/
example : linSubst (fun _ : Unit ↦ fun _ : Fin 1 ↦ ![(1 : ℚ), 1])
    (X ((), 0) - X ((), 1)) = 0 := by
  rw [map_sub, linSubst_X, linSubst_X]
  simp

/-- **Acceptance test: non-vanishing at a small point.** -/
example {k : Type*} [Field k] [CharZero k] {κ ι ρ : Type*} [Fintype ι] [Fintype ρ] [Finite κ]
    {d : κ → ℕ} {P : MvPolynomial (κ × ι) k} (hP : IsMultiHomogeneous d P) (y : κ → ρ → ι → k)
    (I : κ × ι →₀ ℕ) (hne : linSubst y (hasseDeriv I P) ≠ 0) {B : ℕ} (hB : 0 < B) :
    ∃ z : κ → ρ → ℤ, (∀ h l, (z h l).natAbs ≤ B) ∧ ∃ I' : κ × ι →₀ ℕ,
      (∀ h, B * ∑ i, I' (h, i) ≤ Fintype.card ρ * d h) ∧
      eval (fun p : κ × ι ↦ ∑ l, (z p.1 l : k) * y p.1 l p.2) (hasseDeriv (I + I') P) ≠ 0 :=
  exists_eval_hasseDeriv_add_ne_zero hP y I hne hB

end Acceptance

end MvPolynomial
