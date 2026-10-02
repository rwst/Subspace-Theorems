/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.WedgeDomain
public import DiophantineApproximation.MinimaBounds

/-!
# The weight of the wedge domain is negative

The wedge domain of Layer 4.5 is an approximation domain in `⋀^p Kⁱ` whose exponents move with the
level `Q`. Step IX of Bombieri–Gubler's proof needs its weight to be negative uniformly in `Q`,
and this file proves it for every system of exponents whose weight is given by the exact formula
of Layer 4.5 (`NumberField.rpow_approxWeight_wedgeExponent`): the wedge domain of the book, and the
wedge domain with the minima at one place (`NumberField.rpow_approxWeight_wedgeExponentAt`) that
Layer 6.1 uses.

Lemma 7.5.31 bounds `Q` to that weight by a constant times the jump `(μ (k - 1) / μ k) ^ d` of the
minima, and the choice (7.41) of `k` bounds that jump by the last minimum, which Layer 4.3 bounds
below by a positive power of `Q`. Together: the weight is at most `weight / (2 (#ι) ^ 2)` at every
large enough level — a negative number fixed in advance.

## Main results

* `NumberField.exists_forall_approxWeight_wedgeExponent_le`: **the negative weight**, uniformly in
  the level, the rank and the exponents.
* `Real.abs_logb_le`, `Real.le_div_of_rpow_pow_le`: the two arithmetic steps, factored out.

## Implementation notes

⚠ **The rank enters the weight only through `N - R`.** The chain raises the jump to the power
`d N (N - R)`, so the constant that survives depends on `R`; it is bounded by taking the maximum
of the base with `1` and the exponent with `(#ι) ^ 2`, which is why the conclusion carries
`2 (#ι) ^ 2` and not the sharper `2 N (N - R)`.

⚠ **The statement quantifies over the exponents and over `R` after `Q`.** Layer 6.1 chooses `k`,
the bijection and the realizing vectors only after it has fixed `Q`, so every constant here is
chosen before any of them; the exponents enter only through the exact formula for their weight.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 7.5.31 and 7.5.32 (Step IX).

This is part of Layer 6.1 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset Module NumberField NumberField.mixedEmbedding exteriorPower

namespace Real

/-- A logarithm to a base greater than one, of an argument confined between two powers. -/
theorem abs_logb_le {Q X G : ℝ} (hQ : 1 < Q) (hX : 0 < X) (h1 : Q ^ (-G) ≤ X) (h2 : X ≤ Q ^ G) :
    |Real.logb Q X| ≤ G := by
  have hQ0 : (0 : ℝ) < Q := lt_trans one_pos hQ
  have hlogQ : 0 < Real.log Q := Real.log_pos hQ
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · rw [Real.logb, le_div_iff₀ hlogQ]
    have h := Real.log_le_log (Real.rpow_pos_of_pos hQ0 (-G)) h1
    rwa [Real.log_rpow hQ0] at h
  · rw [Real.logb, div_le_iff₀ hlogQ]
    have h := Real.log_le_log hX h2
    rwa [Real.log_rpow hQ0] at h

/-- From a power of `Q` to an exponent bound: if `(Q ^ a) ^ s` is at most `C * Q ^ W` with `W`
negative, `C` at least `1` and `Q` large enough that `2 log C ≤ (-W) log Q`, then `a` is at most
`W / (2 N ^ 2)` for every `N` with `s ≤ N ^ 2`. -/
theorem le_div_of_rpow_pow_le {a W Q C : ℝ} {s N : ℕ} (hQ : 1 < Q) (hs : 0 < s)
    (hsN : s ≤ N ^ 2) (hW : W < 0) (hC : 1 ≤ C)
    (hlogQ : 2 * Real.log C ≤ (-W) * Real.log Q) (h : (Q ^ a) ^ s ≤ C * Q ^ W) :
    a ≤ W / (2 * (N : ℝ) ^ 2) := by
  have hQ0 : (0 : ℝ) < Q := lt_trans one_pos hQ
  have hlog : 0 < Real.log Q := Real.log_pos hQ
  have hpow : (Q ^ a) ^ s = Q ^ (a * s) := by
    rw [← Real.rpow_natCast (Q ^ a) s, ← Real.rpow_mul hQ0.le]
  rw [hpow] at h
  have hlogle : a * s * Real.log Q ≤ Real.log C + W * Real.log Q := by
    have hle := Real.log_le_log (Real.rpow_pos_of_pos hQ0 _) h
    rwa [Real.log_rpow hQ0, Real.log_mul (by linarith) (Real.rpow_pos_of_pos hQ0 W).ne',
      Real.log_rpow hQ0] at hle
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hsN' : (s : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hsN
  have hN0 : (0 : ℝ) < (N : ℝ) ^ 2 := lt_of_lt_of_le hs0 hsN'
  have hhalf : a * s ≤ W / 2 := by
    have : a * s * Real.log Q ≤ (W / 2) * Real.log Q := by nlinarith
    exact le_of_mul_le_mul_right (by linarith) hlog
  have hwc : a < 0 := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  have hstep : a * (2 * (N : ℝ) ^ 2) ≤ a * (2 * s) :=
    mul_le_mul_of_nonpos_left (by linarith) hwc.le
  nlinarith

end Real

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]

open scoped Classical in
/-- **The constant of the wedge weight**: `max (max C₁ 1 ^ (N ^ 2) / A₃) 1`, where
`C₁ = C ^ (M d) a₂ ^ binom(N - 1, p - 1)`, `a₂ = 2 ^ (d N) ∏_{v ∈ Sfin} N(v) ^ N / approxConst`
and `A₃ = 2 ^ (d N) / ((d N)! c_K ^ (d N) approxConst)`. -/
noncomputable def wedgeWeightConst (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (C : ℝ) (p : ℕ) : ℝ :=
  max (max (C ^ (Fintype.card (Set.powersetCard ι p) * finrank ℚ K) *
      (2 ^ (finrank ℚ K * Fintype.card ι) *
        (∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ Fintype.card ι) /
          approxConst Sfin L) ^ ((Fintype.card ι - 1).choose (p - 1))) 1 ^
      (Fintype.card ι ^ 2) *
    (2 ^ (finrank ℚ K * Fintype.card ι) / ((finrank ℚ K * Fintype.card ι).factorial *
      integralBasisHouse K ^ (finrank ℚ K * Fintype.card ι) * approxConst Sfin L))⁻¹) 1

omit [LinearOrder ι] in
open scoped Classical in
/-- **The weight of the wedge domain is negative, uniformly in the level** (Bombieri–Gubler,
7.5.31 and (7.41) put together): for a domain of rank `R` with `1 ≤ R ≤ k` whose jump at `k` is
large enough, every system of exponents in `⋀^p` with the exact weight of Layer 4.5 at the minima
of the domain has weight at most `weight / (2 (#ι) ^ 2)` at every large enough level, and that is a
negative number depending on nothing but the data. -/
theorem exists_forall_approxWeight_wedgeExponent_le [Nonempty ι]
    {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {c : AbsoluteValue K ℝ → ι → ℝ}
    (hc : approxWeight Sfin c < 0) {C : ℝ} (hC : 0 < C) {k p : ℕ}
    (hkp : k + p = Fintype.card ι) (hp : 0 < p) :
    ∃ Q₂ : ℝ, 1 < Q₂ ∧ Q₂ = max 2 (Real.exp (2 * Real.log (wedgeWeightConst Sfin L C p) /
        (-approxWeight Sfin c))) ∧ ∀ Q : ℝ, Q₂ ≤ Q → ∀ R : ℕ, 1 ≤ R → R ≤ k →
      (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) (k - 1) /
          successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) k) ^ (Fintype.card ι - R)
        ≤ (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)
            (Fintype.card ι - 1))⁻¹ →
      ∀ c' : AbsoluteValue K ℝ → Set.powersetCard ι p → ℝ,
      Q ^ approxWeight Sfin c' =
        Q ^ ((Fintype.card ι - 1).choose (p - 1) * approxWeight Sfin c) *
          (C ^ Fintype.card (Set.powersetCard ι p) *
            (∏ j ∈ Finset.range (Fintype.card ι),
              successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) j) ^
                (Fintype.card ι - 1).choose (p - 1) *
              (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) (k - 1) /
                successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) k)) ^
            finrank ℚ K →
        approxWeight Sfin c' ≤ approxWeight Sfin c / (2 * (Fintype.card ι : ℝ) ^ 2) := by
  set N := Fintype.card ι with hN
  set d := finrank ℚ K with hd
  set W := approxWeight Sfin c with hW
  set M := Fintype.card (Set.powersetCard ι p) with hM
  set a₂ : ℝ := 2 ^ (d * N) *
    (∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ N) / approxConst Sfin L with ha₂
  set C₁ : ℝ := C ^ (M * d) * a₂ ^ ((N - 1).choose (p - 1)) with hC₁
  set A₃ : ℝ := 2 ^ (d * N) / ((d * N).factorial * integralBasisHouse K ^ (d * N) *
    approxConst Sfin L) with hA₃
  have hconst : 0 < approxConst Sfin L := approxConst_pos hLInf hLFin
  have hA₃0 : 0 < A₃ := by
    have := zero_lt_one.trans_le (one_le_integralBasisHouse K)
    rw [hA₃]
    positivity
  have ha₂0 : 0 ≤ a₂ := by
    rw [ha₂]
    positivity
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]
    positivity
  set C₂ : ℝ := max (max C₁ 1 ^ (N ^ 2) * A₃⁻¹) 1 with hC₂
  have hC₂1 : 1 ≤ C₂ := le_max_right _ _
  have hC₂0 : 0 < C₂ := lt_of_lt_of_le one_pos hC₂1
  refine ⟨max 2 (Real.exp (2 * Real.log C₂ / (-W))), lt_of_lt_of_le one_lt_two (le_max_left _ _),
    by rw [hC₂, hC₁, ha₂, hA₃, wedgeWeightConst], fun Q hQ R hR1 hRk hjump c' hc' ↦ ?_⟩
  have hQ2 : (2 : ℝ) ≤ Q := le_trans (le_max_left _ _) hQ
  have hQ1 : (1 : ℝ) < Q := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hlogQ : 2 * Real.log C₂ ≤ (-W) * Real.log Q := by
    have hexp : Real.exp (2 * Real.log C₂ / (-W)) ≤ Q := le_trans (le_max_right _ _) hQ
    have hle : 2 * Real.log C₂ / (-W) ≤ Real.log Q := by
      have := Real.log_le_log (Real.exp_pos _) hexp
      rwa [Real.log_exp] at this
    rw [div_le_iff₀ (by linarith)] at hle
    linarith
  set μ := successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) with hμ
  have hDt : DiscreteTopology (approxLattice Sfin L c Q) :=
    discreteTopology_approxLattice hLFin c hQ0.ne'
  have : DiscreteTopology (approxModule Sfin L c Q).mixedImage := hDt
  have hZ : IsZLattice ℝ (approxLattice Sfin L c Q) := isZLattice_approxLattice hLFin c hQ0.ne'
  have : IsZLattice ℝ (approxModule Sfin L c Q).mixedImage := hZ
  have hNpos : 0 < N := Fintype.card_pos
  have hkN : k < N := by omega
  have hμpos : ∀ j, j < N → 0 < μ j := fun j hj ↦
    successiveMinimum_pos _ (convex_approxBody L c Q) (fun z hz ↦ neg_mem_approxBody hz)
      ⟨0, mem_interior_iff_mem_nhds.2 (approxBody_mem_nhds_zero L c hQ0)⟩
      (isBounded_approxBody hLInf c Q) hj
  set r : ℝ := μ (k - 1) / μ k with hr
  have hr0 : 0 ≤ r := le_of_lt (div_pos (hμpos _ (by omega)) (hμpos k hkN))
  set s : ℕ := N * (N - R) with hs
  have hs0 : 0 < s := Nat.mul_pos hNpos (by omega)
  have hsN : s ≤ N ^ 2 := by
    rw [hs, sq]
    exact Nat.mul_le_mul_left N (by omega)
  have hmink := le_successiveMinimum_approx_pow (Sfin := Sfin) (L := L) hLInf hLFin c hQ0
  have hchain : r ^ (d * s) ≤ A₃⁻¹ * Q ^ W := by
    have h1 : r ^ (d * s) = (r ^ (N - R)) ^ (d * N) := by
      rw [← pow_mul]
      congr 1
      rw [hs]
      ring
    have h2 : (r ^ (N - R)) ^ (d * N) ≤ ((μ (N - 1))⁻¹) ^ (d * N) :=
      pow_le_pow_left₀ (pow_nonneg hr0 _) hjump _
    have h4 : (μ (N - 1) ^ (d * N))⁻¹ ≤ (A₃ * Q ^ (-W))⁻¹ := inv_anti₀ (by positivity) hmink
    calc r ^ (d * s) = (r ^ (N - R)) ^ (d * N) := h1
      _ ≤ ((μ (N - 1))⁻¹) ^ (d * N) := h2
      _ = (μ (N - 1) ^ (d * N))⁻¹ := by rw [inv_pow]
      _ ≤ (A₃ * Q ^ (-W))⁻¹ := h4
      _ = A₃⁻¹ * Q ^ W := by rw [mul_inv, Real.rpow_neg hQ0.le, inv_inv]
  have hwedge := rpow_approxWeight_le_of_eq hLInf hLFin c hQ1 hC hkp hp hc'
  have hQw0 : (0 : ℝ) ≤ Q ^ approxWeight Sfin (c') :=
    (Real.rpow_pos_of_pos hQ0 _).le
  have hfinal : (Q ^ approxWeight Sfin (c')) ^ s ≤ C₂ * Q ^ W := by
    have h1 : (Q ^ approxWeight Sfin (c')) ^ s ≤ (C₁ * r ^ d) ^ s :=
      pow_le_pow_left₀ hQw0 hwedge s
    have h2 : (C₁ * r ^ d) ^ s = C₁ ^ s * r ^ (d * s) := by
      rw [mul_pow, ← pow_mul]
    have h3 : C₁ ^ s ≤ max C₁ 1 ^ (N ^ 2) :=
      le_trans (pow_le_pow_left₀ hC₁0 (le_max_left _ _) s)
        (pow_le_pow_right₀ (le_max_right _ _) hsN)
    have h4 : C₁ ^ s * r ^ (d * s) ≤ max C₁ 1 ^ (N ^ 2) * (A₃⁻¹ * Q ^ W) :=
      mul_le_mul h3 hchain (pow_nonneg hr0 _) (by positivity)
    have h5 : max C₁ 1 ^ (N ^ 2) * (A₃⁻¹ * Q ^ W) ≤ C₂ * Q ^ W := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hQ0.le _)
    rw [h2] at h1
    linarith
  exact Real.le_div_of_rpow_pow_le hQ1 hs0 hsN hc hC₂1 hlogQ hfinal

end NumberField
