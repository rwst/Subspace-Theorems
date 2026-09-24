/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.WedgeDomain
public import DiophantineApproximation.MinimaBounds

/-!
# The exponents of the wedge domain: a box, and a negative weight

The wedge domain of Layer 4.5 is an approximation domain in `⋀^p Kⁱ` whose exponents
`NumberField.wedgeExponent` move with the level `Q`: at an infinite place they are the sums of the
original exponents over a `p`-subset, corrected by `logb Q` of a product of minima, a ratio of two
more and a constant. Step IX of Bombieri–Gubler's proof needs two things about them, and this file
proves both.

**They stay in a box.** With the minima confined between `Q ^ (-B)` and `Q ^ B`
(`MinimaBounds.lean`), the correction is between `-G` and `G` for a `G` that does not depend on
`Q`, on the bijections or on `k`. That is what lets Layer 6.1 round them to a grid.

**Their weight is negative, uniformly.** Lemma 7.5.31 bounds `Q` to the weight of the wedge domain
by a constant times the jump `(μ (k - 1) / μ k) ^ d` of the minima, and the choice (7.41) of `k`
bounds that jump by the last minimum, which Layer 4.3 bounds below by a positive power of `Q`.
Together: the weight of the wedge domain is at most `weight / (2 (#ι) ^ 2)` at every large enough
level — a negative number fixed in advance.

## Main results

* `NumberField.abs_wedgeExponent_sub_sum_le`: **the box**.
* `NumberField.exists_forall_approxWeight_wedgeExponent_le`: **the negative weight**, uniformly in
  the level, the rank and the bijections.
* `Real.abs_logb_le`, `Real.le_div_of_rpow_pow_le`: the two arithmetic steps, factored out.

## Implementation notes

⚠ **The box is uniform in `k` and in the bijections.** The correction at an infinite place reads
the minima through the bijection `π v`, which changes with `Q`; but every minimum is confined to
the same interval, so the bound is the same for all of them. The same goes for the constant of
Evertse's lemma, which is fixed before `Q` and is swallowed by one unit of exponent.

⚠ **The rank enters the weight only through `N - R`.** The chain raises the jump to the power
`d N (N - R)`, so the constant that survives depends on `R`; it is bounded by taking the maximum
of the base with `1` and the exponent with `(#ι) ^ 2`, which is why the conclusion carries
`2 (#ι) ^ 2` and not the sharper `2 N (N - R)`.

⚠ **Both statements quantify over `π` and over `R` after `Q`.** Layer 6.1 chooses `k`, the
bijections and the realizing vectors only after it has fixed `Q`, so every constant here is chosen
before any of them.

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

omit [NumberField K] in
open scoped Classical in
/-- **The exponents of the wedge domain stay in a box around the sums of the original
exponents** (Bombieri–Gubler, Step IX): the correction is a logarithm to the base `Q` of a
product of `p` minima, a ratio of two more and a constant, all between two fixed powers of `Q`. -/
theorem abs_wedgeExponent_sub_sum_le {c : AbsoluteValue K ℝ → ι → ℝ}
    {π : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι} {μ : ℕ → ℝ} {C Q B : ℝ} {k p : ℕ}
    (hQ : 1 < Q) (hCQ : C ≤ Q) (hQC : 1 ≤ C * Q) (hB : 0 ≤ B)
    (hk : k < Fintype.card ι) (hp : p ≤ Fintype.card ι)
    (hμlow : ∀ j, j < Fintype.card ι → Q ^ (-B) ≤ μ j)
    (hμhigh : ∀ j, j < Fintype.card ι → μ j ≤ Q ^ B)
    (v : AbsoluteValue K ℝ) (T : Set.powersetCard ι p) :
    |wedgeExponent c π μ C Q k p v T - ∑ t ∈ (T : Finset ι), c v t|
      ≤ 1 + B * Fintype.card ι + 2 * B := by
  have hQ0 : (0 : ℝ) < Q := lt_trans one_pos hQ
  have hG : (0 : ℝ) ≤ 1 + B * Fintype.card ι + 2 * B := by positivity
  by_cases hv : IsNonarchimedean v
  · simp only [wedgeExponent, hv, ↓reduceIte, add_zero, sub_self, abs_zero]
    exact hG
  · rw [wedgeExponent, add_sub_cancel_left]
    simp only [hv, ↓reduceIte]
    have hμ0 : ∀ j, j < Fintype.card ι → 0 < μ j := fun j hj ↦
      lt_of_lt_of_le (Real.rpow_pos_of_pos hQ0 _) (hμlow j hj)
    set X : ℝ := C * (∏ t ∈ (T : Finset ι), μ ((π v).symm t)) *
      if ∀ t ∈ (T : Finset ι), k ≤ ((π v).symm t : ℕ) then μ (k - 1) / μ k else 1 with hX
    have hC0 : 0 < C := by nlinarith
    have hprodpos : 0 < ∏ t ∈ (T : Finset ι), μ ((π v).symm t) :=
      Finset.prod_pos fun t _ ↦ hμ0 _ ((π v).symm t).2
    have hcard : (T : Finset ι).card = p := Set.powersetCard.card_eq T
    have hprodle : (∏ t ∈ (T : Finset ι), μ ((π v).symm t)) ≤ Q ^ (B * Fintype.card ι) := by
      have h1 : (∏ t ∈ (T : Finset ι), μ ((π v).symm t)) ≤ ∏ _t ∈ (T : Finset ι), Q ^ B :=
        Finset.prod_le_prod₀ (fun t _ ↦ (hμ0 _ ((π v).symm t).2).le)
          fun t _ ↦ hμhigh _ ((π v).symm t).2
      rw [Finset.prod_const, hcard, ← Real.rpow_natCast (Q ^ B) p, ← Real.rpow_mul hQ0.le] at h1
      exact h1.trans (Real.rpow_le_rpow_of_exponent_le hQ.le
        (by have : (p : ℝ) ≤ Fintype.card ι := by exact_mod_cast hp
            nlinarith))
    have hprodge : Q ^ (-(B * Fintype.card ι)) ≤ ∏ t ∈ (T : Finset ι), μ ((π v).symm t) := by
      have h1 : (∏ _t ∈ (T : Finset ι), Q ^ (-B)) ≤ ∏ t ∈ (T : Finset ι), μ ((π v).symm t) :=
        Finset.prod_le_prod₀ (fun t _ ↦ (Real.rpow_pos_of_pos hQ0 _).le)
          fun t _ ↦ hμlow _ ((π v).symm t).2
      rw [Finset.prod_const, hcard, ← Real.rpow_natCast (Q ^ (-B)) p, ← Real.rpow_mul hQ0.le] at h1
      refine le_trans (Real.rpow_le_rpow_of_exponent_le hQ.le ?_) h1
      have : (p : ℝ) ≤ Fintype.card ι := by exact_mod_cast hp
      nlinarith
    have hρpos : (0 : ℝ) < if ∀ t ∈ (T : Finset ι), k ≤ ((π v).symm t : ℕ)
        then μ (k - 1) / μ k else 1 := by
      split_ifs
      · exact div_pos (hμ0 _ (by omega)) (hμ0 _ hk)
      · exact one_pos
    have hρle : (if ∀ t ∈ (T : Finset ι), k ≤ ((π v).symm t : ℕ) then μ (k - 1) / μ k else 1)
        ≤ Q ^ (2 * B) := by
      have h2B : Q ^ B / Q ^ (-B) = Q ^ (2 * B) := by
        rw [← Real.rpow_sub hQ0]
        ring_nf
      split_ifs
      · rw [← h2B, div_le_div_iff₀ (hμ0 k hk) (Real.rpow_pos_of_pos hQ0 _)]
        exact mul_le_mul (hμhigh _ (by omega)) (hμlow k hk) (Real.rpow_nonneg hQ0.le _)
          (Real.rpow_nonneg hQ0.le _)
      · calc (1 : ℝ) = Q ^ (0 : ℝ) := (Real.rpow_zero Q).symm
          _ ≤ Q ^ (2 * B) := Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith)
    have hρge : Q ^ (-(2 * B))
        ≤ if ∀ t ∈ (T : Finset ι), k ≤ ((π v).symm t : ℕ) then μ (k - 1) / μ k else 1 := by
      have h2B : Q ^ (-B) / Q ^ B = Q ^ (-(2 * B)) := by
        rw [← Real.rpow_sub hQ0]
        ring_nf
      split_ifs
      · rw [← h2B, div_le_div_iff₀ (Real.rpow_pos_of_pos hQ0 _) (hμ0 k hk)]
        exact mul_le_mul (hμlow _ (by omega)) (hμhigh k hk) (hμ0 k hk).le
          (hμ0 _ (by omega)).le
      · exact Real.rpow_le_one_of_one_le_of_nonpos hQ.le (by linarith)
    have hX0 : 0 < X := by
      rw [hX]
      exact mul_pos (mul_pos hC0 hprodpos) hρpos
    refine Real.abs_logb_le hQ hX0 ?_ ?_
    · have hCge : Q ^ (-1 : ℝ) ≤ C := by
        rw [Real.rpow_neg_one, inv_le_iff_one_le_mul₀ hQ0]
        linarith [hQC]
      have := mul_le_mul (mul_le_mul hCge hprodge (Real.rpow_nonneg hQ0.le _) hC0.le) hρge
        (Real.rpow_nonneg hQ0.le _) (mul_nonneg hC0.le hprodpos.le)
      have hsplit : Q ^ (-(1 + B * (Fintype.card ι : ℝ) + 2 * B))
          = Q ^ (-1 : ℝ) * Q ^ (-(B * Fintype.card ι)) * Q ^ (-(2 * B)) := by
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
        ring_nf
      rw [hsplit]
      exact this
    · have := mul_le_mul (mul_le_mul hCQ hprodle hprodpos.le (by linarith)) hρle hρpos.le
        (by positivity)
      have hsplit : Q ^ (1 + B * (Fintype.card ι : ℝ) + 2 * B)
          = Q * Q ^ (B * Fintype.card ι) * Q ^ (2 * B) := by
        rw [Real.rpow_add hQ0, Real.rpow_add hQ0, Real.rpow_one]
      rw [hsplit]
      exact this

open scoped Classical in
/-- **The weight of the wedge domain is negative, uniformly in the level** (Bombieri–Gubler,
7.5.31 and (7.41) put together): for a domain of rank `R` with `1 ≤ R ≤ k` whose jump at `k` is
large enough, the weight of the wedge domain in `⋀^p` is at most `weight / (2 (#ι) ^ 2)` at every
large enough level, and that is a negative number depending on nothing but the data. -/
theorem exists_forall_approxWeight_wedgeExponent_le [Nonempty ι]
    {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {c : AbsoluteValue K ℝ → ι → ℝ}
    (hc : approxWeight Sfin c < 0) {C : ℝ} (hC : 0 < C) {k p : ℕ}
    (hkp : k + p = Fintype.card ι) (hp : 0 < p) :
    ∃ Q₂ : ℝ, 1 < Q₂ ∧ ∀ Q : ℝ, Q₂ ≤ Q → ∀ R : ℕ, 1 ≤ R → R ≤ k →
      (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) (k - 1) /
          successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) k) ^ (Fintype.card ι - R)
        ≤ (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)
            (Fintype.card ι - 1))⁻¹ →
      ∀ π : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι,
        approxWeight Sfin (wedgeExponent c π
            (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)) C Q k p)
          ≤ approxWeight Sfin c / (2 * (Fintype.card ι : ℝ) ^ 2) := by
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
    fun Q hQ R hR1 hRk hjump π ↦ ?_⟩
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
  have hwedge := rpow_approxWeight_wedgeExponent_le hLInf hLFin c π hQ1 hC hkp hp
  have hQw0 : (0 : ℝ) ≤ Q ^ approxWeight Sfin (wedgeExponent c π μ C Q k p) :=
    (Real.rpow_pos_of_pos hQ0 _).le
  have hfinal : (Q ^ approxWeight Sfin (wedgeExponent c π μ C Q k p)) ^ s ≤ C₂ * Q ^ W := by
    have h1 : (Q ^ approxWeight Sfin (wedgeExponent c π μ C Q k p)) ^ s ≤ (C₁ * r ^ d) ^ s :=
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
