/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.BombieriVaalerEntries
public import ArithmeticHeights.Gelfond
public import DiophantineApproximation.MonomialDeviation
public import DiophantineApproximation.PolynomialDeterminantHeight
public import DiophantineApproximation.MultiHomogeneous
public import DiophantineApproximation.MvHasseDerivHeight

/-!
# The multihomogeneous auxiliary polynomial

Step I of the proof of the Subspace Theorem builds one polynomial in `m` blocks of `n + 1`
variables that vanishes, to high order in every block, along every one of the finitely many
systems of linear forms in play. This file is that construction: Bombieri–Gubler's (7.5.14) and
Lemma 7.5.15.

The space of candidates is the multihomogeneous polynomials of a fixed multidegree `d : κ → ℕ`,
whose monomials are `MvPolynomial.multiMons d` (`DiophantineApproximation.MultiHomogeneous`). For
one invertible matrix `A` the polynomial read in the coordinates `A · X h` is
`MvPolynomial.blockSubst A⁻¹ P`, and the expansion coefficients of the Hasse derivatives that
Lemma 7.5.15 is about are the coefficients of `blockSubst A⁻¹ (hasseDeriv I P)`.

Three things have to be supplied. *That enough coefficients may be killed*: the monomials whose
exponent of one variable is far below its mean `∑ h, d h / (n + 1)` are exponentially few
(`DiophantineApproximation.MonomialDeviation`), so the conditions are at most half as many as the
unknowns and Siegel's lemma applies. *That the height stays linear in `∑ h, d h`*: the height of
the condition matrix and of a substituted Hasse derivative are controlled here from the local
factors, the only inputs being the number of monomials, the number of variables in a block, and
one reference tuple collecting the entries of all the matrices. *That killing those coefficients
kills the others*: the vanishing propagates from order `0` to order `I` by the chain rule, which
is `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero`.

## Main results

* `Height.mulHeight_le_pow_mul_mul_pow` and `Height.mulHeight_le_pow_mul_pow`: **transport from
  local factors to the height** — a tuple whose local factor is at most `C` times a product of a
  local factor of `z` and a `D`-th power of one of `y` at the archimedean absolute values, and at
  most that product at the nonarchimedean ones, has height at most
  `C ^ totalWeight K * H z * H y ^ D`.
* `MvPolynomial.iSup_coeff_blockSubst_le` and
  `MvPolynomial.iSup_coeff_blockSubst_le_of_isNonarchimedean`: **the local factor of a substituted
  polynomial**, with `#support · (#ι · ‖A‖_v) ^ D` at an archimedean absolute value and
  `‖A‖_v ^ D` at a nonarchimedean one (Gauss's lemma).
* `MvPolynomial.mulHeight_blockSubst_hasseDeriv_le` and its logarithmic form
  `MvPolynomial.logHeight_blockSubst_hasseDeriv_le`: **the height of a substituted Hasse
  derivative**.
* `MvPolynomial.mulHeight_matrix_blockSubst_monomial_le`: **the height of the condition matrix**,
  which does not depend on the number of rows or columns.
* `MvPolynomial.mulHeight_eq_mulHeight_coeff_multiMons` and
  `MvPolynomial.absMulHeight_coeff_multiMons`: the dictionary between the vector Siegel's lemma
  produces and the polynomial the milestone is about.
* `MvPolynomial.exists_ne_zero_isMultiHomogeneous_coeff_blockSubst_eq_zero`: **Siegel's lemma in
  the multihomogeneous setting** — at most half as many linear conditions as monomials give a
  nonzero multihomogeneous solution of logarithmic height `O (∑ h, d h)`.
* `MvPolynomial.exists_ne_zero_isMultiHomogeneous_forall_coeff_blockSubst_hasseDeriv_eq_zero`:
  **the milestone**, Lemma 7.5.15.

## Implementation notes

⚠ **The chain rule is the whole content of the vanishing statement.** The expansion coefficient
`a(L v; J; I)` is *not* `binom (J + I) I · a(L v; J + I; 0)`: Bombieri–Gubler differentiate in the
original coordinates and expand in the transformed ones, so a coefficient of `∂_I P` is a
combination, over all orders with the same block degrees, of coefficients of `P` read in the
transformed coordinates. `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero` proves exactly what is
needed by induction on the order and never names that combination. It needs characteristic zero,
because `hasseDeriv_comp` produces a positive integer factor that has to be inverted.

⚠ **The conditions imposed are at order `0` only, and they are indexed by the monomial.** For each
`v ∈ S`, each coordinate `i`, and each monomial `N` of multidegree `d` with
`∑ h, N (h, i) / d h ≤ m/(n+1) − m η`, the condition is `(blockSubst (A v)⁻¹ P).coeff N = 0`. That
this implies the vanishing at every order `I` with `∑ h, (∑ i, I (h, i)) / d h ≤ m η` and every
`J` with `∑ h, J (h, i) / d h ≤ m/(n+1) − 2 m η` is exactly where the factor `2` in the book's
`2 m η` is spent: `N = J + I'` moves the threshold by at most `m η`.

⚠ **The upper half of the book's interval is free.** A Hasse derivative of a multihomogeneous
polynomial is multihomogeneous (`MvPolynomial.IsMultiHomogeneous.hasseDeriv`), so a nonzero
coefficient has `∑ i, ∑ h, J (h, i) / d h = m − ∑ h, (∑ i, I (h, i)) / d h`. If one exponent
exceeds `m/(n+1) + 2 n m η`, the remaining `n` of them average below `m/(n+1) − 2 m η`, and the
lower half applies to one of those. This is why `n ≥ 1` is needed a second time.

⚠ **The hypothesis on `m` is strict here.** Bombieri–Gubler ask
`m ≥ 4 log (2 (n+1) |S|) / ((n+1)(n+2) η²)`, which leaves no room for the error term
`(η (n+1)(n+2)/2)² / (2(n+1)) · ∑ h, 1/d h` of the Chernoff bound; that term is positive for every
`d` and tends to `0` only as `d → ∞`. The strict inequality creates a positive slack, and `D₀` is
chosen to make the error term smaller than it. Replacing `2 (n+1) |S|` by `4 (n+1) |S|` and keeping
`≥` would do the same.

⚠ **`C₂` and `C₃` are allowed to depend on `m`, `S` and `η`.** The book claims they depend only on
`K` and the forms. That is true — the `m`-dependence sits in `log #multiMons d`, which is
`O (log d)` and could be absorbed into `D₀` — but Layer 5.6 fixes `m` before it uses `C₂`, so
nothing downstream needs the stronger form, and the crude bound
`log #multiMons d ≤ #ι · ∑ h, d h` keeps the proof linear.

⚠ **Mathlib's finiteness of the nonarchimedean local factors is private.** `Height.mulHeight` is
built from a `finprod` over the nonarchimedean absolute values, and the fact that the local factors
of a nonzero tuple differ from `1` at only finitely many of them is proved in Mathlib as a
`private lemma`. It is reproved here as `Height.hasFiniteMulSupport_iSup`; `fun_prop` cannot be
used for it across the module boundary, because it would have to name the private lemma.

⚠ **Only the `≤` direction of the height transport is available.** Mathlib's
`Finsupp.mulHeight_le_of_forall_iSup_le` needs *equality* of the local factors at the
nonarchimedean absolute values. The archimedean product and the nonarchimedean `finprod` are
therefore compared separately here (`finprod_le_finprod₀`, `finprod_pow`, `finprod_mul_distrib`).

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
(7.5.14), Lemma 7.5.15 and (7.20)–(7.25).

This is Layer 5.2 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset Height AdmissibleAbsValues Real

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι ρ : Type*} [Finite ι] [Finite ρ]

/-- The local factors of a nonzero tuple differ from `1` at only finitely many nonarchimedean
absolute values. Mathlib proves this, but privately. -/
theorem hasFiniteMulSupport_iSup {x : ι → K} (hx : x ≠ 0) :
    (fun v : nonarchAbsVal (K := K) ↦ ⨆ i, v.val (x i)).HasFiniteMulSupport := by
  classical
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  have : Nonempty ι := ⟨i₀⟩
  have hsub : Function.mulSupport (fun v : nonarchAbsVal (K := K) ↦ ⨆ i, v.val (x i))
      ⊆ ⋃ i ∈ {i : ι | x i ≠ 0},
        (fun v : nonarchAbsVal (K := K) ↦ v.val (x i)) ⁻¹' {y | y ≠ 1} := by
    intro v hv
    by_contra hc
    refine hv ?_
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_ofPred_eq, not_exists] at hc
    have hall : ∀ i, v.val (x i) ≤ 1 := by
      intro i
      rcases eq_or_ne (x i) 0 with h | h
      · rw [h, map_zero]; exact zero_le_one
      · exact le_of_eq (not_not.mp (fun hne ↦ hc i h hne))
    have h1 : v.val (x i₀) = 1 := not_not.mp (fun hne ↦ hc i₀ hi₀ hne)
    refine le_antisymm (Real.iSup_le hall zero_le_one) ?_
    rw [← h1]
    exact Finite.le_ciSup_of_le i₀ le_rfl
  exact Set.Finite.subset
    (Set.Finite.biUnion (Set.toFinite _) fun i hi ↦ AdmissibleAbsValues.hasFiniteMulSupport hi)
    hsub

/-- **Transport from local factors to the height.** A tuple whose local factor is at most `C`
times the local factor of `z` and the `D`-th power of that of `y` at every archimedean absolute
value, and at most that product at every nonarchimedean one, has height at most
`C ^ totalWeight K * H(z) * H(y) ^ D`. -/
theorem mulHeight_le_pow_mul_mul_pow {τ : Type*} [Finite τ] {x : ι → K} {z : τ → K} {y : ρ → K}
    {C : ℝ} {D : ℕ} (hC : 1 ≤ C) (hz : z ≠ 0) (hy : y ≠ 0)
    (harch : ∀ v ∈ archAbsVal (K := K),
      (⨆ i, v (x i)) ≤ C * ((⨆ t, v (z t)) * (⨆ r, v (y r)) ^ D))
    (hnon : ∀ v ∈ nonarchAbsVal (K := K),
      (⨆ i, v (x i)) ≤ (⨆ t, v (z t)) * (⨆ r, v (y r)) ^ D) :
    mulHeight x ≤ C ^ totalWeight K * (mulHeight z * mulHeight y ^ D) := by
  have hCtw : (1 : ℝ) ≤ C ^ totalWeight K := one_le_pow₀ hC
  have hyD : (1 : ℝ) ≤ mulHeight y ^ D := one_le_pow₀ (one_le_mulHeight y)
  have hz1 : (1 : ℝ) ≤ mulHeight z := one_le_mulHeight z
  rcases eq_or_ne x 0 with rfl | hx
  · rw [mulHeight_zero]
    calc (1 : ℝ) = 1 * (1 * 1) := by ring
      _ ≤ C ^ totalWeight K * (mulHeight z * mulHeight y ^ D) := by gcongr
  rw [mulHeight_eq hx, mulHeight_eq hy, mulHeight_eq hz, mul_pow]
  set az : Multiset ℝ := archAbsVal.map fun v : AbsoluteValue K ℝ ↦ ⨆ t, v (z t) with hazdef
  set ay : Multiset ℝ := archAbsVal.map fun v : AbsoluteValue K ℝ ↦ ⨆ r, v (y r) with haydef
  have hnnz : (0 : ℝ) ≤ az.prod := by
    refine Multiset.prod_nonneg fun a ha ↦ ?_
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp ha
    exact Real.iSup_nonneg fun _ ↦ v.nonneg _
  have hnny : (0 : ℝ) ≤ ay.prod := by
    refine Multiset.prod_nonneg fun a ha ↦ ?_
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp ha
    exact Real.iSup_nonneg fun _ ↦ v.nonneg _
  have harch' : (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod
      ≤ C ^ totalWeight K * (az.prod * ay.prod ^ D) := by
    calc (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod
        ≤ (archAbsVal.map fun v : AbsoluteValue K ℝ ↦
            C * ((⨆ t, v (z t)) * (⨆ r, v (y r)) ^ D)).prod :=
          Multiset.prod_map_le_prod_map₀ _ _
            (fun v _ ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _) harch
      _ = (archAbsVal.map fun _ : AbsoluteValue K ℝ ↦ C).prod
            * (archAbsVal.map fun v : AbsoluteValue K ℝ ↦
                (⨆ t, v (z t)) * (⨆ r, v (y r)) ^ D).prod := Multiset.prod_map_mul
      _ = C ^ totalWeight K * (az.prod * (archAbsVal.map fun v : AbsoluteValue K ℝ ↦
                (⨆ r, v (y r)) ^ D).prod) := by
          rw [Multiset.map_const', Multiset.prod_replicate, Multiset.prod_map_mul, hazdef]
          rfl
      _ = C ^ totalWeight K * (az.prod * ay.prod ^ D) := by
          rw [haydef, ← Multiset.prod_map_pow]
  have hnon' : ∏ᶠ v : nonarchAbsVal (K := K), ⨆ i, v.val (x i)
      ≤ (∏ᶠ v : nonarchAbsVal (K := K), ⨆ t, v.val (z t))
        * (∏ᶠ v : nonarchAbsVal (K := K), ⨆ r, v.val (y r)) ^ D := by
    have hfy : Function.HasFiniteMulSupport
        (fun v : nonarchAbsVal (K := K) ↦ ⨆ r, v.val (y r)) := hasFiniteMulSupport_iSup hy
    have hfz : Function.HasFiniteMulSupport
        (fun v : nonarchAbsVal (K := K) ↦ ⨆ t, v.val (z t)) := hasFiniteMulSupport_iSup hz
    have hfx : Function.HasFiniteMulSupport
        (fun v : nonarchAbsVal (K := K) ↦ ⨆ i, v.val (x i)) := hasFiniteMulSupport_iSup hx
    have hfyD : Function.HasFiniteMulSupport
        (fun v : nonarchAbsVal (K := K) ↦ (⨆ r, v.val (y r)) ^ D) :=
      Set.Finite.subset hfy fun v hv ↦ by
        simp only [Function.mem_mulSupport] at hv ⊢
        exact fun hc ↦ hv (by rw [hc, one_pow])
    have hfzy : Function.HasFiniteMulSupport
        (fun v : nonarchAbsVal (K := K) ↦ (⨆ t, v.val (z t)) * (⨆ r, v.val (y r)) ^ D) :=
      Set.Finite.subset (Set.Finite.union hfz hfyD) (Function.mulSupport_mul _ _)
    rw [finprod_pow hfy D, ← finprod_mul_distrib hfz hfyD]
    exact finprod_le_finprod₀ hfx (fun v ↦ Real.iSup_nonneg fun _ ↦ v.val.nonneg _)
      hfzy fun v ↦ hnon v.val v.prop
  have hnn1 : (0 : ℝ) ≤ ∏ᶠ v : nonarchAbsVal (K := K), ⨆ i, v.val (x i) :=
    finprod_nonneg fun v ↦ Real.iSup_nonneg fun _ ↦ v.val.nonneg _
  have hnnfz : (0 : ℝ) ≤ ∏ᶠ v : nonarchAbsVal (K := K), ⨆ t, v.val (z t) :=
    finprod_nonneg fun v ↦ Real.iSup_nonneg fun _ ↦ v.val.nonneg _
  have hnnfy : (0 : ℝ) ≤ ∏ᶠ v : nonarchAbsVal (K := K), ⨆ r, v.val (y r) :=
    finprod_nonneg fun v ↦ Real.iSup_nonneg fun _ ↦ v.val.nonneg _
  calc (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod
        * ∏ᶠ v : nonarchAbsVal (K := K), ⨆ i, v.val (x i)
      ≤ (C ^ totalWeight K * (az.prod * ay.prod ^ D))
          * ((∏ᶠ v : nonarchAbsVal (K := K), ⨆ t, v.val (z t))
            * (∏ᶠ v : nonarchAbsVal (K := K), ⨆ r, v.val (y r)) ^ D) := by
        refine mul_le_mul harch' hnon' hnn1 ?_
        have : (0 : ℝ) ≤ C ^ totalWeight K := by positivity
        positivity
    _ = C ^ totalWeight K * ((az.prod * ∏ᶠ v : nonarchAbsVal (K := K), ⨆ t, v.val (z t))
          * (ay.prod ^ D * (∏ᶠ v : nonarchAbsVal (K := K), ⨆ r, v.val (y r)) ^ D)) := by ring

/-- **Transport from local factors to the height, with a power.** -/
theorem mulHeight_le_pow_mul_pow {x : ι → K} {y : ρ → K} {C : ℝ} {D : ℕ}
    (hC : 1 ≤ C) (hy : y ≠ 0)
    (harch : ∀ v ∈ archAbsVal (K := K), (⨆ i, v (x i)) ≤ C * (⨆ r, v (y r)) ^ D)
    (hnon : ∀ v ∈ nonarchAbsVal (K := K), (⨆ i, v (x i)) ≤ (⨆ r, v (y r)) ^ D) :
    mulHeight x ≤ C ^ totalWeight K * mulHeight y ^ D := by
  have hone : ∀ v : AbsoluteValue K ℝ, (⨆ _ : Unit, v ((1 : Unit → K) ())) = 1 := by
    intro v
    rw [ciSup_unique]
    simp
  have hz : (1 : Unit → K) ≠ 0 := by
    intro hc
    exact one_ne_zero (congrFun hc ())
  have := mulHeight_le_pow_mul_mul_pow (x := x) (z := (1 : Unit → K)) (y := y) hC hz hy
    (fun v hv ↦ by rw [hone v, one_mul]; exact harch v hv)
    (fun v hv ↦ by rw [hone v, one_mul]; exact hnon v hv)
  rwa [mulHeight_one, one_mul] at this

end Height

namespace MvPolynomial

variable {K : Type*} [Field K] {κ ι : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- A substituted variable has at most `#ι` monomials. -/
theorem card_support_blockSubst_X_le (A : Matrix ι ι K) (h : κ) (j : ι) :
    #(blockSubst A (X ((h, j) : κ × ι))).support ≤ Fintype.card ι := by
  classical
  have hsub : (blockSubst A (X ((h, j) : κ × ι))).support
      ⊆ Finset.univ.image fun l : ι ↦ Finsupp.single ((h, l) : κ × ι) 1 := by
    rw [blockSubst_X]
    refine (MvPolynomial.support_sum).trans (Finset.biUnion_subset.mpr fun l _ ↦ ?_)
    rw [C_mul_X_eq_monomial]
    refine (MvPolynomial.support_monomial_subset).trans ?_
    simp only [Finset.singleton_subset_iff, Finset.mem_image]
    exact ⟨l, Finset.mem_univ l, rfl⟩
  exact (Finset.card_le_card hsub).trans
    (Finset.card_image_le.trans (le_of_eq Finset.card_univ))

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem coeff_blockSubst_X_apply (A : Matrix ι ι K) (h : κ) (j : ι) (m : κ × ι →₀ ℕ) :
    (blockSubst A (X ((h, j) : κ × ι))).coeff m
      = ∑ l, A j l * ((X ((h, l) : κ × ι) : MvPolynomial (κ × ι) K)).coeff m := by
  rw [blockSubst_X, MvPolynomial.coeff_sum]
  exact Finset.sum_congr rfl fun l _ ↦ by rw [coeff_C_mul]

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- **The local factor of a substituted variable** is at most the largest local factor of the
matrix, or `1`. -/
theorem iSup_coeff_blockSubst_X_le (v : AbsoluteValue K ℝ) (A : Matrix ι ι K) (h : κ) (j : ι) :
    (⨆ m : κ × ι →₀ ℕ, v ((blockSubst A (X ((h, j) : κ × ι))).coeff m))
      ≤ (⨆ p : ι × ι, v (A p.1 p.2)) ⊔ 1 := by
  classical
  have hbd : ∀ p : ι × ι, v (A p.1 p.2) ≤ (⨆ p : ι × ι, v (A p.1 p.2)) ⊔ 1 := fun p ↦
    le_sup_of_le_left
      (le_ciSup (f := fun q : ι × ι ↦ v (A q.1 q.2)) (Finite.bddAbove_range _) p)
  refine Real.iSup_le (fun m ↦ ?_) (le_sup_of_le_right zero_le_one)
  rw [coeff_blockSubst_X_apply]
  by_cases hm : ∃ l : ι, m = Finsupp.single ((h, l) : κ × ι) 1
  · obtain ⟨l₀, rfl⟩ := hm
    rw [Finset.sum_eq_single l₀]
    · simp only [coeff_X, ↓reduceIte, mul_one]
      exact hbd (j, l₀)
    · intro l _ hl
      have hne : Finsupp.single ((h, l) : κ × ι) 1 ≠ Finsupp.single ((h, l₀) : κ × ι) 1 := by
        intro hc
        exact hl (Prod.ext_iff.mp
          (Finsupp.single_left_injective (b := (1 : ℕ)) one_ne_zero hc)).2
      rw [coeff_X, ite_eq_right hne, mul_zero]
    · intro hl; exact absurd (Finset.mem_univ l₀) hl
  · rw [Finset.sum_eq_zero, map_zero]
    · exact le_sup_of_le_right zero_le_one
    · intro l _
      have hne : Finsupp.single ((h, l) : κ × ι) 1 ≠ m := fun hc ↦ hm ⟨l, hc.symm⟩
      rw [coeff_X, ite_eq_right hne, mul_zero]

omit [DecidableEq ι] [DecidableEq κ] in
/-- **The local factor of a monomial in the substituted variables**, with a multiplicativity
constant `c` supplied by the caller: `#ι` at an archimedean absolute value, `1` at a
nonarchimedean one. -/
theorem iSup_coeff_blockSubst_monomial_le_of (v : AbsoluteValue K ℝ) (A : Matrix ι ι K)
    {c : ℝ} (hc : 1 ≤ c)
    (hmul : ∀ (p : MvPolynomial (κ × ι) K) (t : κ × ι),
      (⨆ m : κ × ι →₀ ℕ, v ((p * blockSubst A (X t)).coeff m))
        ≤ c * ((⨆ m : κ × ι →₀ ℕ, v (p.coeff m))
            * ⨆ m : κ × ι →₀ ℕ, v ((blockSubst A (X t)).coeff m))) :
    ∀ (N : ℕ) (ν : κ × ι →₀ ℕ), ∑ t, ν t = N →
      (⨆ J : κ × ι →₀ ℕ, v ((blockSubst A (monomial ν (1 : K))).coeff J))
        ≤ (c * ((⨆ p : ι × ι, v (A p.1 p.2)) ⊔ 1)) ^ N := by
  have hB : (1 : ℝ) ≤ (⨆ p : ι × ι, v (A p.1 p.2)) ⊔ 1 := le_sup_right
  intro N
  induction N with
  | zero =>
      intro ν hν
      have hν0 : ν = 0 := by
        ext t
        have := Finset.sum_eq_zero_iff.mp hν t (Finset.mem_univ t)
        simpa using this
      subst hν0
      rw [show (monomial (0 : κ × ι →₀ ℕ) (1 : K)) = 1 by simp, map_one, iSup_coeff_one, pow_zero]
  | succ N ih =>
      intro ν hν
      have hν0 : ν ≠ 0 := by
        rintro rfl
        simp at hν
      obtain ⟨t, ht⟩ := Finsupp.support_nonempty_iff.mpr hν0
      obtain ⟨h₀, j₀⟩ := t
      set ν' : κ × ι →₀ ℕ := ν - Finsupp.single ((h₀, j₀) : κ × ι) 1 with hν'def
      have hνs : 1 ≤ ν (h₀, j₀) := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp ht)
      have hνeq : ν' + Finsupp.single ((h₀, j₀) : κ × ι) 1 = ν := by
        ext u
        rcases eq_or_ne u ((h₀, j₀) : κ × ι) with rfl | hu
        · simp only [hν'def, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
          omega
        · simp [hν'def, Ne.symm hu]
      have hsingle : ∑ u : κ × ι, (Finsupp.single ((h₀, j₀) : κ × ι) 1) u = 1 := by
        rw [Finset.sum_eq_single ((h₀, j₀) : κ × ι)]
        · simp
        · intro u _ hu
          simp [Ne.symm hu]
        · intro hu; exact absurd (Finset.mem_univ ((h₀, j₀) : κ × ι)) hu
      have hν'sum : ∑ u, ν' u = N := by
        have := congrArg (fun f : κ × ι →₀ ℕ ↦ ∑ u, f u) hνeq
        simp only [Finsupp.add_apply, Finset.sum_add_distrib, hsingle] at this
        omega
      have hfac : blockSubst A (monomial ν (1 : K))
          = blockSubst A (monomial ν' (1 : K)) * blockSubst A (X ((h₀, j₀) : κ × ι)) := by
        rw [← map_mul, ← hνeq, monomial_add_single, pow_one]
      have hX := iSup_coeff_blockSubst_X_le v A h₀ j₀
      have hnnX : (0 : ℝ) ≤ ⨆ m : κ × ι →₀ ℕ, v ((blockSubst A (X ((h₀, j₀) : κ × ι))).coeff m) :=
        Real.iSup_nonneg fun _ ↦ v.nonneg _
      calc (⨆ J : κ × ι →₀ ℕ, v ((blockSubst A (monomial ν (1 : K))).coeff J))
          ≤ c * ((⨆ m : κ × ι →₀ ℕ, v ((blockSubst A (monomial ν' (1 : K))).coeff m))
              * ⨆ m : κ × ι →₀ ℕ, v ((blockSubst A (X ((h₀, j₀) : κ × ι))).coeff m)) := by
            rw [hfac]; exact hmul _ _
        _ ≤ c * ((c * ((⨆ p : ι × ι, v (A p.1 p.2)) ⊔ 1)) ^ N
              * ((⨆ p : ι × ι, v (A p.1 p.2)) ⊔ 1)) := by
            gcongr
            exact ih ν' hν'sum
        _ = (c * ((⨆ p : ι × ι, v (A p.1 p.2)) ⊔ 1)) ^ (N + 1) := by ring

/-! ### The local factor of a substituted polynomial -/

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem blockSubst_eq_sum (M : Matrix ι ι K) (R : MvPolynomial (κ × ι) K) :
    blockSubst M R
      = ∑ ν ∈ R.support, C (R.coeff ν) * blockSubst M (monomial ν (1 : K)) := by
  conv_lhs => rw [R.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun ν _ ↦ ?_
  have h1 : blockSubst M (monomial ν (R.coeff ν))
      = blockSubst M (C (R.coeff ν) * monomial ν (1 : K)) := by
    rw [C_mul_monomial, mul_one]
  rw [h1, map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem iSup_coeff_C_mul_le (v : AbsoluteValue K ℝ) (a : K) (Q : MvPolynomial (κ × ι) K) :
    (⨆ m : κ × ι →₀ ℕ, v ((C a * Q).coeff m)) ≤ v a * ⨆ m : κ × ι →₀ ℕ, v (Q.coeff m) := by
  refine Real.iSup_le (fun m ↦ ?_)
    (mul_nonneg (v.nonneg a) (Real.iSup_nonneg fun _ ↦ v.nonneg _))
  rw [coeff_C_mul, map_mul]
  exact mul_le_mul_of_nonneg_left
    (le_ciSup (Finsupp.bddAbove_range_apply Q.coeff v) m) (v.nonneg a)

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- Multiplying by a substituted variable multiplies the local factor by at most `#ι`. -/
theorem iSup_coeff_mul_blockSubst_X_le (v : AbsoluteValue K ℝ) (A : Matrix ι ι K)
    (p : MvPolynomial (κ × ι) K) (t : κ × ι) :
    (⨆ m : κ × ι →₀ ℕ, v ((p * blockSubst A (X t)).coeff m))
      ≤ (Fintype.card ι : ℝ) * ((⨆ m : κ × ι →₀ ℕ, v (p.coeff m))
          * ⨆ m : κ × ι →₀ ℕ, v ((blockSubst A (X t)).coeff m)) := by
  obtain ⟨h, j⟩ := t
  refine (iSup_coeff_mul_le_card_support v p _).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _)
    (Real.iSup_nonneg fun _ ↦ v.nonneg _))
  exact_mod_cast (min_le_right _ _).trans (card_support_blockSubst_X_le A h j)

omit [DecidableEq ι] [DecidableEq κ] in
/-- **The local factor of a substituted monomial of degree `D`**, archimedean form. -/
theorem iSup_coeff_blockSubst_monomial_le [Nonempty ι] (v : AbsoluteValue K ℝ)
    (A : Matrix ι ι K) {ν : κ × ι →₀ ℕ} {D : ℕ} (hν : ∑ t, ν t = D) :
    (⨆ J : κ × ι →₀ ℕ, v ((blockSubst A (monomial ν (1 : K))).coeff J))
      ≤ ((Fintype.card ι : ℝ) * ((⨆ p : ι × ι, v (A p.1 p.2)) ⊔ 1)) ^ D := by
  have hcard : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  exact iSup_coeff_blockSubst_monomial_le_of v A hcard
    (iSup_coeff_mul_blockSubst_X_le (κ := κ) v A) D ν hν

omit [DecidableEq ι] [DecidableEq κ] in
/-- **The local factor of a substituted monomial of degree `D`**, nonarchimedean form: the
number of variables drops out. -/
theorem iSup_coeff_blockSubst_monomial_le_of_isNonarchimedean {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) (A : Matrix ι ι K) {ν : κ × ι →₀ ℕ} {D : ℕ} (hν : ∑ t, ν t = D) :
    (⨆ J : κ × ι →₀ ℕ, v ((blockSubst A (monomial ν (1 : K))).coeff J))
      ≤ ((⨆ p : ι × ι, v (A p.1 p.2)) ⊔ 1) ^ D := by
  have h := iSup_coeff_blockSubst_monomial_le_of v A le_rfl
    (fun p t ↦ by rw [one_mul, MvPolynomial.iSup_coeff_mul hv]) D ν hν
  rwa [one_mul] at h

omit [DecidableEq ι] [DecidableEq κ] in
/-- **The local factor of a substituted polynomial**, archimedean form: the number of monomials,
the number of variables in a block raised to the degree, and the largest entry of the matrix. -/
theorem iSup_coeff_blockSubst_le [Nonempty ι] (v : AbsoluteValue K ℝ) (M : Matrix ι ι K)
    {R : MvPolynomial (κ × ι) K} {D : ℕ} (hR : ∀ ν ∈ R.support, ∑ t, ν t ≤ D) :
    (⨆ m : κ × ι →₀ ℕ, v ((blockSubst M R).coeff m))
      ≤ (#R.support : ℝ) * ((⨆ m : κ × ι →₀ ℕ, v (R.coeff m))
        * ((Fintype.card ι : ℝ) * ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1)) ^ D) := by
  have hcard : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hB1 : (1 : ℝ) ≤ (⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1 := le_sup_right
  have hB : (1 : ℝ) ≤ (Fintype.card ι : ℝ) * ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1) := by
    nlinarith
  have hmul := iSup_coeff_mul_blockSubst_X_le (κ := κ) v M
  have hmono : ∀ ν ∈ R.support,
      (⨆ m : κ × ι →₀ ℕ, v ((C (R.coeff ν) * blockSubst M (monomial ν (1 : K))).coeff m))
        ≤ (⨆ m : κ × ι →₀ ℕ, v (R.coeff m))
          * ((Fintype.card ι : ℝ) * ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1)) ^ D := by
    intro ν hν
    refine (iSup_coeff_C_mul_le v _ _).trans ?_
    refine mul_le_mul (le_ciSup (Finsupp.bddAbove_range_apply R.coeff v) ν) ?_
      (Real.iSup_nonneg fun _ ↦ v.nonneg _) (Real.iSup_nonneg fun _ ↦ v.nonneg _)
    exact (iSup_coeff_blockSubst_monomial_le_of v M hcard hmul (∑ t, ν t) ν rfl).trans
      (pow_le_pow_right₀ hB (hR ν hν))
  rw [blockSubst_eq_sum]
  exact iSup_coeff_sum_le R.support _
    (mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _) (pow_nonneg (by linarith) D)) hmono

omit [DecidableEq ι] [DecidableEq κ] in
/-- **The local factor of a substituted polynomial**, nonarchimedean form: neither the number of
monomials nor the number of variables appears. -/
theorem iSup_coeff_blockSubst_le_of_isNonarchimedean {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) (M : Matrix ι ι K)
    {R : MvPolynomial (κ × ι) K} {D : ℕ} (hR : ∀ ν ∈ R.support, ∑ t, ν t ≤ D) :
    (⨆ m : κ × ι →₀ ℕ, v ((blockSubst M R).coeff m))
      ≤ (⨆ m : κ × ι →₀ ℕ, v (R.coeff m)) * ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1) ^ D := by
  have hB1 : (1 : ℝ) ≤ (⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1 := le_sup_right
  have hmul : ∀ (p : MvPolynomial (κ × ι) K) (t : κ × ι),
      (⨆ m : κ × ι →₀ ℕ, v ((p * blockSubst M (X t)).coeff m))
        ≤ 1 * ((⨆ m : κ × ι →₀ ℕ, v (p.coeff m))
            * ⨆ m : κ × ι →₀ ℕ, v ((blockSubst M (X t)).coeff m)) := by
    intro p t
    rw [one_mul, MvPolynomial.iSup_coeff_mul hv]
  have hmono : ∀ ν ∈ R.support,
      (⨆ m : κ × ι →₀ ℕ, v ((C (R.coeff ν) * blockSubst M (monomial ν (1 : K))).coeff m))
        ≤ (⨆ m : κ × ι →₀ ℕ, v (R.coeff m)) * ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1) ^ D := by
    intro ν hν
    refine (iSup_coeff_C_mul_le v _ _).trans ?_
    refine mul_le_mul (le_ciSup (Finsupp.bddAbove_range_apply R.coeff v) ν) ?_
      (Real.iSup_nonneg fun _ ↦ v.nonneg _) (Real.iSup_nonneg fun _ ↦ v.nonneg _)
    have hmon := iSup_coeff_blockSubst_monomial_le_of v M le_rfl hmul (∑ t, ν t) ν rfl
    rw [one_mul] at hmon
    exact hmon.trans (pow_le_pow_right₀ hB1 (hR ν hν))
  rw [blockSubst_eq_sum]
  exact iSup_coeff_sum_le_of_isNonarchimedean hv R.support _
    (mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _) (pow_nonneg (by linarith) D)) hmono

/-! ### From local factors to the height of a polynomial -/

section Heights

variable [AdmissibleAbsValues K] {ρ : Type*} [Finite ρ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- **The height of a polynomial from a comparison of local factors.** -/
theorem mulHeight_le_pow_mul_mul_pow {σ : Type*} {P Q : MvPolynomial σ K} {y : ρ → K}
    {C : ℝ} {D : ℕ} (hC : 1 ≤ C) (hQ : Q ≠ 0) (hy : y ≠ 0)
    (harch : ∀ w ∈ archAbsVal (K := K), (⨆ m : σ →₀ ℕ, w (P.coeff m))
      ≤ C * ((⨆ m : σ →₀ ℕ, w (Q.coeff m)) * (⨆ r, w (y r)) ^ D))
    (hnon : ∀ w ∈ nonarchAbsVal (K := K), (⨆ m : σ →₀ ℕ, w (P.coeff m))
      ≤ (⨆ m : σ →₀ ℕ, w (Q.coeff m)) * (⨆ r, w (y r)) ^ D) :
    P.mulHeight ≤ C ^ Height.totalWeight K * (Q.mulHeight * Height.mulHeight y ^ D) := by
  have hPeq : P.mulHeight
      = Height.mulHeight fun i : P.support ↦ P.coeff (i : σ →₀ ℕ) :=
    Finsupp.mulHeight_eq_mulHeight_subtype P.coeff (le_of_eq rfl)
  have hQeq : Q.mulHeight
      = Height.mulHeight fun i : Q.support ↦ Q.coeff (i : σ →₀ ℕ) :=
    Finsupp.mulHeight_eq_mulHeight_subtype Q.coeff (le_of_eq rfl)
  have hQ0 : (fun i : Q.support ↦ Q.coeff (i : σ →₀ ℕ)) ≠ 0 := by
    obtain ⟨m, hm⟩ := Finsupp.support_nonempty_iff.mpr
      (show Q.coeff ≠ 0 from fun hc ↦ hQ (MvPolynomial.ext _ _ fun m ↦ by
        rw [show Q.coeff m = (Q.coeff : (σ →₀ ℕ) →₀ K) m from rfl, hc]; simp))
    exact Function.ne_iff.mpr ⟨⟨m, hm⟩, Finsupp.mem_support_iff.mp hm⟩
  have hPs : ∀ w : AbsoluteValue K ℝ, (⨆ m : σ →₀ ℕ, w (P.coeff m))
      = ⨆ i : P.support, w (P.coeff (i : σ →₀ ℕ)) :=
    fun w ↦ Finsupp.iSup_apply_eq_iSup_support P.coeff w
  have hQs : ∀ w : AbsoluteValue K ℝ, (⨆ m : σ →₀ ℕ, w (Q.coeff m))
      = ⨆ i : Q.support, w (Q.coeff (i : σ →₀ ℕ)) :=
    fun w ↦ Finsupp.iSup_apply_eq_iSup_support Q.coeff w
  rw [hPeq, hQeq]
  refine Height.mulHeight_le_pow_mul_mul_pow hC hQ0 hy (fun w hw ↦ ?_) fun w hw ↦ ?_
  · rw [← hPs w, ← hQs w]
    exact harch w hw
  · rw [← hPs w, ← hQs w]
    exact hnon w hw

omit [DecidableEq ι] [DecidableEq κ] in
/-- **The height of a substituted polynomial.** The tuple `y` is a reference tuple dominating
the entries of `M` and `1` at every absolute value; in the application it collects the entries
of a whole family of matrices, so that a single height carries the family. -/
theorem mulHeight_blockSubst_le [Nonempty ι] (M : Matrix ι ι K) {y : ρ → K} (hy : y ≠ 0)
    (hMy : ∀ w : AbsoluteValue K ℝ, (⨆ p : ι × ι, w (M p.1 p.2)) ⊔ 1 ≤ ⨆ r, w (y r))
    {R : MvPolynomial (κ × ι) K} {D : ℕ} (hR0 : R ≠ 0)
    (hR : ∀ ν ∈ R.support, ∑ t, ν t ≤ D) :
    (blockSubst M R).mulHeight
      ≤ ((#R.support : ℝ) * (Fintype.card ι : ℝ) ^ D) ^ Height.totalWeight K
        * (R.mulHeight * Height.mulHeight y ^ D) := by
  have hc1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcD : (1 : ℝ) ≤ (Fintype.card ι : ℝ) ^ D := one_le_pow₀ hc1
  have hs1 : (1 : ℝ) ≤ (#R.support : ℝ) := by
    have h : 0 < #R.support := Finset.card_pos.mpr
      (Finset.nonempty_iff_ne_empty.mpr fun hc ↦ hR0 (MvPolynomial.support_eq_empty.mp hc))
    exact_mod_cast h
  refine mulHeight_le_pow_mul_mul_pow (by nlinarith) hR0 hy (fun w _ ↦ ?_) fun w hw ↦ ?_
  · have hB1 : (1 : ℝ) ≤ (⨆ p : ι × ι, w (M p.1 p.2)) ⊔ 1 := le_sup_right
    have hQ0 : (0 : ℝ) ≤ ⨆ m : κ × ι →₀ ℕ, w (R.coeff m) := Real.iSup_nonneg fun _ ↦ w.nonneg _
    have hpow : ((Fintype.card ι : ℝ) * ((⨆ p : ι × ι, w (M p.1 p.2)) ⊔ 1)) ^ D
        ≤ (Fintype.card ι : ℝ) ^ D * (⨆ r, w (y r)) ^ D := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (hMy w) D) (by positivity)
    calc (⨆ m : κ × ι →₀ ℕ, w ((blockSubst M R).coeff m))
        ≤ (#R.support : ℝ) * ((⨆ m : κ × ι →₀ ℕ, w (R.coeff m))
            * ((Fintype.card ι : ℝ) * ((⨆ p : ι × ι, w (M p.1 p.2)) ⊔ 1)) ^ D) :=
          iSup_coeff_blockSubst_le w M hR
      _ ≤ (#R.support : ℝ) * ((⨆ m : κ × ι →₀ ℕ, w (R.coeff m))
            * ((Fintype.card ι : ℝ) ^ D * (⨆ r, w (y r)) ^ D)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hQ0) (by linarith)
      _ = (#R.support : ℝ) * (Fintype.card ι : ℝ) ^ D
            * ((⨆ m : κ × ι →₀ ℕ, w (R.coeff m)) * (⨆ r, w (y r)) ^ D) := by ring
  · have hB1 : (1 : ℝ) ≤ (⨆ p : ι × ι, w (M p.1 p.2)) ⊔ 1 := le_sup_right
    have hQ0 : (0 : ℝ) ≤ ⨆ m : κ × ι →₀ ℕ, w (R.coeff m) := Real.iSup_nonneg fun _ ↦ w.nonneg _
    refine (iSup_coeff_blockSubst_le_of_isNonarchimedean (isNonarchimedean w hw) M hR).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (hMy w) D) hQ0

omit [DecidableEq ι] [DecidableEq κ] in
/-- **The height of a substituted Hasse derivative**, which is where Layer 5.2's constant `C₃`
comes from: differentiating costs a factor `2 ^ D` at the archimedean absolute values and
nothing at the nonarchimedean ones. -/
theorem mulHeight_blockSubst_hasseDeriv_le [Nonempty ι] (M : Matrix ι ι K) (I : κ × ι →₀ ℕ)
    {y : ρ → K} (hy : y ≠ 0)
    (hMy : ∀ w : AbsoluteValue K ℝ, (⨆ p : ι × ι, w (M p.1 p.2)) ⊔ 1 ≤ ⨆ r, w (y r))
    {P : MvPolynomial (κ × ι) K} {D : ℕ} (hP0 : P ≠ 0)
    (hP : ∀ ν ∈ P.support, ∑ t, ν t ≤ D) :
    (blockSubst M (hasseDeriv I P)).mulHeight
      ≤ ((#P.support : ℝ) * 2 ^ D * (Fintype.card ι : ℝ) ^ D) ^ Height.totalWeight K
        * (P.mulHeight * Height.mulHeight y ^ D) := by
  have hmaps : ∀ ν ∈ (hasseDeriv I P).support, ν + I ∈ P.support := by
    intro ν hν
    rw [MvPolynomial.mem_support_iff] at hν ⊢
    intro hc
    rw [hasseDeriv_coeff, hc, mul_zero] at hν
    exact hν rfl
  have hsupp : #(hasseDeriv I P).support ≤ #P.support :=
    Finset.card_le_card_of_injOn (· + I)
      (fun ν hν ↦ Finset.mem_coe.mpr (hmaps ν (Finset.mem_coe.mp hν)))
      fun a _ b _ h ↦ add_right_cancel h
  have hdeg : ∀ ν ∈ (hasseDeriv I P).support, ∑ t, ν t ≤ D := by
    intro ν hν
    have h := hP _ (hmaps ν hν)
    have hle : ∑ t, ν t ≤ ∑ t, (ν + I) t :=
      Finset.sum_le_sum fun t _ ↦ by simp
    omega
  have htot : P.totalDegree ≤ D := by
    rw [MvPolynomial.totalDegree]
    refine Finset.sup_le fun m hm ↦ ?_
    rw [show (m.sum fun _ k ↦ k) = ∑ t, m t from Finsupp.sum_fintype _ _ fun _ ↦ rfl]
    exact hP m hm
  have hc1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcD : (1 : ℝ) ≤ (Fintype.card ι : ℝ) ^ D := one_le_pow₀ hc1
  have h2D : (1 : ℝ) ≤ (2 : ℝ) ^ D := one_le_pow₀ one_le_two
  have hs1 : (1 : ℝ) ≤ (#P.support : ℝ) := by
    have h : 0 < #P.support := Finset.card_pos.mpr
      (Finset.nonempty_iff_ne_empty.mpr fun hc ↦ hP0 (MvPolynomial.support_eq_empty.mp hc))
    exact_mod_cast h
  have hsuppR : (#(hasseDeriv I P).support : ℝ) ≤ (#P.support : ℝ) := by exact_mod_cast hsupp
  have hA : (1 : ℝ) ≤ (#P.support : ℝ) * 2 ^ D := by nlinarith
  have hC : (1 : ℝ) ≤ (#P.support : ℝ) * 2 ^ D * (Fintype.card ι : ℝ) ^ D := by nlinarith
  refine mulHeight_le_pow_mul_mul_pow hC hP0 hy (fun w _ ↦ ?_) fun w hw ↦ ?_
  · have hB1 : (1 : ℝ) ≤ (⨆ p : ι × ι, w (M p.1 p.2)) ⊔ 1 := le_sup_right
    have hPn : (0 : ℝ) ≤ ⨆ m : κ × ι →₀ ℕ, w (P.coeff m) := Real.iSup_nonneg fun _ ↦ w.nonneg _
    have hQ : (⨆ m : κ × ι →₀ ℕ, w ((hasseDeriv I P).coeff m))
        ≤ (2 : ℝ) ^ D * ⨆ m : κ × ι →₀ ℕ, w (P.coeff m) :=
      (iSup_coeff_hasseDeriv_le w I P).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two htot) hPn)
    have hpow : ((Fintype.card ι : ℝ) * ((⨆ p : ι × ι, w (M p.1 p.2)) ⊔ 1)) ^ D
        ≤ (Fintype.card ι : ℝ) ^ D * (⨆ r, w (y r)) ^ D := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (hMy w) D) (by positivity)
    calc (⨆ m : κ × ι →₀ ℕ, w ((blockSubst M (hasseDeriv I P)).coeff m))
        ≤ (#(hasseDeriv I P).support : ℝ)
            * ((⨆ m : κ × ι →₀ ℕ, w ((hasseDeriv I P).coeff m))
              * ((Fintype.card ι : ℝ) * ((⨆ p : ι × ι, w (M p.1 p.2)) ⊔ 1)) ^ D) :=
          iSup_coeff_blockSubst_le w M hdeg
      _ ≤ (#P.support : ℝ) * (((2 : ℝ) ^ D * ⨆ m : κ × ι →₀ ℕ, w (P.coeff m))
            * ((Fintype.card ι : ℝ) ^ D * (⨆ r, w (y r)) ^ D)) :=
          mul_le_mul hsuppR (mul_le_mul hQ hpow
              (pow_nonneg (mul_nonneg (by linarith) (by linarith)) D)
              (mul_nonneg (by positivity) hPn))
            (mul_nonneg (Real.iSup_nonneg fun _ ↦ w.nonneg _)
              (pow_nonneg (mul_nonneg (by linarith) (by linarith)) D)) (by linarith)
      _ = (#P.support : ℝ) * 2 ^ D * (Fintype.card ι : ℝ) ^ D
            * ((⨆ m : κ × ι →₀ ℕ, w (P.coeff m)) * (⨆ r, w (y r)) ^ D) := by ring
  · have hB1 : (1 : ℝ) ≤ (⨆ p : ι × ι, w (M p.1 p.2)) ⊔ 1 := le_sup_right
    have hPn : (0 : ℝ) ≤ ⨆ m : κ × ι →₀ ℕ, w (P.coeff m) := Real.iSup_nonneg fun _ ↦ w.nonneg _
    have hnv := isNonarchimedean w hw
    refine (iSup_coeff_blockSubst_le_of_isNonarchimedean hnv M hdeg).trans ?_
    exact mul_le_mul (iSup_coeff_hasseDeriv_le_of_isNonarchimedean hnv I P)
      (pow_le_pow_left₀ (by linarith) (hMy w) D) (pow_nonneg (by linarith) D) hPn

omit [DecidableEq ι] [DecidableEq κ] in
/-- **The logarithmic form of `MvPolynomial.mulHeight_blockSubst_hasseDeriv_le`**, which is the
shape Layer 5.2's constant `C₃` is read off from. -/
theorem logHeight_blockSubst_hasseDeriv_le [Nonempty ι] (M : Matrix ι ι K) (I : κ × ι →₀ ℕ)
    {y : ρ → K} (hy : y ≠ 0)
    (hMy : ∀ w : AbsoluteValue K ℝ, (⨆ p : ι × ι, w (M p.1 p.2)) ⊔ 1 ≤ ⨆ r, w (y r))
    {P : MvPolynomial (κ × ι) K} {D : ℕ} (hP0 : P ≠ 0)
    (hP : ∀ ν ∈ P.support, ∑ t, ν t ≤ D) :
    (blockSubst M (hasseDeriv I P)).logHeight
      ≤ (Height.totalWeight K : ℝ) * (Real.log (#P.support)
          + (D : ℝ) * Real.log 2 + (D : ℝ) * Real.log (Fintype.card ι))
        + P.logHeight + (D : ℝ) * Real.log (Height.mulHeight y) := by
  have hsp0 : (0 : ℝ) < (#P.support : ℝ) := by
    have h : 0 < #P.support := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr
      fun hc ↦ hP0 (MvPolynomial.support_eq_empty.mp hc))
    exact_mod_cast h
  have hcι0 : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hHy0 : (0 : ℝ) < Height.mulHeight y :=
    lt_of_lt_of_le zero_lt_one (Height.one_le_mulHeight y)
  have hPh0 : (0 : ℝ) < P.mulHeight := MvPolynomial.mulHeight_pos P
  rw [MvPolynomial.logHeight_eq_log_mulHeight, MvPolynomial.logHeight_eq_log_mulHeight]
  refine le_trans (Real.log_le_log (MvPolynomial.mulHeight_pos _)
    (mulHeight_blockSubst_hasseDeriv_le M I hy hMy hP0 hP)) (le_of_eq ?_)
  rw [Real.log_mul (ne_of_gt (pow_pos (mul_pos (mul_pos hsp0 (by positivity))
        (pow_pos hcι0 D)) _)) (ne_of_gt (mul_pos hPh0 (pow_pos hHy0 D))),
    Real.log_pow,
    Real.log_mul (ne_of_gt (mul_pos hsp0 (by positivity))) (ne_of_gt (pow_pos hcι0 D)),
    Real.log_mul (ne_of_gt hsp0) (by positivity),
    Real.log_pow, Real.log_pow,
    Real.log_mul (ne_of_gt hPh0) (ne_of_gt (pow_pos hHy0 D)), Real.log_pow]
  ring

omit [DecidableEq ι] [DecidableEq κ] in
/-- **The height of the condition matrix of Layer 5.2.** Its entries are the coefficients of the
monomials of multidegree `d` after substitution, one row for each condition; the number of rows
and columns does not enter, because a coefficient of a substituted monomial is a sum of products
of at most `D` entries of the matrix. -/
theorem mulHeight_matrix_blockSubst_monomial_le [Nonempty ι] {α β : Type*} [Finite α] [Finite β]
    (Mat : α → Matrix ι ι K) (N : α → (κ × ι →₀ ℕ)) (c : β → (κ × ι →₀ ℕ)) {D : ℕ}
    (hc : ∀ b, ∑ t, c b t = D) {y : ρ → K} (hy : y ≠ 0)
    (hMy : ∀ (a : α) (w : AbsoluteValue K ℝ),
      (⨆ p : ι × ι, w (Mat a p.1 p.2)) ⊔ 1 ≤ ⨆ r, w (y r)) :
    Height.mulHeight (fun q : α × β ↦
        (blockSubst (Mat q.1) (monomial (c q.2) (1 : K))).coeff (N q.1))
      ≤ ((Fintype.card ι : ℝ) ^ D) ^ Height.totalWeight K * Height.mulHeight y ^ D := by
  have hc1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcD : (1 : ℝ) ≤ (Fintype.card ι : ℝ) ^ D := one_le_pow₀ hc1
  have hentry : ∀ (w : AbsoluteValue K ℝ) (q : α × β),
      w ((blockSubst (Mat q.1) (monomial (c q.2) (1 : K))).coeff (N q.1))
        ≤ ((Fintype.card ι : ℝ) * ((⨆ p : ι × ι, w (Mat q.1 p.1 p.2)) ⊔ 1)) ^ D := by
    intro w q
    exact (le_ciSup (Finsupp.bddAbove_range_apply
      (blockSubst (Mat q.1) (monomial (c q.2) (1 : K))).coeff w) (N q.1)).trans
        (iSup_coeff_blockSubst_monomial_le w (Mat q.1) (hc q.2))
  refine Height.mulHeight_le_pow_mul_pow hcD hy (fun w _ ↦ ?_) fun w hw ↦ ?_
  · refine Real.iSup_le (fun q ↦ (hentry w q).trans ?_)
      (mul_nonneg (by positivity) (pow_nonneg (Real.iSup_nonneg fun _ ↦ w.nonneg _) D))
    have hB1 : (1 : ℝ) ≤ (⨆ p : ι × ι, w (Mat q.1 p.1 p.2)) ⊔ 1 := le_sup_right
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (hMy q.1 w) D) (by positivity)
  · refine Real.iSup_le (fun q ↦ ?_) (pow_nonneg (Real.iSup_nonneg fun _ ↦ w.nonneg _) D)
    have hB1 : (1 : ℝ) ≤ (⨆ p : ι × ι, w (Mat q.1 p.1 p.2)) ⊔ 1 := le_sup_right
    refine le_trans ((le_ciSup (Finsupp.bddAbove_range_apply
      (blockSubst (Mat q.1) (monomial (c q.2) (1 : K))).coeff w) (N q.1)).trans
        (iSup_coeff_blockSubst_monomial_le_of_isNonarchimedean (isNonarchimedean w hw)
          (Mat q.1) (hc q.2))) ?_
    exact pow_le_pow_left₀ (by linarith) (hMy q.1 w) D

end Heights

/-! ### The coefficient vector on the monomials of a fixed multidegree -/

section Dictionary

variable [AdmissibleAbsValues K] {d : κ → ℕ}

/-- **The height of a multihomogeneous polynomial is the height of its coefficient vector** on
the monomials of multidegree `d`. This is the translation Layer 5.2 makes between the vector
Siegel's lemma produces and the polynomial the milestone is about. -/
theorem mulHeight_eq_mulHeight_coeff_multiMons {P : MvPolynomial (κ × ι) K}
    (hP : IsMultiHomogeneous d P) :
    P.mulHeight
      = Height.mulHeight fun ν : (multiMons (ι := ι) d) ↦ P.coeff (ν : κ × ι →₀ ℕ) :=
  Finsupp.mulHeight_eq_mulHeight_subtype P.coeff fun _ hν ↦
    mem_multiMons.mpr fun h ↦ hP (Finsupp.mem_support_iff.mp hν) h

omit [AdmissibleAbsValues K] in
/-- **A crude bound on the logarithm of the number of monomials of multidegree `d`.** It is
`O (log d)`, but all that Layer 5.2 needs is that it is a constant times `∑ h, d h`. -/
theorem log_card_multiMons_le (d : κ → ℕ) :
    Real.log (#(multiMons (ι := ι) d)) ≤ (Fintype.card ι : ℝ) * ∑ h, (d h : ℝ) := by
  have hprod : Real.log (∏ t : κ × ι, ((d t.1 : ℝ) + 1))
      ≤ (Fintype.card ι : ℝ) * ∑ h, (d h : ℝ) := by
    rw [Real.log_prod (fun t _ ↦ by positivity)]
    have hterm : ∀ t : κ × ι, Real.log ((d t.1 : ℝ) + 1) ≤ (d t.1 : ℝ) := fun t ↦ by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < (d t.1 : ℝ) + 1 by positivity)
      linarith
    refine (Finset.sum_le_sum fun t _ ↦ hterm t).trans ?_
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp [Finset.sum_const, Finset.card_univ]
  have hcast : ((∏ t : κ × ι, (d t.1 + 1) : ℕ) : ℝ) = ∏ t : κ × ι, ((d t.1 : ℝ) + 1) := by
    push_cast
    rfl
  rcases Nat.eq_zero_or_pos (#(multiMons (ι := ι) d)) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    refine le_trans ?_ hprod
    rw [← hcast]
    exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity))
  · refine le_trans (Real.log_le_log (by exact_mod_cast hpos) ?_) hprod
    rw [← hcast]
    exact_mod_cast card_multiMons_le d

end Dictionary

section Absolute

variable [NumberField K] {d : κ → ℕ}

/-- The absolute form of `MvPolynomial.mulHeight_eq_mulHeight_coeff_multiMons`. -/
theorem absMulHeight_coeff_multiMons {P : MvPolynomial (κ × ι) K}
    (hP : IsMultiHomogeneous d P) :
    NumberField.absMulHeight (fun ν : (multiMons (ι := ι) d) ↦ P.coeff (ν : κ × ι →₀ ℕ))
      = P.mulHeight ^ ((Module.finrank ℚ K : ℝ))⁻¹ := by
  rw [NumberField.absMulHeight_eq, mulHeight_eq_mulHeight_coeff_multiMons hP]

end Absolute

/-! ### Siegel's lemma for the multihomogeneous auxiliary polynomial -/

section Siegel

variable [NumberField K] {ρ : Type*} [Finite ρ] {d : κ → ℕ}

/-- **Siegel's lemma in the multihomogeneous setting.** Given finitely many conditions, each of
them the vanishing of one coefficient of the polynomial read in one system of coordinates, and
at most half as many conditions as monomials of multidegree `d`, there is a nonzero
multihomogeneous polynomial of multidegree `d` satisfying all of them, of logarithmic height a
constant times `∑ h, d h`. -/
theorem exists_ne_zero_isMultiHomogeneous_coeff_blockSubst_eq_zero [Nonempty ι]
    {Row : Type*} [Fintype Row] (Mat : Row → Matrix ι ι K) (Nrow : Row → (κ × ι →₀ ℕ))
    {y : ρ → K} (hy : y ≠ 0)
    (hMy : ∀ (r : Row) (w : AbsoluteValue K ℝ),
      (⨆ p : ι × ι, w (Mat r p.1 p.2)) ⊔ 1 ≤ ⨆ s, w (y s))
    (hrow : 2 * (Fintype.card Row : ℝ) ≤ #(multiMons (ι := ι) d)) :
    ∃ P : MvPolynomial (κ × ι) K, P ≠ 0 ∧ IsMultiHomogeneous d P ∧
      (∀ r : Row, (blockSubst (Mat r) P).coeff (Nrow r) = 0) ∧
      P.logHeight ≤ 2⁻¹ * Real.log |(NumberField.discr K : ℝ)|
        + ((Module.finrank ℚ K : ℝ) / 2 * Fintype.card ι
            + Height.totalWeight K * Real.log (Fintype.card ι)
            + Real.log (Height.mulHeight y)) * ∑ h, (d h : ℝ) := by
  classical
  let _ : LinearOrder (multiMons (ι := ι) d) := linearOrderOfSTO WellOrderingRel
  set D : ℕ := ∑ h, d h with hDdef
  set MM : ℕ := Fintype.card (multiMons (ι := ι) d) with hMMdef
  have hMMcard : MM = #(multiMons (ι := ι) d) := Fintype.card_coe _
  have hMMpos : 0 < MM := by
    rw [hMMcard]
    exact Finset.card_pos.mpr (multiMons_nonempty d)
  have hcols : ∀ b : (multiMons (ι := ι) d), ∑ t, (b : κ × ι →₀ ℕ) t = D := by
    intro b
    rw [hDdef, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun h _ ↦ mem_multiMons.mp b.2 h
  obtain ⟨Nr, e⟩ : Σ' Nr : ℕ, Fin Nr ≃ Row := ⟨_, (Fintype.equivFin _).symm⟩
  have hNr : Nr = Fintype.card Row := by simpa using Fintype.card_congr e
  set Acond : Matrix (Fin Nr) (multiMons (ι := ι) d) K :=
    (fun i c ↦ (blockSubst (Mat (e i)) (monomial (c : κ × ι →₀ ℕ) (1 : K))).coeff (Nrow (e i)))
    with hAcond
  have hrankNr : Acond.rank ≤ Nr := by simpa using Acond.rank_le_card_height
  have hrankR : (Acond.rank : ℝ) ≤ (Fintype.card Row : ℝ) := by
    rw [← hNr]; exact_mod_cast hrankNr
  have hMM0 : (0 : ℝ) < (MM : ℝ) := by exact_mod_cast hMMpos
  have hMM2 : 2 * (Acond.rank : ℝ) ≤ (MM : ℝ) := by
    rw [hMMcard]; linarith
  have hfeas : Acond.rank < Fintype.card (multiMons (ι := ι) d) := by
    have h : (Acond.rank : ℝ) < (MM : ℝ) := by linarith
    exact_mod_cast h
  obtain ⟨x, hx0, hxker, -, hxle⟩ :=
    NumberField.exists_ne_zero_mem_ker_absMulHeight_le Acond hfeas
  set P : MvPolynomial (κ × ι) K := ofMulti d x with hPdef
  have hPmulti : IsMultiHomogeneous d P := isMultiHomogeneous_ofMulti x
  refine ⟨P, fun hc ↦ hx0 ((ofMulti_eq_zero_iff x).mp hc), hPmulti, fun r ↦ ?_, ?_⟩
  · have hsum : ∑ c : (multiMons (ι := ι) d), Acond (e.symm r) c * x c = 0 := by
      rw [← Matrix.mulVec_apply_eq_sum, hxker]
      rfl
    rw [hPdef, coeff_blockSubst_ofMulti, ← hsum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [hAcond]
    simp only [Equiv.apply_symm_apply]
    ring
  · -- the height bound
    set dK : ℝ := (Module.finrank ℚ K : ℝ) with hdKdef
    have hdK0 : (0 : ℝ) < dK := by
      rw [hdKdef]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
    have hdisc1 : (1 : ℝ) ≤ |(NumberField.discr K : ℝ)| := by
      have h : (1 : ℤ) ≤ |NumberField.discr K| :=
        Int.one_le_abs (NumberField.discr_ne_zero (K := K))
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|NumberField.discr K| : ℤ) : ℝ) := by exact_mod_cast h
        _ = |(NumberField.discr K : ℝ)| := by push_cast; rfl
    have hdisc0 : (0 : ℝ) < |(NumberField.discr K : ℝ)| := by linarith
    have hcι1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    have hHy1 : (1 : ℝ) ≤ Height.mulHeight y := Height.one_le_mulHeight y
    have hHA1 : (1 : ℝ) ≤ Acond.mulHeight := Height.one_le_mulHeight _
    -- the height of the condition matrix
    have hAle : Acond.mulHeight
        ≤ ((Fintype.card ι : ℝ) ^ D) ^ Height.totalWeight K * Height.mulHeight y ^ D := by
      have heq : Acond.mulHeight
          = Height.mulHeight (fun q : Fin Nr × (multiMons (ι := ι) d) ↦
              (blockSubst (Mat (e q.1)) (monomial (q.2 : κ × ι →₀ ℕ) (1 : K))).coeff
                (Nrow (e q.1))) := rfl
      rw [heq]
      exact mulHeight_matrix_blockSubst_monomial_le (β := (multiMons (ι := ι) d))
        (fun i ↦ Mat (e i)) (fun i ↦ Nrow (e i))
        (fun c ↦ (c : κ × ι →₀ ℕ)) hcols hy fun i w ↦ hMy (e i) w
    have hlogA : Real.log Acond.mulHeight
        ≤ Height.totalWeight K * ((D : ℝ) * Real.log (Fintype.card ι))
          + (D : ℝ) * Real.log (Height.mulHeight y) := by
      refine (Real.log_le_log (by linarith) hAle).trans ?_
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        Real.log_pow]
    -- Siegel's bound
    have hxeq : (fun ν : (multiMons (ι := ι) d) ↦ P.coeff (ν : κ × ι →₀ ℕ)) = x :=
      funext fun ν ↦ coeff_ofMulti x ν
    have habs : NumberField.absMulHeight x = P.mulHeight ^ (dK)⁻¹ := by
      rw [← hxeq, hdKdef]
      exact absMulHeight_coeff_multiMons hPmulti
    have hB1 : (1 : ℝ) ≤ Real.sqrt (MM : ℝ) * Acond.mulHeight ^ (dK)⁻¹ := by
      have h1 : (1 : ℝ) ≤ Real.sqrt (MM : ℝ) := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hMMpos)
      have h2 : (1 : ℝ) ≤ Acond.mulHeight ^ (dK)⁻¹ := by
        have h := Real.rpow_le_rpow_of_exponent_le hHA1
          (show (0 : ℝ) ≤ (dK)⁻¹ by positivity)
        rwa [Real.rpow_zero] at h
      nlinarith
    have hexp : (Acond.rank : ℝ) / ((MM : ℝ) - Acond.rank) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have hpow : (Real.sqrt (MM : ℝ) * Acond.mulHeight ^ (dK)⁻¹)
          ^ ((Acond.rank : ℝ) / ((MM : ℝ) - Acond.rank))
        ≤ Real.sqrt (MM : ℝ) * Acond.mulHeight ^ (dK)⁻¹ := by
      have h := Real.rpow_le_rpow_of_exponent_le hB1 hexp
      rwa [Real.rpow_one] at h
    have hfinal : P.mulHeight ^ (dK)⁻¹
        ≤ |(NumberField.discr K : ℝ)| ^ (2 * dK : ℝ)⁻¹
          * (Real.sqrt (MM : ℝ) * Acond.mulHeight ^ (dK)⁻¹) := by
      rw [← habs]
      refine hxle.trans ?_
      rw [hMMdef]
      exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (abs_nonneg _) _)
    -- take logarithms
    have hlog := Real.log_le_log (Real.rpow_pos_of_pos (MvPolynomial.mulHeight_pos P) _) hfinal
    rw [Real.log_rpow (MvPolynomial.mulHeight_pos P),
      Real.log_mul (Real.rpow_pos_of_pos hdisc0 _).ne' (by positivity),
      Real.log_rpow hdisc0, Real.log_mul (by positivity) (by positivity),
      Real.log_sqrt (le_of_lt hMM0), Real.log_rpow (by linarith)] at hlog
    have hlogMM : Real.log (MM : ℝ) ≤ (Fintype.card ι : ℝ) * (D : ℝ) := by
      have h : Real.log ((#(multiMons (ι := ι) d) : ℕ) : ℝ)
          ≤ (Fintype.card ι : ℝ) * ∑ h, (d h : ℝ) := log_card_multiMons_le d
      rw [hMMcard, hDdef]
      push_cast
      exact h
    have hDsum : (D : ℝ) = ∑ h, (d h : ℝ) := by rw [hDdef]; push_cast; ring
    rw [MvPolynomial.logHeight_eq_log_mulHeight, ← hDsum]
    have hlogMM0 : (0 : ℝ) ≤ Real.log (MM : ℝ) := Real.log_nonneg (by exact_mod_cast hMMpos)
    have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hdK0)
    rw [← mul_assoc, mul_inv_cancel₀ hdK0.ne', one_mul] at hmul
    have hexpand : dK * ((2 * dK : ℝ)⁻¹ * Real.log |(NumberField.discr K : ℝ)|
          + (Real.log (MM : ℝ) / 2 + (dK)⁻¹ * Real.log Acond.mulHeight))
        = 2⁻¹ * Real.log |(NumberField.discr K : ℝ)|
          + (dK / 2 * Real.log (MM : ℝ) + Real.log Acond.mulHeight) := by
      field_simp
    rw [hexpand] at hmul
    have h1 : dK / 2 * Real.log (MM : ℝ) ≤ dK / 2 * ((Fintype.card ι : ℝ) * (D : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogMM (by positivity)
    nlinarith [hmul, hlogA, h1]

end Siegel

/-! ### Counting the monomials the auxiliary polynomial must omit -/

section Counting

/-- **The Chernoff bound of `Finset.card_le_of_subset_eta`, read on `multiMons`.** -/
theorem card_le_of_subset_multiMons {n : ℕ} (hn : 1 ≤ n) (hcard : Fintype.card ι = n + 1)
    (i₀ : ι) {d : κ → ℕ} (hd : ∀ h, 1 ≤ d h) {η : ℝ} (hη : 0 ≤ η)
    (E : Finset (κ × ι →₀ ℕ)) (hE : E ⊆ multiMons d)
    (hEθ : ∀ N ∈ E, ∑ h, (N (h, i₀) : ℝ) / (d h : ℝ)
      ≤ Fintype.card κ / ((n : ℝ) + 1) - Fintype.card κ * η) :
    (#E : ℝ) ≤ #(multiMons (ι := ι) d) *
      Real.exp (-(((n : ℝ) + 1) * ((n : ℝ) + 2) * η ^ 2 * Fintype.card κ / 4)
        + (η * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2) ^ 2 / (2 * ((n : ℝ) + 1))
          * ∑ h, ((d h : ℝ))⁻¹) := by
  have hval : ∀ (J : κ → ι →₀ ℕ) (h : κ),
      (blockSplit.symm J : κ × ι →₀ ℕ) (h, i₀) = J h i₀ := by
    intro J h
    rw [← blockSplit_apply, Equiv.apply_symm_apply]
  rw [show #E = #(E.map (blockSplit (κ := κ) (ι := ι)).toEmbedding) from (Finset.card_map _).symm,
    card_multiMons]
  refine Finset.card_le_of_subset_eta hn hcard i₀ d hd hη _ (fun J hJ ↦ ?_) fun J hJ ↦ ?_
  · rw [Finset.mem_map_equiv] at hJ
    have h := mem_multiMons_iff_blockSplit_mem.mp (hE hJ)
    rwa [Equiv.apply_symm_apply] at h
  · rw [Finset.mem_map_equiv] at hJ
    have h := hEθ _ hJ
    rwa [Finset.sum_congr rfl fun t _ ↦ by rw [hval J t]] at h

omit [DecidableEq κ] in
/-- Taking every block degree large enough makes the error term of the Chernoff bound as small
as required. This is the only place `d` has to be large in Layer 5.2. -/
theorem exists_forall_sum_inv_le {c θ : ℝ} (hc : 0 ≤ c) (hθ : 0 < θ) :
    ∃ D₀ : ℕ, 1 ≤ D₀ ∧ ∀ d : κ → ℕ, (∀ h, D₀ ≤ d h) → c * ∑ h, ((d h : ℝ))⁻¹ ≤ θ := by
  refine ⟨⌈c * Fintype.card κ / θ⌉₊ + 1, Nat.le_add_left 1 _, fun d hd ↦ ?_⟩
  have hD₀0 : (0 : ℝ) < ((⌈c * Fintype.card κ / θ⌉₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos _
  have hinv : ∑ h, ((d h : ℝ))⁻¹
      ≤ (Fintype.card κ : ℝ) * (((⌈c * Fintype.card κ / θ⌉₊ + 1 : ℕ) : ℝ))⁻¹ := by
    calc ∑ h, ((d h : ℝ))⁻¹
        ≤ ∑ _h : κ, (((⌈c * Fintype.card κ / θ⌉₊ + 1 : ℕ) : ℝ))⁻¹ :=
          Finset.sum_le_sum fun h _ ↦ inv_anti₀ hD₀0 (by exact_mod_cast hd h)
      _ = (Fintype.card κ : ℝ) * (((⌈c * Fintype.card κ / θ⌉₊ + 1 : ℕ) : ℝ))⁻¹ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hceil : c * Fintype.card κ / θ ≤ ((⌈c * Fintype.card κ / θ⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.le_ceil (c * Fintype.card κ / θ)]
  rw [div_le_iff₀ hθ] at hceil
  calc c * ∑ h, ((d h : ℝ))⁻¹
      ≤ c * ((Fintype.card κ : ℝ) * (((⌈c * Fintype.card κ / θ⌉₊ + 1 : ℕ) : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_left hinv hc
    _ = (c * Fintype.card κ) * (((⌈c * Fintype.card κ / θ⌉₊ + 1 : ℕ) : ℝ))⁻¹ := by ring
    _ ≤ θ := by
        rw [mul_inv_le_iff₀ hD₀0]
        linarith

end Counting

/-! ### The milestone -/

section Milestone

variable [NumberField K]

omit [DecidableEq κ] in
/-- **Layer 5.2 — the multihomogeneous auxiliary polynomial** (Bombieri–Gubler, Lemma 7.5.15).
For every multidegree `d` with all entries large enough there is a nonzero multihomogeneous
polynomial `P` of multidegree `d` of logarithmic height at most `C₂ ∑ h, d h`, such that every
Hasse derivative of `P` read in any of the coordinate systems `A v` again has logarithmic height
at most `C₃ ∑ h, d h`, and such that the coefficient of the monomial `J` in that derivative
vanishes whenever the order `I` is small and one of the exponents of `J` is far from its mean
`∑ h, d h / (n + 1)`. -/
theorem exists_ne_zero_isMultiHomogeneous_forall_coeff_blockSubst_hasseDeriv_eq_zero
    [Nonempty ι] [Nonempty κ] {n : ℕ} (hn : 1 ≤ n) (hcard : Fintype.card ι = n + 1)
    {S : Type*} [Fintype S] [Nonempty S] (A : S → Matrix ι ι K) (hA : ∀ v, IsUnit (A v).det)
    {η : ℝ} (hη : 0 < η)
    (hm : 4 * Real.log (2 * ((n : ℝ) + 1) * Fintype.card S)
      < ((n : ℝ) + 1) * ((n : ℝ) + 2) * η ^ 2 * Fintype.card κ) :
    ∃ C₂ C₃ : ℝ, ∃ D₀ : ℕ, ∀ d : κ → ℕ, (∀ h, D₀ ≤ d h) →
      ∃ P : MvPolynomial (κ × ι) K, P ≠ 0 ∧ IsMultiHomogeneous d P ∧
        P.logHeight ≤ C₂ * ∑ h, (d h : ℝ) ∧
        (∀ (v : S) (I : κ × ι →₀ ℕ),
          (blockSubst (A v)⁻¹ (hasseDeriv I P)).logHeight ≤ C₃ * ∑ h, (d h : ℝ)) ∧
        ∀ (v : S) (I J : κ × ι →₀ ℕ),
          ∑ h, (∑ i, (I (h, i) : ℝ)) / (d h : ℝ) ≤ Fintype.card κ * η →
          (∃ i, ∑ h, (J (h, i) : ℝ) / (d h : ℝ)
                ≤ Fintype.card κ / ((n : ℝ) + 1) - 2 * Fintype.card κ * η ∨
              Fintype.card κ / ((n : ℝ) + 1) + 2 * (n : ℝ) * Fintype.card κ * η
                ≤ ∑ h, (J (h, i) : ℝ) / (d h : ℝ)) →
          (blockSubst (A v)⁻¹ (hasseDeriv I P)).coeff J = 0 := by
  classical
  -- a reference tuple collecting the entries of all the matrices `(A v)⁻¹` and `1`
  obtain ⟨y, hy0, hMy⟩ : ∃ y : (S × ι × ι) ⊕ Unit → K, y ≠ 0 ∧
      ∀ (v : S) (w : AbsoluteValue K ℝ),
        (⨆ p : ι × ι, w (((A v)⁻¹) p.1 p.2)) ⊔ 1 ≤ ⨆ s, w (y s) := by
    refine ⟨Sum.elim (fun p : S × ι × ι ↦ ((A p.1)⁻¹) p.2.1 p.2.2) (fun _ : Unit ↦ 1),
      fun hc ↦ one_ne_zero (congrFun hc (Sum.inr ())), fun v w ↦ ?_⟩
    set z : (S × ι × ι) ⊕ Unit → K :=
      Sum.elim (fun p : S × ι × ι ↦ ((A p.1)⁻¹) p.2.1 p.2.2) (fun _ : Unit ↦ 1) with hz
    have hb : ∀ s, w (z s) ≤ ⨆ s', w (z s') :=
      fun s ↦ le_ciSup (f := fun s' ↦ w (z s')) (Finite.bddAbove_range _) s
    have hone : w (z (Sum.inr ())) = 1 := by rw [hz]; simp
    have hval : ∀ p : ι × ι, w (z (Sum.inl (v, p))) = w (((A v)⁻¹) p.1 p.2) := by
      intro p
      rw [hz]
      simp
    have h1 : (1 : ℝ) ≤ ⨆ s', w (z s') := by
      rw [← hone]
      exact hb (Sum.inr ())
    refine sup_le (Real.iSup_le (fun p ↦ ?_) (by linarith)) h1
    rw [← hval p]
    exact hb (Sum.inl (v, p))
  have hcι1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hHy1 : (1 : ℝ) ≤ Height.mulHeight y := Height.one_le_mulHeight y
  have hdisc0 : (0 : ℝ) ≤ Real.log |(NumberField.discr K : ℝ)| := by
    refine Real.log_nonneg ?_
    have h : (1 : ℤ) ≤ |NumberField.discr K| :=
      Int.one_le_abs (NumberField.discr_ne_zero (K := K))
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|NumberField.discr K| : ℤ) : ℝ) := by exact_mod_cast h
      _ = |(NumberField.discr K : ℝ)| := by push_cast; rfl
  -- the degree threshold
  obtain ⟨D₀, hD₀1, hD₀⟩ := exists_forall_sum_inv_le (κ := κ)
    (c := (η * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2) ^ 2 / (2 * ((n : ℝ) + 1)))
    (θ := ((n : ℝ) + 1) * ((n : ℝ) + 2) * η ^ 2 * Fintype.card κ / 4
      - Real.log (2 * ((n : ℝ) + 1) * Fintype.card S))
    (by positivity) (by linarith)
  refine ⟨2⁻¹ * Real.log |(NumberField.discr K : ℝ)|
      + ((Module.finrank ℚ K : ℝ) / 2 * Fintype.card ι
          + Height.totalWeight K * Real.log (Fintype.card ι)
          + Real.log (Height.mulHeight y)),
    Height.totalWeight K * ((Fintype.card ι : ℝ) + Real.log 2 + Real.log (Fintype.card ι))
      + (2⁻¹ * Real.log |(NumberField.discr K : ℝ)|
        + ((Module.finrank ℚ K : ℝ) / 2 * Fintype.card ι
            + Height.totalWeight K * Real.log (Fintype.card ι)
            + Real.log (Height.mulHeight y)))
      + Real.log (Height.mulHeight y), D₀, fun d hd ↦ ?_⟩
  have hd1 : ∀ h, 1 ≤ d h := fun h ↦ le_trans hD₀1 (hd h)
  have hdpos : ∀ h, (0 : ℝ) < (d h : ℝ) := fun h ↦ by exact_mod_cast hd1 h
  have hDcast : ((∑ h, d h : ℕ) : ℝ) = ∑ h, (d h : ℝ) := by push_cast; ring
  have hD1 : (1 : ℝ) ≤ ∑ h, (d h : ℝ) := by
    obtain ⟨h₀⟩ := ‹Nonempty κ›
    calc (1 : ℝ) ≤ (d h₀ : ℝ) := by exact_mod_cast hd1 h₀
      _ ≤ ∑ h, (d h : ℝ) := Finset.single_le_sum (fun h _ ↦ (hdpos h).le) (Finset.mem_univ h₀)
  -- the monomials that must be omitted, one set for each coordinate
  obtain ⟨Bad, hBad⟩ : ∃ Bad : ι → Finset (κ × ι →₀ ℕ), ∀ (i₀ : ι) (N : κ × ι →₀ ℕ),
      N ∈ Bad i₀ ↔ (N ∈ multiMons d ∧ ∑ h, (N (h, i₀) : ℝ) / (d h : ℝ)
        ≤ Fintype.card κ / ((n : ℝ) + 1) - Fintype.card κ * η) :=
    ⟨fun i₀ ↦ {N ∈ multiMons d | ∑ h, (N (h, i₀) : ℝ) / (d h : ℝ)
      ≤ Fintype.card κ / ((n : ℝ) + 1) - Fintype.card κ * η}, fun i₀ N ↦ Finset.mem_filter⟩
  have hcS0 : (0 : ℝ) < (Fintype.card S : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcιn : (Fintype.card ι : ℝ) = (n : ℝ) + 1 := by rw [hcard]; push_cast; ring
  have hbad : ∀ i₀ : ι, (#(Bad i₀) : ℝ)
      ≤ #(multiMons (ι := ι) d) * (2 * ((n : ℝ) + 1) * Fintype.card S)⁻¹ := by
    intro i₀
    refine (card_le_of_subset_multiMons hn hcard i₀ hd1 hη.le _
      (fun N hN ↦ ((hBad i₀ N).mp hN).1) (fun N hN ↦ ((hBad i₀ N).mp hN).2)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hexp : -(((n : ℝ) + 1) * ((n : ℝ) + 2) * η ^ 2 * Fintype.card κ / 4)
        + (η * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2) ^ 2 / (2 * ((n : ℝ) + 1))
          * ∑ h, ((d h : ℝ))⁻¹
        ≤ -Real.log (2 * ((n : ℝ) + 1) * Fintype.card S) := by
      linarith [hD₀ d hd]
    calc Real.exp (-(((n : ℝ) + 1) * ((n : ℝ) + 2) * η ^ 2 * Fintype.card κ / 4)
            + (η * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2) ^ 2 / (2 * ((n : ℝ) + 1))
              * ∑ h, ((d h : ℝ))⁻¹)
        ≤ Real.exp (-Real.log (2 * ((n : ℝ) + 1) * Fintype.card S)) := Real.exp_le_exp.mpr hexp
      _ = (2 * ((n : ℝ) + 1) * Fintype.card S)⁻¹ := by
          rw [Real.exp_neg, Real.exp_log (by positivity)]
  -- there are at most half as many conditions as monomials
  have hcount : 2 * (Fintype.card (Σ p : S × ι, ↥(Bad p.2)) : ℝ)
      ≤ #(multiMons (ι := ι) d) := by
    have hcardsig : (Fintype.card (Σ p : S × ι, ↥(Bad p.2)) : ℝ)
        = ∑ p : S × ι, (#(Bad p.2) : ℝ) := by
      rw [Fintype.card_sigma]
      push_cast
      exact Finset.sum_congr rfl fun p _ ↦ by rw [Fintype.card_coe]
    have hle : ∑ p : S × ι, (#(Bad p.2) : ℝ)
        ≤ (Fintype.card S : ℝ) * ((n : ℝ) + 1)
          * (#(multiMons (ι := ι) d) * (2 * ((n : ℝ) + 1) * Fintype.card S)⁻¹) := by
      calc ∑ p : S × ι, (#(Bad p.2) : ℝ)
          ≤ ∑ _p : S × ι,
              (#(multiMons (ι := ι) d) : ℝ) * (2 * ((n : ℝ) + 1) * Fintype.card S)⁻¹ :=
            Finset.sum_le_sum fun p _ ↦ hbad p.2
        _ = (Fintype.card S : ℝ) * ((n : ℝ) + 1)
              * (#(multiMons (ι := ι) d) * (2 * ((n : ℝ) + 1) * Fintype.card S)⁻¹) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, ← hcιn]
            push_cast
            ring
    rw [hcardsig]
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have heq : 2 * ((Fintype.card S : ℝ) * ((n : ℝ) + 1)
        * (#(multiMons (ι := ι) d) * (2 * ((n : ℝ) + 1) * Fintype.card S)⁻¹))
        = (#(multiMons (ι := ι) d) : ℝ) := by field_simp
    linarith [mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 2)]
  -- Siegel's lemma
  obtain ⟨P, hP0, hPmulti, hPcond, hPht⟩ :=
    exists_ne_zero_isMultiHomogeneous_coeff_blockSubst_eq_zero (d := d)
      (Row := Σ p : S × ι, ↥(Bad p.2))
      (fun r ↦ (A r.1.1)⁻¹) (fun r ↦ (r.2 : κ × ι →₀ ℕ)) hy0 (fun r w ↦ hMy r.1.1 w) hcount
  have hPsub : P.support ⊆ multiMons d := fun ν hν ↦
    mem_multiMons.mpr fun h ↦ hPmulti (MvPolynomial.mem_support_iff.mp hν) h
  have hPsupp : ∀ ν ∈ P.support, ∑ t, ν t ≤ ∑ h, d h := fun ν hν ↦
    le_of_eq (hPmulti.sum_eq (MvPolynomial.mem_support_iff.mp hν))
  have hsp0 : (0 : ℝ) < (#P.support : ℝ) := by
    have h : 0 < #P.support := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr
      fun hc ↦ hP0 (MvPolynomial.support_eq_empty.mp hc))
    exact_mod_cast h
  have hlogsp : Real.log (#P.support : ℝ) ≤ (Fintype.card ι : ℝ) * ∑ h, (d h : ℝ) := by
    have hcardle : ((#P.support : ℕ) : ℝ) ≤ ((#(multiMons (ι := ι) d) : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_le_card hPsub
    exact le_trans (Real.log_le_log hsp0 hcardle) (log_card_multiMons_le d)
  -- the height of `P`
  have hheight : P.logHeight ≤ (2⁻¹ * Real.log |(NumberField.discr K : ℝ)|
      + ((Module.finrank ℚ K : ℝ) / 2 * Fintype.card ι
          + Height.totalWeight K * Real.log (Fintype.card ι)
          + Real.log (Height.mulHeight y))) * ∑ h, (d h : ℝ) := by
    nlinarith [hPht, hdisc0, hD1]
  -- the vanishing in the low case
  have hlow : ∀ (v : S) (I J : κ × ι →₀ ℕ) (i₀ : ι),
      ∑ h, (∑ i, (I (h, i) : ℝ)) / (d h : ℝ) ≤ Fintype.card κ * η →
      ∑ h, (J (h, i₀) : ℝ) / (d h : ℝ)
        ≤ Fintype.card κ / ((n : ℝ) + 1) - 2 * Fintype.card κ * η →
      (blockSubst (A v)⁻¹ (hasseDeriv I P)).coeff J = 0 := by
    intro v I J i₀ hI hJ
    have hQ : blockSubst (A v) (blockSubst ((A v)⁻¹) P) = P :=
      blockSubst_blockSubst (Matrix.nonsing_inv_mul _ (hA v)) P
    have hcond : ∀ I' : κ × ι →₀ ℕ, (∀ h, ∑ i, I' (h, i) = ∑ i, I (h, i)) →
        (blockSubst ((A v)⁻¹) P).coeff (J + I') = 0 := by
      intro I' hI'
      by_cases hmem : J + I' ∈ multiMons d
      · refine hPcond ⟨(v, i₀), ⟨J + I', (hBad i₀ (J + I')).mpr ⟨hmem, ?_⟩⟩⟩
        have hsplit : ∀ h : κ, ((J + I') (h, i₀) : ℝ) / (d h : ℝ)
            = (J (h, i₀) : ℝ) / (d h : ℝ) + (I' (h, i₀) : ℝ) / (d h : ℝ) := by
          intro h
          rw [Finsupp.add_apply]
          push_cast
          ring
        have hI'le : ∀ h : κ, (I' (h, i₀) : ℝ) / (d h : ℝ)
            ≤ (∑ i, (I (h, i) : ℝ)) / (d h : ℝ) := by
          intro h
          refine div_le_div_of_nonneg_right ?_ (hdpos h).le
          have h1 : (I' (h, i₀) : ℝ) ≤ ∑ i, (I' (h, i) : ℝ) :=
            Finset.single_le_sum (f := fun i ↦ (I' (h, i) : ℝ))
              (fun i _ ↦ Nat.cast_nonneg _) (Finset.mem_univ i₀)
          have h2 : ∑ i, (I' (h, i) : ℝ) = ∑ i, (I (h, i) : ℝ) := by
            have h5 : ((∑ i, I' (h, i) : ℕ) : ℝ) = ((∑ i, I (h, i) : ℕ) : ℝ) := by
              exact_mod_cast congrArg (fun k : ℕ ↦ (k : ℝ)) (hI' h)
            push_cast at h5
            exact h5
          linarith
        have h3 : ∑ h, (I' (h, i₀) : ℝ) / (d h : ℝ) ≤ Fintype.card κ * η :=
          le_trans (Finset.sum_le_sum fun h _ ↦ hI'le h) hI
        rw [Finset.sum_congr rfl fun h _ ↦ hsplit h, Finset.sum_add_distrib]
        linarith
      · by_contra hne
        exact hmem (mem_multiMons.mpr fun h ↦ (hPmulti.blockSubst ((A v)⁻¹)) hne h)
    have h := coeff_blockSubst_hasseDeriv_eq_zero (A := A v) (M := (A v)⁻¹)
      (Matrix.mul_nonsing_inv _ (hA v)) (∑ t, I t) I rfl (blockSubst ((A v)⁻¹) P) J hcond
    rwa [hQ] at h
  refine ⟨P, hP0, hPmulti, hheight, fun v I ↦ ?_, fun v I J hI hJ ↦ ?_⟩
  · -- the height of a substituted Hasse derivative
    have hb := logHeight_blockSubst_hasseDeriv_le ((A v)⁻¹) I hy0 (hMy v) hP0
      (D := ∑ h, d h) hPsupp
    rw [hDcast] at hb
    have htw0 : (0 : ℝ) ≤ (Height.totalWeight K : ℝ) := Nat.cast_nonneg _
    linarith [hb, hheight, mul_le_mul_of_nonneg_left hlogsp htw0]
  · -- the vanishing
    obtain ⟨i₀, hi₀ | hi₀⟩ := hJ
    · exact hlow v I J i₀ hI hi₀
    · by_contra hne
      have hHne : hasseDeriv I P ≠ 0 := by
        intro hc
        rw [hc, map_zero] at hne
        exact hne (by simp)
      obtain ⟨ν₀, hν₀⟩ := Finset.nonempty_iff_ne_empty.mpr
        (fun hc ↦ hHne (MvPolynomial.support_eq_empty.mp hc))
      have hIle : ∀ h, ∑ i, I (h, i) ≤ d h := by
        intro h
        have := hPmulti.coeff_hasseDeriv (MvPolynomial.mem_support_iff.mp hν₀) h
        omega
      have hJdeg : ∀ h, ∑ i, (J (h, i) : ℝ) = (d h : ℝ) - ∑ i, (I (h, i) : ℝ) := by
        intro h
        have h1 : ∑ i, J (h, i) = d h - ∑ i, I (h, i) :=
          (hPmulti.hasseDeriv I).blockSubst ((A v)⁻¹) hne h
        have h4 : ((∑ i, J (h, i) : ℕ) : ℝ) = ((d h - ∑ i, I (h, i) : ℕ) : ℝ) := by
          exact_mod_cast congrArg (fun k : ℕ ↦ (k : ℝ)) h1
        rw [Nat.cast_sub (hIle h)] at h4
        push_cast at h4 ⊢
        linarith
      have hsumJ : ∑ i, ∑ h, (J (h, i) : ℝ) / (d h : ℝ)
          = (Fintype.card κ : ℝ) - ∑ h, (∑ i, (I (h, i) : ℝ)) / (d h : ℝ) := by
        rw [Finset.sum_comm]
        have hterm : ∀ h : κ, ∑ i, (J (h, i) : ℝ) / (d h : ℝ)
            = 1 - (∑ i, (I (h, i) : ℝ)) / (d h : ℝ) := by
          intro h
          rw [← Finset.sum_div, hJdeg h, sub_div, div_self (hdpos h).ne']
        rw [Finset.sum_congr rfl fun h _ ↦ hterm h, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_one]
      have hI0 : 0 ≤ ∑ h, (∑ i, (I (h, i) : ℝ)) / (d h : ℝ) :=
        Finset.sum_nonneg fun h _ ↦ div_nonneg (Finset.sum_nonneg fun i _ ↦ Nat.cast_nonneg _)
          (hdpos h).le
      have hcarde : #(Finset.univ.erase i₀) = n := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, hcard]
        omega
      have hne0 : (Finset.univ.erase i₀).Nonempty := by
        rw [← Finset.card_pos, hcarde]
        omega
      have hsplit : ∑ i ∈ Finset.univ.erase i₀, ∑ h, (J (h, i) : ℝ) / (d h : ℝ)
          = (∑ i, ∑ h, (J (h, i) : ℝ) / (d h : ℝ)) - ∑ h, (J (h, i₀) : ℝ) / (d h : ℝ) := by
        rw [eq_sub_iff_add_eq, Finset.sum_erase_add _ _ (Finset.mem_univ i₀)]
      have hbound : ∑ i ∈ Finset.univ.erase i₀, ∑ h, (J (h, i) : ℝ) / (d h : ℝ)
          ≤ ∑ _i ∈ Finset.univ.erase i₀,
            ((Fintype.card κ : ℝ) / ((n : ℝ) + 1) - 2 * Fintype.card κ * η) := by
        rw [Finset.sum_const, hcarde, nsmul_eq_mul, hsplit, hsumJ]
        have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hexp : (n : ℝ) * ((Fintype.card κ : ℝ) / ((n : ℝ) + 1) - 2 * Fintype.card κ * η)
            = (Fintype.card κ : ℝ) - (Fintype.card κ : ℝ) / ((n : ℝ) + 1)
              - 2 * (n : ℝ) * Fintype.card κ * η := by
          field_simp
          ring
        rw [hexp]
        linarith
      obtain ⟨i₁, hi₁, hle⟩ := Finset.exists_le_of_sum_le hne0 hbound
      exact hne (hlow v I J i₁ hI hle)

end Milestone

/-! ### Acceptance criteria -/

section Acceptance

/-- **Acceptance test: the substitution composes contravariantly.** This is why the expansion
coefficients of Lemma 7.5.15 are read through `(A v)⁻¹` and not through `A v`. -/
example {F : Type*} [Field F] {α β : Type*} [Fintype β] [DecidableEq β] (A : Matrix β β F)
    (hA : IsUnit A.det) (P : MvPolynomial (α × β) F) : blockSubst A (blockSubst A⁻¹ P) = P :=
  blockSubst_blockSubst (Matrix.nonsing_inv_mul _ hA) P

/-- **Acceptance test: at order `0` the milestone's vanishing is a statement about the
coefficients of `P` itself**, read in the transformed coordinates. -/
example {F : Type*} [Field F] {α β : Type*} [Fintype β] [DecidableEq β] (A : Matrix β β F)
    (P : MvPolynomial (α × β) F) :
    blockSubst A⁻¹ (hasseDeriv 0 P) = blockSubst A⁻¹ P := by
  rw [hasseDeriv_zero_apply]

/-- **Rejection test: a Hasse derivative loses degree in a block only up to the order in that
block.** The multidegree of `hasseDeriv I P` is `d h − ∑ i, I (h, i)`, not `d h − ∑ t, I t`, which
is what makes the identity `∑ i, ∑ h, J (h, i) / d h = m − ∑ h, (∑ i, I (h, i)) / d h` of the
upper half of Lemma 7.5.15 come out. -/
example {F : Type*} [Field F] [CharZero F] :
    hasseDeriv (Finsupp.single ((0, 0) : Fin 1 × Fin 2) 1)
        (X ((0, 0) : Fin 1 × Fin 2) * X ((0, 1) : Fin 1 × Fin 2) : MvPolynomial (Fin 1 × Fin 2) F)
      = X ((0, 1) : Fin 1 × Fin 2) := by
  rw [hasseDeriv_single_one, Derivation.leibniz]
  simp

end Acceptance

end MvPolynomial
