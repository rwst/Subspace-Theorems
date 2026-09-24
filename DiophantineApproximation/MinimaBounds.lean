/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ApproximationRank

-- Used only inside proofs.
import DiophantineApproximation.SubspaceHeightBounds

/-!
# The minima of an approximation domain lie between two powers of the level

For a number field `K`, forms `L` independent at every infinite place and at every place of
`Sfin`, exponents `c` and a level `Q`, the successive minima over `K` of the approximation domain
(Layer 4.2) satisfy

```text
Q ^ (-B)  ≤  μ j  ≤  Q ^ B      for all  j < #ι  and all large  Q,
```

with `B` depending on `K`, `Sfin`, the forms and `c` but not on `Q`. This is the one estimate
Step IX of Bombieri–Gubler's proof needs that Layers 4.1–4.5 do not state: it is what confines the
exponents of the wedge domain to a box, so that rounding them to a grid leaves finitely many
systems of exponents.

The lower bound is arithmetic and not geometry of numbers: a nonzero point of `Λ ∩ t B` has
height at least `1`, while its height is at most a constant times `t ^ d` times `Q` to the sum of
the largest exponents, so `t` cannot be smaller than a fixed negative power of `Q`. The upper
bound is then Minkowski's second theorem over `K` from above (Layer 4.2), which bounds the product
of all the minima: the last is the product divided by the others, and the others are bounded below
by the first bound.

## Main results

* `NumberField.exists_pos_forall_one_le_mul_pow_rpow`: the height of a nonzero point of a dilated
  domain, from below by `1` and from above by the local bounds.
* `NumberField.exists_pos_forall_rpow_le_successiveMinimum`: the first minimum is at least a
  negative power of `Q`.
* `NumberField.exists_pos_forall_rpow_le_successiveMinimum_le`: **all the minima lie between
  `Q ^ (-B)` and `Q ^ B`**.

## Implementation notes

⚠ **Only the lower bound is new.** Layer 4.2 bounds the product of the minima from both sides, and
both bounds are useless alone at the ends: the product bounds give an upper bound for the *first*
minimum and a lower bound for the *last*, which are the two directions that do not confine the
system. The missing direction is the product formula, in the form `1 ≤ H(x)`.

⚠ **The exponent absorbs every constant.** The statements are of the shape `Q ^ (-B) ≤ μ j` and
not `E · Q ^ (-B) ≤ μ j`: above a threshold the constant is at most `Q`, and one more unit in the
exponent swallows it. That keeps the grid of Layer 6.1 free of constants.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
7.5.32 (Step IX).

This is part of Layer 6.1 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset Module NumberField NumberField.mixedEmbedding NumberField.InfinitePlace

open scoped Pointwise

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Nonempty ι]
  {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}

/-- **A nonzero point of a dilated approximation domain is not too small**: its height is at
least `1`, and its height is at most a constant times `t ^ d` times `Q` to the sum of the largest
exponents. -/
theorem exists_pos_forall_one_le_mul_pow_rpow [Finite ι]
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∃ W : ℝ, ∀ Q t : ℝ, 1 ≤ Q → 0 < t → ∀ x : ι → K, x ≠ 0 →
      (∀ (w : InfinitePlace K) (i : ι), w (L w.1 i x) ≤ t * Q ^ c w.1 i) →
      (∀ v ∈ Sfin, ∀ i : ι, v (L v.1 i x) ≤ Q ^ c v.1 i) →
      (∀ v : FinitePlace K, v ∉ Sfin → ∀ j : ι, v (x j) ≤ 1) →
      1 ≤ A * t ^ finrank ℚ K * Q ^ W := by
  classical
  choose AI hAI1 hAI using fun w : InfinitePlace K ↦
    NumberField.exists_one_le_forall_apply_le w.1 (hLInf w)
  choose AF hAF1 hAF using fun v : {v : FinitePlace K // v ∈ Sfin} ↦
    NumberField.exists_one_le_forall_apply_le v.1.1 (hLFin v.1 v.2)
  obtain ⟨A₁, hA₁, hA₁le⟩ := Finset.exists_one_le_forall_le (univ : Finset (InfinitePlace K)) AI
  obtain ⟨A₂, hA₂, hA₂le⟩ :=
    Finset.exists_one_le_forall_le (univ : Finset {v : FinitePlace K // v ∈ Sfin}) AF
  set A' : ℝ := A₁ * A₂ with hA'
  have hA'1 : 1 ≤ A' := by nlinarith
  refine ⟨A' ^ (finrank ℚ K + #Sfin), by positivity,
    ∑ w : InfinitePlace K, (w.mult : ℝ) * (⨆ i, c w.1 i) + ∑ v ∈ Sfin, (⨆ i, c v.1 i), ?_⟩
  intro Q t hQ ht x hx hinf hfin hout
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le one_pos hQ
  have hnn : ∀ v : AbsoluteValue K ℝ, (0 : ℝ) ≤ ⨆ i, v (x i) :=
    fun v ↦ Real.iSup_nonneg fun i ↦ v.nonneg _
  have hcle : ∀ (v : AbsoluteValue K ℝ) (i : ι), Q ^ c v i ≤ Q ^ (⨆ i, c v i) := fun v i ↦
    Real.rpow_le_rpow_of_exponent_le hQ (Finite.le_ciSup_of_le i le_rfl)
  have hI : ∀ w : InfinitePlace K, (⨆ i, w (x i)) ≤ A' * (t * Q ^ (⨆ i, c w.1 i)) := by
    intro w
    have hb : ∀ k, w.1 (L w.1 k x) ≤ t * Q ^ (⨆ i, c w.1 i) := fun k ↦
      (hinf w k).trans (by nlinarith [hcle w.1 k, Real.rpow_nonneg hQ0.le (c w.1 k)])
    have hb0 : (0 : ℝ) ≤ t * Q ^ (⨆ i, c w.1 i) := by positivity
    refine Real.iSup_le (fun i ↦ le_trans (hAI w x _ hb0 hb i) ?_) (by positivity)
    exact mul_le_mul_of_nonneg_right
      (le_trans (hA₁le w (mem_univ w)) (le_mul_of_one_le_right (by linarith) hA₂)) hb0
  have hF : ∀ v ∈ Sfin, (⨆ i, v (x i)) ≤ A' * Q ^ (⨆ i, c v.1 i) := by
    intro v hv
    have hb : ∀ k, v.1 (L v.1 k x) ≤ Q ^ (⨆ i, c v.1 i) := fun k ↦ (hfin v hv k).trans (hcle v.1 k)
    have hb0 : (0 : ℝ) ≤ Q ^ (⨆ i, c v.1 i) := Real.rpow_nonneg hQ0.le _
    refine Real.iSup_le (fun i ↦ le_trans (hAF ⟨v, hv⟩ x _ hb0 hb i) ?_) (by positivity)
    exact mul_le_mul_of_nonneg_right
      (le_trans (hA₂le ⟨v, hv⟩ (mem_univ _)) (le_mul_of_one_le_left (by linarith) hA₁)) hb0
  have hO : ∀ v : FinitePlace K, v ∉ Sfin → (⨆ i, v (x i)) ≤ 1 := fun v hv ↦
    Real.iSup_le (fun i ↦ hout v hv i) zero_le_one
  have hkey : Height.mulHeight x ≤ A' ^ (finrank ℚ K + #Sfin) * t ^ finrank ℚ K *
      Q ^ (∑ w : InfinitePlace K, (w.mult : ℝ) * (⨆ i, c w.1 i) + ∑ v ∈ Sfin, (⨆ i, c v.1 i)) := by
    rw [NumberField.mulHeight_eq hx]
    have h1 : (∏ w : InfinitePlace K, (⨆ i, w (x i)) ^ w.mult)
        ≤ ∏ w : InfinitePlace K, (A' * t * Q ^ (⨆ i, c w.1 i)) ^ w.mult :=
      Finset.prod_le_prod₀ (fun w _ ↦ pow_nonneg (hnn w.1) _)
        fun w _ ↦ pow_le_pow_left₀ (hnn w.1) (by rw [mul_assoc]; exact hI w) _
    have h2 : (∏ᶠ v : FinitePlace K, ⨆ i, v (x i)) ≤ ∏ v ∈ Sfin, A' * Q ^ (⨆ i, c v.1 i) := by
      refine le_trans (finprod_le_prod_of_le_one_outside Sfin (fun v ↦ hnn v.1) hO
        (FinitePlace.hasFiniteMulSupport_iSup hx)) ?_
      exact Finset.prod_le_prod₀ (fun v _ ↦ hnn v.1) fun v hv ↦ hF v hv
    have h3 : (0 : ℝ) ≤ ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) := finprod_nonneg fun v ↦ hnn v.1
    have h4 : (0 : ℝ) ≤ ∏ w : InfinitePlace K, (A' * t * Q ^ (⨆ i, c w.1 i)) ^ w.mult :=
      Finset.prod_nonneg fun w _ ↦ pow_nonneg (by positivity) _
    refine le_trans (mul_le_mul h1 h2 h3 h4) ?_
    rw [prod_mul_rpow_pow hQ0 univ (fun w : InfinitePlace K ↦ ⨆ i, c w.1 i) (fun w ↦ w.mult),
      show (∏ v ∈ Sfin, A' * Q ^ (⨆ i, c v.1 i))
          = ∏ v ∈ Sfin, (A' * Q ^ (⨆ i, c v.1 i)) ^ (fun _ : FinitePlace K ↦ 1) v from by simp,
      prod_mul_rpow_pow hQ0 Sfin (fun v : FinitePlace K ↦ ⨆ i, c v.1 i) (fun _ ↦ 1)]
    rw [mul_mul_mul_comm, ← Real.rpow_add hQ0]
    have hmult : ∑ w : InfinitePlace K, w.mult = finrank ℚ K := by
      rw [← NumberField.totalWeight_eq_sum_mult K, NumberField.totalWeight_eq_finrank]
    have hcard : ∑ _v ∈ Sfin, 1 = #Sfin := by simp
    have he1 : (∑ a : InfinitePlace K, (⨆ i, c a.1 i) * (a.mult : ℝ))
        = ∑ w : InfinitePlace K, (w.mult : ℝ) * ⨆ i, c w.1 i :=
      Finset.sum_congr rfl fun w _ ↦ mul_comm _ _
    have he2 : (∑ a ∈ Sfin, (⨆ i, c a.1 i) * (((1 : ℕ) : ℝ))) = ∑ v ∈ Sfin, ⨆ i, c v.1 i :=
      Finset.sum_congr rfl fun v _ ↦ by push_cast; ring
    rw [hmult, hcard, he1, he2, mul_pow, pow_add]
    exact le_of_eq (by ring)
  linarith [Height.one_le_mulHeight x, hkey]

variable [Fintype ι]

open scoped Classical in
/-- **The first minimum of an approximation domain is at least a negative power of `Q`**: a
nonzero point of the domain has height at least `1`, and its height is at most a constant times
the dilation to the power `d` times `Q` to the sum of the largest exponents. -/
theorem exists_pos_forall_rpow_le_successiveMinimum
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∃ Q₁ : ℝ, 1 ≤ Q₁ ∧ ∀ Q : ℝ, Q₁ ≤ Q →
      Q ^ (-B) ≤ successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) 0 := by
  obtain ⟨A, hA, W, hW⟩ := exists_pos_forall_one_le_mul_pow_rpow hLInf hLFin c
  have hd : 0 < finrank ℚ K := finrank_pos
  have hd0 : ((finrank ℚ K : ℝ)) ≠ 0 := by positivity
  refine ⟨(max W 0 + 1) / finrank ℚ K, by positivity, max 1 A, le_max_left _ _, fun Q hQ ↦ ?_⟩
  set B : ℝ := (max W 0 + 1) / finrank ℚ K with hB
  have hQ1 : (1 : ℝ) ≤ Q := le_trans (le_max_left _ _) hQ
  have hQA : A ≤ Q := le_trans (le_max_right _ _) hQ
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le one_pos hQ1
  have hBd : B * finrank ℚ K = max W 0 + 1 := div_mul_cancel₀ _ hd0
  have hprod : A * Q ^ (W - B * finrank ℚ K) ≤ 1 := by
    have h1 : Q ^ (W - B * finrank ℚ K) ≤ Q ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hBd]; linarith [le_max_left W 0])
    rw [Real.rpow_neg hQ0.le, Real.rpow_one] at h1
    have h2 : A * Q⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ hQ0, one_mul]
      exact hQA
    nlinarith [Real.rpow_nonneg hQ0.le (W - B * finrank ℚ K)]
  have hD : DiscreteTopology (approxLattice Sfin L c Q) :=
    discreteTopology_approxLattice hLFin c hQ0.ne'
  have : DiscreteTopology (approxModule Sfin L c Q).mixedImage := hD
  have hZ : IsZLattice ℝ (approxLattice Sfin L c Q) := isZLattice_approxLattice hLFin c hQ0.ne'
  have : IsZLattice ℝ (approxModule Sfin L c Q).mixedImage := hZ
  refine le_successiveMinimum _ (convex_approxBody L c Q) (fun z hz ↦ neg_mem_approxBody hz)
    ⟨0, mem_interior_iff_mem_nhds.2 (approxBody_mem_nhds_zero L c hQ0)⟩
    (isBounded_approxBody hLInf c Q) Fintype.card_pos ?_
  intro t ht x hx hind
  by_contra hcon
  push Not at hcon
  have hne : x 0 ≠ 0 := hind.ne_zero 0
  have hinf : ∀ (w : InfinitePlace K) (i : ι), w (L w.1 i (x 0)) ≤ t * Q ^ c w.1 i := by
    intro w i
    have h := (mem_smul_approxBody_iff ht).1 (hx 0).2 w i
    rwa [normAtPlace_sum_mixedEmbedding] at h
  have hfin : ∀ v ∈ Sfin, ∀ i : ι, v (L v.1 i (x 0)) ≤ Q ^ c v.1 i := by
    intro v hv i
    have h := (hx 0).1.1 v hv i
    rwa [abs_of_pos hQ0] at h
  have hkey := hW Q t hQ1 ht (x 0) hne hinf hfin (hx 0).1.2
  have hpow : t ^ finrank ℚ K < Q ^ (-(B * finrank ℚ K)) := by
    have h1 : t ^ finrank ℚ K < (Q ^ (-B)) ^ finrank ℚ K :=
      pow_lt_pow_left₀ hcon ht.le hd.ne'
    rwa [← Real.rpow_natCast (Q ^ (-B)) (finrank ℚ K), ← Real.rpow_mul hQ0.le,
      show -B * (finrank ℚ K : ℝ) = -(B * finrank ℚ K) by ring] at h1
  have hQW : (0 : ℝ) < Q ^ W := Real.rpow_pos_of_pos hQ0 _
  have hchain : A * t ^ finrank ℚ K * Q ^ W < A * Q ^ (W - B * finrank ℚ K) := by
    have heq : A * Q ^ (-(B * (finrank ℚ K : ℝ))) * Q ^ W = A * Q ^ (W - B * finrank ℚ K) := by
      rw [mul_assoc, ← Real.rpow_add hQ0]
      ring_nf
    have h1 : A * t ^ finrank ℚ K < A * Q ^ (-(B * (finrank ℚ K : ℝ))) :=
      mul_lt_mul_of_pos_left hpow hA
    have h2 := mul_lt_mul_of_pos_right h1 hQW
    rwa [heq] at h2
  linarith

theorem _root_.Real.rpow_le_of_pow_le_rpow {x Q a b : ℝ} {d : ℕ} (hQ : 1 ≤ Q) (hx : 0 ≤ x)
    (hd : d ≠ 0) (h : x ^ d ≤ Q ^ a) (hab : a ≤ b * d) : x ≤ Q ^ b := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le one_pos hQ
  have h1 : Q ^ a ≤ (Q ^ b) ^ d := by
    rw [← Real.rpow_natCast (Q ^ b) d, ← Real.rpow_mul hQ0.le]
    exact Real.rpow_le_rpow_of_exponent_le hQ hab
  exact (pow_le_pow_iff_left₀ hx (Real.rpow_nonneg hQ0.le b) hd).1 (h.trans h1)

open scoped Classical in
/-- **The minima of an approximation domain lie between two powers of `Q`** (Bombieri–Gubler,
Step IX): the first is at least `Q ^ (-B)` because a nonzero point has height at least `1`, and
the last is then at most `Q ^ B` by Minkowski's second theorem over `K` from above. -/
theorem exists_pos_forall_rpow_le_successiveMinimum_le
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∃ Q₁ : ℝ, 1 ≤ Q₁ ∧ ∀ Q : ℝ, Q₁ ≤ Q → ∀ j < Fintype.card ι,
      Q ^ (-B) ≤ successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) j ∧
        successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) j ≤ Q ^ B := by
  obtain ⟨B₀, hB₀, Q₁, hQ₁, hlow⟩ := exists_pos_forall_rpow_le_successiveMinimum hLInf hLFin c
  set N := Fintype.card ι with hN
  set d := finrank ℚ K with hd
  have hd0 : 0 < d := finrank_pos
  have hN0 : 0 < N := Fintype.card_pos
  set A₂ : ℝ := 2 ^ (d * N) *
    (∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ N) / approxConst Sfin L with hA₂
  set m : ℕ := N - 1 with hm
  have hmN : m + 1 = N := by omega
  set W : ℝ := approxWeight Sfin c with hW
  set B : ℝ := max B₀ ((|W| + B₀ * m * d + 1) / d) with hBdef
  have hB : 0 < B := lt_of_lt_of_le hB₀ (le_max_left _ _)
  refine ⟨B, hB, max Q₁ (max A₂ 1), le_trans hQ₁ (le_max_left _ _), fun Q hQ j hj ↦ ?_⟩
  have hQ1 : (1 : ℝ) ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  have hQA₂ : A₂ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQQ₁ : Q₁ ≤ Q := le_trans (le_max_left _ _) hQ
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le one_pos hQ1
  have hDt : DiscreteTopology (approxLattice Sfin L c Q) :=
    discreteTopology_approxLattice hLFin c hQ0.ne'
  have : DiscreteTopology (approxModule Sfin L c Q).mixedImage := hDt
  have hZ : IsZLattice ℝ (approxLattice Sfin L c Q) := isZLattice_approxLattice hLFin c hQ0.ne'
  have : IsZLattice ℝ (approxModule Sfin L c Q).mixedImage := hZ
  set μ : ℕ → ℝ := successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) with hμ
  have hmono : ∀ i j : ℕ, i ≤ j → j < N → μ i ≤ μ j := fun i j hij hjN ↦
    successiveMinimum_le_of_le _ (convex_approxBody L c Q) (fun z hz ↦ neg_mem_approxBody hz)
      ⟨0, mem_interior_iff_mem_nhds.2 (approxBody_mem_nhds_zero L c hQ0)⟩
      (isBounded_approxBody hLInf c Q) hij hjN
  have hlow0 : Q ^ (-B₀) ≤ μ 0 := hlow Q hQQ₁
  have hlowj : ∀ i, i < N → Q ^ (-B₀) ≤ μ i := fun i hi ↦ le_trans hlow0 (hmono 0 i (by omega) hi)
  have hnneg : ∀ i, 0 ≤ μ i := fun i ↦ successiveMinimum_nonneg _ _ _
  have hupper : μ m ≤ Q ^ B := by
    have hprod := prod_successiveMinimum_approx_le hLInf hLFin c hQ0
    have hsplit : ∏ i ∈ Finset.range N, μ i = (∏ i ∈ Finset.range m, μ i) * μ m := by
      conv_lhs => rw [← hmN]
      rw [Finset.prod_range_succ]
    have hge : (Q ^ (-B₀)) ^ m ≤ ∏ i ∈ Finset.range m, μ i := by
      have := Finset.prod_le_prod₀ (s := Finset.range m) (f := fun _ ↦ Q ^ (-B₀)) (g := μ)
        (fun i _ ↦ Real.rpow_nonneg hQ0.le _)
        (fun i hi ↦ hlowj i (by rw [Finset.mem_range] at hi; omega))
      rwa [Finset.prod_const, Finset.card_range] at this
    have hmid : (Q ^ (-B₀)) ^ m * μ m ≤ ∏ i ∈ Finset.range N, μ i := by
      rw [hsplit]
      exact mul_le_mul_of_nonneg_right hge (hnneg _)
    have hpowle : ((Q ^ (-B₀)) ^ m * μ m) ^ d ≤ A₂ * Q ^ (-W) :=
      le_trans (pow_le_pow_left₀
        (mul_nonneg (pow_nonneg (Real.rpow_nonneg hQ0.le _) _) (hnneg _)) hmid d) hprod
    have hQpow : ((Q ^ (-B₀)) ^ m) ^ d = Q ^ (-(B₀ * m * d)) := by
      rw [← Real.rpow_natCast (Q ^ (-B₀)) m, ← Real.rpow_mul hQ0.le,
        ← Real.rpow_natCast (Q ^ (-B₀ * (m : ℝ))) d, ← Real.rpow_mul hQ0.le]
      ring_nf
    have h1 : Q ^ (-(B₀ * (m : ℝ) * d)) * μ m ^ d ≤ A₂ * Q ^ (-W) := by
      rw [← hQpow, ← mul_pow]
      exact hpowle
    have h2 : A₂ * Q ^ (-W) ≤ Q ^ (1 + |W|) := by
      have hle : Q ^ (-W) ≤ Q ^ |W| := Real.rpow_le_rpow_of_exponent_le hQ1 (neg_le_abs _)
      have h := mul_le_mul hQA₂ hle (Real.rpow_nonneg hQ0.le _) hQ0.le
      rwa [show Q * Q ^ |W| = Q ^ (1 + |W|) by rw [Real.rpow_add hQ0, Real.rpow_one]] at h
    have hkey : μ m ^ d ≤ Q ^ (|W| + B₀ * m * d + 1) := by
      have h4 : μ m ^ d = Q ^ (B₀ * (m : ℝ) * d) * (Q ^ (-(B₀ * (m : ℝ) * d)) * μ m ^ d) := by
        rw [← mul_assoc, ← Real.rpow_add hQ0, add_neg_cancel, Real.rpow_zero, one_mul]
      rw [h4]
      have h5 : Q ^ (B₀ * (m : ℝ) * d) * (Q ^ (-(B₀ * (m : ℝ) * d)) * μ m ^ d)
          ≤ Q ^ (B₀ * (m : ℝ) * d) * Q ^ (1 + |W|) :=
        mul_le_mul_of_nonneg_left (le_trans h1 h2) (Real.rpow_nonneg hQ0.le _)
      refine le_trans h5 (le_of_eq ?_)
      rw [← Real.rpow_add hQ0]
      ring_nf
    refine Real.rpow_le_of_pow_le_rpow hQ1 (hnneg _) hd0.ne' hkey ?_
    have hle : (|W| + B₀ * m * d + 1) / d ≤ B := le_max_right _ _
    rw [div_le_iff₀ (by positivity)] at hle
    linarith
  refine ⟨le_trans (Real.rpow_le_rpow_of_exponent_le hQ1 ?_) (hlowj j hj),
    le_trans (hmono j m (by omega) (by omega)) hupper⟩
  have : B₀ ≤ B := le_max_left _ _
  linarith

end NumberField
