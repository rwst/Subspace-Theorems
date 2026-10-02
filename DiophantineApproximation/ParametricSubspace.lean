/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.WedgeExponentBound
public import DiophantineApproximation.WedgeRecovery
public import DiophantineApproximation.ExponentGrid
public import DiophantineApproximation.PenultimateMinimum

/-!
# The parametric Subspace Theorem

For a number field `K`, forms `L v i : Module.Dual K (Kⁱ)` linearly independent at every infinite
place and at every place of a finite set `Sfin`, and exponents `c` of **negative weight**, there
are a finite set `T` of proper subspaces of `Kⁱ` and a level `Q₀` such that every approximation
domain `approxDomain Sfin L c Q` with `Q ≥ Q₀` is contained in a member of `T`. This is
Bombieri–Gubler's 7.5.32 — Steps VIII and IX of the proof of the Subspace Theorem — and it is the
statement the quantitative theory strengthens by counting `T`.

The route, for a level `Q` at which the domain has rank `R`:

* `R = 0`. The domain spans `⊥`, which is proper.
* `1 ≤ R < #ι`. Layer 4.3 makes the rank less than `#ι` at every large level. The choice (7.41) of
  Layer 4.5 gives a `k` in `[R, #ι)` at which the jump of the minima is large; Evertse's lemma
  (Layer 4.4), applied to vectors realizing the minima, produces vectors `y` whose wedges of the
  `p`-subsets meeting `y 0, …, y (k - 1)`, `k + p = #ι`, lie in a domain in `⋀^p Kⁱ` whose
  exponents `wedgeExponent` move with `Q` (Layer 4.5). Those exponents stay in a box
  (`WedgeExponentBound.lean`), so rounding them up to a grid of mesh `γ`
  (`ExponentGrid.lean`) leaves finitely many systems of exponents, each still of negative weight;
  the wedge domain is contained in the domain of the rounded system, whose rank is at most
  `M - 1 = #(⋀^p) - 1` at every large level by Layer 4.3 and is therefore **exactly** `M - 1`,
  since the wedges already span a hyperplane. Layer 5.6 in `⋀^p Kⁱ` makes those spans finite in
  number, and Lemma 7.5.33, read as the function `recoverSpan` (`WedgeRecovery.lean`), recovers
  from each the span of `y 0, …, y (k - 1)` — which contains `V(Q)` and is proper because
  `k < #ι`.

## Main results

* `NumberField.approxAbsWeight_gridExponent_le`: the grid systems have uniformly bounded
  absolute weight, so Layer 5.6's chain length and ratio are uniform over them.
* `NumberField.approxAbsWeight_sum_le`: the sums over `p`-subsets have absolute weight at most
  `#(⋀^p)` times that of the exponents.
* `NumberField.exists_forall_mem_interval_approxSpan_le`: along one choice of `k`, the spans of
  the domains lie in a bounded number of proper subspaces, except at levels in a bounded number
  of intervals.
* `NumberField.exists_forall_mem_interval_approxDomain`: **Layer 6.1 as an interval result**,
  with the counts `parametricSubspaceCount`, `parametricIntervalCount` and the ratio
  `parametricRatio` closed forms in `#ι`, `[K : ℚ]`, the number of places, `ε` and `A`.
* `NumberField.exists_finset_submodule_forall_approxDomain_subset`: **the milestone**, read off
  the interval result.

## Main definitions

* `NumberField.parametricMinimaExp`, `parametricDelta`, `parametricMesh`, `parametricBox`,
  `parametricGridCount`, `parametricWedgeAbsWeight`: the exponent `B` of the minima, the weight
  margin `δ`, the mesh `γ`, the box `m`, the number of grids and the absolute-weight bound of the
  grid systems.
* `NumberField.parametricChainLength`, `parametricStepRatio`: Layer 5.6's number of intervals and
  their ratio for one grid system in `⋀^p`. The ratio, the totals below and the thresholds take
  the parameters of the generalized Roth lemma (`NumberField.RothParams`) that Layer 5.6 runs
  with, and the interval results take the lemma itself (`NumberField.SubspaceRoth`); the
  milestone uses Bombieri–Gubler's.
* `NumberField.parametricIntervalCount`, `parametricSubspaceCount`, `parametricRatio`: the totals
  over the classes `(k, g)`.
* `NumberField.parametricStepThreshold`, `parametricThreshold`: the threshold `Q₀`, on the scale of
  `log Q`, as a formula in the forms: `c_K`, `approxConst`, the inverse matrices, the Plücker
  constant and Layer 5.6's `penultimateThreshold` for the wedge forms.

## Implementation notes

⚠ **The rank `#ι - 1` needs no separate argument.** Bombieri–Gubler treat the penultimate case by
Theorem 7.5.13 directly. Here it is the case `k = #ι - 1`, `p = 1` of the same construction: the
wedge domain in `⋀^1 Kⁱ` is the original domain re-indexed by the one-element subsets, with the
exponents shifted by the minima, and Layer 5.6 applies to it exactly as it does in higher `p`. One
mechanism covers every rank from `1` to `#ι - 1`.

⚠ **No pigeonhole and no subsequence.** The book argues along an unbounded family of levels and
extracts a subfamily on which `k` and the rounded exponents are constant. That is not needed: the
rounding is a *function* of the level, its range is finite, and the finite set of subspaces is the
union over that range. What the book's pigeonhole buys — finitely many classes — is bought here by
the box bound alone.

⚠ **The finite set is not the set of spans.** `T` collects subspaces *containing* the domains, not
the spans `V(Q)` themselves: the wedge route recovers the span of the first `k` minimal vectors,
which contains `V(Q)` and is what Lemma 7.5.33 determines. Whether the `V(Q)` themselves are
finite in number is not claimed and is not needed by Layer 6.2.

⚠ **The interval result is summed over the classes.** Each class `(k, g)` contributes Layer 5.6
as an interval result in `⋀^p`, whose exceptional subspaces are pulled back through
`recoverSpan`. The number of classes is bounded because the box is explicit: the minima exponent
is `B = N (A + 1) / d`. The ratios differ between the `p`, and their sum bounds each of them.

⚠ **The order on `ι` is internal.** The milestone is stated without `[LinearOrder ι]`: the wedge
construction needs an order to index the Plücker coordinates, but the statement does not mention
one, so the proof chooses one by transport from `Fin (#ι)`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
7.5.30–7.5.32.

J.-H. Evertse and H. P. Schlickewei, "A quantitative version of the absolute subspace theorem",
*Journal für die reine und angewandte Mathematik* **548** (2002), 21–127, for the parametric
formulation.

This is Layer 6.1 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Filter Finset Module NumberField NumberField.mixedEmbedding exteriorPower

universe u

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type u} [Fintype ι]
  {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}

omit [Fintype ι] in
/-- **The grid systems have uniformly bounded absolute weight**: rounding at the infinite places by
at most `m` steps of mesh `γ` raises the weight of the absolute values of the exponents by at most
`γ m #ρ [K : ℚ]`. So every class of the parametric Subspace Theorem shares one bound `A` in
`NumberField.exists_forall_not_chain`, and with it one chain length and one ratio. -/
theorem approxAbsWeight_gridExponent_le {ρ : Type*} [Fintype ρ] (Sfin : Finset (FinitePlace K))
    (cT : AbsoluteValue K ℝ → ρ → ℝ) {γ : ℝ} (hγ : 0 ≤ γ) {g : InfinitePlace K → ρ → ℤ} {m : ℤ}
    (hg : ∀ w T, |g w T| ≤ m) :
    approxAbsWeight Sfin (gridExponent cT γ g)
      ≤ approxAbsWeight Sfin cT + γ * m * (Fintype.card ρ * finrank ℚ K) := by
  classical
  have hfin : ∀ v ∈ Sfin, ∀ i, gridExponent cT γ g v.1 i = cT v.1 i := fun v _ i ↦
    gridExponent_of_forall_ne cT g (fun w hcc ↦ InfinitePlace.not_isNonarchimedean w
      (by rw [hcc]; exact fun a b ↦ v.add_le a b)) i
  have hinf : ∀ (w : InfinitePlace K) (i : ρ),
      |gridExponent cT γ g w.1 i| ≤ |cT w.1 i| + γ * m := fun w i ↦ by
    rw [gridExponent_infinitePlace]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul, abs_of_nonneg hγ]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hg w i) hγ
  have hle : ∑ v : InfinitePlace K, (v.mult : ℝ) * ∑ i, |gridExponent cT γ g v.1 i|
      ≤ ∑ v : InfinitePlace K, (v.mult : ℝ) * ∑ i, (|cT v.1 i| + γ * m) :=
    Finset.sum_le_sum fun v _ ↦ mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ ↦ hinf v i) (Nat.cast_nonneg _)
  have heq : ∑ v : InfinitePlace K, (v.mult : ℝ) * ∑ i, (|cT v.1 i| + γ * m)
      = ∑ v : InfinitePlace K, (v.mult : ℝ) * ∑ i, |cT v.1 i|
        + γ * m * (Fintype.card ρ * finrank ℚ K) := by
    have hsum : ∑ v : InfinitePlace K, (v.mult : ℝ) = finrank ℚ K := by
      exact_mod_cast InfinitePlace.sum_mult_eq
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_add]
    rw [← hsum, Finset.mul_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun v _ ↦ by ring
  have hfin' : ∑ v ∈ Sfin, ∑ i, |gridExponent cT γ g v.1 i| = ∑ v ∈ Sfin, ∑ i, |cT v.1 i| :=
    Finset.sum_congr rfl fun v hv ↦ Finset.sum_congr rfl fun i _ ↦ by rw [hfin v hv i]
  rw [approxAbsWeight, approxAbsWeight, hfin']
  linarith

/-- **The sums over `p`-subsets have absolute weight at most `#(⋀^p)` times that of the
exponents**: each `|∑_{t ∈ T} c v t|` is at most `∑_i |c v i|`. -/
theorem approxAbsWeight_sum_le (Sfin : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (p : ℕ) :
    approxAbsWeight Sfin (fun v (T : Set.powersetCard ι p) ↦ ∑ t ∈ (T : Finset ι), c v t)
      ≤ Fintype.card (Set.powersetCard ι p) * approxAbsWeight Sfin c := by
  have hv : ∀ v : AbsoluteValue K ℝ,
      ∑ T : Set.powersetCard ι p, |∑ t ∈ (T : Finset ι), c v t|
        ≤ Fintype.card (Set.powersetCard ι p) * ∑ i, |c v i| := by
    intro v
    calc ∑ T : Set.powersetCard ι p, |∑ t ∈ (T : Finset ι), c v t|
        ≤ ∑ _T : Set.powersetCard ι p, ∑ i, |c v i| :=
          Finset.sum_le_sum fun T _ ↦ (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun i _ _ ↦ abs_nonneg _)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [approxAbsWeight, approxAbsWeight, mul_add, Finset.mul_sum, Finset.mul_sum]
  refine add_le_add (Finset.sum_le_sum fun w _ ↦ ?_) (Finset.sum_le_sum fun v _ ↦ hv v.1)
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hv w.1) (Nat.cast_nonneg _)

/-! ### The parameters

Everything below is a function of `N = #ι`, `d = [K : ℚ]`, the number `r` of infinite places,
`s = r + |Sfin|`, the margin `ε` of the weight and a bound `A` on the absolute weight. The index
`p` is the size of the subsets, so that the wedge domains live in `⋀^p Kⁱ` of dimension
`binom(N, p)`. -/

/-- **The exponent of the minima**, `B = N (A + 1) / d`: for exponents of absolute weight at most
`A`, every minimum of a domain lies between `Q ^ (-B)` and `Q ^ B` at every large level
(`NumberField.exists_pos_forall_rpow_le_successiveMinimum_le`). -/
noncomputable def parametricMinimaExp (N d : ℕ) (A : ℝ) : ℝ :=
  N * (A + 1) / d

/-- **The weight margin of the wedge domains**, `δ = ε / (2 N ^ 2)`. -/
noncomputable def parametricDelta (N : ℕ) (ε : ℝ) : ℝ :=
  ε / (2 * (N : ℝ) ^ 2)

/-- **The mesh of the grid** in `⋀^p`, `γ = δ / (2 d binom(N, p))`. -/
noncomputable def parametricMesh (N d p : ℕ) (ε : ℝ) : ℝ :=
  parametricDelta N ε / (2 * ((d : ℝ) * (N.choose p : ℝ)))

/-- **The size of the box of grids**, `m = ⌈(1 + B N + 2 B) / γ⌉`. -/
noncomputable def parametricBox (N d p : ℕ) (ε A : ℝ) : ℤ :=
  ⌈(1 + parametricMinimaExp N d A * N + 2 * parametricMinimaExp N d A)
    / parametricMesh N d p ε⌉

/-- **The number of grids**, `(2 m + 1) ^ (r binom(N, p))`. -/
noncomputable def parametricGridCount (N d r p : ℕ) (ε A : ℝ) : ℕ :=
  (2 * parametricBox N d p ε A + 1).toNat ^ (r * N.choose p)

/-- **A bound for the absolute weight of every grid system**,
`binom(N, p) A + γ m binom(N, p) d`. -/
noncomputable def parametricWedgeAbsWeight (N d p : ℕ) (ε A : ℝ) : ℝ :=
  N.choose p * A + parametricMesh N d p ε * parametricBox N d p ε A * (N.choose p * d)

/-- **The number of intervals of one grid system**: Layer 5.6's chain length in `⋀^p`. -/
noncomputable def parametricChainLength (N d s p : ℕ) (ε A : ℝ) : ℕ :=
  subspaceChainLength (N.choose p - 1) s (parametricDelta N ε) (parametricWedgeAbsWeight N d p ε A)

/-- **The ratio of the intervals of one grid system**, `4 σ⁻¹` for the ratio `σ` of the Roth
lemma `R` that Layer 5.6 runs with in `⋀^p`. -/
noncomputable def parametricStepRatio (R : RothParams) (N d s p : ℕ) (ε A : ℝ) : ℝ :=
  4 * (R.ratio (N.choose p - 1) s (parametricDelta N ε)
    (parametricWedgeAbsWeight N d p ε A))⁻¹

/-- **The number of intervals of the parametric Subspace Theorem**: the sum over `p < N` of the
number of grids times the number of intervals of each. -/
noncomputable def parametricIntervalCount (N d r s : ℕ) (ε A : ℝ) : ℕ :=
  ∑ p ∈ Finset.range N, parametricGridCount N d r p ε A * parametricChainLength N d s p ε A

/-- **The number of subspaces of the parametric Subspace Theorem**: `⊥`, and for every `p < N`
and every grid at most `2 ^ (binom(N, p) s)` subspaces. -/
noncomputable def parametricSubspaceCount (N d r s : ℕ) (ε A : ℝ) : ℕ :=
  1 + ∑ p ∈ Finset.range N, parametricGridCount N d r p ε A * 2 ^ (N.choose p * s)

/-- **The ratio of the intervals of the parametric Subspace Theorem**: the sum over `p < N` of
the ratios of the grid systems, which bounds each of them. -/
noncomputable def parametricRatio (R : RothParams) (N d s : ℕ) (ε A : ℝ) : ℝ :=
  ∑ p ∈ Finset.range N, parametricStepRatio R N d s p ε A

theorem parametricDelta_pos {N : ℕ} {ε : ℝ} (hN : 0 < N) (hε : 0 < ε) :
    0 < parametricDelta N ε := by
  rw [parametricDelta]
  positivity

theorem parametricMesh_nonneg (N d p : ℕ) {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ parametricMesh N d p ε := by
  rw [parametricMesh, parametricDelta]
  positivity

theorem parametricWedgeAbsWeight_nonneg (N d p : ℕ) {ε A : ℝ} (hε : 0 ≤ ε) (hA : 0 ≤ A) :
    0 ≤ parametricWedgeAbsWeight N d p ε A := by
  have hγ := parametricMesh_nonneg N d p hε
  have hm0 : 0 ≤ parametricBox N d p ε A := by
    refine Int.ceil_nonneg (div_nonneg ?_ hγ)
    rw [parametricMinimaExp]
    positivity
  have hm : (0 : ℝ) ≤ parametricBox N d p ε A := by exact_mod_cast hm0
  rw [parametricWedgeAbsWeight]
  positivity

theorem parametricStepRatio_pos (R : RothParams) {N : ℕ} (d s p : ℕ) {ε A : ℝ} (hN : 0 < N)
    (hε : 0 < ε) (hA : 0 ≤ A) : 0 < parametricStepRatio R N d s p ε A :=
  mul_pos four_pos (inv_pos.2 (R.ratio_pos (parametricDelta_pos hN hε)
    (parametricWedgeAbsWeight_nonneg N d p hε.le hA)))

section Wedge

variable [LinearOrder ι] [Nonempty ι]

open scoped Classical in
/-- **The threshold of Layer 6.1 along one size `p` of subsets**, on the scale of `log Q`: the
largest of `1`, the logarithms of the level `minimaThreshold` of the minima bounds, of `2`, of the
Plücker constant and of the rank threshold of the wedge forms at weight `-δ / 2`, of
`2 log (wedgeWeightConst) / ε`, and of the threshold `penultimateThreshold` of Layer 5.6 for the
wedge forms. -/
noncomputable def parametricStepThreshold (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (R : RothParams) (ε A : ℝ) (p : ℕ) : ℝ :=
  letI : LinearOrder (Set.powersetCard ι p) :=
    LinearOrder.lift' (Fintype.equivFin _) (Equiv.injective _)
  max 1 (max (Real.log (minimaThreshold Sfin L))
    (max (max (Real.log 2)
        (2 * Real.log (wedgeWeightConst Sfin L (pluckerConst K (Fintype.card ι)) p) / ε))
      (max (Real.log (pluckerConst K (Fintype.card ι)))
        (max (Real.log (rankThreshold Sfin (fun v ↦ wedgeForms (L v) p)
            (parametricDelta (Fintype.card ι) ε / 2)))
          (penultimateThreshold Sfin (fun v ↦ wedgeForms (L v) p) R
            ((Fintype.card ι).choose p - 1) (parametricDelta (Fintype.card ι) ε)
            (parametricWedgeAbsWeight (Fintype.card ι) (finrank ℚ K) p ε A))))))

open scoped Classical in
/-- **The spans of the domains of a fixed rank, along one choice of `k`, as an interval result**
(Bombieri–Gubler, 7.5.32, Steps VIII and IX, with Layer 5.6 as an interval result). There are at
most `#grids · 2 ^ (binom(N, p) s)` proper subspaces `𝒮` and a level `Q₀ > 0` such that for every
`Q₀' ≥ Q₀`, at the levels `Q` with `log Q ≥ Q₀'` whose rank `R` and jump at `k` are as in (7.41),
either `V(Q)` lies in a member of `𝒮`, or `log Q` lies in one of at most
`#grids · parametricChainLength` intervals `[t, ρ t)` with `t ≥ Q₀'`,
`ρ = parametricStepRatio`. -/
theorem exists_forall_mem_interval_approxSpan_le (R : SubspaceRoth.{u} K)
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {c : AbsoluteValue K ℝ → ι → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hc : approxWeight Sfin c ≤ -ε) {A : ℝ}
    (hA : approxAbsWeight Sfin c ≤ A) {k p : ℕ} (hkp : k + p = Fintype.card ι) (hk : 0 < k)
    (hp : 0 < p) :
    ∃ 𝒮 : Finset (Submodule K (ι → K)),
      #𝒮 ≤ parametricGridCount (Fintype.card ι) (finrank ℚ K) (Fintype.card (InfinitePlace K))
          p ε A * 2 ^ ((Fintype.card ι).choose p * (Fintype.card (InfinitePlace K) + #Sfin)) ∧
      (∀ Z ∈ 𝒮, Z ≠ ⊤) ∧ ∃ Q₀ : ℝ, 0 < Q₀ ∧
      Q₀ = parametricStepThreshold Sfin L R.toRothParams ε A p ∧
      ∀ Q₀' : ℝ, Q₀ ≤ Q₀' →
      ∃ 𝒯 : Finset ℝ, #𝒯 ≤ parametricGridCount (Fintype.card ι) (finrank ℚ K)
            (Fintype.card (InfinitePlace K)) p ε A
          * parametricChainLength (Fintype.card ι) (finrank ℚ K)
            (Fintype.card (InfinitePlace K) + #Sfin) p ε A ∧
        (∀ t ∈ 𝒯, Q₀' ≤ t) ∧
        ∀ Q : ℝ, 1 < Q → Q₀' ≤ Real.log Q →
        ∀ r : ℕ, finrank K (approxSpan Sfin L c Q) = r → 1 ≤ r → r ≤ k →
          (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) (k - 1) /
              successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) k) ^
                (Fintype.card ι - r)
            ≤ (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)
                (Fintype.card ι - 1))⁻¹ →
          (∃ Z ∈ 𝒮, approxSpan Sfin L c Q ≤ Z) ∨
            ∃ t ∈ 𝒯, t ≤ Real.log Q ∧ Real.log Q < parametricStepRatio R.toRothParams
              (Fintype.card ι)
              (finrank ℚ K) (Fintype.card (InfinitePlace K) + #Sfin) p ε A * t := by
  set N := Fintype.card ι with hN
  set d := finrank ℚ K with hd
  set r := Fintype.card (InfinitePlace K) with hr
  set s := r + #Sfin with hs
  set M := Fintype.card (Set.powersetCard ι p) with hM
  have hMch : M = N.choose p := by
    rw [hM, Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_eq_fintype_card]
  have hNpos : 0 < N := Fintype.card_pos
  have hkN : k < N := by omega
  have hpN : p ≤ N := by omega
  have hd0 : 0 < d := finrank_pos
  -- the wedge forms and the reference exponents
  set L' : AbsoluteValue K ℝ → Set.powersetCard ι p → Dual K (Set.powersetCard ι p → K) :=
    fun v ↦ wedgeForms (L v) p with hL'
  have hL'Inf : ∀ w : InfinitePlace K, LinearIndependent K (L' w.1) :=
    fun w ↦ linearIndependent_wedgeForms (hLInf w) p
  have hL'Fin : ∀ v ∈ Sfin, LinearIndependent K (L' v.1) :=
    fun v hv ↦ linearIndependent_wedgeForms (hLFin v hv) p
  set cT : AbsoluteValue K ℝ → Set.powersetCard ι p → ℝ :=
    fun v T ↦ ∑ t ∈ (T : Finset ι), c v t with hcT
  -- the constants
  obtain ⟨C, hC, hCeq, hplucker⟩ := exists_plucker_mem_approxDomain_wedgeForms K ι
  set B : ℝ := parametricMinimaExp N d A with hBdef
  obtain ⟨B₀, hB₀, hB₀le, Q₁, hQ₁, hQ₁eq, hminima₀⟩ :=
    exists_pos_forall_rpow_le_successiveMinimum_le hLInf hLFin c
  have hB₀B : B₀ ≤ B := by
    refine hB₀le.trans ?_
    rw [hBdef, parametricMinimaExp]
    rw [approxAbsWeight] at hA
    gcongr
  have hB : 0 < B := hB₀.trans_le hB₀B
  have hminima : ∀ Q : ℝ, Q₁ ≤ Q → ∀ j < N,
      Q ^ (-B) ≤ successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) j ∧
        successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) j ≤ Q ^ B := by
    intro Q hQ j hj
    have hQ1 : 1 ≤ Q := hQ₁.trans hQ
    obtain ⟨h1, h2⟩ := hminima₀ Q hQ j hj
    exact ⟨(Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)).trans h1,
      h2.trans (Real.rpow_le_rpow_of_exponent_le hQ1 hB₀B)⟩
  have hcneg : approxWeight Sfin c < 0 := by linarith
  obtain ⟨Q₂, hQ₂1, hQ₂eq, hwt⟩ :=
    exists_forall_approxWeight_wedgeExponent_le hLInf hLFin hcneg hC hkp hp
  have hM2 : 2 ≤ M := by
    have h1 : Nontrivial (Set.powersetCard ι p) := by
      rw [← not_subsingleton_iff_nontrivial, Set.powersetCard.subsingleton_iff]
      push Not
      exact ⟨by omega, by rw [Nat.card_eq_fintype_card]; omega⟩
    exact Fintype.one_lt_card
  have hMpos : 0 < M := by omega
  set δ : ℝ := parametricDelta N ε with hδ
  have hδ0 : 0 < δ := parametricDelta_pos hNpos hε
  have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
  have hM0' : (0 : ℝ) < M := by exact_mod_cast hMpos
  set γ : ℝ := parametricMesh N d p ε with hγ
  have hγeq : γ = δ / (2 * ((d : ℝ) * (M : ℝ))) := by rw [hγ, parametricMesh, hMch]
  have hγ0 : 0 < γ := by rw [hγeq]; positivity
  set G : ℝ := 1 + B * N + 2 * B with hG
  set m : ℤ := parametricBox N d p ε A with hm
  -- the finite pool of grids
  set pool : Set (InfinitePlace K → Set.powersetCard ι p → ℤ) :=
    {g | (∀ w T, |g w T| ≤ m) ∧ approxWeight Sfin (gridExponent cT γ g) ≤ -δ / 2} with hpool
  have hpoolfin : pool.Finite :=
    Set.Finite.subset (finite_setOf_abs_le (Set.powersetCard ι p) m) fun g hg ↦ hg.1
  set P := hpoolfin.toFinset with hP
  have hpoolcard : #P ≤ parametricGridCount N d r p ε A := by
    rw [hP, ← Set.ncard_eq_toFinset_card pool hpoolfin]
    refine (Set.ncard_le_ncard (fun g hg ↦ hg.1) (finite_setOf_abs_le _ m)).trans ?_
    refine (ncard_setOf_abs_le_le (K := K) (Set.powersetCard ι p) m).trans (le_of_eq ?_)
    rw [parametricGridCount, ← hMch]
  -- every grid system has absolute weight at most `A'`
  set A' : ℝ := parametricWedgeAbsWeight N d p ε A with hA'
  have hAW' : ∀ g ∈ pool, approxAbsWeight Sfin (gridExponent cT γ g) ≤ A' := by
    intro g hg
    refine (approxAbsWeight_gridExponent_le Sfin cT hγ0.le hg.1).trans ?_
    have h1 := approxAbsWeight_sum_le Sfin c p
    have h2 : (M : ℝ) * approxAbsWeight Sfin c ≤ M * A := mul_le_mul_of_nonneg_left hA hM0'.le
    rw [hA', parametricWedgeAbsWeight, ← hMch]
    linarith
  -- for every grid, Layer 5.6 as an interval result in `⋀^p`
  have hne : Nonempty (Set.powersetCard ι p) := Fintype.card_pos_iff.1 hMpos
  let _ : LinearOrder (Set.powersetCard ι p) :=
    LinearOrder.lift' (Fintype.equivFin _) (Equiv.injective _)
  have hM1 : 1 ≤ M - 1 := by omega
  have hcardM : Fintype.card (Set.powersetCard ι p) = M - 1 + 1 := by omega
  set Q56 : ℝ := penultimateThreshold Sfin L' R.toRothParams (M - 1) δ A' with hQ56
  have h56 : ∀ g : InfinitePlace K → Set.powersetCard ι p → ℤ,
      ∃ 𝒲 : Set (Submodule K (Set.powersetCard ι p → K)), 𝒲.Finite ∧
        𝒲.ncard ≤ 2 ^ (M * s) ∧ ∀ Q₀' : ℝ, Q56 ≤ Q₀' →
          ∃ 𝒯 : Finset ℝ, #𝒯 ≤ parametricChainLength N d s p ε A ∧ (∀ t ∈ 𝒯, Q₀' ≤ t) ∧
          (g ∈ pool → ∀ Q : ℝ, 1 < Q → Q₀' ≤ Real.log Q →
            finrank K (approxSpan Sfin L' (gridExponent cT γ g) Q) = M - 1 →
            approxSpan Sfin L' (gridExponent cT γ g) Q ∉ 𝒲 →
            ∃ t ∈ 𝒯, t ≤ Real.log Q ∧ Real.log Q
              < parametricStepRatio R.toRothParams N d s p ε A * t) := by
    intro g
    by_cases hg : g ∈ pool
    · obtain ⟨𝒲, Q₀, hfin, hcard, -, hQ₀eq, hint⟩ :=
        exists_forall_mem_interval_approxSpan R hM1 hcardM hL'Inf hL'Fin hδ0 hg.2 (hAW' g hg)
      refine ⟨𝒲, hfin, ?_, fun Q₀' hQ₀' ↦ ?_⟩
      · rwa [Nat.sub_add_cancel (by omega : 1 ≤ M)] at hcard
      obtain ⟨j, hj, t, ht, hint'⟩ := hint Q₀' (hQ₀eq ▸ hQ₀')
      refine ⟨Finset.univ.image t, ?_, ?_, fun _ Q hQ1 hQ hrank hnot ↦ ?_⟩
      · refine Finset.card_image_le.trans ?_
        rw [Finset.card_univ, Fintype.card_fin, parametricChainLength, ← hMch]
        exact hj
      · simpa using ht
      · obtain ⟨i, hi1, hi2⟩ := hint' Q hQ1 hQ hrank hnot
        refine ⟨t i, Finset.mem_image_of_mem _ (Finset.mem_univ i), hi1, ?_⟩
        rwa [parametricStepRatio, ← hMch]
    · exact ⟨∅, Set.finite_empty, by simp,
        fun _ _ ↦ ⟨∅, by simp, by simp, fun h ↦ absurd h hg⟩⟩
  choose 𝒲 h𝒲fin h𝒲card 𝒯g h𝒯gcard h𝒯gge h𝒯gint using h56
  -- the candidate subspaces
  set 𝒮 : Finset (Submodule K (ι → K)) :=
    (P.biUnion fun g ↦ (h𝒲fin g).toFinset.image (recoverSpan p)).filter (· ≠ ⊤) with h𝒮
  have h𝒮card : #𝒮 ≤ parametricGridCount N d r p ε A * 2 ^ (N.choose p * s) := by
    refine (Finset.card_filter_le _ _).trans (Finset.card_biUnion_le.trans ?_)
    refine (Finset.sum_le_card_nsmul P _ (2 ^ (M * s)) fun g _ ↦ ?_).trans ?_
    · refine Finset.card_image_le.trans ?_
      rw [← Set.ncard_eq_toFinset_card _ (h𝒲fin g)]
      exact h𝒲card g
    · rw [smul_eq_mul, ← hMch]
      exact Nat.mul_le_mul_right _ hpoolcard
  -- the thresholds, on the scale of `log Q`
  have hC1 : 1 ≤ C := by
    rw [hCeq, pluckerConst]
    exact one_le_mul_of_one_le_of_one_le
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
      (one_le_pow₀ (le_max_left _ _))
  set wWC : ℝ := wedgeWeightConst Sfin L C p with hwWC
  have hwWC1 : 1 ≤ wWC := le_max_right _ _
  set aT : ℝ := rankThreshold Sfin L' (δ / 2) with haT
  have haT0 : 0 < aT := by
    rw [haT, rankThreshold]
    positivity
  have hQ₁0 : 0 < Q₁ := lt_of_lt_of_le one_pos hQ₁
  set Q₀ : ℝ := max 1 (max (Real.log Q₁) (max (max (Real.log 2) (2 * Real.log wWC / ε))
    (max (Real.log C) (max (Real.log aT) Q56)))) with hQ₀
  refine ⟨𝒮, h𝒮card, fun Z hZ ↦ (Finset.mem_filter.1 hZ).2, Q₀,
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_, fun Q₀' hQ₀' ↦ ?_⟩
  · rw [hQ₀, hQ₁eq, hwWC, hCeq, haT, hQ56, parametricStepThreshold, hMch]
  have hle : ∀ x, x ≤ max (Real.log Q₁) (max (max (Real.log 2) (2 * Real.log wWC / ε))
      (max (Real.log C) (max (Real.log aT) Q56))) → x ≤ Q₀' := fun x hx ↦
    (hx.trans (le_max_right _ _)).trans hQ₀'
  have hQ₀1 : 1 ≤ Q₀' := (le_max_left _ _).trans hQ₀'
  have hlQ₁ : Real.log Q₁ ≤ Q₀' := hle _ (le_max_left _ _)
  have hl2 : Real.log 2 ≤ Q₀' :=
    hle _ ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _)))
  have hlW : 2 * Real.log wWC / ε ≤ Q₀' :=
    hle _ ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _)))
  have hlC : Real.log C ≤ Q₀' :=
    hle _ ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hlaT : Real.log aT ≤ Q₀' := hle _ ((le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hQ56' : Q56 ≤ Q₀' := hle _ ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  set 𝒯 : Finset ℝ := P.biUnion fun g ↦ 𝒯g g Q₀' hQ56' with h𝒯
  refine ⟨𝒯, ?_, fun t ht ↦ ?_, ?_⟩
  · refine Finset.card_biUnion_le.trans ((Finset.sum_le_card_nsmul P _ _
      fun g _ ↦ h𝒯gcard g _ _).trans ?_)
    rw [smul_eq_mul]
    exact Nat.mul_le_mul_right _ hpoolcard
  · obtain ⟨g, -, htg⟩ := Finset.mem_biUnion.1 ht
    exact h𝒯gge g _ _ t htg
  intro Q hQ1 hQlog r hrank hR1 hRk hjump
  have hQ0 : (0 : ℝ) < Q := lt_trans one_pos hQ1
  have hQQ₁ : Q₁ ≤ Q := (Real.log_le_log_iff hQ₁0 hQ0).1 (hlQ₁.trans hQlog)
  have hQC : C ≤ Q := (Real.log_le_log_iff (by linarith) hQ0).1 (hlC.trans hQlog)
  have hQaT : aT ≤ Q := (Real.log_le_log_iff haT0 hQ0).1 (hlaT.trans hQlog)
  have hQQ₂ : Q₂ ≤ Q := by
    rw [hQ₂eq]
    refine max_le ((Real.log_le_log_iff two_pos hQ0).1 (hl2.trans hQlog)) ?_
    rw [← Real.le_log_iff_exp_le hQ0]
    refine le_trans ?_ (hlW.trans hQlog)
    exact div_le_div_of_nonneg_left (by linarith [Real.log_nonneg hwWC1]) hε (by linarith)
  have hrank' : ∀ g ∈ P, finrank K (approxSpan Sfin L' (gridExponent cT γ g) Q) < M := by
    intro g hg
    rw [hP, Set.Finite.mem_toFinset] at hg
    exact finrank_approxSpan_lt_of_rankThreshold_le hL'Inf hL'Fin (half_pos hδ0)
      (by have := hg.2; rw [neg_div] at this; exact this) hQaT
  have hna : ∀ v : FinitePlace K, IsNonarchimedean v.1 := fun v a b ↦ v.add_le a b
  have hDt : DiscreteTopology (approxLattice Sfin L c Q) :=
    discreteTopology_approxLattice hLFin c hQ0.ne'
  have : DiscreteTopology (approxModule Sfin L c Q).mixedImage := hDt
  have hZl : IsZLattice ℝ (approxLattice Sfin L c Q) := isZLattice_approxLattice hLFin c hQ0.ne'
  have : IsZLattice ℝ (approxModule Sfin L c Q).mixedImage := hZl
  have hB₂ : (interior (approxBody L c Q)).Nonempty :=
    ⟨0, mem_interior_iff_mem_nhds.2 (approxBody_mem_nhds_zero L c hQ0)⟩
  set μ := successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) with hμ
  have hμpos : ∀ j, j < N → 0 < μ j := fun j hj ↦
    successiveMinimum_pos _ (convex_approxBody L c Q) (fun z hz ↦ neg_mem_approxBody hz) hB₂
      (isBounded_approxBody hLInf c Q) hj
  have hmono : MonotoneOn μ (Set.Iio N) := fun i _ j hj hij ↦
    successiveMinimum_le_of_le _ (convex_approxBody L c Q) (fun z hz ↦ neg_mem_approxBody hz)
      hB₂ (isBounded_approxBody hLInf c Q) hij (Set.mem_Iio.1 hj)
  obtain ⟨x, hxind, hx⟩ := exists_linearIndependent_mem_smul_successiveMinimum
    (approxModule Sfin L c Q) (convex_approxBody L c Q) (fun z hz ↦ neg_mem_approxBody hz) hB₂
    (isBounded_approxBody hLInf c Q) (isClosed_approxBody L c Q)
  obtain ⟨ξ, hξ, π, hmem⟩ := hplucker Sfin L hLInf hLFin c Q hQ1 x hxind μ hmono hμpos hx
  set y : Fin N → ι → K := fun j ↦ x j + ∑ l ∈ Finset.Iio j, ξ j l • x l with hy
  have hyind : LinearIndependent K y := linearIndependent_add_sum_smul hxind ξ
  set cw := wedgeExponent c π μ C Q k p with hcw
  set g := roundExponent cT cw γ with hg
  set c' := gridExponent cT γ g with hc'
  -- the exponents of the wedge domain stay in the box, and are exact at the finite places
  have hCQ1 : (1 : ℝ) ≤ C * Q := one_le_mul_of_one_le_of_one_le hC1 hQ1.le
  have hbox : ∀ (w : InfinitePlace K) (T : Set.powersetCard ι p), |cw w.1 T - cT w.1 T| ≤ G :=
    fun w T ↦ abs_wedgeExponent_sub_sum_le hQ1 hQC hCQ1 hB.le hkN hpN
      (fun j hj ↦ (hminima Q hQQ₁ j hj).1) (fun j hj ↦ (hminima Q hQQ₁ j hj).2) w.1 T
  have hfinex : ∀ v ∈ Sfin, ∀ T : Set.powersetCard ι p, cw v.1 T = cT v.1 T := by
    intro v _ T
    rw [hcw, wedgeExponent]
    simp only [hna v, ↓reduceIte, add_zero]
    rfl
  have hgridfin : ∀ v ∈ Sfin, ∀ T : Set.powersetCard ι p, c' v.1 T = cT v.1 T := by
    intro v _ T
    exact gridExponent_of_forall_ne cT g
      (fun w hcc ↦ InfinitePlace.not_isNonarchimedean w (by rw [hcc]; exact hna v)) T
  -- the rounded exponents are one of the finitely many grids
  have hgpool : g ∈ pool := by
    refine ⟨fun w T ↦ le_of_le_of_eq (abs_roundExponent_le hγ0 hbox w T) rfl, ?_⟩
    have h1 : approxWeight Sfin c' ≤ approxWeight Sfin cw + γ * ((d : ℝ) * (M : ℝ)) :=
      approxWeight_le_of_le (fun w T ↦ gridExponent_roundExponent_le hγ0 w T)
        (fun v hv T ↦ le_of_eq ((hgridfin v hv T).trans (hfinex v hv T).symm))
    have h2 : approxWeight Sfin cw ≤ -δ := by
      refine (hwt Q hQQ₂ r hR1 hRk hjump π).trans ?_
      rw [hδ, parametricDelta, ← neg_div]
      exact div_le_div_of_nonneg_right hc (by positivity)
    have h3 : γ * ((d : ℝ) * (M : ℝ)) = δ / 2 := by
      rw [hγeq]
      field_simp
    linarith
  have hgP : g ∈ P := hpoolfin.mem_toFinset.2 hgpool
  -- the wedges of Evertse's vectors lie in the grid domain
  have hsub : approxDomain Sfin L' cw Q ⊆ approxDomain Sfin L' c' Q :=
    approxDomain_subset_of_le hQ1.le (fun w T ↦ le_gridExponent_roundExponent hγ0 w T)
      (fun v hv T ↦ le_of_eq ((hfinex v hv T).trans (hgridfin v hv T).symm))
  have hwedgele : wedgeSpan k p y ≤ approxSpan Sfin L' c' Q := by
    rw [wedgeSpan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨J, hJ, rfl⟩
    exact Submodule.subset_span (hsub (hmem k p J hJ))
  have hrk : finrank K (wedgeSpan k p y) + 1 = M := finrank_wedgeSpan_add_one hyind hkp
  have hlt : finrank K (approxSpan Sfin L' c' Q) < M := hrank' g hgP
  have heq : wedgeSpan k p y = approxSpan Sfin L' c' Q :=
    Submodule.eq_of_le_of_finrank_le hwedgele (by omega)
  have hrankM : finrank K (approxSpan Sfin L' c' Q) = M - 1 := by rw [← heq]; omega
  have hZ : recoverSpan p (approxSpan Sfin L' c' Q)
      = Submodule.span K (x '' {j | (j : ℕ) < k}) := by
    rw [← heq, recoverSpan_wedgeSpan hyind hkp, hy, Submodule.span_image_add_sum_smul_eq]
  by_cases hin : approxSpan Sfin L' c' Q ∈ 𝒲 g
  · refine Or.inl ⟨recoverSpan p (approxSpan Sfin L' c' Q), ?_, ?_⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨g, hgP, Finset.mem_image_of_mem _
        ((h𝒲fin g).mem_toFinset.2 hin)⟩, ?_⟩
      rw [hZ]
      exact Submodule.span_image_setOf_lt_ne_top x hkN
    · rw [hZ, approxSpan_eq_span_image hLInf hLFin c hQ0 hxind hx]
      refine Submodule.span_mono (Set.image_mono fun j hj ↦ ?_)
      have hjR : (j : ℕ) < finrank K (approxSpan Sfin L c Q) :=
        (successiveMinimum_approx_le_one_iff hLInf hLFin c hQ0 j.2).1 hj
      rw [hrank] at hjR
      exact lt_of_lt_of_le hjR hRk
  · obtain ⟨t, ht, h1, h2⟩ := h𝒯gint g _ _ hgpool Q hQ1 hQlog hrankM hin
    exact Or.inr ⟨t, Finset.mem_biUnion.2 ⟨g, hgP, ht⟩, h1, h2⟩

end Wedge

open scoped Classical in
/-- **The threshold of Layer 6.1**, on the scale of `log Q`: the largest of `1`, the logarithm of
the rank threshold at weight `-ε`, and the sum over `0 < p < #ι` of the thresholds
`parametricStepThreshold` along `p`. An order on `ι` is chosen by transport from `Fin #ι`, as the
proof does. -/
noncomputable def parametricThreshold (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (R : RothParams) (ε A : ℝ) : ℝ :=
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Equiv.injective _)
  max 1 (max (Real.log (rankThreshold Sfin L ε))
    (∑ p ∈ Finset.range (Fintype.card ι),
      if 0 < p then parametricStepThreshold Sfin L R ε A p else 1))

open scoped Classical in
/-- **Layer 6.1 as an interval result** (Bombieri–Gubler 7.5.30–7.5.32 with Layer 5.6 as an
interval result; Evertse–Schlickewei for the formulation). For forms with coefficients in `K`,
linearly independent at every infinite place and at every place of `Sfin`, and exponents with
`approxWeight ≤ -ε < 0` and `approxAbsWeight ≤ A`, there are a finite set `T` of at most
`parametricSubspaceCount` proper subspaces of `Kⁱ` and a level `Q₀ > 0` such that for every
`Q₀' ≥ Q₀` the levels `Q` with `log Q ≥ Q₀'` at which the domain lies in no member of `T` have
`log Q` in at most `parametricIntervalCount` intervals `[t, ρ t)` with `t ≥ Q₀'` and
`ρ = parametricRatio`. The two counts and the ratio depend on `#ι`, `[K : ℚ]`, the number of
places, `ε` and `A` alone. -/
theorem exists_forall_mem_interval_approxDomain [Nontrivial ι] (R : SubspaceRoth.{u} K)
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {c : AbsoluteValue K ℝ → ι → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hc : approxWeight Sfin c ≤ -ε) {A : ℝ}
    (hA : approxAbsWeight Sfin c ≤ A) :
    ∃ T : Finset (Submodule K (ι → K)),
      #T ≤ parametricSubspaceCount (Fintype.card ι) (finrank ℚ K)
        (Fintype.card (InfinitePlace K)) (Fintype.card (InfinitePlace K) + #Sfin) ε A ∧
      (∀ W ∈ T, W ≠ ⊤) ∧ ∃ Q₀ : ℝ, 0 < Q₀ ∧ Q₀ = parametricThreshold Sfin L R.toRothParams ε A ∧
      ∀ Q₀' : ℝ, Q₀ ≤ Q₀' →
      ∃ 𝒯 : Finset ℝ, #𝒯 ≤ parametricIntervalCount (Fintype.card ι) (finrank ℚ K)
          (Fintype.card (InfinitePlace K)) (Fintype.card (InfinitePlace K) + #Sfin) ε A ∧
        (∀ t ∈ 𝒯, Q₀' ≤ t) ∧ ∀ Q : ℝ, 1 < Q → Q₀' ≤ Real.log Q →
          (∃ W ∈ T, approxDomain Sfin L c Q ⊆ W) ∨
            ∃ t ∈ 𝒯, t ≤ Real.log Q ∧ Real.log Q < parametricRatio R.toRothParams (Fintype.card ι)
              (finrank ℚ K) (Fintype.card (InfinitePlace K) + #Sfin) ε A * t := by
  have hne : Nonempty ι := ⟨Classical.arbitrary ι⟩
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Equiv.injective _)
  set N := Fintype.card ι with hN
  set d := finrank ℚ K with hd
  set r := Fintype.card (InfinitePlace K) with hr
  set s := r + #Sfin with hs
  have hN2 : 2 ≤ N := Fintype.one_lt_card
  have hA0 : 0 ≤ A := (approxAbsWeight_nonneg Sfin c).trans hA
  -- for every `p` in `(0, #ι)` the interval result along `k = #ι - p`
  have hfam : ∀ p : ℕ, ∃ 𝒮 : Finset (Submodule K (ι → K)),
      #𝒮 ≤ parametricGridCount N d r p ε A * 2 ^ (N.choose p * s) ∧ (∀ Z ∈ 𝒮, Z ≠ ⊤) ∧
      ∃ Q₀ : ℝ, 0 < Q₀ ∧
      Q₀ = (if 0 < p ∧ p < N then parametricStepThreshold Sfin L R.toRothParams ε A p else 1) ∧
      ∀ Q₀' : ℝ, Q₀ ≤ Q₀' →
      ∃ 𝒯 : Finset ℝ, #𝒯 ≤ parametricGridCount N d r p ε A * parametricChainLength N d s p ε A ∧
        (∀ t ∈ 𝒯, Q₀' ≤ t) ∧ (0 < p → p < N →
        ∀ Q : ℝ, 1 < Q → Q₀' ≤ Real.log Q →
        ∀ r : ℕ, finrank K (approxSpan Sfin L c Q) = r → 1 ≤ r → r ≤ N - p →
          (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) (N - p - 1) /
              successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) (N - p)) ^ (N - r)
            ≤ (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) (N - 1))⁻¹ →
          (∃ Z ∈ 𝒮, approxSpan Sfin L c Q ≤ Z) ∨
            ∃ t ∈ 𝒯, t ≤ Real.log Q ∧ Real.log Q
              < parametricStepRatio R.toRothParams N d s p ε A * t) := by
    intro p
    by_cases hp : 0 < p ∧ p < N
    · obtain ⟨𝒮, h1, h2, Q₀, h3, h3', h4⟩ := exists_forall_mem_interval_approxSpan_le R hLInf
        hLFin hε hc hA (k := N - p) (p := p) (by omega) (by omega) hp.1
      refine ⟨𝒮, h1, h2, Q₀, h3, by simp only [hp, and_self, ↓reduceIte, h3'],
        fun Q₀' hQ₀' ↦ ?_⟩
      obtain ⟨𝒯, h5, h6, h7⟩ := h4 Q₀' hQ₀'
      exact ⟨𝒯, h5, h6, fun _ _ ↦ h7⟩
    · exact ⟨∅, by simp, by simp, 1, one_pos, by simp only [hp, ↓reduceIte],
        fun _ _ ↦ ⟨∅, by simp, by simp, fun h1 h2 ↦ absurd ⟨h1, h2⟩ hp⟩⟩
  choose 𝒮 h𝒮card h𝒮top Q₀p hQ₀p hQ₀peq 𝒯p h𝒯pcard h𝒯pge h𝒯pint using hfam
  set T : Finset (Submodule K (ι → K)) := insert ⊥ ((Finset.range N).biUnion 𝒮) with hT
  set a : ℝ := rankThreshold Sfin L ε with ha
  have ha0 : 0 < a := by
    rw [ha, rankThreshold]
    positivity
  set Q₀ : ℝ := max 1 (max (Real.log a) (∑ p ∈ Finset.range N, Q₀p p)) with hQ₀
  refine ⟨T, ?_, ?_, Q₀, lt_of_lt_of_le one_pos (le_max_left _ _), ?_, fun Q₀' hQ₀' ↦ ?_⟩
  · refine (Finset.card_insert_le _ _).trans ?_
    rw [parametricSubspaceCount, add_comm 1]
    exact Nat.add_le_add_right
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun p _ ↦ h𝒮card p)) 1
  · intro W hW
    rcases Finset.mem_insert.1 hW with rfl | hW
    · exact bot_ne_top
    · obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.1 hW
      exact h𝒮top p W hp
  · rw [hQ₀, parametricThreshold]
    refine congrArg _ (congrArg _ (Finset.sum_congr rfl fun p hp ↦ ?_))
    rw [hQ₀peq p]
    by_cases h0 : 0 < p
    · have hpN : p < N := Finset.mem_range.1 hp
      simp only [h0, hpN, and_self, ↓reduceIte]
    · simp only [h0, false_and, ↓reduceIte]
  have hQ₀1 : 1 ≤ Q₀' := (le_max_left _ _).trans hQ₀'
  have hQ₀a : Real.log a ≤ Q₀' := ((le_max_left _ _).trans (le_max_right _ _)).trans hQ₀'
  have hQ₀p' : ∀ p ∈ Finset.range N, Q₀p p ≤ Q₀' := fun p hp ↦
    (Finset.single_le_sum (f := Q₀p) (fun p _ ↦ (hQ₀p p).le) hp).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hQ₀'))
  set 𝒯 : Finset ℝ := (Finset.range N).biUnion fun p ↦
    𝒯p p (max Q₀' (Q₀p p)) (le_max_right _ _) with h𝒯
  refine ⟨𝒯, ?_, fun t ht ↦ ?_, fun Q hQ1 hQlog ↦ ?_⟩
  · exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun p _ ↦ h𝒯pcard p _ _)
  · obtain ⟨p, -, htp⟩ := Finset.mem_biUnion.1 ht
    exact (le_max_left _ _).trans (h𝒯pge p _ _ t htp)
  have hQ0 : (0 : ℝ) < Q := lt_trans one_pos hQ1
  have hrank := finrank_approxSpan_lt_of_rankThreshold_le hLInf hLFin hε hc
    ((Real.log_le_log_iff ha0 hQ0).1 (hQ₀a.trans hQlog))
  have hDt : DiscreteTopology (approxLattice Sfin L c Q) :=
    discreteTopology_approxLattice hLFin c hQ0.ne'
  have : DiscreteTopology (approxModule Sfin L c Q).mixedImage := hDt
  have hZl : IsZLattice ℝ (approxLattice Sfin L c Q) := isZLattice_approxLattice hLFin c hQ0.ne'
  have : IsZLattice ℝ (approxModule Sfin L c Q).mixedImage := hZl
  have hB₂ : (interior (approxBody L c Q)).Nonempty :=
    ⟨0, mem_interior_iff_mem_nhds.2 (approxBody_mem_nhds_zero L c hQ0)⟩
  set μ := successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) with hμ
  have hμpos : ∀ j, j < N → 0 < μ j := fun j hj ↦
    successiveMinimum_pos _ (convex_approxBody L c Q) (fun z hz ↦ neg_mem_approxBody hz) hB₂
      (isBounded_approxBody hLInf c Q) hj
  rcases Nat.eq_zero_or_pos (finrank K (approxSpan Sfin L c Q)) with hR0 | hR1
  · refine Or.inl ⟨⊥, Finset.mem_insert_self _ _, fun z hz ↦ ?_⟩
    have hmem : z ∈ approxSpan Sfin L c Q := Submodule.subset_span hz
    rwa [Submodule.finrank_eq_zero.1 hR0] at hmem
  obtain ⟨k, hkR, hkN, hjump⟩ := exists_div_pow_le_inv (μ := μ)
    (R := finrank K (approxSpan Sfin L c Q)) (N := N) hR1 hrank hμpos
    ((successiveMinimum_approx_le_one_iff hLInf hLFin c hQ0 (by omega)).2 (by omega))
  obtain ⟨p, rfl⟩ : ∃ p, k = N - p := ⟨N - k, by omega⟩
  have hpN : p < N := by omega
  have hp0 : 0 < p := by omega
  have hpr : p ∈ Finset.range N := Finset.mem_range.2 hpN
  rcases h𝒯pint p _ _ hp0 hpN Q hQ1 (max_le hQlog ((hQ₀p' p hpr).trans hQlog)) _ rfl hR1 hkR
      hjump with ⟨Z, hZ, hle⟩ | ⟨t, ht, h1, h2⟩
  · exact Or.inl ⟨Z, Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨p, hpr, hZ⟩),
      Submodule.span_le.1 hle⟩
  · refine Or.inr ⟨t, Finset.mem_biUnion.2 ⟨p, hpr, ht⟩, h1, h2.trans_le ?_⟩
    have ht0 : 0 ≤ t := by linarith [h𝒯pge p _ _ t ht, le_max_left Q₀' (Q₀p p)]
    refine mul_le_mul_of_nonneg_right ?_ ht0
    exact Finset.single_le_sum (f := fun p ↦ parametricStepRatio R.toRothParams N d s p ε A)
      (fun p _ ↦ (parametricStepRatio_pos R.toRothParams d s p (by omega) hε hA0).le) hpr

/-- **Layer 6.1, the parametric Subspace Theorem** (Bombieri–Gubler 7.5.30–7.5.32, Steps VIII and
IX; Evertse–Schlickewei for the formulation). For forms with coefficients in `K`, linearly
independent at every infinite place and at every place of `Sfin`, and exponents of negative
weight, there are a finite set `T` of proper subspaces of `Kⁱ` and a level `Q₀` such that every
approximation domain of level at least `Q₀` is contained in a member of `T`. It is read off the
interval result `NumberField.exists_forall_mem_interval_approxDomain`: above the last of its
intervals no level is left. -/
theorem exists_finset_submodule_forall_approxDomain_subset [Nontrivial ι]
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {c : AbsoluteValue K ℝ → ι → ℝ}
    (hc : approxWeight Sfin c < 0) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∃ Q₀ : ℝ, ∀ Q ≥ Q₀, ∃ W ∈ T, approxDomain Sfin L c Q ⊆ W := by
  obtain ⟨T, -, hT, Q₀, hQ₀, -, hint⟩ := exists_forall_mem_interval_approxDomain
    (SubspaceRoth.bombieriGubler K) hLInf hLFin (neg_pos.2 hc) (neg_neg _).ge le_rfl
  obtain ⟨𝒯, -, h𝒯, hQint⟩ := hint Q₀ le_rfl
  set ρ := parametricRatio (SubspaceRoth.bombieriGubler.{u} K).toRothParams (Fintype.card ι)
    (finrank ℚ K) (Fintype.card (InfinitePlace K) + #Sfin) (-approxWeight Sfin c)
    (approxAbsWeight Sfin c)
  set X : ℝ := Q₀ + ∑ t ∈ 𝒯, |ρ * t| with hX
  have hsum0 : 0 ≤ ∑ t ∈ 𝒯, |ρ * t| := Finset.sum_nonneg fun t _ ↦ abs_nonneg _
  refine ⟨T, hT, Real.exp (X + 1), fun Q hQ ↦ ?_⟩
  have hQ0 : 0 < Q := (Real.exp_pos _).trans_le hQ
  have hlog : X + 1 ≤ Real.log Q := by rwa [Real.le_log_iff_exp_le hQ0]
  have hQ1 : 1 < Q := by
    rw [← Real.log_pos_iff hQ0.le]
    linarith
  rcases hQint Q hQ1 (by linarith) with h | ⟨t, ht, -, h2⟩
  · exact h
  · have h1 : ρ * t ≤ ∑ t ∈ 𝒯, |ρ * t| :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun t ↦ |ρ * t|)
        (fun t _ ↦ abs_nonneg _) ht)
    linarith

end NumberField
