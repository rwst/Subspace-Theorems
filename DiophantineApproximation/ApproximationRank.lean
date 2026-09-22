/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.FieldMinkowski

-- Used only inside proofs.
import DiophantineApproximation.FinitePlaceValues
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The rank of an approximation domain

For a number field `K`, the span `V(Q) ⊆ Kⁱ` of the approximation domain of level `Q`
(`ApproximationDomain.lean`) is `NumberField.approxSpan`, and its dimension is the **rank** of the
domain (Bombieri–Gubler, Definition 7.5.11). The rank is the number of successive minima over `K`
of the domain that are at most `1`, and `V(Q)` is spanned by the vectors realizing them; this holds
for the points of any lattice `Λ` in any closed bounded symmetric convex body `B`, and is stated so
first. For exponents of negative weight, the lower bound of Minkowski's second theorem over `K`
(`FieldMinkowski.lean`), with every minimum replaced by the last, makes the last minimum at least a
positive power of `Q`, so the rank is at most `#ι - 1` at every large enough level — Lemma 7.5.12 in
parametric form. And a bounded range of levels contributes finitely many points, hence finitely
many subspaces `V(Q)`.

## Main results

* `NumberField.approxSpan`: `V(Q)`, the span of the approximation domain.
* `NumberField.successiveMinimum_le_one_iff` and `NumberField.finrank_span_setOf_mem`: `μ i ≤ 1`
  exactly when `i` is less than the dimension of the span of `Λ ∩ B`, which is therefore the number
  of minima at most `1`; `NumberField.finrank_approxSpan` for approximation domains.
* `NumberField.span_setOf_mem_eq_span_image` and `NumberField.approxSpan_eq_span_image`: the span
  is spanned by the vectors realizing the minima at most `1`.
* `NumberField.le_successiveMinimum_approx_pow`: the last minimum to the power `d #ι` is at least a
  constant times `Q ^ (-weight)`.
* `NumberField.eventually_finrank_approxSpan_lt` and `NumberField.eventually_approxSpan_ne_top`:
  for negative weight, the rank is less than `#ι` for all large `Q` (Bombieri–Gubler,
  Lemma 7.5.12).
* `NumberField.finite_approxDomain`, `NumberField.finite_biUnion_approxDomain` and
  `NumberField.finite_image_approxSpan`: a domain of positive level is finite, and the levels in
  `[Q₁, Q₂]` with `Q₁ > 0` contribute finitely many points and finitely many subspaces `V(Q)`.

## Implementation notes

⚠ **The lemma is stated along the levels, not along a sequence of solutions.** Bombieri–Gubler
state 7.5.12 for the heights `Q = H(x)` of a hypothetical infinite set of solutions, as
`1 ≤ rank ≤ n` for all but finitely many of them: the lower bound because `x` lies in its own
domain, and "for all but finitely many" by Northcott's theorem, which makes the heights large.
Neither is a statement about domains; what their proof shows about domains is that the rank is at
most `n` for every large enough level, and that is what is stated here. The rank can be `0`: over
`ℚ` with `c = -1` it is, past the level `1`.

⚠ **The rank is read from the minima through attainment.** `μ i ≤ 1` gives `i + 1` independent
points in `Λ ∩ B` only because the minima are attained, by one family, and `μ k B ⊆ B` for
`μ k ≤ 1`: the body is balanced. The converse needs nothing — the dilation `1` is admissible.
Counting the minima at most `1` and taking the largest index with `μ i ≤ 1`, the book's form, agree
because the minima are monotone below `#ι`.

⚠ **A bounded range of levels lies in one domain.** For `Q` in `[Q₁, Q₂]` every bound
`Q ^ c v i` is at most `max Q₂ Q₁⁻¹ ^ |c v i|`, so the domains all lie in the domain of the
exponents `|c|` at one level, which is the set of points of a lattice in a bounded body. `Q₁ > 0`
is needed: as `Q → 0` the bounds with `c v i < 0` blow up.

⚠ **Three acceptance tests.** Over `ℚ`, in one variable, with no finite place, the coordinate form
and `c = -1`, the rank is `1` exactly when `Q ≤ 1`: the domain is the set of integers of absolute
value at most `Q⁻¹`. So the conclusion is eventual and fails at `Q = 1`, where the weight is already
negative. With `c = 0` instead the domain is `ℤ ∩ [-1, 1]`, of rank `1`, and its minimum is exactly
`1`: the minima are counted at most `1`, not below it. And for the coordinate forms with `c = 0`,
of weight `0`, every domain contains the standard basis and the rank is `#ι` at every level: the
weight has to be negative, not merely nonpositive.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Definition 7.5.11 and Lemma 7.5.12.

This is Layer 4.3 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Module NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Filter

open scoped Pointwise

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}

/-- **The span of an approximation domain**, `V(Q)` (Bombieri–Gubler, Definition 7.5.11): the
subspace of `Kⁱ` spanned by the domain of level `Q`. Its dimension is the **rank** of the domain. -/
def approxSpan (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) : Submodule K (ι → K) :=
  Submodule.span K (approxDomain Sfin L c Q)

variable [Fintype ι]

section Minima

variable {B : Set (ι → mixedSpace K)} {i : ℕ}

open scoped Classical in
/-- **A minimum is at most `1` exactly when the points of `Λ` in `B` span more than its index**:
`i + 1` independent points of `Λ` in `B` make the dilation `1` admissible, and conversely the first
`i + 1` vectors of a family realizing the minima lie in `μ k B ⊆ B`. -/
theorem successiveMinimum_le_one_iff (Λ : Submodule (𝓞 K) (ι → K))
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage] (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B)
    (hB₄ : IsClosed B) (hi : i < Fintype.card ι) :
    successiveMinimum Λ B i ≤ 1 ↔
      i < finrank K (Submodule.span K {x | x ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x j)) ∈ B}) := by
  set S := {x : ι → K | x ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x j)) ∈ B}
  have hbal : Balanced ℝ B := (balanced_iff_neg_mem hB₀).2 fun x hx ↦ hB₁ x hx
  constructor
  · intro h
    obtain ⟨x, hxind, hx⟩ :=
      exists_linearIndependent_mem_smul_successiveMinimum Λ hB₀ hB₁ hB₂ hB₃ hB₄
    have hle : i + 1 ≤ Fintype.card ι := hi
    have hyS : ∀ k : Fin (i + 1), x (Fin.castLE hle k) ∈ S := by
      intro k
      refine ⟨(hx _).1, ?_⟩
      have hk : ((Fin.castLE hle k : Fin (Fintype.card ι)) : ℕ) ≤ i := by
        simp only [Fin.val_castLE]; omega
      have hmk := successiveMinimum_le_of_le Λ hB₀ hB₁ hB₂ hB₃ hk hi
      have hpos := successiveMinimum_pos Λ hB₀ hB₁ hB₂ hB₃ (Fin.castLE hle k).isLt
      obtain ⟨b, hb, hbz⟩ := Set.mem_smul_set.1 (hx (Fin.castLE hle k)).2
      rw [← hbz]
      exact hbal.smul_mem (by rw [Real.norm_of_nonneg hpos.le]; exact hmk.trans h) hb
    have h1 := Submodule.finrank_mono
      (Submodule.span_mono (Set.range_subset_iff.2 hyS) :
        Submodule.span K (Set.range (x ∘ Fin.castLE hle)) ≤
          Submodule.span K S)
    rw [finrank_span_eq_card (hxind.comp _ (Fin.castLE_injective hle)), Fintype.card_fin] at h1
    omega
  · intro h
    obtain ⟨f, hfS, -, hfind⟩ := Submodule.exists_fun_fin_finrank_span_eq K S
    have hle : i + 1 ≤ finrank K (Submodule.span K S) := h
    refine successiveMinimum_le one_pos (x := fun k ↦ f (Fin.castLE hle k)) (fun k ↦ ?_)
      (hfind.comp _ (Fin.castLE_injective hle))
    exact ⟨(hfS _).1, by rw [one_smul]; exact (hfS _).2⟩

open scoped Classical in
/-- **The rank is the number of minima at most `1`**: the dimension of the span of the points of
`Λ` in `B` is the number of `i < #ι` with `μ i ≤ 1`. -/
theorem finrank_span_setOf_mem (Λ : Submodule (𝓞 K) (ι → K))
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage] (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B)
    (hB₄ : IsClosed B) :
    finrank K (Submodule.span K {x | x ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x j)) ∈ B}) =
      {i ∈ Finset.range (Fintype.card ι) | successiveMinimum Λ B i ≤ 1}.card := by
  set r := finrank K (Submodule.span K {x | x ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x j)) ∈ B})
  have hr : r ≤ Fintype.card ι :=
    (Submodule.finrank_le _).trans (finrank_fintype_fun_eq_card K).le
  have : {i ∈ Finset.range (Fintype.card ι) | successiveMinimum Λ B i ≤ 1} = Finset.range r := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, h⟩
      exact (successiveMinimum_le_one_iff Λ hB₀ hB₁ hB₂ hB₃ hB₄ hi).1 h
    · intro hi
      exact ⟨hi.trans_le hr,
        (successiveMinimum_le_one_iff Λ hB₀ hB₁ hB₂ hB₃ hB₄ (hi.trans_le hr)).2 hi⟩
  rw [this, Finset.card_range]

open scoped Classical in
/-- **The span is spanned by the vectors realizing the minima at most `1`**, for any family
realizing the minima (Bombieri–Gubler, proof of Lemma 7.5.12). -/
theorem span_setOf_mem_eq_span_image (Λ : Submodule (𝓞 K) (ι → K))
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage] (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B)
    (hB₄ : IsClosed B) {x : Fin (Fintype.card ι) → ι → K} (hxind : LinearIndependent K x)
    (hx : ∀ k, x k ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x k j)) ∈ successiveMinimum Λ B k • B) :
    Submodule.span K {y | y ∈ Λ ∧ (fun j ↦ mixedEmbedding K (y j)) ∈ B} =
      Submodule.span K (x '' {k | successiveMinimum Λ B k ≤ 1}) := by
  set S := {y : ι → K | y ∈ Λ ∧ (fun j ↦ mixedEmbedding K (y j)) ∈ B}
  have hbal : Balanced ℝ B := (balanced_iff_neg_mem hB₀).2 fun x hx ↦ hB₁ x hx
  have hsub : x '' {k | successiveMinimum Λ B k ≤ 1} ⊆ S := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨(hx k).1, ?_⟩
    have hpos := successiveMinimum_pos Λ hB₀ hB₁ hB₂ hB₃ k.isLt
    obtain ⟨b, hb, hbz⟩ := Set.mem_smul_set.1 (hx k).2
    rw [← hbz]
    exact hbal.smul_mem (by rw [Real.norm_of_nonneg hpos.le]; exact hk) hb
  refine le_antisymm ?_ (Submodule.span_mono hsub)
  set r := finrank K (Submodule.span K S)
  have hr : r ≤ Fintype.card ι :=
    (Submodule.finrank_le _).trans (finrank_fintype_fun_eq_card K).le
  set y : Fin r → ι → K := x ∘ Fin.castLE hr
  have hy : ∀ k, y k ∈ x '' {k | successiveMinimum Λ B k ≤ 1} := fun k ↦
    ⟨Fin.castLE hr k, (successiveMinimum_le_one_iff Λ hB₀ hB₁ hB₂ hB₃ hB₄
      (Fin.castLE hr k).isLt).2 (by rw [Fin.val_castLE]; exact k.isLt), rfl⟩
  have hyS : Submodule.span K (Set.range y) ≤ Submodule.span K S :=
    Submodule.span_mono ((Set.range_subset_iff.2 hy).trans hsub)
  have heq : Submodule.span K (Set.range y) = Submodule.span K S :=
    Submodule.eq_of_le_of_finrank_eq hyS (by
      rw [finrank_span_eq_card (hxind.comp _ (Fin.castLE_injective hr)), Fintype.card_fin])
  rw [← heq]
  exact Submodule.span_mono (Set.range_subset_iff.2 hy)

end Minima

section Approximation

variable {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}

open scoped Classical in
/-- **A minimum of an approximation domain is at most `1` exactly when the rank exceeds its
index.** -/
theorem successiveMinimum_approx_le_one_iff
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : 0 < Q) {i : ℕ} (hi : i < Fintype.card ι) :
    successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) i ≤ 1 ↔
      i < finrank K (approxSpan Sfin L c Q) := by
  have hD : DiscreteTopology (approxLattice Sfin L c Q) :=
    discreteTopology_approxLattice hLFin c hQ.ne'
  have : DiscreteTopology (approxModule Sfin L c Q).mixedImage := hD
  have hZ : IsZLattice ℝ (approxLattice Sfin L c Q) := isZLattice_approxLattice hLFin c hQ.ne'
  have : IsZLattice ℝ (approxModule Sfin L c Q).mixedImage := hZ
  rw [approxSpan, approxDomain_eq Sfin L c hQ.le]
  exact successiveMinimum_le_one_iff _ (convex_approxBody L c Q)
    (fun x hx ↦ neg_mem_approxBody hx)
    ⟨0, mem_interior_iff_mem_nhds.2 (approxBody_mem_nhds_zero L c hQ)⟩
    (isBounded_approxBody hLInf c Q) (isClosed_approxBody L c Q) hi

open scoped Classical in
/-- **The rank of an approximation domain is the number of its minima at most `1`**
(Bombieri–Gubler, proof of Lemma 7.5.12). -/
theorem finrank_approxSpan (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : 0 < Q) :
    finrank K (approxSpan Sfin L c Q) = {i ∈ Finset.range (Fintype.card ι) |
      successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) i ≤ 1}.card := by
  have hD : DiscreteTopology (approxLattice Sfin L c Q) :=
    discreteTopology_approxLattice hLFin c hQ.ne'
  have : DiscreteTopology (approxModule Sfin L c Q).mixedImage := hD
  have hZ : IsZLattice ℝ (approxLattice Sfin L c Q) := isZLattice_approxLattice hLFin c hQ.ne'
  have : IsZLattice ℝ (approxModule Sfin L c Q).mixedImage := hZ
  rw [approxSpan, approxDomain_eq Sfin L c hQ.le]
  exact finrank_span_setOf_mem _ (convex_approxBody L c Q) (fun x hx ↦ neg_mem_approxBody hx)
    ⟨0, mem_interior_iff_mem_nhds.2 (approxBody_mem_nhds_zero L c hQ)⟩
    (isBounded_approxBody hLInf c Q) (isClosed_approxBody L c Q)

open scoped Classical in
/-- **`V(Q)` is spanned by the vectors realizing the minima at most `1`**, for any family realizing
the minima of the domain (Bombieri–Gubler, proof of Lemma 7.5.12). -/
theorem approxSpan_eq_span_image (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : 0 < Q) {x : Fin (Fintype.card ι) → ι → K} (hxind : LinearIndependent K x)
    (hx : ∀ k, x k ∈ approxModule Sfin L c Q ∧ (fun j ↦ mixedEmbedding K (x k j)) ∈
      successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) k • approxBody L c Q) :
    approxSpan Sfin L c Q = Submodule.span K
      (x '' {k | successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) k ≤ 1}) := by
  have hD : DiscreteTopology (approxLattice Sfin L c Q) :=
    discreteTopology_approxLattice hLFin c hQ.ne'
  have : DiscreteTopology (approxModule Sfin L c Q).mixedImage := hD
  have hZ : IsZLattice ℝ (approxLattice Sfin L c Q) := isZLattice_approxLattice hLFin c hQ.ne'
  have : IsZLattice ℝ (approxModule Sfin L c Q).mixedImage := hZ
  rw [approxSpan, approxDomain_eq Sfin L c hQ.le]
  exact span_setOf_mem_eq_span_image _ (convex_approxBody L c Q)
    (fun x hx ↦ neg_mem_approxBody hx)
    ⟨0, mem_interior_iff_mem_nhds.2 (approxBody_mem_nhds_zero L c hQ)⟩
    (isBounded_approxBody hLInf c Q) (isClosed_approxBody L c Q) hxind hx

open scoped Classical in
/-- **The last minimum of an approximation domain is at least a constant times `Q` to minus the
weight**, all to the power `d #ι`: the lower bound of Minkowski's second theorem over `K` with every
minimum replaced by the last. For a negative weight it is a positive power of `Q`. -/
theorem le_successiveMinimum_approx_pow [Nonempty ι]
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : 0 < Q) :
    2 ^ (finrank ℚ K * Fintype.card ι) / ((finrank ℚ K * Fintype.card ι).factorial *
        integralBasisHouse K ^ (finrank ℚ K * Fintype.card ι) * approxConst Sfin L) *
        Q ^ (-approxWeight Sfin c) ≤
      successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) (Fintype.card ι - 1) ^
        (finrank ℚ K * Fintype.card ι) := by
  have hD : DiscreteTopology (approxLattice Sfin L c Q) :=
    discreteTopology_approxLattice hLFin c hQ.ne'
  have : DiscreteTopology (approxModule Sfin L c Q).mixedImage := hD
  have hZ : IsZLattice ℝ (approxLattice Sfin L c Q) := isZLattice_approxLattice hLFin c hQ.ne'
  have : IsZLattice ℝ (approxModule Sfin L c Q).mixedImage := hZ
  refine (le_prod_successiveMinimum_approx hLInf hLFin c hQ).trans ?_
  rw [mul_comm, pow_mul]
  refine pow_le_pow_left₀ (Finset.prod_nonneg fun i _ ↦ successiveMinimum_nonneg _ _ _) ?_ _
  have hn : Fintype.card ι - 1 < Fintype.card ι := Nat.sub_lt Fintype.card_pos one_pos
  calc ∏ i ∈ Finset.range (Fintype.card ι),
        successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) i
      ≤ ∏ _i ∈ Finset.range (Fintype.card ι),
          successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) (Fintype.card ι - 1) :=
        Finset.prod_le_prod₀ (fun i _ ↦ successiveMinimum_nonneg _ _ _) fun i hi ↦
          successiveMinimum_le_of_le _ (convex_approxBody L c Q)
            (fun x hx ↦ neg_mem_approxBody hx)
            ⟨0, mem_interior_iff_mem_nhds.2 (approxBody_mem_nhds_zero L c hQ)⟩
            (isBounded_approxBody hLInf c Q) (by rw [Finset.mem_range] at hi; omega) hn
    _ = _ := by rw [Finset.prod_const, Finset.card_range]

open scoped Classical in
/-- **Bombieri–Gubler, Lemma 7.5.12, in parametric form**: for exponents of negative weight, the
rank of the approximation domain is at most `n` at every large enough level — the last minimum
exceeds `1`. -/
theorem eventually_finrank_approxSpan_lt
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {c : AbsoluteValue K ℝ → ι → ℝ}
    (hc : approxWeight Sfin c < 0) :
    ∀ᶠ Q in atTop, finrank K (approxSpan Sfin L c Q) < Fintype.card ι := by
  have : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [approxWeight] at hc
  set D := finrank ℚ K * Fintype.card ι
  set A : ℝ := 2 ^ D / (D.factorial * integralBasisHouse K ^ D * approxConst Sfin L)
  have hA : 0 < A := by
    have := approxConst_pos hLInf hLFin
    have := zero_lt_one.trans_le (one_le_integralBasisHouse K)
    positivity
  have hT : Tendsto (fun Q : ℝ ↦ A * Q ^ (-approxWeight Sfin c)) atTop atTop :=
    (tendsto_rpow_atTop (neg_pos.2 hc)).const_mul_atTop hA
  filter_upwards [hT.eventually_gt_atTop 1, eventually_gt_atTop 0] with Q hQ1 hQ
  have hn : Fintype.card ι - 1 < Fintype.card ι := Nat.sub_lt Fintype.card_pos one_pos
  by_contra hcon
  push Not at hcon
  have hle := (successiveMinimum_approx_le_one_iff hLInf hLFin c hQ hn).2 (by omega)
  have hpow := pow_le_one₀ (n := D) (successiveMinimum_nonneg _ _ _) hle
  linarith [le_successiveMinimum_approx_pow hLInf hLFin c hQ]

open scoped Classical in
/-- **For exponents of negative weight, `V(Q)` is a proper subspace at every large enough
level.** This is the form Layer 6.1 consumes. -/
theorem eventually_approxSpan_ne_top
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {c : AbsoluteValue K ℝ → ι → ℝ}
    (hc : approxWeight Sfin c < 0) : ∀ᶠ Q in atTop, approxSpan Sfin L c Q ≠ ⊤ := by
  filter_upwards [eventually_finrank_approxSpan_lt hLInf hLFin hc] with Q hQ htop
  rw [htop, finrank_top, finrank_fintype_fun_eq_card] at hQ
  exact lt_irrefl _ hQ

/-- On a range `[Q₁, Q₂]` with `Q₁ > 0`, every bound `Q ^ e` is at most `max Q₂ Q₁⁻¹ ^ |e|`. -/
private theorem rpow_le_max_rpow_abs {Q₁ Q₂ Q : ℝ} (hQ₁ : 0 < Q₁) (h₁ : Q₁ ≤ Q) (h₂ : Q ≤ Q₂)
    (e : ℝ) : Q ^ e ≤ max Q₂ Q₁⁻¹ ^ |e| := by
  have hQ : 0 < Q := hQ₁.trans_le h₁
  rcases le_or_gt 0 e with he | he
  · rw [abs_of_nonneg he]
    exact (Real.rpow_le_rpow hQ.le h₂ he).trans
      (Real.rpow_le_rpow (hQ.le.trans h₂) (le_max_left _ _) he)
  · rw [abs_of_neg he]
    have : Q⁻¹ ^ (-e) = Q ^ e := by rw [Real.inv_rpow hQ.le, Real.rpow_neg hQ.le, inv_inv]
    rw [← this]
    exact (Real.rpow_le_rpow (inv_nonneg.2 hQ.le) ((inv_le_inv₀ hQ hQ₁).2 h₁)
      (neg_nonneg.2 he.le)).trans
      (Real.rpow_le_rpow (inv_nonneg.2 hQ₁.le) (le_max_right _ _) (neg_nonneg.2 he.le))

omit [Fintype ι] in
/-- Raising every bound enlarges the domain. -/
private theorem approxDomain_subset_of_le {c c' : AbsoluteValue K ℝ → ι → ℝ} {Q Q' : ℝ}
    (h : ∀ v i, Q ^ c v i ≤ Q' ^ c' v i) :
    approxDomain Sfin L c Q ⊆ approxDomain Sfin L c' Q' := fun _ hx ↦
  ⟨fun v i ↦ (hx.1 v i).trans (h _ _), fun v hv i ↦ (hx.2.1 v hv i).trans (h _ _), hx.2.2⟩

omit [Fintype ι] in
open scoped Classical in
/-- **An approximation domain of positive level is finite**: the points of a lattice in a bounded
body. -/
theorem finite_approxDomain [Finite ι]
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : 0 < Q) : (approxDomain Sfin L c Q).Finite := by
  have : Fintype ι := Fintype.ofFinite ι
  have hD : DiscreteTopology (approxLattice Sfin L c Q) :=
    discreteTopology_approxLattice hLFin c hQ.ne'
  have : DiscreteTopology (approxModule Sfin L c Q).mixedImage := hD
  rw [approxDomain_eq Sfin L c hQ.le]
  exact finite_setOf_mem_of_isBounded _ (isBounded_approxBody hLInf c Q)

omit [Fintype ι] in
/-- **A bounded range of levels contributes finitely many points**: for `0 < Q₁`, the domains of
level in `[Q₁, Q₂]` all lie in the domain of the exponents `|c|` at the level `max Q₂ Q₁⁻¹`. -/
theorem finite_biUnion_approxDomain [Finite ι]
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ)
    {Q₁ Q₂ : ℝ} (hQ₁ : 0 < Q₁) :
    (⋃ Q ∈ Set.Icc Q₁ Q₂, approxDomain Sfin L c Q).Finite :=
  (finite_approxDomain hLInf hLFin (fun v i ↦ |c v i|)
    (lt_max_of_lt_right (inv_pos.2 hQ₁) : 0 < max Q₂ Q₁⁻¹)).subset
    (Set.iUnion₂_subset fun _ hQ ↦
      approxDomain_subset_of_le fun v i ↦ rpow_le_max_rpow_abs hQ₁ hQ.1 hQ.2 (c v i))

omit [Fintype ι] in
/-- **A bounded range of levels contributes finitely many subspaces `V(Q)`**: they are spans of
subsets of one finite set. This is how the levels below a threshold are disposed of in Layers 5.6
and 6.1. -/
theorem finite_image_approxSpan [Finite ι]
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ)
    {Q₁ Q₂ : ℝ} (hQ₁ : 0 < Q₁) : (approxSpan Sfin L c '' Set.Icc Q₁ Q₂).Finite := by
  refine (((finite_biUnion_approxDomain hLInf hLFin c (Q₂ := Q₂) hQ₁).finite_subsets).image
    (Submodule.span K)).subset ?_
  rintro _ ⟨Q, hQ, rfl⟩
  exact ⟨approxDomain Sfin L c Q,
    Set.subset_biUnion_of_mem (u := fun Q ↦ approxDomain Sfin L c Q) hQ, rfl⟩

end Approximation

/-! ### Acceptance criteria -/

section Tests

omit [NumberField K] [Fintype ι] in
/-- The coordinate forms take the value `0` or `1` at a standard basis vector. -/
private theorem apply_dualBasis_basisFun_le_one [Finite ι] [DecidableEq ι] (v : AbsoluteValue K ℝ)
    (i j : ι) : v ((Pi.basisFun K ι).dualBasis i (Pi.basisFun K ι j)) ≤ 1 := by
  rw [Basis.dualBasis_apply_self]
  split_ifs <;> simp

omit [Fintype ι] in
/-- At a level where every bound is at least `1`, the domain of the coordinate forms contains the
standard basis, so its rank is `#ι`. -/
private theorem approxSpan_dualBasis_eq_top [Finite ι] [DecidableEq ι]
    {Sfin : Finset (FinitePlace K)} {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ}
    (h : ∀ v i, 1 ≤ Q ^ c v i) :
    approxSpan Sfin (fun _ ↦ ⇑(Pi.basisFun K ι).dualBasis) c Q = ⊤ := by
  have hmem : ∀ j, Pi.basisFun K ι j ∈
      approxDomain Sfin (fun _ ↦ ⇑(Pi.basisFun K ι).dualBasis) c Q := by
    intro j
    refine ⟨fun v i ↦ (apply_dualBasis_basisFun_le_one v.1 i j).trans (h _ _),
      fun v _ i ↦ (apply_dualBasis_basisFun_le_one v.1 i j).trans (h _ _), fun v _ i ↦ ?_⟩
    rw [Pi.basisFun_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [eq_top_iff, ← (Pi.basisFun K ι).span_eq, approxSpan]
  exact Submodule.span_mono (Set.range_subset_iff.2 hmem)

/-- **Conformance: over `ℚ`, in one variable, the rank drops exactly past the level `1`.** With no
finite place, the coordinate form and `c = -1`, of weight `-1`, the domain of level `Q` is the set
of integers of absolute value at most `Q⁻¹`: it contains `1` for `Q ≤ 1` and is `{0}` for `Q > 1`.
So the conclusion of Lemma 7.5.12 holds from `Q > 1` on and fails at `Q = 1`: it is eventual, and
not uniform in the level. -/
example {Q : ℝ} (hQ : 0 < Q) :
    approxWeight (∅ : Finset (FinitePlace ℚ))
        (fun _ _ ↦ -1 : AbsoluteValue ℚ ℝ → Fin 1 → ℝ) = -1 ∧
      (finrank ℚ (approxSpan ∅ (fun _ ↦ ⇑(Pi.basisFun ℚ (Fin 1)).dualBasis) (fun _ _ ↦ -1) Q) = 1
        ↔ Q ≤ 1) := by
  refine ⟨?_, ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
  · have := InfinitePlace.sum_mult_eq (K := ℚ)
    rw [Module.finrank_self] at this
    simp only [approxWeight, Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul,
      Finset.card_empty, zero_smul, add_zero, mul_neg, mul_one, Finset.sum_neg_distrib, neg_inj]
    exact_mod_cast this
  · by_contra hcon
    push Not at hcon
    have hbot : approxSpan ∅ (fun _ ↦ ⇑(Pi.basisFun ℚ (Fin 1)).dualBasis)
        (fun _ _ ↦ (-1 : ℝ)) Q = ⊥ := by
      refine Submodule.span_eq_bot.2 fun x hx ↦ ?_
      obtain ⟨z, hz⟩ := FinitePlace.exists_eq_of_forall_apply_le_one fun v ↦
        hx.2.2 v (Finset.notMem_empty v) 0
      have hinf := hx.1 Rat.infinitePlace 0
      simp only [Rat.infinitePlace_apply, Basis.dualBasis_apply, Pi.basisFun_repr] at hinf
      have hlt : Q ^ (-1 : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hcon (by norm_num)
      have hn : ((Rat.ringOfIntegersEquiv z : ℤ) : ℚ) = x 0 := by
        rw [Rat.ringOfIntegersEquiv_apply_coe, ← hz]
      rw [← hn] at hinf
      have h1 : |((Rat.ringOfIntegersEquiv z : ℤ) : ℝ)| < 1 := by
        have := hinf.trans_lt hlt
        exact_mod_cast this
      have h0 : (Rat.ringOfIntegersEquiv z : ℤ) = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast h1)
      funext i
      rw [Subsingleton.elim i 0, ← hn, h0]
      simp
    rw [hbot, finrank_bot] at h
    exact zero_ne_one h
  · rw [approxSpan_dualBasis_eq_top fun _ _ ↦
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hQ h (by norm_num), finrank_top,
      finrank_fintype_fun_eq_card, Fintype.card_fin]

open scoped Classical in
/-- **Rejection: the weight must be negative, not merely nonpositive.** For the coordinate forms and
`c = 0`, of weight `0`, every domain contains the standard basis, so the rank is `#ι` at every
level and never drops. -/
example (Sfin : Finset (FinitePlace K)) :
    approxWeight Sfin (0 : AbsoluteValue K ℝ → ι → ℝ) = 0 ∧
      ¬ ∀ᶠ Q in atTop, finrank K (approxSpan Sfin (fun _ ↦ ⇑(Pi.basisFun K ι).dualBasis) 0 Q) <
        Fintype.card ι := by
  refine ⟨by simp [approxWeight], fun hev ↦ ?_⟩
  obtain ⟨Q, hQ⟩ := hev.exists
  rw [approxSpan_dualBasis_eq_top fun _ _ ↦ by simp, finrank_top,
    finrank_fintype_fun_eq_card] at hQ
  exact lt_irrefl _ hQ

open scoped Classical in
/-- **Rejection: the minima are counted at most `1`, not below `1`.** Over `ℚ`, in one variable,
with no finite place, the coordinate form and `c = 0`, the domain is `ℤ ∩ [-1, 1]`: its rank is `1`
and its only minimum is exactly `1`, so counting the minima below `1` would give `0`. -/
example {Q : ℝ} (hQ : 0 < Q) :
    finrank ℚ (approxSpan ∅ (fun _ ↦ ⇑(Pi.basisFun ℚ (Fin 1)).dualBasis) 0 Q) = 1 ∧
      successiveMinimum (approxModule ∅ (fun _ ↦ ⇑(Pi.basisFun ℚ (Fin 1)).dualBasis) 0 Q)
        (approxBody (fun _ ↦ ⇑(Pi.basisFun ℚ (Fin 1)).dualBasis) 0 Q) 0 = 1 := by
  set L : AbsoluteValue ℚ ℝ → Fin 1 → Dual ℚ (Fin 1 → ℚ) :=
    fun _ ↦ ⇑(Pi.basisFun ℚ (Fin 1)).dualBasis
  have hLInf : ∀ w : InfinitePlace ℚ, LinearIndependent ℚ (L w.1) :=
    fun _ ↦ (Pi.basisFun ℚ (Fin 1)).dualBasis.linearIndependent
  have hLFin : ∀ v ∈ (∅ : Finset (FinitePlace ℚ)), LinearIndependent ℚ (L v.1) := by simp
  have hrank : finrank ℚ (approxSpan ∅ L 0 Q) = 1 := by
    rw [approxSpan_dualBasis_eq_top fun _ _ ↦ by simp, finrank_top, finrank_fintype_fun_eq_card,
      Fintype.card_fin]
  refine ⟨hrank, le_antisymm ((successiveMinimum_approx_le_one_iff hLInf hLFin 0 hQ
    (by simp)).2 (by rw [hrank]; exact one_pos)) ?_⟩
  have hD : DiscreteTopology (approxLattice ∅ L 0 Q) :=
    discreteTopology_approxLattice hLFin 0 hQ.ne'
  have : DiscreteTopology (approxModule ∅ L 0 Q).mixedImage := hD
  have hZ : IsZLattice ℝ (approxLattice ∅ L 0 Q) := isZLattice_approxLattice hLFin 0 hQ.ne'
  have : IsZLattice ℝ (approxModule ∅ L 0 Q).mixedImage := hZ
  refine le_successiveMinimum _ (convex_approxBody L 0 Q) (fun x hx ↦ neg_mem_approxBody hx)
    ⟨0, mem_interior_iff_mem_nhds.2 (approxBody_mem_nhds_zero L 0 hQ)⟩
    (isBounded_approxBody hLInf 0 Q) (by simp) fun t ht x hx hind ↦ ?_
  obtain ⟨z, hz⟩ := FinitePlace.exists_eq_of_forall_apply_le_one fun v ↦
    (hx 0).1.2 v (Finset.notMem_empty v) 0
  have hn : ((Rat.ringOfIntegersEquiv z : ℤ) : ℚ) = x 0 0 := by
    rw [Rat.ringOfIntegersEquiv_apply_coe, ← hz]
  have hne : (Rat.ringOfIntegersEquiv z : ℤ) ≠ 0 := by
    intro h0
    refine hind.ne_zero 0 (funext fun i ↦ ?_)
    rw [Subsingleton.elim i 0, ← hn, h0]
    simp
  have hinf := (mem_smul_approxBody_iff ht).1 (hx 0).2 Rat.infinitePlace 0
  simp only [L, Fin.sum_univ_one, Basis.dualBasis_apply_self, ↓reduceIte, map_one, one_mul,
    normAtPlace_apply, Rat.infinitePlace_apply, Pi.zero_apply, Real.rpow_zero, mul_one] at hinf
  rw [← hn] at hinf
  have h1 : (1 : ℝ) ≤ |((Rat.ringOfIntegersEquiv z : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hne
  have : |((Rat.ringOfIntegersEquiv z : ℤ) : ℝ)| ≤ t := by exact_mod_cast hinf
  linarith

end Tests

end NumberField
