/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ApproximationRank
public import DiophantineApproximation.WedgeForm
public import Mathlib.Analysis.SpecialFunctions.Log.Base

-- Used only inside proofs.
import DiophantineApproximation.EvertseLemma
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# The wedge domain of an approximation domain

For a number field `K`, a domain `approxDomain Sfin L c Q` of `Kⁱ` (Layer 4.1), vectors
`x 0, …, x (#ι - 1)` realizing its successive minima `μ 0 ≤ ⋯ ≤ μ (#ι - 1)` over `K` (Layer 4.2)
and the vectors `y j = x j + ∑ l < j, ξ j l • x l` and bijections `π v` of Evertse's lemma
(Layer 4.4), applied with the weights `Q ^ c v i`, pass to the exterior power
`⋀^p Kⁱ = Set.powersetCard ι p → K`, `k + p = #ι`: the wedges `y J` of the `p`-subsets `J` of the
vector indices that meet the first `k` lie in an approximation domain for the wedges of the forms
(`WedgeForm.lean`) — Bombieri–Gubler's `S(Q)`, the book's (7.44) and (7.45). Its exponents depend
on `Q`, the minima and the bijections. Every minimum of that domain but the last is at most `1`,
because the wedges meeting the first `k` span a hyperplane, and the last is at least a constant
times `μ k / μ (k - 1)` by Minkowski's second theorem over `K`, from below in `⋀^p` and from above
in `Kⁱ` (Lemma 7.5.31). If the rank `R` of the domain is at least `1`, some `k` in `[R, #ι)` makes
`(μ (k - 1) / μ k) ^ (#ι - R)` at most `(μ (#ι - 1))⁻¹` (the book's (7.41)), and Layer 4.3 makes
that a negative power of `Q` when the weight is negative: the last minimum of the wedge domain is
then at least a positive power of `Q`.

## Main results

* `NumberField.wedgeExponent`: the exponents of the wedge domain.
* `NumberField.exists_plucker_mem_approxDomain_wedgeForms`: the wedges of Evertse's vectors that
  meet the first `k` indices lie in the wedge domain (Bombieri–Gubler 7.5.30, (7.44)–(7.45)), with
  a constant depending only on `K` and `#ι`.
* `NumberField.rpow_approxWeight_wedgeExponent`: the weight of the wedge domain, exactly, and
  `NumberField.rpow_approxWeight_wedgeExponent_le`: bounded by `(μ (k - 1) / μ k) ^ d` times a
  constant.
* `NumberField.exists_successiveMinimum_wedge`: Bombieri–Gubler, Lemma 7.5.31.
* `NumberField.exists_div_pow_le_inv`: the choice of `k`, (7.41).
* `NumberField.exists_successiveMinimum_wedge_pow`: the two together — the last minimum of the
  wedge domain to the power `d #ι (#ι - R)` is at least a constant times `Q ^ (-weight)`.
* `NumberField.InfinitePlace.not_isNonarchimedean`: an infinite place is archimedean.

## Implementation notes

⚠ **The wedge domain is an approximation domain whose exponents move with `Q`.** The book's `S(Q)`
bounds the wedge form of the forms `π v I` by `C μ_I Q ^ c(π v I)` at the infinite places, with an
extra factor `μ k / μ (k + 1)` (the book's indexing) on the top block, and by `Q ^ c(π v I)` at the
places of `S₀`. Here the forms are indexed by the `p`-subsets `T` of the form indices, the vector
indices are `π v⁻¹ T`, and the bound at an infinite place is written `Q ^ e` with
`e = ∑_{t ∈ T} c v t + logb Q (C μ_{π v⁻¹ T} ρ)`; for `Q > 1` that is the bound itself. So Layers
4.2 and 4.3 apply to `S(Q)` verbatim, with their constants — which see the wedge forms only through
the determinants — uniform in `Q`.

⚠ **No normalization at the infinite places.** The book raises each minimum to `ε v = [K_v : ℝ] / d`
so that the product over the infinite places is the minimum, (7.42). In Mathlib's normalization a
dilation by `λ` multiplies the bound at every infinite place by `λ`, so the minima enter each place
unnormalized, and `d` reappears as the exponent of Minkowski's second theorem.

⚠ **The refinement (7.45) is a statement about one factor.** A subset `J ≠ top` of the vector
indices contains an index `j₀ < k`, so in each term of the determinant one factor is at most
`μ j₀ ≤ μ (k - 1)` instead of the minimum of its form index, which is at least `μ k`; that alone
gains `μ (k - 1) / μ k`, with no need to order `J`.

⚠ **The constant of the wedge estimate depends only on `K` and `#ι`**, as Evertse's does: a
determinant of `p` terms costs `p!` and Evertse's constant to the `p`, and
`p! C ^ p ≤ #ι! max 1 C ^ #ι`. The constant of Lemma 7.5.31 depends on `Sfin`, the forms and `p`
as well, through Minkowski's theorem, and on nothing else.

⚠ **The weight is computed exactly.** Each form index lies in `e = (#ι - 1).choose (p - 1)` of the
`p`-subsets, each vector index likewise through `π v`, and exactly one wedge form comes from the top
block; so `Q` to the weight of the wedge domain is `Q ^ (e w)` times
`(C ^ M (∏ μ) ^ e μ (k - 1) / μ k) ^ d`, and Minkowski's upper bound `(∏ μ) ^ d ≪ Q ^ (-w)` leaves
`(μ (k - 1) / μ k) ^ d` up to a constant. This is the book's chain after (7.46), and it is the form
Layer 6.1 needs: once the exponents are rounded to a grid, a negative weight of the wedge domain is
what makes its rank eventually `M - 1`.

⚠ **The choice of `k` needs `R ≥ 1`, and any `k` with a large jump will do.** The book takes the
smallest `k` in `[R, n]` minimizing `λ k / λ (k + 1)`; the proof uses only that the jump is at
least the geometric mean, `λ (R - 1) ≤ 1` telescoping the product. Without `λ (R - 1) ≤ 1` no `k`
need exist.

⚠ **Two acceptance tests, on the choice of `k`.** For the minima `1/2, 2, 2, 8` of a domain of
rank `1` the jump at `k = 2` is `1` and fails (7.41), while the jump at `k = 1` meets it: the
choice matters. And for the minima `4, 8` of a domain of rank `0` no `k` meets it: the rank has to
be positive.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
7.5.30 and Lemma 7.5.31.

This is Layer 4.5 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Module NumberField NumberField.mixedEmbedding NumberField.InfinitePlace exteriorPower

open scoped Pointwise

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]

omit [NumberField K] in
/-- **An infinite place is archimedean**: `w (1 + 1) = 2`. -/
theorem InfinitePlace.not_isNonarchimedean (w : InfinitePlace K) : ¬ IsNonarchimedean w.1 := by
  intro h
  have h2 := h 1 1
  have : w.1 (1 + 1) = 2 := by
    have := w.map_natCast 2
    rw [Nat.cast_ofNat, Nat.cast_ofNat] at this
    rw [one_add_one_eq_two]
    exact this
  rw [this, map_one, max_self] at h2
  norm_num at h2

omit [NumberField K] [LinearOrder ι] in
/-- **A unitriangular change of a basis is a basis.** -/
theorem linearIndependent_add_sum_smul {x : Fin (Fintype.card ι) → ι → K}
    (hx : LinearIndependent K x) (ξ : Fin (Fintype.card ι) → Fin (Fintype.card ι) → K) :
    LinearIndependent K fun j ↦ x j + ∑ l ∈ Finset.Iio j, ξ j l • x l := by
  set y := fun j ↦ x j + ∑ l ∈ Finset.Iio j, ξ j l • x l
  have hmem : ∀ n, ∀ j : Fin (Fintype.card ι), (j : ℕ) < n →
      x j ∈ Submodule.span K (Set.range y) := by
    intro n
    induction n with
    | zero => intro j hj; omega
    | succ n ih =>
      intro j hj
      have hxj : x j = y j - ∑ l ∈ Finset.Iio j, ξ j l • x l := by simp [y]
      rw [hxj]
      refine Submodule.sub_mem _ (Submodule.subset_span ⟨j, rfl⟩)
        (Submodule.sum_mem _ fun l hl ↦ ?_)
      exact Submodule.smul_mem _ _ (ih l (by rw [Finset.mem_Iio] at hl; omega))
  have hsp : Submodule.span K (Set.range x) = ⊤ :=
    hx.span_eq_top_of_card_eq_finrank' (by simp)
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp)
  rw [← hsp, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact hmem _ j (Nat.lt_succ_self _)


open scoped Classical in
/-- **The exponents of the wedge domain** (Bombieri–Gubler 7.5.30–7.5.31). -/
noncomputable def wedgeExponent (c : AbsoluteValue K ℝ → ι → ℝ)
    (π : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι) (μ : ℕ → ℝ) (C Q : ℝ) (k p : ℕ)
    (v : AbsoluteValue K ℝ) (T : Set.powersetCard ι p) : ℝ :=
  ∑ t ∈ (T : Finset ι), c v t + if IsNonarchimedean v then 0 else Real.logb Q
    (C * (∏ t ∈ (T : Finset ι), μ ((π v).symm t)) *
      if ∀ t ∈ (T : Finset ι), k ≤ ((π v).symm t : ℕ) then μ (k - 1) / μ k else 1)

section Exponent

variable {c : AbsoluteValue K ℝ → ι → ℝ} {π : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι}
  {μ : ℕ → ℝ} {C Q : ℝ} {k p : ℕ}

omit [NumberField K] in
private theorem rpow_wedgeExponent_of_isNonarchimedean (hQ : 0 < Q) {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) (T : Set.powersetCard ι p) :
    Q ^ wedgeExponent c π μ C Q k p v T = ∏ t ∈ (T : Finset ι), Q ^ c v t := by
  simp only [wedgeExponent, hv, ↓reduceIte, add_zero]
  exact Real.rpow_sum_of_pos hQ _ _

omit [NumberField K] in
private theorem rpow_wedgeExponent_of_not_isNonarchimedean (hQ : 0 < Q) (hQ1 : Q ≠ 1)
    {v : AbsoluteValue K ℝ} (hv : ¬ IsNonarchimedean v) (T : Set.powersetCard ι p)
    (hpos : 0 < C * (∏ t ∈ (T : Finset ι), μ ((π v).symm t)) *
      if ∀ t ∈ (T : Finset ι), k ≤ ((π v).symm t : ℕ) then μ (k - 1) / μ k else 1) :
    Q ^ wedgeExponent c π μ C Q k p v T = (∏ t ∈ (T : Finset ι), Q ^ c v t) *
      (C * (∏ t ∈ (T : Finset ι), μ ((π v).symm t)) *
        if ∀ t ∈ (T : Finset ι), k ≤ ((π v).symm t : ℕ) then μ (k - 1) / μ k else 1) := by
  classical
  simp only [wedgeExponent, hv, ↓reduceIte]
  rw [Real.rpow_add hQ, Real.rpow_sum_of_pos hQ, Real.rpow_logb hQ hQ1 hpos]

end Exponent

/-- **The book's (7.44) and (7.45) for one term of a determinant**: of `p` minima, each paired with
a vector index and a form index, the product is at most that over the form indices, and if every
form index is in the top block `{k, …}` while some vector index is below it, by a factor
`μ (k - 1) / μ k` less. -/
private theorem prod_min_le {N k p : ℕ} {μ : ℕ → ℝ} (hμm : MonotoneOn μ (Set.Iio N))
    (hμp : ∀ j < N, 0 < μ j) {i j : Fin p → ℕ} (hi : ∀ b, i b < N) (hj : ∀ b, j b < N)
    (hk : ∃ b, j b < k) (P : Prop) [Decidable P] (hP : P → ∀ b, k ≤ i b) :
    ∏ b, min (μ (i b)) (μ (j b)) ≤ (if P then μ (k - 1) / μ k else 1) * ∏ b, μ (i b) := by
  have hm0 : ∀ b, 0 ≤ min (μ (i b)) (μ (j b)) := fun b ↦
    le_min (hμp _ (hi b)).le (hμp _ (hj b)).le
  split_ifs with hPt
  · have htop := hP hPt
    obtain ⟨b₀, hb₀⟩ := hk
    have hkN : k < N := (htop b₀).trans_lt (hi b₀)
    have hk0 : 0 < μ k := hμp k hkN
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ b₀),
      ← Finset.mul_prod_erase _ (fun b ↦ μ (i b)) (Finset.mem_univ b₀), ← mul_assoc]
    refine mul_le_mul ?_ (Finset.prod_le_prod₀ (fun b _ ↦ hm0 b) fun b _ ↦ min_le_left _ _)
      (Finset.prod_nonneg fun b _ ↦ hm0 b) ?_
    · calc min (μ (i b₀)) (μ (j b₀)) ≤ μ (j b₀) := min_le_right _ _
        _ ≤ μ (k - 1) := hμm (hj b₀) (by simp only [Set.mem_Iio]; omega) (by omega)
        _ = μ (k - 1) / μ k * μ k := by field_simp
        _ ≤ μ (k - 1) / μ k * μ (i b₀) := by
          refine mul_le_mul_of_nonneg_left (hμm hkN (hi b₀) (htop b₀)) ?_
          exact div_nonneg (hμp _ (by omega)).le hk0.le
    · exact mul_nonneg (div_nonneg (hμp _ (by omega)).le hk0.le) (hμp _ (hi b₀)).le
  · rw [one_mul]
    exact Finset.prod_le_prod₀ (fun b _ ↦ hm0 b) fun b _ ↦ min_le_left _ _


variable (K ι) in
/-- **The wedges of Evertse's vectors lie in the wedge domain** (Bombieri–Gubler 7.5.30, (7.44)
and (7.45)). -/
theorem exists_plucker_mem_approxDomain_wedgeForms : ∃ C : ℝ, 0 < C ∧
    ∀ (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)),
    (∀ w : InfinitePlace K, LinearIndependent K (L w.1)) →
    (∀ v ∈ Sfin, LinearIndependent K (L v.1)) →
    ∀ (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ), 1 < Q →
    ∀ (x : Fin (Fintype.card ι) → ι → K), LinearIndependent K x →
    ∀ μ : ℕ → ℝ, MonotoneOn μ (Set.Iio (Fintype.card ι)) →
    (∀ j < Fintype.card ι, 0 < μ j) →
    (∀ j, x j ∈ approxModule Sfin L c Q ∧
      (fun i ↦ mixedEmbedding K (x j i)) ∈ μ j • approxBody L c Q) →
    ∃ ξ : Fin (Fintype.card ι) → Fin (Fintype.card ι) → K,
      (∀ i j, ∀ v : FinitePlace K, v ∉ Sfin → v (ξ i j) ≤ 1) ∧
      ∃ π : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι, ∀ k p : ℕ,
        ∀ J : Set.powersetCard (Fin (Fintype.card ι)) p, (∃ j ∈ J, (j : ℕ) < k) →
          plucker p ((fun j ↦ x j + ∑ l ∈ Finset.Iio j, ξ j l • x l) ∘
              Set.powersetCard.ofFinEmbEquiv.symm J) ∈
            approxDomain Sfin (fun v ↦ wedgeForms (L v) p) (wedgeExponent c π μ C Q k p) Q := by
  obtain ⟨CE, hCE, hev⟩ := exists_evertse K ι
  refine ⟨(Fintype.card ι).factorial * max 1 CE ^ Fintype.card ι, by positivity, ?_⟩
  intro Sfin L hLInf hLFin c Q hQ x hx μ hμm hμp hxm
  classical
  have hQ0 : 0 < Q := by linarith
  have hna : ∀ v : FinitePlace K, IsNonarchimedean v.1 := fun v a b ↦ v.add_le a b
  set μ' : AbsoluteValue K ℝ → Fin (Fintype.card ι) → ℝ :=
    fun v j ↦ if IsNonarchimedean v then 1 else μ j with hμ'
  set ν : AbsoluteValue K ℝ → ι → ℝ := fun v i ↦ Q ^ c v i with hν
  have hmono : ∀ v, Monotone (μ' v) := fun v i j hij ↦ by
    by_cases hv : IsNonarchimedean v
    · simp [hμ', hv]
    · simp only [hμ', hv, ↓reduceIte]
      exact hμm i.2 j.2 hij
  have hinf : ∀ (w : InfinitePlace K) i j, w (L w.1 i (x j)) ≤ ν w.1 i * μ' w.1 j := by
    intro w i j
    have h := ((mem_smul_approxBody_iff (hμp j j.2)).1 (hxm j).2) w i
    rw [normAtPlace_sum_mixedEmbedding] at h
    simp only [hμ', hν, InfinitePlace.not_isNonarchimedean w, ↓reduceIte]
    linarith
  have hfin : ∀ v ∈ Sfin, ∀ i j, v (L v.1 i (x j)) ≤ ν v.1 i * μ' v.1 j := by
    intro v hv i j
    have h := (hxm j).1.1 v hv i
    simp only [hμ', hν, hna v, ↓reduceIte, mul_one]
    rwa [abs_of_pos hQ0] at h
  obtain ⟨ξ, hξ, π, hπinf, hπfin⟩ := hev Sfin L hLInf hLFin x hx μ' ν hmono
    (fun v i ↦ Real.rpow_pos_of_pos hQ0 _) hinf hfin
  refine ⟨ξ, hξ, π, fun k p J hJ ↦ ?_⟩
  set y := fun j ↦ x j + ∑ l ∈ Finset.Iio j, ξ j l • x l with hy
  set eJ := Set.powersetCard.ofFinEmbEquiv.symm J with heJ
  obtain ⟨j₀, hj₀J, hj₀k⟩ := hJ
  obtain ⟨b₀, hb₀⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem J j₀).2 hj₀J
  have hbJ : ∃ b, ((eJ b : Fin (Fintype.card ι)) : ℕ) < k := ⟨b₀, by rw [heJ, hb₀]; exact hj₀k⟩
  have hpN : p ≤ Fintype.card ι := by
    have := Finset.card_le_univ (J : Finset (Fin (Fintype.card ι)))
    rwa [Set.powersetCard.card_eq, Fintype.card_fin] at this
  -- the products over `σ` of a subset in order, as products over the subset
  have hperm : ∀ (T : Set.powersetCard ι p) (σ : Equiv.Perm (Fin p)) (g : ι → ℝ),
      ∏ b, g (Set.powersetCard.ofFinEmbEquiv.symm T (σ b)) = ∏ t ∈ (T : Finset ι), g t :=
    fun T σ g ↦ (Equiv.prod_comp σ fun a ↦ g (Set.powersetCard.ofFinEmbEquiv.symm T a)).trans
      (Set.powersetCard.prod_comp_ofFinEmbEquiv_symm T g)
  refine ⟨fun w T ↦ ?_, fun v hv T ↦ ?_, fun v hv s ↦ ?_⟩
  · -- an infinite place: Evertse's bound, a sum of `p!` terms, and the top block
    set eT := Set.powersetCard.ofFinEmbEquiv.symm T with heT
    have hTne : ∀ t ∈ (T : Finset ι), ∃ a, eT a = t := fun t ht ↦
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T t).2 ht
    set P : Prop := ∀ t ∈ (T : Finset ι), k ≤ ((π w.1).symm t : ℕ) with hPdef
    have hμT : 0 < ∏ t ∈ (T : Finset ι), μ ((π w.1).symm t) :=
      Finset.prod_pos fun t _ ↦ hμp _ ((π w.1).symm t).2
    have hρ : 0 < if P then μ (k - 1) / μ k else 1 := by
      split_ifs with hP
      · obtain ⟨a, -⟩ : ∃ a : Fin p, True := ⟨⟨0, by
          have := b₀.2; omega⟩, trivial⟩
        have hk := hP (eT a) ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T _).1
          ⟨a, rfl⟩)
        have hkN := ((π w.1).symm (eT a)).2
        exact div_pos (hμp _ (by omega)) (hμp _ (by omega))
      · exact one_pos
    have hC0 : 0 < (Fintype.card ι).factorial * max 1 CE ^ Fintype.card ι := by positivity
    rw [wedgeForms_plucker, rpow_wedgeExponent_of_not_isNonarchimedean hQ0 hQ.ne'
      (InfinitePlace.not_isNonarchimedean w) T (by positivity)]
    have hterm : ∀ σ : Equiv.Perm (Fin p),
        ∏ b, w.1 ((Matrix.of fun a b ↦ L w.1 (eT a) ((y ∘ eJ) b)) (σ b) b) ≤
          max 1 CE ^ p * ((∏ t ∈ (T : Finset ι), Q ^ c w.1 t) *
            ((if P then μ (k - 1) / μ k else 1) * ∏ t ∈ (T : Finset ι), μ ((π w.1).symm t))) := by
      intro σ
      have hb : ∀ b, w.1 ((Matrix.of fun a b ↦ L w.1 (eT a) ((y ∘ eJ) b)) (σ b) b) ≤
          CE * Q ^ c w.1 (eT (σ b)) * min (μ ((π w.1).symm (eT (σ b)))) (μ (eJ b)) := by
        intro b
        have h := hπinf w ((π w.1).symm (eT (σ b))) (eJ b)
        simp only [Equiv.apply_symm_apply, hμ', hν, InfinitePlace.not_isNonarchimedean w,
          ↓reduceIte] at h
        exact h
      refine (Finset.prod_le_prod₀ (fun b _ ↦ w.1.nonneg _) fun b _ ↦ hb b).trans ?_
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, hperm T σ fun t ↦ Q ^ c w.1 t,
        ← hperm T σ fun t ↦ μ ((π w.1).symm t)]
      have hmin := prod_min_le (N := Fintype.card ι) hμm hμp
        (i := fun b ↦ (((π w.1).symm (eT (σ b)) : Fin (Fintype.card ι)) : ℕ))
        (j := fun b ↦ ((eJ b : Fin (Fintype.card ι)) : ℕ)) (fun b ↦ Fin.is_lt _)
        (fun b ↦ Fin.is_lt _) hbJ P fun hP b ↦
          hP _ ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T _).1 ⟨σ b, rfl⟩)
      have hQT : 0 ≤ ∏ t ∈ (T : Finset ι), Q ^ c w.1 t :=
        Finset.prod_nonneg fun t _ ↦ (Real.rpow_pos_of_pos hQ0 _).le
      calc CE ^ p * (∏ t ∈ (T : Finset ι), Q ^ c w.1 t) *
            ∏ b, min (μ ((π w.1).symm (eT (σ b)))) (μ (eJ b))
          ≤ CE ^ p * (∏ t ∈ (T : Finset ι), Q ^ c w.1 t) * ((if P then μ (k - 1) / μ k else 1) *
              ∏ b, μ ((π w.1).symm (eT (σ b)))) :=
            mul_le_mul_of_nonneg_left hmin (mul_nonneg (by positivity) hQT)
        _ ≤ max 1 CE ^ p * ((∏ t ∈ (T : Finset ι), Q ^ c w.1 t) *
              ((if P then μ (k - 1) / μ k else 1) * ∏ b, μ ((π w.1).symm (eT (σ b))))) := by
            rw [mul_assoc]
            refine mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ hCE.le (le_max_right _ _) _) ?_
            rw [hperm T σ fun t ↦ μ ((π w.1).symm t)]
            positivity
    refine (w.1.apply_det_le _ hterm).trans ?_
    have hfac : ((p.factorial : ℕ) : ℝ) * max 1 CE ^ p ≤
        (Fintype.card ι).factorial * max 1 CE ^ Fintype.card ι := by
      gcongr
      · exact le_max_left _ _
    calc (p.factorial : ℝ) * (max 1 CE ^ p * ((∏ t ∈ (T : Finset ι), Q ^ c w.1 t) *
          ((if P then μ (k - 1) / μ k else 1) * ∏ t ∈ (T : Finset ι), μ ((π w.1).symm t))))
        = (p.factorial * max 1 CE ^ p) * ((∏ t ∈ (T : Finset ι), Q ^ c w.1 t) *
          ((if P then μ (k - 1) / μ k else 1) * ∏ t ∈ (T : Finset ι), μ ((π w.1).symm t))) := by
          ring
      _ ≤ ((Fintype.card ι).factorial * max 1 CE ^ Fintype.card ι) *
          ((∏ t ∈ (T : Finset ι), Q ^ c w.1 t) *
            ((if P then μ (k - 1) / μ k else 1) * ∏ t ∈ (T : Finset ι), μ ((π w.1).symm t))) := by
          refine mul_le_mul_of_nonneg_right hfac ?_
          have hQT : 0 ≤ ∏ t ∈ (T : Finset ι), Q ^ c w.1 t :=
            Finset.prod_nonneg fun t _ ↦ (Real.rpow_pos_of_pos hQ0 _).le
          positivity
      _ = _ := by ring
  · -- a place of `Sfin`: the ultrametric bound, exactly
    rw [wedgeForms_plucker, rpow_wedgeExponent_of_isNonarchimedean hQ0 (hna v) T]
    refine AbsoluteValue.apply_det_le_of_isNonarchimedean (hna v) _
      (Finset.prod_nonneg fun t _ ↦ (Real.rpow_pos_of_pos hQ0 _).le) fun σ ↦ ?_
    rw [← hperm T σ fun t ↦ Q ^ c v.1 t]
    refine Finset.prod_le_prod₀ (fun b _ ↦ v.1.nonneg _) fun b _ ↦ ?_
    have h := hπfin v hv ((π v.1).symm (Set.powersetCard.ofFinEmbEquiv.symm T (σ b))) (eJ b)
    simp only [Equiv.apply_symm_apply, hμ', hν, hna v, ↓reduceIte, min_self, mul_one] at h
    exact h
  · -- outside `Sfin`: the wedge of integral vectors is integral
    have hyint : ∀ j i, v (y j i) ≤ 1 := fun j i ↦ by
      simp only [hy, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine (hna v _ _).trans (max_le ((hxm j).1.2 v hv i) ?_)
      refine Finset.sum_induction _ (fun z ↦ v z ≤ 1)
        (fun a b ha hb ↦ (hna v a b).trans (max_le ha hb)) (by simp) fun l _ ↦ ?_
      rw [map_mul]
      calc v (ξ j l) * v (x l i) ≤ 1 * 1 :=
            mul_le_mul (hξ j l v hv) ((hxm l).1.2 v hv i) (v.1.nonneg _) zero_le_one
        _ = 1 := one_mul 1
    exact apply_plucker_le_one (hna v) (fun b i ↦ hyint _ i) s


open scoped Classical in
/-- Exactly one `p`-subset of forms comes from the top block of vectors. -/
private theorem prod_ite_topBlock (σ : Fin (Fintype.card ι) ≃ ι) {k p : ℕ}
    (h : k + p = Fintype.card ι) (r : ℝ) :
    ∏ T : Set.powersetCard ι p,
      (if ∀ t ∈ (T : Finset ι), k ≤ (σ.symm t : ℕ) then r else 1) = r := by
  set T₀ := Set.powersetCard.map p σ.toEmbedding (topBlock h) with hT₀
  have hT : ∀ T : Set.powersetCard ι p, (∀ t ∈ (T : Finset ι), k ≤ (σ.symm t : ℕ)) ↔ T = T₀ := by
    intro T
    constructor
    · intro hT
      refine Set.powersetCard.eq_iff_subset.2 fun t ht ↦ ?_
      exact (Set.powersetCard.mem_map_iff_mem_range p σ.toEmbedding (topBlock h) t).2
        ⟨σ.symm t, (mem_topBlock h).2 (hT t ht), by simp⟩
    · rintro rfl t ht
      obtain ⟨j, hj, rfl⟩ := (Set.powersetCard.mem_map_iff_mem_range p σ.toEmbedding _ t).1 ht
      simpa using (mem_topBlock h).1 hj
  simp [hT]

omit [LinearOrder ι] in
/-- A product over the forms of values at the corresponding vectors is the product over the
vectors. -/
private theorem prod_symm_eq_prod_range (σ : Fin (Fintype.card ι) ≃ ι) (μ : ℕ → ℝ) :
    ∏ t, μ (σ.symm t) = ∏ j ∈ Finset.range (Fintype.card ι), μ j := by
  rw [Equiv.prod_comp σ.symm (fun j ↦ μ j), Fin.prod_univ_eq_prod_range]

/-- **The weight of the wedge domain, exactly** (Bombieri–Gubler 7.5.31): `Q` to it is `Q` to
`e` times the weight of the domain, times `(C ^ M (∏ μ) ^ e μ (k - 1) / μ k) ^ d`, where `M` is the
number of `p`-subsets and `e = (#ι - 1).choose (p - 1)`. -/
theorem rpow_approxWeight_wedgeExponent (Sfin : Finset (FinitePlace K))
    (c : AbsoluteValue K ℝ → ι → ℝ) (π : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι)
    {μ : ℕ → ℝ} {C Q : ℝ} {k p : ℕ} (hQ : 1 < Q) (hC : 0 < C)
    (hμ : ∀ j < Fintype.card ι, 0 < μ j) (h : k + p = Fintype.card ι) (hp : 0 < p) :
    Q ^ approxWeight Sfin (wedgeExponent c π μ C Q k p) =
      Q ^ ((Fintype.card ι - 1).choose (p - 1) * approxWeight Sfin c) *
        (C ^ Fintype.card (Set.powersetCard ι p) *
          (∏ j ∈ Finset.range (Fintype.card ι), μ j) ^ (Fintype.card ι - 1).choose (p - 1) *
            (μ (k - 1) / μ k)) ^ finrank ℚ K := by
  classical
  have hQ0 : 0 < Q := by linarith
  set e := (Fintype.card ι - 1).choose (p - 1) with he
  set r := μ (k - 1) / μ k with hr
  have hr0 : 0 < r := div_pos (hμ _ (by omega)) (hμ _ (by omega))
  set X : ℝ := C ^ Fintype.card (Set.powersetCard ι p) *
    (∏ j ∈ Finset.range (Fintype.card ι), μ j) ^ e * r with hX
  have hprod : 0 < ∏ j ∈ Finset.range (Fintype.card ι), μ j :=
    Finset.prod_pos fun j hj ↦ hμ j (Finset.mem_range.1 hj)
  have hX0 : 0 < X := by positivity
  have hB : ∀ (v : AbsoluteValue K ℝ) (T : Set.powersetCard ι p),
      0 < C * (∏ t ∈ (T : Finset ι), μ ((π v).symm t)) *
        (if ∀ t ∈ (T : Finset ι), k ≤ ((π v).symm t : ℕ) then r else 1) := fun v T ↦ by
    have : 0 < ∏ t ∈ (T : Finset ι), μ ((π v).symm t) :=
      Finset.prod_pos fun t _ ↦ hμ _ ((π v).symm t).2
    split_ifs <;> positivity
  have hprodB : ∀ v : AbsoluteValue K ℝ, ∏ T : Set.powersetCard ι p,
      (C * (∏ t ∈ (T : Finset ι), μ ((π v).symm t)) *
        (if ∀ t ∈ (T : Finset ι), k ≤ ((π v).symm t : ℕ) then r else 1)) = X := fun v ↦ by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Set.powersetCard.prod_prod_mem _ hp, prod_symm_eq_prod_range, prod_ite_topBlock _ h]
  have hfin : ∀ v : FinitePlace K, ∑ T : Set.powersetCard ι p,
      wedgeExponent c π μ C Q k p v.1 T = e * ∑ i, c v.1 i := fun v ↦ by
    have hna : IsNonarchimedean v.1 := fun a b ↦ v.add_le a b
    simp only [wedgeExponent, hna, ↓reduceIte, add_zero]
    rw [Set.powersetCard.sum_sum_mem _ hp, nsmul_eq_mul]
  have hinf : ∀ w : InfinitePlace K, ∑ T : Set.powersetCard ι p,
      wedgeExponent c π μ C Q k p w.1 T = e * ∑ i, c w.1 i + Real.logb Q X := fun w ↦ by
    simp only [wedgeExponent, InfinitePlace.not_isNonarchimedean w, ↓reduceIte]
    rw [Finset.sum_add_distrib, Set.powersetCard.sum_sum_mem _ hp, nsmul_eq_mul, ← hprodB w.1,
      Real.logb_prod _ _ fun T _ ↦ (hB w.1 T).ne']
  have hw : approxWeight Sfin (wedgeExponent c π μ C Q k p) =
      e * approxWeight Sfin c + Real.logb Q X * finrank ℚ K := by
    have h1 : ∀ w : InfinitePlace K, (w.mult : ℝ) * (e * ∑ i, c w.1 i + Real.logb Q X) =
        e * (w.mult * ∑ i, c w.1 i) + Real.logb Q X * w.mult := fun w ↦ by ring
    simp only [approxWeight, hinf, hfin, h1, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← InfinitePlace.sum_mult_eq, Nat.cast_sum]
    ring
  rw [hw, Real.rpow_add hQ0, Real.rpow_mul_natCast hQ0.le, Real.rpow_logb hQ0 hQ.ne' hX0]


open scoped Classical in
/-- **The weight of the wedge domain is at most a constant times the jump of the minima**
(Bombieri–Gubler 7.5.31, the chain after (7.46)): with `μ` the minima of the domain, Minkowski's
second theorem over `K` from above cancels everything in the exact weight but
`(μ (k - 1) / μ k) ^ d`. The constant depends on `K`, `Sfin`, the forms, `C` and `p`, and not on
`c`, `Q` or the bijections. -/
theorem rpow_approxWeight_wedgeExponent_le {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (π : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι) {C Q : ℝ} {k p : ℕ} (hQ : 1 < Q)
    (hC : 0 < C) (h : k + p = Fintype.card ι) (hp : 0 < p) :
    Q ^ approxWeight Sfin (wedgeExponent c π
        (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)) C Q k p) ≤
      C ^ (Fintype.card (Set.powersetCard ι p) * finrank ℚ K) *
        (2 ^ (finrank ℚ K * Fintype.card ι) *
          (∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ Fintype.card ι) /
            approxConst Sfin L) ^ (Fintype.card ι - 1).choose (p - 1) *
        (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) (k - 1) /
          successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) k) ^ finrank ℚ K := by
  have hQ0 : 0 < Q := by linarith
  set M := Fintype.card (Set.powersetCard ι p) with hM
  set e := (Fintype.card ι - 1).choose (p - 1) with he
  set d := finrank ℚ K with hd
  set a₂ : ℝ := 2 ^ (d * Fintype.card ι) *
    (∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ Fintype.card ι) /
      approxConst Sfin L with ha₂
  set lam := successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) with hlam
  have hD : DiscreteTopology (approxLattice Sfin L c Q) :=
    discreteTopology_approxLattice hLFin c hQ0.ne'
  have : DiscreteTopology (approxModule Sfin L c Q).mixedImage := hD
  have hZ : IsZLattice ℝ (approxLattice Sfin L c Q) := isZLattice_approxLattice hLFin c hQ0.ne'
  have : IsZLattice ℝ (approxModule Sfin L c Q).mixedImage := hZ
  have hB₂ : (interior (approxBody L c Q)).Nonempty :=
    ⟨0, mem_interior_iff_mem_nhds.2 (approxBody_mem_nhds_zero L c hQ0)⟩
  have hlampos : ∀ j < Fintype.card ι, 0 < lam j := fun j hj ↦
    successiveMinimum_pos _ (convex_approxBody L c Q) (fun x hx ↦ neg_mem_approxBody hx) hB₂
      (isBounded_approxBody hLInf c Q) hj
  have hup := prod_successiveMinimum_approx_le hLInf hLFin c hQ0
  have hwt := rpow_approxWeight_wedgeExponent Sfin c π (μ := lam) hQ hC hlampos h hp
  set Pr := ∏ j ∈ Finset.range (Fintype.card ι), lam j with hPr
  set r := lam (k - 1) / lam k with hr
  have hr0 : 0 < r := div_pos (hlampos _ (by omega)) (hlampos _ (by omega))
  have hPr0 : 0 < Pr := Finset.prod_pos fun j hj ↦ hlampos j (Finset.mem_range.1 hj)
  have hQw : Q ^ ((e : ℝ) * approxWeight Sfin c) * (Q ^ (-approxWeight Sfin c)) ^ e = 1 := by
    rw [← Real.rpow_mul_natCast hQ0.le, ← Real.rpow_add hQ0]
    ring_nf
    exact Real.rpow_zero Q
  have hPre : (Pr ^ d) ^ e ≤ (a₂ * Q ^ (-approxWeight Sfin c)) ^ e :=
    pow_le_pow_left₀ (by positivity) hup e
  rw [hwt, mul_pow, mul_pow, pow_right_comm Pr e d, pow_mul C M d]
  calc Q ^ ((e : ℝ) * approxWeight Sfin c) * ((C ^ M) ^ d * (Pr ^ d) ^ e * r ^ d)
      ≤ Q ^ ((e : ℝ) * approxWeight Sfin c) * ((C ^ M) ^ d *
          (a₂ * Q ^ (-approxWeight Sfin c)) ^ e * r ^ d) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPre (by positivity)) (by positivity)) (by positivity)
    _ = (C ^ M) ^ d * a₂ ^ e * r ^ d *
          (Q ^ ((e : ℝ) * approxWeight Sfin c) * (Q ^ (-approxWeight Sfin c)) ^ e) := by ring
    _ = (C ^ M) ^ d * a₂ ^ e * r ^ d := by rw [hQw, mul_one]

variable (K ι) in
open scoped Classical in
/-- **Bombieri–Gubler, Lemma 7.5.31**: in the wedge domain of Evertse's vectors built on vectors
realizing the minima, every minimum but the last is at most `1`, and the last is at least a
constant times `μ k / μ (k - 1)`. -/
theorem exists_successiveMinimum_wedge : ∃ C : ℝ, 0 < C ∧
    ∀ (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)),
    (∀ w : InfinitePlace K, LinearIndependent K (L w.1)) →
    (∀ v ∈ Sfin, LinearIndependent K (L v.1)) →
    ∀ {k p : ℕ}, k + p = Fintype.card ι → 0 < p →
    ∃ A : ℝ, 0 < A ∧ ∀ (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ), 1 < Q →
    ∀ x : Fin (Fintype.card ι) → ι → K, LinearIndependent K x →
    (∀ j, x j ∈ approxModule Sfin L c Q ∧ (fun i ↦ mixedEmbedding K (x j i)) ∈
      successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) j • approxBody L c Q) →
    ∃ ξ : Fin (Fintype.card ι) → Fin (Fintype.card ι) → K,
      (∀ i j, ∀ v : FinitePlace K, v ∉ Sfin → v (ξ i j) ≤ 1) ∧
      ∃ π : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι,
        (∀ J : Set.powersetCard (Fin (Fintype.card ι)) p, (∃ j ∈ J, (j : ℕ) < k) →
          plucker p ((fun j ↦ x j + ∑ l ∈ Finset.Iio j, ξ j l • x l) ∘
              Set.powersetCard.ofFinEmbEquiv.symm J) ∈
            approxDomain Sfin (fun v ↦ wedgeForms (L v) p) (wedgeExponent c π
              (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)) C Q k p) Q) ∧
        (∀ m < Fintype.card (Set.powersetCard ι p) - 1,
          successiveMinimum (approxModule Sfin (fun v ↦ wedgeForms (L v) p) (wedgeExponent c π
              (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)) C Q k p) Q)
            (approxBody (fun v ↦ wedgeForms (L v) p) (wedgeExponent c π
              (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)) C Q k p) Q) m ≤ 1) ∧
        A ≤ (successiveMinimum (approxModule Sfin (fun v ↦ wedgeForms (L v) p) (wedgeExponent c π
              (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)) C Q k p) Q)
            (approxBody (fun v ↦ wedgeForms (L v) p) (wedgeExponent c π
              (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)) C Q k p) Q)
            (Fintype.card (Set.powersetCard ι p) - 1) *
          (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) (k - 1) /
            successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) k)) ^ finrank ℚ K := by
  obtain ⟨C, hC, hmem⟩ := exists_plucker_mem_approxDomain_wedgeForms K ι
  refine ⟨C, hC, fun Sfin L hLInf hLFin k p hkp hp ↦ ?_⟩
  set M := Fintype.card (Set.powersetCard ι p) with hM
  set N := Fintype.card ι with hN
  set e := (N - 1).choose (p - 1) with he
  set d := finrank ℚ K with hd
  have hLInf' : ∀ w : InfinitePlace K, LinearIndependent K (wedgeForms (L w.1) p) := fun w ↦
    linearIndependent_wedgeForms (hLInf w) p
  have hLFin' : ∀ v ∈ Sfin, LinearIndependent K (wedgeForms (L v.1) p) := fun v hv ↦
    linearIndependent_wedgeForms (hLFin v hv) p
  set a₁ : ℝ := 2 ^ (d * M) / ((d * M).factorial * integralBasisHouse K ^ (d * M) *
    approxConst Sfin fun v ↦ wedgeForms (L v) p) with ha₁
  set a₂ : ℝ := 2 ^ (d * N) * (∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ N) /
    approxConst Sfin L with ha₂
  have ha₁0 : 0 < a₁ := by
    have := approxConst_pos (L := fun v ↦ wedgeForms (L v) p) hLInf' hLFin'
    have := one_le_integralBasisHouse (K := K)
    positivity
  have ha₂0 : 0 < a₂ := by
    have := approxConst_pos hLInf hLFin
    have : ∀ v ∈ Sfin, (0 : ℝ) < (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ N := fun v _ ↦
      pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h ↦ by
        simp [Ideal.absNorm_eq_zero_iff, v.maximalIdeal.ne_bot] at h)) _
    have := Finset.prod_pos this
    positivity
  refine ⟨a₁ / (C ^ (M * d) * a₂ ^ e), by positivity, fun c Q hQ x hx hxm ↦ ?_⟩
  have hQ0 : 0 < Q := by linarith
  set lam := successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) with hlam
  have hD : DiscreteTopology (approxLattice Sfin L c Q) :=
    discreteTopology_approxLattice hLFin c hQ0.ne'
  have : DiscreteTopology (approxModule Sfin L c Q).mixedImage := hD
  have hZ : IsZLattice ℝ (approxLattice Sfin L c Q) := isZLattice_approxLattice hLFin c hQ0.ne'
  have : IsZLattice ℝ (approxModule Sfin L c Q).mixedImage := hZ
  have hB₂ : (interior (approxBody L c Q)).Nonempty :=
    ⟨0, mem_interior_iff_mem_nhds.2 (approxBody_mem_nhds_zero L c hQ0)⟩
  have hlampos : ∀ j < N, 0 < lam j := fun j hj ↦
    successiveMinimum_pos _ (convex_approxBody L c Q) (fun x hx ↦ neg_mem_approxBody hx) hB₂
      (isBounded_approxBody hLInf c Q) hj
  have hlammono : MonotoneOn lam (Set.Iio N) := fun i _ j hj hij ↦
    successiveMinimum_le_of_le _ (convex_approxBody L c Q) (fun x hx ↦ neg_mem_approxBody hx) hB₂
      (isBounded_approxBody hLInf c Q) hij hj
  obtain ⟨ξ, hξ, π, hπ⟩ := hmem Sfin L hLInf hLFin c Q hQ x hx lam hlammono hlampos hxm
  refine ⟨ξ, hξ, π, fun J hJ ↦ hπ k p J hJ, ?_⟩
  set c' := wedgeExponent c π lam C Q k p with hc'
  set lamW := successiveMinimum (approxModule Sfin (fun v ↦ wedgeForms (L v) p) c' Q)
    (approxBody (fun v ↦ wedgeForms (L v) p) c' Q) with hlamW
  have hyind := linearIndependent_add_sum_smul hx ξ
  -- the span of the wedge domain contains the wedges meeting the first `k` indices
  have hspan : wedgeSpan k p (fun j ↦ x j + ∑ l ∈ Finset.Iio j, ξ j l • x l) ≤
      approxSpan Sfin (fun v ↦ wedgeForms (L v) p) c' Q := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨J, hJ, rfl⟩
    exact Submodule.subset_span (hπ k p J hJ)
  have hcodim := finrank_wedgeSpan_add_one hyind hkp
  have hrank := Submodule.finrank_mono hspan
  have hle1 : ∀ m < M - 1, lamW m ≤ 1 := fun m hm ↦
    (successiveMinimum_approx_le_one_iff (L := fun v ↦ wedgeForms (L v) p) hLInf' hLFin' c' hQ0
      (by omega)).2 (by omega)
  refine ⟨hle1, ?_⟩
  -- Minkowski's second theorem over `K` from below in `⋀^p`, and the weight from above
  have hlow := le_prod_successiveMinimum_approx (L := fun v ↦ wedgeForms (L v) p) hLInf' hLFin'
    c' hQ0
  have hWle := rpow_approxWeight_wedgeExponent_le hLInf hLFin c π hQ hC hkp hp
  set r := lam (k - 1) / lam k with hr
  have hr0 : 0 < r := div_pos (hlampos _ (by omega)) (hlampos _ (by omega))
  have hW0 : 0 < Q ^ approxWeight Sfin c' := Real.rpow_pos_of_pos hQ0 _
  have hlamW0 : ∀ m, 0 ≤ lamW m := fun m ↦ successiveMinimum_nonneg _ _ m
  -- the product of the wedge minima is at most the last
  have hM1 : 1 ≤ M := by omega
  have hPle : ∏ m ∈ Finset.range M, lamW m ≤ lamW (M - 1) := by
    rw [show M = M - 1 + 1 by omega, Finset.prod_range_succ, Nat.add_sub_cancel]
    exact mul_le_of_le_one_left (hlamW0 _) (Finset.prod_le_one₀ (fun m _ ↦ hlamW0 m)
      fun m hm ↦ hle1 m (Finset.mem_range.1 hm))
  have hP0 : 0 ≤ ∏ m ∈ Finset.range M, lamW m := Finset.prod_nonneg fun m _ ↦ hlamW0 m
  rw [Real.rpow_neg hQ0.le] at hlow
  have h1 : a₁ ≤ (∏ m ∈ Finset.range M, lamW m) ^ d * (C ^ (M * d) * a₂ ^ e * r ^ d) :=
    ((mul_inv_le_iff₀ hW0).1 hlow).trans (mul_le_mul_of_nonneg_left hWle (pow_nonneg hP0 d))
  have hCa : 0 < C ^ (M * d) * a₂ ^ e := mul_pos (pow_pos hC _) (pow_pos ha₂0 _)
  rw [div_le_iff₀ hCa]
  calc a₁ ≤ (∏ m ∈ Finset.range M, lamW m) ^ d * (C ^ (M * d) * a₂ ^ e * r ^ d) := h1
    _ = ((∏ m ∈ Finset.range M, lamW m) * r) ^ d * (C ^ (M * d) * a₂ ^ e) := by
      rw [mul_pow]; ring
    _ ≤ (lamW (M - 1) * r) ^ d * (C ^ (M * d) * a₂ ^ e) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg hP0 hr0.le)
        (mul_le_mul_of_nonneg_right hPle hr0.le) d) hCa.le


omit [NumberField K] [Fintype ι] [LinearOrder ι] in
/-- The quotients of consecutive minima telescope. -/
private theorem prod_Ico_div {μ : ℕ → ℝ} {R N : ℕ} (hR : 0 < R) (hμ : ∀ j < N, 0 < μ j) :
    ∀ n, R + n ≤ N → ∏ k ∈ Finset.Ico R (R + n), μ (k - 1) / μ k = μ (R - 1) / μ (R + n - 1) := by
  intro n
  induction n with
  | zero =>
    intro h
    rw [add_zero, Finset.Ico_self, Finset.prod_empty, div_self (hμ _ (by omega)).ne']
  | succ n ih =>
    intro h
    rw [← add_assoc, Finset.prod_Ico_succ_top (by omega), ih (by omega),
      show R + n + 1 - 1 = R + n by omega]
    have h1 := hμ (R + n - 1) (by omega)
    have h2 := hμ (R + n) (by omega)
    field_simp

omit [NumberField K] [Fintype ι] [LinearOrder ι] in
/-- **The choice of `k`** (Bombieri–Gubler (7.41)): if the `R`-th minimum, `R ≥ 1`, is at most
`1` and the first `N` are positive, some `k` in `[R, N)` has
`(μ (k - 1) / μ k) ^ (N - R) ≤ (μ (N - 1))⁻¹`. -/
theorem exists_div_pow_le_inv {μ : ℕ → ℝ} {R N : ℕ} (hR : 0 < R) (hRN : R < N)
    (hμ : ∀ j < N, 0 < μ j) (hR1 : μ (R - 1) ≤ 1) :
    ∃ k, R ≤ k ∧ k < N ∧ (μ (k - 1) / μ k) ^ (N - R) ≤ (μ (N - 1))⁻¹ := by
  obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image (Finset.Ico R N) (fun k ↦ μ (k - 1) / μ k)
    ⟨R, Finset.mem_Ico.2 ⟨le_rfl, hRN⟩⟩
  obtain ⟨hRk, hkN⟩ := Finset.mem_Ico.1 hk
  refine ⟨k, hRk, hkN, ?_⟩
  have hpos : ∀ j ∈ Finset.Ico R N, 0 < μ (j - 1) / μ j := fun j hj ↦ by
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hj
    exact div_pos (hμ _ (by omega)) (hμ _ h2)
  calc (μ (k - 1) / μ k) ^ (N - R) = ∏ _j ∈ Finset.Ico R N, μ (k - 1) / μ k := by
        rw [Finset.prod_const, Nat.card_Ico]
    _ ≤ ∏ j ∈ Finset.Ico R N, μ (j - 1) / μ j :=
        Finset.prod_le_prod₀ (fun _ _ ↦ (hpos k hk).le) fun j hj ↦ hmin j hj
    _ = μ (R - 1) / μ (N - 1) := by
        have := prod_Ico_div hR hμ (N - R) (by omega)
        rwa [show R + (N - R) = N by omega] at this
    _ ≤ (μ (N - 1))⁻¹ := by
        rw [div_eq_mul_inv]
        exact mul_le_of_le_one_left (inv_pos.2 (hμ _ (by omega))).le hR1


omit [NumberField K] [LinearOrder ι] in
/-- A product of numbers in `(0, 1]` is at most each of them. -/
private theorem prod_min_one_le {a : ℕ → ℝ} (ha : ∀ j, 0 < a j) {n j : ℕ} (hj : j < n) :
    ∏ i ∈ Finset.range n, min 1 (a i) ≤ a j := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hj)]
  exact (mul_le_of_le_one_right (lt_min one_pos (ha j)).le (Finset.prod_le_one₀
    (fun i _ ↦ (lt_min one_pos (ha i)).le) fun i _ ↦ min_le_left _ _)).trans (min_le_right _ _)

variable (K ι) in
open scoped Classical in
/-- **Bombieri–Gubler, Lemma 7.5.31, with the choice of `k`** (7.41): for a domain of rank `R`,
`1 ≤ R < #ι`, some `k` in `[R, #ι)` makes every minimum of the wedge domain in `⋀^(#ι - k)` but
the last at most `1`, and the last to the power `d #ι (#ι - R)` at least a constant times
`Q ^ (-weight)` — for negative weight, a positive power of `Q`. -/
theorem exists_successiveMinimum_wedge_pow : ∃ C : ℝ, 0 < C ∧
    ∀ (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)),
    (∀ w : InfinitePlace K, LinearIndependent K (L w.1)) →
    (∀ v ∈ Sfin, LinearIndependent K (L v.1)) →
    ∃ A : ℝ, 0 < A ∧ ∀ (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ), 1 < Q →
    0 < finrank K (approxSpan Sfin L c Q) → finrank K (approxSpan Sfin L c Q) < Fintype.card ι →
    ∀ x : Fin (Fintype.card ι) → ι → K, LinearIndependent K x →
    (∀ j, x j ∈ approxModule Sfin L c Q ∧ (fun i ↦ mixedEmbedding K (x j i)) ∈
      successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) j • approxBody L c Q) →
    ∃ k, finrank K (approxSpan Sfin L c Q) ≤ k ∧ k < Fintype.card ι ∧
    ∃ ξ : Fin (Fintype.card ι) → Fin (Fintype.card ι) → K,
      (∀ i j, ∀ v : FinitePlace K, v ∉ Sfin → v (ξ i j) ≤ 1) ∧
      ∃ π : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι,
        (∀ J : Set.powersetCard (Fin (Fintype.card ι)) (Fintype.card ι - k),
          (∃ j ∈ J, (j : ℕ) < k) →
          plucker (Fintype.card ι - k) ((fun j ↦ x j + ∑ l ∈ Finset.Iio j, ξ j l • x l) ∘
              Set.powersetCard.ofFinEmbEquiv.symm J) ∈
            approxDomain Sfin (fun v ↦ wedgeForms (L v) (Fintype.card ι - k)) (wedgeExponent c π
              (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)) C Q k
                (Fintype.card ι - k)) Q) ∧
        (∀ m < Fintype.card (Set.powersetCard ι (Fintype.card ι - k)) - 1,
          successiveMinimum (approxModule Sfin (fun v ↦ wedgeForms (L v) (Fintype.card ι - k))
              (wedgeExponent c π (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q))
                C Q k (Fintype.card ι - k)) Q)
            (approxBody (fun v ↦ wedgeForms (L v) (Fintype.card ι - k)) (wedgeExponent c π
              (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)) C Q k
                (Fintype.card ι - k)) Q) m ≤ 1) ∧
        A * Q ^ (-approxWeight Sfin c) ≤
          successiveMinimum (approxModule Sfin (fun v ↦ wedgeForms (L v) (Fintype.card ι - k))
              (wedgeExponent c π (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q))
                C Q k (Fintype.card ι - k)) Q)
            (approxBody (fun v ↦ wedgeForms (L v) (Fintype.card ι - k)) (wedgeExponent c π
              (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)) C Q k
                (Fintype.card ι - k)) Q)
            (Fintype.card (Set.powersetCard ι (Fintype.card ι - k)) - 1) ^
              (finrank ℚ K * Fintype.card ι *
                (Fintype.card ι - finrank K (approxSpan Sfin L c Q))) := by
  obtain ⟨C, hC, hwedge⟩ := exists_successiveMinimum_wedge K ι
  refine ⟨C, hC, fun Sfin L hLInf hLFin ↦ ?_⟩
  set N := Fintype.card ι with hN
  set d := finrank ℚ K with hd
  have hA : ∀ k, ∃ A : ℝ, 0 < A ∧ (k < N → ∀ (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ), 1 < Q →
      ∀ x : Fin N → ι → K, LinearIndependent K x →
      (∀ j, x j ∈ approxModule Sfin L c Q ∧ (fun i ↦ mixedEmbedding K (x j i)) ∈
        successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) j • approxBody L c Q) →
      ∃ ξ : Fin N → Fin N → K, (∀ i j, ∀ v : FinitePlace K, v ∉ Sfin → v (ξ i j) ≤ 1) ∧
        ∃ π : AbsoluteValue K ℝ → Fin N ≃ ι,
          (∀ J : Set.powersetCard (Fin N) (N - k), (∃ j ∈ J, (j : ℕ) < k) →
            plucker (N - k) ((fun j ↦ x j + ∑ l ∈ Finset.Iio j, ξ j l • x l) ∘
                Set.powersetCard.ofFinEmbEquiv.symm J) ∈
              approxDomain Sfin (fun v ↦ wedgeForms (L v) (N - k)) (wedgeExponent c π
                (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)) C Q k
                  (N - k)) Q) ∧
          (∀ m < Fintype.card (Set.powersetCard ι (N - k)) - 1,
            successiveMinimum (approxModule Sfin (fun v ↦ wedgeForms (L v) (N - k))
                (wedgeExponent c π (successiveMinimum (approxModule Sfin L c Q)
                  (approxBody L c Q)) C Q k (N - k)) Q)
              (approxBody (fun v ↦ wedgeForms (L v) (N - k)) (wedgeExponent c π
                (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)) C Q k
                  (N - k)) Q) m ≤ 1) ∧
          A ≤ (successiveMinimum (approxModule Sfin (fun v ↦ wedgeForms (L v) (N - k))
                (wedgeExponent c π (successiveMinimum (approxModule Sfin L c Q)
                  (approxBody L c Q)) C Q k (N - k)) Q)
              (approxBody (fun v ↦ wedgeForms (L v) (N - k)) (wedgeExponent c π
                (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q)) C Q k
                  (N - k)) Q)
              (Fintype.card (Set.powersetCard ι (N - k)) - 1) *
            (successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) (k - 1) /
              successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) k)) ^ d) := by
    intro k
    by_cases hk : k < N
    · obtain ⟨A, hA0, hAP⟩ := hwedge Sfin L hLInf hLFin (k := k) (p := N - k) (by omega)
        (by omega)
      exact ⟨A, hA0, fun _ ↦ hAP⟩
    · exact ⟨1, one_pos, fun h ↦ absurd h hk⟩
  choose A hA0 hAP using hA
  set B := ∏ i ∈ Finset.range N, min 1 (A i) with hB
  have hB0 : 0 < B := Finset.prod_pos fun i _ ↦ lt_min one_pos (hA0 i)
  have hB1 : B ≤ 1 := Finset.prod_le_one₀ (fun i _ ↦ (lt_min one_pos (hA0 i)).le)
    fun i _ ↦ min_le_left _ _
  set a₁ : ℝ := 2 ^ (d * N) / ((d * N).factorial * integralBasisHouse K ^ (d * N) *
    approxConst Sfin L) with ha₁
  have ha₁0 : 0 < a₁ := by
    have := approxConst_pos hLInf hLFin
    have := one_le_integralBasisHouse (K := K)
    positivity
  refine ⟨B ^ (N * N) * a₁, by positivity, fun c Q hQ hR hRN x hx hxm ↦ ?_⟩
  have hQ0 : 0 < Q := by linarith
  set R := finrank K (approxSpan Sfin L c Q) with hRdef
  set lam := successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) with hlam
  have hD : DiscreteTopology (approxLattice Sfin L c Q) :=
    discreteTopology_approxLattice hLFin c hQ0.ne'
  have : DiscreteTopology (approxModule Sfin L c Q).mixedImage := hD
  have hZ : IsZLattice ℝ (approxLattice Sfin L c Q) := isZLattice_approxLattice hLFin c hQ0.ne'
  have : IsZLattice ℝ (approxModule Sfin L c Q).mixedImage := hZ
  have hB₂ : (interior (approxBody L c Q)).Nonempty :=
    ⟨0, mem_interior_iff_mem_nhds.2 (approxBody_mem_nhds_zero L c hQ0)⟩
  have hlampos : ∀ j < N, 0 < lam j := fun j hj ↦
    successiveMinimum_pos _ (convex_approxBody L c Q) (fun x hx ↦ neg_mem_approxBody hx) hB₂
      (isBounded_approxBody hLInf c Q) hj
  have hlamR : lam (R - 1) ≤ 1 :=
    (successiveMinimum_approx_le_one_iff hLInf hLFin c hQ0 (by omega)).2 (by omega)
  obtain ⟨k, hRk, hkN, hr⟩ := exists_div_pow_le_inv hR hRN hlampos hlamR
  obtain ⟨ξ, hξ, π, hmemJ, hle1, hlast⟩ := hAP k hkN c Q hQ x hx hxm
  refine ⟨k, hRk, hkN, ξ, hξ, π, hmemJ, hle1, ?_⟩
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hlastN := le_successiveMinimum_approx_pow hLInf hLFin c hQ0
  set t := successiveMinimum (approxModule Sfin (fun v ↦ wedgeForms (L v) (N - k))
    (wedgeExponent c π lam C Q k (N - k)) Q) (approxBody (fun v ↦ wedgeForms (L v) (N - k))
      (wedgeExponent c π lam C Q k (N - k)) Q)
    (Fintype.card (Set.powersetCard ι (N - k)) - 1) with ht
  set r := lam (k - 1) / lam k with hrdef
  set sN := lam (N - 1) with hsN
  have ht0 : 0 ≤ t := successiveMinimum_nonneg _ _ _
  have hr0 : 0 < r := div_pos (hlampos _ (by omega)) (hlampos _ hkN)
  have hs0 : 0 < sN := hlampos _ (by omega)
  have hBA : B ^ (N * N) ≤ A k ^ (N * (N - R)) :=
    (pow_le_pow_of_le_one hB0.le hB1 (Nat.mul_le_mul_left N (Nat.sub_le N R))).trans
      (pow_le_pow_left₀ hB0.le (prod_min_one_le hA0 hkN) _)
  have h1 : A k ^ (N * (N - R)) ≤ t ^ (d * N * (N - R)) * (r ^ (N - R)) ^ (d * N) := by
    calc A k ^ (N * (N - R)) ≤ ((t * r) ^ d) ^ (N * (N - R)) :=
          pow_le_pow_left₀ (hA0 k).le hlast _
      _ = t ^ (d * N * (N - R)) * (r ^ (N - R)) ^ (d * N) := by
          rw [← pow_mul, mul_pow, ← pow_mul, mul_assoc d N (N - R),
            show (N - R) * (d * N) = d * (N * (N - R)) by ring]
  have h2 : (r ^ (N - R)) ^ (d * N) ≤ sN⁻¹ ^ (d * N) := pow_le_pow_left₀ (by positivity) hr _
  calc B ^ (N * N) * a₁ * Q ^ (-approxWeight Sfin c)
      = B ^ (N * N) * (a₁ * Q ^ (-approxWeight Sfin c)) := mul_assoc _ _ _
    _ ≤ A k ^ (N * (N - R)) * sN ^ (d * N) :=
        mul_le_mul hBA hlastN (mul_pos ha₁0 (Real.rpow_pos_of_pos hQ0 _)).le
          (pow_pos (hA0 k) _).le
    _ ≤ t ^ (d * N * (N - R)) * (r ^ (N - R)) ^ (d * N) * sN ^ (d * N) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ t ^ (d * N * (N - R)) * sN⁻¹ ^ (d * N) * sN ^ (d * N) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)
    _ = t ^ (d * N * (N - R)) := by
        rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hs0.ne', one_pow, mul_one]

end NumberField

section Tests

/-- Four minima `1/2, 2, 2, 8` of a domain of rank `1`. -/
private noncomputable def minima4 (j : ℕ) : ℝ := if j = 0 then 1 / 2 else if j = 3 then 8 else 2

/-- **Not every `k` in `[R, #ι)` will do** (7.41): for the minima `1/2, 2, 2, 8`, rank `1`, the
jump at `k = 2` is `1` and fails the bound `(μ (k-1) / μ k) ^ 3 ≤ (μ 3)⁻¹ = 1/8`, while the jump
at `k = 1` meets it. -/
example : ¬ (minima4 1 / minima4 2) ^ (4 - 1) ≤ (minima4 3)⁻¹ ∧
    (minima4 0 / minima4 1) ^ (4 - 1) ≤ (minima4 3)⁻¹ := by
  norm_num [minima4]

/-- Two minima `4, 8` of a domain of rank `0`. -/
private noncomputable def minima2 (j : ℕ) : ℝ := if j = 0 then 4 else 8

/-- **The choice of `k` needs the rank to be positive**: for the minima `4, 8`, of a domain of
rank `0`, no `k` in `[1, 2)` meets the bound, since `μ 0 = 4 > 1`. -/
example : ¬ ∃ k, 1 ≤ k ∧ k < 2 ∧ (minima2 (k - 1) / minima2 k) ^ (2 - 1) ≤ (minima2 (2 - 1))⁻¹ := by
  rintro ⟨k, h1, h2, h⟩
  obtain rfl : k = 1 := by omega
  norm_num [minima2] at h

end Tests
