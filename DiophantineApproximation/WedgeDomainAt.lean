/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.WedgeExponentBound

/-!
# The wedge domain with the minima at one place

The wedge domain of Layer 4.5 (`WedgeDomain.lean`) carries the minima `μ` at every infinite place,
read through one bijection `π v` per place from Evertse's lemma. Rounding those exponents to a grid
(Layer 6.1) then costs `#ι! ^ r` grids for the bijections, `r` the number of infinite places: the
`n d` in the exponent of the quantitative count. Evertse–Schlickewei 2002 avoid it by putting all
the minima at one place `v₀`, where Davenport's lemma (their § 9) needs one permutation only.

Here the place is an infinite place `w₀` with `mult w₀ ∣ [K : ℚ]`, `a = [K : ℚ] / mult w₀`, and the
move costs nothing but a constant. A vector `x j` realizing the `j`-th minimum `μ j` at every
infinite place is replaced by `β j • x j`, where Minkowski's first theorem for one scalar gives a
nonzero integer `β j` with `|β j|_w ≤ μ j⁻¹` at `w ≠ w₀` and `|β j|_{w₀} ≤ c μ j ^ (a - 1)`; the
product formula balances because `mult w₀ (a - 1) = [K : ℚ] - mult w₀`. The new vectors satisfy the
original bounds at every place but `w₀`, and `c μ j ^ a` times them at `w₀`. Evertse's lemma, run
with minima at `w₀` alone, then has only one bijection that matters, and the wedge domain
`NumberField.wedgeExponentAt` has the exponents of the domain plus a constant at every infinite
place, and `a` times the minima correction at `w₀` alone. Its weight is that of the wedge domain of
Layer 4.5 exactly (`NumberField.rpow_approxWeight_wedgeExponentAt`), so Layer 4.5's bounds on it
apply verbatim.

## Main results

* `NumberField.exists_ne_zero_le_of_unitConst_le`: Minkowski's first theorem for one scalar at
  the infinite places, with the constant `NumberField.unitConst K = 2 ^ [K : ℚ] √|D_K|`.
* `NumberField.exists_mult_dvd_finrank`: an infinite place whose multiplicity divides `[K : ℚ]`.
* `NumberField.exists_balance`: the scalar that moves a minimum to `w₀`.
* `NumberField.exists_plucker_mem_approxDomain_wedgeForms_at`: the wedges of Evertse's vectors
  built on the balanced vectors lie in the wedge domain at `w₀`, with one bijection.
* `NumberField.rpow_approxWeight_wedgeExponentAt`: its weight, exactly as in Layer 4.5.

## Implementation notes

⚠ **The place is infinite, not finite.** Evertse–Schlickewei need `v₀` nonarchimedean to keep
Davenport's coefficients at most `1` ((9.31)): their constants are absolute. Evertse's lemma over a
fixed field has a constant at the archimedean places anyway (`evertseConst`), so an infinite `w₀`
costs nothing more, and moving the minima there needs a scalar from Minkowski's theorem only, not
`S`-units with a controlled regulator, which a finite `v₀` would.

⚠ **`a` is an integer.** If `K` has a real place, `w₀` is real and `a = [K : ℚ]`; otherwise every
place is complex, `[K : ℚ]` is even and `a = [K : ℚ] / 2`. An integer `a` keeps the grid of the
minima at `w₀` on the same mesh as the constant (`MinimaGrid.lean`).

## References

J.-H. Evertse and H. P. Schlickewei, "A quantitative version of the absolute subspace theorem",
*J. reine angew. Math.* **548** (2002), 21–127, § 9 and Lemmas 17.2, 18.1.

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
7.5.29–7.5.31.

This is part of Layer 6.1 of the `DiophantineApproximation` roadmap, and item Q1.8c of the
`QuantitativeSubspace` roadmap.
-/

@[expose] public section

open Module NumberField NumberField.mixedEmbedding NumberField.InfinitePlace exteriorPower

open scoped Pointwise

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-! ### One scalar -/

variable (K) in
/-- **The constant of Minkowski's theorem for one scalar**, `2 ^ [K : ℚ] √|D_K|`. -/
noncomputable def unitConst : ℝ :=
  2 ^ finrank ℚ K * √|(discr K : ℝ)|

theorem one_le_unitConst : 1 ≤ unitConst K := by
  have hD : (1 : ℝ) ≤ |(discr K : ℝ)| := by exact_mod_cast Int.one_le_abs (discr_ne_zero K)
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) (Real.one_le_sqrt.2 hD)

open scoped Classical in
/-- The constant of the coordinate form on `K¹`. -/
theorem approxConst_proj (Sfin : Finset (FinitePlace K)) :
    approxConst Sfin (fun _ _ ↦ (LinearMap.proj () : Dual K (Unit → K))) =
      2 ^ InfinitePlace.nrRealPlaces K * Real.pi ^ InfinitePlace.nrComplexPlaces K /
        ZLattice.covolume (mixedEmbedding.integerLattice K) := by
  have hid : LinearMap.pi (fun _ : Unit ↦ (LinearMap.proj () : Dual K (Unit → K))) =
      LinearMap.id := rfl
  simp [approxConst, hid]

/-- **Minkowski's first theorem for one scalar at the infinite places.** If the product of
positive bounds `B w` is at least `unitConst K`, some nonzero integer `β` has
`|β|_w ^ mult w ≤ B w` at every infinite place. This is the domain of Layer 4.1 for the coordinate
form on `K¹` and no finite places: its first minimum is at most `1`. -/
theorem exists_ne_zero_le_of_unitConst_le {B : InfinitePlace K → ℝ} (hB : ∀ w, 0 < B w)
    (h : unitConst K ≤ ∏ w, B w) :
    ∃ β : K, β ≠ 0 ∧ (∀ v : FinitePlace K, v β ≤ 1) ∧
      ∀ w : InfinitePlace K, w β ^ w.mult ≤ B w := by
  classical
  set L₀ : AbsoluteValue K ℝ → Unit → Dual K (Unit → K) := fun _ _ ↦ LinearMap.proj ()
    with hL₀
  set c : AbsoluteValue K ℝ → Unit → ℝ := fun a _ ↦
    Function.extend (fun w : InfinitePlace K ↦ w.1) (fun w ↦ Real.log (B w) / w.mult) 0 a
    with hc
  have hc' : ∀ (w : InfinitePlace K) i, c w.1 i = Real.log (B w) / w.mult := fun w i ↦
    Subtype.val_injective.extend_apply _ _ _
  set Q := Real.exp 1 with hQ
  have hQ0 : 0 < Q := Real.exp_pos 1
  have hLI : ∀ a, LinearIndependent K (L₀ a) := fun a ↦ linearIndependent_unique_iff.2 fun h0 ↦ by
    have := LinearMap.congr_fun h0 fun _ ↦ 1
    simp [hL₀] at this
  have hw : approxWeight ∅ c = ∑ w, Real.log (B w) := by
    rw [approxWeight, Finset.sum_empty, add_zero]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    simp only [Finset.univ_unique, Finset.sum_singleton, PUnit.default_eq_unit, hc' w ()]
    field_simp [w.mult_pos.ne']
  have hpow : ∀ (w : InfinitePlace K) (a : ℝ), 0 ≤ a → a ≤ Q ^ c w.1 () →
      a ^ w.mult ≤ B w := fun w a ha hle ↦ by
    have hm : (0 : ℝ) < w.mult := by exact_mod_cast w.mult_pos
    rw [hc' w (), hQ, Real.exp_one_rpow] at hle
    calc a ^ w.mult ≤ Real.exp (Real.log (B w) / w.mult) ^ w.mult := pow_le_pow_left₀ ha hle _
      _ = B w := by
          rw [← Real.exp_nat_mul, mul_div_cancel₀ _ hm.ne', Real.exp_log (hB w)]
  have hprod := prod_successiveMinimum_approx_le (Sfin := ∅) (L := L₀) (fun w ↦ hLI w.1)
    (fun v hv ↦ absurd hv (Finset.notMem_empty v)) c hQ0
  simp only [Fintype.card_unit, Finset.range_one, Finset.prod_singleton, mul_one, pow_one,
    Finset.prod_empty] at hprod
  rw [approxConst_proj, hw] at hprod
  have hQB : Q ^ (-∑ w, Real.log (B w)) = (∏ w, B w)⁻¹ := by
    rw [hQ, Real.exp_one_rpow, Real.exp_neg, Real.exp_sum]
    simp only [Real.exp_log (hB _)]
  rw [hQB] at hprod
  have hBpos : 0 < ∏ w, B w := Finset.prod_pos fun w _ ↦ hB w
  have hcov : ZLattice.covolume (mixedEmbedding.integerLattice K) ≤ √|(discr K : ℝ)| := by
    rw [mixedEmbedding.covolume_integerLattice]
    exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))
  have hcov0 := ZLattice.covolume_pos (mixedEmbedding.integerLattice K)
  have hpi : (1 : ℝ) ≤
      2 ^ InfinitePlace.nrRealPlaces K * Real.pi ^ InfinitePlace.nrComplexPlaces K :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two)
      (one_le_pow₀ (by linarith [Real.pi_gt_three]))
  have hRHS : 2 ^ finrank ℚ K /
      (2 ^ InfinitePlace.nrRealPlaces K * Real.pi ^ InfinitePlace.nrComplexPlaces K /
        ZLattice.covolume (mixedEmbedding.integerLattice K)) * (∏ w, B w)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hBpos, div_div_eq_mul_div]
    refine (div_le_of_le_mul₀ (by positivity) (zero_le_one.trans one_le_unitConst) ?_).trans h
    rw [unitConst]
    calc 2 ^ finrank ℚ K * ZLattice.covolume (mixedEmbedding.integerLattice K)
        ≤ 2 ^ finrank ℚ K * √|(discr K : ℝ)| := mul_le_mul_of_nonneg_left hcov (by positivity)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hpi
  have hμ0 := successiveMinimum_nonneg (approxModule ∅ L₀ c Q) (approxBody L₀ c Q) 0
  have hμ : successiveMinimum (approxModule ∅ L₀ c Q) (approxBody L₀ c Q) 0 ≤ 1 :=
    (pow_le_one_iff_of_nonneg hμ0 (finrank_pos (R := ℚ) (M := K)).ne').1 (hprod.trans hRHS)
  rw [successiveMinimum_approx_le_one_iff (fun w ↦ hLI w.1)
    (fun v hv ↦ absurd hv (Finset.notMem_empty v)) c hQ0 (by simp)] at hμ
  obtain ⟨y, hy, hy0⟩ : ∃ y ∈ approxDomain ∅ L₀ c Q, y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : approxSpan ∅ L₀ c Q = ⊥ := Submodule.span_eq_bot.2 hcon
    rw [h0, finrank_bot] at hμ
    exact lt_irrefl _ hμ
  exact ⟨y (), fun h0 ↦ hy0 (funext fun _ ↦ h0), fun v ↦ hy.2.2 v (Finset.notMem_empty v) (),
    fun w ↦ hpow w _ (apply_nonneg _ _) (hy.1 w ())⟩

/-- **An infinite place whose multiplicity divides the degree**: a real place if there is one,
and otherwise any place, every place being complex and the degree even. -/
theorem exists_mult_dvd_finrank : ∃ w₀ : InfinitePlace K, w₀.mult ∣ finrank ℚ K := by
  by_cases h : ∃ w : InfinitePlace K, w.IsReal
  · obtain ⟨w, hw⟩ := h
    exact ⟨w, by simp [InfinitePlace.mult, hw]⟩
  · push Not at h
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
    have hm : ∀ w : InfinitePlace K, w.mult = 2 := fun w ↦ by
      simp [InfinitePlace.mult, h w]
    refine ⟨w, ?_⟩
    rw [hm, ← InfinitePlace.sum_mult_eq]
    exact Finset.dvd_sum fun w _ ↦ by rw [hm]

/-- **The scalar that moves a minimum to one place.** For an infinite place `w₀` with
`a mult w₀ = [K : ℚ]` and `μ > 0`, some nonzero integer `β` has `|β|_w μ ≤ 1` at every other
infinite place and `|β|_{w₀} ≤ unitConst K · μ ^ (a - 1)`: the product formula balances because
the other places carry `[K : ℚ] - mult w₀ = (a - 1) mult w₀` in total. -/
theorem exists_balance (w₀ : InfinitePlace K) {a : ℕ} (ha : a * w₀.mult = finrank ℚ K) {μ : ℝ}
    (hμ : 0 < μ) :
    ∃ β : K, β ≠ 0 ∧ (∀ v : FinitePlace K, v β ≤ 1) ∧
      (∀ w : InfinitePlace K, w ≠ w₀ → w β * μ ≤ 1) ∧ w₀ β ≤ unitConst K * μ ^ (a - 1) := by
  classical
  set U := unitConst K with hU
  have hU1 : 1 ≤ U := one_le_unitConst
  have hm₀ : 0 < w₀.mult := w₀.mult_pos
  set B : InfinitePlace K → ℝ := fun w ↦
    if w = w₀ then (U * μ ^ (a - 1)) ^ w₀.mult else μ⁻¹ ^ w.mult with hB
  have hBpos : ∀ w, 0 < B w := fun w ↦ by
    simp only [hB]
    split_ifs <;> positivity
  have hsum : ∑ w ∈ Finset.univ.erase w₀, w.mult = (a - 1) * w₀.mult := by
    have h1 := Finset.add_sum_erase Finset.univ (fun w : InfinitePlace K ↦ w.mult)
      (Finset.mem_univ w₀)
    rw [InfinitePlace.sum_mult_eq, ← ha] at h1
    rw [Nat.sub_mul, one_mul]
    omega
  have hprod : ∏ w, B w = U ^ w₀.mult := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w₀)]
    have h2 : ∏ w ∈ Finset.univ.erase w₀, B w = μ⁻¹ ^ ((a - 1) * w₀.mult) := by
      rw [← hsum, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_congr rfl fun w hw ↦ by
        simp only [hB, Finset.ne_of_mem_erase hw, ↓reduceIte]
    rw [h2]
    simp only [hB, ↓reduceIte]
    rw [pow_mul, ← mul_pow, mul_assoc, ← mul_pow, mul_inv_cancel₀ hμ.ne', one_pow, mul_one]
  obtain ⟨β, hβ0, hβint, hβ⟩ := exists_ne_zero_le_of_unitConst_le hBpos
    (hprod ▸ le_self_pow₀ hU1 hm₀.ne')
  refine ⟨β, hβ0, hβint, fun w hw ↦ ?_, ?_⟩
  · have h := hβ w
    simp only [hB, hw, ↓reduceIte] at h
    have := (pow_le_pow_iff_left₀ (apply_nonneg _ _) (by positivity) w.mult_pos.ne').1 h
    calc w β * μ ≤ μ⁻¹ * μ := mul_le_mul_of_nonneg_right this hμ.le
      _ = 1 := inv_mul_cancel₀ hμ.ne'
  · have h := hβ w₀
    simp only [hB, ↓reduceIte] at h
    exact (pow_le_pow_iff_left₀ (apply_nonneg _ _) (by positivity) hm₀.ne').1 h

/-! ### Scaling vectors -/

omit [NumberField K] in
/-- Scaling vectors by nonzero scalars keeps them linearly independent. -/
theorem linearIndependent_smul_of_ne_zero {κ V : Type*} [AddCommGroup V] [Module K V]
    {x : κ → V} (hx : LinearIndependent K x) {β : κ → K} (hβ : ∀ j, β j ≠ 0) :
    LinearIndependent K fun j ↦ β j • x j := by
  have := hx.units_smul fun j ↦ Units.mk0 (β j) (hβ j)
  convert this using 1
  funext j
  simp [Units.smul_def]

omit [NumberField K] in
/-- Scaling vectors by nonzero scalars does not change the spans of their subfamilies. -/
theorem span_image_smul_of_ne_zero {κ V : Type*} [AddCommGroup V] [Module K V] (x : κ → V)
    {β : κ → K} (hβ : ∀ j, β j ≠ 0) (S : Set κ) :
    Submodule.span K ((fun j ↦ β j • x j) '' S) = Submodule.span K (x '' S) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨j, hj, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · rintro _ ⟨j, hj, rfl⟩
    have h : x j = (β j)⁻¹ • (β j • x j) := by rw [smul_smul, inv_mul_cancel₀ (hβ j), one_smul]
    rw [SetLike.mem_coe, h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)

/-! ### The wedge domain at one place -/

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

open scoped Classical in
/-- **The exponents of the wedge domain at one place**: the sums of the exponents of the domain
over a `p`-subset `T`, plus `logb Q C` at every infinite place, plus at `w₀` alone `a` times the
logarithm of the minima read through `π` and, if `T` comes from the top block `{k, …}`, of the
jump `μ (k - 1) / μ k`. -/
noncomputable def wedgeExponentAt (c : AbsoluteValue K ℝ → ι → ℝ) (w₀ : InfinitePlace K) (a : ℕ)
    (π : Fin (Fintype.card ι) ≃ ι) (μ : ℕ → ℝ) (C Q : ℝ) (k p : ℕ) (v : AbsoluteValue K ℝ)
    (T : Set.powersetCard ι p) : ℝ :=
  ∑ t ∈ (T : Finset ι), c v t + if IsNonarchimedean v then 0 else
    Real.logb Q C + if v = w₀.1 then Real.logb Q ((∏ t ∈ (T : Finset ι), μ (π.symm t)) *
      if ∀ t ∈ (T : Finset ι), k ≤ (π.symm t : ℕ) then μ (k - 1) / μ k else 1) * a else 0

section Exponent

variable {c : AbsoluteValue K ℝ → ι → ℝ} {w₀ : InfinitePlace K} {a : ℕ}
  {π : Fin (Fintype.card ι) ≃ ι} {μ : ℕ → ℝ} {C Q : ℝ} {k p : ℕ}

omit [NumberField K] in
open scoped Classical in
private theorem rpow_wedgeExponentAt_of_isNonarchimedean (hQ : 0 < Q) {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) (T : Set.powersetCard ι p) :
    Q ^ wedgeExponentAt c w₀ a π μ C Q k p v T = ∏ t ∈ (T : Finset ι), Q ^ c v t := by
  simp only [wedgeExponentAt, hv, ↓reduceIte, add_zero]
  exact Real.rpow_sum_of_pos hQ _ _

omit [NumberField K] in
open scoped Classical in
private theorem rpow_wedgeExponentAt_of_not_isNonarchimedean (hQ : 0 < Q) (hQ1 : Q ≠ 1)
    (hC : 0 < C) {v : AbsoluteValue K ℝ} (hv : ¬ IsNonarchimedean v) (T : Set.powersetCard ι p)
    (hpos : v = w₀.1 → 0 < (∏ t ∈ (T : Finset ι), μ (π.symm t)) *
      if ∀ t ∈ (T : Finset ι), k ≤ (π.symm t : ℕ) then μ (k - 1) / μ k else 1) :
    Q ^ wedgeExponentAt c w₀ a π μ C Q k p v T = (∏ t ∈ (T : Finset ι), Q ^ c v t) *
      (C * if v = w₀.1 then ((∏ t ∈ (T : Finset ι), μ (π.symm t)) *
        if ∀ t ∈ (T : Finset ι), k ≤ (π.symm t : ℕ) then μ (k - 1) / μ k else 1) ^ a
      else 1) := by
  by_cases hw : v = w₀.1
  · have h := hpos hw
    subst hw
    simp only [wedgeExponentAt, hv, ↓reduceIte]
    rw [Real.rpow_add hQ, Real.rpow_sum_of_pos hQ, Real.rpow_add hQ, Real.rpow_logb hQ hQ1 hC,
      Real.rpow_mul_natCast hQ.le, Real.rpow_logb hQ hQ1 h]
  · simp only [wedgeExponentAt, hv, hw, ↓reduceIte, add_zero]
    rw [Real.rpow_add hQ, Real.rpow_sum_of_pos hQ, Real.rpow_logb hQ hQ1 hC, mul_one]

end Exponent

variable (K) in
/-- **The constant of the wedge domain at one place**, `pluckerConst K N · unitConst K ^ N`: the
constant of Layer 4.5 and the cost of moving the minima to `w₀`. -/
noncomputable def pluckerConstAt (N : ℕ) : ℝ :=
  pluckerConst K N * unitConst K ^ N

variable (K ι) in
open scoped Classical in
/-- **The wedges lie in the wedge domain at one place** (Bombieri–Gubler 7.5.30 with the minima
at `w₀`, Evertse–Schlickewei Lemma 9.2). For vectors `x j` realizing the minima `μ j` of the
domain, there are nonzero integers `β j`, `Sfin`-integers `ξ j l` and **one** bijection `π` such
that the wedges of `y j = β j • x j + ∑_{l < j} ξ j l • β l • x l` over the `p`-subsets meeting
the first `k` indices lie in the domain of `NumberField.wedgeExponentAt`, with the constant
`pluckerConstAt K #ι`. -/
theorem exists_plucker_mem_approxDomain_wedgeForms_at : ∃ C : ℝ, 0 < C ∧
    C = pluckerConstAt K (Fintype.card ι) ∧
    ∀ (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)),
    (∀ w : InfinitePlace K, LinearIndependent K (L w.1)) →
    (∀ v ∈ Sfin, LinearIndependent K (L v.1)) →
    ∀ (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ), 1 < Q →
    ∀ (w₀ : InfinitePlace K) (a : ℕ), a * w₀.mult = finrank ℚ K →
    ∀ (x : Fin (Fintype.card ι) → ι → K), LinearIndependent K x →
    ∀ μ : ℕ → ℝ, MonotoneOn μ (Set.Iio (Fintype.card ι)) →
    (∀ j < Fintype.card ι, 0 < μ j) →
    (∀ j, x j ∈ approxModule Sfin L c Q ∧
      (fun i ↦ mixedEmbedding K (x j i)) ∈ μ j • approxBody L c Q) →
    ∃ β : Fin (Fintype.card ι) → K, (∀ j, β j ≠ 0) ∧
      ∃ ξ : Fin (Fintype.card ι) → Fin (Fintype.card ι) → K,
      (∀ i j, ∀ v : FinitePlace K, v ∉ Sfin → v (ξ i j) ≤ 1) ∧
      ∃ π : Fin (Fintype.card ι) ≃ ι, ∀ k p : ℕ,
        ∀ J : Set.powersetCard (Fin (Fintype.card ι)) p, (∃ j ∈ J, (j : ℕ) < k) →
          plucker p ((fun j ↦ β j • x j + ∑ l ∈ Finset.Iio j, ξ j l • (β l • x l)) ∘
              Set.powersetCard.ofFinEmbEquiv.symm J) ∈
            approxDomain Sfin (fun v ↦ wedgeForms (L v) p)
              (wedgeExponentAt c w₀ a π μ C Q k p) Q := by
  obtain ⟨CE, hCE, hCEeq, hev⟩ := exists_evertse K ι
  set N := Fintype.card ι with hN
  set U := unitConst K with hU
  have hU1 : 1 ≤ U := one_le_unitConst
  refine ⟨N.factorial * max 1 CE ^ N * U ^ N, by positivity,
    by rw [hCEeq, pluckerConstAt, pluckerConst], ?_⟩
  intro Sfin L hLInf hLFin c Q hQ w₀ a ha x hx μ hμm hμp hxm
  classical
  have hQ0 : 0 < Q := by linarith
  have hna : ∀ v : FinitePlace K, IsNonarchimedean v.1 := fun v a b ↦ v.add_le a b
  have hw₀na : ¬ IsNonarchimedean w₀.1 := InfinitePlace.not_isNonarchimedean w₀
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, zero_mul] at ha
      exact absurd ha.symm (finrank_pos (R := ℚ) (M := K)).ne'
    · exact h0
  -- the balanced vectors
  choose β hβ0 hβint hβw hβw₀ using fun j : Fin N ↦ exists_balance w₀ ha (hμp j j.2)
  set g : Fin N → ι → K := fun j ↦ β j • x j with hg
  have hgind : LinearIndependent K g := linearIndependent_smul_of_ne_zero hx hβ0
  -- Evertse's lemma with the minima at `w₀` alone
  set μ₀ : ℕ → ℝ := fun j ↦ U * μ j ^ a with hμ₀
  have hμ₀m : MonotoneOn μ₀ (Set.Iio N) := fun i hi j hj hij ↦
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hμp i hi).le (hμm hi hj hij) a) (by positivity)
  have hμ₀p : ∀ j < N, 0 < μ₀ j := fun j hj ↦ by have := hμp j hj; positivity
  set μ' : AbsoluteValue K ℝ → Fin N → ℝ := fun v j ↦ if v = w₀.1 then μ₀ j else 1 with hμ'
  set ν : AbsoluteValue K ℝ → ι → ℝ := fun v i ↦ Q ^ c v i with hν
  have hmono : ∀ v, Monotone (μ' v) := fun v i j hij ↦ by
    by_cases hv : v = w₀.1
    · simp only [hμ', hv, ↓reduceIte]
      exact hμ₀m i.2 j.2 hij
    · simp [hμ', hv]
  have hLg : ∀ (l : Dual K (ι → K)) j, l (g j) = β j * l (x j) := fun l j ↦ by
    simp only [hg, map_smul, smul_eq_mul]
  have hinf : ∀ (w : InfinitePlace K) i j, w (L w.1 i (g j)) ≤ ν w.1 i * μ' w.1 j := by
    intro w i j
    have h := ((mem_smul_approxBody_iff (hμp j j.2)).1 (hxm j).2) w i
    rw [normAtPlace_sum_mixedEmbedding] at h
    rw [hLg, map_mul]
    by_cases hw : w = w₀
    · subst hw
      simp only [hμ', hν, hμ₀, ↓reduceIte]
      calc w (β j) * w (L w.1 i (x j)) ≤ (U * μ j ^ (a - 1)) * (μ j * Q ^ c w.1 i) :=
            mul_le_mul (hβw₀ j) h (apply_nonneg _ _) (by have := hμp j j.2; positivity)
        _ = Q ^ c w.1 i * (U * μ j ^ a) := by
            rw [← Nat.sub_add_cancel ha1, pow_succ, Nat.add_sub_cancel]; ring
    · have hw' : w.1 ≠ w₀.1 := fun h ↦ hw (Subtype.ext h)
      simp only [hμ', hν, hw', ↓reduceIte, mul_one]
      calc w (β j) * w (L w.1 i (x j)) ≤ w (β j) * (μ j * Q ^ c w.1 i) :=
            mul_le_mul_of_nonneg_left h (apply_nonneg _ _)
        _ = (w (β j) * μ j) * Q ^ c w.1 i := by ring
        _ ≤ 1 * Q ^ c w.1 i :=
            mul_le_mul_of_nonneg_right (hβw j w hw) (Real.rpow_pos_of_pos hQ0 _).le
        _ = Q ^ c w.1 i := one_mul _
  have hvw₀ : ∀ v : FinitePlace K, v.1 ≠ w₀.1 := fun v h ↦ hw₀na (h ▸ hna v)
  have hfin : ∀ v ∈ Sfin, ∀ i j, v (L v.1 i (g j)) ≤ ν v.1 i * μ' v.1 j := by
    intro v hv i j
    have h := (hxm j).1.1 v hv i
    rw [abs_of_pos hQ0] at h
    simp only [hμ', hν, hvw₀ v, ↓reduceIte, mul_one]
    rw [hLg, FinitePlace.coe_apply, map_mul, ← FinitePlace.coe_apply, ← FinitePlace.coe_apply]
    calc v (β j) * v (L v.1 i (x j)) ≤ 1 * Q ^ c v.1 i :=
          mul_le_mul (hβint j v) h (apply_nonneg _ _) zero_le_one
      _ = Q ^ c v.1 i := one_mul _
  obtain ⟨ξ, hξ, π, hπinf, hπfin⟩ := hev Sfin L hLInf hLFin g hgind μ' ν hmono
    (fun v i ↦ Real.rpow_pos_of_pos hQ0 _) hinf hfin
  refine ⟨β, hβ0, ξ, hξ, π w₀.1, fun k p J hJ ↦ ?_⟩
  set y := fun j ↦ g j + ∑ l ∈ Finset.Iio j, ξ j l • g l with hy
  change plucker p (y ∘ Set.powersetCard.ofFinEmbEquiv.symm J) ∈ _
  have hpN : p ≤ N := by
    have := Finset.card_le_univ (J : Finset (Fin N))
    rwa [Set.powersetCard.card_eq, Fintype.card_fin] at this
  obtain ⟨j₀, hj₀J, hj₀k⟩ := hJ
  obtain ⟨b₀, -⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem J j₀).2 hj₀J
  have hν0 : ∀ v i, 0 ≤ ν v i := fun v i ↦ (Real.rpow_pos_of_pos hQ0 _).le
  have hC0 : 0 < N.factorial * max 1 CE ^ N * U ^ N := by positivity
  have hEC : (N.factorial : ℝ) * max 1 CE ^ N ≤ N.factorial * max 1 CE ^ N * U ^ N :=
    le_mul_of_one_le_right (by positivity) (one_le_pow₀ hU1)
  -- the products over `σ` of a subset in order, as products over the subset
  have hperm : ∀ (T : Set.powersetCard ι p) (σ : Equiv.Perm (Fin p)) (f : ι → ℝ),
      ∏ b, f (Set.powersetCard.ofFinEmbEquiv.symm T (σ b)) = ∏ t ∈ (T : Finset ι), f t :=
    fun T σ f ↦ (Equiv.prod_comp σ fun a ↦ f (Set.powersetCard.ofFinEmbEquiv.symm T a)).trans
      (Set.powersetCard.prod_comp_ofFinEmbEquiv_symm T f)
  refine ⟨fun w T ↦ ?_, fun v hv T ↦ ?_, fun v hv s ↦ ?_⟩
  · -- an infinite place: Evertse's bound, with the minima at `w₀` alone
    set P : Prop := ∀ t ∈ (T : Finset ι), k ≤ ((π w₀.1).symm t : ℕ) with hPdef
    have hμT : 0 < ∏ t ∈ (T : Finset ι), μ ((π w₀.1).symm t) :=
      Finset.prod_pos fun t _ ↦ hμp _ ((π w₀.1).symm t).2
    have hρ : 0 < if P then μ (k - 1) / μ k else 1 := by
      split_ifs with hP
      · obtain ⟨a', -⟩ : ∃ a' : Fin p, True := ⟨⟨0, by have := b₀.2; omega⟩, trivial⟩
        have hk := hP (Set.powersetCard.ofFinEmbEquiv.symm T a')
          ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T _).1 ⟨a', rfl⟩)
        have hkN := ((π w₀.1).symm (Set.powersetCard.ofFinEmbEquiv.symm T a')).2
        exact div_pos (hμp _ (by omega)) (hμp _ (by omega))
      · exact one_pos
    rw [rpow_wedgeExponentAt_of_not_isNonarchimedean hQ0 hQ.ne' hC0
      (InfinitePlace.not_isNonarchimedean w) T fun _ ↦ mul_pos hμT hρ]
    have hQT : 0 ≤ ∏ t ∈ (T : Finset ι), Q ^ c w.1 t :=
      Finset.prod_nonneg fun t _ ↦ (Real.rpow_pos_of_pos hQ0 _).le
    by_cases hw : w = w₀
    · subst hw
      have hy : ∀ i j, w.1 (L w.1 (π w.1 i) (y j)) ≤ CE * ν w.1 (π w.1 i) * min (μ₀ i) (μ₀ j) := by
        intro i j
        have h := hπinf w i j
        simp only [hμ', ↓reduceIte] at h
        exact h
      refine (apply_wedgeForms_plucker_le w.1 (L w.1) (π w.1) hμ₀m hμ₀p (hν0 w.1) hCE hy J
        ⟨j₀, hj₀J, hj₀k⟩ T).trans ?_
      simp only [↓reduceIte]
      -- the minima at `w₀` are `U μ ^ a`
      have hjump : (if P then μ₀ (k - 1) / μ₀ k else 1) =
          (if P then μ (k - 1) / μ k else 1) ^ a := by
        split_ifs
        · simp only [hμ₀]
          rw [div_pow, mul_div_mul_left _ _ (by positivity : U ≠ 0)]
        · rw [one_pow]
      have hprodT : ∏ t ∈ (T : Finset ι), μ₀ ((π w.1).symm t) =
          U ^ p * (∏ t ∈ (T : Finset ι), μ ((π w.1).symm t)) ^ a := by
        simp only [hμ₀]
        rw [Finset.prod_mul_distrib, Finset.prod_const, Set.powersetCard.card_eq,
          Finset.prod_pow]
      rw [hjump, hprodT]
      have hUp : U ^ p ≤ U ^ N := pow_le_pow_right₀ hU1 hpN
      have hX : 0 ≤ ((∏ t ∈ (T : Finset ι), μ ((π w.1).symm t)) *
          if P then μ (k - 1) / μ k else 1) ^ a := by positivity
      calc (N.factorial : ℝ) * max 1 CE ^ N * ((∏ t ∈ (T : Finset ι), ν w.1 t) *
            ((if P then μ (k - 1) / μ k else 1) ^ a *
              (U ^ p * (∏ t ∈ (T : Finset ι), μ ((π w.1).symm t)) ^ a)))
          = (∏ t ∈ (T : Finset ι), Q ^ c w.1 t) * ((N.factorial * max 1 CE ^ N * U ^ p) *
              ((∏ t ∈ (T : Finset ι), μ ((π w.1).symm t)) *
                if P then μ (k - 1) / μ k else 1) ^ a) := by
            rw [mul_pow]; ring
        _ ≤ _ := by gcongr
    · have hw' : w.1 ≠ w₀.1 := fun h ↦ hw (Subtype.ext h)
      have hy : ∀ i j, w.1 (L w.1 (π w.1 i) (y j)) ≤
          CE * ν w.1 (π w.1 i) * min ((fun _ ↦ (1 : ℝ)) i) ((fun _ ↦ (1 : ℝ)) j) := by
        intro i j
        have h := hπinf w i j
        simp only [hμ', hw', ↓reduceIte] at h
        exact h
      refine (apply_wedgeForms_plucker_le w.1 (L w.1) (π w.1) (μ := fun _ ↦ 1)
        (fun _ _ _ _ _ ↦ le_rfl) (fun _ _ ↦ one_pos) (hν0 w.1) hCE hy J
        ⟨j₀, hj₀J, hj₀k⟩ T).trans ?_
      simp only [hw', ↓reduceIte, div_one, ite_self, Finset.prod_const_one, mul_one]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hEC hQT
  · -- a place of `Sfin`: the ultrametric bound, exactly
    rw [wedgeForms_plucker, rpow_wedgeExponentAt_of_isNonarchimedean hQ0 (hna v) T]
    refine AbsoluteValue.apply_det_le_of_isNonarchimedean (hna v) _
      (Finset.prod_nonneg fun t _ ↦ (Real.rpow_pos_of_pos hQ0 _).le) fun σ ↦ ?_
    rw [← hperm T σ fun t ↦ Q ^ c v.1 t]
    refine Finset.prod_le_prod₀ (fun b _ ↦ v.1.nonneg _) fun b _ ↦ ?_
    have h := hπfin v hv ((π v.1).symm (Set.powersetCard.ofFinEmbEquiv.symm T (σ b)))
      (Set.powersetCard.ofFinEmbEquiv.symm J b)
    simp only [Equiv.apply_symm_apply, hμ', hν, hvw₀ v, ↓reduceIte, min_self, mul_one] at h
    exact h
  · -- outside `Sfin`: the wedge of integral vectors is integral
    have hgint : ∀ j i, v (g j i) ≤ 1 := fun j i ↦ by
      simp only [hg, Pi.smul_apply, smul_eq_mul]
      rw [FinitePlace.coe_apply, map_mul, ← FinitePlace.coe_apply, ← FinitePlace.coe_apply]
      calc v (β j) * v (x j i) ≤ 1 * 1 :=
            mul_le_mul (hβint j v) ((hxm j).1.2 v hv i) (apply_nonneg _ _) zero_le_one
        _ = 1 := one_mul 1
    have hyint : ∀ j i, v (y j i) ≤ 1 := fun j i ↦ by
      simp only [hy, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine (hna v _ _).trans (max_le (hgint j i) ?_)
      refine Finset.sum_induction _ (fun z ↦ v z ≤ 1)
        (fun a b ha hb ↦ (hna v a b).trans (max_le ha hb)) (by simp) fun l _ ↦ ?_
      rw [FinitePlace.coe_apply, map_mul, ← FinitePlace.coe_apply, ← FinitePlace.coe_apply]
      calc v (ξ j l) * v (g l i) ≤ 1 * 1 :=
            mul_le_mul (hξ j l v hv) (hgint l i) (apply_nonneg _ _) zero_le_one
        _ = 1 := one_mul 1
    exact apply_plucker_le_one (hna v) (fun b i ↦ hyint _ i) s

open scoped Classical in
/-- **The weight of the wedge domain at one place, exactly**: as in Layer 4.5
(`NumberField.rpow_approxWeight_wedgeExponent`), `Q` to it is `Q` to `e` times the weight of the
domain, times `(C ^ M (∏ μ) ^ e μ (k - 1) / μ k) ^ d`, `M` the number of `p`-subsets and
`e = (#ι - 1).choose (p - 1)`: the place `w₀` carries `a` times the minima and `mult w₀` in the
weight, and `a mult w₀ = d`. -/
theorem rpow_approxWeight_wedgeExponentAt (Sfin : Finset (FinitePlace K))
    (c : AbsoluteValue K ℝ → ι → ℝ) (w₀ : InfinitePlace K) {a : ℕ}
    (ha : a * w₀.mult = finrank ℚ K) (π : Fin (Fintype.card ι) ≃ ι) {μ : ℕ → ℝ} {C Q : ℝ}
    {k p : ℕ} (hQ : 1 < Q) (hC : 0 < C) (hμ : ∀ j < Fintype.card ι, 0 < μ j)
    (h : k + p = Fintype.card ι) (hp : 0 < p) :
    Q ^ approxWeight Sfin (wedgeExponentAt c w₀ a π μ C Q k p) =
      Q ^ ((Fintype.card ι - 1).choose (p - 1) * approxWeight Sfin c) *
        (C ^ Fintype.card (Set.powersetCard ι p) *
          (∏ j ∈ Finset.range (Fintype.card ι), μ j) ^ (Fintype.card ι - 1).choose (p - 1) *
            (μ (k - 1) / μ k)) ^ finrank ℚ K := by
  have hQ0 : 0 < Q := by linarith
  set e := (Fintype.card ι - 1).choose (p - 1) with he
  set M := Fintype.card (Set.powersetCard ι p) with hM
  set r := μ (k - 1) / μ k with hr
  have hr0 : 0 < r := div_pos (hμ _ (by omega)) (hμ _ (by omega))
  set Y : ℝ := (∏ j ∈ Finset.range (Fintype.card ι), μ j) ^ e * r with hY
  have hprod : 0 < ∏ j ∈ Finset.range (Fintype.card ι), μ j :=
    Finset.prod_pos fun j hj ↦ hμ j (Finset.mem_range.1 hj)
  have hY0 : 0 < Y := by positivity
  set X : Set.powersetCard ι p → ℝ := fun T ↦ (∏ t ∈ (T : Finset ι), μ (π.symm t)) *
    if ∀ t ∈ (T : Finset ι), k ≤ (π.symm t : ℕ) then r else 1 with hX
  have hX0 : ∀ T, 0 < X T := fun T ↦ by
    have : 0 < ∏ t ∈ (T : Finset ι), μ (π.symm t) :=
      Finset.prod_pos fun t _ ↦ hμ _ (π.symm t).2
    simp only [hX]
    split_ifs <;> positivity
  have hprodX : ∏ T, X T = Y := by
    rw [Finset.prod_mul_distrib, Set.powersetCard.prod_prod_mem _ hp, prod_symm_eq_prod_range,
      prod_ite_topBlock _ h]
  have hfin : ∀ v : FinitePlace K, ∑ T : Set.powersetCard ι p,
      wedgeExponentAt c w₀ a π μ C Q k p v.1 T = e * ∑ i, c v.1 i := fun v ↦ by
    have hna : IsNonarchimedean v.1 := fun a b ↦ v.add_le a b
    simp only [wedgeExponentAt, hna, ↓reduceIte, add_zero]
    rw [Set.powersetCard.sum_sum_mem _ hp, nsmul_eq_mul]
  have hinf : ∀ w : InfinitePlace K, ∑ T : Set.powersetCard ι p,
      wedgeExponentAt c w₀ a π μ C Q k p w.1 T =
        e * ∑ i, c w.1 i + (M * Real.logb Q C + if w = w₀ then Real.logb Q Y * a else 0) := by
    intro w
    simp only [wedgeExponentAt, InfinitePlace.not_isNonarchimedean w, ↓reduceIte]
    rw [Finset.sum_add_distrib, Set.powersetCard.sum_sum_mem _ hp, nsmul_eq_mul,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 2
    by_cases hw : w = w₀
    · have hw' : w.1 = w₀.1 := congrArg Subtype.val hw
      simp only [hw, ↓reduceIte]
      rw [← Finset.sum_mul, ← hprodX, Real.logb_prod _ _ fun T _ ↦ (hX0 T).ne']
    · have hw' : w.1 ≠ w₀.1 := fun h ↦ hw (Subtype.ext h)
      simp only [hw', hw, ↓reduceIte, Finset.sum_const_zero]
  have hw : approxWeight Sfin (wedgeExponentAt c w₀ a π μ C Q k p) =
      e * approxWeight Sfin c + Real.logb Q (C ^ M * Y) * finrank ℚ K := by
    have h1 : ∀ w : InfinitePlace K, (w.mult : ℝ) *
        (e * ∑ i, c w.1 i + (M * Real.logb Q C + if w = w₀ then Real.logb Q Y * a else 0)) =
        e * (w.mult * ∑ i, c w.1 i) + M * Real.logb Q C * w.mult +
          if w = w₀ then Real.logb Q Y * (a * w₀.mult) else 0 := fun w ↦ by
      split_ifs with hw
      · subst hw; ring
      · ring
    simp only [approxWeight, hinf, hfin, h1, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [← Nat.cast_mul, ha, ← InfinitePlace.sum_mult_eq, Nat.cast_sum,
      Real.logb_mul (by positivity) hY0.ne', Real.logb_pow]
    ring
  rw [hw, Real.rpow_add hQ0, Real.rpow_mul_natCast hQ0.le, Real.rpow_logb hQ0 hQ.ne'
    (by positivity), mul_assoc (C ^ M)]

end NumberField
