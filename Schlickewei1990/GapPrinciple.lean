/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Schlickewei1990.SubspaceStep

-- Used only inside proofs.
import DiophantineApproximation.SubspaceGap
import DiophantineApproximation.SubspaceReduction

/-!
# The gap principle (Lemmas 4.2 and 5.3)

Schlickewei's gap principle puts the solutions `y = α x` of `∑ αᵢ xᵢ = 0` (in `S`-units) whose
height lies in a window into few proper subspaces: any `n` of them in one subclass have
determinant `0`. It covers the heights below the Subspace step of S90.3, which starts at
`stepThreshold`, far above Schlickewei's own `A² n^{3n+2}` (see `README.md`, the S90.3 check).

The proof follows §4 of the paper, with three changes:

* **Exponential windows.** Schlickewei's windows `[B, B A^{1/(2(n²−1))}]` cover only up to
  `A² n^{3n+2}`. Here the windows are `[B, B ^ (1 + 1/(4n)))`, for every `B > (n!) ^ (2 [K : ℚ])`,
  so a chain of `⌊log (log Θ / log B) / log (1 + 1/(4n))⌋ + 1` of them passes any `Θ`. That is what
  makes the count `log log` in the threshold of S90.3.
* **The subclasses are a grid**, not Lemma 4.1's simplex net. The relative sizes
  `u p i = ‖L_i(y')‖_p / ‖y_{r p}‖_p ≤ 1` (`NumberField.gapRatio`) multiply to exactly
  `A / H(y) ^ (n + 1)` (`NumberField.prod_gapRatio`, (4.9) as an identity), with `A` Schlickewei's
  constant (3.6) (`NumberField.gapConst`, `≥ 1`). So `u p i = (A / H(y)^{n+1}) ^ e p i` with
  `∑ e = 1`. Rounding `e` down on a grid of mesh `1 / N`, `N = 4 (n + 1) t n`, loses at most
  `1 / (4 (n + 1))` (`NumberField.exists_le_rpow_prod_grid`, DA `SystemGrid.lean`). The column
  `k(v)` of (4.8) is not singled out.
* **The places off `S` go through a height inequality** instead of (4.19). For `Δ ≠ 0`,
  every `ζ α_k` with `ζ = Δ / ∏ α_o` is an `S`-integer (off `S` the forms at `v` are the `y_o`,
  `o ≠ k`, with determinant `Δ` and sizes `‖α_o‖_v`, (4.18)), and `H(ζ α) = H(α)` is at most
  its product over `S∞ ∪ S`. Together with (4.14)–(4.15) at the places of `S∞ ∪ S`, where each
  column is divided by its largest coordinate, this gives
  `A ≤ (n!) ^ [K : ℚ] · ∏ⱼ H(y_j) · ∏ R` (`NumberField.gapConst_le`, (4.20)).

In a window `[B, B ^ (1 + 1/(4n)))` the right side is at most
`A · (n!) ^ [K : ℚ] · B ^ (−1/2) < A` (`NumberField.det_eq_zero_of_gapWindow`), **uniformly in
`A`**: when `A > B ^ (n + 1)` the relative sizes are only bounded by `1`, and `A⁻¹` pays.

No hypothesis on the coefficients except `αᵢ ≠ 0`, and none on `S`.

## Main results

* `NumberField.one_le_gapConst`, `NumberField.prod_gapRatio`: Schlickewei's (3.6) and (4.9).
* `NumberField.prod_placeProd_mul_mulHeight_le`, `NumberField.placeProd_det_le`,
  `NumberField.gapConst_le`: the determinant of `n` solutions, from below and from above.
* `NumberField.det_eq_zero_of_gapWindow`: **Lemma 4.2**, any `n` solutions in a subclass and a
  window are dependent.
* `NumberField.exists_finset_submodule_of_le_mulHeight_le`: **Lemmas 4.2 and 5.3**, the solutions
  with `B ≤ H(α x) ≤ Θ` lie in at most
  `(n + 1) ^ t (N + 1) ^ (n t) · (⌊log (log Θ / log B) / log (1 + 1/(4n))⌋ + 1)` proper
  subspaces.
* `NumberField.exists_finset_submodule_of_mulHeight_some_le`: the same for `B ≤ H(α x)` and
  `H(y') ≤ θ`, with `Θ = n ^ [K : ℚ] θ` (DA's `mulHeight_elim_neg_sum_le`). This is the range
  S90.3 leaves open.

## References

H. P. Schlickewei, *`S`-unit equations over number fields*, Invent. Math. **102** (1990), 95–107,
§4 and Lemma 5.3.

This is milestone S90.4 of `Schlickewei1990/README.md`.
-/

@[expose] public section

open IsDedekindDomain Height Module Finset

namespace NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The constant and the relative sizes of the forms -/

/-- **Schlickewei's constant** (3.6):
`A = ∏ᵢ ∏_{v ∈ S∞ ∪ S} ‖αᵢ‖_v · (∏_{v ∉ S∞ ∪ S} max ‖α‖_v) ^ (n + 1)`, the product off `S` written
as `H(α) / ∏_{v ∈ S∞ ∪ S} max ‖α‖_v`. It is invariant under scaling `α`, and at least `1`
(`NumberField.one_le_gapConst`). -/
noncomputable def gapConst (S : Finset (HeightOneSpectrum (𝓞 K))) (α : Option ι → K) : ℝ :=
  (∏ o, placeProd S Set.univ (fun v ↦ v (α o))) *
    (mulHeight α / placeProd S Set.univ (fun v ↦ ⨆ o, v (α o))) ^ (Fintype.card ι + 1)

/-- **The relative size of a form** (Schlickewei's `‖yᵢ‖_v / max_j ‖y_j‖_v`, (4.9)): the `i`-th
form (3.7) at `y'` over the coordinate `y_{r v}` at the place `p`. -/
noncomputable def gapRatio (S : Finset (HeightOneSpectrum (𝓞 K)))
    (r : AbsoluteValue K ℝ → Option ι) (y : Option ι → K) (p : InfinitePlace K ⊕ S) (i : ι) :
    ℝ :=
  systemValue S (fun v ↦ v) (sumForms r) p i (fun i ↦ y (some i)) /
    systemAbs S (fun v ↦ v) p (y (r (systemPlace S p)))

omit [DecidableEq ι] in
/-- **The constant is at least `1`**: for each `o`, the tuple `α / α_o` has a coordinate `1`, so
its height is at least its product over `S∞ ∪ S`
(`NumberField.placeProd_iSup_le_mulHeight_of_eq_one`). -/
theorem one_le_gapConst (S : Finset (HeightOneSpectrum (𝓞 K))) {α : Option ι → K}
    (hα0 : ∀ o, α o ≠ 0) : 1 ≤ gapConst S α := by
  set Pα := placeProd S Set.univ (fun v ↦ ⨆ o, v (α o)) with hPα
  have hPα0 : 0 < Pα := placeProd_pos S _ fun v _ ↦
    (v.pos (hα0 none)).trans_le (le_ciSup (f := fun o ↦ v (α o)) (Finite.bddAbove_range _) none)
  have hfac : ∀ o, 1 ≤ placeProd S Set.univ (fun v ↦ v (α o)) * (mulHeight α / Pα) := fun o ↦ by
    have h1 := placeProd_iSup_le_mulHeight_of_eq_one S (x := fun o' ↦ (α o)⁻¹ * α o') (i₀ := o)
      (inv_mul_cancel₀ (hα0 o))
    rw [placeProd_univ_iSup_mul, show (fun o' ↦ (α o)⁻¹ * α o') = (α o)⁻¹ • α from rfl,
      mulHeight_smul_eq_mulHeight α (inv_ne_zero (hα0 o))] at h1
    have hinv : placeProd S Set.univ (fun v ↦ v (α o)) *
        placeProd S Set.univ (fun v ↦ v (α o)⁻¹) = 1 := by
      rw [← placeProd_mul, placeProd_congr S _ fun v _ ↦ by
        rw [map_inv₀, mul_inv_cancel₀ (v.pos (hα0 o)).ne']]
      simp [placeProd]
    rw [← mul_div_assoc, one_le_div hPα0]
    calc Pα = placeProd S Set.univ (fun v ↦ v (α o)) *
          placeProd S Set.univ (fun v ↦ v (α o)⁻¹) * Pα := by rw [hinv, one_mul]
      _ = placeProd S Set.univ (fun v ↦ v (α o)) *
          (placeProd S Set.univ (fun v ↦ v (α o)⁻¹) * Pα) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1
          (placeProd_nonneg S _ fun v _ ↦ apply_nonneg _ _)
  have h := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ ↦ (1 : ℝ))
    (fun _ _ ↦ zero_le_one) fun o _ ↦ hfac o
  rw [Finset.prod_const_one, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_option] at h
  exact h

omit [Fintype ι] [DecidableEq ι] in
/-- **In a class, the largest coordinates multiply to the product of the sup norms.** -/
theorem prod_systemAbs_eq_placeProd (S : Finset (HeightOneSpectrum (𝓞 K)))
    {r : AbsoluteValue K ℝ → Option ι} {y : Option ι → K}
    (hr : ∀ v ∈ relevantPlaces S, v (y (r v)) = ⨆ o, v (y o)) :
    ∏ p, systemAbs S (fun v ↦ v) p (y (r (systemPlace S p))) =
      placeProd S Set.univ (fun v ↦ ⨆ o, v (y o)) := by
  rw [placeProd_univ_eq_prod_systemPlace]
  exact Finset.prod_congr rfl fun p _ ↦ by
    rw [← hr _ (systemPlace_mem_relevantPlaces S p)]
    rfl

/-- **The relative sizes are positive** on the hyperplane, with nonzero coordinates. -/
theorem gapRatio_pos (S : Finset (HeightOneSpectrum (𝓞 K))) (r : AbsoluteValue K ℝ → Option ι)
    {y : Option ι → K} (hy : ∑ o, y o = 0) (hy0 : ∀ o, y o ≠ 0) (p : InfinitePlace K ⊕ S)
    (i : ι) : 0 < gapRatio S r y p i := by
  unfold gapRatio systemValue systemAbs
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  exact div_pos (pow_pos ((systemPlace S p).pos (sumForms_ne_zero r _ hy hy0 i)) _)
    (pow_pos ((systemPlace S p).pos (hy0 _)) _)

/-- **In a class, the relative sizes are at most `1`** (`NumberField.apply_sumForms_le_iSup`). -/
theorem gapRatio_le_one (S : Finset (HeightOneSpectrum (𝓞 K))) {r : AbsoluteValue K ℝ → Option ι}
    {y : Option ι → K} (hy : ∑ o, y o = 0) (hy0 : ∀ o, y o ≠ 0)
    (hr : ∀ v ∈ relevantPlaces S, v (y (r v)) = ⨆ o, v (y o)) (p : InfinitePlace K ⊕ S)
    (i : ι) : gapRatio S r y p i ≤ 1 := by
  have hv := hr _ (systemPlace_mem_relevantPlaces S p)
  unfold gapRatio systemValue systemAbs
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [div_le_one (pow_pos ((systemPlace S p).pos (hy0 _)) _)]
  refine pow_le_pow_left₀ (apply_nonneg _ _) ?_ _
  refine (apply_sumForms_le_iSup r _ hy hv i).trans ?_
  rw [hv]
  exact Real.iSup_le (fun j ↦ le_ciSup_of_le (Finite.bddAbove_range _) (some j) le_rfl)
    (Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)

/-- **The product of the relative sizes in a class** (Schlickewei's (4.9), exact): it is
`A / H(y) ^ (n + 1)`, by the product identity (3.14)–(3.15) of S90.2 and the height of `α x`
(`NumberField.mulHeight_mul_unit_mul_placeProd`). -/
theorem prod_gapRatio (S : Finset (HeightOneSpectrum (𝓞 K))) (r : AbsoluteValue K ℝ → Option ι)
    {α : Option ι → K} (hα0 : ∀ o, α o ≠ 0) {x : Option ι → Kˣ}
    (hx : ∀ o, x o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (hsum : ∑ o, α o * x o = 0)
    (hr : ∀ v ∈ relevantPlaces S, v (α (r v) * x (r v)) = ⨆ o, v (α o * x o)) :
    ∏ p, ∏ i, gapRatio S r (fun o ↦ α o * x o) p i =
      gapConst S α / mulHeight (fun o ↦ α o * (x o : K)) ^ (Fintype.card ι + 1) := by
  set h := placeProd S Set.univ (fun v ↦ ⨆ o, v (α o * x o)) with hh
  set Pα := placeProd S Set.univ (fun v ↦ ⨆ o, v (α o)) with hPα
  have hα : α ≠ 0 := fun h0 ↦ hα0 none (congrFun h0 none)
  have hPα0 : 0 < Pα := placeProd_pos S _ fun v _ ↦
    (v.pos (hα0 none)).trans_le (le_ciSup (f := fun o ↦ v (α o)) (Finite.bddAbove_range _) none)
  have hh0 : 0 < h := placeProd_pos S _ fun v _ ↦
    (v.pos (mul_ne_zero (hα0 none) (x none).ne_zero)).trans_le
      (le_ciSup (f := fun o ↦ v (α o * x o)) (Finite.bddAbove_range _) none)
  have hHα : 0 < mulHeight α := zero_lt_one.trans_le (one_le_mulHeight α)
  have hrel := mulHeight_mul_unit_mul_placeProd S hα (fun o ↦ x o) hx
  have hid := affineProd_sumForms_mul_placeProd_iSup_eq S r hx hsum hr
  have hm := prod_systemAbs_eq_placeProd S (y := fun o ↦ α o * x o) hr
  have hgr : ∏ p, ∏ i, gapRatio S r (fun o ↦ α o * x o) p i =
      affineProd S (fun v ↦ v) (sumForms r) (fun i ↦ α (some i) * x (some i)) /
        h ^ Fintype.card ι := by
    simp only [gapRatio, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
    rw [affineProd_eq_prod_systemValue, Finset.prod_pow, hm]
  have haff := eq_div_of_mul_eq hh0.ne' hid
  have hHy := eq_div_of_mul_eq hPα0.ne' hrel
  rw [hgr, haff, hHy, gapConst, ← hPα, ← hh]
  field_simp
  ring

/-! ### The determinant of `n` solutions -/

/-- **The lower bound** (Schlickewei's (4.18)–(4.19), through the product formula). For `n`
solutions with `det (y'₁, …, y'ₙ) = Δ ≠ 0`, `ζ = Δ / ∏ α_o` makes every `ζ α_k` an `S`-integer:
off `S` the forms `y_o`, `o ≠ k`, have determinant `Δ` and sizes `‖α_o‖`, so
`‖Δ‖ ≤ ∏_{o ≠ k} ‖α_o‖`. The height of `ζ α = (ζ α_k)_k` is that of `α`, and at most its product
over `S∞ ∪ S`. -/
theorem prod_placeProd_mul_mulHeight_le [Nonempty ι] (S : Finset (HeightOneSpectrum (𝓞 K)))
    {α : Option ι → K} (hα0 : ∀ o, α o ≠ 0) {x : ι → Option ι → Kˣ}
    (hx : ∀ j o, x j o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (hsum : ∀ j, ∑ o, α o * x j o = 0)
    (hΔ : (Pi.basisFun K ι).det (fun j i ↦ α (some i) * (x j (some i) : K)) ≠ 0) :
    (∏ o, placeProd S Set.univ (fun v ↦ v (α o))) * mulHeight α ≤
      placeProd S Set.univ
          (fun v ↦ v ((Pi.basisFun K ι).det fun j i ↦ α (some i) * (x j (some i) : K))) *
        placeProd S Set.univ (fun v ↦ ⨆ o, v (α o)) := by
  set Y' : ι → ι → K := fun j i ↦ α (some i) * (x j (some i) : K) with hY'
  set Δ := (Pi.basisFun K ι).det Y' with hΔdef
  have hprod0 : ∏ o, α o ≠ 0 := Finset.prod_ne_zero_iff.2 fun o _ ↦ hα0 o
  set ζ := Δ / ∏ o, α o with hζ
  have hζ0 : ζ ≠ 0 := div_ne_zero hΔ hprod0
  have hz0 : (fun k ↦ ζ * α k) ≠ 0 := fun h0 ↦ mul_ne_zero hζ0 (hα0 none) (congrFun h0 none)
  have hzS : ∀ k, ζ * α k ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K := by
    intro k P hP
    rw [← FinitePlace.mk_apply_le_one_iff]
    set w : AbsoluteValue K ℝ := (FinitePlace.mk P).1 with hw
    have hunit : ∀ j o, w (x j o : K) = 1 := fun j o ↦
      (FinitePlace.mk_apply_eq_one_iff P _).2
        (Set.unit_valuation_eq_one (S : Set (HeightOneSpectrum (𝓞 K))) K ⟨x j o, hx j o⟩ hP)
    have hna : IsNonarchimedean (w : K → ℝ) := fun a b ↦ map_add_le_max (FinitePlace.mk P) a b
    have hrow : ∀ i j, w (sumForms (fun _ ↦ k) w i (Y' j)) =
        w (α (if k = some i then none else some i)) := fun i j ↦ by
      rw [apply_sumForms_eq (fun _ ↦ k) w (y := fun o ↦ α o * x j o) (hsum j) i, map_mul,
        hunit, mul_one]
    have hdet : w Δ ≤ ∏ i, w (α (if k = some i then none else some i)) := by
      rw [hΔdef, ← det_sumForms_apply (fun _ ↦ k) w Y']
      exact AbsoluteValue.apply_det_le_prod_of_isNonarchimedean hna _
        (fun i ↦ apply_nonneg _ _) fun i j ↦ (hrow i j).le
    obtain ⟨j₀⟩ := (inferInstance : Nonempty ι)
    have hall : (∏ i, w (α (if k = some i then none else some i))) * w (α k) =
        ∏ o, w (α o) := by
      calc (∏ i, w (α (if k = some i then none else some i))) * w (α k)
          = (∏ i, w (sumForms (fun _ ↦ k) w i fun i ↦ α (some i) * x j₀ (some i))) *
              w (α ((fun _ ↦ k) w) * x j₀ ((fun _ ↦ k) w)) := by
            congr 1
            · exact Finset.prod_congr rfl fun i _ ↦ (hrow i j₀).symm
            · rw [map_mul, hunit, mul_one]
        _ = ∏ o, w (α o * x j₀ o) :=
            prod_sumForms_mul_eq_prod_option (fun _ ↦ k) w (y := fun o ↦ α o * x j₀ o)
              (hsum j₀)
        _ = ∏ o, w (α o) := Finset.prod_congr rfl fun o _ ↦ by rw [map_mul, hunit, mul_one]
    change w (ζ * α k) ≤ 1
    have hpos : 0 < ∏ o, w (α o) := Finset.prod_pos fun o _ ↦ w.pos (hα0 o)
    rw [map_mul, hζ, map_div₀, map_prod, div_mul_eq_mul_div, div_le_one hpos, ← hall]
    exact mul_le_mul_of_nonneg_right hdet (apply_nonneg _ _)
  have hH := mulHeight_le_placeProd_univ S hz0 hzS
  rw [placeProd_univ_iSup_mul, show (fun k ↦ ζ * α k) = ζ • α from rfl,
    mulHeight_smul_eq_mulHeight α hζ0] at hH
  have hpp := placeProd_prod S Set.univ Finset.univ (fun o v ↦ v (α o))
  have hPΔ : placeProd S Set.univ (fun v ↦ v Δ) =
      placeProd S Set.univ (fun v ↦ v ζ) * ∏ o, placeProd S Set.univ (fun v ↦ v (α o)) := by
    rw [← hpp, ← placeProd_mul]
    refine placeProd_congr S _ fun v _ ↦ ?_
    rw [← map_prod, ← map_mul, hζ, div_mul_cancel₀ _ hprod0]
  rw [hPΔ]
  calc (∏ o, placeProd S Set.univ (fun v ↦ v (α o))) * mulHeight α
      ≤ (∏ o, placeProd S Set.univ (fun v ↦ v (α o))) *
          (placeProd S Set.univ (fun v ↦ v ζ) * placeProd S Set.univ (fun v ↦ ⨆ o, v (α o))) :=
        mul_le_mul_of_nonneg_left hH
          (Finset.prod_nonneg fun o _ ↦ placeProd_nonneg S _ fun v _ ↦ apply_nonneg _ _)
    _ = _ := by ring

/-- **The upper bound** (Schlickewei's (4.14)–(4.15)). At each place `p` of the system, divide
the `j`-th column of the forms at the points by `y_{j, r v}`: the determinant is `Δ / ∏ y_{j, r v}`,
and Leibniz bounds it by the rows' bounds `R p i` on the relative sizes. The product over the
places is `(n!) ^ [K : ℚ] · ∏ⱼ ∏_{S∞ ∪ S} max ‖y_j‖ · ∏ R`. -/
theorem placeProd_det_le (S : Finset (HeightOneSpectrum (𝓞 K)))
    (r : AbsoluteValue K ℝ → Option ι) {α : Option ι → K} (hα0 : ∀ o, α o ≠ 0)
    {x : ι → Option ι → Kˣ}
    (hr : ∀ j, ∀ v ∈ relevantPlaces S, v (α (r v) * x j (r v)) = ⨆ o, v (α o * x j o))
    {R : InfinitePlace K ⊕ S → ι → ℝ} (hR0 : ∀ p i, 0 ≤ R p i)
    (hR : ∀ j p i, gapRatio S r (fun o ↦ α o * x j o) p i ≤ R p i) :
    placeProd S Set.univ
        (fun v ↦ v ((Pi.basisFun K ι).det fun j i ↦ α (some i) * (x j (some i) : K))) ≤
      ((Fintype.card ι).factorial : ℝ) ^ finrank ℚ K *
        (∏ j, placeProd S Set.univ (fun v ↦ ⨆ o, v (α o * x j o))) * ∏ p, ∏ i, R p i := by
  set n := Fintype.card ι
  set Y' : ι → ι → K := fun j i ↦ α (some i) * (x j (some i) : K) with hY'
  have hfac0 : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hloc : ∀ p, systemAbs S (fun v ↦ v) p ((Pi.basisFun K ι).det Y') ≤
      (n.factorial : ℝ) ^ (systemExponent S p * finrank ℚ K) *
        ((∏ j, systemAbs S (fun v ↦ v) p
          (α (r (systemPlace S p)) * x j (r (systemPlace S p)))) * ∏ i, R p i) := by
    intro p
    set v := systemPlace S p with hv
    set e : ι → K := fun j ↦ α (r v) * x j (r v) with he
    have he0 : ∀ j, e j ≠ 0 := fun j ↦ mul_ne_zero (hα0 _) (x j _).ne_zero
    set M' : Matrix ι ι K := Matrix.of fun i j ↦ sumForms r v i (Y' j) / e j with hM'
    have hdet : (Pi.basisFun K ι).det Y' = (∏ j, e j) * M'.det := by
      rw [← Matrix.det_mul_row, ← det_sumForms_apply r v Y']
      congr 1
      ext i j
      simp [hM', mul_div_cancel₀ _ (he0 j)]
    have hM'le : ∀ i j, systemAbs S (fun v ↦ v) p (M' i j) ≤ R p i := fun i j ↦ by
      refine le_trans (le_of_eq ?_) (hR j p i)
      simp only [hM', Matrix.of_apply, gapRatio, systemValue, systemAbs, map_div₀, div_pow,
        Algebra.algebraMap_self, RingHom.id_apply, hv, he, hY']
    have hle := systemAbs_det_le S (fun v ↦ v) (fun P _ ↦ AbsoluteValue.liesOver_self _) p M'
      (hR0 p) hM'le
    have hprod : systemAbs S (fun v ↦ v) p (∏ j, e j) =
        ∏ j, systemAbs S (fun v ↦ v) p (e j) := by
      simp only [systemAbs, map_prod, Finset.prod_pow]
    rw [hdet, show systemAbs S (fun v ↦ v) p ((∏ j, e j) * M'.det) =
        systemAbs S (fun v ↦ v) p (∏ j, e j) * systemAbs S (fun v ↦ v) p M'.det by
      simp only [systemAbs, map_mul, mul_pow], hprod]
    calc (∏ j, systemAbs S (fun v ↦ v) p (e j)) * systemAbs S (fun v ↦ v) p M'.det
        ≤ (∏ j, systemAbs S (fun v ↦ v) p (e j)) *
            ((n.factorial : ℝ) ^ (systemExponent S p * finrank ℚ K) * ∏ i, R p i) :=
          mul_le_mul_of_nonneg_left hle
            (Finset.prod_nonneg fun j _ ↦ pow_nonneg (apply_nonneg _ _) _)
      _ = _ := by ring
  have hprod_g : ∏ p, (n.factorial : ℝ) ^ (systemExponent S p * finrank ℚ K) =
      (n.factorial : ℝ) ^ finrank ℚ K := by
    rw [← Real.rpow_sum_of_pos hfac0, ← Finset.sum_mul, sum_systemExponent, one_mul,
      Real.rpow_natCast]
  rw [placeProd_univ_eq_prod_systemPlace]
  calc ∏ p, systemPlace S p ((Pi.basisFun K ι).det Y') ^ systemMult S p
      = ∏ p, systemAbs S (fun v ↦ v) p ((Pi.basisFun K ι).det Y') := rfl
    _ ≤ ∏ p, ((n.factorial : ℝ) ^ (systemExponent S p * finrank ℚ K) *
        ((∏ j, systemAbs S (fun v ↦ v) p
          (α (r (systemPlace S p)) * x j (r (systemPlace S p)))) * ∏ i, R p i)) :=
        Finset.prod_le_prod₀ (fun p _ ↦ pow_nonneg (apply_nonneg _ _) _) fun p _ ↦ hloc p
    _ = (n.factorial : ℝ) ^ finrank ℚ K *
        ((∏ j, ∏ p, systemAbs S (fun v ↦ v) p
          (α (r (systemPlace S p)) * x j (r (systemPlace S p)))) * ∏ p, ∏ i, R p i) := by
        rw [Finset.prod_mul_distrib, hprod_g, Finset.prod_mul_distrib, Finset.prod_comm]
    _ = _ := by
        rw [Finset.prod_congr rfl fun j _ ↦
          prod_systemAbs_eq_placeProd S (y := fun o ↦ α o * x j o) (hr j)]
        ring

/-- **The determinant inequality** (Schlickewei's (4.20)). If `n` solutions in a class have
`Δ ≠ 0` and relative sizes at most `R p i`, then `A ≤ (n!) ^ [K : ℚ] · ∏ⱼ H(y_j) · ∏ R`. -/
theorem gapConst_le [Nonempty ι] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (r : AbsoluteValue K ℝ → Option ι) {α : Option ι → K} (hα0 : ∀ o, α o ≠ 0)
    {x : ι → Option ι → Kˣ} (hx : ∀ j o, x j o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (hsum : ∀ j, ∑ o, α o * x j o = 0)
    (hr : ∀ j, ∀ v ∈ relevantPlaces S, v (α (r v) * x j (r v)) = ⨆ o, v (α o * x j o))
    {R : InfinitePlace K ⊕ S → ι → ℝ} (hR0 : ∀ p i, 0 ≤ R p i)
    (hR : ∀ j p i, gapRatio S r (fun o ↦ α o * x j o) p i ≤ R p i)
    (hΔ : (Pi.basisFun K ι).det (fun j i ↦ α (some i) * (x j (some i) : K)) ≠ 0) :
    gapConst S α ≤ ((Fintype.card ι).factorial : ℝ) ^ finrank ℚ K *
      (∏ j, mulHeight (fun o ↦ α o * (x j o : K))) * ∏ p, ∏ i, R p i := by
  set Pα := placeProd S Set.univ (fun v ↦ ⨆ o, v (α o)) with hPα
  have hα : α ≠ 0 := fun h0 ↦ hα0 none (congrFun h0 none)
  have hPα0 : 0 < Pα := placeProd_pos S _ fun v _ ↦
    (v.pos (hα0 none)).trans_le (le_ciSup (f := fun o ↦ v (α o)) (Finite.bddAbove_range _) none)
  set c := mulHeight α / Pα with hc
  have hc0 : 0 < c := div_pos (zero_lt_one.trans_le (one_le_mulHeight α)) hPα0
  have hlow := prod_placeProd_mul_mulHeight_le S hα0 hx hsum hΔ
  have hup := placeProd_det_le S r hα0 hr hR0 hR
  have hHy : ∀ j, mulHeight (fun o ↦ α o * (x j o : K)) =
      c * placeProd S Set.univ (fun v ↦ ⨆ o, v (α o * x j o)) := fun j ↦ by
    have := mulHeight_mul_unit_mul_placeProd S hα (fun o ↦ x j o) (hx j)
    rw [hc, div_mul_eq_mul_div, eq_div_iff hPα0.ne']
    exact this
  have hkey : (∏ o, placeProd S Set.univ (fun v ↦ v (α o))) * c ≤
      ((Fintype.card ι).factorial : ℝ) ^ finrank ℚ K *
        (∏ j, placeProd S Set.univ (fun v ↦ ⨆ o, v (α o * x j o))) * ∏ p, ∏ i, R p i := by
    calc (∏ o, placeProd S Set.univ (fun v ↦ v (α o))) * c
        = (∏ o, placeProd S Set.univ (fun v ↦ v (α o))) * mulHeight α / Pα := by
          rw [hc, mul_div_assoc]
      _ ≤ placeProd S Set.univ
            (fun v ↦ v ((Pi.basisFun K ι).det fun j i ↦ α (some i) * (x j (some i) : K))) *
            Pα / Pα := div_le_div_of_nonneg_right hlow hPα0.le
      _ = placeProd S Set.univ
            (fun v ↦ v ((Pi.basisFun K ι).det fun j i ↦ α (some i) * (x j (some i) : K))) :=
          mul_div_cancel_right₀ _ hPα0.ne'
      _ ≤ _ := hup
  rw [gapConst, ← hPα, ← hc, Finset.prod_congr rfl fun j _ ↦ hHy j, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, pow_succ]
  calc (∏ o, placeProd S Set.univ (fun v ↦ v (α o))) * (c ^ Fintype.card ι * c)
      = c ^ Fintype.card ι * ((∏ o, placeProd S Set.univ (fun v ↦ v (α o))) * c) := by ring
    _ ≤ c ^ Fintype.card ι * (((Fintype.card ι).factorial : ℝ) ^ finrank ℚ K *
        (∏ j, placeProd S Set.univ (fun v ↦ ⨆ o, v (α o * x j o))) * ∏ p, ∏ i, R p i) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = _ := by ring

/-! ### The windows -/

/-- **Any `n` solutions in a subclass and a window are dependent** (Lemma 4.2, with exponential
windows). Let `n` solutions lie in one class, with relative sizes at most
`(A / H(y_j) ^ (n + 1)) ^ e p i` for exponents `e p i ≥ 0` with `∑ e ≥ 1 − 1 / (4 (n + 1))` (a
subclass), and with heights in `[B, B ^ (1 + 1 / (4 n)))` for `B > (n!) ^ (2 [K : ℚ])`. Then
`det (y'₁, …, y'ₙ) = 0`: otherwise
`A ≤ (n!) ^ [K : ℚ] · B ^ (n + 1/4) · min (1, A / B ^ (n + 1)) ^ γ` with `γ = 1 − 1 / (4 (n + 1))`,
which is `< A`, uniformly in `A ≥ 1`. -/
theorem det_eq_zero_of_gapWindow [Nonempty ι] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (r : AbsoluteValue K ℝ → Option ι) {α : Option ι → K} (hα0 : ∀ o, α o ≠ 0)
    {x : ι → Option ι → Kˣ} (hx : ∀ j o, x j o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (hsum : ∀ j, ∑ o, α o * x j o = 0)
    (hr : ∀ j, ∀ v ∈ relevantPlaces S, v (α (r v) * x j (r v)) = ⨆ o, v (α o * x j o))
    {e : InfinitePlace K ⊕ S → ι → ℝ} (he0 : ∀ p i, 0 ≤ e p i)
    (he : ∀ j p i, gapRatio S r (fun o ↦ α o * x j o) p i ≤
      (gapConst S α / mulHeight (fun o ↦ α o * (x j o : K)) ^ (Fintype.card ι + 1)) ^ e p i)
    (hes : 1 - 1 / (4 * ((Fintype.card ι : ℝ) + 1)) ≤ ∑ p, ∑ i, e p i)
    {B : ℝ} (hB : (((Fintype.card ι).factorial : ℝ) ^ finrank ℚ K) ^ 2 < B)
    (hlo : ∀ j, B ≤ mulHeight (fun o ↦ α o * (x j o : K)))
    (hhi : ∀ j, mulHeight (fun o ↦ α o * (x j o : K)) <
      B ^ (1 + 1 / (4 * (Fintype.card ι : ℝ)))) :
    (Pi.basisFun K ι).det (fun j i ↦ α (some i) * (x j (some i) : K)) = 0 := by
  by_contra hΔ
  set n := Fintype.card ι with hn
  set A := gapConst S α with hA
  set g : ℝ := (n.factorial : ℝ) ^ finrank ℚ K with hg
  set γ : ℝ := 1 - 1 / (4 * ((n : ℝ) + 1)) with hγ
  set ε : ℝ := 1 / (4 * (n : ℝ)) with hε
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Fintype.card_pos
  have hA1 : 1 ≤ A := one_le_gapConst S hα0
  have hA0 : 0 < A := by linarith
  have hg1 : 1 ≤ g := one_le_pow₀ (by exact_mod_cast n.factorial_pos)
  have hB1 : 1 < B := by nlinarith
  have hB0 : 0 < B := by linarith
  have hγ1 : γ ≤ 1 := by
    have : 0 ≤ 1 / (4 * ((n : ℝ) + 1)) := by positivity
    linarith
  set X : ℝ := B ^ (n + 1) with hX
  have hX0 : 0 < X := by positivity
  set m := min 1 (A / X) with hm
  have hm0 : 0 < m := lt_min one_pos (div_pos hA0 hX0)
  have hm1 : m ≤ 1 := min_le_left _ _
  have hy0 : ∀ j o, α o * (x j o : K) ≠ 0 := fun j o ↦ mul_ne_zero (hα0 o) (x j o).ne_zero
  have hH0 : ∀ j, 0 < mulHeight (fun o ↦ α o * (x j o : K)) := fun j ↦
    zero_lt_one.trans_le (one_le_mulHeight _)
  have hR : ∀ j p i, gapRatio S r (fun o ↦ α o * x j o) p i ≤ m ^ e p i := fun j p i ↦ by
    have hb0 : 0 ≤ A / mulHeight (fun o ↦ α o * (x j o : K)) ^ (n + 1) :=
      div_nonneg hA0.le (pow_nonneg (hH0 j).le _)
    have hb1 : A / mulHeight (fun o ↦ α o * (x j o : K)) ^ (n + 1) ≤ 1 := by
      rw [hA, ← prod_gapRatio S r hα0 (hx j) (hsum j) (hr j)]
      exact Finset.prod_le_one₀
        (fun p _ ↦ Finset.prod_nonneg fun i _ ↦ (gapRatio_pos S r (hsum j) (hy0 j) p i).le)
        fun p _ ↦ Finset.prod_le_one₀ (fun i _ ↦ (gapRatio_pos S r (hsum j) (hy0 j) p i).le)
          fun i _ ↦ gapRatio_le_one S (hsum j) (hy0 j) (hr j) p i
    have hbX : A / mulHeight (fun o ↦ α o * (x j o : K)) ^ (n + 1) ≤ A / X :=
      div_le_div_of_nonneg_left hA0.le hX0 (pow_le_pow_left₀ hB0.le (hlo j) _)
    exact (he j p i).trans (Real.rpow_le_rpow hb0 (le_min hb1 hbX) (he0 p i))
  have hkey := gapConst_le S r hα0 hx hsum hr (fun p i ↦ Real.rpow_nonneg hm0.le _) hR hΔ
  have hprodH : ∏ j, mulHeight (fun o ↦ α o * (x j o : K)) ≤ (B ^ (1 + ε)) ^ n := by
    calc ∏ j, mulHeight (fun o ↦ α o * (x j o : K)) ≤ ∏ _j : ι, B ^ (1 + ε) :=
          Finset.prod_le_prod₀ (fun j _ ↦ (hH0 j).le) fun j _ ↦ (hhi j).le
      _ = _ := by rw [Finset.prod_const, Finset.card_univ]
  have hprodR : ∏ p, ∏ i, m ^ e p i ≤ m ^ γ := by
    rw [show ∏ p, ∏ i, m ^ e p i = m ^ ∑ p, ∑ i, e p i by
      rw [Real.rpow_sum_of_pos hm0]
      exact Finset.prod_congr rfl fun p _ ↦ (Real.rpow_sum_of_pos hm0 _ _).symm]
    exact Real.rpow_le_rpow_of_exponent_ge hm0 hm1 hes
  have hXγ : X ^ γ = B ^ (γ * ((n : ℝ) + 1)) := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hB0.le, mul_comm]
    push_cast
    ring_nf
  have hBγ : 0 < B ^ (γ * ((n : ℝ) + 1)) := Real.rpow_pos_of_pos hB0 _
  have hmγ : m ^ γ * B ^ (γ * ((n : ℝ) + 1)) ≤ A := by
    by_cases hAX : A ≤ X
    · rw [show m = A / X from min_eq_right ((div_le_one hX0).2 hAX),
        Real.div_rpow hA0.le hX0.le, hXγ, div_mul_cancel₀ _ hBγ.ne']
      calc A ^ γ ≤ A ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hA1 hγ1
        _ = A := Real.rpow_one A
    · rw [show m = 1 from min_eq_left ((one_le_div hX0).2 (not_le.1 hAX).le), Real.one_rpow,
        one_mul, ← hXγ]
      calc X ^ γ ≤ X ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hB1.le) hγ1
        _ = X := Real.rpow_one X
        _ ≤ A := (not_le.1 hAX).le
  have hexp : (1 + ε) * n - γ * ((n : ℝ) + 1) = -(1 / 2) := by
    rw [hε, hγ]
    field_simp
    ring
  have hsqrt : g < B ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.lt_sqrt (by positivity)).2 hB
  have h1 : A ≤ g * B ^ ((1 + ε) * n) * (A / B ^ (γ * ((n : ℝ) + 1))) := by
    calc A ≤ g * (∏ j, mulHeight (fun o ↦ α o * (x j o : K))) * ∏ p, ∏ i, m ^ e p i := hkey
      _ ≤ g * (B ^ (1 + ε)) ^ n * m ^ γ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hprodH (by positivity)) hprodR
            (Finset.prod_nonneg fun p _ ↦ Finset.prod_nonneg fun i _ ↦
              Real.rpow_nonneg hm0.le _) (by positivity)
      _ ≤ g * B ^ ((1 + ε) * n) * (A / B ^ (γ * ((n : ℝ) + 1))) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hB0.le]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rwa [le_div_iff₀ hBγ]
  have h2 : g * B ^ ((1 + ε) * n) * (A / B ^ (γ * ((n : ℝ) + 1))) =
      A * (g * B ^ (-(1 / 2 : ℝ))) := by
    rw [← hexp, Real.rpow_sub hB0]
    ring
  have h3 : g * B ^ (-(1 / 2 : ℝ)) < 1 := by
    rw [Real.rpow_neg hB0.le, ← div_eq_mul_inv, div_lt_one (Real.rpow_pos_of_pos hB0 _)]
    exact hsqrt
  nlinarith

/-! ### The count -/

/-- **The grid of the gap principle**: `N = 4 (n + 1) t n`, `t` the number of places of
`S∞ ∪ S`, so that rounding the exponents costs at most `1 / (4 (n + 1))`. -/
noncomputable def gapGrid (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) : ℕ :=
  4 * (n + 1) * Fintype.card (InfinitePlace K ⊕ S) * n

/-- **The number of windows** `[Q, Q ^ (1 + 1 / (4 n)))` in a chain from `B` past `Θ`:
`⌊log (log Θ / log B) / log (1 + 1 / (4 n))⌋ + 1`. -/
noncomputable def gapWindows (n : ℕ) (B Θ : ℝ) : ℕ :=
  ⌊Real.log (Real.log Θ / Real.log B) / Real.log (1 + 1 / (4 * (n : ℝ)))⌋₊ + 1

omit [NumberField K] [Fintype ι] [DecidableEq ι] in
/-- **On the hyperplane, `y` is recovered from `y'`**: `y_{n+1} = −(y₁ + ⋯ + yₙ)`. -/
theorem elim_neg_sum_eq [Fintype ι] {y : Option ι → K} (hy : ∑ o, y o = 0) :
    (fun o ↦ o.elim (-∑ i, y (some i)) fun i ↦ y (some i)) = y := by
  funext o
  cases o with
  | none =>
    rw [Fintype.sum_option, add_comm, add_eq_zero_iff_eq_neg] at hy
    simp [hy]
  | some i => rfl

omit [DecidableEq ι] in
/-- **The gap principle** (Lemmas 4.2 and 5.3 of Schlickewei, with exponential windows). For
nonzero coefficients `α` and `B > (n!) ^ (2 [K : ℚ])`, the points `y' = (α₁ x₁, …, αₙ xₙ)` of the
solutions of `∑ αᵢ xᵢ = 0` in `S`-units with `B ≤ H(α x) ≤ Θ` lie in at most
`(n + 1) ^ t (N + 1) ^ (n t) · (⌊log (log Θ / log B) / log (1 + 1 / (4 n))⌋ + 1)` proper
subspaces of `Kⁿ`, `t` the number of places of `S∞ ∪ S` and `N = 4 (n + 1) t n`. The count does
not depend on `α`, and depends on `K` only through `[K : ℚ]` in `B` and through `log log Θ`. -/
theorem exists_finset_submodule_of_le_mulHeight_le [Nonempty ι]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {α : Option ι → K} (hα0 : ∀ o, α o ≠ 0) {B Θ : ℝ}
    (hB : (((Fintype.card ι).factorial : ℝ) ^ finrank ℚ K) ^ 2 < B) :
    ∃ T : Finset (Submodule K (ι → K)),
      #T ≤ (Fintype.card ι + 1) ^ Fintype.card (InfinitePlace K ⊕ S) *
          (gapGrid S (Fintype.card ι) + 1) ^
            (Fintype.card ι * Fintype.card (InfinitePlace K ⊕ S)) *
          gapWindows (Fintype.card ι) B Θ ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x : Option ι → Kˣ, (∀ o, x o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) →
        ∑ o, α o * x o = 0 → B ≤ mulHeight (fun o ↦ α o * (x o : K)) →
        mulHeight (fun o ↦ α o * (x o : K)) ≤ Θ →
        ∃ U ∈ T, (fun i ↦ α (some i) * (x (some i) : K)) ∈ U := by
  classical
  set n := Fintype.card ι with hn
  set t := Fintype.card (InfinitePlace K ⊕ S) with ht
  set N := gapGrid S n with hN
  set ε : ℝ := 1 / (4 * (n : ℝ)) with hε
  set a : ℕ → ℝ := fun h ↦ B ^ ((1 + ε) ^ h) with ha
  have hn1 : 1 ≤ n := Fintype.card_pos
  have ht1 : 1 ≤ t := Fintype.card_pos
  have hN0 : 0 < N := by
    simp only [hN, gapGrid]
    positivity
  have hg1 : (1 : ℝ) ≤ (n.factorial : ℝ) ^ finrank ℚ K :=
    one_le_pow₀ (by exact_mod_cast n.factorial_pos)
  have hB1 : 1 < B := by nlinarith
  have hε0 : 0 < ε := by positivity
  have haB : ∀ h, B ≤ a h := fun h ↦
    calc B = B ^ (1 : ℝ) := (Real.rpow_one B).symm
      _ ≤ a h := Real.rpow_le_rpow_of_exponent_le hB1.le (one_le_pow₀ (by linarith))
  have hasucc : ∀ h, a (h + 1) = a h ^ (1 + ε) := fun h ↦ by
    simp only [ha]
    rw [← Real.rpow_mul (by linarith), pow_succ]
  -- The subclasses: a class `ρ`, a grid point `k`, and a window `h`.
  let Q := (InfinitePlace K ⊕ S → Option ι) × (InfinitePlace K ⊕ S → ι → Fin (N + 1))
  let X : Q → ℕ → Set (ι → K) := fun q h ↦ {z | ∃ x : Option ι → Kˣ,
    (∀ o, x o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) ∧ ∑ o, α o * x o = 0 ∧
    (∀ v ∈ relevantPlaces S, v (α (classChoice S q.1 v) * x (classChoice S q.1 v)) =
      ⨆ o, v (α o * x o)) ∧
    (∀ p i, gapRatio S (classChoice S q.1) (fun o ↦ α o * x o) p i ≤
      (gapConst S α / mulHeight (fun o ↦ α o * (x o : K)) ^ (n + 1)) ^
        (((q.2 p i : ℕ) : ℝ) / N)) ∧
    1 - 1 / (4 * ((n : ℝ) + 1)) ≤ ∑ p, ∑ i, ((q.2 p i : ℕ) : ℝ) / N ∧
    a h ≤ mulHeight (fun o ↦ α o * (x o : K)) ∧ mulHeight (fun o ↦ α o * (x o : K)) < a (h + 1) ∧
    z = fun i ↦ α (some i) * (x (some i) : K)}
  have hspan : ∀ q h, Submodule.span K (X q h) ≠ ⊤ := fun q h ↦
    span_ne_top_of_forall_det_eq_zero fun Y hY ↦ by
      simp only [X, Set.mem_ofPred_eq] at hY
      choose x hx hsum hr hk hks hlo hhi hY' using hY
      obtain ⟨j₀⟩ := (inferInstance : Nonempty ι)
      rw [show Y = fun j i ↦ α (some i) * (x j (some i) : K) from funext hY']
      exact det_eq_zero_of_gapWindow S (classChoice S q.1) hα0 hx hsum hr
        (e := fun p i ↦ ((q.2 p i : ℕ) : ℝ) / N) (fun p i ↦ by positivity) hk (hks j₀)
        (hB.trans_le (haB h)) hlo fun j ↦ (hhi j).trans_eq (hasucc h)
  let T : ℕ → Finset (Submodule K (ι → K)) := fun h ↦
    Finset.univ.image fun q : Q ↦ Submodule.span K (X q h)
  have hTcard : ∀ h, #(T h) ≤ Fintype.card Q := fun h ↦
    Finset.card_image_le.trans_eq Finset.card_univ
  have hTtop : ∀ h, ∀ U ∈ T h, U ≠ ⊤ := fun h U hU ↦ by
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hU
    exact hspan q h
  let P : (ι → K) → Prop := fun z ↦ ∃ x : Option ι → Kˣ,
    (∀ o, x o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) ∧ ∑ o, α o * x o = 0 ∧
    z = fun i ↦ α (some i) * (x (some i) : K)
  let hgt : (ι → K) → ℝ := fun z ↦ mulHeight (fun o : Option ι ↦ o.elim (-∑ i, z i) z)
  have hhgt : ∀ x : Option ι → Kˣ, ∑ o, α o * x o = 0 →
      hgt (fun i ↦ α (some i) * (x (some i) : K)) = mulHeight (fun o ↦ α o * (x o : K)) :=
    fun x hsum ↦ congrArg mulHeight (elim_neg_sum_eq (y := fun o ↦ α o * (x o : K)) hsum)
  have hcov : ∀ h z, P z → a h ≤ hgt z → hgt z < a (h + 1) → ∃ U ∈ T h, z ∈ U := by
    rintro h z ⟨x, hx, hsum, rfl⟩ hlo hhi
    rw [hhgt x hsum] at hlo hhi
    have hy0 : ∀ o, α o * (x o : K) ≠ 0 := fun o ↦ mul_ne_zero (hα0 o) (x o).ne_zero
    obtain ⟨ρ, hρ⟩ := exists_classChoice S (fun o ↦ α o * (x o : K))
    obtain ⟨k, hk, hks⟩ := exists_le_rpow_prod_grid
      (u := gapRatio S (classChoice S ρ) (fun o ↦ α o * x o))
      (fun p i ↦ gapRatio_pos S _ hsum hy0 p i) (fun p i ↦ gapRatio_le_one S hsum hy0 hρ p i)
      hN0
    rw [prod_gapRatio S _ hα0 hx hsum hρ] at hk
    have hks' : 1 - 1 / (4 * ((n : ℝ) + 1)) ≤ ∑ p, ∑ i, ((k p i : ℕ) : ℝ) / N := by
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have ht0 : (0 : ℝ) < t := by exact_mod_cast ht1
      have hNr : (N : ℝ) = 4 * ((n : ℝ) + 1) * t * n := by
        simp only [hN, gapGrid, ht]
        push_cast
        ring
      have : (t * n : ℝ) / N = 1 / (4 * ((n : ℝ) + 1)) := by
        rw [hNr]
        field_simp
      rw [← this]
      exact hks
    exact ⟨Submodule.span K (X (ρ, k) h), Finset.mem_image_of_mem _ (Finset.mem_univ _),
      Submodule.subset_span ⟨x, hx, hsum, hρ, hk, hks', hlo, hhi, rfl⟩⟩
  obtain ⟨T', hT'card, hT'top, hT'cov⟩ :=
    exists_finset_submodule_of_chain (P := P) (ht := hgt) a T hTtop hcov (gapWindows n B Θ)
  refine ⟨T', ?_, hT'top, fun x hx hsum hlo hhi ↦ ?_⟩
  · calc #T' ≤ ∑ h ∈ Finset.range (gapWindows n B Θ), #(T h) := hT'card
      _ ≤ ∑ _h ∈ Finset.range (gapWindows n B Θ), Fintype.card Q :=
          Finset.sum_le_sum fun h _ ↦ hTcard h
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, Q, Fintype.card_prod,
            Fintype.card_fun, Fintype.card_option, Fintype.card_fin, pow_mul]
          ring
  · have hBΘ : B ≤ Θ := hlo.trans hhi
    have hB0 : 0 < B := by linarith
    have hΘ0 : 0 < Θ := by linarith
    have hlogB : 0 < Real.log B := Real.log_pos hB1
    have hq : 0 < Real.log Θ / Real.log B :=
      div_pos (Real.log_pos (by linarith)) hlogB
    have hlog1ε : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
    have hm : Real.log (Real.log Θ / Real.log B) / Real.log (1 + ε) < gapWindows n B Θ := by
      exact_mod_cast Nat.lt_floor_add_one _
    have hqm : Real.log Θ / Real.log B < (1 + ε) ^ gapWindows n B Θ := by
      rw [← Real.log_lt_log_iff hq (by positivity), Real.log_pow]
      rwa [div_lt_iff₀ hlog1ε] at hm
    have hΘa : Θ < a (gapWindows n B Θ) :=
      calc Θ = B ^ (Real.log Θ / Real.log B) := by
            rw [Real.log_div_log, Real.rpow_logb hB0 hB1.ne' hΘ0]
        _ < _ := Real.rpow_lt_rpow_of_exponent_lt hB1 hqm
    refine hT'cov _ ⟨x, hx, hsum, rfl⟩ ?_ ?_
    · rw [hhgt x hsum]
      simpa [ha] using hlo
    · rw [hhgt x hsum]
      exact hhi.trans_lt hΘa

omit [DecidableEq ι] in
/-- **The gap principle below the Subspace step.** The solutions with `B ≤ H(α x)` and
`H(y') ≤ θ`, the range that `NumberField.exists_finset_submodule_of_stepThreshold_lt` leaves
open at `θ = stepThreshold`, have `H(α x) ≤ n ^ [K : ℚ] θ`
(`NumberField.mulHeight_elim_neg_sum_le`), so they lie in the subspaces of
`NumberField.exists_finset_submodule_of_le_mulHeight_le` at
`Θ = n ^ [K : ℚ] θ`. -/
theorem exists_finset_submodule_of_mulHeight_some_le [Nonempty ι]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {α : Option ι → K} (hα0 : ∀ o, α o ≠ 0) {B θ : ℝ}
    (hB : (((Fintype.card ι).factorial : ℝ) ^ finrank ℚ K) ^ 2 < B) :
    ∃ T : Finset (Submodule K (ι → K)),
      #T ≤ (Fintype.card ι + 1) ^ Fintype.card (InfinitePlace K ⊕ S) *
          (gapGrid S (Fintype.card ι) + 1) ^
            (Fintype.card ι * Fintype.card (InfinitePlace K ⊕ S)) *
          gapWindows (Fintype.card ι) B ((Fintype.card ι : ℝ) ^ finrank ℚ K * θ) ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x : Option ι → Kˣ, (∀ o, x o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) →
        ∑ o, α o * x o = 0 → B ≤ mulHeight (fun o ↦ α o * (x o : K)) →
        mulHeight (fun i ↦ α (some i) * (x (some i) : K)) ≤ θ →
        ∃ U ∈ T, (fun i ↦ α (some i) * (x (some i) : K)) ∈ U := by
  obtain ⟨T, hT, htop, hcov⟩ := exists_finset_submodule_of_le_mulHeight_le S hα0
    (Θ := (Fintype.card ι : ℝ) ^ finrank ℚ K * θ) hB
  refine ⟨T, hT, htop, fun x hx hsum hlo hhi ↦ hcov x hx hsum hlo ?_⟩
  rw [← elim_neg_sum_eq (y := fun o ↦ α o * (x o : K)) hsum]
  exact (mulHeight_elim_neg_sum_le _).trans (by gcongr)

end NumberField
