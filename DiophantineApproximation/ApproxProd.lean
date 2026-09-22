/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ProjectiveTarget
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Pi

/-!
# The central quantity of the Subspace Theorem, and its local shape in two variables

**Layer 3.4, the global dictionary.** The Subspace Theorem measures a point `x` of `Kⁿ⁺¹` by

```text
approxProd S∞ S₀ w L x = ∏_{v ∈ S} (∏ᵢ ‖L_{v,i} x‖_v / ‖x‖_v) ^ (mult v),
```

a quantity invariant under scaling `x` by `Kˣ`, so a function on the projective space. This file
defines it for an arbitrary finite index type, and proves the two facts Layer 3.4 needs when the
index type has two elements: that the height of `x` is then the height of the single number
`β = x i₁ / x i₀`, and that each local factor of `approxProd` dominates — up to a constant
depending on the forms alone — the smaller of the two local approximation factors of Roth's
theorem at the zeros of the two forms.

## Main results

* `NumberField.approxProd`: the central quantity.
* `NumberField.approxProd_smul`: it is invariant under scaling, hence a function on `ℙ(Kⁿ⁺¹)`.
* `Height.mulHeight_eq_mulHeight₁_div`: for two coordinates, the projective height of `x` is the
  height of the ratio of its coordinates.
* `NumberField.det_ne_zero_of_linearIndependent`: two linearly independent forms in two variables
  have a nonvanishing determinant.
* `NumberField.onePointApprox_min_le_localFactor`: the local step of Layer 3.4.

## Implementation notes

⚠ **The invariance under scaling needs `LiesOver`.** The numerator of a local factor is measured
by `w v`, an absolute value of `F`, and the denominator by `v`, an absolute value of `K`; under
`x ↦ c • x` the first scales by `w v (algebraMap K F c)` and the second by `v c`. These agree
only because `w v` lies over `v`. So `approxProd` is a function on projective space only relative
to the `LiesOver` hypotheses that Layers 3.2 to 3.4 carry anyway — a scaling-invariant quantity
cannot be read off the definition alone.

⚠ **Two coordinates, not `Fin 2`.** Everything here is stated for an arbitrary index type with
two elements `i₀ ≠ i₁`, given as `∀ i, i = i₀ ∨ i = i₁`, and never transported along an
equivalence with `Fin 2`. The transport would have to be carried through `approxProd`, through
`LinearIndependent` and through `Module.Dual`, where it buys nothing; the supremum over the index
type and the height of the tuple are the only places where `Fin 2` appears, and they are handled
by the two lemmas below.

⚠ **The coefficients of the forms are a hypothesis, not a definition.** A linear form on `ι → F`
is given here by `∀ y, L i y = a i * y i₀ + b i * y i₁` rather than by extracting `a` and `b`
from `L`; the extraction is `L i (Pi.single i₀ 1)` and is done once, in
`DiophantineApproximation/RothProjective.lean`, so that no new name for the coefficients of a
linear form enters the library.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 7.2.2 and Example 7.2.7.

This is part of Layer 3.4 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height Module

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

/-- The supremum of a real-valued function on a two-element index type is the larger of its two
values. -/
theorem iSup_eq_max_of_forall_eq_or {ι : Type*} [Finite ι] {i₀ i₁ : ι}
    (hall : ∀ i, i = i₀ ∨ i = i₁) (f : ι → ℝ) : ⨆ i, f i = max (f i₀) (f i₁) := by
  have : Nonempty ι := ⟨i₀⟩
  have hbdd : BddAbove (Set.range f) := (Set.finite_range f).bddAbove
  refine le_antisymm (ciSup_le fun i ↦ ?_) (max_le (le_ciSup hbdd i₀) (le_ciSup hbdd i₁))
  rcases hall i with rfl | rfl
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- A tuple indexed by a two-element type has the height of the pair of its two entries. -/
theorem mulHeight_eq_mulHeight_pair {ι : Type*} [Finite ι] {i₀ i₁ : ι}
    (hall : ∀ i, i = i₀ ∨ i = i₁) (x : ι → K) :
    mulHeight x = mulHeight ![x i₀, x i₁] := by
  have hsup : ∀ v : AbsoluteValue K ℝ,
      (⨆ i, v (x i)) = ⨆ j : Fin 2, v (![x i₀, x i₁] j) := by
    intro v
    rw [iSup_eq_max_of_forall_eq_or hall fun i ↦ v (x i),
      iSup_eq_max_of_forall_eq_or (i₀ := (0 : Fin 2)) (i₁ := 1) (fun j ↦ by omega)
        fun j ↦ v (![x i₀, x i₁] j)]
    simp
  rcases eq_or_ne x 0 with rfl | hx
  · have : ![(0 : K), 0] = 0 := by
      funext j
      fin_cases j <;> rfl
    simp [this]
  · have hx' : ![x i₀, x i₁] ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      rcases hall i with rfl | rfl
      · exact fun h ↦ hi (by simpa using congrFun h 0)
      · exact fun h ↦ hi (by simpa using congrFun h 1)
    rw [mulHeight_eq hx, mulHeight_eq hx']
    simp only [hsup]

/-- **The projective height in two coordinates is the height of the ratio.** -/
theorem mulHeight_eq_mulHeight₁_div {ι : Type*} [Finite ι] {i₀ i₁ : ι}
    (hall : ∀ i, i = i₀ ∨ i = i₁) (x : ι → K) :
    mulHeight x = mulHeight₁ (x i₁ / x i₀) := by
  rw [mulHeight₁_div_eq_mulHeight, mulHeight_eq_mulHeight_pair hall x, mulHeight_swap]

end Height

/-- The index type of a two-element family is exhausted by its two members. -/
theorem Finset.univ_eq_pair_of_forall_eq_or {ι : Type*} [Fintype ι] [DecidableEq ι] {i₀ i₁ : ι}
    (hall : ∀ i, i = i₀ ∨ i = i₁) : (Finset.univ : Finset ι) = {i₀, i₁} :=
  (Finset.eq_univ_of_forall fun i ↦ by
    rcases hall i with rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)).symm

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι]

/-- **The central quantity of the Subspace Theorem.** For finite sets `Sinf`, `Sfin` of places of
`K`, an absolute value `w v` of `F` over each, and linear forms `L v i` over `F`, this is
`∏_{v ∈ S} ∏ᵢ ‖L_{v,i}(x)‖_v / ‖x‖_v` in Mathlib's normalization, for a point `x` of `Kⁿ⁺¹`. The
forms and the absolute values are indexed by the underlying absolute value of a place, so that one
family serves both finsets. -/
noncomputable def approxProd (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) (x : ι → K) : ℝ :=
  (∏ v ∈ Sinf, (∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ^ v.mult) *
    ∏ v ∈ Sfin, ∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)

omit [NumberField F] in
/-- The central quantity is a product of quotients of nonnegative reals. -/
theorem approxProd_nonneg (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) (x : ι → K) :
    0 ≤ approxProd Sinf Sfin w L x := by
  have hfac : ∀ (v : AbsoluteValue K ℝ) (W : AbsoluteValue F ℝ),
      (0 : ℝ) ≤ ∏ i, W (L v i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := by
    intro v W
    exact Finset.prod_nonneg fun i _ ↦
      div_nonneg (W.nonneg _) (Real.iSup_nonneg fun j ↦ v.nonneg _)
  exact mul_nonneg (Finset.prod_nonneg fun v _ ↦ pow_nonneg (hfac v.1 (w v.1)) _)
    (Finset.prod_nonneg fun v _ ↦ hfac v.1 (w v.1))

/-- **The central quantity is invariant under scaling, hence a function on projective space.**
This is what makes the Subspace Theorem a statement about subspaces. -/
theorem approxProd_smul (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) (x : ι → K) {c : K} (hc : c ≠ 0) :
    approxProd Sinf Sfin w L (c • x) = approxProd Sinf Sfin w L x := by
  have hfac : ∀ (v : AbsoluteValue K ℝ) (W : AbsoluteValue F ℝ), W.LiesOver v →
      (∏ i, W (L v i fun j ↦ algebraMap K F ((c • x) j)) / ⨆ j, v ((c • x) j))
        = ∏ i, W (L v i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := by
    intro v W hW
    have : W.LiesOver v := hW
    have hcv : 0 < v c := v.pos hc
    have hnum : ∀ i, W (L v i fun j ↦ algebraMap K F ((c • x) j))
        = v c * W (L v i fun j ↦ algebraMap K F (x j)) := by
      intro i
      have harg : (fun j ↦ algebraMap K F ((c • x) j))
          = algebraMap K F c • fun j ↦ algebraMap K F (x j) := by
        funext j
        simp
      rw [harg, map_smul, smul_eq_mul, map_mul,
        AbsoluteValue.apply_algebraMap_of_liesOver (v := v) W c]
    have hden : (⨆ j, v ((c • x) j)) = v c * ⨆ j, v (x j) := by
      have : ∀ j, v ((c • x) j) = v c * v (x j) := fun j ↦ by
        simp [smul_eq_mul, map_mul]
      simp only [this]
      exact Real.mul_iSup_of_nonneg (v.nonneg c) _ |>.symm
    simp only [hnum, hden]
    exact Finset.prod_congr rfl fun i _ ↦ by
      rw [mul_div_mul_left _ _ hcv.ne']
  rw [approxProd, approxProd]
  congr 1
  · exact Finset.prod_congr rfl fun v hv ↦
      congrArg (fun t : ℝ ↦ t ^ v.mult) (hfac v.1 (w v.1) (hwInf v hv))
  · exact Finset.prod_congr rfl fun v hv ↦ hfac v.1 (w v.1) (hwFin v hv)

omit [NumberField F] [Fintype ι] in
/-- **Linear independence of two forms in two variables is the nonvanishing of their
determinant.** This is Cramer's criterion, and it is the only place in Layer 3.4 where the
hypothesis `LinearIndependent F (L v)` of the Subspace Theorem is used. -/
theorem det_ne_zero_of_linearIndependent [Finite ι] {i₀ i₁ : ι} (hne : i₀ ≠ i₁)
    (hall : ∀ i, i = i₀ ∨ i = i₁) {L : ι → Dual F (ι → F)} (hL : LinearIndependent F L)
    {a b : ι → F} (hab : ∀ i, ∀ y : ι → F, L i y = a i * y i₀ + b i * y i₁) :
    a i₀ * b i₁ - a i₁ * b i₀ ≠ 0 := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  intro hd
  have key : ∀ c₀ c₁ : F, (∀ y : ι → F, c₀ * L i₀ y + c₁ * L i₁ y = 0) → c₀ = 0 ∧ c₁ = 0 := by
    intro c₀ c₁ hrel
    set g : ι → F := fun i ↦ if i = i₀ then c₀ else c₁ with hg
    have hg₀ : g i₀ = c₀ := by rw [hg]; exact ite_eq_left rfl
    have hg₁ : g i₁ = c₁ := by rw [hg]; exact ite_eq_right (Ne.symm hne)
    have hsum : ∑ i, g i • L i = 0 := by
      refine LinearMap.ext fun y ↦ ?_
      rw [LinearMap.sum_apply, LinearMap.zero_apply,
        Finset.univ_eq_pair_of_forall_eq_or hall, Finset.sum_pair hne]
      simp only [LinearMap.smul_apply, smul_eq_mul, hg₀, hg₁]
      exact hrel y
    have hzero := Fintype.linearIndependent_iff.mp hL g hsum
    exact ⟨hg₀ ▸ hzero i₀, hg₁ ▸ hzero i₁⟩
  by_cases hb : b i₀ = 0 ∧ b i₁ = 0
  · obtain ⟨ha₁, ha₀⟩ := key (a i₁) (-a i₀) fun y ↦ by
      rw [hab i₀ y, hab i₁ y, hb.1, hb.2]
      ring
    have ha₀' : a i₀ = 0 := by
      have := neg_eq_zero.mp ha₀
      exact this
    refine hL.ne_zero i₀ (LinearMap.ext fun y ↦ ?_)
    rw [hab i₀ y, ha₀', hb.1, LinearMap.zero_apply]
    ring
  · obtain ⟨hb₁, hb₀⟩ := key (b i₁) (-b i₀) fun y ↦ by
      rw [hab i₀ y, hab i₁ y]
      have : b i₁ * (a i₀ * y i₀ + b i₀ * y i₁) + -b i₀ * (a i₁ * y i₀ + b i₁ * y i₁)
          = (a i₀ * b i₁ - a i₁ * b i₀) * y i₀ := by ring
      rw [this, hd, zero_mul]
    exact hb ⟨neg_eq_zero.mp hb₀, hb₁⟩

/-- **The local step of Layer 3.4.** At one place, the smaller of the two local approximation
factors of Roth's theorem — at the zeros of the two forms, evaluated at `β = x i₁ / x i₀` — is at
most a constant depending on the forms alone times the local factor of `approxProd`. -/
theorem onePointApprox_min_le_localFactor {u : AbsoluteValue K ℝ} (W : AbsoluteValue F ℝ)
    [W.LiesOver u] {i₀ i₁ : ι} (hne : i₀ ≠ i₁) (hall : ∀ i, i = i₀ ∨ i = i₁)
    {L : ι → Dual F (ι → F)} {a b : ι → F}
    (hab : ∀ i, ∀ y : ι → F, L i y = a i * y i₀ + b i * y i₁)
    (hd : a i₀ * b i₁ - a i₁ * b i₀ ≠ 0) {x : ι → K} (hx : x i₀ ≠ 0) :
    min (W.onePointApprox (OnePoint.formRoot (a i₀) (b i₀)) (algebraMap K F (x i₁ / x i₀)))
        (W.onePointApprox (OnePoint.formRoot (a i₁) (b i₁)) (algebraMap K F (x i₁ / x i₀)))
      ≤ (W.formConst (a i₀) (b i₀) + W.formConst (a i₁) (b i₁))
          * ((W (a i₀) + W (a i₁) + W (b i₀) + W (b i₁)) / W (a i₀ * b i₁ - a i₁ * b i₀))
        * ∏ i, W (L i fun j ↦ algebraMap K F (x j)) / ⨆ j, u (x j) := by
  classical
  set β : F := algebraMap K F (x i₁ / x i₀) with hβ
  have hux : 0 < u (x i₀) := u.pos hx
  have hx' : algebraMap K F (x i₀) ≠ 0 := fun h ↦
    hx ((algebraMap K F).injective (by rw [h, map_zero]))
  have hmap : algebraMap K F (x i₁) = algebraMap K F (x i₀) * β := by
    rw [hβ, map_div₀]
    field_simp
  have hWβ : W β = u (x i₁) / u (x i₀) := by
    rw [hβ, AbsoluteValue.apply_algebraMap_of_liesOver (v := u) W, map_div₀]
  have hden : (⨆ j, u (x j)) = u (x i₀) * max 1 (W β) := by
    rw [Height.iSup_eq_max_of_forall_eq_or hall fun j ↦ u (x j), hWβ,
      mul_max_of_nonneg _ _ hux.le, mul_one, mul_div_cancel₀ _ hux.ne']
  have hfac : ∀ i, W (L i fun j ↦ algebraMap K F (x j)) / ⨆ j, u (x j)
      = W (a i + b i * β) / max 1 (W β) := by
    intro i
    have hval : (L i fun j ↦ algebraMap K F (x j))
        = algebraMap K F (x i₀) * (a i + b i * β) := by
      rw [hab i, hmap]
      ring
    rw [hval, map_mul, AbsoluteValue.apply_algebraMap_of_liesOver (v := u) W, hden,
      mul_div_mul_left _ _ hux.ne']
  rw [Finset.univ_eq_pair_of_forall_eq_or hall, Finset.prod_pair hne, hfac i₀, hfac i₁]
  exact W.onePointApprox_min_le hd β

end NumberField

/-! ### Acceptance criteria -/

/-- **The central quantity is a function on projective space.** Scaling a point by a nonzero
element of `K` multiplies every numerator and every denominator of a local factor by the same
`v c`, once the absolute values of `F` lie over the places of `K`. -/
example {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
    {ι : Type*} [Fintype ι] (Sinf : Finset (NumberField.InfinitePlace K))
    (Sfin : Finset (NumberField.FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) (x : ι → K) {c : K} (hc : c ≠ 0) :
    NumberField.approxProd Sinf Sfin w L (c • x) = NumberField.approxProd Sinf Sfin w L x :=
  NumberField.approxProd_smul Sinf Sfin w hwInf hwFin L x hc

/-- **The affine chart: the height of `(1, β)` is the height of `β`.** -/
example {K : Type*} [Field K] [AdmissibleAbsValues K] (β : K) :
    mulHeight (![1, β] : Fin 2 → K) = mulHeight₁ β := by
  rw [Height.mulHeight_eq_mulHeight₁_div (i₀ := 0) (i₁ := 1)
    (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1)]
  simp

/-- ⚠ **The point at infinity has height `1`.** The ratio `x 1 / x 0` is Lean's junk `0` there,
and `mulHeight₁ 0 = 1`; the projective height of `[0 : 1]` is also `1`, by the product formula.
So `Height.mulHeight_eq_mulHeight₁_div` needs no hypothesis `x i₀ ≠ 0`, and the reading "the
height of `x` is the height of `β`" is correct even where `β` is not defined. -/
example {K : Type*} [Field K] [AdmissibleAbsValues K] (y : K) :
    mulHeight (![0, y] : Fin 2 → K) = 1 := by
  rw [Height.mulHeight_eq_mulHeight₁_div (i₀ := 0) (i₁ := 1)
    (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1)]
  simp
