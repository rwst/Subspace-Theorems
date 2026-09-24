/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ApproximationDomain
public import DiophantineApproximation.GlobalBound
public import DiophantineApproximation.SubspaceValueBound

/-!
# Step VI: the product formula against the local bounds

This file carries out Bombieri–Gubler's 7.5.26, the last step of the proof of Theorem 7.5.13.
The data are a multihomogeneous auxiliary polynomial `P` of multidegree `d` (Layer 5.2), a Hasse
derivative `∂_I P` that does not vanish at the point

```text
X (h, i) = ∑ l, z h l * y h l i,        |z h l| ≤ B,   y h l ∈ Π(Q h)
```

(Layer 5.5), and the vanishing pattern of Layer 5.2, which says that the coefficients of
`∂_I P` in the coordinates of the forms at a place of `S` survive only at orders `J` with
`∑ h, J (h, j) / d h` within `Δ` of a common value. Multiplying the local bounds of
`DiophantineApproximation/SubspaceValueBound.lean` by the product formula gives

```text
0 ≤ tw · log C + h(P) + 2 |d| · H(β) + D · (mean · w(c) + Δ · w(|c|)) + (∑ h, log (Q h)) · w(|c|),
```

where `w(c)` is the weight of the system of exponents and `w(|c|)` the weight of its absolute
values. The first three terms are `O(|d|)` and `O(∑ h, log (d h + 1))`; the fourth carries the
negative weight, which is what produces the contradiction once `D` is large.

## Main definitions

* `NumberField.formMatrix`: the matrix of a system of linear forms, whose rows are the values of
  the forms at the standard basis.
* `NumberField.sPlace`: the places of `S`, as one index type — every infinite place and the
  chosen finite ones.
* `NumberField.refFamily`: **the reference family charged by the product formula**: the entries of
  the inverse matrices of the systems of forms at the places of `S`, and the integers of the grid.
* `NumberField.approxAbsWeight`: the weight of the *absolute values* of a system of exponents.

## Main results

* `Height.le_prod_max_one` and `Height.iSup_sup_one_le_prod_max_one`: a member, or the largest
  member, of a finite family is at most the product of the truncated local factors.
* `AbsoluteValue.apply_dual_sum_smul_le` and its nonarchimedean companion: the value of a form at
  a small integral combination.
* `NumberField.sum_formMatrix_mul`: the matrix of a system of forms computes the forms.
* `NumberField.subspace_key_inequality`: **Step VI**, the displayed inequality.

## Implementation notes

⚠ **The reference family is what keeps the constants global.** The local bound at a place of `S`
contains the largest entry of the inverse matrix there, and the local bound at every place
contains the size of the grid integers. Neither product over `S` alone is a height, so both are
charged through the `β` slot of `NumberField.one_le_of_forall_apply_le`, whose conclusion is a
product over *all* places. The exponent is `2 |d|` and not `|d|` because the two factors are
bounded by the same product.

⚠ **`S` contains every archimedean place, and that is used.** Away from `S` the bound has no
constant at all, and the point is integral there only because the coordinates of the `y h l` are;
at an archimedean place outside `S` neither would hold. This is the book's standing hypothesis on
`S`, and here it is the choice `Sinf = univ`.

⚠ **The weight of the absolute values is a second invariant of the system.** The book absorbs it
into its `O(m η D)` and `O(log (1/η) D / log Q₁)`; it is kept explicit here because it is what
the caller has to make small against `ε`, by choosing `η`, and because it is the only place where
the *size* of the exponents — as opposed to their sum — enters the proof.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
7.5.26.

This is part of Layer 5.6 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset Module

noncomputable section

namespace Height

variable {K : Type*} [Field K]

/-- Every member of a finite family is at most the product of the truncated local factors. -/
theorem one_le_prod_max_one' {Θ : Type*} (v : AbsoluteValue K ℝ) (β : Θ → K)
    (s : Finset Θ) : (1 : ℝ) ≤ ∏ θ' ∈ s, max (v (β θ')) 1 := by
  calc (1 : ℝ) = ∏ _θ' ∈ s, (1 : ℝ) := Finset.prod_const_one.symm
    _ ≤ ∏ θ' ∈ s, max (v (β θ')) 1 :=
        Finset.prod_le_prod₀ (fun _ _ ↦ zero_le_one) (fun _ _ ↦ le_max_right _ _)

theorem le_prod_max_one {Θ : Type*} [Fintype Θ] (v : AbsoluteValue K ℝ) (β : Θ → K) (θ : Θ) :
    max (v (β θ)) 1 ≤ ∏ θ', max (v (β θ')) 1 := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ θ)]
  exact le_mul_of_one_le_right (le_trans zero_le_one (le_max_right _ _))
    (one_le_prod_max_one' v β _)

/-- One factor at a time: the local factor of a member is at most the product. -/
theorem apply_le_prod_max_one {Θ : Type*} [Fintype Θ] (v : AbsoluteValue K ℝ) (β : Θ → K)
    (θ : Θ) : v (β θ) ≤ ∏ θ', max (v (β θ')) 1 :=
  le_trans (le_max_left _ _) (le_prod_max_one v β θ)

/-- The product of the truncated local factors is at least `1`. -/
theorem one_le_prod_max_one {Θ : Type*} [Fintype Θ] (v : AbsoluteValue K ℝ) (β : Θ → K) :
    (1 : ℝ) ≤ ∏ θ', max (v (β θ')) 1 :=
  one_le_prod_max_one' v β _

/-- The largest local factor of a family indexed by a subfamily of `β`. -/
theorem iSup_sup_one_le_prod_max_one {Θ σ : Type*} [Fintype Θ]
    (v : AbsoluteValue K ℝ) (β : Θ → K) (g : σ → Θ) (x : σ → K) (hx : ∀ s, x s = β (g s)) :
    (⨆ s, v (x s)) ⊔ 1 ≤ ∏ θ', max (v (β θ')) 1 := by
  refine sup_le (Real.iSup_le (fun s ↦ ?_) (le_trans zero_le_one (one_le_prod_max_one v β)))
    (one_le_prod_max_one v β)
  rw [hx s]
  exact apply_le_prod_max_one v β (g s)

end Height

namespace AbsoluteValue

variable {K : Type*} [Field K] {ι : Type*}

/-- **The value of a form at a small combination of points of the domain.** -/
theorem apply_dual_sum_smul_le {ρ : Type*} [Fintype ρ] (v : AbsoluteValue K ℝ)
    (l : Module.Dual K (ι → K)) (y : ρ → ι → K) (z : ρ → K) {Zb G : ℝ}
    (hZb : 0 ≤ Zb) (hz : ∀ r, v (z r) ≤ Zb) (hy : ∀ r, v (l (y r)) ≤ G) :
    v (l (∑ r, z r • y r)) ≤ (Fintype.card ρ : ℝ) * (Zb * G) := by
  rw [map_sum]
  refine le_trans (v.sum_le _ _) ?_
  calc ∑ r, v (l (z r • y r)) ≤ ∑ _r : ρ, Zb * G := by
        refine Finset.sum_le_sum fun r _ ↦ ?_
        rw [map_smul, smul_eq_mul, map_mul]
        exact mul_le_mul (hz r) (hy r) (v.nonneg _) hZb
    _ = (Fintype.card ρ : ℝ) * (Zb * G) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- **The same at a nonarchimedean absolute value**, with no cardinality factor. -/
theorem apply_dual_sum_smul_le_of_isNonarchimedean {ρ : Type*} [Fintype ρ]
    {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    (l : Module.Dual K (ι → K)) (y : ρ → ι → K) (z : ρ → K) {Zb G : ℝ}
    (hZb : 0 ≤ Zb) (hG : 0 ≤ G) (hz : ∀ r, v (z r) ≤ Zb) (hy : ∀ r, v (l (y r)) ≤ G) :
    v (l (∑ r, z r • y r)) ≤ Zb * G := by
  rcases isEmpty_or_nonempty ρ with hρ | hρ
  · rw [Finset.univ_eq_empty, Finset.sum_empty, map_zero, AbsoluteValue.map_zero]
    exact mul_nonneg hZb hG
  rw [map_sum]
  obtain ⟨r, _, hle⟩ :=
    hv.finset_image_add_of_nonempty (fun r ↦ l (z r • y r)) Finset.univ_nonempty
  refine le_trans hle ?_
  rw [map_smul, smul_eq_mul, map_mul]
  exact mul_le_mul (hz r) (hy r) (v.nonneg _) hZb

end AbsoluteValue

namespace NumberField

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The matrix of a system of linear forms**: its `(j, i)` entry is the value of the `j`-th
form at the `i`-th standard basis vector. -/
def formMatrix (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (v : AbsoluteValue K ℝ) :
    Matrix ι ι K := LinearMap.toMatrix' (LinearMap.pi (L v))

theorem formMatrix_apply (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (v : AbsoluteValue K ℝ)
    (j i : ι) : formMatrix L v j i = L v j (Pi.single i 1) :=
  LinearMap.toMatrix'_pi_apply _ _ _

/-- **The matrix of a system of forms computes the forms.** -/
theorem sum_formMatrix_mul (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (v : AbsoluteValue K ℝ) (j : ι) (x : ι → K) :
    ∑ i, formMatrix L v j i * x i = L v j x := by
  have hx : x = ∑ i, x i • (Pi.single i 1 : ι → K) := by
    funext i'
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [map_smul, smul_eq_mul, formMatrix_apply, mul_comm]

/-- **The matrix of an independent system of forms is invertible.** -/
theorem isUnit_det_formMatrix {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    {v : AbsoluteValue K ℝ} (hL : LinearIndependent K (L v)) :
    IsUnit (formMatrix L v).det := by
  rw [formMatrix, LinearMap.det_toMatrix']
  exact isUnit_iff_ne_zero.mpr (LinearMap.det_pi_ne_zero hL)

theorem inv_mul_formMatrix {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    {v : AbsoluteValue K ℝ} (hL : LinearIndependent K (L v)) :
    (formMatrix L v)⁻¹ * formMatrix L v = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_det_formMatrix hL)

variable [NumberField K]

/-- **The weight of the absolute values of a system of exponents.** -/
def approxAbsWeight (Sfin : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ) : ℝ :=
  ∑ v : InfinitePlace K, (v.mult : ℝ) * ∑ i, |c v.1 i| + ∑ v ∈ Sfin, ∑ i, |c v.1 i|

omit [DecidableEq ι] in
theorem approxAbsWeight_nonneg (Sfin : Finset (FinitePlace K))
    (c : AbsoluteValue K ℝ → ι → ℝ) : 0 ≤ approxAbsWeight Sfin c := by
  refine add_nonneg (Finset.sum_nonneg fun v _ ↦ ?_) (Finset.sum_nonneg fun v _ ↦ ?_)
  · exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ ↦ abs_nonneg _)
  · exact Finset.sum_nonneg fun i _ ↦ abs_nonneg _


/-- The places of `S`: every infinite place and the chosen finite ones. -/
def sPlace (Sfin : Finset (FinitePlace K)) :
    InfinitePlace K ⊕ ↥Sfin → AbsoluteValue K ℝ :=
  Sum.elim (fun w ↦ w.1) fun w ↦ (w : FinitePlace K).1

/-- **The reference family charged by the product formula**: the entries of the inverse matrices
of the systems of forms at the places of `S`, and the integers of the grid. -/
def refFamily (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (Sfin : Finset (FinitePlace K))
    (B : ℕ) :
    ((InfinitePlace K ⊕ ↥Sfin) × ι × ι) ⊕ ↥(Finset.Icc (-(B : ℤ)) (B : ℤ)) → K :=
  Sum.elim (fun t ↦ (formMatrix L (sPlace Sfin t.1))⁻¹ t.2.1 t.2.2) fun k ↦ ((k : ℤ) : K)

section Point

variable {ρ : Type*} [Fintype ρ]

omit [Fintype ι] [DecidableEq ι] [NumberField K] in
/-- The point of the product, block by block, is a small combination of the given family. -/
theorem funext_point (z : ρ → ℤ) (y : ρ → ι → K) :
    (fun i ↦ ∑ l, (z l : K) * y l i) = ∑ l, (z l : K) • y l := by
  funext i
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun l _ ↦ rfl

omit [NumberField K] in
/-- **The value of a form of `S` at the small point**, archimedean form. -/
theorem apply_form_point_le (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (v : AbsoluteValue K ℝ) {cc : ι → ℝ} {Q : ℝ} (hQ : 0 < Q)
    {y : ρ → ι → K} {z : ρ → ℤ} {Pb : ℝ} (hPb : 1 ≤ Pb)
    (hzPb : ∀ l, v ((z l : K)) ≤ Pb)
    (hyQ : ∀ (l : ρ) (j : ι), v (L v j (y l)) ≤ Q ^ cc j) (j : ι) :
    v (∑ i, formMatrix L v j i * (∑ l, (z l : K) * y l i))
      ≤ (Fintype.card ρ : ℝ) * Pb * Real.exp (cc j * Real.log Q) := by
  rw [sum_formMatrix_mul, funext_point]
  have hexp : Q ^ cc j = Real.exp (cc j * Real.log Q) := by
    rw [Real.rpow_def_of_pos hQ, mul_comm]
  rw [mul_assoc]
  refine le_trans (AbsoluteValue.apply_dual_sum_smul_le v (L v j) y (fun l ↦ ((z l : K)))
    (le_trans zero_le_one hPb) hzPb fun l ↦ hyQ l j) ?_
  rw [hexp]

omit [NumberField K] in
/-- **The value of a form of `S` at the small point**, nonarchimedean form. -/
theorem apply_form_point_le_of_isNonarchimedean (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v) {cc : ι → ℝ} {Q : ℝ} (hQ : 0 < Q)
    {y : ρ → ι → K} {z : ρ → ℤ} {Pb : ℝ} (hPb : 1 ≤ Pb)
    (hzPb : ∀ l, v ((z l : K)) ≤ Pb)
    (hyQ : ∀ (l : ρ) (j : ι), v (L v j (y l)) ≤ Q ^ cc j) (j : ι) :
    v (∑ i, formMatrix L v j i * (∑ l, (z l : K) * y l i))
      ≤ Pb * Real.exp (cc j * Real.log Q) := by
  rw [sum_formMatrix_mul, funext_point]
  have hexp : Q ^ cc j = Real.exp (cc j * Real.log Q) := by
    rw [Real.rpow_def_of_pos hQ, mul_comm]
  refine le_trans (AbsoluteValue.apply_dual_sum_smul_le_of_isNonarchimedean hv (L v j) y
    (fun l ↦ ((z l : K))) (le_trans zero_le_one hPb) (Real.rpow_nonneg hQ.le _) hzPb
    fun l ↦ hyQ l j) ?_
  rw [hexp]

omit [Fintype ι] [DecidableEq ι] [NumberField K] in
/-- **The coordinates of the small point are integral away from `S`.** -/
theorem apply_point_le_of_isNonarchimedean {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    {y : ρ → ι → K} {z : ρ → ℤ} {Pb : ℝ} (hPb : 1 ≤ Pb)
    (hzPb : ∀ l, v ((z l : K)) ≤ Pb) (hyv : ∀ (l : ρ) (i : ι), v (y l i) ≤ 1) (i : ι) :
    v (∑ l, (z l : K) * y l i) ≤ Pb := by
  rcases isEmpty_or_nonempty ρ with hρ | hρ
  · rw [Finset.univ_eq_empty, Finset.sum_empty, AbsoluteValue.map_zero]
    exact le_trans zero_le_one hPb
  obtain ⟨l, _, hle⟩ :=
    hv.finset_image_add_of_nonempty (fun l ↦ (z l : K) * y l i) Finset.univ_nonempty
  refine le_trans hle ?_
  rw [map_mul]
  calc v ((z l : K)) * v (y l i) ≤ Pb * 1 :=
        mul_le_mul (hzPb l) (hyv l i) (v.nonneg _) (le_trans zero_le_one hPb)
    _ = Pb := mul_one Pb

end Point


/-! ### The key inequality -/

section KeyInequality

open MvPolynomial Height

variable {κ ρ : Type*} [Fintype κ] [Fintype ρ] [Nonempty ρ] [Nonempty ι]

/-- **Step VI of the proof of Theorem 7.5.13: the product formula against the local bounds.** -/
theorem subspace_key_inequality
    {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    {cf : AbsoluteValue K ℝ → ι → ℝ}
    (hLinf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLfin : ∀ w ∈ Sfin, LinearIndependent K (L w.1))
    {Q : κ → ℝ} (hQ : ∀ h, 1 < Q h)
    {y : κ → ρ → ι → K} (hy : ∀ h l, y h l ∈ approxDomain Sfin L cf (Q h))
    {B : ℕ} {z : κ → ρ → ℤ} (hz : ∀ h l, (z h l).natAbs ≤ B)
    {d : κ → ℕ} (hd : ∀ h, 0 < d h) {D : ℝ} (hD : 0 ≤ D)
    (hdq : ∀ h, D ≤ (d h : ℝ) * Real.log (Q h))
    (hdq' : ∀ h, (d h : ℝ) * Real.log (Q h) ≤ D + Real.log (Q h))
    {P : MvPolynomial (κ × ι) K} (hP0 : P ≠ 0) (hP : IsMultiHomogeneous d P)
    {I : κ × ι →₀ ℕ}
    (hne : eval (fun p : κ × ι ↦ ∑ l, (z p.1 l : K) * y p.1 l p.2) (hasseDeriv I P) ≠ 0)
    {Δ mean : ℝ}
    (hpat : ∀ (a : InfinitePlace K ⊕ ↥Sfin) (J : κ × ι →₀ ℕ),
      (blockSubst (formMatrix L (sPlace Sfin a))⁻¹ (hasseDeriv I P)).coeff J ≠ 0 →
      ∀ j, |(∑ h, (J (h, j) : ℝ) / (d h : ℝ)) - mean| ≤ Δ) :
    0 ≤ (Height.totalWeight K : ℝ)
        * Real.log ((∏ p : κ × ι, ((d p.1 : ℝ) + 1)) ^ 2
          * (2 * Fintype.card ι * Fintype.card ρ : ℝ) ^ (∑ h, d h))
      + P.logHeight
      + 2 * ((∑ h, d h : ℕ) : ℝ) * ∑ θ, Real.log (Height.mulHeight₁ (refFamily L Sfin B θ))
      + D * (mean * approxWeight Sfin cf + Δ * approxAbsWeight Sfin cf)
      + (∑ h, Real.log (Q h)) * approxAbsWeight Sfin cf := by
  classical
  set Dsum := ∑ h, d h with hDsum
  set X : κ × ι → K := fun p ↦ ∑ l, (z p.1 l : K) * y p.1 l p.2 with hXdef
  set dd : κ × ι → ℕ := fun p ↦ d p.1 with hdd
  have hdeg : ∀ p, P.degreeOf p ≤ dd p := fun p ↦ hP.degreeOf_le p.1 p.2
  set xc : (∀ p : κ × ι, Fin (dd p + 1)) → K := fun bx ↦ P.coeff (boxMonomial dd bx) with hxcdef
  set β := refFamily L Sfin B with hβdef
  set Pb : AbsoluteValue K ℝ → ℝ := fun v ↦ ∏ θ, max (v (β θ)) 1 with hPbdef
  set q : κ → ℝ := fun h ↦ Real.log (Q h) with hqdef
  set gain : AbsoluteValue K ℝ → ℝ := fun v ↦
    Real.exp (D * (mean * ∑ j, cf v j + Δ * ∑ j, |cf v j|) + (∑ h, q h) * ∑ j, |cf v j|)
    with hgaindef
  set C : ℝ := (∏ p : κ × ι, ((d p.1 : ℝ) + 1)) ^ 2
      * (2 * Fintype.card ι * Fintype.card ρ : ℝ) ^ Dsum with hCdef
  -- basic positivity
  have hq : ∀ h, 0 < q h := fun h ↦ Real.log_pos (hQ h)
  have hQ0 : ∀ h, 0 < Q h := fun h ↦ lt_trans zero_lt_one (hQ h)
  have hPb1 : ∀ v, (1 : ℝ) ≤ Pb v := fun v ↦ one_le_prod_max_one v β
  have hC1 : (1 : ℝ) ≤ C := by
    refine one_le_mul_of_one_le_of_one_le ?_ ?_
    · refine one_le_pow₀ (Finset.one_le_prod₀ fun p _ ↦ ?_)
      have : (0 : ℝ) ≤ (d p.1 : ℝ) := Nat.cast_nonneg _
      linarith
    · refine one_le_pow₀ ?_
      have h1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
      have h2 : (1 : ℝ) ≤ (Fintype.card ρ : ℝ) := by exact_mod_cast Fintype.card_pos
      nlinarith
  -- the grid integers and the matrix entries lie in the reference family
  have hzmem : ∀ (h : κ) (l : ρ) (v : AbsoluteValue K ℝ), v ((z h l : K)) ≤ Pb v := by
    intro h l v
    have hmem : z h l ∈ Finset.Icc (-(B : ℤ)) (B : ℤ) := by
      rw [Finset.mem_Icc]
      have := hz h l
      omega
    exact apply_le_prod_max_one v β (Sum.inr ⟨z h l, hmem⟩)
  have hWmem : ∀ (a : InfinitePlace K ⊕ ↥Sfin) (v : AbsoluteValue K ℝ),
      (⨆ p : ι × ι, v ((formMatrix L (sPlace Sfin a))⁻¹ p.1 p.2)) ⊔ 1 ≤ Pb v := by
    intro a v
    exact iSup_sup_one_le_prod_max_one v β (fun p : ι × ι ↦ Sum.inl (a, p.1, p.2))
      (fun p ↦ (formMatrix L (sPlace Sfin a))⁻¹ p.1 p.2) fun p ↦ rfl
  -- the coefficient vector
  have hiSup : ∀ v : AbsoluteValue K ℝ, (⨆ bx, v (xc bx)) = ⨆ ν, v (P.coeff ν) :=
    fun v ↦ iSup_coeff_boxMonomial v hdeg
  have hxc0 : xc ≠ 0 := by
    obtain ⟨ν, hν⟩ := support_nonempty.mpr hP0
    obtain ⟨bx, hbx⟩ := mem_range_boxMonomial_of_mem_support hdeg hν
    refine Function.ne_iff.mpr ⟨bx, ?_⟩
    change P.coeff (boxMonomial dd bx) ≠ (0 : K)
    rw [hbx]
    exact mem_support_iff.mp hν
  -- the pattern at a place of `S`
  have hJc : ∀ (a : InfinitePlace K ⊕ ↥Sfin),
      ∀ J ∈ (blockSubst (formMatrix L (sPlace Sfin a))⁻¹ (hasseDeriv I P)).support,
        ∀ j, |(∑ h, (J (h, j) : ℝ) / (d h : ℝ)) - mean| ≤ Δ :=
    fun a J hJ ↦ hpat a J (mem_support_iff.mp hJ)
  set t : FinitePlace K → ℝ := fun v ↦ if v ∈ Sfin then gain v.1 else 1 with htdef
  have hprodpow : ∀ v : AbsoluteValue K ℝ,
      (∏ θ, max (v (β θ)) 1 ^ (2 * Dsum)) = Pb v ^ (2 * Dsum) := fun v ↦ by
    rw [hPbdef, ← Finset.prod_pow]
  -- the bound at an infinite place
  have hinf : ∀ w : InfinitePlace K,
      w (eval X (hasseDeriv I P))
        ≤ C * (⨆ bx, w.1 (xc bx)) * (∏ θ, max (w.1 (β θ)) 1 ^ (2 * Dsum)) * gain w.1 := by
    intro w
    have hMA : ((formMatrix L w.1)⁻¹) * formMatrix L w.1 = 1 := inv_mul_formMatrix (hLinf w)
    have hXb : ∀ (h : κ) (j : ι), w.1 (∑ i, formMatrix L w.1 j i * X (h, i))
        ≤ (Fintype.card ρ : ℝ) * Pb w.1 * Real.exp (cf w.1 j * q h) :=
      fun h j ↦ apply_form_point_le L w.1 (hQ0 h) (hPb1 w.1) (fun l ↦ hzmem h l w.1)
        (fun l j' ↦ (hy h l).1 w j') j
    have hbound := apply_eval_hasseDeriv_le_place (ρ := ρ) w.1 hMA hd hP I (hPb1 w.1)
      (hWmem (Sum.inl w) w.1) hq hD hdq hdq' hXb (hJc (Sum.inl w))
    rw [hprodpow, hiSup w.1, mul_assoc]
    exact hbound
  -- the bound at a finite place
  have hfin : ∀ v : FinitePlace K,
      v (eval X (hasseDeriv I P))
        ≤ (⨆ bx, v.1 (xc bx)) * (∏ θ, max (v.1 (β θ)) 1 ^ (2 * Dsum)) * t v := by
    intro v
    have hna : IsNonarchimedean (v.1 : K → ℝ) := fun a b ↦ v.add_le a b
    by_cases hv : v ∈ Sfin
    · have hMA : ((formMatrix L v.1)⁻¹) * formMatrix L v.1 = 1 :=
        inv_mul_formMatrix (hLfin v hv)
      have hXb : ∀ (h : κ) (j : ι), v.1 (∑ i, formMatrix L v.1 j i * X (h, i))
          ≤ Pb v.1 * Real.exp (cf v.1 j * q h) :=
        fun h j ↦ apply_form_point_le_of_isNonarchimedean L hna (hQ0 h) (hPb1 v.1)
          (fun l ↦ hzmem h l v.1) (fun l j' ↦ (hy h l).2.1 v hv j') j
      have hbound := apply_eval_hasseDeriv_le_place_of_isNonarchimedean hna hMA hd hP I
        (hPb1 v.1) (hWmem (Sum.inr ⟨v, hv⟩) v.1) hq hD hdq hdq' hXb (hJc (Sum.inr ⟨v, hv⟩))
      have htv : t v = gain v.1 := by rw [htdef]; simp only [hv, ite_true]
      rw [hprodpow, hiSup v.1, htv, mul_assoc]
      exact hbound
    · have hXle : ∀ p : κ × ι, v.1 (X p) ≤ Pb v.1 := fun p ↦
        apply_point_le_of_isNonarchimedean hna (hPb1 v.1) (fun l ↦ hzmem p.1 l v.1)
          (fun l i ↦ (hy p.1 l).2.2 v hv i) p.2
      have hbound := apply_eval_hasseDeriv_le_of_isNonarchimedean hna hP I
        (hPb1 v.1) hXle
      have htv : t v = 1 := by rw [htdef]; simp only [hv, ite_false]
      rw [hprodpow, hiSup v.1, htv, mul_one]
      exact hbound
  -- the product formula
  have hmain := one_le_of_forall_apply_le (Sinf := (Finset.univ : Finset (InfinitePlace K)))
    (Sfin := Sfin) hne hxc0 β (fun _ ↦ 2 * Dsum) hC1 (s := fun w : InfinitePlace K ↦ gain w.1)
    (t := t) (fun w ↦ Real.exp_nonneg _) (fun w hw ↦ absurd (Finset.mem_univ w) hw)
    (fun v hv ↦ by rw [htdef]; simp only [hv, ite_false]) hinf hfin
  -- take logarithms
  have hgpos : ∀ v : AbsoluteValue K ℝ, (0 : ℝ) < gain v := fun v ↦ by
    rw [hgaindef]; exact Real.exp_pos _
  have htpos : ∀ v ∈ Sfin, (0 : ℝ) < t v := fun v hv ↦ by
    rw [htdef]; simp only [hv, ite_true]; exact hgpos v.1
  have hpos1 : (0 : ℝ) < C ^ Height.totalWeight K := by positivity
  have hpos2 : (0 : ℝ) < Height.mulHeight xc :=
    lt_of_lt_of_le zero_lt_one (Height.one_le_mulHeight xc)
  have hpos3 : (0 : ℝ) < ∏ θ, Height.mulHeight₁ (β θ) ^ (2 * Dsum) :=
    Finset.prod_pos fun θ _ ↦
      pow_pos (lt_of_lt_of_le zero_lt_one (Height.one_le_mulHeight₁ _)) _
  have hpos4 : (0 : ℝ) < (∏ w : InfinitePlace K, gain w.1 ^ w.mult) * ∏ v ∈ Sfin, t v :=
    mul_pos (Finset.prod_pos fun w _ ↦ pow_pos (hgpos w.1) _)
      (Finset.prod_pos fun v hv ↦ htpos v hv)
  have hlog := Real.log_nonneg hmain
  rw [Real.log_mul (by positivity) hpos4.ne', Real.log_mul (by positivity) hpos3.ne',
    Real.log_mul hpos1.ne' hpos2.ne'] at hlog
  -- the four logarithms
  have hL1 : Real.log (C ^ Height.totalWeight K) = (Height.totalWeight K : ℝ) * Real.log C :=
    Real.log_pow _ _
  have hL2 : Real.log (Height.mulHeight xc) = P.logHeight := by
    rw [MvPolynomial.logHeight_eq_log_mulHeight, MvPolynomial.mulHeight_eq_mulHeight_coeff_box P
      hdeg]
  have hL3 : Real.log (∏ θ, Height.mulHeight₁ (β θ) ^ (2 * Dsum))
      = 2 * (Dsum : ℝ) * ∑ θ, Real.log (Height.mulHeight₁ (β θ)) := by
    rw [Real.log_prod fun θ _ ↦
      (pow_pos (lt_of_lt_of_le zero_lt_one (Height.one_le_mulHeight₁ _)) _).ne']
    have hterm : ∀ θ, Real.log (Height.mulHeight₁ (β θ) ^ (2 * Dsum))
        = 2 * (Dsum : ℝ) * Real.log (Height.mulHeight₁ (β θ)) := by
      intro θ
      rw [Real.log_pow]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun θ _ ↦ hterm θ, ← Finset.mul_sum]
  have e1 : ∀ v : AbsoluteValue K ℝ, Real.log (gain v)
      = D * mean * (∑ j, cf v j) + (D * Δ + ∑ h, q h) * ∑ j, |cf v j| := by
    intro v
    simp only [hgaindef, Real.log_exp]
    ring
  have hL4 : Real.log ((∏ w : InfinitePlace K, gain w.1 ^ w.mult) * ∏ v ∈ Sfin, t v)
      = D * (mean * approxWeight Sfin cf + Δ * approxAbsWeight Sfin cf)
        + (∑ h, q h) * approxAbsWeight Sfin cf := by
    rw [Real.log_mul (Finset.prod_pos fun w _ ↦ pow_pos (hgpos w.1) _).ne'
        (Finset.prod_pos fun v hv ↦ htpos v hv).ne',
      Real.log_prod fun w _ ↦ (pow_pos (hgpos w.1) _).ne',
      Real.log_prod fun v hv ↦ (htpos v hv).ne']
    have e2 : ∑ w : InfinitePlace K, Real.log (gain w.1 ^ w.mult)
        = D * mean * (∑ w : InfinitePlace K, (w.mult : ℝ) * ∑ j, cf w.1 j)
          + (D * Δ + ∑ h, q h) * ∑ w : InfinitePlace K, (w.mult : ℝ) * ∑ j, |cf w.1 j| := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w _ ↦ ?_
      rw [Real.log_pow, e1]
      ring
    have e3 : ∑ v ∈ Sfin, Real.log (t v)
        = D * mean * (∑ v ∈ Sfin, ∑ j, cf v.1 j)
          + (D * Δ + ∑ h, q h) * ∑ v ∈ Sfin, ∑ j, |cf v.1 j| := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v hv ↦ ?_
      have htv : t v = gain v.1 := by rw [htdef]; simp only [hv, ite_true]
      rw [htv, e1]
    rw [e2, e3, approxWeight, approxAbsWeight]
    ring
  rw [hL1, hL2, hL3, hL4] at hlog
  linarith



end KeyInequality

end NumberField

end

end
