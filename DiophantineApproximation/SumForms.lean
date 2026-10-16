/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.AffineProd
public import DiophantineApproximation.PlaceProd

-- Used only inside proofs.
import DiophantineApproximation.HeightTransport

/-!
# Sum forms: the coordinates with the largest one replaced by the sum

**Layer 8.8, first piece** (moved from `Evertse1984/SumForms.lean`; used by Evertse 1984 and
Schlickewei 1990). For `x₀, …, xₘ` and a choice `r v` of a coordinate at each place `v`, the forms
at `v` are the coordinates, except that the `r v`-th one is replaced by the sum `x₀ + ⋯ + xₘ`; at
a place where `r v = none`, they are the coordinates. At every place they are linearly
independent, and at a point `x` whose largest coordinate at each `v` is the one `r` names, their
product is

```text
(∏_{k} ∏_{v ∈ S} ‖x_k‖_v) · (∏_{v ∈ T} ‖x₀ + ⋯ + xₘ‖_v) / ∏_{v ∈ T} max_k ‖x_k‖_v,
```

with `T` the places where `r` is defined. These are the forms of Evertse's proof of his
Theorem 2 (§2, p. 232). They are also Schlickewei's forms (3.7) for the homogeneous unit equation
`y₁ + ⋯ + y_{n+1} = 0`: in the coordinates `y₁, …, yₙ`, omitting `y_{i(v)}` and keeping
`y_{n+1} = −(y₁ + ⋯ + yₙ)` is the sum form at `r v = some (i(v))`, and `i(v) = n + 1` is
`r v = none`. The choice `r` is Schlickewei's class (3.12).

## Main definitions

* `NumberField.sumForms`: the forms at every place.

## Main results

* `NumberField.linearIndependent_sumForms`: the forms are linearly independent at every place.
* `NumberField.prod_sumForms_mul`: the product at one place.
* `NumberField.affineProd_sumForms_mul`: the product over `S∞ ∪ S` at a point.
* `NumberField.affineProd_sumForms_mul_eq_prod_option`: the same on the hyperplane
  `y₁ + ⋯ + y_{n+1} = 0`, Schlickewei's (3.14).
* `NumberField.apply_sumForms_le_iSup`: on the hyperplane every form is at most the sup norm.
* `NumberField.det_pi_sumForms`: the forms have determinant `1`.
* `NumberField.apply_sumForms_eq`, `NumberField.det_sumForms_apply`: on the hyperplane each form
  has the size of a coordinate, and the forms at `n` points have the determinant of the points.
* `NumberField.mulHeight_elim_neg_sum_le`: the point on the hyperplane from its first `n`
  coordinates, `H(y₁, …, yₙ, −(y₁ + ⋯ + yₙ)) ≤ n ^ [K : ℚ] H(y₁, …, yₙ)`.

## References

J.-H. Evertse, *On sums of `S`-units and linear recurrences*, Compositio Math. **53** (1984),
225–244, §2. H. P. Schlickewei, *`S`-unit equations over number fields*, Invent. Math. **102**
(1990), 95–107, §3.

This is milestone 8.8 of `DiophantineApproximation/README.md`.
-/

@[expose] public section

open IsDedekindDomain Height Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The forms of Evertse's proof.** At a place `v` with `r v = some a`, the coordinates with the
`a`-th replaced by the sum of all of them; at a place with `r v = none`, the coordinates. -/
noncomputable def sumForms (r : AbsoluteValue K ℝ → Option ι) :
    AbsoluteValue K ℝ → ι → Dual K (ι → K) :=
  fun v ↦ match r v with
  | none => fun i ↦ LinearMap.proj i
  | some a => Function.update (fun i ↦ LinearMap.proj i) a (∑ j, LinearMap.proj j)

omit [NumberField K] in
/-- **The forms are linearly independent at every place.** -/
theorem linearIndependent_sumForms (r : AbsoluteValue K ℝ → Option ι) (v : AbsoluteValue K ℝ) :
    LinearIndependent K (sumForms r v) := by
  unfold sumForms
  cases r v with
  | none =>
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have h := congrArg (fun φ : Dual K (ι → K) ↦ φ (Pi.single k 1)) hg
    simpa [LinearMap.sum_apply, Pi.single_apply] using h
  | some a =>
    set F := Function.update (fun i ↦ (LinearMap.proj i : Dual K (ι → K))) a
      (∑ j, LinearMap.proj j) with hF
    have hval : ∀ i k, F i (Pi.single k 1) = if i = a then 1 else if i = k then 1 else 0 := by
      intro i k
      by_cases hi : i = a
      · subst hi
        simp [hF, Pi.single_apply]
      · simp [hF, hi, Pi.single_apply]
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hev : ∀ k, ∑ i, g i * F i (Pi.single k 1) = 0 := by
      intro k
      have h := congrArg (fun φ : Dual K (ι → K) ↦ φ (Pi.single k 1)) hg
      simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        LinearMap.zero_apply] using h
    have h0 : g a = 0 := by
      have h := hev a
      rw [Finset.sum_eq_single a (fun i _ hi ↦ by simp [hval, hi]) (by simp)] at h
      simpa [hval] using h
    intro k
    by_cases hk : k = a
    · rwa [hk]
    · have h := hev k
      rw [Finset.sum_eq_add a k (Ne.symm hk) (fun i _ ⟨hia, hik⟩ ↦ by simp [hval, hia, hik])
        (by simp) (by simp)] at h
      simpa [hval, hk, h0] using h

omit [NumberField K] in
/-- **The forms at one place, at a point.** When `r v = some a` and the `a`-th coordinate is the
largest at `v`, multiplying by it turns the product of the forms into the size of the sum times
the product of the coordinates. -/
theorem prod_sumForms_mul (r : AbsoluteValue K ℝ → Option ι) (x : ι → K)
    (v : AbsoluteValue K ℝ) (hr : ∀ i, r v = some i → v (x i) = ⨆ j, v (x j)) :
    (∏ i, v (sumForms r v i x)) *
        {w | (r w).isSome}.mulIndicator (fun w ↦ ⨆ j, w (x j)) v =
      {w | (r w).isSome}.mulIndicator (fun w ↦ w (∑ j, x j)) v * ∏ i, v (x i) := by
  cases h : r v with
  | none =>
    have hv : v ∉ {w | (r w).isSome} := by simp [h]
    rw [Set.mulIndicator_of_notMem hv, Set.mulIndicator_of_notMem hv]
    simp [sumForms, h]
  | some a =>
    have hv : v ∈ {w | (r w).isSome} := by simp [h]
    rw [Set.mulIndicator_of_mem hv, Set.mulIndicator_of_mem hv, ← hr a h]
    have hfun : (fun i ↦ v (sumForms r v i x)) =
        Function.update (fun i ↦ v (x i)) a (v (∑ j, x j)) := by
      funext i
      by_cases hi : i = a
      · subst hi
        simp [sumForms, h]
      · simp [sumForms, h, hi]
    rw [show (∏ i, v (sumForms r v i x)) = ∏ i, Function.update (fun i ↦ v (x i)) a
      (v (∑ j, x j)) i from congrArg (fun f ↦ ∏ i, f i) hfun,
      Finset.prod_update_of_mem (Finset.mem_univ a), ← Finset.mul_prod_erase _ _
        (Finset.mem_univ a), Finset.sdiff_singleton_eq_erase]
    ring

/-- **The product of Evertse's forms at a point.** With `T` the places where `r` is defined and
`r` choosing the largest coordinate at each of them, the affine product of the forms times the
product over `T` of the largest coordinates is the product over `S∞ ∪ S` of the coordinates times
the product over `T` of the sum. -/
theorem affineProd_sumForms_mul (S : Finset (HeightOneSpectrum (𝓞 K)))
    (r : AbsoluteValue K ℝ → Option ι) (x : ι → K)
    (hr : ∀ v i, r v = some i → v (x i) = ⨆ j, v (x j)) :
    affineProd S (fun v ↦ v) (sumForms r) x *
        placeProd S {w | (r w).isSome} (fun w ↦ ⨆ j, w (x j)) =
      (∏ i, placeProd S Set.univ (fun w ↦ w (x i))) *
        placeProd S {w | (r w).isSome} (fun w ↦ w (∑ j, x j)) := by
  have key := fun v ↦ prod_sumForms_mul r x v (hr v)
  have hU : ∏ i, placeProd S Set.univ (fun w ↦ w (x i)) =
      (∏ v : InfinitePlace K, (∏ i, v.1 (x i)) ^ v.mult) *
        ∏ P ∈ S, ∏ i, (FinitePlace.mk P).1 (x i) := by
    simp only [placeProd, Set.mulIndicator_univ, Finset.prod_mul_distrib]
    congr 1
    · rw [Finset.prod_comm]
      exact Finset.prod_congr rfl fun v _ ↦ Finset.prod_pow _ _ _
    · exact Finset.prod_comm
  rw [hU]
  unfold affineProd placeProd
  change (∏ v : InfinitePlace K, (∏ i, v.1 (sumForms r v.1 i x)) ^ v.mult) *
      (∏ P ∈ S, ∏ i, (FinitePlace.mk P).1 (sumForms r (FinitePlace.mk P).1 i x)) *
    ((∏ v : InfinitePlace K, {w | (r w).isSome}.mulIndicator (fun w ↦ ⨆ j, w (x j)) v.1
        ^ v.mult) *
      ∏ P ∈ S, {w | (r w).isSome}.mulIndicator (fun w ↦ ⨆ j, w (x j)) (FinitePlace.mk P).1) = _
  calc _ = (∏ v : InfinitePlace K, ((∏ i, v.1 (sumForms r v.1 i x)) *
            {w | (r w).isSome}.mulIndicator (fun w ↦ ⨆ j, w (x j)) v.1) ^ v.mult) *
          ∏ P ∈ S, ((∏ i, (FinitePlace.mk P).1 (sumForms r (FinitePlace.mk P).1 i x)) *
            {w | (r w).isSome}.mulIndicator (fun w ↦ ⨆ j, w (x j)) (FinitePlace.mk P).1) := by
        simp only [mul_pow, Finset.prod_mul_distrib]
        ring
    _ = (∏ v : InfinitePlace K, ({w | (r w).isSome}.mulIndicator (fun w ↦ w (∑ j, x j)) v.1 *
            ∏ i, v.1 (x i)) ^ v.mult) *
          ∏ P ∈ S, ({w | (r w).isSome}.mulIndicator (fun w ↦ w (∑ j, x j)) (FinitePlace.mk P).1 *
            ∏ i, (FinitePlace.mk P).1 (x i)) := by
        congr 1
        · exact Finset.prod_congr rfl fun v _ ↦ by rw [key]
        · exact Finset.prod_congr rfl fun P _ ↦ key _
    _ = _ := by
        simp only [mul_pow, Finset.prod_mul_distrib]
        ring

omit [NumberField K] in
/-- **The forms at one place on the hyperplane `y₁ + ⋯ + y_{n+1} = 0`.** With `none` the
coordinate `y_{n+1}` and the forms in `y₁, …, yₙ`, the sum form is `−y_{n+1}`, so the forms at `v`
are the `y_o` with `o ≠ r v`: their product times `‖y_{r v}‖_v` is the product of all the
coordinates. No choice of largest coordinate is needed. -/
theorem prod_sumForms_mul_eq_prod_option (r : AbsoluteValue K ℝ → Option ι)
    (v : AbsoluteValue K ℝ) {y : Option ι → K} (hy : ∑ o, y o = 0) :
    (∏ i, v (sumForms r v i fun i ↦ y (some i))) * v (y (r v)) = ∏ o, v (y o) := by
  rw [Fintype.prod_option]
  have hsum : v (∑ j, y (some j)) = v (y none) := by
    rw [Fintype.sum_option, add_comm, add_eq_zero_iff_eq_neg] at hy
    rw [hy, map_neg_eq_map]
  cases h : r v with
  | none => simp [sumForms, h, mul_comm]
  | some a =>
    have hfun : (fun i ↦ v (sumForms r v i fun i ↦ y (some i))) =
        Function.update (fun i ↦ v (y (some i))) a (v (y none)) := by
      funext i
      by_cases hi : i = a
      · subst hi
        simp [sumForms, h, hsum]
      · simp [sumForms, h, hi]
    rw [show (∏ i, v (sumForms r v i fun i ↦ y (some i))) = ∏ i, Function.update
      (fun i ↦ v (y (some i))) a (v (y none)) i from congrArg (fun f ↦ ∏ i, f i) hfun,
      Finset.prod_update_of_mem (Finset.mem_univ a), ← Finset.mul_prod_erase _ _
        (Finset.mem_univ a), Finset.sdiff_singleton_eq_erase]
    ring

/-- **The product of the forms on the hyperplane `y₁ + ⋯ + y_{n+1} = 0`** (Schlickewei's (3.11),
(3.14)). For any choice `r`, the affine product of the sum forms at `(y₁, …, yₙ)` times the product
over `S∞ ∪ S` of `‖y_{r v}‖_v` is the product over `S∞ ∪ S` of all the coordinates. -/
theorem affineProd_sumForms_mul_eq_prod_option (S : Finset (HeightOneSpectrum (𝓞 K)))
    (r : AbsoluteValue K ℝ → Option ι) {y : Option ι → K} (hy : ∑ o, y o = 0) :
    affineProd S (fun v ↦ v) (sumForms r) (fun i ↦ y (some i)) *
        placeProd S Set.univ (fun v ↦ v (y (r v))) =
      ∏ o, placeProd S Set.univ (fun v ↦ v (y o)) := by
  have key := fun v ↦ prod_sumForms_mul_eq_prod_option r v hy
  have hU : ∏ o, placeProd S Set.univ (fun w ↦ w (y o)) =
      (∏ v : InfinitePlace K, (∏ o, v.1 (y o)) ^ v.mult) *
        ∏ P ∈ S, ∏ o, (FinitePlace.mk P).1 (y o) := by
    simp only [placeProd, Set.mulIndicator_univ, Finset.prod_mul_distrib]
    congr 1
    · rw [Finset.prod_comm]
      exact Finset.prod_congr rfl fun v _ ↦ Finset.prod_pow _ _ _
    · exact Finset.prod_comm
  rw [hU]
  unfold affineProd placeProd
  simp only [Set.mulIndicator_univ, Algebra.algebraMap_self, RingHom.id_apply]
  calc _ = (∏ v : InfinitePlace K, ((∏ i, v.1 (sumForms r v.1 i fun i ↦ y (some i))) *
            v.1 (y (r v.1))) ^ v.mult) *
          ∏ P ∈ S, ((∏ i, (FinitePlace.mk P).1
            (sumForms r (FinitePlace.mk P).1 i fun i ↦ y (some i))) *
            (FinitePlace.mk P).1 (y (r (FinitePlace.mk P).1))) := by
        simp only [mul_pow, Finset.prod_mul_distrib]
        ring
    _ = _ := by simp only [key]

omit [NumberField K] in
/-- **On the hyperplane, every form is at most the sup norm of `(y₁, …, yₙ)`** at a place where
`r v` names a largest of the `n + 1` coordinates: the sum form is `−y_{n+1}`, and
`‖y_{n+1}‖_v ≤ ‖y_{r v}‖_v`. -/
theorem apply_sumForms_le_iSup (r : AbsoluteValue K ℝ → Option ι) (v : AbsoluteValue K ℝ)
    {y : Option ι → K} (hy : ∑ o, y o = 0) (hr : v (y (r v)) = ⨆ o, v (y o)) (i : ι) :
    v (sumForms r v i fun i ↦ y (some i)) ≤ ⨆ j, v (y (some j)) := by
  have hle : ∀ j, v (y (some j)) ≤ ⨆ j, v (y (some j)) := fun j ↦
    le_ciSup (f := fun j ↦ v (y (some j))) (Finite.bddAbove_range _) j
  have hsum : v (∑ j, y (some j)) = v (y none) := by
    rw [Fintype.sum_option, add_comm, add_eq_zero_iff_eq_neg] at hy
    rw [hy, map_neg_eq_map]
  cases h : r v with
  | none => simpa [sumForms, h] using hle i
  | some a =>
    rw [h] at hr
    by_cases hi : i = a
    · subst hi
      have hval : v (sumForms r v i fun i ↦ y (some i)) = v (y none) := by
        simp [sumForms, h, hsum]
      rw [hval]
      exact (le_ciSup (f := fun o ↦ v (y o)) (Finite.bddAbove_range _) none).trans
        (hr.symm.le.trans (hle i))
    · simpa [sumForms, h, hi] using hle i

omit [NumberField K] in
/-- **The forms have determinant `1`** at every place: the identity with one row replaced by the
sum of all rows. -/
theorem det_pi_sumForms (r : AbsoluteValue K ℝ → Option ι) (v : AbsoluteValue K ℝ) :
    LinearMap.det (LinearMap.pi (sumForms r v)) = 1 := by
  unfold sumForms
  cases r v with
  | none =>
    have h : LinearMap.pi (fun i ↦ (LinearMap.proj i : Dual K (ι → K))) = LinearMap.id := by
      ext; simp
    rw [h, LinearMap.det_id]
  | some a =>
    rw [← LinearMap.det_toMatrix (Pi.basisFun K ι)]
    have hM : LinearMap.toMatrix (Pi.basisFun K ι) (Pi.basisFun K ι) (LinearMap.pi
        (Function.update (fun i ↦ (LinearMap.proj i : Dual K (ι → K))) a
          (∑ j, LinearMap.proj j))) =
        (1 : Matrix ι ι K).updateRow a (∑ k, (1 : K) • (1 : Matrix ι ι K) k) := by
      ext i j
      rw [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr]
      by_cases hi : i = a
      · subst hi
        simp only [Matrix.updateRow_self, one_smul]
        rw [show (∑ k, (1 : Matrix ι ι K) k) = fun j ↦ ∑ k, (1 : Matrix ι ι K) k j from
          funext fun j ↦ Finset.sum_apply j _ _]
        simp [Pi.single_apply, Matrix.one_apply]
      · simp [hi, Pi.single_apply, Matrix.one_apply]
    rw [hM, Matrix.det_updateRow_sum, Matrix.det_one, smul_eq_mul, mul_one]

omit [NumberField K] in
/-- **The sup norm is at most `n` times the largest form** at every place: the replaced
coordinate is the sum form minus the others. -/
theorem iSup_le_card_mul_iSup_sumForms (r : AbsoluteValue K ℝ → Option ι)
    (v : AbsoluteValue K ℝ) (y : ι → K) :
    ⨆ j, v (y j) ≤ Fintype.card ι * ⨆ i, v (sumForms r v i y) := by
  set M := ⨆ i, v (sumForms r v i y) with hM
  have hle : ∀ i, v (sumForms r v i y) ≤ M := fun i ↦
    le_ciSup (f := fun i ↦ v (sumForms r v i y)) (Finite.bddAbove_range _) i
  have hM0 : 0 ≤ M := Real.iSup_nonneg fun _ ↦ v.nonneg _
  refine Real.iSup_le (fun j ↦ ?_) (by positivity)
  have hn : (1 : ℝ) ≤ Fintype.card ι := Nat.one_le_cast.2 (Fintype.card_pos_iff.2 ⟨j⟩)
  have hoth : ∀ i, r v ≠ some i → v (y i) ≤ M := fun i hi ↦ by
    have := hle i
    cases h : r v with
    | none => simpa [sumForms, h] using this
    | some a =>
      have hia : i ≠ a := fun e ↦ hi (by rw [h, e])
      simpa [sumForms, h, hia] using this
  by_cases hj : r v = some j
  · have hsum : v (∑ i, y i) ≤ M := by simpa [sumForms, hj] using hle j
    have he : y j = (∑ i, y i) - ∑ i ∈ Finset.univ.erase j, y i := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      ring
    have hrest : ∑ i ∈ Finset.univ.erase j, v (y i) ≤ ∑ _i ∈ Finset.univ.erase j, M :=
      Finset.sum_le_sum fun i hi ↦ hoth i fun h ↦
        Finset.ne_of_mem_erase hi (Option.some_injective _ (hj.symm.trans h)).symm
    have hcard : ((Finset.univ.erase j).card : ℝ) + 1 = Fintype.card ι := by
      exact_mod_cast Finset.card_erase_add_one (Finset.mem_univ j)
    rw [Finset.sum_const, nsmul_eq_mul] at hrest
    calc v (y j) = v ((∑ i, y i) + -∑ i ∈ Finset.univ.erase j, y i) := by
          rw [← sub_eq_add_neg, ← he]
      _ ≤ v (∑ i, y i) + v (∑ i ∈ Finset.univ.erase j, y i) := by
          rw [← map_neg_eq_map v (∑ i ∈ Finset.univ.erase j, y i)]
          exact v.add_le _ _
      _ ≤ M + ∑ i ∈ Finset.univ.erase j, v (y i) := by gcongr; exact v.sum_le _ _
      _ ≤ Fintype.card ι * M := by rw [← hcard]; linarith
  · exact (hoth j hj).trans (le_mul_of_one_le_left hM0 hn)

omit [NumberField K] in
/-- **On the hyperplane with nonzero coordinates, no form vanishes**: the forms are coordinates of
`y`, and the sum form is `−y_{n+1}`. -/
theorem sumForms_ne_zero (r : AbsoluteValue K ℝ → Option ι) (v : AbsoluteValue K ℝ)
    {y : Option ι → K} (hy : ∑ o, y o = 0) (hy0 : ∀ o, y o ≠ 0) (i : ι) :
    sumForms r v i (fun i ↦ y (some i)) ≠ 0 := by
  have hsum : ∑ j, y (some j) = -y none := by
    rw [Fintype.sum_option, add_comm, add_eq_zero_iff_eq_neg] at hy
    exact hy
  cases h : r v with
  | none => simpa [sumForms, h] using hy0 (some i)
  | some a =>
    by_cases hi : i = a
    · subst hi
      simpa [sumForms, h, hsum] using hy0 none
    · simpa [sumForms, h, hi] using hy0 (some i)

omit [NumberField K] in
/-- **Every form is one of `n + 1`**: a coordinate or the sum of all of them. -/
theorem sumForms_mem_range (r : AbsoluteValue K ℝ → Option ι) (v : AbsoluteValue K ℝ) (i : ι) :
    sumForms r v i ∈
      Set.range fun o : Option ι ↦ o.elim (∑ j, LinearMap.proj j) fun j ↦ LinearMap.proj j := by
  cases h : r v with
  | none => exact ⟨some i, by simp [sumForms, h]⟩
  | some a =>
    by_cases hi : i = a
    · subst hi
      exact ⟨none, by simp [sumForms, h]⟩
    · exact ⟨some i, by simp [sumForms, h, hi]⟩

omit [NumberField K] in
/-- **The coefficients of a form are `0` or `1`.** -/
theorem sumForms_basisFun (r : AbsoluteValue K ℝ → Option ι) (v : AbsoluteValue K ℝ) (i j : ι) :
    sumForms r v i (Pi.basisFun K ι j) = 0 ∨ sumForms r v i (Pi.basisFun K ι j) = 1 := by
  obtain ⟨o, ho⟩ := sumForms_mem_range r v i
  rw [← ho]
  cases o with
  | none => exact Or.inr (by simp)
  | some k =>
    by_cases hk : j = k
    · exact Or.inr (by simp [hk])
    · exact Or.inl (by simp [Ne.symm hk])

omit [NumberField K] in
/-- **On the hyperplane, every form is a coordinate up to sign**: at `v` the `i`-th form has the
size of `y_{n+1}` if it is the sum form (`r v = some i`), and of `yᵢ` otherwise. -/
theorem apply_sumForms_eq (r : AbsoluteValue K ℝ → Option ι) (v : AbsoluteValue K ℝ)
    {y : Option ι → K} (hy : ∑ o, y o = 0) (i : ι) :
    v (sumForms r v i fun i ↦ y (some i)) = v (y (if r v = some i then none else some i)) := by
  have hsum : v (∑ j, y (some j)) = v (y none) := by
    rw [Fintype.sum_option, add_comm, add_eq_zero_iff_eq_neg] at hy
    rw [hy, map_neg_eq_map]
  cases h : r v with
  | none => simp [sumForms, h]
  | some a =>
    by_cases hi : i = a
    · subst hi
      simp [sumForms, h, hsum]
    · simp [sumForms, h, hi, Ne.symm hi]

omit [NumberField K] in
/-- **The forms at `n` points have the determinant of the points**, the forms having
determinant `1` (`NumberField.det_pi_sumForms`). -/
theorem det_sumForms_apply (r : AbsoluteValue K ℝ → Option ι) (v : AbsoluteValue K ℝ)
    (y : ι → ι → K) :
    (Matrix.of fun i j ↦ sumForms r v i (y j)).det = (Pi.basisFun K ι).det y := by
  have hM : (Matrix.of fun i j ↦ sumForms r v i (y j)) =
      LinearMap.toMatrix' (LinearMap.pi (sumForms r v)) * (Matrix.of y).transpose := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, LinearMap.toMatrix'_apply, LinearMap.pi_apply,
      Matrix.transpose_apply]
    conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ (sumForms r v i)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    funext l
    rw [Pi.single_apply]
    exact if_congr eq_comm rfl rfl
  rw [hM, Matrix.det_mul, LinearMap.det_toMatrix', det_pi_sumForms, one_mul,
    Matrix.det_transpose, Pi.basisFun_det_apply]

omit [DecidableEq ι] in
/-- **The point on the hyperplane from its first `n` coordinates**:
`H(y₁, …, yₙ, −(y₁ + ⋯ + yₙ)) ≤ n ^ [K : ℚ] H(y₁, …, yₙ)`. At an archimedean place the new
coordinate is at most `n` times the largest one, at a nonarchimedean place at most the largest. -/
theorem mulHeight_elim_neg_sum_le [Nonempty ι] (z : ι → K) :
    mulHeight (fun o : Option ι ↦ o.elim (-∑ i, z i) z) ≤
      (Fintype.card ι : ℝ) ^ finrank ℚ K * mulHeight z := by
  have hn : (1 : ℝ) ≤ Fintype.card ι := Nat.one_le_cast.2 Fintype.card_pos
  rcases eq_or_ne z 0 with rfl | hz
  · have : (fun o : Option ι ↦ o.elim (-∑ i, (0 : ι → K) i) 0) = 0 := by
      funext o
      cases o <;> simp
    rw [this, mulHeight_zero, mulHeight_zero, mul_one]
    exact one_le_pow₀ hn
  have hz' : Finsupp.equivFunOnFinite.symm z ≠ 0 := fun h ↦
    hz (by rw [← Finsupp.coe_equivFunOnFinite_symm z, h, Finsupp.coe_zero])
  have hle : ∀ v : AbsoluteValue K ℝ, ∀ c : ℝ, (∀ i, v (z i) ≤ c * ⨆ j, v (z j)) →
      v (-∑ i, z i) ≤ c * ⨆ j, v (z j) →
      (⨆ o : Option ι, v (o.elim (-∑ i, z i) z)) ≤ c * ⨆ j, v (z j) := fun v c h1 h2 ↦ by
    have : Nonempty (Option ι) := ⟨none⟩
    exact ciSup_le fun o ↦ by cases o with
      | none => exact h2
      | some i => exact h1 i
  have hsup : ∀ v : AbsoluteValue K ℝ, ∀ i, v (z i) ≤ ⨆ j, v (z j) := fun v i ↦
    le_ciSup (f := fun j ↦ v (z j)) (Finite.bddAbove_range _) i
  have h := Finsupp.mulHeight_le_pow_of_forall_iSup_le (p := 1)
    (z := Finsupp.equivFunOnFinite.symm fun o : Option ι ↦ o.elim (-∑ i, z i) z) hz' hn
    (fun v _ ↦ by
      simp only [Finsupp.coe_equivFunOnFinite_symm, pow_one]
      refine hle v _ (fun i ↦ (hsup v i).trans (le_mul_of_one_le_left
        (Real.iSup_nonneg fun _ ↦ v.nonneg _) hn)) ?_
      rw [map_neg_eq_map]
      calc v (∑ i, z i) ≤ ∑ i, v (z i) := v.sum_le _ _
        _ ≤ ∑ _i : ι, ⨆ j, v (z j) := Finset.sum_le_sum fun i _ ↦ hsup v i
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ])
    (fun v hv ↦ by
      simp only [Finsupp.coe_equivFunOnFinite_symm, pow_one]
      rw [← one_mul (⨆ j, v (z j))]
      refine hle v 1 (fun i ↦ (one_mul (⨆ j, v (z j))).symm ▸ hsup v i) ?_
      rw [map_neg_eq_map, one_mul]
      obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
      refine ((AdmissibleAbsValues.isNonarchimedean v hv).apply_sum_le_sup
        Finset.univ_nonempty).trans (Finset.sup'_le _ _ fun i _ ↦ hsup v i))
  rw [← Finsupp.mulHeight_coe_eq, ← Finsupp.mulHeight_coe_eq, pow_one,
    totalWeight_eq_finrank] at h
  simpa using h

end NumberField
