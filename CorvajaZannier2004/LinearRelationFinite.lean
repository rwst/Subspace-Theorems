/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import CorvajaZannier2004.LinearRelation

-- Used only inside proofs.
import ArithmeticHeights.Absolute
import ArithmeticHeights.SUnit
import DiophantineApproximation.SubspaceAffine

/-!
# Lemma 1 of Corvaja–Zannier at a finite place

Lemma 1 (p. 3) is stated for any place `w` of `K`; `CorvajaZannier2004.LinearRelation` treats the
archimedean ones. Here `w` is the place of a prime `P ∈ S`, which is what Lemma 4 needs: there `w`
is a finite place at which `α` is not integral.

## Main results

* `NumberField.affineProd_evertseFormsAt`: at a point of `S`-units the affine product of the
  system of Lemma 1 at the place of `P ∈ S` is `w (∑ λⱼ xⱼ) / w (x i₁)`.
* `NumberField.exists_ne_zero_infinite_setOf_sum_eq_zero_of_mem`: Lemma 1 at a finite place, for
  any family of `S`-unit points, against their projective height, `n ≥ 2`.
* `NumberField.exists_ne_zero_infinite_setOf_sum_eq_zero_of_mem_of_tendsto`: the same for points
  whose heights tend to infinity, every `n ≥ 1`.

## References

P. Corvaja and U. Zannier, Acta Math. **193** (2004), 175–191, Lemma 1.
-/

@[expose] public section

open IsDedekindDomain Height Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Classical in
/-- **The forms of Lemma 1 at any place `w`.** The coordinates at every place, except at `w`,
where the `i₁`-th coordinate is replaced by `∑ⱼ c j * x j`. -/
noncomputable def evertseFormsAt (w : AbsoluteValue K ℝ) (i₁ : ι) (c : ι → K) :
    AbsoluteValue K ℝ → ι → Dual K (ι → K) :=
  fun v ↦ if v = w then
    Function.update (fun i ↦ LinearMap.proj i) i₁ (∑ j, c j • LinearMap.proj j)
  else fun i ↦ LinearMap.proj i

/-- At every place the forms of Lemma 1 are linearly independent, as soon as `c i₁ ≠ 0`. -/
theorem linearIndependent_evertseFormsAt (w : AbsoluteValue K ℝ) {i₁ : ι} {c : ι → K}
    (hc : c i₁ ≠ 0) (v : AbsoluteValue K ℝ) :
    LinearIndependent K (evertseFormsAt w i₁ c v) := by
  unfold evertseFormsAt
  split_ifs
  · refine linearIndependent_update_proj ?_
    simpa [Pi.single_apply] using hc
  · have h := linearIndependent_update_proj (K := K) (i₀ := i₁) (f := LinearMap.proj i₁)
      (by simp)
    rwa [Function.update_eq_self] at h

/-- **The affine product of Lemma 1 at a finite place, at a point of `S`-units**, is the single
quotient `w (∑ⱼ c j x j) / w (x i₁)`: every coordinate cancels by the product formula. -/
theorem affineProd_evertseFormsAt (S : Finset (HeightOneSpectrum (𝓞 K)))
    {P : HeightOneSpectrum (𝓞 K)} (hP : P ∈ S) (i₁ : ι) (c : ι → K) {x : ι → Kˣ}
    (hx : ∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    affineProd S (fun v ↦ v) (evertseFormsAt (FinitePlace.mk P).1 i₁ c) (fun i ↦ (x i : K)) =
      FinitePlace.mk P (∑ j, c j * x j) / FinitePlace.mk P (x i₁ : K) := by
  classical
  set w := FinitePlace.mk P with hw
  set r : HeightOneSpectrum (𝓞 K) → ℝ := fun P' ↦
    if P' = P then w (∑ j, c j * x j) / w (x i₁ : K) else 1 with hr
  have hinf : ∀ v : InfinitePlace K,
      ∏ i, v.1 (evertseFormsAt w.1 i₁ c v.1 i fun j ↦ algebraMap K K (x j : K)) =
        ∏ i, v.1 (x i : K) := by
    intro v
    have hv : v.1 ≠ w.1 := InfinitePlace.val_ne_finitePlace_val v w
    simp [evertseFormsAt, hv]
  have hfin : ∀ P' ∈ S,
      ∏ i, (FinitePlace.mk P').1 (evertseFormsAt w.1 i₁ c (FinitePlace.mk P').1 i
        fun j ↦ algebraMap K K (x j : K)) = r P' * ∏ i, (FinitePlace.mk P').1 (x i : K) := by
    intro P' _
    by_cases hP' : P' = P
    · subst hP'
      have hne : w (x i₁ : K) ≠ 0 := by simp
      simp only [evertseFormsAt, ← hw, ite_true, hr, Algebra.algebraMap_self, RingHom.id_apply]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₁),
        ← Finset.mul_prod_erase _ (fun i ↦ w.1 (x i : K)) (Finset.mem_univ i₁),
        Function.update_self]
      rw [Finset.prod_congr rfl fun i hi ↦ by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply,
        LinearMap.proj_apply, smul_eq_mul]
      field_simp
      simp only [show ∀ y : K, w.1 y = w y from fun _ ↦ rfl]
      ring
    · have hne : (FinitePlace.mk P').1 ≠ w.1 := fun h ↦
        hP' (FinitePlace.mk_injective (Subtype.ext h))
      simp [evertseFormsAt, hne, hr, hP']
  have hone : ∀ i, (∏ v : InfinitePlace K, v.1 (x i : K) ^ v.mult) *
      ∏ P' ∈ S, (FinitePlace.mk P').1 (x i : K) = 1 := fun i ↦
    prod_apply_eq_one_of_mem_unit S (hx i)
  unfold affineProd
  rw [Finset.prod_congr rfl fun v _ ↦ by rw [hinf v], Finset.prod_congr rfl hfin]
  simp only [Finset.prod_mul_distrib, ← Finset.prod_pow]
  rw [Finset.prod_comm (s := Finset.univ) (t := Finset.univ), Finset.prod_comm (s := S),
    mul_left_comm, ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun i _ ↦ hone i,
    Finset.prod_const_one, mul_one, Finset.prod_eq_single P (fun P' _ hP' ↦ by simp [hr, hP'])
      (fun h ↦ absurd hP h)]
  simp [hr]

omit [DecidableEq ι] in
/-- **Lemma 1 of Corvaja–Zannier at a finite place**, for any family of `S`-unit points,
`n ≥ 2`. If `P ∈ S`, `w` its place, and infinitely many `u ∈ Ξ` satisfy
`w (∑ i, c i * y u i) < (max_i w (y u i)) * H(y u) ^ (-ε)`, with all `c i ≠ 0` and all `y u i`
`S`-units, then a nonzero `a` has `∑ i, a i * y u i = 0` for infinitely many `u ∈ Ξ`. -/
theorem exists_ne_zero_infinite_setOf_sum_eq_zero_of_mem [Nontrivial ι] {α : Type*}
    (S : Finset (HeightOneSpectrum (𝓞 K))) (y : α → ι → Kˣ) (c : ι → K) (hc : ∀ i, c i ≠ 0)
    {P : HeightOneSpectrum (𝓞 K)} (hP : P ∈ S) {ε : ℝ} (hε : 0 < ε) {Ξ : Set α}
    (hΞ : Ξ.Infinite) (hS : ∀ u ∈ Ξ, ∀ i, y u i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (h : ∀ u ∈ Ξ, FinitePlace.mk P (∑ i, c i * y u i) <
      (⨆ i, FinitePlace.mk P (y u i : K)) * mulHeight (fun i ↦ (y u i : K)) ^ (-ε)) :
    ∃ a : ι → K, a ≠ 0 ∧ {u ∈ Ξ | ∑ i, a i * y u i = 0}.Infinite := by
  classical
  set w := FinitePlace.mk P with hw
  -- the coordinate at which `w` is largest, fixed along an infinite subset
  have hcov : Ξ ⊆ ⋃ i₁ : ι, {u ∈ Ξ | w (y u i₁ : K) = ⨆ i, w (y u i : K)} := by
    intro u hu
    obtain ⟨i₁, hi₁⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ w (y u i : K))
    exact Set.mem_iUnion.mpr ⟨i₁, hu, hi₁⟩
  obtain ⟨i₁, hi₁⟩ : ∃ i₁ : ι, {u ∈ Ξ | w (y u i₁ : K) = ⨆ i, w (y u i : K)}.Infinite := by
    by_contra hne
    push Not at hne
    exact hΞ ((Set.finite_iUnion hne).subset hcov)
  -- the affine Subspace Theorem for the forms of Lemma 1
  obtain ⟨T, hT, hcovT⟩ := exists_finset_submodule_of_integer_of_affineProd_le S (fun v ↦ v)
    (fun _ ↦ ⟨AbsoluteValue.ext fun _ ↦ rfl⟩) (fun _ _ ↦ ⟨AbsoluteValue.ext fun _ ↦ rfl⟩)
    (evertseFormsAt w.1 i₁ c) (fun v ↦ linearIndependent_evertseFormsAt w.1 (hc i₁) v.1)
    (fun v _ ↦ linearIndependent_evertseFormsAt w.1 (hc i₁) _) hε
  have hmemT : ∀ u ∈ {u ∈ Ξ | w (y u i₁ : K) = ⨆ i, w (y u i : K)},
      ∃ W ∈ T, (fun i ↦ (y u i : K)) ∈ W := by
    rintro u ⟨hu, hmax⟩
    refine hcovT _ (fun h0 ↦ (y u i₁).ne_zero (congrFun h0 i₁))
      (fun i ↦ Set.mem_integer_of_mem_unit (hS u hu i)) ?_
    rw [affineProd_evertseFormsAt S hP i₁ c (hS u hu)]
    have hpos : 0 < w (y u i₁ : K) := FinitePlace.pos_iff.mpr (Units.ne_zero _)
    rw [div_le_iff₀ hpos, mul_comm, hmax]
    exact (h u hu).le
  -- one subspace carries infinitely many points
  obtain ⟨W, hWT, hWinf⟩ : ∃ W ∈ T,
      {u ∈ Ξ | w (y u i₁ : K) = ⨆ i, w (y u i : K) ∧ (fun i ↦ (y u i : K)) ∈ W}.Infinite := by
    by_contra hne
    push Not at hne
    refine hi₁ ((T.finite_toSet.biUnion fun W hW ↦ hne W hW).subset fun u hu ↦ ?_)
    obtain ⟨W, hW, hxW⟩ := hmemT u hu
    exact Set.mem_biUnion hW ⟨hu.1, hu.2, hxW⟩
  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_forall_mem_sum_eq_zero (hT W hWT)
  exact ⟨a, ha0, hWinf.mono fun u hu ↦ ⟨hu.1, ha _ hu.2.2⟩⟩

omit [DecidableEq ι] in
/-- **Lemma 1 at a finite place, along a family of growing height**, every `n ≥ 1`. If the heights
`Hf u` tend to infinity along `Ξ`, bound the projective height of the points polynomially, and
`w (∑ c i y u i) < max_i w (y u i) · Hf u ^ (-ε)` at the place `w` of `P ∈ S`, then one nonzero
relation holds infinitely often. For `n = 1` the hypothesis bounds `Hf u`, which leaves only
finitely many `u`. -/
theorem exists_ne_zero_infinite_setOf_sum_eq_zero_of_mem_of_tendsto [Nonempty ι] {α : Type*}
    (S : Finset (HeightOneSpectrum (𝓞 K))) (y : α → ι → Kˣ) (c : ι → K) (hc : ∀ i, c i ≠ 0)
    {P : HeightOneSpectrum (𝓞 K)} (hP : P ∈ S) {ε : ℝ} (hε : 0 < ε) {Ξ : Set α}
    (hΞ : Ξ.Infinite) (hS : ∀ u ∈ Ξ, ∀ i, y u i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (Hf : α → ℝ) (hHf1 : ∀ u, 1 ≤ Hf u) (hHf : ∀ B : ℝ, {u ∈ Ξ | Hf u ≤ B}.Finite) {N : ℕ}
    (hN : 0 < N) (hmul : ∀ u ∈ Ξ, mulHeight (fun i ↦ (y u i : K)) ≤ Hf u ^ N)
    (h : ∀ u ∈ Ξ, FinitePlace.mk P (∑ i, c i * y u i) <
      (⨆ i, FinitePlace.mk P (y u i : K)) * Hf u ^ (-ε)) :
    ∃ a : ι → K, a ≠ 0 ∧ {u ∈ Ξ | ∑ i, a i * y u i = 0}.Infinite := by
  classical
  rcases subsingleton_or_nontrivial ι with hι | hι
  · -- `n = 1`: the hypothesis bounds the height
    exfalso
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have : Unique ι := uniqueOfSubsingleton i₀
    have hc0 : 0 < FinitePlace.mk P (c i₀) := FinitePlace.pos_iff.mpr (hc i₀)
    refine hΞ ((hHf (FinitePlace.mk P (c i₀) ^ (-ε⁻¹))).subset fun u hu ↦ ⟨hu, ?_⟩)
    have hlt := h u hu
    rw [Fintype.sum_subsingleton _ i₀, ciSup_unique, Subsingleton.elim default i₀, map_mul,
      mul_comm, mul_lt_mul_iff_right₀ (FinitePlace.pos_iff.mpr (Units.ne_zero _))] at hlt
    have hA : 0 < Hf u := zero_lt_one.trans_le (hHf1 u)
    have h2 := Real.rpow_le_rpow_of_nonpos hc0 hlt.le (neg_nonpos.mpr (inv_pos.mpr hε).le)
    rwa [← Real.rpow_mul hA.le, neg_mul_neg, mul_inv_cancel₀ hε.ne', Real.rpow_one] at h2
  · refine exists_ne_zero_infinite_setOf_sum_eq_zero_of_mem S y c hc hP (ε := ε / N)
      (by positivity) hΞ hS fun u hu ↦ (h u hu).trans_le (mul_le_mul_of_nonneg_left ?_
        (Real.iSup_nonneg fun i ↦ apply_nonneg _ _))
    have hA : 0 < Hf u := zero_lt_one.trans_le (hHf1 u)
    calc Hf u ^ (-ε) = (Hf u ^ N) ^ (-(ε / N)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le]
          congr 1
          field_simp
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (mulHeight_pos _) (hmul u hu)
          (neg_nonpos.mpr (by positivity))

end NumberField
