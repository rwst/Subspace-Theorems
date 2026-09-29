/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.AffineProd
public import Evertse1984.PlaceProd

-- Used only inside proofs.
import DiophantineApproximation.NormForm
import DiophantineApproximation.SubspaceAffine

/-!
# The forms of Evertse's proof, and the Subspace step

In the proof of Theorem 2 (§2, p. 232) Evertse applies Schlickewei's `p`-adic Subspace Theorem
(his Theorem 4) to the following forms in `x₀, …, xₘ`: at a place `v` of `T` the coordinates, except
that the largest one at `v`, `x_{i₀ᵥ}`, is replaced by the sum `x₀ + ⋯ + xₘ`; at a place of `S`
outside `T`, the coordinates. At every place they are linearly independent, and at a point
`x` their product is

```text
(∏_{k} ∏_{v ∈ S} ‖x_k‖_v) · (∏_{v ∈ T} ‖x₀ + ⋯ + xₘ‖_v) / ∏_{v ∈ T} ‖x_{i₀ᵥ}‖_v.
```

Here the choice of `i₀ᵥ` is a function `r : AbsoluteValue K ℝ → Option ι`, with `T` the places
where it is defined. Theorem 4 is the affine Subspace Theorem of Layer 6.4, and Evertse's size
`‖x‖ ^ (-ε)` is traded for the height `H(x) ^ (-ε / [K : ℚ])`.

## Main definitions

* `NumberField.sumForms`: the forms at every place.

## Main results

* `NumberField.affineProd_sumForms_mul`: the product of the forms at a point.
* `NumberField.exists_finset_submodule_of_prod_placeProd_le`: **the Subspace step**, the points
  with small product lie in finitely many proper subspaces.

## References

J.-H. Evertse, *On sums of `S`-units and linear recurrences*, Compositio Math. **53** (1984),
225–244, §2.
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

omit [DecidableEq ι] in
/-- **The Subspace step of Evertse's proof.** For a choice `r` of largest coordinates at the
places `T = {v | r v ≠ none}` and `ε > 0`, the points of `𝓞_Kⁿ⁺¹` with nonzero coordinates, the
largest coordinate at each `v ∈ T` the one `r` names, and

```text
(∏_{k} ∏_{v ∈ S} ‖x_k‖_v) · ∏_{v ∈ T} ‖x₀ + ⋯ + xₘ‖_v ≤ (∏_{v ∈ T} max_k ‖x_k‖_v) · ‖x‖ ^ (-ε)
```

(Evertse's (20)) lie in finitely many proper subspaces. -/
theorem exists_finset_submodule_of_prod_placeProd_le [Nontrivial ι]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (r : AbsoluteValue K ℝ → Option ι) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ Ws : Finset (Submodule K (ι → K)), (∀ W ∈ Ws, W ≠ ⊤) ∧
      ∀ x : ι → K, (∀ i, IsIntegral ℤ (x i)) → (∀ i, x i ≠ 0) →
        (∀ v i, r v = some i → v (x i) = ⨆ j, v (x j)) →
        (∏ i, placeProd S Set.univ (fun w ↦ w (x i))) *
            placeProd S {w | (r w).isSome} (fun w ↦ w (∑ j, x j)) ≤
          placeProd S {w | (r w).isSome} (fun w ↦ ⨆ j, w (x j)) * (⨆ i, house (x i)) ^ (-ε) →
        ∃ W ∈ Ws, x ∈ W := by
  classical
  set D : ℕ := finrank ℚ K with hD
  have hDpos : (0 : ℝ) < D := by exact_mod_cast Module.finrank_pos
  obtain ⟨Ws, hWs, hcov⟩ := exists_finset_submodule_of_integer_of_affineProd_le (F := K) S
    (fun v ↦ v) (fun _ ↦ ⟨AbsoluteValue.ext fun _ ↦ rfl⟩)
    (fun _ _ ↦ ⟨AbsoluteValue.ext fun _ ↦ rfl⟩) (sumForms r)
    (fun v ↦ linearIndependent_sumForms r v.1) (fun _ _ ↦ linearIndependent_sumForms r _)
    (ε := ε / D) (by positivity)
  refine ⟨Ws, hWs, fun x hint hx0 hr hle ↦ ?_⟩
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hx : x ≠ 0 := fun h ↦ hx0 i₀ (congrFun h i₀)
  refine hcov x hx (fun i ↦ mem_integer_of_isIntegral (hint i)) ?_
  have hM : 0 < placeProd S {w | (r w).isSome} (fun w ↦ ⨆ j, w (x j)) :=
    placeProd_pos S _ fun w _ ↦ (AbsoluteValue.pos w (hx0 i₀)).trans_le
      (le_ciSup (f := fun j ↦ w (x j)) (Finite.bddAbove_range _) i₀)
  have hh : 0 < ⨆ i, house (x i) := zero_lt_one.trans_le (one_le_iSup_house (hint i₀) (hx0 i₀))
  have h1 : affineProd S (fun v ↦ v) (sumForms r) x ≤ (⨆ i, house (x i)) ^ (-ε) := by
    refine le_of_mul_le_mul_right ?_ hM
    rw [affineProd_sumForms_mul S r x hr, mul_comm ((⨆ i, house (x i)) ^ (-ε))]
    exact hle
  refine h1.trans ?_
  calc (⨆ i, house (x i)) ^ (-ε) = ((⨆ i, house (x i)) ^ D) ^ (-(ε / D)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
        congr 1
        field_simp
    _ ≤ mulHeight x ^ (-(ε / D)) :=
        Real.rpow_le_rpow_of_nonpos (mulHeight_pos x) (mulHeight_le_iSup_house_pow hx hint)
          (neg_nonpos.mpr (by positivity))

end NumberField
