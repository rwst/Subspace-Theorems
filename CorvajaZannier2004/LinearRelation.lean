/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.AffineProd
public import Mathlib.NumberTheory.Height.NumberField

-- Used only inside proofs.
import ArithmeticHeights.Absolute
import ArithmeticHeights.SUnit
import DiophantineApproximation.PlacesOver
import DiophantineApproximation.SAdicHeight
import DiophantineApproximation.SubspaceAffine
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Lemma 1 of Corvaja–Zannier: a small linear form in conjugates forces a linear relation

**Lemma 1** (Corvaja–Zannier 2004, p. 3; a special case of a theorem of Evertse). Let
`σ₁, …, σₙ` be automorphisms of a number field `K`, `λ₁, …, λₙ` nonzero elements of `K`, `w` a
place of `K` and `ε > 0`. If infinitely many `S`-units `u` satisfy

```text
|λ₁ σ₁(u) + ⋯ + λₙ σₙ(u)|_w < max_i |σᵢ(u)|_w · H(u) ^ (-ε),
```

then one nontrivial relation `a₁ σ₁(u) + ⋯ + aₙ σₙ(u) = 0`, `aᵢ ∈ K`, holds for infinitely many
of them.

## Main results

* `NumberField.linearIndependent_update_proj`: the coordinate forms with one of them replaced by a
  form with a nonzero coefficient there are linearly independent.
* `NumberField.affineProd_evertseForms`: at a point of `S`-units the affine product of the system
  of Lemma 1 is `(w (∑ λⱼ xⱼ) / w (x i₁)) ^ mult w` — every coordinate cancels by the product
  formula.
* `NumberField.exists_ne_zero_infinite_setOf_sum_eq_zero`: Lemma 1 for any family of `S`-unit
  points, against their projective height, `n ≥ 2`.
* `NumberField.exists_ne_zero_infinite_setOf_sum_algEquiv_eq_zero`: Lemma 1 as stated, with
  automorphisms and the absolute height of `u`, every `n ≥ 1`.

## Implementation notes

⚠ **The affine Subspace Theorem, not the projective one.** The paper divides every form by
`‖x‖_v` and then multiplies back by `|x₁|_w` using that the coordinates are `S`-units. Layer 6.4
(`NumberField.exists_finset_submodule_of_integer_of_affineProd_le`) has no denominators, and at
`S`-unit points every coordinate contributes `1` over `S∞ ∪ S` by the product formula
(`NumberField.prod_apply_eq_one_of_mem_unit`), so the product *equals* the one quotient
`|∑ λⱼ xⱼ|_w / |x_{i₁}|_w`, raised to the local degree.

⚠ **`|·|_w` is Mathlib's place, not the paper's normalized absolute value.** The paper's
`|x|_w` is `w x ^ (mult w / [K:ℚ])`. The hypothesis of the lemma is homogeneous of degree one in
`|·|_w` apart from `H(u) ^ (-ε)`, so the two readings differ by rescaling `ε`, and a statement for
every `ε > 0` is the same statement.

⚠ **`n = 1` is not an application of the Subspace Theorem.** There the hypothesis reads
`w (λ₁) < H(u) ^ (-ε)`, which bounds the height of `u`; by Northcott only finitely many `u`
qualify, and the lemma holds vacuously. The Subspace Theorem needs `n ≥ 2`, and so does the
general form, whose projective height of a one-coordinate point is `1`.

## References

P. Corvaja and U. Zannier, Acta Math. **193** (2004), 175–191, Lemma 1.
-/

@[expose] public section

open IsDedekindDomain Height Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField K] [Fintype ι] in
/-- **The coordinate forms with one of them replaced stay independent**, provided the new form has
a nonzero coefficient at the replaced coordinate. -/
theorem linearIndependent_update_proj [Finite ι] {i₀ : ι} {f : Dual K (ι → K)}
    (hf : f (Pi.single i₀ 1) ≠ 0) :
    LinearIndependent K
      (Function.update (fun i ↦ (LinearMap.proj i : Dual K (ι → K))) i₀ f) := by
  have := Fintype.ofFinite ι
  set F := Function.update (fun i ↦ (LinearMap.proj i : Dual K (ι → K))) i₀ f with hF
  have hval : ∀ i k, F i (Pi.single k 1) =
      if i = i₀ then f (Pi.single k 1) else if i = k then 1 else 0 := by
    intro i k
    by_cases hi : i = i₀
    · subst hi
      simp [hF]
    · simp [hF, hi, Pi.single_apply]
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hev : ∀ k, ∑ i, g i * F i (Pi.single k 1) = 0 := by
    intro k
    have h := congrArg (fun φ : Dual K (ι → K) ↦ φ (Pi.single k 1)) hg
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply] using h
  have h0 : g i₀ = 0 := by
    have h := hev i₀
    rw [Finset.sum_eq_single i₀
      (fun i _ hi ↦ by rw [hval, ite_eq_right hi, ite_eq_right hi, mul_zero]) (by simp), hval,
      ite_eq_left rfl] at h
    exact (mul_eq_zero.mp h).resolve_right hf
  intro k
  by_cases hk : k = i₀
  · rwa [hk]
  · have h := hev k
    rw [Finset.sum_eq_single k (fun i _ hi ↦ ?_) (by simp), hval, ite_eq_right hk, ite_eq_left rfl,
      mul_one] at h
    · exact h
    · rw [hval]
      by_cases h1 : i = i₀
      · rw [ite_eq_left h1, h1, h0, zero_mul]
      · rw [ite_eq_right h1, ite_eq_right hi, mul_zero]

open scoped Classical in
/-- **The forms of Lemma 1.** The coordinates at every place, except at `w`, where the `i₁`-th
coordinate is replaced by `∑ⱼ c j * x j`. -/
noncomputable def evertseForms (w : InfinitePlace K) (i₁ : ι) (c : ι → K) :
    AbsoluteValue K ℝ → ι → Dual K (ι → K) :=
  fun v ↦ if v = w.1 then
    Function.update (fun i ↦ LinearMap.proj i) i₁ (∑ j, c j • LinearMap.proj j)
  else fun i ↦ LinearMap.proj i

/-- At every place the forms of Lemma 1 are linearly independent, as soon as `c i₁ ≠ 0`. -/
theorem linearIndependent_evertseForms (w : InfinitePlace K) {i₁ : ι} {c : ι → K}
    (hc : c i₁ ≠ 0) (v : AbsoluteValue K ℝ) :
    LinearIndependent K (evertseForms w i₁ c v) := by
  unfold evertseForms
  split_ifs
  · refine linearIndependent_update_proj ?_
    simpa [Pi.single_apply] using hc
  · have h := linearIndependent_update_proj (K := K) (i₀ := i₁) (f := LinearMap.proj i₁)
      (by simp)
    rwa [Function.update_eq_self] at h

/-- The product over the places of `S∞ ∪ S` of a fixed `S`-unit's local factors is `1`: the
`S`-product formula, `NumberField.prod_apply_eq_one_of_mem_unit`, restated with `(mk P).1`. -/
private theorem prod_formula (S : Finset (HeightOneSpectrum (𝓞 K))) {u : Kˣ}
    (hu : u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    (∏ v : InfinitePlace K, v.1 (u : K) ^ v.mult) *
      ∏ P ∈ S, (FinitePlace.mk P).1 (u : K) = 1 :=
  prod_apply_eq_one_of_mem_unit S hu

/-- **The affine product of Lemma 1 at a point of `S`-units** is the single quotient
`w (∑ⱼ c j x j) / w (x i₁)`, to the local degree: every coordinate cancels by the product
formula. -/
theorem affineProd_evertseForms (S : Finset (HeightOneSpectrum (𝓞 K))) (w : InfinitePlace K)
    (i₁ : ι) (c : ι → K) {x : ι → Kˣ}
    (hx : ∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    affineProd S (fun v ↦ v) (evertseForms w i₁ c) (fun i ↦ (x i : K)) =
      (w (∑ j, c j * x j) / w (x i₁ : K)) ^ w.mult := by
  classical
  set r : InfinitePlace K → ℝ := fun v ↦ if v = w then w (∑ j, c j * x j) / w (x i₁ : K) else 1
  have hinf : ∀ v : InfinitePlace K,
      ∏ i, v.1 (evertseForms w i₁ c v.1 i fun j ↦ algebraMap K K (x j : K)) =
        r v * ∏ i, v.1 (x i : K) := by
    intro v
    by_cases hv : v = w
    · subst hv
      have hne : v (x i₁ : K) ≠ 0 := by simp
      simp only [evertseForms, ite_true, r, ite_true, Algebra.algebraMap_self, RingHom.id_apply]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₁),
        ← Finset.mul_prod_erase _ (fun i ↦ v.1 (x i : K)) (Finset.mem_univ i₁),
        Function.update_self]
      rw [Finset.prod_congr rfl fun i hi ↦ by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply,
        LinearMap.proj_apply, smul_eq_mul]
      field_simp
      simp only [show ∀ y : K, v.1 y = v y from fun _ ↦ rfl]
      ring
    · have hv' : v.1 ≠ w.1 := fun h ↦ hv (Subtype.ext h)
      simp [evertseForms, hv', r, hv]
  have hfin : ∀ P ∈ S,
      ∏ i, (FinitePlace.mk P).1 (evertseForms w i₁ c (FinitePlace.mk P).1 i
        fun j ↦ algebraMap K K (x j : K)) = ∏ i, (FinitePlace.mk P).1 (x i : K) := by
    intro P _
    have hP : (FinitePlace.mk P).1 ≠ w.1 := fun h ↦
      InfinitePlace.val_ne_finitePlace_val w (FinitePlace.mk P) h.symm
    simp [evertseForms, hP]
  unfold affineProd
  rw [Finset.prod_congr rfl fun v _ ↦ by rw [hinf v], Finset.prod_congr rfl hfin]
  simp only [mul_pow, Finset.prod_mul_distrib, ← Finset.prod_pow]
  rw [Finset.prod_comm (s := Finset.univ) (t := Finset.univ), Finset.prod_comm (s := S), mul_assoc,
    ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun i _ ↦ prod_formula S (hx i),
    Finset.prod_const_one, mul_one, Finset.prod_eq_single w (fun v _ hv ↦ by simp [r, hv])
      (by simp)]
  simp [r]

omit [NumberField K] [DecidableEq ι] in
/-- A proper subspace of `Kⁱ` lies in the kernel of a nonzero linear relation. -/
theorem exists_ne_zero_forall_mem_sum_eq_zero {W : Submodule K (ι → K)} (hW : W ≠ ⊤) :
    ∃ a : ι → K, a ≠ 0 ∧ ∀ x ∈ W, ∑ i, a i * x i = 0 := by
  classical
  obtain ⟨f, hf0, hWf⟩ := W.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hW)
  refine ⟨fun i ↦ f (Pi.single i 1), fun h ↦ hf0 ?_, fun x hx ↦ ?_⟩
  · refine (Pi.basisFun K ι).ext fun i ↦ ?_
    simpa [Pi.basisFun_apply] using congrFun h i
  · have h := LinearMap.mem_ker.mp (hWf hx)
    rw [LinearMap.pi_apply_eq_sum_univ] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    change f (Pi.single i 1) = _
    congr 1
    funext j
    simp [Pi.single_apply, eq_comm]

omit [DecidableEq ι] in
/-- **Lemma 1 of Corvaja–Zannier, for any family of `S`-unit points**, `n ≥ 2`. If infinitely many
`u ∈ Ξ` satisfy `w (∑ i, c i * y u i) < (max_i w (y u i)) * H(y u) ^ (-ε)`, with all `c i ≠ 0`,
all `y u i` `S`-units and `H` the projective height, then a nonzero `a` has
`∑ i, a i * y u i = 0` for infinitely many `u ∈ Ξ`. -/
theorem exists_ne_zero_infinite_setOf_sum_eq_zero [Nontrivial ι] {α : Type*}
    (S : Finset (HeightOneSpectrum (𝓞 K))) (y : α → ι → Kˣ) (c : ι → K) (hc : ∀ i, c i ≠ 0)
    (w : InfinitePlace K) {ε : ℝ} (hε : 0 < ε) {Ξ : Set α} (hΞ : Ξ.Infinite)
    (hS : ∀ u ∈ Ξ, ∀ i, y u i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (h : ∀ u ∈ Ξ, w (∑ i, c i * y u i) <
      (⨆ i, w (y u i : K)) * mulHeight (fun i ↦ (y u i : K)) ^ (-ε)) :
    ∃ a : ι → K, a ≠ 0 ∧ {u ∈ Ξ | ∑ i, a i * y u i = 0}.Infinite := by
  classical
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
    (evertseForms w i₁ c) (fun v ↦ linearIndependent_evertseForms w (hc i₁) v.1)
    (fun v _ ↦ linearIndependent_evertseForms w (hc i₁) _) hε
  have hmemT : ∀ u ∈ {u ∈ Ξ | w (y u i₁ : K) = ⨆ i, w (y u i : K)},
      ∃ W ∈ T, (fun i ↦ (y u i : K)) ∈ W := by
    rintro u ⟨hu, hmax⟩
    refine hcovT _ (fun h0 ↦ (y u i₁).ne_zero (congrFun h0 i₁))
      (fun i ↦ Set.mem_integer_of_mem_unit (hS u hu i)) ?_
    rw [affineProd_evertseForms S w i₁ c (hS u hu)]
    have hpos : 0 < w (y u i₁ : K) := InfinitePlace.pos_iff.mpr (Units.ne_zero _)
    have hH : 0 < mulHeight (fun i ↦ (y u i : K)) ^ (-ε) :=
      Real.rpow_pos_of_pos (mulHeight_pos _) _
    have hle1 : mulHeight (fun i ↦ (y u i : K)) ^ (-ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (one_le_mulHeight _) (by linarith)
    have hq : w (∑ j, c j * y u j) / w (y u i₁ : K) < mulHeight (fun i ↦ (y u i : K)) ^ (-ε) := by
      rw [div_lt_iff₀ hpos, mul_comm, hmax]
      exact h u hu
    have hq0 : 0 ≤ w (∑ j, c j * y u j) / w (y u i₁ : K) := div_nonneg (apply_nonneg _ _) hpos.le
    calc (w (∑ j, c j * y u j) / w (y u i₁ : K)) ^ w.mult
        ≤ w (∑ j, c j * y u j) / w (y u i₁ : K) :=
          pow_le_of_le_one hq0 (hq.le.trans hle1) w.mult_ne_zero
      _ ≤ _ := hq.le
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
/-- The projective height of a tuple of `S`-integers is at most the product of the heights of its
coordinates. -/
theorem mulHeight_le_prod_mulHeight₁ (S : Finset (HeightOneSpectrum (𝓞 K))) {x : ι → K}
    (hx : x ≠ 0) (hxS : ∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) :
    mulHeight x ≤ ∏ i, mulHeight₁ (x i) := by
  classical
  have : Nonempty ι := ⟨(Function.ne_iff.mp hx).choose⟩
  have hsup : ∀ v : AbsoluteValue K ℝ, (⨆ i, v (x i)) ≤ ∏ i, max (v (x i)) 1 := fun v ↦
    ciSup_le fun i ↦ by
      rw [← Finset.mul_prod_erase _ (fun i ↦ max (v (x i)) 1) (Finset.mem_univ i)]
      exact (le_max_left _ _).trans (le_mul_of_one_le_right (zero_le_one.trans (le_max_right _ _))
        (Finset.one_le_prod₀ fun j _ ↦ le_max_right _ _))
  refine (mulHeight_le_prod_of_forall_mem_integer S hx hxS).trans ?_
  rw [Finset.prod_congr rfl fun i _ ↦ mulHeight₁_eq_prod_of_mem_integer S (hxS i),
    Finset.prod_mul_distrib, Finset.prod_comm (s := Finset.univ) (t := Finset.univ),
    Finset.prod_comm (s := Finset.univ) (t := S)]
  refine mul_le_mul (Finset.prod_le_prod₀ (fun v _ ↦ pow_nonneg (Real.iSup_nonneg fun i ↦
    apply_nonneg _ _) _) fun v _ ↦ ?_) (Finset.prod_le_prod₀ (fun P _ ↦ Real.iSup_nonneg fun i ↦
      apply_nonneg _ _) fun P _ ↦ hsup _) (Finset.prod_nonneg fun P _ ↦ Real.iSup_nonneg
        fun i ↦ apply_nonneg _ _) (Finset.prod_nonneg fun v _ ↦ Finset.prod_nonneg fun i _ ↦
          pow_nonneg (zero_le_one.trans (le_max_right _ _)) _)
  rw [Finset.prod_pow]
  exact pow_le_pow_left₀ (Real.iSup_nonneg fun i ↦ apply_nonneg _ _) (hsup v.1) _

omit [DecidableEq ι] in
/-- **Lemma 1 of Corvaja–Zannier** (p. 3). Let `σ : ι → Gal(K/ℚ)`, `c i ≠ 0`, `w` an infinite
place and `ε > 0`. If infinitely many `u ∈ Ξ`, all of whose conjugates `σ i u` are `S`-units,
satisfy `w (∑ i, c i * σ i u) < (max_i w (σ i u)) * H(u) ^ (-ε)`, `H` the absolute height, then a
nonzero `a` has `∑ i, a i * σ i u = 0` for infinitely many `u ∈ Ξ`. -/
theorem exists_ne_zero_infinite_setOf_sum_algEquiv_eq_zero [Nonempty ι]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (σ : ι → K ≃ₐ[ℚ] K) (c : ι → K) (hc : ∀ i, c i ≠ 0)
    (w : InfinitePlace K) {ε : ℝ} (hε : 0 < ε) {Ξ : Set Kˣ} (hΞ : Ξ.Infinite)
    (hS : ∀ u ∈ Ξ, ∀ i, Units.map (σ i : K →* K) u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (h : ∀ u ∈ Ξ, w (∑ i, c i * σ i (u : K)) <
      (⨆ i, w (σ i (u : K))) * absMulHeight₁ (u : K) ^ (-ε)) :
    ∃ a : ι → K, a ≠ 0 ∧ {u ∈ Ξ | ∑ i, a i * σ i (u : K) = 0}.Infinite := by
  classical
  have hHσ : ∀ i (u : Kˣ), absMulHeight₁ (σ i (u : K)) = absMulHeight₁ (u : K) := fun i u ↦
    absMulHeight₁_comp (σ i).toAlgHom (u : K)
  rcases subsingleton_or_nontrivial ι with hι | hι
  · -- `n = 1`: the hypothesis bounds the height, and Northcott leaves finitely many `u`
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have hsum : ∀ u : Kˣ, ∑ i, c i * σ i (u : K) = c i₀ * σ i₀ (u : K) := fun u ↦ by
      rw [Fintype.sum_subsingleton _ i₀]
    have : Unique ι := uniqueOfSubsingleton i₀
    have hsup : ∀ u : Kˣ, (⨆ i, w (σ i (u : K))) = w (σ i₀ (u : K)) := fun u ↦ by
      rw [ciSup_unique, Subsingleton.elim default i₀]
    exfalso
    have hc0 : 0 < w (c i₀) := InfinitePlace.pos_iff.mpr (hc i₀)
    set B : ℝ := (w (c i₀) ^ (-ε⁻¹)) ^ finrank ℚ K
    refine hΞ (((finite_setOfPred_mulHeight₁_le (K := K) B).preimage
      (Units.val_injective.injOn)).subset fun u hu ↦ ?_)
    have hσ0 : 0 < w (σ i₀ (u : K)) := InfinitePlace.pos_iff.mpr (by simp)
    have hlt := h u hu
    rw [hsum, hsup, map_mul, mul_comm, mul_lt_mul_iff_right₀ hσ0] at hlt
    have hA : 0 < absMulHeight₁ (u : K) := zero_lt_one.trans_le (one_le_absMulHeight₁ _)
    -- `w c < H ^ (-ε)` gives `H ≤ (w c) ^ (-1/ε)`
    have hHle : absMulHeight₁ (u : K) ≤ w (c i₀) ^ (-ε⁻¹) := by
      have h2 := Real.rpow_le_rpow_of_nonpos hc0 hlt.le (neg_nonpos.mpr (inv_pos.mpr hε).le)
      rwa [← Real.rpow_mul hA.le, neg_mul_neg, mul_inv_cancel₀ hε.ne', Real.rpow_one] at h2
    change mulHeight₁ (u : K) ≤ B
    rw [← absMulHeight₁_pow_finrank]
    exact pow_le_pow_left₀ hA.le hHle _
  · -- `n ≥ 2`: the general form, against the projective height of the conjugates
    set n := Fintype.card ι
    have hn : 0 < (n : ℝ) := by exact_mod_cast Fintype.card_pos
    have hD : 0 < (finrank ℚ K : ℝ) := by exact_mod_cast finrank_pos
    refine exists_ne_zero_infinite_setOf_sum_eq_zero S
      (fun u i ↦ Units.map (σ i : K →* K) u) c hc w (ε := ε / (n * finrank ℚ K))
      (by positivity) hΞ hS fun u hu ↦ ?_
    refine (h u hu).trans_le (mul_le_mul_of_nonneg_left ?_ (Real.iSup_nonneg fun i ↦
      apply_nonneg _ _))
    -- `H(σ u) ≤ H(u) ^ (n [K:ℚ])`
    have hx0 : (fun i ↦ ((Units.map (σ i : K →* K) u : Kˣ) : K)) ≠ 0 := fun h0 ↦ by
      obtain ⟨i₀⟩ := ‹Nonempty ι›
      exact (Units.map (σ i₀ : K →* K) u).ne_zero (congrFun h0 i₀)
    have hle := mulHeight_le_prod_mulHeight₁ S hx0
      fun i ↦ Set.mem_integer_of_mem_unit (hS u hu i)
    have hprod : ∏ i, mulHeight₁ ((Units.map (σ i : K →* K) u : Kˣ) : K) =
        absMulHeight₁ (u : K) ^ (n * finrank ℚ K) := by
      have h1 : ∀ i, mulHeight₁ ((Units.map (σ i : K →* K) u : Kˣ) : K) =
          absMulHeight₁ (u : K) ^ finrank ℚ K := fun i ↦ by
        rw [← absMulHeight₁_pow_finrank]
        exact congrArg (· ^ finrank ℚ K) (hHσ i u)
      rw [Finset.prod_congr rfl fun i _ ↦ h1 i, Finset.prod_const, Finset.card_univ, ← pow_mul,
        mul_comm]
    rw [hprod] at hle
    have hA : 0 < absMulHeight₁ (u : K) := zero_lt_one.trans_le (one_le_absMulHeight₁ _)
    calc absMulHeight₁ (u : K) ^ (-ε)
        = (absMulHeight₁ (u : K) ^ (n * finrank ℚ K)) ^ (-(ε / (n * finrank ℚ K))) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le]
          congr 1
          push_cast
          field_simp
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (mulHeight_pos _) hle
          (neg_nonpos.mpr (by positivity))

end NumberField
