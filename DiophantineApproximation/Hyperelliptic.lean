/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.SUnit
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.SplittingField.Construction

-- Used only inside proofs.
import DiophantineApproximation.SIntegerExtension
import DiophantineApproximation.SIntegerSquares
import DiophantineApproximation.UnitEquation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Perfect

/-!
# The hyperelliptic equation

**Layer 8.5** (Siegel 1926; Bombieri–Gubler, Theorem 5.3.5). Let `K` be a number field, `S` a
finite set of primes of `𝓞 K`, `b ∈ Kˣ` and `f ∈ K[X]` with at least three distinct roots of odd
multiplicity in an algebraically closed field `Ω ⊇ K`. Then `b y ^ 2 = f (x)` has finitely many
solutions in `S`-integers. In particular this holds when `f` is squarefree of degree at least `3`,
which is the book's statement.

## Main results

* `NumberField.finite_setOf_mul_sq_eq_eval_of_splits`: the theorem when `f` splits over `K`.
* `NumberField.finite_setOf_mul_sq_eq_eval`: the theorem.
* `NumberField.finite_setOf_mul_sq_eq_eval_of_squarefree`: the book's form.

## Route

For three roots `α₁, α₂, α₃` of odd multiplicity, enlarge `S` until the leading coefficient, `b`,
the nonzero roots and the nonzero differences of roots are units and the `S`-integers form a
principal ideal domain. At a solution `x - αᵢ` is coprime to the other linear factors of `f(x)`,
so it is one of finitely many constants `eᵢ` times a square (`DiophantineApproximation/
SIntegerSquares.lean`). Adjoin square roots of all the constants: then `x - αᵢ = δᵢ ^ 2`, the
`δᵢ` are integral above `S`, and `(δᵢ - δⱼ)(δᵢ + δⱼ) = αⱼ - αᵢ` makes both factors units.
**Siegel's identity**

```text
(δ₁ - δ₂) / (δ₁ - δ₃) + (δ₂ - δ₃) / (δ₁ - δ₃) = 1
```

is a unit equation, with finitely many solutions (Layer 8.1), and the ratio `t` it produces
determines `x`: `(δ₁ - δ₃) ^ 2 = (t (α₃ - α₁) - (α₂ - α₁)) / (t (t - 1))`, and
`2 (δ₁ - δ₃) δ₁ = (δ₁ - δ₃) ^ 2 + (α₃ - α₁)`. Each `x` carries at most two `y`.

## Implementation notes

⚠ **Odd multiplicity is enough, and is the right hypothesis.** The coprimality argument needs
nothing of the other roots, and an odd power of `x - α` is a unit times a square exactly when
`x - α` is. So the theorem holds for `f` with three roots of odd multiplicity, not only for
squarefree `f`; the rejection tests below show that neither "three" nor "odd" can be dropped.

⚠ **One unit equation, and nothing above 8.1.** The book recovers `x` from the finitely many
values of the three differences. Here a single ratio `t` does it, by the two displayed identities,
so the finite set is the image of the solutions of one unit equation under an explicit rational
function. No 8.2, no Subspace Theorem and no heights are used.

⚠ **Two extensions, both splitting fields, and no degree is computed.** The roots live in the
splitting field of `f`; the square roots in the splitting field over it of
`∏ₑ (X ^ 2 - e)`. Both passages are 8.4's `SIntegerExtension.lean`, used in the forward direction
only.

⚠ **Qualitative only.** The book's count of the solutions rests on the Beukers–Schlickewei bound,
which is not built.

This is Layer 8.5 of the `DiophantineApproximation` roadmap.
-/

public section

open IsDedekindDomain NumberField Polynomial

/-- **The ratio in Siegel's identity determines `x`.** If `δᵢ ^ 2 = x - aᵢ` for three distinct
`aᵢ` and `t (δ₁ - δ₃) = δ₁ - δ₂`, then `x` is a rational function of `t` and the `aᵢ`. -/
private theorem eq_of_sq_eq_sub {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {x a₁ a₂ a₃ δ₁ δ₂ δ₃ t : F} (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h23 : a₂ ≠ a₃)
    (hδ₁ : δ₁ ^ 2 = x - a₁) (hδ₂ : δ₂ ^ 2 = x - a₂) (hδ₃ : δ₃ ^ 2 = x - a₃)
    (ht : t * (δ₁ - δ₃) = δ₁ - δ₂) :
    x = a₁ + ((t * (a₃ - a₁) - (a₂ - a₁)) / (t * (t - 1)) + (a₃ - a₁)) ^ 2 /
      (4 * ((t * (a₃ - a₁) - (a₂ - a₁)) / (t * (t - 1)))) := by
  have hB : δ₁ - δ₃ ≠ 0 := fun h ↦ h13 (by
    rw [sub_eq_zero.mp h] at hδ₁
    linear_combination hδ₁ - hδ₃)
  have hA : δ₁ - δ₂ ≠ 0 := fun h ↦ h12 (by
    rw [sub_eq_zero.mp h] at hδ₁
    linear_combination hδ₁ - hδ₂)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hA (by rw [← ht, zero_mul])
  have ht1 : t - 1 ≠ 0 := fun h ↦ h23 (by
    rw [sub_eq_zero.mp h, one_mul] at ht
    rw [show δ₂ = δ₃ by linear_combination ht] at hδ₂
    linear_combination hδ₂ - hδ₃)
  have hδ₂' : δ₂ = δ₁ - t * (δ₁ - δ₃) := by linear_combination ht
  subst hδ₂'
  have hβ : (t * (a₃ - a₁) - (a₂ - a₁)) / (t * (t - 1)) = (δ₁ - δ₃) ^ 2 := by
    rw [div_eq_iff (mul_ne_zero ht0 ht1)]
    linear_combination (hδ₁ - hδ₂) - t * (hδ₁ - hδ₃)
  have hc : (δ₁ - δ₃) ^ 2 + (a₃ - a₁) = 2 * (δ₁ - δ₃) * δ₁ := by
    linear_combination hδ₃ - hδ₁
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  rw [hβ, hc, show (2 * (δ₁ - δ₃) * δ₁) ^ 2 / (4 * (δ₁ - δ₃) ^ 2) = δ₁ ^ 2 by
    rw [div_eq_iff (mul_ne_zero h4 (pow_ne_zero 2 hB))]
    ring, hδ₁]
  ring

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- For `y` with `y ^ 2 = c` there are finitely many choices. -/
private theorem finite_setOf_sq_eq (c : K) : {y : K | y ^ 2 = c}.Finite := by
  classical
  refine ((X ^ 2 - C c).roots.toFinset.finite_toSet).subset fun y hy ↦ ?_
  simp only [Set.mem_ofPred_eq] at hy
  simp [mem_roots (X_pow_sub_C_ne_zero two_pos c), hy]

/-- **Siegel's theorem on the hyperelliptic equation, split case.** If `f ∈ K[X]` splits over `K`
and has at least three distinct roots of odd multiplicity, then for `b ≠ 0` the equation
`b y ^ 2 = f (x)` has finitely many solutions in `S`-integers. -/
theorem finite_setOf_mul_sq_eq_eval_of_splits [DecidableEq K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {f : K[X]} (hf : f.Splits)
    (h3 : 3 ≤ (f.roots.toFinset.filter fun r ↦ Odd (f.roots.count r)).card)
    {b : K} (hb : b ≠ 0) :
    {p : K × K | p.1 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K ∧
      p.2 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K ∧ b * p.2 ^ 2 = f.eval p.1}.Finite := by
  classical
  obtain ⟨α₁, h₁, α₂, h₂, α₃, h₃, h12, h13, h23⟩ := Finset.two_lt_card.mp h3
  simp only [Finset.mem_filter, Multiset.mem_toFinset] at h₁ h₂ h₃
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at h₁
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  set R₀ := f.roots.toFinset with hR₀
  obtain ⟨T, hST, hTfin, hPID, hTunit⟩ := exists_finite_superset_forall_mem_unit S.finite_toSet
    (insert f.leadingCoeff (insert b (R₀ ∪ (R₀ ×ˢ R₀).image fun p ↦ p.1 - p.2)))
  have hlcT : Units.mk0 _ hlc ∈ T.unit K := hTunit _ (by simp) hlc
  have hbT : Units.mk0 _ hb ∈ T.unit K := hTunit _ (by simp) hb
  have hrootT : ∀ r ∈ f.roots, r ∈ T.integer K := fun r hr ↦ by
    by_cases hr0 : r = 0
    · rw [hr0]
      exact zero_mem _
    · exact Set.mem_integer_of_mem_unit (hTunit r (by simp [hR₀, hr]) hr0)
  have hdiffT : ∀ r ∈ f.roots, ∀ r' ∈ f.roots, ∀ h : r - r' ≠ 0, Units.mk0 _ h ∈ T.unit K :=
    fun r hr r' hr' h ↦ hTunit _ (by
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_product]
      exact Or.inr (Or.inr (Or.inr ⟨(r, r'), ⟨by simp [hR₀, hr], by simp [hR₀, hr']⟩, rfl⟩))) h
  obtain ⟨E, hE⟩ := exists_finset_forall_eq_mul_sq hTfin
  -- At a solution, `x - α` is one of finitely many constants times a square.
  have hsq : ∀ x y : K, x ∈ T.integer K → y ∈ T.integer K → b * y ^ 2 = f.eval x →
      ∀ α ∈ f.roots, Odd (f.roots.count α) → ∃ e ∈ E, ∃ γ : K, x - α = e * γ ^ 2 := by
    intro x y hx hy hxy α hα hodd
    have hsplit : f.roots =
        Multiset.replicate (f.roots.count α) α + f.roots.filter fun r ↦ ¬ r = α := by
      rw [← Multiset.filter_eq', Multiset.filter_add_not]
    have heval := hf.eval_eq_prod_roots x
    rw [hsplit, Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
      Multiset.prod_replicate] at heval
    have hs : ∀ w ∈ (f.roots.filter fun r ↦ ¬ r = α).map (x - ·),
        w ∈ T.integer K ∧ ∃ v ∈ T.unit K, (v : K) = w - (x - α) := by
      intro w hw
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hw
      rw [Multiset.mem_filter] at hr
      refine ⟨sub_mem hx (hrootT r hr.1), _,
        hdiffT α hα r hr.1 (sub_ne_zero.mpr (Ne.symm hr.2)), ?_⟩
      rw [Units.val_mk0]
      ring
    have hprod : (x - α) ^ f.roots.count α *
        ((f.roots.filter fun r ↦ ¬ r = α).map (x - ·)).prod =
        ((Units.mk0 _ hb / Units.mk0 _ hlc : Kˣ) : K) * y ^ 2 := by
      rw [Units.val_div_eq_div_val, Units.val_mk0, Units.val_mk0, div_mul_eq_mul_div, hxy, heval,
        mul_div_cancel_left₀ _ hlc]
    obtain ⟨v, hv, γ, hγ⟩ := exists_eq_mul_sq_of_pow_mul_prod_eq (S := T) hodd
      (sub_mem hx (hrootT α hα)) hs hy (div_mem hbT hlcT) hprod
    obtain ⟨e, he, h, hh⟩ := hE v hv
    exact ⟨e, he, h * γ, by rw [hγ, hh]; ring⟩
  -- The square roots of the constants.
  let P : K[X] := ∏ e ∈ E, (X ^ 2 - C e)
  let L := P.SplittingField
  have : NumberField L := NumberField.of_module_finite K L
  have hroot : ∀ e ∈ E, ∃ σ : L, σ ^ 2 = algebraMap K L e := by
    intro e he
    have hP0 : P.map (algebraMap K L) ≠ 0 :=
      Polynomial.map_ne_zero (Finset.prod_ne_zero_iff.mpr fun e _ ↦ X_pow_sub_C_ne_zero two_pos e)
    have hdvd : (X ^ 2 - C e).map (algebraMap K L) ∣ P.map (algebraMap K L) :=
      Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ he)
    obtain ⟨σ, hσ⟩ := ((SplittingField.splits P).of_dvd hP0 hdvd).exists_eval_eq_zero
      (by rw [degree_map, degree_X_pow_sub_C two_pos]; decide)
    refine ⟨σ, ?_⟩
    simpa [sub_eq_zero] using hσ
  choose! σ hσ using hroot
  set T' : Set (HeightOneSpectrum (𝓞 L)) := HeightOneSpectrum.under (𝓞 K) ⁻¹' T with hT'
  have hT'fin : T'.Finite := finite_preimage_under L hTfin
  set ι := algebraMap K L
  have hι₁₂ : ι α₁ ≠ ι α₂ := fun h ↦ h12 (ι.injective h)
  have hι₁₃ : ι α₁ ≠ ι α₃ := fun h ↦ h13 (ι.injective h)
  have hι₂₃ : ι α₂ ≠ ι α₃ := fun h ↦ h23 (ι.injective h)
  set U := {p : Lˣ × Lˣ | p.1 ∈ (hT'fin.toFinset : Set (HeightOneSpectrum (𝓞 L))).unit L ∧
    p.2 ∈ (hT'fin.toFinset : Set (HeightOneSpectrum (𝓞 L))).unit L ∧
    ((1 : Lˣ) : L) * p.1 + ((1 : Lˣ) : L) * p.2 = 1} with hU
  have hUfin : U.Finite := finite_setOf_unit_add_unit_eq_one hT'fin.toFinset 1 1
  set Φ : Lˣ × Lˣ → L := fun p ↦ ι α₁ +
    (((p.1 : L) * (ι α₃ - ι α₁) - (ι α₂ - ι α₁)) / ((p.1 : L) * ((p.1 : L) - 1)) +
      (ι α₃ - ι α₁)) ^ 2 /
    (4 * (((p.1 : L) * (ι α₃ - ι α₁) - (ι α₂ - ι α₁)) / ((p.1 : L) * ((p.1 : L) - 1))))
  -- The `x` of a solution is determined by a solution of Siegel's unit equation.
  have hX : ∀ x y : K, x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K →
      y ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K → b * y ^ 2 = f.eval x →
      ι x ∈ Φ '' U := by
    intro x y hx hy hxy
    have hxT := mem_integer_of_subset hST hx
    have hyT := mem_integer_of_subset hST hy
    have hδ : ∀ α ∈ f.roots, Odd (f.roots.count α) →
        ∃ δ ∈ T'.integer L, δ ^ 2 = ι x - ι α := by
      intro α hα hodd
      obtain ⟨e, he, γ, hγ⟩ := hsq x y hxT hyT hxy α hα hodd
      have hδ2 : (σ e * ι γ) ^ 2 = ι x - ι α := by
        rw [mul_pow, hσ e he, ← map_pow, ← map_mul, ← hγ, map_sub]
      refine ⟨σ e * ι γ, mem_integer_of_sq_mem ?_, hδ2⟩
      rw [hδ2, ← map_sub]
      exact algebraMap_mem_integer_iff.mpr (sub_mem hxT (hrootT α hα))
    obtain ⟨δ₁, hδ₁, hδ₁2⟩ := hδ α₁ h₁.1 h₁.2
    obtain ⟨δ₂, hδ₂, hδ₂2⟩ := hδ α₂ h₂.1 h₂.2
    obtain ⟨δ₃, hδ₃, hδ₃2⟩ := hδ α₃ h₃.1 h₃.2
    have hunit : ∀ α ∈ f.roots, ∀ α' ∈ f.roots, α ≠ α' → ∀ δ ∈ T'.integer L,
        ∀ δ' ∈ T'.integer L, δ ^ 2 = ι x - ι α → δ' ^ 2 = ι x - ι α' →
        ∃ u ∈ T'.unit L, (u : L) = δ - δ' := by
      intro α hα α' hα' hne δ hδ δ' hδ' h h'
      have hne' : α' - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      refine exists_mem_unit_of_mul_eq (sub_mem hδ hδ') (add_mem hδ hδ')
        (w := Units.map (ι : K →* L) (Units.mk0 _ hne'))
        (map_mem_unit_iff.mpr (hdiffT α' hα' α hα hne')) ?_
      rw [Units.coe_map, MonoidHom.coe_ofClass, Units.val_mk0, map_sub]
      linear_combination h - h'
    obtain ⟨u₁₂, hu₁₂, hu₁₂'⟩ := hunit α₁ h₁.1 α₂ h₂.1 h12 δ₁ hδ₁ δ₂ hδ₂ hδ₁2 hδ₂2
    obtain ⟨u₁₃, hu₁₃, hu₁₃'⟩ := hunit α₁ h₁.1 α₃ h₃.1 h13 δ₁ hδ₁ δ₃ hδ₃ hδ₁2 hδ₃2
    obtain ⟨u₂₃, hu₂₃, hu₂₃'⟩ := hunit α₂ h₂.1 α₃ h₃.1 h23 δ₂ hδ₂ δ₃ hδ₃ hδ₂2 hδ₃2
    have h0 : δ₁ - δ₃ ≠ 0 := by
      rw [← hu₁₃']
      exact u₁₃.ne_zero
    have hmem : ∀ {u : Lˣ}, u ∈ T'.unit L →
        u ∈ (hT'fin.toFinset : Set (HeightOneSpectrum (𝓞 L))).unit L := fun h ↦ by
      rwa [Set.Finite.coe_toFinset]
    refine ⟨(u₁₂ / u₁₃, u₂₃ / u₁₃), ⟨hmem (div_mem hu₁₂ hu₁₃), hmem (div_mem hu₂₃ hu₁₃), ?_⟩,
      ?_⟩
    · simp only [Units.val_one, one_mul, Units.val_div_eq_div_val, hu₁₂', hu₁₃', hu₂₃']
      rw [← add_div, div_eq_one_iff_eq h0]
      ring
    · refine (eq_of_sq_eq_sub two_ne_zero hι₁₂ hι₁₃ hι₂₃ hδ₁2 hδ₂2 hδ₃2 ?_).symm
      simp only [Units.val_div_eq_div_val, hu₁₂', hu₁₃']
      exact div_mul_cancel₀ _ h0
  have hXfin : {x : K | ∃ y, x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K ∧
      y ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K ∧ b * y ^ 2 = f.eval x}.Finite :=
    ((hUfin.image Φ).preimage ι.injective.injOn).subset fun x ⟨y, hx, hy, hxy⟩ ↦
      hX x y hx hy hxy
  refine (hXfin.biUnion fun x _ ↦ (Set.finite_singleton x).prod
    (finite_setOf_sq_eq (f.eval x / b))).subset ?_
  rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
  refine Set.mem_biUnion ⟨y, hx, hy, hxy⟩ ⟨Set.mem_singleton x, ?_⟩
  change y ^ 2 = f.eval x / b
  rw [← hxy, mul_div_cancel_left₀ _ hb]

variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [DecidableEq Ω]

/-- **Siegel's theorem on the hyperelliptic equation** (Siegel 1926; Bombieri–Gubler,
Theorem 5.3.5). If `f ∈ K[X]` has at least three distinct roots of odd multiplicity in an
algebraically closed field `Ω ⊇ K`, then for `b ≠ 0` the equation `b y ^ 2 = f (x)` has finitely
many solutions in `S`-integers. -/
theorem finite_setOf_mul_sq_eq_eval (S : Finset (HeightOneSpectrum (𝓞 K))) {f : K[X]}
    (h3 : 3 ≤ ((f.map (algebraMap K Ω)).roots.toFinset.filter
      fun r ↦ Odd ((f.map (algebraMap K Ω)).roots.count r)).card)
    {b : K} (hb : b ≠ 0) :
    {p : K × K | p.1 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K ∧
      p.2 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K ∧ b * p.2 ^ 2 = f.eval p.1}.Finite := by
  classical
  let L := f.SplittingField
  have : NumberField L := NumberField.of_module_finite K L
  let T := (finite_preimage_under L S.finite_toSet).toFinset
  have hT : (T : Set (HeightOneSpectrum (𝓞 L))) =
      HeightOneSpectrum.under (𝓞 K) ⁻¹' (S : Set (HeightOneSpectrum (𝓞 K))) :=
    Set.Finite.coe_toFinset _
  set ι := algebraMap K L
  have h3L : 3 ≤ ((f.map ι).roots.toFinset.filter fun r ↦ Odd ((f.map ι).roots.count r)).card := by
    let φ : L →ₐ[K] Ω := IsAlgClosed.lift
    have hroots : (f.map (algebraMap K Ω)).roots = (f.map ι).roots.map φ := by
      rw [show f.map (algebraMap K Ω) = (f.map ι).map (φ : L →+* Ω) by
        rw [Polynomial.map_map, φ.comp_algebraMap], (SplittingField.splits f).roots_map]
      rfl
    have hφ : Function.Injective φ := φ.toRingHom.injective
    rw [hroots, Multiset.toFinset_map, Finset.filter_image,
      Finset.card_image_of_injective _ hφ] at h3
    convert h3 using 3 with r
    simp [Multiset.count_map_eq_count' _ _ hφ]
  refine ((finite_setOf_mul_sq_eq_eval_of_splits T (SplittingField.splits f) h3L
    ((_root_.map_ne_zero ι).mpr hb)).preimage (f := fun p : K × K ↦ (ι p.1, ι p.2))
    fun p _ q _ h ↦ Prod.ext (ι.injective (congrArg Prod.fst h))
      (ι.injective (congrArg Prod.snd h))).subset ?_
  rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
  refine ⟨by rw [hT]; exact algebraMap_mem_integer_iff.mpr hx,
    by rw [hT]; exact algebraMap_mem_integer_iff.mpr hy, ?_⟩
  change ι b * ι y ^ 2 = (f.map ι).eval (ι x)
  rw [eval_map, eval₂_hom, ← map_pow, ← map_mul, hxy]

/-- **Siegel's theorem, the book's form.** For squarefree `f ∈ K[X]` of degree at least `3` and
`b ≠ 0`, the equation `b y ^ 2 = f (x)` has finitely many solutions in `S`-integers. -/
theorem finite_setOf_mul_sq_eq_eval_of_squarefree (S : Finset (HeightOneSpectrum (𝓞 K)))
    {f : K[X]} (hf : Squarefree f) (hdeg : 3 ≤ f.natDegree) {b : K} (hb : b ≠ 0) :
    {p : K × K | p.1 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K ∧
      p.2 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K ∧ b * p.2 ^ 2 = f.eval p.1}.Finite := by
  classical
  refine finite_setOf_mul_sq_eq_eval (Ω := AlgebraicClosure K) S ?_ hb
  set g := f.map (algebraMap K (AlgebraicClosure K))
  have hnd : g.roots.Nodup := nodup_roots (PerfectField.separable_iff_squarefree.mpr hf).map
  rw [Finset.filter_true_of_mem fun r hr ↦ by
      rw [Multiset.count_eq_one_of_mem hnd (Multiset.mem_toFinset.mp hr)]
      exact odd_one,
    Multiset.toFinset_card_of_nodup hnd, splits_iff_card_roots.mp (IsAlgClosed.splits g),
    natDegree_map]
  exact hdeg

end NumberField

/-! ### Acceptance criteria -/

section Tests

variable {K : Type*} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- **Mordell's `y ^ 2 = x ^ 3 - 2` has finitely many `S`-integral solutions, in every number
field and for every finite `S`.** -/
example : {p : K × K | p.1 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K ∧
    p.2 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K ∧ p.2 ^ 2 = p.1 ^ 3 - 2}.Finite := by
  convert NumberField.finite_setOf_mul_sq_eq_eval_of_squarefree S (f := X ^ 3 - C 2)
    (separable_X_pow_sub_C _ (by norm_num) (by norm_num)).squarefree
    (by rw [natDegree_X_pow_sub_C]) one_ne_zero using 4
  simp

open scoped Classical in
/-- `X ^ 3 (X ^ 2 - 2)` has three roots of odd multiplicity: `0` three times and `±√2` once. -/
private theorem three_le_card_odd_count :
    3 ≤ (((X ^ 3 * (X ^ 2 - C 2) : K[X]).map
      (algebraMap K (AlgebraicClosure K))).roots.toFinset.filter
        fun r ↦ Odd (((X ^ 3 * (X ^ 2 - C 2) : K[X]).map
          (algebraMap K (AlgebraicClosure K))).roots.count r)).card := by
  have : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  set R := (X ^ 2 - C 2 : (AlgebraicClosure K)[X]).roots with hR
  have hq : (X ^ 2 - C 2 : (AlgebraicClosure K)[X]) ≠ 0 := X_pow_sub_C_ne_zero two_pos 2
  have hnd : R.Nodup := nodup_roots (separable_X_pow_sub_C _ (by norm_num) (by norm_num))
  have hcard : R.card = 2 := by
    rw [hR, splits_iff_card_roots.mp (IsAlgClosed.splits _), natDegree_X_pow_sub_C]
  have h0 : (0 : AlgebraicClosure K) ∉ R := by simp [hR, mem_roots hq]
  have hroots : ((X ^ 3 * (X ^ 2 - C 2) : K[X]).map (algebraMap K (AlgebraicClosure K))).roots =
      3 • {0} + R := by
    rw [Polynomial.map_mul, Polynomial.map_pow, map_X, Polynomial.map_sub, Polynomial.map_pow,
      map_X, map_C, map_ofNat, roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hq), roots_X_pow]
  rw [hroots, Finset.filter_true_of_mem]
  · rw [Multiset.toFinset_add, Multiset.toFinset_nsmul _ _ (by norm_num),
      Multiset.toFinset_singleton, ← Finset.insert_eq,
      Finset.card_insert_of_notMem (by simpa using h0), Multiset.toFinset_card_of_nodup hnd,
      hcard]
  · intro r hr
    rw [Multiset.count_add, Multiset.count_nsmul, Multiset.count_singleton]
    by_cases hr0 : r = 0
    · subst hr0
      simp only [Multiset.count_eq_zero.mpr h0, add_zero]
      decide
    · have hrR : r ∈ R := by simpa [hr0] using hr
      simp [hr0, Multiset.count_eq_one_of_mem hnd hrR]

/-- **Beyond the book: `f` need not be squarefree.** `y ^ 2 = x ^ 3 (x ^ 2 - 2)` has finitely many
`S`-integral solutions in every number field, because `0` is a root of odd multiplicity. -/
example : {p : K × K | p.1 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K ∧
    p.2 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K ∧
    p.2 ^ 2 = p.1 ^ 3 * (p.1 ^ 2 - 2)}.Finite := by
  convert NumberField.finite_setOf_mul_sq_eq_eval (Ω := AlgebraicClosure K) S
    three_le_card_odd_count one_ne_zero using 4
  simp

/-- **Conformance**: `(3, 5)` is an integral solution of `y ^ 2 = x ^ 3 - 2`. -/
example : ((3 : ℚ), (5 : ℚ)) ∈ {p : ℚ × ℚ | p.1 ∈ (∅ : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ ∧
    p.2 ∈ (∅ : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ ∧ p.2 ^ 2 = p.1 ^ 3 - 2} :=
  ⟨by exact_mod_cast natCast_mem ((∅ : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ) 3,
    by exact_mod_cast natCast_mem ((∅ : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ) 5,
    by norm_num⟩

/-- **Rejection: odd multiplicity is load-bearing.** `x ^ 2 (x - 1)` has degree `3` but only one
root of odd multiplicity, and `y ^ 2 = x ^ 2 (x - 1)` has the infinitely many integral solutions
`(t ^ 2 + 1, t (t ^ 2 + 1))`. -/
example : {p : ℚ × ℚ | p.1 ∈ (∅ : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ ∧
    p.2 ∈ (∅ : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ ∧
    1 * p.2 ^ 2 = (X ^ 2 * (X - 1) : ℚ[X]).eval p.1}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun t : ℕ ↦ (((t ^ 2 + 1 : ℕ) : ℚ), ((t * (t ^ 2 + 1) : ℕ) : ℚ)))
    (fun t u h ↦ ?_) fun t ↦ ?_
  · have h1 : ((t ^ 2 + 1 : ℕ) : ℚ) = ((u ^ 2 + 1 : ℕ) : ℚ) := congrArg Prod.fst h
    have h2 : t ^ 2 = u ^ 2 := by
      have := Nat.cast_injective h1
      omega
    exact Nat.pow_left_injective two_ne_zero h2
  · refine ⟨natCast_mem _ _, natCast_mem _ _, ?_⟩
    simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one]
    push_cast
    ring

/-- **Rejection: three roots cannot be lowered to two.** `2 x ^ 2 + 1` has two simple roots, and
`y ^ 2 = 2 x ^ 2 + 1` has the infinitely many integral solutions of Pell's equation, generated
from `(0, 1)` by `(x, y) ↦ (3 x + 2 y, 4 x + 3 y)`. -/
example : {p : ℚ × ℚ | p.1 ∈ (∅ : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ ∧
    p.2 ∈ (∅ : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ ∧
    1 * p.2 ^ 2 = (C 2 * X ^ 2 + 1 : ℚ[X]).eval p.1}.Infinite := by
  let s : ℕ → ℕ × ℕ := fun n ↦ Nat.rec (0, 1) (fun _ p ↦ (3 * p.1 + 2 * p.2, 4 * p.1 + 3 * p.2)) n
  have hs : ∀ n, ((s n).2 : ℤ) ^ 2 = 2 * (s n).1 ^ 2 + 1 ∧ 1 ≤ (s n).2 := by
    intro n
    induction n with
    | zero => simp [s]
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      change ((4 * (s n).1 + 3 * (s n).2 : ℕ) : ℤ) ^ 2 =
        2 * ((3 * (s n).1 + 2 * (s n).2 : ℕ) : ℤ) ^ 2 + 1 ∧ 1 ≤ 4 * (s n).1 + 3 * (s n).2
      push_cast
      exact ⟨by linear_combination h1, by omega⟩
  have hmono : StrictMono fun n ↦ (s n).1 := by
    refine strictMono_nat_of_lt_succ fun n ↦ ?_
    change (s n).1 < 3 * (s n).1 + 2 * (s n).2
    have := (hs n).2
    omega
  refine Set.infinite_of_injective_forall_mem (f := fun n ↦ (((s n).1 : ℚ), ((s n).2 : ℚ)))
    (fun i j hij ↦ hmono.injective
      (Nat.cast_injective (congrArg Prod.fst hij : ((s i).1 : ℚ) = (s j).1))) fun n ↦ ?_
  refine ⟨natCast_mem _ _, natCast_mem _ _, ?_⟩
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_one, one_mul]
  exact_mod_cast (hs n).1

end Tests
