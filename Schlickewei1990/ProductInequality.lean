/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.BalancedPoint
public import DiophantineApproximation.SumForms

/-!
# The product inequality of a class of solutions

Schlickewei's §3 changes variables `yᵢ = αᵢ xᵢ` (3.1), so that (1.6) becomes
`y₁ + ⋯ + y_{n+1} = 0` (3.2) with `∏_{v ∈ S} ‖yᵢ‖_v = ∏_{v ∈ S} ‖αᵢ‖_v` (3.3). He sorts the
solutions into classes by the index `i(v)` of the largest coordinate at each place of `S` (3.12),
and on a class he takes the forms (3.7): at `v`, the coordinates `y₁, …, yₙ` with `y_{i(v)}`
replaced by `y_{n+1} = −(y₁ + ⋯ + yₙ)`. These are the sum forms `NumberField.sumForms r` of
`DiophantineApproximation/SumForms.lean` with `r v = i(v)` (`none` for `i(v) = n + 1`). On the
class

```text
∏_{v ∈ S∞ ∪ S} ∏_{i ≠ i(v)} ‖yᵢ‖_v · H(y') ≤ ∏_{i ≤ n+1} ∏_{v ∈ S∞ ∪ S} ‖αᵢ‖_v,
```

`y' = (y₁, …, yₙ)` and `H` the projective height in Mathlib's normalization. This is (3.20) in
the unnormalized form that the Subspace Theorems of Layers 6.4 and Q4.3 take (`affineProd`): there
the forms are not divided by `‖L‖_v ‖y'‖_v`, so the exponent is `−1` and not `−n − 1`, and the
factors `n^{3n+1}` of (3.19), which compare `‖y'‖_v` with `‖y_{i(v)}‖_v`, do not arise. The proof
is (3.11)–(3.15): on the hyperplane, the product of the forms times `∏ ‖y_{i(v)}‖_v` is the
product of all the coordinates (`NumberField.affineProd_sumForms_mul_eq_prod_option`, exact for
any `r`); by (3.3) that is the right-hand side; and since `i(v)` is the largest coordinate,
`∏ ‖y_{i(v)}‖_v` is the `S`-product of the sup norms, which bounds the height of the `S`-integral
point `y` and so that of `y'`.

⚠ **The coefficients are `S`-integers.** Then so is every `yᵢ`, and the height of `y` is at most
its product over `S∞ ∪ S`; Schlickewei's factor `∏_{v ∉ S} max_i ‖αᵢ‖_v` in (3.6) is `≤ 1` and
is dropped. Clearing denominators of `α` does not change the projective solutions.

## Main results

* `NumberField.exists_unitClass`: every point has a class, `none` outside `S∞ ∪ S`.
* `NumberField.affineProd_sumForms_mul_mulHeight_le`: **the product inequality** (3.20) for the
  point `y` of `ℙⁿ`.
* `NumberField.affineProd_sumForms_mul_mulHeight_some_le`: the same with the height of `y'`.
* `NumberField.exists_smul_balanced_unitClass`: **the balanced representative** of a solution,
  normalized for Q4.3 at the cost `κ ^ (n + 2)`, `κ = scalarConst K S`.

## References

H. P. Schlickewei, *`S`-unit equations over number fields*, Invent. Math. **102** (1990), 95–107,
§3, (3.1)–(3.20).

This is milestone S90.2 of `Schlickewei1990/README.md`.
-/

@[expose] public section

open IsDedekindDomain Height

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- **Every point has a class** (3.12): a choice of a largest coordinate at each place of
`S∞ ∪ S`, and `none` at the other places, so that there are finitely many classes. -/
theorem exists_unitClass [Finite ι] (S : Finset (HeightOneSpectrum (𝓞 K))) (y : Option ι → K) :
    ∃ r : AbsoluteValue K ℝ → Option ι,
      (∀ v ∈ relevantPlaces S, v (y (r v)) = ⨆ o, v (y o)) ∧
        ∀ v ∉ relevantPlaces S, r v = none := by
  classical
  have hmax : ∀ v : AbsoluteValue K ℝ, ∃ o, v (y o) = ⨆ o', v (y o') := fun v ↦ by
    obtain ⟨o, ho⟩ := Finite.exists_max fun o ↦ v (y o)
    exact ⟨o, le_antisymm (le_ciSup (f := fun o ↦ v (y o)) (Finite.bddAbove_range _) o)
      (ciSup_le ho)⟩
  refine ⟨fun v ↦ if v ∈ relevantPlaces S then (hmax v).choose else none, fun v hv ↦ ?_,
    fun v hv ↦ by simp [hv]⟩
  simp only [hv, ↓reduceIte]
  exact (hmax v).choose_spec

/-- **The product identity of a class** ((3.14)–(3.15)). For `S`-units `x` with
`∑ αᵢ xᵢ = 0` and `r` naming a largest coordinate of `y = α x` at every place of `S∞ ∪ S`, the
product of the forms (3.7) at `y'` times the `S`-product of the sup norms of `y` is
`∏ᵢ ∏_{v ∈ S∞ ∪ S} ‖αᵢ‖_v`. -/
theorem affineProd_sumForms_mul_placeProd_iSup_eq (S : Finset (HeightOneSpectrum (𝓞 K)))
    (r : AbsoluteValue K ℝ → Option ι) {α : Option ι → K} {x : Option ι → Kˣ}
    (hx : ∀ o, x o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (hsum : ∑ o, α o * x o = 0)
    (hr : ∀ v ∈ relevantPlaces S, v (α (r v) * x (r v)) = ⨆ o, v (α o * x o)) :
    affineProd S (fun v ↦ v) (sumForms r) (fun i ↦ α (some i) * x (some i)) *
        placeProd S Set.univ (fun v ↦ ⨆ o, v (α o * x o)) =
      ∏ o, placeProd S Set.univ (fun v ↦ v (α o)) := by
  have hid := affineProd_sumForms_mul_eq_prod_option S r (y := fun o ↦ α o * x o) hsum
  have hmax : placeProd S Set.univ (fun v ↦ v (α (r v) * x (r v))) =
      placeProd S Set.univ (fun v ↦ ⨆ o, v (α o * x o)) := by
    rw [← placeProd_inter_relevantPlaces, placeProd_congr S _ fun v hv ↦ hr v hv.2,
      placeProd_inter_relevantPlaces]
  rwa [hmax, Finset.prod_congr rfl fun o _ ↦ placeProd_univ_mul_unit S (α o) (hx o)] at hid

/-- **The product inequality of a class** (Schlickewei's (3.20), unnormalized). For `S`-integral
nonzero coefficients `α`, `S`-units `x` with `∑ αᵢ xᵢ = 0`, and `r` naming a largest coordinate of
`y = α x` at every place of `S∞ ∪ S`, the product of the forms (3.7) at `y'` times the height of
`y` is at most `∏ᵢ ∏_{v ∈ S∞ ∪ S} ‖αᵢ‖_v`. -/
theorem affineProd_sumForms_mul_mulHeight_le (S : Finset (HeightOneSpectrum (𝓞 K)))
    (r : AbsoluteValue K ℝ → Option ι) {α : Option ι → K}
    (hα : ∀ o, α o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) (hα0 : ∀ o, α o ≠ 0)
    {x : Option ι → Kˣ} (hx : ∀ o, x o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (hsum : ∑ o, α o * x o = 0)
    (hr : ∀ v ∈ relevantPlaces S, v (α (r v) * x (r v)) = ⨆ o, v (α o * x o)) :
    affineProd S (fun v ↦ v) (sumForms r) (fun i ↦ α (some i) * x (some i)) *
        mulHeight (fun o ↦ α o * x o) ≤ ∏ o, placeProd S Set.univ (fun v ↦ v (α o)) := by
  have hy0 : (fun o ↦ α o * (x o : K)) ≠ 0 := fun h ↦
    mul_ne_zero (hα0 none) (x none).ne_zero (congrFun h none)
  have hyS : ∀ o, α o * (x o : K) ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K :=
    fun o ↦ mul_mem (hα o) (Set.mem_integer_of_mem_unit (hx o))
  rw [← affineProd_sumForms_mul_placeProd_iSup_eq S r hx hsum hr]
  exact mul_le_mul_of_nonneg_left (mulHeight_le_placeProd_univ S hy0 hyS)
    (affineProd_nonneg _ _ _ _)

/-- **The product inequality with the height of `y'`** (3.20): dropping `y_{n+1}` does not
increase the height. -/
theorem affineProd_sumForms_mul_mulHeight_some_le (S : Finset (HeightOneSpectrum (𝓞 K)))
    (r : AbsoluteValue K ℝ → Option ι) {α : Option ι → K}
    (hα : ∀ o, α o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) (hα0 : ∀ o, α o ≠ 0)
    {x : Option ι → Kˣ} (hx : ∀ o, x o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (hsum : ∑ o, α o * x o = 0)
    (hr : ∀ v ∈ relevantPlaces S, v (α (r v) * x (r v)) = ⨆ o, v (α o * x o)) :
    affineProd S (fun v ↦ v) (sumForms r) (fun i ↦ α (some i) * x (some i)) *
        mulHeight (fun i ↦ α (some i) * x (some i)) ≤
      ∏ o, placeProd S Set.univ (fun v ↦ v (α o)) :=
  (mul_le_mul_of_nonneg_left (mulHeight_comp_le some fun o ↦ α o * (x o : K))
    (affineProd_nonneg _ _ _ _)).trans
    (affineProd_sumForms_mul_mulHeight_le S r hα hα0 hx hsum hr)

open scoped Classical in
/-- **The balanced representative of a solution in a class** (the input of S90.3). For
`P₀ ∈ S` and the data of `NumberField.affineProd_sumForms_mul_mulHeight_le`, some nonzero
`β` makes `z = β y'` an `S`-integral point at which every form (3.7) is at most
`balancedConst p · H_aff(z) ^ s(p)` at every place `p` of `S∞ ∪ S`, the constants multiplying to
`1` (Evertse's normalization (2.4) for the largest exponents), and

```text
∏_{v ∈ S∞ ∪ S} ∏_{i ≠ i(v)} ‖L_i(z)‖_v · H_aff(z) ≤ κ ^ (n + 2) ∏ᵢ ∏_{v ∈ S∞ ∪ S} ‖αᵢ‖_v,
```

`κ = scalarConst K S`: the product inequality (3.20) against the **affine** height of a
representative, as Q4.3 takes it. Also `H_aff(z) ≤ κ² ∏_{v ∈ S∞ ∪ S} ‖z‖_v`. The cost of the
representative is `κ ^ (n + 2)`, explicit in `[K : ℚ]`, `|D_K|` and the norms of `S`. -/
theorem exists_smul_balanced_unitClass [Nonempty ι] (S : Finset (HeightOneSpectrum (𝓞 K)))
    {P₀ : HeightOneSpectrum (𝓞 K)} (hP₀ : P₀ ∈ S) (r : AbsoluteValue K ℝ → Option ι)
    {α : Option ι → K} (hα : ∀ o, α o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K)
    (hα0 : ∀ o, α o ≠ 0) {x : Option ι → Kˣ}
    (hx : ∀ o, x o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (hsum : ∑ o, α o * x o = 0)
    (hr : ∀ v ∈ relevantPlaces S, v (α (r v) * x (r v)) = ⨆ o, v (α o * x o)) :
    ∃ β : K, β ≠ 0 ∧
      (∀ i, (β • fun i ↦ α (some i) * (x (some i) : K)) i ∈
        (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
      (∀ p i, systemValue S (fun v ↦ v) (sumForms r) p i
          (β • fun i ↦ α (some i) * (x (some i) : K)) ≤
        balancedConst S P₀ p *
          mulHeightAff (β • fun i ↦ α (some i) * (x (some i) : K)) ^ systemExponent S p) ∧
      affineProd S (fun v ↦ v) (sumForms r) (β • fun i ↦ α (some i) * (x (some i) : K)) *
          mulHeightAff (β • fun i ↦ α (some i) * (x (some i) : K)) ≤
        scalarConst K S ^ (Fintype.card ι + 2) * ∏ o, placeProd S Set.univ (fun v ↦ v (α o)) ∧
      mulHeightAff (β • fun i ↦ α (some i) * (x (some i) : K)) ≤ scalarConst K S ^ 2 *
        placeProd S Set.univ (fun v ↦ ⨆ i, v ((β • fun i ↦ α (some i) * (x (some i) : K)) i)) := by
  set y' : ι → K := fun i ↦ α (some i) * (x (some i) : K) with hy'
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hy'0 : y' ≠ 0 := fun h ↦
    mul_ne_zero (hα0 (some i₀)) (x (some i₀)).ne_zero (congrFun h i₀)
  have hy'S : ∀ i, y' i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K :=
    fun i ↦ mul_mem (hα _) (Set.mem_integer_of_mem_unit (hx _))
  have hL : ∀ v ∈ relevantPlaces S, ∀ i, v (sumForms r v i y') ≤ ⨆ j, v (y' j) :=
    fun v hv i ↦ apply_sumForms_le_iSup r v (y := fun o ↦ α o * x o) hsum (hr v hv) i
  obtain ⟨β, hβ0, hzS, hsys, hprod, hH⟩ :=
    exists_smul_systemValue_le S hP₀ hy'0 hy'S (sumForms r) hL
  refine ⟨β, hβ0, hzS, hsys, hprod.trans ?_, hH⟩
  have hκ := scalarConst_pos S
  gcongr
  rw [← affineProd_sumForms_mul_placeProd_iSup_eq S r hx hsum hr]
  refine mul_le_mul_of_nonneg_left ?_ (affineProd_nonneg _ _ _ _)
  refine placeProd_le_placeProd S _ (fun v _ ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _) fun v _ ↦ ?_
  exact Real.iSup_le (fun i ↦ le_ciSup_of_le (Finite.bddAbove_range _) (some i) le_rfl)
    (Real.iSup_nonneg fun _ ↦ v.nonneg _)

end NumberField
