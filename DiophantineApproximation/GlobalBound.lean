/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.FundamentalInequality
public import DiophantineApproximation.SAdicHeight

/-!
# From local upper bounds at every place to a global inequality

Step IV of Roth's proof is one line of mathematics — "since `Q(β) ≠ 0` is in `K`, the lower bound
is given by the product formula" — and this file is that line, in the shape the rest of the proof
hands it. Let `y ≠ 0` in `K`, let `x` be a nonzero tuple, let `β` be a family with exponents `e`,
and suppose that at **every** place of `K`

```text
|y|_v  ≤  C · (⨆ i, |x i|_v) · ∏ i, max (|β i|_v) 1 ^ e i · (a factor that is `1` off `S`).
```

Then the product formula turns the product of the right-hand sides into
`C ^ [K : ℚ] · H(x) · ∏ i, H(β i) ^ e i` times the `S`-factors, and it is at least `1`.

The constant is charged only at the archimedean places, as `C ^ totalWeight K`; at the
nonarchimedean ones the bound must be constant-free, which is what the ultrametric inequality
supplies and what makes the whole estimate finite.

## Main definitions

* `NumberField.sPlaceAbsValue` and `NumberField.sPlaceWeight`: the absolute value and the weight
  attached to a place of `S`, where `S` is the **disjoint union of the two typed finsets**
  `↥Sinf ⊕ ↥Sfin`. This is the index type of Mahler's reduction over a number field; it is never
  a `Finset (AbsoluteValue K ℝ)`.

## Main results

* `NumberField.one_le_of_forall_apply_le`: the transport, with the `S`-factors carried by two
  functions supported on the two finsets.
* `NumberField.one_le_of_forall_apply_le_sum`: the same with the places of `S` collected into one
  index type, which is the form Layer 3.2 consumes.
* `NumberField.FinitePlace.hasFiniteMulSupport_max_one'`: the truncation `max (v x) 1` has finite
  multiplicative support with no hypothesis on `x`.

## Implementation notes

⚠ **The fundamental inequality of Layer 0.4 is not what Step IV needs.** Its lower bound
`(mulHeight₁ y)⁻¹ ≤ ∏_{v ∈ S} min 1 (|y|_v) ^ w_v` cuts the product down to `S`, and the local
bound on `|Q(β)|_v` contains the local factor of the coefficients of `Q`, whose product over `S`
alone is **not** bounded by the height of `Q` — the complementary product can be smaller than `1`.
Using it would charge the height of `Q` and the heights of the `β j` twice and would prove Roth's
theorem only for `κ > 4`. The product over *all* places is what makes the constant `2` come out,
and that is why this file exists beside `DiophantineApproximation/FundamentalInequality.lean`.

⚠ **The uniform hypothesis at the places of `S` carries the constant `C` as well.** A finite place
of `S` is charged `C` once in the conclusion (`(C * g a) ^ sPlaceWeight a`) although the
nonarchimedean bound needs none: the places of `S` are finitely many, so the waste is a bounded
factor, and one hypothesis in place of two is worth it to the caller.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.4.4 and §6.4.9.

This is part of Layer 3.2 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Truncating from below keeps the finite multiplicative support**, with no hypothesis: at
`x = 0` every factor is `1`. -/
theorem FinitePlace.hasFiniteMulSupport_max_one' (x : K) :
    Function.HasFiniteMulSupport fun v : FinitePlace K ↦ max (v x) 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [map_zero, max_eq_right zero_le_one]
    exact Function.hasFiniteMulSupport_one
  · exact FinitePlace.hasFiniteMulSupport_max_one hx

/-- **The product formula against local upper bounds.** -/
theorem one_le_of_forall_apply_le
    {y : K} (hy : y ≠ 0) {γ : Type*} [Finite γ] {x : γ → K} (hx : x ≠ 0)
    {ι : Type*} [Fintype ι] (β : ι → K) (e : ι → ℕ)
    {C : ℝ} (hC : 1 ≤ C)
    {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    {s : InfinitePlace K → ℝ} {t : FinitePlace K → ℝ}
    (hs0 : ∀ v, 0 ≤ s v)
    (hs1 : ∀ v ∉ Sinf, s v = 1) (ht1 : ∀ v ∉ Sfin, t v = 1)
    (hinf : ∀ v : InfinitePlace K,
      v y ≤ C * (⨆ i, v (x i)) * (∏ i, max (v (β i)) 1 ^ e i) * s v)
    (hfin : ∀ v : FinitePlace K,
      v y ≤ (⨆ i, v (x i)) * (∏ i, max (v (β i)) 1 ^ e i) * t v) :
    1 ≤ C ^ totalWeight K * mulHeight x * (∏ i, mulHeight₁ (β i) ^ e i)
      * ((∏ v ∈ Sinf, s v ^ v.mult) * ∏ v ∈ Sfin, t v) := by
  have hsup : ∀ v : AbsoluteValue K ℝ, 0 ≤ ⨆ i, v (x i) :=
    fun v ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _
  have hmax : ∀ (v : AbsoluteValue K ℝ) (i : ι), (0 : ℝ) ≤ max (v (β i)) 1 :=
    fun v i ↦ le_trans zero_le_one (le_max_right _ _)
  have hprodmax : ∀ v : AbsoluteValue K ℝ, (0 : ℝ) ≤ ∏ i, max (v (β i)) 1 ^ e i :=
    fun v ↦ Finset.prod_nonneg fun i _ ↦ pow_nonneg (hmax v i) _
  -- the infinite places
  have hInf : (∏ v : InfinitePlace K, v y ^ v.mult)
      ≤ C ^ totalWeight K * (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
        * (∏ i, (∏ v : InfinitePlace K, max (v (β i)) 1 ^ v.mult) ^ e i)
        * ∏ v ∈ Sinf, s v ^ v.mult := by
    calc (∏ v : InfinitePlace K, v y ^ v.mult)
        ≤ ∏ v : InfinitePlace K,
            (C * (⨆ i, v (x i)) * (∏ i, max (v (β i)) 1 ^ e i) * s v) ^ v.mult :=
          Finset.prod_le_prod₀ (fun v _ ↦ pow_nonneg (v.1.nonneg _) _)
            fun v _ ↦ pow_le_pow_left₀ (v.1.nonneg _) (hinf v) _
      _ = (∏ _v : InfinitePlace K, C ^ _v.mult)
            * (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
            * (∏ v : InfinitePlace K, (∏ i, max (v (β i)) 1 ^ e i) ^ v.mult)
            * ∏ v : InfinitePlace K, s v ^ v.mult := by
          simp only [mul_pow]
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      _ = C ^ totalWeight K * (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
            * (∏ i, (∏ v : InfinitePlace K, max (v (β i)) 1 ^ v.mult) ^ e i)
            * ∏ v ∈ Sinf, s v ^ v.mult := by
          congr 1
          · congr 1
            · congr 1
              · rw [Finset.prod_pow_eq_pow_sum, ← totalWeight_eq_sum_mult]
            · calc ∏ v : InfinitePlace K, (∏ i, max (v (β i)) 1 ^ e i) ^ v.mult
                  = ∏ v : InfinitePlace K, ∏ i, (max (v (β i)) 1 ^ v.mult) ^ e i := by
                    refine Finset.prod_congr rfl fun v _ ↦ ?_
                    rw [← Finset.prod_pow]
                    exact Finset.prod_congr rfl fun i _ ↦ by
                      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
                _ = ∏ i, ∏ v : InfinitePlace K, (max (v (β i)) 1 ^ v.mult) ^ e i :=
                    Finset.prod_comm
                _ = ∏ i, (∏ v : InfinitePlace K, max (v (β i)) 1 ^ v.mult) ^ e i :=
                    Finset.prod_congr rfl fun i _ ↦ Finset.prod_pow _ _ _
          · exact (Finset.prod_subset (Finset.subset_univ Sinf)
              fun v _ hv ↦ by rw [hs1 v hv, one_pow]).symm
  -- the finite places
  have hfsup : Function.HasFiniteMulSupport fun v : FinitePlace K ↦ ⨆ i, v (x i) :=
    FinitePlace.hasFiniteMulSupport_iSup hx
  have hfmax : ∀ i, Function.HasFiniteMulSupport fun v : FinitePlace K ↦ max (v (β i)) 1 ^ e i :=
    fun i ↦ Set.Finite.subset (FinitePlace.hasFiniteMulSupport_max_one' (β i)) fun v hv ↦ by
      simp only [Function.mem_mulSupport] at hv ⊢
      exact fun h ↦ hv (by rw [h, one_pow])
  have hfprod : Function.HasFiniteMulSupport
      fun v : FinitePlace K ↦ ∏ i, max (v (β i)) 1 ^ e i :=
    Set.Finite.subset ((Finset.univ : Finset ι).finite_toSet.biUnion fun i _ ↦ hfmax i)
      (Finset.mulSupport_prod Finset.univ _)
  have hmulsupp : ∀ {f g : FinitePlace K → ℝ}, Function.HasFiniteMulSupport f →
      Function.HasFiniteMulSupport g → Function.HasFiniteMulSupport fun v ↦ f v * g v :=
    fun {f g} hf hg ↦ Set.Finite.subset (Set.Finite.union hf hg) (Function.mulSupport_mul f g)
  have hft : Function.HasFiniteMulSupport t :=
    Set.Finite.subset Sfin.finite_toSet fun v hv ↦ by
      by_contra hmem
      exact hv (ht1 v hmem)
  have hFin : (∏ᶠ v : FinitePlace K, v y)
      ≤ (∏ᶠ v : FinitePlace K, ⨆ i, v (x i))
        * (∏ i, (∏ᶠ v : FinitePlace K, max (v (β i)) 1) ^ e i)
        * ∏ v ∈ Sfin, t v := by
    calc (∏ᶠ v : FinitePlace K, v y)
        ≤ ∏ᶠ v : FinitePlace K, (⨆ i, v (x i)) * (∏ i, max (v (β i)) 1 ^ e i) * t v :=
          finprod_le_finprod₀ (FinitePlace.hasFiniteMulSupport hy) (fun v ↦ v.1.nonneg _)
            (hmulsupp (hmulsupp hfsup hfprod) hft) hfin
      _ = (∏ᶠ v : FinitePlace K, ⨆ i, v (x i))
            * (∏ᶠ v : FinitePlace K, ∏ i, max (v (β i)) 1 ^ e i)
            * ∏ᶠ v : FinitePlace K, t v := by
          rw [finprod_mul_distrib (hmulsupp hfsup hfprod) hft,
            finprod_mul_distrib hfsup hfprod]
      _ = (∏ᶠ v : FinitePlace K, ⨆ i, v (x i))
            * (∏ i, (∏ᶠ v : FinitePlace K, max (v (β i)) 1) ^ e i)
            * ∏ v ∈ Sfin, t v := by
          congr 1
          · congr 1
            rw [finprod_prod_comm _ _ fun i _ ↦ hfmax i]
            exact Finset.prod_congr rfl fun i _ ↦
              (finprod_pow (FinitePlace.hasFiniteMulSupport_max_one' (β i)) (e i)).symm
          · exact finprod_eq_prod_of_mulSupport_subset t fun v hv ↦ by
              by_contra hmem
              exact hv (ht1 v hmem)
  -- putting the two halves together
  have hInf0 : (0 : ℝ) ≤ C ^ totalWeight K * (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
      * (∏ i, (∏ v : InfinitePlace K, max (v (β i)) 1 ^ v.mult) ^ e i)
      * ∏ v ∈ Sinf, s v ^ v.mult := by
    have h1 : (0 : ℝ) ≤ C ^ totalWeight K := pow_nonneg (le_trans zero_le_one hC) _
    have h2 : (0 : ℝ) ≤ ∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult :=
      Finset.prod_nonneg fun v _ ↦ pow_nonneg (hsup v.1) _
    have h3 : (0 : ℝ) ≤ ∏ i, (∏ v : InfinitePlace K, max (v (β i)) 1 ^ v.mult) ^ e i :=
      Finset.prod_nonneg fun i _ ↦ pow_nonneg
        (Finset.prod_nonneg fun v _ ↦ pow_nonneg (hmax v.1 i) _) _
    have h4 : (0 : ℝ) ≤ ∏ v ∈ Sinf, s v ^ v.mult :=
      Finset.prod_nonneg fun v _ ↦ pow_nonneg (hs0 v) _
    positivity
  calc (1 : ℝ) = (∏ v : InfinitePlace K, v y ^ v.mult) * ∏ᶠ v : FinitePlace K, v y :=
        (prod_abs_eq_one hy).symm
    _ ≤ (C ^ totalWeight K * (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
          * (∏ i, (∏ v : InfinitePlace K, max (v (β i)) 1 ^ v.mult) ^ e i)
          * ∏ v ∈ Sinf, s v ^ v.mult)
        * ((∏ᶠ v : FinitePlace K, ⨆ i, v (x i))
          * (∏ i, (∏ᶠ v : FinitePlace K, max (v (β i)) 1) ^ e i)
          * ∏ v ∈ Sfin, t v) :=
        mul_le_mul hInf hFin (finprod_nonneg fun v ↦ v.1.nonneg _) hInf0
    _ = C ^ totalWeight K * mulHeight x * (∏ i, mulHeight₁ (β i) ^ e i)
          * ((∏ v ∈ Sinf, s v ^ v.mult) * ∏ v ∈ Sfin, t v) := by
        have hxsplit : (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
            * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) = mulHeight x := (mulHeight_eq hx).symm
        have hβsplit : (∏ i, (∏ v : InfinitePlace K, max (v (β i)) 1 ^ v.mult) ^ e i)
            * ∏ i, (∏ᶠ v : FinitePlace K, max (v (β i)) 1) ^ e i
              = ∏ i, mulHeight₁ (β i) ^ e i := by
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun i _ ↦ by rw [mulHeight₁_eq, mul_pow]
        rw [← hxsplit, ← hβsplit]
        ring


/-- **The places of `S`, as one finite index type.** Over a number field the index set of
Mahler's reduction is the disjoint union of the two typed finsets, never a set of absolute
values; this is the absolute value attached to such an index. -/
def sPlaceAbsValue {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    (a : ↥Sinf ⊕ ↥Sfin) : AbsoluteValue K ℝ :=
  a.elim (fun v : ↥Sinf ↦ (v : InfinitePlace K).1) fun v : ↥Sfin ↦ (v : FinitePlace K).1

@[simp]
theorem sPlaceAbsValue_inl {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    (v : ↥Sinf) :
    (sPlaceAbsValue (Sfin := Sfin) (Sum.inl v)) = (v : InfinitePlace K).1 := rfl

@[simp]
theorem sPlaceAbsValue_inr {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    (v : ↥Sfin) :
    (sPlaceAbsValue (Sinf := Sinf) (Sum.inr v)) = (v : FinitePlace K).1 := rfl

/-- **The weight of a place of `S`** in Mathlib's relative normalisation: `mult` at an infinite
place and `1` at a finite one. -/
noncomputable def sPlaceWeight {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    (a : ↥Sinf ⊕ ↥Sfin) : ℕ :=
  a.elim (fun v : ↥Sinf ↦ (v : InfinitePlace K).mult) fun _ : ↥Sfin ↦ 1

@[simp]
theorem sPlaceWeight_inl {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    (v : ↥Sinf) :
    (sPlaceWeight (Sfin := Sfin) (Sum.inl v)) = (v : InfinitePlace K).mult := rfl

@[simp]
theorem sPlaceWeight_inr {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    (v : ↥Sfin) : (sPlaceWeight (Sinf := Sinf) (Sum.inr v)) = 1 := rfl

/-- The weight of a place of `S` is positive. -/
theorem one_le_sPlaceWeight {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    (a : ↥Sinf ⊕ ↥Sfin) : 1 ≤ sPlaceWeight a := by
  cases a with
  | inl v => exact Nat.one_le_iff_ne_zero.mpr (v : InfinitePlace K).mult_ne_zero
  | inr v => exact le_rfl

/-- **The product-formula bound with the places of `S` collected into one index type.** -/
theorem one_le_of_forall_apply_le_sum
    {y : K} (hy : y ≠ 0) {γ : Type*} [Finite γ] {x : γ → K} (hx : x ≠ 0)
    {ι : Type*} [Fintype ι] (β : ι → K) (e : ι → ℕ) {C : ℝ} (hC : 1 ≤ C)
    {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    {g : (↥Sinf ⊕ ↥Sfin) → ℝ} (hg0 : ∀ a, 0 ≤ g a)
    (hinf : ∀ v : InfinitePlace K, v y ≤ C * (⨆ i, v (x i)) * ∏ i, max (v (β i)) 1 ^ e i)
    (hfin : ∀ v : FinitePlace K, v y ≤ (⨆ i, v (x i)) * ∏ i, max (v (β i)) 1 ^ e i)
    (hS : ∀ a : ↥Sinf ⊕ ↥Sfin, sPlaceAbsValue a y ≤ C * (⨆ i, sPlaceAbsValue a (x i))
      * (∏ i, max (sPlaceAbsValue a (β i)) 1 ^ e i) * g a) :
    1 ≤ C ^ totalWeight K * mulHeight x * (∏ i, mulHeight₁ (β i) ^ e i)
      * ∏ a, (C * g a) ^ sPlaceWeight a := by
  classical
  have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC
  set s : InfinitePlace K → ℝ :=
    fun v ↦ if h : v ∈ Sinf then C * g (Sum.inl ⟨v, h⟩) else 1 with hsdef
  set t : FinitePlace K → ℝ :=
    fun v ↦ if h : v ∈ Sfin then C * g (Sum.inr ⟨v, h⟩) else 1 with htdef
  have hs0 : ∀ v, 0 ≤ s v := fun v ↦ by
    simp only [hsdef]
    by_cases h : v ∈ Sinf <;> simp [h, mul_nonneg hC0 (hg0 _)]
  have hs1 : ∀ v ∉ Sinf, s v = 1 := fun v hv ↦ by simp [hsdef, hv]
  have ht1 : ∀ v ∉ Sfin, t v = 1 := fun v hv ↦ by simp [htdef, hv]
  have key := one_le_of_forall_apply_le hy hx β e hC hs0 hs1 ht1
    (fun v ↦ by
      by_cases h : v ∈ Sinf
      · have hsv : s v = C * g (Sum.inl ⟨v, h⟩) := by simp [hsdef, h]
        have hb := hS (Sum.inl ⟨v, h⟩)
        simp only [sPlaceAbsValue_inl] at hb
        have hnn : (0 : ℝ) ≤ (⨆ i, v (x i)) * ∏ i, max (v (β i)) 1 ^ e i :=
          mul_nonneg (Real.iSup_nonneg fun _ ↦ v.1.nonneg _)
            (Finset.prod_nonneg fun i _ ↦ pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _)
        rw [hsv]
        calc v y ≤ C * (⨆ i, v (x i)) * (∏ i, max (v (β i)) 1 ^ e i) * g (Sum.inl ⟨v, h⟩) := hb
          _ ≤ C * (⨆ i, v (x i)) * (∏ i, max (v (β i)) 1 ^ e i) * (C * g (Sum.inl ⟨v, h⟩)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by rw [mul_assoc]; exact mul_nonneg hC0 hnn)
              nlinarith [hg0 (Sum.inl ⟨v, h⟩)]
      · rw [hs1 v h, mul_one]
        exact hinf v)
    (fun v ↦ by
      by_cases h : v ∈ Sfin
      · have htv : t v = C * g (Sum.inr ⟨v, h⟩) := by simp [htdef, h]
        rw [htv]
        have hb := hS (Sum.inr ⟨v, h⟩)
        simp only [sPlaceAbsValue_inr] at hb
        calc v y ≤ C * (⨆ i, v (x i)) * (∏ i, max (v (β i)) 1 ^ e i) * g (Sum.inr ⟨v, h⟩) := hb
          _ = (⨆ i, v (x i)) * (∏ i, max (v (β i)) 1 ^ e i) * (C * g (Sum.inr ⟨v, h⟩)) := by ring
      · rw [ht1 v h, mul_one]
        exact hfin v)
  refine le_trans key (le_of_eq ?_)
  congr 1
  rw [Fintype.prod_sum_type]
  congr 1
  · rw [← Finset.prod_coe_sort Sinf fun v ↦ s v ^ v.mult]
    exact Finset.prod_congr rfl fun v _ ↦ by simp [hsdef, v.2, sPlaceWeight]
  · rw [← Finset.prod_coe_sort Sfin fun v ↦ t v]
    exact Finset.prod_congr rfl fun v _ ↦ by simp [htdef, v.2, sPlaceWeight]

end NumberField

end
