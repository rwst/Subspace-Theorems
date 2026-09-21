/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Polynomial

/-!
# Transport from local factors to heights, one object at a time

`ArithmeticHeights`'s `Finsupp.mulHeight_le_of_forall_iSup_le` compares the local factor of one
finitely supported family with the *product* of the local factors of two others, and demands an
**equality** at the nonarchimedean absolute values — which is what Gauss's lemma supplies for a
product of polynomials. Roth's lemma compares a single family with a *power* of a single other
one, and at the nonarchimedean places it has only an inequality: a Hasse derivative does not
increase the local factor, and nothing says it preserves it.

This file proves that transport. The obstruction is that `Height.mulHeight` is a `finprod` over
the nonarchimedean absolute values, and `finprod_le_finprod₀` needs both sides to have finite
multiplicative support — a fact Mathlib has for a single field element
(`AdmissibleAbsValues.hasFiniteMulSupport`) and only privately for the local factor of a family.
`Finsupp.hasFiniteMulSupport_iSup_apply` recovers it in three lines: off the finitely many
absolute values where some coefficient is not a unit, every coefficient has absolute value `1`
and so does their supremum.

## Main results

* `Finsupp.hasFiniteMulSupport_iSup_apply`: the local factor of a nonzero family is `1` at all
  but finitely many nonarchimedean absolute values.
* `Finsupp.mulHeight_le_pow_of_forall_iSup_le`: the transport, with a constant at the archimedean
  absolute values and a one-sided bound at the others.
* `MvPolynomial.mulHeight_le_pow_of_forall_iSup_le`: its form for polynomials.

## Implementation notes

⚠ **The general two-input form with an inequality at the nonarchimedean places is not what is
proved here.** One input suffices for every consumer in Layer 2.7, because a *power* of a local
factor is what the determinant estimate produces, and `Finsupp.mulHeight` has
`finprod_pow` available once the support is known to be finite. A two-input form would need the
same support lemma twice and nothing else.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.6.

This is part of Layer 2.7 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height AdmissibleAbsValues

namespace Finsupp

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {α γ : Type*}

/-- **The local factor of a nonzero family is `1` at all but finitely many nonarchimedean
absolute values.** The multiplicative support is contained in the union, over the finitely many
coefficients in the support, of the multiplicative supports of the coefficients themselves. -/
theorem hasFiniteMulSupport_iSup_apply {x : α →₀ K} (hx : x ≠ 0) :
    (fun v : nonarchAbsVal (K := K) ↦ ⨆ i : α, v.val (x i)).HasFiniteMulSupport := by
  classical
  obtain ⟨i₀, hi₀⟩ := Finsupp.support_nonempty_iff.mpr hx
  have hne : Nonempty x.support := ⟨⟨i₀, hi₀⟩⟩
  refine Set.Finite.subset (Set.Finite.biUnion x.support.finite_toSet fun i hi ↦
    AdmissibleAbsValues.hasFiniteMulSupport (Finsupp.mem_support_iff.mp hi)) ?_
  intro v hv
  by_contra hmem
  refine hv ?_
  have h1 : ∀ i : x.support, v.val (x i.val) = 1 := fun i ↦ by
    by_contra hne'
    exact hmem (Set.mem_biUnion (Finset.mem_coe.mpr i.prop) hne')
  change (⨆ i : α, v.val (x i)) = 1
  rw [iSup_apply_eq_iSup_support x v.val]
  simp only [h1, ciSup_const]

/-- **The transport, one object against a power of another.** If the local factor of `z` is at
most `C` times the `p`-th power of that of `x` at every archimedean absolute value and at most
that power at every nonarchimedean one, then `mulHeight z ≤ C ^ totalWeight K * mulHeight x ^ p`.

No hypothesis is needed on `z`: at `z = 0` the height is the junk value `1`, which the right-hand
side dominates. -/
theorem mulHeight_le_pow_of_forall_iSup_le {x : α →₀ K} {z : γ →₀ K} {C : ℝ} {p : ℕ}
    (hx : x ≠ 0) (hC : 1 ≤ C)
    (harch : ∀ v ∈ archAbsVal (K := K), (⨆ i : γ, v (z i)) ≤ C * (⨆ i : α, v (x i)) ^ p)
    (hnon : ∀ v ∈ nonarchAbsVal (K := K), (⨆ i : γ, v (z i)) ≤ (⨆ i : α, v (x i)) ^ p) :
    z.mulHeight ≤ C ^ totalWeight K * x.mulHeight ^ p := by
  have hCtw : (1 : ℝ) ≤ C ^ totalWeight K := one_le_pow₀ hC
  have hxh : (1 : ℝ) ≤ x.mulHeight ^ p := one_le_pow₀ x.one_le_mulHeight
  rcases eq_or_ne z 0 with rfl | hz
  · rw [Finsupp.mulHeight_zero]
    exact one_le_mul_of_one_le_of_one_le hCtw hxh
  have hzc : ⇑z ≠ 0 := fun h ↦ hz (DFunLike.coe_injective h)
  have hxc : ⇑x ≠ 0 := fun h ↦ hx (DFunLike.coe_injective h)
  have hFnn : ∀ v : AbsoluteValue K ℝ, 0 ≤ ⨆ i : α, v (x i) :=
    fun v ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _
  have hGnn : ∀ v : AbsoluteValue K ℝ, 0 ≤ ⨆ i : γ, v (z i) :=
    fun v ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _
  rw [← Finsupp.mulHeight_coe_eq z, ← Finsupp.mulHeight_coe_eq x, Height.mulHeight_eq hzc,
    Height.mulHeight_eq hxc]
  have harchprod :
      (archAbsVal.map fun v ↦ ⨆ i : γ, v (z i)).prod
        ≤ C ^ totalWeight K * (archAbsVal.map fun v ↦ ⨆ i : α, v (x i)).prod ^ p := by
    calc (archAbsVal.map fun v ↦ ⨆ i : γ, v (z i)).prod
        ≤ (archAbsVal.map fun v ↦ C * (⨆ i : α, v (x i)) ^ p).prod :=
          Multiset.prod_map_le_prod_map₀ _ _ (fun v _ ↦ hGnn v) harch
      _ = (archAbsVal.map fun _ : AbsoluteValue K ℝ ↦ C).prod
            * (archAbsVal.map fun v ↦ (⨆ i : α, v (x i)) ^ p).prod := Multiset.prod_map_mul
      _ = C ^ totalWeight K * (archAbsVal.map fun v ↦ ⨆ i : α, v (x i)).prod ^ p := by
          rw [Multiset.map_const', Multiset.prod_replicate, ← Multiset.prod_map_pow]
          rfl
  have hnonprod :
      (∏ᶠ v : nonarchAbsVal (K := K), ⨆ i : γ, v.val (z i))
        ≤ (∏ᶠ v : nonarchAbsVal (K := K), ⨆ i : α, v.val (x i)) ^ p := by
    have hFp : (fun v : nonarchAbsVal (K := K) ↦ (⨆ i : α, v.val (x i)) ^ p).HasFiniteMulSupport :=
      Set.Finite.subset (hasFiniteMulSupport_iSup_apply hx) fun v hv ↦ by
        simp only [Function.mem_mulSupport] at hv ⊢
        exact fun h ↦ hv (by rw [h, one_pow])
    rw [finprod_pow (hasFiniteMulSupport_iSup_apply hx)]
    exact finprod_le_finprod₀ (hasFiniteMulSupport_iSup_apply hz) (fun v ↦ hGnn v.val)
      hFp fun v ↦ hnon v.val v.prop
  have hXnn : (0 : ℝ) ≤ (archAbsVal.map fun v ↦ ⨆ i : α, v (x i)).prod :=
    Multiset.prod_nonneg fun a ha ↦ by
      obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp ha
      exact hFnn v
  calc (archAbsVal.map fun v ↦ ⨆ i : γ, v (z i)).prod
          * ∏ᶠ v : nonarchAbsVal (K := K), ⨆ i : γ, v.val (z i)
      ≤ (C ^ totalWeight K * (archAbsVal.map fun v ↦ ⨆ i : α, v (x i)).prod ^ p)
          * (∏ᶠ v : nonarchAbsVal (K := K), ⨆ i : α, v.val (x i)) ^ p :=
        mul_le_mul harchprod hnonprod (finprod_nonneg fun v ↦ hGnn v.val)
          (mul_nonneg (by positivity) (pow_nonneg hXnn p))
    _ = C ^ totalWeight K * ((archAbsVal.map fun v ↦ ⨆ i : α, v (x i)).prod
          * ∏ᶠ v : nonarchAbsVal (K := K), ⨆ i : α, v.val (x i)) ^ p := by
        rw [mul_pow, mul_assoc]

end Finsupp

namespace MvPolynomial

open Height AdmissibleAbsValues

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {σ : Type*}

/-- **The transport for polynomials**: `Finsupp.mulHeight_le_pow_of_forall_iSup_le` read through
`MvPolynomial.mulHeight`. -/
theorem mulHeight_le_pow_of_forall_iSup_le {P Q : MvPolynomial σ K} {C : ℝ} {p : ℕ}
    (hP : P ≠ 0) (hC : 1 ≤ C)
    (harch : ∀ v ∈ archAbsVal (K := K),
      (⨆ ν, v (Q.coeff ν)) ≤ C * (⨆ ν, v (P.coeff ν)) ^ p)
    (hnon : ∀ v ∈ nonarchAbsVal (K := K),
      (⨆ ν, v (Q.coeff ν)) ≤ (⨆ ν, v (P.coeff ν)) ^ p) :
    Q.mulHeight ≤ C ^ totalWeight K * P.mulHeight ^ p :=
  Finsupp.mulHeight_le_pow_of_forall_iSup_le
    (fun h ↦ hP (by ext ν; exact congrFun (congrArg DFunLike.coe h) ν)) hC harch hnon

end MvPolynomial
