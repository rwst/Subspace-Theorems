/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.UnitEquationSeveral
public import Mathlib.LinearAlgebra.Projectivization.Basic

-- Used only inside proofs.
import Mathlib.Data.Finset.Option

/-!
# The projective solutions of the homogeneous unit equation

Schlickewei proves his Theorem 1.1, a bound for the number of solutions of

```text
a₁ x₁ + ⋯ + aₙ xₙ = 1                                                        (1.4)
```

in `S`-units with no vanishing subsum, in its homogeneous form: the number of **projective**
solutions `(x₁ : ⋯ : x_{n+1})` of

```text
α₁ x₁ + ⋯ + αₙ xₙ + α_{n+1} x_{n+1} = 0                                      (1.6)
```

with a representative in `S`-units and no vanishing proper subsum. "It is clear that this claim
is equivalent with the assertion of Theorem 1.1" (p. 96). This file makes the equivalence
precise: with the index set `Option ι` (`none` the extra coordinate `x_{n+1}`) and
`aᵢ = -αᵢ / α_{n+1}`, the map `x ↦ (x₁ : ⋯ : xₙ : 1)` is a bijection from the solutions of (1.4)
(`NumberField.unitSolutions`, Layer 8.2) onto the projective solutions of (1.6). A projective
solution has a representative with `x_{n+1} = 1` because `x_{n+1}` is an `S`-unit, and the
proper subsums of (1.6) vanish exactly when the subsums of (1.4) do: a proper subsum containing
`x_{n+1}` vanishes iff its complement, a subsum of (1.4), does.

The change of variables (3.1) `yᵢ = αᵢ xᵢ`, with `∏_{v ∈ S} ‖yᵢ‖_v = ∏_{v ∈ S} ‖αᵢ‖_v` (3.3), is
`NumberField.placeProd_univ_mul_unit` of `DiophantineApproximation/PlaceProd.lean`.

## Main definitions

* `NumberField.projUnitSolutions`: the projective solutions of (1.6).
* `NumberField.homogenize`: `x ↦ (x, 1)`, indexed by `Option ι`.

## Main results

* `NumberField.projUnitSolutions_eq_image`: the projective solutions of (1.6) are the image of
  the solutions of (1.4).
* `NumberField.ncard_projUnitSolutions`: **the two counts agree**.
* `NumberField.finite_projUnitSolutions`: the projective solutions are finite (Layer 8.2).
* `NumberField.projUnitSolutions_mono`, `NumberField.projUnitSolutions_mul`: the reductions of
  S90.3, to a set `S` with a finite place and to normalized coefficients (these come from
  `NumberField.exists_mul_isIntegral_inv_le_finprod_iSup`, DA `BalancedPoint.lean`).

## References

H. P. Schlickewei, *`S`-unit equations over number fields*, Invent. Math. **102** (1990), 95–107,
§1, (1.4) and (1.6).

This is milestone S90.1 of `Schlickewei1990/README.md`.
-/

@[expose] public section

open Finset IsDedekindDomain

namespace NumberField

variable {K : Type*} [Field K] {ι : Type*}

/-- A tuple of units, read in `K`, is a nonzero vector. -/
theorem coe_units_ne_zero [Nonempty ι] (x : ι → Kˣ) : (fun i ↦ (x i : K)) ≠ 0 := fun h ↦
  (x (Classical.arbitrary ι)).ne_zero (congrFun h _)

/-- **`x ↦ (x, 1)`**: the tuple `x` with the coordinate `1` added at `none`. -/
def homogenize (x : ι → Kˣ) : Option ι → Kˣ := fun o ↦ o.elim 1 x

@[simp]
theorem homogenize_none (x : ι → Kˣ) : homogenize x none = 1 := rfl

@[simp]
theorem homogenize_some (x : ι → Kˣ) (i : ι) : homogenize x (some i) = x i := rfl

/-- A sum over a set of `Option ι` not containing `none` is a sum over `ι`. -/
theorem sum_eq_sum_eraseNone {M : Type*} [AddCommMonoid M] (f : Option ι → M)
    {J : Finset (Option ι)} (hJ : none ∉ J) : ∑ o ∈ J, f o = ∑ i ∈ J.eraseNone, f (some i) := by
  classical
  calc ∑ o ∈ J, f o = ∑ o ∈ J.eraseNone.map Function.Embedding.some, f o := by
        rw [map_some_eraseNone, erase_eq_of_notMem hJ]
    _ = _ := sum_map _ _ _

/-- A nonempty set of `Option ι` not containing `none` has nonempty `eraseNone`. -/
theorem nonempty_eraseNone {J : Finset (Option ι)} (hJ : J.Nonempty) (hn : none ∉ J) :
    J.eraseNone.Nonempty := by
  obtain ⟨o, ho⟩ := hJ
  cases o with
  | none => exact absurd ho hn
  | some i => exact ⟨i, mem_eraseNone.2 ho⟩

/-- The point `(x₁ : ⋯ : xₙ : 1)` of `ℙ(K^{Option ι})`. -/
noncomputable def homogenizeMk (x : ι → Kˣ) : Projectivization K (Option ι → K) :=
  Projectivization.mk K (fun o ↦ (homogenize x o : K)) (coe_units_ne_zero _)

/-- `x ↦ (x₁ : ⋯ : xₙ : 1)` is injective. -/
theorem homogenizeMk_injective : Function.Injective (homogenizeMk (K := K) (ι := ι)) := by
  intro x y h
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).1 h
  have hc1 : (c : K) = 1 := by
    simpa [Units.smul_def] using congrFun hc none
  funext i
  ext
  simpa [Units.smul_def, hc1] using (congrFun hc (some i)).symm

/-- The coefficients of (1.4) from those of (1.6): `aᵢ = -αᵢ / α_{n+1}`. -/
theorem sum_mul_some_eq {α : Option ι → K} (h0 : α none ≠ 0) (I : Finset ι) (z : ι → K) :
    ∑ i ∈ I, α (some i) * z i = -α none * ∑ i ∈ I, -α (some i) / α none * z i := by
  rw [mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  field_simp

variable [Fintype ι] [NumberField K]

/-- **The projective solutions of the homogeneous unit equation** (1.6): the points of
`ℙ(Kⁱ)` with a representative `x` in `S`-units such that `∑ i, α i * x i = 0` and no proper
nonempty subsum vanishes. -/
def projUnitSolutions [Nonempty ι] (S : Finset (HeightOneSpectrum (𝓞 K))) (α : ι → K) :
    Set (Projectivization K (ι → K)) :=
  {p | ∃ x : ι → Kˣ, (∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) ∧
    ∑ i, α i * x i = 0 ∧ (∀ J : Finset ι, J.Nonempty → J ≠ univ → ∑ i ∈ J, α i * x i ≠ 0) ∧
    Projectivization.mk K (fun i ↦ (x i : K)) (coe_units_ne_zero x) = p}

/-- **Enlarging `S` keeps every projective solution.** So a bound for `S'` is a bound for `S`;
the Subspace step uses it to have a finite place in `S`. -/
theorem projUnitSolutions_mono [Nonempty ι] {S S' : Finset (HeightOneSpectrum (𝓞 K))}
    (h : S ⊆ S') (α : ι → K) : projUnitSolutions S α ⊆ projUnitSolutions S' α :=
  fun _ ⟨x, hx, h1, h2, h3⟩ ↦ ⟨x, fun i ↦ mem_unit_of_subset (coe_subset.2 h) (hx i), h1, h2, h3⟩

/-- **Scaling the coefficients does not change the projective solutions.** -/
theorem projUnitSolutions_mul [Nonempty ι] (S : Finset (HeightOneSpectrum (𝓞 K))) {c : K}
    (hc : c ≠ 0) (α : ι → K) : projUnitSolutions S (fun i ↦ c * α i) = projUnitSolutions S α := by
  have key : ∀ (x : ι → Kˣ) (J : Finset ι),
      ∑ i ∈ J, c * α i * x i = c * ∑ i ∈ J, α i * x i := fun x J ↦ by
    rw [mul_sum]
    simp only [mul_assoc]
  ext p
  constructor <;> rintro ⟨x, hx, h1, h2, h3⟩ <;> refine ⟨x, hx, ?_, fun J hJ hJu ↦ ?_, h3⟩
  · rw [key] at h1
    exact (mul_eq_zero.1 h1).resolve_left hc
  · have h := h2 J hJ hJu
    rw [key] at h
    exact right_ne_zero_of_mul h
  · rw [key, h1, mul_zero]
  · rw [key]
    exact mul_ne_zero hc (h2 J hJ hJu)

section Dictionary

variable {α : Option ι → K}

/-- **The projective solutions of (1.6) are the image of the solutions of (1.4)** under
`x ↦ (x₁ : ⋯ : xₙ : 1)`, with `aᵢ = -αᵢ / α_{n+1}`. -/
theorem projUnitSolutions_eq_image (S : Finset (HeightOneSpectrum (𝓞 K))) (h0 : α none ≠ 0) :
    projUnitSolutions S α =
      homogenizeMk '' unitSolutions S (fun i ↦ -α (some i) / α none) := by
  classical
  ext p
  constructor
  · rintro ⟨x, hxS, hsum, hsub, rfl⟩
    set y : ι → Kˣ := fun i ↦ x (some i) / x none with hy
    have hx0 : α none * x none ≠ 0 := mul_ne_zero h0 (x none).ne_zero
    -- the sums of (1.4) at `y` are those of (1.6) at `x`, times `-1 / (α_{n+1} x_{n+1})`
    have hI : ∀ I : Finset ι, ∑ i ∈ I, -α (some i) / α none * (y i : K) =
        (∑ i ∈ I, α (some i) * x (some i)) * (-1 / (α none * x none)) := by
      intro I
      rw [sum_mul]
      refine sum_congr rfl fun i _ ↦ ?_
      simp only [hy, Units.val_div_eq_div_val]
      field_simp
    refine ⟨y, ⟨fun i ↦ div_mem (hxS _) (hxS _), ?_, fun I hI0 ↦ ?_⟩, ?_⟩
    · rw [hI]
      have h := hsum
      rw [Fintype.sum_option] at h
      rw [show ∑ i, α (some i) * (x (some i) : K) = -(α none * x none) by linear_combination h]
      field_simp
    · rw [hI]
      refine mul_ne_zero ?_ (div_ne_zero (by norm_num) hx0)
      rw [show ∑ i ∈ I, α (some i) * (x (some i) : K) =
          ∑ o ∈ I.map Function.Embedding.some, α o * x o by rw [sum_map]; rfl]
      refine hsub _ hI0.map fun h ↦ ?_
      have : none ∈ I.map Function.Embedding.some := h ▸ mem_univ _
      simp at this
    · refine (Projectivization.mk_eq_mk_iff K _ _ _ _).2 ⟨(x none)⁻¹, funext fun o ↦ ?_⟩
      cases o with
      | none => simp [Units.smul_def]
      | some i =>
        simp only [Pi.smul_apply, Units.smul_def, homogenize_some, hy, smul_eq_mul,
          Units.val_div_eq_div_val, Units.val_inv_eq_inv_val]
        field_simp
  · rintro ⟨x, ⟨hxS, hsum, hsub⟩, rfl⟩
    have hsome : ∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, α (some i) * (x i : K) ≠ 0 := fun I hI ↦ by
      rw [sum_mul_some_eq h0]
      exact mul_ne_zero (neg_ne_zero.2 h0) (hsub I hI)
    have hnone : ∀ J : Finset (Option ι), J.Nonempty → none ∉ J →
        ∑ o ∈ J, α o * (homogenize x o : K) ≠ 0 := fun J hJ hn ↦ by
      rw [sum_eq_sum_eraseNone _ hn]
      simpa using hsome _ (nonempty_eraseNone hJ hn)
    have htot : ∑ o, α o * (homogenize x o : K) = 0 := by
      rw [Fintype.sum_option]
      simp only [homogenize_none, Units.val_one, mul_one, homogenize_some]
      rw [sum_mul_some_eq h0, hsum]
      ring
    refine ⟨homogenize x, fun o ↦ ?_, htot, fun J hJ hJu ↦ ?_, rfl⟩
    · cases o with
      | none => exact one_mem _
      | some i => exact hxS i
    · by_cases hn : none ∈ J
      · have hc : none ∉ Jᶜ := by simpa using hn
        have h := sum_add_sum_compl J (fun o ↦ α o * (homogenize x o : K))
        rw [htot] at h
        rw [show ∑ o ∈ J, α o * (homogenize x o : K) = -∑ o ∈ Jᶜ, α o * (homogenize x o : K) by
          linear_combination h]
        have hne : Jᶜ.Nonempty := nonempty_iff_ne_empty.2 fun h ↦ hJu ((compl_eq_empty_iff J).1 h)
        exact neg_ne_zero.2 (hnone _ hne hc)
      · exact hnone J hJ hn

/-- **Theorem 1.1 and its homogeneous form (1.6) count the same thing**: the number of
projective solutions of (1.6) is the number of solutions of (1.4), `aᵢ = -αᵢ / α_{n+1}`. -/
theorem ncard_projUnitSolutions (S : Finset (HeightOneSpectrum (𝓞 K))) (h0 : α none ≠ 0) :
    (projUnitSolutions S α).ncard = (unitSolutions S (fun i ↦ -α (some i) / α none)).ncard := by
  rw [projUnitSolutions_eq_image S h0, Set.ncard_image_of_injective _ homogenizeMk_injective]

/-- **The projective solutions of (1.6) are finitely many**, for nonzero coefficients (from
Layer 8.2, `NumberField.finite_unitSolutions`). -/
theorem finite_projUnitSolutions (S : Finset (HeightOneSpectrum (𝓞 K))) (hα : ∀ o, α o ≠ 0) :
    (projUnitSolutions S α).Finite := by
  rw [projUnitSolutions_eq_image S (hα none)]
  exact (finite_unitSolutions S _ fun i ↦ div_ne_zero (neg_ne_zero.2 (hα _)) (hα none)).image _

end Dictionary

end NumberField
