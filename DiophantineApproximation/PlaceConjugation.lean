/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ConjugatePlaces
public import DiophantineApproximation.LocalExtension

-- Used only inside proofs.
import DiophantineApproximation.PlacesOver

/-!
# The places of a Galois extension as conjugates of one of them

For `E / K` Galois and a place `v` of `K`, Layer 0.2 says that the absolute values of `E` over `v`
form one orbit of `Gal(E/K)`. The Subspace Theorem with algebraic coefficients needs that in a
shape Layer 0.2 does not state: for a **typed place** `V` of `E` above `v` — an
`InfinitePlace E` or a `FinitePlace E`, both normalized as Mathlib normalizes them — and a chosen
absolute value `w'` of `E` over `v`, an automorphism `σ` with

```text
V (σ z) = w' z ^ (local degree)      for every z in E,
```

the local degree being `1` at an infinite place and `e f` at a finite one. At an infinite place
this is Layer 0.2 verbatim, because an infinite place of `E` above `v` *is* an absolute value over
`v`; at a finite place it is not, because Mathlib's finite places are normalized so that the
product formula holds with exponent one and therefore restrict to `v ^ (e f)` and not to `v`. The
`(e f)`-th root of a finite place is the absolute value Layer 0.2 applies to.

## Main results

* `NumberField.InfinitePlace.exists_algEquiv_apply_eq` and
  `NumberField.FinitePlace.exists_algEquiv_apply_eq`: the two shapes.
* `Real.iSup_pow_eq`: a supremum of nonnegative reals over a finite nonempty index commutes with
  a power — the shape in which a finite place's normalization passes through the denominator of a
  local factor.

## Implementation notes

⚠ **The finite half needs the `(e f)`-th root, and that root is an absolute value only because
the place is nonarchimedean.** `AbsoluteValue.nonarchRpow` of Layer 0.1 is what supplies it; at an
archimedean place only the exponents `t ≤ 1` are available, which is one more reason the two
halves cannot be treated uniformly.

This is part of Layer 6.3 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open NumberField

namespace Real

/-- **A supremum commutes with a power**, for nonnegative reals over a finite nonempty index. -/
theorem iSup_pow_eq {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) (n : ℕ) :
    ⨆ i, f i ^ n = (⨆ i, f i) ^ n := by
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max f
  have h1 : ⨆ i, f i = f i₀ :=
    le_antisymm (Real.iSup_le hi₀ (hf i₀)) (Finite.le_ciSup_of_le i₀ le_rfl)
  have h2 : ⨆ i, f i ^ n = f i₀ ^ n :=
    le_antisymm (Real.iSup_le (fun i ↦ pow_le_pow_left₀ (hf i) (hi₀ i) n) (pow_nonneg (hf i₀) n))
      (Finite.le_ciSup_of_le i₀ le_rfl)
  rw [h1, h2]

end Real

namespace NumberField

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

/-- **Every infinite place of `E` above `v` is a conjugate of the chosen absolute value over `v`**
(Bombieri–Gubler, Remark 7.2.3). At an infinite place the local degree is absorbed in `mult`, so
no exponent appears. -/
theorem InfinitePlace.exists_algEquiv_apply_eq [IsGalois K E] (v : InfinitePlace K)
    (w' : AbsoluteValue E ℝ) [w'.LiesOver v.1] (V : InfinitePlace E) (hV : V.LiesOver v) :
    ∃ σ : E ≃ₐ[K] E, ∀ z : E, V (σ z) = w' z := by
  have hmem : V.1 ∈ {w' : AbsoluteValue E ℝ | w'.LiesOver v.1} := hV
  rw [setOf_liesOver_eq_range_smul v.1 (Or.inl (isInfinitePlace v)) w'] at hmem
  obtain ⟨σ, hσ⟩ := hmem
  exact ⟨σ, fun z ↦ by rw [show V (σ z) = V.1 (σ z) from rfl, ← hσ]; simp⟩

/-- **Every finite place of `E` above `v` is a conjugate of the chosen absolute value over `v`,
raised to the local degree** (Bombieri–Gubler, Remark 7.2.3). The exponent is the price of
Mathlib's normalization of finite places; Layer 0.2 applies to the `(e f)`-th root. -/
theorem FinitePlace.exists_algEquiv_apply_eq [IsGalois K E] (v : FinitePlace K)
    (w' : AbsoluteValue E ℝ) [w'.LiesOver v.1] (V : FinitePlace E) (hV : V.LiesOver v) :
    ∃ σ : E ≃ₐ[K] E, ∀ z : E, V (σ z) = w' z ^ V.localDegree K := by
  have := hV
  have he : 0 < V.localDegree K := V.localDegree_pos
  have hna : IsNonarchimedean (V.1 : E → ℝ) := by
    rw [← V.mk_maximalIdeal]
    exact isNonarchimedean_mk _
  have hinv : (0 : ℝ) < ((V.localDegree K : ℝ))⁻¹ := by positivity
  set Vt := AbsoluteValue.nonarchRpow hna hinv with hVt
  have hpow : ∀ z : E, Vt z ^ V.localDegree K = V z := by
    intro z
    rw [hVt, AbsoluteValue.nonarchRpow_apply, ← Real.rpow_natCast (V.1 z ^ _) _,
      ← Real.rpow_mul (V.1.nonneg z), inv_mul_cancel₀ (by exact_mod_cast he.ne'),
      Real.rpow_one]
    rfl
  have hVtover : Vt.LiesOver v.1 := by
    refine ⟨AbsoluteValue.ext fun y ↦ ?_⟩
    change Vt (algebraMap K E y) = v y
    have hy : (0 : ℝ) ≤ v y := apply_nonneg _ _
    rw [hVt, AbsoluteValue.nonarchRpow_apply,
      show V.1 (algebraMap K E y) = v y ^ V.localDegree K from V.apply_algebraMap v y,
      ← Real.rpow_natCast (v y) (V.localDegree K), ← Real.rpow_mul hy,
      mul_inv_cancel₀ (by exact_mod_cast he.ne'), Real.rpow_one]
  have hmem : Vt ∈ {w' : AbsoluteValue E ℝ | w'.LiesOver v.1} := hVtover
  rw [setOf_liesOver_eq_range_smul v.1 (Or.inr (isFinitePlace v)) w'] at hmem
  obtain ⟨σ, hσ⟩ := hmem
  refine ⟨σ, fun z ↦ ?_⟩
  rw [← hpow (σ z), ← hσ]
  simp

end NumberField
