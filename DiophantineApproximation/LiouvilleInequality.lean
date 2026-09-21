/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Extension
public import DiophantineApproximation.FundamentalInequality
public import DiophantineApproximation.PlacesOver

public import Mathlib.NumberTheory.Real.Irrational

-- Used only inside proofs.
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Liouville's inequality over a number field

An algebraic number cannot be approximated too well by the elements of a number field, and the
statement that says so at *every* place at once is **Liouville's inequality**. Let `F / K` be an
extension of number fields, `α` an element of `F`, `β` an element of `K` distinct from it, and
choose for every place `v` of `K` an absolute value `w v` of `F` lying over it. Then

```text
(∏ v ∈ S∞, min 1 (w v (β − α)) ^ mult v) * ∏ v ∈ S₀, min 1 (w v (β − α))
    ≥ (2 ^ [F : ℚ] * H(α) * H(β) ^ [F : K])⁻¹,
```

the heights being Mathlib's relative ones, of `α` over `F` and of `β` over `K`. In particular no
single local factor can be small unless the heights are large, which is Step IV of every proof in
Layers 3 and 5 of the roadmap.

The proof is two lines of mathematics on top of
`DiophantineApproximation/FundamentalInequality.lean`. The truncated local factors of `β − α`,
taken over *all* the places of `F`, multiply to `(mulHeight₁ (β − α))⁻¹`; a finite subfamily has
a larger product, every factor being at most `1`; and `Height.mulHeight₁_sub_le` bounds
`mulHeight₁ (β − α)` by `2 ^ [F : ℚ] * H(α) * H(β) ^ [F : K]`. Everything else is the bookkeeping
that identifies the chosen `w v` inside the places of `F`, which is Layer 0.1.

The file closes with the classical statement the milestone asks for as its acceptance test:
Liouville's theorem over `ℝ` with the constant named, and Mathlib's
`Liouville.exists_pos_real_of_irrational_root` derived from it.

## Main results

* `NumberField.liouville_inequality`: the milestone, Bombieri–Gubler Theorem 1.5.21.
* `NumberField.liouville_inequality_self`: the case `F = K`, which needs none of the
  places-above-places bookkeeping and is what the acceptance test runs on.
* `NumberField.one_le_pow_mul_abs_sub_div`: Liouville's theorem over `ℝ` with the constant
  `2 ^ [F : ℚ] * mulHeight₁ ξ * (⌈|ψ ξ|⌉₊ + 1) ^ [F : ℚ]` exhibited, for a number field with a
  real embedding `ψ`.
* `NumberField.exists_infinitePlace_comap_eq` and
  `NumberField.exists_finitePlace_rpow_liesOver`: Layer 0.1's classification in the shape this
  layer consumes it, with the place of `F` named and, at a finite place, the exponent bundled.

## Implementation notes

⚠ **Layer 0.2 is not used.** Neither the local extension formula nor the Galois action on the
places above `v` appears. The inequality compares *one* chosen absolute value above each `v` with
the full product over `F`; it never counts the places above `v`, never adds their local degrees
and never conjugates one into another. What it does consume is Layer 0.1 — an absolute value over
an infinite place is an infinite place, one over a finite place is a root of a finite place — and
`ArithmeticHeights` 0.3, `NumberField.mulHeight₁_pow_finrank`, of which this is the roadmap's
first consumer.

⚠ **The truncation `min 1 ·` makes the statement stronger, not weaker.** Since
`min 1 t ≤ t`, the truncated product is at most the untruncated one, so the bound proved here
implies the bound without truncation. Bombieri–Gubler's `min` is the sharp form and there is no
reason to state the other.

⚠ **At an infinite place the work is `InfinitePlace.mult_comap_le`; at a finite place it is an
`rpow`.** Above an infinite `v` the chosen `w` is an infinite place `u` of `F` on the nose, and
`v.mult ≤ u.mult` is Mathlib's once `AbsoluteValue.LiesOver` has been turned into
`u.comap (algebraMap K F) = v`. Above a finite `v` there is no such identification: `w` is only
`|·|_𝔓 ^ (e f)⁻¹`, and what saves the comparison is that the exponent is at most `1`, so
`min 1 (s ^ t) ≥ min 1 s`. That three-line real inequality is the whole finite half.

⚠ **The comparison is a subproduct, so the chosen places must be distinct.** On the infinite side
injectivity of `v ↦ u v` is free — `u v` determines `v` as its `comap`. On the finite side it is
`Ideal.LiesOver` followed by `NumberField.FinitePlace.maximalIdeal_inj`: a prime of `𝓞 F` lies
over exactly one prime of `𝓞 K`.

⚠ **The acceptance test is the case `F = K`, and taking `K = ℚ` would be harder.** Deriving
`Liouville.exists_pos_real_of_irrational_root` looks like a job for the relative inequality with
`K = ℚ` and `F = ℚ⟮α⟯`, but that needs the infinite place of `ℚ` and an absolute value of `F`
over it. Reading everything in `F = ℚ⟮α⟯` instead — one real embedding, no finite places — needs
only `NumberField.mulHeight₁_pow_finrank` to turn `H_F(β)` into `H_ℚ(β) ^ [F : ℚ]`, and the only
further arithmetic is `Rat.mulHeight₁_eq_max` together with `q.num ∣ a` and `q.den ∣ b + 1`.

⚠ **The multiplicity never has to be computed.** The real place of `F` could a priori be complex,
and its `mult` is not `1` in general; `min 1 t ≤ 1` makes `(min 1 t) ^ mult ≤ min 1 t` for every
`mult ≥ 1`, so the acceptance test needs only `InfinitePlace.mult_ne_zero`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 1.5.21 and (1.8); the projective form is Theorem 2.8.21.

This is the second half of Layer 0.4 of the `DiophantineApproximation` roadmap.
-/

public section

open Height IsDedekindDomain Module

namespace NumberField

/-!
### Liouville's inequality over one number field
-/

section Self

variable {K : Type*} [Field K] [NumberField K]

/-- **Liouville's inequality over a number field**, in the case where the approximating element
lies in the same field. -/
theorem liouville_inequality_self (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) {α β : K} (hne : β ≠ α) :
    (2 ^ finrank ℚ K * mulHeight₁ α * mulHeight₁ β)⁻¹
      ≤ (∏ v ∈ Sinf, min 1 (v (β - α)) ^ v.mult) * ∏ v ∈ Sfin, min 1 (v (β - α)) := by
  have h0 : β - α ≠ 0 := sub_ne_zero.mpr hne
  refine le_trans ?_ (inv_mulHeight₁_le_prod_min_one_apply Sinf Sfin h0)
  have hle : mulHeight₁ (β - α) ≤ 2 ^ finrank ℚ K * mulHeight₁ α * mulHeight₁ β :=
    calc mulHeight₁ (β - α) ≤ 2 ^ totalWeight K * mulHeight₁ β * mulHeight₁ α :=
          mulHeight₁_sub_le β α
      _ = 2 ^ finrank ℚ K * mulHeight₁ α * mulHeight₁ β := by
          rw [totalWeight_eq_finrank]; ring
  have hpos : 0 < mulHeight₁ (β - α) := mulHeight₁_pos _
  gcongr

end Self

/-!
### Places above places, as the truncated local factors see them
-/

section Extension

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- Raising a nonnegative real to an exponent in `(0, 1]` moves it towards `1`, so it can only
increase the truncation `min 1 ·`. -/
private theorem min_one_le_min_one_rpow {s t : ℝ} (hs : 0 ≤ s) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    min 1 s ≤ min 1 (s ^ t) := by
  rcases le_or_gt s 1 with h | h
  · rw [min_eq_right h]
    refine le_min h ?_
    rcases eq_or_lt_of_le hs with rfl | hs'
    · rw [Real.zero_rpow ht0.ne']
    · calc s = s ^ (1 : ℝ) := (Real.rpow_one s).symm
        _ ≤ s ^ t := Real.rpow_le_rpow_of_exponent_ge hs' h ht1
  · rw [min_eq_left h.le]
    refine le_min le_rfl ?_
    calc (1 : ℝ) = 1 ^ t := (Real.one_rpow t).symm
      _ ≤ s ^ t := Real.rpow_le_rpow zero_le_one h.le ht0.le

/-- **An absolute value of `F` over an infinite place of `K` is an infinite place of `F` above
it.** The restriction condition of `AbsoluteValue.LiesOver` becomes the `comap` of
`NumberField.InfinitePlace`, which is what carries Mathlib's comparison of multiplicities. -/
theorem exists_infinitePlace_comap_eq (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    (hw : w.LiesOver v.1) :
    ∃ u : InfinitePlace F, (∀ y : F, u y = w y) ∧ u.comap (algebraMap K F) = v := by
  have := hw
  obtain ⟨u, hu⟩ := exists_infinitePlace_eq_of_liesOver v w
  have happ : ∀ y : F, u y = w y := fun y ↦ by rw [InfinitePlace.coe_apply, hu]
  refine ⟨u, happ, ?_⟩
  ext y
  rw [InfinitePlace.comap_apply, happ]
  exact AbsoluteValue.apply_algebraMap_of_liesOver w y

/-- **An absolute value of `F` over a finite place of `K` is a root of a finite place of `F`
above it**, restated from Layer 0.1 with the exponent bundled and the prime named. -/
theorem exists_finitePlace_rpow_liesOver (v : FinitePlace K) (w : AbsoluteValue F ℝ)
    (hw : w.LiesOver v.1) :
    ∃ (u : FinitePlace F) (t : ℝ), 0 < t ∧ t ≤ 1 ∧
      u.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal ∧ ∀ y : F, w y = u y ^ t := by
  have := hw
  obtain ⟨P, hover, hPt⟩ := exists_finitePlace_rpow_inv_eq_of_liesOver (K := K) v w
  have hef : 0 < P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) :=
    Nat.mul_pos (P.asIdeal.ramificationIdx_pos (𝓞 K)) (P.asIdeal.inertiaDeg_pos (𝓞 K))
  have hefR : (1 : ℝ) ≤ ((P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) : ℕ) : ℝ) :=
    by exact_mod_cast hef
  refine ⟨FinitePlace.mk P, _, by positivity, inv_le_one_of_one_le₀ hefR, ?_, hPt⟩
  rwa [FinitePlace.maximalIdeal_mk]

/-!
### Liouville's inequality
-/

/-- **Liouville's inequality over a number field** (Bombieri–Gubler, Theorem 1.5.21). Let `F / K`
be an extension of number fields, `α` an element of `F`, `β` an element of `K` distinct from it,
and choose for every place `v` of `K` an absolute value of `F` lying over `v`. Then the truncated
local factors of `β - α` over any finite set of places of `K` cannot all be small: their product
is at least `(2 ^ [F : ℚ] * H(α) * H(β) ^ [F : K])⁻¹`, the heights being Mathlib's relative ones
of `α` over `F` and of `β` over `K`. -/
theorem liouville_inequality (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (winf : InfinitePlace K → AbsoluteValue F ℝ) (hwinf : ∀ v, (winf v).LiesOver v.1)
    (wfin : FinitePlace K → AbsoluteValue F ℝ) (hwfin : ∀ v, (wfin v).LiesOver v.1)
    {α : F} {β : K} (hne : algebraMap K F β ≠ α) :
    (2 ^ finrank ℚ F * mulHeight₁ α * mulHeight₁ β ^ finrank K F)⁻¹
      ≤ (∏ v ∈ Sinf, min 1 (winf v (algebraMap K F β - α)) ^ v.mult)
        * ∏ v ∈ Sfin, min 1 (wfin v (algebraMap K F β - α)) := by
  classical
  set γ : F := algebraMap K F β - α with hγdef
  have hγ : γ ≠ 0 := sub_ne_zero.mpr hne
  choose uof huof hucomap using fun v : InfinitePlace K ↦
    exists_infinitePlace_comap_eq v (winf v) (hwinf v)
  choose mof tof htpos htle hmover hmeq using fun v : FinitePlace K ↦
    exists_finitePlace_rpow_liesOver v (wfin v) (hwfin v)
  have hnnI : ∀ u : InfinitePlace F, 0 ≤ min 1 (u γ) :=
    fun _ ↦ le_min zero_le_one (apply_nonneg _ _)
  have hA : (∏ u : InfinitePlace F, min 1 (u γ) ^ u.mult)
      ≤ ∏ v ∈ Sinf, min 1 (winf v γ) ^ v.mult :=
    calc (∏ u : InfinitePlace F, min 1 (u γ) ^ u.mult)
        ≤ ∏ u ∈ Sinf.image uof, min 1 (u γ) ^ u.mult :=
          Finset.prod_le_prod_of_subset_of_le_one₀ (Finset.subset_univ _)
            (fun u _ ↦ pow_nonneg (hnnI u) _)
            fun u _ _ ↦ pow_le_one₀ (hnnI u) (min_le_left _ _)
      _ = ∏ v ∈ Sinf, min 1 (uof v γ) ^ (uof v).mult :=
          Finset.prod_image fun a _ b _ h ↦ by rw [← hucomap a, ← hucomap b, h]
      _ ≤ ∏ v ∈ Sinf, min 1 (winf v γ) ^ v.mult := by
          refine Finset.prod_le_prod₀ (fun v _ ↦ pow_nonneg (hnnI _) _) fun v _ ↦ ?_
          rw [huof v]
          have hmult := InfinitePlace.mult_comap_le (algebraMap K F) (uof v)
          rw [hucomap v] at hmult
          exact pow_le_pow_of_le_one (le_min zero_le_one (apply_nonneg _ _))
            (min_le_left _ _) hmult
  have hminj : Function.Injective mof := by
    intro v v' h
    have h1 := (hmover v).over
    rw [h] at h1
    exact (FinitePlace.maximalIdeal_inj v v').mp
      (IsDedekindDomain.HeightOneSpectrum.ext (h1.trans (hmover v').over.symm))
  have hB : (∏ᶠ u : FinitePlace F, min 1 (u γ)) ≤ ∏ v ∈ Sfin, min 1 (wfin v γ) :=
    calc (∏ᶠ u : FinitePlace F, min 1 (u γ)) ≤ ∏ u ∈ Sfin.image mof, min 1 (u γ) :=
          finprod_min_one_le_prod _ hγ
      _ = ∏ v ∈ Sfin, min 1 (mof v γ) := Finset.prod_image fun a _ b _ h ↦ hminj h
      _ ≤ ∏ v ∈ Sfin, min 1 (wfin v γ) := by
          refine Finset.prod_le_prod₀ (fun _ _ ↦ le_min zero_le_one (apply_nonneg _ _))
            fun v _ ↦ ?_
          rw [hmeq v γ]
          exact min_one_le_min_one_rpow (apply_nonneg _ _) (htpos v) (htle v)
  have step : (mulHeight₁ γ)⁻¹ ≤ (∏ v ∈ Sinf, min 1 (winf v γ) ^ v.mult)
      * ∏ v ∈ Sfin, min 1 (wfin v γ) := by
    rw [← prod_min_one_apply_eq_inv_mulHeight₁ hγ]
    exact mul_le_mul hA hB (finprod_nonneg fun _ ↦ le_min zero_le_one (apply_nonneg _ _))
      (Finset.prod_nonneg fun _ _ ↦ pow_nonneg (le_min zero_le_one (apply_nonneg _ _)) _)
  refine le_trans ?_ step
  have hle : mulHeight₁ γ ≤ 2 ^ finrank ℚ F * mulHeight₁ α * mulHeight₁ β ^ finrank K F :=
    calc mulHeight₁ γ ≤ 2 ^ totalWeight F * mulHeight₁ (algebraMap K F β) * mulHeight₁ α := by
          rw [hγdef]; exact mulHeight₁_sub_le _ _
      _ = 2 ^ finrank ℚ F * mulHeight₁ α * mulHeight₁ β ^ finrank K F := by
          rw [totalWeight_eq_finrank, ← mulHeight₁_pow_finrank (L := F) β]; ring
  have hpos : 0 < mulHeight₁ γ := mulHeight₁_pos _
  gcongr

end Extension

/-!
### Liouville's theorem over `ℝ`, with the constant made explicit
-/

section Real

variable {F : Type*} [Field F] [NumberField F]

omit [NumberField F] in
/-- The infinite place of `F` cut out by a real embedding reads as the ordinary absolute value. -/
theorem apply_mk_algebraMap_comp (ψ : F →+* ℝ) (x : F) :
    (InfinitePlace.mk ((algebraMap ℝ ℂ).comp ψ)) x = |ψ x| := by
  rw [InfinitePlace.apply]
  simp

/-- **Liouville's inequality over `ℝ`, with the constant explicit.** If a number field `F` has a
real embedding `ψ` under which `ξ` becomes irrational, then no rational number `a / (b + 1)`
approximates `ψ ξ` to order `n ≥ [F : ℚ]` better than the constant
`2 ^ [F : ℚ] * mulHeight₁ ξ * (⌈|ψ ξ|⌉₊ + 1) ^ [F : ℚ]` allows. This is the shape of
`Liouville.exists_pos_real_of_irrational_root`, with the constant named. -/
theorem one_le_pow_mul_abs_sub_div (ψ : F →+* ℝ) {ξ : F} (hξ : Irrational (ψ ξ))
    {n : ℕ} (hn : finrank ℚ F ≤ n) (a : ℤ) (b : ℕ) :
    1 ≤ ((b : ℝ) + 1) ^ n * (|ψ ξ - a / (b + 1)| *
      (2 ^ finrank ℚ F * mulHeight₁ ξ * ((⌈|ψ ξ|⌉₊ : ℝ) + 1) ^ finrank ℚ F)) := by
  set d := finrank ℚ F with hd
  set B : ℝ := (b : ℝ) + 1 with hBdef
  set C : ℝ := (⌈|ψ ξ|⌉₊ : ℝ) + 1 with hCdef
  set A : ℝ := 2 ^ d * mulHeight₁ ξ * C ^ d with hAdef
  have hB1 : (1 : ℝ) ≤ B := by rw [hBdef]; have : (0 : ℝ) ≤ b := b.cast_nonneg; linarith
  have hC1 : (1 : ℝ) ≤ C := by
    rw [hCdef]; have : (0 : ℝ) ≤ (⌈|ψ ξ|⌉₊ : ℝ) := Nat.cast_nonneg _; linarith
  have hHξ : (1 : ℝ) ≤ mulHeight₁ ξ := one_le_mulHeight₁ ξ
  have hA1 : (1 : ℝ) ≤ A := by
    rw [hAdef]
    have h2 : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ one_le_two
    have h3 : (1 : ℝ) ≤ C ^ d := one_le_pow₀ hC1
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h2 hHξ) h3
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA1
  have hBn : (1 : ℝ) ≤ B ^ n := one_le_pow₀ hB1
  rcases le_or_gt 1 |ψ ξ - (a : ℝ) / B| with hbig | hsmall
  · have h2 : (1 : ℝ) ≤ |ψ ξ - (a : ℝ) / B| * A := by nlinarith
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ B ^ n * (|ψ ξ - (a : ℝ) / B| * A) :=
          mul_le_mul hBn h2 zero_le_one (le_trans zero_le_one hBn)
  · set q : ℚ := (a : ℚ) / ((b : ℚ) + 1) with hqdef
    have hB0 : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
    have hqr : ((q : ℚ) : ℝ) = (a : ℝ) / B := by rw [hqdef, hBdef]; push_cast; ring
    set u : InfinitePlace F := InfinitePlace.mk ((algebraMap ℝ ℂ).comp ψ) with hudef
    have hu : ∀ x : F, u x = |ψ x| := fun x ↦ by rw [hudef, apply_mk_algebraMap_comp]
    have hcast : (algebraMap ℚ F) q = (q : F) := eq_ratCast (algebraMap ℚ F) q
    have hne : (algebraMap ℚ F) q ≠ ξ := by
      intro h
      exact hξ ⟨q, by rw [← map_ratCast ψ q, ← hcast, h]⟩
    have hliou := liouville_inequality_self ({u} : Finset (InfinitePlace F)) ∅ hne
    rw [Finset.prod_singleton, Finset.prod_empty, mul_one] at hliou
    have hmin : min 1 (u ((algebraMap ℚ F) q - ξ)) ^ u.mult ≤ |ψ ξ - (a : ℝ) / B| :=
      calc min 1 (u ((algebraMap ℚ F) q - ξ)) ^ u.mult
          ≤ min 1 (u ((algebraMap ℚ F) q - ξ)) ^ 1 :=
            pow_le_pow_of_le_one (le_min zero_le_one (apply_nonneg _ _)) (min_le_left _ _)
              (Nat.one_le_iff_ne_zero.mpr u.mult_ne_zero)
        _ ≤ u ((algebraMap ℚ F) q - ξ) := by rw [pow_one]; exact min_le_right _ _
        _ = |ψ ξ - (a : ℝ) / B| := by
            rw [hu, map_sub, hcast, map_ratCast, hqr, abs_sub_comm]
    have key : (2 ^ d * mulHeight₁ ξ * mulHeight₁ ((algebraMap ℚ F) q))⁻¹
        ≤ |ψ ξ - (a : ℝ) / B| := le_trans hliou hmin
    have hqH : mulHeight₁ ((algebraMap ℚ F) q) = mulHeight₁ q ^ d :=
      (mulHeight₁_pow_finrank (L := F) q).symm
    have hMle : mulHeight₁ q ≤ C * B := by
      have hm : ((b : ℤ) + 1) ≠ 0 := by positivity
      have hq' : q = Rat.divInt a ((b : ℤ) + 1) := by
        rw [Rat.divInt_eq_div, hqdef]; push_cast; ring
      have hnum : q.num ∣ a := by rw [hq']; exact Rat.num_dvd a hm
      have hden : ((q.den : ℤ)) ∣ ((b : ℤ) + 1) := by rw [hq']; exact Rat.den_dvd a _
      have hdenle : (q.den : ℝ) ≤ B := by
        have := Int.le_of_dvd (by positivity) hden
        rw [hBdef]; exact_mod_cast this
      have hnumle : q.num.natAbs ≤ a.natAbs := by
        rcases eq_or_ne a 0 with rfl | ha
        · simp [hqdef]
        · exact Nat.le_of_dvd (Int.natAbs_pos.mpr ha) (Int.natAbs_dvd_natAbs.mpr hnum)
      have habs : |(a : ℝ)| ≤ C * B := by
        have h1 : |(q : ℝ)| ≤ C := by
          have h2 : |ψ ξ| ≤ (⌈|ψ ξ|⌉₊ : ℝ) := Nat.le_ceil _
          have h3 : |(a : ℝ) / B| - |ψ ξ| ≤ |(a : ℝ) / B - ψ ξ| := abs_sub_abs_le_abs_sub _ _
          rw [abs_sub_comm ((a : ℝ) / B) (ψ ξ)] at h3
          rw [hqr, hCdef]
          linarith
        have h5 : |(a : ℝ)| = |(q : ℝ)| * B := by
          rw [hqr, abs_div, abs_of_pos hB0]
          field_simp
        rw [h5]
        exact mul_le_mul_of_nonneg_right h1 (le_of_lt hB0)
      have hnumR : (q.num.natAbs : ℝ) ≤ C * B := by
        refine le_trans ?_ habs
        have hcast2 : ((a.natAbs : ℕ) : ℝ) = |(a : ℝ)| := by
          rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
        rw [← hcast2]
        exact_mod_cast hnumle
      rw [Rat.mulHeight₁_eq_max]
      push_cast
      exact max_le hnumR (le_trans hdenle (le_mul_of_one_le_left (le_of_lt hB0) hC1))
    have hbound : 2 ^ d * mulHeight₁ ξ * mulHeight₁ ((algebraMap ℚ F) q) ≤ A * B ^ d := by
      have hCB : mulHeight₁ q ^ d ≤ (C * B) ^ d :=
        pow_le_pow_left₀ (mulHeight₁_nonneg q) hMle d
      have hAB : A * B ^ d = 2 ^ d * mulHeight₁ ξ * (C * B) ^ d := by rw [hAdef, mul_pow]; ring
      rw [hqH, hAB]
      exact mul_le_mul_of_nonneg_left hCB (by positivity)
    have key2 : (A * B ^ d)⁻¹ ≤ |ψ ξ - (a : ℝ) / B| := by
      refine le_trans ?_ key
      gcongr
    have hBd : B ^ d ≤ B ^ n := pow_le_pow_right₀ hB1 hn
    calc (1 : ℝ) = (A * B ^ d)⁻¹ * (A * B ^ d) := by field_simp
      _ ≤ |ψ ξ - (a : ℝ) / B| * (A * B ^ n) := by gcongr
      _ = B ^ n * (|ψ ξ - (a : ℝ) / B| * A) := by ring

open IntermediateField in
/-- **Liouville's theorem over `ℝ`.** A real algebraic irrational `ξ` of degree `d` is approximated
by no rational `a / (b + 1)` better than `1 / (A * (b + 1) ^ d)`, for an explicit `A` depending
only on `ξ`. This is `NumberField.one_le_pow_mul_abs_sub_div` read inside the number field
`ℚ⟮ξ⟯ ⊆ ℝ`, where the constant is
`2 ^ d * mulHeight₁ ξ * (⌈|ξ|⌉₊ + 1) ^ d`. -/
theorem _root_.Real.exists_pos_one_le_pow_natDegree_mul_abs_sub_div {ξ : ℝ}
    (hirr : Irrational ξ) (halg : IsAlgebraic ℚ ξ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (a : ℤ) (b : ℕ),
      1 ≤ ((b : ℝ) + 1) ^ (minpoly ℚ ξ).natDegree * (|ξ - a / (b + 1)| * A) := by
  have hint : IsIntegral ℚ ξ := halg.isIntegral
  have hfd : FiniteDimensional ℚ ℚ⟮ξ⟯ := adjoin.finiteDimensional hint
  have hnf : NumberField ℚ⟮ξ⟯ := {}
  have hdeg : finrank ℚ ℚ⟮ξ⟯ = (minpoly ℚ ξ).natDegree := adjoin.finrank hint
  have hψξ : (algebraMap ℚ⟮ξ⟯ ℝ) (AdjoinSimple.gen ℚ ξ) = ξ := AdjoinSimple.algebraMap_gen ℚ ξ
  refine ⟨2 ^ finrank ℚ ℚ⟮ξ⟯ * mulHeight₁ (AdjoinSimple.gen ℚ ξ)
    * ((⌈|ξ|⌉₊ : ℝ) + 1) ^ finrank ℚ ℚ⟮ξ⟯, by positivity, fun a b ↦ ?_⟩
  have h := one_le_pow_mul_abs_sub_div (algebraMap ℚ⟮ξ⟯ ℝ)
    (ξ := AdjoinSimple.gen ℚ ξ) (by rw [hψξ]; exact hirr) hdeg.le a b
  rwa [hψξ] at h

/-! ### Acceptance criteria -/

open IntermediateField Polynomial in
/-- **Acceptance test: Mathlib's `Liouville.exists_pos_real_of_irrational_root` follows**, with
the constant `A` exhibited. The number field is `ℚ⟮α⟯` inside `ℝ`, its real embedding is the
inclusion, and the order `n` of approximation is `f.natDegree`, which bounds `[ℚ⟮α⟯ : ℚ]` because
the minimal polynomial of `α` divides `f`. -/
example {α : ℝ} (ha : Irrational α) {f : ℤ[X]} (f0 : f ≠ 0)
    (fa : eval α (map (algebraMap ℤ ℝ) f) = 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℤ, ∀ b : ℕ,
      (1 : ℝ) ≤ ((b : ℝ) + 1) ^ f.natDegree * (|α - a / (b + 1)| * A) := by
  have hginj : Function.Injective (algebraMap ℤ ℚ) := (algebraMap ℤ ℚ).injective_int
  set g : ℚ[X] := f.map (algebraMap ℤ ℚ) with hgdef
  have hgne : g ≠ 0 := by
    rw [hgdef]
    exact (Polynomial.map_ne_zero_iff hginj).mpr f0
  have hga : aeval α g = 0 := by
    rw [hgdef, aeval_def, eval₂_eq_eval_map, Polynomial.map_map,
      ← IsScalarTower.algebraMap_eq ℤ ℚ ℝ]
    exact fa
  have hdeg : (minpoly ℚ α).natDegree ≤ f.natDegree := by
    have h1 : (minpoly ℚ α).natDegree ≤ g.natDegree :=
      Polynomial.natDegree_le_natDegree (minpoly.degree_le_of_ne_zero ℚ α hgne hga)
    have h2 : g.natDegree = f.natDegree := by
      rw [hgdef]; exact Polynomial.natDegree_map_eq_of_injective hginj f
    omega
  obtain ⟨A, hA0, hA⟩ := Real.exists_pos_one_le_pow_natDegree_mul_abs_sub_div ha ⟨g, hgne, hga⟩
  refine ⟨A, hA0, fun a b ↦ le_trans (hA a b) ?_⟩
  have hB1 : (1 : ℝ) ≤ (b : ℝ) + 1 := by
    have : (0 : ℝ) ≤ b := b.cast_nonneg
    linarith
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 hdeg) (by positivity)

/-- **Rejection test: the factor `2 ^ [K : ℚ]` cannot be dropped.** The bound
`mulHeight₁ (β - α) ≤ 2 ^ [K : ℚ] * mulHeight₁ α * mulHeight₁ β` that
`NumberField.liouville_inequality_self` runs on is false without it: over `ℚ`, at `α = -1` and
`β = 1`, the difference is `2`, of height `2`, while both heights are `1`. -/
example : ¬ mulHeight₁ ((1 : ℚ) - (-1 : ℚ)) ≤ mulHeight₁ (-1 : ℚ) * mulHeight₁ (1 : ℚ) := by
  norm_num [Rat.mulHeight₁_eq_max]

end Real

end NumberField
