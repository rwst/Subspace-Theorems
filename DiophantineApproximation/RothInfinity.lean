/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.PlacesOver
public import DiophantineApproximation.RothTheorem
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Roth's theorem with targets at infinity

**Layer 3.3, the general form** (Bombieri–Gubler, Remark 6.2.5). Roth's theorem as Layer 3.2
proves it carries one target `α v ∈ F` at each place of `S`. The forms the applications quote —
Ridout's theorem, the `p`-adic form, Mahler's theorem on `(p / q) ^ k` — need the point at
infinity as a target too, with the local factor

```text
Λ v β = (max 1 |β| v)⁻¹      instead of     Λ v β = min 1 |β - α v| v.
```

This file states Roth's theorem with targets in `OnePoint F` and proves it from Layer 3.2 by the
Möbius change of variable `β ↦ (β - c)⁻¹`, which sends `∞` to `0` and moves every other target
to a finite one.

## Main results

* `NumberField.finite_setOf_prod_onePointApprox_le`: Roth's theorem with targets in `OnePoint F`.
* `AbsoluteValue.onePointApprox`: the local factor at a target in `OnePoint F`.
* `AbsoluteValue.min_one_sub_onePointMobius_le`: the local content — the Möbius change of
  variable distorts each factor by a constant that does not depend on `β`.
* `NumberField.exists_liesOver_fun`: Layer 0.1's fibres, packaged as one function.

## Implementation notes

⚠ **The factor at `∞` is `(max 1 |β|)⁻¹`, not `min 1 |β|⁻¹`.** The two agree for `β ≠ 0`, and
the second is the reading the roadmap gives; but in Lean `(0 : ℝ)⁻¹ = 0`, so at `β = 0` the
second is `0` where the value of the factor is `1`. Written as a reciprocal of a maximum the
definition needs no case and no hypothesis, and the acceptance criteria below pin the difference.

⚠ **A single inversion does not suffice, and the base point must avoid the targets.** The map
`β ↦ β⁻¹` exchanges the targets `0` and `∞` rather than removing `∞`, so it cannot clear a mixed
configuration. The map used is `β ↦ (β - c)⁻¹` with `c ∈ K` chosen off the finitely many targets;
it sends `∞` to `0` and each finite `α v` to `(α v - c)⁻¹`, all finite. Such a `c` exists because
`K` is infinite and `S` is finite.

⚠ **The distortion at a finite target needs two cases, and they are not symmetric.** The new
factor is the old one divided by `|β - c| v |α v - c| v`, which is harmless when `β` is far from
`c`; when `β` is *close* to `c` the denominator is small, but then `β` is far from `α v` and the
old factor is bounded below by a constant. Only the second case uses that `α v ≠ c`.

⚠ **The constant is absorbed by lowering the exponent, not by sharpening the estimate.** The
change of variable multiplies the left side by a constant `C` and the height by a constant, so
what comes out is `Λ ≤ C H ^ (-κ)`, not `Λ ≤ H ^ (-κ)`. Roth's theorem is then applied at an
exponent `κ₁` strictly between `2` and `κ`, and the finitely many `β` of height below
`C ^ (κ - κ₁)⁻¹` are collected by Northcott. This is the only place in Layer 3.3 where `κ > 2`
is used with room to spare.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Remark 6.2.5.

This is part of Layer 3.3 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height OnePoint

namespace AbsoluteValue

variable {F : Type*} [Field F] (W : AbsoluteValue F ℝ)

/-- The local approximation factor at a target in `OnePoint F`: `min 1 |β - a|` at a finite
target `a`, and `(max 1 |β|)⁻¹` at the target `∞`. -/
noncomputable def onePointApprox : OnePoint F → F → ℝ
  | ∞, β => (max 1 (W β))⁻¹
  | (a : F), β => min 1 (W (β - a))

@[simp] theorem onePointApprox_infty (β : F) :
    W.onePointApprox ∞ β = (max 1 (W β))⁻¹ := rfl

@[simp] theorem onePointApprox_coe (a β : F) :
    W.onePointApprox (a : OnePoint F) β = min 1 (W (β - a)) := rfl

theorem onePointApprox_nonneg (t : OnePoint F) (β : F) : 0 ≤ W.onePointApprox t β := by
  induction t with
  | infty => exact inv_nonneg.mpr (le_trans zero_le_one (le_max_left _ _))
  | coe a => exact le_min zero_le_one (W.nonneg _)

theorem onePointApprox_le_one (t : OnePoint F) (β : F) : W.onePointApprox t β ≤ 1 := by
  induction t with
  | infty =>
      rw [onePointApprox_infty, inv_le_one₀ (by positivity)]
      exact le_max_left _ _
  | coe a => exact min_le_left _ _

/-- The target `t` moved by the Möbius change of variable `x ↦ (x - c)⁻¹`, which sends `∞` to
`0` and every `a ≠ c` to `(a - c)⁻¹`. -/
def onePointMobius (c : F) : OnePoint F → F
  | ∞ => 0
  | (a : F) => (a - c)⁻¹

@[simp] theorem onePointMobius_infty (c : F) : onePointMobius c (∞ : OnePoint F) = 0 := rfl

@[simp] theorem onePointMobius_coe (c a : F) :
    onePointMobius c (a : OnePoint F) = (a - c)⁻¹ := rfl

/-- The distortion constant of the Möbius change of variable at one target. -/
noncomputable def mobiusConst (c : F) : OnePoint F → ℝ
  | ∞ => 1 + W c
  | (a : F) => max (2 / W (a - c) ^ 2) (2 / min 1 (W (a - c)))

@[simp] theorem mobiusConst_infty (c : F) : W.mobiusConst c (∞ : OnePoint F) = 1 + W c := rfl

@[simp] theorem mobiusConst_coe (c a : F) :
    W.mobiusConst c (a : OnePoint F) = max (2 / W (a - c) ^ 2) (2 / min 1 (W (a - c))) := rfl

/-- Truncation at `1` turns a bounded scaling into a bounded factor. -/
theorem min_one_mul_le {s x : ℝ} (hx : 0 ≤ x) :
    min 1 (s * x) ≤ max 1 s * min 1 x := by
  rcases le_or_gt 1 x with hx1 | hx1
  · rw [min_eq_left hx1, mul_one]
    exact le_trans (min_le_left _ _) (le_max_left _ _)
  · rw [min_eq_right hx1.le]
    exact le_trans (min_le_right _ _) (by nlinarith [le_max_right (1 : ℝ) s])

theorem one_le_mobiusConst {c : F} {t : OnePoint F} (ht : t ≠ (c : OnePoint F)) :
    1 ≤ W.mobiusConst c t := by
  induction t with
  | infty => simp [W.nonneg c]
  | coe a =>
      have hac : a - c ≠ 0 := sub_ne_zero.mpr fun h ↦ ht (by rw [h])
      have hD : 0 < W (a - c) := W.pos hac
      have hm : 0 < min 1 (W (a - c)) := lt_min zero_lt_one hD
      have hm1 : min 1 (W (a - c)) ≤ 1 := min_le_left _ _
      refine le_trans ?_ (le_max_right _ _)
      rw [le_div_iff₀ hm]
      linarith

/-- `min 1 x⁻¹` is `(max 1 x)⁻¹`, which is the junk-free form of the factor at the target `∞`. -/
theorem min_one_inv {x : ℝ} (hx : 0 < x) : min 1 x⁻¹ = (max 1 x)⁻¹ := by
  rcases le_or_gt 1 x with h | h
  · rw [max_eq_right h, min_eq_right (by rwa [inv_le_one₀ hx])]
  · rw [max_eq_left h.le,
      min_eq_left (by rw [le_inv_comm₀ zero_lt_one hx, inv_one]; exact h.le), inv_one]

/-- The translated value is bounded by the original one, up to `1 + |c|`. -/
theorem max_one_le_mul_max_one_sub (c β : F) :
    max 1 (W β) ≤ (1 + W c) * max 1 (W (β - c)) := by
  have h1 : (1 : ℝ) ≤ max 1 (W (β - c)) := le_max_left _ _
  have h2 : W (β - c) ≤ max 1 (W (β - c)) := le_max_right _ _
  have h3 : W β ≤ W (β - c) + W c := by
    calc W β = W (β - c + c) := by ring_nf
      _ ≤ W (β - c) + W c := W.add_le _ _
  have hc : 0 ≤ W c := W.nonneg c
  rcases le_or_gt (W β) 1 with h | h
  · rw [max_eq_left h]
    nlinarith
  · rw [max_eq_right h.le]
    nlinarith

/-- **The Möbius change of variable `x ↦ (x - c)⁻¹` distorts the local factor by a bounded
factor.** This is the whole content of allowing the target `∞`: after the change of variable
every target is finite, and the two sides of the inequality of Roth's theorem move by constants
that do not depend on `β`. -/
theorem min_one_sub_onePointMobius_le {c : F} {t : OnePoint F} (ht : t ≠ (c : OnePoint F))
    {β : F} (hβ : β ≠ c) :
    min 1 (W ((β - c)⁻¹ - onePointMobius c t)) ≤ W.mobiusConst c t * W.onePointApprox t β := by
  have hbc : β - c ≠ 0 := sub_ne_zero.mpr hβ
  have hbc0 : 0 < W (β - c) := W.pos hbc
  induction t with
  | infty =>
      rw [onePointMobius_infty, sub_zero, mobiusConst_infty, onePointApprox_infty, map_inv₀,
        min_one_inv hbc0]
      have hA : (0 : ℝ) < max 1 (W (β - c)) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      have hB : (0 : ℝ) < max 1 (W β) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hA hB, one_mul]
      exact max_one_le_mul_max_one_sub W c β
  | coe a =>
      have hac : a - c ≠ 0 := sub_ne_zero.mpr fun h ↦ ht (by rw [h])
      have hD : 0 < W (a - c) := W.pos hac
      have hm : 0 < min 1 (W (a - c)) := lt_min zero_lt_one hD
      have hm1 : min 1 (W (a - c)) ≤ 1 := min_le_left _ _
      have hmD : min 1 (W (a - c)) ≤ W (a - c) := min_le_right _ _
      rw [onePointMobius_coe, mobiusConst_coe, onePointApprox_coe]
      have hexpr : (β - c)⁻¹ - (a - c)⁻¹ = (a - β) / ((β - c) * (a - c)) := by
        field_simp
        ring
      have hW : W ((β - c)⁻¹ - (a - c)⁻¹) = W (β - a) / (W (β - c) * W (a - c)) := by
        rw [hexpr, map_div₀, map_mul, W.map_sub a β]
      have hsum : W (a - c) ≤ W (β - a) + W (β - c) := by
        calc W (a - c) ≤ W (a - β) + W (β - c) := W.sub_le a β c
          _ = W (β - a) + W (β - c) := by rw [W.map_sub a β]
      rcases le_or_gt (W (a - c) / 2) (W (β - c)) with hcase | hcase
      · -- `β` is not close to `c`: the denominator is bounded below
        have hden : W (a - c) ^ 2 / 2 ≤ W (β - c) * W (a - c) := by nlinarith
        have hfac : (0 : ℝ) ≤ 2 / W (a - c) ^ 2 * W (β - a) :=
          mul_nonneg (div_pos two_pos (pow_pos hD 2)).le (W.nonneg _)
        have hle : W ((β - c)⁻¹ - (a - c)⁻¹) ≤ 2 / W (a - c) ^ 2 * W (β - a) := by
          rw [hW, div_le_iff₀ (mul_pos hbc0 hD)]
          have hstep : 2 / W (a - c) ^ 2 * W (β - a) * (W (a - c) ^ 2 / 2)
              ≤ 2 / W (a - c) ^ 2 * W (β - a) * (W (β - c) * W (a - c)) :=
            mul_le_mul_of_nonneg_left hden hfac
          have heq : 2 / W (a - c) ^ 2 * W (β - a) * (W (a - c) ^ 2 / 2) = W (β - a) := by
            field_simp
          linarith
        calc min 1 (W ((β - c)⁻¹ - (a - c)⁻¹))
            ≤ min 1 (2 / W (a - c) ^ 2 * W (β - a)) := min_le_min le_rfl hle
          _ ≤ max 1 (2 / W (a - c) ^ 2) * min 1 (W (β - a)) := min_one_mul_le (W.nonneg _)
          _ ≤ max (2 / W (a - c) ^ 2) (2 / min 1 (W (a - c))) * min 1 (W (β - a)) := by
              refine mul_le_mul_of_nonneg_right ?_ (le_min zero_le_one (W.nonneg _))
              refine max_le (le_trans ?_ (le_max_right _ _)) (le_max_left _ _)
              rw [le_div_iff₀ hm]
              linarith
      · -- `β` is close to `c`, hence far from `a`
        have hfar : W (a - c) / 2 < W (β - a) := by linarith
        have hlow : min 1 (W (a - c)) / 2 ≤ min 1 (W (β - a)) := by
          refine le_min (by linarith) (by linarith)
        have hC : 2 / min 1 (W (a - c))
            ≤ max (2 / W (a - c) ^ 2) (2 / min 1 (W (a - c))) := le_max_right _ _
        have hpos : (0 : ℝ) < 2 / min 1 (W (a - c)) := by positivity
        calc min 1 (W ((β - c)⁻¹ - (a - c)⁻¹)) ≤ 1 := min_le_left _ _
          _ = 2 / min 1 (W (a - c)) * (min 1 (W (a - c)) / 2) := by field_simp
          _ ≤ max (2 / W (a - c) ^ 2) (2 / min 1 (W (a - c))) * min 1 (W (β - a)) :=
              mul_le_mul hC hlow (by linarith) (le_trans hpos.le hC)

end AbsoluteValue


namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

open AbsoluteValue

/-- **One absolute value of `F` over every place of `K`, as a single function.** Roth's theorem
takes the extension `w` as a function on all absolute values of `K`, and only its values on `S`
matter; Layer 0.1 supplies one over every place, and this packages the choices. -/
theorem exists_liesOver_fun :
    ∃ w : AbsoluteValue K ℝ → AbsoluteValue F ℝ,
      (∀ v : InfinitePlace K, (w v.1).LiesOver v.1) ∧
        ∀ v : FinitePlace K, (w v.1).LiesOver v.1 := by
  classical
  have hne : Nonempty (AbsoluteValue F ℝ) := ⟨(Classical.arbitrary (InfinitePlace F)).1⟩
  have key : ∀ u : AbsoluteValue K ℝ, ∃ x : AbsoluteValue F ℝ,
      ((∃ v : InfinitePlace K, v.1 = u) ∨ ∃ v : FinitePlace K, v.1 = u) → x.LiesOver u := by
    intro u
    by_cases hu : (∃ v : InfinitePlace K, v.1 = u) ∨ ∃ v : FinitePlace K, v.1 = u
    · rcases hu with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · obtain ⟨x, hx⟩ := exists_liesOver_infinitePlace (F := F) v
        exact ⟨x.1, fun _ ↦ hx⟩
      · obtain ⟨x, hx⟩ := exists_liesOver_finitePlace (F := F) v
        exact ⟨x, fun _ ↦ hx⟩
    · exact ⟨Classical.arbitrary _, fun hc ↦ absurd hc hu⟩
  choose g hg using key
  exact ⟨g, fun v ↦ hg v.1 (Or.inl ⟨v, rfl⟩), fun v ↦ hg v.1 (Or.inr ⟨v, rfl⟩)⟩

/-- **Layer 3.3: Roth's theorem with targets in `OnePoint F`.** -/
theorem finite_setOf_prod_onePointApprox_le (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → OnePoint F) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | (∏ v ∈ Sinf, (w v.1).onePointApprox (α v.1) (algebraMap K F β) ^ v.mult) *
        ∏ v ∈ Sfin, (w v.1).onePointApprox (α v.1) (algebraMap K F β)
      ≤ mulHeight₁ β ^ (-κ)}.Finite := by
  classical
  -- a base point of the Möbius change of variable that is none of the targets
  obtain ⟨c, hc⟩ : ∃ c : K, ∀ v : AbsoluteValue K ℝ,
      ((∃ u ∈ Sinf, u.1 = v) ∨ ∃ u ∈ Sfin, u.1 = v) →
      α v ≠ ((algebraMap K F c : F) : OnePoint F) := by
    set T : Set (OnePoint F) := ((fun u : InfinitePlace K ↦ α u.1) '' (Sinf : Set _))
      ∪ ((fun u : FinitePlace K ↦ α u.1) '' (Sfin : Set _)) with hTdef
    have hT : T.Finite := (Sinf.finite_toSet.image _).union (Sfin.finite_toSet.image _)
    set g : K → OnePoint F := fun x ↦ ((algebraMap K F x : F) : OnePoint F) with hgdef
    have hg : Function.Injective g := fun x y h ↦
      (algebraMap K F).injective (OnePoint.coe_injective h)
    have hpre : (g ⁻¹' T).Finite := Set.Finite.preimage hg.injOn hT
    obtain ⟨c, hcmem⟩ := hpre.infinite_compl.nonempty
    refine ⟨c, fun v hv hcon ↦ hcmem ?_⟩
    rcases hv with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact Or.inl ⟨u, hu, hcon⟩
    · exact Or.inr ⟨u, hu, hcon⟩
  set c' : F := algebraMap K F c with hc'def
  set α' : AbsoluteValue K ℝ → F := fun u ↦ onePointMobius c' (α u) with hα'def
  -- the constants
  set Cfun : AbsoluteValue K ℝ → ℝ := fun u ↦ (w u).mobiusConst c' (α u) with hCfundef
  set Ctot : ℝ := (∏ v ∈ Sinf, Cfun v.1 ^ v.mult) * ∏ v ∈ Sfin, Cfun v.1 with hCtotdef
  have hCfun1 : ∀ v : AbsoluteValue K ℝ,
      ((∃ u ∈ Sinf, u.1 = v) ∨ ∃ u ∈ Sfin, u.1 = v) → 1 ≤ Cfun v :=
    fun v hv ↦ one_le_mobiusConst _ (hc v hv)
  have hCtot1 : 1 ≤ Ctot := by
    refine one_le_mul_of_one_le_of_one_le ?_ ?_
    · exact Finset.one_le_prod₀ fun u hu ↦ one_le_pow₀ (hCfun1 u.1 (Or.inl ⟨u, hu, rfl⟩))
    · exact Finset.one_le_prod₀ fun u hu ↦ hCfun1 u.1 (Or.inr ⟨u, hu, rfl⟩)
  set M : ℝ := 2 ^ totalWeight K * mulHeight₁ c with hMdef
  have hM1 : 1 ≤ M := by
    refine one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_mulHeight₁ c)
  set κ₁ : ℝ := (κ + 2) / 2 with hκ₁def
  have hκ₁2 : 2 < κ₁ := by rw [hκ₁def]; linarith
  have hκ₁κ : κ₁ < κ := by rw [hκ₁def]; linarith
  set C₂ : ℝ := Ctot * M ^ κ with hC₂def
  have hC₂1 : 1 ≤ C₂ := by
    refine one_le_mul_of_one_le_of_one_le hCtot1 (Real.one_le_rpow hM1 (by linarith))
  set B : ℝ := C₂ ^ (κ - κ₁)⁻¹ with hBdef
  -- the two finite sets the solutions land in
  have hroth := finite_setOf_prod_min_one_le Sinf Sfin w hwInf hwFin α' hκ₁2
  have hnorth := finite_setOfPred_mulHeight₁_le (K := K) B
  refine Set.Finite.subset (((hroth.union hnorth).image fun γ : K ↦ c + γ⁻¹).union
    (Set.finite_singleton c)) ?_
  intro β hβ
  rw [Set.mem_ofPred_eq] at hβ
  by_cases hβc : β = c
  · exact Or.inr hβc
  refine Or.inl ⟨(β - c)⁻¹, ?_, ?_⟩
  swap
  · have : ((β - c)⁻¹)⁻¹ = β - c := inv_inv _
    simp only []
    rw [this]
    ring
  -- the change of variable
  have hbc : β - c ≠ 0 := sub_ne_zero.mpr hβc
  have hbc' : algebraMap K F β ≠ c' := fun h ↦ hβc ((algebraMap K F).injective h)
  set γ : K := (β - c)⁻¹ with hγdef
  have hmapγ : algebraMap K F γ = (algebraMap K F β - c')⁻¹ := by
    rw [hγdef, map_inv₀, map_sub, hc'def]
  -- the local comparison at every place of `S`
  have hstep : ∀ v : AbsoluteValue K ℝ, ((∃ u ∈ Sinf, u.1 = v) ∨ ∃ u ∈ Sfin, u.1 = v) →
      min 1 (w v (algebraMap K F γ - α' v))
        ≤ Cfun v * (w v).onePointApprox (α v) (algebraMap K F β) := by
    intro v hv
    rw [hmapγ, hα'def, hCfundef]
    exact min_one_sub_onePointMobius_le (w v) (hc v hv) hbc'
  have hnn : ∀ v : AbsoluteValue K ℝ, 0 ≤ min 1 (w v (algebraMap K F γ - α' v)) :=
    fun v ↦ le_min zero_le_one ((w v).nonneg _)
  have hA : (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F γ - α' v.1)) ^ v.mult)
      ≤ (∏ v ∈ Sinf, Cfun v.1 ^ v.mult) *
        ∏ v ∈ Sinf, (w v.1).onePointApprox (α v.1) (algebraMap K F β) ^ v.mult := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun u _ ↦ pow_nonneg (hnn u.1) _) fun u hu ↦ ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (hnn u.1) (hstep u.1 (Or.inl ⟨u, hu, rfl⟩)) _
  have hBb : (∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F γ - α' v.1)))
      ≤ (∏ v ∈ Sfin, Cfun v.1) *
        ∏ v ∈ Sfin, (w v.1).onePointApprox (α v.1) (algebraMap K F β) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun u _ ↦ hnn u.1) fun u hu ↦ hstep u.1 (Or.inr ⟨u, hu, rfl⟩)
  -- the height comparison
  have hheight : mulHeight₁ γ ≤ M * mulHeight₁ β := by
    rw [hγdef, mulHeight₁_inv, hMdef]
    calc mulHeight₁ (β - c) ≤ 2 ^ totalWeight K * mulHeight₁ β * mulHeight₁ c :=
          mulHeight₁_sub_le β c
      _ = 2 ^ totalWeight K * mulHeight₁ c * mulHeight₁ β := by ring
  have hβpos : (0 : ℝ) < mulHeight₁ β := mulHeight₁_pos β
  have hγpos : (0 : ℝ) < mulHeight₁ γ := mulHeight₁_pos γ
  have hM0 : (0 : ℝ) < M := by linarith
  have hMκ : (0 : ℝ) < M ^ κ := Real.rpow_pos_of_pos hM0 κ
  have hγκ : (0 : ℝ) < mulHeight₁ γ ^ κ := Real.rpow_pos_of_pos hγpos κ
  have hβκ : (0 : ℝ) < mulHeight₁ β ^ κ := Real.rpow_pos_of_pos hβpos κ
  have hrpow : mulHeight₁ β ^ (-κ) ≤ M ^ κ * mulHeight₁ γ ^ (-κ) := by
    have h1 : mulHeight₁ γ / M ≤ mulHeight₁ β := by
      rw [div_le_iff₀ hM0]
      linarith [hheight]
    have h2 : (mulHeight₁ γ / M) ^ κ ≤ mulHeight₁ β ^ κ :=
      Real.rpow_le_rpow (by positivity) h1 (by linarith)
    rw [Real.div_rpow hγpos.le hM0.le, div_le_iff₀ hMκ] at h2
    have e1 : M ^ κ * (mulHeight₁ γ ^ κ)⁻¹ - (mulHeight₁ β ^ κ)⁻¹
        = (M ^ κ * mulHeight₁ β ^ κ - mulHeight₁ γ ^ κ)
          / (mulHeight₁ γ ^ κ * mulHeight₁ β ^ κ) := by
      field_simp
    have e2 : (0 : ℝ) ≤ (M ^ κ * mulHeight₁ β ^ κ - mulHeight₁ γ ^ κ)
        / (mulHeight₁ γ ^ κ * mulHeight₁ β ^ κ) :=
      div_nonneg (by nlinarith) (mul_nonneg hγκ.le hβκ.le)
    rw [Real.rpow_neg hβpos.le, Real.rpow_neg hγpos.le]
    linarith
  -- put the two together
  by_cases hbig : mulHeight₁ γ ≤ B
  · exact Or.inr hbig
  refine Or.inl ?_
  rw [Set.mem_ofPred_eq]
  push Not at hbig
  have hC₂le : C₂ ≤ mulHeight₁ γ ^ (κ - κ₁) := by
    have hBκ : B ^ (κ - κ₁) = C₂ := by
      rw [hBdef, Real.rpow_inv_rpow (by linarith) (by linarith)]
    rw [← hBκ]
    exact Real.rpow_le_rpow (by positivity) hbig.le (by linarith)
  calc (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F γ - α' v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F γ - α' v.1))
      ≤ Ctot * ((∏ v ∈ Sinf, (w v.1).onePointApprox (α v.1) (algebraMap K F β) ^ v.mult) *
        ∏ v ∈ Sfin, (w v.1).onePointApprox (α v.1) (algebraMap K F β)) := by
        rw [hCtotdef]
        have h0 : (0 : ℝ) ≤ ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F γ - α' v.1)) :=
          Finset.prod_nonneg fun u _ ↦ hnn u.1
        have h1 : (0 : ℝ) ≤ (∏ v ∈ Sinf, Cfun v.1 ^ v.mult) *
            ∏ v ∈ Sinf, (w v.1).onePointApprox (α v.1) (algebraMap K F β) ^ v.mult := by
          refine mul_nonneg (Finset.prod_nonneg fun u hu ↦ ?_) (Finset.prod_nonneg fun u _ ↦ ?_)
          · exact pow_nonneg (le_trans zero_le_one (hCfun1 u.1 (Or.inl ⟨u, hu, rfl⟩))) _
          · exact pow_nonneg ((w u.1).onePointApprox_nonneg _ _) _
        calc (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F γ - α' v.1)) ^ v.mult) *
              ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F γ - α' v.1))
            ≤ ((∏ v ∈ Sinf, Cfun v.1 ^ v.mult) *
                ∏ v ∈ Sinf, (w v.1).onePointApprox (α v.1) (algebraMap K F β) ^ v.mult) *
              ((∏ v ∈ Sfin, Cfun v.1) *
                ∏ v ∈ Sfin, (w v.1).onePointApprox (α v.1) (algebraMap K F β)) :=
              mul_le_mul hA hBb h0 h1
          _ = _ := by ring
    _ ≤ Ctot * mulHeight₁ β ^ (-κ) := by
        refine mul_le_mul_of_nonneg_left hβ (by linarith)
    _ ≤ Ctot * (M ^ κ * mulHeight₁ γ ^ (-κ)) :=
        mul_le_mul_of_nonneg_left hrpow (by linarith)
    _ = C₂ * mulHeight₁ γ ^ (-κ) := by rw [hC₂def]; ring
    _ ≤ mulHeight₁ γ ^ (κ - κ₁) * mulHeight₁ γ ^ (-κ) :=
        mul_le_mul_of_nonneg_right hC₂le (Real.rpow_nonneg hγpos.le _)
    _ = mulHeight₁ γ ^ (-κ₁) := by
        rw [← Real.rpow_add hγpos]
        ring_nf

/-! ### Acceptance criteria -/

/-- **Conformance: Layer 3.2 is the case of finite targets.** With every target in `F`, the
statement above is Roth's theorem as Layer 3.2 proves it. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
      ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1))
        ≤ mulHeight₁ β ^ (-κ)}.Finite := by
  have h := finite_setOf_prod_onePointApprox_le Sinf Sfin w hwInf hwFin
    (fun u ↦ ((α u : F) : OnePoint F)) hκ
  simpa using h

/-- **The factor at `∞` is junk-free at `0`, where the roadmap's reading is not.** The value of
the factor at `β = 0` is `1`; `min 1 (W 0)⁻¹` is `0`, because `(0 : ℝ)⁻¹ = 0`. -/
example (W : AbsoluteValue F ℝ) : W.onePointApprox ∞ 0 = 1 ∧ min 1 (W 0)⁻¹ = 0 := by
  constructor
  · rw [AbsoluteValue.onePointApprox_infty, map_zero, max_eq_left zero_le_one, inv_one]
  · rw [map_zero, inv_zero, min_eq_right zero_le_one]

/-- **Rejection test: `∞` is not the target `0`.** At a `β` of size `2` the factor at the target
`∞` is `1 / 2` and the factor at the target `0` is `1`, so the two targets are not
interchangeable and the `OnePoint` in the statement is not decoration. -/
example (W : AbsoluteValue F ℝ) (β : F) (hβ : W β = 2) :
    W.onePointApprox ∞ β = 1 / 2 ∧ W.onePointApprox ((0 : F) : OnePoint F) β = 1 := by
  constructor
  · rw [AbsoluteValue.onePointApprox_infty, hβ, max_eq_right one_le_two]
    norm_num
  · rw [AbsoluteValue.onePointApprox_coe, sub_zero, hβ, min_eq_left one_le_two]

end NumberField

end
