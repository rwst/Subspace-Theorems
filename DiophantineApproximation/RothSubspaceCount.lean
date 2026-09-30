/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.RothIntervals
public import DiophantineApproximation.SubspaceIntervals

-- Used only inside proofs.
import DiophantineApproximation.ApproxProd
import DiophantineApproximation.LiouvilleInequality
import DiophantineApproximation.ProjectiveTarget
import DiophantineApproximation.SAdicHeight
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# Roth's interval result fed to Evertse's covering, for two variables

**Layer 3.7 into Layer 9.4.** For a normalized system (Evertse's (2.4)) in two variables, the
solutions of large absolute affine height lie in at most

```text
s + 1 + m (N + s).choose s · (1 + log (3 r s M) / log (1 + δ / 4))
```

proper subspaces of `K²` (`NumberField.exists_finset_submodule_of_card_eq_two`), where
`s = #(places of the system)`, `r = [F : K]`, and `m`, `M`, `N` are Roth's chain length, ratio
and class size at the exponent `2 + δ / 2` (Layer 3.7). The count depends on `δ`, `s` and `r`
alone. It is Roth's interval result (Layer 3.7, `RothIntervals.lean`) turned into a count of
subspaces by Evertse's covering (Layer 9.4), which is what the roadmap asks of 9.4's input.

The link has three steps.

* **The system is Roth's inequality.** At each place one form attains the normalized local degree
  `s(v)`; the other, the *small* form, carries the weight: the exponents of the small forms sum to
  at most `-1 - δ`. Writing `β = x₁ / x₀`, the product over the places of the small forms, divided
  by the local sizes of `x`, is at most a constant times `H(β) ^ (-2 - δ)`, because the local sizes
  of an `S`-integral point multiply to at least its height. The zero of the small form at each
  place is a target in `OnePoint F` (Layer 3.4's `formRoot`), so `β` solves Roth's inequality
  with targets at infinity allowed (Layer 3.3) at the exponent `2 + δ`.
* **The affine height is a power of the height of `β`.** The point `x` and its multiples by
  integers have the same `β`, and the system bounds the multiplier: the small forms at `x` are at
  least `H(β) ^ (-r)` each, by Liouville's inequality at one place (Layer 0.4), while their product
  is at most a constant times `H(x) ^ (-1 - δ)` in the affine height. So
  `H(x) ≤ C H(β) ^ (r s)`, off the lines where a small form vanishes.
* **Intervals, then subspaces.** Roth's interval result with targets at infinity
  (`NumberField.exists_forall_mem_interval_of_prod_onePointApprox_le`) puts the log heights of the
  `β` in few windows `[t - e, M t + e)`; the comparison of heights moves them to windows
  `[Q, Q ^ ω)` of the affine height with `ω = 3 r s M`, and 9.4 covers them.

## Main results

* `NumberField.systemPlace_injective`: the places of a system are distinct absolute values.
* `NumberField.exists_finset_submodule_of_card_eq_two`: **the large solutions of a normalized
  system in two variables lie in a number of proper subspaces depending on `δ`, `s` and `r`
  alone**, by Roth's interval result and Evertse's covering, above the explicit height
  `NumberField.systemRothThreshold`.
* `NumberField.systemRothThreshold`: that height, a formula in the height bound `H` of the
  coefficients, `δ`, `s` and the degrees.

## Implementation notes

⚠ **The threshold is explicit, and the count is not Evertse's.** The height above which the
count holds is `NumberField.systemRothThreshold s r [F : ℚ] [K : ℚ] δ H`, a formula in the bound
`H` on the absolute heights of the coefficients that `IsNormalizedSystem` carries. With
`G = H ^ [F : ℚ]`, every coefficient has local size in `[G⁻¹, G]` when nonzero (Liouville's
inequality at one place and its upper half), so the constant of each form is at most `4 G ^ 3`,
the product of the system's constants at most `(2 G ^ 2) ^ s` through the determinant, the lower
bounds of the height comparison at least `(2 ^ [F : ℚ] G ^ 4)⁻¹`, and the roots of the forms have
height at most `2 log H`. The threshold is `exp (O_{δ, s, r}(log H + 1))`, the shape of Evertse's
`max (2 H, n ^ (2 n / δ))` up to the power. The count depends only on `δ`, the number of places
and `[F : K]`. Evertse's Theorem 2.1 has a bound of shape `δ⁻¹ log (…)` from his own interval
result, Theorem 3.1, which this roadmap does not prove.
Roth's parameters are far worse, and the point is the link, not the bound.

⚠ **The lines where a small form vanishes are counted separately.** On such a line the affine
height is not bounded by the height of `β`, and the line can hold infinitely many solutions of
unbounded height, all in one subspace. There is one per place, and one more, `x₀ = 0`, where
`β` is not defined: `s + 1` subspaces, added to 9.4's.

⚠ **No split over the choice of form.** Layer 3.4 splits the solutions over the `2 ^ s` choices of
a small form at each place. Under the normalization the small form is determined by the
exponents — the one that does not attain `s(v)` — so one Roth inequality serves every solution.

## References

J.-H. Evertse, *On the Quantitative Subspace Theorem*, Zap. Nauchn. Sem. POMI **377** (2010),
217–240 (arXiv:1008.2268), §2 and the proof of Theorem 2.1. E. Bombieri and W. Gubler, *Heights
in Diophantine Geometry*, Cambridge University Press (2006), §6.5.7.

This links Layers 3.7 and 9.4 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height IsDedekindDomain Module

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- **The places of a system are distinct absolute values**: two infinite places, or two primes,
with the same absolute value are equal, and an infinite place is never a finite one. -/
theorem systemPlace_injective (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (systemPlace S) := by
  rintro (v | v) (v' | v') h <;> simp only [systemPlace] at h
  · exact congrArg Sum.inl (Subtype.ext h)
  · exact absurd h (InfinitePlace.val_ne_finitePlace_val v (FinitePlace.mk v'.1))
  · exact absurd h.symm (InfinitePlace.val_ne_finitePlace_val v' (FinitePlace.mk v.1))
  · exact congrArg Sum.inr (Subtype.ext (FinitePlace.mk_injective (Subtype.ext h)))

/-- A product over the places of a system, split into the infinite places and `S`. -/
private theorem prod_systemPlace (S : Finset (HeightOneSpectrum (𝓞 K)))
    (G : AbsoluteValue K ℝ → ℝ) :
    ∏ p : InfinitePlace K ⊕ S, G (systemPlace S p) ^ systemMult S p
      = (∏ v : InfinitePlace K, G v.1 ^ v.mult) * ∏ v ∈ S, G (FinitePlace.mk v).1 := by
  rw [Fintype.prod_sum_type, ← Finset.prod_coe_sort S]
  simp only [systemPlace, systemMult, pow_one]

open scoped Classical in
/-- A product over the finite places of `S`, read on the primes. -/
private theorem prod_image_mk (S : Finset (HeightOneSpectrum (𝓞 K)))
    (G : AbsoluteValue K ℝ → ℝ) :
    ∏ v ∈ S.image FinitePlace.mk, G v.1 = ∏ v ∈ S, G (FinitePlace.mk v).1 :=
  Finset.prod_image fun _ _ _ _ h ↦ FinitePlace.mk_injective h

/-- **Liouville's inequality at one place of a system** (Layer 0.4 on a single place). -/
private theorem inv_le_min_one_pow_systemMult (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (p : InfinitePlace K ⊕ S)
    (hp : (w (systemPlace S p)).LiesOver (systemPlace S p)) {α : F} {β : K}
    (hne : algebraMap K F β ≠ α) :
    (2 ^ finrank ℚ F * mulHeight₁ α * mulHeight₁ β ^ finrank K F)⁻¹
      ≤ min 1 (w (systemPlace S p) (algebraMap K F β - α)) ^ systemMult S p := by
  classical
  obtain ⟨w₀, h₀inf, h₀fin⟩ := exists_liesOver_fun (K := K) (F := F)
  rcases p with v | v
  · have h := liouville_inequality {v} ∅ (fun u ↦ if u = v then w v.1 else w₀ u.1)
      (fun u ↦ by
        by_cases h : u = v
        · simp only [h, ↓reduceIte]; exact hp
        · simp only [h, ↓reduceIte]; exact h₀inf u)
      (fun u ↦ w₀ u.1) h₀fin hne
    simpa [systemPlace, systemMult] using h
  · have h := liouville_inequality ∅ {FinitePlace.mk v.1} (fun u ↦ w₀ u.1) h₀inf
      (fun u ↦ if u = FinitePlace.mk v.1 then w (FinitePlace.mk v.1).1 else w₀ u.1)
      (fun u ↦ by
        by_cases h : u = FinitePlace.mk v.1
        · simp only [h, ↓reduceIte]; exact hp
        · simp only [h, ↓reduceIte]; exact h₀fin u) hne
    simpa [systemPlace, systemMult] using h

/-- **A local size at a place of a system is at most the height** (Layer 0.4 on a single
place, upper half). -/
private theorem apply_le_mulHeight₁_systemPlace (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (p : InfinitePlace K ⊕ S)
    (hp : (w (systemPlace S p)).LiesOver (systemPlace S p)) (x : F) :
    w (systemPlace S p) x ≤ mulHeight₁ x := by
  rcases p with v | v
  · have : (w v.1).LiesOver v.1 := hp
    exact (le_max_left _ _).trans
      (max_apply_one_le_mulHeight₁_of_liesOver_infinitePlace v (w v.1) x)
  · have : (w (FinitePlace.mk v.1).1).LiesOver (FinitePlace.mk v.1).1 := hp
    exact (le_max_left _ _).trans (max_apply_one_le_mulHeight₁_of_liesOver_finitePlace
      (FinitePlace.mk v.1) (w (FinitePlace.mk v.1).1) x)

/-- **A nonzero local size at a place of a system is at least the reciprocal of the height**
(Liouville's inequality at one place). -/
private theorem inv_mulHeight₁_le_systemPlace (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (p : InfinitePlace K ⊕ S)
    (hp : (w (systemPlace S p)).LiesOver (systemPlace S p)) {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ w (systemPlace S p) x := by
  rcases p with v | v
  · exact (inv_mulHeight₁_le_min_one_of_infinitePlace v hp hx).trans (min_le_right _ _)
  · exact (inv_mulHeight₁_le_min_one_of_finitePlace (FinitePlace.mk v.1) hp hx).trans
      (min_le_right _ _)

omit [NumberField K] in
/-- The multiplicity of a place of a system is at most `2`. -/
private theorem systemMult_le_two (S : Finset (HeightOneSpectrum (𝓞 K))) (p : InfinitePlace K ⊕ S) :
    systemMult S p ≤ 2 := by
  rcases p with v | v
  · change v.mult ≤ 2
    unfold InfinitePlace.mult
    split_ifs <;> norm_num
  · exact one_le_two

omit [NumberField K] [NumberField F] [Algebra K F] in
/-- **The constant of a form, bounded by bounds on its coefficients.** If both coefficients of a
nonzero form have local size at most `G`, and each nonzero one at least `G⁻¹`, then its constant
is at most `4 G ^ 3`. -/
private theorem formConst_le_of_bounds {W : AbsoluteValue F ℝ} {a b : F} {G : ℝ} (hG1 : 1 ≤ G)
    (hab : a ≠ 0 ∨ b ≠ 0) (hua : W a ≤ G) (hla : a ≠ 0 → G⁻¹ ≤ W a)
    (hlb : b ≠ 0 → G⁻¹ ≤ W b) : W.formConst a b ≤ 4 * G ^ 3 := by
  have hG0 : 0 < G := by linarith
  have hG3 : G ≤ G ^ 3 := le_self_pow₀ hG1 (by norm_num)
  by_cases hb : b = 0
  · have ha := hab.resolve_right (not_not.mpr hb)
    have h1 : (W a)⁻¹ ≤ G := by rw [inv_le_comm₀ (W.pos ha) hG0]; exact hla ha
    simp only [AbsoluteValue.formConst, hb, ↓reduceIte]
    linarith
  · have hWb : 0 < W b := W.pos hb
    have h1 : (W b)⁻¹ ≤ G := by rw [inv_le_comm₀ hWb hG0]; exact hlb hb
    have h2 : 0 ≤ (W b)⁻¹ := (inv_pos.mpr hWb).le
    simp only [AbsoluteValue.formConst, hb, ↓reduceIte, map_div₀]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have h4 : W a * (W b)⁻¹ ≤ G * G := mul_le_mul hua h1 h2 hG0.le
    have h5 : (2 + 2 * (W a * (W b)⁻¹)) * (W b)⁻¹ ≤ (2 + 2 * (G * G)) * G :=
      mul_le_mul (by linarith) h1 h2 (by positivity)
    nlinarith

omit [NumberField K] [Algebra K F] in
/-- The height of the root `-a / b` of a form is at most the product of the heights of its
coefficients. -/
private theorem mulHeight₁_neg_div_le {a b : F} {G : ℝ} (hHa : mulHeight₁ a ≤ G)
    (hHb : mulHeight₁ b ≤ G) : mulHeight₁ (-(a / b)) ≤ G ^ 2 := by
  rw [mulHeight₁_neg, div_eq_mul_inv]
  calc _ ≤ mulHeight₁ a * mulHeight₁ b⁻¹ := mulHeight₁_mul_le _ _
    _ ≤ G * G := by
        rw [mulHeight₁_inv]
        exact mul_le_mul hHa hHb (mulHeight₁_pos _).le ((mulHeight₁_pos _).le.trans hHa)
    _ = G ^ 2 := by ring

omit [NumberField K] [Algebra K F] in
open Classical in
/-- **The lower bound for a small form at a point of Roth's inequality, bounded by heights.** -/
private theorem inv_le_kap_of_bounds {W : AbsoluteValue F ℝ} {a b : F} {G : ℝ} {m : ℕ}
    (hG1 : 1 ≤ G) (hm : m ≤ 2) (hab : a ≠ 0 ∨ b ≠ 0) (hHa : mulHeight₁ a ≤ G)
    (hHb : mulHeight₁ b ≤ G) (hla : a ≠ 0 → G⁻¹ ≤ W a) (hlb : b ≠ 0 → G⁻¹ ≤ W b) :
    (2 ^ finrank ℚ F * G ^ 4)⁻¹ ≤
      if b = 0 then W a ^ m else W b ^ m * (2 ^ finrank ℚ F * mulHeight₁ (-(a / b)))⁻¹ := by
  have hG0 : 0 < G := by linarith
  have hGi : G⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hG1
  have hGi0 : 0 ≤ G⁻¹ := (inv_pos.mpr hG0).le
  have h2F : (1 : ℝ) ≤ 2 ^ finrank ℚ F := one_le_pow₀ one_le_two
  split_ifs with hb
  · have ha := hab.resolve_right (not_not.mpr hb)
    calc (2 ^ finrank ℚ F * G ^ 4)⁻¹ ≤ G⁻¹ ^ 2 := by
          rw [inv_pow, inv_le_inv₀ (by positivity) (by positivity)]
          calc G ^ 2 ≤ G ^ 4 := pow_le_pow_right₀ hG1 (by norm_num)
            _ ≤ _ := le_mul_of_one_le_left (by positivity) h2F
      _ ≤ G⁻¹ ^ m := pow_le_pow_of_le_one hGi0 hGi hm
      _ ≤ _ := pow_le_pow_left₀ hGi0 (hla ha) _
  · have hpos : 0 < 2 ^ finrank ℚ F * mulHeight₁ (-(a / b)) := by
      have := mulHeight₁_pos (-(a / b)); positivity
    calc (2 ^ finrank ℚ F * G ^ 4)⁻¹ = G⁻¹ ^ 2 * (2 ^ finrank ℚ F * G ^ 2)⁻¹ := by
          field_simp
      _ ≤ W b ^ m * (2 ^ finrank ℚ F * mulHeight₁ (-(a / b)))⁻¹ := by
          refine mul_le_mul ?_ ?_ (by positivity) (pow_nonneg (W.nonneg _) _)
          · exact (pow_le_pow_of_le_one hGi0 hGi hm).trans (pow_le_pow_left₀ hGi0 (hlb hb) _)
          · rw [inv_le_inv₀ (by positivity) hpos]
            exact mul_le_mul_of_nonneg_left (mulHeight₁_neg_div_le hHa hHb) (by positivity)

omit [NumberField K] [Algebra K F] in
/-- **The root of a form has absolute height at most `2 log H`** when both coefficients have
relative height at most `H ^ [F : ℚ]`. -/
private theorem onePointHeight_formRoot_le {a b : F} {H : ℝ} (hH1 : 1 ≤ H)
    (hHa : mulHeight₁ a ≤ H ^ finrank ℚ F) (hHb : mulHeight₁ b ≤ H ^ finrank ℚ F) :
    onePointHeight (OnePoint.formRoot a b) ≤ 2 * Real.log H := by
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH1
  rw [OnePoint.formRoot]
  split_ifs with hb
  · rw [onePointHeight_infty]; linarith
  · have hnF : (0 : ℝ) < finrank ℚ F := by exact_mod_cast Module.finrank_pos
    rw [onePointHeight_coe, absLogHeight₁_eq_inv_mul, inv_mul_le_iff₀ hnF]
    calc _ ≤ Real.log ((H ^ finrank ℚ F) ^ 2) :=
          Real.log_le_log (mulHeight₁_pos _) (mulHeight₁_neg_div_le hHa hHb)
      _ = _ := by rw [Real.log_pow, Real.log_pow, Nat.cast_ofNat]; ring

omit [NumberField K] [NumberField F] [Algebra K F] in
/-- A product of powers of at most `2` of factors in `[0, X]`, with `X ≥ 1`. -/
private theorem prod_pow_le_of_le {P : Type*} [Fintype P] {f : P → ℝ} {m : P → ℕ} {X : ℝ}
    (hX : 1 ≤ X) (hf0 : ∀ p, 0 ≤ f p) (hf : ∀ p, f p ≤ X) (hm : ∀ p, m p ≤ 2) :
    ∏ p, f p ^ m p ≤ (X ^ 2) ^ Fintype.card P := by
  rw [← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun p _ ↦ pow_nonneg (hf0 p) _) fun p _ ↦
    (pow_le_pow_left₀ (hf0 p) (hf p) _).trans (pow_le_pow_right₀ hX (hm p))

omit [NumberField K] [NumberField F] [Algebra K F] in
/-- The logarithm of the constant of Roth's inequality, bounded by the coefficient bound `G`. -/
private theorem log_max_mul_le {Γ Cs G : ℝ} {s : ℕ} (hG1 : 1 ≤ G) (hCs0 : 0 ≤ Cs)
    (hΓ : Γ ≤ ((4 * G ^ 3) ^ 2) ^ s) (hCs : Cs ≤ (2 * G ^ 2) ^ s) :
    Real.log (max (Γ * Cs) 1) ≤ s * (Real.log 32 + 8 * Real.log G) := by
  have hG0 : 0 < G := by linarith
  have h32 : (1 : ℝ) ≤ 32 * G ^ 8 := by nlinarith [one_le_pow₀ (n := 8) hG1]
  have hle : max (Γ * Cs) 1 ≤ (32 * G ^ 8) ^ s := by
    refine max_le ?_ (one_le_pow₀ h32)
    calc Γ * Cs ≤ ((4 * G ^ 3) ^ 2) ^ s * (2 * G ^ 2) ^ s :=
          mul_le_mul hΓ hCs hCs0 (by positivity)
      _ = (32 * G ^ 8) ^ s := by rw [← mul_pow]; ring
  calc _ ≤ Real.log ((32 * G ^ 8) ^ s) :=
        Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _)) hle
    _ = _ := by
        rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow,
          Nat.cast_ofNat]

omit [NumberField K] [NumberField F] [Algebra K F] in
/-- The logarithm of the ratio of the constants of the height comparison, bounded by the
coefficient bound `G`. -/
private theorem log_div_le {Cs κc G : ℝ} {s n : ℕ} (hG1 : 1 ≤ G) (hCs0 : 0 < Cs)
    (hκc0 : 0 < κc) (hCs : Cs ≤ (2 * G ^ 2) ^ s) (hκc : ((2 ^ n * G ^ 4) ^ s)⁻¹ ≤ κc) :
    Real.log (Cs / κc) ≤ s * ((n + 1) * Real.log 2 + 6 * Real.log G) := by
  have hG0 : 0 < G := by linarith
  have hle : Cs / κc ≤ (2 * G ^ 2) ^ s * (2 ^ n * G ^ 4) ^ s := by
    rw [div_le_iff₀ hκc0]
    calc Cs ≤ (2 * G ^ 2) ^ s := hCs
      _ = (2 * G ^ 2) ^ s * (2 ^ n * G ^ 4) ^ s * ((2 ^ n * G ^ 4) ^ s)⁻¹ := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hκc (by positivity)
  calc Real.log (Cs / κc) ≤ Real.log ((2 * G ^ 2) ^ s * (2 ^ n * G ^ 4) ^ s) :=
        Real.log_le_log (div_pos hCs0 hκc0) hle
    _ = _ := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
          Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity)
            (by positivity), Real.log_pow, Real.log_pow, Real.log_pow, Nat.cast_ofNat,
          Nat.cast_ofNat]
        ring

/-- **The product of the constants of a normalized system in two variables, bounded by the
coefficients**: it is at most `(2 G ^ 2) ^ s` when every coefficient has local size at most `G`,
through the determinant. -/
private theorem systemConst_le_of_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = 2) {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ} {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)}
    {C : InfinitePlace K ⊕ S → ℝ} {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) {G : ℝ} (hG1 : 1 ≤ G)
    (hup : ∀ p i j, w (systemPlace S p) (L (systemPlace S p) i (Pi.single j 1)) ≤ G) :
    systemConst C ≤ (2 * G ^ 2) ^ Fintype.card (InfinitePlace K ⊕ S) := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hdet : ∀ p, w (systemPlace S p) (LinearMap.det (LinearMap.pi (L (systemPlace S p))))
      ≤ 2 * G ^ 2 := by
    intro p
    rw [← LinearMap.det_toMatrix']
    have h := Matrix.det_le (abv := w (systemPlace S p))
      (A := LinearMap.toMatrix' (LinearMap.pi (L (systemPlace S p)))) (x := G) fun i j ↦ by
        rw [LinearMap.toMatrix'_apply, LinearMap.pi_apply]
        exact hup p i j
    rwa [hι, nsmul_eq_mul, Nat.factorial_two, Nat.cast_ofNat] at h
  have h1 := systemConst_pow_le_systemDet hN
  rw [hι] at h1
  have h2 : systemDet S w L ≤ ((2 * G ^ 2) ^ Fintype.card (InfinitePlace K ⊕ S)) ^ 2 := by
    rw [← pow_mul, mul_comm _ 2, pow_mul]
    exact prod_pow_le_of_le (by nlinarith [one_le_pow₀ (n := 2) hG1])
      (fun p ↦ apply_nonneg _ _) hdet (systemMult_le_two S)
  have hC0 : 0 ≤ systemConst C := Finset.prod_nonneg fun p _ ↦ (hN.const_pos p).le
  exact (pow_le_pow_iff_left₀ hC0 (by positivity) two_ne_zero).mp (h1.trans h2)

omit [NumberField F] in
/-- A linear form in two variables is read off its values at the two unit vectors. -/
private theorem apply_eq_of_forall_eq_or {ι : Type*} [DecidableEq ι] {i₀ i₁ : ι} (hne : i₀ ≠ i₁)
    (huniv : ∀ i, i = i₀ ∨ i = i₁) (f : Dual F (ι → F)) (y : ι → F) :
    f y = y i₀ * f (Pi.single i₀ 1) + y i₁ * f (Pi.single i₁ 1) := by
  have hy : y = y i₀ • Pi.single i₀ 1 + y i₁ • Pi.single i₁ 1 := by
    funext j
    rcases huniv j with rfl | rfl
    · simp [hne.symm]
    · simp [hne]
  conv_lhs => rw [hy]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- **The system at its small forms.** For a normalized system in two variables, a choice `σ` of
one form at each place whose exponents sum to at most `-1 - δ`, and a solution `x` with
`x i₀ ≠ 0`, write `β = x i₁ / x i₀`: the product of the small forms is the product of the local
sizes of `x i₀` times that of the values `a + b β` of the forms at `(1, β)`, and it is at most
`∏ C · H(x) ^ (-1 - δ)`; the first factor is at least `1`; and the local sizes of `x` multiply to
at least the height of `β`. -/
private theorem prod_small_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) {i₀ i₁ : ι} (hne : i₀ ≠ i₁)
    (huniv : ∀ i, i = i₀ ∨ i = i₁) (σ : InfinitePlace K ⊕ S → ι)
    (hσ : ∑ p, c p (σ p) ≤ -1 - δ) {x : ι → K} (hx : x ∈ systemSet S w L C c)
    (hx0 : x i₀ ≠ 0) :
    (∏ p, systemPlace S p (x i₀) ^ systemMult S p) *
        ∏ p, w (systemPlace S p) (L (systemPlace S p) (σ p) (Pi.single i₀ 1) +
          L (systemPlace S p) (σ p) (Pi.single i₁ 1) * algebraMap K F (x i₁ / x i₀))
            ^ systemMult S p
        ≤ systemConst C * mulHeightAff x ^ (-(1 + δ)) ∧
      1 ≤ ∏ p, systemPlace S p (x i₀) ^ systemMult S p ∧
      mulHeight₁ (x i₁ / x i₀) ≤ ∏ p, (systemPlace S p (x i₀) *
        max 1 (systemPlace S p (x i₁ / x i₀))) ^ systemMult S p := by
  set β : K := x i₁ / x i₀ with hβdef
  have hxβ : x i₁ = x i₀ * β := by rw [hβdef]; field_simp
  have hlies : ∀ p, (w (systemPlace S p)).LiesOver (systemPlace S p) := by
    rintro (v | v)
    · exact hwInf v
    · exact hwFin v.1 v.2
  have hval : ∀ p, systemValue S w L p (σ p) x = (systemPlace S p (x i₀) *
      w (systemPlace S p) (L (systemPlace S p) (σ p) (Pi.single i₀ 1) +
        L (systemPlace S p) (σ p) (Pi.single i₁ 1) * algebraMap K F β)) ^ systemMult S p := by
    intro p
    have := hlies p
    rw [systemValue, systemAbs, apply_eq_of_forall_eq_or hne huniv]
    congr 1
    rw [hxβ, map_mul, show algebraMap K F (x i₀) * L (systemPlace S p) (σ p) (Pi.single i₀ 1) +
      algebraMap K F (x i₀) * algebraMap K F β * L (systemPlace S p) (σ p) (Pi.single i₁ 1) =
      algebraMap K F (x i₀) * (L (systemPlace S p) (σ p) (Pi.single i₀ 1) +
        L (systemPlace S p) (σ p) (Pi.single i₁ 1) * algebraMap K F β) by ring, map_mul,
      AbsoluteValue.apply_algebraMap_of_liesOver (v := systemPlace S p)]
  have hH1 := one_le_mulHeightAff x
  have hH0 : 0 < mulHeightAff x := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [← Finset.prod_mul_distrib]
    simp only [← mul_pow]
    rw [← Finset.prod_congr rfl fun p _ ↦ hval p]
    calc ∏ p, systemValue S w L p (σ p) x ≤ ∏ p, (C p * mulHeightAff x ^ c p (σ p)) :=
          Finset.prod_le_prod₀ (fun p _ ↦ systemValue_nonneg S w L p _ x)
            fun p _ ↦ hx.2 p (σ p)
      _ = systemConst C * mulHeightAff x ^ (∑ p, c p (σ p)) := by
          rw [Real.rpow_sum_of_pos hH0, Finset.prod_mul_distrib]; rfl
      _ ≤ systemConst C * mulHeightAff x ^ (-(1 + δ)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith))
            (Finset.prod_nonneg fun p _ ↦ (hN.const_pos p).le)
  · refine (one_le_prod_systemAbs_algebraMap S w hwInf hwFin (hx.1 i₀) hx0).trans_eq
      (Finset.prod_congr rfl fun p _ ↦ ?_)
    have := hlies p
    rw [systemAbs, AbsoluteValue.apply_algebraMap_of_liesOver (v := systemPlace S p)]
  · have hxne : x ≠ 0 := fun h ↦ hx0 (by rw [h]; rfl)
    have h1 := mulHeight_le_prod_of_forall_mem_integer S hxne hx.1
    rw [Height.mulHeight_eq_mulHeight₁_div huniv x] at h1
    have h2 : (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) *
        ∏ v ∈ S, ⨆ i, FinitePlace.mk v (x i) =
        ∏ p, (⨆ j, systemPlace S p (x j)) ^ systemMult S p := by
      rw [prod_systemPlace S fun u ↦ ⨆ j, u (x j)]
      rfl
    rw [h2] at h1
    refine h1.trans_eq (Finset.prod_congr rfl fun p _ ↦ ?_)
    rw [Height.iSup_eq_max_of_forall_eq_or huniv, hxβ, map_mul,
      mul_max_of_nonneg _ _ (apply_nonneg _ _), mul_one]

/-- The arithmetic of the last step: a window `[t - e, M t + e)` of `h(β)` inside the range
`ha ≤ A h(β) + E` fits under `(t - e) · 3 A M` once `t ≥ 2 e + E`. -/
private theorem lt_mul_of_window {A M t e E hb ha : ℝ} (hA : 1 ≤ A) (hM : 1 ≤ M) (he : 0 ≤ e)
    (hE : 0 ≤ E) (ht : 2 * e + E ≤ t) (hup : ha ≤ A * hb + E) (hhi : hb < M * t + e) :
    ha < (t - e) * (3 * A * M) := by
  have h1 : A * hb < A * (M * t + e) := mul_lt_mul_of_pos_left hhi (by linarith)
  have hAM : 1 ≤ A * M := one_le_mul_of_one_le_of_one_le hA hM
  have h2 : A * M * (2 * e + E) ≤ A * M * t := mul_le_mul_of_nonneg_left ht (by linarith)
  have h3 : A * 1 * e ≤ A * M * e :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM (by linarith)) he
  have h4 : E ≤ A * M * E := le_mul_of_one_le_left hE hAM
  have h5 : 0 ≤ A * M * E := by linarith
  linarith

/-- **The threshold of the count for a normalized system in two variables**, a formula in the
height bound `H` of the coefficients, `δ`, the number `s` of places, `r = [F : K]`,
`nF = [F : ℚ]` and `nK = [K : ℚ]`. With `e = mobiusShift s` and
`E = s ((nF + 1) log 2 + 6 nF log H) / nK`, it is `exp (r s (L + e + 1) + E)`, where `L` is the
largest of Roth's threshold with targets at infinity (`NumberField.rothOnePointBound`, with the
targets of height at most `2 log H` and the constant at most `(32 H ^ (8 nF)) ^ s`), `2 e + E` and
`e + (4 / δ) log 2`. -/
noncomputable def systemRothThreshold (s r nF nK : ℕ) (δ H : ℝ) : ℝ :=
  Real.exp (((r * s : ℕ) : ℝ) * (max (rothOnePointBound s r nF nK (2 * (s : ℝ) * Real.log H)
      ((s : ℝ) * (Real.log 32 + 8 * (nF : ℝ) * Real.log H)) (2 + δ))
    (max (2 * mobiusShift s
        + (s : ℝ) * (((nF : ℝ) + 1) * Real.log 2 + 6 * (nF : ℝ) * Real.log H) / nK)
      (mobiusShift s + 4 / δ * Real.log 2)) + mobiusShift s + 1)
    + (s : ℝ) * (((nF : ℝ) + 1) * Real.log 2 + 6 * (nF : ℝ) * Real.log H) / nK)

/-- **Roth's interval result fed to Evertse's covering** (Layers 3.7 and 9.4, for two variables).
For a normalized system in two variables, at most
`s + 1 + m (N + s).choose s · (1 + log (3 r s M) / log (1 + δ / 4))` proper subspaces of `K²`
contain every solution of absolute affine height at least the explicit
`systemRothThreshold s r [F : ℚ] [K : ℚ] δ H`. Here `s` is the number of places of the system,
`r = [F : K]`, `H` bounds the absolute heights of the coefficients, and `m`, `M` and `N` are Roth's
chain length, ratio and class size at the exponent `2 + δ / 2`, so the count depends on `δ`, `s`
and `r` alone, and the threshold on these, `H` and the degrees. -/
theorem exists_finset_submodule_of_card_eq_two {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = 2) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    ∃ T : Finset (Submodule K (ι → K)),
      (T.card : ℝ) ≤ ((Fintype.card (InfinitePlace K) + S.card + 1 : ℕ) : ℝ) +
        ((rothChainLength (2 + δ / 2) (Fintype.card (InfinitePlace K) + S.card) (finrank K F) *
          (rothClassSize (2 + δ / 2) (Fintype.card (InfinitePlace K) + S.card) +
            (Fintype.card (InfinitePlace K) + S.card)).choose
              (Fintype.card (InfinitePlace K) + S.card) : ℕ) : ℝ) *
          (1 + Real.log (3 * ((finrank K F * (Fintype.card (InfinitePlace K) + S.card) : ℕ) : ℝ) *
            rothRatio (2 + δ / 2) (Fintype.card (InfinitePlace K) + S.card) (finrank K F)) /
            Real.log (1 + δ / 4)) ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x ∈ systemSet S w L C c,
        systemRothThreshold (Fintype.card (InfinitePlace K) + S.card) (finrank K F)
          (finrank ℚ F) (finrank ℚ K) δ H ≤ mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) →
        ∃ U ∈ T, x ∈ U := by
  classical
  -- the two indices
  obtain ⟨i₀, i₁, hne, huniv⟩ : ∃ i₀ i₁ : ι, i₀ ≠ i₁ ∧ ∀ i, i = i₀ ∨ i = i₁ := by
    have hnc : Nat.card ι = 2 := by rw [Nat.card_eq_fintype_card, hι]
    obtain ⟨p, q, hpq, hset⟩ := Nat.card_eq_two_iff.mp hnc
    refine ⟨p, q, hpq, fun i ↦ ?_⟩
    have hmem : i ∈ ({p, q} : Set ι) := by rw [hset]; exact Set.mem_univ i
    simpa using hmem
  have : Nonempty ι := ⟨i₀⟩
  set s : ℕ := Fintype.card (InfinitePlace K) + S.card with hsdef
  set r : ℕ := finrank K F with hrdef
  have hδ := hN.delta_pos
  have hcardP : Fintype.card (InfinitePlace K ⊕ S) = s := by
    rw [Fintype.card_sum, Fintype.card_coe]
  have hs1 : 1 ≤ s := by
    have : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
    omega
  have hr1 : 1 ≤ r := Module.finrank_pos
  have hlies : ∀ p, (w (systemPlace S p)).LiesOver (systemPlace S p) := by
    rintro (v | v)
    · exact hwInf v
    · exact hwFin v.1 v.2
  -- the small form at each place
  choose istar histar using hN.exists_exponent_eq
  set σ : InfinitePlace K ⊕ S → ι := fun p ↦ if istar p = i₀ then i₁ else i₀ with hσdef
  have hpair : ∀ p, ∑ i, c p i = c p (σ p) + systemExponent S p := fun p ↦ by
    rw [Finset.univ_eq_pair_of_forall_eq_or huniv, Finset.sum_pair hne, ← histar p]
    by_cases h : istar p = i₀
    · have : σ p = i₁ := by simp [hσdef, h]
      rw [this, h]; ring
    · have h1 : istar p = i₁ := (huniv _).resolve_left h
      have : σ p = i₀ := by simp [hσdef, h]
      rw [this, h1]
  have hσ : ∑ p, c p (σ p) ≤ -1 - δ := by
    have hw := hN.weight_le
    simp only [systemWeight, hpair, Finset.sum_add_distrib, sum_systemExponent] at hw
    linarith
  -- the forms are nonzero
  have hLne : ∀ p i, L (systemPlace S p) i ≠ 0 := by
    intro p i hL0
    have hdet := systemDet_pos hN
    have hd : LinearMap.det (LinearMap.pi (L (systemPlace S p))) = 0 := by
      by_contra hd
      have hu : IsUnit (LinearMap.pi (L (systemPlace S p))) :=
        (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
      obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).mp hu).2 (Pi.single i 1)
      have := congrFun hy i
      rw [LinearMap.pi_apply, hL0, LinearMap.zero_apply, Pi.single_eq_same] at this
      exact zero_ne_one this
    refine hdet.ne' (Finset.prod_eq_zero (Finset.mem_univ p) ?_)
    rw [systemAbs, hd, map_zero, zero_pow (systemMult_ne_zero S p)]
  set a : AbsoluteValue K ℝ → ι → F := fun u i ↦ L u i (Pi.single i₀ 1) with hadef
  set b : AbsoluteValue K ℝ → ι → F := fun u i ↦ L u i (Pi.single i₁ 1) with hbdef
  have hab0 : ∀ p i, a (systemPlace S p) i ≠ 0 ∨ b (systemPlace S p) i ≠ 0 := by
    intro p i
    by_contra h
    push Not at h
    refine hLne p i (LinearMap.ext fun y ↦ ?_)
    rw [apply_eq_of_forall_eq_or hne huniv, LinearMap.zero_apply]
    simp only [hadef, hbdef] at h
    rw [h.1, h.2]; ring
  -- the targets, spread to every absolute value
  set σ' : AbsoluteValue K ℝ → ι := fun u ↦
    if h : ∃ p, systemPlace S p = u then σ h.choose else i₀ with hσ'def
  have hσ' : ∀ p, σ' (systemPlace S p) = σ p := fun p ↦ by
    have h : ∃ q, systemPlace S q = systemPlace S p := ⟨p, rfl⟩
    simp only [hσ'def, h, ↓reduceDIte]
    exact congrArg σ (systemPlace_injective S h.choose_spec)
  set tgt : AbsoluteValue K ℝ → OnePoint F := fun u ↦
    OnePoint.formRoot (a u (σ' u)) (b u (σ' u)) with htgtdef
  -- the constants
  set Γ : ℝ := ∏ p, (w (systemPlace S p)).formConst (a (systemPlace S p) (σ p))
    (b (systemPlace S p) (σ p)) ^ systemMult S p with hΓdef
  have hΓ0 : 0 ≤ Γ :=
    Finset.prod_nonneg fun p _ ↦ pow_nonneg (AbsoluteValue.formConst_nonneg _ _ _) _
  set Cs : ℝ := systemConst C with hCsdef
  have hCs0 : 0 < Cs := Finset.prod_pos fun p _ ↦ hN.const_pos p
  set kap : InfinitePlace K ⊕ S → ℝ := fun p ↦
    if b (systemPlace S p) (σ p) = 0 then
      w (systemPlace S p) (a (systemPlace S p) (σ p)) ^ systemMult S p
    else w (systemPlace S p) (b (systemPlace S p) (σ p)) ^ systemMult S p *
      (2 ^ finrank ℚ F * mulHeight₁ (-(a (systemPlace S p) (σ p) / b (systemPlace S p) (σ p))))⁻¹
    with hkapdef
  have hkap0 : ∀ p, 0 < kap p := fun p ↦ by
    simp only [hkapdef]
    split_ifs with hb
    · have ha := (hab0 p (σ p)).resolve_right (not_not.mpr hb)
      exact pow_pos ((w _).pos ha) _
    · exact mul_pos (pow_pos ((w _).pos hb) _) (inv_pos.mpr (mul_pos (by positivity)
        (mulHeight₁_pos _)))
  set κc : ℝ := ∏ p, kap p with hκcdef
  have hκc0 : 0 < κc := Finset.prod_pos fun p _ ↦ hkap0 p
  -- the constants, bounded by the height bound `H` of the coefficients
  set G : ℝ := H ^ finrank ℚ F with hGdef
  have hcoef : ∀ p i j, mulHeight₁ (L (systemPlace S p) i (Pi.single j 1)) ≤ G := by
    intro p i j
    rw [← absMulHeight₁_pow_finrank, hGdef]
    have h := hN.height_le p i j
    rw [Pi.basisFun_apply] at h
    exact pow_le_pow_left₀ (zero_le_one.trans (one_le_absMulHeight₁ _)) h _
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hH1 : 1 ≤ H := (one_le_absMulHeight₁ _).trans (hN.height_le (Sum.inl v₀) i₀ i₀)
  have hG1 : 1 ≤ G := one_le_pow₀ hH1
  have hlogG : Real.log G = (finrank ℚ F : ℝ) * Real.log H := by rw [hGdef, Real.log_pow]
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH1
  have hup : ∀ p i j, w (systemPlace S p) (L (systemPlace S p) i (Pi.single j 1)) ≤ G :=
    fun p i j ↦ (apply_le_mulHeight₁_systemPlace S w p (hlies p) _).trans (hcoef p i j)
  have hlo : ∀ p i j, L (systemPlace S p) i (Pi.single j 1) ≠ 0 →
      G⁻¹ ≤ w (systemPlace S p) (L (systemPlace S p) i (Pi.single j 1)) := fun p i j hx ↦
    (inv_anti₀ (mulHeight₁_pos _) (hcoef p i j)).trans
      (inv_mulHeight₁_le_systemPlace S w p (hlies p) hx)
  have hΓle : Γ ≤ ((4 * G ^ 3) ^ 2) ^ s := by
    rw [hΓdef, ← hcardP]
    exact prod_pow_le_of_le (by nlinarith [one_le_pow₀ (n := 3) hG1])
      (fun p ↦ AbsoluteValue.formConst_nonneg _ _ _)
      (fun p ↦ formConst_le_of_bounds hG1 (hab0 p (σ p)) (hup p (σ p) i₀) (hlo p (σ p) i₀)
        (hlo p (σ p) i₁)) (systemMult_le_two S)
  have hCsle : Cs ≤ (2 * G ^ 2) ^ s := by
    rw [← hcardP]; exact systemConst_le_of_bounds hι hN hG1 hup
  have hκcle : ((2 ^ finrank ℚ F * G ^ 4) ^ s)⁻¹ ≤ κc := by
    rw [hκcdef, ← inv_pow, ← hcardP, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun p _ ↦ by positivity) fun p _ ↦
      inv_le_kap_of_bounds hG1 (systemMult_le_two S p) (hab0 p (σ p)) (hcoef p (σ p) i₀)
        (hcoef p (σ p) i₁) (hlo p (σ p) i₀) (hlo p (σ p) i₁)
  -- Roth's interval result with targets at infinity
  have hwFin' : ∀ v ∈ S.image FinitePlace.mk, (w v.1).LiesOver v.1 := by
    intro v hv
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    exact hwFin v' hv'
  have hA := exists_forall_mem_interval_of_prod_onePointApprox_le
    Finset.univ (S.image FinitePlace.mk) w (fun v _ ↦ hwInf v) hwFin' tgt (Γ * Cs)
    (κ := 2 + δ) (by linarith)
  have hcardS : (Finset.univ : Finset (InfinitePlace K)).card + (S.image FinitePlace.mk).card
      = s := by
    rw [Finset.card_univ, Finset.card_image_of_injective _ FinitePlace.mk_injective]
  have hκ₁ : (2 + δ + 2) / 2 = 2 + δ / 2 := by ring
  rw [hcardS, hκ₁] at hA
  set e : ℝ := mobiusShift s with hedef
  have he0 : 0 ≤ e := mobiusShift_nonneg _
  -- the threshold of the interval result, bounded by `H`
  have htgt : ∀ p, onePointHeight (tgt (systemPlace S p)) ≤ 2 * Real.log H := fun p ↦ by
    simp only [htgtdef, hσ' p]
    exact onePointHeight_formRoot_le hH1 (hcoef p (σ p) i₀) (hcoef p (σ p) i₁)
  have hHt : ∑ q : ↥(Finset.univ : Finset (InfinitePlace K)) ⊕ ↥(S.image FinitePlace.mk),
      onePointHeight (tgt (sPlaceAbsValue q)) ≤ 2 * (s : ℝ) * Real.log H := by
    calc _ ≤ ∑ _q : ↥(Finset.univ : Finset (InfinitePlace K)) ⊕ ↥(S.image FinitePlace.mk),
          2 * Real.log H := Finset.sum_le_sum fun q _ ↦ by
            rcases q with ⟨v, -⟩ | ⟨v, hv⟩
            · exact htgt (Sum.inl v)
            · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
              exact htgt (Sum.inr ⟨u, hu⟩)
      _ = 2 * (s : ℝ) * Real.log H := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_coe,
            Fintype.card_coe, hcardS, nsmul_eq_mul]
          ring
  have hlogC : Real.log (max (Γ * Cs) 1)
      ≤ (s : ℝ) * (Real.log 32 + 8 * (finrank ℚ F : ℝ) * Real.log H) :=
    (log_max_mul_le hG1 hCs0.le hΓle hCsle).trans_eq (by rw [hlogG]; ring)
  set LA₀ : ℝ := rothOnePointBound s r (finrank ℚ F) (finrank ℚ K) (2 * (s : ℝ) * Real.log H)
    ((s : ℝ) * (Real.log 32 + 8 * (finrank ℚ F : ℝ) * Real.log H)) (2 + δ) with hLA₀def
  have hLA : rothOnePointThreshold Finset.univ (S.image FinitePlace.mk) tgt (Γ * Cs) (2 + δ)
      ≤ LA₀ := by
    rw [rothOnePointThreshold, hcardS]
    exact rothOnePointBound_mono (by linarith) hHt hlogC
  -- the local analysis of a solution
  set d : ℝ := (finrank ℚ K : ℝ) with hddef
  have hd : 0 < d := by rw [hddef]; exact_mod_cast Module.finrank_pos
  have habs : ∀ y : K, absLogHeight₁ y = Real.log (mulHeight₁ y) / d := fun y ↦ by
    rw [absLogHeight₁_eq_inv_mul_logHeight₁, logHeight₁_eq_log_mulHeight₁, hddef,
      inv_mul_eq_div]
  have hrpow : ∀ x : ι → K,
      mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) = Real.exp (Real.log (mulHeightAff x) / d) :=
    fun x ↦ by rw [Real.rpow_def_of_pos (mulHeightAff_pos x), hddef, div_eq_mul_inv]
  set E : ℝ := max 0 (Real.log (Cs / κc)) / d with hEdef
  set E₀ : ℝ := (s : ℝ) * (((finrank ℚ F : ℝ) + 1) * Real.log 2
    + 6 * (finrank ℚ F : ℝ) * Real.log H) / d with hE₀def
  have hnum0 : 0 ≤ (s : ℝ) * (((finrank ℚ F : ℝ) + 1) * Real.log 2
      + 6 * (finrank ℚ F : ℝ) * Real.log H) := by
    have h2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have h0 : (0 : ℝ) ≤ finrank ℚ F := Nat.cast_nonneg _
    exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (mul_nonneg (by linarith) h2)
      (mul_nonneg (by linarith) hlogH))
  have hE₀0 : 0 ≤ E₀ := div_nonneg hnum0 hd.le
  have hEE₀ : E ≤ E₀ := by
    rw [hEdef, hE₀def]
    refine div_le_div_of_nonneg_right (max_le hnum0 ?_) hd.le
    exact (log_div_le hG1 hCs0 hκc0 hCsle hκcle).trans_eq (by rw [hlogG]; ring)
  set A : ℝ := ((r * s : ℕ) : ℝ) with hAdef
  have hA1 : 1 ≤ A := by rw [hAdef]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hsol : ∀ x ∈ systemSet S w L C c, x i₀ ≠ 0 →
      ((∏ v ∈ (Finset.univ : Finset (InfinitePlace K)),
          (w v.1).onePointApprox (tgt v.1) (algebraMap K F (x i₁ / x i₀)) ^ v.mult) *
        ∏ v ∈ S.image FinitePlace.mk,
          (w v.1).onePointApprox (tgt v.1) (algebraMap K F (x i₁ / x i₀))
        ≤ Γ * Cs * mulHeight₁ (x i₁ / x i₀) ^ (-(2 + δ))) ∧
      absLogHeight₁ (x i₁ / x i₀) ≤ Real.log (mulHeightAff x) / d ∧
      ((∀ p, L (systemPlace S p) (σ p) (fun j ↦ algebraMap K F (x j)) ≠ 0) →
        Real.log (mulHeightAff x) / d ≤ A * absLogHeight₁ (x i₁ / x i₀) + E) := by
    intro x hx hx0
    set β : K := x i₁ / x i₀ with hβdef
    obtain ⟨hsys, hx1, hHβ⟩ := prod_small_le S w hwInf hwFin hN hne huniv σ hσ hx hx0
    set z : InfinitePlace K ⊕ S → F := fun p ↦ a (systemPlace S p) (σ p) +
      b (systemPlace S p) (σ p) * algebraMap K F β with hzdef
    have hWβ : ∀ p, w (systemPlace S p) (algebraMap K F β) = systemPlace S p β := fun p ↦ by
      have := hlies p
      exact AbsoluteValue.apply_algebraMap_of_liesOver (v := systemPlace S p) _ β
    have hβpos : 0 < mulHeight₁ β := mulHeight₁_pos β
    have hHaff : mulHeight₁ β ≤ mulHeightAff x := by
      rw [hβdef, ← Height.mulHeight_eq_mulHeight₁_div huniv x]
      exact mulHeight_le_mulHeightAff x
    have hP0 : 0 ≤ ∏ p, systemPlace S p (x i₀) ^ systemMult S p :=
      Finset.prod_nonneg fun p _ ↦ pow_nonneg (apply_nonneg _ _) _
    have hZ0 : 0 ≤ ∏ p, w (systemPlace S p) (z p) ^ systemMult S p :=
      Finset.prod_nonneg fun p _ ↦ pow_nonneg (apply_nonneg _ _) _
    have hZle : ∏ p, w (systemPlace S p) (z p) ^ systemMult S p
        ≤ Cs * mulHeightAff x ^ (-(1 + δ)) :=
      (le_mul_of_one_le_left hZ0 hx1).trans hsys
    refine ⟨?_, ?_, fun hL ↦ ?_⟩
    · -- Roth's inequality for `β`
      have hconv : (∏ v ∈ (Finset.univ : Finset (InfinitePlace K)),
            (w v.1).onePointApprox (tgt v.1) (algebraMap K F β) ^ v.mult) *
          ∏ v ∈ S.image FinitePlace.mk, (w v.1).onePointApprox (tgt v.1) (algebraMap K F β)
          = ∏ p, (w (systemPlace S p)).onePointApprox (tgt (systemPlace S p))
              (algebraMap K F β) ^ systemMult S p := by
        rw [prod_image_mk S fun u ↦ (w u).onePointApprox (tgt u) (algebraMap K F β),
          prod_systemPlace S fun u ↦ (w u).onePointApprox (tgt u) (algebraMap K F β)]
      rw [hconv]
      set O : ℝ := ∏ p, (w (systemPlace S p)).onePointApprox (tgt (systemPlace S p))
        (algebraMap K F β) ^ systemMult S p with hOdef
      have hO0 : 0 ≤ O := Finset.prod_nonneg fun p _ ↦ pow_nonneg
        ((w _).onePointApprox_nonneg _ _) _
      have hloc : ∀ p, (w (systemPlace S p)).onePointApprox (tgt (systemPlace S p))
            (algebraMap K F β) * (systemPlace S p (x i₀) * max 1 (systemPlace S p β))
          ≤ (w (systemPlace S p)).formConst (a (systemPlace S p) (σ p))
              (b (systemPlace S p) (σ p)) *
                (systemPlace S p (x i₀) * w (systemPlace S p) (z p)) := by
        intro p
        have h1 := (w (systemPlace S p)).onePointApprox_formRoot_le (hab0 p (σ p))
          (algebraMap K F β)
        simp only [htgtdef, hσ' p]
        rw [hWβ p] at h1
        have hm : 0 < max 1 (systemPlace S p β) := lt_of_lt_of_le one_pos (le_max_left _ _)
        have hx0p : 0 ≤ systemPlace S p (x i₀) := apply_nonneg _ _
        calc (w (systemPlace S p)).onePointApprox
              (OnePoint.formRoot (a (systemPlace S p) (σ p)) (b (systemPlace S p) (σ p)))
              (algebraMap K F β) * (systemPlace S p (x i₀) * max 1 (systemPlace S p β))
            ≤ (w (systemPlace S p)).formConst (a (systemPlace S p) (σ p))
                (b (systemPlace S p) (σ p)) * (w (systemPlace S p) (z p) /
                  max 1 (systemPlace S p β)) *
                (systemPlace S p (x i₀) * max 1 (systemPlace S p β)) :=
              mul_le_mul_of_nonneg_right h1 (mul_nonneg hx0p hm.le)
          _ = _ := by field_simp
      have hprod : O * ∏ p, (systemPlace S p (x i₀) * max 1 (systemPlace S p β))
            ^ systemMult S p
          ≤ Γ * ((∏ p, systemPlace S p (x i₀) ^ systemMult S p) *
            ∏ p, w (systemPlace S p) (z p) ^ systemMult S p) := by
        rw [hOdef, hΓdef, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
          ← Finset.prod_mul_distrib]
        refine Finset.prod_le_prod₀ (fun p _ ↦ mul_nonneg (pow_nonneg
          ((w _).onePointApprox_nonneg _ _) _) (pow_nonneg (mul_nonneg (apply_nonneg _ _)
            (le_trans zero_le_one (le_max_left _ _))) _)) fun p _ ↦ ?_
        rw [← mul_pow, ← mul_pow, ← mul_pow]
        exact pow_le_pow_left₀ (mul_nonneg ((w _).onePointApprox_nonneg _ _)
          (mul_nonneg (apply_nonneg _ _) (le_trans zero_le_one (le_max_left _ _))))
          ((hloc p).trans_eq (by ring)) _
      have hHaffr : mulHeightAff x ^ (-(1 + δ)) ≤ mulHeight₁ β ^ (-(1 + δ)) :=
        Real.rpow_le_rpow_of_nonpos hβpos hHaff (by linarith)
      have hkey : O * mulHeight₁ β ≤ Γ * Cs * mulHeight₁ β ^ (-(1 + δ)) :=
        calc O * mulHeight₁ β ≤ O * ∏ p, (systemPlace S p (x i₀) *
              max 1 (systemPlace S p β)) ^ systemMult S p :=
              mul_le_mul_of_nonneg_left hHβ hO0
          _ ≤ Γ * ((∏ p, systemPlace S p (x i₀) ^ systemMult S p) *
              ∏ p, w (systemPlace S p) (z p) ^ systemMult S p) := hprod
          _ ≤ Γ * (Cs * mulHeightAff x ^ (-(1 + δ))) := mul_le_mul_of_nonneg_left hsys hΓ0
          _ ≤ Γ * (Cs * mulHeight₁ β ^ (-(1 + δ))) := by gcongr
          _ = Γ * Cs * mulHeight₁ β ^ (-(1 + δ)) := by ring
      have heq : mulHeight₁ β ^ (-(2 + δ)) = mulHeight₁ β ^ (-(1 + δ)) / mulHeight₁ β := by
        rw [show -(2 + δ) = -(1 + δ) - 1 by ring, Real.rpow_sub hβpos, Real.rpow_one]
      rw [heq, ← mul_div_assoc, le_div_iff₀ hβpos]
      exact hkey
    · -- the height of `β` is at most the affine height
      rw [habs]
      exact div_le_div_of_nonneg_right (Real.log_le_log hβpos hHaff) hd.le
    · -- the affine height is at most a power of the height of `β`
      have hz : ∀ p, z p ≠ 0 := fun p hzp ↦ by
        refine hL p ?_
        rw [apply_eq_of_forall_eq_or hne huniv]
        have : algebraMap K F (x i₁) = algebraMap K F (x i₀) * algebraMap K F β := by
          rw [← map_mul, hβdef, mul_div_cancel₀ _ hx0]
        rw [this, show algebraMap K F (x i₀) * L (systemPlace S p) (σ p) (Pi.single i₀ 1) +
          algebraMap K F (x i₀) * algebraMap K F β * L (systemPlace S p) (σ p) (Pi.single i₁ 1)
          = algebraMap K F (x i₀) * z p by simp only [hzdef, hadef, hbdef]; ring, hzp, mul_zero]
      have hlow : ∀ p, kap p ≤ w (systemPlace S p) (z p) ^ systemMult S p * mulHeight₁ β ^ r := by
        intro p
        have hHr : 1 ≤ mulHeight₁ β ^ r := one_le_pow₀ (one_le_mulHeight₁ β)
        simp only [hkapdef]
        split_ifs with hb
        · have hzp : z p = a (systemPlace S p) (σ p) := by simp [hzdef, hb]
          rw [hzp]
          exact le_mul_of_one_le_right (pow_nonneg (apply_nonneg _ _) _) hHr
        · set α : F := -(a (systemPlace S p) (σ p) / b (systemPlace S p) (σ p)) with hαdef
          have hzα : z p = b (systemPlace S p) (σ p) * (algebraMap K F β - α) := by
            simp only [hzdef, hαdef]; field_simp; ring
          have hne' : algebraMap K F β ≠ α := fun h ↦ hz p (by rw [hzα, h, sub_self, mul_zero])
          have hliou := inv_le_min_one_pow_systemMult S w p (hlies p) hne'
          have hmin : min 1 (w (systemPlace S p) (algebraMap K F β - α)) ^ systemMult S p
              ≤ w (systemPlace S p) (algebraMap K F β - α) ^ systemMult S p :=
            pow_le_pow_left₀ (le_min zero_le_one (apply_nonneg _ _)) (min_le_right _ _) _
          have hpos : 0 < 2 ^ finrank ℚ F * mulHeight₁ α := by
            have := mulHeight₁_pos α; positivity
          rw [hzα, map_mul, mul_pow]
          calc w (systemPlace S p) (b (systemPlace S p) (σ p)) ^ systemMult S p *
                (2 ^ finrank ℚ F * mulHeight₁ α)⁻¹
              = w (systemPlace S p) (b (systemPlace S p) (σ p)) ^ systemMult S p *
                ((2 ^ finrank ℚ F * mulHeight₁ α * mulHeight₁ β ^ r)⁻¹ * mulHeight₁ β ^ r) := by
                field_simp
            _ ≤ w (systemPlace S p) (b (systemPlace S p) (σ p)) ^ systemMult S p *
                (w (systemPlace S p) (algebraMap K F β - α) ^ systemMult S p *
                  mulHeight₁ β ^ r) := by
                gcongr
                exact hliou.trans hmin
            _ = _ := by ring
      have hprodlow : κc ≤ (∏ p, w (systemPlace S p) (z p) ^ systemMult S p) *
          mulHeight₁ β ^ (r * s) := by
        calc κc ≤ ∏ p, (w (systemPlace S p) (z p) ^ systemMult S p * mulHeight₁ β ^ r) :=
              Finset.prod_le_prod₀ (fun p _ ↦ (hkap0 p).le) fun p _ ↦ hlow p
          _ = _ := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcardP, ← pow_mul]
      have hHa1 := one_le_mulHeightAff x
      have hHa0 : 0 < mulHeightAff x := by linarith
      -- `κc · H(x) ≤ Cs · H(β) ^ (r s)`
      have hmain : κc * mulHeightAff x ≤ Cs * mulHeight₁ β ^ (r * s) := by
        have h1 : κc ≤ Cs * mulHeightAff x ^ (-(1 + δ)) * mulHeight₁ β ^ (r * s) :=
          hprodlow.trans (mul_le_mul_of_nonneg_right hZle (by positivity))
        have h2 : mulHeightAff x ≤ mulHeightAff x ^ (1 + δ) := by
          conv_lhs => rw [← Real.rpow_one (mulHeightAff x)]
          exact Real.rpow_le_rpow_of_exponent_le hHa1 (by linarith)
        have h3 : mulHeightAff x ^ (-(1 + δ)) * mulHeightAff x ^ (1 + δ) = 1 := by
          rw [← Real.rpow_add hHa0]; simp
        calc κc * mulHeightAff x ≤ κc * mulHeightAff x ^ (1 + δ) :=
              mul_le_mul_of_nonneg_left h2 hκc0.le
          _ ≤ Cs * mulHeightAff x ^ (-(1 + δ)) * mulHeight₁ β ^ (r * s) *
              mulHeightAff x ^ (1 + δ) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = Cs * mulHeight₁ β ^ (r * s) *
              (mulHeightAff x ^ (-(1 + δ)) * mulHeightAff x ^ (1 + δ)) := by ring
          _ = Cs * mulHeight₁ β ^ (r * s) := by rw [h3, mul_one]
      have hlog : Real.log (mulHeightAff x) ≤ Real.log (Cs / κc) + (r * s : ℕ) *
          Real.log (mulHeight₁ β) := by
        have h1 : mulHeightAff x ≤ Cs / κc * mulHeight₁ β ^ (r * s) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hκc0, mul_comm]; exact hmain
        have h2 := Real.log_le_log hHa0 h1
        rwa [Real.log_mul (div_pos hCs0 hκc0).ne' (pow_pos hβpos _).ne', Real.log_pow] at h2
      rw [habs, hEdef, hAdef]
      have hmx : Real.log (Cs / κc) ≤ max 0 (Real.log (Cs / κc)) := le_max_right _ _
      have : Real.log (mulHeightAff x) / d ≤
          (max 0 (Real.log (Cs / κc)) + (r * s : ℕ) * Real.log (mulHeight₁ β)) / d :=
        div_le_div_of_nonneg_right (by linarith) hd.le
      rw [add_div] at this
      linarith [show ((r * s : ℕ) : ℝ) * Real.log (mulHeight₁ β) / d =
        ((r * s : ℕ) : ℝ) * (Real.log (mulHeight₁ β) / d) by ring]
  -- the windows of the affine height
  set MR : ℝ := rothRatio (2 + δ / 2) s r with hMRdef
  have hMR1 : 1 ≤ MR := one_le_rothRatio (by linarith) s r
  set ω : ℝ := 3 * A * MR with hωdef
  have hAM : 1 ≤ A * MR := one_le_mul_of_one_le_of_one_le hA1 hMR1
  have hω1 : 1 ≤ ω := by rw [hωdef, mul_assoc]; linarith
  set L' : ℝ := max LA₀ (max (2 * e + E₀) (e + 4 / δ * Real.log 2)) with hL'def
  have hL'1 : 2 * e + E₀ ≤ L' := (le_max_left _ _).trans (le_max_right _ _)
  have hL'2 : e + 4 / δ * Real.log 2 ≤ L' := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨k, hk, t, ht, hcov⟩ := hA L' (hLA.trans (le_max_left _ _))
  set X₀ : ℝ := Real.exp (A * (L' + e + 1) + E₀) with hX₀def
  have hX₀eq : systemRothThreshold s r (finrank ℚ F) (finrank ℚ K) δ H = X₀ := rfl
  set X : Set (ι → K) := {x | x i₀ ≠ 0 ∧
    (∀ p, L (systemPlace S p) (σ p) (fun j ↦ algebraMap K F (x j)) ≠ 0) ∧
    X₀ ≤ mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹)} with hXdef
  set Q : Fin k → ℝ := fun i ↦ Real.exp (t i - e) with hQdef
  have hQ : ∀ i, (Fintype.card ι : ℝ) ^ (2 * Fintype.card ι / δ) ≤ Q i := fun i ↦ by
    rw [hι, hQdef, Nat.cast_ofNat, Real.rpow_def_of_pos two_pos]
    have h4 : Real.log 2 * (2 * 2 / δ) = 4 / δ * Real.log 2 := by ring
    rw [h4]
    exact Real.exp_le_exp.mpr (by linarith [ht i])
  have hint : ∀ x ∈ systemSet S w L C c, x ∈ X →
      ∃ i, Q i ≤ mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) ∧
        mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) < Q i ^ ω := by
    rintro x hx ⟨hx0, hL, hX⟩
    obtain ⟨hroth, hle, hup⟩ := hsol x hx hx0
    have hup' : Real.log (mulHeightAff x) / d ≤ A * absLogHeight₁ (x i₁ / x i₀) + E₀ := by
      linarith [hup hL]
    have hX' : A * (L' + e + 1) + E₀ ≤ Real.log (mulHeightAff x) / d := by
      rw [hrpow, hX₀def] at hX
      exact Real.exp_le_exp.mp hX
    have hβL : L' + e < absLogHeight₁ (x i₁ / x i₀) := by
      have h1 : A * (L' + e + 1) ≤ A * absLogHeight₁ (x i₁ / x i₀) := by linarith
      have h2 := le_of_mul_le_mul_left h1 (by linarith : 0 < A)
      linarith
    obtain ⟨i, hlo, hhi⟩ := hcov _ hroth hβL
    refine ⟨i, ?_, ?_⟩
    · rw [hrpow, hQdef]
      exact Real.exp_le_exp.mpr (by linarith)
    · rw [hrpow, hQdef, ← Real.exp_mul]
      exact Real.exp_lt_exp.mpr (lt_mul_of_window hA1 hMR1 he0 hE₀0 (hL'1.trans (ht i).le) hup'
        hhi)
  obtain ⟨T, hTcard, hTtop, hTcov⟩ :=
    exists_finset_submodule_of_forall_mem_interval_of_mem S w hwInf hwFin hN X Q hQ hω1 hint
  -- the lines where a small form vanishes, and the line `x₀ = 0`
  set kerL : InfinitePlace K ⊕ S → Submodule K (ι → K) := fun p ↦ LinearMap.ker
    (((L (systemPlace S p) (σ p)).restrictScalars K).comp
      (LinearMap.pi fun j ↦ (Algebra.linearMap K F).comp (LinearMap.proj j))) with hkerLdef
  have hmemker : ∀ p x, x ∈ kerL p ↔
      L (systemPlace S p) (σ p) (fun j ↦ algebraMap K F (x j)) = 0 := fun p x ↦ by
    simp only [hkerLdef, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_restrictScalars]
    rfl
  set V₀ : Submodule K (ι → K) := LinearMap.ker (LinearMap.proj i₀) with hV₀def
  refine ⟨insert V₀ (T ∪ Finset.univ.image kerL), ?_, ?_, ?_⟩
  · have h1 : ((insert V₀ (T ∪ Finset.univ.image kerL)).card : ℝ) ≤ T.card + (s + 1 : ℕ) := by
      have h2 := Finset.card_insert_le V₀ (T ∪ Finset.univ.image kerL)
      have h3 := Finset.card_union_le T (Finset.univ.image kerL)
      have h4 : (Finset.univ.image kerL).card ≤ s :=
        Finset.card_image_le.trans (by rw [Finset.card_univ, hcardP])
      have : (insert V₀ (T ∪ Finset.univ.image kerL)).card ≤ T.card + (s + 1) := by omega
      exact_mod_cast this
    have h22 : δ / (2 * (Fintype.card ι : ℝ)) = δ / 4 := by rw [hι]; norm_num
    rw [h22] at hTcard
    have hF0 : 0 ≤ 1 + Real.log ω / Real.log (1 + δ / 4) :=
      add_nonneg zero_le_one (div_nonneg (Real.log_nonneg hω1)
        (Real.log_nonneg (by linarith)))
    have h5 : (k : ℝ) * (1 + Real.log ω / Real.log (1 + δ / 4)) ≤
        ((rothChainLength (2 + δ / 2) s r * (rothClassSize (2 + δ / 2) s + s).choose s : ℕ) : ℝ) *
          (1 + Real.log ω / Real.log (1 + δ / 4)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hF0
    linarith
  · intro U hU
    rcases Finset.mem_insert.mp hU with rfl | hU
    · intro htop
      have h : (Pi.single i₀ (1 : K) : ι → K) ∈ V₀ := htop ▸ Submodule.mem_top
      simp [hV₀def] at h
    rcases Finset.mem_union.mp hU with hU | hU
    · exact hTtop U hU
    · obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hU
      intro htop
      have h0 : (Pi.single i₀ (1 : K) : ι → K) ∈ kerL p := htop ▸ Submodule.mem_top
      have h1 : (Pi.single i₁ (1 : K) : ι → K) ∈ kerL p := htop ▸ Submodule.mem_top
      rw [hmemker] at h0 h1
      have hsing : ∀ i, (fun j ↦ algebraMap K F ((Pi.single i (1 : K) : ι → K) j)) =
          Pi.single i 1 := fun i ↦ by
        funext j
        by_cases h : j = i
        · subst h; simp
        · simp [h]
      rw [hsing] at h0 h1
      rcases hab0 p (σ p) with h | h
      · exact h h0
      · exact h h1
  · intro x hx hX
    by_cases hx0 : x i₀ = 0
    · exact ⟨V₀, Finset.mem_insert_self _ _, by simp [hV₀def, hx0]⟩
    by_cases hL : ∃ p, L (systemPlace S p) (σ p) (fun j ↦ algebraMap K F (x j)) = 0
    · obtain ⟨p, hp⟩ := hL
      exact ⟨kerL p, Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_univ p))), (hmemker p x).mpr hp⟩
    · push Not at hL
      obtain ⟨U, hU, hxU⟩ := hTcov x hx ⟨hx0, hL, hX₀eq ▸ hX⟩
      exact ⟨U, Finset.mem_insert_of_mem (Finset.mem_union_left _ hU), hxU⟩

end NumberField
