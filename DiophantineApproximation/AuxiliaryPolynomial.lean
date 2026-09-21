/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.BombieriVaalerRelative
public import DiophantineApproximation.IndexConditions
public import DiophantineApproximation.MonomialHeight

/-!
# The auxiliary polynomial

Roth's method starts by manufacturing a polynomial that vanishes to high order at every one of
finitely many algebraic points and is not much larger than it has to be. This file is that
construction, Bombieri–Gubler's Lemma 6.3.4 — **the index theorem**.

Let `F / K` be a finite extension of number fields of degree `r`, let `α k : Fin m → F` be `N`
points and let `t k > 0` satisfy `r ∑ k, V_m (t k) < 1`, with `V_m` the volume of Layer 2.5. For
every `δ > 0` there is a `D₀` such that every multidegree `d` with `D₀ ≤ d j` carries a nonzero
`P` over `K` with `degreeOf j P ≤ d j`, with index at least `t k` at `α k` for every `k`, and
with

`h(P) ≤ r / (1 - r ∑ k, V_m (t k)) * ∑ k, ∑ j, V_m (t k) * (h (α k j) + log 2 + δ) * d j`,

all heights absolute and logarithmic. That is the `ε`–`D₀` reading of the book's `o(1)`, and it
is the form every application uses, because every application lets `d j → ∞` with `m` fixed.

The construction is Siegel's lemma on the coefficient space of the box `∏ j, {0, …, d j}`: the
conditions are the vanishing of `∂_μ P` at `α k` for every order `μ` of weight `∑ j, μ j / d j`
less than `t k`, they are counted by Layer 2.5 and their rows are measured by Layer 2.1.

## Main results

* `MvPolynomial.exists_ne_zero_le_index_logHeight_le`: **the milestone**, in the `ε`–`D₀` form.
* `MvPolynomial.exists_ne_zero_le_index_logHeight_le_of_pow_le`: the same at a **fixed**
  multidegree, with the lattice-point correction `κ` as a hypothesis. This is the whole of the
  construction; the milestone is this plus a choice of `D₀`.
* `MvPolynomial.absLogHeight_hasseDerivRow_le`: the absolute Arakelov height of a condition row,
  `½ log M + ∑ j, d j (log 2 + h (α j))`.
* `MvPolynomial.auxiliaryPolynomial_numeric_bound`: the numerical core — the passage from the
  constant Siegel's lemma produces to the constant the milestone states.
* `Real.log_add_one_le_mul` and `Real.one_add_pow_le_one_add`: the two elementary estimates that
  say what "large enough `D₀`" means, with `Real.log_le_two_mul_sqrt` and
  `Real.one_add_pow_le_of_le_one` behind them.

## Implementation notes

⚠ **`ArithmeticHeights` 5.7 is the wrong packaging, and 2.6 repackages 5.6 itself.** Layer 5.7
puts Siegel's lemma on the coefficient space of `totalDegree P ≤ D` — the *simplex* of monomials
— and Lemma 6.3.4 bounds the partial degrees, `degreeOf j P ≤ d j`, which is a *box*. No
inclusion mediates: shrinking `D` until the simplex fits inside the box throws away the monomials
of large total degree that carry the construction, and enlarging it breaks the degree bound the
index estimate of Layer 2.7 will need. So the milestone consumes Layer 5.6 —
`NumberField.exists_ne_zero_mem_ker_absMulHeight_le_relative_rank`, the relative Siegel lemma on
an arbitrary finite index type — directly, and supplies its own dictionary between coefficient
vectors and polynomials in `DiophantineApproximation/BoxMonomial.lean`. The roadmap's route,
"5.7 with the relative Siegel lemma of 5.6 behind it", was half right: 5.7 is a sibling of this
file rather than an ancestor of it.

⚠ **The rank form of 5.6 is not what 2.6 needed.** Layer 5.7 sent 5.6 back for a feasibility
hypothesis stated with `rank A` rather than with the number of rows, and that strengthening is
invisible here: what Layer 2.5 counts is the number of *conditions*, the estimate used is
`Matrix.rank_le_card_height`, and the row form of 5.6 would have served equally. The conditions
imposed at distinct orders at distinct points are visibly distinct rows, and nothing in Roth's
method asks whether they are independent.

⚠ **The `log 2` of the milestone is the binomial coefficient, and it is the only loss in the row
height.** The entry of a row at the monomial `X ^ I` is
`(∏ j, (I j).choose (μ j)) * ∏ j, α j ^ (I j - μ j)`, a multiplication table over the variables,
so Mathlib's Segre relation gives its height as a product of one-variable heights **exactly**;
the tuple of powers `α j ^ k, k ≤ d j`, has height exactly `H(α j) ^ d j`; and the only estimate
made anywhere is `(I j).choose (μ j) ≤ 2 ^ d j`. That is where `h (α k j) + log 2` comes from,
and the `+ δ` is not part of it.

⚠ **Three quantities have to be negligible and they are of three different orders.** The
lattice-point correction `(1 + ρ) ^ m - 1` is `O(m² / D₀)`; the `√M` by which the Arakelov
normalization of Siegel's lemma exceeds the sup-norm one contributes `½ log M = O(∑ j log d j)`;
and the discriminant of `K` contributes a constant. All three are `o(∑ j, d j)`, which is the
only reason the book can write `o(1)`, and the `δ` of the statement is exactly the room they
need. The elementary inequality behind the second is `log y ≤ 2 √y`, and behind the first
`(1 + x) ^ m ≤ 1 + x m 2 ^ m`; neither is sharp and neither needs to be.

⚠ **`m = 0` is excluded by the hypothesis rather than handled by the proof, and that is the
rejection test.** `V₀(t) = 1` for every `t ≥ 0`, so `r ∑ k, V₀(t k) = r N`, and the feasibility
hypothesis forces `N = 0`. That is as it should be: with no variables and one point there is no
auxiliary polynomial at all, since a nonzero constant has index `0` at every point. The
acceptance criteria record it.

⚠ **The numerical core is a separate statement because it is about nothing.** The passage from
the constant `r κ / (1 - r κ S)` that Siegel's lemma produces to the constant `r / (1 - r S)`
that the milestone states, at the price of `δ` per unit of degree, mentions no polynomial, no
height and no place; it is one inequality between eleven real numbers, and it is where the choice
of `ε` is made.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 6.3.4. M. Hindry and J. H. Silverman, *Diophantine Geometry: An Introduction*, Springer
GTM 201 (2000), Section D.4, for the shape of the Siegel lemma this consumes.

This is Layer 2.6 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset Height MeasureTheory Module MvPolynomial NumberField Real

noncomputable section

namespace Real

/-- `log y ≤ 2 √y`, the crude comparison that makes `log` negligible beside its argument. -/
theorem log_le_two_mul_sqrt {y : ℝ} (hy : 0 < y) : log y ≤ 2 * Real.sqrt y := by
  have h1 : log y = 2 * log (Real.sqrt y) := by rw [Real.log_sqrt hy.le]; ring
  have h2 : log (Real.sqrt y) ≤ Real.sqrt y - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hy)
  nlinarith [Real.sqrt_nonneg y]

/-- `(1 + x) ^ m ≤ 1 + x * m * 2 ^ m` for `0 ≤ x ≤ 1`: the crude form of the binomial theorem
that makes the lattice-point correction `(1 + ρ) ^ m` tend to `1`. -/
theorem one_add_pow_le_of_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    (1 + x) ^ m ≤ 1 + x * m * 2 ^ m := by
  induction m with
  | zero => simp
  | succ n ih =>
      have h2 : (0 : ℝ) < 2 ^ n := by positivity
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      calc (1 + x) ^ (n + 1) = (1 + x) ^ n * (1 + x) := by ring
        _ ≤ (1 + x * n * 2 ^ n) * (1 + x) := mul_le_mul_of_nonneg_right ih (by linarith)
        _ ≤ 1 + x * ((n : ℝ) + 1) * 2 ^ (n + 1) := by
            have hxx : x * x ≤ x := by nlinarith
            have hB : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
            have hA : x * x * ((n : ℝ) * 2 ^ n) ≤ x * ((n : ℝ) * 2 ^ n) := by
              have h := mul_nonneg hn h2.le
              nlinarith
            rw [pow_succ]
            nlinarith
        _ = 1 + x * ((n + 1 : ℕ) : ℝ) * 2 ^ (n + 1) := by push_cast; ring

/-- **The logarithm is negligible beside its argument**, in the explicit form Layer 2.6 needs:
`log (x + 1) ≤ ε x` as soon as `x ≥ 9 / ε ^ 2`. -/
theorem log_add_one_le_mul {ε x : ℝ} (hε0 : 0 < ε) (hx : 1 ≤ x) (h9 : 9 / ε ^ 2 ≤ x) :
    Real.log (x + 1) ≤ ε * x := by
  have hsq : 3 / ε ≤ Real.sqrt x := by
    rw [show (3 : ℝ) / ε = Real.sqrt ((3 / ε) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt ?_
    rw [div_pow]
    norm_num
    exact h9
  have hl1 : Real.log (x + 1) ≤ 2 * Real.sqrt (x + 1) := log_le_two_mul_sqrt (by linarith)
  have hl2 : Real.sqrt (x + 1) ≤ Real.sqrt (2 * x) := Real.sqrt_le_sqrt (by linarith)
  have hl3 : Real.sqrt (2 * x) ≤ 1.5 * Real.sqrt x := by
    rw [Real.sqrt_mul (by norm_num)]
    have h2 : Real.sqrt 2 ≤ 1.5 := by
      rw [show (1.5 : ℝ) = Real.sqrt (1.5 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg x]
  have hsq0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hsqsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have h3 : 3 ≤ ε * Real.sqrt x := by
    rw [div_le_iff₀ hε0] at hsq
    linarith
  calc Real.log (x + 1) ≤ 2 * Real.sqrt (x + 1) := hl1
    _ ≤ 2 * (1.5 * Real.sqrt x) := by linarith
    _ = 3 * Real.sqrt x := by ring
    _ ≤ (ε * Real.sqrt x) * Real.sqrt x := by nlinarith
    _ = ε * x := by rw [mul_assoc, hsqsq]

/-- **The lattice-point correction tends to `1`**, in the explicit form Layer 2.6 needs. -/
theorem one_add_pow_le_one_add {ρ ε : ℝ} {m : ℕ} (hρ0 : 0 ≤ ρ) (hε1 : ε ≤ 1)
    (hmpow : (1 : ℝ) ≤ (m : ℝ) * 2 ^ m) (hρ : ρ ≤ ε / ((m : ℝ) * 2 ^ m)) :
    (1 + ρ) ^ m ≤ 1 + ε := by
  have hmp : (0 : ℝ) < (m : ℝ) * 2 ^ m := by linarith
  have hεnn : 0 ≤ ε := by
    have h := hρ0.trans hρ
    rwa [le_div_iff₀ hmp, zero_mul] at h
  have hρ1 : ρ ≤ 1 := by
    refine hρ.trans ?_
    rw [div_le_one hmp]
    linarith
  refine (Real.one_add_pow_le_of_le_one hρ0 hρ1 m).trans ?_
  rw [le_div_iff₀ hmp] at hρ
  nlinarith

end Real

namespace MvPolynomial

/-- **The numerical core of the index theorem.** The Siegel bound produces the constant
`r κ / (1 − r κ S)` with `κ` the lattice-point correction, and the milestone asks for
`r / (1 − r S)` at the price of `δ` per unit of degree; this lemma is the bookkeeping that
turns one into the other once `κ ≤ 1 + ε`, the logarithm `lm` of the number of monomials and the
discriminant term `Δ` are all at most `ε` times the total degree `D`. -/
theorem auxiliaryPolynomial_numeric_bound {r S κ ε δ Δ lm G D L : ℝ}
    (hr : 0 < r) (hS : 0 < S) (hrS : r * S < 1)
    (hκ1 : 1 ≤ κ) (hκ : κ ≤ 1 + ε) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hεa : ε * (r * S) ≤ (1 - r * S) / 2)
    (hlm0 : 0 ≤ lm) (hlmD : lm ≤ ε * D) (hΔD : Δ ≤ ε * D)
    (hD0 : 0 ≤ D) (hGD : G ≤ S * D * L) (hL0 : 0 < L)
    (hfin : ε * (1 + 2 * r * S * L / (1 - r * S) ^ 2 + 2 * r * S / (1 - r * S))
      ≤ r * δ * S / (1 - r * S)) :
    Δ + r * κ / (1 - r * κ * S) * (G + S / 2 * lm) ≤ r / (1 - r * S) * (G + δ * S * D) := by
  have ha0 : (0 : ℝ) < 1 - r * S := by linarith
  have hb2 : (1 - r * S) / 2 ≤ 1 - r * κ * S := by nlinarith
  have hb0 : (0 : ℝ) < 1 - r * κ * S := by linarith
  have hba : 1 - r * κ * S ≤ 1 - r * S := by
    nlinarith [mul_nonneg (mul_nonneg hr.le hS.le) (sub_nonneg.mpr hκ1)]
  have hC1 : r * κ / (1 - r * κ * S) ≤ 4 * r / (1 - r * S) := by
    rw [div_le_div_iff₀ hb0 ha0]
    nlinarith [mul_nonneg (mul_pos hr ha0).le (by linarith : (0 : ℝ) ≤ 2 - κ),
      mul_nonneg hr.le (sub_nonneg.mpr hb2)]
  have hkey : r * κ / (1 - r * κ * S) - r / (1 - r * S)
      = r * (κ - 1) / ((1 - r * S) * (1 - r * κ * S)) := by field_simp; ring
  have hdiff : r * κ / (1 - r * κ * S) - r / (1 - r * S) ≤ 2 * r * ε / (1 - r * S) ^ 2 := by
    rw [hkey, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hr.le (sq_nonneg (1 - r * S)))
        (by linarith : (0 : ℝ) ≤ ε - (κ - 1)),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr.le) hε0.le)
        (mul_nonneg ha0.le (sub_nonneg.mpr hb2))]
  have hp1 : (r * κ / (1 - r * κ * S) - r / (1 - r * S)) * G
      ≤ 2 * r * ε / (1 - r * S) ^ 2 * (S * D * L) := by
    have h1 : (0 : ℝ) ≤ r * κ / (1 - r * κ * S) - r / (1 - r * S) := by rw [hkey]; positivity
    calc (r * κ / (1 - r * κ * S) - r / (1 - r * S)) * G
        ≤ (r * κ / (1 - r * κ * S) - r / (1 - r * S)) * (S * D * L) :=
          mul_le_mul_of_nonneg_left hGD h1
      _ ≤ 2 * r * ε / (1 - r * S) ^ 2 * (S * D * L) :=
          mul_le_mul_of_nonneg_right hdiff (by positivity)
  have hp2 : r * κ / (1 - r * κ * S) * (S / 2 * lm)
      ≤ 4 * r / (1 - r * S) * (S / 2 * (ε * D)) :=
    mul_le_mul hC1 (by nlinarith) (by positivity) (by positivity)
  have hexp : Δ + r * κ / (1 - r * κ * S) * (G + S / 2 * lm)
      = Δ + (r * κ / (1 - r * κ * S) - r / (1 - r * S)) * G
        + r * κ / (1 - r * κ * S) * (S / 2 * lm) + r / (1 - r * S) * G := by ring
  have hsum : Δ + (r * κ / (1 - r * κ * S) - r / (1 - r * S)) * G
      + r * κ / (1 - r * κ * S) * (S / 2 * lm)
      ≤ ε * D * (1 + 2 * r * S * L / (1 - r * S) ^ 2 + 2 * r * S / (1 - r * S)) := by
    have e1 : 2 * r * ε / (1 - r * S) ^ 2 * (S * D * L)
        = ε * D * (2 * r * S * L / (1 - r * S) ^ 2) := by field_simp
    have e2 : 4 * r / (1 - r * S) * (S / 2 * (ε * D))
        = ε * D * (2 * r * S / (1 - r * S)) := by field_simp; ring
    calc Δ + (r * κ / (1 - r * κ * S) - r / (1 - r * S)) * G
          + r * κ / (1 - r * κ * S) * (S / 2 * lm)
        ≤ ε * D + 2 * r * ε / (1 - r * S) ^ 2 * (S * D * L)
            + 4 * r / (1 - r * S) * (S / 2 * (ε * D)) := by linarith
      _ = ε * D * (1 + 2 * r * S * L / (1 - r * S) ^ 2 + 2 * r * S / (1 - r * S)) := by
          rw [e1, e2]; ring
  have hlast : ε * D * (1 + 2 * r * S * L / (1 - r * S) ^ 2 + 2 * r * S / (1 - r * S))
      ≤ r / (1 - r * S) * (δ * S * D) := by
    have h := mul_le_mul_of_nonneg_left hfin hD0
    calc ε * D * (1 + 2 * r * S * L / (1 - r * S) ^ 2 + 2 * r * S / (1 - r * S))
        = D * (ε * (1 + 2 * r * S * L / (1 - r * S) ^ 2 + 2 * r * S / (1 - r * S))) := by ring
      _ ≤ D * (r * δ * S / (1 - r * S)) := h
      _ = r / (1 - r * S) * (δ * S * D) := by field_simp
  rw [hexp, show r / (1 - r * S) * (G + δ * S * D)
    = r / (1 - r * S) * (δ * S * D) + r / (1 - r * S) * G by ring]
  linarith


end MvPolynomial

/-! ### The absolute height of a condition row -/

namespace NumberField

/-- The absolute logarithmic height of a field element, in terms of Mathlib's relative one. -/
theorem absLogHeight₁_eq_inv_mul {F : Type*} [Field F] [NumberField F] (y : F) :
    absLogHeight₁ y = ((finrank ℚ F : ℝ))⁻¹ * Real.log (Height.mulHeight₁ y) := by
  rw [← absLogHeight_eq_absLogHeight₁, absLogHeight_eq, Height.logHeight_eq_log_mulHeight,
    ← Height.mulHeight₁_eq_mulHeight]

end NumberField

namespace MvPolynomial

/-- **The absolute Arakelov height of a condition row** (Bombieri–Gubler, Lemma 6.3.4): the
sup-norm estimate of `MvPolynomial.mulHeight_hasseDerivRow_le` in the normalization Siegel's
lemma charges in. The square root of the number of monomials is the whole difference between the
two normalizations, and it is what the `δ` of the milestone absorbs. -/
theorem absLogHeight_hasseDerivRow_le {F : Type*} [Field F] [NumberField F] {m : ℕ}
    (d : Fin m → ℕ) (α : Fin m → F) {μ : Fin m →₀ ℕ} (hmu : ∀ j, μ j ≤ d j) :
    Real.log (arakelovMulHeight (hasseDerivRow d α μ)) / (finrank ℚ F : ℝ)
      ≤ 2⁻¹ * Real.log (Fintype.card (∀ j : Fin m, Fin (d j + 1)))
        + ∑ j, (d j : ℝ) * (Real.log 2 + absLogHeight₁ (α j)) := by
  have hdF : (0 : ℝ) < (finrank ℚ F : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
  have htw : (Height.totalWeight F : ℝ) = (finrank ℚ F : ℝ) := by
    rw [NumberField.totalWeight_eq_finrank]
  have hne : Nonempty (∀ j : Fin m, Fin (d j + 1)) := ⟨fun j ↦ 0⟩
  have hcard : (0 : ℝ) < (Fintype.card (∀ j : Fin m, Fin (d j + 1)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hpos1 : 0 < Height.mulHeight (hasseDerivRow d α μ) := Height.mulHeight_pos _
  have h1 := Real.log_le_log (arakelovMulHeight_pos (hasseDerivRow d α μ))
    (arakelovMulHeight_le_mulHeight (hasseDerivRow d α μ))
  rw [Real.log_mul (by positivity) hpos1.ne', Real.log_rpow hcard, htw] at h1
  have h2 := Real.log_le_log hpos1 (mulHeight_hasseDerivRow_le α hmu)
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_prod (fun j _ ↦ by positivity)] at h2
  have h3 : Real.log (((2 : ℝ) ^ (∑ j, d j)) ^ Height.totalWeight F)
      = (finrank ℚ F : ℝ) * ((∑ j, (d j : ℝ)) * Real.log 2) := by
    rw [← pow_mul, Real.log_pow, ← htw]
    push_cast
    ring
  have h4 : ∑ j, Real.log (Height.mulHeight₁ (α j) ^ d j)
      = ∑ j, (d j : ℝ) * Real.log (Height.mulHeight₁ (α j)) :=
    Finset.sum_congr rfl fun j _ ↦ Real.log_pow _ _
  rw [h3, h4] at h2
  rw [div_le_iff₀ hdF]
  have hterm : ∀ j : Fin m, (d j : ℝ) * (Real.log 2 + NumberField.absLogHeight₁ (α j))
        * (finrank ℚ F : ℝ)
      = (finrank ℚ F : ℝ) * ((d j : ℝ) * Real.log 2)
        + (d j : ℝ) * Real.log (Height.mulHeight₁ (α j)) := by
    intro j
    rw [NumberField.absLogHeight₁_eq_inv_mul]
    field_simp
  have hexp : (2⁻¹ * Real.log (Fintype.card (∀ j : Fin m, Fin (d j + 1)))
        + ∑ j, (d j : ℝ) * (Real.log 2 + NumberField.absLogHeight₁ (α j))) * (finrank ℚ F : ℝ)
      = (finrank ℚ F : ℝ) / 2 * Real.log (Fintype.card (∀ j : Fin m, Fin (d j + 1)))
        + ((finrank ℚ F : ℝ) * ((∑ j, (d j : ℝ)) * Real.log 2)
          + ∑ j, (d j : ℝ) * Real.log (Height.mulHeight₁ (α j))) := by
    rw [add_mul, Finset.sum_mul, Finset.sum_congr rfl fun j _ ↦ hterm j,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [hexp]
  linarith only [h1, h2]

/-! ### The index theorem at a fixed multidegree -/

/-- **Layer 2.6 at a fixed multidegree.** -/
theorem exists_ne_zero_le_index_logHeight_le_of_pow_le
    {K : Type*} [Field K] [NumberField K] {F : Type*} [Field F] [NumberField F] [Algebra K F]
    {m N : ℕ} (α : Fin N → Fin m → F) {t : Fin N → ℝ} (ht : ∀ k, 0 < t k)
    {d : Fin m → ℕ} (hd : ∀ j, 0 < d j) {κ : ℝ} (hκ1 : 1 ≤ κ)
    (hκ : ∀ k, (1 + max 1 (t k)⁻¹ * ∑ j, ((d j : ℝ))⁻¹) ^ m ≤ κ)
    (hfeas : (finrank K F : ℝ) * κ * ∑ k, cubeSimplexVolume m (t k) < 1) :
    ∃ P : MvPolynomial (Fin m) K, P ≠ 0 ∧ (∀ j, P.degreeOf j ≤ d j) ∧
      (∀ k, ENNReal.ofReal (t k) ≤ index (fun j ↦ (d j : ℝ)) (α k) (P.map (algebraMap K F))) ∧
      Real.log P.mulHeight / (finrank ℚ K : ℝ)
        ≤ (2 * (finrank ℚ K : ℝ))⁻¹ * Real.log |(NumberField.discr K : ℝ)|
          + (finrank K F : ℝ) * κ
              / (1 - (finrank K F : ℝ) * κ * ∑ k, cubeSimplexVolume m (t k))
            * ((∑ k, cubeSimplexVolume m (t k)
                  * ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ))
              + (∑ k, cubeSimplexVolume m (t k)) / 2
                * Real.log (Fintype.card (∀ j : Fin m, Fin (d j + 1)))) := by
  classical
  have hst : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hFin : Module.Finite K F := Module.Finite.of_restrictScalars_finite ℚ K F
  have hrpos : 0 < finrank K F := Module.finrank_pos
  have hr1 : (1 : ℝ) ≤ (finrank K F : ℝ) := by exact_mod_cast hrpos
  set rr : ℝ := (finrank K F : ℝ) with hrrdef
  set S : ℝ := ∑ k, cubeSimplexVolume m (t k) with hSdef
  set G : ℝ := ∑ k, cubeSimplexVolume m (t k)
    * ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ) with hGdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ ↦ cubeSimplexVolume_nonneg m (t k)
  have hκ0 : 0 < κ := lt_of_lt_of_le zero_lt_one hκ1
  have hb0 : 0 < 1 - rr * κ * S := by linarith
  have hProd0 : (0 : ℝ) ≤ ∏ j, (d j : ℝ) := Finset.prod_nonneg fun j _ ↦ Nat.cast_nonneg _
  -- the bracket is nonnegative
  have hB0 : ∀ k, 0 ≤ ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ) := fun k ↦
    Finset.sum_nonneg fun j _ ↦ mul_nonneg
      (by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
          have := absLogHeight₁_nonneg (α k j)
          linarith) (Nat.cast_nonneg _)
  have hG0 : 0 ≤ G :=
    Finset.sum_nonneg fun k _ ↦ mul_nonneg (cubeSimplexVolume_nonneg m (t k)) (hB0 k)
  -- the box
  have hne : Nonempty (∀ j : Fin m, Fin (d j + 1)) := ⟨fun j ↦ 0⟩
  set MM : ℕ := Fintype.card (∀ j : Fin m, Fin (d j + 1)) with hMMdef
  have hMpos : 0 < MM := Fintype.card_pos
  have hM0 : (0 : ℝ) < (MM : ℝ) := by exact_mod_cast hMpos
  have hM1 : (1 : ℝ) ≤ (MM : ℝ) := by exact_mod_cast hMpos
  have hlm0 : 0 ≤ Real.log (MM : ℝ) := Real.log_nonneg hM1
  have hMprod : (MM : ℝ) = ∏ j, ((d j : ℝ) + 1) := by
    rw [hMMdef, Fintype.card_pi]
    push_cast
    simp
  have hProdM : ∏ j, (d j : ℝ) ≤ (MM : ℝ) := by
    rw [hMprod]
    exact Finset.prod_le_prod₀ (fun j _ ↦ Nat.cast_nonneg _)
      fun j _ ↦ le_add_of_nonneg_right zero_le_one
  -- the rows
  obtain ⟨n, e⟩ : Σ' n : ℕ, Fin n ≃ (Σ k : Fin N, {I : ∀ j, Fin (d j + 1) //
      ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) < t k}) := ⟨_, (Fintype.equivFin _).symm⟩
  have hncard : n = Fintype.card (Σ k : Fin N, {I : ∀ j, Fin (d j + 1) //
      ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) < t k} : Type _) := by
    simpa using Fintype.card_congr e
  have hcardk : ∀ k, (Fintype.card {I : ∀ j, Fin (d j + 1) //
        ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) < t k} : ℝ)
      ≤ cubeSimplexVolume m (t k) * (κ * ∏ j, (d j : ℝ)) := by
    intro k
    have h1 : (Fintype.card {I : ∀ j, Fin (d j + 1) //
        ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) < t k} : ℝ) ≤ ((latticePoints d (t k)).card : ℝ) := by
      exact_mod_cast card_boxOrder_le_card_latticePoints d (t k)
    refine h1.trans ((card_latticePoints_le hd (ht k)).trans ?_)
    have hk := hκ k
    have hV := cubeSimplexVolume_nonneg m (t k)
    calc cubeSimplexVolume m (t k) * (1 + max 1 (t k)⁻¹ * ∑ j, ((d j : ℝ))⁻¹) ^ m
          * ∏ j, (d j : ℝ)
        ≤ cubeSimplexVolume m (t k) * κ * ∏ j, (d j : ℝ) := by gcongr
      _ = cubeSimplexVolume m (t k) * (κ * ∏ j, (d j : ℝ)) := by ring
  have hcount : (n : ℝ) ≤ κ * S * ∏ j, (d j : ℝ) := by
    have h1 : (n : ℝ) = ∑ k, (Fintype.card {I : ∀ j, Fin (d j + 1) //
        ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) < t k} : ℝ) := by
      rw [hncard, Fintype.card_sigma]
      push_cast
      ring
    calc (n : ℝ) = ∑ k, (Fintype.card {I : ∀ j, Fin (d j + 1) //
            ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) < t k} : ℝ) := h1
      _ ≤ ∑ k, cubeSimplexVolume m (t k) * (κ * ∏ j, (d j : ℝ)) :=
          Finset.sum_le_sum fun k _ ↦ hcardk k
      _ = S * (κ * ∏ j, (d j : ℝ)) := by rw [hSdef, ← Finset.sum_mul]
      _ = κ * S * ∏ j, (d j : ℝ) := by ring
  -- the condition matrix
  let _ : LinearOrder (∀ j : Fin m, Fin (d j + 1)) := linearOrderOfSTO WellOrderingRel
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix (Fin n) (∀ j : Fin m, Fin (d j + 1)) F,
      A = fun i ↦ hasseDerivRow d (α (e i).1) (boxMonomial d (e i).2.1) := ⟨_, rfl⟩
  have hrankn : (A.rank : ℝ) ≤ (n : ℝ) := by
    have h : A.rank ≤ n := by simpa using A.rank_le_card_height
    exact_mod_cast h
  have hrr0 : (0 : ℝ) ≤ rr := by linarith only [hr1]
  have hrκS0 : (0 : ℝ) ≤ rr * κ * S := by positivity
  have hrankM : rr * (A.rank : ℝ) ≤ rr * κ * S * (MM : ℝ) := by
    have h2 : rr * (A.rank : ℝ) ≤ rr * (κ * S * ∏ j, (d j : ℝ)) :=
      mul_le_mul_of_nonneg_left (hrankn.trans hcount) hrr0
    have h3 : rr * (κ * S * ∏ j, (d j : ℝ)) ≤ rr * κ * S * (MM : ℝ) := by
      rw [show rr * (κ * S * ∏ j, (d j : ℝ)) = rr * κ * S * ∏ j, (d j : ℝ) by ring]
      exact mul_le_mul_of_nonneg_left hProdM hrκS0
    linarith only [h2, h3]
  have hfeas' : finrank K F * A.rank < MM := by
    have h1 : ((finrank K F * A.rank : ℕ) : ℝ) = rr * (A.rank : ℝ) := by
      rw [hrrdef]; push_cast; ring
    have h4 : rr * κ * S * (MM : ℝ) < (MM : ℝ) := by
      calc rr * κ * S * (MM : ℝ) < 1 * (MM : ℝ) := by
            refine mul_lt_mul_of_pos_right ?_ hM0
            rw [hrrdef]; exact hfeas
        _ = (MM : ℝ) := one_mul _
    have h5 : ((finrank K F * A.rank : ℕ) : ℝ) < ((MM : ℕ) : ℝ) := by
      rw [h1]; linarith only [hrankM, h4]
    exact_mod_cast h5
  obtain ⟨x, hx0, hxker, hxint, hxle⟩ :=
    NumberField.exists_ne_zero_mem_ker_absMulHeight_le_relative_rank (K := K) A
      (by rw [hMMdef] at hfeas'; exact hfeas')
  rw [← hMMdef] at hxle
  -- the auxiliary polynomial
  obtain ⟨P, hPdef⟩ : ∃ P : MvPolynomial (Fin m) K, P = ofBox d x := ⟨_, rfl⟩
  have hPdeg : ∀ j, P.degreeOf j ≤ d j := by rw [hPdef]; exact degreeOf_ofBox_le x
  have hPcoeff : ∀ I, P.coeff (boxMonomial d I) = x I := by rw [hPdef]; exact coeff_ofBox x
  have hP0 : P ≠ 0 := by
    rw [hPdef]
    exact fun h ↦ hx0 (ofBox_injective (h.trans (map_zero (ofBox d)).symm))
  have hQdeg : ∀ j, (P.map (algebraMap K F)).degreeOf j ≤ d j := fun j ↦
    (degreeOf_map_le _ P j).trans (hPdeg j)
  refine ⟨P, hP0, hPdeg, ?_, ?_⟩
  · -- the index conditions
    intro k
    refine le_index_of_forall_eval_eq_zero (fun j ↦ (d j : ℝ)) (α k) _ fun μ hμ ↦ ?_
    by_cases hbox : ∀ j, μ j ≤ d j
    · obtain ⟨I, rfl⟩ := exists_boxMonomial_eq hbox
      have hw : ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) < t k := by
        rw [← sum_weight_boxMonomial d I]; exact hμ
      obtain ⟨i, hi⟩ : ∃ i : Fin n, e i = ⟨k, ⟨I, hw⟩⟩ :=
        ⟨e.symm _, Equiv.apply_symm_apply e _⟩
      have hAi : A i = hasseDerivRow d (α k) (boxMonomial d I) := by
        simp only [hAdef]
        rw [hi]
      have hmv : ∑ I', A i I' * algebraMap K F (x I') = 0 := by
        rw [← Matrix.mulVec_apply_eq_sum, hxker]
        rfl
      rw [eval_hasseDeriv_eq_sum hQdeg]
      refine Eq.trans (Finset.sum_congr rfl fun I' _ ↦ ?_) hmv
      rw [hAi, coeff_map, hPcoeff]
    · push Not at hbox
      obtain ⟨j, hj⟩ := hbox
      rw [hasseDeriv_eq_zero_of_lt (lt_of_le_of_lt (hQdeg j) hj), map_zero]
  · -- the height bound
    have hdF : (0 : ℝ) < (finrank ℚ F : ℝ) := by
      exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
    have hdisc : (0 : ℝ) < |(NumberField.discr K : ℝ)| := by
      have h : (NumberField.discr K : ℝ) ≠ 0 := by
        exact_mod_cast NumberField.discr_ne_zero (K := K)
      positivity
    have hlm0' : 0 ≤ Real.log (MM : ℝ) := hlm0
    have hZ0 : 0 ≤ G + S / 2 * Real.log (MM : ℝ) :=
      add_nonneg hG0 (mul_nonneg (by linarith) hlm0')
    -- the row estimate
    have hrowi : ∀ i : Fin n, Real.log (arakelovMulHeight (A i)) / (finrank ℚ F : ℝ)
        ≤ 2⁻¹ * Real.log (MM : ℝ)
          + ∑ j, (Real.log 2 + absLogHeight₁ (α (e i).1 j)) * (d j : ℝ) := by
      intro i
      have h := absLogHeight_hasseDerivRow_le d (α (e i).1) (boxMonomial_le d (e i).2.1)
      rw [← hMMdef] at h
      have hcomm : ∑ j, (d j : ℝ) * (Real.log 2 + absLogHeight₁ (α (e i).1 j))
          = ∑ j, (Real.log 2 + absLogHeight₁ (α (e i).1 j)) * (d j : ℝ) :=
        Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
      simp only [hAdef]
      rw [← hcomm]
      exact h
    have hW : ∑ i, Real.log (arakelovMulHeight (A i)) / (finrank ℚ F : ℝ)
        ≤ κ * (∏ j, (d j : ℝ)) * (G + S / 2 * Real.log (MM : ℝ)) := by
      have h1 : ∑ i, Real.log (arakelovMulHeight (A i)) / (finrank ℚ F : ℝ)
          ≤ ∑ i : Fin n, (2⁻¹ * Real.log (MM : ℝ)
              + ∑ j, (Real.log 2 + absLogHeight₁ (α (e i).1 j)) * (d j : ℝ)) :=
        Finset.sum_le_sum fun i _ ↦ hrowi i
      have h2 : ∑ i : Fin n, (2⁻¹ * Real.log (MM : ℝ)
              + ∑ j, (Real.log 2 + absLogHeight₁ (α (e i).1 j)) * (d j : ℝ))
          = ∑ k, (Fintype.card {I : ∀ j, Fin (d j + 1) //
                ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) < t k} : ℝ)
              * (2⁻¹ * Real.log (MM : ℝ)
                + ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ)) := by
        rw [Equiv.sum_comp e (fun ρ ↦ 2⁻¹ * Real.log (MM : ℝ)
            + ∑ j, (Real.log 2 + absLogHeight₁ (α ρ.1 j)) * (d j : ℝ)),
          ← Finset.univ_sigma_univ, Finset.sum_sigma]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        dsimp only
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have h3 : ∑ k, (Fintype.card {I : ∀ j, Fin (d j + 1) //
                ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) < t k} : ℝ)
              * (2⁻¹ * Real.log (MM : ℝ)
                + ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ))
          ≤ ∑ k, cubeSimplexVolume m (t k) * (κ * ∏ j, (d j : ℝ))
              * (2⁻¹ * Real.log (MM : ℝ)
                + ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ)) :=
        Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_right (hcardk k)
          (add_nonneg (by positivity) (hB0 k))
      have h4 : ∑ k, cubeSimplexVolume m (t k) * (κ * ∏ j, (d j : ℝ))
              * (2⁻¹ * Real.log (MM : ℝ)
                + ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ))
          = κ * (∏ j, (d j : ℝ)) * (G + S / 2 * Real.log (MM : ℝ)) := by
        have hterm : ∀ k : Fin N, cubeSimplexVolume m (t k) * (κ * ∏ j, (d j : ℝ))
              * (2⁻¹ * Real.log (MM : ℝ)
                + ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ))
            = (κ * ∏ j, (d j : ℝ)) * (cubeSimplexVolume m (t k) * (2⁻¹ * Real.log (MM : ℝ)))
              + (κ * ∏ j, (d j : ℝ)) * (cubeSimplexVolume m (t k)
                  * ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ)) := fun k ↦ by ring
        rw [Finset.sum_congr rfl fun k _ ↦ hterm k, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, ← Finset.sum_mul, ← hGdef, ← hSdef]
        ring
      linarith [h1, h3]
    -- the logarithm of the Siegel bound
    have hRk0 : (0 : ℝ)
        < ∏ i, (arakelovMulHeight (A i) ^ ((finrank ℚ F : ℝ))⁻¹) ^ finrank K F :=
      Finset.prod_pos fun i _ ↦ pow_pos (Real.rpow_pos_of_pos (arakelovMulHeight_pos _) _) _
    have hlogRk : Real.log (∏ i, (arakelovMulHeight (A i) ^ ((finrank ℚ F : ℝ))⁻¹)
          ^ finrank K F)
        = rr * ∑ i, Real.log (arakelovMulHeight (A i)) / (finrank ℚ F : ℝ) := by
      rw [Real.log_prod (f := fun i : Fin n ↦
          (arakelovMulHeight (A i) ^ ((finrank ℚ F : ℝ))⁻¹) ^ finrank K F)
        (fun i _ ↦ (pow_pos (Real.rpow_pos_of_pos (arakelovMulHeight_pos _) _) _).ne'),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Real.log_pow, Real.log_rpow (arakelovMulHeight_pos _), hrrdef]
      ring
    have hxP : absMulHeight x = P.mulHeight ^ ((finrank ℚ K : ℝ))⁻¹ := by
      rw [← funext hPcoeff]
      exact absMulHeight_coeff_box P hPdeg
    have hlogle := Real.log_le_log (absMulHeight_pos x) hxle
    rw [hxP, Real.log_rpow (MvPolynomial.mulHeight_pos P),
      Real.log_mul (Real.rpow_pos_of_pos hdisc _).ne' (Real.rpow_pos_of_pos hRk0 _).ne',
      Real.log_rpow hdisc, Real.log_rpow hRk0, hlogRk] at hlogle
    -- the denominator
    have hden2 : (MM : ℝ) * (1 - rr * κ * S) ≤ (MM : ℝ) - rr * (A.rank : ℝ) := by
      linarith [hrankM]
    have hden1 : (0 : ℝ) < (MM : ℝ) * (1 - rr * κ * S) := mul_pos hM0 hb0
    have hden0 : (0 : ℝ) < (MM : ℝ) - rr * (A.rank : ℝ) := lt_of_lt_of_le hden1 hden2
    have hCnn : (0 : ℝ) ≤ rr * κ / (1 - rr * κ * S) * (G + S / 2 * Real.log (MM : ℝ)) :=
      mul_nonneg (div_nonneg (mul_nonneg hrr0 hκ0.le) hb0.le) hZ0
    have hkey : ((MM : ℝ) - rr * (A.rank : ℝ))⁻¹
          * (rr * ∑ i, Real.log (arakelovMulHeight (A i)) / (finrank ℚ F : ℝ))
        ≤ rr * κ / (1 - rr * κ * S) * (G + S / 2 * Real.log (MM : ℝ)) := by
      rw [← div_eq_inv_mul, div_le_iff₀ hden0]
      have e1 : rr * κ / (1 - rr * κ * S) * (G + S / 2 * Real.log (MM : ℝ))
            * ((MM : ℝ) * (1 - rr * κ * S))
          = rr * κ * (MM : ℝ) * (G + S / 2 * Real.log (MM : ℝ)) := by
        field_simp
      have e2 : rr * ∑ i, Real.log (arakelovMulHeight (A i)) / (finrank ℚ F : ℝ)
          ≤ rr * κ * (MM : ℝ) * (G + S / 2 * Real.log (MM : ℝ)) := by
        calc rr * ∑ i, Real.log (arakelovMulHeight (A i)) / (finrank ℚ F : ℝ)
            ≤ rr * (κ * (∏ j, (d j : ℝ)) * (G + S / 2 * Real.log (MM : ℝ))) :=
              mul_le_mul_of_nonneg_left hW hrr0
          _ ≤ rr * κ * (MM : ℝ) * (G + S / 2 * Real.log (MM : ℝ)) := by
              rw [show rr * (κ * (∏ j, (d j : ℝ)) * (G + S / 2 * Real.log (MM : ℝ)))
                  = rr * κ * (G + S / 2 * Real.log (MM : ℝ)) * ∏ j, (d j : ℝ) by ring,
                show rr * κ * (MM : ℝ) * (G + S / 2 * Real.log (MM : ℝ))
                  = rr * κ * (G + S / 2 * Real.log (MM : ℝ)) * (MM : ℝ) by ring]
              exact mul_le_mul_of_nonneg_left hProdM
                (mul_nonneg (mul_nonneg hrr0 hκ0.le) hZ0)
      have e3 : rr * κ / (1 - rr * κ * S) * (G + S / 2 * Real.log (MM : ℝ))
            * ((MM : ℝ) * (1 - rr * κ * S))
          ≤ rr * κ / (1 - rr * κ * S) * (G + S / 2 * Real.log (MM : ℝ))
            * ((MM : ℝ) - rr * (A.rank : ℝ)) :=
        mul_le_mul_of_nonneg_left hden2 hCnn
      linarith [e1, e2, e3]
    rw [div_eq_inv_mul]
    linarith [hlogle, hkey]

/-! ### The index theorem -/

/-- **Layer 2.6 — the auxiliary polynomial** (Bombieri–Gubler, Lemma 6.3.4). -/
theorem exists_ne_zero_le_index_logHeight_le
    {K : Type*} [Field K] [NumberField K] {F : Type*} [Field F] [NumberField F] [Algebra K F]
    {m N : ℕ} (α : Fin N → Fin m → F) {t : Fin N → ℝ} (ht : ∀ k, 0 < t k)
    (hfeas : (finrank K F : ℝ) * ∑ k, cubeSimplexVolume m (t k) < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ D₀ : ℕ, ∀ d : Fin m → ℕ, (∀ j, D₀ ≤ d j) →
      ∃ P : MvPolynomial (Fin m) K, P ≠ 0 ∧ (∀ j, P.degreeOf j ≤ d j) ∧
        (∀ k, ENNReal.ofReal (t k)
            ≤ index (fun j ↦ (d j : ℝ)) (α k) (P.map (algebraMap K F))) ∧
        Real.log P.mulHeight / (finrank ℚ K : ℝ)
          ≤ (finrank K F : ℝ) / (1 - (finrank K F : ℝ) * ∑ k, cubeSimplexVolume m (t k))
            * ∑ k, ∑ j, cubeSimplexVolume m (t k)
                * (absLogHeight₁ (α k j) + Real.log 2 + δ) * (d j : ℝ) := by
  classical
  have hst : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hFin : Module.Finite K F := Module.Finite.of_restrictScalars_finite ℚ K F
  have hrpos : 0 < finrank K F := Module.finrank_pos
  have hr1 : (1 : ℝ) ≤ (finrank K F : ℝ) := by exact_mod_cast hrpos
  -- No points: the constant polynomial `1` does the job.
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    exact ⟨0, fun d _ ↦ ⟨1, one_ne_zero, fun j ↦ by simp, fun k ↦ k.elim0,
      by simp [MvPolynomial.mulHeight_one]⟩⟩
  -- No variables: the feasibility hypothesis is contradictory.
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · exfalso
    subst hm0
    have hV : ∀ k : Fin N, cubeSimplexVolume 0 (t k) = 1 := fun k ↦
      cubeSimplexVolume_eq_one 0 (by simpa using (ht k).le)
    have hS : ∑ k, cubeSimplexVolume 0 (t k) = (N : ℝ) := by simp [hV]
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
    rw [hS] at hfeas
    nlinarith
  have : NeZero N := ⟨hNpos.ne'⟩
  have : NeZero m := ⟨hmpos.ne'⟩
  -- The data of the estimate.
  have hVpos : ∀ k, 0 < cubeSimplexVolume m (t k) := fun k ↦ cubeSimplexVolume_pos m (ht k)
  have hSpos : 0 < ∑ k, cubeSimplexVolume m (t k) :=
    Finset.sum_pos (fun k _ ↦ hVpos k) Finset.univ_nonempty
  set rr : ℝ := (finrank K F : ℝ) with hrrdef
  set S : ℝ := ∑ k, cubeSimplexVolume m (t k) with hSdef
  have ha0 : 0 < 1 - rr * S := by linarith
  -- a uniform bound for the local heights
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log 2 + ∑ k, ∑ j, absLogHeight₁ (α k j) := ⟨_, rfl⟩
  have hL0 : 0 < L := by
    have h1 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h2 : (0 : ℝ) ≤ ∑ k, ∑ j, absLogHeight₁ (α k j) :=
      Finset.sum_nonneg fun k _ ↦ Finset.sum_nonneg fun j _ ↦ absLogHeight₁_nonneg _
    rw [hLdef]; linarith
  have hLle : ∀ k j, Real.log 2 + absLogHeight₁ (α k j) ≤ L := by
    intro k j
    have h1 : absLogHeight₁ (α k j) ≤ ∑ j', absLogHeight₁ (α k j') :=
      Finset.single_le_sum (fun j' _ ↦ absLogHeight₁_nonneg _) (Finset.mem_univ j)
    have h2 : (∑ j', absLogHeight₁ (α k j')) ≤ ∑ k', ∑ j', absLogHeight₁ (α k' j') :=
      Finset.single_le_sum
        (fun k' _ ↦ Finset.sum_nonneg fun j' _ ↦ absLogHeight₁_nonneg _) (Finset.mem_univ k)
    rw [hLdef]; linarith
  -- the small parameter
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ,
      Q = 1 + 2 * rr * S * L / (1 - rr * S) ^ 2 + 2 * rr * S / (1 - rr * S) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by
    rw [hQdef]
    have h1 : (0 : ℝ) < 2 * rr * S * L / (1 - rr * S) ^ 2 := by positivity
    have h2 : (0 : ℝ) < 2 * rr * S / (1 - rr * S) := by positivity
    linarith
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ,
      ε = min 1 (min ((1 - rr * S) / (2 * rr * S)) ((rr * δ * S / (1 - rr * S)) / Q)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by
    rw [hεdef]
    exact lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  have hε1 : ε ≤ 1 := by rw [hεdef]; exact min_le_left _ _
  have hεa : ε * (rr * S) ≤ (1 - rr * S) / 2 := by
    have h : ε ≤ (1 - rr * S) / (2 * rr * S) :=
      le_trans (by rw [hεdef]; exact min_le_right _ _) (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hfin : ε * Q ≤ rr * δ * S / (1 - rr * S) := by
    have h : ε ≤ (rr * δ * S / (1 - rr * S)) / Q :=
      le_trans (by rw [hεdef]; exact min_le_right _ _) (min_le_right _ _)
    rw [le_div_iff₀ hQ0] at h
    exact h
  -- the threshold
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 1 + ∑ k, (t k)⁻¹ := ⟨_, rfl⟩
  have hT1 : (1 : ℝ) ≤ T := by
    rw [hTdef]
    have : (0 : ℝ) ≤ ∑ k, (t k)⁻¹ :=
      Finset.sum_nonneg fun k _ ↦ inv_nonneg.mpr (ht k).le
    linarith
  have hTk : ∀ k, max 1 (t k)⁻¹ ≤ T := by
    intro k
    refine max_le hT1 ?_
    have h1 : (t k)⁻¹ ≤ ∑ k', (t k')⁻¹ :=
      Finset.single_le_sum (f := fun k' ↦ (t k')⁻¹)
        (fun k' _ ↦ inv_nonneg.mpr (ht k').le) (Finset.mem_univ k)
    rw [hTdef]; linarith
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : ℝ,
      Δ = (2 * (finrank ℚ K : ℝ))⁻¹ * Real.log |(NumberField.discr K : ℝ)| := ⟨_, rfl⟩
  have hdisc1 : (1 : ℝ) ≤ |(NumberField.discr K : ℝ)| := by
    have h : (1 : ℤ) ≤ |NumberField.discr K| :=
      Int.one_le_abs (NumberField.discr_ne_zero K)
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|NumberField.discr K| : ℤ) : ℝ) := by exact_mod_cast h
      _ = |(NumberField.discr K : ℝ)| := by push_cast [abs_abs]; rfl
  have hΔ0 : 0 ≤ Δ := by
    rw [hΔdef]
    have : (0 : ℝ) ≤ Real.log |(NumberField.discr K : ℝ)| := Real.log_nonneg hdisc1
    positivity
  refine ⟨⌈max (max (T * m ^ 2 * 2 ^ m / ε) (9 / ε ^ 2)) (Δ / ε)⌉₊ + 1, fun d hd ↦ ?_⟩
  have hdX : ∀ j, max (max (T * m ^ 2 * 2 ^ m / ε) (9 / ε ^ 2)) (Δ / ε) ≤ (d j : ℝ) := by
    intro j
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast le_trans (Nat.le_succ _) (hd j)
  have hd1 : ∀ j, 1 ≤ d j := fun j ↦ le_trans (Nat.le_add_left 1 _) (hd j)
  have hdpos : ∀ j, 0 < d j := fun j ↦ hd1 j
  have hd1R : ∀ j, (1 : ℝ) ≤ (d j : ℝ) := fun j ↦ by exact_mod_cast hd1 j
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
  -- The lattice-point correction is at most `κ = 1 + ε`.
  have hκ0 : (0 : ℝ) < 1 + ε := by linarith
  have hκ1 : (1 : ℝ) ≤ 1 + ε := by linarith
  have hrκS : rr * (1 + ε) * S < 1 := by linarith only [hεa, hfeas]
  have hXpos : (0 : ℝ) < T * (m : ℝ) ^ 2 * 2 ^ m := by positivity
  have hinv : ∀ j, ((d j : ℝ))⁻¹ ≤ ε / (T * (m : ℝ) ^ 2 * 2 ^ m) := by
    intro j
    have h1 : T * (m : ℝ) ^ 2 * 2 ^ m / ε ≤ (d j : ℝ) :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (hdX j)
    rw [div_le_iff₀ hε0] at h1
    rw [← one_div, div_le_div_iff₀ (by linarith [hd1R j]) hXpos]
    nlinarith [hd1R j]
  have hsuminv : ∑ j, ((d j : ℝ))⁻¹ ≤ ε / (T * (m : ℝ) * 2 ^ m) := by
    calc ∑ j, ((d j : ℝ))⁻¹ ≤ ∑ _j : Fin m, ε / (T * (m : ℝ) ^ 2 * 2 ^ m) :=
          Finset.sum_le_sum fun j _ ↦ hinv j
      _ = (m : ℝ) * (ε / (T * (m : ℝ) ^ 2 * 2 ^ m)) := by simp
      _ = ε / (T * (m : ℝ) * 2 ^ m) := by field_simp
  have hmpow : (1 : ℝ) ≤ (m : ℝ) * 2 ^ m := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    nlinarith
  have hpow : ∀ k, (1 + max 1 (t k)⁻¹ * ∑ j, ((d j : ℝ))⁻¹) ^ m ≤ 1 + ε := by
    intro k
    have hs0 : (0 : ℝ) ≤ ∑ j, ((d j : ℝ))⁻¹ := Finset.sum_nonneg fun j _ ↦ by positivity
    have hmax0 : (0 : ℝ) ≤ max 1 (t k)⁻¹ := le_trans zero_le_one (le_max_left _ _)
    have h0 : 0 ≤ max 1 (t k)⁻¹ * ∑ j, ((d j : ℝ))⁻¹ := mul_nonneg hmax0 hs0
    have hrhok : max 1 (t k)⁻¹ * ∑ j, ((d j : ℝ))⁻¹ ≤ ε / ((m : ℝ) * 2 ^ m) := by
      calc max 1 (t k)⁻¹ * ∑ j, ((d j : ℝ))⁻¹ ≤ T * (ε / (T * (m : ℝ) * 2 ^ m)) :=
            mul_le_mul (hTk k) hsuminv hs0 (by linarith)
        _ = ε / ((m : ℝ) * 2 ^ m) := by field_simp
    exact Real.one_add_pow_le_one_add h0 hε1 hmpow hrhok
  -- Apply the index theorem at this multidegree.
  obtain ⟨P, hP0, hPdeg, hPindex, hPheight⟩ :=
    exists_ne_zero_le_index_logHeight_le_of_pow_le α ht hdpos hκ1 hpow
      (by rw [← hrrdef, ← hSdef]; exact hrκS)
  refine ⟨P, hP0, hPdeg, hPindex, le_trans hPheight ?_⟩
  -- The bookkeeping.
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = ∑ k, cubeSimplexVolume m (t k)
      * ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ) := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = ∑ j, (d j : ℝ) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hDdef]; exact Finset.sum_nonneg fun j _ ↦ Nat.cast_nonneg _
  have hGD : G ≤ S * D * L := by
    rw [hGdef, hSdef, hDdef]
    have hk : ∀ k : Fin N, ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ)
        ≤ (∑ j, (d j : ℝ)) * L := by
      intro k
      calc ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ)
          ≤ ∑ j, L * (d j : ℝ) :=
            Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_right (hLle k j) (Nat.cast_nonneg _)
        _ = (∑ j, (d j : ℝ)) * L := by rw [← Finset.mul_sum]; ring
    calc ∑ k, cubeSimplexVolume m (t k) * ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ)
        ≤ ∑ k, cubeSimplexVolume m (t k) * ((∑ j, (d j : ℝ)) * L) :=
          Finset.sum_le_sum fun k _ ↦
            mul_le_mul_of_nonneg_left (hk k) (cubeSimplexVolume_nonneg m (t k))
      _ = (∑ k, cubeSimplexVolume m (t k)) * (∑ j, (d j : ℝ)) * L := by
          rw [← Finset.sum_mul]; ring
  -- the number of monomials is negligible
  have hMprod : ((Fintype.card (∀ j : Fin m, Fin (d j + 1))) : ℝ) = ∏ j, ((d j : ℝ) + 1) := by
    rw [Fintype.card_pi]
    push_cast
    simp
  have hlogd : ∀ j, Real.log ((d j : ℝ) + 1) ≤ ε * (d j : ℝ) := fun j ↦
    Real.log_add_one_le_mul hε0 (hd1R j)
      (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (hdX j))
  have hlmD : Real.log ((Fintype.card (∀ j : Fin m, Fin (d j + 1))) : ℝ) ≤ ε * D := by
    rw [hMprod, Real.log_prod (f := fun j : Fin m ↦ (d j : ℝ) + 1)
      (fun j _ ↦ by have := hd1R j; positivity), hDdef, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ ↦ hlogd j
  have hlm0 : 0 ≤ Real.log ((Fintype.card (∀ j : Fin m, Fin (d j + 1))) : ℝ) := by
    refine Real.log_nonneg ?_
    exact_mod_cast Fintype.card_pos
  have hΔD : Δ ≤ ε * D := by
    obtain ⟨j0⟩ : Nonempty (Fin m) := ⟨⟨0, hmpos⟩⟩
    have h1 : Δ / ε ≤ (d j0 : ℝ) := le_trans (le_max_right _ _) (hdX j0)
    have h2 : (d j0 : ℝ) ≤ D := by
      rw [hDdef]
      exact Finset.single_le_sum (f := fun j ↦ (d j : ℝ))
        (fun j _ ↦ Nat.cast_nonneg _) (Finset.mem_univ j0)
    rw [div_le_iff₀ hε0] at h1
    nlinarith
  -- the target, rewritten
  have htarget : ∑ k, ∑ j, cubeSimplexVolume m (t k)
      * (absLogHeight₁ (α k j) + Real.log 2 + δ) * (d j : ℝ) = G + δ * S * D := by
    rw [hGdef, hSdef, hDdef]
    have hk : ∀ k : Fin N, ∑ j, cubeSimplexVolume m (t k)
          * (absLogHeight₁ (α k j) + Real.log 2 + δ) * (d j : ℝ)
        = cubeSimplexVolume m (t k) * ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ)
          + δ * (cubeSimplexVolume m (t k) * ∑ j, (d j : ℝ)) := by
      intro k
      rw [Finset.mul_sum, show δ * (cubeSimplexVolume m (t k) * ∑ j, (d j : ℝ))
          = ∑ j, δ * (cubeSimplexVolume m (t k) * (d j : ℝ)) by
            rw [Finset.mul_sum, Finset.mul_sum], ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [Finset.sum_congr rfl fun k _ ↦ hk k, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul]
    ring
  rw [← hrrdef, ← hSdef, ← hGdef, ← hΔdef, htarget]
  rw [hQdef] at hfin
  exact auxiliaryPolynomial_numeric_bound (by linarith) hSpos hfeas hκ1 le_rfl hε0 hε1 hεa
    hlm0 hlmD hΔD hD0 hGD hL0 hfin

/-! ### Acceptance criteria -/

/-- **Rejection test: with no variables the feasibility hypothesis forbids every point.** The
region `𝒱₀(t)` is a point of volume `1` as soon as `t ≥ 0`, so `r ∑ k, V₀(t k) = r N`, and
`r ≥ 1` leaves no room for a single point. This is not an artefact: a nonzero polynomial in no
variables is a nonzero constant, whose index at any point is `0`. -/
example {K : Type*} [Field K] [NumberField K] {F : Type*} [Field F] [NumberField F] [Algebra K F]
    {N : ℕ} {t : Fin N → ℝ} (ht : ∀ k, 0 < t k)
    (hfeas : (finrank K F : ℝ) * ∑ k, cubeSimplexVolume 0 (t k) < 1) : N = 0 := by
  have hst : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hFin : Module.Finite K F := Module.Finite.of_restrictScalars_finite ℚ K F
  have hr1 : (1 : ℝ) ≤ (finrank K F : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := K) (M := F)
  have hV : ∀ k : Fin N, cubeSimplexVolume 0 (t k) = 1 := fun k ↦
    cubeSimplexVolume_eq_one 0 (by simpa using (ht k).le)
  rw [show ∑ k, cubeSimplexVolume 0 (t k) = (N : ℝ) by simp [hV]] at hfeas
  by_contra h
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
  nlinarith

/-- **Rejection test: the smallness of `ε` is not decoration.** The feasibility hypothesis of
the construction is `r κ S < 1` with `κ = 1 + ε` the lattice-point correction, and it does not
follow from the milestone's `r S < 1`: at `r = 1` and `S = 1/2` the hypothesis survives `ε` up to
`1` and no further. This is what `D₀` is chosen to guarantee, and it is why the choice of `ε`
comes before the choice of `D₀` and not after. -/
example : (1 : ℝ) * (1 / 2) < 1 ∧ ¬ ((1 : ℝ) * (1 + 1) * (1 / 2) < 1) := by norm_num

end MvPolynomial

end
