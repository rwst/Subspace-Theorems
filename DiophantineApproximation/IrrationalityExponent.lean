/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith

-- Used only inside proofs and in the acceptance criteria.
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

/-!
# The irrationality exponent

The **irrationality exponent** `Real.irrationalityExponent ξ` of a real number is the supremum of
the orders `p` to which `ξ` can be approximated by rationals: the `p` for which

```text
|ξ - m / n| < C / n ^ p
```

holds for some `C` and infinitely many denominators `n`. That condition is Mathlib's
`LiouvilleWith p ξ`, so the exponent is an `ℝ≥0∞`-valued supremum over the `p` that satisfy it, in
the shape of `dimH`. It is `1` at a rational, at least `2` at an irrational — Dirichlet — and `⊤`
exactly at a Liouville number. The value `⊤` is not junk: it is the exponent Liouville numbers
have, and a real-valued definition by an infimum of admissible exponents would give them the junk
value `0`, below every other irrational.

Everything here is about real numbers and rational approximations; nothing in this file knows what
an algebraic number is. The Liouville bound `irrationalityExponent ξ ≤ deg ξ` for an algebraic `ξ`
is the companion file `DiophantineApproximation/LiouvilleExponent.lean`, which gets it from Layer
0.4.

## Main results

* `Real.irrationalityExponent`: the definition, and the order API
  `Real.le_irrationalityExponent`, `Real.irrationalityExponent_le_iff`,
  `Real.liouvilleWith_of_lt_irrationalityExponent` that turns the supremum into a usable object.
* `Real.irrationalityExponent_ratCast`: the value `1` at a rational, and
  `Real.two_le_irrationalityExponent`: the bound `2` at an irrational, from Dirichlet's theorem in
  the form `Irrational.liouvilleWith_two`.
* `Real.irrationalityExponent_eq_top_iff`: the exponent is `⊤` exactly at a Liouville number.
* `Real.irrationalityExponent_mobius`: invariance under `ξ ↦ (a ξ + b) / (c ξ + d)` for a rational
  matrix of nonzero determinant, and the special cases it is assembled from
  (`Real.irrationalityExponent_add_rat`, `_mul_rat`, `_neg`, `_inv`). The inversion rests on
  `LiouvilleWith.inv`, which Mathlib does not have.
* `Real.le_irrationalityExponent_iff`: the characterization with no constant in front of
  `n ^ (-ν)`, and `Real.liouvilleWith_iff_frequently_max`: the one with the naive height
  `max |m| n` of the fraction in place of its denominator.

## Implementation notes

⚠ **Mathlib has Dirichlet's theorem but not in this shape, and the gap is not the approximation —
it is the denominator.** `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` produces
infinitely many `q` with `|ξ - q| < 1 / q.den ^ 2`, but `LiouvilleWith` quantifies over
denominators along `atTop`, and an infinite set of rationals is not visibly a set with unbounded
denominators: seeing that it is needs the finiteness of the rationals of bounded height in a
bounded interval. `Irrational.liouvilleWith_two` avoids that argument entirely, because
`LiouvilleWith` does **not** ask `m / n` to be in lowest terms: one Dirichlet approximation with
denominator `d ≤ n` is *inflated* to the denominator `d * t ≥ N` by multiplying numerator and
denominator by `t = N / d + 1`, and its quality `1 / ((n + 1) * d)` survives the inflation exactly
when `d * t ^ 2 < 4 * (n + 1)`, which `n = N ^ 2 + 1` guarantees. The constant is `4` and it is not
sharp.

⚠ **`LiouvilleWith` has no `inv` in Mathlib, and that single lemma is the whole cost of the Möbius
invariance.** The affine part is Mathlib's, ready-made: `LiouvilleWith.add_rat_iff`, `mul_rat_iff`
and `neg_iff` transport the exponent through `ξ ↦ (a ξ + b) / d` with no work at all, and
`irrationalityExponent_mobius` is then the partial-fraction identity
`(a ξ + b) / (c ξ + d) = (ξ + d / c)⁻¹ * ((b c - a d) / c ^ 2) + a / c` read as a composition of
four maps.

⚠ **The frequently-transfer is what `LiouvilleWith.inv` costs, not the inequality.** The
approximations to `ξ⁻¹` are indexed by the *numerators* `m` of the approximations to `ξ`, so the
target's `atTop` is a different filter, and `m ≥ n ξ / 2` holds only past the threshold
`C / n ^ p ≤ ξ / 2`. Reaching that threshold uses `n ≤ n ^ p`, which is where the hypothesis
`1 < p` enters; below it the statement is free from `liouvilleWith_one`. Reducing to `0 < ξ`
through `LiouvilleWith.neg_iff` removes all the sign bookkeeping: the new denominator is then `m`
itself and not `|m|`.

⚠ **Replacing the denominator by the naive height changes only the constant.** Since
`n ≤ max |m| n ≤ (|ξ| + C + 1) * n` for every approximation of quality `C`, the two conditions
differ by a factor `(|ξ| + C + 1) ^ μ`, which `LiouvilleWith` absorbs. So there is no separate
"height exponent"; `Real.liouvilleWith_iff_frequently_max` is the statement that there is nothing
to prove here beyond two `rpow` monotonicities.

⚠ **`Real.le_irrationalityExponent_iff` needs `0 < μ`.** At `μ = 0` its right-hand side
quantifies over negative `ν`, where `n ^ (-ν)` grows without bound and the condition says
something about *bad* approximations; it is true, and it is not about the exponent.

## References

Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), Chapter 1;
E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Section 1.

This is the first half of Layer 1.1 of the `DiophantineApproximation` roadmap.
-/

public section

open Filter
open scoped ENNReal NNReal

namespace Real

/-- The **irrationality exponent** of a real number `ξ`: the supremum of the `p` with
`LiouvilleWith p ξ`, that is, of the orders to which `ξ` is approximable by rationals. It is
`ℝ≥0∞`-valued, in the shape of `dimH`; the value `⊤` is the exponent of a Liouville number. -/
@[expose] noncomputable def irrationalityExponent (ξ : ℝ) : ℝ≥0∞ :=
  ⨆ (p : ℝ≥0) (_ : LiouvilleWith p ξ), (p : ℝ≥0∞)

variable {ξ : ℝ}

theorem le_irrationalityExponent {p : ℝ≥0} (h : LiouvilleWith p ξ) :
    (p : ℝ≥0∞) ≤ irrationalityExponent ξ :=
  le_iSup₂ (f := fun (p : ℝ≥0) (_ : LiouvilleWith p ξ) ↦ (p : ℝ≥0∞)) p h

theorem irrationalityExponent_le_iff {c : ℝ≥0∞} :
    irrationalityExponent ξ ≤ c ↔ ∀ p : ℝ≥0, LiouvilleWith p ξ → (p : ℝ≥0∞) ≤ c :=
  iSup₂_le_iff

theorem one_le_irrationalityExponent (ξ : ℝ) : 1 ≤ irrationalityExponent ξ := by
  simpa using le_irrationalityExponent (p := 1) (liouvilleWith_one ξ)

theorem liouvilleWith_of_lt_irrationalityExponent {p : ℝ}
    (h : ENNReal.ofReal p < irrationalityExponent ξ) : LiouvilleWith p ξ := by
  rcases le_or_gt p 0 with hp | hp
  · exact (liouvilleWith_one ξ).mono (hp.trans zero_le_one)
  · by_contra hcon
    refine absurd (irrationalityExponent_le_iff.2 fun q hq ↦ ?_) (not_le.2 h)
    rw [← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    by_contra hqp
    exact hcon (hq.mono (le_of_not_ge hqp))

theorem irrationalityExponent_eq_top_iff : irrationalityExponent ξ = ⊤ ↔ Liouville ξ := by
  rw [← forall_liouvilleWith_iff]
  refine ⟨fun h p ↦ liouvilleWith_of_lt_irrationalityExponent ?_, fun h ↦ ?_⟩
  · rw [h]; exact ENNReal.ofReal_lt_top
  · exact ENNReal.eq_top_of_forall_nnreal_le fun r ↦ le_irrationalityExponent (h r)

theorem irrationalityExponent_eq_one_of_not_irrational (h : ¬ Irrational ξ) :
    irrationalityExponent ξ = 1 :=
  le_antisymm (irrationalityExponent_le_iff.2 fun p hp ↦ by
    by_contra hlt
    exact h (hp.irrational (by exact_mod_cast not_le.1 hlt)))
    (one_le_irrationalityExponent ξ)

@[simp] theorem irrationalityExponent_ratCast (q : ℚ) : irrationalityExponent (q : ℝ) = 1 :=
  irrationalityExponent_eq_one_of_not_irrational (by simp [Rat.not_irrational])

/-!
### The lower bound `2`, from Dirichlet's theorem
-/

/-- **Dirichlet's theorem**, in the shape `LiouvilleWith` asks for. -/
theorem _root_.Irrational.liouvilleWith_two {ξ : ℝ} (hξ : Irrational ξ) : LiouvilleWith 2 ξ := by
  refine ⟨4, frequently_atTop.2 fun N ↦ ?_⟩
  obtain ⟨q, hq, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le ξ (n := N ^ 2 + 1) (by positivity)
  set d : ℕ := q.den with hd
  set t : ℕ := N / d + 1 with ht
  have hd0 : 0 < d := q.pos
  have ht0 : 0 < t := Nat.succ_pos _
  have hNdt : N < d * t := by
    have h1 := Nat.div_add_mod N d
    have h2 := Nat.mod_lt N hd0
    rw [ht, Nat.mul_add, mul_one]
    omega
  have hdt : d * t ≤ N + d := by
    rw [ht, Nat.mul_add, mul_one]
    exact Nat.add_le_add_right (by rw [mul_comm]; exact Nat.div_mul_le_self N d) d
  have hcast : ((q.num * t : ℤ) : ℝ) / ((d * t : ℕ) : ℝ) = (q : ℝ) := by
    have ht' : ((t : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht0.ne'
    have hd' : ((d : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
    push_cast
    rw [Rat.cast_def]
    field_simp
    ring
  refine ⟨d * t, hNdt.le, q.num * t, ?_, ?_⟩
  · rw [hcast]
    exact hξ.ne_rat q
  · rw [hcast, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hD0 : (0 : ℝ) < d := Nat.cast_pos.mpr hd0
    have hT0 : (0 : ℝ) < t := Nat.cast_pos.mpr ht0
    have key : (d : ℝ) * t * t < 4 * ((N : ℝ) ^ 2 + 2) := by
      have hD1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
      have hDn : (d : ℝ) ≤ (N : ℝ) ^ 2 + 1 := by exact_mod_cast hden
      have hDT : (d : ℝ) * t ≤ (N : ℝ) + d := by exact_mod_cast hdt
      have step : (d : ℝ) * ((d : ℝ) * t * t) < (d : ℝ) * (4 * ((N : ℝ) ^ 2 + 2)) := by
        have hsq : ((d : ℝ) * t) ^ 2 ≤ ((N : ℝ) + d) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hDT 2
        rcases Nat.eq_zero_or_pos N with hN | hN
        · subst hN
          have : (d : ℝ) = 1 := by
            have : d ≤ 1 := by simpa using hden
            have : d = 1 := le_antisymm this hd0
            exact_mod_cast this
          simp only [this] at *
          push_cast at *
          nlinarith [hsq]
        · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
          nlinarith [hsq, mul_nonneg (sub_nonneg.2 hDn) (le_of_lt hD0),
            mul_nonneg (sub_nonneg.2 hD1) (sq_nonneg (N : ℝ))]
      exact lt_of_mul_lt_mul_left step hD0.le
    rw [lt_div_iff₀ (by positivity)]
    have h1 : |ξ - (q : ℝ)| * ((d * t : ℕ) : ℝ) ^ 2
        ≤ (1 / ((((N ^ 2 + 1 : ℕ) : ℝ) + 1) * (d : ℝ))) * ((d * t : ℕ) : ℝ) ^ 2 := by gcongr
    refine lt_of_le_of_lt h1 ?_
    rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ (by positivity)]
    push_cast
    nlinarith [mul_lt_mul_of_pos_left key hD0, hD0, hT0]

theorem two_le_irrationalityExponent (hξ : Irrational ξ) : 2 ≤ irrationalityExponent ξ := by
  have h : LiouvilleWith ((2 : ℝ≥0) : ℝ) ξ := by
    simpa using hξ.liouvilleWith_two
  simpa using le_irrationalityExponent h

/-!
### Invariance under the rational Möbius group
-/

end Real

namespace LiouvilleWith

variable {p ξ : ℝ}

private theorem inv_of_pos (hp : 1 < p) (hξ : 0 < ξ) (h : LiouvilleWith p ξ) :
    LiouvilleWith p ξ⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := h.exists_pos
  have hs : 0 < p - 1 := by linarith
  set A : ℝ := (3 * ξ / 2) ^ (p - 1) with hA
  have hA0 : 0 < A := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨C * A / ξ + 1, frequently_atTop.2 fun K ↦ ?_⟩
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max (2 * C / ξ) (2 * K / ξ))
  obtain ⟨n, hnN, hn1, m, hne, hlt⟩ := frequently_atTop.1 hC (max N₀ 1)
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right N₀ 1) hnN
  have hn0 : (0 : ℝ) < n := by linarith
  have hNn : (N₀ : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left N₀ 1) hnN
  have hCn : 2 * C / ξ ≤ (n : ℝ) := le_trans (le_trans (le_max_left _ _) hN₀) hNn
  have hKn : 2 * K / ξ ≤ (n : ℝ) := le_trans (le_trans (le_max_right _ _) hN₀) hNn
  have hnp0 : (0 : ℝ) < (n : ℝ) ^ p := Real.rpow_pos_of_pos hn0 p
  have hnsplit : (n : ℝ) * (n : ℝ) ^ (p - 1) = (n : ℝ) ^ p := by
    nth_rewrite 1 [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  have hnp1 : (n : ℝ) ≤ (n : ℝ) ^ p := by
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (n : ℝ) ^ p := Real.rpow_le_rpow_of_exponent_le hn1' hp.le
  have hhalf : C / (n : ℝ) ^ p ≤ ξ / 2 := by
    rw [div_le_iff₀ hnp0]
    have h1 : 2 * C / ξ ≤ (n : ℝ) ^ p := le_trans hCn hnp1
    rw [div_le_iff₀ hξ] at h1
    nlinarith
  have hmn : |ξ - (m : ℝ) / (n : ℝ)| < ξ / 2 := lt_of_lt_of_le hlt hhalf
  obtain ⟨hlo, hhi⟩ := abs_lt.1 hmn
  have hmlo : (n : ℝ) * ξ / 2 < (m : ℝ) := by
    have h2 : ξ / 2 < (m : ℝ) / (n : ℝ) := by linarith
    rw [lt_div_iff₀ hn0] at h2
    linarith
  have hmhi : (m : ℝ) < 3 * (n : ℝ) * ξ / 2 := by
    have h2 : (m : ℝ) / (n : ℝ) < 3 * ξ / 2 := by linarith
    rw [div_lt_iff₀ hn0] at h2
    linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := by nlinarith
  have hmz : 0 < m := by exact_mod_cast hm0
  have hk : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hmz.le]
  have hKm : (K : ℝ) ≤ (m : ℝ) := by
    rw [div_le_iff₀ hξ] at hKn
    nlinarith
  refine ⟨m.toNat, by exact_mod_cast hk ▸ hKm, (n : ℤ), ?_, ?_⟩
  · rw [hk]
    intro hcon
    refine hne ?_
    push_cast at hcon ⊢
    rw [← inv_inv ξ, hcon, inv_div]
  · rw [hk, lt_div_iff₀ (Real.rpow_pos_of_pos hm0 p)]
    have hmsplit : (m : ℝ) ^ (p - 1) * (m : ℝ) = (m : ℝ) ^ p := by
      nth_rewrite 2 [← Real.rpow_one (m : ℝ)]
      rw [← Real.rpow_add hm0]
      congr 1
      ring
    have e2 : |ξ⁻¹ - ((n : ℤ) : ℝ) / (m : ℝ)| = |(m : ℝ) - (n : ℝ) * ξ| / (ξ * (m : ℝ)) := by
      have e1 : ξ⁻¹ - ((n : ℤ) : ℝ) / (m : ℝ) = ((m : ℝ) - (n : ℝ) * ξ) / (ξ * (m : ℝ)) := by
        push_cast
        field_simp
      rw [e1, abs_div, abs_of_pos (show (0 : ℝ) < ξ * (m : ℝ) by positivity)]
    have e3 : |(m : ℝ) - (n : ℝ) * ξ| = (n : ℝ) * |ξ - (m : ℝ) / (n : ℝ)| := by
      rw [abs_sub_comm, show (n : ℝ) * ξ - (m : ℝ) = (n : ℝ) * (ξ - (m : ℝ) / (n : ℝ)) by
        field_simp, abs_mul, abs_of_pos hn0]
    have e4 : |(m : ℝ) - (n : ℝ) * ξ| < C / (n : ℝ) ^ (p - 1) := by
      rw [e3]
      have h5 : (n : ℝ) * |ξ - (m : ℝ) / (n : ℝ)| < (n : ℝ) * (C / (n : ℝ) ^ p) :=
        mul_lt_mul_of_pos_left hlt hn0
      refine lt_of_lt_of_le h5 (le_of_eq ?_)
      rw [← hnsplit]
      field_simp
    have hmp : (m : ℝ) ^ (p - 1) < A * (n : ℝ) ^ (p - 1) := by
      have h1 : (m : ℝ) ^ (p - 1) < (3 * (n : ℝ) * ξ / 2) ^ (p - 1) :=
        Real.rpow_lt_rpow hm0.le hmhi hs
      rwa [show 3 * (n : ℝ) * ξ / 2 = (3 * ξ / 2) * (n : ℝ) by ring,
        Real.mul_rpow (by positivity) hn0.le] at h1
    have hnp1' : (0 : ℝ) < (n : ℝ) ^ (p - 1) := Real.rpow_pos_of_pos hn0 _
    calc |ξ⁻¹ - ((n : ℤ) : ℝ) / (m : ℝ)| * (m : ℝ) ^ p
        = |(m : ℝ) - (n : ℝ) * ξ| * (m : ℝ) ^ (p - 1) / ξ := by
          rw [e2, ← hmsplit]
          field_simp
      _ < (C / (n : ℝ) ^ (p - 1)) * (A * (n : ℝ) ^ (p - 1)) / ξ := by
          gcongr
      _ = C * A / ξ := by field_simp
      _ < C * A / ξ + 1 := by linarith

protected theorem inv (hξ : Irrational ξ) (h : LiouvilleWith p ξ) : LiouvilleWith p ξ⁻¹ := by
  rcases le_or_gt p 1 with hp | hp
  · exact (liouvilleWith_one _).mono hp
  · rcases lt_trichotomy ξ 0 with hneg | hzero | hpos
    · have h2 : LiouvilleWith p (-ξ)⁻¹ := inv_of_pos hp (by linarith) h.neg
      rw [inv_neg] at h2
      exact neg_iff.1 h2
    · exact absurd (hzero ▸ hξ) not_irrational_zero
    · exact inv_of_pos hp hpos h

theorem inv_iff (hξ : Irrational ξ) : LiouvilleWith p ξ⁻¹ ↔ LiouvilleWith p ξ :=
  ⟨fun h ↦ by simpa using h.inv hξ.inv, fun h ↦ h.inv hξ⟩

end LiouvilleWith

namespace Real

variable {ξ : ℝ}

theorem irrationalityExponent_congr {ξ η : ℝ}
    (h : ∀ p : ℝ, LiouvilleWith p ξ ↔ LiouvilleWith p η) :
    irrationalityExponent ξ = irrationalityExponent η := by
  simp only [irrationalityExponent]
  exact iSup_congr fun p ↦ iSup_congr_Prop (h p) fun _ ↦ rfl

theorem irrationalityExponent_add_rat (ξ : ℝ) (r : ℚ) :
    irrationalityExponent (ξ + r) = irrationalityExponent ξ :=
  irrationalityExponent_congr fun _ ↦ LiouvilleWith.add_rat_iff

theorem irrationalityExponent_rat_add (ξ : ℝ) (r : ℚ) :
    irrationalityExponent ((r : ℝ) + ξ) = irrationalityExponent ξ :=
  irrationalityExponent_congr fun _ ↦ LiouvilleWith.rat_add_iff

theorem irrationalityExponent_mul_rat (ξ : ℝ) {r : ℚ} (hr : r ≠ 0) :
    irrationalityExponent (ξ * r) = irrationalityExponent ξ :=
  irrationalityExponent_congr fun _ ↦ LiouvilleWith.mul_rat_iff hr

theorem irrationalityExponent_neg (ξ : ℝ) :
    irrationalityExponent (-ξ) = irrationalityExponent ξ :=
  irrationalityExponent_congr fun _ ↦ LiouvilleWith.neg_iff

theorem irrationalityExponent_inv (ξ : ℝ) :
    irrationalityExponent ξ⁻¹ = irrationalityExponent ξ := by
  rcases em (Irrational ξ) with hξ | hξ
  · exact irrationalityExponent_congr fun _ ↦ LiouvilleWith.inv_iff hξ
  · obtain ⟨q, rfl⟩ := exists_rat_of_not_irrational hξ
    rw [← Rat.cast_inv, irrationalityExponent_ratCast, irrationalityExponent_ratCast]

theorem irrationalityExponent_mobius (ξ : ℝ) {a b c d : ℚ} (hdet : a * d - b * c ≠ 0)
    (hden : (c : ℝ) * ξ + d ≠ 0) :
    irrationalityExponent (((a : ℝ) * ξ + b) / ((c : ℝ) * ξ + d)) = irrationalityExponent ξ := by
  rcases eq_or_ne c 0 with rfl | hc
  · have hd : (d : ℝ) ≠ 0 := by simpa using hden
    have hdq : d ≠ 0 := Rat.cast_ne_zero.1 hd
    have ha : a ≠ 0 := fun h ↦ hdet (by rw [h]; ring)
    have key : ((a : ℝ) * ξ + b) / (((0 : ℚ) : ℝ) * ξ + d)
        = ξ * ((a / d : ℚ) : ℝ) + ((b / d : ℚ) : ℝ) := by
      push_cast
      rw [zero_mul, zero_add]
      field_simp
    rw [key, irrationalityExponent_add_rat, irrationalityExponent_mul_rat _ (div_ne_zero ha hdq)]
  · have hcR : (c : ℝ) ≠ 0 := Rat.cast_ne_zero.2 hc
    have hx : ξ + ((d / c : ℚ) : ℝ) ≠ 0 := by
      intro h
      refine hden ?_
      have hξ' : ξ = -((d : ℝ) / (c : ℝ)) := by push_cast at h; linarith
      rw [hξ']
      field_simp
      ring
    have hr : (b * c - a * d) / c ^ 2 ≠ 0 :=
      div_ne_zero (fun h ↦ hdet (by linear_combination -h)) (pow_ne_zero 2 hc)
    have hden' : ξ * (c : ℝ) + (d : ℝ) ≠ 0 := by rw [mul_comm]; exact hden
    have key : ((a : ℝ) * ξ + b) / ((c : ℝ) * ξ + d)
        = (ξ + ((d / c : ℚ) : ℝ))⁻¹ * (((b * c - a * d) / c ^ 2 : ℚ) : ℝ) + ((a / c : ℚ) : ℝ) := by
      push_cast
      push_cast at hx
      field_simp [hden']
      ring
    rw [key, irrationalityExponent_add_rat, irrationalityExponent_mul_rat _ hr,
      irrationalityExponent_inv, irrationalityExponent_add_rat]

/-!
### Characterizations by the quality of rational approximations
-/

theorem le_irrationalityExponent_of_frequently {μ C : ℝ}
    (h : ∃ᶠ n : ℕ in atTop, ∃ m : ℤ, ξ ≠ m / n ∧ |ξ - m / n| < C / (n : ℝ) ^ μ) :
    ENNReal.ofReal μ ≤ irrationalityExponent ξ := by
  rcases le_or_gt μ 0 with hμ | hμ
  · simp [ENNReal.ofReal_of_nonpos hμ]
  · have hlw : LiouvilleWith ((μ.toNNReal : ℝ≥0) : ℝ) ξ := by
      rw [Real.coe_toNNReal μ hμ.le]
      exact ⟨C, h⟩
    exact le_irrationalityExponent hlw

theorem frequently_lt_rpow_neg_of_lt_irrationalityExponent {μ : ℝ}
    (h : ENNReal.ofReal μ < irrationalityExponent ξ) :
    ∃ᶠ n : ℕ in atTop, ∃ m : ℤ, ξ ≠ m / n ∧ |ξ - m / n| < (n : ℝ) ^ (-μ) := by
  rw [irrationalityExponent, lt_iSup_iff] at h
  obtain ⟨q, hq⟩ := h
  rw [lt_iSup_iff] at hq
  obtain ⟨hlw, hlt⟩ := hq
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff'] at hlt
  exact hlw.frequently_lt_rpow_neg hlt.1

/-- The irrationality exponent, read off the approximations with **no constant** in front of
`q ^ (-ν)`: the constant of `LiouvilleWith` can always be absorbed by decreasing the exponent. -/
theorem le_irrationalityExponent_iff {μ : ℝ≥0} (hμ : 0 < μ) :
    (μ : ℝ≥0∞) ≤ irrationalityExponent ξ ↔
      ∀ ν : ℝ, ν < μ → ∃ᶠ n : ℕ in atTop, ∃ m : ℤ,
        ξ ≠ m / n ∧ |ξ - m / n| < (n : ℝ) ^ (-ν) := by
  refine ⟨fun h ν hν ↦ frequently_lt_rpow_neg_of_lt_irrationalityExponent ?_, fun h ↦ ?_⟩
  · refine lt_of_lt_of_le ?_ h
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff']
    exact ⟨hν, by exact_mod_cast hμ⟩
  · refine le_of_forall_lt_imp_le_of_dense fun a ha ↦ ?_
    lift a to ℝ≥0 using ne_top_of_lt ha
    have ha' : (a : ℝ) < (μ : ℝ) := by exact_mod_cast ha
    have hfr := h a ha'
    have := le_irrationalityExponent_of_frequently (C := 1) (μ := (a : ℝ))
      (hfr.mono fun n hn ↦ by
        obtain ⟨m, hne, hmn⟩ := hn
        exact ⟨m, hne, by rwa [Real.rpow_neg (Nat.cast_nonneg n), ← one_div] at hmn⟩)
    rwa [ENNReal.ofReal_coe_nnreal] at this

/-- **The naive height in place of the denominator.** Replacing `n` by the naive height
`max |m| n` of the fraction `m / n` changes the admissible constants and nothing else, so it
changes neither `LiouvilleWith` nor the irrationality exponent. -/
theorem liouvilleWith_iff_frequently_max {μ : ℝ} (hμ : 0 ≤ μ) :
    LiouvilleWith μ ξ ↔ ∃ C : ℝ, ∃ᶠ n : ℕ in atTop, ∃ m : ℤ,
      ξ ≠ m / n ∧ |ξ - m / n| < C / (max |(m : ℝ)| n) ^ μ := by
  constructor
  · intro h
    obtain ⟨C, hC0, hC⟩ := h.exists_pos
    refine ⟨C * (|ξ| + C + 1) ^ μ, hC.mono ?_⟩
    rintro n ⟨hn1, m, hne, hlt⟩
    refine ⟨m, hne, ?_⟩
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hn0 : (0 : ℝ) < n := by linarith
    have hnμ : (1 : ℝ) ≤ (n : ℝ) ^ μ := Real.one_le_rpow hn1' hμ
    have hnμ0 : (0 : ℝ) < (n : ℝ) ^ μ := by linarith
    have hCn : C / (n : ℝ) ^ μ ≤ C := by
      rw [div_le_iff₀ hnμ0]
      nlinarith
    have h1 : |(m : ℝ) / (n : ℝ)| ≤ |ξ| + C := by
      have h2 := abs_sub_abs_le_abs_sub ((m : ℝ) / (n : ℝ)) ξ
      rw [abs_sub_comm ((m : ℝ) / (n : ℝ)) ξ] at h2
      linarith [hlt.le]
    have hmle : |(m : ℝ)| ≤ (n : ℝ) * (|ξ| + C) := by
      rw [abs_div, abs_of_pos hn0, div_le_iff₀ hn0] at h1
      linarith
    have hmax : max |(m : ℝ)| (n : ℝ) ≤ (n : ℝ) * (|ξ| + C + 1) := by
      refine max_le (by nlinarith [abs_nonneg ξ]) ?_
      nlinarith [abs_nonneg ξ]
    have hmaxpos : (0 : ℝ) < max |(m : ℝ)| (n : ℝ) := lt_of_lt_of_le hn0 (le_max_right _ _)
    have hmaxμ0 : (0 : ℝ) < (max |(m : ℝ)| (n : ℝ)) ^ μ := Real.rpow_pos_of_pos hmaxpos _
    have hkey : (max |(m : ℝ)| (n : ℝ)) ^ μ ≤ (n : ℝ) ^ μ * (|ξ| + C + 1) ^ μ := by
      rw [← Real.mul_rpow hn0.le (by positivity)]
      exact Real.rpow_le_rpow hmaxpos.le hmax hμ
    refine lt_of_lt_of_le hlt ?_
    rw [div_le_div_iff₀ hnμ0 hmaxμ0]
    calc C * (max |(m : ℝ)| (n : ℝ)) ^ μ ≤ C * ((n : ℝ) ^ μ * (|ξ| + C + 1) ^ μ) := by
          gcongr
      _ = C * (|ξ| + C + 1) ^ μ * (n : ℝ) ^ μ := by ring
  · rintro ⟨C, hC⟩
    refine ⟨max C 1, ((eventually_ge_atTop 1).and_frequently hC).mono ?_⟩
    rintro n ⟨hn1, m, hne, hlt⟩
    refine ⟨m, hne, lt_of_lt_of_le hlt ?_⟩
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hn0 : (0 : ℝ) < n := by linarith
    have hnμ0 : (0 : ℝ) < (n : ℝ) ^ μ := Real.rpow_pos_of_pos hn0 _
    have hmaxpos : (0 : ℝ) < max |(m : ℝ)| (n : ℝ) := lt_of_lt_of_le hn0 (le_max_right _ _)
    have hmaxμ0 : (0 : ℝ) < (max |(m : ℝ)| (n : ℝ)) ^ μ := Real.rpow_pos_of_pos hmaxpos _
    have hmax : (n : ℝ) ^ μ ≤ (max |(m : ℝ)| (n : ℝ)) ^ μ :=
      Real.rpow_le_rpow hn0.le (le_max_right _ _) hμ
    calc C / (max |(m : ℝ)| (n : ℝ)) ^ μ ≤ max C 1 / (max |(m : ℝ)| (n : ℝ)) ^ μ := by
          gcongr
          exact le_max_left _ _
      _ ≤ max C 1 / (n : ℝ) ^ μ :=
          div_le_div_of_nonneg_left (le_trans zero_le_one (le_max_right C 1)) hnμ0 hmax

theorem le_irrationalityExponent_of_frequently_max {μ C : ℝ} (hμ : 0 ≤ μ)
    (h : ∃ᶠ n : ℕ in atTop, ∃ m : ℤ, ξ ≠ m / n ∧ |ξ - m / n| < C / (max |(m : ℝ)| n) ^ μ) :
    ENNReal.ofReal μ ≤ irrationalityExponent ξ := by
  obtain ⟨C', hC'⟩ := (liouvilleWith_iff_frequently_max (ξ := ξ) hμ).2 ⟨C, h⟩
  exact le_irrationalityExponent_of_frequently hC'

/-! ### Acceptance criteria -/

/-- A rational number is approximable to order `1` and no better. -/
example : irrationalityExponent (2 / 3 : ℚ) = 1 := irrationalityExponent_ratCast _

/-- Liouville's constant sits at the top of the scale; `⊤` is a value, not a junk value. -/
example : irrationalityExponent (liouvilleNumber 2) = ⊤ :=
  irrationalityExponent_eq_top_iff.2 (liouville_liouvilleNumber le_rfl)

/-- Dirichlet's bound at a concrete irrational. -/
example : 2 ≤ irrationalityExponent (√2) := two_le_irrationalityExponent irrational_sqrt_two

/-- The exponent is a projective invariant of `ξ` over `ℚ`. -/
example (ξ : ℝ) : irrationalityExponent (1 / ξ) = irrationalityExponent ξ := by
  rw [one_div, irrationalityExponent_inv]

/-- **Rejection test: `Irrational ξ` is needed for the lower bound `2`.** Every real number is
`LiouvilleWith 1`, and a rational one is `LiouvilleWith p` for no `p > 1`, so its exponent is `1`
and the bound fails there. -/
example : ¬ ∀ ξ : ℝ, 2 ≤ irrationalityExponent ξ := by
  intro h
  have h1 := h ((0 : ℚ) : ℝ)
  rw [irrationalityExponent_ratCast] at h1
  exact absurd h1 (by norm_num)

/-- **Rejection test: the determinant hypothesis of `irrationalityExponent_mobius` is
load-bearing.** At `a = b = c = d = 1` the determinant vanishes, the map is constant `1`, and the
exponent of `√2` is not the exponent of `1`. -/
example : ¬ ∀ ξ : ℝ, (1 : ℝ) * ξ + 1 ≠ 0 →
    irrationalityExponent (((1 : ℝ) * ξ + 1) / ((1 : ℝ) * ξ + 1)) = irrationalityExponent ξ := by
  intro h
  have hne : (1 : ℝ) * √2 + 1 ≠ 0 := by positivity
  have h1 := h (√2) hne
  rw [div_self hne] at h1
  have h2 : irrationalityExponent (1 : ℝ) = 1 := by
    simpa using irrationalityExponent_ratCast 1
  rw [h2] at h1
  have h3 := two_le_irrationalityExponent irrational_sqrt_two
  rw [← h1] at h3
  exact absurd h3 (by norm_num)

end Real
