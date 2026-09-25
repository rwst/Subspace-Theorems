/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.BoundedDegreeApproximation
public import DiophantineApproximation.AlgebraicExponent
public import DiophantineApproximation.WirsingThird

-- Used only in the acceptance criteria.
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

/-!
# The exponents of an algebraic number

**Layer 7.3** (Schmidt 1970). Let `α` be a real algebraic number of degree `D`. Then for every
degree bound `n`,

```text
mahlerExponent n α = koksmaExponent n α = min n (D - 1).
```

Both exponents were defined in Layer 1.2 and bounded in Layer 1.3; what Layer 1 could not supply
is the upper bound `w_n(α) ≤ n`, and that is the one new theorem of this file. It is Layer 7.1
applied to the `n + 1` coefficients `1, α, …, α ^ n` and to the coefficient vector of the
polynomial — the proof of Layer 7.2 with its first step, the mean value theorem, deleted.
Everything else is assembly: Liouville's inequality of Layer 1.3 for `w_n(α) ≤ D - 1`, the box
principle of Layer 1.3 for the lower bounds, and Wirsing's third inequality of Layer 1.3 to
transport them from Mahler's exponent to Koksma's.

## Main results

* `Complex.finite_setOf_norm_aeval_le`: **finitely many integer polynomials of degree at most `D`
  take a nonzero value at an algebraic `α` below `H(P) ^ (-D - ε)`** — Layer 7.1 with no mean
  value theorem in front of it.
* `Real.mahlerExponent_le_natCast_of_isAlgebraic`: `w_n(α) ≤ n`, the same read in the language of
  Layer 1.3.
* `Real.aeval_ne_zero_of_natDegree_lt`: below the degree of the minimal polynomial, no nonzero
  integer polynomial vanishes — the hypothesis the box principle is stated with.
* `Real.natCast_le_koksmaExponent_of_natDegree_lt`: `n ≤ w_n^*(α)` for `n < D`, Wirsing's third
  inequality at the value the box principle forces.
* `Real.mahlerExponent_eq_of_isAlgebraic` and `Real.koksmaExponent_eq_of_isAlgebraic`:
  **the milestone**, `w_n(α) = w_n^*(α) = min n (D - 1)`.

## Implementation notes

⚠ **The hypothesis `1 ≤ n` of the prototype is not needed.** At `n = 0` both sides vanish:
`min 0 (D - 1) = 0`, no integer polynomial of degree `0` takes a nonzero value below its own
height, and the upper bound proved here covers that case with no separate argument. The
prototype carried `1 ≤ n` because Wirsing's first two inequalities need it; the milestone does
not, and the statements below are free of it.

⚠ **The name `Real.mahlerExponent_le_of_isAlgebraic` was taken, by the other upper bound.** Layer
1.3 proved `w_n(α) ≤ D - 1` under exactly the hypothesis `IsAlgebraic ℚ α`, so the bound proved
here, `w_n(α) ≤ n`, had to be named for its conclusion instead. The two are incomparable — the
first is what decides the milestone for `n ≥ D`, the second for `n ≤ D - 1` — and the proof of
the milestone is the case split between them.

⚠ **The conjugates of `α` cost nothing here, unlike in Layer 7.2.** Layer 7.1 needs a nonzero
value, and `Real.mahlerSet` asks for one in its definition: the polynomials that vanish at `α`
are excluded from the count by the statement itself, so neither the rigidity of the minimal
polynomial nor Northcott's theorem is needed, and with them goes the threshold height that Layer
7.2's proof had to carry. What is left of that proof is the height comparison
`Rat.mulHeight_coeff_le_supNorm` and one application of Layer 7.1.

⚠ **The lower bounds are the box principle, and they are one theorem applied twice.** For
`n ≤ D - 1` the box principle gives `n ≤ w_n(α)` directly; for `n ≥ D - 1` it gives
`D - 1 ≤ w_{D-1}(α)`, and monotonicity in the degree carries that up to `n`. The same two
applications serve Koksma's exponent through
`Real.natCast_le_koksmaExponent_of_natDegree_lt`, which is Wirsing's third inequality
`w_n ≤ w_n^* (w_n + 1 - n)` at the value `w_n = n`.

⚠ **At `n = 1` the milestone is Roth's theorem**, and the acceptance criteria check it: for a
real algebraic irrational the minimal polynomial has degree at least two, so
`min 1 (D - 1) = 1`, and `Real.mahlerExponent_one_add_one` turns that into
`irrationalityExponent α = 2`. Layer 3 is not used anywhere in the proof — the road taken here
runs through Layer 6 and Layer 7.1 instead — so this is a second, independent proof of Roth's
theorem inside the same library.

## References

W.M. Schmidt, *Simultaneous approximation to algebraic numbers by elements of a number field*,
Monatshefte für Mathematik **79** (1970), 55–66. E. Bombieri and W. Gubler, *Heights in
Diophantine Geometry*, Cambridge University Press (2006), Corollary 7.3.5 and Remark 7.3.4.
Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), §2.4.

This is part of Layer 7.3 of the `DiophantineApproximation` roadmap.
-/

public section

open Finset Height Polynomial
open scoped ENNReal

namespace Complex

/-- **Layer 7.1 with the mean value theorem deleted.** For a complex algebraic `α`, a degree
bound `D` and `ε > 0`, only finitely many integer polynomials of degree at most `D` take a
nonzero value at `α` with `‖P α‖ ≤ H(P) ^ (-D - ε)`. This is the upper bound on Mahler's
exponent: the coefficient vector of `P` is an integer point at which the linear form with the
algebraic coefficients `1, α, …, α ^ D` is small. -/
theorem finite_setOf_norm_aeval_le {α : ℂ} (hα : IsAlgebraic ℚ α) (D : ℕ) {ε : ℝ} (hε : 0 < ε) :
    {P : ℤ[X] | P.natDegree ≤ D ∧ aeval α P ≠ 0 ∧
      ‖aeval α P‖ ≤ P.supNorm ^ (-(D : ℝ) - ε)}.Finite := by
  classical
  set T : Set (Fin (D + 1) → ℤ) :=
    {x | 0 < ‖∑ i : Fin (D + 1), α ^ (i : ℕ) * ((x i : ℤ) : ℂ)‖ ∧
      ‖∑ i : Fin (D + 1), α ^ (i : ℕ) * ((x i : ℤ) : ℂ)‖
        ≤ mulHeight (fun i ↦ ((x i : ℤ) : ℚ)) ^ (-(D : ℝ) - ε)} with hTdef
  have hT : T.Finite :=
    Complex.finite_setOf_norm_sum_mul_le_fin
      (α := fun i : Fin (D + 1) ↦ α ^ (i : ℕ))
      (fun i ↦ (hα.isIntegral.pow (i : ℕ)).isAlgebraic) hε
  refine Set.Finite.of_finite_image
    (f := fun P : ℤ[X] ↦ fun i : Fin (D + 1) ↦ P.coeff (i : ℕ)) ?_ ?_
  · refine hT.subset ?_
    rintro _ ⟨P, ⟨hdeg, hne, hle⟩, rfl⟩
    have hP0 : P ≠ 0 := fun h ↦ hne (by rw [h, map_zero])
    have hH1 : (1 : ℝ) ≤ P.supNorm := Polynomial.one_le_supNorm hP0
    have hxne : (fun i : Fin (D + 1) ↦ ((P.coeff (i : ℕ) : ℤ) : ℚ)) ≠ 0 := by
      intro h
      refine hP0 (Polynomial.ext fun i ↦ ?_)
      rw [coeff_zero]
      rcases le_or_gt i D with hi | hi
      · have hc := congrFun h ⟨i, Nat.lt_succ_of_le hi⟩
        simp only [Pi.zero_apply] at hc
        exact_mod_cast hc
      · exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hi)
    have hmh : mulHeight (fun i : Fin (D + 1) ↦ ((P.coeff (i : ℕ) : ℤ) : ℚ)) ≤ P.supNorm :=
      Rat.mulHeight_coeff_le_supNorm hxne
    have hmh1 : (1 : ℝ) ≤ mulHeight (fun i : Fin (D + 1) ↦ ((P.coeff (i : ℕ) : ℤ) : ℚ)) :=
      Height.one_le_mulHeight _
    have hcmp : P.supNorm ^ (-(D : ℝ) - ε)
        ≤ mulHeight (fun i : Fin (D + 1) ↦ ((P.coeff (i : ℕ) : ℤ) : ℚ)) ^ (-(D : ℝ) - ε) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hmh
        (by linarith [Nat.cast_nonneg (α := ℝ) D])
    have hsum : ∑ i : Fin (D + 1), α ^ (i : ℕ) * ((P.coeff (i : ℕ) : ℤ) : ℂ) = aeval α P :=
      (Polynomial.aeval_eq_sum_fin hdeg α).symm
    exact ⟨by rw [hsum]; exact norm_pos_iff.mpr hne, by rw [hsum]; exact hle.trans hcmp⟩
  · rintro Q hQ R hR hQR
    ext i
    rcases le_or_gt i D with hi | hi
    · exact congrFun hQR ⟨i, Nat.lt_succ_of_le hi⟩
    · rw [coeff_eq_zero_of_natDegree_lt (hQ.1.trans_lt hi),
        coeff_eq_zero_of_natDegree_lt (hR.1.trans_lt hi)]

end Complex

namespace Real

/-- **Mahler's exponent of a real algebraic number is at most the degree bound**, `w_n(α) ≤ n`.
This is the upper bound Layer 1 could not supply, and the only new theorem Layer 7.3 needs. -/
theorem mahlerExponent_le_natCast_of_isAlgebraic {α : ℝ} (hα : IsAlgebraic ℚ α) (n : ℕ) :
    mahlerExponent n α ≤ (n : ℝ≥0∞) := by
  refine mahlerExponent_le_iff.2 fun w hinf ↦ ?_
  by_contra hlt
  push Not at hlt
  have hlt' : (n : ℝ) < (w : ℝ) := by exact_mod_cast hlt
  have hε : (0 : ℝ) < (w : ℝ) - n := by linarith
  have halg : IsAlgebraic ℚ ((α : ℝ) : ℂ) := hα.algebraMap
  refine hinf (Set.Finite.subset (Complex.finite_setOf_norm_aeval_le halg n hε) ?_)
  rintro P ⟨hdeg, hpos, hle⟩
  have hcast : aeval ((α : ℝ) : ℂ) P = ((aeval α P : ℝ) : ℂ) := by
    rw [show (((α : ℝ)) : ℂ) = IsScalarTower.toAlgHom ℤ ℝ ℂ α from rfl,
      Polynomial.aeval_algHom_apply]
    rfl
  refine ⟨hdeg, ?_, ?_⟩
  · rw [hcast]
    simpa using abs_pos.mp hpos
  · rw [hcast, Complex.norm_real, show -(n : ℝ) - ((w : ℝ) - n) = -(w : ℝ) by ring]
    exact hle

/-- **Below the degree of the minimal polynomial nothing vanishes.** If `m` is smaller than the
degree of `minpoly ℚ α`, no nonzero integer polynomial of degree at most `m` has `α` as a root —
the hypothesis in which Layer 1.3 states the box principle. -/
theorem aeval_ne_zero_of_natDegree_lt {α : ℝ} {m : ℕ} (hm : m < (minpoly ℚ α).natDegree)
    {P : ℤ[X]} (hP0 : P ≠ 0) (hdeg : P.natDegree ≤ m) : aeval α P ≠ 0 := by
  intro h
  have hinj : Function.Injective (Int.castRingHom ℚ) := (Int.castRingHom ℚ).injective_int
  have hQ0 : P.map (Int.castRingHom ℚ) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).2 hP0
  have hQ : aeval α (P.map (Int.castRingHom ℚ)) = 0 := by
    rw [show (Int.castRingHom ℚ) = algebraMap ℤ ℚ from rfl, aeval_map_algebraMap]
    exact h
  have hdle := Polynomial.natDegree_le_natDegree (minpoly.degree_le_of_ne_zero ℚ α hQ0 hQ)
  rw [Polynomial.natDegree_map_eq_of_injective hinj] at hdle
  omega

/-- **Wirsing's third inequality at the value the box principle forces.** Below the degree of the
minimal polynomial Mahler's exponent equals `m`, and there Wirsing's inequality reads
`m ≤ w_m^*(α)`: Wirsing's conjecture holds, with equality, at an algebraic number. -/
theorem natCast_le_koksmaExponent_of_natDegree_lt {α : ℝ} (hα : IsAlgebraic ℚ α) {m : ℕ}
    (hm : m < (minpoly ℚ α).natDegree) : (m : ℝ≥0∞) ≤ koksmaExponent m α := by
  have hbox : ∀ P : ℤ[X], P ≠ 0 → P.natDegree ≤ m → aeval α P ≠ 0 :=
    fun _ h0 hd ↦ aeval_ne_zero_of_natDegree_lt hm h0 hd
  have hmw : mahlerExponent m α = (m : ℝ≥0∞) :=
    le_antisymm (mahlerExponent_le_natCast_of_isAlgebraic hα m)
      (le_mahlerExponent_of_aeval_ne_zero hbox)
  have h := mahlerExponent_le_koksmaExponent_mul hbox
  rw [hmw] at h
  have hone : (m : ℝ≥0∞) + 1 - (m : ℝ≥0∞) = 1 := by
    rw [add_comm]
    exact ENNReal.add_sub_cancel_right (by simp)
  rwa [hone, mul_one] at h

/-- **Layer 7.3, Mahler's exponent** (Schmidt 1970). For a real algebraic `α` of degree `D`,
`w_n(α) = min n (D - 1)` at every degree bound `n`. -/
theorem mahlerExponent_eq_of_isAlgebraic {α : ℝ} (hα : IsAlgebraic ℚ α) (n : ℕ) :
    mahlerExponent n α = ((min n ((minpoly ℚ α).natDegree - 1) : ℕ) : ℝ≥0∞) := by
  set D := (minpoly ℚ α).natDegree with hDdef
  have hD1 : 0 < D := minpoly.natDegree_pos hα.isIntegral
  rcases le_total n (D - 1) with h | h
  · rw [min_eq_left h]
    exact le_antisymm (mahlerExponent_le_natCast_of_isAlgebraic hα n)
      (le_mahlerExponent_of_aeval_ne_zero fun _ h0 hd ↦
        aeval_ne_zero_of_natDegree_lt (by omega) h0 hd)
  · rw [min_eq_right h]
    refine le_antisymm (mahlerExponent_le_of_isAlgebraic hα n)
      (le_trans ?_ (mahlerExponent_mono h α))
    exact le_mahlerExponent_of_aeval_ne_zero fun _ h0 hd ↦
      aeval_ne_zero_of_natDegree_lt (by omega) h0 hd

/-- **Layer 7.3, Koksma's exponent** (Schmidt 1970). For a real algebraic `α` of degree `D`,
`w_n^*(α) = min n (D - 1)` at every degree bound `n`; in particular the two exponents agree at
every algebraic number. -/
theorem koksmaExponent_eq_of_isAlgebraic {α : ℝ} (hα : IsAlgebraic ℚ α) (n : ℕ) :
    koksmaExponent n α = ((min n ((minpoly ℚ α).natDegree - 1) : ℕ) : ℝ≥0∞) := by
  set D := (minpoly ℚ α).natDegree with hDdef
  have hD1 : 0 < D := minpoly.natDegree_pos hα.isIntegral
  refine le_antisymm
    ((koksmaExponent_le_mahlerExponent n α).trans (mahlerExponent_eq_of_isAlgebraic hα n).le) ?_
  rcases le_total n (D - 1) with h | h
  · rw [min_eq_left h]
    exact natCast_le_koksmaExponent_of_natDegree_lt hα (by omega)
  · rw [min_eq_right h]
    exact le_trans (natCast_le_koksmaExponent_of_natDegree_lt hα (by omega))
      (koksmaExponent_mono h α)

/-- **Wirsing's conjecture holds at an algebraic number**, with equality: the two exponents of
Layer 1.2 agree there, at every degree bound. -/
theorem koksmaExponent_eq_mahlerExponent_of_isAlgebraic {α : ℝ} (hα : IsAlgebraic ℚ α) (n : ℕ) :
    koksmaExponent n α = mahlerExponent n α :=
  (koksmaExponent_eq_of_isAlgebraic hα n).trans (mahlerExponent_eq_of_isAlgebraic hα n).symm

end Real

/-!
## Acceptance criteria
-/

namespace Real

/-- Layer 7.3 in the shape the roadmap states it, hypothesis `1 ≤ n` and all. -/
example {α : ℝ} (hα : IsAlgebraic ℚ α) {n : ℕ} (_hn : 1 ≤ n) :
    mahlerExponent n α = ((min n ((minpoly ℚ α).natDegree - 1) : ℕ) : ℝ≥0∞) ∧
      koksmaExponent n α = ((min n ((minpoly ℚ α).natDegree - 1) : ℕ) : ℝ≥0∞) :=
  ⟨mahlerExponent_eq_of_isAlgebraic hα n, koksmaExponent_eq_of_isAlgebraic hα n⟩

/-- **Acceptance test: at `n = 1` the milestone is Roth's theorem.** A real algebraic irrational
has a minimal polynomial of degree at least two, so `min 1 (D - 1) = 1`, and Layer 1.2's identity
`w_1 + 1 = irrationalityExponent` turns the value into `irrationalityExponent α = 2`. Layer 3 is
used nowhere above, so this is a second proof of Roth's theorem. -/
example {α : ℝ} (hα : IsAlgebraic ℚ α) (hirr : Irrational α) : irrationalityExponent α = 2 := by
  have h2 : 2 ≤ (minpoly ℚ α).natDegree := by
    rw [minpoly.two_le_natDegree_iff hα.isIntegral]
    rintro ⟨q, hq⟩
    exact hirr ⟨q, by rw [← hq]; exact eq_ratCast (algebraMap ℚ ℝ) q⟩
  have hval := mahlerExponent_eq_of_isAlgebraic hα 1
  rw [min_eq_left (by omega : 1 ≤ (minpoly ℚ α).natDegree - 1)] at hval
  have h := mahlerExponent_one_add_one α
  rw [hval] at h
  rw [← h]
  norm_num

/-- **Acceptance test: the exponent stops growing at `D - 1`.** Beyond the degree of the minimal
polynomial the value is constant, which is Liouville's inequality of Layer 1.3 meeting the box
principle. -/
example {α : ℝ} (hα : IsAlgebraic ℚ α) {n : ℕ} (hn : (minpoly ℚ α).natDegree - 1 ≤ n) :
    mahlerExponent n α = (((minpoly ℚ α).natDegree - 1 : ℕ) : ℝ≥0∞) := by
  rw [mahlerExponent_eq_of_isAlgebraic hα n, min_eq_right hn]

/-- **Acceptance test: a rational number.** Its minimal polynomial has degree one, so both
exponents vanish at every degree bound — Layer 1.2 computed this at `n = 1` only. -/
example (q : ℚ) (n : ℕ) : mahlerExponent n (q : ℝ) = 0 ∧ koksmaExponent n (q : ℝ) = 0 := by
  have halg : IsAlgebraic ℚ ((q : ℝ)) := ⟨X - C q, X_sub_C_ne_zero q, by simp⟩
  have hmin : (minpoly ℚ ((q : ℝ))).natDegree = 1 := by
    rw [show ((q : ℝ)) = algebraMap ℚ ℝ q from rfl, minpoly.eq_X_sub_C ℝ q, natDegree_X_sub_C]
  refine ⟨?_, ?_⟩
  · rw [mahlerExponent_eq_of_isAlgebraic halg n, hmin]
    simp
  · rw [koksmaExponent_eq_of_isAlgebraic halg n, hmin]
    simp

/-- **Rejection test: the hypothesis `IsAlgebraic` is load-bearing.** At a Liouville number
Mahler's exponent is `⊤` already at `n = 1`, while the right-hand side of the milestone is `0`,
because the minimal polynomial of a transcendental number is `0`. -/
example : ¬ ∀ ξ : ℝ, mahlerExponent 1 ξ = ((min 1 ((minpoly ℚ ξ).natDegree - 1) : ℕ) : ℝ≥0∞) := by
  intro h
  have htop : irrationalityExponent (liouvilleNumber 2) = ⊤ :=
    irrationalityExponent_eq_top_iff.2 (liouville_liouvilleNumber le_rfl)
  have hone := mahlerExponent_one_add_one (liouvilleNumber 2)
  rw [h (liouvilleNumber 2), htop] at hone
  exact ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top _, ENNReal.one_ne_top⟩ hone

end Real
