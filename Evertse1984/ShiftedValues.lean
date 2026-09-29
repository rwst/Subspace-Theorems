/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Evertse1984.AdmissiblePoints
public import Evertse1984.PolynomialValues

-- Used only inside proofs.
import ArithmeticHeights.Northcott
import DiophantineApproximation.NormForm

/-!
# Evertse's Lemma 2, the core: three `S`-integers summing to zero

The heart of the proof of Lemma 2 (Evertse 1984, pp. 237–239). Fix `S`-integers `a`, `b` and
consider pairs of integers `(r, s)` with `0 < |r - s| ≤ β |r| ^ γ`, `γ (m + n + 2) < 1`, such that

```text
∏_{v ∈ S∞ ∪ S} ‖r - a‖_v ≤ c |r - s| ^ (D n),    ∏_{v ∈ S∞ ∪ S} ‖s - b‖_v ≤ c |r - s| ^ (D m).
```

Then `ζ₀ = s - r + a - b`, `ζ₁ = r - a`, `ζ₂ = b - s` are `S`-integers with `ζ₀ + ζ₁ + ζ₂ = 0`,
the product of their sizes over `S∞ ∪ S` is at most `C |r - s| ^ (D (m + n + 1))`, and the height
of `Z = (ζ₀ : ζ₁ : ζ₂)` is at least `C' |r| ^ D |r - s| ^ (-D)`. With
`d = (m + n + 1) γ / (1 - γ) < 1` the points `Z` are `(C'', d, S)`-admissible, so by Theorem 1
there are finitely many. Each fixes `ζ₁ / ζ₀`, and then `|r - a| = |ζ₁ / ζ₀| |r - s + b - a|` at an
infinite place bounds `|r|`. Only finitely many pairs remain.

## Main results

* `NumberField.placeProd_div`, `NumberField.placeProd_range_infinitePlace`: products over the
  places of a set.
* `NumberField.finite_setOf_shifted_core`: **the core of Lemma 2**.

## References

J.-H. Evertse, *On sums of `S`-units and linear recurrences*, Compositio Math. **53** (1984),
225–244, proof of Lemma 2.
-/

@[expose] public section

open IsDedekindDomain Height Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- An infinite place at an integer is its absolute value. -/
theorem InfinitePlace.apply_intCast (w : InfinitePlace K) (r : ℤ) : w (r : K) = |(r : ℝ)| := by
  rw [← w.norm_embedding_eq, map_intCast, Complex.norm_intCast]

/-- **A finite place is not an infinite place**: they differ at `2`. -/
theorem finitePlace_notMem_range_infinitePlace (P : HeightOneSpectrum (𝓞 K)) :
    (FinitePlace.mk P).1 ∉ Set.range (fun w : InfinitePlace K ↦ w.1) := by
  rintro ⟨w, hw⟩
  have h1 : w ((2 : ℤ) : K) = 2 := by rw [InfinitePlace.apply_intCast]; norm_num
  have h2 : FinitePlace.mk P ((2 : ℤ) : K) ≤ 1 := by
    have hv : IsNonarchimedean ((FinitePlace.mk P) ·) := FinitePlace.add_le _
    exact hv.apply_intCast_le_one (map_zero_le _ 1) (map_one _) (map_neg_eq_map _)
  have h3 := congrArg (fun v : AbsoluteValue K ℝ ↦ v ((2 : ℤ) : K)) hw
  change w ((2 : ℤ) : K) = FinitePlace.mk P ((2 : ℤ) : K) at h3
  linarith

variable (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Set (AbsoluteValue K ℝ))

/-- **The product over the infinite places.** -/
theorem placeProd_range_infinitePlace (g : AbsoluteValue K ℝ → ℝ) :
    placeProd S (Set.range fun w : InfinitePlace K ↦ w.1) g =
      ∏ w : InfinitePlace K, g w.1 ^ w.mult := by
  unfold placeProd
  rw [Finset.prod_eq_one fun P _ ↦
    Set.mulIndicator_of_notMem (finitePlace_notMem_range_infinitePlace P) _, mul_one]
  exact Finset.prod_congr rfl fun w _ ↦ by rw [Set.mulIndicator_of_mem (Set.mem_range_self w)]

/-- The product of the inverse is the inverse of the product. -/
theorem placeProd_inv (f : AbsoluteValue K ℝ → ℝ) :
    placeProd S T (fun v ↦ (f v)⁻¹) = (placeProd S T f)⁻¹ := by
  have h : ∀ v, T.mulIndicator (fun v ↦ (f v)⁻¹) v = (T.mulIndicator f v)⁻¹ := fun v ↦ by
    by_cases hv : v ∈ T <;> simp [hv]
  simp only [placeProd, h, inv_pow, Finset.prod_inv_distrib, mul_inv]

/-- **The product of a quotient is the quotient of the products.** -/
theorem placeProd_div (x y : K) :
    placeProd S T (fun v ↦ v (x / y)) =
      placeProd S T (fun v ↦ v x) / placeProd S T (fun v ↦ v y) := by
  simp only [div_eq_mul_inv, map_mul, map_inv₀]
  rw [placeProd_mul, placeProd_inv]

/-- The exponent bookkeeping of Lemma 2: from `τ ≤ β u ^ γ` and `d = γ (e + d)`,
`τ ^ (D e) ≤ β ^ (D (e + d)) (u / τ) ^ (D d)`. -/
private theorem rpow_le_of_le_mul_rpow {u τ β γ d e D : ℝ} (hu : 0 < u) (hτ : 0 < τ) (hβ : 0 < β)
    (hτu : τ ≤ β * u ^ γ) (hd : d = γ * (e + d)) (he : 0 ≤ e) (hd0 : 0 ≤ d) (hD : 0 ≤ D) :
    τ ^ (D * e) ≤ β ^ (D * (e + d)) * (u / τ) ^ (D * d) := by
  have huτ : 0 < u / τ := div_pos hu hτ
  have hlog : Real.log τ ≤ Real.log β + γ * Real.log u := by
    rw [← Real.log_rpow hu, ← Real.log_mul hβ.ne' (Real.rpow_pos_of_pos hu _).ne']
    exact Real.log_le_log hτ hτu
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hτ _)
      (mul_pos (Real.rpow_pos_of_pos hβ _) (Real.rpow_pos_of_pos huτ _)),
    Real.log_mul (Real.rpow_pos_of_pos hβ _).ne' (Real.rpow_pos_of_pos huτ _).ne',
    Real.log_rpow hτ, Real.log_rpow hβ, Real.log_rpow huτ, Real.log_div hu.ne' hτ.ne']
  have h1 : D * (e + d) * Real.log τ ≤ D * (e + d) * (Real.log β + γ * Real.log u) :=
    mul_le_mul_of_nonneg_left hlog (mul_nonneg hD (add_nonneg he hd0))
  have h2 : D * (e + d) * (γ * Real.log u) = D * d * Real.log u := by
    linear_combination (-(D * Real.log u)) * hd
  nlinarith [h1, h2]

/-- From `u ≤ M u ^ γ` with `γ < 1`, a bound for `u`. -/
private theorem le_rpow_of_le_mul_rpow {u M γ : ℝ} (hu : 0 < u) (hγ : γ < 1)
    (h : u ≤ M * u ^ γ) : u ≤ M ^ (1 - γ)⁻¹ := by
  have h1γ : 0 < 1 - γ := sub_pos.mpr hγ
  have hM : u ^ (1 - γ) ≤ M := by
    rw [Real.rpow_sub hu, Real.rpow_one, div_le_iff₀ (Real.rpow_pos_of_pos hu _)]
    exact h
  calc u = (u ^ (1 - γ)) ^ (1 - γ)⁻¹ := by
        rw [← Real.rpow_mul hu.le, mul_inv_cancel₀ h1γ.ne', Real.rpow_one]
    _ ≤ M ^ (1 - γ)⁻¹ := Real.rpow_le_rpow (Real.rpow_nonneg hu.le _) hM (inv_nonneg.mpr h1γ.le)

open scoped Classical in
/-- **The core of Evertse's Lemma 2.** For `S`-integers `a`, `b` and `γ (m + n + 2) < 1`, only
finitely many pairs of integers `(r, s)` satisfy `0 < |r - s| ≤ β |r| ^ γ`, `r - s ≠ a - b`,
`r ≠ a`, `s ≠ b`,
`∏_{v ∈ S∞ ∪ S} ‖r - a‖_v ≤ c |r - s| ^ (D n)` and `∏_{v ∈ S∞ ∪ S} ‖s - b‖_v ≤ c |r - s| ^ (D m)`,
where `D = [K : ℚ]`. -/
theorem finite_setOf_shifted_core {a b : K} (ha : a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K)
    (hb : b ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) (m n : ℕ) {c β γ : ℝ} (hc : 0 ≤ c)
    (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ : γ * (m + n + 2) < 1) :
    {p : ℤ × ℤ | p.1 ≠ p.2 ∧ |(p.1 : ℝ) - p.2| ≤ β * |(p.1 : ℝ)| ^ γ ∧
      (p.1 : K) - p.2 ≠ a - b ∧ (p.1 : K) ≠ a ∧ (p.2 : K) ≠ b ∧
      placeProd S Set.univ (fun v ↦ v ((p.1 : K) - a)) ≤
        c * |(p.1 : ℝ) - p.2| ^ (finrank ℚ K * n) ∧
      placeProd S Set.univ (fun v ↦ v ((p.2 : K) - b)) ≤
        c * |(p.1 : ℝ) - p.2| ^ (finrank ℚ K * m)}.Finite := by
  set D : ℝ := ((finrank ℚ K : ℕ) : ℝ) with hD
  have hD0 : 0 ≤ D := Nat.cast_nonneg _
  set e : ℝ := m + n + 1 with he
  have he0 : 0 ≤ e := by positivity
  have hγ1 : γ < 1 := by
    have : γ ≤ γ * (m + n + 2) := le_mul_of_one_le_right hγ0 (by linarith [
      (Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    linarith
  have h1γ : 0 < 1 - γ := sub_pos.mpr hγ1
  set d : ℝ := γ * e / (1 - γ) with hd
  have hd0 : 0 ≤ d := div_nonneg (mul_nonneg hγ0 he0) h1γ.le
  have hd1 : d < 1 := by
    rw [hd, div_lt_one h1γ]
    have : γ * e = γ * (m + n + 2) - γ := by rw [he]; ring
    linarith
  have hde : d = γ * (e + d) := by
    rw [hd]; field_simp; ring
  -- the constants
  set Tinf : Set (AbsoluteValue K ℝ) := Set.range fun w : InfinitePlace K ↦ w.1 with hTinf
  set A : ℝ := ⨆ w : InfinitePlace K, w a with hA
  have hwA : ∀ w : InfinitePlace K, w a ≤ A :=
    fun w ↦ le_ciSup (f := fun w : InfinitePlace K ↦ w a) (Finite.bddAbove_range _) w
  set R₀ : ℝ := 2 * A + 1 with hR₀
  set C₀ : ℝ := 2 ^ totalWeight K * mulHeight₁ (b - a) with hC₀def
  have hC₀ : 0 < C₀ := by positivity
  set c' : ℝ := C₀ * c ^ 2 * β ^ (D * (e + d)) * (2 ^ D * C₀) ^ d with hc'
  -- the three coordinates
  let ζ : ℤ × ℤ → Fin 3 → K := fun p ↦ ![(p.2 : K) - p.1 + a - b, (p.1 : K) - a, b - p.2]
  set V := {p : ℤ × ℤ | p.1 ≠ p.2 ∧ |(p.1 : ℝ) - p.2| ≤ β * |(p.1 : ℝ)| ^ γ ∧
      (p.1 : K) - p.2 ≠ a - b ∧ (p.1 : K) ≠ a ∧ (p.2 : K) ≠ b ∧
      placeProd S Set.univ (fun v ↦ v ((p.1 : K) - a)) ≤
        c * |(p.1 : ℝ) - p.2| ^ (finrank ℚ K * n) ∧
      placeProd S Set.univ (fun v ↦ v ((p.2 : K) - b)) ≤
        c * |(p.1 : ℝ) - p.2| ^ (finrank ℚ K * m)} with hV
  -- facts about a pair of `V`
  have hζ0 : ∀ p ∈ V, ζ p 0 ≠ 0 := fun p hp h ↦ hp.2.2.1 (by
    have : (p.2 : K) - p.1 + a - b = 0 := h
    linear_combination -this)
  have hζ1 : ∀ p ∈ V, ζ p 1 ≠ 0 := fun p hp h ↦ hp.2.2.2.1 (sub_eq_zero.mp h)
  have hζ2 : ∀ p ∈ V, ζ p 2 ≠ 0 := fun p hp h ↦ hp.2.2.2.2.1 (sub_eq_zero.mp h).symm
  have ht1 : ∀ p ∈ V, 1 ≤ |(p.1 : ℝ) - p.2| := fun p hp ↦ by
    have := Int.one_le_abs (sub_ne_zero.mpr hp.1)
    exact_mod_cast this
  -- the height of `ζ₀`
  have hHζ0 : ∀ p ∈ V, mulHeight₁ (ζ p 0) ≤ C₀ * |(p.1 : ℝ) - p.2| ^ (finrank ℚ K) := by
    intro p hp
    have heq : ζ p 0 = -(((p.1 - p.2 : ℤ) : K) + (b - a)) := by
      simp only [ζ, Matrix.cons_val_zero]; push_cast; ring
    rw [heq, mulHeight₁_neg]
    refine (mulHeight₁_add_le _ _).trans ?_
    rw [mulHeight₁_intCast, max_eq_left (by exact_mod_cast ht1 p hp), hC₀def]
    push_cast
    nlinarith [mulHeight₁_pos (b - a), pow_pos (zero_lt_one.trans_le (ht1 p hp)) (finrank ℚ K),
      (by positivity : (0 : ℝ) < 2 ^ totalWeight K)]
  have hτ : ∀ p ∈ V, 0 < |(p.1 : ℝ) - p.2| := fun p hp ↦ zero_lt_one.trans_le (ht1 p hp)
  -- (a) the product of the sizes of the coordinates
  have hprod : ∀ p ∈ V, ∏ i, placeProd S Set.univ (fun v ↦ v (ζ p i)) ≤
      C₀ * c ^ 2 * |(p.1 : ℝ) - p.2| ^ (D * e) := by
    intro p hp
    have h1 := hp.2.2.2.2.2.1
    have h2 := hp.2.2.2.2.2.2
    set τ := |(p.1 : ℝ) - p.2|
    have hτ0 : 0 ≤ τ := abs_nonneg _
    have h0 : placeProd S Set.univ (fun v ↦ v (ζ p 0)) ≤ C₀ * τ ^ finrank ℚ K :=
      (placeProd_le_mulHeight₁ S _ _).trans (hHζ0 p hp)
    have h2' : placeProd S Set.univ (fun v ↦ v (ζ p 2)) ≤ c * τ ^ (finrank ℚ K * m) := by
      refine le_trans (le_of_eq ?_) h2
      refine placeProd_congr S _ fun v _ ↦ ?_
      simp only [ζ, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      exact AbsoluteValue.map_sub v _ _
    have hP : ∀ i, 0 ≤ placeProd S Set.univ (fun v ↦ v (ζ p i)) :=
      fun i ↦ placeProd_nonneg S _ fun v _ ↦ apply_nonneg _ _
    rw [Fin.prod_univ_three]
    calc _ ≤ (C₀ * τ ^ finrank ℚ K) * (c * τ ^ (finrank ℚ K * n)) *
          (c * τ ^ (finrank ℚ K * m)) :=
          mul_le_mul (mul_le_mul h0 h1 (hP 1) (by positivity)) h2' (hP 2) (by positivity)
      _ = C₀ * c ^ 2 * τ ^ (finrank ℚ K * (m + n + 1)) := by ring
      _ = C₀ * c ^ 2 * τ ^ (D * e) := by
          rw [show D * e = ((finrank ℚ K * (m + n + 1) : ℕ) : ℝ) by rw [hD, he]; push_cast; ring,
            Real.rpow_natCast]
  -- (b) the height of `ζ` is large
  have hheight : ∀ p ∈ V, R₀ ≤ |(p.1 : ℝ)| →
      (|(p.1 : ℝ)| / 2) ^ finrank ℚ K / (C₀ * |(p.1 : ℝ) - p.2| ^ finrank ℚ K) ≤
        mulHeight (ζ p) := by
    intro p hp hr
    refine le_trans ?_ ((placeProd_le_mulHeight₁ S Tinf _).trans
      (mulHeight₁_div_le_mulHeight (ζ p) 1 0))
    rw [placeProd_div]
    have hden : placeProd S Tinf (fun v ↦ v (ζ p 0)) ≤ C₀ * |(p.1 : ℝ) - p.2| ^ finrank ℚ K :=
      (placeProd_le_mulHeight₁ S _ _).trans (hHζ0 p hp)
    have hden0 : 0 < placeProd S Tinf (fun v ↦ v (ζ p 0)) :=
      placeProd_pos S _ fun v _ ↦ v.pos (hζ0 p hp)
    have hnum : (|(p.1 : ℝ)| / 2) ^ finrank ℚ K ≤ placeProd S Tinf (fun v ↦ v (ζ p 1)) := by
      rw [hTinf, placeProd_range_infinitePlace, ← InfinitePlace.sum_mult_eq,
        ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod₀ (fun w _ ↦ by positivity) fun w _ ↦
        pow_le_pow_left₀ (by positivity) ?_ _
      have hsub := AbsoluteValue.le_sub w.1 (p.1 : K) a
      change w (p.1 : K) - w a ≤ w ((p.1 : K) - a) at hsub
      rw [InfinitePlace.apply_intCast] at hsub
      change |(p.1 : ℝ)| / 2 ≤ w ((p.1 : K) - a)
      have := hwA w
      linarith
    exact div_le_div₀ (placeProd_nonneg S _ fun v _ ↦ apply_nonneg _ _) hnum hden0 hden
  -- (c) admissibility
  have hadm : ∀ p ∈ V, R₀ ≤ |(p.1 : ℝ)| →
      ∏ i, placeProd S Set.univ (fun v ↦ v (ζ p i)) ≤ c' * mulHeight (ζ p) ^ d := by
    intro p hp hr
    set u := |(p.1 : ℝ)| with hu
    set τ := |(p.1 : ℝ) - p.2| with hτdef
    have hA0 : 0 ≤ A := (apply_nonneg _ _).trans (hwA (Classical.arbitrary _))
    have hu0 : 0 < u := by linarith
    have hτ0 := hτ p hp
    have key := rpow_le_of_le_mul_rpow hu0 hτ0 hβ hp.2.1 hde he0 hd0 hD0
    set B : ℝ := (u / 2) ^ finrank ℚ K / (C₀ * τ ^ finrank ℚ K) with hB
    have hB0 : 0 ≤ B := by positivity
    have hBH : B ^ d ≤ mulHeight (ζ p) ^ d :=
      Real.rpow_le_rpow hB0 (hheight p hp hr) hd0
    have hsplit : (u / τ) ^ (D * d) = (2 ^ D * C₀) ^ d * B ^ d := by
      rw [← Real.mul_rpow (by positivity) hB0, Real.rpow_mul (div_pos hu0 hτ0).le]
      congr 1
      rw [hB, hD, Real.rpow_natCast, Real.rpow_natCast, div_pow, div_pow]
      field_simp
      rw [← hτdef, div_self (pow_pos hτ0 _).ne']
    calc ∏ i, placeProd S Set.univ (fun v ↦ v (ζ p i)) ≤ C₀ * c ^ 2 * τ ^ (D * e) := hprod p hp
      _ ≤ C₀ * c ^ 2 * (β ^ (D * (e + d)) * ((2 ^ D * C₀) ^ d * B ^ d)) := by
          rw [← hsplit]; exact mul_le_mul_of_nonneg_left key (by positivity)
      _ ≤ C₀ * c ^ 2 * (β ^ (D * (e + d)) * ((2 ^ D * C₀) ^ d * mulHeight (ζ p) ^ d)) := by
          gcongr
      _ = c' * mulHeight (ζ p) ^ d := by rw [hc']; ring
  -- (d) Theorem 1: finitely many points `(ζ₀ : ζ₁ : ζ₂)`
  have hne : ∀ p ∈ V, ζ p ≠ 0 := fun p hp h ↦ hζ1 p hp (congrFun h 1)
  have hF := finite_setOf_admissible_sum_eq_zero S (Fin 3) (c := c') hd0 hd1
  set F := {X : Projectivization K (Fin 3 → K) | ∃ (x : Fin 3 → K) (hx : x ≠ 0),
      Projectivization.mk K x hx = X ∧
      (∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
      ∏ i, placeProd S Set.univ (fun v ↦ v (x i)) ≤ c' * mulHeight x ^ d ∧
      ∑ i, x i = 0 ∧ ∀ I : Finset (Fin 3), I.Nonempty → I ≠ Finset.univ → ∑ i ∈ I, x i ≠ 0}
    with hFdef
  have hmemF : ∀ p (hp : p ∈ V), R₀ ≤ |(p.1 : ℝ)| →
      Projectivization.mk K (ζ p) (hne p hp) ∈ F := by
    intro p hp hr
    have hnz : ∀ i, ζ p i ≠ 0 := fun i ↦ by
      fin_cases i
      exacts [hζ0 p hp, hζ1 p hp, hζ2 p hp]
    have hsum : ∑ i, ζ p i = 0 := by
      simp only [Fin.sum_univ_three, ζ, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ring
    refine ⟨ζ p, hne p hp, rfl, fun i ↦ ?_, hadm p hp hr, hsum, fun I hI hIu ↦ ?_⟩
    · have hr : ((p.1 : ℤ) : K) ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K :=
        intCast_mem _ _
      have hs : ((p.2 : ℤ) : K) ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K :=
        intCast_mem _ _
      fin_cases i
      · exact sub_mem (add_mem (sub_mem hs hr) ha) hb
      · exact sub_mem hr ha
      · exact sub_mem hb hs
    · have hcard : I.card = 1 ∨ Iᶜ.card = 1 := by
        have h1 := hI.card_pos
        have h2 : I.card ≠ 3 := fun h ↦ hIu (Finset.eq_univ_of_card I (by simpa using h))
        have h3 : I.card ≤ 3 := by simpa using Finset.card_le_univ I
        rw [Finset.card_compl, Fintype.card_fin]
        omega
      rcases hcard with h | h
      · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h
        simpa using hnz i
      · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
        have hsplit := Finset.sum_compl_add_sum I (ζ p)
        rw [hsum, hi, Finset.sum_singleton] at hsplit
        intro h0
        rw [h0, add_zero] at hsplit
        exact hnz i hsplit
  -- (e) each point fixes `ζ₁ / ζ₀`, and the ratio bounds `|r|`
  set wstar : InfinitePlace K := Classical.arbitrary _
  obtain ⟨Q, hQ⟩ := ((hF.image fun Z : Projectivization K (Fin 3 → K) ↦ Z.rep 1 / Z.rep 0).image
    fun q : K ↦ wstar q).bddAbove
  set Q' : ℝ := max Q 0
  set W : ℝ := wstar (b - a)
  set M : ℝ := 2 * Q' * (β + W)
  have hratio : ∀ p (hp : p ∈ V), R₀ ≤ |(p.1 : ℝ)| → wstar (ζ p 1 / ζ p 0) ≤ Q' := by
    intro p hp hr
    refine le_max_of_le_left (hQ ⟨ζ p 1 / ζ p 0, ⟨_, hmemF p hp hr, ?_⟩, rfl⟩)
    obtain ⟨u, hu⟩ := (Projectivization.mk_eq_mk_iff K _ _ (Projectivization.rep_nonzero _)
      (hne p hp)).mp (Projectivization.mk_rep (Projectivization.mk K (ζ p) (hne p hp)))
    change (Projectivization.mk K (ζ p) (hne p hp)).rep 1 /
      (Projectivization.mk K (ζ p) (hne p hp)).rep 0 = _
    rw [← hu, Pi.smul_apply, Pi.smul_apply, Units.smul_def, Units.smul_def, smul_eq_mul,
      smul_eq_mul]
    exact mul_div_mul_left _ _ (Units.ne_zero u)
  have hbound : ∀ p ∈ V, R₀ ≤ |(p.1 : ℝ)| → |(p.1 : ℝ)| ≤ M ^ (1 - γ)⁻¹ := by
    intro p hp hr
    have hA0 : 0 ≤ A := (apply_nonneg _ _).trans (hwA wstar)
    have hu1 : 1 ≤ |(p.1 : ℝ)| := by linarith
    have hlow : |(p.1 : ℝ)| / 2 ≤ wstar (ζ p 1) := by
      have hsub := AbsoluteValue.le_sub wstar.1 (p.1 : K) a
      change wstar (p.1 : K) - wstar a ≤ wstar ((p.1 : K) - a) at hsub
      rw [InfinitePlace.apply_intCast] at hsub
      change |(p.1 : ℝ)| / 2 ≤ wstar ((p.1 : K) - a)
      have := hwA wstar
      linarith
    have hζ0le : wstar (ζ p 0) ≤ |(p.1 : ℝ) - p.2| + W := by
      have heq : ζ p 0 = -(((p.1 - p.2 : ℤ) : K) + (b - a)) := by
        simp only [ζ, Matrix.cons_val_zero]; push_cast; ring
      rw [heq]
      change wstar.1 (-(((p.1 - p.2 : ℤ) : K) + (b - a))) ≤ _
      rw [AbsoluteValue.map_neg]
      refine (AbsoluteValue.add_le _ _ _).trans ?_
      change wstar ((p.1 - p.2 : ℤ) : K) + wstar (b - a) ≤ _
      rw [InfinitePlace.apply_intCast]; push_cast; rfl
    have hsplit : ζ p 1 = ζ p 1 / ζ p 0 * ζ p 0 := (div_mul_cancel₀ _ (hζ0 p hp)).symm
    have hQ'0 : 0 ≤ Q' := le_max_right _ _
    have hW0 : 0 ≤ W := apply_nonneg _ _
    have hrγ : 1 ≤ |(p.1 : ℝ)| ^ γ := Real.one_le_rpow hu1 hγ0
    have h1 : |(p.1 : ℝ)| / 2 ≤ Q' * (|(p.1 : ℝ) - p.2| + W) := by
      refine hlow.trans ?_
      rw [hsplit, map_mul]
      exact mul_le_mul (hratio p hp hr) hζ0le (apply_nonneg _ _) hQ'0
    refine le_rpow_of_le_mul_rpow (by linarith) hγ1 ?_
    have h2 : |(p.1 : ℝ) - p.2| + W ≤ (β + W) * |(p.1 : ℝ)| ^ γ := by
      have := hp.2.1
      nlinarith
    calc |(p.1 : ℝ)| ≤ 2 * (Q' * (|(p.1 : ℝ) - p.2| + W)) := by linarith
      _ ≤ 2 * (Q' * ((β + W) * |(p.1 : ℝ)| ^ γ)) := by gcongr
      _ = M * |(p.1 : ℝ)| ^ γ := by ring
  -- (f) finitely many pairs of bounded size
  set R : ℝ := max R₀ (M ^ (1 - γ)⁻¹)
  have hR : ∀ p ∈ V, |(p.1 : ℝ)| ≤ R := fun p hp ↦ by
    by_cases hr : R₀ ≤ |(p.1 : ℝ)|
    · exact (hbound p hp hr).trans (le_max_right _ _)
    · exact (le_of_lt (not_le.mp hr)).trans (le_max_left _ _)
  refine ((Set.finite_Icc (-⌈R⌉) ⌈R⌉).prod
    (Set.finite_Icc (-⌈R + β * R ^ γ⌉) ⌈R + β * R ^ γ⌉)).subset fun p hp ↦ ?_
  have h1 := hR p hp
  have h2 : |(p.2 : ℝ)| ≤ R + β * R ^ γ := by
    have hγR : |(p.1 : ℝ)| ^ γ ≤ R ^ γ := Real.rpow_le_rpow (abs_nonneg _) h1 hγ0
    have := hp.2.1
    have habs : |(p.2 : ℝ)| ≤ |(p.1 : ℝ)| + |(p.1 : ℝ) - p.2| := by
      have := abs_sub_abs_le_abs_sub (p.2 : ℝ) p.1
      rw [abs_sub_comm (p.2 : ℝ)] at this
      linarith
    nlinarith
  refine ⟨abs_le.mp ?_, abs_le.mp ?_⟩
  · have : ((|p.1| : ℤ) : ℝ) ≤ ⌈R⌉ := by push_cast; exact h1.trans (Int.le_ceil R)
    exact_mod_cast this
  · have : ((|p.2| : ℤ) : ℝ) ≤ ⌈R + β * R ^ γ⌉ := by
      push_cast; exact h2.trans (Int.le_ceil _)
    exact_mod_cast this

end NumberField
