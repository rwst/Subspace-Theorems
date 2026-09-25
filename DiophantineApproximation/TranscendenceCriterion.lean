/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.DigitExpansions
public import DiophantineApproximation.RepetitionSubspaces

-- Used only inside proofs.
import DiophantineApproximation.PrimeProducts
import DiophantineApproximation.Ridout
import Mathlib.Tactic.LinearCombination

/-!
# The combinatorial transcendence criterion

**Layer 7.4** (Adamczewski–Bugeaud–Luca 2004; Adamczewski–Bugeaud 2007; Ferenczi–Mauduit 1997).
For `b ≥ 2`, if the sequence of digits `a : ℕ → Fin b` is stammering and not eventually periodic,
then `ξ = ∑ k, a k / b ^ (k + 1)` is transcendental.

The route is the one of the roadmap. A repetition `U V ^ w` at the start of `a`, with `r = |U|` and
`s = |V|`, puts `(b ^ (r + s) - b ^ r) ξ` within `b ^ (-(w - 1) s)` of an integer `p`
(`Real.abs_mul_ofDigits_sub_le_rpow`). At the integer points `(b ^ (r + s), b ^ r, p)` the forms
`X, Y, ξ X - ξ Y - Z` at `∞` and the coordinate forms at the primes of `b` have product at most
`b ^ (-(w - 1) s)`, which is a negative power of the height as long as `r / s` is bounded, so
Layer 6.3 over `ℚ` in three variables puts all the points into finitely many proper subspaces
(`Real.exists_finset_submodule_of_repetition`). One subspace contains infinitely many of them;
its equation `z 0 X + z 1 Y + z 2 Z = 0` either does not involve `Z`, and then fixes `b ^ s`, or it
does, and then the approximation makes `ξ = -z 0 / z 2` rational.

With `w > 2` the same approximations are good enough for Ridout's theorem (Layer 3.3), with the
primes of `b` on the denominator, and the criterion follows with none of Layers 4–6.

## Main results

* `Real.transcendental_ofDigits_of_isStammering`: **the criterion**.
* `Real.transcendental_ofDigits_of_isStammeringWith_of_two_lt`: **the weaker criterion** for
  `w > 2`, from Ridout's theorem alone.
* `Real.transcendental_ofDigits_of_forall_periodic` and
  `Real.transcendental_ofDigits_of_forall_periodic_of_two_lt`: both in their working form, on
  periodic segments of the digits and for any irrational value.
* `Rat.one_le_mul_prod_padicNorm` and `Rat.mul_prod_padicNorm_le_of_dvd`: the part of a natural
  number prime to a set of primes is at least `1` and does not grow along divisors.

## Implementation notes

⚠ **There is no induction on the subspace.** A single proper subspace containing infinitely many
of the points already decides everything: if its equation does not involve the numerator, it
reads `z 0 b ^ s + z 1 = 0` and holds for at most one `s`; if it does, the approximation becomes
`|θ b ^ s + η| ≤ 1` with `θ = ξ + z 0 / z 2`, which forces `θ = 0` as `s` grows. Non-periodicity
enters only through the irrationality of `ξ` (`Real.irrational_ofDigits`), in the second case.

⚠ **`1 ≤ |V k|` is used by Ridout's route and not by the Subspace Theorem's.** The Subspace route
never divides by `b ^ s - 1`, and a point with `s = 0` is harmless; strict monotonicity of `|V k|`
is all it needs. Ridout's theorem is about the rational `p / (b ^ r (b ^ s - 1))`, which needs
`s ≥ 1`; `Function.IsStammeringWith.exists_periodic` supplies it.

⚠ **The primes of `b` are Ridout's `S₂`, not `S₁`.** The factor `b ^ r` is in the denominator of
the approximant, whose target is `∞`; Layer 3.3's `S₁` carries the target `0` on the numerator.
The roadmap's "`S₁` the primes dividing `b` and `S₂` empty" had them the other way round.

⚠ **Ridout's theorem sees the approximant in lowest terms, and cancellation costs nothing.**
Reducing `p / (b ^ r (b ^ s - 1))` may remove primes of `b` from the denominator, and those are
the ones that carry the gain. What is used is that the part of the denominator prime to `b`,
`den ∏ l ∣ b, |den|_l`, does not grow along divisors (`Rat.mul_prod_padicNorm_le_of_dvd`) and is
therefore at most `b ^ s - 1`, while the denominator itself is at most `b ^ r (b ^ s - 1)`. The
height is the denominator because the approximant lies in `[0, 1]`
(`Real.digitsPrefix_sub_mem`).

⚠ **No threshold is needed.** The approximation is exact — `b ^ (-(⌈w s⌉ - s))`, with no
constant — so `ε = (w - 1) / (C + 1)`, resp. `(w - 2) / (C + 1)`, works for every point and
not only for large `s`.

## References

B. Adamczewski, Y. Bugeaud and F. Luca, *Sur la complexité des nombres algébriques*, C. R. Acad.
Sci. Paris **339** (2004), 11–14; B. Adamczewski and Y. Bugeaud, *On the complexity of algebraic
numbers I. Expansions in integer bases*, Annals of Mathematics **165** (2007), 547–565; S.
Ferenczi and C. Mauduit, *Transcendence of numbers with a low complexity expansion*, Journal of
Number Theory **67** (1997), 146–161.

This is part of Layer 7.4 of the `DiophantineApproximation` roadmap.
-/

public section

open Finset

namespace Rat

/-- **A nonzero natural number is at least its `S`-part**: `1 ≤ n ∏ l ∈ S, |n|_l`. The product
over `S` is at least the product over `S` together with the primes of `n`, which is `n⁻¹`. -/
theorem one_le_mul_prod_padicNorm (S : Finset Nat.Primes) {n : ℕ} (hn : n ≠ 0) :
    1 ≤ (n : ℚ) * ∏ l ∈ S, padicNorm (l : ℕ) (n : ℚ) := by
  classical
  have hall := Rat.prod_padicNorm_natCast (S ∪ n.primesOf) n hn
    fun l hl ↦ Finset.mem_union_right _ ((Nat.mem_primesOf_iff_dvd hn).mpr hl)
  have hsplit := Finset.prod_sdiff (s₁ := S) (s₂ := S ∪ n.primesOf)
    (f := fun l : Nat.Primes ↦ padicNorm (l : ℕ) (n : ℚ)) Finset.subset_union_left
  have hle : ∏ l ∈ (S ∪ n.primesOf) \ S, padicNorm (l : ℕ) (n : ℚ) ≤ 1 :=
    Finset.prod_le_one₀ (fun l _ ↦ padicNorm.nonneg _) fun l _ ↦ padicNorm.of_nat _
  have hnn : 0 ≤ ∏ l ∈ S, padicNorm (l : ℕ) (n : ℚ) :=
    Finset.prod_nonneg fun l _ ↦ padicNorm.nonneg _
  have hn' : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h1 : (n : ℚ)⁻¹ ≤ ∏ l ∈ S, padicNorm (l : ℕ) (n : ℚ) := by
    rw [← hall, ← hsplit]
    exact mul_le_of_le_one_left hnn hle
  calc (1 : ℚ) = n * (n : ℚ)⁻¹ := (mul_inv_cancel₀ hn'.ne').symm
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 hn'.le

/-- **The `S`-free part does not grow along divisors**: for `d ∣ n ≠ 0`,
`d ∏ l ∈ S, |d|_l ≤ n ∏ l ∈ S, |n|_l`. -/
theorem mul_prod_padicNorm_le_of_dvd (S : Finset Nat.Primes) {d n : ℕ} (hn : n ≠ 0)
    (h : d ∣ n) :
    (d : ℚ) * ∏ l ∈ S, padicNorm (l : ℕ) (d : ℚ)
      ≤ (n : ℚ) * ∏ l ∈ S, padicNorm (l : ℕ) (n : ℚ) := by
  obtain ⟨m, rfl⟩ := h
  have hm : m ≠ 0 := right_ne_zero_of_mul hn
  have hd0 : 0 ≤ (d : ℚ) * ∏ l ∈ S, padicNorm (l : ℕ) (d : ℚ) :=
    mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun l _ ↦ padicNorm.nonneg _)
  have hsplit : ((d * m : ℕ) : ℚ) * ∏ l ∈ S, padicNorm (l : ℕ) ((d * m : ℕ) : ℚ)
      = ((d : ℚ) * ∏ l ∈ S, padicNorm (l : ℕ) (d : ℚ))
        * ((m : ℚ) * ∏ l ∈ S, padicNorm (l : ℕ) (m : ℚ)) := by
    push_cast
    simp only [padicNorm.mul, Finset.prod_mul_distrib]
    ring
  rw [hsplit]
  exact le_mul_of_one_le_right hd0 (one_le_mul_prod_padicNorm S hm)

end Rat

namespace Real

variable {b : ℕ}

/-- A period `s` on `[r, r + ⌈w s⌉)` says that the `⌈w s⌉ - s` digits after position `r + s`
repeat those after position `r`. -/
theorem forall_lt_eq_of_periodic {a : ℕ → Fin b} {w : ℝ} {r s : ℕ}
    (h : ∀ i, r ≤ i → i + s < r + ⌈w * s⌉₊ → a (i + s) = a i) :
    ∀ i < ⌈w * s⌉₊ - s, a (i + (r + s)) = a (i + r) := by
  intro i hi
  rw [← h (i + r) (by omega) (by omega), add_assoc]

/-- **The approximation given by a repetition**, in the form the criteria use: a period `s` on
`[r, r + ⌈w s⌉)` puts `(b ^ (r + s) - b ^ r) ξ` within `b ^ (-(w - 1) s)` of an integer. -/
theorem abs_mul_ofDigits_sub_le_rpow (hb : 2 ≤ b) {a : ℕ → Fin b} {w : ℝ} (hw : 1 ≤ w)
    {r s : ℕ} (h : ∀ i, r ≤ i → i + s < r + ⌈w * s⌉₊ → a (i + s) = a i) :
    |((b : ℝ) ^ (r + s) - b ^ r) * ofDigits a
        - ((digitsPrefix a (r + s) : ℝ) - digitsPrefix a r)| ≤ (b : ℝ) ^ (-((w - 1) * s)) := by
  have hB : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hs : s ≤ ⌈w * s⌉₊ := by
    have : (s : ℝ) ≤ w * s := le_mul_of_one_le_left (Nat.cast_nonneg _) hw
    exact_mod_cast this.trans (Nat.le_ceil _)
  refine (abs_mul_ofDigits_sub_le a (t := ⌈w * s⌉₊ - s) (forall_lt_eq_of_periodic h)).trans ?_
  rw [← Real.rpow_natCast, ← Real.rpow_neg (by positivity)]
  refine Real.rpow_le_rpow_of_exponent_le hB ?_
  rw [Nat.cast_sub hs]
  have := Nat.le_ceil (w * s)
  linarith

/-- **The combinatorial transcendence criterion, in its working form** (Adamczewski–Bugeaud–Luca
2004; Adamczewski–Bugeaud 2007). Let `ξ = 0.a 0 a 1 …` in base `b ≥ 2` be irrational, and suppose
that for `w > 1` there are positions `r k` and strictly increasing periods `s k` with
`r k ≤ C s k` such that the segment of the digits of length `⌈w s k⌉` after position `r k` has
period `s k`. Then `ξ` is transcendental. -/
theorem transcendental_ofDigits_of_forall_periodic (hb : 2 ≤ b) {a : ℕ → Fin b}
    (hirr : Irrational (ofDigits a)) {w C : ℝ} (hw : 1 < w) (hC : 0 ≤ C) {r s : ℕ → ℕ}
    (hs : StrictMono s) (hrs : ∀ k, (r k : ℝ) ≤ C * s k)
    (hper : ∀ k i, r k ≤ i → i + s k < r k + ⌈w * s k⌉₊ → a (i + s k) = a i) :
    Transcendental ℚ (ofDigits a) := by
  intro halg
  set ξ := ofDigits a with hξ
  set B : ℝ := (b : ℝ) with hBdef
  have hB1 : (1 : ℝ) < B := by rw [hBdef]; exact_mod_cast (by omega : 1 < b)
  have hB0 : (0 : ℝ) < B := by linarith
  set ε : ℝ := (w - 1) / (C + 1) with hεdef
  have hε : 0 < ε := div_pos (by linarith) (by linarith)
  obtain ⟨T, hTproper, hTmem⟩ := exists_finset_submodule_of_repetition halg b.primesOf hε
  set p : ℕ → ℤ := fun k ↦ (digitsPrefix a (r k + s k) : ℤ) - digitsPrefix a (r k) with hpdef
  set x : ℕ → Fin 3 → ℤ := fun k ↦ ![(b : ℤ) ^ (r k + s k), (b : ℤ) ^ r k, p k] with hxdef
  have hx0 : ∀ k, ((x k 0 : ℤ) : ℝ) = B ^ (r k + s k) := fun k ↦ by simp [hxdef, hBdef]
  have hx1 : ∀ k, ((x k 1 : ℤ) : ℝ) = B ^ r k := fun k ↦ by simp [hxdef, hBdef]
  have hx2 : ∀ k, ((x k 2 : ℤ) : ℝ) = (p k : ℝ) := fun k ↦ by simp [hxdef]
  have hL3 : ∀ k, |ξ * ((x k 0 : ℤ) : ℝ) - ξ * ((x k 1 : ℤ) : ℝ) - ((x k 2 : ℤ) : ℝ)|
      ≤ B ^ (-((w - 1) * s k)) := by
    intro k
    have h := abs_mul_ofDigits_sub_le_rpow hb hw.le (hper k)
    rw [hx0, hx1, hx2]
    convert h using 2
    simp only [hpdef, hBdef, hξ]
    push_cast
    ring
  have hxne : ∀ k, (fun i ↦ ((x k i : ℤ) : ℚ)) ≠ 0 := by
    intro k h
    have h0 : ((x k 0 : ℤ) : ℚ) = 0 := by simpa using congrFun h 0
    have : ((x k 0 : ℤ) : ℝ) = 0 := by exact_mod_cast h0
    rw [hx0] at this
    exact (pow_pos hB0 _).ne' this
  -- the `l`-adic sizes of the first two coordinates
  have hpadpow : ∀ m : ℕ, ∏ l ∈ b.primesOf, ((padicNorm (l : ℕ) (((b : ℤ) ^ m : ℤ) : ℚ) : ℚ) : ℝ)
      = (B ^ m)⁻¹ := by
    intro m
    have h := Rat.prod_padicNorm_natCast b.primesOf (b ^ m) (pow_ne_zero _ (by omega))
      fun l hl ↦ Nat.mem_primesOf_of_dvd_pow (by omega) hl
    have h' := congrArg (fun q : ℚ ↦ (q : ℝ)) h
    simp only [Rat.cast_prod] at h'
    rw [hBdef]
    convert h' using 3 <;> push_cast <;> rfl
  have hpad : ∀ k, ∏ l ∈ b.primesOf, ∏ i, ((padicNorm (l : ℕ) ((x k i : ℤ) : ℚ) : ℚ) : ℝ)
      ≤ (B ^ (r k + s k))⁻¹ * (B ^ r k)⁻¹ := by
    intro k
    rw [← hpadpow, ← hpadpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun l _ ↦ Finset.prod_nonneg fun i _ ↦ by
      exact_mod_cast padicNorm.nonneg _) fun l _ ↦ ?_
    rw [Fin.prod_univ_three]
    have h2 : ((padicNorm (l : ℕ) ((x k 2 : ℤ) : ℚ) : ℚ) : ℝ) ≤ 1 := by
      exact_mod_cast padicNorm.of_int _
    have hn0 : (0 : ℝ) ≤ ((padicNorm (l : ℕ) ((x k 0 : ℤ) : ℚ) : ℚ) : ℝ) := by
      exact_mod_cast padicNorm.nonneg _
    have hn1 : (0 : ℝ) ≤ ((padicNorm (l : ℕ) ((x k 1 : ℤ) : ℚ) : ℚ) : ℝ) := by
      exact_mod_cast padicNorm.nonneg _
    have e0 : x k 0 = (b : ℤ) ^ (r k + s k) := rfl
    have e1 : x k 1 = (b : ℤ) ^ r k := rfl
    rw [e0] at hn0
    rw [e1] at hn1
    rw [e0, e1]
    calc _ ≤ ((padicNorm (l : ℕ) (((b : ℤ) ^ (r k + s k) : ℤ) : ℚ) : ℚ) : ℝ)
            * ((padicNorm (l : ℕ) (((b : ℤ) ^ r k : ℤ) : ℚ) : ℚ) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hn0 hn1)
      _ = _ := mul_one _
  -- the sup norm of the point is `b ^ (r + s)`
  have hp : ∀ k, 0 ≤ (p k : ℝ) ∧ (p k : ℝ) ≤ B ^ (r k + s k) := by
    intro k
    have h1 : 0 ≤ p k := (digitsPrefix_sub_mem a (r k) (s k)).1
    have h2 : p k ≤ (b : ℤ) ^ r k * ((b : ℤ) ^ s k - 1) := (digitsPrefix_sub_mem a (r k) (s k)).2
    have h2' : (p k : ℝ) ≤ B ^ r k * (B ^ s k - 1) := by
      have : ((p k : ℤ) : ℝ) ≤ (((b : ℤ) ^ r k * ((b : ℤ) ^ s k - 1) : ℤ) : ℝ) := by
        exact_mod_cast h2
      simpa [hBdef] using this
    refine ⟨by exact_mod_cast h1, h2'.trans ?_⟩
    rw [pow_add]
    nlinarith [pow_pos hB0 (r k)]
  have hsup : ∀ k, (⨆ i, |((x k i : ℤ) : ℝ)|) ≤ B ^ (r k + s k) := by
    intro k
    refine ciSup_le fun i ↦ ?_
    fin_cases i
    · simp only [Fin.zero_eta, hx0, abs_of_pos (pow_pos hB0 _), le_refl]
    · simp only [Fin.mk_one, hx1, abs_of_pos (pow_pos hB0 _)]
      exact pow_le_pow_right₀ hB1.le (Nat.le_add_right _ _)
    · change |((x k 2 : ℤ) : ℝ)| ≤ _
      rw [hx2, abs_of_nonneg (hp k).1]
      exact (hp k).2
  have hsuppos : ∀ k, 0 < ⨆ i, |((x k i : ℤ) : ℝ)| := fun k ↦
    lt_of_lt_of_le (by rw [hx0]; exact abs_pos.mpr (pow_pos hB0 _).ne')
      (Finite.le_ciSup_of_le (0 : Fin 3) le_rfl)
  have hsmall : ∀ k, |((x k 0 : ℤ) : ℝ)| * |((x k 1 : ℤ) : ℝ)|
        * |ξ * ((x k 0 : ℤ) : ℝ) - ξ * ((x k 1 : ℤ) : ℝ) - ((x k 2 : ℤ) : ℝ)|
        * ∏ l ∈ b.primesOf, ∏ i, ((padicNorm (l : ℕ) ((x k i : ℤ) : ℚ) : ℚ) : ℝ)
      ≤ (⨆ i, |((x k i : ℤ) : ℝ)|) ^ (-ε) := by
    intro k
    have hr : (0 : ℝ) < B ^ r k := pow_pos hB0 _
    have hrs' : (0 : ℝ) < B ^ (r k + s k) := pow_pos hB0 _
    have hE := hL3 k
    have hP := hpad k
    have hPn : 0 ≤ ∏ l ∈ b.primesOf, ∏ i, ((padicNorm (l : ℕ) ((x k i : ℤ) : ℚ) : ℚ) : ℝ) :=
      Finset.prod_nonneg fun l _ ↦ Finset.prod_nonneg fun i _ ↦ by
        exact_mod_cast padicNorm.nonneg _
    rw [hx0, hx1, abs_of_pos hrs', abs_of_pos hr]
    rw [hx0, hx1] at hE
    calc B ^ (r k + s k) * B ^ r k * |ξ * B ^ (r k + s k) - ξ * B ^ r k - ((x k 2 : ℤ) : ℝ)|
          * ∏ l ∈ b.primesOf, ∏ i, ((padicNorm (l : ℕ) ((x k i : ℤ) : ℚ) : ℚ) : ℝ)
        ≤ B ^ (r k + s k) * B ^ r k * B ^ (-((w - 1) * s k))
          * ((B ^ (r k + s k))⁻¹ * (B ^ r k)⁻¹) := by
          gcongr
      _ = B ^ (-((w - 1) * s k)) := by field_simp
      _ ≤ B ^ (-(ε * ((r k + s k : ℕ) : ℝ))) := by
          refine Real.rpow_le_rpow_of_exponent_le hB1.le (neg_le_neg ?_)
          rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          push_cast
          nlinarith [hrs k, (Nat.cast_nonneg (s k) : (0 : ℝ) ≤ s k)]
      _ = (B ^ (r k + s k)) ^ (-ε) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hB0.le]
          ring_nf
      _ ≤ (⨆ i, |((x k i : ℤ) : ℝ)|) ^ (-ε) :=
          Real.rpow_le_rpow_of_nonpos (hsuppos k) (hsup k) (by linarith)
  -- one subspace contains infinitely many of the points
  have hmem : ∀ k, ∃ V ∈ T, (fun i ↦ ((x k i : ℤ) : ℚ)) ∈ V := fun k ↦
    hTmem (x k) (hxne k) (hsmall k)
  choose V hVT hxV using hmem
  obtain ⟨⟨V₀, hV₀⟩, hinf⟩ := Finite.exists_infinite_fiber (fun k ↦ (⟨V k, hVT k⟩ : T))
  set K : Set ℕ := (fun k ↦ (⟨V k, hVT k⟩ : T)) ⁻¹' {⟨V₀, hV₀⟩} with hKdef
  have hK : K.Infinite := Set.infinite_coe_iff.mp hinf
  have hKV : ∀ k ∈ K, (fun i ↦ ((x k i : ℤ) : ℚ)) ∈ V₀ := fun k hk ↦ by
    have h : V k = V₀ := congrArg Subtype.val (Set.mem_singleton_iff.mp hk)
    rw [← h]
    exact hxV k
  obtain ⟨f, hf0, hfV⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.mpr (hTproper V₀ hV₀)) inferInstance
  set z : Fin 3 → ℚ := fun i ↦ f (fun t ↦ if i = t then 1 else 0) with hzdef
  have hfx : ∀ y : Fin 3 → ℚ, f y = ∑ i, y i * z i := by
    intro y
    rw [LinearMap.pi_apply_eq_sum_univ f y]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_eq_mul]
  have hz : ¬ (z 0 = 0 ∧ z 1 = 0 ∧ z 2 = 0) := by
    rintro ⟨h0, h1, h2⟩
    exact hf0 (LinearMap.ext fun y ↦ by simp [hfx y, Fin.sum_univ_three, h0, h1, h2])
  have hrel : ∀ k ∈ K,
      B ^ (r k + s k) * (z 0 : ℝ) + B ^ r k * (z 1 : ℝ) + (p k : ℝ) * (z 2 : ℝ) = 0 := by
    intro k hk
    have hmap : f (fun i ↦ ((x k i : ℤ) : ℚ)) ∈ Submodule.map f V₀ :=
      Submodule.mem_map_of_mem (hKV k hk)
    rw [hfV, Submodule.mem_bot, hfx, Fin.sum_univ_three] at hmap
    have h := congrArg (fun q : ℚ ↦ (q : ℝ)) hmap
    push_cast at h
    rw [hx0, hx1, hx2] at h
    exact h
  by_cases hz2 : z 2 = 0
  · -- the relation does not involve the numerator: it pins down `b ^ s`
    obtain ⟨k₁, hk₁⟩ := hK.nonempty
    obtain ⟨k₂, hk₂, hlt⟩ := hK.exists_gt k₁
    have hlin : ∀ k ∈ K, B ^ s k * (z 0 : ℝ) + (z 1 : ℝ) = 0 := by
      intro k hk
      have h := hrel k hk
      rw [hz2, Rat.cast_zero, mul_zero, add_zero, pow_add] at h
      have hr : B ^ r k ≠ 0 := (pow_pos hB0 _).ne'
      have : B ^ r k * (B ^ s k * (z 0 : ℝ) + (z 1 : ℝ)) = 0 := by linear_combination h
      exact (mul_eq_zero.mp this).resolve_left hr
    have hne : B ^ s k₁ - B ^ s k₂ ≠ 0 :=
      sub_ne_zero.mpr (pow_lt_pow_right₀ hB1 (hs hlt)).ne
    have hz0 : (z 0 : ℝ) = 0 := by
      have : (B ^ s k₁ - B ^ s k₂) * (z 0 : ℝ) = 0 := by
        linear_combination hlin k₁ hk₁ - hlin k₂ hk₂
      exact (mul_eq_zero.mp this).resolve_left hne
    have hz1 : (z 1 : ℝ) = 0 := by linear_combination hlin k₁ hk₁ - B ^ s k₁ * hz0
    exact hz ⟨by exact_mod_cast hz0, by exact_mod_cast hz1, hz2⟩
  · -- the relation determines the numerator, and the repetition makes `ξ` rational
    have hz2' : (z 2 : ℝ) ≠ 0 := by exact_mod_cast hz2
    set θ : ℝ := ξ + (z 0 : ℝ) / (z 2 : ℝ) with hθ
    set η : ℝ := (z 1 : ℝ) / (z 2 : ℝ) - ξ with hη
    have hbound : ∀ k ∈ K, |θ * B ^ s k + η| ≤ 1 := by
      intro k hk
      have hr : (0 : ℝ) < B ^ r k := pow_pos hB0 _
      have hid : ξ * B ^ (r k + s k) - ξ * B ^ r k - (p k : ℝ) = B ^ r k * (θ * B ^ s k + η) := by
        have h := hrel k hk
        rw [hθ, hη, pow_add]
        rw [pow_add] at h
        field_simp
        linear_combination -h
      have hE := hL3 k
      rw [hx0, hx1, hx2, hid, abs_mul, abs_of_pos hr] at hE
      have hE1 : B ^ (-((w - 1) * s k)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hB1.le
          (neg_nonpos.mpr (mul_nonneg (by linarith) (Nat.cast_nonneg _)))
      have hr1 : (1 : ℝ) ≤ B ^ r k := one_le_pow₀ hB1.le
      nlinarith [abs_nonneg (θ * B ^ s k + η)]
    by_cases hθ0 : θ = 0
    · refine hirr ⟨-(z 0 / z 2), ?_⟩
      push_cast
      linarith
    · obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ((1 + |η|) / |θ|) hB1
      obtain ⟨k, hk, hNk⟩ := hK.exists_gt N
      have hsk : N ≤ s k := hNk.le.trans (hs.id_le k)
      have h1 := hbound k hk
      have h2 : (1 + |η|) / |θ| < B ^ s k := hN.trans_le (pow_le_pow_right₀ hB1.le hsk)
      rw [div_lt_iff₀ (abs_pos.mpr hθ0)] at h2
      have h3 : |θ * B ^ s k| ≤ |θ * B ^ s k + η| + |η| := by
        have := abs_sub (θ * B ^ s k + η) η
        rwa [add_sub_cancel_right] at this
      rw [abs_mul, abs_of_pos (pow_pos hB0 _)] at h3
      linarith

/-- **The criterion for `w > 2`, from Ridout's theorem alone** (Ferenczi–Mauduit 1997). The same
statement as `transcendental_ofDigits_of_forall_periodic` under the stronger hypothesis `w > 2`,
proved from Layer 3.3 with the primes of `b` as Ridout's primes of the denominator and none of
Layers 4–6. -/
theorem transcendental_ofDigits_of_forall_periodic_of_two_lt (hb : 2 ≤ b) {a : ℕ → Fin b}
    (hirr : Irrational (ofDigits a)) {w C : ℝ} (hw : 2 < w) (hC : 0 ≤ C) {r s : ℕ → ℕ}
    (hs : StrictMono s) (hs1 : ∀ k, 1 ≤ s k) (hrs : ∀ k, (r k : ℝ) ≤ C * s k)
    (hper : ∀ k i, r k ≤ i → i + s k < r k + ⌈w * s k⌉₊ → a (i + s k) = a i) :
    Transcendental ℚ (ofDigits a) := by
  intro halg
  set ξ := ofDigits a with hξ
  set B : ℝ := (b : ℝ) with hBdef
  have hB1 : (1 : ℝ) < B := by rw [hBdef]; exact_mod_cast (by omega : 1 < b)
  have hB0 : (0 : ℝ) < B := by linarith
  set ε : ℝ := (w - 2) / (C + 1) with hεdef
  have hε : 0 < ε := div_pos (by linarith) (by linarith)
  set S := b.primesOf with hSdef
  have hR := Rat.finite_setOf_ridout halg ∅ S hε
  set p : ℕ → ℤ := fun k ↦ (digitsPrefix a (r k + s k) : ℤ) - digitsPrefix a (r k) with hpdef
  set q : ℕ → ℕ := fun k ↦ b ^ r k * (b ^ s k - 1) with hqdef
  have hbs : ∀ k, 2 ≤ b ^ s k := fun k ↦
    le_trans hb (Nat.le_self_pow (by have := hs1 k; omega) b)
  have hq0 : ∀ k, q k ≠ 0 := fun k ↦
    mul_ne_zero (pow_ne_zero _ (by omega)) (by have := hbs k; omega)
  have hqR : ∀ k, (q k : ℝ) = B ^ (r k + s k) - B ^ r k := fun k ↦ by
    simp only [hqdef, hBdef]
    rw [Nat.cast_mul, Nat.cast_sub (by have := hbs k; omega)]
    push_cast
    ring
  have hqpos : ∀ k, (0 : ℝ) < q k := fun k ↦ by exact_mod_cast Nat.pos_of_ne_zero (hq0 k)
  have hp : ∀ k, 0 ≤ p k ∧ p k ≤ (q k : ℤ) := fun k ↦ by
    have h := digitsPrefix_sub_mem a (r k) (s k)
    refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
    simp only [hqdef]
    rw [Nat.cast_mul, Nat.cast_sub (by have := hbs k; omega)]
    push_cast
    ring
  set β : ℕ → ℚ := fun k ↦ (p k : ℚ) / (q k : ℚ) with hβdef
  have hE : ∀ k, |ξ - (β k : ℝ)| * q k ≤ B ^ (-((w - 1) * s k)) := fun k ↦ by
    have h := abs_mul_ofDigits_sub_le_rpow hb (by linarith) (hper k)
    have hqk := hqpos k
    have hid : |ξ - (β k : ℝ)| * q k = |((b : ℝ) ^ (r k + s k) - b ^ r k) * ξ
        - ((digitsPrefix a (r k + s k) : ℝ) - digitsPrefix a (r k))| := by
      rw [← abs_of_pos hqk, ← abs_mul]
      congr 1
      have hq := hqR k
      simp only [hβdef, hpdef, hBdef] at hq ⊢
      push_cast
      rw [← hq]
      field_simp
    rw [hid]
    exact h
  -- every `β k` satisfies Ridout's inequality
  have hmemR : ∀ k, β k ∈ {β : ℚ | |ξ - (β : ℝ)|
      * (∏ l ∈ (∅ : Finset Nat.Primes), ((padicNorm (l : ℕ) β.num : ℚ) : ℝ))
      * ∏ l ∈ S, ((padicNorm (l : ℕ) β.den : ℚ) : ℝ)
      ≤ (max β.num.natAbs β.den : ℝ) ^ (-2 - ε)} := by
    intro k
    rw [Set.mem_ofPred_eq, Finset.prod_empty, mul_one]
    have hqk := hqpos k
    obtain ⟨hp0, hpq⟩ := hp k
    have hden_dvd : (β k).den ∣ q k := by
      have h := Rat.den_dvd (p k) (q k : ℤ)
      have hβ' : β k = Rat.divInt (p k) (q k : ℤ) := by
        rw [Rat.divInt_eq_div]; push_cast; rfl
      rw [hβ']
      exact_mod_cast h
    have hden_le : ((β k).den : ℝ) ≤ q k := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (hq0 k)) hden_dvd
    have hβ0 : 0 ≤ β k := div_nonneg (by exact_mod_cast hp0) (Nat.cast_nonneg _)
    have hβ1 : β k ≤ 1 := by
      rw [hβdef, div_le_one (by exact_mod_cast Nat.pos_of_ne_zero (hq0 k))]
      exact_mod_cast hpq
    have hnum : (β k).num.natAbs ≤ (β k).den := by
      have h := Rat.mul_den_eq_num (β k)
      have : ((β k).num.natAbs : ℚ) ≤ (β k).den := by
        rw [Nat.cast_natAbs, Int.cast_abs, ← h, abs_mul, abs_of_nonneg hβ0, Nat.abs_cast]
        exact mul_le_of_le_one_left (Nat.cast_nonneg _) hβ1
      exact_mod_cast this
    rw [max_eq_right (by exact_mod_cast hnum)]
    -- the part of the denominator prime to `b` is below `b ^ s`
    have hfree : ((β k).den : ℝ) * ∏ l ∈ S, ((padicNorm (l : ℕ) ((β k).den : ℚ) : ℚ) : ℝ)
        ≤ B ^ s k := by
      have h1 := Rat.mul_prod_padicNorm_le_of_dvd S (hq0 k) hden_dvd
      have hbr : ∏ l ∈ S, padicNorm (l : ℕ) ((b ^ r k : ℕ) : ℚ) = ((b ^ r k : ℕ) : ℚ)⁻¹ :=
        Rat.prod_padicNorm_natCast S (b ^ r k) (pow_ne_zero _ (by omega))
          fun l hl ↦ Nat.mem_primesOf_of_dvd_pow (by omega) hl
      have hbr0 : ((b ^ r k : ℕ) : ℚ) ≠ 0 := by
        exact_mod_cast pow_ne_zero _ (by omega : b ≠ 0)
      have hle1 : ∏ l ∈ S, padicNorm (l : ℕ) ((b ^ s k - 1 : ℕ) : ℚ) ≤ 1 :=
        Finset.prod_le_one₀ (fun l _ ↦ padicNorm.nonneg _) fun l _ ↦ padicNorm.of_nat _
      have h2 : (q k : ℚ) * ∏ l ∈ S, padicNorm (l : ℕ) (q k : ℚ) ≤ ((b ^ s k - 1 : ℕ) : ℚ) := by
        have hq : (q k : ℚ) = ((b ^ r k : ℕ) : ℚ) * ((b ^ s k - 1 : ℕ) : ℚ) := by
          simp only [hqdef]; push_cast; ring
        rw [hq]
        simp only [padicNorm.mul, Finset.prod_mul_distrib, hbr]
        calc ((b ^ r k : ℕ) : ℚ) * ((b ^ s k - 1 : ℕ) : ℚ)
              * (((b ^ r k : ℕ) : ℚ)⁻¹ * ∏ l ∈ S, padicNorm (l : ℕ) ((b ^ s k - 1 : ℕ) : ℚ))
            = ((b ^ s k - 1 : ℕ) : ℚ) * ∏ l ∈ S, padicNorm (l : ℕ) ((b ^ s k - 1 : ℕ) : ℚ) := by
              field_simp
          _ ≤ ((b ^ s k - 1 : ℕ) : ℚ) * 1 :=
              mul_le_mul_of_nonneg_left hle1 (Nat.cast_nonneg _)
          _ = _ := mul_one _
      have h3 : (((b ^ s k - 1 : ℕ) : ℚ) : ℝ) ≤ B ^ s k := by
        rw [hBdef]
        push_cast
        rw [Nat.cast_sub (by have := hbs k; omega)]
        push_cast
        linarith
      have h4 := (Rat.cast_le (K := ℝ)).mpr (h1.trans h2)
      push_cast at h4 h3 ⊢
      linarith
    have hD1 : (1 : ℝ) ≤ (β k).den := by exact_mod_cast (β k).den_pos
    have hD0 : (0 : ℝ) < (β k).den := by linarith
    have hprod0 : 0 ≤ ∏ l ∈ S, ((padicNorm (l : ℕ) ((β k).den : ℚ) : ℚ) : ℝ) :=
      Finset.prod_nonneg fun l _ ↦ by exact_mod_cast padicNorm.nonneg _
    have hqle : (q k : ℝ) ≤ B ^ (r k + s k) := by
      rw [hqR]; linarith [pow_pos hB0 (r k)]
    have hexp : -((w - 1) * s k) + s k + ε * ((r k : ℝ) + s k) ≤ 0 := by
      have : ε * ((r k : ℝ) + s k) ≤ (w - 2) * s k := by
        rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith [hrs k, (Nat.cast_nonneg (s k) : (0 : ℝ) ≤ s k)]
      linarith
    have key : (|ξ - (β k : ℝ)| * ∏ l ∈ S, ((padicNorm (l : ℕ) ((β k).den : ℚ) : ℚ) : ℝ))
        * ((β k).den : ℝ) ^ (2 + ε) ≤ 1 := by
      calc (|ξ - (β k : ℝ)| * ∏ l ∈ S, ((padicNorm (l : ℕ) ((β k).den : ℚ) : ℚ) : ℝ))
            * ((β k).den : ℝ) ^ (2 + ε)
          = (|ξ - (β k : ℝ)| * (((β k).den : ℝ)
              * ∏ l ∈ S, ((padicNorm (l : ℕ) ((β k).den : ℚ) : ℚ) : ℝ)))
            * ((β k).den : ℝ) ^ (1 + ε) := by
            rw [show (2 : ℝ) + ε = 1 + (1 + ε) by ring, Real.rpow_add hD0, Real.rpow_one]
            ring
        _ ≤ (|ξ - (β k : ℝ)| * B ^ s k) * (q k : ℝ) ^ (1 + ε) := by
            gcongr
        _ = (|ξ - (β k : ℝ)| * q k) * B ^ s k * (q k : ℝ) ^ ε := by
            rw [Real.rpow_add hqk, Real.rpow_one]
            ring
        _ ≤ B ^ (-((w - 1) * s k)) * B ^ s k * (B ^ (r k + s k)) ^ ε := by
            gcongr
            exact hE k
        _ = B ^ (-((w - 1) * s k) + s k + ε * ((r k : ℝ) + s k)) := by
            rw [Real.rpow_add hB0, Real.rpow_add hB0, Real.rpow_natCast,
              ← Real.rpow_natCast B (r k + s k), ← Real.rpow_mul hB0.le]
            push_cast
            ring_nf
        _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hB1.le hexp
    rw [show (-2 - ε : ℝ) = -(2 + ε) by ring, Real.rpow_neg hD0.le, ← one_div,
      le_div_iff₀ (Real.rpow_pos_of_pos hD0 _)]
    exact key
  obtain ⟨⟨β₀, hβ₀⟩, hinf⟩ := @Finite.exists_infinite_fiber _ _ _ hR.to_subtype
    (fun k ↦ (⟨β k, hmemR k⟩ : {β : ℚ | _}))
  set K : Set ℕ := (fun k ↦ (⟨β k, hmemR k⟩ : {β : ℚ | _})) ⁻¹' {⟨β₀, hβ₀⟩} with hKdef
  have hK : K.Infinite := Set.infinite_coe_iff.mp hinf
  have hKβ : ∀ k ∈ K, β k = β₀ := fun k hk ↦ congrArg Subtype.val (Set.mem_singleton_iff.mp hk)
  have hpos : 0 < |ξ - (β₀ : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr fun h ↦ hirr ⟨β₀, h.symm⟩)
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (|ξ - (β₀ : ℝ)|)⁻¹ hB1
  obtain ⟨k, hk, hNk⟩ := hK.exists_gt N
  have hsk : N ≤ s k := hNk.le.trans (hs.id_le k)
  have h1 := hE k
  rw [hKβ k hk] at h1
  have hq1 : (1 : ℝ) ≤ q k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hq0 k)
  have h2 : B ^ (-((w - 1) * s k)) ≤ (B ^ s k)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hB0.le]
    refine Real.rpow_le_rpow_of_exponent_le hB1.le ?_
    nlinarith [(Nat.cast_nonneg (s k) : (0 : ℝ) ≤ s k)]
  have h3 : (|ξ - (β₀ : ℝ)|)⁻¹ < B ^ s k := hN.trans_le (pow_le_pow_right₀ hB1.le hsk)
  have h4 : |ξ - (β₀ : ℝ)| ≤ (B ^ s k)⁻¹ :=
    le_trans (le_mul_of_one_le_right (abs_nonneg _) hq1) (h1.trans h2)
  have h5 := (inv_lt_comm₀ hpos (pow_pos hB0 _)).mp h3
  linarith

/-- **Layer 7.4: the combinatorial transcendence criterion** (Adamczewski–Bugeaud–Luca 2004;
Adamczewski–Bugeaud 2007). For `b ≥ 2`, if the sequence of digits `a` is stammering and not
eventually periodic, then `∑ k, a k / b ^ (k + 1)` is transcendental. -/
theorem transcendental_ofDigits_of_isStammering (hb : 2 ≤ b) {a : ℕ → Fin b}
    (hst : Function.IsStammering a) (hper : ¬ Function.IsEventuallyPeriodic a) :
    Transcendental ℚ (ofDigits a) := by
  obtain ⟨w, hw, h⟩ := hst
  obtain ⟨C, hC, r, s, hs, -, hrs, hp⟩ := h.exists_periodic (by linarith)
  exact transcendental_ofDigits_of_forall_periodic hb (irrational_ofDigits hper) hw hC hs hrs hp

/-- **Layer 7.4, the weaker criterion** (Ferenczi–Mauduit 1997): Condition `(∗)_w` for some
`w > 2`, from Ridout's theorem (Layer 3.3) alone. -/
theorem transcendental_ofDigits_of_isStammeringWith_of_two_lt (hb : 2 ≤ b) {a : ℕ → Fin b}
    {w : ℝ} (hw : 2 < w) (hst : Function.IsStammeringWith w a)
    (hper : ¬ Function.IsEventuallyPeriodic a) :
    Transcendental ℚ (ofDigits a) := by
  obtain ⟨C, hC, r, s, hs, hs1, hrs, hp⟩ := hst.exists_periodic (by linarith)
  exact transcendental_ofDigits_of_forall_periodic_of_two_lt hb (irrational_ofDigits hper) hw hC
    hs hs1 hrs hp

end Real

/-! ### Acceptance criteria -/

section Examples

open Classical in
/-- The digits of the lacunary number: `1` at the powers of `2`, `0` elsewhere. -/
private noncomputable def lacunaryDigits (n : ℕ) : Fin 10 := if ∃ j, n = 2 ^ j then 1 else 0

private theorem lacunaryDigits_eq_zero {m n : ℕ} (h1 : 2 ^ m < n) (h2 : n < 2 ^ (m + 1)) :
    lacunaryDigits n = 0 := by
  classical
  simp only [lacunaryDigits]
  refine ite_eq_right fun ⟨j, hj⟩ ↦ ?_
  subst hj
  have h1' := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h1
  have h2' := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2
  omega

private theorem lacunaryDigits_pow (j : ℕ) : lacunaryDigits (2 ^ j) = 1 := by
  classical
  simp only [lacunaryDigits]
  exact ite_eq_left ⟨j, rfl⟩

private theorem not_isEventuallyPeriodic_lacunaryDigits :
    ¬ Function.IsEventuallyPeriodic lacunaryDigits := by
  rintro ⟨N, p, hp, h⟩
  obtain ⟨j, hj⟩ : ∃ j, N + p < 2 ^ j := ⟨N + p, Nat.lt_two_pow_self⟩
  have hN : N ≤ 2 ^ j := by omega
  have e := h (2 ^ j) hN
  rw [lacunaryDigits_pow, lacunaryDigits_eq_zero (m := j) (by omega)
    (by rw [pow_succ]; omega)] at e
  exact absurd e (by decide)

private theorem lacunaryDigits_periodic (k i : ℕ) (h1 : 2 ^ (k + 2) + 1 ≤ i)
    (h2 : i + 2 ^ k < 2 ^ (k + 2) + 1 + ⌈(3 : ℝ) * ((2 ^ k : ℕ) : ℝ)⌉₊) :
    lacunaryDigits (i + 2 ^ k) = lacunaryDigits i := by
  have hceil : ⌈(3 : ℝ) * ((2 ^ k : ℕ) : ℝ)⌉₊ = 3 * 2 ^ k := by
    rw [show (3 : ℝ) * ((2 ^ k : ℕ) : ℝ) = ((3 * 2 ^ k : ℕ) : ℝ) by push_cast; ring,
      Nat.ceil_natCast]
  rw [hceil] at h2
  have e8 : 2 ^ (k + 3) = 8 * 2 ^ k := by rw [pow_add]; ring
  have e4 : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; ring
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [lacunaryDigits_eq_zero (m := k + 2) (by omega) (by omega),
    lacunaryDigits_eq_zero (m := k + 2) (by omega) (by omega)]

/-- **Conformance: a stammering sequence.** The digits of the lacunary number satisfy Condition
`(∗)_3`: after position `4 · 2 ^ k + 1` there are `3 · 2 ^ k` zeros, a word `0 ^ (2 ^ k)` to the
power `3`. -/
private theorem isStammeringWith_lacunaryDigits : Function.IsStammeringWith 3 lacunaryDigits :=
  Function.isStammeringWith_of_periodic (C := 5) (by norm_num) (r := fun k ↦ 2 ^ (k + 2) + 1)
    (s := fun k ↦ 2 ^ k) (fun _ _ h ↦ Nat.pow_lt_pow_right (by norm_num) h)
    (fun k ↦ Nat.one_le_two_pow) (fun k ↦ by
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      push_cast; rw [pow_add]; linarith)
    lacunaryDigits_periodic

/-- **The lacunary number `∑ j, 10 ^ (-(2 ^ j + 1))` is transcendental**, by the milestone as
stated: its digits are stammering and not eventually periodic. -/
example : Transcendental ℚ (Real.ofDigits lacunaryDigits) :=
  Real.transcendental_ofDigits_of_isStammering (by norm_num)
    ⟨3, by norm_num, isStammeringWith_lacunaryDigits⟩ not_isEventuallyPeriodic_lacunaryDigits

/-- The same number by the Ferenczi–Mauduit criterion, since `3 > 2`: Ridout's theorem alone. -/
example : Transcendental ℚ (Real.ofDigits lacunaryDigits) :=
  Real.transcendental_ofDigits_of_isStammeringWith_of_two_lt (by norm_num) (by norm_num)
    isStammeringWith_lacunaryDigits not_isEventuallyPeriodic_lacunaryDigits

/-- The same number by the working form of the criterion. -/
example : Transcendental ℚ (Real.ofDigits lacunaryDigits) :=
  Real.transcendental_ofDigits_of_forall_periodic (by norm_num)
    (Real.irrational_ofDigits not_isEventuallyPeriodic_lacunaryDigits) (w := 3) (C := 5)
    (by norm_num) (by norm_num) (r := fun k ↦ 2 ^ (k + 2) + 1) (s := fun k ↦ 2 ^ k)
    (fun _ _ h ↦ Nat.pow_lt_pow_right (by norm_num) h) (fun k ↦ by
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      push_cast; rw [pow_add]; linarith)
    lacunaryDigits_periodic

/-- The same number by the working form of the weaker criterion. -/
example : Transcendental ℚ (Real.ofDigits lacunaryDigits) :=
  Real.transcendental_ofDigits_of_forall_periodic_of_two_lt (by norm_num)
    (Real.irrational_ofDigits not_isEventuallyPeriodic_lacunaryDigits) (w := 3) (C := 5)
    (by norm_num) (by norm_num) (r := fun k ↦ 2 ^ (k + 2) + 1) (s := fun k ↦ 2 ^ k)
    (fun _ _ h ↦ Nat.pow_lt_pow_right (by norm_num) h) (fun k ↦ Nat.one_le_two_pow) (fun k ↦ by
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      push_cast; rw [pow_add]; linarith)
    lacunaryDigits_periodic

/-- **Rejection: non-periodicity is load-bearing.** The constant sequence `0` is stammering, and
its value `0` is algebraic. -/
example : Function.IsStammering (fun _ : ℕ ↦ (0 : Fin 10)) ∧
    ¬ Transcendental ℚ (Real.ofDigits fun _ : ℕ ↦ (0 : Fin 10)) := by
  refine ⟨⟨2, by norm_num, Function.isStammeringWith_of_periodic (C := 0) (by norm_num)
    (r := fun _ ↦ 0) (s := fun k ↦ k + 1) (fun _ _ h ↦ Nat.succ_lt_succ h)
    (fun k ↦ Nat.succ_pos k) (fun k ↦ by simp) (fun _ _ _ _ ↦ rfl)⟩, ?_⟩
  have h0 : Real.ofDigits (fun _ : ℕ ↦ (0 : Fin 10)) = 0 := by
    simp [Real.ofDigits, Real.ofDigitsTerm]
  rw [h0]
  exact fun h ↦ h isAlgebraic_zero

/-- **Rejection: `w > 1` is load-bearing.** Condition `(∗)_1` holds for every sequence, with
`U k` empty and `V k` the first `k + 1` letters. -/
example (a : ℕ → Fin 10) : Function.IsStammeringWith 1 a :=
  Function.isStammeringWith_of_periodic (C := 0) (by norm_num) (r := fun _ ↦ 0)
    (s := fun k ↦ k + 1) (fun _ _ h ↦ Nat.succ_lt_succ h) (fun k ↦ Nat.succ_pos k)
    (fun k ↦ by simp) (fun k i _ hi ↦ by
      rw [one_mul, Nat.ceil_natCast] at hi
      omega)

end Examples
