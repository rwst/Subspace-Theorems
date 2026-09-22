/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.PrimeProducts
public import DiophantineApproximation.Ridout

/-!
# Mahler's theorem on the fractional parts of `(p / q) ^ k`

**Mahler's theorem** (Mahler 1957). For coprime integers `p > q ≥ 2` and every `ε > 0`, the
distance from `(p / q) ^ k` to the nearest integer exceeds `exp (-ε k)` for all but finitely many
`k`. It is the first Diophantine *equation*-flavoured consequence of Roth's theorem in this
roadmap, and the acceptance test of Layer 3.3: Ridout's theorem is exactly the strength needed,
and Roth's theorem alone is not.

The route is Ridout's theorem at the target `1`, applied not to `(p / q) ^ k` but to the
auxiliary rational

```text
β = N q ^ k / p ^ k,        N the integer nearest to (p / q) ^ k.
```

Its distance to `1` is `q ^ k ‖(p / q) ^ k‖ / p ^ k`; the primes of `q` divide its numerator to
order at least `k`, the primes of `p` carry its whole denominator, and the two `S`-adic products
are `q ^ (-k)` and `1 / β.den`. Against a height that is at most `2 β.den`, the denominator
cancels and what is left is `‖(p / q) ^ k‖ ≤ 2 ^ (-2 - δ) p ^ (-δ k)`, which is the hypothesis.

## Main results

* `Nat.finite_setOf_exists_int_abs_sub_ratPow_le_rpow`: the finiteness with the bound
  `2 ^ (-2 - δ) p ^ (-δ k)`, which is what Ridout's theorem gives.
* `Nat.finite_setOf_exists_int_abs_sub_ratPow_le`: the same with `exp (-ε k)`.
* `Nat.eventually_exp_neg_lt_abs_sub_round`: Mahler's theorem, at the nearest integer.

## Implementation notes

⚠ **The exceptional set is genuinely nonempty, and the statement has to be `∀ᶠ`.** At `k = 0`
the number `(p / q) ^ 0` is the integer `1`, so the distance is `0` and the inequality fails for
every `ε`; there is no version quantified over all `k`. Nothing stronger is claimed, and in
particular **no bound on the exceptional set is asserted** — that is the ineffectivity of Roth's
method, inherited unchanged.

⚠ **The auxiliary rational is `N q ^ k / p ^ k`, not `(p / q) ^ k`.** Reading `(p / q) ^ k`
itself as a rational approximation to an integer gives nothing: its denominator is `q ^ k` and
Roth's theorem would ask for quality `2 + ε` against `p ^ k`, which is false. The whole gain is
that `N q ^ k / p ^ k` is close to `1`, a *fixed* algebraic number, and that its denominator is
built from the primes of `p` alone, so Ridout's product over those primes is `1 / β.den` exactly
and cancels the height.

⚠ **The gcd cancels and never needs to be named.** Reducing `N q ^ k / p ^ k` to lowest terms
divides numerator and denominator by `gcd (N, p ^ k)`, which shrinks both the height and the
`S`-adic product at the primes of `p` by the same factor. The proof never names it: it uses only
`β.den ∣ p ^ k`, `q ^ k ∣ β.num` and the bound `max |β.num| β.den ≤ 2 β.den`, and the last is
where the cancellation happens. ⚠ Using the cruder `max |β.num| β.den ≤ 2 p ^ k` instead — which
is what `Rat.max_num_den_le_of_div` gives — loses exactly that factor and the proof fails.

⚠ **The roadmap's orientation is the reciprocal of this one, and it is the orientation that
forces the gcd into the proof.** `README.md` takes `β = p ^ k / (N q ^ k)` with the target `0` at
the primes of `p` and `∞` at those of `q`. That is correct mathematics, but the denominator is
then `N q ^ k / gcd (N, p ^ k)`, whose prime factors need not divide `p q` at all, so the product
over the primes of `q` is only an estimate and the cancellation against the height has to be done
by hand. In the orientation used here the denominator divides `p ^ k`, the product over the
primes of `p` is `1 / β.den` *exactly*, and the height bound finishes it. Both orientations prove
the theorem; only one of them never mentions `gcd (N, p ^ k)`.

⚠ **Roth's theorem alone does not prove this; Ridout's does.** The finite places are not a
convenience here. Without the products over the primes of `p` and of `q` the left-hand side is
smaller by `p ^ (-2k)` and the inequality never holds, which is the concrete sense in which
Layer 3.3 and not Layer 3.2 is the input.

⚠ **`q ≥ 2` and coprimality are both needed, and for the same reason.** If `q = 1`, or if
`gcd (p, q) > 1` with `q` dividing `p`, then `(p / q) ^ k` is an integer and the distance is `0`
for every `k`. The acceptance criteria below record both.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Section 6.2.7; K. Mahler, *On the fractional parts of the powers of a rational number II*,
Mathematika 4 (1957), 122–124.

This is part of Layer 3.5 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

namespace Nat

variable {p q : ℕ}

/-- **Mahler's theorem, in the shape Ridout's theorem proves.** For coprime `p > q ≥ 2` and
`δ > 0` there are only finitely many `k` for which some integer `N` has
`|(p / q) ^ k - N| ≤ 2 ^ (-2 - δ) p ^ (-δ k)`. The constant `2 ^ (-2 - δ)` is the one the
height bound `max |β.num| β.den ≤ 2 β.den` leaves behind; it is absorbed in the `exp` form. -/
theorem finite_setOf_exists_int_abs_sub_ratPow_le_rpow (hq : 2 ≤ q) (hpq : q < p)
    (hcop : p.Coprime q) {δ : ℝ} (hδ : 0 < δ) :
    {k : ℕ | ∃ N : ℤ, |((p : ℝ) / q) ^ k - (N : ℝ)|
      ≤ (2 : ℝ) ^ (-2 - δ) * (p : ℝ) ^ (-δ * k)}.Finite := by
  classical
  have hq0 : 0 < q := lt_of_lt_of_le two_pos hq
  have hp0 : 0 < p := hq0.trans hpq
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hqpR : (q : ℝ) < (p : ℝ) := by exact_mod_cast hpq
  have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp0
  set c : ℝ := (2 : ℝ) ^ (-2 - δ) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; exact Real.rpow_pos_of_pos two_pos _
  have hc4 : c ≤ 1 / 4 := by
    have h : (2 : ℝ) ^ (-2 - δ) ≤ (2 : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
    rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast] at h
    norm_num at h
    rw [hcdef]
    linarith
  -- the set, and a choice of nearest integer on it
  obtain ⟨A, hAval⟩ : ∃ A : Set ℕ,
      A = {k : ℕ | ∃ N : ℤ, |((p : ℝ) / q) ^ k - (N : ℝ)|
        ≤ c * (p : ℝ) ^ (-δ * (k : ℝ))} := ⟨_, rfl⟩
  have hAmem : ∀ k : ℕ, k ∈ A ↔ ∃ N : ℤ, |((p : ℝ) / q) ^ k - (N : ℝ)|
      ≤ c * (p : ℝ) ^ (-δ * (k : ℝ)) := fun k ↦ by rw [hAval]; rfl
  rw [← hAval]
  choose! Nf hNf using fun k (hk : k ∈ A) ↦ (hAmem k).mp hk
  obtain ⟨n, hnval⟩ : ∃ n : ℕ → ℤ, ∀ k, n k = Nf k * (q : ℤ) ^ k := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨m, hmval⟩ : ∃ m : ℕ → ℤ, ∀ k, m k = (p : ℤ) ^ k := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨f, hfval⟩ : ∃ f : ℕ → ℚ, ∀ k, f k = ((n k : ℤ) : ℚ) / ((m k : ℤ) : ℚ) :=
    ⟨_, fun _ ↦ rfl⟩
  -- elementary bounds on the size of the local factor
  have hE0 : ∀ k : ℕ, 0 < c * (p : ℝ) ^ (-δ * (k : ℝ)) :=
    fun k ↦ mul_pos hc0 (Real.rpow_pos_of_pos hpR _)
  have hEle : ∀ k : ℕ, c * (p : ℝ) ^ (-δ * (k : ℝ)) ≤ 1 / 4 := by
    intro k
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h1 : (p : ℝ) ^ (-δ * (k : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hp1R (by nlinarith)
    nlinarith [Real.rpow_pos_of_pos hpR (-δ * (k : ℝ))]
  have hθ1 : ∀ k : ℕ, (1 : ℝ) ≤ ((p : ℝ) / q) ^ k := fun k ↦
    one_le_pow₀ (by rw [le_div_iff₀ hqR]; linarith)
  -- the nearest integer is positive, and `n k ≤ 2 m k`
  have hm0 : ∀ k : ℕ, (0 : ℤ) < m k := fun k ↦ by
    rw [hmval k]; exact pow_pos (by exact_mod_cast hp0) k
  have hmR : ∀ k : ℕ, ((m k : ℤ) : ℝ) = (p : ℝ) ^ k := fun k ↦ by
    rw [hmval k]; push_cast; ring
  have hN1 : ∀ k ∈ A, (1 : ℤ) ≤ Nf k := by
    intro k hk
    have h := (abs_le.mp (hNf k hk)).2
    have hpos : (0 : ℝ) < ((Nf k : ℤ) : ℝ) := by linarith [hθ1 k, hEle k]
    have : (0 : ℤ) < Nf k := by exact_mod_cast hpos
    omega
  have hn0 : ∀ k ∈ A, (0 : ℤ) < n k := by
    intro k hk
    rw [hnval k]
    exact mul_pos (lt_of_lt_of_le zero_lt_one (hN1 k hk)) (pow_pos (by exact_mod_cast hq0) k)
  have hn2m : ∀ k ∈ A, ((n k : ℤ) : ℝ) ≤ 2 * ((m k : ℤ) : ℝ) := by
    intro k hk
    have h := (abs_le.mp (hNf k hk)).1
    have hqk : (0 : ℝ) < (q : ℝ) ^ k := pow_pos hqR k
    have hqpk : ((q : ℝ)) ^ k ≤ ((p : ℝ)) ^ k := pow_le_pow_left₀ hqR.le hqpR.le k
    have hθ : ((p : ℝ) / q) ^ k * (q : ℝ) ^ k = (p : ℝ) ^ k := by
      rw [div_pow]; field_simp
    calc ((n k : ℤ) : ℝ) = ((Nf k : ℤ) : ℝ) * (q : ℝ) ^ k := by rw [hnval k]; push_cast; ring
      _ ≤ (((p : ℝ) / q) ^ k + c * (p : ℝ) ^ (-δ * (k : ℝ))) * (q : ℝ) ^ k := by
          exact mul_le_mul_of_nonneg_right (by linarith) hqk.le
      _ = (p : ℝ) ^ k + (c * (p : ℝ) ^ (-δ * (k : ℝ))) * (q : ℝ) ^ k := by rw [add_mul, hθ]
      _ ≤ (p : ℝ) ^ k + (1 / 4) * (p : ℝ) ^ k := by nlinarith [hEle k, (hE0 k).le]
      _ ≤ 2 * ((m k : ℤ) : ℝ) := by rw [hmR k]; linarith
  -- the arithmetic of the auxiliary rational
  have hcross : ∀ k : ℕ, (f k).num * m k = n k * ((f k).den : ℤ) := by
    intro k
    have hd : (((f k).den : ℚ)) ≠ 0 := by exact_mod_cast (f k).den_nz
    have hmq : ((m k : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (hm0 k).ne'
    have h1 : (((f k).num : ℚ)) / (((f k).den : ℚ)) = ((n k : ℤ) : ℚ) / ((m k : ℤ) : ℚ) := by
      rw [Rat.num_div_den, hfval k]
    rw [div_eq_div_iff hd hmq] at h1
    exact_mod_cast h1
  have hdendvd : ∀ k : ℕ, ((f k).den : ℤ) ∣ m k := fun k ↦ by
    rw [hfval k, ← Rat.divInt_eq_div]
    exact Rat.den_dvd _ _
  have hdendvdnat : ∀ k : ℕ, (f k).den ∣ p ^ k := by
    intro k
    have h := hdendvd k
    rw [hmval k] at h
    have h2 : (((f k).den : ℕ) : ℤ) ∣ ((p ^ k : ℕ) : ℤ) := by push_cast; exact h
    exact Int.natCast_dvd_natCast.mp h2
  have hcopk : ∀ k : ℕ, IsCoprime ((q : ℤ) ^ k) ((p : ℤ) ^ k) := fun k ↦
    (Nat.isCoprime_iff_coprime.mpr hcop.symm).pow
  have hqdvd : ∀ k : ℕ, ((q : ℤ)) ^ k ∣ (f k).num := by
    intro k
    refine (hcopk k).dvd_of_dvd_mul_right ?_
    rw [← hmval k, hcross k, hnval k]
    exact ⟨Nf k * ((f k).den : ℤ), by ring⟩
  -- the two `S`-adic products
  have hP2 : ∀ k : ℕ, (∏ l ∈ p.primesOf, padicNorm (l : ℕ) (((f k).den : ℕ) : ℚ))
      = (((f k).den : ℕ) : ℚ)⁻¹ := by
    intro k
    refine Rat.prod_padicNorm_natCast _ _ (f k).den_nz fun l hl ↦ ?_
    exact Nat.mem_primesOf_of_dvd_pow hp0.ne' (hl.trans (hdendvdnat k))
  have hP1 : ∀ k : ℕ, (∏ l ∈ q.primesOf, padicNorm (l : ℕ) (((f k).num : ℤ) : ℚ))
      ≤ ((q ^ k : ℕ) : ℚ)⁻¹ := by
    intro k
    refine le_trans (Rat.prod_padicNorm_le_of_dvd _ (hqdvd k)) (le_of_eq ?_)
    rw [show ((((q : ℤ)) ^ k : ℤ) : ℚ) = ((q ^ k : ℕ) : ℚ) by push_cast; ring]
    exact Rat.prod_padicNorm_natCast _ _ (pow_ne_zero k hq0.ne')
      fun l hl ↦ Nat.mem_primesOf_of_dvd_pow hq0.ne' hl
  -- the distance of the auxiliary rational to `1`
  have hone : ∀ k ∈ A, |(1 : ℝ) - ((f k : ℚ) : ℝ)|
      ≤ ((q : ℝ) ^ k * (c * (p : ℝ) ^ (-δ * (k : ℝ)))) / (p : ℝ) ^ k := by
    intro k hk
    have hmne : ((m k : ℤ) : ℝ) ≠ 0 := by rw [hmR k]; exact (pow_pos hpR k).ne'
    have hfR : ((f k : ℚ) : ℝ) = ((n k : ℤ) : ℝ) / ((m k : ℤ) : ℝ) := by
      rw [hfval k]; push_cast; ring
    have hdiff : (1 : ℝ) - ((f k : ℚ) : ℝ)
        = (((m k : ℤ) : ℝ) - ((n k : ℤ) : ℝ)) / ((m k : ℤ) : ℝ) := by
      rw [hfR]; field_simp
    have heq : ((m k : ℤ) : ℝ) - ((n k : ℤ) : ℝ)
        = (q : ℝ) ^ k * (((p : ℝ) / q) ^ k - ((Nf k : ℤ) : ℝ)) := by
      rw [hmval k, hnval k, div_pow]
      have hqk : ((q : ℝ)) ^ k ≠ 0 := (pow_pos hqR k).ne'
      push_cast
      field_simp
    have habsmn : |((m k : ℤ) : ℝ) - ((n k : ℤ) : ℝ)|
        ≤ (q : ℝ) ^ k * (c * (p : ℝ) ^ (-δ * (k : ℝ))) := by
      rw [heq, abs_mul, abs_of_pos (pow_pos hqR k)]
      exact mul_le_mul_of_nonneg_left (hNf k hk) (by positivity)
    have habsm : |((m k : ℤ) : ℝ)| = (p : ℝ) ^ k := by
      rw [hmR k, abs_of_pos (pow_pos hpR k)]
    rw [hdiff, abs_div, habsm, div_le_div_iff₀ (pow_pos hpR k) (pow_pos hpR k)]
    exact mul_le_mul_of_nonneg_right habsmn (pow_pos hpR k).le
  -- membership in Ridout's finite set
  set S₁ : Finset Nat.Primes := q.primesOf with hS₁def
  set S₂ : Finset Nat.Primes := p.primesOf with hS₂def
  set R : Set ℚ := {β : ℚ | |(1 : ℝ) - (β : ℝ)|
      * (∏ l ∈ S₁, ((padicNorm (l : ℕ) β.num : ℚ) : ℝ))
      * ∏ l ∈ S₂, ((padicNorm (l : ℕ) β.den : ℚ) : ℝ)
    ≤ (max β.num.natAbs β.den : ℝ) ^ (-2 - δ)} with hRdef
  have hRfin : R.Finite := Rat.finite_setOf_ridout isAlgebraic_one S₁ S₂ hδ
  have hmem : ∀ k ∈ A, f k ∈ R := by
    intro k hk
    rw [hRdef, Set.mem_ofPred_eq]
    have hd0 : (0 : ℝ) < ((f k).den : ℝ) := by exact_mod_cast (f k).pos
    have hdle : (((f k).den : ℕ) : ℝ) ≤ (p : ℝ) ^ k := by
      have := Nat.le_of_dvd (pow_pos hp0 k) (hdendvdnat k)
      have h2 : (((f k).den : ℕ) : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h2
      exact h2
    -- the height is at most twice the denominator
    have hfkpos : (0 : ℚ) < f k := by
      rw [hfval k]
      have h1 : (0 : ℚ) < ((n k : ℤ) : ℚ) := by exact_mod_cast hn0 k hk
      have h2 : (0 : ℚ) < ((m k : ℤ) : ℚ) := by exact_mod_cast hm0 k
      exact _root_.div_pos h1 h2
    have hnumpos : 0 < (f k).num := Rat.num_pos.mpr hfkpos
    have hnumle : (f k).num ≤ 2 * ((f k).den : ℤ) := by
      have hdpos : (0 : ℤ) < ((f k).den : ℤ) := by exact_mod_cast (f k).pos
      have h1 : (f k).num * m k ≤ (2 * ((f k).den : ℤ)) * m k := by
        rw [hcross k]
        have hn2 : n k ≤ 2 * m k := by exact_mod_cast hn2m k hk
        nlinarith [hm0 k]
      exact le_of_mul_le_mul_right h1 (hm0 k)
    have hmaxle : max (((f k).num.natAbs : ℕ) : ℝ) (((f k).den : ℕ) : ℝ)
        ≤ 2 * (((f k).den : ℕ) : ℝ) := by
      refine max_le ?_ (by linarith)
      have : (f k).num.natAbs ≤ 2 * (f k).den := by omega
      have h2 : (((f k).num.natAbs : ℕ) : ℝ) ≤ ((2 * (f k).den : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h2
      exact h2
    -- the two products, read in `ℝ`
    have hX2 : (∏ l ∈ S₁, ((padicNorm (l : ℕ) ((f k).num : ℚ) : ℚ) : ℝ))
        ≤ ((q : ℝ) ^ k)⁻¹ := by
      have h : ((∏ l ∈ S₁, padicNorm (l : ℕ) (((f k).num : ℤ) : ℚ) : ℚ) : ℝ)
          ≤ ((((q ^ k : ℕ) : ℚ)⁻¹ : ℚ) : ℝ) := by exact_mod_cast hP1 k
      rw [Rat.cast_prod, show ((((q ^ k : ℕ) : ℚ)⁻¹ : ℚ) : ℝ) = ((q : ℝ) ^ k)⁻¹ by
        push_cast; ring] at h
      exact h
    have hX3 : (∏ l ∈ S₂, ((padicNorm (l : ℕ) ((f k).den : ℚ) : ℚ) : ℝ))
        = (((f k).den : ℕ) : ℝ)⁻¹ := by
      have h : ((∏ l ∈ S₂, padicNorm (l : ℕ) (((f k).den : ℕ) : ℚ) : ℚ) : ℝ)
          = (((((f k).den : ℕ) : ℚ)⁻¹ : ℚ) : ℝ) := by exact_mod_cast hP2 k
      rw [Rat.cast_prod, show ((((((f k).den : ℕ) : ℚ)⁻¹ : ℚ) : ℝ)) = (((f k).den : ℕ) : ℝ)⁻¹ by
        push_cast; ring] at h
      exact h
    -- the assembled inequality
    have hprodnn : (0 : ℝ) ≤ ∏ l ∈ S₁, ((padicNorm (l : ℕ) ((f k).num : ℚ) : ℚ) : ℝ) :=
      Finset.prod_nonneg fun l _ ↦ by exact_mod_cast padicNorm.nonneg (p := (l : ℕ)) _
    have hA0nn : (0 : ℝ) ≤ ((q : ℝ) ^ k * (c * (p : ℝ) ^ (-δ * (k : ℝ)))) / (p : ℝ) ^ k := by
      positivity
    have hstep1 : |(1 : ℝ) - ((f k : ℚ) : ℝ)|
        * (∏ l ∈ S₁, ((padicNorm (l : ℕ) ((f k).num : ℚ) : ℚ) : ℝ))
        ≤ (((q : ℝ) ^ k * (c * (p : ℝ) ^ (-δ * (k : ℝ)))) / (p : ℝ) ^ k) * ((q : ℝ) ^ k)⁻¹ :=
      mul_le_mul (hone k hk) hX2 hprodnn hA0nn
    have hcollapse : ((((q : ℝ) ^ k * (c * (p : ℝ) ^ (-δ * (k : ℝ)))) / (p : ℝ) ^ k)
        * ((q : ℝ) ^ k)⁻¹) * (((f k).den : ℕ) : ℝ)⁻¹
        = (c * (p : ℝ) ^ (-δ * (k : ℝ))) / ((p : ℝ) ^ k * (((f k).den : ℕ) : ℝ)) := by
      have h1 : ((q : ℝ) ^ k) ≠ 0 := (pow_pos hqR k).ne'
      have h2 : ((p : ℝ) ^ k) ≠ 0 := (pow_pos hpR k).ne'
      have h3 : (((f k).den : ℕ) : ℝ) ≠ 0 := hd0.ne'
      field_simp
    -- the exponent bookkeeping
    have hPpos : (0 : ℝ) < (p : ℝ) ^ k := pow_pos hpR k
    have hPrpow : ((p : ℝ) ^ k) ^ (-δ) = (p : ℝ) ^ (-δ * (k : ℝ)) := by
      rw [← Real.rpow_natCast (p : ℝ) k, ← Real.rpow_mul hpR.le]
      ring_nf
    have hPsplit : ((p : ℝ) ^ k) ^ (-δ)
        = ((p : ℝ) ^ k) * (((p : ℝ) ^ k) ^ (-1 - δ)) := by
      have h := Real.rpow_add hPpos 1 (-1 - δ)
      rw [Real.rpow_one] at h
      rw [show (-δ : ℝ) = (1 : ℝ) + (-1 - δ) by ring, h]
    have hkey : c * (p : ℝ) ^ (-δ * (k : ℝ))
        ≤ c * ((p : ℝ) ^ k) * ((((f k).den : ℕ) : ℝ) ^ (-1 - δ)) := by
      rw [← hPrpow, hPsplit]
      have h1 : ((p : ℝ) ^ k) ^ (-1 - δ) ≤ ((((f k).den : ℕ) : ℝ)) ^ (-1 - δ) :=
        Real.rpow_le_rpow_of_nonpos hd0 hdle (by linarith)
      calc c * (((p : ℝ) ^ k) * (((p : ℝ) ^ k) ^ (-1 - δ)))
          = (c * ((p : ℝ) ^ k)) * (((p : ℝ) ^ k) ^ (-1 - δ)) := by ring
        _ ≤ (c * ((p : ℝ) ^ k)) * ((((f k).den : ℕ) : ℝ) ^ (-1 - δ)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = c * ((p : ℝ) ^ k) * ((((f k).den : ℕ) : ℝ) ^ (-1 - δ)) := by ring
    have hdsplit : ((((f k).den : ℕ) : ℝ) ^ (-2 - δ)) * (((f k).den : ℕ) : ℝ)
        = (((f k).den : ℕ) : ℝ) ^ (-1 - δ) := by
      have h := Real.rpow_add hd0 (-2 - δ) 1
      rw [Real.rpow_one] at h
      rw [show (-1 - δ : ℝ) = (-2 - δ) + 1 by ring, h]
    have hfinal : (c * (p : ℝ) ^ (-δ * (k : ℝ))) / ((p : ℝ) ^ k * (((f k).den : ℕ) : ℝ))
        ≤ c * ((((f k).den : ℕ) : ℝ) ^ (-2 - δ)) := by
      rw [div_le_iff₀ (by positivity)]
      calc c * (p : ℝ) ^ (-δ * (k : ℝ))
          ≤ c * ((p : ℝ) ^ k) * ((((f k).den : ℕ) : ℝ) ^ (-1 - δ)) := hkey
        _ = c * ((((f k).den : ℕ) : ℝ) ^ (-2 - δ)) * ((p : ℝ) ^ k * (((f k).den : ℕ) : ℝ)) := by
            rw [← hdsplit]; ring
    have hrhs : c * ((((f k).den : ℕ) : ℝ) ^ (-2 - δ))
        ≤ (max (((f k).num.natAbs : ℕ) : ℝ) (((f k).den : ℕ) : ℝ)) ^ (-2 - δ) := by
      have h2d : (2 * (((f k).den : ℕ) : ℝ)) ^ (-2 - δ)
          = c * ((((f k).den : ℕ) : ℝ) ^ (-2 - δ)) := by
        rw [Real.mul_rpow (by norm_num) hd0.le, hcdef]
      rw [← h2d]
      refine Real.rpow_le_rpow_of_nonpos ?_ hmaxle (by linarith)
      exact lt_of_lt_of_le hd0 (le_max_right _ _)
    calc |(1 : ℝ) - ((f k : ℚ) : ℝ)|
          * (∏ l ∈ S₁, ((padicNorm (l : ℕ) ((f k).num : ℚ) : ℚ) : ℝ))
          * ∏ l ∈ S₂, ((padicNorm (l : ℕ) ((f k).den : ℚ) : ℚ) : ℝ)
        = |(1 : ℝ) - ((f k : ℚ) : ℝ)|
            * (∏ l ∈ S₁, ((padicNorm (l : ℕ) ((f k).num : ℚ) : ℚ) : ℝ))
            * (((f k).den : ℕ) : ℝ)⁻¹ := by rw [hX3]
      _ ≤ ((((q : ℝ) ^ k * (c * (p : ℝ) ^ (-δ * (k : ℝ)))) / (p : ℝ) ^ k)
            * ((q : ℝ) ^ k)⁻¹) * (((f k).den : ℕ) : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hstep1 (by positivity)
      _ = (c * (p : ℝ) ^ (-δ * (k : ℝ))) / ((p : ℝ) ^ k * (((f k).den : ℕ) : ℝ)) := hcollapse
      _ ≤ c * ((((f k).den : ℕ) : ℝ) ^ (-2 - δ)) := hfinal
      _ ≤ (max (((f k).num.natAbs : ℕ) : ℝ) (((f k).den : ℕ) : ℝ)) ^ (-2 - δ) := hrhs
  -- the auxiliary rationals are distinct, so finitely many `β` means finitely many `k`
  have hclose : ∀ k ∈ A, |(1 : ℝ) - ((f k : ℚ) : ℝ)| ≤ ((q : ℝ) / (p : ℝ)) ^ k := by
    intro k hk
    refine (hone k hk).trans ?_
    rw [div_pow, div_le_div_iff₀ (pow_pos hpR k) (pow_pos hpR k)]
    have h1 : c * (p : ℝ) ^ (-δ * (k : ℝ)) ≤ 1 := le_trans (hEle k) (by norm_num)
    have h2 : (0 : ℝ) < (q : ℝ) ^ k * (p : ℝ) ^ k :=
      mul_pos (pow_pos hqR k) (pow_pos hpR k)
    nlinarith [h1, h2]
  have hne1 : ∀ k ∈ A, 1 ≤ k → f k ≠ 1 := by
    intro k hk hk1 hcon
    have hmq : ((m k : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (hm0 k).ne'
    have h0 : ((n k : ℤ) : ℚ) / ((m k : ℤ) : ℚ) = 1 := by rw [← hfval k]; exact hcon
    have h1 : n k = m k := by exact_mod_cast (div_eq_one_iff_eq hmq).mp h0
    have h3 : ((q : ℤ)) ^ k ∣ ((p : ℤ)) ^ k := by
      rw [← hmval k, ← h1, hnval k]
      exact ⟨Nf k, by ring⟩
    have h4 : q ^ k ∣ p ^ k := by exact_mod_cast h3
    have h5 : q ^ k = 1 := (Nat.Coprime.pow k k hcop.symm).eq_one_of_dvd h4
    have h6 : 2 ≤ q ^ k := le_trans hq (Nat.le_self_pow (by omega) q)
    omega
  have hqp1 : ((q : ℝ) / (p : ℝ)) < 1 := by rw [div_lt_one hpR]; exact hqpR
  have hqp0 : (0 : ℝ) ≤ (q : ℝ) / (p : ℝ) := by positivity
  have hfib : ∀ b : ℚ,
      {k : ℕ | |(1 : ℝ) - (b : ℝ)| ≤ ((q : ℝ) / (p : ℝ)) ^ k ∧ b ≠ 1}.Finite := by
    intro b
    by_cases hb : b = 1
    · convert Set.finite_empty
      ext k
      simp [hb]
    have hb0 : (0 : ℝ) < |(1 : ℝ) - (b : ℝ)| := by
      rw [abs_pos, sub_ne_zero]
      exact fun hcon ↦ hb (by exact_mod_cast hcon.symm)
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hb0 hqp1
    refine Set.Finite.subset (Set.finite_Iio M) fun k hk ↦ ?_
    rw [Set.mem_Iio]
    by_contra hcon
    push Not at hcon
    have hmono : ((q : ℝ) / (p : ℝ)) ^ k ≤ ((q : ℝ) / (p : ℝ)) ^ M :=
      pow_le_pow_of_le_one hqp0 hqp1.le hcon
    exact absurd (hk.1.trans hmono) (not_le.mpr hM)
  refine Set.Finite.subset ((Set.finite_Iio 1).union (hRfin.biUnion fun b _ ↦ hfib b)) ?_
  intro k hk
  rcases Nat.lt_or_ge k 1 with hk1 | hk1
  · exact Or.inl hk1
  exact Or.inr (Set.mem_biUnion (hmem k hk) ⟨hclose k hk, hne1 k hk hk1⟩)

/-- **Mahler's theorem, as a finiteness statement.** For coprime `p > q ≥ 2` and `ε > 0`, only
finitely many `k` admit an integer within `exp (-ε k)` of `(p / q) ^ k`. The constant of
`finite_setOf_exists_int_abs_sub_ratPow_le_rpow` is absorbed by discarding an initial segment,
and the exponent `δ` is chosen so that `p ^ (-δ k)` is `exp (-ε k / 2)`. -/
theorem finite_setOf_exists_int_abs_sub_ratPow_le (hq : 2 ≤ q) (hpq : q < p)
    (hcop : p.Coprime q) {ε : ℝ} (hε : 0 < ε) :
    {k : ℕ | ∃ N : ℤ, |((p : ℝ) / q) ^ k - (N : ℝ)| ≤ Real.exp (-ε * k)}.Finite := by
  have hp1N : 1 < p := by omega
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp1N
  have hpR : (0 : ℝ) < (p : ℝ) := by linarith
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hlogne : Real.log (p : ℝ) ≠ 0 := hlogp.ne'
  set δ : ℝ := ε / (2 * Real.log (p : ℝ)) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδlog : δ * Real.log (p : ℝ) = ε / 2 := by rw [hδdef]; field_simp
  set c : ℝ := (2 : ℝ) ^ (-2 - δ) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; exact Real.rpow_pos_of_pos two_pos _
  obtain ⟨K, hK⟩ := exists_nat_gt (-(2 / ε) * Real.log c)
  refine Set.Finite.subset ((Set.finite_Iio K).union
    (finite_setOf_exists_int_abs_sub_ratPow_le_rpow hq hpq hcop hδ0)) ?_
  intro k hk
  rcases lt_or_ge k K with h | h
  · exact Or.inl h
  refine Or.inr ?_
  obtain ⟨N, hN⟩ := hk
  refine ⟨N, hN.trans ?_⟩
  rw [← hcdef]
  have hk' : ((K : ℝ)) ≤ (k : ℝ) := by exact_mod_cast h
  have hprpow : (p : ℝ) ^ (-δ * (k : ℝ)) = Real.exp (-(ε / 2) * (k : ℝ)) := by
    rw [Real.rpow_def_of_pos hpR,
      show Real.log (p : ℝ) * (-δ * (k : ℝ)) = -(ε / 2) * (k : ℝ) by rw [← hδlog]; ring]
  have hlt : -(ε / 2) * (k : ℝ) ≤ Real.log c := by
    have h1 : -(ε / 2) * (k : ℝ) ≤ -(ε / 2) * (-(2 / ε) * Real.log c) := by
      refine mul_le_mul_of_nonpos_left ?_ (by linarith)
      linarith
    have h2 : -(ε / 2) * (-(2 / ε) * Real.log c) = Real.log c := by field_simp
    linarith
  have hexp : Real.exp (-(ε / 2) * (k : ℝ)) ≤ c :=
    (Real.exp_le_exp.mpr hlt).trans_eq (Real.exp_log hc0)
  rw [hprpow]
  calc Real.exp (-ε * (k : ℝ))
      = Real.exp (-(ε / 2) * (k : ℝ)) * Real.exp (-(ε / 2) * (k : ℝ)) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ c * Real.exp (-(ε / 2) * (k : ℝ)) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le

/-- **Mahler's theorem** (Mahler 1957; Bombieri–Gubler 6.2.7 for `3 / 2`). For coprime integers
`p > q ≥ 2` and every `ε > 0`, the distance from `(p / q) ^ k` to the nearest integer exceeds
`exp (-ε k)` for all but finitely many `k`. ⚠ No bound on the exceptional set is asserted, and
none is available by this method. -/
theorem eventually_exp_neg_lt_abs_sub_round (hq : 2 ≤ q) (hpq : q < p) (hcop : p.Coprime q)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in Filter.atTop,
      Real.exp (-ε * k) < |((p : ℝ) / q) ^ k - round (((p : ℝ) / q) ^ k)| := by
  obtain ⟨K, hK⟩ := (finite_setOf_exists_int_abs_sub_ratPow_le hq hpq hcop hε).bddAbove
  rw [Filter.eventually_atTop]
  refine ⟨K + 1, fun k hk ↦ ?_⟩
  by_contra hcon
  push Not at hcon
  have hmem : k ∈ {k : ℕ | ∃ N : ℤ, |((p : ℝ) / q) ^ k - (N : ℝ)| ≤ Real.exp (-ε * k)} :=
    ⟨round (((p : ℝ) / q) ^ k), hcon⟩
  have hle := hK hmem
  omega

end Nat

/-! ### Acceptance criteria -/

/-- **The roadmap's acceptance test.** `‖(3 / 2) ^ k‖ > exp (-k / 10)` for all but finitely many
`k`, with no value of the exceptional set asserted. -/
example : ∀ᶠ k : ℕ in Filter.atTop,
    Real.exp (-(k : ℝ) / 10) < |((3 : ℝ) / 2) ^ k - round (((3 : ℝ) / 2) ^ k)| := by
  have h := Nat.eventually_exp_neg_lt_abs_sub_round (p := 3) (q := 2) (by norm_num) (by norm_num)
    (by norm_num) (ε := 1 / 10) (by norm_num)
  filter_upwards [h] with k hk
  have e1 : ((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = (3 : ℝ) / 2 := by norm_num
  have e2 : -(1 / 10 : ℝ) * (k : ℝ) = -(k : ℝ) / 10 := by ring
  rw [e1, e2] at hk
  exact hk

/-- **`k = 0` is in the exceptional set for every `ε`**, so the conclusion has to be `∀ᶠ` and
cannot be `∀`: `(p / q) ^ 0` is the integer `1`. -/
example (ε : ℝ) : ∃ N : ℤ,
    |((3 : ℝ) / 2) ^ (0 : ℕ) - (N : ℝ)| ≤ Real.exp (-ε * ((0 : ℕ) : ℝ)) := by
  refine ⟨1, ?_⟩
  simp

/-- **Rejection test: `2 ≤ q` is not removable.** With `q = 1` — coprime to `p` and less than it
— the power is an integer, the distance is `0`, and the conclusion fails for every `ε`. -/
example (ε : ℝ) : ¬ ∀ᶠ k : ℕ in Filter.atTop,
    Real.exp (-ε * k) < |((3 : ℝ) / 1) ^ k - round (((3 : ℝ) / 1) ^ k)| := by
  intro h
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp h
  have h0 := hK K le_rfl
  have he : ((3 : ℝ) / 1) ^ K = (((3 ^ K : ℤ)) : ℝ) := by push_cast; ring
  rw [he, round_intCast, sub_self, abs_zero] at h0
  exact absurd h0 (not_lt.mpr (Real.exp_pos _).le)

/-- **Rejection test: coprimality is not removable.** With `p = 4`, `q = 2` — where `2 ≤ q` and
`q < p` both hold — the power is again an integer. -/
example (ε : ℝ) : ¬ ∀ᶠ k : ℕ in Filter.atTop,
    Real.exp (-ε * k) < |((4 : ℝ) / 2) ^ k - round (((4 : ℝ) / 2) ^ k)| := by
  intro h
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp h
  have h0 := hK K le_rfl
  have he : ((4 : ℝ) / 2) ^ K = (((2 ^ K : ℤ)) : ℝ) := by
    rw [show ((4 : ℝ) / 2) = 2 by norm_num]
    push_cast
    ring
  rw [he, round_intCast, sub_self, abs_zero] at h0
  exact absurd h0 (not_lt.mpr (Real.exp_pos _).le)

end
