/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.SubspaceCount

/-!
# The count of the large solutions with Evertse's Roth lemma, in closed form

Q0.3 (`NumberField.exists_finset_submodule_of_isNormalizedSystem`) counts the subspaces that
contain the large solutions of a normalized system by `systemLargeCount`: the number of subspaces
and intervals of Layer 6.1, run once, times `1 + log ρ / log (1 + δ / (2 n))`. This file bounds
it in closed form when the chain runs with Evertse's Roth lemma (`NumberField.RothParams.evertse`,
Q1.5), and compares the result with Evertse 1996 and Evertse–Schlickewei 2002.

## Main results

* `NumberField.systemLargeCount_evertse_le`:
  `systemLargeCount ≤ c ^ (n + 7) Z ^ (n + 3) ℓ (1 + log (ℓ Z))` with
  `c = 2 ^ (n + 11) n ^ 6` (`NumberField.evertseCountConst`), `Z = c / δ`
  (`NumberField.evertseCountBase`) and `ℓ = 1 + log (2 ^ (n + 1) s ^ n)`
  (`NumberField.evertseLogFactor`), where `n` is the number of variables, `e = [E : K]` and
  `s = R e` bounds the number of distinct forms over `E` for `R` distinct forms of the system.
  Neither the number `t` of places of the system nor `|S|` enters, nor any degree, except
  `[E : K]` through `ℓ`.
* `NumberField.exists_finset_submodule_of_isNormalizedSystem_evertse_le`: Q0.3's count with that
  bound for the large solutions.
* The pieces, with the power of `δ⁻¹` each one costs: the grids in `⋀^p`
  (`NumberField.parametricGridCount_system_le`, `c ^ n Z ^ n`, one exceptional subspace each:
  `δ ^ (-n)`), the chain lengths (`NumberField.parametricChainLength_step_le`,
  `2 ℓ c ^ 6 Z ^ 2`: `δ ^ (-2)`, the square of `η⁻¹ ≤ c ^ 3 Z`) and the ratio
  (`NumberField.parametricRatio_evertse_system_le`, `32 ℓ c ^ 10 Z ^ 3`), so that
  `1 + log ρ / log (1 + δ / (2 n)) ≤ Z (1 + log (ℓ Z))`
  (`NumberField.one_add_log_parametricRatio_div_le`: `δ⁻¹` up to a logarithm). In all
  `δ ^ (-n - 3)` up to a logarithm.

## Comparison with Evertse 1996 and Evertse–Schlickewei 2002

Evertse's Theorem (i) bounds the number of subspaces for the solutions with `H(x) ≥ H` by
`(2 ^ (60 n ^ 2) δ ^ (-7 n)) ^ s log 4D log log 4D`, with `s = |S|` and `D` a bound for the
degrees of the coefficients over `K`; Evertse–Schlickewei's parametric count is
`4 ^ ((n + 8) ^ 2) δ ^ (-n - 4) log 2r log log 2r`, `r` the number of distinct forms. Here:

* **`δ`: all three counts are polynomial in `δ⁻¹`.** This is what Evertse's Roth lemma buys.
  With Bombieri–Gubler's, `log ρ` is `2 ^ m log (4 / η)` with `m` of order
  `n ^ 2 (A + 1) ^ 2 / ε ^ 2`, so the count is exponential in a power of `δ⁻¹`. The exponent here
  is `n + 3` with a factor `log δ⁻¹`, within Evertse–Schlickewei's `n + 4`: the grids cost
  `δ ^ (-n)` like their `(2 n B) ^ n` classes, the chain `δ ^ (-2)` like theirs, and the ratio
  `δ⁻¹ log δ⁻¹`. Until Q1.9b it was `2 n + 14`: the factors free of `δ` (`n!`,
  `binom(n, p) ^ 3`, `log ρ`) were bounded by powers of `Z`, and the grids rounded the constant
  `log_Q C` and the jump as two more integers in the box. Now the threshold keeps
  `log_Q C ≤ γ`, so the constant rounds to `1`, and the jump is the difference of two rounded
  minima (`NumberField.minimaJump`).
* **`n`: all three are singly exponential in `n`.** `c` carries `2 ^ n`, so the count is
  `2 ^ (O(n ^ 2))` times a power of `δ⁻¹`. Until Q1.7 the exponent carried
  `2 ^ n (2 d + e u)`, from rounding every wedge exponent in Layer 6.1 and from the patterns of
  Layer 5.4; rounding the minima instead (`NumberField.minimaGrid`, Evertse's Lemma 18) and a
  single exceptional subspace (Evertse–Schlickewei 2002, Lemma 12.4) removed both. Until Q1.8a it
  also carried `t n`, from the grid systems of Q0.3's exponents, and `Z` carried `t ^ 2`, from
  their absolute weight; the raised exponents and one scalar for the constants removed both.
* **The forms: `ℓ log ℓ` with `ℓ ≍ n log s`**, `s = R [E : K]` distinct forms over `E`:
  Evertse–Schlickewei's `log 2r log log 2r`, with the `k log 2r` of their (18.40) in `⋀^k`
  (Q1.8b; before, `s` was the number of places of `E`, without the factor `n`).
* **The degree: `d = [E : ℚ]` does not enter** (Q1.8c, Q1.9a), as in Evertse–Schlickewei;
  Evertse 1996 has `[K : ℚ]` in the exponent (through `s`) and `log 4D log log 4D` for the degree
  of the coefficients. Until Q1.8c `d` entered the exponent as `n d`, through the `n! ^ d`
  bijections of the grids of the minima, one per infinite place of `E`; with all the minima at one
  infinite place (`NumberField.exists_balance`, after Evertse–Schlickewei's one finite place) one
  bijection remains. Until Q1.9a it entered `Z` linearly, as `d ^ (2 n + 14)` in the count: the
  mesh of the grids is `∝ 1 / d`, and the constant `log_Q C` had range `1` at each infinite place.
  Layer 6.1's threshold now keeps it in `[-B, B]` like the minima, `B = N (A + 1) / d`
  (`NumberField.parametricStepThreshold` takes `log C / B`), so the box and the absolute weight
  are free of `d` (`NumberField.parametricBox_arg_eq`), and `A ∝ [E : K]` cancels against
  `ε = [E : K] δ / 4` (`NumberField.systemCoeff_div_le`).

The thresholds and the domains also differ: Q0.3 counts the solutions above the threshold `X₀`
of Layer 6.1 and handles the others by Layers 9.3 and 9.4, and its `δ` is the weight of a
normalized system.

This is Layer Q1.6 of the `QuantitativeSubspace` roadmap, with the counts of Q1.7, Q1.8a–c and
Q1.9a–b.
-/

@[expose] public section

open Finset Module MvPolynomial Height IsDedekindDomain

universe u

namespace NumberField

/-- **The constant of the closed-form count**, `c = 2 ^ (n + 11) n ^ 6`: it bounds the factors of
the count that do not depend on `δ`. -/
noncomputable def evertseCountConst (n : ℕ) : ℝ :=
  2 ^ (n + 11) * (n : ℝ) ^ 6

/-- **The base of the closed-form count**, `Z = c / δ = 2 ^ (n + 11) n ^ 6 / δ`. -/
noncomputable def evertseCountBase (n : ℕ) (δ : ℝ) : ℝ :=
  evertseCountConst n / δ

/-- **The logarithmic factor of the closed-form count**, `ℓ = 1 + log (2 ^ (n + 1) s ^ n)`, for `s`
distinct forms: it bounds `1 + log (2 binom(n, p) s ^ p)`, the logarithm in the chain length of
`⋀^p`, where at most `s ^ p` wedge forms occur. So `ℓ ≤ (n + 1) (1 + log (2 s))`. -/
noncomputable def evertseLogFactor (n s : ℕ) : ℝ :=
  1 + Real.log (2 ^ (n + 1) * (s : ℝ) ^ n)

section Base

variable {n : ℕ} {δ : ℝ}

/-- Any `x / δ` with `x ≤ 2 ^ (n + 11) n ^ 6` is at most `Z`. -/
theorem div_le_evertseCountBase (hδ : 0 < δ) {x : ℝ} (hx : x ≤ 2 ^ (n + 11) * (n : ℝ) ^ 6) :
    x / δ ≤ evertseCountBase n δ := by
  rw [evertseCountBase, evertseCountConst]; gcongr

/-- Any `x ≤ 2 ^ (n + 11) n ^ 6` is at most `Z`, as `δ ≤ 1`. -/
theorem le_evertseCountBase (hδ : 0 < δ) (hδ1 : δ ≤ 1) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 2 ^ (n + 11) * (n : ℝ) ^ 6) :
    x ≤ evertseCountBase n δ :=
  (le_div_self hx0 hδ hδ1).trans (div_le_evertseCountBase hδ hx)

/-- The monomials that the count is made of: `2 ^ (n + 11) n ^ 6` bounds `c 2 ^ n n ^ a` for
`c ≤ 2048` and `a ≤ 6`. -/
theorem monomial_le (hn : 1 ≤ n) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 2048) {a : ℕ} (ha : a ≤ 6) :
    c * 2 ^ n * (n : ℝ) ^ a ≤ 2 ^ (n + 11) * (n : ℝ) ^ 6 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc2 : 0 ≤ c * 2 ^ n := mul_nonneg hc0 (by positivity)
  rw [pow_add]
  calc c * 2 ^ n * (n : ℝ) ^ a
      ≤ 2 ^ 11 * 2 ^ n * (n : ℝ) ^ 6 := by
        gcongr
        all_goals first | assumption | linarith [show (2 : ℝ) ^ 11 = 2048 by norm_num]
    _ = _ := by ring

theorem one_le_evertseCountBase (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ evertseCountBase n δ := by
  refine le_evertseCountBase hδ hδ1 zero_le_one ?_
  have := monomial_le hn (c := 1) zero_le_one (by norm_num) (a := 0) (by norm_num)
  have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  simp only [pow_zero, mul_one, one_mul] at this
  linarith

/-- `c n ^ a ≤ 2 ^ (n + 11) n ^ 6` without the factor `2 ^ n`. -/
theorem monomial_le' (hn : 1 ≤ n) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 2048) {a : ℕ} (ha : a ≤ 6) :
    c * (n : ℝ) ^ a ≤ 2 ^ (n + 11) * (n : ℝ) ^ 6 := by
  refine le_trans ?_ (monomial_le hn hc0 hc ha)
  have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  have : 0 ≤ c * (n : ℝ) ^ a := by positivity
  nlinarith

theorem mul_two_pow_le_evertseCountBase (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    2048 * 2 ^ n ≤ evertseCountBase n δ := by
  refine le_evertseCountBase hδ hδ1 (by positivity) ?_
  have := monomial_le hn (c := 2048) (by norm_num) le_rfl (a := 0) (by norm_num)
  simpa using this

theorem two_pow_le_evertseCountBase (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (2 : ℝ) ^ n ≤ evertseCountBase n δ := by
  have := mul_two_pow_le_evertseCountBase hn hδ hδ1
  have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  linarith

theorem const_le_evertseCountBase (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    2048 ≤ evertseCountBase n δ := by
  have := mul_two_pow_le_evertseCountBase hn hδ hδ1
  have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  nlinarith

theorem evertseCountBase_nonneg (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ evertseCountBase n δ :=
  le_trans (by norm_num) (const_le_evertseCountBase hn hδ hδ1)

/-- `n ≤ Z`. -/
theorem le_evertseCountBase_self (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (n : ℝ) ≤ evertseCountBase n δ := by
  have : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
  linarith [two_pow_le_evertseCountBase hn hδ hδ1]

theorem mul_two_pow_le_evertseCountConst (hn : 1 ≤ n) : 2048 * 2 ^ n ≤ evertseCountConst n := by
  have := monomial_le hn (c := 2048) (by norm_num) le_rfl (a := 0) (by norm_num)
  simpa [evertseCountConst] using this

theorem const_le_evertseCountConst (hn : 1 ≤ n) : 2048 ≤ evertseCountConst n := by
  have := mul_two_pow_le_evertseCountConst hn
  have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  nlinarith

/-- `4 (n + 1) ≤ c`. -/
theorem four_mul_add_one_le_evertseCountConst (hn : 1 ≤ n) :
    4 * ((n : ℝ) + 1) ≤ evertseCountConst n := by
  have := mul_two_pow_le_evertseCountConst hn
  have : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
  have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  linarith

/-- `2 ^ n ≤ c`. -/
theorem two_pow_le_evertseCountConst (hn : 1 ≤ n) : (2 : ℝ) ^ n ≤ evertseCountConst n := by
  have := mul_two_pow_le_evertseCountConst hn
  have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  linarith

/-- `c ≤ Z`, as `δ ≤ 1`. -/
theorem evertseCountConst_le_base (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    evertseCountConst n ≤ evertseCountBase n δ :=
  le_div_self (by linarith [const_le_evertseCountConst hn]) hδ hδ1

theorem one_le_evertseLogFactor (n : ℕ) {s : ℕ} (hs : 1 ≤ s) : 1 ≤ evertseLogFactor n s := by
  have : (1 : ℝ) ≤ 2 ^ (n + 1) * (s : ℝ) ^ n :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) (one_le_pow₀ (by exact_mod_cast hs))
  rw [evertseLogFactor]
  linarith [Real.log_nonneg this]

/-- `1 + log (2 binom(n, p) s ^ p) ≤ ℓ`. -/
theorem one_add_log_le_evertseLogFactor {s p : ℕ} (hs : 1 ≤ s) (hp : p ≤ n) :
    1 + Real.log (2 * (n.choose p : ℝ) * ((s ^ p : ℕ) : ℝ)) ≤ evertseLogFactor n s := by
  have hC1 : (1 : ℝ) ≤ n.choose p := by exact_mod_cast Nat.choose_pos hp
  have hC2 : (n.choose p : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n p
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsp : ((s ^ p : ℕ) : ℝ) ≤ (s : ℝ) ^ n := by
    push_cast; exact pow_le_pow_right₀ hs1 hp
  have hsp1 : (1 : ℝ) ≤ ((s ^ p : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow _ _ hs
  have hpos : 0 < 2 * (n.choose p : ℝ) * ((s ^ p : ℕ) : ℝ) := by positivity
  have hle : 2 * (n.choose p : ℝ) * ((s ^ p : ℕ) : ℝ) ≤ 2 ^ (n + 1) * (s : ℝ) ^ n := by
    rw [pow_succ]
    have : (0 : ℝ) ≤ 2 ^ n := by positivity
    nlinarith [mul_le_mul hC2 hsp (by linarith) this]
  rw [evertseLogFactor]
  linarith [Real.log_le_log hpos hle]

end Base

/-! ### The pieces of the parametric Subspace Theorem -/

section Parametric

variable {N d p : ℕ} {ε A : ℝ}

/-- The box of grids: `B / γ = 4 N ^ 3 binom(N, p) (N + 2) (A + 1) / ε`, free of `d`. -/
theorem parametricBox_arg_eq (hN : 1 ≤ N) (hd : 1 ≤ d) (hp : p ≤ N) (hε : 0 < ε) :
    parametricMinimaExp N d A / parametricMesh N d p ε
      = 4 * (N : ℝ) ^ 3 * N.choose p * (N + 2) * (A + 1) / ε := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hC : (0 : ℝ) < N.choose p := by exact_mod_cast Nat.choose_pos hp
  rw [parametricMinimaExp, parametricMesh, parametricDelta]
  field_simp
  ring

theorem parametricMesh_pos (hN : 1 ≤ N) (hd : 1 ≤ d) (hp : p ≤ N) (hε : 0 < ε) :
    0 < parametricMesh N d p ε := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hC : (0 : ℝ) < N.choose p := by exact_mod_cast Nat.choose_pos hp
  rw [parametricMesh, parametricDelta]; positivity

theorem parametricBox_nonneg (hN : 1 ≤ N) (hd : 1 ≤ d) (hp : p ≤ N) (hε : 0 < ε) (hA : 0 ≤ A) :
    0 ≤ parametricBox N d p ε A := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have := parametricMesh_pos hN hd hp hε
  rw [parametricBox, parametricMinimaExp]
  exact Int.ceil_nonneg (by positivity)

/-- The box of grids is at most `4 N ^ 3 binom(N, p) (N + 2) (A + 1) / ε + 1`. -/
theorem parametricBox_le (hN : 1 ≤ N) (hd : 1 ≤ d) (hp : p ≤ N) (hε : 0 < ε) :
    (parametricBox N d p ε A : ℝ)
      ≤ 4 * (N : ℝ) ^ 3 * N.choose p * (N + 2) * (A + 1) / ε + 1 := by
  rw [parametricBox, ← parametricBox_arg_eq hN hd hp hε]
  exact (Int.ceil_lt_add_one _).le

/-- The number of grids in `⋀^p`: `N! (8 N ^ 3 binom(N, p) (N + 2) (A + 1) / ε + 3) ^ N`. -/
theorem parametricGridCount_le (hN : 1 ≤ N) (hd : 1 ≤ d) (hp : p ≤ N) (hε : 0 < ε)
    (hA : 0 ≤ A) : (parametricGridCount N d p ε A : ℝ)
      ≤ (N.factorial : ℝ)
        * (8 * (N : ℝ) ^ 3 * N.choose p * (N + 2) * (A + 1) / ε + 3) ^ N := by
  have h0 := parametricBox_nonneg hN hd hp hε hA
  have hb := parametricBox_le (A := A) hN hd hp hε
  have hcast : (((2 * parametricBox N d p ε A + 1).toNat : ℕ) : ℝ)
      = 2 * (parametricBox N d p ε A : ℝ) + 1 := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
  rw [parametricGridCount, Nat.cast_mul, Nat.cast_pow, hcast]
  have : (0 : ℝ) ≤ parametricBox N d p ε A := by exact_mod_cast h0
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) (by positivity)
  have h8 : 8 * (N : ℝ) ^ 3 * N.choose p * (N + 2) * (A + 1) / ε
      = 2 * (4 * (N : ℝ) ^ 3 * N.choose p * (N + 2) * (A + 1) / ε) := by
    ring
  linarith

/-- The absolute weight of the grid systems in `⋀^p`:
`A_p ≤ binom(N, p) (A + N ^ 2 (A + 1)) + ε`, free of `d`. -/
theorem parametricWedgeAbsWeight_le (hN : 1 ≤ N) (hd : 1 ≤ d) (hp : p ≤ N) (hε : 0 < ε) :
    parametricWedgeAbsWeight N d p ε A
      ≤ N.choose p * (A + N ^ 2 * (A + 1)) + ε := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hC : (0 : ℝ) < N.choose p := by exact_mod_cast Nat.choose_pos hp
  have hγ := parametricMesh_pos hN hd hp hε
  have hb := parametricBox_le (A := A) hN hd hp hε
  have hγb : parametricMesh N d p ε * (1 + N * parametricBox N d p ε A)
      ≤ N ^ 2 * (A + 1) / d + parametricMesh N d p ε * ((N : ℝ) + 1) := by
    calc _ ≤ parametricMesh N d p ε
          * (1 + N * (4 * (N : ℝ) ^ 3 * N.choose p * (N + 2) * (A + 1) / ε + 1)) := by gcongr
      _ = _ := by rw [parametricMesh, parametricDelta]; field_simp; ring
  have hγd : parametricMesh N d p ε * ((N : ℝ) + 1) * (N.choose p * d) ≤ ε := by
    rw [parametricMesh, parametricDelta]
    have : ε / (2 * (N : ℝ) ^ 2) / (2 * ((d : ℝ) * N.choose p * ((N : ℝ) + 2))) * ((N : ℝ) + 1)
        * (N.choose p * d) = ε * (N + 1) / (4 * (N : ℝ) ^ 2 * (N + 2)) := by
      field_simp; norm_num
    rw [this, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ N ^ 2 := one_le_pow₀ (by exact_mod_cast hN)
    have : (N : ℝ) + 1 ≤ 4 * N ^ 2 * (N + 2) := by nlinarith
    nlinarith
  rw [parametricWedgeAbsWeight]
  calc (N.choose p : ℝ) * A
        + parametricMesh N d p ε * (1 + N * parametricBox N d p ε A) * (N.choose p * d)
      ≤ N.choose p * A + (N ^ 2 * (A + 1) / d
          + parametricMesh N d p ε * ((N : ℝ) + 1)) * (N.choose p * d) := by gcongr
    _ = N.choose p * (A + N ^ 2 * (A + 1))
          + parametricMesh N d p ε * ((N : ℝ) + 1) * (N.choose p * d) := by field_simp; ring
    _ ≤ _ := by linarith

end Parametric

/-! ### The parameters of a system -/

section System

variable {n e : ℕ} {δ : ℝ}

theorem systemAbsBound_nonneg (e n : ℕ) : 0 ≤ systemAbsBound e n := by
  rw [systemAbsBound]; positivity

theorem systemAbsBound_add_one_le (hn : 1 ≤ n) (he : 1 ≤ e) :
    systemAbsBound e n + 1 ≤ 5 * e * (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  rw [systemAbsBound]
  nlinarith

/-- `n (n + 3) (A + 1) ≤ 20 e n ^ 3` for the absolute weight `A` of the system. -/
theorem systemCoeff_le (hn : 1 ≤ n) (he : 1 ≤ e) :
    (n : ℝ) * (n + 3) * (systemAbsBound e n + 1) ≤ 20 * (e * (n : ℝ) ^ 3) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hA := systemAbsBound_add_one_le hn he
  have hA0 : 0 ≤ systemAbsBound e n + 1 := by linarith [systemAbsBound_nonneg e n]
  have hnn : (n : ℝ) * (n + 3) ≤ 4 * n ^ 2 := by nlinarith
  calc (n : ℝ) * (n + 3) * (systemAbsBound e n + 1)
      ≤ 4 * n ^ 2 * (5 * e * (n : ℝ)) := mul_le_mul hnn hA hA0 (by positivity)
    _ = _ := by ring

/-- `n (n + 3) (A + 1) / ε ≤ 80 n ^ 3 / δ` for the parameters of a system: `[E : K]` cancels. -/
theorem systemCoeff_div_le (hn : 1 ≤ n) (he : 1 ≤ e) (hδ : 0 < δ) :
    (n : ℝ) * (n + 3) * (systemAbsBound e n + 1) / systemEps e δ ≤ 80 * (n : ℝ) ^ 3 / δ := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  rw [systemEps, div_le_div_iff₀ (by positivity) hδ]
  have := systemCoeff_le hn he
  have : 0 ≤ δ := hδ.le
  calc (n : ℝ) * (n + 3) * (systemAbsBound e n + 1) * δ
      ≤ 20 * (e * (n : ℝ) ^ 3) * δ := by gcongr
    _ = 80 * (n : ℝ) ^ 3 * (e * δ / 4) := by ring

/-- The base of the number of grids in `⋀^p` for a system is at most `Z`. -/
theorem systemGridBase_le (hn : 1 ≤ n) (he : 1 ≤ e) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (p : ℕ) :
    8 * (n : ℝ) ^ 3 * n.choose p * (n + 2) * (systemAbsBound e n + 1)
        / systemEps e δ + 3 ≤ evertseCountBase n δ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  have hA0 := systemAbsBound_nonneg e n
  have hstep : 8 * (n : ℝ) ^ 3 * n.choose p * (n + 2) * (systemAbsBound e n + 1) / systemEps e δ
      ≤ 8 * (n : ℝ) ^ 3 * n.choose p * (n + 2) * (n + 3) * (systemAbsBound e n + 1)
        / systemEps e δ := by
    refine div_le_div_of_nonneg_right ?_ hε.le
    have : 0 ≤ 8 * (n : ℝ) ^ 3 * n.choose p * (n + 2) * (systemAbsBound e n + 1) := by
      positivity
    nlinarith
  have hK := systemCoeff_div_le hn he hδ
  have hC : (n.choose p : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n p
  have hM : (1 : ℝ) ≤ 2 ^ n * (n : ℝ) ^ 6 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) (one_le_pow₀ hn1)
  have hmono := monomial_le hn (c := 1923) (by norm_num) (by norm_num) (a := 6) le_rfl
  set K₀ := (n : ℝ) * (n + 3) * (systemAbsBound e n + 1)
  have hn2 : (n : ℝ) + 2 ≤ 3 * n := by linarith
  have hK0 : 0 ≤ K₀ / systemEps e δ := by
    have := systemAbsBound_nonneg e n
    rw [systemEps]; positivity
  calc 8 * (n : ℝ) ^ 3 * n.choose p * (n + 2) * (systemAbsBound e n + 1)
        / systemEps e δ + 3
      ≤ 8 * (n : ℝ) ^ 3 * n.choose p * (n + 2) * (n + 3) * (systemAbsBound e n + 1)
        / systemEps e δ + 3 := by linarith
    _ = 8 * (n : ℝ) ^ 2 * n.choose p * (n + 2) * (K₀ / systemEps e δ) + 3 := by ring
    _ ≤ 8 * (n : ℝ) ^ 2 * 2 ^ n * (3 * n) * (80 * (n : ℝ) ^ 3 / δ) + 3 / δ := by
        gcongr
        exact le_div_self (by norm_num : (0 : ℝ) ≤ 3) hδ hδ1
    _ = (1920 * (2 ^ n * (n : ℝ) ^ 6) + 3) / δ := by ring
    _ ≤ _ := div_le_evertseCountBase hδ (by nlinarith)

end System

/-! ### One step of Layer 6.1 for a system -/

section Step

variable {n d e s : ℕ} {δ : ℝ}

theorem cast_choose_sub_one_add_one {p : ℕ} (hp : p ≤ n) :
    ((n.choose p - 1 : ℕ) : ℝ) + 1 = n.choose p := by
  have : 1 ≤ n.choose p := Nat.choose_pos hp
  rw [Nat.cast_sub this]; push_cast; ring

/-- `X_p ≤ c ^ 3 Z`: the bound for `η⁻¹` in `⋀^p`, of order `δ⁻¹`. -/
theorem evertseEtaInvBound_step_le (hn : 1 ≤ n) (he : 1 ≤ e) (hd : 1 ≤ d) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {p : ℕ} (hp : p ≤ n) :
    evertseEtaInvBound (n.choose p - 1) (parametricDelta n (systemEps e δ))
        (parametricWedgeAbsWeight n d p (systemEps e δ) (systemAbsBound e n))
      ≤ evertseCountConst n ^ 3 * evertseCountBase n δ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  have hC1 : (1 : ℝ) ≤ n.choose p := by exact_mod_cast Nat.choose_pos hp
  have hC2 : (n.choose p : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n p
  have hAp := parametricWedgeAbsWeight_le (A := systemAbsBound e n) hn hd hp hε
  have hn2 : (n : ℝ) ^ 2 * (systemAbsBound e n + 1)
      ≤ n * (n + 3) * (systemAbsBound e n + 1) := by
    have := systemAbsBound_nonneg e n
    have : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have hK := systemCoeff_le hn he
  have hA := systemAbsBound_add_one_le hn he
  have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn1
  have heW : (e : ℝ) ≤ e * (n : ℝ) ^ 3 := le_mul_of_one_le_right (by linarith) hn3
  have hAW : systemAbsBound e n ≤ 5 * (e * (n : ℝ) ^ 3) := by
    have : (e : ℝ) * n ≤ e * (n : ℝ) ^ 3 := by
      gcongr
      have := pow_le_pow_right₀ hn1 (show 1 ≤ 3 by norm_num)
      rwa [pow_one] at this
    linarith
  have hεW : systemEps e δ ≤ e * (n : ℝ) ^ 3 := by
    rw [systemEps]
    have : (e : ℝ) * δ / 4 ≤ e := by nlinarith
    linarith
  set W := e * (n : ℝ) ^ 3 with hW
  set C := (n.choose p : ℝ) with hC
  set Ap := parametricWedgeAbsWeight n d p (systemEps e δ) (systemAbsBound e n)
  have hAp1 : Ap + 1 ≤ 27 * C * W := by nlinarith
  have hQ : 1 ≤ C ^ 3 * ((n : ℝ) ^ 5 / δ) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 5 := one_le_pow₀ hn1
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 5 / δ := by
      rw [le_div_iff₀ hδ]; linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC1) h2
  have hmono := monomial_le' hn (c := 1729) (by norm_num) (by norm_num) (a := 5) (by norm_num)
  have hZ := div_le_evertseCountBase hδ hmono
  have hdiv : (Ap + 1) / e ≤ 27 * C * (n : ℝ) ^ 3 := by
    rw [div_le_iff₀ (by linarith)]; rw [hW] at hAp1; linarith
  rw [evertseEtaInvBound, cast_choose_sub_one_add_one hp, parametricDelta, systemEps]
  calc 1 + 8 * C ^ 2 * (Ap + 1) / (e * δ / 4 / (2 * (n : ℝ) ^ 2))
      = 1 + 64 * (n : ℝ) ^ 2 * C ^ 2 * ((Ap + 1) / e) / δ := by field_simp; ring
    _ ≤ 1 + 64 * (n : ℝ) ^ 2 * C ^ 2 * (27 * C * (n : ℝ) ^ 3) / δ := by gcongr
    _ = 1 + 1728 * (C ^ 3 * ((n : ℝ) ^ 5 / δ)) := by ring
    _ ≤ C ^ 3 * (1729 * (n : ℝ) ^ 5 / δ) := by
        have : C ^ 3 * (1729 * (n : ℝ) ^ 5 / δ)
            = 1729 * (C ^ 3 * ((n : ℝ) ^ 5 / δ)) := by ring
        linarith
    _ ≤ evertseCountConst n ^ 3 * evertseCountBase n δ := by
        have hc0 : 0 ≤ evertseCountConst n := by linarith [const_le_evertseCountConst hn]
        gcongr
        exact hC2.trans (two_pow_le_evertseCountConst hn)

/-- `T_p ≤ 2 ℓ c ^ 6 Z ^ 2`: the bound for the number of blocks in `⋀^p`, for `s` distinct forms and
`ℓ = evertseLogFactor n s`. -/
theorem evertseChainBound_step_le (hn : 1 ≤ n) (he : 1 ≤ e) (hd : 1 ≤ d) (hs : 1 ≤ s)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {p : ℕ} (hp : p ≤ n) :
    evertseChainBound (n.choose p - 1) (s ^ p) (parametricDelta n (systemEps e δ))
        (parametricWedgeAbsWeight n d p (systemEps e δ) (systemAbsBound e n))
      ≤ 2 * evertseLogFactor n s * (evertseCountConst n ^ 6 * evertseCountBase n δ ^ 2) := by
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  have hX := evertseEtaInvBound_step_le hn he hd hδ hδ1 hp
  have hX1 := one_le_evertseEtaInvBound (n.choose p - 1) (parametricDelta_pos hn hε)
    (parametricWedgeAbsWeight_nonneg n d p hε.le (systemAbsBound_nonneg e n))
  have hL := one_add_log_le_evertseLogFactor (n := n) hs hp
  have hL0 : 0 ≤ 1 + Real.log (2 * (n.choose p : ℝ) * ((s ^ p : ℕ) : ℝ)) := by
    have hC1 : (1 : ℝ) ≤ n.choose p := by exact_mod_cast Nat.choose_pos hp
    have hs1 : (1 : ℝ) ≤ ((s ^ p : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow _ _ hs
    have : (1 : ℝ) ≤ 2 * (n.choose p : ℝ) * ((s ^ p : ℕ) : ℝ) := by nlinarith
    linarith [Real.log_nonneg this]
  have hℓ0 : 0 ≤ 2 * evertseLogFactor n s := by
    linarith [one_le_evertseLogFactor n hs]
  rw [evertseChainBound, cast_choose_sub_one_add_one hp]
  calc 2 * (1 + Real.log (2 * (n.choose p : ℝ) * ((s ^ p : ℕ) : ℝ)))
        * evertseEtaInvBound (n.choose p - 1) (parametricDelta n (systemEps e δ))
          (parametricWedgeAbsWeight n d p (systemEps e δ) (systemAbsBound e n)) ^ 2
      ≤ 2 * evertseLogFactor n s * (evertseCountConst n ^ 3 * evertseCountBase n δ) ^ 2 := by
        gcongr
    _ = _ := by ring

/-- The number `m_p + 1` of blocks in `⋀^p` is at most `2 ℓ c ^ 6 Z ^ 2`. -/
theorem parametricChainLength_step_le (hn : 1 ≤ n) (he : 1 ≤ e) (hd : 1 ≤ d) (hs : 1 ≤ s)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {p : ℕ} (hp : p ≤ n) :
    (parametricChainLength n d s p (systemEps e δ) (systemAbsBound e n) : ℝ) + 1
      ≤ 2 * evertseLogFactor n s * (evertseCountConst n ^ 6 * evertseCountBase n δ ^ 2) := by
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  exact (subspaceChainLength_add_one_le _ _ (parametricDelta_pos hn hε)
    (parametricWedgeAbsWeight_nonneg n d p hε.le (systemAbsBound_nonneg e n))).trans
    (evertseChainBound_step_le hn he hd hs hδ hδ1 hp)

/-- The ratio `ρ` of the intervals of Layer 6.1 for a system, with Evertse's Roth lemma, is at
most `32 ℓ c ^ 10 Z ^ 3`. -/
theorem parametricRatio_evertse_system_le (b : ℕ → ℝ) (hn : 1 ≤ n) (he : 1 ≤ e) (hd : 1 ≤ d)
    (hs : 1 ≤ s) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    parametricRatio (RothParams.evertse b) n d s (systemEps e δ) (systemAbsBound e n)
      ≤ 32 * evertseLogFactor n s * (evertseCountConst n ^ 10 * evertseCountBase n δ ^ 3) := by
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  have hZ0 := evertseCountBase_nonneg hn hδ hδ1
  have hc0 : 0 ≤ evertseCountConst n := by linarith [const_le_evertseCountConst hn]
  have hnc : (n : ℝ) ≤ evertseCountConst n := by
    linarith [four_mul_add_one_le_evertseCountConst hn]
  have hℓ := one_le_evertseLogFactor n hs
  have hstep : ∀ p ∈ Finset.range n,
      parametricStepRatio (RothParams.evertse b) n d s p (systemEps e δ)
        (systemAbsBound e n)
        ≤ 32 * evertseLogFactor n s * (evertseCountConst n ^ 9 * evertseCountBase n δ ^ 3) :=
      fun p hp ↦ by
    have hp' : p ≤ n := (Finset.mem_range.1 hp).le
    refine (parametricStepRatio_evertse_le b d s p (by omega) hε
      (systemAbsBound_nonneg e n)).trans ?_
    have hT := evertseChainBound_step_le hn he hd hs hδ hδ1 hp'
    have hX := evertseEtaInvBound_step_le hn he hd hδ hδ1 hp'
    have hT0 := (two_le_evertseChainBound (n.choose p - 1) (s ^ p) (parametricDelta_pos hn hε)
      (parametricWedgeAbsWeight_nonneg n d p hε.le (systemAbsBound_nonneg e n)))
    calc 16 * evertseChainBound (n.choose p - 1) (s ^ p) (parametricDelta n (systemEps e δ))
          (parametricWedgeAbsWeight n d p (systemEps e δ) (systemAbsBound e n))
          * evertseEtaInvBound (n.choose p - 1) (parametricDelta n (systemEps e δ))
            (parametricWedgeAbsWeight n d p (systemEps e δ) (systemAbsBound e n))
        ≤ 16 * (2 * evertseLogFactor n s * (evertseCountConst n ^ 6 * evertseCountBase n δ ^ 2))
          * (evertseCountConst n ^ 3 * evertseCountBase n δ) := by
          have hX1 := one_le_evertseEtaInvBound (n.choose p - 1) (parametricDelta_pos hn hε)
            (parametricWedgeAbsWeight_nonneg n d p hε.le (systemAbsBound_nonneg e n))
          gcongr
      _ = _ := by ring
  calc parametricRatio (RothParams.evertse b) n d s (systemEps e δ)
        (systemAbsBound e n)
      ≤ ∑ _p ∈ Finset.range n,
          32 * evertseLogFactor n s * (evertseCountConst n ^ 9 * evertseCountBase n δ ^ 3) :=
        Finset.sum_le_sum hstep
    _ = n * (32 * evertseLogFactor n s * (evertseCountConst n ^ 9 * evertseCountBase n δ ^ 3)) := by
        simp
    _ ≤ evertseCountConst n * (32 * evertseLogFactor n s
          * (evertseCountConst n ^ 9 * evertseCountBase n δ ^ 3)) := by gcongr
    _ = _ := by ring

end Step

/-! ### The count of the large solutions -/

section Count

variable {n d e s : ℕ} {δ : ℝ}

/-- The number of grids in `⋀^p` for a system is at most `c ^ n Z ^ n`: `n! ≤ c ^ n` for the one
bijection, `Z ^ n` for the rounded minima. -/
theorem parametricGridCount_system_le (hn : 1 ≤ n) (he : 1 ≤ e) (hd : 1 ≤ d) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {p : ℕ} (hp : p ≤ n) :
    (parametricGridCount n d p (systemEps e δ) (systemAbsBound e n) : ℝ)
      ≤ evertseCountConst n ^ n * evertseCountBase n δ ^ n := by
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  have hA0 := systemAbsBound_nonneg e n
  have hnc : (n : ℝ) ≤ evertseCountConst n := by
    linarith [four_mul_add_one_le_evertseCountConst hn]
  have hfac : (n.factorial : ℝ) ≤ evertseCountConst n ^ n := by
    calc (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
      _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg n) hnc n
  calc (parametricGridCount n d p (systemEps e δ) (systemAbsBound e n) : ℝ)
      ≤ (n.factorial : ℝ) * (8 * (n : ℝ) ^ 3 * n.choose p * (n + 2)
          * (systemAbsBound e n + 1) / systemEps e δ + 3) ^ n :=
        parametricGridCount_le hn hd hp hε hA0
    _ ≤ _ := by
        have hb0 : (0 : ℝ) ≤ 8 * (n : ℝ) ^ 3 * n.choose p * (n + 2)
            * (systemAbsBound e n + 1) / systemEps e δ + 3 := by
          positivity
        exact mul_le_mul hfac
          (pow_le_pow_left₀ hb0 (systemGridBase_le hn he hδ hδ1 p) _)
          (pow_nonneg hb0 _) (pow_nonneg (hnc.trans' (Nat.cast_nonneg _)) _)

/-- The number of subspaces of Layer 6.1 for a system is at most `1 + n c ^ n Z ^ n`: one
exceptional subspace per grid, whatever the number of places. -/
theorem parametricSubspaceCount_system_le (hn : 1 ≤ n) (he : 1 ≤ e) (hd : 1 ≤ d) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    (parametricSubspaceCount n d s (systemEps e δ) (systemAbsBound e n) : ℝ)
      ≤ 1 + n * (evertseCountConst n ^ n * evertseCountBase n δ ^ n) := by
  rw [parametricSubspaceCount]
  push_cast
  gcongr
  calc ∑ p ∈ Finset.range n, (parametricGridCount n d p (systemEps e δ)
        (systemAbsBound e n) : ℝ)
      ≤ ∑ _p ∈ Finset.range n, evertseCountConst n ^ n * evertseCountBase n δ ^ n :=
        Finset.sum_le_sum fun p hp ↦
          parametricGridCount_system_le hn he hd hδ hδ1 (Finset.mem_range.1 hp).le
    _ = _ := by simp

/-- The number of intervals of Layer 6.1 for a system, with Evertse's chain, is at most
`2 n ℓ c ^ (n + 6) Z ^ (n + 2)`. -/
theorem parametricIntervalCount_system_le (hn : 1 ≤ n) (he : 1 ≤ e) (hd : 1 ≤ d) (hs : 1 ≤ s)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (parametricIntervalCount n d s (systemEps e δ) (systemAbsBound e n) : ℝ)
      ≤ n * (2 * evertseLogFactor n s
        * (evertseCountConst n ^ (n + 6) * evertseCountBase n δ ^ (n + 2))) := by
  have hstep : ∀ p ∈ Finset.range n,
      (parametricGridCount n d p (systemEps e δ) (systemAbsBound e n) : ℝ)
        * (parametricChainLength n d s p (systemEps e δ) (systemAbsBound e n) : ℝ)
      ≤ 2 * evertseLogFactor n s
        * (evertseCountConst n ^ (n + 6) * evertseCountBase n δ ^ (n + 2)) :=
    fun p hp ↦ by
      have hp' : p ≤ n := (Finset.mem_range.1 hp).le
      have hm := parametricChainLength_step_le hn he hd hs hδ hδ1 hp'
      have hZ0 := evertseCountBase_nonneg hn hδ hδ1
      have hc0 : 0 ≤ evertseCountConst n := by linarith [const_le_evertseCountConst hn]
      calc (parametricGridCount n d p (systemEps e δ) (systemAbsBound e n) : ℝ)
            * (parametricChainLength n d s p (systemEps e δ) (systemAbsBound e n) : ℝ)
          ≤ evertseCountConst n ^ n * evertseCountBase n δ ^ n
            * (2 * evertseLogFactor n s
              * (evertseCountConst n ^ 6 * evertseCountBase n δ ^ 2)) :=
            mul_le_mul (parametricGridCount_system_le hn he hd hδ hδ1 hp') (by linarith)
              (Nat.cast_nonneg _) (by positivity)
        _ = _ := by ring
  rw [parametricIntervalCount]
  push_cast
  calc ∑ p ∈ Finset.range n, (parametricGridCount n d p (systemEps e δ)
        (systemAbsBound e n) : ℝ)
        * (parametricChainLength n d s p (systemEps e δ) (systemAbsBound e n) : ℝ)
      ≤ ∑ _p ∈ Finset.range n, 2 * evertseLogFactor n s
          * (evertseCountConst n ^ (n + 6) * evertseCountBase n δ ^ (n + 2)) :=
        Finset.sum_le_sum hstep
    _ = _ := by simp

/-- The factor `1 + log ρ / log (1 + δ / (2 n))` of the count, with Evertse's Roth lemma, is at
most `Z (1 + log (ℓ Z))`: `δ⁻¹` once, up to the logarithm. -/
theorem one_add_log_parametricRatio_div_le (b : ℕ → ℝ) (hn : 1 ≤ n) (he : 1 ≤ e) (hd : 1 ≤ d)
    (hs : 1 ≤ s) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 + Real.log (parametricRatio (RothParams.evertse b) n d s (systemEps e δ)
        (systemAbsBound e n)) / Real.log (1 + δ / (2 * n))
      ≤ evertseCountBase n δ * (1 + Real.log (evertseLogFactor n s * evertseCountBase n δ)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  have hcZ := evertseCountConst_le_base hn hδ hδ1
  have hc := const_le_evertseCountConst hn
  set c := evertseCountConst n with hcdef
  set Z := evertseCountBase n δ with hZdef
  set ℓ := evertseLogFactor n s with hℓdef
  have hZ : 2048 ≤ Z := hc.trans hcZ
  have hZ0 : 0 < Z := by linarith
  have hc0 : 0 < c := by linarith
  have hℓ1 : 1 ≤ ℓ := one_le_evertseLogFactor n hs
  have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  have hlogZ : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  have hρ := parametricRatio_evertse_system_le b hn he hd hs hδ hδ1
  have hρ1 := one_le_parametricRatio (RothParams.evertse b) d s (by omega : 0 < n) hε
    (systemAbsBound_nonneg e n)
  set ρ := parametricRatio (RothParams.evertse b) n d s (systemEps e δ)
    (systemAbsBound e n) with hρdef
  have hlogρ0 : 0 ≤ Real.log ρ := Real.log_nonneg hρ1
  have hlogρ : Real.log ρ ≤ Real.log ℓ + 14 * Real.log Z := by
    have h := Real.log_le_log (by linarith) hρ
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h
    have h32 : Real.log 32 ≤ Real.log Z := Real.log_le_log (by norm_num) (by linarith)
    have hlc : Real.log c ≤ Real.log Z := Real.log_le_log hc0 hcZ
    push_cast at h
    linarith
  set x := δ / (2 * (n : ℝ)) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one (by positivity)]; linarith
  have hL : x / 2 ≤ Real.log (1 + x) := by
    refine le_trans ?_ (Real.le_log_one_add_of_nonneg hx0.le)
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have hmono := monomial_le' hn (c := 64) (by norm_num) (by norm_num) (a := 1) (by norm_num)
  rw [pow_one] at hmono
  have h64 := div_le_evertseCountBase hδ hmono
  -- `1 / (x / 2) = 4 n / δ ≤ Z / 16`
  have hinv : 1 / (x / 2) ≤ Z / 16 := by
    rw [hx, show (1 : ℝ) / (δ / (2 * n) / 2) = 64 * n / δ / 16 by field_simp; ring]
    gcongr
  have hdiv : Real.log ρ / Real.log (1 + x) ≤ Z / 16 * (Real.log ℓ + 14 * Real.log Z) := by
    calc Real.log ρ / Real.log (1 + x) ≤ Real.log ρ / (x / 2) :=
          div_le_div_of_nonneg_left hlogρ0 (by positivity) hL
      _ = Real.log ρ * (1 / (x / 2)) := by ring
      _ ≤ (Real.log ℓ + 14 * Real.log Z) * (Z / 16) :=
          mul_le_mul hlogρ hinv (by positivity) (by positivity)
      _ = _ := by ring
  rw [Real.log_mul (by positivity) (by positivity)]
  nlinarith [mul_nonneg hZ0.le hlogℓ, mul_nonneg hZ0.le hlogZ]

/-- **The number of subspaces for the large solutions of a system, with Evertse's Roth lemma, in
closed form** (Q1.6, Q1.7, Q1.8a–c, Q1.9a–b): Q0.3's `systemLargeCount` is at most
`c ^ (n + 7) Z ^ (n + 3) ℓ (1 + log (ℓ Z))` with `c = 2 ^ (n + 11) n ^ 6`, `Z = c / δ` and
`ℓ = 1 + log (2 ^ (n + 1) (r e) ^ n)`: `δ ^ (-n - 3)` up to a logarithm, singly exponential in
`n`, and `ℓ log ℓ` with `ℓ ≍ n log (r e)` in the number `r` of distinct forms. Here `n` is the
number of variables, `d = [E : ℚ]` (which does not enter) and `e = [E : K]`. -/
theorem systemLargeCount_evertse_le (b : ℕ → ℝ) {r : ℕ} (hn : 1 ≤ n) (he : 1 ≤ e) (hd : 1 ≤ d)
    (hr : 1 ≤ r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    systemLargeCount (RothParams.evertse b) n d e r δ
      ≤ evertseCountConst n ^ (n + 7) * evertseCountBase n δ ^ (n + 3)
        * (evertseLogFactor n (r * e)
          * (1 + Real.log (evertseLogFactor n (r * e) * evertseCountBase n δ))) := by
  have hs : 1 ≤ r * e := Nat.mul_le_mul hr he
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  have hcZ := evertseCountConst_le_base hn hδ hδ1
  have hc := const_le_evertseCountConst hn
  have h4n := four_mul_add_one_le_evertseCountConst hn
  set c := evertseCountConst n with hcdef
  set Z := evertseCountBase n δ with hZdef
  set ℓ := evertseLogFactor n (r * e) with hℓdef
  have hc1 : 1 ≤ c := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hℓ1 : 1 ≤ ℓ := one_le_evertseLogFactor n hs
  have hlog : 0 ≤ Real.log (ℓ * Z) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hℓ1 hZ1)
  set P := ℓ * (1 + Real.log (ℓ * Z)) with hP
  have hP1 : 1 ≤ P := by rw [hP]; nlinarith
  have hS := parametricSubspaceCount_system_le (s := r * e) hn he hd hδ hδ1
  have hI := parametricIntervalCount_system_le hn he hd hs hδ hδ1
  have hW := one_add_log_parametricRatio_div_le b hn he hd hs hδ hδ1
  have hρ1 := one_le_parametricRatio (RothParams.evertse b) d (r * e) (by omega : 0 < n) hε
    (systemAbsBound_nonneg e n)
  have hW0 : 0 ≤ 1 + Real.log (parametricRatio (RothParams.evertse b) n d (r * e)
      (systemEps e δ) (systemAbsBound e n)) / Real.log (1 + δ / (2 * n)) := by
    have : 0 < Real.log (1 + δ / (2 * n)) :=
      Real.log_pos (by have : (0 : ℝ) < δ / (2 * n) := by positivity
                       linarith)
    have := Real.log_nonneg hρ1
    positivity
  set Y := c ^ n * Z ^ n with hY
  set Q := c ^ 6 * Z ^ 3 * P with hQ
  have hY1 : 1 ≤ Y := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hc1) (one_le_pow₀ hZ1)
  have hQ1 : 1 ≤ Q :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hc1) (one_le_pow₀ hZ1)) hP1
  have hA : 1 + n * Y ≤ c / 2 * Y * Q := by
    have h1 : 1 + n * Y ≤ (1 + n) * Y := by nlinarith
    have h2 : (1 + n) * Y ≤ c / 2 * Y := by
      gcongr
      linarith
    have h3 : c / 2 * Y ≤ c / 2 * Y * Q := le_mul_of_one_le_right (by positivity) hQ1
    linarith
  have hB : 2 * n * Q * Y ≤ c / 2 * Q * Y := by
    gcongr
    linarith
  rw [systemLargeCount]
  calc (parametricSubspaceCount n d (r * e) (systemEps e δ) (systemAbsBound e n) : ℝ)
        + (parametricIntervalCount n d (r * e) (systemEps e δ) (systemAbsBound e n) : ℝ)
          * (1 + Real.log (parametricRatio (RothParams.evertse b) n d (r * e)
            (systemEps e δ) (systemAbsBound e n)) / Real.log (1 + δ / (2 * n)))
      ≤ (1 + n * Y) + n * (2 * ℓ * (c ^ (n + 6) * Z ^ (n + 2)))
          * (Z * (1 + Real.log (ℓ * Z))) := by
        gcongr
    _ = (1 + n * Y) + 2 * n * Q * Y := by rw [hY, hQ, hP]; ring
    _ ≤ c / 2 * Y * Q + c / 2 * Q * Y := by linarith
    _ = c ^ (n + 7) * Z ^ (n + 3) * P := by rw [hY, hQ]; ring

end Count

/-! ### The quantitative Subspace Theorem for a system -/

section System

variable {K : Type*} [Field K] [NumberField K] {ι : Type u} [Fintype ι]

open scoped Classical in
/-- **The quantitative Subspace Theorem for a system, with Evertse's Roth lemma, in closed form**
(Q1.6, Q1.8a–c, Q1.9a–b): as `NumberField.exists_finset_submodule_of_isNormalizedSystem_evertse`,
with the count of the large solutions bounded by `c ^ (n + 7) Z ^ (n + 3) ℓ (1 + log (ℓ Z))`,
where `c = 2 ^ (n + 11) n ^ 6`, `Z = c / δ`, `ℓ = 1 + log (2 ^ (n + 1) (R [E : K]) ^ n)` and
`n = #ι`. -/
theorem exists_finset_submodule_of_isNormalizedSystem_evertse_le {E : Type*} [Field E]
    [NumberField E] [Algebra K E] [IsGalois K E]
    (H : ∀ m : ℕ, MultiprojectiveHeight (K := E) (Prod.fst : Fin m × Fin 2 → Fin m))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {Hc : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c Hc D R δ) :
    ∃ T : Finset (Submodule K (ι → K)),
      (#T : ℝ) ≤ δ⁻¹ * ((10 ^ 3 * Fintype.card ι) ^ (Fintype.card ι * finrank ℚ K) +
          4 * Fintype.card ι * Real.log (Real.log (4 * Hc))) +
        (1 + Real.log (systemMiddleRatio (finrank ℚ K) (Fintype.card ι) Hc δ
            (systemThreshold E S w L (RothParams.evertse fun m ↦ (H m).botBound 1) R Hc δ)) /
              Real.log (1 + δ / (2 * Fintype.card ι))) +
        evertseCountConst (Fintype.card ι) ^ (Fintype.card ι + 7)
            * evertseCountBase (Fintype.card ι) δ ^ (Fintype.card ι + 3) *
          (evertseLogFactor (Fintype.card ι) (R * finrank K E) *
            (1 + Real.log (evertseLogFactor (Fintype.card ι) (R * finrank K E)
              * evertseCountBase (Fintype.card ι) δ))) ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∀ x ∈ systemSet S w L C c, ∃ U ∈ T, x ∈ U := by
  obtain ⟨T, hT, hTtop, hTmem⟩ :=
    exists_finset_submodule_of_isNormalizedSystem_evertse H S w hwInf hwFin hN
  refine ⟨T, hT.trans ?_, hTtop, hTmem⟩
  have hn : 1 ≤ Fintype.card ι := by have := hN.two_le_card; omega
  have he : 1 ≤ finrank K E := finrank_pos
  exact add_le_add_right (systemLargeCount_evertse_le _ hn he finrank_pos hN.one_le_formBound
    hN.delta_pos hN.delta_le_one) _

end System

end NumberField
