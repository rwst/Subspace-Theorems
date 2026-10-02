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
  `systemLargeCount ≤ Z ^ (2 n + 14) ℓ (1 + log ℓ)` with
  `Z = 2 ^ (n + 11) n ^ 6 d / δ` (`NumberField.evertseCountBase`) and
  `ℓ = 1 + log (2 ^ (n + 1) s ^ n)` (`NumberField.evertseLogFactor`), where `n` is the number
  of variables, `d = [E : ℚ]`, `e = [E : K]` and `s = R e` bounds the number of distinct forms over
  `E` for `R` distinct forms of the system. Neither the number `t` of places of the system nor
  `|S|` enters.
* `NumberField.exists_finset_submodule_of_isNormalizedSystem_evertse_le`: Q0.3's count with that
  bound for the large solutions.
* The pieces: the grids in `⋀^p` (`NumberField.parametricGridCount_system_le`,
  `Z ^ (2 n + 2)`, one exceptional subspace each), the chain lengths
  (`NumberField.parametricChainLength_step_le`, `2 ℓ Z ^ 8`) and the ratio
  (`NumberField.parametricRatio_evertse_system_le`, `32 ℓ Z ^ 13`), so that
  `1 + log ρ / log (1 + δ / (2 n)) ≤ Z ^ 2 (1 + log ℓ)`
  (`NumberField.one_add_log_parametricRatio_div_le`).

## Comparison with Evertse 1996 and Evertse–Schlickewei 2002

Evertse's Theorem (i) bounds the number of subspaces for the solutions with `H(x) ≥ H` by
`(2 ^ (60 n ^ 2) δ ^ (-7 n)) ^ s log 4D log log 4D`, with `s = |S|` and `D` a bound for the
degrees of the coefficients over `K`; Evertse–Schlickewei's parametric count is
`4 ^ ((n + 8) ^ 2) δ ^ (-n - 4) log 2r log log 2r`, `r` the number of distinct forms. Here:

* **`δ`: all three counts are polynomial in `δ⁻¹`.** This is what Evertse's Roth lemma buys.
  With Bombieri–Gubler's, `log ρ` is `2 ^ m log (4 / η)` with `m` of order
  `n ^ 2 (A + 1) ^ 2 / ε ^ 2`, so the count is exponential in a power of `δ⁻¹`. The exponent here
  is `2 n + 14`.
* **`n`: all three are singly exponential in `n`.** `Z` carries `2 ^ n`, so the count is
  `2 ^ (O(n ^ 2))` times a power of `d` and `δ⁻¹`. Until Q1.7 the exponent carried
  `2 ^ n (2 d + e u)`, from rounding every wedge exponent in Layer 6.1 and from the patterns of
  Layer 5.4; rounding the minima instead (`NumberField.minimaGrid`, Evertse's Lemma 18) and a
  single exceptional subspace (Evertse–Schlickewei 2002, Lemma 12.4) removed both. Until Q1.8a it
  also carried `t n`, from the grid systems of Q0.3's exponents, and `Z` carried `t ^ 2`, from
  their absolute weight; the raised exponents and one scalar for the constants removed both.
* **The forms: `ℓ log ℓ` with `ℓ ≍ n log s`**, `s = R [E : K]` distinct forms over `E`:
  Evertse–Schlickewei's `log 2r log log 2r`, with the `k log 2r` of their (18.40) in `⋀^k`
  (Q1.8b; before, `s` was the number of places of `E`, without the factor `n`).
* **The degree: `d = [E : ℚ]` no longer enters the exponent** (Q1.8c). Until then it entered as
  `n d`, through the `n! ^ d` bijections of the grids of the minima, one per infinite place of
  `E`; with all the minima at one infinite place (`NumberField.exists_balance`, after
  Evertse–Schlickewei's one finite place) one bijection remains. `d` is left in `Z`, linearly:
  through the mesh of the grids and `[E : K] ≤ d` in the absolute weight, so the count is
  `d ^ (2 n + 14)` where Evertse–Schlickewei have nothing, and Evertse 1996 has `[K : ℚ]` in the
  exponent (through `s`) and `log 4D log log 4D` for the degree of the coefficients.

The thresholds and the domains also differ: Q0.3 counts the solutions above the threshold `X₀`
of Layer 6.1 and handles the others by Layers 9.3 and 9.4, and its `δ` is the weight of a
normalized system.

This is Layer Q1.6 of the `QuantitativeSubspace` roadmap, with the counts of Q1.7 and Q1.8a–c.
-/

@[expose] public section

open Finset Module MvPolynomial Height IsDedekindDomain

universe u

namespace NumberField

/-- **The base of the closed-form count**, `Z = 2 ^ (n + 11) n ^ 6 d / δ`. -/
noncomputable def evertseCountBase (n d : ℕ) (δ : ℝ) : ℝ :=
  2 ^ (n + 11) * (n : ℝ) ^ 6 * d / δ

/-- **The logarithmic factor of the closed-form count**, `ℓ = 1 + log (2 ^ (n + 1) s ^ n)`, for `s`
distinct forms: it bounds `1 + log (2 binom(n, p) s ^ p)`, the logarithm in the chain length of
`⋀^p`, where at most `s ^ p` wedge forms occur. So `ℓ ≤ (n + 1) (1 + log (2 s))`. -/
noncomputable def evertseLogFactor (n s : ℕ) : ℝ :=
  1 + Real.log (2 ^ (n + 1) * (s : ℝ) ^ n)

section Base

variable {n d : ℕ} {δ : ℝ}

/-- Any `x / δ` with `x ≤ 2 ^ (n + 11) n ^ 6 d` is at most `Z`. -/
theorem div_le_evertseCountBase (hδ : 0 < δ) {x : ℝ}
    (hx : x ≤ 2 ^ (n + 11) * (n : ℝ) ^ 6 * d) :
    x / δ ≤ evertseCountBase n d δ := by
  rw [evertseCountBase]; gcongr

/-- Any `x ≤ 2 ^ (n + 11) n ^ 6 d` is at most `Z`, as `δ ≤ 1`. -/
theorem le_evertseCountBase (hδ : 0 < δ) (hδ1 : δ ≤ 1) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 2 ^ (n + 11) * (n : ℝ) ^ 6 * d) :
    x ≤ evertseCountBase n d δ :=
  (le_div_self hx0 hδ hδ1).trans (div_le_evertseCountBase hδ hx)

/-- The monomials that the count is made of: `2 ^ (n + 11) n ^ 6 d` bounds `c 2 ^ n n ^ a d ^ k`
for `c ≤ 2048`, `a ≤ 6` and `k ≤ 1`. -/
theorem monomial_le (hn : 1 ≤ n) (hd : 1 ≤ d) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 2048) {a k : ℕ}
    (ha : a ≤ 6) (hk : k ≤ 1) :
    c * 2 ^ n * (n : ℝ) ^ a * (d : ℝ) ^ k ≤ 2 ^ (n + 11) * (n : ℝ) ^ 6 * d := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hc2 : 0 ≤ c * 2 ^ n := mul_nonneg hc0 (by positivity)
  rw [pow_add]
  calc c * 2 ^ n * (n : ℝ) ^ a * (d : ℝ) ^ k
      ≤ 2 ^ 11 * 2 ^ n * (n : ℝ) ^ 6 * (d : ℝ) ^ 1 := by
        gcongr
        all_goals first | assumption | linarith [show (2 : ℝ) ^ 11 = 2048 by norm_num]
    _ = _ := by ring

theorem one_le_evertseCountBase (hn : 1 ≤ n) (hd : 1 ≤ d) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ evertseCountBase n d δ := by
  refine le_evertseCountBase hδ hδ1 zero_le_one ?_
  have := monomial_le hn hd (c := 1) zero_le_one (by norm_num) (a := 0) (k := 0)
    (by norm_num) (by norm_num)
  have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  simp only [pow_zero, mul_one, one_mul] at this
  linarith

/-- `c n ^ a d ^ k ≤ 2 ^ (n + 11) n ^ 6 d` without the factor `2 ^ n`. -/
theorem monomial_le' (hn : 1 ≤ n) (hd : 1 ≤ d) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 2048) {a k : ℕ}
    (ha : a ≤ 6) (hk : k ≤ 1) :
    c * (n : ℝ) ^ a * (d : ℝ) ^ k ≤ 2 ^ (n + 11) * (n : ℝ) ^ 6 * d := by
  refine le_trans ?_ (monomial_le hn hd hc0 hc ha hk)
  have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  have : 0 ≤ c * (n : ℝ) ^ a * (d : ℝ) ^ k := by positivity
  nlinarith

theorem mul_two_pow_le_evertseCountBase (hn : 1 ≤ n) (hd : 1 ≤ d) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) : 2048 * 2 ^ n ≤ evertseCountBase n d δ := by
  refine le_evertseCountBase hδ hδ1 (by positivity) ?_
  have := monomial_le hn hd (c := 2048) (by norm_num) le_rfl (a := 0) (k := 0)
    (by norm_num) (by norm_num)
  simpa using this

theorem two_pow_le_evertseCountBase (hn : 1 ≤ n) (hd : 1 ≤ d) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (2 : ℝ) ^ n ≤ evertseCountBase n d δ := by
  have := mul_two_pow_le_evertseCountBase hn hd hδ hδ1
  have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  linarith

theorem const_le_evertseCountBase (hn : 1 ≤ n) (hd : 1 ≤ d) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    2048 ≤ evertseCountBase n d δ := by
  have := mul_two_pow_le_evertseCountBase hn hd hδ hδ1
  have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  nlinarith

theorem evertseCountBase_nonneg (hn : 1 ≤ n) (hd : 1 ≤ d) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ evertseCountBase n d δ :=
  le_trans (by norm_num) (const_le_evertseCountBase hn hd hδ hδ1)

/-- `n ≤ Z`. -/
theorem le_evertseCountBase_self (hn : 1 ≤ n) (hd : 1 ≤ d) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (n : ℝ) ≤ evertseCountBase n d δ := by
  have : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
  linarith [two_pow_le_evertseCountBase hn hd hδ hδ1]

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

/-- The box of grids: `Y / γ = 4 N ^ 2 binom(N, p) (N + 2) (d + N (N + 2) (A + 1)) / ε`. -/
theorem parametricBox_arg_eq (hN : 1 ≤ N) (hd : 1 ≤ d) (hp : p ≤ N) (hε : 0 < ε) :
    (1 + parametricMinimaExp N d A * N + 2 * parametricMinimaExp N d A) / parametricMesh N d p ε
      = 4 * (N : ℝ) ^ 2 * N.choose p * (N + 2) * (d + N * (N + 2) * (A + 1)) / ε := by
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

/-- The box of grids is at most `4 N ^ 2 binom(N, p) (N + 2) (d + N (N + 2) (A + 1)) / ε + 1`. -/
theorem parametricBox_le (hN : 1 ≤ N) (hd : 1 ≤ d) (hp : p ≤ N) (hε : 0 < ε) :
    (parametricBox N d p ε A : ℝ)
      ≤ 4 * (N : ℝ) ^ 2 * N.choose p * (N + 2) * (d + N * (N + 2) * (A + 1)) / ε + 1 := by
  rw [parametricBox, ← parametricBox_arg_eq hN hd hp hε]
  exact (Int.ceil_lt_add_one _).le

/-- The number of grids in `⋀^p`:
`N! (8 N ^ 2 binom(N, p) (N + 2) (d + N (N + 2) (A + 1)) / ε + 3) ^ (N + 2)`. -/
theorem parametricGridCount_le (hN : 1 ≤ N) (hd : 1 ≤ d) (hp : p ≤ N) (hε : 0 < ε)
    (hA : 0 ≤ A) : (parametricGridCount N d p ε A : ℝ)
      ≤ (N.factorial : ℝ)
        * (8 * (N : ℝ) ^ 2 * N.choose p * (N + 2) * (d + N * (N + 2) * (A + 1)) / ε + 3)
          ^ (N + 2) := by
  have h0 := parametricBox_nonneg hN hd hp hε hA
  have hb := parametricBox_le (A := A) hN hd hp hε
  have hcast : (((2 * parametricBox N d p ε A + 1).toNat : ℕ) : ℝ)
      = 2 * (parametricBox N d p ε A : ℝ) + 1 := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
  rw [parametricGridCount, Nat.cast_mul, Nat.cast_pow, hcast]
  have : (0 : ℝ) ≤ parametricBox N d p ε A := by exact_mod_cast h0
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) (by positivity)
  have h8 : 8 * (N : ℝ) ^ 2 * N.choose p * (N + 2) * (d + N * (N + 2) * (A + 1)) / ε
      = 2 * (4 * (N : ℝ) ^ 2 * N.choose p * (N + 2) * (d + N * (N + 2) * (A + 1)) / ε) := by
    ring
  linarith

/-- The absolute weight of the grid systems in `⋀^p`:
`A_p ≤ binom(N, p) (A + d + N (N + 2) (A + 1)) + ε`. -/
theorem parametricWedgeAbsWeight_le (hN : 1 ≤ N) (hd : 1 ≤ d) (hp : p ≤ N) (hε : 0 < ε) :
    parametricWedgeAbsWeight N d p ε A
      ≤ N.choose p * (A + d + N * (N + 2) * (A + 1)) + ε := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hC : (0 : ℝ) < N.choose p := by exact_mod_cast Nat.choose_pos hp
  have hγ := parametricMesh_pos hN hd hp hε
  have hb := parametricBox_le (A := A) hN hd hp hε
  have hN2 : (N : ℝ) + 2 ≠ 0 := by positivity
  have hγb : parametricMesh N d p ε * (parametricBox N d p ε A + N + 2)
      ≤ (d + N * (N + 2) * (A + 1)) / d + parametricMesh N d p ε * ((N : ℝ) + 3) := by
    calc _ ≤ parametricMesh N d p ε
          * ((4 * (N : ℝ) ^ 2 * N.choose p * (N + 2) * (d + N * (N + 2) * (A + 1)) / ε + 1)
            + N + 2) := by gcongr
      _ = _ := by rw [parametricMesh, parametricDelta]; field_simp; ring
  have hγd : parametricMesh N d p ε * ((N : ℝ) + 3) * (N.choose p * d) ≤ ε := by
    rw [parametricMesh, parametricDelta]
    have : ε / (2 * (N : ℝ) ^ 2) / (2 * ((d : ℝ) * N.choose p * ((N : ℝ) + 2))) * ((N : ℝ) + 3)
        * (N.choose p * d) = ε * (N + 3) / (4 * (N : ℝ) ^ 2 * (N + 2)) := by
      field_simp; norm_num
    rw [this, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ N ^ 2 := one_le_pow₀ (by exact_mod_cast hN)
    have : (N : ℝ) + 3 ≤ 4 * N ^ 2 * (N + 2) := by nlinarith
    nlinarith
  rw [parametricWedgeAbsWeight]
  calc (N.choose p : ℝ) * A
        + parametricMesh N d p ε * (parametricBox N d p ε A + N + 2) * (N.choose p * d)
      ≤ N.choose p * A + ((d + N * (N + 2) * (A + 1)) / d
          + parametricMesh N d p ε * ((N : ℝ) + 3)) * (N.choose p * d) := by gcongr
    _ = N.choose p * (A + d + N * (N + 2) * (A + 1))
          + parametricMesh N d p ε * ((N : ℝ) + 3) * (N.choose p * d) := by field_simp; ring
    _ ≤ _ := by linarith

end Parametric

/-! ### The parameters of a system -/

section System

variable {n d e : ℕ} {δ : ℝ}

theorem systemAbsBound_nonneg (e n : ℕ) : 0 ≤ systemAbsBound e n := by
  rw [systemAbsBound]; positivity

theorem systemAbsBound_add_one_le (hn : 1 ≤ n) (he : 1 ≤ e) :
    systemAbsBound e n + 1 ≤ 5 * e * (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  rw [systemAbsBound]
  nlinarith

/-- `d + n (n + 2) (A + 1) ≤ 16 d n ^ 3` for the absolute weight `A` of the system. -/
theorem systemCoeff_le (hn : 1 ≤ n) (he : 1 ≤ e) (hed : e ≤ d) :
    (d : ℝ) + n * (n + 2) * (systemAbsBound e n + 1) ≤ 16 * d * (n : ℝ) ^ 3 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hed' : (e : ℝ) ≤ d := by exact_mod_cast hed
  have hA := systemAbsBound_add_one_le hn he
  have hA0 : 0 ≤ systemAbsBound e n + 1 := by linarith [systemAbsBound_nonneg e n]
  have hP : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn1
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc (d : ℝ) + n * (n + 2) * (systemAbsBound e n + 1)
      ≤ d * (n : ℝ) ^ 3 + 3 * n ^ 2 * (5 * e * (n : ℝ)) := by
        have hnn : (n : ℝ) * (n + 2) ≤ 3 * n ^ 2 := by nlinarith
        exact add_le_add (le_mul_of_one_le_right hd0 hP) (mul_le_mul hnn hA hA0 (by positivity))
    _ ≤ d * (n : ℝ) ^ 3 + 3 * n ^ 2 * (5 * d * (n : ℝ)) := by gcongr
    _ = _ := by ring

/-- The base of the number of grids in `⋀^p` for a system is at most `Z`. -/
theorem systemGridBase_le (hn : 1 ≤ n) (he : 1 ≤ e) (hed : e ≤ d) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (p : ℕ) :
    8 * (n : ℝ) ^ 2 * n.choose p * (n + 2) * (d + n * (n + 2) * (systemAbsBound e n + 1))
        / systemEps e δ + 3 ≤ evertseCountBase n d δ := by
  have hd : 1 ≤ d := he.trans hed
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hK := systemCoeff_le hn he hed
  have hC : (n.choose p : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n p
  have hM : (1 : ℝ) ≤ 2 ^ n * (n : ℝ) ^ 6 * d :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) (one_le_pow₀ hn1)) hd1
  have hmono := monomial_le hn hd (c := 1539) (by norm_num) (by norm_num) (a := 6) (k := 1)
    le_rfl le_rfl
  rw [pow_one] at hmono
  have hK0 : 0 ≤ (d : ℝ) + n * (n + 2) * (systemAbsBound e n + 1) := by
    have := systemAbsBound_nonneg e n
    positivity
  set K₀ := (d : ℝ) + n * (n + 2) * (systemAbsBound e n + 1)
  have hn2 : (n : ℝ) + 2 ≤ 3 * n := by linarith
  calc 8 * (n : ℝ) ^ 2 * n.choose p * (n + 2) * K₀ / systemEps e δ + 3
      = 32 * (n : ℝ) ^ 2 * n.choose p * (n + 2) * K₀ / (e * δ) + 3 := by
        rw [systemEps]; field_simp; ring
    _ ≤ 32 * (n : ℝ) ^ 2 * n.choose p * (n + 2) * K₀ / δ + 3 / δ := by
        gcongr
        · nlinarith
        · exact le_div_self (by norm_num) hδ hδ1
    _ ≤ 32 * (n : ℝ) ^ 2 * 2 ^ n * (3 * n) * (16 * d * (n : ℝ) ^ 3) / δ + 3 / δ := by
        gcongr
    _ = (1536 * (2 ^ n * (n : ℝ) ^ 6 * d) + 3) / δ := by ring
    _ ≤ _ := div_le_evertseCountBase hδ (by nlinarith)

end System

/-! ### One step of Layer 6.1 for a system -/

section Step

variable {n d e s : ℕ} {δ : ℝ}

theorem cast_choose_sub_one_add_one {p : ℕ} (hp : p ≤ n) :
    ((n.choose p - 1 : ℕ) : ℝ) + 1 = n.choose p := by
  have : 1 ≤ n.choose p := Nat.choose_pos hp
  rw [Nat.cast_sub this]; push_cast; ring

/-- `X_p ≤ Z ^ 4`: the bound for `η⁻¹` in `⋀^p`. -/
theorem evertseEtaInvBound_step_le (hn : 1 ≤ n) (he : 1 ≤ e) (hed : e ≤ d) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {p : ℕ} (hp : p ≤ n) :
    evertseEtaInvBound (n.choose p - 1) (parametricDelta n (systemEps e δ))
        (parametricWedgeAbsWeight n d p (systemEps e δ) (systemAbsBound e n))
      ≤ evertseCountBase n d δ ^ 4 := by
  have hd : 1 ≤ d := he.trans hed
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hed' : (e : ℝ) ≤ d := by exact_mod_cast hed
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  have hC1 : (1 : ℝ) ≤ n.choose p := by exact_mod_cast Nat.choose_pos hp
  have hC2 : (n.choose p : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n p
  have hAp := parametricWedgeAbsWeight_le (A := systemAbsBound e n) hn hd hp hε
  have hK := systemCoeff_le hn he hed
  have hA := systemAbsBound_add_one_le hn he
  have hn13 : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    calc (n : ℝ) = n ^ 1 := (pow_one _).symm
      _ ≤ n ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
  have hW1 : (1 : ℝ) ≤ d * (n : ℝ) ^ 3 :=
    one_le_mul_of_one_le_of_one_le hd1 (one_le_pow₀ hn1)
  have hAW : systemAbsBound e n ≤ 5 * (d * (n : ℝ) ^ 3) := by
    have : (e : ℝ) * n ≤ d * (n : ℝ) ^ 3 := by gcongr
    linarith
  have hεW : systemEps e δ ≤ d * (n : ℝ) ^ 3 := by
    rw [systemEps]
    have : (e : ℝ) * δ / 4 ≤ e := by nlinarith
    have : (d : ℝ) ≤ d * (n : ℝ) ^ 3 := le_mul_of_one_le_right (by linarith) (one_le_pow₀ hn1)
    linarith
  set W := d * (n : ℝ) ^ 3 with hW
  set C := (n.choose p : ℝ) with hC
  set Ap := parametricWedgeAbsWeight n d p (systemEps e δ) (systemAbsBound e n)
  have hAp1 : Ap + 1 ≤ 23 * C * W := by nlinarith
  have hAp0 : 0 ≤ Ap := parametricWedgeAbsWeight_nonneg n d p hε.le (systemAbsBound_nonneg e n)
  have hQ : 1 ≤ C ^ 3 * ((n : ℝ) ^ 5 * d / δ) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 5 * d := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn1) hd1
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 5 * d / δ := by
      rw [le_div_iff₀ hδ]; linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC1) h2
  have hmono := monomial_le' hn hd (c := 1473) (by norm_num) (by norm_num) (a := 5) (k := 1)
    (by norm_num) le_rfl
  rw [pow_one] at hmono
  have hZ := div_le_evertseCountBase hδ hmono
  have h2Z := two_pow_le_evertseCountBase hn hd hδ hδ1
  rw [evertseEtaInvBound, cast_choose_sub_one_add_one hp, parametricDelta, systemEps]
  calc 1 + 8 * C ^ 2 * (Ap + 1) / (e * δ / 4 / (2 * (n : ℝ) ^ 2))
      = 1 + 64 * (n : ℝ) ^ 2 * C ^ 2 * (Ap + 1) / (e * δ) := by field_simp; ring
    _ ≤ 1 + 64 * (n : ℝ) ^ 2 * C ^ 2 * (23 * C * W) / δ := by
        gcongr
        nlinarith
    _ = 1 + 1472 * (C ^ 3 * ((n : ℝ) ^ 5 * d / δ)) := by rw [hW]; ring
    _ ≤ C ^ 3 * (1473 * (n : ℝ) ^ 5 * d / δ) := by
        have : C ^ 3 * (1473 * (n : ℝ) ^ 5 * d / δ)
            = 1473 * (C ^ 3 * ((n : ℝ) ^ 5 * d / δ)) := by ring
        linarith
    _ ≤ evertseCountBase n d δ ^ 3 * evertseCountBase n d δ := by
        have hZ0 := evertseCountBase_nonneg hn hd hδ hδ1
        gcongr
        exact hC2.trans h2Z
    _ = _ := by ring

/-- `T_p ≤ 2 ℓ Z ^ 8`: the bound for the number of blocks in `⋀^p`, for `s` distinct forms and
`ℓ = evertseLogFactor n s`. -/
theorem evertseChainBound_step_le (hn : 1 ≤ n) (he : 1 ≤ e) (hed : e ≤ d) (hs : 1 ≤ s)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {p : ℕ} (hp : p ≤ n) :
    evertseChainBound (n.choose p - 1) (s ^ p) (parametricDelta n (systemEps e δ))
        (parametricWedgeAbsWeight n d p (systemEps e δ) (systemAbsBound e n))
      ≤ 2 * evertseLogFactor n s * evertseCountBase n d δ ^ 8 := by
  have hd : 1 ≤ d := he.trans hed
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  have hX := evertseEtaInvBound_step_le hn he hed hδ hδ1 hp
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
      ≤ 2 * evertseLogFactor n s * (evertseCountBase n d δ ^ 4) ^ 2 := by
        gcongr
    _ = _ := by ring

/-- The number `m_p + 1` of blocks in `⋀^p` is at most `2 ℓ Z ^ 8`. -/
theorem parametricChainLength_step_le (hn : 1 ≤ n) (he : 1 ≤ e) (hed : e ≤ d) (hs : 1 ≤ s)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {p : ℕ} (hp : p ≤ n) :
    (parametricChainLength n d s p (systemEps e δ) (systemAbsBound e n) : ℝ) + 1
      ≤ 2 * evertseLogFactor n s * evertseCountBase n d δ ^ 8 := by
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  exact (subspaceChainLength_add_one_le _ _ (parametricDelta_pos hn hε)
    (parametricWedgeAbsWeight_nonneg n d p hε.le (systemAbsBound_nonneg e n))).trans
    (evertseChainBound_step_le hn he hed hs hδ hδ1 hp)

/-- The ratio `ρ` of the intervals of Layer 6.1 for a system, with Evertse's Roth lemma, is at
most `32 ℓ Z ^ 13`. -/
theorem parametricRatio_evertse_system_le (b : ℕ → ℝ) (hn : 1 ≤ n) (he : 1 ≤ e) (hed : e ≤ d)
    (hs : 1 ≤ s) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    parametricRatio (RothParams.evertse b) n d s (systemEps e δ) (systemAbsBound e n)
      ≤ 32 * evertseLogFactor n s * evertseCountBase n d δ ^ 13 := by
  have hd : 1 ≤ d := he.trans hed
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  have hZ0 := evertseCountBase_nonneg hn hd hδ hδ1
  have hnZ := le_evertseCountBase_self hn hd hδ hδ1
  have hℓ := one_le_evertseLogFactor n hs
  have hstep : ∀ p ∈ Finset.range n,
      parametricStepRatio (RothParams.evertse b) n d s p (systemEps e δ)
        (systemAbsBound e n)
        ≤ 32 * evertseLogFactor n s * evertseCountBase n d δ ^ 12 := fun p hp ↦ by
    have hp' : p ≤ n := (Finset.mem_range.1 hp).le
    refine (parametricStepRatio_evertse_le b d s p (by omega) hε
      (systemAbsBound_nonneg e n)).trans ?_
    have hT := evertseChainBound_step_le hn he hed hs hδ hδ1 hp'
    have hX := evertseEtaInvBound_step_le hn he hed hδ hδ1 hp'
    have hT0 := (two_le_evertseChainBound (n.choose p - 1) (s ^ p) (parametricDelta_pos hn hε)
      (parametricWedgeAbsWeight_nonneg n d p hε.le (systemAbsBound_nonneg e n)))
    calc 16 * evertseChainBound (n.choose p - 1) (s ^ p) (parametricDelta n (systemEps e δ))
          (parametricWedgeAbsWeight n d p (systemEps e δ) (systemAbsBound e n))
          * evertseEtaInvBound (n.choose p - 1) (parametricDelta n (systemEps e δ))
            (parametricWedgeAbsWeight n d p (systemEps e δ) (systemAbsBound e n))
        ≤ 16 * (2 * evertseLogFactor n s * evertseCountBase n d δ ^ 8)
          * evertseCountBase n d δ ^ 4 := by
          have hX1 := one_le_evertseEtaInvBound (n.choose p - 1) (parametricDelta_pos hn hε)
            (parametricWedgeAbsWeight_nonneg n d p hε.le (systemAbsBound_nonneg e n))
          gcongr
      _ = _ := by ring
  calc parametricRatio (RothParams.evertse b) n d s (systemEps e δ)
        (systemAbsBound e n)
      ≤ ∑ _p ∈ Finset.range n, 32 * evertseLogFactor n s * evertseCountBase n d δ ^ 12 :=
        Finset.sum_le_sum hstep
    _ = n * (32 * evertseLogFactor n s * evertseCountBase n d δ ^ 12) := by simp
    _ ≤ evertseCountBase n d δ * (32 * evertseLogFactor n s
          * evertseCountBase n d δ ^ 12) := by gcongr
    _ = _ := by ring

end Step

/-! ### The count of the large solutions -/

section Count

variable {n d e s : ℕ} {δ : ℝ}

/-- The number of grids in `⋀^p` for a system is at most `Z ^ (2 n + 2)`: `n! ≤ Z ^ n` for the
one bijection, `Z ^ (n + 2)` for the integers. -/
theorem parametricGridCount_system_le (hn : 1 ≤ n) (he : 1 ≤ e) (hed : e ≤ d) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {p : ℕ} (hp : p ≤ n) :
    (parametricGridCount n d p (systemEps e δ) (systemAbsBound e n) : ℝ)
      ≤ evertseCountBase n d δ ^ (2 * n + 2) := by
  have hd : 1 ≤ d := he.trans hed
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  have hA0 := systemAbsBound_nonneg e n
  have hnZ := le_evertseCountBase_self hn hd hδ hδ1
  have hfac : (n.factorial : ℝ) ≤ evertseCountBase n d δ ^ n := by
    calc (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
      _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg n) hnZ n
  calc (parametricGridCount n d p (systemEps e δ) (systemAbsBound e n) : ℝ)
      ≤ (n.factorial : ℝ) * (8 * (n : ℝ) ^ 2 * n.choose p * (n + 2)
          * (d + n * (n + 2) * (systemAbsBound e n + 1)) / systemEps e δ + 3) ^ (n + 2) :=
        parametricGridCount_le hn hd hp hε hA0
    _ ≤ evertseCountBase n d δ ^ n * evertseCountBase n d δ ^ (n + 2) := by
        have hb0 : (0 : ℝ) ≤ 8 * (n : ℝ) ^ 2 * n.choose p * (n + 2)
            * (d + n * (n + 2) * (systemAbsBound e n + 1)) / systemEps e δ + 3 := by
          positivity
        exact mul_le_mul hfac
          (pow_le_pow_left₀ hb0 (systemGridBase_le hn he hed hδ hδ1 p) _)
          (pow_nonneg hb0 _) (pow_nonneg (hnZ.trans' (Nat.cast_nonneg _)) _)
    _ = _ := by rw [← pow_add]; ring_nf

/-- The number of subspaces of Layer 6.1 for a system is at most `1 + n Z ^ (2 n + 2)`: one
exceptional subspace per grid, whatever the number of places. -/
theorem parametricSubspaceCount_system_le (hn : 1 ≤ n) (he : 1 ≤ e) (hed : e ≤ d) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    (parametricSubspaceCount n d s (systemEps e δ) (systemAbsBound e n) : ℝ)
      ≤ 1 + n * evertseCountBase n d δ ^ (2 * n + 2) := by
  rw [parametricSubspaceCount]
  push_cast
  gcongr
  calc ∑ p ∈ Finset.range n, (parametricGridCount n d p (systemEps e δ)
        (systemAbsBound e n) : ℝ)
      ≤ ∑ _p ∈ Finset.range n, evertseCountBase n d δ ^ (2 * n + 2) :=
        Finset.sum_le_sum fun p hp ↦
          parametricGridCount_system_le hn he hed hδ hδ1 (Finset.mem_range.1 hp).le
    _ = _ := by simp

/-- The number of intervals of Layer 6.1 for a system, with Evertse's chain, is at most
`2 n ℓ Z ^ (2 n + 10)`. -/
theorem parametricIntervalCount_system_le (hn : 1 ≤ n) (he : 1 ≤ e) (hed : e ≤ d) (hs : 1 ≤ s)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (parametricIntervalCount n d s (systemEps e δ) (systemAbsBound e n) : ℝ)
      ≤ n * (2 * evertseLogFactor n s * evertseCountBase n d δ ^ (2 * n + 10)) := by
  have hstep : ∀ p ∈ Finset.range n,
      (parametricGridCount n d p (systemEps e δ) (systemAbsBound e n) : ℝ)
        * (parametricChainLength n d s p (systemEps e δ) (systemAbsBound e n) : ℝ)
      ≤ 2 * evertseLogFactor n s * evertseCountBase n d δ ^ (2 * n + 10) :=
    fun p hp ↦ by
      have hp' : p ≤ n := (Finset.mem_range.1 hp).le
      have hm := parametricChainLength_step_le hn he hed hs hδ hδ1 hp'
      have hZ0 := evertseCountBase_nonneg hn (he.trans hed) hδ hδ1
      calc (parametricGridCount n d p (systemEps e δ) (systemAbsBound e n) : ℝ)
            * (parametricChainLength n d s p (systemEps e δ) (systemAbsBound e n) : ℝ)
          ≤ evertseCountBase n d δ ^ (2 * n + 2)
            * (2 * evertseLogFactor n s * evertseCountBase n d δ ^ 8) :=
            mul_le_mul (parametricGridCount_system_le hn he hed hδ hδ1 hp') (by linarith)
              (Nat.cast_nonneg _) (pow_nonneg hZ0 _)
        _ = _ := by rw [show 2 * n + 10 = (2 * n + 2) + 8 by ring, pow_add]; ring
  rw [parametricIntervalCount]
  push_cast
  calc ∑ p ∈ Finset.range n, (parametricGridCount n d p (systemEps e δ)
        (systemAbsBound e n) : ℝ)
        * (parametricChainLength n d s p (systemEps e δ) (systemAbsBound e n) : ℝ)
      ≤ ∑ _p ∈ Finset.range n,
          2 * evertseLogFactor n s * evertseCountBase n d δ ^ (2 * n + 10) :=
        Finset.sum_le_sum hstep
    _ = _ := by simp

/-- The factor `1 + log ρ / log (1 + δ / (2 n))` of the count, with Evertse's Roth lemma, is at
most `Z ^ 2 (1 + log ℓ)`. -/
theorem one_add_log_parametricRatio_div_le (b : ℕ → ℝ) (hn : 1 ≤ n) (he : 1 ≤ e) (hed : e ≤ d)
    (hs : 1 ≤ s) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 + Real.log (parametricRatio (RothParams.evertse b) n d s (systemEps e δ)
        (systemAbsBound e n)) / Real.log (1 + δ / (2 * n))
      ≤ evertseCountBase n d δ ^ 2 * (1 + Real.log (evertseLogFactor n s)) := by
  have hd : 1 ≤ d := he.trans hed
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  set Z := evertseCountBase n d δ with hZdef
  set ℓ := evertseLogFactor n s with hℓdef
  have hZ : 2048 ≤ Z := const_le_evertseCountBase hn hd hδ hδ1
  have hZ0 : 0 < Z := by linarith
  have hℓ1 : 1 ≤ ℓ := one_le_evertseLogFactor n hs
  have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  have hρ := parametricRatio_evertse_system_le b hn he hed hs hδ hδ1
  have hρ1 := one_le_parametricRatio (RothParams.evertse b) d s (by omega : 0 < n) hε
    (systemAbsBound_nonneg e n)
  set ρ := parametricRatio (RothParams.evertse b) n d s (systemEps e δ)
    (systemAbsBound e n) with hρdef
  have hlogρ0 : 0 ≤ Real.log ρ := Real.log_nonneg hρ1
  have hlogρ : Real.log ρ ≤ 14 * Z + Real.log ℓ := by
    have h := Real.log_le_log (by linarith) hρ
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow] at h
    have hlogZ := Real.log_le_sub_one_of_pos hZ0
    have h32 : Real.log 32 ≤ 32 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
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
  have hmono := monomial_le' hn hd (c := 64) (by norm_num) (by norm_num) (a := 1) (k := 0)
    (by norm_num) (by norm_num)
  simp only [pow_one, pow_zero, mul_one] at hmono
  have h64 := div_le_evertseCountBase hδ hmono
  -- `1 / (x / 2) = 4 n / δ ≤ Z / 16`
  have hinv : 1 / (x / 2) ≤ Z / 16 := by
    rw [hx, show (1 : ℝ) / (δ / (2 * n) / 2) = 64 * n / δ / 16 by field_simp; ring]
    gcongr
  have hdiv : Real.log ρ / Real.log (1 + x) ≤ Z / 16 * (14 * Z + Real.log ℓ) := by
    calc Real.log ρ / Real.log (1 + x) ≤ Real.log ρ / (x / 2) :=
          div_le_div_of_nonneg_left hlogρ0 (by positivity) hL
      _ = Real.log ρ * (1 / (x / 2)) := by ring
      _ ≤ (14 * Z + Real.log ℓ) * (Z / 16) :=
          mul_le_mul hlogρ hinv (by positivity) (by positivity)
      _ = _ := by ring
  have hZ1 : 1 ≤ Z := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hZ1 hlogℓ, mul_le_mul_of_nonneg_left hZ1 hZ0.le]

/-- **The number of subspaces for the large solutions of a system, with Evertse's Roth lemma, in
closed form** (Q1.6, Q1.7, Q1.8a–c): Q0.3's `systemLargeCount` is at most
`Z ^ (2 n + 14) ℓ (1 + log ℓ)` with `Z = 2 ^ (n + 11) n ^ 6 d / δ` and
`ℓ = 1 + log (2 ^ (n + 1) (r e) ^ n)`: polynomial in `δ⁻¹`, singly exponential in `n`, and
`ℓ log ℓ` with `ℓ ≍ n log (r e)` in the number `r` of distinct forms. Here `n` is the number of
variables, `d = [E : ℚ]` and `e = [E : K]`. -/
theorem systemLargeCount_evertse_le (b : ℕ → ℝ) {r : ℕ} (hn : 1 ≤ n) (he : 1 ≤ e)
    (hed : e ≤ d) (hr : 1 ≤ r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    systemLargeCount (RothParams.evertse b) n d e r δ
      ≤ evertseCountBase n d δ ^ (2 * n + 14) * (evertseLogFactor n (r * e)
        * (1 + Real.log (evertseLogFactor n (r * e)))) := by
  have hd : 1 ≤ d := he.trans hed
  have hs : 1 ≤ r * e := Nat.mul_le_mul hr he
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  set Z := evertseCountBase n d δ with hZdef
  set ℓ := evertseLogFactor n (r * e) with hℓdef
  have hZ : 2048 ≤ Z := const_le_evertseCountBase hn hd hδ hδ1
  have hZ1 : 1 ≤ Z := le_trans (by norm_num) hZ
  have hnZ : (n : ℝ) ≤ Z := le_evertseCountBase_self hn hd hδ hδ1
  have h4n : 4 * (n : ℝ) ≤ Z := by
    have : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
    have := mul_two_pow_le_evertseCountBase hn hd hδ hδ1
    linarith
  have hℓ1 : 1 ≤ ℓ := one_le_evertseLogFactor n hs
  have hP1 : 1 ≤ ℓ * (1 + Real.log ℓ) := by
    have := Real.log_nonneg hℓ1
    nlinarith
  have hS := parametricSubspaceCount_system_le (s := r * e) hn he hed hδ hδ1
  have hI := parametricIntervalCount_system_le hn he hed hs hδ hδ1
  have hW := one_add_log_parametricRatio_div_le b hn he hed hs hδ hδ1
  have hρ1 := one_le_parametricRatio (RothParams.evertse b) d (r * e) (by omega : 0 < n) hε
    (systemAbsBound_nonneg e n)
  have hW0 : 0 ≤ 1 + Real.log (parametricRatio (RothParams.evertse b) n d (r * e)
      (systemEps e δ) (systemAbsBound e n)) / Real.log (1 + δ / (2 * n)) := by
    have : 0 < Real.log (1 + δ / (2 * n)) :=
      Real.log_pos (by have : (0 : ℝ) < δ / (2 * n) := by positivity
                       linarith)
    have := Real.log_nonneg hρ1
    positivity
  set E := 2 * n + 2 with hE
  set P := ℓ * (1 + Real.log ℓ) with hP
  have hZE1 : 1 ≤ Z ^ E := one_le_pow₀ hZ1
  have hZE0 : 0 ≤ Z ^ E := by positivity
  have hZ2 : 2 * Z ≤ Z ^ 2 := by nlinarith
  have hZZ : Z ≤ Z ^ 2 := by nlinarith
  have hP0 : 0 ≤ P := by linarith
  have h1 : 1 + n * Z ^ E ≤ Z ^ (E + 2) := by
    have hA : 1 ≤ Z * Z ^ E := by nlinarith
    have hB : n * Z ^ E ≤ Z * Z ^ E := mul_le_mul_of_nonneg_right hnZ hZE0
    have hC : 2 * Z * Z ^ E ≤ Z ^ 2 * Z ^ E := mul_le_mul_of_nonneg_right hZ2 hZE0
    rw [pow_add Z E 2]
    nlinarith
  have hZ10 : 2 * Z ^ (E + 2) ≤ Z ^ (E + 12) := by
    have h2 : (2 : ℝ) ≤ Z ^ 10 :=
      le_trans (by norm_num) (hZ.trans (le_self_pow₀ hZ1 (by norm_num)))
    rw [show E + 12 = E + 2 + 10 by omega, pow_add Z (E + 2) 10]
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ Z ^ (E + 2))]
  have h3 : Z / 2 * P * Z ^ (E + 10) ≤ Z ^ (E + 12) * P / 2 := by
    rw [show E + 12 = E + 10 + 2 by omega, pow_add Z (E + 10) 2]
    have hZE10 : 0 ≤ Z ^ (E + 10) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hZZ (mul_nonneg hP0 hZE10)]
  rw [systemLargeCount]
  calc (parametricSubspaceCount n d (r * e) (systemEps e δ) (systemAbsBound e n) : ℝ)
        + (parametricIntervalCount n d (r * e) (systemEps e δ) (systemAbsBound e n) : ℝ)
          * (1 + Real.log (parametricRatio (RothParams.evertse b) n d (r * e)
            (systemEps e δ) (systemAbsBound e n)) / Real.log (1 + δ / (2 * n)))
      ≤ (1 + n * Z ^ E) + n * (2 * ℓ * Z ^ (2 * n + 10)) * (Z ^ 2 * (1 + Real.log ℓ)) := by
        gcongr
    _ = (1 + n * Z ^ E) + 2 * n * P * Z ^ (E + 10) := by rw [hE, hP]; ring
    _ ≤ Z ^ (E + 2) + Z / 2 * P * Z ^ (E + 10) := by
        have h2 : 2 * (n : ℝ) ≤ Z / 2 := by linarith
        gcongr
    _ ≤ Z ^ (E + 12) * P := by
        nlinarith [mul_le_mul_of_nonneg_left hP1 (by positivity : (0 : ℝ) ≤ Z ^ (E + 12))]
    _ = Z ^ (2 * n + 14) * P := by rw [hE]

end Count

/-! ### The quantitative Subspace Theorem for a system -/

section System

variable {K : Type*} [Field K] [NumberField K] {ι : Type u} [Fintype ι]

open scoped Classical in
/-- **The quantitative Subspace Theorem for a system, with Evertse's Roth lemma, in closed form**
(Q1.6, Q1.8a–c): as `NumberField.exists_finset_submodule_of_isNormalizedSystem_evertse`, with the
count of the large solutions bounded by `Z ^ (2 n + 14) ℓ (1 + log ℓ)`, where
`Z = 2 ^ (n + 11) n ^ 6 [E : ℚ] / δ`, `ℓ = 1 + log (2 ^ (n + 1) (R [E : K]) ^ n)` and
`n = #ι`. -/
theorem exists_finset_submodule_of_isNormalizedSystem_evertse_le {E : Type*} [Field E]
    [NumberField E] [Algebra K E] [IsGalois K E]
    (H : ∀ m : ℕ, MultiprojectiveHeight (K := E) (Prod.fst : Fin m × Fin 2 → Fin m))
    (hCM : ∀ (m : ℕ) (𝔭 : Ideal (MvPolynomial (Fin m × Fin 2) E)) [𝔭.IsPrime],
      IsUnmixedRing (Localization.AtPrime 𝔭))
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
        evertseCountBase (Fintype.card ι) (finrank ℚ E) δ
            ^ (2 * Fintype.card ι + 14) *
          (evertseLogFactor (Fintype.card ι) (R * finrank K E) *
            (1 + Real.log (evertseLogFactor (Fintype.card ι) (R * finrank K E)))) ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∀ x ∈ systemSet S w L C c, ∃ U ∈ T, x ∈ U := by
  obtain ⟨T, hT, hTtop, hTmem⟩ :=
    exists_finset_submodule_of_isNormalizedSystem_evertse H hCM S w hwInf hwFin hN
  refine ⟨T, hT.trans ?_, hTtop, hTmem⟩
  have hn : 1 ≤ Fintype.card ι := by have := hN.two_le_card; omega
  have he : 1 ≤ finrank K E := finrank_pos
  have hed : finrank K E ≤ finrank ℚ E := by
    rw [← Module.finrank_mul_finrank ℚ K E]
    exact Nat.le_mul_of_pos_left _ finrank_pos
  exact add_le_add_right (systemLargeCount_evertse_le _ hn he hed hN.one_le_formBound
    hN.delta_pos hN.delta_le_one) _

end System

end NumberField
