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
contain the large solutions of a normalized system by `systemLargeCount`: the number of grid
systems, times the number of subspaces and intervals of Layer 6.1, times
`1 + log ρ / log (1 + δ / (2 n))`. This file bounds it in closed form when the chain runs with
Evertse's Roth lemma (`NumberField.RothParams.evertse`, Q1.5), and compares the result with
Evertse 1996.

## Main results

* `NumberField.systemLargeCount_evertse_le`:
  `systemLargeCount ≤ Z ^ (t n + 2 ^ n (2 d + e u) + 13)` with
  `Z = 2 ^ (n + 12) n ^ 6 t ^ 2 d ^ 2 / δ` (`NumberField.evertseCountBase`), where `n` is the
  number of variables, `d = [E : ℚ]`, `e = [E : K]`, `t` the number of places in `S` and `u` the
  number of finite ones.
* `NumberField.exists_finset_submodule_of_isNormalizedSystem_evertse_le`: Q0.3's count with that
  bound for the large solutions.
* The pieces, each at most a power of `Z`: the grid systems (`NumberField.systemGridCount_le`,
  `Z ^ (t n)`), the grids in `⋀^p` (`NumberField.parametricGridCount_system_le`,
  `Z ^ (2 ^ n d)`), the chain lengths (`NumberField.parametricChainLength_step_le`, `Z ^ 10`)
  and the ratio (`NumberField.parametricRatio_evertse_system_le`, `Z ^ 16`), so that
  `1 + log ρ / log (1 + δ / (2 n)) ≤ 2 Z ^ 2`
  (`NumberField.one_add_log_parametricRatio_div_le`).

## Comparison with Evertse 1996

Evertse's Theorem (i) bounds the number of subspaces for the solutions with `H(x) ≥ H` by
`(2 ^ (60 n ^ 2) δ ^ (-7 n)) ^ s log 4D log log 4D`, with `s = |S|` and `D` a bound for the
degrees of the coefficients over `K`. Here:

* **`δ`: both counts are polynomial in `δ⁻¹`.** This is what Evertse's Roth lemma buys. With
  Bombieri–Gubler's, `log ρ` is `2 ^ m log (4 / η)` with `m` of order
  `n ^ 2 (A + 1) ^ 2 / ε ^ 2`, so the count is exponential in a power of `δ⁻¹`. The exponents
  differ: `t n + 2 ^ n (2 d + e u)` against `7 n s`.
* **`n`: the count is doubly exponential in `n`, Evertse's singly.** The exponent carries
  `2 ^ n d` where Evertse's carries `60 n ^ 2 s`.
* **The degree: `d = [E : ℚ]` enters the exponent**, where Evertse's count has only
  `log 4D log log 4D`; `E` is the Galois extension carrying the forms.

Both gaps come from Layer 6.1's grids, not from the Roth lemma: Layer 6.1 covers the exponents
of a domain in `⋀^p` by a grid in each of the `[E : ℚ]` infinite places and the `binom(n, p)`
coordinates, so its count is `(2 m + 1) ^ ([E : ℚ] binom(n, p))`. The thresholds and the
domains also differ: Q0.3 counts the solutions above the threshold `X₀` of Layer 6.1 and handles
the others by Layers 9.3 and 9.4, and its `δ` is the weight of a normalized system.

This is Layer Q1.6 of the `QuantitativeSubspace` roadmap.
-/

@[expose] public section

open Finset Module MvPolynomial Height IsDedekindDomain

universe u

namespace NumberField

/-- **The base of the closed-form count**, `Z = 2 ^ (n + 12) n ^ 6 t ^ 2 d ^ 2 / δ`. -/
noncomputable def evertseCountBase (n d t : ℕ) (δ : ℝ) : ℝ :=
  2 ^ (n + 12) * (n : ℝ) ^ 6 * (t : ℝ) ^ 2 * (d : ℝ) ^ 2 / δ

section Base

variable {n d t : ℕ} {δ : ℝ}

/-- Any `x / δ` with `x ≤ 2 ^ (n + 12) n ^ 6 t ^ 2 d ^ 2` is at most `Z`. -/
theorem div_le_evertseCountBase (hδ : 0 < δ) {x : ℝ}
    (hx : x ≤ 2 ^ (n + 12) * (n : ℝ) ^ 6 * (t : ℝ) ^ 2 * (d : ℝ) ^ 2) :
    x / δ ≤ evertseCountBase n d t δ := by
  rw [evertseCountBase]; gcongr

/-- Any `x ≤ 2 ^ (n + 12) n ^ 6 t ^ 2 d ^ 2` is at most `Z`, as `δ ≤ 1`. -/
theorem le_evertseCountBase (hδ : 0 < δ) (hδ1 : δ ≤ 1) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 2 ^ (n + 12) * (n : ℝ) ^ 6 * (t : ℝ) ^ 2 * (d : ℝ) ^ 2) :
    x ≤ evertseCountBase n d t δ :=
  (le_div_self hx0 hδ hδ1).trans (div_le_evertseCountBase hδ hx)

/-- The monomials that the count is made of: `2 ^ (n + 12) n ^ 6 t ^ 2 d ^ 2` bounds
`c 2 ^ n n ^ a t ^ b d ^ k` for `c ≤ 4096`, `a ≤ 6`, `b ≤ 2` and `k ≤ 2`. -/
theorem monomial_le (hn : 1 ≤ n) (ht : 1 ≤ t) (hd : 1 ≤ d) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c ≤ 4096) {a b k : ℕ} (ha : a ≤ 6) (hb : b ≤ 2) (hk : k ≤ 2) :
    c * 2 ^ n * (n : ℝ) ^ a * (t : ℝ) ^ b * (d : ℝ) ^ k
      ≤ 2 ^ (n + 12) * (n : ℝ) ^ 6 * (t : ℝ) ^ 2 * (d : ℝ) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hc2 : 0 ≤ c * 2 ^ n := mul_nonneg hc0 (by positivity)
  rw [pow_add]
  calc c * 2 ^ n * (n : ℝ) ^ a * (t : ℝ) ^ b * (d : ℝ) ^ k
      ≤ 2 ^ 12 * 2 ^ n * (n : ℝ) ^ 6 * (t : ℝ) ^ 2 * (d : ℝ) ^ 2 := by
        gcongr
        all_goals first | assumption | linarith [show (2 : ℝ) ^ 12 = 4096 by norm_num]
    _ = _ := by ring

theorem one_le_evertseCountBase (hn : 1 ≤ n) (ht : 1 ≤ t) (hd : 1 ≤ d) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) : 1 ≤ evertseCountBase n d t δ := by
  refine le_evertseCountBase hδ hδ1 zero_le_one ?_
  have := monomial_le hn ht hd (c := 1) zero_le_one (by norm_num) (a := 0) (b := 0) (k := 0)
    (by norm_num) (by norm_num) (by norm_num)
  have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  simp only [pow_zero, mul_one, one_mul] at this
  linarith

/-- `c n ^ a t ^ b d ^ k ≤ 2 ^ (n + 12) n ^ 6 t ^ 2 d ^ 2` without the factor `2 ^ n`. -/
theorem monomial_le' (hn : 1 ≤ n) (ht : 1 ≤ t) (hd : 1 ≤ d) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c ≤ 4096) {a b k : ℕ} (ha : a ≤ 6) (hb : b ≤ 2) (hk : k ≤ 2) :
    c * (n : ℝ) ^ a * (t : ℝ) ^ b * (d : ℝ) ^ k
      ≤ 2 ^ (n + 12) * (n : ℝ) ^ 6 * (t : ℝ) ^ 2 * (d : ℝ) ^ 2 := by
  refine le_trans ?_ (monomial_le hn ht hd hc0 hc ha hb hk)
  have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  have : 0 ≤ c * (n : ℝ) ^ a * (t : ℝ) ^ b * (d : ℝ) ^ k := by positivity
  nlinarith

theorem mul_two_pow_le_evertseCountBase (hn : 1 ≤ n) (ht : 1 ≤ t) (hd : 1 ≤ d) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) : 4096 * 2 ^ n ≤ evertseCountBase n d t δ := by
  refine le_evertseCountBase hδ hδ1 (by positivity) ?_
  have := monomial_le hn ht hd (c := 4096) (by norm_num) le_rfl (a := 0) (b := 0) (k := 0)
    (by norm_num) (by norm_num) (by norm_num)
  simpa using this

theorem two_pow_le_evertseCountBase (hn : 1 ≤ n) (ht : 1 ≤ t) (hd : 1 ≤ d) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) : (2 : ℝ) ^ n ≤ evertseCountBase n d t δ := by
  have := mul_two_pow_le_evertseCountBase hn ht hd hδ hδ1
  have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  linarith

theorem const_le_evertseCountBase (hn : 1 ≤ n) (ht : 1 ≤ t) (hd : 1 ≤ d) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) : 4096 ≤ evertseCountBase n d t δ := by
  have := mul_two_pow_le_evertseCountBase hn ht hd hδ hδ1
  have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  nlinarith

end Base

/-! ### The pieces of the parametric Subspace Theorem -/

section Parametric

variable {N d p : ℕ} {ε A : ℝ}

/-- The box of grids: `Y / γ = 4 N ^ 2 binom(N, p) (d + N (N + 2) (A + 1)) / ε`. -/
theorem parametricBox_arg_eq (hN : 1 ≤ N) (hd : 1 ≤ d) (hp : p ≤ N) (hε : 0 < ε) :
    (1 + parametricMinimaExp N d A * N + 2 * parametricMinimaExp N d A) / parametricMesh N d p ε
      = 4 * (N : ℝ) ^ 2 * N.choose p * (d + N * (N + 2) * (A + 1)) / ε := by
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

/-- The box of grids is at most `4 N ^ 2 binom(N, p) (d + N (N + 2) (A + 1)) / ε + 1`. -/
theorem parametricBox_le (hN : 1 ≤ N) (hd : 1 ≤ d) (hp : p ≤ N) (hε : 0 < ε) :
    (parametricBox N d p ε A : ℝ)
      ≤ 4 * (N : ℝ) ^ 2 * N.choose p * (d + N * (N + 2) * (A + 1)) / ε + 1 := by
  rw [parametricBox, ← parametricBox_arg_eq hN hd hp hε]
  exact (Int.ceil_lt_add_one _).le

/-- The number of grids in `⋀^p`:
`(8 N ^ 2 binom(N, p) (d + N (N + 2) (A + 1)) / ε + 3) ^ (r binom(N, p))`. -/
theorem parametricGridCount_le (r : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d) (hp : p ≤ N) (hε : 0 < ε)
    (hA : 0 ≤ A) : (parametricGridCount N d r p ε A : ℝ)
      ≤ (8 * (N : ℝ) ^ 2 * N.choose p * (d + N * (N + 2) * (A + 1)) / ε + 3)
        ^ (r * N.choose p) := by
  have h0 := parametricBox_nonneg hN hd hp hε hA
  have hb := parametricBox_le (A := A) hN hd hp hε
  have hcast : (((2 * parametricBox N d p ε A + 1).toNat : ℕ) : ℝ)
      = 2 * (parametricBox N d p ε A : ℝ) + 1 := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
  rw [parametricGridCount, Nat.cast_pow, hcast]
  have : (0 : ℝ) ≤ parametricBox N d p ε A := by exact_mod_cast h0
  refine pow_le_pow_left₀ (by positivity) ?_ _
  have h8 : 8 * (N : ℝ) ^ 2 * N.choose p * (d + N * (N + 2) * (A + 1)) / ε
      = 2 * (4 * (N : ℝ) ^ 2 * N.choose p * (d + N * (N + 2) * (A + 1)) / ε) := by ring
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
  have hγb : parametricMesh N d p ε * parametricBox N d p ε A
      ≤ (d + N * (N + 2) * (A + 1)) / d + parametricMesh N d p ε := by
    calc _ ≤ parametricMesh N d p ε
          * (4 * (N : ℝ) ^ 2 * N.choose p * (d + N * (N + 2) * (A + 1)) / ε + 1) :=
          mul_le_mul_of_nonneg_left hb hγ.le
      _ = _ := by rw [parametricMesh, parametricDelta]; field_simp; ring
  have hγd : parametricMesh N d p ε * (N.choose p * d) ≤ ε := by
    rw [parametricMesh, parametricDelta]
    have : ε / (2 * (N : ℝ) ^ 2) / (2 * ((d : ℝ) * N.choose p)) * (N.choose p * d)
        = ε / (4 * (N : ℝ) ^ 2) := by field_simp; ring
    rw [this, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ N ^ 2 := one_le_pow₀ (by exact_mod_cast hN)
    nlinarith
  rw [parametricWedgeAbsWeight]
  calc (N.choose p : ℝ) * A + parametricMesh N d p ε * parametricBox N d p ε A * (N.choose p * d)
      ≤ N.choose p * A + ((d + N * (N + 2) * (A + 1)) / d + parametricMesh N d p ε)
          * (N.choose p * d) := by gcongr
    _ = N.choose p * (A + d + N * (N + 2) * (A + 1))
          + parametricMesh N d p ε * (N.choose p * d) := by field_simp; ring
    _ ≤ _ := by linarith

end Parametric

/-! ### The parameters of a system -/

section System

variable {n d e t : ℕ} {δ : ℝ}

theorem systemAbsBound_nonneg (e n t : ℕ) : 0 ≤ systemAbsBound e n t := by
  rw [systemAbsBound]; positivity

theorem systemAbsBound_add_one_le (hn : 1 ≤ n) (ht : 1 ≤ t) (he : 1 ≤ e) :
    systemAbsBound e n t + 1 ≤ 5 * e * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hx : (1 : ℝ) ≤ n * t := one_le_mul_of_one_le_of_one_le hn1 ht1
  rw [systemAbsBound, systemClamp]
  push_cast
  have h : (e : ℝ) * (t * n * (2 * n * t + 2)) + 1 = 2 * e * (n * t) ^ 2 + 2 * e * (n * t) + 1 := by
    ring
  have h' : 5 * (e : ℝ) * n ^ 2 * t ^ 2 = 5 * e * (n * t) ^ 2 := by ring
  rw [h, h']
  generalize (n : ℝ) * t = x at *
  nlinarith [mul_le_mul_of_nonneg_left hx (by linarith : (0 : ℝ) ≤ e)]

/-- `d + n (n + 2) (A + 1) ≤ 16 d n ^ 4 t ^ 2` for the absolute weight `A` of the system. -/
theorem systemCoeff_le (hn : 1 ≤ n) (ht : 1 ≤ t) (he : 1 ≤ e) (hed : e ≤ d) :
    (d : ℝ) + n * (n + 2) * (systemAbsBound e n t + 1) ≤ 16 * d * (n : ℝ) ^ 4 * (t : ℝ) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hed' : (e : ℝ) ≤ d := by exact_mod_cast hed
  have hA := systemAbsBound_add_one_le hn ht he
  have hA0 : 0 ≤ systemAbsBound e n t + 1 := by linarith [systemAbsBound_nonneg e n t]
  have hP : (1 : ℝ) ≤ (n : ℝ) ^ 4 * (t : ℝ) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn1) (one_le_pow₀ (by exact_mod_cast ht))
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc (d : ℝ) + n * (n + 2) * (systemAbsBound e n t + 1)
      ≤ d * ((n : ℝ) ^ 4 * (t : ℝ) ^ 2) + 3 * n ^ 2 * (5 * e * (n : ℝ) ^ 2 * (t : ℝ) ^ 2) := by
        have hnn : (n : ℝ) * (n + 2) ≤ 3 * n ^ 2 := by nlinarith
        exact add_le_add (le_mul_of_one_le_right hd0 hP) (mul_le_mul hnn hA hA0 (by positivity))
    _ ≤ d * ((n : ℝ) ^ 4 * (t : ℝ) ^ 2) + 3 * n ^ 2 * (5 * d * (n : ℝ) ^ 2 * (t : ℝ) ^ 2) := by
        gcongr
    _ = _ := by ring

/-- The base of the number of grids in `⋀^p` for a system is at most `Z`. -/
theorem systemGridBase_le (hn : 1 ≤ n) (ht : 1 ≤ t) (he : 1 ≤ e) (hed : e ≤ d) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (p : ℕ) :
    8 * (n : ℝ) ^ 2 * n.choose p * (d + n * (n + 2) * (systemAbsBound e n t + 1))
        / systemEps e δ + 3 ≤ evertseCountBase n d t δ := by
  have hd : 1 ≤ d := he.trans hed
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hK := systemCoeff_le hn ht he hed
  have hC : (n.choose p : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n p
  have hM : (1 : ℝ) ≤ 2 ^ n * (n : ℝ) ^ 6 * (t : ℝ) ^ 2 * d := by
    have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 6 := one_le_pow₀ hn1
    have h3 : (1 : ℝ) ≤ (t : ℝ) ^ 2 := one_le_pow₀ ht1
    have h12 : (1 : ℝ) ≤ 2 ^ n * (n : ℝ) ^ 6 := one_le_mul_of_one_le_of_one_le h1 h2
    have h123 : (1 : ℝ) ≤ 2 ^ n * (n : ℝ) ^ 6 * (t : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le h12 h3
    exact one_le_mul_of_one_le_of_one_le h123 hd1
  have hmono := monomial_le hn ht hd (c := 515) (by norm_num) (by norm_num) (a := 6) (b := 2)
    (k := 1) le_rfl le_rfl (by norm_num)
  rw [pow_one] at hmono
  have hK0 : 0 ≤ (d : ℝ) + n * (n + 2) * (systemAbsBound e n t + 1) := by
    have := systemAbsBound_nonneg e n t
    positivity
  set K₀ := (d : ℝ) + n * (n + 2) * (systemAbsBound e n t + 1)
  calc 8 * (n : ℝ) ^ 2 * n.choose p * K₀ / systemEps e δ + 3
      = 32 * (n : ℝ) ^ 2 * n.choose p * K₀ / (e * δ) + 3 := by
        rw [systemEps]; field_simp; ring
    _ ≤ 32 * (n : ℝ) ^ 2 * n.choose p * K₀ / δ + 3 / δ := by
        gcongr
        · nlinarith
        · exact le_div_self (by norm_num) hδ hδ1
    _ ≤ 32 * (n : ℝ) ^ 2 * 2 ^ n * (16 * d * (n : ℝ) ^ 4 * (t : ℝ) ^ 2) / δ + 3 / δ := by
        gcongr
    _ = (512 * (2 ^ n * (n : ℝ) ^ 6 * (t : ℝ) ^ 2 * d) + 3) / δ := by ring
    _ ≤ _ := div_le_evertseCountBase hδ (by nlinarith)

/-- The number of grids of the system is at most `Z ^ (t n)`. -/
theorem systemGridCount_le (hn : 1 ≤ n) (ht : 1 ≤ t) (hd : 1 ≤ d) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (systemGridCount n t δ : ℝ) ≤ evertseCountBase n d t δ ^ (t * n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hx : 1 ≤ 4 * (n : ℝ) * t / δ := by
    rw [le_div_iff₀ hδ]; nlinarith
  have hm := Nat.ceil_lt_add_one (by linarith : 0 ≤ 4 * (n : ℝ) * t / δ)
  have hm1 : (1 : ℝ) ≤ systemGridDen n t δ := by
    exact_mod_cast Nat.one_le_ceil_iff.2 (by linarith)
  have hmono := monomial_le' hn ht hd (c := 40) (by norm_num) (by norm_num) (a := 2) (b := 2)
    (k := 0) (by norm_num) le_rfl (by norm_num)
  rw [pow_zero, mul_one] at hmono
  rw [systemGridCount, systemClamp]
  push_cast
  refine pow_le_pow_left₀ (by positivity) ?_ _
  simp only [systemGridDen] at hm1 ⊢
  generalize (⌈4 * (n : ℝ) * t / δ⌉₊ : ℝ) = m at *
  have h8 : m ≤ 8 * n * t / δ := by
    have : 8 * (n : ℝ) * t / δ = 2 * (4 * n * t / δ) := by ring
    linarith
  have hnt : (1 : ℝ) ≤ n * t := one_le_mul_of_one_le_of_one_le hn1 ht1
  have hntm := mul_le_mul_of_nonneg_right hnt (by linarith : (0 : ℝ) ≤ m)
  calc 2 * (n : ℝ) * t * m + 2 * m + 1 ≤ 5 * n * t * m := by nlinarith
    _ ≤ 5 * n * t * (8 * n * t / δ) := by gcongr
    _ = 40 * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 / δ := by ring
    _ ≤ _ := div_le_evertseCountBase hδ hmono

end System

/-! ### One step of Layer 6.1 for a system -/

section Step

variable {n d e t u : ℕ} {δ : ℝ}

theorem cast_choose_sub_one_add_one {p : ℕ} (hp : p ≤ n) :
    ((n.choose p - 1 : ℕ) : ℝ) + 1 = n.choose p := by
  have : 1 ≤ n.choose p := Nat.choose_pos hp
  rw [Nat.cast_sub this]; push_cast; ring

/-- `X_p ≤ Z ^ 4`: the bound for `η⁻¹` in `⋀^p`. -/
theorem evertseEtaInvBound_step_le (hn : 1 ≤ n) (ht : 1 ≤ t) (he : 1 ≤ e) (hed : e ≤ d)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {p : ℕ} (hp : p ≤ n) :
    evertseEtaInvBound (n.choose p - 1) (parametricDelta n (systemEps e δ))
        (parametricWedgeAbsWeight n d p (systemEps e δ) (systemAbsBound e n t))
      ≤ evertseCountBase n d t δ ^ 4 := by
  have hd : 1 ≤ d := he.trans hed
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hed' : (e : ℝ) ≤ d := by exact_mod_cast hed
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  have hC1 : (1 : ℝ) ≤ n.choose p := by exact_mod_cast Nat.choose_pos hp
  have hC2 : (n.choose p : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n p
  have hAp := parametricWedgeAbsWeight_le (A := systemAbsBound e n t) hn hd hp hε
  have hK := systemCoeff_le hn ht he hed
  have hA := systemAbsBound_add_one_le hn ht he
  have hn24 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := pow_le_pow_right₀ hn1 (by norm_num)
  have hW1 : (1 : ℝ) ≤ d * (n : ℝ) ^ 4 * (t : ℝ) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hd1 (one_le_pow₀ hn1))
      (one_le_pow₀ ht1)
  have hAW : systemAbsBound e n t ≤ 5 * (d * (n : ℝ) ^ 4 * (t : ℝ) ^ 2) := by
    have : (e : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 ≤ d * (n : ℝ) ^ 4 * (t : ℝ) ^ 2 := by gcongr
    linarith
  have hεW : systemEps e δ ≤ d * (n : ℝ) ^ 4 * (t : ℝ) ^ 2 := by
    rw [systemEps]
    have : (e : ℝ) * δ / 4 ≤ e := by nlinarith
    have : (d : ℝ) ≤ d * (n : ℝ) ^ 4 * (t : ℝ) ^ 2 := by
      have := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 4)
        (one_le_pow₀ ht1 : (1 : ℝ) ≤ (t : ℝ) ^ 2)
      nlinarith
    linarith
  set W := d * (n : ℝ) ^ 4 * (t : ℝ) ^ 2 with hW
  set C := (n.choose p : ℝ) with hC
  set Ap := parametricWedgeAbsWeight n d p (systemEps e δ) (systemAbsBound e n t)
  have hAp1 : Ap + 1 ≤ 23 * C * W := by nlinarith
  have hAp0 : 0 ≤ Ap := parametricWedgeAbsWeight_nonneg n d p hε.le (systemAbsBound_nonneg e n t)
  have hQ : 1 ≤ C ^ 3 * ((n : ℝ) ^ 6 * (t : ℝ) ^ 2 * d / δ) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 6 * (t : ℝ) ^ 2 * d :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn1)
        (one_le_pow₀ ht1)) hd1
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 6 * (t : ℝ) ^ 2 * d / δ := by
      rw [le_div_iff₀ hδ]; linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC1) h2
  have hmono := monomial_le' hn ht hd (c := 1473) (by norm_num) (by norm_num) (a := 6) (b := 2)
    (k := 1) le_rfl le_rfl (by norm_num)
  rw [pow_one] at hmono
  have hZ := div_le_evertseCountBase hδ hmono
  have h2Z := two_pow_le_evertseCountBase hn ht hd hδ hδ1
  rw [evertseEtaInvBound, cast_choose_sub_one_add_one hp, parametricDelta, systemEps]
  calc 1 + 8 * C ^ 2 * (Ap + 1) / (e * δ / 4 / (2 * (n : ℝ) ^ 2))
      = 1 + 64 * (n : ℝ) ^ 2 * C ^ 2 * (Ap + 1) / (e * δ) := by field_simp; ring
    _ ≤ 1 + 64 * (n : ℝ) ^ 2 * C ^ 2 * (23 * C * W) / δ := by
        gcongr
        nlinarith
    _ = 1 + 1472 * (C ^ 3 * ((n : ℝ) ^ 6 * (t : ℝ) ^ 2 * d / δ)) := by rw [hW]; ring
    _ ≤ C ^ 3 * (1473 * (n : ℝ) ^ 6 * (t : ℝ) ^ 2 * d / δ) := by
        have : C ^ 3 * (1473 * (n : ℝ) ^ 6 * (t : ℝ) ^ 2 * d / δ)
            = 1473 * (C ^ 3 * ((n : ℝ) ^ 6 * (t : ℝ) ^ 2 * d / δ)) := by ring
        linarith
    _ ≤ evertseCountBase n d t δ ^ 3 * evertseCountBase n d t δ := by
        have hZ0 : 0 ≤ evertseCountBase n d t δ :=
          le_trans (by norm_num) (const_le_evertseCountBase hn ht hd hδ hδ1)
        gcongr
        exact hC2.trans h2Z
    _ = _ := by ring

theorem evertseCountBase_nonneg (hn : 1 ≤ n) (ht : 1 ≤ t) (hd : 1 ≤ d) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) : 0 ≤ evertseCountBase n d t δ :=
  le_trans (by norm_num) (const_le_evertseCountBase hn ht hd hδ hδ1)

/-- `T_p ≤ Z ^ 10`: the bound for the number of blocks in `⋀^p`, with `s = d + e u`. -/
theorem evertseChainBound_step_le (hn : 1 ≤ n) (ht : 1 ≤ t) (he : 1 ≤ e) (hed : e ≤ d)
    (hu : u ≤ t) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {p : ℕ} (hp : p ≤ n) :
    evertseChainBound (n.choose p - 1) (d + e * u) (parametricDelta n (systemEps e δ))
        (parametricWedgeAbsWeight n d p (systemEps e δ) (systemAbsBound e n t))
      ≤ evertseCountBase n d t δ ^ 10 := by
  have hd : 1 ≤ d := he.trans hed
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  have hX := evertseEtaInvBound_step_le hn ht he hed hδ hδ1 hp
  have hX1 := one_le_evertseEtaInvBound (n.choose p - 1) (parametricDelta_pos hn hε)
    (parametricWedgeAbsWeight_nonneg n d p hε.le (systemAbsBound_nonneg e n t))
  have hZ := const_le_evertseCountBase hn ht hd hδ hδ1
  have h2Z := two_pow_le_evertseCountBase hn ht hd hδ hδ1
  have hC1 : (1 : ℝ) ≤ n.choose p := by exact_mod_cast Nat.choose_pos hp
  have hC2 : (n.choose p : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n p
  have hs1 : (1 : ℝ) ≤ ((d + e * u : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ d + e * u)
  have hs : ((d + e * u : ℕ) : ℝ) ≤ 2 * t * d := by
    have hn1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have : e * u ≤ d * t := Nat.mul_le_mul hed hu
    have : ((e * u : ℕ) : ℝ) ≤ d * t := by exact_mod_cast this
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    push_cast at this ⊢
    nlinarith
  have hpos : 0 < 2 * (n.choose p : ℝ) * ((d + e * u : ℕ) : ℝ) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hpos
  have hlog0 : 0 ≤ Real.log (2 * (n.choose p : ℝ) * ((d + e * u : ℕ) : ℝ)) :=
    Real.log_nonneg (by nlinarith)
  have hmono := monomial_le hn ht hd (c := 4) (by norm_num) (by norm_num) (a := 0) (b := 1)
    (k := 1) (by norm_num) (by norm_num) (by norm_num)
  simp only [pow_zero, mul_one, pow_one] at hmono
  have hL : 1 + Real.log (2 * (n.choose p : ℝ) * ((d + e * u : ℕ) : ℝ))
      ≤ evertseCountBase n d t δ := by
    refine le_evertseCountBase hδ hδ1 (by linarith) ?_
    calc 1 + Real.log (2 * (n.choose p : ℝ) * ((d + e * u : ℕ) : ℝ))
        ≤ 2 * (n.choose p : ℝ) * ((d + e * u : ℕ) : ℝ) := by linarith
      _ ≤ 2 * 2 ^ n * (2 * t * d) := by gcongr
      _ = 4 * 2 ^ n * t * d := by ring
      _ ≤ _ := hmono
  rw [evertseChainBound, cast_choose_sub_one_add_one hp]
  calc 2 * (1 + Real.log (2 * (n.choose p : ℝ) * ((d + e * u : ℕ) : ℝ)))
        * evertseEtaInvBound (n.choose p - 1) (parametricDelta n (systemEps e δ))
          (parametricWedgeAbsWeight n d p (systemEps e δ) (systemAbsBound e n t)) ^ 2
      ≤ 2 * evertseCountBase n d t δ * (evertseCountBase n d t δ ^ 4) ^ 2 := by
        gcongr
    _ ≤ evertseCountBase n d t δ * evertseCountBase n d t δ
          * (evertseCountBase n d t δ ^ 4) ^ 2 := by
        gcongr
        linarith
    _ = _ := by ring

/-- The number `m_p + 1` of blocks in `⋀^p` is at most `Z ^ 10`. -/
theorem parametricChainLength_step_le (hn : 1 ≤ n) (ht : 1 ≤ t) (he : 1 ≤ e) (hed : e ≤ d)
    (hu : u ≤ t) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {p : ℕ} (hp : p ≤ n) :
    (parametricChainLength n d (d + e * u) p (systemEps e δ) (systemAbsBound e n t) : ℝ) + 1
      ≤ evertseCountBase n d t δ ^ 10 := by
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  exact (subspaceChainLength_add_one_le _ _ (parametricDelta_pos hn hε)
    (parametricWedgeAbsWeight_nonneg n d p hε.le (systemAbsBound_nonneg e n t))).trans
    (evertseChainBound_step_le hn ht he hed hu hδ hδ1 hp)

/-- The ratio `ρ` of the intervals of Layer 6.1 for a system, with Evertse's Roth lemma, is at
most `Z ^ 16`. -/
theorem parametricRatio_evertse_system_le (b : ℕ → ℝ) (hn : 1 ≤ n) (ht : 1 ≤ t) (he : 1 ≤ e)
    (hed : e ≤ d) (hu : u ≤ t) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    parametricRatio (RothParams.evertse b) n d (d + e * u) (systemEps e δ) (systemAbsBound e n t)
      ≤ evertseCountBase n d t δ ^ 16 := by
  have hd : 1 ≤ d := he.trans hed
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  have hZ := const_le_evertseCountBase hn ht hd hδ hδ1
  have hZ0 := evertseCountBase_nonneg hn ht hd hδ hδ1
  have hnZ : (n : ℝ) ≤ evertseCountBase n d t δ := by
    have : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
    exact this.trans (two_pow_le_evertseCountBase hn ht hd hδ hδ1)
  have hstep : ∀ p ∈ Finset.range n,
      parametricStepRatio (RothParams.evertse b) n d (d + e * u) p (systemEps e δ)
        (systemAbsBound e n t) ≤ evertseCountBase n d t δ ^ 15 := fun p hp ↦ by
    have hp' : p ≤ n := (Finset.mem_range.1 hp).le
    refine (parametricStepRatio_evertse_le b d (d + e * u) p (by omega) hε
      (systemAbsBound_nonneg e n t)).trans ?_
    have hT := evertseChainBound_step_le hn ht he hed hu hδ hδ1 hp'
    have hX := evertseEtaInvBound_step_le hn ht he hed hδ hδ1 hp'
    have hT0 := (two_le_evertseChainBound (n.choose p - 1) (d + e * u) (parametricDelta_pos hn hε)
      (parametricWedgeAbsWeight_nonneg n d p hε.le (systemAbsBound_nonneg e n t)))
    calc 16 * evertseChainBound (n.choose p - 1) (d + e * u) (parametricDelta n (systemEps e δ))
          (parametricWedgeAbsWeight n d p (systemEps e δ) (systemAbsBound e n t))
          * evertseEtaInvBound (n.choose p - 1) (parametricDelta n (systemEps e δ))
            (parametricWedgeAbsWeight n d p (systemEps e δ) (systemAbsBound e n t))
        ≤ evertseCountBase n d t δ * evertseCountBase n d t δ ^ 10
          * evertseCountBase n d t δ ^ 4 := by
          have hX1 := one_le_evertseEtaInvBound (n.choose p - 1) (parametricDelta_pos hn hε)
            (parametricWedgeAbsWeight_nonneg n d p hε.le (systemAbsBound_nonneg e n t))
          gcongr
          all_goals linarith
      _ = _ := by ring
  calc parametricRatio (RothParams.evertse b) n d (d + e * u) (systemEps e δ)
        (systemAbsBound e n t)
      ≤ ∑ _p ∈ Finset.range n, evertseCountBase n d t δ ^ 15 := Finset.sum_le_sum hstep
    _ = n * evertseCountBase n d t δ ^ 15 := by simp
    _ ≤ evertseCountBase n d t δ * evertseCountBase n d t δ ^ 15 := by gcongr
    _ = _ := by ring

end Step

/-! ### The count of the large solutions -/

section Count

variable {n d e t u : ℕ} {δ : ℝ}

/-- The number of grids in `⋀^p` for a system is at most `Z ^ (2 ^ n d)`. -/
theorem parametricGridCount_system_le (hn : 1 ≤ n) (ht : 1 ≤ t) (he : 1 ≤ e) (hed : e ≤ d)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {p : ℕ} (hp : p ≤ n) :
    (parametricGridCount n d d p (systemEps e δ) (systemAbsBound e n t) : ℝ)
      ≤ evertseCountBase n d t δ ^ (2 ^ n * d) := by
  have hd : 1 ≤ d := he.trans hed
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  have hA0 := systemAbsBound_nonneg e n t
  have hZ1 : 1 ≤ evertseCountBase n d t δ :=
    le_trans (by norm_num) (const_le_evertseCountBase hn ht hd hδ hδ1)
  have hC : n.choose p ≤ 2 ^ n := Nat.choose_le_two_pow n p
  calc (parametricGridCount n d d p (systemEps e δ) (systemAbsBound e n t) : ℝ)
      ≤ (8 * (n : ℝ) ^ 2 * n.choose p * (d + n * (n + 2) * (systemAbsBound e n t + 1))
          / systemEps e δ + 3) ^ (d * n.choose p) := parametricGridCount_le d hn hd hp hε hA0
    _ ≤ evertseCountBase n d t δ ^ (d * n.choose p) :=
        pow_le_pow_left₀ (by positivity) (systemGridBase_le hn ht he hed hδ hδ1 p) _
    _ ≤ _ := pow_le_pow_right₀ hZ1 (by rw [mul_comm]; exact Nat.mul_le_mul_right d hC)

/-- The number of subspaces of Layer 6.1 for a system is at most
`1 + n Z ^ (2 ^ n (2 d + e u))`. -/
theorem parametricSubspaceCount_system_le (hn : 1 ≤ n) (ht : 1 ≤ t) (he : 1 ≤ e) (hed : e ≤ d)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (parametricSubspaceCount n d d (d + e * u) (systemEps e δ) (systemAbsBound e n t) : ℝ)
      ≤ 1 + n * evertseCountBase n d t δ ^ (2 ^ n * (2 * d + e * u)) := by
  have hd : 1 ≤ d := he.trans hed
  have hZ := const_le_evertseCountBase hn ht hd hδ hδ1
  have hZ1 : 1 ≤ evertseCountBase n d t δ := le_trans (by norm_num) hZ
  have hstep : ∀ p ∈ Finset.range n,
      (parametricGridCount n d d p (systemEps e δ) (systemAbsBound e n t) : ℝ)
        * 2 ^ (n.choose p * (d + e * u))
      ≤ evertseCountBase n d t δ ^ (2 ^ n * (2 * d + e * u)) := fun p hp ↦ by
    have hp' : p ≤ n := (Finset.mem_range.1 hp).le
    have hC : n.choose p ≤ 2 ^ n := Nat.choose_le_two_pow n p
    calc (parametricGridCount n d d p (systemEps e δ) (systemAbsBound e n t) : ℝ)
          * 2 ^ (n.choose p * (d + e * u))
        ≤ evertseCountBase n d t δ ^ (2 ^ n * d)
          * evertseCountBase n d t δ ^ (2 ^ n * (d + e * u)) := by
          gcongr
          · exact parametricGridCount_system_le hn ht he hed hδ hδ1 hp'
          · calc (2 : ℝ) ^ (n.choose p * (d + e * u))
                ≤ evertseCountBase n d t δ ^ (n.choose p * (d + e * u)) :=
                  pow_le_pow_left₀ (by norm_num) (by linarith) _
              _ ≤ _ := pow_le_pow_right₀ hZ1 (Nat.mul_le_mul_right _ hC)
      _ = _ := by rw [← pow_add]; congr 1; ring
  rw [parametricSubspaceCount]
  push_cast
  gcongr
  calc ∑ p ∈ Finset.range n, (parametricGridCount n d d p (systemEps e δ)
        (systemAbsBound e n t) : ℝ) * 2 ^ (n.choose p * (d + e * u))
      ≤ ∑ _p ∈ Finset.range n, evertseCountBase n d t δ ^ (2 ^ n * (2 * d + e * u)) :=
        Finset.sum_le_sum hstep
    _ = _ := by simp

/-- The number of intervals of Layer 6.1 for a system, with Evertse's chain, is at most
`n Z ^ (2 ^ n d + 10)`. -/
theorem parametricIntervalCount_system_le (hn : 1 ≤ n) (ht : 1 ≤ t) (he : 1 ≤ e) (hed : e ≤ d)
    (hu : u ≤ t) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (parametricIntervalCount n d d (d + e * u) (systemEps e δ) (systemAbsBound e n t) : ℝ)
      ≤ n * evertseCountBase n d t δ ^ (2 ^ n * d + 10) := by
  have hstep : ∀ p ∈ Finset.range n,
      (parametricGridCount n d d p (systemEps e δ) (systemAbsBound e n t) : ℝ)
        * (parametricChainLength n d (d + e * u) p (systemEps e δ) (systemAbsBound e n t) : ℝ)
      ≤ evertseCountBase n d t δ ^ (2 ^ n * d + 10) := fun p hp ↦ by
    have hp' : p ≤ n := (Finset.mem_range.1 hp).le
    have hm := parametricChainLength_step_le hn ht he hed hu hδ hδ1 hp'
    have hZ0 := evertseCountBase_nonneg hn ht (he.trans hed) hδ hδ1
    rw [pow_add]
    exact mul_le_mul (parametricGridCount_system_le hn ht he hed hδ hδ1 hp') (by linarith)
      (Nat.cast_nonneg _) (pow_nonneg hZ0 _)
  rw [parametricIntervalCount]
  push_cast
  calc ∑ p ∈ Finset.range n, (parametricGridCount n d d p (systemEps e δ)
        (systemAbsBound e n t) : ℝ)
        * (parametricChainLength n d (d + e * u) p (systemEps e δ) (systemAbsBound e n t) : ℝ)
      ≤ ∑ _p ∈ Finset.range n, evertseCountBase n d t δ ^ (2 ^ n * d + 10) :=
        Finset.sum_le_sum hstep
    _ = _ := by simp

/-- The factor `1 + log ρ / log (1 + δ / (2 n))` of the count, with Evertse's Roth lemma, is at
most `2 Z ^ 2`. -/
theorem one_add_log_parametricRatio_div_le (b : ℕ → ℝ) (hn : 1 ≤ n) (ht : 1 ≤ t) (he : 1 ≤ e)
    (hed : e ≤ d) (hu : u ≤ t) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 + Real.log (parametricRatio (RothParams.evertse b) n d (d + e * u) (systemEps e δ)
        (systemAbsBound e n t)) / Real.log (1 + δ / (2 * n))
      ≤ 2 * evertseCountBase n d t δ ^ 2 := by
  have hd : 1 ≤ d := he.trans hed
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  have hZ := const_le_evertseCountBase hn ht hd hδ hδ1
  have hZ0 : 0 < evertseCountBase n d t δ := by linarith
  have hρ := parametricRatio_evertse_system_le b hn ht he hed hu hδ hδ1
  have hρ1 := one_le_parametricRatio (RothParams.evertse b) d (d + e * u) (by omega : 0 < n) hε
    (systemAbsBound_nonneg e n t)
  have hlogρ : Real.log (parametricRatio (RothParams.evertse b) n d (d + e * u) (systemEps e δ)
      (systemAbsBound e n t)) ≤ 16 * evertseCountBase n d t δ := by
    have h := Real.log_le_log (by linarith) hρ
    rw [Real.log_pow] at h
    have hlogZ := Real.log_le_sub_one_of_pos hZ0
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
  have hmono := monomial_le' hn ht hd (c := 64) (by norm_num) (by norm_num) (a := 1) (b := 0)
    (k := 0) (by norm_num) (by norm_num) (by norm_num)
  simp only [pow_one, pow_zero, mul_one] at hmono
  have h64 := div_le_evertseCountBase hδ hmono
  rw [div_le_iff₀ hδ] at h64
  have hkey : 16 * evertseCountBase n d t δ ≤ evertseCountBase n d t δ ^ 2 * (x / 2) := by
    have : evertseCountBase n d t δ ^ 2 * (x / 2)
        = evertseCountBase n d t δ * (evertseCountBase n d t δ * δ) / (4 * n) := by
      rw [hx]; field_simp; ring
    rw [this, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h64 hZ0.le]
  have hdiv : Real.log (parametricRatio (RothParams.evertse b) n d (d + e * u) (systemEps e δ)
      (systemAbsBound e n t)) / Real.log (1 + x) ≤ evertseCountBase n d t δ ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hL (sq_nonneg (evertseCountBase n d t δ))]
  nlinarith

/-- **The number of subspaces for the large solutions of a system, with Evertse's Roth lemma, in
closed form** (Q1.6): Q0.3's `systemLargeCount` is at most
`Z ^ (t n + 2 ^ n (2 d + e u) + 13)` with `Z = 2 ^ (n + 12) n ^ 6 t ^ 2 d ^ 2 / δ`, polynomial in
`δ⁻¹`. Here `n` is the number of variables, `d = [E : ℚ]`, `e = [E : K]`, `t` the number of
places of `K` in `S` and `u` the number of finite ones. -/
theorem systemLargeCount_evertse_le (b : ℕ → ℝ) (hn : 1 ≤ n) (ht : 1 ≤ t) (he : 1 ≤ e)
    (hed : e ≤ d) (hu : u ≤ t) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    systemLargeCount (RothParams.evertse b) n d e t u δ
      ≤ evertseCountBase n d t δ ^ (t * n + 2 ^ n * (2 * d + e * u) + 13) := by
  have hd : 1 ≤ d := he.trans hed
  have hε : 0 < systemEps e δ := by rw [systemEps]; positivity
  have hZ := const_le_evertseCountBase hn ht hd hδ hδ1
  have hZ1 : 1 ≤ evertseCountBase n d t δ := le_trans (by norm_num) hZ
  have h3n : 1 + 3 * (n : ℝ) ≤ evertseCountBase n d t δ := by
    have : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
    have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
    have := mul_two_pow_le_evertseCountBase hn ht hd hδ hδ1
    linarith
  have hG := systemGridCount_le hn ht hd hδ hδ1
  have hS := parametricSubspaceCount_system_le (u := u) hn ht he hed hδ hδ1
  have hI := parametricIntervalCount_system_le hn ht he hed hu hδ hδ1
  have hW := one_add_log_parametricRatio_div_le b hn ht he hed hu hδ hδ1
  have hρ1 := one_le_parametricRatio (RothParams.evertse b) d (d + e * u) (by omega : 0 < n) hε
    (systemAbsBound_nonneg e n t)
  have hW0 : 0 ≤ 1 + Real.log (parametricRatio (RothParams.evertse b) n d (d + e * u)
      (systemEps e δ) (systemAbsBound e n t)) / Real.log (1 + δ / (2 * n)) := by
    have : 0 < Real.log (1 + δ / (2 * n)) :=
      Real.log_pos (by have : (0 : ℝ) < δ / (2 * n) := by positivity
                       linarith)
    have := Real.log_nonneg hρ1
    positivity
  set E := 2 ^ n * (2 * d + e * u) with hE
  set Z := evertseCountBase n d t δ with hZdef
  have hdE : 2 ^ n * d ≤ E := by rw [hE]; exact Nat.mul_le_mul_left _ (by omega)
  have hI' : (n : ℝ) * Z ^ (2 ^ n * d + 10) ≤ n * Z ^ (E + 10) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hZ1 (by omega)) (Nat.cast_nonneg n)
  have hI2 := hI.trans hI'
  have hZE : Z ^ E ≤ Z ^ (E + 12) := pow_le_pow_right₀ hZ1 (by omega)
  have hZE1 : 1 ≤ Z ^ (E + 12) := one_le_pow₀ hZ1
  rw [systemLargeCount]
  calc (systemGridCount n t δ : ℝ) * ((parametricSubspaceCount n d d (d + e * u) (systemEps e δ)
          (systemAbsBound e n t) : ℝ) + (parametricIntervalCount n d d (d + e * u)
            (systemEps e δ) (systemAbsBound e n t) : ℝ)
          * (1 + Real.log (parametricRatio (RothParams.evertse b) n d (d + e * u)
            (systemEps e δ) (systemAbsBound e n t)) / Real.log (1 + δ / (2 * n))))
      ≤ Z ^ (t * n) * ((1 + n * Z ^ E) + (n * Z ^ (E + 10)) * (2 * Z ^ 2)) := by
        gcongr
    _ ≤ Z ^ (t * n) * (Z * Z ^ (E + 12)) := by
        gcongr
        have : (n : ℝ) * Z ^ (E + 10) * (2 * Z ^ 2) = 2 * n * Z ^ (E + 12) := by ring
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith [mul_le_mul_of_nonneg_left hZE hn0, mul_le_mul_of_nonneg_right h3n
          (by linarith : (0 : ℝ) ≤ Z ^ (E + 12))]
    _ = Z ^ (t * n + E + 13) := by ring

end Count

/-! ### The quantitative Subspace Theorem for a system -/

section System

variable {K : Type*} [Field K] [NumberField K] {ι : Type u} [Fintype ι]

open scoped Classical in
/-- **The quantitative Subspace Theorem for a system, with Evertse's Roth lemma, in closed form**
(Q1.6): as `NumberField.exists_finset_submodule_of_isNormalizedSystem_evertse`, with the count of
the large solutions bounded by `Z ^ (t n + 2 ^ n (2 [E : ℚ] + [E : K] |S_fin|) + 13)`, where
`Z = 2 ^ (n + 12) n ^ 6 t ^ 2 [E : ℚ] ^ 2 / δ`, `n = #ι` and `t` is the number of places of `K`
in `S`. -/
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
            (systemThreshold E S w L (RothParams.evertse fun m ↦ (H m).botBound 1) Hc δ)) /
              Real.log (1 + δ / (2 * Fintype.card ι))) +
        evertseCountBase (Fintype.card ι) (finrank ℚ E) (Fintype.card (InfinitePlace K) + #S) δ
          ^ ((Fintype.card (InfinitePlace K) + #S) * Fintype.card ι
            + 2 ^ Fintype.card ι * (2 * finrank ℚ E + finrank K E * #S) + 13) ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∀ x ∈ systemSet S w L C c, ∃ U ∈ T, x ∈ U := by
  obtain ⟨T, hT, hTtop, hTmem⟩ :=
    exists_finset_submodule_of_isNormalizedSystem_evertse H hCM S w hwInf hwFin hN
  refine ⟨T, hT.trans ?_, hTtop, hTmem⟩
  have hn : 1 ≤ Fintype.card ι := by have := hN.two_le_card; omega
  have ht : 1 ≤ Fintype.card (InfinitePlace K) + #S := by
    have := Fintype.card_pos (α := InfinitePlace K); omega
  have he : 1 ≤ finrank K E := finrank_pos
  have hed : finrank K E ≤ finrank ℚ E := by
    rw [← Module.finrank_mul_finrank ℚ K E]
    exact Nat.le_mul_of_pos_left _ finrank_pos
  exact add_le_add_right (systemLargeCount_evertse_le (u := #S) _ hn ht he hed (by omega)
    hN.delta_pos hN.delta_le_one) _

end System

end NumberField
