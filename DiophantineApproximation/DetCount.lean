/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SubspaceSystem
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Dual.Defs

-- Used only inside proofs.
import DiophantineApproximation.ApproximationVolume
import DiophantineApproximation.FieldMinkowski
import DiophantineApproximation.FinitePlaceValues
import DiophantineApproximation.PlacesOverFinite
import DiophantineApproximation.SubspaceGap
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Nat

/-!
# Covering points of bounded determinant by few subspaces

**Layer 9.3 (infrastructure for `ℚ`).** Evertse, "On the Quantitative Subspace Theorem",
Lemmas 4.4 and 4.5: a set of `S`-integral points of `ℚⁿ`, `n ≥ 2`, any `n` of which have
determinant at most `D v` at every place `v`, lies in at most
`100 ^ n max (1, ∏ D v) ^ (1 / (n - 1))` proper subspaces. The source quotes Lemma 4.4 (the case of
integral points) from Lemma 5 of Evertse, *On the norm form inequality `|F(x)| ≤ h`*, and deduces
Lemma 4.5 from it through a lattice; here both are proved directly, with the sharper constant
`3 ^ n (4 n² + 2)²`.

## Main results

* `Module.Dual.exists_finset_submodule_of_forall_eq_intCast`: **the pigeonhole**. If independent
  functionals `φ 0, …, φ (n - 1)` take integer values of size at most `R μ k` on `T`, with
  `1 ≤ μ 0 ≤ μ 1 ≤ ⋯`, then `T` lies in at most `3 ^ n c (c ∏ μ k) ^ (1 / (n - 1))` proper
  subspaces, `c = 2 R n + 2`.
* `NumberField.dotProduct_eq_sum_det_update_div`: Cramer's rule, against a functional.
* `Rat.exists_finset_submodule_of_det_le`: **Lemma 4.5**, with `3 ^ n (4 n² + 2)²`.
* `Rat.exists_finset_submodule_of_det_le_hundred_pow`: Lemma 4.5 with Evertse's `100 ^ n`.
* `Rat.exists_finset_submodule_of_abs_det_le`: **Lemma 4.4**, for integral points.

## Implementation notes

⚠ **The dual lattice is an approximation module of Layer 4, and Minkowski's second theorem is
Layer 4.2's.** For each place `v` choose `n` points `Y v` of `T` whose determinant is at least
half of every other at `v`. By Cramer's rule every point of `T` is a combination of the `Y v i`
with coefficients of size `< 2` at `v`, hence `≤ 1` at a finite `v`, the values there being powers
of `p`. So every `h` with `|h · Y v i|_v ≤ 1` at the finite places of `S` and integral elsewhere
takes integer values on `T`: this is `approxModule` with the forms `h ↦ Y v i · h` at level `1`,
exponents `0`. Its minima `μ k` against the body `|h · Y ∞ i| ≤ 1` satisfy
`∏ μ k ≤ |det Y ∞| ∏ |det Y v|_v ≤ ∏ D v`, the volume and covolume being those of Layer 4.1
(`volume_approxBody`, `covolume_approxLattice`) with no loss at level `1`. The minimal vectors
take integer values of size `≤ 2 n μ k` on `T`, and `μ 0 ≥ 1` because the first one is nonzero on
some `Y ∞ i`.

⚠ **The pigeonhole uses a prefix of the minima, not all of them.** With `X` defined by
`X ^ (m - 1) = c μ 0 ⋯ μ (m - 1)`, the box `∏_{k < m} [0, X / μ k]` has at least `c X` points and
the values `∑ a k φ k x` fewer, so two coincide and `x` lies in the kernel of a nonzero
`∑ b k φ k` with `|b k| ≤ X / μ k`; there are at most `3 ^ m c X` of those. This needs
`μ (m - 1) ≤ X`, which may fail for `m = n` when the last minimum is large; the longest prefix for
which it holds has the smallest level, and `X ≤ (c ∏ μ k) ^ (1 / (n - 1))`.

⚠ **`max (1, ·)` is needed.** A set in a proper subspace needs one subspace whatever `D`, so the
source's `100 ^ n D ^ (1 / (n - 1))` fails for small `D`; when `T` spans, `D ≥ 1` anyway.

## References

J.-H. Evertse, *On the Quantitative Subspace Theorem*, Zap. Nauchn. Sem. POMI **377** (2010),
217–240 (arXiv:1008.2268), Lemmas 4.4 and 4.5; J.-H. Evertse, *On the norm form inequality
`|F(x)| ≤ h`*, Publ. Math. Debrecen **56** (2000), 337–374, Lemma 5.

This is part of Layer 9.3 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset

namespace Module.Dual

/-- The level of the prefix of length `m` of the minima: `X m ^ (m - 1) = c · μ 0 ⋯ μ (m - 1)`. -/
private noncomputable def prefixLevel (c : ℝ) (μ : ℕ → ℝ) (m : ℕ) : ℝ :=
  (c * ∏ k ∈ range m, μ k) ^ (((m - 1 : ℕ) : ℝ)⁻¹)

private theorem prefixLevel_pow {c : ℝ} (hc : 0 ≤ c) {μ : ℕ → ℝ} (hμ : ∀ k, 0 ≤ μ k) {m : ℕ}
    (hm : 2 ≤ m) : prefixLevel c μ m ^ (m - 1) = c * ∏ k ∈ range m, μ k :=
  Real.rpow_inv_natCast_pow (mul_nonneg hc (prod_nonneg fun k _ ↦ hμ k)) (by omega)

private theorem prefixLevel_nonneg (c : ℝ) (μ : ℕ → ℝ) (hc : 0 ≤ c) (hμ : ∀ k, 0 ≤ μ k)
    (m : ℕ) : 0 ≤ prefixLevel c μ m :=
  Real.rpow_nonneg (mul_nonneg hc (prod_nonneg fun k _ ↦ hμ k)) _

/-- **The choice of the prefix.** For minima `1 ≤ μ 0 ≤ μ 1 ≤ ⋯` and `c ≥ 1` there is a length
`m ∈ [2, M]` whose last minimum is at most its level, and whose level is at most that of the
whole family. If the last minimum of a prefix exceeds its level, the shorter prefix has the
smaller level, so the longest admissible prefix does. -/
private theorem exists_prefix {c : ℝ} (hc : 1 ≤ c) {μ : ℕ → ℝ} (hμ : ∀ k, 1 ≤ μ k) :
    ∀ M, 2 ≤ M → ∃ m, 2 ≤ m ∧ m ≤ M ∧ μ (m - 1) ≤ prefixLevel c μ m ∧
      prefixLevel c μ m ≤ prefixLevel c μ M := by
  have hμ0 : ∀ k, 0 ≤ μ k := fun k ↦ zero_le_one.trans (hμ k)
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  intro M hM
  induction M, hM using Nat.le_induction with
  | base =>
    refine ⟨2, le_rfl, le_rfl, ?_, le_rfl⟩
    have h := prefixLevel_pow hc0 hμ0 (le_refl 2)
    simp only [Nat.reduceSub, pow_one, prod_range_succ, prod_range_zero, one_mul] at h
    rw [h, show 2 - 1 = 1 from rfl]
    have h1 : 1 ≤ c * μ 0 := one_le_mul_of_one_le_of_one_le hc (hμ 0)
    nlinarith [hμ 1]
  | succ m hm ih =>
    obtain ⟨m', hm'2, hm'm, hm'μ, hm'X⟩ := ih
    by_cases h : μ m ≤ prefixLevel c μ (m + 1)
    · exact ⟨m + 1, by omega, le_rfl, by simpa using h, le_rfl⟩
    · refine ⟨m', hm'2, by omega, hm'μ, hm'X.trans ?_⟩
      push Not at h
      by_contra hlt
      push Not at hlt
      have h0 := prefixLevel_nonneg c μ hc0 hμ0 (m + 1)
      have e1 := prefixLevel_pow hc0 hμ0 (show 2 ≤ m + 1 by omega)
      have e2 := prefixLevel_pow hc0 hμ0 hm
      rw [prod_range_succ, ← mul_assoc, ← e2, Nat.add_sub_cancel] at e1
      have hpow : prefixLevel c μ (m + 1) ^ (m - 1) < prefixLevel c μ m ^ (m - 1) :=
        pow_lt_pow_left₀ hlt h0 (by omega)
      have : prefixLevel c μ (m + 1) ^ (m - 1) * prefixLevel c μ (m + 1) <
          prefixLevel c μ m ^ (m - 1) * μ m :=
        mul_lt_mul'' hpow h (pow_nonneg h0 _) h0
      rw [← pow_succ, Nat.sub_add_cancel (by omega), ← e1] at this
      exact lt_irrefl _ this

/-- **The pigeonhole.** If the integers `z k` are small against the box `∏ [0, A k]`, some nonzero
integer combination with `|b k| ≤ A k` vanishes. -/
private theorem exists_ne_zero_sum_eq_zero {n : ℕ} (A : Fin n → ℕ) (z : Fin n → ℤ) (N : ℕ)
    (hz : ∑ k, (A k : ℤ) * |z k| ≤ N) (hcard : 2 * N + 1 < ∏ k, (A k + 1)) :
    ∃ b : Fin n → ℤ, b ≠ 0 ∧ (∀ k, |b k| ≤ A k) ∧ ∑ k, b k * z k = 0 := by
  classical
  set s := Fintype.piFinset fun k ↦ range (A k + 1) with hs
  set t := Icc (-(N : ℤ)) N with ht
  have hst : t.card < s.card := by
    rw [hs, Fintype.card_piFinset, ht, Int.card_Icc]
    simp only [card_range]
    omega
  have hmaps : Set.MapsTo (fun a : Fin n → ℕ ↦ ∑ k, (a k : ℤ) * z k) s t := by
    intro a ha
    have ha' : ∀ k, a k ≤ A k := fun k ↦ by
      have := Fintype.mem_piFinset.1 ha k
      rw [mem_range] at this
      omega
    have hle : |∑ k, (a k : ℤ) * z k| ≤ N := by
      refine (abs_sum_le_sum_abs _ _).trans (le_trans ?_ hz)
      refine sum_le_sum fun k _ ↦ ?_
      rw [abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast ha' k) (abs_nonneg _)
    simp only [ht, coe_Icc, Set.mem_Icc]
    exact abs_le.1 hle
  obtain ⟨a, ha, a', ha', hne, heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hst hmaps
  have hle : ∀ k, a k ≤ A k ∧ a' k ≤ A k := fun k ↦ by
    have h1 := Fintype.mem_piFinset.1 ha k
    have h2 := Fintype.mem_piFinset.1 ha' k
    rw [mem_range] at h1 h2
    omega
  refine ⟨fun k ↦ (a k : ℤ) - a' k, fun h ↦ hne (funext fun k ↦ ?_), fun k ↦ ?_, ?_⟩
  · have := congrFun h k
    simp only [Pi.zero_apply, sub_eq_zero] at this
    exact_mod_cast this
  · have := hle k
    change |((a k : ℤ) - a' k)| ≤ A k
    rw [abs_le]
    constructor <;> omega
  · simp only [sub_mul, sum_sub_distrib]
    exact sub_eq_zero.2 heq

/-- **Covering by kernels** (the pigeonhole of Evertse's Lemma 4.4). Let `φ 0, …, φ (n - 1)` be
independent functionals, `n ≥ 2`, and `1 ≤ μ 0 ≤ μ 1 ≤ ⋯`. If on every point of `T` each
`φ k` takes an integer value of size at most `R μ k`, then `T` lies in at most
`3 ^ n c (c μ 0 ⋯ μ (n - 1)) ^ (1 / (n - 1))` proper subspaces, `c = 2 R n + 2`. -/
theorem exists_finset_submodule_of_forall_eq_intCast {V : Type*} [AddCommGroup V] [Module ℚ V]
    {n : ℕ} (hn : 2 ≤ n) (φ : Fin n → Module.Dual ℚ V) (hφ : LinearIndependent ℚ φ)
    {μ : ℕ → ℝ} (hμ : ∀ k, 1 ≤ μ k) (hmono : ∀ i j, i ≤ j → μ i ≤ μ j) {R : ℝ} (hR : 0 ≤ R)
    (T : Set V) (hT : ∀ x ∈ T, ∀ k, ∃ z : ℤ, φ k x = z ∧ |(z : ℝ)| ≤ R * μ k) :
    ∃ U : Finset (Submodule ℚ V),
      (U.card : ℝ) ≤ 3 ^ n * (2 * R * n + 2) *
        ((2 * R * n + 2) * ∏ k ∈ range n, μ k) ^ (((n - 1 : ℕ) : ℝ)⁻¹) ∧
      (∀ W ∈ U, W ≠ ⊤) ∧ ∀ x ∈ T, ∃ W ∈ U, x ∈ W := by
  classical
  set c : ℝ := 2 * R * n + 2 with hc
  have hc1 : 1 ≤ c := by rw [hc]; have : 0 ≤ 2 * R * n := by positivity
                         linarith
  have hμ0 : ∀ k, 0 < μ k := fun k ↦ zero_lt_one.trans_le (hμ k)
  obtain ⟨m, hm2, hmn, hmX, hXX⟩ := exists_prefix hc1 hμ n hn
  set X := prefixLevel c μ m with hX
  have hX1 : 1 ≤ X := (hμ _).trans hmX
  have hX0 : 0 < X := zero_lt_one.trans_le hX1
  have hXpow : X ^ (m - 1) = c * ∏ k ∈ range m, μ k :=
    prefixLevel_pow (zero_le_one.trans hc1) (fun k ↦ (hμ0 k).le) hm2
  -- the box
  set A : ℕ → ℕ := fun k ↦ if k < m then ⌊X / μ k⌋₊ else 0 with hA
  have hXμ : ∀ k < m, 1 ≤ X / μ k := fun k hk ↦ by
    rw [le_div_iff₀ (hμ0 k), one_mul]
    exact (hmono k (m - 1) (by omega)).trans hmX
  have hprodX : ∏ k ∈ range m, X / μ k = c * X := by
    rw [prod_div_distrib, prod_const, card_range, div_eq_iff (prod_pos fun k _ ↦ hμ0 k).ne',
      show m = m - 1 + 1 by omega, pow_succ, hXpow, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    ring
  have hsplit : ∀ f : ℕ → ℝ, (∀ k, m ≤ k → f k = 1) →
      ∏ k : Fin n, f k = ∏ k ∈ range m, f k := fun f hf ↦ by
    rw [Fin.prod_univ_eq_prod_range f n, ← prod_range_mul_prod_Ico f hmn,
      prod_eq_one fun k hk ↦ hf k (mem_Ico.1 hk).1, mul_one]
  have hlow : c * X ≤ ∏ k : Fin n, ((A k : ℝ) + 1) := by
    rw [hsplit (fun k ↦ (A k : ℝ) + 1) fun k hk ↦ by simp [hA, not_lt.2 hk], ← hprodX]
    refine Finset.prod_le_prod₀ (fun k hk ↦ (div_pos hX0 (hμ0 k)).le) fun k hk ↦ ?_
    have hk := mem_range.1 hk
    simp only [hA, hk, ↓reduceIte]
    exact (Nat.lt_floor_add_one _).le
  have hup : ∏ k : Fin n, (2 * (A k : ℝ) + 1) ≤ 3 ^ n * (c * X) := by
    rw [hsplit (fun k ↦ 2 * (A k : ℝ) + 1) fun k hk ↦ by simp [hA, not_lt.2 hk], ← hprodX]
    calc ∏ k ∈ range m, (2 * (A k : ℝ) + 1) ≤ ∏ k ∈ range m, (3 * (X / μ k)) := by
          refine Finset.prod_le_prod₀ (fun k _ ↦ by positivity) fun k hk ↦ ?_
          have hk := mem_range.1 hk
          simp only [hA, hk, ↓reduceIte]
          have h1 : (1 : ℝ) ≤ ⌊X / μ k⌋₊ := by
            exact_mod_cast Nat.one_le_iff_ne_zero.2
              (Nat.floor_pos.2 (hXμ k hk)).ne'
          have h2 : (⌊X / μ k⌋₊ : ℝ) ≤ X / μ k := Nat.floor_le (div_pos hX0 (hμ0 k)).le
          linarith
      _ = 3 ^ m * ∏ k ∈ range m, X / μ k := by rw [prod_mul_distrib, prod_const, card_range]
      _ ≤ 3 ^ n * ∏ k ∈ range m, X / μ k :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hmn)
            (prod_nonneg fun k _ ↦ (div_pos hX0 (hμ0 k)).le)
  -- the kernels
  set B : Finset (Fin n → ℤ) :=
    (Fintype.piFinset fun k ↦ Icc (-(A (k : Fin n) : ℤ)) (A k)).filter (· ≠ 0) with hB
  set ker : (Fin n → ℤ) → Submodule ℚ V :=
    fun b ↦ LinearMap.ker (∑ k, ((b k : ℚ)) • φ k) with hker
  refine ⟨B.image ker, ?_, fun W hW ↦ ?_, fun x hx ↦ ?_⟩
  · calc ((B.image ker).card : ℝ) ≤ B.card := by exact_mod_cast card_image_le
      _ ≤ (Fintype.piFinset fun k ↦ Icc (-(A (k : Fin n) : ℤ)) (A k)).card := by
          exact_mod_cast card_filter_le _ _
      _ = ∏ k : Fin n, (2 * (A k : ℝ) + 1) := by
          rw [Fintype.card_piFinset]
          push_cast
          refine prod_congr rfl fun k _ ↦ ?_
          rw [Int.card_Icc]
          have : ((A k : ℤ) + 1 - -(A k : ℤ)).toNat = 2 * A k + 1 := by omega
          rw [this]; push_cast; ring
      _ ≤ 3 ^ n * (c * X) := hup
      _ ≤ 3 ^ n * (c * (c * ∏ k ∈ range n, μ k) ^ (((n - 1 : ℕ) : ℝ)⁻¹)) := by
          gcongr
          exact hXX
      _ = _ := by ring
  · obtain ⟨b, hb, rfl⟩ := mem_image.1 hW
    have hb0 := (mem_filter.1 hb).2
    rw [hker, Ne, LinearMap.ker_eq_top]
    intro h0
    refine hb0 (funext fun k ↦ ?_)
    have := Fintype.linearIndependent_iff.1 hφ (fun k ↦ (b k : ℚ)) h0 k
    exact_mod_cast this
  · choose z hz hzle using hT x hx
    have hzA : ∑ k : Fin n, (A k : ℤ) * |z k| ≤ ⌊R * n * X⌋₊ := by
      have hr : (∑ k : Fin n, (A k : ℤ) * |z k| : ℝ) ≤ R * n * X := by
        push_cast
        calc ∑ k : Fin n, (A k : ℝ) * |(z k : ℝ)| ≤ ∑ k : Fin n, R * X := by
              refine sum_le_sum fun k _ ↦ ?_
              by_cases hk : (k : ℕ) < m
              · simp only [hA, hk, ↓reduceIte]
                have h2 : (⌊X / μ k⌋₊ : ℝ) * μ k ≤ X := by
                  have := Nat.floor_le (div_pos hX0 (hμ0 k)).le
                  rwa [le_div_iff₀ (hμ0 k)] at this
                calc (⌊X / μ k⌋₊ : ℝ) * |(z k : ℝ)| ≤ ⌊X / μ k⌋₊ * (R * μ k) :=
                      mul_le_mul_of_nonneg_left (hzle k) (Nat.cast_nonneg _)
                  _ = R * ((⌊X / μ k⌋₊ : ℝ) * μ k) := by ring
                  _ ≤ R * X := mul_le_mul_of_nonneg_left h2 hR
              · simp only [hA, hk, ↓reduceIte, Nat.cast_zero, zero_mul]
                positivity
          _ = R * n * X := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      have hs0 : 0 ≤ ∑ k : Fin n, (A k : ℤ) * |z k| :=
        sum_nonneg fun k _ ↦ mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
      have := Nat.le_floor
        (show (((∑ k : Fin n, (A k : ℤ) * |z k|).toNat : ℕ) : ℝ) ≤ R * n * X by
          rw [show (((∑ k : Fin n, (A k : ℤ) * |z k|).toNat : ℕ) : ℝ) =
            ((∑ k : Fin n, (A k : ℤ) * |z k| : ℤ) : ℝ) by exact_mod_cast Int.toNat_of_nonneg hs0]
          exact_mod_cast hr)
      omega
    have hcard : 2 * ⌊R * n * X⌋₊ + 1 < ∏ k : Fin n, (A k + 1) := by
      have h1 : (⌊R * n * X⌋₊ : ℝ) ≤ R * n * X := Nat.floor_le (by positivity)
      have h2 : ((2 * ⌊R * n * X⌋₊ + 1 : ℕ) : ℝ) < ((∏ k : Fin n, (A k + 1) : ℕ) : ℝ) := by
        push_cast
        refine lt_of_lt_of_le ?_ hlow
        rw [hc]
        nlinarith
      exact_mod_cast h2
    obtain ⟨b, hb0, hbA, hbz⟩ :=
      exists_ne_zero_sum_eq_zero (fun k : Fin n ↦ A k) z _ hzA hcard
    refine ⟨ker b, mem_image_of_mem _ (mem_filter.2 ⟨Fintype.mem_piFinset.2 fun k ↦ ?_, hb0⟩), ?_⟩
    · exact mem_Icc.2 (abs_le.1 (hbA k))
    · rw [hker, LinearMap.mem_ker, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, hz, smul_eq_mul]
      exact_mod_cast hbz

end Module.Dual

namespace NumberField

open Module IsDedekindDomain Matrix

/-- A value of a finite place below `2` is at most `1`: the values are powers of the norm of the
prime, which is at least `2`. -/
theorem FinitePlace.apply_le_one_of_lt_two {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) {x : K} (h : v x < 2) : v x ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨k, hk⟩ := v.exists_apply_eq_zpow hx
  have hN := v.one_lt_absNorm
  have hN2 : (2 : ℝ) ≤ (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) := by
    have h1 : 1 < Ideal.absNorm v.maximalIdeal.asIdeal := by exact_mod_cast hN
    have h2 : 2 ≤ Ideal.absNorm v.maximalIdeal.asIdeal := h1
    exact_mod_cast h2
  rw [hk] at h ⊢
  have hk0 : k ≤ 0 := by
    by_contra hk1
    push Not at hk1
    have := zpow_le_zpow_right₀ hN.le (show (1 : ℤ) ≤ k by omega)
    rw [zpow_one] at this
    linarith
  exact zpow_le_one_of_nonpos₀ hN.le hk0

/-- A rational number of value at most `1` at every finite place is an integer. -/
theorem _root_.Rat.exists_intCast_eq_of_forall_finitePlace_le_one {q : ℚ}
    (h : ∀ v : FinitePlace ℚ, v q ≤ 1) : ∃ z : ℤ, (z : ℚ) = q := by
  obtain ⟨z, hz⟩ := FinitePlace.exists_eq_of_forall_apply_le_one h
  have hi : IsIntegral ℤ q := hz ▸ RingOfIntegers.isIntegral_coe z
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 hi
  exact ⟨y, by simpa using hy⟩

variable {ι : Type*} [Fintype ι]

/-- **Cramer's rule, against a functional.** If `det y ≠ 0`, then `h · x` is the sum of the
`h · y i` weighted by the quotients `det (y with x in row i) / det y`. -/
theorem dotProduct_eq_sum_det_update_div [DecidableEq ι] {K : Type*} [Field K]
    {y : ι → ι → K} (hy : (Pi.basisFun K ι).det y ≠ 0) (x h : ι → K) :
    h ⬝ᵥ x = ∑ i, (Pi.basisFun K ι).det (Function.update y i x) / (Pi.basisFun K ι).det y *
      (h ⬝ᵥ y i) := by
  obtain ⟨hli, hsp⟩ := ((Pi.basisFun K ι).is_basis_iff_det).2 (isUnit_iff_ne_zero.2 hy)
  set b := Basis.mk hli hsp.ge with hb
  have hcoord : ∀ i, b.coord i x =
      (Pi.basisFun K ι).det (Function.update y i x) / (Pi.basisFun K ι).det y := fun i ↦ by
    have := congrArg (· x) ((Pi.basisFun K ι).det_smul_mk_coord_eq_det_update hli hsp.ge i)
    simp only [LinearMap.smul_apply, smul_eq_mul, MultilinearMap.toLinearMap_apply] at this
    rw [eq_div_iff hy, mul_comm]
    exact this
  conv_lhs => rw [← b.sum_repr x]
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [dotProduct_smul, Basis.mk_apply, smul_eq_mul, ← Basis.coord_apply, hcoord]

/-- **A tuple of nearly largest determinant.** If the values of an absolute value at the
determinants of the tuples from `T` are bounded and one is nonzero, some tuple from `T` has a
determinant at least half of every other. -/
theorem exists_forall_apply_det_lt_two_mul [DecidableEq ι] {K : Type*} [Field K]
    (a : AbsoluteValue K ℝ) {T : Set (ι → K)} {B : ℝ}
    (hB : ∀ y : ι → ι → K, (∀ j, y j ∈ T) → a ((Pi.basisFun K ι).det y) ≤ B)
    {y₀ : ι → ι → K} (hy₀T : ∀ j, y₀ j ∈ T) (hy₀ : (Pi.basisFun K ι).det y₀ ≠ 0) :
    ∃ y : ι → ι → K, (∀ j, y j ∈ T) ∧ (Pi.basisFun K ι).det y ≠ 0 ∧
      ∀ y' : ι → ι → K, (∀ j, y' j ∈ T) →
        a ((Pi.basisFun K ι).det y') < 2 * a ((Pi.basisFun K ι).det y) := by
  set V : Set ℝ := {r | ∃ y : ι → ι → K, (∀ j, y j ∈ T) ∧ r = a ((Pi.basisFun K ι).det y)}
    with hV
  have hbdd : BddAbove V := ⟨B, by rintro r ⟨y, hy, rfl⟩; exact hB y hy⟩
  have h0 : a ((Pi.basisFun K ι).det y₀) ∈ V := ⟨y₀, hy₀T, rfl⟩
  have hpos : 0 < a ((Pi.basisFun K ι).det y₀) := a.pos hy₀
  have hs : 0 < sSup V := hpos.trans_le (le_csSup hbdd h0)
  obtain ⟨r, ⟨y, hyT, rfl⟩, hr⟩ := exists_lt_of_lt_csSup ⟨_, h0⟩ (half_lt_self hs)
  refine ⟨y, hyT, fun h ↦ ?_, fun y' hy' ↦ ?_⟩
  · rw [h, map_zero] at hr
    linarith
  · have := le_csSup hbdd ⟨y', hy', rfl⟩
    linarith

open scoped Classical in
/-- **Evertse's Lemma 4.5 over `ℚ`, in the form of a system.** Let `T` be a set of `S`-integral
points of `ℚⁿ`, `n ≥ 2`, any `n` of which have determinant at most `D p` at every place `p` of
the system. Then `T` lies in at most `3 ^ n (4 n² + 2)² max (1, ∏ D p) ^ (1 / (n - 1))` proper
subspaces. -/
theorem _root_.Rat.exists_finset_submodule_of_det_le (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hn : 2 ≤ Fintype.card ι) {T : Set (ι → ℚ)}
    (hT : ∀ x ∈ T, ∀ j, x j ∈ (S : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)
    (D : InfinitePlace ℚ ⊕ S → ℝ)
    (hD : ∀ y : ι → ι → ℚ, (∀ j, y j ∈ T) → ∀ p,
      systemPlace S p ((Pi.basisFun ℚ ι).det y) ≤ D p) :
    ∃ U : Finset (Submodule ℚ (ι → ℚ)),
      (U.card : ℝ) ≤ 3 ^ Fintype.card ι * (4 * Fintype.card ι ^ 2 + 2) ^ 2 *
        max 1 (∏ p, D p) ^ (((Fintype.card ι - 1 : ℕ) : ℝ)⁻¹) ∧
      (∀ W ∈ U, W ≠ ⊤) ∧ ∀ x ∈ T, ∃ W ∈ U, x ∈ W := by
  set n := Fintype.card ι with hn_def
  set e : ℝ := ((n - 1 : ℕ) : ℝ)⁻¹ with he
  have hn0 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 := by
    rw [he]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ n - 1))
  set c : ℝ := 4 * n ^ 2 + 2 with hc
  have hc1 : 1 ≤ c := by rw [hc]; nlinarith
  have hbound1 : (1 : ℝ) ≤ 3 ^ n * c ^ 2 * max 1 (∏ p, D p) ^ e :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (one_le_pow₀ hc1)) (Real.one_le_rpow (le_max_left _ _) he0)
  by_cases hspan : Submodule.span ℚ T ≠ ⊤
  · exact ⟨{Submodule.span ℚ T}, by simpa using hbound1, by simpa using hspan,
      fun x hx ↦ ⟨_, Finset.mem_singleton_self _, Submodule.subset_span hx⟩⟩
  push Not at hspan
  obtain ⟨y₀, hy₀T, hy₀⟩ : ∃ y₀ : ι → ι → ℚ, (∀ j, y₀ j ∈ T) ∧ (Pi.basisFun ℚ ι).det y₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact span_ne_top_of_forall_det_eq_zero h hspan
  -- a tuple of nearly largest determinant at each place
  have hYex : ∀ a : AbsoluteValue ℚ ℝ, ∃ y : ι → ι → ℚ, (∀ j, y j ∈ T) ∧
      (Pi.basisFun ℚ ι).det y ≠ 0 ∧ ((∃ B : ℝ, ∀ y' : ι → ι → ℚ, (∀ j, y' j ∈ T) →
        a ((Pi.basisFun ℚ ι).det y') ≤ B) → ∀ y' : ι → ι → ℚ, (∀ j, y' j ∈ T) →
          a ((Pi.basisFun ℚ ι).det y') < 2 * a ((Pi.basisFun ℚ ι).det y)) := fun a ↦ by
    by_cases hB : ∃ B : ℝ, ∀ y' : ι → ι → ℚ, (∀ j, y' j ∈ T) → a ((Pi.basisFun ℚ ι).det y') ≤ B
    · obtain ⟨B, hB⟩ := hB
      obtain ⟨y, hyT, hy, hy2⟩ := exists_forall_apply_det_lt_two_mul a hB hy₀T hy₀
      exact ⟨y, hyT, hy, fun _ ↦ hy2⟩
    · exact ⟨y₀, hy₀T, hy₀, fun h ↦ absurd h hB⟩
  choose Y hYT hYdet hYgood using hYex
  have hgood : ∀ p y', (∀ j, y' j ∈ T) → systemPlace S p ((Pi.basisFun ℚ ι).det y') <
      2 * systemPlace S p ((Pi.basisFun ℚ ι).det (Y (systemPlace S p))) := fun p ↦
    hYgood _ ⟨D p, fun y' hy' ↦ hD y' hy' p⟩
  -- the forms `h ↦ Y a i ⬝ᵥ h`
  set L : AbsoluteValue ℚ ℝ → ι → Dual ℚ (ι → ℚ) := fun a i ↦ dotProductEquiv ℚ ι (Y a i)
    with hL
  have hLapply : ∀ a i h, L a i h = Y a i ⬝ᵥ h := fun a i h ↦ rfl
  have hLdet : ∀ a, LinearMap.det (LinearMap.pi (L a)) = (Pi.basisFun ℚ ι).det (Y a) := fun a ↦ by
    have : LinearMap.pi (L a) = Matrix.toLin' (Matrix.of (Y a)) := by
      ext h i
      simp [hLapply, Matrix.mulVec]
    rw [this, LinearMap.det_toLin', Pi.basisFun_det_apply]
  have hLind : ∀ a, LinearIndependent ℚ (L a) := fun a ↦
    (((Pi.basisFun ℚ ι).is_basis_iff_det).2 (isUnit_iff_ne_zero.2 (hYdet a))).1.map'
      (dotProductEquiv ℚ ι).toLinearMap (dotProductEquiv ℚ ι).ker
  -- the approximation domain of level `1` with all exponents `0`
  set Sfin : Finset (FinitePlace ℚ) := S.image FinitePlace.mk with hSfin
  set c0 : AbsoluteValue ℚ ℝ → ι → ℝ := fun _ _ ↦ 0 with hc0
  have hLFin : ∀ v ∈ Sfin, LinearIndependent ℚ (L v.1) := fun v _ ↦ hLind v.1
  set Λ := approxModule Sfin L c0 1 with hΛ
  set B := approxBody L c0 1 with hBdef
  have hDT : DiscreteTopology (approxLattice Sfin L c0 1) :=
    discreteTopology_approxLattice hLFin c0 one_ne_zero
  have : DiscreteTopology Λ.mixedImage := hDT
  have hZ : IsZLattice ℝ (approxLattice Sfin L c0 1) :=
    isZLattice_approxLattice hLFin c0 one_ne_zero
  have : IsZLattice ℝ Λ.mixedImage := hZ
  have hB₀ := convex_approxBody L c0 1
  have hB₁ : ∀ z ∈ B, -z ∈ B := fun z hz ↦ neg_mem_approxBody hz
  have hB₂ : (interior B).Nonempty :=
    ⟨0, mem_interior_iff_mem_nhds.2 (approxBody_mem_nhds_zero L c0 one_pos)⟩
  have hB₃ := isBounded_approxBody (fun w ↦ hLind w.1) c0 1
  obtain ⟨g, hgind, hg⟩ := exists_linearIndependent_mem_smul_successiveMinimum Λ hB₀ hB₁ hB₂ hB₃
    (isClosed_approxBody L c0 1)
  set μ := successiveMinimum Λ B with hμ
  have hμpos : ∀ k < n, 0 < μ k := fun k hk ↦ successiveMinimum_pos Λ hB₀ hB₁ hB₂ hB₃ hk
  have hμmono : ∀ i j, i ≤ j → j < n → μ i ≤ μ j := fun i j hij hj ↦
    successiveMinimum_le_of_le Λ hB₀ hB₁ hB₂ hB₃ hij hj
  -- the bounds on the minimal vectors
  set wI : InfinitePlace ℚ := default with hwI
  set YI := Y wI.1 with hYI
  have hginf : ∀ (k : Fin n) i, wI (YI i ⬝ᵥ g k) ≤ μ k := fun k i ↦ by
    have h := (mem_smul_approxBody_iff (hμpos k k.2)).1 (hg k).2 wI i
    rw [normAtPlace_sum_mixedEmbedding, hc0] at h
    simpa [hLapply] using h
  have hgfin : ∀ k, ∀ v ∈ Sfin, ∀ i, v (Y v.1 i ⬝ᵥ g k) ≤ 1 := fun k v hv i ↦ by
    have h := (hg k).1.1 v hv i
    simpa [hLapply, hc0] using h
  have hgout : ∀ k, ∀ v ∉ Sfin, ∀ j, v (g k j) ≤ 1 := fun k v hv j ↦ (hg k).1.2 v hv j
  have hupd : ∀ a i, ∀ x ∈ T, ∀ j, Function.update (Y a) i x j ∈ T := fun a i x hx j ↦ by
    rcases eq_or_ne j i with rfl | hji
    · simpa using hx
    · simpa [Function.update_of_ne hji] using hYT a j
  -- the values of the minimal vectors at the points of `T` are integers
  have hint : ∀ (k : Fin n), ∀ x ∈ T, ∃ z : ℤ, g k ⬝ᵥ x = z := fun k x hx ↦ by
    suffices h : ∃ z : ℤ, (z : ℚ) = g k ⬝ᵥ x by
      obtain ⟨z, hz⟩ := h
      exact ⟨z, hz.symm⟩
    refine Rat.exists_intCast_eq_of_forall_finitePlace_le_one fun v ↦ ?_
    by_cases hv : v ∈ Sfin
    · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hv
      set p : InfinitePlace ℚ ⊕ S := .inr ⟨P, hP⟩ with hp
      rw [dotProduct_eq_sum_det_update_div (hYdet (FinitePlace.mk P).1) x (g k)]
      refine FinitePlace.apply_sum_le_of_forall_le _ zero_le_one fun i _ ↦ ?_
      rw [map_mul]
      have hcoef : FinitePlace.mk P ((Pi.basisFun ℚ ι).det (Function.update
          (Y (FinitePlace.mk P).1) i x) / (Pi.basisFun ℚ ι).det (Y (FinitePlace.mk P).1)) ≤ 1 := by
        refine FinitePlace.apply_le_one_of_lt_two _ ?_
        rw [map_div₀, div_lt_iff₀ (FinitePlace.pos_iff.2 (hYdet _))]
        exact hgood p _ (hupd _ i x hx)
      have hdot : FinitePlace.mk P (g k ⬝ᵥ Y (FinitePlace.mk P).1 i) ≤ 1 := by
        rw [dotProduct_comm]; exact hgfin k _ hv i
      exact (mul_le_mul hcoef hdot (apply_nonneg _ _) zero_le_one).trans_eq (mul_one 1)
    · have hP : v.maximalIdeal ∉ S := fun h ↦
        hv (Finset.mem_image.2 ⟨_, h, FinitePlace.mk_maximalIdeal v⟩)
      have hx' : ∀ j, v (x j) ≤ 1 := fun j ↦ by
        rw [← FinitePlace.mk_maximalIdeal v]
        exact (FinitePlace.mk_le_one_iff _ _).2 (hT x hx j _ hP)
      rw [dotProduct]
      refine FinitePlace.apply_sum_le_of_forall_le _ zero_le_one fun j _ ↦ ?_
      rw [map_mul]
      exact (mul_le_mul (hgout k v hv j) (hx' j) (apply_nonneg _ _) zero_le_one).trans_eq
        (mul_one 1)
  -- and they are small
  have hsize : ∀ (k : Fin n), ∀ x ∈ T, wI (g k ⬝ᵥ x) ≤ 2 * n * μ k := fun k x hx ↦ by
    rw [dotProduct_eq_sum_det_update_div (hYdet wI.1) x (g k)]
    refine (AbsoluteValue.sum_le _ _ _).trans ?_
    calc ∑ i, wI ((Pi.basisFun ℚ ι).det (Function.update YI i x) / (Pi.basisFun ℚ ι).det YI *
          (g k ⬝ᵥ YI i)) ≤ ∑ _i : ι, 2 * μ k := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [map_mul]
          have hcoef : wI ((Pi.basisFun ℚ ι).det (Function.update YI i x) /
              (Pi.basisFun ℚ ι).det YI) ≤ 2 := by
            rw [map_div₀, div_le_iff₀ (wI.pos_iff.2 (hYdet _))]
            exact (hgood (.inl wI) _ (hupd _ i x hx)).le
          have hdot : wI (g k ⬝ᵥ YI i) ≤ μ k := by rw [dotProduct_comm]; exact hginf k i
          exact mul_le_mul hcoef hdot (apply_nonneg _ _) zero_le_two
      _ = 2 * n * μ k := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  -- the minima are at least `1`
  have hμ1 : 1 ≤ μ 0 := by
    set k0 : Fin n := ⟨0, by omega⟩
    have hg0 : g k0 ≠ 0 := hgind.ne_zero k0
    obtain ⟨i, hi⟩ : ∃ i, YI i ⬝ᵥ g k0 ≠ 0 := by
      by_contra h
      push Not at h
      apply hg0
      refine Matrix.eq_zero_of_mulVec_eq_zero (M := Matrix.of YI) ?_ (funext fun i ↦ h i)
      rw [← Pi.basisFun_det_apply]
      exact hYdet _
    obtain ⟨z, hz⟩ := hint k0 (YI i) (hYT _ i)
    rw [dotProduct_comm, hz] at hi
    have hz0 : z ≠ 0 := by exact_mod_cast hi
    have h1 := hginf k0 i
    rw [dotProduct_comm, hz, Rat.infinitePlace_apply] at h1
    have h2 : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz0
    push_cast at h1
    exact h2.trans h1
  -- the pigeonhole
  set μ' : ℕ → ℝ := fun k ↦ μ (min k (n - 1)) with hμ'
  have hμ'1 : ∀ k, 1 ≤ μ' k := fun k ↦ hμ1.trans (hμmono 0 _ (Nat.zero_le _) (by omega))
  have hμ'mono : ∀ i j, i ≤ j → μ' i ≤ μ' j := fun i j hij ↦ hμmono _ _ (by omega) (by omega)
  have hμ'eq : ∀ k < n, μ' k = μ k := fun k hk ↦ by
    simp only [hμ']
    rw [Nat.min_eq_left (by omega)]
  set φ : Fin n → Dual ℚ (ι → ℚ) := fun k ↦ dotProductEquiv ℚ ι (g k) with hφdef
  have hφ : LinearIndependent ℚ φ :=
    hgind.map' (dotProductEquiv ℚ ι).toLinearMap (dotProductEquiv ℚ ι).ker
  obtain ⟨U, hUcard, hUtop, hUcov⟩ := Module.Dual.exists_finset_submodule_of_forall_eq_intCast hn
    φ hφ hμ'1 hμ'mono (R := 2 * n) (by positivity) T fun x hx k ↦ by
      obtain ⟨z, hz⟩ := hint k x hx
      refine ⟨z, hz, ?_⟩
      rw [hμ'eq k k.2]
      have := hsize k x hx
      rw [hz, Rat.infinitePlace_apply] at this
      exact_mod_cast this
  refine ⟨U, hUcard.trans ?_, hUtop, hUcov⟩
  -- Minkowski's second theorem bounds the product of the minima by the determinants
  have hprod : ∏ k ∈ Finset.range n, μ k ≤ ∏ p, D p := by
    have hmink := prod_successiveMinimum_pow_mul_measure_le Λ MeasureTheory.volume hB₀ hB₁ hB₂ hB₃
    have hvol := volume_approxBody (fun w ↦ hLind w.1) c0 one_pos
    have hcov := covolume_approxLattice hLFin c0 one_pos
    have hr : InfinitePlace.nrRealPlaces ℚ = 1 :=
      InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ)
    have hcx : InfinitePlace.nrComplexPlaces ℚ = 0 :=
      InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ)
    have hmult : (default : InfinitePlace ℚ).mult = 1 :=
      InfinitePlace.mult_isReal ⟨default, Rat.isReal_infinitePlace⟩
    have hO : ZLattice.covolume (mixedEmbedding.integerLattice ℚ) = 1 := by
      rw [mixedEmbedding.covolume_integerLattice, hcx, discr_rat]
      simp
    have hfl : ∀ v : FinitePlace ℚ, v.floorValue 1 = 1 := fun v ↦ by
      simp [FinitePlace.floorValue]
    simp only [hc0, Real.rpow_zero, Finset.prod_const_one, mul_one, hr, hcx, one_mul,
      Fintype.prod_unique, hfl, inv_one, Finset.prod_const_one, hO, one_pow] at hvol hcov
    set a := wI (LinearMap.det (LinearMap.pi (L wI.1))) with ha
    have ha0 : 0 < a := wI.pos_iff.2 (LinearMap.det_pi_ne_zero (hLind _))
    have hV : (MeasureTheory.volume B).toReal = 2 ^ n * a⁻¹ := by
      change (MeasureTheory.volume (approxBody L (fun _ _ ↦ 0) 1)).toReal = _
      rw [hvol, hmult, pow_one, zero_mul, pow_zero, mul_one, ENNReal.toReal_ofReal (by positivity)]
    have hC : ZLattice.covolume Λ.mixedImage MeasureTheory.volume =
        ∏ v ∈ Sfin, v (LinearMap.det (LinearMap.pi (L v.1))) := hcov
    rw [Module.finrank_self, pow_one, one_mul, hV, hC] at hmink
    set F := ∏ v ∈ Sfin, v (LinearMap.det (LinearMap.pi (L v.1))) with hF
    have hPF : ∏ k ∈ Finset.range n, μ k ≤ a * F := by
      have h2 : (0 : ℝ) < 2 ^ n := by positivity
      have key : (∏ k ∈ Finset.range n, μ k) * (2 ^ n * a⁻¹) ≤ 2 ^ n * F := hmink
      have : (∏ k ∈ Finset.range n, μ k) * a⁻¹ ≤ F := by
        rw [mul_left_comm] at key
        exact le_of_mul_le_mul_left key h2
      rwa [mul_inv_le_iff₀ ha0, mul_comm] at this
    have haD : a ≤ D (.inl wI) := by
      rw [ha, hLdet]
      exact hD _ (hYT _) (.inl wI)
    have hFD : F ≤ ∏ P : S, D (.inr P) := by
      rw [hF, hSfin, Finset.prod_image fun P _ Q _ h ↦ FinitePlace.mk_eq_iff.1 h,
        ← Finset.prod_coe_sort S]
      refine Finset.prod_le_prod₀ (fun P _ ↦ apply_nonneg _ _) fun P _ ↦ ?_
      rw [hLdet]
      exact hD _ (hYT _) (.inr P)
    have hD0 : ∀ p, 0 ≤ D p := fun p ↦ (apply_nonneg _ _).trans (hD y₀ hy₀T p)
    rw [Fintype.prod_sum_type, Fintype.prod_unique]
    exact hPF.trans (mul_le_mul haD hFD (Finset.prod_nonneg fun v _ ↦ apply_nonneg _ _)
      (hD0 _))
  have hc' : 2 * (2 * (n : ℝ)) * n + 2 = c := by rw [hc]; ring
  have hprod' : ∏ k ∈ Finset.range n, μ' k = ∏ k ∈ Finset.range n, μ k :=
    Finset.prod_congr rfl fun k hk ↦ hμ'eq k (Finset.mem_range.1 hk)
  have hP0 : 0 ≤ ∏ k ∈ Finset.range n, μ k :=
    Finset.prod_nonneg fun k hk ↦ (hμpos k (Finset.mem_range.1 hk)).le
  rw [hc', hprod', Real.mul_rpow (by linarith) hP0]
  have h1 : c ^ e ≤ c := by
    conv_rhs => rw [← Real.rpow_one c]
    exact Real.rpow_le_rpow_of_exponent_le hc1 he1
  have h2 : (∏ k ∈ Finset.range n, μ k) ^ e ≤ max 1 (∏ p, D p) ^ e :=
    Real.rpow_le_rpow hP0 (hprod.trans (le_max_right _ _)) he0
  calc 3 ^ n * c * (c ^ e * (∏ k ∈ Finset.range n, μ k) ^ e)
      ≤ 3 ^ n * c * (c * max 1 (∏ p, D p) ^ e) := by
        gcongr
    _ = 3 ^ n * c ^ 2 * max 1 (∏ p, D p) ^ e := by ring

private theorem four_mul_sq_add_two_le (n : ℕ) (hn : 2 ≤ n) : 4 * n ^ 2 + 2 ≤ 5 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ 5 m]; nlinarith [ih, hm]

open scoped Classical in
/-- **Evertse's Lemma 4.5 over `ℚ`, with his constant**: the points lie in at most
`100 ^ n max (1, ∏ D p) ^ (1 / (n - 1))` proper subspaces. -/
theorem _root_.Rat.exists_finset_submodule_of_det_le_hundred_pow
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hn : 2 ≤ Fintype.card ι) {T : Set (ι → ℚ)}
    (hT : ∀ x ∈ T, ∀ j, x j ∈ (S : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)
    (D : InfinitePlace ℚ ⊕ S → ℝ)
    (hD : ∀ y : ι → ι → ℚ, (∀ j, y j ∈ T) → ∀ p,
      systemPlace S p ((Pi.basisFun ℚ ι).det y) ≤ D p) :
    ∃ U : Finset (Submodule ℚ (ι → ℚ)),
      (U.card : ℝ) ≤ 100 ^ Fintype.card ι *
        max 1 (∏ p, D p) ^ (((Fintype.card ι - 1 : ℕ) : ℝ)⁻¹) ∧
      (∀ W ∈ U, W ≠ ⊤) ∧ ∀ x ∈ T, ∃ W ∈ U, x ∈ W := by
  obtain ⟨U, hU, hUtop, hUcov⟩ := Rat.exists_finset_submodule_of_det_le S hn hT D hD
  refine ⟨U, hU.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)),
    hUtop, hUcov⟩
  set n := Fintype.card ι
  have h5 : (4 * (n : ℝ) ^ 2 + 2) ≤ 5 ^ n := by exact_mod_cast four_mul_sq_add_two_le n hn
  calc (3 : ℝ) ^ n * (4 * n ^ 2 + 2) ^ 2 ≤ 3 ^ n * (5 ^ n) ^ 2 := by gcongr
    _ = 75 ^ n := by rw [← pow_mul, mul_comm n 2, pow_mul, ← mul_pow]; norm_num
    _ ≤ 100 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) _

open scoped Classical in
/-- **Evertse's Lemma 4.4** (Lemma 5 of Evertse, *On the norm form inequality `|F(x)| ≤ h`*): a
set of integral points of `ℚⁿ`, `n ≥ 2`, any `n` of which have determinant at most `D` in absolute
value, lies in at most `100 ^ n max (1, D) ^ (1 / (n - 1))` proper subspaces. -/
theorem _root_.Rat.exists_finset_submodule_of_abs_det_le (hn : 2 ≤ Fintype.card ι)
    {T : Set (ι → ℚ)} (hT : ∀ x ∈ T, ∀ j, ∃ z : ℤ, x j = z) {D : ℝ}
    (hD : ∀ y : ι → ι → ℚ, (∀ j, y j ∈ T) → |((Pi.basisFun ℚ ι).det y : ℝ)| ≤ D) :
    ∃ U : Finset (Submodule ℚ (ι → ℚ)),
      (U.card : ℝ) ≤ 100 ^ Fintype.card ι * max 1 D ^ (((Fintype.card ι - 1 : ℕ) : ℝ)⁻¹) ∧
      (∀ W ∈ U, W ≠ ⊤) ∧ ∀ x ∈ T, ∃ W ∈ U, x ∈ W := by
  have hT' : ∀ x ∈ T, ∀ j, x j ∈ ((∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) :
      Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ := fun x hx j ↦ by
    obtain ⟨z, hz⟩ := hT x hx j
    rw [hz]
    exact intCast_mem _ z
  have hprod : ∏ p : InfinitePlace ℚ ⊕ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))),
      Sum.elim (fun _ ↦ D) (fun _ ↦ 1) p = D := by
    rw [Fintype.prod_sum_type, Fintype.prod_unique]
    simp
  obtain ⟨U, hU, hUtop, hUcov⟩ := Rat.exists_finset_submodule_of_det_le_hundred_pow ∅ hn hT'
    (Sum.elim (fun _ ↦ D) (fun _ ↦ 1)) fun y hy p ↦ by
      rcases p with v | ⟨v, hv⟩
      · change v _ ≤ D
        rw [Rat.infinitePlace_apply]
        exact_mod_cast hD y hy
      · exact absurd hv (Finset.notMem_empty v)
  exact ⟨U, hprod ▸ hU, hUtop, hUcov⟩

end NumberField
