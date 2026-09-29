/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Evertse1984.PowerSumTools
public import Evertse1984.ShiftedPolynomials

-- Used only inside proofs.
import DiophantineApproximation.DecomposableForm
import DiophantineApproximation.NormForm
import DiophantineApproximation.SIntegerSquares
import DiophantineApproximation.UnitEquation
import Evertse1984.Normalization
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Evertse's Theorem 3: prime divisors of `u_r / u_s`

**Theorem 3** (Evertse 1984, p. 229). Let `u_k = ∑_{i=1}^m f_i(k) α_i ^ k` be a non-degenerate
linear recurrence in `K` with at least two characteristic roots. Then `P_K(u_r / u_s) → ∞` as
`r → ∞`, `r > s`, `u_s ≠ 0`, where `P_K(α)` is the largest norm of a prime ideal at which `α` has
nonzero order (`P_K(0) = 0`).

Equivalently, for every finite set `S` of primes only finitely many pairs `r > s ≥ 0` have
`u_s ≠ 0` and `u_r / u_s` an `S`-unit or zero. This file proves it
(`NumberField.finite_setOf_powerSum_div_mem_unit_of_splits`) for generalized power sums with
characteristic roots `α_i ∈ K` and polynomials `f_i` that split over `K`. Evertse reduces to that
case by a finite extension ("no restriction"); that passage is `Evertse1984.GeneralRoots`.

The proof is Evertse's. From `ζ u_r - β u_s = 0` (with `ζ` an `S`-unit and `β ∈ {0, 1}`), the
`2m` terms `ζ f_i(r) α_i ^ r`, `-β f_i(s) α_i ^ s` split into minimal vanishing subsums.

* *Step A.* A block containing two terms `ζ f_i(r) α_i ^ r`, `ζ f_j(r) α_j ^ r` happens only
  finitely often: its height is at least `H(α_i / α_j) ^ r / (C r ^ N)` by Kronecker, while its
  product over `S∞ ∪ S` is polynomial in `r`. So Theorem 1 gives finitely many points, each of
  which fixes the ratio, and then `H(α_i / α_j) ^ r` is polynomial in `r`.
* *Otherwise* the blocks are pairs, `ζ f_i(r) α_i ^ r = f_{σ i}(s) α_{σ i} ^ s` for a permutation
  `σ`. For `σ = 1`, `H(α_i / α_j) ^ (r - s)` is polynomial in `r`, so `r - s = O(log r)`, and
  Lemma 2 applies to a nonconstant `f_i`. For `σ ≠ 1`, along a cycle of `σ` the relations
  telescope (`mul_le_two_mul_of_telescope`) to `r · log H(α_i / α_{σ i}) = O(log r)`.

## Main definitions

* `NumberField.powerSum`: `k ↦ ∑_i f_i(k) α_i ^ k`.

## Main results

* `NumberField.finite_setOf_powerSum_div_mem_unit_of_splits`: **Theorem 3**.
* `NumberField.exists_powerSum_ne_zero`: `u` has a nonzero term.

## References

J.-H. Evertse, *On sums of `S`-units and linear recurrences*, Compositio Math. **53** (1984),
225–244, Theorem 3 and §4.
-/

@[expose] public section

open IsDedekindDomain Height Module Polynomial

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **A generalized power sum** `k ↦ ∑_i f_i(k) α_i ^ k`. -/
noncomputable def powerSum {ι : Type*} [Fintype ι] (α : ι → K) (f : ι → K[X]) (k : ℕ) : K :=
  ∑ i, (f i).eval (k : K) * α i ^ k

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The pairs of Theorem 3: `r > s`, `u_s ≠ 0`, and `u_r / u_s` zero or an `S`-unit. -/
def powerSumPairs {ι : Type*} [Fintype ι] (α : ι → K) (f : ι → K[X]) : Set (ℕ × ℕ) :=
  {p | p.2 < p.1 ∧ powerSum α f p.2 ≠ 0 ∧ (powerSum α f p.1 = 0 ∨
    ∃ w : Kˣ, w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧
      (w : K) = powerSum α f p.1 / powerSum α f p.2)}

/-- **Scaling by an `S`-unit leaves the product over `S∞ ∪ S` unchanged.** -/
theorem placeProd_univ_unit_mul {w : Kˣ} (hw : w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (y : K) : placeProd S Set.univ (fun v ↦ v ((w : K) * y)) =
      placeProd S Set.univ (fun v ↦ v y) := by
  simp only [map_mul]
  rw [placeProd_mul, placeProd_univ_eq_one_of_mem_unit S hw, one_mul]

/-- The product over the places of `T` of a power. -/
theorem placeProd_pow (T : Set (AbsoluteValue K ℝ)) (y : K) (n : ℕ) :
    placeProd S T (fun v ↦ v (y ^ n)) = placeProd S T (fun v ↦ v y) ^ n := by
  induction n with
  | zero => simp [placeProd]
  | succ n ih =>
    simp only [pow_succ, map_mul]
    rw [placeProd_mul, ih]

/-- **Values at natural numbers of a polynomial with `S`-integral coefficients are
`S`-integers.** -/
theorem eval_natCast_mem_integer {g : K[X]}
    (hg : ∀ n, g.coeff n ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) (t : ℕ) :
    g.eval (t : K) ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K := by
  rw [eval_eq_sum_range]
  exact sum_mem fun n _ ↦ mul_mem (hg n) (pow_mem (natCast_mem _ t) n)

/-- **The heights of the values of finitely many polynomials are polynomial**: there are
`C ≥ 1` and `N` with `H(f_i(t)) ≤ C r ^ N` whenever `t ≤ r` and `r ≥ 1`. -/
theorem exists_forall_mulHeight₁_eval_le {ι : Type*} [Finite ι] (f : ι → K[X]) :
    ∃ C ≥ (1 : ℝ), ∃ N : ℕ, ∀ i (t r : ℕ), t ≤ r → 1 ≤ r →
      mulHeight₁ ((f i).eval (t : K)) ≤ C * (r : ℝ) ^ N := by
  have := Fintype.ofFinite ι
  choose C hC h using fun i ↦ (f i).exists_pos_forall_mulHeight₁_eval_le (K := K)
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ ↦ (hC i).le
  refine ⟨1 + ∑ i, C i, by linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦
    (hC i).le], finrank ℚ K * ∑ i, (f i).natDegree, fun i t r htr hr ↦ ?_⟩
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ht : max |((t : ℤ) : ℝ)| 1 ≤ r := by
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg t)]
    exact max_le (by exact_mod_cast htr) hr1
  calc mulHeight₁ ((f i).eval (t : K))
      ≤ C i * mulHeight₁ (t : K) ^ (f i).natDegree := h i _
    _ = C i * max |((t : ℤ) : ℝ)| 1 ^ (finrank ℚ K * (f i).natDegree) := by
        rw [show (t : K) = ((t : ℤ) : K) by push_cast; rfl, mulHeight₁_intCast, pow_mul]
    _ ≤ C i * (r : ℝ) ^ (finrank ℚ K * (f i).natDegree) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ht _) (hC i).le
    _ ≤ (1 + ∑ i, C i) * (r : ℝ) ^ (finrank ℚ K * ∑ i, (f i).natDegree) := by
        refine mul_le_mul ?_ (pow_le_pow_right₀ hr1 (Nat.mul_le_mul_left _
          (Finset.single_le_sum (f := fun i ↦ (f i).natDegree) (fun _ _ ↦ Nat.zero_le _)
            (Finset.mem_univ i)))) (by positivity) (by linarith)
        have := Finset.single_le_sum (f := C) (fun i _ ↦ (hC i).le) (Finset.mem_univ i)
        linarith

section Pairs

variable {ι : Type*} [Fintype ι] (α : ι → K) (f : ι → K[X])

open scoped Classical in
/-- The `S`-unit `ζ` of `ζ u_r - β u_s = 0`: `u_s / u_r`, or `1` when `u_r = 0`. -/
noncomputable def pairZeta (p : ℕ × ℕ) : K :=
  if powerSum α f p.1 = 0 then 1 else powerSum α f p.2 / powerSum α f p.1

open scoped Classical in
/-- The coefficient `β` of `ζ u_r - β u_s = 0`: `1`, or `0` when `u_r = 0`. -/
noncomputable def pairBeta (p : ℕ × ℕ) : K :=
  if powerSum α f p.1 = 0 then 0 else 1

/-- The `2m` terms of `ζ u_r - β u_s = 0`. -/
noncomputable def pairTerms (p : ℕ × ℕ) : ι ⊕ ι → K :=
  Sum.elim (fun i ↦ pairZeta α f p * ((f i).eval (p.1 : K) * α i ^ p.1))
    (fun i ↦ -(pairBeta α f p * ((f i).eval (p.2 : K) * α i ^ p.2)))

variable {S α f}

/-- `ζ` is an `S`-unit. -/
theorem exists_unit_eq_pairZeta {p : ℕ × ℕ} (hp : p ∈ powerSumPairs S α f) :
    ∃ w : Kˣ, w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧ (w : K) = pairZeta α f p := by
  unfold pairZeta
  split_ifs with h
  · exact ⟨1, one_mem _, rfl⟩
  · obtain ⟨-, -, h0 | ⟨w, hw, hwe⟩⟩ := hp
    · exact absurd h0 h
    · exact ⟨w⁻¹, inv_mem hw, by rw [Units.val_inv_eq_inv_val, hwe, inv_div]⟩

theorem pairZeta_ne_zero {p : ℕ × ℕ} (hp : p ∈ powerSumPairs S α f) : pairZeta α f p ≠ 0 := by
  obtain ⟨w, -, hw⟩ := exists_unit_eq_pairZeta hp
  rw [← hw]; exact Units.ne_zero w

omit [NumberField K] in
/-- **The terms sum to zero.** -/
theorem sum_pairTerms (p : ℕ × ℕ) : ∑ a, pairTerms α f p a = 0 := by
  simp only [pairTerms, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_neg_distrib,
    ← Finset.mul_sum]
  change pairZeta α f p * powerSum α f p.1 + -(pairBeta α f p * powerSum α f p.2) = 0
  unfold pairZeta pairBeta
  split_ifs with h
  · rw [h]; ring
  · rw [div_mul_cancel₀ _ h]; ring

/-- **The terms are `S`-integers**, when the `α_i` are `S`-units and the coefficients of the
`f_i` are `S`-integers. -/
theorem pairTerms_mem_integer
    (hαS : ∀ i, ∃ w : Kˣ, w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧ (w : K) = α i)
    (hcS : ∀ i n, (f i).coeff n ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K)
    {p : ℕ × ℕ} (hp : p ∈ powerSumPairs S α f) (a : ι ⊕ ι) :
    pairTerms α f p a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K := by
  have hαI : ∀ i, α i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K := fun i ↦ by
    obtain ⟨w, hw, hwe⟩ := hαS i
    rw [← hwe]; exact Set.mem_integer_of_mem_unit hw
  rcases a with i | i
  · obtain ⟨w, hw, hwe⟩ := exists_unit_eq_pairZeta hp
    refine mul_mem (hwe ▸ Set.mem_integer_of_mem_unit hw) (mul_mem ?_ (pow_mem (hαI i) _))
    exact eval_natCast_mem_integer S (hcS i) _
  · refine neg_mem (mul_mem ?_ (mul_mem (eval_natCast_mem_integer S (hcS i) _)
      (pow_mem (hαI i) _)))
    unfold pairBeta
    split_ifs
    · exact zero_mem _
    · exact one_mem _

/-- **The size of a term over `S∞ ∪ S`** is at most the height of the polynomial value in it. -/
theorem placeProd_pairTerms_le
    (hαS : ∀ i, ∃ w : Kˣ, w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧ (w : K) = α i)
    {p : ℕ × ℕ} (hp : p ∈ powerSumPairs S α f) {C : ℝ} (hC : 1 ≤ C)
    (hH : ∀ i, mulHeight₁ ((f i).eval (p.1 : K)) ≤ C ∧ mulHeight₁ ((f i).eval (p.2 : K)) ≤ C)
    (a : ι ⊕ ι) : placeProd S Set.univ (fun v ↦ v (pairTerms α f p a)) ≤ C := by
  obtain ⟨z, hz, hze⟩ := exists_unit_eq_pairZeta hp
  rcases a with i | i
  · obtain ⟨w, hw, hwe⟩ := hαS i
    have heq : pairTerms α f p (Sum.inl i) = ((z * w ^ p.1 : Kˣ) : K) * (f i).eval (p.1 : K) := by
      simp only [pairTerms, Sum.elim_inl, Units.val_mul, Units.val_pow_eq_pow_val, hze, hwe]
      ring
    rw [heq, placeProd_univ_unit_mul S (mul_mem hz (pow_mem hw _))]
    exact (placeProd_le_mulHeight₁ S _ _).trans (hH i).1
  · obtain ⟨w, hw, hwe⟩ := hαS i
    have hneg : placeProd S Set.univ (fun v ↦ v (pairTerms α f p (Sum.inr i))) =
        placeProd S Set.univ (fun v ↦ v (pairBeta α f p * ((f i).eval (p.2 : K) * α i ^ p.2))) :=
      placeProd_congr S _ fun v _ ↦ by
        simp only [pairTerms, Sum.elim_inr]; exact AbsoluteValue.map_neg v _
    rw [hneg]
    unfold pairBeta
    split_ifs
    · rw [zero_mul]
      exact (placeProd_le_mulHeight₁ S _ _).trans (by rw [mulHeight₁_zero]; exact hC)
    · have heq : (1 : K) * ((f i).eval (p.2 : K) * α i ^ p.2) =
          ((w ^ p.2 : Kˣ) : K) * (f i).eval (p.2 : K) := by
        simp only [Units.val_pow_eq_pow_val, hwe]; ring
      rw [heq, placeProd_univ_unit_mul S (pow_mem hw _)]
      exact (placeProd_le_mulHeight₁ S _ _).trans (hH i).2

/-- Finitely many pairs once `r` is bounded. -/
theorem finite_of_forall_fst_lt {W : Set (ℕ × ℕ)} (B : ℕ) (hW : ∀ p ∈ W, p.2 < p.1 ∧ p.1 < B) :
    W.Finite :=
  ((Set.finite_Iio B).prod (Set.finite_Iio B)).subset fun p hp ↦
    ⟨(hW p hp).2, ((hW p hp).1.trans (hW p hp).2)⟩

open scoped Classical in
/-- **Step A of Theorem 3.** A minimal vanishing subsum containing two of the terms
`ζ f_i(r) α_i ^ r`, `ζ f_j(r) α_j ^ r` occurs for only finitely many pairs. -/
theorem finite_setOf_pair_mem_block (hα0 : ∀ i, α i ≠ 0)
    (hnd : ∀ i j, i ≠ j → ∀ n : ℕ, 0 < n → (α i / α j) ^ n ≠ 1)
    (hαS : ∀ i, ∃ w : Kˣ, w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧ (w : K) = α i)
    (hcS : ∀ i n, (f i).coeff n ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K)
    {i j : ι} (hij : i ≠ j) (J : Finset (ι ⊕ ι)) (hi : Sum.inl i ∈ J) (hj : Sum.inl j ∈ J) :
    {p | p ∈ powerSumPairs S α f ∧ (∀ k, (f k).eval (p.1 : K) ≠ 0) ∧
      ∑ a ∈ J, pairTerms α f p a = 0 ∧
      ∀ I ⊆ J, I.Nonempty → I ≠ J → ∑ a ∈ I, pairTerms α f p a ≠ 0}.Finite := by
  obtain ⟨C, hC1, N, hCN⟩ := exists_forall_mulHeight₁_eval_le (K := K) f
  set θ := α i / α j with hθdef
  have hθ0 : θ ≠ 0 := div_ne_zero (hα0 i) (hα0 j)
  have hθ : 1 < mulHeight₁ θ := one_lt_mulHeight₁ hθ0 (hnd i j hij)
  set m₂ := Fintype.card (ι ⊕ ι)
  obtain ⟨R₁, hR₁⟩ := exists_forall_mul_pow_lt_pow hθ (C ^ (2 * m₂ + 2)) (N * (2 * m₂ + 2))
  have hF := finite_setOf_admissible_sum_eq_zero S J (c := 1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  set F := {X : Projectivization K (J → K) | ∃ (x : J → K) (hx : x ≠ 0),
      Projectivization.mk K x hx = X ∧
      (∀ a, x a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
      ∏ a, placeProd S Set.univ (fun v ↦ v (x a)) ≤ 1 * mulHeight x ^ (1 / 2 : ℝ) ∧
      ∑ a, x a = 0 ∧ ∀ I : Finset J, I.Nonempty → I ≠ Finset.univ → ∑ a ∈ I, x a ≠ 0}
    with hFdef
  obtain ⟨Q, hQ⟩ := ((hF.image fun Z : Projectivization K (J → K) ↦
    Z.rep ⟨_, hi⟩ / Z.rep ⟨_, hj⟩).image fun q : K ↦ mulHeight₁ q).bddAbove
  obtain ⟨R₂, hR₂⟩ := exists_forall_mul_pow_lt_pow hθ (max Q 1 * C ^ 2) (2 * N)
  refine finite_of_forall_fst_lt (max (max R₁ R₂) 1) fun p ⟨hp, hnz, hJ0, hJmin⟩ ↦
    ⟨hp.1, ?_⟩
  by_contra hcon
  push Not at hcon
  have hr1 : 1 ≤ p.1 := (le_max_right _ _).trans hcon
  have hrR₁ : R₁ ≤ p.1 := (le_max_left _ _).trans ((le_max_left _ _).trans hcon)
  have hrR₂ : R₂ ≤ p.1 := (le_max_right _ _).trans ((le_max_left _ _).trans hcon)
  have hr1' : (1 : ℝ) ≤ p.1 := by exact_mod_cast hr1
  have hH : ∀ k, mulHeight₁ ((f k).eval (p.1 : K)) ≤ C * (p.1 : ℝ) ^ N ∧
      mulHeight₁ ((f k).eval (p.2 : K)) ≤ C * (p.1 : ℝ) ^ N :=
    fun k ↦ ⟨hCN k _ _ le_rfl hr1, hCN k _ _ hp.1.le hr1⟩
  have hCr : 1 ≤ C * (p.1 : ℝ) ^ N := one_le_mul_of_one_le_of_one_le hC1 (one_le_pow₀ hr1')
  -- the point
  set x : J → K := fun a ↦ pairTerms α f p a with hx
  have hz0 := pairZeta_ne_zero hp
  have hxi : x ⟨_, hi⟩ ≠ 0 := by
    simp only [hx, pairTerms, Sum.elim_inl]
    exact mul_ne_zero hz0 (mul_ne_zero (hnz i) (pow_ne_zero _ (hα0 i)))
  have hxj : x ⟨_, hj⟩ ≠ 0 := by
    simp only [hx, pairTerms, Sum.elim_inl]
    exact mul_ne_zero hz0 (mul_ne_zero (hnz j) (pow_ne_zero _ (hα0 j)))
  have hx0 : x ≠ 0 := fun h ↦ hxi (congrFun h _)
  have hratio : x ⟨_, hi⟩ / x ⟨_, hj⟩ =
      θ ^ p.1 * ((f i).eval (p.1 : K) / (f j).eval (p.1 : K)) := by
    simp only [hx, pairTerms, Sum.elim_inl, hθdef, div_pow]
    field_simp [hα0 j, hnz j]
  have hq : mulHeight₁ ((f i).eval (p.1 : K) / (f j).eval (p.1 : K)) ≤
      C ^ 2 * (p.1 : ℝ) ^ (2 * N) := by
    refine (mulHeight₁_div_le _ _).trans ?_
    calc _ ≤ (C * (p.1 : ℝ) ^ N) * (C * (p.1 : ℝ) ^ N) :=
          mul_le_mul (hH i).1 (hH j).1 (mulHeight₁_pos _).le (by positivity)
      _ = C ^ 2 * (p.1 : ℝ) ^ (2 * N) := by ring
  have hlow : mulHeight₁ θ ^ p.1 / (C ^ 2 * (p.1 : ℝ) ^ (2 * N)) ≤ mulHeight x := by
    refine le_trans ?_ ((div_le_mulHeight₁_mul (div_ne_zero (hnz i) (hnz j))).trans
      (hratio ▸ mulHeight₁_div_le_mulHeight x ⟨_, hi⟩ ⟨_, hj⟩))
    rw [mulHeight₁_pow]
    exact div_le_div_of_nonneg_left (by positivity) (mulHeight₁_pos _) hq
  -- admissibility
  have hadm : ∏ a, placeProd S Set.univ (fun v ↦ v (x a)) ≤ 1 * mulHeight x ^ (1 / 2 : ℝ) := by
    have hprod : ∏ a, placeProd S Set.univ (fun v ↦ v (x a)) ≤ (C * (p.1 : ℝ) ^ N) ^ m₂ := by
      calc _ ≤ ∏ _a : J, C * (p.1 : ℝ) ^ N :=
            Finset.prod_le_prod₀ (fun a _ ↦ placeProd_nonneg S _ fun v _ ↦ apply_nonneg _ _)
              fun a _ ↦ placeProd_pairTerms_le hαS hp hCr hH a
        _ = (C * (p.1 : ℝ) ^ N) ^ J.card := by rw [Finset.prod_const, Finset.card_univ,
              Fintype.card_coe]
        _ ≤ (C * (p.1 : ℝ) ^ N) ^ m₂ := pow_le_pow_right₀ hCr (Finset.card_le_univ J)
    refine hprod.trans ?_
    rw [one_mul, ← Real.sqrt_eq_rpow, Real.le_sqrt (by positivity) (by positivity)]
    have h1 := hR₁ p.1 hrR₁
    refine le_trans ?_ hlow
    rw [le_div_iff₀ (by positivity)]
    calc ((C * (p.1 : ℝ) ^ N) ^ m₂) ^ 2 * (C ^ 2 * (p.1 : ℝ) ^ (2 * N))
        = C ^ (2 * m₂ + 2) * (p.1 : ℝ) ^ (N * (2 * m₂ + 2)) := by ring
      _ ≤ mulHeight₁ θ ^ p.1 := h1.le
  -- the point is one of finitely many
  have hsum : ∑ a, x a = 0 := by rw [hx, Finset.sum_coe_sort J (pairTerms α f p)]; exact hJ0
  have hnv : ∀ I : Finset J, I.Nonempty → I ≠ Finset.univ → ∑ a ∈ I, x a ≠ 0 := by
    intro I hI hIu
    have hmap : ∑ a ∈ I, x a = ∑ b ∈ I.map (Function.Embedding.subtype _), pairTerms α f p b := by
      rw [Finset.sum_map]; rfl
    rw [hmap]
    refine hJmin _ (fun b hb ↦ ?_) hI.map fun hIJ ↦ hIu ?_
    · obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hb; exact a.2
    · refine Finset.eq_univ_of_forall fun a ↦ ?_
      have : a.1 ∈ I.map (Function.Embedding.subtype _) := by rw [hIJ]; exact a.2
      obtain ⟨a', ha', h'⟩ := Finset.mem_map.mp this
      rwa [show a = a' from Subtype.ext h'.symm]
  have hmem : Projectivization.mk K x hx0 ∈ F :=
    ⟨x, hx0, rfl, fun a ↦ pairTerms_mem_integer hαS hcS hp a, hadm, hsum, hnv⟩
  have hQr : mulHeight₁ (x ⟨_, hi⟩ / x ⟨_, hj⟩) ≤ Q := by
    refine hQ ⟨_, ⟨_, hmem, ?_⟩, rfl⟩
    obtain ⟨u, hu⟩ := (Projectivization.mk_eq_mk_iff K _ _ (Projectivization.rep_nonzero _)
      hx0).mp (Projectivization.mk_rep (Projectivization.mk K x hx0))
    change (Projectivization.mk K x hx0).rep ⟨_, hi⟩ / (Projectivization.mk K x hx0).rep ⟨_, hj⟩
      = _
    rw [← hu, Pi.smul_apply, Pi.smul_apply, Units.smul_def, Units.smul_def, smul_eq_mul,
      smul_eq_mul]
    exact mul_div_mul_left _ _ (Units.ne_zero u)
  -- the ratio bounds `r`
  have hθr : θ ^ p.1 = x ⟨_, hi⟩ / x ⟨_, hj⟩ * ((f j).eval (p.1 : K) / (f i).eval (p.1 : K)) := by
    rw [hratio]; field_simp [hnz i, hnz j]
  have hup : mulHeight₁ θ ^ p.1 ≤ max Q 1 * C ^ 2 * (p.1 : ℝ) ^ (2 * N) := by
    rw [← mulHeight₁_pow, hθr]
    refine (mulHeight₁_mul_le _ _).trans ?_
    have hq' : mulHeight₁ ((f j).eval (p.1 : K) / (f i).eval (p.1 : K)) ≤
        C ^ 2 * (p.1 : ℝ) ^ (2 * N) := by
      refine (mulHeight₁_div_le _ _).trans ?_
      calc _ ≤ (C * (p.1 : ℝ) ^ N) * (C * (p.1 : ℝ) ^ N) :=
            mul_le_mul (hH j).1 (hH i).1 (mulHeight₁_pos _).le (by positivity)
        _ = C ^ 2 * (p.1 : ℝ) ^ (2 * N) := by ring
    calc _ ≤ max Q 1 * (C ^ 2 * (p.1 : ℝ) ^ (2 * N)) :=
          mul_le_mul (hQr.trans (le_max_left _ _)) hq' (mulHeight₁_pos _).le (by positivity)
      _ = _ := by ring
  exact (hR₂ p.1 hrR₂).not_ge hup

/-- **The pair equation**: a vanishing pair `ζ f_i(r) α_i ^ r - β f_j(s) α_j ^ s` with
`f_i(r) ≠ 0` has `β = 1`. -/
theorem pairZeta_mul_eq {p : ℕ × ℕ} (hp : p ∈ powerSumPairs S α f) (hα0 : ∀ i, α i ≠ 0)
    {i j : ι} (hi : (f i).eval (p.1 : K) ≠ 0)
    (h : pairTerms α f p (Sum.inl i) + pairTerms α f p (Sum.inr j) = 0) :
    pairZeta α f p * ((f i).eval (p.1 : K) * α i ^ p.1) = (f j).eval (p.2 : K) * α j ^ p.2 := by
  have hz := pairZeta_ne_zero hp
  simp only [pairTerms, Sum.elim_inl, Sum.elim_inr] at h
  unfold pairBeta at h
  split_ifs at h with hb
  · rw [zero_mul, neg_zero, add_zero] at h
    exact absurd h (mul_ne_zero hz (mul_ne_zero hi (pow_ne_zero _ (hα0 i))))
  · linear_combination h

/-- **Case 1 of Theorem 3** (`σ = 1`): if every term `ζ f_i(r) α_i ^ r` cancels against
`f_i(s) α_i ^ s`, then `H(α_i / α_j) ^ (r - s)` is polynomial in `r`, so `r - s = O(log r)`, and
Lemma 2 applied to a nonconstant `f_i` leaves finitely many pairs. -/
theorem finite_setOf_pairTerms_refl [Nontrivial ι] (hα0 : ∀ i, α i ≠ 0)
    (hnd : ∀ i j, i ≠ j → ∀ n : ℕ, 0 < n → (α i / α j) ^ n ≠ 1)
    (hαS : ∀ i, ∃ w : Kˣ, w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧ (w : K) = α i)
    (hfs : ∀ i, (f i).Splits) :
    {p | p ∈ powerSumPairs S α f ∧ (∀ k, (f k).eval (p.1 : K) ≠ 0) ∧
      ∀ k, pairTerms α f p (Sum.inl k) + pairTerms α f p (Sum.inr k) = 0}.Finite := by
  -- the equation for two indices
  have hkey : ∀ p ∈ powerSumPairs S α f, (∀ k, (f k).eval (p.1 : K) ≠ 0) →
      (∀ k, pairTerms α f p (Sum.inl k) + pairTerms α f p (Sum.inr k) = 0) →
      ∀ i j, (α i / α j) ^ p.1 * ((f i).eval (p.1 : K) / (f j).eval (p.1 : K)) =
        (α i / α j) ^ p.2 * ((f i).eval (p.2 : K) / (f j).eval (p.2 : K)) := by
    intro p hp hnz hk i j
    have hi := pairZeta_mul_eq hp hα0 (hnz i) (hk i)
    have hj := pairZeta_mul_eq hp hα0 (hnz j) (hk j)
    have hz := pairZeta_ne_zero hp
    have hjs : (f j).eval (p.2 : K) ≠ 0 := fun h0 ↦ by
      rw [h0, zero_mul] at hj
      exact mul_ne_zero hz (mul_ne_zero (hnz j) (pow_ne_zero _ (hα0 j))) hj
    have hzi : pairZeta α f p * ((f j).eval (p.1 : K) * α j ^ p.1) ≠ 0 :=
      mul_ne_zero hz (mul_ne_zero (hnz j) (pow_ne_zero _ (hα0 j)))
    calc (α i / α j) ^ p.1 * ((f i).eval (p.1 : K) / (f j).eval (p.1 : K))
        = pairZeta α f p * ((f i).eval (p.1 : K) * α i ^ p.1) /
          (pairZeta α f p * ((f j).eval (p.1 : K) * α j ^ p.1)) := by
          rw [div_pow]; field_simp [hα0 j, hnz j]
      _ = (f i).eval (p.2 : K) * α i ^ p.2 / ((f j).eval (p.2 : K) * α j ^ p.2) := by rw [hi, hj]
      _ = (α i / α j) ^ p.2 * ((f i).eval (p.2 : K) / (f j).eval (p.2 : K)) := by
          rw [div_pow]; field_simp [hα0 j, hjs]
  by_cases hconst : ∀ k, (f k).natDegree = 0
  · -- all `f_k` constant: then `(α_i / α_j) ^ (r - s) = 1`
    obtain ⟨i, j, hij⟩ := exists_pair_ne ι
    refine Set.finite_empty.subset fun p ⟨hp, hnz, hk⟩ ↦ ?_
    have h := hkey p hp hnz hk i j
    have hc : ∀ k (x y : K), (f k).eval x = (f k).eval y := fun k x y ↦ by
      rw [eq_C_of_natDegree_eq_zero (hconst k), eval_C, eval_C]
    rw [hc i (p.2 : K) (p.1 : K), hc j (p.2 : K) (p.1 : K)] at h
    have hq : (f i).eval (p.1 : K) / (f j).eval (p.1 : K) ≠ 0 := div_ne_zero (hnz i) (hnz j)
    have hθ : (α i / α j) ^ p.1 = (α i / α j) ^ p.2 := mul_right_cancel₀ hq h
    have hsr : p.2 < p.1 := hp.1
    refine hnd i j hij (p.1 - p.2) (Nat.sub_pos_of_lt hsr) ?_
    have hθ0 : (α i / α j) ^ p.2 ≠ 0 := pow_ne_zero _ (div_ne_zero (hα0 i) (hα0 j))
    rw [← Nat.sub_add_cancel hsr.le, pow_add] at hθ
    exact (mul_eq_right₀ hθ0).mp hθ
  push Not at hconst
  obtain ⟨i, hdeg⟩ := hconst
  obtain ⟨j, hji⟩ := exists_ne i
  obtain ⟨C, hC1, N, hCN⟩ := exists_forall_mulHeight₁_eval_le (K := K) f
  set θ := α i / α j with hθdef
  have hθ : 1 < mulHeight₁ θ := one_lt_mulHeight₁ (div_ne_zero (hα0 i) (hα0 j)) (hnd i j hji.symm)
  set d := (f i).natDegree
  set γ : ℝ := 1 / (2 * d + 3) with hγ
  have hγ0 : 0 < γ := by positivity
  obtain ⟨β, hβ0, hβ⟩ := exists_forall_sub_le_mul_rpow hθ hC1 N hγ0
  have hγd : γ < 1 / ((f i).natDegree + (f i).natDegree + 2) := by
    rw [hγ]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have hL2 := finite_setOf_eval_div_eval_mem_unit_of_splits S (hfs i) (hfs i)
    (fun h hh ↦ Polynomial.not_comp_X_add_C_dvd (Nat.pos_of_ne_zero hdeg)
      (Int.cast_ne_zero.mpr hh)) hβ0 hγ0.le hγd
  refine (hL2.preimage (f := fun p : ℕ × ℕ ↦ ((p.1 : ℤ), (p.2 : ℤ))) fun p _ q _ h ↦ ?_).subset
    fun p ⟨hp, hnz, hk⟩ ↦ ?_
  · simp only [Prod.mk.injEq, Nat.cast_inj] at h
    exact Prod.ext h.1 h.2
  have hsr : p.2 < p.1 := hp.1
  have hr1 : 1 ≤ p.1 := Nat.one_le_of_lt hsr
  have hr1' : (1 : ℝ) ≤ p.1 := by exact_mod_cast hr1
  have hz := pairZeta_ne_zero hp
  have hi := pairZeta_mul_eq hp hα0 (hnz i) (hk i)
  have hjs : ∀ k, (f k).eval (p.2 : K) ≠ 0 := fun k h0 ↦ by
    have := pairZeta_mul_eq hp hα0 (hnz k) (hk k)
    rw [h0, zero_mul] at this
    exact mul_ne_zero hz (mul_ne_zero (hnz k) (pow_ne_zero _ (hα0 k))) this
  -- `θ ^ (r - s)` is a ratio of polynomial values
  have hθrs : θ ^ (p.1 - p.2) = (f i).eval (p.2 : K) * (f j).eval (p.1 : K) /
      ((f j).eval (p.2 : K) * (f i).eval (p.1 : K)) := by
    have h := hkey p hp hnz hk i j
    have hθ0 : θ ^ p.2 ≠ 0 := pow_ne_zero _ (div_ne_zero (hα0 i) (hα0 j))
    have hpow : θ ^ p.1 = θ ^ (p.1 - p.2) * θ ^ p.2 := by
      rw [← pow_add, Nat.sub_add_cancel hsr.le]
    rw [← hθdef, hpow] at h
    have h' : θ ^ (p.1 - p.2) * ((f i).eval (p.1 : K) / (f j).eval (p.1 : K)) =
        (f i).eval (p.2 : K) / (f j).eval (p.2 : K) := by
      apply mul_left_cancel₀ hθ0
      linear_combination h
    rw [eq_div_iff (mul_ne_zero (hjs j) (hnz i))]
    field_simp [hnz j, hjs j] at h'
    linear_combination h'
  have hH : ∀ k, mulHeight₁ ((f k).eval (p.1 : K)) ≤ C * (p.1 : ℝ) ^ N ∧
      mulHeight₁ ((f k).eval (p.2 : K)) ≤ C * (p.1 : ℝ) ^ N :=
    fun k ↦ ⟨hCN k _ _ le_rfl hr1, hCN k _ _ hsr.le hr1⟩
  have hup : mulHeight₁ θ ^ (p.1 - p.2) ≤ (C * (p.1 : ℝ) ^ N) ^ 4 := by
    rw [← mulHeight₁_pow, hθrs]
    refine (mulHeight₁_div_le _ _).trans ?_
    have h1 := mulHeight₁_mul_le ((f i).eval (p.2 : K)) ((f j).eval (p.1 : K))
    have h2 := mulHeight₁_mul_le ((f j).eval (p.2 : K)) ((f i).eval (p.1 : K))
    have hCr : 0 ≤ C * (p.1 : ℝ) ^ N := by positivity
    calc _ ≤ (mulHeight₁ ((f i).eval (p.2 : K)) * mulHeight₁ ((f j).eval (p.1 : K))) *
          (mulHeight₁ ((f j).eval (p.2 : K)) * mulHeight₁ ((f i).eval (p.1 : K))) :=
          mul_le_mul h1 h2 (mulHeight₁_pos _).le (by positivity)
      _ ≤ ((C * (p.1 : ℝ) ^ N) * (C * (p.1 : ℝ) ^ N)) *
          ((C * (p.1 : ℝ) ^ N) * (C * (p.1 : ℝ) ^ N)) := by
          gcongr
          exacts [(hH i).2, (hH j).1, (hH j).2, (hH i).1]
      _ = _ := by ring
  -- so `r - s = O(log r)`
  have hrs := hβ p.1 p.2 hsr hup
  refine ⟨?_, ?_, ?_⟩
  · change (p.1 : ℤ) ≠ (p.2 : ℤ)
    exact_mod_cast hsr.ne'
  · simp only [Int.cast_natCast]
    rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hsr.le : (p.2 : ℝ) ≤ p.1)),
      abs_of_nonneg (Nat.cast_nonneg _)]
    have : ((p.1 - p.2 : ℕ) : ℝ) = (p.1 : ℝ) - p.2 := Nat.cast_sub hsr.le
    rw [← this]; exact hrs
  · obtain ⟨zw, hzw, hzwe⟩ := exists_unit_eq_pairZeta hp
    obtain ⟨w, hw, hwe⟩ := hαS i
    refine ⟨w ^ p.2 * (zw * w ^ p.1)⁻¹, mul_mem (pow_mem hw _) (inv_mem (mul_mem hzw
      (pow_mem hw _))), ?_⟩
    simp only [Int.cast_natCast, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      hzwe, hwe]
    rw [eq_div_iff (hjs i)]
    field_simp [hz, hα0 i]
    linear_combination -hi

open scoped Classical in
/-- **Case 2 of Theorem 3** (`σ ≠ 1`): along a cycle `i, σ i, σ² i, …` of `σ`, the quotients
`θ_k = α_{σ^k i} / α_{σ^{k+1} i}` satisfy `θ_k ^ r q_{k+1} = q_k θ_{k+1} ^ s` with `q_k`
quotients of polynomial values. Measured by the logarithm of their size at the places where
`|θ_0| > 1`, these telescope to `r · log H(θ_0) = O(log r)`, so `r` is bounded. -/
theorem finite_setOf_pairTerms_perm (hα0 : ∀ i, α i ≠ 0)
    (hnd : ∀ i j, i ≠ j → ∀ n : ℕ, 0 < n → (α i / α j) ^ n ≠ 1)
    (hαS : ∀ i, ∃ w : Kˣ, w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧ (w : K) = α i)
    {σ : Equiv.Perm ι} (hσ : σ ≠ 1) :
    {p | p ∈ powerSumPairs S α f ∧ (∀ k, (f k).eval (p.1 : K) ≠ 0) ∧
      ∀ k, pairTerms α f p (Sum.inl k) + pairTerms α f p (Sum.inr (σ k)) = 0}.Finite := by
  obtain ⟨i, hσi⟩ : ∃ i, σ i ≠ i := by
    by_contra h
    push Not at h
    exact hσ (Equiv.ext h)
  obtain ⟨C, hC1, N, hCN⟩ := exists_forall_mulHeight₁_eval_le (K := K) f
  set ℓ := orderOf σ with hℓdef
  have hℓ : 0 < ℓ := orderOf_pos σ
  set idx : ℕ → ι := fun k ↦ (σ ^ k) i with hidx
  have hidx_succ : ∀ k, idx (k + 1) = σ (idx k) := fun k ↦ by
    simp only [hidx, pow_succ', Equiv.Perm.mul_apply]
  have hidxℓ : idx ℓ = idx 0 := by simp [hidx, hℓdef, pow_orderOf_eq_one]
  have hidxℓ1 : idx (ℓ + 1) = idx 1 := by rw [hidx_succ, hidxℓ, ← hidx_succ]
  set θ : ℕ → K := fun k ↦ α (idx k) / α (idx (k + 1)) with hθdef
  have hθ0 : 1 < mulHeight₁ (θ 0) := by
    refine one_lt_mulHeight₁ (div_ne_zero (hα0 _) (hα0 _)) ?_
    simp only [hθdef, hidx, pow_zero, Equiv.Perm.one_apply, zero_add, pow_one]
    exact hnd i (σ i) (Ne.symm hσi)
  set L := Real.log (mulHeight₁ (θ 0)) with hL
  have hL0 : 0 < L := Real.log_pos hθ0
  -- the logarithmic size at the places where `|θ₀| > 1`
  set T : Set (AbsoluteValue K ℝ) := {v | 1 < v (θ 0)} with hT
  set Λ : K → ℝ := fun y ↦ Real.log (placeProd S T (fun v ↦ v y)) with hΛ
  have hPpos : ∀ {y : K}, y ≠ 0 → 0 < placeProd S T (fun v ↦ v y) :=
    fun hy ↦ placeProd_pos S T fun v _ ↦ v.pos hy
  have hΛmul : ∀ {x y : K}, x ≠ 0 → y ≠ 0 → Λ (x * y) = Λ x + Λ y := fun hx hy ↦ by
    simp only [hΛ, map_mul]
    rw [placeProd_mul, Real.log_mul (hPpos hx).ne' (hPpos hy).ne']
  have hΛpow : ∀ {x : K} (n : ℕ), Λ (x ^ n) = n * Λ x := fun n ↦ by
    simp only [hΛ]; rw [placeProd_pow, Real.log_pow]
  have hΛbound : ∀ {y : K}, y ≠ 0 → |Λ y| ≤ Real.log (mulHeight₁ y) := by
    intro y hy
    refine abs_le.mpr ⟨?_, Real.log_le_log (hPpos hy) (placeProd_le_mulHeight₁ S T y)⟩
    have h := Real.log_le_log (inv_pos.mpr (mulHeight₁_pos y)) (inv_mulHeight₁_le_placeProd S T hy)
    rw [Real.log_inv] at h
    simp only [hΛ]
    linarith
  have hΛθ : L ≤ Λ (θ 0) := by
    have hθint : θ 0 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K := by
      obtain ⟨w₁, hw₁, hw₁e⟩ := hαS (idx 0)
      obtain ⟨w₂, hw₂, hw₂e⟩ := hαS (idx 1)
      have : θ 0 = ((w₁ * w₂⁻¹ : Kˣ) : K) := by
        simp [hθdef, hw₁e, hw₂e, div_eq_mul_inv]
      rw [this]
      exact Set.mem_integer_of_mem_unit (mul_mem hw₁ (inv_mem hw₂))
    have hpt : ∀ v : AbsoluteValue K ℝ,
        T.mulIndicator (fun v ↦ v (θ 0)) v = ⨆ k, v (![θ 0, 1] k) := by
      intro v
      have hle : ∀ k, v (![θ 0, 1] k) ≤ max (v (θ 0)) 1 := fun k ↦ by
        fin_cases k
        · exact le_max_left _ _
        · simp
      have hsup : (⨆ k, v (![θ 0, 1] k)) = max (v (θ 0)) 1 := by
        refine le_antisymm (ciSup_le hle) (max_le ?_ ?_)
        · exact le_ciSup (f := fun k ↦ v (![θ 0, 1] k)) (Finite.bddAbove_range _) 0
        · have := le_ciSup (f := fun k ↦ v (![θ 0, 1] k)) (Finite.bddAbove_range _) 1
          simpa using this
      rw [hsup]
      by_cases hv : v ∈ T
      · rw [Set.mulIndicator_of_mem hv, max_eq_left (le_of_lt hv)]
      · rw [Set.mulIndicator_of_notMem hv, max_eq_right (not_lt.mp hv)]
    have heq : placeProd S T (fun v ↦ v (θ 0)) =
        placeProd S Set.univ (fun v ↦ ⨆ k, v (![θ 0, 1] k)) := by
      simp only [placeProd, Set.mulIndicator_univ, hpt]
    have hH := mulHeight_le_placeProd_univ S (x := ![θ 0, 1])
      (fun h ↦ one_ne_zero (congrFun h 1)) fun k ↦ by
        fin_cases k
        · exact hθint
        · exact one_mem _
    rw [← mulHeight₁_eq_mulHeight, ← heq] at hH
    exact Real.log_le_log (mulHeight₁_pos _) hH
  obtain ⟨R, hR⟩ := exists_forall_mul_pow_lt_pow hθ0 (C ^ 4) (4 * N)
  refine finite_of_forall_fst_lt (max R 1) fun p ⟨hp, hnz, hk⟩ ↦ ⟨hp.1, ?_⟩
  by_contra hcon
  push Not at hcon
  have hsr : p.2 < p.1 := hp.1
  have hr1 : 1 ≤ p.1 := (le_max_right _ _).trans hcon
  have hrR : R ≤ p.1 := (le_max_left _ _).trans hcon
  have hr1' : (1 : ℝ) ≤ p.1 := by exact_mod_cast hr1
  have hz := pairZeta_ne_zero hp
  -- the equations along the cycle
  have heqk : ∀ k, pairZeta α f p * ((f (idx k)).eval (p.1 : K) * α (idx k) ^ p.1) =
      (f (idx (k + 1))).eval (p.2 : K) * α (idx (k + 1)) ^ p.2 := fun k ↦ by
    rw [hidx_succ]; exact pairZeta_mul_eq hp hα0 (hnz _) (hk _)
  have hfs : ∀ k, (f (idx (k + 1))).eval (p.2 : K) ≠ 0 := fun k h0 ↦ by
    have := heqk k
    rw [h0, zero_mul] at this
    exact mul_ne_zero hz (mul_ne_zero (hnz _) (pow_ne_zero _ (hα0 _))) this
  set q : ℕ → K := fun k ↦ (f (idx (k + 1))).eval (p.2 : K) / (f (idx k)).eval (p.1 : K) with hq
  have hq0 : ∀ k, q k ≠ 0 := fun k ↦ div_ne_zero (hfs k) (hnz _)
  have hθne : ∀ k, θ k ≠ 0 := fun k ↦ div_ne_zero (hα0 _) (hα0 _)
  have hrel : ∀ k, θ k ^ p.1 * q (k + 1) = q k * θ (k + 1) ^ p.2 := by
    intro k
    have h1 := heqk k
    have h2 := heqk (k + 1)
    have hr0 := hnz (idx k)
    have hr1 := hnz (idx (k + 1))
    have hs2 := hfs (k + 1)
    have hs1 := hfs k
    have hak : α (idx k) ^ p.1 = (f (idx (k + 1))).eval (p.2 : K) * α (idx (k + 1)) ^ p.2 /
        (pairZeta α f p * (f (idx k)).eval (p.1 : K)) := by
      rw [eq_div_iff (mul_ne_zero hz hr0)]; linear_combination h1
    have hak1 : α (idx (k + 1)) ^ p.1 =
        (f (idx (k + 1 + 1))).eval (p.2 : K) * α (idx (k + 1 + 1)) ^ p.2 /
        (pairZeta α f p * (f (idx (k + 1))).eval (p.1 : K)) := by
      rw [eq_div_iff (mul_ne_zero hz hr1)]; linear_combination h2
    simp only [hθdef, hq, div_pow]
    rw [hak, hak1]
    field_simp [hα0 (idx k), hα0 (idx (k + 1)), hα0 (idx (k + 1 + 1))]
  -- apply the logarithmic size
  set x : ℕ → ℝ := fun k ↦ Λ (θ k) with hx
  set y : ℕ → ℝ := fun k ↦ Λ (q k) with hy
  have hrelΛ : ∀ k, (p.1 : ℝ) * x k - (p.2 : ℝ) * x (k + 1) = y k - y (k + 1) := by
    intro k
    have h := congrArg Λ (hrel k)
    rw [hΛmul (pow_ne_zero _ (hθne k)) (hq0 _), hΛmul (hq0 k) (pow_ne_zero _ (hθne _)),
      hΛpow, hΛpow] at h
    simp only [hx, hy]
    linarith
  have hxℓ : x ℓ = x 0 := by simp only [hx, hθdef, hidxℓ, hidxℓ1]
  have hyℓ : y ℓ = y 0 := by simp only [hy, hq, hidxℓ, hidxℓ1]
  have hH : ∀ k, mulHeight₁ (q k) ≤ C ^ 2 * (p.1 : ℝ) ^ (2 * N) := by
    intro k
    refine (mulHeight₁_div_le _ _).trans ?_
    calc _ ≤ (C * (p.1 : ℝ) ^ N) * (C * (p.1 : ℝ) ^ N) :=
          mul_le_mul (hCN _ _ _ hsr.le hr1) (hCN _ _ _ le_rfl hr1) (mulHeight₁_pos _).le
            (by positivity)
      _ = C ^ 2 * (p.1 : ℝ) ^ (2 * N) := by ring
  have hY : ∀ k ≤ ℓ, |y k| ≤ Real.log (C ^ 2 * (p.1 : ℝ) ^ (2 * N)) := fun k _ ↦
    (hΛbound (hq0 k)).trans (Real.log_le_log (mulHeight₁_pos _) (hH k))
  have htel := mul_le_two_mul_of_telescope hℓ (Nat.cast_nonneg p.2)
    (by exact_mod_cast hsr) x y (fun k _ ↦ hrelΛ k) hxℓ hyℓ hY
  have hrL : (p.1 : ℝ) * L ≤ 2 * Real.log (C ^ 2 * (p.1 : ℝ) ^ (2 * N)) :=
    (mul_le_mul_of_nonneg_left hΛθ (by positivity)).trans htel
  have hup : mulHeight₁ (θ 0) ^ p.1 ≤ C ^ 4 * (p.1 : ℝ) ^ (4 * N) := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, ← hL]
    calc (p.1 : ℝ) * L ≤ 2 * Real.log (C ^ 2 * (p.1 : ℝ) ^ (2 * N)) := hrL
      _ = Real.log (C ^ 4 * (p.1 : ℝ) ^ (4 * N)) := by
          rw [← Real.log_rpow (by positivity)]
          congr 1
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          ring
  exact (hR p.1 hrR).not_ge hup

/-- The pairs grow with `S`. -/
theorem powerSumPairs_mono {S S' : Finset (HeightOneSpectrum (𝓞 K))} (h : S ⊆ S') :
    powerSumPairs S α f ⊆ powerSumPairs S' α f := by
  rintro p ⟨h1, h2, h3 | ⟨w, hw, hwe⟩⟩
  · exact ⟨h1, h2, Or.inl h3⟩
  · exact ⟨h1, h2, Or.inr ⟨w, mem_unit_of_subset (by exact_mod_cast h) hw, hwe⟩⟩

end Pairs

open scoped Classical in
/-- **Evertse's Theorem 3**, for generalized power sums over `K` with split polynomials. Let
`u_k = ∑_i f_i(k) α_i ^ k` with at least two nonzero characteristic roots `α_i ∈ K`, no quotient
`α_i / α_j` (`i ≠ j`) a root of unity, and nonzero polynomials `f_i` that split over `K`. Then for
every finite set `S` of primes only finitely many pairs `r > s ≥ 0` have `u_s ≠ 0` and `u_r / u_s`
zero or an `S`-unit; that is, `P_K(u_r / u_s) → ∞` as `r → ∞` with `r > s`, `u_s ≠ 0`. -/
theorem finite_setOf_powerSum_div_mem_unit_of_splits {ι : Type*} [Fintype ι] [Nontrivial ι]
    {α : ι → K} {f : ι → K[X]} (hα0 : ∀ i, α i ≠ 0)
    (hnd : ∀ i j, i ≠ j → ∀ n : ℕ, 0 < n → (α i / α j) ^ n ≠ 1) (hf0 : ∀ i, f i ≠ 0)
    (hfs : ∀ i, (f i).Splits) :
    (powerSumPairs S α f).Finite := by
  -- enlarge `S`
  choose Tα hTα using fun i ↦ exists_finset_mem_unit (Units.mk0 (α i) (hα0 i))
  obtain ⟨Tc, -, hTc⟩ := exists_finset_forall_mem_integer S
    (fun c : Σ i, Fin ((f i).natDegree + 1) ↦ (f c.1).coeff c.2)
  set S' := S ∪ Finset.univ.biUnion Tα ∪ Tc with hS'
  have hSS' : S ⊆ S' := fun x hx ↦ by simp [hS', hx]
  have hαS : ∀ i, ∃ w : Kˣ, w ∈ (S' : Set (HeightOneSpectrum (𝓞 K))).unit K ∧ (w : K) = α i :=
    fun i ↦ ⟨_, mem_unit_of_subset (by
      intro x hx; simp only [Finset.coe_union, Finset.coe_biUnion, Finset.coe_univ,
        Set.mem_univ, Set.iUnion_true, Set.mem_union, Set.mem_iUnion, Finset.mem_coe, hS']
      exact Or.inl (Or.inr ⟨i, hx⟩)) (hTα i), rfl⟩
  have hcS : ∀ i n, (f i).coeff n ∈ (S' : Set (HeightOneSpectrum (𝓞 K))).integer K := by
    intro i n
    by_cases hn : n ≤ (f i).natDegree
    · exact mem_integer_of_subset (by intro x hx; simp [hS', hx])
        (hTc ⟨i, ⟨n, Nat.lt_succ_of_le hn⟩⟩)
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hn)]
      exact zero_mem _
  refine Set.Finite.subset ?_ (powerSumPairs_mono (α := α) (f := f) hSS')
  -- the pairs with a vanishing `f_k(r)`
  have hE : {p | p ∈ powerSumPairs S' α f ∧ ∃ k, (f k).eval (p.1 : K) = 0}.Finite := by
    have hR : {r : ℕ | ∃ k, (f k).eval (r : K) = 0}.Finite := by
      refine (Set.finite_iUnion fun k ↦ ((f k).roots.toFinset.finite_toSet.preimage
        (Nat.cast_injective (R := K)).injOn)).subset fun r ⟨k, hk⟩ ↦ ?_
      exact Set.mem_iUnion.mpr ⟨k, Multiset.mem_toFinset.mpr ((mem_roots (hf0 k)).mpr hk)⟩
    obtain ⟨M, hM⟩ := hR.bddAbove
    exact finite_of_forall_fst_lt (M + 1) fun p ⟨hp, k, hk⟩ ↦
      ⟨hp.1, Nat.lt_succ_of_le (hM ⟨k, hk⟩)⟩
  -- Step A
  have hA := Set.Finite.biUnion (Set.toFinite {t : ι × ι × Finset (ι ⊕ ι) |
      t.1 ≠ t.2.1 ∧ Sum.inl t.1 ∈ t.2.2 ∧ Sum.inl t.2.1 ∈ t.2.2}) fun t ht ↦
    finite_setOf_pair_mem_block (S := S') (f := f) hα0 hnd hαS hcS ht.1 t.2.2 ht.2.1 ht.2.2
  -- the permutations
  have hB := Set.finite_iUnion (ι := Equiv.Perm ι) fun σ ↦
    (if hσ : σ = 1 then (finite_setOf_pairTerms_refl (S := S') (f := f) hα0 hnd hαS hfs).subset
      (fun p ⟨hp, hnz, hk⟩ ↦ ⟨hp, hnz, fun k ↦ by simpa [hσ] using hk k⟩) else
      finite_setOf_pairTerms_perm (S := S') (f := f) hα0 hnd hαS hσ :
      {p | p ∈ powerSumPairs S' α f ∧ (∀ k, (f k).eval (p.1 : K) ≠ 0) ∧
        ∀ k, pairTerms α f p (Sum.inl k) + pairTerms α f p (Sum.inr (σ k)) = 0}.Finite)
  refine (hE.union (hA.union hB)).subset fun p hp ↦ ?_
  by_cases hnz : ∃ k, (f k).eval (p.1 : K) = 0
  · exact Or.inl ⟨hp, hnz⟩
  push Not at hnz
  have hne : ∀ i, pairTerms α f p (Sum.inl i) ≠ 0 := fun i ↦
    mul_ne_zero (pairZeta_ne_zero hp) (mul_ne_zero (hnz i) (pow_ne_zero _ (hα0 i)))
  rcases exists_pair_or_exists_perm (pairTerms α f p) (sum_pairTerms p) hne with
    ⟨i, j, hij, J, hi, hj, hJ0, hJmin⟩ | ⟨σ, hσ⟩
  · exact Or.inr (Or.inl (Set.mem_biUnion (x := (i, j, J)) ⟨hij, hi, hj⟩
      ⟨hp, hnz, hJ0, hJmin⟩))
  · exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨σ, hp, hnz, hσ⟩))

/-- **A generalized power sum with nonzero polynomials and distinct nonzero characteristic roots
has a nonzero term** (linear independence of exponential polynomials). -/
theorem exists_powerSum_ne_zero {ι : Type*} [Fintype ι] [Nonempty ι] {α : ι → K} {f : ι → K[X]}
    (hα : Function.Injective α) (hα0 : ∀ i, α i ≠ 0) (hf0 : ∀ i, f i ≠ 0) :
    ∃ s₀ : ℕ, powerSum α f s₀ ≠ 0 := by
  by_contra! h
  exact hf0 (Classical.arbitrary ι) (eq_zero_of_forall_sum_eval_mul_pow_eq_zero hα hα0 h _)

omit [NumberField K] in
/-- Non-degeneracy makes the characteristic roots distinct. -/
theorem injective_of_forall_div_pow_ne_one {ι : Type*} {α : ι → K}
    (hnd : ∀ i j, i ≠ j → ∀ n : ℕ, 0 < n → (α i / α j) ^ n ≠ 1) (hα0 : ∀ i, α i ≠ 0) :
    Function.Injective α := fun i j hij ↦ by
  by_contra hne
  exact hnd i j hne 1 one_pos (by rw [pow_one, hij, div_self (hα0 j)])

end NumberField
