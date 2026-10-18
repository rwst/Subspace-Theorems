/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Stephan2026a.Reduction
public import Stephan2026a.SubspaceStep

-- Used only inside proofs.
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Finset.Nat

/-!
# Constant gap: Mahler's theorem with a rational multiplier

**Lemma 4.2.** For rational `ξ > 0` and `θ ∈ (0, 1)`, only finitely many `a` satisfy
`0 < ‖ξ (3/2)^a‖ ≤ θ^a`. Dividing by `(3/2)^a`, with `M` the integer nearest to `ξ (3/2)^a`, the
inequality says `|ξ - M 2^a / 3^a| ≤ θ^a (2/3)^a`: an approximation to the fixed rational `ξ` by
fractions whose denominator is a power of `3` and whose numerator is divisible by a large power
of `2`. Ridout's theorem says that such `p`-adic constraints are paid for exactly as the
accounting principle, equation (1) of the paper, describes, so that the approximations cannot be
appreciably better than trivial. The proof is the two-variable case of Theorem 4.1: with
`ξ = u / v`, the integer point `y = (u 3^a, v M 2^a)` and the forms `Y₁ - Y₂`, `Y₂` at `∞`, the
double product is at most `v² (ξ + 1) θ^a` while `‖y‖ ≤ (u + v) 3^a`. The points `y` lie on
finitely many lines `Y₂ = ρ Y₁`, and on such a line `|1 - ρ| u 3^a ≤ v 2^a θ^a` bounds `a`.

For `ξ = 1` this is Mahler's theorem (DA `Nat.finite_setOf_exists_int_abs_sub_ratPow_le`).

**Corollary 4.3.** For every `S`, the pairs of `V(θ)` with gap `c - a ≤ S` are finitely many: for
a gap `s`, `(3/2)^(a+s) - (3/2)^a = ξ (3/2)^a` with `ξ = (3/2)^s - 1`.

## Main results

* `SteeringWord.finite_setOf_distToNearestInt_mul_le`: **Lemma 4.2**.
* `SteeringWord.finite_kernelViolators_gap_le`: **Corollary 4.3**, the gap-bounded slice.

## References

R. Stephan, *Superlinear complexity of the `(3/2)^n` steering word*, arXiv:2607.11648, §4.2;
D. Ridout, *The `p`-adic generalization of the Thue–Siegel–Roth theorem*, Mathematika **5**
(1958), 40–48; K. Mahler, *On the fractional parts of the powers of a rational number II*,
Mathematika **4** (1957), 122–124.
-/

public section

namespace SteeringWord

/-- **Lemma 4.2, Mahler's theorem with a rational multiplier.** For rational `ξ > 0` and
`θ ∈ (0, 1)`, only finitely many `a` satisfy `0 < ‖ξ (3/2)^a‖ ≤ θ^a`. Ineffective. -/
theorem finite_setOf_distToNearestInt_mul_le {ξ : ℚ} (hξ : 0 < ξ) {θ : ℚ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) :
    {a : ℕ | 0 < (ξ * (3 / 2) ^ a).distToNearestInt ∧
      (ξ * (3 / 2) ^ a).distToNearestInt ≤ θ ^ a}.Finite := by
  classical
  set A : Set ℕ := {a : ℕ | 0 < (ξ * (3 / 2) ^ a).distToNearestInt ∧
    (ξ * (3 / 2) ^ a).distToNearestInt ≤ θ ^ a} with hAdef
  set u : ℤ := ξ.num with hudef
  set v : ℤ := (ξ.den : ℤ) with hvdef
  have hu : 0 < u := Rat.num_pos.mpr hξ
  have hv : 0 < v := Nat.cast_pos.mpr ξ.den_pos
  have huq : (0 : ℚ) < u := by exact_mod_cast hu
  have hvq : (0 : ℚ) < v := by exact_mod_cast hv
  have hξv : ξ * (v : ℚ) = u := by simp [hudef, hvdef]
  set M : ℕ → ℤ := fun a ↦ round (ξ * (3 / 2 : ℚ) ^ a) with hMdef
  set N : ℕ → ℤ := fun a ↦ u * 3 ^ a - v * M a * 2 ^ a with hNdef
  set y : ℕ → Fin 2 → ℤ := fun a ↦ ![u * 3 ^ a, v * M a * 2 ^ a] with hydef
  have hN : ∀ a, (N a : ℚ) = v * 2 ^ a * (ξ * (3 / 2) ^ a - M a) := fun a ↦ by
    simp only [hNdef]
    push_cast
    rw [← hξv, div_pow]
    field_simp
  have hNabs : ∀ a, |(N a : ℚ)| = v * 2 ^ a * (ξ * (3 / 2) ^ a).distToNearestInt := fun a ↦ by
    rw [hN, abs_mul, abs_of_pos (by positivity)]
    rfl
  have hM : ∀ a, |(M a : ℚ)| ≤ ξ * (3 / 2) ^ a + 1 / 2 := fun a ↦ by
    have h := abs_le.mp (abs_sub_round (ξ * (3 / 2 : ℚ) ^ a))
    have hx : 0 ≤ ξ * (3 / 2 : ℚ) ^ a := by positivity
    exact abs_le.mpr ⟨by simp only [hMdef]; linarith, by simp only [hMdef]; linarith⟩
  have hy1 : ∀ a, |((v * M a * 2 ^ a : ℤ) : ℚ)| ≤ v * (ξ * (3 / 2) ^ a + 1 / 2) * 2 ^ a :=
    fun a ↦ by
      push_cast
      rw [abs_mul, abs_mul, abs_of_pos hvq, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ a)]
      gcongr
      exact hM a
  -- the double product of Theorem 4.1 at `y a`
  set P : ℕ → ℚ := fun a ↦ |(N a : ℚ)| * |((v * M a * 2 ^ a : ℤ) : ℚ)|
    * (padicNorm 2 ((u * 3 ^ a : ℤ) : ℚ) * padicNorm 2 ((v * M a * 2 ^ a : ℤ) : ℚ))
    * (padicNorm 3 ((u * 3 ^ a : ℤ) : ℚ) * padicNorm 3 ((v * M a * 2 ^ a : ℤ) : ℚ)) with hPdef
  have hP : ∀ a ∈ A, P a ≤ v ^ 2 * (ξ + 1) * θ ^ a := fun a ha ↦ by
    have h2 : padicNorm 2 ((u * 3 ^ a : ℤ) : ℚ) * padicNorm 2 ((v * M a * 2 ^ a : ℤ) : ℚ)
        ≤ (1 / 2 : ℚ) ^ a :=
      calc _ ≤ 1 * (1 / 2 : ℚ) ^ a := mul_le_mul (padicNorm.of_int _)
              (padicNorm_le_of_dvd (by push_cast; exact Dvd.intro_left _ rfl))
              (padicNorm.nonneg _) zero_le_one
        _ = _ := one_mul _
    have h3 : padicNorm 3 ((u * 3 ^ a : ℤ) : ℚ) * padicNorm 3 ((v * M a * 2 ^ a : ℤ) : ℚ)
        ≤ (1 / 3 : ℚ) ^ a :=
      calc _ ≤ (1 / 3 : ℚ) ^ a * 1 := mul_le_mul
              (padicNorm_le_of_dvd (by push_cast; exact Dvd.intro_left _ rfl))
              (padicNorm.of_int _) (padicNorm.nonneg _) (by positivity)
        _ = _ := mul_one _
    have hNle : |(N a : ℚ)| ≤ v * 2 ^ a * θ ^ a := by
      rw [hNabs]
      exact mul_le_mul_of_nonneg_left ha.2 (by positivity)
    have hY : (2 : ℚ) ^ a * 2 ^ a * (1 / 2) ^ a * (1 / 3) ^ a = (2 / 3) ^ a := by
      rw [← mul_pow, ← mul_pow, ← mul_pow]
      norm_num
    have hXY : (3 / 2 : ℚ) ^ a * (2 / 3) ^ a = 1 := by
      rw [← mul_pow]
      norm_num
    have hY1 : (2 / 3 : ℚ) ^ a ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc P a ≤ (v * 2 ^ a * θ ^ a) * (v * (ξ * (3 / 2) ^ a + 1 / 2) * 2 ^ a)
          * (1 / 2) ^ a * (1 / 3) ^ a := by
          simp only [hPdef]
          refine mul_le_mul (mul_le_mul (mul_le_mul hNle (hy1 a) (abs_nonneg _) (by positivity))
            h2 (mul_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _)) (by positivity)) h3
            (mul_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _)) (by positivity)
      _ = v ^ 2 * θ ^ a * (ξ * ((3 / 2) ^ a * ((2 : ℚ) ^ a * 2 ^ a * (1 / 2) ^ a * (1 / 3) ^ a))
          + (2 ^ a * 2 ^ a * (1 / 2) ^ a * (1 / 3) ^ a) / 2) := by ring
      _ = v ^ 2 * θ ^ a * (ξ + (2 / 3) ^ a / 2) := by rw [hY, hXY, mul_one]
      _ ≤ v ^ 2 * θ ^ a * (ξ + 1) := by gcongr; linarith
      _ = v ^ 2 * (ξ + 1) * θ ^ a := by ring
  -- the size of `y a`
  have hsize : ∀ a, ⨆ i, |((y a i : ℤ) : ℝ)| ≤ ((u + v : ℤ) : ℝ) * 3 ^ a := fun a ↦ by
    have hz0 : |u * 3 ^ a| ≤ (u + v) * 3 ^ a := by
      rw [abs_of_pos (by positivity)]
      nlinarith [pow_pos (by norm_num : (0 : ℤ) < 3) a]
    have hz1 : |v * M a * 2 ^ a| ≤ (u + v) * 3 ^ a := by
      have hq : |((v * M a * 2 ^ a : ℤ) : ℚ)| ≤ ((u + v) * 3 ^ a : ℤ) := by
        refine (hy1 a).trans ?_
        have e : (v : ℚ) * (ξ * (3 / 2) ^ a + 1 / 2) * 2 ^ a = u * 3 ^ a + v * 2 ^ a / 2 := by
          rw [← hξv, div_pow]
          field_simp
        rw [e]
        push_cast
        nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 2) (by norm_num : (2 : ℚ) ≤ 3) a,
          pow_pos (by norm_num : (0 : ℚ) < 2) a]
      exact_mod_cast hq
    refine ciSup_le fun i ↦ ?_
    fin_cases i
    · simpa [hydef] using (show (|u * 3 ^ a| : ℝ) ≤ ((u + v) * 3 ^ a : ℤ) by exact_mod_cast hz0)
    · simpa [hydef] using
        (show (|v * M a * 2 ^ a| : ℝ) ≤ ((u + v) * 3 ^ a : ℤ) by exact_mod_cast hz1)
  have hsize0 : ∀ a, 0 < ⨆ i, |((y a i : ℤ) : ℝ)| := fun a ↦ by
    refine lt_of_lt_of_le ?_ (le_ciSup (Set.finite_range _).bddAbove 0)
    simp only [hydef, Matrix.cons_val_zero]
    positivity
  -- Theorem 4.1 with `n = 2`
  have hθ0' : (0 : ℝ) < θ := by exact_mod_cast hθ0
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  obtain ⟨ε, hε, a₀, ha₀⟩ := exists_forall_mul_pow_le_rpow_neg hθ0' hθ1'
    ((v ^ 2 * (ξ + 1) : ℚ) : ℝ) (B := ((u + v : ℤ) : ℝ)) (by exact_mod_cast (by omega : 0 < u + v))
  set c : Fin 2 → Fin 2 → ℚ := ![![1, -1], ![0, 1]] with hcdef
  have hc : LinearIndependent ℚ c := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : g 0 = 0 := by simpa [hcdef, Fin.sum_univ_two] using congrFun hg 0
    intro i
    fin_cases i
    · exact h0
    · simpa [hcdef, Fin.sum_univ_two, h0] using congrFun hg 1
  obtain ⟨T, hT, hmem⟩ := exists_finset_submodule_of_prod_le c hc hε
  have hcover : ∀ a ∈ A, a₀ ≤ a → ∃ V ∈ T, (fun i ↦ ((y a i : ℤ) : ℚ)) ∈ V := fun a ha ha₀' ↦ by
    refine hmem (y a) (fun h ↦ ?_) ?_
    · have := congrFun h 0
      simp only [hydef, Matrix.cons_val_zero, Pi.zero_apply] at this
      have : (0 : ℚ) < ((u * 3 ^ a : ℤ) : ℚ) := by push_cast; positivity
      linarith
    · have hLHS : (∏ i, |∑ j, (c i j : ℝ) * (y a j : ℝ)|) * ((∏ i, ((padicNorm 2 (y a i) : ℚ) : ℝ))
          * ∏ i, ((padicNorm 3 (y a i) : ℚ) : ℝ)) = ((P a : ℚ) : ℝ) := by
        simp only [hPdef, hNdef, hydef, hcdef, Fin.prod_univ_two, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one]
        push_cast
        ring_nf
      rw [hLHS]
      exact le_trans (by exact_mod_cast hP a ha) (ha₀ a ha₀' _ (hsize0 a) (hsize a))
  -- each line through the origin carries finitely many of the points
  have hfin : ∀ V ∈ T, {a | a ∈ A ∧ (fun i ↦ ((y a i : ℤ) : ℚ)) ∈ V}.Finite := fun V hV ↦ by
    obtain ⟨w, hw0, hwV⟩ := exists_ne_zero_forall_sum_mul_eq_zero (hT V hV)
    have hrel : ∀ a, (fun i ↦ ((y a i : ℤ) : ℚ)) ∈ V →
        w 0 * ((u * 3 ^ a : ℤ) : ℚ) + w 1 * ((v * M a * 2 ^ a : ℤ) : ℚ) = 0 := fun a h ↦ by
      simpa [hydef, Fin.sum_univ_two] using hwV _ h
    have hNne : ∀ a ∈ A, (N a : ℚ) ≠ 0 := fun a ha h ↦ by
      have := hNabs a
      rw [h, abs_zero] at this
      have : 0 < (v : ℚ) * 2 ^ a * (ξ * (3 / 2) ^ a).distToNearestInt := by
        have := ha.1
        positivity
      linarith
    by_cases hw1 : w 1 = 0
    · refine Set.finite_empty.subset fun a ⟨_, ha⟩ ↦ hw0 (funext fun i ↦ ?_)
      have h := hrel a ha
      rw [hw1, zero_mul, add_zero] at h
      have hne : ((u * 3 ^ a : ℤ) : ℚ) ≠ 0 := by push_cast; positivity
      fin_cases i
      · exact (mul_eq_zero.mp h).resolve_right hne
      · exact hw1
    set γ : ℚ := 1 + w 0 / w 1 with hγdef
    have hNγ : ∀ a, (fun i ↦ ((y a i : ℤ) : ℚ)) ∈ V → (N a : ℚ) = γ * (u * 3 ^ a) := fun a ha ↦ by
      have h := hrel a ha
      have hy : ((v * M a * 2 ^ a : ℤ) : ℚ) = -(w 0 / w 1) * (u * 3 ^ a) := by
        field_simp
        push_cast at h ⊢
        linarith
      simp only [hNdef]
      push_cast at hy ⊢
      rw [hy, hγdef]
      ring
    by_cases hγ : γ = 0
    · refine Set.finite_empty.subset fun a ⟨haA, ha⟩ ↦ hNne a haA ?_
      rw [hNγ a ha, hγ, zero_mul]
    refine (finite_setOf_three_halves_pow_le (v / (|γ| * u))).subset fun a ⟨haA, ha⟩ ↦ ?_
    have hle : |γ| * u * 3 ^ a ≤ v * 2 ^ a := by
      have h1 : |(N a : ℚ)| ≤ v * 2 ^ a * θ ^ a := by
        rw [hNabs]
        exact mul_le_mul_of_nonneg_left haA.2 (by positivity)
      have h2 : (v : ℚ) * 2 ^ a * θ ^ a ≤ v * 2 ^ a :=
        mul_le_of_le_one_right (by positivity) (pow_le_one₀ hθ0.le hθ1.le)
      rw [hNγ a ha, abs_mul, abs_of_pos (by positivity : (0 : ℚ) < u * 3 ^ a)] at h1
      linarith
    have hγ0 : 0 < |γ| := abs_pos.mpr hγ
    change (3 / 2 : ℚ) ^ a ≤ v / (|γ| * u)
    rw [le_div_iff₀ (by positivity), div_pow]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  refine ((Set.finite_Iio a₀).union (T.finite_toSet.biUnion fun V hV ↦ hfin V hV)).subset
    fun a ha ↦ ?_
  rcases lt_or_ge a a₀ with h | h
  · exact Or.inl h
  · obtain ⟨V, hV, hyV⟩ := hcover a ha h
    exact Or.inr (Set.mem_biUnion hV ⟨ha, hyV⟩)

/-- **Corollary 4.3, the gap-bounded slice**: for every `S` and rational `θ ∈ (0, 1)`, only
finitely many pairs of `V(θ)` have `c ≤ a + S`. -/
theorem finite_kernelViolators_gap_le (S : ℕ) {θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    {p | p ∈ kernelViolators θ ∧ p.2 ≤ p.1 + S}.Finite := by
  have hslice : ∀ s ∈ Finset.Icc 1 S, {p | p ∈ kernelViolators θ ∧ p.2 = p.1 + s}.Finite :=
    fun s hs ↦ by
      have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
      have hξ : 0 < (3 / 2 : ℚ) ^ s - 1 := by
        have : (3 / 2 : ℚ) ^ 1 ≤ (3 / 2) ^ s := pow_le_pow_right₀ (by norm_num) hs1
        linarith
      refine ((finite_setOf_distToNearestInt_mul_le hξ hθ0 hθ1).image
        fun a ↦ (a, a + s)).subset ?_
      rintro ⟨a, c⟩ ⟨⟨ha, hac, hd⟩, hcs⟩
      simp only at ha hac hd hcs
      subst hcs
      have heq : (3 / 2 : ℚ) ^ (a + s) - (3 / 2) ^ a = ((3 / 2) ^ s - 1) * (3 / 2) ^ a := by
        rw [pow_add]
        ring
      refine ⟨a, ⟨?_, ?_⟩, rfl⟩
      · rw [← heq]
        exact distToNearestInt_orbit_pos (by omega) hac
      · rw [← heq]
        exact hd.trans (pow_le_pow_of_le_one hθ0.le hθ1.le (by omega))
  refine ((Finset.Icc 1 S).finite_toSet.biUnion fun s hs ↦ hslice s hs).subset ?_
  rintro ⟨a, c⟩ ⟨hp, hcS⟩
  have hac := hp.2.1
  exact Set.mem_biUnion (x := c - a) (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega,
    by simp only at hcS; omega⟩)) ⟨hp, by simp only; omega⟩

end SteeringWord
