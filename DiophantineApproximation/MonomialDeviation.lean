/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Choose.Sum

/-!
# How many monomials have a small exponent in one variable

Step I of the Subspace Theorem's proof counts the monomials that the auxiliary polynomial is
required to omit. Over `m` blocks of `n + 1` variables, a monomial of multidegree `d` is a tuple
`J = (j_1, …, j_m)` with `|j_h| = d h`, and the condition imposed is that the exponent of one
fixed variable be small in the weighted sense,

`(J_i / d) = ∑ h, j h i / d h ≤ m / (n + 1) − m η`.

Since the mean of `j h i / d h` is `1 / (n + 1)`, this is a large-deviation event, and the count
is smaller than the total by a factor `exp (−(n+1)(n+2) η² m / 4)`. That is the content of this
file, and it is what makes Siegel's lemma applicable in Layer 5.2.

## Main results

* `Nat.sum_range_choose_mul_choose`: the convolution `∑ a, C(a, k) C(M − a, r) = C(M + 1, k+r+1)`.
* `Finset.sum_choose_apply_finsuppAntidiag`: **the moments** — the sum of `C(j i₀, k)` over the
  monomials of degree `N` in `n + 1` variables is `C(N + n, n + k)`. The cases `k = 0, 1, 2` are
  the cardinality and the first two moments of the exponent of one variable.
* `Finset.sum_exp_le`: **the exponential moment** — `E[exp (−λ j i₀ / N)]` is at most
  `exp (−λ/(n+1) + λ²/((n+1)(n+2)) + λ²/(2 N (n+1)))`.
* `Finset.card_le_of_subset_deviation`: the Chernoff bound over the `m` blocks.
* `Finset.card_le_of_subset_eta`: the same at the book's choice `λ = η (n+1)(n+2)/2`, which is
  the form Layer 5.2 consumes.

## Implementation notes

⚠ **The book's volume computation is not needed, and neither is its "sufficiently large `d`".**
Bombieri–Gubler estimate the number of lattice points by the volume of a region and then majorize
the characteristic function by an exponential. The exponential moment is exact on the lattice:
the uniform distribution on the monomials of degree `N` in `n + 1` variables has
`E[j i₀] = N/(n+1)` and `E[C(j i₀, 2)] = N(N−1)/((n+1)(n+2))` on the nose — two binomial
identities — and `exp(−t) ≤ 1 − t + t²/2` for `t ≥ 0` turns them into the bound above. The only
trace of the passage to the continuum is the term `λ²/(2 N (n+1))`, which is explicit and is
what the caller makes small by taking `d` large.

⚠ **The restriction `0 < λ ≤ n + 4` of the book's proof disappears**, because the quadratic
majorant of `exp (−t)` is valid for every `t ≥ 0`; the book needs it to truncate a MacLaurin
series.

⚠ **`n ≥ 1` is needed, and it is not a convenience.** The moment identity is proved by splitting
off the variable `i₀` and convolving with the count in the remaining `n` variables; that count is
`C(b + n − 1, n − 1)`, which is the wrong thing when `n = 0`. For the Subspace Theorem `n ≥ 1`
always, since `n = 0` makes the ambient projective space a point.

⚠ **The statement is about an arbitrary subset, not a filter**, so that no `DecidablePred`
instance is needed for the real inequality that cuts it out; the caller passes the `Finset` it
has together with the two facts about it.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 7.5.15, (7.23)–(7.25).

This is part of Layer 5.2 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset Real

namespace Nat

/-- **The convolution of two binomial coefficients in the upper index.** -/
theorem sum_range_choose_mul_choose (k : ℕ) : ∀ r M : ℕ,
    ∑ a ∈ Finset.range (M + 1), a.choose k * (M - a).choose r = (M + 1).choose (k + r + 1) := by
  intro r
  induction r with
  | zero =>
      intro M
      simp only [Nat.choose_zero_right, mul_one, Nat.add_zero]
      rw [← Nat.sum_Icc_choose M k]
      refine (Finset.sum_subset ?_ ?_).symm
      · intro a ha
        simp only [Finset.mem_Icc] at ha
        exact Finset.mem_range.mpr (by omega)
      · intro a ha ha'
        simp only [Finset.mem_range] at ha
        simp only [Finset.mem_Icc] at ha'
        exact Nat.choose_eq_zero_of_lt (by omega)
  | succ r ih =>
      intro M
      induction M with
      | zero => simp [Nat.choose_eq_zero_of_lt]
      | succ M ihM =>
          rw [Finset.sum_range_succ]
          have h0 : (M + 1 - (M + 1)).choose (r + 1) = 0 := by
            rw [Nat.sub_self]; exact Nat.choose_eq_zero_of_lt (by omega)
          rw [h0, mul_zero, Nat.add_zero]
          have key : ∀ a ∈ Finset.range (M + 1),
              a.choose k * (M + 1 - a).choose (r + 1)
                = a.choose k * (M - a).choose r + a.choose k * (M - a).choose (r + 1) := by
            intro a ha
            simp only [Finset.mem_range] at ha
            have : M + 1 - a = (M - a) + 1 := by omega
            rw [this, Nat.choose_succ_succ, Nat.mul_add]
          rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ih M, ihM,
            show k + (r + 1) + 1 = (k + r + 1) + 1 by ring,
            Nat.choose_succ_succ (M + 1) (k + r + 1)]

end Nat

namespace Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem card_fiber_finsuppAntidiag (i₀ : ι) {N a : ℕ} (ha : a ≤ N) :
    #{f ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) N | f i₀ = a}
      = #(Finset.finsuppAntidiag (Finset.univ.erase i₀) (N - a)) := by
  have hmem : ∀ f : ι →₀ ℕ, f ∈ {f ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) N | f i₀ = a}
      ↔ (∑ x, f x = N ∧ f i₀ = a) := by
    intro f
    simp [Finset.mem_finsuppAntidiag]
  have hmem' : ∀ g : ι →₀ ℕ, g ∈ Finset.finsuppAntidiag (Finset.univ.erase i₀) (N - a)
      ↔ (∑ x ∈ Finset.univ.erase i₀, g x = N - a ∧ g.support ⊆ Finset.univ.erase i₀) := by
    intro g; simp [Finset.mem_finsuppAntidiag]
  refine Finset.card_nbij' (fun f ↦ Finsupp.erase i₀ f) (fun g ↦ Finsupp.update g i₀ a)
    (fun f hf ↦ ?_) (fun g hg ↦ ?_) (fun f hf ↦ ?_) (fun g hg ↦ ?_)
  · rw [Finset.mem_coe, hmem] at hf
    rw [Finset.mem_coe, hmem']
    refine ⟨?_, fun x hx ↦ ?_⟩
    · have : ∑ x ∈ Finset.univ.erase i₀, (Finsupp.erase i₀ f) x
          = ∑ x ∈ Finset.univ.erase i₀, f x :=
        Finset.sum_congr rfl fun x hx ↦ Finsupp.erase_ne (Finset.ne_of_mem_erase hx)
      rw [this]
      have := Finset.add_sum_erase Finset.univ (f ·) (Finset.mem_univ i₀)
      omega
    · rw [Finsupp.support_erase] at hx
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ x⟩
  · rw [Finset.mem_coe, hmem'] at hg
    rw [Finset.mem_coe, hmem]
    refine ⟨?_, by simp⟩
    change ∑ x, (Finsupp.update g i₀ a) x = N
    have h1 := Finset.add_sum_erase Finset.univ (fun x ↦ (Finsupp.update g i₀ a) x)
      (Finset.mem_univ i₀)
    have h2 : ∑ x ∈ Finset.univ.erase i₀, (Finsupp.update g i₀ a) x
        = ∑ x ∈ Finset.univ.erase i₀, g x :=
      Finset.sum_congr rfl fun x hx ↦ by
        simp [Finsupp.coe_update, Function.update_of_ne (Finset.ne_of_mem_erase hx)]
    rw [show ((Finsupp.update g i₀ a) i₀) = a from by simp] at h1
    rw [h2, hg.1] at h1
    omega
  · rw [Finset.mem_coe, hmem] at hf
    ext x
    by_cases hx : x = i₀
    · subst hx; simp [hf.2]
    · simp [hx]
  · rw [Finset.mem_coe, hmem'] at hg
    ext x
    by_cases hx : x = i₀
    · subst hx
      have : g x = 0 := Finsupp.notMem_support_iff.mp
        (fun h ↦ (Finset.mem_erase.mp (hg.2 h)).1 rfl)
      simp [this]
    · simp [hx]

theorem sum_choose_apply_finsuppAntidiag {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card ι = n + 1) (i₀ : ι)
    (N k : ℕ) :
    ∑ f ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) N, (f i₀).choose k
      = (N + n).choose (n + k) := by
  have herase : #(Finset.univ.erase i₀ : Finset ι) = n := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, hcard]
    omega
  have hmaps : ∀ f ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) N,
      f i₀ ∈ Finset.range (N + 1) := by
    intro f hf
    rw [Finset.mem_finsuppAntidiag] at hf
    have : f i₀ ≤ ∑ x, f x := Finset.single_le_sum (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ i₀)
    have h1 : ∑ x, f x = N := hf.1
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hstep : ∀ a ∈ Finset.range (N + 1),
      (∑ f ∈ {f ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) N | f i₀ = a},
        (f i₀).choose k) = a.choose k * (N + n - 1 - a).choose (n - 1) := by
    intro a ha
    rw [Finset.mem_range] at ha
    rw [Finset.sum_congr rfl (fun f hf ↦ by rw [(Finset.mem_filter.mp hf).2]),
      Finset.sum_const, smul_eq_mul, card_fiber_finsuppAntidiag i₀ (by omega), mul_comm]
    congr 1
    rw [Finset.card_finsuppAntidiag_nat_eq_choose, herase]
    have h1 : n + (N - a) - 1 = N + n - 1 - a := by omega
    rw [h1, ← Nat.choose_symm (show N - a ≤ N + n - 1 - a by omega)]
    congr 1
    omega
  rw [Finset.sum_congr rfl hstep]
  have hext : ∑ a ∈ Finset.range (N + 1), a.choose k * (N + n - 1 - a).choose (n - 1)
      = ∑ a ∈ Finset.range (N + n - 1 + 1), a.choose k * (N + n - 1 - a).choose (n - 1) := by
    have hsub : Finset.range (N + 1) ⊆ Finset.range (N + n - 1 + 1) := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    refine Finset.sum_subset hsub (fun a ha ha' ↦ ?_)
    rw [Finset.mem_range] at ha ha'
    have : (N + n - 1 - a).choose (n - 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [this, Nat.mul_zero]
  rw [hext, Nat.sum_range_choose_mul_choose k (n - 1) (N + n - 1)]
  congr 1 <;> omega


theorem exp_neg_le_quadratic {t : ℝ} (ht : 0 ≤ t) : Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 := by
  have h1 : 1 + t + t ^ 2 / 2 ≤ Real.exp t := Real.quadratic_le_exp_of_nonneg ht
  have h2 : (0 : ℝ) < 1 + t + t ^ 2 / 2 := by positivity
  have h3 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-t), Real.exp_pos t, sq_nonneg t, sq_nonneg (t ^ 2)]

theorem sq_eq_two_mul_choose_add (k : ℕ) : k ^ 2 = 2 * k.choose 2 + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.choose_succ_succ k 1, Nat.choose_one_right]
      ring_nf
      ring_nf at ih
      omega

variable {n : ℕ}

theorem sum_exp_le (hn : 1 ≤ n) (hcard : Fintype.card ι = n + 1) (i₀ : ι)
    {N : ℕ} (hN : 1 ≤ N) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∑ f ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) N,
        Real.exp (-(lam * (f i₀ : ℝ) / N))
      ≤ #(Finset.finsuppAntidiag (Finset.univ : Finset ι) N) *
        Real.exp (-(lam / (n + 1)) + lam ^ 2 / ((n + 1) * (n + 2))
          + lam ^ 2 / (2 * N * (n + 1))) := by
  set A := Finset.finsuppAntidiag (Finset.univ : Finset ι) N with hA
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  -- the three moments
  have hC : (#A : ℕ) = (N + n).choose n := by
    simpa using sum_choose_apply_finsuppAntidiag hn hcard i₀ N 0
  have h1 : ∑ f ∈ A, (f i₀) = (N + n).choose (n + 1) := by
    simpa using sum_choose_apply_finsuppAntidiag hn hcard i₀ N 1
  have h2 : ∑ f ∈ A, (f i₀).choose 2 = (N + n).choose (n + 2) :=
    sum_choose_apply_finsuppAntidiag hn hcard i₀ N 2
  -- the two binomial relations, in ℝ
  have e1 : ((N + n).choose (n + 1) : ℝ) * ((n : ℝ) + 1)
      = ((N + n).choose n : ℝ) * N := by
    have := Nat.choose_succ_right_eq (N + n) n
    have h : N + n - n = N := by omega
    rw [h] at this
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) this
  have e2 : ((N + n).choose (n + 2) : ℝ) * ((n : ℝ) + 2)
      = ((N + n).choose (n + 1) : ℝ) * ((N : ℝ) - 1) := by
    have := Nat.choose_succ_right_eq (N + n) (n + 1)
    have h : N + n - (n + 1) = N - 1 := by omega
    rw [h] at this
    have hc : (((N - 1 : ℕ)) : ℝ) = (N : ℝ) - 1 := by
      have : (1 : ℕ) ≤ N := hN
      push_cast [Nat.cast_sub this]
      ring
    calc ((N + n).choose (n + 2) : ℝ) * ((n : ℝ) + 2)
        = (((N + n).choose (n + 1 + 1) * (n + 1 + 1) : ℕ) : ℝ) := by push_cast; ring
      _ = (((N + n).choose (n + 1) * (N - 1) : ℕ) : ℝ) := by rw [this]
      _ = ((N + n).choose (n + 1) : ℝ) * ((N : ℝ) - 1) := by push_cast [hc]; ring
  set C : ℝ := ((N + n).choose n : ℝ) with hCdef
  set S1 : ℝ := ((N + n).choose (n + 1) : ℝ) with hS1def
  set S2 : ℝ := ((N + n).choose (n + 2) : ℝ) with hS2def
  have hC0 : (0 : ℝ) ≤ C := by positivity
  have hcardC : (#A : ℝ) = C := by rw [hCdef, hC]
  -- the sum of the quadratic majorants
  have hsum : ∑ f ∈ A, (1 - lam * (f i₀ : ℝ) / N + (lam * (f i₀ : ℝ) / N) ^ 2 / 2)
      = C - lam / N * S1 + lam ^ 2 / (2 * N ^ 2) * (2 * S2 + S1) := by
    have hs1 : ∑ f ∈ A, ((f i₀ : ℕ) : ℝ) = S1 := by
      rw [← Nat.cast_sum, h1]
    have hs2 : ∑ f ∈ A, (((f i₀ : ℕ) : ℝ)) ^ 2 = 2 * S2 + S1 := by
      have : ∑ f ∈ A, (f i₀) ^ 2 = 2 * ((N + n).choose (n + 2)) + (N + n).choose (n + 1) := by
        rw [Finset.sum_congr rfl fun f _ ↦ sq_eq_two_mul_choose_add (f i₀),
          Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2]
      calc ∑ f ∈ A, (((f i₀ : ℕ) : ℝ)) ^ 2 = ((∑ f ∈ A, (f i₀) ^ 2 : ℕ) : ℝ) := by push_cast; ring
        _ = 2 * S2 + S1 := by rw [this]; push_cast; ring
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      hcardC]
    rw [show ∑ f ∈ A, lam * (f i₀ : ℝ) / N = lam / N * ∑ f ∈ A, ((f i₀ : ℕ) : ℝ) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun f _ ↦ by ring, hs1]
    have hq : ∑ f ∈ A, (lam * (f i₀ : ℝ) / N) ^ 2 / 2
        = lam ^ 2 / (2 * N ^ 2) * ∑ f ∈ A, (((f i₀ : ℕ) : ℝ)) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ ↦ ?_
      field_simp
    rw [hq, hs2]
  -- the algebra
  have hS1eq : S1 = C * N / ((n : ℝ) + 1) := by
    rw [eq_div_iff (ne_of_gt hn1)]; exact e1
  have h3 : S2 * (((n : ℝ) + 1) * ((n : ℝ) + 2)) = C * N * ((N : ℝ) - 1) := by
    rw [hS1eq] at e2
    field_simp at e2 ⊢
    linarith
  have key : C - lam / N * S1 + lam ^ 2 / (2 * N ^ 2) * (2 * S2 + S1)
      ≤ C * (1 + (-(lam / ((n : ℝ) + 1)) + lam ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))
        + lam ^ 2 / (2 * N * ((n : ℝ) + 1)))) := by
    rw [← sub_nonneg, hS1eq]
    have expand : C * (1 + (-(lam / ((n : ℝ) + 1)) + lam ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))
          + lam ^ 2 / (2 * N * ((n : ℝ) + 1))))
        - (C - lam / N * (C * N / ((n : ℝ) + 1))
          + lam ^ 2 / (2 * N ^ 2) * (2 * S2 + C * N / ((n : ℝ) + 1)))
        = lam ^ 2 * (C * N ^ 2 - S2 * (((n : ℝ) + 1) * ((n : ℝ) + 2)))
            / (N ^ 2 * (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
      field_simp
      ring
    rw [expand, h3]
    have : C * (N : ℝ) ^ 2 - C * N * ((N : ℝ) - 1) = C * N := by ring
    rw [this]
    positivity
  calc ∑ f ∈ A, Real.exp (-(lam * (f i₀ : ℝ) / N))
      ≤ ∑ f ∈ A, (1 - lam * (f i₀ : ℝ) / N + (lam * (f i₀ : ℝ) / N) ^ 2 / 2) :=
        Finset.sum_le_sum fun f _ ↦ exp_neg_le_quadratic (by positivity)
    _ = C - lam / N * S1 + lam ^ 2 / (2 * N ^ 2) * (2 * S2 + S1) := hsum
    _ ≤ C * (1 + (-(lam / ((n : ℝ) + 1)) + lam ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))
          + lam ^ 2 / (2 * N * ((n : ℝ) + 1)))) := key
    _ ≤ C * Real.exp (-(lam / ((n : ℝ) + 1)) + lam ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))
          + lam ^ 2 / (2 * N * ((n : ℝ) + 1))) := by
        gcongr
        linarith [Real.add_one_le_exp (-(lam / ((n : ℝ) + 1))
          + lam ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) + lam ^ 2 / (2 * N * ((n : ℝ) + 1)))]
    _ = _ := by rw [hcardC]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem card_le_of_subset_deviation (hn : 1 ≤ n) (hcard : Fintype.card ι = n + 1) (i₀ : ι)
    (d : κ → ℕ) (hd : ∀ h, 1 ≤ d h) {θ lam : ℝ} (hlam : 0 ≤ lam)
    (E : Finset (κ → ι →₀ ℕ))
    (hE : E ⊆ Fintype.piFinset fun h ↦ Finset.finsuppAntidiag (Finset.univ : Finset ι) (d h))
    (hEθ : ∀ J ∈ E, ∑ h, (J h i₀ : ℝ) / d h ≤ θ) :
    (#E : ℝ)
      ≤ #(Fintype.piFinset fun h ↦ Finset.finsuppAntidiag (Finset.univ : Finset ι) (d h)) *
        Real.exp (lam * θ - Fintype.card κ * (lam / ((n : ℝ) + 1))
          + Fintype.card κ * (lam ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)))
          + lam ^ 2 / (2 * ((n : ℝ) + 1)) * ∑ h, ((d h : ℝ))⁻¹) := by
  set A : κ → Finset (ι →₀ ℕ) :=
    fun h ↦ Finset.finsuppAntidiag (Finset.univ : Finset ι) (d h) with hAdef
  set P := Fintype.piFinset A with hPdef
  set g : (κ → ι →₀ ℕ) → ℝ := fun J ↦ Real.exp (lam * (θ - ∑ h, (J h i₀ : ℝ) / d h)) with hgdef
  have hsplit : ∀ J : κ → ι →₀ ℕ,
      g J = Real.exp (lam * θ) * ∏ h, Real.exp (-(lam * (J h i₀ : ℝ) / d h)) := by
    intro J
    rw [← Real.exp_sum, ← Real.exp_add]
    change Real.exp (lam * (θ - ∑ h, (J h i₀ : ℝ) / d h)) = _
    congr 1
    have hneg : ∑ x, -(lam * (J x i₀ : ℝ) / d x) = -(lam * ∑ h, (J h i₀ : ℝ) / d h) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun h _ ↦ by ring
    rw [hneg]
    ring
  have step1 : (#E : ℝ) ≤ ∑ J ∈ P, g J := by
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hE
      (fun J _ _ ↦ (Real.exp_pos _).le))
    have hcast : (#E : ℝ) = ∑ _J ∈ E, (1 : ℝ) := by simp
    rw [hcast]
    exact Finset.sum_le_sum fun J hJ ↦ Real.one_le_exp (mul_nonneg hlam (by linarith [hEθ J hJ]))
  have step2 : ∑ J ∈ P, g J
      = Real.exp (lam * θ) * ∏ h, ∑ j ∈ A h, Real.exp (-(lam * (j i₀ : ℝ) / d h)) := by
    rw [Finset.prod_univ_sum A (fun h j ↦ Real.exp (-(lam * (j i₀ : ℝ) / d h))), Finset.mul_sum]
    exact Finset.sum_congr rfl fun J _ ↦ hsplit J
  have step3 : ∏ h, ∑ j ∈ A h, Real.exp (-(lam * (j i₀ : ℝ) / d h))
      ≤ ∏ h : κ, ((#(A h) : ℝ) * Real.exp (-(lam / ((n : ℝ) + 1))
          + lam ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))
          + lam ^ 2 / (2 * (d h) * ((n : ℝ) + 1)))) := by
    refine Finset.prod_le_prod₀ (fun h _ ↦ Finset.sum_nonneg fun j _ ↦ (Real.exp_pos _).le)
      (fun h _ ↦ ?_)
    exact sum_exp_le hn hcard i₀ (hd h) hlam
  have hinv : ∀ h : κ, lam ^ 2 / (2 * (d h : ℝ) * ((n : ℝ) + 1))
      = lam ^ 2 / (2 * ((n : ℝ) + 1)) * ((d h : ℝ))⁻¹ := by
    intro h
    rw [show (2 * (d h : ℝ) * ((n : ℝ) + 1)) = 2 * ((n : ℝ) + 1) * (d h : ℝ) from by ring,
      ← div_div, div_eq_mul_inv]
  have hexp : ∑ _h : κ, (-(lam / ((n : ℝ) + 1))
        + lam ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)))
      + ∑ h : κ, lam ^ 2 / (2 * (d h) * ((n : ℝ) + 1))
      = -(Fintype.card κ * (lam / ((n : ℝ) + 1)))
        + Fintype.card κ * (lam ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)))
        + lam ^ 2 / (2 * ((n : ℝ) + 1)) * ∑ h, ((d h : ℝ))⁻¹ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_congr rfl
      (fun h _ ↦ hinv h), ← Finset.mul_sum]
    ring
  have step4 : ∏ h : κ, ((#(A h) : ℝ) * Real.exp (-(lam / ((n : ℝ) + 1))
        + lam ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) + lam ^ 2 / (2 * (d h) * ((n : ℝ) + 1))))
      = (#P : ℝ) * Real.exp (-(Fintype.card κ * (lam / ((n : ℝ) + 1)))
        + Fintype.card κ * (lam ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)))
        + lam ^ 2 / (2 * ((n : ℝ) + 1)) * ∑ h, ((d h : ℝ))⁻¹) := by
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, hPdef, Fintype.card_piFinset]
    push_cast
    rw [← hexp, Finset.sum_add_distrib]
  calc (#E : ℝ) ≤ ∑ J ∈ P, g J := step1
    _ = Real.exp (lam * θ) * ∏ h, ∑ j ∈ A h, Real.exp (-(lam * (j i₀ : ℝ) / d h)) := step2
    _ ≤ Real.exp (lam * θ) * ∏ h : κ, ((#(A h) : ℝ) * Real.exp (-(lam / ((n : ℝ) + 1))
          + lam ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))
          + lam ^ 2 / (2 * (d h) * ((n : ℝ) + 1)))) := by
        exact mul_le_mul_of_nonneg_left step3 (Real.exp_pos _).le
    _ = Real.exp (lam * θ) * ((#P : ℝ) * Real.exp (-(Fintype.card κ * (lam / ((n : ℝ) + 1)))
          + Fintype.card κ * (lam ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)))
          + lam ^ 2 / (2 * ((n : ℝ) + 1)) * ∑ h, ((d h : ℝ))⁻¹)) := by rw [step4]
    _ = (#P : ℝ) * Real.exp (lam * θ - Fintype.card κ * (lam / ((n : ℝ) + 1))
          + Fintype.card κ * (lam ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)))
          + lam ^ 2 / (2 * ((n : ℝ) + 1)) * ∑ h, ((d h : ℝ))⁻¹) := by
        rw [← mul_assoc, mul_comm (Real.exp (lam * θ)) ((#P : ℝ)), mul_assoc, ← Real.exp_add]
        congr 2
        ring

theorem card_le_of_subset_eta (hn : 1 ≤ n) (hcard : Fintype.card ι = n + 1) (i₀ : ι)
    (d : κ → ℕ) (hd : ∀ h, 1 ≤ d h) {η : ℝ} (hη : 0 ≤ η)
    (E : Finset (κ → ι →₀ ℕ))
    (hE : E ⊆ Fintype.piFinset fun h ↦ Finset.finsuppAntidiag (Finset.univ : Finset ι) (d h))
    (hEθ : ∀ J ∈ E, ∑ h, (J h i₀ : ℝ) / d h
      ≤ Fintype.card κ / ((n : ℝ) + 1) - Fintype.card κ * η) :
    (#E : ℝ)
      ≤ #(Fintype.piFinset fun h ↦ Finset.finsuppAntidiag (Finset.univ : Finset ι) (d h)) *
        Real.exp (-(((n : ℝ) + 1) * ((n : ℝ) + 2) * η ^ 2 * Fintype.card κ / 4)
          + (η * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2) ^ 2 / (2 * ((n : ℝ) + 1))
            * ∑ h, ((d h : ℝ))⁻¹) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hθ : (η * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2)
        * (Fintype.card κ / ((n : ℝ) + 1) - Fintype.card κ * η)
      - Fintype.card κ * ((η * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2) / ((n : ℝ) + 1))
      + Fintype.card κ * ((η * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2) ^ 2
          / (((n : ℝ) + 1) * ((n : ℝ) + 2)))
      = -(((n : ℝ) + 1) * ((n : ℝ) + 2) * η ^ 2 * Fintype.card κ / 4) := by
    field_simp
    ring
  refine (card_le_of_subset_deviation hn hcard i₀ d hd
    (show (0:ℝ) ≤ η * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 by positivity) E hE hEθ).trans_eq ?_
  rw [hθ]

end Finset
