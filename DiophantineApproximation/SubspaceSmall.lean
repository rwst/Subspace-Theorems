/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SubspaceGap

-- Used only inside proofs.
import ArithmeticHeights.Absolute
import DiophantineApproximation.DetCount
import DiophantineApproximation.DetPartition
import DiophantineApproximation.PlacesOverInfinite
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Small solutions: the second gap principle

**Layer 9.3.** Evertse, "On the Quantitative Subspace Theorem", Proposition 4.2 and Theorem 2.2.
Under the normalization (2.4) of a system (`NumberField.IsNormalizedSystem`) of degree `d` over
`ℚ`:

* for `Q ≥ 1` the solutions whose absolute affine height lies in `[Q, 2 Q ^ (1 + δ / (2 n)))` lie
  in at most `(90 n) ^ (n d)` proper subspaces
  (`NumberField.exists_finset_submodule_of_window_two_mul`, **the second gap principle**);
* the solutions that are not large (`NumberField.IsLargeSolution`) lie in at most
  `δ⁻¹ ((10³ n) ^ (n d) + 4 n log log (4 H))` proper subspaces
  (`NumberField.exists_finset_submodule_of_not_isLargeSolution`, **Theorem 2.2**);
* over `ℚ`, `200 ^ n` subspaces per window (`Rat.exists_finset_submodule_of_window_two_mul`) and
  `δ⁻¹ (10 ^ (3 n) + 4 n log log (4 H))` for the small solutions
  (`Rat.exists_finset_submodule_of_not_isLargeSolution`), **Evertse's refinement over `ℚ`**.

The second gap principle is the first one (Layer 9.2) with one more ingredient: at each infinite
place the points are first sorted by Evertse's Lemma 4.3 (`Matrix.exists_det_partition`), applied
to the values of the forms divided by their bounds, so that within a class the determinant at that
place is `M⁻¹` times smaller than the trivial bound, with `M = (9/2) ^ (n / 2) > 2 ^ n`. That
saving pays for the factor `2` in the window. Theorem 2.2 covers `[1, max (2 H) (n ^ (2 n / δ)))`
by two chains of windows, `n ^ (2 n / δ) ^ ((1 + δ / (2 n)) ^ h)` above `n ^ (2 n / δ)` for 9.2 and
`2 ^ ((2 n / δ) ((1 + δ / (2 n)) ^ h - 1))` below it for Proposition 4.2. Over `ℚ` the partition
of Lemma 4.3 is replaced by the lattice-point count of Lemma 4.5 (`DetCount.lean`), which uses the
bounds on the determinants at all the places at once.

## Main results

* `NumberField.IsNormalizedSystem.two_le_card`: a normalized system has at least two forms.
* `NumberField.exists_finset_submodule_of_window_two_mul`: **Proposition 4.2**.
* `NumberField.exists_finset_submodule_of_not_isLargeSolution_of_window`: Theorem 2.2 from any
  bound `P` on the subspaces per window of the second gap principle.
* `NumberField.exists_finset_submodule_of_not_isLargeSolution`: **Theorem 2.2**.
* `Rat.exists_finset_submodule_of_window_two_mul`: **Proposition 4.2 over `ℚ`**, `200 ^ n`.
* `Rat.exists_finset_submodule_of_not_isLargeSolution`: **Theorem 2.2 over `ℚ`**,
  `δ⁻¹ (10 ^ (3 n) + 4 n log log (4 H))`.

## Implementation notes

⚠ **`n ≥ 2` is not a hypothesis: the normalization forces it.** For `n = 1` the last condition of
(2.4) makes each exponent equal to `s(v)`, so the weight is `∑ s(v) = 1`, not `≤ -δ`
(`NumberField.IsNormalizedSystem.two_le_card`). Lemma 4.3 is false for `n = 1`.

⚠ **The infinite places become complex embeddings.** Lemma 4.3 lives in `ℂⁿ`, and the absolute
value `w v` of `F` over an infinite place `v` of `K` is `|φ ·|` for a ring homomorphism
`φ : F →+* ℂ` (Layer 0.1, `NumberField.exists_infinitePlace_eq_of_liesOver`). Evertse's vector
`ϕ_v(x) = (Q ^ (-c_{iv} / s(v)) L_i(x))_i` is taken here as `(φ (L_i x) / t_i)_i` with
`t_i = (C_v Q ^ (c_{iv} + s(v) δ / (2 n))) ^ (1 / mult v)`, which is the same normalization
written with this repository's constants, and puts every point of the window in the ball of
radius `2`.

⚠ **The count is Evertse's, with a different bookkeeping of the windows.** The number of windows
above `n ^ (2 n / δ)` is at most `4 n δ⁻¹ log log (4 H)`, as in the source. Below it, the source's
`4 n δ⁻¹ log (3 log n)` is not proved; the windows are bounded by `δ⁻¹ (1 + 4 n (n - 1))` instead,
from `log (1 + log₂ n) ≤ log₂ n ≤ n - 1`. Over `K` the factor `(10³ n / (90 n)) ^ (n d) ≥ 11 ^ n`
absorbs it, and over `ℚ` the factor `10 ^ (3 n) / 200 ^ n = 5 ^ n` does.

⚠ **Over `ℚ` the determinant at the infinite place carries `2 ^ n n!`, not Evertse's
`2 n ^ (n / 2)`.** The window costs `2 ^ s(v)` per form, so `2 ^ n` in all (the source writes a
single `2`), and the Leibniz bound replaces Hadamard's. With Lemma 4.5's constant `100 ^ n` this
would give `100 ^ n (2 ^ n n!) ^ (1 / (n - 1)) ≤ 400 ^ n`, not `200 ^ n`; the proof of Lemma 4.5
here gives `3 ^ n (4 n² + 2) ²` (`Rat.exists_finset_submodule_of_det_le`), and
`3 ^ n (4 n² + 2)² · 4 n ≤ 200 ^ n` recovers the source's count.

## References

J.-H. Evertse, *On the Quantitative Subspace Theorem*, Zap. Nauchn. Sem. POMI **377** (2010),
217–240; J. Math. Sci. **171** (2010), 824–837 (arXiv:1008.2268), Proposition 4.2, Lemmas 4.3
and 4.5 and Theorem 2.2.

This is Layer 9.3 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height IsDedekindDomain Module

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι]

/-- **A normalized system has at least two forms.** With one form the last condition of (2.4)
makes every exponent `s(v)`, and the weight `∑ s(v) = 1` is not negative. -/
theorem IsNormalizedSystem.two_le_card {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ} {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)}
    {C : InfinitePlace K ⊕ S → ℝ} {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) : 2 ≤ Fintype.card ι := by
  by_contra h
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  obtain ⟨i₀, -⟩ := hN.exists_exponent_eq (.inl v)
  have : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.1 (by omega)
  have hc : ∀ p, c p i₀ = systemExponent S p := fun p ↦ by
    obtain ⟨i, hi⟩ := hN.exists_exponent_eq p
    rwa [Subsingleton.elim i i₀] at hi
  have hw : systemWeight c = 1 := by
    rw [systemWeight, ← sum_systemExponent S]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [← hc p, Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ _) fun i _ hi ↦
      absurd (Subsingleton.elim i i₀) hi]
  linarith [hN.weight_le, hN.delta_pos]

private theorem exists_ringHom_complex (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : ∃ φ : F →+* ℂ, ∀ a, w a = ‖φ a‖ := by
  obtain ⟨w', hw'⟩ := exists_infinitePlace_eq_of_liesOver v w
  exact ⟨w'.embedding, fun a ↦ by rw [InfinitePlace.norm_embedding_eq, ← hw']; rfl⟩

private theorem card_infinitePlace_le : Fintype.card (InfinitePlace K) ≤ finrank ℚ K := by
  rw [← InfinitePlace.sum_mult_eq, Fintype.card_eq_sum_ones]
  exact Finset.sum_le_sum fun v _ ↦ Nat.one_le_iff_ne_zero.2 InfinitePlace.mult_ne_zero

/-- **The second gap principle** (Evertse, Proposition 4.2). Under the normalization (2.4) and for
`Q ≥ 1`, the solutions of the system whose absolute affine height lies in
`[Q, 2 Q ^ (1 + δ / (2 n)))` lie in at most `(90 n) ^ (n [K : ℚ])` proper subspaces of `Kⁿ`. -/
theorem exists_finset_submodule_of_window_two_mul
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∃ T : Finset (Submodule K (ι → K)),
      (T.card : ℝ) ≤ (90 * Fintype.card ι) ^ (Fintype.card ι * finrank ℚ K) ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∀ x ∈ systemSet S w L C c,
        Q ≤ mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) →
        mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) < 2 * Q ^ (1 + δ / (2 * Fintype.card ι)) →
        ∃ U ∈ T, x ∈ U := by
  classical
  set n := Fintype.card ι with hn
  set d := finrank ℚ K with hd
  set ε := δ / (2 * n) with hε
  have hn2 : 2 ≤ n := hN.two_le_card
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hδ := hN.delta_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hd0' : (0 : ℝ) < d := by exact_mod_cast (Module.finrank_pos : 0 < d)
  have hQ0 : 0 < Q := by linarith
  set Q' := Q ^ (d : ℝ) with hQ'
  have hQ'1 : 1 ≤ Q' := Real.one_le_rpow hQ hd0'.le
  have hQ'0 : 0 < Q' := by linarith
  -- The window, in `mulHeightAff`.
  set W : Set (ι → K) := {x | x ∈ systemSet S w L C c ∧
    Q ≤ mulHeightAff x ^ ((d : ℝ)⁻¹) ∧ mulHeightAff x ^ ((d : ℝ)⁻¹) < 2 * Q ^ (1 + ε)} with hW
  have hlo' : ∀ x ∈ W, Q' ≤ mulHeightAff x := fun x hx ↦ by
    have := Real.rpow_le_rpow hQ0.le hx.2.1 hd0'.le
    rwa [Real.rpow_inv_rpow (mulHeightAff_pos _).le hd0'.ne'] at this
  have hhi' : ∀ x ∈ W, mulHeightAff x ≤ 2 ^ d * Q' ^ (1 + ε) := fun x hx ↦ by
    have := Real.rpow_le_rpow (Real.rpow_nonneg (mulHeightAff_pos _).le _) hx.2.2.le hd0'.le
    have e : (2 * Q ^ (1 + ε)) ^ (d : ℝ) = 2 ^ d * Q' ^ (1 + ε) := by
      rw [Real.mul_rpow zero_le_two (Real.rpow_nonneg hQ0.le _), Real.rpow_natCast, hQ',
        ← Real.rpow_mul hQ0.le, ← Real.rpow_mul hQ0.le, mul_comm (1 + ε)]
    rwa [Real.rpow_inv_rpow (mulHeightAff_pos _).le hd0'.ne', e] at this
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  have hrow : ∀ x ∈ W, ∀ p i, systemValue S w L p i x ≤
      C p * (2 ^ d) ^ systemExponent S p * Q' ^ (c p i + systemExponent S p * ε) := fun x hx p i ↦
    systemValue_le_rpow_of_window hx.1 (hN.const_pos p).le (hN.exponent_le p i) hQ'0 h2d
      (hlo' x hx) (hhi' x hx)
  -- The complex embeddings of the infinite places, and the normalized vectors.
  have hφex : ∀ v : InfinitePlace K, ∃ φ : F →+* ℂ, ∀ a, w v.1 a = ‖φ a‖ := fun v ↦ by
    have := hwInf v
    exact exists_ringHom_complex v (w v.1)
  choose φ hφ using hφex
  set t : InfinitePlace K → ι → ℝ := fun v i ↦
    (C (.inl v) * Q' ^ (c (.inl v) i + systemExponent S (.inl v) * ε)) ^ ((v.mult : ℝ)⁻¹)
    with ht
  have hbase0 : ∀ v i, 0 < C (.inl v) * Q' ^ (c (.inl v) i + systemExponent S (.inl v) * ε) :=
    fun v i ↦ mul_pos (hN.const_pos _) (Real.rpow_pos_of_pos hQ'0 _)
  have ht0 : ∀ v i, 0 < t v i := fun v i ↦ Real.rpow_pos_of_pos (hbase0 v i) _
  have htpow : ∀ v i, t v i ^ v.mult =
      C (.inl v) * Q' ^ (c (.inl v) i + systemExponent S (.inl v) * ε) := fun v i ↦
    Real.rpow_inv_natCast_pow (hbase0 v i).le InfinitePlace.mult_ne_zero
  set ϕ : InfinitePlace K → (ι → K) → ι → ℂ := fun v x i ↦
    φ v (L v.1 i fun k ↦ algebraMap K F (x k)) / (t v i : ℂ) with hϕ
  have hϕle : ∀ v, ∀ x ∈ W, ‖ϕ v x‖ ≤ 2 := fun v x hx ↦ by
    refine (pi_norm_le_iff_of_nonneg zero_le_two).2 fun i ↦ ?_
    have hm0 : v.mult ≠ 0 := InfinitePlace.mult_ne_zero
    have hval : ‖φ v (L v.1 i fun k ↦ algebraMap K F (x k))‖ ^ v.mult ≤ (2 * t v i) ^ v.mult := by
      rw [mul_pow, htpow, ← hφ]
      have := hrow x hx (.inl v) i
      have hs : ((2 : ℝ) ^ d) ^ systemExponent S (.inl v) = 2 ^ v.mult := by
        change ((2 : ℝ) ^ d) ^ ((v.mult : ℝ) / d) = _
        rw [← Real.rpow_natCast 2 d, ← Real.rpow_mul zero_le_two,
          mul_div_cancel₀ _ hd0'.ne', Real.rpow_natCast]
      rw [hs] at this
      calc w v.1 (L v.1 i fun k ↦ algebraMap K F (x k)) ^ v.mult = systemValue S w L (.inl v) i x :=
            rfl
        _ ≤ _ := this
        _ = _ := by ring
    have := (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith [ht0 v i]) hm0).1 hval
    rw [hϕ]
    simp only
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (ht0 v i).le,
      div_le_iff₀ (ht0 v i)]
    exact this
  -- Lemma 4.3 at each infinite place.
  set Mv : ℝ := (9 / 2 : ℝ) ^ ((n : ℝ) / 2) with hMv
  have hMv1 : 1 ≤ Mv := Real.one_le_rpow (by norm_num) (by positivity)
  have hMv0 : 0 < Mv := by linarith
  obtain ⟨α, _, f, hcardα, hdetα⟩ := Matrix.exists_det_partition (ι := ι) hn2 hMv1
  set cls : (ι → K) → InfinitePlace K → α := fun x v ↦ f (ϕ v x) with hcls
  set U : (InfinitePlace K → α) → Submodule K (ι → K) := fun κ ↦
    Submodule.span K {x | x ∈ W ∧ cls x = κ} with hU
  set g : ℝ := 2 ^ n / Mv with hg
  have hg0 : 0 < g := by positivity
  have hg1 : g < 1 := by
    rw [hg, div_lt_one hMv0, hMv]
    calc (2 : ℝ) ^ n = (4 : ℝ) ^ ((n : ℝ) / 2) := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul zero_le_two,
            mul_div_cancel₀ _ two_ne_zero, Real.rpow_natCast]
      _ < (9 / 2 : ℝ) ^ ((n : ℝ) / 2) := Real.rpow_lt_rpow (by norm_num) (by norm_num)
          (by positivity)
  -- Within a class every determinant vanishes.
  have hdet0 : ∀ κ, ∀ y : ι → ι → K, (∀ j, y j ∈ {x | x ∈ W ∧ cls x = κ}) →
      (Pi.basisFun K ι).det y = 0 := fun κ y hy ↦ by
    refine det_eq_zero_of_systemAbs_det_le S w hwInf hwFin hN hQ'1 hg0 ?_ y
      (fun j k ↦ (hy j).1.1.1 k) fun p ↦ ?_
    · calc g ^ d * Q' ^ (-(δ / 2)) ≤ g ^ d * 1 := mul_le_mul_of_nonneg_left
            (Real.rpow_le_one_of_one_le_of_nonpos hQ'1 (by linarith)) (by positivity)
        _ < 1 := by rw [mul_one]; exact pow_lt_one₀ hg0.le hg1 (Module.finrank_pos).ne'
    rcases p with v | v
    · -- An infinite place: Lemma 4.3.
      have hm0 : v.mult ≠ 0 := InfinitePlace.mult_ne_zero
      set Mp := systemMatrix S L y (.inl v) with hMp
      set P : Matrix ι ι ℂ := Matrix.of fun j ↦ ϕ v (y j) with hP
      have hPeq : P = ((φ v).mapMatrix Mp).transpose *
          Matrix.diagonal fun i ↦ ((t v i : ℂ))⁻¹ := by
        ext j i
        simp [hP, hϕ, hMp, systemMatrix, Matrix.mul_diagonal, div_eq_mul_inv, systemPlace]
      have hdetP : P.det = φ v Mp.det * ∏ i, ((t v i : ℂ))⁻¹ := by
        rw [hPeq, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, RingHom.map_det]
      have hcl : ∀ j k, f (ϕ v (y j)) = f (ϕ v (y k)) := fun j k ↦ by
        have hj := congrFun (hy j).2 v
        have hk := congrFun (hy k).2 v
        simp only [hcls] at hj hk
        rw [hj, hk]
      have hPle : ‖P.det‖ ≤ Mv⁻¹ * 2 ^ n := by
        calc ‖P.det‖ ≤ Mv⁻¹ * ∏ j, ‖ϕ v (y j)‖ := hdetα _ hcl
          _ ≤ Mv⁻¹ * ∏ _j : ι, (2 : ℝ) :=
              mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
                fun j _ ↦ hϕle v (y j) (hy j).1) (inv_nonneg.2 hMv0.le)
          _ = Mv⁻¹ * 2 ^ n := by rw [Finset.prod_const, Finset.card_univ]
      have hprodt : ‖∏ i, ((t v i : ℂ))⁻¹‖ = (∏ i, t v i)⁻¹ := by
        rw [norm_prod, ← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (ht0 v i).le]
      have htprod : 0 < ∏ i, t v i := Finset.prod_pos fun i _ ↦ ht0 v i
      have hφdet : ‖φ v Mp.det‖ ≤ g * ∏ i, t v i := by
        have := hPle
        rw [hdetP, norm_mul, hprodt, mul_inv_le_iff₀ htprod] at this
        calc ‖φ v Mp.det‖ ≤ Mv⁻¹ * 2 ^ n * ∏ i, t v i := this
          _ = g * ∏ i, t v i := by rw [hg, div_eq_inv_mul]
      have hexp : systemExponent S (.inl v) * d = v.mult := by
        change (v.mult : ℝ) / d * d = v.mult
        rw [div_mul_cancel₀ _ hd0'.ne']
      rw [hexp, Real.rpow_natCast]
      calc systemAbs S w (.inl v) Mp.det = ‖φ v Mp.det‖ ^ v.mult := by
            change w v.1 Mp.det ^ v.mult = _
            rw [hφ]
        _ ≤ (g * ∏ i, t v i) ^ v.mult := pow_le_pow_left₀ (norm_nonneg _) hφdet _
        _ = g ^ v.mult * ∏ i, (C (.inl v) *
              Q' ^ (c (.inl v) i + systemExponent S (.inl v) * (δ / (2 * n)))) := by
            rw [mul_pow, ← Finset.prod_pow]
            congr 1
            refine Finset.prod_congr rfl fun i _ ↦ ?_
            rw [htpow]
    · -- A finite place: the ultrametric Leibniz bound.
      have h := systemAbs_det_le S w hwFin (.inr v) (systemMatrix S L y (.inr v))
        (r := fun i ↦ C (.inr v) * Q' ^ (c (.inr v) i + systemExponent S (.inr v) * ε))
        (fun i ↦ mul_nonneg (hN.const_pos _).le (Real.rpow_nonneg hQ'0.le _)) fun i j ↦ by
          have := hrow (y j) (hy j).1 (.inr v) i
          rw [show systemExponent S (.inr v) = 0 from rfl, Real.rpow_zero, mul_one] at this
          exact this
      simp only [show systemExponent S (.inr v) = 0 from rfl, zero_mul, Real.rpow_zero,
        one_mul] at h ⊢
      exact h
  have hUne : ∀ κ, U κ ≠ ⊤ := fun κ ↦ span_ne_top_of_forall_det_eq_zero (hdet0 κ)
  refine ⟨Finset.univ.image U, ?_, fun V hV ↦ ?_, fun x hx hlo hhi ↦ ?_⟩
  · -- The count.
    have h2n : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hB1 : (1 : ℝ) ≤ (20 * n) ^ n * Mv ^ 2 := one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (by linarith)) (one_le_pow₀ hMv1)
    have hB : (20 * (n : ℝ)) ^ n * Mv ^ 2 = (90 * n) ^ n := by
      rw [hMv, ← Real.rpow_natCast ((9 / 2 : ℝ) ^ ((n : ℝ) / 2)) 2, ← Real.rpow_mul (by norm_num),
        show (n : ℝ) / 2 * ((2 : ℕ) : ℝ) = ((n : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
        ← mul_pow]
      congr 1
      ring
    calc ((Finset.univ.image U).card : ℝ) ≤ (Finset.univ : Finset (InfinitePlace K → α)).card :=
          by exact_mod_cast Finset.card_image_le
      _ = (Fintype.card α : ℝ) ^ Fintype.card (InfinitePlace K) := by
          rw [Finset.card_univ, Fintype.card_fun]; push_cast; ring
      _ ≤ ((20 * n) ^ n * Mv ^ 2) ^ Fintype.card (InfinitePlace K) :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hcardα _
      _ ≤ ((20 * n) ^ n * Mv ^ 2) ^ d := pow_le_pow_right₀ hB1 card_infinitePlace_le
      _ = (90 * n) ^ (n * d) := by rw [hB, pow_mul]
  · obtain ⟨κ, -, rfl⟩ := Finset.mem_image.1 hV
    exact hUne κ
  · exact ⟨U (cls x), Finset.mem_image_of_mem _ (Finset.mem_univ _),
      Submodule.subset_span ⟨⟨hx, hlo, hhi⟩, rfl⟩⟩

/-- The number of steps `(1 + e) ^ h` needs to pass `r`. -/
private theorem le_pow_ceil {e r : ℝ} (he : 0 < e) (hr : 0 < r) :
    r ≤ (1 + e) ^ ⌈Real.log r / Real.log (1 + e)⌉₊ := by
  have hl : 0 < Real.log (1 + e) := Real.log_pos (by linarith)
  rw [← Real.log_le_log_iff hr (by positivity), Real.log_pow]
  calc Real.log r = Real.log r / Real.log (1 + e) * Real.log (1 + e) := by field_simp
    _ ≤ ⌈Real.log r / Real.log (1 + e)⌉₊ * Real.log (1 + e) :=
        mul_le_mul_of_nonneg_right (Nat.le_ceil _) hl.le

/-- And that number is at most `1 + 2 log r / e`, for `e ≤ 1`. -/
private theorem ceil_div_log_le {e x : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hx : 0 ≤ x) :
    (⌈x / Real.log (1 + e)⌉₊ : ℝ) ≤ 1 + 2 * x / e := by
  have hl : e / 2 ≤ Real.log (1 + e) := by
    have := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + e by linarith)
    have h2 : e / 2 ≤ 1 - (1 + e)⁻¹ := by
      rw [show 1 - (1 + e)⁻¹ = e / (1 + e) by field_simp; ring,
        div_le_div_iff₀ two_pos (by linarith)]
      nlinarith
    linarith
  have hy : x / Real.log (1 + e) ≤ 2 * x / e :=
    calc x / Real.log (1 + e) ≤ x / (e / 2) :=
          div_le_div_of_nonneg_left hx (by positivity) hl
      _ = 2 * x / e := by ring
  have hl0 : 0 < Real.log (1 + e) := Real.log_pos (by linarith)
  have := Nat.ceil_lt_add_one (div_nonneg hx hl0.le)
  linarith

private theorem one_add_eight_mul_sq_le (n : ℕ) (hn : 2 ≤ n) : 1 + 8 * n ^ 2 ≤ 11 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ 11 m]; nlinarith [ih, hm]

/-- **Theorem 2.2 from a second gap principle.** Under the normalization (2.4), if for every
`Q ≥ 1` the solutions in the window `[Q, 2 Q ^ (1 + δ / (2 n)))` lie in at most `P` proper
subspaces, then the solutions that are not large lie in at most
`δ⁻¹ ((1 + 4 n (n - 1)) P + 4 n log log (4 H))` of them. Those above `n ^ (2 n / δ)` are covered
by 9.2, one subspace for each of at most `4 n δ⁻¹ log log (4 H)` windows, and those below by at
most `δ⁻¹ (1 + 4 n (n - 1))` windows of the second gap principle. -/
theorem exists_finset_submodule_of_not_isLargeSolution_of_window
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) {P : ℝ} (hP0 : 0 ≤ P)
    (hwin : ∀ Q : ℝ, 1 ≤ Q → ∃ T : Finset (Submodule K (ι → K)), (T.card : ℝ) ≤ P ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∀ x ∈ systemSet S w L C c,
        Q ≤ mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) →
        mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) < 2 * Q ^ (1 + δ / (2 * Fintype.card ι)) →
        ∃ U ∈ T, x ∈ U) :
    ∃ T : Finset (Submodule K (ι → K)),
      (T.card : ℝ) ≤ δ⁻¹ * ((1 + 4 * Fintype.card ι * (Fintype.card ι - 1)) * P +
        4 * Fintype.card ι * Real.log (Real.log (4 * H))) ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x ∈ systemSet S w L C c, ¬ IsLargeSolution H δ x → ∃ U ∈ T, x ∈ U := by
  classical
  set n := Fintype.card ι with hn
  set d := finrank ℚ K with hd
  set e := δ / (2 * n) with he
  have hn2 : 2 ≤ n := hN.two_le_card
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hδ := hN.delta_pos
  have hδ1 := hN.delta_le_one
  have h2n : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn0 : (0 : ℝ) < n := by linarith
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 := by
    rw [he, div_le_one (by positivity)]; linarith
  have hk : 2 / e = 4 * n / δ := by rw [he]; field_simp; ring
  have hk8 : 8 ≤ 4 * n / δ := by rw [le_div_iff₀ hδ]; nlinarith
  have hH1 : 1 ≤ H := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
    exact (one_le_absMulHeight₁ _).trans (hN.height_le (.inl v) i i)
  have hlog2 : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  set q0 : ℝ := (n : ℝ) ^ (2 * n / δ) with hq0def
  have hq0 : 1 < q0 := Real.one_lt_rpow (by linarith) (by positivity)
  have hlq0 : 0 < Real.log q0 := Real.log_pos hq0
  have hlogq0 : 2 ≤ Real.log q0 := by
    rw [hq0def, Real.log_rpow hn0]
    have h4 : 4 ≤ 2 * (n : ℝ) / δ := by rw [le_div_iff₀ hδ]; nlinarith
    have hl : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos h2n
    nlinarith
  set X := max (2 * H) q0 with hX
  have hXq0 : q0 ≤ X := le_max_right _ _
  -- The chain above `n ^ (2 n / δ)`: the first gap principle.
  set a1 : ℕ → ℝ := fun h ↦ q0 ^ ((1 + e) ^ h) with ha1def
  have ha1 : ∀ h, a1 (h + 1) = a1 h ^ (1 + δ / (2 * Fintype.card ι)) := fun h ↦ by
    change q0 ^ ((1 + e) ^ (h + 1)) = (q0 ^ ((1 + e) ^ h)) ^ (1 + δ / (2 * Fintype.card ι))
    rw [← Real.rpow_mul (by linarith : (0 : ℝ) ≤ q0), pow_succ]
  have ha1q : ∀ h, q0 ≤ a1 h := fun h ↦ by
    conv_lhs => rw [← Real.rpow_one q0]
    exact Real.rpow_le_rpow_of_exponent_le hq0.le (one_le_pow₀ (by linarith))
  have hU1 := fun h ↦ exists_submodule_ne_top_of_window S w hwInf hwFin hN (ha1q h)
  choose U1 hU1top hU1 using hU1
  set rA := Real.log X / Real.log q0 with hrA
  set A := ⌈Real.log rA / Real.log (1 + e)⌉₊ with hA
  have hrA1 : 1 ≤ rA := by
    rw [hrA, le_div_iff₀ hlq0, one_mul]; exact Real.log_le_log (by linarith) hXq0
  obtain ⟨T1, hT1card, hT1top, hT1⟩ := exists_finset_submodule_of_chain
    (P := (· ∈ systemSet S w L C c)) (ht := fun x ↦ mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹)) a1
    (fun h ↦ {U1 h}) (fun h U hU ↦ (Finset.mem_singleton.1 hU) ▸ hU1top h)
    (fun h x hx h1 h2 ↦ ⟨U1 h, Finset.mem_singleton_self _,
      hU1 h x hx h1 (by rw [← ha1]; exact h2)⟩)
    A
  have haA : X ≤ a1 A := by
    have := le_pow_ceil he0 (show 0 < rA by linarith)
    calc X = q0 ^ rA := by
          rw [hrA, Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ _ hlq0.ne',
            Real.exp_log (by linarith)]
      _ ≤ a1 A := Real.rpow_le_rpow_of_exponent_le hq0.le this
  have hl4H : 1 ≤ Real.log (4 * H) := by
    have : Real.log 4 ≤ Real.log (4 * H) := Real.log_le_log (by norm_num) (by linarith)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hAle : (A : ℝ) ≤ 4 * n / δ * Real.log (Real.log (4 * H)) := by
    by_cases hXq : X ≤ q0
    · have hXe : X = q0 := le_antisymm hXq hXq0
      have hA0 : A = 0 := by
        rw [hA, hrA, hXe, div_self hlq0.ne', Real.log_one, zero_div, Nat.ceil_zero]
      rw [hA0, Nat.cast_zero]
      exact mul_nonneg (by positivity) (Real.log_nonneg hl4H)
    · push Not at hXq
      have hX2H : X = 2 * H := by
        rcases max_choice (2 * H) q0 with h | h
        · exact h
        · exact absurd h hXq.ne'
      have hAb := ceil_div_log_le he0 he1 (Real.log_nonneg hrA1)
      rw [show 2 * Real.log rA / e = 4 * n / δ * Real.log rA by rw [he]; field_simp; ring] at hAb
      have hlogrA : Real.log rA ≤ Real.log (Real.log (4 * H)) - Real.log (Real.log q0) := by
        rw [hrA, Real.log_div (Real.log_pos (by linarith)).ne' hlq0.ne']
        have : Real.log (Real.log X) ≤ Real.log (Real.log (4 * H)) :=
          Real.log_le_log (Real.log_pos (by linarith))
            (Real.log_le_log (by linarith) (by rw [hX2H]; linarith))
        linarith
      have hllq0 : 1 / 2 ≤ Real.log (Real.log q0) := by
        have := Real.log_le_log two_pos hlogq0
        linarith
      have hk0 : 0 ≤ 4 * (n : ℝ) / δ := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hlogrA hk0, mul_le_mul_of_nonneg_left hllq0 hk0]
  -- The chain below `n ^ (2 n / δ)`: the second gap principle.
  set a2 : ℕ → ℝ := fun h ↦ 2 ^ (2 * n / δ * ((1 + e) ^ h - 1)) with ha2def
  have ha2 : ∀ h, a2 (h + 1) = 2 * a2 h ^ (1 + δ / (2 * Fintype.card ι)) := fun h ↦ by
    simp only [ha2def]
    rw [← Real.rpow_mul zero_le_two]
    rw [show (2 : ℝ) * 2 ^ (2 * n / δ * ((1 + e) ^ h - 1) * (1 + δ / (2 * Fintype.card ι))) =
      2 ^ (1 + 2 * n / δ * ((1 + e) ^ h - 1) * (1 + δ / (2 * Fintype.card ι))) by
        rw [Real.rpow_add two_pos, Real.rpow_one]]
    congr 1
    rw [pow_succ, ← hn, ← he, he]
    field_simp
    ring
  have h1e : ∀ h : ℕ, 1 ≤ (1 + e) ^ h := fun h ↦ one_le_pow₀ (by linarith)
  have ha21 : ∀ h, 1 ≤ a2 h := fun h ↦ Real.one_le_rpow one_le_two
    (mul_nonneg (by positivity) (by linarith [h1e h]))
  have ha20 : a2 0 = 1 := by simp [ha2def]
  have hT2 := fun h ↦ hwin (a2 h) (ha21 h)
  choose T2 hT2card hT2top hT2 using hT2
  set rB := 1 + Real.log n / Real.log 2 with hrB
  set B := ⌈Real.log rB / Real.log (1 + e)⌉₊ with hB
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hrB1 : 1 ≤ rB := by
    rw [hrB]; linarith [div_nonneg hlogn (by linarith : (0 : ℝ) ≤ Real.log 2)]
  obtain ⟨T2', hT2'card, hT2'top, hT2'⟩ := exists_finset_submodule_of_chain
    (P := (· ∈ systemSet S w L C c)) (ht := fun x ↦ mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹)) a2
    T2 hT2top (fun h x hx h1 h2 ↦ hT2 h x hx h1 (by rw [← ha2]; exact h2)) B
  have haB : q0 ≤ a2 B := by
    have := le_pow_ceil he0 (show 0 < rB by linarith)
    calc q0 = 2 ^ (2 * n / δ * (rB - 1)) := by
          rw [hq0def, Real.rpow_def_of_pos two_pos, Real.rpow_def_of_pos hn0, hrB]
          congr 1
          field_simp
          ring
      _ ≤ a2 B := Real.rpow_le_rpow_of_exponent_le one_le_two
          (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hBle : (B : ℝ) ≤ δ⁻¹ * (1 + 4 * n * (n - 1)) := by
    have hBb := ceil_div_log_le he0 he1 (Real.log_nonneg hrB1)
    rw [show 2 * Real.log rB / e = 4 * n / δ * Real.log rB by rw [he]; field_simp; ring] at hBb
    have h1 : Real.log rB ≤ n - 1 := by
      have := Real.log_le_sub_one_of_pos (show 0 < rB by linarith)
      have h2 : Real.log n ≤ (n - 1) * Real.log 2 := by
        have hpow : n ≤ 2 ^ (n - 1) := by
          have := Nat.lt_two_pow_self (n := n - 1)
          omega
        have := Real.log_le_log hn0 (show (n : ℝ) ≤ 2 ^ (n - 1) by exact_mod_cast hpow)
        rwa [Real.log_pow, Nat.cast_sub (by omega), Nat.cast_one] at this
      have h3 : Real.log n / Real.log 2 ≤ n - 1 := by
        rw [div_le_iff₀ (by linarith)]; exact h2
      rw [hrB] at this
      linarith
    have hδinv : 1 ≤ δ⁻¹ := one_le_inv₀ hδ |>.2 hδ1
    have : 4 * (n : ℝ) / δ * Real.log rB ≤ δ⁻¹ * (4 * n * (n - 1)) := by
      rw [div_eq_mul_inv]
      nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 * n * δ⁻¹)]
    have hn1 : (0 : ℝ) ≤ 4 * n * (n - 1) := by nlinarith
    nlinarith
  -- The count.
  refine ⟨T1 ∪ T2', ?_, fun U hU ↦ ?_, fun x hx hxs ↦ ?_⟩
  · have h1 : (T1.card : ℝ) ≤ A := by
      have : T1.card ≤ A := by simpa using hT1card
      exact_mod_cast this
    have h2 : (T2'.card : ℝ) ≤ B * P := by
      calc (T2'.card : ℝ) ≤ ∑ h ∈ Finset.range B, ((T2 h).card : ℝ) := by exact_mod_cast hT2'card
        _ ≤ ∑ _h ∈ Finset.range B, P := Finset.sum_le_sum fun h _ ↦ hT2card h
        _ = B * P := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc ((T1 ∪ T2').card : ℝ) ≤ T1.card + T2'.card := by exact_mod_cast Finset.card_union_le _ _
      _ ≤ 4 * n / δ * Real.log (Real.log (4 * H)) + δ⁻¹ * (1 + 4 * n * (n - 1)) * P := by
          gcongr
          · exact h1.trans hAle
          · exact h2.trans (mul_le_mul_of_nonneg_right hBle hP0)
      _ = δ⁻¹ * ((1 + 4 * n * (n - 1)) * P + 4 * n * Real.log (Real.log (4 * H))) := by ring
  · rcases Finset.mem_union.1 hU with hU | hU
    · exact hT1top U hU
    · exact hT2'top U hU
  · have hlt : mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) < X := not_le.1 hxs
    have hge : 1 ≤ mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) :=
      Real.one_le_rpow (one_le_mulHeightAff x) (by positivity)
    by_cases hxq : mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) < q0
    · obtain ⟨U, hU, hxU⟩ := hT2' x hx (by rw [ha20]; exact hge) (hxq.trans_le haB)
      exact ⟨U, Finset.mem_union_right _ hU, hxU⟩
    · obtain ⟨U, hU, hxU⟩ := hT1 x hx (by simpa [ha1def] using not_lt.1 hxq)
        (hlt.trans_le haA)
      exact ⟨U, Finset.mem_union_left _ hU, hxU⟩

/-- **Evertse's Theorem 2.2: the small solutions.** Under the normalization (2.4), the solutions
of the system that are not large lie in at most `δ⁻¹ ((10³ n) ^ (n [K : ℚ]) + 4 n log log (4 H))`
proper subspaces of `Kⁿ`. -/
theorem exists_finset_submodule_of_not_isLargeSolution (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    ∃ T : Finset (Submodule K (ι → K)),
      (T.card : ℝ) ≤ δ⁻¹ * ((10 ^ 3 * Fintype.card ι) ^ (Fintype.card ι * finrank ℚ K) +
        4 * Fintype.card ι * Real.log (Real.log (4 * H))) ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x ∈ systemSet S w L C c, ¬ IsLargeSolution H δ x → ∃ U ∈ T, x ∈ U := by
  set n := Fintype.card ι with hn
  set d := finrank ℚ K with hd
  have hn2 : 2 ≤ n := hN.two_le_card
  set P : ℝ := (90 * n) ^ (n * d) with hP
  obtain ⟨T, hT, hTtop, hTcov⟩ := exists_finset_submodule_of_not_isLargeSolution_of_window S w
    hwInf hwFin hN (P := P) (by positivity) fun Q hQ ↦
      exists_finset_submodule_of_window_two_mul S w hwInf hwFin hN hQ
  refine ⟨T, hT.trans ?_, hTtop, hTcov⟩
  have hsmall : (1 + 4 * (n : ℝ) * (n - 1)) * P ≤ (10 ^ 3 * n) ^ (n * d) := by
    have h11 : (1 + 4 * (n : ℝ) * (n - 1)) ≤ (100 / 9) ^ (n * d) := by
      calc (1 + 4 * (n : ℝ) * (n - 1)) ≤ 1 + 8 * n ^ 2 := by nlinarith
        _ ≤ 11 ^ n := by exact_mod_cast one_add_eight_mul_sq_le n hn2
        _ ≤ (100 / 9) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) _
        _ ≤ (100 / 9) ^ (n * d) := pow_le_pow_right₀ (by norm_num)
            (Nat.le_mul_of_pos_right _ Module.finrank_pos)
    calc (1 + 4 * (n : ℝ) * (n - 1)) * P ≤ (100 / 9) ^ (n * d) * P :=
          mul_le_mul_of_nonneg_right h11 (by positivity)
      _ = (10 ^ 3 * n) ^ (n * d) := by rw [hP, ← mul_pow]; congr 1; ring
  have hδ := hN.delta_pos
  gcongr

end NumberField

namespace Rat

open NumberField

variable {F : Type*} [Field F] [NumberField F] [Algebra ℚ F] {ι : Type*} [Fintype ι]

private theorem factorial_le_pow_pred (n : ℕ) : n.factorial ≤ n ^ (n - 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    rw [Nat.factorial_succ, Nat.add_sub_cancel, show m = m - 1 + 1 by omega, pow_succ,
      Nat.sub_add_cancel hm, mul_comm (m + 1)]
    exact Nat.mul_le_mul_right _ (ih.trans (Nat.pow_le_pow_left (by omega) _))

private theorem factorial_mul_two_pow_le {n : ℕ} (hn : 2 ≤ n) :
    n.factorial * 2 ^ n ≤ (4 * n) ^ (n - 1) := by
  rw [mul_pow, mul_comm]
  refine Nat.mul_le_mul ?_ (factorial_le_pow_pred n)
  rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul]
  exact Nat.pow_le_pow_right two_pos (by omega)

private theorem three_pow_mul_le_two_hundred_pow (n : ℕ) (hn : 2 ≤ n) :
    3 ^ n * (4 * n ^ 2 + 2) ^ 2 * (4 * n) ≤ 200 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h1 : 4 * (m + 1) ^ 2 + 2 ≤ 3 * (4 * m ^ 2 + 2) := by nlinarith
    have h2 : 4 * (m + 1) ≤ 2 * (4 * m) := by omega
    calc 3 ^ (m + 1) * (4 * (m + 1) ^ 2 + 2) ^ 2 * (4 * (m + 1))
        ≤ 3 ^ (m + 1) * (3 * (4 * m ^ 2 + 2)) ^ 2 * (2 * (4 * m)) := by gcongr
      _ = 54 * (3 ^ m * (4 * m ^ 2 + 2) ^ 2 * (4 * m)) := by ring
      _ ≤ 54 * 200 ^ m := Nat.mul_le_mul_left _ ih
      _ ≤ 200 ^ (m + 1) := by rw [pow_succ]; omega

private theorem one_add_four_mul_le_five_pow (n : ℕ) (hn : 2 ≤ n) :
    1 + 4 * n * (n - 1) ≤ 5 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ, Nat.add_sub_cancel]
    have : 1 + 4 * (m + 1) * m ≤ 5 * (1 + 4 * m * (m - 1)) := by
      rcases m with _ | _ | m
      · omega
      · omega
      · simp only [Nat.add_sub_cancel]; nlinarith
    omega

open scoped Classical in
/-- **The second gap principle over `ℚ`** (Evertse, Proposition 4.2, `K = ℚ`). Under the
normalization (2.4) and for `Q ≥ 1`, the solutions of the system whose affine height lies in
`[Q, 2 Q ^ (1 + δ / (2 n)))` lie in at most `200 ^ n` proper subspaces of `ℚⁿ`. Lemma 4.5 replaces
the partition of Lemma 4.3. -/
theorem exists_finset_submodule_of_window_two_mul (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (w : AbsoluteValue ℚ ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace ℚ, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue ℚ ℝ → ι → Dual F (ι → F)} {C : InfinitePlace ℚ ⊕ S → ℝ}
    {c : InfinitePlace ℚ ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∃ T : Finset (Submodule ℚ (ι → ℚ)),
      (T.card : ℝ) ≤ 200 ^ Fintype.card ι ∧ (∀ U ∈ T, U ≠ ⊤) ∧ ∀ x ∈ systemSet S w L C c,
        Q ≤ mulHeightAff x → mulHeightAff x < 2 * Q ^ (1 + δ / (2 * Fintype.card ι)) →
        ∃ U ∈ T, x ∈ U := by
  set n := Fintype.card ι with hn
  set ε := δ / (2 * n) with hε
  have hn2 : 2 ≤ n := hN.two_le_card
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hQ0 : 0 < Q := by linarith
  set W : Set (ι → ℚ) := {x | x ∈ systemSet S w L C c ∧ Q ≤ mulHeightAff x ∧
    mulHeightAff x < 2 * Q ^ (1 + ε)} with hW
  have hrow : ∀ x ∈ W, ∀ p i, systemValue S w L p i x ≤
      C p * 2 ^ systemExponent S p * Q ^ (c p i + systemExponent S p * ε) := fun x hx p i ↦
    systemValue_le_rpow_of_window hx.1 (hN.const_pos p).le (hN.exponent_le p i) hQ0 two_pos
      hx.2.1 hx.2.2.le
  -- over `ℚ` every place has multiplicity `1`
  have hmult : ∀ p, systemMult S p = 1 := by
    rintro (v | v)
    · change v.mult = 1
      exact InfinitePlace.mult_isReal ⟨v, Subsingleton.elim Rat.infinitePlace v ▸
        Rat.isReal_infinitePlace⟩
    · rfl
  have habs : ∀ p (a : ℚ), systemAbs S w p (algebraMap ℚ F a) = systemPlace S p a := by
    rintro (v | v) a
    · have := hwInf v
      rw [systemAbs, hmult, pow_one]
      change w v.1 (algebraMap ℚ F a) = v.1 a
      exact AbsoluteValue.apply_algebraMap_of_liesOver (v := v.1) _ a
    · have := hwFin v.1 v.2
      rw [systemAbs, hmult, pow_one]
      change w (FinitePlace.mk v.1).1 (algebraMap ℚ F a) = (FinitePlace.mk v.1).1 a
      exact AbsoluteValue.apply_algebraMap_of_liesOver (v := (FinitePlace.mk v.1).1) _ a
  -- the local bounds on the determinants
  set g : ℝ := n.factorial * 2 ^ n with hg
  have hg1 : 1 ≤ g := one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos n)
    (one_le_pow₀ one_le_two)
  set num : InfinitePlace ℚ ⊕ S → ℝ := fun p ↦ g ^ (systemExponent S p * finrank ℚ ℚ) *
    ∏ i, (C p * Q ^ (c p i + systemExponent S p * (δ / (2 * n)))) with hnum
  set Ld : InfinitePlace ℚ ⊕ S → ℝ := fun p ↦
    systemAbs S w p (LinearMap.det (LinearMap.pi (L (systemPlace S p)))) with hLd
  have hLd0 : ∀ p, 0 < Ld p := fun p ↦ by
    have h := systemDet_pos hN
    rw [systemDet] at h
    exact lt_of_le_of_ne (pow_nonneg (apply_nonneg _ _) _)
      (Finset.prod_ne_zero_iff.1 h.ne' p (Finset.mem_univ _)).symm
  have hD : ∀ y : ι → ι → ℚ, (∀ j, y j ∈ W) → ∀ p,
      systemPlace S p ((Pi.basisFun ℚ ι).det y) ≤ num p / Ld p := fun y hy p ↦ by
    have hs0 := systemExponent_nonneg S p
    have hlb := systemAbs_det_le S w hwFin p (systemMatrix S L y p)
      (r := fun i ↦ C p * 2 ^ systemExponent S p * Q ^ (c p i + systemExponent S p * ε))
      (fun i ↦ by have := hN.const_pos p; positivity) fun i j ↦ hrow (y j) (hy j) p i
    have e1 : systemAbs S w p (systemMatrix S L y p).det =
        Ld p * systemPlace S p ((Pi.basisFun ℚ ι).det y) := by
      rw [det_systemMatrix, systemAbs, map_mul, mul_pow, ← systemAbs, ← systemAbs, habs]
    have h2 : ((2 : ℝ) ^ systemExponent S p) ^ n = ((2 : ℝ) ^ n) ^ systemExponent S p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, ← Real.rpow_natCast (2 : ℝ) n,
        ← Real.rpow_mul zero_le_two, mul_comm]
    have e2 : ((n.factorial : ℕ) : ℝ) ^ (systemExponent S p * finrank ℚ ℚ) *
        ∏ i, (C p * 2 ^ systemExponent S p * Q ^ (c p i + systemExponent S p * ε)) = num p := by
      simp only [hnum, hg, Module.finrank_self, Nat.cast_one, mul_one, ← hε]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Finset.prod_const (2 ^ systemExponent S p : ℝ), Finset.card_univ, ← hn, h2,
        Real.mul_rpow (by positivity) (by positivity)]
      ring
    rw [le_div_iff₀ (hLd0 p), mul_comm, ← e1, ← e2]
    exact hlb
  obtain ⟨U, hU, hUtop, hUcov⟩ :=
    Rat.exists_finset_submodule_of_det_le S hn2 (T := W) (fun x hx ↦ hx.1.1) _ hD
  refine ⟨U, hU.trans ?_, hUtop, fun x hx hlo hhi ↦ hUcov x ⟨hx, hlo, hhi⟩⟩
  -- the count
  have hprod : ∏ p, num p / Ld p ≤ g := by
    rw [Finset.prod_div_distrib]
    have h := prod_systemBound_le hN hQ (zero_lt_one.trans_le hg1)
    have hdet : ∏ p, Ld p = systemDet S w L := rfl
    rw [hdet, div_le_iff₀ (systemDet_pos hN)]
    calc ∏ p, num p ≤ g ^ finrank ℚ ℚ * (systemDet S w L * Q ^ (-(δ / 2))) := h
      _ = g * (systemDet S w L * Q ^ (-(δ / 2))) := by rw [Module.finrank_self, pow_one]
      _ ≤ g * (systemDet S w L * 1) := by
          gcongr
          · exact (systemDet_pos hN).le
          · exact Real.rpow_le_one_of_one_le_of_nonpos hQ (by linarith [hN.delta_pos])
      _ = g * systemDet S w L := by ring
  set e : ℝ := ((n - 1 : ℕ) : ℝ)⁻¹ with he
  have hn1 : (n - 1 : ℕ) ≠ 0 := by omega
  have hge : max 1 (∏ p, num p / Ld p) ^ e ≤ 4 * n := by
    have hmax : max 1 (∏ p, num p / Ld p) ≤ (4 * n) ^ (n - 1) := by
      refine max_le (one_le_pow₀ (by have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
                                     linarith)) (hprod.trans ?_)
      rw [hg]
      exact_mod_cast factorial_mul_two_pow_le hn2
    calc max 1 (∏ p, num p / Ld p) ^ e ≤ (((4 * n : ℝ)) ^ (n - 1)) ^ e :=
          Real.rpow_le_rpow (by positivity) hmax (by positivity)
      _ = 4 * n := Real.pow_rpow_inv_natCast (by positivity) hn1
  calc (3 : ℝ) ^ n * (4 * n ^ 2 + 2) ^ 2 * max 1 (∏ p, num p / Ld p) ^ e
      ≤ 3 ^ n * (4 * n ^ 2 + 2) ^ 2 * (4 * n) := by gcongr
    _ ≤ 200 ^ n := by exact_mod_cast three_pow_mul_le_two_hundred_pow n hn2

/-- **Evertse's Theorem 2.2 over `ℚ`.** Under the normalization (2.4), the solutions of the system
that are not large lie in at most `δ⁻¹ (10 ^ (3 n) + 4 n log log (4 H))` proper subspaces of
`ℚⁿ`. -/
theorem exists_finset_submodule_of_not_isLargeSolution (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (w : AbsoluteValue ℚ ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace ℚ, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue ℚ ℝ → ι → Dual F (ι → F)} {C : InfinitePlace ℚ ⊕ S → ℝ}
    {c : InfinitePlace ℚ ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    ∃ T : Finset (Submodule ℚ (ι → ℚ)),
      (T.card : ℝ) ≤ δ⁻¹ * (10 ^ (3 * Fintype.card ι) +
        4 * Fintype.card ι * Real.log (Real.log (4 * H))) ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x ∈ systemSet S w L C c, ¬ IsLargeSolution H δ x → ∃ U ∈ T, x ∈ U := by
  set n := Fintype.card ι with hn
  have hn2 : 2 ≤ n := hN.two_le_card
  have hH : ∀ x : ι → ℚ, mulHeightAff x ^ ((finrank ℚ ℚ : ℝ)⁻¹) = mulHeightAff x := fun x ↦ by
    rw [Module.finrank_self, Nat.cast_one, inv_one, Real.rpow_one]
  obtain ⟨T, hT, hTtop, hTcov⟩ :=
    NumberField.exists_finset_submodule_of_not_isLargeSolution_of_window S w hwInf hwFin hN
      (P := 200 ^ n) (by positivity) fun Q hQ ↦ by
      obtain ⟨T, hT, hTtop, hTcov⟩ :=
        exists_finset_submodule_of_window_two_mul S w hwInf hwFin hN hQ
      exact ⟨T, hT, hTtop, fun x hx hlo hhi ↦ hTcov x hx (by rwa [hH] at hlo) (by rwa [hH] at hhi)⟩
  refine ⟨T, hT.trans ?_, hTtop, hTcov⟩
  have hδ := hN.delta_pos
  have h5 : (1 + 4 * (n : ℝ) * (n - 1)) ≤ 5 ^ n := by
    have := one_add_four_mul_le_five_pow n hn2
    have h : ((1 + 4 * n * (n - 1) : ℕ) : ℝ) = 1 + 4 * (n : ℝ) * (n - 1) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring
    rw [← h]
    exact_mod_cast this
  have hsmall : (1 + 4 * (n : ℝ) * (n - 1)) * 200 ^ n ≤ 10 ^ (3 * n) := by
    calc (1 + 4 * (n : ℝ) * (n - 1)) * 200 ^ n ≤ 5 ^ n * 200 ^ n := by gcongr
      _ = 10 ^ (3 * n) := by rw [← mul_pow, pow_mul]; norm_num
  gcongr

end Rat
