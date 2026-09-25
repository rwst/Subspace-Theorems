/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SubspaceSystem

-- Used only inside proofs.
import DiophantineApproximation.PlacesOverFinite
import DiophantineApproximation.SAdicHeight

/-!
# The gap principle

**Layer 9.2.** Evertse, "On the Quantitative Subspace Theorem", Proposition 4.1: under the
normalization (2.4) of a system (`NumberField.IsNormalizedSystem`, Layer 9.1) and for
`Q ≥ n ^ (2 n / δ)`, the solutions whose absolute affine height `H(x) ^ (1 / [K : ℚ])` lies in
`[Q, Q ^ (1 + δ / (2 n)))` lie in a **single** proper subspace of `Kⁿ`
(`NumberField.exists_submodule_ne_top_of_window`). Any `n` of them have determinant `0`
(`NumberField.det_eq_zero_of_window`): the determinant is an `S`-integer, so by the product
formula its local sizes over the places of the system multiply to at least `1`
(`NumberField.one_le_prod_systemAbs_algebraMap`), while the system bounds each of them.

## Main results

* `NumberField.systemValue_le_rpow_of_window`: in a window `[Q, b Q ^ (1 + ε)]` of heights, each
  local value is at most `C p · b ^ s(p) · Q ^ (c p i + s(p) ε)`. This is where `c p i ≤ s(p)` is
  used; `b = 2 ^ [K : ℚ]` is the second gap principle's window (Layer 9.3).
* `NumberField.prod_systemBound_le`: the product over the places of the local bounds of a window
  is at most `g ^ [K : ℚ] ∏ |det L v|_v Q ^ (-δ / 2)` — the bookkeeping shared with both forms of
  the second gap principle, over `K` and over `ℚ` (Layer 9.3).
* `NumberField.det_eq_zero_of_systemAbs_det_le`: the assembly by the product formula, shared with
  the second gap principle — local bounds `g ^ ([K : ℚ] s(p)) ∏ C p Q ^ (…)` with
  `g ^ [K : ℚ] Q ^ (-δ / 2) < 1` force the determinant to vanish.
* `NumberField.span_ne_top_of_forall_det_eq_zero`: a set any `n` of whose points are dependent
  spans a proper subspace.
* `NumberField.one_le_prod_systemAbs_algebraMap`: the product formula for a nonzero `S`-integer,
  over the places of a system.
* `NumberField.det_eq_zero_of_window`: **any `n` solutions in a window are dependent**.
* `NumberField.exists_submodule_ne_top_of_window`: **the gap principle**.
* `NumberField.exists_finset_submodule_of_chain`: a chain of windows, each covered by finitely
  many subspaces, is covered by their union — how 9.3 and 9.4 count windows.

## Implementation notes

⚠ **Leibniz instead of Hadamard, and it costs nothing.** Evertse bounds the determinant at an
infinite place by Hadamard's inequality, `n ^ (n / 2)` times the product of the row maxima. The
places here are abstract absolute values of `F` over the infinite places of `K`, with no inner
product in sight, and the Leibniz expansion gives `n!` instead. Over the infinite places the
factors multiply to `(n!) ^ [K : ℚ]`, and `Q ≥ n ^ (2 n / δ)` makes `Q ^ ([K : ℚ] δ / 2)` at
least `n ^ (n [K : ℚ])`, which beats `(n!) ^ [K : ℚ]` for `n ≥ 2`. For `n = 1` the two agree and
the strict inequality comes from the window being nonempty, which forces `Q > 1`. Evertse's
bound had room to spare; the hypothesis on `Q` is his.

⚠ **Only five fields of (2.4) are used**: the positivity of the constants and of `δ`, `∏ C p` at
most `(∏ |det L p|_p) ^ (1 / n)`, the weight at most `-δ`, and `c p i ≤ s(p)`. The heights and
degrees of the coefficients, the number of forms, `δ ≤ 1` and the attained maximum are not; they
are for the interval result that 9.4 feeds this into. Nor are the forms assumed independent:
`∏ C p > 0` forces every determinant to be nonzero.

⚠ **The window is in the absolute height**, `Q ≤ H(x) ^ (1 / [K : ℚ]) < Q ^ (1 + δ / (2 n))`, as
in the source and as in `NumberField.IsLargeSolution`; with Mathlib's `mulHeightAff` it is
`Q ^ [K : ℚ] ≤ mulHeightAff x < Q ^ ([K : ℚ] (1 + δ / (2 n)))`. The source's statement writes
`‖x‖` for `H(x)`; its proof uses `H(x)`.

## References

J.-H. Evertse, *On the Quantitative Subspace Theorem*, Zap. Nauchn. Sem. POMI **377** (2010),
217–240; J. Math. Sci. **171** (2010), 824–837 (arXiv:1008.2268), Proposition 4.1.

This is Layer 9.2 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height IsDedekindDomain Module

namespace AbsoluteValue

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem apply_sign_smul (W : AbsoluteValue F ℝ) (σ : Equiv.Perm ι) (a : F) :
    W (Equiv.Perm.sign σ • a) = W a := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

private theorem prod_apply_perm_le (W : AbsoluteValue F ℝ) (M : Matrix ι ι F) {r : ι → ℝ}
    (h : ∀ i j, W (M i j) ≤ r i) (σ : Equiv.Perm ι) :
    W (Equiv.Perm.sign σ • ∏ i, M (σ i) i) ≤ ∏ i, r i := by
  rw [apply_sign_smul, map_prod, ← Equiv.prod_comp σ r]
  exact Finset.prod_le_prod₀ (fun i _ ↦ apply_nonneg _ _) fun i _ ↦ h (σ i) i

/-- **The Leibniz bound**: a determinant whose rows are bounded by `r i` is at most `n!` times the
product of the bounds. -/
theorem apply_det_le_factorial_mul_prod (W : AbsoluteValue F ℝ) (M : Matrix ι ι F) {r : ι → ℝ}
    (h : ∀ i j, W (M i j) ≤ r i) :
    W M.det ≤ (Fintype.card ι).factorial * ∏ i, r i := by
  rw [Matrix.det_apply]
  calc W (∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, M (σ i) i)
      ≤ ∑ σ : Equiv.Perm ι, W (Equiv.Perm.sign σ • ∏ i, M (σ i) i) := W.sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, ∏ i, r i :=
        Finset.sum_le_sum fun σ _ ↦ prod_apply_perm_le W M h σ
    _ = (Fintype.card ι).factorial * ∏ i, r i := by simp [Fintype.card_perm]

/-- **The ultrametric Leibniz bound**: a nonarchimedean determinant whose rows are bounded by
`r i` is at most the product of the bounds. -/
theorem apply_det_le_prod_of_isNonarchimedean {W : AbsoluteValue F ℝ}
    (hW : IsNonarchimedean (W : F → ℝ)) (M : Matrix ι ι F) {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i)
    (h : ∀ i j, W (M i j) ≤ r i) : W M.det ≤ ∏ i, r i := by
  rw [Matrix.det_apply]
  exact Finset.sum_induction _ (fun y ↦ W y ≤ ∏ i, r i)
    (fun a b ha hb ↦ (hW a b).trans (max_le ha hb))
    (by simpa using Finset.prod_nonneg fun i _ ↦ hr i) fun σ _ ↦ prod_apply_perm_le W M h σ

end AbsoluteValue

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι]

omit [NumberField F] in
theorem systemExponent_nonneg (S : Finset (HeightOneSpectrum (𝓞 K))) (p : InfinitePlace K ⊕ S) :
    0 ≤ systemExponent S p := by
  rcases p with v | v
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact le_rfl

/-- The normalized local degrees `s(p)` sum to `1`. -/
theorem sum_systemExponent (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∑ p, systemExponent S p = 1 := by
  rw [Fintype.sum_sum_type]
  simp only [systemExponent, Finset.sum_const_zero, add_zero]
  rw [← Finset.sum_div, ← Nat.cast_sum, InfinitePlace.sum_mult_eq,
    div_self (Nat.cast_ne_zero.2 Module.finrank_pos.ne')]

/-- Under the normalization, `(∏ C p) ^ n ≤ ∏ |det L p|_p`. -/
theorem systemConst_pow_le_systemDet [Nonempty ι] {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ} {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)}
    {C : InfinitePlace K ⊕ S → ℝ} {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    systemConst C ^ Fintype.card ι ≤ systemDet S w L := by
  have hdet0 : 0 ≤ systemDet S w L := Finset.prod_nonneg fun p _ ↦ pow_nonneg (apply_nonneg _ _) _
  have hC0 : 0 ≤ systemConst C := Finset.prod_nonneg fun p _ ↦ (hN.const_pos p).le
  have hN0 : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  calc systemConst C ^ Fintype.card ι
      ≤ (systemDet S w L ^ (Fintype.card ι : ℝ)⁻¹) ^ Fintype.card ι :=
        pow_le_pow_left₀ hC0 hN.const_le _
    _ = systemDet S w L := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hdet0, inv_mul_cancel₀ hN0, Real.rpow_one]

/-- Under the normalization the determinant product is positive. -/
theorem systemDet_pos [Nonempty ι] {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ} {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)}
    {C : InfinitePlace K ⊕ S → ℝ} {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) : 0 < systemDet S w L :=
  lt_of_lt_of_le (pow_pos (Finset.prod_pos fun p _ ↦ hN.const_pos p) _)
    (systemConst_pow_le_systemDet hN)

omit [NumberField F] [Fintype ι] in
/-- **In a window of heights each local value is bounded by a power of the window's end**:
if `Q ≤ H(x) ≤ b · Q ^ (1 + ε)` then `|L p i x|_p ≤ C p · b ^ s(p) · Q ^ (c p i + s(p) ε)`. This is
where `c p i ≤ s(p)` is used: the part `c p i - s(p)` of the exponent is `≤ 0` and is bounded at
the bottom of the window, the part `s(p) ≥ 0` at the top. -/
theorem systemValue_le_rpow_of_window [Finite ι] {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ} {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)}
    {C : InfinitePlace K ⊕ S → ℝ} {c : InfinitePlace K ⊕ S → ι → ℝ} {x : ι → K}
    (hx : x ∈ systemSet S w L C c) {p : InfinitePlace K ⊕ S} {i : ι} (hC : 0 ≤ C p)
    (hc : c p i ≤ systemExponent S p) {Q b ε : ℝ} (hQ : 0 < Q) (hb : 0 < b)
    (hlo : Q ≤ mulHeightAff x) (hhi : mulHeightAff x ≤ b * Q ^ (1 + ε)) :
    systemValue S w L p i x ≤
      C p * b ^ systemExponent S p * Q ^ (c p i + systemExponent S p * ε) := by
  have hH := mulHeightAff_pos x
  set s := systemExponent S p
  have hs := systemExponent_nonneg S p
  refine (hx.2 p i).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC
  calc mulHeightAff x ^ c p i = mulHeightAff x ^ (c p i - s) * mulHeightAff x ^ s := by
        rw [← Real.rpow_add hH, sub_add_cancel]
    _ ≤ Q ^ (c p i - s) * (b * Q ^ (1 + ε)) ^ s :=
        mul_le_mul (Real.rpow_le_rpow_of_nonpos hQ hlo (by linarith))
          (Real.rpow_le_rpow hH.le hhi hs) (Real.rpow_nonneg hH.le _)
          (Real.rpow_nonneg hQ.le _)
    _ = b ^ s * Q ^ (c p i + s * ε) := by
        rw [Real.mul_rpow hb.le (Real.rpow_nonneg hQ.le _), ← Real.rpow_mul hQ.le, mul_left_comm,
          ← Real.rpow_add hQ]
        congr 2; ring

/-- **The product formula for a nonzero `S`-integer, over the places of a system**: its local
sizes at the infinite places and at `S` multiply to at least `1`. -/
theorem one_le_prod_systemAbs_algebraMap (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1) {a : K}
    (ha : a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) (ha0 : a ≠ 0) :
    1 ≤ ∏ p, systemAbs S w p (algebraMap K F a) := by
  have h := mulHeight_le_prod_of_forall_mem_integer S (x := fun _ : Unit ↦ a)
    (fun h ↦ ha0 (congrFun h ())) fun _ ↦ ha
  rw [mulHeight_eq_one_of_subsingleton] at h
  simp only [ciSup_const] at h
  refine h.trans_eq ?_
  rw [Fintype.prod_sum_type, ← Finset.prod_coe_sort S]
  congr 1
  · refine Finset.prod_congr rfl fun v _ ↦ ?_
    have := hwInf v
    change v a ^ v.mult = w v.1 (algebraMap K F a) ^ v.mult
    rw [AbsoluteValue.apply_algebraMap_of_liesOver (v := v.1)]
    rfl
  · refine Finset.prod_congr rfl fun v _ ↦ ?_
    have := hwFin v.1 v.2
    change FinitePlace.mk v.1 a = w (FinitePlace.mk v.1).1 (algebraMap K F a) ^ 1
    rw [pow_one, AbsoluteValue.apply_algebraMap_of_liesOver (v := (FinitePlace.mk v.1).1)]
    rfl

/-- **The Leibniz bound at a place of a system**: a determinant whose rows have local sizes at
most `r i` has local size at most `(n!) ^ ([K : ℚ] s(p)) · ∏ r i` — the factor `n! ^ mult v` at an
infinite place, and no factor at a finite one. -/
theorem systemAbs_det_le [DecidableEq ι] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    (p : InfinitePlace K ⊕ S) (M : Matrix ι ι F) {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i)
    (h : ∀ i j, systemAbs S w p (M i j) ≤ r i) :
    systemAbs S w p M.det ≤
      ((Fintype.card ι).factorial : ℝ) ^ (systemExponent S p * finrank ℚ K) * ∏ i, r i := by
  rcases p with v | v
  · have hm0 : v.mult ≠ 0 := InfinitePlace.mult_ne_zero
    have hexp : systemExponent S (.inl v) * finrank ℚ K = v.mult := by
      change (v.mult : ℝ) / finrank ℚ K * finrank ℚ K = v.mult
      rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.2 Module.finrank_pos.ne')]
    rw [hexp, Real.rpow_natCast]
    change w v.1 M.det ^ v.mult ≤ _
    set t : ι → ℝ := fun i ↦ r i ^ (v.mult⁻¹ : ℝ) with ht
    have ht0 : ∀ i, 0 ≤ t i := fun i ↦ Real.rpow_nonneg (hr i) _
    have htr : ∀ i, t i ^ v.mult = r i := fun i ↦ Real.rpow_inv_natCast_pow (hr i) hm0
    have hle : ∀ i j, w v.1 (M i j) ≤ t i := fun i j ↦
      (pow_le_pow_iff_left₀ (apply_nonneg _ _) (ht0 i) hm0).1 (by rw [htr]; exact h i j)
    calc w v.1 M.det ^ v.mult
        ≤ ((Fintype.card ι).factorial * ∏ i, t i) ^ v.mult :=
          pow_le_pow_left₀ (apply_nonneg _ _)
            ((w v.1).apply_det_le_factorial_mul_prod M hle) _
      _ = ((Fintype.card ι).factorial : ℝ) ^ v.mult * ∏ i, r i := by
          rw [mul_pow, ← Finset.prod_pow]; simp only [htr]
  · have := hwFin v.1 v.2
    have hna := isNonarchimedean_of_liesOver_finitePlace (FinitePlace.mk v.1)
      (w (FinitePlace.mk v.1).1)
    change w (FinitePlace.mk v.1).1 M.det ^ 1 ≤
      ((Fintype.card ι).factorial : ℝ) ^ ((0 : ℝ) * finrank ℚ K) * ∏ i, r i
    rw [zero_mul, Real.rpow_zero, one_mul, pow_one]
    exact AbsoluteValue.apply_det_le_prod_of_isNonarchimedean hna M hr fun i j ↦ by
      simpa [systemAbs, systemMult, systemPlace] using h i j

/-- **The matrix of the forms of a system at `n` points**: its `(i, j)` entry is the `i`-th form
at the place `p`, evaluated at the `j`-th point. -/
noncomputable def systemMatrix (S : Finset (HeightOneSpectrum (𝓞 K)))
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) (y : ι → ι → K) (p : InfinitePlace K ⊕ S) :
    Matrix ι ι F :=
  Matrix.of fun i j ↦ L (systemPlace S p) i fun k ↦ algebraMap K F (y j k)

omit [NumberField F] in
/-- The determinant of the forms at `n` points is that of the forms times that of the points. -/
theorem det_systemMatrix [DecidableEq ι] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) (y : ι → ι → K) (p : InfinitePlace K ⊕ S) :
    (systemMatrix S L y p).det =
      LinearMap.det (LinearMap.pi (L (systemPlace S p))) * algebraMap K F ((Pi.basisFun K ι).det y)
    := by
  have hMp : systemMatrix S L y p = LinearMap.toMatrix' (LinearMap.pi (L (systemPlace S p))) *
      ((algebraMap K F).mapMatrix (Matrix.of y)).transpose := by
    ext i j
    simp only [systemMatrix, Matrix.of_apply, Matrix.mul_apply, LinearMap.toMatrix'_apply,
      LinearMap.pi_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
    conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ (L (systemPlace S p) i)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    funext l
    rw [Pi.single_apply]; exact if_congr eq_comm rfl rfl
  rw [hMp, Matrix.det_mul, LinearMap.det_toMatrix', Matrix.det_transpose, ← RingHom.map_det,
    Pi.basisFun_det_apply]

/-- **The product of the local bounds of a window** (the bookkeeping of Evertse's proofs of
Propositions 4.1 and 4.2). Under the normalization, the product over the places of
`g ^ ([K : ℚ] s(p)) · ∏ i, C p · Q ^ (c p i + s(p) δ / (2 n))` is at most
`g ^ [K : ℚ] · ∏ |det L v|_v · Q ^ (-δ / 2)`. -/
theorem prod_systemBound_le [Nonempty ι] {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ} {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)}
    {C : InfinitePlace K ⊕ S → ℝ} {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) {Q g : ℝ} (hQ : 1 ≤ Q) (hg : 0 < g) :
    ∏ p, (g ^ (systemExponent S p * finrank ℚ K) *
        ∏ i, (C p * Q ^ (c p i + systemExponent S p * (δ / (2 * Fintype.card ι))))) ≤
      g ^ finrank ℚ K * (systemDet S w L * Q ^ (-(δ / 2))) := by
  set n := Fintype.card ι with hn
  set d := finrank ℚ K with hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  have hQ0 : 0 < Q := by linarith
  have hprod_r : ∏ p, ∏ i, (C p * Q ^ (c p i + systemExponent S p * (δ / (2 * n)))) =
      systemConst C ^ n * Q ^ (systemWeight c + δ / 2) := by
    have hsum : ∑ p, ∑ i, (c p i + systemExponent S p * (δ / (2 * n))) =
        systemWeight c + δ / 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        systemWeight, ← Finset.mul_sum, ← Finset.sum_mul, sum_systemExponent]
      rw [← hn]
      field_simp
    rw [← hsum, Real.rpow_sum_of_pos hQ0, systemConst, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ ↦ ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Real.rpow_sum_of_pos hQ0]
  have hprod_g : ∏ p, g ^ (systemExponent S p * d) = g ^ d := by
    rw [← Real.rpow_sum_of_pos hg, ← Finset.sum_mul, sum_systemExponent, one_mul,
      Real.rpow_natCast]
  have hdet := systemDet_pos hN
  calc ∏ p, (g ^ (systemExponent S p * d) *
        ∏ i, (C p * Q ^ (c p i + systemExponent S p * (δ / (2 * n)))))
      = g ^ d * (systemConst C ^ n * Q ^ (systemWeight c + δ / 2)) := by
        rw [Finset.prod_mul_distrib, hprod_g, hprod_r]
    _ ≤ g ^ d * (systemDet S w L * Q ^ (-(δ / 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul (systemConst_pow_le_systemDet hN)
          (Real.rpow_le_rpow_of_exponent_le hQ (by linarith [hN.weight_le]))
          (Real.rpow_nonneg hQ0.le _) hdet.le) (by positivity)

/-- **The determinant of `n` solutions vanishes once the places bound it below the product
formula** (the assembly of Evertse's proofs of Propositions 4.1 and 4.2). Under the normalization,
if at every place the determinant of the forms at the points `y j` is at most
`g ^ ([K : ℚ] s(p)) · ∏ i, C p · Q ^ (c p i + s(p) δ / (2 n))`, and
`g ^ [K : ℚ] · Q ^ (-δ / 2) < 1`, then `det (y 1, …, y n) = 0`. -/
theorem det_eq_zero_of_systemAbs_det_le [Nonempty ι] [DecidableEq ι]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) {Q g : ℝ} (hQ : 1 ≤ Q) (hg : 0 < g)
    (hlt : g ^ finrank ℚ K * Q ^ (-(δ / 2)) < 1) (y : ι → ι → K)
    (hy : ∀ j k, y j k ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K)
    (hbound : ∀ p, systemAbs S w p (systemMatrix S L y p).det ≤
      g ^ (systemExponent S p * finrank ℚ K) *
        ∏ i, C p * Q ^ (c p i + systemExponent S p * (δ / (2 * Fintype.card ι)))) :
    (Pi.basisFun K ι).det y = 0 := by
  set n := Fintype.card ι with hn
  set d := finrank ℚ K with hd
  by_contra hΔ
  set Δ := (Pi.basisFun K ι).det y with hΔdef
  have hΔint : Δ ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K := by
    rw [hΔdef, Pi.basisFun_det_apply, Matrix.det_apply]
    refine Subalgebra.sum_mem _ fun σ _ ↦ ?_
    rw [Units.smul_def, zsmul_eq_mul]
    exact Subalgebra.mul_mem _ (intCast_mem _ _) (Subalgebra.prod_mem _ fun i _ ↦ hy (σ i) i)
  have hdet := systemDet_pos hN
  have key : systemDet S w L * 1 ≤ systemDet S w L * (g ^ d * Q ^ (-(δ / 2))) := by
    calc systemDet S w L * 1
        ≤ systemDet S w L * ∏ p, systemAbs S w p (algebraMap K F Δ) :=
          mul_le_mul_of_nonneg_left (one_le_prod_systemAbs_algebraMap S w hwInf hwFin hΔint hΔ)
            hdet.le
      _ = ∏ p, systemAbs S w p (systemMatrix S L y p).det := by
          rw [systemDet, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun p _ ↦ ?_
          rw [det_systemMatrix, systemAbs, systemAbs, systemAbs, map_mul, mul_pow]
      _ ≤ ∏ p, (g ^ (systemExponent S p * d) *
            ∏ i, (C p * Q ^ (c p i + systemExponent S p * (δ / (2 * n))))) :=
          Finset.prod_le_prod₀ (fun p _ ↦ pow_nonneg (apply_nonneg _ _) _) fun p _ ↦ hbound p
      _ ≤ g ^ d * (systemDet S w L * Q ^ (-(δ / 2))) := prod_systemBound_le hN hQ hg
      _ = systemDet S w L * (g ^ d * Q ^ (-(δ / 2))) := by ring
  exact absurd hlt (not_lt.2 (le_of_mul_le_mul_left key hdet))

omit [NumberField K] in
/-- **A set any `n` of whose points are dependent spans a proper subspace.** -/
theorem span_ne_top_of_forall_det_eq_zero [DecidableEq ι] {T : Set (ι → K)}
    (hT : ∀ y : ι → ι → K, (∀ j, y j ∈ T) → (Pi.basisFun K ι).det y = 0) :
    Submodule.span K T ≠ ⊤ := fun htop ↦ by
  obtain ⟨b, hbT, hspan, hli⟩ := exists_linearIndependent K T
  let B : Basis b K (ι → K) := Basis.mk hli (by rw [Subtype.range_coe, hspan, htop])
  let e : ι ≃ b := (Pi.basisFun K ι).indexEquiv B
  have hB : ∀ j, (B.reindex e.symm) j ∈ T := fun j ↦ by
    rw [Basis.reindex_apply, Equiv.symm_symm, Basis.mk_apply]
    exact hbT (e j).2
  exact ((Pi.basisFun K ι).isUnit_det (B.reindex e.symm)).ne_zero (hT _ hB)

private theorem factorial_pow_lt {n d : ℕ} (hn : 2 ≤ n) (hd : d ≠ 0) :
    n.factorial ^ d < (n ^ n) ^ d := by
  refine Nat.pow_lt_pow_left ?_ hd
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.factorial_succ, pow_succ']
  refine Nat.mul_lt_mul_of_pos_left ?_ (by omega)
  exact (Nat.factorial_le_pow k).trans_lt (Nat.pow_lt_pow_left (by omega) (by omega))

/-- **Any `n` solutions in a window are dependent** (Evertse, proof of Proposition 4.1). Under
the normalization (2.4), if `Q ≥ n ^ (2 n / δ)` and `y 1, …, y n` are solutions of the system
whose absolute affine heights lie in `[Q, Q ^ (1 + δ / (2 n)))`, then `det (y 1, …, y n) = 0`. -/
theorem det_eq_zero_of_window [Nonempty ι] [DecidableEq ι] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) {Q : ℝ}
    (hQ : (Fintype.card ι : ℝ) ^ (2 * Fintype.card ι / δ) ≤ Q) (y : ι → ι → K)
    (hy : ∀ j, y j ∈ systemSet S w L C c)
    (hlo : ∀ j, Q ≤ mulHeightAff (y j) ^ ((finrank ℚ K : ℝ)⁻¹))
    (hhi : ∀ j, mulHeightAff (y j) ^ ((finrank ℚ K : ℝ)⁻¹) < Q ^ (1 + δ / (2 * Fintype.card ι))) :
    (Pi.basisFun K ι).det y = 0 := by
  set n := Fintype.card ι with hn
  set d := finrank ℚ K with hd
  set ε := δ / (2 * n) with hε
  have hδ := hN.delta_pos
  have hn1 : 1 ≤ n := Fintype.card_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hd0 : 0 < d := Module.finrank_pos
  have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
  -- `Q ≥ 1`, and the window is nonempty, so `Q > 1`.
  have hQ1 : 1 ≤ Q := (Real.one_le_rpow (by exact_mod_cast hn1) (by positivity)).trans hQ
  have hQ0 : 0 < Q := by linarith
  obtain ⟨j₀⟩ := ‹Nonempty ι›
  have hQ1' : 1 < Q := by
    refine lt_of_le_of_ne hQ1 fun h ↦ ?_
    have := (hlo j₀).trans_lt (hhi j₀)
    rw [← h, Real.one_rpow] at this
    exact lt_irrefl _ this
  -- The window in `mulHeightAff`.
  set Q' := Q ^ (d : ℝ) with hQ'
  have hQ'0 : 0 < Q' := Real.rpow_pos_of_pos hQ0 _
  have hQ'1 : 1 < Q' := Real.one_lt_rpow hQ1' hd0'
  have hlo' : ∀ j, Q' ≤ mulHeightAff (y j) := fun j ↦ by
    have := Real.rpow_le_rpow hQ0.le (hlo j) hd0'.le
    rwa [Real.rpow_inv_rpow (mulHeightAff_pos _).le hd0'.ne'] at this
  have hhi' : ∀ j, mulHeightAff (y j) ≤ 1 * Q' ^ (1 + ε) := fun j ↦ by
    have := Real.rpow_le_rpow (Real.rpow_nonneg (mulHeightAff_pos _).le _) (hhi j).le hd0'.le
    rwa [Real.rpow_inv_rpow (mulHeightAff_pos _).le hd0'.ne', ← Real.rpow_mul hQ0.le, mul_comm,
      Real.rpow_mul hQ0.le, ← one_mul (Q' ^ (1 + ε))] at this
  have hfac0 : (0 : ℝ) < (n.factorial : ℕ) := by exact_mod_cast n.factorial_pos
  refine det_eq_zero_of_systemAbs_det_le S w hwInf hwFin hN hQ'1.le hfac0 ?_ y
    (fun j k ↦ (hy j).1 k) fun p ↦ ?_
  · -- `Q' ^ (δ / 2) > (n!) ^ d`.
    rw [Real.rpow_neg hQ'0.le, ← div_eq_mul_inv, div_lt_one (Real.rpow_pos_of_pos hQ'0 _)]
    have hQ'δ : ((n ^ n : ℕ) : ℝ) ^ d ≤ Q' ^ (δ / 2) := by
      calc ((n ^ n : ℕ) : ℝ) ^ d = ((n : ℝ) ^ (2 * n / δ)) ^ ((d : ℝ) * (δ / 2)) := by
            have : 2 * (n : ℝ) / δ * (d * (δ / 2)) = ((n * d : ℕ) : ℝ) := by
              push_cast; field_simp
            rw [← Real.rpow_mul hn0.le, this, Real.rpow_natCast, Nat.cast_pow, ← pow_mul]
        _ ≤ Q ^ ((d : ℝ) * (δ / 2)) := Real.rpow_le_rpow (by positivity) hQ (by positivity)
        _ = Q' ^ (δ / 2) := by rw [hQ', ← Real.rpow_mul hQ0.le]
    rcases eq_or_lt_of_le (show 1 ≤ n from hn1) with h1 | h2
    · rw [← h1, Nat.factorial_one, Nat.cast_one, one_pow]
      exact Real.one_lt_rpow hQ'1 (by positivity)
    · have hlt : ((n.factorial : ℕ) : ℝ) ^ d < ((n ^ n : ℕ) : ℝ) ^ d := by
        exact_mod_cast factorial_pow_lt h2 hd0.ne'
      exact hlt.trans_le hQ'δ
  · exact systemAbs_det_le S w hwFin p (systemMatrix S L y p)
      (r := fun i ↦ C p * Q' ^ (c p i + systemExponent S p * ε))
      (fun i ↦ mul_nonneg (hN.const_pos p).le (Real.rpow_nonneg hQ'0.le _)) fun i j ↦ by
        have := systemValue_le_rpow_of_window (hy j) (hN.const_pos p).le (hN.exponent_le p i)
          hQ'0 one_pos (hlo' j) (hhi' j)
        rwa [Real.one_rpow, mul_one] at this

/-- **The gap principle** (Evertse, Proposition 4.1). Under the normalization (2.4) and for
`Q ≥ n ^ (2 n / δ)`, the solutions of the system whose absolute affine height lies in
`[Q, Q ^ (1 + δ / (2 n)))` lie in a single proper subspace of `Kⁿ`. -/
theorem exists_submodule_ne_top_of_window [Nonempty ι] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) {Q : ℝ}
    (hQ : (Fintype.card ι : ℝ) ^ (2 * Fintype.card ι / δ) ≤ Q) :
    ∃ U : Submodule K (ι → K), U ≠ ⊤ ∧ ∀ x ∈ systemSet S w L C c,
      Q ≤ mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) →
      mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) < Q ^ (1 + δ / (2 * Fintype.card ι)) → x ∈ U := by
  classical
  refine ⟨Submodule.span K {x | x ∈ systemSet S w L C c ∧
    Q ≤ mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) ∧
    mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) < Q ^ (1 + δ / (2 * Fintype.card ι))},
    span_ne_top_of_forall_det_eq_zero fun y hy ↦ det_eq_zero_of_window S w hwInf hwFin hN hQ y
      (fun j ↦ (hy j).1) (fun j ↦ (hy j).2.1) fun j ↦ (hy j).2.2,
    fun x hx hlo hhi ↦ Submodule.subset_span ⟨hx, hlo, hhi⟩⟩

private theorem exists_lt_of_chain {a : ℕ → ℝ} {t : ℝ} :
    ∀ m, a 0 ≤ t → t < a m → ∃ h < m, a h ≤ t ∧ t < a (h + 1)
  | 0, h0, hm => absurd (h0.trans_lt hm) (lt_irrefl _)
  | m + 1, h0, hm => by
    by_cases ht : t < a m
    · obtain ⟨h, hh, h1, h2⟩ := exists_lt_of_chain m h0 ht
      exact ⟨h, by omega, h1, h2⟩
    · exact ⟨m, by omega, not_lt.1 ht, hm⟩

omit [NumberField K] [Fintype ι] in
/-- **A chain of windows**, each covered by finitely many subspaces, covers its union by all of
them: if every point with `a h ≤ ht x < a (h + 1)` lies in a subspace of `T h`, then every point
with `a 0 ≤ ht x < a m` lies in one of the at most `∑_{h < m} #(T h)` subspaces of their union. -/
theorem exists_finset_submodule_of_chain {P : (ι → K) → Prop} {ht : (ι → K) → ℝ} (a : ℕ → ℝ)
    (T : ℕ → Finset (Submodule K (ι → K))) (hT : ∀ h, ∀ U ∈ T h, U ≠ ⊤)
    (hcov : ∀ h x, P x → a h ≤ ht x → ht x < a (h + 1) → ∃ U ∈ T h, x ∈ U) (m : ℕ) :
    ∃ T' : Finset (Submodule K (ι → K)), T'.card ≤ ∑ h ∈ Finset.range m, (T h).card ∧
      (∀ U ∈ T', U ≠ ⊤) ∧ ∀ x, P x → a 0 ≤ ht x → ht x < a m → ∃ U ∈ T', x ∈ U := by
  classical
  refine ⟨(Finset.range m).biUnion T, Finset.card_biUnion_le, fun U hU ↦ ?_,
    fun x hx h0 hm ↦ ?_⟩
  · obtain ⟨h, -, hU⟩ := Finset.mem_biUnion.1 hU
    exact hT h U hU
  · obtain ⟨h, hh, h1, h2⟩ := exists_lt_of_chain m h0 hm
    obtain ⟨U, hU, hxU⟩ := hcov h x hx h1 h2
    exact ⟨U, Finset.mem_biUnion.2 ⟨h, Finset.mem_range.2 hh, hU⟩, hxU⟩

end NumberField
