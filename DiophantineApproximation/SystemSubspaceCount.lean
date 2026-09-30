/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SystemDomain
public import DiophantineApproximation.ParametricSubspace
public import DiophantineApproximation.SubspaceIntervals
public import DiophantineApproximation.SubspaceSmall
public import DiophantineApproximation.ThresholdBound

/-!
# The quantitative Subspace Theorem for systems

**Milestone Q0.3** of the `QuantitativeSubspace` roadmap: Layer 6.1 as an interval result (Q0.2d),
fed to Layer 9.4. For a system of Layer 9.1 under Evertse's normalization (2.4)
(`NumberField.IsNormalizedSystem`), with forms over a Galois extension `E / K`, `n` forms, `t`
places and coefficients of absolute height at most `H`:

* the solutions with `log H(x) ≥ X₀ = systemThreshold` lie in at most `systemLargeCount` proper
  subspaces, a number depending on `n`, `δ`, `[E : ℚ]`, `[E : K]`, `t` and `|S|` alone;
* all solutions lie in at most that number, plus Layer 9.3's count for the solutions that are not
  large, plus `1 + log ω / log (1 + δ / (2 n))` for the large ones below `X₀`, where
  `ω = max (1, X₀ / ([K : ℚ] log Q))` and `Q` is the height from which a solution is large;
* `X₀` is linear in `log H`, with coefficients depending on `n`, `δ`, the fields and `S`
  (`systemThreshold_le`). It does not depend on the constants `C p`.

The route, for a solution `x` above `X₀`:

1. **Exponents from the solution** (`IsNormalizedSystem.exists_gridExponent`). The exponents
   `log |L p i x|_p / log H(x)` are at most `2` by the trivial bound `|L p i x|_p ≤ (n H^d)² H(x)`.
   Clamped below at `-M = -2 n t`, their weight is at most `-δ / 2`: either one is clamped, or
   their sum is `log ∏ |L p i x|_p / log H(x)`, and (2.4) gives
   `∏ |L p i x|_p ≤ systemDet · H(x) ^ (-δ)` with `systemDet ≤ (n! H^{n d}) ^ (2 t)`
   (`IsNormalizedSystem.systemDet_le`). Rounded up to the grid `ℤ / m`, `m = ⌈4 n t / δ⌉`, they
   become one of `systemGridCount` systems of weight at most `-δ / 4`, with constants `1`. Only
   the product bound on the constants is used, as in Evertse.
2. **Bridge** (Q0.2c): `x`, read in `Eⁿ`, lies in the approximation domain over `E` of the
   conjugated forms and the grid exponents at level `H(x)`.
3. **Layer 6.1 as an interval result** (Q0.2d) over `E`, once per grid system. Its threshold does
   not depend on the exponents, so all grid systems share it. Either the domain lies in one of the
   exceptional subspaces, whose `K`-points form a proper subspace of `Kⁿ`
   (`comap_algebraMapPi_ne_top`), or `log H(x)` lies in one of the intervals `[t, ρ t)`.
4. **Layer 9.4** turns each interval `[exp (t / [K : ℚ]), exp (t / [K : ℚ]) ^ ρ)` of the absolute
   affine height into `1 + log ρ / log (1 + δ / (2 n))` windows of the gap principle.

The counts of Layer 6.1 over `E` are bounded by those at `[E : ℚ]` infinite places and
`[E : ℚ] + [E : K] |S|` places, by monotonicity (`parametricSubspaceCount_mono`,
`parametricIntervalCount_mono`, `parametricRatio_mono`, `card_systemPlacesOver_le`). The heights
of the conjugated forms are those of the coefficients (`logHeight₁_algEquiv`,
`IsNormalizedSystem.formLogHeight_conjSystem_le`).

## Main results

* `NumberField.exists_finset_submodule_of_systemThreshold_le`: the large solutions above `X₀`.
* `NumberField.exists_finset_submodule_of_isNormalizedSystem`: all solutions.
* `NumberField.systemThreshold_le`: `X₀` in terms of `log H`, `|D_E|` and the norms of the
  primes of `E` above `S`.
* `NumberField.IsNormalizedSystem.exists_gridExponent`: the exponents of a solution on a grid.
* `NumberField.IsNormalizedSystem.linearIndependent`: the forms of a normalized system are
  independent at every place of the system.

## Implementation notes

⚠ **The forms are over a Galois extension `E / K`.** The bridge of Q0.2c needs it, to read the
places of `E` as conjugates. A system over an intermediate field is the same system over its
Galois closure (`NumberField.systemSet_compRingHom`), so this costs nothing but the degree.

⚠ **The grid replaces the constants.** Absorbing each `C p` into its own exponent would put
`max (0, log C p)` into the threshold, and (2.4) bounds only the product of the `C p`. Taking the
exponents from the solution and gridding them uses only the product, at the price of the factor
`systemGridCount` in the count.

⚠ **Below `X₀` one interval of Layer 9.4 covers the large solutions**, which costs `log X₀`, so
`O(log log H)`: the doubly logarithmic dependence on the heights of Schlickewei's count.

## References

J.-H. Evertse, *On the Quantitative Subspace Theorem*, Zap. Nauchn. Sem. POMI **377** (2010),
217–240 (arXiv:1008.2268), proof of Theorem 2.1. H. P. Schlickewei, "The quantitative Subspace
Theorem for number fields", *Compositio Math.* **82** (1992), 245–273.

This is milestone Q0.3 of the `QuantitativeSubspace` roadmap.
-/

@[expose] public section

open Finset Module NumberField IsDedekindDomain Height

namespace LinearMap

variable {F : Type*} [Field F] {ι : Type*} [Finite ι]

/-- A family of `#ι` forms on `Fⁱ` with nonzero determinant is linearly independent. -/
theorem linearIndependent_of_det_pi_ne_zero {l : ι → Dual F (ι → F)}
    (h : LinearMap.det (LinearMap.pi l) ≠ 0) : LinearIndependent F l := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  set ψ : Dual F (ι → F) →ₗ[F] (ι → F) :=
    LinearMap.pi fun j ↦ Module.Dual.eval F (ι → F) (Pi.single j 1) with hψ
  have hrows : LinearIndependent F fun i ↦ (LinearMap.toMatrix' (LinearMap.pi l)) i :=
    Matrix.linearIndependent_rows_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2
      (by rw [LinearMap.det_toMatrix']; exact h.isUnit))
  have hcomp : (fun i ↦ (LinearMap.toMatrix' (LinearMap.pi l)) i) = ψ ∘ l := by
    funext i; funext j; simp [hψ]
  rw [hcomp] at hrows
  exact LinearIndependent.of_comp ψ hrows

end LinearMap

namespace NumberField

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
variable {ι : Type*} [Fintype ι]

/-- **The forms of a normalized system are independent at every place of the system**: the
normalization makes the determinant product positive. -/
theorem IsNormalizedSystem.linearIndependent [Nonempty ι] {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w : AbsoluteValue K ℝ → AbsoluteValue E ℝ} {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)}
    {C : InfinitePlace K ⊕ S → ℝ} {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) (p : InfinitePlace K ⊕ S) :
    LinearIndependent E (L (systemPlace S p)) := by
  refine LinearMap.linearIndependent_of_det_pi_ne_zero fun h0 ↦ ?_
  have hpos := systemDet_pos hN
  rw [systemDet] at hpos
  have h : systemAbs S w p (LinearMap.det (LinearMap.pi (L (systemPlace S p)))) = 0 := by
    rw [systemAbs, h0, map_zero, zero_pow (systemMult_ne_zero S p)]
  exact hpos.ne' (Finset.prod_eq_zero (Finset.mem_univ p) h)

/-- `σ ≤ 1`. -/
theorem subspaceRatio_le_one {n s : ℕ} {ε A : ℝ} (hε : 0 < ε) (hA : 0 ≤ A) :
    subspaceRatio n s ε A ≤ 1 := by
  have h0 := subspaceEta_pos (n := n) hε hA
  have h1 : subspaceEta n ε A ≤ 1 := min_le_left _ _
  exact pow_le_one₀ (by positivity) (by linarith)

/-- The ratio of every grid system is at least `4`. -/
theorem four_le_parametricStepRatio {N : ℕ} (d s p : ℕ) {ε A : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (hA : 0 ≤ A) : 4 ≤ parametricStepRatio N d s p ε A := by
  have hδ := parametricDelta_pos hN hε
  have hW := parametricWedgeAbsWeight_nonneg N d p hε.le hA
  have h0 := subspaceRatio_pos (n := N.choose p - 1) (s := s) hδ hW
  have h1 := subspaceRatio_le_one (n := N.choose p - 1) (s := s) hδ hW
  have h2 : 1 ≤ (subspaceRatio (N.choose p - 1) s (parametricDelta N ε)
      (parametricWedgeAbsWeight N d p ε A))⁻¹ := (one_le_inv₀ h0).2 h1
  rw [parametricStepRatio]
  linarith

/-- **The ratio of the parametric Subspace Theorem is at least `1`.** -/
theorem one_le_parametricRatio {N : ℕ} (d s : ℕ) {ε A : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (hA : 0 ≤ A) : 1 ≤ parametricRatio N d s ε A := by
  rw [parametricRatio]
  calc (1 : ℝ) ≤ parametricStepRatio N d s 0 ε A := by
        linarith [four_le_parametricStepRatio d s 0 hN hε hA]
    _ ≤ ∑ p ∈ Finset.range N, parametricStepRatio N d s p ε A :=
        Finset.single_le_sum (f := fun p ↦ parametricStepRatio N d s p ε A)
          (fun p _ ↦ (parametricStepRatio_pos d s p hN hε hA).le) (Finset.mem_range.2 hN)

variable (K E ι) in
/-- The `K`-linear inclusion `Kⁱ → Eⁱ`. -/
noncomputable def algebraMapPi : (ι → K) →ₗ[K] (ι → E) :=
  LinearMap.pi fun j ↦ (Algebra.linearMap K E).comp (LinearMap.proj j)

omit [NumberField K] [NumberField E] [Fintype ι] in
theorem algebraMapPi_apply (x : ι → K) : algebraMapPi K E ι x = fun j ↦ algebraMap K E (x j) :=
  rfl

omit [NumberField K] [NumberField E] [Fintype ι] in
/-- **The `K`-points of a proper `E`-subspace form a proper `K`-subspace.** -/
theorem comap_algebraMapPi_ne_top [Finite ι] {W : Submodule E (ι → E)} (hW : W ≠ ⊤) :
    (W.restrictScalars K).comap (algebraMapPi K E ι) ≠ ⊤ := by
  classical
  intro htop
  apply hW
  rw [eq_top_iff, ← (Pi.basisFun E ι).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have hmem : (Pi.single j 1 : ι → K) ∈ (W.restrictScalars K).comap (algebraMapPi K E ι) :=
    htop ▸ Submodule.mem_top
  have hf : algebraMapPi K E ι (Pi.single j 1) = Pi.basisFun E ι j := by
    funext k
    rw [algebraMapPi_apply, Pi.basisFun_apply]
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  simpa [hf] using hmem

/-! ### Local bounds in terms of the coefficient height -/

omit [NumberField K] in
theorem systemMult_le_two (S : Finset (HeightOneSpectrum (𝓞 K))) (p : InfinitePlace K ⊕ S) :
    systemMult S p ≤ 2 := by
  rcases p with v | v
  · change v.mult ≤ 2
    unfold InfinitePlace.mult
    split_ifs <;> norm_num
  · exact one_le_two

/-- **A coefficient of a normalized system is at most `H ^ [E : ℚ]` at every place of the
system**: the absolute value lies over a place of `K`, so it is bounded by the relative height,
which is the `[E : ℚ]`-th power of the absolute one. -/
theorem IsNormalizedSystem.apply_coeff_le [DecidableEq ι] {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w : AbsoluteValue K ℝ → AbsoluteValue E ℝ}
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)}
    {C : InfinitePlace K ⊕ S → ℝ} {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) (p : InfinitePlace K ⊕ S) (i j : ι) :
    w (systemPlace S p) (L (systemPlace S p) i (Pi.single j 1)) ≤ H ^ finrank ℚ E := by
  set a := L (systemPlace S p) i (Pi.single j 1) with ha
  have hH : absMulHeight₁ a ≤ H := by
    have := hN.height_le p i j
    rwa [Pi.basisFun_apply] at this
  have hmax : max (w (systemPlace S p) a) 1 ≤ mulHeight₁ a := by
    rcases p with v | ⟨q, hq⟩
    · have : (w (systemPlace S (.inl v))).LiesOver v.1 := hwInf v
      exact max_apply_one_le_mulHeight₁_of_liesOver_infinitePlace v _ a
    · have : (w (systemPlace S (.inr ⟨q, hq⟩))).LiesOver (FinitePlace.mk q).1 := hwFin q hq
      exact max_apply_one_le_mulHeight₁_of_liesOver_finitePlace (FinitePlace.mk q) _ a
  refine (le_max_left _ _).trans (hmax.trans ?_)
  rw [← absMulHeight₁_pow_finrank]
  exact pow_le_pow_left₀ (zero_le_one.trans (one_le_absMulHeight₁ a)) hH _

theorem IsNormalizedSystem.one_le_height [Nonempty ι] {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w : AbsoluteValue K ℝ → AbsoluteValue E ℝ} {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)}
    {C : InfinitePlace K ⊕ S → ℝ} {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) : 1 ≤ H := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact (one_le_absMulHeight₁ _).trans (hN.height_le (.inl v) i i)

/-- **Every local value is at most `(n G) ^ mult` times the affine height**, if the coefficients
of the form are at most `G` at the place. -/
theorem systemValue_le_mul_mulHeightAff [DecidableEq ι] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    (L : AbsoluteValue K ℝ → ι → Dual E (ι → E)) (p : InfinitePlace K ⊕ S) (i : ι) (x : ι → K)
    {G : ℝ} (hG : ∀ j, w (systemPlace S p) (L (systemPlace S p) i (Pi.single j 1)) ≤ G) :
    systemValue S w L p i x ≤ (Fintype.card ι * G) ^ systemMult S p * mulHeightAff x := by
  have hlies : (w (systemPlace S p)).LiesOver (systemPlace S p) := by
    rcases p with v | v
    · exact hwInf v
    · exact hwFin v.1 v.2
  set m := systemMult S p with hm
  have hm0 : m ≠ 0 := systemMult_ne_zero S p
  set Q := mulHeightAff x with hQ
  have hQ0 : 0 ≤ Q := (mulHeightAff_pos x).le
  set T : ℝ := Q ^ (m⁻¹ : ℝ) with hT
  have hT0 : 0 ≤ T := Real.rpow_nonneg hQ0 _
  have hcoord : ∀ j, w (systemPlace S p) (algebraMap K E (x j)) ≤ T := fun j ↦ by
    rw [AbsoluteValue.apply_algebraMap_of_liesOver (v := systemPlace S p)]
    refine (pow_le_pow_iff_left₀ (apply_nonneg _ _) hT0 hm0).1 ?_
    rw [hT, Real.rpow_inv_natCast_pow hQ0 hm0]
    exact systemPlace_pow_le_mulHeightAff S p x j
  have hsum : w (systemPlace S p) (L (systemPlace S p) i fun j ↦ algebraMap K E (x j)) ≤
      T * (Fintype.card ι * G) := by
    rw [LinearMap.pi_apply_eq_sum_univ]
    refine (AbsoluteValue.sum_le _ _ _).trans ?_
    calc ∑ j, w (systemPlace S p) ((algebraMap K E (x j)) •
          L (systemPlace S p) i fun k ↦ if j = k then 1 else 0)
        ≤ ∑ _j : ι, T * G := Finset.sum_le_sum fun j _ ↦ by
          rw [smul_eq_mul, map_mul]
          have hj : (fun k ↦ if j = k then (1 : E) else 0) = Pi.single j 1 := by
            funext k; simp [Pi.single_apply, eq_comm]
          rw [hj]
          exact mul_le_mul (hcoord j) (hG j) (apply_nonneg _ _) hT0
      _ = T * (Fintype.card ι * G) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  calc systemValue S w L p i x ≤ (T * (Fintype.card ι * G)) ^ m :=
        pow_le_pow_left₀ (apply_nonneg _ _) hsum _
    _ = (Fintype.card ι * G) ^ m * Q := by
        rw [mul_pow, hT, Real.rpow_inv_natCast_pow hQ0 hm0, mul_comm]

/-- **The determinant product of a normalized system is at most `(n! G ^ n) ^ (2 t)`**, with
`G = H ^ [E : ℚ]` and `t` places. -/
theorem IsNormalizedSystem.systemDet_le {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w : AbsoluteValue K ℝ → AbsoluteValue E ℝ}
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)}
    {C : InfinitePlace K ⊕ S → ℝ} {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    systemDet S w L ≤ ((Fintype.card ι).factorial * (H ^ finrank ℚ E) ^ Fintype.card ι) ^
      (2 * (Fintype.card (InfinitePlace K) + #S)) := by
  classical
  have : Nonempty ι := Fintype.card_pos_iff.1 (by linarith [hN.two_le_card])
  set Z := ((Fintype.card ι).factorial * (H ^ finrank ℚ E) ^ Fintype.card ι : ℝ) with hZ
  have hH1 := hN.one_le_height
  have hZ1 : 1 ≤ Z := one_le_mul_of_one_le_of_one_le
    (Nat.one_le_cast.2 (Nat.factorial_pos _)) (one_le_pow₀ (one_le_pow₀ hH1))
  have hfac : ∀ p, systemAbs S w p (LinearMap.det (LinearMap.pi (L (systemPlace S p)))) ≤ Z ^ 2 :=
    fun p ↦ by
      have hdet : w (systemPlace S p) (LinearMap.det (LinearMap.pi (L (systemPlace S p)))) ≤ Z := by
        rw [← LinearMap.det_toMatrix']
        refine (AbsoluteValue.apply_det_le_factorial_mul_prod _ _
          (r := fun _ ↦ H ^ finrank ℚ E) fun i j ↦ ?_).trans ?_
        · rw [LinearMap.toMatrix'_pi_apply]
          exact hN.apply_coeff_le hwInf hwFin p i j
        · rw [Finset.prod_const, Finset.card_univ]
      rw [systemAbs]
      calc w (systemPlace S p) _ ^ systemMult S p ≤ Z ^ systemMult S p :=
            pow_le_pow_left₀ (apply_nonneg _ _) hdet _
        _ ≤ Z ^ 2 := pow_le_pow_right₀ hZ1 (systemMult_le_two S p)
  calc systemDet S w L ≤ ∏ _p : InfinitePlace K ⊕ S, Z ^ 2 :=
        Finset.prod_le_prod₀ (fun p _ ↦ pow_nonneg (apply_nonneg _ _) _) fun p _ ↦ hfac p
    _ = Z ^ (2 * (Fintype.card (InfinitePlace K) + #S)) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_sum, Fintype.card_coe, ← pow_mul]

omit [NumberField K] [Fintype ι] in
/-- **The height is invariant under the automorphisms of `E / K`.** -/
theorem logHeight₁_algEquiv (σ : E ≃ₐ[K] E) (a : E) :
    logHeight₁ (σ a) = logHeight₁ a := by
  have h : ![σ a, 1] = (σ : E ≃+* E) ∘ ![a, 1] := by
    funext k; fin_cases k <;> simp
  rw [logHeight₁, logHeight₁, mulHeight₁_eq_mulHeight, mulHeight₁_eq_mulHeight, h,
    mulHeight_comp_ringEquiv]

omit [Fintype ι] in
/-- The logarithmic height over `E` is `[E : ℚ]` times the logarithm of the absolute height. -/
theorem logHeight₁_le_of_absMulHeight₁_le {a : E} {H : ℝ} (h : absMulHeight₁ a ≤ H) :
    logHeight₁ a ≤ finrank ℚ E * Real.log H := by
  rw [logHeight₁, ← absMulHeight₁_pow_finrank, Real.log_pow]
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log (zero_lt_one.trans_le (one_le_absMulHeight₁ a)) h) (Nat.cast_nonneg _)

omit [NumberField K] [NumberField E] in
/-- **An entry of a conjugated form is a conjugate of a coefficient.** -/
theorem compRingHom_algEquiv_single [DecidableEq ι] (M : Dual E (ι → E)) (σ : E ≃ₐ[K] E)
    (i : ι) : M.compRingHom (σ : E →+* E) (Pi.single i 1) = σ (M (Pi.single i 1)) := by
  rw [Module.Dual.compRingHom_apply]
  simp [Pi.single_apply]

open scoped Classical in
/-- **The heights of the conjugated forms are those of the system**: every entry of their
matrices is a Galois conjugate of a coefficient, so `formLogHeight` over `E` is at most
`#places · n² · [E : ℚ] log H`. -/
theorem IsNormalizedSystem.formLogHeight_conjSystem_le [IsGalois K E] [DecidableEq ι]
    {S : Finset (HeightOneSpectrum (𝓞 K))} {w : AbsoluteValue K ℝ → AbsoluteValue E ℝ}
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)}
    {C : InfinitePlace K ⊕ S → ℝ} {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    formLogHeight (systemPlacesOver E S) (conjSystem univ (S.image FinitePlace.mk) w L) ≤
      (Fintype.card (InfinitePlace E) + #(systemPlacesOver E S)) * Fintype.card ι ^ 2 *
        (finrank ℚ E * Real.log H) := by
  have hentry : ∀ (t : InfinitePlace E ⊕ ↥(systemPlacesOver E S)) (j i : ι),
      logHeight₁ (formMatrix (conjSystem univ (S.image FinitePlace.mk) w L)
        (sPlace (systemPlacesOver E S) t) j i) ≤ finrank ℚ E * Real.log H := by
    intro t j i
    rw [formMatrix_apply]
    have hcoeff : ∀ p : InfinitePlace K ⊕ S,
        logHeight₁ (L (systemPlace S p) j (Pi.single i 1)) ≤ finrank ℚ E * Real.log H :=
      fun p ↦ logHeight₁_le_of_absMulHeight₁_le (by
        have := hN.height_le p j i
        rwa [Pi.basisFun_apply] at this)
    rcases t with V | ⟨V, hV⟩
    · obtain ⟨σ, -, heq⟩ := exists_conjSystem_inf (Sfin := S.image FinitePlace.mk) (L := L)
        (fun v _ ↦ hwInf v) (mem_univ _) (InfinitePlace.liesOver_comap (K := K) V)
      change logHeight₁ (conjSystem univ (S.image FinitePlace.mk) w L V.1 j (Pi.single i 1)) ≤ _
      rw [heq, compRingHom_algEquiv_single, logHeight₁_algEquiv]
      exact hcoeff (.inl _)
    · obtain ⟨q, hq, hVq⟩ := mem_systemPlacesOver.mp hV
      obtain ⟨σ, -, heq⟩ := exists_conjSystem_fin (Sinf := univ) (L := L)
        (fun v hv ↦ by
          obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hv
          exact hwFin q' hq') (Finset.mem_image_of_mem _ hq) hVq
      change logHeight₁ (conjSystem univ (S.image FinitePlace.mk) w L V.1 j (Pi.single i 1)) ≤ _
      rw [heq, compRingHom_algEquiv_single, logHeight₁_algEquiv]
      exact hcoeff (.inr ⟨q, hq⟩)
  calc formLogHeight (systemPlacesOver E S) (conjSystem univ (S.image FinitePlace.mk) w L)
      ≤ ∑ _t : (InfinitePlace E ⊕ ↥(systemPlacesOver E S)) × ι × ι,
          (finrank ℚ E * Real.log H) :=
        Finset.sum_le_sum fun t _ ↦ hentry t.1 t.2.1 t.2.2
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_coe]
        push_cast; ring

/-! ### The counts are monotone in the numbers of places -/

omit [NumberField K] [Algebra K E] [Fintype ι] in
/-- A number field has at most `[E : ℚ]` infinite places. -/
theorem card_infinitePlace_le_finrank : Fintype.card (InfinitePlace E) ≤ finrank ℚ E := by
  rw [← InfinitePlace.sum_mult_eq, Fintype.card_eq_sum_ones]
  exact Finset.sum_le_sum fun v _ ↦ Nat.one_le_iff_ne_zero.2 InfinitePlace.mult_ne_zero

omit [Fintype ι] in
/-- **At most `[E : K] |S|` places of `E` lie above `S`.** -/
theorem card_systemPlacesOver_le (S : Finset (HeightOneSpectrum (𝓞 K))) :
    #(systemPlacesOver E S) ≤ finrank K E * #S := by
  classical
  unfold systemPlacesOver
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ p ∈ S.attach, #(FinitePlace.placesOverFinset E (FinitePlace.mk p.1))
      ≤ ∑ _p ∈ S.attach, finrank K E := Finset.sum_le_sum fun p _ ↦ by
        rw [← FinitePlace.sum_localDegree (F := E) (FinitePlace.mk p.1)]
        simpa using Finset.card_nsmul_le_sum
          (FinitePlace.placesOverFinset E (FinitePlace.mk p.1)) (fun V ↦ V.localDegree K) 1
          (fun V _ ↦ V.localDegree_pos)
    _ = finrank K E * #S := by rw [Finset.sum_const, Finset.card_attach, smul_eq_mul, mul_comm]

theorem subspaceChainLength_mono {n s s' : ℕ} {ε A : ℝ} (hε : 0 < ε) (hA : 0 ≤ A) (hs : 1 ≤ s)
    (hss : s ≤ s') : subspaceChainLength n s ε A ≤ subspaceChainLength n s' ε A := by
  have hη := subspaceEta_pos (n := n) hε hA
  refine Nat.ceil_mono (div_le_div_of_nonneg_right ?_ (by positivity))
  refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) (by norm_num)
  have : (s : ℝ) ≤ s' := by exact_mod_cast hss
  gcongr

theorem subspaceRatio_anti {n s s' : ℕ} {ε A : ℝ} (hε : 0 < ε) (hA : 0 ≤ A) (hs : 1 ≤ s)
    (hss : s ≤ s') : subspaceRatio n s' ε A ≤ subspaceRatio n s ε A := by
  have hη := subspaceEta_pos (n := n) hε hA
  have h1 : subspaceEta n ε A ≤ 1 := min_le_left _ _
  exact pow_le_pow_of_le_one (by positivity) (by linarith)
    (Nat.pow_le_pow_right two_pos (subspaceChainLength_mono hε hA hs hss))

theorem parametricChainLength_mono {N d s s' p : ℕ} {ε A : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (hA : 0 ≤ A) (hs : 1 ≤ s) (hss : s ≤ s') :
    parametricChainLength N d s p ε A ≤ parametricChainLength N d s' p ε A :=
  subspaceChainLength_mono (parametricDelta_pos hN hε)
    (parametricWedgeAbsWeight_nonneg N d p hε.le hA) hs hss

theorem parametricStepRatio_mono {N d s s' p : ℕ} {ε A : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (hA : 0 ≤ A) (hs : 1 ≤ s) (hss : s ≤ s') :
    parametricStepRatio N d s p ε A ≤ parametricStepRatio N d s' p ε A := by
  have hδ := parametricDelta_pos hN hε
  have hW := parametricWedgeAbsWeight_nonneg N d p hε.le hA
  rw [parametricStepRatio, parametricStepRatio]
  exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ (subspaceRatio_pos hδ hW)
    (subspaceRatio_pos hδ hW)).2 (subspaceRatio_anti hδ hW hs hss)) four_pos.le

theorem parametricRatio_mono {N d s s' : ℕ} {ε A : ℝ} (hN : 0 < N) (hε : 0 < ε) (hA : 0 ≤ A)
    (hs : 1 ≤ s) (hss : s ≤ s') : parametricRatio N d s ε A ≤ parametricRatio N d s' ε A :=
  Finset.sum_le_sum fun _ _ ↦ parametricStepRatio_mono hN hε hA hs hss

theorem one_le_parametricGridBase (N d p : ℕ) {ε A : ℝ} (hε : 0 ≤ ε) (hA : 0 ≤ A) :
    1 ≤ (2 * parametricBox N d p ε A + 1).toNat := by
  have hm0 : 0 ≤ parametricBox N d p ε A := by
    refine Int.ceil_nonneg (div_nonneg ?_ (parametricMesh_nonneg N d p hε))
    rw [parametricMinimaExp]
    positivity
  omega

theorem parametricGridCount_mono {N d r r' p : ℕ} {ε A : ℝ} (hε : 0 ≤ ε) (hA : 0 ≤ A)
    (hrr : r ≤ r') : parametricGridCount N d r p ε A ≤ parametricGridCount N d r' p ε A :=
  Nat.pow_le_pow_right (one_le_parametricGridBase N d p hε hA)
    (Nat.mul_le_mul_right _ hrr)

theorem parametricSubspaceCount_mono {N d r r' s s' : ℕ} {ε A : ℝ} (hε : 0 ≤ ε) (hA : 0 ≤ A)
    (hrr : r ≤ r') (hss : s ≤ s') :
    parametricSubspaceCount N d r s ε A ≤ parametricSubspaceCount N d r' s' ε A := by
  refine Nat.add_le_add_left (Finset.sum_le_sum fun p _ ↦ ?_) 1
  exact Nat.mul_le_mul (parametricGridCount_mono hε hA hrr)
    (Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_left _ hss))

theorem parametricIntervalCount_mono {N d r r' s s' : ℕ} {ε A : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (hA : 0 ≤ A) (hs : 1 ≤ s) (hrr : r ≤ r') (hss : s ≤ s') :
    parametricIntervalCount N d r s ε A ≤ parametricIntervalCount N d r' s' ε A :=
  Finset.sum_le_sum fun _ _ ↦ Nat.mul_le_mul (parametricGridCount_mono hε.le hA hrr)
    (parametricChainLength_mono hN hε hA hs hss)

/-! ### The parameters -/

/-- **The depth of the lower clamp**, `M = 2 n t`, for `n` forms and `t` places: one exponent at
`-M` makes the weight negative, the others being at most `2`. -/
def systemClamp (n t : ℕ) : ℕ :=
  2 * n * t

/-- **The denominator of the grid**, `m = ⌈4 n t / δ⌉`: rounding up to `ℤ / m` raises the weight
by at most `δ / 4`. -/
noncomputable def systemGridDen (n t : ℕ) (δ : ℝ) : ℕ :=
  ⌈4 * n * t / δ⌉₊

/-- **The number of grid systems**, `(M m + 2 m + 1) ^ (t n)`: the exponents are `k / m` with
`-M m ≤ k ≤ 2 m`. -/
noncomputable def systemGridCount (n t : ℕ) (δ : ℝ) : ℕ :=
  (systemClamp n t * systemGridDen n t δ + 2 * systemGridDen n t δ + 1) ^ (t * n)

/-- **The weight margin over `E`**, `ε = [E : K] δ / 4`. -/
noncomputable def systemEps (e : ℕ) (δ : ℝ) : ℝ :=
  e * δ / 4

/-- **The bound on the absolute weight over `E`**, `A = [E : K] t n (M + 2)`. -/
noncomputable def systemAbsBound (e n t : ℕ) : ℝ :=
  e * (t * n * (systemClamp n t + 2))

/-- **The part of the threshold that comes from the system itself**, in the coefficient height
`H`: `2 log (n H ^ d)`, above which every local value is at most `H(x) ^ 2`, and
`4 t log (n! H ^ (n d)) / δ`, above which the determinant product costs at most `δ / 2` of the
weight. Here `d = [E : ℚ]`. -/
noncomputable def systemHeightThreshold (n d t : ℕ) (δ H : ℝ) : ℝ :=
  max (2 * (Real.log n + d * Real.log H))
    (4 * t * (Real.log n.factorial + n * (d * Real.log H)) / δ)

variable (E) in
open scoped Classical in
/-- **The threshold of the quantitative Subspace Theorem for a system**, on the scale of
`log H(x)`: the largest of the threshold of Layer 6.1 for the conjugated forms over `E` (shared
by all grid systems), of `[K : ℚ] (2 n / δ) log n` (so that the gap principle applies), and of
`systemHeightThreshold`. It does not depend on the constants `C`. -/
noncomputable def systemThreshold (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ) (L : AbsoluteValue K ℝ → ι → Dual E (ι → E))
    (H δ : ℝ) : ℝ :=
  max (parametricThreshold (systemPlacesOver E S) (conjSystem univ (S.image FinitePlace.mk) w L)
      (systemEps (finrank K E) δ)
      (systemAbsBound (finrank K E) (Fintype.card ι) (Fintype.card (InfinitePlace K) + #S)))
    (max (finrank ℚ K * (2 * Fintype.card ι / δ) * Real.log (Fintype.card ι))
      (systemHeightThreshold (Fintype.card ι) (finrank ℚ E) (Fintype.card (InfinitePlace K) + #S)
        δ H))

/-- **The number of subspaces of the large solutions**: for each grid system, Layer 6.1's
exceptional subspaces over `E` and, for each of its intervals, the windows of the gap principle.
The parameters are `n` forms, `d = [E : ℚ]`, `e = [E : K]`, `t` places of the system and
`|S| = u`; Layer 6.1's counts are taken at `d` infinite places and `d + e u` places, which bound
those of `E`. -/
noncomputable def systemLargeCount (n d e t u : ℕ) (δ : ℝ) : ℝ :=
  systemGridCount n t δ *
    (parametricSubspaceCount n d d (d + e * u) (systemEps e δ) (systemAbsBound e n t) +
      parametricIntervalCount n d d (d + e * u) (systemEps e δ) (systemAbsBound e n t) *
        (1 + Real.log (parametricRatio n d (d + e * u) (systemEps e δ) (systemAbsBound e n t)) /
          Real.log (1 + δ / (2 * n))))

/-- **The ratio of the middle interval**: the large solutions below the threshold `X` have
absolute affine height in `[Q, Q ^ ω)` with `Q = max (2 H) (n ^ (2 n / δ))` and
`ω = max (1, X / ([K : ℚ] log Q))`. -/
noncomputable def systemMiddleRatio (d n : ℕ) (H δ X : ℝ) : ℝ :=
  max 1 (X / (d * Real.log (max (2 * H) ((n : ℝ) ^ (2 * n / δ)))))

/-! ### The exponents of a solution, on a grid -/

omit [NumberField E] in
private theorem sum_single_eq_one {S : Finset (HeightOneSpectrum (𝓞 K))} [DecidableEq ι]
    [DecidableEq (InfinitePlace K ⊕ S)] (p₀ : InfinitePlace K ⊕ S) (i₀ : ι) :
    ∑ p, ∑ i, (Pi.single p₀ (Pi.single i₀ (1 : ℝ)) : InfinitePlace K ⊕ S → ι → ℝ) p i = 1 := by
  rw [Finset.sum_eq_single p₀ (fun p _ hp ↦ by simp [hp]) (by simp)]
  simp

/-- **The exponents of a large solution lie on a grid.** Under the normalization, a solution `x`
with `log H(x) ≥ systemHeightThreshold` meets `|L p i x|_p ≤ H(x) ^ (k p i / m)` for integers
`-M m ≤ k p i ≤ 2 m` whose system has weight at most `-δ / 4`. The exponents are
`log |L p i x|_p / log H(x)`, clamped below at `-M` and rounded up; they are at most `2` by the
trivial bound, and their weight is at most `-δ / 2` before rounding, by the product bound
`∏ |L p i x|_p ≤ systemDet · H(x) ^ (-δ)` of (2.4), or because one of them is clamped. -/
theorem IsNormalizedSystem.exists_gridExponent {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w : AbsoluteValue K ℝ → AbsoluteValue E ℝ}
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)}
    {C : InfinitePlace K ⊕ S → ℝ} {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) {x : ι → K} (hx : x ∈ systemSet S w L C c)
    (hlog : systemHeightThreshold (Fintype.card ι) (finrank ℚ E)
      (Fintype.card (InfinitePlace K) + #S) δ H ≤ Real.log (mulHeightAff x)) :
    ∃ k : InfinitePlace K ⊕ S → ι → ℤ,
      (∀ p i, -((systemClamp (Fintype.card ι) (Fintype.card (InfinitePlace K) + #S) *
          systemGridDen (Fintype.card ι) (Fintype.card (InfinitePlace K) + #S) δ : ℕ) : ℤ) ≤
          k p i ∧
        k p i ≤ 2 * (systemGridDen (Fintype.card ι) (Fintype.card (InfinitePlace K) + #S) δ : ℤ))
      ∧ systemWeight (fun p i ↦ (k p i : ℝ) /
          systemGridDen (Fintype.card ι) (Fintype.card (InfinitePlace K) + #S) δ) ≤ -(δ / 4)
      ∧ ∀ p i, systemValue S w L p i x ≤ mulHeightAff x ^ ((k p i : ℝ) /
          systemGridDen (Fintype.card ι) (Fintype.card (InfinitePlace K) + #S) δ) := by
  classical
  set n := Fintype.card ι with hn
  set t := Fintype.card (InfinitePlace K) + #S with ht
  set M := systemClamp n t with hM
  set m := systemGridDen n t δ with hm
  have hn2 : 2 ≤ n := hN.two_le_card
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hδ := hN.delta_pos
  have hδ1 := hN.delta_le_one
  have hH1 := hN.one_le_height
  have hcardS : Fintype.card (InfinitePlace K ⊕ S) = t := by
    rw [Fintype.card_sum, Fintype.card_coe]
  have ht1 : 1 ≤ t := by
    have := Fintype.card_pos (α := InfinitePlace K)
    omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hMdef : (M : ℝ) = 2 * n * t := by rw [hM, systemClamp]; push_cast; ring
  have hm4 : 4 * n * t / δ ≤ (m : ℝ) := Nat.le_ceil _
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hm4
  have hmδ : (t : ℝ) * n / m ≤ δ / 4 := by
    rw [div_le_iff₀ hm0]
    rw [div_le_iff₀ hδ] at hm4
    linarith
  set Hx := mulHeightAff x with hHx
  have hHx0 : 0 < Hx := mulHeightAff_pos x
  set G : ℝ := H ^ finrank ℚ E with hG
  have hG1 : 1 ≤ G := one_le_pow₀ hH1
  have hnG : 1 ≤ (n : ℝ) * G := one_le_mul_of_one_le_of_one_le (by exact_mod_cast (by omega :
    1 ≤ n)) hG1
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH1
  have hlognG : Real.log ((n : ℝ) * G) = Real.log n + finrank ℚ E * Real.log H := by
    rw [Real.log_mul hn0.ne' (by positivity), hG, Real.log_pow]
  have h2 : 2 * Real.log ((n : ℝ) * G) ≤ Real.log Hx := by
    rw [hlognG]; exact (le_max_left _ _).trans hlog
  have hlH : 0 < Real.log Hx := by
    have : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    rw [hlognG] at h2
    nlinarith [Nat.cast_nonneg (α := ℝ) (finrank ℚ E)]
  have hHx1 : 1 ≤ Hx := le_of_lt ((Real.log_pos_iff hHx0.le).1 hlH)
  set lH := Real.log Hx with hlHdef
  -- the exponents
  set v : InfinitePlace K ⊕ S → ι → ℝ := fun p i ↦ systemValue S w L p i x with hv
  have hv0 : ∀ p i, 0 ≤ v p i := fun p i ↦ systemValue_nonneg S w L p i x
  set f : InfinitePlace K ⊕ S → ι → ℝ := fun p i ↦
    if v p i = 0 then -(M : ℝ) else Real.log (v p i) / lH with hf
  set e : InfinitePlace K ⊕ S → ι → ℝ := fun p i ↦ max (-(M : ℝ)) (f p i) with he
  set k : InfinitePlace K ⊕ S → ι → ℤ := fun p i ↦ ⌈e p i * m⌉ with hk
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hf2 : ∀ p i, f p i ≤ 2 := fun p i ↦ by
    simp only [hf]
    split_ifs with h0
    · linarith
    · have hvpos : 0 < v p i := lt_of_le_of_ne (hv0 p i) (Ne.symm h0)
      have hle : v p i ≤ ((n : ℝ) * G) ^ 2 * Hx := by
        refine (systemValue_le_mul_mulHeightAff S w hwInf hwFin L p i x
          (fun j ↦ hN.apply_coeff_le hwInf hwFin p i j)).trans ?_
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hnG (systemMult_le_two S p))
          hHx0.le
      rw [div_le_iff₀ hlH]
      have := Real.log_le_log hvpos hle
      rw [Real.log_mul (by positivity) hHx0.ne', Real.log_pow] at this
      push_cast at this
      linarith
  have he2 : ∀ p i, e p i ≤ 2 := fun p i ↦ max_le (by linarith) (hf2 p i)
  have hkm : ∀ p i, e p i ≤ (k p i : ℝ) / m := fun p i ↦ by
    rw [le_div_iff₀ hm0]; exact Int.le_ceil _
  have hkm' : ∀ p i, (k p i : ℝ) / m ≤ e p i + 1 / m := fun p i ↦ by
    rw [div_le_iff₀ hm0, add_mul, one_div_mul_cancel hm0.ne']
    exact (Int.ceil_lt_add_one _).le
  refine ⟨k, fun p i ↦ ⟨?_, ?_⟩, ?_, fun p i ↦ ?_⟩
  · have h1 : (((-((M * m : ℕ) : ℤ)) : ℤ) : ℝ) ≤ e p i * m := by
      push_cast
      nlinarith [le_max_left (-(M : ℝ)) (f p i)]
    exact Int.cast_le.1 (h1.trans (Int.le_ceil _))
  · refine Int.ceil_le.2 ?_
    push_cast
    nlinarith [he2 p i]
  · -- the weight
    have hsum_e : systemWeight e ≤ -(δ / 2) := by
      by_cases hcl : ∃ p i, e p i = -(M : ℝ)
      · obtain ⟨p₀, i₀, h₀⟩ := hcl
        set g : InfinitePlace K ⊕ S → ι → ℝ := Pi.single p₀ (Pi.single i₀ 1) with hg
        have hle : ∀ p i, e p i ≤ 2 - ((M : ℝ) + 2) * g p i := by
          intro p i
          by_cases hp : p = p₀
          · subst hp
            by_cases hi : i = i₀
            · subst hi
              simp only [hg, Pi.single_eq_same, mul_one, h₀]
              linarith
            · simp only [hg, Pi.single_eq_same, Pi.single_eq_of_ne hi, mul_zero, sub_zero]
              exact he2 p i
          · simp only [hg, Pi.single_eq_of_ne hp, Pi.zero_apply, mul_zero, sub_zero]
            exact he2 p i
        calc systemWeight e ≤ ∑ p, ∑ i, (2 - ((M : ℝ) + 2) * g p i) :=
              Finset.sum_le_sum fun p _ ↦ Finset.sum_le_sum fun i _ ↦ hle p i
          _ = 2 * (t * n) - ((M : ℝ) + 2) := by
              simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hg, sum_single_eq_one,
                Finset.sum_const, Finset.card_univ, hcardS, nsmul_eq_mul]
              ring
          _ ≤ -(δ / 2) := by rw [hMdef]; nlinarith
      · push Not at hcl
        have hpos : ∀ p i, v p i ≠ 0 := fun p i h0 ↦ hcl p i (by
          simp only [he, hf, h0, ↓reduceIte, max_self])
        have hef : ∀ p i, e p i = Real.log (v p i) / lH := fun p i ↦ by
          have hne := hcl p i
          simp only [he, hf, hpos p i, ↓reduceIte] at hne ⊢
          rcases le_total (-(M : ℝ)) (Real.log (v p i) / lH) with h | h
          · exact max_eq_right h
          · exact absurd (max_eq_left h) hne
        have hprod : ∏ p, ∏ i, v p i ≤ systemDet S w L * Hx ^ (-δ) := by
          have := affineProd_le_systemDet_mul_rpow hN hx
          rwa [affineProd_eq_prod_systemValue] at this
        have hdet0 := systemDet_pos hN
        set Z : ℝ := (n.factorial : ℝ) * G ^ n with hZ
        have hZ1 : 1 ≤ Z := one_le_mul_of_one_le_of_one_le
          (Nat.one_le_cast.2 (Nat.factorial_pos _)) (one_le_pow₀ hG1)
        have hdetZ : Real.log (systemDet S w L) ≤ 2 * t * Real.log Z := by
          have h : systemDet S w L ≤ Z ^ (2 * t) := hN.systemDet_le hwInf hwFin
          have h' := Real.log_le_log hdet0 h
          rw [Real.log_pow] at h'
          push_cast at h'
          linarith
        have hlogZ : Real.log Z = Real.log n.factorial + n * (finrank ℚ E * Real.log H) := by
          rw [hZ, Real.log_mul (by positivity) (by positivity), Real.log_pow, hG, Real.log_pow]
        have hZlH : 4 * t * Real.log Z / δ ≤ lH := by
          rw [hlogZ]; exact (le_max_right _ _).trans hlog
        have hZlH' : 2 * t * Real.log Z ≤ δ / 2 * lH := by
          rw [div_le_iff₀ hδ] at hZlH
          linarith
        have hlog_prod : Real.log (∏ p, ∏ i, v p i) = ∑ p, ∑ i, Real.log (v p i) := by
          rw [Real.log_prod fun p _ ↦ Finset.prod_ne_zero_iff.2 fun i _ ↦ hpos p i]
          exact Finset.sum_congr rfl fun p _ ↦ Real.log_prod fun i _ ↦ hpos p i
        have hle : ∑ p, ∑ i, Real.log (v p i) ≤ Real.log (systemDet S w L) - δ * lH := by
          rw [← hlog_prod]
          have hprod0 : 0 < ∏ p, ∏ i, v p i := Finset.prod_pos fun p _ ↦
            Finset.prod_pos fun i _ ↦ lt_of_le_of_ne (hv0 p i) (Ne.symm (hpos p i))
          refine (Real.log_le_log hprod0 hprod).trans_eq ?_
          rw [Real.log_mul hdet0.ne' (Real.rpow_pos_of_pos hHx0 _).ne', Real.log_rpow hHx0]
          ring
        calc systemWeight e = (∑ p, ∑ i, Real.log (v p i)) / lH := by
              rw [systemWeight, Finset.sum_div]
              exact Finset.sum_congr rfl fun p _ ↦ by
                rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ ↦ hef p i
          _ ≤ -(δ / 2) := by
              rw [div_le_iff₀ hlH]
              linarith
    calc systemWeight (fun p i ↦ (k p i : ℝ) / m) ≤ ∑ p, ∑ i, (e p i + 1 / m) :=
          Finset.sum_le_sum fun p _ ↦ Finset.sum_le_sum fun i _ ↦ hkm' p i
      _ = systemWeight e + t * n / m := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcardS,
            nsmul_eq_mul, systemWeight]
          ring
      _ ≤ -(δ / 4) := by linarith
  · -- the local values
    change v p i ≤ Hx ^ ((k p i : ℝ) / m)
    by_cases h0 : v p i = 0
    · rw [h0]; exact Real.rpow_nonneg hHx0.le _
    · have hvpos : 0 < v p i := lt_of_le_of_ne (hv0 p i) (Ne.symm h0)
      have hfe : f p i = Real.log (v p i) / lH := by simp only [hf, h0, ↓reduceIte]
      have hvf : v p i = Hx ^ f p i := by
        rw [hfe, Real.rpow_def_of_pos hHx0, mul_div_cancel₀ _ hlH.ne', Real.exp_log hvpos]
      rw [hvf]
      exact Real.rpow_le_rpow_of_exponent_le hHx1 ((le_max_right _ _).trans (hkm p i))

/-! ### The large solutions -/

open scoped Classical in
/-- **The quantitative Subspace Theorem for the large solutions of a system** (Q0.3). Under the
normalization (2.4), with forms over a Galois extension `E / K`, the solutions `x` with
`log H(x) ≥ systemThreshold` lie in at most `systemLargeCount` proper subspaces of `Kⁿ`, a
number that depends on `n`, `δ`, `[E : ℚ]`, `[E : K]`, the number of infinite places of `K` and
`|S|` only. -/
theorem exists_finset_submodule_of_systemThreshold_le [IsGalois K E]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    ∃ T : Finset (Submodule K (ι → K)),
      (#T : ℝ) ≤ systemLargeCount (Fintype.card ι) (finrank ℚ E) (finrank K E)
        (Fintype.card (InfinitePlace K) + #S) #S δ ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x ∈ systemSet S w L C c, systemThreshold E S w L H δ ≤ Real.log (mulHeightAff x) →
        ∃ U ∈ T, x ∈ U := by
  set n := Fintype.card ι with hn
  have hn2 : 2 ≤ n := hN.two_le_card
  have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hδ := hN.delta_pos
  set e := finrank K E with he
  set dE := finrank ℚ E with hdE
  set t := Fintype.card (InfinitePlace K) + #S with ht
  set M := systemClamp n t with hM
  set m := systemGridDen n t δ with hm
  have he0 : (0 : ℝ) < e := by exact_mod_cast (finrank_pos : 0 < finrank K E)
  have hm0 : (0 : ℝ) < m := by
    have ht1 : 1 ≤ t := by
      have := Fintype.card_pos (α := InfinitePlace K)
      omega
    have ht0 : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
    exact lt_of_lt_of_le (by positivity) (Nat.le_ceil (4 * n * t / δ))
  -- the grid systems
  set Gr : Finset (InfinitePlace K ⊕ S → ι → ℤ) := Fintype.piFinset fun _ ↦
    Fintype.piFinset fun _ ↦ Finset.Icc (-((M * m : ℕ) : ℤ)) (2 * (m : ℤ)) with hGr
  have hGrcard : #Gr = systemGridCount n t δ := by
    rw [hGr, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_sum,
      Fintype.card_coe]
    simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Int.card_Icc]
    rw [systemGridCount, ← pow_mul, mul_comm n t, ← hM, ← hm]
    congr 1
    have h : 2 * (m : ℤ) + 1 - -((M * m : ℕ) : ℤ) = ((M * m + 2 * m + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [h, Int.toNat_natCast]
  set g : (InfinitePlace K ⊕ S → ι → ℤ) → InfinitePlace K ⊕ S → ι → ℝ :=
    fun k p i ↦ (k p i : ℝ) / m with hg
  set Sfin' := systemPlacesOver E S with hSfin'
  set L' := conjSystem univ (S.image FinitePlace.mk) w L with hL'
  set ε := systemEps e δ with hε
  set A := systemAbsBound e n t with hA
  have hε0 : 0 < ε := by rw [hε, systemEps]; positivity
  have hA0 : 0 ≤ A := by rw [hA, systemAbsBound]; positivity
  set rE := Fintype.card (InfinitePlace E) with hrE
  set sE := rE + #Sfin' with hsE
  have hrE : rE ≤ dE := card_infinitePlace_le_finrank
  have hsE : sE ≤ dE + e * #S := Nat.add_le_add hrE (card_systemPlacesOver_le S)
  have hsE1 : 1 ≤ sE := by
    have := Fintype.card_pos (α := InfinitePlace E)
    omega
  have hLI : ∀ v : InfinitePlace K, LinearIndependent E (L v.1) := fun v ↦
    hN.linearIndependent (.inl v)
  have hLF : ∀ p ∈ S, LinearIndependent E (L (FinitePlace.mk p).1) := fun p hp ↦
    hN.linearIndependent (.inr ⟨p, hp⟩)
  set X₀ := systemThreshold E S w L H δ with hX₀
  have hX₀P : parametricThreshold Sfin' L' ε A ≤ X₀ := le_max_left _ _
  have hX₀n : (finrank ℚ K : ℝ) * (2 * n / δ) * Real.log n ≤ X₀ :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hX₀H : systemHeightThreshold n dE t δ H ≤ X₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hX₀1 : 1 ≤ X₀ := (le_max_left _ _).trans hX₀P
  set ρE := parametricRatio n dE sE ε A with hρE
  -- Layer 6.1 for every grid system of weight at most `-δ / 4`
  have hfam : ∀ k : InfinitePlace K ⊕ S → ι → ℤ, ∃ T : Finset (Submodule E (ι → E)),
      #T ≤ parametricSubspaceCount n dE rE sE ε A ∧ (∀ W ∈ T, W ≠ ⊤) ∧
      ∃ 𝒯 : Finset ℝ, #𝒯 ≤ parametricIntervalCount n dE rE sE ε A ∧ (∀ s ∈ 𝒯, X₀ ≤ s) ∧
        (k ∈ Gr → systemWeight (g k) ≤ -(δ / 4) → ∀ Q : ℝ, 1 < Q → X₀ ≤ Real.log Q →
          (∃ W ∈ T, approxDomain Sfin' L' (conjExponent S (g k)) Q ⊆ W) ∨
            ∃ s ∈ 𝒯, s ≤ Real.log Q ∧ Real.log Q < ρE * s) := by
    intro k
    by_cases hk : k ∈ Gr ∧ systemWeight (g k) ≤ -(δ / 4)
    · obtain ⟨hkG, hkw⟩ := hk
      have hcw : approxWeight Sfin' (conjExponent S (g k)) ≤ -ε := by
        rw [approxWeight_conjExponent, hε, systemEps]
        nlinarith
      have hcA : approxAbsWeight Sfin' (conjExponent S (g k)) ≤ A := by
        rw [approxAbsWeight_conjExponent, hA, systemAbsBound]
        refine mul_le_mul_of_nonneg_left ?_ he0.le
        have hbd : ∀ p i, |g k p i| ≤ (M : ℝ) + 2 := fun p i ↦ by
          have hki := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hkG p) i)
          have h1 : -((M : ℝ) * m) ≤ k p i := by exact_mod_cast hki.1
          have h2 : (k p i : ℝ) ≤ 2 * m := by exact_mod_cast hki.2
          simp only [hg]
          rw [abs_div, abs_of_pos hm0, div_le_iff₀ hm0, abs_le]
          constructor <;> nlinarith
        calc ∑ p, ∑ i, |g k p i| ≤ ∑ _p : InfinitePlace K ⊕ S, ∑ _i : ι, ((M : ℝ) + 2) :=
              Finset.sum_le_sum fun p _ ↦ Finset.sum_le_sum fun i _ ↦ hbd p i
          _ = t * n * (M + 2) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_coe,
                nsmul_eq_mul, ht]
              push_cast; ring
      obtain ⟨T, hTcard, hTtop, Q₀, -, hQ₀eq, hint⟩ :=
        exists_forall_mem_interval_approxDomain (K := E) (Sfin := Sfin') (L := L')
          (linearIndependent_conjSystem_infinitePlace hwInf hLI)
          (fun V hV ↦ linearIndependent_conjSystem_systemPlacesOver hwFin hLF hV) hε0 hcw hcA
      obtain ⟨𝒯, h𝒯card, h𝒯ge, hQint⟩ := hint X₀ (hQ₀eq ▸ hX₀P)
      exact ⟨T, hTcard, hTtop, 𝒯, h𝒯card, h𝒯ge, fun _ _ ↦ hQint⟩
    · exact ⟨∅, by simp, by simp, ∅, by simp, by simp, fun hkG hkw ↦ absurd ⟨hkG, hkw⟩ hk⟩
  choose Tk hTkcard hTktop 𝒯k h𝒯kcard h𝒯kge hTkint using hfam
  set T₀ := Gr.biUnion Tk with hT₀
  set 𝒯 := Gr.biUnion 𝒯k with h𝒯
  set T₁ := T₀.image fun W ↦ (W.restrictScalars K).comap (algebraMapPi K E ι) with hT₁
  -- the intervals, as intervals of the absolute affine height
  set d := finrank ℚ K with hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (finrank_pos : 0 < finrank ℚ K)
  set ρ := parametricRatio n dE (dE + e * #S) ε A with hρ
  have hρ1 : 1 ≤ ρ := one_le_parametricRatio _ _ (by omega) hε0 hA0
  have hρρ : ρE ≤ ρ := parametricRatio_mono (by omega) hε0 hA0 hsE1 hsE
  set Q : Fin #𝒯 → ℝ := fun i ↦ Real.exp ((𝒯.equivFin.symm i : ℝ) / d) with hQ
  have hQn : ∀ i, (n : ℝ) ^ (2 * n / δ) ≤ Q i := fun i ↦ by
    rw [Real.rpow_def_of_pos hn0]
    refine Real.exp_le_exp.2 ((le_div_iff₀ hd0).2 ?_)
    obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.1 (𝒯.equivFin.symm i).2
    have := h𝒯kge k _ hk
    nlinarith
  obtain ⟨T₂, hT₂card, hT₂top, hT₂⟩ := exists_finset_submodule_of_forall_mem_interval_of_mem S w
    hwInf hwFin hN {x | X₀ ≤ Real.log (mulHeightAff x) ∧ ∀ U ∈ T₁, x ∉ U} Q hQn hρ1
    (fun x hx hxX ↦ by
      have hH := mulHeightAff_pos x
      obtain ⟨hlogH, hxT⟩ := hxX
      obtain ⟨k, hkG, hkw, hkv⟩ := hN.exists_gridExponent hwInf hwFin hx (hX₀H.trans hlogH)
      have hkGr : k ∈ Gr := Fintype.mem_piFinset.2 fun p ↦ Fintype.mem_piFinset.2 fun i ↦
        Finset.mem_Icc.2 (hkG p i)
      have hy := mem_approxDomain_conjSystem hwInf hwFin L hH.le hx.1 (e := g k) hkv
      have hH1 : 1 < mulHeightAff x := by
        rw [← Real.log_pos_iff hH.le]; linarith
      rcases hTkint k hkGr hkw (mulHeightAff x) hH1 hlogH with ⟨W, hW, hsub⟩ | ⟨s, hs, h1, h2⟩
      · exact absurd (hsub hy) fun hyW ↦ hxT _ (Finset.mem_image_of_mem _
          (Finset.mem_biUnion.2 ⟨k, hkGr, hW⟩)) hyW
      · have hs𝒯 : s ∈ 𝒯 := Finset.mem_biUnion.2 ⟨k, hkGr, hs⟩
        have hs0 : 0 ≤ s := by linarith [h𝒯kge k s hs]
        refine ⟨𝒯.equivFin ⟨s, hs𝒯⟩, ?_, ?_⟩
        · simp only [hQ, Equiv.symm_apply_apply]
          rw [Real.rpow_def_of_pos hH]
          refine Real.exp_le_exp.2 ?_
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hd0.le)
        · simp only [hQ, Equiv.symm_apply_apply]
          rw [Real.rpow_def_of_pos hH, ← Real.exp_mul]
          refine Real.exp_lt_exp.2 ?_
          rw [div_mul_eq_mul_div, mul_comm (s : ℝ) ρ, div_eq_mul_inv]
          exact mul_lt_mul_of_pos_right (h2.trans_le (mul_le_mul_of_nonneg_right hρρ hs0))
            (inv_pos.2 hd0))
  refine ⟨T₁ ∪ T₂, ?_, fun U hU ↦ ?_, fun x hx hlogH ↦ ?_⟩
  · have hl : 0 < Real.log (1 + δ / (2 * n)) := Real.log_pos (by
      have : 0 < δ / (2 * n) := by positivity
      linarith)
    have hfac : 0 ≤ 1 + Real.log ρ / Real.log (1 + δ / (2 * n)) :=
      add_nonneg zero_le_one (div_nonneg (Real.log_nonneg hρ1) hl.le)
    have hSC : parametricSubspaceCount n dE rE sE ε A ≤
        parametricSubspaceCount n dE dE (dE + e * #S) ε A :=
      parametricSubspaceCount_mono hε0.le hA0 hrE hsE
    have hIC : parametricIntervalCount n dE rE sE ε A ≤
        parametricIntervalCount n dE dE (dE + e * #S) ε A :=
      parametricIntervalCount_mono (by omega) hε0 hA0 hsE1 hrE hsE
    have hT₀ : #T₀ ≤ systemGridCount n t δ * parametricSubspaceCount n dE dE (dE + e * #S) ε A :=
      Finset.card_biUnion_le.trans ((Finset.sum_le_sum fun k _ ↦ (hTkcard k).trans hSC).trans
        (by rw [Finset.sum_const, smul_eq_mul, hGrcard]))
    have h𝒯c : #𝒯 ≤ systemGridCount n t δ * parametricIntervalCount n dE dE (dE + e * #S) ε A :=
      Finset.card_biUnion_le.trans ((Finset.sum_le_sum fun k _ ↦ (h𝒯kcard k).trans hIC).trans
        (by rw [Finset.sum_const, smul_eq_mul, hGrcard]))
    calc (#(T₁ ∪ T₂) : ℝ) ≤ #T₀ + #T₂ := by
          exact_mod_cast (Finset.card_union_le _ _).trans
            (Nat.add_le_add_right Finset.card_image_le _)
      _ ≤ systemGridCount n t δ * parametricSubspaceCount n dE dE (dE + e * #S) ε A +
          (systemGridCount n t δ * parametricIntervalCount n dE dE (dE + e * #S) ε A : ℕ) *
            (1 + Real.log ρ / Real.log (1 + δ / (2 * n))) := by
          refine add_le_add (by exact_mod_cast hT₀) (hT₂card.trans ?_)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast h𝒯c) hfac
      _ = _ := by
          rw [systemLargeCount]
          push_cast
          ring
  · rcases Finset.mem_union.1 hU with hU | hU
    · obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hU
      obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.1 hW
      exact comap_algebraMapPi_ne_top (hTktop k W hk)
    · exact hT₂top U hU
  · by_cases hxT : ∃ U ∈ T₁, x ∈ U
    · obtain ⟨U, hU, hxU⟩ := hxT
      exact ⟨U, Finset.mem_union_left _ hU, hxU⟩
    · push Not at hxT
      obtain ⟨U, hU, hxU⟩ := hT₂ x hx ⟨hlogH, hxT⟩
      exact ⟨U, Finset.mem_union_right _ hU, hxU⟩

/-! ### All solutions -/

open scoped Classical in
/-- **The quantitative Subspace Theorem for a system** (Q0.3). Under the normalization (2.4), with
forms over a Galois extension `E / K`, all solutions lie in at most

`δ⁻¹ ((10³ n) ^ (n [K : ℚ]) + 4 n log log (4 H)) + 1 + log ω / log (1 + δ / (2 n))`
`+ systemLargeCount`

proper subspaces of `Kⁿ`: the solutions that are not large by Layer 9.3, the large ones below
`X₀ = systemThreshold` by one interval of Layer 9.4 with ratio `ω = systemMiddleRatio`, and the
rest by `NumberField.exists_finset_submodule_of_systemThreshold_le`. Only `ω` depends on the
coefficient height `H` beyond `log log (4 H)`, through `log X₀`; `X₀` is linear in `log H`
(`NumberField.systemThreshold_le`). -/
theorem exists_finset_submodule_of_isNormalizedSystem [IsGalois K E]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    ∃ T : Finset (Submodule K (ι → K)),
      (#T : ℝ) ≤ δ⁻¹ * ((10 ^ 3 * Fintype.card ι) ^ (Fintype.card ι * finrank ℚ K) +
          4 * Fintype.card ι * Real.log (Real.log (4 * H))) +
        (1 + Real.log (systemMiddleRatio (finrank ℚ K) (Fintype.card ι) H δ
            (systemThreshold E S w L H δ)) / Real.log (1 + δ / (2 * Fintype.card ι))) +
        systemLargeCount (Fintype.card ι) (finrank ℚ E) (finrank K E)
          (Fintype.card (InfinitePlace K) + #S) #S δ ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∀ x ∈ systemSet S w L C c, ∃ U ∈ T, x ∈ U := by
  set n := Fintype.card ι with hn
  have hn2 : 2 ≤ n := hN.two_le_card
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hδ := hN.delta_pos
  set d := finrank ℚ K with hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (finrank_pos : 0 < finrank ℚ K)
  set X₀ := systemThreshold E S w L H δ with hX₀
  set QL := max (2 * H) ((n : ℝ) ^ (2 * n / δ)) with hQL
  have hQL1 : 1 < QL := (Real.one_lt_rpow (by exact_mod_cast (by omega : 1 < n))
    (by positivity)).trans_le (le_max_right _ _)
  have hlQL : 0 < Real.log QL := Real.log_pos hQL1
  set ω := systemMiddleRatio d n H δ X₀ with hω
  have hω1 : 1 ≤ ω := le_max_left _ _
  obtain ⟨T₁, hT₁card, hT₁top, hT₁⟩ := exists_finset_submodule_of_not_isLargeSolution S w hwInf
    hwFin hN
  obtain ⟨T₂, hT₂card, hT₂top, hT₂⟩ := exists_finset_submodule_of_forall_mem_interval_of_mem S w
    hwInf hwFin hN {x | IsLargeSolution H δ x ∧ Real.log (mulHeightAff x) < X₀}
    (m := 1) (fun _ ↦ QL) (fun _ ↦ le_max_right _ _) hω1 (fun x _ hxX ↦ by
      obtain ⟨hlarge, hlog⟩ := hxX
      have hH := mulHeightAff_pos x
      refine ⟨0, hlarge, ?_⟩
      rw [Real.rpow_def_of_pos hH, Real.rpow_def_of_pos (by linarith)]
      refine Real.exp_lt_exp.2 ?_
      have h1 : X₀ ≤ ω * (d * Real.log QL) := by
        rw [← div_le_iff₀ (by positivity)]; exact le_max_right _ _
      rw [← div_eq_mul_inv, div_lt_iff₀ hd0]
      nlinarith)
  obtain ⟨T₃, hT₃card, hT₃top, hT₃⟩ := exists_finset_submodule_of_systemThreshold_le S w hwInf
    hwFin hN
  refine ⟨T₁ ∪ T₂ ∪ T₃, ?_, fun U hU ↦ ?_, fun x hx ↦ ?_⟩
  · calc (#(T₁ ∪ T₂ ∪ T₃) : ℝ) ≤ #T₁ + #T₂ + #T₃ := by
          exact_mod_cast (Finset.card_union_le _ _).trans
            (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      _ ≤ _ := by
          refine add_le_add (add_le_add hT₁card (hT₂card.trans_eq ?_)) hT₃card
          rw [Nat.cast_one, one_mul]
  · rcases Finset.mem_union.1 hU with hU | hU
    · rcases Finset.mem_union.1 hU with hU | hU
      · exact hT₁top U hU
      · exact hT₂top U hU
    · exact hT₃top U hU
  · by_cases hlarge : IsLargeSolution H δ x
    · by_cases hlog : Real.log (mulHeightAff x) < X₀
      · obtain ⟨U, hU, hxU⟩ := hT₂ x hx ⟨hlarge, hlog⟩
        exact ⟨U, Finset.mem_union_left _ (Finset.mem_union_right _ hU), hxU⟩
      · obtain ⟨U, hU, hxU⟩ := hT₃ x hx (not_lt.1 hlog)
        exact ⟨U, Finset.mem_union_right _ hU, hxU⟩
    · obtain ⟨U, hU, hxU⟩ := hT₁ x hx hlarge
      exact ⟨U, Finset.mem_union_left _ (Finset.mem_union_left _ hU), hxU⟩

/-! ### The threshold in terms of heights -/

open scoped Classical in
/-- **The threshold is linear in the height of the coefficients** (Q0.2e with the heights of the
conjugated forms bounded by Galois invariance): `systemThreshold` is at most the largest of
`parametricCoeff · ((r_E + s_E) n² [E : ℚ] log H + log |D_E| + ∑ log N(V) + 1)`, the sum over
the places `V` of `E` above `S`, of `[K : ℚ] (2 n / δ) log n` and of `systemHeightThreshold`.
Besides `log H` it sees only the fields and `S`. -/
theorem systemThreshold_le [IsGalois K E] {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w : AbsoluteValue K ℝ → AbsoluteValue E ℝ}
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    systemThreshold E S w L H δ ≤
      max (parametricCoeff (finrank ℚ E) (Fintype.card ι) (Fintype.card (InfinitePlace E))
          #(systemPlacesOver E S) (systemEps (finrank K E) δ)
          (systemAbsBound (finrank K E) (Fintype.card ι) (Fintype.card (InfinitePlace K) + #S)) *
          ((Fintype.card (InfinitePlace E) + #(systemPlacesOver E S)) * Fintype.card ι ^ 2 *
              (finrank ℚ E * Real.log H) + Real.log |(discr E : ℝ)| +
            ∑ V ∈ systemPlacesOver E S, Real.log (Ideal.absNorm V.maximalIdeal.asIdeal : ℝ) + 1))
        (max (finrank ℚ K * (2 * Fintype.card ι / δ) * Real.log (Fintype.card ι))
          (systemHeightThreshold (Fintype.card ι) (finrank ℚ E)
            (Fintype.card (InfinitePlace K) + #S) δ H)) := by
  have hn2 := hN.two_le_card
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hδ := hN.delta_pos
  have he0 : (0 : ℝ) < finrank K E := by exact_mod_cast (finrank_pos : 0 < finrank K E)
  have hε : 0 < systemEps (finrank K E) δ := by rw [systemEps]; positivity
  have hA : 0 ≤ systemAbsBound (finrank K E) (Fintype.card ι)
      (Fintype.card (InfinitePlace K) + #S) := by rw [systemAbsBound]; positivity
  refine max_le_max ?_ le_rfl
  refine (parametricThreshold_le (linearIndependent_conjSystem_infinitePlace hwInf
    fun v ↦ hN.linearIndependent (.inl v))
    (fun V hV ↦ linearIndependent_conjSystem_systemPlacesOver hwFin
      (fun p hp ↦ hN.linearIndependent (.inr ⟨p, hp⟩)) hV) hε hA).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (parametricCoeff_nonneg _ _ _ _ (by omega) hε hA)
  rw [thresholdScale]
  gcongr
  exact hN.formLogHeight_conjSystem_le hwInf hwFin

end NumberField
