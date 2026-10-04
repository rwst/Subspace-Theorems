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
  subspaces, a number depending on `n`, `δ`, `[E : ℚ]`, `[E : K]` and the number `R` of distinct
  forms alone, not on `t` or `|S|`;
* all solutions lie in at most that number, plus Layer 9.3's count for the solutions that are not
  large, plus `1 + log ω / log (1 + δ / (2 n))` for the large ones below `X₀`, where
  `ω = max (1, X₀ / ([K : ℚ] log Q))` and `Q` is the height from which a solution is large;
* `X₀` is linear in `log H`, with coefficients depending on `n`, `δ`, the fields and `S`
  (`systemThreshold_le`). It does not depend on the constants `C p`.

Everything is stated for a generalized Roth lemma `R` (`NumberField.SubspaceRoth`), which Layer
5.6 uses; the threshold and `systemLargeCount` see it through its parameters. Bombieri–Gubler's
(`NumberField.SubspaceRoth.bombieriGubler`) gives Q0.3; Evertse's gives Q1.6
(`QuantitativeSubspace/SubspaceCount.lean`).

The route, for a solution `x` above `X₀`:

1. **Raised exponents** (`IsNormalizedSystem.exists_raise`). The positive exponents sum to at
   most `n`, since `max_i c p i = s(p)`; scaling the negative ones down leaves weight `-δ` and
   absolute weight at most `2 n + δ`, for any number `t` of places (ES02 uses only
   `∑_v max_i c_{iv} ≤ 1` in the same way).
2. **One scalar for the constants** (`exists_ne_zero_systemAbs_le`, Minkowski's first theorem on
   `K¹`). There is a nonzero `S`-integer `β` with `|β|_p ^ mult p ≤ κ / C p` at every place, where
   `κ ^ t = scalarConst K S · (n! H^{n d}) ^ (2 t / n)` bounds `scalarConst K S · ∏ C p` by (2.4)
   and `systemDet ≤ (n! H^{n d}) ^ (2 t)` (`IsNormalizedSystem.systemDet_le`). Above the
   threshold `κ ≤ H(x) ^ (δ / (2 n t))`, so `β x` meets the raised exponents shifted by
   `δ / (2 n t)`: weight `-δ / 2`, absolute weight at most `2 n + 2`.
3. **Bridge** (Q0.2c): `β x`, read in `Eⁿ`, lies in the approximation domain over `E` of the
   conjugated forms and these exponents at level `H(x)`. **Layer 6.1 as an interval result**
   (Q0.2d) over `E`, once: either the domain lies in one of the exceptional subspaces, whose
   `K`-points form a proper subspace of `Kⁿ` (`comap_algebraMapPi_ne_top`) and contain `x` with
   `β x`, or `log H(x)` lies in one of the intervals `[t, ρ t)`.
4. **Layer 9.4** turns each interval `[exp (t / [K : ℚ]), exp (t / [K : ℚ]) ^ ρ)` of the absolute
   affine height into `1 + log ρ / log (1 + δ / (2 n))` windows of the gap principle.

The counts of Layer 6.1 over `E` do not depend on the number of infinite places of `E`
(Q1.8c: the minima sit at one place), and are taken at `R [E : K]` distinct forms: the forms
at a place of `E` are `Gal(E / K)`-conjugates of the forms at the place of `K` below it
(`formCount_conjSystem_le`). The heights
of the conjugated forms are those of the coefficients (`logHeight₁_algEquiv`,
`IsNormalizedSystem.formLogHeight_conjSystem_le`).

## Main results

* `NumberField.exists_finset_submodule_of_forall_interval`: steps 1–4 for **any** interval
  result above `X₀` for the conjugated forms, with counts `NS`, `NI` and ratio `ρ`. Layer 6.1 is
  one; for `n = 2` Layer 5.6 is one (`QuantitativeSubspace/SubspaceCountTwo.lean`).
* `NumberField.exists_finset_submodule_of_systemThreshold_le`: the large solutions above `X₀`,
  with Layer 6.1's interval result.
* `NumberField.exists_finset_submodule_of_isNormalizedSystem_of_large`: all solutions, from any
  count of the large ones above any `X₀`.
* `NumberField.exists_finset_submodule_of_isNormalizedSystem`: all solutions.
* `NumberField.systemThreshold_le`: `X₀` in terms of `log H`, `|D_E|` and the norms of the
  primes of `E` above `S`.
* `NumberField.IsNormalizedSystem.exists_raise`: the raised exponents.
* `NumberField.exists_ne_zero_systemAbs_le`: Minkowski's first theorem for one scalar.
* `NumberField.IsNormalizedSystem.linearIndependent`: the forms of a normalized system are
  independent at every place of the system.
* `NumberField.formCount_conjSystem_le`: at most `R [E : K]` distinct conjugated forms over `E`.

## Implementation notes

⚠ **The forms are over a Galois extension `E / K`.** The bridge of Q0.2c needs it, to read the
places of `E` as conjugates. A system over an intermediate field is the same system over its
Galois closure (`NumberField.systemSet_compRingHom`), so this costs nothing but the degree.

⚠ **One scalar replaces the constants.** Absorbing each `C p` into its own exponent would put
`max (0, log C p)` into the threshold, and (2.4) bounds only the product of the `C p`. Scaling the
solutions by one `β` uses only the product, and costs `log scalarConst K S` (`[K : ℚ] log 2`,
`∑ log N(q)` and `½ log |D_K|`) in the threshold, nothing in the count. Q0.3 took the exponents
from each solution instead, which multiplied the count by `(2 n t ⌈4 n t / δ⌉ + …) ^ (t n)` grid
systems and put `A ≍ t² n²` into Layer 6.1 (Q1.8a removed both).

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

universe u

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
variable {ι : Type u} [Fintype ι]

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

/-- The ratio of every step of Layer 6.1 is at least `4`. -/
theorem four_le_parametricStepRatio (R : RothParams) {N : ℕ} (d s p : ℕ) {ε A : ℝ} (hN : 0 < N)
    (hε : 0 < ε) (hA : 0 ≤ A) : 4 ≤ parametricStepRatio R N d s p ε A := by
  have hδ := parametricDelta_pos hN hε
  have hW := parametricWedgeAbsWeight_nonneg N d p hε.le hA
  have h0 := R.ratio_pos (n := N.choose p - 1) (s := s ^ p) hδ hW
  have h1 := R.ratio_le_one (n := N.choose p - 1) (s := s ^ p) hδ hW
  have h2 : 1 ≤ (R.ratio (N.choose p - 1) (s ^ p) (parametricDelta N ε)
      (parametricWedgeAbsWeight N d p ε A))⁻¹ := (one_le_inv₀ h0).2 h1
  rw [parametricStepRatio]
  linarith

/-- **The ratio of the parametric Subspace Theorem is at least `1`.** -/
theorem one_le_parametricRatio (R : RothParams) {N : ℕ} (d s : ℕ) {ε A : ℝ} (hN : 0 < N)
    (hε : 0 < ε) (hA : 0 ≤ A) : 1 ≤ parametricRatio R N d s ε A := by
  rw [parametricRatio]
  calc (1 : ℝ) ≤ parametricStepRatio R N d s 0 ε A := by
        linarith [four_le_parametricStepRatio R d s 0 hN hε hA]
    _ ≤ ∑ p ∈ Finset.range N, parametricStepRatio R N d s p ε A :=
        Finset.single_le_sum (f := fun p ↦ parametricStepRatio R N d s p ε A)
          (fun p _ ↦ (parametricStepRatio_pos R d s p hN hε hA).le) (Finset.mem_range.2 hN)

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

open scoped Classical in
/-- **At most `R [E : K]` distinct forms over `E`**, for `R` distinct forms of the system: the
forms at a place of `E` are conjugates of those at the place of `K` below it. -/
theorem formCount_conjSystem_le [IsGalois K E] {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w : AbsoluteValue K ℝ → AbsoluteValue E ℝ}
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {R : ℕ}
    (hR : (Set.range fun q : (InfinitePlace K ⊕ S) × ι ↦ L (systemPlace S q.1) q.2).ncard ≤ R) :
    formCount (systemPlacesOver E S) (conjSystem univ (S.image FinitePlace.mk) w L)
      ≤ R * finrank K E := by
  set F := Set.range fun q : (InfinitePlace K ⊕ S) × ι ↦ L (systemPlace S q.1) q.2 with hF
  have hwF : ∀ v ∈ S.image FinitePlace.mk, (w v.1).LiesOver v.1 := fun v hv ↦ by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    exact hwFin q hq
  have hsub : (Set.range fun q : (InfinitePlace E ⊕ ↥(systemPlacesOver E S)) × ι ↦
      conjSystem univ (S.image FinitePlace.mk) w L (sPlace (systemPlacesOver E S) q.1) q.2)
      ⊆ Set.range fun p : ↥F × (E ≃ₐ[K] E) ↦
        (p.1 : Dual E (ι → E)).compRingHom (p.2 : E →+* E) := by
    rintro _ ⟨⟨a | a, i⟩, rfl⟩
    · obtain ⟨σ, -, hσ⟩ := exists_conjSystem_inf (L := L) (Sfin := S.image FinitePlace.mk)
        (fun v _ ↦ hwInf v) (mem_univ _) (InfinitePlace.liesOver_comap (K := K) a)
      exact ⟨(⟨_, (.inl (a.comap (algebraMap K E)), i), rfl⟩, σ), by
        simp only [sPlace, Sum.elim_inl, hσ, systemPlace]⟩
    · obtain ⟨p, hp, hVp⟩ := mem_systemPlacesOver.mp a.2
      obtain ⟨σ, -, hσ⟩ := exists_conjSystem_fin (L := L) (Sinf := univ) hwF
        (Finset.mem_image_of_mem _ hp) hVp
      exact ⟨(⟨_, (.inr ⟨p, hp⟩, i), rfl⟩, σ), by
        simp only [sPlace, Sum.elim_inr, hσ, systemPlace]⟩
  rw [formCount]
  refine (Set.ncard_le_ncard hsub (Set.finite_range _)).trans ?_
  rw [← Set.image_univ]
  refine (Set.ncard_image_le Set.finite_univ).trans ?_
  rw [Set.ncard_univ, Nat.card_prod, Nat.card_coe_set_eq, IsGalois.card_aut_eq_finrank]
  exact Nat.mul_le_mul_right _ hR

/-- A normalized system has at least one form, so its bound `R` on the number of distinct forms is
at least `1`. -/
theorem IsNormalizedSystem.one_le_formBound {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w : AbsoluteValue K ℝ → AbsoluteValue E ℝ} {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)}
    {C : InfinitePlace K ⊕ S → ℝ} {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) : 1 ≤ R := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by have := hN.two_le_card; omega)
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  refine le_trans ?_ hN.ncard_le
  rw [Nat.one_le_iff_ne_zero, ne_eq, Set.ncard_eq_zero (Set.finite_range _)]
  exact (Set.range_nonempty _).ne_empty

theorem parametricChainLength_mono {N d s s' p : ℕ} {ε A : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (hA : 0 ≤ A) (hs : 1 ≤ s) (hss : s ≤ s') :
    parametricChainLength N d s p ε A ≤ parametricChainLength N d s' p ε A :=
  subspaceChainLength_mono (parametricDelta_pos hN hε)
    (parametricWedgeAbsWeight_nonneg N d p hε.le hA) (Nat.one_le_pow _ _ hs)
    (Nat.pow_le_pow_left hss p)

theorem parametricStepRatio_mono (R : RothParams) {N d s s' p : ℕ} {ε A : ℝ} (hN : 0 < N)
    (hε : 0 < ε) (hA : 0 ≤ A) (hs : 1 ≤ s) (hss : s ≤ s') :
    parametricStepRatio R N d s p ε A ≤ parametricStepRatio R N d s' p ε A := by
  have hδ := parametricDelta_pos hN hε
  have hW := parametricWedgeAbsWeight_nonneg N d p hε.le hA
  rw [parametricStepRatio, parametricStepRatio]
  exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ (R.ratio_pos hδ hW)
    (R.ratio_pos hδ hW)).2 (R.ratio_anti hδ hW (Nat.one_le_pow _ _ hs)
      (Nat.pow_le_pow_left hss p))) four_pos.le

theorem parametricRatio_mono (R : RothParams) {N d s s' : ℕ} {ε A : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (hA : 0 ≤ A) (hs : 1 ≤ s) (hss : s ≤ s') :
    parametricRatio R N d s ε A ≤ parametricRatio R N d s' ε A :=
  Finset.sum_le_sum fun _ _ ↦ parametricStepRatio_mono R hN hε hA hs hss

theorem one_le_parametricGridBase (N d p : ℕ) {ε A : ℝ} (hε : 0 ≤ ε) (hA : 0 ≤ A) :
    1 ≤ (2 * parametricBox N d p ε A + 1).toNat := by
  have hm0 : 0 ≤ parametricBox N d p ε A := by
    refine Int.ceil_nonneg (div_nonneg ?_ (parametricMesh_nonneg N d p hε))
    rw [parametricMinimaExp]
    positivity
  omega

theorem parametricIntervalCount_mono {N d s s' : ℕ} {ε A : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (hA : 0 ≤ A) (hs : 1 ≤ s) (hss : s ≤ s') :
    parametricIntervalCount N d s ε A ≤ parametricIntervalCount N d s' ε A :=
  Finset.sum_le_sum fun _ _ ↦ Nat.mul_le_mul_left _ (parametricChainLength_mono hN hε hA hs hss)

/-! ### The parameters -/

/-- **The weight margin over `E`**, `ε = [E : K] δ / 4`. -/
noncomputable def systemEps (e : ℕ) (δ : ℝ) : ℝ :=
  e * δ / 4

/-- **The bound on the absolute weight over `E`**, `A = [E : K] (2 n + 2)`: the raised exponents
have absolute weight at most `2 n + δ`, and the shift that absorbs the scalar adds `δ / 2`. -/
noncomputable def systemAbsBound (e n : ℕ) : ℝ :=
  e * (2 * n + 2)

variable (K) in
/-- **Minkowski's constant for one scalar**, `2 ^ [K : ℚ] ∏_{q ∈ S} N(q) √|D_K|`: if the product
of the bounds `B p` at the places of a system is at least this, some nonzero `S`-integer `β` has
`|β|_p ≤ B p` at all of them (`NumberField.exists_ne_zero_systemAbs_le`). -/
noncomputable def scalarConst (S : Finset (HeightOneSpectrum (𝓞 K))) : ℝ :=
  2 ^ finrank ℚ K * (∏ q ∈ S, (Ideal.absNorm q.asIdeal : ℝ)) * √|(discr K : ℝ)|

/-- **The part of the threshold that comes from the system itself**, in the coefficient height
`H` and `μ = log scalarConst`: `(2 n μ + 4 t log (n! H ^ (n d))) / δ`, above which the scalar
that absorbs the constants costs at most `H(x) ^ (δ / (2 n t))` at every place. Here
`d = [E : ℚ]` and `t` is the number of places. -/
noncomputable def systemHeightThreshold (n d t : ℕ) (δ H μ : ℝ) : ℝ :=
  (2 * n * μ + 4 * t * (Real.log n.factorial + n * (d * Real.log H))) / δ

variable (E) in
open scoped Classical in
/-- **The threshold of the quantitative Subspace Theorem for a system**, on the scale of
`log H(x)`: the largest of the threshold of Layer 6.1 for the conjugated forms over `E`, of
`[K : ℚ] (2 n / δ) log n` (so that the gap principle applies), and of `systemHeightThreshold`.
It does not depend on the constants `C`. -/
noncomputable def systemThreshold (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ) (L : AbsoluteValue K ℝ → ι → Dual E (ι → E))
    (R : RothParams) (r : ℕ) (H δ : ℝ) : ℝ :=
  max (parametricThreshold (systemPlacesOver E S) (conjSystem univ (S.image FinitePlace.mk) w L) R
      (r * finrank K E) (systemEps (finrank K E) δ)
      (systemAbsBound (finrank K E) (Fintype.card ι)))
    (max (finrank ℚ K * (2 * Fintype.card ι / δ) * Real.log (Fintype.card ι))
      (systemHeightThreshold (Fintype.card ι) (finrank ℚ E) (Fintype.card (InfinitePlace K) + #S)
        δ H (Real.log (scalarConst K S))))

/-- **The number of subspaces of the large solutions**: Layer 6.1's exceptional subspaces over
`E` and, for each of its intervals, the windows of the gap principle. The parameters are `n`
variables, `d = [E : ℚ]`, `e = [E : K]` and `r` distinct forms; Layer 6.1's counts are taken at
`r e` distinct forms, which bound the conjugated forms over `E`
(`NumberField.formCount_conjSystem_le`). -/
noncomputable def systemLargeCount (R : RothParams) (n d e r : ℕ) (δ : ℝ) : ℝ :=
  parametricSubspaceCount n d (r * e) (systemEps e δ) (systemAbsBound e n) +
    parametricIntervalCount n d (r * e) (systemEps e δ) (systemAbsBound e n) *
      (1 + Real.log (parametricRatio R n d (r * e) (systemEps e δ) (systemAbsBound e n)) /
        Real.log (1 + δ / (2 * n)))

/-- **The ratio of the middle interval**: the large solutions below the threshold `X` have
absolute affine height in `[Q, Q ^ ω)` with `Q = max (2 H) (n ^ (2 n / δ))` and
`ω = max (1, X / ([K : ℚ] log Q))`. -/
noncomputable def systemMiddleRatio (d n : ℕ) (H δ X : ℝ) : ℝ :=
  max 1 (X / (d * Real.log (max (2 * H) ((n : ℝ) ^ (2 * n / δ)))))

/-! ### One scalar for the constants -/

private theorem systemPlace_inj (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (systemPlace S) := by
  rintro (v | v) (v' | v') h <;> simp only [systemPlace] at h
  · exact congrArg Sum.inl (Subtype.ext h)
  · exact absurd h (InfinitePlace.val_ne_finitePlace_val v (FinitePlace.mk v'.1))
  · exact absurd h.symm (InfinitePlace.val_ne_finitePlace_val v' (FinitePlace.mk v.1))
  · exact congrArg Sum.inr (Subtype.ext (FinitePlace.mk_injective (Subtype.ext h)))

theorem scalarConst_pos (S : Finset (HeightOneSpectrum (𝓞 K))) : 0 < scalarConst K S := by
  have hN : ∀ q ∈ S, (0 : ℝ) < Ideal.absNorm q.asIdeal := fun q _ ↦ by
    have := (FinitePlace.mk q).one_lt_absNorm
    rw [FinitePlace.maximalIdeal_mk] at this
    linarith
  have hD : 0 < √|(discr K : ℝ)| :=
    Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero K))
  rw [scalarConst]
  exact mul_pos (mul_pos (by positivity) (Finset.prod_pos hN)) hD

/-- **Minkowski's first theorem for one scalar.** If the product of positive bounds `B p` over
the places of a system is at least `scalarConst K S`, some nonzero `S`-integer `β` has
`|β|_p ^ mult p ≤ B p` at every place of the system. This is the domain of Layer 4.1 for the
coordinate form on `K¹`: its first minimum is at most `1`. -/
theorem exists_ne_zero_systemAbs_le (S : Finset (HeightOneSpectrum (𝓞 K)))
    {B : InfinitePlace K ⊕ S → ℝ} (hB : ∀ p, 0 < B p) (h : scalarConst K S ≤ ∏ p, B p) :
    ∃ β : K, β ≠ 0 ∧ β ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K ∧
      ∀ p, systemPlace S p β ^ systemMult S p ≤ B p := by
  classical
  set Sfin := S.image FinitePlace.mk with hSfin
  set L₀ : AbsoluteValue K ℝ → Unit → Dual K (Unit → K) := fun _ _ ↦ LinearMap.proj ()
    with hL₀
  set c : AbsoluteValue K ℝ → Unit → ℝ := fun a _ ↦
    Function.extend (systemPlace S) (fun p ↦ Real.log (B p) / systemMult S p) 0 a with hc
  have hc' : ∀ p i, c (systemPlace S p) i = Real.log (B p) / systemMult S p := fun p i ↦
    (systemPlace_inj S).extend_apply _ _ _
  set Q := Real.exp 1 with hQ
  have hQ0 : 0 < Q := Real.exp_pos 1
  have hLI : ∀ a, LinearIndependent K (L₀ a) := fun a ↦ linearIndependent_unique_iff.2 fun h0 ↦ by
    have := LinearMap.congr_fun h0 fun _ ↦ 1
    simp [hL₀] at this
  have hw : approxWeight Sfin c = ∑ p, Real.log (B p) := by
    rw [approxWeight, Fintype.sum_sum_type, hSfin,
      Finset.sum_image fun _ _ _ _ h ↦ FinitePlace.mk_injective h]
    congr 1
    · refine Finset.sum_congr rfl fun v _ ↦ ?_
      have := hc' (.inl v) ()
      simp only [systemPlace, systemMult] at this
      simp only [Finset.univ_unique, Finset.sum_singleton, PUnit.default_eq_unit, this]
      field_simp [v.mult_pos.ne']
    · rw [← Finset.sum_coe_sort S]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      have := hc' (.inr q) ()
      simp only [systemPlace, systemMult, Nat.cast_one, div_one] at this
      simp [this]
  have hpow : ∀ p (a : ℝ), 0 ≤ a → a ≤ Q ^ c (systemPlace S p) () →
      a ^ systemMult S p ≤ B p := fun p a ha hle ↦ by
    have hm : (0 : ℝ) < systemMult S p := by
      exact_mod_cast Nat.pos_of_ne_zero (systemMult_ne_zero S p)
    rw [hc' p (), hQ, Real.exp_one_rpow] at hle
    calc a ^ systemMult S p ≤ Real.exp (Real.log (B p) / systemMult S p) ^ systemMult S p :=
          pow_le_pow_left₀ ha hle _
      _ = B p := by
          rw [← Real.exp_nat_mul, mul_div_cancel₀ _ hm.ne', Real.exp_log (hB p)]
  have hprod := prod_successiveMinimum_approx_le (Sfin := Sfin) (L := L₀) (fun w ↦ hLI w.1)
    (fun v _ ↦ hLI v.1) c hQ0
  simp only [Fintype.card_unit, Finset.range_one, Finset.prod_singleton, mul_one, pow_one]
    at hprod
  rw [approxConst_proj, hw] at hprod
  have hN : ∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) =
      ∏ q ∈ S, (Ideal.absNorm q.asIdeal : ℝ) := by
    rw [hSfin, Finset.prod_image fun _ _ _ _ h ↦ FinitePlace.mk_injective h]
    simp only [FinitePlace.maximalIdeal_mk]
  have hQB : Q ^ (-∑ p, Real.log (B p)) = (∏ p, B p)⁻¹ := by
    rw [hQ, Real.exp_one_rpow, Real.exp_neg, Real.exp_sum]
    simp only [Real.exp_log (hB _)]
  rw [hN, hQB] at hprod
  have hBpos : 0 < ∏ p, B p := Finset.prod_pos fun p _ ↦ hB p
  have hcov := covolume_le_sqrt (K := K)
  have hcov0 := ZLattice.covolume_pos (mixedEmbedding.integerLattice K)
  have hpi : (1 : ℝ) ≤
      2 ^ InfinitePlace.nrRealPlaces K * Real.pi ^ InfinitePlace.nrComplexPlaces K :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two)
      (one_le_pow₀ (by linarith [Real.pi_gt_three]))
  have hP0 : 0 ≤ ∏ q ∈ S, (Ideal.absNorm q.asIdeal : ℝ) :=
    Finset.prod_nonneg fun _ _ ↦ by positivity
  have hRHS : 2 ^ finrank ℚ K * (∏ q ∈ S, (Ideal.absNorm q.asIdeal : ℝ)) /
      (2 ^ InfinitePlace.nrRealPlaces K * Real.pi ^ InfinitePlace.nrComplexPlaces K /
        ZLattice.covolume (mixedEmbedding.integerLattice K)) * (∏ p, B p)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hBpos, div_div_eq_mul_div]
    refine (div_le_of_le_mul₀ (by positivity) (scalarConst_pos S).le ?_).trans h
    rw [scalarConst]
    calc 2 ^ finrank ℚ K * (∏ q ∈ S, (Ideal.absNorm q.asIdeal : ℝ)) *
          ZLattice.covolume (mixedEmbedding.integerLattice K)
        ≤ 2 ^ finrank ℚ K * (∏ q ∈ S, (Ideal.absNorm q.asIdeal : ℝ)) * √|(discr K : ℝ)| :=
          mul_le_mul_of_nonneg_left hcov (by positivity)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hpi
  have hμ0 := successiveMinimum_nonneg (approxModule Sfin L₀ c Q) (approxBody L₀ c Q) 0
  have hμ : successiveMinimum (approxModule Sfin L₀ c Q) (approxBody L₀ c Q) 0 ≤ 1 :=
    (pow_le_one_iff_of_nonneg hμ0 (finrank_pos (R := ℚ) (M := K)).ne').1 (hprod.trans hRHS)
  rw [successiveMinimum_approx_le_one_iff (fun w ↦ hLI w.1) (fun v _ ↦ hLI v.1) c hQ0
    (by simp)] at hμ
  obtain ⟨y, hy, hy0⟩ : ∃ y ∈ approxDomain Sfin L₀ c Q, y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : approxSpan Sfin L₀ c Q = ⊥ := Submodule.span_eq_bot.2 hcon
    rw [h0, finrank_bot] at hμ
    exact lt_irrefl _ hμ
  refine ⟨y (), fun h0 ↦ hy0 (funext fun _ ↦ h0), ?_, fun p ↦ ?_⟩
  · refine (Set.mem_integer_iff_finitePlace _ _).2 fun q hq ↦ hy.2.2 (FinitePlace.mk q)
      (fun hm ↦ hq ?_) ()
    obtain ⟨q', hq', heq⟩ := Finset.mem_image.1 hm
    exact FinitePlace.mk_injective heq ▸ hq'
  · rcases p with v | q
    · exact hpow (.inl v) _ (apply_nonneg _ _) (hy.1 v ())
    · exact hpow (.inr q) _ (apply_nonneg _ _)
        (hy.2.1 (FinitePlace.mk q.1) (Finset.mem_image_of_mem _ q.2) ())

omit [Fintype ι] in
/-- **Scaling a point scales its local values** by `|β|_p ^ mult p`. -/
theorem systemValue_mul (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    (L : AbsoluteValue K ℝ → ι → Dual E (ι → E)) (p : InfinitePlace K ⊕ S) (i : ι) (β : K)
    (x : ι → K) :
    systemValue S w L p i (fun j ↦ β * x j) =
      systemPlace S p β ^ systemMult S p * systemValue S w L p i x := by
  have hlies : (w (systemPlace S p)).LiesOver (systemPlace S p) := by
    rcases p with v | v
    · exact hwInf v
    · exact hwFin v.1 v.2
  have hv : (fun j ↦ algebraMap K E (β * x j)) =
      algebraMap K E β • fun j ↦ algebraMap K E (x j) := by
    funext j; simp [map_mul]
  simp only [systemValue, systemAbs]
  rw [hv, map_smul, smul_eq_mul, map_mul,
    AbsoluteValue.apply_algebraMap_of_liesOver (v := systemPlace S p), mul_pow]

/-! ### The raised exponents -/

/-- **The exponents can be raised to absolute weight at most `2 n + δ`.** The positive exponents
sum to at most `n`, since each is at most the normalized local degree; scaling the negative ones
by `λ = (P + δ) / N ≤ 1`, `P` and `N` the sums of the positive and negative parts, leaves the
weight at exactly `-δ`, and no exponent above the normalized local degree. Raising the exponents
only enlarges the set of solutions. -/
theorem IsNormalizedSystem.exists_raise {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w : AbsoluteValue K ℝ → AbsoluteValue E ℝ} {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)}
    {C : InfinitePlace K ⊕ S → ℝ} {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    ∃ c' : InfinitePlace K ⊕ S → ι → ℝ, (∀ p i, c p i ≤ c' p i) ∧ systemWeight c' = -δ ∧
      ∑ p, ∑ i, |c' p i| ≤ 2 * Fintype.card ι + δ ∧ ∀ p i, c' p i ≤ systemExponent S p := by
  have hδ := hN.delta_pos
  set P := ∑ p, ∑ i, max (c p i) 0 with hP
  set M := ∑ p, ∑ i, max (-c p i) 0 with hM
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun p _ ↦ Finset.sum_nonneg fun i _ ↦ le_max_right _ _
  have hs : ∀ p, 0 ≤ systemExponent S p := fun p ↦ by
    rcases p with v | v <;> simp only [systemExponent] <;> positivity
  have hPn : P ≤ Fintype.card ι := by
    calc P ≤ ∑ p, ∑ _i : ι, systemExponent S p :=
          Finset.sum_le_sum fun p _ ↦ Finset.sum_le_sum fun i _ ↦
            max_le (hN.exponent_le p i) (hs p)
      _ = Fintype.card ι := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
            sum_systemExponent, mul_one]
  have hsplit : systemWeight c = P - M := by
    rw [systemWeight, hP, hM, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rcases le_total 0 (c p i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hPM : P + δ ≤ M := by linarith [hN.weight_le]
  have hM0 : 0 < M := by linarith
  set l := (P + δ) / M with hl
  have hl0 : 0 ≤ l := by positivity
  have hl1 : l ≤ 1 := (div_le_one hM0).2 hPM
  have hlM : l * M = P + δ := div_mul_cancel₀ _ hM0.ne'
  refine ⟨fun p i ↦ max (c p i) 0 - l * max (-c p i) 0, fun p i ↦ ?_, ?_, ?_, fun p i ↦ ?_⟩
  · change c p i ≤ max (c p i) 0 - l * max (-c p i) 0
    rcases le_total 0 (c p i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; simp
    · rw [max_eq_right h, max_eq_left (by linarith)]; nlinarith
  · have : systemWeight (fun p i ↦ max (c p i) 0 - l * max (-c p i) 0) = P - l * M := by
      simp only [systemWeight, Finset.sum_sub_distrib, ← Finset.mul_sum, hP, hM]
    rw [this, hlM]
    linarith
  · calc ∑ p, ∑ i, |max (c p i) 0 - l * max (-c p i) 0|
        ≤ ∑ p, ∑ i, (max (c p i) 0 + l * max (-c p i) 0) :=
          Finset.sum_le_sum fun p _ ↦ Finset.sum_le_sum fun i _ ↦ by
            refine (abs_sub _ _).trans_eq ?_
            rw [abs_of_nonneg (le_max_right _ _),
              abs_of_nonneg (mul_nonneg hl0 (le_max_right _ _))]
      _ = P + l * M := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hP, hM]
      _ ≤ 2 * Fintype.card ι + δ := by rw [hlM]; linarith
  · have h0 : 0 ≤ l * max (-c p i) 0 := mul_nonneg hl0 (le_max_right _ _)
    have h1 : max (c p i) 0 ≤ systemExponent S p := max_le (hN.exponent_le p i) (hs p)
    change max (c p i) 0 - l * max (-c p i) 0 ≤ _
    linarith

/-! ### The large solutions -/

open scoped Classical in
/-- **The large solutions of a system, from any interval result** (the assembly of Q0.3). Under
the normalization (2.4), with forms over a Galois extension `E / K`, suppose that every system of
exponents over `E` of weight at most `-systemEps [E : K] δ` and absolute weight at most
`systemAbsBound [E : K] n` (and, which the interval result may also use, of weight exactly
`-[E : K] δ / 2` and largest exponents of weight `approxSupWeight ≤ [E : K] (1 + δ / 2n)`) has an
interval result above `X₀` for the conjugated forms: its
domains at levels `log Q ≥ X₀` lie in one of at most `NS` proper subspaces of `Eⁿ`, or `log Q`
lies in one of at most `NI` intervals `[s, ρ s)` with `s ≥ X₀`. If `X₀` is at least
`systemHeightThreshold` and `[K : ℚ] (2 n / δ) log n`, the solutions with `log H(x) ≥ X₀` lie in
at most `NS + NI (1 + log ρ / log (1 + δ / (2 n)))` proper subspaces of `Kⁿ`.

The interval result is used **once**: the exponents are raised to absolute weight at most
`2 n + δ` (`IsNormalizedSystem.exists_raise`), and the constants are absorbed by one nonzero
`S`-integer `β` with `|β|_p ^ mult p ≤ κ / C p` (`exists_ne_zero_systemAbs_le`), `κ` depending on
`H`, `K` and `S` only; `β x` lies in the domain at level `H(x)` of the raised exponents shifted by
`δ / (2 n t)`, and `x` lies in every subspace that `β x` lies in. Layer 6.1 supplies such an
interval result for every `n` (`NumberField.exists_finset_submodule_of_systemThreshold_le`); for
`n = 2` Layer 5.6 does. -/
theorem exists_finset_submodule_of_forall_interval [IsGalois K E]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) {X₀ ρ : ℝ} {NS NI : ℕ}
    (hX₀H : systemHeightThreshold (Fintype.card ι) (finrank ℚ E)
      (Fintype.card (InfinitePlace K) + #S) δ H (Real.log (scalarConst K S)) ≤ X₀)
    (hX₀n : finrank ℚ K * (2 * Fintype.card ι / δ) * Real.log (Fintype.card ι) ≤ X₀)
    (hρ1 : 1 ≤ ρ)
    (hint : ∀ c' : AbsoluteValue E ℝ → ι → ℝ,
      approxWeight (systemPlacesOver E S) c' ≤ -systemEps (finrank K E) δ →
      approxAbsWeight (systemPlacesOver E S) c' ≤ systemAbsBound (finrank K E) (Fintype.card ι) →
      approxWeight (systemPlacesOver E S) c' = -(finrank K E * δ / 2) →
      approxSupWeight (systemPlacesOver E S) c' ≤
        finrank K E * (1 + δ / (2 * Fintype.card ι)) →
      ∃ T : Finset (Submodule E (ι → E)), #T ≤ NS ∧ (∀ W ∈ T, W ≠ ⊤) ∧
        ∃ 𝒯 : Finset ℝ, #𝒯 ≤ NI ∧ (∀ s ∈ 𝒯, X₀ ≤ s) ∧
          ∀ Q : ℝ, 1 < Q → X₀ ≤ Real.log Q →
            (∃ W ∈ T, approxDomain (systemPlacesOver E S)
              (conjSystem univ (S.image FinitePlace.mk) w L) c' Q ⊆ W) ∨
              ∃ s ∈ 𝒯, s ≤ Real.log Q ∧ Real.log Q < ρ * s) :
    ∃ T : Finset (Submodule K (ι → K)),
      (#T : ℝ) ≤ NS + NI * (1 + Real.log ρ / Real.log (1 + δ / (2 * Fintype.card ι))) ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x ∈ systemSet S w L C c, X₀ ≤ Real.log (mulHeightAff x) → ∃ U ∈ T, x ∈ U := by
  set n := Fintype.card ι with hn
  have hn2 : 2 ≤ n := hN.two_le_card
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hδ := hN.delta_pos
  have hδ1 := hN.delta_le_one
  have hH1 := hN.one_le_height
  set e := finrank K E with he
  set t := Fintype.card (InfinitePlace K) + #S with ht
  have hcardS : Fintype.card (InfinitePlace K ⊕ S) = t := by
    rw [Fintype.card_sum, Fintype.card_coe]
  have ht0 : (0 : ℝ) < t := by
    have := Fintype.card_pos (α := InfinitePlace K)
    exact_mod_cast (by omega : 0 < t)
  have he0 : (0 : ℝ) < e := by exact_mod_cast (finrank_pos : 0 < finrank K E)
  set Sfin' := systemPlacesOver E S with hSfin'
  set L' := conjSystem univ (S.image FinitePlace.mk) w L with hL'
  have hX₀pos : 0 < X₀ := by
    have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hK : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
    exact (by positivity : (0 : ℝ) < finrank ℚ K * (2 * n / δ) * Real.log n).trans_le hX₀n
  -- the raised exponents
  obtain ⟨c', hcc', hc'w, hc'A, hc's⟩ := hN.exists_raise
  -- the scalar
  set Z : ℝ := (n.factorial : ℝ) * (H ^ finrank ℚ E) ^ n with hZ
  have hZ1 : 1 ≤ Z := one_le_mul_of_one_le_of_one_le
    (Nat.one_le_cast.2 (Nat.factorial_pos _)) (one_le_pow₀ (one_le_pow₀ hH1))
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ1
  have hlogZ : Real.log Z = Real.log n.factorial + n * (finrank ℚ E * Real.log H) := by
    rw [hZ, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  set μ := Real.log (scalarConst K S) with hμ
  set a : ℝ := (μ + 2 * t / n * Real.log Z) / t with ha
  set κ := Real.exp a with hκ
  have hC0 := hN.const_pos
  have hprodC : ∏ p, C p ≤ Z ^ (2 * (t : ℝ) / n) := by
    have h1 := hN.const_le
    rw [systemConst] at h1
    refine h1.trans ?_
    calc systemDet S w L ^ ((n : ℝ)⁻¹) ≤ (Z ^ (2 * t)) ^ ((n : ℝ)⁻¹) :=
          Real.rpow_le_rpow (systemDet_pos hN).le (hN.systemDet_le hwInf hwFin) (by positivity)
      _ = Z ^ (2 * (t : ℝ) / n) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]
          push_cast
          ring_nf
  have hκt : κ ^ t = scalarConst K S * Z ^ (2 * (t : ℝ) / n) := by
    rw [hκ, ← Real.exp_nat_mul, ha, mul_div_cancel₀ _ ht0.ne', Real.exp_add, hμ,
      Real.exp_log (scalarConst_pos S), Real.rpow_def_of_pos hZ0]
    ring_nf
  have hB : ∀ p, 0 < κ / C p := fun p ↦ div_pos (Real.exp_pos _) (hC0 p)
  have hBprod : scalarConst K S ≤ ∏ p, κ / C p := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, hcardS, hκt,
      le_div_iff₀ (Finset.prod_pos fun p _ ↦ hC0 p)]
    exact mul_le_mul_of_nonneg_left hprodC (scalarConst_pos S).le
  obtain ⟨β, hβ0, hβint, hβ⟩ := exists_ne_zero_systemAbs_le S hB hBprod
  -- the exponents of the domain
  set γ : ℝ := δ / (2 * n * t) with hγ
  have hγ0 : 0 ≤ γ := by positivity
  have htnγ : (t : ℝ) * n * γ = δ / 2 := by rw [hγ]; field_simp
  set e' : InfinitePlace K ⊕ S → ι → ℝ := fun p i ↦ c' p i + γ with he'
  have hw' : approxWeight Sfin' (conjExponent S e') ≤ -systemEps e δ := by
    rw [approxWeight_conjExponent, systemEps]
    have : systemWeight e' = systemWeight c' + t * n * γ := by
      simp only [he', systemWeight, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        hcardS, nsmul_eq_mul]
      ring
    rw [this, htnγ]
    nlinarith
  have hA' : approxAbsWeight Sfin' (conjExponent S e') ≤ systemAbsBound e n := by
    rw [approxAbsWeight_conjExponent, systemAbsBound]
    refine mul_le_mul_of_nonneg_left ?_ he0.le
    calc ∑ p, ∑ i, |e' p i| ≤ ∑ p, ∑ i, (|c' p i| + γ) :=
          Finset.sum_le_sum fun p _ ↦ Finset.sum_le_sum fun i _ ↦ by
            refine (abs_add_le _ _).trans_eq ?_
            rw [abs_of_nonneg hγ0]
      _ = ∑ p, ∑ i, |c' p i| + t * n * γ := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcardS,
            nsmul_eq_mul]
          ring
      _ ≤ 2 * n + 2 := by rw [htnγ]; linarith
  have hwe : approxWeight Sfin' (conjExponent S e') = -(e * δ / 2) := by
    rw [approxWeight_conjExponent]
    have : systemWeight e' = systemWeight c' + t * n * γ := by
      simp only [he', systemWeight, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        hcardS, nsmul_eq_mul]
      ring
    rw [this, htnγ, hc'w]
    ring
  have hsup : approxSupWeight Sfin' (conjExponent S e') ≤ e * (1 + δ / (2 * n)) := by
    rw [approxSupWeight_conjExponent]
    refine mul_le_mul_of_nonneg_left ?_ he0.le
    calc ∑ p, ⨆ i, e' p i ≤ ∑ p, (systemExponent S p + γ) :=
          Finset.sum_le_sum fun p _ ↦ ciSup_le fun i ↦ by
            simp only [he']
            linarith [hc's p i]
      _ = 1 + δ / (2 * n) := by
          rw [Finset.sum_add_distrib, sum_systemExponent, Finset.sum_const, Finset.card_univ,
            hcardS, nsmul_eq_mul, hγ]
          field_simp
  obtain ⟨T, hTcard, hTtop, 𝒯, h𝒯card, h𝒯ge, hQint⟩ := hint _ hw' hA' hwe hsup
  set T₁ := T.image fun W ↦ (W.restrictScalars K).comap (algebraMapPi K E ι) with hT₁
  -- `β x` lies in the domain
  have hdom : ∀ x ∈ systemSet S w L C c, X₀ ≤ Real.log (mulHeightAff x) →
      (fun j ↦ algebraMap K E (β * x j)) ∈ approxDomain Sfin' L' (conjExponent S e')
        (mulHeightAff x) := fun x hx hlogH ↦ by
    have hHx0 := mulHeightAff_pos x
    have hlH : 0 < Real.log (mulHeightAff x) := hX₀pos.trans_le hlogH
    have hHx1 : 1 ≤ mulHeightAff x := ((Real.log_pos_iff hHx0.le).1 hlH).le
    have hκx : κ ≤ mulHeightAff x ^ γ := by
      rw [hκ, Real.rpow_def_of_pos hHx0, Real.exp_le_exp]
      have h1 := hX₀H.trans hlogH
      rw [systemHeightThreshold, ← hlogZ, div_le_iff₀ hδ] at h1
      rw [ha, hγ, div_le_iff₀ ht0]
      have : Real.log (mulHeightAff x) * (δ / (2 * n * t)) * t =
          Real.log (mulHeightAff x) * δ / (2 * n) := by field_simp
      rw [this, le_div_iff₀ (by positivity)]
      have : (μ + 2 * t / n * Real.log Z) * (2 * n) = 2 * n * μ + 4 * t * Real.log Z := by
        field_simp
        ring
      rw [this]
      linarith
    refine mem_approxDomain_conjSystem hwInf hwFin L hHx0.le
      (fun j ↦ mul_mem hβint (hx.1 j)) fun p i ↦ ?_
    rw [systemValue_mul S w hwInf hwFin]
    calc systemPlace S p β ^ systemMult S p * systemValue S w L p i x
        ≤ κ / C p * (C p * mulHeightAff x ^ c p i) :=
          mul_le_mul (hβ p) (hx.2 p i) (systemValue_nonneg ..) (hB p).le
      _ = κ * mulHeightAff x ^ c p i := by field_simp [(hC0 p).ne']
      _ ≤ mulHeightAff x ^ γ * mulHeightAff x ^ c' p i :=
          mul_le_mul hκx (Real.rpow_le_rpow_of_exponent_le hHx1 (hcc' p i))
            (Real.rpow_nonneg hHx0.le _) (Real.rpow_nonneg hHx0.le _)
      _ = mulHeightAff x ^ e' p i := by rw [he', Real.rpow_add hHx0, mul_comm]
  -- the intervals, as intervals of the absolute affine height
  set d := finrank ℚ K with hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (finrank_pos : 0 < finrank ℚ K)
  set Q : Fin #𝒯 → ℝ := fun i ↦ Real.exp ((𝒯.equivFin.symm i : ℝ) / d) with hQ
  have hQn : ∀ i, (n : ℝ) ^ (2 * n / δ) ≤ Q i := fun i ↦ by
    rw [Real.rpow_def_of_pos hn0]
    refine Real.exp_le_exp.2 ((le_div_iff₀ hd0).2 ?_)
    have := h𝒯ge _ (𝒯.equivFin.symm i).2
    nlinarith
  obtain ⟨T₂, hT₂card, hT₂top, hT₂⟩ := exists_finset_submodule_of_forall_mem_interval_of_mem S w
    hwInf hwFin hN {x | X₀ ≤ Real.log (mulHeightAff x) ∧ ∀ U ∈ T₁, x ∉ U} Q hQn hρ1
    (fun x hx hxX ↦ by
      have hH := mulHeightAff_pos x
      obtain ⟨hlogH, hxT⟩ := hxX
      have hy := hdom x hx hlogH
      have hH1 : 1 < mulHeightAff x := by
        rw [← Real.log_pos_iff hH.le]
        linarith
      rcases hQint (mulHeightAff x) hH1 hlogH with ⟨W, hW, hsub⟩ | ⟨s, hs, h1, h2⟩
      · refine absurd (hsub hy) fun hyW ↦ hxT _ (Finset.mem_image_of_mem _ hW) ?_
        have hβE : algebraMap K E β ≠ 0 := (map_ne_zero _).2 hβ0
        have hxW : (fun j ↦ algebraMap K E (x j)) ∈ W := by
          have h := W.smul_mem (algebraMap K E β)⁻¹ hyW
          convert h using 1
          funext j
          simp [map_mul, inv_mul_cancel_left₀ hβE]
        exact hxW
      · refine ⟨𝒯.equivFin ⟨s, hs⟩, ?_, ?_⟩
        · simp only [hQ, Equiv.symm_apply_apply]
          rw [Real.rpow_def_of_pos hH]
          refine Real.exp_le_exp.2 ?_
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hd0.le)
        · simp only [hQ, Equiv.symm_apply_apply]
          rw [Real.rpow_def_of_pos hH, ← Real.exp_mul]
          refine Real.exp_lt_exp.2 ?_
          rw [div_mul_eq_mul_div, mul_comm (s : ℝ) ρ, div_eq_mul_inv]
          exact mul_lt_mul_of_pos_right h2 (inv_pos.2 hd0))
  refine ⟨T₁ ∪ T₂, ?_, fun U hU ↦ ?_, fun x hx hlogH ↦ ?_⟩
  · have hl : 0 < Real.log (1 + δ / (2 * n)) := Real.log_pos (by
      have : 0 < δ / (2 * n) := by positivity
      linarith)
    have hfac : 0 ≤ 1 + Real.log ρ / Real.log (1 + δ / (2 * n)) :=
      add_nonneg zero_le_one (div_nonneg (Real.log_nonneg hρ1) hl.le)
    calc (#(T₁ ∪ T₂) : ℝ) ≤ #T + #T₂ := by
          exact_mod_cast (Finset.card_union_le _ _).trans
            (Nat.add_le_add_right Finset.card_image_le _)
      _ ≤ NS + (NI : ℕ) * (1 + Real.log ρ / Real.log (1 + δ / (2 * n))) := by
          refine add_le_add (by exact_mod_cast hTcard) (hT₂card.trans ?_)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast h𝒯card) hfac
  · rcases Finset.mem_union.1 hU with hU | hU
    · obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hU
      exact comap_algebraMapPi_ne_top (hTtop W hW)
    · exact hT₂top U hU
  · by_cases hxT : ∃ U ∈ T₁, x ∈ U
    · obtain ⟨U, hU, hxU⟩ := hxT
      exact ⟨U, Finset.mem_union_left _ hU, hxU⟩
    · push Not at hxT
      obtain ⟨U, hU, hxU⟩ := hT₂ x hx ⟨hlogH, hxT⟩
      exact ⟨U, Finset.mem_union_right _ hU, hxU⟩

open scoped Classical in
/-- **The quantitative Subspace Theorem for the large solutions of a system** (Q0.3). Under the
normalization (2.4), with forms over a Galois extension `E / K`, the solutions `x` with
`log H(x) ≥ systemThreshold` lie in at most `systemLargeCount` proper subspaces of `Kⁿ`, a
number that depends on `n`, `δ`, `[E : ℚ]`, `[E : K]` and the number `R` of distinct forms only.
It is `NumberField.exists_finset_submodule_of_forall_interval` with Layer 6.1's interval result,
whose counts over `E` are bounded by those at `[E : ℚ]` infinite places and `R [E : K]` forms. -/
theorem exists_finset_submodule_of_systemThreshold_le [IsGalois K E] (RL : SubspaceRoth.{u} E)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    ∃ T : Finset (Submodule K (ι → K)),
      (#T : ℝ) ≤ systemLargeCount RL.toRothParams (Fintype.card ι) (finrank ℚ E) (finrank K E)
        R δ ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x ∈ systemSet S w L C c,
        systemThreshold E S w L RL.toRothParams R H δ ≤ Real.log (mulHeightAff x) →
        ∃ U ∈ T, x ∈ U := by
  set n := Fintype.card ι with hn
  have hn2 : 2 ≤ n := hN.two_le_card
  have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have hδ := hN.delta_pos
  set e := finrank K E with he
  set dE := finrank ℚ E with hdE
  have he0 : (0 : ℝ) < e := by exact_mod_cast (finrank_pos : 0 < finrank K E)
  set Sfin' := systemPlacesOver E S with hSfin'
  set L' := conjSystem univ (S.image FinitePlace.mk) w L with hL'
  set ε := systemEps e δ with hε
  set A := systemAbsBound e n with hA
  have hε0 : 0 < ε := by rw [hε, systemEps]; positivity
  have hA0 : 0 ≤ A := by rw [hA, systemAbsBound]; positivity
  have hsE : formCount Sfin' L' ≤ R * e := formCount_conjSystem_le hwInf hwFin hN.ncard_le
  have hLI : ∀ v : InfinitePlace K, LinearIndependent E (L v.1) := fun v ↦
    hN.linearIndependent (.inl v)
  have hLF : ∀ p ∈ S, LinearIndependent E (L (FinitePlace.mk p).1) := fun p hp ↦
    hN.linearIndependent (.inr ⟨p, hp⟩)
  set X₀ := systemThreshold E S w L RL.toRothParams R H δ with hX₀
  have hX₀P : parametricThreshold Sfin' L' RL.toRothParams (R * e) ε A ≤ X₀ := le_max_left _ _
  set ρ := parametricRatio RL.toRothParams n dE (R * e) ε A with hρ
  obtain ⟨T, hTcard, hTtop, hT⟩ := exists_finset_submodule_of_forall_interval S w hwInf hwFin hN
    (X₀ := X₀) (ρ := ρ)
    (NS := parametricSubspaceCount n dE (R * e) ε A)
    (NI := parametricIntervalCount n dE (R * e) ε A)
    ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))
    (one_le_parametricRatio RL.toRothParams _ _ (by omega) hε0 hA0) fun c' hcw hcA _ _ ↦ by
      obtain ⟨T, hTcard, hTtop, Q₀, -, hQ₀eq, hint⟩ :=
        exists_forall_mem_interval_approxDomain (K := E) (Sfin := Sfin') (L := L') RL
          (linearIndependent_conjSystem_infinitePlace hwInf hLI)
          (fun V hV ↦ linearIndependent_conjSystem_systemPlacesOver hwFin hLF hV) hε0 hcw hcA hsE
      obtain ⟨𝒯, h𝒯card, h𝒯ge, hQint⟩ := hint X₀ (hQ₀eq ▸ hX₀P)
      exact ⟨T, hTcard, hTtop, 𝒯, h𝒯card, h𝒯ge, hQint⟩
  exact ⟨T, hTcard.trans_eq (by rw [systemLargeCount]), hTtop, hT⟩

/-! ### All solutions -/

open scoped Classical in
/-- **All solutions of a system, from a count of the large ones above `X₀`** (the last step of
Q0.3). Under the normalization (2.4), with forms over a Galois extension `E / K`, if the solutions
with `log H(x) ≥ X₀` lie in at most `NL` proper subspaces, then all solutions lie in at most

`δ⁻¹ ((10³ n) ^ (n [K : ℚ]) + 4 n log log (4 H)) + 1 + log ω / log (1 + δ / (2 n)) + NL`

proper subspaces of `Kⁿ`, with `ω = systemMiddleRatio [K : ℚ] n H δ X₀`: the solutions that are
not large by Layer 9.3 and the large ones below `X₀` by one interval of Layer 9.4. -/
theorem exists_finset_submodule_of_isNormalizedSystem_of_large [IsGalois K E]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) {X₀ NL : ℝ}
    (hlarge : ∃ T : Finset (Submodule K (ι → K)), (#T : ℝ) ≤ NL ∧ (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x ∈ systemSet S w L C c, X₀ ≤ Real.log (mulHeightAff x) → ∃ U ∈ T, x ∈ U) :
    ∃ T : Finset (Submodule K (ι → K)),
      (#T : ℝ) ≤ δ⁻¹ * ((10 ^ 3 * Fintype.card ι) ^ (Fintype.card ι * finrank ℚ K) +
          4 * Fintype.card ι * Real.log (Real.log (4 * H))) +
        (1 + Real.log (systemMiddleRatio (finrank ℚ K) (Fintype.card ι) H δ X₀) /
              Real.log (1 + δ / (2 * Fintype.card ι))) + NL ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∀ x ∈ systemSet S w L C c, ∃ U ∈ T, x ∈ U := by
  set n := Fintype.card ι with hn
  have hn2 : 2 ≤ n := hN.two_le_card
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hδ := hN.delta_pos
  set d := finrank ℚ K with hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (finrank_pos : 0 < finrank ℚ K)
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
  obtain ⟨T₃, hT₃card, hT₃top, hT₃⟩ := hlarge
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
theorem exists_finset_submodule_of_isNormalizedSystem [IsGalois K E] (RL : SubspaceRoth.{u} E)
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
            (systemThreshold E S w L RL.toRothParams R H δ)) /
              Real.log (1 + δ / (2 * Fintype.card ι))) +
        systemLargeCount RL.toRothParams (Fintype.card ι) (finrank ℚ E) (finrank K E) R δ ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∀ x ∈ systemSet S w L C c, ∃ U ∈ T, x ∈ U :=
  exists_finset_submodule_of_isNormalizedSystem_of_large S w hwInf hwFin hN
    (exists_finset_submodule_of_systemThreshold_le RL S w hwInf hwFin hN)

/-! ### The threshold in terms of heights -/

open scoped Classical in
/-- **The threshold is linear in the height of the coefficients** (Q0.2e with the heights of the
conjugated forms bounded by Galois invariance): `systemThreshold` is at most the largest of
`parametricCoeff · ((r_E + s_E) n² [E : ℚ] log H + log |D_E| + ∑ log N(V) + 1)`, the sum over
the places `V` of `E` above `S`, of `[K : ℚ] (2 n / δ) log n` and of `systemHeightThreshold`.
Besides `log H` it sees only the fields and `S`. -/
theorem systemThreshold_le [IsGalois K E] (RL : RothParams) {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w : AbsoluteValue K ℝ → AbsoluteValue E ℝ}
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    systemThreshold E S w L RL R H δ ≤
      max (parametricCoeff RL (finrank ℚ E) (Fintype.card ι) (Fintype.card (InfinitePlace E))
          #(systemPlacesOver E S) (R * finrank K E) (systemEps (finrank K E) δ)
          (systemAbsBound (finrank K E) (Fintype.card ι)) *
          ((Fintype.card (InfinitePlace E) + #(systemPlacesOver E S)) * Fintype.card ι ^ 2 *
              (finrank ℚ E * Real.log H) + Real.log |(discr E : ℝ)| +
            ∑ V ∈ systemPlacesOver E S, Real.log (Ideal.absNorm V.maximalIdeal.asIdeal : ℝ) + 1))
        (max (finrank ℚ K * (2 * Fintype.card ι / δ) * Real.log (Fintype.card ι))
          (systemHeightThreshold (Fintype.card ι) (finrank ℚ E)
            (Fintype.card (InfinitePlace K) + #S) δ H (Real.log (scalarConst K S)))) := by
  have hn2 := hN.two_le_card
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hδ := hN.delta_pos
  have he0 : (0 : ℝ) < finrank K E := by exact_mod_cast (finrank_pos : 0 < finrank K E)
  have hε : 0 < systemEps (finrank K E) δ := by rw [systemEps]; positivity
  have hA : 0 ≤ systemAbsBound (finrank K E) (Fintype.card ι) := by
    rw [systemAbsBound]; positivity
  refine max_le_max ?_ le_rfl
  refine (parametricThreshold_le RL (linearIndependent_conjSystem_infinitePlace hwInf
    fun v ↦ hN.linearIndependent (.inl v))
    (fun V hV ↦ linearIndependent_conjSystem_systemPlacesOver hwFin
      (fun p hp ↦ hN.linearIndependent (.inr ⟨p, hp⟩)) hV) (R * finrank K E) hε hA).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (parametricCoeff_nonneg RL _ _ _ _ _ (by omega) hε hA)
  rw [thresholdScale]
  gcongr
  exact hN.formLogHeight_conjSystem_le hwInf hwFin

end NumberField
