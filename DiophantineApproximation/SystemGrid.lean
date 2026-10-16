/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.PlaceProd
public import DiophantineApproximation.SubspaceSystem

-- Used only inside proofs.
import DiophantineApproximation.SubspaceGap

/-!
# A product inequality as finitely many normalized systems

The quantitative Subspace Theorem of Q4.3 counts the solutions of one **normalized system**
(`NumberField.IsNormalizedSystem`): `|L_i(x)|_p ≤ C p · H(x) ^ c p i` at every place `p` of
`S∞ ∪ S`, with `c p i ≤ s(p)`, `max_i c p i = s(p)` and weight `∑ c p i ≤ −δ`. The applications
(Schlickewei's §3, Evertse–Schlickewei's product form) have a **product inequality** instead. This
file turns it into one of finitely many such systems, with the constants unchanged, the number of
systems depending only on `n` and the number of places. It is the hard direction of the
equivalence whose easy direction is `NumberField.affineProd_le_of_mem_systemSet`. Unlike 9.1's
`NumberField.exists_finset_forall_exists_mem_systemSet`, the systems are **normalized**
(`max_i c p i = s(p)`), the constants are the caller's, there is no existential level, and the
number of systems is explicit. (Layer 6.1's `NumberField.gridExponent`, for approximation
domains, is a different grid.)

The hypotheses are on one point `x`, measured by its affine height `H = H(x) > 1`: every form is
at most `C p · H ^ s(p)`, and

```text
∏_p ∏_i |L_i(x)|_p · H ^ (n + 2 δ) ≤ (∏_p max_i |L_i(x)|_p) ^ n.
```

The exponent of `|L_i(x)|_p` relative to the largest form at `p`,
`f p i = log_H (M_p / |L_i(x)|_p)`, is `≥ 0`, vanishes at a largest form, and sums to at least
`n + 2 δ`. Rounding `N f p i` down and capping it at `(n + 1) N` gives `k p i`, and the
exponents `c p i = s(p) − k p i / N` (`NumberField.systemGridExponent`) are a system that `x`
solves.
With `N δ` at least the number of pairs `(p, i)`, the rounding loses at most `δ`, so the weight
is at most `−δ`. There are at most
`((n + 1) N + 1) ^ (t n)` grids, `t` the number of places.

⚠ **The lower bound on the largest form is the caller's.** It is what makes `max_i c p i = s(p)`
cost nothing: the deficit of the largest form at `p` from `C p · H ^ s(p)` is charged to the
right-hand side of the product inequality. A caller gets it from `|x|_p ≤ n · max_i |L_i(x)|_p`
and a balanced representative (`NumberField.exists_smul_balanced`).

## Main results

* `NumberField.systemGridExponent`: the exponents of a grid point.
* `NumberField.exists_mem_systemSet_systemGridExponent`: **the product inequality gives a system**.
* `NumberField.systemWeight_systemGridExponent_le`, `NumberField.systemGridExponent_le`,
  `NumberField.exists_systemGridExponent_eq`: the normalization (2.4) of the exponents.
* `NumberField.placeProd_iSup_le_mul_prod_iSup_systemValue`: the lower bound on the largest forms
  from `|x|_p ≤ c · max_i |L_i(x)|_p`.
* `NumberField.exists_le_rpow_prod_grid`: a factorization of `b` into factors `≤ 1`, rounded on a
  grid of mesh `1 / N` (the subclasses of Schlickewei's gap principle).

## References

J.-H. Evertse, *On the Quantitative Subspace Theorem*, Zap. Nauchn. Sem. POMI **377** (2010),
217–240, §2; H. P. Schlickewei, *`S`-unit equations over number fields*, Invent. Math. **102**
(1990), 95–107, Lemma 4.1 (a simplex net doing the same job).

This is part of Layer 9.1 of the `DiophantineApproximation` roadmap (added with S90.3).
-/

@[expose] public section

open Height IsDedekindDomain Module

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι]

/-- **The exponents of a grid point** `k`: `s(p) − k p i / N`. -/
noncomputable def systemGridExponent (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) {M : ℕ}
    (k : InfinitePlace K ⊕ S → ι → Fin M) : InfinitePlace K ⊕ S → ι → ℝ :=
  fun p i ↦ systemExponent S p - ((k p i : ℕ) : ℝ) / N

omit [Fintype ι] in
/-- No exponent of a grid point exceeds the normalized local degree. -/
theorem systemGridExponent_le (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) {M : ℕ}
    (k : InfinitePlace K ⊕ S → ι → Fin M) (p : InfinitePlace K ⊕ S) (i : ι) :
    systemGridExponent S N k p i ≤ systemExponent S p :=
  sub_le_self _ (by positivity)

omit [Fintype ι] in
/-- A zero of the grid attains the normalized local degree. -/
theorem exists_systemGridExponent_eq (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) {M : ℕ}
    {k : InfinitePlace K ⊕ S → ι → Fin M} (hk : ∀ p, ∃ i, (k p i : ℕ) = 0)
    (p : InfinitePlace K ⊕ S) : ∃ i, systemGridExponent S N k p i = systemExponent S p := by
  obtain ⟨i, hi⟩ := hk p
  exact ⟨i, by simp [systemGridExponent, hi]⟩

/-- **The weight of a grid point** is `n − ∑ k p i / N`. -/
theorem systemWeight_systemGridExponent (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) {M : ℕ}
    (k : InfinitePlace K ⊕ S → ι → Fin M) :
    systemWeight (systemGridExponent S N k) =
      Fintype.card ι - ∑ p, ∑ i, ((k p i : ℕ) : ℝ) / N := by
  simp only [systemWeight, systemGridExponent, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, sum_systemExponent, mul_one]

/-- The weight of a grid point is at most `−δ` once `∑ k p i / N ≥ n + δ`. -/
theorem systemWeight_systemGridExponent_le (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) {M : ℕ}
    {k : InfinitePlace K ⊕ S → ι → Fin M} {δ : ℝ}
    (hk : Fintype.card ι + δ ≤ ∑ p, ∑ i, ((k p i : ℕ) : ℝ) / N) :
    systemWeight (systemGridExponent S N k) ≤ -δ := by
  rw [systemWeight_systemGridExponent]
  linarith

omit [NumberField F] in
/-- **A product inequality gives one of finitely many normalized systems.** Let `x` be
`S`-integral with affine height `H > 1`, every form at most `C p · H ^ s(p)` and nonzero, and

```text
∏_p ∏_i |L_i(x)|_p · H ^ (n + 2 δ) ≤ (∏_p max_i |L_i(x)|_p) ^ n.
```

If `N δ` is at least the number of pairs `(p, i)`, then `x` solves the system with the constants
`C` and the exponents `s(p) − k p i / N` of a grid point `k` with entries at most `(n + 1) N`,
some entry `0` at every place, and `∑ k p i / N ≥ n + δ`. -/
theorem exists_mem_systemSet_systemGridExponent [Nonempty ι] {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ} {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)}
    {C : InfinitePlace K ⊕ S → ℝ} {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : δ ≤ 1)
    (hq : (Fintype.card (InfinitePlace K ⊕ S) * Fintype.card ι : ℝ) ≤ N * δ) {x : ι → K}
    (hxS : ∀ j, x j ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) (hH : 1 < mulHeightAff x)
    (hpos : ∀ p i, 0 < systemValue S w L p i x)
    (hle : ∀ p i, systemValue S w L p i x ≤ C p * mulHeightAff x ^ systemExponent S p)
    (hprod : (∏ p, ∏ i, systemValue S w L p i x) *
        mulHeightAff x ^ ((Fintype.card ι : ℝ) + 2 * δ) ≤
      (∏ p, ⨆ i, systemValue S w L p i x) ^ Fintype.card ι) :
    ∃ k : InfinitePlace K ⊕ S → ι → Fin ((Fintype.card ι + 1) * N + 1),
      (∀ p, ∃ i, (k p i : ℕ) = 0) ∧
      (Fintype.card ι : ℝ) + δ ≤ ∑ p, ∑ i, ((k p i : ℕ) : ℝ) / N ∧
      x ∈ systemSet S w L C (systemGridExponent S N k) := by
  set n := Fintype.card ι with hn
  set H := mulHeightAff x with hHdef
  set V : InfinitePlace K ⊕ S → ι → ℝ := fun p i ↦ systemValue S w L p i x with hV
  set Mx : InfinitePlace K ⊕ S → ℝ := fun p ↦ ⨆ i, V p i with hMx
  have hH0 : 0 < H := zero_lt_one.trans hH
  have hℓ : 0 < Real.log H := Real.log_pos hH
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hVM : ∀ p i, V p i ≤ Mx p := fun p i ↦ le_ciSup (Finite.bddAbove_range (V p)) i
  have hMpos : ∀ p, 0 < Mx p := fun p ↦ (hpos p (Classical.arbitrary ι)).trans_le (hVM _ _)
  set f : InfinitePlace K ⊕ S → ι → ℝ := fun p i ↦ Real.log (Mx p / V p i) / Real.log H with hf
  have hf0 : ∀ p i, 0 ≤ f p i := fun p i ↦ div_nonneg
    (Real.log_nonneg ((one_le_div (hpos p i)).2 (hVM p i))) hℓ.le
  have hHf : ∀ p i, H ^ f p i = Mx p / V p i := fun p i ↦ by
    rw [Real.rpow_def_of_pos hH0, hf, mul_div_cancel₀ _ hℓ.ne',
      Real.exp_log (div_pos (hMpos p) (hpos p i))]
  set kk : InfinitePlace K ⊕ S → ι → ℕ := fun p i ↦ min ⌊N * f p i⌋₊ ((n + 1) * N) with hkk
  have hkf : ∀ p i, ((kk p i : ℕ) : ℝ) / N ≤ f p i := fun p i ↦ by
    rw [div_le_iff₀ hN0, mul_comm]
    exact (Nat.cast_le.2 (min_le_left _ _)).trans
      (Nat.floor_le (mul_nonneg hN0.le (hf0 p i)))
  refine ⟨fun p i ↦ ⟨kk p i, Nat.lt_succ_of_le (min_le_right _ _)⟩, fun p ↦ ?_, ?_, hxS,
    fun p i ↦ ?_⟩
  · -- a largest form has `f = 0`
    obtain ⟨i, hi⟩ := Finite.exists_max (V p)
    have hMi : Mx p = V p i := le_antisymm (ciSup_le hi) (hVM p i)
    refine ⟨i, ?_⟩
    simp [hkk, hf, hMi]
  · -- the sum of the grid
    have hsumf : (n : ℝ) + 2 * δ ≤ ∑ p, ∑ i, f p i := by
      have hprod0 : 0 < ∏ p, ∏ i, V p i :=
        Finset.prod_pos fun p _ ↦ Finset.prod_pos fun i _ ↦ hpos p i
      have hlog := Real.log_le_log (mul_pos hprod0 (Real.rpow_pos_of_pos hH0 _)) hprod
      rw [Real.log_mul hprod0.ne' (Real.rpow_pos_of_pos hH0 _).ne', Real.log_rpow hH0,
        Real.log_pow, Real.log_prod (fun p _ ↦ (hMpos p).ne'),
        Real.log_prod (fun p _ ↦ (Finset.prod_pos fun i _ ↦ hpos p i).ne')] at hlog
      simp only [Real.log_prod (fun i _ ↦ (hpos _ i).ne')] at hlog
      have hsum : (∑ p, ∑ i, f p i) * Real.log H =
          n * ∑ p, Real.log (Mx p) - ∑ p, ∑ i, Real.log (V p i) := by
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [Finset.sum_mul]
        have h : ∀ i, f p i * Real.log H = Real.log (Mx p) - Real.log (V p i) := fun i ↦ by
          rw [hf, div_mul_cancel₀ _ hℓ.ne', Real.log_div (hMpos p).ne' (hpos p i).ne']
        simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn]
      refine le_of_mul_le_mul_right ?_ hℓ
      linarith
    by_cases hcap : ∃ p i, (n + 1) * N ≤ ⌊N * f p i⌋₊
    · obtain ⟨p, i, hpi⟩ := hcap
      have hk : ((kk p i : ℕ) : ℝ) / N = n + 1 := by
        simp only [hkk, min_eq_right hpi]
        rw [Nat.cast_mul, mul_div_cancel_right₀ _ hN0.ne']
        push_cast
        ring
      have hnonneg : ∀ p i, (0 : ℝ) ≤ ((kk p i : ℕ) : ℝ) / N := fun _ _ ↦ by positivity
      calc (n : ℝ) + δ ≤ n + 1 := by linarith
        _ = ((kk p i : ℕ) : ℝ) / N := hk.symm
        _ ≤ ∑ i, ((kk p i : ℕ) : ℝ) / N :=
          Finset.single_le_sum (fun i _ ↦ hnonneg p i) (Finset.mem_univ i)
        _ ≤ ∑ p, ∑ i, ((kk p i : ℕ) : ℝ) / N :=
          Finset.single_le_sum (f := fun p ↦ ∑ i, ((kk p i : ℕ) : ℝ) / N)
            (fun p _ ↦ Finset.sum_nonneg fun i _ ↦ hnonneg p i) (Finset.mem_univ p)
    · push Not at hcap
      have hlow : ∀ p i, f p i - 1 / N ≤ ((kk p i : ℕ) : ℝ) / N := fun p i ↦ by
        simp only [hkk, min_eq_left (hcap p i).le]
        rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hN0]
        have := Nat.lt_floor_add_one (N * f p i)
        linarith
      have hq' : ∑ _p : InfinitePlace K ⊕ S, ∑ _i : ι, (1 : ℝ) / N ≤ δ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
        rw [mul_one_div, div_le_iff₀ hN0, mul_comm δ]
        exact hq
      calc (n : ℝ) + δ ≤ ∑ p, ∑ i, f p i - ∑ _p : InfinitePlace K ⊕ S, ∑ _i : ι, (1 : ℝ) / N := by
            linarith
        _ = ∑ p, ∑ i, (f p i - 1 / N) := by simp only [Finset.sum_sub_distrib]
        _ ≤ ∑ p, ∑ i, ((kk p i : ℕ) : ℝ) / N :=
          Finset.sum_le_sum fun p _ ↦ Finset.sum_le_sum fun i _ ↦ hlow p i
  · -- the point solves the system
    change V p i ≤ C p * H ^ (systemExponent S p - ((kk p i : ℕ) : ℝ) / N)
    have hpow : H ^ (((kk p i : ℕ) : ℝ) / N) ≤ Mx p / V p i :=
      (hHf p i) ▸ Real.rpow_le_rpow_of_exponent_le hH.le (hkf p i)
    have hpow0 : 0 < H ^ (((kk p i : ℕ) : ℝ) / N) := Real.rpow_pos_of_pos hH0 _
    rw [Real.rpow_sub hH0, mul_div_assoc', le_div_iff₀ hpow0]
    calc V p i * H ^ (((kk p i : ℕ) : ℝ) / N) ≤ V p i * (Mx p / V p i) :=
          mul_le_mul_of_nonneg_left hpow (hpos p i).le
      _ = Mx p := by rw [mul_div_assoc', mul_div_cancel_left₀ _ (hpos p i).ne']
      _ ≤ C p * H ^ systemExponent S p := ciSup_le fun j ↦ hle p j

/-! ### The largest forms -/

/-- **Every place of `S∞ ∪ S` is a place of the system.** -/
theorem exists_systemPlace_eq {S : Finset (HeightOneSpectrum (𝓞 K))} {v : AbsoluteValue K ℝ}
    (hv : v ∈ relevantPlaces S) : ∃ p, systemPlace S p = v := by
  rcases hv with ⟨w, rfl⟩ | ⟨P, hP, rfl⟩
  · exact ⟨.inl w, rfl⟩
  · exact ⟨.inr ⟨P, hP⟩, rfl⟩

/-- **Every place of a system is a place of `S∞ ∪ S`.** -/
theorem systemPlace_mem_relevantPlaces (S : Finset (HeightOneSpectrum (𝓞 K)))
    (p : InfinitePlace K ⊕ S) : systemPlace S p ∈ relevantPlaces S := by
  rcases p with v | v
  · exact Or.inl ⟨v, rfl⟩
  · exact Or.inr ⟨v.1, v.2, rfl⟩

/-- **The product over `S∞ ∪ S` is the product over the places of a system**, each to its
multiplicity. -/
theorem placeProd_univ_eq_prod_systemPlace (S : Finset (HeightOneSpectrum (𝓞 K)))
    (g : AbsoluteValue K ℝ → ℝ) :
    placeProd S Set.univ g = ∏ p, g (systemPlace S p) ^ systemMult S p := by
  rw [Fintype.prod_sum_type]
  simp only [placeProd, systemPlace, systemMult, Set.mulIndicator_univ, pow_one]
  rw [Finset.prod_coe_sort S (fun P ↦ g (FinitePlace.mk P).1)]

/-- The multiplicities of the places of a system sum to `[K : ℚ] + #S`. -/
theorem sum_systemMult (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∑ p, systemMult S p = finrank ℚ K + S.card := by
  rw [Fintype.sum_sum_type]
  simp [systemMult, InfinitePlace.sum_mult_eq]

omit [Fintype ι] in
/-- **The largest forms bound the sup norms.** If at every place of the system the sup norm of `x`
is at most `c` times the largest form, then the product of the sup norms over `S∞ ∪ S` is at most
`c ^ ([K : ℚ] + #S)` times the product over the places of the largest local values. -/
theorem placeProd_iSup_le_mul_prod_iSup_systemValue [Finite ι] [Nonempty ι]
    {S : Finset (HeightOneSpectrum (𝓞 K))} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    {x : ι → K} {c : ℝ} (hc : 0 ≤ c)
    (hL : ∀ p, ⨆ j, systemPlace S p (x j) ≤ c * ⨆ i, systemPlace S p (L (systemPlace S p) i x)) :
    placeProd S Set.univ (fun v ↦ ⨆ j, v (x j)) ≤
      c ^ (finrank ℚ K + S.card) * ∏ p, ⨆ i, systemValue S (fun v ↦ v) L p i x := by
  rw [placeProd_univ_eq_prod_systemPlace, ← sum_systemMult, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun p _ ↦ pow_nonneg (Real.iSup_nonneg fun _ ↦ apply_nonneg _ _) _)
    fun p _ ↦ ?_
  set v := systemPlace S p
  obtain ⟨i, hi⟩ := Finite.exists_max fun i ↦ v (L v i x)
  have hG : ⨆ i, v (L v i x) = v (L v i x) :=
    le_antisymm (ciSup_le hi) (le_ciSup (f := fun i ↦ v (L v i x)) (Finite.bddAbove_range _) i)
  have hval : systemValue S (fun v ↦ v) L p i x = v (L v i x) ^ systemMult S p := by
    simp [systemValue, systemAbs, v]
  calc (⨆ j, v (x j)) ^ systemMult S p ≤ (c * v (L v i x)) ^ systemMult S p :=
        pow_le_pow_left₀ (Real.iSup_nonneg fun _ ↦ apply_nonneg _ _) (hG ▸ hL p) _
    _ = c ^ systemMult S p * systemValue S (fun v ↦ v) L p i x := by rw [hval, mul_pow]
    _ ≤ c ^ systemMult S p * ⨆ i, systemValue S (fun v ↦ v) L p i x :=
        mul_le_mul_of_nonneg_left
          (le_ciSup (f := fun i ↦ systemValue S (fun v ↦ v) L p i x) (Finite.bddAbove_range _) i)
          (pow_nonneg hc _)

/-! ### Rounding a factorization -/

omit [Fintype ι] in
/-- **A factorization of `b` into factors `≤ 1`, rounded on a grid.** If `0 < u p i ≤ 1` and
`b = ∏ p, ∏ i, u p i`, then there are `k p i ∈ {0, …, N}` with `u p i ≤ b ^ (k p i / N)` and
`∑ k p i / N ≥ 1 − #P #ι / N`: the exponents `log (u p i) / log b` sum to `1`, and each is
rounded down. -/
theorem exists_le_rpow_prod_grid {P : Type*} [Fintype P] [Fintype ι] [Nonempty P] [Nonempty ι]
    {u : P → ι → ℝ} (hu0 : ∀ p i, 0 < u p i) (hu1 : ∀ p i, u p i ≤ 1) {N : ℕ} (hN : 0 < N) :
    ∃ k : P → ι → Fin (N + 1),
      (∀ p i, u p i ≤ (∏ p, ∏ i, u p i) ^ (((k p i : ℕ) : ℝ) / N)) ∧
        1 - (Fintype.card P * Fintype.card ι : ℝ) / N ≤ ∑ p, ∑ i, ((k p i : ℕ) : ℝ) / N := by
  set b := ∏ p, ∏ i, u p i with hb
  have hb0 : 0 < b := Finset.prod_pos fun p _ ↦ Finset.prod_pos fun i _ ↦ hu0 p i
  have hb1 : b ≤ 1 := Finset.prod_le_one₀ (fun p _ ↦ Finset.prod_nonneg fun i _ ↦ (hu0 p i).le)
    fun p _ ↦ Finset.prod_le_one₀ (fun i _ ↦ (hu0 p i).le) fun i _ ↦ hu1 p i
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcard : (1 : ℝ) ≤ Fintype.card P * Fintype.card ι := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero Fintype.card_ne_zero
      Fintype.card_ne_zero)
  rcases hb1.eq_or_lt with h1 | h1
  · refine ⟨fun _ _ ↦ Fin.last N, fun p i ↦ by rw [h1, Real.one_rpow]; exact hu1 p i, ?_⟩
    simp only [Fin.val_last, div_self hNr.ne', Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
    have : 0 ≤ (Fintype.card P * Fintype.card ι : ℝ) / N := by positivity
    linarith
  have hlogb : Real.log b < 0 := Real.log_neg hb0 h1
  set f : P → ι → ℝ := fun p i ↦ Real.log (u p i) / Real.log b with hf
  have hf0 : ∀ p i, 0 ≤ f p i := fun p i ↦
    div_nonneg_of_nonpos (Real.log_nonpos (hu0 p i).le (hu1 p i)) hlogb.le
  have hfsum : ∑ p, ∑ i, f p i = 1 := by
    have hlog : Real.log b = ∑ p, ∑ i, Real.log (u p i) := by
      rw [hb, Real.log_prod fun p _ ↦ (Finset.prod_pos fun i _ ↦ hu0 p i).ne']
      exact Finset.sum_congr rfl fun p _ ↦ Real.log_prod fun i _ ↦ (hu0 p i).ne'
    simp only [hf, ← Finset.sum_div, ← hlog, div_self hlogb.ne]
  have hf1 : ∀ p i, f p i ≤ 1 := fun p i ↦ by
    rw [← hfsum]
    exact (Finset.single_le_sum (fun i _ ↦ hf0 p i) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (fun p _ ↦ Finset.sum_nonneg fun i _ ↦ hf0 p i) (Finset.mem_univ p))
  refine ⟨fun p i ↦ ⟨min ⌊N * f p i⌋₊ N, Nat.lt_succ_of_le (min_le_right _ _)⟩,
    fun p i ↦ ?_, ?_⟩
  · have hle : ((min ⌊N * f p i⌋₊ N : ℕ) : ℝ) / N ≤ f p i := by
      rw [div_le_iff₀ hNr, mul_comm]
      exact (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le (by have := hf0 p i; positivity))
    calc u p i = b ^ f p i := by
          rw [Real.rpow_def_of_pos hb0, hf, mul_div_cancel₀ _ hlogb.ne, Real.exp_log (hu0 p i)]
      _ ≤ b ^ (((min ⌊N * f p i⌋₊ N : ℕ) : ℝ) / N) :=
          Real.rpow_le_rpow_of_exponent_ge hb0 hb1 hle
  · have hterm : ∀ p i, f p i - 1 / N ≤ ((min ⌊N * f p i⌋₊ N : ℕ) : ℝ) / N := fun p i ↦ by
      rw [sub_div' hNr.ne', div_le_div_iff_of_pos_right hNr, Nat.cast_min, le_min_iff]
      refine ⟨by linarith [Nat.lt_floor_add_one (N * f p i)], ?_⟩
      nlinarith [hf1 p i]
    calc 1 - (Fintype.card P * Fintype.card ι : ℝ) / N
        = ∑ p, ∑ i, (f p i - 1 / N) := by
          simp only [Finset.sum_sub_distrib, hfsum, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
          ring
      _ ≤ _ := Finset.sum_le_sum fun p _ ↦ Finset.sum_le_sum fun i _ ↦ hterm p i

end NumberField
