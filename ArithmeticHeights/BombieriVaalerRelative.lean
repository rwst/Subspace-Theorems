/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.BombieriVaalerEntries
public import ArithmeticHeights.RestrictScalars

/-!
# The relative Siegel lemma

**Bombieri–Gubler, Theorem 2.9.19.** Let `K` be a number field of degree `d` and discriminant `D`,
let `F / K` be a finite extension of degree `r`, and let `A` be an `M × N` matrix with entries in
`F` with `r M < N`. Then there are `N − r M` `K`-linearly independent vectors `x l` with
coordinates integral over `ℤ`, solving `A x = 0`, and

```text
∏_{l} H(x l)  ≤  |D| ^ ((N − r M) / (2 d)) · ∏_{i=1}^{M} H_Ar(A i) ^ r,
```

`H` the absolute multiplicative height on `K ^ N` and `H_Ar(A i)` the absolute Arakelov height of
the `i`-th row of `A`, an element of `F ^ N`. This is the form transcendence and
Diophantine-approximation arguments import, where the auxiliary construction and the field of
definition differ; the `K = ℚ` case is Hindry–Silverman, Lemma D.4.2.

## Main results

* `NumberField.exists_linearIndependent_mem_ker_prod_absMulHeight_le`: the milestone.
* `NumberField.exists_basis_ker_prod_absMulHeight_le_relative`: the product bound over a *basis*
  of the `K`-rational solution space, from which the milestone is extracted. Its exponent on the
  discriminant is the dimension of that solution space rather than `N − r M`.
* `Real.exists_injective_prod_pow_le`: Bombieri and Gubler's "rearrange by increasing height", the
  step that turns the basis bound into the bound for `N − r M` of the vectors.
* `NumberField.exists_ne_zero_mem_ker_absMulHeight_le_relative`: a single small solution, the form
  Bombieri and Gubler's own applications quote.
* `NumberField.exists_linearIndependent_mem_ker_prod_absMulHeight_le_rank` and
  `NumberField.exists_ne_zero_mem_ker_absMulHeight_le_relative_rank`: the same two statements with
  `r · rank A < N` in place of `r M < N`. Added for Layer 5.7.

## Implementation notes

⚠ **The two statements differ in the exponent of the discriminant, and the sorting step is what
separates them.** The basis form gives `k = dim ker` vectors with `∏ H ≤ |D| ^ (k / (2 d)) · P`,
and `k ≥ N − r M` with equality only when the restricted system has full rank `r M`, which it need
not have — a single row over `F` all of whose entries lie in `K` descends to a system of rank `1`,
not `r`. Dropping `k − (N − r M)` factors is free, since every height is at least `1`, but
dropping the discriminant they carry is not, and `|D| ≥ 1`. Bombieri and Gubler's fix is to order
the vectors by increasing height and take the smallest `N − r M`: the geometric mean of the
smallest `k'` of `k` numbers is at most the geometric mean of all `k`, so the bound is raised to
the power `k' / k`, which divides the exponent of `|D|` down to `k' / (2 d)` exactly and costs
nothing on `P ≥ 1`. That is `Real.exists_injective_prod_pow_le`.

⚠ **The solution space is stated as the kernel of `Matrix.mulVecRestrict`,** the `K`-linear map
`x ↦ A x` on `K`-rational vectors, and not as the kernel of any restricted system: a basis of
`F / K` is an artefact of the proof and does not belong in the statement. That the two agree is
`Matrix.ker_mulVecLin_restrictScalars`.

⚠ **The feasibility hypothesis is about the rank, not about the number of rows.** `r M < N` is
what Bombieri and Gubler state and it is what a caller who has not computed a rank can check, but
the descended system has `K`-rank at most `r · rank A`, so `r · rank A < N` is already enough and
produces `N − r · rank A` solutions rather than `N − r M`. Both forms are one lemma apart —
`Matrix.le_finrank_ker_mulVecRestrict` — and both are delivered; Layer 5.7 quotes the rank form,
because a system of vanishing conditions on a polynomial is normally given with repetitions.

⚠ **Layer 5.4 had to lose its `Fin m`.** The restricted system has rows indexed by
`Fin m × Fin r`, and the row index is inert in the whole of 5.4 — the bound is in terms of the row
*space* — so `NumberField.exists_basis_ker_prod_absMulHeight_le` and
`Matrix.finrank_ker_mulVecLin` are now stated for an arbitrary row type. Nothing else changed.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 2.9.19. M. Hindry and J. H. Silverman, *Diophantine Geometry: An Introduction*, Springer
GTM 201 (2000), Lemma D.4.2, "Siegel's lemma, second form", the case `K = ℚ`.

This is Layer 5.6 of the `ArithmeticHeights` roadmap.
-/

public section

open Finset Matrix Module NumberField Real

/-!
### Rearranging by increasing height
-/

namespace Real

private lemma prod_range_pow_le {k : ℕ} (G : ℕ → ℝ) (h1 : ∀ i, 1 ≤ G i)
    (hm : ∀ a b, a ≤ b → b < k → G a ≤ G b) {k' : ℕ} (hk' : k' ≤ k) :
    (∏ i ∈ Finset.range k', G i) ^ k ≤ (∏ i ∈ Finset.range k, G i) ^ k' := by
  rcases eq_or_lt_of_le hk' with rfl | hlt
  · exact le_rfl
  set P₁ := ∏ i ∈ Finset.range k', G i with hP1def
  set P₂ := ∏ i ∈ Finset.Ico k' k, G i with hP2def
  have hP : P₁ * P₂ = ∏ i ∈ Finset.range k, G i := Finset.prod_range_mul_prod_Ico G hk'
  have hP1 : 1 ≤ P₁ := Finset.one_le_prod₀ fun i _ ↦ h1 i
  have hP2 : 1 ≤ P₂ := Finset.one_le_prod₀ fun i _ ↦ h1 i
  set c := G k' with hcdef
  have hc1 : 1 ≤ c := h1 k'
  have hub : P₁ ≤ c ^ k' := by
    calc P₁ ≤ ∏ _i ∈ Finset.range k', c :=
          Finset.prod_le_prod₀ (fun i _ ↦ by linarith [h1 i])
            (fun i hi ↦ hm i k' (le_of_lt (Finset.mem_range.1 hi)) hlt)
      _ = c ^ k' := by rw [Finset.prod_const, Finset.card_range]
  have hlb : c ^ (k - k') ≤ P₂ := by
    calc c ^ (k - k') = ∏ _i ∈ Finset.Ico k' k, c := by
          rw [Finset.prod_const, Nat.card_Ico]
      _ ≤ P₂ := Finset.prod_le_prod₀ (fun i _ ↦ by linarith)
            (fun i hi ↦ hm k' i (Finset.mem_Ico.1 hi).1 (Finset.mem_Ico.1 hi).2)
  have key : P₁ ^ (k - k') ≤ P₂ ^ k' := by
    calc P₁ ^ (k - k') ≤ (c ^ k') ^ (k - k') := pow_le_pow_left₀ (by linarith) hub _
      _ = (c ^ (k - k')) ^ k' := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ P₂ ^ k' := pow_le_pow_left₀ (by positivity) hlb _
  calc P₁ ^ k = P₁ ^ k' * P₁ ^ (k - k') := by rw [← pow_add]; congr 1; omega
    _ ≤ P₁ ^ k' * P₂ ^ k' := by
        have hnn : (0 : ℝ) ≤ P₁ ^ k' := by positivity
        nlinarith
    _ = (P₁ * P₂) ^ k' := (mul_pow _ _ _).symm
    _ = _ := by rw [hP]

/-- **Rearranging by increasing size** (Bombieri–Gubler, in the proof of Theorem 2.9.19). From `k`
numbers, all at least `1`, one can select `k'` of them whose product `T` satisfies
`T ^ k ≤ (∏ all) ^ k'` — the geometric mean of the `k'` smallest is at most the geometric mean of
all `k`. Selecting is an injection `Fin k' → Fin k`, and the proof is the sorting permutation
`Tuple.sort`. -/
theorem exists_injective_prod_pow_le {k : ℕ} (g : Fin k → ℝ) (hg : ∀ l, 1 ≤ g l) {k' : ℕ}
    (hk' : k' ≤ k) :
    ∃ f : Fin k' → Fin k, Function.Injective f ∧
      (∏ l, g (f l)) ^ k ≤ (∏ l, g l) ^ k' := by
  classical
  set s := Tuple.sort g with hsdef
  set G : ℕ → ℝ := fun n ↦ if h : n < k then g (s ⟨n, h⟩) else 1 with hGdef
  have hG1 : ∀ i, 1 ≤ G i := by
    intro i
    rw [hGdef]
    dsimp only
    split
    · exact hg _
    · exact le_rfl
  have hGm : ∀ a b, a ≤ b → b < k → G a ≤ G b := by
    intro a b hab hb
    have ha : a < k := lt_of_le_of_lt hab hb
    simp only [hGdef, ha, hb, ↓reduceDIte]
    exact Tuple.monotone_sort g (show (⟨a, ha⟩ : Fin k) ≤ ⟨b, hb⟩ from hab)
  have e1 : ∏ l : Fin k', g (s (Fin.castLE hk' l)) = ∏ i ∈ Finset.range k', G i := by
    rw [← Fin.prod_univ_eq_prod_range G k']
    refine Finset.prod_congr rfl fun l _ ↦ ?_
    have hl : (l : ℕ) < k := lt_of_lt_of_le l.2 hk'
    simp only [hGdef, hl, ↓reduceDIte]
    rfl
  have e2 : ∏ l : Fin k, g l = ∏ i ∈ Finset.range k, G i := by
    rw [← Fin.prod_univ_eq_prod_range G k, ← Equiv.prod_comp s g]
    refine Finset.prod_congr rfl fun l _ ↦ ?_
    simp only [hGdef, l.2, ↓reduceDIte]
  refine ⟨fun l ↦ s (Fin.castLE hk' l), fun a b hab ↦ ?_, ?_⟩
  · exact Fin.castLE_injective hk' (s.injective hab)
  · rw [e1, e2]
    exact prod_range_pow_le G hG1 hGm hk'

end Real

/-!
### The relative Siegel lemma
-/

namespace NumberField

variable {K F : Type*} [Field K] [Field F] [NumberField K] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

open scoped Classical in
/-- **Layer 5.6 — the product bound over a basis of the `K`-rational solution space.** With
`k = dim_K {x ∈ K^N | A x = 0}`, `d = [K : ℚ]`, `r = [F : K]` and `D` the discriminant of `K`,
there is a basis of that space with coordinates integral over `ℤ` and

`∏ₗ H(xₗ) ≤ |D| ^ (k / (2 d)) · ∏ᵢ H_Ar(Aᵢ) ^ r`,

`H` absolute and `H_Ar` the absolute Arakelov height over `F`. -/
theorem exists_basis_ker_prod_absMulHeight_le_relative (A : Matrix (Fin m) ι F) {k : ℕ}
    (hk : finrank K (LinearMap.ker (Matrix.mulVecRestrict (K := K) A)) = k) :
    ∃ b : Basis (Fin k) K ↥(LinearMap.ker (Matrix.mulVecRestrict (K := K) A)),
      (∀ l j, IsIntegral ℤ ((b l : ι → K) j)) ∧
      (∏ l, absMulHeight fun j ↦ (b l : ι → K) j) ≤
        |(NumberField.discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K))
          * ∏ i, (arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ finrank K F := by
  have : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Module.Finite K F := Module.Finite.of_restrictScalars_finite ℚ K F
  set e := Module.finBasis K F with hedef
  have hker := Matrix.ker_mulVecLin_restrictScalars e A
  rw [← hker] at hk ⊢
  obtain ⟨b, hint, hle⟩ := exists_basis_ker_prod_absMulHeight_le (Matrix.restrictScalars e A) hk
  exact ⟨b, hint, hle.trans (mul_le_mul_of_nonneg_left
    (Matrix.arakelovMulHeight_span_restrictScalars_rpow_le' e A)
    (Real.rpow_nonneg (abs_nonneg _) _))⟩

open scoped Classical in
/-- **The relative Siegel lemma, in the form both hypotheses specialize.** The number of
independent solutions produced is any `k'` bounded by the dimension of the `K`-rational solution
space; the two public forms below supply that bound from the number of rows and from the rank. -/
private theorem exists_linearIndependent_mem_ker_prod_absMulHeight_le_aux
    (A : Matrix (Fin m) ι F) {k' : ℕ} (hk'0 : 0 < k')
    (hk'k : k' ≤ finrank K (LinearMap.ker (Matrix.mulVecRestrict (K := K) A))) :
    ∃ x : Fin k' → (ι → K),
      LinearIndependent K x ∧
      (∀ l, A.mulVec (fun j ↦ algebraMap K F (x l j)) = 0) ∧
      (∀ l j, IsIntegral ℤ (x l j)) ∧
      (∏ l, absMulHeight (x l)) ≤
        |(NumberField.discr K : ℝ)| ^ ((k' : ℝ) / (2 * finrank ℚ K))
          * ∏ i, (arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ finrank K F := by
  classical
  set V := LinearMap.ker (Matrix.mulVecRestrict (K := K) A) with hVdef
  set k : ℕ := finrank K V with hkdef
  have hk0 : 0 < k := lt_of_lt_of_le hk'0 hk'k
  obtain ⟨b, hint, hle⟩ := exists_basis_ker_prod_absMulHeight_le_relative A hkdef.symm
  set g : Fin k → ℝ := fun l ↦ absMulHeight fun j ↦ (b l : ι → K) j with hgdef
  have hg : ∀ l, 1 ≤ g l := fun l ↦ one_le_absMulHeight _
  obtain ⟨f, hfinj, hfle⟩ := Real.exists_injective_prod_pow_le g hg hk'k
  set P : ℝ := ∏ i, (arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ finrank K F with hPdef
  set Dk : ℝ := |(NumberField.discr K : ℝ)| with hDkdef
  have hDk0 : (0 : ℝ) ≤ Dk := abs_nonneg _
  have hP1 : 1 ≤ P :=
    Finset.one_le_prod₀ fun i _ ↦ one_le_pow₀
      (Real.one_le_rpow (one_le_arakelovMulHeight _) (by positivity))
  set Q : ℝ := Dk ^ ((k : ℝ) / (2 * finrank ℚ K)) * P with hQdef
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  set T : ℝ := ∏ l, g (f l) with hTdef
  have hT0 : (0 : ℝ) ≤ T := Finset.prod_nonneg fun l _ ↦ le_trans zero_le_one (hg _)
  have hstep : T ^ k ≤ Q ^ k' :=
    hfle.trans (pow_le_pow_left₀ (Finset.prod_nonneg fun l _ ↦ le_trans zero_le_one (hg l)) hle k')
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk0.ne'
  have hTle : T ≤ Q ^ ((k' : ℝ) / k) := by
    have h := Real.rpow_le_rpow (by positivity) hstep (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹)
    rw [Real.pow_rpow_inv_natCast hT0 hk0.ne'] at h
    refine h.trans (le_of_eq ?_)
    rw [← Real.rpow_natCast Q k', ← Real.rpow_mul hQ0, div_eq_mul_inv]
  have hDpow : (Dk ^ ((k : ℝ) / (2 * finrank ℚ K))) ^ ((k' : ℝ) / k)
      = Dk ^ ((k' : ℝ) / (2 * finrank ℚ K)) := by
    rw [← Real.rpow_mul hDk0]
    congr 1
    field_simp
  have hPpow : P ^ ((k' : ℝ) / k) ≤ P := by
    calc P ^ ((k' : ℝ) / k) ≤ P ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hP1
            (by rw [div_le_one (by positivity)]; exact_mod_cast hk'k)
      _ = P := Real.rpow_one P
  have hfinal : Q ^ ((k' : ℝ) / k) ≤ Dk ^ ((k' : ℝ) / (2 * finrank ℚ K)) * P := by
    rw [hQdef, Real.mul_rpow (Real.rpow_nonneg hDk0 _) (by linarith), hDpow]
    exact mul_le_mul_of_nonneg_left hPpow (Real.rpow_nonneg hDk0 _)
  refine ⟨fun l ↦ fun j ↦ (b (f l) : ι → K) j, ?_, ?_, fun l j ↦ hint (f l) j, ?_⟩
  · exact (b.linearIndependent.comp f hfinj).map' V.subtype V.ker_subtype
  · intro l
    have hmem := (b (f l)).2
    rw [LinearMap.mem_ker, Matrix.mulVecRestrict_apply] at hmem
    exact hmem
  · exact hTle.trans hfinal

omit [LinearOrder ι] in
/-- The `K`-rational solution space of `A x = 0` has dimension at least `N − r M`, and at least
`N − r · rank A`. Both bounds come from `Matrix.le_finrank_ker_mulVecRestrict`. -/
private theorem le_finrank_ker_mulVecRestrict_row (A : Matrix (Fin m) ι F) :
    Fintype.card ι - finrank K F * m
      ≤ finrank K (LinearMap.ker (Matrix.mulVecRestrict (K := K) A)) := by
  have : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Module.Finite K F := Module.Finite.of_restrictScalars_finite ℚ K F
  have hrank : A.rank ≤ m := by simpa using A.rank_le_card_height
  have := Matrix.le_finrank_ker_mulVecRestrict (K := K) A
  have hmul : finrank K F * A.rank ≤ finrank K F * m := Nat.mul_le_mul_left _ hrank
  omega

open scoped Classical in
/-- **Layer 5.6 — the relative Siegel lemma** (Bombieri–Gubler, Theorem 2.9.19). Entries in a
finite extension `F / K` of degree `r`, solutions required in `K`: if `r M < N` there are
`N − r M` `K`-linearly independent solutions with coordinates integral over `ℤ` and

`∏ₗ H(xₗ) ≤ |D| ^ ((N − r M) / (2 d)) · ∏ᵢ H_Ar(Aᵢ) ^ r`. -/
theorem exists_linearIndependent_mem_ker_prod_absMulHeight_le (A : Matrix (Fin m) ι F)
    (hmn : finrank K F * m < Fintype.card ι) :
    ∃ x : Fin (Fintype.card ι - finrank K F * m) → (ι → K),
      LinearIndependent K x ∧
      (∀ l, A.mulVec (fun j ↦ algebraMap K F (x l j)) = 0) ∧
      (∀ l j, IsIntegral ℤ (x l j)) ∧
      (∏ l, absMulHeight (x l)) ≤
        |(NumberField.discr K : ℝ)| ^
            ((Fintype.card ι - finrank K F * m : ℝ) / (2 * finrank ℚ K))
          * ∏ i, (arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ finrank K F := by
  have hcast : ((Fintype.card ι - finrank K F * m : ℝ))
      = ((Fintype.card ι - finrank K F * m : ℕ) : ℝ) := by
    rw [Nat.cast_sub hmn.le]
    push_cast
    ring
  rw [hcast]
  exact exists_linearIndependent_mem_ker_prod_absMulHeight_le_aux A (by omega)
    (le_finrank_ker_mulVecRestrict_row A)

open scoped Classical in
/-- **Layer 5.6 with the rank in place of the number of rows.** The feasibility hypothesis that
the descended system really needs is `r · rank A < N`, not `r M < N`: a system of `M` rows over
`F` whose rank is `R` descends to one of `K`-rank at most `r R`, which is strictly less than
`r M` as soon as the rows of `A` are dependent. This is the form Layer 5.7 quotes. -/
theorem exists_linearIndependent_mem_ker_prod_absMulHeight_le_rank (A : Matrix (Fin m) ι F)
    (hmn : finrank K F * A.rank < Fintype.card ι) :
    ∃ x : Fin (Fintype.card ι - finrank K F * A.rank) → (ι → K),
      LinearIndependent K x ∧
      (∀ l, A.mulVec (fun j ↦ algebraMap K F (x l j)) = 0) ∧
      (∀ l j, IsIntegral ℤ (x l j)) ∧
      (∏ l, absMulHeight (x l)) ≤
        |(NumberField.discr K : ℝ)| ^
            ((Fintype.card ι - finrank K F * A.rank : ℝ) / (2 * finrank ℚ K))
          * ∏ i, (arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ finrank K F := by
  have : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Module.Finite K F := Module.Finite.of_restrictScalars_finite ℚ K F
  have hcast : ((Fintype.card ι - finrank K F * A.rank : ℝ))
      = ((Fintype.card ι - finrank K F * A.rank : ℕ) : ℝ) := by
    rw [Nat.cast_sub hmn.le]
    push_cast
    ring
  rw [hcast]
  exact exists_linearIndependent_mem_ker_prod_absMulHeight_le_aux A (by omega)
    (Matrix.le_finrank_ker_mulVecRestrict A)

open scoped Classical in
/-- **A single small solution, in the form both hypotheses specialize.** -/
private theorem exists_ne_zero_mem_ker_absMulHeight_le_relative_aux (A : Matrix (Fin m) ι F)
    {k' : ℕ} (hk'0 : 0 < k')
    (hk'k : k' ≤ finrank K (LinearMap.ker (Matrix.mulVecRestrict (K := K) A))) :
    ∃ x : ι → K, x ≠ 0 ∧ A.mulVec (fun j ↦ algebraMap K F (x j)) = 0 ∧
      (∀ j, IsIntegral ℤ (x j)) ∧
      absMulHeight x ≤
        |(NumberField.discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹
          * (∏ i, (arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ finrank K F)
              ^ ((k' : ℝ))⁻¹ := by
  classical
  obtain ⟨x, hind, hmem, hint, hle⟩ :=
    exists_linearIndependent_mem_ker_prod_absMulHeight_le_aux A hk'0 hk'k
  have : Nonempty (Fin k') := Fin.pos_iff_nonempty.1 hk'0
  obtain ⟨l₀, hl₀⟩ := Finite.exists_min fun l : Fin k' ↦ absMulHeight (x l)
  set P : ℝ := ∏ i, (arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ finrank K F with hPdef
  set Dk : ℝ := |(NumberField.discr K : ℝ)| with hDkdef
  have hDk0 : (0 : ℝ) ≤ Dk := abs_nonneg _
  have hP1 : 1 ≤ P :=
    Finset.one_le_prod₀ fun i _ ↦ one_le_pow₀
      (Real.one_le_rpow (one_le_arakelovMulHeight _) (by positivity))
  set H : ℝ := absMulHeight (x l₀) with hHdef
  have hH1 : 1 ≤ H := one_le_absMulHeight _
  have hpow : H ^ k' ≤ Dk ^ ((k' : ℝ) / (2 * finrank ℚ K)) * P := by
    refine le_trans ?_ hle
    calc H ^ k' = ∏ _l : Fin k', H := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ l, absMulHeight (x l) :=
          Finset.prod_le_prod₀ (fun l _ ↦ by positivity) fun l _ ↦ hl₀ l
  have hfinal : H ≤ Dk ^ (2 * finrank ℚ K : ℝ)⁻¹ * P ^ ((k' : ℝ))⁻¹ := by
    have hstep := Real.rpow_le_rpow (by positivity) hpow
      (by positivity : (0 : ℝ) ≤ (k' : ℝ)⁻¹)
    rw [Real.pow_rpow_inv_natCast (by linarith) hk'0.ne'] at hstep
    refine hstep.trans (le_of_eq ?_)
    rw [Real.mul_rpow (Real.rpow_nonneg hDk0 _) (by linarith), ← Real.rpow_mul hDk0]
    congr 2
    have hkne : (k' : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk'0.ne'
    field_simp
  exact ⟨x l₀, hind.ne_zero l₀, hmem l₀, fun j ↦ hint l₀ j, hfinal⟩

open scoped Classical in
/-- **Layer 5.6 — a single small solution** (Bombieri–Gubler use exactly this form of 2.9.19 in
their applications). With `r M < N`, the system `A x = 0` has a nonzero `K`-rational solution with
coordinates integral over `ℤ` and

`H(x) ≤ |D| ^ (1 / (2 d)) · (∏ᵢ H_Ar(Aᵢ) ^ r) ^ (1 / (N − r M))`. -/
theorem exists_ne_zero_mem_ker_absMulHeight_le_relative (A : Matrix (Fin m) ι F)
    (hmn : finrank K F * m < Fintype.card ι) :
    ∃ x : ι → K, x ≠ 0 ∧ A.mulVec (fun j ↦ algebraMap K F (x j)) = 0 ∧
      (∀ j, IsIntegral ℤ (x j)) ∧
      absMulHeight x ≤
        |(NumberField.discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹
          * (∏ i, (arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ finrank K F)
              ^ ((Fintype.card ι - finrank K F * m : ℝ))⁻¹ := by
  have hcast : ((Fintype.card ι - finrank K F * m : ℝ))
      = ((Fintype.card ι - finrank K F * m : ℕ) : ℝ) := by
    rw [Nat.cast_sub hmn.le]
    push_cast
    ring
  rw [hcast]
  exact exists_ne_zero_mem_ker_absMulHeight_le_relative_aux A (by omega)
    (le_finrank_ker_mulVecRestrict_row A)

open scoped Classical in
/-- **Layer 5.6 — a single small solution, with the rank in place of the number of rows.** -/
theorem exists_ne_zero_mem_ker_absMulHeight_le_relative_rank (A : Matrix (Fin m) ι F)
    (hmn : finrank K F * A.rank < Fintype.card ι) :
    ∃ x : ι → K, x ≠ 0 ∧ A.mulVec (fun j ↦ algebraMap K F (x j)) = 0 ∧
      (∀ j, IsIntegral ℤ (x j)) ∧
      absMulHeight x ≤
        |(NumberField.discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹
          * (∏ i, (arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ finrank K F)
              ^ ((Fintype.card ι - finrank K F * A.rank : ℝ))⁻¹ := by
  have : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Module.Finite K F := Module.Finite.of_restrictScalars_finite ℚ K F
  have hcast : ((Fintype.card ι - finrank K F * A.rank : ℝ))
      = ((Fintype.card ι - finrank K F * A.rank : ℕ) : ℝ) := by
    rw [Nat.cast_sub hmn.le]
    push_cast
    ring
  rw [hcast]
  exact exists_ne_zero_mem_ker_absMulHeight_le_relative_aux A (by omega)
    (Matrix.le_finrank_ker_mulVecRestrict A)

end NumberField

/-!
### Examples

The absolute case is the milestone at `F = K`, and it is Bombieri–Gubler's Corollary 2.9.9 in the
row-space normalization; the conformance example pairs the two statements of the milestone.
-/

section Examples

open Matrix Module NumberField

/-- **Conformance: the absolute case is `F = K`.** At `r = 1` the relative Siegel lemma is the
statement Layer 5.4 produces — `N − M` independent integral solutions of `A x = 0` with
`∏ₗ H(xₗ) ≤ |D| ^ ((N − M) / (2 d)) · ∏ᵢ H_Ar(Aᵢ)`, absolute heights throughout. A development in
which the degree `r` had been miscounted produces a different exponent here. -/
example {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}
    (A : Matrix (Fin m) ι K) (hmn : m < Fintype.card ι) :
    ∃ x : Fin (Fintype.card ι - m) → (ι → K),
      LinearIndependent K x ∧ (∀ l, A.mulVec (x l) = 0) ∧
      (∀ l j, IsIntegral ℤ (x l j)) ∧
      (∏ l, NumberField.absMulHeight (x l)) ≤
        |(NumberField.discr K : ℝ)| ^ ((Fintype.card ι - m : ℝ) / (2 * finrank ℚ K))
          * ∏ i, NumberField.arakelovMulHeight (A i) ^ (finrank ℚ K : ℝ)⁻¹ := by
  have hr : finrank K K = 1 := Module.finrank_self K
  have h := NumberField.exists_linearIndependent_mem_ker_prod_absMulHeight_le
    (K := K) (F := K) A (by rw [hr]; simpa using hmn)
  rw [hr, one_mul] at h
  simpa using h

/-- **Conformance.** The two statements of the milestone: the product bound over `N − r M`
independent solutions, and the single small solution extracted from it. -/
example {K F : Type*} [Field K] [Field F] [NumberField K] [NumberField F] [Algebra K F]
    {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ} (A : Matrix (Fin m) ι F)
    (hmn : finrank K F * m < Fintype.card ι) :
    (∃ x : Fin (Fintype.card ι - finrank K F * m) → (ι → K),
        LinearIndependent K x ∧ (∀ l, A.mulVec (fun j ↦ algebraMap K F (x l j)) = 0) ∧
        (∀ l j, IsIntegral ℤ (x l j)) ∧
        (∏ l, NumberField.absMulHeight (x l)) ≤
          |(NumberField.discr K : ℝ)| ^
              ((Fintype.card ι - finrank K F * m : ℝ) / (2 * finrank ℚ K))
            * ∏ i, (NumberField.arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ finrank K F) ∧
      ∃ x : ι → K, x ≠ 0 ∧ A.mulVec (fun j ↦ algebraMap K F (x j)) = 0 ∧
        (∀ j, IsIntegral ℤ (x j)) ∧
        NumberField.absMulHeight x ≤
          |(NumberField.discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹
            * (∏ i, (NumberField.arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ finrank K F)
                ^ ((Fintype.card ι - finrank K F * m : ℝ))⁻¹ :=
  ⟨NumberField.exists_linearIndependent_mem_ker_prod_absMulHeight_le A hmn,
    NumberField.exists_ne_zero_mem_ker_absMulHeight_le_relative A hmn⟩

end Examples

end
