/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SubspaceHeightBounds
public import ArithmeticHeights.FinitePlaceIdeal

/-!
# The exceptional subspaces, and the height of `V(Q)`

Bombieri–Gubler's Lemma 7.5.21, Step III of the proof of the Subspace Theorem. For approximation
domains whose exponents have weight at most `-ε/2` there are a **finite** set `𝒲` of subspaces,
depending only on the forms and on `S`, and constants `C₄`, `C₅`, `C₆` **not depending on `Q`**,
such that for every level `Q` with `log Q ≥ C₄ / ε` at which the domain has rank `n`, either its
span `V(Q)` lies in `𝒲` or

```text
ε log Q / (4 |S|) - C₅  ≤  h(V(Q))  ≤  n (∑_{v ∈ S} d_v c_max(v)) log Q + C₆ .
```

The dichotomy is on the **pattern** of `V(Q)`: at each place of `S`, the set `I v` of indices `i`
for which the wedge of the forms `L v i'`, `i' ≠ i`, does not vanish at the Plücker point. Let
`k v` be the index of `I v` with the largest exponent. If the weight along `k` is at least
`-ε/4`, the two bounds of `DiophantineApproximation/SubspaceHeightBounds.lean` apply and give the
lower bound. If it is below `-ε/4`, then `V(Q)` is the kernel of a vector fixed in advance by the
pattern, and there are only finitely many patterns.

## Main definitions

* `Module.Dual.vec`: the coefficient vector of a linear form, `f.vec ⬝ᵥ x = f x`.
* `NumberField.patternSpace`: the vectors carried by a pattern — at each place of `S`, the span of
  the coefficient vectors of the forms the pattern names.

## Main results

* `NumberField.exists_finite_forall_logHeight_approxSpan`: **the milestone**, Lemma 7.5.21.
* `NumberField.exists_finite_forall_mem_of_weightAt_lt`: the exceptional alternative.
* `NumberField.mem_span_vec_of_normal`: the normal vector of `V(Q)` is carried by its pattern.
* `NumberField.one_le_mul_rpow_weightAt`: the product formula against the bounds at `S`.
* `exists_smul_eq_of_forall_dotProduct_eq_zero`: two vectors with nested kernels are proportional.
* `NumberField.exists_smul_apply_le_one`: every tuple has a nonzero multiple integral at every
  finite place.

## Implementation notes

⚠ **The book's exceptional space is one space per pattern, not one space.** Bombieri–Gubler write
"there is a linear space `W`, independent of `Π(Q)` and `ε`"; their proof fixes one solution `w`
of the system `L̂_{v i}(w) = 0`, `i ∉ I_v`, and that system depends on the pattern `(I_v)`, which
moves with `Q`. What is true is that there are finitely many patterns and hence finitely many
exceptional subspaces, which is all Step IV consumes. A formal statement with a single `W` is not
what the proof gives.

⚠ **The system is an intersection of spans of coefficient vectors, and no star operator appears.**
Read in the original coordinates, `L̂_{v i}(w) = 0` for `i ∉ I_v` says exactly that `w` lies in the
span of the coefficient vectors of the forms `L v i` with `i ∈ I_v` (`NumberField.patternSpace`).
That description is manifestly independent of `Q`, needs no Hodge star, no adjugate and no Laplace
expansion of an `(n+1) × (n+1)` determinant, and it hands the estimate its coefficients directly:
`w ⬝ᵥ x = ∑_{i ∈ I_v} β_i · L v i (x)`, each term small because `x` lies in the domain.

⚠ **That the pattern of `V(Q)` is the pattern of its normal vector is Plücker duality at the ranks
`n` and `1`.** `Submodule.exists_normal` says that the Plücker coordinate of a basis at the
`n`-subset omitting `i` vanishes exactly when the `i`-th coordinate of the normal vector does;
applying it to the family transformed by the forms at `v` turns "the wedge omitting `i` kills the
Plücker point" into "the `i`-th coordinate of the normal vector of the transformed subspace
vanishes", and the two normal vectors are proportional because their kernels agree.

⚠ **The chosen exceptional vector has to be scaled into the integers, and that is what confines
the product formula to `S`.** A nonzero vector of the pattern space becomes integral at *every*
finite place after multiplication by a common denominator
(`NumberField.exists_smul_apply_le_one`), and only then is `|w ⬝ᵥ x|_v ≤ 1` outside `S`, which is
what lets `1 = ∏_v |w ⬝ᵥ x|_v` be bounded by the product over `S` alone. Scaling changes neither
the kernel nor the pattern, so nothing else has to be re-proved.

⚠ **`n ≥ 1` is not needed.** In rank `0` the single `n`-subset is the empty one, every wedge is
the empty product `1`, so the pattern is full, `k v` is the only index, the weight along `k` *is*
the weight of the exponents, and the hypothesis `weight ≤ -ε/2` puts every level in the
exceptional branch. The statement is then vacuously true there, and the proof never divides by
`n`.

⚠ **The constant is `(4 |S|)⁻¹` and not the book's `(4 r |S|)⁻¹`**, because in Mathlib's
normalization the local degrees `d_v` sit inside the local factors; `|S|` here counts the places
of `S` without multiplicity, and the upper bound correspondingly reads
`n ∑_{v ∈ S} d_v c_max(v)` where the book reads `n c_max |S|`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
7.5.20 and Lemma 7.5.21.

This is Layer 5.4 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

noncomputable section

open Finset Module exteriorPower Matrix Real NumberField Height

/-- The coefficient vector of a linear form: its values at the standard basis. -/
def Module.Dual.vec {K ι : Type*} [Field K] [DecidableEq ι]
    (f : Dual K (ι → K)) : ι → K := fun j ↦ f (Pi.single j 1)

theorem Module.Dual.vec_dotProduct {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (f : Dual K (ι → K)) (x : ι → K) : f.vec ⬝ᵥ x = f x := by
  rw [Module.Dual.apply_eq_sum f x, dotProduct]
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

/-- **Two vectors whose kernels are nested are proportional.** -/
theorem exists_smul_eq_of_forall_dotProduct_eq_zero {K ι : Type*} [Field K] [Fintype ι]
    {ζ ζ' : ι → K} (hζ' : ζ' ≠ 0)
    (h : ∀ x : ι → K, ζ' ⬝ᵥ x = 0 → ζ ⬝ᵥ x = 0) : ∃ μ : K, ζ = μ • ζ' := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hζ'
  rw [Pi.zero_apply] at hj
  refine ⟨ζ j / ζ' j, funext fun i ↦ ?_⟩
  have hx : ζ' ⬝ᵥ (ζ' j • Pi.single i 1 - ζ' i • Pi.single j (1 : K)) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_single, dotProduct_single]
    ring
  have hy := h _ hx
  rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_single, dotProduct_single] at hy
  simp only [smul_eq_mul, mul_one] at hy
  rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hj]
  linear_combination hy

/-- **Every tuple has a nonzero multiple that is integral at every finite place.** -/
theorem NumberField.exists_smul_apply_le_one {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Finite ι] (ζ : ι → K) :
    ∃ lam : K, lam ≠ 0 ∧ ∀ (w : FinitePlace K) (i : ι), w (lam * ζ i) ≤ 1 := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (RingOfIntegers K)) ζ
  refine ⟨algebraMap (RingOfIntegers K) K (b : RingOfIntegers K), ?_, fun w i ↦ ?_⟩
  · simp [nonZeroDivisors.coe_ne_zero b]
  · obtain ⟨a, ha⟩ := hb i
    have : algebraMap (RingOfIntegers K) K (b : RingOfIntegers K) * ζ i
        = algebraMap (RingOfIntegers K) K a := by
      rw [ha, Algebra.smul_def]
    rw [this]
    exact FinitePlace.apply_le_one w a

namespace AbsoluteValue

variable {K ι : Type*} [Field K]

/-- A sum is at most the number of terms times a common bound. -/
theorem apply_sum_le_of_le (v : AbsoluteValue K ℝ) (T : Finset ι) (f : ι → K) {b : ℝ}
    (hb : ∀ i ∈ T, v (f i) ≤ b) : v (∑ i ∈ T, f i) ≤ (#T : ℝ) * b := by
  calc v (∑ i ∈ T, f i) ≤ ∑ i ∈ T, v (f i) := v.sum_le _ _
    _ ≤ ∑ _i ∈ T, b := Finset.sum_le_sum hb
    _ = (#T : ℝ) * b := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The nonarchimedean companion of `AbsoluteValue.apply_sum_le_of_le`. -/
theorem apply_sum_le_of_le_of_isNonarchimedean {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    (T : Finset ι) (f : ι → K) {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ i ∈ T, v (f i) ≤ b) :
    v (∑ i ∈ T, f i) ≤ b :=
  Finset.sum_induction f (fun t ↦ v t ≤ b) (fun p q hp hq ↦ (hv p q).trans (max_le hp hq))
    (by simpa using hb0) hb

end AbsoluteValue

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
  {S₀ : Finset (FinitePlace K)} {c : AbsoluteValue K ℝ → ι → ℝ}

omit [Fintype ι] in
/-- **The product formula against the bounds at the places of `S`.** If a nonzero element of `K`
is at most `A * Q ^ c v (k v)` at each place of `S` and at most `1` at the other finite places,
then `1` is at most `A` to the number of places times `Q` to the weight along `k`. -/
theorem one_le_mul_rpow_weightAt {Q : ℝ} (hQ : 1 ≤ Q) {D : K} (hD : D ≠ 0) {A : ℝ} (hA : 1 ≤ A)
    {k : AbsoluteValue K ℝ → ι}
    (hI : ∀ w : InfinitePlace K, w D ≤ A * Q ^ c w.1 (k w.1))
    (hF : ∀ w ∈ S₀, w D ≤ A * Q ^ c w.1 (k w.1))
    (hO : ∀ w : FinitePlace K, w ∉ S₀ → w D ≤ 1) :
    (1 : ℝ) ≤ A ^ (Height.totalWeight K + #S₀) * Q ^ weightAt S₀ c k := by
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hpf := NumberField.prod_abs_eq_one hD
  have h1 : (∏ w : InfinitePlace K, w D ^ w.mult)
      ≤ ∏ w : InfinitePlace K, (A * Q ^ c w.1 (k w.1)) ^ w.mult :=
    Finset.prod_le_prod₀ (fun w _ ↦ pow_nonneg (w.1.nonneg _) _)
      fun w _ ↦ pow_le_pow_left₀ (w.1.nonneg _) (hI w) _
  have h2 : (∏ᶠ w : FinitePlace K, w D)
      ≤ ∏ w ∈ S₀, (A * Q ^ c w.1 (k w.1)) ^ (fun _ ↦ 1 : FinitePlace K → ℕ) w := by
    simp only [pow_one]
    refine le_trans (finprod_le_prod_of_le_one_outside S₀ (fun w ↦ w.1.nonneg _) hO
      (FinitePlace.hasFiniteMulSupport hD)) ?_
    exact Finset.prod_le_prod₀ (fun w _ ↦ w.1.nonneg _) fun w hw ↦ hF w hw
  have h3 : (1 : ℝ) ≤ (∏ w : InfinitePlace K, (A * Q ^ c w.1 (k w.1)) ^ w.mult)
      * ∏ w ∈ S₀, (A * Q ^ c w.1 (k w.1)) ^ (fun _ ↦ 1 : FinitePlace K → ℕ) w := by
    rw [← hpf]
    exact mul_le_mul h1 h2 (finprod_nonneg fun w ↦ w.1.nonneg _)
      (Finset.prod_nonneg fun w _ ↦ pow_nonneg (by positivity) _)
  refine le_trans h3 (le_of_eq ?_)
  rw [prod_mul_rpow_pow hQ0 univ (fun w : InfinitePlace K ↦ c w.1 (k w.1)) (fun w ↦ w.mult),
    prod_mul_rpow_pow hQ0 S₀ (fun w : FinitePlace K ↦ c w.1 (k w.1)) (fun _ ↦ 1),
    mul_mul_mul_comm, ← pow_add, ← Real.rpow_add hQ0]
  refine congrArg₂ _ (congrArg _ ?_) (congrArg _ ?_)
  · rw [← NumberField.totalWeight_eq_sum_mult K, Finset.sum_const, smul_eq_mul, mul_one]
  · rw [weightAt]
    simp only [Nat.cast_one, mul_one]
    exact congrArg₂ _ (Finset.sum_congr rfl fun w _ ↦ by ring) rfl

variable {n : ℕ} [LinearOrder ι]

omit [NumberField K] in
/-- **The normal vector of a hyperplane is supported by the pattern of the forms.** If `V` is
spanned by `y`, has normal vector `ζ` and `l` is an independent system of forms, then `ζ` lies in
the span of the coefficient vectors of the forms `l i` for which the transformed Plücker
coordinate omitting `i` does not vanish. -/
theorem mem_span_vec_of_normal {V : Submodule K (ι → K)} {y : Fin n → ι → K}
    (hyli : LinearIndependent K y) (hyspan : Submodule.span K (Set.range y) = V)
    (hlk : 1 + n = Fintype.card ι) {ζ : ι → K} (hker : ∀ x, x ∈ V ↔ ζ ⬝ᵥ x = 0)
    {l : ι → Dual K (ι → K)} (hl : LinearIndependent K l) (T : Finset ι)
    (hT : ∀ i, i ∈ T ↔
      plucker n (fun j i' ↦ l i' (y j)) (Set.powersetCard.omitOne hlk i) ≠ 0) :
    ζ ∈ Submodule.span K (Set.range fun i : {i : ι // i ∈ T} ↦ (l i.1).vec) := by
  classical
  have hinj : Function.Injective (LinearMap.pi l) := by
    obtain ⟨e, he⟩ := LinearMap.exists_inverse_forms hl
    exact fun x x' hx ↦ funext fun i ↦ by
      rw [← he x i, ← he x' i]
      exact congrArg (e i) hx
  have hy'li : LinearIndependent K (fun j i' ↦ l i' (y j)) := by
    have : (fun j ↦ (fun i' ↦ l i' (y j))) = (LinearMap.pi l) ∘ y := rfl
    rw [this]
    exact hyli.map' (LinearMap.pi l) (LinearMap.ker_eq_bot.mpr hinj)
  obtain ⟨d, hd0, hdker, hdsupp⟩ := Submodule.exists_normal hy'li rfl hlk
  set ζ' : ι → K := ∑ i, d i • (l i).vec with hζ'def
  have hζ'dot : ∀ x : ι → K, ζ' ⬝ᵥ x = d ⬝ᵥ (LinearMap.pi l x) := by
    intro x
    rw [hζ'def, _root_.sum_dotProduct, dotProduct]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [smul_dotProduct, smul_eq_mul, Module.Dual.vec_dotProduct]
      rfl
  have hmapV : Submodule.span K (Set.range (fun j i' ↦ l i' (y j) : Fin n → ι → K))
      = Submodule.map (LinearMap.pi l) V := by
    rw [← hyspan, ← Submodule.span_image, ← Set.range_comp]
    rfl
  have hker' : ∀ x : ι → K, ζ' ⬝ᵥ x = 0 ↔ x ∈ V := by
    intro x
    rw [hζ'dot, ← hdker, hmapV]
    constructor
    · rintro ⟨z, hz, hzx⟩
      rwa [hinj hzx] at hz
    · exact fun hx ↦ ⟨x, hx, rfl⟩
  have hζ'0 : ζ' ≠ 0 := by
    intro h
    have hV : V = ⊤ := by
      refine eq_top_iff.mpr fun x _ ↦ (hker' x).mp ?_
      rw [h]
      simp
    have h1 : Module.finrank K V = n := by
      rw [← hyspan]
      exact (finrank_span_eq_card hyli).trans (Fintype.card_fin n)
    rw [hV, finrank_top, finrank_fintype_fun_eq_card] at h1
    omega
  obtain ⟨μ, hμ⟩ := exists_smul_eq_of_forall_dotProduct_eq_zero hζ'0
    fun x hx ↦ (hker x).mp ((hker' x).mp hx)
  refine (Submodule.mem_span_range_iff_exists_fun K).mpr ⟨fun i ↦ μ * d i.1, ?_⟩
  rw [hμ, hζ'def, Finset.smul_sum]
  rw [Finset.sum_coe_sort T (fun i ↦ (μ * d i) • (l i).vec)]
  refine (Finset.sum_subset (Finset.subset_univ T) fun i _ hi ↦ ?_).trans
    (Finset.sum_congr rfl fun i _ ↦ by rw [smul_smul])
  rw [(hdsupp i).mp (not_not.mp (fun hc ↦ hi ((hT i).mpr hc))), mul_zero, zero_smul]

variable [Nonempty ι] {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}

/-- The subspace of vectors carried by a pattern: at each place of `S`, the span of the
coefficient vectors of the forms indexed by the pattern. -/
def patternSpace (S₀ : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (p : (InfinitePlace K → Finset ι) × ({w : FinitePlace K // w ∈ S₀} → Finset ι)) :
    Submodule K (ι → K) :=
  (⨅ w : InfinitePlace K,
      Submodule.span K (Set.range fun i : {i : ι // i ∈ p.1 w} ↦ (L w.1 i.1).vec))
    ⊓ ⨅ w : {w : FinitePlace K // w ∈ S₀},
      Submodule.span K (Set.range fun i : {i : ι // i ∈ p.2 w} ↦ (L w.1.1 i.1).vec)

/-- **A vector of a pattern space is a bounded combination of the forms it is carried by.** -/
theorem exists_one_le_forall_apply_dotProduct_le
    (p : (InfinitePlace K → Finset ι) × ({w : FinitePlace K // w ∈ S₀} → Finset ι))
    {ζ : ι → K} (hζ : ζ ∈ patternSpace S₀ L p) :
    ∃ A : ℝ, 1 ≤ A ∧
      (∀ (w : InfinitePlace K) (x : ι → K) (b : ℝ), 0 ≤ b →
        (∀ i ∈ p.1 w, w (L w.1 i x) ≤ b) → w (ζ ⬝ᵥ x) ≤ A * b) ∧
      ∀ (w : {w : FinitePlace K // w ∈ S₀}) (x : ι → K) (b : ℝ), 0 ≤ b →
        (∀ i ∈ p.2 w, w.1.1 (L w.1.1 i x) ≤ b) → w.1.1 (ζ ⬝ᵥ x) ≤ A * b := by
  classical
  choose βI hβI using fun w : InfinitePlace K ↦
    (Submodule.mem_span_range_iff_exists_fun K).mp (Submodule.mem_iInf _ |>.mp hζ.1 w)
  choose βF hβF using fun w : {w : FinitePlace K // w ∈ S₀} ↦
    (Submodule.mem_span_range_iff_exists_fun K).mp (Submodule.mem_iInf _ |>.mp hζ.2 w)
  obtain ⟨A₁, hA₁, hA₁le⟩ := Finset.exists_one_le_forall_le
    (univ : Finset ((w : InfinitePlace K) × {i : ι // i ∈ p.1 w}))
    fun q ↦ q.1 (βI q.1 q.2)
  obtain ⟨A₂, hA₂, hA₂le⟩ := Finset.exists_one_le_forall_le
    (univ : Finset ((w : {w : FinitePlace K // w ∈ S₀}) × {i : ι // i ∈ p.2 w}))
    fun q ↦ q.1.1.1 (βF q.1 q.2)
  have hdotI : ∀ (w : InfinitePlace K) (x : ι → K),
      ζ ⬝ᵥ x = ∑ i : {i : ι // i ∈ p.1 w}, βI w i * L w.1 i.1 x := by
    intro w x
    rw [← hβI w, _root_.sum_dotProduct]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [smul_dotProduct, smul_eq_mul, Module.Dual.vec_dotProduct]
  have hdotF : ∀ (w : {w : FinitePlace K // w ∈ S₀}) (x : ι → K),
      ζ ⬝ᵥ x = ∑ i : {i : ι // i ∈ p.2 w}, βF w i * L w.1.1 i.1 x := by
    intro w x
    rw [← hβF w, _root_.sum_dotProduct]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [smul_dotProduct, smul_eq_mul, Module.Dual.vec_dotProduct]
  have hcard1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  have hA₁0 : (0 : ℝ) ≤ A₁ := by linarith
  have hA₂0 : (0 : ℝ) ≤ A₂ := by linarith
  have hprod : (1 : ℝ) ≤ (Fintype.card ι : ℝ) * (A₁ * A₂) := by
    have h12 : (1 : ℝ) ≤ A₁ * A₂ := by
      calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
        _ ≤ A₁ * A₂ := mul_le_mul hA₁ hA₂ zero_le_one hA₁0
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ (Fintype.card ι : ℝ) * (A₁ * A₂) :=
        mul_le_mul hcard1 h12 zero_le_one (by linarith)
  refine ⟨(Fintype.card ι : ℝ) * (A₁ * A₂), hprod, fun w x b hb hx ↦ ?_, fun w x b hb hx ↦ ?_⟩
  · rw [hdotI w x]
    refine le_trans (AbsoluteValue.apply_sum_le_of_le w.1 _ _ (b := A₁ * b) fun i _ ↦ ?_) ?_
    · rw [map_mul]
      exact mul_le_mul (hA₁le ⟨w, i⟩ (mem_univ _)) (hx i.1 i.2) (w.1.nonneg _) hA₁0
    · have hcard : ((#(univ : Finset {i : ι // i ∈ p.1 w}) : ℝ)) ≤ (Fintype.card ι : ℝ) := by
        rw [Finset.card_univ, Fintype.card_coe]
        exact_mod_cast Finset.card_le_univ (p.1 w)
      have h3 : (#(univ : Finset {i : ι // i ∈ p.1 w}) : ℝ) * A₁
          ≤ (Fintype.card ι : ℝ) * (A₁ * A₂) :=
        le_trans (mul_le_mul_of_nonneg_right hcard hA₁0)
          (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hA₁0 hA₂) (Nat.cast_nonneg _))
      calc (#(univ : Finset {i : ι // i ∈ p.1 w}) : ℝ) * (A₁ * b)
          = ((#(univ : Finset {i : ι // i ∈ p.1 w}) : ℝ) * A₁) * b := by ring
        _ ≤ ((Fintype.card ι : ℝ) * (A₁ * A₂)) * b := mul_le_mul_of_nonneg_right h3 hb
  · rw [hdotF w x]
    refine le_trans (AbsoluteValue.apply_sum_le_of_le_of_isNonarchimedean
      (fun a b' ↦ w.1.add_le a b') _ _ (b := A₂ * b) (mul_nonneg hA₂0 hb) fun i _ ↦ ?_) ?_
    · rw [map_mul]
      exact mul_le_mul (hA₂le ⟨w, i⟩ (mem_univ _)) (hx i.1 i.2) (w.1.1.nonneg _) hA₂0
    · have h3 : A₂ ≤ (Fintype.card ι : ℝ) * (A₁ * A₂) := by
        calc A₂ = 1 * A₂ := (one_mul _).symm
          _ ≤ ((Fintype.card ι : ℝ) * A₁) * A₂ :=
            mul_le_mul_of_nonneg_right
              (le_trans hcard1 (le_mul_of_one_le_right (by linarith) hA₁)) hA₂0
          _ = (Fintype.card ι : ℝ) * (A₁ * A₂) := by ring
      exact mul_le_mul_of_nonneg_right h3 hb

/-- **The exceptional subspaces** (Bombieri–Gubler, Lemma 7.5.21). There is a finite set of
subspaces, depending only on the forms and on `S`, and a constant `C₄`, such that whenever the
weight of the exponents along the largest surviving index at each place is below `-ε/4` and
`log Q ≥ C₄ / ε`, the span of a basis of the domain is one of them. -/
theorem exists_finite_forall_mem_of_weightAt_lt {n : ℕ} (hlk : 1 + n = Fintype.card ι)
    (hLinf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLfin : ∀ w ∈ S₀, LinearIndependent K (L w.1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (𝒲 : Set (Submodule K (ι → K))) (C₄ : ℝ), 𝒲.Finite ∧
      ∀ Q : ℝ, 1 ≤ Q → C₄ / ε ≤ Real.log Q →
      ∀ y : Fin n → ι → K, LinearIndependent K y →
        (∀ j, y j ∈ approxDomain S₀ L c Q) →
        ∀ k : AbsoluteValue K ℝ → ι,
          (∀ (w : InfinitePlace K) (i : ι),
             plucker n (fun j i' ↦ L w.1 i' (y j)) (Set.powersetCard.omitOne hlk i) ≠ 0 →
             c w.1 i ≤ c w.1 (k w.1)) →
          (∀ w ∈ S₀, ∀ i : ι,
             plucker n (fun j i' ↦ L w.1 i' (y j)) (Set.powersetCard.omitOne hlk i) ≠ 0 →
             c w.1 i ≤ c w.1 (k w.1)) →
          weightAt S₀ c k < -ε / 4 →
          Submodule.span K (Set.range y) ∈ 𝒲 := by
  classical
  have hchoice : ∀ p : (InfinitePlace K → Finset ι) × ({w : FinitePlace K // w ∈ S₀} → Finset ι),
      ∃ (ζ : ι → K) (A : ℝ), 1 ≤ A ∧
      ((∃ ξ ∈ patternSpace S₀ L p, ξ ≠ 0) →
        (ζ ≠ 0 ∧ (∀ (w : FinitePlace K) (i : ι), w (ζ i) ≤ 1) ∧
          (∀ (w : InfinitePlace K) (x : ι → K) (b : ℝ), 0 ≤ b →
             (∀ i ∈ p.1 w, w (L w.1 i x) ≤ b) → w (ζ ⬝ᵥ x) ≤ A * b) ∧
          ∀ (w : {w : FinitePlace K // w ∈ S₀}) (x : ι → K) (b : ℝ), 0 ≤ b →
             (∀ i ∈ p.2 w, w.1.1 (L w.1.1 i x) ≤ b) → w.1.1 (ζ ⬝ᵥ x) ≤ A * b)) := by
    intro p
    by_cases h : ∃ ξ ∈ patternSpace S₀ L p, ξ ≠ 0
    · obtain ⟨ξ, hξU, hξ0⟩ := h
      obtain ⟨lam, hlam0, hlam⟩ := NumberField.exists_smul_apply_le_one ξ
      have hζU : lam • ξ ∈ patternSpace S₀ L p := Submodule.smul_mem _ _ hξU
      obtain ⟨A, hA1, hAI, hAF⟩ := exists_one_le_forall_apply_dotProduct_le p hζU
      exact ⟨lam • ξ, A, hA1, fun _ ↦ ⟨smul_ne_zero hlam0 hξ0,
        fun w i ↦ by simpa [Pi.smul_apply, smul_eq_mul] using hlam w i, hAI, hAF⟩⟩
    · exact ⟨0, 1, le_rfl, fun hc ↦ absurd hc h⟩
  choose ζ A hA1 hdata using hchoice
  obtain ⟨A₀, hA₀1, hA₀⟩ := Finset.exists_one_le_forall_le univ A
  set m : ℕ := Height.totalWeight K + #S₀ with hm
  refine ⟨Set.range fun p ↦ LinearMap.ker (Module.piEquiv ι K K (ζ p)),
    4 * (m : ℝ) * Real.log A₀ + 1, Set.finite_range _, ?_⟩
  intro Q hQ hQlarge y hyli hy k hkI hkF hbad
  have hQ0 : (0 : ℝ) < Q := by linarith
  set T : AbsoluteValue K ℝ → Finset ι := fun v ↦
    univ.filter fun i ↦ plucker n (fun j i' ↦ L v i' (y j))
      (Set.powersetCard.omitOne hlk i) ≠ 0 with hT
  set p₀ : (InfinitePlace K → Finset ι) × ({w : FinitePlace K // w ∈ S₀} → Finset ι) :=
    (fun w ↦ T w.1, fun w ↦ T w.1.1) with hp₀
  obtain ⟨ζQ, hζQ0, hζQker, -⟩ := Submodule.exists_normal hyli rfl hlk
  have hmemT : ∀ (v : AbsoluteValue K ℝ) (i : ι), i ∈ T v ↔
      plucker n (fun j i' ↦ L v i' (y j)) (Set.powersetCard.omitOne hlk i) ≠ 0 := by
    intro v i
    rw [hT]
    simp
  have hζQU : ζQ ∈ patternSpace S₀ L p₀ := by
    refine ⟨Submodule.mem_iInf _ |>.mpr fun w ↦ ?_, Submodule.mem_iInf _ |>.mpr fun w ↦ ?_⟩
    · exact mem_span_vec_of_normal hyli rfl hlk hζQker (hLinf w) (T w.1) (hmemT w.1)
    · exact mem_span_vec_of_normal hyli rfl hlk hζQker (hLfin w.1 w.2) (T w.1.1) (hmemT w.1.1)
  obtain ⟨hζ0, hζint, hζI, hζF⟩ := hdata p₀ ⟨ζQ, hζQU, hζQ0⟩
  have hvanish : ∀ j, ζ p₀ ⬝ᵥ y j = 0 := by
    intro j
    by_contra hne
    have hI : ∀ w : InfinitePlace K, w (ζ p₀ ⬝ᵥ y j) ≤ A₀ * Q ^ c w.1 (k w.1) := by
      intro w
      refine le_trans (hζI w (y j) (Q ^ c w.1 (k w.1))
        (Real.rpow_nonneg hQ0.le _) fun i hi ↦ ?_) ?_
      · exact le_trans ((hy j).1 w i)
          (Real.rpow_le_rpow_of_exponent_le hQ (hkI w i ((hmemT w.1 i).mp hi)))
      · exact mul_le_mul_of_nonneg_right (hA₀ p₀ (mem_univ _)) (Real.rpow_nonneg hQ0.le _)
    have hF : ∀ w ∈ S₀, w (ζ p₀ ⬝ᵥ y j) ≤ A₀ * Q ^ c w.1 (k w.1) := by
      intro w hw
      refine le_trans (hζF ⟨w, hw⟩ (y j) (Q ^ c w.1 (k w.1))
        (Real.rpow_nonneg hQ0.le _) fun i hi ↦ ?_) ?_
      · exact le_trans ((hy j).2.1 w hw i)
          (Real.rpow_le_rpow_of_exponent_le hQ (hkF w hw i ((hmemT w.1 i).mp hi)))
      · exact mul_le_mul_of_nonneg_right (hA₀ p₀ (mem_univ _)) (Real.rpow_nonneg hQ0.le _)
    have hO : ∀ w : FinitePlace K, w ∉ S₀ → w (ζ p₀ ⬝ᵥ y j) ≤ 1 := by
      intro w hw
      rw [dotProduct]
      refine AbsoluteValue.apply_sum_le_of_le_of_isNonarchimedean (fun a b ↦ w.add_le a b)
        univ _ zero_le_one fun i _ ↦ ?_
      rw [map_mul]
      have hmul := mul_le_mul (hζint w i) ((hy j).2.2 w hw i) (w.1.nonneg _) zero_le_one
      rwa [one_mul] at hmul
    have hone := one_le_mul_rpow_weightAt (c := c) hQ hne hA₀1 hI hF hO
    have hstep : Q ^ weightAt S₀ c k ≤ Q ^ (-ε / 4) :=
      Real.rpow_le_rpow_of_exponent_le hQ hbad.le
    have hApos : (0 : ℝ) < (A₀ : ℝ) ^ m := pow_pos (by linarith) _
    have h2 : (1 : ℝ) ≤ A₀ ^ m * Q ^ (-ε / 4) :=
      le_trans hone (mul_le_mul_of_nonneg_left hstep hApos.le)
    have h3 : Q ^ (ε / 4) ≤ A₀ ^ m := by
      rw [show (-ε / 4 : ℝ) = -(ε / 4) by ring, Real.rpow_neg hQ0.le] at h2
      have hp : (0 : ℝ) < Q ^ (ε / 4) := Real.rpow_pos_of_pos hQ0 _
      have hmul := mul_le_mul_of_nonneg_right h2 hp.le
      rwa [one_mul, mul_assoc, inv_mul_cancel₀ hp.ne', mul_one] at hmul
    have h4 : (ε / 4) * Real.log Q ≤ (m : ℝ) * Real.log A₀ := by
      have := Real.log_le_log (Real.rpow_pos_of_pos hQ0 (ε / 4)) h3
      rwa [Real.log_rpow hQ0, Real.log_pow] at this
    have hlogA : (0 : ℝ) ≤ Real.log A₀ := Real.log_nonneg hA₀1
    have h5 : (4 * (m : ℝ) * Real.log A₀ + 1) / ε ≤ Real.log Q := hQlarge
    rw [div_le_iff₀ hε] at h5
    nlinarith
  have hVrank : Module.finrank K (Submodule.span K (Set.range y)) = n :=
    (finrank_span_eq_card hyli).trans (Fintype.card_fin n)
  have hle : Submodule.span K (Set.range y) ≤ LinearMap.ker (Module.piEquiv ι K K (ζ p₀)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Module.piEquiv_apply_apply, smul_eq_mul]
    have := hvanish j
    rw [dotProduct_comm] at this
    simpa [dotProduct] using this
  have hlt : Module.finrank K (LinearMap.ker (Module.piEquiv ι K K (ζ p₀))) < Fintype.card ι := by
    have hne : Module.piEquiv ι K K (ζ p₀) ≠ 0 := by
      simpa using (Module.piEquiv ι K K).map_eq_zero_iff.not.mpr hζ0
    have := Submodule.finrank_lt (K := K) (V := ι → K)
      (s := LinearMap.ker (Module.piEquiv ι K K (ζ p₀))) (by rwa [Ne, LinearMap.ker_eq_top])
    rwa [finrank_fintype_fun_eq_card] at this
  exact ⟨p₀, (Submodule.eq_of_le_of_finrank_le hle (by rw [hVrank]; omega)).symm⟩

omit [NumberField K] [Nonempty ι] in
/-- Every `n`-subset of an `(n+1)`-element index type omits exactly one index. -/
theorem _root_.Set.powersetCard.omitOne_surjective {n : ℕ} (hlk : 1 + n = Fintype.card ι) :
    Function.Surjective (Set.powersetCard.omitOne (ι := ι) hlk) := fun s ↦
  ⟨Set.powersetCard.ofSingleton.symm (Set.powersetCard.compl hlk s), by
    rw [Set.powersetCard.omitOne, Equiv.apply_symm_apply, Equiv.symm_apply_apply]⟩

/-- **The height of `V(Q)` and the exceptional subspaces** (Bombieri–Gubler, Lemma 7.5.21). For
exponents of weight at most `-ε/2` there are a finite set `𝒲` of subspaces and constants `C₄`,
`C₅`, `C₆`, all independent of `Q`, such that for every level `Q` with `log Q ≥ C₄ / ε` at which
the approximation domain has rank `n`, either its span is one of the exceptional subspaces or its
height is between a positive multiple of `ε log Q` and a multiple of `log Q`. -/
theorem exists_finite_forall_logHeight_approxSpan {n : ℕ} (hlk : 1 + n = Fintype.card ι)
    (hLinf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLfin : ∀ w ∈ S₀, LinearIndependent K (L w.1))
    {ε : ℝ} (hε : 0 < ε) (hweight : approxWeight S₀ c ≤ -ε / 2) :
    ∃ (𝒲 : Set (Submodule K (ι → K))) (C₄ C₅ C₆ : ℝ), 𝒲.Finite ∧
      ∀ Q : ℝ, 1 ≤ Q → C₄ / ε ≤ Real.log Q →
        Module.finrank K (approxSpan S₀ L c Q) = n →
          approxSpan S₀ L c Q ∈ 𝒲 ∨
            (ε * Real.log Q / (4 * (Fintype.card (InfinitePlace K) + #S₀ : ℕ))
                  - C₅ ≤ (approxSpan S₀ L c Q).logHeight ∧
              (approxSpan S₀ L c Q).logHeight
                ≤ (n : ℝ) * (∑ w : InfinitePlace K, (w.mult : ℝ) * cMax c w.1
                    + ∑ w ∈ S₀, cMax c w.1) * Real.log Q + C₆) := by
  classical
  obtain ⟨𝒲, C₄, h𝒲fin, hexc⟩ := exists_finite_forall_mem_of_weightAt_lt (c := c) hlk hLinf hLfin hε
  obtain ⟨C₆, hC₆1, hC₆⟩ := exists_one_le_forall_mulHeight_plucker_le (c := c) hLinf hLfin
  obtain ⟨κ, hκ0, hκ⟩ := exists_pos_forall_prod_le (c := c) hlk hLinf hLfin
  set NS : ℕ := Fintype.card (InfinitePlace K) + #S₀ with hNS
  have hNS1 : 1 ≤ NS := by
    have : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
    omega
  refine ⟨𝒲, C₄, |(NS : ℝ) * Real.log κ⁻¹
      + (Height.totalWeight K : ℝ) * Real.log n.factorial|, Real.log C₆, h𝒲fin, ?_⟩
  intro Q hQ hQlarge hrank
  have hQ0 : (0 : ℝ) < Q := by linarith
  obtain ⟨y, hymem, hyli, hyspan⟩ :=
    Submodule.exists_linearIndependent_fin (s := approxDomain S₀ L c Q) (n := n) hrank
  have hVeq : Submodule.span K (Set.range y) = approxSpan S₀ L c Q := hyspan
  have hHeq : (approxSpan S₀ L c Q).logHeight = Real.log (Height.mulHeight (plucker n y)) := by
    rw [← hVeq, Submodule.logHeight_eq_log_mulHeight, Submodule.mulHeight_span_range hyli]
  set H := Height.mulHeight (plucker n y) with hHdef
  have hH1 : 1 ≤ H := Height.one_le_mulHeight _
  have hH0 : (0 : ℝ) < H := by linarith
  -- the upper bound
  have hupper : (approxSpan S₀ L c Q).logHeight
      ≤ (n : ℝ) * (∑ w : InfinitePlace K, (w.mult : ℝ) * cMax c w.1
          + ∑ w ∈ S₀, cMax c w.1) * Real.log Q + Real.log C₆ := by
    rw [hHeq]
    refine le_trans (Real.log_le_log hH0 (hC₆ Q hQ y hyli hymem)) (le_of_eq ?_)
    rw [Real.log_mul (by linarith) (by positivity), Real.log_rpow hQ0]
    ring
  -- the pattern and the maximizing index at each place
  set T : AbsoluteValue K ℝ → Finset ι := fun v ↦
    univ.filter fun i ↦ plucker n (fun j i' ↦ L v i' (y j))
      (Set.powersetCard.omitOne hlk i) ≠ 0 with hT
  have hmemT : ∀ (v : AbsoluteValue K ℝ) (i : ι), i ∈ T v ↔
      plucker n (fun j i' ↦ L v i' (y j)) (Set.powersetCard.omitOne hlk i) ≠ 0 := by
    intro v i
    rw [hT]
    simp
  have hTne : ∀ v : AbsoluteValue K ℝ, LinearIndependent K (L v) → (T v).Nonempty := by
    intro v hv
    obtain ⟨e, he⟩ := LinearMap.exists_inverse_forms hv
    have hinj : Function.Injective (LinearMap.pi (L v)) := fun x x' hx ↦
      funext fun i ↦ by rw [← he x i, ← he x' i]; exact congrArg (e i) hx
    have hy'li : LinearIndependent K (fun j i' ↦ L v i' (y j)) := by
      have hcomp : (fun j ↦ (fun i' ↦ L v i' (y j))) = (LinearMap.pi (L v)) ∘ y := rfl
      rw [hcomp]
      exact hyli.map' (LinearMap.pi (L v)) (LinearMap.ker_eq_bot.mpr hinj)
    obtain ⟨s, hs⟩ := Function.ne_iff.mp (plucker_ne_zero hy'li)
    obtain ⟨i, rfl⟩ := Set.powersetCard.omitOne_surjective hlk s
    exact ⟨i, (hmemT v i).mpr (by simpa using hs)⟩
  have hex : ∀ v : AbsoluteValue K ℝ, ∃ i : ι,
      ((T v).Nonempty → i ∈ T v) ∧ ∀ i' ∈ T v, c v i' ≤ c v i := by
    intro v
    by_cases h : (T v).Nonempty
    · obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (T v) (c v) h
      exact ⟨i, fun _ ↦ hi, hmax⟩
    · exact ⟨Classical.ofNonempty, fun hc ↦ absurd hc h, fun i' hi' ↦ absurd ⟨i', hi'⟩ h⟩
  choose k hkmem hkmax using hex
  rcases lt_or_ge (weightAt S₀ c k) (-ε / 4) with hbad | hgood
  · exact Or.inl (hVeq ▸ hexc Q hQ hQlarge y hyli hymem k
      (fun w i hi ↦ hkmax w.1 i ((hmemT w.1 i).mpr hi))
      (fun w _ i hi ↦ hkmax w.1 i ((hmemT w.1 i).mpr hi)) hbad)
  · refine Or.inr ⟨?_, hupper⟩
    have hsI : ∀ w : InfinitePlace K,
        plucker n (fun j i ↦ L w.1 i (y j)) (Set.powersetCard.omitOne hlk (k w.1)) ≠ 0 :=
      fun w ↦ (hmemT w.1 (k w.1)).mp (hkmem w.1 (hTne w.1 (hLinf w)))
    have hsF : ∀ w ∈ S₀,
        plucker n (fun j i ↦ L w.1 i (y j)) (Set.powersetCard.omitOne hlk (k w.1)) ≠ 0 :=
      fun w hw ↦ (hmemT w.1 (k w.1)).mp (hkmem w.1 (hTne w.1 (hLfin w hw)))
    have hlow := hκ y hyli hymem (fun v ↦ Set.powersetCard.omitOne hlk (k v)) hsI hsF
    have hup := prod_apply_plucker_pi_le (c := c) hlk hQ hymem k
    have hchain : κ ^ NS * H
        ≤ H ^ NS * ((n.factorial : ℝ) ^ Height.totalWeight K * Q ^ (-ε / 4)) := by
      refine le_trans hlow (mul_le_mul_of_nonneg_left (le_trans hup ?_) (pow_nonneg hH0.le _))
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ ?_) (by positivity)
      linarith
    have hfac : (1 : ℝ) ≤ (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
    have hlog := Real.log_le_log (by positivity) hchain
    rw [Real.log_mul (by positivity) (by linarith), Real.log_pow,
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_rpow hQ0] at hlog
    have hLH : (0 : ℝ) ≤ Real.log H := Real.log_nonneg hH1
    have hLn : (0 : ℝ) ≤ Real.log (n.factorial : ℝ) := Real.log_nonneg hfac
    have hNSr : (1 : ℝ) ≤ (NS : ℝ) := by exact_mod_cast hNS1
    set C₅ := |(NS : ℝ) * Real.log κ⁻¹
      + (Height.totalWeight K : ℝ) * Real.log n.factorial| with hC₅def
    have hC₅ : (NS : ℝ) * (-Real.log κ)
        + (Height.totalWeight K : ℝ) * Real.log n.factorial ≤ C₅ := by
      rw [hC₅def, ← Real.log_inv κ]
      exact le_abs_self _
    have hC₅0 : (0 : ℝ) ≤ C₅ := abs_nonneg _
    have hkey : (0 : ℝ) ≤ C₅ * ((NS : ℝ) - 1) := mul_nonneg hC₅0 (by linarith)
    rw [hHeq, div_sub' (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [hlog, hLH, hLn, hNSr, hC₅, hC₅0, hkey]

end NumberField
