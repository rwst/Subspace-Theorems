/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormSystemFamily
public import QuantitativeSubspace.RealFormInterval

/-!
# The interval form for real forms, for a set of exponents

For the systems of `QuantitativeSubspace/RealFormCount.lean` (forms in `1, α, α²` at `∞`, the
coordinates at the primes of a finite set `S`, integer points), the interval form
`Real.SubspaceIntervalWith α S n K` for a whole set `𝒞` of exponent tuples `(e, f)` at once: the
solutions of all of them above the threshold lie in at most `K` proper subspaces of `ℚⁿ`, or
`log |x|` lies in one of at most `K δ⁻² (1 + log δ⁻¹)` intervals `[s, K δ⁻¹ s)`
(`Real.SubspaceIntervalFamilyWith α S n K`). Neither count depends on `𝒞`.

The scaled forms of a system depend on `e` only through the set of `i` with `e i > 1 - δ / 2n`
(`Real.normLam`), so `𝒞` falls into at most `2ⁿ` classes with common forms, constants and
normalization; in each class EF13's Theorem 2.3 for a set of exponents
(`NumberField.exists_forall_mem_interval_of_efSystemThreshold_le_family`) gives one set of
subspaces and intervals for all members.

A set of exponents arises when the solutions are split into classes by their exponents, as in the
applications of Bugeaud–Evertse type: one interval result for all classes replaces one per class,
and saves the factor of the number of classes.

## Main definitions

* `Real.IsIntervalExponent S n δ e f`: the conditions on the exponents of
  `Real.SubspaceIntervalWith`.
* `Real.SubspaceIntervalFamilyWith α S n K`, `Real.SubspaceIntervalFamilyAt α S`: the interval
  form for a set of exponents.
* `Real.familyIntervalConst n d s t h μ`: its constant.

## Main results

* `Real.subspaceIntervalFamilyWith_of_mem`: the interval form for a set of exponents, with an
  explicit constant, for `2 ≤ n ≤ 4` and every Galois field `E ⊆ ℂ` containing `α`.
* `Real.subspaceIntervalFamilyAt_of_isAlgebraic`: for every real algebraic `α`.
* `Real.subspaceIntervalFamilyAt_zero`: the case `α = 0`.

## References

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, Theorems 2.3 and 3.3.

R. Stephan, *The Evertse–Ferretti interval result for a set of weights, and the exponent `1/2` in
three complexity bounds* (2026), Theorem 4.2.
-/

@[expose] public section

open Module Finset Height NumberField IsDedekindDomain

namespace Real

/-- **The conditions on the exponents** of `Real.SubspaceIntervalWith`: `e i ≤ 1` with equality
somewhere and `e i ≤ 1 - δ / 2n` somewhere, `f l i ≤ 0` with equality somewhere at every `l ∈ S`,
and total weight at most `-δ`. -/
def IsIntervalExponent {P : Type*} (S : Finset P) (n : ℕ) (δ : ℝ) (e : Fin n → ℝ)
    (f : P → Fin n → ℝ) : Prop :=
  (∀ i, e i ≤ 1) ∧ (∃ i, e i = 1) ∧ (∃ i, e i ≤ 1 - δ / (2 * n)) ∧
    (∀ l ∈ S, ∀ i, f l i ≤ 0) ∧ (∀ l ∈ S, ∃ i, f l i = 0) ∧ ∑ i, e i + ∑ l ∈ S, ∑ i, f l i ≤ -δ

/-- **The interval form for a set of exponents**: for the data of `Real.SubspaceIntervalWith` and
a set `𝒞` of exponent tuples `(e, f)`, there are at most `K` proper subspaces of `ℚⁿ` and at most
`K δ⁻² (1 + log δ⁻¹)` reals `s` such that, for every `(e, f) ∈ 𝒞`, every solution `x` above the
threshold `K δ⁻¹ (1 + log B + log C + log γ⁻¹)` lies in one of the subspaces or has
`s ≤ log |x| < K δ⁻¹ s` for one of the reals. -/
def SubspaceIntervalFamilyWith (α : ℝ) (S : Finset Nat.Primes) (n : ℕ) (K : ℝ) : Prop :=
  ∀ (P : Fin n → Fin n → Fin 3 → ℤ) (B : ℝ), 1 ≤ B → (∀ i k m, |(P i k m : ℝ)| ≤ B) →
    ∀ γ : ℝ, 0 < γ → γ ≤ 1 → γ ≤ |(Matrix.of fun i k ↦ quadVal α (P i k)).det| →
    ∀ C : ℝ, 1 ≤ C → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    ∀ 𝒞 : Set ((Fin n → ℝ) × (Nat.Primes → Fin n → ℝ)),
      (∀ p ∈ 𝒞, IsIntervalExponent S n δ p.1 p.2) →
    ∃ T : Finset (Submodule ℚ (Fin n → ℚ)), (#T : ℝ) ≤ K ∧ (∀ U ∈ T, U ≠ ⊤) ∧
      ∃ 𝒯 : Finset ℝ, (#𝒯 : ℝ) ≤ K * δ⁻¹ ^ 2 * (1 + log δ⁻¹) ∧
      ∀ p ∈ 𝒞, ∀ x : Fin n → ℤ, x ≠ 0 →
        (∀ i, |∑ k, quadVal α (P i k) * x k| ≤ C * (⨆ k, |(x k : ℝ)|) ^ p.1 i) →
        (∀ l ∈ S, ∀ i, ((padicNorm (l : ℕ) (x i : ℚ) : ℚ) : ℝ) ≤ (⨆ k, |(x k : ℝ)|) ^ p.2 l i) →
        K * δ⁻¹ * (1 + log B + log C + log γ⁻¹) ≤ log (⨆ k, |(x k : ℝ)|) →
        (∃ U ∈ T, (fun k ↦ (x k : ℚ)) ∈ U) ∨
          ∃ s ∈ 𝒯, s ≤ log (⨆ k, |(x k : ℝ)|) ∧ log (⨆ k, |(x k : ℝ)|) < K * δ⁻¹ * s

/-- **The interval form for a set of exponents at `∞` and the primes of `S`**:
`Real.SubspaceIntervalFamilyWith α S n K` for `2 ≤ n ≤ 4` and some `K ≥ 1`, which depends on
`α`, `S` and `n` only. -/
def SubspaceIntervalFamilyAt (α : ℝ) (S : Finset Nat.Primes) : Prop :=
  ∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∃ K : ℝ, 1 ≤ K ∧ SubspaceIntervalFamilyWith α S n K

/-- **The constant of the interval form for a set of exponents**, for `n` variables, forms over a
field of degree `d` in which `α` has height `h`, `s` finite places with `μ` the logarithm of
Minkowski's constant, and `t` places of the field above `∞` and the `s` places: the largest of the
number `2ⁿ J (nⁿ)^t efIntervalConstAt n M a` of intervals, the ratio constant `log (3M) a`, the
number `2ⁿ J` of subspaces and `Real.subspaceConst` (for the threshold), with
`J = familyCount n t`, `M = efFamilyForms (2n) d n t` and `a = 32 n (n + 1) t`. -/
noncomputable def familyIntervalConst (n d s t : ℕ) (h μ : ℝ) : ℝ :=
  max (2 ^ n * FormSystem.familyCount n t * (n ^ n) ^ t *
      efIntervalConstAt n (efFamilyForms (2 * n) d n t) (32 * n * (n + 1) * t))
    (max (Real.log (3 * efFamilyForms (2 * n) d n t) * (32 * n * (n + 1) * t))
      (max (2 ^ n * FormSystem.familyCount n t) (subspaceConst n d s h μ)))

theorem one_le_familyIntervalConst (n d s t : ℕ) (h μ : ℝ) :
    1 ≤ familyIntervalConst n d s t h μ :=
  (one_le_subspaceConst ..).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    (le_max_right _ _)))

open scoped Classical in
/-- **The interval form for a set of exponents at `∞` and finitely many finite places of `ℚ`**,
with an explicit constant (`Real.familyIntervalConst`): `Real.subspaceInterval_places_of_mem` for
a set `𝒞` of exponents. -/
theorem subspaceIntervalFamily_places_of_mem {α : ℝ} (E : IntermediateField ℚ ℂ) [IsGalois ℚ E]
    [NumberField E] (hαE : (α : ℂ) ∈ E) {n : ℕ} (hn : 2 ≤ n) (hn4 : n ≤ 4)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    let K := familyIntervalConst n (finrank ℚ E) #S (efFamilyPlaces E S)
        (log (mulHeight₁ (⟨α, hαE⟩ : E))) (log (scalarConst ℚ S))
    ∀ (P : Fin n → Fin n → Fin 3 → ℤ) (B : ℝ), 1 ≤ B → (∀ i k m, |(P i k m : ℝ)| ≤ B) →
      ∀ γ : ℝ, 0 < γ → γ ≤ 1 → γ ≤ |(Matrix.of fun i k ↦ quadVal α (P i k)).det| →
      ∀ C : ℝ, 1 ≤ C → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ 𝒞 : Set ((Fin n → ℝ) × (HeightOneSpectrum (𝓞 ℚ) → Fin n → ℝ)),
        (∀ p ∈ 𝒞, IsIntervalExponent S n δ p.1 p.2) →
      ∃ T : Finset (Submodule ℚ (Fin n → ℚ)), (#T : ℝ) ≤ K ∧ (∀ U ∈ T, U ≠ ⊤) ∧
        ∃ 𝒯 : Finset ℝ, (#𝒯 : ℝ) ≤ K * δ⁻¹ ^ 2 * (1 + log δ⁻¹) ∧
        ∀ p ∈ 𝒞, ∀ x : Fin n → ℤ, x ≠ 0 →
          (∀ i, |∑ k, quadVal α (P i k) * x k| ≤ C * (⨆ k, |(x k : ℝ)|) ^ p.1 i) →
          (∀ v ∈ S, ∀ i, FinitePlace.mk v (x i : ℚ) ≤ (⨆ k, |(x k : ℝ)|) ^ p.2 v i) →
          K * δ⁻¹ * (1 + log B + log C + log γ⁻¹) ≤ log (⨆ k, |(x k : ℝ)|) →
          (∃ U ∈ T, (fun k ↦ (x k : ℚ)) ∈ U) ∨
            ∃ s ∈ 𝒯, s ≤ log (⨆ k, |(x k : ℝ)|) ∧ log (⨆ k, |(x k : ℝ)|) < K * δ⁻¹ * s := by
  intro K P B hB hP γ hγ hγ1 hdet C hC δ hδ hδ1 𝒞 h𝒞
  set d := finrank ℚ E with hd
  set t := efFamilyPlaces E S with ht
  set M := efFamilyForms (2 * n) d n t with hMdef
  set a : ℝ := 32 * n * (n + 1) * t with ha
  set J := FormSystem.familyCount n t with hJ
  have hwInf := placeAbs_liesOver_infinitePlace E.val.toRingHom
  have hwFin : ∀ v ∈ S, (placeAbs E.val.toRingHom (FinitePlace.mk v).1).LiesOver
      (FinitePlace.mk v).1 := fun v _ ↦ placeAbs_liesOver_finitePlace _ (FinitePlace.mk v)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ht1 : 1 ≤ t := by
    have := Fintype.card_pos (α := InfinitePlace E)
    rw [ht, efFamilyPlaces]
    omega
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hM : 2 ≤ M := by rw [hMdef, efFamilyForms]; omega
  have ha1 : 1 ≤ a := by
    rw [ha]
    have h1 : (1 : ℝ) ≤ t := by exact_mod_cast ht1
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : (1 : ℝ) ≤ 32 * n * (n + 1) := by nlinarith
    exact one_le_mul_of_one_le_of_one_le h3 h1
  have hδi : 0 < δ⁻¹ := inv_pos.2 hδ
  have hl : 0 ≤ log δ⁻¹ := Real.log_nonneg ((one_le_inv₀ hδ).2 hδ1)
  -- the classes
  obtain ⟨k, hk, hklog⟩ := exists_two_pow hC hγ hγ1 n
  set pat : (Fin n → ℝ) → Finset (Fin n) := fun e ↦ univ.filter fun i ↦ 1 - δ / (2 * n) < e i
    with hpat
  set lam : Finset (Fin n) → Fin n → ℕ := fun σ i ↦ if i ∈ σ then 1 else 2 ^ k with hlamdef
  have hlam : ∀ e, normLam e δ k = lam (pat e) := fun e ↦ by
    funext i
    simp [normLam, hlamdef, hpat]
  have hspec := fun (p : (Fin n → ℝ) × (HeightOneSpectrum (𝓞 ℚ) → Fin n → ℝ)) (hp : p ∈ 𝒞) ↦
    normalized_placeForms_of_mem E hαE hn hn4 S P hB hP hγ hγ1 hdet hC p.1 p.2 hδ hδ1
      (h𝒞 p hp).1 (h𝒞 p hp).2.1 (h𝒞 p hp).2.2.1 (h𝒞 p hp).2.2.2.1 (h𝒞 p hp).2.2.2.2.1
      (h𝒞 p hp).2.2.2.2.2 hk hklog
  have hclass : ∀ σ : Finset (Fin n), ∃ T : Finset (Submodule ℚ (Fin n → ℚ)), #T ≤ J ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∃ 𝒯 : Finset ℝ,
        #𝒯 ≤ FormSystem.familyIntervalCount n t M (efFamilyDelta n t (δ / 2)) ∧
        ∀ p ∈ 𝒞, pat p.1 = σ → ∀ x : Fin n → ℤ, x ≠ 0 →
          (∀ i, |∑ k, quadVal α (P i k) * x k| ≤ C * (⨆ k, |(x k : ℝ)|) ^ p.1 i) →
          (∀ v ∈ S, ∀ i, FinitePlace.mk v (x i : ℚ) ≤ (⨆ k, |(x k : ℝ)|) ^ p.2 v i) →
          (thrConstAt n d S * (1 + 17 * d + 3 * log (mulHeight₁ (⟨α, hαE⟩ : E))) + 2 * n ^ 2) *
            δ⁻¹ * (1 + log B + log C + log γ⁻¹) ≤ log (⨆ k, |(x k : ℝ)|) →
          (∃ U ∈ T, (fun k ↦ (x k : ℚ)) ∈ U) ∨ ∃ s ∈ 𝒯,
            s ≤ log (mulHeightAff fun j ↦ (x j : ℚ)) ∧
            log (mulHeightAff fun j ↦ (x j : ℚ)) < FormSystem.cutRatio M
              (efFamilyDelta n t (δ / 2)) * s := by
    intro σ
    set 𝒩 : Set (InfinitePlace ℚ ⊕ S → Fin n → ℝ) :=
      (fun p ↦ placeExp p.1 δ S p.2) '' {p | p ∈ 𝒞 ∧ pat p.1 = σ}
    have hN : ∀ c ∈ 𝒩, IsNormalizedSystem S (placeAbs E.val.toRingHom)
        (placeForms ⟨α, hαE⟩ (lam σ) P)
        (placeConst S (|(Matrix.of fun i j ↦ (lam σ i : ℝ) * quadVal α (P i j)).det| ^
          (n : ℝ)⁻¹))
        c (3 ^ d * (2 ^ k * B) ^ (3 * d) * mulHeight₁ (⟨α, hαE⟩ : E) ^ 3) d (2 * n) (δ / 2) := by
      rintro _ ⟨p, ⟨hp, hpσ⟩, rfl⟩
      have h := (hspec p hp).1
      rwa [hlam p.1, hpσ] at h
    obtain ⟨T, hT, hTtop, 𝒯, h𝒯, -, hmem⟩ :=
      exists_forall_mem_interval_of_efSystemThreshold_le_family (E := E) S _ hwInf hwFin 𝒩 hN
    rw [Fintype.card_fin] at hT h𝒯 hmem
    refine ⟨T, ?_, hTtop, 𝒯, ?_, fun p hp hpσ x hx hsol hfin hlarge ↦ ?_⟩
    · exact hT
    · exact h𝒯
    obtain ⟨h1, h2⟩ := (hspec p hp).2 x hx hsol hfin hlarge
    rw [hlam p.1, hpσ] at h1 h2
    exact hmem _ ⟨p, ⟨hp, hpσ⟩, rfl⟩ _ h1 h2
  choose T hT hTtop 𝒯 h𝒯 hmem using hclass
  have hδ' : efFamilyDelta n t (δ / 2) = (a * δ⁻¹)⁻¹ := by
    rw [efFamilyDelta, ha]
    field_simp
    ring
  have hδ'0 : 0 < efFamilyDelta n t (δ / 2) := by rw [hδ']; positivity
  have hδ'1 : efFamilyDelta n t (δ / 2) ≤ 1 := by
    rw [hδ', inv_le_one₀ (by positivity)]
    calc (1 : ℝ) ≤ a := ha1
      _ ≤ a * δ⁻¹ := le_mul_of_one_le_right (by linarith) ((one_le_inv₀ hδ).2 hδ1)
  have hcount : (FormSystem.intervalCount n M (efFamilyDelta n t (δ / 2)) : ℝ) ≤
      efIntervalConstAt n M a * δ⁻¹ ^ 2 * (1 + log δ⁻¹) :=
    intervalCount_le_of_inv_le hn hM hδ hδ1 hδ'0 hδ'1 ha1 (by rw [hδ', inv_inv])
  have hcard : (#(univ : Finset (Finset (Fin n))) : ℝ) = 2 ^ n := by
    rw [card_univ, Fintype.card_finset, Fintype.card_fin]
    push_cast
    rfl
  refine ⟨univ.biUnion T, ?_, ?_, univ.biUnion 𝒯, ?_, fun p hp x hx hsol hfin hlarge ↦ ?_⟩
  · calc (#(univ.biUnion T) : ℝ) ≤ ∑ σ, (#(T σ) : ℝ) := by exact_mod_cast card_biUnion_le
      _ ≤ ∑ _σ : Finset (Fin n), (J : ℝ) := sum_le_sum fun σ _ ↦ by exact_mod_cast hT σ
      _ = 2 ^ n * J := by rw [sum_const, nsmul_eq_mul, hcard]
      _ ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · intro U hU
    obtain ⟨σ, -, hU⟩ := mem_biUnion.1 hU
    exact hTtop σ U hU
  · calc (#(univ.biUnion 𝒯) : ℝ) ≤ ∑ σ, (#(𝒯 σ) : ℝ) := by exact_mod_cast card_biUnion_le
      _ ≤ ∑ _σ : Finset (Fin n),
          (J * ((n ^ n) ^ t * FormSystem.intervalCount n M (efFamilyDelta n t (δ / 2))) : ℝ) :=
          sum_le_sum fun σ _ ↦ by exact_mod_cast h𝒯 σ
      _ = 2 ^ n * J * (n ^ n) ^ t *
          FormSystem.intervalCount n M (efFamilyDelta n t (δ / 2)) := by
          rw [sum_const, nsmul_eq_mul, hcard]
          ring
      _ ≤ 2 ^ n * J * (n ^ n) ^ t * (efIntervalConstAt n M a * δ⁻¹ ^ 2 * (1 + log δ⁻¹)) := by
          gcongr
      _ = 2 ^ n * J * (n ^ n) ^ t * efIntervalConstAt n M a * (δ⁻¹ ^ 2 * (1 + log δ⁻¹)) := by
          ring
      _ ≤ K * (δ⁻¹ ^ 2 * (1 + log δ⁻¹)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact le_max_left _ _
      _ = K * δ⁻¹ ^ 2 * (1 + log δ⁻¹) := by ring
  have hΞ : 0 ≤ δ⁻¹ * (1 + log B + log C + log γ⁻¹) := by
    have := Real.log_nonneg hB
    have := Real.log_nonneg hC
    have := Real.log_nonneg ((one_le_inv₀ hγ).2 hγ1)
    positivity
  have hthr : thrConstAt n d S * (1 + 17 * d + 3 * log (mulHeight₁ (⟨α, hαE⟩ : E))) +
      2 * n ^ 2 ≤ K :=
    (thrConst_le_subspaceConst ..).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _)))
  rcases hmem (pat p.1) p hp rfl x hx hsol hfin (le_trans (by
    rw [mul_assoc, mul_assoc K]
    exact mul_le_mul_of_nonneg_right hthr hΞ) hlarge) with hU | ⟨s, hs, hs1, hs2⟩
  · obtain ⟨U, hU, hxU⟩ := hU
    exact .inl ⟨U, mem_biUnion.2 ⟨_, mem_univ _, hU⟩, hxU⟩
  refine .inr ⟨s, mem_biUnion.2 ⟨_, mem_univ _, hs⟩, ?_, ?_⟩ <;>
    rw [Height.mulHeightAff_intCast hx] at hs1 hs2
  · exact hs1
  · have hX : 0 ≤ log (⨆ k, |(x k : ℝ)|) := by
      refine Real.log_nonneg ?_
      rw [← Height.mulHeightAff_intCast hx]
      exact one_le_mulHeightAff _
    have hρ := FormSystem.one_lt_cutRatio hM hδ'0 hδ'1
    have hs0 : 0 ≤ s := by
      by_contra hs0
      push Not at hs0
      nlinarith
    refine hs2.trans_le ?_
    have hr : FormSystem.cutRatio M (efFamilyDelta n t (δ / 2)) ≤
        Real.log (3 * M) * a * δ⁻¹ := by
      rw [FormSystem.cutRatio, hδ', div_inv_eq_mul]
      ring_nf
      exact le_rfl
    have hK : Real.log (3 * M) * a ≤ K :=
      (le_max_left _ _).trans (le_max_right _ _)
    calc FormSystem.cutRatio M (efFamilyDelta n t (δ / 2)) * s ≤
          Real.log (3 * M) * a * δ⁻¹ * s := by gcongr
      _ ≤ K * δ⁻¹ * s := by gcongr

open scoped Classical in
/-- **The interval form of Evertse–Ferretti 2013 for a set of exponents, with an explicit
constant**: `Real.subspaceIntervalWith_of_mem` for a set `𝒞` of exponent tuples, with the constant
`Real.familyIntervalConst` of `n`, the degree `d` of a Galois field `E ⊆ ℂ` containing `α`, `#S`,
the number `t` of places of `E` above `∞` and the primes of `S`, the height `log H(α)` of `α` in
`E` and `log 2 + ∑_{l ∈ S} log l`. -/
theorem subspaceIntervalFamilyWith_of_mem {α : ℝ} (E : IntermediateField ℚ ℂ) [IsGalois ℚ E]
    [NumberField E] (hαE : (α : ℂ) ∈ E) (S : Finset Nat.Primes) {n : ℕ} (hn : 2 ≤ n)
    (hn4 : n ≤ 4) :
    SubspaceIntervalFamilyWith α S n (familyIntervalConst n (finrank ℚ E) #S
      (efFamilyPlaces E (S.image primeIdeal))
      (log (mulHeight₁ (⟨α, hαE⟩ : E))) (log 2 + ∑ l ∈ S, log (l : ℕ))) := by
  classical
  have hT := subspaceIntervalFamily_places_of_mem E hαE hn hn4 (S.image primeIdeal)
  rw [card_image_primeIdeal, log_scalarConst_image_primeIdeal] at hT
  intro P B hB hP γ hγ hγ1 hdet C hC δ hδ hδ1 𝒞 h𝒞
  set g : (Nat.Primes → Fin n → ℝ) → HeightOneSpectrum (𝓞 ℚ) → Fin n → ℝ :=
    fun f v ↦ f (Function.invFun primeIdeal v) with hg
  have hg' (f : Nat.Primes → Fin n → ℝ) (l : Nat.Primes) : g f (primeIdeal l) = f l := by
    simp only [hg, Function.leftInverse_invFun primeIdeal_injective l]
  set 𝒞' := (fun p : (Fin n → ℝ) × (Nat.Primes → Fin n → ℝ) ↦ (p.1, g p.2)) '' 𝒞
  obtain ⟨T, hT1, hTtop, 𝒯, hcard, hmem⟩ := hT P B hB hP γ hγ hγ1 hdet C hC δ hδ hδ1 𝒞' (by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h𝒞 p hp
    refine ⟨h1, h2, h3, fun v hv ↦ ?_, fun v hv ↦ ?_, ?_⟩
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hv
      dsimp only
      rw [hg']; exact h4 l hl
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hv
      dsimp only
      rw [hg']; exact h5 l hl
    · have hsum : ∑ v ∈ S.image primeIdeal, ∑ i, g p.2 v i = ∑ l ∈ S, ∑ i, p.2 l i := by
        rw [Finset.sum_image fun l _ l' _ h ↦ primeIdeal_injective h]
        simp only [hg']
      rwa [hsum])
  refine ⟨T, hT1, hTtop, 𝒯, hcard, fun p hp x hx hsol hfin hlarge ↦
    hmem _ ⟨p, hp, rfl⟩ x hx hsol (fun v hv i ↦ ?_) hlarge⟩
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hv
  dsimp only
  rw [hg', finitePlace_mk_primeIdeal]
  exact hfin l hl i

/-- **The interval form for a set of exponents**, for every real algebraic `α`. The forms are
taken over the Galois closure of `α` in `ℂ` (`Real.subspaceIntervalFamilyWith_of_mem`). -/
theorem subspaceIntervalFamilyAt_of_isAlgebraic {α : ℝ} (hα : IsAlgebraic ℚ α)
    (S : Finset Nat.Primes) : SubspaceIntervalFamilyAt α S := by
  intro n hn hn4
  obtain ⟨E, hgal, hfd, hmem⟩ := exists_isGalois_mem hα
  have : NumberField E := { }
  exact ⟨_, one_le_familyIntervalConst .., subspaceIntervalFamilyWith_of_mem E hmem S hn hn4⟩

/-- **The case `α = 0`** of the interval form for a set of exponents: forms with integer
coefficients, for some constant `K ≥ 1` depending on `S` and `n`. -/
theorem subspaceIntervalFamilyAt_zero (S : Finset Nat.Primes) : SubspaceIntervalFamilyAt 0 S :=
  subspaceIntervalFamilyAt_of_isAlgebraic isAlgebraic_zero S

end Real
