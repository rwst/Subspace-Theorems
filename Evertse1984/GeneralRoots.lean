/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SIntegerExtension
public import Evertse1984.EqualTerms

-- Used only inside proofs.
import DiophantineApproximation.UnitEquation
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.SplittingField.Construction

/-!
# The passage to a splitting field

Evertse proves Lemma 2 and Theorem 3 after replacing `K` by a finite extension in which the
polynomials split and which contains the characteristic roots ("no restriction", §3–4). This file
makes that step: the `S`-units of `K` map into the units of `L` for the primes above `S`
(`NumberField.map_mem_unit_iff` of `DiophantineApproximation`), and the hypotheses on `f`, `g`,
`α_i` survive the passage (divisibility of polynomials does not depend on the field, and
`K → L` is injective). Nothing is assumed to split any more.

## Main results

* `NumberField.finite_setOf_eval_div_eval_mem_unit`: **Lemma 2**.
* `NumberField.finite_setOf_powerSum_div_mem_unit`: **Theorem 3** for `α_i ∈ K`, `f_i ∈ K[X]`.
* `NumberField.finite_setOf_div_mem_unit_of_eq_powerSum`: **Theorem 3** for a sequence `u` in `K`
  whose characteristic roots and polynomials lie in an extension `L`.
* `NumberField.finite_setOf_powerSum_mem_unit`, `NumberField.finite_setOf_mem_unit_of_eq_powerSum`:
  **Corollary 3**.
* `NumberField.finite_setOf_powerSum_eq`, `NumberField.finite_setOf_eq_of_eq_powerSum`:
  **Corollary 4**.

## References

J.-H. Evertse, *On sums of `S`-units and linear recurrences*, Compositio Math. **53** (1984),
225–244, §3–4.
-/

@[expose] public section

open IsDedekindDomain Polynomial

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]

omit [NumberField K] [NumberField L] in
/-- Evaluating the image of a polynomial at the image of a point. -/
theorem eval_map_algebraMap_apply (f : K[X]) (x : K) :
    (f.map (algebraMap K L)).eval (algebraMap K L x) = algebraMap K L (f.eval x) := by
  rw [eval_map, eval₂_hom]

omit [NumberField K] [NumberField L] in
/-- **A power sum commutes with a field embedding.** -/
theorem algebraMap_powerSum {ι : Type*} [Fintype ι] (α : ι → K) (f : ι → K[X]) (k : ℕ) :
    algebraMap K L (powerSum α f k) =
      powerSum (fun i ↦ algebraMap K L (α i)) (fun i ↦ (f i).map (algebraMap K L)) k := by
  simp only [powerSum, map_sum, map_mul, map_pow]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← map_natCast (algebraMap K L), eval_map_algebraMap_apply]

omit [NumberField K] [NumberField L] in
/-- Non-degeneracy survives a field embedding. -/
theorem map_div_pow_ne_one {a b : K} {n : ℕ} (h : (a / b) ^ n ≠ 1) :
    (algebraMap K L a / algebraMap K L b) ^ n ≠ 1 := by
  rwa [← map_div₀, ← map_pow, ne_eq, map_eq_one_iff _ (algebraMap K L).injective]

variable (L) in
/-- The primes of `L` above a finite set of primes of `K`, as a `Finset`. -/
noncomputable def primesAbove (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finset (HeightOneSpectrum (𝓞 L)) :=
  (finite_preimage_under L S.finite_toSet).toFinset

theorem coe_primesAbove (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (primesAbove L S : Set (HeightOneSpectrum (𝓞 L))) =
      HeightOneSpectrum.under (𝓞 K) ⁻¹' (S : Set (HeightOneSpectrum (𝓞 K))) := by
  unfold primesAbove; exact Set.Finite.coe_toFinset _

/-- **An `S`-unit of `K` is a unit of `L` for the primes above `S`.** -/
theorem map_mem_unit_primesAbove {S : Finset (HeightOneSpectrum (𝓞 K))} {w : Kˣ}
    (hw : w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    Units.map (algebraMap K L : K →* L) w ∈
      (primesAbove L S : Set (HeightOneSpectrum (𝓞 L))).unit L := by
  rw [coe_primesAbove]; exact map_mem_unit_iff.mpr hw

/-- **The pairs of Theorem 3 in `K` are pairs of Theorem 3 in `L`.** -/
theorem subset_powerSumPairs (S : Finset (HeightOneSpectrum (𝓞 K))) {u : ℕ → K} {ι : Type*}
    [Fintype ι] {α : ι → L} {f : ι → L[X]} (hu : ∀ k, algebraMap K L (u k) = powerSum α f k) :
    {p : ℕ × ℕ | p.2 < p.1 ∧ u p.2 ≠ 0 ∧ (u p.1 = 0 ∨
      ∃ w : Kˣ, w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧ (w : K) = u p.1 / u p.2)} ⊆
      powerSumPairs (primesAbove L S) α f := by
  rintro p ⟨h1, h2, h3 | ⟨w, hw, hwe⟩⟩
  · exact ⟨h1, by rw [← hu]; exact (_root_.map_ne_zero _).mpr h2,
      Or.inl (by rw [← hu, h3, map_zero])⟩
  · refine ⟨h1, by rw [← hu]; exact (_root_.map_ne_zero _).mpr h2,
      Or.inr ⟨_, map_mem_unit_primesAbove hw, ?_⟩⟩
    simp [← hu, hwe]

/-- **Evertse's Lemma 2.** Let `f, g ∈ K[X]` be such that no shift `f(X + h)`, `h ∈ ℤ \ {0}`,
divides or is divisible by `g`, and let `0 ≤ γ < 1 / (deg f + deg g + 2)`, `β > 0`. Then only
finitely many pairs of integers `r ≠ s` with `|r - s| ≤ β |r| ^ γ` have `f(r) / g(s)` an
`S`-unit. -/
theorem finite_setOf_eval_div_eval_mem_unit (S : Finset (HeightOneSpectrum (𝓞 K))) {f g : K[X]}
    (hfg : ∀ h : ℤ, h ≠ 0 → ¬ f.comp (X + C (h : K)) ∣ g ∧ ¬ g ∣ f.comp (X + C (h : K)))
    {β γ : ℝ} (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ : γ < 1 / (f.natDegree + g.natDegree + 2)) :
    {p : ℤ × ℤ | p.1 ≠ p.2 ∧ |(p.1 : ℝ) - p.2| ≤ β * |(p.1 : ℝ)| ^ γ ∧
      ∃ u : Kˣ, u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧
        (u : K) = f.eval (p.1 : K) / g.eval (p.2 : K)}.Finite := by
  by_cases hfg0 : f * g = 0
  · refine Set.finite_empty.subset ?_
    rintro p ⟨-, -, u, -, hu⟩
    refine Units.ne_zero u ?_
    rcases mul_eq_zero.mp hfg0 with h | h <;> simp [hu, h]
  let M := (f * g).SplittingField
  have : NumberField M := NumberField.of_module_finite K M
  set φ := algebraMap K M with hφ
  have hsplit : ∀ q : K[X], q ∣ f * g → (q.map φ).Splits := fun q hq ↦
    (SplittingField.splits (f * g)).of_dvd ((Polynomial.map_ne_zero_iff φ.injective).mpr hfg0)
      (Polynomial.map_dvd _ hq)
  have hcomp : ∀ h : ℤ, (f.map φ).comp (X + C (h : M)) = (f.comp (X + C (h : K))).map φ :=
    fun h ↦ by rw [Polynomial.map_comp, Polynomial.map_add, map_X, map_C, map_intCast φ h]
  have hfg' : ∀ h : ℤ, h ≠ 0 → ¬ (f.map φ).comp (X + C (h : M)) ∣ g.map φ ∧
      ¬ g.map φ ∣ (f.map φ).comp (X + C (h : M)) := fun h hh ↦ by
    rw [hcomp, map_dvd_map', map_dvd_map']; exact hfg h hh
  have hL2 := finite_setOf_eval_div_eval_mem_unit_of_splits (primesAbove M S)
    (hsplit f (dvd_mul_right f g)) (hsplit g (dvd_mul_left g f)) hfg' hβ hγ0
    (by rwa [natDegree_map, natDegree_map])
  refine hL2.subset fun p ⟨h1, h2, u, hu, hue⟩ ↦ ⟨h1, h2, _, map_mem_unit_primesAbove hu, ?_⟩
  simp only [Units.coe_map, MonoidHom.coe_ofClass, hue, map_div₀]
  rw [← map_intCast φ, ← map_intCast φ, eval_map_algebraMap_apply, eval_map_algebraMap_apply]

omit [NumberField K] in
/-- The splitting field of `∏_i f_i`: every `f_i` splits in it. -/
theorem splits_map_splittingField_prod {ι : Type*} [Fintype ι] {f : ι → K[X]}
    (hf0 : ∀ i, f i ≠ 0) (i : ι) :
    ((f i).map (algebraMap K (∏ j, f j).SplittingField)).Splits :=
  (SplittingField.splits _).of_dvd ((Polynomial.map_ne_zero_iff (algebraMap K _).injective).mpr
    (Finset.prod_ne_zero_iff.mpr fun j _ ↦ hf0 j))
    (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))

/-- **Evertse's Theorem 3** for generalized power sums over `K`. Let `u_k = ∑_i f_i(k) α_i ^ k`
with at least two nonzero characteristic roots `α_i ∈ K`, no quotient `α_i / α_j` (`i ≠ j`) a root
of unity, and nonzero `f_i ∈ K[X]`. Then for every finite set `S` of primes only finitely many
pairs `r > s ≥ 0` have `u_s ≠ 0` and `u_r / u_s` zero or an `S`-unit. -/
theorem finite_setOf_powerSum_div_mem_unit (S : Finset (HeightOneSpectrum (𝓞 K))) {ι : Type*}
    [Fintype ι] [Nontrivial ι] {α : ι → K} {f : ι → K[X]} (hα0 : ∀ i, α i ≠ 0)
    (hnd : ∀ i j, i ≠ j → ∀ n : ℕ, 0 < n → (α i / α j) ^ n ≠ 1) (hf0 : ∀ i, f i ≠ 0) :
    (powerSumPairs S α f).Finite := by
  let M := (∏ j, f j).SplittingField
  have : NumberField M := NumberField.of_module_finite K M
  exact (finite_setOf_powerSum_div_mem_unit_of_splits (primesAbove M S)
    (fun i ↦ (_root_.map_ne_zero _).mpr (hα0 i))
    (fun i j hij n hn ↦ map_div_pow_ne_one (hnd i j hij n hn))
    (fun i ↦ (Polynomial.map_ne_zero_iff (algebraMap K M).injective).mpr (hf0 i))
    (splits_map_splittingField_prod hf0)).subset
    (subset_powerSumPairs S (algebraMap_powerSum α f))

/-- **Evertse's Theorem 3** for a sequence in `K` with characteristic roots in an extension. Let
`u : ℕ → K` be given in a number field `L ⊇ K` by `u_k = ∑_i f_i(k) α_i ^ k`, with at least two
nonzero characteristic roots `α_i ∈ L`, no quotient `α_i / α_j` (`i ≠ j`) a root of unity, and
nonzero `f_i ∈ L[X]`. Then for every finite set `S` of primes of `K` only finitely many pairs
`r > s ≥ 0` have `u_s ≠ 0` and `u_r / u_s` zero or an `S`-unit; that is,
`P_K(u_r / u_s) → ∞`. -/
theorem finite_setOf_div_mem_unit_of_eq_powerSum (S : Finset (HeightOneSpectrum (𝓞 K)))
    {u : ℕ → K} {ι : Type*} [Fintype ι] [Nontrivial ι] {α : ι → L} {f : ι → L[X]}
    (hu : ∀ k, algebraMap K L (u k) = powerSum α f k) (hα0 : ∀ i, α i ≠ 0)
    (hnd : ∀ i j, i ≠ j → ∀ n : ℕ, 0 < n → (α i / α j) ^ n ≠ 1) (hf0 : ∀ i, f i ≠ 0) :
    {p : ℕ × ℕ | p.2 < p.1 ∧ u p.2 ≠ 0 ∧ (u p.1 = 0 ∨
      ∃ w : Kˣ, w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧
        (w : K) = u p.1 / u p.2)}.Finite :=
  (finite_setOf_powerSum_div_mem_unit (primesAbove L S) hα0 hnd hf0).subset
    (subset_powerSumPairs S hu)

/-- **Evertse's Corollary 3**: `P_K(u_r) → ∞`. Under the hypotheses of Theorem 3, only finitely
many `r` have `u_r` zero or an `S`-unit. -/
theorem finite_setOf_powerSum_mem_unit (S : Finset (HeightOneSpectrum (𝓞 K))) {ι : Type*}
    [Fintype ι] [Nontrivial ι] {α : ι → K} {f : ι → K[X]} (hα0 : ∀ i, α i ≠ 0)
    (hnd : ∀ i j, i ≠ j → ∀ n : ℕ, 0 < n → (α i / α j) ^ n ≠ 1) (hf0 : ∀ i, f i ≠ 0) :
    {r : ℕ | powerSum α f r = 0 ∨ ∃ w : Kˣ, w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧
      (w : K) = powerSum α f r}.Finite := by
  classical
  obtain ⟨s₀, hs₀⟩ := exists_powerSum_ne_zero (injective_of_forall_div_pow_ne_one hnd hα0) hα0 hf0
  obtain ⟨T, hT⟩ := exists_finset_mem_unit (Units.mk0 _ hs₀)
  have hP := finite_setOf_powerSum_div_mem_unit (S ∪ T) hα0 hnd hf0
  refine ((Set.finite_Iic s₀).union (hP.image Prod.fst)).subset fun r hr ↦ ?_
  by_cases hrs : r ≤ s₀
  · exact Or.inl hrs
  refine Or.inr ⟨(r, s₀), ⟨not_le.mp hrs, hs₀, ?_⟩, rfl⟩
  rcases hr with h0 | ⟨w, hw, hwe⟩
  · exact Or.inl h0
  · refine Or.inr ⟨w * (Units.mk0 _ hs₀)⁻¹, mul_mem (mem_unit_of_subset (by simp) hw)
      (inv_mem (mem_unit_of_subset (by simp) hT)), ?_⟩
    simp [hwe, div_eq_mul_inv]

/-- **Evertse's Corollary 3** for a sequence in `K` with characteristic roots in an extension
`L`: only finitely many `r` have `u_r` zero or an `S`-unit. -/
theorem finite_setOf_mem_unit_of_eq_powerSum (S : Finset (HeightOneSpectrum (𝓞 K)))
    {u : ℕ → K} {ι : Type*} [Fintype ι] [Nontrivial ι] {α : ι → L} {f : ι → L[X]}
    (hu : ∀ k, algebraMap K L (u k) = powerSum α f k) (hα0 : ∀ i, α i ≠ 0)
    (hnd : ∀ i j, i ≠ j → ∀ n : ℕ, 0 < n → (α i / α j) ^ n ≠ 1) (hf0 : ∀ i, f i ≠ 0) :
    {r : ℕ | u r = 0 ∨ ∃ w : Kˣ, w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧
      (w : K) = u r}.Finite := by
  refine (finite_setOf_powerSum_mem_unit (primesAbove L S) hα0 hnd hf0).subset ?_
  rintro r (h0 | ⟨w, hw, hwe⟩)
  · exact Or.inl (by rw [← hu, h0, map_zero])
  · exact Or.inr ⟨_, map_mem_unit_primesAbove hw, by simp [← hu, hwe]⟩

/-- **Corollary 4, two or more characteristic roots**: under the hypotheses of Theorem 3, only
finitely many pairs `r > s` have `u_r = u_s`. -/
theorem finite_setOf_powerSum_eq_of_nontrivial {ι : Type*} [Fintype ι] [Nontrivial ι]
    {α : ι → K} {f : ι → K[X]} (hα0 : ∀ i, α i ≠ 0)
    (hnd : ∀ i j, i ≠ j → ∀ n : ℕ, 0 < n → (α i / α j) ^ n ≠ 1) (hf0 : ∀ i, f i ≠ 0) :
    {p : ℕ × ℕ | p.2 < p.1 ∧ powerSum α f p.1 = powerSum α f p.2}.Finite := by
  have hP := finite_setOf_powerSum_div_mem_unit ∅ hα0 hnd hf0
  have hZ := finite_setOf_powerSum_mem_unit ∅ hα0 hnd hf0
  refine (hP.union (hZ.prod hZ)).subset fun p ⟨hsr, heq⟩ ↦ ?_
  by_cases hs : powerSum α f p.2 = 0
  · exact Or.inr ⟨Or.inl (heq.trans hs), Or.inl hs⟩
  · exact Or.inl ⟨hsr, hs, Or.inr ⟨1, one_mem _, by rw [heq, div_self hs, Units.val_one]⟩⟩

/-- **Corollary 4, one characteristic root**: `u_k = f(k) α ^ k` with `α ≠ 0`, `f ≠ 0`, and not
both `f` constant and `α` a root of unity, has only finitely many pairs `r > s` with
`u_r = u_s`. -/
theorem finite_setOf_eval_mul_pow_eq {α : K} (hα0 : α ≠ 0) {f : K[X]} (hf0 : f ≠ 0)
    (h : 0 < f.natDegree ∨ ∀ n : ℕ, 0 < n → α ^ n ≠ 1) :
    {p : ℕ × ℕ | p.2 < p.1 ∧ f.eval (p.1 : K) * α ^ p.1 = f.eval (p.2 : K) * α ^ p.2}.Finite := by
  let M := f.SplittingField
  have : NumberField M := NumberField.of_module_finite K M
  set φ := algebraMap K M
  have h' : 0 < (f.map φ).natDegree ∨ ∀ n : ℕ, 0 < n → φ α ^ n ≠ 1 := by
    rw [natDegree_map]
    refine h.imp id fun h n hn ↦ ?_
    rw [← map_pow, ne_eq, map_eq_one_iff _ φ.injective]; exact h n hn
  refine (finite_setOf_eval_mul_pow_eq_of_splits ((_root_.map_ne_zero _).mpr hα0)
    ((Polynomial.map_ne_zero_iff φ.injective).mpr hf0) (SplittingField.splits f) h').subset
    fun p ⟨hsr, hp⟩ ↦ ⟨hsr, ?_⟩
  rw [← map_natCast φ, ← map_natCast φ, eval_map_algebraMap_apply, eval_map_algebraMap_apply,
    ← map_pow, ← map_pow, ← map_mul, ← map_mul, hp]

/-- **Evertse's Corollary 4.** Let `u_k = ∑_i f_i(k) α_i ^ k` with nonzero characteristic roots
`α_i ∈ K`, no quotient `α_i / α_j` (`i ≠ j`) a root of unity, and nonzero `f_i ∈ K[X]`. Unless
`u_k = c α ^ k` with `α` a root of unity, only finitely many pairs `r > s` have `u_r = u_s`. -/
theorem finite_setOf_powerSum_eq {ι : Type*} [Fintype ι] [Nonempty ι] {α : ι → K}
    {f : ι → K[X]} (hα0 : ∀ i, α i ≠ 0)
    (hnd : ∀ i j, i ≠ j → ∀ n : ℕ, 0 < n → (α i / α j) ^ n ≠ 1) (hf0 : ∀ i, f i ≠ 0)
    (hone : Subsingleton ι → ∀ i, 0 < (f i).natDegree ∨ ∀ n : ℕ, 0 < n → α i ^ n ≠ 1) :
    {p : ℕ × ℕ | p.2 < p.1 ∧ powerSum α f p.1 = powerSum α f p.2}.Finite := by
  rcases subsingleton_or_nontrivial ι with hι | hι
  · obtain ⟨i⟩ := ‹Nonempty ι›
    have hu : ∀ k, powerSum α f k = (f i).eval (k : K) * α i ^ k := fun k ↦
      Fintype.sum_subsingleton _ i
    simp only [hu]
    exact finite_setOf_eval_mul_pow_eq (hα0 i) (hf0 i) (hone hι i)
  · exact finite_setOf_powerSum_eq_of_nontrivial hα0 hnd hf0

omit [NumberField K] in
/-- **Evertse's Corollary 4** for a sequence in `K` with characteristic roots in an extension
`L`: unless `u_k = c α ^ k` with `α` a root of unity, only finitely many pairs `r > s` have
`u_r = u_s`. -/
theorem finite_setOf_eq_of_eq_powerSum {u : ℕ → K} {ι : Type*} [Fintype ι] [Nonempty ι]
    {α : ι → L} {f : ι → L[X]} (hu : ∀ k, algebraMap K L (u k) = powerSum α f k)
    (hα0 : ∀ i, α i ≠ 0)
    (hnd : ∀ i j, i ≠ j → ∀ n : ℕ, 0 < n → (α i / α j) ^ n ≠ 1) (hf0 : ∀ i, f i ≠ 0)
    (hone : Subsingleton ι → ∀ i, 0 < (f i).natDegree ∨ ∀ n : ℕ, 0 < n → α i ^ n ≠ 1) :
    {p : ℕ × ℕ | p.2 < p.1 ∧ u p.1 = u p.2}.Finite :=
  (finite_setOf_powerSum_eq hα0 hnd hf0 hone).subset fun p ⟨hsr, h⟩ ↦
    ⟨hsr, by rw [← hu, ← hu, h]⟩

end NumberField
