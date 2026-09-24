/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.NumberTheory.Height.NumberField

/-!
# Liouville's inequality for the value of a linear form

A nonzero element of a number field is not small at one place unless it is large at another: that
is the fundamental inequality of Bombieri–Gubler (1.8). This file records the form of it that the
Subspace Theorem's Step III needs, where the element is the value `∑ s, a s * z s` of a linear
form and what has to be bounded is the **local factor of the point `z`**, not the element itself.

For a tuple `b` one of whose subsums over a `Finset` `t` is nonzero, at every place the local
factor `⨆ p, |b p|` is at most `(#t) ^ [K : ℚ]` times the height of `b` times the local value of
the subsum. Applied to the multiplication table `b (s, s') = a s * z s'` and the diagonal, this
reads

```text
(⨆ s, |a s|_v) * (⨆ s, |z s|_v)  ≤  (#ρ) ^ [K : ℚ] * H(a) * H(z) * |∑ s, a s * z s|_v ,
```

a two-sided statement: the value of the form is small at `v` only if the point is small at `v`
in the projective sense, with a constant that depends on the coefficients only through their
height.

## Main results

* `NumberField.InfinitePlace.iSup_pow_mult_le_of_sum_ne_zero` and
  `NumberField.FinitePlace.iSup_le_of_sum_ne_zero`: the bound for a subsum of a tuple.
* `NumberField.InfinitePlace.iSup_mul_iSup_pow_mult_le` and
  `NumberField.FinitePlace.iSup_mul_iSup_le`: the bound for the value of a linear form.
* `NumberField.FinitePlace.hasFiniteMulSupport_iSup`: the local factor of a nonzero tuple is `1`
  at all but finitely many finite places, in the `FinitePlace` indexing. Mathlib proves this only
  for the `nonarchAbsVal` indexing, and privately.
* `NumberField.prod_le_finprod_of_one_le` and `NumberField.finprod_le_prod_of_le_one_outside`:
  the two comparisons between a `finprod` over the finite places and a subproduct.

An acceptance test at the end of the file machine-checks that the book's form of the inequality is
false: over `ℚ` the tuple `![N, 0]` has projective height `1` and the value `N` of the first
coordinate form has height `|N|`.

## Implementation notes

⚠ **The product formula is not used, and the normalization carries it.** The proof divides the
tuple by the value of the subsum, which leaves the height unchanged
(`Height.mulHeight_smul_eq_mulHeight`) — that invariance *is* the product formula — and then
reads off that every local factor of the normalized tuple is at least `(#t)⁻¹` at an infinite
place and at least `1` at a finite one, because the entries sum to `1`. The height of a tuple
whose local factors are bounded below everywhere bounds each of them above. No `finprod` is ever
split at a place.

⚠ **Bombieri–Gubler's form of the inequality is not the one that is true.** The proof of Lemma
7.5.21 bounds `h(D_{vi})` — the height of the single number `L̂_{vi}(w)` — by `h(V(Q)) + C₇`.
That cannot hold: the left-hand side changes when `w` is rescaled and the right-hand side does
not, and over `ℚ` the vector `w = (N, 0)` has `h(V) = 0` and `h(w_0) = log N`. What is true, and
what the proof needs, is the displayed inequality above, in which the local factor of `z` appears
on the left and the *projective* height of `z` on the right. It is also **stronger** than what
the book extracts: summing it over `S` costs `|S| - 1` powers of the height of the subspace and
not `|S|`, because the local factors of `z` at the places of `S` multiply to at least its height.

⚠ **The archimedean count is the number of terms, not the number of variables.** Only the
diagonal of the multiplication table is summed, so `#t = #ρ` and not `#ρ ^ 2`; at a
nonarchimedean place there is no count at all, and the constant is a power of `#t` over the
archimedean places only, which is `(#t) ^ totalWeight K`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
(1.8) and Lemma 7.5.21.

This is Layer 5.4 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

noncomputable section

open Finset Real Height

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

section FiniteSupport

variable {ι : Type*} [Finite ι]

/-- The local factor of a nonzero tuple is `1` at all but finitely many finite places. -/
theorem FinitePlace.hasFiniteMulSupport_iSup {x : ι → K} (hx : x ≠ 0) :
    (fun v : FinitePlace K ↦ ⨆ i, v (x i)).HasFiniteMulSupport := by
  classical
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  have : Nonempty ι := ⟨i₀⟩
  have hsub : Function.mulSupport (fun v : FinitePlace K ↦ ⨆ i, v (x i))
      ⊆ ⋃ i ∈ {i : ι | x i ≠ 0}, Function.mulSupport (fun v : FinitePlace K ↦ v (x i)) := by
    intro v hv
    by_contra hc
    refine hv ?_
    simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not,
      Set.mem_ofPred_eq] at hc
    have hall : ∀ i, v (x i) ≤ 1 := by
      intro i
      rcases eq_or_ne (x i) 0 with h | h
      · rw [h, map_zero]; exact zero_le_one
      · exact le_of_eq (hc i h)
    have h1 : v (x i₀) = 1 := hc i₀ hi₀
    refine le_antisymm (Real.iSup_le hall zero_le_one) ?_
    rw [← h1]
    exact Finite.le_ciSup_of_le i₀ le_rfl
  exact Set.Finite.subset
    (Set.Finite.biUnion (Set.toFinite _) fun i hi ↦ FinitePlace.hasFiniteMulSupport hi) hsub

/-- A subproduct of factors `≥ 1` is at most the whole `finprod`. -/
theorem prod_le_finprod_of_one_le {α : Type*} {f : α → ℝ} (s : Finset α) (hf : ∀ a, 1 ≤ f a)
    (hfin : Function.HasFiniteMulSupport f) : ∏ a ∈ s, f a ≤ ∏ᶠ a, f a := by
  have h1 : Function.HasFiniteMulSupport ((s : Set α).mulIndicator f) := by
    refine Set.Finite.subset s.finite_toSet fun a ha ↦ ?_
    simp only [Function.mem_mulSupport, Set.mulIndicator_apply_ne_one] at ha
    exact ha.1
  have h2 : (∏ᶠ a, (s : Set α).mulIndicator f a) = ∏ a ∈ s, f a := by
    rw [← finprod_mem_def, finprod_mem_coe_finset]
  rw [← h2]
  exact finprod_le_finprod₀ h1
    (fun a ↦ le_trans zero_le_one (Set.one_le_mulIndicator (fun b _ ↦ hf b) a)) hfin
    (Set.mulIndicator_le_self' fun b _ ↦ hf b)

/-- A `finprod` of nonnegative factors that are at most `1` outside a `Finset` is at most the
subproduct over that `Finset`. -/
theorem finprod_le_prod_of_le_one_outside {α : Type*} {f : α → ℝ} (s : Finset α)
    (hf0 : ∀ a, 0 ≤ f a) (hf : ∀ a ∉ s, f a ≤ 1) (hfin : Function.HasFiniteMulSupport f) :
    ∏ᶠ a, f a ≤ ∏ a ∈ s, f a := by
  have h1 : Function.HasFiniteMulSupport ((s : Set α).mulIndicator f) := by
    refine Set.Finite.subset s.finite_toSet fun a ha ↦ ?_
    simp only [Function.mem_mulSupport, Set.mulIndicator_apply_ne_one] at ha
    exact ha.1
  have h2 : (∏ᶠ a, (s : Set α).mulIndicator f a) = ∏ a ∈ s, f a := by
    rw [← finprod_mem_def, finprod_mem_coe_finset]
  rw [← h2]
  refine finprod_le_finprod₀ hfin hf0 h1 fun a ↦ ?_
  by_cases ha : a ∈ s
  · rw [Set.mulIndicator_of_mem (by exact_mod_cast ha)]
  · rw [Set.mulIndicator_of_notMem (by exact_mod_cast ha)]
    exact hf a ha

end FiniteSupport

/-!
### Liouville's inequality for the value of a linear form
-/

section LinearForm

variable {ρ : Type*} [Finite ρ] [Nonempty ρ]

omit [Nonempty ρ] in
/-- The local factor of a tuple whose entries sum to `1` over `t` is at least `(#t)⁻¹`. -/
private theorem inv_card_le_iSup_infinite (w : InfinitePlace K) {b : ρ → K} {t : Finset ρ}
    (ht : ∑ p ∈ t, b p = 1) : ((#t : ℝ))⁻¹ ≤ ⨆ p, w (b p) := by
  have hb : ∀ p, w (b p) ≤ ⨆ q, w (b q) := fun p ↦ Finite.le_ciSup_of_le p le_rfl
  have h1 : (1 : ℝ) ≤ ∑ p ∈ t, w (b p) := by
    calc (1 : ℝ) = w (∑ p ∈ t, b p) := by rw [ht, map_one]
      _ ≤ ∑ p ∈ t, w (b p) := w.1.sum_le _ _
  have h2 : ∑ p ∈ t, w (b p) ≤ (#t : ℝ) * ⨆ q, w (b q) := by
    calc ∑ p ∈ t, w (b p) ≤ ∑ _p ∈ t, ⨆ q, w (b q) := Finset.sum_le_sum fun p _ ↦ hb p
      _ = (#t : ℝ) * ⨆ q, w (b q) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : 0 < (#t : ℝ) := by
    rcases Finset.eq_empty_or_nonempty t with rfl | hne
    · simp at ht
    · exact_mod_cast Finset.card_pos.mpr hne
  rw [inv_le_iff_one_le_mul₀ hcard]
  linarith

/-- The local factor at a finite place of a tuple whose entries sum to `1` over `t` is at
least `1`: the ultrametric inequality needs no count of the terms. -/
private theorem one_le_iSup_finite (w : FinitePlace K) {b : ρ → K} {t : Finset ρ}
    (ht : ∑ p ∈ t, b p = 1) : (1 : ℝ) ≤ ⨆ p, w (b p) := by
  have hb : ∀ p, w (b p) ≤ ⨆ q, w (b q) := fun p ↦ Finite.le_ciSup_of_le p le_rfl
  have key : w (∑ p ∈ t, b p) ≤ ⨆ q, w (b q) := by
    refine Finset.sum_induction b (fun y ↦ w y ≤ ⨆ q, w (b q))
      (fun a c ha hc ↦ (w.add_le a c).trans (max_le ha hc)) ?_ (fun p _ ↦ hb p)
    have : (0 : ℝ) ≤ ⨆ q, w (b q) := le_trans (w.1.nonneg _) (hb Classical.ofNonempty)
    simpa using this
  rw [ht, map_one] at key
  exact key

/-- The data attached to a tuple with a nonzero subsum: its normalization `D⁻¹ • b` is nonzero,
its entries sum to `1` over `t`, its height is that of `b`, and its local factors are those of
`b` divided by the local value of the subsum. -/
private theorem normalization {b : ρ → K} {t : Finset ρ} (hD : ∑ p ∈ t, b p ≠ 0) :
    (1 : ℝ) ≤ (#t : ℝ) ∧ ((∑ p ∈ t, b p)⁻¹ • b) ≠ 0 ∧
      (∑ p ∈ t, ((∑ p ∈ t, b p)⁻¹ • b) p) = 1 ∧
      Height.mulHeight ((∑ p ∈ t, b p)⁻¹ • b) = Height.mulHeight b ∧
      (∀ u : InfinitePlace K, ((#t : ℝ))⁻¹ ≤ ⨆ p, u (((∑ p ∈ t, b p)⁻¹ • b) p)) ∧
      (∀ u : FinitePlace K, (1 : ℝ) ≤ ⨆ p, u (((∑ p ∈ t, b p)⁻¹ • b) p)) ∧
      (∀ u : InfinitePlace K, (⨆ p, u (((∑ p ∈ t, b p)⁻¹ • b) p))
        = (u (∑ p ∈ t, b p))⁻¹ * ⨆ p, u (b p)) ∧
      ∀ u : FinitePlace K, (⨆ p, u (((∑ p ∈ t, b p)⁻¹ • b) p))
        = (u (∑ p ∈ t, b p))⁻¹ * ⨆ p, u (b p) := by
  have hb : b ≠ 0 := fun h ↦ hD (by simp [h])
  have hz : ((∑ p ∈ t, b p)⁻¹ • b) ≠ 0 := smul_ne_zero (inv_ne_zero hD) hb
  have hsum : (∑ p ∈ t, ((∑ p ∈ t, b p)⁻¹ • b) p) = 1 := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hD
  have hcard : (1 : ℝ) ≤ (#t : ℝ) := by
    rcases Finset.eq_empty_or_nonempty t with rfl | hne
    · simp at hsum
    · exact_mod_cast Finset.card_pos.mpr hne
  refine ⟨hcard, hz, hsum, Height.mulHeight_smul_eq_mulHeight b (inv_ne_zero hD),
    fun u ↦ inv_card_le_iSup_infinite u hsum, fun u ↦ one_le_iSup_finite u hsum,
    fun u ↦ ?_, fun u ↦ ?_⟩
  · have hp : ∀ p, u (((∑ p ∈ t, b p)⁻¹ • b) p) = (u (∑ p ∈ t, b p))⁻¹ * u (b p) := fun p ↦ by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    simp only [hp]
    exact (Real.mul_iSup_of_nonneg (by positivity) _).symm
  · have hp : ∀ p, u (((∑ p ∈ t, b p)⁻¹ • b) p) = (u (∑ p ∈ t, b p))⁻¹ * u (b p) := fun p ↦ by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    simp only [hp]
    exact (Real.mul_iSup_of_nonneg (by positivity) _).symm

omit [Nonempty ρ] in
/-- **The local factor is bounded by the height once it is bounded below everywhere.** If the
local factors of `z` are at least `c ≤ 1` at the infinite places and at least `1` at the finite
ones, then at any one place the local factor is at most `c ^ (-totalWeight)` times the height. -/
private theorem bound_of_local_lower {z : ρ → K} (hz : z ≠ 0) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hinf : ∀ u : InfinitePlace K, c ≤ ⨆ p, u (z p))
    (hfin : ∀ u : FinitePlace K, (1 : ℝ) ≤ ⨆ p, u (z p)) :
    (∀ w : InfinitePlace K,
        (⨆ p, w (z p)) ^ w.mult ≤ (c⁻¹) ^ Height.totalWeight K * Height.mulHeight z) ∧
      ∀ w : FinitePlace K,
        (⨆ p, w (z p)) ≤ (c⁻¹) ^ Height.totalWeight K * Height.mulHeight z := by
  classical
  have hHeq : Height.mulHeight z
      = (∏ u : InfinitePlace K, (⨆ p, u (z p)) ^ u.mult) * ∏ᶠ u : FinitePlace K, ⨆ p, u (z p) :=
    NumberField.mulHeight_eq hz
  have hfinC : Function.HasFiniteMulSupport (fun u : FinitePlace K ↦ ⨆ p, u (z p)) :=
    FinitePlace.hasFiniteMulSupport_iSup hz
  have hcpow : (0 : ℝ) < c ^ Height.totalWeight K := pow_pos hc0 _
  have hprodC : (1 : ℝ) ≤ ∏ᶠ u : FinitePlace K, ⨆ p, u (z p) := one_le_finprod hfin
  have hsum : ∀ s : Finset (InfinitePlace K),
      c ^ (∑ u ∈ s, u.mult) ≤ ∏ u ∈ s, (⨆ p, u (z p)) ^ u.mult := by
    intro s
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod₀ (fun u _ ↦ pow_nonneg hc0.le _)
      fun u _ ↦ pow_le_pow_left₀ hc0.le (hinf u) _
  have htw : Height.totalWeight K = ∑ u : InfinitePlace K, u.mult :=
    NumberField.totalWeight_eq_sum_mult K
  constructor
  · intro w
    have herase : ∑ u ∈ univ.erase w, u.mult ≤ Height.totalWeight K := by
      rw [htw]
      exact Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
    have hsplit : (∏ u : InfinitePlace K, (⨆ p, u (z p)) ^ u.mult)
        = (⨆ p, w (z p)) ^ w.mult * ∏ u ∈ univ.erase w, (⨆ p, u (z p)) ^ u.mult :=
      (Finset.mul_prod_erase _ _ (mem_univ w)).symm
    have hlow : c ^ Height.totalWeight K * (⨆ p, w (z p)) ^ w.mult
        ≤ ∏ u : InfinitePlace K, (⨆ p, u (z p)) ^ u.mult := by
      rw [hsplit]
      have h1 : c ^ Height.totalWeight K ≤ c ^ (∑ u ∈ univ.erase w, u.mult) :=
        pow_le_pow_of_le_one hc0.le hc1 herase
      have h2 := hsum (univ.erase w)
      have h3 : (0 : ℝ) ≤ (⨆ p, w (z p)) ^ w.mult :=
        pow_nonneg (le_trans hc0.le (hinf w)) _
      nlinarith [hcpow, h1.trans h2]
    have hfinal : c ^ Height.totalWeight K * (⨆ p, w (z p)) ^ w.mult ≤ Height.mulHeight z := by
      rw [hHeq]
      have hnn := Finset.prod_nonneg
        (fun u (_ : u ∈ (univ : Finset (InfinitePlace K))) ↦
          pow_nonneg (le_trans hc0.le (hinf u)) u.mult)
      nlinarith [hlow, hprodC, hnn]
    rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ hcpow, mul_comm]
    exact hfinal
  · intro w
    have hlow : c ^ Height.totalWeight K ≤ ∏ u : InfinitePlace K, (⨆ p, u (z p)) ^ u.mult := by
      have := hsum univ
      rwa [← htw] at this
    have hCw : (⨆ p, w (z p)) ≤ ∏ᶠ u : FinitePlace K, ⨆ p, u (z p) := by
      have := prod_le_finprod_of_one_le (f := fun u : FinitePlace K ↦ ⨆ p, u (z p)) {w} hfin hfinC
      simpa using this
    have hfinal : c ^ Height.totalWeight K * (⨆ p, w (z p)) ≤ Height.mulHeight z := by
      rw [hHeq]
      nlinarith [hlow, hCw, hcpow, le_trans zero_le_one (hfin w)]
    rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ hcpow, mul_comm]
    exact hfinal

/-- **Liouville's inequality for the value of a linear form** (the lower bound of
Bombieri–Gubler (1.8), read on a subsum of a tuple). If a subsum over `t` of the entries of a
tuple `b` is nonzero, then at every infinite place the local factor of `b` is at most the height
of `b` times that value, up to the number of terms. -/
theorem InfinitePlace.iSup_pow_mult_le_of_sum_ne_zero (w : InfinitePlace K) (b : ρ → K)
    (t : Finset ρ) (hD : ∑ p ∈ t, b p ≠ 0) :
    (⨆ p, w (b p)) ^ w.mult
      ≤ (#t : ℝ) ^ Height.totalWeight K * Height.mulHeight b * w (∑ p ∈ t, b p) ^ w.mult := by
  obtain ⟨hcard, hz, hsum, hHeq, hinf, hfin, hscaleI, hscaleF⟩ := normalization hD
  obtain ⟨key, -⟩ := bound_of_local_lower hz (c := ((#t : ℝ))⁻¹)
    (by positivity) ((inv_le_one₀ (lt_of_lt_of_le zero_lt_one hcard)).mpr hcard) hinf hfin
  have hw : (0 : ℝ) < w (∑ p ∈ t, b p) := by
    simpa using (InfinitePlace.pos_iff (w := w)).mpr hD
  have hk := key w
  rw [hscaleI w, hHeq, inv_inv, mul_pow] at hk
  calc (⨆ p, w (b p)) ^ w.mult
      = ((w (∑ p ∈ t, b p))⁻¹ ^ w.mult * (⨆ p, w (b p)) ^ w.mult)
          * w (∑ p ∈ t, b p) ^ w.mult := by
        rw [mul_comm _ ((⨆ p, w (b p)) ^ w.mult), mul_assoc, ← mul_pow,
          inv_mul_cancel₀ hw.ne', one_pow, mul_one]
    _ ≤ ((#t : ℝ) ^ Height.totalWeight K * Height.mulHeight b) * w (∑ p ∈ t, b p) ^ w.mult :=
        mul_le_mul_of_nonneg_right hk (pow_nonneg hw.le _)
    _ = (#t : ℝ) ^ Height.totalWeight K * Height.mulHeight b * w (∑ p ∈ t, b p) ^ w.mult := rfl

/-- The finite-place companion of
`NumberField.InfinitePlace.iSup_pow_mult_le_of_sum_ne_zero`. -/
theorem FinitePlace.iSup_le_of_sum_ne_zero (w : FinitePlace K) (b : ρ → K)
    (t : Finset ρ) (hD : ∑ p ∈ t, b p ≠ 0) :
    (⨆ p, w (b p)) ≤ (#t : ℝ) ^ Height.totalWeight K * Height.mulHeight b * w (∑ p ∈ t, b p) := by
  obtain ⟨hcard, hz, hsum, hHeq, hinf, hfin, hscaleI, hscaleF⟩ := normalization hD
  obtain ⟨-, key⟩ := bound_of_local_lower hz (c := ((#t : ℝ))⁻¹)
    (by positivity) ((inv_le_one₀ (lt_of_lt_of_le zero_lt_one hcard)).mpr hcard) hinf hfin
  have hw : (0 : ℝ) < w (∑ p ∈ t, b p) := FinitePlace.pos_iff.mpr hD
  have hk := key w
  rw [hscaleF w, hHeq, inv_inv] at hk
  calc (⨆ p, w (b p))
      = ((w (∑ p ∈ t, b p))⁻¹ * ⨆ p, w (b p)) * w (∑ p ∈ t, b p) := by
        rw [mul_comm _ (⨆ p, w (b p)), mul_assoc, inv_mul_cancel₀ hw.ne', mul_one]
    _ ≤ ((#t : ℝ) ^ Height.totalWeight K * Height.mulHeight b) * w (∑ p ∈ t, b p) :=
        mul_le_mul_of_nonneg_right hk hw.le
    _ = (#t : ℝ) ^ Height.totalWeight K * Height.mulHeight b * w (∑ p ∈ t, b p) := rfl

/-! ### The form read on its coefficients and its point -/

section DotProduct

variable {σ : Type*} [Fintype σ] [Nonempty σ]

omit [Nonempty σ] in
/-- The data shared by the two places: the diagonal of the multiplication table. -/
private theorem diagonal_data (a z : σ → K) (hD : ∑ s, a s * z s ≠ 0) :
    ∃ t : Finset (σ × σ), #t = Fintype.card σ ∧
      (∑ p ∈ t, (fun p : σ × σ ↦ a p.1 * z p.2) p) = ∑ s, a s * z s ∧
      Height.mulHeight (fun p : σ × σ ↦ a p.1 * z p.2)
        = Height.mulHeight a * Height.mulHeight z := by
  classical
  have ha : a ≠ 0 := fun h ↦ hD (by simp [h])
  have hz : z ≠ 0 := fun h ↦ hD (by simp [h])
  refine ⟨Finset.univ.image fun s ↦ (s, s), ?_, ?_, Height.mulHeight_fun_mul_eq ha hz⟩
  · rw [Finset.card_image_of_injective _ (fun s t h ↦ (Prod.mk.injEq .. ▸ h).1),
      Finset.card_univ]
  · rw [Finset.sum_image (fun s _ t _ h ↦ (Prod.mk.injEq .. ▸ h).1)]

/-- **Liouville's inequality for the value of a linear form**, at an infinite place: the product
of the local factors of the coefficient tuple and of the point is at most the height of the two
tuples times the local value of the form. -/
theorem InfinitePlace.iSup_mul_iSup_pow_mult_le (w : InfinitePlace K) (a z : σ → K)
    (hD : ∑ s, a s * z s ≠ 0) :
    ((⨆ s, w (a s)) * ⨆ s, w (z s)) ^ w.mult
      ≤ (Fintype.card σ : ℝ) ^ Height.totalWeight K
        * (Height.mulHeight a * Height.mulHeight z) * w (∑ s, a s * z s) ^ w.mult := by
  obtain ⟨t, hcard, hsum, hH⟩ := diagonal_data a z hD
  have key := InfinitePlace.iSup_pow_mult_le_of_sum_ne_zero w
    (fun p : σ × σ ↦ a p.1 * z p.2) t (by rw [hsum]; exact hD)
  rwa [hsum, hcard, hH, Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg w a z] at key

/-- The finite-place companion of `NumberField.InfinitePlace.iSup_mul_iSup_pow_mult_le`. -/
theorem FinitePlace.iSup_mul_iSup_le (w : FinitePlace K) (a z : σ → K)
    (hD : ∑ s, a s * z s ≠ 0) :
    ((⨆ s, w (a s)) * ⨆ s, w (z s))
      ≤ (Fintype.card σ : ℝ) ^ Height.totalWeight K
        * (Height.mulHeight a * Height.mulHeight z) * w (∑ s, a s * z s) := by
  obtain ⟨t, hcard, hsum, hH⟩ := diagonal_data a z hD
  have key := FinitePlace.iSup_le_of_sum_ne_zero w
    (fun p : σ × σ ↦ a p.1 * z p.2) t (by rw [hsum]; exact hD)
  rwa [hsum, hcard, hH, Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg w a z] at key

end DotProduct

end LinearForm

end NumberField

/-!
### Acceptance criteria

That the book's form of the inequality is false, and that no constant repairs it.
-/

section Examples

/-- **Bombieri–Gubler's `h(D_{v i}) ≤ h(V(Q)) + C₇` holds for no constant.** Over `ℚ`, take the
first coordinate form `a = ![1, 0]` and the point `z = ![N, 0]`. The value of the form is `N`,
whose height is `|N|` and grows without bound, while the **projective** height of `z` is `1`,
whatever `N` is: scaling a tuple does not change it. The inequality proved above puts the *local
factor* of `z` on the left instead, and is invariant under the same scaling as its right-hand
side. -/
example (N : ℤ) (hN : N ≠ 0) :
    (∑ s, (![(1 : ℚ), 0]) s * (![(N : ℚ), 0]) s) = (N : ℚ) ∧
      Height.mulHeight (![(N : ℚ), 0]) = 1 ∧
      Height.mulHeight₁ ((N : ℚ)) = (N.natAbs : ℝ) := by
  refine ⟨by simp [Fin.sum_univ_two], ?_, ?_⟩
  · have h1 : (![(N : ℚ), 0]) = (N : ℚ) • (![(1 : ℚ), 0]) := by
      funext i
      fin_cases i <;> simp
    rw [h1, Height.mulHeight_smul_eq_mulHeight _ (by exact_mod_cast hN)]
    have hgcd : (Finset.univ.gcd (![(1 : ℤ), 0])) = 1 := by decide
    have key := Rat.mulHeight_eq_max_abs_of_gcd_eq_one hgcd
    have hcast : ((↑) : ℤ → ℚ) ∘ (![(1 : ℤ), 0]) = ![(1 : ℚ), 0] := by
      funext i
      fin_cases i <;> simp
    rw [hcast] at key
    rw [key]
    have hone : (⨆ i, |(![(1 : ℤ), 0]) i|) = 1 := by
      refine le_antisymm (ciSup_le fun i ↦ ?_) (Finite.le_ciSup_of_le 0 (by simp))
      fin_cases i <;> simp
    rw [hone]
    norm_num
  · rw [Rat.mulHeight₁_eq_max]
    simp [Int.natAbs_eq_zero.not.mpr hN, Nat.one_le_iff_ne_zero]

end Examples
