/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Regular.RegularSequence

-- Used only inside proofs.
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import STForMathlib.RingTheory.RegularLocalRing.RegularSequence

/-!
# Sequences of the right height are regular

Let `R` be a Noetherian local ring of dimension `d` whose maximal ideal contains an `R`-regular
sequence of length `d` (a Cohen–Macaulay local ring; a regular local ring by
`IsRegularLocalRing.exists_isRegular`). If `x₁, …, x_m` in the maximal ideal generate an ideal of
height `m`, then `x₁, …, x_m` is a regular sequence, in this order (Matsumura, Thm. 17.4).

The proof needs no catenarity. If `x_{j+1}` lay in an associated prime `Q` of
`R / (x₁, …, x_j)`, then `dim R / Q ≥ d - j` by depth
(`IsLocalRing.length_le_ringKrullDim_quotient_of_mem_associatedPrimes`), and the remaining
`m - j - 1` elements cut `R / Q` down to `R / (Q + (x_{j+2}, …, x_m))`, of dimension
`≥ d - m + 1` by Krull's height theorem. But every prime containing all the `x_i` has height
`≥ m`, so that quotient has dimension `≤ d - m`.

## Main statements

* `Ideal.ringKrullDim_quotient_le_of_forall`: `dim R / I` is bounded by the bounds on `dim R / P`
  for the primes `P ⊇ I`.
* `Ideal.ringKrullDim_quotient_le_sub`: `dim R / P ≤ d - m` for a prime of height `≥ m`.
* `IsLocalRing.isSMulRegular_of_le_height`: **sequences of height `m` are regular**.
-/

@[expose] public section

open IsLocalRing RingTheory.Sequence

namespace Ideal

variable {R : Type*} [CommRing R]

/-- `dim R / I` is bounded by any bound on `dim R / P` for the primes `P ⊇ I`. -/
theorem ringKrullDim_quotient_le_of_forall (I : Ideal R) {k : WithBot ℕ∞}
    (h : ∀ P : Ideal R, P.IsPrime → I ≤ P → ringKrullDim (R ⧸ P) ≤ k) :
    ringKrullDim (R ⧸ I) ≤ k := by
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun a ↦ ?_
  have := a.1.2
  refine le_trans ?_ (h a.1.asIdeal inferInstance ((PrimeSpectrum.mem_zeroLocus _ _).mp a.2))
  rw [ringKrullDim_quotient_eq_coheight]
  exact_mod_cast Order.coheight_le_coheight_apply_of_strictMono Subtype.val
    (fun _ _ h ↦ h) a

/-- `dim R / P ≤ d - m` for a prime `P` of height `≥ m` in a ring of dimension `d`. -/
theorem ringKrullDim_quotient_le_sub {d m : ℕ} (hdim : ringKrullDim R = d)
    {P : Ideal R} [P.IsPrime] (hP : (m : ℕ∞) ≤ P.height) :
    ringKrullDim (R ⧸ P) ≤ ((d - m : ℕ) : WithBot ℕ∞) := by
  have h := Ideal.height_add_ringKrullDim_quotient_le P
  rw [hdim] at h
  obtain ⟨c, hc⟩ := WithBot.ne_bot_iff_exists.mp
    (ne_bot_of_le_ne_bot (by simp) (ringKrullDim_nonneg_of_nontrivial (R := R ⧸ P)))
  rw [← hc] at h ⊢
  have h' : P.height + c ≤ d := by exact_mod_cast h
  have hm : (m : ℕ∞) + c ≤ d := (add_le_add_left hP c).trans h'
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℕ∞) = c := ENat.ne_top_iff_exists.mp fun h ↦ by
    simp [h] at hm
  have : m + n ≤ d := by exact_mod_cast hm
  rw [← WithBot.coe_natCast]
  exact WithBot.coe_le_coe.mpr (by exact_mod_cast (by omega : n ≤ d - m))

end Ideal

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- **Sequences of height `m` are regular** (Matsumura, Thm. 17.4). In a Noetherian local ring
of dimension `d` with a regular sequence of length `d` in the maximal ideal, elements
`x₀, …, x_{m-1}` of the maximal ideal generating an ideal of height `≥ m` form a regular
sequence: each `x j` is a nonzerodivisor modulo `(x i | i < j)`. -/
theorem isSMulRegular_of_le_height {d : ℕ} (hdim : ringKrullDim R = d) {rs : List R}
    (hlen : rs.length = d) (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R) (hrs : IsRegular R rs)
    {m : ℕ} {x : Fin m → R} (hx : ∀ j, x j ∈ maximalIdeal R)
    (hht : (m : ℕ∞) ≤ (Ideal.span (Set.range x)).height) (j : Fin m) :
    IsSMulRegular (R ⧸ Ideal.span (x '' Set.Iio j)) (x j) := by
  have hle𝔪 : Ideal.span (Set.range x) ≤ maximalIdeal R :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hx)
  have hmd : m ≤ d := by
    have h := Ideal.height_le_ringKrullDim_of_ne_top
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hle𝔪)
    rw [hdim] at h
    have : (m : ℕ∞) ≤ d := hht.trans (by exact_mod_cast h)
    exact_mod_cast this
  -- The step: with depth `d - j` modulo `(x i | i < j)`, `x j` is regular.
  have step : ∀ (j : Fin m) (rs' : List R), rs'.length + j = d →
      (∀ r ∈ rs', r ∈ maximalIdeal R) → IsRegular (R ⧸ Ideal.span (x '' Set.Iio j)) rs' →
      IsSMulRegular (R ⧸ Ideal.span (x '' Set.Iio j)) (x j) := by
    intro j rs' hlen' hmem' hrs'
    set I := Ideal.span (x '' Set.Iio j)
    by_contra hreg
    obtain ⟨Q, hQ, hxQ⟩ : ∃ Q ∈ associatedPrimes R (R ⧸ I), x j ∈ Q := by
      have : x j ∈ {r : R | ∃ v : R ⧸ I, v ≠ 0 ∧ r • v = 0} := by
        simp only [IsSMulRegular, Function.Injective, not_forall] at hreg
        obtain ⟨a, b, hab, hne⟩ := hreg
        exact ⟨a - b, sub_ne_zero.mpr hne, by simp only [smul_sub, hab, sub_self]⟩
      rw [← biUnion_associatedPrimes_eq_zero_divisors] at this
      obtain ⟨Q, hQ, h⟩ := Set.mem_iUnion₂.mp this
      exact ⟨Q, hQ, h⟩
    have := hQ.isPrime
    have hIQ : I ≤ Q := by
      simpa [Submodule.annihilator_top, Ideal.annihilator_quotient] using hQ.annihilator_le
    have h1 := length_le_ringKrullDim_quotient_of_mem_associatedPrimes hmem' hrs' hQ
    classical
    set T : Finset R := (Finset.Ioi j).image x
    have hT : ((T.image (Ideal.Quotient.mk Q) : Finset (R ⧸ Q)) : Set (R ⧸ Q)) ⊆
        Ring.jacobson (R ⧸ Q) := by
      intro t ht
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, T] at ht
      obtain ⟨_, ⟨l, -, rfl⟩, rfl⟩ := ht
      rw [← Ideal.jacobson_bot, SetLike.mem_coe, Ideal.mem_jacobson_bot]
      intro y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hu : IsUnit (x l * y + 1) := by
        by_contra hu
        have h1 : x l * y + 1 ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hu
        have h2 : x l * y ∈ maximalIdeal R := Ideal.mul_mem_right _ _ (hx l)
        exact (maximalIdeal.isMaximal R).ne_top
          ((Ideal.eq_top_iff_one _).mpr (by simpa using sub_mem h1 h2))
      simpa using hu.map (Ideal.Quotient.mk Q)
    have h2 := ringKrullDim_le_ringKrullDim_quotient_add_card _ hT
    rw [Finset.coe_image, ← Ideal.map_span,
      ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup Q _)] at h2
    have h3 : ringKrullDim (R ⧸ (Q ⊔ Ideal.span (T : Set R))) ≤ ((d - m : ℕ) : WithBot ℕ∞) := by
      refine Ideal.ringKrullDim_quotient_le_of_forall _ fun P hP hle ↦ ?_
      have hxP : Ideal.span (Set.range x) ≤ P := by
        refine Ideal.span_le.mpr (Set.range_subset_iff.mpr fun l ↦ ?_)
        rcases lt_trichotomy l j with h | rfl | h
        · exact hle (Ideal.mem_sup_left (hIQ (Ideal.subset_span ⟨l, h, rfl⟩)))
        · exact hle (Ideal.mem_sup_left hxQ)
        · exact hle (Ideal.mem_sup_right (Ideal.subset_span (by
            simp only [Finset.coe_image, T]
            exact ⟨l, by simpa using h, rfl⟩)))
      exact Ideal.ringKrullDim_quotient_le_sub hdim (hht.trans (Ideal.height_mono hxP))
    have hcard : (T.image (Ideal.Quotient.mk Q)).card ≤ m - 1 - j :=
      Finset.card_image_le.trans (Finset.card_image_le.trans (Fin.card_Ioi j).le)
    have h4 : (rs'.length : WithBot ℕ∞) ≤ ((d - m : ℕ) : WithBot ℕ∞) + ((m - 1 - j : ℕ) : _) :=
      h1.trans (h2.trans (add_le_add h3 (by exact_mod_cast hcard)))
    have h5 : rs'.length ≤ (d - m) + (m - 1 - j) := by exact_mod_cast h4
    have := j.2
    omega
  -- The depth modulo `(x i | i < k)` is `d - k`.
  have depth : ∀ k (hk : k < m), ∃ rs' : List R, rs'.length + k = d ∧
      (∀ r ∈ rs', r ∈ maximalIdeal R) ∧
      IsRegular (R ⧸ Ideal.span (x '' Set.Iio ⟨k, hk⟩)) rs' := by
    intro k
    induction k with
    | zero =>
      intro hk
      have : x '' Set.Iio ⟨0, hk⟩ = ∅ := by
        rw [Set.image_eq_empty]
        ext l
        simp [Fin.lt_def]
      refine ⟨rs, by omega, hmem, ?_⟩
      rw [this, Ideal.span_empty]
      exact (Submodule.quotEquivOfEqBot ⊥ rfl).isRegular_congr rs |>.mpr hrs
    | succ k IH =>
      intro hk
      obtain ⟨rs', hlen', hmem', hrs'⟩ := IH (by omega)
      change rs'.length + k = d at hlen'
      have hreg := step ⟨k, by omega⟩ rs' hlen' hmem' hrs'
      obtain ⟨rs'', hlen'', hmem'', hrs''⟩ := exists_isRegular_quotient_sup _
        (n := rs'.length - 1) (by omega) hmem' hrs' (hx _) hreg
      refine ⟨rs'', by omega, hmem'', ?_⟩
      have : x '' Set.Iio ⟨k + 1, hk⟩ = insert (x ⟨k, by omega⟩) (x '' Set.Iio ⟨k, by omega⟩) := by
        rw [← Set.image_insert_eq]
        congr 1
        ext l
        simp only [Set.mem_Iio, Set.mem_insert_iff, Fin.lt_def, Fin.ext_iff]
        omega
      rw [this, Ideal.span_insert, sup_comm]
      exact hrs''
  obtain ⟨rs', hlen', hmem', hrs'⟩ := depth j j.2
  exact step j rs' hlen' hmem' hrs'

end IsLocalRing
