/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.Multiplicity
public import ForMathlib.RingTheory.MvPolynomial.Transversal
public import Mathlib.RingTheory.Ideal.Height

-- Used only inside proofs.
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# The number of transversal equations is the height

For a prime `𝔭` of `B = K[X_s : s ∈ σ]`, `K` a field of characteristic `0`,
`MvPolynomial.exists_isTranscendenceBasis_transversal` gives a transcendence basis
`(x_t)_{t ∈ T}` of `B/𝔭` and transversal equations `Q_s ∈ 𝔭`, `s ∉ T`. Their number is `ht 𝔭`:

* `ht 𝔭 ≤ |σ \ T|` by Krull's height theorem, since `𝔭` is minimal over the `Q_s`;
* `|σ \ T| ≤ ht 𝔭` by the length comparison `MvPolynomial.le_of_localLength_eq` against a system
  of parameters of `B_𝔭`, `ht 𝔭` elements of `𝔭` over which `𝔭` is minimal.

As a consequence `ht 𝔭 + trdeg_K (B/𝔭) = |σ|`, the dimension formula for polynomial rings in
characteristic `0`.

## Main statements

* `MvPolynomial.exists_isTranscendenceBasis_transversal_height`: the transversal equations, with
  `ht 𝔭 = |σ \ T|`.
* `MvPolynomial.height_add_trdeg`: `ht 𝔭 + trdeg_K (B/𝔭) = |σ|`.
* `MvPolynomial.exists_transversal_fin`: `ht 𝔭` transversal equations indexed by `Fin (ht 𝔭)`, in
  the form `MvPolynomial.prod_mul_pow_le_localLength` asks for.
-/

@[expose] public section

namespace MvPolynomial

variable {σ K : Type*} [Field K] [CharZero K] [Finite σ]

/-- **The transversal equations number `ht 𝔭`.** The transcendence basis `T` and the equations
`Q_s`, `s ∉ T`, of `MvPolynomial.exists_isTranscendenceBasis_transversal` have `ht 𝔭 = |σ \ T|`. -/
theorem exists_isTranscendenceBasis_transversal_height {ι : Type*} [LinearOrder ι] (b : σ → ι)
    (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime] :
    ∃ T : Finset σ,
      IsTranscendenceBasis K (fun t : (T : Set σ) ↦ Ideal.Quotient.mk 𝔭 (X (t : σ))) ∧
      (∀ s ∉ T, IsAlgebraic (Algebra.adjoin K
        ((fun t ↦ Ideal.Quotient.mk 𝔭 (X t)) '' {t | t ∈ T ∧ b s ≤ b t}))
          (Ideal.Quotient.mk 𝔭 (X s))) ∧
      (∃ Q : σ → MvPolynomial σ K, ∀ s ∉ T, Q s ∈ 𝔭 ∧ pderiv s (Q s) ∉ 𝔭 ∧
        ∀ t, t ≠ s → (t ∉ T ∨ b t < b s) → pderiv t (Q s) = 0) ∧
      𝔭.height = ((T : Set σ)ᶜ).ncard := by
  classical
  have := Fintype.ofFinite σ
  obtain ⟨T, hB, hadapt, Q, hQ, hmin⟩ := exists_isTranscendenceBasis_transversal b 𝔭
  set C := Finset.univ \ T
  have hC : ((T : Set σ)ᶜ) = (C : Set σ) := by
    rw [Finset.coe_sdiff, Finset.coe_univ, Set.compl_eq_univ_sdiff]
  refine ⟨T, hB, hadapt, ⟨Q, hQ⟩, le_antisymm ?_ ?_⟩
  · rw [hC, Set.ncard_coe_finset]
    have h := Ideal.height_le_card_of_mem_minimalPrimes_span_finset (s := C.image Q)
      (by rwa [Finset.coe_image, ← hC])
    exact h.trans (by exact_mod_cast Finset.card_image_le)
  · obtain ⟨S, hS, hcard⟩ := Ideal.exists_finset_card_eq_height_of_isNoetherianRing 𝔭
    rw [← hcard, hC, Set.ncard_coe_finset]
    obtain ⟨ℓ, hℓ⟩ := ENat.ne_top_iff_exists.mp (Ideal.localLength_ne_top_of_mem_minimalPrimes hS)
    set x : Fin S.card → MvPolynomial σ K := fun i ↦ (S.equivFin.symm i : MvPolynomial σ K)
    have hspan : Ideal.span (Set.range x) = Ideal.span (S : Set (MvPolynomial σ K)) := by
      congr 1
      ext y
      refine ⟨?_, fun hy ↦ ⟨S.equivFin ⟨y, hy⟩, by simp [x]⟩⟩
      rintro ⟨i, rfl⟩
      exact (S.equivFin.symm i).2
    set v : Fin C.card → σ := fun α ↦ (C.equivFin.symm α : σ)
    have hvT : ∀ α, v α ∉ T := fun α ↦ (Finset.mem_sdiff.mp (C.equivFin.symm α).2).2
    have hv : Function.Injective v := fun α β h ↦ C.equivFin.symm.injective (Subtype.ext h)
    have hle := le_of_localLength_eq (Q := fun α ↦ Q (v α)) (v := v) (x := x)
      (fun α ↦ (hQ (v α) (hvT α)).1)
      (fun α β hαβ ↦ by
        rw [(hQ (v β) (hvT β)).2.2 (v α) (hv.ne hαβ) (Or.inl (hvT α))]
        exact zero_mem _)
      (fun α ↦ (hQ (v α) (hvT α)).2.1)
      (fun i ↦ hS.1.2 (Ideal.subset_span (S.equivFin.symm i).2))
      (by rw [hspan]; exact hℓ.symm)
    exact_mod_cast hle

/-- **The dimension formula** in characteristic `0`: `ht 𝔭 + trdeg_K (B/𝔭) = |σ|` for a prime `𝔭`
of `B = K[X_s : s ∈ σ]`. -/
theorem height_add_trdeg (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime] :
    𝔭.height + (Algebra.trdeg K (MvPolynomial σ K ⧸ 𝔭)).toENat = Nat.card σ := by
  obtain ⟨T, hB, -, -, hht⟩ := exists_isTranscendenceBasis_transversal_height (fun _ ↦ (0 : ℕ)) 𝔭
  have h := congrArg Cardinal.toENat hB.lift_cardinalMk_eq_trdeg
  rw [Cardinal.toENat_lift, Cardinal.toENat_lift, Finset.coe_sort_coe, Cardinal.mk_coe_finset,
    Cardinal.toENat_nat] at h
  rw [hht, ← h, ← Set.ncard_coe_finset, ← Nat.cast_add, add_comm, Set.ncard_add_ncard_compl]

/-- **`ht 𝔭` transversal equations, indexed by `Fin (ht 𝔭)`**, in the form the multiplicity
estimate `MvPolynomial.prod_mul_pow_le_localLength` asks for: `Q_α ∈ 𝔭` and distinct directions
`v_α` with `∂Q_β/∂X_{v_α} ∈ 𝔭` exactly when `α ≠ β`. The directions are the complement of a
transcendence basis `(x_t)_{t ∈ T}` of `B/𝔭` adapted to the factors `b`. -/
theorem exists_transversal_fin {ι : Type*} [LinearOrder ι] (b : σ → ι)
    (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime] {t : ℕ} (ht : 𝔭.height = t) :
    ∃ T : Finset σ,
      IsTranscendenceBasis K (fun t : (T : Set σ) ↦ Ideal.Quotient.mk 𝔭 (X (t : σ))) ∧
      (∀ s ∉ T, IsAlgebraic (Algebra.adjoin K
        ((fun t ↦ Ideal.Quotient.mk 𝔭 (X t)) '' {t | t ∈ T ∧ b s ≤ b t}))
          (Ideal.Quotient.mk 𝔭 (X s))) ∧
      ∃ v : Fin t → σ, Function.Injective v ∧ Set.range v = (T : Set σ)ᶜ ∧
      ∃ Q : Fin t → MvPolynomial σ K, (∀ α, Q α ∈ 𝔭) ∧
        (∀ α β, α ≠ β → pderiv (v α) (Q β) ∈ 𝔭) ∧ ∀ α, pderiv (v α) (Q α) ∉ 𝔭 := by
  classical
  have := Fintype.ofFinite σ
  obtain ⟨T, hB, hadapt, ⟨Q, hQ⟩, hht⟩ := exists_isTranscendenceBasis_transversal_height b 𝔭
  set C := Finset.univ \ T
  have hC : ((T : Set σ)ᶜ) = (C : Set σ) := by
    rw [Finset.coe_sdiff, Finset.coe_univ, Set.compl_eq_univ_sdiff]
  have hcard : Fintype.card C = t := by
    rw [ht, hC, Set.ncard_coe_finset] at hht
    rw [Fintype.card_coe]
    exact_mod_cast hht.symm
  set e := Fintype.equivFinOfCardEq hcard
  set v : Fin t → σ := fun α ↦ (e.symm α : σ)
  have hvT : ∀ α, v α ∉ T := fun α ↦ (Finset.mem_sdiff.mp (e.symm α).2).2
  have hv : Function.Injective v := fun α β h ↦ e.symm.injective (Subtype.ext h)
  refine ⟨T, hB, hadapt, v, hv, ?_, fun α ↦ Q (v α), fun α ↦ (hQ (v α) (hvT α)).1,
    fun α β hαβ ↦ ?_, fun α ↦ (hQ (v α) (hvT α)).2.1⟩
  · ext s
    refine ⟨?_, fun hs ↦ ?_⟩
    · rintro ⟨α, rfl⟩
      exact hvT α
    · have hsC : s ∈ C := Finset.mem_sdiff.mpr ⟨Finset.mem_univ s, hs⟩
      exact ⟨e ⟨s, hsC⟩, by simp [v]⟩
  · rw [(hQ (v β) (hvT β)).2.2 (v α) (hv.ne hαβ) (Or.inl (hvT α))]
    exact zero_mem _

end MvPolynomial
