/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

-- Used only inside proofs.
import Mathlib.Algebra.CharP.Algebra

/-!
# Transversal equations at the generic point of a prime

Let `𝔭` be a prime of `B = K[X_s : s ∈ σ]`, `K` a field of characteristic `0`, and `x_s` the image
of `X_s` in `B/𝔭`. This file finds a transcendence basis `(x_t)_{t ∈ T}` of `B/𝔭` over `K` and,
for every `s ∉ T`, an equation `Q_s ∈ 𝔭` with `∂Q_s/∂X_s ∉ 𝔭` and `∂Q_s/∂X_t = 0` for the other
`t ∉ T`. The Jacobian matrix `(∂Q_s/∂X_t)_{s, t ∉ T}` is therefore diagonal and invertible modulo
`𝔭`: these are the transversal equations the multiplicity estimate
(`MvPolynomial.prod_mul_pow_le_localLength`) asks for, `|σ| - trdeg_K (B/𝔭)` of them.

This is the Jacobian criterion at the generic point, which Rémond derives from exact sequences of
Kähler differentials (G. Rémond, *Sur le théorème du produit*, J. Théor. Nombres Bordeaux **13**
(2001), §4). In characteristic `0` it has an elementary proof: `x_s` is algebraic over `K[x_T]`,
a relation `f(x_s) = 0` of least degree has `f'(x_s) ≠ 0`, and lifting the coefficients of `f`
to `K[X_T]` gives `Q_s`.

The variables come in factors, `b : σ → ι` with `ι` linearly ordered, and Rémond needs the
equations adapted to the tower of the traces of `𝔭` on the last factors. The transcendence basis is
chosen greedily in order of decreasing factor, so `x_s` is algebraic over the `x_t`, `t ∈ T`, of
factor `≥ b s`, and `Q_s` involves only `X_s` and these `X_t`.

## Main statements

* `MvPolynomial.exists_mem_pderiv_notMem_of_isAlgebraic`: one equation `Q_s` from `x_s` algebraic
  over `K[x_W]`, `s ∉ W`.
* `MvPolynomial.mem_minimalPrimes_of_forall_isAlgebraic`: `𝔭` is minimal over an ideal `J` if
  modulo every prime between them the `X_s` stay algebraic over the `X_t`, `t ∈ T`.
* `MvPolynomial.exists_algebraicIndepOn_isAlgebraic`: the greedy transcendence basis.
* `MvPolynomial.exists_isTranscendenceBasis_isAlgebraic`: a transcendence basis adapted to ordered
  blocks: each `X_s`, `s ∉ T`, is algebraic over the `X_t`, `t ∈ T`, in blocks `≥ b s`.
* `MvPolynomial.exists_isTranscendenceBasis_transversal`: the transcendence basis `T` and the
  equations `Q_s`, `s ∉ T`; `𝔭` is minimal over the `Q_s`.
-/

@[expose] public section

namespace MvPolynomial

variable {σ K : Type*} [Field K]

section Derivative

/-- A polynomial in the variables `W` has no derivative in a variable outside `W`. -/
theorem pderiv_rename_val_eq_zero {W : Set σ} {t : σ} (ht : t ∉ W) (c : MvPolynomial W K) :
    pderiv t (rename Subtype.val c) = 0 := by
  induction c using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p w hp =>
    have : (w : σ) ≠ t := fun h ↦ ht (h ▸ w.2)
    simp [hp, pderiv_X_of_ne this]

/-- The chain rule for `g(X_s)`, `g` a polynomial with coefficients in the variables `W`, against
a variable `t ∉ W`. -/
theorem pderiv_eval₂_rename_val {W : Set σ} {t : σ} (ht : t ∉ W) (s : σ)
    (g : Polynomial (MvPolynomial W K)) :
    pderiv t (g.eval₂ (rename Subtype.val).toRingHom (X s)) =
      (Polynomial.derivative g).eval₂ (rename Subtype.val).toRingHom (X s) * pderiv t (X s) := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add, map_add, hp, hq, Polynomial.derivative_add,
      Polynomial.eval₂_add, add_mul]
  | monomial n c =>
    rw [Polynomial.eval₂_monomial, Polynomial.derivative_monomial, Polynomial.eval₂_monomial,
      Derivation.leibniz, Derivation.leibniz_pow]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, pderiv_rename_val_eq_zero ht,
      smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
    ring

end Derivative

section Lift

/-- The surjection `K[X_W] → K[x_W]`, `x_t = X_t mod 𝔮`. -/
noncomputable def adjoinLift (𝔮 : Ideal (MvPolynomial σ K)) (W : Set σ) :
    MvPolynomial W K →ₐ[K] Algebra.adjoin K ((fun t ↦ Ideal.Quotient.mk 𝔮 (X t)) '' W) :=
  (aeval fun w : W ↦ Ideal.Quotient.mk 𝔮 (X (w : σ))).codRestrict _ fun c ↦ by
    rw [Set.image_eq_range, Algebra.adjoin_range_eq_range_aeval]
    exact ⟨c, rfl⟩

theorem adjoinLift_surjective (𝔮 : Ideal (MvPolynomial σ K)) (W : Set σ) :
    Function.Surjective (adjoinLift 𝔮 W) := by
  rintro ⟨r, hr⟩
  rw [Set.image_eq_range, Algebra.adjoin_range_eq_range_aeval] at hr
  obtain ⟨c, rfl⟩ := hr
  exact ⟨c, rfl⟩

theorem coe_adjoinLift (𝔮 : Ideal (MvPolynomial σ K)) (W : Set σ) (c : MvPolynomial W K) :
    (adjoinLift 𝔮 W c : MvPolynomial σ K ⧸ 𝔮) = Ideal.Quotient.mk 𝔮 (rename Subtype.val c) := by
  change aeval _ c = _
  induction c using MvPolynomial.induction_on with
  | C a => simp; rfl
  | add p q hp hq => simp [hp, hq]
  | mul_X p w hp => simp [hp]

/-- Reducing `g(X_s)`, `g` with coefficients in `K[X_W]`, modulo `𝔮` evaluates the reduced
polynomial at `x_s`. -/
theorem mk_eval₂_rename_val (𝔮 : Ideal (MvPolynomial σ K)) (W : Set σ) (s : σ)
    (p : Polynomial (MvPolynomial W K)) :
    Ideal.Quotient.mk 𝔮 (p.eval₂ (rename Subtype.val).toRingHom (X s)) =
      Polynomial.aeval (Ideal.Quotient.mk 𝔮 (X s))
        (p.map (adjoinLift 𝔮 W).toRingHom) := by
  rw [Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map]
  congr 1
  refine RingHom.ext fun c ↦ ?_
  exact (coe_adjoinLift 𝔮 W c).symm

end Lift

section Equation

variable [CharZero K]

/-- **One transversal equation.** If `x_s = X_s mod 𝔭` is algebraic over `K[x_W]`, `s ∉ W`, then
some `Q ∈ 𝔭` has `∂Q/∂X_s ∉ 𝔭` and involves no variable outside `W` but `X_s`. Moreover `Q` is a
polynomial relation for `X_s mod 𝔮` over `K[X_W] mod 𝔮`, for every `𝔮 ⊆ 𝔭` containing it, and
`Q ∈ K[X_W, X_s]`. -/
theorem exists_mem_pderiv_notMem_of_isAlgebraic (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime]
    {W : Set σ} {s : σ} (hs : s ∉ W)
    (h : IsAlgebraic (Algebra.adjoin K ((fun t ↦ Ideal.Quotient.mk 𝔭 (X t)) '' W))
      (Ideal.Quotient.mk 𝔭 (X s))) :
    ∃ Q ∈ 𝔭, pderiv s Q ∉ 𝔭 ∧ (∀ t, t ≠ s → t ∉ W → pderiv t Q = 0) ∧
      (∀ 𝔮 : Ideal (MvPolynomial σ K), 𝔮 ≤ 𝔭 → Q ∈ 𝔮 →
        IsAlgebraic (Algebra.adjoin K ((fun t ↦ Ideal.Quotient.mk 𝔮 (X t)) '' W))
          (Ideal.Quotient.mk 𝔮 (X s))) ∧ Q ∈ supported K (insert s W) := by
  classical
  set R := Algebra.adjoin K ((fun t ↦ Ideal.Quotient.mk 𝔭 (X t)) '' W)
  set xs := Ideal.Quotient.mk 𝔭 (X s)
  -- A relation of least degree.
  have hex : ∃ n, ∃ f : Polynomial R, f ≠ 0 ∧ Polynomial.aeval xs f = 0 ∧ f.natDegree = n := by
    obtain ⟨f, hf0, hf⟩ := h
    exact ⟨_, f, hf0, hf, rfl⟩
  obtain ⟨f, hf0, hf, hfn⟩ := Nat.find_spec hex
  have hmin : ∀ g : Polynomial R, g ≠ 0 → Polynomial.aeval xs g = 0 →
      Nat.find hex ≤ g.natDegree := fun g hg0 hg ↦ Nat.find_min' hex ⟨g, hg0, hg, rfl⟩
  have : CharZero R := charZero_of_injective_algebraMap (algebraMap K R).injective
  have hd : Polynomial.aeval xs (Polynomial.derivative f) ≠ 0 := by
    intro hd
    have hf1 : f.natDegree ≠ 0 := by
      intro h0
      rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.aeval_C] at hf
      have hc : f.coeff 0 = 0 := Subtype.ext hf
      apply hf0
      rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hc, map_zero]
    have := hmin _ (Polynomial.derivative_ne_zero.mpr hf1) hd
    rw [← hfn] at this
    exact absurd this (not_le.mpr (Polynomial.natDegree_derivative_lt hf1))
  -- Lift the coefficients to `K[X_W]`.
  obtain ⟨g, rfl⟩ := Polynomial.map_surjective _ (adjoinLift_surjective 𝔭 W) f
  set Q := g.eval₂ (rename Subtype.val).toRingHom (X s)
  have hdQ : ∀ 𝔮 : Ideal (MvPolynomial σ K), Ideal.Quotient.mk 𝔮 (pderiv s Q) =
      Polynomial.aeval (Ideal.Quotient.mk 𝔮 (X s))
        (Polynomial.derivative (g.map (adjoinLift 𝔮 W).toRingHom)) := fun 𝔮 ↦ by
    rw [pderiv_eval₂_rename_val hs, pderiv_X_self, mul_one, mk_eval₂_rename_val,
      Polynomial.derivative_map]
  have hd𝔭 : pderiv s Q ∉ 𝔭 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hdQ]
    exact hd
  have hsupp : ∀ g' : Polynomial (MvPolynomial W K),
      g'.eval₂ (rename Subtype.val).toRingHom (X s) ∈ supported K (insert s W) := by
    intro g'
    induction g' using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.eval₂_add]
      exact add_mem hp hq
    | monomial n c =>
      rw [Polynomial.eval₂_monomial]
      refine mul_mem (supported_mono (Set.subset_insert _ _) ?_)
        (pow_mem (X_mem_supported.mpr (Set.mem_insert _ _)) _)
      rw [supported_eq_range_rename]
      exact ⟨c, rfl⟩
  refine ⟨Q, ?_, hd𝔭, fun t hts htW ↦ ?_, fun 𝔮 h𝔮 hQ ↦
    ⟨g.map (adjoinLift 𝔮 W).toRingHom, fun h0 ↦ ?_, ?_⟩, hsupp g⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, mk_eval₂_rename_val]
    exact hf
  · rw [pderiv_eval₂_rename_val htW, pderiv_X_of_ne (Ne.symm hts), mul_zero]
  · apply hd𝔭
    apply h𝔮
    rw [← Ideal.Quotient.eq_zero_iff_mem, hdQ, h0, Polynomial.derivative_zero, map_zero]
  · rw [← mk_eval₂_rename_val, Ideal.Quotient.eq_zero_iff_mem]
    exact hQ

end Equation

section Minimal

/-- **`𝔭` is minimal over `J`** when `(x_t)_{t ∈ T}` is algebraically independent modulo `𝔭` and,
modulo every prime `J ⊆ 𝔮 ⊆ 𝔭`, every `X_s` is algebraic over `K[X_T]`: a proper `𝔮 ⊊ 𝔭` would
make an element of `𝔭 \ 𝔮` satisfy a relation whose constant term is a nonzero polynomial in the
`X_t` lying in `𝔭`. -/
theorem mem_minimalPrimes_of_forall_isAlgebraic (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime]
    {T : Set σ} (hT : AlgebraicIndepOn K (fun t ↦ Ideal.Quotient.mk 𝔭 (X t)) T)
    {J : Ideal (MvPolynomial σ K)} (hJ : J ≤ 𝔭)
    (halg : ∀ 𝔮 : Ideal (MvPolynomial σ K), 𝔮.IsPrime → J ≤ 𝔮 → 𝔮 ≤ 𝔭 → ∀ s,
      IsAlgebraic (Algebra.adjoin K ((fun t ↦ Ideal.Quotient.mk 𝔮 (X t)) '' T))
        (Ideal.Quotient.mk 𝔮 (X s))) :
    𝔭 ∈ J.minimalPrimes := by
  refine ⟨⟨inferInstance, hJ⟩, fun 𝔮 ⟨h𝔮, hJ𝔮⟩ h𝔮𝔭 a ha ↦ ?_⟩
  by_contra haq
  set y : σ → MvPolynomial σ K ⧸ 𝔮 := fun t ↦ Ideal.Quotient.mk 𝔮 (X t) with hy
  have hA : IsAlgebraic (Algebra.adjoin K (y '' T)) (Ideal.Quotient.mk 𝔮 a) := by
    refine IsAlgebraic.adjoin_of_forall_isAlgebraic (s := Set.range y) ?_ ?_
    · rintro _ ⟨⟨s, rfl⟩, -⟩
      exact halg 𝔮 h𝔮 hJ𝔮 h𝔮𝔭 s
    · have hP : Ideal.Quotient.mk 𝔮 a = aeval y a :=
        congrArg (· a) (MvPolynomial.aeval_unique (Ideal.Quotient.mkₐ K 𝔮))
      have hmem : Ideal.Quotient.mk 𝔮 a ∈ Algebra.adjoin K (Set.range y) := by
        rw [hP, Algebra.adjoin_range_eq_range_aeval]
        exact ⟨a, rfl⟩
      exact isAlgebraic_algebraMap (⟨_, hmem⟩ : Algebra.adjoin K (Set.range y))
  have hne : Ideal.Quotient.mk 𝔮 a ∈ nonZeroDivisors (MvPolynomial σ K ⧸ 𝔮) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  obtain ⟨f, hf0, hf⟩ := hA.exists_nonzero_coeff_and_aeval_eq_zero hne
  obtain ⟨p, hp⟩ := adjoinLift_surjective 𝔮 T (f.coeff 0)
  -- Reduce the relation modulo `𝔭`: only the constant term survives.
  set φ := Ideal.Quotient.factorₐ K h𝔮𝔭
  have hφa : (φ : MvPolynomial σ K ⧸ 𝔮 →+* MvPolynomial σ K ⧸ 𝔭) (Ideal.Quotient.mk 𝔮 a) = 0 := by
    simpa [φ, Ideal.Quotient.eq_zero_iff_mem] using ha
  have h1 : φ (f.coeff 0 : MvPolynomial σ K ⧸ 𝔮) = 0 := by
    have := congrArg (φ : MvPolynomial σ K ⧸ 𝔮 →+* MvPolynomial σ K ⧸ 𝔭) hf
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hφa, Polynomial.eval₂_at_zero] at this
    simpa using this
  have h2 : φ (f.coeff 0 : MvPolynomial σ K ⧸ 𝔮) =
      aeval (fun t : T ↦ Ideal.Quotient.mk 𝔭 (X (t : σ))) p := by
    rw [← hp, coe_adjoinLift]
    simp only [φ, Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk]
    rw [← coe_adjoinLift 𝔭 T p]
    rfl
  rw [h2] at h1
  have hp0 : p = 0 := hT.eq_zero_of_aeval_eq_zero p h1
  apply hf0
  rw [← hp, hp0, map_zero]

end Minimal

section Basis

/-- **A greedy transcendence basis adapted to the factors.** For `x : σ → A`, `A` a domain, and
factors `b : σ → ι`, some `T ⊆ S` has `(x_t)_{t ∈ T}` algebraically independent and every `x_s`,
`s ∈ S \ T`, algebraic over the `x_t` with `t ∈ T` in a factor `≥ b s`. -/
theorem exists_algebraicIndepOn_isAlgebraic {A : Type*} [CommRing A] [IsDomain A] [Algebra K A]
    {ι : Type*} [LinearOrder ι] (x : σ → A) (b : σ → ι) (S : Finset σ) :
    ∃ T ⊆ S, AlgebraicIndepOn K x (T : Set σ) ∧ ∀ s ∈ S, s ∉ T →
      IsAlgebraic (Algebra.adjoin K (x '' {t | t ∈ T ∧ b s ≤ b t})) (x s) := by
  classical
  refine Finset.induction_on_max_value (fun s ↦ OrderDual.toDual (b s)) S ?_ ?_
  · refine ⟨∅, subset_rfl, ?_, by simp⟩
    rw [Finset.coe_empty]
    exact algebraicIndependent_empty_type_iff.mpr (algebraMap K A).injective
  · rintro a S haS hmax ⟨T, hTS, hT, halg⟩
    have hmax' : ∀ t ∈ S, b a ≤ b t := fun t ht ↦ OrderDual.toDual_le_toDual.mp (hmax t ht)
    by_cases ha : IsAlgebraic (Algebra.adjoin K (x '' T)) (x a)
    · refine ⟨T, hTS.trans (Finset.subset_insert _ _), hT, fun s hs hsT ↦ ?_⟩
      rcases Finset.mem_insert.mp hs with rfl | hs
      · have : {t | t ∈ T ∧ b s ≤ b t} = (T : Set σ) :=
          Set.ext fun t ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, hmax' t (hTS h)⟩⟩
        rw [this]
        exact ha
      · exact halg s hs hsT
    · refine ⟨insert a T, Finset.insert_subset_insert _ hTS, ?_, fun s hs hsT ↦ ?_⟩
      · rw [Finset.coe_insert]
        exact hT.insert ha
      have hsT' : s ∉ T := fun h ↦ hsT (Finset.mem_insert_of_mem h)
      have hsS : s ∈ S := by
        rcases Finset.mem_insert.mp hs with rfl | h
        · exact absurd (Finset.mem_insert_self _ _) hsT
        · exact h
      refine (halg s hsS hsT').tower_top_of_subalgebra_le
        (Algebra.adjoin_mono (Set.image_mono fun t ht ↦ ?_))
      exact ⟨Finset.mem_insert_of_mem ht.1, ht.2⟩

variable [Finite σ]

/-- **An adapted transcendence basis of `B/𝔭`**: variables `(x_t)_{t ∈ T}` such that each `x_s`,
`s ∉ T`, is algebraic over the `x_t`, `t ∈ T`, with `b t ≥ b s`. -/
theorem exists_isTranscendenceBasis_isAlgebraic {ι : Type*} [LinearOrder ι] (b : σ → ι)
    (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime] :
    ∃ T : Finset σ,
      IsTranscendenceBasis K (fun t : (T : Set σ) ↦ Ideal.Quotient.mk 𝔭 (X (t : σ))) ∧
      ∀ s ∉ T, IsAlgebraic (Algebra.adjoin K
        ((fun t ↦ Ideal.Quotient.mk 𝔭 (X t)) '' {t | t ∈ T ∧ b s ≤ b t}))
          (Ideal.Quotient.mk 𝔭 (X s)) := by
  classical
  have := Fintype.ofFinite σ
  set x : σ → MvPolynomial σ K ⧸ 𝔭 := fun t ↦ Ideal.Quotient.mk 𝔭 (X t) with hx
  obtain ⟨T, -, hT, halg⟩ := exists_algebraicIndepOn_isAlgebraic (K := K) x b Finset.univ
  have halg' : ∀ s ∉ T, IsAlgebraic (Algebra.adjoin K (x '' T)) (x s) := fun s hs ↦
    (halg s (Finset.mem_univ s) hs).tower_top_of_subalgebra_le
      (Algebra.adjoin_mono (Set.image_mono fun t ht ↦ ht.1))
  refine ⟨T, isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr ⟨hT, ?_⟩,
    fun s hs ↦ halg s (Finset.mem_univ s) hs⟩
  change Algebra.IsAlgebraic (Algebra.adjoin K (Set.range fun t : (T : Set σ) ↦ x t)) _
  rw [← Set.image_eq_range]
  constructor
  intro a
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine IsAlgebraic.adjoin_of_forall_isAlgebraic (s := Set.range x) ?_ ?_
  · rintro _ ⟨⟨s, rfl⟩, hs⟩
    exact halg' s fun h ↦ hs ⟨s, h, rfl⟩
  · have hP : Ideal.Quotient.mk 𝔭 P = aeval x P :=
      congrArg (· P) (MvPolynomial.aeval_unique (Ideal.Quotient.mkₐ K 𝔭))
    have hmem : Ideal.Quotient.mk 𝔭 P ∈ Algebra.adjoin K (Set.range x) := by
      rw [hP, Algebra.adjoin_range_eq_range_aeval]
      exact ⟨P, rfl⟩
    exact isAlgebraic_algebraMap (⟨_, hmem⟩ : Algebra.adjoin K (Set.range x))

variable [CharZero K]

/-- **The transversal equations at the generic point of `𝔭`.** Let `b : σ → ι` sort the variables
into linearly ordered factors. There is a transcendence basis `(x_t)_{t ∈ T}` of `B/𝔭` over `K`,
`x_t = X_t mod 𝔭`, adapted to the factors (each `x_s`, `s ∉ T`, is algebraic over the `x_t` with
`t ∈ T` in a factor `≥ b s`), and for each `s ∉ T` an equation `Q_s ∈ 𝔭` with `∂Q_s/∂X_s ∉ 𝔭`
and `∂Q_s/∂X_t = 0` for every other `t` outside `T` or in a factor `< b s`. The prime `𝔭` is
minimal over the `Q_s`. -/
theorem exists_isTranscendenceBasis_transversal {ι : Type*} [LinearOrder ι] (b : σ → ι)
    (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime] :
    ∃ T : Finset σ,
      IsTranscendenceBasis K (fun t : (T : Set σ) ↦ Ideal.Quotient.mk 𝔭 (X (t : σ))) ∧
      (∀ s ∉ T, IsAlgebraic (Algebra.adjoin K
        ((fun t ↦ Ideal.Quotient.mk 𝔭 (X t)) '' {t | t ∈ T ∧ b s ≤ b t}))
          (Ideal.Quotient.mk 𝔭 (X s))) ∧
      ∃ Q : σ → MvPolynomial σ K, (∀ s ∉ T, Q s ∈ 𝔭 ∧ pderiv s (Q s) ∉ 𝔭 ∧
        ∀ t, t ≠ s → (t ∉ T ∨ b t < b s) → pderiv t (Q s) = 0) ∧
        𝔭 ∈ (Ideal.span (Q '' (T : Set σ)ᶜ)).minimalPrimes := by
  classical
  obtain ⟨T, hB, halg⟩ := exists_isTranscendenceBasis_isAlgebraic b 𝔭
  refine ⟨T, hB, halg, ?_⟩
  have hT := hB.1
  · have : ∀ s, ∃ Q : MvPolynomial σ K, s ∉ T → Q ∈ 𝔭 ∧ pderiv s Q ∉ 𝔭 ∧
        (∀ t, t ≠ s → (t ∉ T ∨ b t < b s) → pderiv t Q = 0) ∧
        ∀ 𝔮 : Ideal (MvPolynomial σ K), 𝔮 ≤ 𝔭 → Q ∈ 𝔮 →
          IsAlgebraic (Algebra.adjoin K ((fun t ↦ Ideal.Quotient.mk 𝔮 (X t)) '' T))
            (Ideal.Quotient.mk 𝔮 (X s)) := by
      intro s
      by_cases hs : s ∈ T
      · exact ⟨0, fun h ↦ absurd hs h⟩
      obtain ⟨Q, hQ, hd, h0, h𝔮, -⟩ := exists_mem_pderiv_notMem_of_isAlgebraic 𝔭
        (W := {t | t ∈ T ∧ b s ≤ b t}) (fun h ↦ hs h.1) (halg s hs)
      refine ⟨Q, fun _ ↦ ⟨hQ, hd, fun t hts ht ↦ h0 t hts fun hW ↦ ?_, fun 𝔮 hle hQ𝔮 ↦ ?_⟩⟩
      · rcases ht with ht | ht
        · exact ht hW.1
        · exact absurd hW.2 (not_le.mpr ht)
      · exact (h𝔮 𝔮 hle hQ𝔮).tower_top_of_subalgebra_le
          (Algebra.adjoin_mono (Set.image_mono fun t ht ↦ ht.1))
    choose Q hQ using this
    refine ⟨Q, fun s hs ↦ (hQ s hs).imp_right fun h ↦ h.imp_right fun h ↦ h.1, ?_⟩
    have hJ : Ideal.span (Q '' (T : Set σ)ᶜ) ≤ 𝔭 :=
      Ideal.span_le.mpr (Set.image_subset_iff.mpr fun s hs ↦ (hQ s hs).1)
    refine mem_minimalPrimes_of_forall_isAlgebraic 𝔭 hT hJ fun 𝔮 _ hJ𝔮 h𝔮𝔭 s ↦ ?_
    by_cases hs : s ∈ T
    · exact isAlgebraic_algebraMap (⟨_, Algebra.subset_adjoin ⟨s, Finset.mem_coe.mpr hs, rfl⟩⟩ :
        Algebra.adjoin K ((fun t ↦ Ideal.Quotient.mk 𝔮 (X t)) '' (T : Set σ)))
    · exact (hQ s hs).2.2.2 𝔮 h𝔮𝔭 (hJ𝔮 (Ideal.subset_span ⟨s, hs, rfl⟩))

end Basis

end MvPolynomial
