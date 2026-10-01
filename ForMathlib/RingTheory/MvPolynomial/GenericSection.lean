/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.MultiprojectiveDegree
public import ForMathlib.RingTheory.MvPolynomial.Saturation
public import Mathlib.RingTheory.Localization.FractionRing

-- Used only inside proofs.
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# The generic hypersurface section

Let `𝔭` be a multihomogeneous prime of `K[X]`, `X` in blocks, not containing the irrelevant ideal
`𝔪`. Let `U = ∑_m u_m X^m` be the generic form of multidegree `e`, with coefficients in
`C = K[u]`, and `L = Frac(C)`. G. Rémond's Lemma 2.12 (*Élimination multihomogène*, Chapter 5 of
Nesterenko–Philippon (eds.), *Introduction to algebraic independence theory*, LNM 1752 (2001))
passes from `𝔭` to the extension `𝔮 = 𝔄_{(e)}(𝔭) L[X]` of the characteristic ideal of index
`(e)`, a section of `V(𝔭)` by the generic hypersurface `U = 0` over `L`:

* `𝔮` is prime when `𝔈_{(e)}(𝔭) = 0` (`MvPolynomial.isPrime_map_charIdeal`);
* `H_𝔮(T) = H_𝔭(T) - H_𝔭(T - e)` (`MvPolynomial.hilbertPoly_map_charIdeal`);
* `d_β(𝔮) = ∑_i e_i d_{β + ε_i}(𝔭)` (`MvPolynomial.multidegree_map_charIdeal`).

`𝔄_{(e)}(𝔭)` is the saturation of `𝔭 C[X] + (U)` by `𝔪`, and saturation commutes with the
localization `C[X] → L[X]` (`MvPolynomial.map_saturation`). So `𝔮` is the saturation of
`𝔭 L[X] + (U)`, which has the same Hilbert polynomial
(`MvPolynomial.hilbertPoly_saturation`). The ideal `𝔭 L[X]` is prime, it has the Hilbert
polynomial of `𝔭` (`MvPolynomial.hilbertPoly_map`), and it does not contain `U`: a monomial of
multidegree `e` lies outside `𝔭`. Then `H_{𝔭 L[X] + (U)} = H_𝔭(T) - H_𝔭(T - e)` by the exact
sequence of `MvPolynomial.hilbertPoly_sup_span_singleton_of_isPrime`.

## Main statements

* `MvPolynomial.exists_monomial_notMem_of_not_le`: if `𝔪 ⊄ 𝔭`, every multidegree has a monomial
  outside `𝔭`.
* `MvPolynomial.genericForm_notMem_map_map_C`: such a monomial keeps `U_l` outside `𝔭[u]`.
* `MvPolynomial.isPrime_map_map_fractionRing`: `𝔭 L[X]` is prime.
* `MvPolynomial.hilbertPoly_map_charIdeal`, `MvPolynomial.multidegree_map_charIdeal`: the Hilbert
  polynomial and the degrees of `𝔮`.
* `MvPolynomial.not_le_of_elimIdeal_eq_bot`, `MvPolynomial.isPrime_map_charIdeal`: if
  `𝔈_d(𝔭) = 0`, then `𝔪 ⊄ 𝔭` and `𝔄_d(𝔭) L[X]` is prime.
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {σ ι K : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι} [Field K]

section Prime

variable {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime]

omit [𝔭.IsPrime] in
/-- If the irrelevant ideal is not contained in the ideal `𝔭`, then every block has a variable
outside `𝔭`. -/
theorem exists_forall_X_notMem_of_not_le (h : ¬irrelevantIdeal K b ≤ 𝔭) :
    ∃ t : ι → σ, (∀ i, b (t i) = i) ∧ ∀ i, X (t i) ∉ 𝔭 := by
  classical
  rw [irrelevantIdeal, Ideal.span_le, Set.not_subset] at h
  obtain ⟨_, ⟨c, hc, rfl⟩, hc𝔭⟩ := h
  obtain ⟨t, ht, rfl⟩ := exists_eq_sum_single_of_weight_eq_one (mem_blockMonomials.mp hc)
  have hprod : (monomial (∑ i, Finsupp.single (t i) 1) 1 : MvPolynomial σ K) =
      ∏ i, X (t i) := by
    simpa using monomial_sum_single_eq_prod (S := K) t fun _ ↦ 1
  refine ⟨t, ht, fun i hi ↦ hc𝔭 ?_⟩
  change (monomial (∑ i, Finsupp.single (t i) 1) 1 : MvPolynomial σ K) ∈ 𝔭
  rw [hprod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact 𝔭.mul_mem_right _ hi

/-- If the irrelevant ideal is not contained in the prime `𝔭`, then in every multidegree `e`
there is a monomial outside `𝔭`. -/
theorem exists_monomial_notMem_of_not_le (h : ¬irrelevantIdeal K b ≤ 𝔭) (e : ι → ℕ) :
    ∃ m ∈ blockMonomials b e, monomial m (1 : K) ∉ 𝔭 := by
  classical
  obtain ⟨t, ht, hX⟩ := exists_forall_X_notMem_of_not_le h
  refine ⟨∑ i, Finsupp.single (t i) (e i), mem_blockMonomials.mpr ?_, ?_⟩
  · simp only [map_sum, Finsupp.weight_single, multiWeight, ht]
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  · rw [monomial_sum_single_eq_prod]
    intro hmem
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hX i (Ideal.IsPrime.mem_of_pow_mem inferInstance _ hi)

/-- If `𝔪 ⊄ 𝔭`, the Hilbert polynomial of the multihomogeneous prime `𝔭` is not zero. -/
theorem hilbertPoly_ne_zero_of_not_le (hb : Function.Surjective b)
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (h : ¬irrelevantIdeal K b ≤ 𝔭) :
    hilbertPoly b 𝔭 ≠ 0 := by
  intro h0
  obtain ⟨d₀, hd₀⟩ := exists_forall_le_hilbertFunction_eq_hilbertPoly hb h𝔭
  have h1 := hd₀ d₀ le_rfl
  rw [h0, map_zero, Nat.cast_eq_zero, hilbertFunction] at h1
  obtain ⟨m, hm, hm𝔭⟩ := exists_monomial_notMem_of_not_le h d₀
  have hlt : 𝔭.restrictScalars K ⊓ weightedHomogeneousSubmodule K (multiWeight b) d₀ <
      weightedHomogeneousSubmodule K (multiWeight b) d₀ :=
    lt_of_le_of_ne inf_le_right fun heq ↦ hm𝔭 (by
      have : monomial m (1 : K) ∈ weightedHomogeneousSubmodule K (multiWeight b) d₀ :=
        isWeightedHomogeneous_monomial _ _ _ (mem_blockMonomials.mp hm)
      rw [← heq] at this
      exact this.1)
  have := Submodule.finrank_lt_finrank_of_lt hlt
  omega

end Prime

section Comm

variable {R S₁ S₂ : Type*} [CommSemiring R]

omit [DecidableEq ι] in
theorem commAlgEquiv_map_C (p : MvPolynomial S₁ R) :
    commAlgEquiv R S₁ S₂ (map C p) = C p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [map_C, commAlgEquiv_C, map_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p n hp => rw [map_mul, map_mul, hp, map_X, commAlgEquiv_X, map_mul]

end Comm

omit [Fintype σ] in
/-- The constants `C s`, `s ≠ 0`, of `K[u][X]` are not in `𝔭[u]` for a proper ideal `𝔭`. -/
theorem C_notMem_map_map_C {P : Type*} {I : Ideal (MvPolynomial σ K)} (hI : I ≠ ⊤)
    {s : MvPolynomial P K} (hs : s ≠ 0) :
    (C s : MvPolynomial σ (MvPolynomial P K)) ∉ I.map (map C) := by
  rw [mem_map_map_C_iff]
  push Not
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hs
  refine ⟨m, fun h ↦ hI (Ideal.eq_top_of_isUnit_mem _ h ?_)⟩
  have : (commAlgEquiv K P σ).symm (C s) = map C s := by
    rw [AlgEquiv.symm_apply_eq, commAlgEquiv_map_C]
  rw [this, coeff_map]
  exact (isUnit_iff_ne_zero.mpr hm).map C

/-- A generic form is not in `𝔭[u]` if one of its monomials is not in `𝔭`. -/
theorem genericForm_notMem_map_map_C {κ : Type*} {d : κ → ι → ℕ} {I : Ideal (MvPolynomial σ K)}
    {l : κ} {m : σ →₀ ℕ} (hm : m ∈ blockMonomials b (d l)) (hmI : monomial m (1 : K) ∉ I) :
    genericForm K b d l ∉ I.map (map C) := by
  classical
  set ψ : MvPolynomial σ (MvPolynomial (GenericVar b d) K) →+* MvPolynomial σ K :=
    map (aeval fun v : GenericVar b d ↦ if v = ⟨l, ⟨m, hm⟩⟩ then (1 : K) else 0).toRingHom
  have hψC : ψ.comp (map C) = RingHom.id _ := by
    refine RingHom.ext fun p ↦ ?_
    rw [RingHom.comp_apply, map_map, RingHom.id_apply]
    convert map_id p
    exact RingHom.ext fun a ↦ by simp
  intro hU
  have h1 : ψ (genericForm K b d l) ∈ I := by
    have := Ideal.mem_map_of_mem ψ hU
    rwa [Ideal.map_map, hψC, Ideal.map_id] at this
  have h2 : ψ (genericForm K b d l) = monomial m 1 := by
    rw [genericForm, map_sum, Finset.sum_eq_single ⟨m, hm⟩]
    · simp [ψ]
    · intro m' _ hm'
      have hne : (⟨l, m'⟩ : GenericVar b d) ≠ ⟨l, ⟨m, hm⟩⟩ :=
        fun h ↦ hm' (eq_of_heq (Sigma.mk.inj h).2)
      simp [ψ, hne]
    · simp
  exact hmI (h2 ▸ h1)

section Section

variable (K b) in
/-- The coefficient ring `K[u]` of one generic form of multidegree `e`. -/
abbrev GenericRing (e : ι → ℕ) : Type _ := MvPolynomial (GenericVar b fun _ : Unit ↦ e) K

variable {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime] {e : ι → ℕ}

attribute [local instance] algebraMvPolynomial

omit [Fintype σ] in
/-- The nonzero constants of `K[u]` avoid `𝔭[u]`. -/
theorem disjoint_map_map_C {P : Type*} :
    Disjoint (((nonZeroDivisors (MvPolynomial P K)).map (C (σ := σ))) :
      Set (MvPolynomial σ (MvPolynomial P K)))
      ((𝔭.map (map (C : K →+* MvPolynomial P K)) : Ideal _) :
        Set (MvPolynomial σ (MvPolynomial P K))) := by
  rw [Set.disjoint_left]
  rintro _ ⟨s, hs, rfl⟩
  exact C_notMem_map_map_C (Ideal.IsPrime.ne_top inferInstance) (nonZeroDivisors.ne_zero hs)

omit [Fintype σ] in
/-- The extension `𝔭 L[X]` of `𝔭` to `L = Frac(K[u])` is prime. -/
theorem isPrime_map_map_fractionRing {P : Type*} :
    ((𝔭.map (map (C : K →+* MvPolynomial P K))).map
      (map (algebraMap (MvPolynomial P K) (FractionRing (MvPolynomial P K))))).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint
    ((nonZeroDivisors (MvPolynomial P K)).map (C (σ := σ)))
    (MvPolynomial σ (FractionRing (MvPolynomial P K))) _ isPrime_map_map_C disjoint_map_map_C

omit [Fintype σ] in
theorem comap_map_map_fractionRing {P : Type*} :
    ((𝔭.map (map (C : K →+* MvPolynomial P K))).map
      (map (algebraMap (MvPolynomial P K) (FractionRing (MvPolynomial P K))))).comap
        (map (algebraMap (MvPolynomial P K) (FractionRing (MvPolynomial P K)))) =
      𝔭.map (map C) :=
  IsLocalization.under_map_of_isPrime_disjoint
    ((nonZeroDivisors (MvPolynomial P K)).map (C (σ := σ)))
    (MvPolynomial σ (FractionRing (MvPolynomial P K))) isPrime_map_map_C disjoint_map_map_C

omit [Fintype σ] [𝔭.IsPrime] in
theorem map_map_map_fractionRing {P : Type*} :
    (𝔭.map (map (C : K →+* MvPolynomial P K))).map
      (map (algebraMap (MvPolynomial P K) (FractionRing (MvPolynomial P K)))) =
      𝔭.map (map (algebraMap K (FractionRing (MvPolynomial P K)))) := by
  rw [Ideal.map_map]
  congr 1
  refine RingHom.ext fun p ↦ ?_
  rw [RingHom.comp_apply, map_map, IsScalarTower.algebraMap_eq K (MvPolynomial P K)
    (FractionRing (MvPolynomial P K)), algebraMap_eq]

/-- **The Hilbert polynomial of the generic hypersurface section** (Rémond, LNM 1752, Ch. 5,
Lemma 2.12, first assertion). Let `𝔭` be a multihomogeneous prime not containing the irrelevant
ideal, `U = ∑_m u_m X^m` the generic form of multidegree `e`, and `L = K(u)`. The extension
`𝔮 = 𝔄_{(e)}(𝔭) L[X]` of the characteristic ideal has `H_𝔮(T) = H_𝔭(T) - H_𝔭(T - e)`: it is the
saturation of `𝔭 L[X] + (U)`, and `U ∉ 𝔭 L[X]`. -/
theorem hilbertPoly_map_charIdeal (hb : Function.Surjective b)
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (hm : ¬irrelevantIdeal K b ≤ 𝔭)
    (e : ι → ℕ) :
    hilbertPoly b ((charIdeal K b (fun _ : Unit ↦ e) 𝔭).map
      (map (algebraMap (GenericRing K b e) (FractionRing (GenericRing K b e))))) =
      hilbertPoly b 𝔭 - shiftPoly e (hilbertPoly b 𝔭) := by
  set φ : MvPolynomial σ (GenericRing K b e) →+*
    MvPolynomial σ (FractionRing (GenericRing K b e)) := map (algebraMap _ _)
  set 𝔭L := (𝔭.map (map (C : K →+* GenericRing K b e))).map φ
  have h𝔭L : 𝔭L.IsPrime := isPrime_map_map_fractionRing
  have hU : φ (genericForm K b (fun _ : Unit ↦ e) ()) ∉ 𝔭L := by
    obtain ⟨m, hm, hm𝔭⟩ := exists_monomial_notMem_of_not_le hm e
    intro h
    exact genericForm_notMem_map_map_C (d := fun _ : Unit ↦ e) (l := ()) hm hm𝔭
      ((comap_map_map_fractionRing (𝔭 := 𝔭) (P := GenericVar b fun _ : Unit ↦ e)).le h)
  have hUe : IsWeightedHomogeneous (multiWeight b) (φ (genericForm K b (fun _ : Unit ↦ e) ())) e :=
    fun c hc ↦ isWeightedHomogeneous_genericForm (R := K) (b := b) (d := fun _ : Unit ↦ e) ()
      (show (genericForm K b (fun _ : Unit ↦ e) ()).coeff c ≠ 0 from
        fun h ↦ hc (by simp only [φ, coeff_map, h, map_zero]))
  have h𝔭Lh : 𝔭L.IsWeightedHomogeneous (multiWeight b) := (h𝔭.map C).map _
  have hJ : (genericIdeal K b (fun _ : Unit ↦ e) 𝔭).map φ =
      𝔭L ⊔ Ideal.span {φ (genericForm K b (fun _ : Unit ↦ e) ())} := by
    rw [genericIdeal, Ideal.map_sup, Ideal.map_span, ← Set.range_comp, Set.range_unique]
    rfl
  have hJh : ((genericIdeal K b (fun _ : Unit ↦ e) 𝔭).map φ).IsWeightedHomogeneous
      (multiWeight b) := (isWeightedHomogeneous_genericIdeal h𝔭).map _
  rw [charIdeal_eq_saturation, map_saturation (nonZeroDivisors (GenericRing K b e)),
    hilbertPoly_saturation hb hJh, hJ,
    hilbertPoly_sup_span_singleton_of_isPrime hb h𝔭Lh hUe hU]
  have : 𝔭L = 𝔭.map (map (algebraMap K (FractionRing (GenericRing K b e)))) :=
    map_map_map_fractionRing
  rw [this, hilbertPoly_map _ h𝔭]

/-- **The degrees of the generic hypersurface section** (Rémond, LNM 1752, Ch. 5, Lemma 2.12,
second assertion: `deg 𝔮 = deg 𝔭 * e`). In every degree `|β| ≥ deg H_𝔭 - 1`:
`d_β(𝔮) = ∑ i, e i · d_{β + ε_i}(𝔭)`. -/
theorem multidegree_map_charIdeal (hb : Function.Surjective b)
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (hm : ¬irrelevantIdeal K b ≤ 𝔭)
    (e : ι → ℕ) {β : ι →₀ ℕ} (hβ : (hilbertPoly b 𝔭).totalDegree - 1 ≤ β.degree) :
    multidegree b ((charIdeal K b (fun _ : Unit ↦ e) 𝔭).map
      (map (algebraMap (GenericRing K b e) (FractionRing (GenericRing K b e))))) β =
      ∑ i, (e i : ℚ) * multidegree b 𝔭 (β + Finsupp.single i 1) := by
  rw [multidegree, hilbertPoly_map_charIdeal hb h𝔭 hm e, coeff_sub_shiftPoly e _ hβ,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [multidegree, prod_factorial_add_single]
  ring

omit [𝔭.IsPrime] in
/-- If the eliminant ideal vanishes, `𝔭` does not contain the irrelevant ideal. -/
theorem not_le_of_elimIdeal_eq_bot {κ : Type*} {d : κ → ι → ℕ}
    (h : elimIdeal K b d 𝔭 = ⊥) : ¬irrelevantIdeal K b ≤ 𝔭 := by
  intro hle
  have h1 : (1 : MvPolynomial (GenericVar b d) K) ∈ elimIdeal K b d 𝔭 := by
    refine mem_elimIdeal.mpr ⟨1, fun g hg ↦ ?_⟩
    rw [pow_one, ← map_irrelevantIdeal C] at hg
    rw [map_one, mul_one]
    exact (le_sup_left : 𝔭.map (map C) ≤ genericIdeal K b d 𝔭) (Ideal.map_mono hle hg)
  rw [h, Ideal.mem_bot] at h1
  exact one_ne_zero h1

omit [𝔭.IsPrime] in
/-- The nonzero constants avoid `𝔄_d(𝔭)` when `𝔈_d(𝔭) = 0`. -/
theorem disjoint_charIdeal {κ : Type*} {d : κ → ι → ℕ} (h : elimIdeal K b d 𝔭 = ⊥) :
    Disjoint (((nonZeroDivisors (MvPolynomial (GenericVar b d) K)).map (C (σ := σ))) :
      Set (MvPolynomial σ (MvPolynomial (GenericVar b d) K))) (charIdeal K b d 𝔭 : Set _) := by
  rw [Set.disjoint_left]
  rintro _ ⟨s, hs, rfl⟩ hmem
  have : s ∈ elimIdeal K b d 𝔭 := hmem
  rw [h, Ideal.mem_bot] at this
  exact nonZeroDivisors.ne_zero hs this

/-- **The generic hypersurface section is prime** (Rémond, LNM 1752, Ch. 5, Lemma 2.12): if
`𝔈_d(𝔭) = 0`, the extension of `𝔄_d(𝔭)` to `L[X]`, `L = Frac(K[u])`, is prime. -/
theorem isPrime_map_charIdeal {κ : Type*} {d : κ → ι → ℕ} (h : elimIdeal K b d 𝔭 = ⊥) :
    ((charIdeal K b d 𝔭).map (map (algebraMap (MvPolynomial (GenericVar b d) K)
      (FractionRing (MvPolynomial (GenericVar b d) K))))).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint
    ((nonZeroDivisors (MvPolynomial (GenericVar b d) K)).map (C (σ := σ))) _ _
    (isPrime_charIdeal (not_le_of_elimIdeal_eq_bot h)) (disjoint_charIdeal h)

/-- `𝔄_d(𝔭) L[X] ∩ K[X] = 𝔭` when `𝔈_d(𝔭) = 0` (Rémond, LNM 1752, Ch. 5, proof of
Lemma 2.12). -/
theorem comap_map_charIdeal {κ : Type*} {d : κ → ι → ℕ} (h : elimIdeal K b d 𝔭 = ⊥) :
    ((charIdeal K b d 𝔭).map (map (algebraMap (MvPolynomial (GenericVar b d) K)
      (FractionRing (MvPolynomial (GenericVar b d) K))))).comap
        (map (algebraMap K (FractionRing (MvPolynomial (GenericVar b d) K)))) = 𝔭 := by
  have hcomp : (map (algebraMap K (FractionRing (MvPolynomial (GenericVar b d) K))) :
      MvPolynomial σ K →+* _) = (map (algebraMap (MvPolynomial (GenericVar b d) K)
        (FractionRing (MvPolynomial (GenericVar b d) K)))).comp (map C) := by
    refine RingHom.ext fun p ↦ ?_
    rw [RingHom.comp_apply, map_map, IsScalarTower.algebraMap_eq K (MvPolynomial (GenericVar b d) K)
      (FractionRing (MvPolynomial (GenericVar b d) K)), algebraMap_eq]
  rw [hcomp, ← Ideal.comap_comap]
  have h2 := IsLocalization.under_map_of_isPrime_disjoint
    ((nonZeroDivisors (MvPolynomial (GenericVar b d) K)).map (C (σ := σ)))
    (MvPolynomial σ (FractionRing (MvPolynomial (GenericVar b d) K)))
    (isPrime_charIdeal (not_le_of_elimIdeal_eq_bot h)) (disjoint_charIdeal h)
  have h2' : ((charIdeal K b d 𝔭).map (map (algebraMap (MvPolynomial (GenericVar b d) K)
      (FractionRing (MvPolynomial (GenericVar b d) K))))).comap
        (map (algebraMap (MvPolynomial (GenericVar b d) K)
          (FractionRing (MvPolynomial (GenericVar b d) K)))) = charIdeal K b d 𝔭 := h2
  rw [h2', comap_map_C_charIdeal (not_le_of_elimIdeal_eq_bot h)]

omit [𝔭.IsPrime] in
/-- `𝔄_d(𝔭) L[X]` is multihomogeneous. -/
theorem isWeightedHomogeneous_map_charIdeal {κ : Type*} [Finite κ] {d : κ → ι → ℕ}
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) :
    ((charIdeal K b d 𝔭).map (map (algebraMap (MvPolynomial (GenericVar b d) K)
      (FractionRing (MvPolynomial (GenericVar b d) K))))).IsWeightedHomogeneous
        (multiWeight b) := by
  rw [charIdeal_eq_saturation]
  exact (isWeightedHomogeneous_saturation (isWeightedHomogeneous_genericIdeal h𝔭)).map _

end Section

end MvPolynomial

end
