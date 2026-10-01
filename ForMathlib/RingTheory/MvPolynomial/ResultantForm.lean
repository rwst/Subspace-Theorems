/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.Associativity
public import ForMathlib.RingTheory.MvPolynomial.EliminantForm
public import ForMathlib.RingTheory.MvPolynomial.GradedPiece
public import ForMathlib.RingTheory.MvPolynomial.Saturation
public import ForMathlib.RingTheory.UniqueFactorizationDomain.CharForm

-- Used only inside proofs.
import Mathlib.Algebra.Order.Sub.Prod
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal

/-!
# Resultant forms of multihomogeneous ideals

Let `I` be a multihomogeneous ideal of `B = K[X]` and `d` an index of generic forms. The graded
pieces `(B[d]/I[d])_k` are finite modules over the factorial ring `K[d]`; their characteristic
forms `χ` (`Module.charForm`) stabilize for large `k`, and the common value is the *resultant
form* `res_d(I)` of G. Rémond, *Élimination multihomogène*, Chapter 5 of Nesterenko–Philippon
(eds.), *Introduction to algebraic independence theory*, LNM 1752 (2001), §3.2.

## Main statements

* `MvPolynomial.charIdeal_colon`: `𝔄_d(J) : f = 𝔄_d(J : f)` for `f ∈ K[X]`, from Rémond's
  Lemma 2.3. This replaces the flatness of `B_𝔭 → (B[d]/(U))_{𝔄_d(𝔭)}` in Rémond's proof of
  Thm 3.3.
* `MvPolynomial.associated_charForm_genPiece`: for a form `f` of multidegree `a`,
  `χ((B[d]/J[d])_{k+a}) = χ((B[d]/(J : f)[d])_k) χ((B[d]/(J + (f))[d])_{k+a})` for large `k`.
* `MvPolynomial.isUnit_charForm_genPiece`: if `𝔈_d(J)` lies in no principal prime, `χ` is
  eventually a unit.
* `MvPolynomial.exists_associated_charForm_genPiece`: **Rémond's Lemma 3.2**, `χ` stabilizes for a
  prime all of whose larger primes are small. Instead of an extra generic form we multiply by a
  variable outside the prime in each block.
* `MvPolynomial.resForm`: the resultant form `res_d(I)`, the eventual value of `χ`.
* `MvPolynomial.associated_resForm_prod`: **Rémond's Theorem 3.3**, for `deg H_I ≤ r - 1`,
  `χ((B[d]/I[d])_k)` is eventually `res_d(I)`, and `res_d(I) = ∏_𝔭 res_d(𝔭)^{ℓ(B_𝔭/I_𝔭)}` over
  the multihomogeneous primes `𝔭 ⊇ I` with `𝔪 ⊄ 𝔭` and `deg H_𝔭 = r - 1`.
-/

@[expose] public section

open Ideal
open scoped Finset

namespace MvPolynomial

section Colon

variable {σ R P : Type*} [CommRing R]

/-- Colon ideals commute with extending the coefficients `R → R[P]`. -/
theorem map_map_C_colon (I : Ideal (MvPolynomial σ R)) (f : MvPolynomial σ R) :
    (I.map (map (C : R →+* MvPolynomial P R))).colon {map C f} =
      (I.colon {f}).map (map (C : R →+* MvPolynomial P R)) := by
  ext p
  have hf : (commAlgEquiv R P σ).symm (map C f) = C f := by
    rw [AlgEquiv.symm_apply_eq, commAlgEquiv_C]
  simp only [Submodule.mem_colon_singleton, smul_eq_mul, mem_map_map_C_iff, map_mul, hf,
    mul_comm _ (C f), coeff_C_mul, mul_comm f]

end Colon

section Generic

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
variable {R : Type*} [CommRing R] {κ : Type*} {d : κ → ι → ℕ}

/-- **The colon of a characteristic ideal** by a polynomial of `R[X]`:
`𝔄_d(J) : f = 𝔄_d(J : f)`. -/
theorem charIdeal_colon (J : Ideal (MvPolynomial σ R)) (f : MvPolynomial σ R) :
    (charIdeal R b d J).colon {map C f} = charIdeal R b d (J.colon {f}) := by
  ext g
  rw [Submodule.mem_colon_singleton, smul_eq_mul, mem_charIdeal_iff_subst,
    mem_charIdeal_iff_subst, ← map_map_C_colon]
  simp only [Submodule.mem_colon_singleton, smul_eq_mul, map_mul, subst_map_C, mul_assoc]

omit [Fintype σ] [Fintype ι] in
theorem IsWeightedHomogeneous.map_ringHom {f : MvPolynomial σ R} {a : ι → ℕ}
    (hf : IsWeightedHomogeneous (multiWeight b) f a) {S : Type*} [CommRing S] (φ : R →+* S) :
    IsWeightedHomogeneous (multiWeight b) (map φ f) a := by
  intro c hc
  refine hf fun h ↦ hc ?_
  rw [coeff_map, h, map_zero]

end Generic

section Prime

variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]

/-- A nonzero prime ideal of a factorial ring inside a principal prime is that principal prime;
so a nonprincipal one lies in no principal prime. -/
theorem _root_.Ideal.IsPrime.not_le_span_singleton {P : Ideal A} [hP : P.IsPrime] (hP0 : P ≠ ⊥)
    (hnp : ¬P.IsPrincipal) {π : A} (hπ : Prime π) : ¬P ≤ span {π} := by
  intro hle
  obtain ⟨q, hqP, hq⟩ := hP.exists_mem_prime_of_ne_bot hP0
  have hπq : Associated π q := hπ.associated_of_dvd hq (mem_span_singleton.mp (hle hqP))
  refine hnp ⟨π, le_antisymm hle ?_⟩
  rw [← span_singleton_le_iff_mem, ← span_singleton_eq_span_singleton.mpr hπq] at hqP
  exact hqP

end Prime

section Pieces

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] (b : σ → ι)
variable (K : Type*) [Field K] {κ : Type*} (d : κ → ι → ℕ)

/-- The `K[d]`-module `(B[d]/J[d])_k`. -/
abbrev genPiece (J : Ideal (MvPolynomial σ K)) (k : ι → ℕ) : Type _ :=
  gradedPiece b (genericIdeal K b d J) k

variable {b K d} [Finite κ]

local notation "Kd" => MvPolynomial (GenericVar b d) K

/-- **`χ` is multiplicative along `0 → (B/(J : f))(-a) → B/J → B/(J + (f)) → 0`** in large
multidegrees. -/
theorem associated_charForm_genPiece {J : Ideal (MvPolynomial σ K)}
    (hJ : J.IsWeightedHomogeneous (multiWeight b)) {f : MvPolynomial σ K} {a : ι → ℕ}
    (hf : IsWeightedHomogeneous (multiWeight b) f a) :
    ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k →
      Associated (Module.charForm (Kd) (genPiece b K d J (k + a)))
        (Module.charForm (Kd) (genPiece b K d (J.colon {f}) k) *
          Module.charForm (Kd) (genPiece b K d (J ⊔ span {f}) (k + a))) := by
  set I := genericIdeal K b d J
  set I' := genericIdeal K b d (J.colon {f})
  set F : MvPolynomial σ Kd := map C f
  have hF : IsWeightedHomogeneous (multiWeight b) F a := hf.map_ringHom C
  have hI : I.IsWeightedHomogeneous (multiWeight b) := isWeightedHomogeneous_genericIdeal hJ
  have hle : I' ≤ I.colon {F} := by
    refine sup_le ?_ ?_
    · rw [← map_map_C_colon]
      exact Submodule.colon_mono le_sup_left le_rfl
    · refine (le_sup_right : span (Set.range (genericForm K b d)) ≤ I).trans
        fun x hx ↦ ?_
      rw [Submodule.mem_colon_singleton, smul_eq_mul]
      exact I.mul_mem_right _ hx
  have h : ∀ g ∈ I', g * F ∈ I := fun g hg ↦ by
    have := Submodule.mem_colon_singleton.mp (hle hg)
    rwa [smul_eq_mul] at this
  obtain ⟨k₀, hk₀⟩ := exists_forall_le_mem_of_mem_saturation (b := b)
    (isWeightedHomogeneous_genericIdeal (d := d) (hJ.colon hf))
  have hsup : genericIdeal K b d (J ⊔ span {f}) = I ⊔ span {F} := by
    rw [genericIdeal, Ideal.map_sup, Ideal.map_span, Set.image_singleton, sup_right_comm]
    rfl
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hinj : ∀ g ∈ weightedHomogeneousSubmodule _ (multiWeight b) k, g * F ∈ I → g ∈ I' := by
    intro g hg hgF
    have hmem : g ∈ (charIdeal K b d J).colon {F} := by
      rw [Submodule.mem_colon_singleton, smul_eq_mul]
      exact le_saturation (b := b) I hgF
    rw [charIdeal_colon, charIdeal_eq_saturation] at hmem
    exact hk₀ k hk g hmem hg
  have e : genPiece b K d (J ⊔ span {f}) (k + a) ≃ₗ[Kd]
      gradedPiece b (I ⊔ span {F}) (k + a) := Submodule.quotEquivOfEq _ _ (by rw [hsup])
  rw [Module.charForm_congr e]
  exact Module.associated_charForm_of_exact _ _ (gradedPiece.mulMap_injective hF h hinj)
    (gradedPiece.factor_surjective _ _) (gradedPiece.exact_mulMap_factor hI hF h k)

/-- **The eliminant ideal annihilates the pieces of large degree** of `B[d]/J[d]`. -/
theorem exists_elimIdeal_le_annihilator (J : Ideal (MvPolynomial σ K)) :
    ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k →
      elimIdeal K b d J ≤ Module.annihilator Kd (genPiece b K d J k) := by
  obtain ⟨N, hN⟩ := exists_saturation_eq_colon (b := b) (genericIdeal K b d J)
  refine ⟨fun _ ↦ N, fun k hk c hc ↦ ?_⟩
  rw [elimIdeal, mem_comap, charIdeal_eq_saturation, hN] at hc
  refine Module.mem_annihilator.mpr fun x ↦ ?_
  obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ x
  rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  change c • (g : MvPolynomial σ Kd) ∈ genericIdeal K b d J
  rw [smul_eq_C_mul]
  have hg : (g : MvPolynomial σ Kd) ∈ irrelevantIdeal Kd b ^ N :=
    mem_irrelevantIdeal_pow (fun i ↦ hk i) g.2
  have := Submodule.mem_colon.mp hc _ hg
  rwa [smul_eq_mul] at this

/-- `χ((B[d]/J[d])_k)` is eventually nonzero when the eliminant ideal is nonzero. -/
theorem exists_charForm_genPiece_ne_zero (J : Ideal (MvPolynomial σ K))
    (h0 : elimIdeal K b d J ≠ ⊥) :
    ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k → Module.charForm Kd (genPiece b K d J k) ≠ 0 := by
  obtain ⟨k₀, hk₀⟩ := exists_elimIdeal_le_annihilator (d := d) J
  exact ⟨k₀, fun k hk ↦ Module.charForm_ne_zero (ne_bot_of_le_ne_bot h0 (hk₀ k hk))⟩

/-- **`χ` is eventually a unit** when the eliminant ideal is nonzero and lies in no principal
prime (e.g. it is `⊤`, or a nonzero nonprincipal prime). -/
theorem isUnit_charForm_genPiece (J : Ideal (MvPolynomial σ K))
    (h0 : elimIdeal K b d J ≠ ⊥) (h : ∀ π, Prime π → ¬elimIdeal K b d J ≤ span {π}) :
    ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k → IsUnit (Module.charForm (Kd) (genPiece b K d J k)) := by
  obtain ⟨k₀, hk₀⟩ := exists_elimIdeal_le_annihilator (d := d) J
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hann := hk₀ k hk
  have hne : Module.annihilator (Kd) (genPiece b K d J k) ≠ ⊥ :=
    ne_bot_of_le_ne_bot h0 hann
  refine isUnit_of_dvd_one ((UniqueFactorizationMonoid.dvd_iff_emultiplicity_le
    (Module.charForm_ne_zero hne)).mpr fun π hπ ↦ ?_)
  rw [Module.emultiplicity_charForm hne hπ]
  obtain ⟨c, hc, hcπ⟩ := Set.not_subset.mp (h π hπ)
  rw [Module.primeLength_eq_zero hπ (hann hc) (by rwa [SetLike.mem_coe, mem_span_singleton] at hcπ)]
  exact zero_le

omit [Finite κ] in
theorem isUnit_charForm_genPiece_top (k : ι → ℕ) :
    IsUnit (Module.charForm Kd (genPiece b K d ⊤ k)) := by
  have : genericIdeal K b d (⊤ : Ideal (MvPolynomial σ K)) = ⊤ := by
    rw [genericIdeal, Ideal.map_top, top_sup_eq]
  have : Subsingleton (genPiece b K d ⊤ k) := by
    unfold genPiece gradedPiece
    rw [this, Submodule.restrictScalars_top, Submodule.comap_top]
    infer_instance
  exact Module.isUnit_charForm_of_subsingleton

/-- **`χ` along a prime filtration** `J = J_0 ⊂ ⋯ ⊂ J_n = K[X]`, `J_j = J_{j-1} + (f_j)`,
`(J_{j-1} : f_j) = 𝔮_j` (Rémond's Lemma 2.6 for `B/J`): for large `k`,
`χ((B[d]/J[d])_k) = ∏_j χ((B[d]/𝔮_j[d])_{k - a_j})`, with `a_j = deg f_j`, and
`ℓ((K[X]/J)_𝔭) = ∑_j ℓ((K[X]/𝔮_j)_𝔭)` for every prime `𝔭`. -/
theorem exists_charForm_filtration {J : Ideal (MvPolynomial σ K)}
    (hJ : J.IsWeightedHomogeneous (multiWeight b)) :
    ∃ (n : ℕ) (a : Fin n → ι → ℕ) (𝔮 : Fin n → Ideal (MvPolynomial σ K)),
      (∀ j, (𝔮 j).IsPrime ∧ (𝔮 j).IsWeightedHomogeneous (multiWeight b) ∧ J ≤ 𝔮 j) ∧
      (∀ (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime],
        Ideal.localLength 𝔭 J = ∑ j, Ideal.localLength 𝔭 (𝔮 j)) ∧
      ∃ k₀ : ι → ℕ, (∀ j, a j ≤ k₀) ∧ ∀ k, k₀ ≤ k →
        Associated (Module.charForm Kd (genPiece b K d J k))
          (∏ j, Module.charForm Kd (genPiece b K d (𝔮 j) (k - a j))) := by
  induction J using IsNoetherian.induction with
  | hgt J IH =>
  by_cases hJt : J = ⊤
  · subst hJt
    refine ⟨0, Fin.elim0, Fin.elim0, fun j ↦ j.elim0, fun 𝔭 _ ↦ by simp [Ideal.localLength_top],
      0, fun j ↦ j.elim0, fun k _ ↦ ?_⟩
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    exact associated_one_iff_isUnit.mpr (isUnit_charForm_genPiece_top k)
  obtain ⟨f, e, hf, -, hfJ, hprime⟩ := exists_isPrime_colon hJ (isWeightedHomogeneous_top _)
    (fun h ↦ hJt (top_le_iff.mp h))
  have hJ' : Ideal.IsWeightedHomogeneous (multiWeight b) (J ⊔ Ideal.span {f}) :=
    hJ.sup (isWeightedHomogeneous_span fun x hx ↦ ⟨e, (Set.mem_singleton_iff.mp hx) ▸ hf⟩)
  have hlt : J < J ⊔ Ideal.span {f} := lt_of_le_of_ne le_sup_left fun h ↦
    hfJ (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  obtain ⟨n, a, 𝔮, h𝔮, hℓ, k₀, hk₀a, hk₀⟩ := IH _ hlt hJ'
  obtain ⟨k₁, hk₁⟩ := associated_charForm_genPiece (d := d) hJ hf
  refine ⟨n + 1, Fin.cons e a, Fin.cons (J.colon {f}) 𝔮, fun j ↦ ?_, fun 𝔭 _ ↦ ?_,
    k₀ ⊔ (k₁ + e), fun j ↦ ?_, fun k hk ↦ ?_⟩
  · refine Fin.cases ⟨hprime, hJ.colon hf, le_colon_singleton J f⟩ (fun j ↦ ?_) j
    exact ⟨(h𝔮 j).1, (h𝔮 j).2.1, le_sup_left.trans (h𝔮 j).2.2⟩
  · rw [Fin.sum_univ_succ, Fin.cons_zero, Ideal.localLength_eq_add_colon 𝔭 J f, hℓ 𝔭]
    simp only [Fin.cons_succ]
  · refine Fin.cases ?_ (fun j ↦ ?_) j
    · exact (le_add_self).trans le_sup_right
    · exact (hk₀a j).trans le_sup_left
  · have hek : e ≤ k := (le_add_self.trans le_sup_right).trans hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + e := ⟨k - e, (tsub_add_cancel_of_le hek).symm⟩
    have hk' : k₁ ≤ k' := le_of_add_le_add_right (le_sup_right.trans hk)
    rw [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_zero, add_tsub_cancel_right]
    exact (hk₁ k' hk').trans ((hk₀ _ (le_sup_left.trans hk)).mul_left _)

end Pieces

section Stable

/-- **Stabilization**: a function of multidegrees which is eventually invariant (up to units)
under each step `k ↦ k + ε_i` is eventually constant. -/
theorem exists_associated_of_forall_step {ι α : Type*} [Finite ι] [DecidableEq ι] [Monoid α]
    {g : (ι → ℕ) → α}
    (h : ∀ i, ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k → Associated (g (k + Pi.single i 1)) (g k)) :
    ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k → Associated (g k) (g k₀) := by
  have := Fintype.ofFinite ι
  choose ks hks using h
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ι → ℕ, k₀ = Finset.univ.sup ks := ⟨_, rfl⟩
  have hks₀ : ∀ i, ks i ≤ k₀ := fun i ↦ hk₀ ▸ Finset.le_sup (Finset.mem_univ i)
  refine ⟨k₀, ?_⟩
  suffices key : ∀ m k, k₀ ≤ k → ∑ i, (k i - k₀ i) = m → Associated (g k) (g k₀) from
    fun k hk ↦ key _ k hk rfl
  intro m
  induction m with
  | zero =>
    intro k hk hm
    have : k = k₀ := funext fun i ↦ by
      have h1 := (Finset.sum_eq_zero_iff.mp hm) i (Finset.mem_univ i)
      have h2 : k₀ i ≤ k i := hk i
      omega
    rw [this]
  | succ m ih =>
    intro k hk hm
    obtain ⟨i, hi⟩ : ∃ i, k₀ i < k i := by
      by_contra! hc
      have : ∑ i, (k i - k₀ i) = 0 := Finset.sum_eq_zero fun i _ ↦ by have := hc i; omega
      omega
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + Pi.single i 1 := ⟨k - Pi.single i 1, funext fun j ↦ by
      rcases eq_or_ne j i with rfl | hj
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
        omega
      · simp [hj]⟩
    have hk' : k₀ ≤ k' := fun j ↦ by
      have := hk j
      rcases eq_or_ne j i with rfl | hj
      · simp only [Pi.add_apply, Pi.single_eq_same] at hi
        exact Nat.lt_succ_iff.mp hi
      · simpa [hj] using this
    have hsum : ∑ j, (k' j - k₀ j) = m := by
      have : ∀ j, (k' + Pi.single i 1 : ι → ℕ) j - k₀ j =
          (k' j - k₀ j) + (Pi.single i 1 : ι → ℕ) j := fun j ↦ by
        have := hk' j
        rcases eq_or_ne j i with rfl | hj
        · simp only [Pi.add_apply, Pi.single_eq_same]
          rw [Nat.sub_add_comm this]
        · simp [hj]
      simp only [this, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
        ite_true] at hm
      omega
    exact (hks i k' ((hks₀ i).trans hk')).trans (ih k' hk' hsum)

universe u

variable {σ ι : Type u} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
  {K : Type u} [Field K] {κ : Type u} [Finite κ] {d : κ → ι → ℕ}

local notation "Kd" => MvPolynomial (GenericVar b d) K

/-- **`χ` is eventually a unit for small primes**: those containing the irrelevant ideal, and
those with `e_J(𝔮) ≤ r_J(d) - 2` for some `J` (Rémond's Cor. 2.15 (3)). -/
theorem isUnit_charForm_genPiece_of_small (hb : Function.Surjective b)
    {𝔮 : Ideal (MvPolynomial σ K)} [𝔮.IsPrime] (h𝔮 : 𝔮.IsWeightedHomogeneous (multiWeight b))
    (hs : irrelevantIdeal K b ≤ 𝔮 ∨ ∃ J : Finset ι, blockRank 𝔮 b J + 2 ≤ numForms d J + #J) :
    ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k → IsUnit (Module.charForm Kd (genPiece b K d 𝔮 k)) := by
  by_cases hm : irrelevantIdeal K b ≤ 𝔮
  · have htop := elimIdeal_eq_top_of_le (d := d) hm
    refine isUnit_charForm_genPiece 𝔮 (by simp [htop]) fun π hπ hle ↦ hπ.not_isUnit ?_
    rw [htop, top_le_iff, span_singleton_eq_top] at hle
    exact hle
  obtain ⟨J, hJ⟩ := hs.resolve_left hm
  have hprime := isPrime_elimIdeal (d := d) hm
  have h0 : elimIdeal K b d 𝔮 ≠ ⊥ := fun h ↦ by
    have := ((elimIdeal_eq_bot_iff hb h𝔮 d).mp h).2 J
    omega
  exact isUnit_charForm_genPiece 𝔮 h0 fun π hπ ↦
    hprime.not_le_span_singleton h0 (not_isPrincipal_elimIdeal hb h𝔮 d hm hJ) hπ

/-- `χ` is eventually a unit when all multihomogeneous primes above `J` are small. -/
theorem isUnit_charForm_genPiece_of_forall (hb : Function.Surjective b)
    {J : Ideal (MvPolynomial σ K)} (hJ : J.IsWeightedHomogeneous (multiWeight b))
    (hs : ∀ (𝔮 : Ideal (MvPolynomial σ K)) [𝔮.IsPrime], 𝔮.IsWeightedHomogeneous (multiWeight b) →
      J ≤ 𝔮 → irrelevantIdeal K b ≤ 𝔮 ∨ ∃ J : Finset ι, blockRank 𝔮 b J + 2 ≤ numForms d J + #J) :
    ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k → IsUnit (Module.charForm Kd (genPiece b K d J k)) := by
  obtain ⟨n, a, 𝔮, h𝔮, -, k₀, -, hk₀⟩ := exists_charForm_filtration (d := d) hJ
  have hu : ∀ j, ∃ k₁ : ι → ℕ, ∀ k, k₁ ≤ k →
      IsUnit (Module.charForm Kd (genPiece b K d (𝔮 j) k)) := fun j ↦ by
    have := (h𝔮 j).1
    exact isUnit_charForm_genPiece_of_small hb (h𝔮 j).2.1 (hs _ (h𝔮 j).2.1 (h𝔮 j).2.2)
  choose k₁ hk₁ using hu
  refine ⟨k₀ ⊔ Finset.univ.sup fun j ↦ k₁ j + a j, fun k hk ↦ ?_⟩
  refine ((hk₀ k (le_sup_left.trans hk)).isUnit_iff).mpr (IsUnit.prod_univ_iff.mpr fun j ↦ ?_)
  refine hk₁ j _ fun i ↦ ?_
  have := ((Finset.le_sup (f := fun j ↦ k₁ j + a j) (Finset.mem_univ j)).trans
    (le_sup_right.trans hk)) i
  simp only [Pi.add_apply] at this
  simp only [Pi.sub_apply]
  omega

theorem colon_singleton_eq_self {A : Type*} [CommRing A] {P : Ideal A} [hP : P.IsPrime] {x : A}
    (hx : x ∉ P) : P.colon {x} = P := by
  ext y
  rw [Submodule.mem_colon_singleton, smul_eq_mul]
  exact ⟨fun h ↦ (hP.mem_or_mem h).resolve_right hx, fun h ↦ P.mul_mem_right x h⟩

omit [Finite κ] in
theorem charForm_genPiece_congr {J J' : Ideal (MvPolynomial σ K)} (h : J = J') (k : ι → ℕ) :
    Module.charForm Kd (genPiece b K d J k) = Module.charForm Kd (genPiece b K d J' k) := by
  subst h
  rfl

/-- **Rémond's Lemma 3.2**: for a multihomogeneous prime `𝔭` all of whose strictly larger
multihomogeneous primes are small (e.g. `ht 𝔭 ≥ n - r + 1`), `χ((B[d]/𝔭[d])_k)` is
eventually constant. Instead of an extra generic form we multiply by a variable `X_s ∉ 𝔭`
of each block. -/
theorem exists_associated_charForm_genPiece (hb : Function.Surjective b)
    {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime] (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b))
    (hs : ∀ (𝔮 : Ideal (MvPolynomial σ K)) [𝔮.IsPrime], 𝔮.IsWeightedHomogeneous (multiWeight b) →
      𝔭 < 𝔮 → irrelevantIdeal K b ≤ 𝔮 ∨ ∃ J : Finset ι, blockRank 𝔮 b J + 2 ≤ numForms d J + #J) :
    ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k →
      Associated (Module.charForm Kd (genPiece b K d 𝔭 k))
        (Module.charForm Kd (genPiece b K d 𝔭 k₀)) := by
  by_cases hm : irrelevantIdeal K b ≤ 𝔭
  · obtain ⟨k₀, hk₀⟩ := isUnit_charForm_genPiece_of_small (d := d) hb h𝔭 (Or.inl hm)
    exact ⟨k₀, fun k hk ↦ (associated_one_iff_isUnit.mpr (hk₀ k hk)).trans
      (associated_one_iff_isUnit.mpr (hk₀ k₀ le_rfl)).symm⟩
  obtain ⟨t, ht, htp⟩ := exists_forall_X_notMem_of_not_le hm
  refine exists_associated_of_forall_step fun i ↦ ?_
  have hX : IsWeightedHomogeneous (multiWeight b) (X (t i) : MvPolynomial σ K)
      (Pi.single i 1) := by
    have := isWeightedHomogeneous_X K (multiWeight b) (t i)
    simpa [multiWeight, ht i] using this
  obtain ⟨k₁, hk₁⟩ := associated_charForm_genPiece (d := d) h𝔭 hX
  obtain ⟨k₂, hk₂⟩ := isUnit_charForm_genPiece_of_forall (d := d) hb
    (h𝔭.sup (isWeightedHomogeneous_span fun x hx ↦
      ⟨Pi.single i 1, (Set.mem_singleton_iff.mp hx) ▸ hX⟩))
    fun 𝔮 _ h𝔮h hle ↦ hs 𝔮 h𝔮h (lt_of_le_of_ne (le_sup_left.trans hle) fun h ↦ htp i
      (h ▸ hle (mem_sup_right (mem_span_singleton_self _))))
  refine ⟨k₁ ⊔ k₂, fun k hk ↦ ?_⟩
  have := hk₁ k (le_sup_left.trans hk)
  rw [charForm_genPiece_congr (colon_singleton_eq_self (htp i))] at this
  refine this.trans ?_
  have hu := hk₂ (k + Pi.single i 1) ((le_sup_right.trans hk).trans le_self_add)
  simpa using (Associated.refl _).mul_left _ |>.trans
    ((associated_one_iff_isUnit.mpr hu).mul_left _) |>.trans (by rw [mul_one])

omit [Fintype ι] [DecidableEq ι] in
theorem _root_.numForms_univ {κ : Type*} (d : κ → ι → ℕ) : numForms d Set.univ = Nat.card κ :=
  Nat.card_congr (Equiv.subtypeUnivEquiv fun _ _ _ ↦ Set.mem_univ _)

omit [Fintype σ] [Finite κ] in
/-- For a prime with nonzero Hilbert polynomial, the variables have rank `deg H_𝔮 + q`. -/
theorem blockRank_univ [Finite σ] (hb : Function.Surjective b) {𝔮 : Ideal (MvPolynomial σ K)}
    [𝔮.IsPrime] (h𝔮 : 𝔮.IsWeightedHomogeneous (multiWeight b)) (hne : hilbertPoly b 𝔮 ≠ 0) :
    blockRank 𝔮 b ((Finset.univ : Finset ι) : Set ι) =
      (hilbertPoly b 𝔮).totalDegree + Fintype.card ι := by
  obtain ⟨α, -, hdeg, h, -⟩ := exists_coeff_hilbertPoly_ne_zero_blockRank hb h𝔮 hne
    (subset_refl Finset.univ)
  rw [← h, ← hdeg, Finsupp.degree_eq_sum, Finset.card_univ]

omit [Finite κ] in
/-- A prime of dimension `deg H_𝔮 ≤ r - 2` is small. -/
theorem small_of_totalDegree (hb : Function.Surjective b) {𝔮 : Ideal (MvPolynomial σ K)}
    [𝔮.IsPrime] (h𝔮 : 𝔮.IsWeightedHomogeneous (multiWeight b))
    (h : ¬irrelevantIdeal K b ≤ 𝔮 → (hilbertPoly b 𝔮).totalDegree + 2 ≤ Nat.card κ) :
    irrelevantIdeal K b ≤ 𝔮 ∨ ∃ J : Finset ι, blockRank 𝔮 b J + 2 ≤ numForms d J + #J := by
  by_cases hm : irrelevantIdeal K b ≤ 𝔮
  · exact Or.inl hm
  refine Or.inr ⟨Finset.univ, ?_⟩
  rw [blockRank_univ hb h𝔮 (hilbertPoly_ne_zero_of_not_le hb h𝔮 hm), Finset.coe_univ,
    numForms_univ, Finset.card_univ]
  have := h hm
  omega

variable (b K d) in
omit [Finite κ] in
/-- The **resultant form** `res_d(I)` (Rémond, LNM 1752, Ch. 5, §3.2): the eventual value of
`χ((B[d]/I[d])_k)` up to units, when it stabilizes (`0` otherwise). -/
noncomputable def resForm (I : Ideal (MvPolynomial σ K)) : Kd :=
  open Classical in
  if h : ∃ (c : Kd) (k₀ : ι → ℕ), ∀ k, k₀ ≤ k →
    Associated (Module.charForm Kd (genPiece b K d I k)) c then h.choose else 0

omit [Finite κ] in
theorem associated_resForm_of {I : Ideal (MvPolynomial σ K)} {c : Kd}
    (h : ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k → Associated (Module.charForm Kd (genPiece b K d I k)) c) :
    Associated (resForm b K d I) c := by
  obtain ⟨k₀, hk₀⟩ := h
  have h' : ∃ (c : Kd) (k₀ : ι → ℕ), ∀ k, k₀ ≤ k →
      Associated (Module.charForm Kd (genPiece b K d I k)) c := ⟨c, k₀, hk₀⟩
  rw [resForm, dite_eq_left h']
  obtain ⟨k₁, hk₁⟩ := h'.choose_spec
  exact (hk₁ (k₀ ⊔ k₁) le_sup_right).symm.trans (hk₀ _ le_sup_left)

omit [Finite κ] in
theorem associated_resForm {I : Ideal (MvPolynomial σ K)}
    (h : ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k → Associated (Module.charForm Kd (genPiece b K d I k))
      (Module.charForm Kd (genPiece b K d I k₀))) :
    ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k →
      Associated (Module.charForm Kd (genPiece b K d I k)) (resForm b K d I) := by
  obtain ⟨k₀, hk₀⟩ := h
  exact ⟨k₀, fun k hk ↦ (hk₀ k hk).trans (associated_resForm_of ⟨k₀, hk₀⟩).symm⟩

/-- **Rémond's Theorem 3.3** (LNM 1752, Ch. 5): for a multihomogeneous ideal `I` of dimension
`deg H_I ≤ r - 1` (i.e. `ht I ≥ n - r + 1`), `χ((B[d]/I[d])_k)` is eventually
`∏_𝔭 res_d(𝔭)^{ℓ(B_𝔭/I_𝔭)}`, the product over the multihomogeneous primes `𝔭 ⊇ I` with
`𝔪 ⊄ 𝔭` and `deg H_𝔭 = r - 1`. -/
theorem exists_associated_charForm_prod_resForm (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree + 1 ≤ Nat.card κ) :
    ∃ (S : Finset (Ideal (MvPolynomial σ K))) (ℓ : Ideal (MvPolynomial σ K) → ℕ),
      (∀ 𝔭, 𝔭 ∈ S ↔ 𝔭.IsPrime ∧ 𝔭.IsWeightedHomogeneous (multiWeight b) ∧ I ≤ 𝔭 ∧
        ¬irrelevantIdeal K b ≤ 𝔭 ∧ (hilbertPoly b 𝔭).totalDegree + 1 = Nat.card κ) ∧
      (∀ 𝔭 ∈ S, ∀ [𝔭.IsPrime], Ideal.localLength 𝔭 I = ℓ 𝔭) ∧
      ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k → Associated (Module.charForm Kd (genPiece b K d I k))
        (∏ 𝔭 ∈ S, resForm b K d 𝔭 ^ ℓ 𝔭) := by
  classical
  obtain ⟨n, a, 𝔮, h𝔮, hℓ, k₀, -, hk₀⟩ := exists_charForm_filtration (d := d) hI
  obtain ⟨Q, hQ⟩ : ∃ Q : Ideal (MvPolynomial σ K) → Prop, ∀ 𝔭, Q 𝔭 ↔
      ¬irrelevantIdeal K b ≤ 𝔭 ∧ (hilbertPoly b 𝔭).totalDegree + 1 = Nat.card κ :=
    ⟨_, fun _ ↦ Iff.rfl⟩
  have hdeg : ∀ j, (hilbertPoly b (𝔮 j)).totalDegree ≤ (hilbertPoly b I).totalDegree := fun j ↦
    totalDegree_hilbertPoly_le_of_le hb hI (h𝔮 j).2.1 (h𝔮 j).2.2
  -- A top-dimensional prime contains no smaller `𝔮 j`.
  have hkey : ∀ (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime],
      𝔭.IsWeightedHomogeneous (multiWeight b) → Q 𝔭 → ∀ j, 𝔮 j ≤ 𝔭 → 𝔮 j = 𝔭 := by
    intro 𝔭 _ h𝔭 hQ𝔭 j hj
    rw [hQ] at hQ𝔭
    by_contra hj'
    have := (h𝔮 j).1
    have := totalDegree_hilbertPoly_lt_of_lt hb (h𝔮 j).2.1 h𝔭 (lt_of_le_of_ne hj hj')
      (hilbertPoly_ne_zero_of_not_le hb h𝔭 hQ𝔭.1)
    have := hdeg j
    omega
  have hj : ∀ j, ∃ k₁ : ι → ℕ, ∀ k, k₁ ≤ k →
      Associated (Module.charForm Kd (genPiece b K d (𝔮 j) k))
        (if Q (𝔮 j) then resForm b K d (𝔮 j) else 1) := by
    intro j
    have := (h𝔮 j).1
    split_ifs with hQj
    · rw [hQ] at hQj
      refine associated_resForm (exists_associated_charForm_genPiece hb (h𝔮 j).2.1
        fun 𝔮' _ h𝔮' hlt ↦ small_of_totalDegree hb h𝔮' fun hm ↦ ?_)
      have := totalDegree_hilbertPoly_lt_of_lt hb (h𝔮 j).2.1 h𝔮' hlt
        (hilbertPoly_ne_zero_of_not_le hb h𝔮' hm)
      omega
    · rw [hQ] at hQj
      push Not at hQj
      obtain ⟨k₁, hk₁⟩ := isUnit_charForm_genPiece_of_small (d := d) hb (h𝔮 j).2.1
        (small_of_totalDegree hb (h𝔮 j).2.1 fun hm ↦ by have := hQj hm; have := hdeg j; omega)
      exact ⟨k₁, fun k hk ↦ associated_one_iff_isUnit.mpr (hk₁ k hk)⟩
  choose k₁ hk₁ using hj
  refine ⟨(Finset.univ.filter fun j ↦ Q (𝔮 j)).image 𝔮, fun 𝔭 ↦ #{j | 𝔮 j = 𝔭},
    fun 𝔭 ↦ ?_, fun 𝔭 h𝔭 _ ↦ ?_, k₀ ⊔ Finset.univ.sup fun j ↦ k₁ j + a j, fun k hk ↦ ?_⟩
  · simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hQj, rfl⟩
      exact ⟨(h𝔮 j).1, (h𝔮 j).2.1, (h𝔮 j).2.2, (hQ _).mp hQj⟩
    · rintro ⟨hprime, h𝔭, hI𝔭, hm, hn⟩
      have hpos := Ideal.localLength_ne_zero (𝔭 := 𝔭) hI𝔭
      rw [hℓ 𝔭] at hpos
      obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos
      by_cases hj' : 𝔮 j ≤ 𝔭
      · have heq := hkey 𝔭 h𝔭 ((hQ 𝔭).mpr ⟨hm, hn⟩) j hj'
        exact ⟨j, heq ▸ (hQ 𝔭).mpr ⟨hm, hn⟩, heq⟩
      · exact absurd (Ideal.localLength_of_not_le hj') hj
  · simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h𝔭
    obtain ⟨j₀, hQj₀, rfl⟩ := h𝔭
    change _ = ((#{j | 𝔮 j = 𝔮 j₀} : ℕ) : ℕ∞)
    rw [hℓ, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hj : 𝔮 j = 𝔮 j₀
    · rw [hj]
      simp [Ideal.localLength_self]
    · rw [Ideal.localLength_of_not_le fun h ↦ hj (hkey _ (h𝔮 j₀).2.1 hQj₀ j h)]
      simp [hj]
  · refine (hk₀ k (le_sup_left.trans hk)).trans ?_
    refine (Associated.prod _ _ _ fun j _ ↦ hk₁ j _ fun i ↦ ?_).trans (Associated.of_eq ?_)
    · have := ((Finset.le_sup (f := fun j ↦ k₁ j + a j) (Finset.mem_univ j)).trans
        (le_sup_right.trans hk)) i
      simp only [Pi.add_apply] at this
      simp only [Pi.sub_apply]
      omega
    · rw [← Finset.prod_filter, Finset.prod_comp (f := resForm b K d) (g := 𝔮)]
      refine Finset.prod_congr rfl fun 𝔭 h𝔭 ↦ ?_
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h𝔭
      obtain ⟨j₀, hQj₀, rfl⟩ := h𝔭
      rw [Finset.filter_filter]
      congr 2
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
      exact fun h ↦ h ▸ hQj₀

/-- **Rémond's Theorem 3.3**, with the resultant form: for `deg H_I ≤ r - 1`, `χ((B[d]/I[d])_k)`
is eventually `res_d(I)`, and `res_d(I) = ∏_𝔭 res_d(𝔭)^{ℓ(B_𝔭/I_𝔭)}` up to a unit. -/
theorem associated_resForm_prod (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree + 1 ≤ Nat.card κ) :
    (∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k →
      Associated (Module.charForm Kd (genPiece b K d I k)) (resForm b K d I)) ∧
    ∃ (S : Finset (Ideal (MvPolynomial σ K))) (ℓ : Ideal (MvPolynomial σ K) → ℕ),
      (∀ 𝔭, 𝔭 ∈ S ↔ 𝔭.IsPrime ∧ 𝔭.IsWeightedHomogeneous (multiWeight b) ∧ I ≤ 𝔭 ∧
        ¬irrelevantIdeal K b ≤ 𝔭 ∧ (hilbertPoly b 𝔭).totalDegree + 1 = Nat.card κ) ∧
      (∀ 𝔭 ∈ S, ∀ [𝔭.IsPrime], Ideal.localLength 𝔭 I = ℓ 𝔭) ∧
      Associated (resForm b K d I) (∏ 𝔭 ∈ S, resForm b K d 𝔭 ^ ℓ 𝔭) := by
  obtain ⟨S, ℓ, hS, hℓ, k₀, hk₀⟩ := exists_associated_charForm_prod_resForm (d := d) hb hI hdim
  have := associated_resForm_of ⟨k₀, hk₀⟩
  exact ⟨⟨k₀, fun k hk ↦ (hk₀ k hk).trans this.symm⟩, S, ℓ, hS, hℓ, this⟩

/-- The eliminant ideal of a prime with `deg H_𝔭 ≤ r - 1` is nonzero (Thm. 2.13 (1) with
`J = ι`). -/
theorem elimIdeal_ne_bot_of_totalDegree (hb : Function.Surjective b)
    {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime] (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b 𝔭).totalDegree + 1 ≤ Nat.card κ) : elimIdeal K b d 𝔭 ≠ ⊥ := by
  intro h0
  obtain ⟨hm, h⟩ := (elimIdeal_eq_bot_iff hb h𝔭 d).mp h0
  have := h Finset.univ
  have hr := blockRank_univ hb h𝔭 (hilbertPoly_ne_zero_of_not_le hb h𝔭 hm)
  rw [Finset.coe_univ] at hr
  rw [Finset.coe_univ, numForms_univ, Finset.card_univ] at this
  rw [hr] at this
  omega

/-- **Resultant forms are nonzero**: `res_d(I) ≠ 0` for `deg H_I ≤ r - 1`. -/
theorem resForm_ne_zero (hb : Function.Surjective b) {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree + 1 ≤ Nat.card κ) : resForm b K d I ≠ 0 := by
  obtain ⟨-, S, ℓ, hS, -, hassoc⟩ := associated_resForm_prod (d := d) hb hI hdim
  rw [hassoc.ne_zero_iff, Finset.prod_ne_zero_iff]
  intro 𝔭 h𝔭
  obtain ⟨_, h𝔭h, -, -, h𝔭d⟩ := (hS 𝔭).mp h𝔭
  refine pow_ne_zero _ fun h0 ↦ ?_
  obtain ⟨⟨k₀, hk₀⟩, -⟩ := associated_resForm_prod (d := d) hb h𝔭h h𝔭d.le
  obtain ⟨k₁, hk₁⟩ := exists_charForm_genPiece_ne_zero (d := d) 𝔭
    (elimIdeal_ne_bot_of_totalDegree hb h𝔭h h𝔭d.le)
  exact hk₁ (k₀ ⊔ k₁) le_sup_right
    ((hk₀ (k₀ ⊔ k₁) le_sup_left).eq_zero_iff.mpr h0)

end Stable

end MvPolynomial
