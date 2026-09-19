/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Pseudo-bases of finitely generated modules over a Dedekind domain

A finitely generated `A`-submodule `M` of `Kⁱ`, with `A` a Dedekind domain and `K` its field of
fractions, is a direct sum of fractional ideals:

```text
M  =  𝔞₁ y₁ ⊕ ⋯ ⊕ 𝔞_k y_k,
```

with `y₁, …, y_k` independent over `K` and `𝔞₁, …, 𝔞_k` nonzero fractional ideals. This is the
existence half of the Steinitz classification of finitely generated torsion-free modules over a
Dedekind domain, in the form a lattice computation needs: not an abstract isomorphism, but a
decomposition realized inside `Kⁱ`, so that the `y i` can be taken inside `M` and the Plücker
coordinates of the family are the ones the height of the span is computed from.

## Main results

* `Submodule.exists_pseudoBasis`: the decomposition, stated as a membership criterion —
  `x ∈ M ↔ ∃ c, (∀ i, c i ∈ 𝔞 i) ∧ x = ∑ i, c i • y i`.
* `Submodule.exists_pseudoBasis_mem`: the same with every `y i` in `M`, which is what makes the
  Plücker coordinates integral when `M ⊆ Aⁱ`.
* `Submodule.exists_smul_mem_of_mem_span`: every element of the `K`-span of `M` has a nonzero
  `A`-multiple in `M`.
* `FractionalIdeal.exists_dual_finset`: a nonzero fractional ideal has a finite dual basis
  `∑ aⱼ bⱼ = 1` with `aⱼ ∈ 𝔞`, `bⱼ ∈ 𝔞⁻¹`.

## Implementation notes

⚠ **No projectivity is invoked, and no splitting lemma.** The induction peels off one rank at a
time with a `K`-linear functional `f` that is nonzero on `M`; the image `f(M)` is a nonzero
fractional ideal `𝔞`, and a dual basis `∑ aⱼbⱼ = 1` for `𝔞` produces the splitting vector
`y := ∑ⱼ bⱼ • mⱼ` explicitly, where `f mⱼ = aⱼ` and `mⱼ ∈ M`. That `y` satisfies `f y = 1` and
`𝔞 • y ⊆ M` — the second because `a bⱼ ∈ 𝔞 𝔞⁻¹ = A` for `a ∈ 𝔞`. Invertibility of a nonzero
fractional ideal is therefore the only input, and `Module.Projective` never appears.

⚠ **The `y i` can be normalized into `M`.** Scaling `y i` by a nonzero `a ∈ 𝔞 i` and `𝔞 i` by
`a⁻¹` changes neither the module nor the `K`-span, and puts `y i = a • y i` inside `M`. This is
what makes the Plücker coordinates of the family integral, and hence readable by the finite places.

## References

E. Steinitz, "Rechteckige Systeme und Moduln in algebraischen Zahlkörpern", *Mathematische
Annalen* **71** (1911), 328–354, and **72** (1912), 297–345. See also H. Cohen, *Advanced Topics
in Computational Number Theory*, Springer (2000), §1.2, where the decomposition above is called a
pseudo-basis and is the data an algorithm carries in place of a basis.

This is Layer 4.3 of the `ArithmeticHeights` roadmap, infrastructure for the number-field case:
it replaces the `ℤ`-basis of the rational case, which exists because `ℤ` is principal.
-/

public section

open FractionalIdeal Module
open scoped nonZeroDivisors

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] {ι : Type*}

/-- **A nonzero fractional ideal has a finite dual basis.** -/
theorem FractionalIdeal.exists_dual_finset (I : FractionalIdeal A⁰ K) (hI : I ≠ 0) :
    ∃ (s : Finset K) (a b : K → K), (∀ x ∈ s, a x ∈ I) ∧ (∀ x ∈ s, b x ∈ I⁻¹) ∧
      ∑ x ∈ s, a x * b x = 1 := by
  classical
  have h1 : (1 : K) ∈ (I * I⁻¹ : FractionalIdeal A⁰ K) := by
    rw [mul_inv_cancel₀ hI]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, by simp⟩
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul,
    Submodule.mul_eq_span_mul_set, Submodule.mem_span_set] at h1
  obtain ⟨c, hc, hsum⟩ := h1
  have hmem : ∀ x ∈ c.support, ∃ p q : K, p ∈ I ∧ q ∈ I⁻¹ ∧ p * q = x := by
    intro x hx
    obtain ⟨p, hp, q, hq, hpq⟩ := Set.mem_mul.1 (hc hx)
    exact ⟨p, q, hp, hq, hpq⟩
  choose! p q hp hq hpq using hmem
  refine ⟨c.support, fun x ↦ c x • p x, q, fun x hx ↦ ?_, fun x hx ↦ hq x hx, ?_⟩
  · exact (I : Submodule A K).smul_mem _ (hp x hx)
  · rw [← hsum, Finsupp.sum]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [smul_mul_assoc, hpq x hx]

/-- Splitting off one rank: a `K`-linear functional nonzero on `M` produces a vector `y` with
`f y = 1` and `𝔞 • y ⊆ M`, where `𝔞 = f(M)`. -/
private theorem exists_split (M : Submodule A (ι → K)) (hM : M.FG)
    (f : (ι → K) →ₗ[K] K) (hf : ∃ m ∈ M, f m ≠ 0) :
    ∃ (y : ι → K) (𝔞 : FractionalIdeal A⁰ K), 𝔞 ≠ 0 ∧ f y = 1 ∧
      (∀ c ∈ 𝔞, c • y ∈ M) ∧ (∀ x ∈ M, f x ∈ 𝔞) := by
  classical
  set I₀ : Submodule A K := Submodule.map (f.restrictScalars A) M with hI₀
  have hI₀fg : I₀.FG := hM.map _
  set 𝔞 : FractionalIdeal A⁰ K := ⟨I₀, isFractional_of_fg hI₀fg⟩ with h𝔞
  have hmem𝔞 : ∀ z : K, z ∈ 𝔞 ↔ z ∈ I₀ := fun _ ↦ Iff.rfl
  have h𝔞ne : 𝔞 ≠ 0 := by
    obtain ⟨m, hm, hfm⟩ := hf
    intro h
    apply hfm
    have : f m ∈ 𝔞 := (hmem𝔞 _).2 ⟨m, hm, rfl⟩
    rw [h] at this
    simpa using this
  obtain ⟨s, a, b, ha, hb, hab⟩ := FractionalIdeal.exists_dual_finset 𝔞 h𝔞ne
  have hpre : ∀ x ∈ s, ∃ m ∈ M, f m = a x := fun x hx ↦ ha x hx
  choose! m hmM hfm using hpre
  refine ⟨∑ x ∈ s, b x • m x, 𝔞, h𝔞ne, ?_, ?_, fun x hx ↦ (hmem𝔞 _).2 ⟨x, hx, rfl⟩⟩
  · rw [map_sum]
    simp_rw [map_smul, smul_eq_mul]
    rw [← hab]
    exact Finset.sum_congr rfl fun x hx ↦ by rw [hfm x hx, mul_comm]
  · intro c hc
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun x hx ↦ ?_
    have hone : c * b x ∈ (1 : FractionalIdeal A⁰ K) := by
      rw [← mul_inv_cancel₀ h𝔞ne]
      exact FractionalIdeal.mul_mem_mul hc (hb x hx)
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hone
    rw [smul_smul, ← hr, algebraMap_smul]
    exact Submodule.smul_mem _ _ (hmM x hx)

omit [IsDedekindDomain A] in
/-- **Clearing denominators.** Every element of the `K`-span of `M` has a nonzero `A`-multiple
in `M`. -/
theorem Submodule.exists_smul_mem_of_mem_span (M : Submodule A (ι → K)) {v : ι → K}
    (hv : v ∈ Submodule.span K (M : Set (ι → K))) : ∃ d : A⁰, (d : A) • v ∈ M := by
  classical
  set S : Submodule K (ι → K) :=
    { carrier := {w | ∃ d : A⁰, (d : A) • w ∈ M}
      add_mem' := by
        rintro x y ⟨d, hd⟩ ⟨e, he⟩
        refine ⟨d * e, ?_⟩
        have : ((d * e : A⁰) : A) • (x + y)
            = (e : A) • ((d : A) • x) + (d : A) • ((e : A) • y) := by
          simp [smul_add, smul_smul, mul_comm]
        rw [this]
        exact M.add_mem (M.smul_mem _ hd) (M.smul_mem _ he)
      zero_mem' := ⟨1, by simp⟩
      smul_mem' := by
        rintro c x ⟨d, hd⟩
        obtain ⟨⟨r, q⟩, hrq⟩ := IsLocalization.surj (M := A⁰) (S := K) c
        refine ⟨q * d, ?_⟩
        have hc : c * (algebraMap A K (q : A)) = algebraMap A K r := hrq
        have : ((q * d : A⁰) : A) • (c • x) = r • ((d : A) • x) := by
          funext l
          rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply]
          simp only [Submonoid.coe_mul, smul_eq_mul, Algebra.smul_def, map_mul]
          rw [← hc]; ring
        rw [this]
        exact M.smul_mem _ hd } with hS
  have hMS : (M : Set (ι → K)) ⊆ (S : Set (ι → K)) := fun x hx ↦ ⟨1, by simpa using hx⟩
  exact (Submodule.span_le.2 hMS) hv

/-- **A finitely generated module over a Dedekind domain has a pseudo-basis.** -/
theorem Submodule.exists_pseudoBasis [Finite ι] : ∀ (k : ℕ) (M : Submodule A (ι → K)), M.FG →
    finrank K (Submodule.span K (M : Set (ι → K))) = k →
    ∃ (y : Fin k → (ι → K)) (𝔞 : Fin k → FractionalIdeal A⁰ K),
      LinearIndependent K y ∧ (∀ i, 𝔞 i ≠ 0) ∧
      (∀ x, x ∈ M ↔ ∃ c : Fin k → K, (∀ i, c i ∈ 𝔞 i) ∧ x = ∑ i, c i • y i) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  intro k
  induction k with
  | zero =>
    intro M hM hk
    have hbot : Submodule.span K (M : Set (ι → K)) = ⊥ := Submodule.finrank_eq_zero.1 hk
    refine ⟨fun i ↦ i.elim0, fun i ↦ i.elim0, linearIndependent_empty_type,
      fun i ↦ i.elim0, fun x ↦ ?_⟩
    constructor
    · intro hx
      refine ⟨fun i ↦ i.elim0, fun i ↦ i.elim0, ?_⟩
      have hx' : x ∈ Submodule.span K (M : Set (ι → K)) := Submodule.subset_span hx
      rw [hbot, Submodule.mem_bot] at hx'
      simp [hx']
    · rintro ⟨c, -, rfl⟩
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact M.zero_mem
  | succ k ih =>
    intro M hM hk
    -- a nonzero element of M
    have hne : ∃ m ∈ M, m ≠ 0 := by
      by_contra h
      push Not at h
      have : Submodule.span K (M : Set (ι → K)) = ⊥ := Submodule.span_eq_bot.2 (fun x hx ↦ h x hx)
      rw [this] at hk
      simp at hk
    obtain ⟨m, hmM, hm0⟩ := hne
    obtain ⟨l, hl⟩ : ∃ l, m l ≠ 0 := by
      by_contra h
      push Not at h
      exact hm0 (funext h)
    set f : (ι → K) →ₗ[K] K := LinearMap.proj l with hf
    obtain ⟨y₀, 𝔞₀, h𝔞₀, hfy₀, hsmul, hfM⟩ := exists_split M hM f ⟨m, hmM, hl⟩
    set M' : Submodule A (ι → K) := M ⊓ (LinearMap.ker f).restrictScalars A with hM'
    have hM'le : M' ≤ M := inf_le_left
    have hM'fg : M'.FG := by
      have hN : IsNoetherian A ↥M := isNoetherian_of_fg_of_noetherian M hM
      have h1 : (M'.comap M.subtype).FG := IsNoetherian.noetherian _
      have h2 : M' = Submodule.map M.subtype (M'.comap M.subtype) :=
        (Submodule.map_comap_eq_self (by simpa using hM'le)).symm
      rw [h2]
      exact h1.map _
    have hspanM' : Submodule.span K (M' : Set (ι → K))
        = Submodule.span K (M : Set (ι → K)) ⊓ LinearMap.ker f := by
      refine le_antisymm (Submodule.span_le.2 ?_) ?_
      · rintro x ⟨hxM, hxk⟩
        exact ⟨Submodule.subset_span hxM, hxk⟩
      · rintro v ⟨hv1, hv2⟩
        obtain ⟨d, hd⟩ := M.exists_smul_mem_of_mem_span hv1
        have hdK : (algebraMap A K (d : A)) ≠ 0 :=
          IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
        have hfv : f v = 0 := hv2
        have hdM' : ((d : A) • v) ∈ M' := by
          refine Submodule.mem_inf.2 ⟨hd, ?_⟩
          rw [Submodule.restrictScalars_mem, LinearMap.mem_ker,
            ← algebraMap_smul (R := A) K (d : A) v, map_smul, hfv, smul_zero]
        have hvv : v = (algebraMap A K (d : A))⁻¹ • ((d : A) • v) := by
          rw [← algebraMap_smul (R := A) K (d : A) v, inv_smul_smul₀ hdK]
        rw [hvv]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hdM')
    have hrank' : finrank K (Submodule.span K (M' : Set (ι → K))) = k := by
      set W := Submodule.span K (M : Set (ι → K)) with hW
      set g : W →ₗ[K] K := f.domRestrict W with hg
      have hsurj : LinearMap.range g = ⊤ := by
        refine LinearMap.range_eq_top.2 ?_
        intro z
        refine ⟨(z / f m) • ⟨m, Submodule.subset_span hmM⟩, ?_⟩
        simp only [hg, LinearMap.domRestrict_apply, map_smul]
        have hfm : f m ≠ 0 := hl
        rw [smul_eq_mul, div_mul_cancel₀ _ hfm]
      have h1 := LinearMap.finrank_range_add_finrank_ker g
      rw [hsurj, finrank_top, Module.finrank_self] at h1
      have h2 : finrank K ↥(LinearMap.ker g) = k := by omega
      have hkerg : LinearMap.ker g = Submodule.comap W.subtype (LinearMap.ker f) := rfl
      have h3 : Submodule.map W.subtype (LinearMap.ker g) = W ⊓ LinearMap.ker f := by
        rw [hkerg]; exact Submodule.map_comap_subtype W (LinearMap.ker f)
      have h4 : finrank K ↥(Submodule.map W.subtype (LinearMap.ker g))
          = finrank K ↥(LinearMap.ker g) :=
        (Submodule.equivMapOfInjective W.subtype W.injective_subtype
          (LinearMap.ker g)).finrank_eq.symm
      rw [hspanM', ← h3, h4, h2]
    obtain ⟨y', 𝔞', hli', h𝔞', hchar'⟩ := ih M' hM'fg hrank'
    have hy'ker : ∀ i, f (y' i) = 0 := by
      intro i
      obtain ⟨a, ha, ha0⟩ : ∃ a ∈ 𝔞' i, a ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact h𝔞' i (FractionalIdeal.eq_zero_iff.2 hcon)
      have hmem : a • y' i ∈ M' := by
        refine (hchar' _).2 ⟨Pi.single i a, fun j ↦ ?_, ?_⟩
        · rcases eq_or_ne j i with rfl | hj
          · simpa using ha
          · simp [hj, (𝔞' j).zero_mem]
        · rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hj; simp [hj]
          · simp
      have : f (a • y' i) = 0 := hmem.2
      rw [map_smul, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left ha0
    have hy₀notin : y₀ ∉ Submodule.span K (Set.range y') := by
      intro hcon
      have hle : Submodule.span K (Set.range y') ≤ LinearMap.ker f :=
        Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hy'ker i)
      have : f y₀ = 0 := hle hcon
      rw [hfy₀] at this
      exact one_ne_zero this
    refine ⟨Fin.cons y₀ y', Fin.cons 𝔞₀ 𝔞', linearIndependent_finCons.2 ⟨hli', hy₀notin⟩,
      fun i ↦ Fin.cases h𝔞₀ h𝔞' i, fun x ↦ ?_⟩
    constructor
    · intro hx
      have hc₀ : f x ∈ 𝔞₀ := hfM x hx
      have hrest : x - (f x) • y₀ ∈ M' := by
        refine Submodule.mem_inf.2 ⟨M.sub_mem hx (hsmul _ hc₀), ?_⟩
        rw [Submodule.restrictScalars_mem, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul,
          hfy₀, mul_one, sub_self]
      obtain ⟨c', hc', heq⟩ := (hchar' _).1 hrest
      refine ⟨Fin.cons (f x) c', fun i ↦ Fin.cases hc₀ hc' i, ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← heq]
      abel
    · rintro ⟨c, hc, rfl⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      refine M.add_mem (hsmul _ (by simpa using hc 0)) (hM'le ((hchar' _).2 ⟨fun i ↦ c i.succ,
        fun i ↦ by simpa using hc i.succ, rfl⟩))

omit [IsDedekindDomain A] in
/-- Membership in a fractional ideal scaled by a nonzero element. -/
private theorem mem_spanSingleton_mul' {b : K} (hb : b ≠ 0) (I : FractionalIdeal A⁰ K) (z : K) :
    z ∈ FractionalIdeal.spanSingleton A⁰ b * I ↔ b⁻¹ * z ∈ I := by
  constructor
  · intro h
    have h2 : b⁻¹ * z ∈ FractionalIdeal.spanSingleton A⁰ b⁻¹ *
        (FractionalIdeal.spanSingleton A⁰ b * I) :=
      FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) h
    rwa [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hb,
      FractionalIdeal.spanSingleton_one, one_mul] at h2
  · intro h
    have h2 := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self A⁰ b) h
    rwa [mul_inv_cancel_left₀ hb] at h2

omit [IsDedekindDomain A] [IsFractionRing A K] in
/-- A nonzero fractional ideal has a nonzero element. -/
private theorem exists_ne_zero_mem' {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : ∃ a ∈ I, a ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hI (FractionalIdeal.eq_zero_iff.2 hcon)

/-- **A pseudo-basis with all its vectors inside the module.** -/
theorem Submodule.exists_pseudoBasis_mem [Finite ι] (k : ℕ) (M : Submodule A (ι → K)) (hM : M.FG)
    (hk : finrank K (Submodule.span K (M : Set (ι → K))) = k) :
    ∃ (y : Fin k → (ι → K)) (𝔞 : Fin k → FractionalIdeal A⁰ K),
      LinearIndependent K y ∧ (∀ i, 𝔞 i ≠ 0) ∧ (∀ i, y i ∈ M) ∧
      (∀ x, x ∈ M ↔ ∃ c : Fin k → K, (∀ i, c i ∈ 𝔞 i) ∧ x = ∑ i, c i • y i) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨y, 𝔞, hli, h𝔞, hchar⟩ := Submodule.exists_pseudoBasis k M hM hk
  choose a ha ha0 using fun i ↦ exists_ne_zero_mem' (h𝔞 i)
  have hmem𝔞' : ∀ (i : Fin k) (z : K),
      z ∈ FractionalIdeal.spanSingleton A⁰ (a i)⁻¹ * 𝔞 i ↔ a i * z ∈ 𝔞 i := fun i z ↦ by
    rw [mem_spanSingleton_mul' (inv_ne_zero (ha0 i)), inv_inv]
  refine ⟨fun i ↦ a i • y i, fun i ↦ FractionalIdeal.spanSingleton A⁰ (a i)⁻¹ * 𝔞 i,
    ?_, ?_, ?_, ?_⟩
  · exact hli.units_smul (fun i ↦ Units.mk0 (a i) (ha0 i))
  · intro i
    exact mul_ne_zero
      ((FractionalIdeal.spanSingleton_ne_zero_iff).2 (inv_ne_zero (ha0 i))) (h𝔞 i)
  · intro i
    refine (hchar _).2 ⟨Pi.single i (a i), fun j ↦ ?_, ?_⟩
    · rcases eq_or_ne j i with rfl | hj
      · simpa using ha j
      · simp [hj, (𝔞 j).zero_mem]
    · rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [hj]
      · simp
  · intro x
    rw [hchar x]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun i ↦ (a i)⁻¹ * c i, fun i ↦ ?_, ?_⟩
      · rw [hmem𝔞' i, mul_inv_cancel_left₀ (ha0 i)]
        exact hc i
      · refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [smul_smul]
        congr 1
        rw [mul_comm ((a i)⁻¹) (c i), mul_assoc, inv_mul_cancel₀ (ha0 i), mul_one]
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun i ↦ a i * c i, fun i ↦ (hmem𝔞' i _).1 (hc i), ?_⟩
      exact Finset.sum_congr rfl fun i _ ↦ by simp [smul_smul, mul_comm]

end
