/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ExtensionApproxProd
public import DiophantineApproximation.SubspaceKeyInequality
public import DiophantineApproximation.SubspaceSystem

-- Used only inside proofs.
import DiophantineApproximation.PlacesOver
import DiophantineApproximation.SIntegerExtension

/-!
# From systems to approximation domains

**Milestone Q0.2c** of the `QuantitativeSubspace` roadmap. A solution `x` of a system of Layer 9.1,

```text
|L v i (x)|_v ≤ C v · H(x) ^ (c v i)   at every place v of S∞ ∪ S,   x S-integral,
```

with forms over a Galois extension `E / K`, is a point of an **approximation domain over `E`**
(Layer 4.1) at the level `Q = H(x)`:
- the forms are 6.3's conjugated system `NumberField.conjSystem`;
- the finite places are those of `E` above `S` (`NumberField.systemPlacesOver`);
- the exponents are `NumberField.conjExponent`, which is `c v i / mult v` above an infinite
  place `v` and `e f · c v i` above a prime of `S`;
- the constants are absorbed into the exponents, as `C v ≤ H(x) ^ (γ v)`.

The weight of the domain is `[E : K]` times the weight of the system
(`NumberField.approxWeight_conjExponent`), and so is the weight of the absolute values of the
exponents (`NumberField.approxAbsWeight_conjExponent`), which is what Layer 5.6's chain length
and ratio are computed from.

This replaces Layers 5.1 and 6.2 on the quantitative path. Layer 5.1 normalized a point of the
product inequality by an `S`-unit and enlarged `S` to a set `S′` with no bound on its size; a
point of a system is already `S`-integral, and measured against the affine height it needs no
normalization. Nothing here uses Northcott.

## Main definitions

* `NumberField.systemPlacesOver`: the finite places of `E` above the primes of `S`.
* `NumberField.conjExponent`: the exponents of the domain over `E`.

## Main results

* `NumberField.mem_approxDomain_conjSystem`: a point meeting the system's bounds with exponents
  `e` lies in the domain over `E` with exponents `conjExponent S e`.
* `NumberField.mem_approxDomain_conjSystem_of_mem_systemSet`: **the bridge**, for the solutions of
  a system, with the constants absorbed.
* `NumberField.approxWeight_conjExponent` and `NumberField.approxAbsWeight_conjExponent`: the two
  weights over `E` are `[E : K]` times those of the system;
  `NumberField.approxWeight_conjExponent_add` with the constants absorbed.
* `NumberField.linearIndependent_conjSystem_infinitePlace` and
  `NumberField.linearIndependent_conjSystem_systemPlacesOver`: the forms over `E` are independent
  at every place the domain reads.
* `NumberField.systemSet_compRingHom`: a system over an intermediate field `F` is the same system
  over `E`, so the Galois closure costs nothing.

## Implementation notes

⚠ **The exponents are a function of the absolute value, defined by cases, as `conjSystem` is.**
An approximation domain over `E` reads its exponents at `V.1` for places `V` of `E`, so
`conjExponent` chooses, for an absolute value of `E`, a place of `K` below it, and the evaluation
lemmas prove that the choice is the one wanted: two places of `K` below one place of `E` agree.
At an infinite place that is `AbsoluteValue.LiesOver.under_eq`; at a finite place it is that a
prime of `𝓞 E` contracts to one prime of `𝓞 K`.

⚠ **The two normalizations of the local factors cost one exponent each.** A system measures an
infinite place `v` by `|·|_v ^ mult v` and a finite one by `|·|_v`; an approximation domain over
`E` measures an infinite place `V` by `|·|_V`, which equals `|·|_v` on the conjugated forms at a
point of `Kⁱ`, and a finite place by `|·|_V = |·|_v ^ (e f)`. So the exponent is divided by
`mult v` at an infinite place and multiplied by `e f` at a finite one, and the weights come out as
`∑_{V | v} mult V = [E : K] mult v` and `∑_{V | v} e f = [E : K]`.

⚠ **The constants go into the exponents, not into the level.** A domain has no constants. With
`C v ≤ H(x) ^ (γ v)` the bound `C v H(x) ^ (c v i)` becomes `H(x) ^ (c v i + γ v)`, which raises the
weight by `#ι ∑ γ v`; the caller picks `γ` small against the weight of the system, and the
height above which `C v ≤ H(x) ^ (γ v)` holds is explicit in `C v`.

## References

J.-H. Evertse, *On the Quantitative Subspace Theorem*, Zap. Nauchn. Sem. POMI **377** (2010),
217–240 (arXiv:1008.2268), §2. E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*,
Cambridge University Press (2006), Remark 7.2.3.

This is milestone Q0.2c of the `QuantitativeSubspace` roadmap.
-/

@[expose] public section

open Finset Module NumberField IsDedekindDomain Height

namespace NumberField

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
variable {ι : Type*} [Fintype ι]

/-! ### The places and the exponents over `E` -/

variable (E) in
open scoped Classical in
/-- **The finite places of `E` above the primes of `S`.** -/
noncomputable def systemPlacesOver (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finset (FinitePlace E) :=
  S.attach.biUnion fun p ↦ FinitePlace.placesOverFinset E (FinitePlace.mk p.1)

open scoped Classical in
/-- **The exponents of the domain over `E`**: at an infinite place above `v`, the exponent of the
system at `v` divided by `mult v`; at a finite place above a prime `p` of `S`, the exponent at `p`
times the local degree; `0` elsewhere. -/
noncomputable def conjExponent (S : Finset (HeightOneSpectrum (𝓞 K)))
    (e : InfinitePlace K ⊕ S → ι → ℝ) (U : AbsoluteValue E ℝ) : ι → ℝ :=
  if h : ∃ p : InfinitePlace K × InfinitePlace E, p.2.1 = U ∧ p.2.LiesOver p.1 then
    fun i ↦ e (.inl h.choose.1) i / h.choose.1.mult
  else if h' : ∃ p : S × FinitePlace E, p.2.1 = U ∧ p.2.LiesOver (FinitePlace.mk p.1.1) then
    fun i ↦ (h'.choose.2.localDegree K : ℝ) * e (.inr h'.choose.1) i
  else 0

omit [NumberField K] [NumberField E] in
/-- Every infinite place of `E` lies over its restriction to `K`. -/
theorem InfinitePlace.liesOver_comap (V : InfinitePlace E) :
    V.LiesOver (V.comap (algebraMap K E)) :=
  ⟨AbsoluteValue.ext fun _ ↦ rfl⟩

omit [Fintype ι] in
/-- **The exponent at an infinite place above `v`.** -/
theorem conjExponent_inf (S : Finset (HeightOneSpectrum (𝓞 K)))
    (e : InfinitePlace K ⊕ S → ι → ℝ) {v : InfinitePlace K} {V : InfinitePlace E}
    (hV : V.LiesOver v) : conjExponent S e V.1 = fun i ↦ e (.inl v) i / v.mult := by
  classical
  have hex : ∃ p : InfinitePlace K × InfinitePlace E, p.2.1 = V.1 ∧ p.2.LiesOver p.1 :=
    ⟨(v, V), rfl, hV⟩
  rw [conjExponent, dite_eq_left hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  have hveq : hex.choose.1 = v := by
    refine Subtype.ext ?_
    have e1 : hex.choose.2.1.under K = hex.choose.1.1 := AbsoluteValue.LiesOver.under_eq _ _
    have e2 : V.1.under K = v.1 := AbsoluteValue.LiesOver.under_eq _ _
    rw [← e1, ← e2, h1]
  rw [hveq]

/-- A finite place of `E` lies over at most one prime of `𝓞 K`. -/
theorem eq_of_liesOver_mk {V V' : FinitePlace E} {p q : HeightOneSpectrum (𝓞 K)}
    (hp : V.LiesOver (FinitePlace.mk p)) (hq : V'.LiesOver (FinitePlace.mk q)) (hVV : V = V') :
    p = q := by
  subst hVV
  have h1 : (FinitePlace.mk p).maximalIdeal.asIdeal = V.maximalIdeal.asIdeal.under (𝓞 K) := hp.over
  have h2 : (FinitePlace.mk q).maximalIdeal.asIdeal = V.maximalIdeal.asIdeal.under (𝓞 K) := hq.over
  rw [FinitePlace.maximalIdeal_mk] at h1 h2
  exact HeightOneSpectrum.asIdeal_injective (h1.trans h2.symm)

open scoped Classical in
/-- Membership in the places above `S`. -/
theorem mem_systemPlacesOver {S : Finset (HeightOneSpectrum (𝓞 K))} {V : FinitePlace E} :
    V ∈ systemPlacesOver E S ↔ ∃ p ∈ S, V.LiesOver (FinitePlace.mk p) := by
  unfold systemPlacesOver
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨p, hp⟩, -, hV⟩
    exact ⟨p, hp, FinitePlace.mem_placesOverFinset.mp hV⟩
  · rintro ⟨p, hp, hV⟩
    exact ⟨⟨p, hp⟩, Finset.mem_attach _ _, FinitePlace.mem_placesOverFinset.mpr hV⟩

omit [Fintype ι] in
/-- **The exponent at a finite place above a prime `p` of `S`.** -/
theorem conjExponent_fin (S : Finset (HeightOneSpectrum (𝓞 K)))
    (e : InfinitePlace K ⊕ S → ι → ℝ) {p : HeightOneSpectrum (𝓞 K)} (hp : p ∈ S)
    {V : FinitePlace E} (hV : V.LiesOver (FinitePlace.mk p)) :
    conjExponent S e V.1 = fun i ↦ (V.localDegree K : ℝ) * e (.inr ⟨p, hp⟩) i := by
  classical
  have hninf : ¬ ∃ q : InfinitePlace K × InfinitePlace E, q.2.1 = V.1 ∧ q.2.LiesOver q.1 :=
    fun ⟨q, hq, _⟩ ↦ InfinitePlace.val_ne_finitePlace_val q.2 V hq
  have hex : ∃ q : S × FinitePlace E, q.2.1 = V.1 ∧ q.2.LiesOver (FinitePlace.mk q.1.1) :=
    ⟨(⟨p, hp⟩, V), rfl, hV⟩
  rw [conjExponent, dite_eq_right hninf, dite_eq_left hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  have hVeq : hex.choose.2 = V := Subtype.ext h1
  have hpeq : hex.choose.1 = ⟨p, hp⟩ := Subtype.ext (eq_of_liesOver_mk h2 hV hVeq)
  rw [hVeq, hpeq]

omit [Fintype ι] in
/-- The absolute values of the exponents over `E` are the exponents of the absolute values. -/
theorem abs_conjExponent (S : Finset (HeightOneSpectrum (𝓞 K)))
    (e : InfinitePlace K ⊕ S → ι → ℝ) (U : AbsoluteValue E ℝ) (i : ι) :
    |conjExponent S e U i| = conjExponent S (fun p i ↦ |e p i|) U i := by
  classical
  unfold conjExponent
  split_ifs
  · rw [abs_div, Nat.abs_cast]
  · rw [abs_mul, Nat.abs_cast]
  · simp

/-! ### The bridge -/

/-- `a ^ m ≤ Q ^ t` gives `a ≤ Q ^ (t / m)`. -/
private theorem le_rpow_div_of_pow_le {a Q t : ℝ} {m : ℕ} (ha : 0 ≤ a) (hQ : 0 ≤ Q) (hm : 0 < m)
    (h : a ^ m ≤ Q ^ t) : a ≤ Q ^ (t / m) := by
  have h1 := Real.rpow_le_rpow (pow_nonneg ha m) h (inv_nonneg.mpr (Nat.cast_nonneg m))
  rwa [Real.pow_rpow_inv_natCast ha hm.ne', ← Real.rpow_mul hQ, ← div_eq_mul_inv] at h1

/-- `a ≤ Q ^ t` gives `a ^ m ≤ Q ^ (m t)`. -/
private theorem pow_le_rpow_mul_of_le {a Q t : ℝ} (m : ℕ) (ha : 0 ≤ a) (hQ : 0 ≤ Q)
    (h : a ≤ Q ^ t) : a ^ m ≤ Q ^ ((m : ℝ) * t) := by
  rw [mul_comm, Real.rpow_mul hQ, Real.rpow_natCast]
  exact pow_le_pow_left₀ ha h m

open scoped Classical in
/-- **A point meeting the bounds of a system lies in the domain over `E`.** If `x` is
`S`-integral and every local value of the system at `x` is at most `Q ^ (e p i)`, then `x`, read in
`Eⁱ`, lies in the approximation domain over `E` at level `Q` with the conjugated forms, the places
above `S` and the exponents `conjExponent S e`. -/
theorem mem_approxDomain_conjSystem [IsGalois K E] {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w' : AbsoluteValue K ℝ → AbsoluteValue E ℝ}
    (hwI : ∀ v : InfinitePlace K, (w' v.1).LiesOver v.1)
    (hwF : ∀ p ∈ S, (w' (FinitePlace.mk p).1).LiesOver (FinitePlace.mk p).1)
    (L : AbsoluteValue K ℝ → ι → Dual E (ι → E)) {e : InfinitePlace K ⊕ S → ι → ℝ} {Q : ℝ}
    (hQ : 0 ≤ Q) {x : ι → K}
    (hxint : ∀ j, x j ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K)
    (hx : ∀ p i, systemValue S w' L p i x ≤ Q ^ e p i) :
    (fun j ↦ algebraMap K E (x j)) ∈ approxDomain (systemPlacesOver E S)
      (conjSystem univ (S.image FinitePlace.mk) w' L) (conjExponent S e) Q := by
  have hwI' : ∀ v ∈ (univ : Finset (InfinitePlace K)), (w' v.1).LiesOver v.1 :=
    fun v _ ↦ hwI v
  have hwF' : ∀ v ∈ S.image FinitePlace.mk, (w' v.1).LiesOver v.1 := fun v hv ↦ by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    exact hwF p hp
  refine ⟨fun V i ↦ ?_, fun V hV i ↦ ?_, fun V hV j ↦ ?_⟩
  · -- an infinite place
    have hVv := InfinitePlace.liesOver_comap (K := K) V
    rw [conjSystem_apply_inf hwI' (mem_univ _) hVv i x, conjExponent_inf S e hVv]
    exact le_rpow_div_of_pow_le (apply_nonneg _ _) hQ (V.comap (algebraMap K E)).mult_pos
      (hx (.inl _) i)
  · -- a finite place above `S`
    obtain ⟨p, hp, hVp⟩ := mem_systemPlacesOver.mp hV
    rw [conjSystem_apply_fin hwF' (Finset.mem_image_of_mem _ hp) hVp i x,
      conjExponent_fin S e hp hVp]
    have h1 := hx (.inr ⟨p, hp⟩) i
    simp only [systemValue, systemAbs, systemPlace, systemMult, pow_one] at h1
    exact pow_le_rpow_mul_of_le _ (apply_nonneg _ _) hQ h1
  · -- integrality at the other finite places
    set P := V.maximalIdeal with hPdef
    have hVP : V = FinitePlace.mk P := V.mk_maximalIdeal.symm
    obtain ⟨n, -, hn⟩ := exists_mk_algebraMap_eq_pow (K := K) P
    have hq : P.under (𝓞 K) ∉ S := by
      intro hq
      refine hV (mem_systemPlacesOver.mpr ⟨_, hq, ?_⟩)
      change V.maximalIdeal.asIdeal.LiesOver (FinitePlace.mk (P.under (𝓞 K))).maximalIdeal.asIdeal
      rw [FinitePlace.maximalIdeal_mk]
      exact ⟨rfl⟩
    rw [hVP, hn]
    exact pow_le_one₀ (apply_nonneg _ _)
      ((Set.mem_integer_iff_finitePlace _ _).mp (hxint j) _ hq)

open scoped Classical in
/-- **From a system to an approximation domain over `E`** (Q0.2c). A solution `x` of the system
`|L p i (x)|_p ≤ C p · H(x) ^ (c p i)`, where `H` is the affine height, whose constants satisfy
`C p ≤ H(x) ^ (γ p)`, lies — read in `Eⁱ` — in the approximation domain over `E` at level `H(x)`
with the conjugated forms, the places above `S` and the exponents `conjExponent S (c + γ)`. -/
theorem mem_approxDomain_conjSystem_of_mem_systemSet [IsGalois K E]
    {S : Finset (HeightOneSpectrum (𝓞 K))} {w' : AbsoluteValue K ℝ → AbsoluteValue E ℝ}
    (hwI : ∀ v : InfinitePlace K, (w' v.1).LiesOver v.1)
    (hwF : ∀ p ∈ S, (w' (FinitePlace.mk p).1).LiesOver (FinitePlace.mk p).1)
    (L : AbsoluteValue K ℝ → ι → Dual E (ι → E)) {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {x : ι → K} (hx : x ∈ systemSet S w' L C c)
    {γ : InfinitePlace K ⊕ S → ℝ} (hC : ∀ p, C p ≤ mulHeightAff x ^ γ p) :
    (fun j ↦ algebraMap K E (x j)) ∈ approxDomain (systemPlacesOver E S)
      (conjSystem univ (S.image FinitePlace.mk) w' L)
      (conjExponent S fun p i ↦ c p i + γ p) (mulHeightAff x) := by
  have hH : 0 < mulHeightAff x := mulHeightAff_pos x
  refine mem_approxDomain_conjSystem hwI hwF L hH.le hx.1 fun p i ↦ ?_
  rw [Real.rpow_add hH, mul_comm]
  exact (hx.2 p i).trans (mul_le_mul_of_nonneg_right (hC p) (Real.rpow_nonneg hH.le _))

/-! ### The weights over `E` -/

/-- The infinite places of `E` are the union of the places above those of `K`. -/
private theorem univ_eq_biUnion_placesOverFinset_inf [DecidableEq (InfinitePlace E)] :
    (univ : Finset (InfinitePlace E))
      = (univ : Finset (InfinitePlace K)).biUnion (InfinitePlace.placesOverFinset E) := by
  ext V
  simp only [mem_univ, mem_biUnion, true_and, true_iff, InfinitePlace.mem_placesOverFinset]
  exact ⟨_, InfinitePlace.liesOver_comap V⟩

/-- The places above distinct primes of `S` are distinct. -/
private theorem pairwiseDisjoint_placesOverFinset_mk (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (S.attach : Set S).PairwiseDisjoint
      fun p ↦ FinitePlace.placesOverFinset E (FinitePlace.mk p.1) := by
  intro p _ q _ hne
  simp only [Function.onFun, Finset.disjoint_left]
  intro V hVp hVq
  rw [FinitePlace.mem_placesOverFinset] at hVp hVq
  exact hne (Subtype.ext (eq_of_liesOver_mk hVp hVq rfl))

/-- **The weight of the domain over `E` is `[E : K]` times the weight of the system.** -/
theorem approxWeight_conjExponent (S : Finset (HeightOneSpectrum (𝓞 K)))
    (e : InfinitePlace K ⊕ S → ι → ℝ) :
    approxWeight (systemPlacesOver E S) (conjExponent S e) = finrank K E * systemWeight e := by
  classical
  have hinf : ∑ V : InfinitePlace E, (V.mult : ℝ) * ∑ i, conjExponent S e V.1 i
      = finrank K E * ∑ v : InfinitePlace K, ∑ i, e (.inl v) i := by
    rw [univ_eq_biUnion_placesOverFinset_inf (K := K),
      Finset.sum_biUnion (pairwiseDisjoint_placesOverFinset_inf univ), Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    have hterm : ∀ V ∈ InfinitePlace.placesOverFinset E v,
        (V.mult : ℝ) * ∑ i, conjExponent S e V.1 i
          = (V.mult : ℝ) * ((∑ i, e (.inl v) i) / v.mult) := fun V hV ↦ by
      rw [conjExponent_inf S e (InfinitePlace.mem_placesOverFinset.mp hV), Finset.sum_div]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    have hsum : ∑ V ∈ InfinitePlace.placesOverFinset E v, (V.mult : ℝ)
        = v.mult * finrank K E := by
      exact_mod_cast InfinitePlace.sum_mult v
    have hv : (v.mult : ℝ) ≠ 0 := by exact_mod_cast v.mult_pos.ne'
    rw [hsum]
    field_simp
  have hfin : ∑ V ∈ systemPlacesOver E S, ∑ i, conjExponent S e V.1 i
      = finrank K E * ∑ p : S, ∑ i, e (.inr p) i := by
    unfold systemPlacesOver
    rw [Finset.sum_biUnion (pairwiseDisjoint_placesOverFinset_mk S),
      Finset.mul_sum, ← Finset.univ_eq_attach]
    refine Finset.sum_congr rfl fun ⟨p, hp⟩ _ ↦ ?_
    have hterm : ∀ V ∈ FinitePlace.placesOverFinset E (FinitePlace.mk p),
        ∑ i, conjExponent S e V.1 i = (V.localDegree K : ℝ) * ∑ i, e (.inr ⟨p, hp⟩) i :=
      fun V hV ↦ by
        rw [conjExponent_fin S e hp (FinitePlace.mem_placesOverFinset.mp hV), Finset.mul_sum]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    have hsum : ∑ V ∈ FinitePlace.placesOverFinset E (FinitePlace.mk p), (V.localDegree K : ℝ)
        = finrank K E := by
      exact_mod_cast FinitePlace.sum_localDegree (FinitePlace.mk p)
    rw [hsum]
  rw [approxWeight, hinf, hfin, systemWeight, Fintype.sum_sum_type, mul_add]

/-- **The weight after absorbing the constants**: raising every exponent at `p` by `γ p` raises
the weight over `E` by `[E : K] #ι ∑ γ p`. -/
theorem approxWeight_conjExponent_add (S : Finset (HeightOneSpectrum (𝓞 K)))
    (c : InfinitePlace K ⊕ S → ι → ℝ) (γ : InfinitePlace K ⊕ S → ℝ) :
    approxWeight (systemPlacesOver E S) (conjExponent S fun p i ↦ c p i + γ p)
      = finrank K E * (systemWeight c + Fintype.card ι * ∑ p, γ p) := by
  rw [approxWeight_conjExponent, systemWeight, systemWeight]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.mul_sum]

/-- **The weight of the absolute values of the exponents over `E`** is `[E : K]` times
`∑ |c p i|`, the quantity Layer 5.6's chain length and ratio are computed from. -/
theorem approxAbsWeight_conjExponent (S : Finset (HeightOneSpectrum (𝓞 K)))
    (e : InfinitePlace K ⊕ S → ι → ℝ) :
    approxAbsWeight (systemPlacesOver E S) (conjExponent S e)
      = finrank K E * ∑ p, ∑ i, |e p i| := by
  have h := approxWeight_conjExponent (E := E) S fun p i ↦ |e p i|
  rw [approxWeight, systemWeight] at h
  rw [approxAbsWeight, ← h]
  simp only [abs_conjExponent]

/-! ### Independence over `E` -/

open scoped Classical in
/-- The conjugated forms are independent at every infinite place of `E`. -/
theorem linearIndependent_conjSystem_infinitePlace [IsGalois K E]
    {S : Finset (HeightOneSpectrum (𝓞 K))} {w' : AbsoluteValue K ℝ → AbsoluteValue E ℝ}
    (hwI : ∀ v : InfinitePlace K, (w' v.1).LiesOver v.1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)}
    (hLI : ∀ v : InfinitePlace K, LinearIndependent E (L v.1)) (V : InfinitePlace E) :
    LinearIndependent E (conjSystem univ (S.image FinitePlace.mk) w' L V.1) :=
  linearIndependent_conjSystem_inf (fun v _ ↦ hwI v) (fun v _ ↦ hLI v) (mem_univ _)
    (InfinitePlace.liesOver_comap (K := K) V)

open scoped Classical in
/-- The conjugated forms are independent at every finite place of `E` above `S`. -/
theorem linearIndependent_conjSystem_systemPlacesOver [IsGalois K E]
    {S : Finset (HeightOneSpectrum (𝓞 K))} {w' : AbsoluteValue K ℝ → AbsoluteValue E ℝ}
    (hwF : ∀ p ∈ S, (w' (FinitePlace.mk p).1).LiesOver (FinitePlace.mk p).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)}
    (hLF : ∀ p ∈ S, LinearIndependent E (L (FinitePlace.mk p).1))
    {V : FinitePlace E} (hV : V ∈ systemPlacesOver E S) :
    LinearIndependent E (conjSystem univ (S.image FinitePlace.mk) w' L V.1) := by
  obtain ⟨p, hp, hVp⟩ := mem_systemPlacesOver.mp hV
  refine linearIndependent_conjSystem_fin (fun v hv ↦ ?_) (fun v hv ↦ ?_)
    (Finset.mem_image_of_mem _ hp) hVp
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    exact hwF q hq
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    exact hLF q hq

/-! ### From an intermediate field to `E` -/

omit [NumberField E] in
open scoped Classical in
/-- **A system over an intermediate field `F` is the same system over `E`**: base-changing the
forms to `E` and extending each absolute value leaves every local value, and so the solution set,
unchanged. -/
theorem systemSet_compRingHom {F : Type*} [Field F] [Algebra K F] [Algebra F E]
    [IsScalarTower K F E] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (w' : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hw : ∀ p z, w' (systemPlace S p) (algebraMap F E z) = w (systemPlace S p) z)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) (C : InfinitePlace K ⊕ S → ℝ)
    (c : InfinitePlace K ⊕ S → ι → ℝ) :
    systemSet S w' (fun u i ↦ (L u i).compRingHom (algebraMap F E)) C c = systemSet S w L C c := by
  have hval : ∀ p i (x : ι → K), systemValue S w' (fun u i ↦ (L u i).compRingHom
      (algebraMap F E)) p i x = systemValue S w L p i x := by
    intro p i x
    have hcomp : (fun j ↦ algebraMap K E (x j))
        = fun j ↦ algebraMap F E (algebraMap K F (x j)) := by
      funext j
      rw [IsScalarTower.algebraMap_apply K F E]
    simp only [systemValue, systemAbs]
    rw [hcomp, Module.Dual.compRingHom_comp, hw]
  ext x
  simp only [systemSet, Set.mem_ofPred_eq, hval]

end NumberField
