/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.DecomposableForm
public import DiophantineApproximation.RationalPlaces
public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.SplittingField.Construction

-- Used only inside proofs.
import DiophantineApproximation.BinaryForm
import DiophantineApproximation.SIntegerExtension

/-!
# Thue and Thue–Mahler equations over a number field

**Layer 8.4** (Thue 1909; Mahler 1933; Bombieri–Gubler 5.3.1–5.3.2). Let `g ∈ K[X]` have degree
at most `d` and suppose the binary form `G = g.homogenize d` has at least three pairwise
non-proportional linear factors over an algebraically closed field `Ω ⊇ K` — that is, `g` has at
least three distinct roots in `Ω`, the point at infinity counting as one when `deg g < d`, the
hypothesis of Layer 3.6. Then for a finite set `S` of primes of `𝓞 K`:

* `G(x, y) = m`, `m ≠ 0`, has finitely many solutions in `S`-integers;
* the `S`-integral `(x, y)` with `G(x, y)` an `S`-unit are `S`-unit multiples of finitely many of
  them;
* over `ℚ`, `G(x, y) = ± p₁ ^ z₁ ⋯ pₛ ^ zₛ` has finitely many solutions in coprime integers
  `x, y` and exponents `z` (Thue–Mahler).

## Main results

* `NumberField.finite_setOf_eval_homogenize_eq` and
  `NumberField.exists_finite_forall_eval_homogenize_mem_unit`: the first two, over any number
  field.
* `Polynomial.finite_setOf_natAbs_eval_homogenize_eq_prod_pow`: Thue–Mahler over `ℚ`.
* `NumberField.finite_setOf_eval_homogenize_eq_of_splits` and its unit version: the same when `g`
  splits over `K` itself, which is Layer 8.3 for two variables.
* `Module.Dual.isTriangularlyConnected_binary`: **pairwise non-proportional binary forms, at least
  three of them, are triangularly connected** — any two span the dual of `K²`, so a third is a
  combination of them with nonzero coefficients (Cramer's rule).
* `Polynomial.exists_eval_homogenize_eq_mul_prod_binary`: a split binary form is its leading
  coefficient times a product of powers of pairwise non-proportional linear forms, `Y` among them
  when `deg g < d`.

## Implementation notes

Route: pass to the splitting field `L` of `g` and to the primes of `𝓞 L` above `S`
(`DiophantineApproximation/SIntegerExtension.lean`), where `G` is a product of linear forms and
Layer 8.3 applies. Finiteness comes back to `K` along the injection `K² → L²`.

⚠ **The unit version descends without any theory of the extension.** Over `L` every solution is a
unit multiple `u • y` of one of finitely many `y`. Two solutions `z, z₀ ∈ K²` on the same line
`L ⬝ y` differ by a scalar of `L`, which is a ratio of coordinates of `z` and `z₀`, so lies in `K`;
and it is an `L`-unit for the primes above `S`, hence an `S`-unit of `K`
(`NumberField.map_mem_unit_iff`). So one chosen `K`-solution per line suffices — neither the
degree `[L : K]` nor a norm is used, nor the homogeneity of `G`.

⚠ **Coprimality is what makes Thue–Mahler finite**, and it enters only at the end: the solutions
form finitely many classes modulo `S`-units, and a line through the origin carries at most two
coprime integer points, `c` and `-c` — if `(x, y) = t • c` with both coprime, Bézout for `c` makes
`t` an integer and Bézout for `(x, y)` makes it a unit
(`Int.finite_setOf_isCoprime_eq_mul`). The exponents are then bounded by `|G(x, y)|`.

⚠ **Nothing above 8.3 is used**, and nothing above 8.1 through it: no Roth, no Subspace Theorem,
no heights — unlike Layer 3.6, which proves Thue's theorem over `ℤ` by approximation.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§5.3. J.-H. Evertse and K. Győry, *Unit Equations in Diophantine Number Theory*, Cambridge
University Press (2015), Ch. 9.

This is Layer 8.4 of the `DiophantineApproximation` roadmap.
-/

public section

open IsDedekindDomain NumberField Module Finset Polynomial

namespace Module.Dual

variable {F : Type*} [Field F]

/-- The binary linear form `p 0 * X + p 1 * Y`. -/
@[expose] def binary (p : Fin 2 → F) : Dual F (Fin 2 → F) where
  toFun v := p 0 * v 0 + p 1 * v 1
  map_add' v w := by simp only [Pi.add_apply]; ring
  map_smul' c v := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp]
theorem binary_apply (p v : Fin 2 → F) : binary p v = p 0 * v 0 + p 1 * v 1 := rfl

/-- **A third form joins two.** If `p k` is non-proportional to both `p j` and `p j'`, which
are non-proportional to each other, then `binary (p k)` is a combination of the other two with
nonzero coefficients — Cramer's rule. -/
theorem triangleAdj_binary {κ : Type*} {p : κ → Fin 2 → F} {j j' k : κ}
    (hjj' : p j 0 * p j' 1 ≠ p j 1 * p j' 0) (hkj : p k 0 * p j 1 ≠ p k 1 * p j 0)
    (hkj' : p k 0 * p j' 1 ≠ p k 1 * p j' 0) :
    TriangleAdj (fun i ↦ binary (p i)) j j' := by
  have hD : p j 0 * p j' 1 - p j 1 * p j' 0 ≠ 0 := sub_ne_zero.mpr hjj'
  refine ⟨k, (p k 0 * p j' 1 - p k 1 * p j' 0) / (p j 0 * p j' 1 - p j 1 * p j' 0),
    (p j 0 * p k 1 - p j 1 * p k 0) / (p j 0 * p j' 1 - p j 1 * p j' 0),
    div_ne_zero (sub_ne_zero.mpr hkj') hD, div_ne_zero (fun h ↦ hkj ?_) hD,
    LinearMap.ext fun v ↦ ?_⟩
  · linear_combination -h
  · simp only [binary_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD]
    ring

/-- **At least three pairwise non-proportional binary forms are triangularly connected.** -/
theorem isTriangularlyConnected_binary {κ : Type*} [Finite κ] {p : κ → Fin 2 → F}
    (hp : Pairwise fun j j' ↦ p j 0 * p j' 1 ≠ p j 1 * p j' 0) (h3 : 3 ≤ Nat.card κ) :
    IsTriangularlyConnected fun j ↦ binary (p j) := by
  classical
  have := Fintype.ofFinite κ
  intro j j'
  rcases eq_or_ne j j' with rfl | hne
  · exact .refl
  obtain ⟨k, hk⟩ : ∃ k, k ∉ ({j, j'} : Finset κ) := by
    by_contra! h
    have h1 := card_le_card fun k (_ : k ∈ (univ : Finset κ)) ↦ h k
    have h2 := card_insert_le j ({j'} : Finset κ)
    rw [card_univ, ← Nat.card_eq_fintype_card, card_singleton] at *
    omega
  simp only [mem_insert, mem_singleton, not_or] at hk
  exact .single (triangleAdj_binary (hp hne) (hp hk.1) (hp hk.2))

/-- Two non-proportional binary forms have common kernel `0`. -/
theorem iInf_ker_binary_eq_bot {κ : Type*} {p : κ → Fin 2 → F} {j j' : κ}
    (h : p j 0 * p j' 1 ≠ p j 1 * p j' 0) : ⨅ i, LinearMap.ker (binary (p i)) = ⊥ := by
  refine eq_bot_iff.mpr fun v hv ↦ ?_
  have h1 := (Submodule.mem_iInf _).mp hv j
  have h2 := (Submodule.mem_iInf _).mp hv j'
  simp only [LinearMap.mem_ker, binary_apply] at h1 h2
  have hD : p j 0 * p j' 1 - p j 1 * p j' 0 ≠ 0 := sub_ne_zero.mpr h
  have e0 : v 0 = 0 := by
    have : (p j 0 * p j' 1 - p j 1 * p j' 0) * v 0 = 0 := by
      linear_combination p j' 1 * h1 - p j 1 * h2
    exact (mul_eq_zero.mp this).resolve_left hD
  have e1 : v 1 = 0 := by
    have : (p j 0 * p j' 1 - p j 1 * p j' 0) * v 1 = 0 := by
      linear_combination p j 0 * h2 - p j' 0 * h1
    exact (mul_eq_zero.mp this).resolve_left hD
  rw [Submodule.mem_bot]
  ext i
  fin_cases i <;> simp [e0, e1]

end Module.Dual

namespace Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-- **A split binary form**: `G(x, y) = a y ^ (d - n) ∏ (x - r y) ^ μ r` over the distinct roots `r`
of `g`, with `a` the leading coefficient, `n` the degree and `μ` the multiplicities. -/
theorem eval_homogenize_eq_mul_prod {q : F[X]} (hq : q.Splits) {d : ℕ} (hd : q.natDegree ≤ d)
    (z : Fin 2 → F) :
    MvPolynomial.eval z (q.homogenize d) = q.leadingCoeff * z 1 ^ (d - q.natDegree) *
      ∏ r ∈ q.roots.toFinset, (z 0 - r * z 1) ^ q.roots.count r := by
  have hsum : ∑ r ∈ q.roots.toFinset, q.roots.count r = q.natDegree := by
    rw [Multiset.toFinset_sum_count_eq, splits_iff_card_roots.mp hq]
  rcases eq_or_ne (z 1) 0 with h1 | h1
  · have hz : z = ![z 0, 0] := by
      ext i
      fin_cases i <;> simp [h1]
    rw [hz, eval_homogenize_eq_coeff_mul_pow]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, sub_zero,
      prod_pow_eq_pow_sum, hsum]
    rcases hd.lt_or_eq with hlt | heq
    · rw [coeff_eq_zero_of_natDegree_lt hlt, zero_pow (Nat.sub_ne_zero_of_lt hlt)]
      ring
    · subst heq
      rw [Nat.sub_self, pow_zero, coeff_natDegree]
      ring
  · rw [eval_homogenize hd z h1]
    conv_lhs => rw [hq.eq_prod_roots]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, prod_multiset_map_count]
    have hr : ∀ r, z 0 - r * z 1 = (z 0 / z 1 - r) * z 1 := fun r ↦ by field_simp
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C, hr, mul_pow, prod_mul_distrib,
      prod_pow_eq_pow_sum, hsum]
    conv_lhs => rw [← Nat.sub_add_cancel hd, pow_add]
    ring

/-- **A split binary form as a decomposable form**: its leading coefficient times powers of
pairwise non-proportional linear forms — `X - r Y` for the distinct roots `r`, and `Y` when
`deg g < d` — as many as the hypothesis of Thue's theorem counts, every exponent positive. -/
theorem exists_eval_homogenize_eq_mul_prod_binary {q : F[X]} (hq : q.Splits) {d : ℕ}
    (hd : q.natDegree ≤ d) :
    ∃ (s : Finset (Option F)) (p : Option F → Fin 2 → F) (e : Option F → ℕ),
      (∀ j ∈ s, e j ≠ 0) ∧ Pairwise (fun j j' ↦ p j 0 * p j' 1 ≠ p j 1 * p j' 0) ∧
      s.card = q.roots.toFinset.card + (if q.natDegree = d then 0 else 1) ∧
      ∀ z, MvPolynomial.eval z (q.homogenize d) =
        q.leadingCoeff * ∏ j ∈ s, Dual.binary (p j) z ^ e j := by
  classical
  set R := q.roots.toFinset
  let p : Option F → Fin 2 → F := fun | none => ![0, 1] | some r => ![1, -r]
  let e : Option F → ℕ := fun | none => d - q.natDegree | some r => q.roots.count r
  set s₀ := R.map ⟨some, Option.some_injective F⟩
  have hs₀ : ∀ z, ∏ j ∈ s₀, Dual.binary (p j) z ^ e j =
      ∏ r ∈ R, (z 0 - r * z 1) ^ q.roots.count r := fun z ↦ by
    rw [prod_map]
    refine prod_congr rfl fun r _ ↦ ?_
    simp [p, e]
    ring
  have hnone : none ∉ s₀ := by simp [s₀]
  refine ⟨if q.natDegree = d then s₀ else insert none s₀, p, e, ?_, ?_, ?_, fun z ↦ ?_⟩
  · have h1 : ∀ j ∈ s₀, e j ≠ 0 := by
      intro j hj
      obtain ⟨r, hr, rfl⟩ := mem_map.mp hj
      exact Multiset.count_ne_zero.mpr (Multiset.mem_toFinset.mp hr)
    split_ifs with h
    · exact h1
    · intro j hj
      rcases mem_insert.mp hj with rfl | hj
      · exact Nat.sub_ne_zero_of_lt (lt_of_le_of_ne hd h)
      · exact h1 j hj
  · rintro (_ | r) (_ | r') h
    · exact absurd rfl h
    · simp [p]
    · simp [p]
    · have : r ≠ r' := fun h' ↦ h (by rw [h'])
      simp only [p, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, mul_one, ne_eq,
        neg_inj]
      exact this.symm
  · split_ifs with h
    · simp [s₀, R]
    · rw [card_insert_of_notMem hnone, card_map]
  · rw [eval_homogenize_eq_mul_prod hq hd]
    split_ifs with h
    · rw [hs₀, h, Nat.sub_self, pow_zero, mul_one]
    · rw [prod_insert hnone, hs₀]
      simp [p, e]
      ring

end Polynomial

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Thue's theorem over `S`-integers, split case.** If `q` splits over `K` and
`G = q.homogenize d` has at least three pairwise non-proportional linear factors, then
`G(x, y) = m` with `m ≠ 0` has finitely many `S`-integral solutions. This is Layer 8.3 for two
variables. -/
theorem finite_setOf_eval_homogenize_eq_of_splits [DecidableEq K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {q : K[X]} (hq : q.Splits) {d : ℕ}
    (hd : q.natDegree ≤ d) (h3 : 3 ≤ q.roots.toFinset.card + if q.natDegree = d then 0 else 1)
    {m : K} (hm : m ≠ 0) :
    {z : Fin 2 → K | (∀ i, z i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
      MvPolynomial.eval z (q.homogenize d) = m}.Finite := by
  obtain ⟨s, p, e, he, hp, hcard, heval⟩ := exists_eval_homogenize_eq_mul_prod_binary hq hd
  rw [← hcard] at h3
  have hps : Pairwise fun j j' : s ↦ p j 0 * p j' 1 ≠ p j 1 * p j' 0 :=
    fun j j' h ↦ hp (Subtype.coe_injective.ne h)
  have h3' : 3 ≤ Nat.card s := by rwa [Nat.card_eq_fintype_card, Fintype.card_coe]
  obtain ⟨j, j', hjj'⟩ : ∃ j j' : s, j ≠ j' :=
    Fintype.exists_pair_of_one_lt_card (by rw [← Nat.card_eq_fintype_card]; omega)
  refine (finite_setOf_mul_prod_eq S (l := fun j : s ↦ Dual.binary (p j))
    (Dual.iInf_ker_binary_eq_bot (hps hjj')) (Dual.isTriangularlyConnected_binary hps h3')
    (e := fun j : s ↦ e j) (fun j ↦ he j j.2) q.leadingCoeff hm).subset ?_
  rintro z ⟨hz, hzm⟩
  refine ⟨hz, ?_⟩
  rw [← hzm, heval, prod_coe_sort s fun j ↦ Dual.binary (p j) z ^ e j]

/-- **Thue–Mahler over `S`-integers, split case**: the `S`-integral points at which `G` is an
`S`-unit are `S`-unit multiples of finitely many of them. -/
theorem exists_finite_forall_eval_homogenize_mem_unit_of_splits [DecidableEq K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {q : K[X]} (hq : q.Splits) {d : ℕ}
    (hd : q.natDegree ≤ d) (h3 : 3 ≤ q.roots.toFinset.card + if q.natDegree = d then 0 else 1) :
    ∃ F : Set (Fin 2 → K), F.Finite ∧
      F ⊆ {z | (∀ i, z i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
        ∃ w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
          (w : K) = MvPolynomial.eval z (q.homogenize d)} ∧
      ∀ z : Fin 2 → K, (∀ i, z i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
        (∃ w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
          (w : K) = MvPolynomial.eval z (q.homogenize d)) →
        ∃ u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, ∃ y ∈ F, z = (u : K) • y := by
  obtain ⟨s, p, e, he, hp, hcard, heval⟩ := exists_eval_homogenize_eq_mul_prod_binary hq hd
  rw [← hcard] at h3
  have hps : Pairwise fun j j' : s ↦ p j 0 * p j' 1 ≠ p j 1 * p j' 0 :=
    fun j j' h ↦ hp (Subtype.coe_injective.ne h)
  have h3' : 3 ≤ Nat.card s := by rwa [Nat.card_eq_fintype_card, Fintype.card_coe]
  obtain ⟨j, j', hjj'⟩ : ∃ j j' : s, j ≠ j' :=
    Fintype.exists_pair_of_one_lt_card (by rw [← Nat.card_eq_fintype_card]; omega)
  have hG : ∀ z, q.leadingCoeff * ∏ j : s, Dual.binary (p j) z ^ e j =
      MvPolynomial.eval z (q.homogenize d) := fun z ↦ by
    rw [heval, prod_coe_sort s fun j ↦ Dual.binary (p j) z ^ e j]
  obtain ⟨F, hF, hFsub, hFall⟩ := exists_finite_forall_mul_prod_mem_unit S
    (l := fun j : s ↦ Dual.binary (p j)) (Dual.iInf_ker_binary_eq_bot (hps hjj'))
    (Dual.isTriangularlyConnected_binary hps h3') (e := fun j : s ↦ e j) (fun j ↦ he j j.2)
    q.leadingCoeff
  simp only [hG] at hFsub hFall
  exact ⟨F, hF, hFsub, hFall⟩

/-- Evaluating the image of a binary form at the image of a point. -/
theorem _root_.Polynomial.eval_homogenize_map {R L : Type*} [CommRing R] [CommRing L]
    (f : R →+* L) (g : R[X])
    (d : ℕ) (z : Fin 2 → R) :
    MvPolynomial.eval (fun i ↦ f (z i)) ((g.map f).homogenize d) =
      f (MvPolynomial.eval z (g.homogenize d)) := by
  rw [homogenize_map, MvPolynomial.eval_map]
  simp only [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left,
    RingHom.comp_id]
  rfl

variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [DecidableEq Ω]

omit [NumberField K] in
/-- A polynomial has as many distinct roots in its splitting field as in an algebraically closed
field. -/
theorem card_roots_toFinset_splittingField (g : K[X])
    [DecidableEq g.SplittingField] :
    (g.map (algebraMap K g.SplittingField)).roots.toFinset.card =
      (g.map (algebraMap K Ω)).roots.toFinset.card := by
  let φ : g.SplittingField →ₐ[K] Ω := IsAlgClosed.lift
  have hmap : g.map (algebraMap K Ω) =
      (g.map (algebraMap K g.SplittingField)).map (φ : g.SplittingField →+* Ω) := by
    rw [Polynomial.map_map, φ.comp_algebraMap]
  rw [hmap, (SplittingField.splits g).roots_map, Multiset.toFinset_map,
    card_image_of_injective _ (φ : g.SplittingField →+* Ω).injective]

/-- **Thue's theorem over a number field** (Thue 1909; Siegel). Let `g ∈ K[X]` have degree at most
`d` and at least three distinct roots in an algebraically closed `Ω ⊇ K`, the point at infinity
counting as one when `deg g < d`. Then for `m ≠ 0` the equation `G(x, y) = m`, `G = g.homogenize d`,
has finitely many solutions in `S`-integers. -/
theorem finite_setOf_eval_homogenize_eq (S : Finset (HeightOneSpectrum (𝓞 K))) {g : K[X]}
    {d : ℕ} (hd : g.natDegree ≤ d)
    (hroots : 3 ≤ (g.map (algebraMap K Ω)).roots.toFinset.card +
      if g.natDegree = d then 0 else 1)
    {m : K} (hm : m ≠ 0) :
    {z : Fin 2 → K | (∀ i, z i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
      MvPolynomial.eval z (g.homogenize d) = m}.Finite := by
  classical
  let L := g.SplittingField
  have : NumberField L := NumberField.of_module_finite K L
  have hqd : (g.map (algebraMap K L)).natDegree = g.natDegree := natDegree_map _
  let T := (finite_preimage_under L S.finite_toSet).toFinset
  have hT : (T : Set (HeightOneSpectrum (𝓞 L))) =
      HeightOneSpectrum.under (𝓞 K) ⁻¹' (S : Set (HeightOneSpectrum (𝓞 K))) :=
    Set.Finite.coe_toFinset _
  have hfin := finite_setOf_eval_homogenize_eq_of_splits T (SplittingField.splits g)
    (hqd ▸ hd) (by rw [hqd, card_roots_toFinset_splittingField (Ω := Ω)]; exact hroots)
    ((map_ne_zero (algebraMap K L)).mpr hm)
  refine (hfin.preimage (f := fun (z : Fin 2 → K) i ↦ algebraMap K L (z i))
    fun a _ b _ h ↦ _root_.funext fun i ↦ (algebraMap K L).injective (congrFun h i)).subset ?_
  rintro z ⟨hz, hzm⟩
  refine ⟨fun i ↦ ?_, ?_⟩
  · rw [hT]
    exact algebraMap_mem_integer_iff.mpr (hz i)
  · change MvPolynomial.eval (fun i ↦ algebraMap K L (z i))
      ((g.map (algebraMap K L)).homogenize d) = algebraMap K L m
    rw [eval_homogenize_map, hzm]

/-- **Thue–Mahler over a number field** (Mahler 1933; Bombieri–Gubler, Theorem 5.3.1). Under the
hypotheses of `NumberField.finite_setOf_eval_homogenize_eq`, the `S`-integral points `(x, y)` at
which `G(x, y)` is an `S`-unit are `S`-unit multiples of finitely many of them, which can be taken
among those points. -/
theorem exists_finite_forall_eval_homogenize_mem_unit (S : Finset (HeightOneSpectrum (𝓞 K)))
    {g : K[X]} {d : ℕ} (hd : g.natDegree ≤ d)
    (hroots : 3 ≤ (g.map (algebraMap K Ω)).roots.toFinset.card +
      if g.natDegree = d then 0 else 1) :
    ∃ F : Set (Fin 2 → K), F.Finite ∧
      F ⊆ {z | (∀ i, z i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
        ∃ w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
          (w : K) = MvPolynomial.eval z (g.homogenize d)} ∧
      ∀ z : Fin 2 → K, (∀ i, z i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
        (∃ w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
          (w : K) = MvPolynomial.eval z (g.homogenize d)) →
        ∃ u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, ∃ y ∈ F, z = (u : K) • y := by
  classical
  let L := g.SplittingField
  have : NumberField L := NumberField.of_module_finite K L
  have hqd : (g.map (algebraMap K L)).natDegree = g.natDegree := natDegree_map _
  let T := (finite_preimage_under L S.finite_toSet).toFinset
  have hT : (T : Set (HeightOneSpectrum (𝓞 L))) =
      HeightOneSpectrum.under (𝓞 K) ⁻¹' (S : Set (HeightOneSpectrum (𝓞 K))) :=
    Set.Finite.coe_toFinset _
  obtain ⟨FL, hFL, -, hFLall⟩ := exists_finite_forall_eval_homogenize_mem_unit_of_splits T
    (SplittingField.splits g) (hqd ▸ hd)
    (by rw [hqd, card_roots_toFinset_splittingField (Ω := Ω)]; exact hroots)
  set X := {z : Fin 2 → K | (∀ i, z i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
    ∃ w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
      (w : K) = MvPolynomial.eval z (g.homogenize d)} with hX
  let ι : (Fin 2 → K) → Fin 2 → L := fun z i ↦ algebraMap K L (z i)
  have hι : Function.Injective ι := fun a b h ↦
    _root_.funext fun i ↦ (algebraMap K L).injective (congrFun h i)
  have hcover : ∀ z ∈ X, ∃ u ∈ (T : Set (HeightOneSpectrum (𝓞 L))).unit L, ∃ y ∈ FL,
      ι z = (u : L) • y := by
    rintro z ⟨hz, w, hwS, hw⟩
    refine hFLall (ι z) (fun i ↦ ?_) ⟨Units.map (algebraMap K L : K →* L) w, ?_, ?_⟩
    · rw [hT]
      exact algebraMap_mem_integer_iff.mpr (hz i)
    · rw [hT]
      exact map_mem_unit_iff.mpr hwS
    · rw [Units.coe_map, MonoidHom.coe_ofClass, hw, ← eval_homogenize_map]
  set P : (Fin 2 → L) → Prop := fun y ↦ ∃ z ∈ X, ∃ u ∈ (T : Set (HeightOneSpectrum (𝓞 L))).unit L,
    ι z = (u : L) • y
  let rep : (Fin 2 → L) → Fin 2 → K := fun y ↦ if h : P y then h.choose else 0
  have hrep : ∀ y, P y → rep y ∈ X ∧
      ∃ u ∈ (T : Set (HeightOneSpectrum (𝓞 L))).unit L, ι (rep y) = (u : L) • y := fun y h ↦ by
    simp only [rep, h, ↓reduceDIte]
    exact h.choose_spec
  refine ⟨rep '' {y ∈ FL | P y}, (hFL.subset fun y hy ↦ hy.1).image rep, ?_, fun z hz hzw ↦ ?_⟩
  · rintro _ ⟨y, ⟨-, hy⟩, rfl⟩
    exact (hrep y hy).1
  obtain ⟨u, hu, y, hy, hzy⟩ := hcover z ⟨hz, hzw⟩
  have hPy : P y := ⟨z, ⟨hz, hzw⟩, u, hu, hzy⟩
  obtain ⟨-, u₀, hu₀, hz₀⟩ := hrep y hPy
  set z₀ := rep y
  have hzz₀ : ι z = ((u / u₀ : Lˣ) : L) • ι z₀ := by
    rw [hzy, hz₀, smul_smul, Units.val_div_eq_div_val, div_mul_cancel₀ _ u₀.ne_zero]
  have hmem : z₀ ∈ rep '' {y ∈ FL | P y} := ⟨y, ⟨hy, hPy⟩, rfl⟩
  by_cases h0 : z₀ = 0
  · refine ⟨1, one_mem _, z₀, hmem, ?_⟩
    rw [h0, smul_zero]
    funext i
    apply (algebraMap K L).injective
    have := congrFun hzz₀ i
    simp only [ι, h0, Pi.zero_apply, map_zero] at this
    rw [this, Pi.zero_apply, map_zero, Pi.smul_apply]
    exact smul_zero _
  obtain ⟨i, hi⟩ : ∃ i, z₀ i ≠ 0 := by
    by_contra! h
    exact h0 (funext h)
  have hτ : algebraMap K L (z i / z₀ i) = ((u / u₀ : Lˣ) : L) := by
    have := congrFun hzz₀ i
    simp only [ι, Pi.smul_apply, smul_eq_mul] at this
    rw [map_div₀, this, mul_div_cancel_right₀ _ ((_root_.map_ne_zero _).mpr hi)]
  have hτ0 : z i / z₀ i ≠ 0 := fun h ↦ (u / u₀).ne_zero (by rw [← hτ, h, map_zero])
  refine ⟨Units.mk0 _ hτ0, ?_, z₀, hmem, ?_⟩
  · rw [← map_mem_unit_iff (L := L), ← hT]
    convert div_mem hu hu₀ using 1
    ext
    simp [hτ]
  · funext i'
    apply (algebraMap K L).injective
    have := congrFun hzz₀ i'
    simp only [ι, Pi.smul_apply, smul_eq_mul] at this
    rw [this, Pi.smul_apply, smul_eq_mul, Units.val_mk0, map_mul, hτ]

end NumberField

/-! ### Thue–Mahler over `ℚ` -/

/-- **Coprime integer points on a line through the origin**: at most two, `c` and `-c`. -/
theorem Int.finite_setOf_isCoprime_eq_mul (y₀ : Fin 2 → ℚ) :
    {xy : ℤ × ℤ | IsCoprime xy.1 xy.2 ∧
      ∃ t : ℚ, (xy.1 : ℚ) = t * y₀ 0 ∧ (xy.2 : ℚ) = t * y₀ 1}.Finite := by
  set Y := {xy : ℤ × ℤ | IsCoprime xy.1 xy.2 ∧
    ∃ t : ℚ, (xy.1 : ℚ) = t * y₀ 0 ∧ (xy.2 : ℚ) = t * y₀ 1} with hY
  rcases Y.eq_empty_or_nonempty with h | ⟨c, ⟨α, β, hc⟩, tc, hc0, hc1⟩
  · rw [h]
    exact Set.finite_empty
  refine ((Set.finite_singleton (-c)).insert c).subset ?_
  rintro ⟨x, y⟩ ⟨hxy, t, hx, hy⟩
  have h : x * c.2 = y * c.1 := by
    have : (x : ℚ) * c.2 = y * c.1 := by
      rw [show ((x, y) : ℤ × ℤ).1 = x from rfl] at hx
      rw [show ((x, y) : ℤ × ℤ).2 = y from rfl] at hy
      rw [hx, hy, hc0, hc1]
      ring
    exact_mod_cast this
  have hx' : x = c.1 * (α * x + β * y) := by linear_combination (-x) * hc + β * h
  have hy' : y = c.2 * (α * x + β * y) := by linear_combination (-y) * hc - α * h
  have hu : IsUnit (α * x + β * y) :=
    hxy.isUnit_of_dvd' (Dvd.intro_left _ hx'.symm) (Dvd.intro_left _ hy'.symm)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases Int.isUnit_iff.mp hu with h1 | h1
  · left
    rw [h1, mul_one] at hx' hy'
    exact Prod.ext hx' hy'
  · right
    rw [h1, mul_neg_one] at hx' hy'
    exact Prod.ext hx' hy'

/-- At a finite place of `ℚ` outside `S`, a prime of `S` has absolute value `1`. -/
theorem Rat.mk_natCast_eq_one_of_notMem {S : Set (HeightOneSpectrum (𝓞 ℚ))} (p : Nat.Primes)
    (hp : (Rat.finitePlace p).maximalIdeal ∈ S) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ S) :
    FinitePlace.mk v ((p : ℕ) : ℚ) = 1 := by
  obtain ⟨q, hq, hvq⟩ := Rat.exists_prime_padic_eq (FinitePlace.mk v)
  have hmem : ∀ q' : Nat.Primes, (q' : ℕ) = q → v = (Rat.finitePlace q').maximalIdeal :=
    fun q' hq' ↦ by
      subst hq'
      rw [← FinitePlace.maximalIdeal_mk v]
      congr 1
      exact Subtype.ext (by rw [hvq, Rat.finitePlace_val])
  have hpq : q ≠ p := fun h ↦ hv (by rw [hmem p h.symm]; exact hp)
  have hnorm : padicNorm q ((p : ℕ) : ℚ) = 1 := (padicNorm.nat_eq_one_iff _).mpr fun hpd ↦
    hpq ((Nat.prime_dvd_prime_iff_eq hq.out p.2).mp hpd)
  change (FinitePlace.mk v).1 ((p : ℕ) : ℚ) = 1
  rw [hvq]
  change ((padicNorm q ((p : ℕ) : ℚ) : ℚ) : ℝ) = 1
  exact_mod_cast hnorm

/-- **The Thue–Mahler theorem** (Mahler 1933; Bombieri–Gubler, Theorem 5.3.2). Let `g ∈ ℤ[X]`
have degree at most `d`, and suppose `G = g.homogenize d` has at least three pairwise
non-proportional linear factors over `ℂ`. For primes `p₁, …, pₛ`, finitely many coprime integers
`x, y` and exponents `z₁, …, zₛ` satisfy `G(x, y) = ± p₁ ^ z₁ ⋯ pₛ ^ zₛ`. -/
theorem Polynomial.finite_setOf_natAbs_eval_homogenize_eq_prod_pow {g : ℤ[X]} {d : ℕ}
    (hd : g.natDegree ≤ d)
    (hroots : 3 ≤ (g.map (Int.castRingHom ℂ)).roots.toFinset.card +
      if g.natDegree = d then 0 else 1)
    {s : ℕ} (p : Fin s → Nat.Primes) :
    {t : (ℤ × ℤ) × (Fin s → ℕ) | IsCoprime t.1.1 t.1.2 ∧
      (MvPolynomial.eval ![t.1.1, t.1.2] (g.homogenize d)).natAbs =
        ∏ i, (p i : ℕ) ^ t.2 i}.Finite := by
  classical
  set gQ := g.map (Int.castRingHom ℚ)
  have hgQ : gQ.natDegree = g.natDegree := natDegree_map_eq_of_injective (RingHom.injective_int _) g
  have hmapC : gQ.map (algebraMap ℚ ℂ) = g.map (Int.castRingHom ℂ) := by
    rw [Polynomial.map_map]
    congr 1
  set G : ℤ × ℤ → ℤ := fun xy ↦ MvPolynomial.eval ![xy.1, xy.2] (g.homogenize d)
  have hev : ∀ xy : ℤ × ℤ, MvPolynomial.eval ![(xy.1 : ℚ), (xy.2 : ℚ)] (gQ.homogenize d) =
      (G xy : ℚ) := fun xy ↦ by
    have h := eval_homogenize_map (Int.castRingHom ℚ) g d ![xy.1, xy.2]
    rw [eq_intCast] at h
    convert h using 3
    funext i
    fin_cases i <;> simp
  set S : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
    univ.image fun i ↦ (Rat.finitePlace (p i)).maximalIdeal
  obtain ⟨F, hF, -, hall⟩ := NumberField.exists_finite_forall_eval_homogenize_mem_unit (Ω := ℂ) S
    (hgQ ▸ hd) (by rw [hmapC, hgQ]; exact hroots)
  set Y := {xy : ℤ × ℤ | IsCoprime xy.1 xy.2 ∧
    ∃ z : Fin s → ℕ, (G xy).natAbs = ∏ i, (p i : ℕ) ^ z i}
  have hY : Y.Finite := by
    refine (hF.biUnion fun y₀ _ ↦ Int.finite_setOf_isCoprime_eq_mul y₀).subset ?_
    rintro xy ⟨hcop, z, hz⟩
    have hG0 : (G xy : ℚ) ≠ 0 := by
      have : (G xy).natAbs ≠ 0 := by
        rw [hz]
        exact prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (p i).2.ne_zero
      exact_mod_cast Int.natAbs_ne_zero.mp this
    have hunit : Units.mk0 _ hG0 ∈ (S : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ := by
      refine (Set.mk0_mem_unit_iff_finitePlace _ hG0).mpr fun v hv ↦ ?_
      have habs : FinitePlace.mk v ((G xy).natAbs : ℚ) = FinitePlace.mk v (G xy : ℚ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
        rcases abs_choice (G xy : ℚ) with h | h <;> rw [h]
        rw [map_neg_eq_map]
      rw [← habs, hz]
      push_cast
      rw [map_prod]
      refine prod_eq_one fun i _ ↦ ?_
      rw [map_pow, Rat.mk_natCast_eq_one_of_notMem (p i) (by simp [S]) hv, one_pow]
    obtain ⟨u, -, y₀, hy₀, hxy⟩ := hall ![(xy.1 : ℚ), (xy.2 : ℚ)] (fun i ↦ by
        fin_cases i <;> exact intCast_mem _ _) ⟨_, hunit, (hev xy).symm⟩
    exact Set.mem_biUnion hy₀ ⟨hcop, u, by simpa using congrFun hxy 0,
      by simpa using congrFun hxy 1⟩
  have hZ : ∀ xy : ℤ × ℤ, {z : Fin s → ℕ | (G xy).natAbs = ∏ i, (p i : ℕ) ^ z i}.Finite :=
    fun xy ↦ (Set.Finite.pi (t := fun _ ↦ Set.Iic (G xy).natAbs)
      fun _ ↦ Set.finite_Iic _).subset fun z hz i _ ↦ by
      have h1 : z i < (p i : ℕ) ^ z i := Nat.lt_pow_self (p i).2.one_lt
      have h2 : (p i : ℕ) ^ z i ≤ ∏ j, (p j : ℕ) ^ z j :=
        single_le_prod (fun j _ ↦ Nat.one_le_pow _ _ (p j).2.pos) (mem_univ i)
      have hz' : (G xy).natAbs = ∏ i, (p i : ℕ) ^ z i := hz
      simp only [Set.mem_Iic]
      omega
  refine (hY.biUnion fun xy _ ↦ (Set.finite_singleton xy).prod (hZ xy)).subset ?_
  rintro ⟨xy, z⟩ ⟨hcop, hG⟩
  exact Set.mem_biUnion ⟨hcop, z, hG⟩ ⟨Set.mem_singleton _, hG⟩

/-! ### Acceptance criteria -/

/-- `X ^ 3 - 2` has three distinct roots in an algebraically closed field of characteristic `0`,
because it is separable. -/
private theorem card_roots_X_pow_three_sub_two {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    [DecidableEq Ω] : (X ^ 3 - 2 : Polynomial Ω).roots.toFinset.card = 3 := by
  rw [show (X ^ 3 - 2 : Polynomial Ω) = X ^ 3 - C 2 by rw [C_ofNat],
    Multiset.toFinset_card_of_nodup (nodup_roots (separable_X_pow_sub_C _ (by norm_num)
    (by norm_num))), splits_iff_card_roots.mp (IsAlgClosed.splits _), natDegree_X_pow_sub_C]

/-- The form of the classical example. -/
private theorem eval_homogenize_X_pow_three_sub_two {R : Type*} [CommRing R] (z : Fin 2 → R) :
    MvPolynomial.eval z ((X ^ 3 - C 2 : R[X]).homogenize 3) = z 0 ^ 3 - 2 * z 1 ^ 3 := by
  rw [homogenize_sub, homogenize_C, homogenize_X_pow le_rfl]
  simp

section Field

variable {K : Type*} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))

open scoped Classical in
/-- The hypothesis of Thue's theorem for `X ^ 3 - 2 Y ^ 3` over a number field. -/
private theorem hroots_X_pow_three_sub_two :
    3 ≤ ((X ^ 3 - C 2 : K[X]).map (algebraMap K (AlgebraicClosure K))).roots.toFinset.card +
      if (X ^ 3 - C 2 : K[X]).natDegree = 3 then 0 else 1 := by
  have : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  simp [map_ofNat, card_roots_X_pow_three_sub_two]

/-- **`x ^ 3 - 2 y ^ 3 = 1` has finitely many `S`-integral solutions, in every number field and
for every finite `S`.** -/
example : {z : Fin 2 → K | (∀ i, z i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
    z 0 ^ 3 - 2 * z 1 ^ 3 = 1}.Finite := by
  classical
  convert NumberField.finite_setOf_eval_homogenize_eq (Ω := AlgebraicClosure K) S
    natDegree_X_pow_sub_C.le
    (hroots_X_pow_three_sub_two (K := K)) one_ne_zero using 4 with z
  rw [eval_homogenize_X_pow_three_sub_two]

/-- **Modulo `S`-units, finitely many `S`-integral points make `x ^ 3 - 2 y ^ 3` an `S`-unit**, in
every number field and for every finite `S`. -/
example : ∃ F : Set (Fin 2 → K), F.Finite ∧
    ∀ z : Fin 2 → K, (∀ i, z i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
      (∃ w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, (w : K) = z 0 ^ 3 - 2 * z 1 ^ 3) →
      ∃ u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, ∃ y ∈ F, z = (u : K) • y := by
  classical
  obtain ⟨F, hF, -, hall⟩ := NumberField.exists_finite_forall_eval_homogenize_mem_unit
    (Ω := AlgebraicClosure K) S natDegree_X_pow_sub_C.le (hroots_X_pow_three_sub_two (K := K))
  refine ⟨F, hF, fun z hz hw ↦ hall z hz ?_⟩
  simpa only [eval_homogenize_X_pow_three_sub_two] using hw

end Field

/-- The hypothesis of Thue's theorem for `X ^ 3 - 2 Y ^ 3` over `ℤ`. -/
private theorem hroots_int :
    3 ≤ ((X ^ 3 - C 2 : ℤ[X]).map (Int.castRingHom ℂ)).roots.toFinset.card +
      if (X ^ 3 - C 2 : ℤ[X]).natDegree = 3 then 0 else 1 := by
  classical
  simp [card_roots_X_pow_three_sub_two]

/-- **Thue–Mahler for `x ^ 3 - 2 y ^ 3` and the primes `2, 3`**: finitely many coprime `x, y` and
exponents `a, b` satisfy `x ^ 3 - 2 y ^ 3 = ± 2 ^ a 3 ^ b`. -/
example : {t : (ℤ × ℤ) × (Fin 2 → ℕ) | IsCoprime t.1.1 t.1.2 ∧
    (t.1.1 ^ 3 - 2 * t.1.2 ^ 3).natAbs = 2 ^ t.2 0 * 3 ^ t.2 1}.Finite := by
  convert Polynomial.finite_setOf_natAbs_eval_homogenize_eq_prod_pow natDegree_X_pow_sub_C.le
    hroots_int ![⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩] using 4 with t
  rw [eval_homogenize_X_pow_three_sub_two]
  simp [Fin.prod_univ_two]

/-- **Conformance**: `2 ^ 3 - 2 · 1 ^ 3 = 2 · 3`, so the set of the previous test is not empty. -/
example : ((2, 1), ![1, 1]) ∈ {t : (ℤ × ℤ) × (Fin 2 → ℕ) | IsCoprime t.1.1 t.1.2 ∧
    (t.1.1 ^ 3 - 2 * t.1.2 ^ 3).natAbs = 2 ^ t.2 0 * 3 ^ t.2 1} :=
  ⟨⟨0, 1, by norm_num⟩, by decide⟩

/-- **Rejection: coprimality is load-bearing.** Without it, `(2 ^ k, 0)` solves
`x ^ 3 - 2 y ^ 3 = 2 ^ (3 k)` for every `k`. -/
example : {t : (ℤ × ℤ) × (Fin 1 → ℕ) |
    (t.1.1 ^ 3 - 2 * t.1.2 ^ 3).natAbs = 2 ^ t.2 0}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ ↦ (((2 : ℤ) ^ k, (0 : ℤ)), ![3 * k]))
    (fun k l h ↦ ?_) fun k ↦ ?_
  · have := congrArg (fun t ↦ t.2 0) h
    simp only [Matrix.cons_val_zero] at this
    omega
  · simp only [Set.mem_ofPred_eq, Matrix.cons_val_zero]
    rw [← pow_mul, mul_comm k 3]
    simp [Int.natAbs_pow]

/-- **Rejection: three factors cannot be lowered to two.** `X ^ 2 - 2 Y ^ 2` has two linear
factors, and its Thue–Mahler equation with no primes, `x ^ 2 - 2 y ^ 2 = ± 1`, has infinitely many
coprime solutions: Pell's, generated from `(1, 0)` by `(x, y) ↦ (3 x + 4 y, 2 x + 3 y)`. -/
example : {xy : ℤ × ℤ | IsCoprime xy.1 xy.2 ∧ (xy.1 ^ 2 - 2 * xy.2 ^ 2).natAbs = 1}.Infinite := by
  let s : ℕ → ℤ × ℤ := fun n ↦ Nat.rec (1, 0) (fun _ p ↦ (3 * p.1 + 4 * p.2, 2 * p.1 + 3 * p.2)) n
  have hs : ∀ n, (s n).1 ^ 2 - 2 * (s n).2 ^ 2 = 1 ∧ 1 ≤ (s n).1 ∧ 0 ≤ (s n).2 := by
    intro n
    induction n with
    | zero => simp [s]
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      change (3 * (s n).1 + 4 * (s n).2) ^ 2 - 2 * (2 * (s n).1 + 3 * (s n).2) ^ 2 = 1 ∧
        1 ≤ 3 * (s n).1 + 4 * (s n).2 ∧ 0 ≤ 2 * (s n).1 + 3 * (s n).2
      refine ⟨by linear_combination h1, by linarith, by linarith⟩
  have hmono : StrictMono fun n ↦ (s n).2 := by
    refine strictMono_nat_of_lt_succ fun n ↦ ?_
    change (s n).2 < 2 * (s n).1 + 3 * (s n).2
    linarith [(hs n).2.1, (hs n).2.2]
  refine Set.infinite_of_injective_forall_mem (f := s)
    (fun i j hij ↦ hmono.injective (congrArg Prod.snd hij)) fun n ↦ ?_
  have h := (hs n).1
  exact ⟨⟨(s n).1, -2 * (s n).2, by linear_combination h⟩, by rw [h]; rfl⟩
