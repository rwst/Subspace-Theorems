/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.IrreducibleExponent
public import Mathlib.Analysis.Polynomial.MahlerMeasure

-- Used only inside proofs.
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Where the roots of a small integer polynomial are

Wirsing's third inequality needs to turn a polynomial that is *small at `ξ`* into an algebraic
number *close to `ξ`*, and the only honest way to do that is to look at the roots. This file
collects the four facts about the complex roots of an integer polynomial that the argument uses,
all of them consequences of the factorisation `p = lc(p) ∏ (X - α)` and of Mathlib's Mahler
measure `M(p) = |lc(p)| ∏ max(1, |α|)`:

* a point at distance at least `ρ` from every root has `|p(x)| ≥ (ρ / (2B + 2)) ^ deg p · M(p)`,
  where `B` bounds `|x|` — so a *small* value forces a *nearby* root;
* if every root is bounded by `R`, then `M(p) ≤ |lc(p)| R ^ deg p`, so the leading coefficient is
  comparable to the height;
* if `m` points are pairwise at distance at least `1` and each carries a root, and `deg p ≤ m`,
  then the roots are *exactly* those `m` roots, each simple — so each point carries exactly one;
* the roots of an integer polynomial come in conjugate pairs, so a root that is alone in a disc
  centred on the real axis is real.

Together these say: a polynomial of degree at most `n` that is tiny at `ξ` and merely bounded at
`n - 1` further points has exactly one root near `ξ`, that root is real, and it is as close to `ξ`
as `|p(ξ)| / H(p)`.

## Main results

* `Polynomial.mul_mahlerMeasure_le_norm_eval` and `Polynomial.exists_root_norm_sub_lt`: the
  root-free lower bound and its contrapositive, **a small value produces a nearby root**.
* `Polynomial.mahlerMeasure_le_leadingCoeff_mul_pow`: bounded roots make the leading coefficient
  comparable to the Mahler measure.
* `Polynomial.norm_leadingCoeff_mul_pow_mul_le_norm_eval`: the value at `x` is at least
  `|lc(p)| c ^ deg p |x - α|` when every root other than `α` is at distance at least `c`.
* `Polynomial.roots_toFinset_eq_image`: **one root per point**, with simplicity.
* `Polynomial.conj_mem_roots_map`: the roots of an integer polynomial are stable under
  conjugation.
* `Polynomial.supNorm_le_two_pow_mul_mahlerMeasure`: the naive height is at most
  `2 ^ deg p` times the Mahler measure, the direction Mathlib states with a binomial coefficient.

## Implementation notes

⚠ **The lower bound has to be relative to the Mahler measure, not to the leading coefficient.**
`|p(x)| ≥ ρ ^ d |lc(p)|` is immediate and useless: `|lc(p)|` can be `1` while the height is huge.
What makes the argument work is `|x - α| ≥ (ρ / (2B + 2)) max(1, |α|)` for *every* root, which
turns the product into the Mahler measure; the two cases of that inequality are "`α` is in the
disc of radius `2B + 2`", where `max(1, |α|)` is bounded, and "`α` is outside", where
`|x - α| ≥ |α| / 2` because `|x| ≤ B`.

⚠ **The counting argument needs no multiplicity bookkeeping.** The `m` chosen roots are distinct
because the points are `1` apart and the roots are within `ρ ≤ 1/2` of them, so their image has
`m` elements, sits inside `p.roots.toFinset`, and `p.roots.toFinset.card ≤ card p.roots = deg p ≤
m` closes the sandwich. Simplicity then comes for free from
`Multiset.toFinset_card_eq_card_iff_nodup`, and it is simplicity that makes "exactly one root in
the disc around `ξ`" usable: without it the same root could be counted twice and the product over
the other roots could contain a factor that is not bounded away from zero.

⚠ **Conjugation is the archimedean Krasner lemma.** In the ultrametric analogue of this layer one
proves that a root which is strictly closest to `ξ` generates the same field as `ξ` and is
therefore in the base field. Over `ℝ` the same statement is the remark that the conjugate of a
root is a root at the same distance from a real point, so a root alone in a disc centred on `ℝ`
equals its own conjugate.

## References

Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), Lemma A.3
and Lemma A.6; Y. Bugeaud, *Exponents of Diophantine approximation*, Cambridge University Press
(2016), proof of Theorem 2.6.

This is part of Layer 1.3 of the `DiophantineApproximation` roadmap.
-/

public section

open scoped ENNReal NNReal

namespace Polynomial

/-! ### Products over a multiset of reals -/

/-- A product of nonnegative reals over a multiset is nonnegative. -/
theorem prod_map_nonneg {ι : Type*} {s : Multiset ι} {f : ι → ℝ} (h0 : ∀ x ∈ s, 0 ≤ f x) :
    0 ≤ (s.map f).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      exact mul_nonneg (h0 a (Multiset.mem_cons_self a s))
        (ih fun x hx ↦ h0 x (Multiset.mem_cons_of_mem hx))

/-- Products over a multiset of reals are monotone in the factors, provided the smaller ones are
nonnegative. The `MulLeftMono` instance that `Multiset.prod_map_le_prod_map` asks for does not
exist on `ℝ`, and `Finset.prod_le_prod₀` is about finsets. -/
theorem prod_map_le_prod_map_of_nonneg {ι : Type*} {s : Multiset ι} {f g : ι → ℝ}
    (h0 : ∀ x ∈ s, 0 ≤ f x) (h : ∀ x ∈ s, f x ≤ g x) :
    (s.map f).prod ≤ (s.map g).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      have ha : a ∈ a ::ₘ s := Multiset.mem_cons_self a s
      have h0' : ∀ x ∈ s, 0 ≤ f x := fun x hx ↦ h0 x (Multiset.mem_cons_of_mem hx)
      have h' : ∀ x ∈ s, f x ≤ g x := fun x hx ↦ h x (Multiset.mem_cons_of_mem hx)
      exact mul_le_mul (h a ha) (ih h0' h') (prod_map_nonneg h0')
        (le_trans (h0 a ha) (h a ha))

/-- A constant lower bound on the factors bounds the product from below by a power. -/
theorem pow_card_le_prod_map {ι : Type*} {s : Multiset ι} {f : ι → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x ∈ s, c ≤ f x) : c ^ Multiset.card s ≤ (s.map f).prod := by
  have h2 := prod_map_le_prod_map_of_nonneg (s := s) (f := fun _ : ι ↦ c) (g := f)
    (fun _ _ ↦ hc) h
  rwa [Multiset.map_const', Multiset.prod_replicate] at h2

/-- The norm of a product over a multiset of complex numbers is the product of the norms. -/
theorem norm_multiset_prod_complex (s : Multiset ℂ) : ‖s.prod‖ = (s.map fun z ↦ ‖z‖).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => simp [ih]

/-! ### The value of a complex polynomial as a product over its roots -/

/-- Over `ℂ` every polynomial splits, so it has as many roots as its degree. -/
theorem card_roots_complex (p : ℂ[X]) : Multiset.card p.roots = p.natDegree :=
  splits_iff_card_roots.1 (IsAlgClosed.splits p)

/-- The absolute value of `p` at `x` is the leading coefficient times the product of the
distances from `x` to the roots. -/
theorem norm_eval_eq_prod_roots (p : ℂ[X]) (x : ℂ) :
    ‖eval x p‖ = ‖p.leadingCoeff‖ * (p.roots.map fun a ↦ ‖x - a‖).prod := by
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (card_roots_complex p)]
  rw [eval_mul, eval_C, norm_mul, eval_multiset_prod, Multiset.map_map]
  simp only [Function.comp_def, eval_sub, eval_X, eval_C]
  rw [norm_multiset_prod_complex, Multiset.map_map]
  rfl

/-! ### A small value forces a nearby root -/

/-- **The root-free lower bound.** If every root of `p` is at distance at least `ρ ≤ 1` from `x`,
and `|x| ≤ B` with `1 ≤ B`, then `|p(x)|` is at least `(ρ / (2B + 2)) ^ deg p` times the Mahler
measure of `p`. -/
theorem mul_mahlerMeasure_le_norm_eval {p : ℂ[X]} {x : ℂ} {ρ B : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hB : 1 ≤ B) (hx : ‖x‖ ≤ B) (h : ∀ a ∈ p.roots, ρ ≤ ‖x - a‖) :
    (ρ / (2 * B + 2)) ^ p.natDegree * p.mahlerMeasure ≤ ‖eval x p‖ := by
  have hC0 : (0 : ℝ) < 2 * B + 2 := by linarith
  have hratio : ρ / (2 * B + 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ hC0]
    linarith
  have hratio0 : 0 ≤ ρ / (2 * B + 2) := le_of_lt (div_pos hρ0 hC0)
  have key : ∀ a ∈ p.roots, ρ / (2 * B + 2) * max 1 ‖a‖ ≤ ‖x - a‖ := by
    intro a ha
    rcases le_or_gt ‖a‖ (2 * B + 2) with h1 | h1
    · have hmax : max 1 ‖a‖ ≤ 2 * B + 2 := max_le (by linarith) h1
      have hstep : ρ / (2 * B + 2) * max 1 ‖a‖ ≤ ρ / (2 * B + 2) * (2 * B + 2) :=
        mul_le_mul_of_nonneg_left hmax hratio0
      rw [div_mul_cancel₀ _ (ne_of_gt hC0)] at hstep
      exact hstep.trans (h a ha)
    · have h2 : max 1 ‖a‖ = ‖a‖ := max_eq_right (by linarith)
      have h3 : ‖a‖ - B ≤ ‖x - a‖ := by
        have h4 : ‖a‖ - ‖x‖ ≤ ‖a - x‖ := norm_sub_norm_le a x
        rw [norm_sub_rev] at h4
        linarith
      rw [h2]
      nlinarith
  calc (ρ / (2 * B + 2)) ^ p.natDegree * p.mahlerMeasure
      = ‖p.leadingCoeff‖ *
        ((p.roots.map fun _ ↦ ρ / (2 * B + 2)).prod * (p.roots.map fun a ↦ max 1 ‖a‖).prod) := by
        rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, Multiset.map_const',
          Multiset.prod_replicate, card_roots_complex]
        ring
    _ = ‖p.leadingCoeff‖ * (p.roots.map fun a ↦ ρ / (2 * B + 2) * max 1 ‖a‖).prod := by
        rw [Multiset.prod_map_mul]
    _ ≤ ‖p.leadingCoeff‖ * (p.roots.map fun a ↦ ‖x - a‖).prod := by
        refine mul_le_mul_of_nonneg_left (prod_map_le_prod_map_of_nonneg ?_ key) (norm_nonneg _)
        exact fun a _ ↦ mul_nonneg hratio0 (le_trans zero_le_one (le_max_left _ _))
    _ = ‖eval x p‖ := (norm_eval_eq_prod_roots p x).symm

/-- **A small value produces a nearby root.** The contrapositive of
`Polynomial.mul_mahlerMeasure_le_norm_eval`, with the degree relaxed to a bound. -/
theorem exists_root_norm_sub_lt {p : ℂ[X]} {x : ℂ} {ρ B : ℝ} {n : ℕ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hB : 1 ≤ B) (hx : ‖x‖ ≤ B) (hdeg : p.natDegree ≤ n)
    (hlt : ‖eval x p‖ < (ρ / (2 * B + 2)) ^ n * p.mahlerMeasure) :
    ∃ a ∈ p.roots, ‖x - a‖ < ρ := by
  by_contra hcon
  push Not at hcon
  have hC0 : (0 : ℝ) < 2 * B + 2 := by linarith
  have hratio0 : 0 ≤ ρ / (2 * B + 2) := le_of_lt (div_pos hρ0 hC0)
  have hratio1 : ρ / (2 * B + 2) ≤ 1 := by
    rw [div_le_one hC0]; linarith
  have hmono : (ρ / (2 * B + 2)) ^ n ≤ (ρ / (2 * B + 2)) ^ p.natDegree :=
    pow_le_pow_of_le_one hratio0 hratio1 hdeg
  have hM : 0 ≤ p.mahlerMeasure := mahlerMeasure_nonneg p
  have := mul_mahlerMeasure_le_norm_eval hρ0 hρ1 hB hx fun a ha ↦ hcon a ha
  nlinarith

/-! ### Bounded roots, and the value at a distinguished root -/

/-- If every root of `p` has absolute value at most `R ≥ 1`, then the Mahler measure is at most
`|lc(p)| R ^ deg p`: the leading coefficient carries the whole height. -/
theorem mahlerMeasure_le_leadingCoeff_mul_pow {p : ℂ[X]} {R : ℝ} (hR : 1 ≤ R)
    (h : ∀ a ∈ p.roots, ‖a‖ ≤ R) : p.mahlerMeasure ≤ ‖p.leadingCoeff‖ * R ^ p.natDegree := by
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc (p.roots.map fun a ↦ max 1 ‖a‖).prod ≤ (p.roots.map fun _ ↦ R).prod :=
        prod_map_le_prod_map_of_nonneg (fun a _ ↦ le_trans zero_le_one (le_max_left _ _))
          fun a ha ↦ max_le hR (h a ha)
    _ = R ^ p.natDegree := by
        rw [Multiset.map_const', Multiset.prod_replicate, card_roots_complex]

/-- **The value at a point with one nearby root.** If `α` is a root of the squarefree `p` and
every other root is at distance at least `c ≤ 1` from `x`, then `|p(x)|` is at least
`|lc(p)| c ^ deg p |x - α|`. -/
theorem norm_leadingCoeff_mul_pow_mul_le_norm_eval {p : ℂ[X]} {x α : ℂ} {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hα : α ∈ p.roots) (hnd : p.roots.Nodup)
    (h : ∀ β ∈ p.roots, β ≠ α → c ≤ ‖x - β‖) :
    ‖p.leadingCoeff‖ * c ^ p.natDegree * ‖x - α‖ ≤ ‖eval x p‖ := by
  classical
  have hsplit : ‖x - α‖ * ((p.roots.erase α).map fun a ↦ ‖x - a‖).prod =
      (p.roots.map fun a ↦ ‖x - a‖).prod :=
    Multiset.prod_map_erase (f := fun a ↦ ‖x - a‖) hα
  have hmem : ∀ β ∈ p.roots.erase α, c ≤ ‖x - β‖ := by
    intro β hβ
    have hβ' : β ∈ p.roots := Multiset.mem_of_mem_erase hβ
    refine h β hβ' fun hne ↦ ?_
    rw [hne] at hβ
    exact hnd.notMem_erase hβ
  have hlow : c ^ Multiset.card (p.roots.erase α) ≤
      ((p.roots.erase α).map fun a ↦ ‖x - a‖).prod := pow_card_le_prod_map hc0 hmem
  have hcard : Multiset.card (p.roots.erase α) + 1 = p.natDegree := by
    have hpos : 0 < Multiset.card p.roots := Multiset.card_pos_iff_exists_mem.2 ⟨α, hα⟩
    rw [Multiset.card_erase_of_mem hα, ← card_roots_complex p, Nat.pred_eq_sub_one]
    omega
  have hpow : c ^ p.natDegree ≤ c ^ Multiset.card (p.roots.erase α) :=
    pow_le_pow_of_le_one hc0 hc1 (by omega)
  rw [norm_eval_eq_prod_roots p x, ← hsplit]
  have h1 : c ^ p.natDegree ≤ ((p.roots.erase α).map fun a ↦ ‖x - a‖).prod := hpow.trans hlow
  have h2 : (0 : ℝ) ≤ ‖x - α‖ := norm_nonneg _
  have h3 : (0 : ℝ) ≤ ‖p.leadingCoeff‖ := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg h3 h2)]

/-! ### One root per point -/

/-- **One root per point.** If `p` has degree at most `m`, the `m` points `s i` are pairwise at
distance at least `1`, and `f i` is a root of `p` within `ρ ≤ 1/2` of `s i`, then the roots of `p`
are simple and are exactly the `f i`. -/
theorem roots_toFinset_eq_image {p : ℂ[X]} {m : ℕ} (hdeg : p.natDegree ≤ m) {s f : Fin m → ℂ}
    {ρ : ℝ} (hρ : ρ ≤ 1 / 2) (hs : ∀ i j, i ≠ j → 1 ≤ ‖s i - s j‖) (hf : ∀ i, f i ∈ p.roots)
    (hfs : ∀ i, ‖f i - s i‖ < ρ) :
    p.roots.Nodup ∧ p.roots.toFinset = Finset.image f Finset.univ := by
  classical
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have h1 : ‖s i - s j‖ ≤ ‖s i - f i‖ + ‖f j - s j‖ := by
      have : s i - s j = (s i - f i) + (f j - s j) := by rw [hij]; ring
      rw [this]
      exact norm_add_le _ _
    rw [norm_sub_rev (s i) (f i)] at h1
    have := hs i j hne
    have h2 := hfs i
    have h3 := hfs j
    linarith
  have hsub : Finset.image f Finset.univ ⊆ p.roots.toFinset := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    exact Multiset.mem_toFinset.2 (hf i)
  have himcard : (Finset.image f Finset.univ).card = m := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hle : p.roots.toFinset.card ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
  have hcardroots : Multiset.card p.roots = p.natDegree := card_roots_complex p
  have hsand : p.roots.toFinset.card ≤ (Finset.image f Finset.univ).card := by
    rw [himcard]
    exact le_trans hle (by rw [hcardroots]; exact hdeg)
  have heq : Finset.image f Finset.univ = p.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hsub hsand
  have hcard2 : m ≤ Multiset.card p.roots := by
    have h5 : (Finset.image f Finset.univ).card ≤ p.roots.toFinset.card :=
      Finset.card_le_card hsub
    rw [himcard] at h5
    exact le_trans h5 hle
  have hnd : p.roots.Nodup := by
    refine Multiset.toFinset_card_eq_card_iff_nodup.1 ?_
    have h6 : p.roots.toFinset.card = m := by rw [← heq, himcard]
    rw [h6]
    omega
  exact ⟨hnd, heq.symm⟩

/-! ### Conjugation -/

/-- The complex roots of an integer polynomial are stable under conjugation. -/
theorem conj_mem_roots_map (P : ℤ[X]) {a : ℂ}
    (h : a ∈ (P.map (Int.castRingHom ℂ)).roots) :
    (starRingEnd ℂ) a ∈ (P.map (Int.castRingHom ℂ)).roots := by
  set q : ℂ[X] := P.map (Int.castRingHom ℂ) with hq
  have hq0 : q ≠ 0 := ne_zero_of_mem_roots h
  have hconj : ∀ z : ℂ, (starRingEnd ℂ) (eval z q) = eval ((starRingEnd ℂ) z) q := by
    intro z
    rw [eval_eq_sum_range, eval_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_pow]
    congr 1
    rw [hq, coeff_map]
    simp
  have hroot : eval a q = 0 := ((mem_roots' ).1 h).2
  refine (mem_roots' ).2 ⟨hq0, ?_⟩
  change eval ((starRingEnd ℂ) a) q = 0
  rw [← hconj a, hroot, map_zero]

/-! ### The naive height against the Mahler measure -/

/-- The naive height of an integer polynomial is at most `2 ^ deg P` times the Mahler measure of
its complex image. Mathlib states the bound with the middle binomial coefficient. -/
theorem supNorm_le_two_pow_mul_mahlerMeasure (P : ℤ[X]) :
    P.supNorm ≤ 2 ^ P.natDegree * (P.map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hinj : Function.Injective (Int.castRingHom ℂ) := fun _ _ h ↦ Int.cast_injective h
  have hdeg : (P.map (Int.castRingHom ℂ)).natDegree = P.natDegree :=
    natDegree_map_eq_of_injective hinj P
  have h := supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure (P.map (Int.castRingHom ℂ))
  rw [supNorm_map_complex, hdeg] at h
  refine h.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (mahlerMeasure_nonneg _)
  exact_mod_cast Nat.choose_le_two_pow P.natDegree (P.natDegree / 2)

/-! ### Acceptance criteria -/

/-- **Acceptance test: a small value produces a nearby root.** -/
example {p : ℂ[X]} {x : ℂ} {ρ B : ℝ} {n : ℕ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hB : 1 ≤ B)
    (hx : ‖x‖ ≤ B) (hdeg : p.natDegree ≤ n)
    (hlt : ‖eval x p‖ < (ρ / (2 * B + 2)) ^ n * p.mahlerMeasure) :
    ∃ a ∈ p.roots, ‖x - a‖ < ρ :=
  exists_root_norm_sub_lt hρ0 hρ1 hB hx hdeg hlt

/-- **Acceptance test: the roots of an integer polynomial come in conjugate pairs.** -/
example (P : ℤ[X]) {a : ℂ} (h : a ∈ (P.map (Int.castRingHom ℂ)).roots) :
    (starRingEnd ℂ) a ∈ (P.map (Int.castRingHom ℂ)).roots :=
  conj_mem_roots_map P h

end Polynomial
