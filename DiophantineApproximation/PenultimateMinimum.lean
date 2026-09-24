/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.NorthcottSubspace
public import DiophantineApproximation.ExceptionalSubspace
public import DiophantineApproximation.FormIndexSubspace
public import DiophantineApproximation.GeneralizedRothLemma
public import DiophantineApproximation.LogComparison
public import DiophantineApproximation.SubspaceKeyInequality
public import DiophantineApproximation.SubspaceNormal

/-!
# The penultimate-minimum theorem

This file is Bombieri–Gubler's Theorem 7.5.13, Steps IV and VI: for forms `L v i` linearly
independent at every place of `S` — every infinite place together with a finite set `Sfin` — and
exponents `c v i` of negative weight, the spans

```text
V(Q) = span K (approxDomain Sfin L c Q)
```

of the approximation domains of rank `n` form a **finite** set of subspaces of `Kⁿ⁺¹`.

The argument is by contradiction, and it is where every layer of the Subspace machinery meets.
Suppose the spans of rank `n` are unbounded in the level. Layer 5.4 makes all but finitely many
of them have height at least a positive multiple of `log Q`, so there is a chain of levels
`Q 0, …, Q m` whose logarithms grow at the rate `2 σ⁻¹` and whose spans all have large height.
Take multidegrees `d h ≈ D / log (Q h)`, which then decrease at the rate `σ`, and let `P` be the
multihomogeneous auxiliary polynomial of Layer 5.2 at that multidegree. Layer 5.3 — the
generalized Roth lemma — turns the height hypothesis into a small index of `P` along the forms
`M h` cutting out the `V(Q h)`; `DiophantineApproximation/FormIndexSubspace.lean` turns that into
a derivative `∂_I P` of small weighted order that does not vanish identically on
`V(Q 0) × ⋯ × V(Q m)`; Layer 5.5 replaces it by a derivative `∂_{I'} P` that does not vanish at
an explicit point `X` of small height in that product. Step VI, which is
`DiophantineApproximation/SubspaceKeyInequality.lean`, bounds `∂_{I'} P (X)` above at every place
of `S` and below by the product formula. Letting `D → ∞` against a fixed `m` gives the
contradiction.

## Main results

* `NumberField.exists_forall_not_chain`: **Steps IV and VI**, the whole contradiction. There are
  `m`, `σ > 0` and `Qlow` such that no `m + 1` levels with `log (Q h) ≥ Qlow`, growing at the
  rate `2 σ⁻¹`, can all have rank `n` and height at least `ε log (Q h) / (4 |S|) - C₅`.
* `NumberField.exists_forall_approxSpan_mem`: beyond a level, `V(Q)` lies in the finite set of
  exceptional subspaces of Layer 5.4.
* `NumberField.finite_setOf_approxSpan`: **the milestone**, Theorem 7.5.13.
* `NumberField.logHeight_approxSpan_le`: the upper half of Lemma 7.5.21 without its hypothesis
  that the level be large, which is what covers a bounded range of levels.
* `Submodule.exists_basis_subset` and `Submodule.logHeight_eq_logHeight_of_forall_dotProduct`:
  a spanning set contains a basis, and the height of a hyperplane is the height of its normal
  vector (Bombieri–Gubler's (7.28)).
* `NumberField.PenultimateMinimum.le_mul_of_le_mul_div_add_one`,
  `NumberField.PenultimateMinimum.not_of_key_inequality`,
  `NumberField.PenultimateMinimum.two_mul_mul_le_div`,
  `NumberField.PenultimateMinimum.ceil_div_le_mul_ceil_div` and
  `NumberField.PenultimateMinimum.log_box_eq`: the arithmetic of the proof, stated over `ℝ`
  alone.

## Implementation notes

⚠ **The chain rule is not needed a third time.** Layer 5.3 measures the index in the coordinates
in which the forms are the variables, and Layer 5.5 wants a derivative in the original ones. The
change of coordinates *is* a block-wise linear substitution
(`MvPolynomial.substFormInv_eq_linSubst`), so Layer 5.5's own `MvPolynomial.shift_linSubst` and
`MvPolynomial.exists_coeff_ne_zero_of_coeff_linSubst_ne_zero` transport a surviving coefficient
between the two systems **with the same degree in every block** — which is exactly what makes
the two weighted orders agree. That is `FormIndexSubspace.lean`, and it is all the bridge there
is.

⚠ **The pattern of Layer 5.2 enters only as a two-sided bound.** Step VI consumes
`|ρ j - mean| ≤ Δ` for the exponents `ρ j = ∑ h, J (h, j) / d h` of every surviving monomial;
Layer 5.2's interval `(m/(n+1) - 2 m η, m/(n+1) + 2 n m η)` is asymmetric, and `n ≥ 1` absorbs
it into `Δ = 2 n (m+1) η`. Which end is wider is the caller's business.

⚠ **Two invariants of the system of exponents, not one.** Besides `NumberField.approxWeight`,
which is negative, the estimate needs `NumberField.approxAbsWeight`, the weight of the
`|c v i|`; it is the quantity `η` is chosen against, and it is the only place where the size of
the exponents rather than their sum enters. `NumberField.PenultimateMinimum.two_mul_mul_le_div`
is that choice.

⚠ **`S` must contain every archimedean place, and that is where it is used.** Away from `S` the
local bound carries no constant and the point is integral, so the product formula is applied
with `Sinf = univ`. This is the same convention as Layers 4 and 5.4.

⚠ **The heartbeat budget is per declaration, which is why the arithmetic is factored out.** The
proof of `exists_forall_not_chain` constructs a dozen parameters before it can state the
hypothesis of Layer 5.3, and every `field_simp`, `positivity` and `linarith` on the way spends
from the same budget. The five lemmas of `NumberField.PenultimateMinimum` carry all the
inequalities that have divisions in them; inside the main proof only `linarith only` is used, on
goals whose atoms are already in normal form.

⚠ **The milestone is stated for `1 ≤ Q`, and the bounded range is covered separately.** Layer
5.4 states its dichotomy only for `C₄ / ε ≤ log Q`, but its *upper* bound needs no such
hypothesis; `NumberField.logHeight_approxSpan_le` restates it for every level, and Northcott for
subspaces (`ArithmeticHeights` 3.7) then makes the levels below the threshold contribute
finitely many spans. Bombieri–Gubler leave this to the reader.
-/

@[expose] public section

open Finset Module

noncomputable section

namespace NumberField.PenultimateMinimum

/-- **The height hypothesis of the generalized Roth lemma, in arithmetic form.** -/
theorem le_mul_of_le_mul_div_add_one {ε Scard Qlow D q dh Mh K₁ C₅ C₅' L : ℝ}
    (hε : 0 < ε) (hS : 0 < Scard) (hQlow : 0 < Qlow) (hD : 0 < D) (hq : 0 < q)
    (hQq : Qlow ≤ q) (hMh : 0 ≤ Mh) (hC₅ : C₅ ≤ C₅') (hC₅0 : 0 ≤ C₅')
    (hQbig : 8 * Scard * (K₁ + C₅') / ε ≤ Qlow) (hDbig : 8 * Scard * K₁ / ε ≤ D)
    (hlow : ε * q / (4 * Scard) - C₅ ≤ Mh) (hdh : D / q ≤ dh)
    (hL : L ≤ K₁ * (D / Qlow + 1)) :
    L ≤ dh * Mh := by
  have hεne : ε ≠ 0 := hε.ne'
  have hSne : Scard ≠ 0 := hS.ne'
  have hQne : Qlow ≠ 0 := hQlow.ne'
  have hqne : q ≠ 0 := hq.ne'
  have hr0 : (0 : ℝ) ≤ D / Qlow := (div_pos hD hQlow).le
  have hDq0 : (0 : ℝ) ≤ D / q := (div_pos hD hq).le
  have h8S : (0 : ℝ) < 8 * Scard := by linarith
  set G : ℝ := ε / (8 * Scard) with hGdef
  have hG0 : 0 < G := by rw [hGdef]; exact div_pos hε h8S
  have hKQ : K₁ + C₅' ≤ G * Qlow := by
    have h := mul_le_mul_of_nonneg_left hQbig hG0.le
    have he : G * (8 * Scard * (K₁ + C₅') / ε) = K₁ + C₅' := by rw [hGdef]; field_simp
    rwa [he] at h
  have hKD : K₁ ≤ G * D := by
    have h := mul_le_mul_of_nonneg_left hDbig hG0.le
    have he : G * (8 * Scard * K₁ / ε) = K₁ := by rw [hGdef]; field_simp
    rwa [he] at h
  have hprod : (K₁ + C₅') * (D / Qlow) ≤ G * D := by
    have h1 : (K₁ + C₅') * (D / Qlow) ≤ G * Qlow * (D / Qlow) :=
      mul_le_mul_of_nonneg_right hKQ hr0
    have h2 : G * Qlow * (D / Qlow) = G * D := by field_simp
    rwa [h2] at h1
  have heq : D / q * (ε * q / (4 * Scard) - C₅) = 2 * (G * D) - D / q * C₅ := by
    rw [hGdef]; field_simp; ring
  have hCb : D / q * C₅ ≤ C₅' * (D / Qlow) := by
    have h1 : D / q * C₅ ≤ D / q * C₅' := mul_le_mul_of_nonneg_left hC₅ hDq0
    have h2 : D / q ≤ D / Qlow := div_le_div_of_nonneg_left hD.le hQlow hQq
    have h3 : D / q * C₅' ≤ D / Qlow * C₅' := mul_le_mul_of_nonneg_right h2 hC₅0
    calc D / q * C₅ ≤ D / q * C₅' := h1
      _ ≤ D / Qlow * C₅' := h3
      _ = C₅' * (D / Qlow) := by ring
  have hstep2 : D / q * (ε * q / (4 * Scard) - C₅) ≤ D / q * Mh :=
    mul_le_mul_of_nonneg_left hlow hDq0
  have hstep1 : D / q * Mh ≤ dh * Mh := mul_le_mul_of_nonneg_right hdh hMh
  linarith only [hL, hprod, hKD, heq, hCb, hstep2, hstep1]

/-- **The final comparison of Step VI, in arithmetic form**: the inequality the product formula
produces is incompatible with a degree `D` so large that `Ca log (D + 2) + E < ε D / (8 n₁)`. -/
theorem not_of_key_inequality {tw n₁ m₁ Ca Cb C₂ Hb bl Ls Dsum D Qlow rr lg ε Qsum AW mixed
    Ph : ℝ}
    (htw0 : 0 ≤ tw) (hn₁ : 0 < n₁) (hm₁ : 0 < m₁) (hCb0 : 0 ≤ Cb)
    (hDsum0 : 0 ≤ Dsum) (hD0 : 0 < D) (hε : 0 < ε) (hrr0 : 0 ≤ rr) (hrr : rr * Qlow = D)
    (hCa : Ca = 2 * tw * n₁) (hCble : tw * bl + C₂ + 2 * Hb ≤ Cb)
    (hLsle : Ls ≤ m₁ * lg) (hDsumle : Dsum ≤ m₁ * (rr + 1)) (hPh : Ph ≤ C₂ * Dsum)
    (hQlowCb : 8 * n₁ * Cb / ε ≤ Qlow) (hmix : mixed ≤ -(m₁ * ε / (4 * n₁)))
    (hkey : 0 ≤ 2 * tw * n₁ * Ls + tw * Dsum * bl + Ph + 2 * Dsum * Hb + D * mixed + Qsum * AW)
    (hDlog : Ca * lg + (Cb + Qsum * AW / m₁) < ε / (8 * n₁) * D) :
    False := by
  subst hCa
  have hεne : ε ≠ 0 := hε.ne'
  have hn₁ne : n₁ ≠ 0 := hn₁.ne'
  have hm₁ne : m₁ ≠ 0 := hm₁.ne'
  have h8n : (0 : ℝ) < 8 * n₁ := by linarith
  set G : ℝ := ε / (8 * n₁) with hGdef
  have hG0 : 0 < G := by rw [hGdef]; exact div_pos hε h8n
  have h1 : 2 * tw * n₁ * Ls ≤ 2 * tw * n₁ * (m₁ * lg) :=
    mul_le_mul_of_nonneg_left hLsle (by positivity)
  have h2 : tw * Dsum * bl + Ph + 2 * Dsum * Hb ≤ Dsum * Cb := by
    have hA : Dsum * (tw * bl + C₂ + 2 * Hb) ≤ Dsum * Cb :=
      mul_le_mul_of_nonneg_left hCble hDsum0
    linarith only [hA, hPh]
  have h3 : Dsum * Cb ≤ m₁ * (rr + 1) * Cb := mul_le_mul_of_nonneg_right hDsumle hCb0
  have h4 : D * mixed ≤ D * -(m₁ * ε / (4 * n₁)) := mul_le_mul_of_nonneg_left hmix hD0.le
  have hCbG : Cb ≤ G * Qlow := by
    have h := mul_le_mul_of_nonneg_left hQlowCb hG0.le
    have he : G * (8 * n₁ * Cb / ε) = Cb := by rw [hGdef]; field_simp
    rwa [he] at h
  have h5 : Cb * rr ≤ G * D := by
    have h := mul_le_mul_of_nonneg_right hCbG hrr0
    rwa [show G * Qlow * rr = G * D by rw [← hrr]; ring] at h
  have h6 : m₁ * (Cb * rr) ≤ m₁ * (G * D) := mul_le_mul_of_nonneg_left h5 hm₁.le
  have h7 := mul_lt_mul_of_pos_left hDlog hm₁
  have he7 : m₁ * (2 * tw * n₁ * lg + (Cb + Qsum * AW / m₁))
      = 2 * tw * n₁ * (m₁ * lg) + m₁ * Cb + Qsum * AW := by field_simp; ring
  rw [he7] at h7
  have he8 : m₁ * (G * D) = m₁ * (ε / (8 * n₁) * D) := by rw [hGdef]
  have hmixeq : D * -(m₁ * ε / (4 * n₁)) = -(2 * (m₁ * (G * D))) := by
    rw [hGdef]; field_simp; ring
  rw [hmixeq] at h4
  rw [← he8] at h7
  linarith only [hkey, h1, h2, h3, h4, h6, h7]

/-- **The choice of `η`**: the weight of the absolute values of the exponents is charged at most
a quarter of `ε`. -/
theorem two_mul_mul_le_div {ε AW η n : ℝ} (hε : 0 < ε) (hAW : 0 ≤ AW) (hn : 0 ≤ n)
    (hη0 : 0 < η) (hle : η ≤ ε / (8 * (n + 1) ^ 2 * (AW + 1))) :
    2 * n * η * AW ≤ ε / (4 * (n + 1)) := by
  have hn1 : (0 : ℝ) < n + 1 := by linarith
  have hA1 : (0 : ℝ) < AW + 1 := by linarith
  have hn1ne : n + 1 ≠ 0 := hn1.ne'
  have hA1ne : AW + 1 ≠ 0 := hA1.ne'
  have hηAW : (0 : ℝ) ≤ η * AW := mul_nonneg hη0.le hAW
  have hs1 : 2 * n * η * AW ≤ 2 * (n + 1) * (η * AW) := by
    have h := mul_le_mul_of_nonneg_right (show (2 : ℝ) * n ≤ 2 * (n + 1) by linarith) hηAW
    linarith only [h]
  have hs2 : 2 * (n + 1) * (η * AW)
      ≤ 2 * (n + 1) * (ε / (8 * (n + 1) ^ 2 * (AW + 1)) * AW) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle hAW) (by linarith)
  have heq : 2 * (n + 1) * (ε / (8 * (n + 1) ^ 2 * (AW + 1)) * AW)
      = ε / (4 * (n + 1)) * (AW / (AW + 1)) := by field_simp; ring
  have h3 : AW / (AW + 1) ≤ 1 := by rw [div_le_one hA1]; linarith
  have h4 : (0 : ℝ) ≤ ε / (4 * (n + 1)) := by positivity
  have h5 : ε / (4 * (n + 1)) * (AW / (AW + 1)) ≤ ε / (4 * (n + 1)) * 1 :=
    mul_le_mul_of_nonneg_left h3 h4
  linarith only [hs1, hs2, heq, h5]

/-- **The multidegrees decrease geometrically** when the levels grow geometrically. -/
theorem ceil_div_le_mul_ceil_div {σ D a b : ℝ} (hσ0 : 0 < σ) (hD : 0 < D)
    (ha : 0 < a) (hb : 0 < b) (hab : 2 * σ⁻¹ * a ≤ b) (hDa : 2 * a ≤ σ * D) :
    ((⌈D / b⌉₊ : ℕ) : ℝ) ≤ σ * ((⌈D / a⌉₊ : ℕ) : ℝ) := by
  have hσne : σ ≠ 0 := hσ0.ne'
  have hane : a ≠ 0 := ha.ne'
  have hqsσ : 2 * a ≤ σ * b := by
    have h0 := mul_le_mul_of_nonneg_left hab hσ0.le
    rwa [show σ * (2 * σ⁻¹ * a) = 2 * a by field_simp] at h0
  have hqc2 : (0 : ℝ) < 2 * a := by linarith
  have hdiv : D / b ≤ σ * D / (2 * a) := by
    rw [div_le_div_iff₀ hb hqc2]
    have h := mul_le_mul_of_nonneg_left hqsσ hD.le
    linarith only [h]
  have h1 : ((⌈D / b⌉₊ : ℕ) : ℝ) ≤ D / b + 1 := (Nat.ceil_lt_add_one (div_pos hD hb).le).le
  have h2 : D / a ≤ ((⌈D / a⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h3 : (1 : ℝ) ≤ σ * D / (2 * a) := by rw [le_div_iff₀ hqc2]; linarith
  calc ((⌈D / b⌉₊ : ℕ) : ℝ) ≤ D / b + 1 := h1
    _ ≤ σ * D / (2 * a) + σ * D / (2 * a) := by linarith
    _ = σ * (D / a) := by field_simp; ring
    _ ≤ σ * ((⌈D / a⌉₊ : ℕ) : ℝ) := mul_le_mul_of_nonneg_left h2 hσ0.le

/-- **The logarithm of the combinatorial constant of the key inequality.** -/
theorem log_box_eq {ι ρ : Type*} [Fintype ι] [Fintype ρ] {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card ι = n + 1) (hcardρ : Fintype.card ρ = n) {m : ℕ} (d : Fin (m + 1) → ℕ) :
    Real.log ((∏ p : Fin (m + 1) × ι, ((d p.1 : ℝ) + 1)) ^ 2
        * (2 * Fintype.card ι * Fintype.card ρ : ℝ) ^ (∑ h, d h))
      = 2 * (((n : ℝ) + 1) * ∑ h, Real.log ((d h : ℝ) + 1))
        + (∑ h, (d h : ℝ)) * Real.log (2 * ((n : ℝ) + 1) * (n : ℝ)) := by
  have hne : ∀ p : Fin (m + 1) × ι, ((d p.1 : ℝ) + 1) ≠ 0 := fun p ↦ by positivity
  have hprodne : (∏ p : Fin (m + 1) × ι, ((d p.1 : ℝ) + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ ↦ hne p
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hbaseeq : (2 * (Fintype.card ι : ℝ) * (Fintype.card ρ : ℝ))
      = 2 * ((n : ℝ) + 1) * (n : ℝ) := by
    rw [hcard, hcardρ]; push_cast; ring
  have hbasepos : (0 : ℝ) < 2 * ((n : ℝ) + 1) * (n : ℝ) :=
    mul_pos (by linarith) (by linarith)
  rw [hbaseeq, Real.log_mul (pow_ne_zero 2 hprodne) (pow_ne_zero _ hbasepos.ne'), Real.log_pow,
    Real.log_pow, Real.log_prod (fun p _ ↦ hne p), Fintype.sum_prod_type]
  have hinner : ∀ h : Fin (m + 1), ∑ _i : ι, Real.log ((d h : ℝ) + 1)
      = ((n : ℝ) + 1) * Real.log ((d h : ℝ) + 1) := by
    intro h
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun h _ ↦ hinner h, ← Finset.mul_sum]
  push_cast
  ring

end NumberField.PenultimateMinimum

namespace Submodule

variable {K : Type*} [Field K] {ι : Type*}

/-- **A spanning set contains a basis**, indexed by `Fin n` when the span has dimension `n`. -/
theorem exists_basis_subset [Finite ι] {V : Submodule K (ι → K)} {s : Set (ι → K)}
    (hs : Submodule.span K s = V) {n : ℕ} (hn : Module.finrank K V = n) :
    ∃ y : Fin n → ι → K, LinearIndependent K y ∧
      Submodule.span K (Set.range y) = V ∧ ∀ l, y l ∈ s := by
  classical
  obtain ⟨t, hts, hspan, hli⟩ := exists_linearIndependent K s
  have hfin : t.Finite := hli.finite
  have : Fintype t := hfin.fintype
  have hspanV : Submodule.span K t = V := by rw [hspan, hs]
  have hcard : Fintype.card t = n := by
    rw [← hn, ← hspanV, finrank_span_set_eq_card hli]
    exact (Set.toFinset_card t).symm
  obtain ⟨e⟩ : Nonempty (t ≃ Fin n) := ⟨Fintype.equivFinOfCardEq hcard⟩
  refine ⟨fun l ↦ (e.symm l : ι → K), hli.comp e.symm e.symm.injective, ?_, ?_⟩
  · rw [← hspanV]
    congr 1
    ext x
    constructor
    · rintro ⟨l, rfl⟩
      exact (e.symm l).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp⟩
  · intro l
    exact hts (e.symm l).2

variable [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Height.AdmissibleAbsValues K]

omit [DecidableEq ι] in
/-- **The height of a hyperplane is the height of its normal vector** (Bombieri–Gubler's
(7.28)). -/
theorem logHeight_eq_logHeight_of_forall_dotProduct {V : Submodule K (ι → K)} {ζ : ι → K}
    (hζ : ζ ≠ 0) (hV : ∀ x, x ∈ V ↔ ζ ⬝ᵥ x = 0) :
    V.logHeight = Height.logHeight ζ := by
  classical
  set A : Matrix Unit ι K := fun _ ↦ ζ with hA
  have hker : LinearMap.ker A.mulVecLin = V := by
    ext x
    rw [LinearMap.mem_ker, hV x]
    constructor
    · intro h
      exact congrFun h ()
    · intro h
      funext u
      exact h
  have hrow : Submodule.span K (Set.range A.row) = Submodule.span K {ζ} := by
    congr 1
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact rfl
    · intro hx
      exact ⟨(), hx.symm ▸ rfl⟩
  have := Matrix.logHeight_ker_mulVecLin (K := K) A
  rw [hker, hrow, Submodule.logHeight_span_singleton hζ] at this
  exact this

end Submodule

namespace NumberField

open MvPolynomial Height exteriorPower PenultimateMinimum

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]
  [LinearOrder ι] [Nonempty ι]

omit [DecidableEq ι] in
/-- **The height of `V(Q)` is at most a multiple of `log Q`**, for every level: the upper half of
Lemma 7.5.21 without its hypothesis that `Q` be large. -/
theorem logHeight_approxSpan_le {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {cf : AbsoluteValue K ℝ → ι → ℝ} {n : ℕ}
    (hLinf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLfin : ∀ w ∈ Sfin, LinearIndependent K (L w.1)) :
    ∃ C₆ : ℝ, ∀ Q : ℝ, 1 ≤ Q → Module.finrank K (approxSpan Sfin L cf Q) = n →
      (approxSpan Sfin L cf Q).logHeight
        ≤ (n : ℝ) * (∑ w : InfinitePlace K, (w.mult : ℝ) * cMax cf w.1
            + ∑ w ∈ Sfin, cMax cf w.1) * Real.log Q + C₆ := by
  obtain ⟨C, hC1, hC⟩ := exists_one_le_forall_mulHeight_plucker_le (c := cf) (n := n) hLinf hLfin
  refine ⟨Real.log C, fun Q hQ hrank ↦ ?_⟩
  have hQ0 : (0 : ℝ) < Q := by linarith
  obtain ⟨y, hymem, hyli, hyspan⟩ :=
    Submodule.exists_linearIndependent_fin (s := approxDomain Sfin L cf Q) (n := n) hrank
  have hVeq : Submodule.span K (Set.range y) = approxSpan Sfin L cf Q := hyspan
  have hHeq : (approxSpan Sfin L cf Q).logHeight
      = Real.log (Height.mulHeight (plucker n y)) := by
    rw [← hVeq, Submodule.logHeight_eq_log_mulHeight, Submodule.mulHeight_span_range hyli]
  have hH1 : 1 ≤ Height.mulHeight (plucker n y) := Height.one_le_mulHeight _
  rw [hHeq]
  refine le_trans (Real.log_le_log (by linarith) (hC Q hQ y hyli hymem)) (le_of_eq ?_)
  rw [Real.log_mul (by linarith : C ≠ 0) (Real.rpow_pos_of_pos hQ0 _).ne', Real.log_rpow hQ0]
  ring


omit [DecidableEq ι] in
/-- **No chain of levels of rank `n` whose heights grow with the level**, which is the whole of
Bombieri--Gubler's Steps IV and VI. -/
theorem exists_forall_not_chain {n : ℕ} (hn : 1 ≤ n) (hcard : Fintype.card ι = n + 1)
    {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    {cf : AbsoluteValue K ℝ → ι → ℝ}
    (hLinf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLfin : ∀ w ∈ Sfin, LinearIndependent K (L w.1))
    {ε : ℝ} (hε : 0 < ε) (hweight : approxWeight Sfin cf ≤ -ε / 2) (C₅ : ℝ) :
    ∃ (m : ℕ) (σ Qlow : ℝ), 0 < σ ∧
      ∀ Q : Fin (m + 1) → ℝ, (∀ h, 1 < Q h) → (∀ h, Qlow ≤ Real.log (Q h)) →
        (∀ h : Fin m, 2 * σ⁻¹ * Real.log (Q h.castSucc) ≤ Real.log (Q h.succ)) →
        (∀ h, Module.finrank K (approxSpan Sfin L cf (Q h)) = n) →
        (∀ h, ε * Real.log (Q h)
              / (4 * ((Fintype.card (InfinitePlace K) + Sfin.card : ℕ) : ℝ)) - C₅
            ≤ (approxSpan Sfin L cf (Q h)).logHeight) → False := by
  classical
  set AW : ℝ := approxAbsWeight Sfin cf with hAWdef
  have hAW0 : 0 ≤ AW := approxAbsWeight_nonneg Sfin cf
  -- the matrices of the forms at the places of `S`
  set A : (InfinitePlace K ⊕ ↥Sfin) → Matrix ι ι K :=
    fun a ↦ formMatrix L (sPlace Sfin a) with hAdef
  have hA : ∀ a, IsUnit (A a).det := by
    rintro (w | w)
    · exact isUnit_det_formMatrix (hLinf w)
    · exact isUnit_det_formMatrix (hLfin w w.2)
  -- the parameter `η`, chosen against the weight of the absolute values of the exponents
  set η : ℝ := min 1 (ε / (8 * ((n : ℝ) + 1) ^ 2 * (AW + 1))) with hηdef
  have hη0 : 0 < η := by
    refine lt_min zero_lt_one (div_pos hε ?_)
    positivity
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηW : 2 * (n : ℝ) * η * AW ≤ ε / (4 * ((n : ℝ) + 1)) :=
    two_mul_mul_le_div hε hAW0 (Nat.cast_nonneg n) hη0 (min_le_right _ _)
  -- the number of blocks
  set Scard : ℝ := ((Fintype.card (InfinitePlace K) + Sfin.card : ℕ) : ℝ) with hScard
  set cardS : ℝ := ((Fintype.card (InfinitePlace K ⊕ ↥Sfin) : ℕ) : ℝ) with hcardS
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) * η ^ 2 := by positivity
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 4 * Real.log (2 * ((n : ℝ) + 1) * cardS)
      < ((n : ℝ) + 1) * ((n : ℝ) + 2) * η ^ 2 * ((m : ℝ) + 1) := by
    obtain ⟨m, hmm⟩ := exists_nat_gt
      ((4 * Real.log (2 * ((n : ℝ) + 1) * cardS)) / (((n : ℝ) + 1) * ((n : ℝ) + 2) * η ^ 2))
    refine ⟨m, ?_⟩
    rw [div_lt_iff₀ hpos] at hmm
    linarith only [hmm, hpos]
  -- the ratio `σ` of consecutive multidegrees
  set σ : ℝ := (η / 4) ^ (2 ^ m) with hσdef
  have hη40 : (0 : ℝ) < η / 4 := by linarith
  have hσ0 : 0 < σ := by positivity
  have hσ1 : σ ≤ 1 / 2 := by
    have h1 : σ ≤ (η / 4) ^ 1 :=
      pow_le_pow_of_le_one hη40.le (by linarith) Nat.one_le_two_pow
    rw [pow_one] at h1
    linarith
  have hσrpow : σ ^ ((1 / 2 : ℝ) ^ m) = η / 4 := by
    rw [hσdef, ← Real.rpow_natCast (η / 4) (2 ^ m), ← Real.rpow_mul hη40.le]
    have hmul : ((2 ^ m : ℕ) : ℝ) * (1 / 2 : ℝ) ^ m = 1 := by
      push_cast
      rw [← mul_pow]
      norm_num
    rw [hmul, Real.rpow_one]
  -- Layer 5.2: the auxiliary polynomial
  have hmκ : 4 * Real.log (2 * ((n : ℝ) + 1) * (Fintype.card (InfinitePlace K ⊕ ↥Sfin) : ℕ))
      < ((n : ℝ) + 1) * ((n : ℝ) + 2) * η ^ 2 * (Fintype.card (Fin (m + 1)) : ℕ) := by
    rw [Fintype.card_fin]
    push_cast
    exact hm
  obtain ⟨C₂, C₃, D₀, haux⟩ :=
    MvPolynomial.exists_ne_zero_isMultiHomogeneous_forall_coeff_blockSubst_hasseDeriv_eq_zero
      (κ := Fin (m + 1)) hn hcard A hA hη0 hmκ
  -- the constants of the final comparison
  set tw : ℝ := (Height.totalWeight K : ℝ) with htwdef
  set B : ℕ := ⌈2 * (n : ℝ) / η + 1⌉₊ with hBdef
  set Hβ : ℝ := ∑ θ, Real.log (Height.mulHeight₁ (refFamily L Sfin B θ)) with hHβdef
  set Ca : ℝ := 2 * tw * ((n : ℝ) + 1) with hCadef
  set Cb : ℝ :=
    max (tw * Real.log (2 * ((n : ℝ) + 1) * (n : ℝ)) + max C₂ 0 + 2 * Hβ) 0 with hCbdef
  set K₁ : ℝ := (n : ℝ) * σ⁻¹ * ((m : ℝ) + 1) * (max C₂ 0 + 4 * tw) with hK1def
  set Qlow : ℝ :=
    max 1 (max (8 * ((n : ℝ) + 1) * Cb / ε) (8 * Scard * (K₁ + max C₅ 0) / ε)) with hQlowdef
  refine ⟨m, σ, Qlow, hσ0, ?_⟩
  intro Q hQ1 hQlowh hgrow hrank hhgt
  have hlk : 1 + n = Fintype.card ι := by rw [hcard]; ring
  set q : Fin (m + 1) → ℝ := fun h ↦ Real.log (Q h) with hqdef
  have hq0 : ∀ h, 0 < q h := fun h ↦ Real.log_pos (hQ1 h)
  have hQlow1 : (1 : ℝ) ≤ Qlow := le_max_left _ _
  set Qsum : ℝ := ∑ h, q h with hQsumdef
  have hqQsum : ∀ h, q h ≤ Qsum :=
    fun h ↦ Finset.single_le_sum (fun h' _ ↦ (hq0 h').le) (Finset.mem_univ h)
  -- a basis of each `V(Q h)` inside the domain, and its normal vector
  have hbasis : ∀ h, ∃ yb : Fin n → ι → K, LinearIndependent K yb ∧
      Submodule.span K (Set.range yb) = approxSpan Sfin L cf (Q h) ∧
      ∀ l, yb l ∈ approxDomain Sfin L cf (Q h) :=
    fun h ↦ Submodule.exists_basis_subset rfl (hrank h)
  choose yb hyb_li hyb_span hyb_mem using hbasis
  have hnormal : ∀ h, ∃ ζ : ι → K, ζ ≠ 0 ∧
      ∀ x, x ∈ approxSpan Sfin L cf (Q h) ↔ ζ ⬝ᵥ x = 0 := by
    intro h
    obtain ⟨ζ, hζ0, hζV, -⟩ := Submodule.exists_normal (hyb_li h) (hyb_span h) hlk
    exact ⟨ζ, hζ0, hζV⟩
  choose M hM0 hMV using hnormal
  have hMh : ∀ h, Height.logHeight (M h) = (approxSpan Sfin L cf (Q h)).logHeight :=
    fun h ↦ (Submodule.logHeight_eq_logHeight_of_forall_dotProduct (hM0 h) (hMV h)).symm
  -- the degree parameter `D`
  set D₁ : ℝ := max (max ((D₀ : ℝ) * Qsum) (2 * Qsum / σ)) (8 * Scard * K₁ / ε) with hD1def
  have htw0 : (0 : ℝ) ≤ tw := Nat.cast_nonneg _
  have hCa0 : (0 : ℝ) ≤ Ca := by positivity
  have hεc : (0 : ℝ) < ε / (8 * ((n : ℝ) + 1)) := by positivity
  obtain ⟨D, hDD₁, hD0, hDlog⟩ := Real.exists_le_and_mul_log_add_lt
    (B := Ca) (E := Cb + Qsum * AW / ((m : ℝ) + 1)) (D₁ := D₁) hCa0 hεc
  -- the multidegree
  set d : Fin (m + 1) → ℕ := fun h ↦ ⌈D / q h⌉₊ with hddef
  have hdq : ∀ h, D ≤ (d h : ℝ) * q h := by
    intro h
    have h1 : D / q h ≤ (d h : ℝ) := Nat.le_ceil _
    rwa [div_le_iff₀ (hq0 h)] at h1
  have hdq' : ∀ h, (d h : ℝ) * q h ≤ D + q h := by
    intro h
    have hqne : q h ≠ 0 := (hq0 h).ne'
    have h1 : (d h : ℝ) < D / q h + 1 := Nat.ceil_lt_add_one (div_pos hD0 (hq0 h)).le
    have h2 : ((d h : ℝ)) * q h ≤ (D / q h + 1) * q h :=
      mul_le_mul_of_nonneg_right h1.le (hq0 h).le
    have h3 : (D / q h + 1) * q h = D + q h := by field_simp
    linarith
  have hdpos : ∀ h, 0 < d h := fun h ↦ Nat.ceil_pos.mpr (div_pos hD0 (hq0 h))
  have hd1 : ∀ h, 1 ≤ d h := hdpos
  have hdD₀ : ∀ h, D₀ ≤ d h := by
    intro h
    have hbig : (D₀ : ℝ) * Qsum ≤ D :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hDD₁
    have h1 : (D₀ : ℝ) ≤ D / q h := by
      rw [le_div_iff₀ (hq0 h)]
      have : (D₀ : ℝ) * q h ≤ (D₀ : ℝ) * Qsum :=
        mul_le_mul_of_nonneg_left (hqQsum h) (Nat.cast_nonneg _)
      linarith
    exact_mod_cast le_trans h1 (Nat.le_ceil _)
  have hratio : ∀ h : Fin m, (d h.succ : ℝ) ≤ σ * d h.castSucc := by
    intro h
    have hDσ : 2 * Qsum / σ ≤ D :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hDD₁
    have hA2 : 2 * Qsum ≤ σ * D := by
      rw [div_le_iff₀ hσ0, mul_comm] at hDσ
      linarith
    have h2qc : 2 * q h.castSucc ≤ σ * D := by linarith [hqQsum h.castSucc]
    exact ceil_div_le_mul_ceil_div hσ0 hD0 (hq0 h.castSucc) (hq0 h.succ) (hgrow h) h2qc
  -- Layer 5.2 at this multidegree
  obtain ⟨P, hP0, hPhom, hPh, -, hPvan⟩ := haux d hdD₀
  set Dsum : ℝ := ∑ h, (d h : ℝ) with hDsumdef
  have hQlowpos : (0 : ℝ) < Qlow := lt_of_lt_of_le zero_lt_one hQlow1
  have hdle : ∀ h, (d h : ℝ) ≤ D / Qlow + 1 := by
    intro h
    have h1 : (d h : ℝ) < D / q h + 1 := Nat.ceil_lt_add_one (div_pos hD0 (hq0 h)).le
    have h2 : D / q h ≤ D / Qlow := div_le_div_of_nonneg_left hD0.le hQlowpos (hQlowh h)
    linarith
  have hDsum0 : 0 ≤ Dsum := Finset.sum_nonneg fun h _ ↦ Nat.cast_nonneg _
  have hDsumle : Dsum ≤ ((m : ℝ) + 1) * (D / Qlow + 1) := by
    calc Dsum ≤ ∑ _h : Fin (m + 1), (D / Qlow + 1) := Finset.sum_le_sum fun h _ ↦ hdle h
      _ = ((m : ℝ) + 1) * (D / Qlow + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hK10 : 0 ≤ K₁ := by
    rw [hK1def]
    have : (0 : ℝ) ≤ max C₂ 0 + 4 * tw := by positivity
    positivity
  have hScard0 : (0 : ℝ) < Scard := by
    rw [hScard]
    have : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
    have hc : 0 < Fintype.card (InfinitePlace K) + Sfin.card := by omega
    exact_mod_cast hc
  have hr0 : (0 : ℝ) ≤ D / Qlow := (div_pos hD0 hQlowpos).le
  have hQne : Qlow ≠ 0 := hQlowpos.ne'
  have hrrQ : D / Qlow * Qlow = D := by field_simp
  have hPle : P.logHeight ≤ max C₂ 0 * Dsum :=
    le_trans hPh (mul_le_mul_of_nonneg_right (le_max_left _ _) hDsum0)
  have hQbig : 8 * Scard * (K₁ + max C₅ 0) / ε ≤ Qlow :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hDbig : 8 * Scard * K₁ / ε ≤ D := le_trans (le_max_right _ _) hDD₁
  -- the height hypothesis of the generalized Roth lemma
  have hheight53 : ∀ h, (n : ℝ) * σ⁻¹ * (P.logHeight + 4 * ((m : ℝ) + 1) * (d 0 : ℝ) * tw)
      ≤ (d h : ℝ) * Height.logHeight (M h) := by
    intro h
    have hlow : ε * q h / (4 * Scard) - C₅ ≤ Height.logHeight (M h) := by
      rw [hMh h]; exact hhgt h
    have hlhs : (n : ℝ) * σ⁻¹ * (P.logHeight + 4 * ((m : ℝ) + 1) * (d 0 : ℝ) * tw)
        ≤ K₁ * (D / Qlow + 1) := by
      have hPle2 : P.logHeight ≤ max C₂ 0 * (((m : ℝ) + 1) * (D / Qlow + 1)) :=
        le_trans hPle (mul_le_mul_of_nonneg_left hDsumle (le_max_right _ _))
      have hd0 : 4 * ((m : ℝ) + 1) * (d 0 : ℝ) * tw
          ≤ 4 * ((m : ℝ) + 1) * (D / Qlow + 1) * tw :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hdle 0) (by positivity)) htw0
      have hmul := mul_le_mul_of_nonneg_left (add_le_add hPle2 hd0)
        (show (0 : ℝ) ≤ (n : ℝ) * σ⁻¹ by positivity)
      refine le_trans hmul (le_of_eq ?_)
      rw [hK1def]; ring
    exact le_mul_of_le_mul_div_add_one hε hScard0 hQlowpos hD0 (hq0 h) (hQlowh h)
      (Height.logHeight_nonneg _) (le_max_left C₅ 0) (le_max_right C₅ 0) hQbig hDbig hlow
      (Nat.le_ceil _) hlhs
  -- Layer 5.3: the index of `P` along the forms is small
  have hindex := MvPolynomial.formIndex_le_of_degree_ratio hn hcard hd1 hσ0 hσ1 hratio hP0 hPhom
    (fun h ↦ le_rfl) hM0 hheight53
  rw [hσrpow] at hindex
  have ht0 : (0 : ℝ) ≤ ((m : ℝ) + 1) * η / 2 := by positivity
  have hindex2 : MvPolynomial.formIndex (fun h ↦ (d h : ℝ)) M P
      ≤ ENNReal.ofReal (((m : ℝ) + 1) * η / 2) := by
    refine le_trans hindex (le_of_eq ?_)
    congr 1
    ring
  -- the bridge: a derivative of small order surviving on `V(Q 0) × ⋯ × V(Q m)`
  have hyspan : ∀ (h : Fin (m + 1)) (x : ι → K), ∑ i, M h i * x i = 0 →
      x ∈ Submodule.span K (Set.range (yb h)) := by
    intro h x hx
    rw [hyb_span h, hMV h]
    exact hx
  obtain ⟨I, hIsum, hIne⟩ :=
    MvPolynomial.exists_linSubst_hasseDeriv_ne_zero_of_formIndex_le
      (fun h ↦ (Nat.cast_nonneg (d h) : (0 : ℝ) ≤ (d h : ℝ))) hM0 hyspan hP0 ht0 hindex2
  -- Layer 5.5: a small point at which a further derivative does not vanish
  have hI2 : ∑ h, (∑ i, (I (h, i) : ℝ)) / (d h : ℝ)
      ≤ (Fintype.card (Fin (m + 1)) : ℝ) * η / 2 := by
    rw [Fintype.card_fin]
    push_cast
    linarith only [hIsum]
  obtain ⟨z, hz, I', -, hI'sum, hne'⟩ :=
    MvPolynomial.exists_eval_hasseDeriv_ne_zero_of_sum_div_le hPhom yb hη0 I hI2 hIne
  have hzB : ∀ h l, (z h l).natAbs ≤ B := by
    intro h l
    have h1 : ((z h l).natAbs : ℝ) ≤ 2 * (Fintype.card (Fin n) : ℝ) / η + 1 := hz h l
    rw [Fintype.card_fin] at h1
    have h2 : 2 * (n : ℝ) / η + 1 ≤ (B : ℝ) := by rw [hBdef]; exact Nat.le_ceil _
    exact_mod_cast le_trans h1 h2
  -- the vanishing pattern of Layer 5.2, read as a two-sided bound
  have hpat : ∀ (a : InfinitePlace K ⊕ ↥Sfin) (J : Fin (m + 1) × ι →₀ ℕ),
      (blockSubst (formMatrix L (sPlace Sfin a))⁻¹ (hasseDeriv I' P)).coeff J ≠ 0 →
      ∀ j, |(∑ h, (J (h, j) : ℝ) / (d h : ℝ)) - ((m : ℝ) + 1) / ((n : ℝ) + 1)|
        ≤ 2 * (n : ℝ) * ((m : ℝ) + 1) * η := by
    intro a J hJ j
    by_contra hc
    refine hJ (hPvan a I' J hI'sum ⟨j, ?_⟩)
    have hc' : 2 * (n : ℝ) * ((m : ℝ) + 1) * η
        < |(∑ h, (J (h, j) : ℝ) / (d h : ℝ)) - ((m : ℝ) + 1) / ((n : ℝ) + 1)| := not_le.mp hc
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hgap : 2 * ((m : ℝ) + 1) * η ≤ 2 * (n : ℝ) * ((m : ℝ) + 1) * η := by
      have h3 : (0 : ℝ) ≤ 2 * ((m : ℝ) + 1) * η * ((n : ℝ) - 1) :=
        mul_nonneg (by positivity) (by linarith)
      linarith only [h3]
    rw [Fintype.card_fin]
    push_cast
    rcases abs_cases ((∑ h, (J (h, j) : ℝ) / (d h : ℝ)) - ((m : ℝ) + 1) / ((n : ℝ) + 1)) with
      ⟨he, -⟩ | ⟨he, -⟩
    · rw [he] at hc'
      exact Or.inr (by linarith only [hc'])
    · rw [he] at hc'
      exact Or.inl (by linarith only [hc', hgap])
  -- Step VI: the product formula against the local bounds
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hkey := subspace_key_inequality hLinf hLfin hQ1 hyb_mem hzB hdpos hD0.le hdq hdq'
    hP0 hPhom hne' hpat
  have hcastDsum : ((∑ h, d h : ℕ) : ℝ) = Dsum := by rw [hDsumdef]; push_cast; ring
  have hQsumeq : Qsum = ∑ h, Real.log (Q h) := rfl
  rw [hcastDsum, log_box_eq hn hcard (Fintype.card_fin n) d, ← hDsumdef, ← hAWdef, ← htwdef,
    ← hHβdef, ← hQsumeq] at hkey
  -- the final comparison
  have hLsle : ∑ h, Real.log ((d h : ℝ) + 1) ≤ ((m : ℝ) + 1) * Real.log (D + 2) := by
    have hterm : ∀ h : Fin (m + 1), Real.log ((d h : ℝ) + 1) ≤ Real.log (D + 2) := by
      intro h
      refine Real.log_le_log (by positivity) ?_
      have h1 := hdle h
      have h2 : D / Qlow ≤ D := div_le_self hD0.le hQlow1
      linarith
    calc ∑ h, Real.log ((d h : ℝ) + 1) ≤ ∑ _h : Fin (m + 1), Real.log (D + 2) :=
          Finset.sum_le_sum fun h _ ↦ hterm h
      _ = ((m : ℝ) + 1) * Real.log (D + 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hmix : ((m : ℝ) + 1) / ((n : ℝ) + 1) * approxWeight Sfin cf
      + 2 * (n : ℝ) * ((m : ℝ) + 1) * η * AW
      ≤ -(((m : ℝ) + 1) * ε / (4 * ((n : ℝ) + 1))) := by
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hne1 : ((n : ℝ) + 1) ≠ 0 := hn1.ne'
    have h1 : ((m : ℝ) + 1) / ((n : ℝ) + 1) * approxWeight Sfin cf
        ≤ ((m : ℝ) + 1) / ((n : ℝ) + 1) * (-ε / 2) :=
      mul_le_mul_of_nonneg_left hweight (by positivity)
    have h2 : ((m : ℝ) + 1) * (2 * (n : ℝ) * η * AW)
        ≤ ((m : ℝ) + 1) * (ε / (4 * ((n : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hηW (by positivity)
    have h3 : ((m : ℝ) + 1) / ((n : ℝ) + 1) * (-ε / 2)
        = -(2 * (((m : ℝ) + 1) * ε / (4 * ((n : ℝ) + 1)))) := by field_simp; ring
    have h4 : ((m : ℝ) + 1) * (ε / (4 * ((n : ℝ) + 1)))
        = ((m : ℝ) + 1) * ε / (4 * ((n : ℝ) + 1)) := by ring
    linarith only [h1, h2, h3, h4]
  exact not_of_key_inequality (tw := tw) (n₁ := (n : ℝ) + 1) (m₁ := (m : ℝ) + 1) (Ca := Ca)
    (Cb := Cb) (C₂ := max C₂ 0) (Hb := Hβ)
    (bl := Real.log (2 * ((n : ℝ) + 1) * (n : ℝ)))
    (Ls := ∑ h, Real.log ((d h : ℝ) + 1)) (Dsum := Dsum) (D := D) (Qlow := Qlow)
    (rr := D / Qlow) (lg := Real.log (D + 2)) (ε := ε) (Qsum := Qsum) (AW := AW)
    (mixed := ((m : ℝ) + 1) / ((n : ℝ) + 1) * approxWeight Sfin cf
      + 2 * (n : ℝ) * ((m : ℝ) + 1) * η * AW)
    (Ph := P.logHeight)
    htw0 (by positivity) (by positivity) (le_max_right _ _) hDsum0 hD0 hε hr0 hrrQ hCadef
    (le_max_left _ _) hLsle hDsumle hPle (le_trans (le_max_left _ _) (le_max_right _ _)) hmix
    (by linarith only [hkey]) hDlog


omit [DecidableEq ι] in
/-- **Beyond a level, the span of the approximation domain is one of finitely many subspaces**:
Bombieri--Gubler's Theorem 7.5.13 for levels bounded below. -/
theorem exists_forall_approxSpan_mem {n : ℕ} (hn : 1 ≤ n) (hcard : Fintype.card ι = n + 1)
    {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    {cf : AbsoluteValue K ℝ → ι → ℝ}
    (hLinf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLfin : ∀ w ∈ Sfin, LinearIndependent K (L w.1))
    {ε : ℝ} (hε : 0 < ε) (hweight : approxWeight Sfin cf ≤ -ε / 2) :
    ∃ 𝒲 : Set (Submodule K (ι → K)), 𝒲.Finite ∧ ∃ Q₀ : ℝ, ∀ Q : ℝ, 1 < Q → Q₀ ≤ Real.log Q →
      Module.finrank K (approxSpan Sfin L cf Q) = n → approxSpan Sfin L cf Q ∈ 𝒲 := by
  classical
  have hlk : 1 + n = Fintype.card ι := by rw [hcard]; ring
  obtain ⟨𝒲, C₄, C₅, C₆, h𝒲fin, hdich⟩ :=
    exists_finite_forall_logHeight_approxSpan hlk hLinf hLfin hε hweight
  obtain ⟨m, σ, Qlow, hσ0, hchain⟩ := exists_forall_not_chain hn hcard hLinf hLfin hε hweight C₅
  refine ⟨𝒲, h𝒲fin, ?_⟩
  by_contra hcon
  push Not at hcon
  choose f hf1 hf2 hf3 hf4 using hcon
  set Qb : ℝ := max Qlow (C₄ / ε) with hQbdef
  obtain ⟨a, ha0, hasucc⟩ : ∃ a : ℕ → ℝ, a 0 = f Qb ∧
      ∀ k, a (k + 1) = f (max Qb (2 * σ⁻¹ * Real.log (a k))) :=
    ⟨fun k ↦ Nat.rec (f Qb) (fun _ prev ↦ f (max Qb (2 * σ⁻¹ * Real.log prev))) k, rfl,
      fun _ ↦ rfl⟩
  have haf : ∀ k, ∃ t : ℝ, a k = f t ∧ Qb ≤ t := by
    intro k
    cases k with
    | zero => exact ⟨Qb, ha0, le_rfl⟩
    | succ k => exact ⟨max Qb (2 * σ⁻¹ * Real.log (a k)), hasucc k, le_max_left _ _⟩
  have ha1 : ∀ k, 1 < a k := by
    intro k
    obtain ⟨t, ht, -⟩ := haf k
    rw [ht]
    exact hf1 t
  have haQb : ∀ k, Qb ≤ Real.log (a k) := by
    intro k
    obtain ⟨t, ht, hQt⟩ := haf k
    rw [ht]
    exact le_trans hQt (hf2 t)
  have harank : ∀ k, Module.finrank K (approxSpan Sfin L cf (a k)) = n := by
    intro k
    obtain ⟨t, ht, -⟩ := haf k
    rw [ht]
    exact hf3 t
  have hanot : ∀ k, approxSpan Sfin L cf (a k) ∉ 𝒲 := by
    intro k
    obtain ⟨t, ht, -⟩ := haf k
    rw [ht]
    exact hf4 t
  have hagrow : ∀ k, 2 * σ⁻¹ * Real.log (a k) ≤ Real.log (a (k + 1)) := by
    intro k
    rw [hasucc k]
    exact le_trans (le_max_right _ _) (hf2 _)
  refine hchain (fun h ↦ a h.val) (fun h ↦ ha1 _)
    (fun h ↦ le_trans (le_max_left _ _) (haQb _)) (fun h ↦ ?_) (fun h ↦ harank _) (fun h ↦ ?_)
  · rw [Fin.val_castSucc, Fin.val_succ]
    exact hagrow h.val
  · rcases hdich (a h.val) (le_of_lt (ha1 _))
      (le_trans (le_max_right _ _) (haQb _)) (harank _) with hw | ⟨hl, -⟩
    · exact absurd hw (hanot _)
    · exact hl

omit [DecidableEq ι] in
/-- **The penultimate-minimum theorem** (Bombieri--Gubler, Theorem 7.5.13): for forms
independent at every place of `S` and exponents of negative weight, the spans of the
approximation domains of rank `n` form a finite set of subspaces. -/
theorem finite_setOf_approxSpan {n : ℕ} (hn : 1 ≤ n) (hcard : Fintype.card ι = n + 1)
    {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    {cf : AbsoluteValue K ℝ → ι → ℝ}
    (hLinf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLfin : ∀ w ∈ Sfin, LinearIndependent K (L w.1))
    {ε : ℝ} (hε : 0 < ε) (hweight : approxWeight Sfin cf ≤ -ε / 2) :
    {V : Submodule K (ι → K) | ∃ Q : ℝ, 1 ≤ Q ∧
      Module.finrank K (approxSpan Sfin L cf Q) = n ∧ V = approxSpan Sfin L cf Q}.Finite := by
  classical
  obtain ⟨𝒲, h𝒲fin, Q₀, hmem⟩ := exists_forall_approxSpan_mem hn hcard hLinf hLfin hε hweight
  obtain ⟨C₆, hC₆⟩ := logHeight_approxSpan_le (cf := cf) (n := n) hLinf hLfin
  set W' : ℝ := (n : ℝ) * (∑ w : InfinitePlace K, (w.mult : ℝ) * cMax cf w.1
    + ∑ w ∈ Sfin, cMax cf w.1) with hW'def
  refine Set.Finite.subset
    (h𝒲fin.union (Submodule.finite_setOf_logHeight_le (|W'| * max Q₀ 1 + C₆))) ?_
  rintro V ⟨Q, hQ1, hrank, rfl⟩
  rcases le_or_gt (max Q₀ 1) (Real.log Q) with hbig | hsmall
  · refine Or.inl (hmem Q ?_ (le_trans (le_max_left _ _) hbig) hrank)
    rcases eq_or_lt_of_le hQ1 with he | hlt
    · exfalso
      rw [← he, Real.log_one] at hbig
      have h1 : (1 : ℝ) ≤ max Q₀ 1 := le_max_right _ _
      linarith
    · exact hlt
  · refine Or.inr ?_
    have hlog0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
    have h1 := hC₆ Q hQ1 hrank
    have h2 : W' * Real.log Q ≤ |W'| * Real.log Q :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hlog0
    have h3 : |W'| * Real.log Q ≤ |W'| * max Q₀ 1 :=
      mul_le_mul_of_nonneg_left hsmall.le (abs_nonneg _)
    exact le_trans h1 (by linarith)

end NumberField

end

end
