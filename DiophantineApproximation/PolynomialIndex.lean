/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.MvHasseDerivTaylor
public import DiophantineApproximation.WeightedOrder
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Basic.ENNReal.Real

-- Used only by the acceptance criteria.
import Mathlib.Data.ZMod.Basic

/-!
# The index of a polynomial at a point

Fix weights `d j` on the variables. The **index** of `P` at `α` is the least weighted order
`∑ j, μ j / d j` of a Hasse derivative `∂_μ P` that does not vanish at `α`, and `⊤` when there is
none, which happens only for `P = 0`. It measures how strongly `P` vanishes at `α`, counting a
derivative in the variable `j` as `1 / d j` of a vanishing; in Roth's theorem the `d j` are the
degrees of `P` in each variable, so that the index lies between `0` and the number of variables.

The file is short because the index is not a new construction. Translating `P` so that `α`
becomes the origin turns the Hasse derivatives at `α` into the coefficients at `0`:
`coeff μ (P (X + α)) = (∂_μ P)(α)`, which is the Taylor expansion of Layer 2.1 read as a
statement about one polynomial rather than two. So the index is the **weighted order of the
translate**, and every property the roadmap asks for is a property of the weighted order —
proved once, in `DiophantineApproximation/WeightedOrder.lean`, for a polynomial in any variables
over any commutative semiring.

## Main results

* `MvPolynomial.taylorAt` and `MvPolynomial.coeff_taylorAt`: the translation `P ↦ P (X + α)`,
  whose coefficients are the Hasse derivatives of `P` at `α`. It is the several-variable form of
  `Polynomial.taylor`, which Mathlib has only in one variable.
* `MvPolynomial.index`: **the index** (Bombieri–Gubler 6.3.2), and
  `MvPolynomial.index_eq_weightedOrder`, the identity the rest of the file runs on.
* `MvPolynomial.index_eq_top_iff`: `⊤` exactly at `P = 0`.
* `MvPolynomial.le_index_add` and `MvPolynomial.index_mul`: **the index is a valuation**, the
  second over a domain, in any characteristic.
* `MvPolynomial.index_le_hasseDeriv_add`: differentiating `μ` times costs at most the weight of
  `μ`, which is the form Roth's lemma uses.
* `MvPolynomial.index_map`, `MvPolynomial.index_taylorAt` and
  `MvPolynomial.index_const_mul_weights`: invariance under an injective ring homomorphism, under
  translation of the point to the origin, and homogeneity in the weights.
* `MvPolynomial.index_of_unique`: in one variable with weight `1` the index is
  `Polynomial.rootMultiplicity`, which is the test that the definition means what it should.

## Implementation notes

⚠ **Hasse derivatives, not `pderiv` — and this is where Layer 2.1 pays.** In characteristic `p`
the ordinary partial derivative of `X^p` is zero, so a `pderiv`-based index would report `⊤` for
polynomials that do not vanish identically, and the valuation properties would be false. The
rejection test below is `X ^ 2` over `ZMod 2`: its index at the origin is `2`, while its `pderiv`
is `0`.

⚠ **The whole milestone is one identity about coefficients.** `coeff_taylorAt` says that the
index is the weighted order of the translate; `index_eq_weightedOrder` says it in the form the
proofs use; everything else in this file is three lines of rewriting. In particular
multiplicativity is *not* proved here — it is `MvPolynomial.weightedOrder_mul`, a statement about
supports with no derivative and no point in it.

⚠ **`0 ≤ d j` is enough; strict positivity is never used.** Bombieri–Gubler ask for `d j > 0`,
and the theorems below ask only that the weights be nonnegative, which is what turns
`ENNReal.ofReal (∑ j, μ j / d j)` into a sum of weights. The reason to keep reading `d j > 0`
anyway is that Lean's `k / 0 = 0` makes a variable of weight `0` *invisible* to the index rather
than making the index infinite, which is the opposite of the intended degenerate behaviour: with
`d j = 0` the index of `X j` is `0`, not `⊤`. The generalisation is therefore harmless and the
reading is not.

⚠ **The nonvanishing hypothesis of `index_of_unique` is Mathlib's junk value, not ours.**
`index d α 0 = ⊤` is the correct value of a valuation at `0`, while
`Polynomial.rootMultiplicity a 0 = 0`; the two agree exactly when `P ≠ 0`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Definition 6.3.2 and the valuation properties collected after it.

This is Layer 2.3 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace MvPolynomial

variable {σ R : Type*} [CommRing R]

/-! ### Translation to the origin -/

/-- **Translation**: `taylorAt α P` is `P (X + α)`, the several-variable `Polynomial.taylor`. -/
def taylorAt (α : σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun j ↦ X j + C (α j)

@[simp]
theorem taylorAt_X (α : σ → R) (j : σ) : taylorAt α (X j) = X j + C (α j) :=
  aeval_X _ _

theorem taylorAt_C (α : σ → R) (a : R) : taylorAt α (C a) = C a :=
  aeval_C _ _

/-- Translating twice translates by the sum. -/
theorem taylorAt_comp (α β : σ → R) : (taylorAt α).comp (taylorAt β) = taylorAt (α + β) := by
  refine MvPolynomial.algHom_ext fun j ↦ ?_
  rw [AlgHom.comp_apply, taylorAt_X, map_add, taylorAt_X, taylorAt_C, taylorAt_X, add_assoc,
    ← C_add]
  rfl

theorem taylorAt_taylorAt (α β : σ → R) (P : MvPolynomial σ R) :
    taylorAt α (taylorAt β P) = taylorAt (α + β) P :=
  AlgHom.congr_fun (taylorAt_comp α β) P

@[simp]
theorem taylorAt_zero (P : MvPolynomial σ R) : taylorAt (0 : σ → R) P = P := by
  have h : taylorAt (0 : σ → R) = AlgHom.id R (MvPolynomial σ R) :=
    MvPolynomial.algHom_ext fun j ↦ by simp
  rw [h, AlgHom.id_apply]

/-- Translation is injective, being invertible: `⊤` below is a value of the index and not a
failure of one. -/
theorem taylorAt_eq_zero_iff {α : σ → R} {P : MvPolynomial σ R} :
    taylorAt α P = 0 ↔ P = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  have h2 := congrArg (taylorAt (-α)) h
  rwa [map_zero, taylorAt_taylorAt, neg_add_cancel, taylorAt_zero] at h2

/-- The substitution formula of Layer 2.1, with the first family of variables specialised to the
point `α`. -/
theorem map_eval_aeval (α : σ → R) (P : MvPolynomial σ R) :
    map (eval α) (aeval (fun j ↦ C (X j) + X j) P : MvPolynomial σ (MvPolynomial σ R))
      = taylorAt α P := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [aeval_C, show algebraMap R (MvPolynomial σ (MvPolynomial σ R)) a = C (C a) from rfl,
        map_C, eval_C, taylorAt_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p j hp =>
      simp only [map_mul, aeval_X, taylorAt_X, map_add, map_C, eval_X, map_X, hp]
      ring

/-- **The coefficients of the translate are the Hasse derivatives at the point.** This one
identity is the whole of Layer 2.3. -/
theorem coeff_taylorAt (α : σ → R) (P : MvPolynomial σ R) (μ : σ →₀ ℕ) :
    (taylorAt α P).coeff μ = eval α (hasseDeriv μ P) := by
  rw [← map_eval_aeval, coeff_map, coeff_taylor]

/-- Translation commutes with a change of coefficient ring. -/
theorem map_taylorAt {S : Type*} [CommRing S] (f : R →+* S) (α : σ → R) (P : MvPolynomial σ R) :
    map f (taylorAt α P) = taylorAt (fun j ↦ f (α j)) (map f P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [taylorAt_C, map_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, taylorAt_X, map_add, map_X, map_C, hp]

/-! ### The index -/

variable (d : σ → ℝ)

/-- **Layer 2.3. The index of `P` at `α` with respect to the weights `d`** (Bombieri–Gubler,
Definition 6.3.2): the least weighted order `∑ j, μ j / d j` of a Hasse derivative that does not
vanish at `α`. It is `⊤` exactly at `P = 0`, which is its value as a valuation and not a junk
value. -/
def index (d : σ → ℝ) (α : σ → R) (P : MvPolynomial σ R) : ℝ≥0∞ :=
  ⨅ (μ : σ →₀ ℕ) (_ : eval α (hasseDeriv μ P) ≠ 0), ENNReal.ofReal (μ.sum fun j k ↦ k / d j)

/-- A Hasse derivative that survives at `α` bounds the index from above. -/
theorem index_le {α : σ → R} {P : MvPolynomial σ R} {μ : σ →₀ ℕ}
    (h : eval α (hasseDeriv μ P) ≠ 0) :
    index d α P ≤ ENNReal.ofReal (μ.sum fun j k ↦ k / d j) :=
  iInf_le_of_le μ (iInf_le _ h)

/-- The index is the greatest lower bound: to bound it from below, bound every surviving Hasse
derivative. -/
theorem le_index {α : σ → R} {P : MvPolynomial σ R} {c : ℝ≥0∞}
    (h : ∀ μ : σ →₀ ℕ, eval α (hasseDeriv μ P) ≠ 0 →
      c ≤ ENNReal.ofReal (μ.sum fun j k ↦ k / d j)) : c ≤ index d α P :=
  le_iInf fun μ ↦ le_iInf fun hμ ↦ h μ hμ

@[simp]
theorem index_zero (α : σ → R) : index d α (0 : MvPolynomial σ R) = ⊤ := by
  simp [index]

end MvPolynomial

namespace Finsupp

/-- The weight attached to `d` is the sum the index is defined by. Nonnegative weights are what
lets the single `ENNReal.ofReal` of the definition be distributed over the sum. -/
theorem weight_ofReal_inv {σ : Type*} (d : σ → ℝ) (hd : ∀ j, 0 ≤ d j) (μ : σ →₀ ℕ) :
    Finsupp.weight (fun j ↦ ENNReal.ofReal (d j)⁻¹) μ
      = ENNReal.ofReal (μ.sum fun j k ↦ k / d j) := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.sum,
    ENNReal.ofReal_sum_of_nonneg fun j _ ↦ div_nonneg (Nat.cast_nonneg _) (hd j)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    div_eq_mul_inv]

end Finsupp

namespace MvPolynomial

variable {σ R : Type*} [CommRing R] (d : σ → ℝ)

/-- **The index is the weighted order of the translate.** Everything below is this identity and
a theorem of `DiophantineApproximation/WeightedOrder.lean`. -/
theorem index_eq_weightedOrder (hd : ∀ j, 0 ≤ d j) (α : σ → R) (P : MvPolynomial σ R) :
    index d α P = weightedOrder (fun j ↦ ENNReal.ofReal (d j)⁻¹) (taylorAt α P) := by
  refine le_antisymm (le_weightedOrder fun μ hμ ↦ ?_) (le_index d fun μ hμ ↦ ?_)
  · rw [Finsupp.weight_ofReal_inv d hd]
    exact index_le d (by rwa [coeff_taylorAt] at hμ)
  · rw [← Finsupp.weight_ofReal_inv d hd]
    exact weightedOrder_le_of_coeff_ne_zero (by rwa [coeff_taylorAt])

/-- **The index is `⊤` exactly at the zero polynomial.** -/
theorem index_eq_top_iff (hd : ∀ j, 0 ≤ d j) (α : σ → R) (P : MvPolynomial σ R) :
    index d α P = ⊤ ↔ P = 0 := by
  rw [index_eq_weightedOrder d hd, weightedOrder_eq_top_iff fun _ ↦ ENNReal.ofReal_ne_top,
    taylorAt_eq_zero_iff]

/-- **The ultrametric inequality.** -/
theorem le_index_add (hd : ∀ j, 0 ≤ d j) (α : σ → R) (P Q : MvPolynomial σ R) :
    min (index d α P) (index d α Q) ≤ index d α (P + Q) := by
  rw [index_eq_weightedOrder d hd, index_eq_weightedOrder d hd, index_eq_weightedOrder d hd,
    map_add]
  exact le_weightedOrder_add _ _ _

/-- **The index is a valuation on a domain** — in any characteristic, because the derivatives are
Hasse derivatives, and under `NoZeroDivisors` alone, which is one hypothesis less than a domain:
nothing here needs `R` to be nontrivial. -/
theorem index_mul [NoZeroDivisors R] (hd : ∀ j, 0 ≤ d j) (α : σ → R) (P Q : MvPolynomial σ R) :
    index d α (P * Q) = index d α P + index d α Q := by
  rw [index_eq_weightedOrder d hd, index_eq_weightedOrder d hd, index_eq_weightedOrder d hd,
    map_mul, weightedOrder_mul fun _ ↦ ENNReal.ofReal_ne_top]

/-- The index of a power. -/
theorem index_pow [NoZeroDivisors R] [Nontrivial R] (hd : ∀ j, 0 ≤ d j) (α : σ → R)
    (P : MvPolynomial σ R) (k : ℕ) :
    index d α (P ^ k) = k * index d α P := by
  rw [index_eq_weightedOrder d hd, index_eq_weightedOrder d hd, map_pow,
    weightedOrder_pow (fun _ ↦ ENNReal.ofReal_ne_top)]

/-- **Differentiating costs at most the weight of the order.** This is the estimate Roth's lemma
uses, in the form that avoids truncated subtraction in `ℝ≥0∞`. -/
theorem index_le_hasseDeriv_add (hd : ∀ j, 0 ≤ d j) (α : σ → R) (P : MvPolynomial σ R)
    (μ : σ →₀ ℕ) :
    index d α P
      ≤ index d α (hasseDeriv μ P) + ENNReal.ofReal (μ.sum fun j k ↦ k / d j) := by
  rw [index_eq_weightedOrder d hd, index_eq_weightedOrder d hd, ← Finsupp.weight_ofReal_inv d hd]
  refine le_weightedOrder_add_const fun ν hν ↦ ?_
  rw [coeff_taylorAt, hasseDeriv_comp, map_nsmul] at hν
  have hne : eval α (hasseDeriv (ν + μ) P) ≠ 0 := fun h ↦ hν (by rw [h, smul_zero])
  calc weightedOrder (fun j ↦ ENNReal.ofReal (d j)⁻¹) (taylorAt α P)
      ≤ Finsupp.weight (fun j ↦ ENNReal.ofReal (d j)⁻¹) (ν + μ) :=
        weightedOrder_le_of_coeff_ne_zero (by rw [coeff_taylorAt]; exact hne)
    _ = _ := map_add _ _ _

/-- **Invariance under an injective change of coefficient ring.** -/
theorem index_map {S : Type*} [CommRing S] {f : R →+* S} (hf : Function.Injective f)
    (hd : ∀ j, 0 ≤ d j) (α : σ → R) (P : MvPolynomial σ R) :
    index d (fun j ↦ f (α j)) (map f P) = index d α P := by
  rw [index_eq_weightedOrder d hd, index_eq_weightedOrder d hd, ← map_taylorAt,
    weightedOrder_map hf]

/-- **Invariance under translation of the point to the origin.** -/
theorem index_taylorAt (hd : ∀ j, 0 ≤ d j) (α : σ → R) (P : MvPolynomial σ R) :
    index d 0 (taylorAt α P) = index d α P := by
  rw [index_eq_weightedOrder d hd, index_eq_weightedOrder d hd, taylorAt_zero]

/-- **Homogeneity in the weights**: scaling every `d j` scales the index inversely. -/
theorem index_const_mul_weights {c : ℝ} (hc : 0 < c) (hd : ∀ j, 0 ≤ d j) (α : σ → R)
    (P : MvPolynomial σ R) :
    index (fun j ↦ c * d j) α P = ENNReal.ofReal c⁻¹ * index d α P := by
  have hcd : ∀ j, 0 ≤ c * d j := fun j ↦ mul_nonneg hc.le (hd j)
  have hw : (fun j ↦ ENNReal.ofReal (c * d j)⁻¹)
      = fun j ↦ ENNReal.ofReal c⁻¹ * ENNReal.ofReal (d j)⁻¹ := by
    funext j
    rw [mul_inv, ENNReal.ofReal_mul (by positivity)]
  rw [index_eq_weightedOrder _ hcd, index_eq_weightedOrder d hd, hw,
    weightedOrder_const_mul (ENNReal.ofReal_pos.mpr (inv_pos.mpr hc)).ne' _ _]

/-! ### One variable: the index is the multiplicity of the root -/

/-- Evaluation of a polynomial in one variable, read through `MvPolynomial.uniqueAlgEquiv`. -/
theorem eval_eq_polynomial_eval [Unique σ] (a : R) (P : MvPolynomial σ R) :
    eval (fun _ ↦ a) P = Polynomial.eval a (uniqueAlgEquiv R σ P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp => simp [hp]

/-- **In one variable with weight `1` the index is the multiplicity of the root.** The
nonvanishing hypothesis is forced by `Polynomial.rootMultiplicity a 0 = 0`, where the index is
`⊤`. -/
theorem index_of_unique [Unique σ] (a : R) {P : MvPolynomial σ R} (hP : P ≠ 0) :
    index (fun _ ↦ 1) (fun _ ↦ a) P
      = ((uniqueAlgEquiv R σ P).rootMultiplicity a : ℝ≥0∞) := by
  set p : Polynomial R := uniqueAlgEquiv R σ P with hpdef
  have hp0 : p ≠ 0 := fun h ↦ hP ((uniqueAlgEquiv R σ).injective (by rw [← hpdef, h, map_zero]))
  have htp : Polynomial.taylor a p ≠ 0 := fun h ↦ hp0 (Polynomial.taylor_injective a
    (by rw [h, map_zero]))
  set m : ℕ := (Polynomial.taylor a p).natTrailingDegree with hmdef
  have hroot : p.rootMultiplicity a = m := by
    rw [hmdef, Polynomial.taylor_apply, Polynomial.rootMultiplicity_eq_natTrailingDegree]
  have hkey : ∀ k : ℕ, eval (fun _ ↦ a) (hasseDeriv (Finsupp.single default k) P)
      = (Polynomial.taylor a p).coeff k := by
    intro k
    rw [eval_eq_polynomial_eval, uniqueAlgEquiv_hasseDeriv, Polynomial.taylor_coeff, ← hpdef]
  have hweight : ∀ k : ℕ,
      ((Finsupp.single (default : σ) k).sum fun _ e ↦ (e : ℝ) / 1) = (k : ℝ) := by
    intro k
    rw [Finsupp.sum_single_index (by norm_num), div_one]
  rw [hroot]
  refine le_antisymm ?_ (le_index _ fun μ hμ ↦ ?_)
  · have hne : eval (fun _ ↦ a) (hasseDeriv (Finsupp.single (default : σ) m) P) ≠ 0 := by
      rw [hkey m, hmdef]
      exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr htp
    have := index_le (fun _ ↦ (1 : ℝ)) hne
    rwa [hweight m, ENNReal.ofReal_natCast] at this
  · obtain ⟨k, rfl⟩ : ∃ k, μ = Finsupp.single (default : σ) k :=
      ⟨μ default, Finsupp.unique_single μ⟩
    rw [hweight k, ENNReal.ofReal_natCast, Nat.cast_le]
    rw [hkey k] at hμ
    exact Polynomial.natTrailingDegree_le_of_ne_zero hμ

/-! ### Acceptance criteria -/

/-- **Acceptance test (the roadmap's): the index sees the weights.** A polynomial vanishing on
the diagonal has small index when the weights are unbalanced — which is why Roth's lemma needs
`d (j + 1) / d j ≤ σ`. -/
example {d : Fin 2 → ℝ} (hd : ∀ j, 0 < d j) (a : ℚ) (k : ℕ) :
    index d (fun _ ↦ a) ((X 0 - X 1 : MvPolynomial (Fin 2) ℚ) ^ k)
      = ENNReal.ofReal (k / max (d 0) (d 1)) := by
  classical
  have hd0 : ∀ j, 0 ≤ d j := fun j ↦ (hd j).le
  have hX : taylorAt (fun _ ↦ a) (X 0 - X 1 : MvPolynomial (Fin 2) ℚ) = X 0 - X 1 := by
    rw [map_sub, taylorAt_X, taylorAt_X]
    ring
  have hne : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := fun h ↦ by
    simpa using congrArg (fun f ↦ f 0) h
  have hc : ∀ μ : Fin 2 →₀ ℕ, (X 0 - X 1 : MvPolynomial (Fin 2) ℚ).coeff μ
      = (if Finsupp.single 0 1 = μ then (1 : ℚ) else 0)
        - if Finsupp.single 1 1 = μ then (1 : ℚ) else 0 := fun μ ↦ by
    rw [show (X 0 - X 1 : MvPolynomial (Fin 2) ℚ).coeff μ
        = (X 0 : MvPolynomial (Fin 2) ℚ).coeff μ - (X 1 : MvPolynomial (Fin 2) ℚ).coeff μ from
      by simp, coeff_X, coeff_X]
  have hbase : index d (fun _ ↦ a) (X 0 - X 1 : MvPolynomial (Fin 2) ℚ)
      = ENNReal.ofReal (max (d 0) (d 1))⁻¹ := by
    have hmin : ENNReal.ofReal (max (d 0) (d 1))⁻¹
        = min (ENNReal.ofReal (d 0)⁻¹) (ENNReal.ofReal (d 1)⁻¹) := by
      rcases le_total (d 0) (d 1) with h | h
      · rw [max_eq_right h, min_eq_right (ENNReal.ofReal_le_ofReal (inv_anti₀ (hd 0) h))]
      · rw [max_eq_left h, min_eq_left (ENNReal.ofReal_le_ofReal (inv_anti₀ (hd 1) h))]
    rw [index_eq_weightedOrder d hd0, hX, hmin]
    refine le_antisymm (le_min ?_ ?_) (le_weightedOrder fun μ hμ ↦ ?_)
    · have h := weightedOrder_le_of_coeff_ne_zero
        (w := fun j ↦ ENNReal.ofReal (d j)⁻¹) (P := (X 0 - X 1 : MvPolynomial (Fin 2) ℚ))
        (μ := Finsupp.single 0 1) (by rw [hc]; simp [hne.symm])
      rwa [Finsupp.weight_single, one_smul] at h
    · have h := weightedOrder_le_of_coeff_ne_zero
        (w := fun j ↦ ENNReal.ofReal (d j)⁻¹) (P := (X 0 - X 1 : MvPolynomial (Fin 2) ℚ))
        (μ := Finsupp.single 1 1) (by rw [hc]; simp [hne])
      rwa [Finsupp.weight_single, one_smul] at h
    · by_cases h0 : Finsupp.single (0 : Fin 2) 1 = μ
      · rw [← h0, Finsupp.weight_single, one_smul]
        exact min_le_left _ _
      by_cases h1 : Finsupp.single (1 : Fin 2) 1 = μ
      · rw [← h1, Finsupp.weight_single, one_smul]
        exact min_le_right _ _
      · exact absurd (by rw [hc]; simp [h0, h1]) hμ
  rw [index_pow d hd0, hbase, ← ENNReal.ofReal_natCast k,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), div_eq_mul_inv]

/-- **Acceptance test: the index is a valuation.** -/
example [IsDomain R] (hd : ∀ j, 0 ≤ d j) (α : σ → R) (P Q : MvPolynomial σ R) :
    index d α (P * Q) = index d α P + index d α Q ∧
      min (index d α P) (index d α Q) ≤ index d α (P + Q) ∧
      (index d α P = ⊤ ↔ P = 0) :=
  ⟨index_mul d hd α P Q, le_index_add d hd α P Q, index_eq_top_iff d hd α P⟩

/-- **Acceptance test: one variable, weight one.** -/
example [Unique σ] (a : R) {P : MvPolynomial σ R} (hP : P ≠ 0) :
    index (fun _ ↦ 1) (fun _ ↦ a) P = ((uniqueAlgEquiv R σ P).rootMultiplicity a : ℝ≥0∞) :=
  index_of_unique a hP

/-- **Rejection test: Hasse derivatives, not `pderiv`.** Over `ZMod 2` the square of a variable
has index `2` at the origin, while its ordinary partial derivative is the zero polynomial — a
`pderiv`-based index would call it `⊤`, and the valuation properties above would be false. -/
example : index (fun _ ↦ (1 : ℝ)) (0 : Unit → ZMod 2) (X () ^ 2 : MvPolynomial Unit (ZMod 2))
      = 2 ∧ pderiv () (X () ^ 2 : MvPolynomial Unit (ZMod 2)) = 0 := by
  constructor
  · rw [index_eq_weightedOrder _ (fun _ ↦ zero_le_one), taylorAt_zero, X_pow_eq_monomial,
      weightedOrder_monomial (one_ne_zero (α := ZMod 2)), Finsupp.weight_single, inv_one]
    simp
  · have h2 : (X () + X () : MvPolynomial Unit (ZMod 2)) = 0 := by
      calc (X () + X () : MvPolynomial Unit (ZMod 2))
          = C (1 + 1) * X () := by rw [C_add, add_mul, C_1, one_mul]
        _ = 0 := by rw [show (1 + 1 : ZMod 2) = 0 from by decide, C_0, zero_mul]
    rw [pow_two, pderiv_mul, pderiv_X_self, one_mul, mul_one, h2]

/-- **Rejection test: the domain hypothesis is not decoration.** Over `ZMod 4` the square of
`2 X` is `0`, so the index of the product is `⊤` while the indices add up to `2`. -/
example : index (fun _ ↦ (1 : ℝ)) (0 : Unit → ZMod 4)
      ((C 2 * X () : MvPolynomial Unit (ZMod 4)) * (C 2 * X ())) = ⊤ ∧
    index (fun _ ↦ (1 : ℝ)) (0 : Unit → ZMod 4) (C 2 * X () : MvPolynomial Unit (ZMod 4))
      + index (fun _ ↦ (1 : ℝ)) (0 : Unit → ZMod 4)
        (C 2 * X () : MvPolynomial Unit (ZMod 4)) = 2 := by
  have h2 : (2 : ZMod 4) ≠ 0 := by decide
  have hone : index (fun _ ↦ (1 : ℝ)) (0 : Unit → ZMod 4)
      (C 2 * X () : MvPolynomial Unit (ZMod 4)) = 1 := by
    rw [index_eq_weightedOrder _ (fun _ ↦ zero_le_one), taylorAt_zero, C_mul_X_eq_monomial,
      weightedOrder_monomial h2, Finsupp.weight_single, inv_one]
    simp
  refine ⟨(index_eq_top_iff _ (fun _ ↦ zero_le_one) _ _).mpr ?_, by rw [hone]; norm_num⟩
  rw [C_mul_X_eq_monomial, monomial_mul_monomial, show (2 : ZMod 4) * 2 = 0 from by decide,
    monomial_zero]

end MvPolynomial

end

end
