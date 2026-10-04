/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormInverseHeight
public import QuantitativeSubspace.FormMonomialCount

-- Used only inside proofs.
import Mathlib.Algebra.FiniteSupport.Basic

/-!
# The auxiliary polynomial (EF13 Lemmas 13.4, 13.5, Prop. 13.6)

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, §13.

EF13 build the auxiliary polynomial `P` in `m` blocks of `N = C(n, n-k)` variables, homogeneous
of degree `r_h` in block `h`, whose Hasse derivatives of small order vanish to high order along
the forms `L̂^{(v)}` of the exterior power (§11) at every place. The polynomial machinery is
Schmidt's, already in `DiophantineApproximation` (Layer 5.2): `MvPolynomial.blockSubst`,
`MvPolynomial.multiMons`, the chain rule `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero`, and
the multihomogeneous Siegel lemma. This file supplies EF13's counting and choice of places.

* **Lemma 13.4.** EF13's `d^{(v)}_{I,J}(a_P)`, the coefficient of `∏ L̂_l^{(v)}(X_h)^{J_{hl}}` in
  `P_I = ∂_I P`, is `(blockSubst (L̂^{(v)})⁻¹ (∂_I P)).coeff J`; (13.10) is
  `MvPolynomial.blockSubst_blockSubst`. The bounds (13.11) are
  `FormSystem.iSup_coeff_blockSubst_hasseDeriv_le` (archimedean type) and
  `iSup_coeff_blockSubst_hasseDeriv_le_of_isNonarchimedean`, against the reference tuple
  `FormSystem.invTuple` of the joint Lemma 11.5 (`QuantitativeSubspace.FormInverseHeight`).
* **Lemma 13.3 on the monomials.** `MvPolynomial.blockAvg r ν f` is EF13's
  `Σ_h r_h⁻¹ Σ_l ν_{hl} f_{hl}`, and `MvPolynomial.card_filter_multiMons_le` is Lemma 13.3 on
  `multiMons r` (`multiMons_eq_map`: these are `U(r)`).
* **Siegel's lemma for families of conditions**:
  `MvPolynomial.exists_ne_zero_coeff_blockSubst_eq_zero_of_card`.
* **Lemma 13.5**: `FormSystem.exists_auxiliaryPolynomial`.
* **Prop. 13.6**: `FormSystem.exists_representatives` (the set `S₀` of (13.30)–(13.32)),
  `FormSystem.exists_auxiliaryPolynomial_hasseDeriv` ((i)–(iii)) and
  `FormSystem.prod_iSup_coeff_blockSubst_hasseDeriv_le` ((iv), (13.29)).

## Implementation notes

⚠ **Heights.** `P.logHeight` is the logarithmic height of the coefficient vector relative to `K`
with sup norms at every place (`Height.mulHeight`), where EF13 use `H₂` (ℓ² norms) and absolute
heights. The constants are therefore different. The bound (13.18) reads
`h(P) ≤ ½ log |D_K| + ([K:ℚ](N/2 + log N + log p!) + 2ps log H_L) Σ_h r_h` here, with
`p = n - k` and `s = #matSet ≤ R^n`; EF13 have `log H₂(P) ≤ log C_K + (3n log 2 + R^n log H_L) Σ r`.
The factor `2` in the exponent of `H_L` comes from the joint Lemma 11.5.

⚠ **(13.22) is replaced by an explicit count.** EF13 derive (13.13) from (13.22)
`m ≥ 2nε⁻² log(4R/ε)` through `s₀ ≤ (3R/ε)^n`, and two steps there do not go through as written.
The points `c_{iv}/γ_v` lie in `[-(n-1), 1]^n`, not `[-1, 1]^n`, since `Σ_i c_{iv} = 0`. And
`2((3R/ε)^n + 1) ≤ (4R/ε)^n` fails for `n = 2`. Here
`FormSystem.exists_representatives` cuts `[-(n-1), 1]^n` into cells of side `ε` and gets
`s₀ ≤ #matSet (n/ε + 2)^n`. Prop. 13.6 assumes `2 (#matSet (n/ε + 2)^n + 1) ≤ e^{mε²/2}`.

⚠ **The exponents at `v₀` are an input.** EF13's `ĉ_{l,v₀}(Q_h)` come from Davenport's lemma and
satisfy (11.21) and (11.22) only through Lemmas 9.3, 9.4 and Theorem 8.1's constant `C₂`, which
are Q4.1. Lemma 13.5 and Prop. 13.6 take reals `e_{hs}` with `|e_{hs}| ≤ n` and
`Σ_s e_{hs} ≤ -δ/n` instead.

⚠ **Prop. 13.6 (i) holds at every place**, `v₀` included: at a place with `c_v = 0` there is no
`J` with (13.24). At the other places the conditions are imposed at a representative `v₁ ∈ S₀`
with the same matrix and nearby `c_{v₁}/γ_{v₁}`, and propagated to the derivatives by the chain
rule.
-/

@[expose] public section

open Finset Module Matrix Real

namespace MvPolynomial

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

/-! ### Block averages and the monomial count on `multiMons` -/

/-- EF13's weighted block average `Σ_h r_h⁻¹ Σ_l ν_{hl} f_{hl}` of a monomial `ν` against reals
`f`, as in (13.7), (13.14), (13.16). -/
noncomputable def blockAvg (r : κ → ℕ) (ν : κ × ι →₀ ℕ) (f : κ → ι → ℝ) : ℝ :=
  ∑ h, (∑ l, (ν (h, l) : ℝ) * f h l) / r h

omit [DecidableEq κ] [DecidableEq ι] in
theorem blockAvg_add_left (r : κ → ℕ) (ν μ : κ × ι →₀ ℕ) (f : κ → ι → ℝ) :
    blockAvg r (ν + μ) f = blockAvg r ν f + blockAvg r μ f := by
  simp only [blockAvg, Finsupp.add_apply, Nat.cast_add, add_mul, sum_add_distrib, add_div]

omit [DecidableEq κ] [DecidableEq ι] in
theorem blockAvg_add_right (r : κ → ℕ) (ν : κ × ι →₀ ℕ) (f g : κ → ι → ℝ) :
    blockAvg r ν (f + g) = blockAvg r ν f + blockAvg r ν g := by
  simp only [blockAvg, Pi.add_apply, mul_add, sum_add_distrib, add_div]

omit [DecidableEq κ] [DecidableEq ι] in
theorem blockAvg_smul (r : κ → ℕ) (ν : κ × ι →₀ ℕ) (a : ℝ) (f : κ → ι → ℝ) :
    blockAvg r ν (a • f) = a * blockAvg r ν f := by
  simp only [blockAvg, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun h _ ↦ by
    rw [sum_div, sum_div, mul_sum]
    exact sum_congr rfl fun l _ ↦ by ring

omit [DecidableEq κ] [DecidableEq ι] in
theorem blockAvg_mono (r : κ → ℕ) (ν : κ × ι →₀ ℕ) {f g : κ → ι → ℝ} (h : ∀ h l, f h l ≤ g h l) :
    blockAvg r ν f ≤ blockAvg r ν g :=
  sum_le_sum fun h' _ ↦ div_le_div_of_nonneg_right
    (sum_le_sum fun l _ ↦ mul_le_mul_of_nonneg_left (h h' l) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

omit [DecidableEq κ] [DecidableEq ι] in
/-- A block average against a bounded `f` is bounded by the block average of the constant. -/
theorem abs_blockAvg_le (r : κ → ℕ) (ν : κ × ι →₀ ℕ) {f : κ → ι → ℝ} {C : ℝ}
    (h : ∀ h l, |f h l| ≤ C) :
    |blockAvg r ν f| ≤ C * blockAvg r ν 1 := by
  rw [abs_le]
  constructor
  · have := blockAvg_mono r ν (f := (-C) • (1 : κ → ι → ℝ)) (g := f) fun h' l ↦ by
      simpa using neg_le_of_abs_le (h h' l)
    rwa [blockAvg_smul, neg_mul] at this
  · have := blockAvg_mono r ν (f := f) (g := C • (1 : κ → ι → ℝ)) fun h' l ↦ by
      simpa using le_of_abs_le (h h' l)
    rwa [blockAvg_smul] at this

/-- The block average of `1` over a monomial of multidegree `r` is the number of blocks. -/
theorem blockAvg_one_of_mem {r : κ → ℕ} (hr : ∀ h, r h ≠ 0) {ν : κ × ι →₀ ℕ}
    (hν : ν ∈ multiMons (ι := ι) r) : blockAvg r ν 1 = Fintype.card κ := by
  simp only [blockAvg, Pi.one_apply, mul_one]
  rw [← card_univ, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine sum_congr rfl fun h _ ↦ ?_
  rw [← Nat.cast_sum, mem_multiMons.mp hν h, div_self (Nat.cast_ne_zero.mpr (hr h))]

omit [DecidableEq κ] [DecidableEq ι] in
/-- The block average of `1` depends only on the degrees in the blocks. -/
theorem blockAvg_one_eq {r : κ → ℕ} {ν μ : κ × ι →₀ ℕ}
    (h : ∀ h, ∑ l, ν (h, l) = ∑ l, μ (h, l)) : blockAvg r ν 1 = blockAvg r μ 1 := by
  simp only [blockAvg, Pi.one_apply, mul_one, ← Nat.cast_sum, h]

/-- The monomial of a block tuple `j : κ → ι → ℕ`. -/
noncomputable def blockExp : (κ → ι → ℕ) ≃ (κ × ι →₀ ℕ) :=
  (Equiv.curry κ ι ℕ).symm.trans Finsupp.equivFunOnFinite.symm

omit [DecidableEq κ] [DecidableEq ι] in
@[simp]
theorem blockExp_apply (j : κ → ι → ℕ) (x : κ × ι) : blockExp j x = j x.1 x.2 := rfl

omit [DecidableEq κ] [DecidableEq ι] in
@[simp]
theorem blockExp_symm_apply (ν : κ × ι →₀ ℕ) (h : κ) (l : ι) : blockExp.symm ν h l = ν (h, l) :=
  rfl

/-- The monomials of multidegree `r` are EF13's `U(r)` (`Finset.blockCompositions`). -/
theorem multiMons_eq_map (r : κ → ℕ) :
    multiMons (ι := ι) r = (blockCompositions r).map blockExp.toEmbedding := by
  ext ν
  rw [mem_map_equiv, mem_blockCompositions, mem_multiMons]
  rfl

/-- **EF13 Lemma 13.3** on the monomials of multidegree `r`: if `|c_{hl}| ≤ γ`, at most
`e^{-mε²/2} #U(r)` of them have block average at least `N⁻¹ Σ_{h,l} c_{hl} + mγε`. -/
theorem card_filter_multiMons_le [Nonempty ι] {r : κ → ℕ} (hr : ∀ h, r h ≠ 0)
    {c : κ → ι → ℝ} {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 ≤ ε) (hc : ∀ h l, |c h l| ≤ γ) :
    (#{ν ∈ multiMons (ι := ι) r | (∑ h, ∑ l, c h l) / Fintype.card ι +
        Fintype.card κ * γ * ε ≤ blockAvg r ν c} : ℝ) ≤
      exp (-(Fintype.card κ * ε ^ 2 / 2)) * #(multiMons (ι := ι) r) := by
  rw [multiMons_eq_map, filter_map, card_map, card_map]
  exact card_filter_blockCompositions_le hr hγ hε hc

/-- A coefficient of a multihomogeneous polynomial of multidegree `r`, read in any coordinates,
vanishes outside the monomials of multidegree `r`. -/
theorem coeff_blockSubst_eq_zero_of_notMem {K : Type*} [Field K] {r : κ → ℕ}
    {P : MvPolynomial (κ × ι) K} (hP : IsMultiHomogeneous r P) (M : Matrix ι ι K)
    {ν : κ × ι →₀ ℕ} (hν : ν ∉ multiMons (ι := ι) r) : (blockSubst M P).coeff ν = 0 := by
  by_contra h
  exact hν (mem_multiMons.mpr ((hP.blockSubst M) h))

/-! ### Siegel's lemma for families of conditions -/

section Siegel

variable {K : Type*} [Field K] [NumberField K] {ρ : Type*} [Finite ρ]

/-- **Siegel's lemma for families of conditions** (the core of EF13 Lemma 13.5): for each `t` in a
finite set `T`, the coefficients of `P` read in the coordinates `Mat t` at the monomials in `Bad t`
are to vanish. If there are at most half as many conditions as monomials of multidegree `r`, and
a reference tuple `y` dominates every `Mat t` at every absolute value, there is such a nonzero
multihomogeneous `P` of logarithmic height `O(Σ_h r_h)`. -/
theorem exists_ne_zero_coeff_blockSubst_eq_zero_of_card [Nonempty ι] {r : κ → ℕ} {τ : Type*}
    (T : Finset τ) (Mat : τ → Matrix ι ι K) (Bad : τ → Finset (κ × ι →₀ ℕ)) {y : ρ → K}
    (hy : y ≠ 0)
    (hMy : ∀ t ∈ T, ∀ w : AbsoluteValue K ℝ,
      (⨆ p : ι × ι, w (Mat t p.1 p.2)) ⊔ 1 ≤ ⨆ s, w (y s))
    (hcard : 2 * ∑ t ∈ T, (#(Bad t) : ℝ) ≤ #(multiMons (ι := ι) r)) :
    ∃ P : MvPolynomial (κ × ι) K, P ≠ 0 ∧ IsMultiHomogeneous r P ∧
      (∀ t ∈ T, ∀ ν ∈ Bad t, (blockSubst (Mat t) P).coeff ν = 0) ∧
      P.logHeight ≤ 2⁻¹ * Real.log |(NumberField.discr K : ℝ)|
        + ((finrank ℚ K : ℝ) / 2 * Fintype.card ι
            + Height.totalWeight K * Real.log (Fintype.card ι)
            + Real.log (Height.mulHeight y)) * ∑ h, (r h : ℝ) := by
  classical
  obtain ⟨P, hP0, hPh, hPc, hPh'⟩ := exists_ne_zero_isMultiHomogeneous_coeff_blockSubst_eq_zero
    (Row := Σ t : T, Bad t) (fun q ↦ Mat q.1) (fun q ↦ q.2) hy (fun q w ↦ hMy q.1 q.1.2 w)
    (by
      rw [Fintype.card_sigma]
      simpa [Fintype.card_coe, ← sum_coe_sort T (fun t ↦ (#(Bad t) : ℝ))] using hcard)
  exact ⟨P, hP0, hPh, fun t ht ν hν ↦ hPc ⟨⟨t, ht⟩, ⟨ν, hν⟩⟩, hPh'⟩

end Siegel

/-! ### Local factors over the support -/

section Support

variable {K : Type*} [Field K] {σ : Type*}

omit [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] in
/-- The local factor of a polynomial is the supremum over its support. -/
theorem iSup_coeff_eq_iSup_support (Q : MvPolynomial σ K) (w : AbsoluteValue K ℝ) :
    (⨆ J, w (Q.coeff J)) = ⨆ J : Q.support, w (Q.coeff J) := by
  refine le_antisymm (Real.iSup_le (fun J ↦ ?_) (Real.iSup_nonneg fun _ ↦ apply_nonneg _ _))
    (Real.iSup_le (fun J ↦ le_iSup_coeff Q w J) (iSup_coeff_nonneg Q w))
  by_cases hJ : J ∈ Q.support
  · exact le_ciSup (f := fun J : Q.support ↦ w (Q.coeff J)) (Finite.bddAbove_range _) ⟨J, hJ⟩
  · rw [notMem_support_iff.mp hJ, map_zero]
    exact Real.iSup_nonneg fun _ ↦ apply_nonneg _ _

omit [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] in
theorem coeff_support_ne_zero {Q : MvPolynomial σ K} (hQ : Q ≠ 0) :
    (fun J : Q.support ↦ Q.coeff J) ≠ 0 := by
  obtain ⟨J, hJ⟩ := Finset.nonempty_iff_ne_empty.mpr (mt support_eq_empty.mp hQ)
  exact fun h ↦ mem_support_iff.mp hJ (congrFun h ⟨J, hJ⟩)

omit [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] in
/-- The local factors of a nonzero polynomial are `1` at all but finitely many finite places. -/
theorem hasFiniteMulSupport_iSup_coeff [NumberField K] {Q : MvPolynomial σ K} (hQ : Q ≠ 0) :
    (fun v : NumberField.FinitePlace K ↦ ⨆ J, v (Q.coeff J)).HasFiniteMulSupport := by
  rw [show (fun v : NumberField.FinitePlace K ↦ ⨆ J, v (Q.coeff J)) =
      fun v ↦ ⨆ J : Q.support, v (Q.coeff J) from
    funext fun v ↦ iSup_coeff_eq_iSup_support Q v.1]
  exact Height.hasFiniteMulSupport_iSup (coeff_support_ne_zero hQ)

omit [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] in
/-- The height of a nonzero polynomial as a product of local factors. -/
theorem mulHeight_eq_prod [NumberField K] {Q : MvPolynomial σ K} (hQ : Q ≠ 0) :
    Q.mulHeight = (∏ v : NumberField.InfinitePlace K, (⨆ J, v (Q.coeff J)) ^ v.mult) *
      ∏ᶠ v : NumberField.FinitePlace K, ⨆ J, v (Q.coeff J) := by
  rw [show (fun v : NumberField.FinitePlace K ↦ ⨆ J, v (Q.coeff J)) =
      fun v ↦ ⨆ J : Q.support, v (Q.coeff J) from
    funext fun v ↦ iSup_coeff_eq_iSup_support Q v.1]
  rw [Finset.prod_congr rfl fun v _ ↦ by
    rw [show (⨆ J, v (Q.coeff J)) = ⨆ J : Q.support, v (Q.coeff J) from
      iSup_coeff_eq_iSup_support Q v.1]]
  rw [MvPolynomial.mulHeight, Finsupp.mulHeight_eq_mulHeight_subtype Q.coeff (s := Q.support)
    fun J hJ ↦ mem_support_iff.mpr (Finsupp.mem_support_iff.mp hJ),
    NumberField.mulHeight_eq (coeff_support_ne_zero hQ)]

omit [DecidableEq κ] [DecidableEq ι] in
/-- A Hasse derivative has no more monomials than the polynomial. -/
theorem card_support_hasseDeriv_le (I : σ →₀ ℕ) (P : MvPolynomial σ K) :
    #(hasseDeriv I P).support ≤ #P.support := by
  refine card_le_card_of_injOn (· + I) (fun ν hν ↦ ?_) fun a _ b _ h ↦ add_right_cancel h
  rw [mem_coe, mem_support_iff] at hν ⊢
  intro hc
  rw [hasseDeriv_coeff, hc, mul_zero] at hν
  exact hν rfl

end Support

end MvPolynomial

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]

open MvPolynomial

/-! ### The data at all places -/

namespace FormSystem

variable (L : FormSystem K ι)

/-- The matrix `L^{(v)}` at a place `v` of `K`, infinite or finite. -/
def mat : InfinitePlace K ⊕ FinitePlace K → Matrix ι ι K := Sum.elim L.arch L.fin

theorem mat_mem_matSet (v : InfinitePlace K ⊕ FinitePlace K) : L.mat v ∈ L.matSet := by
  rcases v with v | v
  exacts [L.arch_mem_matSet v, L.fin_mem_matSet v]

end FormSystem

namespace FormExponent

variable (c : FormExponent K ι)

/-- The exponents `c_v` at a place `v` of `K`, infinite or finite. -/
def vec : InfinitePlace K ⊕ FinitePlace K → ι → ℝ := Sum.elim c.arch c.fin

omit [Fintype ι] [LinearOrder ι] in
theorem exteriorPower_vec (p : ℕ) (v : InfinitePlace K ⊕ FinitePlace K)
    (s : Set.powersetCard ι p) : (c.exteriorPower p).vec v s = ∑ i ∈ s.val, c.vec v i := by
  rcases v with v | v <;> rfl

variable {c}

omit [LinearOrder ι] in
/-- With `Σ_i c_{iv} = 0` (EF13 (8.3)), the largest exponent is nonnegative. -/
theorem iSup_vec_nonneg [Nonempty ι] {v : InfinitePlace K ⊕ FinitePlace K}
    (h0 : ∑ i, c.vec v i = 0) : 0 ≤ ⨆ i, c.vec v i := by
  by_contra h
  have : ∑ i, c.vec v i < 0 :=
    sum_neg (fun i _ ↦ (le_ciSup (Finite.bddAbove_range _) i).trans_lt (not_le.1 h))
      univ_nonempty
  linarith

omit [LinearOrder ι] in
/-- With `Σ_i c_{iv} = 0`, every exponent is at least `-(n-1) max_i c_{iv}`. -/
theorem neg_le_vec {v : InfinitePlace K ⊕ FinitePlace K} (h0 : ∑ i, c.vec v i = 0) (i : ι) :
    -((Fintype.card ι - 1 : ℕ) * ⨆ i, c.vec v i) ≤ c.vec v i := by
  classical
  have hsplit := add_sum_erase univ (c.vec v) (mem_univ i)
  have hle : ∑ j ∈ univ.erase i, c.vec v j ≤ #(univ.erase i) * ⨆ i, c.vec v i := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun j _ ↦ le_ciSup (Finite.bddAbove_range _) j
  rw [card_erase_of_mem (mem_univ i), card_univ] at hle
  linarith

omit [LinearOrder ι] in
/-- If the largest exponent is `≤ 0` while `Σ_i c_{iv} = 0`, all exponents vanish. -/
theorem vec_eq_zero_of_iSup_nonpos {v : InfinitePlace K ⊕ FinitePlace K}
    (h0 : ∑ i, c.vec v i = 0) (hγ : (⨆ i, c.vec v i) ≤ 0) (i : ι) : c.vec v i = 0 := by
  have hle : ∀ j, c.vec v j ≤ 0 := fun j ↦ (le_ciSup (Finite.bddAbove_range _) j).trans hγ
  exact le_antisymm (hle i) (by
    have := (sum_eq_zero_iff_of_nonpos fun j _ ↦ hle j).1 h0 i (mem_univ i)
    rw [this])

omit [LinearOrder ι] in
/-- **EF13 (11.18)** at one place: `Σ_s ĉ_{sv} = 0` when `Σ_i c_{iv} = 0`. -/
theorem sum_exteriorPower_vec_eq_zero {p : ℕ} (hp : 1 ≤ p) {v : InfinitePlace K ⊕ FinitePlace K}
    (h0 : ∑ i, c.vec v i = 0) : ∑ s, (c.exteriorPower p).vec v s = 0 := by
  rcases v with v | v
  · change ∑ s, (c.exteriorPower p).arch v s = 0
    rw [c.sum_exteriorPower_arch hp]
    simp [show ∑ i, c.arch v i = 0 from h0]
  · change ∑ s, (c.exteriorPower p).fin v s = 0
    rw [c.sum_exteriorPower_fin hp]
    simp [show ∑ i, c.fin v i = 0 from h0]

omit [LinearOrder ι] in
/-- **EF13 (11.19)** at one place, in the weaker form `|ĉ_{sv}| ≤ n max_i c_{iv}`. -/
theorem abs_exteriorPower_vec_le {p : ℕ} (hp : 1 ≤ p) (hpn : p < Fintype.card ι)
    {v : InfinitePlace K ⊕ FinitePlace K} (h0 : ∑ i, c.vec v i = 0) (s : Set.powersetCard ι p) :
    |(c.exteriorPower p).vec v s| ≤ Fintype.card ι * ⨆ i, c.vec v i := by
  have : Nonempty ι := ⟨(Set.powersetCard.nonempty_ne_univ hp hpn s).1.choose⟩
  have hγ := iSup_vec_nonneg h0
  have hle : |(c.exteriorPower p).vec v s| ≤ (Fintype.card ι - 1 : ℕ) * ⨆ i, c.vec v i := by
    rcases v with v | v
    · exact c.abs_exteriorPower_arch_le hp hpn h0 s
    · exact c.abs_exteriorPower_fin_le hp hpn h0 s
  refine hle.trans (mul_le_mul_of_nonneg_right ?_ hγ)
  exact_mod_cast Nat.sub_le _ _

end FormExponent

/-! ### EF13 Lemma 13.5 -/

namespace FormSystem

variable {L : FormSystem K ι} {κ : Type*} [Fintype κ]

/-- **EF13 Lemma 13.5.** Let `L^{(v₀)}` be the coordinates (8.8), `Σ_i c_{iv} = 0` (8.3),
`1 ≤ p < n` (`p = n - k`), `N = C(n, p)`, and `r_h ≥ 1`. Let `S₀` be a finite set of places
with `c_v ≠ 0`, `m = #κ` and `2 (#S₀ + 1) ≤ e^{mε²/2}` (13.13). Let `e_{hs}` (EF13's
`ĉ_{s,v₀}(Q_h)`) satisfy `|e_{hs}| ≤ n` (11.22) and `Σ_s e_{hs} ≤ -δ/n` (11.21). Then there is a
nonzero polynomial `P`, multihomogeneous of multidegree `r` in `m` blocks of `N` variables, such
that

* (i) for `v ∈ S₀`, the coefficients of `P` read in the coordinates `L̂^{(v)}` vanish at every
  monomial `ν` with `Σ_h r_h⁻¹ Σ_s ν_{hs} ĉ_{sv} ≥ mnε max_i c_{iv}` (13.14), (13.15);
* (ii) the coefficients of `P` vanish at every `ν` with
  `Σ_h r_h⁻¹ Σ_s ν_{hs} e_{hs} ≥ -mδ/(nN) + mnε` (13.16), (13.17);
* (iii) `h(P) ≤ ½ log |D_K| + ([K:ℚ](N/2 + log N + log p!) + 2ps log H_L) Σ_h r_h`, relative to
  `K`, `s = #matSet` (13.18). -/
theorem exists_auxiliaryPolynomial {v₀ : FinitePlace K} (hL : L.fin v₀ = 1)
    {c : FormExponent K ι} (hc0 : ∀ v, ∑ i, c.vec v i = 0) {p : ℕ} (hp : 1 ≤ p)
    (hpn : p < Fintype.card ι) {r : κ → ℕ} (hr : ∀ h, r h ≠ 0)
    (S₀ : Finset (InfinitePlace K ⊕ FinitePlace K)) (hS₀ : ∀ v ∈ S₀, 0 < ⨆ i, c.vec v i)
    {ε : ℝ} (hε : 0 ≤ ε) (hm : 2 * (#S₀ + 1 : ℝ) ≤ exp (Fintype.card κ * ε ^ 2 / 2))
    (e : κ → Set.powersetCard ι p → ℝ) {δ : ℝ} (he : ∀ h s, |e h s| ≤ Fintype.card ι)
    (hes : ∀ h, ∑ s, e h s ≤ -δ / Fintype.card ι) :
    ∃ P : MvPolynomial (κ × Set.powersetCard ι p) K, P ≠ 0 ∧ IsMultiHomogeneous r P ∧
      (∀ v ∈ S₀, ∀ ν, Fintype.card κ * Fintype.card ι * ε * (⨆ i, c.vec v i) ≤
          blockAvg r ν (fun _ s ↦ (c.exteriorPower p).vec v s) →
        (blockSubst ((L.mat v).compound p)⁻¹ P).coeff ν = 0) ∧
      (∀ ν, -(Fintype.card κ * δ / (Fintype.card ι * Fintype.card (Set.powersetCard ι p))) +
          Fintype.card κ * Fintype.card ι * ε ≤ blockAvg r ν e → P.coeff ν = 0) ∧
      P.logHeight ≤ 2⁻¹ * Real.log |(NumberField.discr K : ℝ)|
        + ((finrank ℚ K : ℝ) / 2 * Fintype.card (Set.powersetCard ι p)
            + finrank ℚ K * Real.log (Fintype.card (Set.powersetCard ι p))
            + finrank ℚ K * Real.log p.factorial
            + 2 * p * #L.matSet * Real.log L.mulFormHeight) * ∑ h, (r h : ℝ) := by
  classical
  have : Nonempty (Set.powersetCard ι p) := Set.powersetCard.nonempty_iff.2 hpn.le
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  set m : ℝ := (Fintype.card κ : ℝ) with hm_def
  set N : ℝ := (Fintype.card (Set.powersetCard ι p) : ℝ) with hN_def
  have hn : 0 < n := by rw [hn_def]; exact_mod_cast (Nat.zero_lt_of_lt hpn)
  have hN : 0 < N := by rw [hN_def]; exact_mod_cast Fintype.card_pos
  have h1 := L.one_mem_forms hL
  -- the conditions: `none` stands for `v₀`
  set T : Finset (Option (InfinitePlace K ⊕ FinitePlace K)) :=
    insert none (S₀.map Function.Embedding.some) with hT
  set Bmat : Option (InfinitePlace K ⊕ FinitePlace K) → Matrix ι ι K :=
    fun t ↦ t.elim (L.fin v₀) L.mat with hBmat
  set cv : Option (InfinitePlace K ⊕ FinitePlace K) → κ → Set.powersetCard ι p → ℝ :=
    fun t ↦ t.elim e fun v _ s ↦ (c.exteriorPower p).vec v s with hcv
  set γv : Option (InfinitePlace K ⊕ FinitePlace K) → ℝ :=
    fun t ↦ t.elim n fun v ↦ n * ⨆ i, c.vec v i with hγv
  set Bad : Option (InfinitePlace K ⊕ FinitePlace K) → Finset (κ × Set.powersetCard ι p →₀ ℕ) :=
    fun t ↦ {ν ∈ multiMons r | (∑ h, ∑ s, cv t h s) / N + m * γv t * ε ≤ blockAvg r ν (cv t)}
    with hBad
  have hcount : ∀ t ∈ T, (#(Bad t) : ℝ) ≤
      exp (-(m * ε ^ 2 / 2)) * #(multiMons (ι := Set.powersetCard ι p) r) := by
    intro t ht
    rcases t with _ | v
    · exact card_filter_multiMons_le hr hn hε he
    · have hv : v ∈ S₀ := by simpa [hT] using ht
      exact card_filter_multiMons_le hr (mul_pos hn (hS₀ v hv)) hε fun h s ↦
        c.abs_exteriorPower_vec_le hp hpn (hc0 v) s
  have hTcard : (#T : ℝ) ≤ #S₀ + 1 := by
    have := card_insert_le none (S₀.map Function.Embedding.some)
    rw [card_map] at this
    exact_mod_cast this
  have hcard : 2 * ∑ t ∈ T, (#(Bad t) : ℝ) ≤ #(multiMons (ι := Set.powersetCard ι p) r) := by
    have hV : (0 : ℝ) ≤ #(multiMons (ι := Set.powersetCard ι p) r) := Nat.cast_nonneg _
    calc 2 * ∑ t ∈ T, (#(Bad t) : ℝ)
        ≤ 2 * ∑ _t ∈ T, exp (-(m * ε ^ 2 / 2)) * #(multiMons (ι := Set.powersetCard ι p) r) :=
          mul_le_mul_of_nonneg_left (sum_le_sum hcount) zero_le_two
      _ = (2 * #T * exp (-(m * ε ^ 2 / 2))) * #(multiMons (ι := Set.powersetCard ι p) r) := by
          rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ 1 * #(multiMons (ι := Set.powersetCard ι p) r) := by
          refine mul_le_mul_of_nonneg_right ?_ hV
          rw [exp_neg, ← div_eq_mul_inv, div_le_one (exp_pos _)]
          exact (mul_le_mul_of_nonneg_left hTcard zero_le_two).trans hm
      _ = _ := one_mul _
  have hMy : ∀ t ∈ T, ∀ w : AbsoluteValue K ℝ,
      (⨆ q : Set.powersetCard ι p × Set.powersetCard ι p,
        w (((Bmat t).compound p)⁻¹ q.1 q.2)) ⊔ 1 ≤ ⨆ s, w (L.invTuple p s) := by
    intro t _ w
    refine le_iSup_invTuple ?_ w
    rcases t with _ | v
    exacts [L.fin_mem_matSet v₀, L.mat_mem_matSet v]
  obtain ⟨P, hP0, hPh, hPc, hPht⟩ := exists_ne_zero_coeff_blockSubst_eq_zero_of_card T
    (fun t ↦ ((Bmat t).compound p)⁻¹) Bad (L.invTuple_ne_zero p) hMy hcard
  refine ⟨P, hP0, hPh, fun v hv ν hν ↦ ?_, fun ν hν ↦ ?_, ?_⟩
  · -- (i)
    by_cases hmem : ν ∈ multiMons (ι := Set.powersetCard ι p) r
    · refine hPc (some v) (by simp [hT, hv]) ν (mem_filter.mpr ⟨hmem, ?_⟩)
      change (∑ h : κ, ∑ s, (c.exteriorPower p).vec v s) / N + m * (n * ⨆ i, c.vec v i) * ε ≤
        blockAvg r ν fun _ s ↦ (c.exteriorPower p).vec v s
      simp only [c.sum_exteriorPower_vec_eq_zero hp (hc0 v), sum_const_zero, zero_div, zero_add]
      linarith
    · exact coeff_blockSubst_eq_zero_of_notMem hPh _ hmem
  · -- (ii)
    have hP1 : blockSubst ((Bmat none).compound p)⁻¹ P = P := by
      simp [hBmat, hL, blockSubst_one]
    by_cases hmem : ν ∈ multiMons (ι := Set.powersetCard ι p) r
    · rw [← hP1]
      refine hPc none (mem_insert_self _ _) ν (mem_filter.mpr ⟨hmem, ?_⟩)
      change (∑ h, ∑ s, e h s) / N + m * n * ε ≤ blockAvg r ν e
      have hsum : ∑ h, ∑ s, e h s ≤ m * (-δ / n) := by
        calc ∑ h, ∑ s, e h s ≤ ∑ _h : κ, -δ / n := sum_le_sum fun h _ ↦ hes h
          _ = m * (-δ / n) := by rw [sum_const, card_univ, nsmul_eq_mul]
      have : (∑ h, ∑ s, e h s) / N ≤ -(m * δ / (n * N)) := by
        rw [div_le_iff₀ hN]
        calc ∑ h, ∑ s, e h s ≤ m * (-δ / n) := hsum
          _ = -(m * δ / (n * N)) * N := by field_simp
      linarith
    · by_contra h
      exact hmem (mem_multiMons.mpr (hPh h))
  · -- (iii)
    refine hPht.trans ?_
    have hy := L.mulHeight_invTuple_le h1 p
    have hH1 := L.one_le_mulFormHeight
    have hlog : Real.log (Height.mulHeight (L.invTuple p)) ≤
        finrank ℚ K * Real.log p.factorial + 2 * p * #L.matSet * Real.log L.mulFormHeight := by
      refine (Real.log_le_log (Height.mulHeight_pos _) hy).trans_eq ?_
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      push_cast
      ring
    rw [NumberField.totalWeight_eq_finrank]
    have hr0 : (0 : ℝ) ≤ ∑ h, (r h : ℝ) := sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hlog hr0]

/-! ### EF13 Prop. 13.6 -/

omit [Fintype κ] in
/-- **The representatives of EF13 (13.30)–(13.32).** There is a finite set `S₀` of places with
`c_v ≠ 0`, of size at most `#matSet (n/ε + 2)^n`, such that every place `v` with `c_v ≠ 0` has a
representative `v₁ ∈ S₀` with the same matrix `L^{(v₁)} = L^{(v)}` and
`|c_{iv}/γ_v - c_{iv₁}/γ_{v₁}| < ε`, `γ_v = max_i c_{iv}`. -/
theorem exists_representatives {c : FormExponent K ι} (hc0 : ∀ v, ∑ i, c.vec v i = 0)
    (hn : 1 ≤ Fintype.card ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ S₀ : Finset (InfinitePlace K ⊕ FinitePlace K), (∀ v ∈ S₀, 0 < ⨆ i, c.vec v i) ∧
      (#S₀ : ℝ) ≤ #L.matSet * (Fintype.card ι / ε + 2) ^ Fintype.card ι ∧
      ∀ v, 0 < ⨆ i, c.vec v i → ∃ v₁ ∈ S₀, L.mat v₁ = L.mat v ∧
        ∀ i, |c.vec v i / (⨆ j, c.vec v j) - c.vec v₁ i / (⨆ j, c.vec v₁ j)| < ε := by
  classical
  set γ : InfinitePlace K ⊕ FinitePlace K → ℝ := fun v ↦ ⨆ j, c.vec v j with hγ
  have hS1fin : {v : InfinitePlace K ⊕ FinitePlace K | 0 < γ v}.Finite := by
    refine ((Set.finite_range Sum.inl).union (c.finite_setOf_fin_ne_zero.image Sum.inr)).subset ?_
    rintro (v | v) hv
    · exact Or.inl ⟨v, rfl⟩
    · refine Or.inr ⟨v, fun h ↦ ?_, rfl⟩
      change 0 < ⨆ j, c.fin v j at hv
      rw [h] at hv
      simp at hv
  set S₁ := hS1fin.toFinset
  set key : InfinitePlace K ⊕ FinitePlace K → Matrix ι ι K × (ι → ℤ) :=
    fun v ↦ (L.mat v, fun i ↦ ⌊c.vec v i / γ v / ε⌋) with hkey
  set rep := Function.invFunOn key (S₁ : Set (InfinitePlace K ⊕ FinitePlace K))
  refine ⟨(S₁.image key).image rep, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hv
    obtain ⟨v', hv', rfl⟩ := mem_image.mp hk
    have := Function.invFunOn_mem (f := key) (⟨v', by simpa using hv', rfl⟩ :
      ∃ a ∈ (S₁ : Set _), key a = key v')
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at this
    exact this
  · -- the count
    set n : ℝ := (Fintype.card ι : ℝ)
    set lo : ℤ := ⌊-((Fintype.card ι - 1 : ℕ) : ℝ) / ε⌋
    set hi : ℤ := ⌊1 / ε⌋
    have hn1 : ((Fintype.card ι - 1 : ℕ) : ℝ) = n - 1 := by
      rw [Nat.cast_sub hn, Nat.cast_one]
    have hsub : S₁.image key ⊆ L.matSet ×ˢ Fintype.piFinset fun _ : ι ↦ Icc lo hi := by
      intro k hk
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hk
      have hγv : 0 < γ v := by simpa [S₁] using hv
      refine mem_product.mpr ⟨L.mat_mem_matSet v, Fintype.mem_piFinset.mpr fun i ↦ ?_⟩
      have hle : c.vec v i ≤ γ v := le_ciSup (Finite.bddAbove_range _) i
      have hge := FormExponent.neg_le_vec (hc0 v) i
      refine mem_Icc.mpr ⟨Int.floor_mono ?_, Int.floor_mono ?_⟩
      · refine div_le_div_of_nonneg_right ?_ hε.le
        rw [le_div_iff₀ hγv]
        linarith
      · refine div_le_div_of_nonneg_right ?_ hε.le
        rw [div_le_one hγv]
        exact hle
    have hlohi : lo ≤ hi + 1 := by
      have : -((Fintype.card ι - 1 : ℕ) : ℝ) / ε ≤ 1 / ε :=
        div_le_div_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι - 1)])
          hε.le
      have := Int.floor_mono this
      omega
    have hIcc : (#(Icc lo hi) : ℝ) ≤ n / ε + 2 := by
      have h := Int.card_Icc_of_le _ _ hlohi
      have h' : (#(Icc lo hi) : ℝ) = ((hi + 1 - lo : ℤ) : ℝ) := by
        rw [← h]
        push_cast
        rfl
      rw [h']
      push_cast
      have h1 : (hi : ℝ) ≤ 1 / ε := Int.floor_le _
      have h2 : -((Fintype.card ι - 1 : ℕ) : ℝ) / ε - 1 < lo := Int.sub_one_lt_floor _
      rw [hn1] at h2
      have h3 : -(n - 1) / ε = -(n / ε) + 1 / ε := by field_simp; ring
      rw [h3] at h2
      linarith
    calc (#((S₁.image key).image rep) : ℝ) ≤ #(S₁.image key) := by
          exact_mod_cast card_image_le
      _ ≤ #(L.matSet ×ˢ Fintype.piFinset fun _ : ι ↦ Icc lo hi) := by
          exact_mod_cast card_le_card hsub
      _ = #L.matSet * #(Icc lo hi) ^ Fintype.card ι := by
          rw [card_product, Fintype.card_piFinset, prod_const, card_univ]
          push_cast
          rfl
      _ ≤ #L.matSet * (n / ε + 2) ^ Fintype.card ι := by
          gcongr
  · intro v hv
    have hvS : v ∈ (S₁ : Set (InfinitePlace K ⊕ FinitePlace K)) := by simpa [S₁] using hv
    have hex : ∃ a ∈ (S₁ : Set (InfinitePlace K ⊕ FinitePlace K)), key a = key v := ⟨v, hvS, rfl⟩
    have heq : key (rep (key v)) = key v := Function.invFunOn_eq hex
    have hmem : rep (key v) ∈ (S₁ : Set (InfinitePlace K ⊕ FinitePlace K)) :=
      Function.invFunOn_mem hex
    have hγ1 : 0 < γ (rep (key v)) := by simpa [S₁] using hmem
    refine ⟨rep (key v), mem_image.mpr ⟨key v, mem_image_of_mem _ (by simpa [S₁] using hv), rfl⟩,
      (congrArg Prod.fst heq), fun i ↦ ?_⟩
    have hfl := congrFun (congrArg Prod.snd heq) i
    have := Int.abs_sub_lt_one_of_floor_eq_floor hfl.symm
    rw [← sub_div, abs_div, abs_of_pos hε, div_lt_one hε] at this
    exact this

omit [Fintype κ] [LinearOrder ι] in
/-- Comparing the `ĉ` at a place and at its representative (EF13 (13.32)). -/
theorem abs_exteriorPower_div_sub_le {c : FormExponent K ι} {p : ℕ}
    {v v₁ : InfinitePlace K ⊕ FinitePlace K} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ i, |c.vec v i / (⨆ j, c.vec v j) - c.vec v₁ i / (⨆ j, c.vec v₁ j)| < ε)
    (s : Set.powersetCard ι p) :
    |(c.exteriorPower p).vec v s / (⨆ j, c.vec v j) -
      (c.exteriorPower p).vec v₁ s / (⨆ j, c.vec v₁ j)| ≤ Fintype.card ι * ε := by
  rw [c.exteriorPower_vec, c.exteriorPower_vec, sum_div, sum_div, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ s.val, |c.vec v i / (⨆ j, c.vec v j) - c.vec v₁ i / (⨆ j, c.vec v₁ j)|
      ≤ ∑ _i ∈ s.val, ε := sum_le_sum fun i _ ↦ (h i).le
    _ = #s.val * ε := by rw [sum_const, nsmul_eq_mul]
    _ ≤ Fintype.card ι * ε :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_univ s.val) hε

/-- **EF13 Prop. 13.6.** Under the hypotheses of `exists_auxiliaryPolynomial`, with `ε > 0` and
`2 (#matSet (n/ε + 2)^n + 1) ≤ e^{mε²/2}` in place of (13.13), there is a nonzero polynomial
`P`, multihomogeneous of multidegree `r`, such that for every order `I` with
`Σ_h r_h⁻¹ Σ_s I_{hs} ≤ 2mε` (13.23):

* (i) at every place `v`, the coefficients of `∂_I P` read in the coordinates `L̂^{(v)}` vanish at
  every `J` with `Σ_h r_h⁻¹ Σ_s J_{hs} ĉ_{sv} > 4mnε max_i c_{iv}` (13.24), (13.25);
* (ii) the coefficients of `∂_I P` vanish at every `J` with
  `Σ_h r_h⁻¹ Σ_s J_{hs} e_{hs} > -mδ/(nN) + 4mnε` (13.26), (13.27);
* (iii) the height bound of `exists_auxiliaryPolynomial` (13.28). -/
theorem exists_auxiliaryPolynomial_hasseDeriv {v₀ : FinitePlace K} (hL : L.fin v₀ = 1)
    {c : FormExponent K ι} (hc0 : ∀ v, ∑ i, c.vec v i = 0) {p : ℕ} (hp : 1 ≤ p)
    (hpn : p < Fintype.card ι) {r : κ → ℕ} (hr : ∀ h, r h ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hm : 2 * (#L.matSet * (Fintype.card ι / ε + 2) ^ Fintype.card ι + 1) ≤
      exp (Fintype.card κ * ε ^ 2 / 2))
    (e : κ → Set.powersetCard ι p → ℝ) {δ : ℝ} (he : ∀ h s, |e h s| ≤ Fintype.card ι)
    (hes : ∀ h, ∑ s, e h s ≤ -δ / Fintype.card ι) :
    ∃ P : MvPolynomial (κ × Set.powersetCard ι p) K, P ≠ 0 ∧ IsMultiHomogeneous r P ∧
      (∀ v (I J : κ × Set.powersetCard ι p →₀ ℕ), blockAvg r I 1 ≤ 2 * Fintype.card κ * ε →
        4 * Fintype.card κ * Fintype.card ι * ε * (⨆ i, c.vec v i) <
          blockAvg r J (fun _ s ↦ (c.exteriorPower p).vec v s) →
        (blockSubst ((L.mat v).compound p)⁻¹ (hasseDeriv I P)).coeff J = 0) ∧
      (∀ I J : κ × Set.powersetCard ι p →₀ ℕ, blockAvg r I 1 ≤ 2 * Fintype.card κ * ε →
        -(Fintype.card κ * δ / (Fintype.card ι * Fintype.card (Set.powersetCard ι p))) +
          4 * Fintype.card κ * Fintype.card ι * ε < blockAvg r J e →
        (hasseDeriv I P).coeff J = 0) ∧
      P.logHeight ≤ 2⁻¹ * Real.log |(NumberField.discr K : ℝ)|
        + ((finrank ℚ K : ℝ) / 2 * Fintype.card (Set.powersetCard ι p)
            + finrank ℚ K * Real.log (Fintype.card (Set.powersetCard ι p))
            + finrank ℚ K * Real.log p.factorial
            + 2 * p * #L.matSet * Real.log L.mulFormHeight) * ∑ h, (r h : ℝ) := by
  classical
  have : Nonempty ι := Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt hpn)
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  set m : ℝ := (Fintype.card κ : ℝ) with hm_def
  have hn : 0 < n := by rw [hn_def]; exact_mod_cast Nat.zero_lt_of_lt hpn
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  obtain ⟨S₀, hS₀, hS₀card, hrep⟩ := exists_representatives (L := L) hc0 (Nat.zero_lt_of_lt hpn) hε
  have hm' : 2 * (#S₀ + 1 : ℝ) ≤ exp (m * ε ^ 2 / 2) :=
    (mul_le_mul_of_nonneg_left (by linarith) zero_le_two).trans hm
  obtain ⟨P, hP0, hPh, hPi, hPii, hPht⟩ :=
    exists_auxiliaryPolynomial hL hc0 hp hpn hr S₀ hS₀ hε.le hm' e he hes
  refine ⟨P, hP0, hPh, fun v I J hI hJ ↦ ?_, fun I J hI hJ ↦ ?_, hPht⟩
  · -- (i)
    set f : κ → Set.powersetCard ι p → ℝ := fun _ s ↦ (c.exteriorPower p).vec v s with hf
    have hγ0 := FormExponent.iSup_vec_nonneg (hc0 v)
    rcases hγ0.lt_or_eq with hγ | hγ
    swap
    · -- `c_v = 0`: there is no such `J`
      have hf0 : f = 0 := by
        funext h s
        simp [hf, c.exteriorPower_vec, FormExponent.vec_eq_zero_of_iSup_nonpos (hc0 v) hγ.ge]
      rw [hf0, ← hγ] at hJ
      simp [blockAvg] at hJ
    obtain ⟨v₁, hv₁, hmat, hclose⟩ := hrep v hγ
    have hγ₁ := hS₀ v₁ hv₁
    set A := (L.mat v).compound p with hA
    have hdet : A.det ≠ 0 :=
      det_compound_ne_zero p (det_ne_zero_of_mem_matSet (L.mat_mem_matSet v))
    have hAM : A * A⁻¹ = 1 := mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet)
    have hMA : A⁻¹ * A = 1 := nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hdet)
    have key := coeff_blockSubst_hasseDeriv_eq_zero hAM (∑ t, I t) I rfl (blockSubst A⁻¹ P) J
      fun I' hI' ↦ ?_
    · rwa [blockSubst_blockSubst hMA] at key
    by_cases hmem : J + I' ∈ multiMons (ι := Set.powersetCard ι p) r
    swap
    · exact coeff_blockSubst_eq_zero_of_notMem hPh _ hmem
    rw [hA, ← hmat]
    refine hPi v₁ hv₁ (J + I') ?_
    -- the threshold at `v` …
    have hI'1 : blockAvg r I' 1 = blockAvg r I 1 := blockAvg_one_eq hI'
    have hfb : ∀ h s, |f h s| ≤ n * ⨆ i, c.vec v i := fun h s ↦
      c.abs_exteriorPower_vec_le hp hpn (hc0 v) s
    have hI'f := abs_blockAvg_le r I' hfb
    rw [hI'1] at hI'f
    have hX : 2 * m * n * ε * (⨆ i, c.vec v i) < blockAvg r (J + I') f := by
      rw [blockAvg_add_left]
      have := neg_abs_le (blockAvg r I' f)
      have hγn : 0 ≤ n * ⨆ i, c.vec v i := mul_nonneg hn.le hγ.le
      nlinarith [mul_le_mul_of_nonneg_left hI hγn]
    -- … transported to `v₁`
    set f₁ : κ → Set.powersetCard ι p → ℝ := fun _ s ↦ (c.exteriorPower p).vec v₁ s with hf₁
    set g : κ → Set.powersetCard ι p → ℝ :=
      (⨆ i, c.vec v i)⁻¹ • f - (⨆ i, c.vec v₁ i)⁻¹ • f₁ with hg
    have hgb : ∀ h s, |g h s| ≤ n * ε := fun h s ↦ by
      simpa [hg, hf, hf₁, div_eq_inv_mul] using
        abs_exteriorPower_div_sub_le (p := p) hε.le hclose s
    have hgJ := abs_blockAvg_le r (J + I') hgb
    rw [blockAvg_one_of_mem hr hmem, ← hm_def] at hgJ
    have hsplit : (⨆ i, c.vec v i)⁻¹ • f = g + (⨆ i, c.vec v₁ i)⁻¹ • f₁ := by
      rw [hg, sub_add_cancel]
    have h1 := congrArg (blockAvg r (J + I')) hsplit
    rw [blockAvg_smul, blockAvg_add_right, blockAvg_smul] at h1
    have hX' : 2 * m * n * ε < (⨆ i, c.vec v i)⁻¹ * blockAvg r (J + I') f := by
      rw [← div_eq_inv_mul, lt_div_iff₀ hγ]
      linarith
    have hY : m * n * ε < (⨆ i, c.vec v₁ i)⁻¹ * blockAvg r (J + I') f₁ := by
      have := le_abs_self (blockAvg r (J + I') g)
      linarith
    rw [← div_eq_inv_mul, lt_div_iff₀ hγ₁] at hY
    exact hY.le
  · -- (ii)
    rw [hasseDeriv_coeff, hPii (J + I), mul_zero]
    rw [blockAvg_add_left, ← hm_def, ← hn_def]
    have hIe := abs_blockAvg_le r I he
    have := neg_abs_le (blockAvg r I e)
    nlinarith [mul_le_mul_of_nonneg_left hI hn.le, mul_nonneg (mul_nonneg hm0 hn.le) hε.le]

/-! ### EF13 Lemma 13.4 and (13.29) -/

/-- A product over all places of local bounds `f_v ≤ g_v`. -/
private theorem prod_places_le' {f g : InfinitePlace K → ℝ} {f' g' : FinitePlace K → ℝ}
    (hf : ∀ v, 0 ≤ f v) (hf' : ∀ v, 0 ≤ f' v) (hfs : f'.HasFiniteMulSupport)
    (hgs : g'.HasFiniteMulSupport) (h : ∀ v, f v ≤ g v) (h' : ∀ v, f' v ≤ g' v) :
    (∏ v, f v ^ v.mult) * ∏ᶠ v, f' v ≤ (∏ v, g v ^ v.mult) * ∏ᶠ v, g' v :=
  mul_le_mul (Finset.prod_le_prod₀ (fun v _ ↦ pow_nonneg (hf v) _)
      fun v _ ↦ pow_le_pow_left₀ (hf v) (h v) _)
    (Twist.finprod_le_finprod_of_nonneg hfs hgs hf' h')
    (finprod_nonneg hf') (Finset.prod_nonneg fun v _ ↦ pow_nonneg ((hf v).trans (h v)) _)

omit [NumberField K] [LinearOrder ι] in
private theorem sum_le_of_isMultiHomogeneous {p : ℕ} {r : κ → ℕ}
    {P : MvPolynomial (κ × Set.powersetCard ι p) K} (hP : IsMultiHomogeneous r P)
    (I : κ × Set.powersetCard ι p →₀ ℕ) :
    ∀ ν ∈ (hasseDeriv I P).support, ∑ t, ν t ≤ ∑ h, r h := by
  intro ν hν
  rw [(hP.hasseDeriv I).sum_eq (mem_support_iff.mp hν)]
  exact sum_le_sum fun h _ ↦ Nat.sub_le _ _

variable (L) in
/-- **EF13 Lemma 13.4, (13.11), at an archimedean-type absolute value.** For `P` multihomogeneous
of multidegree `r` and `B` one of the matrices `L^{(v)}`, the coefficients of `∂_I P` read in the
coordinates `B^{∧p}` (EF13's `d_{I,J}(a_P)`) are at most
`#supp P · 2^{Σr} (N max_s |y_s|_w)^{Σr} max_ν |P_ν|_w`, `y = invTuple`. -/
theorem iSup_coeff_blockSubst_hasseDeriv_le {p : ℕ} (hpn : p ≤ Fintype.card ι) {r : κ → ℕ}
    {P : MvPolynomial (κ × Set.powersetCard ι p) K} (hP : IsMultiHomogeneous r P)
    {B : Matrix ι ι K} (hB : B ∈ L.matSet) (w : AbsoluteValue K ℝ)
    (I : κ × Set.powersetCard ι p →₀ ℕ) :
    (⨆ J, w ((blockSubst (B.compound p)⁻¹ (hasseDeriv I P)).coeff J)) ≤
      #P.support * 2 ^ (∑ h, r h) *
        (Fintype.card (Set.powersetCard ι p) * ⨆ s, w (L.invTuple p s)) ^ (∑ h, r h) *
          ⨆ ν, w (P.coeff ν) := by
  have : Nonempty (Set.powersetCard ι p) := Set.powersetCard.nonempty_iff.2 hpn
  set D := ∑ h, r h
  refine (iSup_coeff_blockSubst_le w _ (sum_le_of_isMultiHomogeneous hP I)).trans ?_
  have hsupp : (#(hasseDeriv I P).support : ℝ) ≤ #P.support := by
    exact_mod_cast card_support_hasseDeriv_le I P
  have htd : P.totalDegree ≤ D := Finset.sup_le fun ν hν ↦ by
    rw [Finsupp.sum_fintype _ _ fun _ ↦ rfl]
    exact (hP.sum_eq (mem_support_iff.mp hν)).le
  have hder : (⨆ m, w ((hasseDeriv I P).coeff m)) ≤ 2 ^ D * ⨆ m, w (P.coeff m) :=
    (iSup_coeff_hasseDeriv_le w I P).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ one_le_two htd) (iSup_coeff_nonneg _ _))
  have hy := le_iSup_invTuple (p := p) hB w
  have h0 := iSup_coeff_nonneg (hasseDeriv I P) w
  have h0' := iSup_coeff_nonneg P w
  have hy0 : 0 ≤ (⨆ q : Set.powersetCard ι p × Set.powersetCard ι p,
      w ((B.compound p)⁻¹ q.1 q.2)) ⊔ 1 := zero_le_one.trans le_sup_right
  calc (#(hasseDeriv I P).support : ℝ) * ((⨆ m, w ((hasseDeriv I P).coeff m)) *
        ((Fintype.card (Set.powersetCard ι p) : ℝ) *
          ((⨆ q : Set.powersetCard ι p × Set.powersetCard ι p,
            w ((B.compound p)⁻¹ q.1 q.2)) ⊔ 1)) ^ D)
      ≤ #P.support * ((2 ^ D * ⨆ m, w (P.coeff m)) *
        ((Fintype.card (Set.powersetCard ι p) : ℝ) * ⨆ s, w (L.invTuple p s)) ^ D) := by
        gcongr
    _ = _ := by ring

variable (L) in
/-- **EF13 Lemma 13.4, (13.11), at a nonarchimedean absolute value**: neither the number of
monomials nor the binomial factors appear. -/
theorem iSup_coeff_blockSubst_hasseDeriv_le_of_isNonarchimedean {p : ℕ} {r : κ → ℕ}
    {P : MvPolynomial (κ × Set.powersetCard ι p) K} (hP : IsMultiHomogeneous r P)
    {B : Matrix ι ι K} (hB : B ∈ L.matSet) {w : AbsoluteValue K ℝ} (hw : IsNonarchimedean w)
    (I : κ × Set.powersetCard ι p →₀ ℕ) :
    (⨆ J, w ((blockSubst (B.compound p)⁻¹ (hasseDeriv I P)).coeff J)) ≤
      (⨆ s, w (L.invTuple p s)) ^ (∑ h, r h) * ⨆ ν, w (P.coeff ν) := by
  refine (iSup_coeff_blockSubst_le_of_isNonarchimedean hw _
    (sum_le_of_isMultiHomogeneous hP I)).trans ?_
  have hy := le_iSup_invTuple (p := p) hB w
  have hy0 : 0 ≤ (⨆ q : Set.powersetCard ι p × Set.powersetCard ι p,
      w ((B.compound p)⁻¹ q.1 q.2)) ⊔ 1 := zero_le_one.trans le_sup_right
  rw [mul_comm]
  exact mul_le_mul (pow_le_pow_left₀ hy0 hy _)
    (iSup_coeff_hasseDeriv_le_of_isNonarchimedean hw I P) (iSup_coeff_nonneg _ _)
    (pow_nonneg (hy0.trans hy) _)

variable (L) in
/-- **EF13 (13.29)**: for `P ≠ 0` multihomogeneous of multidegree `r` and any order `I`,
`∏_v max_J |d^{(v)}_{I,J}(a_P)|_v ≤ (#supp P · 2^{Σr} N^{Σr})^{[K:ℚ]} H(P) H(invTuple)^{Σr}`,
relative to `K`. With `mulHeight_invTuple_le` and Lemma 13.5 (iii) this is EF13's
`C_K 2^{6n} H_L^{2R^n Σr}`. -/
theorem prod_iSup_coeff_blockSubst_hasseDeriv_le {p : ℕ} (hpn : p ≤ Fintype.card ι)
    {r : κ → ℕ} {P : MvPolynomial (κ × Set.powersetCard ι p) K} (hP : IsMultiHomogeneous r P)
    (hP0 : P ≠ 0) (I : κ × Set.powersetCard ι p →₀ ℕ) :
    (∏ v : InfinitePlace K,
        (⨆ J, v ((blockSubst ((L.arch v).compound p)⁻¹ (hasseDeriv I P)).coeff J)) ^ v.mult) *
      ∏ᶠ v : FinitePlace K,
        ⨆ J, v ((blockSubst ((L.fin v).compound p)⁻¹ (hasseDeriv I P)).coeff J) ≤
      ((#P.support : ℝ) * 2 ^ (∑ h, r h) * Fintype.card (Set.powersetCard ι p) ^ (∑ h, r h)) ^
          finrank ℚ K * P.mulHeight * Height.mulHeight (L.invTuple p) ^ (∑ h, r h) := by
  classical
  set D := ∑ h, r h
  set N : ℝ := (Fintype.card (Set.powersetCard ι p) : ℝ)
  set C : ℝ := (#P.support : ℝ) * 2 ^ D * N ^ D with hC
  have hC0 : 0 ≤ C := by positivity
  have hRHS0 : 0 ≤ C ^ finrank ℚ K * P.mulHeight * Height.mulHeight (L.invTuple p) ^ D := by
    have := MvPolynomial.mulHeight_pos P
    have := Height.mulHeight_pos (L.invTuple p)
    positivity
  by_cases hΔ : hasseDeriv I P = 0
  · rw [hΔ]
    have hz (B : Matrix (Set.powersetCard ι p) (Set.powersetCard ι p) K) (w : AbsoluteValue K ℝ) :
        (⨆ J, w ((blockSubst B (0 : MvPolynomial (κ × Set.powersetCard ι p) K)).coeff J)) = 0 := by
      simp
    have : (∏ v : InfinitePlace K,
        (⨆ J, v ((blockSubst ((L.arch v).compound p)⁻¹
          (0 : MvPolynomial (κ × Set.powersetCard ι p) K)).coeff J)) ^ v.mult) = 0 := by
      refine prod_eq_zero (mem_univ (Classical.arbitrary _)) ?_
      rw [show (⨆ J, (Classical.arbitrary (InfinitePlace K))
          ((blockSubst ((L.arch (Classical.arbitrary _)).compound p)⁻¹
            (0 : MvPolynomial (κ × Set.powersetCard ι p) K)).coeff J)) = 0 from hz _ _]
      exact zero_pow (Classical.arbitrary (InfinitePlace K)).mult_ne_zero
    rw [this, zero_mul]
    exact hRHS0
  -- the substituted derivatives are nonzero
  have hQ : ∀ B ∈ L.matSet, blockSubst (B.compound p)⁻¹ (hasseDeriv I P) ≠ 0 := by
    intro B hB h
    have hdet : (B.compound p).det ≠ 0 := det_compound_ne_zero p (det_ne_zero_of_mem_matSet hB)
    have hMA : (B.compound p)⁻¹ * B.compound p = 1 :=
      nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
    refine hΔ ?_
    rw [← blockSubst_blockSubst hMA (hasseDeriv I P), h, map_zero]
  set G : Matrix ι ι K → FinitePlace K → ℝ :=
    fun B v ↦ ⨆ J, v ((blockSubst (B.compound p)⁻¹ (hasseDeriv I P)).coeff J) with hG
  have hfs : (fun v : FinitePlace K ↦ G (L.fin v) v).HasFiniteMulSupport := by
    refine (L.matSet.finite_toSet.biUnion fun B hB ↦
      hasFiniteMulSupport_iSup_coeff (hQ B hB)).subset fun v hv ↦ ?_
    refine Set.mem_biUnion (x := L.fin v) (L.fin_mem_matSet v) ?_
    rw [Function.mem_mulSupport] at hv ⊢
    exact hv
  have ha : (fun v : FinitePlace K ↦ ⨆ ν, v (P.coeff ν)).HasFiniteMulSupport :=
    hasFiniteMulSupport_iSup_coeff hP0
  have hb : (fun v : FinitePlace K ↦ ⨆ s, v (L.invTuple p s)).HasFiniteMulSupport :=
    Height.hasFiniteMulSupport_iSup (L.invTuple_ne_zero p)
  have hbD : Function.HasFiniteMulSupport fun v : FinitePlace K ↦
      (⨆ s, v (L.invTuple p s)) ^ D := Function.HasFiniteMulSupport.pow hb D
  refine (prod_places_le' (g := fun v ↦ C * ((⨆ ν, v (P.coeff ν)) * (⨆ s, v (L.invTuple p s)) ^ D))
    (g' := fun v ↦ (⨆ ν, v (P.coeff ν)) * (⨆ s, v (L.invTuple p s)) ^ D)
    (fun v ↦ iSup_coeff_nonneg _ v.1) (fun v ↦ iSup_coeff_nonneg _ v.1) hfs
    (Function.HasFiniteMulSupport.mul ha hbD)
    (fun v ↦ ?_) fun v ↦ ?_).trans_eq ?_
  · have : (⨆ J, v ((blockSubst ((L.arch v).compound p)⁻¹ (hasseDeriv I P)).coeff J)) ≤
        #P.support * 2 ^ D * (N * ⨆ s, v (L.invTuple p s)) ^ D * ⨆ ν, v (P.coeff ν) :=
      iSup_coeff_blockSubst_hasseDeriv_le L hpn hP (L.arch_mem_matSet v) v.1 I
    refine this.trans_eq ?_
    simp only [C, N, mul_pow]
    ring
  · have : (⨆ J, v ((blockSubst ((L.fin v).compound p)⁻¹ (hasseDeriv I P)).coeff J)) ≤
        (⨆ s, v (L.invTuple p s)) ^ D * ⨆ ν, v (P.coeff ν) :=
      iSup_coeff_blockSubst_hasseDeriv_le_of_isNonarchimedean L hP (L.fin_mem_matSet v)
        (Height.AdmissibleAbsValues.isNonarchimedean v.1 v.2) I
    exact this.trans_eq (mul_comm _ _)
  · rw [mulHeight_eq_prod hP0, NumberField.mulHeight_eq (L.invTuple_ne_zero p),
      finprod_mul_distrib ha hbD, ← finprod_pow hb]
    simp only [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
    rw [show ∏ v : InfinitePlace K, ((⨆ s, v (L.invTuple p s)) ^ D) ^ v.mult =
        (∏ v : InfinitePlace K, (⨆ s, v (L.invTuple p s)) ^ v.mult) ^ D by
      rw [← prod_pow]
      exact prod_congr rfl fun v _ ↦ by rw [← pow_mul, ← pow_mul, mul_comm]]
    ring

end FormSystem

end NumberField
