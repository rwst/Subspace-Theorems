/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SystemSubspaceCount
public import QuantitativeSubspace.GeneralizedRothLemma

/-!
# The quantitative Subspace Theorem with Evertse's Roth lemma

J.-H. Evertse, *An improvement of the quantitative Subspace theorem*, Compositio Math. **101**
(1996), 225–311. Layer Q0 of this roadmap runs Bombieri–Gubler's proof of the Subspace Theorem with
explicit constants (`DiophantineApproximation/PenultimateMinimum.lean` to
`DiophantineApproximation/SystemSubspaceCount.lean`). That proof uses its generalized Roth lemma
(Layer 5.3) only through a `NumberField.SubspaceRoth`: the ratio `σ` by which consecutive
multidegrees fall, and the height cost at which the index along the forms is at most
`(m + 1) η / 2`. This file supplies Evertse's lemma (`MvPolynomial.formIndex_le_of_sq_lt_ratio`)
as one, and so re-runs Q0 with it.

* `NumberField.evertseRatio`: Evertse's ratio `σ = η / (4 (m + 1))`, against Bombieri–Gubler's
  `(η / 4) ^ (2 ^ m)` (`NumberField.subspaceRatio`). The intervals of the interval result then
  have ratio `4 σ⁻¹ = 16 (m + 1) / η` (`NumberField.four_mul_inv_evertseRatio`), polynomial in
  the chain length `m` where Bombieri–Gubler's is doubly exponential in it, so their logarithm,
  which is what the counts see, drops from `2 ^ m log (4 / η)` to `log (16 (m + 1) / η)`.
* `NumberField.four_mul_inv_evertseRatio_le`: the ratio in closed form, `4 σ⁻¹ ≤ 16 T X` with
  `X = 1 + 8 (n + 1) ^ 2 (A + 1) / ε ≥ η⁻¹` and `T = 2 (1 + log (2 (n + 1) s)) X ^ 2 ≥ m + 1`,
  and `NumberField.parametricRatio_evertse_le`, the ratio of the counts of Layer 6.1 and Q0.3.
* `NumberField.penultimateThreshold_evertse_le` and `NumberField.parametricThreshold_evertse_le`:
  the thresholds of Layers 5.6 and 6.1 in closed form, through the parameters
  `NumberField.RothParams.evertseBound`, whose height cost `n T exp (T log (2 T X))`
  (`NumberField.evertse_factor_le`) replaces Bombieri–Gubler's `n (4 / η) ^ (2 ^ m)`: the
  logarithm of the coefficient is polynomial in `(A + 1) / ε`, not exponential.
* `NumberField.RothParams.evertse`: the parameters, with height cost
  `n max(1, 2 (m + 1) / η) ^ (m + 1) (m + 1) (h(P) + (h(ℙ¹) + m + 2) (m + 1) d₀ [K : ℚ])`.
* `NumberField.SubspaceRoth.evertse`: Evertse's Lemma 24 as an input of Steps IV and VI.
* `NumberField.exists_forall_mem_interval_approxSpan_evertse`: Layer 5.6 as an interval result
  with intervals of ratio `16 (m + 1) / η`.
* `NumberField.exists_finset_submodule_of_isNormalizedSystem_evertse`: Q0.3's count for a system
  with Evertse's Roth lemma.

## Implementation notes

⚠ **The hypotheses are those of the Roth lemma, for every number of blocks.** The chain length
`m` is a function of `n`, `|S|`, `ε` and `A`, so the results take a multiprojective height
`H m` on `(ℙ¹)^m` and the Cohen–Macaulay hypothesis `hCM m` for every `m`, as Q1.4 and Q1.5 do
for one. `h(ℙ¹)` enters as `(H (m + 1)).botBound 1`.

⚠ **The chain length is unchanged.** It comes from the auxiliary polynomial of Layer 5.2, not
from the Roth lemma. What Evertse's lemma changes is the ratio of the chain and the height cost,
and with them the thresholds and the logarithm of the ratio in the counts.

This is Layer Q1.6 of the `QuantitativeSubspace` roadmap.
-/

@[expose] public section

open Finset Module MvPolynomial Height IsDedekindDomain

universe u

namespace NumberField

/-- **Evertse's ratio of consecutive multidegrees**, `σ = η / (4 (m + 1))` with
`η = subspaceEta n ε A` and `m = subspaceChainLength n s ε A`. -/
noncomputable def evertseRatio (n s : ℕ) (ε A : ℝ) : ℝ :=
  subspaceEta n ε A / (4 * ((subspaceChainLength n s ε A : ℝ) + 1))

/-- The intervals of the interval result have ratio `4 σ⁻¹ = 16 (m + 1) / η`. -/
theorem four_mul_inv_evertseRatio (n s : ℕ) (ε A : ℝ) :
    4 * (evertseRatio n s ε A)⁻¹
      = 16 * ((subspaceChainLength n s ε A : ℝ) + 1) / subspaceEta n ε A := by
  rw [evertseRatio, inv_div]
  ring

/-- **The parameters of Evertse's generalized Roth lemma**: the ratio `σ = η / (4 (m + 1))` and
the height cost `n max(1, 2 (m + 1) / η) ^ (m + 1) (m + 1) (h(P) + g (m + 1) d₀ [K : ℚ])` with
`g = max(b (m + 1), 0) + m + 2`, where `b k` bounds `h(ℙ¹)` for `k` blocks. -/
noncomputable def RothParams.evertse (b : ℕ → ℝ) : RothParams where
  ratio := evertseRatio
  factor n s ε A := n * max 1 (2 * ((subspaceChainLength n s ε A : ℝ) + 1) / subspaceEta n ε A)
    ^ (subspaceChainLength n s ε A + 1) * ((subspaceChainLength n s ε A : ℝ) + 1)
  shift n s ε A := max (b (subspaceChainLength n s ε A + 1)) 0
    + (subspaceChainLength n s ε A : ℝ) + 2
  ratio_pos hε hA := div_pos (subspaceEta_pos hε hA) (by positivity)
  ratio_le_one {n s ε A} hε hA := by
    have h1 : subspaceEta n ε A ≤ 1 := min_le_left _ _
    have h2 : (1 : ℝ) ≤ 4 * ((subspaceChainLength n s ε A : ℝ) + 1) := by
      have : (0 : ℝ) ≤ subspaceChainLength n s ε A := Nat.cast_nonneg _
      linarith
    exact div_le_one_of_le₀ (h1.trans h2) (by positivity)
  ratio_anti {n s s' ε A} hε hA hs hss := by
    have hm : (subspaceChainLength n s ε A : ℝ) ≤ subspaceChainLength n s' ε A := by
      exact_mod_cast subspaceChainLength_mono hε hA hs hss
    exact div_le_div_of_nonneg_left (subspaceEta_pos hε hA).le (by positivity) (by linarith)
  factor_nonneg _ _ := by positivity
  shift_nonneg _ _ := by positivity

/-- **The height comparison behind Evertse's height cost**, in arithmetic form: with `D ≤ m₁ d₀`,
`1 ≤ D`, `log 2 < 1` and `log D ≤ D - 1`, Evertse's bound
`[K : ℚ] b D + m₁ (h + [K : ℚ] (D log 2 + m₁ log D + m₁))` is less than
`m₁ (h + (b + m₁ + 1) m₁ d₀ [K : ℚ])`. -/
theorem evertse_height_lt {tw b m₁ D d₀ lg₂ lgD h : ℝ} (htw : 0 < tw) (hb : 0 ≤ b)
    (hm : 1 ≤ m₁) (hD1 : 1 ≤ D) (hDd : D ≤ m₁ * d₀) (hlg₂ : lg₂ < 1) (hlgD : lgD ≤ D - 1) :
    tw * b * D + m₁ * (h + tw * (D * lg₂ + m₁ * lgD + m₁))
      < m₁ * (h + (b + m₁ + 1) * m₁ * d₀ * tw) := by
  have hm0 : 0 < m₁ := by linarith
  have h1 : tw * b * D ≤ tw * b * (m₁ * d₀) := mul_le_mul_of_nonneg_left hDd (by positivity)
  have hmd : 0 ≤ m₁ * d₀ := by linarith
  have h2 : tw * b * (m₁ * d₀) ≤ tw * b * (m₁ * d₀) * m₁ :=
    le_mul_of_one_le_right (mul_nonneg (mul_nonneg htw.le hb) hmd) hm
  have h3 : D * lg₂ < D := by nlinarith
  have h4 : m₁ * lgD ≤ m₁ * (D - 1) := mul_le_mul_of_nonneg_left hlgD hm0.le
  have h5 : m₁ * D ≤ m₁ * (m₁ * d₀) := mul_le_mul_of_nonneg_left hDd hm0.le
  have hin : D * lg₂ + m₁ * lgD + m₁ < m₁ * d₀ + m₁ * (m₁ * d₀) := by nlinarith
  have hmul : m₁ * (tw * (D * lg₂ + m₁ * lgD + m₁))
      < m₁ * (tw * (m₁ * d₀ + m₁ * (m₁ * d₀))) :=
    mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hin htw) hm0
  have e1 : m₁ * (h + (b + m₁ + 1) * m₁ * d₀ * tw)
      = m₁ * h + tw * b * (m₁ * d₀) * m₁ + m₁ * (tw * (m₁ * d₀ + m₁ * (m₁ * d₀))) := by ring
  have e2 : tw * b * D + m₁ * (h + tw * (D * lg₂ + m₁ * lgD + m₁))
      = tw * b * D + m₁ * h + m₁ * (tw * (D * lg₂ + m₁ * lgD + m₁)) := by ring
  rw [e1, e2]
  linarith

variable {K : Type*} [Field K] [NumberField K]

/-- **Evertse's generalized Roth lemma** (Evertse 1996, Lemma 24;
`MvPolynomial.formIndex_le_of_sq_lt_ratio`) as an input of Steps IV and VI, with the parameters
`NumberField.RothParams.evertse` at `b m = h(ℙ¹)` for `m` blocks. It takes a multiprojective
height `H m` on `(ℙ¹)^m` and the Cohen–Macaulay hypothesis for every `m`. -/
noncomputable def SubspaceRoth.evertse
    (H : ∀ m : ℕ, MultiprojectiveHeight (K := K) (Prod.fst : Fin m × Fin 2 → Fin m))
    (hCM : ∀ (m : ℕ) (𝔭 : Ideal (MvPolynomial (Fin m × Fin 2) K)) [𝔭.IsPrime],
      IsUnmixedRing (Localization.AtPrime 𝔭)) :
    SubspaceRoth.{u} K where
  toRothParams := RothParams.evertse fun m ↦ (H m).botBound 1
  formIndex_le := by
    intro ι _ _ n s ε A hn hcard hε hA d hd hratio P hP0 hP M hM hheight
    dsimp only [RothParams.evertse, evertseRatio] at hratio hheight
    have hη0 : 0 < subspaceEta n ε A := subspaceEta_pos hε hA
    have hη1 : subspaceEta n ε A ≤ 1 := min_le_left _ _
    generalize subspaceEta n ε A = η at *
    generalize subspaceChainLength n s ε A = m at *
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hd0 : ∀ h, (0 : ℝ) < d h := fun h ↦ by exact_mod_cast hd h
    set θ : ℝ := ((m : ℝ) + 1) * η / 2 with hθdef
    have hθ : 0 < θ := by positivity
    have hσ1 : η / (4 * ((m : ℝ) + 1)) ≤ 1 :=
      div_le_one_of_le₀ (by linarith) (by positivity)
    -- the ratio condition of Evertse's lemma
    have hratio' : ∀ i j : Fin (m + 1), (i : ℕ) + 1 = j →
        ((m + 1 : ℕ) : ℝ) ^ 2 < θ * (d i / d j) := by
      intro i j hij
      have hi : (i : ℕ) < m := by omega
      have h1 := hratio ⟨i, hi⟩
      have hs : (⟨i, hi⟩ : Fin m).succ = j := Fin.ext (by simp [hij])
      have hc : (⟨i, hi⟩ : Fin m).castSucc = i := Fin.ext rfl
      rw [hs, hc] at h1
      rw [mul_div_assoc', lt_div_iff₀ (hd0 j)]
      push_cast
      have h2 : ((m : ℝ) + 1) ^ 2 * d j ≤ ((m : ℝ) + 1) ^ 2 * (η / (4 * ((m : ℝ) + 1)) * d i) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : ((m : ℝ) + 1) ^ 2 * (η / (4 * ((m : ℝ) + 1)) * d i) = θ * d i / 2 := by
        rw [hθdef]
        field_simp
        ring
      have h4 := mul_pos hθ (hd0 i)
      linarith
    have hanti : Antitone d := Fin.antitone_iff_succ_le.2 fun i ↦ by
      have h1 := hratio i
      have h2 : η / (4 * ((m : ℝ) + 1)) * d i.castSucc ≤ d i.castSucc :=
        mul_le_of_le_one_left (Nat.cast_nonneg _) hσ1
      exact_mod_cast h1.trans h2
    -- the height condition of Evertse's lemma
    have hheight' : ∀ h, (n : ℝ) * (max 1 (((m + 1 : ℕ) : ℝ) ^ 2 / θ) ^ (m + 1) *
        (totalWeight K * max ((H (m + 1)).botBound 1) 0 * (∑ i, d i : ℕ) + (m + 1 : ℕ) *
          (P.logHeight + totalWeight K * ((∑ i, d i : ℕ) * Real.log 2 +
            (m + 1 : ℕ) * Real.log (∑ i, d i : ℕ) + (m + 1 : ℕ))))) <
        d h * Height.logHeight (M h) := by
      intro h
      refine lt_of_lt_of_le ?_ (hheight h)
      have hsq : ((m + 1 : ℕ) : ℝ) ^ 2 / θ = 2 * ((m : ℝ) + 1) / η := by
        rw [hθdef]
        push_cast
        field_simp
      rw [hsq]
      set X := max 1 (2 * ((m : ℝ) + 1) / η) ^ (m + 1) with hX
      have hX0 : 0 < X := pow_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) _
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have htw : (0 : ℝ) < totalWeight K := by exact_mod_cast totalWeight_pos K
      have hsum : (∑ i, d i : ℕ) ≤ (m + 1) * d 0 := by
        calc ∑ i, d i ≤ ∑ _i : Fin (m + 1), d 0 :=
              Finset.sum_le_sum fun i _ ↦ hanti (Fin.zero_le i)
          _ = (m + 1) * d 0 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                smul_eq_mul]
      have hsum1 : 1 ≤ (∑ i, d i : ℕ) :=
        (hd 0).trans (Finset.single_le_sum (f := d) (fun _ _ ↦ Nat.zero_le _)
          (Finset.mem_univ 0))
      have hDd : ((∑ i, d i : ℕ) : ℝ) ≤ ((m : ℝ) + 1) * d 0 := by exact_mod_cast hsum
      have hD1 : (1 : ℝ) ≤ ((∑ i, d i : ℕ) : ℝ) := by exact_mod_cast hsum1
      have hlt := evertse_height_lt (h := P.logHeight) htw
        (le_max_right ((H (m + 1)).botBound 1) 0) (by linarith : (1 : ℝ) ≤ (m : ℝ) + 1) hD1
        hDd (lt_trans Real.log_two_lt_d9 (by norm_num))
        (Real.log_le_sub_one_of_pos (by linarith))
      have hmul := mul_lt_mul_of_pos_left hlt (mul_pos hn0 hX0)
      simp only [Nat.cast_add, Nat.cast_one]
      refine lt_of_lt_of_le (b := (n : ℝ) * X * (((m : ℝ) + 1) * (P.logHeight
        + (max ((H (m + 1)).botBound 1) 0 + ((m : ℝ) + 1) + 1) * ((m : ℝ) + 1) * d 0
          * totalWeight K))) ?_ (le_of_eq ?_)
      · refine lt_of_le_of_lt (le_of_eq ?_) hmul
        ring
      · ring
    have h := formIndex_le_of_sq_lt_ratio (H (m + 1)) (hCM (m + 1)) hn hcard hd hanti hθ hratio'
      hP0 hP (fun _ ↦ le_rfl) hM hheight'
    exact h

/-! ### Closed forms -/

/-- **The closed-form bound `X` for `η⁻¹`**: `1 + 8 (n + 1) ^ 2 (A + 1) / ε`. -/
noncomputable def evertseEtaInvBound (n : ℕ) (ε A : ℝ) : ℝ :=
  1 + 8 * ((n : ℝ) + 1) ^ 2 * (A + 1) / ε

/-- **The closed-form bound `T` for the number `m + 1` of blocks**:
`2 (1 + log (2 (n + 1) s)) X ^ 2`. -/
noncomputable def evertseChainBound (n s : ℕ) (ε A : ℝ) : ℝ :=
  2 * (1 + Real.log (2 * ((n : ℝ) + 1) * s)) * evertseEtaInvBound n ε A ^ 2

theorem log_two_mul_add_one_mul_natCast_nonneg (n s : ℕ) :
    0 ≤ Real.log (2 * ((n : ℝ) + 1) * s) := by
  have : (2 * ((n : ℝ) + 1) * s) = ((2 * (n + 1) * s : ℕ) : ℝ) := by push_cast; ring
  rw [this]; exact Real.log_natCast_nonneg _

theorem one_le_evertseEtaInvBound (n : ℕ) {ε A : ℝ} (hε : 0 < ε) (hA : 0 ≤ A) :
    1 ≤ evertseEtaInvBound n ε A := by
  have : 0 ≤ 8 * ((n : ℝ) + 1) ^ 2 * (A + 1) / ε := by positivity
  rw [evertseEtaInvBound]; linarith

theorem two_le_evertseChainBound (n s : ℕ) {ε A : ℝ} (hε : 0 < ε) (hA : 0 ≤ A) :
    2 ≤ evertseChainBound n s ε A := by
  have hX := one_le_evertseEtaInvBound n hε hA
  have hℓ := log_two_mul_add_one_mul_natCast_nonneg n s
  have hX2 : 1 ≤ evertseEtaInvBound n ε A ^ 2 := one_le_pow₀ hX
  rw [evertseChainBound]; nlinarith

/-- `η⁻¹ ≤ X`. -/
theorem inv_subspaceEta_le (n : ℕ) {ε A : ℝ} (hε : 0 < ε) (hA : 0 ≤ A) :
    (subspaceEta n ε A)⁻¹ ≤ evertseEtaInvBound n ε A := by
  have hX : 0 ≤ 8 * ((n : ℝ) + 1) ^ 2 * (A + 1) / ε := by positivity
  rw [subspaceEta, evertseEtaInvBound]
  rcases le_total 1 (ε / (8 * ((n : ℝ) + 1) ^ 2 * (A + 1))) with h | h
  · rw [min_eq_left h, inv_one]; linarith
  · rw [min_eq_right h, inv_div]; linarith

/-- The chain length in closed form: `m + 1 ≤ T`. -/
theorem subspaceChainLength_add_one_le (n s : ℕ) {ε A : ℝ} (hε : 0 < ε) (hA : 0 ≤ A) :
    (subspaceChainLength n s ε A : ℝ) + 1 ≤ evertseChainBound n s ε A := by
  have hη : 0 < subspaceEta n ε A := subspaceEta_pos hε hA
  have hη1 : subspaceEta n ε A ≤ 1 := min_le_left _ _
  have hI := inv_subspaceEta_le n hε hA
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hℓ := log_two_mul_add_one_mul_natCast_nonneg n s
  rw [subspaceChainLength, evertseChainBound]
  generalize subspaceEta n ε A = η at *
  generalize Real.log (2 * ((n : ℝ) + 1) * s) = ℓ at *
  generalize evertseEtaInvBound n ε A = X at *
  have hI1 : 1 ≤ η⁻¹ := (one_le_inv₀ hη).2 hη1
  have hI2 : η⁻¹ ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by linarith) hI 2
  have hm := Nat.ceil_lt_add_one (show 0 ≤ 4 * ℓ / (((n : ℝ) + 1) * ((n : ℝ) + 2) * η ^ 2) by
    positivity)
  have hfrac : 4 * ℓ / (((n : ℝ) + 1) * ((n : ℝ) + 2) * η ^ 2) ≤ 2 * ℓ * η⁻¹ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    calc 4 * ℓ ≤ 2 * ℓ * (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
          nlinarith [mul_nonneg hℓ (by positivity : (0 : ℝ) ≤ 3 * n + n ^ 2)]
      _ = 2 * ℓ * η⁻¹ ^ 2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * η ^ 2) := by field_simp
  have hX1 : 1 ≤ X ^ 2 := le_trans (one_le_pow₀ hI1) hI2
  nlinarith

/-- **Evertse's interval ratio in closed form**: `4 σ⁻¹ ≤ 16 T X`, i.e.
`4 σ⁻¹ ≤ 32 (1 + log (2 (n + 1) s)) (1 + 8 (n + 1) ^ 2 (A + 1) / ε) ^ 3`, so its logarithm is
`O(log (n s (A + 1) / ε))`, where Bombieri–Gubler's is `2 ^ m log (4 / η)` with `m` itself of
order `n ^ 2 (A + 1) ^ 2 log (n s) / ε ^ 2`. -/
theorem four_mul_inv_evertseRatio_le (n s : ℕ) {ε A : ℝ} (hε : 0 < ε) (hA : 0 ≤ A) :
    4 * (evertseRatio n s ε A)⁻¹ ≤ 16 * evertseChainBound n s ε A * evertseEtaInvBound n ε A := by
  have hm := subspaceChainLength_add_one_le n s hε hA
  have hi := inv_subspaceEta_le n hε hA
  have hI : 0 ≤ (subspaceEta n ε A)⁻¹ := inv_nonneg.2 (subspaceEta_pos hε hA).le
  have hT := two_le_evertseChainBound n s hε hA
  rw [four_mul_inv_evertseRatio, div_eq_mul_inv]
  gcongr

/-- The ratio of one step of Layer 6.1 with Evertse's Roth lemma, in closed form in the
parameters `δ = parametricDelta N ε` and `A_p = parametricWedgeAbsWeight N d p ε A` of the grid
system in `⋀^p`. -/
theorem parametricStepRatio_evertse_le (b : ℕ → ℝ) {N : ℕ} (d s p : ℕ) (hN : 0 < N) {ε A : ℝ}
    (hε : 0 < ε) (hA : 0 ≤ A) :
    parametricStepRatio (RothParams.evertse b) N d s p ε A
      ≤ 16 * evertseChainBound (N.choose p - 1) s (parametricDelta N ε)
          (parametricWedgeAbsWeight N d p ε A)
        * evertseEtaInvBound (N.choose p - 1) (parametricDelta N ε)
          (parametricWedgeAbsWeight N d p ε A) :=
  four_mul_inv_evertseRatio_le _ s (parametricDelta_pos hN hε)
    (parametricWedgeAbsWeight_nonneg N d p hε.le hA)

/-- The ratio `ρ` whose logarithm enters the counts of Layer 6.1 and Q0.3
(`NumberField.parametricRatio`), with Evertse's Roth lemma, in closed form step by step. -/
theorem parametricRatio_evertse_le (b : ℕ → ℝ) {N : ℕ} (d s : ℕ) (hN : 0 < N) {ε A : ℝ}
    (hε : 0 < ε) (hA : 0 ≤ A) :
    parametricRatio (RothParams.evertse b) N d s ε A
      ≤ ∑ p ∈ Finset.range N, 16 * evertseChainBound (N.choose p - 1) s (parametricDelta N ε)
          (parametricWedgeAbsWeight N d p ε A)
        * evertseEtaInvBound (N.choose p - 1) (parametricDelta N ε)
          (parametricWedgeAbsWeight N d p ε A) :=
  Finset.sum_le_sum fun p _ ↦ parametricStepRatio_evertse_le b d s p hN hε hA

/-- **Closed-form parameters dominating Evertse's**: the same ratio, height cost
`n T exp (T log (2 T X))` and shift `max(β, 0) + T + 1`, where `β` bounds `h(ℙ¹)`. They are not
the parameters of a Roth lemma; they bound the thresholds of `NumberField.RothParams.evertse`
through the monotonicity of the coefficients (`NumberField.parametricCoeff_mono`). -/
noncomputable def RothParams.evertseBound (β : ℝ) : RothParams where
  ratio := evertseRatio
  factor n s ε A := n * evertseChainBound n s ε A
    * Real.exp (evertseChainBound n s ε A
      * Real.log (2 * evertseChainBound n s ε A * evertseEtaInvBound n ε A))
  shift n s ε A := max β 0 + evertseChainBound n s ε A + 1
  ratio_pos := (RothParams.evertse 0).ratio_pos
  ratio_le_one := (RothParams.evertse 0).ratio_le_one
  ratio_anti := (RothParams.evertse 0).ratio_anti
  factor_nonneg {n s ε A} hε hA := by
    have := two_le_evertseChainBound n s hε hA
    positivity
  shift_nonneg {n s ε A} hε hA := by
    have := two_le_evertseChainBound n s hε hA
    positivity

/-- **Evertse's height cost in closed form**: `F ≤ n T exp (T log (2 T X))`, against
Bombieri–Gubler's `n (4 / η) ^ (2 ^ m)`. -/
theorem evertse_factor_le (b : ℕ → ℝ) (β : ℝ) (n s : ℕ) {ε A : ℝ} (hε : 0 < ε) (hA : 0 ≤ A) :
    (RothParams.evertse b).factor n s ε A ≤ (RothParams.evertseBound β).factor n s ε A := by
  have hη := subspaceEta_pos (n := n) hε hA
  have hη1 : subspaceEta n ε A ≤ 1 := min_le_left _ _
  have hI := inv_subspaceEta_le n hε hA
  have hM := subspaceChainLength_add_one_le n s hε hA
  have hT := two_le_evertseChainBound n s hε hA
  have hX := one_le_evertseEtaInvBound n hε hA
  simp only [RothParams.evertse, RothParams.evertseBound]
  generalize evertseChainBound n s ε A = T at *
  generalize evertseEtaInvBound n ε A = X at *
  generalize subspaceChainLength n s ε A = m at *
  generalize subspaceEta n ε A = η at *
  have hI1 : 1 ≤ η⁻¹ := (one_le_inv₀ hη).2 hη1
  have hY1 : 1 ≤ 2 * T * X := by nlinarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hbase : max 1 (2 * ((m : ℝ) + 1) / η) ≤ 2 * T * X := by
    refine max_le hY1 ?_
    rw [div_eq_mul_inv]
    have := mul_le_mul hM hI (by positivity) (by linarith)
    nlinarith
  have hmax0 : 0 ≤ max 1 (2 * ((m : ℝ) + 1) / η) := zero_le_one.trans (le_max_left _ _)
  have hpow : max 1 (2 * ((m : ℝ) + 1) / η) ^ (m + 1) ≤ Real.exp (T * Real.log (2 * T * X)) :=
    calc _ ≤ (2 * T * X) ^ (m + 1) := pow_le_pow_left₀ hmax0 hbase _
      _ = Real.exp (((m + 1 : ℕ) : ℝ) * Real.log (2 * T * X)) := by
          rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
      _ ≤ _ := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by push_cast; exact hM)
          (Real.log_nonneg hY1))
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (n : ℝ) * max 1 (2 * ((m : ℝ) + 1) / η) ^ (m + 1) * ((m : ℝ) + 1)
      ≤ n * Real.exp (T * Real.log (2 * T * X)) * T := by gcongr
    _ = _ := by ring

/-- Evertse's shift in closed form: `g ≤ max(β, 0) + T + 1` when `β` bounds `h(ℙ¹)`. -/
theorem evertse_shift_le {b : ℕ → ℝ} {β : ℝ} (hb : ∀ k, b k ≤ β) (n s : ℕ) {ε A : ℝ}
    (hε : 0 < ε) (hA : 0 ≤ A) :
    (RothParams.evertse b).shift n s ε A ≤ (RothParams.evertseBound β).shift n s ε A := by
  have hM := subspaceChainLength_add_one_le n s hε hA
  have := max_le_max_right 0 (hb (subspaceChainLength n s ε A + 1))
  simp only [RothParams.evertse, RothParams.evertseBound]
  linarith

variable {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι]

/-- **The threshold of Layer 5.6 with Evertse's Roth lemma, in closed form** (Q1.6): at most
`penultimateCoeff Λ` for the parameters `NumberField.RothParams.evertseBound`, whose height cost
`n T exp (T log (2 T X))` replaces Bombieri–Gubler's `n (4 / η) ^ (2 ^ m)`. Here `β` bounds
`h(ℙ¹)`, `X = 1 + 8 (n + 1) ^ 2 (A + 1) / ε` and `T = 2 (1 + log (2 (n + 1) s)) X ^ 2`. -/
theorem penultimateThreshold_evertse_le {b : ℕ → ℝ} {β : ℝ} (hb : ∀ k, b k ≤ β)
    {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {n : ℕ} (hn : n ≤ Fintype.card ι)
    {ε : ℝ} (hε : 0 < ε) {A : ℝ} (hA : 0 ≤ A) :
    penultimateThreshold Sfin L (RothParams.evertse b) n ε A
      ≤ penultimateCoeff (RothParams.evertseBound β) (finrank ℚ K) (Fintype.card ι)
        (Fintype.card (InfinitePlace K)) #Sfin n ε A * thresholdScale Sfin L :=
  (penultimateThreshold_le _ hLInf hLFin hn hε hA).trans <| mul_le_mul_of_nonneg_right
    (penultimateCoeff_mono _ _ _ _ _ hε hA (evertse_factor_le b β _ _ hε hA)
      (evertse_shift_le hb _ _ hε hA)) (thresholdScale_nonneg Sfin L)

omit [LinearOrder ι] in
/-- **The threshold of Layer 6.1 with Evertse's Roth lemma, in closed form** (Q1.6):
`parametricThreshold ≤ a Λ` with `a = parametricCoeff` for the parameters
`NumberField.RothParams.evertseBound`, where `β` bounds `h(ℙ¹)`. -/
theorem parametricThreshold_evertse_le {b : ℕ → ℝ} {β : ℝ} (hb : ∀ k, b k ≤ β)
    {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {ε : ℝ} (hε : 0 < ε) {A : ℝ}
    (hA : 0 ≤ A) :
    parametricThreshold Sfin L (RothParams.evertse b) ε A
      ≤ parametricCoeff (RothParams.evertseBound β) (finrank ℚ K) (Fintype.card ι)
        (Fintype.card (InfinitePlace K)) #Sfin ε A * thresholdScale Sfin L := by
  have h := parametricThreshold_le (RothParams.evertse b) hLInf hLFin hε hA
  rw [thresholdScale_congr _ ‹DecidableEq ι›] at h
  exact h.trans <| mul_le_mul_of_nonneg_right
    (parametricCoeff_mono _ _ _ _ Fintype.card_pos hε hA
      (fun n s _ _ hε hA ↦ evertse_factor_le b β n s hε hA)
      (fun n s _ _ hε hA ↦ evertse_shift_le hb n s hε hA)) (thresholdScale_nonneg Sfin L)

/-- **Layer 5.6 as an interval result, with Evertse's Roth lemma** (Q1.6). As
`NumberField.exists_forall_mem_interval_approxSpan`, with the same number `m` of intervals, but of
ratio `16 (m + 1) / η` in place of `4 (4 / η) ^ (2 ^ m)`. -/
theorem exists_forall_mem_interval_approxSpan_evertse
    (H : ∀ m : ℕ, MultiprojectiveHeight (K := K) (Prod.fst : Fin m × Fin 2 → Fin m))
    (hCM : ∀ (m : ℕ) (𝔭 : Ideal (MvPolynomial (Fin m × Fin 2) K)) [𝔭.IsPrime],
      IsUnmixedRing (Localization.AtPrime 𝔭))
    {n : ℕ} (hn : 1 ≤ n) (hcard : Fintype.card ι = n + 1) {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {cf : AbsoluteValue K ℝ → ι → ℝ}
    (hLinf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLfin : ∀ w ∈ Sfin, LinearIndependent K (L w.1))
    {ε : ℝ} (hε : 0 < ε) (hweight : approxWeight Sfin cf ≤ -ε / 2) {A : ℝ}
    (hA : approxAbsWeight Sfin cf ≤ A) :
    ∃ (𝒲 : Set (Submodule K (ι → K))) (Q₀ : ℝ), 𝒲.Finite ∧
      𝒲.ncard ≤ 2 ^ ((n + 1) * (Fintype.card (InfinitePlace K) + Sfin.card)) ∧ 0 < Q₀ ∧
      Q₀ = penultimateThreshold Sfin L (RothParams.evertse fun m ↦ (H m).botBound 1) n ε A ∧
      ∀ Q₀' : ℝ, Q₀ ≤ Q₀' →
        ∃ k ≤ subspaceChainLength n (Fintype.card (InfinitePlace K) + Sfin.card) ε A,
        ∃ t : Fin k → ℝ, (∀ i, Q₀' ≤ t i) ∧
        ∀ Q : ℝ, 1 < Q → Q₀' ≤ Real.log Q →
          Module.finrank K (approxSpan Sfin L cf Q) = n → approxSpan Sfin L cf Q ∉ 𝒲 →
          ∃ i, t i ≤ Real.log Q ∧ Real.log Q
            < 16 * ((subspaceChainLength n (Fintype.card (InfinitePlace K) + Sfin.card) ε A
                : ℝ) + 1) / subspaceEta n ε A * t i := by
  obtain ⟨𝒲, Q₀, h1, h2, h3, h4, h5⟩ := exists_forall_mem_interval_approxSpan
    (SubspaceRoth.evertse.{u} H hCM) hn hcard hLinf hLfin hε hweight hA
  refine ⟨𝒲, Q₀, h1, h2, h3, h4, fun Q₀' hQ₀' ↦ ?_⟩
  obtain ⟨k, hk, t, ht, h⟩ := h5 Q₀' hQ₀'
  refine ⟨k, hk, t, ht, fun Q hQ1 hQ hrank hnot ↦ ?_⟩
  obtain ⟨i, hi1, hi2⟩ := h Q hQ1 hQ hrank hnot
  refine ⟨i, hi1, ?_⟩
  rwa [← four_mul_inv_evertseRatio]

omit [DecidableEq ι] [LinearOrder ι] [Nonempty ι] in
open scoped Classical in
/-- **The quantitative Subspace Theorem for a system, with Evertse's Roth lemma** (Q1.6): Q0.3's
count (`NumberField.exists_finset_submodule_of_isNormalizedSystem`) run with
`NumberField.SubspaceRoth.evertse` over the Galois extension `E` that carries the forms. -/
theorem exists_finset_submodule_of_isNormalizedSystem_evertse {E : Type*} [Field E]
    [NumberField E] [Algebra K E] [IsGalois K E]
    (H : ∀ m : ℕ, MultiprojectiveHeight (K := E) (Prod.fst : Fin m × Fin 2 → Fin m))
    (hCM : ∀ (m : ℕ) (𝔭 : Ideal (MvPolynomial (Fin m × Fin 2) E)) [𝔭.IsPrime],
      IsUnmixedRing (Localization.AtPrime 𝔭))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {Hc : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c Hc D R δ) :
    ∃ T : Finset (Submodule K (ι → K)),
      (#T : ℝ) ≤ δ⁻¹ * ((10 ^ 3 * Fintype.card ι) ^ (Fintype.card ι * finrank ℚ K) +
          4 * Fintype.card ι * Real.log (Real.log (4 * Hc))) +
        (1 + Real.log (systemMiddleRatio (finrank ℚ K) (Fintype.card ι) Hc δ
            (systemThreshold E S w L (RothParams.evertse fun m ↦ (H m).botBound 1) Hc δ)) /
              Real.log (1 + δ / (2 * Fintype.card ι))) +
        systemLargeCount (RothParams.evertse fun m ↦ (H m).botBound 1) (Fintype.card ι)
          (finrank ℚ E) (finrank K E) (Fintype.card (InfinitePlace K) + #S) #S δ ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∀ x ∈ systemSet S w L C c, ∃ U ∈ T, x ∈ U :=
  exists_finset_submodule_of_isNormalizedSystem (SubspaceRoth.evertse.{u} H hCM) S w hwInf hwFin
    hN

end NumberField
