/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import CorvajaZannier2004.PseudoPisot
public import Mathlib.Algebra.Order.Round
public import Mathlib.Order.Filter.AtTopBot.Defs

-- Used only inside proofs.
import CorvajaZannier2004.PisotNearInteger
import CorvajaZannier2004.PisotPowers
import Mathlib.Order.Filter.Cofinite
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-!
# The Appendix of Corvaja–Zannier: "algebraic" cannot be dropped from Theorem 1

There is a real `α > 1` with `‖αⁿ‖ ≤ 2⁻ⁿ` for infinitely many `n` such that no power `α ^ d`,
`d ≥ 1`, is a Pisot number. By Theorem 1 every such `α` is transcendental.

## Main results

* `Real.exists_frequently_not_isPisot`: the Appendix.
* `Real.exists_transcendental_frequently_not_isPisot`: with the closing remark, `α` transcendental.

## Implementation notes

The construction is the paper's: intervals `Iₙ = [aₙ, aₙ + 2^{-Bₙ}]` with `I_{n+1} ⊆ Iₙ^{b_{n+1}}`,
`Bₙ = b₀ ⋯ bₙ`, `(n + 1) ∣ b_{n+1}`, and `a_{n+1} = q + β_{n+1}` for an integer `q`; here
`I₀ = [2, 5/2]` instead of `[2, 3]`, so that every interval has the same shape. The point `α` is in
`⋂ Jₙ`, `Jₙ = {x ∈ [2, 3] | x^{Bₙ} ∈ Iₙ}`, a decreasing sequence of nonempty compact sets; the
paper's `Jₙ = Iₙ^{1/Bₙ}` is the same set, but defined by a preimage no roots are needed.
`βₙ` is `0` for even and `1/3` for odd `n`.

## References

P. Corvaja and U. Zannier, Acta Math. **193** (2004), 175–191, Appendix, p. 11.
-/

@[expose] public section

open Filter Topology

namespace Real

/-- **One step of the construction.** From `I = [a, a + 2^{-B}]`, `a ≥ 2`: an exponent `b ≥ 3`
divisible by `k`, and an integer `q ≥ 2` with `[q + β, q + β + 2^{-Bb}] ⊆ I^b`. -/
private theorem exists_pow_image_superset {a : ℝ} (ha : 2 ≤ a) (B : ℕ) {k : ℕ} (hk : 0 < k) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2) :
    ∃ b : ℕ, k ∣ b ∧ 3 ≤ b ∧ ∃ q : ℤ, 2 ≤ q ∧
      Set.Icc (q + β) (q + β + 1 / 2 ^ (B * b)) ⊆ (· ^ b) '' Set.Icc a (a + 1 / 2 ^ B) := by
  set ε : ℝ := 1 / 2 ^ B with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (3 / ε)
  have hk1 : 1 ≤ k := hk
  set b := k * (N + 3) with hbdef
  have hb3 : 3 ≤ b := by nlinarith
  have hbR : (N : ℝ) + 3 ≤ b := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    rw [hbdef]
    push_cast
    nlinarith
  have hab : a ≤ a ^ b := le_self_pow₀ (by linarith) (by omega)
  refine ⟨b, dvd_mul_right _ _, hb3, ⌊a ^ b⌋ + 1, ?_, ?_⟩
  · have : (1 : ℤ) ≤ ⌊a ^ b⌋ := Int.le_floor.mpr (by push_cast; linarith)
    omega
  intro y hy
  -- `a^b ≤ y ≤ a^b + 3 ≤ (a + ε)^b`
  have hsmall : (1 : ℝ) / 2 ^ (B * b) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hfl := Int.floor_le (a ^ b)
  have hfl' := Int.lt_floor_add_one (a ^ b)
  have hlow : a ^ b ≤ y := by
    have := hy.1
    push_cast at this
    linarith
  have hup : y ≤ a ^ b + 3 := by
    have := hy.2
    push_cast at this
    linarith
  have hbern : a ^ b + 3 ≤ (a + ε) ^ b := by
    have ha0 : 0 < a := by linarith
    have h1 := one_add_mul_le_pow (a := ε / a) (by linarith [show 0 ≤ ε / a by positivity]) b
    have h2 : (a + ε) ^ b = a ^ b * (1 + ε / a) ^ b := by
      rw [← mul_pow]
      congr 1
      field_simp
    have h3 : 3 ≤ b * ε := by
      rw [div_lt_iff₀ hε0] at hN
      nlinarith
    have h4 : a ^ b * (b * (ε / a)) = (a ^ b / a) * (b * ε) := by
      field_simp
    have h5 : 1 ≤ a ^ b / a := by rw [le_div_iff₀ ha0]; linarith
    rw [h2]
    nlinarith [pow_pos ha0 b]
  obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc (by linarith : a ≤ a + ε)
    (continuous_pow b).continuousOn ⟨hlow, hup.trans hbern⟩
  exact ⟨x, hx, hxy⟩

/-- **The sequences of the construction**, for a sequence `βₙ ∈ [0, 1/2]`. -/
private theorem exists_seq (βs : ℕ → ℝ) (hβs0 : ∀ n, 0 ≤ βs n) (hβs : ∀ n, βs n ≤ 1 / 2) :
    ∃ (a : ℕ → ℝ) (B : ℕ → ℕ), a 0 = 2 ∧ B 0 = 1 ∧ (∀ n, 2 ≤ a n) ∧ (∀ n, 0 < B n) ∧
      ∀ n, ∃ b : ℕ, (n + 1) ∣ b ∧ 3 ≤ b ∧ B (n + 1) = B n * b ∧
        (∃ q : ℤ, a (n + 1) = q + βs (n + 1)) ∧
        Set.Icc (a (n + 1)) (a (n + 1) + 1 / 2 ^ B (n + 1)) ⊆
          (· ^ b) '' Set.Icc (a n) (a n + 1 / 2 ^ B n) := by
  choose! b hdvd h3 q hq2 hsub using fun (n : ℕ) (a : ℝ) (ha : 2 ≤ a) (B : ℕ) ↦
    exists_pow_image_superset ha B n.succ_pos (hβs0 (n + 1)) (hβs (n + 1))
  let st : ℕ → ℝ × ℕ := fun n ↦
    Nat.rec (2, 1) (fun n p ↦ (q n p.1 p.2 + βs (n + 1), p.2 * b n p.1 p.2)) n
  have hst : ∀ n, st (n + 1) =
      (q n (st n).1 (st n).2 + βs (n + 1), (st n).2 * b n (st n).1 (st n).2) := fun _ ↦ rfl
  have ha : ∀ n, 2 ≤ (st n).1 := by
    intro n
    induction n with
    | zero => norm_num [st]
    | succ n ih =>
      rw [hst]
      have : (2 : ℝ) ≤ q n (st n).1 (st n).2 := by exact_mod_cast hq2 n _ ih _
      linarith [hβs0 (n + 1)]
  have hB : ∀ n, 0 < (st n).2 := by
    intro n
    induction n with
    | zero => norm_num [st]
    | succ n ih =>
      rw [hst]
      exact Nat.mul_pos ih (by have := h3 n _ (ha n) (st n).2; omega)
  refine ⟨fun n ↦ (st n).1, fun n ↦ (st n).2, rfl, rfl, ha, hB, fun n ↦
    ⟨b n (st n).1 (st n).2, hdvd n _ (ha n) _, h3 n _ (ha n) _, congrArg Prod.snd (hst n),
      ⟨q n (st n).1 (st n).2, congrArg Prod.fst (hst n)⟩, ?_⟩⟩
  exact hsub n _ (ha n) (st n).2

/-- **The Appendix of Corvaja–Zannier** (p. 11): the word "algebraic" cannot be removed from
Theorem 1. There is a real `α > 1` with `‖αⁿ‖ ≤ 2⁻ⁿ` for infinitely many `n` such that no power
`α ^ d`, `d ≥ 1`, is a Pisot number. -/
theorem exists_frequently_not_isPisot :
    ∃ α : ℝ, 1 < α ∧ (∃ᶠ n : ℕ in atTop, |α ^ n - round (α ^ n)| ≤ 1 / 2 ^ n) ∧
      ∀ d, 0 < d → ¬ IsPisot (α ^ d) := by
  classical
  set βs : ℕ → ℝ := fun n ↦ if Even n then 0 else 1 / 3 with hβs
  obtain ⟨a, B, ha0, hB0, ha, hBpos, hstep⟩ := exists_seq βs
    (fun n ↦ by simp only [hβs]; split_ifs <;> norm_num)
    (fun n ↦ by simp only [hβs]; split_ifs <;> norm_num)
  set I : ℕ → Set ℝ := fun n ↦ Set.Icc (a n) (a n + 1 / 2 ^ B n) with hI
  set J : ℕ → Set ℝ := fun n ↦ Set.Icc 2 3 ∩ (· ^ B n) ⁻¹' I n with hJ
  -- `(·)^{Bₙ}` maps `[2, 3]` onto a superset of `Iₙ`
  have hIJ : ∀ n, ∀ z ∈ I n, ∃ x ∈ Set.Icc (2 : ℝ) 3, x ^ B n = z := by
    intro n
    induction n with
    | zero =>
      intro z hz
      simp only [hI, ha0, hB0, pow_one] at hz
      exact ⟨z, ⟨hz.1, by linarith [hz.2]⟩, by rw [hB0, pow_one]⟩
    | succ n ih =>
      intro z hz
      obtain ⟨b, -, -, hBn, -, hsub⟩ := hstep n
      obtain ⟨y, hyI, hy⟩ := hsub hz
      obtain ⟨x, hx, rfl⟩ := ih y hyI
      exact ⟨x, hx, by rw [hBn, pow_mul]; exact hy⟩
  have hJsub : ∀ n, J (n + 1) ⊆ J n := by
    rintro n x ⟨hx23, hxI⟩
    refine ⟨hx23, ?_⟩
    obtain ⟨b, -, hb3, hBn, -, hsub⟩ := hstep n
    obtain ⟨y, hyI, hy⟩ := hsub hxI
    have hy' : y ^ b = (x ^ B n) ^ b := by rw [← pow_mul, ← hBn]; exact hy
    have hy0 : 0 ≤ y := by linarith [hyI.1, ha n]
    have hx0 : 0 ≤ x ^ B n := pow_nonneg (by linarith [hx23.1]) _
    rw [Set.mem_preimage, ← (pow_left_inj₀ hy0 hx0 (by omega)).mp hy']
    exact hyI
  have hJne : ∀ n, (J n).Nonempty := fun n ↦ by
    have hε : (0 : ℝ) < 1 / 2 ^ B n := by positivity
    obtain ⟨x, hx, hxz⟩ := hIJ n (a n) ⟨le_rfl, by linarith⟩
    refine ⟨x, hx, ?_⟩
    rw [Set.mem_preimage, hxz]
    exact ⟨le_rfl, by linarith⟩
  have hJcl : ∀ n, IsClosed (J n) := fun n ↦
    isClosed_Icc.inter (isClosed_Icc.preimage (continuous_pow _))
  obtain ⟨α, hα⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed J hJsub hJne
    (isCompact_Icc.inter_right (isClosed_Icc.preimage (continuous_pow _))) hJcl
  have hαJ : ∀ n, α ∈ J n := Set.mem_iInter.mp hα
  have hα2 : 2 ≤ α := (hαJ 0).1.1
  -- `α^{B_{n+1}} ∈ [q + β_{n+1}, q + β_{n+1} + 2^{-B_{n+1}}]`
  have hpos : ∀ n, ∃ q : ℤ, q + βs (n + 1) ≤ α ^ B (n + 1) ∧
      α ^ B (n + 1) ≤ q + βs (n + 1) + 1 / 2 ^ B (n + 1) := fun n ↦ by
    obtain ⟨b, -, -, -, ⟨q, hq⟩, -⟩ := hstep n
    have := (hαJ (n + 1)).2
    change α ^ B (n + 1) ∈ Set.Icc (a (n + 1)) (a (n + 1) + 1 / 2 ^ B (n + 1)) at this
    rw [hq] at this
    exact ⟨q, this.1, this.2⟩
  -- the growth of `Bₙ`
  have hBsucc : ∀ n, 3 * B n ≤ B (n + 1) := fun n ↦ by
    obtain ⟨b, -, hb3, hBn, -⟩ := hstep n
    rw [hBn]
    nlinarith [hBpos n]
  have hBge : ∀ n, n ≤ B n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih => have := hBsucc n; have := hBpos n; omega
  have hBmono : StrictMono B := strictMono_nat_of_lt_succ fun n ↦ by
    have := hBsucc n; have := hBpos n; omega
  have hBdvd : ∀ m n, m ≤ n → B m ∣ B n := fun m n hmn ↦ by
    induction n, hmn using Nat.le_induction with
    | base => exact dvd_rfl
    | succ n _ ih =>
      obtain ⟨b, -, -, hBn, -⟩ := hstep n
      rw [hBn]
      exact ih.mul_right _
  refine ⟨α, by linarith, ?_, fun d hd hPis ↦ ?_⟩
  · -- the even indices
    rw [Nat.frequently_atTop_iff_infinite]
    have hinj : Function.Injective fun k : ℕ ↦ B (2 * k + 2) :=
      hBmono.injective.comp fun k₁ k₂ h ↦ by
        have : 2 * k₁ + 2 = 2 * k₂ + 2 := h
        omega
    refine (Set.infinite_range_of_injective hinj).mono ?_
    rintro _ ⟨k, rfl⟩
    obtain ⟨q, hq1, hq2⟩ := hpos (2 * k + 1)
    have hβ : βs (2 * k + 1 + 1) = 0 := by
      simp [hβs, show Even (2 * k + 1 + 1) from ⟨k + 1, by ring⟩]
    rw [hβ, add_zero] at hq1 hq2
    change |α ^ B (2 * k + 2) - round (α ^ B (2 * k + 2))| ≤ 1 / 2 ^ B (2 * k + 2)
    refine (round_le _ q).trans ?_
    rw [abs_le]
    constructor <;> linarith
  · -- no power is Pisot: the odd indices
    obtain ⟨M, hM⟩ := eventually_atTop.mp
      (hPis.tendsto_abs_sub_round.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 6)))
    set n := 2 * (d * M + d) with hn
    have hdn : d ∣ B (n + 1) := by
      obtain ⟨b, hdb, -, hBd, -⟩ := hstep (d - 1)
      rw [Nat.sub_add_cancel hd] at hdb hBd
      exact (hdb.trans (Dvd.intro_left _ hBd.symm)).trans (hBdvd d (n + 1) (by omega))
    obtain ⟨c, hc⟩ := hdn
    have hcM : M ≤ c := by
      have h1 := hBge (n + 1)
      rw [hc] at h1
      have h2 : d * M < d * c := by
        have : d * M < n + 1 := by rw [hn]; nlinarith
        omega
      exact (Nat.lt_of_mul_lt_mul_left h2).le
    have h1 := hM c hcM
    rw [← pow_mul, ← hc] at h1
    obtain ⟨q, hq1, hq2⟩ := hpos n
    have hβ : βs (n + 1) = 1 / 3 := by
      simp [hβs, show ¬ Even (n + 1) from Nat.not_even_iff_odd.mpr ⟨d * M + d, by rw [hn]⟩]
    rw [hβ] at hq1 hq2
    have hB3 : 3 ≤ B (n + 1) := by have := hBsucc n; have := hBpos n; omega
    have hsmall : (1 : ℝ) / 2 ^ B (n + 1) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num), one_mul, one_mul]
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ B (n + 1) := pow_le_pow_right₀ (by norm_num) hB3
    have hround : round (α ^ B (n + 1)) = q := by
      rw [round_eq, Int.floor_eq_iff]
      constructor <;> linarith
    rw [hround, abs_lt] at h1
    linarith [h1.2]

/-- **The Appendix with the closing remark**: every such `α` is transcendental, by Theorem 1. -/
theorem exists_transcendental_frequently_not_isPisot :
    ∃ α : ℝ, 1 < α ∧ (∃ᶠ n : ℕ in atTop, |α ^ n - round (α ^ n)| ≤ 1 / 2 ^ n) ∧
      (∀ d, 0 < d → ¬ IsPisot (α ^ d)) ∧ Transcendental ℚ α := by
  obtain ⟨α, h1, hfr, hnP⟩ := exists_frequently_not_isPisot
  refine ⟨α, h1, hfr, hnP, fun halg ↦ ?_⟩
  have hfr' : ∃ᶠ n : ℕ in atTop, |α ^ n - round (α ^ n)| < (3 / 4) ^ n :=
    hfr.mp ((eventually_gt_atTop 0).mono fun n hn hle ↦ hle.trans_lt (by
      rw [one_div, ← inv_pow]
      exact pow_lt_pow_left₀ (by norm_num) (by norm_num) hn.ne'))
  obtain ⟨⟨n, hn, hP⟩, -⟩ :=
    exists_isPisot_pow_of_frequently h1 halg (by norm_num) (by norm_num) hfr'
  exact hnP n hn hP

end Real
