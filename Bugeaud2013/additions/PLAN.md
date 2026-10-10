# additions/: the exponent δ in (6.1) — plan and status

**COMPLETE 2026-10-10**: all 11 files build clean, std3 axioms, `#lint` clean, guards pass;
`Nat.frequently_lt_encard_factors{,_of_lt_quarter,_of_lt_ninth}` in `Delta.lean`. See README.md.
Only open item: lint-style wants `Additions/` (UpperCamelCase) — not renamed (user named the dir).

User request (2026-10-10): "in an additions/ directory add the proofs for the delta bounds
`δ < 1/4` (EF13), `δ < 1/9` (ES02) from outgoing.md". Lean, in `Bugeaud2013/additions/`
(modules `Bugeaud2013.additions.*`, picked up by the lib glob). Nothing committed.

## Target theorem

(6.1): `a_i ≥ 1`, `3 ≤ (minpoly ℚ (contFrac a)).natDegree`, `δ < 1/(a+1)` ⇒ for every `C`,
`∃ᶠ n, ∀ k : ℕ, (Function.factors (fun i ↦ a (i+1)) n).encard = k → C * n * log n ^ δ < k`.
Parametric in the count exponent `a` via `Real.SubspaceBound α a`:
EF13 (`a = 3`, proved: `Real.subspaceBound_three`) ⇒ `δ < 1/4`; ES02 shape (`a = 8 = n+4` at
`n = 4`) via `SubspaceBound.mono` ⇒ `δ < 1/9` (ES02 itself not formalized; its shape is implied
by the proved EF13 count).

## Paper proof (checked by hand this session; refines outgoing.md)

Notation: `v_n = spadeVec a (w-1) (u+v)` = (X1,X2,X3,X4), `H = q_w q_m`, `m = w+u+v = t_n`,
`L1 = α²X1 − α(X2+X3) + X4`, `L2 = αX1 − X2`, `L3 = αX1 − X3`, `L4 = X1`; `T0 = {X2 = X3}`.

0. Combinatorics (BE08 Lemma 6.1 analog): from `p(m) ≤ c m (log m)^δ`: for each ℓ, pigeonhole
   gives a period-`P` segment; re-cut (if `P < m`, use `s = P⌊(m+P)/2P⌋ ≥ m/4`) to get
   `x(p+P)=x(p)` on `[r, r+L)`, `P ≥ L ≥ m/4`, `r+P+L ≤ ℓ`; shift left to minimal `r`
   (⇒ `a_w ≠ a_{w+P}`); `w = 0` ⇒ move one letter (as in `exists_spadeData`).
   Subsequence `ℓ_{k+1} = K(k+2) ℓ_k` ⇒ `t_{k+1} > 2 t_k` and `t_k ≤ K u_k (k+2)^{δ1}` (any δ1>δ).
   For `n ≤ N`: `2^{-u_n} ≤ H_n^{-ε}`, `ε^{-1} ≲ N^{δ1}`.
A. Estimates: `|L1| ≤ 24 H^{-1} 2^{-u}` (abs_spadeL1_le + contDen_sq_div_le), `|L2| ≤ 2q_w/q_m
   ≤ 2√2·2^{-u/2}`, `|L3| ≤ 2q_m/q_w`, `|X_i| ≤ H`; head gap `|X1| ≥ H/(A+2)^3` (mirror formula,
   `a_w ≠ a_m`; w=1 direct); `|L2| ≥ 1/(2H)` (terms of same sign); `L1(v) ≠ 0`.
   Quadratic Liouville (from `exists_pos_le_abs_aeval`, n=2): `|b0+b1α+b2α²| ≥ c (max|b|+1)^{-(d-1)}`.
B. Doubling: `t_{n'} ≥ 2^{n'-n} t_n`, `log H ≍ t` ⇒ `#{n ≥ b : t_n ≤ K(1+t_b)} ≤ log2(2K)+1`.
C. Line: `v_{n'} ∈ ℚ v_n` ⇒ `n' − n = O(1)` (L1 Liouville vs H^{-1}).
D. Plane `P = span(v_a, v_b)`: `D = L1(v_a)L2(v_b) − L1(v_b)L2(v_a)` is quadratic in α (X³ cancels).
   D ≠ 0: Cramer ⇒ `1 ≤ |X1(v_n)| ≲ H_b^{2d+1} 2^{-u_n/2}`; D = 0: `L2 = κL1` on P,
   `|κ| ≲ H_a^d`, vs `|L2(v_n)| ≥ 1/(2H_n)`. Both ⇒ `log H_n ≲ ε^{-1}(1+log H_b)` ⇒ plane has
   `O(log 1/ε)` points.
E. Proper subspace S, points outside T0: first a, b, c independent; `z` = cross product
   (`|z| ≤ 6H_c³`, z ≠ 0 via det with completing basis vector), `Λ = z1+(z2+z3)α+z4α² ≠ 0`
   (v_a ∉ T0). Claim (`abs_claim_le`): `q_{w-1} ≤ 36|z|/|Λ| ≲ |z|^d` ⇒ late points have
   `q_w² ≤ H^{1/4}`. Project (drop coord j, z_j ≠ 0): forms `M_i = z_j c_ik − c_ij z_k` (i=1,2,3),
   **det M = ±z_j² Λ** (sympy-checked, all j) ⇒ independent, `|det| ≥ |Λ|`; exponents
   `(−1, −3/4, 1)`, δ = 3/4 fixed ⇒ O(1) planes (threshold ≲ log|z|) ⇒ each plane D.
   Total `O(log 1/ε)`.
F. T0: y = (X1,X2,X4), forms `α²y1−2αy2+y3, αy1−y2, y1`, exponents `(−1−ε, 0, 1)` ⇒
   `cnt(3, ε/2)` planes, each D.
G. Step 1: ρ = log q_w/log H ∈ [0,1/2], grid k = ⌈8/ε⌉ cells; exponents
   `(−1−ε, 2ρ⁺−1, 1−2ρ⁻, 1)`, sum ≤ −7ε/8, constant 2(A+2)³ ⇒ `k·cnt(4,·)` subspaces.
H. N/2 ≤ k·cnt4·B_S + cnt3·B_P ≲ ε^{-(a+1)} log³ ⇒ contradiction for `(a+1)δ1 < 1`.

## Lean status

* `SubspaceCount.lean` **DONE** (builds clean): `Real.subspaceBound_three` (EF13 ⇒
  `SubspaceBound α 3`), via `isNormalizedSystem_qForms`, `mem_systemSet_qForms`,
  `efSystemThreshold_le_thrConst`, `normLam`/`normExp`.
* **DONE, build clean** (2026-10-10): `Liouville2.lean` (`exists_pos_le_abs_quadVal`,
  `quadVal_ne_zero`), `Points.lean` (`CFPoint`, `Doubling`, `LiouvilleQuad`,
  `rpow_le_of_mem_span_pair`, `Doubling.card_le`, `card_mem_le_of_finrank_le_two`),
  `Forms.lean` (`formCoef`, `projCoef`, `det_projCoef`, `t0Coef`, `crossZ`, `crossZ_ne_zero`),
  `Hyperplanes.lean` (`exists_planes_of_lamCoef_ne_zero`, `exists_planes_t0`),
  `Subspaces.lean` (`PlaneCover`, `card_mem_le_of_ne_top`), `Count.lean`
  (`exists_cover_four`, **`card_le_of_cfPoints`**: ∃ K, family with `CFPoint` (ε), `Doubling`,
  `K ε^-K ≤ log H` ⇒ `#I ≤ K ε^-(a+1) (1+log ε⁻¹)³`).
  `CFPoints.lean` **DONE** (`Nat.cfPoint_spadeVec ha hA hu hur (hr : 2 ≤ r) hrep
  (hne : 1 ≤ j → a (j+1) ≠ a (j+1+r)) (hεu : (q_{j+1} q_{j+1+r})^ε ≤ 2^u)` : CFPoint (contFrac a)
  A ε (spadeVec a j r) (q_{j+1} q_{j+1+r}) q_{j+1}; also `contDen_le_pow` q_n ≤ (A+1)^n,
  `contDen_succ_le`, `head_le`, `le_abs_formL2`).
  `Complexity.lean`, `Asymptotics.lean`, `Delta.lean` **DONE** (sequence `ℓ_k = E^(k+1)(k+1)^(2(k+1))`
  explicit instead of recursive).
* `Complexity.lean` design: `Nat.exists_config (hℓ : 12 ≤ ℓ) (hfin : (factors x ℓ).Finite)
  (hp : ncard ≤ p)`, x = fun k ↦ a (k+1): ∃ j r u, 1 ≤ u ≤ r, 2 ≤ r, ℓ ≤ 4u, j+1+r ≤ 2p+ℓ+1,
  rep (Estimates form), ne. Proof: pigeonhole `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`
  on range (p+1) → x0 < y0 ≤ p, `Function.factor_eq_factor_iff`; s = y0−x0; s ≥ ℓ: (w0=x0, r=s,
  u=ℓ); s < ℓ: c = (ℓ+s)/(2s), P = c s (give omega: 2P ≤ ℓ+s, ℓ+s < 2P+2s, s ≤ P),
  `Function.forall_add_mul_eq_of_forall_add_eq` with L = x0+ℓ+s, (w0=x0, r=u=P). Minimize
  w' := Nat.find (∃ w, ∀ i, w ≤ i → i < w0+u → x(i+r) = x i); w' = 0 ⇒ (j=0, u−1); else
  j = w'−1, ne from Nat.find_min. 0-indexed rep i ↔ 1-indexed m = i+1.
* `Delta.lean` design: theorem `∃ᶠ n, ∀ k : ℕ, encard(factors (a ·+1) n) = k → C n (log n)^δ < k`
  from ha, hdeg (3 ≤ natDegree minpoly), `SubspaceBound α b`, 0 ≤ b, 0 ≤ δ, (b+1)δ < 1.
  By contra: ∀ᶠ ℓ, ncard ≤ C ℓ log^δ ℓ (WLOG C ≥ 1); finite alphabet ⇒ A (as Theorem11);
  Liouville c, D; K from `card_le_of_cfPoints`. `choose` configs J R U for ℓ ≥ L0 (≥ 16);
  ℓ₀ = L0, ℓ_{k+1} = 64(A+1) m_k (m = j+1+r): doubling via log q_m ≥ (m−1)/2·log 2,
  log H ≤ 2m log(A+1). ε(ℓ) = log 2 /(8(2C(log ℓ)^δ+2) log(A+1)) (antitone; H^ε ≤ 2^u since
  m ≤ (2C log^δ+2)ℓ, u ≥ ℓ/4). I = Ico N (2N), ε = ε(ℓ_{2N}). Growth: λ_k = log ℓ_k,
  λ_{k+1} ≤ λ_k + log B + log λ_k (B = 64(A+1)(2C+2)); first λ_k ≤ c(k+1)² (log x ≤ 2√x via
  `Real.log_le_rpow_div`), then λ_N ≤ λ_0 + N(log B + log c + 2 log(N+1)). Threshold: log H_k ≥
  2^k beats poly. Final: N ≤ K ε^-(b+1)(1+log ε⁻¹)³ with ε⁻¹ ≲ (N log N)^δ, θ = δ(b+1) < 1,
  choose η with θ(1+η)+3η < 1, log x ≤ x^η/η ⇒ contradiction for large N.
  Instances: EF13 `subspaceBound_three` (needs IsAlgebraic, from minpoly natDegree ≥ 3) ⇒ δ < 1/4;
  `.mono (3 ≤ 8)` ⇒ δ < 1/9.
* Architecture of the rest (decided 2026-10-10, sympy-checked identities):
  1. `Liouville2.lean`: `quadVal α b ≠ 0` for `b ≠ 0` (deg ≥ 3) and
     `c ≤ |quadVal α b| · (max|bᵢ|)^D` (from `Real.exists_pos_le_abs_aeval`, n = 2, D = d−1).
  2. `Points.lean` (abstract, no CF): `structure CFPoint α A ε (v : Fin 4 → ℤ) (H Q : ℝ)` with
     fields `|vᵢ| ≤ H`, `H ≤ (A+1)⁴|v₀|` (head gap), `1 ≤ Q`, `Q² ≤ H`,
     `|L1| ≤ 24 H^(-1-ε)`, `|L2| ≤ 2Q²/H`, `|L2| ≤ 3H^(-ε/2)`, `Q²/(2H) ≤ |L2|`, `|L3| ≤ 2H/Q²`,
     claim `∀ z : Fin 4 → ℝ, ∑ zᵢvᵢ = 0 → Q·|z0+(z1+z2)α+z3α²| ≤ 12(A+1)²∑|zᵢ|`.
     (0-indexed: L1 = α²v0 − α(v1+v2) + v3, L2 = αv0 − v1, L3 = αv0 − v2, L4 = v0.)
     Family: `H : ℕ → ℝ`, `1 ≤ log H k`, `2 log H k ≤ log H (k+1)` for all k; CFPoint for k ∈ I.
     Doubling count: `#{k ∈ I, b ≤ k, log H k ≤ M(1+log H b)} ≤ log₂(2M)+1`.
     Line: `v_n = λ v_a` ⇒ `H_n ≤ 24 H_a (2H_a)^D / c`. Two-point: `v_a, v_b` indep, `v_n ∈ span`:
     `D = quadVal(b)`, `b0 = x1y3−x3y1, b1 = x2y1−x1y2+x3y0−x0y3, b2 = x0y2−x2y0` (x=v_a,y=v_b);
     D≠0 Cramer with L1,L2 ⇒ `H_n^(ε/2) ≤ 324 H_b²(4H_b²)^D/c`; D=0 ⇒ `L2(v_n)L1(v_a)=L2(v_a)L1(v_n)`
     ⇒ `H_n^ε ≤ 192 H_a(2H_a)^D/c`. Plane count (finrank ≤ 2): a = min, b = min off line ⇒
     `O(log 1/ε)`.
  3. `Hyperplanes.lean`: cross product z (Laplace `det_succ_row_zero`, |z| ≤ 6H³), Λ(z) ≠ 0 off T0,
     projected forms `M i k = z_j•c(i, j.succAbove k) − c(i,j)•z(j.succAbove k)` (i = L1,L2,L3),
     **det = (−1)^j z_j² Λ**; exponents (−1, −3/4, 1), C = 6|z|²(A+1)⁴, B = 2|z|; late ⟺
     log H ≥ K(1+log|z|); a<b<c first independent; T0: y=(v0,v1,v3), forms
     (α²,−2α,1),(α,−1,0),(1,0,0) det 1, exponents (−1−ε,0,1), δ = ε.
  4. `Count.lean`: step 1 (cells from tmp `exists_cell`, forms det −1, C = 24(A+1)⁴, δ = ε/2) ⇒
     `#I ≤ K ε^-(a+1) (1+log ε⁻¹)³` given `log H k ≥ K ε^-K` on I.
  5. `CFPoints.lean`: config (j, r, u, rep, 1 ≤ u ≤ r, ne for w ≥ 2, m = j+1+r ≥ 3) ⇒ CFPoint
     (head gap via q_w = a_w q_{w−1} + q_{w−2}; L2 low via signs of e_ℓ and
     `q_{ℓ+1}e_ℓ − q_ℓe_{ℓ+1} = ±1`; claim via `abs_claim_le` for w ≥ 3, `q_w ≤ (A+1)²` else).
  6. `Complexity.lean`: pigeonhole (x0 < y0 ≤ p(ℓ)), u = ℓ (s ≥ ℓ) or u = r = s⌊(ℓ+s)/2s⌋ ≥ ℓ/3,
     left-shift to minimal w, w = 0 ⇒ move a letter. `ℓ_k = B^k (k!)²`.
  7. `Delta.lean`: contradiction for `(a+1)δ < 1`; instances 1/4 (EF13), 1/9 (ES02 shape).
  Gotchas: `NumberField E` is a Prop (use `have`, not `haveI`); `Finset.single_le_prod` (not ');
  `if_pos` deprecated → `simp only [h, ↓reduceIte]`; ℝ rpow literal `(3:ℝ)` needs
  `show (3:ℝ) = ((3:ℕ):ℝ)`; nlinarith times out with big contexts — give explicit products.
