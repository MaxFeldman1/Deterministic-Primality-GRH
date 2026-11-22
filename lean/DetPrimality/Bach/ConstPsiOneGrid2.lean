import Mathlib
import DetPrimality.Bach.ConstPsiOneGrid

/-!
# Near-exact lower bounds for `ψ₁(x)` on a grid, `1536 < x ≤ 6000`

Continuation of `ConstPsiOneGrid.lean` (`256 < x ≤ 1536`).  As there, for a natural `K < x`

  `x ψ₁(x) ≥ ∑_{k<K} ψ(k) + (x - K) ψ(K)`   (`psiOneGrid_mul_ge`).

For `K` up to `6000` the product `∏_{k<K} lcm(1..k)` used in `ConstPsiOneGrid.lean` has about
`2.6 · 10⁷` bits, too expensive to recompute in the kernel for every grid point (and the
non-tail-recursive `lcmProd` hits the kernel recursion limit).  Instead `psiAcc K = (L, P, E)` is
computed by a tail-recursive loop (`psiLoop`) keeping a *floating-point* product rounded down:
`L = lcm(1..K)` exactly and `P · 2^E ≤ ∏_{k<K} lcm(1..k)`, with `P < 2^9216 · L` (relative rounding
error `< 2^-500` per step).  A certificate

  `e ≤ E ∧ 2^m ≤ P⁸ ∧ 2^B ≤ L⁸`   (`decide +kernel`, well under a second per grid point)

gives `8 ∑_{k<K} ψ(k) ≥ (8 e + m) log 2`, `8 ψ(K) ≥ B log 2`, hence

  `ψ₁(x) ≥ a_K - c_K / x`  for all `x > K`   (`psiOne_lower_grid2_K`),

with `a_K ≈ ψ(K)`, `c_K ≈ K ψ(K) - ∑_{k<K} ψ(k)`.  Grid: `K = 1536, 1552, …, 5984`.
Combined: `psiOne_lower_grid2` (`ψ₁(x) ≥ x/2 - 2.9` on `(1536, 6000]`; the true minimum of
`ψ₁(x) - x/2` on this range is `≈ -2.826`, and the cell bounds `a_K - c_K/x` are within `0.21`
(relative `2.5 · 10⁻⁴`) of the true `ψ₁`).

This file is generated (generator: `gen2.py`, reproduced in the comment at the end of the file);
the generic lemmas are at the top.
-/

namespace DetPrimality.Bach

/-- Truncation threshold for `psiLoop`. -/
def psiAccT : ℕ := 2 ^ 9216

/-- One-pass floating-point accumulation: starting from `(n, L, P, E)`, do `m` steps of
`(n, L, P, E) ↦ (n + 1, lcm L (n + 1), P · L, E)`, where the mantissa `P · L` is shifted right by
`8704` bits (and `E` increased by `8704`) whenever it reaches `2^9216`. -/
def psiLoop : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ
  | 0, _, L, P, E => (L, P, E)
  | m + 1, n, L, P, E =>
    cond (Nat.ble (psiAccT + E) (P * L + E))
      (psiLoop m (n + 1) (Nat.lcm L (n + 1)) ((P * L) >>> 8704) (E + 8704))
      (psiLoop m (n + 1) (Nat.lcm L (n + 1)) (P * L) E)

/-- `psiAcc n = (lcm(1..n), P, E)` with `P · 2^E ≤ ∏_{k<n} lcm(1..k)`. -/
def psiAcc (n : ℕ) : ℕ × ℕ × ℕ := psiLoop n 0 1 1 0


theorem psiAcc_shift_le (Q s E : ℕ) : (Q >>> s) * 2 ^ (E + s) ≤ Q * 2 ^ E := by
  rw [Nat.shiftRight_eq_div_pow, pow_add, ← mul_assoc, mul_right_comm]
  exact Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)

theorem psiLoop_spec (m : ℕ) : ∀ n L P E : ℕ, L = Nat.lcmUpto n →
    P * 2 ^ E ≤ ∏ k ∈ Finset.range n, Nat.lcmUpto k →
    (psiLoop m n L P E).1 = Nat.lcmUpto (n + m) ∧
      (psiLoop m n L P E).2.1 * 2 ^ (psiLoop m n L P E).2.2
        ≤ ∏ k ∈ Finset.range (n + m), Nat.lcmUpto k := by
  induction m with
  | zero => intro n L P E hL hP; exact ⟨hL, hP⟩
  | succ m ih =>
    intro n L P E hL hP
    have hL' : Nat.lcm L (n + 1) = Nat.lcmUpto (n + 1) := by rw [hL, lcmUpto_succ']
    have hPL : P * L * 2 ^ E ≤ ∏ k ∈ Finset.range (n + 1), Nat.lcmUpto k := by
      rw [Finset.prod_range_succ, ← hL]
      calc P * L * 2 ^ E = P * 2 ^ E * L := by ring
        _ ≤ _ := Nat.mul_le_mul_right L hP
    have hn : n + (m + 1) = n + 1 + m := by omega
    rw [hn]
    unfold psiLoop
    cases Nat.ble (psiAccT + E) (P * L + E) with
    | false => exact ih (n + 1) _ _ _ hL' hPL
    | true =>
      refine ih (n + 1) _ _ _ hL' (le_trans ?_ hPL)
      exact psiAcc_shift_le _ _ _

theorem psiAcc_fst (n : ℕ) : (psiAcc n).1 = Nat.lcmUpto n := by
  have h := (psiLoop_spec n 0 1 1 0 lcmUpto_zero'.symm (by simp)).1
  simpa [psiAcc] using h

theorem psiAcc_snd (n : ℕ) :
    (psiAcc n).2.1 * 2 ^ (psiAcc n).2.2 ≤ ∏ k ∈ Finset.range n, Nat.lcmUpto k := by
  have h := (psiLoop_spec n 0 1 1 0 lcmUpto_zero'.symm (by simp)).2
  simpa [psiAcc] using h

/-- `B log 2 ≤ 8 ψ(K)` if `2^B ≤ lcm(1..K)⁸`. -/
theorem psiAcc_fst_le {K B : ℕ} (hB : 2 ^ B ≤ (psiAcc K).1 ^ 8) :
    (B : ℝ) * Real.log 2 ≤ 8 * Chebyshev.psi (K : ℝ) := by
  have hpos : 0 < (psiAcc K).1 := by rw [psiAcc_fst]; exact Nat.lcmUpto_pos K
  have h3 : (8 : ℝ) * Chebyshev.psi (K : ℝ) = Real.log (((psiAcc K).1 : ℝ) ^ 8) := by
    rw [Chebyshev.psi_eq_log_lcmUpto, ← psiAcc_fst, Real.log_pow]; norm_num
  rw [h3, ← Real.log_pow]
  exact Real.log_le_log (by positivity) (by exact_mod_cast hB)

/-- `(8 e + m) log 2 ≤ 8 ∑_{k<K} ψ(k)` if `e ≤ E` and `2^m ≤ P⁸`, where `psiAcc K = (_, P, E)`. -/
theorem psiAcc_snd_le {K e m : ℕ} (he : e ≤ (psiAcc K).2.2) (hm : 2 ^ m ≤ (psiAcc K).2.1 ^ 8) :
    ((8 * e + m : ℕ) : ℝ) * Real.log 2 ≤ 8 * ∑ k ∈ Finset.range K, Chebyshev.psi (k : ℝ) := by
  have h1 : 2 ^ (8 * e + m) ≤ (∏ k ∈ Finset.range K, Nat.lcmUpto k) ^ 8 := by
    calc 2 ^ (8 * e + m) = 2 ^ m * (2 ^ e) ^ 8 := by rw [pow_add, pow_mul, mul_comm, pow_right_comm]
      _ ≤ (psiAcc K).2.1 ^ 8 * (2 ^ (psiAcc K).2.2) ^ 8 :=
          Nat.mul_le_mul hm (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) he) 8)
      _ = ((psiAcc K).2.1 * 2 ^ (psiAcc K).2.2) ^ 8 := (mul_pow _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_left (psiAcc_snd K) 8
  have hprod : 0 < ∏ k ∈ Finset.range K, Nat.lcmUpto k :=
    Finset.prod_pos fun k _ => Nat.lcmUpto_pos k
  have h2 : (8 : ℝ) * ∑ k ∈ Finset.range K, Chebyshev.psi (k : ℝ)
      = Real.log (((∏ k ∈ Finset.range K, Nat.lcmUpto k : ℕ) : ℝ) ^ 8) := by
    rw [Real.log_pow, Nat.cast_prod,
      Real.log_prod (fun k _ => by exact_mod_cast (Nat.lcmUpto_pos k).ne')]
    norm_num
    exact Finset.sum_congr rfl fun k _ => Chebyshev.psi_eq_log_lcmUpto k
  rw [h2, ← Real.log_pow]
  exact Real.log_le_log (by positivity) (by exact_mod_cast h1)

/-- Rational form: `a x - c ≤ x ψ₁(x)` for `x > K`, given a certificate
`e ≤ E`, `2^m ≤ P⁸`, `2^B ≤ L⁸` (`psiAcc K = (L, P, E)`) with `a ≤ 0.6931471803 · B/8` and
`0.6931471803 · (K B - (8 e + m))/8 ≤ c`. -/
theorem psiOneGrid2_mul {K e m B : ℕ} (he : e ≤ (psiAcc K).2.2)
    (hm : 2 ^ m ≤ (psiAcc K).2.1 ^ 8) (hB : 2 ^ B ≤ (psiAcc K).1 ^ 8) {a c : ℝ}
    (ha : a ≤ 0.6931471803 * ((B : ℝ) / 8))
    (hc : 0.6931471803 * (((K : ℝ) * B - (8 * e + m : ℕ)) / 8) ≤ c) {x : ℝ} (hKx : (K : ℝ) < x) :
    a * x - c ≤ x * psiOne x := by
  have key := psiOneGrid_mul_ge K hKx
  have hx0 : 0 < x := lt_of_le_of_lt (Nat.cast_nonneg K) hKx
  have hl := Real.log_two_gt_d9
  have hS := psiAcc_snd_le he hm
  have hpsi := psiAcc_fst_le hB
  have hA0 : (0 : ℝ) ≤ ((8 * e + m : ℕ) : ℝ) := Nat.cast_nonneg _
  generalize ((8 * e + m : ℕ) : ℝ) = A at hS hc hA0
  have hxK : 0 ≤ x - K := by linarith
  have hnn : 0 ≤ A + (x - K) * B := add_nonneg hA0 (mul_nonneg hxK (Nat.cast_nonneg B))
  have h1 : Real.log 2 * (A + (x - K) * B) ≤ 8 * (x * psiOne x) := by
    nlinarith [mul_le_mul_of_nonneg_left hpsi hxK]
  have h2 : 0.6931471803 * (A + (x - K) * B) ≤ Real.log 2 * (A + (x - K) * B) :=
    mul_le_mul_of_nonneg_right hl.le hnn
  nlinarith [mul_le_mul_of_nonneg_right ha hx0.le]

/-- Rational form: `a - c / x ≤ ψ₁(x)`. -/
theorem psiOneGrid2_div {K e m B : ℕ} (he : e ≤ (psiAcc K).2.2)
    (hm : 2 ^ m ≤ (psiAcc K).2.1 ^ 8) (hB : 2 ^ B ≤ (psiAcc K).1 ^ 8) {a c : ℝ}
    (ha : a ≤ 0.6931471803 * ((B : ℝ) / 8))
    (hc : 0.6931471803 * (((K : ℝ) * B - (8 * e + m : ℕ)) / 8) ≤ c) {x : ℝ} (hKx : (K : ℝ) < x) :
    a - c / x ≤ psiOne x := by
  have h := psiOneGrid2_mul he hm hB ha hc hKx
  have hx0 : 0 < x := lt_of_le_of_lt (Nat.cast_nonneg K) hKx
  refine le_of_mul_le_mul_left ?_ hx0
  have : x * (a - c / x) = a * x - c := by field_simp
  rw [this]; exact h

/-- Cell lemma: a bound `a x - c ≤ x ψ₁(x)` implies `x/2 - E ≤ ψ₁(x)` on `(k, k']` as soon as
it does so at the two endpoints (convexity of `x²/2 - (E + a) x + c`). -/
theorem psiOneGrid2_cell {k k' a c E x : ℝ} (h : a * x - c ≤ x * psiOne x)
    (h1 : k * (k / 2 - E) ≤ a * k - c) (h2 : k' * (k' / 2 - E) ≤ a * k' - c)
    (hk : 0 ≤ k) (hx : k < x) (hx' : x ≤ k') : x / 2 - E ≤ psiOne x := by
  have hx0 : 0 < x := lt_of_le_of_lt hk hx
  refine le_of_mul_le_mul_left ?_ hx0
  have hkk : 0 < k' - k := by linarith
  have h3 : (k' - k) * (x * (x / 2 - E)) ≤ (k' - k) * (a * x - c) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx'),
      mul_le_mul_of_nonneg_right h1 (sub_nonneg.mpr hx'),
      mul_le_mul_of_nonneg_right h2 (sub_nonneg.mpr hx.le)]
  exact (le_of_mul_le_mul_left h3 hkk).trans h

/-! ## Grid certificates (generated) -/


theorem psiOneGrid2_cert_1536 :
    1688576 ≤ (psiAcc 1536).2.2 ∧ 2 ^ 64864 ≤ (psiAcc 1536).2.1 ^ 8 ∧ 2 ^ 17673 ≤ (psiAcc 1536).1 ^ 8 := by
  decide +kernel

/-- For `x > 1536`: `1531.248 x - 1175947 ≤ x ψ₁(x)` (sharp on `(1536, 1552]`). -/
theorem psiOne_lower_grid2_mul_1536 {x : ℝ} (hx : 1536 < x) : 1531.248 * x - 1175947 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1536.1 psiOneGrid2_cert_1536.2.1 psiOneGrid2_cert_1536.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1536`: `ψ₁(x) ≥ 1531.248 - 1175947/x` (sharp on `(1536, 1552]`). -/
theorem psiOne_lower_grid2_1536 {x : ℝ} (hx : 1536 < x) : 1531.248 - 1175947 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1536.1 psiOneGrid2_cert_1536.2.1 psiOneGrid2_cert_1536.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1536 {x : ℝ} (hx : 1536 < x) (hx' : x ≤ 1552) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1536 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1552 :
    1723392 ≤ (psiAcc 1552).2.2 ∧ 2 ^ 70123 ≤ (psiAcc 1552).2.1 ^ 8 ∧ 2 ^ 17842 ≤ (psiAcc 1552).1 ^ 8 := by
  decide +kernel

/-- For `x > 1552`: `1545.891 x - 1198584 ≤ x ψ₁(x)` (sharp on `(1552, 1568]`). -/
theorem psiOne_lower_grid2_mul_1552 {x : ℝ} (hx : 1552 < x) : 1545.891 * x - 1198584 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1552.1 psiOneGrid2_cert_1552.2.1 psiOneGrid2_cert_1552.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1552`: `ψ₁(x) ≥ 1545.891 - 1198584/x` (sharp on `(1552, 1568]`). -/
theorem psiOne_lower_grid2_1552 {x : ℝ} (hx : 1552 < x) : 1545.891 - 1198584 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1552.1 psiOneGrid2_cert_1552.2.1 psiOneGrid2_cert_1552.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1552 {x : ℝ} (hx : 1552 < x) (hx' : x ≤ 1568) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1552 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1568 :
    1766912 ≤ (psiAcc 1568).2.2 ∧ 2 ^ 9566 ≤ (psiAcc 1568).2.1 ^ 8 ∧ 2 ^ 18097 ≤ (psiAcc 1568).1 ^ 8 := by
  decide +kernel

/-- For `x > 1568`: `1567.985 x - 1233043 ≤ x ψ₁(x)` (sharp on `(1568, 1584]`). -/
theorem psiOne_lower_grid2_mul_1568 {x : ℝ} (hx : 1568 < x) : 1567.985 * x - 1233043 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1568.1 psiOneGrid2_cert_1568.2.1 psiOneGrid2_cert_1568.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1568`: `ψ₁(x) ≥ 1567.985 - 1233043/x` (sharp on `(1568, 1584]`). -/
theorem psiOne_lower_grid2_1568 {x : ℝ} (hx : 1568 < x) : 1567.985 - 1233043 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1568.1 psiOneGrid2_cert_1568.2.1 psiOneGrid2_cert_1568.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1568 {x : ℝ} (hx : 1568 < x) (hx' : x ≤ 1584) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1568 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1584 :
    1801728 ≤ (psiAcc 1584).2.2 ∧ 2 ^ 22208 ≤ (psiAcc 1584).2.1 ^ 8 ∧ 2 ^ 18352 ≤ (psiAcc 1584).1 ^ 8 := by
  decide +kernel

/-- For `x > 1584`: `1590.079 x - 1267900 ≤ x ψ₁(x)` (sharp on `(1584, 1600]`). -/
theorem psiOne_lower_grid2_mul_1584 {x : ℝ} (hx : 1584 < x) : 1590.079 * x - 1267900 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1584.1 psiOneGrid2_cert_1584.2.1 psiOneGrid2_cert_1584.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1584`: `ψ₁(x) ≥ 1590.079 - 1267900/x` (sharp on `(1584, 1600]`). -/
theorem psiOne_lower_grid2_1584 {x : ℝ} (hx : 1584 < x) : 1590.079 - 1267900 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1584.1 psiOneGrid2_cert_1584.2.1 psiOneGrid2_cert_1584.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1584 {x : ℝ} (hx : 1584 < x) (hx' : x ≤ 1600) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1584 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1600 :
    1836544 ≤ (psiAcc 1600).2.2 ∧ 2 ^ 37571 ≤ (psiAcc 1600).2.1 ^ 8 ∧ 2 ^ 18437 ≤ (psiAcc 1600).1 ^ 8 := by
  decide +kernel

/-- For `x > 1600`: `1597.444 x - 1279661 ≤ x ψ₁(x)` (sharp on `(1600, 1616]`). -/
theorem psiOne_lower_grid2_mul_1600 {x : ℝ} (hx : 1600 < x) : 1597.444 * x - 1279661 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1600.1 psiOneGrid2_cert_1600.2.1 psiOneGrid2_cert_1600.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1600`: `ψ₁(x) ≥ 1597.444 - 1279661/x` (sharp on `(1600, 1616]`). -/
theorem psiOne_lower_grid2_1600 {x : ℝ} (hx : 1600 < x) : 1597.444 - 1279661 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1600.1 psiOneGrid2_cert_1600.2.1 psiOneGrid2_cert_1600.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1600 {x : ℝ} (hx : 1600 < x) (hx' : x ≤ 1616) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1600 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1616 :
    1871360 ≤ (psiAcc 1616).2.2 ∧ 2 ^ 56936 ≤ (psiAcc 1616).2.1 ^ 8 ∧ 2 ^ 18778 ≤ (psiAcc 1616).1 ^ 8 := by
  decide +kernel

/-- For `x > 1616`: `1626.989 x - 1327155 ≤ x ψ₁(x)` (sharp on `(1616, 1632]`). -/
theorem psiOne_lower_grid2_mul_1616 {x : ℝ} (hx : 1616 < x) : 1626.989 * x - 1327155 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1616.1 psiOneGrid2_cert_1616.2.1 psiOneGrid2_cert_1616.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1616`: `ψ₁(x) ≥ 1626.989 - 1327155/x` (sharp on `(1616, 1632]`). -/
theorem psiOne_lower_grid2_1616 {x : ℝ} (hx : 1616 < x) : 1626.989 - 1327155 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1616.1 psiOneGrid2_cert_1616.2.1 psiOneGrid2_cert_1616.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1616 {x : ℝ} (hx : 1616 < x) (hx' : x ≤ 1632) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1616 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1632 :
    1914880 ≤ (psiAcc 1632).2.2 ∧ 2 ^ 11700 ≤ (psiAcc 1632).2.1 ^ 8 ∧ 2 ^ 19034 ≤ (psiAcc 1632).1 ^ 8 := by
  decide +kernel

/-- For `x > 1632`: `1649.170 x - 1363139 ≤ x ψ₁(x)` (sharp on `(1632, 1648]`). -/
theorem psiOne_lower_grid2_mul_1632 {x : ℝ} (hx : 1632 < x) : 1649.170 * x - 1363139 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1632.1 psiOneGrid2_cert_1632.2.1 psiOneGrid2_cert_1632.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1632`: `ψ₁(x) ≥ 1649.170 - 1363139/x` (sharp on `(1632, 1648]`). -/
theorem psiOne_lower_grid2_1632 {x : ℝ} (hx : 1632 < x) : 1649.170 - 1363139 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1632.1 psiOneGrid2_cert_1632.2.1 psiOneGrid2_cert_1632.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1632 {x : ℝ} (hx : 1632 < x) (hx' : x ≤ 1648) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1632 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1648 :
    1949696 ≤ (psiAcc 1648).2.2 ∧ 2 ^ 38657 ≤ (psiAcc 1648).2.1 ^ 8 ∧ 2 ^ 19119 ≤ (psiAcc 1648).1 ^ 8 := by
  decide +kernel

/-- For `x > 1648`: `1656.535 x - 1375195 ≤ x ψ₁(x)` (sharp on `(1648, 1664]`). -/
theorem psiOne_lower_grid2_mul_1648 {x : ℝ} (hx : 1648 < x) : 1656.535 * x - 1375195 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1648.1 psiOneGrid2_cert_1648.2.1 psiOneGrid2_cert_1648.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1648`: `ψ₁(x) ≥ 1656.535 - 1375195/x` (sharp on `(1648, 1664]`). -/
theorem psiOne_lower_grid2_1648 {x : ℝ} (hx : 1648 < x) : 1656.535 - 1375195 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1648.1 psiOneGrid2_cert_1648.2.1 psiOneGrid2_cert_1648.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1648 {x : ℝ} (hx : 1648 < x) (hx' : x ≤ 1664) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1648 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1664 :
    1984512 ≤ (psiAcc 1664).2.2 ∧ 2 ^ 66725 ≤ (psiAcc 1664).2.1 ^ 8 ∧ 2 ^ 19290 ≤ (psiAcc 1664).1 ^ 8 := by
  decide +kernel

/-- For `x > 1664`: `1671.351 x - 1399789 ≤ x ψ₁(x)` (sharp on `(1664, 1680]`). -/
theorem psiOne_lower_grid2_mul_1664 {x : ℝ} (hx : 1664 < x) : 1671.351 * x - 1399789 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1664.1 psiOneGrid2_cert_1664.2.1 psiOneGrid2_cert_1664.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1664`: `ψ₁(x) ≥ 1671.351 - 1399789/x` (sharp on `(1664, 1680]`). -/
theorem psiOne_lower_grid2_1664 {x : ℝ} (hx : 1664 < x) : 1671.351 - 1399789 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1664.1 psiOneGrid2_cert_1664.2.1 psiOneGrid2_cert_1664.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1664 {x : ℝ} (hx : 1664 < x) (hx' : x ≤ 1680) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1664 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1680 :
    2028032 ≤ (psiAcc 1680).2.2 ∧ 2 ^ 29271 ≤ (psiAcc 1680).2.1 ^ 8 ∧ 2 ^ 19461 ≤ (psiAcc 1680).1 ^ 8 := by
  decide +kernel

/-- For `x > 1680`: `1686.167 x - 1424501 ≤ x ψ₁(x)` (sharp on `(1680, 1696]`). -/
theorem psiOne_lower_grid2_mul_1680 {x : ℝ} (hx : 1680 < x) : 1686.167 * x - 1424501 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1680.1 psiOneGrid2_cert_1680.2.1 psiOneGrid2_cert_1680.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1680`: `ψ₁(x) ≥ 1686.167 - 1424501/x` (sharp on `(1680, 1696]`). -/
theorem psiOne_lower_grid2_1680 {x : ℝ} (hx : 1680 < x) : 1686.167 - 1424501 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1680.1 psiOneGrid2_cert_1680.2.1 psiOneGrid2_cert_1680.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1680 {x : ℝ} (hx : 1680 < x) (hx' : x ≤ 1696) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1680 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1696 :
    2062848 ≤ (psiAcc 1696).2.2 ∧ 2 ^ 63034 ≤ (psiAcc 1696).2.1 ^ 8 ∧ 2 ^ 19590 ≤ (psiAcc 1696).1 ^ 8 := by
  decide +kernel

/-- For `x > 1696`: `1697.344 x - 1443377 ≤ x ψ₁(x)` (sharp on `(1696, 1712]`). -/
theorem psiOne_lower_grid2_mul_1696 {x : ℝ} (hx : 1696 < x) : 1697.344 * x - 1443377 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1696.1 psiOneGrid2_cert_1696.2.1 psiOneGrid2_cert_1696.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1696`: `ψ₁(x) ≥ 1697.344 - 1443377/x` (sharp on `(1696, 1712]`). -/
theorem psiOne_lower_grid2_1696 {x : ℝ} (hx : 1696 < x) : 1697.344 - 1443377 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1696.1 psiOneGrid2_cert_1696.2.1 psiOneGrid2_cert_1696.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1696 {x : ℝ} (hx : 1696 < x) (hx' : x ≤ 1712) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1696 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1712 :
    2106368 ≤ (psiAcc 1712).2.2 ∧ 2 ^ 30984 ≤ (psiAcc 1712).2.1 ^ 8 ∧ 2 ^ 19848 ≤ (psiAcc 1712).1 ^ 8 := by
  decide +kernel

/-- For `x > 1712`: `1719.698 x - 1481416 ≤ x ψ₁(x)` (sharp on `(1712, 1728]`). -/
theorem psiOne_lower_grid2_mul_1712 {x : ℝ} (hx : 1712 < x) : 1719.698 * x - 1481416 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1712.1 psiOneGrid2_cert_1712.2.1 psiOneGrid2_cert_1712.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1712`: `ψ₁(x) ≥ 1719.698 - 1481416/x` (sharp on `(1712, 1728]`). -/
theorem psiOne_lower_grid2_1712 {x : ℝ} (hx : 1712 < x) : 1719.698 - 1481416 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1712.1 psiOneGrid2_cert_1712.2.1 psiOneGrid2_cert_1712.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1712 {x : ℝ} (hx : 1712 < x) (hx' : x ≤ 1728) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1712 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1728 :
    2141184 ≤ (psiAcc 1728).2.2 ∧ 2 ^ 71058 ≤ (psiAcc 1728).2.1 ^ 8 ∧ 2 ^ 20020 ≤ (psiAcc 1728).1 ^ 8 := by
  decide +kernel

/-- For `x > 1728`: `1734.600 x - 1507078 ≤ x ψ₁(x)` (sharp on `(1728, 1744]`). -/
theorem psiOne_lower_grid2_mul_1728 {x : ℝ} (hx : 1728 < x) : 1734.600 * x - 1507078 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1728.1 psiOneGrid2_cert_1728.2.1 psiOneGrid2_cert_1728.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1728`: `ψ₁(x) ≥ 1734.600 - 1507078/x` (sharp on `(1728, 1744]`). -/
theorem psiOne_lower_grid2_1728 {x : ℝ} (hx : 1728 < x) : 1734.600 - 1507078 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1728.1 psiOneGrid2_cert_1728.2.1 psiOneGrid2_cert_1728.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1728 {x : ℝ} (hx : 1728 < x) (hx' : x ≤ 1744) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1728 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1744 :
    2184704 ≤ (psiAcc 1744).2.2 ∧ 2 ^ 44426 ≤ (psiAcc 1744).2.1 ^ 8 ∧ 2 ^ 20192 ≤ (psiAcc 1744).1 ^ 8 := by
  decide +kernel

/-- For `x > 1744`: `1749.503 x - 1532964 ≤ x ψ₁(x)` (sharp on `(1744, 1760]`). -/
theorem psiOne_lower_grid2_mul_1744 {x : ℝ} (hx : 1744 < x) : 1749.503 * x - 1532964 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1744.1 psiOneGrid2_cert_1744.2.1 psiOneGrid2_cert_1744.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1744`: `ψ₁(x) ≥ 1749.503 - 1532964/x` (sharp on `(1744, 1760]`). -/
theorem psiOne_lower_grid2_1744 {x : ℝ} (hx : 1744 < x) : 1749.503 - 1532964 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1744.1 psiOneGrid2_cert_1744.2.1 psiOneGrid2_cert_1744.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1744 {x : ℝ} (hx : 1744 < x) (hx' : x ≤ 1760) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1744 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1760 :
    2228224 ≤ (psiAcc 1760).2.2 ∧ 2 ^ 21153 ≤ (psiAcc 1760).2.1 ^ 8 ∧ 2 ^ 20450 ≤ (psiAcc 1760).1 ^ 8 := by
  decide +kernel

/-- For `x > 1760`: `1771.857 x - 1572150 ≤ x ψ₁(x)` (sharp on `(1760, 1776]`). -/
theorem psiOne_lower_grid2_mul_1760 {x : ℝ} (hx : 1760 < x) : 1771.857 * x - 1572150 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1760.1 psiOneGrid2_cert_1760.2.1 psiOneGrid2_cert_1760.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1760`: `ψ₁(x) ≥ 1771.857 - 1572150/x` (sharp on `(1760, 1776]`). -/
theorem psiOne_lower_grid2_1760 {x : ℝ} (hx : 1760 < x) : 1771.857 - 1572150 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1760.1 psiOneGrid2_cert_1760.2.1 psiOneGrid2_cert_1760.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1760 {x : ℝ} (hx : 1760 < x) (hx' : x ≤ 1776) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1760 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1776 :
    2263040 ≤ (psiAcc 1776).2.2 ∧ 2 ^ 69841 ≤ (psiAcc 1776).2.1 ^ 8 ∧ 2 ^ 20450 ≤ (psiAcc 1776).1 ^ 8 := by
  decide +kernel

/-- For `x > 1776`: `1771.857 x - 1572148 ≤ x ψ₁(x)` (sharp on `(1776, 1792]`). -/
theorem psiOne_lower_grid2_mul_1776 {x : ℝ} (hx : 1776 < x) : 1771.857 * x - 1572148 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1776.1 psiOneGrid2_cert_1776.2.1 psiOneGrid2_cert_1776.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1776`: `ψ₁(x) ≥ 1771.857 - 1572148/x` (sharp on `(1776, 1792]`). -/
theorem psiOne_lower_grid2_1776 {x : ℝ} (hx : 1776 < x) : 1771.857 - 1572148 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1776.1 psiOneGrid2_cert_1776.2.1 psiOneGrid2_cert_1776.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1776 {x : ℝ} (hx : 1776 < x) (hx' : x ≤ 1792) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1776 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1792 :
    2306560 ≤ (psiAcc 1792).2.2 ∧ 2 ^ 51660 ≤ (psiAcc 1792).2.1 ^ 8 ∧ 2 ^ 20796 ≤ (psiAcc 1792).1 ^ 8 := by
  decide +kernel

/-- For `x > 1792`: `1801.836 x - 1625629 ≤ x ψ₁(x)` (sharp on `(1792, 1808]`). -/
theorem psiOne_lower_grid2_mul_1792 {x : ℝ} (hx : 1792 < x) : 1801.836 * x - 1625629 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1792.1 psiOneGrid2_cert_1792.2.1 psiOneGrid2_cert_1792.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1792`: `ψ₁(x) ≥ 1801.836 - 1625629/x` (sharp on `(1792, 1808]`). -/
theorem psiOne_lower_grid2_1792 {x : ℝ} (hx : 1792 < x) : 1801.836 - 1625629 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1792.1 psiOneGrid2_cert_1792.2.1 psiOneGrid2_cert_1792.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1792 {x : ℝ} (hx : 1792 < x) (hx' : x ≤ 1808) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1792 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1808 :
    2350080 ≤ (psiAcc 1808).2.2 ∧ 2 ^ 36852 ≤ (psiAcc 1808).2.1 ^ 8 ∧ 2 ^ 20883 ≤ (psiAcc 1808).1 ^ 8 := by
  decide +kernel

/-- For `x > 1808`: `1809.374 x - 1639205 ≤ x ψ₁(x)` (sharp on `(1808, 1824]`). -/
theorem psiOne_lower_grid2_mul_1808 {x : ℝ} (hx : 1808 < x) : 1809.374 * x - 1639205 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1808.1 psiOneGrid2_cert_1808.2.1 psiOneGrid2_cert_1808.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1808`: `ψ₁(x) ≥ 1809.374 - 1639205/x` (sharp on `(1808, 1824]`). -/
theorem psiOne_lower_grid2_1808 {x : ℝ} (hx : 1808 < x) : 1809.374 - 1639205 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1808.1 psiOneGrid2_cert_1808.2.1 psiOneGrid2_cert_1808.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1808 {x : ℝ} (hx : 1808 < x) (hx' : x ≤ 1824) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1808 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1824 :
    2393600 ≤ (psiAcc 1824).2.2 ∧ 2 ^ 24034 ≤ (psiAcc 1824).2.1 ^ 8 ∧ 2 ^ 21056 ≤ (psiAcc 1824).1 ^ 8 := by
  decide +kernel

/-- For `x > 1824`: `1824.363 x - 1666440 ≤ x ψ₁(x)` (sharp on `(1824, 1840]`). -/
theorem psiOne_lower_grid2_mul_1824 {x : ℝ} (hx : 1824 < x) : 1824.363 * x - 1666440 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1824.1 psiOneGrid2_cert_1824.2.1 psiOneGrid2_cert_1824.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1824`: `ψ₁(x) ≥ 1824.363 - 1666440/x` (sharp on `(1824, 1840]`). -/
theorem psiOne_lower_grid2_1824 {x : ℝ} (hx : 1824 < x) : 1824.363 - 1666440 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1824.1 psiOneGrid2_cert_1824.2.1 psiOneGrid2_cert_1824.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1824 {x : ℝ} (hx : 1824 < x) (hx' : x ≤ 1840) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1824 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1840 :
    2437120 ≤ (psiAcc 1840).2.2 ∧ 2 ^ 13555 ≤ (psiAcc 1840).2.1 ^ 8 ∧ 2 ^ 21143 ≤ (psiAcc 1840).1 ^ 8 := by
  decide +kernel

/-- For `x > 1840`: `1831.901 x - 1680242 ≤ x ψ₁(x)` (sharp on `(1840, 1856]`). -/
theorem psiOne_lower_grid2_mul_1840 {x : ℝ} (hx : 1840 < x) : 1831.901 * x - 1680242 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1840.1 psiOneGrid2_cert_1840.2.1 psiOneGrid2_cert_1840.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1840`: `ψ₁(x) ≥ 1831.901 - 1680242/x` (sharp on `(1840, 1856]`). -/
theorem psiOne_lower_grid2_1840 {x : ℝ} (hx : 1840 < x) : 1831.901 - 1680242 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1840.1 psiOneGrid2_cert_1840.2.1 psiOneGrid2_cert_1840.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1840 {x : ℝ} (hx : 1840 < x) (hx' : x ≤ 1856) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1840 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1856 :
    2480640 ≤ (psiAcc 1856).2.2 ∧ 2 ^ 4769 ≤ (psiAcc 1856).2.1 ^ 8 ∧ 2 ^ 21273 ≤ (psiAcc 1856).1 ^ 8 := by
  decide +kernel

/-- For `x > 1856`: `1843.164 x - 1701053 ≤ x ψ₁(x)` (sharp on `(1856, 1872]`). -/
theorem psiOne_lower_grid2_mul_1856 {x : ℝ} (hx : 1856 < x) : 1843.164 * x - 1701053 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1856.1 psiOneGrid2_cert_1856.2.1 psiOneGrid2_cert_1856.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1856`: `ψ₁(x) ≥ 1843.164 - 1701053/x` (sharp on `(1856, 1872]`). -/
theorem psiOne_lower_grid2_1856 {x : ℝ} (hx : 1856 < x) : 1843.164 - 1701053 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1856.1 psiOneGrid2_cert_1856.2.1 psiOneGrid2_cert_1856.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1856 {x : ℝ} (hx : 1856 < x) (hx' : x ≤ 1872) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1856 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1872 :
    2515456 ≤ (psiAcc 1872).2.2 ∧ 2 ^ 68091 ≤ (psiAcc 1872).2.1 ^ 8 ∧ 2 ^ 21534 ≤ (psiAcc 1872).1 ^ 8 := by
  decide +kernel

/-- For `x > 1872`: `1865.778 x - 1743258 ≤ x ψ₁(x)` (sharp on `(1872, 1888]`). -/
theorem psiOne_lower_grid2_mul_1872 {x : ℝ} (hx : 1872 < x) : 1865.778 * x - 1743258 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1872.1 psiOneGrid2_cert_1872.2.1 psiOneGrid2_cert_1872.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1872`: `ψ₁(x) ≥ 1865.778 - 1743258/x` (sharp on `(1872, 1888]`). -/
theorem psiOne_lower_grid2_1872 {x : ℝ} (hx : 1872 < x) : 1865.778 - 1743258 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1872.1 psiOneGrid2_cert_1872.2.1 psiOneGrid2_cert_1872.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1872 {x : ℝ} (hx : 1872 < x) (hx' : x ≤ 1888) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1872 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1888 :
    2558976 ≤ (psiAcc 1888).2.2 ∧ 2 ^ 67521 ≤ (psiAcc 1888).2.1 ^ 8 ∧ 2 ^ 21795 ≤ (psiAcc 1888).1 ^ 8 := by
  decide +kernel

/-- For `x > 1888`: `1888.392 x - 1785689 ≤ x ψ₁(x)` (sharp on `(1888, 1904]`). -/
theorem psiOne_lower_grid2_mul_1888 {x : ℝ} (hx : 1888 < x) : 1888.392 * x - 1785689 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1888.1 psiOneGrid2_cert_1888.2.1 psiOneGrid2_cert_1888.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1888`: `ψ₁(x) ≥ 1888.392 - 1785689/x` (sharp on `(1888, 1904]`). -/
theorem psiOne_lower_grid2_1888 {x : ℝ} (hx : 1888 < x) : 1888.392 - 1785689 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1888.1 psiOneGrid2_cert_1888.2.1 psiOneGrid2_cert_1888.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1888 {x : ℝ} (hx : 1888 < x) (hx' : x ≤ 1904) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1888 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1904 :
    2602496 ≤ (psiAcc 1904).2.2 ∧ 2 ^ 69648 ≤ (psiAcc 1904).2.1 ^ 8 ∧ 2 ^ 21969 ≤ (psiAcc 1904).1 ^ 8 := by
  decide +kernel

/-- For `x > 1904`: `1903.468 x - 1814258 ≤ x ψ₁(x)` (sharp on `(1904, 1920]`). -/
theorem psiOne_lower_grid2_mul_1904 {x : ℝ} (hx : 1904 < x) : 1903.468 * x - 1814258 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1904.1 psiOneGrid2_cert_1904.2.1 psiOneGrid2_cert_1904.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1904`: `ψ₁(x) ≥ 1903.468 - 1814258/x` (sharp on `(1904, 1920]`). -/
theorem psiOne_lower_grid2_1904 {x : ℝ} (hx : 1904 < x) : 1903.468 - 1814258 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1904.1 psiOneGrid2_cert_1904.2.1 psiOneGrid2_cert_1904.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1904 {x : ℝ} (hx : 1904 < x) (hx' : x ≤ 1920) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1904 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1920 :
    2654720 ≤ (psiAcc 1920).2.2 ∧ 2 ^ 5108 ≤ (psiAcc 1920).2.1 ^ 8 ∧ 2 ^ 22143 ≤ (psiAcc 1920).1 ^ 8 := by
  decide +kernel

/-- For `x > 1920`: `1918.544 x - 1843052 ≤ x ψ₁(x)` (sharp on `(1920, 1936]`). -/
theorem psiOne_lower_grid2_mul_1920 {x : ℝ} (hx : 1920 < x) : 1918.544 * x - 1843052 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1920.1 psiOneGrid2_cert_1920.2.1 psiOneGrid2_cert_1920.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1920`: `ψ₁(x) ≥ 1918.544 - 1843052/x` (sharp on `(1920, 1936]`). -/
theorem psiOne_lower_grid2_1920 {x : ℝ} (hx : 1920 < x) : 1918.544 - 1843052 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1920.1 psiOneGrid2_cert_1920.2.1 psiOneGrid2_cert_1920.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1920 {x : ℝ} (hx : 1920 < x) (hx' : x ≤ 1936) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1920 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1936 :
    2698240 ≤ (psiAcc 1936).2.2 ∧ 2 ^ 11944 ≤ (psiAcc 1936).2.1 ^ 8 ∧ 2 ^ 22318 ≤ (psiAcc 1936).1 ^ 8 := by
  decide +kernel

/-- For `x > 1936`: `1933.707 x - 1872346 ≤ x ψ₁(x)` (sharp on `(1936, 1952]`). -/
theorem psiOne_lower_grid2_mul_1936 {x : ℝ} (hx : 1936 < x) : 1933.707 * x - 1872346 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1936.1 psiOneGrid2_cert_1936.2.1 psiOneGrid2_cert_1936.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1936`: `ψ₁(x) ≥ 1933.707 - 1872346/x` (sharp on `(1936, 1952]`). -/
theorem psiOne_lower_grid2_1936 {x : ℝ} (hx : 1936 < x) : 1933.707 - 1872346 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1936.1 psiOneGrid2_cert_1936.2.1 psiOneGrid2_cert_1936.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1936 {x : ℝ} (hx : 1936 < x) (hx' : x ≤ 1952) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1936 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1952 :
    2741760 ≤ (psiAcc 1952).2.2 ∧ 2 ^ 21227 ≤ (psiAcc 1952).2.1 ^ 8 ∧ 2 ^ 22493 ≤ (psiAcc 1952).1 ^ 8 := by
  decide +kernel

/-- For `x > 1952`: `1948.869 x - 1901912 ≤ x ψ₁(x)` (sharp on `(1952, 1968]`). -/
theorem psiOne_lower_grid2_mul_1952 {x : ℝ} (hx : 1952 < x) : 1948.869 * x - 1901912 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1952.1 psiOneGrid2_cert_1952.2.1 psiOneGrid2_cert_1952.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1952`: `ψ₁(x) ≥ 1948.869 - 1901912/x` (sharp on `(1952, 1968]`). -/
theorem psiOne_lower_grid2_1952 {x : ℝ} (hx : 1952 < x) : 1948.869 - 1901912 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1952.1 psiOneGrid2_cert_1952.2.1 psiOneGrid2_cert_1952.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1952 {x : ℝ} (hx : 1952 < x) (hx' : x ≤ 1968) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1952 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1968 :
    2785280 ≤ (psiAcc 1968).2.2 ∧ 2 ^ 32957 ≤ (psiAcc 1968).2.1 ^ 8 ∧ 2 ^ 22493 ≤ (psiAcc 1968).1 ^ 8 := by
  decide +kernel

/-- For `x > 1968`: `1948.869 x - 1901912 ≤ x ψ₁(x)` (sharp on `(1968, 1984]`). -/
theorem psiOne_lower_grid2_mul_1968 {x : ℝ} (hx : 1968 < x) : 1948.869 * x - 1901912 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1968.1 psiOneGrid2_cert_1968.2.1 psiOneGrid2_cert_1968.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1968`: `ψ₁(x) ≥ 1948.869 - 1901912/x` (sharp on `(1968, 1984]`). -/
theorem psiOne_lower_grid2_1968 {x : ℝ} (hx : 1968 < x) : 1948.869 - 1901912 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1968.1 psiOneGrid2_cert_1968.2.1 psiOneGrid2_cert_1968.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1968 {x : ℝ} (hx : 1968 < x) (hx' : x ≤ 1984) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1968 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_1984 :
    2828800 ≤ (psiAcc 1984).2.2 ∧ 2 ^ 46088 ≤ (psiAcc 1984).2.1 ^ 8 ∧ 2 ^ 22668 ≤ (psiAcc 1984).1 ^ 8 := by
  decide +kernel

/-- For `x > 1984`: `1964.032 x - 1931873 ≤ x ψ₁(x)` (sharp on `(1984, 2000]`). -/
theorem psiOne_lower_grid2_mul_1984 {x : ℝ} (hx : 1984 < x) : 1964.032 * x - 1931873 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_1984.1 psiOneGrid2_cert_1984.2.1 psiOneGrid2_cert_1984.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 1984`: `ψ₁(x) ≥ 1964.032 - 1931873/x` (sharp on `(1984, 2000]`). -/
theorem psiOne_lower_grid2_1984 {x : ℝ} (hx : 1984 < x) : 1964.032 - 1931873 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_1984.1 psiOneGrid2_cert_1984.2.1 psiOneGrid2_cert_1984.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_1984 {x : ℝ} (hx : 1984 < x) (hx' : x ≤ 2000) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_1984 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2000 :
    2872320 ≤ (psiAcc 2000).2.2 ∧ 2 ^ 62726 ≤ (psiAcc 2000).2.1 ^ 8 ∧ 2 ^ 23019 ≤ (psiAcc 2000).1 ^ 8 := by
  decide +kernel

/-- For `x > 2000`: `1994.444 x - 1992514 ≤ x ψ₁(x)` (sharp on `(2000, 2016]`). -/
theorem psiOne_lower_grid2_mul_2000 {x : ℝ} (hx : 2000 < x) : 1994.444 * x - 1992514 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2000.1 psiOneGrid2_cert_2000.2.1 psiOneGrid2_cert_2000.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2000`: `ψ₁(x) ≥ 1994.444 - 1992514/x` (sharp on `(2000, 2016]`). -/
theorem psiOne_lower_grid2_2000 {x : ℝ} (hx : 2000 < x) : 1994.444 - 1992514 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2000.1 psiOneGrid2_cert_2000.2.1 psiOneGrid2_cert_2000.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2000 {x : ℝ} (hx : 2000 < x) (hx' : x ≤ 2016) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2000 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2016 :
    2924544 ≤ (psiAcc 2016).2.2 ∧ 2 ^ 14819 ≤ (psiAcc 2016).2.1 ^ 8 ∧ 2 ^ 23194 ≤ (psiAcc 2016).1 ^ 8 := by
  decide +kernel

/-- For `x > 2016`: `2009.606 x - 2022945 ≤ x ψ₁(x)` (sharp on `(2016, 2032]`). -/
theorem psiOne_lower_grid2_mul_2016 {x : ℝ} (hx : 2016 < x) : 2009.606 * x - 2022945 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2016.1 psiOneGrid2_cert_2016.2.1 psiOneGrid2_cert_2016.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2016`: `ψ₁(x) ≥ 2009.606 - 2022945/x` (sharp on `(2016, 2032]`). -/
theorem psiOne_lower_grid2_2016 {x : ℝ} (hx : 2016 < x) : 2009.606 - 2022945 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2016.1 psiOneGrid2_cert_2016.2.1 psiOneGrid2_cert_2016.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2016 {x : ℝ} (hx : 2016 < x) (hx' : x ≤ 2032) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2016 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2032 :
    2968064 ≤ (psiAcc 2032).2.2 ∧ 2 ^ 39793 ≤ (psiAcc 2032).2.1 ^ 8 ∧ 2 ^ 23458 ≤ (psiAcc 2032).1 ^ 8 := by
  decide +kernel

/-- For `x > 2032`: `2032.480 x - 2069249 ≤ x ψ₁(x)` (sharp on `(2032, 2048]`). -/
theorem psiOne_lower_grid2_mul_2032 {x : ℝ} (hx : 2032 < x) : 2032.480 * x - 2069249 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2032.1 psiOneGrid2_cert_2032.2.1 psiOneGrid2_cert_2032.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2032`: `ψ₁(x) ≥ 2032.480 - 2069249/x` (sharp on `(2032, 2048]`). -/
theorem psiOne_lower_grid2_2032 {x : ℝ} (hx : 2032 < x) : 2032.480 - 2069249 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2032.1 psiOneGrid2_cert_2032.2.1 psiOneGrid2_cert_2032.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2032 {x : ℝ} (hx : 2032 < x) (hx' : x ≤ 2048) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2032 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2048 :
    3011584 ≤ (psiAcc 2048).2.2 ∧ 2 ^ 67756 ≤ (psiAcc 2048).2.1 ^ 8 ∧ 2 ^ 23554 ≤ (psiAcc 2048).1 ^ 8 := by
  decide +kernel

/-- For `x > 2048`: `2040.798 x - 2086214 ≤ x ψ₁(x)` (sharp on `(2048, 2064]`). -/
theorem psiOne_lower_grid2_mul_2048 {x : ℝ} (hx : 2048 < x) : 2040.798 * x - 2086214 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2048.1 psiOneGrid2_cert_2048.2.1 psiOneGrid2_cert_2048.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2048`: `ψ₁(x) ≥ 2040.798 - 2086214/x` (sharp on `(2048, 2064]`). -/
theorem psiOne_lower_grid2_2048 {x : ℝ} (hx : 2048 < x) : 2040.798 - 2086214 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2048.1 psiOneGrid2_cert_2048.2.1 psiOneGrid2_cert_2048.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2048 {x : ℝ} (hx : 2048 < x) (hx' : x ≤ 2064) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2048 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2064 :
    3063808 ≤ (psiAcc 2064).2.2 ∧ 2 ^ 27887 ≤ (psiAcc 2064).2.1 ^ 8 ∧ 2 ^ 23730 ≤ (psiAcc 2064).1 ^ 8 := by
  decide +kernel

/-- For `x > 2064`: `2056.047 x - 2117597 ≤ x ψ₁(x)` (sharp on `(2064, 2080]`). -/
theorem psiOne_lower_grid2_mul_2064 {x : ℝ} (hx : 2064 < x) : 2056.047 * x - 2117597 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2064.1 psiOneGrid2_cert_2064.2.1 psiOneGrid2_cert_2064.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2064`: `ψ₁(x) ≥ 2056.047 - 2117597/x` (sharp on `(2064, 2080]`). -/
theorem psiOne_lower_grid2_2064 {x : ℝ} (hx : 2064 < x) : 2056.047 - 2117597 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2064.1 psiOneGrid2_cert_2064.2.1 psiOneGrid2_cert_2064.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2064 {x : ℝ} (hx : 2064 < x) (hx' : x ≤ 2080) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2064 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2080 :
    3107328 ≤ (psiAcc 2080).2.2 ∧ 2 ^ 60381 ≤ (psiAcc 2080).2.1 ^ 8 ∧ 2 ^ 23818 ≤ (psiAcc 2080).1 ^ 8 := by
  decide +kernel

/-- For `x > 2080`: `2063.672 x - 2133372 ≤ x ψ₁(x)` (sharp on `(2080, 2096]`). -/
theorem psiOne_lower_grid2_mul_2080 {x : ℝ} (hx : 2080 < x) : 2063.672 * x - 2133372 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2080.1 psiOneGrid2_cert_2080.2.1 psiOneGrid2_cert_2080.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2080`: `ψ₁(x) ≥ 2063.672 - 2133372/x` (sharp on `(2080, 2096]`). -/
theorem psiOne_lower_grid2_2080 {x : ℝ} (hx : 2080 < x) : 2063.672 - 2133372 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2080.1 psiOneGrid2_cert_2080.2.1 psiOneGrid2_cert_2080.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2080 {x : ℝ} (hx : 2080 < x) (hx' : x ≤ 2096) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2080 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2096 :
    3159552 ≤ (psiAcc 2096).2.2 ∧ 2 ^ 27564 ≤ (psiAcc 2096).2.1 ^ 8 ∧ 2 ^ 24171 ≤ (psiAcc 2096).1 ^ 8 := by
  decide +kernel

/-- For `x > 2096`: `2094.257 x - 2197142 ≤ x ψ₁(x)` (sharp on `(2096, 2112]`). -/
theorem psiOne_lower_grid2_mul_2096 {x : ℝ} (hx : 2096 < x) : 2094.257 * x - 2197142 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2096.1 psiOneGrid2_cert_2096.2.1 psiOneGrid2_cert_2096.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2096`: `ψ₁(x) ≥ 2094.257 - 2197142/x` (sharp on `(2096, 2112]`). -/
theorem psiOne_lower_grid2_2096 {x : ℝ} (hx : 2096 < x) : 2094.257 - 2197142 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2096.1 psiOneGrid2_cert_2096.2.1 psiOneGrid2_cert_2096.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2096 {x : ℝ} (hx : 2096 < x) (hx' : x ≤ 2112) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2096 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2112 :
    3203072 ≤ (psiAcc 2112).2.2 ∧ 2 ^ 67379 ≤ (psiAcc 2112).2.1 ^ 8 ∧ 2 ^ 24347 ≤ (psiAcc 2112).1 ^ 8 := by
  decide +kernel

/-- For `x > 2112`: `2109.506 x - 2229241 ≤ x ψ₁(x)` (sharp on `(2112, 2128]`). -/
theorem psiOne_lower_grid2_mul_2112 {x : ℝ} (hx : 2112 < x) : 2109.506 * x - 2229241 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2112.1 psiOneGrid2_cert_2112.2.1 psiOneGrid2_cert_2112.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2112`: `ψ₁(x) ≥ 2109.506 - 2229241/x` (sharp on `(2112, 2128]`). -/
theorem psiOne_lower_grid2_2112 {x : ℝ} (hx : 2112 < x) : 2109.506 - 2229241 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2112.1 psiOneGrid2_cert_2112.2.1 psiOneGrid2_cert_2112.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2112 {x : ℝ} (hx : 2112 < x) (hx' : x ≤ 2128) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2112 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2128 :
    3255296 ≤ (psiAcc 2128).2.2 ∧ 2 ^ 40478 ≤ (psiAcc 2128).2.1 ^ 8 ∧ 2 ^ 24436 ≤ (psiAcc 2128).1 ^ 8 := by
  decide +kernel

/-- For `x > 2128`: `2117.218 x - 2245534 ≤ x ψ₁(x)` (sharp on `(2128, 2144]`). -/
theorem psiOne_lower_grid2_mul_2128 {x : ℝ} (hx : 2128 < x) : 2117.218 * x - 2245534 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2128.1 psiOneGrid2_cert_2128.2.1 psiOneGrid2_cert_2128.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2128`: `ψ₁(x) ≥ 2117.218 - 2245534/x` (sharp on `(2128, 2144]`). -/
theorem psiOne_lower_grid2_2128 {x : ℝ} (hx : 2128 < x) : 2117.218 - 2245534 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2128.1 psiOneGrid2_cert_2128.2.1 psiOneGrid2_cert_2128.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2128 {x : ℝ} (hx : 2128 < x) (hx' : x ≤ 2144) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2128 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2144 :
    3307520 ≤ (psiAcc 2144).2.2 ∧ 2 ^ 17116 ≤ (psiAcc 2144).2.1 ^ 8 ∧ 2 ^ 24878 ≤ (psiAcc 2144).1 ^ 8 := by
  decide +kernel

/-- For `x > 2144`: `2155.514 x - 2327342 ≤ x ψ₁(x)` (sharp on `(2144, 2160]`). -/
theorem psiOne_lower_grid2_mul_2144 {x : ℝ} (hx : 2144 < x) : 2155.514 * x - 2327342 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2144.1 psiOneGrid2_cert_2144.2.1 psiOneGrid2_cert_2144.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2144`: `ψ₁(x) ≥ 2155.514 - 2327342/x` (sharp on `(2144, 2160]`). -/
theorem psiOne_lower_grid2_2144 {x : ℝ} (hx : 2144 < x) : 2155.514 - 2327342 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2144.1 psiOneGrid2_cert_2144.2.1 psiOneGrid2_cert_2144.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2144 {x : ℝ} (hx : 2144 < x) (hx' : x ≤ 2160) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2144 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2160 :
    3351040 ≤ (psiAcc 2160).2.2 ∧ 2 ^ 67634 ≤ (psiAcc 2160).2.1 ^ 8 ∧ 2 ^ 24967 ≤ (psiAcc 2160).1 ^ 8 := by
  decide +kernel

/-- For `x > 2160`: `2163.225 x - 2343944 ≤ x ψ₁(x)` (sharp on `(2160, 2176]`). -/
theorem psiOne_lower_grid2_mul_2160 {x : ℝ} (hx : 2160 < x) : 2163.225 * x - 2343944 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2160.1 psiOneGrid2_cert_2160.2.1 psiOneGrid2_cert_2160.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2160`: `ψ₁(x) ≥ 2163.225 - 2343944/x` (sharp on `(2160, 2176]`). -/
theorem psiOne_lower_grid2_2160 {x : ℝ} (hx : 2160 < x) : 2163.225 - 2343944 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2160.1 psiOneGrid2_cert_2160.2.1 psiOneGrid2_cert_2160.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2160 {x : ℝ} (hx : 2160 < x) (hx' : x ≤ 2176) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2160 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2176 :
    3403264 ≤ (psiAcc 2176).2.2 ∧ 2 ^ 50647 ≤ (psiAcc 2176).2.1 ^ 8 ∧ 2 ^ 25055 ≤ (psiAcc 2176).1 ^ 8 := by
  decide +kernel

/-- For `x > 2176`: `2170.850 x - 2360420 ≤ x ψ₁(x)` (sharp on `(2176, 2192]`). -/
theorem psiOne_lower_grid2_mul_2176 {x : ℝ} (hx : 2176 < x) : 2170.850 * x - 2360420 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2176.1 psiOneGrid2_cert_2176.2.1 psiOneGrid2_cert_2176.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2176`: `ψ₁(x) ≥ 2170.850 - 2360420/x` (sharp on `(2176, 2192]`). -/
theorem psiOne_lower_grid2_2176 {x : ℝ} (hx : 2176 < x) : 2170.850 - 2360420 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2176.1 psiOneGrid2_cert_2176.2.1 psiOneGrid2_cert_2176.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2176 {x : ℝ} (hx : 2176 < x) (hx' : x ≤ 2192) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2176 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2192 :
    3455488 ≤ (psiAcc 2192).2.2 ∧ 2 ^ 34965 ≤ (psiAcc 2192).2.1 ^ 8 ∧ 2 ^ 25157 ≤ (psiAcc 2192).1 ^ 8 := by
  decide +kernel

/-- For `x > 2192`: `2179.687 x - 2379685 ≤ x ψ₁(x)` (sharp on `(2192, 2208]`). -/
theorem psiOne_lower_grid2_mul_2192 {x : ℝ} (hx : 2192 < x) : 2179.687 * x - 2379685 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2192.1 psiOneGrid2_cert_2192.2.1 psiOneGrid2_cert_2192.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2192`: `ψ₁(x) ≥ 2179.687 - 2379685/x` (sharp on `(2192, 2208]`). -/
theorem psiOne_lower_grid2_2192 {x : ℝ} (hx : 2192 < x) : 2179.687 - 2379685 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2192.1 psiOneGrid2_cert_2192.2.1 psiOneGrid2_cert_2192.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2192 {x : ℝ} (hx : 2192 < x) (hx' : x ≤ 2208) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2192 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2208 :
    3507712 ≤ (psiAcc 2208).2.2 ∧ 2 ^ 20548 ≤ (psiAcc 2208).2.1 ^ 8 ∧ 2 ^ 25364 ≤ (psiAcc 2208).1 ^ 8 := by
  decide +kernel

/-- For `x > 2208`: `2197.623 x - 2419211 ≤ x ψ₁(x)` (sharp on `(2208, 2224]`). -/
theorem psiOne_lower_grid2_mul_2208 {x : ℝ} (hx : 2208 < x) : 2197.623 * x - 2419211 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2208.1 psiOneGrid2_cert_2208.2.1 psiOneGrid2_cert_2208.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2208`: `ψ₁(x) ≥ 2197.623 - 2419211/x` (sharp on `(2208, 2224]`). -/
theorem psiOne_lower_grid2_2208 {x : ℝ} (hx : 2208 < x) : 2197.623 - 2419211 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2208.1 psiOneGrid2_cert_2208.2.1 psiOneGrid2_cert_2208.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2208 {x : ℝ} (hx : 2208 < x) (hx' : x ≤ 2224) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2208 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2224 :
    3559936 ≤ (psiAcc 2224).2.2 ∧ 2 ^ 10500 ≤ (psiAcc 2224).2.1 ^ 8 ∧ 2 ^ 25586 ≤ (psiAcc 2224).1 ^ 8 := by
  decide +kernel

/-- For `x > 2224`: `2216.857 x - 2461823 ≤ x ψ₁(x)` (sharp on `(2224, 2240]`). -/
theorem psiOne_lower_grid2_mul_2224 {x : ℝ} (hx : 2224 < x) : 2216.857 * x - 2461823 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2224.1 psiOneGrid2_cert_2224.2.1 psiOneGrid2_cert_2224.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2224`: `ψ₁(x) ≥ 2216.857 - 2461823/x` (sharp on `(2224, 2240]`). -/
theorem psiOne_lower_grid2_2224 {x : ℝ} (hx : 2224 < x) : 2216.857 - 2461823 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2224.1 psiOneGrid2_cert_2224.2.1 psiOneGrid2_cert_2224.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2224 {x : ℝ} (hx : 2224 < x) (hx' : x ≤ 2240) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2224 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2240 :
    3603456 ≤ (psiAcc 2240).2.2 ∧ 2 ^ 72085 ≤ (psiAcc 2240).2.1 ^ 8 ∧ 2 ^ 25764 ≤ (psiAcc 2240).1 ^ 8 := by
  decide +kernel

/-- For `x > 2240`: `2232.280 x - 2496338 ≤ x ψ₁(x)` (sharp on `(2240, 2256]`). -/
theorem psiOne_lower_grid2_mul_2240 {x : ℝ} (hx : 2240 < x) : 2232.280 * x - 2496338 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2240.1 psiOneGrid2_cert_2240.2.1 psiOneGrid2_cert_2240.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2240`: `ψ₁(x) ≥ 2232.280 - 2496338/x` (sharp on `(2240, 2256]`). -/
theorem psiOne_lower_grid2_2240 {x : ℝ} (hx : 2240 < x) : 2232.280 - 2496338 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2240.1 psiOneGrid2_cert_2240.2.1 psiOneGrid2_cert_2240.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2240 {x : ℝ} (hx : 2240 < x) (hx' : x ≤ 2256) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2240 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2256 :
    3655680 ≤ (psiAcc 2256).2.2 ∧ 2 ^ 68134 ≤ (psiAcc 2256).2.1 ^ 8 ∧ 2 ^ 25943 ≤ (psiAcc 2256).1 ^ 8 := by
  decide +kernel

/-- For `x > 2256`: `2247.789 x - 2531186 ≤ x ψ₁(x)` (sharp on `(2256, 2272]`). -/
theorem psiOne_lower_grid2_mul_2256 {x : ℝ} (hx : 2256 < x) : 2247.789 * x - 2531186 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2256.1 psiOneGrid2_cert_2256.2.1 psiOneGrid2_cert_2256.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2256`: `ψ₁(x) ≥ 2247.789 - 2531186/x` (sharp on `(2256, 2272]`). -/
theorem psiOne_lower_grid2_2256 {x : ℝ} (hx : 2256 < x) : 2247.789 - 2531186 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2256.1 psiOneGrid2_cert_2256.2.1 psiOneGrid2_cert_2256.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2256 {x : ℝ} (hx : 2256 < x) (hx' : x ≤ 2272) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2256 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2272 :
    3707904 ≤ (psiAcc 2272).2.2 ∧ 2 ^ 66143 ≤ (psiAcc 2272).2.1 ^ 8 ∧ 2 ^ 26121 ≤ (psiAcc 2272).1 ^ 8 := by
  decide +kernel

/-- For `x > 2272`: `2263.212 x - 2566165 ≤ x ψ₁(x)` (sharp on `(2272, 2288]`). -/
theorem psiOne_lower_grid2_mul_2272 {x : ℝ} (hx : 2272 < x) : 2263.212 * x - 2566165 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2272.1 psiOneGrid2_cert_2272.2.1 psiOneGrid2_cert_2272.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2272`: `ψ₁(x) ≥ 2263.212 - 2566165/x` (sharp on `(2272, 2288]`). -/
theorem psiOne_lower_grid2_2272 {x : ℝ} (hx : 2272 < x) : 2263.212 - 2566165 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2272.1 psiOneGrid2_cert_2272.2.1 psiOneGrid2_cert_2272.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2272 {x : ℝ} (hx : 2272 < x) (hx' : x ≤ 2288) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2272 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2288 :
    3760128 ≤ (psiAcc 2288).2.2 ∧ 2 ^ 68345 ≤ (psiAcc 2288).2.1 ^ 8 ∧ 2 ^ 26389 ≤ (psiAcc 2288).1 ^ 8 := by
  decide +kernel

/-- For `x > 2288`: `2286.432 x - 2619115 ≤ x ψ₁(x)` (sharp on `(2288, 2304]`). -/
theorem psiOne_lower_grid2_mul_2288 {x : ℝ} (hx : 2288 < x) : 2286.432 * x - 2619115 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2288.1 psiOneGrid2_cert_2288.2.1 psiOneGrid2_cert_2288.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2288`: `ψ₁(x) ≥ 2286.432 - 2619115/x` (sharp on `(2288, 2304]`). -/
theorem psiOne_lower_grid2_2288 {x : ℝ} (hx : 2288 < x) : 2286.432 - 2619115 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2288.1 psiOneGrid2_cert_2288.2.1 psiOneGrid2_cert_2288.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2288 {x : ℝ} (hx : 2288 < x) (hx' : x ≤ 2304) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2288 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2304 :
    3821056 ≤ (psiAcc 2304).2.2 ∧ 2 ^ 4754 ≤ (psiAcc 2304).2.1 ^ 8 ∧ 2 ^ 26567 ≤ (psiAcc 2304).1 ^ 8 := by
  decide +kernel

/-- For `x > 2304`: `2301.855 x - 2654509 ≤ x ψ₁(x)` (sharp on `(2304, 2320]`). -/
theorem psiOne_lower_grid2_mul_2304 {x : ℝ} (hx : 2304 < x) : 2301.855 * x - 2654509 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2304.1 psiOneGrid2_cert_2304.2.1 psiOneGrid2_cert_2304.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2304`: `ψ₁(x) ≥ 2301.855 - 2654509/x` (sharp on `(2304, 2320]`). -/
theorem psiOne_lower_grid2_2304 {x : ℝ} (hx : 2304 < x) : 2301.855 - 2654509 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2304.1 psiOneGrid2_cert_2304.2.1 psiOneGrid2_cert_2304.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2304 {x : ℝ} (hx : 2304 < x) (hx' : x ≤ 2320) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2304 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2320 :
    3873280 ≤ (psiAcc 2320).2.2 ∧ 2 ^ 13833 ≤ (psiAcc 2320).2.1 ^ 8 ∧ 2 ^ 26746 ≤ (psiAcc 2320).1 ^ 8 := by
  decide +kernel

/-- For `x > 2320`: `2317.364 x - 2690334 ≤ x ψ₁(x)` (sharp on `(2320, 2336]`). -/
theorem psiOne_lower_grid2_mul_2320 {x : ℝ} (hx : 2320 < x) : 2317.364 * x - 2690334 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2320.1 psiOneGrid2_cert_2320.2.1 psiOneGrid2_cert_2320.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2320`: `ψ₁(x) ≥ 2317.364 - 2690334/x` (sharp on `(2320, 2336]`). -/
theorem psiOne_lower_grid2_2320 {x : ℝ} (hx : 2320 < x) : 2317.364 - 2690334 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2320.1 psiOneGrid2_cert_2320.2.1 psiOneGrid2_cert_2320.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2320 {x : ℝ} (hx : 2320 < x) (hx' : x ≤ 2336) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2320 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2336 :
    3925504 ≤ (psiAcc 2336).2.2 ∧ 2 ^ 24253 ≤ (psiAcc 2336).2.1 ^ 8 ∧ 2 ^ 26835 ≤ (psiAcc 2336).1 ^ 8 := by
  decide +kernel

/-- For `x > 2336`: `2325.075 x - 2708324 ≤ x ψ₁(x)` (sharp on `(2336, 2352]`). -/
theorem psiOne_lower_grid2_mul_2336 {x : ℝ} (hx : 2336 < x) : 2325.075 * x - 2708324 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2336.1 psiOneGrid2_cert_2336.2.1 psiOneGrid2_cert_2336.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2336`: `ψ₁(x) ≥ 2325.075 - 2708324/x` (sharp on `(2336, 2352]`). -/
theorem psiOne_lower_grid2_2336 {x : ℝ} (hx : 2336 < x) : 2325.075 - 2708324 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2336.1 psiOneGrid2_cert_2336.2.1 psiOneGrid2_cert_2336.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2336 {x : ℝ} (hx : 2336 < x) (hx' : x ≤ 2352) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2336 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2352 :
    3977728 ≤ (psiAcc 2352).2.2 ∧ 2 ^ 38524 ≤ (psiAcc 2352).2.1 ^ 8 ∧ 2 ^ 27194 ≤ (psiAcc 2352).1 ^ 8 := by
  decide +kernel

/-- For `x > 2352`: `2356.180 x - 2781248 ≤ x ψ₁(x)` (sharp on `(2352, 2368]`). -/
theorem psiOne_lower_grid2_mul_2352 {x : ℝ} (hx : 2352 < x) : 2356.180 * x - 2781248 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2352.1 psiOneGrid2_cert_2352.2.1 psiOneGrid2_cert_2352.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2352`: `ψ₁(x) ≥ 2356.180 - 2781248/x` (sharp on `(2352, 2368]`). -/
theorem psiOne_lower_grid2_2352 {x : ℝ} (hx : 2352 < x) : 2356.180 - 2781248 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2352.1 psiOneGrid2_cert_2352.2.1 psiOneGrid2_cert_2352.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2352 {x : ℝ} (hx : 2352 < x) (hx' : x ≤ 2368) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2352 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2368 :
    4029952 ≤ (psiAcc 2368).2.2 ∧ 2 ^ 56825 ≤ (psiAcc 2368).2.1 ^ 8 ∧ 2 ^ 27283 ≤ (psiAcc 2368).1 ^ 8 := by
  decide +kernel

/-- For `x > 2368`: `2363.891 x - 2799423 ≤ x ψ₁(x)` (sharp on `(2368, 2384]`). -/
theorem psiOne_lower_grid2_mul_2368 {x : ℝ} (hx : 2368 < x) : 2363.891 * x - 2799423 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2368.1 psiOneGrid2_cert_2368.2.1 psiOneGrid2_cert_2368.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2368`: `ψ₁(x) ≥ 2363.891 - 2799423/x` (sharp on `(2368, 2384]`). -/
theorem psiOne_lower_grid2_2368 {x : ℝ} (hx : 2368 < x) : 2363.891 - 2799423 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2368.1 psiOneGrid2_cert_2368.2.1 psiOneGrid2_cert_2368.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2368 {x : ℝ} (hx : 2368 < x) (hx' : x ≤ 2384) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2368 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2384 :
    4090880 ≤ (psiAcc 2384).2.2 ∧ 2 ^ 8096 ≤ (psiAcc 2384).2.1 ^ 8 ∧ 2 ^ 27642 ≤ (psiAcc 2384).1 ^ 8 := by
  decide +kernel

/-- For `x > 2384`: `2394.996 x - 2873389 ≤ x ψ₁(x)` (sharp on `(2384, 2400]`). -/
theorem psiOne_lower_grid2_mul_2384 {x : ℝ} (hx : 2384 < x) : 2394.996 * x - 2873389 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2384.1 psiOneGrid2_cert_2384.2.1 psiOneGrid2_cert_2384.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2384`: `ψ₁(x) ≥ 2394.996 - 2873389/x` (sharp on `(2384, 2400]`). -/
theorem psiOne_lower_grid2_2384 {x : ℝ} (hx : 2384 < x) : 2394.996 - 2873389 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2384.1 psiOneGrid2_cert_2384.2.1 psiOneGrid2_cert_2384.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2384 {x : ℝ} (hx : 2384 < x) (hx' : x ≤ 2400) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2384 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2400 :
    4143104 ≤ (psiAcc 2400).2.2 ∧ 2 ^ 34294 ≤ (psiAcc 2400).2.1 ^ 8 ∧ 2 ^ 27912 ≤ (psiAcc 2400).1 ^ 8 := by
  decide +kernel

/-- For `x > 2400`: `2418.390 x - 2929386 ≤ x ψ₁(x)` (sharp on `(2400, 2416]`). -/
theorem psiOne_lower_grid2_mul_2400 {x : ℝ} (hx : 2400 < x) : 2418.390 * x - 2929386 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2400.1 psiOneGrid2_cert_2400.2.1 psiOneGrid2_cert_2400.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2400`: `ψ₁(x) ≥ 2418.390 - 2929386/x` (sharp on `(2400, 2416]`). -/
theorem psiOne_lower_grid2_2400 {x : ℝ} (hx : 2400 < x) : 2418.390 - 2929386 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2400.1 psiOneGrid2_cert_2400.2.1 psiOneGrid2_cert_2400.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2400 {x : ℝ} (hx : 2400 < x) (hx' : x ≤ 2416) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2400 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2416 :
    4195328 ≤ (psiAcc 2416).2.2 ∧ 2 ^ 63882 ≤ (psiAcc 2416).2.1 ^ 8 ∧ 2 ^ 28024 ≤ (psiAcc 2416).1 ^ 8 := by
  decide +kernel

/-- For `x > 2416`: `2428.094 x - 2952762 ≤ x ψ₁(x)` (sharp on `(2416, 2432]`). -/
theorem psiOne_lower_grid2_mul_2416 {x : ℝ} (hx : 2416 < x) : 2428.094 * x - 2952762 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2416.1 psiOneGrid2_cert_2416.2.1 psiOneGrid2_cert_2416.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2416`: `ψ₁(x) ≥ 2428.094 - 2952762/x` (sharp on `(2416, 2432]`). -/
theorem psiOne_lower_grid2_2416 {x : ℝ} (hx : 2416 < x) : 2428.094 - 2952762 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2416.1 psiOneGrid2_cert_2416.2.1 psiOneGrid2_cert_2416.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2416 {x : ℝ} (hx : 2416 < x) (hx' : x ≤ 2432) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2416 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2432 :
    4256256 ≤ (psiAcc 2432).2.2 ∧ 2 ^ 27008 ≤ (psiAcc 2432).2.1 ^ 8 ∧ 2 ^ 28204 ≤ (psiAcc 2432).1 ^ 8 := by
  decide +kernel

/-- For `x > 2432`: `2443.690 x - 2990504 ≤ x ψ₁(x)` (sharp on `(2432, 2448]`). -/
theorem psiOne_lower_grid2_mul_2432 {x : ℝ} (hx : 2432 < x) : 2443.690 * x - 2990504 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2432.1 psiOneGrid2_cert_2432.2.1 psiOneGrid2_cert_2432.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2432`: `ψ₁(x) ≥ 2443.690 - 2990504/x` (sharp on `(2432, 2448]`). -/
theorem psiOne_lower_grid2_2432 {x : ℝ} (hx : 2432 < x) : 2443.690 - 2990504 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2432.1 psiOneGrid2_cert_2432.2.1 psiOneGrid2_cert_2432.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2432 {x : ℝ} (hx : 2432 < x) (hx' : x ≤ 2448) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2432 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2448 :
    4308480 ≤ (psiAcc 2448).2.2 ∧ 2 ^ 62196 ≤ (psiAcc 2448).2.1 ^ 8 ∧ 2 ^ 28474 ≤ (psiAcc 2448).1 ^ 8 := by
  decide +kernel

/-- For `x > 2448`: `2467.084 x - 3047623 ≤ x ψ₁(x)` (sharp on `(2448, 2464]`). -/
theorem psiOne_lower_grid2_mul_2448 {x : ℝ} (hx : 2448 < x) : 2467.084 * x - 3047623 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2448.1 psiOneGrid2_cert_2448.2.1 psiOneGrid2_cert_2448.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2448`: `ψ₁(x) ≥ 2467.084 - 3047623/x` (sharp on `(2448, 2464]`). -/
theorem psiOne_lower_grid2_2448 {x : ℝ} (hx : 2448 < x) : 2467.084 - 3047623 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2448.1 psiOneGrid2_cert_2448.2.1 psiOneGrid2_cert_2448.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2448 {x : ℝ} (hx : 2448 < x) (hx' : x ≤ 2464) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2448 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2464 :
    4369408 ≤ (psiAcc 2464).2.2 ∧ 2 ^ 30814 ≤ (psiAcc 2464).2.1 ^ 8 ∧ 2 ^ 28564 ≤ (psiAcc 2464).1 ^ 8 := by
  decide +kernel

/-- For `x > 2464`: `2474.882 x - 3066797 ≤ x ψ₁(x)` (sharp on `(2464, 2480]`). -/
theorem psiOne_lower_grid2_mul_2464 {x : ℝ} (hx : 2464 < x) : 2474.882 * x - 3066797 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2464.1 psiOneGrid2_cert_2464.2.1 psiOneGrid2_cert_2464.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2464`: `ψ₁(x) ≥ 2474.882 - 3066797/x` (sharp on `(2464, 2480]`). -/
theorem psiOne_lower_grid2_2464 {x : ℝ} (hx : 2464 < x) : 2474.882 - 3066797 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2464.1 psiOneGrid2_cert_2464.2.1 psiOneGrid2_cert_2464.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2464 {x : ℝ} (hx : 2464 < x) (hx' : x ≤ 2480) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2464 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2480 :
    4421632 ≤ (psiAcc 2480).2.2 ∧ 2 ^ 72128 ≤ (psiAcc 2480).2.1 ^ 8 ∧ 2 ^ 28835 ≤ (psiAcc 2480).1 ^ 8 := by
  decide +kernel

/-- For `x > 2480`: `2498.362 x - 3124848 ≤ x ψ₁(x)` (sharp on `(2480, 2496]`). -/
theorem psiOne_lower_grid2_mul_2480 {x : ℝ} (hx : 2480 < x) : 2498.362 * x - 3124848 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2480.1 psiOneGrid2_cert_2480.2.1 psiOneGrid2_cert_2480.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2480`: `ψ₁(x) ≥ 2498.362 - 3124848/x` (sharp on `(2480, 2496]`). -/
theorem psiOne_lower_grid2_2480 {x : ℝ} (hx : 2480 < x) : 2498.362 - 3124848 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2480.1 psiOneGrid2_cert_2480.2.1 psiOneGrid2_cert_2480.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2480 {x : ℝ} (hx : 2480 < x) (hx' : x ≤ 2496) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2480 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2496 :
    4482560 ≤ (psiAcc 2496).2.2 ∧ 2 ^ 46065 ≤ (psiAcc 2496).2.1 ^ 8 ∧ 2 ^ 28835 ≤ (psiAcc 2496).1 ^ 8 := by
  decide +kernel

/-- For `x > 2496`: `2498.362 x - 3124848 ≤ x ψ₁(x)` (sharp on `(2496, 2512]`). -/
theorem psiOne_lower_grid2_mul_2496 {x : ℝ} (hx : 2496 < x) : 2498.362 * x - 3124848 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2496.1 psiOneGrid2_cert_2496.2.1 psiOneGrid2_cert_2496.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2496`: `ψ₁(x) ≥ 2498.362 - 3124848/x` (sharp on `(2496, 2512]`). -/
theorem psiOne_lower_grid2_2496 {x : ℝ} (hx : 2496 < x) : 2498.362 - 3124848 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2496.1 psiOneGrid2_cert_2496.2.1 psiOneGrid2_cert_2496.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2496 {x : ℝ} (hx : 2496 < x) (hx' : x ≤ 2512) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2496 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2512 :
    4543488 ≤ (psiAcc 2512).2.2 ∧ 2 ^ 20815 ≤ (psiAcc 2512).2.1 ^ 8 ∧ 2 ^ 28925 ≤ (psiAcc 2512).1 ^ 8 := by
  decide +kernel

/-- For `x > 2512`: `2506.160 x - 3144366 ≤ x ψ₁(x)` (sharp on `(2512, 2528]`). -/
theorem psiOne_lower_grid2_mul_2512 {x : ℝ} (hx : 2512 < x) : 2506.160 * x - 3144366 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2512.1 psiOneGrid2_cert_2512.2.1 psiOneGrid2_cert_2512.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2512`: `ψ₁(x) ≥ 2506.160 - 3144366/x` (sharp on `(2512, 2528]`). -/
theorem psiOne_lower_grid2_2512 {x : ℝ} (hx : 2512 < x) : 2506.160 - 3144366 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2512.1 psiOneGrid2_cert_2512.2.1 psiOneGrid2_cert_2512.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2512 {x : ℝ} (hx : 2512 < x) (hx' : x ≤ 2528) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2512 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2528 :
    4595712 ≤ (psiAcc 2528).2.2 ∧ 2 ^ 66462 ≤ (psiAcc 2528).2.1 ^ 8 ∧ 2 ^ 29015 ≤ (psiAcc 2528).1 ^ 8 := by
  decide +kernel

/-- For `x > 2528`: `2513.958 x - 3164023 ≤ x ψ₁(x)` (sharp on `(2528, 2544]`). -/
theorem psiOne_lower_grid2_mul_2528 {x : ℝ} (hx : 2528 < x) : 2513.958 * x - 3164023 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2528.1 psiOneGrid2_cert_2528.2.1 psiOneGrid2_cert_2528.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2528`: `ψ₁(x) ≥ 2513.958 - 3164023/x` (sharp on `(2528, 2544]`). -/
theorem psiOne_lower_grid2_2528 {x : ℝ} (hx : 2528 < x) : 2513.958 - 3164023 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2528.1 psiOneGrid2_cert_2528.2.1 psiOneGrid2_cert_2528.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2528 {x : ℝ} (hx : 2528 < x) (hx' : x ≤ 2544) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2528 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2544 :
    4656640 ≤ (psiAcc 2544).2.2 ∧ 2 ^ 45009 ≤ (psiAcc 2544).2.1 ^ 8 ∧ 2 ^ 29287 ≤ (psiAcc 2544).1 ^ 8 := by
  decide +kernel

/-- For `x > 2544`: `2537.525 x - 3223828 ≤ x ψ₁(x)` (sharp on `(2544, 2560]`). -/
theorem psiOne_lower_grid2_mul_2544 {x : ℝ} (hx : 2544 < x) : 2537.525 * x - 3223828 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2544.1 psiOneGrid2_cert_2544.2.1 psiOneGrid2_cert_2544.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2544`: `ψ₁(x) ≥ 2537.525 - 3223828/x` (sharp on `(2544, 2560]`). -/
theorem psiOne_lower_grid2_2544 {x : ℝ} (hx : 2544 < x) : 2537.525 - 3223828 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2544.1 psiOneGrid2_cert_2544.2.1 psiOneGrid2_cert_2544.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2544 {x : ℝ} (hx : 2544 < x) (hx' : x ≤ 2560) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2544 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2560 :
    4717568 ≤ (psiAcc 2560).2.2 ∧ 2 ^ 28263 ≤ (psiAcc 2560).2.1 ^ 8 ∧ 2 ^ 29558 ≤ (psiAcc 2560).1 ^ 8 := by
  decide +kernel

/-- For `x > 2560`: `2561.005 x - 3283757 ≤ x ψ₁(x)` (sharp on `(2560, 2576]`). -/
theorem psiOne_lower_grid2_mul_2560 {x : ℝ} (hx : 2560 < x) : 2561.005 * x - 3283757 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2560.1 psiOneGrid2_cert_2560.2.1 psiOneGrid2_cert_2560.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2560`: `ψ₁(x) ≥ 2561.005 - 3283757/x` (sharp on `(2560, 2576]`). -/
theorem psiOne_lower_grid2_2560 {x : ℝ} (hx : 2560 < x) : 2561.005 - 3283757 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2560.1 psiOneGrid2_cert_2560.2.1 psiOneGrid2_cert_2560.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2560 {x : ℝ} (hx : 2560 < x) (hx' : x ≤ 2576) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2560 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2576 :
    4778496 ≤ (psiAcc 2576).2.2 ∧ 2 ^ 13780 ≤ (psiAcc 2576).2.1 ^ 8 ∧ 2 ^ 29558 ≤ (psiAcc 2576).1 ^ 8 := by
  decide +kernel

/-- For `x > 2576`: `2561.005 x - 3283756 ≤ x ψ₁(x)` (sharp on `(2576, 2592]`). -/
theorem psiOne_lower_grid2_mul_2576 {x : ℝ} (hx : 2576 < x) : 2561.005 * x - 3283756 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2576.1 psiOneGrid2_cert_2576.2.1 psiOneGrid2_cert_2576.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2576`: `ψ₁(x) ≥ 2561.005 - 3283756/x` (sharp on `(2576, 2592]`). -/
theorem psiOne_lower_grid2_2576 {x : ℝ} (hx : 2576 < x) : 2561.005 - 3283756 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2576.1 psiOneGrid2_cert_2576.2.1 psiOneGrid2_cert_2576.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2576 {x : ℝ} (hx : 2576 < x) (hx' : x ≤ 2592) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2576 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2592 :
    4830720 ≤ (psiAcc 2592).2.2 ∧ 2 ^ 70198 ≤ (psiAcc 2592).2.1 ^ 8 ∧ 2 ^ 29740 ≤ (psiAcc 2592).1 ^ 8 := by
  decide +kernel

/-- For `x > 2592`: `2576.774 x - 3324518 ≤ x ψ₁(x)` (sharp on `(2592, 2608]`). -/
theorem psiOne_lower_grid2_mul_2592 {x : ℝ} (hx : 2592 < x) : 2576.774 * x - 3324518 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2592.1 psiOneGrid2_cert_2592.2.1 psiOneGrid2_cert_2592.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2592`: `ψ₁(x) ≥ 2576.774 - 3324518/x` (sharp on `(2592, 2608]`). -/
theorem psiOne_lower_grid2_2592 {x : ℝ} (hx : 2592 < x) : 2576.774 - 3324518 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2592.1 psiOneGrid2_cert_2592.2.1 psiOneGrid2_cert_2592.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2592 {x : ℝ} (hx : 2592 < x) (hx' : x ≤ 2608) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2592 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2608 :
    4891648 ≤ (psiAcc 2608).2.2 ∧ 2 ^ 59978 ≤ (psiAcc 2608).2.1 ^ 8 ∧ 2 ^ 29830 ≤ (psiAcc 2608).1 ^ 8 := by
  decide +kernel

/-- For `x > 2608`: `2584.572 x - 3344737 ≤ x ψ₁(x)` (sharp on `(2608, 2624]`). -/
theorem psiOne_lower_grid2_mul_2608 {x : ℝ} (hx : 2608 < x) : 2584.572 * x - 3344737 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2608.1 psiOneGrid2_cert_2608.2.1 psiOneGrid2_cert_2608.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2608`: `ψ₁(x) ≥ 2584.572 - 3344737/x` (sharp on `(2608, 2624]`). -/
theorem psiOne_lower_grid2_2608 {x : ℝ} (hx : 2608 < x) : 2584.572 - 3344737 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2608.1 psiOneGrid2_cert_2608.2.1 psiOneGrid2_cert_2608.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2608 {x : ℝ} (hx : 2608 < x) (hx' : x ≤ 2624) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2608 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2624 :
    4952576 ≤ (psiAcc 2624).2.2 ∧ 2 ^ 52119 ≤ (psiAcc 2624).2.1 ^ 8 ∧ 2 ^ 30103 ≤ (psiAcc 2624).1 ^ 8 := by
  decide +kernel

/-- For `x > 2624`: `2608.226 x - 3406606 ≤ x ψ₁(x)` (sharp on `(2624, 2640]`). -/
theorem psiOne_lower_grid2_mul_2624 {x : ℝ} (hx : 2624 < x) : 2608.226 * x - 3406606 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2624.1 psiOneGrid2_cert_2624.2.1 psiOneGrid2_cert_2624.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2624`: `ψ₁(x) ≥ 2608.226 - 3406606/x` (sharp on `(2624, 2640]`). -/
theorem psiOne_lower_grid2_2624 {x : ℝ} (hx : 2624 < x) : 2608.226 - 3406606 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2624.1 psiOneGrid2_cert_2624.2.1 psiOneGrid2_cert_2624.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2624 {x : ℝ} (hx : 2624 < x) (hx' : x ≤ 2640) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2624 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2640 :
    5013504 ≤ (psiAcc 2640).2.2 ∧ 2 ^ 46986 ≤ (psiAcc 2640).2.1 ^ 8 ∧ 2 ^ 30194 ≤ (psiAcc 2640).1 ^ 8 := by
  decide +kernel

/-- For `x > 2640`: `2616.110 x - 3427366 ≤ x ψ₁(x)` (sharp on `(2640, 2656]`). -/
theorem psiOne_lower_grid2_mul_2640 {x : ℝ} (hx : 2640 < x) : 2616.110 * x - 3427366 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2640.1 psiOneGrid2_cert_2640.2.1 psiOneGrid2_cert_2640.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2640`: `ψ₁(x) ≥ 2616.110 - 3427366/x` (sharp on `(2640, 2656]`). -/
theorem psiOne_lower_grid2_2640 {x : ℝ} (hx : 2640 < x) : 2616.110 - 3427366 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2640.1 psiOneGrid2_cert_2640.2.1 psiOneGrid2_cert_2640.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2640 {x : ℝ} (hx : 2640 < x) (hx' : x ≤ 2656) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2640 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2656 :
    5074432 ≤ (psiAcc 2656).2.2 ∧ 2 ^ 43489 ≤ (psiAcc 2656).2.1 ^ 8 ∧ 2 ^ 30285 ≤ (psiAcc 2656).1 ^ 8 := by
  decide +kernel

/-- For `x > 2656`: `2623.995 x - 3448236 ≤ x ψ₁(x)` (sharp on `(2656, 2672]`). -/
theorem psiOne_lower_grid2_mul_2656 {x : ℝ} (hx : 2656 < x) : 2623.995 * x - 3448236 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2656.1 psiOneGrid2_cert_2656.2.1 psiOneGrid2_cert_2656.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2656`: `ψ₁(x) ≥ 2623.995 - 3448236/x` (sharp on `(2656, 2672]`). -/
theorem psiOne_lower_grid2_2656 {x : ℝ} (hx : 2656 < x) : 2623.995 - 3448236 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2656.1 psiOneGrid2_cert_2656.2.1 psiOneGrid2_cert_2656.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2656 {x : ℝ} (hx : 2656 < x) (hx' : x ≤ 2672) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2656 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2672 :
    5135360 ≤ (psiAcc 2672).2.2 ∧ 2 ^ 44088 ≤ (psiAcc 2672).2.1 ^ 8 ∧ 2 ^ 30649 ≤ (psiAcc 2672).1 ^ 8 := by
  decide +kernel

/-- For `x > 2672`: `2655.533 x - 3532206 ≤ x ψ₁(x)` (sharp on `(2672, 2688]`). -/
theorem psiOne_lower_grid2_mul_2672 {x : ℝ} (hx : 2672 < x) : 2655.533 * x - 3532206 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2672.1 psiOneGrid2_cert_2672.2.1 psiOneGrid2_cert_2672.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2672`: `ψ₁(x) ≥ 2655.533 - 3532206/x` (sharp on `(2672, 2688]`). -/
theorem psiOne_lower_grid2_2672 {x : ℝ} (hx : 2672 < x) : 2655.533 - 3532206 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2672.1 psiOneGrid2_cert_2672.2.1 psiOneGrid2_cert_2672.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2672 {x : ℝ} (hx : 2672 < x) (hx' : x ≤ 2688) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2672 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2688 :
    5196288 ≤ (psiAcc 2688).2.2 ∧ 2 ^ 48602 ≤ (psiAcc 2688).2.1 ^ 8 ∧ 2 ^ 30922 ≤ (psiAcc 2688).1 ^ 8 := by
  decide +kernel

/-- For `x > 2688`: `2679.187 x - 3595652 ≤ x ψ₁(x)` (sharp on `(2688, 2704]`). -/
theorem psiOne_lower_grid2_mul_2688 {x : ℝ} (hx : 2688 < x) : 2679.187 * x - 3595652 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2688.1 psiOneGrid2_cert_2688.2.1 psiOneGrid2_cert_2688.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2688`: `ψ₁(x) ≥ 2679.187 - 3595652/x` (sharp on `(2688, 2704]`). -/
theorem psiOne_lower_grid2_2688 {x : ℝ} (hx : 2688 < x) : 2679.187 - 3595652 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2688.1 psiOneGrid2_cert_2688.2.1 psiOneGrid2_cert_2688.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2688 {x : ℝ} (hx : 2688 < x) (hx' : x ≤ 2704) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2688 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2704 :
    5257216 ≤ (psiAcc 2704).2.2 ∧ 2 ^ 58768 ≤ (psiAcc 2704).2.1 ^ 8 ∧ 2 ^ 31196 ≤ (psiAcc 2704).1 ^ 8 := by
  decide +kernel

/-- For `x > 2704`: `2702.927 x - 3659600 ≤ x ψ₁(x)` (sharp on `(2704, 2720]`). -/
theorem psiOne_lower_grid2_mul_2704 {x : ℝ} (hx : 2704 < x) : 2702.927 * x - 3659600 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2704.1 psiOneGrid2_cert_2704.2.1 psiOneGrid2_cert_2704.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2704`: `ψ₁(x) ≥ 2702.927 - 3659600/x` (sharp on `(2704, 2720]`). -/
theorem psiOne_lower_grid2_2704 {x : ℝ} (hx : 2704 < x) : 2702.927 - 3659600 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2704.1 psiOneGrid2_cert_2704.2.1 psiOneGrid2_cert_2704.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2704 {x : ℝ} (hx : 2704 < x) (hx' : x ≤ 2720) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2704 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2720 :
    5318144 ≤ (psiAcc 2720).2.2 ∧ 2 ^ 73220 ≤ (psiAcc 2720).2.1 ^ 8 ∧ 2 ^ 31561 ≤ (psiAcc 2720).1 ^ 8 := by
  decide +kernel

/-- For `x > 2720`: `2734.552 x - 3745382 ≤ x ψ₁(x)` (sharp on `(2720, 2736]`). -/
theorem psiOne_lower_grid2_mul_2720 {x : ℝ} (hx : 2720 < x) : 2734.552 * x - 3745382 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2720.1 psiOneGrid2_cert_2720.2.1 psiOneGrid2_cert_2720.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2720`: `ψ₁(x) ≥ 2734.552 - 3745382/x` (sharp on `(2720, 2736]`). -/
theorem psiOne_lower_grid2_2720 {x : ℝ} (hx : 2720 < x) : 2734.552 - 3745382 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2720.1 psiOneGrid2_cert_2720.2.1 psiOneGrid2_cert_2720.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2720 {x : ℝ} (hx : 2720 < x) (hx' : x ≤ 2736) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2720 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2736 :
    5387776 ≤ (psiAcc 2736).2.2 ∧ 2 ^ 22238 ≤ (psiAcc 2736).2.1 ^ 8 ∧ 2 ^ 31743 ≤ (psiAcc 2736).1 ^ 8 := by
  decide +kernel

/-- For `x > 2736`: `2750.321 x - 3788431 ≤ x ψ₁(x)` (sharp on `(2736, 2752]`). -/
theorem psiOne_lower_grid2_mul_2736 {x : ℝ} (hx : 2736 < x) : 2750.321 * x - 3788431 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2736.1 psiOneGrid2_cert_2736.2.1 psiOneGrid2_cert_2736.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2736`: `ψ₁(x) ≥ 2750.321 - 3788431/x` (sharp on `(2736, 2752]`). -/
theorem psiOne_lower_grid2_2736 {x : ℝ} (hx : 2736 < x) : 2750.321 - 3788431 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2736.1 psiOneGrid2_cert_2736.2.1 psiOneGrid2_cert_2736.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2736 {x : ℝ} (hx : 2736 < x) (hx' : x ≤ 2752) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2736 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2752 :
    5448704 ≤ (psiAcc 2752).2.2 ∧ 2 ^ 43994 ≤ (psiAcc 2752).2.1 ^ 8 ∧ 2 ^ 31926 ≤ (psiAcc 2752).1 ^ 8 := by
  decide +kernel

/-- For `x > 2752`: `2766.177 x - 3831954 ≤ x ψ₁(x)` (sharp on `(2752, 2768]`). -/
theorem psiOne_lower_grid2_mul_2752 {x : ℝ} (hx : 2752 < x) : 2766.177 * x - 3831954 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2752.1 psiOneGrid2_cert_2752.2.1 psiOneGrid2_cert_2752.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2752`: `ψ₁(x) ≥ 2766.177 - 3831954/x` (sharp on `(2752, 2768]`). -/
theorem psiOne_lower_grid2_2752 {x : ℝ} (hx : 2752 < x) : 2766.177 - 3831954 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2752.1 psiOneGrid2_cert_2752.2.1 psiOneGrid2_cert_2752.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2752 {x : ℝ} (hx : 2752 < x) (hx' : x ≤ 2768) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2752 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2768 :
    5509632 ≤ (psiAcc 2768).2.2 ∧ 2 ^ 68858 ≤ (psiAcc 2768).2.1 ^ 8 ∧ 2 ^ 32109 ≤ (psiAcc 2768).1 ^ 8 := by
  decide +kernel

/-- For `x > 2768`: `2782.032 x - 3875715 ≤ x ψ₁(x)` (sharp on `(2768, 2784]`). -/
theorem psiOne_lower_grid2_mul_2768 {x : ℝ} (hx : 2768 < x) : 2782.032 * x - 3875715 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2768.1 psiOneGrid2_cert_2768.2.1 psiOneGrid2_cert_2768.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2768`: `ψ₁(x) ≥ 2782.032 - 3875715/x` (sharp on `(2768, 2784]`). -/
theorem psiOne_lower_grid2_2768 {x : ℝ} (hx : 2768 < x) : 2782.032 - 3875715 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2768.1 psiOneGrid2_cert_2768.2.1 psiOneGrid2_cert_2768.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2768 {x : ℝ} (hx : 2768 < x) (hx' : x ≤ 2784) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2768 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2784 :
    5579264 ≤ (psiAcc 2784).2.2 ∧ 2 ^ 26194 ≤ (psiAcc 2784).2.1 ^ 8 ∧ 2 ^ 32200 ≤ (psiAcc 2784).1 ^ 8 := by
  decide +kernel

/-- For `x > 2784`: `2789.917 x - 3897610 ≤ x ψ₁(x)` (sharp on `(2784, 2800]`). -/
theorem psiOne_lower_grid2_mul_2784 {x : ℝ} (hx : 2784 < x) : 2789.917 * x - 3897610 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2784.1 psiOneGrid2_cert_2784.2.1 psiOneGrid2_cert_2784.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2784`: `ψ₁(x) ≥ 2789.917 - 3897610/x` (sharp on `(2784, 2800]`). -/
theorem psiOne_lower_grid2_2784 {x : ℝ} (hx : 2784 < x) : 2789.917 - 3897610 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2784.1 psiOneGrid2_cert_2784.2.1 psiOneGrid2_cert_2784.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2784 {x : ℝ} (hx : 2784 < x) (hx' : x ≤ 2800) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2784 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2800 :
    5640192 ≤ (psiAcc 2800).2.2 ∧ 2 ^ 56092 ≤ (psiAcc 2800).2.1 ^ 8 ∧ 2 ^ 32475 ≤ (psiAcc 2800).1 ^ 8 := by
  decide +kernel

/-- For `x > 2800`: `2813.744 x - 3964141 ≤ x ψ₁(x)` (sharp on `(2800, 2816]`). -/
theorem psiOne_lower_grid2_mul_2800 {x : ℝ} (hx : 2800 < x) : 2813.744 * x - 3964141 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2800.1 psiOneGrid2_cert_2800.2.1 psiOneGrid2_cert_2800.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2800`: `ψ₁(x) ≥ 2813.744 - 3964141/x` (sharp on `(2800, 2816]`). -/
theorem psiOne_lower_grid2_2800 {x : ℝ} (hx : 2800 < x) : 2813.744 - 3964141 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2800.1 psiOneGrid2_cert_2800.2.1 psiOneGrid2_cert_2800.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2800 {x : ℝ} (hx : 2800 < x) (hx' : x ≤ 2816) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2800 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2816 :
    5709824 ≤ (psiAcc 2816).2.2 ∧ 2 ^ 21533 ≤ (psiAcc 2816).2.1 ^ 8 ∧ 2 ^ 32704 ≤ (psiAcc 2816).1 ^ 8 := by
  decide +kernel

/-- For `x > 2816`: `2833.585 x - 4019764 ≤ x ψ₁(x)` (sharp on `(2816, 2832]`). -/
theorem psiOne_lower_grid2_mul_2816 {x : ℝ} (hx : 2816 < x) : 2833.585 * x - 4019764 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2816.1 psiOneGrid2_cert_2816.2.1 psiOneGrid2_cert_2816.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2816`: `ψ₁(x) ≥ 2833.585 - 4019764/x` (sharp on `(2816, 2832]`). -/
theorem psiOne_lower_grid2_2816 {x : ℝ} (hx : 2816 < x) : 2833.585 - 4019764 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2816.1 psiOneGrid2_cert_2816.2.1 psiOneGrid2_cert_2816.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2816 {x : ℝ} (hx : 2816 < x) (hx' : x ≤ 2832) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2816 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2832 :
    5770752 ≤ (psiAcc 2832).2.2 ∧ 2 ^ 58577 ≤ (psiAcc 2832).2.1 ^ 8 ∧ 2 ^ 32796 ≤ (psiAcc 2832).1 ^ 8 := by
  decide +kernel

/-- For `x > 2832`: `2841.556 x - 4042234 ≤ x ψ₁(x)` (sharp on `(2832, 2848]`). -/
theorem psiOne_lower_grid2_mul_2832 {x : ℝ} (hx : 2832 < x) : 2841.556 * x - 4042234 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2832.1 psiOneGrid2_cert_2832.2.1 psiOneGrid2_cert_2832.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2832`: `ψ₁(x) ≥ 2841.556 - 4042234/x` (sharp on `(2832, 2848]`). -/
theorem psiOne_lower_grid2_2832 {x : ℝ} (hx : 2832 < x) : 2841.556 - 4042234 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2832.1 psiOneGrid2_cert_2832.2.1 psiOneGrid2_cert_2832.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2832 {x : ℝ} (hx : 2832 < x) (hx' : x ≤ 2848) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2832 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2848 :
    5840384 ≤ (psiAcc 2848).2.2 ∧ 2 ^ 29109 ≤ (psiAcc 2848).2.1 ^ 8 ∧ 2 ^ 33071 ≤ (psiAcc 2848).1 ^ 8 := by
  decide +kernel

/-- For `x > 2848`: `2865.383 x - 4109846 ≤ x ψ₁(x)` (sharp on `(2848, 2864]`). -/
theorem psiOne_lower_grid2_mul_2848 {x : ℝ} (hx : 2848 < x) : 2865.383 * x - 4109846 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2848.1 psiOneGrid2_cert_2848.2.1 psiOneGrid2_cert_2848.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2848`: `ψ₁(x) ≥ 2865.383 - 4109846/x` (sharp on `(2848, 2864]`). -/
theorem psiOne_lower_grid2_2848 {x : ℝ} (hx : 2848 < x) : 2865.383 - 4109846 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2848.1 psiOneGrid2_cert_2848.2.1 psiOneGrid2_cert_2848.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2848 {x : ℝ} (hx : 2848 < x) (hx' : x ≤ 2864) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2848 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2864 :
    5901312 ≤ (psiAcc 2864).2.2 ∧ 2 ^ 72945 ≤ (psiAcc 2864).2.1 ^ 8 ∧ 2 ^ 33347 ≤ (psiAcc 2864).1 ^ 8 := by
  decide +kernel

/-- For `x > 2864`: `2889.297 x - 4178150 ≤ x ψ₁(x)` (sharp on `(2864, 2880]`). -/
theorem psiOne_lower_grid2_mul_2864 {x : ℝ} (hx : 2864 < x) : 2889.297 * x - 4178150 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2864.1 psiOneGrid2_cert_2864.2.1 psiOneGrid2_cert_2864.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2864`: `ψ₁(x) ≥ 2889.297 - 4178150/x` (sharp on `(2864, 2880]`). -/
theorem psiOne_lower_grid2_2864 {x : ℝ} (hx : 2864 < x) : 2889.297 - 4178150 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2864.1 psiOneGrid2_cert_2864.2.1 psiOneGrid2_cert_2864.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2864 {x : ℝ} (hx : 2864 < x) (hx' : x ≤ 2880) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2864 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2880 :
    5970944 ≤ (psiAcc 2880).2.2 ∧ 2 ^ 49537 ≤ (psiAcc 2880).2.1 ^ 8 ∧ 2 ^ 33439 ≤ (psiAcc 2880).1 ^ 8 := by
  decide +kernel

/-- For `x > 2880`: `2897.268 x - 4201099 ≤ x ψ₁(x)` (sharp on `(2880, 2896]`). -/
theorem psiOne_lower_grid2_mul_2880 {x : ℝ} (hx : 2880 < x) : 2897.268 * x - 4201099 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2880.1 psiOneGrid2_cert_2880.2.1 psiOneGrid2_cert_2880.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2880`: `ψ₁(x) ≥ 2897.268 - 4201099/x` (sharp on `(2880, 2896]`). -/
theorem psiOne_lower_grid2_2880 {x : ℝ} (hx : 2880 < x) : 2897.268 - 4201099 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2880.1 psiOneGrid2_cert_2880.2.1 psiOneGrid2_cert_2880.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2880 {x : ℝ} (hx : 2880 < x) (hx' : x ≤ 2896) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2880 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2896 :
    6040576 ≤ (psiAcc 2896).2.2 ∧ 2 ^ 28336 ≤ (psiAcc 2896).2.1 ^ 8 ∧ 2 ^ 33531 ≤ (psiAcc 2896).1 ^ 8 := by
  decide +kernel

/-- For `x > 2896`: `2905.239 x - 4224112 ≤ x ψ₁(x)` (sharp on `(2896, 2912]`). -/
theorem psiOne_lower_grid2_mul_2896 {x : ℝ} (hx : 2896 < x) : 2905.239 * x - 4224112 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2896.1 psiOneGrid2_cert_2896.2.1 psiOneGrid2_cert_2896.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2896`: `ψ₁(x) ≥ 2905.239 - 4224112/x` (sharp on `(2896, 2912]`). -/
theorem psiOne_lower_grid2_2896 {x : ℝ} (hx : 2896 < x) : 2905.239 - 4224112 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2896.1 psiOneGrid2_cert_2896.2.1 psiOneGrid2_cert_2896.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2896 {x : ℝ} (hx : 2896 < x) (hx' : x ≤ 2912) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2896 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2912 :
    6110208 ≤ (psiAcc 2912).2.2 ∧ 2 ^ 10263 ≤ (psiAcc 2912).2.1 ^ 8 ∧ 2 ^ 33807 ≤ (psiAcc 2912).1 ^ 8 := by
  decide +kernel

/-- For `x > 2912`: `2929.153 x - 4293532 ≤ x ψ₁(x)` (sharp on `(2912, 2928]`). -/
theorem psiOne_lower_grid2_mul_2912 {x : ℝ} (hx : 2912 < x) : 2929.153 * x - 4293532 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2912.1 psiOneGrid2_cert_2912.2.1 psiOneGrid2_cert_2912.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2912`: `ψ₁(x) ≥ 2929.153 - 4293532/x` (sharp on `(2912, 2928]`). -/
theorem psiOne_lower_grid2_2912 {x : ℝ} (hx : 2912 < x) : 2929.153 - 4293532 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2912.1 psiOneGrid2_cert_2912.2.1 psiOneGrid2_cert_2912.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2912 {x : ℝ} (hx : 2912 < x) (hx' : x ≤ 2928) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2912 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2928 :
    6171136 ≤ (psiAcc 2928).2.2 ∧ 2 ^ 64859 ≤ (psiAcc 2928).2.1 ^ 8 ∧ 2 ^ 33991 ≤ (psiAcc 2928).1 ^ 8 := by
  decide +kernel

/-- For `x > 2928`: `2945.095 x - 4340116 ≤ x ψ₁(x)` (sharp on `(2928, 2944]`). -/
theorem psiOne_lower_grid2_mul_2928 {x : ℝ} (hx : 2928 < x) : 2945.095 * x - 4340116 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2928.1 psiOneGrid2_cert_2928.2.1 psiOneGrid2_cert_2928.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2928`: `ψ₁(x) ≥ 2945.095 - 4340116/x` (sharp on `(2928, 2944]`). -/
theorem psiOne_lower_grid2_2928 {x : ℝ} (hx : 2928 < x) : 2945.095 - 4340116 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2928.1 psiOneGrid2_cert_2928.2.1 psiOneGrid2_cert_2928.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2928 {x : ℝ} (hx : 2928 < x) (hx' : x ≤ 2944) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2928 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2944 :
    6240768 ≤ (psiAcc 2944).2.2 ∧ 2 ^ 52127 ≤ (psiAcc 2944).2.1 ^ 8 ∧ 2 ^ 34083 ≤ (psiAcc 2944).1 ^ 8 := by
  decide +kernel

/-- For `x > 2944`: `2953.066 x - 4363542 ≤ x ψ₁(x)` (sharp on `(2944, 2960]`). -/
theorem psiOne_lower_grid2_mul_2944 {x : ℝ} (hx : 2944 < x) : 2953.066 * x - 4363542 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2944.1 psiOneGrid2_cert_2944.2.1 psiOneGrid2_cert_2944.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2944`: `ψ₁(x) ≥ 2953.066 - 4363542/x` (sharp on `(2944, 2960]`). -/
theorem psiOne_lower_grid2_2944 {x : ℝ} (hx : 2944 < x) : 2953.066 - 4363542 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2944.1 psiOneGrid2_cert_2944.2.1 psiOneGrid2_cert_2944.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2944 {x : ℝ} (hx : 2944 < x) (hx' : x ≤ 2960) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2944 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2960 :
    6310400 ≤ (psiAcc 2960).2.2 ∧ 2 ^ 41331 ≤ (psiAcc 2960).2.1 ^ 8 ∧ 2 ^ 34268 ≤ (psiAcc 2960).1 ^ 8 := by
  decide +kernel

/-- For `x > 2960`: `2969.095 x - 4410907 ≤ x ψ₁(x)` (sharp on `(2960, 2976]`). -/
theorem psiOne_lower_grid2_mul_2960 {x : ℝ} (hx : 2960 < x) : 2969.095 * x - 4410907 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2960.1 psiOneGrid2_cert_2960.2.1 psiOneGrid2_cert_2960.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2960`: `ψ₁(x) ≥ 2969.095 - 4410907/x` (sharp on `(2960, 2976]`). -/
theorem psiOne_lower_grid2_2960 {x : ℝ} (hx : 2960 < x) : 2969.095 - 4410907 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2960.1 psiOneGrid2_cert_2960.2.1 psiOneGrid2_cert_2960.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2960 {x : ℝ} (hx : 2960 < x) (hx' : x ≤ 2976) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2960 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2976 :
    6380032 ≤ (psiAcc 2976).2.2 ∧ 2 ^ 34871 ≤ (psiAcc 2976).2.1 ^ 8 ∧ 2 ^ 34544 ≤ (psiAcc 2976).1 ^ 8 := by
  decide +kernel

/-- For `x > 2976`: `2993.009 x - 4481874 ≤ x ψ₁(x)` (sharp on `(2976, 2992]`). -/
theorem psiOne_lower_grid2_mul_2976 {x : ℝ} (hx : 2976 < x) : 2993.009 * x - 4481874 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2976.1 psiOneGrid2_cert_2976.2.1 psiOneGrid2_cert_2976.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2976`: `ψ₁(x) ≥ 2993.009 - 4481874/x` (sharp on `(2976, 2992]`). -/
theorem psiOne_lower_grid2_2976 {x : ℝ} (hx : 2976 < x) : 2993.009 - 4481874 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2976.1 psiOneGrid2_cert_2976.2.1 psiOneGrid2_cert_2976.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2976 {x : ℝ} (hx : 2976 < x) (hx' : x ≤ 2992) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2976 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_2992 :
    6449664 ≤ (psiAcc 2992).2.2 ∧ 2 ^ 30534 ≤ (psiAcc 2992).2.1 ^ 8 ∧ 2 ^ 34544 ≤ (psiAcc 2992).1 ^ 8 := by
  decide +kernel

/-- For `x > 2992`: `2993.009 x - 4481873 ≤ x ψ₁(x)` (sharp on `(2992, 3008]`). -/
theorem psiOne_lower_grid2_mul_2992 {x : ℝ} (hx : 2992 < x) : 2993.009 * x - 4481873 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_2992.1 psiOneGrid2_cert_2992.2.1 psiOneGrid2_cert_2992.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 2992`: `ψ₁(x) ≥ 2993.009 - 4481873/x` (sharp on `(2992, 3008]`). -/
theorem psiOne_lower_grid2_2992 {x : ℝ} (hx : 2992 < x) : 2993.009 - 4481873 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_2992.1 psiOneGrid2_cert_2992.2.1 psiOneGrid2_cert_2992.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_2992 {x : ℝ} (hx : 2992 < x) (hx' : x ≤ 3008) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_2992 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3008 :
    6519296 ≤ (psiAcc 3008).2.2 ∧ 2 ^ 27675 ≤ (psiAcc 3008).2.1 ^ 8 ∧ 2 ^ 34729 ≤ (psiAcc 3008).1 ^ 8 := by
  decide +kernel

/-- For `x > 3008`: `3009.038 x - 4529959 ≤ x ψ₁(x)` (sharp on `(3008, 3024]`). -/
theorem psiOne_lower_grid2_mul_3008 {x : ℝ} (hx : 3008 < x) : 3009.038 * x - 4529959 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3008.1 psiOneGrid2_cert_3008.2.1 psiOneGrid2_cert_3008.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3008`: `ψ₁(x) ≥ 3009.038 - 4529959/x` (sharp on `(3008, 3024]`). -/
theorem psiOne_lower_grid2_3008 {x : ℝ} (hx : 3008 < x) : 3009.038 - 4529959 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3008.1 psiOneGrid2_cert_3008.2.1 psiOneGrid2_cert_3008.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3008 {x : ℝ} (hx : 3008 < x) (hx' : x ≤ 3024) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3008 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3024 :
    6588928 ≤ (psiAcc 3024).2.2 ∧ 2 ^ 28051 ≤ (psiAcc 3024).2.1 ^ 8 ∧ 2 ^ 35007 ≤ (psiAcc 3024).1 ^ 8 := by
  decide +kernel

/-- For `x > 3024`: `3033.125 x - 4602644 ≤ x ψ₁(x)` (sharp on `(3024, 3040]`). -/
theorem psiOne_lower_grid2_mul_3024 {x : ℝ} (hx : 3024 < x) : 3033.125 * x - 4602644 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3024.1 psiOneGrid2_cert_3024.2.1 psiOneGrid2_cert_3024.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3024`: `ψ₁(x) ≥ 3033.125 - 4602644/x` (sharp on `(3024, 3040]`). -/
theorem psiOne_lower_grid2_3024 {x : ℝ} (hx : 3024 < x) : 3033.125 - 4602644 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3024.1 psiOneGrid2_cert_3024.2.1 psiOneGrid2_cert_3024.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3024 {x : ℝ} (hx : 3024 < x) (hx' : x ≤ 3040) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3024 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3040 :
    6658560 ≤ (psiAcc 3040).2.2 ∧ 2 ^ 31387 ≤ (psiAcc 3040).2.1 ^ 8 ∧ 2 ^ 35099 ≤ (psiAcc 3040).1 ^ 8 := by
  decide +kernel

/-- For `x > 3040`: `3041.096 x - 4626853 ≤ x ψ₁(x)` (sharp on `(3040, 3056]`). -/
theorem psiOne_lower_grid2_mul_3040 {x : ℝ} (hx : 3040 < x) : 3041.096 * x - 4626853 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3040.1 psiOneGrid2_cert_3040.2.1 psiOneGrid2_cert_3040.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3040`: `ψ₁(x) ≥ 3041.096 - 4626853/x` (sharp on `(3040, 3056]`). -/
theorem psiOne_lower_grid2_3040 {x : ℝ} (hx : 3040 < x) : 3041.096 - 4626853 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3040.1 psiOneGrid2_cert_3040.2.1 psiOneGrid2_cert_3040.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3040 {x : ℝ} (hx : 3040 < x) (hx' : x ≤ 3056) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3040 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3056 :
    6728192 ≤ (psiAcc 3056).2.2 ∧ 2 ^ 37963 ≤ (psiAcc 3056).2.1 ^ 8 ∧ 2 ^ 35284 ≤ (psiAcc 3056).1 ^ 8 := by
  decide +kernel

/-- For `x > 3056`: `3057.125 x - 4675660 ≤ x ψ₁(x)` (sharp on `(3056, 3072]`). -/
theorem psiOne_lower_grid2_mul_3056 {x : ℝ} (hx : 3056 < x) : 3057.125 * x - 4675660 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3056.1 psiOneGrid2_cert_3056.2.1 psiOneGrid2_cert_3056.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3056`: `ψ₁(x) ≥ 3057.125 - 4675660/x` (sharp on `(3056, 3072]`). -/
theorem psiOne_lower_grid2_3056 {x : ℝ} (hx : 3056 < x) : 3057.125 - 4675660 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3056.1 psiOneGrid2_cert_3056.2.1 psiOneGrid2_cert_3056.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3056 {x : ℝ} (hx : 3056 < x) (hx' : x ≤ 3072) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3056 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3072 :
    6797824 ≤ (psiAcc 3072).2.2 ∧ 2 ^ 46947 ≤ (psiAcc 3072).2.1 ^ 8 ∧ 2 ^ 35470 ≤ (psiAcc 3072).1 ^ 8 := by
  decide +kernel

/-- For `x > 3072`: `3073.241 x - 4725038 ≤ x ψ₁(x)` (sharp on `(3072, 3088]`). -/
theorem psiOne_lower_grid2_mul_3072 {x : ℝ} (hx : 3072 < x) : 3073.241 * x - 4725038 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3072.1 psiOneGrid2_cert_3072.2.1 psiOneGrid2_cert_3072.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3072`: `ψ₁(x) ≥ 3073.241 - 4725038/x` (sharp on `(3072, 3088]`). -/
theorem psiOne_lower_grid2_3072 {x : ℝ} (hx : 3072 < x) : 3073.241 - 4725038 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3072.1 psiOneGrid2_cert_3072.2.1 psiOneGrid2_cert_3072.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3072 {x : ℝ} (hx : 3072 < x) (hx' : x ≤ 3088) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3072 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3088 :
    6867456 ≤ (psiAcc 3088).2.2 ∧ 2 ^ 58711 ≤ (psiAcc 3088).2.1 ^ 8 ∧ 2 ^ 35655 ≤ (psiAcc 3088).1 ^ 8 := by
  decide +kernel

/-- For `x > 3088`: `3089.270 x - 4774423 ≤ x ψ₁(x)` (sharp on `(3088, 3104]`). -/
theorem psiOne_lower_grid2_mul_3088 {x : ℝ} (hx : 3088 < x) : 3089.270 * x - 4774423 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3088.1 psiOneGrid2_cert_3088.2.1 psiOneGrid2_cert_3088.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3088`: `ψ₁(x) ≥ 3089.270 - 4774423/x` (sharp on `(3088, 3104]`). -/
theorem psiOne_lower_grid2_3088 {x : ℝ} (hx : 3088 < x) : 3089.270 - 4774423 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3088.1 psiOneGrid2_cert_3088.2.1 psiOneGrid2_cert_3088.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3088 {x : ℝ} (hx : 3088 < x) (hx' : x ≤ 3104) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3088 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3104 :
    6937088 ≤ (psiAcc 3104).2.2 ∧ 2 ^ 73535 ≤ (psiAcc 3104).2.1 ^ 8 ∧ 2 ^ 35748 ≤ (psiAcc 3104).1 ^ 8 := by
  decide +kernel

/-- For `x > 3104`: `3097.328 x - 4799313 ≤ x ψ₁(x)` (sharp on `(3104, 3120]`). -/
theorem psiOne_lower_grid2_mul_3104 {x : ℝ} (hx : 3104 < x) : 3097.328 * x - 4799313 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3104.1 psiOneGrid2_cert_3104.2.1 psiOneGrid2_cert_3104.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3104`: `ψ₁(x) ≥ 3097.328 - 4799313/x` (sharp on `(3104, 3120]`). -/
theorem psiOne_lower_grid2_3104 {x : ℝ} (hx : 3104 < x) : 3097.328 - 4799313 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3104.1 psiOneGrid2_cert_3104.2.1 psiOneGrid2_cert_3104.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3104 {x : ℝ} (hx : 3104 < x) (hx' : x ≤ 3120) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3104 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3120 :
    7015424 ≤ (psiAcc 3120).2.2 ∧ 2 ^ 19934 ≤ (psiAcc 3120).2.1 ^ 8 ∧ 2 ^ 35933 ≤ (psiAcc 3120).1 ^ 8 := by
  decide +kernel

/-- For `x > 3120`: `3113.357 x - 4849226 ≤ x ψ₁(x)` (sharp on `(3120, 3136]`). -/
theorem psiOne_lower_grid2_mul_3120 {x : ℝ} (hx : 3120 < x) : 3113.357 * x - 4849226 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3120.1 psiOneGrid2_cert_3120.2.1 psiOneGrid2_cert_3120.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3120`: `ψ₁(x) ≥ 3113.357 - 4849226/x` (sharp on `(3120, 3136]`). -/
theorem psiOne_lower_grid2_3120 {x : ℝ} (hx : 3120 < x) : 3113.357 - 4849226 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3120.1 psiOneGrid2_cert_3120.2.1 psiOneGrid2_cert_3120.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3120 {x : ℝ} (hx : 3120 < x) (hx' : x ≤ 3136) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3120 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3136 :
    7085056 ≤ (psiAcc 3136).2.2 ∧ 2 ^ 39420 ≤ (psiAcc 3136).2.1 ^ 8 ∧ 2 ^ 36045 ≤ (psiAcc 3136).1 ^ 8 := by
  decide +kernel

/-- For `x > 3136`: `3123.061 x - 4879519 ≤ x ψ₁(x)` (sharp on `(3136, 3152]`). -/
theorem psiOne_lower_grid2_mul_3136 {x : ℝ} (hx : 3136 < x) : 3123.061 * x - 4879519 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3136.1 psiOneGrid2_cert_3136.2.1 psiOneGrid2_cert_3136.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3136`: `ψ₁(x) ≥ 3123.061 - 4879519/x` (sharp on `(3136, 3152]`). -/
theorem psiOne_lower_grid2_3136 {x : ℝ} (hx : 3136 < x) : 3123.061 - 4879519 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3136.1 psiOneGrid2_cert_3136.2.1 psiOneGrid2_cert_3136.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3136 {x : ℝ} (hx : 3136 < x) (hx' : x ≤ 3152) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3136 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3152 :
    7154688 ≤ (psiAcc 3152).2.2 ∧ 2 ^ 60484 ≤ (psiAcc 3152).2.1 ^ 8 ∧ 2 ^ 36138 ≤ (psiAcc 3152).1 ^ 8 := by
  decide +kernel

/-- For `x > 3152`: `3131.119 x - 4904796 ≤ x ψ₁(x)` (sharp on `(3152, 3168]`). -/
theorem psiOne_lower_grid2_mul_3152 {x : ℝ} (hx : 3152 < x) : 3131.119 * x - 4904796 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3152.1 psiOneGrid2_cert_3152.2.1 psiOneGrid2_cert_3152.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3152`: `ψ₁(x) ≥ 3131.119 - 4904796/x` (sharp on `(3152, 3168]`). -/
theorem psiOne_lower_grid2_3152 {x : ℝ} (hx : 3152 < x) : 3131.119 - 4904796 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3152.1 psiOneGrid2_cert_3152.2.1 psiOneGrid2_cert_3152.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3152 {x : ℝ} (hx : 3152 < x) (hx' : x ≤ 3168) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3152 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3168 :
    7233024 ≤ (psiAcc 3168).2.2 ∧ 2 ^ 12568 ≤ (psiAcc 3168).2.1 ^ 8 ∧ 2 ^ 36324 ≤ (psiAcc 3168).1 ^ 8 := by
  decide +kernel

/-- For `x > 3168`: `3147.234 x - 4955801 ≤ x ψ₁(x)` (sharp on `(3168, 3184]`). -/
theorem psiOne_lower_grid2_mul_3168 {x : ℝ} (hx : 3168 < x) : 3147.234 * x - 4955801 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3168.1 psiOneGrid2_cert_3168.2.1 psiOneGrid2_cert_3168.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3168`: `ψ₁(x) ≥ 3147.234 - 4955801/x` (sharp on `(3168, 3184]`). -/
theorem psiOne_lower_grid2_3168 {x : ℝ} (hx : 3168 < x) : 3147.234 - 4955801 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3168.1 psiOneGrid2_cert_3168.2.1 psiOneGrid2_cert_3168.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3168 {x : ℝ} (hx : 3168 < x) (hx' : x ≤ 3184) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3168 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3184 :
    7302656 ≤ (psiAcc 3184).2.2 ∧ 2 ^ 38377 ≤ (psiAcc 3184).2.1 ^ 8 ∧ 2 ^ 36510 ≤ (psiAcc 3184).1 ^ 8 := by
  decide +kernel

/-- For `x > 3184`: `3163.350 x - 5006968 ≤ x ψ₁(x)` (sharp on `(3184, 3200]`). -/
theorem psiOne_lower_grid2_mul_3184 {x : ℝ} (hx : 3184 < x) : 3163.350 * x - 5006968 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3184.1 psiOneGrid2_cert_3184.2.1 psiOneGrid2_cert_3184.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3184`: `ψ₁(x) ≥ 3163.350 - 5006968/x` (sharp on `(3184, 3200]`). -/
theorem psiOne_lower_grid2_3184 {x : ℝ} (hx : 3184 < x) : 3163.350 - 5006968 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3184.1 psiOneGrid2_cert_3184.2.1 psiOneGrid2_cert_3184.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3184 {x : ℝ} (hx : 3184 < x) (hx' : x ≤ 3200) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3184 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3200 :
    7372288 ≤ (psiAcc 3200).2.2 ∧ 2 ^ 67538 ≤ (psiAcc 3200).2.1 ^ 8 ∧ 2 ^ 36696 ≤ (psiAcc 3200).1 ^ 8 := by
  decide +kernel

/-- For `x > 3200`: `3179.466 x - 5058360 ≤ x ψ₁(x)` (sharp on `(3200, 3216]`). -/
theorem psiOne_lower_grid2_mul_3200 {x : ℝ} (hx : 3200 < x) : 3179.466 * x - 5058360 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3200.1 psiOneGrid2_cert_3200.2.1 psiOneGrid2_cert_3200.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3200`: `ψ₁(x) ≥ 3179.466 - 5058360/x` (sharp on `(3200, 3216]`). -/
theorem psiOne_lower_grid2_3200 {x : ℝ} (hx : 3200 < x) : 3179.466 - 5058360 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3200.1 psiOneGrid2_cert_3200.2.1 psiOneGrid2_cert_3200.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3200 {x : ℝ} (hx : 3200 < x) (hx' : x ≤ 3216) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3200 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3216 :
    7450624 ≤ (psiAcc 3216).2.2 ∧ 2 ^ 29861 ≤ (psiAcc 3216).2.1 ^ 8 ∧ 2 ^ 36883 ≤ (psiAcc 3216).1 ^ 8 := by
  decide +kernel

/-- For `x > 3216`: `3195.668 x - 5110304 ≤ x ψ₁(x)` (sharp on `(3216, 3232]`). -/
theorem psiOne_lower_grid2_mul_3216 {x : ℝ} (hx : 3216 < x) : 3195.668 * x - 5110304 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3216.1 psiOneGrid2_cert_3216.2.1 psiOneGrid2_cert_3216.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3216`: `ψ₁(x) ≥ 3195.668 - 5110304/x` (sharp on `(3216, 3232]`). -/
theorem psiOne_lower_grid2_3216 {x : ℝ} (hx : 3216 < x) : 3195.668 - 5110304 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3216.1 psiOneGrid2_cert_3216.2.1 psiOneGrid2_cert_3216.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3216 {x : ℝ} (hx : 3216 < x) (hx' : x ≤ 3232) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3216 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3232 :
    7520256 ≤ (psiAcc 3232).2.2 ∧ 2 ^ 65638 ≤ (psiAcc 3232).2.1 ^ 8 ∧ 2 ^ 37162 ≤ (psiAcc 3232).1 ^ 8 := by
  decide +kernel

/-- For `x > 3232`: `3219.841 x - 5188198 ≤ x ψ₁(x)` (sharp on `(3232, 3248]`). -/
theorem psiOne_lower_grid2_mul_3232 {x : ℝ} (hx : 3232 < x) : 3219.841 * x - 5188198 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3232.1 psiOneGrid2_cert_3232.2.1 psiOneGrid2_cert_3232.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3232`: `ψ₁(x) ≥ 3219.841 - 5188198/x` (sharp on `(3232, 3248]`). -/
theorem psiOne_lower_grid2_3232 {x : ℝ} (hx : 3232 < x) : 3219.841 - 5188198 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3232.1 psiOneGrid2_cert_3232.2.1 psiOneGrid2_cert_3232.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3232 {x : ℝ} (hx : 3232 < x) (hx' : x ≤ 3248) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3232 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3248 :
    7598592 ≤ (psiAcc 3248).2.2 ∧ 2 ^ 33554 ≤ (psiAcc 3248).2.1 ^ 8 ∧ 2 ^ 37162 ≤ (psiAcc 3248).1 ^ 8 := by
  decide +kernel

/-- For `x > 3248`: `3219.841 x - 5188197 ≤ x ψ₁(x)` (sharp on `(3248, 3264]`). -/
theorem psiOne_lower_grid2_mul_3248 {x : ℝ} (hx : 3248 < x) : 3219.841 * x - 5188197 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3248.1 psiOneGrid2_cert_3248.2.1 psiOneGrid2_cert_3248.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3248`: `ψ₁(x) ≥ 3219.841 - 5188197/x` (sharp on `(3248, 3264]`). -/
theorem psiOne_lower_grid2_3248 {x : ℝ} (hx : 3248 < x) : 3219.841 - 5188197 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3248.1 psiOneGrid2_cert_3248.2.1 psiOneGrid2_cert_3248.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3248 {x : ℝ} (hx : 3248 < x) (hx' : x ≤ 3264) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3248 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3264 :
    7676928 ≤ (psiAcc 3264).2.2 ∧ 2 ^ 4831 ≤ (psiAcc 3264).2.1 ^ 8 ∧ 2 ^ 37536 ≤ (psiAcc 3264).1 ^ 8 := by
  decide +kernel

/-- For `x > 3264`: `3252.246 x - 5293674 ≤ x ψ₁(x)` (sharp on `(3264, 3280]`). -/
theorem psiOne_lower_grid2_mul_3264 {x : ℝ} (hx : 3264 < x) : 3252.246 * x - 5293674 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3264.1 psiOneGrid2_cert_3264.2.1 psiOneGrid2_cert_3264.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3264`: `ψ₁(x) ≥ 3252.246 - 5293674/x` (sharp on `(3264, 3280]`). -/
theorem psiOne_lower_grid2_3264 {x : ℝ} (hx : 3264 < x) : 3252.246 - 5293674 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3264.1 psiOneGrid2_cert_3264.2.1 psiOneGrid2_cert_3264.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3264 {x : ℝ} (hx : 3264 < x) (hx' : x ≤ 3280) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3264 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3280 :
    7746560 ≤ (psiAcc 3280).2.2 ∧ 2 ^ 49195 ≤ (psiAcc 3280).2.1 ^ 8 ∧ 2 ^ 37629 ≤ (psiAcc 3280).1 ^ 8 := by
  decide +kernel

/-- For `x > 3280`: `3260.304 x - 5320030 ≤ x ψ₁(x)` (sharp on `(3280, 3296]`). -/
theorem psiOne_lower_grid2_mul_3280 {x : ℝ} (hx : 3280 < x) : 3260.304 * x - 5320030 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3280.1 psiOneGrid2_cert_3280.2.1 psiOneGrid2_cert_3280.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3280`: `ψ₁(x) ≥ 3260.304 - 5320030/x` (sharp on `(3280, 3296]`). -/
theorem psiOne_lower_grid2_3280 {x : ℝ} (hx : 3280 < x) : 3260.304 - 5320030 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3280.1 psiOneGrid2_cert_3280.2.1 psiOneGrid2_cert_3280.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3280 {x : ℝ} (hx : 3280 < x) (hx' : x ≤ 3296) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3280 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3296 :
    7824896 ≤ (psiAcc 3296).2.2 ∧ 2 ^ 24580 ≤ (psiAcc 3296).2.1 ^ 8 ∧ 2 ^ 37629 ≤ (psiAcc 3296).1 ^ 8 := by
  decide +kernel

/-- For `x > 3296`: `3260.304 x - 5320030 ≤ x ψ₁(x)` (sharp on `(3296, 3312]`). -/
theorem psiOne_lower_grid2_mul_3296 {x : ℝ} (hx : 3296 < x) : 3260.304 * x - 5320030 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3296.1 psiOneGrid2_cert_3296.2.1 psiOneGrid2_cert_3296.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3296`: `ψ₁(x) ≥ 3260.304 - 5320030/x` (sharp on `(3296, 3312]`). -/
theorem psiOne_lower_grid2_3296 {x : ℝ} (hx : 3296 < x) : 3260.304 - 5320030 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3296.1 psiOneGrid2_cert_3296.2.1 psiOneGrid2_cert_3296.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3296 {x : ℝ} (hx : 3296 < x) (hx' : x ≤ 3312) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3296 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3312 :
    7894528 ≤ (psiAcc 3312).2.2 ∧ 2 ^ 72309 ≤ (psiAcc 3312).2.1 ^ 8 ∧ 2 ^ 37910 ≤ (psiAcc 3312).1 ^ 8 := by
  decide +kernel

/-- For `x > 3312`: `3284.651 x - 5400430 ≤ x ψ₁(x)` (sharp on `(3312, 3328]`). -/
theorem psiOne_lower_grid2_mul_3312 {x : ℝ} (hx : 3312 < x) : 3284.651 * x - 5400430 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3312.1 psiOneGrid2_cert_3312.2.1 psiOneGrid2_cert_3312.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3312`: `ψ₁(x) ≥ 3284.651 - 5400430/x` (sharp on `(3312, 3328]`). -/
theorem psiOne_lower_grid2_3312 {x : ℝ} (hx : 3312 < x) : 3284.651 - 5400430 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3312.1 psiOneGrid2_cert_3312.2.1 psiOneGrid2_cert_3312.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3312 {x : ℝ} (hx : 3312 < x) (hx' : x ≤ 3328) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3312 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3328 :
    7972864 ≤ (psiAcc 3328).2.2 ∧ 2 ^ 54896 ≤ (psiAcc 3328).2.1 ^ 8 ∧ 2 ^ 38190 ≤ (psiAcc 3328).1 ^ 8 := by
  decide +kernel

/-- For `x > 3328`: `3308.911 x - 5480933 ≤ x ψ₁(x)` (sharp on `(3328, 3344]`). -/
theorem psiOne_lower_grid2_mul_3328 {x : ℝ} (hx : 3328 < x) : 3308.911 * x - 5480933 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3328.1 psiOneGrid2_cert_3328.2.1 psiOneGrid2_cert_3328.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3328`: `ψ₁(x) ≥ 3308.911 - 5480933/x` (sharp on `(3328, 3344]`). -/
theorem psiOne_lower_grid2_3328 {x : ℝ} (hx : 3328 < x) : 3308.911 - 5480933 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3328.1 psiOneGrid2_cert_3328.2.1 psiOneGrid2_cert_3328.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3328 {x : ℝ} (hx : 3328 < x) (hx' : x ≤ 3344) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3328 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3344 :
    8051200 ≤ (psiAcc 3344).2.2 ∧ 2 ^ 41976 ≤ (psiAcc 3344).2.1 ^ 8 ∧ 2 ^ 38471 ≤ (psiAcc 3344).1 ^ 8 := by
  decide +kernel

/-- For `x > 3344`: `3333.258 x - 5562112 ≤ x ψ₁(x)` (sharp on `(3344, 3360]`). -/
theorem psiOne_lower_grid2_mul_3344 {x : ℝ} (hx : 3344 < x) : 3333.258 * x - 5562112 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3344.1 psiOneGrid2_cert_3344.2.1 psiOneGrid2_cert_3344.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3344`: `ψ₁(x) ≥ 3333.258 - 5562112/x` (sharp on `(3344, 3360]`). -/
theorem psiOne_lower_grid2_3344 {x : ℝ} (hx : 3344 < x) : 3333.258 - 5562112 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3344.1 psiOneGrid2_cert_3344.2.1 psiOneGrid2_cert_3344.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3344 {x : ℝ} (hx : 3344 < x) (hx' : x ≤ 3360) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3344 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3360 :
    8129536 ≤ (psiAcc 3360).2.2 ∧ 2 ^ 32147 ≤ (psiAcc 3360).2.1 ^ 8 ∧ 2 ^ 38659 ≤ (psiAcc 3360).1 ^ 8 := by
  decide +kernel

/-- For `x > 3360`: `3349.547 x - 5616728 ≤ x ψ₁(x)` (sharp on `(3360, 3376]`). -/
theorem psiOne_lower_grid2_mul_3360 {x : ℝ} (hx : 3360 < x) : 3349.547 * x - 5616728 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3360.1 psiOneGrid2_cert_3360.2.1 psiOneGrid2_cert_3360.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3360`: `ψ₁(x) ≥ 3349.547 - 5616728/x` (sharp on `(3360, 3376]`). -/
theorem psiOne_lower_grid2_3360 {x : ℝ} (hx : 3360 < x) : 3349.547 - 5616728 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3360.1 psiOneGrid2_cert_3360.2.1 psiOneGrid2_cert_3360.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3360 {x : ℝ} (hx : 3360 < x) (hx' : x ≤ 3376) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3360 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3376 :
    8207872 ≤ (psiAcc 3376).2.2 ∧ 2 ^ 26160 ≤ (psiAcc 3376).2.1 ^ 8 ∧ 2 ^ 38940 ≤ (psiAcc 3376).1 ^ 8 := by
  decide +kernel

/-- For `x > 3376`: `3373.893 x - 5698736 ≤ x ψ₁(x)` (sharp on `(3376, 3392]`). -/
theorem psiOne_lower_grid2_mul_3376 {x : ℝ} (hx : 3376 < x) : 3373.893 * x - 5698736 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3376.1 psiOneGrid2_cert_3376.2.1 psiOneGrid2_cert_3376.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3376`: `ψ₁(x) ≥ 3373.893 - 5698736/x` (sharp on `(3376, 3392]`). -/
theorem psiOne_lower_grid2_3376 {x : ℝ} (hx : 3376 < x) : 3373.893 - 5698736 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3376.1 psiOneGrid2_cert_3376.2.1 psiOneGrid2_cert_3376.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3376 {x : ℝ} (hx : 3376 < x) (hx' : x ≤ 3392) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3376 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3392 :
    8286208 ≤ (psiAcc 3392).2.2 ∧ 2 ^ 22892 ≤ (psiAcc 3392).2.1 ^ 8 ∧ 2 ^ 39127 ≤ (psiAcc 3392).1 ^ 8 := by
  decide +kernel

/-- For `x > 3392`: `3390.096 x - 5753662 ≤ x ψ₁(x)` (sharp on `(3392, 3408]`). -/
theorem psiOne_lower_grid2_mul_3392 {x : ℝ} (hx : 3392 < x) : 3390.096 * x - 5753662 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3392.1 psiOneGrid2_cert_3392.2.1 psiOneGrid2_cert_3392.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3392`: `ψ₁(x) ≥ 3390.096 - 5753662/x` (sharp on `(3392, 3408]`). -/
theorem psiOne_lower_grid2_3392 {x : ℝ} (hx : 3392 < x) : 3390.096 - 5753662 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3392.1 psiOneGrid2_cert_3392.2.1 psiOneGrid2_cert_3392.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3392 {x : ℝ} (hx : 3392 < x) (hx' : x ≤ 3408) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3392 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3408 :
    8364544 ≤ (psiAcc 3408).2.2 ∧ 2 ^ 22345 ≤ (psiAcc 3408).2.1 ^ 8 ∧ 2 ^ 39221 ≤ (psiAcc 3408).1 ^ 8 := by
  decide +kernel

/-- For `x > 3408`: `3398.240 x - 5781409 ≤ x ψ₁(x)` (sharp on `(3408, 3424]`). -/
theorem psiOne_lower_grid2_mul_3408 {x : ℝ} (hx : 3408 < x) : 3398.240 * x - 5781409 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3408.1 psiOneGrid2_cert_3408.2.1 psiOneGrid2_cert_3408.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3408`: `ψ₁(x) ≥ 3398.240 - 5781409/x` (sharp on `(3408, 3424]`). -/
theorem psiOne_lower_grid2_3408 {x : ℝ} (hx : 3408 < x) : 3398.240 - 5781409 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3408.1 psiOneGrid2_cert_3408.2.1 psiOneGrid2_cert_3408.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3408 {x : ℝ} (hx : 3408 < x) (hx' : x ≤ 3424) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3408 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3424 :
    8442880 ≤ (psiAcc 3424).2.2 ∧ 2 ^ 24239 ≤ (psiAcc 3424).2.1 ^ 8 ∧ 2 ^ 39315 ≤ (psiAcc 3424).1 ^ 8 := by
  decide +kernel

/-- For `x > 3424`: `3406.385 x - 5809205 ≤ x ψ₁(x)` (sharp on `(3424, 3440]`). -/
theorem psiOne_lower_grid2_mul_3424 {x : ℝ} (hx : 3424 < x) : 3406.385 * x - 5809205 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3424.1 psiOneGrid2_cert_3424.2.1 psiOneGrid2_cert_3424.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3424`: `ψ₁(x) ≥ 3406.385 - 5809205/x` (sharp on `(3424, 3440]`). -/
theorem psiOne_lower_grid2_3424 {x : ℝ} (hx : 3424 < x) : 3406.385 - 5809205 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3424.1 psiOneGrid2_cert_3424.2.1 psiOneGrid2_cert_3424.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3424 {x : ℝ} (hx : 3424 < x) (hx' : x ≤ 3440) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3424 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3440 :
    8521216 ≤ (psiAcc 3440).2.2 ∧ 2 ^ 27260 ≤ (psiAcc 3440).2.1 ^ 8 ∧ 2 ^ 39409 ≤ (psiAcc 3440).1 ^ 8 := by
  decide +kernel

/-- For `x > 3440`: `3414.529 x - 5837164 ≤ x ψ₁(x)` (sharp on `(3440, 3456]`). -/
theorem psiOne_lower_grid2_mul_3440 {x : ℝ} (hx : 3440 < x) : 3414.529 * x - 5837164 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3440.1 psiOneGrid2_cert_3440.2.1 psiOneGrid2_cert_3440.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3440`: `ψ₁(x) ≥ 3414.529 - 5837164/x` (sharp on `(3440, 3456]`). -/
theorem psiOne_lower_grid2_3440 {x : ℝ} (hx : 3440 < x) : 3414.529 - 5837164 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3440.1 psiOneGrid2_cert_3440.2.1 psiOneGrid2_cert_3440.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3440 {x : ℝ} (hx : 3440 < x) (hx' : x ≤ 3456) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3440 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3456 :
    8599552 ≤ (psiAcc 3456).2.2 ∧ 2 ^ 31785 ≤ (psiAcc 3456).2.1 ^ 8 ∧ 2 ^ 39503 ≤ (psiAcc 3456).1 ^ 8 := by
  decide +kernel

/-- For `x > 3456`: `3422.674 x - 5865253 ≤ x ψ₁(x)` (sharp on `(3456, 3472]`). -/
theorem psiOne_lower_grid2_mul_3456 {x : ℝ} (hx : 3456 < x) : 3422.674 * x - 5865253 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3456.1 psiOneGrid2_cert_3456.2.1 psiOneGrid2_cert_3456.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3456`: `ψ₁(x) ≥ 3422.674 - 5865253/x` (sharp on `(3456, 3472]`). -/
theorem psiOne_lower_grid2_3456 {x : ℝ} (hx : 3456 < x) : 3422.674 - 5865253 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3456.1 psiOneGrid2_cert_3456.2.1 psiOneGrid2_cert_3456.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3456 {x : ℝ} (hx : 3456 < x) (hx' : x ≤ 3472) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3456 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3472 :
    8677888 ≤ (psiAcc 3472).2.2 ∧ 2 ^ 41200 ≤ (psiAcc 3472).2.1 ^ 8 ∧ 2 ^ 39974 ≤ (psiAcc 3472).1 ^ 8 := by
  decide +kernel

/-- For `x > 3472`: `3463.483 x - 6006591 ≤ x ψ₁(x)` (sharp on `(3472, 3488]`). -/
theorem psiOne_lower_grid2_mul_3472 {x : ℝ} (hx : 3472 < x) : 3463.483 * x - 6006591 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3472.1 psiOneGrid2_cert_3472.2.1 psiOneGrid2_cert_3472.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3472`: `ψ₁(x) ≥ 3463.483 - 6006591/x` (sharp on `(3472, 3488]`). -/
theorem psiOne_lower_grid2_3472 {x : ℝ} (hx : 3472 < x) : 3463.483 - 6006591 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3472.1 psiOneGrid2_cert_3472.2.1 psiOneGrid2_cert_3472.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3472 {x : ℝ} (hx : 3472 < x) (hx' : x ≤ 3488) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3472 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3488 :
    8756224 ≤ (psiAcc 3488).2.2 ∧ 2 ^ 54426 ≤ (psiAcc 3488).2.1 ^ 8 ∧ 2 ^ 40021 ≤ (psiAcc 3488).1 ^ 8 := by
  decide +kernel

/-- For `x > 3488`: `3467.555 x - 6020766 ≤ x ψ₁(x)` (sharp on `(3488, 3504]`). -/
theorem psiOne_lower_grid2_mul_3488 {x : ℝ} (hx : 3488 < x) : 3467.555 * x - 6020766 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3488.1 psiOneGrid2_cert_3488.2.1 psiOneGrid2_cert_3488.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3488`: `ψ₁(x) ≥ 3467.555 - 6020766/x` (sharp on `(3488, 3504]`). -/
theorem psiOne_lower_grid2_3488 {x : ℝ} (hx : 3488 < x) : 3467.555 - 6020766 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3488.1 psiOneGrid2_cert_3488.2.1 psiOneGrid2_cert_3488.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3488 {x : ℝ} (hx : 3488 < x) (hx' : x ≤ 3504) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3488 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3504 :
    8834560 ≤ (psiAcc 3504).2.2 ∧ 2 ^ 69770 ≤ (psiAcc 3504).2.1 ^ 8 ∧ 2 ^ 40209 ≤ (psiAcc 3504).1 ^ 8 := by
  decide +kernel

/-- For `x > 3504`: `3483.844 x - 6077696 ≤ x ψ₁(x)` (sharp on `(3504, 3520]`). -/
theorem psiOne_lower_grid2_mul_3504 {x : ℝ} (hx : 3504 < x) : 3483.844 * x - 6077696 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3504.1 psiOneGrid2_cert_3504.2.1 psiOneGrid2_cert_3504.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3504`: `ψ₁(x) ≥ 3483.844 - 6077696/x` (sharp on `(3504, 3520]`). -/
theorem psiOne_lower_grid2_3504 {x : ℝ} (hx : 3504 < x) : 3483.844 - 6077696 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3504.1 psiOneGrid2_cert_3504.2.1 psiOneGrid2_cert_3504.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3504 {x : ℝ} (hx : 3504 < x) (hx' : x ≤ 3520) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3504 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3520 :
    8921600 ≤ (psiAcc 3520).2.2 ∧ 2 ^ 17931 ≤ (psiAcc 3520).2.1 ^ 8 ∧ 2 ^ 40397 ≤ (psiAcc 3520).1 ^ 8 := by
  decide +kernel

/-- For `x > 3520`: `3500.133 x - 6134934 ≤ x ψ₁(x)` (sharp on `(3520, 3536]`). -/
theorem psiOne_lower_grid2_mul_3520 {x : ℝ} (hx : 3520 < x) : 3500.133 * x - 6134934 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3520.1 psiOneGrid2_cert_3520.2.1 psiOneGrid2_cert_3520.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3520`: `ψ₁(x) ≥ 3500.133 - 6134934/x` (sharp on `(3520, 3536]`). -/
theorem psiOne_lower_grid2_3520 {x : ℝ} (hx : 3520 < x) : 3500.133 - 6134934 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3520.1 psiOneGrid2_cert_3520.2.1 psiOneGrid2_cert_3520.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3520 {x : ℝ} (hx : 3520 < x) (hx' : x ≤ 3536) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3520 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3536 :
    8999936 ≤ (psiAcc 3536).2.2 ∧ 2 ^ 39400 ≤ (psiAcc 3536).2.1 ^ 8 ∧ 2 ^ 40680 ≤ (psiAcc 3536).1 ^ 8 := by
  decide +kernel

/-- For `x > 3536`: `3524.653 x - 6221481 ≤ x ψ₁(x)` (sharp on `(3536, 3552]`). -/
theorem psiOne_lower_grid2_mul_3536 {x : ℝ} (hx : 3536 < x) : 3524.653 * x - 6221481 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3536.1 psiOneGrid2_cert_3536.2.1 psiOneGrid2_cert_3536.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3536`: `ψ₁(x) ≥ 3524.653 - 6221481/x` (sharp on `(3536, 3552]`). -/
theorem psiOne_lower_grid2_3536 {x : ℝ} (hx : 3536 < x) : 3524.653 - 6221481 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3536.1 psiOneGrid2_cert_3536.2.1 psiOneGrid2_cert_3536.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3536 {x : ℝ} (hx : 3536 < x) (hx' : x ≤ 3552) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3536 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3552 :
    9078272 ≤ (psiAcc 3552).2.2 ∧ 2 ^ 66339 ≤ (psiAcc 3552).2.1 ^ 8 ∧ 2 ^ 40963 ≤ (psiAcc 3552).1 ^ 8 := by
  decide +kernel

/-- For `x > 3552`: `3549.173 x - 6308338 ≤ x ψ₁(x)` (sharp on `(3552, 3568]`). -/
theorem psiOne_lower_grid2_mul_3552 {x : ℝ} (hx : 3552 < x) : 3549.173 * x - 6308338 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3552.1 psiOneGrid2_cert_3552.2.1 psiOneGrid2_cert_3552.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3552`: `ψ₁(x) ≥ 3549.173 - 6308338/x` (sharp on `(3552, 3568]`). -/
theorem psiOne_lower_grid2_3552 {x : ℝ} (hx : 3552 < x) : 3549.173 - 6308338 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3552.1 psiOneGrid2_cert_3552.2.1 psiOneGrid2_cert_3552.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3552 {x : ℝ} (hx : 3552 < x) (hx' : x ≤ 3568) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3552 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3568 :
    9165312 ≤ (psiAcc 3568).2.2 ∧ 2 ^ 27325 ≤ (psiAcc 3568).2.1 ^ 8 ∧ 2 ^ 41152 ≤ (psiAcc 3568).1 ^ 8 := by
  decide +kernel

/-- For `x > 3568`: `3565.549 x - 6366602 ≤ x ψ₁(x)` (sharp on `(3568, 3584]`). -/
theorem psiOne_lower_grid2_mul_3568 {x : ℝ} (hx : 3568 < x) : 3565.549 * x - 6366602 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3568.1 psiOneGrid2_cert_3568.2.1 psiOneGrid2_cert_3568.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3568`: `ψ₁(x) ≥ 3565.549 - 6366602/x` (sharp on `(3568, 3584]`). -/
theorem psiOne_lower_grid2_3568 {x : ℝ} (hx : 3568 < x) : 3565.549 - 6366602 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3568.1 psiOneGrid2_cert_3568.2.1 psiOneGrid2_cert_3568.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3568 {x : ℝ} (hx : 3568 < x) (hx' : x ≤ 3584) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3568 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3584 :
    9243648 ≤ (psiAcc 3584).2.2 ∧ 2 ^ 60682 ≤ (psiAcc 3584).2.1 ^ 8 ∧ 2 ^ 41435 ≤ (psiAcc 3584).1 ^ 8 := by
  decide +kernel

/-- For `x > 3584`: `3590.069 x - 6454342 ≤ x ψ₁(x)` (sharp on `(3584, 3600]`). -/
theorem psiOne_lower_grid2_mul_3584 {x : ℝ} (hx : 3584 < x) : 3590.069 * x - 6454342 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3584.1 psiOneGrid2_cert_3584.2.1 psiOneGrid2_cert_3584.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3584`: `ψ₁(x) ≥ 3590.069 - 6454342/x` (sharp on `(3584, 3600]`). -/
theorem psiOne_lower_grid2_3584 {x : ℝ} (hx : 3584 < x) : 3590.069 - 6454342 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3584.1 psiOneGrid2_cert_3584.2.1 psiOneGrid2_cert_3584.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3584 {x : ℝ} (hx : 3584 < x) (hx' : x ≤ 3600) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3584 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3600 :
    9330688 ≤ (psiAcc 3600).2.2 ∧ 2 ^ 27995 ≤ (psiAcc 3600).2.1 ^ 8 ∧ 2 ^ 41530 ≤ (psiAcc 3600).1 ^ 8 := by
  decide +kernel

/-- For `x > 3600`: `3598.300 x - 6483916 ≤ x ψ₁(x)` (sharp on `(3600, 3616]`). -/
theorem psiOne_lower_grid2_mul_3600 {x : ℝ} (hx : 3600 < x) : 3598.300 * x - 6483916 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3600.1 psiOneGrid2_cert_3600.2.1 psiOneGrid2_cert_3600.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3600`: `ψ₁(x) ≥ 3598.300 - 6483916/x` (sharp on `(3600, 3616]`). -/
theorem psiOne_lower_grid2_3600 {x : ℝ} (hx : 3600 < x) : 3598.300 - 6483916 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3600.1 psiOneGrid2_cert_3600.2.1 psiOneGrid2_cert_3600.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3600 {x : ℝ} (hx : 3600 < x) (hx' : x ≤ 3616) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3600 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3616 :
    9409024 ≤ (psiAcc 3616).2.2 ∧ 2 ^ 66926 ≤ (psiAcc 3616).2.1 ^ 8 ∧ 2 ^ 41719 ≤ (psiAcc 3616).1 ^ 8 := by
  decide +kernel

/-- For `x > 3616`: `3614.675 x - 6543031 ≤ x ψ₁(x)` (sharp on `(3616, 3632]`). -/
theorem psiOne_lower_grid2_mul_3616 {x : ℝ} (hx : 3616 < x) : 3614.675 * x - 6543031 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3616.1 psiOneGrid2_cert_3616.2.1 psiOneGrid2_cert_3616.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3616`: `ψ₁(x) ≥ 3614.675 - 6543031/x` (sharp on `(3616, 3632]`). -/
theorem psiOne_lower_grid2_3616 {x : ℝ} (hx : 3616 < x) : 3614.675 - 6543031 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3616.1 psiOneGrid2_cert_3616.2.1 psiOneGrid2_cert_3616.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3616 {x : ℝ} (hx : 3616 < x) (hx' : x ≤ 3632) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3616 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3632 :
    9496064 ≤ (psiAcc 3632).2.2 ∧ 2 ^ 40479 ≤ (psiAcc 3632).2.1 ^ 8 ∧ 2 ^ 42003 ≤ (psiAcc 3632).1 ^ 8 := by
  decide +kernel

/-- For `x > 3632`: `3639.282 x - 6632198 ≤ x ψ₁(x)` (sharp on `(3632, 3648]`). -/
theorem psiOne_lower_grid2_mul_3632 {x : ℝ} (hx : 3632 < x) : 3639.282 * x - 6632198 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3632.1 psiOneGrid2_cert_3632.2.1 psiOneGrid2_cert_3632.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3632`: `ψ₁(x) ≥ 3639.282 - 6632198/x` (sharp on `(3632, 3648]`). -/
theorem psiOne_lower_grid2_3632 {x : ℝ} (hx : 3632 < x) : 3639.282 - 6632198 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3632.1 psiOneGrid2_cert_3632.2.1 psiOneGrid2_cert_3632.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3632 {x : ℝ} (hx : 3632 < x) (hx' : x ≤ 3648) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3632 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3648 :
    9583104 ≤ (psiAcc 3648).2.2 ∧ 2 ^ 17723 ≤ (psiAcc 3648).2.1 ^ 8 ∧ 2 ^ 42192 ≤ (psiAcc 3648).1 ^ 8 := by
  decide +kernel

/-- For `x > 3648`: `3655.658 x - 6691805 ≤ x ψ₁(x)` (sharp on `(3648, 3664]`). -/
theorem psiOne_lower_grid2_mul_3648 {x : ℝ} (hx : 3648 < x) : 3655.658 * x - 6691805 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3648.1 psiOneGrid2_cert_3648.2.1 psiOneGrid2_cert_3648.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3648`: `ψ₁(x) ≥ 3655.658 - 6691805/x` (sharp on `(3648, 3664]`). -/
theorem psiOne_lower_grid2_3648 {x : ℝ} (hx : 3648 < x) : 3655.658 - 6691805 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3648.1 psiOneGrid2_cert_3648.2.1 psiOneGrid2_cert_3648.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3648 {x : ℝ} (hx : 3648 < x) (hx' : x ≤ 3664) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3648 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3664 :
    9661440 ≤ (psiAcc 3664).2.2 ∧ 2 ^ 66586 ≤ (psiAcc 3664).2.1 ^ 8 ∧ 2 ^ 42287 ≤ (psiAcc 3664).1 ^ 8 := by
  decide +kernel

/-- For `x > 3664`: `3663.889 x - 6721922 ≤ x ψ₁(x)` (sharp on `(3664, 3680]`). -/
theorem psiOne_lower_grid2_mul_3664 {x : ℝ} (hx : 3664 < x) : 3663.889 * x - 6721922 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3664.1 psiOneGrid2_cert_3664.2.1 psiOneGrid2_cert_3664.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3664`: `ψ₁(x) ≥ 3663.889 - 6721922/x` (sharp on `(3664, 3680]`). -/
theorem psiOne_lower_grid2_3664 {x : ℝ} (hx : 3664 < x) : 3663.889 - 6721922 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3664.1 psiOneGrid2_cert_3664.2.1 psiOneGrid2_cert_3664.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3664 {x : ℝ} (hx : 3664 < x) (hx' : x ≤ 3680) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3664 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3680 :
    9748480 ≤ (psiAcc 3680).2.2 ∧ 2 ^ 48659 ≤ (psiAcc 3680).2.1 ^ 8 ∧ 2 ^ 42571 ≤ (psiAcc 3680).1 ^ 8 := by
  decide +kernel

/-- For `x > 3680`: `3688.496 x - 6812319 ≤ x ψ₁(x)` (sharp on `(3680, 3696]`). -/
theorem psiOne_lower_grid2_mul_3680 {x : ℝ} (hx : 3680 < x) : 3688.496 * x - 6812319 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3680.1 psiOneGrid2_cert_3680.2.1 psiOneGrid2_cert_3680.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3680`: `ψ₁(x) ≥ 3688.496 - 6812319/x` (sharp on `(3680, 3696]`). -/
theorem psiOne_lower_grid2_3680 {x : ℝ} (hx : 3680 < x) : 3688.496 - 6812319 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3680.1 psiOneGrid2_cert_3680.2.1 psiOneGrid2_cert_3680.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3680 {x : ℝ} (hx : 3680 < x) (hx' : x ≤ 3696) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3680 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3696 :
    9835520 ≤ (psiAcc 3696).2.2 ∧ 2 ^ 33954 ≤ (psiAcc 3696).2.1 ^ 8 ∧ 2 ^ 42666 ≤ (psiAcc 3696).1 ^ 8 := by
  decide +kernel

/-- For `x > 3696`: `3696.727 x - 6842699 ≤ x ψ₁(x)` (sharp on `(3696, 3712]`). -/
theorem psiOne_lower_grid2_mul_3696 {x : ℝ} (hx : 3696 < x) : 3696.727 * x - 6842699 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3696.1 psiOneGrid2_cert_3696.2.1 psiOneGrid2_cert_3696.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3696`: `ψ₁(x) ≥ 3696.727 - 6842699/x` (sharp on `(3696, 3712]`). -/
theorem psiOne_lower_grid2_3696 {x : ℝ} (hx : 3696 < x) : 3696.727 - 6842699 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3696.1 psiOneGrid2_cert_3696.2.1 psiOneGrid2_cert_3696.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3696 {x : ℝ} (hx : 3696 < x) (hx' : x ≤ 3712) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3696 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3712 :
    9922560 ≤ (psiAcc 3712).2.2 ∧ 2 ^ 23041 ≤ (psiAcc 3712).2.1 ^ 8 ∧ 2 ^ 42950 ≤ (psiAcc 3712).1 ^ 8 := by
  decide +kernel

/-- For `x > 3712`: `3721.333 x - 6933801 ≤ x ψ₁(x)` (sharp on `(3712, 3728]`). -/
theorem psiOne_lower_grid2_mul_3712 {x : ℝ} (hx : 3712 < x) : 3721.333 * x - 6933801 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3712.1 psiOneGrid2_cert_3712.2.1 psiOneGrid2_cert_3712.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3712`: `ψ₁(x) ≥ 3721.333 - 6933801/x` (sharp on `(3712, 3728]`). -/
theorem psiOne_lower_grid2_3712 {x : ℝ} (hx : 3712 < x) : 3721.333 - 6933801 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3712.1 psiOneGrid2_cert_3712.2.1 psiOneGrid2_cert_3712.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3712 {x : ℝ} (hx : 3712 < x) (hx' : x ≤ 3728) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3712 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3728 :
    10009600 ≤ (psiAcc 3728).2.2 ∧ 2 ^ 15212 ≤ (psiAcc 3728).2.1 ^ 8 ∧ 2 ^ 43187 ≤ (psiAcc 3728).1 ^ 8 := by
  decide +kernel

/-- For `x > 3728`: `3741.868 x - 7010242 ≤ x ψ₁(x)` (sharp on `(3728, 3744]`). -/
theorem psiOne_lower_grid2_mul_3728 {x : ℝ} (hx : 3728 < x) : 3741.868 * x - 7010242 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3728.1 psiOneGrid2_cert_3728.2.1 psiOneGrid2_cert_3728.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3728`: `ψ₁(x) ≥ 3741.868 - 7010242/x` (sharp on `(3728, 3744]`). -/
theorem psiOne_lower_grid2_3728 {x : ℝ} (hx : 3728 < x) : 3741.868 - 7010242 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3728.1 psiOneGrid2_cert_3728.2.1 psiOneGrid2_cert_3728.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3728 {x : ℝ} (hx : 3728 < x) (hx' : x ≤ 3744) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3728 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3744 :
    10096640 ≤ (psiAcc 3744).2.2 ∧ 2 ^ 11416 ≤ (psiAcc 3744).2.1 ^ 8 ∧ 2 ^ 43377 ≤ (psiAcc 3744).1 ^ 8 := by
  decide +kernel

/-- For `x > 3744`: `3758.330 x - 7071744 ≤ x ψ₁(x)` (sharp on `(3744, 3760]`). -/
theorem psiOne_lower_grid2_mul_3744 {x : ℝ} (hx : 3744 < x) : 3758.330 * x - 7071744 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3744.1 psiOneGrid2_cert_3744.2.1 psiOneGrid2_cert_3744.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3744`: `ψ₁(x) ≥ 3758.330 - 7071744/x` (sharp on `(3744, 3760]`). -/
theorem psiOne_lower_grid2_3744 {x : ℝ} (hx : 3744 < x) : 3758.330 - 7071744 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3744.1 psiOneGrid2_cert_3744.2.1 psiOneGrid2_cert_3744.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3744 {x : ℝ} (hx : 3744 < x) (hx' : x ≤ 3760) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3744 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3760 :
    10183680 ≤ (psiAcc 3760).2.2 ∧ 2 ^ 9140 ≤ (psiAcc 3760).2.1 ^ 8 ∧ 2 ^ 43377 ≤ (psiAcc 3760).1 ^ 8 := by
  decide +kernel

/-- For `x > 3760`: `3758.330 x - 7071743 ≤ x ψ₁(x)` (sharp on `(3760, 3776]`). -/
theorem psiOne_lower_grid2_mul_3760 {x : ℝ} (hx : 3760 < x) : 3758.330 * x - 7071743 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3760.1 psiOneGrid2_cert_3760.2.1 psiOneGrid2_cert_3760.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3760`: `ψ₁(x) ≥ 3758.330 - 7071743/x` (sharp on `(3760, 3776]`). -/
theorem psiOne_lower_grid2_3760 {x : ℝ} (hx : 3760 < x) : 3758.330 - 7071743 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3760.1 psiOneGrid2_cert_3760.2.1 psiOneGrid2_cert_3760.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3760 {x : ℝ} (hx : 3760 < x) (hx' : x ≤ 3776) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3760 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3776 :
    10270720 ≤ (psiAcc 3776).2.2 ∧ 2 ^ 9809 ≤ (psiAcc 3776).2.1 ^ 8 ∧ 2 ^ 43662 ≤ (psiAcc 3776).1 ^ 8 := by
  decide +kernel

/-- For `x > 3776`: `3783.024 x - 7164729 ≤ x ψ₁(x)` (sharp on `(3776, 3792]`). -/
theorem psiOne_lower_grid2_mul_3776 {x : ℝ} (hx : 3776 < x) : 3783.024 * x - 7164729 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3776.1 psiOneGrid2_cert_3776.2.1 psiOneGrid2_cert_3776.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3776`: `ψ₁(x) ≥ 3783.024 - 7164729/x` (sharp on `(3776, 3792]`). -/
theorem psiOne_lower_grid2_3776 {x : ℝ} (hx : 3776 < x) : 3783.024 - 7164729 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3776.1 psiOneGrid2_cert_3776.2.1 psiOneGrid2_cert_3776.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3776 {x : ℝ} (hx : 3776 < x) (hx' : x ≤ 3792) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3776 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3792 :
    10357760 ≤ (psiAcc 3792).2.2 ∧ 2 ^ 13330 ≤ (psiAcc 3792).2.1 ^ 8 ∧ 2 ^ 43757 ≤ (psiAcc 3792).1 ^ 8 := by
  decide +kernel

/-- For `x > 3792`: `3791.255 x - 7195833 ≤ x ψ₁(x)` (sharp on `(3792, 3808]`). -/
theorem psiOne_lower_grid2_mul_3792 {x : ℝ} (hx : 3792 < x) : 3791.255 * x - 7195833 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3792.1 psiOneGrid2_cert_3792.2.1 psiOneGrid2_cert_3792.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3792`: `ψ₁(x) ≥ 3791.255 - 7195833/x` (sharp on `(3792, 3808]`). -/
theorem psiOne_lower_grid2_3792 {x : ℝ} (hx : 3792 < x) : 3791.255 - 7195833 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3792.1 psiOneGrid2_cert_3792.2.1 psiOneGrid2_cert_3792.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3792 {x : ℝ} (hx : 3792 < x) (hx' : x ≤ 3808) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3792 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3808 :
    10444800 ≤ (psiAcc 3808).2.2 ∧ 2 ^ 20084 ≤ (psiAcc 3808).2.1 ^ 8 ∧ 2 ^ 44043 ≤ (psiAcc 3808).1 ^ 8 := by
  decide +kernel

/-- For `x > 3808`: `3816.035 x - 7289939 ≤ x ψ₁(x)` (sharp on `(3808, 3824]`). -/
theorem psiOne_lower_grid2_mul_3808 {x : ℝ} (hx : 3808 < x) : 3816.035 * x - 7289939 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3808.1 psiOneGrid2_cert_3808.2.1 psiOneGrid2_cert_3808.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3808`: `ψ₁(x) ≥ 3816.035 - 7289939/x` (sharp on `(3808, 3824]`). -/
theorem psiOne_lower_grid2_3808 {x : ℝ} (hx : 3808 < x) : 3816.035 - 7289939 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3808.1 psiOneGrid2_cert_3808.2.1 psiOneGrid2_cert_3808.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3808 {x : ℝ} (hx : 3808 < x) (hx' : x ≤ 3824) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3808 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3824 :
    10531840 ≤ (psiAcc 3824).2.2 ∧ 2 ^ 28837 ≤ (psiAcc 3824).2.1 ^ 8 ∧ 2 ^ 44233 ≤ (psiAcc 3824).1 ^ 8 := by
  decide +kernel

/-- For `x > 3824`: `3832.497 x - 7352857 ≤ x ψ₁(x)` (sharp on `(3824, 3840]`). -/
theorem psiOne_lower_grid2_mul_3824 {x : ℝ} (hx : 3824 < x) : 3832.497 * x - 7352857 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3824.1 psiOneGrid2_cert_3824.2.1 psiOneGrid2_cert_3824.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3824`: `ψ₁(x) ≥ 3832.497 - 7352857/x` (sharp on `(3824, 3840]`). -/
theorem psiOne_lower_grid2_3824 {x : ℝ} (hx : 3824 < x) : 3832.497 - 7352857 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3824.1 psiOneGrid2_cert_3824.2.1 psiOneGrid2_cert_3824.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3824 {x : ℝ} (hx : 3824 < x) (hx' : x ≤ 3840) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3824 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3840 :
    10618880 ≤ (psiAcc 3840).2.2 ∧ 2 ^ 40922 ≤ (psiAcc 3840).2.1 ^ 8 ∧ 2 ^ 44328 ≤ (psiAcc 3840).1 ^ 8 := by
  decide +kernel

/-- For `x > 3840`: `3840.728 x - 7384406 ≤ x ψ₁(x)` (sharp on `(3840, 3856]`). -/
theorem psiOne_lower_grid2_mul_3840 {x : ℝ} (hx : 3840 < x) : 3840.728 * x - 7384406 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3840.1 psiOneGrid2_cert_3840.2.1 psiOneGrid2_cert_3840.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3840`: `ψ₁(x) ≥ 3840.728 - 7384406/x` (sharp on `(3840, 3856]`). -/
theorem psiOne_lower_grid2_3840 {x : ℝ} (hx : 3840 < x) : 3840.728 - 7384406 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3840.1 psiOneGrid2_cert_3840.2.1 psiOneGrid2_cert_3840.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3840 {x : ℝ} (hx : 3840 < x) (hx' : x ≤ 3856) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3840 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3856 :
    10705920 ≤ (psiAcc 3856).2.2 ∧ 2 ^ 55484 ≤ (psiAcc 3856).2.1 ^ 8 ∧ 2 ^ 44614 ≤ (psiAcc 3856).1 ^ 8 := by
  decide +kernel

/-- For `x > 3856`: `3865.508 x - 7479816 ≤ x ψ₁(x)` (sharp on `(3856, 3872]`). -/
theorem psiOne_lower_grid2_mul_3856 {x : ℝ} (hx : 3856 < x) : 3865.508 * x - 7479816 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3856.1 psiOneGrid2_cert_3856.2.1 psiOneGrid2_cert_3856.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3856`: `ψ₁(x) ≥ 3865.508 - 7479816/x` (sharp on `(3856, 3872]`). -/
theorem psiOne_lower_grid2_3856 {x : ℝ} (hx : 3856 < x) : 3865.508 - 7479816 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3856.1 psiOneGrid2_cert_3856.2.1 psiOneGrid2_cert_3856.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3856 {x : ℝ} (hx : 3856 < x) (hx' : x ≤ 3872) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3856 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3872 :
    10801664 ≤ (psiAcc 3872).2.2 ∧ 2 ^ 4226 ≤ (psiAcc 3872).2.1 ^ 8 ∧ 2 ^ 44710 ≤ (psiAcc 3872).1 ^ 8 := by
  decide +kernel

/-- For `x > 3872`: `3873.826 x - 7511947 ≤ x ψ₁(x)` (sharp on `(3872, 3888]`). -/
theorem psiOne_lower_grid2_mul_3872 {x : ℝ} (hx : 3872 < x) : 3873.826 * x - 7511947 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3872.1 psiOneGrid2_cert_3872.2.1 psiOneGrid2_cert_3872.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3872`: `ψ₁(x) ≥ 3873.826 - 7511947/x` (sharp on `(3872, 3888]`). -/
theorem psiOne_lower_grid2_3872 {x : ℝ} (hx : 3872 < x) : 3873.826 - 7511947 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3872.1 psiOneGrid2_cert_3872.2.1 psiOneGrid2_cert_3872.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3872 {x : ℝ} (hx : 3872 < x) (hx' : x ≤ 3888) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3872 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3888 :
    10888704 ≤ (psiAcc 3888).2.2 ∧ 2 ^ 24984 ≤ (psiAcc 3888).2.1 ^ 8 ∧ 2 ^ 44900 ≤ (psiAcc 3888).1 ^ 8 := by
  decide +kernel

/-- For `x > 3888`: `3890.288 x - 7575803 ≤ x ψ₁(x)` (sharp on `(3888, 3904]`). -/
theorem psiOne_lower_grid2_mul_3888 {x : ℝ} (hx : 3888 < x) : 3890.288 * x - 7575803 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3888.1 psiOneGrid2_cert_3888.2.1 psiOneGrid2_cert_3888.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3888`: `ψ₁(x) ≥ 3890.288 - 7575803/x` (sharp on `(3888, 3904]`). -/
theorem psiOne_lower_grid2_3888 {x : ℝ} (hx : 3888 < x) : 3890.288 - 7575803 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3888.1 psiOneGrid2_cert_3888.2.1 psiOneGrid2_cert_3888.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3888 {x : ℝ} (hx : 3888 < x) (hx' : x ≤ 3904) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3888 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3904 :
    10975744 ≤ (psiAcc 3904).2.2 ∧ 2 ^ 48508 ≤ (psiAcc 3904).2.1 ^ 8 ∧ 2 ^ 44996 ≤ (psiAcc 3904).1 ^ 8 := by
  decide +kernel

/-- For `x > 3904`: `3898.606 x - 7608151 ≤ x ψ₁(x)` (sharp on `(3904, 3920]`). -/
theorem psiOne_lower_grid2_mul_3904 {x : ℝ} (hx : 3904 < x) : 3898.606 * x - 7608151 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3904.1 psiOneGrid2_cert_3904.2.1 psiOneGrid2_cert_3904.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3904`: `ψ₁(x) ≥ 3898.606 - 7608151/x` (sharp on `(3904, 3920]`). -/
theorem psiOne_lower_grid2_3904 {x : ℝ} (hx : 3904 < x) : 3898.606 - 7608151 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3904.1 psiOneGrid2_cert_3904.2.1 psiOneGrid2_cert_3904.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3904 {x : ℝ} (hx : 3904 < x) (hx' : x ≤ 3920) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3904 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3920 :
    11071488 ≤ (psiAcc 3920).2.2 ∧ 2 ^ 4978 ≤ (psiAcc 3920).2.1 ^ 8 ∧ 2 ^ 45378 ≤ (psiAcc 3920).1 ^ 8 := by
  decide +kernel

/-- For `x > 3920`: `3931.704 x - 7737679 ≤ x ψ₁(x)` (sharp on `(3920, 3936]`). -/
theorem psiOne_lower_grid2_mul_3920 {x : ℝ} (hx : 3920 < x) : 3931.704 * x - 7737679 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3920.1 psiOneGrid2_cert_3920.2.1 psiOneGrid2_cert_3920.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3920`: `ψ₁(x) ≥ 3931.704 - 7737679/x` (sharp on `(3920, 3936]`). -/
theorem psiOne_lower_grid2_3920 {x : ℝ} (hx : 3920 < x) : 3931.704 - 7737679 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3920.1 psiOneGrid2_cert_3920.2.1 psiOneGrid2_cert_3920.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3920 {x : ℝ} (hx : 3920 < x) (hx' : x ≤ 3936) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3920 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3936 :
    11158528 ≤ (psiAcc 3936).2.2 ∧ 2 ^ 37095 ≤ (psiAcc 3936).2.1 ^ 8 ∧ 2 ^ 45664 ≤ (psiAcc 3936).1 ^ 8 := by
  decide +kernel

/-- For `x > 3936`: `3956.484 x - 7835006 ≤ x ψ₁(x)` (sharp on `(3936, 3952]`). -/
theorem psiOne_lower_grid2_mul_3936 {x : ℝ} (hx : 3936 < x) : 3956.484 * x - 7835006 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3936.1 psiOneGrid2_cert_3936.2.1 psiOneGrid2_cert_3936.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3936`: `ψ₁(x) ≥ 3956.484 - 7835006/x` (sharp on `(3936, 3952]`). -/
theorem psiOne_lower_grid2_3936 {x : ℝ} (hx : 3936 < x) : 3956.484 - 7835006 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3936.1 psiOneGrid2_cert_3936.2.1 psiOneGrid2_cert_3936.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3936 {x : ℝ} (hx : 3936 < x) (hx' : x ≤ 3952) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3936 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3952 :
    11245568 ≤ (psiAcc 3952).2.2 ∧ 2 ^ 72748 ≤ (psiAcc 3952).2.1 ^ 8 ∧ 2 ^ 45855 ≤ (psiAcc 3952).1 ^ 8 := by
  decide +kernel

/-- For `x > 3952`: `3973.032 x - 7900290 ≤ x ψ₁(x)` (sharp on `(3952, 3968]`). -/
theorem psiOne_lower_grid2_mul_3952 {x : ℝ} (hx : 3952 < x) : 3973.032 * x - 7900290 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3952.1 psiOneGrid2_cert_3952.2.1 psiOneGrid2_cert_3952.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3952`: `ψ₁(x) ≥ 3973.032 - 7900290/x` (sharp on `(3952, 3968]`). -/
theorem psiOne_lower_grid2_3952 {x : ℝ} (hx : 3952 < x) : 3973.032 - 7900290 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3952.1 psiOneGrid2_cert_3952.2.1 psiOneGrid2_cert_3952.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3952 {x : ℝ} (hx : 3952 < x) (hx' : x ≤ 3968) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3952 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3968 :
    11341312 ≤ (psiAcc 3968).2.2 ∧ 2 ^ 40584 ≤ (psiAcc 3968).2.1 ^ 8 ∧ 2 ^ 45951 ≤ (psiAcc 3968).1 ^ 8 := by
  decide +kernel

/-- For `x > 3968`: `3981.350 x - 7933286 ≤ x ψ₁(x)` (sharp on `(3968, 3984]`). -/
theorem psiOne_lower_grid2_mul_3968 {x : ℝ} (hx : 3968 < x) : 3981.350 * x - 7933286 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3968.1 psiOneGrid2_cert_3968.2.1 psiOneGrid2_cert_3968.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3968`: `ψ₁(x) ≥ 3981.350 - 7933286/x` (sharp on `(3968, 3984]`). -/
theorem psiOne_lower_grid2_3968 {x : ℝ} (hx : 3968 < x) : 3981.350 - 7933286 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3968.1 psiOneGrid2_cert_3968.2.1 psiOneGrid2_cert_3968.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3968 {x : ℝ} (hx : 3968 < x) (hx' : x ≤ 3984) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3968 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_3984 :
    11437056 ≤ (psiAcc 3984).2.2 ∧ 2 ^ 9855 ≤ (psiAcc 3984).2.1 ^ 8 ∧ 2 ^ 45951 ≤ (psiAcc 3984).1 ^ 8 := by
  decide +kernel

/-- For `x > 3984`: `3981.350 x - 7933285 ≤ x ψ₁(x)` (sharp on `(3984, 4000]`). -/
theorem psiOne_lower_grid2_mul_3984 {x : ℝ} (hx : 3984 < x) : 3981.350 * x - 7933285 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_3984.1 psiOneGrid2_cert_3984.2.1 psiOneGrid2_cert_3984.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 3984`: `ψ₁(x) ≥ 3981.350 - 7933285/x` (sharp on `(3984, 4000]`). -/
theorem psiOne_lower_grid2_3984 {x : ℝ} (hx : 3984 < x) : 3981.350 - 7933285 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_3984.1 psiOneGrid2_cert_3984.2.1 psiOneGrid2_cert_3984.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_3984 {x : ℝ} (hx : 3984 < x) (hx' : x ≤ 4000) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_3984 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4000 :
    11524096 ≤ (psiAcc 4000).2.2 ∧ 2 ^ 49810 ≤ (psiAcc 4000).2.1 ^ 8 ∧ 2 ^ 46047 ≤ (psiAcc 4000).1 ^ 8 := by
  decide +kernel

/-- For `x > 4000`: `3989.668 x - 7966464 ≤ x ψ₁(x)` (sharp on `(4000, 4016]`). -/
theorem psiOne_lower_grid2_mul_4000 {x : ℝ} (hx : 4000 < x) : 3989.668 * x - 7966464 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4000.1 psiOneGrid2_cert_4000.2.1 psiOneGrid2_cert_4000.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4000`: `ψ₁(x) ≥ 3989.668 - 7966464/x` (sharp on `(4000, 4016]`). -/
theorem psiOne_lower_grid2_4000 {x : ℝ} (hx : 4000 < x) : 3989.668 - 7966464 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4000.1 psiOneGrid2_cert_4000.2.1 psiOneGrid2_cert_4000.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4000 {x : ℝ} (hx : 4000 < x) (hx' : x ≤ 4016) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4000 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4016 :
    11619840 ≤ (psiAcc 4016).2.2 ∧ 2 ^ 24441 ≤ (psiAcc 4016).2.1 ^ 8 ∧ 2 ^ 46430 ≤ (psiAcc 4016).1 ^ 8 := by
  decide +kernel

/-- For `x > 4016`: `4022.852 x - 8099401 ≤ x ψ₁(x)` (sharp on `(4016, 4032]`). -/
theorem psiOne_lower_grid2_mul_4016 {x : ℝ} (hx : 4016 < x) : 4022.852 * x - 8099401 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4016.1 psiOneGrid2_cert_4016.2.1 psiOneGrid2_cert_4016.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4016`: `ψ₁(x) ≥ 4022.852 - 8099401/x` (sharp on `(4016, 4032]`). -/
theorem psiOne_lower_grid2_4016 {x : ℝ} (hx : 4016 < x) : 4022.852 - 8099401 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4016.1 psiOneGrid2_cert_4016.2.1 psiOneGrid2_cert_4016.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4016 {x : ℝ} (hx : 4016 < x) (hx' : x ≤ 4032) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4016 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4032 :
    11715584 ≤ (psiAcc 4032).2.2 ∧ 2 ^ 4149 ≤ (psiAcc 4032).2.1 ^ 8 ∧ 2 ^ 46717 ≤ (psiAcc 4032).1 ^ 8 := by
  decide +kernel

/-- For `x > 4032`: `4047.719 x - 8199422 ≤ x ψ₁(x)` (sharp on `(4032, 4048]`). -/
theorem psiOne_lower_grid2_mul_4032 {x : ℝ} (hx : 4032 < x) : 4047.719 * x - 8199422 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4032.1 psiOneGrid2_cert_4032.2.1 psiOneGrid2_cert_4032.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4032`: `ψ₁(x) ≥ 4047.719 - 8199422/x` (sharp on `(4032, 4048]`). -/
theorem psiOne_lower_grid2_4032 {x : ℝ} (hx : 4032 < x) : 4047.719 - 8199422 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4032.1 psiOneGrid2_cert_4032.2.1 psiOneGrid2_cert_4032.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4032 {x : ℝ} (hx : 4032 < x) (hx' : x ≤ 4048) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4032 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4048 :
    11802624 ≤ (psiAcc 4048).2.2 ∧ 2 ^ 55308 ≤ (psiAcc 4048).2.1 ^ 8 ∧ 2 ^ 46717 ≤ (psiAcc 4048).1 ^ 8 := by
  decide +kernel

/-- For `x > 4048`: `4047.719 x - 8199422 ≤ x ψ₁(x)` (sharp on `(4048, 4064]`). -/
theorem psiOne_lower_grid2_mul_4048 {x : ℝ} (hx : 4048 < x) : 4047.719 * x - 8199422 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4048.1 psiOneGrid2_cert_4048.2.1 psiOneGrid2_cert_4048.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4048`: `ψ₁(x) ≥ 4047.719 - 8199422/x` (sharp on `(4048, 4064]`). -/
theorem psiOne_lower_grid2_4048 {x : ℝ} (hx : 4048 < x) : 4047.719 - 8199422 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4048.1 psiOneGrid2_cert_4048.2.1 psiOneGrid2_cert_4048.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4048 {x : ℝ} (hx : 4048 < x) (hx' : x ≤ 4064) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4048 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4064 :
    11898368 ≤ (psiAcc 4064).2.2 ∧ 2 ^ 40191 ≤ (psiAcc 4064).2.1 ^ 8 ∧ 2 ^ 47005 ≤ (psiAcc 4064).1 ^ 8 := by
  decide +kernel

/-- For `x > 4064`: `4072.672 x - 8300541 ≤ x ψ₁(x)` (sharp on `(4064, 4080]`). -/
theorem psiOne_lower_grid2_mul_4064 {x : ℝ} (hx : 4064 < x) : 4072.672 * x - 8300541 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4064.1 psiOneGrid2_cert_4064.2.1 psiOneGrid2_cert_4064.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4064`: `ψ₁(x) ≥ 4072.672 - 8300541/x` (sharp on `(4064, 4080]`). -/
theorem psiOne_lower_grid2_4064 {x : ℝ} (hx : 4064 < x) : 4072.672 - 8300541 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4064.1 psiOneGrid2_cert_4064.2.1 psiOneGrid2_cert_4064.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4064 {x : ℝ} (hx : 4064 < x) (hx' : x ≤ 4080) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4064 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4080 :
    11994112 ≤ (psiAcc 4080).2.2 ∧ 2 ^ 27088 ≤ (psiAcc 4080).2.1 ^ 8 ∧ 2 ^ 47196 ≤ (psiAcc 4080).1 ^ 8 := by
  decide +kernel

/-- For `x > 4080`: `4089.221 x - 8367993 ≤ x ψ₁(x)` (sharp on `(4080, 4096]`). -/
theorem psiOne_lower_grid2_mul_4080 {x : ℝ} (hx : 4080 < x) : 4089.221 * x - 8367993 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4080.1 psiOneGrid2_cert_4080.2.1 psiOneGrid2_cert_4080.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4080`: `ψ₁(x) ≥ 4089.221 - 8367993/x` (sharp on `(4080, 4096]`). -/
theorem psiOne_lower_grid2_4080 {x : ℝ} (hx : 4080 < x) : 4089.221 - 8367993 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4080.1 psiOneGrid2_cert_4080.2.1 psiOneGrid2_cert_4080.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4080 {x : ℝ} (hx : 4080 < x) (hx' : x ≤ 4096) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4080 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4096 :
    12089856 ≤ (psiAcc 4096).2.2 ∧ 2 ^ 17056 ≤ (psiAcc 4096).2.1 ^ 8 ∧ 2 ^ 47396 ≤ (psiAcc 4096).1 ^ 8 := by
  decide +kernel

/-- For `x > 4096`: `4106.550 x - 8438904 ≤ x ψ₁(x)` (sharp on `(4096, 4112]`). -/
theorem psiOne_lower_grid2_mul_4096 {x : ℝ} (hx : 4096 < x) : 4106.550 * x - 8438904 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4096.1 psiOneGrid2_cert_4096.2.1 psiOneGrid2_cert_4096.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4096`: `ψ₁(x) ≥ 4106.550 - 8438904/x` (sharp on `(4096, 4112]`). -/
theorem psiOne_lower_grid2_4096 {x : ℝ} (hx : 4096 < x) : 4106.550 - 8438904 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4096.1 psiOneGrid2_cert_4096.2.1 psiOneGrid2_cert_4096.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4096 {x : ℝ} (hx : 4096 < x) (hx' : x ≤ 4112) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4096 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4112 :
    12185600 ≤ (psiAcc 4112).2.2 ∧ 2 ^ 10799 ≤ (psiAcc 4112).2.1 ^ 8 ∧ 2 ^ 47589 ≤ (psiAcc 4112).1 ^ 8 := by
  decide +kernel

/-- For `x > 4112`: `4123.272 x - 8507548 ≤ x ψ₁(x)` (sharp on `(4112, 4128]`). -/
theorem psiOne_lower_grid2_mul_4112 {x : ℝ} (hx : 4112 < x) : 4123.272 * x - 8507548 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4112.1 psiOneGrid2_cert_4112.2.1 psiOneGrid2_cert_4112.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4112`: `ψ₁(x) ≥ 4123.272 - 8507548/x` (sharp on `(4112, 4128]`). -/
theorem psiOne_lower_grid2_4112 {x : ℝ} (hx : 4112 < x) : 4123.272 - 8507548 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4112.1 psiOneGrid2_cert_4112.2.1 psiOneGrid2_cert_4112.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4112 {x : ℝ} (hx : 4112 < x) (hx' : x ≤ 4128) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4112 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4128 :
    12281344 ≤ (psiAcc 4128).2.2 ∧ 2 ^ 6367 ≤ (psiAcc 4128).2.1 ^ 8 ∧ 2 ^ 47685 ≤ (psiAcc 4128).1 ^ 8 := by
  decide +kernel

/-- For `x > 4128`: `4131.590 x - 8541875 ≤ x ψ₁(x)` (sharp on `(4128, 4144]`). -/
theorem psiOne_lower_grid2_mul_4128 {x : ℝ} (hx : 4128 < x) : 4131.590 * x - 8541875 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4128.1 psiOneGrid2_cert_4128.2.1 psiOneGrid2_cert_4128.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4128`: `ψ₁(x) ≥ 4131.590 - 8541875/x` (sharp on `(4128, 4144]`). -/
theorem psiOne_lower_grid2_4128 {x : ℝ} (hx : 4128 < x) : 4131.590 - 8541875 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4128.1 psiOneGrid2_cert_4128.2.1 psiOneGrid2_cert_4128.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4128 {x : ℝ} (hx : 4128 < x) (hx' : x ≤ 4144) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4128 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4144 :
    12377088 ≤ (psiAcc 4144).2.2 ∧ 2 ^ 6356 ≤ (psiAcc 4144).2.1 ^ 8 ∧ 2 ^ 47973 ≤ (psiAcc 4144).1 ^ 8 := by
  decide +kernel

/-- For `x > 4144`: `4156.543 x - 8645023 ≤ x ψ₁(x)` (sharp on `(4144, 4160]`). -/
theorem psiOne_lower_grid2_mul_4144 {x : ℝ} (hx : 4144 < x) : 4156.543 * x - 8645023 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4144.1 psiOneGrid2_cert_4144.2.1 psiOneGrid2_cert_4144.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4144`: `ψ₁(x) ≥ 4156.543 - 8645023/x` (sharp on `(4144, 4160]`). -/
theorem psiOne_lower_grid2_4144 {x : ℝ} (hx : 4144 < x) : 4156.543 - 8645023 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4144.1 psiOneGrid2_cert_4144.2.1 psiOneGrid2_cert_4144.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4144 {x : ℝ} (hx : 4144 < x) (hx' : x ≤ 4160) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4144 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4160 :
    12472832 ≤ (psiAcc 4160).2.2 ∧ 2 ^ 9036 ≤ (psiAcc 4160).2.1 ^ 8 ∧ 2 ^ 48261 ≤ (psiAcc 4160).1 ^ 8 := by
  decide +kernel

/-- For `x > 4160`: `4181.497 x - 8748737 ≤ x ψ₁(x)` (sharp on `(4160, 4176]`). -/
theorem psiOne_lower_grid2_mul_4160 {x : ℝ} (hx : 4160 < x) : 4181.497 * x - 8748737 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4160.1 psiOneGrid2_cert_4160.2.1 psiOneGrid2_cert_4160.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4160`: `ψ₁(x) ≥ 4181.497 - 8748737/x` (sharp on `(4160, 4176]`). -/
theorem psiOne_lower_grid2_4160 {x : ℝ} (hx : 4160 < x) : 4181.497 - 8748737 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4160.1 psiOneGrid2_cert_4160.2.1 psiOneGrid2_cert_4160.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4160 {x : ℝ} (hx : 4160 < x) (hx' : x ≤ 4176) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4160 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4176 :
    12568576 ≤ (psiAcc 4176).2.2 ∧ 2 ^ 15275 ≤ (psiAcc 4176).2.1 ^ 8 ∧ 2 ^ 48261 ≤ (psiAcc 4176).1 ^ 8 := by
  decide +kernel

/-- For `x > 4176`: `4181.497 x - 8748736 ≤ x ψ₁(x)` (sharp on `(4176, 4192]`). -/
theorem psiOne_lower_grid2_mul_4176 {x : ℝ} (hx : 4176 < x) : 4181.497 * x - 8748736 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4176.1 psiOneGrid2_cert_4176.2.1 psiOneGrid2_cert_4176.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4176`: `ψ₁(x) ≥ 4181.497 - 8748736/x` (sharp on `(4176, 4192]`). -/
theorem psiOne_lower_grid2_4176 {x : ℝ} (hx : 4176 < x) : 4181.497 - 8748736 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4176.1 psiOneGrid2_cert_4176.2.1 psiOneGrid2_cert_4176.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4176 {x : ℝ} (hx : 4176 < x) (hx' : x ≤ 4192) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4176 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4192 :
    12664320 ≤ (psiAcc 4192).2.2 ∧ 2 ^ 22957 ≤ (psiAcc 4192).2.1 ^ 8 ∧ 2 ^ 48358 ≤ (psiAcc 4192).1 ^ 8 := by
  decide +kernel

/-- For `x > 4192`: `4189.901 x - 8783840 ≤ x ψ₁(x)` (sharp on `(4192, 4208]`). -/
theorem psiOne_lower_grid2_mul_4192 {x : ℝ} (hx : 4192 < x) : 4189.901 * x - 8783840 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4192.1 psiOneGrid2_cert_4192.2.1 psiOneGrid2_cert_4192.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4192`: `ψ₁(x) ≥ 4189.901 - 8783840/x` (sharp on `(4192, 4208]`). -/
theorem psiOne_lower_grid2_4192 {x : ℝ} (hx : 4192 < x) : 4189.901 - 8783840 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4192.1 psiOneGrid2_cert_4192.2.1 psiOneGrid2_cert_4192.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4192 {x : ℝ} (hx : 4192 < x) (hx' : x ≤ 4208) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4192 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4208 :
    12760064 ≤ (psiAcc 4208).2.2 ∧ 2 ^ 31409 ≤ (psiAcc 4208).2.1 ^ 8 ∧ 2 ^ 48454 ≤ (psiAcc 4208).1 ^ 8 := by
  decide +kernel

/-- For `x > 4208`: `4198.219 x - 8818783 ≤ x ψ₁(x)` (sharp on `(4208, 4224]`). -/
theorem psiOne_lower_grid2_mul_4208 {x : ℝ} (hx : 4208 < x) : 4198.219 * x - 8818783 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4208.1 psiOneGrid2_cert_4208.2.1 psiOneGrid2_cert_4208.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4208`: `ψ₁(x) ≥ 4198.219 - 8818783/x` (sharp on `(4208, 4224]`). -/
theorem psiOne_lower_grid2_4208 {x : ℝ} (hx : 4208 < x) : 4198.219 - 8818783 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4208.1 psiOneGrid2_cert_4208.2.1 psiOneGrid2_cert_4208.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4208 {x : ℝ} (hx : 4208 < x) (hx' : x ≤ 4224) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4208 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4224 :
    12855808 ≤ (psiAcc 4224).2.2 ∧ 2 ^ 43137 ≤ (psiAcc 4224).2.1 ^ 8 ∧ 2 ^ 48743 ≤ (psiAcc 4224).1 ^ 8 := by
  decide +kernel

/-- For `x > 4224`: `4223.259 x - 8924342 ≤ x ψ₁(x)` (sharp on `(4224, 4240]`). -/
theorem psiOne_lower_grid2_mul_4224 {x : ℝ} (hx : 4224 < x) : 4223.259 * x - 8924342 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4224.1 psiOneGrid2_cert_4224.2.1 psiOneGrid2_cert_4224.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4224`: `ψ₁(x) ≥ 4223.259 - 8924342/x` (sharp on `(4224, 4240]`). -/
theorem psiOne_lower_grid2_4224 {x : ℝ} (hx : 4224 < x) : 4223.259 - 8924342 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4224.1 psiOneGrid2_cert_4224.2.1 psiOneGrid2_cert_4224.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4224 {x : ℝ} (hx : 4224 < x) (hx' : x ≤ 4240) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4224 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4240 :
    12951552 ≤ (psiAcc 4240).2.2 ∧ 2 ^ 59007 ≤ (psiAcc 4240).2.1 ^ 8 ∧ 2 ^ 48936 ≤ (psiAcc 4240).1 ^ 8 := by
  decide +kernel

/-- For `x > 4240`: `4239.981 x - 8995077 ≤ x ψ₁(x)` (sharp on `(4240, 4256]`). -/
theorem psiOne_lower_grid2_mul_4240 {x : ℝ} (hx : 4240 < x) : 4239.981 * x - 8995077 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4240.1 psiOneGrid2_cert_4240.2.1 psiOneGrid2_cert_4240.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4240`: `ψ₁(x) ≥ 4239.981 - 8995077/x` (sharp on `(4240, 4256]`). -/
theorem psiOne_lower_grid2_4240 {x : ℝ} (hx : 4240 < x) : 4239.981 - 8995077 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4240.1 psiOneGrid2_cert_4240.2.1 psiOneGrid2_cert_4240.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4240 {x : ℝ} (hx : 4240 < x) (hx' : x ≤ 4256) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4240 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4256 :
    13056000 ≤ (psiAcc 4256).2.2 ∧ 2 ^ 9390 ≤ (psiAcc 4256).2.1 ^ 8 ∧ 2 ^ 49225 ≤ (psiAcc 4256).1 ^ 8 := by
  decide +kernel

/-- For `x > 4256`: `4265.021 x - 9101388 ≤ x ψ₁(x)` (sharp on `(4256, 4272]`). -/
theorem psiOne_lower_grid2_mul_4256 {x : ℝ} (hx : 4256 < x) : 4265.021 * x - 9101388 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4256.1 psiOneGrid2_cert_4256.2.1 psiOneGrid2_cert_4256.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4256`: `ψ₁(x) ≥ 4265.021 - 9101388/x` (sharp on `(4256, 4272]`). -/
theorem psiOne_lower_grid2_4256 {x : ℝ} (hx : 4256 < x) : 4265.021 - 9101388 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4256.1 psiOneGrid2_cert_4256.2.1 psiOneGrid2_cert_4256.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4256 {x : ℝ} (hx : 4256 < x) (hx' : x ≤ 4272) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4256 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4272 :
    13151744 ≤ (psiAcc 4272).2.2 ∧ 2 ^ 33456 ≤ (psiAcc 4272).2.1 ^ 8 ∧ 2 ^ 49514 ≤ (psiAcc 4272).1 ^ 8 := by
  decide +kernel

/-- For `x > 4272`: `4290.061 x - 9208149 ≤ x ψ₁(x)` (sharp on `(4272, 4288]`). -/
theorem psiOne_lower_grid2_mul_4272 {x : ℝ} (hx : 4272 < x) : 4290.061 * x - 9208149 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4272.1 psiOneGrid2_cert_4272.2.1 psiOneGrid2_cert_4272.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4272`: `ψ₁(x) ≥ 4290.061 - 9208149/x` (sharp on `(4272, 4288]`). -/
theorem psiOne_lower_grid2_4272 {x : ℝ} (hx : 4272 < x) : 4290.061 - 9208149 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4272.1 psiOneGrid2_cert_4272.2.1 psiOneGrid2_cert_4272.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4272 {x : ℝ} (hx : 4272 < x) (hx' : x ≤ 4288) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4272 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4288 :
    13247488 ≤ (psiAcc 4288).2.2 ∧ 2 ^ 61671 ≤ (psiAcc 4288).2.1 ^ 8 ∧ 2 ^ 49707 ≤ (psiAcc 4288).1 ^ 8 := by
  decide +kernel

/-- For `x > 4288`: `4306.783 x - 9279685 ≤ x ψ₁(x)` (sharp on `(4288, 4304]`). -/
theorem psiOne_lower_grid2_mul_4288 {x : ℝ} (hx : 4288 < x) : 4306.783 * x - 9279685 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4288.1 psiOneGrid2_cert_4288.2.1 psiOneGrid2_cert_4288.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4288`: `ψ₁(x) ≥ 4306.783 - 9279685/x` (sharp on `(4288, 4304]`). -/
theorem psiOne_lower_grid2_4288 {x : ℝ} (hx : 4288 < x) : 4306.783 - 9279685 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4288.1 psiOneGrid2_cert_4288.2.1 psiOneGrid2_cert_4288.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4288 {x : ℝ} (hx : 4288 < x) (hx' : x ≤ 4304) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4288 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4304 :
    13351936 ≤ (psiAcc 4304).2.2 ∧ 2 ^ 23536 ≤ (psiAcc 4304).2.1 ^ 8 ∧ 2 ^ 49900 ≤ (psiAcc 4304).1 ^ 8 := by
  decide +kernel

/-- For `x > 4304`: `4323.505 x - 9351472 ≤ x ψ₁(x)` (sharp on `(4304, 4320]`). -/
theorem psiOne_lower_grid2_mul_4304 {x : ℝ} (hx : 4304 < x) : 4323.505 * x - 9351472 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4304.1 psiOneGrid2_cert_4304.2.1 psiOneGrid2_cert_4304.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4304`: `ψ₁(x) ≥ 4323.505 - 9351472/x` (sharp on `(4304, 4320]`). -/
theorem psiOne_lower_grid2_4304 {x : ℝ} (hx : 4304 < x) : 4323.505 - 9351472 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4304.1 psiOneGrid2_cert_4304.2.1 psiOneGrid2_cert_4304.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4304 {x : ℝ} (hx : 4304 < x) (hx' : x ≤ 4320) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4304 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4320 :
    13447680 ≤ (psiAcc 4320).2.2 ∧ 2 ^ 55998 ≤ (psiAcc 4320).2.1 ^ 8 ∧ 2 ^ 49900 ≤ (psiAcc 4320).1 ^ 8 := by
  decide +kernel

/-- For `x > 4320`: `4323.505 x - 9351471 ≤ x ψ₁(x)` (sharp on `(4320, 4336]`). -/
theorem psiOne_lower_grid2_mul_4320 {x : ℝ} (hx : 4320 < x) : 4323.505 * x - 9351471 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4320.1 psiOneGrid2_cert_4320.2.1 psiOneGrid2_cert_4320.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4320`: `ψ₁(x) ≥ 4323.505 - 9351471/x` (sharp on `(4320, 4336]`). -/
theorem psiOne_lower_grid2_4320 {x : ℝ} (hx : 4320 < x) : 4323.505 - 9351471 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4320.1 psiOneGrid2_cert_4320.2.1 psiOneGrid2_cert_4320.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4320 {x : ℝ} (hx : 4320 < x) (hx' : x ≤ 4336) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4320 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4336 :
    13552128 ≤ (psiAcc 4336).2.2 ∧ 2 ^ 19698 ≤ (psiAcc 4336).2.1 ^ 8 ∧ 2 ^ 49997 ≤ (psiAcc 4336).1 ^ 8 := by
  decide +kernel

/-- For `x > 4336`: `4331.909 x - 9387836 ≤ x ψ₁(x)` (sharp on `(4336, 4352]`). -/
theorem psiOne_lower_grid2_mul_4336 {x : ℝ} (hx : 4336 < x) : 4331.909 * x - 9387836 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4336.1 psiOneGrid2_cert_4336.2.1 psiOneGrid2_cert_4336.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4336`: `ψ₁(x) ≥ 4331.909 - 9387836/x` (sharp on `(4336, 4352]`). -/
theorem psiOne_lower_grid2_4336 {x : ℝ} (hx : 4336 < x) : 4331.909 - 9387836 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4336.1 psiOneGrid2_cert_4336.2.1 psiOneGrid2_cert_4336.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4336 {x : ℝ} (hx : 4336 < x) (hx' : x ≤ 4352) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4336 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4352 :
    13647872 ≤ (psiAcc 4352).2.2 ∧ 2 ^ 56704 ≤ (psiAcc 4352).2.1 ^ 8 ∧ 2 ^ 50287 ≤ (psiAcc 4352).1 ^ 8 := by
  decide +kernel

/-- For `x > 4352`: `4357.036 x - 9496926 ≤ x ψ₁(x)` (sharp on `(4352, 4368]`). -/
theorem psiOne_lower_grid2_mul_4352 {x : ℝ} (hx : 4352 < x) : 4357.036 * x - 9496926 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4352.1 psiOneGrid2_cert_4352.2.1 psiOneGrid2_cert_4352.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4352`: `ψ₁(x) ≥ 4357.036 - 9496926/x` (sharp on `(4352, 4368]`). -/
theorem psiOne_lower_grid2_4352 {x : ℝ} (hx : 4352 < x) : 4357.036 - 9496926 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4352.1 psiOneGrid2_cert_4352.2.1 psiOneGrid2_cert_4352.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4352 {x : ℝ} (hx : 4352 < x) (hx' : x ≤ 4368) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4352 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4368 :
    13752320 ≤ (psiAcc 4368).2.2 ∧ 2 ^ 27268 ≤ (psiAcc 4368).2.1 ^ 8 ∧ 2 ^ 50480 ≤ (psiAcc 4368).1 ^ 8 := by
  decide +kernel

/-- For `x > 4368`: `4373.758 x - 9569834 ≤ x ψ₁(x)` (sharp on `(4368, 4384]`). -/
theorem psiOne_lower_grid2_mul_4368 {x : ℝ} (hx : 4368 < x) : 4373.758 * x - 9569834 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4368.1 psiOneGrid2_cert_4368.2.1 psiOneGrid2_cert_4368.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4368`: `ψ₁(x) ≥ 4373.758 - 9569834/x` (sharp on `(4368, 4384]`). -/
theorem psiOne_lower_grid2_4368 {x : ℝ} (hx : 4368 < x) : 4373.758 - 9569834 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4368.1 psiOneGrid2_cert_4368.2.1 psiOneGrid2_cert_4368.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4368 {x : ℝ} (hx : 4368 < x) (hx' : x ≤ 4384) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4368 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4384 :
    13848064 ≤ (psiAcc 4384).2.2 ∧ 2 ^ 70076 ≤ (psiAcc 4384).2.1 ^ 8 ∧ 2 ^ 50577 ≤ (psiAcc 4384).1 ^ 8 := by
  decide +kernel

/-- For `x > 4384`: `4382.163 x - 9606585 ≤ x ψ₁(x)` (sharp on `(4384, 4400]`). -/
theorem psiOne_lower_grid2_mul_4384 {x : ℝ} (hx : 4384 < x) : 4382.163 * x - 9606585 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4384.1 psiOneGrid2_cert_4384.2.1 psiOneGrid2_cert_4384.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4384`: `ψ₁(x) ≥ 4382.163 - 9606585/x` (sharp on `(4384, 4400]`). -/
theorem psiOne_lower_grid2_4384 {x : ℝ} (hx : 4384 < x) : 4382.163 - 9606585 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4384.1 psiOneGrid2_cert_4384.2.1 psiOneGrid2_cert_4384.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4384 {x : ℝ} (hx : 4384 < x) (hx' : x ≤ 4400) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4384 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4400 :
    13952512 ≤ (psiAcc 4400).2.2 ∧ 2 ^ 44897 ≤ (psiAcc 4400).2.1 ^ 8 ∧ 2 ^ 50771 ≤ (psiAcc 4400).1 ^ 8 := by
  decide +kernel

/-- For `x > 4400`: `4398.971 x - 9680443 ≤ x ψ₁(x)` (sharp on `(4400, 4416]`). -/
theorem psiOne_lower_grid2_mul_4400 {x : ℝ} (hx : 4400 < x) : 4398.971 * x - 9680443 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4400.1 psiOneGrid2_cert_4400.2.1 psiOneGrid2_cert_4400.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4400`: `ψ₁(x) ≥ 4398.971 - 9680443/x` (sharp on `(4400, 4416]`). -/
theorem psiOne_lower_grid2_4400 {x : ℝ} (hx : 4400 < x) : 4398.971 - 9680443 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4400.1 psiOneGrid2_cert_4400.2.1 psiOneGrid2_cert_4400.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4400 {x : ℝ} (hx : 4400 < x) (hx' : x ≤ 4416) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4400 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4416 :
    14056960 ≤ (psiAcc 4416).2.2 ∧ 2 ^ 22333 ≤ (psiAcc 4416).2.1 ^ 8 ∧ 2 ^ 50868 ≤ (psiAcc 4416).1 ^ 8 := by
  decide +kernel

/-- For `x > 4416`: `4407.376 x - 9717497 ≤ x ψ₁(x)` (sharp on `(4416, 4432]`). -/
theorem psiOne_lower_grid2_mul_4416 {x : ℝ} (hx : 4416 < x) : 4407.376 * x - 9717497 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4416.1 psiOneGrid2_cert_4416.2.1 psiOneGrid2_cert_4416.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4416`: `ψ₁(x) ≥ 4407.376 - 9717497/x` (sharp on `(4416, 4432]`). -/
theorem psiOne_lower_grid2_4416 {x : ℝ} (hx : 4416 < x) : 4407.376 - 9717497 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4416.1 psiOneGrid2_cert_4416.2.1 psiOneGrid2_cert_4416.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4416 {x : ℝ} (hx : 4416 < x) (hx' : x ≤ 4432) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4416 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4432 :
    14152704 ≤ (psiAcc 4432).2.2 ∧ 2 ^ 72210 ≤ (psiAcc 4432).2.1 ^ 8 ∧ 2 ^ 51061 ≤ (psiAcc 4432).1 ^ 8 := by
  decide +kernel

/-- For `x > 4432`: `4424.098 x - 9791442 ≤ x ψ₁(x)` (sharp on `(4432, 4448]`). -/
theorem psiOne_lower_grid2_mul_4432 {x : ℝ} (hx : 4432 < x) : 4424.098 * x - 9791442 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4432.1 psiOneGrid2_cert_4432.2.1 psiOneGrid2_cert_4432.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4432`: `ψ₁(x) ≥ 4424.098 - 9791442/x` (sharp on `(4432, 4448]`). -/
theorem psiOne_lower_grid2_4432 {x : ℝ} (hx : 4432 < x) : 4424.098 - 9791442 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4432.1 psiOneGrid2_cert_4432.2.1 psiOneGrid2_cert_4432.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4432 {x : ℝ} (hx : 4432 < x) (hx' : x ≤ 4448) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4432 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4448 :
    14257152 ≤ (psiAcc 4448).2.2 ∧ 2 ^ 54393 ≤ (psiAcc 4448).2.1 ^ 8 ∧ 2 ^ 51255 ≤ (psiAcc 4448).1 ^ 8 := by
  decide +kernel

/-- For `x > 4448`: `4440.907 x - 9866139 ≤ x ψ₁(x)` (sharp on `(4448, 4464]`). -/
theorem psiOne_lower_grid2_mul_4448 {x : ℝ} (hx : 4448 < x) : 4440.907 * x - 9866139 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4448.1 psiOneGrid2_cert_4448.2.1 psiOneGrid2_cert_4448.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4448`: `ψ₁(x) ≥ 4440.907 - 9866139/x` (sharp on `(4448, 4464]`). -/
theorem psiOne_lower_grid2_4448 {x : ℝ} (hx : 4448 < x) : 4440.907 - 9866139 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4448.1 psiOneGrid2_cert_4448.2.1 psiOneGrid2_cert_4448.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4448 {x : ℝ} (hx : 4448 < x) (hx' : x ≤ 4464) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4448 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4464 :
    14361600 ≤ (psiAcc 4464).2.2 ∧ 2 ^ 40939 ≤ (psiAcc 4464).2.1 ^ 8 ∧ 2 ^ 51546 ≤ (psiAcc 4464).1 ^ 8 := by
  decide +kernel

/-- For `x > 4464`: `4466.120 x - 9978513 ≤ x ψ₁(x)` (sharp on `(4464, 4480]`). -/
theorem psiOne_lower_grid2_mul_4464 {x : ℝ} (hx : 4464 < x) : 4466.120 * x - 9978513 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4464.1 psiOneGrid2_cert_4464.2.1 psiOneGrid2_cert_4464.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4464`: `ψ₁(x) ≥ 4466.120 - 9978513/x` (sharp on `(4464, 4480]`). -/
theorem psiOne_lower_grid2_4464 {x : ℝ} (hx : 4464 < x) : 4466.120 - 9978513 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4464.1 psiOneGrid2_cert_4464.2.1 psiOneGrid2_cert_4464.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4464 {x : ℝ} (hx : 4464 < x) (hx' : x ≤ 4480) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4464 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4480 :
    14466048 ≤ (psiAcc 4480).2.2 ∧ 2 ^ 30104 ≤ (psiAcc 4480).2.1 ^ 8 ∧ 2 ^ 51546 ≤ (psiAcc 4480).1 ^ 8 := by
  decide +kernel

/-- For `x > 4480`: `4466.120 x - 9978512 ≤ x ψ₁(x)` (sharp on `(4480, 4496]`). -/
theorem psiOne_lower_grid2_mul_4480 {x : ℝ} (hx : 4480 < x) : 4466.120 * x - 9978512 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4480.1 psiOneGrid2_cert_4480.2.1 psiOneGrid2_cert_4480.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4480`: `ψ₁(x) ≥ 4466.120 - 9978512/x` (sharp on `(4480, 4496]`). -/
theorem psiOne_lower_grid2_4480 {x : ℝ} (hx : 4480 < x) : 4466.120 - 9978512 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4480.1 psiOneGrid2_cert_4480.2.1 psiOneGrid2_cert_4480.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4480 {x : ℝ} (hx : 4480 < x) (hx' : x ≤ 4496) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4480 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4496 :
    14570496 ≤ (psiAcc 4496).2.2 ∧ 2 ^ 22617 ≤ (psiAcc 4496).2.1 ^ 8 ∧ 2 ^ 51886 ≤ (psiAcc 4496).1 ^ 8 := by
  decide +kernel

/-- For `x > 4496`: `4495.579 x - 10110667 ≤ x ψ₁(x)` (sharp on `(4496, 4512]`). -/
theorem psiOne_lower_grid2_mul_4496 {x : ℝ} (hx : 4496 < x) : 4495.579 * x - 10110667 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4496.1 psiOneGrid2_cert_4496.2.1 psiOneGrid2_cert_4496.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4496`: `ψ₁(x) ≥ 4495.579 - 10110667/x` (sharp on `(4496, 4512]`). -/
theorem psiOne_lower_grid2_4496 {x : ℝ} (hx : 4496 < x) : 4495.579 - 10110667 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4496.1 psiOneGrid2_cert_4496.2.1 psiOneGrid2_cert_4496.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4496 {x : ℝ} (hx : 4496 < x) (hx' : x ≤ 4512) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4496 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4512 :
    14674944 ≤ (psiAcc 4512).2.2 ∧ 2 ^ 17702 ≤ (psiAcc 4512).2.1 ^ 8 ∧ 2 ^ 51983 ≤ (psiAcc 4512).1 ^ 8 := by
  decide +kernel

/-- For `x > 4512`: `4503.983 x - 10148545 ≤ x ψ₁(x)` (sharp on `(4512, 4528]`). -/
theorem psiOne_lower_grid2_mul_4512 {x : ℝ} (hx : 4512 < x) : 4503.983 * x - 10148545 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4512.1 psiOneGrid2_cert_4512.2.1 psiOneGrid2_cert_4512.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4512`: `ψ₁(x) ≥ 4503.983 - 10148545/x` (sharp on `(4512, 4528]`). -/
theorem psiOne_lower_grid2_4512 {x : ℝ} (hx : 4512 < x) : 4503.983 - 10148545 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4512.1 psiOneGrid2_cert_4512.2.1 psiOneGrid2_cert_4512.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4512 {x : ℝ} (hx : 4512 < x) (hx' : x ≤ 4528) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4512 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4528 :
    14779392 ≤ (psiAcc 4528).2.2 ∧ 2 ^ 17740 ≤ (psiAcc 4528).2.1 ^ 8 ∧ 2 ^ 52372 ≤ (psiAcc 4528).1 ^ 8 := by
  decide +kernel

/-- For `x > 4528`: `4537.688 x - 10300821 ≤ x ψ₁(x)` (sharp on `(4528, 4544]`). -/
theorem psiOne_lower_grid2_mul_4528 {x : ℝ} (hx : 4528 < x) : 4537.688 * x - 10300821 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4528.1 psiOneGrid2_cert_4528.2.1 psiOneGrid2_cert_4528.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4528`: `ψ₁(x) ≥ 4537.688 - 10300821/x` (sharp on `(4528, 4544]`). -/
theorem psiOne_lower_grid2_4528 {x : ℝ} (hx : 4528 < x) : 4537.688 - 10300821 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4528.1 psiOneGrid2_cert_4528.2.1 psiOneGrid2_cert_4528.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4528 {x : ℝ} (hx : 4528 < x) (hx' : x ≤ 4544) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4528 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4544 :
    14883840 ≤ (psiAcc 4544).2.2 ∧ 2 ^ 20109 ≤ (psiAcc 4544).2.1 ^ 8 ∧ 2 ^ 52372 ≤ (psiAcc 4544).1 ^ 8 := by
  decide +kernel

/-- For `x > 4544`: `4537.688 x - 10300821 ≤ x ψ₁(x)` (sharp on `(4544, 4560]`). -/
theorem psiOne_lower_grid2_mul_4544 {x : ℝ} (hx : 4544 < x) : 4537.688 * x - 10300821 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4544.1 psiOneGrid2_cert_4544.2.1 psiOneGrid2_cert_4544.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4544`: `ψ₁(x) ≥ 4537.688 - 10300821/x` (sharp on `(4544, 4560]`). -/
theorem psiOne_lower_grid2_4544 {x : ℝ} (hx : 4544 < x) : 4537.688 - 10300821 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4544.1 psiOneGrid2_cert_4544.2.1 psiOneGrid2_cert_4544.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4544 {x : ℝ} (hx : 4544 < x) (hx' : x ≤ 4560) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4544 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4560 :
    14988288 ≤ (psiAcc 4560).2.2 ∧ 2 ^ 24812 ≤ (psiAcc 4560).2.1 ^ 8 ∧ 2 ^ 52566 ≤ (psiAcc 4560).1 ^ 8 := by
  decide +kernel

/-- For `x > 4560`: `4554.496 x - 10377267 ≤ x ψ₁(x)` (sharp on `(4560, 4576]`). -/
theorem psiOne_lower_grid2_mul_4560 {x : ℝ} (hx : 4560 < x) : 4554.496 * x - 10377267 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4560.1 psiOneGrid2_cert_4560.2.1 psiOneGrid2_cert_4560.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4560`: `ψ₁(x) ≥ 4554.496 - 10377267/x` (sharp on `(4560, 4576]`). -/
theorem psiOne_lower_grid2_4560 {x : ℝ} (hx : 4560 < x) : 4554.496 - 10377267 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4560.1 psiOneGrid2_cert_4560.2.1 psiOneGrid2_cert_4560.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4560 {x : ℝ} (hx : 4560 < x) (hx' : x ≤ 4576) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4560 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4576 :
    15092736 ≤ (psiAcc 4576).2.2 ∧ 2 ^ 32626 ≤ (psiAcc 4576).2.1 ^ 8 ∧ 2 ^ 52761 ≤ (psiAcc 4576).1 ^ 8 := by
  decide +kernel

/-- For `x > 4576`: `4571.392 x - 10454377 ≤ x ψ₁(x)` (sharp on `(4576, 4592]`). -/
theorem psiOne_lower_grid2_mul_4576 {x : ℝ} (hx : 4576 < x) : 4571.392 * x - 10454377 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4576.1 psiOneGrid2_cert_4576.2.1 psiOneGrid2_cert_4576.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4576`: `ψ₁(x) ≥ 4571.392 - 10454377/x` (sharp on `(4576, 4592]`). -/
theorem psiOne_lower_grid2_4576 {x : ℝ} (hx : 4576 < x) : 4571.392 - 10454377 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4576.1 psiOneGrid2_cert_4576.2.1 psiOneGrid2_cert_4576.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4576 {x : ℝ} (hx : 4576 < x) (hx' : x ≤ 4592) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4576 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4592 :
    15197184 ≤ (psiAcc 4592).2.2 ∧ 2 ^ 42191 ≤ (psiAcc 4592).2.1 ^ 8 ∧ 2 ^ 52955 ≤ (psiAcc 4592).1 ^ 8 := by
  decide +kernel

/-- For `x > 4592`: `4588.201 x - 10531479 ≤ x ψ₁(x)` (sharp on `(4592, 4608]`). -/
theorem psiOne_lower_grid2_mul_4592 {x : ℝ} (hx : 4592 < x) : 4588.201 * x - 10531479 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4592.1 psiOneGrid2_cert_4592.2.1 psiOneGrid2_cert_4592.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4592`: `ψ₁(x) ≥ 4588.201 - 10531479/x` (sharp on `(4592, 4608]`). -/
theorem psiOne_lower_grid2_4592 {x : ℝ} (hx : 4592 < x) : 4588.201 - 10531479 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4592.1 psiOneGrid2_cert_4592.2.1 psiOneGrid2_cert_4592.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4592 {x : ℝ} (hx : 4592 < x) (hx' : x ≤ 4608) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4592 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4608 :
    15301632 ≤ (psiAcc 4608).2.2 ∧ 2 ^ 55454 ≤ (psiAcc 4608).2.1 ^ 8 ∧ 2 ^ 53150 ≤ (psiAcc 4608).1 ^ 8 := by
  decide +kernel

/-- For `x > 4608`: `4605.096 x - 10609198 ≤ x ψ₁(x)` (sharp on `(4608, 4624]`). -/
theorem psiOne_lower_grid2_mul_4608 {x : ℝ} (hx : 4608 < x) : 4605.096 * x - 10609198 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4608.1 psiOneGrid2_cert_4608.2.1 psiOneGrid2_cert_4608.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4608`: `ψ₁(x) ≥ 4605.096 - 10609198/x` (sharp on `(4608, 4624]`). -/
theorem psiOne_lower_grid2_4608 {x : ℝ} (hx : 4608 < x) : 4605.096 - 10609198 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4608.1 psiOneGrid2_cert_4608.2.1 psiOneGrid2_cert_4608.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4608 {x : ℝ} (hx : 4608 < x) (hx' : x ≤ 4624) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4608 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4624 :
    15406080 ≤ (psiAcc 4624).2.2 ∧ 2 ^ 70567 ≤ (psiAcc 4624).2.1 ^ 8 ∧ 2 ^ 53247 ≤ (psiAcc 4624).1 ^ 8 := by
  decide +kernel

/-- For `x > 4624`: `4613.500 x - 10648034 ≤ x ψ₁(x)` (sharp on `(4624, 4640]`). -/
theorem psiOne_lower_grid2_mul_4624 {x : ℝ} (hx : 4624 < x) : 4613.500 * x - 10648034 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4624.1 psiOneGrid2_cert_4624.2.1 psiOneGrid2_cert_4624.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4624`: `ψ₁(x) ≥ 4613.500 - 10648034/x` (sharp on `(4624, 4640]`). -/
theorem psiOne_lower_grid2_4624 {x : ℝ} (hx : 4624 < x) : 4613.500 - 10648034 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4624.1 psiOneGrid2_cert_4624.2.1 psiOneGrid2_cert_4624.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4624 {x : ℝ} (hx : 4624 < x) (hx' : x ≤ 4640) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4624 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4640 :
    15519232 ≤ (psiAcc 4640).2.2 ∧ 2 ^ 17704 ≤ (psiAcc 4640).2.1 ^ 8 ∧ 2 ^ 53442 ≤ (psiAcc 4640).1 ^ 8 := by
  decide +kernel

/-- For `x > 4640`: `4630.396 x - 10726394 ≤ x ψ₁(x)` (sharp on `(4640, 4656]`). -/
theorem psiOne_lower_grid2_mul_4640 {x : ℝ} (hx : 4640 < x) : 4630.396 * x - 10726394 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4640.1 psiOneGrid2_cert_4640.2.1 psiOneGrid2_cert_4640.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4640`: `ψ₁(x) ≥ 4630.396 - 10726394/x` (sharp on `(4640, 4656]`). -/
theorem psiOne_lower_grid2_4640 {x : ℝ} (hx : 4640 < x) : 4630.396 - 10726394 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4640.1 psiOneGrid2_cert_4640.2.1 psiOneGrid2_cert_4640.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4640 {x : ℝ} (hx : 4640 < x) (hx' : x ≤ 4656) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4640 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4656 :
    15623680 ≤ (psiAcc 4656).2.2 ∧ 2 ^ 39637 ≤ (psiAcc 4656).2.1 ^ 8 ∧ 2 ^ 53734 ≤ (psiAcc 4656).1 ^ 8 := by
  decide +kernel

/-- For `x > 4656`: `4655.696 x - 10843979 ≤ x ψ₁(x)` (sharp on `(4656, 4672]`). -/
theorem psiOne_lower_grid2_mul_4656 {x : ℝ} (hx : 4656 < x) : 4655.696 * x - 10843979 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4656.1 psiOneGrid2_cert_4656.2.1 psiOneGrid2_cert_4656.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4656`: `ψ₁(x) ≥ 4655.696 - 10843979/x` (sharp on `(4656, 4672]`). -/
theorem psiOne_lower_grid2_4656 {x : ℝ} (hx : 4656 < x) : 4655.696 - 10843979 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4656.1 psiOneGrid2_cert_4656.2.1 psiOneGrid2_cert_4656.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4656 {x : ℝ} (hx : 4656 < x) (hx' : x ≤ 4672) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4656 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4672 :
    15728128 ≤ (psiAcc 4672).2.2 ∧ 2 ^ 66152 ≤ (psiAcc 4672).2.1 ^ 8 ∧ 2 ^ 53929 ≤ (psiAcc 4672).1 ^ 8 := by
  decide +kernel

/-- For `x > 4672`: `4672.591 x - 10922710 ≤ x ψ₁(x)` (sharp on `(4672, 4688]`). -/
theorem psiOne_lower_grid2_mul_4672 {x : ℝ} (hx : 4672 < x) : 4672.591 * x - 10922710 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4672.1 psiOneGrid2_cert_4672.2.1 psiOneGrid2_cert_4672.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4672`: `ψ₁(x) ≥ 4672.591 - 10922710/x` (sharp on `(4672, 4688]`). -/
theorem psiOne_lower_grid2_4672 {x : ℝ} (hx : 4672 < x) : 4672.591 - 10922710 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4672.1 psiOneGrid2_cert_4672.2.1 psiOneGrid2_cert_4672.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4672 {x : ℝ} (hx : 4672 < x) (hx' : x ≤ 4688) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4672 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4688 :
    15841280 ≤ (psiAcc 4688).2.2 ∧ 2 ^ 26155 ≤ (psiAcc 4688).2.1 ^ 8 ∧ 2 ^ 54124 ≤ (psiAcc 4688).1 ^ 8 := by
  decide +kernel

/-- For `x > 4688`: `4689.487 x - 11001712 ≤ x ψ₁(x)` (sharp on `(4688, 4704]`). -/
theorem psiOne_lower_grid2_mul_4688 {x : ℝ} (hx : 4688 < x) : 4689.487 * x - 11001712 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4688.1 psiOneGrid2_cert_4688.2.1 psiOneGrid2_cert_4688.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4688`: `ψ₁(x) ≥ 4689.487 - 11001712/x` (sharp on `(4688, 4704]`). -/
theorem psiOne_lower_grid2_4688 {x : ℝ} (hx : 4688 < x) : 4689.487 - 11001712 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4688.1 psiOneGrid2_cert_4688.2.1 psiOneGrid2_cert_4688.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4688 {x : ℝ} (hx : 4688 < x) (hx' : x ≤ 4704) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4688 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4704 :
    15945728 ≤ (psiAcc 4704).2.2 ∧ 2 ^ 57937 ≤ (psiAcc 4704).2.1 ^ 8 ∧ 2 ^ 54320 ≤ (psiAcc 4704).1 ^ 8 := by
  decide +kernel

/-- For `x > 4704`: `4706.469 x - 11081476 ≤ x ψ₁(x)` (sharp on `(4704, 4720]`). -/
theorem psiOne_lower_grid2_mul_4704 {x : ℝ} (hx : 4704 < x) : 4706.469 * x - 11081476 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4704.1 psiOneGrid2_cert_4704.2.1 psiOneGrid2_cert_4704.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4704`: `ψ₁(x) ≥ 4706.469 - 11081476/x` (sharp on `(4704, 4720]`). -/
theorem psiOne_lower_grid2_4704 {x : ℝ} (hx : 4704 < x) : 4706.469 - 11081476 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4704.1 psiOneGrid2_cert_4704.2.1 psiOneGrid2_cert_4704.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4704 {x : ℝ} (hx : 4704 < x) (hx' : x ≤ 4720) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4704 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4720 :
    16058880 ≤ (psiAcc 4720).2.2 ∧ 2 ^ 21843 ≤ (psiAcc 4720).2.1 ^ 8 ∧ 2 ^ 54320 ≤ (psiAcc 4720).1 ^ 8 := by
  decide +kernel

/-- For `x > 4720`: `4706.469 x - 11081476 ≤ x ψ₁(x)` (sharp on `(4720, 4736]`). -/
theorem psiOne_lower_grid2_mul_4720 {x : ℝ} (hx : 4720 < x) : 4706.469 * x - 11081476 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4720.1 psiOneGrid2_cert_4720.2.1 psiOneGrid2_cert_4720.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4720`: `ψ₁(x) ≥ 4706.469 - 11081476/x` (sharp on `(4720, 4736]`). -/
theorem psiOne_lower_grid2_4720 {x : ℝ} (hx : 4720 < x) : 4706.469 - 11081476 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4720.1 psiOneGrid2_cert_4720.2.1 psiOneGrid2_cert_4720.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4720 {x : ℝ} (hx : 4720 < x) (hx' : x ≤ 4736) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4720 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4736 :
    16163328 ≤ (psiAcc 4736).2.2 ∧ 2 ^ 59091 ≤ (psiAcc 4736).2.1 ^ 8 ∧ 2 ^ 54710 ≤ (psiAcc 4736).1 ^ 8 := by
  decide +kernel

/-- For `x > 4736`: `4740.260 x - 11241188 ≤ x ψ₁(x)` (sharp on `(4736, 4752]`). -/
theorem psiOne_lower_grid2_mul_4736 {x : ℝ} (hx : 4736 < x) : 4740.260 * x - 11241188 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4736.1 psiOneGrid2_cert_4736.2.1 psiOneGrid2_cert_4736.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4736`: `ψ₁(x) ≥ 4740.260 - 11241188/x` (sharp on `(4736, 4752]`). -/
theorem psiOne_lower_grid2_4736 {x : ℝ} (hx : 4736 < x) : 4740.260 - 11241188 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4736.1 psiOneGrid2_cert_4736.2.1 psiOneGrid2_cert_4736.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4736 {x : ℝ} (hx : 4736 < x) (hx' : x ≤ 4752) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4736 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4752 :
    16276480 ≤ (psiAcc 4752).2.2 ∧ 2 ^ 29345 ≤ (psiAcc 4752).2.1 ^ 8 ∧ 2 ^ 54808 ≤ (psiAcc 4752).1 ^ 8 := by
  decide +kernel

/-- For `x > 4752`: `4748.751 x - 11281528 ≤ x ψ₁(x)` (sharp on `(4752, 4768]`). -/
theorem psiOne_lower_grid2_mul_4752 {x : ℝ} (hx : 4752 < x) : 4748.751 * x - 11281528 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4752.1 psiOneGrid2_cert_4752.2.1 psiOneGrid2_cert_4752.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4752`: `ψ₁(x) ≥ 4748.751 - 11281528/x` (sharp on `(4752, 4768]`). -/
theorem psiOne_lower_grid2_4752 {x : ℝ} (hx : 4752 < x) : 4748.751 - 11281528 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4752.1 psiOneGrid2_cert_4752.2.1 psiOneGrid2_cert_4752.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4752 {x : ℝ} (hx : 4752 < x) (hx' : x ≤ 4768) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4752 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4768 :
    16380928 ≤ (psiAcc 4768).2.2 ∧ 2 ^ 71576 ≤ (psiAcc 4768).2.1 ^ 8 ∧ 2 ^ 54906 ≤ (psiAcc 4768).1 ^ 8 := by
  decide +kernel

/-- For `x > 4768`: `4757.242 x - 11321937 ≤ x ψ₁(x)` (sharp on `(4768, 4784]`). -/
theorem psiOne_lower_grid2_mul_4768 {x : ℝ} (hx : 4768 < x) : 4757.242 * x - 11321937 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4768.1 psiOneGrid2_cert_4768.2.1 psiOneGrid2_cert_4768.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4768`: `ψ₁(x) ≥ 4757.242 - 11321937/x` (sharp on `(4768, 4784]`). -/
theorem psiOne_lower_grid2_4768 {x : ℝ} (hx : 4768 < x) : 4757.242 - 11321937 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4768.1 psiOneGrid2_cert_4768.2.1 psiOneGrid2_cert_4768.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4768 {x : ℝ} (hx : 4768 < x) (hx' : x ≤ 4784) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4768 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4784 :
    16494080 ≤ (psiAcc 4784).2.2 ∧ 2 ^ 44957 ≤ (psiAcc 4784).2.1 ^ 8 ∧ 2 ^ 55003 ≤ (psiAcc 4784).1 ^ 8 := by
  decide +kernel

/-- For `x > 4784`: `4765.646 x - 11362134 ≤ x ψ₁(x)` (sharp on `(4784, 4800]`). -/
theorem psiOne_lower_grid2_mul_4784 {x : ℝ} (hx : 4784 < x) : 4765.646 * x - 11362134 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4784.1 psiOneGrid2_cert_4784.2.1 psiOneGrid2_cert_4784.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4784`: `ψ₁(x) ≥ 4765.646 - 11362134/x` (sharp on `(4784, 4800]`). -/
theorem psiOne_lower_grid2_4784 {x : ℝ} (hx : 4784 < x) : 4765.646 - 11362134 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4784.1 psiOneGrid2_cert_4784.2.1 psiOneGrid2_cert_4784.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4784 {x : ℝ} (hx : 4784 < x) (hx' : x ≤ 4800) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4784 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4800 :
    16607232 ≤ (psiAcc 4800).2.2 ∧ 2 ^ 22934 ≤ (psiAcc 4800).2.1 ^ 8 ∧ 2 ^ 55395 ≤ (psiAcc 4800).1 ^ 8 := by
  decide +kernel

/-- For `x > 4800`: `4799.611 x - 11524890 ≤ x ψ₁(x)` (sharp on `(4800, 4816]`). -/
theorem psiOne_lower_grid2_mul_4800 {x : ℝ} (hx : 4800 < x) : 4799.611 * x - 11524890 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4800.1 psiOneGrid2_cert_4800.2.1 psiOneGrid2_cert_4800.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4800`: `ψ₁(x) ≥ 4799.611 - 11524890/x` (sharp on `(4800, 4816]`). -/
theorem psiOne_lower_grid2_4800 {x : ℝ} (hx : 4800 < x) : 4799.611 - 11524890 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4800.1 psiOneGrid2_cert_4800.2.1 psiOneGrid2_cert_4800.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4800 {x : ℝ} (hx : 4800 < x) (hx' : x ≤ 4816) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4800 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4816 :
    16720384 ≤ (psiAcc 4816).2.2 ∧ 2 ^ 5802 ≤ (psiAcc 4816).2.1 ^ 8 ∧ 2 ^ 55590 ≤ (psiAcc 4816).1 ^ 8 := by
  decide +kernel

/-- For `x > 4816`: `4816.506 x - 11606106 ≤ x ψ₁(x)` (sharp on `(4816, 4832]`). -/
theorem psiOne_lower_grid2_mul_4816 {x : ℝ} (hx : 4816 < x) : 4816.506 * x - 11606106 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4816.1 psiOneGrid2_cert_4816.2.1 psiOneGrid2_cert_4816.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4816`: `ψ₁(x) ≥ 4816.506 - 11606106/x` (sharp on `(4816, 4832]`). -/
theorem psiOne_lower_grid2_4816 {x : ℝ} (hx : 4816 < x) : 4816.506 - 11606106 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4816.1 psiOneGrid2_cert_4816.2.1 psiOneGrid2_cert_4816.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4816 {x : ℝ} (hx : 4816 < x) (hx' : x ≤ 4832) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4816 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4832 :
    16824832 ≤ (psiAcc 4832).2.2 ∧ 2 ^ 61239 ≤ (psiAcc 4832).2.1 ^ 8 ∧ 2 ^ 55786 ≤ (psiAcc 4832).1 ^ 8 := by
  decide +kernel

/-- For `x > 4832`: `4833.488 x - 11688026 ≤ x ψ₁(x)` (sharp on `(4832, 4848]`). -/
theorem psiOne_lower_grid2_mul_4832 {x : ℝ} (hx : 4832 < x) : 4833.488 * x - 11688026 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4832.1 psiOneGrid2_cert_4832.2.1 psiOneGrid2_cert_4832.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4832`: `ψ₁(x) ≥ 4833.488 - 11688026/x` (sharp on `(4832, 4848]`). -/
theorem psiOne_lower_grid2_4832 {x : ℝ} (hx : 4832 < x) : 4833.488 - 11688026 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4832.1 psiOneGrid2_cert_4832.2.1 psiOneGrid2_cert_4832.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4832 {x : ℝ} (hx : 4832 < x) (hx' : x ≤ 4848) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4832 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4848 :
    16937984 ≤ (psiAcc 4848).2.2 ∧ 2 ^ 48610 ≤ (psiAcc 4848).2.1 ^ 8 ∧ 2 ^ 55786 ≤ (psiAcc 4848).1 ^ 8 := by
  decide +kernel

/-- For `x > 4848`: `4833.488 x - 11688026 ≤ x ψ₁(x)` (sharp on `(4848, 4864]`). -/
theorem psiOne_lower_grid2_mul_4848 {x : ℝ} (hx : 4848 < x) : 4833.488 * x - 11688026 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4848.1 psiOneGrid2_cert_4848.2.1 psiOneGrid2_cert_4848.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4848`: `ψ₁(x) ≥ 4833.488 - 11688026/x` (sharp on `(4848, 4864]`). -/
theorem psiOne_lower_grid2_4848 {x : ℝ} (hx : 4848 < x) : 4833.488 - 11688026 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4848.1 psiOneGrid2_cert_4848.2.1 psiOneGrid2_cert_4848.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4848 {x : ℝ} (hx : 4848 < x) (hx' : x ≤ 4864) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4848 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4864 :
    17051136 ≤ (psiAcc 4864).2.2 ∧ 2 ^ 36275 ≤ (psiAcc 4864).2.1 ^ 8 ∧ 2 ^ 55884 ≤ (psiAcc 4864).1 ^ 8 := by
  decide +kernel

/-- For `x > 4864`: `4841.979 x - 11729300 ≤ x ψ₁(x)` (sharp on `(4864, 4880]`). -/
theorem psiOne_lower_grid2_mul_4864 {x : ℝ} (hx : 4864 < x) : 4841.979 * x - 11729300 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4864.1 psiOneGrid2_cert_4864.2.1 psiOneGrid2_cert_4864.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4864`: `ψ₁(x) ≥ 4841.979 - 11729300/x` (sharp on `(4864, 4880]`). -/
theorem psiOne_lower_grid2_4864 {x : ℝ} (hx : 4864 < x) : 4841.979 - 11729300 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4864.1 psiOneGrid2_cert_4864.2.1 psiOneGrid2_cert_4864.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4864 {x : ℝ} (hx : 4864 < x) (hx' : x ≤ 4880) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4864 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4880 :
    17164288 ≤ (psiAcc 4880).2.2 ∧ 2 ^ 26390 ≤ (psiAcc 4880).2.1 ^ 8 ∧ 2 ^ 56080 ≤ (psiAcc 4880).1 ^ 8 := by
  decide +kernel

/-- For `x > 4880`: `4858.961 x - 11812069 ≤ x ψ₁(x)` (sharp on `(4880, 4896]`). -/
theorem psiOne_lower_grid2_mul_4880 {x : ℝ} (hx : 4880 < x) : 4858.961 * x - 11812069 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4880.1 psiOneGrid2_cert_4880.2.1 psiOneGrid2_cert_4880.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4880`: `ψ₁(x) ≥ 4858.961 - 11812069/x` (sharp on `(4880, 4896]`). -/
theorem psiOne_lower_grid2_4880 {x : ℝ} (hx : 4880 < x) : 4858.961 - 11812069 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4880.1 psiOneGrid2_cert_4880.2.1 psiOneGrid2_cert_4880.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4880 {x : ℝ} (hx : 4880 < x) (hx' : x ≤ 4896) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4880 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4896 :
    17277440 ≤ (psiAcc 4896).2.2 ∧ 2 ^ 19151 ≤ (psiAcc 4896).2.1 ^ 8 ∧ 2 ^ 56178 ≤ (psiAcc 4896).1 ^ 8 := by
  decide +kernel

/-- For `x > 4896`: `4867.452 x - 11853581 ≤ x ψ₁(x)` (sharp on `(4896, 4912]`). -/
theorem psiOne_lower_grid2_mul_4896 {x : ℝ} (hx : 4896 < x) : 4867.452 * x - 11853581 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4896.1 psiOneGrid2_cert_4896.2.1 psiOneGrid2_cert_4896.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4896`: `ψ₁(x) ≥ 4867.452 - 11853581/x` (sharp on `(4896, 4912]`). -/
theorem psiOne_lower_grid2_4896 {x : ℝ} (hx : 4896 < x) : 4867.452 - 11853581 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4896.1 psiOneGrid2_cert_4896.2.1 psiOneGrid2_cert_4896.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4896 {x : ℝ} (hx : 4896 < x) (hx' : x ≤ 4912) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4896 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4912 :
    17390592 ≤ (psiAcc 4912).2.2 ∧ 2 ^ 13971 ≤ (psiAcc 4912).2.1 ^ 8 ∧ 2 ^ 56374 ≤ (psiAcc 4912).1 ^ 8 := by
  decide +kernel

/-- For `x > 4912`: `4884.434 x - 11936894 ≤ x ψ₁(x)` (sharp on `(4912, 4928]`). -/
theorem psiOne_lower_grid2_mul_4912 {x : ℝ} (hx : 4912 < x) : 4884.434 * x - 11936894 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4912.1 psiOneGrid2_cert_4912.2.1 psiOneGrid2_cert_4912.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4912`: `ψ₁(x) ≥ 4884.434 - 11936894/x` (sharp on `(4912, 4928]`). -/
theorem psiOne_lower_grid2_4912 {x : ℝ} (hx : 4912 < x) : 4884.434 - 11936894 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4912.1 psiOneGrid2_cert_4912.2.1 psiOneGrid2_cert_4912.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4912 {x : ℝ} (hx : 4912 < x) (hx' : x ≤ 4928) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4912 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4928 :
    17503744 ≤ (psiAcc 4928).2.2 ∧ 2 ^ 12127 ≤ (psiAcc 4928).2.1 ^ 8 ∧ 2 ^ 56505 ≤ (psiAcc 4928).1 ^ 8 := by
  decide +kernel

/-- For `x > 4928`: `4895.785 x - 11992708 ≤ x ψ₁(x)` (sharp on `(4928, 4944]`). -/
theorem psiOne_lower_grid2_mul_4928 {x : ℝ} (hx : 4928 < x) : 4895.785 * x - 11992708 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4928.1 psiOneGrid2_cert_4928.2.1 psiOneGrid2_cert_4928.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4928`: `ψ₁(x) ≥ 4895.785 - 11992708/x` (sharp on `(4928, 4944]`). -/
theorem psiOne_lower_grid2_4928 {x : ℝ} (hx : 4928 < x) : 4895.785 - 11992708 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4928.1 psiOneGrid2_cert_4928.2.1 psiOneGrid2_cert_4928.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4928 {x : ℝ} (hx : 4928 < x) (hx' : x ≤ 4944) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4928 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4944 :
    17616896 ≤ (psiAcc 4944).2.2 ∧ 2 ^ 14143 ≤ (psiAcc 4944).2.1 ^ 8 ∧ 2 ^ 56898 ≤ (psiAcc 4944).1 ^ 8 := by
  decide +kernel

/-- For `x > 4944`: `4929.836 x - 12160783 ≤ x ψ₁(x)` (sharp on `(4944, 4960]`). -/
theorem psiOne_lower_grid2_mul_4944 {x : ℝ} (hx : 4944 < x) : 4929.836 * x - 12160783 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4944.1 psiOneGrid2_cert_4944.2.1 psiOneGrid2_cert_4944.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4944`: `ψ₁(x) ≥ 4929.836 - 12160783/x` (sharp on `(4944, 4960]`). -/
theorem psiOne_lower_grid2_4944 {x : ℝ} (hx : 4944 < x) : 4929.836 - 12160783 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4944.1 psiOneGrid2_cert_4944.2.1 psiOneGrid2_cert_4944.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4944 {x : ℝ} (hx : 4944 < x) (hx' : x ≤ 4960) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4944 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4960 :
    17730048 ≤ (psiAcc 4960).2.2 ∧ 2 ^ 20478 ≤ (psiAcc 4960).2.1 ^ 8 ∧ 2 ^ 57094 ≤ (psiAcc 4960).1 ^ 8 := by
  decide +kernel

/-- For `x > 4960`: `4946.818 x - 12244911 ≤ x ψ₁(x)` (sharp on `(4960, 4976]`). -/
theorem psiOne_lower_grid2_mul_4960 {x : ℝ} (hx : 4960 < x) : 4946.818 * x - 12244911 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4960.1 psiOneGrid2_cert_4960.2.1 psiOneGrid2_cert_4960.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4960`: `ψ₁(x) ≥ 4946.818 - 12244911/x` (sharp on `(4960, 4976]`). -/
theorem psiOne_lower_grid2_4960 {x : ℝ} (hx : 4960 < x) : 4946.818 - 12244911 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4960.1 psiOneGrid2_cert_4960.2.1 psiOneGrid2_cert_4960.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4960 {x : ℝ} (hx : 4960 < x) (hx' : x ≤ 4976) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4960 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4976 :
    17843200 ≤ (psiAcc 4976).2.2 ∧ 2 ^ 30644 ≤ (psiAcc 4976).2.1 ^ 8 ∧ 2 ^ 57389 ≤ (psiAcc 4976).1 ^ 8 := by
  decide +kernel

/-- For `x > 4976`: `4972.377 x - 12371934 ≤ x ψ₁(x)` (sharp on `(4976, 4992]`). -/
theorem psiOne_lower_grid2_mul_4976 {x : ℝ} (hx : 4976 < x) : 4972.377 * x - 12371934 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4976.1 psiOneGrid2_cert_4976.2.1 psiOneGrid2_cert_4976.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4976`: `ψ₁(x) ≥ 4972.377 - 12371934/x` (sharp on `(4976, 4992]`). -/
theorem psiOne_lower_grid2_4976 {x : ℝ} (hx : 4976 < x) : 4972.377 - 12371934 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4976.1 psiOneGrid2_cert_4976.2.1 psiOneGrid2_cert_4976.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4976 {x : ℝ} (hx : 4976 < x) (hx' : x ≤ 4992) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4976 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_4992 :
    17956352 ≤ (psiAcc 4992).2.2 ∧ 2 ^ 44150 ≤ (psiAcc 4992).2.1 ^ 8 ∧ 2 ^ 57487 ≤ (psiAcc 4992).1 ^ 8 := by
  decide +kernel

/-- For `x > 4992`: `4980.868 x - 12414278 ≤ x ψ₁(x)` (sharp on `(4992, 5008]`). -/
theorem psiOne_lower_grid2_mul_4992 {x : ℝ} (hx : 4992 < x) : 4980.868 * x - 12414278 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_4992.1 psiOneGrid2_cert_4992.2.1 psiOneGrid2_cert_4992.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 4992`: `ψ₁(x) ≥ 4980.868 - 12414278/x` (sharp on `(4992, 5008]`). -/
theorem psiOne_lower_grid2_4992 {x : ℝ} (hx : 4992 < x) : 4980.868 - 12414278 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_4992.1 psiOneGrid2_cert_4992.2.1 psiOneGrid2_cert_4992.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_4992 {x : ℝ} (hx : 4992 < x) (hx' : x ≤ 5008) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_4992 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5008 :
    18069504 ≤ (psiAcc 5008).2.2 ∧ 2 ^ 61587 ≤ (psiAcc 5008).2.1 ^ 8 ∧ 2 ^ 57782 ≤ (psiAcc 5008).1 ^ 8 := by
  decide +kernel

/-- For `x > 5008`: `5006.428 x - 12542034 ≤ x ψ₁(x)` (sharp on `(5008, 5024]`). -/
theorem psiOne_lower_grid2_mul_5008 {x : ℝ} (hx : 5008 < x) : 5006.428 * x - 12542034 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5008.1 psiOneGrid2_cert_5008.2.1 psiOneGrid2_cert_5008.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5008`: `ψ₁(x) ≥ 5006.428 - 12542034/x` (sharp on `(5008, 5024]`). -/
theorem psiOne_lower_grid2_5008 {x : ℝ} (hx : 5008 < x) : 5006.428 - 12542034 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5008.1 psiOneGrid2_cert_5008.2.1 psiOneGrid2_cert_5008.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5008 {x : ℝ} (hx : 5008 < x) (hx' : x ≤ 5024) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5008 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5024 :
    18191360 ≤ (psiAcc 5024).2.2 ∧ 2 ^ 14406 ≤ (psiAcc 5024).2.1 ^ 8 ∧ 2 ^ 58175 ≤ (psiAcc 5024).1 ^ 8 := by
  decide +kernel

/-- For `x > 5024`: `5040.479 x - 12712832 ≤ x ψ₁(x)` (sharp on `(5024, 5040]`). -/
theorem psiOne_lower_grid2_mul_5024 {x : ℝ} (hx : 5024 < x) : 5040.479 * x - 12712832 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5024.1 psiOneGrid2_cert_5024.2.1 psiOneGrid2_cert_5024.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5024`: `ψ₁(x) ≥ 5040.479 - 12712832/x` (sharp on `(5024, 5040]`). -/
theorem psiOne_lower_grid2_5024 {x : ℝ} (hx : 5024 < x) : 5040.479 - 12712832 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5024.1 psiOneGrid2_cert_5024.2.1 psiOneGrid2_cert_5024.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5024 {x : ℝ} (hx : 5024 < x) (hx' : x ≤ 5040) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5024 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5040 :
    18304512 ≤ (psiAcc 5040).2.2 ∧ 2 ^ 40103 ≤ (psiAcc 5040).2.1 ^ 8 ∧ 2 ^ 58274 ≤ (psiAcc 5040).1 ^ 8 := by
  decide +kernel

/-- For `x > 5040`: `5049.057 x - 12756054 ≤ x ψ₁(x)` (sharp on `(5040, 5056]`). -/
theorem psiOne_lower_grid2_mul_5040 {x : ℝ} (hx : 5040 < x) : 5049.057 * x - 12756054 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5040.1 psiOneGrid2_cert_5040.2.1 psiOneGrid2_cert_5040.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5040`: `ψ₁(x) ≥ 5049.057 - 12756054/x` (sharp on `(5040, 5056]`). -/
theorem psiOne_lower_grid2_5040 {x : ℝ} (hx : 5040 < x) : 5049.057 - 12756054 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5040.1 psiOneGrid2_cert_5040.2.1 psiOneGrid2_cert_5040.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5040 {x : ℝ} (hx : 5040 < x) (hx' : x ≤ 5056) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5040 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5056 :
    18417664 ≤ (psiAcc 5056).2.2 ∧ 2 ^ 68506 ≤ (psiAcc 5056).2.1 ^ 8 ∧ 2 ^ 58421 ≤ (psiAcc 5056).1 ^ 8 := by
  decide +kernel

/-- For `x > 5056`: `5061.793 x - 12820343 ≤ x ψ₁(x)` (sharp on `(5056, 5072]`). -/
theorem psiOne_lower_grid2_mul_5056 {x : ℝ} (hx : 5056 < x) : 5061.793 * x - 12820343 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5056.1 psiOneGrid2_cert_5056.2.1 psiOneGrid2_cert_5056.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5056`: `ψ₁(x) ≥ 5061.793 - 12820343/x` (sharp on `(5056, 5072]`). -/
theorem psiOne_lower_grid2_5056 {x : ℝ} (hx : 5056 < x) : 5061.793 - 12820343 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5056.1 psiOneGrid2_cert_5056.2.1 psiOneGrid2_cert_5056.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5056 {x : ℝ} (hx : 5056 < x) (hx' : x ≤ 5072) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5056 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5072 :
    18539520 ≤ (psiAcc 5072).2.2 ∧ 2 ^ 29689 ≤ (psiAcc 5072).2.1 ^ 8 ∧ 2 ^ 58520 ≤ (psiAcc 5072).1 ^ 8 := by
  decide +kernel

/-- For `x > 5072`: `5070.371 x - 12863737 ≤ x ψ₁(x)` (sharp on `(5072, 5088]`). -/
theorem psiOne_lower_grid2_mul_5072 {x : ℝ} (hx : 5072 < x) : 5070.371 * x - 12863737 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5072.1 psiOneGrid2_cert_5072.2.1 psiOneGrid2_cert_5072.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5072`: `ψ₁(x) ≥ 5070.371 - 12863737/x` (sharp on `(5072, 5088]`). -/
theorem psiOne_lower_grid2_5072 {x : ℝ} (hx : 5072 < x) : 5070.371 - 12863737 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5072.1 psiOneGrid2_cert_5072.2.1 psiOneGrid2_cert_5072.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5072 {x : ℝ} (hx : 5072 < x) (hx' : x ≤ 5088) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5072 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5088 :
    18652672 ≤ (psiAcc 5088).2.2 ∧ 2 ^ 62670 ≤ (psiAcc 5088).2.1 ^ 8 ∧ 2 ^ 58815 ≤ (psiAcc 5088).1 ^ 8 := by
  decide +kernel

/-- For `x > 5088`: `5095.931 x - 12993623 ≤ x ψ₁(x)` (sharp on `(5088, 5104]`). -/
theorem psiOne_lower_grid2_mul_5088 {x : ℝ} (hx : 5088 < x) : 5095.931 * x - 12993623 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5088.1 psiOneGrid2_cert_5088.2.1 psiOneGrid2_cert_5088.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5088`: `ψ₁(x) ≥ 5095.931 - 12993623/x` (sharp on `(5088, 5104]`). -/
theorem psiOne_lower_grid2_5088 {x : ℝ} (hx : 5088 < x) : 5095.931 - 12993623 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5088.1 psiOneGrid2_cert_5088.2.1 psiOneGrid2_cert_5088.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5088 {x : ℝ} (hx : 5088 < x) (hx' : x ≤ 5104) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5088 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5104 :
    18774528 ≤ (psiAcc 5104).2.2 ∧ 2 ^ 29663 ≤ (psiAcc 5104).2.1 ^ 8 ∧ 2 ^ 59012 ≤ (psiAcc 5104).1 ^ 8 := by
  decide +kernel

/-- For `x > 5104`: `5113.000 x - 13080672 ≤ x ψ₁(x)` (sharp on `(5104, 5120]`). -/
theorem psiOne_lower_grid2_mul_5104 {x : ℝ} (hx : 5104 < x) : 5113.000 * x - 13080672 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5104.1 psiOneGrid2_cert_5104.2.1 psiOneGrid2_cert_5104.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5104`: `ψ₁(x) ≥ 5113.000 - 13080672/x` (sharp on `(5104, 5120]`). -/
theorem psiOne_lower_grid2_5104 {x : ℝ} (hx : 5104 < x) : 5113.000 - 13080672 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5104.1 psiOneGrid2_cert_5104.2.1 psiOneGrid2_cert_5104.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5104 {x : ℝ} (hx : 5104 < x) (hx' : x ≤ 5120) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5104 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5120 :
    18887680 ≤ (psiAcc 5120).2.2 ∧ 2 ^ 70723 ≤ (psiAcc 5120).2.1 ^ 8 ∧ 2 ^ 59308 ≤ (psiAcc 5120).1 ^ 8 := by
  decide +kernel

/-- For `x > 5120`: `5138.646 x - 13211801 ≤ x ψ₁(x)` (sharp on `(5120, 5136]`). -/
theorem psiOne_lower_grid2_mul_5120 {x : ℝ} (hx : 5120 < x) : 5138.646 * x - 13211801 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5120.1 psiOneGrid2_cert_5120.2.1 psiOneGrid2_cert_5120.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5120`: `ψ₁(x) ≥ 5138.646 - 13211801/x` (sharp on `(5120, 5136]`). -/
theorem psiOne_lower_grid2_5120 {x : ℝ} (hx : 5120 < x) : 5138.646 - 13211801 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5120.1 psiOneGrid2_cert_5120.2.1 psiOneGrid2_cert_5120.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5120 {x : ℝ} (hx : 5120 < x) (hx' : x ≤ 5136) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5120 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5136 :
    19009536 ≤ (psiAcc 5136).2.2 ∧ 2 ^ 44812 ≤ (psiAcc 5136).2.1 ^ 8 ∧ 2 ^ 59308 ≤ (psiAcc 5136).1 ^ 8 := by
  decide +kernel

/-- For `x > 5136`: `5138.646 x - 13211801 ≤ x ψ₁(x)` (sharp on `(5136, 5152]`). -/
theorem psiOne_lower_grid2_mul_5136 {x : ℝ} (hx : 5136 < x) : 5138.646 * x - 13211801 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5136.1 psiOneGrid2_cert_5136.2.1 psiOneGrid2_cert_5136.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5136`: `ψ₁(x) ≥ 5138.646 - 13211801/x` (sharp on `(5136, 5152]`). -/
theorem psiOne_lower_grid2_5136 {x : ℝ} (hx : 5136 < x) : 5138.646 - 13211801 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5136.1 psiOneGrid2_cert_5136.2.1 psiOneGrid2_cert_5136.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5136 {x : ℝ} (hx : 5136 < x) (hx' : x ≤ 5152) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5136 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5152 :
    19131392 ≤ (psiAcc 5152).2.2 ∧ 2 ^ 19394 ≤ (psiAcc 5152).2.1 ^ 8 ∧ 2 ^ 59407 ≤ (psiAcc 5152).1 ^ 8 := by
  decide +kernel

/-- For `x > 5152`: `5147.224 x - 13255949 ≤ x ψ₁(x)` (sharp on `(5152, 5168]`). -/
theorem psiOne_lower_grid2_mul_5152 {x : ℝ} (hx : 5152 < x) : 5147.224 * x - 13255949 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5152.1 psiOneGrid2_cert_5152.2.1 psiOneGrid2_cert_5152.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5152`: `ψ₁(x) ≥ 5147.224 - 13255949/x` (sharp on `(5152, 5168]`). -/
theorem psiOne_lower_grid2_5152 {x : ℝ} (hx : 5152 < x) : 5147.224 - 13255949 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5152.1 psiOneGrid2_cert_5152.2.1 psiOneGrid2_cert_5152.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5152 {x : ℝ} (hx : 5152 < x) (hx' : x ≤ 5168) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5152 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5168 :
    19244544 ≤ (psiAcc 5168).2.2 ∧ 2 ^ 66272 ≤ (psiAcc 5168).2.1 ^ 8 ∧ 2 ^ 59604 ≤ (psiAcc 5168).1 ^ 8 := by
  decide +kernel

/-- For `x > 5168`: `5164.293 x - 13344024 ≤ x ψ₁(x)` (sharp on `(5168, 5184]`). -/
theorem psiOne_lower_grid2_mul_5168 {x : ℝ} (hx : 5168 < x) : 5164.293 * x - 13344024 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5168.1 psiOneGrid2_cert_5168.2.1 psiOneGrid2_cert_5168.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5168`: `ψ₁(x) ≥ 5164.293 - 13344024/x` (sharp on `(5168, 5184]`). -/
theorem psiOne_lower_grid2_5168 {x : ℝ} (hx : 5168 < x) : 5164.293 - 13344024 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5168.1 psiOneGrid2_cert_5168.2.1 psiOneGrid2_cert_5168.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5168 {x : ℝ} (hx : 5168 < x) (hx' : x ≤ 5184) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5168 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5184 :
    19366400 ≤ (psiAcc 5184).2.2 ∧ 2 ^ 46873 ≤ (psiAcc 5184).2.1 ^ 8 ∧ 2 ^ 59801 ≤ (psiAcc 5184).1 ^ 8 := by
  decide +kernel

/-- For `x > 5184`: `5181.361 x - 13432353 ≤ x ψ₁(x)` (sharp on `(5184, 5200]`). -/
theorem psiOne_lower_grid2_mul_5184 {x : ℝ} (hx : 5184 < x) : 5181.361 * x - 13432353 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5184.1 psiOneGrid2_cert_5184.2.1 psiOneGrid2_cert_5184.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5184`: `ψ₁(x) ≥ 5181.361 - 13432353/x` (sharp on `(5184, 5200]`). -/
theorem psiOne_lower_grid2_5184 {x : ℝ} (hx : 5184 < x) : 5181.361 - 13432353 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5184.1 psiOneGrid2_cert_5184.2.1 psiOneGrid2_cert_5184.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5184 {x : ℝ} (hx : 5184 < x) (hx' : x ≤ 5200) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5184 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5200 :
    19488256 ≤ (psiAcc 5200).2.2 ∧ 2 ^ 30238 ≤ (psiAcc 5200).2.1 ^ 8 ∧ 2 ^ 59999 ≤ (psiAcc 5200).1 ^ 8 := by
  decide +kernel

/-- For `x > 5200`: `5198.517 x - 13521440 ≤ x ψ₁(x)` (sharp on `(5200, 5216]`). -/
theorem psiOne_lower_grid2_mul_5200 {x : ℝ} (hx : 5200 < x) : 5198.517 * x - 13521440 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5200.1 psiOneGrid2_cert_5200.2.1 psiOneGrid2_cert_5200.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5200`: `ψ₁(x) ≥ 5198.517 - 13521440/x` (sharp on `(5200, 5216]`). -/
theorem psiOne_lower_grid2_5200 {x : ℝ} (hx : 5200 < x) : 5198.517 - 13521440 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5200.1 psiOneGrid2_cert_5200.2.1 psiOneGrid2_cert_5200.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5200 {x : ℝ} (hx : 5200 < x) (hx' : x ≤ 5216) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5200 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5216 :
    19610112 ≤ (psiAcc 5216).2.2 ∧ 2 ^ 16072 ≤ (psiAcc 5216).2.1 ^ 8 ∧ 2 ^ 60098 ≤ (psiAcc 5216).1 ^ 8 := by
  decide +kernel

/-- For `x > 5216`: `5207.094 x - 13566121 ≤ x ψ₁(x)` (sharp on `(5216, 5232]`). -/
theorem psiOne_lower_grid2_mul_5216 {x : ℝ} (hx : 5216 < x) : 5207.094 * x - 13566121 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5216.1 psiOneGrid2_cert_5216.2.1 psiOneGrid2_cert_5216.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5216`: `ψ₁(x) ≥ 5207.094 - 13566121/x` (sharp on `(5216, 5232]`). -/
theorem psiOne_lower_grid2_5216 {x : ℝ} (hx : 5216 < x) : 5207.094 - 13566121 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5216.1 psiOneGrid2_cert_5216.2.1 psiOneGrid2_cert_5216.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5216 {x : ℝ} (hx : 5216 < x) (hx' : x ≤ 5232) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5216 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5232 :
    19723264 ≤ (psiAcc 5232).2.2 ∧ 2 ^ 73020 ≤ (psiAcc 5232).2.1 ^ 8 ∧ 2 ^ 60295 ≤ (psiAcc 5232).1 ^ 8 := by
  decide +kernel

/-- For `x > 5232`: `5224.163 x - 13655373 ≤ x ψ₁(x)` (sharp on `(5232, 5248]`). -/
theorem psiOne_lower_grid2_mul_5232 {x : ℝ} (hx : 5232 < x) : 5224.163 * x - 13655373 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5232.1 psiOneGrid2_cert_5232.2.1 psiOneGrid2_cert_5232.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5232`: `ψ₁(x) ≥ 5224.163 - 13655373/x` (sharp on `(5232, 5248]`). -/
theorem psiOne_lower_grid2_5232 {x : ℝ} (hx : 5232 < x) : 5224.163 - 13655373 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5232.1 psiOneGrid2_cert_5232.2.1 psiOneGrid2_cert_5232.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5232 {x : ℝ} (hx : 5232 < x) (hx' : x ≤ 5248) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5232 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5248 :
    19845120 ≤ (psiAcc 5248).2.2 ∧ 2 ^ 65475 ≤ (psiAcc 5248).2.1 ^ 8 ∧ 2 ^ 60493 ≤ (psiAcc 5248).1 ^ 8 := by
  decide +kernel

/-- For `x > 5248`: `5241.319 x - 13745181 ≤ x ψ₁(x)` (sharp on `(5248, 5264]`). -/
theorem psiOne_lower_grid2_mul_5248 {x : ℝ} (hx : 5248 < x) : 5241.319 * x - 13745181 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5248.1 psiOneGrid2_cert_5248.2.1 psiOneGrid2_cert_5248.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5248`: `ψ₁(x) ≥ 5241.319 - 13745181/x` (sharp on `(5248, 5264]`). -/
theorem psiOne_lower_grid2_5248 {x : ℝ} (hx : 5248 < x) : 5241.319 - 13745181 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5248.1 psiOneGrid2_cert_5248.2.1 psiOneGrid2_cert_5248.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5248 {x : ℝ} (hx : 5248 < x) (hx' : x ≤ 5264) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5248 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5264 :
    19966976 ≤ (psiAcc 5264).2.2 ∧ 2 ^ 58819 ≤ (psiAcc 5264).2.1 ^ 8 ∧ 2 ^ 60592 ≤ (psiAcc 5264).1 ^ 8 := by
  decide +kernel

/-- For `x > 5264`: `5249.896 x - 13790308 ≤ x ψ₁(x)` (sharp on `(5264, 5280]`). -/
theorem psiOne_lower_grid2_mul_5264 {x : ℝ} (hx : 5264 < x) : 5249.896 * x - 13790308 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5264.1 psiOneGrid2_cert_5264.2.1 psiOneGrid2_cert_5264.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5264`: `ψ₁(x) ≥ 5249.896 - 13790308/x` (sharp on `(5264, 5280]`). -/
theorem psiOne_lower_grid2_5264 {x : ℝ} (hx : 5264 < x) : 5249.896 - 13790308 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5264.1 psiOneGrid2_cert_5264.2.1 psiOneGrid2_cert_5264.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5264 {x : ℝ} (hx : 5264 < x) (hx' : x ≤ 5280) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5264 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5280 :
    20088832 ≤ (psiAcc 5280).2.2 ∧ 2 ^ 54240 ≤ (psiAcc 5280).2.1 ^ 8 ∧ 2 ^ 60790 ≤ (psiAcc 5280).1 ^ 8 := by
  decide +kernel

/-- For `x > 5280`: `5267.052 x - 13880819 ≤ x ψ₁(x)` (sharp on `(5280, 5296]`). -/
theorem psiOne_lower_grid2_mul_5280 {x : ℝ} (hx : 5280 < x) : 5267.052 * x - 13880819 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5280.1 psiOneGrid2_cert_5280.2.1 psiOneGrid2_cert_5280.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5280`: `ψ₁(x) ≥ 5267.052 - 13880819/x` (sharp on `(5280, 5296]`). -/
theorem psiOne_lower_grid2_5280 {x : ℝ} (hx : 5280 < x) : 5267.052 - 13880819 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5280.1 psiOneGrid2_cert_5280.2.1 psiOneGrid2_cert_5280.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5280 {x : ℝ} (hx : 5280 < x) (hx' : x ≤ 5296) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5280 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5296 :
    20210688 ≤ (psiAcc 5296).2.2 ∧ 2 ^ 53520 ≤ (psiAcc 5296).2.1 ^ 8 ∧ 2 ^ 60889 ≤ (psiAcc 5296).1 ^ 8 := by
  decide +kernel

/-- For `x > 5296`: `5275.629 x - 13926118 ≤ x ψ₁(x)` (sharp on `(5296, 5312]`). -/
theorem psiOne_lower_grid2_mul_5296 {x : ℝ} (hx : 5296 < x) : 5275.629 * x - 13926118 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5296.1 psiOneGrid2_cert_5296.2.1 psiOneGrid2_cert_5296.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5296`: `ψ₁(x) ≥ 5275.629 - 13926118/x` (sharp on `(5296, 5312]`). -/
theorem psiOne_lower_grid2_5296 {x : ℝ} (hx : 5296 < x) : 5275.629 - 13926118 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5296.1 psiOneGrid2_cert_5296.2.1 psiOneGrid2_cert_5296.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5296 {x : ℝ} (hx : 5296 < x) (hx' : x ≤ 5312) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5296 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5312 :
    20332544 ≤ (psiAcc 5312).2.2 ∧ 2 ^ 55571 ≤ (psiAcc 5312).2.1 ^ 8 ∧ 2 ^ 61186 ≤ (psiAcc 5312).1 ^ 8 := by
  decide +kernel

/-- For `x > 5312`: `5301.362 x - 14062580 ≤ x ψ₁(x)` (sharp on `(5312, 5328]`). -/
theorem psiOne_lower_grid2_mul_5312 {x : ℝ} (hx : 5312 < x) : 5301.362 * x - 14062580 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5312.1 psiOneGrid2_cert_5312.2.1 psiOneGrid2_cert_5312.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5312`: `ψ₁(x) ≥ 5301.362 - 14062580/x` (sharp on `(5312, 5328]`). -/
theorem psiOne_lower_grid2_5312 {x : ℝ} (hx : 5312 < x) : 5301.362 - 14062580 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5312.1 psiOneGrid2_cert_5312.2.1 psiOneGrid2_cert_5312.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5312 {x : ℝ} (hx : 5312 < x) (hx' : x ≤ 5328) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5312 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5328 :
    20454400 ≤ (psiAcc 5328).2.2 ∧ 2 ^ 60195 ≤ (psiAcc 5328).2.1 ^ 8 ∧ 2 ^ 61285 ≤ (psiAcc 5328).1 ^ 8 := by
  decide +kernel

/-- For `x > 5328`: `5309.940 x - 14108239 ≤ x ψ₁(x)` (sharp on `(5328, 5344]`). -/
theorem psiOne_lower_grid2_mul_5328 {x : ℝ} (hx : 5328 < x) : 5309.940 * x - 14108239 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5328.1 psiOneGrid2_cert_5328.2.1 psiOneGrid2_cert_5328.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5328`: `ψ₁(x) ≥ 5309.940 - 14108239/x` (sharp on `(5328, 5344]`). -/
theorem psiOne_lower_grid2_5328 {x : ℝ} (hx : 5328 < x) : 5309.940 - 14108239 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5328.1 psiOneGrid2_cert_5328.2.1 psiOneGrid2_cert_5328.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5328 {x : ℝ} (hx : 5328 < x) (hx' : x ≤ 5344) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5328 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5344 :
    20576256 ≤ (psiAcc 5344).2.2 ∧ 2 ^ 67741 ≤ (psiAcc 5344).2.1 ^ 8 ∧ 2 ^ 61433 ≤ (psiAcc 5344).1 ^ 8 := by
  decide +kernel

/-- For `x > 5344`: `5322.763 x - 14176607 ≤ x ψ₁(x)` (sharp on `(5344, 5360]`). -/
theorem psiOne_lower_grid2_mul_5344 {x : ℝ} (hx : 5344 < x) : 5322.763 * x - 14176607 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5344.1 psiOneGrid2_cert_5344.2.1 psiOneGrid2_cert_5344.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5344`: `ψ₁(x) ≥ 5322.763 - 14176607/x` (sharp on `(5344, 5360]`). -/
theorem psiOne_lower_grid2_5344 {x : ℝ} (hx : 5344 < x) : 5322.763 - 14176607 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5344.1 psiOneGrid2_cert_5344.2.1 psiOneGrid2_cert_5344.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5344 {x : ℝ} (hx : 5344 < x) (hx' : x ≤ 5360) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5344 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5360 :
    20706816 ≤ (psiAcc 5360).2.2 ∧ 2 ^ 8380 ≤ (psiAcc 5360).2.1 ^ 8 ∧ 2 ^ 61631 ≤ (psiAcc 5360).1 ^ 8 := by
  decide +kernel

/-- For `x > 5360`: `5339.919 x - 14268370 ≤ x ψ₁(x)` (sharp on `(5360, 5376]`). -/
theorem psiOne_lower_grid2_mul_5360 {x : ℝ} (hx : 5360 < x) : 5339.919 * x - 14268370 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5360.1 psiOneGrid2_cert_5360.2.1 psiOneGrid2_cert_5360.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5360`: `ψ₁(x) ≥ 5339.919 - 14268370/x` (sharp on `(5360, 5376]`). -/
theorem psiOne_lower_grid2_5360 {x : ℝ} (hx : 5360 < x) : 5339.919 - 14268370 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5360.1 psiOneGrid2_cert_5360.2.1 psiOneGrid2_cert_5360.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5360 {x : ℝ} (hx : 5360 < x) (hx' : x ≤ 5376) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5360 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5376 :
    20828672 ≤ (psiAcc 5376).2.2 ∧ 2 ^ 19641 ≤ (psiAcc 5376).2.1 ^ 8 ∧ 2 ^ 61631 ≤ (psiAcc 5376).1 ^ 8 := by
  decide +kernel

/-- For `x > 5376`: `5339.919 x - 14268369 ≤ x ψ₁(x)` (sharp on `(5376, 5392]`). -/
theorem psiOne_lower_grid2_mul_5376 {x : ℝ} (hx : 5376 < x) : 5339.919 * x - 14268369 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5376.1 psiOneGrid2_cert_5376.2.1 psiOneGrid2_cert_5376.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5376`: `ψ₁(x) ≥ 5339.919 - 14268369/x` (sharp on `(5376, 5392]`). -/
theorem psiOne_lower_grid2_5376 {x : ℝ} (hx : 5376 < x) : 5339.919 - 14268369 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5376.1 psiOneGrid2_cert_5376.2.1 psiOneGrid2_cert_5376.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5376 {x : ℝ} (hx : 5376 < x) (hx' : x ≤ 5392) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5376 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5392 :
    20950528 ≤ (psiAcc 5392).2.2 ∧ 2 ^ 32489 ≤ (psiAcc 5392).2.1 ^ 8 ∧ 2 ^ 61830 ≤ (psiAcc 5392).1 ^ 8 := by
  decide +kernel

/-- For `x > 5392`: `5357.161 x - 14361200 ≤ x ψ₁(x)` (sharp on `(5392, 5408]`). -/
theorem psiOne_lower_grid2_mul_5392 {x : ℝ} (hx : 5392 < x) : 5357.161 * x - 14361200 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5392.1 psiOneGrid2_cert_5392.2.1 psiOneGrid2_cert_5392.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5392`: `ψ₁(x) ≥ 5357.161 - 14361200/x` (sharp on `(5392, 5408]`). -/
theorem psiOne_lower_grid2_5392 {x : ℝ} (hx : 5392 < x) : 5357.161 - 14361200 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5392.1 psiOneGrid2_cert_5392.2.1 psiOneGrid2_cert_5392.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5392 {x : ℝ} (hx : 5392 < x) (hx' : x ≤ 5408) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5392 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5408 :
    21072384 ≤ (psiAcc 5408).2.2 ∧ 2 ^ 49403 ≤ (psiAcc 5408).2.1 ^ 8 ∧ 2 ^ 62127 ≤ (psiAcc 5408).1 ^ 8 := by
  decide +kernel

/-- For `x > 5408`: `5382.894 x - 14500149 ≤ x ψ₁(x)` (sharp on `(5408, 5424]`). -/
theorem psiOne_lower_grid2_mul_5408 {x : ℝ} (hx : 5408 < x) : 5382.894 * x - 14500149 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5408.1 psiOneGrid2_cert_5408.2.1 psiOneGrid2_cert_5408.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5408`: `ψ₁(x) ≥ 5382.894 - 14500149/x` (sharp on `(5408, 5424]`). -/
theorem psiOne_lower_grid2_5408 {x : ℝ} (hx : 5408 < x) : 5382.894 - 14500149 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5408.1 psiOneGrid2_cert_5408.2.1 psiOneGrid2_cert_5408.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5408 {x : ℝ} (hx : 5408 < x) (hx' : x ≤ 5424) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5408 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5424 :
    21194240 ≤ (psiAcc 5424).2.2 ∧ 2 ^ 70881 ≤ (psiAcc 5424).2.1 ^ 8 ∧ 2 ^ 62425 ≤ (psiAcc 5424).1 ^ 8 := by
  decide +kernel

/-- For `x > 5424`: `5408.714 x - 14639997 ≤ x ψ₁(x)` (sharp on `(5424, 5440]`). -/
theorem psiOne_lower_grid2_mul_5424 {x : ℝ} (hx : 5424 < x) : 5408.714 * x - 14639997 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5424.1 psiOneGrid2_cert_5424.2.1 psiOneGrid2_cert_5424.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5424`: `ψ₁(x) ≥ 5408.714 - 14639997/x` (sharp on `(5424, 5440]`). -/
theorem psiOne_lower_grid2_5424 {x : ℝ} (hx : 5424 < x) : 5408.714 - 14639997 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5424.1 psiOneGrid2_cert_5424.2.1 psiOneGrid2_cert_5424.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5424 {x : ℝ} (hx : 5424 < x) (hx' : x ≤ 5440) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5424 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5440 :
    21324800 ≤ (psiAcc 5440).2.2 ∧ 2 ^ 26398 ≤ (psiAcc 5440).2.1 ^ 8 ∧ 2 ^ 62623 ≤ (psiAcc 5440).1 ^ 8 := by
  decide +kernel

/-- For `x > 5440`: `5425.869 x - 14733218 ≤ x ψ₁(x)` (sharp on `(5440, 5456]`). -/
theorem psiOne_lower_grid2_mul_5440 {x : ℝ} (hx : 5440 < x) : 5425.869 * x - 14733218 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5440.1 psiOneGrid2_cert_5440.2.1 psiOneGrid2_cert_5440.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5440`: `ψ₁(x) ≥ 5425.869 - 14733218/x` (sharp on `(5440, 5456]`). -/
theorem psiOne_lower_grid2_5440 {x : ℝ} (hx : 5440 < x) : 5425.869 - 14733218 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5440.1 psiOneGrid2_cert_5440.2.1 psiOneGrid2_cert_5440.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5440 {x : ℝ} (hx : 5440 < x) (hx' : x ≤ 5456) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5440 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5456 :
    21446656 ≤ (psiAcc 5456).2.2 ∧ 2 ^ 57008 ≤ (psiAcc 5456).2.1 ^ 8 ∧ 2 ^ 62921 ≤ (psiAcc 5456).1 ^ 8 := by
  decide +kernel

/-- For `x > 5456`: `5451.689 x - 14873788 ≤ x ψ₁(x)` (sharp on `(5456, 5472]`). -/
theorem psiOne_lower_grid2_mul_5456 {x : ℝ} (hx : 5456 < x) : 5451.689 * x - 14873788 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5456.1 psiOneGrid2_cert_5456.2.1 psiOneGrid2_cert_5456.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5456`: `ψ₁(x) ≥ 5451.689 - 14873788/x` (sharp on `(5456, 5472]`). -/
theorem psiOne_lower_grid2_5456 {x : ℝ} (hx : 5456 < x) : 5451.689 - 14873788 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5456.1 psiOneGrid2_cert_5456.2.1 psiOneGrid2_cert_5456.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5456 {x : ℝ} (hx : 5456 < x) (hx' : x ≤ 5472) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5456 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5472 :
    21577216 ≤ (psiAcc 5472).2.2 ∧ 2 ^ 19376 ≤ (psiAcc 5472).2.1 ^ 8 ∧ 2 ^ 63021 ≤ (psiAcc 5472).1 ^ 8 := by
  decide +kernel

/-- For `x > 5472`: `5460.353 x - 14921190 ≤ x ψ₁(x)` (sharp on `(5472, 5488]`). -/
theorem psiOne_lower_grid2_mul_5472 {x : ℝ} (hx : 5472 < x) : 5460.353 * x - 14921190 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5472.1 psiOneGrid2_cert_5472.2.1 psiOneGrid2_cert_5472.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5472`: `ψ₁(x) ≥ 5460.353 - 14921190/x` (sharp on `(5472, 5488]`). -/
theorem psiOne_lower_grid2_5472 {x : ℝ} (hx : 5472 < x) : 5460.353 - 14921190 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5472.1 psiOneGrid2_cert_5472.2.1 psiOneGrid2_cert_5472.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5472 {x : ℝ} (hx : 5472 < x) (hx' : x ≤ 5488) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5472 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5488 :
    21699072 ≤ (psiAcc 5488).2.2 ∧ 2 ^ 55349 ≤ (psiAcc 5488).2.1 ^ 8 ∧ 2 ^ 63319 ≤ (psiAcc 5488).1 ^ 8 := by
  decide +kernel

/-- For `x > 5488`: `5486.173 x - 15062673 ≤ x ψ₁(x)` (sharp on `(5488, 5504]`). -/
theorem psiOne_lower_grid2_mul_5488 {x : ℝ} (hx : 5488 < x) : 5486.173 * x - 15062673 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5488.1 psiOneGrid2_cert_5488.2.1 psiOneGrid2_cert_5488.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5488`: `ψ₁(x) ≥ 5486.173 - 15062673/x` (sharp on `(5488, 5504]`). -/
theorem psiOne_lower_grid2_5488 {x : ℝ} (hx : 5488 < x) : 5486.173 - 15062673 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5488.1 psiOneGrid2_cert_5488.2.1 psiOneGrid2_cert_5488.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5488 {x : ℝ} (hx : 5488 < x) (hx' : x ≤ 5504) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5488 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5504 :
    21829632 ≤ (psiAcc 5504).2.2 ∧ 2 ^ 24374 ≤ (psiAcc 5504).2.1 ^ 8 ∧ 2 ^ 63518 ≤ (psiAcc 5504).1 ^ 8 := by
  decide +kernel

/-- For `x > 5504`: `5503.415 x - 15157539 ≤ x ψ₁(x)` (sharp on `(5504, 5520]`). -/
theorem psiOne_lower_grid2_mul_5504 {x : ℝ} (hx : 5504 < x) : 5503.415 * x - 15157539 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5504.1 psiOneGrid2_cert_5504.2.1 psiOneGrid2_cert_5504.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5504`: `ψ₁(x) ≥ 5503.415 - 15157539/x` (sharp on `(5504, 5520]`). -/
theorem psiOne_lower_grid2_5504 {x : ℝ} (hx : 5504 < x) : 5503.415 - 15157539 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5504.1 psiOneGrid2_cert_5504.2.1 psiOneGrid2_cert_5504.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5504 {x : ℝ} (hx : 5504 < x) (hx' : x ≤ 5520) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5504 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5520 :
    21951488 ≤ (psiAcc 5520).2.2 ∧ 2 ^ 67206 ≤ (psiAcc 5520).2.1 ^ 8 ∧ 2 ^ 63716 ≤ (psiAcc 5520).1 ^ 8 := by
  decide +kernel

/-- For `x > 5520`: `5520.570 x - 15252116 ≤ x ψ₁(x)` (sharp on `(5520, 5536]`). -/
theorem psiOne_lower_grid2_mul_5520 {x : ℝ} (hx : 5520 < x) : 5520.570 * x - 15252116 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5520.1 psiOneGrid2_cert_5520.2.1 psiOneGrid2_cert_5520.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5520`: `ψ₁(x) ≥ 5520.570 - 15252116/x` (sharp on `(5520, 5536]`). -/
theorem psiOne_lower_grid2_5520 {x : ℝ} (hx : 5520 < x) : 5520.570 - 15252116 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5520.1 psiOneGrid2_cert_5520.2.1 psiOneGrid2_cert_5520.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5520 {x : ℝ} (hx : 5520 < x) (hx' : x ≤ 5536) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5520 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5536 :
    22082048 ≤ (psiAcc 5536).2.2 ∧ 2 ^ 45080 ≤ (psiAcc 5536).2.1 ^ 8 ∧ 2 ^ 64015 ≤ (psiAcc 5536).1 ^ 8 := by
  decide +kernel

/-- For `x > 5536`: `5546.477 x - 15395282 ≤ x ψ₁(x)` (sharp on `(5536, 5552]`). -/
theorem psiOne_lower_grid2_mul_5536 {x : ℝ} (hx : 5536 < x) : 5546.477 * x - 15395282 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5536.1 psiOneGrid2_cert_5536.2.1 psiOneGrid2_cert_5536.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5536`: `ψ₁(x) ≥ 5546.477 - 15395282/x` (sharp on `(5536, 5552]`). -/
theorem psiOne_lower_grid2_5536 {x : ℝ} (hx : 5536 < x) : 5546.477 - 15395282 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5536.1 psiOneGrid2_cert_5536.2.1 psiOneGrid2_cert_5536.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5536 {x : ℝ} (hx : 5536 < x) (hx' : x ≤ 5552) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5536 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5552 :
    22212608 ≤ (psiAcc 5552).2.2 ∧ 2 ^ 24843 ≤ (psiAcc 5552).2.1 ^ 8 ∧ 2 ^ 64015 ≤ (psiAcc 5552).1 ^ 8 := by
  decide +kernel

/-- For `x > 5552`: `5546.477 x - 15395282 ≤ x ψ₁(x)` (sharp on `(5552, 5568]`). -/
theorem psiOne_lower_grid2_mul_5552 {x : ℝ} (hx : 5552 < x) : 5546.477 * x - 15395282 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5552.1 psiOneGrid2_cert_5552.2.1 psiOneGrid2_cert_5552.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5552`: `ψ₁(x) ≥ 5546.477 - 15395282/x` (sharp on `(5552, 5568]`). -/
theorem psiOne_lower_grid2_5552 {x : ℝ} (hx : 5552 < x) : 5546.477 - 15395282 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5552.1 psiOneGrid2_cert_5552.2.1 psiOneGrid2_cert_5552.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5552 {x : ℝ} (hx : 5552 < x) (hx' : x ≤ 5568) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5552 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5568 :
    22343168 ≤ (psiAcc 5568).2.2 ∧ 2 ^ 6199 ≤ (psiAcc 5568).2.1 ^ 8 ∧ 2 ^ 64214 ≤ (psiAcc 5568).1 ^ 8 := by
  decide +kernel

/-- For `x > 5568`: `5563.719 x - 15491148 ≤ x ψ₁(x)` (sharp on `(5568, 5584]`). -/
theorem psiOne_lower_grid2_mul_5568 {x : ℝ} (hx : 5568 < x) : 5563.719 * x - 15491148 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5568.1 psiOneGrid2_cert_5568.2.1 psiOneGrid2_cert_5568.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5568`: `ψ₁(x) ≥ 5563.719 - 15491148/x` (sharp on `(5568, 5584]`). -/
theorem psiOne_lower_grid2_5568 {x : ℝ} (hx : 5568 < x) : 5563.719 - 15491148 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5568.1 psiOneGrid2_cert_5568.2.1 psiOneGrid2_cert_5568.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5568 {x : ℝ} (hx : 5568 < x) (hx' : x ≤ 5584) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5568 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5584 :
    22465024 ≤ (psiAcc 5584).2.2 ∧ 2 ^ 61667 ≤ (psiAcc 5584).2.1 ^ 8 ∧ 2 ^ 64512 ≤ (psiAcc 5584).1 ^ 8 := by
  decide +kernel

/-- For `x > 5584`: `5589.538 x - 15635074 ≤ x ψ₁(x)` (sharp on `(5584, 5600]`). -/
theorem psiOne_lower_grid2_mul_5584 {x : ℝ} (hx : 5584 < x) : 5589.538 * x - 15635074 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5584.1 psiOneGrid2_cert_5584.2.1 psiOneGrid2_cert_5584.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5584`: `ψ₁(x) ≥ 5589.538 - 15635074/x` (sharp on `(5584, 5600]`). -/
theorem psiOne_lower_grid2_5584 {x : ℝ} (hx : 5584 < x) : 5589.538 - 15635074 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5584.1 psiOneGrid2_cert_5584.2.1 psiOneGrid2_cert_5584.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5584 {x : ℝ} (hx : 5584 < x) (hx' : x ≤ 5600) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5584 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5600 :
    22595584 ≤ (psiAcc 5600).2.2 ∧ 2 ^ 50291 ≤ (psiAcc 5600).2.1 ^ 8 ∧ 2 ^ 64612 ≤ (psiAcc 5600).1 ^ 8 := by
  decide +kernel

/-- For `x > 5600`: `5598.203 x - 15683516 ≤ x ψ₁(x)` (sharp on `(5600, 5616]`). -/
theorem psiOne_lower_grid2_mul_5600 {x : ℝ} (hx : 5600 < x) : 5598.203 * x - 15683516 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5600.1 psiOneGrid2_cert_5600.2.1 psiOneGrid2_cert_5600.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5600`: `ψ₁(x) ≥ 5598.203 - 15683516/x` (sharp on `(5600, 5616]`). -/
theorem psiOne_lower_grid2_5600 {x : ℝ} (hx : 5600 < x) : 5598.203 - 15683516 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5600.1 psiOneGrid2_cert_5600.2.1 psiOneGrid2_cert_5600.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5600 {x : ℝ} (hx : 5600 < x) (hx' : x ≤ 5616) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5600 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5616 :
    22726144 ≤ (psiAcc 5616).2.2 ∧ 2 ^ 39611 ≤ (psiAcc 5616).2.1 ^ 8 ∧ 2 ^ 64612 ≤ (psiAcc 5616).1 ^ 8 := by
  decide +kernel

/-- For `x > 5616`: `5598.203 x - 15683515 ≤ x ψ₁(x)` (sharp on `(5616, 5632]`). -/
theorem psiOne_lower_grid2_mul_5616 {x : ℝ} (hx : 5616 < x) : 5598.203 * x - 15683515 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5616.1 psiOneGrid2_cert_5616.2.1 psiOneGrid2_cert_5616.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5616`: `ψ₁(x) ≥ 5598.203 - 15683515/x` (sharp on `(5616, 5632]`). -/
theorem psiOne_lower_grid2_5616 {x : ℝ} (hx : 5616 < x) : 5598.203 - 15683515 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5616.1 psiOneGrid2_cert_5616.2.1 psiOneGrid2_cert_5616.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5616 {x : ℝ} (hx : 5616 < x) (hx' : x ≤ 5632) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5616 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5632 :
    22856704 ≤ (psiAcc 5632).2.2 ∧ 2 ^ 29829 ≤ (psiAcc 5632).2.1 ^ 8 ∧ 2 ^ 64712 ≤ (psiAcc 5632).1 ^ 8 := by
  decide +kernel

/-- For `x > 5632`: `5606.867 x - 15732234 ≤ x ψ₁(x)` (sharp on `(5632, 5648]`). -/
theorem psiOne_lower_grid2_mul_5632 {x : ℝ} (hx : 5632 < x) : 5606.867 * x - 15732234 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5632.1 psiOneGrid2_cert_5632.2.1 psiOneGrid2_cert_5632.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5632`: `ψ₁(x) ≥ 5606.867 - 15732234/x` (sharp on `(5632, 5648]`). -/
theorem psiOne_lower_grid2_5632 {x : ℝ} (hx : 5632 < x) : 5606.867 - 15732234 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5632.1 psiOneGrid2_cert_5632.2.1 psiOneGrid2_cert_5632.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5632 {x : ℝ} (hx : 5632 < x) (hx' : x ≤ 5648) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5632 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5648 :
    22987264 ≤ (psiAcc 5648).2.2 ∧ 2 ^ 22439 ≤ (psiAcc 5648).2.1 ^ 8 ∧ 2 ^ 65011 ≤ (psiAcc 5648).1 ^ 8 := by
  decide +kernel

/-- For `x > 5648`: `5632.773 x - 15878406 ≤ x ψ₁(x)` (sharp on `(5648, 5664]`). -/
theorem psiOne_lower_grid2_mul_5648 {x : ℝ} (hx : 5648 < x) : 5632.773 * x - 15878406 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5648.1 psiOneGrid2_cert_5648.2.1 psiOneGrid2_cert_5648.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5648`: `ψ₁(x) ≥ 5632.773 - 15878406/x` (sharp on `(5648, 5664]`). -/
theorem psiOne_lower_grid2_5648 {x : ℝ} (hx : 5648 < x) : 5632.773 - 15878406 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5648.1 psiOneGrid2_cert_5648.2.1 psiOneGrid2_cert_5648.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5648 {x : ℝ} (hx : 5648 < x) (hx' : x ≤ 5664) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5648 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5664 :
    23117824 ≤ (psiAcc 5664).2.2 ∧ 2 ^ 21729 ≤ (psiAcc 5664).2.1 ^ 8 ∧ 2 ^ 65410 ≤ (psiAcc 5664).1 ^ 8 := by
  decide +kernel

/-- For `x > 5664`: `5667.344 x - 16073903 ≤ x ψ₁(x)` (sharp on `(5664, 5680]`). -/
theorem psiOne_lower_grid2_mul_5664 {x : ℝ} (hx : 5664 < x) : 5667.344 * x - 16073903 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5664.1 psiOneGrid2_cert_5664.2.1 psiOneGrid2_cert_5664.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5664`: `ψ₁(x) ≥ 5667.344 - 16073903/x` (sharp on `(5664, 5680]`). -/
theorem psiOne_lower_grid2_5664 {x : ℝ} (hx : 5664 < x) : 5667.344 - 16073903 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5664.1 psiOneGrid2_cert_5664.2.1 psiOneGrid2_cert_5664.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5664 {x : ℝ} (hx : 5664 < x) (hx' : x ≤ 5680) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5664 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5680 :
    23248384 ≤ (psiAcc 5680).2.2 ∧ 2 ^ 24910 ≤ (psiAcc 5680).2.1 ^ 8 ∧ 2 ^ 65509 ≤ (psiAcc 5680).1 ^ 8 := by
  decide +kernel

/-- For `x > 5680`: `5675.922 x - 16122529 ≤ x ψ₁(x)` (sharp on `(5680, 5696]`). -/
theorem psiOne_lower_grid2_mul_5680 {x : ℝ} (hx : 5680 < x) : 5675.922 * x - 16122529 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5680.1 psiOneGrid2_cert_5680.2.1 psiOneGrid2_cert_5680.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5680`: `ψ₁(x) ≥ 5675.922 - 16122529/x` (sharp on `(5680, 5696]`). -/
theorem psiOne_lower_grid2_5680 {x : ℝ} (hx : 5680 < x) : 5675.922 - 16122529 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5680.1 psiOneGrid2_cert_5680.2.1 psiOneGrid2_cert_5680.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5680 {x : ℝ} (hx : 5680 < x) (hx' : x ≤ 5696) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5680 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5696 :
    23378944 ≤ (psiAcc 5696).2.2 ∧ 2 ^ 30884 ≤ (psiAcc 5696).2.1 ^ 8 ∧ 2 ^ 65809 ≤ (psiAcc 5696).1 ^ 8 := by
  decide +kernel

/-- For `x > 5696`: `5701.915 x - 16270385 ≤ x ψ₁(x)` (sharp on `(5696, 5712]`). -/
theorem psiOne_lower_grid2_mul_5696 {x : ℝ} (hx : 5696 < x) : 5701.915 * x - 16270385 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5696.1 psiOneGrid2_cert_5696.2.1 psiOneGrid2_cert_5696.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5696`: `ψ₁(x) ≥ 5701.915 - 16270385/x` (sharp on `(5696, 5712]`). -/
theorem psiOne_lower_grid2_5696 {x : ℝ} (hx : 5696 < x) : 5701.915 - 16270385 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5696.1 psiOneGrid2_cert_5696.2.1 psiOneGrid2_cert_5696.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5696 {x : ℝ} (hx : 5696 < x) (hx' : x ≤ 5712) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5696 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5712 :
    23509504 ≤ (psiAcc 5712).2.2 ∧ 2 ^ 40550 ≤ (psiAcc 5712).2.1 ^ 8 ∧ 2 ^ 66008 ≤ (psiAcc 5712).1 ^ 8 := by
  decide +kernel

/-- For `x > 5712`: `5719.157 x - 16368768 ≤ x ψ₁(x)` (sharp on `(5712, 5728]`). -/
theorem psiOne_lower_grid2_mul_5712 {x : ℝ} (hx : 5712 < x) : 5719.157 * x - 16368768 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5712.1 psiOneGrid2_cert_5712.2.1 psiOneGrid2_cert_5712.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5712`: `ψ₁(x) ≥ 5719.157 - 16368768/x` (sharp on `(5712, 5728]`). -/
theorem psiOne_lower_grid2_5712 {x : ℝ} (hx : 5712 < x) : 5719.157 - 16368768 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5712.1 psiOneGrid2_cert_5712.2.1 psiOneGrid2_cert_5712.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5712 {x : ℝ} (hx : 5712 < x) (hx' : x ≤ 5728) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5712 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5728 :
    23640064 ≤ (psiAcc 5728).2.2 ∧ 2 ^ 53312 ≤ (psiAcc 5728).2.1 ^ 8 ∧ 2 ^ 66108 ≤ (psiAcc 5728).1 ^ 8 := by
  decide +kernel

/-- For `x > 5728`: `5727.821 x - 16418301 ≤ x ψ₁(x)` (sharp on `(5728, 5744]`). -/
theorem psiOne_lower_grid2_mul_5728 {x : ℝ} (hx : 5728 < x) : 5727.821 * x - 16418301 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5728.1 psiOneGrid2_cert_5728.2.1 psiOneGrid2_cert_5728.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5728`: `ψ₁(x) ≥ 5727.821 - 16418301/x` (sharp on `(5728, 5744]`). -/
theorem psiOne_lower_grid2_5728 {x : ℝ} (hx : 5728 < x) : 5727.821 - 16418301 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5728.1 psiOneGrid2_cert_5728.2.1 psiOneGrid2_cert_5728.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5728 {x : ℝ} (hx : 5728 < x) (hx' : x ≤ 5744) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5728 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5744 :
    23770624 ≤ (psiAcc 5744).2.2 ∧ 2 ^ 67672 ≤ (psiAcc 5744).2.1 ^ 8 ∧ 2 ^ 66408 ≤ (psiAcc 5744).1 ^ 8 := by
  decide +kernel

/-- For `x > 5744`: `5753.814 x - 16567508 ≤ x ψ₁(x)` (sharp on `(5744, 5760]`). -/
theorem psiOne_lower_grid2_mul_5744 {x : ℝ} (hx : 5744 < x) : 5753.814 * x - 16567508 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5744.1 psiOneGrid2_cert_5744.2.1 psiOneGrid2_cert_5744.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5744`: `ψ₁(x) ≥ 5753.814 - 16567508/x` (sharp on `(5744, 5760]`). -/
theorem psiOne_lower_grid2_5744 {x : ℝ} (hx : 5744 < x) : 5753.814 - 16567508 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5744.1 psiOneGrid2_cert_5744.2.1 psiOneGrid2_cert_5744.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5744 {x : ℝ} (hx : 5744 < x) (hx' : x ≤ 5760) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5744 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5760 :
    23909888 ≤ (psiAcc 5760).2.2 ∧ 2 ^ 17195 ≤ (psiAcc 5760).2.1 ^ 8 ∧ 2 ^ 66508 ≤ (psiAcc 5760).1 ^ 8 := by
  decide +kernel

/-- For `x > 5760`: `5762.479 x - 16617319 ≤ x ψ₁(x)` (sharp on `(5760, 5776]`). -/
theorem psiOne_lower_grid2_mul_5760 {x : ℝ} (hx : 5760 < x) : 5762.479 * x - 16617319 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5760.1 psiOneGrid2_cert_5760.2.1 psiOneGrid2_cert_5760.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5760`: `ψ₁(x) ≥ 5762.479 - 16617319/x` (sharp on `(5760, 5776]`). -/
theorem psiOne_lower_grid2_5760 {x : ℝ} (hx : 5760 < x) : 5762.479 - 16617319 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5760.1 psiOneGrid2_cert_5760.2.1 psiOneGrid2_cert_5760.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5760 {x : ℝ} (hx : 5760 < x) (hx' : x ≤ 5776) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5760 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5776 :
    24040448 ≤ (psiAcc 5776).2.2 ∧ 2 ^ 36849 ≤ (psiAcc 5776).2.1 ^ 8 ∧ 2 ^ 66508 ≤ (psiAcc 5776).1 ^ 8 := by
  decide +kernel

/-- For `x > 5776`: `5762.479 x - 16617318 ≤ x ψ₁(x)` (sharp on `(5776, 5792]`). -/
theorem psiOne_lower_grid2_mul_5776 {x : ℝ} (hx : 5776 < x) : 5762.479 * x - 16617318 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5776.1 psiOneGrid2_cert_5776.2.1 psiOneGrid2_cert_5776.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5776`: `ψ₁(x) ≥ 5762.479 - 16617318/x` (sharp on `(5776, 5792]`). -/
theorem psiOne_lower_grid2_5776 {x : ℝ} (hx : 5776 < x) : 5762.479 - 16617318 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5776.1 psiOneGrid2_cert_5776.2.1 psiOneGrid2_cert_5776.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5776 {x : ℝ} (hx : 5776 < x) (hx' : x ≤ 5792) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5776 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5792 :
    24171008 ≤ (psiAcc 5792).2.2 ∧ 2 ^ 58803 ≤ (psiAcc 5792).2.1 ^ 8 ∧ 2 ^ 66808 ≤ (psiAcc 5792).1 ^ 8 := by
  decide +kernel

/-- For `x > 5792`: `5788.472 x - 16767670 ≤ x ψ₁(x)` (sharp on `(5792, 5808]`). -/
theorem psiOne_lower_grid2_mul_5792 {x : ℝ} (hx : 5792 < x) : 5788.472 * x - 16767670 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5792.1 psiOneGrid2_cert_5792.2.1 psiOneGrid2_cert_5792.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5792`: `ψ₁(x) ≥ 5788.472 - 16767670/x` (sharp on `(5792, 5808]`). -/
theorem psiOne_lower_grid2_5792 {x : ℝ} (hx : 5792 < x) : 5788.472 - 16767670 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5792.1 psiOneGrid2_cert_5792.2.1 psiOneGrid2_cert_5792.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5792 {x : ℝ} (hx : 5792 < x) (hx' : x ≤ 5808) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5792 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5808 :
    24310272 ≤ (psiAcc 5808).2.2 ∧ 2 ^ 14425 ≤ (psiAcc 5808).2.1 ^ 8 ∧ 2 ^ 67008 ≤ (psiAcc 5808).1 ^ 8 := by
  decide +kernel

/-- For `x > 5808`: `5805.800 x - 16868245 ≤ x ψ₁(x)` (sharp on `(5808, 5824]`). -/
theorem psiOne_lower_grid2_mul_5808 {x : ℝ} (hx : 5808 < x) : 5805.800 * x - 16868245 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5808.1 psiOneGrid2_cert_5808.2.1 psiOneGrid2_cert_5808.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5808`: `ψ₁(x) ≥ 5805.800 - 16868245/x` (sharp on `(5808, 5824]`). -/
theorem psiOne_lower_grid2_5808 {x : ℝ} (hx : 5808 < x) : 5805.800 - 16868245 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5808.1 psiOneGrid2_cert_5808.2.1 psiOneGrid2_cert_5808.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5808 {x : ℝ} (hx : 5808 < x) (hx' : x ≤ 5824) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5808 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5824 :
    24440832 ≤ (psiAcc 5824).2.2 ∧ 2 ^ 43480 ≤ (psiAcc 5824).2.1 ^ 8 ∧ 2 ^ 67208 ≤ (psiAcc 5824).1 ^ 8 := by
  decide +kernel

/-- For `x > 5824`: `5823.129 x - 16969045 ≤ x ψ₁(x)` (sharp on `(5824, 5840]`). -/
theorem psiOne_lower_grid2_mul_5824 {x : ℝ} (hx : 5824 < x) : 5823.129 * x - 16969045 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5824.1 psiOneGrid2_cert_5824.2.1 psiOneGrid2_cert_5824.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5824`: `ψ₁(x) ≥ 5823.129 - 16969045/x` (sharp on `(5824, 5840]`). -/
theorem psiOne_lower_grid2_5824 {x : ℝ} (hx : 5824 < x) : 5823.129 - 16969045 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5824.1 psiOneGrid2_cert_5824.2.1 psiOneGrid2_cert_5824.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5824 {x : ℝ} (hx : 5824 < x) (hx' : x ≤ 5840) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5824 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5840 :
    24580096 ≤ (psiAcc 5840).2.2 ∧ 2 ^ 6105 ≤ (psiAcc 5840).2.1 ^ 8 ∧ 2 ^ 67408 ≤ (psiAcc 5840).1 ^ 8 := by
  decide +kernel

/-- For `x > 5840`: `5840.458 x - 17070123 ≤ x ψ₁(x)` (sharp on `(5840, 5856]`). -/
theorem psiOne_lower_grid2_mul_5840 {x : ℝ} (hx : 5840 < x) : 5840.458 * x - 17070123 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5840.1 psiOneGrid2_cert_5840.2.1 psiOneGrid2_cert_5840.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5840`: `ψ₁(x) ≥ 5840.458 - 17070123/x` (sharp on `(5840, 5856]`). -/
theorem psiOne_lower_grid2_5840 {x : ℝ} (hx : 5840 < x) : 5840.458 - 17070123 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5840.1 psiOneGrid2_cert_5840.2.1 psiOneGrid2_cert_5840.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5840 {x : ℝ} (hx : 5840 < x) (hx' : x ≤ 5856) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5840 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5856 :
    24710656 ≤ (psiAcc 5856).2.2 ∧ 2 ^ 42666 ≤ (psiAcc 5856).2.1 ^ 8 ∧ 2 ^ 67708 ≤ (psiAcc 5856).1 ^ 8 := by
  decide +kernel

/-- For `x > 5856`: `5866.451 x - 17222120 ≤ x ψ₁(x)` (sharp on `(5856, 5872]`). -/
theorem psiOne_lower_grid2_mul_5856 {x : ℝ} (hx : 5856 < x) : 5866.451 * x - 17222120 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5856.1 psiOneGrid2_cert_5856.2.1 psiOneGrid2_cert_5856.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5856`: `ψ₁(x) ≥ 5866.451 - 17222120/x` (sharp on `(5856, 5872]`). -/
theorem psiOne_lower_grid2_5856 {x : ℝ} (hx : 5856 < x) : 5866.451 - 17222120 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5856.1 psiOneGrid2_cert_5856.2.1 psiOneGrid2_cert_5856.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5856 {x : ℝ} (hx : 5856 < x) (hx' : x ≤ 5872) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5856 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5872 :
    24849920 ≤ (psiAcc 5872).2.2 ∧ 2 ^ 15302 ≤ (psiAcc 5872).2.1 ^ 8 ∧ 2 ^ 68109 ≤ (psiAcc 5872).1 ^ 8 := by
  decide +kernel

/-- For `x > 5872`: `5901.195 x - 17425841 ≤ x ψ₁(x)` (sharp on `(5872, 5888]`). -/
theorem psiOne_lower_grid2_mul_5872 {x : ℝ} (hx : 5872 < x) : 5901.195 * x - 17425841 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5872.1 psiOneGrid2_cert_5872.2.1 psiOneGrid2_cert_5872.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5872`: `ψ₁(x) ≥ 5901.195 - 17425841/x` (sharp on `(5872, 5888]`). -/
theorem psiOne_lower_grid2_5872 {x : ℝ} (hx : 5872 < x) : 5901.195 - 17425841 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5872.1 psiOneGrid2_cert_5872.2.1 psiOneGrid2_cert_5872.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5872 {x : ℝ} (hx : 5872 < x) (hx' : x ≤ 5888) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5872 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5888 :
    24980480 ≤ (psiAcc 5888).2.2 ∧ 2 ^ 62178 ≤ (psiAcc 5888).2.1 ^ 8 ∧ 2 ^ 68309 ≤ (psiAcc 5888).1 ^ 8 := by
  decide +kernel

/-- For `x > 5888`: `5918.523 x - 17527732 ≤ x ψ₁(x)` (sharp on `(5888, 5904]`). -/
theorem psiOne_lower_grid2_mul_5888 {x : ℝ} (hx : 5888 < x) : 5918.523 * x - 17527732 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5888.1 psiOneGrid2_cert_5888.2.1 psiOneGrid2_cert_5888.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5888`: `ψ₁(x) ≥ 5918.523 - 17527732/x` (sharp on `(5888, 5904]`). -/
theorem psiOne_lower_grid2_5888 {x : ℝ} (hx : 5888 < x) : 5918.523 - 17527732 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5888.1 psiOneGrid2_cert_5888.2.1 psiOneGrid2_cert_5888.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5888 {x : ℝ} (hx : 5888 < x) (hx' : x ≤ 5904) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5888 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5904 :
    25119744 ≤ (psiAcc 5904).2.2 ∧ 2 ^ 41825 ≤ (psiAcc 5904).2.1 ^ 8 ∧ 2 ^ 68510 ≤ (psiAcc 5904).1 ^ 8 := by
  decide +kernel

/-- For `x > 5904`: `5935.939 x - 17630482 ≤ x ψ₁(x)` (sharp on `(5904, 5920]`). -/
theorem psiOne_lower_grid2_mul_5904 {x : ℝ} (hx : 5904 < x) : 5935.939 * x - 17630482 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5904.1 psiOneGrid2_cert_5904.2.1 psiOneGrid2_cert_5904.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5904`: `ψ₁(x) ≥ 5935.939 - 17630482/x` (sharp on `(5904, 5920]`). -/
theorem psiOne_lower_grid2_5904 {x : ℝ} (hx : 5904 < x) : 5935.939 - 17630482 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5904.1 psiOneGrid2_cert_5904.2.1 psiOneGrid2_cert_5904.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5904 {x : ℝ} (hx : 5904 < x) (hx' : x ≤ 5920) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5904 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5920 :
    25259008 ≤ (psiAcc 5920).2.2 ∧ 2 ^ 23879 ≤ (psiAcc 5920).2.1 ^ 8 ∧ 2 ^ 68510 ≤ (psiAcc 5920).1 ^ 8 := by
  decide +kernel

/-- For `x > 5920`: `5935.939 x - 17630481 ≤ x ψ₁(x)` (sharp on `(5920, 5936]`). -/
theorem psiOne_lower_grid2_mul_5920 {x : ℝ} (hx : 5920 < x) : 5935.939 * x - 17630481 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5920.1 psiOneGrid2_cert_5920.2.1 psiOneGrid2_cert_5920.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5920`: `ψ₁(x) ≥ 5935.939 - 17630481/x` (sharp on `(5920, 5936]`). -/
theorem psiOne_lower_grid2_5920 {x : ℝ} (hx : 5920 < x) : 5935.939 - 17630481 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5920.1 psiOneGrid2_cert_5920.2.1 psiOneGrid2_cert_5920.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5920 {x : ℝ} (hx : 5920 < x) (hx' : x ≤ 5936) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5920 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5936 :
    25398272 ≤ (psiAcc 5936).2.2 ∧ 2 ^ 8137 ≤ (psiAcc 5936).2.1 ^ 8 ∧ 2 ^ 68710 ≤ (psiAcc 5936).1 ^ 8 := by
  decide +kernel

/-- For `x > 5936`: `5953.267 x - 17733153 ≤ x ψ₁(x)` (sharp on `(5936, 5952]`). -/
theorem psiOne_lower_grid2_mul_5936 {x : ℝ} (hx : 5936 < x) : 5953.267 * x - 17733153 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5936.1 psiOneGrid2_cert_5936.2.1 psiOneGrid2_cert_5936.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5936`: `ψ₁(x) ≥ 5953.267 - 17733153/x` (sharp on `(5936, 5952]`). -/
theorem psiOne_lower_grid2_5936 {x : ℝ} (hx : 5936 < x) : 5953.267 - 17733153 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5936.1 psiOneGrid2_cert_5936.2.1 psiOneGrid2_cert_5936.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5936 {x : ℝ} (hx : 5936 < x) (hx' : x ≤ 5952) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5936 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5952 :
    25528832 ≤ (psiAcc 5952).2.2 ∧ 2 ^ 64334 ≤ (psiAcc 5952).2.1 ^ 8 ∧ 2 ^ 68811 ≤ (psiAcc 5952).1 ^ 8 := by
  decide +kernel

/-- For `x > 5952`: `5962.018 x - 17785125 ≤ x ψ₁(x)` (sharp on `(5952, 5968]`). -/
theorem psiOne_lower_grid2_mul_5952 {x : ℝ} (hx : 5952 < x) : 5962.018 * x - 17785125 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5952.1 psiOneGrid2_cert_5952.2.1 psiOneGrid2_cert_5952.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5952`: `ψ₁(x) ≥ 5962.018 - 17785125/x` (sharp on `(5952, 5968]`). -/
theorem psiOne_lower_grid2_5952 {x : ℝ} (hx : 5952 < x) : 5962.018 - 17785125 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5952.1 psiOneGrid2_cert_5952.2.1 psiOneGrid2_cert_5952.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5952 {x : ℝ} (hx : 5952 < x) (hx' : x ≤ 5968) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5952 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5968 :
    25668096 ≤ (psiAcc 5968).2.2 ∧ 2 ^ 52705 ≤ (psiAcc 5968).2.1 ^ 8 ∧ 2 ^ 68911 ≤ (psiAcc 5968).1 ^ 8 := by
  decide +kernel

/-- For `x > 5968`: `5970.683 x - 17836703 ≤ x ψ₁(x)` (sharp on `(5968, 5984]`). -/
theorem psiOne_lower_grid2_mul_5968 {x : ℝ} (hx : 5968 < x) : 5970.683 * x - 17836703 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5968.1 psiOneGrid2_cert_5968.2.1 psiOneGrid2_cert_5968.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5968`: `ψ₁(x) ≥ 5970.683 - 17836703/x` (sharp on `(5968, 5984]`). -/
theorem psiOne_lower_grid2_5968 {x : ℝ} (hx : 5968 < x) : 5970.683 - 17836703 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5968.1 psiOneGrid2_cert_5968.2.1 psiOneGrid2_cert_5968.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5968 {x : ℝ} (hx : 5968 < x) (hx' : x ≤ 5984) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5968 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_cert_5984 :
    25807360 ≤ (psiAcc 5984).2.2 ∧ 2 ^ 41477 ≤ (psiAcc 5984).2.1 ^ 8 ∧ 2 ^ 69011 ≤ (psiAcc 5984).1 ^ 8 := by
  decide +kernel

/-- For `x > 5984`: `5979.347 x - 17888523 ≤ x ψ₁(x)` (sharp on `(5984, 6000]`). -/
theorem psiOne_lower_grid2_mul_5984 {x : ℝ} (hx : 5984 < x) : 5979.347 * x - 17888523 ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_5984.1 psiOneGrid2_cert_5984.2.1 psiOneGrid2_cert_5984.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/-- For `x > 5984`: `ψ₁(x) ≥ 5979.347 - 17888523/x` (sharp on `(5984, 6000]`). -/
theorem psiOne_lower_grid2_5984 {x : ℝ} (hx : 5984 < x) : 5979.347 - 17888523 / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_5984.1 psiOneGrid2_cert_5984.2.1 psiOneGrid2_cert_5984.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_5984 {x : ℝ} (hx : 5984 < x) (hx' : x ≤ 6000) :
    x / 2 - 2.9 ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_5984 hx) (by norm_num) (by norm_num) (by norm_num) hx hx'

theorem psiOneGrid2_block_1536 {x : ℝ} (hx : 1536 < x) (hx' : x ≤ 1792) :
    x / 2 - 2.9 ≤ psiOne x := by
  rcases le_or_gt x 1552 with h | h
  · exact psiOneGrid2_cell_1536 (by assumption) h
  rcases le_or_gt x 1568 with h | h
  · exact psiOneGrid2_cell_1552 (by assumption) h
  rcases le_or_gt x 1584 with h | h
  · exact psiOneGrid2_cell_1568 (by assumption) h
  rcases le_or_gt x 1600 with h | h
  · exact psiOneGrid2_cell_1584 (by assumption) h
  rcases le_or_gt x 1616 with h | h
  · exact psiOneGrid2_cell_1600 (by assumption) h
  rcases le_or_gt x 1632 with h | h
  · exact psiOneGrid2_cell_1616 (by assumption) h
  rcases le_or_gt x 1648 with h | h
  · exact psiOneGrid2_cell_1632 (by assumption) h
  rcases le_or_gt x 1664 with h | h
  · exact psiOneGrid2_cell_1648 (by assumption) h
  rcases le_or_gt x 1680 with h | h
  · exact psiOneGrid2_cell_1664 (by assumption) h
  rcases le_or_gt x 1696 with h | h
  · exact psiOneGrid2_cell_1680 (by assumption) h
  rcases le_or_gt x 1712 with h | h
  · exact psiOneGrid2_cell_1696 (by assumption) h
  rcases le_or_gt x 1728 with h | h
  · exact psiOneGrid2_cell_1712 (by assumption) h
  rcases le_or_gt x 1744 with h | h
  · exact psiOneGrid2_cell_1728 (by assumption) h
  rcases le_or_gt x 1760 with h | h
  · exact psiOneGrid2_cell_1744 (by assumption) h
  rcases le_or_gt x 1776 with h | h
  · exact psiOneGrid2_cell_1760 (by assumption) h
  exact psiOneGrid2_cell_1776 (by assumption) hx'

theorem psiOneGrid2_block_1792 {x : ℝ} (hx : 1792 < x) (hx' : x ≤ 2048) :
    x / 2 - 2.9 ≤ psiOne x := by
  rcases le_or_gt x 1808 with h | h
  · exact psiOneGrid2_cell_1792 (by assumption) h
  rcases le_or_gt x 1824 with h | h
  · exact psiOneGrid2_cell_1808 (by assumption) h
  rcases le_or_gt x 1840 with h | h
  · exact psiOneGrid2_cell_1824 (by assumption) h
  rcases le_or_gt x 1856 with h | h
  · exact psiOneGrid2_cell_1840 (by assumption) h
  rcases le_or_gt x 1872 with h | h
  · exact psiOneGrid2_cell_1856 (by assumption) h
  rcases le_or_gt x 1888 with h | h
  · exact psiOneGrid2_cell_1872 (by assumption) h
  rcases le_or_gt x 1904 with h | h
  · exact psiOneGrid2_cell_1888 (by assumption) h
  rcases le_or_gt x 1920 with h | h
  · exact psiOneGrid2_cell_1904 (by assumption) h
  rcases le_or_gt x 1936 with h | h
  · exact psiOneGrid2_cell_1920 (by assumption) h
  rcases le_or_gt x 1952 with h | h
  · exact psiOneGrid2_cell_1936 (by assumption) h
  rcases le_or_gt x 1968 with h | h
  · exact psiOneGrid2_cell_1952 (by assumption) h
  rcases le_or_gt x 1984 with h | h
  · exact psiOneGrid2_cell_1968 (by assumption) h
  rcases le_or_gt x 2000 with h | h
  · exact psiOneGrid2_cell_1984 (by assumption) h
  rcases le_or_gt x 2016 with h | h
  · exact psiOneGrid2_cell_2000 (by assumption) h
  rcases le_or_gt x 2032 with h | h
  · exact psiOneGrid2_cell_2016 (by assumption) h
  exact psiOneGrid2_cell_2032 (by assumption) hx'

theorem psiOneGrid2_block_2048 {x : ℝ} (hx : 2048 < x) (hx' : x ≤ 2304) :
    x / 2 - 2.9 ≤ psiOne x := by
  rcases le_or_gt x 2064 with h | h
  · exact psiOneGrid2_cell_2048 (by assumption) h
  rcases le_or_gt x 2080 with h | h
  · exact psiOneGrid2_cell_2064 (by assumption) h
  rcases le_or_gt x 2096 with h | h
  · exact psiOneGrid2_cell_2080 (by assumption) h
  rcases le_or_gt x 2112 with h | h
  · exact psiOneGrid2_cell_2096 (by assumption) h
  rcases le_or_gt x 2128 with h | h
  · exact psiOneGrid2_cell_2112 (by assumption) h
  rcases le_or_gt x 2144 with h | h
  · exact psiOneGrid2_cell_2128 (by assumption) h
  rcases le_or_gt x 2160 with h | h
  · exact psiOneGrid2_cell_2144 (by assumption) h
  rcases le_or_gt x 2176 with h | h
  · exact psiOneGrid2_cell_2160 (by assumption) h
  rcases le_or_gt x 2192 with h | h
  · exact psiOneGrid2_cell_2176 (by assumption) h
  rcases le_or_gt x 2208 with h | h
  · exact psiOneGrid2_cell_2192 (by assumption) h
  rcases le_or_gt x 2224 with h | h
  · exact psiOneGrid2_cell_2208 (by assumption) h
  rcases le_or_gt x 2240 with h | h
  · exact psiOneGrid2_cell_2224 (by assumption) h
  rcases le_or_gt x 2256 with h | h
  · exact psiOneGrid2_cell_2240 (by assumption) h
  rcases le_or_gt x 2272 with h | h
  · exact psiOneGrid2_cell_2256 (by assumption) h
  rcases le_or_gt x 2288 with h | h
  · exact psiOneGrid2_cell_2272 (by assumption) h
  exact psiOneGrid2_cell_2288 (by assumption) hx'

theorem psiOneGrid2_block_2304 {x : ℝ} (hx : 2304 < x) (hx' : x ≤ 2560) :
    x / 2 - 2.9 ≤ psiOne x := by
  rcases le_or_gt x 2320 with h | h
  · exact psiOneGrid2_cell_2304 (by assumption) h
  rcases le_or_gt x 2336 with h | h
  · exact psiOneGrid2_cell_2320 (by assumption) h
  rcases le_or_gt x 2352 with h | h
  · exact psiOneGrid2_cell_2336 (by assumption) h
  rcases le_or_gt x 2368 with h | h
  · exact psiOneGrid2_cell_2352 (by assumption) h
  rcases le_or_gt x 2384 with h | h
  · exact psiOneGrid2_cell_2368 (by assumption) h
  rcases le_or_gt x 2400 with h | h
  · exact psiOneGrid2_cell_2384 (by assumption) h
  rcases le_or_gt x 2416 with h | h
  · exact psiOneGrid2_cell_2400 (by assumption) h
  rcases le_or_gt x 2432 with h | h
  · exact psiOneGrid2_cell_2416 (by assumption) h
  rcases le_or_gt x 2448 with h | h
  · exact psiOneGrid2_cell_2432 (by assumption) h
  rcases le_or_gt x 2464 with h | h
  · exact psiOneGrid2_cell_2448 (by assumption) h
  rcases le_or_gt x 2480 with h | h
  · exact psiOneGrid2_cell_2464 (by assumption) h
  rcases le_or_gt x 2496 with h | h
  · exact psiOneGrid2_cell_2480 (by assumption) h
  rcases le_or_gt x 2512 with h | h
  · exact psiOneGrid2_cell_2496 (by assumption) h
  rcases le_or_gt x 2528 with h | h
  · exact psiOneGrid2_cell_2512 (by assumption) h
  rcases le_or_gt x 2544 with h | h
  · exact psiOneGrid2_cell_2528 (by assumption) h
  exact psiOneGrid2_cell_2544 (by assumption) hx'

theorem psiOneGrid2_block_2560 {x : ℝ} (hx : 2560 < x) (hx' : x ≤ 2816) :
    x / 2 - 2.9 ≤ psiOne x := by
  rcases le_or_gt x 2576 with h | h
  · exact psiOneGrid2_cell_2560 (by assumption) h
  rcases le_or_gt x 2592 with h | h
  · exact psiOneGrid2_cell_2576 (by assumption) h
  rcases le_or_gt x 2608 with h | h
  · exact psiOneGrid2_cell_2592 (by assumption) h
  rcases le_or_gt x 2624 with h | h
  · exact psiOneGrid2_cell_2608 (by assumption) h
  rcases le_or_gt x 2640 with h | h
  · exact psiOneGrid2_cell_2624 (by assumption) h
  rcases le_or_gt x 2656 with h | h
  · exact psiOneGrid2_cell_2640 (by assumption) h
  rcases le_or_gt x 2672 with h | h
  · exact psiOneGrid2_cell_2656 (by assumption) h
  rcases le_or_gt x 2688 with h | h
  · exact psiOneGrid2_cell_2672 (by assumption) h
  rcases le_or_gt x 2704 with h | h
  · exact psiOneGrid2_cell_2688 (by assumption) h
  rcases le_or_gt x 2720 with h | h
  · exact psiOneGrid2_cell_2704 (by assumption) h
  rcases le_or_gt x 2736 with h | h
  · exact psiOneGrid2_cell_2720 (by assumption) h
  rcases le_or_gt x 2752 with h | h
  · exact psiOneGrid2_cell_2736 (by assumption) h
  rcases le_or_gt x 2768 with h | h
  · exact psiOneGrid2_cell_2752 (by assumption) h
  rcases le_or_gt x 2784 with h | h
  · exact psiOneGrid2_cell_2768 (by assumption) h
  rcases le_or_gt x 2800 with h | h
  · exact psiOneGrid2_cell_2784 (by assumption) h
  exact psiOneGrid2_cell_2800 (by assumption) hx'

theorem psiOneGrid2_block_2816 {x : ℝ} (hx : 2816 < x) (hx' : x ≤ 3072) :
    x / 2 - 2.9 ≤ psiOne x := by
  rcases le_or_gt x 2832 with h | h
  · exact psiOneGrid2_cell_2816 (by assumption) h
  rcases le_or_gt x 2848 with h | h
  · exact psiOneGrid2_cell_2832 (by assumption) h
  rcases le_or_gt x 2864 with h | h
  · exact psiOneGrid2_cell_2848 (by assumption) h
  rcases le_or_gt x 2880 with h | h
  · exact psiOneGrid2_cell_2864 (by assumption) h
  rcases le_or_gt x 2896 with h | h
  · exact psiOneGrid2_cell_2880 (by assumption) h
  rcases le_or_gt x 2912 with h | h
  · exact psiOneGrid2_cell_2896 (by assumption) h
  rcases le_or_gt x 2928 with h | h
  · exact psiOneGrid2_cell_2912 (by assumption) h
  rcases le_or_gt x 2944 with h | h
  · exact psiOneGrid2_cell_2928 (by assumption) h
  rcases le_or_gt x 2960 with h | h
  · exact psiOneGrid2_cell_2944 (by assumption) h
  rcases le_or_gt x 2976 with h | h
  · exact psiOneGrid2_cell_2960 (by assumption) h
  rcases le_or_gt x 2992 with h | h
  · exact psiOneGrid2_cell_2976 (by assumption) h
  rcases le_or_gt x 3008 with h | h
  · exact psiOneGrid2_cell_2992 (by assumption) h
  rcases le_or_gt x 3024 with h | h
  · exact psiOneGrid2_cell_3008 (by assumption) h
  rcases le_or_gt x 3040 with h | h
  · exact psiOneGrid2_cell_3024 (by assumption) h
  rcases le_or_gt x 3056 with h | h
  · exact psiOneGrid2_cell_3040 (by assumption) h
  exact psiOneGrid2_cell_3056 (by assumption) hx'

theorem psiOneGrid2_block_3072 {x : ℝ} (hx : 3072 < x) (hx' : x ≤ 3328) :
    x / 2 - 2.9 ≤ psiOne x := by
  rcases le_or_gt x 3088 with h | h
  · exact psiOneGrid2_cell_3072 (by assumption) h
  rcases le_or_gt x 3104 with h | h
  · exact psiOneGrid2_cell_3088 (by assumption) h
  rcases le_or_gt x 3120 with h | h
  · exact psiOneGrid2_cell_3104 (by assumption) h
  rcases le_or_gt x 3136 with h | h
  · exact psiOneGrid2_cell_3120 (by assumption) h
  rcases le_or_gt x 3152 with h | h
  · exact psiOneGrid2_cell_3136 (by assumption) h
  rcases le_or_gt x 3168 with h | h
  · exact psiOneGrid2_cell_3152 (by assumption) h
  rcases le_or_gt x 3184 with h | h
  · exact psiOneGrid2_cell_3168 (by assumption) h
  rcases le_or_gt x 3200 with h | h
  · exact psiOneGrid2_cell_3184 (by assumption) h
  rcases le_or_gt x 3216 with h | h
  · exact psiOneGrid2_cell_3200 (by assumption) h
  rcases le_or_gt x 3232 with h | h
  · exact psiOneGrid2_cell_3216 (by assumption) h
  rcases le_or_gt x 3248 with h | h
  · exact psiOneGrid2_cell_3232 (by assumption) h
  rcases le_or_gt x 3264 with h | h
  · exact psiOneGrid2_cell_3248 (by assumption) h
  rcases le_or_gt x 3280 with h | h
  · exact psiOneGrid2_cell_3264 (by assumption) h
  rcases le_or_gt x 3296 with h | h
  · exact psiOneGrid2_cell_3280 (by assumption) h
  rcases le_or_gt x 3312 with h | h
  · exact psiOneGrid2_cell_3296 (by assumption) h
  exact psiOneGrid2_cell_3312 (by assumption) hx'

theorem psiOneGrid2_block_3328 {x : ℝ} (hx : 3328 < x) (hx' : x ≤ 3584) :
    x / 2 - 2.9 ≤ psiOne x := by
  rcases le_or_gt x 3344 with h | h
  · exact psiOneGrid2_cell_3328 (by assumption) h
  rcases le_or_gt x 3360 with h | h
  · exact psiOneGrid2_cell_3344 (by assumption) h
  rcases le_or_gt x 3376 with h | h
  · exact psiOneGrid2_cell_3360 (by assumption) h
  rcases le_or_gt x 3392 with h | h
  · exact psiOneGrid2_cell_3376 (by assumption) h
  rcases le_or_gt x 3408 with h | h
  · exact psiOneGrid2_cell_3392 (by assumption) h
  rcases le_or_gt x 3424 with h | h
  · exact psiOneGrid2_cell_3408 (by assumption) h
  rcases le_or_gt x 3440 with h | h
  · exact psiOneGrid2_cell_3424 (by assumption) h
  rcases le_or_gt x 3456 with h | h
  · exact psiOneGrid2_cell_3440 (by assumption) h
  rcases le_or_gt x 3472 with h | h
  · exact psiOneGrid2_cell_3456 (by assumption) h
  rcases le_or_gt x 3488 with h | h
  · exact psiOneGrid2_cell_3472 (by assumption) h
  rcases le_or_gt x 3504 with h | h
  · exact psiOneGrid2_cell_3488 (by assumption) h
  rcases le_or_gt x 3520 with h | h
  · exact psiOneGrid2_cell_3504 (by assumption) h
  rcases le_or_gt x 3536 with h | h
  · exact psiOneGrid2_cell_3520 (by assumption) h
  rcases le_or_gt x 3552 with h | h
  · exact psiOneGrid2_cell_3536 (by assumption) h
  rcases le_or_gt x 3568 with h | h
  · exact psiOneGrid2_cell_3552 (by assumption) h
  exact psiOneGrid2_cell_3568 (by assumption) hx'

theorem psiOneGrid2_block_3584 {x : ℝ} (hx : 3584 < x) (hx' : x ≤ 3840) :
    x / 2 - 2.9 ≤ psiOne x := by
  rcases le_or_gt x 3600 with h | h
  · exact psiOneGrid2_cell_3584 (by assumption) h
  rcases le_or_gt x 3616 with h | h
  · exact psiOneGrid2_cell_3600 (by assumption) h
  rcases le_or_gt x 3632 with h | h
  · exact psiOneGrid2_cell_3616 (by assumption) h
  rcases le_or_gt x 3648 with h | h
  · exact psiOneGrid2_cell_3632 (by assumption) h
  rcases le_or_gt x 3664 with h | h
  · exact psiOneGrid2_cell_3648 (by assumption) h
  rcases le_or_gt x 3680 with h | h
  · exact psiOneGrid2_cell_3664 (by assumption) h
  rcases le_or_gt x 3696 with h | h
  · exact psiOneGrid2_cell_3680 (by assumption) h
  rcases le_or_gt x 3712 with h | h
  · exact psiOneGrid2_cell_3696 (by assumption) h
  rcases le_or_gt x 3728 with h | h
  · exact psiOneGrid2_cell_3712 (by assumption) h
  rcases le_or_gt x 3744 with h | h
  · exact psiOneGrid2_cell_3728 (by assumption) h
  rcases le_or_gt x 3760 with h | h
  · exact psiOneGrid2_cell_3744 (by assumption) h
  rcases le_or_gt x 3776 with h | h
  · exact psiOneGrid2_cell_3760 (by assumption) h
  rcases le_or_gt x 3792 with h | h
  · exact psiOneGrid2_cell_3776 (by assumption) h
  rcases le_or_gt x 3808 with h | h
  · exact psiOneGrid2_cell_3792 (by assumption) h
  rcases le_or_gt x 3824 with h | h
  · exact psiOneGrid2_cell_3808 (by assumption) h
  exact psiOneGrid2_cell_3824 (by assumption) hx'

theorem psiOneGrid2_block_3840 {x : ℝ} (hx : 3840 < x) (hx' : x ≤ 4096) :
    x / 2 - 2.9 ≤ psiOne x := by
  rcases le_or_gt x 3856 with h | h
  · exact psiOneGrid2_cell_3840 (by assumption) h
  rcases le_or_gt x 3872 with h | h
  · exact psiOneGrid2_cell_3856 (by assumption) h
  rcases le_or_gt x 3888 with h | h
  · exact psiOneGrid2_cell_3872 (by assumption) h
  rcases le_or_gt x 3904 with h | h
  · exact psiOneGrid2_cell_3888 (by assumption) h
  rcases le_or_gt x 3920 with h | h
  · exact psiOneGrid2_cell_3904 (by assumption) h
  rcases le_or_gt x 3936 with h | h
  · exact psiOneGrid2_cell_3920 (by assumption) h
  rcases le_or_gt x 3952 with h | h
  · exact psiOneGrid2_cell_3936 (by assumption) h
  rcases le_or_gt x 3968 with h | h
  · exact psiOneGrid2_cell_3952 (by assumption) h
  rcases le_or_gt x 3984 with h | h
  · exact psiOneGrid2_cell_3968 (by assumption) h
  rcases le_or_gt x 4000 with h | h
  · exact psiOneGrid2_cell_3984 (by assumption) h
  rcases le_or_gt x 4016 with h | h
  · exact psiOneGrid2_cell_4000 (by assumption) h
  rcases le_or_gt x 4032 with h | h
  · exact psiOneGrid2_cell_4016 (by assumption) h
  rcases le_or_gt x 4048 with h | h
  · exact psiOneGrid2_cell_4032 (by assumption) h
  rcases le_or_gt x 4064 with h | h
  · exact psiOneGrid2_cell_4048 (by assumption) h
  rcases le_or_gt x 4080 with h | h
  · exact psiOneGrid2_cell_4064 (by assumption) h
  exact psiOneGrid2_cell_4080 (by assumption) hx'

theorem psiOneGrid2_block_4096 {x : ℝ} (hx : 4096 < x) (hx' : x ≤ 4352) :
    x / 2 - 2.9 ≤ psiOne x := by
  rcases le_or_gt x 4112 with h | h
  · exact psiOneGrid2_cell_4096 (by assumption) h
  rcases le_or_gt x 4128 with h | h
  · exact psiOneGrid2_cell_4112 (by assumption) h
  rcases le_or_gt x 4144 with h | h
  · exact psiOneGrid2_cell_4128 (by assumption) h
  rcases le_or_gt x 4160 with h | h
  · exact psiOneGrid2_cell_4144 (by assumption) h
  rcases le_or_gt x 4176 with h | h
  · exact psiOneGrid2_cell_4160 (by assumption) h
  rcases le_or_gt x 4192 with h | h
  · exact psiOneGrid2_cell_4176 (by assumption) h
  rcases le_or_gt x 4208 with h | h
  · exact psiOneGrid2_cell_4192 (by assumption) h
  rcases le_or_gt x 4224 with h | h
  · exact psiOneGrid2_cell_4208 (by assumption) h
  rcases le_or_gt x 4240 with h | h
  · exact psiOneGrid2_cell_4224 (by assumption) h
  rcases le_or_gt x 4256 with h | h
  · exact psiOneGrid2_cell_4240 (by assumption) h
  rcases le_or_gt x 4272 with h | h
  · exact psiOneGrid2_cell_4256 (by assumption) h
  rcases le_or_gt x 4288 with h | h
  · exact psiOneGrid2_cell_4272 (by assumption) h
  rcases le_or_gt x 4304 with h | h
  · exact psiOneGrid2_cell_4288 (by assumption) h
  rcases le_or_gt x 4320 with h | h
  · exact psiOneGrid2_cell_4304 (by assumption) h
  rcases le_or_gt x 4336 with h | h
  · exact psiOneGrid2_cell_4320 (by assumption) h
  exact psiOneGrid2_cell_4336 (by assumption) hx'

theorem psiOneGrid2_block_4352 {x : ℝ} (hx : 4352 < x) (hx' : x ≤ 4608) :
    x / 2 - 2.9 ≤ psiOne x := by
  rcases le_or_gt x 4368 with h | h
  · exact psiOneGrid2_cell_4352 (by assumption) h
  rcases le_or_gt x 4384 with h | h
  · exact psiOneGrid2_cell_4368 (by assumption) h
  rcases le_or_gt x 4400 with h | h
  · exact psiOneGrid2_cell_4384 (by assumption) h
  rcases le_or_gt x 4416 with h | h
  · exact psiOneGrid2_cell_4400 (by assumption) h
  rcases le_or_gt x 4432 with h | h
  · exact psiOneGrid2_cell_4416 (by assumption) h
  rcases le_or_gt x 4448 with h | h
  · exact psiOneGrid2_cell_4432 (by assumption) h
  rcases le_or_gt x 4464 with h | h
  · exact psiOneGrid2_cell_4448 (by assumption) h
  rcases le_or_gt x 4480 with h | h
  · exact psiOneGrid2_cell_4464 (by assumption) h
  rcases le_or_gt x 4496 with h | h
  · exact psiOneGrid2_cell_4480 (by assumption) h
  rcases le_or_gt x 4512 with h | h
  · exact psiOneGrid2_cell_4496 (by assumption) h
  rcases le_or_gt x 4528 with h | h
  · exact psiOneGrid2_cell_4512 (by assumption) h
  rcases le_or_gt x 4544 with h | h
  · exact psiOneGrid2_cell_4528 (by assumption) h
  rcases le_or_gt x 4560 with h | h
  · exact psiOneGrid2_cell_4544 (by assumption) h
  rcases le_or_gt x 4576 with h | h
  · exact psiOneGrid2_cell_4560 (by assumption) h
  rcases le_or_gt x 4592 with h | h
  · exact psiOneGrid2_cell_4576 (by assumption) h
  exact psiOneGrid2_cell_4592 (by assumption) hx'

theorem psiOneGrid2_block_4608 {x : ℝ} (hx : 4608 < x) (hx' : x ≤ 4864) :
    x / 2 - 2.9 ≤ psiOne x := by
  rcases le_or_gt x 4624 with h | h
  · exact psiOneGrid2_cell_4608 (by assumption) h
  rcases le_or_gt x 4640 with h | h
  · exact psiOneGrid2_cell_4624 (by assumption) h
  rcases le_or_gt x 4656 with h | h
  · exact psiOneGrid2_cell_4640 (by assumption) h
  rcases le_or_gt x 4672 with h | h
  · exact psiOneGrid2_cell_4656 (by assumption) h
  rcases le_or_gt x 4688 with h | h
  · exact psiOneGrid2_cell_4672 (by assumption) h
  rcases le_or_gt x 4704 with h | h
  · exact psiOneGrid2_cell_4688 (by assumption) h
  rcases le_or_gt x 4720 with h | h
  · exact psiOneGrid2_cell_4704 (by assumption) h
  rcases le_or_gt x 4736 with h | h
  · exact psiOneGrid2_cell_4720 (by assumption) h
  rcases le_or_gt x 4752 with h | h
  · exact psiOneGrid2_cell_4736 (by assumption) h
  rcases le_or_gt x 4768 with h | h
  · exact psiOneGrid2_cell_4752 (by assumption) h
  rcases le_or_gt x 4784 with h | h
  · exact psiOneGrid2_cell_4768 (by assumption) h
  rcases le_or_gt x 4800 with h | h
  · exact psiOneGrid2_cell_4784 (by assumption) h
  rcases le_or_gt x 4816 with h | h
  · exact psiOneGrid2_cell_4800 (by assumption) h
  rcases le_or_gt x 4832 with h | h
  · exact psiOneGrid2_cell_4816 (by assumption) h
  rcases le_or_gt x 4848 with h | h
  · exact psiOneGrid2_cell_4832 (by assumption) h
  exact psiOneGrid2_cell_4848 (by assumption) hx'

theorem psiOneGrid2_block_4864 {x : ℝ} (hx : 4864 < x) (hx' : x ≤ 5120) :
    x / 2 - 2.9 ≤ psiOne x := by
  rcases le_or_gt x 4880 with h | h
  · exact psiOneGrid2_cell_4864 (by assumption) h
  rcases le_or_gt x 4896 with h | h
  · exact psiOneGrid2_cell_4880 (by assumption) h
  rcases le_or_gt x 4912 with h | h
  · exact psiOneGrid2_cell_4896 (by assumption) h
  rcases le_or_gt x 4928 with h | h
  · exact psiOneGrid2_cell_4912 (by assumption) h
  rcases le_or_gt x 4944 with h | h
  · exact psiOneGrid2_cell_4928 (by assumption) h
  rcases le_or_gt x 4960 with h | h
  · exact psiOneGrid2_cell_4944 (by assumption) h
  rcases le_or_gt x 4976 with h | h
  · exact psiOneGrid2_cell_4960 (by assumption) h
  rcases le_or_gt x 4992 with h | h
  · exact psiOneGrid2_cell_4976 (by assumption) h
  rcases le_or_gt x 5008 with h | h
  · exact psiOneGrid2_cell_4992 (by assumption) h
  rcases le_or_gt x 5024 with h | h
  · exact psiOneGrid2_cell_5008 (by assumption) h
  rcases le_or_gt x 5040 with h | h
  · exact psiOneGrid2_cell_5024 (by assumption) h
  rcases le_or_gt x 5056 with h | h
  · exact psiOneGrid2_cell_5040 (by assumption) h
  rcases le_or_gt x 5072 with h | h
  · exact psiOneGrid2_cell_5056 (by assumption) h
  rcases le_or_gt x 5088 with h | h
  · exact psiOneGrid2_cell_5072 (by assumption) h
  rcases le_or_gt x 5104 with h | h
  · exact psiOneGrid2_cell_5088 (by assumption) h
  exact psiOneGrid2_cell_5104 (by assumption) hx'

theorem psiOneGrid2_block_5120 {x : ℝ} (hx : 5120 < x) (hx' : x ≤ 5376) :
    x / 2 - 2.9 ≤ psiOne x := by
  rcases le_or_gt x 5136 with h | h
  · exact psiOneGrid2_cell_5120 (by assumption) h
  rcases le_or_gt x 5152 with h | h
  · exact psiOneGrid2_cell_5136 (by assumption) h
  rcases le_or_gt x 5168 with h | h
  · exact psiOneGrid2_cell_5152 (by assumption) h
  rcases le_or_gt x 5184 with h | h
  · exact psiOneGrid2_cell_5168 (by assumption) h
  rcases le_or_gt x 5200 with h | h
  · exact psiOneGrid2_cell_5184 (by assumption) h
  rcases le_or_gt x 5216 with h | h
  · exact psiOneGrid2_cell_5200 (by assumption) h
  rcases le_or_gt x 5232 with h | h
  · exact psiOneGrid2_cell_5216 (by assumption) h
  rcases le_or_gt x 5248 with h | h
  · exact psiOneGrid2_cell_5232 (by assumption) h
  rcases le_or_gt x 5264 with h | h
  · exact psiOneGrid2_cell_5248 (by assumption) h
  rcases le_or_gt x 5280 with h | h
  · exact psiOneGrid2_cell_5264 (by assumption) h
  rcases le_or_gt x 5296 with h | h
  · exact psiOneGrid2_cell_5280 (by assumption) h
  rcases le_or_gt x 5312 with h | h
  · exact psiOneGrid2_cell_5296 (by assumption) h
  rcases le_or_gt x 5328 with h | h
  · exact psiOneGrid2_cell_5312 (by assumption) h
  rcases le_or_gt x 5344 with h | h
  · exact psiOneGrid2_cell_5328 (by assumption) h
  rcases le_or_gt x 5360 with h | h
  · exact psiOneGrid2_cell_5344 (by assumption) h
  exact psiOneGrid2_cell_5360 (by assumption) hx'

theorem psiOneGrid2_block_5376 {x : ℝ} (hx : 5376 < x) (hx' : x ≤ 5632) :
    x / 2 - 2.9 ≤ psiOne x := by
  rcases le_or_gt x 5392 with h | h
  · exact psiOneGrid2_cell_5376 (by assumption) h
  rcases le_or_gt x 5408 with h | h
  · exact psiOneGrid2_cell_5392 (by assumption) h
  rcases le_or_gt x 5424 with h | h
  · exact psiOneGrid2_cell_5408 (by assumption) h
  rcases le_or_gt x 5440 with h | h
  · exact psiOneGrid2_cell_5424 (by assumption) h
  rcases le_or_gt x 5456 with h | h
  · exact psiOneGrid2_cell_5440 (by assumption) h
  rcases le_or_gt x 5472 with h | h
  · exact psiOneGrid2_cell_5456 (by assumption) h
  rcases le_or_gt x 5488 with h | h
  · exact psiOneGrid2_cell_5472 (by assumption) h
  rcases le_or_gt x 5504 with h | h
  · exact psiOneGrid2_cell_5488 (by assumption) h
  rcases le_or_gt x 5520 with h | h
  · exact psiOneGrid2_cell_5504 (by assumption) h
  rcases le_or_gt x 5536 with h | h
  · exact psiOneGrid2_cell_5520 (by assumption) h
  rcases le_or_gt x 5552 with h | h
  · exact psiOneGrid2_cell_5536 (by assumption) h
  rcases le_or_gt x 5568 with h | h
  · exact psiOneGrid2_cell_5552 (by assumption) h
  rcases le_or_gt x 5584 with h | h
  · exact psiOneGrid2_cell_5568 (by assumption) h
  rcases le_or_gt x 5600 with h | h
  · exact psiOneGrid2_cell_5584 (by assumption) h
  rcases le_or_gt x 5616 with h | h
  · exact psiOneGrid2_cell_5600 (by assumption) h
  exact psiOneGrid2_cell_5616 (by assumption) hx'

theorem psiOneGrid2_block_5632 {x : ℝ} (hx : 5632 < x) (hx' : x ≤ 5888) :
    x / 2 - 2.9 ≤ psiOne x := by
  rcases le_or_gt x 5648 with h | h
  · exact psiOneGrid2_cell_5632 (by assumption) h
  rcases le_or_gt x 5664 with h | h
  · exact psiOneGrid2_cell_5648 (by assumption) h
  rcases le_or_gt x 5680 with h | h
  · exact psiOneGrid2_cell_5664 (by assumption) h
  rcases le_or_gt x 5696 with h | h
  · exact psiOneGrid2_cell_5680 (by assumption) h
  rcases le_or_gt x 5712 with h | h
  · exact psiOneGrid2_cell_5696 (by assumption) h
  rcases le_or_gt x 5728 with h | h
  · exact psiOneGrid2_cell_5712 (by assumption) h
  rcases le_or_gt x 5744 with h | h
  · exact psiOneGrid2_cell_5728 (by assumption) h
  rcases le_or_gt x 5760 with h | h
  · exact psiOneGrid2_cell_5744 (by assumption) h
  rcases le_or_gt x 5776 with h | h
  · exact psiOneGrid2_cell_5760 (by assumption) h
  rcases le_or_gt x 5792 with h | h
  · exact psiOneGrid2_cell_5776 (by assumption) h
  rcases le_or_gt x 5808 with h | h
  · exact psiOneGrid2_cell_5792 (by assumption) h
  rcases le_or_gt x 5824 with h | h
  · exact psiOneGrid2_cell_5808 (by assumption) h
  rcases le_or_gt x 5840 with h | h
  · exact psiOneGrid2_cell_5824 (by assumption) h
  rcases le_or_gt x 5856 with h | h
  · exact psiOneGrid2_cell_5840 (by assumption) h
  rcases le_or_gt x 5872 with h | h
  · exact psiOneGrid2_cell_5856 (by assumption) h
  exact psiOneGrid2_cell_5872 (by assumption) hx'

theorem psiOneGrid2_block_5888 {x : ℝ} (hx : 5888 < x) (hx' : x ≤ 6000) :
    x / 2 - 2.9 ≤ psiOne x := by
  rcases le_or_gt x 5904 with h | h
  · exact psiOneGrid2_cell_5888 (by assumption) h
  rcases le_or_gt x 5920 with h | h
  · exact psiOneGrid2_cell_5904 (by assumption) h
  rcases le_or_gt x 5936 with h | h
  · exact psiOneGrid2_cell_5920 (by assumption) h
  rcases le_or_gt x 5952 with h | h
  · exact psiOneGrid2_cell_5936 (by assumption) h
  rcases le_or_gt x 5968 with h | h
  · exact psiOneGrid2_cell_5952 (by assumption) h
  rcases le_or_gt x 5984 with h | h
  · exact psiOneGrid2_cell_5968 (by assumption) h
  exact psiOneGrid2_cell_5984 (by assumption) hx'

/-- **Combined grid bound.** For `1536 < x ≤ 6000`: `ψ₁(x) ≥ x/2 - 2.9`. -/
theorem psiOne_lower_grid2 {x : ℝ} (hx : 1536 < x) (hx' : x ≤ 6000) : x / 2 - 2.9 ≤ psiOne x := by
  rcases le_or_gt x 1792 with h | h
  · exact psiOneGrid2_block_1536 (by assumption) h
  rcases le_or_gt x 2048 with h | h
  · exact psiOneGrid2_block_1792 (by assumption) h
  rcases le_or_gt x 2304 with h | h
  · exact psiOneGrid2_block_2048 (by assumption) h
  rcases le_or_gt x 2560 with h | h
  · exact psiOneGrid2_block_2304 (by assumption) h
  rcases le_or_gt x 2816 with h | h
  · exact psiOneGrid2_block_2560 (by assumption) h
  rcases le_or_gt x 3072 with h | h
  · exact psiOneGrid2_block_2816 (by assumption) h
  rcases le_or_gt x 3328 with h | h
  · exact psiOneGrid2_block_3072 (by assumption) h
  rcases le_or_gt x 3584 with h | h
  · exact psiOneGrid2_block_3328 (by assumption) h
  rcases le_or_gt x 3840 with h | h
  · exact psiOneGrid2_block_3584 (by assumption) h
  rcases le_or_gt x 4096 with h | h
  · exact psiOneGrid2_block_3840 (by assumption) h
  rcases le_or_gt x 4352 with h | h
  · exact psiOneGrid2_block_4096 (by assumption) h
  rcases le_or_gt x 4608 with h | h
  · exact psiOneGrid2_block_4352 (by assumption) h
  rcases le_or_gt x 4864 with h | h
  · exact psiOneGrid2_block_4608 (by assumption) h
  rcases le_or_gt x 5120 with h | h
  · exact psiOneGrid2_block_4864 (by assumption) h
  rcases le_or_gt x 5376 with h | h
  · exact psiOneGrid2_block_5120 (by assumption) h
  rcases le_or_gt x 5632 with h | h
  · exact psiOneGrid2_block_5376 (by assumption) h
  rcases le_or_gt x 5888 with h | h
  · exact psiOneGrid2_block_5632 (by assumption) h
  exact psiOneGrid2_block_5888 (by assumption) hx'

/-
Generator (`python3 gen2.py 16 2.9 > ConstPsiOneGrid2.lean`, with this file's header in `head.lean`):

# Generator for lean/DetPrimality/Bach/ConstPsiOneGrid2.lean
# usage: python3 gen2.py [STEP] > out
import math, sys
from fractions import Fraction as F
LO, HI = 1536, 6000
STEP = int(sys.argv[1]) if len(sys.argv) > 1 else 16
N = HI + 2
# psiAcc (floating-point product, rounded down)
T = 2**9216
Ls = [1]; Ps = [1]; Es = [0]
for n in range(N):
    L, P, E = Ls[-1], Ps[-1], Es[-1]
    Q = P * L
    if Q >= T: Q >>= 8704; E += 8704
    Ls.append(L * (n + 1) // math.gcd(L, n + 1)); Ps.append(Q); Es.append(E)
# true Lambda
lam = [0.0] * (N + 1)
for p in range(2, N + 1):
    if all(p % d for d in range(2, int(p**0.5) + 1)):
        q = p
        while q <= N:
            lam[q] = math.log(p); q *= p
cpsi = [0.0]; cm = [0.0]
for m in range(1, N + 1):
    cpsi.append(cpsi[-1] + lam[m]); cm.append(cm[-1] + m * lam[m])
def psi1(x):
    k = math.ceil(x) - 1
    return cpsi[k] - cm[k] / x
l = F(6931471803, 10**10)
grid = list(range(LO, HI + 1, STEP))
if grid[-1] != HI: grid.append(HI)
rows = []
for K in grid[:-1]:
    e = Es[K]; m = (Ps[K]**8).bit_length() - 1; A = 8 * e + m; B = (Ls[K]**8).bit_length() - 1
    a = F(math.floor(l * B / 8 * 1000), 1000)
    c = math.ceil(l * F(K * B - A, 8))
    rows.append((K, (e, m), B, a, c))
E = 0; wabs = 0; wrel = 0; tmin = 1e9
cellE = []
for (K, A, B, a, c), K2 in zip(rows, grid[1:]):
    e = max(F(x, 2) - (a - F(c, x)) for x in (K, K2))
    cellE.append(e); E = max(E, e)
    for i in range(1, 65):
        x = K + (K2 - K) * i / 64
        lb = float(a) - c / x; t = psi1(x)
        assert lb <= t
        wabs = max(wabs, t - lb); wrel = max(wrel, (t - lb) / t); tmin = min(tmin, t - x / 2)
sys.stderr.write(f"E {float(E)} worst abs {wabs} rel {wrel} true min psi1-x/2 {tmin}\n")
import pickle
pickle.dump((grid, rows, [float(e) for e in cellE]), open(f'rows{STEP}.pkl', 'wb'))

# ---- emit Lean ----
EDEC = sys.argv[2] if len(sys.argv) > 2 else None
if EDEC:
    assert F(EDEC) >= E
    LIMIT = int(sys.argv[3]) if len(sys.argv) > 3 else None
    def dec(a): return f"{float(a):.3f}"
    out = [open('head.lean').read().replace('@E@', EDEC)]
    rr = list(zip(rows, grid[1:]))
    if LIMIT: rr = rr[:1] + rr[-LIMIT:]
    for (K, A, B, a, c), K2 in rr:
        out.append(f"""theorem psiOneGrid2_cert_{K} :
    {A[0]} ≤ (psiAcc {K}).2.2 ∧ 2 ^ {A[1]} ≤ (psiAcc {K}).2.1 ^ 8 ∧ 2 ^ {B} ≤ (psiAcc {K}).1 ^ 8 := by
  decide +kernel

/ -- For `x > {K}`: `{dec(a)} x - {c} ≤ x ψ₁(x)` (sharp on `({K}, {K2}]`). - /
theorem psiOne_lower_grid2_mul_{K} {{x : ℝ}} (hx : {K} < x) : {dec(a)} * x - {c} ≤ x * psiOne x :=
  psiOneGrid2_mul psiOneGrid2_cert_{K}.1 psiOneGrid2_cert_{K}.2.1 psiOneGrid2_cert_{K}.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

/ -- For `x > {K}`: `ψ₁(x) ≥ {dec(a)} - {c}/x` (sharp on `({K}, {K2}]`). - /
theorem psiOne_lower_grid2_{K} {{x : ℝ}} (hx : {K} < x) : {dec(a)} - {c} / x ≤ psiOne x :=
  psiOneGrid2_div psiOneGrid2_cert_{K}.1 psiOneGrid2_cert_{K}.2.1 psiOneGrid2_cert_{K}.2.2
    (by norm_num) (by norm_num) (by push_cast; exact hx)

theorem psiOneGrid2_cell_{K} {{x : ℝ}} (hx : {K} < x) (hx' : x ≤ {K2}) :
    x / 2 - {EDEC} ≤ psiOne x :=
  psiOneGrid2_cell (psiOne_lower_grid2_mul_{K} hx) (by norm_num) (by norm_num) (by norm_num) hx hx'
""")
    if not LIMIT:
        G = 16
        groups = [rr[i:i + G] for i in range(0, len(rr), G)]
        for g in groups:
            lo = g[0][0][0]; hi = g[-1][1]
            s = f"theorem psiOneGrid2_block_{lo} {{x : ℝ}} (hx : {lo} < x) (hx' : x ≤ {hi}) :\n    x / 2 - {EDEC} ≤ psiOne x := by\n"
            for (r, K2) in g[:-1]:
                s += f"  rcases le_or_gt x {K2} with h | h\n  · exact psiOneGrid2_cell_{r[0]} (by assumption) h\n"
            s += f"  exact psiOneGrid2_cell_{g[-1][0][0]} (by assumption) hx'\n"
            out.append(s)
        s = f"/ -- **Combined grid bound.** For `{LO} < x ≤ {HI}`: `ψ₁(x) ≥ x/2 - {EDEC}`. - /\ntheorem psiOne_lower_grid2 {{x : ℝ}} (hx : {LO} < x) (hx' : x ≤ {HI}) : x / 2 - {EDEC} ≤ psiOne x := by\n"
        for g in groups[:-1]:
            s += f"  rcases le_or_gt x {g[-1][1]} with h | h\n  · exact psiOneGrid2_block_{g[0][0][0]} (by assumption) h\n"
        s += f"  exact psiOneGrid2_block_{groups[-1][0][0][0]} (by assumption) hx'\n"
        out.append(s)
        out.append("/ -\nGenerator (`python3 gen2.py 16 2.9 > ConstPsiOneGrid2.lean`, with this file's header in `head.lean`):\n\n"
                   + open('gen2.py').read().replace('/ -', '/ -').replace('- /', '- /') + "- /\n")
    out.append("end DetPrimality.Bach")
    print("\n".join(out))
-/

end DetPrimality.Bach
