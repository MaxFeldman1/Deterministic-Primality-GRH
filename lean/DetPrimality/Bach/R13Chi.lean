import DetPrimality.Bach.R13Defs
import DetPrimality.Bach.R11ChiBound
import DetPrimality.Bach.R11ZeroSumSeries

/-!
# Round 13, (P2): the χ explicit formula of every order `j ≥ 3` (`R13ChiExplicit`)

`Φ_{χ,j}(y) = j! · P_j[L(f,·)](y)` and the Hadamard decomposition `r11Chi_decomp` give
`Φ_{χ,j}(y) = -L'/L(3/2) log^j y - j! ∑_k Q(s_k) - j! ∑_ρ m_ρ Q(ρ+1/2)` with
`Q(w) = y^w / w^{j+1} - N_j(w, log y)`,
`N_j(w, L) = ∑_{i<j} (L^i/i!) w^{i-j-1} + (L^j/j!) · 2/(w(2-w))` (`r13C_N`).
For `|w| ≥ 1/2`, `|w| ≤ |2-w|`: `|N_j(w,L)| ≤ (j 2^j + 2)(1+L)^j / |w|²`.
Zeros: `∑ m_ρ/|ρ+1/2|² = Z₂(χ) ≤ ½ log q + 2`; trivial zeros: `y^{s_k} ≤ √y`.
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## Perron representation -/

theorem r13C_Phi_eq_perron {N : ℕ} (χ : DirichletCharacter ℂ N) {j : ℕ} (hj : 1 ≤ j) {y : ℝ}
    (hy : 0 < y) :
    r13Phi χ j y = (j.factorial : ℂ) * r11Chi_perron j (LSeries (r11Chi_coeff χ)) y := by
  rw [r11Chi_perron_LSeries hj (r11Chi_summable_coeff χ) hy, Finset.mul_sum]
  unfold r13Phi
  refine Finset.sum_congr rfl fun n _ => ?_
  have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have key : ∀ a : ℂ, (j.factorial : ℂ) * (a / (j.factorial : ℂ)) = a := fun a => by
    rw [mul_comm, div_mul_cancel₀ _ hf]
  rw [key]
  simp only [r11Chi_coeff]
  push_cast
  ring

/-! ## One regularised pole -/

/-- The non-oscillating part of `P_j[1/(s-w) - 1/(2-w)]`. -/
noncomputable def r13C_N (j : ℕ) (w : ℂ) (L : ℝ) : ℂ :=
  ∑ i ∈ Finset.range j, (L : ℂ) ^ i / (i.factorial : ℂ) / w ^ (j + 1 - i)
    + (L : ℂ) ^ j / (j.factorial : ℂ) * (2 / (w * (2 - w)))

theorem r13C_perron_pole {j : ℕ} (hj : 1 ≤ j) {w : ℂ} (hw : w.re < 2) (hw0 : w ≠ 0) {y : ℝ}
    (hy : 1 ≤ y) :
    r11Chi_perron j (fun s => 1 / (s - w) - 1 / (2 - w)) y
      = (y : ℂ) ^ w / w ^ (j + 1) - r13C_N j w (Real.log y) := by
  have hy0 : 0 < y := by linarith
  have h2w : (2 : ℂ) - w ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [Complex.sub_re] at this
    norm_num at this
    linarith
  have e : (2 : ℂ) / (w * (2 - w)) = 1 / w + 1 / (2 - w) := by
    rw [div_add_div _ _ hw0 h2w]
    congr 1
    ring
  rw [r11Chi_perron_sub (r11Chi_vi_inv_sub hj hw) (r11Chi_vi_const hj _) hy0,
    r11Chi_perron_inv_sub hj hw hw0 hy, r11Chi_perron_const, r11Chi_perron_one hj hy,
    Finset.sum_range_succ, show j + 1 - j = 1 by omega, pow_one]
  unfold r13C_N
  rw [e]
  ring

theorem r13C_inv_pow_le {x : ℝ} (hx : 1 / 2 ≤ x) {j n : ℕ} (hn : 2 ≤ n) (hnj : n ≤ j + 2) :
    1 / x ^ n ≤ 2 ^ j * (1 / x ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hsplit : x ^ n = x ^ 2 * x ^ (n - 2) := by
    rw [← pow_add]; congr 1; omega
  have h1 : (1 : ℝ) ≤ (2 * x) ^ (n - 2) := one_le_pow₀ (by linarith)
  have h2 : (2 : ℝ) ^ (n - 2) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : (1 : ℝ) ≤ 2 ^ j * x ^ (n - 2) := by
    rw [mul_pow] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))
  have hne : x ^ 2 ≠ 0 := by positivity
  rw [div_le_iff₀ (by positivity), hsplit,
    show (2 : ℝ) ^ j * (1 / x ^ 2) * (x ^ 2 * x ^ (n - 2))
      = 2 ^ j * x ^ (n - 2) * (1 / x ^ 2 * x ^ 2) by ring,
    one_div_mul_cancel hne, mul_one]
  exact h3

theorem r13C_norm_N_le (j : ℕ) {w : ℂ} (hw : 1 / 2 ≤ ‖w‖) (hw2 : ‖w‖ ≤ ‖2 - w‖) {L : ℝ}
    (hL : 0 ≤ L) :
    ‖r13C_N j w L‖ ≤ ((j : ℝ) * 2 ^ j + 2) * (1 + L) ^ j * (1 / ‖w‖ ^ 2) := by
  have hwpos : 0 < ‖w‖ := by linarith
  have hM : ∀ i, i ≤ j → L ^ i ≤ (1 + L) ^ j := fun i hi =>
    (pow_le_pow_left₀ hL (by linarith) i).trans (pow_le_pow_right₀ (by linarith) hi)
  have hfr : ∀ i, i ≤ j → L ^ i / (i.factorial : ℝ) ≤ (1 + L) ^ j := fun i hi =>
    (div_le_self (pow_nonneg hL i) (by exact_mod_cast i.factorial_pos)).trans (hM i hi)
  have hterm : ∀ i ∈ Finset.range j,
      ‖(L : ℂ) ^ i / (i.factorial : ℂ) / w ^ (j + 1 - i)‖
        ≤ 2 ^ j * (1 + L) ^ j * (1 / ‖w‖ ^ 2) := by
    intro i hi
    have hi' : i < j := Finset.mem_range.mp hi
    rw [norm_div, norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hL,
      Complex.norm_natCast, div_eq_mul_one_div]
    have h1 := hfr i hi'.le
    have h2 := r13C_inv_pow_le hw (j := j) (n := j + 1 - i) (by omega) (by omega)
    have h0 : 0 ≤ L ^ i / (i.factorial : ℝ) := by positivity
    calc L ^ i / (i.factorial : ℝ) * (1 / ‖w‖ ^ (j + 1 - i))
        ≤ (1 + L) ^ j * (2 ^ j * (1 / ‖w‖ ^ 2)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2 ^ j * (1 + L) ^ j * (1 / ‖w‖ ^ 2) := by ring
  have hlast : ‖(L : ℂ) ^ j / (j.factorial : ℂ) * (2 / (w * (2 - w)))‖
      ≤ 2 * (1 + L) ^ j * (1 / ‖w‖ ^ 2) := by
    have hn2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hL,
      Complex.norm_natCast, norm_div, norm_mul, hn2]
    have h1 := hfr j le_rfl
    have h2 : 2 / (‖w‖ * ‖2 - w‖) ≤ 2 * (1 / ‖w‖ ^ 2) := by
      rw [show 2 * (1 / ‖w‖ ^ 2) = 2 / (‖w‖ * ‖w‖) by rw [sq]; ring]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left hw2 hwpos.le)
    calc L ^ j / (j.factorial : ℝ) * (2 / (‖w‖ * ‖2 - w‖))
        ≤ (1 + L) ^ j * (2 * (1 / ‖w‖ ^ 2)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2 * (1 + L) ^ j * (1 / ‖w‖ ^ 2) := by ring
  unfold r13C_N
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (j : ℝ) * (2 ^ j * (1 + L) ^ j * (1 / ‖w‖ ^ 2)) + 2 * (1 + L) ^ j * (1 / ‖w‖ ^ 2) :=
        add_le_add hsum hlast
    _ = _ := by ring

/-! ## Trivial zeros -/

theorem r13C_gamma_term_le {j : ℕ} (hj : 1 ≤ j) (a k : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    ‖(-1 : ℂ) * r11Chi_perron j (fun s => 1 / (s - ((r11Chi_r a k : ℝ) : ℂ))
        - 1 / (2 - ((r11Chi_r a k : ℝ) : ℂ))) y‖
      ≤ (2 ^ j * Real.sqrt y + ((j : ℝ) * 2 ^ j + 2) * (1 + Real.log y) ^ j)
        * (1 / r11Chi_r a k ^ 2) := by
  set r := r11Chi_r a k with hr
  have hy0 : 0 < y := by linarith
  have hr0 : r ≠ 0 := r11Chi_r_ne a k
  have hrle : r ≤ 1 / 2 := by
    have := r11Chi_r_le a k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have habs : 1 / 2 ≤ |r| := r11Chi_half_le_abs_r a k
  have hnr : ‖(r : ℂ)‖ = |r| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hn2 : ‖(2 : ℂ) - (r : ℂ)‖ = 2 - r := by
    rw [show (2 : ℂ) - (r : ℂ) = ((2 - r : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hsq : |r| ^ 2 = r ^ 2 := sq_abs r
  rw [r13C_perron_pole hj (w := (r : ℂ)) (by rw [Complex.ofReal_re]; linarith)
    (by exact_mod_cast hr0) hy, neg_one_mul, norm_neg]
  have hN := r13C_norm_N_le j (w := (r : ℂ)) (by rw [hnr]; exact habs)
    (by rw [hnr, hn2]; exact abs_le.mpr ⟨by linarith, by linarith⟩) (Real.log_nonneg hy)
  rw [hnr, hsq] at hN
  have hosc : ‖(y : ℂ) ^ (r : ℂ) / (r : ℂ) ^ (j + 1)‖ ≤ 2 ^ j * Real.sqrt y * (1 / r ^ 2) := by
    rw [norm_div, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.ofReal_re, hnr,
      div_eq_mul_one_div]
    have h1 : y ^ r ≤ Real.sqrt y := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hy hrle
    have h2 := r13C_inv_pow_le habs (j := j) (n := j + 1) (by omega) (by omega)
    rw [hsq] at h2
    calc y ^ r * (1 / |r| ^ (j + 1)) ≤ Real.sqrt y * (2 ^ j * (1 / r ^ 2)) :=
          mul_le_mul h1 h2 (by positivity) (Real.sqrt_nonneg y)
      _ = 2 ^ j * Real.sqrt y * (1 / r ^ 2) := by ring
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ 2 ^ j * Real.sqrt y * (1 / r ^ 2)
        + ((j : ℝ) * 2 ^ j + 2) * (1 + Real.log y) ^ j * (1 / r ^ 2) := add_le_add hosc hN
    _ = _ := by ring

theorem r13C_gamma_le {j : ℕ} (hj : 1 ≤ j) (a : ℕ) {y : ℝ} (hy : 1 ≤ y) {P : ℂ}
    (h : HasSum (fun k : ℕ => (-1 : ℂ) * r11Chi_perron j (fun s =>
        1 / (s - ((r11Chi_r a k : ℝ) : ℂ)) - 1 / (2 - ((r11Chi_r a k : ℝ) : ℂ))) y) P) :
    ‖P‖ ≤ (2 ^ j * Real.sqrt y + ((j : ℝ) * 2 ^ j + 2) * (1 + Real.log y) ^ j)
      * ∑' k : ℕ, 1 / r11Chi_r a k ^ 2 :=
  h.norm_le_of_bounded ((r11Chi_summable_inv_r_pow a (j := 2) le_rfl).hasSum.mul_left _)
    (fun k => r13C_gamma_term_le hj a k hy)

/-! ## Non-trivial zeros -/

theorem r13C_summable_Z2 {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) :
    Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_) hS
  by_cases h0 : zeroOrd χ ρ = 0
  · simp [h0]
  · have hre := (zeroOrd_strip h0).1
    have hρ : 0 < ‖ρ‖ := norm_pos_iff.mpr (ne_zero_of_re_pos hre)
    have h1 := r11Chi_norm_add_half_ge hre
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    exact pow_le_pow_left₀ hρ.le h1 2

theorem r13C_zero_term (hGRH : DirichletLZerosOnLine) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (ρ : ℂ) {j : ℕ} (hj : 1 ≤ j) {y : ℝ} (hy : 1 ≤ y) :
    (-(zeroOrd χ ρ : ℂ)) * r11Chi_perron j (fun s =>
          1 / (s - (ρ + 1 / 2)) - 1 / (2 - (ρ + 1 / 2))) y
        + (zeroOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2) ^ (j + 1)
      = (zeroOrd χ ρ : ℂ) * r13C_N j (ρ + 1 / 2) (Real.log y) ∧
    ‖(zeroOrd χ ρ : ℂ) * r13C_N j (ρ + 1 / 2) (Real.log y)‖
      ≤ ((j : ℝ) * 2 ^ j + 2) * (1 + Real.log y) ^ j
        * ((zeroOrd χ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ 2) ∧
    ‖(zeroOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2) ^ (j + 1)‖
      ≤ y * ((zeroOrd χ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ 2) := by
  by_cases h0 : zeroOrd χ ρ = 0
  · simp [h0]
  obtain ⟨hre, hconj⟩ := r11Chi_zero_geom hGRH χ h0
  have hy0 : 0 < y := by linarith
  have hm0 : (0 : ℝ) ≤ (zeroOrd χ ρ : ℝ) := Nat.cast_nonneg _
  have h2w : (2 : ℂ) - (ρ + 1 / 2) = (starRingEnd ℂ) (ρ + 1 / 2) := by
    rw [← hconj]; ring
  generalize ρ + 1 / 2 = w at hre h2w ⊢
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hre; simp at hre
  have hw1 : 1 ≤ ‖w‖ := by
    have := Complex.re_le_norm w
    rw [hre] at this; exact this
  have hw2 : ‖w‖ ≤ ‖2 - w‖ := by rw [h2w, Complex.norm_conj]
  refine ⟨?_, ?_, ?_⟩
  · rw [r13C_perron_pole hj (by rw [hre]; norm_num) hw0 hy]
    ring
  · rw [norm_mul, Complex.norm_natCast]
    have hN := r13C_norm_N_le j (w := w) (by linarith) hw2 (Real.log_nonneg hy)
    calc (zeroOrd χ ρ : ℝ) * ‖r13C_N j w (Real.log y)‖
        ≤ (zeroOrd χ ρ : ℝ) * (((j : ℝ) * 2 ^ j + 2) * (1 + Real.log y) ^ j * (1 / ‖w‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hN hm0
      _ = _ := by ring
  · rw [norm_div, norm_mul, Complex.norm_natCast, norm_pow,
      Complex.norm_cpow_eq_rpow_re_of_pos hy0, hre, Real.rpow_one,
      show y * ((zeroOrd χ ρ : ℝ) / ‖w‖ ^ 2) = (zeroOrd χ ρ : ℝ) * y / ‖w‖ ^ 2 by ring]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_right₀ hw1 (by omega))

theorem r13C_Z2_le (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    r11Z χ 2 ≤ Real.log q / 2 + 2 := by
  rw [r11Zs_Z2_eq χ hGRH, r11Zs_chi_S1 χ hχ hχ1]
  have h1 := norm_logDeriv_LFunction_three_halves_le_sharp χ
  have h2 := Complex.re_le_norm (deriv (LFunction χ) (3 / 2) / LFunction χ (3 / 2))
  have h3 := re_logDeriv_gammaFactor_three_halves_le_sharp χ
  linarith

/-! ## The explicit formula of order `j` -/

theorem r13C_Phi_formula {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (hH : HadamardLogDeriv χ) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)
    {j : ℕ} (hj : 3 ≤ j) {y : ℝ} (hy : 1 ≤ y) :
    ∃ PA PB : ℂ,
      HasSum (fun k : ℕ => (-1 : ℂ) * r11Chi_perron j (fun s =>
        1 / (s - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))
          - 1 / (2 - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))) y) PA ∧
      HasSum (fun ρ : ℂ => (-(zeroOrd χ ρ : ℂ)) * r11Chi_perron j (fun s =>
        1 / (s - (ρ + 1 / 2)) - 1 / (2 - (ρ + 1 / 2))) y) PB ∧
      r13Phi χ j y = -(deriv (LFunction χ) (3 / 2) / LFunction χ (3 / 2)) * (Real.log y : ℂ) ^ j
        + (j.factorial : ℂ) * PA + (j.factorial : ℂ) * PB := by
  have hj1 : 1 ≤ j := by omega
  have hy0 : 0 < y := by linarith
  have hwk : ∀ k : ℕ, (-1 : ℂ) ≠ 0 → (((r11Chi_r (gammaShift χ) k : ℝ) : ℂ)).re ≤ 3 / 2 := by
    intro k _
    rw [Complex.ofReal_re]
    have := r11Chi_r_le (gammaShift χ) k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hwρ : ∀ ρ : ℂ, (-(zeroOrd χ ρ : ℂ)) ≠ 0 → (ρ + 1 / 2).re ≤ 3 / 2 := by
    intro ρ h
    have h0 : zeroOrd χ ρ ≠ 0 := by
      intro h0; apply h; simp [h0]
    have := (zeroOrd_strip h0).2
    have e1 : (ρ + 1 / 2).re = ρ.re + 1 / 2 := by simp
    rw [e1]; linarith
  have hsk := r11Chi_summable_gamma_weight (gammaShift χ)
  have hsρ := r11Chi_summable_zero_weight χ hS
  refine ⟨_, _, r11Chi_perron_hasSum_poles hj _ _ hwk hsk hy0,
    r11Chi_perron_hasSum_poles hj _ _ hwρ hsρ hy0, ?_⟩
  have hviA := r11Chi_vi_poles hj _ _ hwk hsk
  have hviB := r11Chi_vi_poles hj _ _ hwρ hsρ
  set c0 : ℂ := -(deriv (LFunction χ) (3 / 2) / LFunction χ (3 / 2)) with hc0
  have hvic : VerticalIntegrable (fun s : ℂ => c0 / s ^ (j + 1)) 2 := r11Chi_vi_const hj1 c0
  have hviCA : VerticalIntegrable (fun s : ℂ => (c0 + ∑' k : ℕ, (-1 : ℂ)
      * (1 / (s - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))
        - 1 / (2 - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ)))) / s ^ (j + 1)) 2 := by
    have h := Integrable.add hvic hviA
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, add_div]
  have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  rw [r13C_Phi_eq_perron χ hj1 hy0,
    r11Chi_perron_congr_line (g := fun s => (c0 + ∑' k : ℕ, (-1 : ℂ)
      * (1 / (s - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))
        - 1 / (2 - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))))
      + ∑' ρ : ℂ, (-(zeroOrd χ ρ : ℂ)) * (1 / (s - (ρ + 1 / 2)) - 1 / (2 - (ρ + 1 / 2))))
      (fun t => r11Chi_decomp χ hχ1 hH hS (by rw [line_re]; norm_num)),
    r11Chi_perron_add hviCA hviB hy0, r11Chi_perron_add hvic hviA hy0, r11Chi_perron_const,
    r11Chi_perron_one hj1 hy, mul_add, mul_add,
    show (j.factorial : ℂ) * (c0 * ((Real.log y : ℂ) ^ j / (j.factorial : ℂ)))
      = c0 * (Real.log y : ℂ) ^ j by
        rw [mul_left_comm, mul_comm (j.factorial : ℂ), div_mul_cancel₀ _ hf]]

/-! ## (P2) -/

/-- **(P2)** `R13ChiExplicit`. -/
theorem r13C_main : R13ChiExplicit := by
  intro hGRH j hj
  have hj1 : 1 ≤ j := by omega
  set K : ℝ := (j : ℝ) * 2 ^ j + 2 with hK
  set F : ℝ := (j.factorial : ℝ) with hF
  set G0 : ℝ := ∑' k : ℕ, 1 / r11Chi_r 0 k ^ 2 with hG0
  set G1 : ℝ := ∑' k : ℕ, 1 / r11Chi_r 1 k ^ 2 with hG1
  have hK0 : 0 ≤ K := by positivity
  have hF0 : 0 ≤ F := by positivity
  have hG00 : 0 ≤ G0 := tsum_nonneg fun k => by positivity
  have hG10 : 0 ≤ G1 := tsum_nonneg fun k => by positivity
  refine ⟨2 + F * 2 ^ j * (G0 + G1) + F * K * (G0 + G1) + 2 * F * K, ?_⟩
  intro q _ χ hχ hχ1 y hy
  have hy0 : 0 < y := by linarith
  have hGr := growth_completedLFunction χ hχ1
  have hH := hadamardLogDeriv_of_growth χ hχ hχ1 hGr
  have hS := summable_zeroOrd_div_normSq_proof χ hχ hχ1 hGr
  obtain ⟨PA, PB, hA, hB, hΦ⟩ := r13C_Phi_formula χ hχ1 hH hS hj hy
  have hZs := r13C_summable_Z2 χ hS
  have hT : Summable fun ρ : ℂ =>
      (zeroOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2) ^ (j + 1) :=
    Summable.of_norm_bounded (hZs.mul_left y) fun ρ => (r13C_zero_term hGRH χ ρ hj1 hy).2.2
  set T : ℂ := ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2) ^ (j + 1)
    with hTdef
  set L := Real.log y with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg hy
  set M : ℝ := (1 + L) ^ j with hM
  have hM1 : 1 ≤ M := one_le_pow₀ (by linarith)
  have hZ2 : r11Z χ 2 = ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ 2 := rfl
  have nB : ‖PB + T‖ ≤ K * M * r11Z χ 2 := by
    rw [hZ2]
    refine (hB.add hT.hasSum).norm_le_of_bounded (hZs.hasSum.mul_left _) fun ρ => ?_
    have z := r13C_zero_term hGRH χ ρ hj1 hy
    calc _ = ‖(zeroOrd χ ρ : ℂ) * r13C_N j (ρ + 1 / 2) (Real.log y)‖ := by rw [← z.1]
      _ ≤ _ := z.2.1
  have nA : ‖PA‖ ≤ (2 ^ j * Real.sqrt y + K * M)
      * ∑' k : ℕ, 1 / r11Chi_r (gammaShift χ) k ^ 2 := r13C_gamma_le hj1 (gammaShift χ) hy hA
  have hGa0 : 0 ≤ ∑' k : ℕ, 1 / r11Chi_r (gammaShift χ) k ^ 2 :=
    tsum_nonneg fun k => by positivity
  have hGa : ∑' k : ℕ, 1 / r11Chi_r (gammaShift χ) k ^ 2 ≤ G0 + G1 := by
    rcases gammaShift_cases χ with ha | ha <;> rw [ha] <;> linarith
  generalize ∑' k : ℕ, 1 / r11Chi_r (gammaShift χ) k ^ 2 = Ga at nA hGa0 hGa
  have hZle := r13C_Z2_le hGRH χ hχ hχ1
  have hlq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hc0 := norm_logDeriv_LFunction_three_halves_le_sharp χ
  have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hLj : L ^ j ≤ M := pow_le_pow_left₀ hL0 (by linarith) j
  have e : r13Phi χ j y + (j.factorial : ℂ) * T
      = -(deriv (LFunction χ) (3 / 2) / LFunction χ (3 / 2)) * (L : ℂ) ^ j
        + (j.factorial : ℂ) * PA + (j.factorial : ℂ) * (PB + T) := by
    rw [hΦ]; ring
  rw [e]
  have hn : ‖-(deriv (LFunction χ) (3 / 2) / LFunction χ (3 / 2)) * (L : ℂ) ^ j
        + (j.factorial : ℂ) * PA + (j.factorial : ℂ) * (PB + T)‖
      ≤ ‖deriv (LFunction χ) (3 / 2) / LFunction χ (3 / 2)‖ * L ^ j
        + F * ‖PA‖ + F * ‖PB + T‖ := by
    refine (norm_add₃_le).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hL0, Complex.norm_natCast]
  refine hn.trans ?_
  generalize ‖deriv (LFunction χ) (3 / 2) / LFunction χ (3 / 2)‖ = c at hc0
  generalize ‖PA‖ = a at nA
  generalize ‖PB + T‖ = b at nB
  generalize r11Z χ 2 = Z at nB hZle
  generalize Real.log q = lq at hZle hlq
  generalize Real.sqrt y = s at nA hs0
  generalize G0 + G1 = G at hGa
  have hG0' : 0 ≤ G := hGa0.trans hGa
  clear_value M K F
  norm_num at hc0
  -- W = (lq + 1) * M
  have hW : M ≤ (lq + 1) * M := by nlinarith
  have t1 : c * L ^ j ≤ 2 * ((lq + 1) * M) := by
    have : c * L ^ j ≤ 2 * M :=
      mul_le_mul (by linarith) hLj (by positivity) (by norm_num)
    linarith
  have hKM : 0 ≤ K * M := by positivity
  have t2 : F * a ≤ F * ((2 ^ j * s + K * ((lq + 1) * M)) * G) := by
    refine mul_le_mul_of_nonneg_left (nA.trans ?_) hF0
    refine mul_le_mul ?_ hGa hGa0 (by positivity)
    have := mul_le_mul_of_nonneg_left hW hK0
    linarith
  have t3 : F * b ≤ F * (K * (2 * ((lq + 1) * M))) := by
    refine mul_le_mul_of_nonneg_left (nB.trans ?_) hF0
    have h1 : Z ≤ 2 * (lq + 1) := by linarith
    have := mul_le_mul_of_nonneg_left h1 hKM
    nlinarith
  have hW0 : 0 ≤ (lq + 1) * M := by positivity
  have r1 : 0 ≤ F * 2 ^ j * G * ((lq + 1) * M) := by positivity
  have r2 : 0 ≤ F * K * G * s := by positivity
  have r3 : 0 ≤ F * K * s := by positivity
  nlinarith [t1, t2, t3, r1, r2, r3, hs0, hW0]

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r13C_main
