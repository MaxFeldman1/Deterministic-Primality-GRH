import DetPrimality.Bach.R11ChiDefs
import DetPrimality.Bach.ExplicitZeros
import DetPrimality.Bach.HadamardL

/-!
# Round 11, Lemma 3: termwise differentiation of the Hadamard expansion at `3/2`

* `r11Chi_pole_hasDerivAt`, `r11Chi_pole_hasDerivAt_zero` : generic termwise differentiation of
  `∑ c_i/(z-a_i)^n` and `∑ c_i (1/(z-a_i) - 1/(b-a_i))`;
* `r11Chi_zeroPow_eq` : for `k = 1, 2, 3`,
  `∑_ρ m_ρ/(3/2-ρ)^{k+1} = -∑_i 1/(3/2+m_i)^{k+1} - (1/k!) ∑_n χ(n)Λ(n) log^k n · n^{-3/2}`;
* `r11Chi_norm_LSeries_logMul_le` : the last Dirichlet series has norm `≤ F_k`.
-/

open Complex DirichletCharacter Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## Generic termwise differentiation -/

section Generic

variable {ι : Type*}

/-- Poles `a i` with coefficients `c i`, uniformly away from the open set `U`. -/
structure r11Chi_PoleHyp (c a : ι → ℂ) (u : ι → ℝ) (U : Set ℂ) : Prop where
  isOpen : IsOpen U
  summable : Summable u
  nonneg : ∀ i, 0 ≤ u i
  far : ∀ i, c i ≠ 0 → ∀ z ∈ U, 1 / 4 ≤ ‖z - a i‖
  bound : ∀ i, c i ≠ 0 → ∀ z ∈ U, ‖c i‖ / ‖z - a i‖ ^ 2 ≤ u i

variable {c a : ι → ℂ} {u : ι → ℝ} {U : Set ℂ}

theorem r11Chi_pole_norm_le (h : r11Chi_PoleHyp c a u U) (m : ℕ) (i : ι) {z : ℂ} (hz : z ∈ U) :
    ‖c i / (z - a i) ^ (m + 2)‖ ≤ 4 ^ m * u i := by
  by_cases hc : c i = 0
  · rw [hc, zero_div, norm_zero]
    exact mul_nonneg (by positivity) (h.nonneg i)
  · have hx := h.far i hc z hz
    have hb := h.bound i hc z hz
    have hx0 : 0 < ‖z - a i‖ := by linarith
    rw [norm_div, norm_pow, pow_add]
    have h1 : (1 : ℝ) ≤ 4 ^ m * ‖z - a i‖ ^ m := by
      rw [← mul_pow]; exact one_le_pow₀ (by linarith)
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hb
    calc ‖c i‖ ≤ u i * ‖z - a i‖ ^ 2 := hb
      _ ≤ (u i * ‖z - a i‖ ^ 2) * (4 ^ m * ‖z - a i‖ ^ m) :=
        le_mul_of_one_le_right (mul_nonneg (h.nonneg i) (by positivity)) h1
      _ = 4 ^ m * u i * (‖z - a i‖ ^ m * ‖z - a i‖ ^ 2) := by ring

theorem r11Chi_pole_term_hasDerivAt (c a z : ℂ) (m : ℕ) (hz : z - a ≠ 0) :
    HasDerivAt (fun w : ℂ => c / (w - a) ^ (m + 2))
      (-((m : ℂ) + 2) * (c / (z - a) ^ (m + 3))) z := by
  have h0 : HasDerivAt (fun w : ℂ => w - a) 1 z := (hasDerivAt_id z).sub_const a
  have h1 : HasDerivAt (fun w : ℂ => (w - a) ^ (m + 2))
      (((m + 2 : ℕ) : ℂ) * (z - a) ^ (m + 1) * 1) z := h0.fun_pow (m + 2)
  have h2 := (hasDerivAt_const z c).fun_div h1 (pow_ne_zero _ hz)
  refine h2.congr_deriv ?_
  push_cast
  field_simp
  ring

theorem r11Chi_pole_term_hasDerivAt_zero (c a b z : ℂ) (hz : z - a ≠ 0) :
    HasDerivAt (fun w : ℂ => c * (1 / (w - a) - 1 / (b - a))) (-(c / (z - a) ^ 2)) z := by
  have h0 : HasDerivAt (fun w : ℂ => w - a) 1 z := (hasDerivAt_id z).sub_const a
  have h1 := (hasDerivAt_const z (1 : ℂ)).fun_div h0 hz
  have h2 := ((h1.sub_const (1 / (b - a))).const_mul c)
  refine h2.congr_deriv ?_
  field_simp
  ring

theorem r11Chi_pole_diff (h : r11Chi_PoleHyp c a u U) (m : ℕ) (i : ι) :
    DifferentiableOn ℂ (fun w : ℂ => c i / (w - a i) ^ (m + 2)) U := by
  by_cases hc : c i = 0
  · simp only [hc, zero_div]; exact differentiableOn_const 0
  · intro w hw
    have hne : w - a i ≠ 0 := norm_pos_iff.mp (by linarith [h.far i hc w hw])
    exact (r11Chi_pole_term_hasDerivAt _ _ _ m hne).differentiableAt.differentiableWithinAt

/-- Termwise derivative of `∑ c_i/(z-a_i)^{m+2}`. -/
theorem r11Chi_pole_hasDerivAt (h : r11Chi_PoleHyp c a u U) (m : ℕ) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun w : ℂ => ∑' i, c i / (w - a i) ^ (m + 2))
      (-((m : ℂ) + 2) * ∑' i, c i / (z - a i) ^ (m + 3)) z := by
  have hu := h.summable.mul_left ((4 : ℝ) ^ m)
  have hd := differentiableOn_tsum_of_summable_norm hu (fun i => r11Chi_pole_diff h m i)
    h.isOpen (fun i w hw => r11Chi_pole_norm_le h m i hw)
  have hs := hasSum_deriv_of_summable_norm hu (fun i => r11Chi_pole_diff h m i)
    h.isOpen (fun i w hw => r11Chi_pole_norm_le h m i hw) hz
  have hder : ∀ i, deriv (fun w : ℂ => c i / (w - a i) ^ (m + 2)) z
      = -((m : ℂ) + 2) * (c i / (z - a i) ^ (m + 3)) := by
    intro i
    by_cases hc : c i = 0
    · simp [hc]
    · exact (r11Chi_pole_term_hasDerivAt _ _ _ m
        (norm_pos_iff.mp (by linarith [h.far i hc z hz]))).deriv
  have h3 := (hd.differentiableAt (h.isOpen.mem_nhds hz)).hasDerivAt
  simp only [hder] at hs
  rw [← hs.tsum_eq, tsum_mul_left] at h3
  exact h3

/-- Termwise derivative of `∑ c_i (1/(z-a_i) - 1/(b-a_i))`. -/
theorem r11Chi_pole_hasDerivAt_zero (h : r11Chi_PoleHyp c a u U) {b : ℂ} (hb : b ∈ U)
    (hU1 : ∀ w ∈ U, ‖b - w‖ ≤ 1) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun w : ℂ => ∑' i, c i * (1 / (w - a i) - 1 / (b - a i)))
      (-∑' i, c i / (z - a i) ^ 2) z := by
  have hbound : ∀ (i : ι) (w : ℂ), w ∈ U → ‖c i * (1 / (w - a i) - 1 / (b - a i))‖ ≤ u i := by
    intro i w hw
    by_cases hc : c i = 0
    · rw [hc, zero_mul, norm_zero]; exact h.nonneg i
    · have hx := h.far i hc w hw
      have hy := h.far i hc b hb
      have hx0 : 0 < ‖w - a i‖ := by linarith
      have hy0 : 0 < ‖b - a i‖ := by linarith
      have hwa : w - a i ≠ 0 := norm_pos_iff.mp hx0
      have hba : b - a i ≠ 0 := norm_pos_iff.mp hy0
      have h1 := h.bound i hc w hw
      have h2 := h.bound i hc b hb
      rw [div_le_iff₀ (by positivity)] at h1 h2
      have hu0 := h.nonneg i
      have hsq : ‖c i‖ ^ 2 ≤ (u i * (‖w - a i‖ * ‖b - a i‖)) ^ 2 := by
        calc ‖c i‖ ^ 2 = ‖c i‖ * ‖c i‖ := by ring
          _ ≤ (u i * ‖w - a i‖ ^ 2) * (u i * ‖b - a i‖ ^ 2) :=
            mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hu0 (by positivity))
          _ = _ := by ring
      have hcxy : ‖c i‖ ≤ u i * (‖w - a i‖ * ‖b - a i‖) :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hu0 (by positivity))).mp hsq
      have e : 1 / (w - a i) - 1 / (b - a i) = (b - w) / ((w - a i) * (b - a i)) := by
        rw [div_sub_div _ _ hwa hba]; congr 1; ring
      rw [norm_mul, e, norm_div, norm_mul]
      calc ‖c i‖ * (‖b - w‖ / (‖w - a i‖ * ‖b - a i‖))
          ≤ ‖c i‖ * (1 / (‖w - a i‖ * ‖b - a i‖)) :=
            mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right (hU1 w hw) (by positivity)) (norm_nonneg _)
        _ = ‖c i‖ / (‖w - a i‖ * ‖b - a i‖) := by ring
        _ ≤ u i := by rw [div_le_iff₀ (by positivity)]; exact hcxy
  have hdiff : ∀ i, DifferentiableOn ℂ (fun w : ℂ => c i * (1 / (w - a i) - 1 / (b - a i))) U := by
    intro i
    by_cases hc : c i = 0
    · simp only [hc, zero_mul]; exact differentiableOn_const 0
    · intro w hw
      have hne : w - a i ≠ 0 := norm_pos_iff.mp (by linarith [h.far i hc w hw])
      exact (r11Chi_pole_term_hasDerivAt_zero _ _ b _ hne).differentiableAt.differentiableWithinAt
  have hd := differentiableOn_tsum_of_summable_norm h.summable hdiff h.isOpen hbound
  have hs := hasSum_deriv_of_summable_norm h.summable hdiff h.isOpen hbound hz
  have hder : ∀ i, deriv (fun w : ℂ => c i * (1 / (w - a i) - 1 / (b - a i))) z
      = -(c i / (z - a i) ^ 2) := by
    intro i
    by_cases hc : c i = 0
    · simp [hc]
    · have hne : z - a i ≠ 0 := norm_pos_iff.mp (by linarith [h.far i hc z hz])
      exact (r11Chi_pole_term_hasDerivAt_zero _ _ b _ hne).deriv
  have h3 := (hd.differentiableAt (h.isOpen.mem_nhds hz)).hasDerivAt
  simp only [hder] at hs
  rw [← hs.tsum_eq, tsum_neg] at h3
  exact h3

theorem r11Chi_deriv_eq_zero_of_const {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) {K : ℂ}
    (hg : ∀ w ∈ U, g w = K) {z : ℂ} (hz : z ∈ U) {d : ℂ} (hd : HasDerivAt g d z) : d = 0 := by
  have : g =ᶠ[𝓝 z] fun _ => K := by
    filter_upwards [hU.mem_nhds hz] with w hw using hg w hw
  exact hd.unique ((hasDerivAt_const z K).congr_of_eventuallyEq this)

end Generic

/-! ## The ball around `3/2` -/

theorem r11Chi_ball_facts {z : ℂ} (hz : z ∈ Metric.ball (3 / 2 : ℂ) (1 / 4)) :
    5 / 4 < z.re ∧ ‖z‖ < 7 / 4 := by
  rw [mem_ball_iff_norm] at hz
  have h1 := Complex.abs_re_le_norm (z - 3 / 2)
  have h2 : (z - 3 / 2).re = z.re - 3 / 2 := by
    rw [Complex.sub_re]; norm_num
  rw [h2, abs_le] at h1
  have h3 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by
    rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real]; norm_num
  have h4 : ‖z‖ ≤ ‖z - 3 / 2‖ + ‖(3 / 2 : ℂ)‖ := by
    have := norm_add_le (z - 3 / 2) (3 / 2 : ℂ)
    rwa [sub_add_cancel] at this
  constructor <;> linarith

theorem r11Chi_zeroHyp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) :
    r11Chi_PoleHyp (fun ρ : ℂ => (zeroOrd χ ρ : ℂ)) (fun ρ : ℂ => ρ)
      (fun ρ : ℂ => 64 * ((zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)) (Metric.ball (3 / 2 : ℂ) (1 / 4)) := by
  have key : ∀ ρ : ℂ, (zeroOrd χ ρ : ℂ) ≠ 0 → ∀ z ∈ Metric.ball (3 / 2 : ℂ) (1 / 4),
      1 / 4 ≤ ‖z - ρ‖ ∧ 0 < ‖ρ‖ ∧ ‖ρ‖ ≤ 8 * ‖z - ρ‖ := by
    intro ρ hc z hz
    have hm : zeroOrd χ ρ ≠ 0 := by exact_mod_cast hc
    obtain ⟨hr0, hr1⟩ := zeroOrd_strip hm
    obtain ⟨hz1, hz2⟩ := r11Chi_ball_facts hz
    have h1 : 1 / 4 ≤ ‖z - ρ‖ := by
      have := Complex.re_le_norm (z - ρ)
      rw [Complex.sub_re] at this
      linarith
    have h2 : ‖ρ‖ ≤ ‖z - ρ‖ + ‖z‖ := by
      have := norm_sub_le z (z - ρ)
      rw [sub_sub_cancel] at this
      linarith
    have h3 : 0 < ‖ρ‖ := norm_pos_iff.mpr (ne_zero_of_re_pos hr0)
    exact ⟨h1, h3, by linarith⟩
  refine ⟨Metric.isOpen_ball, hS.mul_left 64, fun ρ => by positivity,
    fun ρ hc z hz => (key ρ hc z hz).1, fun ρ hc z hz => ?_⟩
  obtain ⟨h1, h3, h4⟩ := key ρ hc z hz
  have hx0 : 0 < ‖z - ρ‖ := by linarith
  have h5 : ‖ρ‖ ^ 2 ≤ 64 * ‖z - ρ‖ ^ 2 := by nlinarith
  rw [Complex.norm_natCast, div_le_iff₀ (by positivity),
    show 64 * ((zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) * ‖z - ρ‖ ^ 2
      = (zeroOrd χ ρ : ℝ) * (64 * ‖z - ρ‖ ^ 2) / ‖ρ‖ ^ 2 by ring, le_div_iff₀ (by positivity)]
  exact mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg _)

theorem r11Chi_gammaHyp {N : ℕ} (χ : DirichletCharacter ℂ N) :
    r11Chi_PoleHyp (fun _ : ℕ => (1 : ℂ)) (fun i : ℕ => -((2 * i + gammaShift χ : ℕ) : ℂ))
      (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2) (Metric.ball (3 / 2 : ℂ) (1 / 4)) := by
  have key : ∀ (i : ℕ), ∀ z ∈ Metric.ball (3 / 2 : ℂ) (1 / 4),
      (i : ℝ) + 1 ≤ ‖z - -((2 * i + gammaShift χ : ℕ) : ℂ)‖ := by
    intro i z hz
    obtain ⟨hz1, -⟩ := r11Chi_ball_facts hz
    have := Complex.re_le_norm (z - -((2 * i + gammaShift χ : ℕ) : ℂ))
    rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re] at this
    have h0 : (0 : ℝ) ≤ gammaShift χ := Nat.cast_nonneg _
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have hre : ((2 * i + gammaShift χ : ℕ) : ℝ) = 2 * i + gammaShift χ := by push_cast; ring
    rw [hre] at this
    linarith
  have hsum : Summable fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2 := by
    have h1 : Summable (fun j : ℕ => (1 : ℝ) / (((j + 1 : ℕ) : ℝ)) ^ 2) :=
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num))
    refine h1.congr fun j => ?_
    rw [Nat.cast_add, Nat.cast_one]
  refine ⟨Metric.isOpen_ball, hsum, fun i => by positivity, fun i _ z hz => ?_,
    fun i _ z hz => ?_⟩
  · have := key i z hz
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    linarith
  · have hk := key i z hz
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    rw [norm_one]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hk 2)

theorem r11Chi_mem_ball : (3 / 2 : ℂ) ∈ Metric.ball (3 / 2 : ℂ) (1 / 4) :=
  Metric.mem_ball_self (by norm_num)

/-! ## Summability -/

theorem r11Chi_summable_zeroPow {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) {k : ℕ} (hk : 1 ≤ k) :
    Summable fun ρ : ℂ => (zeroOrd χ ρ : ℂ) / ((3 / 2 : ℂ) - ρ) ^ (k + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h := r11Chi_zeroHyp χ hS
  exact Summable.of_norm_bounded (h.summable.mul_left ((4 : ℝ) ^ m))
    (fun ρ => r11Chi_pole_norm_le h m ρ r11Chi_mem_ball)

theorem r11Chi_summable_gammaPow {N : ℕ} (χ : DirichletCharacter ℂ N) {k : ℕ} (hk : 1 ≤ k) :
    Summable fun i : ℕ => 1 / ((3 / 2 : ℂ) + ((2 * i + gammaShift χ : ℕ) : ℂ)) ^ (k + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h := r11Chi_gammaHyp χ
  have h2 := Summable.of_norm_bounded (h.summable.mul_left ((4 : ℝ) ^ m))
    (fun i => r11Chi_pole_norm_le h m i r11Chi_mem_ball)
  refine h2.congr fun i => ?_
  simp only [sub_neg_eq_add]

/-! ## The Dirichlet series -/

theorem r11Chi_iter_apply (f : ℕ → ℂ) (k n : ℕ) :
    (LSeries.logMul^[k] f) n = Complex.log n ^ k * f n := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [LSeries.logMul]
    ring

theorem r11Chi_abscissa_iter (f : ℕ → ℂ) (k : ℕ) :
    LSeries.abscissaOfAbsConv (LSeries.logMul^[k] f) = LSeries.abscissaOfAbsConv f := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', LSeries.abscissaOfAbsConv_logMul, ih]

theorem r11Chi_norm_term (h : ℕ → ℂ) (k n : ℕ) :
    ‖LSeries.term (LSeries.logMul^[k] h) (3 / 2) n‖
      = ‖h n‖ * Real.log n ^ k / (n : ℝ) ^ (3 / 2 : ℝ) := by
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · subst hn
    rw [Nat.cast_zero, Real.zero_rpow (by norm_num), div_zero]
  · have hre : (3 / 2 : ℂ).re = 3 / 2 := by norm_num
    rw [r11Chi_iter_apply, norm_mul, norm_pow, ← Complex.natCast_log, Complex.norm_real,
      Real.norm_of_nonneg (Real.log_natCast_nonneg n), hre]
    ring

theorem r11Chi_abscissa_vonMangoldt :
    LSeries.abscissaOfAbsConv (fun n : ℕ => (Λ n : ℂ)) ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun y hy => ?_
  have hy' : (1 : ℝ) < y := by exact_mod_cast hy
  exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy')

theorem r11Chi_deriv_summable_F (k : ℕ) :
    Summable fun n : ℕ => Λ n * Real.log n ^ k / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hre : (3 / 2 : ℂ).re = 3 / 2 := by norm_num
  have hlt : LSeries.abscissaOfAbsConv (LSeries.logMul^[k] (fun n : ℕ => (Λ n : ℂ)))
      < ((3 / 2 : ℂ).re : EReal) := by
    rw [r11Chi_abscissa_iter, hre]
    exact lt_of_le_of_lt r11Chi_abscissa_vonMangoldt (by exact_mod_cast (by norm_num : (1 : ℝ) < 3 / 2))
  have h := (LSeriesSummable_of_abscissaOfAbsConv_lt_re hlt).norm
  refine h.congr fun n => ?_
  rw [r11Chi_norm_term, Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- `‖∑ χ(n) Λ(n) log^k n · n^{-3/2}‖ ≤ F_k`. -/
theorem r11Chi_norm_LSeries_logMul_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (k : ℕ) :
    ‖LSeries (LSeries.logMul^[k] (fun n : ℕ => χ (n : ZMod N) * (Λ n : ℂ))) (3 / 2)‖
      ≤ r11Chi_F k := by
  have hF := r11Chi_deriv_summable_F k
  have hle : ∀ n : ℕ, ‖LSeries.term (LSeries.logMul^[k]
      (fun n : ℕ => χ (n : ZMod N) * (Λ n : ℂ))) (3 / 2) n‖
      ≤ Λ n * Real.log n ^ k / (n : ℝ) ^ (3 / 2 : ℝ) := by
    intro n
    rw [r11Chi_norm_term]
    have h1 : ‖χ (n : ZMod N) * (Λ n : ℂ)‖ ≤ Λ n := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1
      (pow_nonneg (Real.log_natCast_nonneg n) k)) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hs : Summable fun n : ℕ => ‖LSeries.term (LSeries.logMul^[k]
      (fun n : ℕ => χ (n : ZMod N) * (Λ n : ℂ))) (3 / 2) n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle hF
  unfold r11Chi_F LSeries
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hle hF)

theorem r11Chi_neg_logDeriv_eq_LSeries {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    -(deriv (LFunction χ) s / LFunction χ s)
      = LSeries (fun n : ℕ => χ (n : ZMod N) * (Λ n : ℂ)) s := by
  have h1 : LSeries (fun n : ℕ => χ (n : ZMod N) * (Λ n : ℂ)) s = _ :=
    LSeries_twist_vonMangoldt_eq χ hs
  rw [h1, deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs, neg_div]

theorem r11Chi_abscissa_twist {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    LSeries.abscissaOfAbsConv (fun n : ℕ => χ (n : ZMod N) * (Λ n : ℂ)) ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun y hy => ?_
  have hy' : (1 : ℝ) < y := by exact_mod_cast hy
  exact LSeriesSummable_twist_vonMangoldt χ (by simpa using hy')

/-! ## The identity on the ball and its derivatives -/

section Main

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- On the ball, `T(z) + Γ₀(z) + ∑ χΛ n^{-z}` is constant. -/
theorem r11Chi_const_identity (hχ1 : χ ≠ 1) (hH : HadamardLogDeriv χ)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) {z : ℂ}
    (hz : z ∈ Metric.ball (3 / 2 : ℂ) (1 / 4)) :
    (∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (z - ρ) - 1 / (3 / 2 - ρ)))
      + (∑' i : ℕ, (1 : ℂ) * (1 / (z - -((2 * i + gammaShift χ : ℕ) : ℂ))
          - 1 / (3 / 2 - -((2 * i + gammaShift χ : ℕ) : ℂ))))
      + LSeries (fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ)) z
      = LSeries (fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ)) (3 / 2) := by
  have hz1 : 1 < z.re := by linarith [(r11Chi_ball_facts hz).1]
  have h32 : 1 < (3 / 2 : ℂ).re := by norm_num
  have h2 : 1 < (2 : ℂ).re := by norm_num
  have hsum : ∀ {s : ℂ}, 1 < s.re →
      Summable fun ρ : ℂ => (zeroOrd χ ρ : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ)) := by
    intro s hs
    exact ((summable_hadamard_terms χ hS hs).sub (summable_hadamard_terms χ hS h2)).congr
      (fun ρ => by ring)
  have hT : ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (z - ρ) - 1 / (3 / 2 - ρ))
      = Zfun χ z - Zfun χ (3 / 2) := by
    unfold Zfun
    rw [← (hsum hz1).tsum_sub (hsum h32)]
    exact tsum_congr fun ρ => by ring
  have hG : ∑' i : ℕ, (1 : ℂ) * (1 / (z - -((2 * i + gammaShift χ : ℕ) : ℂ))
      - 1 / (3 / 2 - -((2 * i + gammaShift χ : ℕ) : ℂ))) = Gfun χ (3 / 2) - Gfun χ z := by
    have h := (hasSum_Gfun_sub χ (s := 3 / 2) (by norm_num)).sub
      (hasSum_Gfun_sub χ (s := z) (by linarith))
    have e : ∑' i : ℕ, (1 : ℂ) * (1 / (z - -((2 * i + gammaShift χ : ℕ) : ℂ))
        - 1 / (3 / 2 - -((2 * i + gammaShift χ : ℕ) : ℂ)))
        = (Gfun χ (3 / 2) - Gfun χ 2) - (Gfun χ z - Gfun χ 2) := by
      rw [← h.tsum_eq]
      refine tsum_congr fun i => ?_
      simp only [sub_neg_eq_add, one_mul]
      ring
    rw [e]; ring
  have eZz := Zfun_eq χ hχ1 hH hS hz1
  have eZ32 := Zfun_eq χ hχ1 hH hS h32
  have eLz := r11Chi_neg_logDeriv_eq_LSeries χ hz1
  have eL32 := r11Chi_neg_logDeriv_eq_LSeries χ h32
  linear_combination hT + hG + eZz - eZ32 - eLz + eL32

theorem r11Chi_ball_dist {w : ℂ} (hw : w ∈ Metric.ball (3 / 2 : ℂ) (1 / 4)) :
    ‖(3 / 2 : ℂ) - w‖ ≤ 1 := by
  rw [mem_ball_iff_norm, ← norm_neg, neg_sub] at hw
  linarith

/-- The three derivative identities at `3/2` (raw form). -/
theorem r11Chi_zeroPow_raw (hχ1 : χ ≠ 1) (hH : HadamardLogDeriv χ)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) :
    let f : ℕ → ℂ := fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ)
    (∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / ((3 / 2 : ℂ) - ρ) ^ 2
      = -(∑' i : ℕ, (1 : ℂ) / ((3 / 2 : ℂ) - -((2 * i + gammaShift χ : ℕ) : ℂ)) ^ 2)
        - LSeries (LSeries.logMul f) (3 / 2)) ∧
    (∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / ((3 / 2 : ℂ) - ρ) ^ 3
      = -(∑' i : ℕ, (1 : ℂ) / ((3 / 2 : ℂ) - -((2 * i + gammaShift χ : ℕ) : ℂ)) ^ 3)
        - 1 / 2 * LSeries (LSeries.logMul (LSeries.logMul f)) (3 / 2)) ∧
    (∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / ((3 / 2 : ℂ) - ρ) ^ 4
      = -(∑' i : ℕ, (1 : ℂ) / ((3 / 2 : ℂ) - -((2 * i + gammaShift χ : ℕ) : ℂ)) ^ 4)
        - 1 / 6 * LSeries (LSeries.logMul (LSeries.logMul (LSeries.logMul f))) (3 / 2)) := by
  intro f
  set B := Metric.ball (3 / 2 : ℂ) (1 / 4) with hB
  have hZ := r11Chi_zeroHyp χ hS
  have hΓ := r11Chi_gammaHyp χ
  have hopen : IsOpen B := Metric.isOpen_ball
  have hab : ∀ (g : ℕ → ℂ), LSeries.abscissaOfAbsConv g = LSeries.abscissaOfAbsConv f →
      ∀ z ∈ B, HasDerivAt (LSeries g) (-LSeries (LSeries.logMul g) z) z := by
    intro g hg z hz
    have hz1 : (1 : ℝ) < z.re := by linarith [(r11Chi_ball_facts hz).1]
    refine LSeries_hasDerivAt ?_
    rw [hg]
    exact lt_of_le_of_lt (r11Chi_abscissa_twist χ) (by exact_mod_cast hz1)
  have a1 : LSeries.abscissaOfAbsConv (LSeries.logMul f) = LSeries.abscissaOfAbsConv f :=
    LSeries.abscissaOfAbsConv_logMul
  have a2 : LSeries.abscissaOfAbsConv (LSeries.logMul (LSeries.logMul f))
      = LSeries.abscissaOfAbsConv f := by rw [LSeries.abscissaOfAbsConv_logMul, a1]
  -- first derivative
  have E1 : ∀ z ∈ B, -(∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / (z - ρ) ^ 2)
      + -(∑' i : ℕ, (1 : ℂ) / (z - -((2 * i + gammaShift χ : ℕ) : ℂ)) ^ 2)
      + -LSeries (LSeries.logMul f) z = 0 := by
    intro z hz
    have d1 := r11Chi_pole_hasDerivAt_zero hZ r11Chi_mem_ball (fun w hw => r11Chi_ball_dist hw) hz
    have d2 := r11Chi_pole_hasDerivAt_zero hΓ r11Chi_mem_ball (fun w hw => r11Chi_ball_dist hw) hz
    have d3 := hab f rfl z hz
    exact r11Chi_deriv_eq_zero_of_const hopen
      (fun w hw => r11Chi_const_identity χ hχ1 hH hS hw) hz ((d1.add d2).add d3)
  -- second derivative
  have E2 : ∀ z ∈ B, -(-(((0 : ℕ) : ℂ) + 2) * ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / (z - ρ) ^ 3)
      + -(-(((0 : ℕ) : ℂ) + 2)
        * ∑' i : ℕ, (1 : ℂ) / (z - -((2 * i + gammaShift χ : ℕ) : ℂ)) ^ 3)
      + -(-LSeries (LSeries.logMul (LSeries.logMul f)) z) = 0 := by
    intro z hz
    have d1 := (r11Chi_pole_hasDerivAt hZ 0 hz).neg
    have d2 := (r11Chi_pole_hasDerivAt hΓ 0 hz).neg
    have d3 := (hab _ a1 z hz).neg
    exact r11Chi_deriv_eq_zero_of_const hopen (fun w hw => E1 w hw) hz ((d1.add d2).add d3)
  -- third derivative
  have E3 : ∀ z ∈ B, -(-(((0 : ℕ) : ℂ) + 2)
        * (-(((1 : ℕ) : ℂ) + 2) * ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / (z - ρ) ^ 4))
      + -(-(((0 : ℕ) : ℂ) + 2) * (-(((1 : ℕ) : ℂ) + 2)
        * ∑' i : ℕ, (1 : ℂ) / (z - -((2 * i + gammaShift χ : ℕ) : ℂ)) ^ 4))
      + -(-(-LSeries (LSeries.logMul (LSeries.logMul (LSeries.logMul f))) z)) = 0 := by
    intro z hz
    have d1 := ((r11Chi_pole_hasDerivAt hZ 1 hz).const_mul (-(((0 : ℕ) : ℂ) + 2))).neg
    have d2 := ((r11Chi_pole_hasDerivAt hΓ 1 hz).const_mul (-(((0 : ℕ) : ℂ) + 2))).neg
    have d3 := (hab _ a2 z hz).neg.neg
    exact r11Chi_deriv_eq_zero_of_const hopen (fun w hw => E2 w hw) hz ((d1.add d2).add d3)
  have e1 := E1 _ r11Chi_mem_ball
  have e2 := E2 _ r11Chi_mem_ball
  have e3 := E3 _ r11Chi_mem_ball
  simp only [Nat.cast_zero, Nat.cast_one] at e2 e3
  refine ⟨?_, ?_, ?_⟩
  · linear_combination -e1
  · linear_combination (1 / 2 : ℂ) * e2
  · linear_combination (-1 / 6 : ℂ) * e3

/-- **Higher partial-fraction identities at `3/2`**: for `k = 1, 2, 3`,
`∑_ρ m_ρ/(3/2-ρ)^{k+1} = -∑_i 1/(3/2+2i+a)^{k+1} - (1/k!) ∑_n χ(n)Λ(n) log^k n · n^{-3/2}`. -/
theorem r11Chi_zeroPow_eq (hχ1 : χ ≠ 1) (hH : HadamardLogDeriv χ)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) {k : ℕ} (hk1 : 1 ≤ k)
    (hk3 : k ≤ 3) :
    ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / ((3 / 2 : ℂ) - ρ) ^ (k + 1)
      = -∑' i : ℕ, 1 / ((3 / 2 : ℂ) + ((2 * i + gammaShift χ : ℕ) : ℂ)) ^ (k + 1)
        - 1 / (k.factorial : ℂ) * LSeries (LSeries.logMul^[k]
            (fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ))) (3 / 2) := by
  obtain ⟨h1, h2, h3⟩ := r11Chi_zeroPow_raw χ hχ1 hH hS
  simp only [sub_neg_eq_add] at h1 h2 h3
  interval_cases k
  · rw [show ((Nat.factorial 1 : ℕ) : ℂ) = 1 by norm_num [Nat.factorial], div_one, one_mul]
    exact h1
  · rw [show ((Nat.factorial 2 : ℕ) : ℂ) = 2 by norm_num [Nat.factorial]]
    exact h2
  · rw [show ((Nat.factorial 3 : ℕ) : ℂ) = 6 by norm_num [Nat.factorial]]
    exact h3

end Main

#print axioms r11Chi_zeroPow_eq
#print axioms r11Chi_norm_LSeries_logMul_le
#print axioms r11Chi_summable_zeroPow
#print axioms r11Chi_summable_gammaPow

end DetPrimality.Bach
