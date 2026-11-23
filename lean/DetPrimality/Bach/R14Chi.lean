import DetPrimality.Bach.R14ChiPerron
import DetPrimality.Bach.R13Chi

/-!
# Round 14, (P2ₐ): the χ explicit formula with shift `a` (`R14ChiExplicit a`, every `a : ℕ`)

With `β = a + 1`, `Y = y^β` and `s″ = (s + a)/β` (formal0760 §1.2):
`Φ^{(a)}_{χ,j}(y) = j! β^{-j} y^{-a} P_j[s″ ↦ D(β s″ - a)](Y)` (`r14C_Phi_eq_perron`), and
`D(β s″ - a) = -L'/L(a + 3/2) - (1/β) ∑_k (1/(s″-u_k) - 1/(2-u_k)) - (1/β) ∑_ρ m_ρ (1/(s″-v_ρ) - 1/(2-v_ρ))`
with `u_k = (s_k + a)/β`, `v_ρ = (ρ + 1/2 + a)/β` (`r14C_decomp_scaled`; Hadamard re-centred at `a + 3/2`).
`Re u_k, Re v_ρ ≤ 3/2`, so `r11Chi_perron_hasSum_poles` applies; `Y^{v_ρ} = y^{ρ+1/2+a}`,
`|u_k| ≥ 1/(2β)`, `|v_ρ| ≥ 1`, `|w| ≤ |2 - w|` for both families, `Y^{u_k} ≤ y^a √y`.
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## The scaling `w ↦ (w + a)/(a + 1)` -/

/-- `w″ = (w + a)/β`, `β = a + 1`. -/
noncomputable def r14C_sc (a : ℕ) (w : ℂ) : ℂ := (w + (a : ℂ)) / ((a : ℂ) + 1)

theorem r14C_B_ne (a : ℕ) : (a : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero a

theorem r14C_norm_B (a : ℕ) : ‖(a : ℂ) + 1‖ = (a : ℝ) + 1 := by
  rw [← Nat.cast_add_one, Complex.norm_natCast, Nat.cast_add_one]

theorem r14C_sc_re (a : ℕ) (w : ℂ) : (r14C_sc a w).re = (w.re + a) / ((a : ℝ) + 1) := by
  unfold r14C_sc
  rw [show (a : ℂ) + 1 = (((a : ℝ) + 1 : ℝ) : ℂ) by simp, Complex.div_ofReal_re]
  simp

theorem r14C_norm_sc (a : ℕ) (w : ℂ) : ‖r14C_sc a w‖ = ‖w + (a : ℂ)‖ / ((a : ℝ) + 1) := by
  unfold r14C_sc
  rw [norm_div, r14C_norm_B]

theorem r14C_scale_term (a : ℕ) (s w : ℂ) :
    1 / (((a : ℂ) + 1) * s - a - w) - 1 / ((a : ℂ) + 2 - w)
      = 1 / ((a : ℂ) + 1) * (1 / (s - r14C_sc a w) - 1 / (2 - r14C_sc a w)) := by
  have hB := r14C_B_ne a
  have e1 : ((a : ℂ) + 1) * s - a - w = ((a : ℂ) + 1) * (s - r14C_sc a w) := by
    unfold r14C_sc
    rw [mul_sub, mul_div_cancel₀ _ hB]
    ring
  have e2 : (a : ℂ) + 2 - w = ((a : ℂ) + 1) * (2 - r14C_sc a w) := by
    unfold r14C_sc
    rw [mul_sub, mul_div_cancel₀ _ hB]
    ring
  rw [e1, e2]
  simp only [one_div, mul_inv]
  ring

theorem r14C_cpow_scale {y : ℝ} (hy : 0 < y) (a : ℕ) (w : ℂ) :
    ((y ^ (a + 1) : ℝ) : ℂ) ^ (r14C_sc a w) = (y : ℂ) ^ (w + (a : ℂ)) := by
  have hY : 0 < y ^ (a + 1) := pow_pos hy _
  have hB := r14C_B_ne a
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hY.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
    ← Complex.ofReal_log hY.le, ← Complex.ofReal_log hy.le, Real.log_pow, Nat.cast_add_one]
  congr 1
  unfold r14C_sc
  rw [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
    mul_comm ((a : ℂ) + 1) _, mul_assoc, mul_div_cancel₀ _ hB]

theorem r14C_norm_le_add {w : ℂ} (hw : 0 ≤ w.re) (a : ℕ) : ‖w‖ ≤ ‖w + (a : ℂ)‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  have e1 : (w + (a : ℂ)).re = w.re + a := by simp
  have e2 : (w + (a : ℂ)).im = w.im := by simp
  rw [e1, e2]
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  nlinarith [mul_nonneg hw ha, mul_nonneg ha ha]

theorem r14C_weight_le (a : ℕ) (w : ℂ) {m : ℝ} (hm : 0 ≤ m) :
    m / ((a : ℝ) + 1) / (1 + ‖r14C_sc a w‖) ^ 2 ≤ ((a : ℝ) + 1) * (m / (1 + ‖w‖) ^ 2) := by
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hB : (0 : ℝ) < (a : ℝ) + 1 := by linarith
  have h0 : 1 + ‖w‖ ≤ ((a : ℝ) + 1) * (1 + ‖r14C_sc a w‖) := by
    rw [r14C_norm_sc, mul_add, mul_one, mul_div_cancel₀ _ hB.ne']
    have h := norm_sub_le (w + (a : ℂ)) (a : ℂ)
    rw [add_sub_cancel_right, Complex.norm_natCast] at h
    linarith
  have h1 : (1 + ‖w‖) ^ 2 ≤ (((a : ℝ) + 1) * (1 + ‖r14C_sc a w‖)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h0 2
  rw [div_div, show ((a : ℝ) + 1) * (m / (1 + ‖w‖) ^ 2) = ((a : ℝ) + 1) * m / (1 + ‖w‖) ^ 2 by ring,
    div_le_div_iff₀ (by positivity) (by positivity)]
  calc m * (1 + ‖w‖) ^ 2 ≤ m * (((a : ℝ) + 1) * (1 + ‖r14C_sc a w‖)) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 hm
    _ = ((a : ℝ) + 1) * m * (((a : ℝ) + 1) * (1 + ‖r14C_sc a w‖) ^ 2) := by ring

/-! ## The Hadamard decomposition, re-centred at `z₀` -/

theorem r14C_decomp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (hH : HadamardLogDeriv χ) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)
    {s z0 : ℂ} (hs : 3 / 2 < s.re) (hz0 : 1 < z0.re) :
    LSeries (r11Chi_coeff χ) s
      = -(deriv (LFunction χ) z0 / LFunction χ z0)
        + ∑' k : ℕ, (-1 : ℂ) * (1 / (s - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))
            - 1 / (z0 + 1 / 2 - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ)))
        + ∑' ρ : ℂ, (-(zeroOrd χ ρ : ℂ))
            * (1 / (s - (ρ + 1 / 2)) - 1 / (z0 + 1 / 2 - (ρ + 1 / 2))) := by
  have hzre : 1 < (s - 1 / 2).re := by
    rw [Complex.sub_re]
    norm_num
    linarith
  have hLS : LSeries (r11Chi_coeff χ) s
      = -(deriv (LFunction χ) (s - 1 / 2) / LFunction χ (s - 1 / 2)) := by
    have h1 : LSeries (fun n => χ (n : ZMod q) * (Λ n : ℂ)) (s - 1 / 2) = _ :=
      LSeries_twist_vonMangoldt_eq χ hzre
    rw [r11Chi_LSeries_shift, h1, deriv_LFunction_eq_deriv_LSeries χ hzre,
      LFunction_eq_LSeries χ hzre, neg_div]
  have hdz := neg_logDeriv_decomp χ hχ1 hH hS hzre
  have hd0 := neg_logDeriv_decomp χ hχ1 hH hS hz0
  have hG1 := hasSum_Gfun_sub χ (s := s - 1 / 2) (by linarith)
  have hG2 := hasSum_Gfun_sub χ (s := z0) (by linarith)
  have hA : ∑' k : ℕ, (-1 : ℂ) * (1 / (s - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))
      - 1 / (z0 + 1 / 2 - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ)))
      = Gfun χ (s - 1 / 2) - Gfun χ z0 := by
    have h := (hG2.sub hG1).tsum_eq
    rw [show Gfun χ (s - 1 / 2) - Gfun χ z0
        = -(Gfun χ z0 - Gfun χ 2 - (Gfun χ (s - 1 / 2) - Gfun χ 2)) by ring, ← h, ← tsum_neg]
    refine tsum_congr fun k => ?_
    have e1 : s - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ)
        = s - 1 / 2 + ((2 * k + gammaShift χ : ℕ) : ℂ) := by
      simp only [r11Chi_r]
      push_cast
      ring
    have e2 : z0 + 1 / 2 - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ)
        = z0 + ((2 * k + gammaShift χ : ℕ) : ℂ) := by
      simp only [r11Chi_r]
      push_cast
      ring
    rw [e1, e2]
    ring
  have hsm : ∀ {u : ℂ}, 1 < u.re →
      Summable fun ρ : ℂ => (zeroOrd χ ρ : ℂ) * (1 / (u - ρ) - 1 / (2 - ρ)) := by
    intro u hu
    have h := (summable_hadamard_terms χ hS hu).sub
      (summable_hadamard_terms χ hS (s := 2) (by norm_num))
    refine h.congr fun ρ => ?_
    ring
  have hB : ∑' ρ : ℂ, (-(zeroOrd χ ρ : ℂ))
        * (1 / (s - (ρ + 1 / 2)) - 1 / (z0 + 1 / 2 - (ρ + 1 / 2)))
      = -((∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (s - 1 / 2 - ρ) - 1 / (2 - ρ)))
        - ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (z0 - ρ) - 1 / (2 - ρ))) := by
    rw [← (hsm hzre).tsum_sub (hsm hz0), ← tsum_neg]
    refine tsum_congr fun ρ => ?_
    rw [show s - (ρ + 1 / 2) = s - 1 / 2 - ρ by ring,
      show z0 + 1 / 2 - (ρ + 1 / 2) = z0 - ρ by ring]
    ring
  rw [hLS, hA, hB]
  linear_combination hdz - hd0

/-- The decomposition of `s″ ↦ D(β s″ - a)` on the line `Re s″ = 2`. -/
theorem r14C_decomp_scaled {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (hH : HadamardLogDeriv χ) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)
    (a : ℕ) {s : ℂ} (hs : s.re = 2) :
    LSeries (r11Chi_coeff χ) (((a : ℂ) + 1) * s - a)
      = -(deriv (LFunction χ) (((a : ℝ) + 3 / 2 : ℝ) : ℂ)
            / LFunction χ (((a : ℝ) + 3 / 2 : ℝ) : ℂ))
        + ∑' k : ℕ, (-(1 / ((a : ℂ) + 1)))
            * (1 / (s - r14C_sc a ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))
              - 1 / (2 - r14C_sc a ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ)))
        + ∑' ρ : ℂ, (-((zeroOrd χ ρ : ℂ) / ((a : ℂ) + 1)))
            * (1 / (s - r14C_sc a (ρ + 1 / 2)) - 1 / (2 - r14C_sc a (ρ + 1 / 2))) := by
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hre : (((a : ℂ) + 1) * s - a).re = ((a : ℝ) + 1) * s.re - a := by
    simp [Complex.mul_re]
  have h1 : 3 / 2 < (((a : ℂ) + 1) * s - a).re := by
    rw [hre, hs]
    linarith
  have h2 : 1 < ((((a : ℝ) + 3 / 2 : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]
    linarith
  have e0 : ((((a : ℝ) + 3 / 2 : ℝ) : ℂ)) + 1 / 2 = (a : ℂ) + 2 := by
    push_cast
    ring
  rw [r14C_decomp χ hχ1 hH hS h1 h2, e0]
  congr 1
  · congr 1
    refine tsum_congr fun k => ?_
    rw [r14C_scale_term]
    ring
  · refine tsum_congr fun ρ => ?_
    rw [r14C_scale_term]
    ring

/-! ## The non-oscillating part with a general lower bound `|w| ≥ 1/D` -/

theorem r14C_inv_pow_le {x D : ℝ} (hx : 0 < x) (hD : 1 ≤ D) (hDx : 1 ≤ D * x) {j n : ℕ}
    (hn : 2 ≤ n) (hnj : n ≤ j + 2) : 1 / x ^ n ≤ D ^ j * (1 / x ^ 2) := by
  have hD0 : 0 < D := by linarith
  have hsplit : x ^ n = x ^ 2 * x ^ (n - 2) := by
    rw [← pow_add]; congr 1; omega
  have h1 : (1 : ℝ) ≤ (D * x) ^ (n - 2) := one_le_pow₀ hDx
  have h2 : D ^ (n - 2) ≤ D ^ j := pow_le_pow_right₀ hD (by omega)
  have h3 : (1 : ℝ) ≤ D ^ j * x ^ (n - 2) := by
    rw [mul_pow] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))
  have hne : x ^ 2 ≠ 0 := by positivity
  rw [div_le_iff₀ (by positivity), hsplit,
    show D ^ j * (1 / x ^ 2) * (x ^ 2 * x ^ (n - 2))
      = D ^ j * x ^ (n - 2) * (1 / x ^ 2 * x ^ 2) by ring,
    one_div_mul_cancel hne, mul_one]
  exact h3

theorem r14C_norm_N_le (j : ℕ) {w : ℂ} {D : ℝ} (hD : 1 ≤ D) (hwpos : 0 < ‖w‖)
    (hw : 1 ≤ D * ‖w‖) (hw2 : ‖w‖ ≤ ‖2 - w‖) {L : ℝ} (hL : 0 ≤ L) :
    ‖r13C_N j w L‖ ≤ ((j : ℝ) * D ^ j + 2) * (1 + L) ^ j * (1 / ‖w‖ ^ 2) := by
  have hD0 : 0 < D := by linarith
  have hM : ∀ i, i ≤ j → L ^ i ≤ (1 + L) ^ j := fun i hi =>
    (pow_le_pow_left₀ hL (by linarith) i).trans (pow_le_pow_right₀ (by linarith) hi)
  have hfr : ∀ i, i ≤ j → L ^ i / (i.factorial : ℝ) ≤ (1 + L) ^ j := fun i hi =>
    (div_le_self (pow_nonneg hL i) (by exact_mod_cast i.factorial_pos)).trans (hM i hi)
  have hterm : ∀ i ∈ Finset.range j,
      ‖(L : ℂ) ^ i / (i.factorial : ℂ) / w ^ (j + 1 - i)‖
        ≤ D ^ j * (1 + L) ^ j * (1 / ‖w‖ ^ 2) := by
    intro i hi
    have hi' : i < j := Finset.mem_range.mp hi
    rw [norm_div, norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hL,
      Complex.norm_natCast, div_eq_mul_one_div]
    have h1 := hfr i hi'.le
    have h2 := r14C_inv_pow_le hwpos hD hw (j := j) (n := j + 1 - i) (by omega) (by omega)
    have h0 : 0 ≤ L ^ i / (i.factorial : ℝ) := by positivity
    calc L ^ i / (i.factorial : ℝ) * (1 / ‖w‖ ^ (j + 1 - i))
        ≤ (1 + L) ^ j * (D ^ j * (1 / ‖w‖ ^ 2)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = D ^ j * (1 + L) ^ j * (1 / ‖w‖ ^ 2) := by ring
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
    _ ≤ (j : ℝ) * (D ^ j * (1 + L) ^ j * (1 / ‖w‖ ^ 2)) + 2 * (1 + L) ^ j * (1 / ‖w‖ ^ 2) :=
        add_le_add hsum hlast
    _ = _ := by ring

/-! ## The normalising factor -/

theorem r14C_norm_scal (a j : ℕ) {y : ℝ} (hy : 0 < y) :
    ‖r14C_scal a j y‖ = 1 / ((a : ℝ) + 1) ^ j / y ^ a := by
  unfold r14C_scal
  rw [norm_div, norm_div, norm_one, norm_pow, norm_pow, r14C_norm_B, Complex.norm_real,
    Real.norm_of_nonneg hy.le]

theorem r14C_norm_scal_le_B (a j : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    ‖r14C_scal a j y‖ ≤ 1 / ((a : ℝ) + 1) ^ j := by
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  rw [r14C_norm_scal a j (by linarith)]
  exact div_le_self (by positivity) (one_le_pow₀ hy)

theorem r14C_norm_scal_le_y (a j : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    ‖r14C_scal a j y‖ ≤ 1 / y ^ a := by
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hy0 : 0 < y := by linarith
  have hB1 : (1 : ℝ) ≤ ((a : ℝ) + 1) ^ j := one_le_pow₀ (by linarith)
  rw [r14C_norm_scal a j hy0]
  exact div_le_div_of_nonneg_right ((div_le_one (by linarith)).mpr hB1) (pow_pos hy0 a).le

/-- `K = j (2β)^j + 2`. -/
noncomputable def r14C_K (a j : ℕ) : ℝ := (j : ℝ) * (2 * ((a : ℝ) + 1)) ^ j + 2

theorem r14C_K_nonneg (a j : ℕ) : 0 ≤ r14C_K a j := by
  unfold r14C_K
  positivity

theorem r14C_log_pow (a : ℕ) (y : ℝ) :
    Real.log (y ^ (a + 1)) = ((a : ℝ) + 1) * Real.log y := by
  rw [Real.log_pow, Nat.cast_add_one]

theorem r14C_scal_N_le (a j : ℕ) {y : ℝ} (hy : 1 ≤ y) {u : ℂ} (hu0 : 0 < ‖u‖)
    (hu : 1 ≤ 2 * ((a : ℝ) + 1) * ‖u‖) (hu2 : ‖u‖ ≤ ‖2 - u‖) :
    ‖r14C_scal a j y * r13C_N j u (Real.log (y ^ (a + 1)))‖
      ≤ r14C_K a j * (1 + Real.log y) ^ j * (1 / ‖u‖ ^ 2) := by
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hL : 0 ≤ Real.log y := Real.log_nonneg hy
  have hB : (0 : ℝ) < (a : ℝ) + 1 := by linarith
  have hBL : 0 ≤ ((a : ℝ) + 1) * Real.log y := mul_nonneg hB.le hL
  have hlogY := r14C_log_pow a y
  have hN := r14C_norm_N_le j (D := 2 * ((a : ℝ) + 1)) (by linarith) hu0 hu hu2
    (L := Real.log (y ^ (a + 1))) (by rw [hlogY]; exact hBL)
  have hpow : (1 + Real.log (y ^ (a + 1))) ^ j ≤ ((a : ℝ) + 1) ^ j * (1 + Real.log y) ^ j := by
    rw [hlogY, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by nlinarith) j
  have hK : 0 ≤ r14C_K a j := r14C_K_nonneg a j
  have hBj : 0 < ((a : ℝ) + 1) ^ j := pow_pos hB j
  have hU : 0 ≤ 1 / ‖u‖ ^ 2 := by positivity
  have hM : 0 ≤ (1 + Real.log y) ^ j := pow_nonneg (by linarith) j
  rw [norm_mul]
  calc ‖r14C_scal a j y‖ * ‖r13C_N j u (Real.log (y ^ (a + 1)))‖
      ≤ (1 / ((a : ℝ) + 1) ^ j)
          * (r14C_K a j * (((a : ℝ) + 1) ^ j * (1 + Real.log y) ^ j) * (1 / ‖u‖ ^ 2)) := by
        refine mul_le_mul (r14C_norm_scal_le_B a j hy) (hN.trans ?_) (norm_nonneg _)
          (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hK) hU
    _ = r14C_K a j * (1 + Real.log y) ^ j * (1 / ‖u‖ ^ 2) := by
        rw [show (1 / ((a : ℝ) + 1) ^ j)
            * (r14C_K a j * (((a : ℝ) + 1) ^ j * (1 + Real.log y) ^ j) * (1 / ‖u‖ ^ 2))
          = (1 / ((a : ℝ) + 1) ^ j * ((a : ℝ) + 1) ^ j)
            * (r14C_K a j * (1 + Real.log y) ^ j * (1 / ‖u‖ ^ 2)) by ring,
          one_div_mul_cancel hBj.ne', one_mul]

theorem r14C_c0_le (a j : ℕ) {y : ℝ} (hy : 1 ≤ y) {c : ℂ} {S : ℝ} (hc : ‖c‖ ≤ S) :
    ‖r14C_scal a j y * (c * (Real.log (y ^ (a + 1)) : ℂ) ^ j)‖ ≤ S * (1 + Real.log y) ^ j := by
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hL : 0 ≤ Real.log y := Real.log_nonneg hy
  have hB : (0 : ℝ) < (a : ℝ) + 1 := by linarith
  have hBL : 0 ≤ ((a : ℝ) + 1) * Real.log y := mul_nonneg hB.le hL
  have hlogY := r14C_log_pow a y
  have hS : 0 ≤ S := (norm_nonneg _).trans hc
  have hLj : Real.log y ^ j ≤ (1 + Real.log y) ^ j := pow_le_pow_left₀ hL (by linarith) j
  have hBj : 0 < ((a : ℝ) + 1) ^ j := pow_pos hB j
  have hLj0 : 0 ≤ Real.log y ^ j := pow_nonneg hL j
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, hlogY, Real.norm_of_nonneg hBL, mul_pow]
  calc ‖r14C_scal a j y‖ * (‖c‖ * (((a : ℝ) + 1) ^ j * Real.log y ^ j))
      ≤ (1 / ((a : ℝ) + 1) ^ j) * (S * (((a : ℝ) + 1) ^ j * (1 + Real.log y) ^ j)) := by
        refine mul_le_mul (r14C_norm_scal_le_B a j hy)
          (mul_le_mul hc (mul_le_mul_of_nonneg_left hLj hBj.le) (mul_nonneg hBj.le hLj0) hS)
          (mul_nonneg (norm_nonneg _) (mul_nonneg hBj.le hLj0)) (by positivity)
    _ = S * (1 + Real.log y) ^ j := by
        rw [show (1 / ((a : ℝ) + 1) ^ j) * (S * (((a : ℝ) + 1) ^ j * (1 + Real.log y) ^ j))
          = (1 / ((a : ℝ) + 1) ^ j * ((a : ℝ) + 1) ^ j) * (S * (1 + Real.log y) ^ j) by ring,
          one_div_mul_cancel hBj.ne', one_mul]

/-! ## Trivial zeros -/

theorem r14C_abs_r_add (a g k : ℕ) : 1 / 2 ≤ |r11Chi_r g k + a| := by
  unfold r11Chi_r
  rcases Nat.lt_or_ge a (2 * k + g) with h | h
  · have h' : ((a + 1 : ℕ) : ℝ) ≤ ((2 * k + g : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have h' : ((2 * k + g : ℕ) : ℝ) ≤ a := by exact_mod_cast h
    push_cast at h'
    rw [abs_of_nonneg (by linarith)]
    linarith

theorem r14C_abs_r_le (a g k : ℕ) :
    |r11Chi_r g k| ≤ (4 * (a : ℝ) + 2) * |r11Chi_r g k + a| := by
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have h1 := r14C_abs_r_add a g k
  have h2 : |r11Chi_r g k| ≤ |r11Chi_r g k + a| + a := by
    rw [abs_le]
    constructor <;> linarith [le_abs_self (r11Chi_r g k + a), neg_abs_le (r11Chi_r g k + a)]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha]

theorem r14C_inv_sq_le (a g k : ℕ) :
    1 / (r11Chi_r g k + a) ^ 2 ≤ (4 * (a : ℝ) + 2) ^ 2 * (1 / r11Chi_r g k ^ 2) := by
  have h := r14C_abs_r_le a g k
  have h1 := r14C_abs_r_add a g k
  have hr := r11Chi_r_ne g k
  have hpos : 0 < (r11Chi_r g k + a) ^ 2 := by
    rw [← sq_abs]
    exact pow_pos (by linarith) 2
  have hrpos : 0 < r11Chi_r g k ^ 2 := by
    rw [← sq_abs]
    exact pow_pos (abs_pos.mpr hr) 2
  have hsq : r11Chi_r g k ^ 2 ≤ (4 * (a : ℝ) + 2) ^ 2 * (r11Chi_r g k + a) ^ 2 := by
    rw [← sq_abs (r11Chi_r g k), ← sq_abs (r11Chi_r g k + a), ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [show (4 * (a : ℝ) + 2) ^ 2 * (1 / r11Chi_r g k ^ 2)
      = (4 * (a : ℝ) + 2) ^ 2 / r11Chi_r g k ^ 2 by ring, div_le_div_iff₀ hpos hrpos]
  linarith

theorem r14C_rpow_le (a : ℕ) {y : ℝ} (hy : 1 ≤ y) {x : ℝ}
    (hx : x * ((a : ℝ) + 1) ≤ a + 1 / 2) : (y ^ (a + 1)) ^ x ≤ y ^ a * Real.sqrt y := by
  have hy0 : 0 < y := by linarith
  rw [← Real.rpow_natCast y (a + 1), ← Real.rpow_mul hy0.le, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast y a, ← Real.rpow_add hy0]
  apply Real.rpow_le_rpow_of_exponent_le hy
  push_cast
  linarith

theorem r14C_gamma_term_le (a : ℕ) {j : ℕ} (hj : 1 ≤ j) (g k : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    ‖r14C_scal a j y * ((-(1 / ((a : ℂ) + 1))) * r11Chi_perron j (fun s =>
        1 / (s - r14C_sc a ((r11Chi_r g k : ℝ) : ℂ))
          - 1 / (2 - r14C_sc a ((r11Chi_r g k : ℝ) : ℂ))) (y ^ (a + 1)))‖
      ≤ ((a : ℝ) + 1) * (4 * (a : ℝ) + 2) ^ 2
        * ((2 * ((a : ℝ) + 1)) ^ j * Real.sqrt y + r14C_K a j * (1 + Real.log y) ^ j)
        * (1 / r11Chi_r g k ^ 2) := by
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hB : (0 : ℝ) < (a : ℝ) + 1 := by linarith
  have hy0 : 0 < y := by linarith
  have hY0 : 0 < y ^ (a + 1) := pow_pos hy0 _
  have hY1 : 1 ≤ y ^ (a + 1) := one_le_pow₀ hy
  have hra : 1 / 2 ≤ |r11Chi_r g k + a| := r14C_abs_r_add a g k
  have hinvr := r14C_inv_sq_le a g k
  have hrle : r11Chi_r g k ≤ 1 / 2 := by
    have := r11Chi_r_le g k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = r11Chi_r g k := ⟨_, rfl⟩
  rw [← hr] at hra hinvr hrle ⊢
  obtain ⟨ur, hur⟩ : ∃ ur : ℝ, ur = (r + a) / ((a : ℝ) + 1) := ⟨_, rfl⟩
  have hsc : r14C_sc a ((r : ℝ) : ℂ) = ((ur : ℝ) : ℂ) := by
    rw [hur]
    unfold r14C_sc
    simp
  have hurB : ur * ((a : ℝ) + 1) = r + a := by
    rw [hur]
    exact div_mul_cancel₀ _ hB.ne'
  have hur1 : ur ≤ 1 := by
    rw [hur, div_le_one hB]
    linarith
  have habs : |ur| = |r + a| / ((a : ℝ) + 1) := by rw [hur, abs_div, abs_of_pos hB]
  have hurpos : 0 < |ur| := by
    rw [habs]
    exact div_pos (by linarith) hB
  have hur0 : ur ≠ 0 := abs_pos.mp hurpos
  have hD : 1 ≤ 2 * ((a : ℝ) + 1) * |ur| := by
    rw [habs, show 2 * ((a : ℝ) + 1) * (|r + a| / ((a : ℝ) + 1))
      = 2 * |r + a| * (((a : ℝ) + 1) / ((a : ℝ) + 1)) by ring, div_self hB.ne']
    linarith
  have hnu : ‖((ur : ℝ) : ℂ)‖ = |ur| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hn2 : ‖(2 : ℂ) - ((ur : ℝ) : ℂ)‖ = 2 - ur := by
    rw [show (2 : ℂ) - (ur : ℂ) = ((2 - ur : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hu2 : |ur| ≤ 2 - ur := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [hsc, r13C_perron_pole hj (w := ((ur : ℝ) : ℂ)) (by rw [Complex.ofReal_re]; linarith)
    (Complex.ofReal_ne_zero.mpr hur0) hY1]
  have hN := r14C_scal_N_le a j hy (u := ((ur : ℝ) : ℂ)) (by rw [hnu]; exact hurpos)
    (by rw [hnu]; exact hD) (by rw [hnu, hn2]; exact hu2)
  rw [hnu, sq_abs] at hN
  have hosc : ‖r14C_scal a j y
        * (((y ^ (a + 1) : ℝ) : ℂ) ^ ((ur : ℝ) : ℂ) / ((ur : ℝ) : ℂ) ^ (j + 1))‖
      ≤ (2 * ((a : ℝ) + 1)) ^ j * Real.sqrt y * (1 / ur ^ 2) := by
    rw [norm_mul, norm_div, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hY0, Complex.ofReal_re,
      hnu]
    have h1 : (y ^ (a + 1)) ^ ur ≤ y ^ a * Real.sqrt y :=
      r14C_rpow_le a hy (by rw [hurB]; linarith)
    have h2 := r14C_inv_pow_le hurpos (D := 2 * ((a : ℝ) + 1)) (by linarith) hD (j := j)
      (n := j + 1) (by omega) (by omega)
    rw [sq_abs] at h2
    have hya : 0 < y ^ a := pow_pos hy0 _
    calc ‖r14C_scal a j y‖ * ((y ^ (a + 1)) ^ ur / |ur| ^ (j + 1))
        ≤ (1 / y ^ a) * (y ^ a * Real.sqrt y * ((2 * ((a : ℝ) + 1)) ^ j * (1 / ur ^ 2))) := by
          refine mul_le_mul (r14C_norm_scal_le_y a j hy) ?_ (by positivity) (by positivity)
          rw [div_eq_mul_one_div]
          exact mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (2 * ((a : ℝ) + 1)) ^ j * Real.sqrt y * (1 / ur ^ 2) := by
          rw [show (1 / y ^ a) * (y ^ a * Real.sqrt y * ((2 * ((a : ℝ) + 1)) ^ j * (1 / ur ^ 2)))
            = (1 / y ^ a * y ^ a) * ((2 * ((a : ℝ) + 1)) ^ j * Real.sqrt y * (1 / ur ^ 2)) by ring,
            one_div_mul_cancel hya.ne', one_mul]
  have hinv : 1 / ur ^ 2 ≤ ((a : ℝ) + 1) ^ 2 * ((4 * (a : ℝ) + 2) ^ 2 * (1 / r ^ 2)) := by
    have e : 1 / ur ^ 2 = ((a : ℝ) + 1) ^ 2 * (1 / (r + a) ^ 2) := by
      rw [hur, div_pow, one_div_div]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hinvr (by positivity)
  have hK0 := r14C_K_nonneg a j
  have hM0 : 0 ≤ (1 + Real.log y) ^ j := pow_nonneg (by linarith [Real.log_nonneg hy]) j
  have hE : 0 ≤ (2 * ((a : ℝ) + 1)) ^ j * Real.sqrt y + r14C_K a j * (1 + Real.log y) ^ j :=
    add_nonneg (mul_nonneg (pow_nonneg (by linarith) j) (Real.sqrt_nonneg y)) (mul_nonneg hK0 hM0)
  rw [mul_left_comm, norm_mul, norm_neg, norm_div, norm_one, r14C_norm_B, mul_sub]
  have hsub := (norm_sub_le _ _).trans (add_le_add hosc hN)
  calc 1 / ((a : ℝ) + 1) * _
      ≤ 1 / ((a : ℝ) + 1) * (((2 * ((a : ℝ) + 1)) ^ j * Real.sqrt y
          + r14C_K a j * (1 + Real.log y) ^ j)
            * (((a : ℝ) + 1) ^ 2 * ((4 * (a : ℝ) + 2) ^ 2 * (1 / r ^ 2)))) := by
        refine mul_le_mul_of_nonneg_left (hsub.trans ?_) (by positivity)
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_left hinv hE
    _ = _ := by
        rw [show 1 / ((a : ℝ) + 1) * (((2 * ((a : ℝ) + 1)) ^ j * Real.sqrt y
          + r14C_K a j * (1 + Real.log y) ^ j)
            * (((a : ℝ) + 1) ^ 2 * ((4 * (a : ℝ) + 2) ^ 2 * (1 / r ^ 2))))
          = (1 / ((a : ℝ) + 1) * ((a : ℝ) + 1)) * (((a : ℝ) + 1) * (4 * (a : ℝ) + 2) ^ 2
            * ((2 * ((a : ℝ) + 1)) ^ j * Real.sqrt y + r14C_K a j * (1 + Real.log y) ^ j)
            * (1 / r ^ 2)) by ring, one_div_mul_cancel hB.ne', one_mul]

theorem r14C_gamma_le (a : ℕ) {j : ℕ} (hj : 1 ≤ j) (g : ℕ) {y : ℝ} (hy : 1 ≤ y) {P : ℂ}
    (h : HasSum (fun k : ℕ => (-(1 / ((a : ℂ) + 1))) * r11Chi_perron j (fun s =>
        1 / (s - r14C_sc a ((r11Chi_r g k : ℝ) : ℂ))
          - 1 / (2 - r14C_sc a ((r11Chi_r g k : ℝ) : ℂ))) (y ^ (a + 1))) P) :
    ‖r14C_scal a j y * P‖ ≤ ((a : ℝ) + 1) * (4 * (a : ℝ) + 2) ^ 2
        * ((2 * ((a : ℝ) + 1)) ^ j * Real.sqrt y + r14C_K a j * (1 + Real.log y) ^ j)
        * ∑' k : ℕ, 1 / r11Chi_r g k ^ 2 :=
  (h.mul_left (r14C_scal a j y)).norm_le_of_bounded
    ((r11Chi_summable_inv_r_pow g (j := 2) le_rfl).hasSum.mul_left _)
    (fun k => r14C_gamma_term_le a hj g k hy)

/-! ## Non-trivial zeros -/

theorem r14C_zero_term (hGRH : DirichletLZerosOnLine) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (ρ : ℂ) (a : ℕ) {j : ℕ} (hj : 1 ≤ j) {y : ℝ} (hy : 1 ≤ y) :
    r14C_scal a j y * ((-((zeroOrd χ ρ : ℂ) / ((a : ℂ) + 1))) * r11Chi_perron j (fun s =>
          1 / (s - r14C_sc a (ρ + 1 / 2)) - 1 / (2 - r14C_sc a (ρ + 1 / 2))) (y ^ (a + 1)))
        + (zeroOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2 + a) ^ (j + 1)
      = (zeroOrd χ ρ : ℂ) / ((a : ℂ) + 1)
        * (r14C_scal a j y * r13C_N j (r14C_sc a (ρ + 1 / 2)) (Real.log (y ^ (a + 1)))) ∧
    ‖(zeroOrd χ ρ : ℂ) / ((a : ℂ) + 1)
        * (r14C_scal a j y * r13C_N j (r14C_sc a (ρ + 1 / 2)) (Real.log (y ^ (a + 1))))‖
      ≤ ((a : ℝ) + 1) * r14C_K a j * (1 + Real.log y) ^ j
        * ((zeroOrd χ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ 2) ∧
    ‖(zeroOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2 + a) ^ (j + 1)‖
      ≤ y * ((zeroOrd χ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ 2) := by
  by_cases h0 : zeroOrd χ ρ = 0
  · simp [h0]
  obtain ⟨hre, -⟩ := r11Chi_zero_geom hGRH χ h0
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hB : (0 : ℝ) < (a : ℝ) + 1 := by linarith
  have hBc := r14C_B_ne a
  have hy0 : 0 < y := by linarith
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy0.ne'
  have hY1 : 1 ≤ y ^ (a + 1) := one_le_pow₀ hy
  have hm0 : (0 : ℝ) ≤ (zeroOrd χ ρ : ℝ) := Nat.cast_nonneg _
  generalize ρ + 1 / 2 = w at hre ⊢
  have hw1 : 1 ≤ ‖w‖ := by
    have := Complex.re_le_norm w
    rw [hre] at this
    exact this
  have hwpos : 0 < ‖w‖ := by linarith
  have hwa : ‖w‖ ≤ ‖w + (a : ℂ)‖ := r14C_norm_le_add (by rw [hre]; norm_num) a
  have hwapos : 0 < ‖w + (a : ℂ)‖ := by linarith
  have hwa0 : w + (a : ℂ) ≠ 0 := norm_pos_iff.mp hwapos
  have hvre : (r14C_sc a w).re = 1 := by
    rw [r14C_sc_re, hre, div_eq_one_iff_eq hB.ne']
    ring
  have hv1 : 1 ≤ ‖r14C_sc a w‖ := by
    have := Complex.re_le_norm (r14C_sc a w)
    rw [hvre] at this
    exact this
  have hvpos : 0 < ‖r14C_sc a w‖ := by linarith
  have hv0 : r14C_sc a w ≠ 0 := norm_pos_iff.mp hvpos
  have hv2 : ‖r14C_sc a w‖ ≤ ‖2 - r14C_sc a w‖ := by
    have e : (2 : ℂ) - r14C_sc a w = (starRingEnd ℂ) (r14C_sc a w) := by
      apply Complex.ext
      · rw [Complex.sub_re, Complex.conj_re, hvre]
        norm_num
      · rw [Complex.sub_im, Complex.conj_im]
        simp
    rw [e, Complex.norm_conj]
  have hinv : 1 / ‖r14C_sc a w‖ ^ 2 ≤ ((a : ℝ) + 1) ^ 2 * (1 / ‖w‖ ^ 2) := by
    rw [r14C_norm_sc, show ((a : ℝ) + 1) ^ 2 * (1 / ‖w‖ ^ 2) = ((a : ℝ) + 1) ^ 2 / ‖w‖ ^ 2 by ring,
      div_pow, one_div_div]
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hwpos 2)
      (pow_le_pow_left₀ hwpos.le hwa 2)
  refine ⟨?_, ?_, ?_⟩
  · have e1 : (y : ℂ) ^ (w + (a : ℂ)) = (y : ℂ) ^ w * (y : ℂ) ^ a := by
      rw [Complex.cpow_add _ _ hyc, Complex.cpow_natCast]
    have e2 : (r14C_sc a w) ^ (j + 1) = (w + (a : ℂ)) ^ (j + 1) / ((a : ℂ) + 1) ^ (j + 1) := by
      unfold r14C_sc
      rw [div_pow]
    rw [r13C_perron_pole hj (by rw [hvre]; norm_num) hv0 hY1, r14C_cpow_scale hy0, e1, e2]
    generalize r13C_N j (r14C_sc a w) (Real.log (y ^ (a + 1))) = Nv
    unfold r14C_scal
    field_simp
    ring
  · rw [norm_mul, norm_div, Complex.norm_natCast, r14C_norm_B]
    have hN := r14C_scal_N_le a j hy (u := r14C_sc a w) hvpos
      (by nlinarith [mul_nonneg ha (norm_nonneg (r14C_sc a w))]) hv2
    have hKM : 0 ≤ r14C_K a j * (1 + Real.log y) ^ j :=
      mul_nonneg (r14C_K_nonneg a j) (pow_nonneg (by linarith [Real.log_nonneg hy]) j)
    calc (zeroOrd χ ρ : ℝ) / ((a : ℝ) + 1)
          * ‖r14C_scal a j y * r13C_N j (r14C_sc a w) (Real.log (y ^ (a + 1)))‖
        ≤ (zeroOrd χ ρ : ℝ) / ((a : ℝ) + 1)
          * (r14C_K a j * (1 + Real.log y) ^ j * (((a : ℝ) + 1) ^ 2 * (1 / ‖w‖ ^ 2))) := by
          refine mul_le_mul_of_nonneg_left (hN.trans ?_) (div_nonneg hm0 hB.le)
          exact mul_le_mul_of_nonneg_left hinv hKM
      _ = _ := by
          rw [show (zeroOrd χ ρ : ℝ) / ((a : ℝ) + 1)
              * (r14C_K a j * (1 + Real.log y) ^ j * (((a : ℝ) + 1) ^ 2 * (1 / ‖w‖ ^ 2)))
            = (((a : ℝ) + 1) / ((a : ℝ) + 1)) * (((a : ℝ) + 1) * r14C_K a j * (1 + Real.log y) ^ j
              * ((zeroOrd χ ρ : ℝ) / ‖w‖ ^ 2)) by ring, div_self hB.ne', one_mul]
  · rw [norm_div, norm_mul, Complex.norm_natCast, norm_pow,
      Complex.norm_cpow_eq_rpow_re_of_pos hy0, hre, Real.rpow_one,
      show y * ((zeroOrd χ ρ : ℝ) / ‖w‖ ^ 2) = (zeroOrd χ ρ : ℝ) * y / ‖w‖ ^ 2 by ring]
    refine div_le_div_of_nonneg_left (by positivity) (pow_pos hwpos 2) ?_
    calc ‖w‖ ^ 2 ≤ ‖w + (a : ℂ)‖ ^ 2 := pow_le_pow_left₀ hwpos.le hwa 2
      _ ≤ ‖w + (a : ℂ)‖ ^ (j + 1) := pow_le_pow_right₀ (by linarith) (by omega)

/-! ## The explicit formula of order `j` with shift `a` -/

theorem r14C_Phi_formula {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (hH : HadamardLogDeriv χ) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)
    (a : ℕ) {j : ℕ} (hj : 3 ≤ j) {y : ℝ} (hy : 1 ≤ y) :
    ∃ PA PB : ℂ,
      HasSum (fun k : ℕ => (-(1 / ((a : ℂ) + 1))) * r11Chi_perron j (fun s =>
        1 / (s - r14C_sc a ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))
          - 1 / (2 - r14C_sc a ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))) (y ^ (a + 1))) PA ∧
      HasSum (fun ρ : ℂ => (-((zeroOrd χ ρ : ℂ) / ((a : ℂ) + 1))) * r11Chi_perron j (fun s =>
        1 / (s - r14C_sc a (ρ + 1 / 2)) - 1 / (2 - r14C_sc a (ρ + 1 / 2))) (y ^ (a + 1))) PB ∧
      r14Phi χ a j y
        = r14C_scal a j y * (-(deriv (LFunction χ) (((a : ℝ) + 3 / 2 : ℝ) : ℂ)
            / LFunction χ (((a : ℝ) + 3 / 2 : ℝ) : ℂ)) * (Real.log (y ^ (a + 1)) : ℂ) ^ j)
          + (j.factorial : ℂ) * (r14C_scal a j y * PA)
          + (j.factorial : ℂ) * (r14C_scal a j y * PB) := by
  have hj1 : 1 ≤ j := by omega
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hB : (0 : ℝ) < (a : ℝ) + 1 := by linarith
  have hy0 : 0 < y := by linarith
  have hY0 : 0 < y ^ (a + 1) := pow_pos hy0 _
  have hY1 : 1 ≤ y ^ (a + 1) := one_le_pow₀ hy
  have hwk : ∀ k : ℕ, (-(1 / ((a : ℂ) + 1))) ≠ 0 →
      (r14C_sc a ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ)).re ≤ 3 / 2 := by
    intro k _
    rw [r14C_sc_re, Complex.ofReal_re, div_le_iff₀ hB]
    have := r11Chi_r_le (gammaShift χ) k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hwρ : ∀ ρ : ℂ, (-((zeroOrd χ ρ : ℂ) / ((a : ℂ) + 1))) ≠ 0 →
      (r14C_sc a (ρ + 1 / 2)).re ≤ 3 / 2 := by
    intro ρ h
    have h0 : zeroOrd χ ρ ≠ 0 := by
      intro h0; apply h; simp [h0]
    have := (zeroOrd_strip h0).2
    have e1 : (ρ + 1 / 2).re = ρ.re + 1 / 2 := by simp
    rw [r14C_sc_re, e1, div_le_iff₀ hB]
    linarith
  have hsk : Summable fun k : ℕ => ‖(-(1 / ((a : ℂ) + 1)))‖
      / (1 + ‖r14C_sc a ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ)‖) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((r11Chi_summable_gamma_weight (gammaShift χ)).mul_left ((a : ℝ) + 1))
    rw [norm_neg, norm_div, norm_one, r14C_norm_B, norm_neg, norm_one]
    exact r14C_weight_le a _ zero_le_one
  have hsρ : Summable fun ρ : ℂ => ‖(-((zeroOrd χ ρ : ℂ) / ((a : ℂ) + 1)))‖
      / (1 + ‖r14C_sc a (ρ + 1 / 2)‖) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_)
      ((r11Chi_summable_zero_weight χ hS).mul_left ((a : ℝ) + 1))
    rw [norm_neg, norm_div, Complex.norm_natCast, r14C_norm_B, norm_neg, Complex.norm_natCast]
    exact r14C_weight_le a _ (Nat.cast_nonneg _)
  refine ⟨_, _, r11Chi_perron_hasSum_poles hj _ _ hwk hsk hY0,
    r11Chi_perron_hasSum_poles hj _ _ hwρ hsρ hY0, ?_⟩
  have hviA := r11Chi_vi_poles hj _ _ hwk hsk
  have hviB := r11Chi_vi_poles hj _ _ hwρ hsρ
  set c0 : ℂ := -(deriv (LFunction χ) (((a : ℝ) + 3 / 2 : ℝ) : ℂ)
    / LFunction χ (((a : ℝ) + 3 / 2 : ℝ) : ℂ)) with hc0
  have hvic : VerticalIntegrable (fun s : ℂ => c0 / s ^ (j + 1)) 2 := r11Chi_vi_const hj1 c0
  have hviCA : VerticalIntegrable (fun s : ℂ => (c0 + ∑' k : ℕ, (-(1 / ((a : ℂ) + 1)))
      * (1 / (s - r14C_sc a ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))
        - 1 / (2 - r14C_sc a ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ)))) / s ^ (j + 1)) 2 := by
    have h := Integrable.add hvic hviA
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, add_div]
  have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have key : ∀ S c l : ℂ,
      (j.factorial : ℂ) * S * (c * (l / (j.factorial : ℂ))) = S * (c * l) := by
    intro S c l
    field_simp
  rw [r14C_Phi_eq_perron χ a hj1 hy0,
    r11Chi_perron_congr_line
      (f := fun s => LSeries (r11Chi_coeff χ) (((a : ℂ) + 1) * s - a))
      (g := fun s => (c0 + ∑' k : ℕ, (-(1 / ((a : ℂ) + 1)))
        * (1 / (s - r14C_sc a ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))
          - 1 / (2 - r14C_sc a ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))))
        + ∑' ρ : ℂ, (-((zeroOrd χ ρ : ℂ) / ((a : ℂ) + 1)))
          * (1 / (s - r14C_sc a (ρ + 1 / 2)) - 1 / (2 - r14C_sc a (ρ + 1 / 2))))
      (fun t => r14C_decomp_scaled χ hχ1 hH hS a (line_re 2 t)),
    r11Chi_perron_add hviCA hviB hY0, r11Chi_perron_add hvic hviA hY0, r11Chi_perron_const,
    r11Chi_perron_one hj1 hY1, mul_add, mul_add, key, mul_assoc, mul_assoc]

/-! ## Final arithmetic -/

theorem r14C_final {S0 F Bq W Dj K G Ga Z lq M s c1 a' b' : ℝ} (hS0 : 0 ≤ S0) (hF : 0 ≤ F)
    (hBq : 0 ≤ Bq) (hW : 0 ≤ W) (hDj : 0 ≤ Dj) (hK : 0 ≤ K) (hlq : 0 ≤ lq) (hM : 1 ≤ M)
    (hs : 0 ≤ s) (h1 : c1 ≤ S0 * M) (nA : a' ≤ Bq * W * (Dj * s + K * M) * Ga) (hGa : Ga ≤ G)
    (hGa0 : 0 ≤ Ga) (nB : b' ≤ Bq * K * M * Z) (hZ : Z ≤ lq / 2 + 2) :
    c1 + F * a' + F * b'
      ≤ (S0 + F * Bq * W * Dj * G + F * Bq * W * K * G + 2 * F * Bq * K) * (lq + 1) * M
        + (S0 + F * Bq * W * Dj * G + F * Bq * W * K * G + 2 * F * Bq * K) * s := by
  have hM0 : 0 ≤ M := by linarith
  have hG : 0 ≤ G := hGa0.trans hGa
  have hX : M ≤ (lq + 1) * M := by nlinarith
  have hX0 : 0 ≤ (lq + 1) * M := by positivity
  have u1 : S0 * M ≤ S0 * ((lq + 1) * M) := mul_le_mul_of_nonneg_left hX hS0
  have u2 : F * a' ≤ F * (Bq * W * (Dj * s + K * ((lq + 1) * M)) * G) := by
    refine mul_le_mul_of_nonneg_left (nA.trans ?_) hF
    refine mul_le_mul ?_ hGa hGa0 (by positivity)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := mul_le_mul_of_nonneg_left hX hK
    linarith
  have u3 : F * b' ≤ F * (Bq * K * ((lq + 1) * M) * 2) := by
    refine mul_le_mul_of_nonneg_left (nB.trans ?_) hF
    have hZ2 : Z ≤ 2 * (lq + 1) := by linarith
    have hBKM : 0 ≤ Bq * K * M := by positivity
    calc Bq * K * M * Z ≤ Bq * K * M * (2 * (lq + 1)) := mul_le_mul_of_nonneg_left hZ2 hBKM
      _ = Bq * K * ((lq + 1) * M) * 2 := by ring
  have n1 : 0 ≤ F * Bq * W * Dj * G * ((lq + 1) * M) := by positivity
  have n2 : 0 ≤ S0 * s := by positivity
  have n3 : 0 ≤ F * Bq * W * K * G * s := by positivity
  have n4 : 0 ≤ 2 * F * Bq * K * s := by positivity
  nlinarith [u1, u2, u3, n1, n2, n3, n4]

/-! ## (P2ₐ) -/

/-- **(P2ₐ)** `R14ChiExplicit a`, for every shift `a : ℕ`. -/
theorem r14C_main (a : ℕ) : R14ChiExplicit a := by
  intro hGRH j hj
  have hj1 : 1 ≤ j := by omega
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  refine ⟨(∑' n : ℕ, Λ n / (n : ℝ) ^ ((a : ℝ) + 3 / 2))
    + (j.factorial : ℝ) * ((a : ℝ) + 1) * (4 * (a : ℝ) + 2) ^ 2 * (2 * ((a : ℝ) + 1)) ^ j
      * ((∑' k : ℕ, 1 / r11Chi_r 0 k ^ 2) + ∑' k : ℕ, 1 / r11Chi_r 1 k ^ 2)
    + (j.factorial : ℝ) * ((a : ℝ) + 1) * (4 * (a : ℝ) + 2) ^ 2 * r14C_K a j
      * ((∑' k : ℕ, 1 / r11Chi_r 0 k ^ 2) + ∑' k : ℕ, 1 / r11Chi_r 1 k ^ 2)
    + 2 * (j.factorial : ℝ) * ((a : ℝ) + 1) * r14C_K a j, ?_⟩
  intro q _ χ hχ hχ1 y hy
  have hy0 : 0 < y := by linarith
  have hGr := growth_completedLFunction χ hχ1
  have hH := hadamardLogDeriv_of_growth χ hχ hχ1 hGr
  have hS := summable_zeroOrd_div_normSq_proof χ hχ hχ1 hGr
  obtain ⟨PA, PB, hA, hB, hΦ⟩ := r14C_Phi_formula χ hχ1 hH hS a hj hy
  have hZs := r13C_summable_Z2 χ hS
  have hT : Summable fun ρ : ℂ =>
      (zeroOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2 + a) ^ (j + 1) :=
    Summable.of_norm_bounded (hZs.mul_left y) fun ρ => (r14C_zero_term hGRH χ ρ a hj1 hy).2.2
  have hZ2 : r11Z χ 2 = ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ 2 := rfl
  have nB : ‖r14C_scal a j y * PB
        + ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2 + a) ^ (j + 1)‖
      ≤ ((a : ℝ) + 1) * r14C_K a j * (1 + Real.log y) ^ j * r11Z χ 2 := by
    rw [hZ2]
    refine ((hB.mul_left (r14C_scal a j y)).add hT.hasSum).norm_le_of_bounded
      (hZs.hasSum.mul_left _) fun ρ => ?_
    have z := r14C_zero_term hGRH χ ρ a hj1 hy
    calc _ = ‖(zeroOrd χ ρ : ℂ) / ((a : ℂ) + 1)
          * (r14C_scal a j y * r13C_N j (r14C_sc a (ρ + 1 / 2)) (Real.log (y ^ (a + 1))))‖ := by
          rw [← z.1]
      _ ≤ _ := z.2.1
  have nA := r14C_gamma_le a hj1 (gammaShift χ) hy hA
  have hGa0 : 0 ≤ ∑' k : ℕ, 1 / r11Chi_r (gammaShift χ) k ^ 2 :=
    tsum_nonneg fun k => by positivity
  have hGa : ∑' k : ℕ, 1 / r11Chi_r (gammaShift χ) k ^ 2
      ≤ (∑' k : ℕ, 1 / r11Chi_r 0 k ^ 2) + ∑' k : ℕ, 1 / r11Chi_r 1 k ^ 2 := by
    have hG00 : 0 ≤ ∑' k : ℕ, 1 / r11Chi_r 0 k ^ 2 := tsum_nonneg fun k => by positivity
    have hG10 : 0 ≤ ∑' k : ℕ, 1 / r11Chi_r 1 k ^ 2 := tsum_nonneg fun k => by positivity
    rcases gammaShift_cases χ with h | h <;> rw [h] <;> linarith
  have hZle := r13C_Z2_le hGRH χ hχ hχ1
  have hlq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hc0 := szs_norm_logDeriv_le χ (σ := (a : ℝ) + 3 / 2) (by linarith)
  have hS0 : 0 ≤ ∑' n : ℕ, Λ n / (n : ℝ) ^ ((a : ℝ) + 3 / 2) := (norm_nonneg _).trans hc0
  have hL0 : 0 ≤ Real.log y := Real.log_nonneg hy
  have hM1 : 1 ≤ (1 + Real.log y) ^ j := one_le_pow₀ (by linarith)
  have t1 := r14C_c0_le a j hy
    (c := -(deriv (LFunction χ) (((a : ℝ) + 3 / 2 : ℝ) : ℂ)
      / LFunction χ (((a : ℝ) + 3 / 2 : ℝ) : ℂ))) ((norm_neg _).le.trans hc0)
  have e : ∀ T : ℂ, r14Phi χ a j y + (j.factorial : ℂ) * T
      = r14C_scal a j y * (-(deriv (LFunction χ) (((a : ℝ) + 3 / 2 : ℝ) : ℂ)
            / LFunction χ (((a : ℝ) + 3 / 2 : ℝ) : ℂ)) * (Real.log (y ^ (a + 1)) : ℂ) ^ j)
        + (j.factorial : ℂ) * (r14C_scal a j y * PA)
        + (j.factorial : ℂ) * (r14C_scal a j y * PB + T) := by
    intro T
    rw [hΦ]
    ring
  rw [e]
  refine (norm_add₃_le).trans ?_
  rw [norm_mul (j.factorial : ℂ), norm_mul (j.factorial : ℂ), Complex.norm_natCast]
  exact r14C_final hS0 (Nat.cast_nonneg _) (by linarith) (by positivity)
    (pow_nonneg (by linarith) j) (r14C_K_nonneg a j) hlq hM1 (Real.sqrt_nonneg y) t1 nA hGa hGa0
    nB hZle

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r14C_main
