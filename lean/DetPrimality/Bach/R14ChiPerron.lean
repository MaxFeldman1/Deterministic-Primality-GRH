import DetPrimality.Bach.R14Defs
import DetPrimality.Bach.R11ChiFormula

/-!
# Round 14, (P2ₐ): Perron representation of `Φ^{(a)}_{χ,j}` (formal0760 §1.2)

* `r14C_perron_gen` : Perron identity for a general Dirichlet series `∑ c_n λ_n^{-s}` (`λ_n > 0`,
  `∑ |c_n| λ_n^{-2} < ∞`) with the kernel `y^s / s^{j+1}` on the line `Re s = 2`;
* `r14C_Phi_eq_perron` : with `β = a + 1`, `λ_n = n^β`, `c_n = Λ(n) χ(n) √n n^a`:
  `Φ^{(a)}_{χ,j}(y) = j! β^{-j} y^{-a} · P_j[s ↦ D(β s - a)](y^β)`, `D = LSeries (r11Chi_coeff χ)`.
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## Perron identity for general frequencies -/

/-- **Perron identity** for `∑ c_n λ_n^{-s}` with the kernel `y^s/s^{j+1}` (`j ≥ 1`). -/
theorem r14C_perron_gen {j : ℕ} (hj : 1 ≤ j) (c : ℕ → ℂ) (lam : ℕ → ℝ) (hlam : ∀ n, 0 < lam n)
    (hs : Summable fun n => ‖c n‖ / lam n ^ 2) {y : ℝ} (hy : 0 < y) :
    r11Chi_perron j (fun s => ∑' n : ℕ, c n * ((lam n : ℝ) : ℂ) ^ (-s)) y
      = ∑' n : ℕ, c n * (if lam n ≤ y then
          ((Real.log (y / lam n) : ℝ) : ℂ) ^ j / (j.factorial : ℂ) else 0) := by
  set K : ℂ → ℂ := fun s => 1 / s ^ (j + 1) with hK
  set F : ℕ → ℝ → ℂ := fun n t =>
    c n * ((((lam n) / y : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + t * I)) • K (((2 : ℝ) : ℂ) + t * I))
    with hFdef
  have hpos : ∀ n : ℕ, 0 < lam n / y := fun n => div_pos (hlam n) hy
  have hpt : ∀ t : ℝ, ((y⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + t * I)) •
      (fun s => (∑' n : ℕ, c n * ((lam n : ℝ) : ℂ) ^ (-s)) / s ^ (j + 1))
        (((2 : ℝ) : ℂ) + t * I) = ∑' n : ℕ, F n t := by
    intro t
    set s : ℂ := ((2 : ℝ) : ℂ) + t * I with hs'
    simp only
    rw [smul_eq_mul, ← tsum_div_const, ← tsum_mul_left]
    congr 1
    funext n
    simp only [hFdef]
    rw [smul_eq_mul, hK]
    have hcp : (((lam n) / y : ℝ) : ℂ) ^ (-s)
        = ((y⁻¹ : ℝ) : ℂ) ^ (-s) * ((lam n : ℝ) : ℂ) ^ (-s) := by
      rw [div_eq_mul_inv, ofReal_mul, mul_cpow_ofReal_nonneg (hlam n).le (inv_nonneg.mpr hy.le)]
      ring
    rw [hcp]
    ring
  have hKint : VerticalIntegrable K 2 := r11Chi_vi_const hj 1
  have hFint : ∀ n, Integrable (F n) := by
    intro n
    have h := (integrable_mellinInv_integrand hKint (hpos n)).const_mul (c n)
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp [hFdef, hK]
  set C : ℝ := ∫ t : ℝ, ‖K (((2 : ℝ) : ℂ) + t * I)‖ with hC
  have hFnorm : ∀ n, ∫ t, ‖F n t‖ = ‖c n‖ / lam n ^ 2 * (y ^ 2 * C) := by
    intro n
    have hpt' : ∀ t : ℝ, ‖F n t‖ = (‖c n‖ * (lam n / y) ^ (-(2 : ℝ)))
        * ‖K (((2 : ℝ) : ℂ) + t * I)‖ := by
      intro t
      simp only [hFdef, norm_mul, norm_smul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (hpos n)]
      have : (-(((2 : ℝ) : ℂ) + t * I)).re = -2 := by simp
      rw [this]
      ring
    rw [integral_congr_ae (Eventually.of_forall hpt'), integral_const_mul, ← hC,
      Real.rpow_neg (div_nonneg (hlam n).le hy.le), Real.div_rpow (hlam n).le hy.le,
      Real.rpow_two, Real.rpow_two]
    have hl := (hlam n).ne'
    have hy' := hy.ne'
    field_simp
  have hsum : Summable fun n => ∫ t, ‖F n t‖ := by
    have h := hs.mul_right (y ^ 2 * C)
    exact h.congr fun n => (hFnorm n).symm
  have hint := integral_tsum_of_summable_integral_norm hFint hsum
  have hFn : ∀ n, ∫ t, F n t = c n * ((2 * Real.pi : ℂ)
        * (if lam n / y ≤ 1 then (-((Real.log (lam n / y) : ℝ) : ℂ)) ^ j / (j.factorial : ℂ)
          else 0)) := by
    intro n
    simp only [hFdef]
    rw [integral_const_mul, r11Chi_kernel_integral hj (hpos n)]
  unfold r11Chi_perron mellinInv
  rw [integral_congr_ae (Eventually.of_forall hpt), ← hint]
  simp_rw [hFn]
  rw [Complex.real_smul, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  have hiff : lam n / y ≤ 1 ↔ lam n ≤ y := div_le_one hy
  have hlog : Real.log (lam n / y) = -Real.log (y / lam n) := by
    rw [← Real.log_inv, inv_div]
  by_cases h : lam n ≤ y
  · rw [if_pos (hiff.mpr h), if_pos h, hlog]
    push_cast
    field_simp
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
    simp

/-! ## The scaled frequencies `λ_n = n^{a+1}` -/

/-- `λ_n = n^{a+1}` (and `1` at `n = 0`). -/
noncomputable def r14C_lam (a n : ℕ) : ℝ := if n = 0 then 1 else (n : ℝ) ^ (a + 1)

theorem r14C_lam_pos (a n : ℕ) : 0 < r14C_lam a n := by
  unfold r14C_lam
  split_ifs with h
  · exact one_pos
  · exact pow_pos (by exact_mod_cast Nat.pos_of_ne_zero h) _

theorem r14C_lam_of_ne (a : ℕ) {n : ℕ} (h : n ≠ 0) : r14C_lam a n = (n : ℝ) ^ (a + 1) :=
  if_neg h

/-- `c_n = χ(n) Λ(n) √n · n^a`. -/
noncomputable def r14C_coeff {N : ℕ} (χ : DirichletCharacter ℂ N) (a n : ℕ) : ℂ :=
  r11Chi_coeff χ n * (n : ℂ) ^ a

theorem r14C_coeff_zero {N : ℕ} (χ : DirichletCharacter ℂ N) (a : ℕ) : r14C_coeff χ a 0 = 0 := by
  simp [r14C_coeff, r11Chi_coeff]

/-- The normalising factor `β^{-j} y^{-a}`, `β = a + 1`. -/
noncomputable def r14C_scal (a j : ℕ) (y : ℝ) : ℂ := 1 / ((a : ℂ) + 1) ^ j / (y : ℂ) ^ a

theorem r14C_summable_coeff {N : ℕ} (χ : DirichletCharacter ℂ N) (a : ℕ) :
    Summable fun n : ℕ => ‖r14C_coeff χ a n‖ / r14C_lam a n ^ 2 := by
  have h := (r11Chi_summable_coeff χ).norm
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h
  rcases eq_or_ne n 0 with rfl | hn
  · simp [r14C_coeff_zero]
  · rw [LSeries.norm_term_eq, if_neg hn, r14C_lam_of_ne a hn, r14C_coeff, norm_mul, norm_pow,
      Complex.norm_natCast]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have h2 : (2 : ℂ).re = 2 := by simp
    rw [h2, Real.rpow_two]
    have hpow : (1 : ℝ) ≤ (n : ℝ) ^ a := one_le_pow₀ hn1
    have hn0 : (0 : ℝ) < n := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e : ((n : ℝ) ^ (a + 1)) ^ 2 = (n : ℝ) ^ a * (n : ℝ) ^ 2 * (n : ℝ) ^ a := by ring
    rw [e]
    have hc := norm_nonneg (r11Chi_coeff χ n)
    have h3 : (n : ℝ) ^ a * (n : ℝ) ^ 2 * 1 ≤ (n : ℝ) ^ a * (n : ℝ) ^ 2 * (n : ℝ) ^ a :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have h4 := mul_le_mul_of_nonneg_left h3 hc
    linarith

theorem r14C_term_eq {N : ℕ} (χ : DirichletCharacter ℂ N) (a : ℕ) (s : ℂ) (n : ℕ) :
    LSeries.term (r11Chi_coeff χ) (((a : ℂ) + 1) * s - a) n
      = r14C_coeff χ a n * ((r14C_lam a n : ℝ) : ℂ) ^ (-s) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [r14C_coeff_zero]
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hlam : (0 : ℝ) < (n : ℝ) ^ (a + 1) := pow_pos hnpos _
    have hlamc : (((n : ℝ) ^ (a + 1) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
    have hpowa : (n : ℂ) ^ a = Complex.exp ((a : ℂ) * Complex.log n) := by
      rw [Complex.exp_nat_mul, Complex.exp_log hn0]
    rw [LSeries.term_of_ne_zero hn, r14C_lam_of_ne a hn, r14C_coeff, hpowa,
      Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hlamc,
      ← Complex.ofReal_log hlam.le, Real.log_pow, div_eq_mul_inv, ← Complex.exp_neg, mul_assoc,
      ← Complex.exp_add]
    congr 2
    rw [← Complex.natCast_log]
    push_cast
    ring

/-! ## `Φ^{(a)}_{χ,j}` as a Perron integral -/

/-- `Φ^{(a)}_{χ,j}(y) = j! β^{-j} y^{-a} · P_j[s ↦ D(βs - a)](y^β)`, `β = a + 1`. -/
theorem r14C_Phi_eq_perron {N : ℕ} (χ : DirichletCharacter ℂ N) (a : ℕ) {j : ℕ} (hj : 1 ≤ j)
    {y : ℝ} (hy : 0 < y) :
    r14Phi χ a j y = (j.factorial : ℂ) * r14C_scal a j y
      * r11Chi_perron j (fun s => LSeries (r11Chi_coeff χ) (((a : ℂ) + 1) * s - a))
          (y ^ (a + 1)) := by
  have hj0 : j ≠ 0 := by omega
  have hY : 0 < y ^ (a + 1) := pow_pos hy _
  have hfun : (fun s : ℂ => LSeries (r11Chi_coeff χ) (((a : ℂ) + 1) * s - a))
      = fun s => ∑' n : ℕ, r14C_coeff χ a n * ((r14C_lam a n : ℝ) : ℂ) ^ (-s) :=
    funext fun s => tsum_congr fun n => r14C_term_eq χ a s n
  have hzero : ∀ n ∉ Finset.range ⌈y⌉₊, r14C_coeff χ a n * (if r14C_lam a n ≤ y ^ (a + 1) then
      ((Real.log (y ^ (a + 1) / r14C_lam a n) : ℝ) : ℂ) ^ j / (j.factorial : ℂ) else 0) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt, Nat.ceil_le] at hn
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le hy hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at hnpos
    rw [r14C_lam_of_ne a hn0]
    have hge : y ^ (a + 1) ≤ (n : ℝ) ^ (a + 1) := pow_le_pow_left₀ hy.le hn _
    split_ifs with h
    · rw [le_antisymm h hge, div_self hY.ne', Real.log_one]
      simp [hj0]
    · simp
  rw [hfun, r14C_perron_gen hj (r14C_coeff χ a) (r14C_lam a) (r14C_lam_pos a)
    (r14C_summable_coeff χ a) hY, tsum_eq_sum hzero, Finset.mul_sum]
  unfold r14Phi
  refine Finset.sum_congr rfl fun n hn => ?_
  have hny : (n : ℝ) < y := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [r14C_coeff_zero]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hle : (n : ℝ) ^ (a + 1) ≤ y ^ (a + 1) := pow_le_pow_left₀ hnpos.le hny.le _
    have hlog : Real.log (y ^ (a + 1) / (n : ℝ) ^ (a + 1))
        = ((a : ℝ) + 1) * Real.log (y / n) := by
      rw [← div_pow, Real.log_pow, Nat.cast_add_one]
    rw [r14C_lam_of_ne a hn0, if_pos hle, hlog]
    have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    have hB : (a : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero a
    have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    simp only [r14C_coeff, r11Chi_coeff, r14C_scal]
    push_cast
    rw [div_pow, mul_pow]
    field_simp

end DetPrimality.Bach
