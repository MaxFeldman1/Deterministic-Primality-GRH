import DetPrimality.Bach.LLSZeta
import DetPrimality.Bach.SharpZeroSum

/-!
# The Hadamard constant `B = ξ'/ξ(0)` of the Riemann zeta function

* `llsZeta_deriv_xi_zero` : `ξ'(0) = B`, `B = log 2 + ½ log π - 1 - γ/2 = ½ log(4π) - 1 - γ/2`
  (`= -0.02309…`), via `ξ'(0) = -ξ'(1)` and the Laurent expansion of `ζ` at `1`;
* `llsZeta_zeroSumSq` : under RH, `∑ m_ρ/|ρ|² = -2B`;
* `llsZeta_zeroSumSq_le` : `∑ m_ρ/|ρ|² ≤ 0.0475 ≤ 1/20`.
-/

open Complex DirichletCharacter Filter Topology

namespace DetPrimality.Bach

/-- `B = ½ log(4π) - 1 - γ/2 = -0.02309…`. -/
noncomputable def llsZeta_B : ℝ :=
  Real.log 2 + Real.log Real.pi / 2 - 1 - Real.eulerMascheroniConstant / 2

theorem llsZeta_B_eq :
    llsZeta_B = Real.log (4 * Real.pi) / 2 - 1 - Real.eulerMascheroniConstant / 2 := by
  rw [llsZeta_B, Real.log_mul (by norm_num) Real.pi_ne_zero,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast; ring

/-- `g(s) = ξ(s) / (s Γ_ℝ(s))`, which is `(s - 1) ζ(s)` near `1`. -/
private noncomputable def llsZeta_g : ℂ → ℂ := fun s => llsZeta_xi s * (Gammaℝ s)⁻¹ * s⁻¹

private lemma llsZeta_g_one : llsZeta_g 1 = 1 := by simp [llsZeta_g, Gammaℝ_one]

private lemma llsZeta_g_eq {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    llsZeta_g s = (s - 1) * riemannZeta s := by
  have h0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hΓ := Gammaℝ_ne_zero_of_re_pos hs
  rw [llsZeta_g, llsZeta_xi_eq_zeta hs h1]
  field_simp

private lemma llsZeta_g_hasDerivAt :
    HasDerivAt llsZeta_g (Real.eulerMascheroniConstant : ℂ) 1 := by
  rw [hasDerivAt_iff_tendsto_slope]
  refine tendsto_riemannZeta_sub_one_div.congr' ?_
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hmem : {s : ℂ | 0 < s.re} ∈ 𝓝[≠] (1 : ℂ) :=
    mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds (by simp))
  filter_upwards [hmem, self_mem_nhdsWithin] with s hs h1
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [slope_def_field, llsZeta_g_one, llsZeta_g_eq hs h1]
  field_simp

private lemma llsZeta_logDeriv_Gammaℝ_one :
    deriv Gammaℝ 1 = ((-(Real.log Real.pi) / 2 - Real.log 2
      - Real.eulerMascheroniConstant / 2 : ℝ) : ℂ) := by
  have h := logDeriv_Gammaℝ (s := 1) (by simp)
  have hlog : Complex.log 2 = (Real.log 2 : ℂ) := by
    rw [Complex.ofReal_log (by norm_num)]; norm_num
  rw [Gammaℝ_one, div_one, digamma_one_half, hlog] at h
  rw [h]; push_cast; ring

/-- `ξ'(1) = 1 + γ/2 - ½ log π - log 2`. -/
theorem llsZeta_deriv_xi_one : deriv llsZeta_xi 1 = ((-llsZeta_B : ℝ) : ℂ) := by
  have hΓd : HasDerivAt Gammaℝ (deriv Gammaℝ 1) 1 :=
    (differentiableAt_Gammaℝ_of_re_pos (by simp)).hasDerivAt
  have hprod := ((hasDerivAt_id (1 : ℂ)).mul hΓd).mul llsZeta_g_hasDerivAt
  have hev : llsZeta_xi =ᶠ[𝓝 1] fun s => s * Gammaℝ s * llsZeta_g s := by
    have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (show (1 : ℂ) ∈ {s : ℂ | 0 < s.re} by simp)] with s hs
    have h0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
    have hΓ := Gammaℝ_ne_zero_of_re_pos hs
    simp only [llsZeta_g]
    field_simp
  have hev' : llsZeta_xi =ᶠ[𝓝 1] id * Gammaℝ * llsZeta_g := hev
  have := (hprod.congr_of_eventuallyEq hev').deriv
  simp only [id_eq, Pi.mul_apply] at this
  rw [this, llsZeta_g_one, Gammaℝ_one, llsZeta_logDeriv_Gammaℝ_one, llsZeta_B]
  push_cast; ring

/-- **`B = ξ'/ξ(0) = ξ'(0) = ½ log(4π) - 1 - γ/2`**; in particular it is real. -/
theorem llsZeta_deriv_xi_zero : deriv llsZeta_xi 0 = (llsZeta_B : ℂ) := by
  rw [llsZeta_deriv_zero, llsZeta_deriv_xi_one]; push_cast; ring

/-- **Hadamard partial fraction for `ξ`**, with the explicit real constant `B`. -/
theorem llsZeta_hadamard {s : ℂ} (hs : llsZeta_xi s ≠ 0) :
    deriv llsZeta_xi s / llsZeta_xi s = (llsZeta_B : ℂ)
      + ∑' ρ : ℂ, (zeroOrd (1 : DirichletCharacter ℂ 1) ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
  rw [llsZeta_logDeriv_eq_tsum hs, llsZeta_deriv_xi_zero]

/-- `B = -∑ m_ρ Re (1/ρ)` (unconditional). -/
theorem llsZeta_B_eq_neg_tsum :
    llsZeta_B = -∑' ρ : ℂ, (zeroOrd (1 : DirichletCharacter ℂ 1) ρ : ℝ) * (1 / ρ).re := by
  rw [← llsZeta_deriv_zero_re, llsZeta_deriv_xi_zero, Complex.ofReal_re]

/-- Under RH, `∑ m_ρ/|ρ|² = -2B`. -/
theorem llsZeta_zeroSumSq (hGRH : DirichletLZerosOnLine) :
    zeroSumSq (1 : DirichletCharacter ℂ 1) = -2 * llsZeta_B := by
  rw [llsZeta_zeroSumSq_eq hGRH, llsZeta_deriv_xi_zero, Complex.ofReal_re]

/-- **Decomposition of `-ζ'/ζ`** for `Re s > 1`:
`-ζ'/ζ(s) = 1/s + 1/(s-1) - ½ log π + ½ ψ(s/2) - B - ∑_ρ m_ρ (1/(s-ρ) + 1/ρ)`. -/
theorem llsZeta_neg_logDeriv_zeta_B {s : ℂ} (hs : 1 < s.re) :
    -(deriv riemannZeta s / riemannZeta s)
      = 1 / s + 1 / (s - 1) + (-(Real.log Real.pi : ℂ) / 2 + digamma (s / 2) / 2)
        - (llsZeta_B : ℂ)
        - ∑' ρ : ℂ, (zeroOrd (1 : DirichletCharacter ℂ 1) ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
  rw [llsZeta_neg_logDeriv_zeta hs, llsZeta_deriv_xi_zero]

/-! ### Numerics -/

theorem llsZeta_cert_harmonic : harmonic 1024 ≤ (750918 / 100000 : ℚ) := by decide +kernel

theorem llsZeta_gamma_lt : Real.eulerMascheroniConstant < 0.57771 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 1024
  rw [Real.eulerMascheroniSeq', if_neg (by norm_num)] at h
  have hH := (Rat.cast_le (K := ℝ)).mpr llsZeta_cert_harmonic
  rw [show ((750918 / 100000 : ℚ) : ℝ) = 750918 / 100000 by norm_num] at hH
  have hl : Real.log ((1024 : ℕ) : ℝ) = 10 * Real.log 2 := by
    rw [show (((1024 : ℕ) : ℝ)) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  rw [hl] at h
  linarith [Real.log_two_gt_d9]

/-- `-0.0238 ≤ B`: the constant `2|B|` is `≤ 0.0475` (true value `0.04618…`). -/
theorem llsZeta_neg_two_B_le : -2 * llsZeta_B ≤ 0.0475 := by
  have h1 := llsZeta_gamma_lt
  have h2 := szs_log_pi_gt
  have h3 := Real.log_two_gt_d9
  rw [llsZeta_B]
  linarith

theorem llsZeta_B_nonpos (hGRH : DirichletLZerosOnLine) : llsZeta_B ≤ 0 := by
  have h : 0 ≤ zeroSumSq (1 : DirichletCharacter ℂ 1) :=
    tsum_nonneg fun ρ => by positivity
  rw [llsZeta_zeroSumSq hGRH] at h
  linarith

/-- Under RH, `∑ m_ρ/|ρ|² = 2|B| ≤ 0.0475`. -/
theorem llsZeta_zeroSumSq_le (hGRH : DirichletLZerosOnLine) :
    zeroSumSq (1 : DirichletCharacter ℂ 1) ≤ 0.0475 := by
  rw [llsZeta_zeroSumSq hGRH]; exact llsZeta_neg_two_B_le

theorem llsZeta_zeroSumSq_eq_abs (hGRH : DirichletLZerosOnLine) :
    zeroSumSq (1 : DirichletCharacter ℂ 1) = 2 * |llsZeta_B| := by
  rw [llsZeta_zeroSumSq hGRH, abs_of_nonpos (llsZeta_B_nonpos hGRH)]; ring

theorem llsZeta_zeroSumSq_le_one_div_twenty (hGRH : DirichletLZerosOnLine) :
    zeroSumSq (1 : DirichletCharacter ℂ 1) ≤ 1 / 20 :=
  (llsZeta_zeroSumSq_le hGRH).trans (by norm_num)

end DetPrimality.Bach

#print axioms DetPrimality.Bach.llsZeta_growth
#print axioms DetPrimality.Bach.llsZeta_hadamard
#print axioms DetPrimality.Bach.llsZeta_summable
#print axioms DetPrimality.Bach.llsZeta_B_eq_neg_tsum
#print axioms DetPrimality.Bach.llsZeta_zeroSumSq_le
#print axioms DetPrimality.Bach.llsZeta_zeroSumSq_eq_abs
#print axioms DetPrimality.Bach.llsZeta_neg_logDeriv_zeta_B
#print axioms DetPrimality.Bach.llsZeta_zeroOrd_eq_order
