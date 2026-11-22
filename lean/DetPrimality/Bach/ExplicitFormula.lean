import DetPrimality.Bach.Handoffs
import DetPrimality.Bach.ExplicitPerron
import DetPrimality.Bach.ExplicitDigamma

/-!
# The smoothed explicit formula (blueprint §3)

Target: `explicit_formula_bound_of_hadamard`, with exactly the conclusion of
`explicit_formula_bound` in `Blueprint.lean`, assuming `HadamardLogDeriv χ` and `∑ 1/|ρ|² < ∞`.

Structure (`I[g](x) := perronI g x = (1/2πi) ∫_{(2)} g(s) x^s ds / (s(s+1))`):
* Step 1 `smoothPsi_eq_perronI`  : `S(x) = I[-L'/L](x)`                      (proved)
* Step 2 `neg_logDeriv_decomp`   : on `Re s > 1`,
    `-L'/L(s) = -L'/L(2) + (G(s) - G(2)) - ∑_ρ m_ρ (1/(s-ρ) - 1/(2-ρ))`    (proved from `hH`, `hS`)
* Step 3 `perronI_one`, `perronI_inv_sub`, `perronI_zeroTerm`, `perronI_trivTerm`  (proved)
* `hasSum_gammaFactor_logDeriv_sub` : `G(s) - G(2) = ∑_k (1/(2k+a+2) - 1/(s+2k+a))` (proved)
* Step 4: `gamma_part` (`ExplicitGamma.lean`), `zero_part` (`ExplicitZeros.lean`, using
  `ExplicitKernel.lean`, `ExplicitWeight.lean`).
* Assembly `explicit_formula_bound_of_hadamard` (`ExplicitMain.lean`).  Everything is sorry-free.
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `perronI g x = (1/2πi) ∫_{(2)} g(s) x^s / (s(s+1)) ds`, written as a Mellin inverse
transform evaluated at `1/x`. -/
noncomputable def perronI (g : ℂ → ℂ) (x : ℝ) : ℂ :=
  mellinInv 2 (fun s => g s / (s * (s + 1))) x⁻¹

/-! ## Linearity -/

section Linear

variable {σ : ℝ}

theorem integrable_mellinInv_integrand {F : ℂ → ℂ} (hF : VerticalIntegrable F σ) {x : ℝ}
    (hx : 0 < x) :
    Integrable (fun y : ℝ => (x : ℂ) ^ (-((σ : ℂ) + y * I)) • F (σ + y * I)) := by
  have hc : Continuous (fun y : ℝ => (x : ℂ) ^ (-((σ : ℂ) + y * I))) :=
    Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx.ne'))
  refine Integrable.mono' ((Integrable.norm hF).const_mul (x ^ (-σ)))
    (hc.aestronglyMeasurable.smul (Integrable.aestronglyMeasurable hF))
    (Eventually.of_forall fun y => ?_)
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have : (-((σ : ℂ) + y * I)).re = -σ := by simp
  rw [this]

theorem mellinInv_add {F G : ℂ → ℂ} (hF : VerticalIntegrable F σ) (hG : VerticalIntegrable G σ)
    {x : ℝ} (hx : 0 < x) :
    mellinInv σ (fun s => F s + G s) x = mellinInv σ F x + mellinInv σ G x := by
  unfold mellinInv
  rw [← smul_add, ← integral_add (integrable_mellinInv_integrand hF hx)
    (integrable_mellinInv_integrand hG hx)]
  refine congrArg _ (integral_congr_ae (Eventually.of_forall fun y => ?_))
  simp only [smul_add]

theorem mellinInv_sub {F G : ℂ → ℂ} (hF : VerticalIntegrable F σ) (hG : VerticalIntegrable G σ)
    {x : ℝ} (hx : 0 < x) :
    mellinInv σ (fun s => F s - G s) x = mellinInv σ F x - mellinInv σ G x := by
  unfold mellinInv
  rw [← smul_sub, ← integral_sub (integrable_mellinInv_integrand hF hx)
    (integrable_mellinInv_integrand hG hx)]
  refine congrArg _ (integral_congr_ae (Eventually.of_forall fun y => ?_))
  simp only [smul_sub]

theorem mellinInv_const_mul (c : ℂ) (F : ℂ → ℂ) (x : ℝ) :
    mellinInv σ (fun s => c * F s) x = c * mellinInv σ F x := by
  unfold mellinInv
  simp only [smul_eq_mul]
  rw [show (fun y : ℝ => (x : ℂ) ^ (-((σ : ℂ) + y * I)) * (c * F (σ + y * I)))
      = fun y : ℝ => c * ((x : ℂ) ^ (-((σ : ℂ) + y * I)) * F (σ + y * I)) by
    funext y; ring, integral_const_mul]
  simp only [Complex.real_smul]
  ring

end Linear

theorem perronI_add {f g : ℂ → ℂ} (hf : VerticalIntegrable (fun s => f s / (s * (s + 1))) 2)
    (hg : VerticalIntegrable (fun s => g s / (s * (s + 1))) 2) {x : ℝ} (hx : 0 < x) :
    perronI (fun s => f s + g s) x = perronI f x + perronI g x := by
  unfold perronI
  rw [show (fun s : ℂ => (f s + g s) / (s * (s + 1)))
      = fun s => f s / (s * (s + 1)) + g s / (s * (s + 1)) from funext fun s => add_div _ _ _]
  exact mellinInv_add hf hg (inv_pos.mpr hx)

theorem perronI_sub {f g : ℂ → ℂ} (hf : VerticalIntegrable (fun s => f s / (s * (s + 1))) 2)
    (hg : VerticalIntegrable (fun s => g s / (s * (s + 1))) 2) {x : ℝ} (hx : 0 < x) :
    perronI (fun s => f s - g s) x = perronI f x - perronI g x := by
  unfold perronI
  rw [show (fun s : ℂ => (f s - g s) / (s * (s + 1)))
      = fun s => f s / (s * (s + 1)) - g s / (s * (s + 1)) from funext fun s => sub_div _ _ _]
  exact mellinInv_sub hf hg (inv_pos.mpr hx)

theorem perronI_const (c : ℂ) (x : ℝ) :
    perronI (fun _ => c) x = c * perronI (fun _ => 1) x := by
  unfold perronI
  rw [← mellinInv_const_mul]
  congr 1
  funext s
  ring

theorem perronI_congr_line {f g : ℂ → ℂ} (h : ∀ y : ℝ, f ((2 : ℝ) + y * I) = g ((2 : ℝ) + y * I))
    (x : ℝ) : perronI f x = perronI g x := by
  unfold perronI
  exact mellinInv_congr_line (fun y => by simp only [h y]) _

theorem verticalIntegrable_const_kernel (c : ℂ) :
    VerticalIntegrable (fun s : ℂ => c / (s * (s + 1))) 2 := by
  have h := (verticalIntegrable_kernel (c := 2) two_pos).const_mul c
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only
  ring

/-! ## Step 3: explicit inverse transforms -/

theorem perronI_one {x : ℝ} (hx : 1 ≤ x) : perronI (fun _ => 1) x = 1 - 1 / (x : ℂ) := by
  have hx0 : 0 < x := by linarith
  unfold perronI
  rw [mellinInv_kernel two_pos (inv_pos.mpr hx0), if_pos (inv_le_one_of_one_le₀ hx)]
  push_cast
  ring

theorem ofReal_inv_cpow_neg {x : ℝ} (hx : 0 < x) (w : ℂ) :
    ((x⁻¹ : ℝ) : ℂ) ^ (-w) = (x : ℂ) ^ w := by
  rw [ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm),
    cpow_neg, inv_inv]

/-- `I[1/(s-w)](x) = x^w/(w(w+1)) - 1/w + 1/((w+1)x)` for `Re w < 2`, `w ≠ 0, -1`, `x ≥ 1`. -/
theorem perronI_inv_sub {w : ℂ} (hw : w.re < 2) (hw0 : w ≠ 0) (hw1 : w + 1 ≠ 0) {x : ℝ}
    (hx : 1 ≤ x) :
    perronI (fun s => 1 / (s - w)) x
      = (x : ℂ) ^ w / (w * (w + 1)) - 1 / w + 1 / ((w + 1) * x) := by
  have hx0 : 0 < x := by linarith
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  unfold perronI
  rw [show (fun s : ℂ => 1 / (s - w) / (s * (s + 1))) = fun s => 1 / (s * (s + 1) * (s - w)) by
    funext s; rw [div_div, mul_comm (s - w)]]
  rw [mellinInv_kernel_inv_sub two_pos hw hw0 hw1 (inv_pos.mpr hx0),
    if_pos (inv_le_one_of_one_le₀ hx), ofReal_inv_cpow_neg hx0]
  push_cast
  field_simp
  ring

theorem verticalIntegrable_inv_sub {w : ℂ} (hw : w.re < 2) :
    VerticalIntegrable (fun s : ℂ => 1 / (s - w) / (s * (s + 1))) 2 := by
  refine (verticalIntegrable_kernel_inv_sub (c := 2) two_pos hw).congr
    (Eventually.of_forall fun y => ?_)
  simp only
  rw [div_div, mul_comm (_ - w)]

/-- The contribution of one nontrivial zero. -/
noncomputable def zeroTerm (ρ : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 2 / (ρ * (2 - ρ)) + 3 / ((ρ + 1) * (2 - ρ) * x)

theorem perronI_inv_sub_sub {w : ℂ} (hw : w.re < 2) (hw0 : w ≠ 0) (hw1 : w + 1 ≠ 0) {x : ℝ}
    (hx : 1 ≤ x) :
    perronI (fun s => 1 / (s - w) - 1 / (2 - w)) x
      = (x : ℂ) ^ w / (w * (w + 1)) - 1 / w + 1 / ((w + 1) * x) - 1 / (2 - w) * (1 - 1 / x) := by
  have hx0 : 0 < x := by linarith
  rw [perronI_sub (verticalIntegrable_inv_sub hw) (verticalIntegrable_const_kernel _) hx0,
    perronI_inv_sub hw hw0 hw1 hx, perronI_const, perronI_one hx]

/-- `I[1/(s-ρ) - 1/(2-ρ)](x) = zeroTerm ρ x`. -/
theorem perronI_zeroTerm {ρ : ℂ} (hρ : 0 < ρ.re ∧ ρ.re < 1) {x : ℝ} (hx : 1 ≤ x) :
    perronI (fun s => 1 / (s - ρ) - 1 / (2 - ρ)) x = zeroTerm ρ x := by
  have hx0 : 0 < x := by linarith
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have h0 : ρ ≠ 0 := ne_zero_of_re_pos hρ.1
  have h1 : ρ + 1 ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have h2 : 2 - ρ ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  rw [perronI_inv_sub_sub (by linarith) h0 h1 hx, zeroTerm]
  field_simp
  ring

/-- Trivial-zero term: for `m ≥ 2`, `I[1/(2+m) - 1/(s+m)](x)
  = -2/(m(m+2)) + 3/((m-1)(m+2)x) - x^{-m}/(m(m-1))`. -/
theorem perronI_trivTerm {m : ℕ} (hm : 2 ≤ m) {x : ℝ} (hx : 1 ≤ x) :
    perronI (fun s => 1 / (2 + m) - 1 / (s + m)) x
      = -2 / (m * (m + 2)) + 3 / ((m - 1) * (m + 2) * x) - (x : ℂ) ^ (-(m : ℂ)) / (m * (m - 1)) := by
  have hx0 : 0 < x := by linarith
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hw : (-(m : ℂ)).re < 2 := by simp; linarith
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hw0 : -(m : ℂ) ≠ 0 := neg_ne_zero.mpr hm0
  have hm1 : (m : ℂ) - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hw1 : -(m : ℂ) + 1 ≠ 0 := by
    intro h; apply hm1; linear_combination -h
  have hm2 : (m : ℂ) + 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have e : (fun s : ℂ => 1 / (2 + (m : ℂ)) - 1 / (s + m))
      = fun s => 1 / (2 + (m : ℂ)) - 1 / (s - -(m : ℂ)) := by
    funext s; rw [sub_neg_eq_add]
  have hm2' : (2 : ℂ) + m ≠ 0 := by rw [add_comm]; exact hm2
  rw [e, perronI_sub (verticalIntegrable_const_kernel _) (verticalIntegrable_inv_sub hw) hx0,
    perronI_const, perronI_one hx, perronI_inv_sub hw hw0 hw1 hx]
  field_simp
  ring

/-! ## Step 1: `S(x) = I[-L'/L](x)` -/

theorem kernel_integral {z : ℝ} (hz : 0 < z) :
    ∫ y : ℝ, (z : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) •
        (fun s : ℂ => 1 / (s * (s + 1))) (((2 : ℝ) : ℂ) + y * I)
      = (2 * Real.pi : ℂ) * (if z ≤ 1 then ((1 - z : ℝ) : ℂ) else 0) := by
  have h := mellinInv_kernel (c := 2) two_pos hz
  unfold mellinInv at h
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  rw [← h, Complex.real_smul, ← mul_assoc]
  push_cast
  rw [mul_one_div_cancel hpi, one_mul]

theorem smoothPsi_eq_perronI {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {x : ℝ}
    (hx : 1 ≤ x) :
    smoothPsi χ x = perronI (fun s => -(deriv (LFunction χ) s / LFunction χ s)) x := by
  have hx0 : 0 < x := by linarith
  set f : ℕ → ℂ := fun n => χ (n : ZMod N) * (Λ n : ℂ) with hf
  set K : ℂ → ℂ := fun s => 1 / (s * (s + 1)) with hK
  set F : ℕ → ℝ → ℂ := fun n y => if n = 0 then 0 else
    f n * ((((n : ℝ) / x : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) • K (((2 : ℝ) : ℂ) + y * I))
    with hFdef
  have hpos : ∀ n : ℕ, n ≠ 0 → 0 < (n : ℝ) / x := fun n hn =>
    div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hx0
  -- the Dirichlet series on the line
  have hLS : ∀ y : ℝ, -(deriv (LFunction χ) (((2 : ℝ) : ℂ) + y * I)
      / LFunction χ (((2 : ℝ) : ℂ) + y * I)) = LSeries f (((2 : ℝ) : ℂ) + y * I) := by
    intro y
    have hs : 1 < (((2 : ℝ) : ℂ) + y * I).re := by simp
    have h1 : LSeries f (((2 : ℝ) : ℂ) + y * I) = _ := LSeries_twist_vonMangoldt_eq χ hs
    rw [h1, deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs, neg_div]
  -- pointwise expansion of the integrand
  have hpt : ∀ y : ℝ, ((x⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) •
      (fun s => -(deriv (LFunction χ) s / LFunction χ s) / (s * (s + 1)))
        (((2 : ℝ) : ℂ) + y * I) = ∑' n : ℕ, F n y := by
    intro y
    set s : ℂ := ((2 : ℝ) : ℂ) + y * I with hs
    simp only
    rw [hLS y, LSeries, smul_eq_mul, ← tsum_div_const, ← tsum_mul_left]
    congr 1
    funext n
    simp only [hFdef]
    split_ifs with hn
    · simp [hn]
    · rw [LSeries.term_of_ne_zero hn, smul_eq_mul, hK]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hcp : (((n : ℝ) / x : ℝ) : ℂ) ^ (-s)
          = ((x⁻¹ : ℝ) : ℂ) ^ (-s) * ((n : ℂ) ^ s)⁻¹ := by
        rw [div_eq_mul_inv, ofReal_mul, mul_cpow_ofReal_nonneg hn0 (inv_nonneg.mpr hx0.le),
          cpow_neg, ofReal_natCast]
        ring
      rw [hcp]
      ring
  -- integrability and the norm series
  have hKint := verticalIntegrable_kernel (c := 2) two_pos
  have hFint : ∀ n, Integrable (F n) := by
    intro n
    by_cases hn : n = 0
    · have : F n = fun _ => 0 := by funext y; simp [hFdef, hn]
      rw [this]; exact integrable_zero _ _ _
    · have h := (integrable_mellinInv_integrand hKint (hpos n hn)).const_mul (f n)
      refine h.congr (Eventually.of_forall fun y => ?_)
      simp [hFdef, hn, hK]
  set C : ℝ := ∫ y : ℝ, ‖K (((2 : ℝ) : ℂ) + y * I)‖ with hC
  have hFnorm : ∀ n, ∫ y, ‖F n y‖ = ‖LSeries.term f 2 n‖ * (x ^ 2 * C) := by
    intro n
    by_cases hn : n = 0
    · simp [hFdef, hn]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hpt' : ∀ y : ℝ, ‖F n y‖ = (‖f n‖ * ((n : ℝ) / x) ^ (-(2 : ℝ)))
          * ‖K (((2 : ℝ) : ℂ) + y * I)‖ := by
        intro y
        simp only [hFdef, hn, if_false, norm_mul, norm_smul]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (hpos n hn)]
        have : (-(((2 : ℝ) : ℂ) + y * I)).re = -2 := by simp
        rw [this]
        ring
      rw [integral_congr_ae (Eventually.of_forall hpt'), integral_const_mul, ← hC,
        LSeries.norm_term_eq, if_neg hn]
      have h2 : (2 : ℂ).re = 2 := by simp
      rw [h2, Real.rpow_neg (div_nonneg hnpos.le hx0.le), Real.div_rpow hnpos.le hx0.le,
        Real.rpow_two, Real.rpow_two]
      field_simp
  have hsum : Summable fun n => ∫ y, ‖F n y‖ := by
    have h := ((LSeriesSummable_twist_vonMangoldt χ (s := 2) (by norm_num)).norm).mul_right
      (x ^ 2 * C)
    refine h.congr fun n => (hFnorm n).symm
  -- interchange
  have hint := integral_tsum_of_summable_integral_norm hFint hsum
  have hFn : ∀ n, ∫ y, F n y = if n = 0 then 0 else
      f n * ((2 * Real.pi : ℂ) * (if (n : ℝ) / x ≤ 1 then ((1 - (n : ℝ) / x : ℝ) : ℂ) else 0)) := by
    intro n
    by_cases hn : n = 0
    · simp [hFdef, hn]
    · simp only [hFdef, hn, if_false]
      rw [integral_const_mul, kernel_integral (hpos n hn)]
  unfold perronI mellinInv
  rw [integral_congr_ae (Eventually.of_forall hpt), ← hint]
  simp_rw [hFn]
  rw [Complex.real_smul, ← tsum_mul_left]
  have hzero : ∀ n ∉ Finset.range ⌈x⌉₊, (((1 / (2 * Real.pi) : ℝ) : ℂ) * (if n = 0 then 0 else
      f n * ((2 * Real.pi : ℂ) * (if (n : ℝ) / x ≤ 1 then ((1 - (n : ℝ) / x : ℝ) : ℂ) else 0))))
      = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt, Nat.ceil_le] at hn
    have h1 : 1 ≤ (n : ℝ) / x := by rw [le_div_iff₀ hx0]; linarith
    split_ifs with h0 h2
    · simp
    · have : (n : ℝ) / x = 1 := le_antisymm h2 h1
      simp [this]
    · simp
  rw [tsum_eq_sum hzero]
  unfold smoothPsi
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnx : (n : ℝ) < x := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  by_cases h0 : n = 0
  · simp [h0]
  · have hle : (n : ℝ) / x ≤ 1 := by rw [div_le_one hx0]; exact hnx.le
    rw [if_neg h0, if_pos hle, hf]
    push_cast
    field_simp

/-! ## The Γ-factor: `G(s) - G(2)` as a series over the trivial zeros -/

/-- Parity shift `a ∈ {0,1}`: trivial zeros of `L(s,χ)` are at `-(2k+a)`. -/
noncomputable def gammaShift {N : ℕ} (χ : DirichletCharacter ℂ N) : ℕ := by
  classical exact if χ.Even then 0 else 1

/-- `G = γ_χ'/γ_χ`, the logarithmic derivative of the Γ-factor. -/
noncomputable def Gfun {N : ℕ} (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  deriv (gammaFactor χ) s / gammaFactor χ s

theorem Gfun_eq {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    Gfun χ s = -(Real.log Real.pi : ℂ) / 2 + digamma ((s + gammaShift χ) / 2) / 2 := by
  classical
  unfold Gfun gammaShift
  rcases χ.even_or_odd with he | ho
  · have hfun : gammaFactor χ = Gammaℝ := funext fun s => he.gammaFactor_def s
    rw [hfun, logDeriv_Gammaℝ hs, if_pos he]
    simp
  · have hfun : gammaFactor χ = fun s => Gammaℝ (s + 1) := funext fun s => ho.gammaFactor_def s
    rw [hfun, deriv_comp_add_const, logDeriv_Gammaℝ (by simp; linarith), if_neg ho.not_even]
    simp

/-- `G(s) - G(2) = ∑_k (1/(2 + m_k) - 1/(s + m_k))`, `m_k = 2k + a`, for `Re s > 0`. -/
theorem hasSum_Gfun_sub {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun k : ℕ => 1 / (2 + ((2 * k + gammaShift χ : ℕ) : ℂ))
        - 1 / (s + ((2 * k + gammaShift χ : ℕ) : ℂ))) (Gfun χ s - Gfun χ 2) := by
  set a : ℕ := gammaShift χ with ha
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hz : 0 < ((s + a) / 2).re := by simp; linarith
  have hz0 : 0 < (((2 : ℂ) + a) / 2).re := by simp; linarith
  have h := (hasSum_digamma_sub hz hz0).mul_left (1 / 2)
  have e1 : (fun k : ℕ => 1 / 2 * (1 / ((k : ℂ) + ((2 : ℂ) + a) / 2) - 1 / ((k : ℂ) + (s + a) / 2)))
      = fun k : ℕ => 1 / (2 + ((2 * k + a : ℕ) : ℂ)) - 1 / (s + ((2 * k + a : ℕ) : ℂ)) := by
    funext k
    push_cast
    rw [show (k : ℂ) + ((2 : ℂ) + a) / 2 = (2 + (2 * k + a)) / 2 by ring,
      show (k : ℂ) + (s + a) / 2 = (s + (2 * k + a)) / 2 by ring, one_div_div, one_div_div]
    ring
  rw [e1] at h
  have e2 : Gfun χ s - Gfun χ 2 = 1 / 2 * (digamma ((s + a) / 2) - digamma (((2 : ℂ) + a) / 2)) := by
    rw [Gfun_eq χ hs, Gfun_eq χ (by norm_num), ← ha]
    ring
  rw [e2]
  exact h

/-! ## Step 2: the partial-fraction decomposition of `-L'/L` on `Re s > 1` -/

theorem differentiableAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Gammaℝ s := by
  have hs2 : ∀ m : ℕ, s / 2 ≠ -m := by
    intro m h
    have h1 := congrArg Complex.re h
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    simp at h1
    linarith
  have hfun : Gammaℝ = fun z => (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2) := funext Gammaℝ_def
  rw [hfun]
  have h1 : DifferentiableAt ℂ (fun z : ℂ => -z / 2) s := (differentiableAt_id.neg).div_const 2
  have h2 : DifferentiableAt ℂ (fun z : ℂ => z / 2) s := differentiableAt_id.div_const 2
  exact (h1.const_cpow (Or.inl (by exact_mod_cast Real.pi_ne_zero))).mul
    ((differentiableAt_Gamma _ hs2).comp s h2)

theorem gammaFactor_diff_ne {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (gammaFactor χ) s ∧ gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · have hfun : gammaFactor χ = Gammaℝ := funext fun s => he.gammaFactor_def s
    rw [hfun]
    exact ⟨differentiableAt_Gammaℝ_of_re_pos hs, Gammaℝ_ne_zero_of_re_pos hs⟩
  · have hfun : gammaFactor χ = fun s => Gammaℝ (s + 1) := funext fun s => ho.gammaFactor_def s
    have hs1 : 0 < (s + 1).re := by simp; linarith
    rw [hfun]
    exact ⟨(differentiableAt_Gammaℝ_of_re_pos hs1).comp s
      (differentiableAt_id.add_const 1), Gammaℝ_ne_zero_of_re_pos hs1⟩

theorem completed_eq_L_mul_gammaFactor {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) : completedLFunction χ s = LFunction χ s * gammaFactor χ s := by
  have h := LFunction_eq_completed_div_gammaFactor χ s (Or.inl (ne_zero_of_re_pos hs))
  rw [h, div_mul_cancel₀ _ (gammaFactor_diff_ne χ hs).2]

theorem logDeriv_completed_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ1 : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    completedLFunction χ s ≠ 0 ∧
    deriv (completedLFunction χ) s / completedLFunction χ s
      = deriv (LFunction χ) s / LFunction χ s + Gfun χ s := by
  have hs0 : 0 < s.re := by linarith
  have hL : LFunction χ s ≠ 0 := LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hs.le
  obtain ⟨hgd, hg⟩ := gammaFactor_diff_ne χ hs0
  have hLd : DifferentiableAt ℂ (LFunction χ) s := differentiableAt_LFunction χ s (Or.inr hχ1)
  have hev : completedLFunction χ =ᶠ[𝓝 s] fun t => LFunction χ t * gammaFactor χ t := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs0] with t ht
    exact completed_eq_L_mul_gammaFactor χ ht
  refine ⟨by rw [completed_eq_L_mul_gammaFactor χ hs0]; exact mul_ne_zero hL hg, ?_⟩
  rw [hev.deriv_eq, completed_eq_L_mul_gammaFactor χ hs0, deriv_fun_mul hLd hgd, Gfun]
  field_simp

theorem zeroOrd_strip {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {ρ : ℂ}
    (h : zeroOrd χ ρ ≠ 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  unfold zeroOrd at h
  split_ifs at h with hs
  · exact hs
  · exact absurd rfl h

theorem summable_hadamard_terms {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) {s : ℂ} (hs : 1 < s.re) :
    Summable fun ρ : ℂ => (zeroOrd χ ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
  set d := s.re - 1 with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  set Cs := ‖s‖ * (1 + ‖s‖ / d) with hCs
  refine Summable.of_norm_bounded (hS.mul_left Cs) fun ρ => ?_
  by_cases h0 : zeroOrd χ ρ = 0
  · simp [h0]
  · obtain ⟨h1, h2⟩ := zeroOrd_strip h0
    have hρ : ρ ≠ 0 := ne_zero_of_re_pos h1
    have hρn : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
    have hsρd : d ≤ ‖s - ρ‖ := by
      have := Complex.re_le_norm (s - ρ)
      rw [Complex.sub_re] at this
      rw [hd]; linarith
    have hsρ : s - ρ ≠ 0 := by
      intro h; rw [h, norm_zero] at hsρd; linarith
    have hsρn : 0 < ‖s - ρ‖ := norm_pos_iff.mpr hsρ
    have heq : 1 / (s - ρ) + 1 / ρ = s / ((s - ρ) * ρ) := by field_simp; ring
    have hρle : ‖ρ‖ ≤ ‖s - ρ‖ * (1 + ‖s‖ / d) := by
      have t1 : ‖ρ‖ ≤ ‖s - ρ‖ + ‖s‖ := by
        calc ‖ρ‖ = ‖s - (s - ρ)‖ := by ring_nf
          _ ≤ ‖s‖ + ‖s - ρ‖ := norm_sub_le _ _
          _ = ‖s - ρ‖ + ‖s‖ := add_comm _ _
      have t2 : ‖s‖ ≤ ‖s - ρ‖ * (‖s‖ / d) := by
        rw [mul_div_assoc', le_div_iff₀ hd0]
        exact mul_le_mul_of_nonneg_left hsρd (norm_nonneg s) |>.trans_eq (mul_comm _ _)
      nlinarith
    rw [heq, norm_mul, norm_div, norm_mul, Complex.norm_natCast]
    have key : ‖s‖ / (‖s - ρ‖ * ‖ρ‖) ≤ Cs / ‖ρ‖ ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), hCs]
      have := mul_le_mul_of_nonneg_left hρle (mul_nonneg (norm_nonneg s) hρn.le)
      nlinarith [norm_nonneg s]
    calc (zeroOrd χ ρ : ℝ) * (‖s‖ / (‖s - ρ‖ * ‖ρ‖))
        ≤ (zeroOrd χ ρ : ℝ) * (Cs / ‖ρ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left key (Nat.cast_nonneg _)
      _ = Cs * ((zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) := by ring

/-- **Step 2.** For `Re s > 1`:
`-L'/L(s) = -L'/L(2) + (G(s) - G(2)) - ∑_ρ m_ρ (1/(s-ρ) - 1/(2-ρ))`. -/
theorem neg_logDeriv_decomp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (hH : HadamardLogDeriv χ) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)
    {s : ℂ} (hs : 1 < s.re) :
    -(deriv (LFunction χ) s / LFunction χ s)
      = -(deriv (LFunction χ) 2 / LFunction χ 2) + (Gfun χ s - Gfun χ 2)
        - ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ)) := by
  obtain ⟨B, hB⟩ := hH
  have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
  obtain ⟨hcs, hds⟩ := logDeriv_completed_eq χ hχ1 hs
  obtain ⟨hc2, hd2⟩ := logDeriv_completed_eq χ hχ1 h2
  have hBs := hB s hcs
  have hB2 := hB 2 hc2
  have hsub : ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ))
      = (∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (s - ρ) + 1 / ρ))
        - ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (2 - ρ) + 1 / ρ) := by
    rw [← (summable_hadamard_terms χ hS hs).tsum_sub (summable_hadamard_terms χ hS h2)]
    congr 1; funext ρ; ring
  rw [hsub]
  linear_combination hds - hd2 - hBs + hB2

end DetPrimality.Bach
