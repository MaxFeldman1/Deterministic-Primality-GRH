import DetPrimality.Bach.R11ZetaXPerron

/-!
# Termwise integration for the kernels `1/(s+1/2)^k` and the explicit formula (designB Lemma 2)

* `r11Zx_Q_zeroSum` : the sum over the zeros, termwise (generic multiplicity function);
* `r11Zx_hasSum_Q_gamma` : the Γ-part, termwise;
* `r11Zx_explicit` : `Q_k[-ζ'/ζ](x)` as pole terms + trivial zeros + nontrivial zeros.
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt
local notation "χ₁" => (1 : DirichletCharacter ℂ 1)

/-- **Termwise integration over the zeros** for the kernel `1/(s+1/2)^k`. -/
theorem r11Zx_Q_zeroSum {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) {m : ℂ → ℕ}
    (hstrip : ∀ ρ, m ρ ≠ 0 → 0 < ρ.re ∧ ρ.re < 1)
    (hWs : Summable fun ρ : ℂ => (m ρ : ℝ) * (1 + |ρ.im|) ^ (-(7 / 4 : ℝ))) {x : ℝ}
    (hx : 1 ≤ x) :
    r11Zx_Q k (fun s => ∑' ρ : ℂ, (m ρ : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ))) x
      = ∑' ρ : ℂ, (m ρ : ℂ) * (r11Zx_R k ρ x - 1 / (2 - ρ) * r11Zx_one k x) := by
  have hx0 : 0 < x := by linarith
  have hk2 := r11Zx_two_le hk
  obtain ⟨CJ, hCJ0, hJ⟩ := kernel_zero_bound
  set Sρ : Set ℂ := Function.support
    (fun ρ : ℂ => (m ρ : ℝ) * (1 + |ρ.im|) ^ (-(7 / 4 : ℝ))) with hSρ
  have : Countable Sρ := hWs.countable_support.to_subtype
  have hmem : ∀ ρ : ℂ, m ρ ≠ 0 → ρ ∈ Sρ := by
    intro ρ h
    rw [hSρ, Function.mem_support]
    exact mul_ne_zero (by exact_mod_cast h) (Real.rpow_pos_of_pos (by positivity) _).ne'
  have hstrip' : ∀ ρ : Sρ, 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
    intro ρ
    apply hstrip
    intro h0
    have h2 : (ρ : ℂ) ∈ Function.support
      (fun ρ : ℂ => (m ρ : ℝ) * (1 + |ρ.im|) ^ (-(7 / 4 : ℝ))) := ρ.2
    rw [Function.mem_support] at h2
    exact h2 (by simp [h0])
  set c : ℝ → ℂ := fun y => ((x⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) with hc
  set F : Sρ → ℝ → ℂ := fun ρ y => c y • ((m (ρ : ℂ) : ℂ)
      * (1 / ((((2 : ℝ) : ℂ) + y * I) - ρ) - 1 / (2 - (ρ : ℂ)))
      / (((2 : ℝ) : ℂ) + y * I + 1 / 2) ^ k) with hF
  have hsupp : ∀ s : ℂ, Function.support (fun ρ : ℂ => (m ρ : ℂ)
      * (1 / (s - ρ) - 1 / (2 - ρ))) ⊆ Sρ := by
    intro s ρ hρ
    apply hmem
    intro h0
    apply hρ
    simp [h0]
  have hpt : ∀ y : ℝ, c y • (fun s => (∑' ρ : ℂ, (m ρ : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ)))
      / (s + 1 / 2) ^ k) (((2 : ℝ) : ℂ) + y * I) = ∑' ρ : Sρ, F ρ y := by
    intro y
    simp only [hF]
    rw [← tsum_subtype_eq_of_support_subset (hsupp _), smul_eq_mul, ← tsum_div_const,
      ← tsum_mul_left]
    rfl
  have hvi : ∀ ρ : Sρ, VerticalIntegrable (fun s : ℂ => (m (ρ : ℂ) : ℂ)
      * (1 / (s - ρ) - 1 / (2 - (ρ : ℂ))) / (s + 1 / 2) ^ k) 2 := fun ρ =>
    r11Zx_vi_of_sq hk2 (llsPer_vi_zero_term (by linarith [(hstrip' ρ).2]) (m (ρ : ℂ) : ℂ))
  have hFint : ∀ ρ : Sρ, Integrable (F ρ) := fun ρ =>
    integrable_mellinInv_integrand (hvi ρ) (inv_pos.mpr hx0)
  have hFnorm : ∀ ρ : Sρ, ∫ y, ‖F ρ y‖
      ≤ (3 * x ^ 2 * CJ) * ((m (ρ : ℂ) : ℝ) * (1 + |(ρ : ℂ).im|) ^ (-(7 / 4 : ℝ))) := by
    intro ρ
    obtain ⟨hJi, hJb⟩ := hJ ρ (hstrip' ρ).2
    set mm : ℝ := (m (ρ : ℂ) : ℝ) with hmm
    set g : ℝ := 1 + |(ρ : ℂ).im| with hg
    have hgpos : 0 < g := by positivity
    have h2ρ : g / 2 ≤ ‖2 - (ρ : ℂ)‖ := norm_two_sub_ge (hstrip' ρ).2
    have h2ρpos : 0 < ‖2 - (ρ : ℂ)‖ := lt_of_lt_of_le (by positivity) h2ρ
    have hm0 : 0 ≤ mm := Nat.cast_nonneg _
    have hpt' : ∀ y : ℝ, ‖F ρ y‖ ≤ (3 / 2 * x ^ 2 * mm / ‖2 - (ρ : ℂ)‖) * (|y|
        * ‖1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖
        / ‖(((2 : ℝ) : ℂ) + y * I) - ρ‖) := by
      intro y
      have hsρ : (((2 : ℝ) : ℂ) + y * I) - ρ ≠ 0 :=
        ne_zero_of_re_pos (by rw [Complex.sub_re, line_re]; linarith [(hstrip' ρ).2])
      have hsρn : 0 < ‖(((2 : ℝ) : ℂ) + y * I) - ρ‖ := norm_pos_iff.mpr hsρ
      have h2 : 2 - (ρ : ℂ) ≠ 0 := norm_pos_iff.mp h2ρpos
      have hs0 := llsPer_line_ne y
      have hs1 : ((2 : ℝ) : ℂ) + y * I + 1 ≠ 0 :=
        ne_zero_of_re_pos (by rw [Complex.add_re, line_re, Complex.one_re]; norm_num)
      have hK := llsPer_inv_sq_le (llsPer_two_le_norm_line y) hs1
      have hK' : ‖1 / (((2 : ℝ) : ℂ) + y * I + 1 / 2) ^ k‖
          ≤ 3 / 2 * ‖1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖ :=
        ((r11Zx_norm_kernel_le hk2 y).trans_eq (llsPer_norm_kernel y).symm).trans hK
      simp only [hF, hc]
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr hx0)]
      have hre : (-(((2 : ℝ) : ℂ) + y * I)).re = -2 := by simp
      rw [hre, Real.rpow_neg (inv_nonneg.mpr hx0.le), Real.inv_rpow hx0.le, inv_inv,
        Real.rpow_two]
      have hid0 : (m (ρ : ℂ) : ℂ) * (1 / ((((2 : ℝ) : ℂ) + y * I) - ρ) - 1 / (2 - (ρ : ℂ)))
          = (m (ρ : ℂ) : ℂ) * (-(y * I)) / (((((2 : ℝ) : ℂ) + y * I) - ρ) * (2 - ρ)) := by
        field_simp
        push_cast
        ring
      rw [div_eq_mul_one_div, hid0, norm_mul, norm_div, norm_mul, norm_mul, norm_neg, norm_mul,
        Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs,
        ← hmm]
      calc x ^ 2 * (mm * |y| / (‖(((2 : ℝ) : ℂ) + y * I) - ρ‖ * ‖2 - (ρ : ℂ)‖)
            * ‖1 / (((2 : ℝ) : ℂ) + y * I + 1 / 2) ^ k‖)
          ≤ x ^ 2 * (mm * |y| / (‖(((2 : ℝ) : ℂ) + y * I) - ρ‖ * ‖2 - (ρ : ℂ)‖)
            * (3 / 2 * ‖1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK' (by positivity))
              (by positivity)
        _ = _ := by field_simp
    have hint0 : 0 ≤ ∫ y : ℝ, |y| * ‖1 / ((((2 : ℝ) : ℂ) + y * I)
        * ((((2 : ℝ) : ℂ) + y * I) + 1))‖ / ‖(((2 : ℝ) : ℂ) + y * I) - ρ‖ :=
      integral_nonneg fun y => by positivity
    have hcoef : 3 / 2 * x ^ 2 * mm / ‖2 - (ρ : ℂ)‖ ≤ 3 / 2 * x ^ 2 * mm * (2 / g) := by
      rw [div_le_iff₀ h2ρpos]
      calc 3 / 2 * x ^ 2 * mm = 3 / 2 * x ^ 2 * mm * (2 / g) * (g / 2) := by field_simp
        _ ≤ 3 / 2 * x ^ 2 * mm * (2 / g) * ‖2 - (ρ : ℂ)‖ :=
          mul_le_mul_of_nonneg_left h2ρ (by positivity)
    have hgexp : (1 / g) * g ^ (-(3 / 4 : ℝ)) = g ^ (-(7 / 4 : ℝ)) := by
      rw [show (-(7 / 4 : ℝ)) = -1 + -(3 / 4) by norm_num, Real.rpow_add hgpos,
        Real.rpow_neg_one, one_div]
    calc ∫ y, ‖F ρ y‖
        ≤ ∫ y : ℝ, (3 / 2 * x ^ 2 * mm / ‖2 - (ρ : ℂ)‖) * (|y|
          * ‖1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖
          / ‖(((2 : ℝ) : ℂ) + y * I) - ρ‖) :=
          integral_mono (hFint ρ).norm (hJi.const_mul _) hpt'
      _ = (3 / 2 * x ^ 2 * mm / ‖2 - (ρ : ℂ)‖) * ∫ y : ℝ, |y|
          * ‖1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖
          / ‖(((2 : ℝ) : ℂ) + y * I) - ρ‖ := integral_const_mul _ _
      _ ≤ 3 / 2 * x ^ 2 * mm * (2 / g) * (CJ * g ^ (-(3 / 4 : ℝ))) :=
          mul_le_mul hcoef hJb hint0 (by positivity)
      _ = 3 * x ^ 2 * CJ * (mm * ((1 / g) * g ^ (-(3 / 4 : ℝ)))) := by ring
      _ = 3 * x ^ 2 * CJ * (mm * g ^ (-(7 / 4 : ℝ))) := by rw [hgexp]
  have hFsum : Summable fun ρ : Sρ => ∫ y, ‖F ρ y‖ :=
    Summable.of_nonneg_of_le (fun ρ => integral_nonneg fun y => norm_nonneg _) hFnorm
      ((hWs.subtype Sρ).mul_left _)
  have hsum := hasSum_integral_of_summable_integral_norm hFint hFsum
  rw [integral_congr_ae (Eventually.of_forall fun y => (hpt y).symm)] at hsum
  have h2 := hsum.const_smul (1 / (2 * Real.pi))
  have e1 : ∀ ρ : Sρ, (1 / (2 * Real.pi)) • ∫ y, F ρ y
      = (m (ρ : ℂ) : ℂ) * (r11Zx_R k ρ x - 1 / (2 - (ρ : ℂ)) * r11Zx_one k x) := by
    intro ρ
    have hρ2 : (ρ : ℂ).re < 2 := by linarith [(hstrip' ρ).2]
    have hρ0 : (ρ : ℂ) + 1 / 2 ≠ 0 := ne_zero_of_re_pos (by
      have : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
      rw [Complex.add_re, this]; linarith [(hstrip' ρ).1])
    have : (1 / (2 * Real.pi)) • ∫ y, F ρ y
        = r11Zx_Q k (fun s => (m (ρ : ℂ) : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ))) x := rfl
    rw [this, r11Zx_Q_const_mul, r11Zx_Q_sub (r11Zx_vi_inv_sub hk2 hρ2) (r11Zx_vi_const hk2 _) hx0,
      r11Zx_Q_inv_sub hk hρ2 hρ0 hx, r11Zx_Q_const, r11Zx_Q_one hk hx]
  simp only [e1] at h2
  have e2 : (1 / (2 * Real.pi)) • ∫ y : ℝ, c y • (fun s =>
      (∑' ρ : ℂ, (m ρ : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ))) / (s + 1 / 2) ^ k)
      (((2 : ℝ) : ℂ) + y * I)
      = r11Zx_Q k (fun s => ∑' ρ : ℂ, (m ρ : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ))) x := rfl
  rw [e2] at h2
  rw [← h2.tsum_eq]
  refine tsum_subtype_eq_of_support_subset
    (f := fun ρ : ℂ => (m ρ : ℂ) * (r11Zx_R k ρ x - 1 / (2 - ρ) * r11Zx_one k x)) (s := Sρ) ?_
  intro ρ hρ
  apply hmem
  intro h0
  apply hρ
  simp [h0]

/-! ## The Γ-part -/

theorem r11Zx_Q_gterm {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) (m : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    r11Zx_Q k (fun s => 1 / (2 + (m : ℂ)) - 1 / (s + m)) x
      = 1 / (2 + (m : ℂ)) * r11Zx_one k x - r11Zx_R k (-(m : ℂ)) x := by
  have hx0 : 0 < x := by linarith
  have hk2 := r11Zx_two_le hk
  have hw : (-(m : ℂ)).re < 2 := by
    simp; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hw0 : -(m : ℂ) + 1 / 2 ≠ 0 := by
    intro h
    have h2 : (2 * m : ℂ) = 1 := by linear_combination (-2) * h
    have h3 : 2 * m = 1 := by exact_mod_cast h2
    omega
  have e : (fun s : ℂ => 1 / (2 + (m : ℂ)) - 1 / (s + m))
      = fun s => 1 / (2 + (m : ℂ)) - 1 / (s - -(m : ℂ)) := by
    funext s; rw [sub_neg_eq_add]
  rw [e, r11Zx_Q_sub (r11Zx_vi_const hk2 _) (r11Zx_vi_inv_sub hk2 hw) hx0, r11Zx_Q_const,
    r11Zx_Q_one hk hx, r11Zx_Q_inv_sub hk hw hw0 hx]

theorem r11Zx_hasSum_Q_gamma {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) {N : ℕ}
    (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 1 ≤ x) :
    HasSum (fun j : ℕ => r11Zx_Q k (fun s => 1 / (2 + ((2 * j + gammaShift χ : ℕ) : ℂ))
        - 1 / (s + ((2 * j + gammaShift χ : ℕ) : ℂ))) x)
      (r11Zx_Q k (fun s => Gfun χ s - Gfun χ 2) x) := by
  have hx0 : 0 < x := by linarith
  have hk2 := r11Zx_two_le hk
  set m : ℕ → ℕ := fun j => 2 * j + gammaShift χ with hm
  have hmk : ∀ j, 2 * j ≤ m j := fun j => by simp [hm]
  set T : ℕ → ℝ → ℂ := fun j y => ((x⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) •
    ((1 / (2 + ((m j : ℕ) : ℂ)) - 1 / ((((2 : ℝ) : ℂ) + y * I) + ((m j : ℕ) : ℂ)))
      / (((2 : ℝ) : ℂ) + y * I + 1 / 2) ^ k) with hT
  have hTint : ∀ j, Integrable (T j) := fun j =>
    integrable_mellinInv_integrand (r11Zx_vi_of_sq hk2 (llsPer_vi_gterm (m j)))
      (inv_pos.mpr hx0)
  have hTle : ∀ j y, ‖T j y‖ ≤ (x ^ 2 * wk j) * phiG y := by
    intro j y
    simp only [hT]
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr hx0)]
    have hre : (-(((2 : ℝ) : ℂ) + y * I)).re = -2 := by simp
    rw [hre, Real.rpow_neg (inv_nonneg.mpr hx0.le), Real.inv_rpow hx0.le, inv_inv,
      Real.rpow_two, div_eq_mul_one_div _ ((((2 : ℝ) : ℂ) + y * I + 1 / 2) ^ k), norm_mul]
    have hg := norm_gterm_le (hmk j) y
    have hker := r11Zx_norm_kernel_le hk2 y
    unfold phiG
    calc x ^ 2 * (‖1 / (2 + ((m j : ℕ) : ℂ)) - 1 / ((((2 : ℝ) : ℂ) + y * I) + ((m j : ℕ) : ℂ))‖
          * ‖1 / (((2 : ℝ) : ℂ) + y * I + 1 / 2) ^ k‖)
        ≤ x ^ 2 * ((√|y| * wk j) * (1 / ((2 : ℝ) ^ 2 + y ^ 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hg hker (norm_nonneg _)
            (mul_nonneg (Real.sqrt_nonneg _) (wk_nonneg _))) (by positivity)
      _ = x ^ 2 * wk j * (√|y| / ((2 : ℝ) ^ 2 + y ^ 2)) := by ring
  have hTsum : Summable fun j => ∫ y, ‖T j y‖ := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun y => norm_nonneg _)
      (fun j => ?_) ((summable_wk.mul_left (x ^ 2)).mul_right (∫ y, phiG y))
    calc ∫ y, ‖T j y‖ ≤ ∫ y, (x ^ 2 * wk j) * phiG y :=
          integral_mono (hTint j).norm (integrable_phiG.const_mul _) (hTle j)
      _ = x ^ 2 * wk j * ∫ y, phiG y := integral_const_mul _ _
  have hsumI := hasSum_integral_of_summable_integral_norm hTint hTsum
  have hpt : ∀ y : ℝ, ∑' j, T j y = ((x⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) •
      ((Gfun χ (((2 : ℝ) : ℂ) + y * I) - Gfun χ 2) / (((2 : ℝ) : ℂ) + y * I + 1 / 2) ^ k) := by
    intro y
    have hre : 0 < (((2 : ℝ) : ℂ) + y * I).re := by simp
    have h := ((hasSum_Gfun_sub χ hre).div_const
      ((((2 : ℝ) : ℂ) + y * I + 1 / 2) ^ k)).mul_left
      (((x⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)))
    exact h.tsum_eq
  rw [integral_congr_ae (Eventually.of_forall hpt)] at hsumI
  have h2 := hsumI.const_smul (1 / (2 * Real.pi))
  exact h2

/-! ## The explicit formula -/

/-- **Explicit formula** for the kernel `1/(s+1/2)^k`, `k ∈ {2,3,4}`, `x ≥ 1`. -/
theorem r11Zx_explicit {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) {x : ℝ} (hx : 1 ≤ x) :
    r11Zx_Q k (fun s => -(deriv (LFunction χ₁) s / LFunction χ₁ s)) x
      = llsZL_c1 * r11Zx_one k x + r11Zx_R k 0 x + r11Zx_R k 1 x
        + ∑' j : ℕ, (1 / (2 + ((2 * j : ℕ) : ℂ)) * r11Zx_one k x
            - r11Zx_R k (-((2 * j : ℕ) : ℂ)) x)
        - ∑' ρ : ℂ, (zeroOrd χ₁ ρ : ℂ) * (r11Zx_R k ρ x - 1 / (2 - ρ) * r11Zx_one k x) := by
  have hx0 : 0 < x := by linarith
  have hk2 := r11Zx_two_le hk
  have hc := r11Zx_vi_const hk2 llsZL_c1
  have h1i : VerticalIntegrable (fun s : ℂ => 1 / s / (s + 1 / 2) ^ k) 2 :=
    r11Zx_vi_of_sq hk2 llsPer_vi_inv_self
  have h2i : VerticalIntegrable (fun s : ℂ => 1 / (s - 1) / (s + 1 / 2) ^ k) 2 :=
    r11Zx_vi_inv_sub hk2 (w := 1) (by norm_num)
  have hGi : VerticalIntegrable (fun s => (Gfun χ₁ s - Gfun χ₁ 2) / (s + 1 / 2) ^ k) 2 :=
    r11Zx_vi_of_sq hk2 (llsPer_vi_gamma χ₁)
  have hA1 : VerticalIntegrable (fun s : ℂ => (llsZL_c1 + 1 / s) / (s + 1 / 2) ^ k) 2 := by
    refine (Integrable.add hc h1i).congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, add_div]
  have hA2 : VerticalIntegrable
      (fun s : ℂ => (llsZL_c1 + 1 / s + 1 / (s - 1)) / (s + 1 / 2) ^ k) 2 := by
    refine (Integrable.add hA1 h2i).congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, add_div]
  have hA3 : VerticalIntegrable (fun s : ℂ =>
      (llsZL_c1 + 1 / s + 1 / (s - 1) + (Gfun χ₁ s - Gfun χ₁ 2)) / (s + 1 / 2) ^ k) 2 := by
    refine (Integrable.add hA2 hGi).congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, add_div]
  have hLi : VerticalIntegrable
      (fun s => -(deriv (LFunction χ₁) s / LFunction χ₁ s) / (s + 1 / 2) ^ k) 2 :=
    r11Zx_vi_of_sq hk2 llsZL_vi_logDeriv
  have hZi : VerticalIntegrable (fun s => llsZL_Z s / (s + 1 / 2) ^ k) 2 := by
    refine (Integrable.sub hA3 hLi).congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]
    rw [llsZL_line_decomp (s := ((2 : ℝ) : ℂ) + y * I) (by rw [line_re]; norm_num)]
    ring
  have hZ : r11Zx_Q k llsZL_Z x = ∑' ρ : ℂ, (zeroOrd χ₁ ρ : ℂ)
      * (r11Zx_R k ρ x - 1 / (2 - ρ) * r11Zx_one k x) :=
    r11Zx_Q_zeroSum hk (m := zeroOrd χ₁) (fun _ h => zeroOrd_strip h) llsZL_summable_weight hx
  have hG := (r11Zx_hasSum_Q_gamma hk χ₁ hx).tsum_eq
  rw [llsZL_gammaShift] at hG
  simp only [add_zero, r11Zx_Q_gterm hk _ hx] at hG
  have h0 : r11Zx_Q k (fun s : ℂ => 1 / s) x = r11Zx_R k 0 x := by
    have e : (fun s : ℂ => 1 / s) = fun s => 1 / (s - 0) := by funext s; rw [sub_zero]
    rw [e, r11Zx_Q_inv_sub hk (by simp) (by norm_num) hx]
  have h1' : r11Zx_Q k (fun s : ℂ => 1 / (s - 1)) x = r11Zx_R k 1 x :=
    r11Zx_Q_inv_sub hk (by simp) (by norm_num) hx
  have h1 : r11Zx_Q k (fun s => -(deriv (LFunction χ₁) s / LFunction χ₁ s)) x
      = r11Zx_Q k (fun s =>
        (llsZL_c1 + 1 / s + 1 / (s - 1) + (Gfun χ₁ s - Gfun χ₁ 2)) - llsZL_Z s) x := by
    apply r11Zx_Q_congr_line
    intro y
    exact llsZL_line_decomp (by rw [line_re]; norm_num)
  rw [r11Zx_Q_sub hA3 hZi hx0, r11Zx_Q_add hA2 hGi hx0, r11Zx_Q_add hA1 h2i hx0,
    r11Zx_Q_add hc h1i hx0, r11Zx_Q_const, r11Zx_Q_one hk hx, h0, h1', hZ, ← hG] at h1
  exact h1

end DetPrimality.Bach
