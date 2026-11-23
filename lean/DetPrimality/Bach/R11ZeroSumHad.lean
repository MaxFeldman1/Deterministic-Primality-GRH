import DetPrimality.Bach.R11Defs
import DetPrimality.Bach.LLSZetaConst

/-!
# Round 11, zero sums: termwise differentiation of the Hadamard series at `3/2`

For a multiplicity function `m` supported in the open critical strip with `∑ m_ρ/|ρ|² < ∞`:

* `r11Zs_hasDerivAt_tsum` : `s ↦ ∑_ρ m_ρ (1/(s-ρ) + 1/ρ)` has derivative
  `-∑_ρ m_ρ/(3/2-ρ)²` at `3/2` (Weierstrass M-test on the disc `|s - 3/2| < 1/4`);
* `r11Zs_Z2_eq`, `r11Zs_Z4_eq` : if moreover all `ρ` are on the critical line, then
  `∑ m_ρ/|ρ+½|² = ∑ m_ρ Re 1/(3/2-ρ)` and
  `∑ m_ρ/|ρ+½|⁴ = ½ [∑ m_ρ Re 1/(3/2-ρ) + Re ∑ m_ρ/(3/2-ρ)²]`.
-/

open Complex Filter Topology

namespace DetPrimality.Bach

section generic

variable {m : ℂ → ℕ}

lemma r11Zs_ball_re {s : ℂ} (hs : s ∈ Metric.ball (3 / 2 : ℂ) (1 / 4)) :
    5 / 4 < s.re ∧ ‖s‖ < 7 / 4 := by
  rw [Metric.mem_ball, dist_eq_norm] at hs
  constructor
  · have h1 := abs_re_le_norm (s - 3 / 2)
    have h2 : (s - 3 / 2).re = s.re - 3 / 2 := by simp
    rw [h2] at h1
    have := abs_le.mp (h1.trans hs.le)
    have h3 := abs_lt.mp (lt_of_le_of_lt h1 hs)
    linarith [h3.1]
  · have h1 : ‖s‖ ≤ ‖s - 3 / 2‖ + ‖(3 / 2 : ℂ)‖ := by
      have := norm_add_le (s - 3 / 2) (3 / 2 : ℂ)
      simpa using this
    have h2 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by
      rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real]
      norm_num
    rw [h2] at h1
    linarith

lemma r11Zs_dist {s ρ : ℂ} (hs : s ∈ Metric.ball (3 / 2 : ℂ) (1 / 4)) (hρ : ρ.re < 1) :
    1 / 4 < ‖s - ρ‖ ∧ ‖ρ‖ ≤ 8 * ‖s - ρ‖ := by
  obtain ⟨h1, h2⟩ := r11Zs_ball_re hs
  have h3 : (s - ρ).re ≤ ‖s - ρ‖ := re_le_norm _
  rw [sub_re] at h3
  have h4 : ‖ρ‖ ≤ ‖s‖ + ‖s - ρ‖ := by
    have := norm_sub_le s (s - ρ)
    simpa using this
  constructor <;> linarith

lemma r11Zs_term_bound (hm : ∀ ρ, m ρ ≠ 0 → 0 < ρ.re ∧ ρ.re < 1) {s : ℂ}
    (hs : s ∈ Metric.ball (3 / 2 : ℂ) (1 / 4)) (ρ : ℂ) :
    ‖(m ρ : ℂ) * (1 / (s - ρ) ^ 2)‖ ≤ 64 * ((m ρ : ℝ) / ‖ρ‖ ^ 2) := by
  by_cases h : m ρ = 0
  · simp [h]
  · obtain ⟨h0, h1⟩ := hm ρ h
    obtain ⟨h2, h3⟩ := r11Zs_dist hs h1
    have hρ0 : 0 < ‖ρ‖ := by
      rw [norm_pos_iff]
      intro h'
      rw [h'] at h0
      simp at h0
    rw [norm_mul, norm_div, norm_one, norm_pow, Complex.norm_natCast]
    have h4 : ‖ρ‖ ^ 2 ≤ 64 * ‖s - ρ‖ ^ 2 := by nlinarith
    have h5 : 1 / ‖s - ρ‖ ^ 2 ≤ 64 / ‖ρ‖ ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    calc (m ρ : ℝ) * (1 / ‖s - ρ‖ ^ 2) ≤ (m ρ : ℝ) * (64 / ‖ρ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg _)
      _ = 64 * ((m ρ : ℝ) / ‖ρ‖ ^ 2) := by ring

lemma r11Zs_summable_sq (hS : Summable fun ρ : ℂ => (m ρ : ℝ) / ‖ρ‖ ^ 2)
    (hm : ∀ ρ, m ρ ≠ 0 → 0 < ρ.re ∧ ρ.re < 1) :
    Summable fun ρ : ℂ => (m ρ : ℂ) * (1 / ((3 / 2 : ℂ) - ρ) ^ 2) :=
  Summable.of_norm_bounded (hS.mul_left 64)
    (fun ρ => r11Zs_term_bound hm (Metric.mem_ball_self (by norm_num)) ρ)

/-- **Termwise differentiation of the Hadamard series** at `3/2`. -/
theorem r11Zs_hasDerivAt_tsum (hS : Summable fun ρ : ℂ => (m ρ : ℝ) / ‖ρ‖ ^ 2)
    (hm : ∀ ρ, m ρ ≠ 0 → 0 < ρ.re ∧ ρ.re < 1) :
    HasDerivAt (fun s : ℂ => ∑' ρ : ℂ, (m ρ : ℂ) * (1 / (s - ρ) + 1 / ρ))
      (-∑' ρ : ℂ, (m ρ : ℂ) * (1 / ((3 / 2 : ℂ) - ρ) ^ 2)) (3 / 2) := by
  have hmem : (3 / 2 : ℂ) ∈ Metric.ball (3 / 2 : ℂ) (1 / 4) := Metric.mem_ball_self (by norm_num)
  have key := hasDerivAt_tsum_of_isPreconnected (𝕜 := ℂ) (F := ℂ)
    (u := fun ρ : ℂ => 64 * ((m ρ : ℝ) / ‖ρ‖ ^ 2))
    (g := fun (ρ : ℂ) (s : ℂ) => (m ρ : ℂ) * (1 / (s - ρ) + 1 / ρ))
    (g' := fun (ρ : ℂ) (s : ℂ) => -((m ρ : ℂ) * (1 / (s - ρ) ^ 2)))
    (t := Metric.ball (3 / 2 : ℂ) (1 / 4)) (y₀ := 3 / 2) (y := 3 / 2)
    (hS.mul_left 64) Metric.isOpen_ball (convex_ball _ _).isPreconnected
    (fun ρ s hs => by
      by_cases h : m ρ = 0
      · simp only [h, Nat.cast_zero, zero_mul, neg_zero]
        exact hasDerivAt_const _ _
      · obtain ⟨h0, h1⟩ := hm ρ h
        have hne : s - ρ ≠ 0 := by
          intro h'
          have := (r11Zs_dist hs h1).1
          rw [h', norm_zero] at this
          linarith
        have h2 : HasDerivAt (fun s : ℂ => s - ρ) 1 s := (hasDerivAt_id s).sub_const ρ
        have h3 := ((h2.inv hne).add_const (1 / ρ)).const_mul (m ρ : ℂ)
        have e : (fun y : ℂ => (m ρ : ℂ) * (1 / (y - ρ) + 1 / ρ))
            = fun y => (m ρ : ℂ) * ((fun s : ℂ => s - ρ)⁻¹ y + 1 / ρ) := by
          funext y; simp [one_div]
        have h4 : HasDerivAt (fun y : ℂ => (m ρ : ℂ) * (1 / (y - ρ) + 1 / ρ))
            ((m ρ : ℂ) * (-1 / (s - ρ) ^ 2)) s := by
          rw [e]; exact h3
        exact h4.congr_deriv (by ring))
    (fun ρ s hs => by rw [norm_neg]; exact r11Zs_term_bound hm hs ρ) hmem
    (Hadamard.summable_partialFraction hS _) hmem
  rw [tsum_neg] at key
  exact key

lemma r11Zs_line_facts {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ‖ρ + 1 / 2‖ ^ 2 = 1 + ρ.im ^ 2 ∧ (1 / ((3 / 2 : ℂ) - ρ)).re = 1 / (1 + ρ.im ^ 2) ∧
      (1 / ((3 / 2 : ℂ) - ρ) ^ 2).re = (1 - ρ.im ^ 2) / (1 + ρ.im ^ 2) ^ 2 := by
  have hpos : (0 : ℝ) < 1 + ρ.im ^ 2 := by positivity
  have hre : ((3 / 2 : ℂ) - ρ).re = 1 := by
    rw [sub_re, hρ]; norm_num
  have him : ((3 / 2 : ℂ) - ρ).im = -ρ.im := by
    rw [sub_im]; norm_num
  have hns : normSq ((3 / 2 : ℂ) - ρ) = 1 + ρ.im ^ 2 := by
    rw [normSq_apply, hre, him]; ring
  have hinvre : (((3 / 2 : ℂ) - ρ)⁻¹).re = 1 / (1 + ρ.im ^ 2) := by
    rw [inv_re, hre, hns]
  have hinvim : (((3 / 2 : ℂ) - ρ)⁻¹).im = ρ.im / (1 + ρ.im ^ 2) := by
    rw [inv_im, him, hns, neg_neg]
  refine ⟨?_, ?_, ?_⟩
  · rw [Complex.sq_norm, normSq_apply]
    simp only [add_re, add_im, hρ]
    norm_num
    ring
  · rw [one_div, hinvre]
  · rw [one_div, ← inv_pow, sq, mul_re, hinvre, hinvim]
    field_simp

lemma r11Zs_pt2 (hline : ∀ ρ, m ρ ≠ 0 → ρ.re = 1 / 2) (ρ : ℂ) :
    (m ρ : ℝ) / ‖ρ + 1 / 2‖ ^ 2 = (m ρ : ℝ) * (1 / ((3 / 2 : ℂ) - ρ)).re := by
  by_cases h : m ρ = 0
  · simp [h]
  · obtain ⟨h1, h2, -⟩ := r11Zs_line_facts (hline ρ h)
    rw [h1, h2]; ring

lemma r11Zs_pt4 (hline : ∀ ρ, m ρ ≠ 0 → ρ.re = 1 / 2) (ρ : ℂ) :
    (m ρ : ℝ) / ‖ρ + 1 / 2‖ ^ 4 = 1 / 2 * ((m ρ : ℝ) * (1 / ((3 / 2 : ℂ) - ρ)).re
      + ((m ρ : ℂ) * (1 / ((3 / 2 : ℂ) - ρ) ^ 2)).re) := by
  by_cases h : m ρ = 0
  · simp [h]
  · obtain ⟨h1, h2, h3⟩ := r11Zs_line_facts (hline ρ h)
    have hpos : (0 : ℝ) < 1 + ρ.im ^ 2 := by positivity
    rw [show ‖ρ + 1 / 2‖ ^ 4 = (‖ρ + 1 / 2‖ ^ 2) ^ 2 by ring, h1, show ((m ρ : ℂ)) = (((m ρ : ℝ)) : ℂ) by norm_num, Complex.re_ofReal_mul, h2, h3]
    field_simp
    ring

end generic

section zeros

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

lemma r11Zs_zeroOrd_strip {ρ : ℂ} (h : zeroOrd χ ρ ≠ 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  unfold zeroOrd at h
  split_ifs at h with h1
  · exact h1
  · exact absurd rfl h

lemma r11Zs_zeroOrd_abs_re {ρ : ℂ} (h : zeroOrd χ ρ ≠ 0) : |ρ.re| ≤ 1 := by
  obtain ⟨h1, h2⟩ := r11Zs_zeroOrd_strip χ h
  rw [abs_le]; constructor <;> linarith

/-- Under GRH, `Z₂(χ) = ∑ m_ρ Re 1/(3/2 - ρ)`. -/
theorem r11Zs_Z2_eq (hGRH : DirichletLZerosOnLine) :
    r11Z χ 2 = ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / ((3 / 2 : ℂ) - ρ)).re :=
  tsum_congr fun ρ => r11Zs_pt2 (fun ρ h => re_eq_half_of_zeroOrd_ne_zero hGRH χ h) ρ

/-- Under GRH, `Z₄(χ) = ½ [∑ m_ρ Re 1/(3/2 - ρ) + Re ∑ m_ρ/(3/2 - ρ)²]`. -/
theorem r11Zs_Z4_eq (hGRH : DirichletLZerosOnLine)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) :
    r11Z χ 4 = 1 / 2 * (∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / ((3 / 2 : ℂ) - ρ)).re
      + (∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / ((3 / 2 : ℂ) - ρ) ^ 2)).re) := by
  have hm := fun ρ (h : zeroOrd χ ρ ≠ 0) => r11Zs_zeroOrd_strip χ h
  have hd := summable_re_inv hS (fun ρ h => r11Zs_zeroOrd_abs_re χ h)
  have h1 := (re_partialFraction hS hd (3 / 2)).1
  have h2 := r11Zs_summable_sq hS hm
  have h3 : Summable fun ρ : ℂ => ((zeroOrd χ ρ : ℂ) * (1 / ((3 / 2 : ℂ) - ρ) ^ 2)).re :=
    Complex.reCLM.summable h2
  rw [Complex.re_tsum h2, ← h1.tsum_add h3, ← tsum_mul_left]
  exact tsum_congr fun ρ => r11Zs_pt4 (fun ρ h => re_eq_half_of_zeroOrd_ne_zero hGRH χ h) ρ

end zeros

end DetPrimality.Bach
