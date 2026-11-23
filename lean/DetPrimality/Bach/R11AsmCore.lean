import Mathlib
import DetPrimality.Bach.R11Defs
import DetPrimality.Bach.LLSElem
import DetPrimality.Bach.LLSZeta

/-!
# Round 11 assembly, part 1: designB Lemmas 6, 7, 8 (the basic inequality)

With `X = W⁴`, `x = 3X`, `ℓ₀ = log 3 ≥ lo := 1.09861`, and for a non-principal `χ` mod `n` with
`χ a = 1` for all `1 ≤ a < X`:

* `r11Asm_Z3` : `Z₃ ≤ 0.002375` (termwise AM–GM form of Cauchy–Schwarz from `Z₂`, `Z₄`);
* `r11Asm_sum_ge` : `2 ∑_{m<X} Λ(m)√m log³(x/m) ≤ A₃(x) + Re Φ_χ̃(x)`  (positivity of `1 + Re χ̃`);
* `r11Asm_Tlt_ge` : `∑_{m<X} Λ(m)√m log³(x/m) ≥ lo³A₀ + 3lo²A₁ + 3lo A₂ + A₃` (at `X`);
* `r11Asm_A0_ge` (Lemma 6): `A₀(X) ≥ (2/3)W⁶ - 0.4336 W⁵ - (2/0.4336) r₁(X) W`.
  NOTE: `R11ZetaExplicit` only gives `|A₁ - main| ≤ Z₂ y + r₁(y)`, not the exact formula, so the
  `log`-terms do not cancel in `A₁(X) - A₁(Y)` as in designB; the price is the term
  `(2/δ₀) r₁(X) X^{1/4}` in place of designB's `γ₀ + 1`.
* `r11Asm_core` (Lemmas 7 + 8): the basic inequality (6.1), multiplied by `X = W⁴`.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt
local notation "χ₁" => (1 : DirichletCharacter ℂ 1)

/-! ## The ζ zero sums -/

theorem r11Asm_norm_facts {ρ : ℂ} (h : zeroOrd χ₁ ρ ≠ 0) :
    0 < ‖ρ‖ ∧ ‖ρ‖ ^ 2 ≤ ‖ρ + 1 / 2‖ ^ 2 ∧ 1 / 2 ≤ ‖ρ + 1 / 2‖ := by
  have hre : 0 < ρ.re := by
    unfold zeroOrd at h
    split_ifs at h with h1
    · exact h1.1
    · exact absurd rfl h
  have h0 : ρ ≠ 0 := by rintro rfl; simp at hre
  have e1 : ‖ρ‖ ^ 2 = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have e2 : ‖ρ + 1 / 2‖ ^ 2 = (ρ.re + 1 / 2) ^ 2 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hr : (ρ + 1 / 2).re = ρ.re + 1 / 2 := by simp
    have hi : (ρ + 1 / 2).im = ρ.im := by simp
    rw [hr, hi]; ring
  refine ⟨norm_pos_iff.mpr h0, by rw [e1, e2]; nlinarith, ?_⟩
  have h2 : (1 / 2 : ℝ) ^ 2 ≤ ‖ρ + 1 / 2‖ ^ 2 := by rw [e2]; nlinarith [sq_nonneg ρ.im]
  exact (sq_le_sq₀ (by norm_num) (norm_nonneg _)).mp h2

theorem r11Asm_summable (k : ℕ) (hk2 : 2 ≤ k) (hk4 : k ≤ 4) :
    Summable fun ρ : ℂ => (zeroOrd χ₁ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ k := by
  refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_)
    (llsZeta_summable.mul_left 4)
  by_cases h : zeroOrd χ₁ ρ = 0
  · simp [h]
  obtain ⟨hr, hrn, hn⟩ := r11Asm_norm_facts h
  set n := ‖ρ + 1 / 2‖ with hndef
  set r := ‖ρ‖ with hrdef
  have hn0 : 0 < n := by linarith
  have hm : (0 : ℝ) ≤ (zeroOrd χ₁ ρ : ℝ) := Nat.cast_nonneg _
  have e : n ^ k = n ^ 2 * n ^ (k - 2) := by rw [← pow_add]; congr 1; omega
  have h1 : (1 / 2 : ℝ) ^ (k - 2) ≤ n ^ (k - 2) := pow_le_pow_left₀ (by norm_num) hn _
  have h2 : (1 / 4 : ℝ) ≤ (1 / 2) ^ (k - 2) := by
    calc (1 / 4 : ℝ) = (1 / 2) ^ 2 := by norm_num
      _ ≤ (1 / 2) ^ (k - 2) := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h3 : r ^ 2 * (1 / 4) ≤ n ^ k := by
    rw [e]
    exact mul_le_mul hrn (h2.trans h1) (by norm_num) (by positivity)
  rw [div_le_iff₀ (pow_pos hn0 k)]
  have h4 : (zeroOrd χ₁ ρ : ℝ) = 4 * ((zeroOrd χ₁ ρ : ℝ) / r ^ 2) * (r ^ 2 * (1 / 4)) := by
    field_simp
  calc (zeroOrd χ₁ ρ : ℝ) = 4 * ((zeroOrd χ₁ ρ : ℝ) / r ^ 2) * (r ^ 2 * (1 / 4)) := h4
    _ ≤ 4 * ((zeroOrd χ₁ ρ : ℝ) / r ^ 2) * n ^ k :=
      mul_le_mul_of_nonneg_left h3 (by positivity)

/-- `Z₃ ≤ (t Z₂ + Z₄/t)/2` for every `t > 0` (Cauchy–Schwarz in AM–GM form). -/
theorem r11Asm_Z3_le {t : ℝ} (ht : 0 < t) :
    r11Z χ₁ 3 ≤ (t * r11Z χ₁ 2 + r11Z χ₁ 4 / t) / 2 := by
  have h2 := r11Asm_summable 2 le_rfl (by norm_num)
  have h3 := r11Asm_summable 3 (by norm_num) (by norm_num)
  have h4 := r11Asm_summable 4 (by norm_num) le_rfl
  have hs := (((h2.hasSum.mul_left t).add (h4.hasSum.div_const t)).div_const 2)
  have hle : ∀ ρ : ℂ, (zeroOrd χ₁ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ 3
      ≤ (t * ((zeroOrd χ₁ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ 2)
        + (zeroOrd χ₁ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ 4 / t) / 2 := by
    intro ρ
    set n := ‖ρ + 1 / 2‖ with hndef
    set m := (zeroOrd χ₁ ρ : ℝ) with hmdef
    have hm : 0 ≤ m := Nat.cast_nonneg _
    rcases (norm_nonneg (ρ + 1 / 2)).eq_or_lt with h0 | h0
    · rw [← hndef] at h0
      rw [← h0]; simp
    · rw [← hndef] at h0
      have e : (t * (m / n ^ 2) + m / n ^ 4 / t) / 2 - m / n ^ 3
          = m * (t * n - 1) ^ 2 / (2 * t * n ^ 4) := by
        field_simp; ring
      have : 0 ≤ m * (t * n - 1) ^ 2 / (2 * t * n ^ 4) := by positivity
      linarith
  have := h3.tsum_le_tsum hle hs.summable
  rw [hs.tsum_eq] at this
  exact this

theorem r11Asm_Z3 (hGRH : DirichletLZerosOnLine) (hZ : R11ZetaZ) : r11Z χ₁ 3 ≤ 0.002375 := by
  obtain ⟨h2, h4⟩ := hZ hGRH
  have h := r11Asm_Z3_le (t := 0.0505) (by norm_num)
  have h4' : r11Z χ₁ 4 / 0.0505 ≤ 0.00012 / 0.0505 :=
    div_le_div_of_nonneg_right h4 (by norm_num)
  have e : (0.00012 : ℝ) / 0.0505 ≤ 0.0023763 := by norm_num
  linarith

/-! ## Expansions of `r_j` -/

theorem r11Asm_r1 (y : ℝ) : r11r 1 y = 1.771 * Real.log y + 0.788 := by
  unfold r11r
  simp [Finset.sum_range_succ, r11gam]
  ring

theorem r11Asm_r2 (y : ℝ) :
    r11r 2 y = 1.771 * Real.log y ^ 2 + 0.296 * Real.log y + 2.561 := by
  unfold r11r
  simp [Finset.sum_range_succ, r11gam, Nat.factorial]
  ring

theorem r11Asm_r3 (y : ℝ) :
    r11r 3 y = 1.771 * Real.log y ^ 3 + 0.444 * Real.log y ^ 2 + 3.843 * Real.log y + 3.8915 := by
  unfold r11r
  have c1 : Nat.choose 3 1 = 3 := by decide
  simp [Finset.sum_range_succ, r11gam, c1, Nat.factorial]
  ring

/-! ## The explicit formula, specialised -/

theorem r11Asm_A1 (hGRH : DirichletLZerosOnLine) (hA : R11ZetaExplicit) {y : ℝ} (hy : 1 < y) :
    |r11A 1 y - 4 / 9 * y ^ ((3 : ℝ) / 2)| ≤ r11Z χ₁ 2 * y + r11r 1 y := by
  have h := hA hGRH 1 le_rfl (by norm_num) y hy
  convert h using 3 <;> norm_num [Nat.factorial]

theorem r11Asm_A2 (hGRH : DirichletLZerosOnLine) (hA : R11ZetaExplicit) {y : ℝ} (hy : 1 < y) :
    |r11A 2 y - 16 / 27 * y ^ ((3 : ℝ) / 2)| ≤ 2 * r11Z χ₁ 3 * y + r11r 2 y := by
  have h := hA hGRH 2 (by norm_num) (by norm_num) y hy
  convert h using 3 <;> norm_num [Nat.factorial]

theorem r11Asm_A3 (hGRH : DirichletLZerosOnLine) (hA : R11ZetaExplicit) {y : ℝ} (hy : 1 < y) :
    |r11A 3 y - 32 / 27 * y ^ ((3 : ℝ) / 2)| ≤ 6 * r11Z χ₁ 4 * y + r11r 3 y := by
  have h := hA hGRH 3 (by norm_num) le_rfl y hy
  convert h using 3 <;> norm_num [Nat.factorial]

theorem r11Asm_rpow32 {x : ℝ} (hx : 0 < x) : x ^ ((3 : ℝ) / 2) = x * √x := by
  rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hx,
    Real.rpow_one]

theorem r11Asm_rpow_W {W : ℝ} (hW : 0 < W) : (W ^ 4) ^ ((3 : ℝ) / 2) = W ^ 6 := by
  rw [r11Asm_rpow32 (by positivity), show W ^ 4 = (W ^ 2) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]
  ring

theorem r11Asm_exp_neg_le {t : ℝ} (ht : 0 ≤ t) : Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 := by
  have h := Real.quadratic_le_exp_of_nonneg ht
  have hpos : 0 < 1 + t + t ^ 2 / 2 := by positivity
  rw [Real.exp_neg]
  refine (inv_anti₀ hpos h).trans ?_
  rw [inv_le_iff_one_le_mul₀ hpos]
  nlinarith [sq_nonneg (t ^ 2)]

/-! ## Sum manipulations -/

theorem r11Asm_sum_ge {q : ℕ} (χ : DirichletCharacter ℂ q) {X x : ℝ} (hXx : X ≤ x)
    (h1 : ∀ m : ℕ, 1 ≤ m → (m : ℝ) < X → χ (m : ZMod q) = 1) :
    2 * ∑ m ∈ Finset.range ⌈X⌉₊, Λ m * √(m : ℝ) * Real.log (x / m) ^ 3
      ≤ r11A 3 x + (r11Phi χ x).re := by
  have hre : (r11Phi χ x).re = ∑ m ∈ Finset.range ⌈x⌉₊,
      Λ m * (χ (m : ZMod q)).re * (√(m : ℝ) * Real.log (x / m) ^ 3) := by
    unfold r11Phi
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero]
  have hsum : r11A 3 x + (r11Phi χ x).re = ∑ m ∈ Finset.range ⌈x⌉₊,
      Λ m * (1 + (χ (m : ZMod q)).re) * (√(m : ℝ) * Real.log (x / m) ^ 3) := by
    rw [hre]; unfold r11A
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hleft : 2 * ∑ m ∈ Finset.range ⌈X⌉₊, Λ m * √(m : ℝ) * Real.log (x / m) ^ 3
      = ∑ m ∈ Finset.range ⌈X⌉₊,
        Λ m * (1 + (χ (m : ZMod q)).re) * (√(m : ℝ) * Real.log (x / m) ^ 3) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp
    · have hlt : (m : ℝ) < X := Nat.lt_ceil.mp (Finset.mem_range.mp hm)
      rw [h1 m hpos hlt, Complex.one_re]; ring
  rw [hsum, hleft]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.ceil_mono hXx))
    fun m hm _ => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp
  · have hlt : (m : ℝ) < x := Nat.lt_ceil.mp (Finset.mem_range.mp hm)
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hpos
    have hlog : 0 ≤ Real.log (x / m) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
    have hχ : 0 ≤ 1 + (χ (m : ZMod q)).re := by
      have := (Complex.abs_re_le_norm (χ (m : ZMod q))).trans
        (DirichletCharacter.norm_le_one χ _)
      linarith [(abs_le.mp this).1]
    have := ArithmeticFunction.vonMangoldt_nonneg (n := m)
    positivity

theorem r11Asm_Tlt_ge {X lo : ℝ} (hX : 0 < X) (hlo0 : 0 ≤ lo) (hlo : lo ≤ Real.log 3) :
    lo ^ 3 * r11A 0 X + 3 * lo ^ 2 * r11A 1 X + 3 * lo * r11A 2 X + r11A 3 X
      ≤ ∑ m ∈ Finset.range ⌈X⌉₊, Λ m * √(m : ℝ) * Real.log (3 * X / m) ^ 3 := by
  calc lo ^ 3 * r11A 0 X + 3 * lo ^ 2 * r11A 1 X + 3 * lo * r11A 2 X + r11A 3 X
      = ∑ m ∈ Finset.range ⌈X⌉₊, Λ m * √(m : ℝ) * (lo + Real.log (X / m)) ^ 3 := by
        unfold r11A
        simp only [Finset.mul_sum]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ ≤ _ := by
        refine Finset.sum_le_sum fun m hm => ?_
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · simp
        · have hlt : (m : ℝ) < X := Nat.lt_ceil.mp (Finset.mem_range.mp hm)
          have hm0 : (0 : ℝ) < m := by exact_mod_cast hpos
          have hlog : 0 ≤ Real.log (X / m) :=
            Real.log_nonneg (by rw [le_div_iff₀ hm0]; linarith)
          have e : Real.log (3 * X / m) = Real.log 3 + Real.log (X / m) := by
            rw [mul_div_assoc, Real.log_mul (by norm_num) (by positivity)]
          rw [e]
          have h3 : (lo + Real.log (X / m)) ^ 3 ≤ (Real.log 3 + Real.log (X / m)) ^ 3 :=
            pow_le_pow_left₀ (by positivity) (by linarith) 3
          exact mul_le_mul_of_nonneg_left h3
            (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))

theorem r11Asm_A1_diff {X δ : ℝ} (hX : 0 < X) (hδ : 0 ≤ δ) :
    r11A 1 X - δ * r11A 0 X ≤ r11A 1 (X * Real.exp (-δ)) := by
  set Y := X * Real.exp (-δ) with hY
  have hY0 : 0 < Y := by positivity
  have hYX : Y ≤ X := by
    rw [hY]
    have : Real.exp (-δ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  have hlogY : Real.log Y = Real.log X - δ := by
    rw [hY, Real.log_mul hX.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
  have hsub : Finset.range ⌈Y⌉₊ ⊆ Finset.range ⌈X⌉₊ := Finset.range_mono (Nat.ceil_mono hYX)
  have e1 : r11A 1 X - δ * r11A 0 X
      = ∑ m ∈ Finset.range ⌈X⌉₊, Λ m * √(m : ℝ) * (Real.log (X / m) - δ) := by
    unfold r11A
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [e1, ← Finset.sum_sdiff hsub]
  have h2 : ∑ m ∈ Finset.range ⌈X⌉₊ \ Finset.range ⌈Y⌉₊,
      Λ m * √(m : ℝ) * (Real.log (X / m) - δ) ≤ 0 := by
    refine Finset.sum_nonpos fun m hm => ?_
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range, not_lt] at hm
    have hYm : Y ≤ m := Nat.ceil_le.mp hm.2
    have hm0 : (0 : ℝ) < m := lt_of_lt_of_le hY0 hYm
    have hl : Real.log (X / m) - δ ≤ 0 := by
      rw [Real.log_div hX.ne' hm0.ne']
      have := Real.log_le_log hY0 hYm
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)) hl
  have h3 : ∑ m ∈ Finset.range ⌈Y⌉₊, Λ m * √(m : ℝ) * (Real.log (X / m) - δ) = r11A 1 Y := by
    unfold r11A
    refine Finset.sum_congr rfl fun m _ => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp
    · have hm0 : (0 : ℝ) < m := by exact_mod_cast hpos
      rw [Real.log_div hX.ne' hm0.ne', Real.log_div hY0.ne' hm0.ne', hlogY]
      ring
  linarith

/-! ## Lemma 6 -/

theorem r11Asm_A0_ge (hGRH : DirichletLZerosOnLine) (hZ : R11ZetaZ) (hA : R11ZetaExplicit)
    {W : ℝ} (hW : 3 ≤ W) :
    2 / 3 * W ^ 6 - 0.4336 * W ^ 5 - 2 / 0.4336 * r11r 1 (W ^ 4) * W ≤ r11A 0 (W ^ 4) := by
  have hW0 : 0 < W := by linarith
  obtain ⟨hZ2, -⟩ := hZ hGRH
  set X := W ^ 4 with hXdef
  have hX81 : (81 : ℝ) ≤ X := by
    rw [hXdef]
    calc (81 : ℝ) = 3 ^ 4 := by norm_num
      _ ≤ W ^ 4 := pow_le_pow_left₀ (by norm_num) hW 4
  have hX0 : 0 < X := by linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 0.4336 / W := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 0.15 := by
    rw [hδ, div_le_iff₀ hW0]; linarith
  have hδW : δ * W = 0.4336 := by rw [hδ]; field_simp
  set Y := X * Real.exp (-δ) with hY
  have hexp : 1 - δ ≤ Real.exp (-δ) := by
    have := Real.add_one_le_exp (-δ); linarith
  have hexp1 : Real.exp (-δ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hY1 : 1 < Y := by rw [hY]; nlinarith
  have hYX : Y ≤ X := by rw [hY]; nlinarith
  have hlogY : Real.log Y = Real.log X - δ := by
    rw [hY, Real.log_mul hX0.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
  have hdiff := r11Asm_A1_diff hX0 hδ0.le
  rw [← hY] at hdiff
  have hX1 := (abs_le.mp (r11Asm_A1 hGRH hA (by linarith : (1 : ℝ) < X))).1
  have hY2 := (abs_le.mp (r11Asm_A1 hGRH hA hY1)).2
  have hXp : X ^ ((3 : ℝ) / 2) = W ^ 6 := r11Asm_rpow_W hW0
  have hYp : Y ^ ((3 : ℝ) / 2) ≤ W ^ 6 * (1 - 3 / 2 * δ + (3 / 2 * δ) ^ 2 / 2) := by
    rw [hY, Real.mul_rpow hX0.le (Real.exp_pos _).le, hXp, ← Real.exp_mul]
    have h1 : -δ * (3 / 2) = -(3 / 2 * δ) := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left (r11Asm_exp_neg_le (by positivity)) (by positivity)
  rw [hXp] at hX1
  rw [r11Asm_r1] at hX1 hY2 ⊢
  rw [hlogY] at hY2
  set l := Real.log X with hl
  set A0 := r11A 0 X
  set A1X := r11A 1 X
  set A1Y := r11A 1 Y
  set Z2 := r11Z χ₁ 2
  have hZX : Z2 * X ≤ 0.047 * X := mul_le_mul_of_nonneg_right hZ2 hX0.le
  have hZY : Z2 * Y ≤ 0.047 * X :=
    (mul_le_mul_of_nonneg_right hZ2 (by linarith)).trans
      (mul_le_mul_of_nonneg_left hYX (by norm_num))
  -- `δ A₀ ≥ A₁(X) - A₁(Y) ≥ ...`
  have h5 : 4 / 9 * W ^ 6 * (3 / 2 * δ - (3 / 2 * δ) ^ 2 / 2) - 0.094 * W ^ 4
      - 2 * (1.771 * l + 0.788) ≤ δ * A0 := by
    have hYp' := mul_le_mul_of_nonneg_left hYp (by norm_num : (0 : ℝ) ≤ 4 / 9)
    have hδl : 0 ≤ 1.771 * δ := by positivity
    linarith
  have h6 := mul_le_mul_of_nonneg_right h5 hW0.le
  have e1 : (4 / 9 * W ^ 6 * (3 / 2 * δ - (3 / 2 * δ) ^ 2 / 2) - 0.094 * W ^ 4
      - 2 * (1.771 * l + 0.788)) * W
      = 2 / 3 * (δ * W) * W ^ 6 - 1 / 2 * (δ * W) ^ 2 * W ^ 5 - 0.094 * W ^ 5
        - 2 * (1.771 * l + 0.788) * W := by ring
  have e2 : δ * A0 * W = δ * W * A0 := by ring
  rw [e1, e2, hδW] at h6
  have hW5 : 0 < W ^ 5 := by positivity
  have e3 : 2 / 0.4336 * (1.771 * l + 0.788) * W
      = (1 / 0.4336) * (2 * (1.771 * l + 0.788) * W) := by ring
  rw [e3]
  nlinarith [h6, hW5]

/-! ## Lemmas 7 and 8: the basic inequality -/

/-- **designB (6.1)** multiplied by `X = W⁴` (`x = 3X`), with `log 3` replaced by `1.09861` on
the prime side, `Z₂ ≤ 0.047`, `Z₃ ≤ 0.002375`, `Z₄ ≤ 0.00012`, `√3 ≤ 1.7320509`, `κ = 12.4`. -/
theorem r11Asm_core (hGRH : DirichletLZerosOnLine) (hZ : R11ZetaZ) (hA : R11ZetaExplicit)
    (hC : R11ChiExplicit) (hG : R11ZeroSumGain) {n : ℕ} (hn : 2 < n)
    (χ : DirichletCharacter ℂ n) (hχ : χ ≠ 1) {W : ℝ} (hW : 3 ≤ W)
    (h : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < W ^ 4 → χ (a : ZMod n) = 1)
    (hlog3 : (1.09861 : ℝ) ≤ Real.log 3) (hsqrt3 : √(3 : ℝ) ≤ 1.7320509) :
    5.1046 * W ^ 6 - 1.1499 * W ^ 5 + 55.4247 * W ^ 4
      ≤ 4.5 * Real.log n * W ^ 4 + 18 * r11T (W ^ 4) * W ^ 4
        + (Real.log n + 1.30) * Real.log (3 * W ^ 4) ^ 3
        + 27.93 * Real.log (3 * W ^ 4) ^ 2 + 98.73 * Real.log (3 * W ^ 4) + 198.31
        + 12.2322 * r11r 1 (W ^ 4) * W + 7.2417 * r11r 1 (W ^ 4)
        + 6.5917 * r11r 2 (W ^ 4) + 2 * r11r 3 (W ^ 4) + r11r 3 (3 * W ^ 4) := by
  have hW0 : 0 < W := by linarith
  obtain ⟨hZ2, hZ4⟩ := hZ hGRH
  have hZ3 := r11Asm_Z3 hGRH hZ
  set X := W ^ 4 with hXdef
  have hX81 : (81 : ℝ) ≤ X := by
    rw [hXdef]
    calc (81 : ℝ) = 3 ^ 4 := by norm_num
      _ ≤ W ^ 4 := pow_le_pow_left₀ (by norm_num) hW 4
  have hX0 : 0 < X := by linarith
  have hX1 : (1 : ℝ) < X := by linarith
  have hx1 : (1 : ℝ) < 3 * X := by linarith
  obtain ⟨-, hprim, hne, hq0, -, hlq0, hlq, hχ1, -⟩ := llsElem_no_witness_facts hn χ hχ h
  have : NeZero χ.conductor := ⟨hq0⟩
  -- the L-side
  have hΦ := hC hGRH χ.conductor χ.primitiveCharacter hprim hne (3 * X) hx1
  have hZχ := hG hGRH χ.conductor χ.primitiveCharacter hprim hne X hX1.le hχ1
  have hS1 := r11Asm_sum_ge χ.primitiveCharacter (by linarith : X ≤ 3 * X) hχ1
  have hS2 := r11Asm_Tlt_ge hX0 (by norm_num) hlog3
  -- the ζ-side
  have hA0 := r11Asm_A0_ge hGRH hZ hA hW
  have hA1 := (abs_le.mp (r11Asm_A1 hGRH hA hX1)).1
  have hA2 := (abs_le.mp (r11Asm_A2 hGRH hA hX1)).1
  have hA3 := (abs_le.mp (r11Asm_A3 hGRH hA hX1)).1
  have hA3x := (abs_le.mp (r11Asm_A3 hGRH hA hx1)).2
  have hXp : X ^ ((3 : ℝ) / 2) = W ^ 6 := r11Asm_rpow_W hW0
  have hxp : (3 * X) ^ ((3 : ℝ) / 2) ≤ 3 * 1.7320509 * W ^ 6 := by
    rw [r11Asm_rpow32 (by linarith), Real.sqrt_mul (by norm_num), hXdef,
      show W ^ 4 = (W ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    have : 3 * (W ^ 2) ^ 2 * (√3 * W ^ 2) = 3 * √3 * W ^ 6 := by ring
    rw [this]
    have hW6 : 0 < W ^ 6 := by positivity
    nlinarith
  rw [hXp] at hA1 hA2 hA3
  rw [← hXdef] at hA0
  set lam := Real.log (3 * X) with hlam
  have hlam0 : 0 ≤ lam := Real.log_nonneg hx1.le
  set L := Real.log n with hL
  set lq := Real.log χ.conductor with hlqdef
  set T := r11T X
  set Zχ := r11Z χ.primitiveCharacter 4
  set Φ := (r11Phi χ.primitiveCharacter (3 * X)).re
  set S := ∑ m ∈ Finset.range ⌈X⌉₊, Λ m * √(m : ℝ) * Real.log (3 * X / m) ^ 3
  set A0 := r11A 0 X
  set A1 := r11A 1 X
  set A2 := r11A 2 X
  set A3 := r11A 3 X
  set A3x := r11A 3 (3 * X)
  set r1 := r11r 1 X
  set r2 := r11r 2 X
  set r3 := r11r 3 X
  set r3x := r11r 3 (3 * X)
  set Z2 := r11Z χ₁ 2
  set Z3 := r11Z χ₁ 3
  set Z4 := r11Z χ₁ 4
  have hW4 : W ^ 4 = X := rfl
  have b1 : Z2 * X ≤ 0.047 * X := mul_le_mul_of_nonneg_right hZ2 hX0.le
  have b2 : 2 * Z3 * X ≤ 2 * 0.002375 * X := by nlinarith
  have b3 : 6 * Z4 * X ≤ 6 * 0.00012 * X := by nlinarith
  have b4 : 6 * Z4 * (3 * X) ≤ 6 * 0.00012 * (3 * X) := by nlinarith
  have b5 : 6 * (3 * X) * Zχ ≤ 6 * (3 * X) * ((lq - 12.4 + 4 * T) / 4) :=
    mul_le_mul_of_nonneg_left hZχ (by positivity)
  have b6 : lq * X ≤ L * X := mul_le_mul_of_nonneg_right hlq hX0.le
  have b7 : lq * lam ^ 3 ≤ L * lam ^ 3 := mul_le_mul_of_nonneg_right hlq (by positivity)
  have b8 := mul_le_mul_of_nonneg_left hxp (by norm_num : (0 : ℝ) ≤ 32 / 27)
  have hW6 : 0 < W ^ 6 := by positivity
  have hW5 : 0 < W ^ 5 := by positivity
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX1.le
  have hr1 : 0 ≤ r1 := by
    show 0 ≤ r11r 1 X
    rw [r11Asm_r1]; positivity
  have hr2 : 0 ≤ r2 := by
    show 0 ≤ r11r 2 X
    rw [r11Asm_r2]; positivity
  have hr1W : 0 ≤ r1 * W := mul_nonneg hr1 hW0.le
  linarith

end DetPrimality.Bach
