import Mathlib
import DetPrimality.Bach.R13Defs

/-!
# Round 13 assembly, part 1: signed positivity and the ζ side (formal076 §4.3)

* `r13A_sum_ge` : signed positivity with the sign cell `[0, L₁]`:
  `2A(X) − 2A(e^{-L₁}x) + A(x) ≤ ∑_j θ_j/j! · Re Φ_{χ,j}(x)` when `χ = 1` below `X = e^{-ℓ}x`;
* `r13A_binom` : `A(Y) = ∑_j θ_j/j! ∑_{i≤j} C(j,i) log^{j-i}(x/Y) A_i(Y)`;
* `r13A_zeta` : from P1, `N₀ x^{3/2} − C x^{5/4} ≤ 2A(X) − 2A(e^{-L₁}x) + A(x)`.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

variable {J m : ℕ} {θ e : ℕ → ℝ} {ℓ L₁ N₀ : ℝ}

/-! ## Signed positivity -/

theorem r13A_re_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (θ : ℕ → ℝ) (J : ℕ) (x : ℝ) :
    ∑ j ∈ Finset.range (J + 1), θ j / (j.factorial : ℝ) * (r13Phi χ j x).re
      = ∑ n ∈ Finset.range ⌈x⌉₊,
        Λ n * (χ (n : ZMod q)).re * (Real.sqrt n * r13W θ J (Real.log (x / n))) := by
  have hre : ∀ j, (r13Phi χ j x).re = ∑ n ∈ Finset.range ⌈x⌉₊,
      Λ n * (χ (n : ZMod q)).re * (Real.sqrt n * Real.log (x / n) ^ j) := by
    intro j
    unfold r13Phi
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero]
  simp only [hre, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold r13W
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Signed positivity** (generalises `r11Asm_sum_ge`). -/
theorem r13A_sum_ge {q : ℕ} (χ : DirichletCharacter ℂ q) {X x : ℝ}
    (cert : R13Cert J m θ e ℓ L₁ N₀) (hx : x = Real.exp ℓ * X)
    (h1 : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < X → χ (a : ZMod q) = 1) :
    2 * r13A θ J x X - 2 * r13A θ J x (Real.exp (-L₁) * x) + r13A θ J x x
      ≤ ∑ j ∈ Finset.range (J + 1), θ j / (j.factorial : ℝ) * (r13Phi χ j x).re := by
  rw [r13A_re_sum]
  obtain ⟨hL0, hL1⟩ := cert.range
  rcases lt_or_ge x 0 with hneg | hx0
  · have hXneg : X < 0 := by
      by_contra h
      rw [not_lt] at h
      have : 0 ≤ Real.exp ℓ * X := mul_nonneg (Real.exp_pos _).le h
      linarith
    have h1' : ⌈x⌉₊ = 0 := Nat.ceil_eq_zero.mpr hneg.le
    have h2' : ⌈X⌉₊ = 0 := Nat.ceil_eq_zero.mpr hXneg.le
    have h3' : ⌈Real.exp (-L₁) * x⌉₊ = 0 :=
      Nat.ceil_eq_zero.mpr (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hneg.le)
    simp [r13A, h1', h2', h3']
  obtain ⟨X₁, hX₁⟩ : ∃ X₁ : ℝ, X₁ = Real.exp (-L₁) * x := ⟨_, rfl⟩
  rw [← hX₁]
  have hee : Real.exp (-L₁) * Real.exp L₁ = 1 := by rw [← Real.exp_add]; simp
  have hxX₁ : x = Real.exp L₁ * X₁ := by rw [hX₁]; linear_combination -x * hee
  have hXX₁ : X ≤ X₁ := by
    have : X = Real.exp (-ℓ) * x := by
      rw [hx, ← mul_assoc, ← Real.exp_add]; simp
    rw [this, hX₁]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hx0
  have hX₁x : X₁ ≤ x := by
    rw [hX₁]
    have : Real.exp (-L₁) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ,
      f = fun n : ℕ => Λ n * Real.sqrt n * r13W θ J (Real.log (x / n)) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, g = fun n : ℕ =>
      Λ n * (χ (n : ZMod q)).re * (Real.sqrt n * r13W θ J (Real.log (x / n))) := ⟨_, rfl⟩
  have hfn : ∀ n, f n = Λ n * Real.sqrt n * r13W θ J (Real.log (x / n)) := fun n => by rw [hf]
  have hgn : ∀ n, g n
      = Λ n * (χ (n : ZMod q)).re * (Real.sqrt n * r13W θ J (Real.log (x / n))) :=
    fun n => by rw [hg]
  have hA : ∀ Y : ℝ, r13A θ J x Y = ∑ n ∈ Finset.range ⌈Y⌉₊, f n := fun Y => by
    unfold r13A; rw [hf]
  have sa : Finset.range ⌈X⌉₊ ⊆ Finset.range ⌈X₁⌉₊ := Finset.range_mono (Nat.ceil_mono hXX₁)
  have sb : Finset.range ⌈X₁⌉₊ ⊆ Finset.range ⌈x⌉₊ := Finset.range_mono (Nat.ceil_mono hX₁x)
  have eA1 : r13A θ J x X₁
      = ∑ n ∈ Finset.range ⌈X₁⌉₊ \ Finset.range ⌈X⌉₊, f n + r13A θ J x X := by
    rw [hA, hA]; exact (Finset.sum_sdiff sa).symm
  have eA2 : r13A θ J x x
      = ∑ n ∈ Finset.range ⌈x⌉₊ \ Finset.range ⌈X₁⌉₊, f n + r13A θ J x X₁ := by
    rw [hA, hA]; exact (Finset.sum_sdiff sb).symm
  have eG : ∑ n ∈ Finset.range ⌈x⌉₊, g n
      = ∑ n ∈ Finset.range ⌈x⌉₊ \ Finset.range ⌈X₁⌉₊, g n
        + (∑ n ∈ Finset.range ⌈X₁⌉₊ \ Finset.range ⌈X⌉₊, g n
          + ∑ n ∈ Finset.range ⌈X⌉₊, g n) := by
    rw [Finset.sum_sdiff sa, Finset.sum_sdiff sb]
  have hGa : ∑ n ∈ Finset.range ⌈X⌉₊, g n = r13A θ J x X := by
    rw [hA]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hfn, hgn]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · have hlt : (n : ℝ) < X := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
      rw [h1 n hpos hlt, Complex.one_re]; ring
  have hre : ∀ n : ℕ, |(χ (n : ZMod q)).re| ≤ 1 := fun n =>
    (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one χ _)
  have hGb : -∑ n ∈ Finset.range ⌈X₁⌉₊ \ Finset.range ⌈X⌉₊, f n
      ≤ ∑ n ∈ Finset.range ⌈X₁⌉₊ \ Finset.range ⌈X⌉₊, g n := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range, not_lt] at hn
    rw [hfn, hgn]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
    have hXn : X ≤ n := Nat.ceil_le.mp hn.2
    have hnX₁ : (n : ℝ) < X₁ := Nat.lt_ceil.mp hn.1
    have hxpos : 0 < x := by linarith
    have hLlo : L₁ ≤ Real.log (x / n) := by
      rw [Real.le_log_iff_exp_le (div_pos hxpos hn0), le_div_iff₀ hn0, hxX₁]
      nlinarith [Real.exp_pos L₁]
    have hLhi : Real.log (x / n) ≤ ℓ := by
      rw [Real.log_le_iff_le_exp (div_pos hxpos hn0), div_le_iff₀ hn0, hx]
      exact mul_le_mul_of_nonneg_left hXn (Real.exp_pos _).le
    have hW := cert.posCell _ hLlo hLhi
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have h1re : 0 ≤ 1 + (χ (n : ZMod q)).re := by linarith [(abs_le.mp (hre n)).1]
    have h0 : 0 ≤ Λ n * Real.sqrt n * r13W θ J (Real.log (x / n)) * (1 + (χ (n : ZMod q)).re) :=
      mul_nonneg (mul_nonneg (mul_nonneg hΛ (Real.sqrt_nonneg _)) hW) h1re
    linarith
  have hGc : ∑ n ∈ Finset.range ⌈x⌉₊ \ Finset.range ⌈X₁⌉₊, f n
      ≤ ∑ n ∈ Finset.range ⌈x⌉₊ \ Finset.range ⌈X₁⌉₊, g n := by
    refine Finset.sum_le_sum fun n hn => ?_
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range, not_lt] at hn
    rw [hfn, hgn]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
    have hX₁n : X₁ ≤ n := Nat.ceil_le.mp hn.2
    have hnx : (n : ℝ) < x := Nat.lt_ceil.mp hn.1
    have hxpos : 0 < x := by linarith
    have hLlo : 0 ≤ Real.log (x / n) :=
      Real.log_nonneg (by rw [le_div_iff₀ hn0]; linarith)
    have hLhi : Real.log (x / n) ≤ L₁ := by
      rw [Real.log_le_iff_le_exp (div_pos hxpos hn0), div_le_iff₀ hn0, hxX₁]
      exact mul_le_mul_of_nonneg_left hX₁n (Real.exp_pos _).le
    have hW := cert.negCell _ hLlo hLhi
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have h1re : 0 ≤ 1 - (χ (n : ZMod q)).re := by linarith [(abs_le.mp (hre n)).2]
    have h0 : 0 ≤ Λ n * Real.sqrt n * (-r13W θ J (Real.log (x / n)))
        * (1 - (χ (n : ZMod q)).re) :=
      mul_nonneg (mul_nonneg (mul_nonneg hΛ (Real.sqrt_nonneg _)) (by linarith)) h1re
    linarith
  have hGoal : ∑ n ∈ Finset.range ⌈x⌉₊,
      Λ n * (χ (n : ZMod q)).re * (Real.sqrt n * r13W θ J (Real.log (x / n)))
      = ∑ n ∈ Finset.range ⌈x⌉₊, g n := by rw [hg]
  rw [hGoal]
  linarith

/-! ## The ζ side -/

/-- Binomial re-expansion `log(x/n) = log(x/Y) + log(Y/n)`. -/
theorem r13A_binom (θ : ℕ → ℝ) (J : ℕ) {x Y : ℝ} (hx : 0 < x) (hY : 0 < Y) :
    r13A θ J x Y = ∑ j ∈ Finset.range (J + 1), θ j / (j.factorial : ℝ) *
      ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * Real.log (x / Y) ^ (j - i) * r11A i Y := by
  unfold r13A r11A r13W
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
  have e : Real.log (x / n) = Real.log (Y / n) + Real.log (x / Y) := by
    rw [Real.log_div hx.ne' hn0.ne', Real.log_div hY.ne' hn0.ne', Real.log_div hx.ne' hY.ne']
    ring
  rw [e, add_pow]
  simp only [Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem r13A_R_eq (θ : ℕ → ℝ) (J : ℕ) (lam : ℝ) :
    ∑ j ∈ Finset.range (J + 1), θ j / (j.factorial : ℝ) *
      ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * lam ^ (j - i) * ((i.factorial : ℝ) * (2 / 3) ^ (i + 1))
      = r13R θ J lam := by
  unfold r13R
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_range_reflect
    (fun i => lam ^ i / (i.factorial : ℝ) * (2 / 3 : ℝ) ^ (j + 1 - i)) (j + 1),
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have e1 : j + 1 - 1 - i = j - i := by omega
  have e2 : j + 1 - (j - i) = i + 1 := by omega
  rw [e1, e2]
  have hc : (j.choose i : ℝ) * (i.factorial : ℝ) * ((j - i).factorial : ℝ)
      = (j.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
  have h1 : (i.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((j - i).factorial : ℝ) ≠ 0 := by positivity
  have h3 : (j.choose i : ℝ) ≠ 0 := by
    have := Nat.choose_pos hi'
    positivity
  rw [← hc]
  field_simp

theorem r13A_zeta_one (hGRH : DirichletLZerosOnLine) (hZ : R13ZetaSmooth) (θ : ℕ → ℝ) (J : ℕ)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x Y : ℝ, 1 ≤ Y → x = Real.exp lam * Y →
      |r13A θ J x Y - Real.exp (-(3 * lam / 2)) * r13R θ J lam * x ^ ((3 : ℝ) / 2)|
        ≤ C * x ^ ((5 : ℝ) / 4) := by
  choose Ci hCi using hZ hGRH
  have hCi0 : ∀ i, 0 ≤ Ci i := by
    intro i
    have := hCi i 1 le_rfl
    simp only [Real.one_rpow, mul_one] at this
    exact (abs_nonneg _).trans this
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℝ, c = fun j i =>
      θ j / (j.factorial : ℝ) * ((j.choose i : ℝ) * lam ^ (j - i)) := ⟨_, rfl⟩
  have hcji : ∀ j i, c j i = θ j / (j.factorial : ℝ) * ((j.choose i : ℝ) * lam ^ (j - i)) :=
    fun j i => by rw [hc]
  refine ⟨∑ j ∈ Finset.range (J + 1), ∑ i ∈ Finset.range (j + 1), |c j i| * Ci i, ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ =>
      mul_nonneg (abs_nonneg _) (hCi0 i)
  intro x Y hY hx
  have hY0 : 0 < Y := by linarith
  have hx0 : 0 < x := by rw [hx]; positivity
  have hYx : Y ≤ x := by
    rw [hx]
    have := Real.one_le_exp hlam
    nlinarith
  have hlog : Real.log (x / Y) = lam := by
    rw [hx, mul_div_assoc, div_self hY0.ne', mul_one, Real.log_exp]
  have hmain : Real.exp (-(3 * lam / 2)) * x ^ ((3 : ℝ) / 2) = Y ^ ((3 : ℝ) / 2) := by
    rw [hx, Real.mul_rpow (Real.exp_pos _).le hY0.le, ← Real.exp_mul, ← mul_assoc,
      ← Real.exp_add]
    have : -(3 * lam / 2) + lam * (3 / 2) = 0 := by ring
    rw [this, Real.exp_zero, one_mul]
  have hpow : Y ^ ((5 : ℝ) / 4) ≤ x ^ ((5 : ℝ) / 4) :=
    Real.rpow_le_rpow hY0.le hYx (by norm_num)
  have e1 : r13A θ J x Y = ∑ j ∈ Finset.range (J + 1), ∑ i ∈ Finset.range (j + 1),
      c j i * r11A i Y := by
    rw [r13A_binom θ J hx0 hY0, hlog]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hcji]; ring
  have e2 : r13R θ J lam * Y ^ ((3 : ℝ) / 2)
      = ∑ j ∈ Finset.range (J + 1), ∑ i ∈ Finset.range (j + 1),
        c j i * ((i.factorial : ℝ) * (2 / 3) ^ (i + 1) * Y ^ ((3 : ℝ) / 2)) := by
    rw [← r13A_R_eq θ J lam, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hcji]; ring
  have e3 : r13A θ J x Y - Real.exp (-(3 * lam / 2)) * r13R θ J lam * x ^ ((3 : ℝ) / 2)
      = ∑ j ∈ Finset.range (J + 1), ∑ i ∈ Finset.range (j + 1),
        c j i * (r11A i Y - (i.factorial : ℝ) * (2 / 3) ^ (i + 1) * Y ^ ((3 : ℝ) / 2)) := by
    have : Real.exp (-(3 * lam / 2)) * r13R θ J lam * x ^ ((3 : ℝ) / 2)
        = r13R θ J lam * Y ^ ((3 : ℝ) / 2) := by rw [← hmain]; ring
    rw [this, e1, e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e3, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have h := hCi i Y hY
  calc |c j i| * |r11A i Y - (i.factorial : ℝ) * (2 / 3) ^ (i + 1) * Y ^ ((3 : ℝ) / 2)|
      ≤ |c j i| * (Ci i * Y ^ ((5 : ℝ) / 4)) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ ≤ |c j i| * (Ci i * x ^ ((5 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (hCi0 i)) (abs_nonneg _)
    _ = |c j i| * Ci i * x ^ ((5 : ℝ) / 4) := by ring

/-- **ζ side**: main term of the left side of `r13A_sum_ge`. -/
theorem r13A_zeta (hGRH : DirichletLZerosOnLine) (hZ : R13ZetaSmooth)
    (cert : R13Cert J m θ e ℓ L₁ N₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 1 ≤ X → ∀ x : ℝ, x = Real.exp ℓ * X →
      N₀ * x ^ ((3 : ℝ) / 2) - C * x ^ ((5 : ℝ) / 4)
        ≤ 2 * r13A θ J x X - 2 * r13A θ J x (Real.exp (-L₁) * x) + r13A θ J x x := by
  obtain ⟨hL0, hL1⟩ := cert.range
  obtain ⟨Ca, hCa0, hCa⟩ := r13A_zeta_one hGRH hZ θ J (lam := ℓ) (by linarith)
  obtain ⟨Cb, hCb0, hCb⟩ := r13A_zeta_one hGRH hZ θ J (lam := L₁) hL0
  obtain ⟨Cc, hCc0, hCc⟩ := r13A_zeta_one hGRH hZ θ J (lam := 0) le_rfl
  refine ⟨2 * Ca + 2 * Cb + Cc, by positivity, fun X hX x hx => ?_⟩
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx1 : 1 ≤ x := by
    rw [hx]
    have := Real.one_le_exp (by linarith : 0 ≤ ℓ)
    nlinarith
  have ha := abs_le.mp (hCa x X hX hx)
  have hX₁ : 1 ≤ Real.exp (-L₁) * x := by
    rw [hx, ← mul_assoc, ← Real.exp_add]
    have : 1 ≤ Real.exp (-L₁ + ℓ) := Real.one_le_exp (by linarith)
    nlinarith
  have hb := abs_le.mp (hCb x (Real.exp (-L₁) * x) hX₁
    (by rw [← mul_assoc, ← Real.exp_add]; simp))
  have hc' := hCc x x hx1 (by simp)
  rw [show Real.exp (-(3 * (0 : ℝ) / 2)) = 1 by norm_num, one_mul] at hc'
  have hc := abs_le.mp hc'
  have hnum := cert.num.2
  have hp : 0 ≤ x ^ ((3 : ℝ) / 2) := by positivity
  have hp' : 0 ≤ x ^ ((5 : ℝ) / 4) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hnum hp
  linarith [ha.1, hb.2, hc.1]

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r13A_sum_ge
#print axioms DetPrimality.Bach.r13A_zeta
