import Mathlib
import DetPrimality.Bach.R13Defs
import DetPrimality.Bach.Growth
import DetPrimality.Bach.HadamardL
import DetPrimality.Bach.R11ChiBound

/-!
# Round 13 assembly, part 2: the χ side (formal076 §4.3)

`r13A_chi` : from P2 (`R13ChiExplicit`), P3 (`R13ZeroPow`) and the exact modulus `cert.modulus`
at `t = γ`: under GRH `‖x^{ρ+½} K(ρ+½)‖ ≤ x·G(γ)` and
`∑_ρ G(γ) = ∑_k e_k ∑_ρ Re (3/2−ρ)^{-k} ≤ (e₁/2) log q + C`.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

variable {J m : ℕ} {θ e : ℕ → ℝ} {ℓ L₁ N₀ : ℝ}

/-- Geometry of a zero on the critical line, in the Perron variable `w = ρ + 1/2 = 1 + iγ`. -/
theorem r13A_zero_geom (hGRH : DirichletLZerosOnLine) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {ρ : ℂ} (h : zeroOrd χ ρ ≠ 0) :
    ρ + 1 / 2 = 1 + (ρ.im : ℂ) * I ∧ (3 / 2 : ℂ) - ρ = (starRingEnd ℂ) (ρ + 1 / 2) ∧
      1 ≤ ‖ρ + 1 / 2‖ ∧ ‖ρ‖ ≤ ‖ρ + 1 / 2‖ ∧ 0 < ‖ρ‖ := by
  have hρ := re_eq_half_of_zeroOrd_ne_zero hGRH χ h
  obtain ⟨hre, hconj⟩ := r11Chi_zero_geom hGRH χ h
  have him : (ρ + 1 / 2).im = ρ.im := by simp
  have h1 : 1 ≤ ‖ρ + 1 / 2‖ := by
    have := Complex.re_le_norm (ρ + 1 / 2)
    rw [hre] at this
    exact this
  refine ⟨?_, hconj, h1, ?_, ?_⟩
  · apply Complex.ext
    · rw [hre]; simp
    · rw [him]; simp
  · have ha2 : ‖ρ‖ ^ 2 = 1 / 4 + ρ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hρ]; ring
    have hb2 : ‖ρ + 1 / 2‖ ^ 2 = 1 + ρ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by rw [ha2, hb2]; linarith)
  · exact norm_pos_iff.mpr (fun h0 => by rw [h0] at hρ; norm_num at hρ)

theorem r13A_pow_ge (hGRH : DirichletLZerosOnLine) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {ρ : ℂ} (h : zeroOrd χ ρ ≠ 0) {k : ℕ} (hk : 2 ≤ k) :
    (zeroOrd χ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ k ≤ (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2 := by
  obtain ⟨-, -, h1, h2, h3⟩ := r13A_zero_geom hGRH χ h
  refine div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) ?_
  calc ‖ρ‖ ^ 2 ≤ ‖ρ + 1 / 2‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ ≤ ‖ρ + 1 / 2‖ ^ k := pow_le_pow_right₀ h1 hk

/-- Summability of the zero sum in P2 (order `j ≥ 1`). -/
theorem r13A_summable_T (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)
    {x : ℝ} (hx : 0 < x) {j : ℕ} (hj : 1 ≤ j) :
    Summable fun ρ : ℂ =>
      (zeroOrd χ ρ : ℂ) * (x : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2) ^ (j + 1) := by
  refine Summable.of_norm_bounded (hS.mul_left x) fun ρ => ?_
  by_cases h0 : zeroOrd χ ρ = 0
  · simp [h0]
  obtain ⟨hw, -, -, -, -⟩ := r13A_zero_geom hGRH χ h0
  have hre : (ρ + 1 / 2).re = 1 := by rw [hw]; simp
  rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, hre, Real.rpow_one]
  have := r13A_pow_ge hGRH χ h0 (k := j + 1) (by omega)
  calc (zeroOrd χ ρ : ℝ) * x / ‖ρ + 1 / 2‖ ^ (j + 1)
      = x * ((zeroOrd χ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ (j + 1)) := by ring
    _ ≤ x * ((zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) := mul_le_mul_of_nonneg_left this hx.le

/-- Summability of the zero sums in P3 (order `k ≥ 1`). -/
theorem r13A_summable_re (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)
    {k : ℕ} (hk : 1 ≤ k) :
    Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ k).re := by
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    simpa only [pow_one] using r11Chi_summable_re_inv hGRH χ hS
  refine Summable.of_norm_bounded hS fun ρ => ?_
  by_cases h0 : zeroOrd χ ρ = 0
  · simp [h0]
  obtain ⟨-, hconj, -, -, -⟩ := r13A_zero_geom hGRH χ h0
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  have h1 : |((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ k).re| ≤ 1 / ‖ρ + 1 / 2‖ ^ k := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_div, norm_one, norm_pow, hconj, Complex.norm_conj]
  calc (zeroOrd χ ρ : ℝ) * |((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ k).re|
      ≤ (zeroOrd χ ρ : ℝ) * (1 / ‖ρ + 1 / 2‖ ^ k) :=
        mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    _ = (zeroOrd χ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ k := by ring
    _ ≤ (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2 := r13A_pow_ge hGRH χ h0 hk2

/-- The zero sum through the exact modulus. -/
theorem r13A_zero_sum_le (hGRH : DirichletLZerosOnLine) (cert : R13Cert J m θ e ℓ L₁ N₀)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    {x : ℝ} (hx : 0 < x) :
    ‖∑' ρ : ℂ, ∑ j ∈ Finset.range (J + 1), (θ j : ℂ) *
        ((zeroOrd χ ρ : ℂ) * (x : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2) ^ (j + 1))‖
      ≤ x * ∑ k ∈ Finset.Icc 1 m, e k *
        ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ k).re := by
  have hS := summable_zeroOrd_div_normSq_proof χ hχ hχ1 (growth_completedLFunction χ hχ1)
  have hSk : ∀ k ∈ Finset.Icc 1 m, Summable fun ρ : ℂ =>
      (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ k).re :=
    fun k hk => r13A_summable_re hGRH χ hS (Finset.mem_Icc.mp hk).1
  have hterm : ∀ ρ : ℂ, ‖∑ j ∈ Finset.range (J + 1), (θ j : ℂ) *
        ((zeroOrd χ ρ : ℂ) * (x : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2) ^ (j + 1))‖
      ≤ x * ∑ k ∈ Finset.Icc 1 m,
        e k * ((zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ k).re) := by
    intro ρ
    by_cases h0 : zeroOrd χ ρ = 0
    · simp [h0]
    obtain ⟨hw, hconj, -, -, -⟩ := r13A_zero_geom hGRH χ h0
    have e1 : ∑ j ∈ Finset.range (J + 1), (θ j : ℂ) *
        ((zeroOrd χ ρ : ℂ) * (x : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2) ^ (j + 1))
        = (zeroOrd χ ρ : ℂ) * (x : ℂ) ^ (ρ + 1 / 2) * r13K θ J (ρ + 1 / 2) := by
      unfold r13K
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∑ k ∈ Finset.Icc 1 m,
        e k * ((zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ k).re)
        = (zeroOrd χ ρ : ℝ) * r13G e m ρ.im := by
      unfold r13G
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : ((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ k).re
          = ((1 : ℂ) / (1 + (ρ.im : ℂ) * I) ^ k).re := by
        calc ((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ k).re
            = ((starRingEnd ℂ) ((1 : ℂ) / (ρ + 1 / 2) ^ k)).re := by
              rw [hconj, map_div₀, map_one, map_pow]
          _ = ((1 : ℂ) / (ρ + 1 / 2) ^ k).re := Complex.conj_re _
          _ = ((1 : ℂ) / (1 + (ρ.im : ℂ) * I) ^ k).re := by rw [← hw]
      rw [this]; ring
    have hre : (ρ + 1 / 2).re = 1 := by rw [hw]; simp
    have hmod := cert.modulus ρ.im
    rw [← hw] at hmod
    rw [e1, e2, norm_mul, norm_mul, Complex.norm_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hx, hre, Real.rpow_one]
    calc (zeroOrd χ ρ : ℝ) * x * ‖r13K θ J (ρ + 1 / 2)‖
        ≤ (zeroOrd χ ρ : ℝ) * x * r13G e m ρ.im :=
          mul_le_mul_of_nonneg_left hmod (mul_nonneg (Nat.cast_nonneg _) hx.le)
      _ = x * ((zeroOrd χ ρ : ℝ) * r13G e m ρ.im) := by ring
  have hsumG : Summable fun ρ : ℂ => x * ∑ k ∈ Finset.Icc 1 m,
      e k * ((zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ k).re) :=
    (summable_sum fun k hk => (hSk k hk).mul_left (e k)).mul_left x
  have hsumN : Summable fun ρ : ℂ => ‖∑ j ∈ Finset.range (J + 1), (θ j : ℂ) *
        ((zeroOrd χ ρ : ℂ) * (x : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2) ^ (j + 1))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumG
  calc ‖∑' ρ : ℂ, ∑ j ∈ Finset.range (J + 1), (θ j : ℂ) *
        ((zeroOrd χ ρ : ℂ) * (x : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2) ^ (j + 1))‖
      ≤ ∑' ρ : ℂ, ‖∑ j ∈ Finset.range (J + 1), (θ j : ℂ) *
        ((zeroOrd χ ρ : ℂ) * (x : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2) ^ (j + 1))‖ :=
        norm_tsum_le_tsum_norm hsumN
    _ ≤ ∑' ρ : ℂ, x * ∑ k ∈ Finset.Icc 1 m,
        e k * ((zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ k).re) :=
        hsumN.tsum_le_tsum hterm hsumG
    _ = x * ∑ k ∈ Finset.Icc 1 m, e k *
        ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ k).re := by
        rw [tsum_mul_left, Summable.tsum_finsetSum (fun k hk => (hSk k hk).mul_left (e k))]
        congr 1
        exact Finset.sum_congr rfl fun k _ => tsum_mul_left

/-- **χ side**: zero sum through the exact modulus. -/
theorem r13A_chi (hGRH : DirichletLZerosOnLine) (hC : R13ChiExplicit) (hP : R13ZeroPow)
    (cert : R13Cert J m θ e ℓ L₁ N₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      χ ≠ 1 → ∀ x : ℝ, 1 ≤ x →
        ∑ j ∈ Finset.range (J + 1), θ j / (j.factorial : ℝ) * (r13Phi χ j x).re
          ≤ x * (e 1 / 2 * Real.log q + C) + C * (Real.log q + 1) * (1 + Real.log x) ^ J
            + C * Real.sqrt x := by
  choose! Cj hCj using hC hGRH
  obtain ⟨⟨C1, hC1⟩, hP2⟩ := hP hGRH
  choose! Ck hCk using hP2
  have he1 := cert.e1pos
  obtain ⟨CE, hCE⟩ : ∃ CE : ℝ,
      CE = ∑ j ∈ Finset.range (J + 1), |θ j| / (j.factorial : ℝ) * |Cj j| := ⟨_, rfl⟩
  obtain ⟨CG, hCG⟩ : ∃ CG : ℝ,
      CG = e 1 * |C1| + ∑ k ∈ Finset.Icc 1 m, |e k| * |Ck k| := ⟨_, rfl⟩
  have hCE0 : 0 ≤ CE := by
    rw [hCE]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (div_nonneg (abs_nonneg _) (by positivity))
      (abs_nonneg _)
  have hCG0 : 0 ≤ CG := by
    rw [hCG]
    exact add_nonneg (mul_nonneg he1.le (abs_nonneg _))
      (Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  refine ⟨CE + CG, add_nonneg hCE0 hCG0, ?_⟩
  intro q _ χ hχ hχ1 x hx
  have hx0 : 0 < x := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlq1 : 0 ≤ Real.log q + 1 := by linarith
  have hlx1 : 1 ≤ 1 + Real.log x := by linarith
  have hS := summable_zeroOrd_div_normSq_proof χ hχ hχ1 (growth_completedLFunction χ hχ1)
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℂ, ∀ j, T j = ∑' ρ : ℂ,
      (zeroOrd χ ρ : ℂ) * (x : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2) ^ (j + 1) :=
    ⟨fun j => _, fun j => rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ,
      E = (Real.log q + 1) * (1 + Real.log x) ^ J + Real.sqrt x := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by
    rw [hE]
    exact add_nonneg (mul_nonneg hlq1 (pow_nonneg (by linarith) _)) (Real.sqrt_nonneg _)
  -- each order
  have hj : ∀ j ∈ Finset.range (J + 1), θ j / (j.factorial : ℝ) * (r13Phi χ j x).re
      ≤ -(((θ j : ℂ) * T j).re) + |θ j| / (j.factorial : ℝ) * |Cj j| * E := by
    intro j hjm
    by_cases h3 : 3 ≤ j
    · have hb := hCj j h3 q χ hχ hχ1 x hx
      rw [← hT j] at hb
      have hfac : (0 : ℝ) < j.factorial := by positivity
      have e1 : (r13Phi χ j x).re
          = (r13Phi χ j x + (j.factorial : ℂ) * T j).re - (j.factorial : ℝ) * (T j).re := by
        rw [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
          sub_zero]
        ring
      have e2 : ((θ j : ℂ) * T j).re = θ j * (T j).re := Complex.re_ofReal_mul _ _
      have hre := Complex.abs_re_le_norm (r13Phi χ j x + (j.factorial : ℂ) * T j)
      have hpow : (1 + Real.log x) ^ j ≤ (1 + Real.log x) ^ J :=
        pow_le_pow_right₀ hlx1 (by have := Finset.mem_range.mp hjm; omega)
      have hmono := mul_le_mul_of_nonneg_left hpow hlq1
      have hEj : 0 ≤ (Real.log q + 1) * (1 + Real.log x) ^ j + Real.sqrt x :=
        add_nonneg (mul_nonneg hlq1 (pow_nonneg (by linarith) _)) (Real.sqrt_nonneg _)
      have hE' : |(r13Phi χ j x + (j.factorial : ℂ) * T j).re| ≤ |Cj j| * E := by
        refine hre.trans (hb.trans ?_)
        calc Cj j * (Real.log q + 1) * (1 + Real.log x) ^ j + Cj j * Real.sqrt x
            = Cj j * ((Real.log q + 1) * (1 + Real.log x) ^ j + Real.sqrt x) := by ring
          _ ≤ |Cj j| * ((Real.log q + 1) * (1 + Real.log x) ^ j + Real.sqrt x) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) hEj
          _ ≤ |Cj j| * E := by
              rw [hE]
              exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      have h4 : θ j / (j.factorial : ℝ) * (r13Phi χ j x + (j.factorial : ℂ) * T j).re
          ≤ |θ j| / (j.factorial : ℝ) * |Cj j| * E := by
        calc θ j / (j.factorial : ℝ) * (r13Phi χ j x + (j.factorial : ℂ) * T j).re
            ≤ |θ j / (j.factorial : ℝ) * (r13Phi χ j x + (j.factorial : ℂ) * T j).re| :=
              le_abs_self _
          _ = |θ j| / (j.factorial : ℝ) * |(r13Phi χ j x + (j.factorial : ℂ) * T j).re| := by
              rw [abs_mul, abs_div, abs_of_pos hfac]
          _ ≤ |θ j| / (j.factorial : ℝ) * (|Cj j| * E) :=
              mul_le_mul_of_nonneg_left hE' (div_nonneg (abs_nonneg _) hfac.le)
          _ = |θ j| / (j.factorial : ℝ) * |Cj j| * E := by ring
      have h5 : θ j / (j.factorial : ℝ) * ((j.factorial : ℝ) * (T j).re) = θ j * (T j).re := by
        rw [← mul_assoc, div_mul_cancel₀ _ hfac.ne']
      rw [e1, e2, mul_sub, h5]
      linarith
    · have h0 : θ j = 0 := cert.low j (by omega)
      simp [h0]
  have hsum := Finset.sum_le_sum hj
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul, ← hCE] at hsum
  -- interchange
  have hZ : ∑ j ∈ Finset.range (J + 1), (θ j : ℂ) * T j
      = ∑' ρ : ℂ, ∑ j ∈ Finset.range (J + 1), (θ j : ℂ) *
        ((zeroOrd χ ρ : ℂ) * (x : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2) ^ (j + 1)) := by
    rw [Summable.tsum_finsetSum]
    · exact Finset.sum_congr rfl fun j _ => by rw [hT j, tsum_mul_left]
    · intro j _
      by_cases h3 : 3 ≤ j
      · exact (r13A_summable_T hGRH χ hS hx0 (by omega)).mul_left _
      · have h0 : θ j = 0 := cert.low j (by omega)
        simp [h0, summable_zero]
  have hz1 := r13A_zero_sum_le hGRH cert χ hχ hχ1 hx0
  rw [← hZ] at hz1
  have hz2 : -(∑ j ∈ Finset.range (J + 1), ((θ j : ℂ) * T j).re)
      ≤ ‖∑ j ∈ Finset.range (J + 1), (θ j : ℂ) * T j‖ := by
    rw [← Complex.re_sum]
    have := Complex.abs_re_le_norm (∑ j ∈ Finset.range (J + 1), (θ j : ℂ) * T j)
    linarith [(abs_le.mp this).1]
  -- the `G` sum
  have hA0 : 0 ≤ e 1 * (Real.log q / 2 + |C1|) :=
    mul_nonneg he1.le (add_nonneg (by linarith) (abs_nonneg _))
  have hk : ∀ k ∈ Finset.Icc 1 m,
      e k * ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ k).re
        ≤ (if k = 1 then e 1 * (Real.log q / 2 + |C1|) else 0) + |e k| * |Ck k| := by
    intro k hk
    by_cases hk1 : k = 1
    · subst hk1
      have h := hC1 q χ hχ hχ1
      simp only [pow_one, if_true]
      have h' : ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ)).re
          ≤ Real.log q / 2 + |C1| := h.trans (by linarith [le_abs_self C1])
      have := mul_le_mul_of_nonneg_left h' he1.le
      have h2 : 0 ≤ |e 1| * |Ck 1| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
      linarith
    · have hk2 : 2 ≤ k := by have := (Finset.mem_Icc.mp hk).1; omega
      have h := hCk k hk2 q χ hχ hχ1
      rw [if_neg hk1, zero_add]
      calc e k * ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ k).re
          ≤ |e k * ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ k).re| :=
            le_abs_self _
        _ = |e k| * |∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ k).re| :=
            abs_mul _ _
        _ ≤ |e k| * |Ck k| :=
            mul_le_mul_of_nonneg_left (h.trans (le_abs_self _)) (abs_nonneg _)
  have hite : ∑ k ∈ Finset.Icc 1 m, (if k = 1 then e 1 * (Real.log q / 2 + |C1|) else 0)
      ≤ e 1 * (Real.log q / 2 + |C1|) := by
    rw [Finset.sum_ite_eq' (Finset.Icc 1 m) 1 (fun _ => e 1 * (Real.log q / 2 + |C1|))]
    split_ifs
    · exact le_rfl
    · exact hA0
  have hG : ∑ k ∈ Finset.Icc 1 m, e k *
      ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ k).re
      ≤ e 1 / 2 * Real.log q + CG := by
    refine (Finset.sum_le_sum hk).trans ?_
    rw [Finset.sum_add_distrib, hCG]
    linarith
  have hxG := mul_le_mul_of_nonneg_left hG hx0.le
  have p1 : 0 ≤ CG * E := mul_nonneg hCG0 hE0
  have p2 : 0 ≤ x * CE := mul_nonneg hx0.le hCE0
  have hfin : x * (e 1 / 2 * Real.log q + (CE + CG)) + (CE + CG) * (Real.log q + 1)
      * (1 + Real.log x) ^ J + (CE + CG) * Real.sqrt x
      = x * (e 1 / 2 * Real.log q + CG) + x * CE + CE * E + CG * E := by
    rw [hE]; ring
  rw [hfin]
  linarith

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r13A_chi
