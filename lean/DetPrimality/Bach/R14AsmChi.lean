import Mathlib
import DetPrimality.Bach.R14AsmSum
import DetPrimality.Bach.R13AsmChi

/-!
# Round 14 assembly, part 2: the χ side (formal0760 §1.2, §4 Stage 1)

`r14A_chi` : from `R14ChiExplicit a`, `R14ZeroPow a` (`a = β − 1`) and the exact modulus `cert.modulus` at
`t = γ/β`. With `s″ = (ρ + ½ + a)/β = 1 + iγ/β` (GRH):
`∑_j θ_j β^j x^{ρ+½}/(ρ+½+a)^{j+1} = x^{ρ+½}·(1/β)·K(s″)`, `‖x^{ρ+½}‖ = x`, `‖K(s″)‖ ≤ G(γ/β)` and
`G(γ/β) = ∑_k e_k β^k Re (a + 3/2 − ρ)^{-k}`, so the zero sum is at most
`(x/β)·∑_k e_k β^k ∑_ρ Re (a+3/2−ρ)^{-k} ≤ x·((e₁/2) log q + C)`.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

variable {β p J m a : ℕ} {θ e b : ℕ → ℝ} {N₀ : ℝ}

/-- Geometry of a zero on the critical line in the scaled Perron variable `s″ = (ρ + 1/2 + a)/β`. -/
theorem r14A_zero_geom (hGRH : DirichletLZerosOnLine) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {ρ : ℂ} (h : zeroOrd χ ρ ≠ 0) {a : ℕ} {β : ℝ} (hβ : β = a + 1) :
    (ρ + 1 / 2 + (a : ℂ)) / (β : ℂ) = 1 + ((ρ.im / β : ℝ) : ℂ) * I ∧
      (a : ℂ) + 3 / 2 - ρ = (starRingEnd ℂ) (ρ + 1 / 2 + (a : ℂ)) ∧
      ‖ρ + 1 / 2‖ ≤ ‖ρ + 1 / 2 + (a : ℂ)‖ ∧ (ρ + 1 / 2 + (a : ℂ)).re = β ∧
      ρ + 1 / 2 + (a : ℂ) ≠ 0 := by
  obtain ⟨hw, hconj, -, -, -⟩ := r13A_zero_geom hGRH χ h
  have hβ0 : (0 : ℝ) < β := by rw [hβ]; positivity
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ0.ne'
  have hre : (ρ + 1 / 2 + (a : ℂ)).re = β := by
    rw [hw, hβ]; simp; ring
  have him : (ρ + 1 / 2 + (a : ℂ)).im = ρ.im := by simp
  have hre1 : (ρ + 1 / 2).re = 1 := by rw [hw]; simp
  have him1 : (ρ + 1 / 2).im = ρ.im := by simp
  refine ⟨?_, ?_, ?_, hre, ?_⟩
  · rw [div_eq_iff hβc, hw]
    push_cast
    have : (β : ℂ) = (a : ℂ) + 1 := by rw [hβ]; push_cast; ring
    field_simp
    rw [this]; ring
  · rw [map_add, Complex.conj_natCast, ← hconj]; ring
  · have ha2 : ‖ρ + 1 / 2‖ ^ 2 = 1 + ρ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre1, him1]; ring
    have hb2 : ‖ρ + 1 / 2 + (a : ℂ)‖ ^ 2 = β ^ 2 + ρ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; ring
    have hβ1 : 1 ≤ β := by rw [hβ]; linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by rw [ha2, hb2]; nlinarith)
  · intro h0
    rw [h0] at hre
    simp at hre
    exact hβ0.ne' hre.symm

theorem r14A_pow_ge (hGRH : DirichletLZerosOnLine) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {ρ : ℂ} (h : zeroOrd χ ρ ≠ 0) (a : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    (zeroOrd χ ρ : ℝ) / ‖ρ + 1 / 2 + (a : ℂ)‖ ^ k ≤ (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2 := by
  obtain ⟨-, -, h1, -, -⟩ := r13A_zero_geom hGRH χ h
  obtain ⟨-, -, h2, -, -⟩ := r14A_zero_geom hGRH χ h (a := a) (β := a + 1) rfl
  refine le_trans ?_ (r13A_pow_ge hGRH χ h hk)
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    (pow_le_pow_left₀ (norm_nonneg _) h2 k)

/-- Summability of the zero sum in `R14ChiExplicit` (order `j ≥ 1`). -/
theorem r14A_summable_T (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)
    (a : ℕ) {x : ℝ} (hx : 0 < x) {j : ℕ} (hj : 1 ≤ j) :
    Summable fun ρ : ℂ =>
      (zeroOrd χ ρ : ℂ) * (x : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2 + (a : ℂ)) ^ (j + 1) := by
  refine Summable.of_norm_bounded (hS.mul_left x) fun ρ => ?_
  by_cases h0 : zeroOrd χ ρ = 0
  · simp [h0]
  obtain ⟨hw, -, -, -, -⟩ := r13A_zero_geom hGRH χ h0
  have hre : (ρ + 1 / 2).re = 1 := by rw [hw]; simp
  rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, hre, Real.rpow_one]
  have := r14A_pow_ge hGRH χ h0 a (k := j + 1) (by omega)
  calc (zeroOrd χ ρ : ℝ) * x / ‖ρ + 1 / 2 + (a : ℂ)‖ ^ (j + 1)
      = x * ((zeroOrd χ ρ : ℝ) / ‖ρ + 1 / 2 + (a : ℂ)‖ ^ (j + 1)) := by ring
    _ ≤ x * ((zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) := mul_le_mul_of_nonneg_left this hx.le

/-- Summability of the zero sums in `R14ZeroPow` (order `k ≥ 1`). -/
theorem r14A_summable_re (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)
    (a : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ k).re := by
  refine Summable.of_norm_bounded (hS.mul_left ((a : ℝ) + 1)) fun ρ => ?_
  by_cases h0 : zeroOrd χ ρ = 0
  · simp [h0]
  obtain ⟨-, hconj, -, hre, hne⟩ := r14A_zero_geom hGRH χ h0 (a := a) (β := a + 1) rfl
  have hβ1 : (1 : ℝ) ≤ (a : ℝ) + 1 := by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
  have hm0 : (0 : ℝ) ≤ zeroOrd χ ρ := Nat.cast_nonneg _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hm0]
  have hmain : |((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ k).re|
      ≤ ((a : ℝ) + 1) * (1 / ‖ρ + 1 / 2 + (a : ℂ)‖ ^ (max k 2)) := by
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 1 := by omega
      have hz : ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ 1).re
          = ((a : ℝ) + 1) / ‖ρ + 1 / 2 + (a : ℂ)‖ ^ 2 := by
        rw [pow_one, one_div, Complex.inv_re, hconj, Complex.conj_re, hre, Complex.normSq_conj,
          Complex.normSq_eq_norm_sq]
      rw [hz, show max 1 2 = 2 from rfl, abs_of_nonneg (by positivity)]
      exact le_of_eq (by ring)
    · rw [max_eq_left hk2]
      have h1 : |((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ k).re| ≤ 1 / ‖ρ + 1 / 2 + (a : ℂ)‖ ^ k := by
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_div, norm_one, norm_pow, hconj, Complex.norm_conj]
      have h2 : 0 ≤ 1 / ‖ρ + 1 / 2 + (a : ℂ)‖ ^ k := by positivity
      nlinarith
  have hpow := r14A_pow_ge hGRH χ h0 a (k := max k 2) (le_max_right _ _)
  calc (zeroOrd χ ρ : ℝ) * |((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ k).re|
      ≤ (zeroOrd χ ρ : ℝ) * (((a : ℝ) + 1) * (1 / ‖ρ + 1 / 2 + (a : ℂ)‖ ^ (max k 2))) :=
        mul_le_mul_of_nonneg_left hmain hm0
    _ = ((a : ℝ) + 1) * ((zeroOrd χ ρ : ℝ) / ‖ρ + 1 / 2 + (a : ℂ)‖ ^ (max k 2)) := by ring
    _ ≤ ((a : ℝ) + 1) * ((zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hpow (by linarith)

/-- The zero sum through the exact modulus at `t = γ/β`. -/
theorem r14A_zero_sum_le (hGRH : DirichletLZerosOnLine) (hβ : β = a + 1)
    (cert : R14Cert β p J m θ e b N₀)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    {x : ℝ} (hx : 0 < x) :
    ‖∑' ρ : ℂ, ∑ j ∈ Finset.range (J + 1), ((θ j * (β : ℝ) ^ j : ℝ) : ℂ) *
        ((zeroOrd χ ρ : ℂ) * (x : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2 + (a : ℂ)) ^ (j + 1))‖
      ≤ x / β * ∑ k ∈ Finset.Icc 1 m, (e k * (β : ℝ) ^ k) *
        ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ k).re := by
  have hβR : (β : ℝ) = (a : ℝ) + 1 := by rw [hβ]; push_cast; ring
  have hβ0 : (0 : ℝ) < β := by rw [hβR]; positivity
  have hβc : ((β : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hβ0.ne'
  have hβn : (β : ℂ) ≠ 0 := by exact_mod_cast hβ0.ne'
  have hS := summable_zeroOrd_div_normSq_proof χ hχ hχ1 (growth_completedLFunction χ hχ1)
  have hSk : ∀ k ∈ Finset.Icc 1 m, Summable fun ρ : ℂ =>
      (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ k).re :=
    fun k hk => r14A_summable_re hGRH χ hS a (Finset.mem_Icc.mp hk).1
  have hterm : ∀ ρ : ℂ, ‖∑ j ∈ Finset.range (J + 1), ((θ j * (β : ℝ) ^ j : ℝ) : ℂ) *
        ((zeroOrd χ ρ : ℂ) * (x : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2 + (a : ℂ)) ^ (j + 1))‖
      ≤ x / β * ∑ k ∈ Finset.Icc 1 m, (e k * (β : ℝ) ^ k) *
        ((zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ k).re) := by
    intro ρ
    by_cases h0 : zeroOrd χ ρ = 0
    · simp [h0]
    obtain ⟨hw, -, -, -, -⟩ := r13A_zero_geom hGRH χ h0
    obtain ⟨hs, hconj, -, -, hne⟩ := r14A_zero_geom hGRH χ h0 hβR
    obtain ⟨s, hsdef⟩ : ∃ s : ℂ, s = (ρ + 1 / 2 + (a : ℂ)) / ((β : ℝ) : ℂ) := ⟨_, rfl⟩
    have hs0 : s ≠ 0 := by rw [hsdef]; exact div_ne_zero hne hβc
    have hws : ρ + 1 / 2 + (a : ℂ) = ((β : ℝ) : ℂ) * s := by
      rw [hsdef]; field_simp
    have e1 : ∑ j ∈ Finset.range (J + 1), ((θ j * (β : ℝ) ^ j : ℝ) : ℂ) *
        ((zeroOrd χ ρ : ℂ) * (x : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2 + (a : ℂ)) ^ (j + 1))
        = (zeroOrd χ ρ : ℂ) * (x : ℂ) ^ (ρ + 1 / 2) * ((1 / (β : ℝ) : ℝ) : ℂ) * r13K θ J s := by
      unfold r13K
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hws, mul_pow, pow_succ ((β : ℝ) : ℂ) j]
      have hsj : s ^ (j + 1) ≠ 0 := pow_ne_zero _ hs0
      push_cast
      field_simp
    have e2 : ∑ k ∈ Finset.Icc 1 m, (e k * (β : ℝ) ^ k) *
        ((zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ k).re)
        = (zeroOrd χ ρ : ℝ) * r13G e m (ρ.im / β) := by
      unfold r13G
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : ((1 : ℂ) / (1 + ((ρ.im / β : ℝ) : ℂ) * I) ^ k).re
          = (β : ℝ) ^ k * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ k).re := by
        have h1 : (1 : ℂ) / (1 + ((ρ.im / β : ℝ) : ℂ) * I) ^ k
            = (((β : ℝ) ^ k : ℝ) : ℂ) * ((1 : ℂ) / (ρ + 1 / 2 + (a : ℂ)) ^ k) := by
          rw [← hs, ← hsdef, hws, mul_pow]
          have hsk : s ^ k ≠ 0 := pow_ne_zero _ hs0
          push_cast
          field_simp
        rw [h1, Complex.re_ofReal_mul]
        congr 1
        calc ((1 : ℂ) / (ρ + 1 / 2 + (a : ℂ)) ^ k).re
            = ((starRingEnd ℂ) ((1 : ℂ) / (ρ + 1 / 2 + (a : ℂ)) ^ k)).re := (Complex.conj_re _).symm
          _ = ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ k).re := by
              rw [hconj, map_div₀, map_one, map_pow]
      rw [this]; ring
    have hre : (ρ + 1 / 2).re = 1 := by rw [hw]; simp
    have hmod := cert.modulus (ρ.im / β)
    rw [← hs, ← hsdef] at hmod
    have hinv : ‖((1 / (β : ℝ) : ℝ) : ℂ)‖ = 1 / β := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [e1, e2, norm_mul, norm_mul, norm_mul, Complex.norm_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hx, hre, Real.rpow_one, hinv]
    calc (zeroOrd χ ρ : ℝ) * x * (1 / β) * ‖r13K θ J s‖
        ≤ (zeroOrd χ ρ : ℝ) * x * (1 / β) * r13G e m (ρ.im / β) :=
          mul_le_mul_of_nonneg_left hmod
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hx.le) (by positivity))
      _ = x / β * ((zeroOrd χ ρ : ℝ) * r13G e m (ρ.im / β)) := by ring
  have hsumG : Summable fun ρ : ℂ => x / β * ∑ k ∈ Finset.Icc 1 m, (e k * (β : ℝ) ^ k) *
        ((zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ k).re) :=
    (summable_sum fun k hk => (hSk k hk).mul_left (e k * (β : ℝ) ^ k)).mul_left (x / β)
  have hsumN : Summable fun ρ : ℂ => ‖∑ j ∈ Finset.range (J + 1), ((θ j * (β : ℝ) ^ j : ℝ) : ℂ) *
        ((zeroOrd χ ρ : ℂ) * (x : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2 + (a : ℂ)) ^ (j + 1))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumG
  calc ‖∑' ρ : ℂ, ∑ j ∈ Finset.range (J + 1), ((θ j * (β : ℝ) ^ j : ℝ) : ℂ) *
        ((zeroOrd χ ρ : ℂ) * (x : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2 + (a : ℂ)) ^ (j + 1))‖
      ≤ ∑' ρ : ℂ, ‖∑ j ∈ Finset.range (J + 1), ((θ j * (β : ℝ) ^ j : ℝ) : ℂ) *
        ((zeroOrd χ ρ : ℂ) * (x : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2 + (a : ℂ)) ^ (j + 1))‖ :=
        norm_tsum_le_tsum_norm hsumN
    _ ≤ ∑' ρ : ℂ, x / β * ∑ k ∈ Finset.Icc 1 m, (e k * (β : ℝ) ^ k) *
        ((zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ k).re) :=
        hsumN.tsum_le_tsum hterm hsumG
    _ = x / β * ∑ k ∈ Finset.Icc 1 m, (e k * (β : ℝ) ^ k) *
        ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ k).re := by
        rw [tsum_mul_left, Summable.tsum_finsetSum
          (fun k hk => (hSk k hk).mul_left (e k * (β : ℝ) ^ k))]
        congr 1
        exact Finset.sum_congr rfl fun k _ => tsum_mul_left

/-- **χ side**: zero sum through the exact modulus. -/
theorem r14A_chi (hGRH : DirichletLZerosOnLine) (hC : R14ChiExplicit a) (hP : R14ZeroPow a)
    (hβ : β = a + 1) (cert : R14Cert β p J m θ e b N₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      χ ≠ 1 → ∀ x : ℝ, 1 ≤ x →
        ∑ j ∈ Finset.range (J + 1), θ j * (β : ℝ) ^ j / (j.factorial : ℝ) * (r14Phi χ a j x).re
          ≤ x * (e 1 / 2 * Real.log q + C) + C * (Real.log q + 1) * (1 + Real.log x) ^ J
            + C * Real.sqrt x := by
  have hβR : (β : ℝ) = (a : ℝ) + 1 := by rw [hβ]; push_cast; ring
  have hβ0 : (0 : ℝ) < β := by rw [hβR]; positivity
  choose! Cj hCj using hC hGRH
  obtain ⟨⟨C1, hC1⟩, hP2⟩ := hP hGRH
  choose! Ck hCk using hP2
  have he1 := cert.e1pos
  -- scaled coefficients
  obtain ⟨θ', hθ'⟩ : ∃ θ' : ℕ → ℝ, θ' = fun j => θ j * (β : ℝ) ^ j := ⟨_, rfl⟩
  have hθ'j : ∀ j, θ j * (β : ℝ) ^ j = θ' j := fun j => by rw [hθ']
  have hlow : ∀ j, j < 3 → θ' j = 0 := fun j hj => by rw [← hθ'j, cert.low j hj, zero_mul]
  obtain ⟨e', he'⟩ : ∃ e' : ℕ → ℝ, e' = fun k => e k * (β : ℝ) ^ k := ⟨_, rfl⟩
  have he'k : ∀ k, e k * (β : ℝ) ^ k = e' k := fun k => by rw [he']
  have he'1 : e' 1 = e 1 * β := by rw [← he'k, pow_one]
  have he'pos : 0 < e' 1 := by rw [he'1]; positivity
  obtain ⟨CE, hCE⟩ : ∃ CE : ℝ,
      CE = ∑ j ∈ Finset.range (J + 1), |θ' j| / (j.factorial : ℝ) * |Cj j| := ⟨_, rfl⟩
  obtain ⟨CG, hCG⟩ : ∃ CG : ℝ,
      CG = e' 1 * |C1| + ∑ k ∈ Finset.Icc 1 m, |e' k| * |Ck k| := ⟨_, rfl⟩
  have hCE0 : 0 ≤ CE := by
    rw [hCE]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (div_nonneg (abs_nonneg _) (by positivity))
      (abs_nonneg _)
  have hCG0 : 0 ≤ CG := by
    rw [hCG]
    exact add_nonneg (mul_nonneg he'pos.le (abs_nonneg _))
      (Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hCGβ0 : 0 ≤ CG / β := div_nonneg hCG0 hβ0.le
  refine ⟨CE + CG / β, add_nonneg hCE0 hCGβ0, ?_⟩
  intro q _ χ hχ hχ1 x hx
  have hx0 : 0 < x := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlq1 : 0 ≤ Real.log q + 1 := by linarith
  have hlx1 : 1 ≤ 1 + Real.log x := by linarith
  have hS := summable_zeroOrd_div_normSq_proof χ hχ hχ1 (growth_completedLFunction χ hχ1)
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℂ, ∀ j, T j = ∑' ρ : ℂ,
      (zeroOrd χ ρ : ℂ) * (x : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2 + (a : ℂ)) ^ (j + 1) :=
    ⟨fun j => _, fun j => rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ,
      E = (Real.log q + 1) * (1 + Real.log x) ^ J + Real.sqrt x := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by
    rw [hE]
    exact add_nonneg (mul_nonneg hlq1 (pow_nonneg (by linarith) _)) (Real.sqrt_nonneg _)
  simp only [hθ'j]
  -- each order
  have hj : ∀ j ∈ Finset.range (J + 1), θ' j / (j.factorial : ℝ) * (r14Phi χ a j x).re
      ≤ -(((θ' j : ℂ) * T j).re) + |θ' j| / (j.factorial : ℝ) * |Cj j| * E := by
    intro j hjm
    by_cases h3 : 3 ≤ j
    · have hb := hCj j h3 q χ hχ hχ1 x hx
      rw [← hT j] at hb
      have hfac : (0 : ℝ) < j.factorial := by positivity
      have e1 : (r14Phi χ a j x).re
          = (r14Phi χ a j x + (j.factorial : ℂ) * T j).re - (j.factorial : ℝ) * (T j).re := by
        rw [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
          sub_zero]
        ring
      have e2 : ((θ' j : ℂ) * T j).re = θ' j * (T j).re := Complex.re_ofReal_mul _ _
      have hre := Complex.abs_re_le_norm (r14Phi χ a j x + (j.factorial : ℂ) * T j)
      have hpow : (1 + Real.log x) ^ j ≤ (1 + Real.log x) ^ J :=
        pow_le_pow_right₀ hlx1 (by have := Finset.mem_range.mp hjm; omega)
      have hmono := mul_le_mul_of_nonneg_left hpow hlq1
      have hEj : 0 ≤ (Real.log q + 1) * (1 + Real.log x) ^ j + Real.sqrt x :=
        add_nonneg (mul_nonneg hlq1 (pow_nonneg (by linarith) _)) (Real.sqrt_nonneg _)
      have hE' : |(r14Phi χ a j x + (j.factorial : ℂ) * T j).re| ≤ |Cj j| * E := by
        refine hre.trans (hb.trans ?_)
        calc Cj j * (Real.log q + 1) * (1 + Real.log x) ^ j + Cj j * Real.sqrt x
            = Cj j * ((Real.log q + 1) * (1 + Real.log x) ^ j + Real.sqrt x) := by ring
          _ ≤ |Cj j| * ((Real.log q + 1) * (1 + Real.log x) ^ j + Real.sqrt x) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) hEj
          _ ≤ |Cj j| * E := by
              rw [hE]
              exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      have h4 : θ' j / (j.factorial : ℝ) * (r14Phi χ a j x + (j.factorial : ℂ) * T j).re
          ≤ |θ' j| / (j.factorial : ℝ) * |Cj j| * E := by
        calc θ' j / (j.factorial : ℝ) * (r14Phi χ a j x + (j.factorial : ℂ) * T j).re
            ≤ |θ' j / (j.factorial : ℝ) * (r14Phi χ a j x + (j.factorial : ℂ) * T j).re| :=
              le_abs_self _
          _ = |θ' j| / (j.factorial : ℝ) * |(r14Phi χ a j x + (j.factorial : ℂ) * T j).re| := by
              rw [abs_mul, abs_div, abs_of_pos hfac]
          _ ≤ |θ' j| / (j.factorial : ℝ) * (|Cj j| * E) :=
              mul_le_mul_of_nonneg_left hE' (div_nonneg (abs_nonneg _) hfac.le)
          _ = |θ' j| / (j.factorial : ℝ) * |Cj j| * E := by ring
      have h5 : θ' j / (j.factorial : ℝ) * ((j.factorial : ℝ) * (T j).re) = θ' j * (T j).re := by
        rw [← mul_assoc, div_mul_cancel₀ _ hfac.ne']
      rw [e1, e2, mul_sub, h5]
      linarith
    · have h0 : θ' j = 0 := hlow j (by omega)
      simp [h0]
  have hsum := Finset.sum_le_sum hj
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul, ← hCE] at hsum
  -- interchange
  have hZ : ∑ j ∈ Finset.range (J + 1), (θ' j : ℂ) * T j
      = ∑' ρ : ℂ, ∑ j ∈ Finset.range (J + 1), (θ' j : ℂ) *
        ((zeroOrd χ ρ : ℂ) * (x : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2 + (a : ℂ)) ^ (j + 1)) := by
    rw [Summable.tsum_finsetSum]
    · exact Finset.sum_congr rfl fun j _ => by rw [hT j, tsum_mul_left]
    · intro j _
      by_cases h3 : 3 ≤ j
      · exact (r14A_summable_T hGRH χ hS a hx0 (by omega)).mul_left _
      · have h0 : θ' j = 0 := hlow j (by omega)
        simp [h0, summable_zero]
  have hz1 := r14A_zero_sum_le hGRH hβ cert χ hχ hχ1 hx0
  simp only [hθ'j, he'k] at hz1
  rw [← hZ] at hz1
  have hz2 : -(∑ j ∈ Finset.range (J + 1), ((θ' j : ℂ) * T j).re)
      ≤ ‖∑ j ∈ Finset.range (J + 1), (θ' j : ℂ) * T j‖ := by
    rw [← Complex.re_sum]
    have := Complex.abs_re_le_norm (∑ j ∈ Finset.range (J + 1), (θ' j : ℂ) * T j)
    linarith [(abs_le.mp this).1]
  -- the `G` sum
  have hA0 : 0 ≤ e' 1 * (Real.log q / 2 + |C1|) :=
    mul_nonneg he'pos.le (add_nonneg (by linarith) (abs_nonneg _))
  have hk : ∀ k ∈ Finset.Icc 1 m,
      e' k * ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ k).re
        ≤ (if k = 1 then e' 1 * (Real.log q / 2 + |C1|) else 0) + |e' k| * |Ck k| := by
    intro k hk
    by_cases hk1 : k = 1
    · subst hk1
      have h := hC1 q χ hχ hχ1
      simp only [pow_one, if_true]
      have h' : ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ)).re
          ≤ Real.log q / 2 + |C1| := h.trans (by linarith [le_abs_self C1])
      have := mul_le_mul_of_nonneg_left h' he'pos.le
      have h2 : 0 ≤ |e' 1| * |Ck 1| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
      linarith
    · have hk2 : 2 ≤ k := by have := (Finset.mem_Icc.mp hk).1; omega
      have h := hCk k hk2 q χ hχ hχ1
      rw [if_neg hk1, zero_add]
      calc e' k * ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ k).re
          ≤ |e' k * ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ k).re| :=
            le_abs_self _
        _ = |e' k| * |∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ k).re| :=
            abs_mul _ _
        _ ≤ |e' k| * |Ck k| :=
            mul_le_mul_of_nonneg_left (h.trans (le_abs_self _)) (abs_nonneg _)
  have hite : ∑ k ∈ Finset.Icc 1 m, (if k = 1 then e' 1 * (Real.log q / 2 + |C1|) else 0)
      ≤ e' 1 * (Real.log q / 2 + |C1|) := by
    rw [Finset.sum_ite_eq' (Finset.Icc 1 m) 1 (fun _ => e' 1 * (Real.log q / 2 + |C1|))]
    split_ifs
    · exact le_rfl
    · exact hA0
  have hG : ∑ k ∈ Finset.Icc 1 m, e' k *
      ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ k).re
      ≤ e' 1 / 2 * Real.log q + CG := by
    refine (Finset.sum_le_sum hk).trans ?_
    rw [Finset.sum_add_distrib, hCG]
    linarith
  have hxG := mul_le_mul_of_nonneg_left hG (div_nonneg hx0.le hβ0.le)
  have hxG' : x / β * (e' 1 / 2 * Real.log q + CG) = x * (e 1 / 2 * Real.log q + CG / β) := by
    rw [he'1]; field_simp
  rw [hxG'] at hxG
  have p1 : 0 ≤ CG / β * E := mul_nonneg hCGβ0 hE0
  have p2 : 0 ≤ x * CE := mul_nonneg hx0.le hCE0
  have hfin : x * (e 1 / 2 * Real.log q + (CE + CG / β)) + (CE + CG / β) * (Real.log q + 1)
      * (1 + Real.log x) ^ J + (CE + CG / β) * Real.sqrt x
      = x * (e 1 / 2 * Real.log q + CG / β) + x * CE + CE * E + CG / β * E := by
    rw [hE]; ring
  rw [hfin]
  linarith

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r14A_chi
