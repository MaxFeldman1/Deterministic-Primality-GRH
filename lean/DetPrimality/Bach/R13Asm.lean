import Mathlib
import DetPrimality.Bach.R13AsmSum
import DetPrimality.Bach.R13AsmChi
import DetPrimality.Bach.LLSElem

/-!
# Round 13 assembly, part 3: the asymptotic theorem (formal076 §1, §4.3)

`r13A_eventually` : under GRH and P1–P3, a certificate `R13Cert J m θ e ℓ L₁ N₀` gives
`R11Bound c n` for all large `n`, for every `c > e^{-ℓ} (e₁/(2N₀))²`.

With `t = log n`, `X = c t²`, `x = e^ℓ X = (bt)²` (`b = √(e^ℓ c)`), the three inequalities
`r13A_zeta`, `r13A_sum_ge`, `r13A_chi` give
`b²(N₀ b − e₁/2) t³ ≤ C (bt)² √(bt) + C (bt)² + C (t+1)(1 + log x)^J + C bt`,
which fails for large `t` (`r13A_ev_aux`).
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

variable {J m : ℕ} {θ e : ℕ → ℝ} {ℓ L₁ N₀ : ℝ}

theorem r13A_rpow32 {x : ℝ} (hx : 0 < x) : x ^ ((3 : ℝ) / 2) = x * √x := by
  rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hx,
    Real.rpow_one]

theorem r13A_rpow54 {x : ℝ} (hx : 0 < x) : x ^ ((5 : ℝ) / 4) = x * √(√x) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
  have : x * x ^ ((1 : ℝ) / 2 * (1 / 2)) = x ^ (1 + (1 : ℝ) / 2 * (1 / 2)) := by
    rw [Real.rpow_add hx, Real.rpow_one]
  rw [this]
  norm_num

/-- The lower-order terms are eventually smaller than `δ t³`. -/
theorem r13A_ev_aux (J : ℕ) {a b Cz Cc δ c : ℝ} (ha : 0 < a) (hb : 0 < b) (_hCz : 0 ≤ Cz)
    (hCc : 0 ≤ Cc) (hδ : 0 < δ) (hc : 0 < c) :
    ∀ᶠ t : ℝ in Filter.atTop, 1 ≤ t ∧ 1 ≤ c * t ^ 2 ∧
      Cz * ((b * t) ^ 2 * √(b * t)) + Cc * (b * t) ^ 2
        + Cc * (t + 1) * (1 + Real.log (a * t ^ 2)) ^ J + Cc * (b * t) < δ * t ^ 3 := by
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp 1 * a := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; positivity
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = δ / (10 * (Cc + 1) * E) := ⟨_, rfl⟩
  have hC1 : 0 < Cc + 1 := by linarith
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεE : ε * ((Cc + 1) * E) = δ / 10 := by rw [hε]; field_simp
  have hlog := (Real.isLittleO_pow_log_id_atTop (n := J)).def hε0
  have htend : Filter.Tendsto (fun t : ℝ => E * t ^ 2) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop two_ne_zero).const_mul_atTop hE0
  have h3 := htend.eventually hlog
  filter_upwards [h3, Filter.eventually_ge_atTop 1, Filter.eventually_ge_atTop (1 / c),
    Filter.eventually_ge_atTop (25 * (Cz * b ^ 2) ^ 2 * b / δ ^ 2),
    Filter.eventually_ge_atTop (5 * Cc * b ^ 2 / δ), Filter.eventually_ge_atTop (5 * Cc * b / δ)]
    with t h3 h1 hc1 hT1 hT2 hT3
  have ht0 : 0 < t := by linarith
  refine ⟨h1, ?_, ?_⟩
  · rw [div_le_iff₀ hc] at hc1
    nlinarith
  -- the logarithmic term
  have hy : Real.log (E * t ^ 2) = 1 + Real.log (a * t ^ 2) := by
    rw [hE, mul_assoc, Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
  have hEt : 0 < E * t ^ 2 := by positivity
  have h3' : (1 + Real.log (a * t ^ 2)) ^ J ≤ ε * (E * t ^ 2) := by
    rw [← hy]
    have h3'' : |Real.log (E * t ^ 2) ^ J| ≤ ε * |E * t ^ 2| := h3
    rw [abs_of_pos hEt] at h3''
    exact (le_abs_self _).trans h3''
  have k1 : 0 ≤ ε * E := by positivity
  have k2 : Cc * (ε * E) ≤ δ / 10 := by linarith
  have k3 : (t + 1) * t ^ 2 ≤ 2 * t ^ 3 := by nlinarith [sq_nonneg t]
  have hiii : Cc * (t + 1) * (1 + Real.log (a * t ^ 2)) ^ J ≤ δ / 5 * t ^ 3 := by
    calc Cc * (t + 1) * (1 + Real.log (a * t ^ 2)) ^ J
        ≤ Cc * (t + 1) * (ε * (E * t ^ 2)) :=
          mul_le_mul_of_nonneg_left h3' (by positivity)
      _ = Cc * (ε * E) * ((t + 1) * t ^ 2) := by ring
      _ ≤ δ / 10 * (2 * t ^ 3) := mul_le_mul k2 k3 (by positivity) (by positivity)
      _ = δ / 5 * t ^ 3 := by ring
  -- the `x^{5/4}` term
  have hr : Cz * b ^ 2 * √(b * t) ≤ δ / 5 * t := by
    by_contra hcon
    rw [not_le] at hcon
    have hsq := pow_lt_pow_left₀ hcon (by positivity) two_ne_zero
    rw [mul_pow (Cz * b ^ 2), Real.sq_sqrt (by positivity)] at hsq
    rw [div_le_iff₀ (by positivity)] at hT1
    have := mul_le_mul_of_nonneg_right hT1 ht0.le
    nlinarith
  have hi : Cz * ((b * t) ^ 2 * √(b * t)) ≤ δ / 5 * t ^ 3 := by
    calc Cz * ((b * t) ^ 2 * √(b * t)) = Cz * b ^ 2 * √(b * t) * t ^ 2 := by ring
      _ ≤ δ / 5 * t * t ^ 2 := mul_le_mul_of_nonneg_right hr (by positivity)
      _ = δ / 5 * t ^ 3 := by ring
  rw [div_le_iff₀ hδ] at hT2 hT3
  have hii : Cc * (b * t) ^ 2 ≤ δ / 5 * t ^ 3 := by
    have := mul_le_mul_of_nonneg_right hT2 (sq_nonneg t)
    nlinarith
  have hiv : Cc * (b * t) ≤ δ / 5 * t ^ 3 := by
    have a1 := mul_le_mul_of_nonneg_right hT3 ht0.le
    have a2 : t ^ 2 ≤ t ^ 3 := by nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr h1)]
    have a3 := mul_le_mul_of_nonneg_left a2 hδ.le
    nlinarith
  have hpos : 0 < δ * t ^ 3 := by positivity
  linarith

/-- **Main theorem of Round 13**: a certificate gives the asymptotic constant
`c* = e^{-ℓ} (e₁/(2N₀))²`. -/
theorem r13A_eventually (hGRH : DirichletLZerosOnLine) (hZ : R13ZetaSmooth)
    (hC : R13ChiExplicit) (hP : R13ZeroPow) (cert : R13Cert J m θ e ℓ L₁ N₀) :
    ∀ c : ℝ, Real.exp (-ℓ) * (e 1 / (2 * N₀)) ^ 2 < c →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → R11Bound c n := by
  intro c hc
  obtain ⟨hL0, hL1⟩ := cert.range
  obtain ⟨hN0, -⟩ := cert.num
  have he1 := cert.e1pos
  have hc0 : 0 < c := lt_of_le_of_lt (by positivity) hc
  obtain ⟨Cz, hCz0, hCz⟩ := r13A_zeta hGRH hZ cert
  obtain ⟨Cc, hCc0, hCc⟩ := r13A_chi hGRH hC hP cert
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = Real.exp ℓ * c := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = √a := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hb]; exact Real.sqrt_pos.mpr ha0
  have hbb : b ^ 2 = a := by rw [hb]; exact Real.sq_sqrt ha0.le
  have h2N : 0 < 2 * N₀ := by linarith
  have hub : e 1 / (2 * N₀) < b := by
    rw [hb]
    apply (Real.lt_sqrt (div_pos he1 h2N).le).mpr
    have h := mul_lt_mul_of_pos_left hc (Real.exp_pos ℓ)
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h
    rw [ha]; exact h
  have hδ : 0 < b ^ 2 * (N₀ * b - e 1 / 2) := by
    have h2 : e 1 < b * (2 * N₀) := by
      calc e 1 = e 1 / (2 * N₀) * (2 * N₀) := (div_mul_cancel₀ _ h2N.ne').symm
        _ < b * (2 * N₀) := mul_lt_mul_of_pos_right hub h2N
    have : 0 < N₀ * b - e 1 / 2 := by linarith
    exact mul_pos (by positivity) this
  have hev := r13A_ev_aux J ha0 hb0 hCz0 hCc0 hδ hc0
  have hnat := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually hev
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hnat
  refine ⟨max N 3, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn3 : 2 < n := by
    have := le_trans (le_max_right N 3) hn
    omega
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Real.log n := ⟨_, rfl⟩
  have hPt : 1 ≤ t ∧ 1 ≤ c * t ^ 2 ∧
      Cz * ((b * t) ^ 2 * √(b * t)) + Cc * (b * t) ^ 2
        + Cc * (t + 1) * (1 + Real.log (a * t ^ 2)) ^ J + Cc * (b * t)
        < b ^ 2 * (N₀ * b - e 1 / 2) * t ^ 3 := by
    rw [ht]; exact hN n hnN
  obtain ⟨ht1, hX1, hlt⟩ := hPt
  unfold R11Bound
  intro χ hχ
  by_contra hno
  have hh : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < c * t ^ 2 → χ (a : ZMod n) = 1 := by
    intro a ha1 ha2
    by_contra hne
    exact hno ⟨a, ha1, by rw [← ht]; exact ha2, hne⟩
  obtain ⟨-, hprim, hne, hq0, -, hlq0, hlq, hχ1, -⟩ := llsElem_no_witness_facts hn3 χ hχ hh
  have : NeZero χ.conductor := ⟨hq0⟩
  rw [← ht] at hlq
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = c * t ^ 2 := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.exp ℓ * X := ⟨_, rfl⟩
  rw [← hX] at hχ1 hX1
  have hbt : 0 < b * t := mul_pos hb0 (by linarith)
  have hxa : x = (b * t) ^ 2 := by rw [hx, hX, mul_pow, hbb, ha]; ring
  have hx1 : 1 ≤ x := by
    rw [hx]
    have := Real.one_le_exp (by linarith : 0 ≤ ℓ)
    nlinarith
  have hx0 : 0 < x := by linarith
  have hsqrt : √x = b * t := by rw [hxa]; exact Real.sqrt_sq hbt.le
  have h32 : x ^ ((3 : ℝ) / 2) = (b * t) ^ 2 * (b * t) := by
    rw [r13A_rpow32 hx0, hsqrt, hxa]
  have h54 : x ^ ((5 : ℝ) / 4) = (b * t) ^ 2 * √(b * t) := by
    rw [r13A_rpow54 hx0, hsqrt, hxa]
  have hlogx : Real.log x = Real.log (a * t ^ 2) := by rw [hx, hX, ha, mul_assoc]
  have s1 := r13A_sum_ge χ.primitiveCharacter cert hx hχ1
  have s2 := hCz X hX1 x hx
  have s3 := hCc χ.conductor χ.primitiveCharacter hprim hne x hx1
  rw [h32, h54] at s2
  rw [hlogx, hsqrt] at s3
  obtain ⟨lq, hlqdef⟩ : ∃ lq : ℝ, lq = Real.log χ.conductor := ⟨_, rfl⟩
  rw [← hlqdef] at s3 hlq hlq0
  have hLJ : 0 ≤ (1 + Real.log (a * t ^ 2)) ^ J :=
    pow_nonneg (by rw [← hlogx]; linarith [Real.log_nonneg hx1]) _
  have b1 : x * (e 1 / 2 * lq + Cc) ≤ (b * t) ^ 2 * (e 1 / 2 * t + Cc) := by
    rw [hxa]
    have := mul_le_mul_of_nonneg_left hlq (half_pos he1).le
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have b2 : Cc * (lq + 1) * (1 + Real.log (a * t ^ 2)) ^ J
      ≤ Cc * (t + 1) * (1 + Real.log (a * t ^ 2)) ^ J :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hCc0) hLJ
  have e3 : b ^ 2 * (N₀ * b - e 1 / 2) * t ^ 3
      = N₀ * ((b * t) ^ 2 * (b * t)) - (b * t) ^ 2 * (e 1 / 2 * t) := by ring
  have e4 : (b * t) ^ 2 * (e 1 / 2 * t + Cc)
      = (b * t) ^ 2 * (e 1 / 2 * t) + Cc * (b * t) ^ 2 := by ring
  linarith

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r13A_eventually
