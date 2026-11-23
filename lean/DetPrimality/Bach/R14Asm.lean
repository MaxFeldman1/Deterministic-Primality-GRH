import Mathlib
import DetPrimality.Bach.R14AsmSum
import DetPrimality.Bach.R14AsmChi
import DetPrimality.Bach.R13Asm
import DetPrimality.Bach.LLSElem

/-!
# Round 14 assembly, part 3: the asymptotic theorem (formal0760 §1, §1.2, §4 Stage 1)

`r14A_eventually` : under GRH and the three analytic inputs with shift `a = β − 1`, a certificate
`R14Cert β p J m θ e b N₀` gives `R11Bound c n` for all large `n`, for every
`c > c* = e^{-b(p+1)/β} · (β e₁/(2N₀))²`.

Normalisation (re-derived; scaled variables `L″ = β log(x/n)`, `ℓ = b(p+1)/β`, `x = e^ℓ X`):
* ζ side (`r14A_zeta`): signed sum `≥ (N₀/β) x^{3/2} − C x^{5/4}`;
* χ side (`r14A_chi`): signed sum `≤ x ((e₁/2) log q + C) + …` (the `1/β` of the kernel cancels the `β` of
  `e₁ β · Re(β+½−ρ)^{-1}`);
so `√x ≤ (β e₁/(2N₀)) log n + o(log n)`, i.e. `c ≤ e^{-ℓ} (β e₁/(2N₀))²`. This is the argument of
`r13A_eventually` with `N₀/β` in place of `N₀` and `b(p+1)/β` in place of `ℓ`; `r13A_ev_aux` is reused as is.
In the unscaled variables of `formal0760_certificate.py` the same number is `e^{-ℓ}(Î/N̂)²`
(checked numerically by `research/barrier/r14Cert_gen/data.py`).
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

variable {β p J m : ℕ} {θ e b : ℕ → ℝ} {N₀ : ℝ}

/-- **Main theorem of Round 14**: a certificate gives the asymptotic constant
`c* = e^{-b(p+1)/β} (β e₁/(2N₀))²`; the weight of `n < x` is `√n (n/x)^{β-1} W(β log(x/n))`. -/
theorem r14A_eventually (hGRH : DirichletLZerosOnLine) (hZ : R14ZetaSmooth (β - 1))
    (hC : R14ChiExplicit (β - 1)) (hP : R14ZeroPow (β - 1)) (cert : R14Cert β p J m θ e b N₀) :
    ∀ c : ℝ, Real.exp (-(b (p + 1) / β)) * (β * e 1 / (2 * N₀)) ^ 2 < c →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → R11Bound c n := by
  intro c hc
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = β - 1 := ⟨_, rfl⟩
  have hβ : β = a + 1 := by have := cert.beta; omega
  rw [← ha] at hZ hC hP
  have hβ0 : (0 : ℝ) < β := by exact_mod_cast cert.beta
  obtain ⟨hN0, -⟩ := cert.num
  have he1 := cert.e1pos
  -- reduction to the Round 13 shape
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = b (p + 1) / β := ⟨_, rfl⟩
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℝ, N₁ = N₀ / β := ⟨_, rfl⟩
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; exact div_nonneg (r14A_b_nonneg cert le_rfl) hβ0.le
  have hN₁0 : 0 < N₁ := by rw [hN₁]; positivity
  have hcN : β * e 1 / (2 * N₀) = e 1 / (2 * N₁) := by
    rw [hN₁]; field_simp
  rw [← hℓ, hcN] at hc
  have hc0 : 0 < c := lt_of_le_of_lt (by positivity) hc
  obtain ⟨Cz, hCz0, hCz⟩ := r14A_zeta hGRH hZ hβ cert
  obtain ⟨Cc, hCc0, hCc⟩ := r14A_chi hGRH hC hP hβ cert
  rw [← hN₁] at hCz
  simp only [← hℓ] at hCz
  obtain ⟨a', ha'⟩ : ∃ a' : ℝ, a' = Real.exp ℓ * c := ⟨_, rfl⟩
  have ha0 : 0 < a' := by rw [ha']; positivity
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = √a' := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; exact Real.sqrt_pos.mpr ha0
  have hdd : d ^ 2 = a' := by rw [hd]; exact Real.sq_sqrt ha0.le
  have h2N : 0 < 2 * N₁ := by linarith
  have hub : e 1 / (2 * N₁) < d := by
    rw [hd]
    apply (Real.lt_sqrt (div_pos he1 h2N).le).mpr
    have h := mul_lt_mul_of_pos_left hc (Real.exp_pos ℓ)
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h
    rw [ha']; exact h
  have hδ : 0 < d ^ 2 * (N₁ * d - e 1 / 2) := by
    have h2 : e 1 < d * (2 * N₁) := by
      calc e 1 = e 1 / (2 * N₁) * (2 * N₁) := (div_mul_cancel₀ _ h2N.ne').symm
        _ < d * (2 * N₁) := mul_lt_mul_of_pos_right hub h2N
    have : 0 < N₁ * d - e 1 / 2 := by linarith
    exact mul_pos (by positivity) this
  have hev := r13A_ev_aux J ha0 hd0 hCz0 hCc0 hδ hc0
  have hnat := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually hev
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hnat
  refine ⟨max N 3, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn3 : 2 < n := by
    have := le_trans (le_max_right N 3) hn
    omega
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Real.log n := ⟨_, rfl⟩
  have hPt : 1 ≤ t ∧ 1 ≤ c * t ^ 2 ∧
      Cz * ((d * t) ^ 2 * √(d * t)) + Cc * (d * t) ^ 2
        + Cc * (t + 1) * (1 + Real.log (a' * t ^ 2)) ^ J + Cc * (d * t)
        < d ^ 2 * (N₁ * d - e 1 / 2) * t ^ 3 := by
    rw [ht]; exact hN n hnN
  obtain ⟨ht1, hX1, hlt⟩ := hPt
  unfold R11Bound
  intro χ hχ
  by_contra hno
  have hh : ∀ k : ℕ, 1 ≤ k → (k : ℝ) < c * t ^ 2 → χ (k : ZMod n) = 1 := by
    intro k hk1 hk2
    by_contra hne
    exact hno ⟨k, hk1, by rw [← ht]; exact hk2, hne⟩
  obtain ⟨-, hprim, hne, hq0, -, hlq0, hlq, hχ1, -⟩ := llsElem_no_witness_facts hn3 χ hχ hh
  have : NeZero χ.conductor := ⟨hq0⟩
  rw [← ht] at hlq
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = c * t ^ 2 := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.exp ℓ * X := ⟨_, rfl⟩
  rw [← hX] at hχ1 hX1
  have hdt : 0 < d * t := mul_pos hd0 (by linarith)
  have hxa : x = (d * t) ^ 2 := by rw [hx, hX, mul_pow, hdd, ha']; ring
  have hx1 : 1 ≤ x := by
    rw [hx]
    have := Real.one_le_exp hℓ0
    nlinarith
  have hx0 : 0 < x := by linarith
  have hsqrt : √x = d * t := by rw [hxa]; exact Real.sqrt_sq hdt.le
  have h32 : x ^ ((3 : ℝ) / 2) = (d * t) ^ 2 * (d * t) := by
    rw [r13A_rpow32 hx0, hsqrt, hxa]
  have h54 : x ^ ((5 : ℝ) / 4) = (d * t) ^ 2 * √(d * t) := by
    rw [r13A_rpow54 hx0, hsqrt, hxa]
  have hlogx : Real.log x = Real.log (a' * t ^ 2) := by rw [hx, hX, ha', mul_assoc]
  have hxb : x = Real.exp (b (p + 1) / β) * X := by rw [hx, hℓ]
  have s1 := r14A_sum_ge (a := a) χ.primitiveCharacter cert (by linarith : (0 : ℝ) < X) hxb hχ1
  have s2 := hCz X hX1 x hx
  have s3 := hCc χ.conductor χ.primitiveCharacter hprim hne x hx1
  rw [h32, h54] at s2
  rw [hlogx, hsqrt] at s3
  obtain ⟨lq, hlqdef⟩ : ∃ lq : ℝ, lq = Real.log χ.conductor := ⟨_, rfl⟩
  rw [← hlqdef] at s3 hlq hlq0
  have hLJ : 0 ≤ (1 + Real.log (a' * t ^ 2)) ^ J :=
    pow_nonneg (by rw [← hlogx]; linarith [Real.log_nonneg hx1]) _
  have b1 : x * (e 1 / 2 * lq + Cc) ≤ (d * t) ^ 2 * (e 1 / 2 * t + Cc) := by
    rw [hxa]
    have := mul_le_mul_of_nonneg_left hlq (half_pos he1).le
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have b2 : Cc * (lq + 1) * (1 + Real.log (a' * t ^ 2)) ^ J
      ≤ Cc * (t + 1) * (1 + Real.log (a' * t ^ 2)) ^ J :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hCc0) hLJ
  have e3 : d ^ 2 * (N₁ * d - e 1 / 2) * t ^ 3
      = N₁ * ((d * t) ^ 2 * (d * t)) - (d * t) ^ 2 * (e 1 / 2 * t) := by ring
  have e4 : (d * t) ^ 2 * (e 1 / 2 * t + Cc)
      = (d * t) ^ 2 * (e 1 / 2 * t) + Cc * (d * t) ^ 2 := by ring
  linarith

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r14A_eventually
