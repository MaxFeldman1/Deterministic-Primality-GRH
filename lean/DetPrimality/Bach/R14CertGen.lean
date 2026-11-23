import Mathlib
import DetPrimality.Bach.R13CertGen
import DetPrimality.Bach.R14AsmSum

/-!
# Round 14 certificate, generic part (formal0760 §1.1 Lemma E′, §3)

* `r14Cert_modulus_of_sum` (**Lemma E′**): if `s^{J+1} K(s) = Q(s) P(s)²` with `P` a real polynomial,
  `Q(s) = ∑_{a ≤ p} ζ_a (−(s−1)²)^a`, `ζ_a ≥ 0`, `J + 1 = 2m`, and
  `Q(s) P(s) P(2−s) = ∑_{k=1}^m (e_k/2) (s^{m−k}(2−s)^m + s^m(2−s)^{m−k})`,
  then `‖K(1+it)‖ ≤ G(t)` (in fact `=`). Proof of `r13Cert_modulus_of_factor` with `A − B(s−1)²` replaced by `Q`.
* `r14Cert_tau` : `R_κ(L) = ∑_i L^i/i! · τ_i` with `τ_i = (1/κ)(θ_i + τ_{i+1})`, `τ_{J+1} = 0`.
* `r14Cert_num_p1`, `r14Cert_num_p2` : the signed combination of `R14Cert.num` written out for `p = 1, 2`.
-/

open Complex

namespace DetPrimality.Bach

/-- **Lemma E′** (formal0760 §1.1): exact modulus on the line `Re s = 1` for
`K = Q·H₀²`, `Q = ∑_{a ≤ p} ζ_a (−(s−1)²)^a`, `ζ_a ≥ 0`. -/
theorem r14Cert_modulus_of_sum {J m d p : ℕ} {θ e h ζ : ℕ → ℝ} (hζ : ∀ a, 0 ≤ ζ a)
    (hJ : J + 1 = 2 * m)
    (h1 : ∀ s : ℂ, ∑ j ∈ Finset.range (J + 1), (θ j : ℂ) * s ^ (J - j)
      = (∑ a ∈ Finset.range (p + 1), (ζ a : ℂ) * (-(s - 1) ^ 2) ^ a) * (∑ i ∈ Finset.range d, (h i : ℂ) * s ^ i) ^ 2)
    (h2 : ∀ s : ℂ, (∑ a ∈ Finset.range (p + 1), (ζ a : ℂ) * (-(s - 1) ^ 2) ^ a) *
        ((∑ i ∈ Finset.range d, (h i : ℂ) * s ^ i)
          * (∑ i ∈ Finset.range d, (h i : ℂ) * (2 - s) ^ i))
      = ∑ k ∈ Finset.range m, (e (k + 1) : ℂ) / 2 *
        (s ^ (m - (k + 1)) * (2 - s) ^ m + s ^ m * (2 - s) ^ (m - (k + 1)))) :
    ∀ t : ℝ, ‖r13K θ J (1 + (t : ℂ) * I)‖ ≤ r13G e m t := by
  intro t
  have hG : r13G e m t = ∑ k ∈ Finset.Icc 1 m,
      e k * ((1 : ℂ) / (1 + (t : ℂ) * I) ^ k).re := rfl
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = 1 + (t : ℂ) * I := ⟨_, rfl⟩
  rw [hG, ← hs]
  have hsre : s.re = 1 := by rw [hs]; simp
  have hsim : s.im = t := by rw [hs]; simp
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre
  have hconj : (starRingEnd ℂ) s = 2 - s := by
    apply Complex.ext
    · rw [Complex.conj_re, Complex.sub_re, hsre]; norm_num
    · rw [Complex.conj_im, Complex.sub_im, hsim]; simp
  have hc0 : (2 : ℂ) - s ≠ 0 := by rw [← hconj]; exact (map_ne_zero _).mpr hs0
  have hN0 : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hsc : s * (2 - s) = ((‖s‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ a ∈ Finset.range (p + 1), ζ a * (t ^ 2) ^ a := ⟨_, rfl⟩
  have hfac : (∑ a ∈ Finset.range (p + 1), (ζ a : ℂ) * (-(s - 1) ^ 2) ^ a) = ((A + 0 * t ^ 2 : ℝ) : ℂ) := by
    have h1 : s - 1 = (t : ℂ) * I := by rw [hs]; ring
    have h2 : -(s - 1) ^ 2 = ((t ^ 2 : ℝ) : ℂ) := by
      rw [h1, mul_pow, Complex.I_sq]; push_cast; ring
    rw [h2, hAdef]
    push_cast
    ring
  have hAB : 0 ≤ A + 0 * t ^ 2 := by
    rw [hAdef, zero_mul, add_zero]
    exact Finset.sum_nonneg fun a _ => mul_nonneg (hζ a) (by positivity)
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, ∀ z, P z = ∑ i ∈ Finset.range d, (h i : ℂ) * z ^ i :=
    ⟨fun z => _, fun z => rfl⟩
  have hPconj : (starRingEnd ℂ) (P s) = P (2 - s) := by
    rw [hP, hP, ← hconj, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, map_pow, Complex.conj_ofReal]
  have hPP : P s * P (2 - s) = ((‖P s‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hPconj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hK : r13K θ J s * s ^ (J + 1) = ∑ j ∈ Finset.range (J + 1), (θ j : ℂ) * s ^ (J - j) := by
    unfold r13K
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have : s ^ (J + 1) = s ^ (J - j) * s ^ (j + 1) := by rw [← pow_add]; congr 1; omega
    rw [this]
    field_simp
  have h1s : r13K θ J s * s ^ (J + 1) = ((A + 0 * t ^ 2 : ℝ) : ℂ) * P s ^ 2 := by
    rw [hK, h1 s, hfac, hP]
  have hnorm : ‖r13K θ J s‖ * (‖s‖ ^ 2) ^ m = (A + 0 * t ^ 2) * ‖P s‖ ^ 2 := by
    have := congrArg norm h1s
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hAB, hJ, pow_mul] at this
    exact this
  have hk : ∀ k ∈ Finset.range m, (e (k + 1) : ℂ) / 2 *
        (s ^ (m - (k + 1)) * (2 - s) ^ m + s ^ m * (2 - s) ^ (m - (k + 1)))
      = (((‖s‖ ^ 2) ^ m * (e (k + 1) * ((1 : ℂ) / s ^ (k + 1)).re) : ℝ) : ℂ) := by
    intro k hk
    have hkm : k + 1 ≤ m := Finset.mem_range.mp hk
    rw [r13Cert_pow_sub hs0 hkm, r13Cert_pow_sub hc0 hkm]
    have hv : (1 / (2 - s)) ^ (k + 1) = (starRingEnd ℂ) ((1 / s) ^ (k + 1)) := by
      rw [← hconj, map_pow, map_div₀, map_one]
    have hadd : (1 / s) ^ (k + 1) + (starRingEnd ℂ) ((1 / s) ^ (k + 1))
        = ((2 * ((1 / s) ^ (k + 1)).re : ℝ) : ℂ) := Complex.add_conj _
    have e1 : s ^ m * (1 / s) ^ (k + 1) * (2 - s) ^ m
        + s ^ m * ((2 - s) ^ m * (1 / (2 - s)) ^ (k + 1))
        = (s * (2 - s)) ^ m * ((1 / s) ^ (k + 1) + (1 / (2 - s)) ^ (k + 1)) := by
      rw [mul_pow]; ring
    rw [e1, hsc, hv, hadd, one_div_pow]
    push_cast
    ring
  have h2s : ((A + 0 * t ^ 2 : ℝ) : ℂ) * ((‖P s‖ ^ 2 : ℝ) : ℂ)
      = ∑ k ∈ Finset.range m,
        (((‖s‖ ^ 2) ^ m * (e (k + 1) * ((1 : ℂ) / s ^ (k + 1)).re) : ℝ) : ℂ) := by
    rw [← hfac, ← hPP, hP, hP, h2 s]
    exact Finset.sum_congr rfl hk
  have hreal : (A + 0 * t ^ 2) * ‖P s‖ ^ 2
      = (‖s‖ ^ 2) ^ m * ∑ k ∈ Finset.Icc 1 m, e k * ((1 : ℂ) / s ^ k).re := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul, h2s, ← Complex.ofReal_sum,
      r13Cert_sum_Icc (fun k => e k * ((1 : ℂ) / s ^ k).re) m, Finset.mul_sum]
  have hNm : 0 < (‖s‖ ^ 2) ^ m := by positivity
  have hfin : ‖r13K θ J s‖ * (‖s‖ ^ 2) ^ m
      = (∑ k ∈ Finset.Icc 1 m, e k * ((1 : ℂ) / s ^ k).re) * (‖s‖ ^ 2) ^ m := by
    rw [hnorm, hreal]; ring
  exact le_of_eq (mul_right_cancel₀ hNm.ne' hfin)

/-- Horner-type evaluation of `r14A_R`: with `τ_i = ∑_{j ≥ i} θ_j (1/κ)^{j+1−i}` given by the
recurrence `τ_i = (1/κ)(θ_i + τ_{i+1})`, `R(L) = ∑_{i ≤ J} L^i/i! · τ_i`. -/
theorem r14Cert_tau {J : ℕ} {θ τ : ℕ → ℝ} {κ : ℝ} (hτ : ∀ i, i ≤ J → τ i = 1 / κ * (θ i + τ (i + 1)))
    (hτJ : τ (J + 1) = 0) (L : ℝ) :
    r14A_R κ θ J L = ∑ i ∈ Finset.range (J + 1), L ^ i / (i.factorial : ℝ) * τ i := by
  -- `τ i = ∑_{j ∈ range (J+1), i ≤ j} θ_j (1/κ)^{j+1-i}` by downward induction
  have key : ∀ n, n ≤ J + 1 → τ (J + 1 - n)
      = ∑ j ∈ Finset.range (J + 1), if J + 1 - n ≤ j then θ j * (1 / κ) ^ (j + 1 - (J + 1 - n))
        else 0 := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [Nat.sub_zero, hτJ]
      refine (Finset.sum_eq_zero fun j hj => ?_).symm
      rw [if_neg (by have := Finset.mem_range.mp hj; omega)]
    | succ n ih =>
      intro hn
      have hi : J + 1 - (n + 1) ≤ J := by omega
      have e1 : J + 1 - (n + 1) + 1 = J + 1 - n := by omega
      rw [hτ _ hi, e1, ih (by omega), ← Finset.add_sum_erase (Finset.range (J + 1))
        (fun j => if J + 1 - (n + 1) ≤ j then θ j * (1 / κ : ℝ) ^ (j + 1 - (J + 1 - (n + 1)))
          else 0) (Finset.mem_range.mpr (by omega : J + 1 - (n + 1) < J + 1)),
        ← Finset.add_sum_erase (Finset.range (J + 1))
        (fun j => if J + 1 - n ≤ j then θ j * (1 / κ : ℝ) ^ (j + 1 - (J + 1 - n)) else 0)
        (Finset.mem_range.mpr (by omega : J + 1 - (n + 1) < J + 1))]
      rw [if_pos le_rfl, if_neg (by omega), zero_add]
      have e2 : J + 1 - (n + 1) + 1 - (J + 1 - (n + 1)) = 1 := by omega
      rw [e2, pow_one, mul_add, Finset.mul_sum]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun j hj => ?_
        have hjne : j ≠ J + 1 - (n + 1) := (Finset.mem_erase.mp hj).1
        by_cases h : J + 1 - n ≤ j
        · rw [if_pos h, if_pos (by omega)]
          have e3 : j + 1 - (J + 1 - (n + 1)) = (j + 1 - (J + 1 - n)) + 1 := by omega
          rw [e3, pow_succ]; ring
        · rw [if_neg h, if_neg (by omega), mul_zero]
  have hτi : ∀ i, i ≤ J → τ i
      = ∑ j ∈ Finset.range (J + 1), if i ≤ j then θ j * (1 / κ) ^ (j + 1 - i) else 0 := by
    intro i hi
    have := key (J + 1 - i) (by omega)
    have e : J + 1 - (J + 1 - i) = i := by omega
    rw [e] at this
    exact this
  unfold r14A_R
  have lhs : ∀ j ∈ Finset.range (J + 1),
      θ j * ∑ i ∈ Finset.range (j + 1), L ^ i / (i.factorial : ℝ) * (1 / κ) ^ (j + 1 - i)
      = ∑ i ∈ Finset.range (J + 1),
        if i ≤ j then L ^ i / (i.factorial : ℝ) * (θ j * (1 / κ) ^ (j + 1 - i)) else 0 := by
    intro j hj
    have hjJ : j + 1 ≤ J + 1 := by have := Finset.mem_range.mp hj; omega
    rw [← Finset.sum_filter, Finset.mul_sum]
    have : (Finset.range (J + 1)).filter (fun i => i ≤ j) = Finset.range (j + 1) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [this]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl lhs, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiJ : i ≤ J := by have := Finset.mem_range.mp hi; omega
  rw [hτi i hiJ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rfl
  · rw [mul_zero]

theorem r14Cert_num_p1 (F : ℝ → ℝ) (b : ℕ → ℝ) :
    F (b (1 + 1)) - ∑ i ∈ Finset.range (1 + 1), (-1) ^ (1 - i) * (F (b i) - F (b (i + 1)))
      = 2 * F (b 2) - 2 * F (b 1) + F (b 0) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

theorem r14Cert_num_p2 (F : ℝ → ℝ) (b : ℕ → ℝ) :
    F (b (2 + 1)) - ∑ i ∈ Finset.range (2 + 1), (-1) ^ (2 - i) * (F (b i) - F (b (i + 1)))
      = 2 * F (b 3) - 2 * F (b 2) + 2 * F (b 1) - F (b 0) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r14Cert_modulus_of_sum
#print axioms DetPrimality.Bach.r14Cert_tau
