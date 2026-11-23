import Mathlib
import DetPrimality.Bach.R13Defs

/-!
# Round 13 certificate, generic part (formal076 §1 Lemma E, §3)

* `r13Cert_modulus_of_factor` (**Lemma E**, exact modulus): if `s^{J+1} K(s) = (A − B(s−1)²) P(s)²`
  with `P` a real polynomial, `A, B ≥ 0`, `J + 1 = 2m`, and
  `(A − B(s−1)²) P(s) P(2−s) = ∑_{k=1}^m (e_k/2) (s^{m−k}(2−s)^m + s^m(2−s)^{m−k})`,
  then `‖K(1+it)‖ = G(t)` (stated as `≤`, the form of `R13Cert.modulus`); the proof uses
  `conj s = 2 − s` on `Re s = 1`.
* `r13Cert_tau` : `R(L) = ∑_i L^i/i! · τ_i` with `τ_i = (2/3)(θ_i + τ_{i+1})`, `τ_{J+1} = 0`.
-/

open Complex

namespace DetPrimality.Bach

theorem r13Cert_pow_sub {z : ℂ} (hz : z ≠ 0) {m k : ℕ} (hk : k ≤ m) :
    z ^ (m - k) = z ^ m * (1 / z) ^ k := by
  rw [one_div, inv_pow, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero k hz), ← pow_add,
    Nat.sub_add_cancel hk]

theorem r13Cert_sum_Icc {α : Type*} [AddCommMonoid α] (f : ℕ → α) (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 m, f k = ∑ k ∈ Finset.range m, f (k + 1) := by
  induction m with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- **Lemma E** (formal076 §1): exact modulus on the line `Re s = 1`. -/
theorem r13Cert_modulus_of_factor {J m d : ℕ} {θ e h : ℕ → ℝ} {A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hJ : J + 1 = 2 * m)
    (h1 : ∀ s : ℂ, ∑ j ∈ Finset.range (J + 1), (θ j : ℂ) * s ^ (J - j)
      = ((A : ℂ) - B * (s - 1) ^ 2) * (∑ i ∈ Finset.range d, (h i : ℂ) * s ^ i) ^ 2)
    (h2 : ∀ s : ℂ, ((A : ℂ) - B * (s - 1) ^ 2) *
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
  have hfac : (A : ℂ) - B * (s - 1) ^ 2 = ((A + B * t ^ 2 : ℝ) : ℂ) := by
    have : s - 1 = (t : ℂ) * I := by rw [hs]; ring
    rw [this, mul_pow, Complex.I_sq]; push_cast; ring
  have hAB : 0 ≤ A + B * t ^ 2 := by positivity
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
  have h1s : r13K θ J s * s ^ (J + 1) = ((A + B * t ^ 2 : ℝ) : ℂ) * P s ^ 2 := by
    rw [hK, h1 s, hfac, hP]
  have hnorm : ‖r13K θ J s‖ * (‖s‖ ^ 2) ^ m = (A + B * t ^ 2) * ‖P s‖ ^ 2 := by
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
  have h2s : ((A + B * t ^ 2 : ℝ) : ℂ) * ((‖P s‖ ^ 2 : ℝ) : ℂ)
      = ∑ k ∈ Finset.range m,
        (((‖s‖ ^ 2) ^ m * (e (k + 1) * ((1 : ℂ) / s ^ (k + 1)).re) : ℝ) : ℂ) := by
    rw [← hfac, ← hPP, hP, hP, h2 s]
    exact Finset.sum_congr rfl hk
  have hreal : (A + B * t ^ 2) * ‖P s‖ ^ 2
      = (‖s‖ ^ 2) ^ m * ∑ k ∈ Finset.Icc 1 m, e k * ((1 : ℂ) / s ^ k).re := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul, h2s, ← Complex.ofReal_sum,
      r13Cert_sum_Icc (fun k => e k * ((1 : ℂ) / s ^ k).re) m, Finset.mul_sum]
  have hNm : 0 < (‖s‖ ^ 2) ^ m := by positivity
  have hfin : ‖r13K θ J s‖ * (‖s‖ ^ 2) ^ m
      = (∑ k ∈ Finset.Icc 1 m, e k * ((1 : ℂ) / s ^ k).re) * (‖s‖ ^ 2) ^ m := by
    rw [hnorm, hreal]; ring
  exact le_of_eq (mul_right_cancel₀ hNm.ne' hfin)

/-- Horner-type evaluation of `r13R`: with `τ_i = ∑_{j ≥ i} θ_j (2/3)^{j+1−i}` given by the
recurrence `τ_i = (2/3)(θ_i + τ_{i+1})`, `R(L) = ∑_{i ≤ J} L^i/i! · τ_i`. -/
theorem r13Cert_tau {J : ℕ} {θ τ : ℕ → ℝ} (hτ : ∀ i, i ≤ J → τ i = 2 / 3 * (θ i + τ (i + 1)))
    (hτJ : τ (J + 1) = 0) (L : ℝ) :
    r13R θ J L = ∑ i ∈ Finset.range (J + 1), L ^ i / (i.factorial : ℝ) * τ i := by
  -- `τ i = ∑_{j ∈ range (J+1), i ≤ j} θ_j (2/3)^{j+1-i}` by downward induction
  have key : ∀ n, n ≤ J + 1 → τ (J + 1 - n)
      = ∑ j ∈ Finset.range (J + 1), if J + 1 - n ≤ j then θ j * (2 / 3) ^ (j + 1 - (J + 1 - n))
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
        (fun j => if J + 1 - (n + 1) ≤ j then θ j * (2 / 3 : ℝ) ^ (j + 1 - (J + 1 - (n + 1)))
          else 0) (Finset.mem_range.mpr (by omega : J + 1 - (n + 1) < J + 1)),
        ← Finset.add_sum_erase (Finset.range (J + 1))
        (fun j => if J + 1 - n ≤ j then θ j * (2 / 3 : ℝ) ^ (j + 1 - (J + 1 - n)) else 0)
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
      = ∑ j ∈ Finset.range (J + 1), if i ≤ j then θ j * (2 / 3) ^ (j + 1 - i) else 0 := by
    intro i hi
    have := key (J + 1 - i) (by omega)
    have e : J + 1 - (J + 1 - i) = i := by omega
    rw [e] at this
    exact this
  unfold r13R
  have lhs : ∀ j ∈ Finset.range (J + 1),
      θ j * ∑ i ∈ Finset.range (j + 1), L ^ i / (i.factorial : ℝ) * (2 / 3) ^ (j + 1 - i)
      = ∑ i ∈ Finset.range (J + 1),
        if i ≤ j then L ^ i / (i.factorial : ℝ) * (θ j * (2 / 3) ^ (j + 1 - i)) else 0 := by
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

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r13Cert_modulus_of_factor
#print axioms DetPrimality.Bach.r13Cert_tau
