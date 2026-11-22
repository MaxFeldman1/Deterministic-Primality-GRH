import Mathlib
import DetPrimality.Bach.Blueprint

/-!
# §6.2 for small `n`: `noncoprimeSum` via the prime divisors of `n`

`noncoprimeSum n x = ∑_{m<x, (m,n)>1} Λ(m)` only sees prime powers `p^k < x` with `p ∣ n`, and each
prime `p` contributes `log p · #{k ≥ 1 : p^k < x} ≤ log x`.  Hence

* `noncoprimeSum_le_sum_log_mul_natLog`:
  `noncoprimeSum n x ≤ ∑_{p ∣ n, p < x} log p · ⌊log_p (⌈x⌉₊ - 1)⌋`;
* `noncoprimeSum_le_card_mul_log`: `noncoprimeSum n x ≤ #{p ∣ n : p < x} · log x`;
* `noncoprimeSum_le_omega_mul_log`: `noncoprimeSum n x ≤ ω(n) · log x`;
* `noncoprimeSum_le_log_add_sum_primeFactors`:
  `noncoprimeSum n x ≤ log n + ∑_{p ∣ n, p ≤ x} (log x - log p)`.

Since a number with `j` distinct prime factors is at least the `j`-th primorial
(`cno_primorial_le_of_card`), this gives for small `n` the explicit corollaries
`noncoprimeSum_le_of_lt_6`, `…_lt_30`, `…_lt_210`, `…_lt_2310`, `…_lt_30030`:
`n < P_{j+1}` and `x ≥ p_j` imply `noncoprimeSum n x ≤ log n + j log x - log P_j`.
-/

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## The general bound -/

/-- `∑_{m<x, (m,n)>1} Λ(m) ≤ ∑_{p ∣ n, p < x} log p · ⌊log_p (⌈x⌉₊ - 1)⌋`. -/
theorem noncoprimeSum_le_sum_log_mul_natLog {n : ℕ} (hn : 0 < n) (x : ℝ) :
    noncoprimeSum n x ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) < x),
      Real.log p * (Nat.log p (⌈x⌉₊ - 1) : ℝ) := by
  unfold noncoprimeSum
  set S := (Finset.range ⌈x⌉₊).filter (fun m => ¬ Nat.Coprime m n) with hS
  set T := n.primeFactors.filter (fun p : ℕ => (p : ℝ) < x) with hT
  have h1 : ∑ m ∈ S, Λ m = ∑ m ∈ S.filter IsPrimePow, Real.log (m.minFac) := by
    exact (Finset.sum_congr rfl fun m _ => ArithmeticFunction.vonMangoldt_apply).trans
      (Finset.sum_filter _ _).symm
  have hmaps : ∀ m ∈ S.filter IsPrimePow, m.minFac ∈ T := by
    intro m hm
    obtain ⟨hmS, hpp⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmr, hnc⟩ := Finset.mem_filter.mp hmS
    obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    have hp' : p.Prime := hp.nat_prime
    rw [hp'.pow_minFac hk.ne']
    obtain ⟨q, hq, hqm, hqn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp').mp (hq.dvd_of_dvd_pow hqm)
    subst hqp
    refine Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hq, hqn, hn.ne'⟩, ?_⟩
    have h2 : ((q ^ k : ℕ) : ℝ) < x := Nat.lt_ceil.mp (Finset.mem_range.mp hmr)
    have h3 : q ≤ q ^ k := Nat.le_self_pow hk.ne' q
    exact lt_of_le_of_lt (by exact_mod_cast h3) h2
  rw [h1, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpP : p.Prime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1
  have hsub : (S.filter IsPrimePow).filter (fun m => m.minFac = p)
      ⊆ (Finset.Icc 1 (Nat.log p (⌈x⌉₊ - 1))).image (fun k => p ^ k) := by
    intro m hm
    obtain ⟨hm1, hmp⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmS, hpp⟩ := Finset.mem_filter.mp hm1
    obtain ⟨hmr, -⟩ := Finset.mem_filter.mp hmS
    obtain ⟨q, k, hq, hk, rfl⟩ := hpp
    rw [hq.nat_prime.pow_minFac hk.ne'] at hmp
    subst hmp
    refine Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk, ?_⟩, rfl⟩
    have : q ^ k < ⌈x⌉₊ := Finset.mem_range.mp hmr
    exact Nat.le_log_of_pow_le hpP.one_lt (by omega)
  calc ∑ m ∈ (S.filter IsPrimePow).filter (fun m => m.minFac = p), Real.log (m.minFac)
      = ∑ m ∈ (S.filter IsPrimePow).filter (fun m => m.minFac = p), Real.log p :=
        Finset.sum_congr rfl fun m hm => by rw [(Finset.mem_filter.mp hm).2]
    _ = (((S.filter IsPrimePow).filter (fun m => m.minFac = p)).card : ℝ) * Real.log p := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Nat.log p (⌈x⌉₊ - 1) : ℝ) * Real.log p := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
        have h := (Finset.card_le_card hsub).trans Finset.card_image_le
        rw [Nat.card_Icc] at h
        have h' : ((S.filter IsPrimePow).filter (fun m => m.minFac = p)).card
            ≤ Nat.log p (⌈x⌉₊ - 1) := by omega
        exact_mod_cast h'
    _ = _ := mul_comm _ _

/-- Each prime contributes at most `log x`: `log p · ⌊log_p (⌈x⌉₊ - 1)⌋ ≤ log x` for `x ≥ 1`. -/
theorem cno_log_mul_natLog_le {p : ℕ} (hp : 0 < p) {x : ℝ} (hx : 1 ≤ x) :
    Real.log p * (Nat.log p (⌈x⌉₊ - 1) : ℝ) ≤ Real.log x := by
  rcases Nat.eq_zero_or_pos (⌈x⌉₊ - 1) with h | h
  · rw [h]
    simpa using Real.log_nonneg hx
  · have h1 : p ^ Nat.log p (⌈x⌉₊ - 1) ≤ ⌈x⌉₊ - 1 := Nat.pow_log_le_self p h.ne'
    have h2 : ((⌈x⌉₊ - 1 : ℕ) : ℝ) < x := Nat.lt_ceil.mp (by omega)
    have h3 : ((p ^ Nat.log p (⌈x⌉₊ - 1) : ℕ) : ℝ) < x :=
      lt_of_le_of_lt (by exact_mod_cast h1) h2
    have h4 : (0 : ℝ) < ((p ^ Nat.log p (⌈x⌉₊ - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_pos hp
    have h5 := Real.log_le_log h4 h3.le
    rwa [Nat.cast_pow, Real.log_pow, mul_comm] at h5

/-- `∑_{m<x, (m,n)>1} Λ(m) ≤ #{p ∣ n : p < x} · log x` for `x ≥ 1`. -/
theorem noncoprimeSum_le_card_mul_log {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 1 ≤ x) :
    noncoprimeSum n x
      ≤ ((n.primeFactors.filter (fun p : ℕ => (p : ℝ) < x)).card : ℝ) * Real.log x := by
  refine (noncoprimeSum_le_sum_log_mul_natLog hn x).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun p hp =>
    cno_log_mul_natLog_le (Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp).1) hx

/-- `∑_{m<x, (m,n)>1} Λ(m) ≤ ω(n) · log x` for `x ≥ 1`. -/
theorem noncoprimeSum_le_omega_mul_log {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 1 ≤ x) :
    noncoprimeSum n x ≤ (n.primeFactors.card : ℝ) * Real.log x := by
  refine (noncoprimeSum_le_card_mul_log hn hx).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.log_nonneg hx)
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-- `∑_{m<x, (m,n)>1} Λ(m) ≤ log n + ∑_{p ∣ n, p ≤ x} (log x - log p)` for `x ≥ 1`. -/
theorem noncoprimeSum_le_log_add_sum_primeFactors {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 1 ≤ x) :
    noncoprimeSum n x ≤ Real.log n
      + ∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ x), (Real.log x - Real.log p) := by
  have h1 := noncoprimeSum_le_card_mul_log hn hx
  rw [← nsmul_eq_mul, ← Finset.sum_const] at h1
  have h2 : ∑ _p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) < x), Real.log x
      = ∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) < x), Real.log p
        + ∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) < x), (Real.log x - Real.log p) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have h3 : ∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) < x), Real.log p ≤ Real.log n := by
    calc _ ≤ ∑ p ∈ n.primeFactors, Real.log p :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun p _ _ => Real.log_natCast_nonneg p)
      _ = Real.log ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) := by
          rw [Nat.cast_prod, Real.log_prod]
          intro p hp
          exact_mod_cast (Nat.pos_of_mem_primeFactors hp).ne'
      _ ≤ Real.log n := by
          apply Real.log_le_log
          · exact_mod_cast Finset.prod_pos fun p hp => Nat.pos_of_mem_primeFactors hp
          · exact_mod_cast Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  have h4 : ∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) < x), (Real.log x - Real.log p)
      ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ x), (Real.log x - Real.log p) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p hp _ => ?_)
    · obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hp1, hp2.le⟩
    · obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      have : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_mem_primeFactors hp1
      linarith [Real.log_le_log this hp2]
  linarith

/-! ## Primorial lower bounds for numbers with many prime factors -/

private theorem cno_step {k pk Pk : ℕ}
    (hcard : ((Finset.range pk).filter Nat.Prime).card ≤ k)
    (ih : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → s.card = k → Pk ≤ ∏ p ∈ s, p) :
    ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → s.card = k + 1 → pk * Pk ≤ ∏ p ∈ s, p := by
  intro s hs hc
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  have hq : s.max' hne ∈ s := Finset.max'_mem s hne
  have hqge : pk ≤ s.max' hne := by
    by_contra hlt
    have hlt := not_le.mp hlt
    have hsub : s ⊆ (Finset.range pk).filter Nat.Prime := fun p hp =>
      Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (lt_of_le_of_lt (Finset.le_max' s p hp) hlt), hs p hp⟩
    have := Finset.card_le_card hsub
    omega
  rw [← Finset.mul_prod_erase s _ hq]
  exact Nat.mul_le_mul hqge
    (ih _ (fun p hp => hs p (Finset.mem_of_mem_erase hp))
      (by rw [Finset.card_erase_of_mem hq, hc]; rfl))

private theorem cno_P0 : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → s.card = 0 → 1 ≤ ∏ p ∈ s, p := by
  intro s _ hc
  rw [Finset.card_eq_zero.mp hc]
  simp

private theorem cno_P1 : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → s.card = 1 → 2 ≤ ∏ p ∈ s, p :=
  cno_step (pk := 2) (by decide) cno_P0

private theorem cno_P2 : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → s.card = 2 → 6 ≤ ∏ p ∈ s, p :=
  cno_step (pk := 3) (by decide) cno_P1

private theorem cno_P3 : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → s.card = 3 → 30 ≤ ∏ p ∈ s, p :=
  cno_step (pk := 5) (by decide) cno_P2

private theorem cno_P4 : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → s.card = 4 → 210 ≤ ∏ p ∈ s, p :=
  cno_step (pk := 7) (by decide) cno_P3

private theorem cno_P5 : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → s.card = 5 → 2310 ≤ ∏ p ∈ s, p :=
  cno_step (pk := 11) (by decide) cno_P4

private theorem cno_P6 : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → s.card = 6 → 30030 ≤ ∏ p ∈ s, p :=
  cno_step (pk := 13) (by decide) cno_P5

private theorem cno_ge {k Pk n : ℕ} (hn : 0 < n)
    (ih : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → s.card = k → Pk ≤ ∏ p ∈ s, p)
    (h : k ≤ n.primeFactors.card) : Pk ≤ n := by
  obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq h
  calc Pk ≤ ∏ p ∈ t, p := ih t (fun p hp => Nat.prime_of_mem_primeFactors (ht hp)) htc
    _ ≤ ∏ p ∈ n.primeFactors, p :=
        Nat.le_of_dvd (Finset.prod_pos fun p hp => Nat.pos_of_mem_primeFactors hp)
          (Finset.prod_dvd_prod_of_subset _ _ _ ht)
    _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

/-- A positive integer with at least `j` distinct prime factors is at least the `j`-th primorial
(`j ≤ 6`). -/
theorem cno_primorial_le_of_card {n : ℕ} (hn : 0 < n) :
    (1 ≤ n.primeFactors.card → 2 ≤ n) ∧ (2 ≤ n.primeFactors.card → 6 ≤ n) ∧
    (3 ≤ n.primeFactors.card → 30 ≤ n) ∧ (4 ≤ n.primeFactors.card → 210 ≤ n) ∧
    (5 ≤ n.primeFactors.card → 2310 ≤ n) ∧ (6 ≤ n.primeFactors.card → 30030 ≤ n) :=
  ⟨cno_ge hn cno_P1, cno_ge hn cno_P2, cno_ge hn cno_P3, cno_ge hn cno_P4, cno_ge hn cno_P5,
    cno_ge hn cno_P6⟩

/-! ## Logarithms of primorials -/

theorem cno_log_6 : Real.log 6 = Real.log 2 + Real.log 3 := by
  rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num

theorem cno_log_30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
  rw [← cno_log_6, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num

theorem cno_log_210 : Real.log 210 = Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 := by
  rw [← cno_log_30, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num

theorem cno_log_2310 :
    Real.log 2310 = Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [← cno_log_210, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num

private theorem cno_log_le {P n : ℕ} (hP : 0 < P) (h : P ≤ n) :
    Real.log (P : ℝ) ≤ Real.log (n : ℝ) :=
  Real.log_le_log (by exact_mod_cast hP) (by exact_mod_cast h)

/-- Real-logarithm form of `cno_primorial_le_of_card`. -/
private theorem cno_logs {n : ℕ} (hn : 0 < n) :
    0 ≤ Real.log n ∧
    (1 ≤ n.primeFactors.card → Real.log 2 ≤ Real.log n) ∧
    (2 ≤ n.primeFactors.card → Real.log 6 ≤ Real.log n) ∧
    (3 ≤ n.primeFactors.card → Real.log 30 ≤ Real.log n) ∧
    (4 ≤ n.primeFactors.card → Real.log 210 ≤ Real.log n) ∧
    (5 ≤ n.primeFactors.card → Real.log 2310 ≤ Real.log n) := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := cno_primorial_le_of_card hn
  refine ⟨Real.log_natCast_nonneg n, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_⟩
  · exact_mod_cast cno_log_le (by norm_num) (h1 h)
  · exact_mod_cast cno_log_le (by norm_num) (h2 h)
  · exact_mod_cast cno_log_le (by norm_num) (h3 h)
  · exact_mod_cast cno_log_le (by norm_num) (h4 h)
  · exact_mod_cast cno_log_le (by norm_num) (h5 h)

private theorem cno_log_le_logx {c x : ℝ} (hc : 0 < c) (h : c ≤ x) : Real.log c ≤ Real.log x :=
  Real.log_le_log hc h

/-! ## Explicit corollaries for small `n` -/

/-- `n < 6 = 2·3`, `x ≥ 2`: `noncoprimeSum n x ≤ log n + log x - log 2`. -/
theorem noncoprimeSum_le_of_lt_6 {n : ℕ} (hn : 0 < n) (hn' : n < 6) {x : ℝ} (hx : 2 ≤ x) :
    noncoprimeSum n x ≤ Real.log n + Real.log x - Real.log 2 := by
  have hmain := noncoprimeSum_le_omega_mul_log hn (x := x) (by linarith)
  obtain ⟨-, p2, -, -, -, -⟩ := cno_primorial_le_of_card hn
  obtain ⟨l0, l1, -, -, -, -⟩ := cno_logs hn
  have hw : n.primeFactors.card ≤ 1 := by
    by_contra h
    have := p2 (by omega)
    omega
  have x2 := cno_log_le_logx (by norm_num) (show (2 : ℝ) ≤ x by linarith)
  generalize n.primeFactors.card = w at *
  interval_cases w
  · push_cast at hmain; linarith
  · have a1 := l1 le_rfl
    push_cast at hmain; linarith

/-- `n < 30 = 2·3·5`, `x ≥ 3`: `noncoprimeSum n x ≤ log n + 2 log x - log 6`. -/
theorem noncoprimeSum_le_of_lt_30 {n : ℕ} (hn : 0 < n) (hn' : n < 30) {x : ℝ} (hx : 3 ≤ x) :
    noncoprimeSum n x ≤ Real.log n + 2 * Real.log x - Real.log 6 := by
  have hmain := noncoprimeSum_le_omega_mul_log hn (x := x) (by linarith)
  obtain ⟨-, -, p3, -, -, -⟩ := cno_primorial_le_of_card hn
  obtain ⟨l0, l1, l2, -, -, -⟩ := cno_logs hn
  have hw : n.primeFactors.card ≤ 2 := by
    by_contra h
    have := p3 (by omega)
    omega
  have x2 := cno_log_le_logx (by norm_num) (show (2 : ℝ) ≤ x by linarith)
  have x3 := cno_log_le_logx (by norm_num) (show (3 : ℝ) ≤ x by linarith)
  rw [cno_log_6] at l2 ⊢
  generalize n.primeFactors.card = w at *
  interval_cases w
  · push_cast at hmain; linarith
  · have a1 := l1 le_rfl
    push_cast at hmain; linarith
  · have a2 := l2 le_rfl
    push_cast at hmain; linarith

/-- `n < 210 = 2·3·5·7`, `x ≥ 5`: `noncoprimeSum n x ≤ log n + 3 log x - log 30`. -/
theorem noncoprimeSum_le_of_lt_210 {n : ℕ} (hn : 0 < n) (hn' : n < 210) {x : ℝ} (hx : 5 ≤ x) :
    noncoprimeSum n x ≤ Real.log n + 3 * Real.log x - Real.log 30 := by
  have hmain := noncoprimeSum_le_omega_mul_log hn (x := x) (by linarith)
  obtain ⟨-, -, -, p4, -, -⟩ := cno_primorial_le_of_card hn
  obtain ⟨l0, l1, l2, l3, -, -⟩ := cno_logs hn
  have hw : n.primeFactors.card ≤ 3 := by
    by_contra h
    have := p4 (by omega)
    omega
  have x2 := cno_log_le_logx (by norm_num) (show (2 : ℝ) ≤ x by linarith)
  have x3 := cno_log_le_logx (by norm_num) (show (3 : ℝ) ≤ x by linarith)
  have x5 := cno_log_le_logx (by norm_num) (show (5 : ℝ) ≤ x by linarith)
  rw [cno_log_6] at l2
  rw [cno_log_30] at l3 ⊢
  generalize n.primeFactors.card = w at *
  interval_cases w
  · push_cast at hmain; linarith
  · have a1 := l1 le_rfl
    push_cast at hmain; linarith
  · have a2 := l2 le_rfl
    push_cast at hmain; linarith
  · have a3 := l3 le_rfl
    push_cast at hmain; linarith

/-- `n < 2310 = 2·3·5·7·11`, `x ≥ 7`: `noncoprimeSum n x ≤ log n + 4 log x - log 210`. -/
theorem noncoprimeSum_le_of_lt_2310 {n : ℕ} (hn : 0 < n) (hn' : n < 2310) {x : ℝ}
    (hx : 7 ≤ x) :
    noncoprimeSum n x ≤ Real.log n + 4 * Real.log x - Real.log 210 := by
  have hmain := noncoprimeSum_le_omega_mul_log hn (x := x) (by linarith)
  obtain ⟨-, -, -, -, p5, -⟩ := cno_primorial_le_of_card hn
  obtain ⟨l0, l1, l2, l3, l4, -⟩ := cno_logs hn
  have hw : n.primeFactors.card ≤ 4 := by
    by_contra h
    have := p5 (by omega)
    omega
  have x2 := cno_log_le_logx (by norm_num) (show (2 : ℝ) ≤ x by linarith)
  have x3 := cno_log_le_logx (by norm_num) (show (3 : ℝ) ≤ x by linarith)
  have x5 := cno_log_le_logx (by norm_num) (show (5 : ℝ) ≤ x by linarith)
  have x7 := cno_log_le_logx (by norm_num) (show (7 : ℝ) ≤ x by linarith)
  rw [cno_log_6] at l2
  rw [cno_log_30] at l3
  rw [cno_log_210] at l4 ⊢
  generalize n.primeFactors.card = w at *
  interval_cases w
  · push_cast at hmain; linarith
  · have a1 := l1 le_rfl
    push_cast at hmain; linarith
  · have a2 := l2 le_rfl
    push_cast at hmain; linarith
  · have a3 := l3 le_rfl
    push_cast at hmain; linarith
  · have a4 := l4 le_rfl
    push_cast at hmain; linarith

/-- `n < 30030 = 2·3·5·7·11·13`, `x ≥ 11`: `noncoprimeSum n x ≤ log n + 5 log x - log 2310`. -/
theorem noncoprimeSum_le_of_lt_30030 {n : ℕ} (hn : 0 < n) (hn' : n < 30030) {x : ℝ}
    (hx : 11 ≤ x) :
    noncoprimeSum n x ≤ Real.log n + 5 * Real.log x - Real.log 2310 := by
  have hmain := noncoprimeSum_le_omega_mul_log hn (x := x) (by linarith)
  obtain ⟨-, -, -, -, -, p6⟩ := cno_primorial_le_of_card hn
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := cno_logs hn
  have hw : n.primeFactors.card ≤ 5 := by
    by_contra h
    have := p6 (by omega)
    omega
  have x2 := cno_log_le_logx (by norm_num) (show (2 : ℝ) ≤ x by linarith)
  have x3 := cno_log_le_logx (by norm_num) (show (3 : ℝ) ≤ x by linarith)
  have x5 := cno_log_le_logx (by norm_num) (show (5 : ℝ) ≤ x by linarith)
  have x7 := cno_log_le_logx (by norm_num) (show (7 : ℝ) ≤ x by linarith)
  have x11 := cno_log_le_logx (by norm_num) (show (11 : ℝ) ≤ x by linarith)
  rw [cno_log_6] at l2
  rw [cno_log_30] at l3
  rw [cno_log_210] at l4
  rw [cno_log_2310] at l5 ⊢
  generalize n.primeFactors.card = w at *
  interval_cases w
  · push_cast at hmain; linarith
  · have a1 := l1 le_rfl
    push_cast at hmain; linarith
  · have a2 := l2 le_rfl
    push_cast at hmain; linarith
  · have a3 := l3 le_rfl
    push_cast at hmain; linarith
  · have a4 := l4 le_rfl
    push_cast at hmain; linarith
  · have a5 := l5 le_rfl
    push_cast at hmain; linarith

end DetPrimality.Bach
