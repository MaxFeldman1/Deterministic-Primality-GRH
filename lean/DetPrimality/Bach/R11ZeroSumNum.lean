import DetPrimality.Bach.R11ZeroSumTele
import DetPrimality.Bach.R11ZeroSumSeries

/-!
# Round 11, zero sums: certified lower bounds for `F₀ = -ζ'/ζ(3/2)` and `F₁ = (ζ'/ζ)'(3/2)`

With `Z = ∑ n^{-3/2}`, `D₁ = ∑ log n · n^{-3/2}`, `D₂ = ∑ log² n · n^{-3/2}`:
`F₀ Z = D₁` (`Λ * 1 = log`) and `F₁ Z + F₀ D₁ = D₂` (its derivative).  The three smooth sums are
bounded by exact integer arithmetic for `n < 256` (`log n` through a table of
`⌊2^20 log₂ n⌋`, checked by `2^e ≤ n^(2^20) < 2^(e+1)`; `n^{-3/2}` through certified integer
square roots at scale `2^40`) plus the trapezoid/midpoint tail bounds of `R11ZeroSumTele`.

Results: `1.5052349 ≤ F₀ ≤ 1.5052362`, `3.8549585 ≤ F₁` (true: `1.5052354`, `3.8549629`).
-/

open Complex Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

noncomputable def r11Zs_Zs : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ)

noncomputable def r11Zs_D1 : ℝ := ∑' n : ℕ, Real.log n / (n : ℝ) ^ (3 / 2 : ℝ)

noncomputable def r11Zs_D2 : ℝ := ∑' n : ℕ, Real.log n ^ 2 / (n : ℝ) ^ (3 / 2 : ℝ)

/-! ## The two convolution identities -/

theorem r11Zs_F0_mul : r11Zs_F0 * r11Zs_Zs = r11Zs_D1 :=
  szs_tsum_mul (σ := 3 / 2) (by norm_num)

theorem r11Zs_F1_mul : r11Zs_F1 * r11Zs_Zs + r11Zs_F0 * r11Zs_D1 = r11Zs_D2 := by
  have hΛabs : LSeries.abscissaOfAbsConv (fun n : ℕ => ((Λ n : ℝ) : ℂ))
      < ((3 / 2 : ℂ).re : EReal) := by
    have h : LSeries.abscissaOfAbsConv (fun n : ℕ => ((Λ n : ℝ) : ℂ)) ≤ ((1 : ℝ) : EReal) :=
      LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
        (fun y hy => ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy))
    exact lt_of_le_of_lt h (by rw [EReal.coe_lt_coe_iff]; exact r11Zs_one_lt_re)
  have h1abs : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < ((3 / 2 : ℂ).re : EReal) := by
    have h : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) ≤ ((1 : ℝ) : EReal) :=
      LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
        (fun y hy => LSeriesSummable_one_iff.mpr (by simpa using hy))
    exact lt_of_le_of_lt h (by rw [EReal.coe_lt_coe_iff]; exact r11Zs_one_lt_re)
  have hlg : LSeries.logMul (1 : ℕ → ℂ) = fun n : ℕ => Complex.log (n : ℂ) := by
    funext n; simp [LSeries.logMul]
  have hlabs : LSeries.abscissaOfAbsConv (LSeries.logMul (1 : ℕ → ℂ))
      < ((3 / 2 : ℂ).re : EReal) := by
    rw [LSeries.abscissaOfAbsConv_logMul]; exact h1abs
  have hid : (fun s : ℂ => LSeries (fun n : ℕ => ((Λ n : ℝ) : ℂ)) s * LSeries (1 : ℕ → ℂ) s)
      =ᶠ[𝓝 (3 / 2 : ℂ)] LSeries (LSeries.logMul (1 : ℕ → ℂ)) := by
    filter_upwards [r11Zs_eventually_re] with s hs
    have h1 := LSeries_convolution' (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
      (LSeriesSummable_one_iff.mpr hs)
    rw [ArithmeticFunction.convolution_vonMangoldt_const_one] at h1
    rw [hlg, h1]
  have hL := (LSeries_hasDerivAt hΛabs).mul (LSeries_hasDerivAt h1abs)
  have hR := (LSeries_hasDerivAt hlabs).congr_of_eventuallyEq hid
  have hEq := hL.unique hR
  have el1 : LSeries.logMul (LSeries.logMul (1 : ℕ → ℂ))
      = fun n : ℕ => ((Real.log n ^ 2 : ℝ) : ℂ) := by
    funext n
    simp only [LSeries.logMul, Pi.one_apply, mul_one]
    rw [← Complex.natCast_log]
    push_cast
    ring
  have el2 : LSeries.logMul (1 : ℕ → ℂ) = fun n : ℕ => ((Real.log n : ℝ) : ℂ) := by
    funext n
    simp only [LSeries.logMul, Pi.one_apply, mul_one]
    rw [← Complex.natCast_log]
  have el3 : LSeries.logMul (fun n : ℕ => ((Λ n : ℝ) : ℂ))
      = fun n : ℕ => ((Λ n * Real.log n : ℝ) : ℂ) := by
    funext n
    simp only [LSeries.logMul]
    rw [← Complex.natCast_log]
    push_cast
    ring
  have e1 : (1 : ℕ → ℂ) = fun n : ℕ => (((fun _ : ℕ => (1 : ℝ)) n : ℝ) : ℂ) := by
    funext n; simp
  have h32 : (3 / 2 : ℝ) ≠ 0 := by norm_num
  rw [el1, el2, el3, e1, ← r11Zs_three_halves, szs_LSeries_ofReal _ h32,
    szs_LSeries_ofReal _ h32, szs_LSeries_ofReal _ h32, szs_LSeries_ofReal _ h32,
    szs_LSeries_ofReal _ h32] at hEq
  have hEq' : -r11Zs_F1 * r11Zs_Zs + r11Zs_F0 * -r11Zs_D1 = -r11Zs_D2 := by
    exact_mod_cast hEq
  linarith

/-! ## Integer certificates -/

/-- `r11Zs_tab n = ⌊2^20 log₂ n⌋` for `1 ≤ n ≤ 255`. -/
def r11Zs_tabL : List ℕ := [0, 0, 1048576, 1661953, 2097152, 2434718, 2710529, 2943724, 3145728, 3323907, 3483294, 3627476, 3759105, 3880192, 3992300, 4096671, 4194304, 4286015, 4372483, 4454274, 4531870, 4605678, 4676052, 4743298, 4807681, 4869436, 4928768, 4985860, 5040876, 5093962, 5145247, 5194851, 5242880, 5289430, 5334591, 5378443, 5421059, 5462507, 5502850, 5542145, 5580446, 5617800, 5654254, 5689850, 5724628, 5758625, 5791874, 5824408, 5856257, 5887449, 5918012, 5947969, 5977344, 6006159, 6034436, 6062195, 6089452, 6116228, 6142538, 6168398, 6193823, 6218828, 6243427, 6267632, 6291456, 6314910, 6338006, 6360755, 6383167, 6405252, 6427019, 6448477, 6469635, 6490501, 6511083, 6531389, 6551426, 6571201, 6590721, 6609993, 6629022, 6647814, 6666376, 6684713, 6702830, 6720733, 6738426, 6755915, 6773204, 6790298, 6807201, 6823917, 6840450, 6856804, 6872984, 6888992, 6904833, 6920510, 6936025, 6951384, 6966588, 6981640, 6996545, 7011303, 7025920, 7040396, 7054735, 7068940, 7083012, 7096955, 7110771, 7124461, 7138028, 7151475, 7164804, 7178016, 7191114, 7204099, 7216974, 7229740, 7242399, 7254953, 7267404, 7279754, 7292003, 7304154, 7316208, 7328167, 7340032, 7351804, 7363486, 7375078, 7386582, 7397999, 7409331, 7420578, 7431743, 7442826, 7453828, 7464750, 7475595, 7486362, 7497053, 7507669, 7518211, 7528680, 7539077, 7549403, 7559659, 7569846, 7579965, 7590017, 7600002, 7609922, 7619777, 7629569, 7639297, 7648964, 7658569, 7668113, 7677598, 7687023, 7696390, 7705699, 7714952, 7724148, 7733289, 7742375, 7751406, 7760384, 7769309, 7778182, 7787002, 7795772, 7804491, 7813161, 7821780, 7830351, 7838874, 7847349, 7855777, 7864158, 7872493, 7880782, 7889026, 7897225, 7905380, 7913492, 7921560, 7929585, 7937568, 7945510, 7953409, 7961268, 7969086, 7976863, 7984601, 7992300, 7999960, 8007581, 8015164, 8022709, 8030216, 8037687, 8045121, 8052518, 8059879, 8067205, 8074496, 8081751, 8088972, 8096159, 8103311, 8110430, 8117516, 8124569, 8131588, 8138576, 8145531, 8152455, 8159347, 8166207, 8173037, 8179836, 8186604, 8193343, 8200051, 8206730, 8213380, 8220000, 8226592, 8233155, 8239690, 8246196, 8252675, 8259126, 8265550, 8271946, 8278316, 8284659, 8290975, 8297265, 8303529, 8309768, 8315980, 8322168, 8328330, 8334467, 8340579, 8346666, 8352730, 8358769, 8364784, 8370775, 8376743, 8382687]

def r11Zs_tab (n : ℕ) : ℕ := r11Zs_tabL.getD n 0

def r11Zs_chk : ℕ → Bool
  | 0 => true
  | n + 1 => r11Zs_chk n && (Nat.ble (2 ^ r11Zs_tab (n + 1)) ((n + 1) ^ 2 ^ 20)
      && Nat.blt ((n + 1) ^ 2 ^ 20) (2 ^ (r11Zs_tab (n + 1) + 1)))

set_option maxRecDepth 100000 in
theorem r11Zs_cert_chk : r11Zs_chk 255 = true := by decide +kernel

theorem r11Zs_chk_spec : ∀ m : ℕ, r11Zs_chk m = true → ∀ n : ℕ, 1 ≤ n → n ≤ m →
    2 ^ r11Zs_tab n ≤ n ^ 2 ^ 20 ∧ n ^ 2 ^ 20 < 2 ^ (r11Zs_tab n + 1) := by
  intro m
  induction m with
  | zero => intro _ n h1 h2; omega
  | succ m ih =>
    intro h n h1 h2
    simp only [r11Zs_chk, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    rcases Nat.lt_or_eq_of_le h2 with h3 | rfl
    · exact ih h.1 n h1 (by omega)
    · exact h.2

theorem r11Zs_tab_zero : r11Zs_tab 0 = 0 := by decide +kernel

theorem r11Zs_log_bounds (n : ℕ) (hn : n ≤ 255) :
    (r11Zs_tab n : ℝ) * Real.log 2 / 2 ^ 20 ≤ Real.log n ∧
      Real.log n ≤ ((r11Zs_tab n : ℝ) + 1) * Real.log 2 / 2 ^ 20 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [r11Zs_tab_zero]
    simp only [Nat.cast_zero, Real.log_zero, zero_mul, zero_div, le_refl, zero_add, one_mul,
      true_and]
    positivity
  · obtain ⟨h1, h2⟩ := r11Zs_chk_spec 255 r11Zs_cert_chk n hpos hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hpos
    have h1' : (2 : ℝ) ^ r11Zs_tab n ≤ (n : ℝ) ^ 2 ^ 20 := by exact_mod_cast h1
    have h2' : (n : ℝ) ^ 2 ^ 20 ≤ (2 : ℝ) ^ (r11Zs_tab n + 1) := by exact_mod_cast h2.le
    have h3 := Real.log_le_log (by positivity) h1'
    have h4 := Real.log_le_log (by positivity) h2'
    rw [Real.log_pow, Real.log_pow] at h3 h4
    push_cast at h3 h4
    constructor
    · rw [div_le_iff₀ (by positivity)]; linarith
    · rw [le_div_iff₀ (by positivity)]; linarith

/-- Lower bound for `2^40 n^{-3/2}`. -/
def r11Zs_rl (n : ℕ) : ℕ := 2 ^ 80 / (n * szs_hi (n * 4 ^ 40))

/-- Upper bound for `2^40 n^{-3/2}`. -/
def r11Zs_ru (n : ℕ) : ℕ :=
  if n = 0 then 0 else
    if szs_lo (n * 4 ^ 40) = 0 then 2 ^ 40 else 2 ^ 80 / (n * szs_lo (n * 4 ^ 40)) + 1

theorem r11Zs_sqrt_scale (n : ℕ) : √((n : ℝ) * 4 ^ 40) = √(n : ℝ) * 2 ^ 40 := by
  rw [Real.sqrt_mul (Nat.cast_nonneg n), show (4 : ℝ) ^ 40 = (2 ^ 40) ^ 2 by norm_num,
    Real.sqrt_sq (by positivity)]

theorem r11Zs_rpow_neg (n : ℕ) : (n : ℝ) ^ (-(3 / 2) : ℝ) = ((n : ℝ) * √(n : ℝ))⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.rpow_neg hn'.le, szs_rpow_three_halves hn']

theorem r11Zs_rl_le (n : ℕ) : (r11Zs_rl n : ℝ) / 2 ^ 40 ≤ (n : ℝ) ^ (-(3 / 2) : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : r11Zs_rl 0 = 0 := by simp [r11Zs_rl]
    rw [this]
    simp [Real.zero_rpow]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn'
    have hpos : (0 : ℝ) < (szs_hi (n * 4 ^ 40) : ℝ) := by exact_mod_cast szs_hi_pos _
    have hle : (n : ℝ) * 4 ^ 40 ≤ ((szs_hi (n * 4 ^ 40) : ℝ)) ^ 2 := by
      have := szs_le_hi_sq (n * 4 ^ 40)
      rw [sq]
      exact_mod_cast this
    have hs : √(n : ℝ) * 2 ^ 40 ≤ (szs_hi (n * 4 ^ 40) : ℝ) := by
      rw [← r11Zs_sqrt_scale, ← Real.sqrt_sq hpos.le]
      exact Real.sqrt_le_sqrt hle
    have h1 : (r11Zs_rl n : ℝ) ≤ (2 : ℝ) ^ 80 / ((n : ℝ) * (szs_hi (n * 4 ^ 40) : ℝ)) := by
      have := Nat.cast_div_le (α := ℝ) (m := 2 ^ 80) (n := n * szs_hi (n * 4 ^ 40))
      unfold r11Zs_rl
      refine this.trans (le_of_eq ?_)
      push_cast
      ring
    have h2 : (2 : ℝ) ^ 80 / ((n : ℝ) * (szs_hi (n * 4 ^ 40) : ℝ))
        ≤ 2 ^ 40 * ((n : ℝ) * √(n : ℝ))⁻¹ := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2 ^ 40 * n)
      calc (2 : ℝ) ^ 80 * ((n : ℝ) * √(n : ℝ)) = 2 ^ 40 * n * (√(n : ℝ) * 2 ^ 40) := by ring
        _ ≤ 2 ^ 40 * n * (szs_hi (n * 4 ^ 40) : ℝ) := this
        _ = 2 ^ 40 * ((n : ℝ) * (szs_hi (n * 4 ^ 40) : ℝ)) := by ring
    rw [r11Zs_rpow_neg, div_le_iff₀ (by positivity)]
    linarith [h1.trans h2]

theorem r11Zs_le_ru (n : ℕ) : (n : ℝ) ^ (-(3 / 2) : ℝ) ≤ (r11Zs_ru n : ℝ) / 2 ^ 40 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [r11Zs_ru, Real.zero_rpow]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn'
    rw [le_div_iff₀ (by positivity)]
    unfold r11Zs_ru
    rw [if_neg hn.ne']
    by_cases h0 : szs_lo (n * 4 ^ 40) = 0
    · rw [if_pos h0]
      have : (n : ℝ) ^ (-(3 / 2) : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
      push_cast
      nlinarith
    · rw [if_neg h0]
      have hpos : (0 : ℝ) < (szs_lo (n * 4 ^ 40) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero h0
      have hle : ((szs_lo (n * 4 ^ 40) : ℝ)) ^ 2 ≤ (n : ℝ) * 4 ^ 40 := by
        have := szs_lo_sq_le (n * 4 ^ 40)
        rw [sq]
        exact_mod_cast this
      have hs : (szs_lo (n * 4 ^ 40) : ℝ) ≤ √(n : ℝ) * 2 ^ 40 := by
        rw [← r11Zs_sqrt_scale, ← Real.sqrt_sq hpos.le]
        exact Real.sqrt_le_sqrt hle
      have hbpos : 0 < n * szs_lo (n * 4 ^ 40) := Nat.mul_pos hn (Nat.pos_of_ne_zero h0)
      have h1 : (2 : ℝ) ^ 80 < ((n : ℝ) * (szs_lo (n * 4 ^ 40) : ℝ))
          * (((2 ^ 80 / (n * szs_lo (n * 4 ^ 40)) : ℕ) : ℝ) + 1) := by
        have := Nat.lt_mul_div_succ (2 ^ 80) hbpos
        exact_mod_cast this
      have h2 : (n : ℝ) * (szs_lo (n * 4 ^ 40) : ℝ) ≤ (n : ℝ) * (√(n : ℝ) * 2 ^ 40) :=
        mul_le_mul_of_nonneg_left hs hn'.le
      have hq : (0 : ℝ) ≤ ((2 ^ 80 / (n * szs_lo (n * 4 ^ 40)) : ℕ) : ℝ) + 1 := by positivity
      have h3 := mul_le_mul_of_nonneg_right h2 hq
      rw [r11Zs_rpow_neg]
      have h4 : ((n : ℝ) * √(n : ℝ))⁻¹ * 2 ^ 40 * ((n : ℝ) * (√(n : ℝ) * 2 ^ 40)) = 2 ^ 80 := by
        field_simp
      have h5 : ((n : ℝ) * √(n : ℝ))⁻¹ * 2 ^ 40 * ((n : ℝ) * (√(n : ℝ) * 2 ^ 40))
          ≤ (((2 ^ 80 / (n * szs_lo (n * 4 ^ 40)) : ℕ) : ℝ) + 1)
            * ((n : ℝ) * (√(n : ℝ) * 2 ^ 40)) := by
        rw [h4]; linarith
      have h6 := le_of_mul_le_mul_right h5 (by positivity)
      push_cast
      exact h6

def r11Zs_sumTo (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => r11Zs_sumTo f n + f n

theorem r11Zs_sumTo_eq (f : ℕ → ℕ) (n : ℕ) :
    r11Zs_sumTo f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [r11Zs_sumTo, ih, Finset.sum_range_succ]

theorem r11Zs_sumTo_cast (f : ℕ → ℕ) (n : ℕ) :
    ((r11Zs_sumTo f n : ℕ) : ℝ) = ∑ i ∈ Finset.range n, (f i : ℝ) := by
  rw [r11Zs_sumTo_eq]; push_cast; rfl

set_option maxRecDepth 100000 in
theorem r11Zs_cert_Zl : 2734763769593 ≤ r11Zs_sumTo r11Zs_rl 256 := by decide +kernel

set_option maxRecDepth 100000 in
theorem r11Zs_cert_Zu : r11Zs_sumTo r11Zs_ru 256 ≤ 2734763769853 := by decide +kernel

set_option maxRecDepth 100000 in
theorem r11Zs_cert_D1l :
    4970672479026152789 ≤ r11Zs_sumTo (fun n => r11Zs_tab n * r11Zs_rl n) 256 := by decide +kernel

set_option maxRecDepth 100000 in
theorem r11Zs_cert_D1u :
    r11Zs_sumTo (fun n => (r11Zs_tab n + 1) * r11Zs_ru n) 256 ≤ 4970675215560963481 := by decide +kernel

set_option maxRecDepth 100000 in
theorem r11Zs_cert_D2l :
    21059724285351519779679445 ≤ r11Zs_sumTo (fun n => r11Zs_tab n ^ 2 * r11Zs_rl n) 256 := by decide +kernel

/-! ## Partial sums `n < 256` -/

theorem r11Zs_term (n : ℕ) (hn : n ∈ Finset.range 256) :
    0 ≤ (r11Zs_rl n : ℝ) / 2 ^ 40 ∧
    (r11Zs_rl n : ℝ) / 2 ^ 40 ≤ (n : ℝ) ^ (-(3 / 2) : ℝ) ∧
    (n : ℝ) ^ (-(3 / 2) : ℝ) ≤ (r11Zs_ru n : ℝ) / 2 ^ 40 ∧
    0 ≤ (r11Zs_tab n : ℝ) * Real.log 2 / 2 ^ 20 ∧
    (r11Zs_tab n : ℝ) * Real.log 2 / 2 ^ 20 ≤ Real.log n ∧
    Real.log n ≤ ((r11Zs_tab n : ℝ) + 1) * Real.log 2 / 2 ^ 20 := by
  have hn' : n ≤ 255 := by
    have := Finset.mem_range.mp hn
    omega
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨h1, h2⟩ := r11Zs_log_bounds n hn'
  exact ⟨by positivity, r11Zs_rl_le n, r11Zs_le_ru n, by positivity, h1, h2⟩

theorem r11Zs_part_Zl : (2734763769593 : ℝ) / 2 ^ 40
    ≤ ∑ n ∈ Finset.range 256, r11Zs_P 1 0 0 (-(3 / 2)) n := by
  have hc : ((2734763769593 : ℕ) : ℝ) ≤ ((r11Zs_sumTo r11Zs_rl 256 : ℕ) : ℝ) :=
    Nat.cast_le.mpr r11Zs_cert_Zl
  rw [r11Zs_sumTo_cast] at hc
  have h : ∑ n ∈ Finset.range 256, (r11Zs_rl n : ℝ) / 2 ^ 40
      ≤ ∑ n ∈ Finset.range 256, r11Zs_P 1 0 0 (-(3 / 2)) n := by
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨-, h2, -⟩ := r11Zs_term n hn
    unfold r11Zs_P
    linarith
  rw [← Finset.sum_div] at h
  have : (2734763769593 : ℝ) / 2 ^ 40 ≤ (∑ n ∈ Finset.range 256, (r11Zs_rl n : ℝ)) / 2 ^ 40 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hc
  linarith

theorem r11Zs_part_Zu : ∑ n ∈ Finset.range 256, r11Zs_P 1 0 0 (-(3 / 2)) n
    ≤ (2734763769853 : ℝ) / 2 ^ 40 := by
  have hc : ((r11Zs_sumTo r11Zs_ru 256 : ℕ) : ℝ) ≤ ((2734763769853 : ℕ) : ℝ) :=
    Nat.cast_le.mpr r11Zs_cert_Zu
  rw [r11Zs_sumTo_cast] at hc
  have h : ∑ n ∈ Finset.range 256, r11Zs_P 1 0 0 (-(3 / 2)) n
      ≤ ∑ n ∈ Finset.range 256, (r11Zs_ru n : ℝ) / 2 ^ 40 := by
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨-, -, h3, -⟩ := r11Zs_term n hn
    unfold r11Zs_P
    linarith
  rw [← Finset.sum_div] at h
  have : (∑ n ∈ Finset.range 256, (r11Zs_ru n : ℝ)) / 2 ^ 40 ≤ (2734763769853 : ℝ) / 2 ^ 40 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hc
  linarith

theorem r11Zs_part_D1l : (4970672479026152789 : ℝ) * Real.log 2 / 2 ^ 60
    ≤ ∑ n ∈ Finset.range 256, r11Zs_P 0 1 0 (-(3 / 2)) n := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : ((4970672479026152789 : ℕ) : ℝ)
      ≤ ((r11Zs_sumTo (fun n => r11Zs_tab n * r11Zs_rl n) 256 : ℕ) : ℝ) :=
    Nat.cast_le.mpr r11Zs_cert_D1l
  rw [r11Zs_sumTo_cast] at hc
  have h : ∑ n ∈ Finset.range 256, ((r11Zs_tab n * r11Zs_rl n : ℕ) : ℝ) * (Real.log 2 / 2 ^ 60)
      ≤ ∑ n ∈ Finset.range 256, r11Zs_P 0 1 0 (-(3 / 2)) n := by
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨h1, h2, -, h4, h5, -⟩ := r11Zs_term n hn
    have hx : 0 ≤ (n : ℝ) ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hL : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    unfold r11Zs_P
    push_cast
    calc (r11Zs_tab n : ℝ) * (r11Zs_rl n : ℝ) * (Real.log 2 / 2 ^ 60)
        = ((r11Zs_tab n : ℝ) * Real.log 2 / 2 ^ 20) * ((r11Zs_rl n : ℝ) / 2 ^ 40) := by ring
      _ ≤ Real.log (n : ℝ) * (n : ℝ) ^ (-(3 / 2) : ℝ) := mul_le_mul h5 h2 h1 hL
      _ = _ := by ring
  rw [← Finset.sum_mul] at h
  have h7 := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ Real.log 2 / 2 ^ 60)
  have e : ((4970672479026152789 : ℕ) : ℝ) * (Real.log 2 / 2 ^ 60) = (4970672479026152789 : ℝ) * Real.log 2 / 2 ^ 60 := by
    push_cast; ring
  linarith

theorem r11Zs_part_D1u : ∑ n ∈ Finset.range 256, r11Zs_P 0 1 0 (-(3 / 2)) n
    ≤ (4970675215560963481 : ℝ) * Real.log 2 / 2 ^ 60 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : ((r11Zs_sumTo (fun n => (r11Zs_tab n + 1) * r11Zs_ru n) 256 : ℕ) : ℝ)
      ≤ ((4970675215560963481 : ℕ) : ℝ) :=
    Nat.cast_le.mpr r11Zs_cert_D1u
  rw [r11Zs_sumTo_cast] at hc
  have h : ∑ n ∈ Finset.range 256, r11Zs_P 0 1 0 (-(3 / 2)) n
      ≤ ∑ n ∈ Finset.range 256,
        (((r11Zs_tab n + 1) * r11Zs_ru n : ℕ) : ℝ) * (Real.log 2 / 2 ^ 60) := by
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := r11Zs_term n hn
    have hx : 0 ≤ (n : ℝ) ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hL : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    unfold r11Zs_P
    push_cast
    calc (0 * Real.log (n : ℝ) ^ 2 + 1 * Real.log (n : ℝ) + 0) * (n : ℝ) ^ (-(3 / 2) : ℝ)
        = Real.log (n : ℝ) * (n : ℝ) ^ (-(3 / 2) : ℝ) := by ring
      _ ≤ (((r11Zs_tab n : ℝ) + 1) * Real.log 2 / 2 ^ 20) * ((r11Zs_ru n : ℝ) / 2 ^ 40) :=
          mul_le_mul h6 h3 hx (le_trans hL h6)
      _ = _ := by ring
  rw [← Finset.sum_mul] at h
  have h7 := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ Real.log 2 / 2 ^ 60)
  have e : ((4970675215560963481 : ℕ) : ℝ) * (Real.log 2 / 2 ^ 60) = (4970675215560963481 : ℝ) * Real.log 2 / 2 ^ 60 := by
    push_cast; ring
  linarith

theorem r11Zs_part_D2l : (21059724285351519779679445 : ℝ) * Real.log 2 ^ 2 / 2 ^ 80
    ≤ ∑ n ∈ Finset.range 256, r11Zs_P 0 0 1 (-(3 / 2)) n := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : ((21059724285351519779679445 : ℕ) : ℝ)
      ≤ ((r11Zs_sumTo (fun n => r11Zs_tab n ^ 2 * r11Zs_rl n) 256 : ℕ) : ℝ) :=
    Nat.cast_le.mpr r11Zs_cert_D2l
  rw [r11Zs_sumTo_cast] at hc
  have h : ∑ n ∈ Finset.range 256,
        ((r11Zs_tab n ^ 2 * r11Zs_rl n : ℕ) : ℝ) * (Real.log 2 ^ 2 / 2 ^ 80)
      ≤ ∑ n ∈ Finset.range 256, r11Zs_P 0 0 1 (-(3 / 2)) n := by
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨h1, h2, -, h4, h5, -⟩ := r11Zs_term n hn
    have hsq : ((r11Zs_tab n : ℝ) * Real.log 2 / 2 ^ 20) ^ 2 ≤ Real.log (n : ℝ) ^ 2 :=
      pow_le_pow_left₀ h4 h5 2
    unfold r11Zs_P
    push_cast
    calc (r11Zs_tab n : ℝ) ^ 2 * (r11Zs_rl n : ℝ) * (Real.log 2 ^ 2 / 2 ^ 80)
        = ((r11Zs_tab n : ℝ) * Real.log 2 / 2 ^ 20) ^ 2 * ((r11Zs_rl n : ℝ) / 2 ^ 40) := by ring
      _ ≤ Real.log (n : ℝ) ^ 2 * (n : ℝ) ^ (-(3 / 2) : ℝ) :=
          mul_le_mul hsq h2 h1 (sq_nonneg _)
      _ = _ := by ring
  rw [← Finset.sum_mul] at h
  have h7 := mul_le_mul_of_nonneg_right hc
    (by positivity : (0 : ℝ) ≤ Real.log 2 ^ 2 / 2 ^ 80)
  have e : ((21059724285351519779679445 : ℕ) : ℝ) * (Real.log 2 ^ 2 / 2 ^ 80)
      = (21059724285351519779679445 : ℝ) * Real.log 2 ^ 2 / 2 ^ 80 := by
    push_cast; ring
  linarith

/-! ## Evaluation of the tail terms -/

theorem r11Zs_rpow_sq {s : ℝ} (hs : 0 < s) :
    (s ^ 2) ^ (-(1 / 2) : ℝ) = s⁻¹ ∧ (s ^ 2) ^ (-(3 / 2) : ℝ) = (s ^ 3)⁻¹ := by
  constructor
  · rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs.le,
      show ((2 : ℕ) : ℝ) * -(1 / 2) = -1 by norm_num, Real.rpow_neg_one]
  · rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs.le,
      show ((2 : ℕ) : ℝ) * -(3 / 2) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hs.le,
      Real.rpow_natCast]

theorem r11Zs_P_256 (c0 c1 c2 d0 d1 d2 : ℝ) :
    r11Zs_P d0 d1 d2 (-(1 / 2)) 256
      = (d2 * (64 * Real.log 2 ^ 2) + d1 * (8 * Real.log 2) + d0) / 16 ∧
    r11Zs_P c0 c1 c2 (-(3 / 2)) 256
      = (c2 * (64 * Real.log 2 ^ 2) + c1 * (8 * Real.log 2) + c0) / 4096 := by
  have hlog : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
  obtain ⟨h1, h2⟩ := r11Zs_rpow_sq (s := 16) (by norm_num)
  rw [show (16 : ℝ) ^ 2 = 256 by norm_num] at h1 h2
  unfold r11Zs_P
  rw [hlog, h1, h2]
  constructor <;> ring

theorem r11Zs_P_big (c0 c1 c2 d0 d1 d2 : ℝ) {T : ℝ} (hT : T = 2 ^ 80) :
    r11Zs_P d0 d1 d2 (-(1 / 2)) T
      = (d2 * (6400 * Real.log 2 ^ 2) + d1 * (80 * Real.log 2) + d0) / 2 ^ 40 ∧
    r11Zs_P c0 c1 c2 (-(3 / 2)) T
      = (c2 * (6400 * Real.log 2 ^ 2) + c1 * (80 * Real.log 2) + c0) / 2 ^ 120 := by
  have hlog : Real.log T = 80 * Real.log 2 := by
    rw [hT, Real.log_pow]; norm_num
  obtain ⟨h1, h2⟩ := r11Zs_rpow_sq (s := 2 ^ 40) (by positivity)
  rw [show ((2 : ℝ) ^ 40) ^ 2 = 2 ^ 80 by norm_num, ← hT] at h1 h2
  unfold r11Zs_P
  rw [hlog, h1, h2]
  constructor <;> ring

theorem r11Zs_half_facts :
    0 ≤ Real.log (255 + 1 / 2 : ℝ) ∧ Real.log (255 + 1 / 2 : ℝ) ≤ 8 * Real.log 2 - 1 / 512 ∧
      0 ≤ (255 + 1 / 2 : ℝ) ^ (-(1 / 2) : ℝ) ∧
      (255 + 1 / 2 : ℝ) ^ (-(1 / 2) : ℝ) ≤ 1000000000 / 15984367363 := by
  refine ⟨Real.log_nonneg (by norm_num), ?_, Real.rpow_nonneg (by norm_num) _, ?_⟩
  · have e : (255 + 1 / 2 : ℝ) = 2 ^ 8 * (511 / 512) := by norm_num
    rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 511 / 512 by norm_num)
    push_cast
    linarith
  · rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    have h : (15984367363 / 1000000000 : ℝ) ≤ √(255 + 1 / 2 : ℝ) :=
      Real.le_sqrt' (by norm_num) |>.mpr (by norm_num)
    have hpos : (0 : ℝ) < 15984367363 / 1000000000 := by norm_num
    calc (√(255 + 1 / 2 : ℝ))⁻¹ ≤ (15984367363 / 1000000000 : ℝ)⁻¹ :=
          inv_anti₀ hpos h
      _ = 1000000000 / 15984367363 := by norm_num

/-! ## The three smooth sums -/

theorem r11Zs_anti {c0 c1 c2 d0 d1 d2 : ℝ} (h0 : d1 + -(1 / 2) * d0 = -c0)
    (h1 : 2 * d2 + -(1 / 2) * d1 = -c1) (h2 : -(1 / 2) * d2 = -c2) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (r11Zs_P d0 d1 d2 (-(1 / 2))) (-(r11Zs_P c0 c1 c2 (-(3 / 2)) t)) t := by
  have h := r11Zs_P_hasDerivAt d0 d1 d2 (-(1 / 2)) ht
  rw [h0, h1, h2, show (-(1 / 2) - 1 : ℝ) = -(3 / 2) by norm_num] at h
  refine h.congr_deriv ?_
  unfold r11Zs_P
  ring

theorem r11Zs_P_apply_nat (c0 c1 c2 : ℝ) (n : ℕ) :
    r11Zs_P c0 c1 c2 (-(3 / 2)) n
      = (c2 * Real.log n ^ 2 + c1 * Real.log n + c0) / (n : ℝ) ^ (3 / 2 : ℝ) := by
  unfold r11Zs_P
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  exact (div_eq_mul_inv _ _).symm

theorem r11Zs_big_exists : ∃ j : ℕ, ((256 + j : ℕ) : ℝ) = 2 ^ 80 :=
  ⟨2 ^ 80 - 256, by norm_num⟩

theorem r11Zs_Zs_bounds : 2.6123752 ≤ r11Zs_Zs ∧ r11Zs_Zs ≤ 2.61237541 := by
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hsq : Real.log 2 ^ 2 ≤ 0.49 := by nlinarith
  have hconv := r11Zs_P_convex 1 0 0 (-(3 / 2)) (fun L hL => by norm_num)
  obtain ⟨hsum, hup, hlow⟩ := r11Zs_tsum_bounds (c0 := 1) (c1 := 0) (c2 := 0) (d0 := 2)
    (d1 := 0) (d2 := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (r11Zs_anti (by norm_num) (by norm_num) (by norm_num)) hconv
  have heq : ∑' n : ℕ, r11Zs_P 1 0 0 (-(3 / 2)) n = r11Zs_Zs :=
    tsum_congr fun n => by rw [r11Zs_P_apply_nat]; congr 1; ring
  rw [heq] at hup hlow
  obtain ⟨j, hj⟩ := r11Zs_big_exists
  have hlow' := hlow j
  obtain ⟨e1, e2⟩ := r11Zs_P_256 1 0 0 2 0 0
  obtain ⟨e3, e4⟩ := r11Zs_P_big 1 0 0 2 0 0 hj
  rw [e1, e2, e3, e4] at hlow'
  obtain ⟨g1, g2, g3, g4⟩ := r11Zs_half_facts
  have hA : r11Zs_P 2 0 0 (-(1 / 2)) (255 + 1 / 2) ≤ 2 * (1000000000 / 15984367363) := by
    unfold r11Zs_P
    nlinarith
  have p1 := r11Zs_part_Zl
  have p2 := r11Zs_part_Zu
  constructor
  · norm_num at hlow' p1 ⊢
    linarith
  · norm_num at hup p2 hA ⊢
    linarith

theorem r11Zs_D1_bounds : 3.9322388 ≤ r11Zs_D1 ∧ r11Zs_D1 ≤ 3.9322416 := by
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hsq : Real.log 2 ^ 2 ≤ 0.49 := by nlinarith
  have hconv := r11Zs_P_convex 0 1 0 (-(3 / 2)) (fun L hL => by norm_num; linarith)
  obtain ⟨hsum, hup, hlow⟩ := r11Zs_tsum_bounds (c0 := 0) (c1 := 1) (c2 := 0) (d0 := 4)
    (d1 := 2) (d2 := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (r11Zs_anti (by norm_num) (by norm_num) (by norm_num)) hconv
  have heq : ∑' n : ℕ, r11Zs_P 0 1 0 (-(3 / 2)) n = r11Zs_D1 :=
    tsum_congr fun n => by rw [r11Zs_P_apply_nat]; congr 1; ring
  rw [heq] at hup hlow
  obtain ⟨j, hj⟩ := r11Zs_big_exists
  have hlow' := hlow j
  obtain ⟨e1, e2⟩ := r11Zs_P_256 0 1 0 4 2 0
  obtain ⟨e3, e4⟩ := r11Zs_P_big 0 1 0 4 2 0 hj
  rw [e1, e2, e3, e4] at hlow'
  obtain ⟨g1, g2, g3, g4⟩ := r11Zs_half_facts
  have hA : r11Zs_P 4 2 0 (-(1 / 2)) (255 + 1 / 2)
      ≤ (2 * (8 * Real.log 2 - 1 / 512) + 4) * (1000000000 / 15984367363) := by
    unfold r11Zs_P
    have h1 : 0 * Real.log (255 + 1 / 2 : ℝ) ^ 2 + 2 * Real.log (255 + 1 / 2 : ℝ) + 4
        ≤ 2 * (8 * Real.log 2 - 1 / 512) + 4 := by linarith
    exact mul_le_mul h1 g4 g3 (by linarith)
  have p1 := r11Zs_part_D1l
  have p2 := r11Zs_part_D1u
  constructor
  · norm_num at hlow' p1 ⊢
    linarith
  · norm_num at hup p2 hA ⊢
    linarith

theorem r11Zs_D2_lower : 15.9895518 ≤ r11Zs_D2 := by
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hsq : Real.log 2 ^ 2 ≤ 0.49 := by nlinarith
  have hsq2 : (0.6931471803 : ℝ) ^ 2 ≤ Real.log 2 ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hl1.le 2
  have hconv := r11Zs_P_convex 0 0 1 (-(3 / 2)) (fun L hL => by
    norm_num
    nlinarith [sq_nonneg (L - 2)])
  obtain ⟨hsum, hup, hlow⟩ := r11Zs_tsum_bounds (c0 := 0) (c1 := 0) (c2 := 1) (d0 := 16)
    (d1 := 8) (d2 := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (r11Zs_anti (by norm_num) (by norm_num) (by norm_num)) hconv
  have heq : ∑' n : ℕ, r11Zs_P 0 0 1 (-(3 / 2)) n = r11Zs_D2 :=
    tsum_congr fun n => by rw [r11Zs_P_apply_nat]; congr 1; ring
  rw [heq] at hlow
  obtain ⟨j, hj⟩ := r11Zs_big_exists
  have hlow' := hlow j
  obtain ⟨e1, e2⟩ := r11Zs_P_256 0 0 1 16 8 2
  obtain ⟨e3, e4⟩ := r11Zs_P_big 0 0 1 16 8 2 hj
  rw [e1, e2, e3, e4] at hlow'
  have p1 := r11Zs_part_D2l
  norm_num at hlow' p1 hsq2 ⊢
  linarith

/-! ## `F₀` and `F₁` -/

theorem r11Zs_F0_nonneg : 0 ≤ r11Zs_F0 :=
  tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem r11Zs_F1_nonneg : 0 ≤ r11Zs_F1 :=
  tsum_nonneg fun n => div_nonneg
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg n))
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- `1.5052349 ≤ F₀ ≤ 1.5052362` (true value `1.5052354`). -/
theorem r11Zs_F0_bounds : 1.5052349 ≤ r11Zs_F0 ∧ r11Zs_F0 ≤ 1.5052362 := by
  obtain ⟨hZ1, hZ2⟩ := r11Zs_Zs_bounds
  obtain ⟨hD1, hD2⟩ := r11Zs_D1_bounds
  have hmul := r11Zs_F0_mul
  have h0 := r11Zs_F0_nonneg
  have h1 := mul_le_mul_of_nonneg_left hZ2 h0
  have h2 := mul_le_mul_of_nonneg_left hZ1 h0
  constructor <;> linarith

/-- `3.8549585 ≤ F₁` (true value `3.8549629`). -/
theorem r11Zs_F1_lower : 3.8549585 ≤ r11Zs_F1 := by
  obtain ⟨hZ1, hZ2⟩ := r11Zs_Zs_bounds
  obtain ⟨hD1, hD2⟩ := r11Zs_D1_bounds
  obtain ⟨hF1, hF2⟩ := r11Zs_F0_bounds
  have hD := r11Zs_D2_lower
  have hmul := r11Zs_F1_mul
  have h0 := r11Zs_F1_nonneg
  have h1 := mul_le_mul_of_nonneg_left hZ2 h0
  have h2 : r11Zs_F0 * r11Zs_D1 ≤ 1.5052362 * 3.9322416 :=
    mul_le_mul hF2 hD2 (by linarith) (by norm_num)
  norm_num at h2
  linarith

end DetPrimality.Bach
