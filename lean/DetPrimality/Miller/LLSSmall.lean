import DetPrimality.Miller.Basic

/-!
# Small-`n` table for the deterministic Miller test with `c = 1`

`llsElem_millerDet_one_small : ∀ n < 3000, millerDet 1 n = true ↔ n.Prime`, by a kernel-checked
table.  The executable functions of `Miller/Basic.lean` use well-founded recursion, so we mirror
them by fuel-based (structurally recursive) versions, prove these equal, and run
`decide +kernel` on the mirrors.
-/

namespace DetPrimality.Miller

/-- Fuel version of `oddDecomp`. -/
def llsElem_oddDecompF : ℕ → ℕ → ℕ × ℕ
  | 0, m => (0, m)
  | f + 1, m =>
    if m ≠ 0 ∧ m % 2 = 0 then
      ((llsElem_oddDecompF f (m / 2)).1 + 1, (llsElem_oddDecompF f (m / 2)).2)
    else (0, m)

theorem llsElem_oddDecompF_eq : ∀ (f m : ℕ), m ≤ f → llsElem_oddDecompF f m = oddDecomp m
  | 0, m, h => by
    have : m = 0 := by omega
    subst this
    rw [oddDecomp]
    simp [llsElem_oddDecompF]
  | f + 1, m, h => by
    rw [oddDecomp, llsElem_oddDecompF]
    dsimp only
    split_ifs with hm
    · rw [llsElem_oddDecompF_eq f (m / 2) (by omega)]
    · rfl

/-- Fuel version of `Nat.log2`. -/
def llsElem_log2F : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => if 2 ≤ n then llsElem_log2F f (n / 2) + 1 else 0

theorem llsElem_log2F_eq : ∀ (f n : ℕ), n ≤ f → llsElem_log2F f n = Nat.log2 n
  | 0, n, h => by
    have : n = 0 := by omega
    subst this
    rw [Nat.log2_def]
    simp [llsElem_log2F]
  | f + 1, n, h => by
    rw [Nat.log2_def, llsElem_log2F]
    split_ifs with hn
    · rw [llsElem_log2F_eq f (n / 2) (by omega)]
    · rfl

theorem llsElem_ceil_aux (q : ℚ) (A : ℕ) (hq : q * 1000000 = (A : ℚ)) :
    ⌈q⌉₊ = (A + 999999) / 1000000 := by
  apply le_antisymm
  · rw [Nat.ceil_le]
    have h : A ≤ ((A + 999999) / 1000000) * 1000000 := by omega
    have h2 : (A : ℚ) ≤ (((A + 999999) / 1000000 : ℕ) : ℚ) * 1000000 := by exact_mod_cast h
    linarith
  · have h := Nat.le_ceil q
    have h2 : (A : ℚ) ≤ (⌈q⌉₊ : ℚ) * 1000000 := by linarith
    have h3 : A ≤ ⌈q⌉₊ * 1000000 := by exact_mod_cast h2
    omega

theorem llsElem_millerBound_one (n : ℕ) :
    millerBound 1 n = (480454 * (Nat.log2 n + 1) ^ 2 + 999999) / 1000000 := by
  unfold millerBound
  apply llsElem_ceil_aux
  unfold log2SqUpper
  push_cast
  ring

/-- Mirror of `sprp` with `a ^ e % n` and the fuel version of `oddDecomp`. -/
def llsElem_sprp (n a : ℕ) : Bool :=
  let s := (llsElem_oddDecompF (n - 1) (n - 1)).1
  let d := (llsElem_oddDecompF (n - 1) (n - 1)).2
  a ^ d % n == 1 || (List.range s).any (fun r => a ^ (d * 2 ^ r) % n == n - 1)

theorem llsElem_sprp_eq (n a : ℕ) : sprp n a = llsElem_sprp n a := by
  simp only [sprp, llsElem_sprp, twoVal, oddPart, powMod_eq, llsElem_oddDecompF_eq _ _ le_rfl]

/-- Mirror of `millerDet 1`. -/
def llsElem_millerDet (n : ℕ) : Bool :=
  if n < 2 then false
  else if n = 2 then true
  else if n % 2 = 0 then false
  else (List.range' 2
    (min ((480454 * (llsElem_log2F n n + 1) ^ 2 + 999999) / 1000000) n - 2)).all
      (fun a => llsElem_sprp n a)

theorem llsElem_millerDet_eq (n : ℕ) : millerDet 1 n = llsElem_millerDet n := by
  have h : (fun a => sprp n a) = fun a => llsElem_sprp n a := funext (llsElem_sprp_eq n)
  simp only [millerDet, llsElem_millerDet, llsElem_millerBound_one,
    llsElem_log2F_eq n n le_rfl, h]

/-- Trial division up to `54` (enough for `n < 3000`). -/
def llsElem_primeB (n : ℕ) : Bool :=
  decide (2 ≤ n) &&
    (List.range 55).all (fun m => decide (m < 2) || decide (n < m * m) || !decide (n % m = 0))

theorem llsElem_primeB_iff {n : ℕ} (hn : n < 3000) : llsElem_primeB n = true ↔ n.Prime := by
  rw [Nat.prime_def_le_sqrt]
  simp only [llsElem_primeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hs hd => ?_⟩
    have hmm : m * m ≤ n := Nat.le_sqrt.mp hs
    have hm55 : m < 55 := by nlinarith
    rcases h m hm55 with (h1 | h1) | h1
    · omega
    · omega
    · exact h1 (Nat.mod_eq_zero_of_dvd hd)
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m _ => ?_⟩
    by_cases h1 : m < 2
    · exact Or.inl (Or.inl h1)
    by_cases h3 : n < m * m
    · exact Or.inl (Or.inr h3)
    exact Or.inr fun h0 =>
      h m (by omega) (Nat.le_sqrt.mpr (by omega)) (Nat.dvd_of_mod_eq_zero h0)

theorem llsElem_table :
    (List.range 3000).all (fun n => llsElem_millerDet n == llsElem_primeB n) = true := by
  decide +kernel

/-- **Small-`n` table**: the deterministic Miller test with `c = 1` is correct below `3000`. -/
theorem llsElem_millerDet_one_small : ∀ n < 3000, (millerDet 1 n = true ↔ n.Prime) := by
  intro n hn
  have h := List.all_eq_true.mp llsElem_table n (List.mem_range.mpr hn)
  rw [llsElem_millerDet_eq, ← llsElem_primeB_iff hn, beq_iff_eq.mp h]

end DetPrimality.Miller

#print axioms DetPrimality.Miller.llsElem_millerDet_one_small
