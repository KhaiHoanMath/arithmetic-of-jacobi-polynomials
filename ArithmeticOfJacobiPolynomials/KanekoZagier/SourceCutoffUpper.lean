/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.ExplicitCutoffContent
public import ArithmeticOfJacobiPolynomials.KanekoZagier.ExplicitCutoffLower
public import ArithmeticOfJacobiPolynomials.KanekoZagier.SourceCutoffArchimedean

/-!
# Proposition B.1: the upper bound for `S_n + log g_n`, as printed

This file proves the intermediate estimates of "Content and the good-prime sum" in the proof of
Proposition B.1 with the printed constants:

* `kzHigherPowerLogSum` is `H(M) = ∑_{p prime, h ≥ 2, p^h ≤ M} log p`;
  `kzHigherPowerLogSum_le_hanson`: `H(M) ≤ log 3 {√M + (log_2 M) M^{1/3}}` from [Hanson, Theorem 1];
  `kzHigherPowerLogSum_lt_eleven_sqrt`: `H(12n + 5) < 11 √n` for `n ≥ 250000`;
* `kz_retained_le_small`, `kz_retained_le_large`: the retained intervals contribute
  `Q_6 n + 5/4 + (5/6) ∑_{ℓ=1}^{6} 1/ℓ` (the printed constant shifts, `< 5`, `shift_total_lt_five`)
  plus `61 √n` for `n ≤ 10^13` (from [BMOR, Theorem 1.9]), respectively `21n/1000` for
  `n > 10^13` (from [BMOR, Corollary 1.7], with `log x > 27`), where
  `Q_6 = 180556377763/157066509600 < 23/20`; the per-`ℓ` shift is `≤ 5/(6ℓ)` (`kz_term_le`) and
  the two intervals beyond `n` shift by at most `5/4` (`kz_tail_le`);
* `kz_level_one_small`, `kz_level_one_large`: the inequality (B.7),
  `T_0(n) < (23/20 + log 3/7) n + 12 + {61 √n; 21n/1000}`, where the small primes `5, 7, 11`
  contribute `log 385 < 6` (`log_threeEightyFive_lt_six`), so with the shifts the constant is
  `< 12`;
* `kz_upper_small`, `kz_upper_large`: the inequality (B.8),
  `S_n + log g_n < (23/20 + log 3/7) n + 12 + {95 √n; 21n/1000 + 33 √n}`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Finset

/-- The main coefficient `(1/t - 6/(6t+1) + 2/(2t+1) - 2/(t+1) + 3/(3t+1))/2` of the three
retained intervals with `ℓ = t`. -/
noncomputable def kzMainCoeff (t : ℝ) : ℝ :=
  (1 / t - 6 / (6 * t + 1) + 2 / (2 * t + 1) - 2 / (t + 1) + 3 / (3 * t + 1)) / 2

theorem kzMainCoeff_eq (t : ℝ) : kzMainCoeff t =
    (1 / t - 6 / (6 * t + 1) + 2 / (2 * t + 1) - 2 / (t + 1) + 3 / (3 * t + 1)) / 2 := (rfl)

/-- `√x ≤ s √y` when `x ≤ s² y`. -/
theorem sqrt_le_mul_sqrt {x s y : ℝ} (hs : 0 ≤ s) (h : x ≤ s ^ 2 * y) : √x ≤ s * √y := by
  calc √x ≤ √(s ^ 2 * y) := Real.sqrt_le_sqrt h
    _ = s * √y := by rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs]

/-- The three retained intervals with `ℓ = t`, for any `F` bounded by `(B - A)/2 + G` on
`n/7 ≤ A ≤ B ≤ n/t`. -/
theorem kz_term_le {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {n : ℕ}
    (hn : 250000 ≤ n) {t : ℝ} (ht1 : 1 ≤ t) (ht6 : t ≤ 6) (F : ℝ → ℝ → ℝ) (G : ℝ)
    (hF : ∀ A B : ℝ, (n : ℝ) / 7 ≤ A → A ≤ B → B ≤ n / t → F A B ≤ (B - A) / 2 + G) :
    F (kzEndA l μ n t) (n / t) + F (n / (t + 1)) (kzEndC μ n t) +
        F (n / (t + 1)) (kzEndD l n t) ≤ n * kzMainCoeff t + 5 / (6 * t) + 3 * G := by
  obtain ⟨v1, v2, -, v4, v5, -, v7, -⟩ := kz_endpoints_valid hl hμ hn ht1 ht6
  have hN : (250000 : ℝ) ≤ n := by exact_mod_cast hn
  have hl' : -1 ≤ (l : ℝ) ∧ (l : ℝ) ≤ 1 := by rcases hl with rfl | rfl <;> norm_num
  have hμ' : -1 ≤ (μ : ℝ) ∧ (μ : ℝ) ≤ 1 := by rcases hμ with rfl | rfl <;> norm_num
  have ht0 : (0 : ℝ) < t := by linarith
  have q4 := mul_le_mul_of_nonneg_right hμ'.2 ht0.le
  have q5 := mul_le_mul_of_nonneg_right hl'.2 ht0.le
  have hC : kzEndC μ n t ≤ n / t := by
    rw [kzEndC_eq, div_le_div_iff₀ (by linarith) ht0]
    linarith
  have hD : kzEndD l n t ≤ n / t := by
    rw [kzEndD_eq, div_le_div_iff₀ (by linarith) ht0]
    linarith
  have h1 := hF _ _ v1 v2 le_rfl
  have h2 := hF _ _ v4 v5 hC
  have h3 := hF _ _ v4 v7 hD
  have e : (n / t - kzEndA l μ n t) / 2 + (kzEndC μ n t - n / (t + 1)) / 2 +
      (kzEndD l n t - n / (t + 1)) / 2 = n * kzMainCoeff t +
        (-(2 * l + 3 * μ) / (6 * t + 1) + μ / (2 * t + 1) + l / (3 * t + 1)) / 2 := by
    rw [kzEndA_eq, kzEndC_eq, kzEndD_eq, kzMainCoeff_eq]
    ring
  have c1 : -(2 * (l : ℝ) + 3 * μ) / (6 * t + 1) ≤ 5 / (6 * t) := by
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right (show -(2 * (l : ℝ) + 3 * μ) ≤ 5 by linarith) ht0.le]
  have c2 : (μ : ℝ) / (2 * t + 1) ≤ 1 / (2 * t) := by
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hμ'.2 ht0.le]
  have c3 : (l : ℝ) / (3 * t + 1) ≤ 1 / (3 * t) := by
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hl'.2 ht0.le]
  have c4 : (5 / (6 * t) + 1 / (2 * t) + 1 / (3 * t)) / 2 = 5 / (6 * t) := by
    field_simp
    ring
  linarith

/-- The two retained intervals beyond `n`. -/
theorem kz_tail_le {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {n : ℕ}
    (hn : 250000 ≤ n) (F : ℝ → ℝ → ℝ) (G : ℝ)
    (hF : ∀ A B : ℝ, (n : ℝ) / 7 ≤ A → A ≤ B → B ≤ 2 * n + 1 → F A B ≤ (B - A) / 2 + G) :
    F n ((3 * n + l) / 2) + F ((6 * n + (2 * l + 3 * μ)) / 5) (2 * n + μ) ≤
      n * (13 / 20) + 5 / 4 + 2 * G := by
  have hN : (250000 : ℝ) ≤ n := by exact_mod_cast hn
  have hl' : -1 ≤ (l : ℝ) ∧ (l : ℝ) ≤ 1 := by rcases hl with rfl | rfl <;> norm_num
  have hμ' : -1 ≤ (μ : ℝ) ∧ (μ : ℝ) ≤ 1 := by rcases hμ with rfl | rfl <;> norm_num
  have h1 := hF n ((3 * n + l) / 2) (by linarith)
    (by rw [le_div_iff₀ (by norm_num)]; linarith) (by rw [div_le_iff₀ (by norm_num)]; linarith)
  have h2 := hF ((6 * n + (2 * l + 3 * μ)) / 5) (2 * n + μ)
    (by rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith)
    (by rw [div_le_iff₀ (by norm_num)]; linarith) (by linarith)
  linarith

/-- The sum of the main coefficients: `∑_{ℓ=1}^{6} kzMainCoeff ℓ = Q_6 - 13/20`. -/
theorem sum_kzMainCoeff :
    ∑ k ∈ range 6, kzMainCoeff ((k : ℝ) + 1) = 78463146523 / 157066509600 := by
  simp only [sum_range_succ, sum_range_zero, kzMainCoeff_eq]
  push_cast
  norm_num

theorem sum_sqrt_coeff :
    ∑ k ∈ range 6, (3 / 10 + 5 / (6 * ((k : ℝ) + 1))) = 461 / 120 := by
  simp only [sum_range_succ, sum_range_zero]
  push_cast
  norm_num

/-- `√n ≤ n / 500` for `n ≥ 250000`. -/
theorem sqrt_le_div_five_hundred {x : ℝ} (hx : 250000 ≤ x) : √x ≤ x / 500 := by
  have h0 : (0 : ℝ) ≤ x := by linarith
  have hs := Real.sq_sqrt h0
  have h5 : (500 : ℝ) ≤ √x := by
    rw [Real.le_sqrt (by norm_num) h0]; linarith
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

theorem gcd_kz_class {l c : ℤ} (hl : l = 1 ∨ l = -1) (hc : c = 3 + 2 * l ∨ c = 3 - 2 * l) :
    Int.gcd c 6 = 1 := by
  rcases hl with rfl | rfl <;> rcases hc with rfl | rfl <;> decide


/-! ### The higher prime powers `H(M)` -/

/-- `H(M) = ∑_{p prime, h ≥ 2, p^h ≤ M} log p`. -/
noncomputable def kzHigherPowerLogSum (M : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 M).filter Nat.Prime, ∑ _h ∈ (Icc 2 M).filter (fun h => p ^ h ≤ M), Real.log p

theorem kzHigherPowerLogSum_eq (M : ℕ) : kzHigherPowerLogSum M =
    ∑ p ∈ (Icc 1 M).filter Nat.Prime, ((Nat.log p M - 1 : ℕ) : ℝ) * Real.log p := by
  unfold kzHigherPowerLogSum
  refine sum_congr rfl fun p hp => ?_
  have hpr := (mem_filter.mp hp).2
  have hM : M ≠ 0 := by
    have := (mem_Icc.mp (mem_filter.mp hp).1).2
    have := hpr.one_lt
    omega
  have e : (Icc 2 M).filter (fun h => p ^ h ≤ M) = Icc 2 (Nat.log p M) := by
    ext h
    simp only [mem_filter, mem_Icc]
    have hl := Nat.log_le_self p M
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, (Nat.le_log_iff_pow_le hpr.one_lt hM).mpr h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, by omega⟩, (Nat.le_log_iff_pow_le hpr.one_lt hM).mp h2⟩
  rw [e, sum_const, Nat.card_Icc, nsmul_eq_mul]
  congr 2

/-- **Hanson's estimate for `H(M)`**: `H(M) ≤ log 3 · {√M + (⌊log_2 M⌋ - 2) ⌊M^{1/3}⌋}`
(the manuscript's `H(M) ≤ log 3 {√M + (log_2 M) M^{1/3}}`), from [Hanson, Theorem 1]. -/
theorem kzHigherPowerLogSum_le_hanson (hH : HansonLcmBound) {M : ℕ} (hM : 1 ≤ M) :
    kzHigherPowerLogSum M ≤ Real.log 3 * (√(M : ℝ) + ((Nat.log 2 M - 2 : ℕ) : ℝ) *
      ((Nat.findGreatest (fun c => c ^ 3 ≤ M) M : ℕ) : ℝ)) := by
  classical
  rw [kzHigherPowerLogSum_eq]
  set P := (Icc 1 M).filter Nat.Prime with hPdef
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (mem_filter.mp hp).2
  have hM0 : M ≠ 0 := by omega
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hN3 : (Nat.findGreatest (fun c => c ^ 3 ≤ M) M) ^ 3 ≤ M :=
    Nat.findGreatest_spec (P := fun c => c ^ 3 ≤ M) (m := 1) hM (by simp; omega)
  have hN3pos : 1 ≤ Nat.findGreatest (fun c => c ^ 3 ≤ M) M :=
    Nat.le_findGreatest (P := fun c => c ^ 3 ≤ M) (m := 1) hM (by simp; omega)
  have hN2pos : 1 ≤ Nat.sqrt M := Nat.le_sqrt.mpr (by omega)
  have hterm : ∀ p ∈ P, Nat.log p M - 1 ≤ (if p ^ 2 ≤ M then 1 else 0) +
      (Nat.log 2 M - 2) * (if p ^ 3 ≤ M then 1 else 0) := by
    intro p hp
    have hpr := hP p hp
    have hle2 : Nat.log p M ≤ Nat.log 2 M := Nat.log_anti_left (by norm_num) hpr.two_le
    by_cases h3 : p ^ 3 ≤ M
    · have h2 : p ^ 2 ≤ M := le_trans (Nat.pow_le_pow_right hpr.pos (by norm_num)) h3
      have := Nat.le_log_of_pow_le hpr.one_lt h3
      simp only [h2, h3, ↓reduceIte]
      omega
    · simp only [h3, ↓reduceIte, mul_zero, add_zero]
      have hlt3 : Nat.log p M < 3 := Nat.log_lt_of_lt_pow hM0 (by omega)
      by_cases h2 : p ^ 2 ≤ M
      · simp only [h2, ↓reduceIte]; omega
      · simp only [h2, ↓reduceIte]
        have : Nat.log p M < 2 := Nat.log_lt_of_lt_pow hM0 (by omega)
        omega
  have hsum1 := sum_mul_log_le_of_pow_le hH P hP
    (fun p => if p ^ 2 ≤ M then 1 else 0) hN2pos (fun p hp => by
      split_ifs with h
      · rw [pow_one]; exact Nat.le_sqrt.mpr (by nlinarith)
      · rw [pow_zero]; exact hN2pos)
  have hsum2 := sum_mul_log_le_of_pow_le hH P hP
    (fun p => if p ^ 3 ≤ M then 1 else 0) hN3pos (fun p hp => by
      split_ifs with h
      · rw [pow_one]
        have hp1 : p ≤ M := le_trans (Nat.le_self_pow (by norm_num) p) h
        exact Nat.le_findGreatest (P := fun c => c ^ 3 ≤ M) hp1 h
      · rw [pow_zero]; exact hN3pos)
  have hmain : ∑ p ∈ P, ((Nat.log p M - 1 : ℕ) : ℝ) * Real.log p ≤
      ∑ p ∈ P, ((if p ^ 2 ≤ M then 1 else 0 : ℕ) : ℝ) * Real.log p +
        ((Nat.log 2 M - 2 : ℕ) : ℝ) *
          ∑ p ∈ P, ((if p ^ 3 ≤ M then 1 else 0 : ℕ) : ℝ) * Real.log p := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun p hp => ?_
    have h := hterm p hp
    have h' : ((Nat.log p M - 1 : ℕ) : ℝ) ≤ ((if p ^ 2 ≤ M then 1 else 0 : ℕ) : ℝ) +
        ((Nat.log 2 M - 2 : ℕ) : ℝ) * ((if p ^ 3 ≤ M then 1 else 0 : ℕ) : ℝ) := by
      exact_mod_cast h
    have hlp := Real.log_natCast_nonneg p
    nlinarith
  have hs2 : ((Nat.sqrt M : ℕ) : ℝ) ≤ √(M : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact_mod_cast Nat.sqrt_le' M
  have hK0 : (0 : ℝ) ≤ ((Nat.log 2 M - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  calc _ ≤ _ := hmain
    _ ≤ ((Nat.sqrt M : ℕ) : ℝ) * Real.log 3 + ((Nat.log 2 M - 2 : ℕ) : ℝ) *
          (((Nat.findGreatest (fun c => c ^ 3 ≤ M) M : ℕ) : ℝ) * Real.log 3) :=
        add_le_add hsum1 (mul_le_mul_of_nonneg_left hsum2 hK0)
    _ = Real.log 3 * (((Nat.sqrt M : ℕ) : ℝ) + ((Nat.log 2 M - 2 : ℕ) : ℝ) *
          ((Nat.findGreatest (fun c => c ^ 3 ≤ M) M : ℕ) : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hs2 le_rfl) hl3.le

/-- `H(12n + 5) < 11 √n` for `n ≥ 250000`: with `r = n^{1/6}` one has `M ≤ 12.1 r^6`,
`√M ≤ 3.5 r³`, `⌊M^{1/3}⌋ ≤ 2.3 r²`, and `(log 12.1 + 6 log r)/ r` is largest at `r = 7.9` where
it is below `15/7.9`; hence `H(M) ≤ 1.1 (3.5 + 2.3 · 15/(7.9 · 0.69)) √n < 11 √n`. -/
theorem kzHigherPowerLogSum_lt_eleven_sqrt (hH : HansonLcmBound) {n : ℕ} (hn : 250000 ≤ n) :
    kzHigherPowerLogSum (12 * n + 5) < 11 * √(n : ℝ) := by
  have hnR : (250000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set M := 12 * n + 5 with hMdef
  have hM1 : 1 ≤ M := by omega
  have h1 := kzHigherPowerLogSum_le_hanson hH hM1
  set r : ℝ := (n : ℝ) ^ ((1 : ℝ) / 6) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hn0 _
  have hr6 : r ^ 6 = n := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have hr79 : 7.9 < r := by
    by_contra h
    push Not at h
    have := pow_le_pow_left₀ hr0.le h 6
    rw [hr6] at this
    norm_num at this
    linarith
  have hsq : √(n : ℝ) = r ^ 3 := by
    rw [← hr6, show r ^ 6 = (r ^ 3) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hMR : (M : ℝ) ≤ 12.1 * r ^ 6 := by
    rw [hr6, hMdef]
    push_cast
    linarith
  have hr3 : 0 < r ^ 3 := by positivity
  have hs1 : √(M : ℝ) ≤ 3.5 * r ^ 3 := by
    have h12 : (M : ℝ) ≤ (3.5 * r ^ 3) ^ 2 := by
      have h6 : (0 : ℝ) < r ^ 6 := by positivity
      have e : (3.5 * r ^ 3) ^ 2 = 12.25 * r ^ 6 := by ring
      rw [e]; linarith
    have := Real.sqrt_le_sqrt h12
    rwa [Real.sqrt_sq (by positivity)] at this
  set N3 := Nat.findGreatest (fun c => c ^ 3 ≤ M) M with hN3def
  have hN3 : N3 ^ 3 ≤ M :=
    Nat.findGreatest_spec (P := fun c => c ^ 3 ≤ M) (m := 1) hM1 (by simp; omega)
  have hN3r : (N3 : ℝ) ≤ 2.3 * r ^ 2 := by
    have h3 : (N3 : ℝ) ^ 3 ≤ (2.3 * r ^ 2) ^ 3 := by
      have : (N3 : ℝ) ^ 3 ≤ M := by exact_mod_cast hN3
      have h6 : (0 : ℝ) < r ^ 6 := by positivity
      calc (N3 : ℝ) ^ 3 ≤ (M : ℝ) := this
        _ ≤ 12.1 * r ^ 6 := hMR
        _ ≤ (2.3 * r ^ 2) ^ 3 := by
          have e : (2.3 * r ^ 2) ^ 3 = 12.167 * r ^ 6 := by ring
          rw [e]; linarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h3
  set K : ℝ := ((Nat.log 2 M - 2 : ℕ) : ℝ) with hKdef
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have hl2 : (0.69 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hKlog : K * Real.log 2 ≤ Real.log 12.1 + 6 * Real.log r := by
    have h2 := natLog_mul_log_le_log (b := 2) le_rfl (m := M) (by omega)
    have e2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [e2] at h2
    have hle : K ≤ (Nat.log 2 M : ℝ) := by
      rw [hKdef]; exact_mod_cast Nat.sub_le _ _
    have hlogM : Real.log (M : ℝ) ≤ Real.log (12.1 * r ^ 6) :=
      Real.log_le_log (by positivity) hMR
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlogM
    push_cast at hlogM
    have hl2' : 0 ≤ Real.log 2 := by linarith
    have := mul_le_mul_of_nonneg_right hle hl2'
    linarith
  have hC : Real.log 12.1 + 6 * Real.log 7.9 < 15 := by
    have : Real.log (12.1 * 7.9 ^ 6) < 15 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      linarith [exp_fifteen_gt, (by norm_num : (12.1 : ℝ) * 7.9 ^ 6 < 3000000)]
    rwa [Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at this
  have hlr := kz_log_le_log_add_div_sub_one (x := r) (y := 7.9) hr0 (by norm_num)
  have hK' : K * 0.69 ≤ 15 * r / 7.9 := by
    have h1' : K * 0.69 ≤ K * Real.log 2 := mul_le_mul_of_nonneg_left hl2 hK0
    have h2' : 6 * (r / 7.9) = 6 * r / 7.9 := by ring
    have h3' : 15 * r / 7.9 = 9 * (r / 7.9) + 6 * r / 7.9 := by ring
    have h4' : 1 ≤ r / 7.9 := by rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  have hKN : K * N3 ≤ 6.33 * r ^ 3 := by
    have h1' : K * N3 ≤ K * (2.3 * r ^ 2) := mul_le_mul_of_nonneg_left hN3r hK0
    have h2' : K * 0.69 * (2.3 * r ^ 2) ≤ 15 * r / 7.9 * (2.3 * r ^ 2) :=
      mul_le_mul_of_nonneg_right hK' (by positivity)
    have h3' : 15 * r / 7.9 * (2.3 * r ^ 2) = (345 / 79) * r ^ 3 := by ring
    have h4' : K * 0.69 * (2.3 * r ^ 2) = 1.587 * (K * r ^ 2) := by ring
    have h5' : K * (2.3 * r ^ 2) = 2.3 * (K * r ^ 2) := by ring
    linarith
  have hl3 : Real.log 3 < 1.1 := lt_trans Real.log_three_lt_d9 (by norm_num)
  have hl30 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hX : √(M : ℝ) + K * N3 ≤ 9.9 * r ^ 3 := by linarith
  calc kzHigherPowerLogSum (12 * n + 5) ≤ Real.log 3 * (√(M : ℝ) + K * N3) := h1
    _ ≤ Real.log 3 * (9.9 * r ^ 3) := mul_le_mul_of_nonneg_left hX hl30.le
    _ < 11 * r ^ 3 := by
        have := mul_le_mul_of_nonneg_right hl3.le (show (0 : ℝ) ≤ 9.9 * r ^ 3 by positivity)
        linarith
    _ = 11 * √(n : ℝ) := by rw [hsq]

/-- The terms of `∑_{5 ≤ p ≤ M} (⌊log_p M⌋ - 1) log p` form a part of `H(M)`. -/
theorem sum_natLog_sub_one_le_kzHigherPowerLogSum (M : ℕ) :
    ∑ p ∈ (Icc 5 M).filter Nat.Prime, ((Nat.log p M - 1 : ℕ) : ℝ) * Real.log p ≤
      kzHigherPowerLogSum M := by
  rw [kzHigherPowerLogSum_eq]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => ?_
  · intro p hp
    simp only [mem_filter, mem_Icc] at hp ⊢
    exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

/-! ### The retained intervals -/

/-- `Q_6 = 13/20 + ∑_{ℓ=1}^{6} kzMainCoeff ℓ = 180556377763/157066509600 < 23/20`. -/
theorem Q6_eq : (13 / 20 : ℝ) + 78463146523 / 157066509600 = 180556377763 / 157066509600 := by
  norm_num

theorem Q6_lt : (180556377763 / 157066509600 : ℝ) < 23 / 20 := by norm_num

/-- **The retained intervals for `250000 ≤ n ≤ 10^13`** (with [BMOR, Theorem 1.9]): their total
contribution is at most `Q_6 n + 21/2 + 61 √n`. -/
theorem kz_retained_le_small (hS : BMORThetaSmallBound) {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : 250000 ≤ n) (hn' : n ≤ 10 ^ 13) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P, kzRetainedInd l μ n p * Real.log p ≤
      n * (180556377763 / 157066509600) + (5 / 4 + 5 / 6 * (49 / 20)) + 61 * √(n : ℝ) := by
  have hN : (250000 : ℝ) ≤ n := by exact_mod_cast hn
  have hN' : (n : ℝ) ≤ 10 ^ 13 := by exact_mod_cast hn'
  have hn0 : (0 : ℝ) ≤ n := by linarith
  set F : ℝ → ℝ → ℝ := fun A B => (B - A) / 2 + 2.072 * (√A + √B) with hFdef
  have hθ : ∀ (A B : ℝ) (c : ℤ), (c = 3 + 2 * l ∨ c = 3 - 2 * l) → (n : ℝ) / 7 ≤ A → A ≤ B →
      B ≤ 2 * n + 1 → chebyshevThetaAP B 6 c - chebyshevThetaAP A 6 c ≤ F A B :=
    fun A B c hc h1 h2 h3 => chebyshevThetaAP_six_sub_le_small hS (gcd_kz_class hl hc)
      (by linarith) h2 (by linarith)
  have hU := sum_kzRetainedInd_mul_log_le hl hμ hn P hP F hθ
  have hsq := Real.sqrt_nonneg (n : ℝ)
  have hterm : ∀ k ∈ range 6, F (kzEndA l μ n (k + 1)) (n / (k + 1)) +
      F (n / (k + 1 + 1)) (kzEndC μ n (k + 1)) + F (n / (k + 1 + 1)) (kzEndD l n (k + 1)) ≤
      n * kzMainCoeff ((k : ℝ) + 1) + 5 / (6 * ((k : ℝ) + 1)) +
        3 * (2 * 2.072 * ((3 / 10 + 5 / (6 * ((k : ℝ) + 1))) * √(n : ℝ))) := by
    intro k hk
    have hk6 : (k : ℝ) ≤ 5 := by
      have := mem_range.mp hk
      exact_mod_cast (show k ≤ 5 by omega)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    refine kz_term_le hl hμ hn (by linarith) (by linarith) F _ fun A B hA hAB hB => ?_
    set t : ℝ := (k : ℝ) + 1 with ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hs0 : (0 : ℝ) ≤ 3 / 10 + 5 / (6 * t) := by positivity
    have hst : n / t ≤ (3 / 10 + 5 / (6 * t)) ^ 2 * n := by
      have e : (3 / 10 + 5 / (6 * t)) ^ 2 * t - 1 = (3 / 10 * t - 5 / 6) ^ 2 / t := by
        field_simp
        ring
      have h1 : 1 ≤ (3 / 10 + 5 / (6 * t)) ^ 2 * t := by
        have : 0 ≤ (3 / 10 * t - 5 / 6) ^ 2 / t := by positivity
        linarith
      rw [div_le_iff₀ ht0]
      nlinarith
    have hA' := sqrt_le_mul_sqrt hs0 (show A ≤ (3 / 10 + 5 / (6 * t)) ^ 2 * n by linarith)
    have hB' := sqrt_le_mul_sqrt hs0 (show B ≤ (3 / 10 + 5 / (6 * t)) ^ 2 * n by linarith)
    simp only [hFdef]
    linarith
  have hS1 := sum_le_sum hterm
  have e1 : ∑ k ∈ range 6, (n * kzMainCoeff ((k : ℝ) + 1) + 5 / (6 * ((k : ℝ) + 1)) +
      3 * (2 * 2.072 * ((3 / 10 + 5 / (6 * ((k : ℝ) + 1))) * √(n : ℝ)))) =
      n * (78463146523 / 157066509600) + 5 / 6 * (49 / 20) +
        3 * (2 * 2.072 * (461 / 120 * √(n : ℝ))) := by
    rw [← sum_kzMainCoeff, ← sum_sqrt_coeff]
    simp only [sum_range_succ, sum_range_zero]
    ring
  have hT := kz_tail_le hl hμ hn F (2 * 2.072 * (1.4143 * √(n : ℝ))) fun A B hA hAB hB => by
    have hA' := sqrt_le_mul_sqrt (show (0 : ℝ) ≤ 1.4143 by norm_num)
      (show A ≤ 1.4143 ^ 2 * n by nlinarith)
    have hB' := sqrt_le_mul_sqrt (show (0 : ℝ) ≤ 1.4143 by norm_num)
      (show B ≤ 1.4143 ^ 2 * n by nlinarith)
    simp only [hFdef]
    linarith
  linarith

theorem exp_twentyseven_lt : Real.exp 27 < 10 ^ 12 := by
  have h : Real.exp 1 ^ 27 = Real.exp 27 := by rw [Real.exp_one_pow]; norm_num
  rw [← h]
  calc Real.exp 1 ^ 27 < (2.7182818286 : ℝ) ^ 27 :=
        pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
    _ < 10 ^ 12 := by norm_num

/-- `log x ≥ 27` for `x ≥ 10^12`. -/
theorem twentyseven_le_log {x : ℝ} (hx : 10 ^ 12 ≤ x) : 27 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [exp_twentyseven_lt]

/-- [BMOR, Corollary 1.7] for an interval, as in the manuscript with `log x > 27` for
`x ≥ n/7 ≥ 10^13/7`: for `10^12 ≤ A ≤ B` and `gcd(c, 6) = 1`,
`θ(B; 6, c) - θ(A; 6, c) ≤ (B - A)/2 + (0.024/27)(A + B)`. -/
theorem chebyshevThetaAP_six_sub_le_large27 (hT : BMORThetaBound) {c : ℤ}
    (hc : Int.gcd c 6 = 1) {A B : ℝ} (hA : 10 ^ 12 ≤ A) (hAB : A ≤ B) :
    chebyshevThetaAP B 6 c - chebyshevThetaAP A 6 c ≤
      (B - A) / 2 + 0.024 / 27 * (A + B) := by
  have h6 : ((Nat.totient 6 : ℕ) : ℝ) = 2 := by rw [totient_six]; norm_num
  have h1 := hT 6 c (by norm_num) (by norm_num) hc B (by linarith)
  have h2 := hT 6 c (by norm_num) (by norm_num) hc A (by linarith)
  rw [h6, abs_lt] at h1 h2
  have hlA := twentyseven_le_log hA
  have hlB := twentyseven_le_log (le_trans hA hAB)
  have eA : 0.024 * A / Real.log A ≤ 0.024 / 27 * A := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have eB : 0.024 * B / Real.log B ≤ 0.024 / 27 * B := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- **The retained intervals for `n ≥ 10^13`** (with [BMOR, Corollary 1.7]): their total
contribution is at most `Q_6 n + 21/2 + (21/1000) n`. -/
theorem kz_retained_le_large (hT : BMORThetaBound) {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : 10 ^ 13 ≤ n) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P, kzRetainedInd l μ n p * Real.log p ≤
      n * (180556377763 / 157066509600) + (5 / 4 + 5 / 6 * (49 / 20)) + 21 / 1000 * n := by
  have hn1 : 250000 ≤ n := le_trans (by norm_num) hn
  have hN : (10 ^ 13 : ℝ) ≤ n := by exact_mod_cast hn
  have hN1 : (250000 : ℝ) ≤ n := by linarith
  set F : ℝ → ℝ → ℝ := fun A B => (B - A) / 2 + 0.024 / 27 * (A + B) with hFdef
  have hθ : ∀ (A B : ℝ) (c : ℤ), (c = 3 + 2 * l ∨ c = 3 - 2 * l) → (n : ℝ) / 7 ≤ A → A ≤ B →
      B ≤ 2 * n + 1 → chebyshevThetaAP B 6 c - chebyshevThetaAP A 6 c ≤ F A B :=
    fun A B c hc h1 h2 h3 => chebyshevThetaAP_six_sub_le_large27 hT (gcd_kz_class hl hc)
      (by linarith) h2
  have hU := sum_kzRetainedInd_mul_log_le hl hμ hn1 P hP F hθ
  have hterm : ∀ k ∈ range 6, F (kzEndA l μ n (k + 1)) (n / (k + 1)) +
      F (n / (k + 1 + 1)) (kzEndC μ n (k + 1)) + F (n / (k + 1 + 1)) (kzEndD l n (k + 1)) ≤
      n * kzMainCoeff ((k : ℝ) + 1) + 5 / (6 * ((k : ℝ) + 1)) +
        3 * (0.024 / 27 * (2 * (n / ((k : ℝ) + 1)))) := by
    intro k hk
    have hk6 : (k : ℝ) ≤ 5 := by
      have := mem_range.mp hk
      exact_mod_cast (show k ≤ 5 by omega)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    refine kz_term_le hl hμ hn1 (by linarith) (by linarith) F _ fun A B hA hAB hB => ?_
    simp only [hFdef]
    linarith
  have hS1 := sum_le_sum hterm
  have e1 : ∑ k ∈ range 6, (n * kzMainCoeff ((k : ℝ) + 1) + 5 / (6 * ((k : ℝ) + 1)) +
      3 * (0.024 / 27 * (2 * (n / ((k : ℝ) + 1))))) =
      n * (78463146523 / 157066509600) + 5 / 6 * (49 / 20) +
        0.024 / 27 * (6 * (49 / 20) * n) := by
    rw [← sum_kzMainCoeff]
    simp only [sum_range_succ, sum_range_zero]
    push_cast
    ring
  have hTl := kz_tail_le hl hμ hn1 F (0.024 / 27 * (2 * (2 * n + 1))) fun A B hA hAB hB => by
    simp only [hFdef]
    linarith
  linarith

/-- The small primes `5, 7, 11` contribute at most `log 385 < 6`. -/
theorem log_threeEightyFive_lt_six : Real.log 385 < 6 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h : Real.exp 1 ^ 6 = Real.exp 6 := by rw [Real.exp_one_pow]; norm_num
  rw [← h]
  calc (385 : ℝ) < (2.7182818283 : ℝ) ^ 6 := by norm_num
    _ < Real.exp 1 ^ 6 := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)

/-- The printed constant shifts: `5/4 + (5/6) ∑_{ℓ=1}^{6} 1/ℓ < 5`; with `log 385 < 6` this is
less than `12`. -/
theorem shift_total_lt_five : (5 / 4 + 5 / 6 * (49 / 20) : ℝ) < 5 := by norm_num

/-- `⌊n/7⌋ log 3 ≤ (n/7) log 3`. -/
theorem natDiv_seven_mul_log_le (n : ℕ) :
    ((n / 7 : ℕ) : ℝ) * Real.log 3 ≤ (n : ℝ) / 7 * Real.log 3 := by
  have := Nat.cast_div_le (m := n) (n := 7) (α := ℝ)
  rw [Nat.cast_ofNat] at this
  exact mul_le_mul_of_nonneg_right this (Real.log_nonneg (by norm_num))

/-- **(B.7), level one, `250000 ≤ n ≤ 10^13`**:
`log 385 + ⌊n/7⌋ log 3 + (retained) < (23/20 + log 3/7) n + 12 + 61 √n`. -/
theorem kz_level_one_small (hS : BMORThetaSmallBound) {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : 250000 ≤ n) (hn' : n ≤ 10 ^ 13) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    Real.log 385 + ((n / 7 : ℕ) : ℝ) * Real.log 3 +
        ∑ p ∈ P, kzRetainedInd l μ n p * Real.log p <
      (23 / 20 + Real.log 3 / 7) * n + 12 + 61 * √(n : ℝ) := by
  have h1 := kz_retained_le_small hS hl hμ hn hn' P hP
  have h2 := natDiv_seven_mul_log_le n
  have hN : (250000 : ℝ) ≤ n := by exact_mod_cast hn
  have h3 := Q6_lt
  have h4 := log_threeEightyFive_lt_six
  have h5 := shift_total_lt_five
  nlinarith

/-- **(B.7), level one, `n > 10^13`**:
`log 385 + ⌊n/7⌋ log 3 + (retained) < (23/20 + log 3/7) n + 12 + (21/1000) n`. -/
theorem kz_level_one_large (hT : BMORThetaBound) {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : 10 ^ 13 ≤ n) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    Real.log 385 + ((n / 7 : ℕ) : ℝ) * Real.log 3 +
        ∑ p ∈ P, kzRetainedInd l μ n p * Real.log p <
      (23 / 20 + Real.log 3 / 7) * n + 12 + 21 / 1000 * n := by
  have h1 := kz_retained_le_large hT hl hμ hn P hP
  have h2 := natDiv_seven_mul_log_le n
  have hN : (10 ^ 13 : ℝ) ≤ n := by exact_mod_cast hn
  have h3 := Q6_lt
  have h4 := log_threeEightyFive_lt_six
  have h5 := shift_total_lt_five
  nlinarith

/-- **(B.8), `250000 ≤ n ≤ 10^13`**:
`S_n + log g_n < (23/20 + log 3/7) n + 12 + 95 √n`. -/
theorem kz_upper_small (hH : HansonLcmBound) (hS : BMORThetaSmallBound) {l μ : ℤ}
    (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : 250000 ≤ n) (hn' : n ≤ 10 ^ 13) :
    kzGoodPrimeSum l μ n + Real.log (kzContent l μ n) <
      (23 / 20 + Real.log 3 / 7) * n + 12 + 95 * √(n : ℝ) := by
  have h1 := kz_content_goodPrime_le hH hl hμ hn
  have h2 := kz_level_one_small hS hl hμ hn hn' ((Icc 5 (12 * n + 5)).filter Nat.Prime)
    (fun p hp => (mem_filter.mp hp).2)
  have h3 := sum_natLog_sub_one_le_kzHigherPowerLogSum (12 * n + 5)
  have h4 := kzHigherPowerLogSum_lt_eleven_sqrt hH hn
  have hsq := Real.sqrt_nonneg (n : ℝ)
  linarith

/-- **(B.8), `n > 10^13`**:
`S_n + log g_n < (23/20 + log 3/7) n + 12 + (21/1000) n + 33 √n`. -/
theorem kz_upper_large (hH : HansonLcmBound) (hT : BMORThetaBound) {l μ : ℤ}
    (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : 10 ^ 13 ≤ n) :
    kzGoodPrimeSum l μ n + Real.log (kzContent l μ n) <
      (23 / 20 + Real.log 3 / 7) * n + 12 + (21 / 1000 * n + 33 * √(n : ℝ)) := by
  have hn1 : 250000 ≤ n := le_trans (by norm_num) hn
  have h1 := kz_content_goodPrime_le hH hl hμ hn1
  have h2 := kz_level_one_large hT hl hμ hn ((Icc 5 (12 * n + 5)).filter Nat.Prime)
    (fun p hp => (mem_filter.mp hp).2)
  have h3 := sum_natLog_sub_one_le_kzHigherPowerLogSum (12 * n + 5)
  have h4 := kzHigherPowerLogSum_lt_eleven_sqrt hH hn1
  linarith

end ArithmeticOfJacobiPolynomials
