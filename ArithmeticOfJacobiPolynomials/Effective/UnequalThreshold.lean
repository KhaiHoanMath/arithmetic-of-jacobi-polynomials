/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.UnequalIrreducibility
public import ArithmeticOfJacobiPolynomials.Analysis.SymmetricRanges

/-!
# An explicit computable threshold for Theorem 1.3 (irreducibility)

Theorem 1.3 asserts an *effectively computable* integer `N(a,b)`
such that `P_n^{(a,b)}` is irreducible for `n ≥ N(a,b)`. The proof of the irreducibility
assertion (§3.1) makes every constant explicit: a root bound for `A_δ`, bounds
`|A_δ(m)| ≤ C (m+1)^{K_δ}`, `D_δ(m) ≤ 2 (m+K_δ)^{K_δ}`, `T ≤ (n+s)^s`, `B ≤ (n+a)^a`, and rational
bounds for the logarithms. We carry this out with `s = a + b`:

* `abs_centralA_eval_le`: `|A_δ(m)| ≤ (s+3)^{2s+1} (m+1)^s`, read off (3.6);
* `centralD_eval_le`: `D_δ(m) ≤ (s+2)^{s+1} (m+1)^s`, read off (3.5);
* the root bound: an integer root `m` of `A_δ` divides `A_δ(0) > 0`, so `A_δ(m) ≠ 0` for
  `m > (s+3)^{2s+1}` (`centralA_eval_ne_zero_of_lt`);
* `eight_div_asymmetricEnergyConstant_le`: `8 / c_{a,b} ≤ 8 (2s+1)^{s+1}`;
* `log 3 < 2`, `log x ≤ x - 1`, `log (4/3) > 0.2876 > 1/4`, and the elementary
  `K √(m+1) + K' < m/4` for `K, K' ≤ P` and `m ≥ (4P+2)²`.

The resulting threshold is the plain natural-number expression
`unequalThreshold a b = 2 ((48 (s+2)² + 2)² + (s+3)^{2s+1} + 2s + 10)`, a computable function.

Main result: `ArithmeticOfJacobiPolynomials.irreducible_jacobiP_of_unequalThreshold_le`,
conditional on the same
cited hypotheses as `exists_forall_irreducible_jacobiP`: `HansonLcmBound` ([Hanson, Theorem 1]),
`JacobiSimpleRealZeros` ([DLMF, §18.2(vi)]).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset Real

/-! ### The explicit threshold -/

/-- The explicit threshold in `m = ⌊n/2⌋`: `(48 (s+2)² + 2)² + (s+3)^{2s+1} + 2s + 10`,
`s = a + b`. -/
def unequalMThreshold (a b : ℕ) : ℕ :=
  (48 * (a + b + 2) ^ 2 + 2) ^ 2 + (a + b + 3) ^ (2 * (a + b) + 1) + 2 * (a + b) + 10

/-- The explicit computable threshold `N(a,b)` of Theorem 1.3 (irreducibility):
`N(a,b) = 2 ((48 (s+2)² + 2)² + (s+3)^{2s+1} + 2s + 10)`, `s = a + b`. -/
def unequalThreshold (a b : ℕ) : ℕ := 2 * unequalMThreshold a b

theorem unequalMThreshold_eq (a b : ℕ) : unequalMThreshold a b =
    (48 * (a + b + 2) ^ 2 + 2) ^ 2 + (a + b + 3) ^ (2 * (a + b) + 1) + 2 * (a + b) + 10 := (rfl)

theorem unequalThreshold_eq (a b : ℕ) : unequalThreshold a b = 2 * unequalMThreshold a b := (rfl)

theorem unequalThreshold_comm (a b : ℕ) : unequalThreshold a b = unequalThreshold b a := by
  rw [unequalThreshold_eq, unequalThreshold_eq, unequalMThreshold_eq, unequalMThreshold_eq,
    Nat.add_comm a b]

/-! ### Explicit bounds for `A_δ(m)` and `D_δ(m)` -/

theorem centralK_le_add (a b δ : ℕ) (hab : b < a) (hδ : δ ≤ 1) : centralK a b δ ≤ a + b := by
  rw [centralK_eq, centralH_eq]
  omega

/-- `|A_δ(m)| ≤ (s+3)^{2s+1} (m+1)^s`, `s = a + b`, read off the defining formula (3.6). -/
theorem abs_centralA_eval_le (a b δ m : ℕ) (hab : b < a) (hδ : δ ≤ 1) :
    |(centralA a b δ).eval (m : ℤ)| ≤
      ((a + b + 3) ^ (2 * (a + b) + 1) * (m + 1) ^ (a + b) : ℕ) := by
  have hK := centralK_eq a b δ
  have hH := centralH_eq a b δ
  have hKs := centralK_le_add a b δ hab hδ
  obtain ⟨X, hX⟩ : ∃ X, X = (a + b + 3) * (m + 1) := ⟨_, rfl⟩
  have hX0 : 0 < X := by rw [hX]; positivity
  have hmX : m ≤ X := by rw [hX]; nlinarith
  have hterm : ∀ h ∈ range (centralH a b δ + 1),
      (a - b).choose (δ + 2 * h) * m.descFactorial h *
        ∏ j ∈ Icc (b + δ + h + 1) (centralK a b δ), (m + j) ≤
          2 ^ (a + b) * X ^ centralH a b δ := by
    intro h hh
    have hh' : h ≤ centralH a b δ := Nat.lt_succ_iff.mp (mem_range.mp hh)
    calc (a - b).choose (δ + 2 * h) * m.descFactorial h *
          ∏ j ∈ Icc (b + δ + h + 1) (centralK a b δ), (m + j)
        ≤ 2 ^ (a + b) * X ^ h * X ^ (Icc (b + δ + h + 1) (centralK a b δ)).card := by
          refine Nat.mul_le_mul (Nat.mul_le_mul ?_ ?_) ?_
          · exact (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
          · exact (Nat.descFactorial_le_pow m h).trans (Nat.pow_le_pow_left hmX h)
          · refine Finset.prod_le_pow_card _ _ _ fun j hj => ?_
            obtain ⟨_, hj2⟩ := mem_Icc.mp hj
            rw [hX]
            nlinarith
      _ = 2 ^ (a + b) * X ^ centralH a b δ := by
          rw [mul_assoc, ← pow_add, Nat.card_Icc]
          congr 2
          omega
  have hprod : ∏ j ∈ Icc 1 (b + δ), (2 * m + j) ≤ X ^ (b + δ) := by
    have := Finset.prod_le_pow_card (Icc 1 (b + δ)) (fun j => 2 * m + j) X fun j hj => by
      obtain ⟨_, hj2⟩ := mem_Icc.mp hj
      rw [hX]
      nlinarith
    rwa [Nat.card_Icc, show b + δ + 1 - 1 = b + δ by omega] at this
  have hsum : |∑ h ∈ range (centralH a b δ + 1), (-1) ^ h * ((a - b).choose (δ + 2 * h) : ℚ) *
        (m.descFactorial h : ℚ) *
          ((∏ j ∈ Icc (b + δ + h + 1) (centralK a b δ), (m + j) : ℕ) : ℚ)| ≤
      (((centralH a b δ + 1) * (2 ^ (a + b) * X ^ centralH a b δ) : ℕ) : ℚ) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ h ∈ range (centralH a b δ + 1), ((2 ^ (a + b) * X ^ centralH a b δ : ℕ) : ℚ) :=
          sum_le_sum fun h hh => by
            simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
            exact_mod_cast hterm h hh
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  have hnat : X ^ (b + δ) * ((centralH a b δ + 1) * (2 ^ (a + b) * X ^ centralH a b δ)) ≤
      (a + b + 3) ^ (2 * (a + b) + 1) * (m + 1) ^ (a + b) := by
    calc X ^ (b + δ) * ((centralH a b δ + 1) * (2 ^ (a + b) * X ^ centralH a b δ))
        = (centralH a b δ + 1) * 2 ^ (a + b) * X ^ centralK a b δ := by rw [hK]; ring
      _ ≤ (a + b + 3) * (a + b + 3) ^ (a + b) * X ^ (a + b) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) _))
            (Nat.pow_le_pow_right hX0 hKs)
      _ = _ := by rw [hX, mul_pow]; ring
  have hq : |(((centralA a b δ).eval (m : ℤ) : ℤ) : ℚ)| ≤
      (((a + b + 3) ^ (2 * (a + b) + 1) * (m + 1) ^ (a + b) : ℕ) : ℚ) := by
    rw [centralA_eval, abs_mul, Nat.abs_cast]
    calc _ ≤ ((X ^ (b + δ) : ℕ) : ℚ) *
          (((centralH a b δ + 1) * (2 ^ (a + b) * X ^ centralH a b δ) : ℕ) : ℚ) :=
          mul_le_mul (by exact_mod_cast hprod) hsum (abs_nonneg _) (by positivity)
      _ ≤ _ := by exact_mod_cast hnat
  exact_mod_cast hq

/-- `D_δ(m) ≤ (s+2)^{s+1} (m+1)^s`, `s = a + b`, read off the defining formula (3.5). -/
theorem centralD_eval_le (a b δ m : ℕ) (hab : b < a) (hδ : δ ≤ 1) :
    (centralD a b δ).eval (m : ℤ) ≤ ((a + b + 2) ^ (a + b + 1) * (m + 1) ^ (a + b) : ℕ) := by
  have hKs := centralK_le_add a b δ hab hδ
  have hprod : ∏ j ∈ Icc 1 (centralK a b δ), (m + j) ≤ ((a + b + 2) * (m + 1)) ^ (a + b) := by
    refine (Finset.prod_le_pow_card _ _ ((a + b + 2) * (m + 1)) fun j hj => ?_).trans ?_
    · obtain ⟨_, hj2⟩ := mem_Icc.mp hj
      nlinarith
    · rw [Nat.card_Icc]
      exact Nat.pow_le_pow_right (by positivity) (by omega)
  have hnat : 2 ^ δ * ∏ j ∈ Icc 1 (centralK a b δ), (m + j) ≤
      (a + b + 2) ^ (a + b + 1) * (m + 1) ^ (a + b) := by
    calc 2 ^ δ * ∏ j ∈ Icc 1 (centralK a b δ), (m + j)
        ≤ (a + b + 2) * ((a + b + 2) * (m + 1)) ^ (a + b) :=
          Nat.mul_le_mul ((Nat.pow_le_pow_right (by norm_num) hδ).trans (by rw [pow_one]; omega))
            hprod
      _ = _ := by rw [mul_pow]; ring
  have hq : (((centralD a b δ).eval (m : ℤ) : ℤ) : ℚ) ≤
      (((a + b + 2) ^ (a + b + 1) * (m + 1) ^ (a + b) : ℕ) : ℚ) := by
    rw [centralD_eval]
    exact_mod_cast hnat
  exact_mod_cast hq

/-- **The root bound.** If `m > (s+3)^{2s+1}`, then `A_δ(m) ≠ 0`: an integer root `m` of `A_δ`
divides `A_δ(0) > 0`, and `A_δ(0) ≤ (s+3)^{2s+1}`. -/
theorem centralA_eval_ne_zero_of_lt (a b δ m : ℕ) (hab : b < a) (hδ : δ ≤ 1)
    (hm : (a + b + 3) ^ (2 * (a + b) + 1) < m) : (centralA a b δ).eval (m : ℤ) ≠ 0 := by
  intro h0
  have hdvd := Polynomial.sub_dvd_eval_sub (m : ℤ) 0 (centralA a b δ)
  rw [h0, sub_zero, zero_sub, dvd_neg] at hdvd
  have hpos := centralA_eval_zero_pos a b δ hab hδ
  have hle := Int.le_of_dvd hpos hdvd
  have h0b := abs_centralA_eval_le a b δ 0 hab hδ
  rw [Nat.cast_zero, zero_add, one_pow, mul_one, abs_of_pos hpos] at h0b
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = (a + b + 3) ^ (2 * (a + b) + 1) := ⟨_, rfl⟩
  rw [← hQ] at h0b hm
  have : (m : ℤ) ≤ (Q : ℤ) := hle.trans h0b
  omega

/-- `8 / c_{a,b} ≤ 8 (2s+1)^{s+1}`, `s = a + b`. -/
theorem eight_div_asymmetricEnergyConstant_le (a b : ℕ) :
    8 / asymmetricEnergyConstant a b ≤ 8 * (2 * ((a + b : ℕ) : ℝ) + 1) ^ (a + b + 1) := by
  rw [asymmetricEnergyConstant_eq, div_div_eq_mul_div]
  have hY0 : (0 : ℝ) ≤ (2 * ((a + b : ℕ) : ℝ) + 1) ^ (a + b + 1) := by positivity
  have ha : (2 * a + 1 : ℝ) ≤ 2 * ((a + b : ℕ) : ℝ) + 1 := by
    push_cast; linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
  have hb : (2 * b + 1 : ℝ) ≤ 2 * ((a + b : ℕ) : ℝ) + 1 := by
    push_cast; linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
  have hX : (2 * a + 1 : ℝ) ^ (2 * a + 1) * (2 * b + 1 : ℝ) ^ (2 * b + 1) ≤
      ((2 * ((a + b : ℕ) : ℝ) + 1) ^ (a + b + 1)) ^ 2 := by
    calc (2 * a + 1 : ℝ) ^ (2 * a + 1) * (2 * b + 1 : ℝ) ^ (2 * b + 1)
        ≤ (2 * ((a + b : ℕ) : ℝ) + 1) ^ (2 * a + 1) * (2 * ((a + b : ℕ) : ℝ) + 1) ^ (2 * b + 1) :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) ha _)
            (pow_le_pow_left₀ (by positivity) hb _) (by positivity) (by positivity)
      _ = _ := by rw [← pow_add, ← pow_mul]; congr 1; ring
  have hsX := (Real.sqrt_le_sqrt hX).trans_eq (Real.sqrt_sq hY0)
  have hP : (1 : ℝ) ≤ ((a + b + 1 : ℝ)) ^ (a + b + 1) :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a), (Nat.cast_nonneg b : (0 : ℝ) ≤ b)])
  rw [div_le_iff₀ (by linarith)]
  have := mul_le_mul_of_nonneg_left hP hY0
  linarith

/-! ### The criterion (3.5) from explicit bounds -/

/-- **The criterion (3.5) at a given `m` from explicit bounds.** The proof of
`exists_forall_asymmetric_criterion`, with the bounds `|A_δ(m)| ≤ K_A (m+1)^{d_A}`,
`|D_δ(m)| ≤ K_D (m+1)^{d_D}` and the final margin inequality taken at the given `m`. -/
theorem asymmetric_criterion_of_bounds (a b δ m dA dD : ℕ) (hδ : δ ≤ 1) (hm : 1 ≤ m)
    {c KA KD : ℝ} (hc : 0 < c) (hKA1 : 1 ≤ KA) (hKD1 : 1 ≤ KD)
    (hAb : |(((centralA a b δ).eval (m : ℤ) : ℤ) : ℝ)| ≤ KA * ((m : ℝ) + 1) ^ dA)
    (hDb : |(((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ)| ≤ KD * ((m : ℝ) + 1) ^ dD)
    (hmain : (√(((a + b : ℕ) : ℝ) + 4) * log 3 + 6 * ((a + b : ℕ) : ℝ) + 2 * dA + 4 + 2 * a +
        2 * dD) * √((m : ℝ) + 1) +
      ((((a + b : ℕ) : ℝ) + 2) * log 3 + 3 * (((a + b : ℕ) : ℝ) * log (((a + b : ℕ) : ℝ) + 2)) +
        log KA + log (8 / c) + log (((a + b : ℕ) : ℝ) + 4) + a * log (a + 2) + log KD) <
      m * log (4 / 3)) :
    (((m + (a + b) + 2 : ℕ) : ℝ) + √((2 * (2 * m + δ) + (a + b) + 1 : ℕ) : ℝ)) * log 3 +
        3 * log ((∏ j ∈ Icc 1 (a + b), (2 * m + δ + j) : ℕ) : ℝ) +
        log |(((centralA a b δ).eval (m : ℤ) : ℤ) : ℝ)| +
        log (8 * ((m : ℝ) + 1) * ((2 * (2 * m + δ) + (a + b) + 1 : ℕ) : ℝ) *
          ((2 * m + δ + a).choose a : ℝ) /
            (c * √(m : ℝ) / (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ))) <
      ((2 * m + δ : ℕ) : ℝ) * log 2 := by
  generalize hs : a + b = s at hmain ⊢
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hsq : 0 ≤ √((m : ℝ) + 1) := Real.sqrt_nonneg _
  have hδ' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ
  -- `S`
  have hS : ((2 * (2 * m + δ) + s + 1 : ℕ) : ℝ) ≤ ((s : ℝ) + 4) * ((m : ℝ) + 1) ^ 1 := by
    push_cast; nlinarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
  have hSpos : (0 : ℝ) < ((2 * (2 * m + δ) + s + 1 : ℕ) : ℝ) := by positivity
  have hlogS := log_abs_le_of_le (K := (s : ℝ) + 4)
    (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])
    (by rw [abs_of_pos hSpos]; exact hS)
  rw [abs_of_pos hSpos] at hlogS
  have hsqrtS : √((2 * (2 * m + δ) + s + 1 : ℕ) : ℝ) ≤ √((s : ℝ) + 4) * √((m : ℝ) + 1) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by simpa using hS)
  -- `T`
  have hT : ((∏ j ∈ Icc 1 s, (2 * m + δ + j) : ℕ) : ℝ) ≤
      ((s : ℝ) + 2) ^ s * ((m : ℝ) + 1) ^ s := by
    have h1 : ∏ j ∈ Icc 1 s, (2 * m + δ + j) ≤ (2 * m + δ + s) ^ s := by
      have := Finset.prod_le_pow_card (Icc 1 s) (fun j => 2 * m + δ + j) (2 * m + δ + s)
        fun j hj => by simp only [mem_Icc] at hj; omega
      rwa [Nat.card_Icc, show s + 1 - 1 = s by omega] at this
    have h2 : ((2 * m + δ + s : ℕ) : ℝ) ≤ ((s : ℝ) + 2) * ((m : ℝ) + 1) := by
      push_cast; nlinarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
    calc ((∏ j ∈ Icc 1 s, (2 * m + δ + j) : ℕ) : ℝ) ≤ ((2 * m + δ + s : ℕ) : ℝ) ^ s := by
          exact_mod_cast h1
      _ ≤ (((s : ℝ) + 2) * ((m : ℝ) + 1)) ^ s := pow_le_pow_left₀ (by positivity) h2 s
      _ = _ := mul_pow _ _ _
  have hTpos : (0 : ℝ) < ((∏ j ∈ Icc 1 s, (2 * m + δ + j) : ℕ) : ℝ) := by
    have : 0 < ∏ j ∈ Icc 1 s, (2 * m + δ + j) := Finset.prod_pos fun j hj => by
      simp only [mem_Icc] at hj; omega
    exact_mod_cast this
  have hlogT := log_abs_le_of_le (K := ((s : ℝ) + 2) ^ s)
    (one_le_pow₀ (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]))
    (by rw [abs_of_pos hTpos]; exact hT)
  rw [abs_of_pos hTpos, Real.log_pow] at hlogT
  -- `A_δ(m)`
  have hlogA := log_abs_le_of_le hKA1 hAb
  -- `B`
  have hB : ((2 * m + δ + a).choose a : ℝ) ≤ ((a : ℝ) + 2) ^ a * ((m : ℝ) + 1) ^ a := by
    have h1 := Nat.choose_le_pow (2 * m + δ + a) a
    have h2 : ((2 * m + δ + a : ℕ) : ℝ) ≤ ((a : ℝ) + 2) * ((m : ℝ) + 1) := by
      push_cast; nlinarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
    calc ((2 * m + δ + a).choose a : ℝ) ≤ ((2 * m + δ + a : ℕ) : ℝ) ^ a := by exact_mod_cast h1
      _ ≤ (((a : ℝ) + 2) * ((m : ℝ) + 1)) ^ a := pow_le_pow_left₀ (by positivity) h2 a
      _ = _ := mul_pow _ _ _
  have hBpos : (0 : ℝ) < ((2 * m + δ + a).choose a : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hlogB := log_abs_le_of_le (K := ((a : ℝ) + 2) ^ a)
    (one_le_pow₀ (by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]))
    (by rw [abs_of_pos hBpos]; exact hB)
  rw [abs_of_pos hBpos, Real.log_pow] at hlogB
  -- `D_δ(m)`
  have hDpos : (0 : ℝ) < (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast centralD_eval_pos a b δ m
  have hlogD := log_abs_le_of_le hKD1 hDb
  rw [abs_of_pos hDpos] at hlogD
  -- the last logarithm
  have hsqm : (1 : ℝ) ≤ √(m : ℝ) := Real.one_le_sqrt.mpr hm1
  have hX : 8 * ((m : ℝ) + 1) * ((2 * (2 * m + δ) + s + 1 : ℕ) : ℝ) *
      ((2 * m + δ + a).choose a : ℝ) / (c * √(m : ℝ) / (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ))
      ≤ 8 / c * ((m : ℝ) + 1) * ((2 * (2 * m + δ) + s + 1 : ℕ) : ℝ) *
        ((2 * m + δ + a).choose a : ℝ) * (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ) := by
    rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    have hprod : 0 ≤ 8 / c * ((m : ℝ) + 1) * ((2 * (2 * m + δ) + s + 1 : ℕ) : ℝ) *
        ((2 * m + δ + a).choose a : ℝ) * (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ) := by positivity
    have e : 8 / c * ((m : ℝ) + 1) * ((2 * (2 * m + δ) + s + 1 : ℕ) : ℝ) *
        ((2 * m + δ + a).choose a : ℝ) * (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ) * c =
        8 * ((m : ℝ) + 1) * ((2 * (2 * m + δ) + s + 1 : ℕ) : ℝ) *
        ((2 * m + δ + a).choose a : ℝ) * (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ) := by
      field_simp
    nlinarith [mul_nonneg (mul_nonneg hprod hc.le) (sub_nonneg.mpr hsqm)]
  have hXpos : 0 < 8 * ((m : ℝ) + 1) * ((2 * (2 * m + δ) + s + 1 : ℕ) : ℝ) *
      ((2 * m + δ + a).choose a : ℝ) /
        (c * √(m : ℝ) / (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ)) := by positivity
  have hlogX := Real.log_le_log hXpos hX
  rw [Real.log_mul (by positivity) hDpos.ne', Real.log_mul (by positivity) hBpos.ne',
    Real.log_mul (by positivity) hSpos.ne', Real.log_mul (by positivity) hm0.ne'] at hlogX
  have hlogm1 := log_le_two_mul_sqrt hm0.le
  have hl3 : 0 < log (3 : ℝ) := Real.log_pos (by norm_num)
  have h43 : log (4 / 3 : ℝ) = 2 * log 2 - log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hsqS3 := mul_le_mul_of_nonneg_right hsqrtS hl3.le
  have hl2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  rw [h43] at hmain
  push_cast at hlogS hlogT hlogB hlogX hsqS3 hmain ⊢
  linarith [mul_nonneg (Nat.cast_nonneg δ : (0 : ℝ) ≤ δ) hl2.le]

/-! ### Rational bounds for the constants -/

/-- `K √(m+1) + K' < m/4` whenever `K, K' ≤ P` and `(4P+2)² ≤ m`. -/
theorem mul_sqrt_add_lt_of_sq_le {K K' P m : ℝ} (hP : 0 ≤ P) (hK : K ≤ P) (hK' : K' ≤ P)
    (hm : (4 * P + 2) ^ 2 ≤ m) : K * √(m + 1) + K' < m / 4 := by
  have hm0 : 0 ≤ m := le_trans (by positivity) hm
  obtain ⟨x, hx⟩ : ∃ x, x = √(m + 1) := ⟨_, rfl⟩
  rw [← hx]
  have hx0 : 0 ≤ x := by rw [hx]; exact Real.sqrt_nonneg _
  have hxsq : x ^ 2 = m + 1 := by rw [hx]; exact Real.sq_sqrt (by linarith)
  have hx4 : 4 * P + 2 < x := by
    by_contra h
    have h' := not_lt.mp h
    have := mul_le_mul h' h' hx0 (by linarith)
    nlinarith
  have hKx : K * x ≤ P * x := mul_le_mul_of_nonneg_right hK hx0
  nlinarith [mul_pos (show (0 : ℝ) < x - 1 - 4 * P by linarith) (show (0 : ℝ) < x + 1 by linarith)]

/-- The constants of `asymmetric_criterion_of_bounds` for `d_A = d_D = s`,
`K_A = (s+3)^{2s+1}`, `K_D = (s+2)^{s+1}` and `c = c_{a,b}` are at most `12 (s+2)²`. -/
theorem asymmetric_explicit_constants_le (a b : ℕ) :
    √(((a + b : ℕ) : ℝ) + 4) * log 3 + 6 * ((a + b : ℕ) : ℝ) + 2 * ((a + b : ℕ) : ℝ) + 4 +
        2 * a + 2 * ((a + b : ℕ) : ℝ) ≤ 12 * (((a + b : ℕ) : ℝ) + 2) ^ 2 ∧
      (((a + b : ℕ) : ℝ) + 2) * log 3 +
          3 * (((a + b : ℕ) : ℝ) * log (((a + b : ℕ) : ℝ) + 2)) +
          log ((((a + b : ℕ) : ℝ) + 3) ^ (2 * (a + b) + 1)) +
          log (8 / asymmetricEnergyConstant a b) + log (((a + b : ℕ) : ℝ) + 4) +
          a * log (a + 2) + log ((((a + b : ℕ) : ℝ) + 2) ^ (a + b + 1)) ≤
        12 * (((a + b : ℕ) : ℝ) + 2) ^ 2 := by
  have h8c := eight_div_asymmetricEnergyConstant_le a b
  have hc := asymmetricEnergyConstant_pos a b
  obtain ⟨s, hs⟩ : ∃ s, s = a + b := ⟨_, rfl⟩
  rw [← hs] at h8c ⊢
  have has : (a : ℝ) ≤ s := by exact_mod_cast (show a ≤ s by omega)
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hl3 : log 3 < (2 : ℝ) := log_three_lt_d4.trans (by norm_num)
  have hl30 : 0 ≤ log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog : ∀ x : ℝ, 0 < x → log x ≤ x - 1 := fun x hx => Real.log_le_sub_one_of_pos hx
  have hsqrt : √((s : ℝ) + 4) ≤ (s : ℝ) + 4 :=
    (Real.sqrt_le_sqrt (by nlinarith)).trans_eq (Real.sqrt_sq (by linarith))
  have l2 := hlog ((s : ℝ) + 2) (by linarith)
  have l3 := hlog ((s : ℝ) + 3) (by linarith)
  have l4 := hlog ((s : ℝ) + 4) (by linarith)
  have la := hlog ((a : ℝ) + 2) (by linarith)
  have l2s := hlog (2 * (s : ℝ) + 1) (by linarith)
  have l8 : log (8 : ℝ) < 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  have hl2 : 0 ≤ log ((s : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hl8c : log (8 / asymmetricEnergyConstant a b) ≤ 3 + ((s : ℝ) + 1) * (2 * s) := by
    have h := Real.log_le_log (div_pos (by norm_num) hc) h8c
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
    push_cast at h
    have := mul_le_mul_of_nonneg_left l2s (show (0 : ℝ) ≤ s + 1 by linarith)
    linarith
  rw [Real.log_pow, Real.log_pow]
  push_cast
  have p1 := mul_le_mul hsqrt hl3.le hl30 (by linarith)
  have p2 := mul_le_mul_of_nonneg_left hl3.le (show (0 : ℝ) ≤ s + 2 by linarith)
  have p3 := mul_le_mul_of_nonneg_left l2 hs0
  have p4 := mul_le_mul_of_nonneg_left l3 (show (0 : ℝ) ≤ 2 * s + 1 by linarith)
  have p5 := mul_le_mul_of_nonneg_left la ha0
  have p6 := mul_le_mul_of_nonneg_left l2 (show (0 : ℝ) ≤ s + 1 by linarith)
  have p7 : (a : ℝ) * (a + 2 - 1) ≤ s * (s + 2 - 1) :=
    mul_le_mul has (by linarith) (by linarith) hs0
  constructor <;> nlinarith

/-! ### Theorem 1.3, irreducibility, with the explicit threshold -/

/-- **Theorem 1.3, irreducibility, effective form.** For distinct nonnegative integers `a, b`,
`P_n^{(a,b)}` is irreducible over `ℚ` for every `n ≥ unequalThreshold a b`, where
`unequalThreshold a b = 2 ((48 (s+2)² + 2)² + (s+3)^{2s+1} + 2s + 10)`, `s = a + b`, is an
explicit computable function. Conditional on the same cited hypotheses as
`exists_forall_irreducible_jacobiP`. -/
theorem irreducible_jacobiP_of_unequalThreshold_le (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros) {a b : ℕ} (hab : a ≠ b) :
    ∀ n ≥ unequalThreshold a b, Irreducible (jacobiP a b n) := by
  wlog hlt : b < a generalizing a b
  · intro n hn
    rw [unequalThreshold_comm] at hn
    exact (irreducible_jacobiP_comm _ _ n).mpr (this hab.symm (by omega) n hn)
  intro n hn
  obtain ⟨m, δ, hδ, rfl⟩ : ∃ m δ, δ ≤ 1 ∧ n = 2 * m + δ :=
    ⟨n / 2, n % 2, by omega, by omega⟩
  have hMth := unequalMThreshold_eq a b
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = 48 * (a + b + 2) ^ 2 + 2 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = (a + b + 3) ^ (2 * (a + b) + 1) := ⟨_, rfl⟩
  rw [← hP, ← hQ] at hMth
  have hmT : unequalMThreshold a b ≤ m := by
    rw [unequalThreshold_eq] at hn
    omega
  have hPm : P ^ 2 ≤ m := by omega
  have hQm : Q < m := by omega
  have hsm : 2 * (a + b) + 10 ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  have hA : (centralA a b δ).eval (m : ℤ) ≠ 0 :=
    centralA_eval_ne_zero_of_lt a b δ m hlt hδ (by rw [← hQ]; exact hQm)
  have hc := asymmetricEnergyConstant_pos a b
  have hAb : |(((centralA a b δ).eval (m : ℤ) : ℤ) : ℝ)| ≤
      (((a + b : ℕ) : ℝ) + 3) ^ (2 * (a + b) + 1) * ((m : ℝ) + 1) ^ (a + b) := by
    have h := abs_centralA_eval_le a b δ m hlt hδ
    exact_mod_cast h
  have hDb : |(((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ)| ≤
      (((a + b : ℕ) : ℝ) + 2) ^ (a + b + 1) * ((m : ℝ) + 1) ^ (a + b) := by
    have hD0 : (0 : ℝ) < (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast centralD_eval_pos a b δ m
    rw [abs_of_pos hD0]
    have h := centralD_eval_le a b δ m hlt hδ
    exact_mod_cast h
  have hKA1 : (1 : ℝ) ≤ (((a + b : ℕ) : ℝ) + 3) ^ (2 * (a + b) + 1) :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg (a + b) : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ))])
  have hKD1 : (1 : ℝ) ≤ (((a + b : ℕ) : ℝ) + 2) ^ (a + b + 1) :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg (a + b) : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ))])
  obtain ⟨hK, hK'⟩ := asymmetric_explicit_constants_le a b
  have hmR : (4 * (12 * (((a + b : ℕ) : ℝ) + 2) ^ 2) + 2) ^ 2 ≤ (m : ℝ) := by
    have h : ((P ^ 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast hPm
    rw [hP] at h
    push_cast at h ⊢
    linarith
  have hlt4 := mul_sqrt_add_lt_of_sq_le (by positivity) hK hK' hmR
  have h43 := log_four_div_three_gt
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hcrit := asymmetric_criterion_of_bounds a b δ m (a + b) (a + b) hδ hm1 hc hKA1 hKD1 hAb
    hDb (lt_of_lt_of_le hlt4 (by nlinarith))
  rw [div_div_eq_mul_div] at hcrit
  exact irreducible_jacobiP_of_criterion hH hZ hlt hδ hsm hA hcrit

/-- The existence form of Theorem 1.3 (irreducibility), with the explicit witness. -/
theorem exists_forall_irreducible_jacobiP_effective (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros) {a b : ℕ} (hab : a ≠ b) :
    ∃ N : ℕ, N = unequalThreshold a b ∧ ∀ n ≥ N, Irreducible (jacobiP a b n) :=
  ⟨_, rfl, irreducible_jacobiP_of_unequalThreshold_le hH hZ hab⟩

end ArithmeticOfJacobiPolynomials
