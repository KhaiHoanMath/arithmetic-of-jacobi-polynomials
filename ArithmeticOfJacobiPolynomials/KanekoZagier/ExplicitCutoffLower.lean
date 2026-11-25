/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.ExplicitCutoffPrimes

/-!
# Proposition B.1: the archimedean lower bound (Appendix B.1)

For `λ, μ ∈ {-1, 1}` (the argument `l` is `λ`), `δ = (μ + 1)/2` and `n ≥ 1`, this file proves the
endpoint identities and bounds of Appendix B.1:

* `kzEndpointTwo_bounds`: `2n - s_2(n) ≤ D_{2,n} ≤ 2n - s_2(n) + ⌊log_2(3n+1)⌋`
  (that is, `0 ≤ b_n ≤ log_2(3n+1)` for `b_n = v_2 binom(n+α, n)`);
* `two_mul_kzEndpointThree`: `2 D_{3,n} = 3n + δ + s_3(n) - s_3(2n+δ)`;
* `log_kzKappa_eq`: `log κ_n = (2n - s_2(n)) log 2 + (3n - s_3(n))/2 · log 3`;
* `kz_lambda_ge_sub`: the lower bound `n(L_* - E) - R_n` in digit-sum form, with
  `L_* = log(4 + 3√3)` (the printed error `6 log(12n)` is proved in `SourceCutoffArchimedean`);
* `abs_kzT2_sub_kzT3_le`: `|T_{2,n} - T_{3,n}| ≤ 9/10` for `n ≥ 250000` (the printed `< 3/10` is
  proved in `SourceCutoffArchimedean`).

Digit sums are bounded through `s_b(m) ≤ (b-1)(⌊log_b m⌋ + 1)`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Finset

/-! ### Digit sums and Legendre's formula -/

theorem digits_sum_le_mul_log_succ {b : ℕ} (hb : 2 ≤ b) (m : ℕ) :
    (b.digits m).sum ≤ (b - 1) * (Nat.log b m + 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have h := List.sum_le_length_nsmul (b.digits m) (b - 1) fun x hx => by
    have := Nat.digits_lt_base (by omega) hx
    omega
  rw [Nat.length_digits b m (by omega) hm.ne', smul_eq_mul] at h
  rw [mul_comm]
  exact h

theorem natLog_mul_log_le_log {b m : ℕ} (hb : 2 ≤ b) (hm : m ≠ 0) :
    (Nat.log b m : ℝ) * Real.log b ≤ Real.log m := by
  have h : ((b : ℝ) ^ Nat.log b m) ≤ m := by exact_mod_cast Nat.pow_log_le_self b hm
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hpos : (0 : ℝ) < (b : ℝ) ^ Nat.log b m := by positivity
  have := Real.log_le_log hpos h
  rwa [Real.log_pow] at this

theorem digits_sum_mul_log_le {b m : ℕ} (hb : 2 ≤ b) (hm : m ≠ 0) :
    ((b.digits m).sum : ℝ) * Real.log b ≤ ((b : ℝ) - 1) * (Real.log m + Real.log b) := by
  have h1 : ((b.digits m).sum : ℝ) ≤ ((b : ℝ) - 1) * ((Nat.log b m : ℝ) + 1) := by
    have h := digits_sum_le_mul_log_succ hb m
    have e : (((b - 1) * (Nat.log b m + 1) : ℕ) : ℝ) =
        ((b : ℝ) - 1) * ((Nat.log b m : ℝ) + 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [← e]
    exact Nat.cast_le.mpr h
  have h2 := natLog_mul_log_le_log hb hm
  have hlb : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast (show 1 ≤ b by omega))
  have hb1 : (0 : ℝ) ≤ (b : ℝ) - 1 := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  calc ((b.digits m).sum : ℝ) * Real.log b
      ≤ ((b : ℝ) - 1) * ((Nat.log b m : ℝ) + 1) * Real.log b :=
        mul_le_mul_of_nonneg_right h1 hlb
    _ = ((b : ℝ) - 1) * ((Nat.log b m : ℝ) * Real.log b + Real.log b) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hb1

theorem digits_two_sum_mul_log_le {m : ℕ} (hm : m ≠ 0) :
    ((Nat.digits 2 m).sum : ℝ) * Real.log 2 ≤ Real.log m + Real.log 2 := by
  have h := digits_sum_mul_log_le (b := 2) le_rfl hm
  have e : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [e] at h
  linarith

theorem digits_three_sum_mul_log_le {m : ℕ} (hm : m ≠ 0) :
    ((Nat.digits 3 m).sum : ℝ) * Real.log 3 ≤ 2 * (Real.log m + Real.log 3) := by
  have h := digits_sum_mul_log_le (b := 3) (by norm_num) hm
  have e : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [e] at h
  linarith

theorem padicValNat_two_factorial_cast (n : ℕ) :
    (padicValNat 2 n.factorial : ℝ) = n - ((Nat.digits 2 n).sum : ℝ) := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  have hle := Nat.digit_sum_le 2 n
  norm_num at h
  have h' : padicValNat 2 n.factorial + (Nat.digits 2 n).sum = n := by omega
  have h'' : ((padicValNat 2 n.factorial + (Nat.digits 2 n).sum : ℕ) : ℝ) = n := by rw [h']
  rw [Nat.cast_add] at h''
  linarith

theorem padicValNat_three_factorial_cast (n : ℕ) :
    2 * (padicValNat 3 n.factorial : ℝ) = n - ((Nat.digits 3 n).sum : ℝ) := by
  have h := sub_one_mul_padicValNat_factorial (p := 3) n
  have hle := Nat.digit_sum_le 3 n
  norm_num at h
  have h' : 2 * padicValNat 3 n.factorial + (Nat.digits 3 n).sum = n := by omega
  have h'' : ((2 * padicValNat 3 n.factorial + (Nat.digits 3 n).sum : ℕ) : ℝ) = n := by
    rw [h']
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h''
  linarith

/-! ### The endpoint `t = 0`: `D_{2,n}` -/

theorem sum_padicValInt_eq_padicValRat_prod (p : ℕ) [Fact p.Prime] (d : ℕ) (r : ℤ)
    (hr : r = 1 ∨ r = -1) (hd : 2 ≤ d) (n : ℕ) :
    ((∑ j ∈ Icc 1 n, padicValInt p ((d : ℤ) * (j : ℤ) + r) : ℕ) : ℤ) =
      padicValRat p (∏ k ∈ Ioc 0 n, (((d : ℤ) * (k : ℤ) + r : ℤ) : ℚ)) := by
  have hI : Icc 1 n = Ioc 0 n := by
    ext k
    simp only [mem_Icc, mem_Ioc]
    omega
  have hne : ∀ k ∈ Ioc 0 n, (d : ℤ) * (k : ℤ) + r ≠ 0 := by
    intro k hk
    have hk1 : (1 : ℤ) ≤ k := by exact_mod_cast (mem_Ioc.mp hk).1
    have hd' : (2 : ℤ) ≤ d := by exact_mod_cast hd
    apply ne_of_gt
    rcases hr with rfl | rfl <;> nlinarith
  rw [padicValRat_prod_intCast (Ioc 0 n) (fun k : ℕ => (d : ℤ) * (k : ℤ) + r) hne, hI,
    Nat.cast_sum]
  exact sum_congr rfl fun k _ => padicValRat.of_int.symm

theorem kzEndpointTwo_sum_bounds {l : ℤ} (hl : l = 1 ∨ l = -1) (n : ℕ) :
    padicValNat 2 n.factorial ≤ ∑ j ∈ Icc 1 n, padicValInt 2 (3 * (j : ℤ) + l) ∧
      ∑ j ∈ Icc 1 n, padicValInt 2 (3 * (j : ℤ) + l) ≤
        padicValNat 2 n.factorial + Nat.log 2 (3 * n + 1) := by
  have hS := sum_padicValInt_eq_padicValRat_prod 2 3 l hl (by norm_num) n
  simp only [Nat.cast_ofNat] at hS
  have hd : ¬ 2 ∣ 3 := by norm_num
  have hpos : ∀ k ∈ Ioc 0 n, 0 < ((3 : ℕ) : ℤ) * (k : ℤ) + l := by
    intro k hk
    have := (mem_Ioc.mp hk).1
    push_cast
    rcases hl with rfl | rfl <;> omega
  have hlo := padicValRat_factorial_le_prod_affine (p := 2) hd l (Nat.zero_le n) hpos
  simp only [Nat.cast_ofNat, Nat.sub_zero, padicValRat.of_nat] at hlo
  set H := Nat.log 2 (3 * n + 1) with hHdef
  have hH : 3 * n + 1 < 2 ^ (H + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hlt : ∀ k ∈ Ioc 0 n, ((3 : ℕ) : ℤ) * (k : ℤ) + l < ((2 : ℕ) : ℤ) ^ (H + 1) := by
    intro k hk
    have := (mem_Ioc.mp hk).2
    have hH' : ((3 * n + 1 : ℕ) : ℤ) < ((2 ^ (H + 1) : ℕ) : ℤ) := by exact_mod_cast hH
    push_cast at hH' ⊢
    rcases hl with rfl | rfl <;> omega
  have hval := padicValRat_prod_affine_eq_sum (p := 2) hd l (Nat.zero_le n) hpos hlt
  simp only [Nat.cast_ofNat] at hval
  have hfac := padicValRat_factorial_eq_sum (p := 2) (m := n) (H := H) (by omega)
  rw [padicValRat.of_nat] at hfac
  have hup : padicValRat 2 (∏ k ∈ Ioc 0 n, ((3 * (k : ℤ) + l : ℤ) : ℚ)) ≤
      padicValNat 2 n.factorial + H := by
    rw [hval, hfac]
    have hcard : ∑ h ∈ Icc 1 H, ((n / 2 ^ h : ℕ) : ℤ) + (H : ℤ) =
        ∑ h ∈ Icc 1 H, (((n / 2 ^ h : ℕ) : ℤ) + 1) := by
      rw [sum_add_distrib]
      simp
    rw [hcard]
    refine sum_le_sum fun h _ => ?_
    have hq : 0 < 2 ^ h := pow_pos (by norm_num) h
    have ha := affineResidue_lt l 3 hq
    have h1 := kz_div_add_le_div_add_one (X := n) hq ha
    have h2 : (0 + affineResidue l 3 (2 ^ h)) / 2 ^ h = 0 := by
      rw [zero_add]; exact Nat.div_eq_of_lt ha
    rw [Nat.add_comm (affineResidue l 3 (2 ^ h)) n] at h1
    have h3 : (n + affineResidue l 3 (2 ^ h)) / 2 ^ h - (0 + affineResidue l 3 (2 ^ h)) / 2 ^ h ≤
        n / 2 ^ h + 1 := (Nat.sub_le _ _).trans h1
    have h4 : (((n + affineResidue l 3 (2 ^ h)) / 2 ^ h -
        (0 + affineResidue l 3 (2 ^ h)) / 2 ^ h : ℕ) : ℤ) ≤ ((n / 2 ^ h + 1 : ℕ) : ℤ) :=
      Nat.cast_le.mpr h3
    rw [Nat.cast_add, Nat.cast_one] at h4
    exact h4
  constructor
  · have : (padicValNat 2 n.factorial : ℤ) ≤
        ((∑ j ∈ Icc 1 n, padicValInt 2 (3 * (j : ℤ) + l) : ℕ) : ℤ) := by
      rw [hS]; exact hlo
    exact Nat.cast_le.mp this
  · have : ((∑ j ∈ Icc 1 n, padicValInt 2 (3 * (j : ℤ) + l) : ℕ) : ℤ) ≤
        ((padicValNat 2 n.factorial + H : ℕ) : ℤ) := by
      rw [Nat.cast_add, hS]; exact hup
    exact Nat.cast_le.mp this

/-- `2n - s_2(n) ≤ D_{2,n} ≤ 2n - s_2(n) + ⌊log_2(3n+1)⌋`. -/
theorem kzEndpointTwo_bounds {l : ℤ} (hl : l = 1 ∨ l = -1) (n : ℕ) :
    (2 * n : ℝ) - (Nat.digits 2 n).sum ≤ kzEndpointTwo l n ∧
      (kzEndpointTwo l n : ℝ) ≤ 2 * n - (Nat.digits 2 n).sum + Nat.log 2 (3 * n + 1) := by
  obtain ⟨h1, h2⟩ := kzEndpointTwo_sum_bounds hl n
  have h1' : (padicValNat 2 n.factorial : ℝ) ≤
      ((∑ j ∈ Icc 1 n, padicValInt 2 (3 * (j : ℤ) + l) : ℕ) : ℝ) := Nat.cast_le.mpr h1
  have h2' : ((∑ j ∈ Icc 1 n, padicValInt 2 (3 * (j : ℤ) + l) : ℕ) : ℝ) ≤
      (padicValNat 2 n.factorial : ℝ) + (Nat.log 2 (3 * n + 1) : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr h2
    rwa [Nat.cast_add] at this
  have hv := padicValNat_two_factorial_cast n
  have hD : (kzEndpointTwo l n : ℝ) =
      n + ((∑ j ∈ Icc 1 n, padicValInt 2 (3 * (j : ℤ) + l) : ℕ) : ℝ) := by
    rw [kzEndpointTwo_eq, Nat.cast_add]
  rw [hD]
  constructor <;> linarith

/-! ### The endpoint `t = 1`: `D_{3,n}` -/

theorem factorial_two_mul_add_kzDelta {μ : ℤ} (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    (((2 * n + kzDelta μ).factorial : ℕ) : ℚ) =
      (∏ k ∈ Ioc 0 n, ((2 * (k : ℤ) + μ : ℤ) : ℚ)) * 2 ^ n * (n.factorial : ℚ) := by
  rcases hμ with rfl | rfl
  · have hd : kzDelta 1 = 1 := by rw [kzDelta_eq]; decide
    rw [hd]
    induction n with
    | zero => simp
    | succ n ih =>
      have f1 : (((2 * (n + 1) + 1).factorial : ℕ) : ℚ) =
          ((2 * n + 3 : ℕ) : ℚ) * ((2 * n + 2 : ℕ) : ℚ) * ((2 * n + 1).factorial : ℚ) := by
        rw [show 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 by ring, Nat.factorial_succ,
          Nat.factorial_succ (2 * n + 1)]
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
        ring
      rw [f1, ih, Finset.prod_Ioc_succ_top (Nat.zero_le n), Nat.factorial_succ n]
      push_cast
      ring
  · have hd : kzDelta (-1) = 0 := by rw [kzDelta_eq]; decide
    rw [hd]
    induction n with
    | zero => simp
    | succ n ih =>
      have f1 : (((2 * (n + 1) + 0).factorial : ℕ) : ℚ) =
          ((2 * n + 2 : ℕ) : ℚ) * ((2 * n + 1 : ℕ) : ℚ) * ((2 * n + 0).factorial : ℚ) := by
        rw [show 2 * (n + 1) + 0 = (2 * n + 0 + 1) + 1 by ring, Nat.factorial_succ,
          Nat.factorial_succ (2 * n + 0)]
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
        ring
      rw [f1, ih, Finset.prod_Ioc_succ_top (Nat.zero_le n), Nat.factorial_succ n]
      push_cast
      ring

theorem kzEndpointThree_sum_eq {μ : ℤ} (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    ((∑ j ∈ Icc 1 n, padicValInt 3 (2 * (j : ℤ) + μ) : ℕ) : ℤ) =
      (padicValNat 3 (2 * n + kzDelta μ).factorial : ℤ) - padicValNat 3 n.factorial := by
  have hS := sum_padicValInt_eq_padicValRat_prod 3 2 μ hμ le_rfl n
  simp only [Nat.cast_ofNat] at hS
  have hF := factorial_two_mul_add_kzDelta hμ n
  have hne : ∏ k ∈ Ioc 0 n, ((2 * (k : ℤ) + μ : ℤ) : ℚ) ≠ 0 := by
    refine prod_ne_zero_iff.mpr fun k hk => ?_
    have := (mem_Ioc.mp hk).1
    have h0 : 2 * (k : ℤ) + μ ≠ 0 := by rcases hμ with rfl | rfl <;> omega
    exact_mod_cast h0
  have h2 : (2 : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have h32 : padicValRat 3 (2 : ℚ) = 0 := by
    have : padicValRat 3 ((2 : ℕ) : ℚ) = 0 := by
      rw [padicValRat.of_nat, padicValNat_primes (p := 3) (q := 2) (by norm_num), Nat.cast_zero]
    exact_mod_cast this
  have hv := congrArg (padicValRat 3) hF
  rw [padicValRat.of_nat, padicValRat.mul (mul_ne_zero hne h2) hf, padicValRat.mul hne h2,
    padicValRat.pow, h32, mul_zero, add_zero, padicValRat.of_nat] at hv
  rw [hS]
  linarith

/-- `2 D_{3,n} = 3n + δ + s_3(n) - s_3(2n + δ)`. -/
theorem two_mul_kzEndpointThree {μ : ℤ} (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    2 * (kzEndpointThree μ n : ℝ) = 3 * n + kzDelta μ + (Nat.digits 3 n).sum -
      (Nat.digits 3 (2 * n + kzDelta μ)).sum := by
  have h := congrArg (Int.cast : ℤ → ℝ) (kzEndpointThree_sum_eq hμ n)
  simp only [Int.cast_sub, Int.cast_natCast] at h
  have h1 := padicValNat_three_factorial_cast n
  have h2 := padicValNat_three_factorial_cast (2 * n + kzDelta μ)
  have e : ((2 * n + kzDelta μ : ℕ) : ℝ) = 2 * n + kzDelta μ := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [e] at h2
  have hD : (kzEndpointThree μ n : ℝ) =
      n + ((∑ j ∈ Icc 1 n, padicValInt 3 (2 * (j : ℤ) + μ) : ℕ) : ℝ) := by
    rw [kzEndpointThree_eq, Nat.cast_add]
  rw [hD, h]
  linarith

/-! ### `log κ_n` and `L_n` -/

/-- `log κ_n = (2n - s_2(n)) log 2 + (3n - s_3(n))/2 · log 3`. -/
theorem log_kzKappa_eq (n : ℕ) : Real.log (kzKappa n) =
    (2 * n - (Nat.digits 2 n).sum) * Real.log 2 +
      (3 * n - (Nat.digits 3 n).sum) / 2 * Real.log 3 := by
  have h2 := padicValNat_two_factorial_cast n
  have h3 := padicValNat_three_factorial_cast n
  rw [kzKappa_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat,
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Nat.cast_add,
    Nat.cast_add]
  linear_combination (Real.log 2) * h2 + (Real.log 3 / 2) * h3

/-- `L_n ≥ L_* - u/n` once `T_{2,n} ≥ 2 log 2 - u/n` and `T_{3,n} ≥ (3/2) log 3 - u/n`. -/
theorem kzL_ge {l μ : ℤ} {n : ℕ} {u : ℝ}
    (h2 : 2 * Real.log 2 - u / n ≤ kzT2 l n) (h3 : 3 / 2 * Real.log 3 - u / n ≤ kzT3 μ n) :
    Real.log (4 + 3 * √3) - u / n ≤ kzL l μ n := by
  have e4 : Real.exp (2 * Real.log 2) = 4 := by
    rw [two_mul, Real.exp_add, Real.exp_log (by norm_num)]
    norm_num
  have hs3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have e3 : Real.exp (3 / 2 * Real.log 3) = 3 * √3 := by
    have : 3 / 2 * Real.log 3 = Real.log 3 + Real.log (√3) := by
      rw [Real.log_sqrt (by norm_num)]
      ring
    rw [this, Real.exp_add, Real.exp_log (by norm_num), Real.exp_log hs3]
  have hx2 : 4 * Real.exp (-(u / n)) ≤ Real.exp (kzT2 l n) := by
    rw [← e4, ← Real.exp_add, Real.exp_le_exp]
    linarith
  have hx3 : 3 * √3 * Real.exp (-(u / n)) ≤ Real.exp (kzT3 μ n) := by
    rw [← e3, ← Real.exp_add, Real.exp_le_exp]
    linarith
  have hpos : 0 < (4 + 3 * √3) * Real.exp (-(u / n)) := by positivity
  have hle : (4 + 3 * √3) * Real.exp (-(u / n)) ≤ Real.exp (kzT2 l n) + Real.exp (kzT3 μ n) := by
    linarith
  have := Real.log_le_log hpos hle
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, ← kzL_eq] at this
  linarith

/-! ### The lower bound -/

theorem kzDelta_le_one {μ : ℤ} (hμ : μ = 1 ∨ μ = -1) : kzDelta μ ≤ 1 := by
  rcases hμ with rfl | rfl <;> rw [kzDelta_eq] <;> decide

/-- The logarithmic facts used for the error terms. -/
theorem kz_log_facts {μ : ℤ} (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : 1 ≤ n) :
    (Nat.log 2 (3 * n + 1) : ℝ) * Real.log 2 ≤ Real.log (3 * n + 1) ∧
    ((Nat.digits 2 n).sum : ℝ) * Real.log 2 ≤ Real.log n + Real.log 2 ∧
    ((Nat.digits 3 n).sum : ℝ) * Real.log 3 ≤ 2 * (Real.log n + Real.log 3) ∧
    ((Nat.digits 3 (2 * n + kzDelta μ)).sum : ℝ) * Real.log 3 ≤
      2 * (Real.log (2 * n + kzDelta μ) + Real.log 3) ∧
    Real.log (3 * n + 1) ≤ (3 * n + 1) / 250000 + 12 ∧
    Real.log n ≤ n / 250000 + 12 ∧
    Real.log (2 * n + kzDelta μ) ≤ (2 * n + kzDelta μ) / 250000 + 12 ∧
    (kzDelta μ : ℝ) ≤ 1 ∧ (0 : ℝ) ≤ kzDelta μ := by
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := natLog_mul_log_le_log (b := 2) le_rfl (m := 3 * n + 1) (by omega)
  have e2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have e31 : ((3 * n + 1 : ℕ) : ℝ) = 3 * n + 1 := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [e2, e31] at h1
  have h4 := digits_three_sum_mul_log_le (m := 2 * n + kzDelta μ) (by omega)
  have e4 : ((2 * n + kzDelta μ : ℕ) : ℝ) = 2 * n + kzDelta μ := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [e4] at h4
  have hδ0 : (0 : ℝ) ≤ kzDelta μ := Nat.cast_nonneg _
  exact ⟨h1, digits_two_sum_mul_log_le (by omega), digits_three_sum_mul_log_le (by omega), h4,
    log_le_div_add_twelve (by positivity), log_le_div_add_twelve (by linarith),
    log_le_div_add_twelve (by linarith), by exact_mod_cast kzDelta_le_one hμ, hδ0⟩

/-- **The lower bound of (Appendix B.1)**, before the numerical estimate of the error: for
`n ≥ 1`, `Λ_n ≥ n (L_* - E) - R_n`, with `L_* = log(4 + 3√3)` and
`R_n = ⌊log_2(3n+1)⌋ log 2 + (3/2) s_2(n) log 2 + s_3(n) log 3 + (δ/2) log 3
  + (1/6) s_3(2n+δ) log 3 + 4 log 2`. -/
theorem kz_lambda_ge_sub {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {n : ℕ}
    (hn : 1 ≤ n) :
    n * (Real.log (4 + 3 * √3) - kzE) -
        ((Nat.log 2 (3 * n + 1) : ℝ) * Real.log 2 +
          3 / 2 * ((Nat.digits 2 n).sum : ℝ) * Real.log 2 +
          ((Nat.digits 3 n).sum : ℝ) * Real.log 3 + (kzDelta μ : ℝ) / 2 * Real.log 3 +
          ((Nat.digits 3 (2 * n + kzDelta μ)).sum : ℝ) / 6 * Real.log 3 + 4 * Real.log 2) ≤
      Real.log (kzKappa n) - kzJ μ n + n * (kzL l μ n - kzT2 l n - kzT3 μ n - kzE) -
        4 * Real.log 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hD2lo, hD2hi⟩ := kzEndpointTwo_bounds hl n
  have hD3 := two_mul_kzEndpointThree hμ n
  have hκ := log_kzKappa_eq n
  have hJ := kzJ_eq μ n
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hT2 : (n : ℝ) * kzT2 l n = kzEndpointTwo l n * Real.log 2 := by
    rw [kzT2_eq, mul_div_assoc', mul_div_cancel_left₀ _ hn0.ne']
  have hT3 : (n : ℝ) * kzT3 μ n = kzEndpointThree μ n * Real.log 3 := by
    rw [kzT3_eq, mul_div_assoc', mul_div_cancel_left₀ _ hn0.ne']
  have hs2 : (0 : ℝ) ≤ (Nat.digits 2 n).sum := Nat.cast_nonneg _
  have hs3 : (0 : ℝ) ≤ (Nat.digits 3 n).sum := Nat.cast_nonneg _
  have hs3' : (0 : ℝ) ≤ (Nat.digits 3 (2 * n + kzDelta μ)).sum := Nat.cast_nonneg _
  have hδ : (0 : ℝ) ≤ kzDelta μ := Nat.cast_nonneg _
  have p1 := mul_nonneg hs2 hl2.le
  have p2 := mul_nonneg hs3 hl3.le
  have p3 := mul_nonneg hs3' hl3.le
  have p4 := mul_nonneg hδ hl3.le
  have hD3l : 2 * (kzEndpointThree μ n : ℝ) * Real.log 3 =
      (3 * n + kzDelta μ + (Nat.digits 3 n).sum - (Nat.digits 3 (2 * n + kzDelta μ)).sum) *
        Real.log 3 := by rw [hD3]
  -- `u = s_2(n) log 2 + s_3(2n+δ) log 3 / 2`
  have hu2 : 2 * Real.log 2 - (((Nat.digits 2 n).sum : ℝ) * Real.log 2 +
      ((Nat.digits 3 (2 * n + kzDelta μ)).sum : ℝ) * Real.log 3 / 2) / n ≤ kzT2 l n := by
    rw [kzT2_eq, le_div_iff₀ hn0, sub_mul, div_mul_cancel₀ _ hn0.ne']
    have := mul_le_mul_of_nonneg_right hD2lo hl2.le
    linarith
  have hu3 : 3 / 2 * Real.log 3 - (((Nat.digits 2 n).sum : ℝ) * Real.log 2 +
      ((Nat.digits 3 (2 * n + kzDelta μ)).sum : ℝ) * Real.log 3 / 2) / n ≤ kzT3 μ n := by
    rw [kzT3_eq, le_div_iff₀ hn0, sub_mul, div_mul_cancel₀ _ hn0.ne']
    linarith
  have hL := kzL_ge hu2 hu3
  have hnL := mul_le_mul_of_nonneg_left hL hn0.le
  have hun : (n : ℝ) * ((((Nat.digits 2 n).sum : ℝ) * Real.log 2 +
      ((Nat.digits 3 (2 * n + kzDelta μ)).sum : ℝ) * Real.log 3 / 2) / n) =
      ((Nat.digits 2 n).sum : ℝ) * Real.log 2 +
        ((Nat.digits 3 (2 * n + kzDelta μ)).sum : ℝ) * Real.log 3 / 2 := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hn0.ne'
  have hD2l : (kzEndpointTwo l n : ℝ) * Real.log 2 ≤
      (2 * n - (Nat.digits 2 n).sum + Nat.log 2 (3 * n + 1)) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hD2hi hl2.le
  have e : (n : ℝ) * (kzL l μ n - kzT2 l n - kzT3 μ n - kzE) =
      n * kzL l μ n - n * kzT2 l n - n * kzT3 μ n - n * kzE := by ring
  have e2 : (n : ℝ) * (Real.log (4 + 3 * √3) - ((((Nat.digits 2 n).sum : ℝ) * Real.log 2 +
      ((Nat.digits 3 (2 * n + kzDelta μ)).sum : ℝ) * Real.log 3 / 2) / n)) =
      n * Real.log (4 + 3 * √3) - (n : ℝ) * ((((Nat.digits 2 n).sum : ℝ) * Real.log 2 +
      ((Nat.digits 3 (2 * n + kzDelta μ)).sum : ℝ) * Real.log 3 / 2) / n) := by ring
  rw [e, hκ, hJ]
  linarith

/-- `|T_{2,n} - T_{3,n}| ≤ 9/10` for `n ≥ 250000`. -/
theorem abs_kzT2_sub_kzT3_le {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {n : ℕ}
    (hn : 250000 ≤ n) : |kzT2 l n - kzT3 μ n| ≤ 9 / 10 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (250000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hD2lo, hD2hi⟩ := kzEndpointTwo_bounds hl n
  have hD3 := two_mul_kzEndpointThree hμ n
  have hT2 : (n : ℝ) * kzT2 l n = kzEndpointTwo l n * Real.log 2 := by
    rw [kzT2_eq, mul_div_assoc', mul_div_cancel_left₀ _ hn0.ne']
  have hT3 : (n : ℝ) * kzT3 μ n = kzEndpointThree μ n * Real.log 3 := by
    rw [kzT3_eq, mul_div_assoc', mul_div_cancel_left₀ _ hn0.ne']
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨h1, h2, h3, h4, g1, g2, g4, hδ, hδ0⟩ := kz_log_facts hμ hn1
  have l2 := Real.log_two_lt_d9
  have l2' := Real.log_two_gt_d9
  have l3 := Real.log_three_lt_d9
  have l3' := Real.log_three_gt_d9
  norm_num at l2 l2' l3 l3'
  have hs2 : (0 : ℝ) ≤ (Nat.digits 2 n).sum := Nat.cast_nonneg _
  have hs3 : (0 : ℝ) ≤ (Nat.digits 3 n).sum := Nat.cast_nonneg _
  have hs3' : (0 : ℝ) ≤ (Nat.digits 3 (2 * n + kzDelta μ)).sum := Nat.cast_nonneg _
  have p1 := mul_nonneg hs2 hl2.le
  have p2 := mul_nonneg hs3 hl3.le
  have p3 := mul_nonneg hs3' hl3.le
  have p4 := mul_nonneg hδ0 hl3.le
  have p5 := mul_le_mul_of_nonneg_right hδ hl3.le
  have q1 := mul_le_mul_of_nonneg_left l2.le hn0.le
  have q2 := mul_le_mul_of_nonneg_left l2'.le hn0.le
  have q3 := mul_le_mul_of_nonneg_left l3.le hn0.le
  have q4 := mul_le_mul_of_nonneg_left l3'.le hn0.le
  have hD2a := mul_le_mul_of_nonneg_right hD2lo hl2.le
  have hD2b := mul_le_mul_of_nonneg_right hD2hi hl2.le
  have hD3l : 2 * (kzEndpointThree μ n : ℝ) * Real.log 3 =
      (3 * n + kzDelta μ + (Nat.digits 3 n).sum - (Nat.digits 3 (2 * n + kzDelta μ)).sum) *
        Real.log 3 := by rw [hD3]
  have hA : (n : ℝ) * (kzT2 l n - kzT3 μ n) ≤ n * (9 / 10) := by
    rw [mul_sub, hT2, hT3]
    linarith
  have hB : (n : ℝ) * (-(9 / 10)) ≤ n * (kzT2 l n - kzT3 μ n) := by
    rw [mul_sub, hT2, hT3]
    linarith
  rw [abs_le]
  exact ⟨le_of_mul_le_mul_left hB hn0, le_of_mul_le_mul_left hA hn0⟩

end ArithmeticOfJacobiPolynomials
