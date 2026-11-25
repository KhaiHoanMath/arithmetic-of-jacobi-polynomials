/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.PrimitiveNormalization
public import ArithmeticOfJacobiPolynomials.KanekoZagier.LevelCount
public import ArithmeticOfJacobiPolynomials.Jacobi.Shift
public import ArithmeticOfJacobiPolynomials.Jacobi.MonicEndpoint
public import ArithmeticOfJacobiPolynomials.Jacobi.Wronskian
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Lemma 4.1: the primitive normalization of the Kaneko–Zagier polynomials

Let `λ, μ ∈ {-1, 1}`, `α = λ/3`, `β = μ/2`, `y_n(t) = P_n^{(α,β)}(1-2t)` and
`κ_n = 2^{n+v_2(n!)} 3^{n+v_3(n!)}`. The coefficient of `t^j` in `y_n` is (2.1)
`(-1)^j binom(n+α, n-j) binom(n+c+j, j)`, which we write as
`(-1)^j A_j C_j / (3^{n-j} 6^j (n-j)! j!)` with
`A_j = ∏_{k ∈ (j,n]} (3k + λ)` and `C_j = ∏_{k ∈ (0,j]} (6k + 6n + 2λ + 3μ)`
(`kz_coeff_eq_prod`). Counting multiples of `p^h` in these progressions shows that
`κ_n y_n` is integral, and that its leading coefficient is a unit at `2` and `3`.

Main results (Lemma 4.1):
* `map_kzScaled`: `κ_n y_n ∈ ℤ[X]`;
* `kanekoZagier_primitive_normalization`: `H_n = (κ_n/g_n) y_n` is primitive and integral of
  degree `n`, its leading coefficient is prime to `6`, and `(g_n, 6) = 1`;
* `log_kzKappa_sub_isBigO`: `log κ_n = (2 log 2 + (3/2) log 3) n + O(log n)`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset Filter Asymptotics

/-! ### The coefficients of `y_n` -/

theorem coeff_jacobiShifted_eq_choose (α β : ℚ) {n j : ℕ} (hj : j ≤ n) :
    (jacobiShifted α β n).coeff j = (-1) ^ j * Ring.choose ((n : ℚ) + α) (n - j) *
      Ring.choose ((n : ℚ) + α + β + j) j := by
  rw [jacobiShifted_eq, jacobiP_comp_one_sub_two_mul_X, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [sum_ite_eq, ite_eq_left (mem_range.mpr (Nat.lt_succ_of_le hj))]

/-- `(x + j + 1)_m = ∏_{k ∈ (j, j+m]} (x + k)`. -/
theorem ascPochhammer_eval_eq_prod_Ioc (x : ℚ) (j m : ℕ) :
    (ascPochhammer ℚ m).eval (x + j + 1) = ∏ k ∈ Ioc j (j + m), (x + k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ascPochhammer_succ_eval, ih, ← add_assoc, Finset.prod_Ioc_succ_top (by omega)]
    push_cast
    ring

/-- `A_j = ∏_{k ∈ (j,n]} (3k + λ)`, the numerator of `binom(n+α, n-j)` times `3^{n-j}`. -/
noncomputable def kzNumA (l : ℤ) (n j : ℕ) : ℚ := ∏ k ∈ Ioc j n, ((3 * (k : ℤ) + l : ℤ) : ℚ)

theorem kzNumA_eq (l : ℤ) (n j : ℕ) :
    kzNumA l n j = ∏ k ∈ Ioc j n, ((3 * (k : ℤ) + l : ℤ) : ℚ) := (rfl)

/-- `C_j = ∏_{k ∈ (0,j]} (6k + 6n + 2λ + 3μ)`, the numerator of `binom(n+c+j, j)` times
`6^j`. -/
noncomputable def kzNumC (l μ : ℤ) (n j : ℕ) : ℚ :=
  ∏ k ∈ Ioc 0 j, ((6 * (k : ℤ) + (6 * n + (2 * l + 3 * μ)) : ℤ) : ℚ)

theorem kzNumC_eq (l μ : ℤ) (n j : ℕ) :
    kzNumC l μ n j = ∏ k ∈ Ioc 0 j, ((6 * (k : ℤ) + (6 * n + (2 * l + 3 * μ)) : ℤ) : ℚ) :=
  (rfl)

/-- The coefficients of `y_n` as quotients of products of progressions. -/
theorem kz_coeff_eq_prod (l μ : ℤ) {n j : ℕ} (hj : j ≤ n) :
    (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n).coeff j =
      (-1) ^ j * kzNumA l n j * kzNumC l μ n j /
        ((3 : ℚ) ^ (n - j) * 6 ^ j * ((n - j).factorial : ℚ) * (j.factorial : ℚ)) := by
  rw [coeff_jacobiShifted_eq_choose _ _ hj, ring_choose_eq_ascPochhammer_div,
    ring_choose_eq_ascPochhammer_div]
  have e1 : (n : ℚ) + (l : ℚ) / 3 - ((n - j : ℕ) : ℚ) + 1 = (l : ℚ) / 3 + j + 1 := by
    rw [Nat.cast_sub hj]; ring
  have e2 : (n : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2 + j - (j : ℕ) + 1 =
      ((n : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2) + ((0 : ℕ) : ℚ) + 1 := by push_cast; ring
  rw [e1, e2, ascPochhammer_eval_eq_prod_Ioc, ascPochhammer_eval_eq_prod_Ioc,
    Nat.add_sub_cancel' hj, zero_add]
  have p1 : ∏ k ∈ Ioc j n, ((l : ℚ) / 3 + k) = kzNumA l n j / 3 ^ (n - j) := by
    rw [kzNumA_eq, show (3 : ℚ) ^ (n - j) = ∏ _k ∈ Ioc j n, (3 : ℚ) by
      rw [prod_const, Nat.card_Ioc], ← prod_div_distrib]
    refine prod_congr rfl fun k _ => ?_
    push_cast
    ring
  have p2 : ∏ k ∈ Ioc 0 j, ((n : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2 + k) =
      kzNumC l μ n j / 6 ^ j := by
    rw [kzNumC_eq, show (6 : ℚ) ^ j = ∏ _k ∈ Ioc 0 j, (6 : ℚ) by
      rw [prod_const, Nat.card_Ioc, Nat.sub_zero], ← prod_div_distrib]
    refine prod_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [p1, p2]
  ring

theorem kzNumA_factor_pos {l : ℤ} (hl : l = 1 ∨ l = -1) {k : ℕ} (hk : 1 ≤ k) :
    0 < 3 * (k : ℤ) + l := by omega

theorem kzNumC_factor_pos {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (n : ℕ)
    {k : ℕ} (hk : 1 ≤ k) : 0 < 6 * (k : ℤ) + (6 * n + (2 * l + 3 * μ)) := by omega

theorem kzNumA_pos {l : ℤ} (hl : l = 1 ∨ l = -1) (n j : ℕ) : 0 < kzNumA l n j := by
  rw [kzNumA_eq]
  exact prod_pos fun k hk => by
    exact_mod_cast kzNumA_factor_pos hl (k := k) (by have := (mem_Ioc.mp hk).1; omega)

theorem kzNumC_pos {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (n j : ℕ) :
    0 < kzNumC l μ n j := by
  rw [kzNumC_eq]
  exact prod_pos fun k hk => by
    exact_mod_cast kzNumC_factor_pos hl hμ n (k := k) (by have := (mem_Ioc.mp hk).1; omega)

/-- The valuation of a coefficient of `y_n`. -/
theorem padicValRat_kz_coeff {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    {n j : ℕ} (hj : j ≤ n) (p : ℕ) [Fact p.Prime] :
    (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n).coeff j ≠ 0 ∧
      padicValRat p ((jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n).coeff j) =
        padicValRat p (kzNumA l n j) + padicValRat p (kzNumC l μ n j) -
          ((n - j : ℕ) : ℤ) * padicValRat p 3 - (j : ℤ) * padicValRat p 6 -
          padicValRat p ((n - j).factorial : ℚ) - padicValRat p (j.factorial : ℚ) := by
  rw [kz_coeff_eq_prod l μ hj]
  have hA := (kzNumA_pos hl n j).ne'
  have hC := (kzNumC_pos hl hμ n j).ne'
  have hs : ((-1 : ℚ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : ((3 : ℚ) ^ (n - j)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h6 : ((6 : ℚ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hf1 : ((n - j).factorial : ℚ) ≠ 0 := by exact_mod_cast (n - j).factorial_ne_zero
  have hf2 : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hnum : (-1 : ℚ) ^ j * kzNumA l n j * kzNumC l μ n j ≠ 0 :=
    mul_ne_zero (mul_ne_zero hs hA) hC
  have hden : (3 : ℚ) ^ (n - j) * 6 ^ j * ((n - j).factorial : ℚ) * (j.factorial : ℚ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h3 h6) hf1) hf2
  refine ⟨div_ne_zero hnum hden, ?_⟩
  rw [padicValRat.div hnum hden, padicValRat.mul (mul_ne_zero hs hA) hC, padicValRat.mul hs hA,
    padicValRat.mul (mul_ne_zero (mul_ne_zero h3 h6) hf1) hf2,
    padicValRat.mul (mul_ne_zero h3 h6) hf1, padicValRat.mul h3 h6, padicValRat.pow,
    padicValRat.pow, padicValRat.pow, padicValRat.neg, padicValRat.one]
  ring

theorem padicValRat_two_eq (p : ℕ) [hp : Fact p.Prime] :
    padicValRat p 2 = if p = 2 then 1 else 0 := by
  rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
  split_ifs with h
  · subst h; exact_mod_cast padicValNat.self (by norm_num : 1 < 2)
  · exact_mod_cast padicValNat.eq_zero_of_not_dvd
      (fun hd => h ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hd))

theorem padicValRat_three_eq (p : ℕ) [hp : Fact p.Prime] :
    padicValRat p 3 = if p = 3 then 1 else 0 := by
  rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
  split_ifs with h
  · subst h; exact_mod_cast padicValNat.self (by norm_num : 1 < 3)
  · exact_mod_cast padicValNat.eq_zero_of_not_dvd
      (fun hd => h ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp hd))

theorem padicValRat_six_eq (p : ℕ) [Fact p.Prime] :
    padicValRat p 6 = padicValRat p 2 + padicValRat p 3 := by
  rw [show (6 : ℚ) = 2 * 3 by norm_num, padicValRat.mul (by norm_num) (by norm_num)]

theorem padicValRat_factorial_le_factorial (p : ℕ) [Fact p.Prime] {m n : ℕ} (h : m ≤ n) :
    padicValRat p (m.factorial : ℚ) ≤ padicValRat p (n.factorial : ℚ) := by
  rw [padicValRat.of_nat, padicValRat.of_nat]
  exact_mod_cast (padicValNat_dvd_iff_le (p := p) n.factorial_ne_zero).mp
    (pow_padicValNat_dvd.trans (Nat.factorial_dvd_factorial h))

theorem padicValRat_factorial_add_le (p : ℕ) [Fact p.Prime] {n j : ℕ} (hj : j ≤ n) :
    padicValRat p ((n - j).factorial : ℚ) + padicValRat p (j.factorial : ℚ) ≤
      padicValRat p (n.factorial : ℚ) := by
  rw [padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat]
  have hd := Nat.factorial_mul_factorial_dvd_factorial hj
  have h := (padicValNat_dvd_iff_le (p := p) n.factorial_ne_zero).mp (pow_padicValNat_dvd.trans hd)
  rw [padicValNat.mul j.factorial_ne_zero (n - j).factorial_ne_zero] at h
  exact_mod_cast (show padicValNat p (n - j).factorial + padicValNat p j.factorial ≤
    padicValNat p n.factorial by omega)

/-- `v_p(A_j) ≥ v_p((n-j)!)` for `p ≠ 3`. -/
theorem factorial_le_padicValRat_kzNumA {l : ℤ} (hl : l = 1 ∨ l = -1) {p : ℕ} [hp : Fact p.Prime]
    (hp3 : p ≠ 3) {n j : ℕ} (hj : j ≤ n) :
    padicValRat p ((n - j).factorial : ℚ) ≤ padicValRat p (kzNumA l n j) := by
  have hd : ¬ p ∣ 3 := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp h)
  have h := padicValRat_factorial_le_prod_affine (p := p) (d := 3) hd l hj
    (fun k hk => by
      have := (mem_Ioc.mp hk).1
      push_cast
      omega)
  simp only [Nat.cast_ofNat] at h
  rw [kzNumA_eq]
  exact h

/-- `v_p(C_j) ≥ v_p(j!)` for `p ≠ 2, 3`. -/
theorem factorial_le_padicValRat_kzNumC {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (n j : ℕ) :
    padicValRat p (j.factorial : ℚ) ≤ padicValRat p (kzNumC l μ n j) := by
  have hd : ¬ p ∣ 6 := by
    intro h
    rw [show (6 : ℕ) = 2 * 3 by norm_num] at h
    rcases (Nat.Prime.dvd_mul hp.out).mp h with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp h)
  have h := padicValRat_factorial_le_prod_affine (p := p) (d := 6) hd
    (6 * (n : ℤ) + (2 * l + 3 * μ)) (Nat.zero_le j)
    (fun k hk => by
      have := (mem_Ioc.mp hk).1
      push_cast
      omega)
  simp only [Nat.cast_ofNat, Nat.sub_zero] at h
  rw [kzNumC_eq]
  exact h

theorem padicValRat_kzNumA_three {l : ℤ} (hl : l = 1 ∨ l = -1) (n j : ℕ) :
    padicValRat 3 (kzNumA l n j) = 0 := by
  rw [kzNumA_eq]
  refine padicValRat_prod_eq_zero_of_not_dvd _ _ (fun k hk => ?_) (fun k _ => ?_)
  · have := (mem_Ioc.mp hk).1; omega
  · push_cast; omega

theorem padicValRat_kzNumC_two {l μ : ℤ} (hμ : μ = 1 ∨ μ = -1) (n j : ℕ) :
    padicValRat 2 (kzNumC l μ n j) = 0 := by
  rw [kzNumC_eq]
  refine padicValRat_prod_eq_zero_of_not_dvd _ _ (fun k _ => ?_) (fun k _ => ?_)
  · omega
  · push_cast; omega

theorem padicValRat_kzNumC_three {l μ : ℤ} (hl : l = 1 ∨ l = -1) (n j : ℕ) :
    padicValRat 3 (kzNumC l μ n j) = 0 := by
  rw [kzNumC_eq]
  refine padicValRat_prod_eq_zero_of_not_dvd _ _ (fun k _ => ?_) (fun k _ => ?_)
  · omega
  · push_cast; omega

theorem kzNumA_self (l : ℤ) (n : ℕ) : kzNumA l n n = 1 := by
  rw [kzNumA_eq, Finset.Ioc_self, prod_empty]

theorem padicValRat_kzKappa (p : ℕ) [Fact p.Prime] (n : ℕ) :
    padicValRat p (kzKappa n : ℚ) =
      ((n + padicValNat 2 n.factorial : ℕ) : ℤ) * padicValRat p 2 +
        ((n + padicValNat 3 n.factorial : ℕ) : ℤ) * padicValRat p 3 := by
  rw [kzKappa_eq]
  push_cast
  rw [padicValRat.mul (by positivity) (by positivity), padicValRat.pow, padicValRat.pow]
  push_cast
  ring

theorem kzKappa_pos (n : ℕ) : 0 < kzKappa n := by
  rw [kzKappa_eq]; positivity

/-- **Integrality of `κ_n y_n`.** Every coefficient `κ_n [t^j] y_n` has nonnegative valuation
at every prime; for the leading coefficient the valuations at `2` and `3` vanish. -/
theorem padicValRat_kzKappa_mul_coeff {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    {n j : ℕ} (hj : j ≤ n) (p : ℕ) [hp : Fact p.Prime] :
    (kzKappa n : ℚ) * (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n).coeff j ≠ 0 ∧
    0 ≤ padicValRat p ((kzKappa n : ℚ) * (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n).coeff j) ∧
    (j = n → (p = 2 ∨ p = 3) →
      padicValRat p ((kzKappa n : ℚ) * (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n).coeff j)
        = 0) := by
  obtain ⟨hc0, hc⟩ := padicValRat_kz_coeff hl hμ hj p
  have hk0 : (kzKappa n : ℚ) ≠ 0 := by exact_mod_cast (kzKappa_pos n).ne'
  refine ⟨mul_ne_zero hk0 hc0, ?_⟩
  rw [padicValRat.mul hk0 hc0, hc, padicValRat_kzKappa, padicValRat_six_eq, padicValRat_two_eq,
    padicValRat_three_eq]
  have hfac := padicValRat_factorial_add_le p hj
  have hfn := padicValRat_factorial_le_factorial p hj
  have hf0 : 0 ≤ padicValRat p ((n - j).factorial : ℚ) := by
    rw [padicValRat.of_nat]; exact Int.natCast_nonneg _
  have hfj0 : 0 ≤ padicValRat p (j.factorial : ℚ) := by
    rw [padicValRat.of_nat]; exact Int.natCast_nonneg _
  by_cases hp2 : p = 2
  · subst hp2
    have hA := factorial_le_padicValRat_kzNumA hl (p := 2) (by norm_num) hj
    have hC := padicValRat_kzNumC_two (l := l) hμ n j
    simp only [ite_eq_right (show (2 : ℕ) ≠ 3 by norm_num)]
    rw [hC]
    have hjn' : (j : ℤ) ≤ n := by exact_mod_cast hj
    refine ⟨?_, fun hjn _ => ?_⟩
    · push_cast
      linarith
    · subst hjn
      rw [kzNumA_self, padicValRat.one, Nat.sub_self, Nat.factorial_zero, Nat.cast_one,
        padicValRat.one]
      push_cast
      ring
  by_cases hp3 : p = 3
  · subst hp3
    have hA := padicValRat_kzNumA_three hl n j
    have hC := padicValRat_kzNumC_three (μ := μ) hl n j
    simp only [ite_eq_right (show (3 : ℕ) ≠ 2 by norm_num)]
    rw [hA, hC]
    refine ⟨?_, fun hjn _ => ?_⟩
    · push_cast
      have : ((n - j : ℕ) : ℤ) + j = n := by omega
      linarith
    · subst hjn
      rw [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, padicValRat.one]
      push_cast
      ring
  · have hA := factorial_le_padicValRat_kzNumA hl (p := p) hp3 hj
    have hC := factorial_le_padicValRat_kzNumC hl hμ (p := p) hp2 hp3 n j
    refine ⟨?_, fun _ h23 => (h23.elim hp2 hp3).elim⟩
    simp only [hp2, hp3, ite_false]
    push_cast
    linarith

/-- A rational number with nonnegative valuation at every prime is an integer. -/
theorem den_eq_one_of_padicValRat_nonneg {x : ℚ} (h : ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p x) :
    x.den = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have : Fact p.Prime := ⟨hp⟩
  have hx := h p hp
  rw [padicValRat_def] at hx
  have hnum : ¬ (p : ℤ) ∣ x.num := by
    intro hdvd
    have h1 : p ∣ x.num.natAbs := Int.natCast_dvd.mp hdvd
    have h2 := Nat.dvd_gcd h1 hpd
    rw [x.reduced.gcd_eq_one] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  rw [padicValInt.eq_zero_of_not_dvd hnum] at hx
  have := one_le_padicValNat_of_dvd x.den_pos.ne' hpd
  omega

theorem kzKappa_mul_coeff_den {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    {n j : ℕ} (hj : j ≤ n) :
    ((kzKappa n : ℚ) * (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n).coeff j).den = 1 :=
  den_eq_one_of_padicValRat_nonneg fun p hp => by
    have : Fact p.Prime := ⟨hp⟩
    exact (padicValRat_kzKappa_mul_coeff hl hμ hj p).2.1

/-- **Lemma 4.1, integrality**: `kzScaled l μ n` is `κ_n y_n`. -/
theorem map_kzScaled {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    (kzScaled l μ n).map (Int.castRingHom ℚ) =
      C (kzKappa n : ℚ) * jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n := by
  ext j
  rw [coeff_map, coeff_C_mul, kzScaled_eq, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  by_cases hj : j ≤ n
  · rw [ite_eq_left (mem_range.mpr (Nat.lt_succ_of_le hj)), eq_intCast,
      Rat.coe_int_num_of_den_eq_one (kzKappa_mul_coeff_den hl hμ hj)]
  · rw [ite_eq_right (by rw [mem_range]; omega), map_zero,
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_jacobiShifted_le _ _ n)
        (by omega)), mul_zero]

theorem coeff_kzScaled {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (n j : ℕ) :
    ((kzScaled l μ n).coeff j : ℚ) =
      (kzKappa n : ℚ) * (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n).coeff j := by
  have h := congrArg (fun P => P.coeff j) (map_kzScaled hl hμ n)
  simpa only [coeff_map, eq_intCast, coeff_C_mul] using h

theorem natDegree_kzScaled {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    (kzScaled l μ n).natDegree = n := by
  rw [← natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective,
    map_kzScaled hl hμ n, natDegree_C_mul (by exact_mod_cast (kzKappa_pos n).ne')]
  exact natDegree_eq_of_le_of_coeff_ne_zero (natDegree_jacobiShifted_le _ _ n)
    (padicValRat_kz_coeff hl hμ le_rfl 2).1

theorem kzScaled_ne_zero {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    kzScaled l μ n ≠ 0 := by
  intro h0
  have h := coeff_kzScaled hl hμ n n
  rw [h0, coeff_zero, Int.cast_zero] at h
  exact (padicValRat_kzKappa_mul_coeff hl hμ (le_refl n) 2).1 h.symm

/-- An integer whose valuation at `p` vanishes is prime to `p`. -/
theorem not_dvd_of_padicValRat_eq_zero {p : ℕ} [Fact p.Prime] {z : ℤ} (hz : z ≠ 0)
    (h : padicValRat p (z : ℚ) = 0) : ¬ (p : ℤ) ∣ z := by
  intro hd
  rw [padicValRat.of_int] at h
  have := (padicValInt_dvd_iff 1 z).mp (by rw [pow_one]; exact hd)
  rcases this with h0 | h1
  · exact hz h0
  · omega

theorem not_dvd_leadingCoeff_kzScaled {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (n : ℕ) {p : ℕ} (hp : p = 2 ∨ p = 3) : ¬ (p : ℤ) ∣ (kzScaled l μ n).leadingCoeff := by
  have : Fact p.Prime := ⟨by rcases hp with rfl | rfl; exacts [Nat.prime_two, Nat.prime_three]⟩
  rw [← coeff_natDegree, natDegree_kzScaled hl hμ n]
  have h := coeff_kzScaled hl hμ n n
  have hne := (padicValRat_kzKappa_mul_coeff hl hμ (le_refl n) p).1
  have hv := (padicValRat_kzKappa_mul_coeff hl hμ (le_refl n) p).2.2 rfl hp
  rw [← h] at hne hv
  exact not_dvd_of_padicValRat_eq_zero (fun h0 => hne (by rw [h0, Int.cast_zero])) hv

theorem kzContent_intCast (l μ : ℤ) (n : ℕ) :
    ((kzContent l μ n : ℕ) : ℤ) = (kzScaled l μ n).content := by
  rw [kzContent_eq, Int.natAbs_of_nonneg (Int.nonneg_of_normalize_eq_self normalize_content)]

theorem leadingCoeff_kzScaled_eq (l μ : ℤ) (n : ℕ) :
    (kzScaled l μ n).leadingCoeff =
      (kzContent l μ n : ℤ) * (kzPrimitive l μ n).leadingCoeff := by
  conv_lhs => rw [eq_C_content_mul_primPart (kzScaled l μ n)]
  rw [leadingCoeff_mul, leadingCoeff_C, kzContent_intCast, kzPrimitive_eq]

theorem kzContent_pos {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    0 < kzContent l μ n := by
  rw [kzContent_eq]
  exact Int.natAbs_pos.mpr (content_eq_zero_iff.not.mpr (kzScaled_ne_zero hl hμ n))

/-- `H_n = (κ_n / g_n) y_n`. -/
theorem map_kzPrimitive {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    (kzPrimitive l μ n).map (Int.castRingHom ℚ) =
      C ((kzKappa n : ℚ) / kzContent l μ n) * jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n := by
  have hg : ((kzContent l μ n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (kzContent_pos hl hμ n).ne'
  have h := congrArg (Polynomial.map (Int.castRingHom ℚ))
    (eq_C_content_mul_primPart (kzScaled l μ n))
  rw [Polynomial.map_mul, Polynomial.map_C, eq_intCast, ← kzContent_intCast, Int.cast_natCast,
    map_kzScaled hl hμ n, ← kzPrimitive_eq] at h
  calc (kzPrimitive l μ n).map (Int.castRingHom ℚ) =
        C ((kzContent l μ n : ℚ)⁻¹) *
          (C (kzContent l μ n : ℚ) * (kzPrimitive l μ n).map (Int.castRingHom ℚ)) := by
        rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hg, C_1, one_mul]
    _ = C ((kzContent l μ n : ℚ)⁻¹) *
          (C (kzKappa n : ℚ) * jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n) := by rw [← h]
    _ = C ((kzKappa n : ℚ) / kzContent l μ n) *
          jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n := by
        rw [← mul_assoc, ← C_mul, div_eq_inv_mul (kzKappa n : ℚ) (kzContent l μ n : ℚ)]

/-- **Lemma 4.1.** For `λ, μ ∈ {-1,1}`: `κ_n y_n` is integral, `g_n > 0`,
`H_n = (κ_n/g_n) y_n` is a primitive integer polynomial of degree `n` whose leading coefficient
is prime to `6`, and `(g_n, 6) = 1`. -/
theorem kanekoZagier_primitive_normalization {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    (kzScaled l μ n).map (Int.castRingHom ℚ) =
        C (kzKappa n : ℚ) * jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n ∧
      0 < kzContent l μ n ∧
      (kzPrimitive l μ n).map (Int.castRingHom ℚ) =
        C ((kzKappa n : ℚ) / kzContent l μ n) * jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n ∧
      (kzPrimitive l μ n).IsPrimitive ∧ (kzPrimitive l μ n).natDegree = n ∧
      IsCoprime (kzPrimitive l μ n).leadingCoeff 6 ∧ Nat.Coprime (kzContent l μ n) 6 := by
  have h2 := not_dvd_leadingCoeff_kzScaled hl hμ n (p := 2) (Or.inl rfl)
  have h3 := not_dvd_leadingCoeff_kzScaled hl hμ n (p := 3) (Or.inr rfl)
  rw [leadingCoeff_kzScaled_eq] at h2 h3
  push_cast at h2 h3
  have hH2 : ¬ (2 : ℤ) ∣ (kzPrimitive l μ n).leadingCoeff := fun h => h2 (dvd_mul_of_dvd_right h _)
  have hH3 : ¬ (3 : ℤ) ∣ (kzPrimitive l μ n).leadingCoeff := fun h => h3 (dvd_mul_of_dvd_right h _)
  have hg2 : ¬ 2 ∣ kzContent l μ n := fun h => h2 (dvd_mul_of_dvd_left (by exact_mod_cast h) _)
  have hg3 : ¬ 3 ∣ kzContent l μ n := fun h => h3 (dvd_mul_of_dvd_left (by exact_mod_cast h) _)
  refine ⟨map_kzScaled hl hμ n, kzContent_pos hl hμ n, map_kzPrimitive hl hμ n, ?_, ?_, ?_, ?_⟩
  · rw [kzPrimitive_eq]; exact isPrimitive_primPart _
  · rw [kzPrimitive_eq, natDegree_primPart, natDegree_kzScaled hl hμ n]
  · rw [show (6 : ℤ) = 2 * 3 by norm_num]
    exact IsCoprime.mul_right (Int.prime_two.coprime_iff_not_dvd.mpr hH2).symm
      (Int.prime_three.coprime_iff_not_dvd.mpr hH3).symm
  · rw [show (6 : ℕ) = 2 * 3 by norm_num]
    exact Nat.Coprime.mul_right
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hg2))
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hg3))

theorem isPrimitive_kzPrimitive {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (n : ℕ) : (kzPrimitive l μ n).IsPrimitive :=
  (kanekoZagier_primitive_normalization hl hμ n).2.2.2.1

theorem natDegree_kzPrimitive {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    (kzPrimitive l μ n).natDegree = n :=
  (kanekoZagier_primitive_normalization hl hμ n).2.2.2.2.1

theorem isCoprime_leadingCoeff_kzPrimitive_six {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) (n : ℕ) : IsCoprime (kzPrimitive l μ n).leadingCoeff 6 :=
  (kanekoZagier_primitive_normalization hl hμ n).2.2.2.2.2.1

theorem coprime_kzContent_six {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    Nat.Coprime (kzContent l μ n) 6 :=
  (kanekoZagier_primitive_normalization hl hμ n).2.2.2.2.2.2

/-! ### The size of `κ_n` -/

/-- The base-`b` digit sum of `n ≠ 0` is at most `(b - 1)(⌊log_b n⌋ + 1)`. -/
theorem digits_sum_le_mul_log {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) :
    (b.digits n).sum ≤ (b - 1) * (Nat.log b n + 1) := by
  have h := List.sum_le_length_nsmul (b.digits n) (b - 1)
    (fun x hx => Nat.le_sub_one_of_lt (Nat.digits_lt_base hb hx))
  rw [Nat.length_digits b n hb hn, smul_eq_mul] at h
  linarith

theorem natLog_mul_log_le {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) :
    (Nat.log b n : ℝ) * Real.log b ≤ Real.log n := by
  have h : ((b ^ Nat.log b n : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.pow_log_le_self b hn
  have h' := Real.log_le_log (Nat.cast_pos.mpr (pow_pos (by omega) _)) h
  rwa [Nat.cast_pow, Real.log_pow] at h'

/-- **Lemma 4.1, size of `κ_n`**: `log κ_n = (2 log 2 + (3/2) log 3) n + O(log n)`. -/
theorem log_kzKappa_sub_isBigO :
    (fun n : ℕ => Real.log (kzKappa n) - (2 * Real.log 2 + 3 / 2 * Real.log 3) * n)
      =O[atTop] (fun n : ℕ => Real.log n) := by
  refine IsBigO.of_bound 3 ?_
  filter_upwards [eventually_ge_atTop 6] with n hn
  have hn0 : n ≠ 0 := by omega
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hl3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have h6 : Real.log 2 + Real.log 3 ≤ Real.log n := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num; exact_mod_cast hn)
  have hlogk : Real.log (kzKappa n : ℝ) =
      ((n : ℝ) + padicValNat 2 n.factorial) * Real.log 2 +
        ((n : ℝ) + padicValNat 3 n.factorial) * Real.log 3 := by
    rw [kzKappa_eq]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hL2 : padicValNat 2 n.factorial + (Nat.digits 2 n).sum = n := by
    have h := sub_one_mul_padicValNat_factorial (p := 2) n
    have hs := Nat.digit_sum_le 2 n
    omega
  have hL3 : 2 * padicValNat 3 n.factorial + (Nat.digits 3 n).sum = n := by
    have h := sub_one_mul_padicValNat_factorial (p := 3) n
    have hs := Nat.digit_sum_le 3 n
    omega
  have hL2' : (padicValNat 2 n.factorial : ℝ) = n - (Nat.digits 2 n).sum := by
    have : (padicValNat 2 n.factorial : ℝ) + (Nat.digits 2 n).sum = n := by exact_mod_cast hL2
    linarith
  have hL3' : (padicValNat 3 n.factorial : ℝ) = (n - (Nat.digits 3 n).sum) / 2 := by
    have : 2 * (padicValNat 3 n.factorial : ℝ) + (Nat.digits 3 n).sum = n := by
      exact_mod_cast hL3
    linarith
  set s2 : ℝ := ((Nat.digits 2 n).sum : ℝ) with hs2
  set s3 : ℝ := ((Nat.digits 3 n).sum : ℝ) with hs3
  have hdiff : Real.log (kzKappa n : ℝ) - (2 * Real.log 2 + 3 / 2 * Real.log 3) * n =
      -(s2 * Real.log 2) - s3 / 2 * Real.log 3 := by
    rw [hlogk, hL2', hL3']
    ring
  have hd2 : s2 ≤ (Nat.log 2 n : ℝ) + 1 := by
    have := digits_sum_le_mul_log (b := 2) (by norm_num) hn0
    rw [hs2]
    exact_mod_cast (show (Nat.digits 2 n).sum ≤ Nat.log 2 n + 1 by omega)
  have hd3 : s3 / 2 ≤ (Nat.log 3 n : ℝ) + 1 := by
    have := digits_sum_le_mul_log (b := 3) (by norm_num) hn0
    have h' : s3 ≤ 2 * ((Nat.log 3 n : ℝ) + 1) := by
      rw [hs3]
      exact_mod_cast (show (Nat.digits 3 n).sum ≤ 2 * (Nat.log 3 n + 1) by omega)
    linarith
  have p2 : s2 * Real.log 2 ≤ (Nat.log 2 n : ℝ) * Real.log 2 + Real.log 2 := by
    have := mul_le_mul_of_nonneg_right hd2 hl2.le
    linarith [show ((Nat.log 2 n : ℝ) + 1) * Real.log 2 =
      (Nat.log 2 n : ℝ) * Real.log 2 + Real.log 2 by ring]
  have p3 : s3 / 2 * Real.log 3 ≤ (Nat.log 3 n : ℝ) * Real.log 3 + Real.log 3 := by
    have := mul_le_mul_of_nonneg_right hd3 hl3.le
    linarith [show ((Nat.log 3 n : ℝ) + 1) * Real.log 3 =
      (Nat.log 3 n : ℝ) * Real.log 3 + Real.log 3 by ring]
  have q2 := natLog_mul_log_le (b := 2) (by norm_num) hn0
  have q3 := natLog_mul_log_le (b := 3) (by norm_num) hn0
  push_cast at q2 q3
  have hs2n : 0 ≤ s2 * Real.log 2 := mul_nonneg (by rw [hs2]; positivity) hl2.le
  have hs3n : 0 ≤ s3 / 2 * Real.log 3 := mul_nonneg (by rw [hs3]; positivity) hl3.le
  have hlogn : 0 ≤ Real.log n := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogn, hdiff, abs_le]
  constructor <;> linarith

end ArithmeticOfJacobiPolynomials
