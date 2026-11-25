/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.FiniteRangeReduction

/-!
# Proposition B.2: the endpoint and digit terms

For `1 ≤ n ≤ 250000` and `λ, μ ∈ {-1, 1}` this file bounds the integers `c_2`, `c_3` of
Proposition B.2 and proves the first condition of (Appendix B.2).

* `card_filter_dvd_affine_le`: `#{1 ≤ j ≤ n : q ∣ A j + B} ≤ ⌊n/q⌋ + 1` for `A` prime to `q`;
* `sum_padicValInt_affine_le`: `∑_{j=1}^n v_p(A j + B) ≤ v_p(n!) + K` when all `|A j + B|` and
  `n` are below `p^{K+1}` (Legendre's formula and a count by levels);
* `kzEndpointTwo_le`, `kzEndpointThree_le`, `kzEndpointTwo_ge`, `kzEndpointThree_ge`:
  `n + ⌊n/2⌋ ≤ D_{2,n} ≤ n + v_2(n!) + 19` and `n ≤ D_{3,n} ≤ n + v_3(n!) + 11`;
* `kzC2_ge`: `c_2 ≥ 210 n - 1515`, and `kzC3_ge`: `2 c_3 ≥ -(59 n + 1536)`;
* `abs_kzEndpoint_le`: `|D_{2,n} log 2 - D_{3,n} log 3| ≤ (9/10) n` for `100 ≤ n ≤ 250000`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Finset

/-! ### Counting along an arithmetic progression -/

/-- `#{1 ≤ j ≤ n : q ∣ A j + B} ≤ ⌊n/q⌋ + 1` when `A` is prime to `q`: the solutions are
congruent modulo `q`, so `j ↦ ⌊j/q⌋` is injective on them. -/
theorem card_filter_dvd_affine_le {q : ℕ} {A B : ℤ} (hA : IsCoprime (q : ℤ) A)
    (n : ℕ) : #((Icc 1 n).filter (fun j : ℕ => (q : ℤ) ∣ A * j + B)) ≤ n / q + 1 := by
  calc _ ≤ #(range (n / q + 1)) := by
        refine card_le_card_of_injOn (fun j => j / q) (fun j hj => ?_) (fun j hj j' hj' he => ?_)
        · have hj' := (mem_filter.mp (mem_coe.mp hj)).1
          simp only [coe_range, Set.mem_Iio]
          have := Nat.div_le_div_right (c := q) (mem_Icc.mp hj').2
          omega
        · have h1 := (mem_filter.mp (mem_coe.mp hj)).2
          have h2 := (mem_filter.mp (mem_coe.mp hj')).2
          have h3 : (q : ℤ) ∣ A * ((j : ℤ) - j') := by
            have := dvd_sub h1 h2
            rwa [show A * (j : ℤ) + B - (A * j' + B) = A * ((j : ℤ) - j') by ring] at this
          have h4 := hA.dvd_of_dvd_mul_left h3
          have h5 : j' ≡ j [MOD q] := Nat.modEq_iff_dvd.mpr h4
          have e1 := Nat.div_add_mod j q
          have e2 := Nat.div_add_mod j' q
          simp only at he
          unfold Nat.ModEq at h5
          rw [he] at e1
          omega
    _ = n / q + 1 := card_range _

section Valuations

variable {p : ℕ} [hp : Fact p.Prime]

/-- `v_p(z) = #{1 ≤ k ≤ K : p^k ∣ z}` for `0 < |z| < p^{K+1}`. -/
theorem padicValInt_eq_card {z : ℤ} (hz : z ≠ 0) {K : ℕ} (hK : z.natAbs < p ^ (K + 1)) :
    padicValInt p z = #((Icc 1 K).filter (fun k => (p : ℤ) ^ k ∣ z)) := by
  have hvK : padicValInt p z ≤ K := by
    have hd := Int.natAbs_dvd_natAbs.mpr (padicValInt_dvd (p := p) z)
    rw [Int.natAbs_pow, Int.natAbs_natCast] at hd
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hz) hd
    by_contra h
    have : p ^ (K + 1) ≤ p ^ padicValInt p z := Nat.pow_le_pow_right hp.out.pos (by omega)
    omega
  have e : (Icc 1 K).filter (fun k => (p : ℤ) ^ k ∣ z) = Icc 1 (padicValInt p z) := by
    ext k
    simp only [mem_filter, mem_Icc, padicValInt_dvd_iff, hz, false_or]
    omega
  rw [e, Nat.card_Icc]
  omega

/-- **Valuations along an arithmetic progression**: `∑_{j=1}^n v_p(A j + B) ≤ v_p(n!) + K` when
`A` is prime to `p`, the values `A j + B` are nonzero with `|A j + B| < p^{K+1}`, and
`n < p^{K+1}`. -/
theorem sum_padicValInt_affine_le {A B : ℤ} (hA : IsCoprime (p : ℤ) A) {n K : ℕ}
    (hne : ∀ j ∈ Icc 1 n, A * (j : ℤ) + B ≠ 0)
    (hlt : ∀ j ∈ Icc 1 n, (A * (j : ℤ) + B).natAbs < p ^ (K + 1)) (hnK : n < p ^ (K + 1)) :
    ∑ j ∈ Icc 1 n, padicValInt p (A * (j : ℤ) + B) ≤ padicValNat p n.factorial + K := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have e1 : ∑ j ∈ Icc 1 n, padicValInt p (A * (j : ℤ) + B) =
      ∑ k ∈ Icc 1 K, #((Icc 1 n).filter (fun j : ℕ => (p : ℤ) ^ k ∣ A * j + B)) := by
    rw [sum_congr rfl fun j hj => padicValInt_eq_card (hne j hj) (hlt j hj)]
    simp only [card_filter]
    rw [sum_comm]
  have e2 : padicValNat p n.factorial = ∑ k ∈ Icc 1 K, n / p ^ k := by
    rw [padicValNat_factorial (b := K + 1) (Nat.log_lt_of_lt_pow (by omega) hnK)]
    exact sum_congr (by ext k; simp only [mem_Ico, mem_Icc]; omega) fun _ _ => rfl
  rw [e1, e2]
  calc _ ≤ ∑ k ∈ Icc 1 K, (n / p ^ k + 1) := by
        refine sum_le_sum fun k _ => ?_
        have := card_filter_dvd_affine_le (q := p ^ k) (A := A) (B := B)
          (by rw [Nat.cast_pow]; exact hA.pow_left) n
        simpa only [Nat.cast_pow] using this
    _ = _ := by
        rw [sum_add_distrib, sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
        omega

end Valuations

/-! ### The endpoint terms -/

theorem isCoprime_two_three : IsCoprime ((2 : ℕ) : ℤ) 3 := ⟨-1, 1, by norm_num⟩

theorem isCoprime_three_two : IsCoprime ((3 : ℕ) : ℤ) 2 := ⟨1, -1, by norm_num⟩

/-- `D_{2,n} ≤ n + v_2(n!) + 19` for `n ≤ 250000`. -/
theorem kzEndpointTwo_le {l : ℤ} (hl : l = 1 ∨ l = -1) {n : ℕ} (hn : n ≤ 250000) :
    kzEndpointTwo l n ≤ n + padicValNat 2 n.factorial + 19 := by
  have h := sum_padicValInt_affine_le (p := 2) (A := 3) (B := l) (n := n) (K := 19)
    isCoprime_two_three (fun j hj => by have := (mem_Icc.mp hj).1; omega)
    (fun j hj => by
      have := (mem_Icc.mp hj).2
      rw [show (2 : ℕ) ^ (19 + 1) = 1048576 by norm_num]
      omega)
    (by rw [show (2 : ℕ) ^ (19 + 1) = 1048576 by norm_num]; omega)
  rw [kzEndpointTwo_eq]
  omega

/-- `D_{3,n} ≤ n + v_3(n!) + 11` for `n ≤ 250000`. -/
theorem kzEndpointThree_le {μ : ℤ} (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : n ≤ 250000) :
    kzEndpointThree μ n ≤ n + padicValNat 3 n.factorial + 11 := by
  have h := sum_padicValInt_affine_le (p := 3) (A := 2) (B := μ) (n := n) (K := 11)
    isCoprime_three_two (fun j hj => by have := (mem_Icc.mp hj).1; omega)
    (fun j hj => by
      have := (mem_Icc.mp hj).2
      rw [show (3 : ℕ) ^ (11 + 1) = 531441 by norm_num]
      omega)
    (by rw [show (3 : ℕ) ^ (11 + 1) = 531441 by norm_num]; omega)
  rw [kzEndpointThree_eq]
  omega

/-- One of two consecutive terms `3j + λ` is even. -/
theorem one_le_padicValInt_two_add {l : ℤ} (hl : l = 1 ∨ l = -1) (m : ℕ) :
    1 ≤ padicValInt 2 (3 * ((m + 1 : ℕ) : ℤ) + l) +
      padicValInt 2 (3 * ((m + 1 + 1 : ℕ) : ℤ) + l) := by
  by_cases h : (2 : ℤ) ∣ 3 * ((m + 1 : ℕ) : ℤ) + l
  · have h2 : ((2 : ℕ) : ℤ) ^ 1 ∣ 3 * ((m + 1 : ℕ) : ℤ) + l := by simpa using h
    have := ((padicValInt_dvd_iff (p := 2) 1 _).mp h2).resolve_left (by omega)
    exact le_add_right this
  · have h' : (2 : ℤ) ∣ 3 * ((m + 1 + 1 : ℕ) : ℤ) + l := by omega
    have h2 : ((2 : ℕ) : ℤ) ^ 1 ∣ 3 * ((m + 1 + 1 : ℕ) : ℤ) + l := by simpa using h'
    have := ((padicValInt_dvd_iff (p := 2) 1 _).mp h2).resolve_left (by omega)
    exact le_add_left this

theorem half_le_sum_padicValInt_two {l : ℤ} (hl : l = 1 ∨ l = -1) : ∀ n : ℕ,
    n / 2 ≤ ∑ j ∈ Icc 1 n, padicValInt 2 (3 * (j : ℤ) + l)
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    rw [show n + 2 = n + 1 + 1 by rfl, Finset.sum_Icc_succ_top (by omega),
      Finset.sum_Icc_succ_top (by omega)]
    have ih := half_le_sum_padicValInt_two hl n
    have h1 := one_le_padicValInt_two_add hl n
    omega

/-- `D_{2,n} ≥ n + ⌊n/2⌋`. -/
theorem kzEndpointTwo_ge {l : ℤ} (hl : l = 1 ∨ l = -1) (n : ℕ) :
    n + n / 2 ≤ kzEndpointTwo l n := by
  have := half_le_sum_padicValInt_two hl n
  rw [kzEndpointTwo_eq]
  omega

/-- `D_{3,n} ≥ n`. -/
theorem kzEndpointThree_ge (μ : ℤ) (n : ℕ) : n ≤ kzEndpointThree μ n := by
  rw [kzEndpointThree_eq]
  omega

/-! ### Digit sums -/

theorem digits_two_sum_le {n : ℕ} (hn : n < 2 ^ 18) : (Nat.digits 2 n).sum ≤ 18 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp
  have h := digits_sum_le_mul_log (b := 2) (by norm_num) hn0.ne'
  have hl := Nat.log_lt_of_lt_pow hn0.ne' hn
  omega

theorem digits_three_sum_le {n : ℕ} (hn : n < 3 ^ 12) : (Nat.digits 3 n).sum ≤ 24 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp
  have h := digits_sum_le_mul_log (b := 3) (by norm_num) hn0.ne'
  have hl := Nat.log_lt_of_lt_pow hn0.ne' hn
  omega

/-! ### The integers `c_2`, `c_3` -/

/-- `c_2 ≥ 210 n - 1515` for `n ≤ 250000`. -/
theorem kzC2_ge {l : ℤ} (hl : l = 1 ∨ l = -1) {n : ℕ} (hn : n ≤ 250000) :
    210 * (n : ℤ) - 1515 ≤ kzC2 l n := by
  have hD := kzEndpointTwo_le hl hn
  have hv := sub_one_mul_padicValNat_factorial (p := 2) n
  have hs := Nat.digit_sum_le 2 n
  have hs2 := digits_two_sum_le (n := n) (by norm_num; omega)
  rw [kzC2_eq]
  norm_num at hv
  omega

/-- `2 c_3 ≥ -(59 n + 1536)` for `n ≤ 250000`. -/
theorem kzC3_ge {μ : ℤ} (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : n ≤ 250000) :
    -(59 * (n : ℤ) + 1536) ≤ 2 * kzC3 μ n := by
  have hD := kzEndpointThree_le hμ hn
  have hv := sub_one_mul_padicValNat_factorial (p := 3) n
  have hs := Nat.digit_sum_le 3 n
  have hs3 := digits_three_sum_le (n := n) (by norm_num; omega)
  have hδ : kzDelta μ ≤ 1 := by
    rw [kzDelta_eq]
    omega
  have hs3' := digits_three_sum_le (n := 2 * n + kzDelta μ) (by norm_num; omega)
  rw [kzC3_eq]
  norm_num at hv
  omega

/-- **The first condition of (Appendix B.2)**:
`|D_{2,n} log 2 - D_{3,n} log 3| ≤ (9/10) n` for `100 ≤ n ≤ 250000`. -/
theorem abs_kzEndpoint_le {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {n : ℕ}
    (hn1 : 100 ≤ n) (hn : n ≤ 250000) :
    |kzEndpointTwo l n * Real.log 2 - kzEndpointThree μ n * Real.log 3| ≤ 9 / 10 * n := by
  have h2u := kzEndpointTwo_le hl hn
  have h2l := kzEndpointTwo_ge hl n
  have h3u := kzEndpointThree_le hμ hn
  have h3l := kzEndpointThree_ge μ n
  have hv2 := sub_one_mul_padicValNat_factorial (p := 2) n
  have hv3 := sub_one_mul_padicValNat_factorial (p := 3) n
  have hs2 := Nat.digit_sum_le 2 n
  have hs3 := Nat.digit_sum_le 3 n
  norm_num at hv2 hv3
  have a2u : (kzEndpointTwo l n : ℝ) ≤ 2 * n + 19 := by
    have : kzEndpointTwo l n ≤ 2 * n + 19 := by omega
    exact_mod_cast this
  have a2l : (3 / 2 : ℝ) * n - 1 ≤ kzEndpointTwo l n := by
    have : 3 * n ≤ 2 * kzEndpointTwo l n + 2 := by omega
    have : (3 * n : ℝ) ≤ 2 * kzEndpointTwo l n + 2 := by exact_mod_cast this
    linarith
  have a3u : 2 * (kzEndpointThree μ n : ℝ) ≤ 3 * n + 22 := by
    have : 2 * kzEndpointThree μ n ≤ 3 * n + 22 := by omega
    exact_mod_cast this
  have a3l : (n : ℝ) ≤ kzEndpointThree μ n := by exact_mod_cast h3l
  have hn1' : (100 : ℝ) ≤ n := by exact_mod_cast hn1
  have l2 := Real.log_two_gt_d9
  have l2' := Real.log_two_lt_d9
  have l3 := Real.log_three_gt_d9
  have l3' := Real.log_three_lt_d9
  have l2p : (0 : ℝ) < Real.log 2 := by linarith
  have l3p : (0 : ℝ) < Real.log 3 := by linarith
  have p1 := mul_le_mul_of_nonneg_right a3u l3p.le
  have p2 := mul_le_mul_of_nonneg_right a2l l2p.le
  have p3 := mul_le_mul_of_nonneg_right a2u l2p.le
  have p4 := mul_le_mul_of_nonneg_right a3l l3p.le
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have q1 := mul_le_mul_of_nonneg_left l3'.le hn0
  have q2 := mul_le_mul_of_nonneg_left l2.le hn0
  have q3 := mul_le_mul_of_nonneg_left l2'.le hn0
  have q4 := mul_le_mul_of_nonneg_left l3.le hn0
  rw [abs_le]
  constructor <;> nlinarith

end ArithmeticOfJacobiPolynomials
