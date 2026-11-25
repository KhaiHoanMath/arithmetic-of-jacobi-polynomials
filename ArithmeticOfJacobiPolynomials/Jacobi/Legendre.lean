/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp

/-!
# Explicit form of the Legendre polynomials

From the definition `legendreP = jacobiP 0 0` we derive the Rodrigues formula
`P_N = (2^N N!)⁻¹ dᴺ/dxᴺ (x²-1)^N` and the classical explicit expansion
`P_N = 2^{-N} ∑_{k ≤ N/2} (-1)^k C(N,k) C(2N-2k,N) x^{N-2k}`, together with the degree,
the leading coefficient and the parity of `P_N`. The comparison with Mathlib's
`Polynomial.shiftedLegendre` is `legendreP_comp_one_sub_two_mul_X`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- Leibniz expansion of `dᴺ/dxᴺ (x²-1)^N`, written in the basis `(x-1)^j (x+1)^{N-j}`. -/
theorem iterate_derivative_X_sq_sub_one_pow (N : ℕ) :
    derivative^[N] ((X ^ 2 - 1 : ℚ[X]) ^ N) =
      C (N.factorial : ℚ) * ∑ j ∈ range (N + 1),
        C ((N.choose j : ℚ) ^ 2) * (X - 1) ^ j * (X + 1) ^ (N - j) := by
  have h : (X ^ 2 - 1 : ℚ[X]) ^ N = (X - C 1) ^ N * (X + C 1) ^ N := by
    rw [← mul_pow, map_one]; ring
  rw [h, iterate_derivative_mul, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj : j ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [iterate_derivative_X_sub_pow, iterate_derivative_X_add_pow, Nat.sub_sub_self hj]
  have hnat : N.choose j * (N.descFactorial (N - j) * N.descFactorial j) =
      N.factorial * N.choose j ^ 2 := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
      Nat.choose_symm hj, ← Nat.choose_mul_factorial_mul_factorial hj]
    ring
  have hcast : ((N.choose j : ℚ[X]) * ((N.descFactorial (N - j) : ℚ[X]) *
      (N.descFactorial j : ℚ[X]))) = (N.factorial : ℚ[X]) * (N.choose j : ℚ[X]) ^ 2 := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℚ[X]) hnat
  simp only [nsmul_eq_mul, map_one, map_pow, map_natCast]
  linear_combination (X - 1) ^ j * (X + 1) ^ (N - j) * hcast

/-- The Rodrigues formula `P_N = (2^N N!)⁻¹ dᴺ/dxᴺ (x²-1)^N`. -/
theorem legendreP_eq_rodrigues (N : ℕ) :
    legendreP N = C (1 / (2 ^ N * (N.factorial : ℚ))) * derivative^[N] ((X ^ 2 - 1) ^ N) := by
  rw [iterate_derivative_X_sq_sub_one_pow, ← mul_assoc, ← C_mul]
  rw [legendreP_eq, jacobiP_eq]
  simp only [add_zero, Ring.choose_natCast]
  congr 1
  · congr 1
    have : (N.factorial : ℚ) ≠ 0 := by positivity
    rw [one_div_pow]
    field_simp
  · refine sum_congr rfl fun j hj => ?_
    have hj : j ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [Nat.choose_symm hj, sq]

/-- Expansion of `dᴺ/dxᴺ (x²-1)^N` in monomials. -/
theorem iterate_derivative_X_sq_sub_one_pow_eq_sum (N : ℕ) :
    derivative^[N] ((X ^ 2 - 1 : ℚ[X]) ^ N) =
      ∑ k ∈ range (N / 2 + 1), C ((-1) ^ k * (N.choose k : ℚ) *
        ((N.factorial : ℚ) * ((2 * N - 2 * k).choose N : ℚ))) * X ^ (N - 2 * k) := by
  have h : (X ^ 2 - 1 : ℚ[X]) ^ N = ∑ k ∈ range (N + 1),
      C ((-1) ^ k * (N.choose k : ℚ)) * X ^ (2 * N - 2 * k) := by
    rw [show (X ^ 2 - 1 : ℚ[X]) = -1 + X ^ 2 by ring, add_pow]
    refine sum_congr rfl fun k hk => ?_
    have hk : k ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [← pow_mul, show 2 * (N - k) = 2 * N - 2 * k by omega]
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  have hsub : range (N / 2 + 1) ⊆ range (N + 1) := fun k hk => by
    simp only [mem_range] at hk ⊢; omega
  rw [h, iterate_derivative_sum, ← sum_subset hsub]
  · refine sum_congr rfl fun k hk => ?_
    have hk : k ≤ N / 2 := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul, ← mul_assoc, ← C_mul,
      Nat.descFactorial_eq_factorial_mul_choose, show 2 * N - 2 * k - N = N - 2 * k by omega]
    push_cast
    ring_nf
  · intro k hk' hk
    have hk : N / 2 < k := by simpa using hk
    have hk' : k ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hk')
    rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul,
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp

/-- **Explicit form of the Legendre polynomials.**
`P_N = 2^{-N} ∑_{k ≤ N/2} (-1)^k C(N,k) C(2N-2k,N) x^{N-2k}`. -/
theorem legendreP_explicit (N : ℕ) :
    legendreP N = C (1 / 2 ^ N) * ∑ k ∈ range (N / 2 + 1),
      C ((-1) ^ k * (N.choose k : ℚ) * ((2 * N - 2 * k).choose N : ℚ)) * X ^ (N - 2 * k) := by
  rw [legendreP_eq_rodrigues, iterate_derivative_X_sq_sub_one_pow_eq_sum, mul_sum, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  simp only [← mul_assoc, ← C_mul]
  congr 2
  have : (N.factorial : ℚ) ≠ 0 := by positivity
  field_simp

/-- The explicit form of `P_N`, with the coefficients inside the sum. -/
theorem legendreP_eq_sum (N : ℕ) :
    legendreP N = ∑ k ∈ range (N / 2 + 1),
      C ((-1) ^ k * (N.choose k : ℚ) * ((2 * N - 2 * k).choose N : ℚ) / 2 ^ N) *
        X ^ (N - 2 * k) := by
  rw [legendreP_explicit, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ← C_mul]
  congr 2
  ring

/-- The coefficient of `x^{N-2k}` in `P_N`, for `k ≤ N/2`. -/
theorem coeff_legendreP_sub_two_mul (N k : ℕ) (hk : k ≤ N / 2) :
    (legendreP N).coeff (N - 2 * k) =
      (-1) ^ k * (N.choose k : ℚ) * ((2 * N - 2 * k).choose N : ℚ) / 2 ^ N := by
  rw [legendreP_eq_sum, finsetSum_coeff, sum_eq_single k]
  · simp only [coeff_C_mul_X_pow, ite_true]
  · intro j hj hjk
    have hj : j ≤ N / 2 := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [coeff_C_mul_X_pow, ite_eq_right_iff.mpr fun h => absurd h (by omega)]
  · intro h; exact absurd (mem_range.mpr (Nat.lt_succ_of_le hk)) h

/-- The coefficients of `P_N` vanish in degrees of the wrong parity. -/
theorem coeff_legendreP_eq_zero_of_odd (N i : ℕ) (h : Odd (N + i)) :
    (legendreP N).coeff i = 0 := by
  rw [legendreP_eq_sum, finsetSum_coeff]
  refine sum_eq_zero fun j hj => ?_
  have hj : j ≤ N / 2 := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [coeff_C_mul_X_pow, ite_eq_right_iff.mpr fun h' => absurd h' ?_]
  rintro rfl
  obtain ⟨t, ht⟩ := h
  omega

theorem natDegree_legendreP_le (N : ℕ) : (legendreP N).natDegree ≤ N := by
  rw [legendreP_eq_sum]
  exact natDegree_sum_le_of_forall_le _ _ fun k _ =>
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)

/-- The leading coefficient of `P_N` is `C(2N, N) / 2^N`. -/
theorem coeff_legendreP_self (N : ℕ) :
    (legendreP N).coeff N = ((2 * N).choose N : ℚ) / 2 ^ N := by
  have := coeff_legendreP_sub_two_mul N 0 (Nat.zero_le _)
  simpa using this

/-- `deg P_N = N`. -/
theorem natDegree_legendreP (N : ℕ) : (legendreP N).natDegree = N := by
  refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_legendreP_le N) ?_
  rw [coeff_legendreP_self]
  have : ((2 * N).choose N : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  exact div_ne_zero this (by positivity)

theorem leadingCoeff_legendreP (N : ℕ) :
    (legendreP N).leadingCoeff = ((2 * N).choose N : ℚ) / 2 ^ N := by
  rw [leadingCoeff, natDegree_legendreP, coeff_legendreP_self]

theorem legendreP_ne_zero (N : ℕ) : legendreP N ≠ 0 := by
  intro h
  have := leadingCoeff_legendreP N
  rw [h, leadingCoeff_zero] at this
  have h2 : ((2 * N).choose N : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  exact div_ne_zero h2 (by positivity) this.symm

/-- Parity: `P_N(-x) = (-1)^N P_N(x)`. -/
theorem legendreP_comp_neg_X (N : ℕ) :
    (legendreP N).comp (-X) = C ((-1) ^ N) * legendreP N := by
  rw [legendreP_eq_sum, Polynomial.sum_comp, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk : k ≤ N / 2 := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [mul_comp, C_comp, X_pow_comp, neg_pow (X : ℚ[X])]
  have : (-1 : ℚ) ^ N = (-1) ^ (N - 2 * k) := by
    have h1 : (-1 : ℚ) ^ N = (-1) ^ (N - 2 * k) * ((-1) ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    rw [h1]; norm_num
  rw [this]
  simp only [map_pow, map_neg, map_one]
  ring

/-- For odd `N`, the polynomial `P_N` is divisible by `x`. -/
theorem X_dvd_legendreP_of_odd {N : ℕ} (hN : Odd N) : X ∣ legendreP N := by
  rw [legendreP_eq_sum]
  refine dvd_sum fun k hk => ?_
  have hk : k ≤ N / 2 := Nat.lt_succ_iff.mp (mem_range.mp hk)
  obtain ⟨t, rfl⟩ := hN
  refine Dvd.dvd.mul_left (dvd_pow_self X ?_) _
  omega

/-- `P_{2m+δ} = x^δ L_{2m+δ}` for `δ ∈ {0,1}`. -/
theorem legendreP_eq_X_pow_mul_reducedLegendre (m δ : ℕ) (hδ : δ ≤ 1) :
    legendreP (2 * m + δ) = X ^ δ * reducedLegendre m δ := by
  rw [reducedLegendre_eq]
  interval_cases δ
  · simp
  · obtain ⟨q, hq⟩ := X_dvd_legendreP_of_odd (N := 2 * m + 1) ⟨m, rfl⟩
    rw [pow_one, hq, mul_divByMonic_cancel_left _ monic_X]

/-- `deg L_{2m+δ} = 2m`. -/
theorem natDegree_reducedLegendre (m δ : ℕ) : (reducedLegendre m δ).natDegree = 2 * m := by
  rw [reducedLegendre_eq, natDegree_divByMonic _ (monic_X_pow δ), natDegree_legendreP,
    natDegree_X_pow]
  omega

/-- Explicit form of the reduced Legendre polynomial:
`L_{2m+δ} = ∑_{k=0}^m c_k x^{2(m-k)}` with `c_k` the coefficient of `x^{N-2k}` in `P_N`,
`N = 2m+δ`. -/
theorem reducedLegendre_eq_sum (m δ : ℕ) (hδ : δ ≤ 1) :
    reducedLegendre m δ = ∑ k ∈ range (m + 1),
      C ((-1) ^ k * ((2 * m + δ).choose k : ℚ) *
        ((2 * (2 * m + δ) - 2 * k).choose (2 * m + δ) : ℚ) / 2 ^ (2 * m + δ)) *
        X ^ (2 * (m - k)) := by
  have hN : (2 * m + δ) / 2 = m := by omega
  have h := legendreP_eq_sum (2 * m + δ)
  rw [hN] at h
  have h2 : legendreP (2 * m + δ) = X ^ δ * ∑ k ∈ range (m + 1),
      C ((-1) ^ k * ((2 * m + δ).choose k : ℚ) *
        ((2 * (2 * m + δ) - 2 * k).choose (2 * m + δ) : ℚ) / 2 ^ (2 * m + δ)) *
        X ^ (2 * (m - k)) := by
    rw [h, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [mul_left_comm, ← pow_add]
    congr 2
    omega
  rw [reducedLegendre_eq, h2, mul_divByMonic_cancel_left _ (monic_X_pow δ)]

/-- The integral polynomial `J_n^ε(T) = ∑_{j=0}^n C(n,j) ∏_{k=1}^n (2j+2k+ε) T^j` of (5.12). -/
noncomputable def legendreJ (ε : ℤ) (n : ℕ) : ℤ[X] :=
  ∑ j ∈ range (n + 1), C ((n.choose j : ℤ) * ∏ k ∈ Icc 1 n, (2 * (j : ℤ) + 2 * k + ε)) * X ^ j

theorem legendreJ_eq (ε : ℤ) (n : ℕ) : legendreJ ε n =
    ∑ j ∈ range (n + 1), C ((n.choose j : ℤ) * ∏ k ∈ Icc 1 n, (2 * (j : ℤ) + 2 * k + ε)) *
      X ^ j := (rfl)

/-- The product identity behind (5.13):
`2^{n+δ} ∏_{k=1}^n (2j+2k+2δ-1) (n+j+δ)! (2j+δ)! = j! (2n+2j+2δ)!`. -/
theorem two_pow_mul_prod_mul_factorial (n j δ : ℕ) (hδ : δ ≤ 1) :
    (2 : ℚ) ^ (n + δ) * (∏ k ∈ Icc 1 n, (2 * (j : ℚ) + 2 * k + 2 * δ - 1)) *
        ((n + j + δ).factorial : ℚ) * ((2 * j + δ).factorial : ℚ) =
      (j.factorial : ℚ) * ((2 * n + 2 * j + 2 * δ).factorial : ℚ) := by
  induction n with
  | zero =>
    interval_cases δ
    · simp
    · simp only [zero_add, Finset.Icc_eq_empty_of_lt one_pos, prod_empty,
        mul_one, show 2 * 0 + 2 * j + 2 * 1 = (2 * j + 1) + 1 by ring, Nat.factorial_succ,
        pow_one]
      push_cast
      ring
  | succ n ih =>
    rw [prod_Icc_succ_top (by omega), show n + 1 + δ = (n + δ) + 1 by ring,
      show n + 1 + j + δ = (n + j + δ) + 1 by ring,
      show 2 * (n + 1) + 2 * j + 2 * δ = (2 * n + 2 * j + 2 * δ + 1) + 1 by ring,
      Nat.factorial_succ (n + j + δ), Nat.factorial_succ (2 * n + 2 * j + 2 * δ + 1),
      Nat.factorial_succ (2 * n + 2 * j + 2 * δ), pow_succ]
    push_cast
    linear_combination (2 * (2 * (j : ℚ) + 2 * n + 2 * δ + 1) * (n + j + δ + 1)) * ih

/-- The scalar identity behind (5.13): the coefficient of `T^j` in `J_n^ε`, times `(-1)^j`,
equals `(-2)^n n!` times the coefficient of `x^{2j}` in `L_{2n+δ}`. -/
theorem legendreJ_coeff_identity (i j δ : ℕ) (hδ : δ ≤ 1) :
    ((j + i).choose j : ℚ) * (∏ k ∈ Icc 1 (j + i), (2 * (j : ℚ) + 2 * k + 2 * δ - 1)) *
        (-1) ^ j =
      (-2) ^ (j + i) * ((j + i).factorial : ℚ) *
        ((-1) ^ i * ((2 * (j + i) + δ).choose i : ℚ) *
          ((2 * (2 * (j + i) + δ) - 2 * i).choose (2 * (j + i) + δ) : ℚ) /
            2 ^ (2 * (j + i) + δ)) := by
  set P := ∏ k ∈ Icc 1 (j + i), (2 * (j : ℚ) + 2 * k + 2 * δ - 1)
  have H := two_pow_mul_prod_mul_factorial (j + i) j δ hδ
  rw [show j + i + j + δ = 2 * j + i + δ by ring,
    show 2 * (j + i) + 2 * j + 2 * δ = 4 * j + 2 * i + 2 * δ by ring] at H
  rw [show 2 * (2 * (j + i) + δ) - 2 * i = 4 * j + 2 * i + 2 * δ by omega]
  have hA : ((2 * (j + i) + δ).choose i : ℚ) * (i.factorial : ℚ) *
      ((2 * j + i + δ).factorial : ℚ) = ((2 * (j + i) + δ).factorial : ℚ) := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 2 * (j + i) + δ) (k := i) (by omega)
    rw [show 2 * (j + i) + δ - i = 2 * j + i + δ by omega] at this
    exact_mod_cast this
  have hB : ((4 * j + 2 * i + 2 * δ).choose (2 * (j + i) + δ) : ℚ) *
      ((2 * (j + i) + δ).factorial : ℚ) * ((2 * j + δ).factorial : ℚ) =
      ((4 * j + 2 * i + 2 * δ).factorial : ℚ) := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 4 * j + 2 * i + 2 * δ)
      (k := 2 * (j + i) + δ) (by omega)
    rw [show 4 * j + 2 * i + 2 * δ - (2 * (j + i) + δ) = 2 * j + δ by omega] at this
    exact_mod_cast this
  have hC : ((j + i).choose j : ℚ) * (j.factorial : ℚ) * (i.factorial : ℚ) =
      ((j + i).factorial : ℚ) := by
    have := Nat.choose_mul_factorial_mul_factorial (n := j + i) (k := j) (by omega)
    rw [show j + i - j = i by omega] at this
    exact_mod_cast this
  set a := ((j + i).choose j : ℚ)
  set A := ((2 * (j + i) + δ).choose i : ℚ)
  set B := ((4 * j + 2 * i + 2 * δ).choose (2 * (j + i) + δ) : ℚ)
  set f1 := ((2 * j + i + δ).factorial : ℚ)
  set f2 := ((2 * j + δ).factorial : ℚ)
  set f3 := ((2 * (j + i) + δ).factorial : ℚ)
  set e := (2 : ℚ) ^ (j + i + δ)
  have key : a * P * e * ((j.factorial : ℚ) * i.factorial * f1 * f2 * f3) =
      (j + i).factorial * A * B * ((j.factorial : ℚ) * i.factorial * f1 * f2 * f3) := by
    linear_combination (P * e * f1 * f2 * f3) * hC + ((j + i).factorial * f3) * H -
      ((j + i).factorial * j.factorial * f3) * hB -
      ((j + i).factorial * j.factorial * f3 * B * f2) * hA
  have hF : ((j.factorial : ℚ) * i.factorial * f1 * f2 * f3) ≠ 0 := by positivity
  have key2 : a * P = (j + i).factorial * A * B / e := by
    rw [eq_div_iff (by positivity)]
    exact mul_right_cancel₀ hF key
  rw [key2]
  have he : (2 : ℚ) ^ (2 * (j + i) + δ) = e * 2 ^ (j + i) := by
    rw [← pow_add]; congr 1; ring
  have hs : (-2 : ℚ) ^ (j + i) * (-1) ^ i = (-1) ^ j * 2 ^ (j + i) := by
    rw [show (-2 : ℚ) = (-1) * 2 by norm_num, mul_pow, pow_add (-1 : ℚ) j i]
    have : ((-1 : ℚ) ^ i) * (-1) ^ i = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    linear_combination ((-1 : ℚ) ^ j * 2 ^ (j + i)) * this
  rw [he]
  have he0 : e ≠ 0 := by positivity
  calc ((j + i).factorial : ℚ) * A * B / e * (-1) ^ j
      = (j + i).factorial * A * B * ((-1) ^ j * 2 ^ (j + i)) / (e * 2 ^ (j + i)) := by
        field_simp
    _ = (j + i).factorial * A * B * ((-2) ^ (j + i) * (-1) ^ i) / (e * 2 ^ (j + i)) := by
        rw [hs]
    _ = _ := by ring

/-- **Eq. (5.13).** For `δ ∈ {0,1}` and `ε = 2δ - 1`,
`J_n^ε(-x^2) = (-2)^n n! L_{2n+δ}(x)`. -/
theorem legendreJ_comp_neg_X_sq (n δ : ℕ) (hδ : δ ≤ 1) :
    ((legendreJ (2 * (δ : ℤ) - 1) n).map (Int.castRingHom ℚ)).comp (-X ^ 2) =
      C ((-2) ^ n * (n.factorial : ℚ)) * reducedLegendre n δ := by
  rw [reducedLegendre_eq_sum n δ hδ, mul_sum, ← sum_range_reflect, legendreJ, Polynomial.map_sum,
    Polynomial.sum_comp]
  refine sum_congr rfl fun j hj => ?_
  have hj : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show j + i + 1 - 1 - j = i by omega, show 2 * (j + i - i) = 2 * j by omega,
    Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, mul_comp, C_comp, X_pow_comp,
    neg_pow, ← pow_mul, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_1, ← C_neg, ← C_pow, ← C_mul]
  congr 2
  rw [← legendreJ_coeff_identity i j δ hδ]
  simp only [eq_intCast, Int.cast_mul, Int.cast_natCast, Int.cast_prod, Int.cast_add,
    Int.cast_ofNat, Int.cast_sub, Int.cast_one]
  simp only [add_sub_assoc]

/-! ### Comparison with Mathlib's shifted Legendre polynomials

Mathlib defines `Polynomial.shiftedLegendre n ∈ ℤ[X]` by its coefficients
`(-1)^k C(n,k) C(n+k,n)`; it satisfies the Rodrigues formula
`factorial_mul_shiftedLegendre_eq`. The manuscript's `P_n = P_n^{(0,0)}` is related to it by the
substitution `x ↦ 1 - 2x`. -/

/-- Iterated derivative of a composition with an affine map. -/
theorem iterate_derivative_comp_affine (a b : ℚ) (p : ℚ[X]) (k : ℕ) :
    derivative^[k] (p.comp (C a * X + C b)) =
      C (a ^ k) * (derivative^[k] p).comp (C a * X + C b) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, derivative_comp]
    have h : derivative (C a * X + C b : ℚ[X]) = C a := by simp
    rw [h, iterate_derivative_C_mul, ih, pow_succ, C_mul]
    ring

/-- **Legendre polynomials and Mathlib's shifted Legendre polynomials.**
`P_n(1 - 2x) = ∑_k (-1)^k C(n,k) C(n+k,n) x^k`, i.e. the image of `Polynomial.shiftedLegendre n`
in `ℚ[X]`. -/
theorem legendreP_comp_one_sub_two_mul_X (n : ℕ) :
    (legendreP n).comp (1 - 2 * X) = (shiftedLegendre n).map (Int.castRingHom ℚ) := by
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  have hq : (1 - 2 * X : ℚ[X]) = C (-2) * X + C 1 := by
    have h2 : (C (-2 : ℚ) : ℚ[X]) = -2 := by rw [map_neg, map_ofNat]
    rw [h2, map_one]; ring
  have hF : ((X ^ 2 - 1 : ℚ[X]) ^ n).comp (C (-2) * X + C 1) =
      C ((-4 : ℚ) ^ n) * (X ^ n * (1 - X) ^ n) := by
    have h4 : (C (-4 : ℚ) : ℚ[X]) = -4 := by rw [map_neg, map_ofNat]
    have hq2 : (1 - 2 * X : ℚ[X]) ^ 2 - 1 = C (-4 : ℚ) * (X * (1 - X)) := by rw [h4]; ring
    rw [← hq]
    simp only [pow_comp, sub_comp, X_comp, one_comp]
    rw [hq2, mul_pow, ← C_pow, mul_pow]
  have hD := iterate_derivative_comp_affine (-2) 1 ((X ^ 2 - 1 : ℚ[X]) ^ n) n
  rw [hF, iterate_derivative_C_mul, ← hq] at hD
  have hS : (C (n.factorial : ℚ)) * (shiftedLegendre n).map (Int.castRingHom ℚ) =
      derivative^[n] (X ^ n * (1 - X) ^ n) := by
    have := congrArg (Polynomial.map (Int.castRingHom ℚ)) (factorial_mul_shiftedLegendre_eq n)
    rw [← iterate_derivative_map] at this
    simpa using this
  rw [← hS] at hD
  rw [legendreP_eq_rodrigues, mul_comp, C_comp]
  set G := (derivative^[n] ((X ^ 2 - 1 : ℚ[X]) ^ n)).comp (1 - 2 * X) with hG
  set S' := (shiftedLegendre n).map (Int.castRingHom ℚ) with hS'
  have hne : C ((-2 : ℚ) ^ n) ≠ (0 : ℚ[X]) := by
    rw [Ne, C_eq_zero]; exact pow_ne_zero _ (by norm_num)
  refine mul_left_cancel₀ hne ?_
  have hu : (1 / (2 ^ n * (n.factorial : ℚ))) * ((-4 : ℚ) ^ n) * (n.factorial : ℚ) =
      (-2 : ℚ) ^ n := by
    have : ((-4 : ℚ) ^ n) = (-2) ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
    rw [this]; field_simp
  calc C ((-2 : ℚ) ^ n) * (C (1 / (2 ^ n * (n.factorial : ℚ))) * G)
      = C (1 / (2 ^ n * (n.factorial : ℚ))) * (C ((-2 : ℚ) ^ n) * G) := by ring
    _ = C (1 / (2 ^ n * (n.factorial : ℚ))) * (C ((-4 : ℚ) ^ n) * (C (n.factorial : ℚ) * S')) := by
        rw [hD]
    _ = C ((1 / (2 ^ n * (n.factorial : ℚ))) * ((-4 : ℚ) ^ n) * (n.factorial : ℚ)) * S' := by
        simp only [C_mul]; ring
    _ = C ((-2 : ℚ) ^ n) * S' := by rw [hu]

end ArithmeticOfJacobiPolynomials
