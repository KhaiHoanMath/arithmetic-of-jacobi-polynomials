/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.Basic

/-!
# Endpoint expansions of Jacobi polynomials

* the expansion at the endpoint `x = -1` (eq. (5.4) of the manuscript, [DLMF, 18.5.8]):
  `P_n^{(α,β)}(2X+1) = ∑_{j=0}^n binom(n+α, n-j) binom(n+α+β+j, j) X^j`;
* the reflection `P_n^{(β,α)}(-x) = (-1)^n P_n^{(α,β)}(x)`;
* the expansion (2.1) of `y_n(t) = P_n^{(α,β)}(1-2t)`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- The two-binomial identity behind the endpoint expansion. -/
private lemma choose_mul_choose_aux (z : ℚ) {n j k : ℕ} (hjk : j ≤ k) (hkn : k ≤ n) :
    Ring.choose z (n - j) * ((n - j).choose (k - j) : ℚ) =
      Ring.choose z (n - k) * Ring.choose (z - (n - k : ℕ)) (k - j) := by
  have h := Ring.choose_smul_choose z (n := n - j) (k := n - k) (by omega)
  rw [nsmul_eq_mul] at h
  have e1 : (n - j).choose (n - k) = (n - j).choose (k - j) := by
    rw [← Nat.choose_symm (by omega)]; congr 1; omega
  have e2 : n - j - (n - k) = k - j := by omega
  rw [e1, e2] at h
  rw [mul_comm, h]

/-- The endpoint expansion (5.4) of the manuscript. -/
theorem jacobiP_comp_two_mul_X_add_one (α β : ℚ) (n : ℕ) :
    (jacobiP α β n).comp (2 * X + 1) = ∑ j ∈ range (n + 1),
      C (Ring.choose ((n : ℚ) + α) (n - j) * Ring.choose ((n : ℚ) + α + β + j) j) * X ^ j := by
  have hstep : (jacobiP α β n).comp (2 * X + 1) = ∑ j ∈ range (n + 1),
      C (Ring.choose ((n : ℚ) + α) (n - j) * Ring.choose ((n : ℚ) + β) j) *
        (X ^ j * (X + 1) ^ (n - j)) := by
    simp only [jacobiP_eq, mul_comp, C_comp, Polynomial.sum_comp, pow_comp, sub_comp, add_comp,
      X_comp, one_comp, mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have h1 : (2 * X + 1 - 1 : ℚ[X]) = C 2 * X := by simp [C_ofNat]
    have h2 : (2 * X + 1 + 1 : ℚ[X]) = C 2 * (X + 1) := by
      rw [show (C (2 : ℚ)) = (2 : ℚ[X]) from rfl]; ring
    rw [h1, h2, mul_pow, mul_pow, ← C_pow, ← C_pow]
    have : (2 : ℚ) ^ j * 2 ^ (n - j) = 2 ^ n := by rw [← pow_add]; congr 1; omega
    calc C ((1 / 2 : ℚ) ^ n) * (C (Ring.choose ((n : ℚ) + α) (n - j) *
            Ring.choose ((n : ℚ) + β) j) * (C (2 ^ j) * X ^ j) * (C (2 ^ (n - j)) *
            (X + 1) ^ (n - j)))
        = C ((1 / 2 : ℚ) ^ n * (2 ^ j * 2 ^ (n - j))) * (C (Ring.choose ((n : ℚ) + α) (n - j) *
            Ring.choose ((n : ℚ) + β) j) * (X ^ j * (X + 1) ^ (n - j))) := by
          simp only [C_mul]; ring
      _ = _ := by rw [this, ← mul_pow]; norm_num
  rw [hstep]
  ext k
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow_mul', coeff_X_add_one_pow, coeff_X_pow]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, mem_range]
  by_cases hk : k ≤ n
  · rw [ite_eq_left (by omega), ← Finset.sum_range_add_sum_Ico _ (show k + 1 ≤ n + 1 by omega)]
    have hzero : ∑ x ∈ Ico (k + 1) (n + 1), (if x ≤ k then Ring.choose ((n : ℚ) + α) (n - x) *
        Ring.choose ((n : ℚ) + β) x * ((n - x).choose (k - x) : ℚ) else 0) = 0 :=
      sum_eq_zero fun x hx => ite_eq_right (by simp at hx; omega)
    rw [hzero, add_zero]
    have hterm : ∀ x ∈ range (k + 1), (if x ≤ k then Ring.choose ((n : ℚ) + α) (n - x) *
        Ring.choose ((n : ℚ) + β) x * ((n - x).choose (k - x) : ℚ) else 0) =
        Ring.choose ((n : ℚ) + α) (n - k) *
          (Ring.choose (α + k) (k - x) * Ring.choose ((n : ℚ) + β) x) := by
      intro x hx
      have hxk : x ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hx)
      rw [ite_eq_left hxk, mul_right_comm, choose_mul_choose_aux _ hxk hk]
      have : (n : ℚ) + α - ((n - k : ℕ) : ℚ) = α + k := by
        rw [Nat.cast_sub hk]; ring
      rw [this]; ring
    rw [sum_congr rfl hterm, ← mul_sum]
    congr 1
    have hv := Ring.add_choose_eq (r := α + k) (s := (n : ℚ) + β) k (Commute.all _ _)
    rw [show (n : ℚ) + α + β + k = α + k + (n + β) by ring, hv,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => Ring.choose (α + k) i *
        Ring.choose ((n : ℚ) + β) j)]
    rw [← Finset.sum_range_reflect]
    refine sum_congr rfl fun x hx => ?_
    have hx' : x < k + 1 := mem_range.mp hx
    congr 2; omega
  · rw [ite_eq_right (by omega)]
    refine sum_eq_zero fun x hx => ?_
    have hxn : x ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hx)
    rw [ite_eq_left (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- The endpoint expansion (2.1): `P_n^{(α,β)}(1-2t) = ∑_j (-1)^j binom(n+α, n-j)
binom(n+α+β+j, j) t^j`. -/
theorem jacobiP_comp_one_sub_two_mul_X (α β : ℚ) (n : ℕ) :
    (jacobiP α β n).comp (1 - 2 * X) = ∑ j ∈ range (n + 1),
      C ((-1) ^ j * Ring.choose ((n : ℚ) + α) (n - j) *
        Ring.choose ((n : ℚ) + α + β + j) j) * X ^ j := by
  have h : (1 - 2 * X : ℚ[X]) = (2 * X + 1).comp (-X) := by simp; ring
  rw [h, ← comp_assoc, jacobiP_comp_two_mul_X_add_one, Polynomial.sum_comp]
  refine sum_congr rfl fun j _ => ?_
  simp only [mul_comp, C_comp, pow_comp, X_comp]
  rw [show (-X : ℚ[X]) ^ j = C ((-1) ^ j) * X ^ j by rw [neg_pow, C_pow, C_neg, C_1],
    C_mul, C_mul, C_mul]
  ring

/-- Reflection: `P_n^{(β,α)}(-x) = (-1)^n P_n^{(α,β)}(x)`. -/
theorem jacobiP_comp_neg_X (α β : ℚ) (n : ℕ) :
    (jacobiP β α n).comp (-X) = C ((-1) ^ n) * jacobiP α β n := by
  rw [jacobiP_eq, jacobiP_eq]
  simp only [mul_comp, C_comp, Polynomial.sum_comp, pow_comp, sub_comp, add_comp, X_comp,
    one_comp, mul_sum]
  rw [← Finset.sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have e1 : n + 1 - 1 - j = n - j := by omega
  have e2 : n - (n - j) = j := by omega
  rw [e1, e2]
  have h1 : (-X - 1 : ℚ[X]) = C (-1) * (X + 1) := by simp; ring
  have h2 : (-X + 1 : ℚ[X]) = C (-1) * (X - 1) := by simp; ring
  rw [h1, h2, mul_pow, mul_pow, ← C_pow, ← C_pow]
  have : ((-1 : ℚ) ^ (n - j) * (-1) ^ j) = (-1) ^ n := by rw [← pow_add]; congr 1; omega
  rw [← this]
  simp only [C_mul]
  ring

end ArithmeticOfJacobiPolynomials
