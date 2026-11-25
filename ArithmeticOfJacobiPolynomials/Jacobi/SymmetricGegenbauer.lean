/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.Basic
public import ArithmeticOfJacobiPolynomials.Jacobi.DifferentialEquation
public import ArithmeticOfJacobiPolynomials.Jacobi.Endpoints
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Symmetric Jacobi polynomials and Gegenbauer polynomials

The manuscript (after Corollary 5.15) says that the symmetric Jacobi polynomials `P_n^{(a,a)}`
are "related to Gegenbauer polynomials with parameter `a + 1/2` by the usual scalar
normalization", for every rational `a > -1`. The relation follows
from the explicit formula for `gegenbauerC` and the Jacobi differential equation:

* `gegenbauerC_eq_C_mul_jacobiP`:
  `C_n^{a+1/2} = ((2a+1)_n / (a+1)_n) P_n^{(a,a)}` for every rational `a > -1`;
* `jacobiP_eq_C_mul_gegenbauerC`: `P_n^{(a,a)} = ((a+1)_n / (2a+1)_n) C_n^{a+1/2}` when
  `(2a+1)_n ≠ 0` (that is, `n = 0` or `a ≠ -1/2`).

This is the identity [DLMF, 18.7.1], `C_n^{(λ)} = (2λ)_n / (λ+1/2)_n P_n^{(λ-1/2, λ-1/2)}`
with `λ = a + 1/2`. The proof compares the coefficient recurrences of the two polynomials, which
come from the differential equation `(1 - x²) y'' - (2a+2) x y' + n (n + 2a + 1) y = 0`, and
the leading coefficients, using the duplication formula `(2x+1)_{2n} = 4^n (x+1/2)_n (x+1)_n`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-! ### Pochhammer symbols -/

/-- The duplication formula `4^n (x + 1/2)_n (x + 1)_n = (2x + 1)_{2n}`. -/
theorem four_pow_mul_ascPochhammer_eval (x : ℚ) (n : ℕ) :
    (4 : ℚ) ^ n * (ascPochhammer ℚ n).eval (x + 1 / 2) * (ascPochhammer ℚ n).eval (x + 1) =
      (ascPochhammer ℚ (2 * n)).eval (2 * x + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, ascPochhammer_succ_eval,
      ascPochhammer_succ_eval, ascPochhammer_succ_eval, ascPochhammer_succ_eval, ← ih]
    push_cast
    ring

/-- `(2x+1)_{2n} = (2x+1)_n (n + 2x + 1)_n`. -/
theorem ascPochhammer_eval_two_mul (x : ℚ) (n : ℕ) :
    (ascPochhammer ℚ (2 * n)).eval (2 * x + 1) =
      (ascPochhammer ℚ n).eval (2 * x + 1) * (ascPochhammer ℚ n).eval ((n : ℚ) + 2 * x + 1) := by
  have h := congrArg (Polynomial.eval (2 * x + 1)) (ascPochhammer_mul ℚ n n)
  rw [eval_mul, eval_comp, ← two_mul] at h
  rw [← h]
  simp only [eval_add, eval_X, eval_natCast]
  rw [add_comm (2 * x + 1) (n : ℚ), add_assoc]

/-- `n! binom(x, n) = (x - n + 1)_n`. -/
theorem factorial_mul_ring_choose (x : ℚ) (n : ℕ) :
    (n.factorial : ℚ) * Ring.choose x n = (ascPochhammer ℚ n).eval (x - n + 1) := by
  rw [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval, smul_eq_mul]
  have : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- The ratio of the top coefficients of `C_n^{a+1/2}` and `P_n^{(a,a)}`:
`4^n (a+1/2)_n / (n + 2a + 1)_n = (2a+1)_n / (a+1)_n`. -/
theorem four_pow_mul_div_eq (a : ℚ) (n : ℕ)
    (h1 : (ascPochhammer ℚ n).eval ((n : ℚ) + 2 * a + 1) ≠ 0)
    (h2 : (ascPochhammer ℚ n).eval (a + 1) ≠ 0) :
    (4 : ℚ) ^ n * (ascPochhammer ℚ n).eval (a + 1 / 2) /
        (ascPochhammer ℚ n).eval ((n : ℚ) + 2 * a + 1) =
      (ascPochhammer ℚ n).eval (2 * a + 1) / (ascPochhammer ℚ n).eval (a + 1) := by
  rw [div_eq_div_iff h1 h2]
  have h := four_pow_mul_ascPochhammer_eval a n
  rw [ascPochhammer_eval_two_mul] at h
  linear_combination h

/-! ### The coefficient recurrence of the symmetric Jacobi equation -/

/-- The coefficient recurrence of `(1 - x²) y'' - (2a+2) x y' + n (n + 2a + 1) y = 0`:
`(j+2)(j+1) y_{j+2} = (j (j + 2a + 1) - n (n + 2a + 1)) y_j`. -/
def SymRecurrence (a : ℚ) (n : ℕ) (y : ℚ[X]) : Prop :=
  ∀ j : ℕ, ((j : ℚ) + 2) * (j + 1) * y.coeff (j + 2) =
    ((j : ℚ) * (j + 2 * a + 1) - n * (n + 2 * a + 1)) * y.coeff j

/-- `P_n^{(a,a)}` satisfies the symmetric recurrence (from the Jacobi equation (5.6)). -/
theorem symRecurrence_jacobiP (a : ℚ) (n : ℕ) : SymRecurrence a n (jacobiP a a n) := by
  intro j
  set y := jacobiP a a n with hy
  have h := jacobiP_ode a a n
  rw [← hy, sub_self, C_0, zero_sub] at h
  have key : (1 - X ^ 2) * derivative (derivative y) +
      -(C (a + a + 2) * X) * derivative y + C ((n : ℚ) * (n + a + a + 1)) * y =
      derivative (derivative y) - X * derivative (X * derivative y) + X * derivative y -
        C (a + a + 2) * (X * derivative y) + C ((n : ℚ) * (n + a + a + 1)) * y := by
    rw [derivative_mul, derivative_X]; ring
  rw [key] at h
  have hj := congrArg (fun q => q.coeff j) h
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul_derivative, coeff_derivative,
    coeff_zero] at hj
  push_cast at hj
  linear_combination hj

/-- Any polynomial solution of `(1 - x²) y'' = (2a+2) x y' - n (n + 2a + 1) y` satisfies the
symmetric recurrence. -/
theorem symRecurrence_of_ode (a : ℚ) (n : ℕ) (y : ℚ[X])
    (h : (1 - X ^ 2) * derivative (derivative y) =
      C (2 * a + 2) * X * derivative y - C ((n : ℚ) * (n + 2 * a + 1)) * y) :
    SymRecurrence a n y := by
  intro j
  have key : (1 - X ^ 2) * derivative (derivative y) =
      derivative (derivative y) - X * derivative (X * derivative y) + X * derivative y := by
    rw [derivative_mul, derivative_X]; ring
  rw [key] at h
  have hj := congrArg (fun q => q.coeff j) h
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul_derivative,
    coeff_derivative, mul_assoc] at hj
  push_cast at hj
  linear_combination hj

/-! ### Uniqueness -/

/-- Two polynomials of degree at most `n` satisfying the symmetric recurrence, for `a > -1`,
are proportional through their top coefficients. -/
theorem symRecurrence_unique {a : ℚ} (ha : -1 < a) {n : ℕ} {y z : ℚ[X]}
    (hy : SymRecurrence a n y) (hz : SymRecurrence a n z)
    (hyn : ∀ j, n < j → y.coeff j = 0) (hzn : ∀ j, n < j → z.coeff j = 0) :
    C (z.coeff n) * y = C (y.coeff n) * z := by
  ext j
  simp only [coeff_C_mul]
  set w : ℕ → ℚ := fun j => z.coeff n * y.coeff j - y.coeff n * z.coeff j with hw
  have hrec : ∀ j : ℕ, ((j : ℚ) + 2) * (j + 1) * w (j + 2) =
      ((j : ℚ) * (j + 2 * a + 1) - n * (n + 2 * a + 1)) * w j := by
    intro j
    simp only [hw]
    linear_combination z.coeff n * hy j - y.coeff n * hz j
  have hall : ∀ d j : ℕ, n ≤ j + d → w j = 0 := by
    intro d
    induction d with
    | zero =>
      intro j hj
      rcases hj.eq_or_lt' with h | h
      · rw [Nat.add_zero] at h
        subst h
        simp only [hw]; ring
      · simp only [hw, hyn j (by omega), hzn j (by omega)]; ring
    | succ d ih =>
      intro j hj
      by_cases hjd : n ≤ j + d
      · exact ih j hjd
      · have hjn : j < n := by omega
        have h2 : w (j + 2) = 0 := ih (j + 2) (by omega)
        have h3 := hrec j
        rw [h2, mul_zero] at h3
        have hne : ((j : ℚ) * (j + 2 * a + 1) - n * (n + 2 * a + 1)) ≠ 0 := by
          have hjn' : (j : ℚ) + 1 ≤ n := by exact_mod_cast hjn
          have hn1 : (1 : ℚ) ≤ n := by linarith [(Nat.cast_nonneg j : (0 : ℚ) ≤ j)]
          have hfac : ((j : ℚ) * (j + 2 * a + 1) - n * (n + 2 * a + 1)) =
              ((j : ℚ) - n) * (j + n + 2 * a + 1) := by ring
          rw [hfac]
          refine mul_ne_zero (by linarith) ?_
          nlinarith [(Nat.cast_nonneg j : (0 : ℚ) ≤ j)]
        exact (mul_eq_zero.mp h3.symm).resolve_left hne
  have := hall n j (by omega)
  simp only [hw] at this
  linarith

/-! ### The Gegenbauer polynomials satisfy the same recurrence -/

theorem coeff_gegenbauerC_zero_gt (ν : ℚ) (n j : ℕ) (h : n < j) :
    (gegenbauerC ν n).coeff j = 0 := by
  rw [gegenbauerC_eq, finsetSum_coeff]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [coeff_C_mul_X_pow]
  split_ifs with h'
  · omega
  · rfl

theorem coeff_gegenbauerC_zero_parity (ν : ℚ) (n j : ℕ) (h : j % 2 ≠ n % 2) :
    (gegenbauerC ν n).coeff j = 0 := by
  rw [gegenbauerC_eq, finsetSum_coeff]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [coeff_C_mul_X_pow]
  split_ifs with h'
  · omega
  · rfl

/-- The coefficient of `x^{n-2k}` in `C_n^{ν}`. -/
theorem coeff_gegenbauerC_sub_two_mul (ν : ℚ) (n k : ℕ) (hk : 2 * k ≤ n) :
    (gegenbauerC ν n).coeff (n - 2 * k) =
      (-1) ^ k * (ascPochhammer ℚ (n - k)).eval ν /
        ((k.factorial : ℚ) * ((n - 2 * k).factorial : ℚ)) * 2 ^ (n - 2 * k) := by
  rw [gegenbauerC_eq, finsetSum_coeff, Finset.sum_eq_single k]
  · rw [coeff_C_mul_X_pow]
    split_ifs with h'
    · rfl
    · exact absurd rfl h'
  · intro k' hk' hne
    rw [Finset.mem_range] at hk'
    rw [coeff_C_mul_X_pow]
    split_ifs with h'
    · omega
    · rfl
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- `C_n^{a+1/2}` satisfies the symmetric recurrence. -/
theorem symRecurrence_gegenbauerC (a : ℚ) (n : ℕ) :
    SymRecurrence a n (gegenbauerC (a + 1 / 2) n) := by
  intro j
  by_cases hmain : j + 2 ≤ n ∧ (n - j) % 2 = 0
  · obtain ⟨k, hk⟩ : ∃ k, n = j + 2 + 2 * k := ⟨(n - j - 2) / 2, by omega⟩
    subst hk
    have e1 := coeff_gegenbauerC_sub_two_mul (a + 1 / 2) (j + 2 + 2 * k) k (by omega)
    have e2 := coeff_gegenbauerC_sub_two_mul (a + 1 / 2) (j + 2 + 2 * k) (k + 1) (by omega)
    rw [show j + 2 + 2 * k - 2 * k = j + 2 by omega,
      show j + 2 + 2 * k - k = j + k + 2 by omega] at e1
    rw [show j + 2 + 2 * k - 2 * (k + 1) = j by omega,
      show j + 2 + 2 * k - (k + 1) = j + k + 1 by omega] at e2
    rw [e1, e2, show j + k + 2 = (j + k + 1) + 1 by ring, ascPochhammer_succ_eval,
      Nat.factorial_succ (j + 1), Nat.factorial_succ j, Nat.factorial_succ k]
    push_cast
    have h1 : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    have h2 : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp
    ring
  · have hcoef : (gegenbauerC (a + 1 / 2) n).coeff j = 0 ∨ (j = n) := by
      by_cases hjn : n < j
      · exact Or.inl (coeff_gegenbauerC_zero_gt _ _ _ hjn)
      · by_cases hp : j % 2 = n % 2
        · right
          omega
        · exact Or.inl (coeff_gegenbauerC_zero_parity _ _ _ hp)
    have hj2 : (gegenbauerC (a + 1 / 2) n).coeff (j + 2) = 0 := by
      by_cases hjn : n < j + 2
      · exact coeff_gegenbauerC_zero_gt _ _ _ hjn
      · exact coeff_gegenbauerC_zero_parity _ _ _ (by omega)
    rw [hj2, mul_zero]
    rcases hcoef with h | h
    · rw [h, mul_zero]
    · subst h
      ring

/-! ### The relation -/

/-- **Symmetric Jacobi polynomials and Gegenbauer polynomials** ([DLMF, 18.7.1] with
`λ = a + 1/2`). For every rational `a > -1`,
`C_n^{a+1/2} = ((2a+1)_n / (a+1)_n) P_n^{(a,a)}`. -/
theorem gegenbauerC_eq_C_mul_jacobiP (a : ℚ) (ha : -1 < a) (n : ℕ) :
    gegenbauerC (a + 1 / 2) n =
      C ((ascPochhammer ℚ n).eval (2 * a + 1) / (ascPochhammer ℚ n).eval (a + 1)) *
        jacobiP a a n := by
  have hu := symRecurrence_unique ha (symRecurrence_jacobiP a n) (symRecurrence_gegenbauerC a n)
    (fun j hj => coeff_eq_zero_of_natDegree_lt ((natDegree_jacobiP_le a a n).trans_lt hj))
    (fun j hj => coeff_gegenbauerC_zero_gt _ _ _ hj)
  have hch := factorial_mul_ring_choose (2 * (n : ℚ) + a + a) n
  rw [show 2 * (n : ℚ) + a + a - n + 1 = n + 2 * a + 1 by ring] at hch
  have h1 : (ascPochhammer ℚ n).eval ((n : ℚ) + 2 * a + 1) ≠ 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have : (1 : ℚ) ≤ n := by exact_mod_cast hn
      exact (ascPochhammer_pos n _ (by linarith)).ne'
  have h2 : (ascPochhammer ℚ n).eval (a + 1) ≠ 0 := (ascPochhammer_pos n _ (by linarith)).ne'
  have hfn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hchoose : Ring.choose (2 * (n : ℚ) + a + a) n ≠ 0 := by
    intro h
    rw [h, mul_zero] at hch
    exact h1 hch.symm
  have hJn : (jacobiP a a n).coeff n ≠ 0 := by
    rw [coeff_jacobiP_self]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hchoose
  have hg : (gegenbauerC (a + 1 / 2) n).coeff n =
      (ascPochhammer ℚ n).eval (a + 1 / 2) / n.factorial * 2 ^ n := by
    have := coeff_gegenbauerC_sub_two_mul (a + 1 / 2) n 0 (by omega)
    simpa using this
  have key : ((jacobiP a a n).coeff n)⁻¹ * (gegenbauerC (a + 1 / 2) n).coeff n =
      (ascPochhammer ℚ n).eval (2 * a + 1) / (ascPochhammer ℚ n).eval (a + 1) := by
    rw [← four_pow_mul_div_eq a n h1 h2, hg, coeff_jacobiP_self, eq_div_iff h1, ← hch]
    generalize (ascPochhammer ℚ n).eval (a + 1 / 2) = e
    field_simp
    have h24 : ((1 : ℚ) / 2) ^ n * 4 ^ n = 2 ^ n := by rw [← mul_pow]; norm_num
    linear_combination (-e) * h24
  calc gegenbauerC (a + 1 / 2) n
      = C (((jacobiP a a n).coeff n)⁻¹ * (jacobiP a a n).coeff n) * gegenbauerC (a + 1 / 2) n := by
        rw [inv_mul_cancel₀ hJn, C_1, one_mul]
    _ = C (((jacobiP a a n).coeff n)⁻¹) *
          (C ((jacobiP a a n).coeff n) * gegenbauerC (a + 1 / 2) n) := by
        rw [C_mul, mul_assoc]
    _ = C (((jacobiP a a n).coeff n)⁻¹) *
          (C ((gegenbauerC (a + 1 / 2) n).coeff n) * jacobiP a a n) := by rw [hu]
    _ = _ := by rw [← mul_assoc, ← C_mul, key]

/-- **The converse normalization**: `P_n^{(a,a)} = ((a+1)_n / (2a+1)_n) C_n^{a+1/2}` whenever
`(2a+1)_n ≠ 0`, that is for `n = 0` or `a ≠ -1/2` (given `a > -1`). -/
theorem jacobiP_eq_C_mul_gegenbauerC (a : ℚ) (ha : -1 < a) (n : ℕ)
    (h : (ascPochhammer ℚ n).eval (2 * a + 1) ≠ 0) :
    jacobiP a a n =
      C ((ascPochhammer ℚ n).eval (a + 1) / (ascPochhammer ℚ n).eval (2 * a + 1)) *
        gegenbauerC (a + 1 / 2) n := by
  have h2 : (ascPochhammer ℚ n).eval (a + 1) ≠ 0 := (ascPochhammer_pos n _ (by linarith)).ne'
  rw [gegenbauerC_eq_C_mul_jacobiP a ha n, ← mul_assoc, ← C_mul, div_mul_div_comm,
    mul_comm ((ascPochhammer ℚ n).eval (2 * a + 1)) ((ascPochhammer ℚ n).eval (a + 1)),
    div_self (mul_ne_zero h2 h), C_1, one_mul]

/-- For an integer `r ≥ 0`, `C_n^{r+1/2}` is a nonzero rational multiple of `P_n^{(r,r)}`
([DLMF, 18.7.1]; the case stated in the Introduction of the manuscript). -/
theorem exists_ne_zero_gegenbauerC_eq_C_mul_jacobiP_nat (r n : ℕ) :
    ∃ c : ℚ, c ≠ 0 ∧ gegenbauerC ((r : ℚ) + 1 / 2) n = C c * jacobiP (r : ℚ) r n := by
  have hr : (0 : ℚ) ≤ r := Nat.cast_nonneg r
  refine ⟨_, ?_, gegenbauerC_eq_C_mul_jacobiP (r : ℚ) (by linarith) n⟩
  exact div_ne_zero (ascPochhammer_pos n _ (by linarith)).ne'
    (ascPochhammer_pos n _ (by linarith)).ne'

end ArithmeticOfJacobiPolynomials
