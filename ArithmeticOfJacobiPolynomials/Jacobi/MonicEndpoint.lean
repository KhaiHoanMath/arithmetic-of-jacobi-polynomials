/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.Shift
public import Mathlib.RingTheory.Binomial
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Group.Irreducible.Lemmas
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic.LinearCombination

/-!
# The monic endpoint expansion (4.24)

For rational parameters with `(n+α+β+1)_n ≠ 0`, the monic endpoint polynomial
`n! P_n^{(α,β)}(2X-1) / (n+α+β+1)_n` has the expansion (eq. (4.24) of the manuscript)
`∑_{j=0}^n (-1)^{n-j} binom(n,j) (β+j+1)_{n-j} / (n+α+β+j+1)_{n-j} X^j`,
where `(x)_k = x(x+1)⋯(x+k-1)` is the rising factorial (`ascPochhammer`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- `P_n^{(α,β)}(2X-1) = ∑_j (-1)^{n-j} binom(n+β, n-j) binom(n+α+β+j, j) X^j`. -/
theorem jacobiP_comp_two_mul_X_sub_one (α β : ℚ) (n : ℕ) :
    (jacobiP α β n).comp (2 * X - 1) = ∑ j ∈ range (n + 1),
      C ((-1) ^ (n - j) * Ring.choose ((n : ℚ) + β) (n - j) *
        Ring.choose ((n : ℚ) + α + β + j) j) * X ^ j := by
  have h1 : (2 * X - 1 : ℚ[X]) = (-X).comp (1 - 2 * X) := by simp
  rw [h1, ← comp_assoc, jacobiP_comp_neg_X β α n, mul_comp, C_comp,
    jacobiP_comp_one_sub_two_mul_X, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hs : ((-1 : ℚ) ^ n * (-1) ^ j) = (-1) ^ (n - j) := by
    rw [← pow_add]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj'
    rw [show j + k + j = k + 2 * j by ring, pow_add, pow_mul]
    simp
  rw [← mul_assoc, ← C_mul, show (n : ℚ) + β + α + j = n + α + β + j by ring, ← hs]
  congr 2
  ring

/-- `binom(a, k) = (a - k + 1)_k / k!`. -/
theorem ring_choose_eq_ascPochhammer_div (a : ℚ) (k : ℕ) :
    Ring.choose a k = (ascPochhammer ℚ k).eval (a - k + 1) / k.factorial := by
  rw [Ring.choose_eq_smul, descPochhammer_smeval_eq_ascPochhammer, ascPochhammer_smeval_eq_eval,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- `(x)_{j+m} = (x)_j (x+j)_m`. -/
theorem ascPochhammer_eval_add (x : ℚ) (j m : ℕ) :
    (ascPochhammer ℚ (j + m)).eval x =
      (ascPochhammer ℚ j).eval x * (ascPochhammer ℚ m).eval (x + j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, ascPochhammer_succ_eval, ih, ascPochhammer_succ_eval]
    push_cast; ring

/-- The monic endpoint polynomial `n! P_n^{(α,β)}(2X-1) / (n+α+β+1)_n` of (4.24). -/
noncomputable def monicEndpoint (α β : ℚ) (n : ℕ) : ℚ[X] :=
  C ((n.factorial : ℚ) / (ascPochhammer ℚ n).eval ((n : ℚ) + α + β + 1)) *
    (jacobiP α β n).comp (2 * X - 1)

theorem monicEndpoint_def (α β : ℚ) (n : ℕ) : monicEndpoint α β n =
    C ((n.factorial : ℚ) / (ascPochhammer ℚ n).eval ((n : ℚ) + α + β + 1)) *
      (jacobiP α β n).comp (2 * X - 1) := (rfl)

/-- The coefficient `b_j` of the monic endpoint polynomial, as displayed in (4.24). -/
noncomputable def monicEndpointCoeff (α β : ℚ) (n j : ℕ) : ℚ :=
  (-1) ^ (n - j) * (n.choose j : ℚ) * (ascPochhammer ℚ (n - j)).eval (β + j + 1) /
    (ascPochhammer ℚ (n - j)).eval ((n : ℚ) + α + β + j + 1)

theorem monicEndpointCoeff_def (α β : ℚ) (n j : ℕ) : monicEndpointCoeff α β n j =
    (-1) ^ (n - j) * (n.choose j : ℚ) * (ascPochhammer ℚ (n - j)).eval (β + j + 1) /
      (ascPochhammer ℚ (n - j)).eval ((n : ℚ) + α + β + j + 1) := (rfl)

/-- **The monic endpoint expansion (4.24).** If `(n+α+β+1)_n ≠ 0`, then
`n! P_n^{(α,β)}(2X-1) / (n+α+β+1)_n = ∑_{j=0}^n (-1)^{n-j} binom(n,j)
(β+j+1)_{n-j} / (n+α+β+j+1)_{n-j} X^j`. -/
theorem monicEndpoint_eq_sum (α β : ℚ) (n : ℕ)
    (h : (ascPochhammer ℚ n).eval ((n : ℚ) + α + β + 1) ≠ 0) :
    monicEndpoint α β n = ∑ j ∈ range (n + 1), C (monicEndpointCoeff α β n j) * X ^ j := by
  rw [monicEndpoint_def, jacobiP_comp_two_mul_X_sub_one, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [← mul_assoc, ← C_mul]
  congr 2
  have hsplit := ascPochhammer_eval_add ((n : ℚ) + α + β + 1) j (n - j)
  rw [Nat.add_sub_cancel' hj'] at hsplit
  rw [hsplit] at h ⊢
  have hA := left_ne_zero_of_mul h
  have hB := right_ne_zero_of_mul h
  rw [ring_choose_eq_ascPochhammer_div, ring_choose_eq_ascPochhammer_div, monicEndpointCoeff_def,
    Nat.cast_choose ℚ hj']
  have e1 : (n : ℚ) + β - ((n - j : ℕ) : ℚ) + 1 = β + j + 1 := by
    rw [Nat.cast_sub hj']; ring
  have e2 : (n : ℚ) + α + β + j - (j : ℕ) + 1 = n + α + β + 1 := by ring
  have e3 : (n : ℚ) + α + β + 1 + j = n + α + β + j + 1 := by ring
  rw [e1, e2, ← e3]
  have hf1 : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hf2 : ((n - j).factorial : ℚ) ≠ 0 := by exact_mod_cast (n - j).factorial_ne_zero
  field_simp

/-- The coefficients of the monic endpoint polynomial. -/
theorem monicEndpoint_coeff (α β : ℚ) (n : ℕ)
    (h : (ascPochhammer ℚ n).eval ((n : ℚ) + α + β + 1) ≠ 0) (j : ℕ) :
    (monicEndpoint α β n).coeff j = if j ≤ n then monicEndpointCoeff α β n j else 0 := by
  rw [monicEndpoint_eq_sum α β n h, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [sum_ite_eq (range (n + 1)) j]
  simp

theorem monicEndpointCoeff_self (α β : ℚ) (n : ℕ) : monicEndpointCoeff α β n n = 1 := by
  simp [monicEndpointCoeff_def]

/-- The monic endpoint polynomial is monic of degree `n`. -/
theorem monicEndpoint_monic (α β : ℚ) (n : ℕ)
    (h : (ascPochhammer ℚ n).eval ((n : ℚ) + α + β + 1) ≠ 0) :
    (monicEndpoint α β n).Monic ∧ (monicEndpoint α β n).natDegree = n := by
  have hle : (monicEndpoint α β n).natDegree ≤ n := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    rw [monicEndpoint_coeff α β n h]
    have : ¬ j ≤ n := by exact_mod_cast not_le.mpr hj
    simp [this]
  have hn : (monicEndpoint α β n).coeff n = 1 := by
    rw [monicEndpoint_coeff α β n h]; simp [monicEndpointCoeff_self]
  have hdeg : (monicEndpoint α β n).natDegree = n :=
    le_antisymm hle (le_natDegree_of_ne_zero (by rw [hn]; exact one_ne_zero))
  refine ⟨?_, hdeg⟩
  rw [Monic, leadingCoeff, hdeg, hn]

/-- The monic endpoint polynomial over an extension field `K` of `ℚ`, in terms of
`P_n^{(α,β)}`. -/
theorem monicEndpoint_map {K : Type*} [Field K] [Algebra ℚ K] (α β : ℚ) (n : ℕ) :
    (monicEndpoint α β n).map (algebraMap ℚ K) =
      C (algebraMap ℚ K ((n.factorial : ℚ) / (ascPochhammer ℚ n).eval ((n : ℚ) + α + β + 1))) *
        ((jacobiP α β n).map (algebraMap ℚ K)).comp (2 * X - 1) := by
  rw [monicEndpoint_def, Polynomial.map_mul, map_C, map_comp]
  simp

private theorem two_ne_zero_of_algebraRat (K : Type*) [Field K] [Algebra ℚ K] : (2 : K) ≠ 0 := by
  have := (algebraMap ℚ K).injective.ne (show (2 : ℚ) ≠ 0 by norm_num)
  simpa using this

/-- The affine substitution `X ↦ 2X - 1` as an algebra automorphism of `K[X]`. -/
noncomputable def affineSubst (K : Type*) [Field K] [Algebra ℚ K] : K[X] ≃ₐ[K] K[X] :=
  algEquivOfCompEqX (C 2 * X - 1) (C (1 / 2 : K) * (X + 1))
    (by
      have h2 : (C 2 : K[X]) * C (1 / 2) = 1 := by
        rw [← C_mul, mul_one_div_cancel (two_ne_zero_of_algebraRat K), C_1]
      simp only [sub_comp, mul_comp, C_comp, X_comp, one_comp]
      linear_combination (X + 1) * h2)
    (by
      have h2 : (C 2 : K[X]) * C (1 / 2) = 1 := by
        rw [← C_mul, mul_one_div_cancel (two_ne_zero_of_algebraRat K), C_1]
      simp only [mul_comp, C_comp, add_comp, X_comp, one_comp]
      linear_combination X * h2)

theorem affineSubst_apply (K : Type*) [Field K] [Algebra ℚ K] (f : K[X]) :
    affineSubst K f = f.comp (2 * X - 1) := by
  rw [affineSubst, algEquivOfCompEqX_apply, comp_eq_aeval, map_ofNat C 2]

/-- Over any extension field `K` of `ℚ`, `P_n^{(α,β)}` is irreducible iff the monic endpoint
polynomial is. -/
theorem irreducible_map_jacobiP_iff {K : Type*} [Field K] [Algebra ℚ K] (α β : ℚ) (n : ℕ)
    (h : (ascPochhammer ℚ n).eval ((n : ℚ) + α + β + 1) ≠ 0) :
    Irreducible ((jacobiP α β n).map (algebraMap ℚ K)) ↔
      Irreducible ((monicEndpoint α β n).map (algebraMap ℚ K)) := by
  rw [monicEndpoint_map, irreducible_isUnit_mul, ← affineSubst_apply]
  · exact (MulEquiv.irreducible_iff (affineSubst K)).symm
  rw [isUnit_C]
  refine IsUnit.mk0 _ ?_
  rw [map_ne_zero]
  exact div_ne_zero (by exact_mod_cast (n.factorial_ne_zero)) h

end ArithmeticOfJacobiPolynomials
