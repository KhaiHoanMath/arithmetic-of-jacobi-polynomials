/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.Wronskian

/-!
# Ordered-parameter Jacobi argument for Lemma 2.1

The manuscript's coefficient, moment and Wronskian argument is stated for real
parameters. The coefficient, moment, and Wronskian results below hold over ordered fields.
-/

public section

namespace ArithmeticOfJacobiPolynomials.JacobiGeneric

open Polynomial Finset

section Basic

variable {K : Type*} [Field K] [CharZero K]

/-- The Jacobi polynomial `P_n^{(α,β)} ∈ K[X]` in the normalization (1.1) of the manuscript
([DLMF, 18.5.8]). It is defined for all characteristic-zero parameters, including those outside the
orthogonality range `α, β > -1`. -/
noncomputable def jacobiP (α β : K) (n : ℕ) : K[X] :=
  C ((1 / 2 : K) ^ n) * ∑ j ∈ Finset.range (n + 1),
    C (Ring.choose ((n : K) + α) (n - j) * Ring.choose ((n : K) + β) j) *
      (X - 1) ^ j * (X + 1) ^ (n - j)

theorem jacobiP_eq (α β : K) (n : ℕ) : jacobiP α β n =
    C ((1 / 2 : K) ^ n) * ∑ j ∈ Finset.range (n + 1),
      C (Ring.choose ((n : K) + α) (n - j) * Ring.choose ((n : K) + β) j) *
        (X - 1) ^ j * (X + 1) ^ (n - j) := (rfl)

end Basic

section Shift

open Polynomial Finset

variable {K : Type*} [Field K] [CharZero K]

/-- The two-binomial identity behind the endpoint expansion. -/
private lemma choose_mul_choose_aux (z : K) {n j k : ℕ} (hjk : j ≤ k) (hkn : k ≤ n) :
    Ring.choose z (n - j) * ((n - j).choose (k - j) : K) =
      Ring.choose z (n - k) * Ring.choose (z - (n - k : ℕ)) (k - j) := by
  have h := Ring.choose_smul_choose z (n := n - j) (k := n - k) (by omega)
  rw [nsmul_eq_mul] at h
  have e1 : (n - j).choose (n - k) = (n - j).choose (k - j) := by
    rw [← Nat.choose_symm (by omega)]; congr 1; omega
  have e2 : n - j - (n - k) = k - j := by omega
  rw [e1, e2] at h
  rw [mul_comm, h]

/-- The endpoint expansion (5.4) of the manuscript. -/
theorem jacobiP_comp_two_mul_X_add_one (α β : K) (n : ℕ) :
    (JacobiGeneric.jacobiP α β n).comp (2 * X + 1) = ∑ j ∈ range (n + 1),
      C (Ring.choose ((n : K) + α) (n - j) * Ring.choose ((n : K) + α + β + j) j) * X ^ j := by
  have hstep : (JacobiGeneric.jacobiP α β n).comp (2 * X + 1) = ∑ j ∈ range (n + 1),
      C (Ring.choose ((n : K) + α) (n - j) * Ring.choose ((n : K) + β) j) *
        (X ^ j * (X + 1) ^ (n - j)) := by
    simp only [jacobiP_eq, mul_comp, C_comp, Polynomial.sum_comp, pow_comp, sub_comp, add_comp,
      X_comp, one_comp, mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have h1 : (2 * X + 1 - 1 : K[X]) = C 2 * X := by simp [C_ofNat]
    have h2 : (2 * X + 1 + 1 : K[X]) = C 2 * (X + 1) := by
      rw [show (C (2 : K)) = (2 : K[X]) from rfl]; ring
    rw [h1, h2, mul_pow, mul_pow, ← C_pow, ← C_pow]
    have : (2 : K) ^ j * 2 ^ (n - j) = 2 ^ n := by rw [← pow_add]; congr 1; omega
    calc C ((1 / 2 : K) ^ n) * (C (Ring.choose ((n : K) + α) (n - j) *
            Ring.choose ((n : K) + β) j) * (C (2 ^ j) * X ^ j) * (C (2 ^ (n - j)) *
            (X + 1) ^ (n - j)))
        = C ((1 / 2 : K) ^ n * (2 ^ j * 2 ^ (n - j))) * (C (Ring.choose ((n : K) + α) (n - j) *
            Ring.choose ((n : K) + β) j) * (X ^ j * (X + 1) ^ (n - j))) := by
          simp only [C_mul]; ring
      _ = _ := by rw [this, ← mul_pow]; norm_num
  rw [hstep]
  ext k
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow_mul', coeff_X_add_one_pow, coeff_X_pow]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, mem_range]
  by_cases hk : k ≤ n
  · rw [ite_eq_left (by omega), ← Finset.sum_range_add_sum_Ico _ (show k + 1 ≤ n + 1 by omega)]
    have hzero : ∑ x ∈ Ico (k + 1) (n + 1), (if x ≤ k then Ring.choose ((n : K) + α) (n - x) *
        Ring.choose ((n : K) + β) x * ((n - x).choose (k - x) : K) else 0) = 0 :=
      sum_eq_zero fun x hx => ite_eq_right (by simp at hx; omega)
    rw [hzero, add_zero]
    have hterm : ∀ x ∈ range (k + 1), (if x ≤ k then Ring.choose ((n : K) + α) (n - x) *
        Ring.choose ((n : K) + β) x * ((n - x).choose (k - x) : K) else 0) =
        Ring.choose ((n : K) + α) (n - k) *
          (Ring.choose (α + k) (k - x) * Ring.choose ((n : K) + β) x) := by
      intro x hx
      have hxk : x ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hx)
      rw [ite_eq_left hxk, mul_right_comm, choose_mul_choose_aux _ hxk hk]
      have : (n : K) + α - ((n - k : ℕ) : K) = α + k := by
        rw [Nat.cast_sub hk]; ring
      rw [this]; ring
    rw [sum_congr rfl hterm, ← mul_sum]
    congr 1
    have hv := Ring.add_choose_eq (r := α + k) (s := (n : K) + β) k (Commute.all _ _)
    rw [show (n : K) + α + β + k = α + k + (n + β) by ring, hv,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => Ring.choose (α + k) i *
        Ring.choose ((n : K) + β) j)]
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
theorem jacobiP_comp_one_sub_two_mul_X (α β : K) (n : ℕ) :
    (JacobiGeneric.jacobiP α β n).comp (1 - 2 * X) = ∑ j ∈ range (n + 1),
      C ((-1) ^ j * Ring.choose ((n : K) + α) (n - j) *
        Ring.choose ((n : K) + α + β + j) j) * X ^ j := by
  have h : (1 - 2 * X : K[X]) = (2 * X + 1).comp (-X) := by simp; ring
  rw [h, ← comp_assoc, jacobiP_comp_two_mul_X_add_one, Polynomial.sum_comp]
  refine sum_congr rfl fun j _ => ?_
  simp only [mul_comp, C_comp, pow_comp, X_comp]
  rw [show (-X : K[X]) ^ j = C ((-1) ^ j) * X ^ j by rw [neg_pow, C_pow, C_neg, C_1],
    C_mul, C_mul, C_mul]
  ring

/-- Reflection: `P_n^{(β,α)}(-x) = (-1)^n P_n^{(α,β)}(x)`. -/
theorem jacobiP_comp_neg_X (α β : K) (n : ℕ) :
    (JacobiGeneric.jacobiP β α n).comp (-X) = C ((-1) ^ n) * JacobiGeneric.jacobiP α β n := by
  rw [jacobiP_eq, jacobiP_eq]
  simp only [mul_comp, C_comp, Polynomial.sum_comp, pow_comp, sub_comp, add_comp, X_comp,
    one_comp, mul_sum]
  rw [← Finset.sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have e1 : n + 1 - 1 - j = n - j := by omega
  have e2 : n - (n - j) = j := by omega
  rw [e1, e2]
  have h1 : (-X - 1 : K[X]) = C (-1) * (X + 1) := by simp; ring
  have h2 : (-X + 1 : K[X]) = C (-1) * (X - 1) := by simp; ring
  rw [h1, h2, mul_pow, mul_pow, ← C_pow, ← C_pow]
  have : ((-1 : K) ^ (n - j) * (-1) ^ j) = (-1) ^ n := by rw [← pow_add]; congr 1; omega
  rw [← this]
  simp only [C_mul]
  ring

end Shift

section DifferentialEquation

open Polynomial Finset

variable {K : Type*} [Field K] [CharZero K]

/-- `binom(r, k+1) (k+1) = binom(r, k) (r - k)`. -/
theorem ring_choose_succ_mul (r : K) (k : ℕ) :
    Ring.choose r (k + 1) * ((k : K) + 1) = Ring.choose r k * (r - k) := by
  have h := Ring.choose_smul_choose r (n := k + 1) (k := k) (by omega)
  rw [Nat.choose_succ_self_right, nsmul_eq_mul, show k + 1 - k = 1 by omega,
    Ring.choose_one_right] at h
  rw [mul_comm, ← h]; push_cast; ring

/-- `binom(r+1, k+1) (k+1) = (r+1) binom(r, k)`. -/
theorem ring_choose_add_one_succ_mul (r : K) (k : ℕ) :
    Ring.choose (r + 1) (k + 1) * ((k : K) + 1) = (r + 1) * Ring.choose r k := by
  have h := Ring.choose_smul_choose (r + 1) (n := k + 1) (k := 1) (by omega)
  rw [Nat.choose_one_right, nsmul_eq_mul, Ring.choose_one_right,
    show k + 1 - 1 = k by omega] at h
  simp only [Nat.cast_one, add_sub_cancel_right] at h
  rw [mul_comm, ← h]; push_cast; ring

/-- The Euler operator on coefficients: `[X^j] (X p') = j [X^j] p`. -/
theorem coeff_X_mul_derivative {R : Type*} [CommSemiring R] (p : R[X]) (j : ℕ) :
    (X * derivative p).coeff j = j * p.coeff j := by
  cases j with
  | zero => simp
  | succ i => rw [coeff_X_mul, coeff_derivative]; push_cast; ring

/-- The coefficients of `P_n^{(α,β)}(2X+1)`. -/
theorem coeff_jacobiP_comp_two_mul_X_add_one (α β : K) (n j : ℕ) :
    ((JacobiGeneric.jacobiP α β n).comp (2 * X + 1)).coeff j = if j ≤ n then
      Ring.choose ((n : K) + α) (n - j) * Ring.choose ((n : K) + α + β + j) j else 0 := by
  rw [jacobiP_comp_two_mul_X_add_one, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, mem_range, Nat.lt_succ_iff]

/-- The two-term coefficient recurrence of `P_n^{(α,β)}(2X+1)`. -/
theorem jacobiP_shift_coeff_recurrence (α β : K) (n j : ℕ) :
    ((j : K) + 1) * (j + α + 1) * ((JacobiGeneric.jacobiP α β n).comp (2 * X + 1)).coeff (j + 1) =
      ((n : K) - j) * (n + j + α + β + 1) * ((JacobiGeneric.jacobiP α β n).comp (2 * X +
        1)).coeff j := by
  rw [coeff_jacobiP_comp_two_mul_X_add_one, coeff_jacobiP_comp_two_mul_X_add_one]
  rcases lt_trichotomy j n with hjn | hjn | hjn
  · have hj1 : j + 1 ≤ n := hjn
    simp only [hj1, hjn.le, ↓reduceIte]
    obtain ⟨m, hm⟩ : ∃ m, n - j = m + 1 := ⟨n - j - 1, by omega⟩
    have hm' : n - (j + 1) = m := by omega
    rw [hm, hm']
    have hmq : (m : K) = n - j - 1 := by
      have : m + j + 1 = n := by omega
      rw [← this]; push_cast; ring
    have h1 := ring_choose_succ_mul ((n : K) + α) m
    have h2 := ring_choose_add_one_succ_mul ((n : K) + α + β + j) j
    have e : ((n : K) + α + β + ((j + 1 : ℕ) : K)) = (n : K) + α + β + j + 1 := by
      push_cast; ring
    rw [e]
    rw [hmq] at h1
    have e2 : ((n : K) - j) = (n - j - 1) + 1 := by ring
    rw [e2]
    linear_combination (↑j + α + 1) * Ring.choose (↑n + α) m * h2 -
      (↑n + ↑j + α + β + 1) * Ring.choose (↑n + α + β + ↑j) j * h1
  · subst hjn; simp
  · have hj1 : ¬ j + 1 ≤ n := by omega
    have hj2 : ¬ j ≤ n := by omega
    simp only [hj1, hj2, ↓reduceIte, mul_zero]

/-- The Jacobi differential equation in the variable `t`, `x = 2t + 1`:
`t(t+1) z'' + [(α+1) + (α+β+2) t] z' = n(n+α+β+1) z` for `z = P_n^{(α,β)}(2t+1)`. -/
theorem jacobiP_shift_ode (α β : K) (n : ℕ) :
    X * (X + 1) * derivative (derivative ((JacobiGeneric.jacobiP α β n).comp (2 * X + 1))) +
      (C (α + 1) + C (α + β + 2) * X) * derivative ((JacobiGeneric.jacobiP α β n).comp (2 * X +
        1)) =
      C ((n : K) * (n + α + β + 1)) * (JacobiGeneric.jacobiP α β n).comp (2 * X + 1) := by
  set z := (JacobiGeneric.jacobiP α β n).comp (2 * X + 1) with hz
  have key : X * (X + 1) * derivative (derivative z) +
      (C (α + 1) + C (α + β + 2) * X) * derivative z =
      X * derivative (X * derivative z) - X * derivative z + X * derivative (derivative z) +
        C (α + 1) * derivative z + C (α + β + 2) * (X * derivative z) := by
    rw [derivative_mul, derivative_X]; ring
  rw [key]
  ext j
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul_derivative, coeff_derivative]
  have hr := jacobiP_shift_coeff_recurrence α β n j
  rw [← hz] at hr
  linear_combination hr

/-- **The Jacobi differential equation (5.6)**:
`(1 - X^2) y'' + [β - α - (α + β + 2) X] y' + n (n + α + β + 1) y = 0` for
`y = P_n^{(α,β)}`. -/
theorem jacobiP_ode (α β : K) (n : ℕ) :
    (1 - X ^ 2) * derivative (derivative (JacobiGeneric.jacobiP α β n)) +
      (C (β - α) - C (α + β + 2) * X) * derivative (JacobiGeneric.jacobiP α β n) +
      C ((n : K) * (n + α + β + 1)) * JacobiGeneric.jacobiP α β n = 0 := by
  set y := JacobiGeneric.jacobiP α β n with hy
  set E := (1 - X ^ 2) * derivative (derivative y) +
      (C (β - α) - C (α + β + 2) * X) * derivative y + C ((n : K) * (n + α + β + 1)) * y
    with hE
  have hz1 : derivative (y.comp (2 * X + 1)) = 2 * (derivative y).comp (2 * X + 1) := by
    rw [derivative_comp]; simp
  have hz2 : derivative (derivative (y.comp (2 * X + 1))) =
      4 * (derivative (derivative y)).comp (2 * X + 1) := by
    rw [hz1, derivative_mul, derivative_comp]; simp; ring
  have hode := jacobiP_shift_ode α β n
  rw [← hy] at hode
  have hEc : E.comp (2 * X + 1) = 0 := by
    rw [hE]
    simp only [add_comp, mul_comp, sub_comp, one_comp, pow_comp, X_comp, C_comp]
    rw [hz2, hz1] at hode
    simp only [map_add, map_sub, map_one, map_ofNat] at hode ⊢
    linear_combination -hode
  have hinv : (2 * X + 1 : K[X]).comp (C (1 / 2) * (X - 1)) = X := by
    rw [show (2 * X + 1 : K[X]) = C 2 * X + C 1 by simp [C_ofNat]]
    simp only [add_comp, mul_comp, X_comp, C_comp]
    rw [← mul_assoc, ← C_mul]
    norm_num
  calc E = E.comp X := (comp_X).symm
    _ = (E.comp (2 * X + 1)).comp (C (1 / 2) * (X - 1)) := by rw [comp_assoc, hinv]
    _ = 0 := by rw [hEc, zero_comp]

end DifferentialEquation

section JacobiMoments

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The Jacobi moments `μ_j = (α+1)_j / (α+β+2)_j` of (2.2) in the manuscript: the moments
of the probability measure `t^α (1-t)^β dt / B(α+1, β+1)` on `(0,1)`. -/
noncomputable def jacobiMoment (α β : K) (j : ℕ) : K :=
  (ascPochhammer K j).eval (α + 1) / (ascPochhammer K j).eval (α + β + 2)

omit [LinearOrder K] [IsStrictOrderedRing K] in
omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem jacobiMoment_eq (α β : K) (j : ℕ) : jacobiMoment α β j =
    (ascPochhammer K j).eval (α + 1) / (ascPochhammer K j).eval (α + β + 2) := (rfl)

/-- The Jacobi functional `I`, acting coefficientwise with the moments `jacobiMoment`. -/
noncomputable def jacobiFunctional (α β : K) : K[X] →ₗ[K] K :=
  momentFunctional (jacobiMoment α β)

omit [LinearOrder K] [IsStrictOrderedRing K] in
omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem jacobiFunctional_eq (α β : K) :
    jacobiFunctional α β = momentFunctional (jacobiMoment α β) := (rfl)

theorem jacobiMoment_zero (α β : K) : jacobiMoment α β 0 = 1 := by
  simp [jacobiMoment]

omit [LinearOrder K] [IsStrictOrderedRing K] in
omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem jacobiFunctional_C_mul (α β a : K) (p : K[X]) :
    jacobiFunctional α β (C a * p) = a * jacobiFunctional α β p :=
  momentFunctional_C_mul _ a p

theorem jacobiFunctional_C (α β a : K) : jacobiFunctional α β (C a) = a := by
  rw [jacobiFunctional_eq, momentFunctional_C, jacobiMoment_zero, one_mul]

omit [LinearOrder K] [IsStrictOrderedRing K] in
omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem jacobiFunctional_X_pow (α β : K) (j : ℕ) :
    jacobiFunctional α β (X ^ j) = jacobiMoment α β j :=
  momentFunctional_X_pow _ j

omit [LinearOrder K] [IsStrictOrderedRing K] in
omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem ascPochhammer_eval_succ_left (j : ℕ) (x : K) :
    (ascPochhammer K (j + 1)).eval x = x * (ascPochhammer K j).eval (x + 1) := by
  rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp]; simp

theorem ascPochhammer_eval_pos_of_pos (j : ℕ) {x : K} (hx : 0 < x) :
    0 < (ascPochhammer K j).eval x := ascPochhammer_pos j x hx

/-- The moment recurrence `μ_{j+1} (α+β+2+j) = μ_j (α+1+j)`. -/
theorem jacobiMoment_succ {α β : K} (hαβ : 0 < α + β + 2) (j : ℕ) :
    jacobiMoment α β (j + 1) * (α + β + 2 + j) = jacobiMoment α β j * (α + 1 + j) := by
  have h1 := ascPochhammer_eval_pos_of_pos j hαβ
  have h2 : (0 : K) < α + β + 2 + j := by positivity
  simp only [jacobiMoment, ascPochhammer_succ_eval]
  field_simp

/-- Multiplication by `σ = X(1-X)` shifts the parameters:
`I_{α,β}(σ f) = κ I_{α+1,β+1}(f)` with `κ = (α+1)(β+1)/((α+β+2)(α+β+3))`. -/
theorem jacobiFunctional_sigma_mul {α β : K} (hαβ : 0 < α + β + 2) (f : K[X]) :
    jacobiFunctional α β (X * (1 - X) * f) =
      (α + 1) * (β + 1) / ((α + β + 2) * (α + β + 3)) *
        jacobiFunctional (α + 1) (β + 1) f := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, map_add, hp, hq, map_add]; ring
  | monomial j a =>
    have e : X * (1 - X) * monomial j a = monomial (j + 1) a - monomial (j + 2) a := by
      rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]
      ring
    rw [e, jacobiFunctional, map_sub, momentFunctional_monomial, momentFunctional_monomial,
      jacobiFunctional, momentFunctional_monomial]
    have hc3 : (0 : K) < α + β + 3 := by linarith
    set A := (ascPochhammer K j).eval (α + 2)
    set B := (ascPochhammer K j).eval (α + β + 3)
    set D := (ascPochhammer K j).eval (α + β + 4)
    have hB : 0 < B := ascPochhammer_eval_pos_of_pos j hc3
    have h2 : (0 : K) < α + β + 3 + j := by positivity
    have hBD : D = B * (α + β + 3 + j) / (α + β + 3) := by
      have e1 := ascPochhammer_succ_eval j (α + β + 3)
      have e2 := ascPochhammer_eval_succ_left j (α + β + 3)
      rw [show α + β + 3 + 1 = α + β + 4 by ring] at e2
      rw [e1] at e2
      field_simp
      linear_combination -e2
    have m1 : jacobiMoment α β (j + 1) = (α + 1) * A / ((α + β + 2) * B) := by
      simp only [jacobiMoment, ascPochhammer_eval_succ_left, A, B]
      rw [show α + 1 + 1 = α + 2 by ring, show α + β + 2 + 1 = α + β + 3 by ring]
    have m2 : jacobiMoment α β (j + 2) =
        (α + 1) * (A * (α + 2 + j)) / ((α + β + 2) * (B * (α + β + 3 + j))) := by
      have n2 : (ascPochhammer K (j + 2)).eval (α + 1) = (α + 1) * (A * (α + 2 + j)) := by
        rw [show j + 2 = (j + 1) + 1 from rfl, ascPochhammer_eval_succ_left,
          ascPochhammer_succ_eval, show α + 1 + 1 = α + 2 by ring]
      have d2 : (ascPochhammer K (j + 2)).eval (α + β + 2) =
          (α + β + 2) * (B * (α + β + 3 + j)) := by
        rw [show j + 2 = (j + 1) + 1 from rfl, ascPochhammer_eval_succ_left,
          ascPochhammer_succ_eval, show α + β + 2 + 1 = α + β + 3 by ring]
      rw [jacobiMoment, n2, d2]
    have m3 : jacobiMoment (α + 1) (β + 1) j = A / D := by
      simp only [jacobiMoment, A, D]
      rw [show α + 1 + 1 = α + 2 by ring, show α + 1 + (β + 1) + 2 = α + β + 4 by ring]
    rw [m1, m2, m3, hBD]
    field_simp
    ring

end JacobiMoments

section JacobiData

variable {K : Type*} [Field K] [CharZero K]

/-- `y_n(t) = P_n^{(α,β)}(1 - 2t)`, the Jacobi polynomial moved to the unit interval. -/
noncomputable def jacobiShifted (α β : K) (n : ℕ) : K[X] := (JacobiGeneric.jacobiP α β n).comp
  (1 - 2 * X)

theorem jacobiShifted_eq (α β : K) (n : ℕ) :
    jacobiShifted α β n = (JacobiGeneric.jacobiP α β n).comp (1 - 2 * X) := (rfl)

/-- The second polynomial `Q_n(t) = I_s((y_n(t) - y_n(s))/(t - s))` for the Jacobi functional,
i.e. `Q_n(t) = ∑_j y_j ∑_{k<j} μ_{j-1-k} t^k`. -/
noncomputable def jacobiSecondPoly (α β : K) (n : ℕ) : K[X] :=
  momentQuotient (jacobiMoment α β) (jacobiShifted α β n)

theorem jacobiSecondPoly_eq (α β : K) (n : ℕ) :
    jacobiSecondPoly α β n = momentQuotient (jacobiMoment α β) (jacobiShifted α β n) := (rfl)

/-- The constant `C_n = (α+1)_n (β+1)_n / (n! (α+β+2)_{n-1})` of Lemma 2.1. -/
noncomputable def jacobiWronskianConstant (α β : K) (n : ℕ) : K :=
  (ascPochhammer K n).eval (α + 1) * (ascPochhammer K n).eval (β + 1) /
    ((n.factorial : K) * (ascPochhammer K (n - 1)).eval (α + β + 2))

omit [CharZero K] in
omit [CharZero K] in
theorem jacobiWronskianConstant_eq (α β : K) (n : ℕ) : jacobiWronskianConstant α β n =
    (ascPochhammer K n).eval (α + 1) * (ascPochhammer K n).eval (β + 1) /
      ((n.factorial : K) * (ascPochhammer K (n - 1)).eval (α + β + 2)) := (rfl)

end JacobiData

section OrderedParameters

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Coefficients, lowering and raising -/

/-- The coefficient `(-1)^k binom(n+α, n-k) binom(n+α+β+k, k)` of `t^k` in `y_n` (2.1). -/
noncomputable def jacobiShiftedCoeff (α β : K) (n k : ℕ) : K :=
  (-1) ^ k * Ring.choose ((n : K) + α) (n - k) * Ring.choose ((n : K) + α + β + k) k

theorem coeff_jacobiShifted (α β : K) (n k : ℕ) :
    (JacobiGeneric.jacobiShifted α β n).coeff k = if k ≤ n then jacobiShiftedCoeff α β n k else
      0 := by
  rw [jacobiShifted_eq, jacobiP_comp_one_sub_two_mul_X, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  simp only [mem_range, Nat.lt_succ_iff, jacobiShiftedCoeff]

/-- Lowering: `y_{m+1}^{(α,β)}' = -(m+α+β+2) y_m^{(α+1,β+1)}`. -/
theorem derivative_jacobiShifted (α β : K) (m : ℕ) :
    derivative (JacobiGeneric.jacobiShifted α β (m + 1)) =
      C (-((m : K) + α + β + 2)) * JacobiGeneric.jacobiShifted (α + 1) (β + 1) m := by
  ext k
  rw [coeff_derivative, coeff_C_mul, coeff_jacobiShifted, coeff_jacobiShifted]
  by_cases hk : k ≤ m
  · rw [ite_eq_left (by omega), ite_eq_left hk]
    simp only [jacobiShiftedCoeff]
    rw [show m + 1 - (k + 1) = m - k by omega,
      show ((m + 1 : ℕ) : K) + α + β + ((k + 1 : ℕ) : K) = (m : K) + (α + 1) + (β + 1) + k by
        push_cast; ring,
      show ((m + 1 : ℕ) : K) + α = (m : K) + (α + 1) by push_cast; ring]
    have h := ring_choose_succ_mul ((m : K) + (α + 1) + (β + 1) + k) k
    rw [show (m : K) + (α + 1) + (β + 1) + k - k = m + α + β + 2 by ring] at h
    rw [pow_succ]
    linear_combination (-(-1 : K) ^ k * Ring.choose ((m : K) + (α + 1)) (m - k)) * h
  · rw [ite_eq_right (by omega), ite_eq_right hk]; simp

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem coeff_sigma_tau_zero (a b : K) (f : K[X]) :
    (X * (1 - X) * derivative f + (C a - C b * X) * f).coeff 0 = a * f.coeff 0 := by
  have e : X * (1 - X) * derivative f + (C a - C b * X) * f =
      X * (derivative f - X * derivative f - C b * f) + C a * f := by ring
  rw [e, coeff_add, coeff_X_mul_zero, coeff_C_mul, zero_add]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem coeff_sigma_tau_succ (a b : K) (f : K[X]) (k : ℕ) :
    (X * (1 - X) * derivative f + (C a - C b * X) * f).coeff (k + 1) =
      ((k : K) + 1 + a) * f.coeff (k + 1) - ((k : K) + b) * f.coeff k := by
  have e : X * (1 - X) * derivative f + (C a - C b * X) * f =
      X * derivative f - X * (X * derivative f) + C a * f - C b * (X * f) := by ring
  simp only [e, coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_derivative]
  rcases k with _ | k
  · rw [coeff_X_mul_zero]; push_cast; ring
  · rw [coeff_X_mul, coeff_derivative]; push_cast; ring

/-- Raising (the algebraic Rodrigues recursion):
`(m+1) y_{m+1}^{(α,β)} = σ f' + τ f` with `f = y_m^{(α+1,β+1)}`, `σ = X(1-X)` and
`τ = (α+1) - (α+β+2) X`. -/
theorem jacobiShifted_raising (α β : K) (m : ℕ) :
    C ((m : K) + 1) * JacobiGeneric.jacobiShifted α β (m + 1) =
      X * (1 - X) * derivative (JacobiGeneric.jacobiShifted (α + 1) (β + 1) m) +
        (C (α + 1) - C (α + β + 2) * X) * JacobiGeneric.jacobiShifted (α + 1) (β + 1) m := by
  ext k
  rw [coeff_C_mul]
  rcases k with _ | k
  · rw [coeff_sigma_tau_zero, coeff_jacobiShifted, coeff_jacobiShifted, ite_eq_left (by omega),
      ite_eq_left (by omega)]
    simp only [jacobiShiftedCoeff, pow_zero, one_mul, Nat.cast_zero, add_zero, Nat.sub_zero,
      Ring.choose_zero_right, mul_one]
    have h := ring_choose_succ_mul ((m : K) + (α + 1)) m
    rw [show ((m + 1 : ℕ) : K) + α = (m : K) + (α + 1) by push_cast; ring]
    rw [show (m : K) + (α + 1) - m = α + 1 by ring] at h
    linear_combination h
  · rw [coeff_sigma_tau_succ, coeff_jacobiShifted, coeff_jacobiShifted, coeff_jacobiShifted]
    rcases lt_trichotomy k m with hk | rfl | hk
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_lt hk
      rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
      simp only [jacobiShiftedCoeff]
      rw [show k + i + 1 + 1 - (k + 1) = i + 1 by omega, show k + i + 1 - (k + 1) = i by omega,
        show k + i + 1 - k = i + 1 by omega]
      rw [show ((k + i + 1 + 1 : ℕ) : K) + α + β + ((k + 1 : ℕ) : K) =
            2 * (k : K) + i + α + β + 3 by push_cast; ring,
        show ((k + i + 1 : ℕ) : K) + (α + 1) + (β + 1) + ((k + 1 : ℕ) : K) =
            2 * (k : K) + i + α + β + 3 + 1 by push_cast; ring,
        show ((k + i + 1 : ℕ) : K) + (α + 1) + (β + 1) + (k : K) =
            2 * (k : K) + i + α + β + 3 by push_cast; ring,
        show ((k + i + 1 + 1 : ℕ) : K) + α = (k : K) + i + α + 2 by push_cast; ring,
        show ((k + i + 1 : ℕ) : K) + (α + 1) = (k : K) + i + α + 2 by push_cast; ring]
      have h1 := ring_choose_succ_mul ((k : K) + i + α + 2) i
      rw [show (k : K) + i + α + 2 - i = k + α + 2 by ring] at h1
      have h2 := Ring.choose_succ_succ (2 * (k : K) + i + α + β + 3) k
      have h3 := ring_choose_succ_mul (2 * (k : K) + i + α + β + 3) k
      rw [show 2 * (k : K) + i + α + β + 3 - k = k + i + α + β + 3 by ring] at h3
      push_cast
      linear_combination
        (-(-1 : K) ^ k * Ring.choose (2 * (k : K) + i + α + β + 3 + 1) (k + 1)) * h1 +
        ((-1 : K) ^ k * Ring.choose ((k : K) + i + α + 2) (i + 1) * (i + 1)) * h2 +
        (-(-1 : K) ^ k * Ring.choose ((k : K) + i + α + 2) (i + 1)) * h3
    · rw [ite_eq_left le_rfl, ite_eq_right (by omega), ite_eq_left le_rfl]
      simp only [jacobiShiftedCoeff]
      rw [Nat.sub_self, Nat.sub_self, Ring.choose_zero_right, Ring.choose_zero_right]
      rw [show ((k + 1 : ℕ) : K) + α + β + ((k + 1 : ℕ) : K) = 2 * (k : K) + α + β + 2 by
          push_cast; ring,
        show (k : K) + (α + 1) + (β + 1) + (k : K) = 2 * (k : K) + α + β + 2 by ring]
      have h3 := ring_choose_succ_mul (2 * (k : K) + α + β + 2) k
      rw [show 2 * (k : K) + α + β + 2 - k = k + α + β + 2 by ring] at h3
      linear_combination (-(-1 : K) ^ k) * h3
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; ring

/-- The differential equation (2.3): `σ y_n'' + τ y_n' + n(n+c+1) y_n = 0`. -/
theorem jacobiShifted_ode (α β : K) (n : ℕ) :
    X * (1 - X) * derivative (derivative (JacobiGeneric.jacobiShifted α β n)) +
        (C (α + 1) - C (α + β + 2) * X) * derivative (JacobiGeneric.jacobiShifted α β n) +
        C ((n : K) * (n + α + β + 1)) * JacobiGeneric.jacobiShifted α β n = 0 := by
  rcases n with _ | m
  · have h0 : JacobiGeneric.jacobiShifted α β 0 = C 1 := by
      ext k; rw [coeff_jacobiShifted, coeff_C]
      rcases k with _ | k <;> simp [jacobiShiftedCoeff]
    rw [h0]; simp
  · rw [derivative_jacobiShifted, derivative_C_mul]
    have hr := jacobiShifted_raising α β m
    have e : X * (1 - X) * (C (-((m : K) + α + β + 2)) *
          derivative (JacobiGeneric.jacobiShifted (α + 1) (β + 1) m)) +
        (C (α + 1) - C (α + β + 2) * X) *
          (C (-((m : K) + α + β + 2)) * JacobiGeneric.jacobiShifted (α + 1) (β + 1) m) =
        C (-((m : K) + α + β + 2)) * (X * (1 - X) * derivative (JacobiGeneric.jacobiShifted (α
          + 1) (β + 1) m) +
          (C (α + 1) - C (α + β + 2) * X) * JacobiGeneric.jacobiShifted (α + 1) (β + 1) m) :=
            by ring
    rw [e, ← hr]
    simp only [C_mul, C_add, C_neg, Nat.cast_add, Nat.cast_one, C_1, C_ofNat]
    ring

theorem jacobiShifted_zero (α β : K) : JacobiGeneric.jacobiShifted α β 0 = 1 := by
  ext k; rw [coeff_jacobiShifted, coeff_one]
  rcases k with _ | k <;> simp [jacobiShiftedCoeff]

theorem natDegree_jacobiShifted_le (α β : K) (n : ℕ) : (JacobiGeneric.jacobiShifted α β
  n).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_jacobiShifted, ite_eq_right (by intro h; exact absurd h (by omega))]

theorem coeff_jacobiShifted_self (α β : K) (n : ℕ) :
    (JacobiGeneric.jacobiShifted α β n).coeff n = (-1) ^ n * Ring.choose (2 * (n : K) + α + β)
      n := by
  rw [coeff_jacobiShifted, ite_eq_left le_rfl, jacobiShiftedCoeff, Nat.sub_self,
    Ring.choose_zero_right, show (n : K) + α + β + n = 2 * n + α + β by ring, mul_one]

/-! ### Orthogonality and the norm -/

theorem jacobiMoment_succ_of_gt {α β : K} (hα : -1 < α) (hβ : -1 < β) (j : ℕ) :
    JacobiGeneric.jacobiMoment α β (j + 1) * (α + β + 2 + j) = JacobiGeneric.jacobiMoment α β j
      * (α + 1 + j) :=
  jacobiMoment_succ (by linarith) j

/-- The raising relation under `I`:
`(m+1) I_{α,β}(y_{m+1} g) = -κ I_{α+1,β+1}(y_m^{(α+1,β+1)} g')`. -/
theorem jacobiFunctional_jacobiShifted_succ_mul {α β : K} (hα : -1 < α) (hβ : -1 < β)
    (m : ℕ) (g : K[X]) :
    ((m : K) + 1) * JacobiGeneric.jacobiFunctional α β (JacobiGeneric.jacobiShifted α β (m + 1)
      * g) =
      -((α + 1) * (β + 1) / ((α + β + 2) * (α + β + 3))) *
        JacobiGeneric.jacobiFunctional (α + 1) (β + 1) (JacobiGeneric.jacobiShifted (α + 1) (β
          + 1) m * derivative g) := by
  set f := JacobiGeneric.jacobiShifted (α + 1) (β + 1) m
  have hr := jacobiShifted_raising α β m
  have hP := momentFunctional_pearson (jacobiMoment_succ_of_gt hα hβ) (f * g)
  have e : C ((m : K) + 1) * (JacobiGeneric.jacobiShifted α β (m + 1) * g) =
      (X * (1 - X) * derivative (f * g) + (C (α + 1) - C (α + β + 2) * X) * (f * g)) -
        X * (1 - X) * (f * derivative g) := by
    rw [← mul_assoc, hr, derivative_mul]; ring
  rw [← jacobiFunctional_eq] at hP
  rw [← jacobiFunctional_C_mul, e, map_sub, hP, jacobiFunctional_sigma_mul (by linarith)]
  ring

/-- Orthogonality: `I(y_n t^k) = 0` for `k < n`. -/
theorem jacobiFunctional_jacobiShifted_mul_X_pow :
    ∀ (n : ℕ) {α β : K}, -1 < α → -1 < β → ∀ k < n,
      JacobiGeneric.jacobiFunctional α β (JacobiGeneric.jacobiShifted α β n * X ^ k) = 0 := by
  intro n
  induction n with
  | zero => intro α β _ _ k hk; omega
  | succ m ih =>
    intro α β hα hβ k hk
    have h := jacobiFunctional_jacobiShifted_succ_mul hα hβ m (X ^ k)
    have hm : ((m : K) + 1) ≠ 0 := by positivity
    rcases k with _ | k
    · simp only [pow_zero, derivative_one, mul_zero, map_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hm
    · rw [derivative_X_pow, add_tsub_cancel_right, mul_left_comm, jacobiFunctional_C_mul,
        ih (by linarith) (by linarith) k (by omega), mul_zero, mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hm

/-- The top value `I(y_n t^n) = (-1)^n (α+1)_n (β+1)_n / (α+β+2)_{2n}`. -/
theorem jacobiFunctional_jacobiShifted_mul_X_pow_self :
    ∀ (n : ℕ) {α β : K}, -1 < α → -1 < β →
      JacobiGeneric.jacobiFunctional α β (JacobiGeneric.jacobiShifted α β n * X ^ n) =
        (-1) ^ n * (ascPochhammer K n).eval (α + 1) * (ascPochhammer K n).eval (β + 1) /
          (ascPochhammer K (2 * n)).eval (α + β + 2) := by
  intro n
  induction n with
  | zero =>
    intro α β _ _
    rw [jacobiShifted_zero, pow_zero, mul_one, ← C_1, jacobiFunctional_C]
    simp
  | succ m ih =>
    intro α β hα hβ
    have h := jacobiFunctional_jacobiShifted_succ_mul hα hβ m (X ^ (m + 1))
    have hm : ((m : K) + 1) ≠ 0 := by positivity
    rw [derivative_X_pow, add_tsub_cancel_right, mul_left_comm, jacobiFunctional_C_mul,
      ih (by linarith) (by linarith)] at h
    have hc2 : (0 : K) < α + β + 2 := by linarith
    have hc3 : (0 : K) < α + β + 3 := by linarith
    have hD := ascPochhammer_eval_pos_of_pos (2 * m) (show (0 : K) < α + β + 4 by linarith)
    have e1 : (ascPochhammer K (m + 1)).eval (α + 1) =
        (α + 1) * (ascPochhammer K m).eval (α + 2) := by
      rw [ascPochhammer_eval_succ_left]; ring_nf
    have e2 : (ascPochhammer K (m + 1)).eval (β + 1) =
        (β + 1) * (ascPochhammer K m).eval (β + 2) := by
      rw [ascPochhammer_eval_succ_left]; ring_nf
    have e3 : (ascPochhammer K (2 * (m + 1))).eval (α + β + 2) =
        (α + β + 2) * ((α + β + 3) * (ascPochhammer K (2 * m)).eval (α + β + 4)) := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, ascPochhammer_eval_succ_left,
        ascPochhammer_eval_succ_left]; ring_nf
    rw [show α + 1 + 1 = α + 2 by ring, show β + 1 + 1 = β + 2 by ring,
      show α + 1 + (β + 1) + 2 = α + β + 4 by ring] at h
    rw [e1, e2, e3]
    have h' : JacobiGeneric.jacobiFunctional α β (JacobiGeneric.jacobiShifted α β (m + 1) * X ^
      (m + 1)) =
        -((α + 1) * (β + 1) / ((α + β + 2) * (α + β + 3))) *
          ((-1) ^ m * (ascPochhammer K m).eval (α + 2) * (ascPochhammer K m).eval (β + 2) /
            (ascPochhammer K (2 * m)).eval (α + β + 4)) := by
      apply mul_left_cancel₀ hm
      rw [h]; push_cast; ring
    rw [h']
    field_simp
    ring

/-- `I(y_n g) = [t^n] g · I(y_n t^n)` whenever `deg g ≤ n` (orthogonality). -/
theorem jacobiFunctional_jacobiShifted_mul_of_natDegree_le {α β : K} (hα : -1 < α)
    (hβ : -1 < β) (n : ℕ) {g : K[X]} (hg : g.natDegree ≤ n) :
    JacobiGeneric.jacobiFunctional α β (JacobiGeneric.jacobiShifted α β n * g) =
      g.coeff n * JacobiGeneric.jacobiFunctional α β (JacobiGeneric.jacobiShifted α β n * X ^
        n) := by
  conv_lhs => rw [as_sum_range' g (n + 1) (by omega)]
  rw [mul_sum, map_sum, sum_range_succ, sum_eq_zero]
  · rw [zero_add, ← C_mul_X_pow_eq_monomial, mul_left_comm, jacobiFunctional_C_mul]
  · intro k hk
    rw [← C_mul_X_pow_eq_monomial, mul_left_comm, jacobiFunctional_C_mul,
      jacobiFunctional_jacobiShifted_mul_X_pow n hα hβ k (by simpa using hk), mul_zero]

/-! ### The identity (2.2) -/

/-- The left side of (2.2) has zero derivative. -/
theorem derivative_jacobiWronskian {α β : K} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    derivative (C (α + β + 1) * JacobiGeneric.jacobiShifted α β n ^ 2 +
      X * (1 - X) * (derivative (JacobiGeneric.jacobiShifted α β n) *
        JacobiGeneric.jacobiSecondPoly α β n -
        JacobiGeneric.jacobiShifted α β n * derivative (JacobiGeneric.jacobiSecondPoly α β n)) +
      (C α - C (α + β) * X) * JacobiGeneric.jacobiShifted α β n *
        JacobiGeneric.jacobiSecondPoly α β n) = 0 := by
  have hE := momentQuotient_second_order (jacobiMoment_zero α β) (jacobiMoment_succ_of_gt hα hβ)
    (JacobiGeneric.jacobiShifted α β n)
  have hode := jacobiShifted_ode α β n
  rw [← jacobiSecondPoly_eq] at hE
  have hQ : momentQuotient (JacobiGeneric.jacobiMoment α β)
      (X * (1 - X) * derivative (derivative (JacobiGeneric.jacobiShifted α β n)) +
        (C (α + 1) - C (α + β + 2) * X) * derivative (JacobiGeneric.jacobiShifted α β n)) =
      -(C ((n : K) * (n + α + β + 1)) * JacobiGeneric.jacobiSecondPoly α β n) := by
    have e : X * (1 - X) * derivative (derivative (JacobiGeneric.jacobiShifted α β n)) +
        (C (α + 1) - C (α + β + 2) * X) * derivative (JacobiGeneric.jacobiShifted α β n) =
        C (-((n : K) * (n + α + β + 1))) * JacobiGeneric.jacobiShifted α β n := by
      rw [C_neg]; linear_combination hode
    rw [e, momentQuotient_C_mul, ← jacobiSecondPoly_eq, C_neg, neg_mul]
  rw [hQ] at hE
  set y := JacobiGeneric.jacobiShifted α β n
  set Q := JacobiGeneric.jacobiSecondPoly α β n
  simp only [derivative_add, derivative_mul, derivative_sub, derivative_C, derivative_X,
    derivative_sq, derivative_one, zero_mul, zero_add, zero_sub]
  simp only [C_add, C_1, C_ofNat, C_mul] at hE hode ⊢
  linear_combination Q * hode - y * hE

/-- **Lemma 2.1, identity (2.2)**, by an independent algebraic proof. The main argument uses
`jacobi_wronskian_stieltjes`. For ordered-field `α, β > -1` and `n ≥ 1`,
`(c+1) y_n² + σ (y_n' Q_n - y_n Q_n') + ρ y_n Q_n = C_n` with `c = α+β`, `σ = t(1-t)`,
`ρ = α - ct` and `C_n = (α+1)_n (β+1)_n / (n! (c+2)_{n-1})`. -/
theorem jacobi_wronskian {α β : K} (hα : -1 < α) (hβ : -1 < β) {n : ℕ} (hn : 1 ≤ n) :
    C (α + β + 1) * JacobiGeneric.jacobiShifted α β n ^ 2 +
      X * (1 - X) * (derivative (JacobiGeneric.jacobiShifted α β n) *
        JacobiGeneric.jacobiSecondPoly α β n -
        JacobiGeneric.jacobiShifted α β n * derivative (JacobiGeneric.jacobiSecondPoly α β n)) +
      (C α - C (α + β) * X) * JacobiGeneric.jacobiShifted α β n *
        JacobiGeneric.jacobiSecondPoly α β n =
    C (JacobiGeneric.jacobiWronskianConstant α β n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hW' := derivative_jacobiWronskian hα hβ (m + 1)
  set y := JacobiGeneric.jacobiShifted α β (m + 1) with hy
  set Q := JacobiGeneric.jacobiSecondPoly α β (m + 1) with hQdef
  set W := C (α + β + 1) * y ^ 2 + X * (1 - X) * (derivative y * Q - y * derivative Q) +
    (C α - C (α + β) * X) * y * Q with hWdef
  have hconst : W = C (W.coeff 0) :=
    eq_C_of_natDegree_eq_zero (derivative_eq_zero.mp hW')
  have hyd : y.natDegree ≤ m + 1 := natDegree_jacobiShifted_le α β (m + 1)
  -- coefficients of `Q`
  have hQtop : Q.coeff m = y.coeff (m + 1) := by
    rw [hQdef, jacobiSecondPoly_eq, coeff_momentQuotient_top _ hyd, jacobiMoment_zero, mul_one]
  have hQzero : ∀ k, m + 1 ≤ k → Q.coeff k = 0 := fun k hk => by
    rw [hQdef, jacobiSecondPoly_eq]; exact coeff_momentQuotient_eq_zero _ hyd hk
  -- the auxiliary polynomial `g₂ = 2σQ' + (1-2X)Q`
  set g2 := (X * (1 - X) * derivative Q + (C 1 - C 2 * X) * Q) +
    (X * (1 - X) * derivative Q + (C 0 - C 0 * X) * Q) with hg2
  have hg2coeff : ∀ k : ℕ, g2.coeff (k + 1) =
      (2 * (k : K) + 3) * Q.coeff (k + 1) - (2 * (k : K) + 2) * Q.coeff k := by
    intro k
    rw [hg2, coeff_add, coeff_sigma_tau_succ, coeff_sigma_tau_succ]; ring
  have hg2d : g2.natDegree ≤ m + 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    rw [hg2coeff, hQzero k (by omega), hQzero (k + 1) (by omega)]; ring
  have hg2top : g2.coeff (m + 1) = -(2 * (m : K) + 2) * y.coeff (m + 1) := by
    rw [hg2coeff, hQzero (m + 1) le_rfl, hQtop]; ring
  have hsplit : W = C (α + β + 1) * (y * y) +
      (X * (1 - X) * derivative (y * Q) + (C (α + 1) - C (α + β + 2) * X) * (y * Q)) -
        y * g2 := by
    rw [hWdef, hg2, derivative_mul]
    simp only [C_add, C_1, C_ofNat, C_0, zero_mul, sub_zero]
    ring
  have hP := momentFunctional_pearson (jacobiMoment_succ_of_gt hα hβ) (y * Q)
  rw [← jacobiFunctional_eq] at hP
  have hIW : JacobiGeneric.jacobiFunctional α β W = W.coeff 0 := by
    conv_lhs => rw [hconst]
    exact jacobiFunctional_C α β _
  have hIW2 : JacobiGeneric.jacobiFunctional α β W =
      (2 * (m : K) + α + β + 3) * y.coeff (m + 1) *
        JacobiGeneric.jacobiFunctional α β (y * X ^ (m + 1)) := by
    rw [hsplit, map_sub, map_add, jacobiFunctional_C_mul, hP,
      jacobiFunctional_jacobiShifted_mul_of_natDegree_le hα hβ (m + 1) hyd,
      jacobiFunctional_jacobiShifted_mul_of_natDegree_le hα hβ (m + 1) hg2d, hg2top]
    ring
  rw [hconst, ← hIW, hIW2, coeff_jacobiShifted_self,
    jacobiFunctional_jacobiShifted_mul_X_pow_self (m + 1) hα hβ, jacobiWronskianConstant_eq,
    add_tsub_cancel_right]
  congr 1
  -- the numerical identity
  have hc2 : (0 : K) < α + β + 2 := by linarith
  set z : K := 2 * ((m + 1 : ℕ) : K) + α + β
  have hch : Ring.choose z (m + 1) * ((m + 1).factorial : K) =
      (ascPochhammer K (m + 1)).eval (α + β + 2 + m) := by
    have h1 := Ring.descPochhammer_eq_factorial_smul_choose z (m + 1)
    rw [descPochhammer_smeval_eq_ascPochhammer, ascPochhammer_smeval_eq_eval, nsmul_eq_mul]
      at h1
    rw [mul_comm, ← h1]
    congr 1
    simp only [z]; push_cast; ring
  have hsplitP : (ascPochhammer K (2 * (m + 1))).eval (α + β + 2) =
      (ascPochhammer K m).eval (α + β + 2) *
        ((ascPochhammer K (m + 1)).eval (α + β + 2 + m) * (α + β + 2 * m + 3)) := by
    have h := congrArg (fun p => p.eval (α + β + 2)) (ascPochhammer_mul K m (m + 2))
    simp only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast] at h
    rw [show 2 * (m + 1) = m + (m + 2) by ring, ← h, show m + 2 = (m + 1) + 1 from rfl,
      ascPochhammer_succ_eval]
    push_cast; ring_nf
  have hP1 := ascPochhammer_eval_pos_of_pos m hc2
  have hm0 : (0 : K) ≤ m := Nat.cast_nonneg m
  have hP2 := ascPochhammer_eval_pos_of_pos (m + 1) (show (0 : K) < α + β + 2 + m by
    linarith)
  have hfac : (0 : K) < ((m + 1).factorial : K) := by positivity
  have h3 : (0 : K) < α + β + 2 * m + 3 := by linarith
  have hs : ((-1 : K) ^ (m + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hchoose : Ring.choose z (m + 1) =
      (ascPochhammer K (m + 1)).eval (α + β + 2 + m) / ((m + 1).factorial : K) :=
    eq_div_of_mul_eq hfac.ne' hch
  rw [hsplitP, hchoose]
  field_simp
  rw [hs]
  ring

/-- `C_n > 0` for `α, β > -1`. -/
theorem jacobiWronskianConstant_pos {α β : K} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    0 < JacobiGeneric.jacobiWronskianConstant α β n := by
  rw [jacobiWronskianConstant_eq]
  have h1 := ascPochhammer_eval_pos_of_pos n (show (0 : K) < α + 1 by linarith)
  have h2 := ascPochhammer_eval_pos_of_pos n (show (0 : K) < β + 1 by linarith)
  have h3 := ascPochhammer_eval_pos_of_pos (n - 1) (show (0 : K) < α + β + 2 by linarith)
  have h4 : (0 : K) < (n.factorial : K) := by positivity
  positivity

end OrderedParameters

end ArithmeticOfJacobiPolynomials.JacobiGeneric
