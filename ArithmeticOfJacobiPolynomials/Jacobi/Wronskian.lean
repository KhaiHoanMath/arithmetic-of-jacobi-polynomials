/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.MomentFunctional
public import ArithmeticOfJacobiPolynomials.Jacobi.DifferentialEquation

/-!
# The Jacobi identity (Lemma 2.1)

For rational `α, β > -1` and `n ≥ 1`, with `y_n(t) = P_n^{(α,β)}(1-2t)`, the Jacobi moment
functional `I` and `Q_n(t) = I_s((y_n(t) - y_n(s))/(t-s))`, we prove the polynomial identity
`(c+1) y_n^2 + σ (y_n' Q_n - y_n Q_n') + ρ y_n Q_n = C_n`, with `c = α+β`, `σ = t(1-t)`,
`ρ = α - ct` and `C_n = (α+1)_n (β+1)_n / (n! (c+2)_{n-1}) > 0`.

The proof is algebraic:
* the lowering and raising relations of `y_n` (parameter shift `(α,β) → (α+1,β+1)`), which
  give the differential equation `σ y_n'' + τ y_n' + n(n+c+1) y_n = 0` (2.3);
* the orthogonality `I(y_n t^k) = 0` (`k < n`) and the value `I(y_n t^n)`, obtained from the
  raising relation by the Pearson identity (`I(σ f' + τ f) = 0`);
* the differential equation of `Q_n`, which makes the left side constant; the constant is
  computed by applying `I`.

This is an independent algebraic proof of the identity. It adds no hypothesis
to the printed statement; it avoids the real integral and the limit argument of the manuscript.
The main chain uses the manuscript's argument instead, formalized in `SourceStieltjesWronskian`
(transported to rational parameters in `SourceStieltjesRational`).

At every real root `t` of `y_n` we then deduce `|y_n'(t)| ≥ 2 √C_n`, using the positivity of the
Gaussian quadrature weight `I(ℓ²) > 0`, which comes from the integral representation of `I`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-! ### Coefficients, lowering and raising -/

/-- The coefficient `(-1)^k binom(n+α, n-k) binom(n+α+β+k, k)` of `t^k` in `y_n` (2.1). -/
noncomputable def jacobiShiftedCoeff (α β : ℚ) (n k : ℕ) : ℚ :=
  (-1) ^ k * Ring.choose ((n : ℚ) + α) (n - k) * Ring.choose ((n : ℚ) + α + β + k) k

theorem coeff_jacobiShifted (α β : ℚ) (n k : ℕ) :
    (jacobiShifted α β n).coeff k = if k ≤ n then jacobiShiftedCoeff α β n k else 0 := by
  rw [jacobiShifted_eq, jacobiP_comp_one_sub_two_mul_X, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  simp only [mem_range, Nat.lt_succ_iff, jacobiShiftedCoeff]

/-- Lowering: `y_{m+1}^{(α,β)}' = -(m+α+β+2) y_m^{(α+1,β+1)}`. -/
theorem derivative_jacobiShifted (α β : ℚ) (m : ℕ) :
    derivative (jacobiShifted α β (m + 1)) =
      C (-((m : ℚ) + α + β + 2)) * jacobiShifted (α + 1) (β + 1) m := by
  ext k
  rw [coeff_derivative, coeff_C_mul, coeff_jacobiShifted, coeff_jacobiShifted]
  by_cases hk : k ≤ m
  · rw [ite_eq_left (by omega), ite_eq_left hk]
    simp only [jacobiShiftedCoeff]
    rw [show m + 1 - (k + 1) = m - k by omega,
      show ((m + 1 : ℕ) : ℚ) + α + β + ((k + 1 : ℕ) : ℚ) = (m : ℚ) + (α + 1) + (β + 1) + k by
        push_cast; ring,
      show ((m + 1 : ℕ) : ℚ) + α = (m : ℚ) + (α + 1) by push_cast; ring]
    have h := ring_choose_succ_mul ((m : ℚ) + (α + 1) + (β + 1) + k) k
    rw [show (m : ℚ) + (α + 1) + (β + 1) + k - k = m + α + β + 2 by ring] at h
    rw [pow_succ]
    linear_combination (-(-1 : ℚ) ^ k * Ring.choose ((m : ℚ) + (α + 1)) (m - k)) * h
  · rw [ite_eq_right (by omega), ite_eq_right hk]; simp

theorem coeff_sigma_tau_zero (a b : ℚ) (f : ℚ[X]) :
    (X * (1 - X) * derivative f + (C a - C b * X) * f).coeff 0 = a * f.coeff 0 := by
  have e : X * (1 - X) * derivative f + (C a - C b * X) * f =
      X * (derivative f - X * derivative f - C b * f) + C a * f := by ring
  rw [e, coeff_add, coeff_X_mul_zero, coeff_C_mul, zero_add]

theorem coeff_sigma_tau_succ (a b : ℚ) (f : ℚ[X]) (k : ℕ) :
    (X * (1 - X) * derivative f + (C a - C b * X) * f).coeff (k + 1) =
      ((k : ℚ) + 1 + a) * f.coeff (k + 1) - ((k : ℚ) + b) * f.coeff k := by
  have e : X * (1 - X) * derivative f + (C a - C b * X) * f =
      X * derivative f - X * (X * derivative f) + C a * f - C b * (X * f) := by ring
  simp only [e, coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_derivative]
  rcases k with _ | k
  · rw [coeff_X_mul_zero]; push_cast; ring
  · rw [coeff_X_mul, coeff_derivative]; push_cast; ring

/-- Raising (the algebraic Rodrigues recursion):
`(m+1) y_{m+1}^{(α,β)} = σ f' + τ f` with `f = y_m^{(α+1,β+1)}`, `σ = X(1-X)` and
`τ = (α+1) - (α+β+2) X`. -/
theorem jacobiShifted_raising (α β : ℚ) (m : ℕ) :
    C ((m : ℚ) + 1) * jacobiShifted α β (m + 1) =
      X * (1 - X) * derivative (jacobiShifted (α + 1) (β + 1) m) +
        (C (α + 1) - C (α + β + 2) * X) * jacobiShifted (α + 1) (β + 1) m := by
  ext k
  rw [coeff_C_mul]
  rcases k with _ | k
  · rw [coeff_sigma_tau_zero, coeff_jacobiShifted, coeff_jacobiShifted, ite_eq_left (by omega),
      ite_eq_left (by omega)]
    simp only [jacobiShiftedCoeff, pow_zero, one_mul, Nat.cast_zero, add_zero, Nat.sub_zero,
      Ring.choose_zero_right, mul_one]
    have h := ring_choose_succ_mul ((m : ℚ) + (α + 1)) m
    rw [show ((m + 1 : ℕ) : ℚ) + α = (m : ℚ) + (α + 1) by push_cast; ring]
    rw [show (m : ℚ) + (α + 1) - m = α + 1 by ring] at h
    linear_combination h
  · rw [coeff_sigma_tau_succ, coeff_jacobiShifted, coeff_jacobiShifted, coeff_jacobiShifted]
    rcases lt_trichotomy k m with hk | rfl | hk
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_lt hk
      rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
      simp only [jacobiShiftedCoeff]
      rw [show k + i + 1 + 1 - (k + 1) = i + 1 by omega, show k + i + 1 - (k + 1) = i by omega,
        show k + i + 1 - k = i + 1 by omega]
      rw [show ((k + i + 1 + 1 : ℕ) : ℚ) + α + β + ((k + 1 : ℕ) : ℚ) =
            2 * (k : ℚ) + i + α + β + 3 by push_cast; ring,
        show ((k + i + 1 : ℕ) : ℚ) + (α + 1) + (β + 1) + ((k + 1 : ℕ) : ℚ) =
            2 * (k : ℚ) + i + α + β + 3 + 1 by push_cast; ring,
        show ((k + i + 1 : ℕ) : ℚ) + (α + 1) + (β + 1) + (k : ℚ) =
            2 * (k : ℚ) + i + α + β + 3 by push_cast; ring,
        show ((k + i + 1 + 1 : ℕ) : ℚ) + α = (k : ℚ) + i + α + 2 by push_cast; ring,
        show ((k + i + 1 : ℕ) : ℚ) + (α + 1) = (k : ℚ) + i + α + 2 by push_cast; ring]
      have h1 := ring_choose_succ_mul ((k : ℚ) + i + α + 2) i
      rw [show (k : ℚ) + i + α + 2 - i = k + α + 2 by ring] at h1
      have h2 := Ring.choose_succ_succ (2 * (k : ℚ) + i + α + β + 3) k
      have h3 := ring_choose_succ_mul (2 * (k : ℚ) + i + α + β + 3) k
      rw [show 2 * (k : ℚ) + i + α + β + 3 - k = k + i + α + β + 3 by ring] at h3
      push_cast
      linear_combination
        (-(-1 : ℚ) ^ k * Ring.choose (2 * (k : ℚ) + i + α + β + 3 + 1) (k + 1)) * h1 +
        ((-1 : ℚ) ^ k * Ring.choose ((k : ℚ) + i + α + 2) (i + 1) * (i + 1)) * h2 +
        (-(-1 : ℚ) ^ k * Ring.choose ((k : ℚ) + i + α + 2) (i + 1)) * h3
    · rw [ite_eq_left le_rfl, ite_eq_right (by omega), ite_eq_left le_rfl]
      simp only [jacobiShiftedCoeff]
      rw [Nat.sub_self, Nat.sub_self, Ring.choose_zero_right, Ring.choose_zero_right]
      rw [show ((k + 1 : ℕ) : ℚ) + α + β + ((k + 1 : ℕ) : ℚ) = 2 * (k : ℚ) + α + β + 2 by
          push_cast; ring,
        show (k : ℚ) + (α + 1) + (β + 1) + (k : ℚ) = 2 * (k : ℚ) + α + β + 2 by ring]
      have h3 := ring_choose_succ_mul (2 * (k : ℚ) + α + β + 2) k
      rw [show 2 * (k : ℚ) + α + β + 2 - k = k + α + β + 2 by ring] at h3
      linear_combination (-(-1 : ℚ) ^ k) * h3
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; ring

/-- The differential equation (2.3): `σ y_n'' + τ y_n' + n(n+c+1) y_n = 0`. -/
theorem jacobiShifted_ode (α β : ℚ) (n : ℕ) :
    X * (1 - X) * derivative (derivative (jacobiShifted α β n)) +
        (C (α + 1) - C (α + β + 2) * X) * derivative (jacobiShifted α β n) +
        C ((n : ℚ) * (n + α + β + 1)) * jacobiShifted α β n = 0 := by
  rcases n with _ | m
  · have h0 : jacobiShifted α β 0 = C 1 := by
      ext k; rw [coeff_jacobiShifted, coeff_C]
      rcases k with _ | k <;> simp [jacobiShiftedCoeff]
    rw [h0]; simp
  · rw [derivative_jacobiShifted, derivative_C_mul]
    have hr := jacobiShifted_raising α β m
    have e : X * (1 - X) * (C (-((m : ℚ) + α + β + 2)) *
          derivative (jacobiShifted (α + 1) (β + 1) m)) +
        (C (α + 1) - C (α + β + 2) * X) *
          (C (-((m : ℚ) + α + β + 2)) * jacobiShifted (α + 1) (β + 1) m) =
        C (-((m : ℚ) + α + β + 2)) * (X * (1 - X) * derivative (jacobiShifted (α + 1) (β + 1) m) +
          (C (α + 1) - C (α + β + 2) * X) * jacobiShifted (α + 1) (β + 1) m) := by ring
    rw [e, ← hr]
    simp only [C_mul, C_add, C_neg, Nat.cast_add, Nat.cast_one, C_1, C_ofNat]
    ring

theorem jacobiShifted_zero (α β : ℚ) : jacobiShifted α β 0 = 1 := by
  ext k; rw [coeff_jacobiShifted, coeff_one]
  rcases k with _ | k <;> simp [jacobiShiftedCoeff]

theorem natDegree_jacobiShifted_le (α β : ℚ) (n : ℕ) : (jacobiShifted α β n).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_jacobiShifted, ite_eq_right (by intro h; exact absurd h (by omega))]

theorem coeff_jacobiShifted_self (α β : ℚ) (n : ℕ) :
    (jacobiShifted α β n).coeff n = (-1) ^ n * Ring.choose (2 * (n : ℚ) + α + β) n := by
  rw [coeff_jacobiShifted, ite_eq_left le_rfl, jacobiShiftedCoeff, Nat.sub_self,
    Ring.choose_zero_right, show (n : ℚ) + α + β + n = 2 * n + α + β by ring, mul_one]

/-! ### Orthogonality and the norm -/

theorem jacobiMoment_succ_of_gt {α β : ℚ} (hα : -1 < α) (hβ : -1 < β) (j : ℕ) :
    jacobiMoment α β (j + 1) * (α + β + 2 + j) = jacobiMoment α β j * (α + 1 + j) :=
  jacobiMoment_succ (by linarith) j

/-- The raising relation under `I`:
`(m+1) I_{α,β}(y_{m+1} g) = -κ I_{α+1,β+1}(y_m^{(α+1,β+1)} g')`. -/
theorem jacobiFunctional_jacobiShifted_succ_mul {α β : ℚ} (hα : -1 < α) (hβ : -1 < β)
    (m : ℕ) (g : ℚ[X]) :
    ((m : ℚ) + 1) * jacobiFunctional α β (jacobiShifted α β (m + 1) * g) =
      -((α + 1) * (β + 1) / ((α + β + 2) * (α + β + 3))) *
        jacobiFunctional (α + 1) (β + 1) (jacobiShifted (α + 1) (β + 1) m * derivative g) := by
  set f := jacobiShifted (α + 1) (β + 1) m
  have hr := jacobiShifted_raising α β m
  have hP := momentFunctional_pearson (jacobiMoment_succ_of_gt hα hβ) (f * g)
  have e : C ((m : ℚ) + 1) * (jacobiShifted α β (m + 1) * g) =
      (X * (1 - X) * derivative (f * g) + (C (α + 1) - C (α + β + 2) * X) * (f * g)) -
        X * (1 - X) * (f * derivative g) := by
    rw [← mul_assoc, hr, derivative_mul]; ring
  rw [← jacobiFunctional_eq] at hP
  rw [← jacobiFunctional_C_mul, e, map_sub, hP, jacobiFunctional_sigma_mul (by linarith)]
  ring

/-- Orthogonality: `I(y_n t^k) = 0` for `k < n`. -/
theorem jacobiFunctional_jacobiShifted_mul_X_pow :
    ∀ (n : ℕ) {α β : ℚ}, -1 < α → -1 < β → ∀ k < n,
      jacobiFunctional α β (jacobiShifted α β n * X ^ k) = 0 := by
  intro n
  induction n with
  | zero => intro α β _ _ k hk; omega
  | succ m ih =>
    intro α β hα hβ k hk
    have h := jacobiFunctional_jacobiShifted_succ_mul hα hβ m (X ^ k)
    have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
    rcases k with _ | k
    · simp only [pow_zero, derivative_one, mul_zero, map_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hm
    · rw [derivative_X_pow, add_tsub_cancel_right, mul_left_comm, jacobiFunctional_C_mul,
        ih (by linarith) (by linarith) k (by omega), mul_zero, mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hm

/-- The top value `I(y_n t^n) = (-1)^n (α+1)_n (β+1)_n / (α+β+2)_{2n}`. -/
theorem jacobiFunctional_jacobiShifted_mul_X_pow_self :
    ∀ (n : ℕ) {α β : ℚ}, -1 < α → -1 < β →
      jacobiFunctional α β (jacobiShifted α β n * X ^ n) =
        (-1) ^ n * (ascPochhammer ℚ n).eval (α + 1) * (ascPochhammer ℚ n).eval (β + 1) /
          (ascPochhammer ℚ (2 * n)).eval (α + β + 2) := by
  intro n
  induction n with
  | zero =>
    intro α β _ _
    rw [jacobiShifted_zero, pow_zero, mul_one, ← C_1, jacobiFunctional_C]
    simp
  | succ m ih =>
    intro α β hα hβ
    have h := jacobiFunctional_jacobiShifted_succ_mul hα hβ m (X ^ (m + 1))
    have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
    rw [derivative_X_pow, add_tsub_cancel_right, mul_left_comm, jacobiFunctional_C_mul,
      ih (by linarith) (by linarith)] at h
    have hc2 : (0 : ℚ) < α + β + 2 := by linarith
    have hc3 : (0 : ℚ) < α + β + 3 := by linarith
    have hD := ascPochhammer_eval_pos_of_pos (2 * m) (show (0 : ℚ) < α + β + 4 by linarith)
    have e1 : (ascPochhammer ℚ (m + 1)).eval (α + 1) =
        (α + 1) * (ascPochhammer ℚ m).eval (α + 2) := by
      rw [ascPochhammer_eval_succ_left]; ring_nf
    have e2 : (ascPochhammer ℚ (m + 1)).eval (β + 1) =
        (β + 1) * (ascPochhammer ℚ m).eval (β + 2) := by
      rw [ascPochhammer_eval_succ_left]; ring_nf
    have e3 : (ascPochhammer ℚ (2 * (m + 1))).eval (α + β + 2) =
        (α + β + 2) * ((α + β + 3) * (ascPochhammer ℚ (2 * m)).eval (α + β + 4)) := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, ascPochhammer_eval_succ_left,
        ascPochhammer_eval_succ_left]; ring_nf
    rw [show α + 1 + 1 = α + 2 by ring, show β + 1 + 1 = β + 2 by ring,
      show α + 1 + (β + 1) + 2 = α + β + 4 by ring] at h
    rw [e1, e2, e3]
    have h' : jacobiFunctional α β (jacobiShifted α β (m + 1) * X ^ (m + 1)) =
        -((α + 1) * (β + 1) / ((α + β + 2) * (α + β + 3))) *
          ((-1) ^ m * (ascPochhammer ℚ m).eval (α + 2) * (ascPochhammer ℚ m).eval (β + 2) /
            (ascPochhammer ℚ (2 * m)).eval (α + β + 4)) := by
      apply mul_left_cancel₀ hm
      rw [h]; push_cast; ring
    rw [h']
    field_simp
    ring

/-- `I(y_n g) = [t^n] g · I(y_n t^n)` whenever `deg g ≤ n` (orthogonality). -/
theorem jacobiFunctional_jacobiShifted_mul_of_natDegree_le {α β : ℚ} (hα : -1 < α)
    (hβ : -1 < β) (n : ℕ) {g : ℚ[X]} (hg : g.natDegree ≤ n) :
    jacobiFunctional α β (jacobiShifted α β n * g) =
      g.coeff n * jacobiFunctional α β (jacobiShifted α β n * X ^ n) := by
  conv_lhs => rw [as_sum_range' g (n + 1) (by omega)]
  rw [mul_sum, map_sum, sum_range_succ, sum_eq_zero]
  · rw [zero_add, ← C_mul_X_pow_eq_monomial, mul_left_comm, jacobiFunctional_C_mul]
  · intro k hk
    rw [← C_mul_X_pow_eq_monomial, mul_left_comm, jacobiFunctional_C_mul,
      jacobiFunctional_jacobiShifted_mul_X_pow n hα hβ k (by simpa using hk), mul_zero]

/-! ### The identity (2.2) -/

/-- The left side of (2.2) has zero derivative. -/
theorem derivative_jacobiWronskian {α β : ℚ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    derivative (C (α + β + 1) * jacobiShifted α β n ^ 2 +
      X * (1 - X) * (derivative (jacobiShifted α β n) * jacobiSecondPoly α β n -
        jacobiShifted α β n * derivative (jacobiSecondPoly α β n)) +
      (C α - C (α + β) * X) * jacobiShifted α β n * jacobiSecondPoly α β n) = 0 := by
  have hE := momentQuotient_second_order (jacobiMoment_zero α β) (jacobiMoment_succ_of_gt hα hβ)
    (jacobiShifted α β n)
  have hode := jacobiShifted_ode α β n
  rw [← jacobiSecondPoly_eq] at hE
  have hQ : momentQuotient (jacobiMoment α β)
      (X * (1 - X) * derivative (derivative (jacobiShifted α β n)) +
        (C (α + 1) - C (α + β + 2) * X) * derivative (jacobiShifted α β n)) =
      -(C ((n : ℚ) * (n + α + β + 1)) * jacobiSecondPoly α β n) := by
    have e : X * (1 - X) * derivative (derivative (jacobiShifted α β n)) +
        (C (α + 1) - C (α + β + 2) * X) * derivative (jacobiShifted α β n) =
        C (-((n : ℚ) * (n + α + β + 1))) * jacobiShifted α β n := by
      rw [C_neg]; linear_combination hode
    rw [e, momentQuotient_C_mul, ← jacobiSecondPoly_eq, C_neg, neg_mul]
  rw [hQ] at hE
  set y := jacobiShifted α β n
  set Q := jacobiSecondPoly α β n
  simp only [derivative_add, derivative_mul, derivative_sub, derivative_C, derivative_X,
    derivative_sq, derivative_one, zero_mul, zero_add, zero_sub]
  simp only [C_add, C_1, C_ofNat, C_mul] at hE hode ⊢
  linear_combination Q * hode - y * hE

/-- **Lemma 2.1, identity (2.2).** For rational `α, β > -1` and `n ≥ 1`,
`(c+1) y_n² + σ (y_n' Q_n - y_n Q_n') + ρ y_n Q_n = C_n` with `c = α+β`, `σ = t(1-t)`,
`ρ = α - ct` and `C_n = (α+1)_n (β+1)_n / (n! (c+2)_{n-1})`. -/
theorem jacobi_wronskian {α β : ℚ} (hα : -1 < α) (hβ : -1 < β) {n : ℕ} (hn : 1 ≤ n) :
    C (α + β + 1) * jacobiShifted α β n ^ 2 +
      X * (1 - X) * (derivative (jacobiShifted α β n) * jacobiSecondPoly α β n -
        jacobiShifted α β n * derivative (jacobiSecondPoly α β n)) +
      (C α - C (α + β) * X) * jacobiShifted α β n * jacobiSecondPoly α β n =
    C (jacobiWronskianConstant α β n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hW' := derivative_jacobiWronskian hα hβ (m + 1)
  set y := jacobiShifted α β (m + 1) with hy
  set Q := jacobiSecondPoly α β (m + 1) with hQdef
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
      (2 * (k : ℚ) + 3) * Q.coeff (k + 1) - (2 * (k : ℚ) + 2) * Q.coeff k := by
    intro k
    rw [hg2, coeff_add, coeff_sigma_tau_succ, coeff_sigma_tau_succ]; ring
  have hg2d : g2.natDegree ≤ m + 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    rw [hg2coeff, hQzero k (by omega), hQzero (k + 1) (by omega)]; ring
  have hg2top : g2.coeff (m + 1) = -(2 * (m : ℚ) + 2) * y.coeff (m + 1) := by
    rw [hg2coeff, hQzero (m + 1) le_rfl, hQtop]; ring
  have hsplit : W = C (α + β + 1) * (y * y) +
      (X * (1 - X) * derivative (y * Q) + (C (α + 1) - C (α + β + 2) * X) * (y * Q)) -
        y * g2 := by
    rw [hWdef, hg2, derivative_mul]
    simp only [C_add, C_1, C_ofNat, C_0, zero_mul, sub_zero]
    ring
  have hP := momentFunctional_pearson (jacobiMoment_succ_of_gt hα hβ) (y * Q)
  rw [← jacobiFunctional_eq] at hP
  have hIW : jacobiFunctional α β W = W.coeff 0 := by
    conv_lhs => rw [hconst]
    exact jacobiFunctional_C α β _
  have hIW2 : jacobiFunctional α β W =
      (2 * (m : ℚ) + α + β + 3) * y.coeff (m + 1) *
        jacobiFunctional α β (y * X ^ (m + 1)) := by
    rw [hsplit, map_sub, map_add, jacobiFunctional_C_mul, hP,
      jacobiFunctional_jacobiShifted_mul_of_natDegree_le hα hβ (m + 1) hyd,
      jacobiFunctional_jacobiShifted_mul_of_natDegree_le hα hβ (m + 1) hg2d, hg2top]
    ring
  rw [hconst, ← hIW, hIW2, coeff_jacobiShifted_self,
    jacobiFunctional_jacobiShifted_mul_X_pow_self (m + 1) hα hβ, jacobiWronskianConstant_eq,
    add_tsub_cancel_right]
  congr 1
  -- the numerical identity
  have hc2 : (0 : ℚ) < α + β + 2 := by linarith
  set z : ℚ := 2 * ((m + 1 : ℕ) : ℚ) + α + β
  have hch : Ring.choose z (m + 1) * ((m + 1).factorial : ℚ) =
      (ascPochhammer ℚ (m + 1)).eval (α + β + 2 + m) := by
    have h1 := Ring.descPochhammer_eq_factorial_smul_choose z (m + 1)
    rw [descPochhammer_smeval_eq_ascPochhammer, ascPochhammer_smeval_eq_eval, nsmul_eq_mul]
      at h1
    rw [mul_comm, ← h1]
    congr 1
    simp only [z]; push_cast; ring
  have hsplitP : (ascPochhammer ℚ (2 * (m + 1))).eval (α + β + 2) =
      (ascPochhammer ℚ m).eval (α + β + 2) *
        ((ascPochhammer ℚ (m + 1)).eval (α + β + 2 + m) * (α + β + 2 * m + 3)) := by
    have h := congrArg (fun p => p.eval (α + β + 2)) (ascPochhammer_mul ℚ m (m + 2))
    simp only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast] at h
    rw [show 2 * (m + 1) = m + (m + 2) by ring, ← h, show m + 2 = (m + 1) + 1 from rfl,
      ascPochhammer_succ_eval]
    push_cast; ring_nf
  have hP1 := ascPochhammer_eval_pos_of_pos m hc2
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hP2 := ascPochhammer_eval_pos_of_pos (m + 1) (show (0 : ℚ) < α + β + 2 + m by
    linarith)
  have hfac : (0 : ℚ) < ((m + 1).factorial : ℚ) := by positivity
  have h3 : (0 : ℚ) < α + β + 2 * m + 3 := by linarith
  have hs : ((-1 : ℚ) ^ (m + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hchoose : Ring.choose z (m + 1) =
      (ascPochhammer ℚ (m + 1)).eval (α + β + 2 + m) / ((m + 1).factorial : ℚ) :=
    eq_div_of_mul_eq hfac.ne' hch
  rw [hsplitP, hchoose]
  field_simp
  rw [hs]
  ring

/-- `C_n > 0` for `α, β > -1`. -/
theorem jacobiWronskianConstant_pos {α β : ℚ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    0 < jacobiWronskianConstant α β n := by
  rw [jacobiWronskianConstant_eq]
  have h1 := ascPochhammer_eval_pos_of_pos n (show (0 : ℚ) < α + 1 by linarith)
  have h2 := ascPochhammer_eval_pos_of_pos n (show (0 : ℚ) < β + 1 by linarith)
  have h3 := ascPochhammer_eval_pos_of_pos (n - 1) (show (0 : ℚ) < α + β + 2 by linarith)
  have h4 : (0 : ℚ) < (n.factorial : ℚ) := by positivity
  positivity

/-! ### The real consequence: the derivative at a root -/

theorem jacobiFunctionalReal_map (α β : ℚ) (p : ℚ[X]) :
    jacobiFunctionalReal α β (p.map (algebraMap ℚ ℝ)) = (jacobiFunctional α β p : ℝ) := by
  have h := momentFunctional_map (algebraMap ℚ ℝ) (jacobiMoment α β) p
  simp only [eq_ratCast] at h
  rw [jacobiFunctionalReal_eq, jacobiFunctional_eq]; exact h

theorem momentQuotient_jacobiMoment_map (α β : ℚ) (p : ℚ[X]) :
    momentQuotient (fun j => ((jacobiMoment α β j : ℚ) : ℝ)) (p.map (algebraMap ℚ ℝ)) =
      (momentQuotient (jacobiMoment α β) p).map (algebraMap ℚ ℝ) := by
  have h := momentQuotient_map (algebraMap ℚ ℝ) (jacobiMoment α β) p
  simp only [eq_ratCast] at h
  exact h

/-- Orthogonality over `ℝ`: `I(y_n h) = 0` for every real polynomial `h` of degree `< n`. -/
theorem jacobiFunctionalReal_jacobiShifted_mul {α β : ℚ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ)
    {h : ℝ[X]} (hh : h.natDegree < n) :
    jacobiFunctionalReal α β ((jacobiShifted α β n).map (algebraMap ℚ ℝ) * h) = 0 := by
  conv_lhs => rw [as_sum_range' h n hh]
  rw [mul_sum, map_sum]
  refine sum_eq_zero fun k hk => ?_
  rw [← C_mul_X_pow_eq_monomial, mul_left_comm, jacobiFunctionalReal_eq, momentFunctional_C_mul,
    ← jacobiFunctionalReal_eq,
    show (X ^ k : ℝ[X]) = (X ^ k : ℚ[X]).map (algebraMap ℚ ℝ) by simp, ← Polynomial.map_mul,
    jacobiFunctionalReal_map,
    jacobiFunctional_jacobiShifted_mul_X_pow n hα hβ k (by simpa using hk)]
  simp

/-- **Lemma 2.1, root bound (2.4).** At every real root `t` of `y_n` one has
`|y_n'(t)| ≥ 2 √C_n`; moreover `0 < t < 1`. The proof uses the Gaussian quadrature weight
`ω = I(ℓ) = I(ℓ²) > 0` of `t`, where `ℓ = y_n / ((X - t) y_n'(t))`, and the root identity
`C_n = t(1-t) y_n'(t)² ω`. -/
theorem jacobi_root_derivative_lower {α β : ℚ} (hα : -1 < α) (hβ : -1 < β) {n : ℕ}
    (hn : 1 ≤ n) {t : ℝ} (ht : aeval t (jacobiShifted α β n) = 0) :
    2 * Real.sqrt (jacobiWronskianConstant α β n) ≤
        |aeval t (derivative (jacobiShifted α β n))| ∧ 0 < t ∧ t < 1 := by
  set y := jacobiShifted α β n with hy
  set yR := y.map (algebraMap ℚ ℝ) with hyR
  have hroot : yR.IsRoot t := by rw [IsRoot, hyR, eval_map_algebraMap]; exact ht
  set g := yR /ₘ (X - C t) with hg
  have hyg : (X - C t) * g = yR := mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hder : aeval t (derivative y) = g.eval t := by
    rw [← eval_map_algebraMap, ← derivative_map, ← hyR, ← hyg, derivative_mul]; simp
  have hQ : aeval t (jacobiSecondPoly α β n) = jacobiFunctionalReal α β g := by
    rw [← eval_map_algebraMap, jacobiSecondPoly_eq, ← momentQuotient_jacobiMoment_map, ← hyR,
      ← hyg, momentQuotient_X_sub_C_mul, ← jacobiFunctionalReal_eq]
    simp
  have hW := congrArg (aeval t) (jacobi_wronskian hα hβ hn)
  simp only [map_add, map_mul, map_sub, map_pow, aeval_C, aeval_X, map_one, ← hy, ht] at hW
  rw [hder, hQ] at hW
  set u := g.eval t
  set v := jacobiFunctionalReal α β g
  set Cn : ℝ := (jacobiWronskianConstant α β n : ℝ)
  have hC : 0 < Cn := by
    simp only [Cn]; exact_mod_cast jacobiWronskianConstant_pos hα hβ n
  have key : t * (1 - t) * (u * v) = Cn := by
    have : algebraMap ℚ ℝ (jacobiWronskianConstant α β n) = Cn := by simp [Cn]
    rw [this] at hW
    linear_combination hW
  -- degrees
  have hgdeg : g.natDegree < n := by
    rw [hg, natDegree_divByMonic _ (monic_X_sub_C t), natDegree_X_sub_C]
    have : yR.natDegree ≤ n := (natDegree_map_le (f := algebraMap ℚ ℝ) (p := y)).trans
      (natDegree_jacobiShifted_le α β n)
    omega
  set h := (g - C u) /ₘ (X - C t) with hh
  have hgh : (X - C t) * h = g - C u :=
    mul_divByMonic_eq_iff_isRoot.mpr (by simp [IsRoot, u])
  have hhdeg : h.natDegree < n := by
    rw [hh, natDegree_divByMonic _ (monic_X_sub_C t), natDegree_sub_C]; omega
  -- `I(g²) = g(t) I(g)`
  have hgg : jacobiFunctionalReal α β (g * g) = u * v := by
    have e : g * g = C u * g + yR * h := by
      rw [← hyg]; linear_combination (-g) * hgh
    rw [e, map_add, jacobiFunctionalReal_eq, momentFunctional_C_mul, ← jacobiFunctionalReal_eq,
      jacobiFunctionalReal_jacobiShifted_mul hα hβ n hhdeg, add_zero]
  have hg0 : g ≠ 0 := by
    intro h0
    have : u = 0 := by simp [u, h0]
    rw [this] at key; simp at key; linarith
  have hpos : 0 < u * v := hgg ▸ jacobiFunctionalReal_mul_self_pos hα hβ hg0
  -- Cauchy–Schwarz: `I(g)² ≤ I(g²)`
  have hCS : v ^ 2 ≤ u * v := by
    have h0 := jacobiFunctionalReal_mul_self_nonneg hα hβ (g - C v)
    have e : (g - C v) * (g - C v) = g * g - C (2 * v) * g + C (v ^ 2) := by
      simp only [C_mul, C_pow, C_ofNat]; ring
    rw [e, map_add, map_sub, jacobiFunctionalReal_eq, momentFunctional_C_mul, momentFunctional_C,
      ← jacobiFunctionalReal_eq, hgg] at h0
    simp only [jacobiMoment_zero, Rat.cast_one, one_mul] at h0
    nlinarith
  have hσ : 0 < t * (1 - t) := by
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith
  have ht0 : 0 < t := by
    by_contra h'; rw [not_lt] at h'; nlinarith
  have ht1 : t < 1 := by
    by_contra h'; rw [not_lt] at h'; nlinarith
  refine ⟨?_, ht0, ht1⟩
  rw [hder]
  have h4 : 4 * Cn ≤ u ^ 2 := by nlinarith [sq_nonneg (t - 1 / 2), sq_nonneg (u - v)]
  have hs := Real.sq_sqrt hC.le
  have hs0 := Real.sqrt_nonneg Cn
  nlinarith [abs_nonneg u, sq_abs u]

end ArithmeticOfJacobiPolynomials
