/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.Shift
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Moment functionals and the second polynomial `Q`

A linear functional `I` on `K[X]` is encoded by its moments `μ_j = I(t^j)`, acting
coefficientwise: `I(∑ a_j t^j) = ∑ a_j μ_j`. Attached to it is the linear map
`Q(f)(t) = I_s((f(t) - f(s))/(t - s))`, which on coefficients is
`Q(f)(t) = ∑_j f_j ∑_{k<j} μ_{j-1-k} t^k`.

The Jacobi moments of Section 2.1 of the manuscript are
`μ_j = (α+1)_j / (α+β+2)_j` (rising factorials); they are the moments of the probability
measure `t^α (1-t)^β dt / B(α+1, β+1)` on `(0,1)`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

section General

variable {K : Type*} [CommRing K]

/-- The kernel `I_s((t^j - s^j)/(t - s)) = ∑_{k<j} μ_{j-1-k} t^k`. -/
noncomputable def momentKernel (μ : ℕ → K) (j : ℕ) : K[X] :=
  ∑ k ∈ range j, C (μ (j - 1 - k)) * X ^ k

theorem momentKernel_eq (μ : ℕ → K) (j : ℕ) :
    momentKernel μ j = ∑ k ∈ range j, C (μ (j - 1 - k)) * X ^ k := (rfl)

/-- The linear functional with moments `μ`, acting coefficientwise:
`I(∑ a_j X^j) = ∑ a_j μ_j`. -/
noncomputable def momentFunctional (μ : ℕ → K) : K[X] →ₗ[K] K :=
  Polynomial.lsum fun j => μ j • LinearMap.id

/-- The second polynomial `Q(f)(t) = I_s((f(t) - f(s))/(t - s))`, i.e.
`Q(f) = ∑_j f_j ∑_{k<j} μ_{j-1-k} t^k`. -/
noncomputable def momentQuotient (μ : ℕ → K) : K[X] →ₗ[K] K[X] :=
  Polynomial.lsum fun j => LinearMap.smulRight LinearMap.id (momentKernel μ j)

theorem momentFunctional_apply (μ : ℕ → K) (p : K[X]) :
    momentFunctional μ p = p.sum fun j a => μ j * a := by
  simp [momentFunctional, Polynomial.lsum_apply]

theorem momentQuotient_apply (μ : ℕ → K) (p : K[X]) :
    momentQuotient μ p = p.sum fun j a => C a * momentKernel μ j := by
  simp [momentQuotient, Polynomial.lsum_apply, smul_eq_C_mul]

@[simp] theorem momentFunctional_monomial (μ : ℕ → K) (j : ℕ) (a : K) :
    momentFunctional μ (monomial j a) = μ j * a := by
  rw [momentFunctional_apply, sum_monomial_index]; simp

@[simp] theorem momentQuotient_monomial (μ : ℕ → K) (j : ℕ) (a : K) :
    momentQuotient μ (monomial j a) = C a * momentKernel μ j := by
  rw [momentQuotient_apply, sum_monomial_index]; simp

theorem momentFunctional_C (μ : ℕ → K) (a : K) : momentFunctional μ (C a) = μ 0 * a := by
  rw [← monomial_zero_left, momentFunctional_monomial]

theorem momentFunctional_X_pow (μ : ℕ → K) (j : ℕ) : momentFunctional μ (X ^ j) = μ j := by
  rw [← monomial_one_right_eq_X_pow, momentFunctional_monomial, mul_one]

theorem momentQuotient_C (μ : ℕ → K) (a : K) : momentQuotient μ (C a) = 0 := by
  rw [← monomial_zero_left, momentQuotient_monomial]; simp [momentKernel]

theorem momentQuotient_C_mul (μ : ℕ → K) (a : K) (p : K[X]) :
    momentQuotient μ (C a * p) = C a * momentQuotient μ p := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul]

theorem momentFunctional_C_mul (μ : ℕ → K) (a : K) (p : K[X]) :
    momentFunctional μ (C a * p) = a * momentFunctional μ p := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

theorem momentKernel_succ (μ : ℕ → K) (j : ℕ) :
    momentKernel μ (j + 1) = X * momentKernel μ j + C (μ j) := by
  rw [momentKernel, sum_range_succ', momentKernel, mul_sum]
  congr 1
  · refine sum_congr rfl fun k hk => ?_
    rw [pow_succ]
    have : j + 1 - 1 - (k + 1) = j - 1 - k := by omega
    rw [this]; ring
  · simp

/-- The basic recursion `Q(X f) = X Q(f) + I(f)`. -/
theorem momentQuotient_X_mul (μ : ℕ → K) (p : K[X]) :
    momentQuotient μ (X * p) = X * momentQuotient μ p + C (momentFunctional μ p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [mul_add, map_add, hp, hq]; abel
  | monomial n a =>
    rw [X_mul_monomial, momentQuotient_monomial, momentQuotient_monomial,
      momentFunctional_monomial, momentKernel_succ]
    simp only [C_mul]; ring

/-- Division by a linear factor: `Q((X - z) g) = (X - z) Q(g) + I(g)`. -/
theorem momentQuotient_X_sub_C_mul (μ : ℕ → K) (z : K) (g : K[X]) :
    momentQuotient μ ((X - C z) * g) =
      (X - C z) * momentQuotient μ g + C (momentFunctional μ g) := by
  rw [sub_mul, map_sub, momentQuotient_X_mul, momentQuotient_C_mul]; ring

/-- An induction principle: a property closed under sums and multiplication by `X`, and
holding for constants, holds for all polynomials. -/
theorem induction_C_add_X_mul {motive : K[X] → Prop} (p : K[X]) (C' : ∀ a, motive (C a))
    (add : ∀ p q, motive p → motive q → motive (p + q))
    (X_mul : ∀ p, motive p → motive (X * p)) : motive p := by
  induction p using Polynomial.induction_on with
  | C a => exact C' a
  | add p q hp hq => exact add p q hp hq
  | monomial n a h =>
    have : C a * X ^ (n + 1) = X * (C a * X ^ n) := by ring
    rw [this]; exact X_mul _ h

/-- Compatibility of `I` with ring homomorphisms. -/
theorem momentFunctional_map {L : Type*} [CommRing L] (φ : K →+* L) (μ : ℕ → K) (p : K[X]) :
    momentFunctional (fun j => φ (μ j)) (p.map φ) = φ (momentFunctional μ p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add, map_add, hp, hq]
  | monomial n a => simp

theorem momentKernel_map {L : Type*} [CommRing L] (φ : K →+* L) (μ : ℕ → K) (j : ℕ) :
    momentKernel (fun j => φ (μ j)) j = (momentKernel μ j).map φ := by
  simp [momentKernel, Polynomial.map_sum]

/-- Compatibility of `Q` with ring homomorphisms. -/
theorem momentQuotient_map {L : Type*} [CommRing L] (φ : K →+* L) (μ : ℕ → K) (p : K[X]) :
    momentQuotient (fun j => φ (μ j)) (p.map φ) = (momentQuotient μ p).map φ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add, map_add, hp, hq]
  | monomial n a => simp [momentKernel_map]

/-- The coefficients of `Q(f)`: `[t^k] Q(f) = ∑_j f_j μ_{j-1-k}` over `j > k`. -/
theorem coeff_momentKernel (μ : ℕ → K) (j k : ℕ) :
    (momentKernel μ j).coeff k = if k < j then μ (j - 1 - k) else 0 := by
  simp only [momentKernel, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [sum_ite_eq]; simp

/-- The coefficients of `Q(f)`, as a finite sum. -/
theorem coeff_momentQuotient (μ : ℕ → K) {p : K[X]} {N : ℕ} (hp : p.natDegree < N) (k : ℕ) :
    (momentQuotient μ p).coeff k =
      ∑ j ∈ range N, p.coeff j * if k < j then μ (j - 1 - k) else 0 := by
  rw [momentQuotient_apply, sum_over_range' _ (by simp) N hp, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_momentKernel]

/-- If `deg f ≤ m + 1` then `deg Q(f) ≤ m`. -/
theorem coeff_momentQuotient_eq_zero (μ : ℕ → K) {p : K[X]} {m : ℕ}
    (hp : p.natDegree ≤ m + 1) {k : ℕ} (hk : m + 1 ≤ k) : (momentQuotient μ p).coeff k = 0 := by
  rw [coeff_momentQuotient μ (N := m + 2) (by omega)]
  refine sum_eq_zero fun j hj => ?_
  have : ¬ k < j := by simp only [mem_range] at hj; omega
  simp [this]

/-- If `deg f ≤ m + 1` then `[t^m] Q(f) = [t^{m+1}] f · μ_0`. -/
theorem coeff_momentQuotient_top (μ : ℕ → K) {p : K[X]} {m : ℕ} (hp : p.natDegree ≤ m + 1) :
    (momentQuotient μ p).coeff m = p.coeff (m + 1) * μ 0 := by
  rw [coeff_momentQuotient μ (N := m + 2) (by omega), sum_range_succ, sum_eq_zero]
  · simp
  · intro j hj
    have : ¬ m < j := by simp only [mem_range] at hj; omega
    simp [this]

private lemma momentQuotient_aux (μ : ℕ → K) (A B : K[X]) :
    momentQuotient μ (X * A + ((B - X * B) + (B - X * B))) =
      X * momentQuotient μ A + C (momentFunctional μ A) +
        2 * (momentQuotient μ B - momentQuotient μ (X * B)) := by
  rw [map_add, map_add, map_sub, momentQuotient_X_mul]; ring

end General

section Pearson

variable {K : Type*} [CommRing K] (α β : K) (μ : ℕ → K)

/-- `Q(τ g) = τ Q(g) - (α+β+2) I(g)` for `τ = (α+1) - (α+β+2) X`. -/
theorem momentQuotient_tau_mul (g : K[X]) :
    momentQuotient μ ((C (α + 1) - C (α + β + 2) * X) * g) =
      (C (α + 1) - C (α + β + 2) * X) * momentQuotient μ g -
        C ((α + β + 2) * momentFunctional μ g) := by
  rw [sub_mul, map_sub, momentQuotient_C_mul, mul_assoc, momentQuotient_C_mul,
    momentQuotient_X_mul, C_mul]; ring

theorem momentFunctional_tau_mul (g : K[X]) :
    momentFunctional μ ((C (α + 1) - C (α + β + 2) * X) * g) =
      (α + 1) * momentFunctional μ g - (α + β + 2) * momentFunctional μ (X * g) := by
  rw [sub_mul, map_sub, momentFunctional_C_mul, mul_assoc, momentFunctional_C_mul]

variable {α β μ}

/-- The Pearson identity `I(σ f' + τ f) = 0`, equivalent to the moment recurrence
`μ_{j+1} (α+β+2+j) = μ_j (α+1+j)`. Here `σ = X(1-X)` and `τ = (α+1) - (α+β+2) X`. -/
theorem momentFunctional_pearson
    (hμ : ∀ j : ℕ, μ (j + 1) * (α + β + 2 + j) = μ j * (α + 1 + j)) (f : K[X]) :
    momentFunctional μ (X * (1 - X) * derivative f + (C (α + 1) - C (α + β + 2) * X) * f) =
      0 := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [derivative_add, mul_add, mul_add, add_add_add_comm, map_add, hp, hq, add_zero]
  | monomial n a =>
    rcases n with _ | m
    · have h : X * (1 - X) * derivative (monomial 0 a) +
          (C (α + 1) - C (α + β + 2) * X) * monomial 0 a =
          C ((α + 1) * a) * X ^ 0 - C ((α + β + 2) * a) * X ^ 1 := by
        simp only [monomial_zero_left, C_mul]; simp; ring
      rw [h, map_sub, momentFunctional_C_mul, momentFunctional_C_mul, momentFunctional_X_pow,
        momentFunctional_X_pow]
      have := hμ 0
      simp only [zero_add, Nat.cast_zero, add_zero] at this
      linear_combination (-a) * this
    · have h : X * (1 - X) * derivative (monomial (m + 1) a) +
          (C (α + 1) - C (α + β + 2) * X) * monomial (m + 1) a =
          C (a * (m + 1) + (α + 1) * a) * X ^ (m + 1) -
            C (a * (m + 1) + (α + β + 2) * a) * X ^ (m + 2) := by
        rw [derivative_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]
        simp only [add_tsub_cancel_right, C_mul, C_add, Nat.cast_add, Nat.cast_one, C_1]
        rw [map_natCast]
        ring
      rw [h, map_sub, momentFunctional_C_mul, momentFunctional_C_mul, momentFunctional_X_pow,
        momentFunctional_X_pow]
      have := hμ (m + 1)
      push_cast at this
      linear_combination (-a) * this

/-- The first-order companion identity used for the differential equation of `Q`:
`2σ Q(f)' + (σ' - ρ) Q(f) + c I(f) = Q(2σ f' + τ f) + 2(c+1) f`, where `c = α+β`,
`σ' = 1 - 2X` and `ρ = α - cX`. -/
theorem momentQuotient_first_order (hμ0 : μ 0 = 1)
    (hμ : ∀ j : ℕ, μ (j + 1) * (α + β + 2 + j) = μ j * (α + 1 + j)) (f : K[X]) :
    2 * (X * (1 - X)) * derivative (momentQuotient μ f) +
        (1 - 2 * X - (C α - C (α + β) * X)) * momentQuotient μ f +
        C ((α + β) * momentFunctional μ f) =
      momentQuotient μ (2 * (X * (1 - X)) * derivative f +
        (C (α + 1) - C (α + β + 2) * X) * f) + C (2 * (α + β + 1)) * f := by
  induction f using induction_C_add_X_mul with
  | C' a =>
    simp only [momentQuotient_C, derivative_C, derivative_zero, mul_zero, zero_add, add_zero,
      momentQuotient_tau_mul, momentFunctional_C, hμ0]
    simp only [C_mul, C_add, C_1, C_ofNat]
    ring
  | add p q hp hq =>
    simp only [map_add, mul_add] at hp hq ⊢
    linear_combination hp + hq
  | X_mul p ih =>
    have hP := momentFunctional_pearson hμ p
    have hQX : momentQuotient μ (X * p) =
        X * momentQuotient μ p + C (momentFunctional μ p) := momentQuotient_X_mul μ p
    have hQXX : momentQuotient μ (X * (X * p)) =
        X * (X * momentQuotient μ p + C (momentFunctional μ p)) +
          C (momentFunctional μ (X * p)) := by
      rw [momentQuotient_X_mul, hQX]
    have hexp : 2 * (X * (1 - X)) * derivative (X * p) +
        (C (α + 1) - C (α + β + 2) * X) * (X * p) =
        X * (2 * (X * (1 - X)) * derivative p + (C (α + 1) - C (α + β + 2) * X) * p) +
          ((X * p - X * (X * p)) + (X * p - X * (X * p))) := by
      rw [derivative_mul, derivative_X]; ring
    have hIexp : momentFunctional μ
        (2 * (X * (1 - X)) * derivative p + (C (α + 1) - C (α + β + 2) * X) * p) =
        -((α + 1) * momentFunctional μ p - (α + β + 2) * momentFunctional μ (X * p)) := by
      have e : 2 * (X * (1 - X)) * derivative p + (C (α + 1) - C (α + β + 2) * X) * p =
          (X * (1 - X) * derivative p + (C (α + 1) - C (α + β + 2) * X) * p) +
            (X * (1 - X) * derivative p + (C (α + 1) - C (α + β + 2) * X) * p) -
            (C (α + 1) - C (α + β + 2) * X) * p := by ring
      rw [e, map_sub, map_add, hP, momentFunctional_tau_mul]; ring
    rw [hexp, momentQuotient_aux, hIexp, hQXX, hQX, eq_sub_of_add_eq ih.symm]
    rw [derivative_add, derivative_mul, derivative_X, derivative_C]
    simp only [C_mul, C_add, C_sub, C_neg, C_1, C_ofNat]
    ring

/-- The second-order identity behind the differential equation of `Q`:
`σ Q(f)'' + (σ' - ρ) Q(f)' + c Q(f) = Q(σ f'' + τ f') + 2(c+1) f'`. -/
theorem momentQuotient_second_order (hμ0 : μ 0 = 1)
    (hμ : ∀ j : ℕ, μ (j + 1) * (α + β + 2 + j) = μ j * (α + 1 + j)) (f : K[X]) :
    X * (1 - X) * derivative (derivative (momentQuotient μ f)) +
        (1 - 2 * X - (C α - C (α + β) * X)) * derivative (momentQuotient μ f) +
        C (α + β) * momentQuotient μ f =
      momentQuotient μ (X * (1 - X) * derivative (derivative f) +
        (C (α + 1) - C (α + β + 2) * X) * derivative f) +
        C (2 * (α + β + 1)) * derivative f := by
  induction f using induction_C_add_X_mul with
  | C' a => simp [momentQuotient_C]
  | add p q hp hq =>
    simp only [map_add, mul_add] at hp hq ⊢
    linear_combination hp + hq
  | X_mul p ih =>
    have hP := momentFunctional_pearson hμ (derivative p)
    have hF := momentQuotient_first_order hμ0 hμ p
    have hQX : momentQuotient μ (X * p) =
        X * momentQuotient μ p + C (momentFunctional μ p) := momentQuotient_X_mul μ p
    have hexp : X * (1 - X) * derivative (derivative (X * p)) +
        (C (α + 1) - C (α + β + 2) * X) * derivative (X * p) =
        X * (X * (1 - X) * derivative (derivative p) +
          (C (α + 1) - C (α + β + 2) * X) * derivative p) +
          (2 * (X * (1 - X)) * derivative p + (C (α + 1) - C (α + β + 2) * X) * p) := by
      simp only [derivative_mul, derivative_X, derivative_add, one_mul]
      ring
    rw [hexp, map_add (momentQuotient μ), momentQuotient_X_mul _
      (X * (1 - X) * derivative (derivative p) +
        (C (α + 1) - C (α + β + 2) * X) * derivative p), hP, eq_sub_of_add_eq hF.symm, hQX,
      eq_sub_of_add_eq ih.symm]
    simp only [derivative_mul, derivative_X, derivative_C, derivative_add, one_mul, add_zero,
      map_zero]
    simp only [C_mul, C_add, C_1, C_ofNat]
    ring

end Pearson

section JacobiMoments

/-- The Jacobi moments `μ_j = (α+1)_j / (α+β+2)_j` of (2.2) in the manuscript: the moments
of the probability measure `t^α (1-t)^β dt / B(α+1, β+1)` on `(0,1)`. -/
noncomputable def jacobiMoment (α β : ℚ) (j : ℕ) : ℚ :=
  (ascPochhammer ℚ j).eval (α + 1) / (ascPochhammer ℚ j).eval (α + β + 2)

theorem jacobiMoment_eq (α β : ℚ) (j : ℕ) : jacobiMoment α β j =
    (ascPochhammer ℚ j).eval (α + 1) / (ascPochhammer ℚ j).eval (α + β + 2) := (rfl)

/-- The Jacobi functional `I`, acting coefficientwise with the moments `jacobiMoment`. -/
noncomputable def jacobiFunctional (α β : ℚ) : ℚ[X] →ₗ[ℚ] ℚ :=
  momentFunctional (jacobiMoment α β)

theorem jacobiFunctional_eq (α β : ℚ) :
    jacobiFunctional α β = momentFunctional (jacobiMoment α β) := (rfl)

theorem jacobiMoment_zero (α β : ℚ) : jacobiMoment α β 0 = 1 := by
  simp [jacobiMoment]

theorem jacobiFunctional_C_mul (α β a : ℚ) (p : ℚ[X]) :
    jacobiFunctional α β (C a * p) = a * jacobiFunctional α β p :=
  momentFunctional_C_mul _ a p

theorem jacobiFunctional_C (α β a : ℚ) : jacobiFunctional α β (C a) = a := by
  rw [jacobiFunctional_eq, momentFunctional_C, jacobiMoment_zero, one_mul]

theorem jacobiFunctional_X_pow (α β : ℚ) (j : ℕ) :
    jacobiFunctional α β (X ^ j) = jacobiMoment α β j :=
  momentFunctional_X_pow _ j

theorem ascPochhammer_eval_succ_left (j : ℕ) (x : ℚ) :
    (ascPochhammer ℚ (j + 1)).eval x = x * (ascPochhammer ℚ j).eval (x + 1) := by
  rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp]; simp

theorem ascPochhammer_eval_pos_of_pos (j : ℕ) {x : ℚ} (hx : 0 < x) :
    0 < (ascPochhammer ℚ j).eval x := ascPochhammer_pos j x hx

/-- The moment recurrence `μ_{j+1} (α+β+2+j) = μ_j (α+1+j)`. -/
theorem jacobiMoment_succ {α β : ℚ} (hαβ : 0 < α + β + 2) (j : ℕ) :
    jacobiMoment α β (j + 1) * (α + β + 2 + j) = jacobiMoment α β j * (α + 1 + j) := by
  have h1 := ascPochhammer_eval_pos_of_pos j hαβ
  have h2 : (0 : ℚ) < α + β + 2 + j := by positivity
  simp only [jacobiMoment, ascPochhammer_succ_eval]
  field_simp

/-- Multiplication by `σ = X(1-X)` shifts the parameters:
`I_{α,β}(σ f) = κ I_{α+1,β+1}(f)` with `κ = (α+1)(β+1)/((α+β+2)(α+β+3))`. -/
theorem jacobiFunctional_sigma_mul {α β : ℚ} (hαβ : 0 < α + β + 2) (f : ℚ[X]) :
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
    have hc3 : (0 : ℚ) < α + β + 3 := by linarith
    set A := (ascPochhammer ℚ j).eval (α + 2)
    set B := (ascPochhammer ℚ j).eval (α + β + 3)
    set D := (ascPochhammer ℚ j).eval (α + β + 4)
    have hB : 0 < B := ascPochhammer_eval_pos_of_pos j hc3
    have h2 : (0 : ℚ) < α + β + 3 + j := by positivity
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
      have n2 : (ascPochhammer ℚ (j + 2)).eval (α + 1) = (α + 1) * (A * (α + 2 + j)) := by
        rw [show j + 2 = (j + 1) + 1 from rfl, ascPochhammer_eval_succ_left,
          ascPochhammer_succ_eval, show α + 1 + 1 = α + 2 by ring]
      have d2 : (ascPochhammer ℚ (j + 2)).eval (α + β + 2) =
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

/-- `y_n(t) = P_n^{(α,β)}(1 - 2t)`, the Jacobi polynomial moved to the unit interval. -/
noncomputable def jacobiShifted (α β : ℚ) (n : ℕ) : ℚ[X] := (jacobiP α β n).comp (1 - 2 * X)

theorem jacobiShifted_eq (α β : ℚ) (n : ℕ) :
    jacobiShifted α β n = (jacobiP α β n).comp (1 - 2 * X) := (rfl)

/-- The second polynomial `Q_n(t) = I_s((y_n(t) - y_n(s))/(t - s))` for the Jacobi functional,
i.e. `Q_n(t) = ∑_j y_j ∑_{k<j} μ_{j-1-k} t^k`. -/
noncomputable def jacobiSecondPoly (α β : ℚ) (n : ℕ) : ℚ[X] :=
  momentQuotient (jacobiMoment α β) (jacobiShifted α β n)

theorem jacobiSecondPoly_eq (α β : ℚ) (n : ℕ) :
    jacobiSecondPoly α β n = momentQuotient (jacobiMoment α β) (jacobiShifted α β n) := (rfl)

/-- The constant `C_n = (α+1)_n (β+1)_n / (n! (α+β+2)_{n-1})` of Lemma 2.1. -/
noncomputable def jacobiWronskianConstant (α β : ℚ) (n : ℕ) : ℚ :=
  (ascPochhammer ℚ n).eval (α + 1) * (ascPochhammer ℚ n).eval (β + 1) /
    ((n.factorial : ℚ) * (ascPochhammer ℚ (n - 1)).eval (α + β + 2))

theorem jacobiWronskianConstant_eq (α β : ℚ) (n : ℕ) : jacobiWronskianConstant α β n =
    (ascPochhammer ℚ n).eval (α + 1) * (ascPochhammer ℚ n).eval (β + 1) /
      ((n.factorial : ℚ) * (ascPochhammer ℚ (n - 1)).eval (α + β + 2)) := (rfl)

end JacobiData

section IntegralRepresentation

open MeasureTheory

/-- The Jacobi weight `t^a (1-t)^b` on `(0,1)`. -/
noncomputable def jacobiWeight (a b : ℝ) (x : ℝ) : ℝ := x ^ a * (1 - x) ^ b

theorem jacobiWeight_eq (a b x : ℝ) : jacobiWeight a b x = x ^ a * (1 - x) ^ b := (rfl)

theorem jacobiWeight_ofReal (a b : ℝ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ((jacobiWeight a b x : ℝ) : ℂ) = (x : ℂ) ^ (a : ℂ) * (1 - (x : ℂ)) ^ (b : ℂ) := by
  rw [jacobiWeight, Complex.ofReal_mul, Complex.ofReal_cpow hx0,
    Complex.ofReal_cpow (by linarith), Complex.ofReal_sub, Complex.ofReal_one]

theorem jacobiWeight_pos (a b : ℝ) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    0 < jacobiWeight a b x :=
  mul_pos (Real.rpow_pos_of_pos hx.1 _) (Real.rpow_pos_of_pos (by linarith [hx.2]) _)

theorem jacobiWeight_nonneg (a b : ℝ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ jacobiWeight a b x :=
  mul_nonneg (Real.rpow_nonneg hx0 _) (Real.rpow_nonneg (by linarith) _)

/-- The Beta integral `B(a+1, b+1) = ∫_0^1 t^a (1-t)^b dt`. -/
theorem betaIntegral_eq_integral_jacobiWeight (a b : ℝ) :
    Complex.betaIntegral ((a : ℂ) + 1) ((b : ℂ) + 1) =
      ((∫ x in (0 : ℝ)..1, jacobiWeight a b x : ℝ) : ℂ) := by
  rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le zero_le_one] at hx
  simp only [add_sub_cancel_right]
  rw [jacobiWeight_ofReal a b hx.1 hx.2]

theorem intervalIntegrable_jacobiWeight {a b : ℝ} (ha : -1 < a) (hb : -1 < b) :
    IntervalIntegrable (jacobiWeight a b) volume 0 1 := by
  have hF := Complex.betaIntegral_convergent (u := (a : ℂ) + 1) (v := (b : ℂ) + 1)
    (by simp; linarith) (by simp; linarith)
  have hre : IntervalIntegrable
      (fun x : ℝ => RCLike.re ((x : ℂ) ^ ((a : ℂ) + 1 - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) + 1 - 1)))
      volume 0 1 := by
    rw [intervalIntegrable_iff] at hF ⊢; exact hF.re
  refine hre.congr fun x hx => ?_
  rw [Set.uIoc_of_le zero_le_one] at hx
  simp only [add_sub_cancel_right]
  rw [← jacobiWeight_ofReal a b hx.1.le hx.2]
  rfl

/-- The recurrence `(u+v) B(u+1, v) = u B(u, v)` of the Beta integral. -/
theorem betaIntegral_add_one_left {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    (u + v) * Complex.betaIntegral (u + 1) v = u * Complex.betaIntegral u v := by
  have h1 := Complex.Gamma_mul_Gamma_eq_betaIntegral hu hv
  have h2 := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := u + 1) (by simp; linarith) hv
  have hu0 : u ≠ 0 := by intro h; rw [h] at hu; simp at hu
  have huv : u + v ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [Complex.Gamma_add_one u hu0, show u + 1 + v = (u + v) + 1 by ring,
    Complex.Gamma_add_one (u + v) huv] at h2
  have hG : Complex.Gamma (u + v) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  apply mul_left_cancel₀ hG
  linear_combination u * h1 - h2

/-- The moments `Z_j = ∫_0^1 t^j t^a (1-t)^b dt` of the Jacobi weight. -/
noncomputable def jacobiWeightMoment (a b : ℝ) (j : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, x ^ j * jacobiWeight a b x

theorem jacobiWeightMoment_eq (a b : ℝ) (j : ℕ) :
    jacobiWeightMoment a b j = ∫ x in (0 : ℝ)..1, x ^ j * jacobiWeight a b x := (rfl)

theorem jacobiWeightMoment_eq_integral (a b : ℝ) (j : ℕ) :
    jacobiWeightMoment a b j = ∫ x in (0 : ℝ)..1, jacobiWeight (a + j) b x := by
  rw [jacobiWeightMoment]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
  rw [Set.uIoc_of_le zero_le_one] at hx
  rw [jacobiWeight, jacobiWeight, Real.rpow_add hx.1, Real.rpow_natCast]; ring

theorem jacobiWeightMoment_succ {a b : ℝ} (ha : -1 < a) (hb : -1 < b) (j : ℕ) :
    jacobiWeightMoment a b (j + 1) * (a + b + 2 + j) = jacobiWeightMoment a b j * (a + 1 + j) := by
  have h := betaIntegral_add_one_left (u := ((a + j : ℝ) : ℂ) + 1) (v := (b : ℂ) + 1)
    (by simp; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]) (by simp; linarith)
  rw [show ((a + j : ℝ) : ℂ) + 1 + 1 = ((a + ((j + 1 : ℕ) : ℝ) : ℝ) : ℂ) + 1 by push_cast; ring,
    betaIntegral_eq_integral_jacobiWeight, betaIntegral_eq_integral_jacobiWeight,
    ← jacobiWeightMoment_eq_integral, ← jacobiWeightMoment_eq_integral] at h
  have h' : ((jacobiWeightMoment a b (j + 1) * (a + b + 2 + j) : ℝ) : ℂ) =
      ((jacobiWeightMoment a b j * (a + 1 + j) : ℝ) : ℂ) := by
    push_cast at h ⊢; linear_combination h
  exact_mod_cast h'

theorem jacobiWeightMoment_zero_pos {a b : ℝ} (ha : -1 < a) (hb : -1 < b) :
    0 < jacobiWeightMoment a b 0 := by
  rw [jacobiWeightMoment]
  simp only [pow_zero, one_mul]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on (intervalIntegrable_jacobiWeight ha hb)
    (fun x hx => jacobiWeight_pos a b hx) zero_lt_one

/-- The Jacobi moments are the normalized moments of the Jacobi weight:
`μ_j = ∫_0^1 t^j t^α (1-t)^β dt / ∫_0^1 t^α (1-t)^β dt` (2.2). -/
theorem jacobiWeightMoment_eq_jacobiMoment {α β : ℚ} (hα : -1 < α) (hβ : -1 < β) (j : ℕ) :
    jacobiWeightMoment α β j = (jacobiMoment α β j : ℝ) * jacobiWeightMoment α β 0 := by
  have hα' : (-1 : ℝ) < α := by exact_mod_cast hα
  have hβ' : (-1 : ℝ) < β := by exact_mod_cast hβ
  induction j with
  | zero => rw [jacobiMoment_zero]; simp
  | succ j ih =>
    have h1 := jacobiWeightMoment_succ hα' hβ' j
    have h2 := jacobiMoment_succ (α := α) (β := β) (by linarith) j
    have h2' : ((jacobiMoment α β (j + 1) : ℚ) : ℝ) * ((α : ℝ) + β + 2 + j) =
        (jacobiMoment α β j : ℝ) * ((α : ℝ) + 1 + j) := by exact_mod_cast h2
    have hpos : (0 : ℝ) < (α : ℝ) + β + 2 + j := by
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    apply mul_right_cancel₀ hpos.ne'
    rw [h1, ih]
    linear_combination (jacobiWeightMoment α β 0) * h2'.symm

/-- The real Jacobi functional, `I` extended coefficientwise to `ℝ[X]`. -/
noncomputable def jacobiFunctionalReal (α β : ℚ) : ℝ[X] →ₗ[ℝ] ℝ :=
  momentFunctional fun j => ((jacobiMoment α β j : ℚ) : ℝ)

theorem jacobiFunctionalReal_eq (α β : ℚ) :
    jacobiFunctionalReal α β = momentFunctional fun j => ((jacobiMoment α β j : ℚ) : ℝ) := (rfl)

theorem intervalIntegrable_eval_mul_jacobiWeight {a b : ℝ} (ha : -1 < a) (hb : -1 < b)
    (f : ℝ[X]) : IntervalIntegrable (fun x => f.eval x * jacobiWeight a b x) volume 0 1 :=
  (intervalIntegrable_jacobiWeight ha hb).continuousOn_mul f.continuous.continuousOn

/-- **Integral representation** of the Jacobi functional:
`I(f) · ∫_0^1 t^α (1-t)^β dt = ∫_0^1 f(t) t^α (1-t)^β dt`. -/
theorem jacobiFunctionalReal_mul_integral {α β : ℚ} (hα : -1 < α) (hβ : -1 < β) (f : ℝ[X]) :
    jacobiFunctionalReal α β f * jacobiWeightMoment α β 0 =
      ∫ x in (0 : ℝ)..1, f.eval x * jacobiWeight α β x := by
  have hα' : (-1 : ℝ) < α := by exact_mod_cast hα
  have hβ' : (-1 : ℝ) < β := by exact_mod_cast hβ
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, add_mul, hp, hq, ← intervalIntegral.integral_add
      (intervalIntegrable_eval_mul_jacobiWeight hα' hβ' p)
      (intervalIntegrable_eval_mul_jacobiWeight hα' hβ' q)]
    simp only [eval_add, add_mul]
  | monomial j c =>
    rw [jacobiFunctionalReal_eq, momentFunctional_monomial]
    simp only [eval_monomial]
    rw [show (fun x => c * x ^ j * jacobiWeight α β x) =
        fun x => c * (x ^ j * jacobiWeight α β x) by ext; ring,
      intervalIntegral.integral_const_mul, ← jacobiWeightMoment_eq,
      jacobiWeightMoment_eq_jacobiMoment hα hβ j]
    ring

/-- Positivity: `I(f²) > 0` for every nonzero real polynomial `f`. -/
theorem jacobiFunctionalReal_mul_self_pos {α β : ℚ} (hα : -1 < α) (hβ : -1 < β) {f : ℝ[X]}
    (hf : f ≠ 0) : 0 < jacobiFunctionalReal α β (f * f) := by
  have hα' : (-1 : ℝ) < α := by exact_mod_cast hα
  have hβ' : (-1 : ℝ) < β := by exact_mod_cast hβ
  have hZ := jacobiWeightMoment_zero_pos hα' hβ'
  have hI := jacobiFunctionalReal_mul_integral hα hβ (f * f)
  suffices h : 0 < ∫ x in (0 : ℝ)..1, (f * f).eval x * jacobiWeight α β x by
    rw [← hI] at h; exact pos_of_mul_pos_left h hZ.le
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae'
    (ae_restrict_of_forall_mem measurableSet_uIoc fun x hx => ?_)
    (intervalIntegrable_eval_mul_jacobiWeight hα' hβ' _)]
  · refine ⟨zero_lt_one, ?_⟩
    have hS := Polynomial.finite_setOfPred_isRoot hf
    have hsub : Set.Ioo (0 : ℝ) 1 \ {x | f.IsRoot x} ⊆
        Function.support (fun x => (f * f).eval x * jacobiWeight α β x) ∩ Set.Ioc 0 1 := by
      intro x ⟨hx, hxr⟩
      refine ⟨?_, hx.1, hx.2.le⟩
      have hfx : f.eval x ≠ 0 := hxr
      simp only [Function.mem_support, eval_mul]
      exact (mul_pos (mul_self_pos.mpr hfx) (jacobiWeight_pos _ _ hx)).ne'
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [measure_sdiff_null (hS.measure_zero _), Real.volume_Ioo]
    norm_num
  · rw [Set.uIoc_of_le zero_le_one] at hx
    simp only [Pi.zero_apply, eval_mul]
    exact mul_nonneg (mul_self_nonneg _) (jacobiWeight_nonneg _ _ hx.1.le hx.2)

/-- Nonnegativity: `I(f²) ≥ 0` for every real polynomial `f`. -/
theorem jacobiFunctionalReal_mul_self_nonneg {α β : ℚ} (hα : -1 < α) (hβ : -1 < β)
    (f : ℝ[X]) : 0 ≤ jacobiFunctionalReal α β (f * f) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · exact (jacobiFunctionalReal_mul_self_pos hα hβ hf).le

end IntegralRepresentation

end ArithmeticOfJacobiPolynomials
