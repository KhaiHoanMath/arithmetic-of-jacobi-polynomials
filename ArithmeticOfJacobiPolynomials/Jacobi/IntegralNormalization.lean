/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.Endpoints
public import ArithmeticOfJacobiPolynomials.Jacobi.DifferentialEquation
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Data.Int.ModEq
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Data.Nat.Prime.Int

/-!
# The integral normalization `K_n^{α,β}` of Jacobi polynomials

For integers `a, u, D, r` the polynomial (eq. (5.8) of the manuscript, §5.1)
`K_n(X) = ∑_{j=0}^n binom(n, j) ∏_{k=j+1}^n (u k + a) ∏_{k=1}^j (D n + r + D k) X^j ∈ ℤ[X]`
equals `u^n n! P_n^{(α,β)}(1 + (2D/u) X)` when `α = a/u` and `r = D(α + β)` (5.7).
For `D = 6` this is (5.17) (§5.4).

We also prove the differential equation of `K_n` over `ℤ`,
`X (D X + u) K'' + [(a + u) + (r + 2D) X] K' = n (D n + r + D) K`,
which is the Jacobi equation (5.6) transported by the affine change of variables.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- The `j`-th coefficient `binom(n, j) ∏_{k=j+1}^n (u k + a) ∏_{k=1}^j (D n + r + D k)` of
`K_n` in (5.8). -/
def integralJacobiCoeff (a u D r : ℤ) (n j : ℕ) : ℤ :=
  (n.choose j : ℤ) * (∏ k ∈ Ioc j n, (u * k + a)) * ∏ k ∈ Icc 1 j, (D * n + r + D * k)

theorem integralJacobiCoeff_eq (a u D r : ℤ) (n j : ℕ) : integralJacobiCoeff a u D r n j =
    (n.choose j : ℤ) * (∏ k ∈ Ioc j n, (u * k + a)) * ∏ k ∈ Icc 1 j, (D * n + r + D * k) :=
  (rfl)

/-- The integral normalization `K_n^{α,β}` of (5.8), for `α = a/u` and `r = D(α + β)`:
`K_n(X) = ∑_{j=0}^n binom(n, j) ∏_{k=j+1}^n (u k + a) ∏_{k=1}^j (D n + r + D k) X^j`. -/
noncomputable def integralJacobi (a u D r : ℤ) (n : ℕ) : ℤ[X] :=
  ∑ j ∈ range (n + 1), C ((n.choose j : ℤ) * (∏ k ∈ Ioc j n, (u * k + a)) *
    ∏ k ∈ Icc 1 j, (D * n + r + D * k)) * X ^ j

theorem integralJacobi_eq (a u D r : ℤ) (n : ℕ) : integralJacobi a u D r n =
    ∑ j ∈ range (n + 1), C ((n.choose j : ℤ) * (∏ k ∈ Ioc j n, (u * k + a)) *
      ∏ k ∈ Icc 1 j, (D * n + r + D * k)) * X ^ j := (rfl)

theorem coeff_integralJacobi (a u D r : ℤ) (n j : ℕ) :
    (integralJacobi a u D r n).coeff j = if j ≤ n then integralJacobiCoeff a u D r n j else 0 := by
  rw [integralJacobi_eq, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, mem_range, Nat.lt_succ_iff,
    integralJacobiCoeff_eq]

/-- `binom(n+y, n-j) (n-j)! = ∏_{k=j+1}^n (k + y)`. -/
theorem ring_choose_mul_factorial_eq_prod_Ioc (y : ℚ) {j n : ℕ} (hjn : j ≤ n) :
    Ring.choose ((n : ℚ) + y) (n - j) * ((n - j).factorial : ℚ) =
      ∏ k ∈ Ioc j n, ((k : ℚ) + y) := by
  induction n, hjn using Nat.le_induction with
  | base => simp
  | succ n hjn ih =>
    rw [prod_Ioc_succ_top hjn, ← ih, show n + 1 - j = (n - j) + 1 by omega, Nat.factorial_succ]
    have h := ring_choose_add_one_succ_mul ((n : ℚ) + y) (n - j)
    push_cast at h ⊢
    rw [show (n : ℚ) + 1 + y = n + y + 1 by ring]
    linear_combination ((n - j).factorial : ℚ) * h

/-- `binom(w+j, j) j! = ∏_{k=1}^j (w + k)`. -/
theorem ring_choose_mul_factorial_eq_prod_Icc (w : ℚ) (j : ℕ) :
    Ring.choose (w + j) j * (j.factorial : ℚ) = ∏ k ∈ Icc 1 j, (w + k) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [prod_Icc_succ_top (by omega), ← ih, Nat.factorial_succ]
    have h := ring_choose_add_one_succ_mul (w + j) j
    push_cast at h ⊢
    rw [show w + (j + 1) = w + j + 1 by ring]
    linear_combination (j.factorial : ℚ) * h

/-- The scalar identity behind (5.8). -/
theorem integralJacobiCoeff_cast (a u D r : ℤ) (β : ℚ) {n j : ℕ} (hjn : j ≤ n) (hu : u ≠ 0)
    (hr : (r : ℚ) = D * ((a : ℚ) / u + β)) :
    (integralJacobiCoeff a u D r n j : ℚ) = (u : ℚ) ^ n * n.factorial *
      (Ring.choose ((n : ℚ) + a / u) (n - j) * Ring.choose ((n : ℚ) + a / u + β + j) j) *
      ((D : ℚ) / u) ^ j := by
  have huq : (u : ℚ) ≠ 0 := by exact_mod_cast hu
  have h1 : ∏ k ∈ Ioc j n, ((u : ℚ) * k + a) =
      (u : ℚ) ^ (n - j) * (Ring.choose ((n : ℚ) + a / u) (n - j) * ((n - j).factorial : ℚ)) := by
    rw [ring_choose_mul_factorial_eq_prod_Ioc _ hjn, ← Nat.card_Ioc j n, ← prod_const,
      ← prod_mul_distrib]
    refine prod_congr rfl fun k _ => ?_
    field_simp
  have h2 : ∏ k ∈ Icc 1 j, ((D : ℚ) * n + r + D * k) =
      (D : ℚ) ^ j * (Ring.choose ((n : ℚ) + a / u + β + j) j * (j.factorial : ℚ)) := by
    rw [ring_choose_mul_factorial_eq_prod_Icc]
    have hc : (D : ℚ) ^ j = ∏ _k ∈ Icc 1 j, (D : ℚ) := by rw [prod_const]; simp
    rw [hc, ← prod_mul_distrib]
    refine prod_congr rfl fun k _ => ?_
    rw [hr]; ring
  rw [integralJacobiCoeff_eq]
  push_cast
  rw [h1, h2]
  have hfac : (n.factorial : ℚ) = n.choose j * j.factorial * (n - j).factorial := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hjn).symm
  rw [hfac, div_pow]
  have hpow : (u : ℚ) ^ n = u ^ (n - j) * u ^ j := by rw [← pow_add]; congr 1; omega
  rw [hpow]
  field_simp

/-- **The integral normalization (5.8)**: if `α = a/u` and `r = D(α + β)`, then
`K_n(X) = u^n n! P_n^{(α,β)}(1 + (2D/u) X)`. -/
theorem integralJacobi_map (a u D r : ℤ) (β : ℚ) (n : ℕ) (hu : u ≠ 0)
    (hr : (r : ℚ) = D * ((a : ℚ) / u + β)) :
    (integralJacobi a u D r n).map (Int.castRingHom ℚ) =
      C ((u : ℚ) ^ n * n.factorial) * (jacobiP ((a : ℚ) / u) β n).comp
        (1 + C (2 * (D : ℚ) / u) * X) := by
  have hlin : (1 + C (2 * (D : ℚ) / u) * X : ℚ[X]) = (2 * X + 1).comp (C ((D : ℚ) / u) * X) := by
    simp only [add_comp, mul_comp, X_comp, one_comp, ofNat_comp]
    rw [show (2 * (D : ℚ) / u) = 2 * (D / u) by ring, C_mul, C_ofNat]; ring
  rw [hlin, ← comp_assoc, jacobiP_comp_two_mul_X_add_one, Polynomial.sum_comp, integralJacobi_eq,
    Polynomial.map_sum, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, mul_comp, C_comp, pow_comp, X_comp,
    mul_pow, ← C_pow]
  have := integralJacobiCoeff_cast a u D r β hjn hu hr
  rw [integralJacobiCoeff_eq] at this
  rw [eq_intCast, this]
  simp only [C_mul]
  ring

/-- The quadratic form of (5.8) used in Proposition 5.2:
`K_n(c' X^2) = u^n n! P_n^{(α,β)}(1 + (2Dc'/u) X^2)`. -/
theorem integralJacobi_map_comp_C_mul_X_sq (a u D r : ℤ) (β : ℚ) (n : ℕ) (hu : u ≠ 0)
    (hr : (r : ℚ) = D * ((a : ℚ) / u + β)) (c' : ℚ) :
    ((integralJacobi a u D r n).map (Int.castRingHom ℚ)).comp (C c' * X ^ 2) =
      C ((u : ℚ) ^ n * n.factorial) * (jacobiP ((a : ℚ) / u) β n).comp
        (1 + C (2 * D * c' / u) * X ^ 2) := by
  rw [integralJacobi_map a u D r β n hu hr, mul_comp, C_comp, comp_assoc]
  congr 2
  simp only [add_comp, one_comp, mul_comp, C_comp, X_comp]
  rw [← mul_assoc, ← C_mul]
  congr 3
  ring

/-- **The Kaneko–Zagier normalization (5.17)** (`D = 6`, `r = 2λ + 3μ`):
`K_n^{λ,μ}(X) = 3^n n! P_n^{(λ/3,μ/2)}(4X + 1)`. -/
theorem integralJacobi_kanekoZagier (l μ : ℤ) (n : ℕ) :
    (integralJacobi l 3 6 (2 * l + 3 * μ) n).map (Int.castRingHom ℚ) =
      C ((3 : ℚ) ^ n * n.factorial) * (jacobiP ((l : ℚ) / 3) ((μ : ℚ) / 2) n).comp
        (4 * X + 1) := by
  have h := integralJacobi_map l 3 6 (2 * l + 3 * μ) ((μ : ℚ) / 2) n (by norm_num)
    (by push_cast; ring)
  rw [h]
  congr 2
  rw [show (2 * ((6 : ℤ) : ℚ) / ((3 : ℤ) : ℚ)) = 4 by norm_num, C_ofNat]
  ring

/-- `∏_{k=j+1}^n f(k) = f(j+1) ∏_{k=j+2}^n f(k)` for `j < n`. -/
private lemma prod_Ioc_eq_mul_prod_Ioc_succ {M : Type*} [CommMonoid M] (f : ℕ → M) {j n : ℕ}
    (hjn : j < n) : ∏ k ∈ Ioc j n, f k = f (j + 1) * ∏ k ∈ Ioc (j + 1) n, f k := by
  have hmem : j + 1 ∈ Ioc j n := by simp; omega
  have herase : (Ioc j n).erase (j + 1) = Ioc (j + 1) n := by
    ext k; simp only [mem_erase, mem_Ioc]; omega
  rw [← mul_prod_erase _ f hmem, herase]

/-- The two-term coefficient recurrence of `K_n`:
`(j+1)(u(j+1)+a) e_{j+1} = (n-j)(D(n+j+1)+r) e_j`. -/
theorem integralJacobi_coeff_recurrence (a u D r : ℤ) (n j : ℕ) :
    ((j : ℤ) + 1) * (u * (j + 1) + a) * (integralJacobi a u D r n).coeff (j + 1) =
      ((n : ℤ) - j) * (D * (n + j + 1) + r) * (integralJacobi a u D r n).coeff j := by
  rw [coeff_integralJacobi, coeff_integralJacobi]
  rcases lt_trichotomy j n with hjn | hjn | hjn
  · have hj1 : j + 1 ≤ n := hjn
    simp only [hj1, hjn.le, ↓reduceIte, integralJacobiCoeff_eq]
    rw [prod_Ioc_eq_mul_prod_Ioc_succ _ hjn, prod_Icc_succ_top (by omega)]
    have hc := Nat.choose_succ_right_eq n j
    have hc' : ((n.choose (j + 1) : ℕ) : ℤ) * ((j : ℤ) + 1) = (n.choose j : ℤ) * ((n : ℤ) - j) := by
      have := congrArg (fun m : ℕ => (m : ℤ)) hc
      push_cast [Nat.cast_sub hjn.le] at this
      exact this
    push_cast
    linear_combination (u * (j + 1) + a) * (∏ k ∈ Ioc (j + 1) n, (u * (k : ℤ) + a)) *
      (∏ k ∈ Icc 1 j, (D * (n : ℤ) + r + D * k)) * (D * n + r + D * (j + 1)) * hc'
  · subst hjn; simp
  · have hj1 : ¬ j + 1 ≤ n := by omega
    have hj2 : ¬ j ≤ n := by omega
    simp only [hj1, hj2, ↓reduceIte, mul_zero]

/-- **The differential equation of `K_n`** over `ℤ`:
`X (D X + u) K'' + [(a + u) + (r + 2D) X] K' = n (D n + r + D) K`. This is the Jacobi
equation (5.6) after the substitution `x = 1 + (2D/u) X` (when `r = D(a/u + β)`), but it holds
for all integers `a, u, D, r`. -/
theorem integralJacobi_ode (a u D r : ℤ) (n : ℕ) :
    X * (C D * X + C u) * derivative (derivative (integralJacobi a u D r n)) +
      (C (a + u) + C (r + 2 * D) * X) * derivative (integralJacobi a u D r n) =
      C ((n : ℤ) * (D * n + r + D)) * integralJacobi a u D r n := by
  set K := integralJacobi a u D r n with hK
  have key : X * (C D * X + C u) * derivative (derivative K) +
      (C (a + u) + C (r + 2 * D) * X) * derivative K =
      C D * (X * derivative (X * derivative K)) - C D * (X * derivative K) +
        C u * (X * derivative (derivative K)) + C (a + u) * derivative K +
        C (r + 2 * D) * (X * derivative K) := by
    rw [derivative_mul, derivative_X]; ring
  rw [key]
  ext j
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul_derivative, coeff_derivative]
  have hr := integralJacobi_coeff_recurrence a u D r n j
  rw [← hK] at hr
  linear_combination hr

/-! ### Repeated roots of solutions of a second-order equation -/

section RepeatedRoots

variable {L : Type*} [Field L]

/-- `(X - z) (d/dX) (X - z)^m = m (X - z)^m`. -/
theorem X_sub_C_mul_derivative_X_sub_C_pow (z : L) (m : ℕ) :
    (X - C z) * derivative ((X - C z) ^ m) = C (m : L) * (X - C z) ^ m := by
  rw [derivative_X_sub_C_pow]
  cases m with
  | zero => simp
  | succ m => simp only [Nat.add_sub_cancel]; ring

/-- If `A K'' + B K' = c K` and the integers up to `deg K` are nonzero in `L`, then a root of
`K` of multiplicity at least two is a zero of `A`. Hence, if `K` does not vanish at the zeros
of `A`, every root of `K` is simple. -/
theorem rootMultiplicity_le_one_of_singular_ode {K A B : L[X]} {c : L} (hK : K ≠ 0)
    (hode : A * derivative (derivative K) + B * derivative K = C c * K)
    (hchar : ∀ m : ℕ, 1 ≤ m → m ≤ K.natDegree → (m : L) ≠ 0)
    (hsing : ∀ z, A.eval z = 0 → K.eval z ≠ 0) (z : L) : K.rootMultiplicity z ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨m, hm⟩ : ∃ m, K.rootMultiplicity z = m + 2 := ⟨K.rootMultiplicity z - 2, by omega⟩
  have hKg := pow_mul_divByMonic_rootMultiplicity_eq K z
  have hgz := eval_divByMonic_pow_rootMultiplicity_ne_zero z hK
  have hdeg : K.rootMultiplicity z ≤ K.natDegree := by
    have := natDegree_le_of_dvd ⟨_, hKg.symm⟩ hK
    simpa using this
  set g := K /ₘ (X - C z) ^ K.rootMultiplicity z
  rw [hm] at hKg hdeg
  set T := X - C z with hT
  have hd1 : derivative K = C ((m : L) + 2) * T ^ (m + 1) * g + T ^ (m + 2) * derivative g := by
    rw [← hKg, derivative_mul, hT, derivative_X_sub_C_pow, show m + 2 - 1 = m + 1 by omega]
    push_cast; ring
  have hd2 : derivative (derivative K) = C ((m : L) + 2) * (C ((m : L) + 1) * T ^ m * g +
      T ^ (m + 1) * derivative g) + C ((m : L) + 2) * T ^ (m + 1) * derivative g +
      T ^ (m + 2) * derivative (derivative g) := by
    rw [hd1]
    simp only [derivative_add, derivative_mul, derivative_C, hT, derivative_X_sub_C_pow,
      show m + 2 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega]
    push_cast; ring
  rw [hd2, hd1] at hode
  rw [← hKg] at hode
  have hQ : T ^ m * (A * (C ((m : L) + 2) * C ((m : L) + 1) * g +
      T * (C ((m : L) + 2) * derivative g + C ((m : L) + 2) * derivative g +
        T * derivative (derivative g))) + B * (T * (C ((m : L) + 2) * g + T * derivative g)) -
      C c * (T ^ 2 * g)) = 0 := by
    linear_combination hode
  have hTne : T ^ m ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero z)
  have hQ' := congrArg (eval z) ((mul_eq_zero.mp hQ).resolve_left hTne)
  simp only [hT, eval_sub, eval_add, eval_mul, eval_C, eval_X, sub_self, zero_mul, mul_zero,
    add_zero, eval_pow, eval_zero] at hQ'
  have h2 : ((m : L) + 2) ≠ 0 := by
    have := hchar (m + 2) (by omega) hdeg; push_cast at this; exact this
  have h1 : ((m : L) + 1) ≠ 0 := by
    have := hchar (m + 1) (by omega) (by omega); push_cast at this; exact this
  have hQ'' : A.eval z * (((m : L) + 2) * ((m : L) + 1) * g.eval z) = 0 := by
    linear_combination hQ'
  have hAz : A.eval z = 0 := by
    rcases mul_eq_zero.mp hQ'' with h | h
    · exact h
    · exact absurd h (mul_ne_zero (mul_ne_zero h2 h1) hgz)
  have hroot : K.IsRoot z := (rootMultiplicity_pos hK).mp (by omega)
  exact hsing z hAz hroot

/-- At a zero `z` of `A = (X - z) A₁`, a solution of `A K'' + B K' = c K` with `K(z) = 0` of
multiplicity `m + 1` forces `(m + 1) (A₁(z) m + B(z)) = 0`; so `K(z) ≠ 0` if these indicial
values are nonzero. -/
theorem eval_ne_zero_of_ode_of_singular {K A₁ B : L[X]} {c z : L} (hK : K ≠ 0)
    (hode : (X - C z) * A₁ * derivative (derivative K) + B * derivative K = C c * K)
    (hind : ∀ m : ℕ, m + 1 ≤ K.natDegree → ((m : L) + 1) * (A₁.eval z * m + B.eval z) ≠ 0) :
    K.eval z ≠ 0 := by
  intro hKz
  have hpos : 0 < K.rootMultiplicity z := (rootMultiplicity_pos hK).mpr hKz
  obtain ⟨m, hm⟩ : ∃ m, K.rootMultiplicity z = m + 1 := ⟨K.rootMultiplicity z - 1, by omega⟩
  have hKg := pow_mul_divByMonic_rootMultiplicity_eq K z
  have hgz := eval_divByMonic_pow_rootMultiplicity_ne_zero z hK
  have hdeg : K.rootMultiplicity z ≤ K.natDegree := by
    have := natDegree_le_of_dvd ⟨_, hKg.symm⟩ hK
    simpa using this
  set g := K /ₘ (X - C z) ^ K.rootMultiplicity z
  rw [hm] at hKg hdeg
  have hTd := X_sub_C_mul_derivative_X_sub_C_pow z m
  set T := X - C z with hT
  have hd1 : derivative K = C ((m : L) + 1) * T ^ m * g + T ^ (m + 1) * derivative g := by
    rw [← hKg, derivative_mul, hT, derivative_X_sub_C_pow, show m + 1 - 1 = m by omega]
    push_cast; ring
  have hd2 : derivative (derivative K) = C ((m : L) + 1) * (derivative (T ^ m) * g +
      T ^ m * derivative g) + C ((m : L) + 1) * T ^ m * derivative g +
      T ^ (m + 1) * derivative (derivative g) := by
    rw [hd1]
    simp only [derivative_add, derivative_mul, derivative_C, hT, derivative_X_sub_C_pow,
      show m + 1 - 1 = m by omega]
    push_cast; ring
  rw [hd2, hd1] at hode
  rw [← hKg] at hode
  have hQ : T ^ m * (A₁ * (C ((m : L) + 1) * C (m : L) * g +
      T * (C ((m : L) + 1) * derivative g + C ((m : L) + 1) * derivative g +
        T * derivative (derivative g))) + B * (C ((m : L) + 1) * g + T * derivative g) -
      C c * (T * g)) = 0 := by
    linear_combination hode - A₁ * C ((m : L) + 1) * g * hTd
  have hTne : T ^ m ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero z)
  have hQ' := congrArg (eval z) ((mul_eq_zero.mp hQ).resolve_left hTne)
  simp only [hT, eval_sub, eval_add, eval_mul, eval_C, eval_X, sub_self, zero_mul, mul_zero,
    add_zero, eval_zero] at hQ'
  have := hind m (by omega)
  apply this
  have hg : g.eval z ≠ 0 := hgz
  have : ((m : L) + 1) * (A₁.eval z * m + B.eval z) * g.eval z = 0 := by
    linear_combination hQ'
  exact (mul_eq_zero.mp this).resolve_right hg

end RepeatedRoots

/-! ### The hypotheses of Proposition 5.2 -/

/-- The index `k₀ = (p - r)/D - n` of Proposition 5.2. -/
def jacobiCycleIndex (p n : ℕ) (D r : ℤ) : ℤ := ((p : ℤ) - r) / D - n

theorem jacobiCycleIndex_eq (p n : ℕ) (D r : ℤ) :
    jacobiCycleIndex p n D r = ((p : ℤ) - r) / D - n := (rfl)

/-- **The hypotheses of Proposition 5.2**, for `α = a/u`, `β = b/v`
with `u, v > 0`, a positive integer `D` with `r = D(α + β)` (5.7), and an odd prime `p`:
(5.9) `p > n`, `p ∤ uvD`, `0 < |uk + a| < p` and `0 < |vk + b| < p` for `1 ≤ k ≤ n`;
(5.10) `0 < D(n+1) + r`, `2Dn + r < 2p`, `p ≡ r (mod D)`; and `1 ≤ k₀ = (p - r)/D - n ≤ n`. -/
structure JacobiCycleHypotheses (p n : ℕ) (a u b v D r : ℤ) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  u_pos : 0 < u
  v_pos : 0 < v
  D_pos : 0 < D
  r_eq : (r : ℚ) = D * ((a : ℚ) / u + (b : ℚ) / v)
  n_lt : n < p
  not_dvd : ¬ (p : ℤ) ∣ u * v * D
  small_u : ∀ k : ℕ, 1 ≤ k → k ≤ n → 0 < |u * k + a| ∧ |u * k + a| < p
  small_v : ∀ k : ℕ, 1 ≤ k → k ≤ n → 0 < |v * k + b| ∧ |v * k + b| < p
  large_pos : 0 < D * (n + 1) + r
  large_lt : 2 * D * n + r < 2 * p
  cong : (p : ℤ) ≡ r [ZMOD D]
  index_pos : 1 ≤ jacobiCycleIndex p n D r
  index_le : jacobiCycleIndex p n D r ≤ n

/-- The index `k₀` of Proposition 5.2 as a natural number. -/
def jacobiCycleIndexNat (p n : ℕ) (D r : ℤ) : ℕ := (jacobiCycleIndex p n D r).toNat

theorem jacobiCycleIndexNat_eq (p n : ℕ) (D r : ℤ) :
    jacobiCycleIndexNat p n D r = (jacobiCycleIndex p n D r).toNat := (rfl)

private lemma not_dvd_of_abs {p : ℕ} {x : ℤ} (h0 : 0 < |x|) (h1 : |x| < p) :
    ¬ (p : ℤ) ∣ x := by
  intro hd
  have := Int.eq_zero_of_abs_lt_dvd hd h1
  rw [this] at h0; simp at h0

namespace JacobiCycleHypotheses

variable {p n : ℕ} {a u b v D r : ℤ} (h : JacobiCycleHypotheses p n a u b v D r)
include h

theorem prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp h.prime

theorem cast_index : (jacobiCycleIndexNat p n D r : ℤ) = jacobiCycleIndex p n D r := by
  rw [jacobiCycleIndexNat_eq, Int.toNat_of_nonneg (by linarith [h.index_pos])]

theorem one_le_index : 1 ≤ jacobiCycleIndexNat p n D r := by
  have := h.cast_index; have := h.index_pos; omega

theorem index_le_n : jacobiCycleIndexNat p n D r ≤ n := by
  have := h.cast_index; have := h.index_le; omega

/-- `p - r = D (n + k₀)`. -/
theorem sub_eq : (p : ℤ) - r = D * (n + jacobiCycleIndexNat p n D r) := by
  rw [h.cast_index, jacobiCycleIndex_eq]
  have hd : D ∣ (p : ℤ) - r := by
    have := h.cong.dvd
    rw [← dvd_neg, neg_sub] at this; exact this
  have := Int.ediv_mul_cancel hd
  linear_combination -this

/-- `r u v = D (a v + b u)`. -/
theorem r_mul : r * u * v = D * (a * v + b * u) := by
  have hu : (u : ℚ) ≠ 0 := by exact_mod_cast h.u_pos.ne'
  have hv : (v : ℚ) ≠ 0 := by exact_mod_cast h.v_pos.ne'
  have := h.r_eq
  have : ((r * u * v : ℤ) : ℚ) = ((D * (a * v + b * u) : ℤ) : ℚ) := by
    push_cast; rw [this]; field_simp
  exact_mod_cast this

theorem not_dvd_u : ¬ (p : ℤ) ∣ u := fun hd => h.not_dvd (dvd_mul_of_dvd_left
  (dvd_mul_of_dvd_left hd _) _)

theorem not_dvd_v : ¬ (p : ℤ) ∣ v := fun hd => h.not_dvd (dvd_mul_of_dvd_left
  (dvd_mul_of_dvd_right hd _) _)

theorem not_dvd_D : ¬ (p : ℤ) ∣ D := fun hd => h.not_dvd (dvd_mul_of_dvd_right hd _)

theorem not_dvd_small_u {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) : ¬ (p : ℤ) ∣ u * k + a :=
  not_dvd_of_abs (h.small_u k hk1 hkn).1 (h.small_u k hk1 hkn).2

theorem not_dvd_small_v {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) : ¬ (p : ℤ) ∣ v * k + b :=
  not_dvd_of_abs (h.small_v k hk1 hkn).1 (h.small_v k hk1 hkn).2

theorem not_dvd_choose {j : ℕ} (hjn : j ≤ n) : ¬ (p : ℤ) ∣ (n.choose j : ℤ) := by
  rw [Int.natCast_dvd_natCast]
  intro hd
  have hfac : p ∣ n.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial hjn]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
  have := (Nat.Prime.dvd_factorial h.prime).mp hfac
  have := h.n_lt; omega

theorem large_bounds {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    0 < D * n + r + D * k ∧ D * n + r + D * k < 2 * p := by
  have hD := h.D_pos
  have h1 : D * 1 ≤ D * (k : ℤ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hk1) hD.le
  have h2 : D * (k : ℤ) ≤ D * n := mul_le_mul_of_nonneg_left (by exact_mod_cast hkn) hD.le
  constructor
  · nlinarith [h.large_pos]
  · nlinarith [h.large_lt]

/-- The factor `D n + r + D k` with `k = k₀` is `p`. -/
theorem large_index : D * n + r + D * jacobiCycleIndexNat p n D r = p := by
  linear_combination -h.sub_eq

/-- The factors `D n + r + D k`, `k ≠ k₀`, are units at `p`. -/
theorem not_dvd_large {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hk : k ≠ jacobiCycleIndexNat p n D r) :
    ¬ (p : ℤ) ∣ D * n + r + D * k := by
  rintro ⟨t, ht⟩
  obtain ⟨h0, h2⟩ := h.large_bounds hk1 hkn
  have hp : (0 : ℤ) < p := by exact_mod_cast h.prime.pos
  have ht1 : t = 1 := by
    rw [ht] at h0 h2
    have : 0 < t := pos_of_mul_pos_right h0 hp.le
    have : t < 2 := by nlinarith
    omega
  rw [ht1, mul_one] at ht
  have hk' : D * (k : ℤ) = D * jacobiCycleIndexNat p n D r := by linarith [h.large_index]
  have := mul_left_cancel₀ h.D_pos.ne' hk'
  exact hk (by exact_mod_cast this)

/-- For `j < k₀`, the coefficient `e_j` of `K_n` is a unit at `p`. -/
theorem not_dvd_coeff_of_lt {j : ℕ} (hj : j < jacobiCycleIndexNat p n D r) :
    ¬ (p : ℤ) ∣ integralJacobiCoeff a u D r n j := by
  have hjn : j ≤ n := by have := h.index_le_n; omega
  have hp := h.prime_int
  rw [integralJacobiCoeff_eq]
  intro hd
  rcases hp.dvd_or_dvd hd with hd | hd
  · rcases hp.dvd_or_dvd hd with hd | hd
    · exact h.not_dvd_choose hjn hd
    · obtain ⟨k, hk, hdk⟩ := (hp.dvd_finsetProd_iff _).mp hd
      rw [mem_Ioc] at hk
      exact h.not_dvd_small_u (by omega) hk.2 hdk
  · obtain ⟨k, hk, hdk⟩ := (hp.dvd_finsetProd_iff _).mp hd
    rw [mem_Icc] at hk
    exact h.not_dvd_large hk.1 (by omega) (by omega) hdk

/-- For `k₀ ≤ j ≤ n`, the coefficient `e_j` of `K_n` has `p`-adic valuation exactly one. -/
theorem coeff_eq_mul_of_le {j : ℕ} (hj : jacobiCycleIndexNat p n D r ≤ j) (hjn : j ≤ n) :
    ∃ m : ℤ, integralJacobiCoeff a u D r n j = p * m ∧ ¬ (p : ℤ) ∣ m := by
  classical
  have hp := h.prime_int
  set k₀ := jacobiCycleIndexNat p n D r
  have hmem : k₀ ∈ Icc 1 j := by rw [mem_Icc]; exact ⟨h.one_le_index, hj⟩
  refine ⟨(n.choose j : ℤ) * (∏ k ∈ Ioc j n, (u * k + a)) *
    ∏ k ∈ (Icc 1 j).erase k₀, (D * n + r + D * k), ?_, ?_⟩
  · rw [integralJacobiCoeff_eq, ← mul_prod_erase _ _ hmem, h.large_index]; ring
  · intro hd
    rcases hp.dvd_or_dvd hd with hd | hd
    · rcases hp.dvd_or_dvd hd with hd | hd
      · exact h.not_dvd_choose hjn hd
      · obtain ⟨k, hk, hdk⟩ := (hp.dvd_finsetProd_iff _).mp hd
        rw [mem_Ioc] at hk
        exact h.not_dvd_small_u (by omega) hk.2 hdk
    · obtain ⟨k, hk, hdk⟩ := (hp.dvd_finsetProd_iff _).mp hd
      rw [mem_erase, mem_Icc] at hk
      exact h.not_dvd_large hk.2.1 (by omega) hk.1 hdk

theorem dvd_coeff_of_le {j : ℕ} (hj : jacobiCycleIndexNat p n D r ≤ j) (hjn : j ≤ n) :
    (p : ℤ) ∣ integralJacobiCoeff a u D r n j ∧
      ¬ (p : ℤ) ^ 2 ∣ integralJacobiCoeff a u D r n j := by
  obtain ⟨m, hm, hnd⟩ := h.coeff_eq_mul_of_le hj hjn
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast h.prime.ne_zero
  refine ⟨hm ▸ dvd_mul_right _ _, ?_⟩
  rw [hm, pow_two]
  exact fun hd => hnd ((mul_dvd_mul_iff_left hp0).mp hd)

/-- The coefficient valuations of `K_n` in the proof of Proposition 5.2: zero for `j < k₀`. -/
theorem not_dvd_coeff_integralJacobi {j : ℕ} (hj : j < jacobiCycleIndexNat p n D r) :
    ¬ (p : ℤ) ∣ (integralJacobi a u D r n).coeff j := by
  have hjn : j ≤ n := by have := h.index_le_n; omega
  simp only [coeff_integralJacobi, hjn, ↓reduceIte]
  exact h.not_dvd_coeff_of_lt hj

/-- The coefficient valuations of `K_n` in the proof of Proposition 5.2: one for
`k₀ ≤ j ≤ n`. -/
theorem dvd_coeff_integralJacobi {j : ℕ} (hj : jacobiCycleIndexNat p n D r ≤ j)
    (hjn : j ≤ n) : (p : ℤ) ∣ (integralJacobi a u D r n).coeff j ∧
      ¬ (p : ℤ) ^ 2 ∣ (integralJacobi a u D r n).coeff j := by
  simp only [coeff_integralJacobi, hjn, ↓reduceIte]
  exact h.dvd_coeff_of_le hj hjn

theorem natDegree_integralJacobi : (integralJacobi a u D r n).natDegree = n := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have hN' : ¬ N ≤ n := by exact_mod_cast hN.not_ge
    simp only [coeff_integralJacobi, hN', ↓reduceIte]
  · intro h0
    exact (h.dvd_coeff_integralJacobi h.index_le_n le_rfl).2 (h0 ▸ dvd_zero _)

theorem leadingCoeff_integralJacobi :
    (integralJacobi a u D r n).leadingCoeff = integralJacobiCoeff a u D r n n := by
  rw [leadingCoeff, h.natDegree_integralJacobi, coeff_integralJacobi]
  simp

/-- The reduction of `K_n` modulo `p` (in any field of characteristic `p`) has degree
`k₀ - 1`. -/
theorem natDegree_map_integralJacobi (F : Type*) [Field F] [CharP F p] :
    ((integralJacobi a u D r n).map (Int.castRingHom F)).natDegree =
      jacobiCycleIndexNat p n D r - 1 := by
  have hk := h.one_le_index
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have hN' : jacobiCycleIndexNat p n D r ≤ N := by
      have : (jacobiCycleIndexNat p n D r - 1 : ℕ) < N := by exact_mod_cast hN
      omega
    rw [coeff_map, eq_intCast, CharP.intCast_eq_zero_iff F p]
    by_cases hNn : N ≤ n
    · exact (h.dvd_coeff_integralJacobi hN' hNn).1
    · simp only [coeff_integralJacobi, hNn, ↓reduceIte, dvd_zero]
  · rw [coeff_map, eq_intCast, Ne, CharP.intCast_eq_zero_iff F p]
    exact h.not_dvd_coeff_integralJacobi (by omega)

/-- **Squarefree reduction.** Under the hypotheses of Proposition 5.2 the reduction of `K_n`
modulo `p` is squarefree. The proof reduces the differential equation of `K_n` modulo `p`:
the degree of the reduction is `< p`, and at the two singular points `0` and `-u/D` the
indicial values `u(m+1) + a` and `-(Du)(v(m+1) + b)/(Dv)` are units. -/
theorem rootMultiplicity_map_integralJacobi_le_one (L : Type*) [Field L] [CharP L p] (z : L) :
    ((integralJacobi a u D r n).map (Int.castRingHom L)).rootMultiplicity z ≤ 1 ∧
      (integralJacobi a u D r n).map (Int.castRingHom L) ≠ 0 := by
  set f := integralJacobi a u D r n
  set fL := f.map (Int.castRingHom L) with hfL
  have hcast : ∀ x : ℤ, (x : L) = 0 ↔ (p : ℤ) ∣ x := fun x => CharP.intCast_eq_zero_iff L p x
  have hdegL : fL.natDegree = jacobiCycleIndexNat p n D r - 1 :=
    h.natDegree_map_integralJacobi L
  have hk := h.index_le_n
  have hnp := h.n_lt
  have hfL0 : fL ≠ 0 := by
    intro h0
    have := congrArg (fun q => q.coeff 0) h0
    simp only [hfL, coeff_map, eq_intCast, coeff_zero] at this
    exact h.not_dvd_coeff_integralJacobi h.one_le_index ((hcast _).mp this)
  -- the differential equation over `L`
  have hode : X * (C (D : L) * X + C (u : L)) * derivative (derivative fL) +
      (C ((a : L) + u) + C ((r : L) + 2 * D) * X) * derivative fL =
      C ((n : L) * (D * n + r + D)) * fL := by
    have := congrArg (Polynomial.map (Int.castRingHom L)) (integralJacobi_ode a u D r n)
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C,
      ← derivative_map] at this
    rw [← hfL] at this
    simp only [eq_intCast, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] at this
    exact this
  have hnat : ∀ m : ℕ, 1 ≤ m → m ≤ fL.natDegree → (m : L) ≠ 0 := by
    intro m hm1 hm2
    rw [Ne, CharP.cast_eq_zero_iff L p]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hu : (u : L) ≠ 0 := fun h0 => h.not_dvd_u ((hcast u).mp h0)
  have hD : (D : L) ≠ 0 := fun h0 => h.not_dvd_D ((hcast D).mp h0)
  have hv : (v : L) ≠ 0 := fun h0 => h.not_dvd_v ((hcast v).mp h0)
  have hsing : ∀ z : L, (X * (C (D : L) * X + C (u : L))).eval z = 0 → fL.eval z ≠ 0 := by
    intro z hz
    simp only [eval_mul, eval_X, eval_add, eval_C] at hz
    rcases mul_eq_zero.mp hz with hz0 | hz0
    · -- the singular point `0`
      subst hz0
      refine eval_ne_zero_of_ode_of_singular (A₁ := C (D : L) * X + C (u : L))
        (B := C ((a : L) + u) + C ((r : L) + 2 * D) * X) (c := (n : L) * (D * n + r + D)) hfL0 ?_ ?_
      · rw [map_zero, sub_zero]; exact hode
      · intro m hm
        simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, zero_add]
        have hm1 := hnat (m + 1) (by omega) hm
        push_cast at hm1
        refine mul_ne_zero hm1 ?_
        have hne : ((u * ((m + 1 : ℕ) : ℤ) + a : ℤ) : L) ≠ 0 := fun h0 =>
          h.not_dvd_small_u (k := m + 1) (by omega) (by omega) ((hcast _).mp h0)
        push_cast at hne
        intro h0; apply hne; linear_combination h0
    · -- the singular point `-u/D`
      have hA : X * (C (D : L) * X + C (u : L)) = (X - C z) * (C (D : L) * X) := by
        have : (u : L) = -(D * z) := by linear_combination hz0
        rw [this, C_neg, C_mul]; ring
      refine eval_ne_zero_of_ode_of_singular (A₁ := C (D : L) * X)
        (B := C ((a : L) + u) + C ((r : L) + 2 * D) * X) (c := (n : L) * (D * n + r + D)) hfL0 ?_ ?_
      · rw [← hA]; exact hode
      · intro m hm
        simp only [eval_add, eval_mul, eval_C, eval_X]
        have hm1 := hnat (m + 1) (by omega) hm
        push_cast at hm1
        refine mul_ne_zero hm1 ?_
        have hne : ((D * u * (v * ((m + 1 : ℕ) : ℤ) + b) : ℤ) : L) ≠ 0 := by
          intro h0
          rcases h.prime_int.dvd_or_dvd ((hcast _).mp h0) with hd | hd
          · rcases h.prime_int.dvd_or_dvd hd with hd | hd
            · exact h.not_dvd_D hd
            · exact h.not_dvd_u hd
          · exact h.not_dvd_small_v (k := m + 1) (by omega) (by omega) hd
        have hruv : ((r * u * v : ℤ) : L) = ((D * (a * v + b * u) : ℤ) : L) := by
          rw [h.r_mul]
        push_cast at hne hruv
        intro h0
        apply hne
        have hz' : (D : L) * z = -u := by linear_combination hz0
        linear_combination (-(D : L) * v) * h0 +
          ((D : L) * v * (m : L) + v * (r + 2 * D)) * hz' - hruv
  exact ⟨rootMultiplicity_le_one_of_singular_ode hfL0 hode hnat hsing z, hfL0⟩

/-- **Squarefree reduction.** Under the hypotheses of Proposition 5.2 the reduction of `K_n`
modulo `p` is squarefree. The proof reduces the differential equation of `K_n` modulo `p`:
the degree of the reduction is `< p`, and at the two singular points `0` and `-u/D` the
indicial values `u(m+1) + a` and `-(Du)(v(m+1) + b)/(Dv)` are units. -/
theorem squarefree_map_integralJacobi :
    Squarefree ((integralJacobi a u D r n).map (Int.castRingHom (ZMod p))) := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  set f := integralJacobi a u D r n
  set fL := f.map (Int.castRingHom (AlgebraicClosure (ZMod p))) with hfL
  have hfL0 : fL ≠ 0 := (h.rootMultiplicity_map_integralJacobi_le_one _ 0).2
  have hsep : fL.Separable := by
    rw [← nodup_roots_iff_of_splits hfL0 (IsAlgClosed.splits _),
      Multiset.nodup_iff_count_le_one]
    intro z
    rw [count_roots]
    exact (h.rootMultiplicity_map_integralJacobi_le_one _ z).1
  have hfL' : fL = (f.map (Int.castRingHom (ZMod p))).map
      (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) := by
    rw [hfL, Polynomial.map_map]
    congr 1
  rw [hfL', separable_map] at hsep
  exact hsep.squarefree

/-- **The hypotheses of Lemma 5.1 for `K_n`.** Under the hypotheses of Proposition 5.2, with
`k₀ = (p - r)/D - n` and `d = n - k₀ + 1`: `1 ≤ d ≤ n < p`, the constant coefficient of `K_n`
is a unit at `p`, its leading coefficient has valuation exactly one, its reduction modulo `p`
has degree `deg K_n - d = k₀ - 1`, and this reduction is squarefree. -/
theorem localCycle_hypotheses :
    1 ≤ n + 1 - jacobiCycleIndexNat p n D r ∧ n + 1 - jacobiCycleIndexNat p n D r ≤ n ∧
    n + 1 - jacobiCycleIndexNat p n D r < p ∧
    (integralJacobi a u D r n).natDegree = n ∧
    ¬ (p : ℤ) ∣ (integralJacobi a u D r n).coeff 0 ∧
    (p : ℤ) ∣ (integralJacobi a u D r n).leadingCoeff ∧
    ¬ (p : ℤ) ^ 2 ∣ (integralJacobi a u D r n).leadingCoeff ∧
    ((integralJacobi a u D r n).map (Int.castRingHom (ZMod p))).natDegree +
      (n + 1 - jacobiCycleIndexNat p n D r) = (integralJacobi a u D r n).natDegree ∧
    Squarefree ((integralJacobi a u D r n).map (Int.castRingHom (ZMod p))) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have h1 := h.one_le_index
  have h2 := h.index_le_n
  have h3 := h.n_lt
  have hlc := h.dvd_coeff_integralJacobi h2 le_rfl
  have hlc' : (integralJacobi a u D r n).leadingCoeff = (integralJacobi a u D r n).coeff n := by
    rw [leadingCoeff, h.natDegree_integralJacobi]
  refine ⟨by omega, by omega, by omega, h.natDegree_integralJacobi,
    h.not_dvd_coeff_integralJacobi (by omega), ?_, ?_, ?_, h.squarefree_map_integralJacobi⟩
  · rw [hlc']; exact hlc.1
  · rw [hlc']; exact hlc.2
  · rw [h.natDegree_map_integralJacobi (ZMod p), h.natDegree_integralJacobi]; omega

end JacobiCycleHypotheses

end ArithmeticOfJacobiPolynomials
