/- Assembled by AxiomProver. -/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic.LinearCombination

/-!
# Harmonic polynomials in three variables

The Laplacian of a polynomial is the sum of its second partial derivatives,
`Δ p = ∑ᵢ ∂ᵢ (∂ᵢ p)` (`polyLaplacian`, defined via `MvPolynomial.pderiv`).

On `ℂ[x, y, z]` we write `w = x + i y` (`xPlusIY`) and `ρ² = x² + y² + z²` (`normSqPoly`) and
compute the Laplacian of the monomials `w^r z^a ρ^{2k}`:
`Δ (w^r z^a ρ^{2k}) = a(a-1) w^r z^{a-2} ρ^{2k} + k(4k + 2 + 4a + 4r) w^r z^a ρ^{2k-2}`.
Consequently, for coefficients `c` satisfying the two-term recurrence of the associated
Legendre equation `(1-x²) y'' - 2(r+1) x y' + n(n+2r+1) y = 0`, the polynomial
`w^r ∑_{k ≤ n/2} c_{n-2k} z^{n-2k} ρ^{2k}` (`zonalSum`) is harmonic. It is homogeneous of
degree `r + n`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open MvPolynomial Finset

/-- The Laplacian `Δ p = ∑ᵢ ∂ᵢ² p` of a polynomial: the sum of its second partial
derivatives. -/
noncomputable def polyLaplacian {σ R : Type*} [Fintype σ] [CommSemiring R]
    (p : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ i, pderiv i (pderiv i p)

theorem polyLaplacian_eq {σ R : Type*} [Fintype σ] [CommSemiring R] (p : MvPolynomial σ R) :
    polyLaplacian p = ∑ i, pderiv i (pderiv i p) := (rfl)

theorem polyLaplacian_add {σ R : Type*} [Fintype σ] [CommSemiring R] (p q : MvPolynomial σ R) :
    polyLaplacian (p + q) = polyLaplacian p + polyLaplacian q := by
  simp only [polyLaplacian, map_add, sum_add_distrib]

theorem polyLaplacian_sum {σ R ι : Type*} [Fintype σ] [CommSemiring R] (s : Finset ι)
    (f : ι → MvPolynomial σ R) :
    polyLaplacian (∑ j ∈ s, f j) = ∑ j ∈ s, polyLaplacian (f j) := by
  simp only [polyLaplacian, map_sum]
  exact Finset.sum_comm

theorem polyLaplacian_C_mul {σ R : Type*} [Fintype σ] [CommSemiring R] (a : R)
    (p : MvPolynomial σ R) : polyLaplacian (C a * p) = C a * polyLaplacian p := by
  simp only [polyLaplacian, pderiv_C_mul, mul_sum]

/-- In three variables, `Δ = ∂₀² + ∂₁² + ∂₂²`. -/
theorem polyLaplacian_fin_three {R : Type*} [CommSemiring R] (p : MvPolynomial (Fin 3) R) :
    polyLaplacian p = pderiv 0 (pderiv 0 p) + pderiv 1 (pderiv 1 p) + pderiv 2 (pderiv 2 p) := by
  rw [polyLaplacian, Fin.sum_univ_three]

theorem pderiv_two {σ R : Type*} [CommSemiring R] (i : σ) :
    pderiv i (2 : MvPolynomial σ R) = 0 := by
  simpa using Derivation.map_natCast (D := pderiv i) 2

/-- `n p^{n-1} p = n p^n` (both sides vanish for `n = 0`). -/
theorem natCast_mul_pow_sub_one_mul {R : Type*} [CommSemiring R] (p : R) (n : ℕ) :
    (n : R) * (p ^ (n - 1) * p) = n * p ^ n := by
  cases n with
  | zero => simp
  | succ n => rw [Nat.add_sub_cancel, ← pow_succ]

/-- `w = x + i y`. -/
noncomputable def xPlusIY : MvPolynomial (Fin 3) ℂ := X 0 + C Complex.I * X 1

theorem xPlusIY_eq : xPlusIY = X 0 + C Complex.I * X 1 := (rfl)

/-- `ρ² = x² + y² + z²`. -/
noncomputable def normSqPoly : MvPolynomial (Fin 3) ℂ := X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2

theorem normSqPoly_eq : normSqPoly = X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2 := (rfl)

private theorem pd00 : pderiv 0 (X 0 : MvPolynomial (Fin 3) ℂ) = 1 := pderiv_X_self 0
private theorem pd11 : pderiv 1 (X 1 : MvPolynomial (Fin 3) ℂ) = 1 := pderiv_X_self 1
private theorem pd22 : pderiv 2 (X 2 : MvPolynomial (Fin 3) ℂ) = 1 := pderiv_X_self 2
private theorem pd01 : pderiv 0 (X 1 : MvPolynomial (Fin 3) ℂ) = 0 := pderiv_X_of_ne (by decide)
private theorem pd02 : pderiv 0 (X 2 : MvPolynomial (Fin 3) ℂ) = 0 := pderiv_X_of_ne (by decide)
private theorem pd10 : pderiv 1 (X 0 : MvPolynomial (Fin 3) ℂ) = 0 := pderiv_X_of_ne (by decide)
private theorem pd12 : pderiv 1 (X 2 : MvPolynomial (Fin 3) ℂ) = 0 := pderiv_X_of_ne (by decide)
private theorem pd20 : pderiv 2 (X 0 : MvPolynomial (Fin 3) ℂ) = 0 := pderiv_X_of_ne (by decide)
private theorem pd21 : pderiv 2 (X 1 : MvPolynomial (Fin 3) ℂ) = 0 := pderiv_X_of_ne (by decide)

theorem pderiv_zero_xPlusIY : pderiv 0 xPlusIY = 1 := by
  rw [xPlusIY, map_add, pderiv_C_mul, pd00, pd01, mul_zero, add_zero]

theorem pderiv_one_xPlusIY : pderiv 1 xPlusIY = C Complex.I := by
  rw [xPlusIY, map_add, pderiv_C_mul, pd10, pd11, mul_one, zero_add]

theorem pderiv_two_xPlusIY : pderiv 2 xPlusIY = 0 := by
  rw [xPlusIY, map_add, pderiv_C_mul, pd20, pd21, mul_zero, add_zero]

theorem pderiv_zero_normSqPoly : pderiv 0 normSqPoly = 2 * X 0 := by
  rw [normSqPoly, map_add, map_add, pderiv_pow, pderiv_pow, pderiv_pow, pd00, pd01, pd02]
  norm_num

theorem pderiv_one_normSqPoly : pderiv 1 normSqPoly = 2 * X 1 := by
  rw [normSqPoly, map_add, map_add, pderiv_pow, pderiv_pow, pderiv_pow, pd10, pd11, pd12]
  norm_num

theorem pderiv_two_normSqPoly : pderiv 2 normSqPoly = 2 * X 2 := by
  rw [normSqPoly, map_add, map_add, pderiv_pow, pderiv_pow, pderiv_pow, pd20, pd21, pd22]
  norm_num

/-- **Laplacian of the monomials `w^r z^a ρ^{2k}`.**
`Δ (w^r z^a ρ^{2k}) = a(a-1) w^r z^{a-2} ρ^{2k} + (4k(k-1) + 6k + 4ak + 4rk) w^r z^a ρ^{2k-2}`
(natural-number subtraction; the corresponding coefficients vanish when it truncates). -/
theorem polyLaplacian_monomial (r a k : ℕ) :
    polyLaplacian (xPlusIY ^ r * (X 2 ^ a * normSqPoly ^ k)) =
      xPlusIY ^ r * ((a : MvPolynomial (Fin 3) ℂ) * ((a - 1 : ℕ) : MvPolynomial (Fin 3) ℂ) *
          (X 2 ^ (a - 1 - 1) * normSqPoly ^ k) +
        (4 * (k : MvPolynomial (Fin 3) ℂ) * ((k - 1 : ℕ) : MvPolynomial (Fin 3) ℂ) +
          6 * (k : MvPolynomial (Fin 3) ℂ) +
          4 * (a : MvPolynomial (Fin 3) ℂ) * (k : MvPolynomial (Fin 3) ℂ) +
          4 * (r : MvPolynomial (Fin 3) ℂ) * (k : MvPolynomial (Fin 3) ℂ)) *
          (X 2 ^ a * normSqPoly ^ (k - 1))) := by
  have hI : C Complex.I * C Complex.I = (-1 : MvPolynomial (Fin 3) ℂ) := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  have hw : xPlusIY = X 0 + C Complex.I * X 1 := rfl
  have hS : X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2 = normSqPoly := rfl
  have Lw := natCast_mul_pow_sub_one_mul xPlusIY r
  have Lz := natCast_mul_pow_sub_one_mul (X 2 : MvPolynomial (Fin 3) ℂ) a
  have LS := natCast_mul_pow_sub_one_mul normSqPoly (k - 1)
  rw [polyLaplacian_fin_three]
  simp only [map_add, pderiv_mul, pderiv_pow, Derivation.map_natCast, pderiv_two, pderiv_C,
    pd00, pd02, pd11, pd12, pd22, pderiv_zero_xPlusIY, pderiv_one_xPlusIY, pderiv_two_xPlusIY,
    pderiv_zero_normSqPoly, pderiv_one_normSqPoly, pderiv_two_normSqPoly, mul_zero, zero_mul,
    add_zero, zero_add, mul_one]
  linear_combination
    ((r : MvPolynomial (Fin 3) ℂ) * ((r - 1 : ℕ) : MvPolynomial (Fin 3) ℂ) *
        xPlusIY ^ (r - 1 - 1) * X 2 ^ a * normSqPoly ^ k) * hI -
      (4 * (k : MvPolynomial (Fin 3) ℂ) * X 2 ^ a * normSqPoly ^ (k - 1) * r *
        xPlusIY ^ (r - 1)) * hw +
      (4 * (k : MvPolynomial (Fin 3) ℂ) * X 2 ^ a * normSqPoly ^ (k - 1)) * Lw +
      (4 * (k : MvPolynomial (Fin 3) ℂ) * xPlusIY ^ r * normSqPoly ^ (k - 1)) * Lz +
      (4 * (k : MvPolynomial (Fin 3) ℂ) * ((k - 1 : ℕ) : MvPolynomial (Fin 3) ℂ) *
        xPlusIY ^ r * X 2 ^ a * normSqPoly ^ (k - 1 - 1)) * hS +
      (4 * (k : MvPolynomial (Fin 3) ℂ) * xPlusIY ^ r * X 2 ^ a) * LS

/-- The monomial formula with a constant coefficient, split into its two parts. -/
theorem polyLaplacian_C_mul_monomial (r a k : ℕ) (b : ℂ) :
    polyLaplacian (xPlusIY ^ r * (C b * (X 2 ^ a * normSqPoly ^ k))) =
      C b * ((a : MvPolynomial (Fin 3) ℂ) * ((a - 1 : ℕ) : MvPolynomial (Fin 3) ℂ)) *
          (xPlusIY ^ r * (X 2 ^ (a - 1 - 1) * normSqPoly ^ k)) +
        C b * (4 * (k : MvPolynomial (Fin 3) ℂ) * ((k - 1 : ℕ) : MvPolynomial (Fin 3) ℂ) +
          6 * (k : MvPolynomial (Fin 3) ℂ) +
          4 * (a : MvPolynomial (Fin 3) ℂ) * (k : MvPolynomial (Fin 3) ℂ) +
          4 * (r : MvPolynomial (Fin 3) ℂ) * (k : MvPolynomial (Fin 3) ℂ)) *
          (xPlusIY ^ r * (X 2 ^ a * normSqPoly ^ (k - 1))) := by
  rw [mul_left_comm (xPlusIY ^ r) (C b), polyLaplacian_C_mul, polyLaplacian_monomial]
  ring

/-- A shifted telescoping sum: `∑_{k ≤ m} (A k + B k) = 0` if `A m = 0`, `B 0 = 0` and
`A k + B (k+1) = 0` for `k < m`. -/
theorem sum_range_add_eq_zero_of_shift {M : Type*} [AddCommMonoid M] (m : ℕ) (A B : ℕ → M)
    (hA : A m = 0) (hB : B 0 = 0) (h : ∀ k < m, A k + B (k + 1) = 0) :
    ∑ k ∈ range (m + 1), (A k + B k) = 0 := by
  rw [sum_add_distrib, sum_range_succ, sum_range_succ' B, hA, hB, add_zero, add_zero,
    ← sum_add_distrib]
  exact sum_eq_zero fun k hk => h k (mem_range.mp hk)

/-- The polynomial `∑_{k ≤ n/2} c_{n-2k} z^{n-2k} ρ^{2k}`. -/
noncomputable def zonalSum (n : ℕ) (c : ℕ → ℂ) : MvPolynomial (Fin 3) ℂ :=
  ∑ k ∈ range (n / 2 + 1), C (c (n - 2 * k)) * (X 2 ^ (n - 2 * k) * normSqPoly ^ k)

theorem zonalSum_eq (n : ℕ) (c : ℕ → ℂ) : zonalSum n c =
    ∑ k ∈ range (n / 2 + 1), C (c (n - 2 * k)) * (X 2 ^ (n - 2 * k) * normSqPoly ^ k) := (rfl)

/-- **Harmonicity.** If the coefficients `c` satisfy the recurrence of the associated Legendre
equation `(1-x²) y'' - 2(r+1) x y' + n(n+2r+1) y = 0`, namely
`(j+2)(j+1) c_{j+2} = (j-n)(j+n+2r+1) c_j`, then `w^r ∑_{k ≤ n/2} c_{n-2k} z^{n-2k} ρ^{2k}`
is harmonic. -/
theorem polyLaplacian_xPlusIY_pow_mul_zonalSum (n r : ℕ) (c : ℕ → ℂ)
    (hc : ∀ j : ℕ, ((j : ℂ) + 2) * ((j : ℂ) + 1) * c (j + 2) =
      ((j : ℂ) - n) * ((j : ℂ) + n + 2 * r + 1) * c j) :
    polyLaplacian (xPlusIY ^ r * zonalSum n c) = 0 := by
  rw [zonalSum, mul_sum, polyLaplacian_sum]
  simp only [polyLaplacian_C_mul_monomial]
  refine sum_range_add_eq_zero_of_shift _ _ _ ?_ ?_ ?_
  · have hn : (n - 2 * (n / 2)) * (n - 2 * (n / 2) - 1) = 0 := Nat.mul_eq_zero.mpr (by omega)
    have h0 : ((n - 2 * (n / 2) : ℕ) : MvPolynomial (Fin 3) ℂ) *
        ((n - 2 * (n / 2) - 1 : ℕ) : MvPolynomial (Fin 3) ℂ) = 0 := by
      rw [← Nat.cast_mul, hn, Nat.cast_zero]
    rw [h0, mul_zero, zero_mul]
  · simp
  · intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 * k + 2 := ⟨n - 2 * k - 2, by omega⟩
    rw [show j + 2 * k + 2 - 2 * k - 1 - 1 = j by omega,
      show j + 2 * k + 2 - 2 * k - 1 = j + 1 by omega,
      show j + 2 * k + 2 - 2 * k = j + 2 by omega,
      show j + 2 * k + 2 - 2 * (k + 1) = j by omega, show k + 1 - 1 = k by omega]
    have h := congrArg (C (σ := Fin 3)) (hc j)
    simp only [map_mul, map_add, map_sub, map_natCast, map_ofNat, map_one] at h
    push_cast at h ⊢
    linear_combination (xPlusIY ^ r * (X 2 ^ j * normSqPoly ^ k)) * h

theorem isHomogeneous_xPlusIY : xPlusIY.IsHomogeneous 1 :=
  (isHomogeneous_X (R := ℂ) (0 : Fin 3)).add ((isHomogeneous_X (R := ℂ) (1 : Fin 3)).C_mul _)

theorem isHomogeneous_normSqPoly : normSqPoly.IsHomogeneous 2 :=
  (((isHomogeneous_X (R := ℂ) (0 : Fin 3)).pow 2).add
    ((isHomogeneous_X (R := ℂ) (1 : Fin 3)).pow 2)).add
    ((isHomogeneous_X (R := ℂ) (2 : Fin 3)).pow 2)

theorem isHomogeneous_zonalSum (n : ℕ) (c : ℕ → ℂ) : (zonalSum n c).IsHomogeneous n := by
  rw [zonalSum]
  refine IsHomogeneous.sum _ _ _ fun k hk => ?_
  have hk' : 2 * k ≤ n := by have := mem_range.mp hk; omega
  have h := (((isHomogeneous_X (R := ℂ) (2 : Fin 3)).pow (n - 2 * k)).mul
    (isHomogeneous_normSqPoly.pow k)).C_mul (c (n - 2 * k))
  rwa [show 1 * (n - 2 * k) + 2 * k = n by omega] at h

/-- `w^r ∑_{k ≤ n/2} c_{n-2k} z^{n-2k} ρ^{2k}` is homogeneous of degree `n + r`. -/
theorem isHomogeneous_xPlusIY_pow_mul_zonalSum (n r : ℕ) (c : ℕ → ℂ) :
    (xPlusIY ^ r * zonalSum n c).IsHomogeneous (n + r) := by
  have h := (isHomogeneous_xPlusIY.pow r).mul (isHomogeneous_zonalSum n c)
  rwa [show 1 * r + n = n + r by ring] at h

theorem eval_xPlusIY (v : Fin 3 → ℂ) : eval v xPlusIY = v 0 + Complex.I * v 1 := by
  simp only [xPlusIY, map_add, map_mul, eval_C, eval_X]

theorem eval_normSqPoly (v : Fin 3 → ℂ) : eval v normSqPoly = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  simp only [normSqPoly, map_add, map_pow, eval_X]

theorem eval_zonalSum (n : ℕ) (c : ℕ → ℂ) (v : Fin 3 → ℂ) :
    eval v (zonalSum n c) = ∑ k ∈ range (n / 2 + 1),
      c (n - 2 * k) * (v 2 ^ (n - 2 * k) * eval v normSqPoly ^ k) := by
  simp only [zonalSum, map_sum, map_mul, map_pow, eval_C, eval_X]

/-- At a point of the isotropic cone `x² + y² + z² = 0` only the top term survives. -/
theorem eval_zonalSum_of_eval_normSqPoly_eq_zero (n : ℕ) (c : ℕ → ℂ) (v : Fin 3 → ℂ)
    (hv : eval v normSqPoly = 0) : eval v (zonalSum n c) = c n * v 2 ^ n := by
  rw [eval_zonalSum, sum_range_succ', sum_eq_zero]
  · simp
  · intro k _
    rw [hv, zero_pow (Nat.succ_ne_zero k), mul_zero, mul_zero]

end ArithmeticOfJacobiPolynomials
