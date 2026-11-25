/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Remarks.HarmonicPolynomials
public import ArithmeticOfJacobiPolynomials.Remarks.SphericalModes
public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricCoefficients
public import ArithmeticOfJacobiPolynomials.Jacobi.DifferentialEquation
import Mathlib.Tactic.LinearCombination

/-!
# The spherical modes are restrictions of harmonic homogeneous polynomials
(§1.5)

The manuscript identifies the modes of degree `ℓ` and order `0 ≤ r ≤ ℓ` with
`ρ^ℓ e^{irφ} (sin θ)^r P_ℓ^{(r)}(cos θ)` (up to normalization). We make this explicit: with
`f = P_ℓ^{(r)}`, `n = ℓ - r`, `w = x + i y` and `ρ² = x² + y² + z²`, the polynomial
`solidMode ℓ r = w^r ∑_{k ≤ n/2} [x^{n-2k}] f · z^{n-2k} ρ^{2k} ∈ ℂ[x, y, z]`

* is homogeneous of degree `ℓ` (`isHomogeneous_solidMode`),
* is harmonic, `Δ solidMode = 0` (`polyLaplacian_solidMode`), from the associated Legendre
  equation `(1-x²) f'' - 2(r+1) x f' + (ℓ-r)(ℓ+r+1) f = 0`,
* is nonzero (`solidMode_ne_zero`), and
* at `(ρ sin θ cos φ, ρ sin θ sin φ, ρ cos θ)` takes the value `ρ^ℓ · sphericalMode ℓ r θ φ`
  (`eval_sphericalPoint_solidMode`), in particular it restricts to `sphericalMode ℓ r` on the
  unit sphere.

The Laplacian is `polyLaplacian` (sum of the second partial derivatives); Mathlib has no
spherical Laplacian, so the eigenfunction statement on the sphere is not formalized.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- The coefficient recurrence of `f = P_{n+r}^{(r)}` from its differential equation:
`(j+2)(j+1) [x^{j+2}] f = (j-n)(j+n+2r+1) [x^j] f`. -/
theorem coeff_iterate_derivative_legendreP_recurrence (n r j : ℕ) :
    ((j : ℚ) + 2) * ((j : ℚ) + 1) * (derivative^[r] (legendreP (n + r))).coeff (j + 2) =
      ((j : ℚ) - n) * ((j : ℚ) + n + 2 * r + 1) *
        (derivative^[r] (legendreP (n + r))).coeff j := by
  have hode := iterate_derivative_legendreP_differential_equation n r
  set f := derivative^[r] (legendreP (n + r))
  have key : (1 - polyX ^ 2) * derivative (derivative f) -
      C (2 * (r : ℚ) + 2) * polyX * derivative f + C ((n : ℚ) * (n + 2 * r + 1)) * f =
      derivative (derivative f) - polyX * derivative (polyX * derivative f) + polyX * derivative f -
        C (2 * (r : ℚ) + 2) * (polyX * derivative f) + C ((n : ℚ) * (n + 2 * r + 1)) * f := by
    rw [derivative_mul, derivative_X]; ring
  rw [key] at hode
  have hj := congrArg (fun p : ℚ[X] => p.coeff j) hode
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul_derivative, coeff_derivative,
    Polynomial.coeff_zero] at hj
  try rw [show j + 1 + 1 = j + 2 from rfl] at hj
  push_cast at hj
  linear_combination hj

/-- `f = P_{n+r}^{(r)}` is the sum of its terms of the parity of `n`:
`f = ∑_{k ≤ n/2} [x^{n-2k}] f · x^{n-2k}`. -/
theorem iterate_derivative_legendreP_eq_sum_coeff (n r : ℕ) :
    derivative^[r] (legendreP (n + r)) = ∑ k ∈ range (n / 2 + 1),
      C ((derivative^[r] (legendreP (n + r))).coeff (n - 2 * k)) * polyX ^ (n - 2 * k) := by
  conv_lhs => rw [iterate_derivative_legendreP]
  rw [mul_sum]
  refine sum_congr rfl fun k hk => ?_
  rw [coeff_iterate_derivative_legendreP n r k (Nat.lt_succ_iff.mp (mem_range.mp hk)), C_mul]
  ring

/-- **The solid harmonic of degree `ℓ` and order `r`:**
`w^r ∑_{k ≤ (ℓ-r)/2} [x^{ℓ-r-2k}] P_ℓ^{(r)} · z^{ℓ-r-2k} (x² + y² + z²)^k`, `w = x + i y`. -/
noncomputable def solidMode (ℓ r : ℕ) : MvPolynomial (Fin 3) ℂ :=
  xPlusIY ^ r * ∑ k ∈ range ((ℓ - r) / 2 + 1),
    MvPolynomial.C (((derivative^[r] (legendreP ℓ)).coeff (ℓ - r - 2 * k) : ℚ) : ℂ) *
      (MvPolynomial.X 2 ^ (ℓ - r - 2 * k) * normSqPoly ^ k)

theorem solidMode_eq_explicit (ℓ r : ℕ) : solidMode ℓ r =
    xPlusIY ^ r * ∑ k ∈ range ((ℓ - r) / 2 + 1),
      MvPolynomial.C (((derivative^[r] (legendreP ℓ)).coeff (ℓ - r - 2 * k) : ℚ) : ℂ) *
        (MvPolynomial.X 2 ^ (ℓ - r - 2 * k) * normSqPoly ^ k) := (rfl)

theorem solidMode_eq (ℓ r : ℕ) : solidMode ℓ r =
    xPlusIY ^ r *
      zonalSum (ℓ - r) (fun j => (((derivative^[r] (legendreP ℓ)).coeff j : ℚ) : ℂ)) := by
  unfold solidMode
  rw [zonalSum_eq]

/-- **`solidMode ℓ r` is homogeneous of degree `ℓ`.** -/
theorem isHomogeneous_solidMode (ℓ r : ℕ) (h : r ≤ ℓ) : (solidMode ℓ r).IsHomogeneous ℓ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h
  rw [solidMode_eq, Nat.add_sub_cancel]
  exact isHomogeneous_xPlusIY_pow_mul_zonalSum n r _

/-- **`solidMode ℓ r` is harmonic:** `Δ (solidMode ℓ r) = 0`, from the differential equation
of `P_ℓ^{(r)}`. -/
theorem polyLaplacian_solidMode (ℓ r : ℕ) (h : r ≤ ℓ) : polyLaplacian (solidMode ℓ r) = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h
  rw [solidMode_eq, Nat.add_sub_cancel]
  refine polyLaplacian_xPlusIY_pow_mul_zonalSum n r _ fun j => ?_
  have hj := coeff_iterate_derivative_legendreP_recurrence n r j
  exact_mod_cast hj

/-- **`solidMode ℓ r ≠ 0`** (its value at the isotropic point `(1, 0, i)` is
`i^{ℓ-r}` times the leading coefficient of `P_ℓ^{(r)}`). -/
theorem solidMode_ne_zero (ℓ r : ℕ) (h : r ≤ ℓ) : solidMode ℓ r ≠ 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h
  intro h0
  have hv := congrArg (MvPolynomial.eval ![(1 : ℂ), 0, Complex.I]) h0
  have hS : MvPolynomial.eval ![(1 : ℂ), 0, Complex.I] normSqPoly = 0 := by
    rw [eval_normSqPoly]
    simp
  rw [solidMode_eq, Nat.add_sub_cancel, map_mul, map_pow, eval_xPlusIY,
    eval_zonalSum_of_eval_normSqPoly_eq_zero _ _ _ hS, map_zero] at hv
  have hc := coeff_iterate_derivative_legendreP_self_ne_zero n r
  simp [hc] at hv

/-- The point `(ρ sin θ cos φ, ρ sin θ sin φ, ρ cos θ)`, as a point of `ℂ³`. -/
noncomputable def sphericalPoint (ρ θ φ : ℝ) : Fin 3 → ℂ :=
  ![(ρ : ℂ) * (Real.sin θ : ℂ) * (Real.cos φ : ℂ), (ρ : ℂ) * (Real.sin θ : ℂ) * (Real.sin φ : ℂ),
    (ρ : ℂ) * (Real.cos θ : ℂ)]

theorem sphericalPoint_zero (ρ θ φ : ℝ) :
    sphericalPoint ρ θ φ 0 = (ρ : ℂ) * (Real.sin θ : ℂ) * (Real.cos φ : ℂ) := by
  simp [sphericalPoint]

theorem sphericalPoint_one (ρ θ φ : ℝ) :
    sphericalPoint ρ θ φ 1 = (ρ : ℂ) * (Real.sin θ : ℂ) * (Real.sin φ : ℂ) := by
  simp [sphericalPoint]

theorem sphericalPoint_two (ρ θ φ : ℝ) :
    sphericalPoint ρ θ φ 2 = (ρ : ℂ) * (Real.cos θ : ℂ) := by
  simp [sphericalPoint]

/-- **Spherical coordinates (§1.5).** At `(ρ sin θ cos φ, ρ sin θ sin φ, ρ cos θ)` the
solid harmonic `solidMode ℓ r` equals `ρ^ℓ e^{irφ} (sin θ)^r P_ℓ^{(r)}(cos θ)`. -/
theorem eval_sphericalPoint_solidMode (ℓ r : ℕ) (h : r ≤ ℓ) (ρ θ φ : ℝ) :
    MvPolynomial.eval (sphericalPoint ρ θ φ) (solidMode ℓ r) =
      (ρ : ℂ) ^ ℓ * sphericalMode ℓ r θ φ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h
  have hθ := congrArg Complex.ofReal (Real.sin_sq_add_cos_sq θ)
  have hφ := congrArg Complex.ofReal (Real.sin_sq_add_cos_sq φ)
  simp only [Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_one] at hθ hφ
  have hw : (ρ : ℂ) * (Real.sin θ : ℂ) * (Real.cos φ : ℂ) +
      Complex.I * ((ρ : ℂ) * (Real.sin θ : ℂ) * (Real.sin φ : ℂ)) =
      (ρ : ℂ) * (Real.sin θ : ℂ) * Complex.exp (φ * Complex.I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; ring
  have hS : ((ρ : ℂ) * (Real.sin θ : ℂ) * (Real.cos φ : ℂ)) ^ 2 +
      ((ρ : ℂ) * (Real.sin θ : ℂ) * (Real.sin φ : ℂ)) ^ 2 + ((ρ : ℂ) * (Real.cos θ : ℂ)) ^ 2 =
      (ρ : ℂ) ^ 2 := by
    linear_combination ((ρ : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2) * hφ + (ρ : ℂ) ^ 2 * hθ
  have hfR : aeval (Real.cos θ) (derivative^[r] (legendreP (n + r))) =
      ∑ k ∈ range (n / 2 + 1),
        (((derivative^[r] (legendreP (n + r))).coeff (n - 2 * k) : ℚ) : ℝ) *
          Real.cos θ ^ (n - 2 * k) := by
    conv_lhs => rw [iterate_derivative_legendreP_eq_sum_coeff n r]
    simp only [map_sum, map_mul, aeval_C, aeval_X_pow, eq_ratCast]
  have hsum : ∑ k ∈ range (n / 2 + 1),
      (((derivative^[r] (legendreP (n + r))).coeff (n - 2 * k) : ℚ) : ℂ) *
        (((ρ : ℂ) * (Real.cos θ : ℂ)) ^ (n - 2 * k) * ((ρ : ℂ) ^ 2) ^ k) =
      (ρ : ℂ) ^ n * ∑ k ∈ range (n / 2 + 1),
        (((derivative^[r] (legendreP (n + r))).coeff (n - 2 * k) : ℚ) : ℂ) *
          (Real.cos θ : ℂ) ^ (n - 2 * k) := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk' : 2 * k ≤ n := by have := mem_range.mp hk; omega
    have e : (ρ : ℂ) ^ n = (ρ : ℂ) ^ (n - 2 * k) * ((ρ : ℂ) ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hk']
    rw [e]; ring
  rw [solidMode_eq, Nat.add_sub_cancel, map_mul, map_pow, eval_xPlusIY, eval_zonalSum,
    eval_normSqPoly, sphericalPoint_zero, sphericalPoint_one, sphericalPoint_two, hw, hS, hsum,
    sphericalMode_eq, Complex.ofReal_mul, Complex.ofReal_pow, hfR,
    show (r : ℂ) * φ * Complex.I = r * (φ * Complex.I) from mul_assoc _ _ _,
    Complex.exp_nat_mul]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ratCast]
  ring

/-- **On the unit sphere** `solidMode ℓ r` restricts to the spherical mode
`e^{irφ} (sin θ)^r P_ℓ^{(r)}(cos θ)`. -/
theorem eval_sphericalPoint_one_solidMode (ℓ r : ℕ) (h : r ≤ ℓ) (θ φ : ℝ) :
    MvPolynomial.eval (sphericalPoint 1 θ φ) (solidMode ℓ r) = sphericalMode ℓ r θ φ := by
  rw [eval_sphericalPoint_solidMode ℓ r h, Complex.ofReal_one, one_pow, one_mul]

/-- **§1.5.** For `0 ≤ r ≤ ℓ` the spherical mode
`e^{irφ} (sin θ)^r P_ℓ^{(r)}(cos θ)` is the restriction to the unit sphere of a nonzero
harmonic polynomial, homogeneous of degree `ℓ`, whose value at radius `ρ` is `ρ^ℓ` times the
mode. -/
theorem sphericalMode_is_solid_harmonic (ℓ r : ℕ) (h : r ≤ ℓ) :
    ∃ p : MvPolynomial (Fin 3) ℂ, p ≠ 0 ∧ p.IsHomogeneous ℓ ∧ polyLaplacian p = 0 ∧
      ∀ ρ θ φ : ℝ, MvPolynomial.eval (sphericalPoint ρ θ φ) p =
        (ρ : ℂ) ^ ℓ * sphericalMode ℓ r θ φ :=
  ⟨solidMode ℓ r, solidMode_ne_zero ℓ r h, isHomogeneous_solidMode ℓ r h,
    polyLaplacian_solidMode ℓ r h, eval_sphericalPoint_solidMode ℓ r h⟩

end ArithmeticOfJacobiPolynomials
