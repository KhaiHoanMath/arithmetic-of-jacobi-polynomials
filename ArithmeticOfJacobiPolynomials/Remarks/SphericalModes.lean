/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Applications.ConeModes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Vanishing of spherical modes on the circular cone (§1.5)

The manuscript describes the polar part of a spherical mode of degree `ℓ` and order `r` as
`(sin θ)^r P_ℓ^{(r)}(cos θ)` (up to normalization; this identification with spherical harmonics is
[DLMF, 14.7.8, 14.30.1] and is not formalized: Mathlib has no spherical harmonics). We record the
explicit mode `e^{irφ} (sin θ)^r P_ℓ^{(r)}(cos θ)` and prove the elementary translations claimed
in the text:

* the cone `x² + y² - 2z² = 0` meets the unit sphere exactly at `z = ±1/√3`;
* for `cos θ ∈ (-1, 1)` the mode vanishes on the latitude `cos θ` iff `P_ℓ^{(r)}(cos θ) = 0`;
* the mode vanishes on the whole intersection of the cone with the sphere iff
  `3x² - 1 ∣ P_ℓ^{(r)}`, iff it vanishes on one of the two latitudes (parity).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Complex

/-- The explicit spherical mode `e^{irφ} (sin θ)^r P_ℓ^{(r)}(cos θ)` of degree `ℓ` and order
`r` (up to normalization). -/
noncomputable def sphericalMode (ℓ r : ℕ) (θ φ : ℝ) : ℂ :=
  Complex.exp (r * φ * Complex.I) * ((Real.sin θ ^ r *
    aeval (Real.cos θ) (derivative^[r] (legendreP ℓ)) : ℝ) : ℂ)

theorem sphericalMode_eq (ℓ r : ℕ) (θ φ : ℝ) : sphericalMode ℓ r θ φ =
    Complex.exp (r * φ * Complex.I) * ((Real.sin θ ^ r *
      aeval (Real.cos θ) (derivative^[r] (legendreP ℓ)) : ℝ) : ℂ) := (rfl)

/-- The circular cone `x² + y² - 2z² = 0` meets the unit sphere exactly where `z² = 1/3`,
i.e. at `z = ±1/√3`. -/
theorem cone_inter_sphere_iff (x y z : ℝ) :
    (x ^ 2 + y ^ 2 + z ^ 2 = 1 ∧ x ^ 2 + y ^ 2 - 2 * z ^ 2 = 0) ↔
      (x ^ 2 + y ^ 2 + z ^ 2 = 1 ∧ (z = 1 / Real.sqrt 3 ∨ z = -(1 / Real.sqrt 3))) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < Real.sqrt 3 := by positivity
  have hz : ∀ z : ℝ, z ^ 2 = 1 / 3 ↔ (z = 1 / Real.sqrt 3 ∨ z = -(1 / Real.sqrt 3)) := by
    intro z
    have e : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by rw [div_pow, h3, one_pow]
    rw [← e, sq_eq_sq_iff_eq_or_eq_neg]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (hz z).mp (by linarith)⟩
  · rintro ⟨h1, h2⟩
    have := (hz z).mpr h2
    exact ⟨h1, by linarith⟩

/-- For `α = cos θ ∈ (-1, 1)`, the mode vanishes on the whole latitude `θ` iff
`P_ℓ^{(r)}(cos θ) = 0`. -/
theorem sphericalMode_latitude_eq_zero_iff (ℓ r : ℕ) {θ : ℝ} (h1 : -1 < Real.cos θ)
    (h2 : Real.cos θ < 1) :
    (∀ φ : ℝ, sphericalMode ℓ r θ φ = 0) ↔
      aeval (Real.cos θ) (derivative^[r] (legendreP ℓ)) = 0 := by
  have hs : Real.sin θ ≠ 0 := by
    intro h
    have := Real.sin_sq_add_cos_sq θ
    rw [h] at this
    nlinarith
  constructor
  · intro h
    have h0 := h 0
    rw [sphericalMode_eq, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact absurd h0 (Complex.exp_ne_zero _)
    · have h0' := Complex.ofReal_eq_zero.mp h0
      exact (mul_eq_zero.mp h0').resolve_left (pow_ne_zero _ hs)
  · intro h φ
    rw [sphericalMode_eq, h, mul_zero, Complex.ofReal_zero, mul_zero]

/-- A rational polynomial vanishes at `1/√3` iff `X² - 1/3` divides it. -/
theorem aeval_inv_sqrt_three_eq_zero_iff (P : ℚ[X]) :
    aeval (1 / Real.sqrt 3) P = 0 ↔ polyX ^ 2 - C (1 / 3 : ℚ) ∣ P := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpa : aeval (1 / Real.sqrt 3) (polyX ^ 2 - C (1 / 3 : ℚ)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, div_pow, h3, eq_ratCast]
    norm_num
  have hmin := minpoly.eq_of_irreducible_of_monic irreducible_X_sq_sub_one_third hpa
    (monic_X_pow_sub_C _ two_ne_zero)
  constructor
  · intro h
    rw [hmin]
    exact minpoly.dvd ℚ _ h
  · rintro ⟨g, rfl⟩
    rw [map_mul, hpa, zero_mul]

/-- Same at `-1/√3`. -/
theorem aeval_neg_inv_sqrt_three_eq_zero_iff (P : ℚ[X]) :
    aeval (-(1 / Real.sqrt 3)) P = 0 ↔ polyX ^ 2 - C (1 / 3 : ℚ) ∣ P := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpa : aeval (-(1 / Real.sqrt 3)) (polyX ^ 2 - C (1 / 3 : ℚ)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, neg_sq, div_pow, h3, eq_ratCast]
    norm_num
  have hmin := minpoly.eq_of_irreducible_of_monic irreducible_X_sq_sub_one_third hpa
    (monic_X_pow_sub_C _ two_ne_zero)
  constructor
  · intro h
    rw [hmin]
    exact minpoly.dvd ℚ _ h
  · rintro ⟨g, rfl⟩
    rw [map_mul, hpa, zero_mul]

/-- `X² - 1/3` and `3X² - 1` have the same multiples in `ℚ[X]`. -/
theorem X_sq_sub_one_third_dvd_iff (P : ℚ[X]) :
    polyX ^ 2 - C (1 / 3 : ℚ) ∣ P ↔ C 3 * polyX ^ 2 - 1 ∣ P := by
  have e : C 3 * polyX ^ 2 - 1 = C (3 : ℚ) * (polyX ^ 2 - C (1 / 3 : ℚ)) := by
    rw [mul_sub, ← C_mul]; norm_num
  rw [e, (C_mul_dvd (by norm_num : (3 : ℚ) ≠ 0))]

/-- **§1.5.** The mode of degree `ℓ` and order `r` vanishes on the intersection
of the cone `x² + y² - 2z² = 0` with the unit sphere (both latitudes `cos θ = ±1/√3`, all
longitudes) iff `3x² - 1` divides `P_ℓ^{(r)}`; vanishing on one of the two latitudes already
suffices (parity). -/
theorem sphericalMode_cone_eq_zero_iff (ℓ r : ℕ) :
    ((∀ θ φ : ℝ, (Real.cos θ = 1 / Real.sqrt 3 ∨ Real.cos θ = -(1 / Real.sqrt 3)) →
        sphericalMode ℓ r θ φ = 0) ↔ C 3 * polyX ^ 2 - 1 ∣ derivative^[r] (legendreP ℓ)) ∧
    (∀ θ : ℝ, (Real.cos θ = 1 / Real.sqrt 3 ∨ Real.cos θ = -(1 / Real.sqrt 3)) →
      ((∀ φ : ℝ, sphericalMode ℓ r θ φ = 0) ↔
        C 3 * polyX ^ 2 - 1 ∣ derivative^[r] (legendreP ℓ))) := by
  have h3 : (1 : ℝ) < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hpos : (0 : ℝ) < 1 / Real.sqrt 3 := by positivity
  have hlt : 1 / Real.sqrt 3 < 1 := by rw [div_lt_one (by positivity)]; exact h3
  have hlat : ∀ θ : ℝ, (Real.cos θ = 1 / Real.sqrt 3 ∨ Real.cos θ = -(1 / Real.sqrt 3)) →
      ((∀ φ : ℝ, sphericalMode ℓ r θ φ = 0) ↔
        C 3 * polyX ^ 2 - 1 ∣ derivative^[r] (legendreP ℓ)) := by
    intro θ hθ
    rcases hθ with hθ | hθ
    · rw [sphericalMode_latitude_eq_zero_iff ℓ r (by rw [hθ]; linarith) (by rw [hθ]; exact hlt),
        hθ, aeval_inv_sqrt_three_eq_zero_iff, X_sq_sub_one_third_dvd_iff]
    · rw [sphericalMode_latitude_eq_zero_iff ℓ r (by rw [hθ]; linarith) (by rw [hθ]; linarith),
        hθ, aeval_neg_inv_sqrt_three_eq_zero_iff, X_sq_sub_one_third_dvd_iff]
  refine ⟨⟨fun h => ?_, fun h θ φ hθ => ((hlat θ hθ).mpr h) φ⟩, hlat⟩
  have hc : Real.cos (Real.arccos (1 / Real.sqrt 3)) = 1 / Real.sqrt 3 :=
    Real.cos_arccos (by linarith) hlt.le
  exact (hlat _ (Or.inl hc)).mp fun φ => h _ φ (Or.inl hc)

end ArithmeticOfJacobiPolynomials
