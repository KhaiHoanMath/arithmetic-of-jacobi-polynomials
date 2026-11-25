/- Assembled by AxiomProver. -/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.CharP.Lemmas
public import ArithmeticOfJacobiPolynomials.Remarks.HassePolynomial
public import ArithmeticOfJacobiPolynomials.External

/-!
# The Legendre elliptic curve and its supersingularity (§6.4)

The manuscript remarks that for an odd prime `p = 2m + 1` the polynomial
`∑_{j ≤ m} binom(m,j)² z^j = (1-z)^m P_m((1+z)/(1-z))` is a Hasse polynomial for the Legendre
curve `y² = x(x-1)(x-z)`: for `z ≠ 0, 1` it vanishes exactly at the supersingular Legendre
curves [BM, §1].

The curve and supersingularity constructions use Mathlib's Weierstrass curve and point group.

* `legendreCurve z : WeierstrassCurve K`, the curve `y² = x³ - (1+z)x² + zx`, with affine
  equation `y² = x(x-1)(x-z)` (`legendreCurve_equation_iff`), discriminant `16 z²(z-1)²`
  (`legendreCurve_Δ`), elliptic when `2 ≠ 0`, `z ≠ 0`, `z ≠ 1` (`legendreCurve_isElliptic`);
* `IsSupersingular p E`: the group of affine points of `E` over `AlgebraicClosure K` has no
  nonzero `p`-torsion (the definition of [KZ, §1]);
* `HasseSupersingularCriterion`, the **cited** classical criterion [KZ, §2, Proposition 1 and
  Corollary], taken as an explicit hypothesis (it is not proved here);
* `legendreCurve_isSupersingular_iff`: under that hypothesis, for a finite field of
  characteristic `p = 2m + 1` and `z ≠ 0, 1`, the Legendre curve is supersingular iff
  `∑_{j ≤ m} binom(m,j)² z^j = 0`.

The arithmetic step is `ArithmeticOfJacobiPolynomials.coeff_legendreCurve_pow`
(Remarks/HassePolynomial): the
coefficient of `x^{2m}` in `(x(x-1)(x-z))^m` is `(-1)^m ∑_j binom(m,j)² z^j`.

The criterion applies over finite fields. The algebraic-closure statement follows by
finite-field descent in `LegendreEllipticDescent`.

-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

namespace LegendreElliptic

open Polynomial Finset

open scoped Polynomial.Bivariate

universe u

/-- **The Legendre curve** `y² = x(x-1)(x-z)`, as the Weierstrass curve with `a₁ = a₃ = a₆ = 0`,
`a₂ = -(1+z)`, `a₄ = z`. -/
@[expose] def legendreCurve {K : Type*} [CommRing K] (z : K) : WeierstrassCurve K :=
  shortCubicCurve (-(1 + z)) z 0

@[simp] theorem legendreCurve_a₁ {K : Type*} [CommRing K] (z : K) : (legendreCurve z).a₁ = 0 :=
  rfl
@[simp] theorem legendreCurve_a₂ {K : Type*} [CommRing K] (z : K) :
    (legendreCurve z).a₂ = -(1 + z) := rfl
@[simp] theorem legendreCurve_a₃ {K : Type*} [CommRing K] (z : K) : (legendreCurve z).a₃ = 0 :=
  rfl
@[simp] theorem legendreCurve_a₄ {K : Type*} [CommRing K] (z : K) : (legendreCurve z).a₄ = z :=
  rfl
@[simp] theorem legendreCurve_a₆ {K : Type*} [CommRing K] (z : K) : (legendreCurve z).a₆ = 0 :=
  rfl

/-- The affine equation of the Legendre curve is `y² = x(x-1)(x-z)`. -/
theorem legendreCurve_equation_iff {K : Type*} [CommRing K] (z x y : K) :
    (legendreCurve z).toAffine.Equation x y ↔ y ^ 2 = x * (x - 1) * (x - z) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [legendreCurve_a₁, legendreCurve_a₂, legendreCurve_a₃, legendreCurve_a₄,
    legendreCurve_a₆]
  constructor <;> intro h <;> linear_combination h

/-- The cubic of the Legendre curve is `x(x-1)(x-z)`. -/
theorem monicCubic_legendre {K : Type*} [CommRing K] (z : K) :
    monicCubic (-(1 + z)) z 0 = polyX * (polyX - 1) * (polyX - C z) := by
  simp only [monicCubic, C_neg, C_add, C_1, C_0, add_zero]
  ring

/-- The affine polynomial of the Legendre curve is `Y² - x(x-1)(x-z)`. -/
theorem legendreCurve_polynomial {K : Type*} [CommRing K] (z : K) :
    (legendreCurve z).toAffine.polynomial = Y ^ 2 - C (polyX * (polyX - 1) * (polyX - C z)) := by
  rw [WeierstrassCurve.Affine.polynomial, ← monicCubic_legendre]
  simp [legendreCurve, shortCubicCurve, monicCubic]

/-- The discriminant of the Legendre curve is `16 z²(z-1)²`. -/
theorem legendreCurve_Δ {K : Type*} [CommRing K] (z : K) :
    (legendreCurve z).Δ = 16 * z ^ 2 * (z - 1) ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, legendreCurve_a₁, legendreCurve_a₂, legendreCurve_a₃, legendreCurve_a₄,
    legendreCurve_a₆]
  ring

/-- The Legendre curve is elliptic when `2 ≠ 0`, `z ≠ 0` and `z ≠ 1`. -/
theorem legendreCurve_isElliptic {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {z : K} (hz0 : z ≠ 0)
    (hz1 : z ≠ 1) : (legendreCurve z).IsElliptic := by
  refine ⟨?_⟩
  rw [legendreCurve_Δ, isUnit_iff_ne_zero]
  have h16 : (16 : K) = 2 ^ 4 := by norm_num
  rw [h16]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ hz0))
    (pow_ne_zero _ (sub_ne_zero.mpr hz1))

/-- **The Legendre family is a Hasse family (§6.4)**, conditional on the cited
Hasse–Deuring criterion. For a finite field `K` of characteristic `p = 2m + 1` and `z ≠ 0, 1`,
the Legendre curve `y² = x(x-1)(x-z)` is supersingular iff `∑_{j ≤ m} binom(m,j)² z^j = 0`. -/
theorem legendreCurve_isSupersingular_iff (hHasse : HasseSupersingularCriterion.{u})
    {K : Type u} [Field K] [Finite K] (p : ℕ) [CharP K p] (m : ℕ) (hp : p = 2 * m + 1)
    {z : K} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    IsSupersingular p (legendreCurve z) ↔
      ∑ j ∈ range (m + 1), ((m.choose j : ℕ) : K) ^ 2 * z ^ j = 0 := by
  have : NeZero p := ⟨by omega⟩
  have : Fact p.Prime := CharP.char_is_prime_of_pos K p
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : (p : ℕ) ∣ 2 := by
      have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
      exact this
    have hle := Nat.le_of_dvd (by norm_num) this
    have := (Fact.out : p.Prime).two_le
    omega
  have hΔ : (shortCubicCurve (-(1 + z)) z 0).Δ ≠ 0 :=
    (legendreCurve_isElliptic h2 hz0 hz1).isUnit.ne_zero
  rw [legendreCurve, hHasse K p hp2 _ _ _ hΔ, monicCubic_legendre,
    show (p - 1) / 2 = m by omega, show p - 1 = 2 * m by omega,
    ArithmeticOfJacobiPolynomials.coeff_legendreCurve_pow]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  · intro h
    rw [h, mul_zero]

end LegendreElliptic

end ArithmeticOfJacobiPolynomials
