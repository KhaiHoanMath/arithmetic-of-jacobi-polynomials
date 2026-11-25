/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Remarks.KanekoZagierSourcePolynomial
public import ArithmeticOfJacobiPolynomials.Remarks.ModularIntegrality
public import ArithmeticOfJacobiPolynomials.Remarks.LegendreEllipticDescent
public import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
public import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ

/-!
# The Kaneko–Zagier reduction to the supersingular `j`-polynomial (§6.4)

The manuscript states: when `ℓ ≥ 5` is prime, `Y^a (Y - 1728)^b F̃_{ℓ-1}(Y)` has `ℓ`-integral
coefficients and reduces to the monic polynomial whose roots are the supersingular
`j`-invariants in `𝔽̄_ℓ` [KZ, Theorem 1]. Here `ℓ = 12n + 6 + 2λ + 3μ`, `a = (λ+1)/2`,
`b = (μ+1)/2` and `F̃_{ℓ-1}(Y) = 1728^n P_n^{(λ/3,μ/2)}(1 - Y/864)`.

The following results describe supersingularity and the reductions of the Jacobi polynomials.

* `isSupersingular_smul_iff`: supersingularity is invariant under every change of variables
  `(x, y) ↦ (u²x + r, u³y + u²sx + t)` of Weierstrass curves. The coordinate change is an
  injective additive map of point groups (`variableChangePoint`, `variableChangePoint_add`),
  so it preserves the existence of nonzero `p`-torsion.
* `supersingularJ ℓ ⊆ 𝔽̄_ℓ`, the set of `j` with `WeierstrassCurve.ofJ j` supersingular, and
  `mem_supersingularJ_iff_exists`: it is the set of `j(E)` for supersingular elliptic curves
  `E/𝔽̄_ℓ` (model independence, via `WeierstrassCurve.exists_variableChange_of_j_eq`).
* `legendreCurve_j`: `j(y² = x(x-1)(x-z)) = 256 (z²-z+1)³ / (z²(z-1)²)`, and
  `mem_supersingularJ_iff_legendre` (conditional only on the cited Hasse–Deuring criterion):
  `j ∈ 𝔽̄_ℓ` is supersingular iff `j = j(z)` for a root `z` of the Hasse polynomial
  `∑_{i ≤ m} binom(m,i)² z^i`, `ℓ = 2m + 1`.
* `ratPolyReduction ℓ f`: the coefficientwise reduction of a rational polynomial to `𝔽_ℓ`;
  `kanekoZagierReduction_monic`: the reduction of `Y^a (Y - 1728)^b F̃_{ℓ-1}` is monic of degree
  `n + a + b` (since `A_{n,r} ≡ 1 mod ℓ`); `kzReduction ℓ` is this reduction with
  `(λ, μ, n)` read off from `ℓ mod 12`.

The polynomial identity of [KZ, Theorem 1] itself (via (10)–(11) and Theorem 5 ii) of [KZ]) is
cited: `KanekoZagierSupersingularReduction` states it over KZ's own source polynomial.
The proved normalization bridge identifies it with the manuscript's Jacobi polynomial, and
`kanekoZagier_supersingular_reduction` derives the manuscript's sentence from it.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset WeierstrassCurve LegendreElliptic

/-! ### Changes of variables preserve supersingularity -/

section VariableChange

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (C : VariableChange F)

/-- The `x`-coordinate on `C • W` of the point with `x`-coordinate `x` on `W`:
`x' = u⁻²(x - r)`. -/
def variableChangeX (x : F) : F := ((C.u⁻¹ : Fˣ) : F) ^ 2 * (x - C.r)

/-- The `y`-coordinate on `C • W` of the point `(x, y)` on `W`:
`y' = u⁻³(y - s(x - r) - t)`. -/
def variableChangeY (x y : F) : F :=
  ((C.u⁻¹ : Fˣ) : F) ^ 3 * (y - C.s * (x - C.r) - C.t)

theorem variableChangeX_inj {x₁ x₂ : F} :
    variableChangeX C x₁ = variableChangeX C x₂ ↔ x₁ = x₂ := by
  constructor
  · intro h
    simp only [variableChangeX] at h
    have := mul_left_cancel₀ (pow_ne_zero 2 (Units.ne_zero C.u⁻¹)) h
    linear_combination this
  · rintro rfl
    rfl

theorem variableChangeY_inj {x y₁ y₂ : F} :
    variableChangeY C x y₁ = variableChangeY C x y₂ ↔ y₁ = y₂ := by
  constructor
  · intro h
    simp only [variableChangeY] at h
    have := mul_left_cancel₀ (pow_ne_zero 3 (Units.ne_zero C.u⁻¹)) h
    linear_combination this
  · rintro rfl
    rfl

theorem variableChange_equation_poly (x y : F) :
    variableChangeY C x y ^ 2 + (C • W).toAffine.a₁ * variableChangeX C x * variableChangeY C x y +
        (C • W).toAffine.a₃ * variableChangeY C x y -
      (variableChangeX C x ^ 3 + (C • W).toAffine.a₂ * variableChangeX C x ^ 2 +
        (C • W).toAffine.a₄ * variableChangeX C x + (C • W).toAffine.a₆) =
      ((C.u⁻¹ : Fˣ) : F) ^ 6 * (y ^ 2 + W.toAffine.a₁ * x * y + W.toAffine.a₃ * y -
        (x ^ 3 + W.toAffine.a₂ * x ^ 2 + W.toAffine.a₄ * x + W.toAffine.a₆)) := by
  simp only [variableChangeX, variableChangeY, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, variableChange_a₆]
  ring

theorem variableChange_polyX (x y : F) :
    (C • W).toAffine.a₁ * variableChangeY C x y - (3 * variableChangeX C x ^ 2 +
        2 * (C • W).toAffine.a₂ * variableChangeX C x + (C • W).toAffine.a₄) =
      ((C.u⁻¹ : Fˣ) : F) ^ 4 * ((W.toAffine.a₁ * y - (3 * x ^ 2 + 2 * W.toAffine.a₂ * x +
        W.toAffine.a₄)) + C.s * (2 * y + W.toAffine.a₁ * x + W.toAffine.a₃)) := by
  simp only [variableChangeX, variableChangeY, variableChange_a₁, variableChange_a₂,
    variableChange_a₄]
  ring

theorem variableChange_polyY (x y : F) :
    2 * variableChangeY C x y + (C • W).toAffine.a₁ * variableChangeX C x +
        (C • W).toAffine.a₃ =
      ((C.u⁻¹ : Fˣ) : F) ^ 3 * (2 * y + W.toAffine.a₁ * x + W.toAffine.a₃) := by
  simp only [variableChangeX, variableChangeY, variableChange_a₁, variableChange_a₃]
  ring

theorem variableChange_equation_iff (x y : F) :
    (C • W).toAffine.Equation (variableChangeX C x) (variableChangeY C x y) ↔
      W.toAffine.Equation x y := by
  rw [Affine.equation_iff', Affine.equation_iff', variableChange_equation_poly,
    mul_eq_zero_iff_left (pow_ne_zero 6 (Units.ne_zero C.u⁻¹))]

theorem variableChange_nonsingular {x y : F} (h : W.toAffine.Nonsingular x y) :
    (C • W).toAffine.Nonsingular (variableChangeX C x) (variableChangeY C x y) := by
  rw [Affine.nonsingular_iff'] at h ⊢
  obtain ⟨he, hne⟩ := h
  refine ⟨(variableChange_equation_iff W C x y).mpr he, ?_⟩
  rw [variableChange_polyX, variableChange_polyY]
  have hv : ((C.u⁻¹ : Fˣ) : F) ≠ 0 := Units.ne_zero _
  rcases hne with hN | hD
  · by_cases hD : 2 * y + W.toAffine.a₁ * x + W.toAffine.a₃ = 0
    · left
      refine mul_ne_zero (pow_ne_zero _ hv) ?_
      rw [hD, mul_zero, add_zero]
      exact hN
    · right
      exact mul_ne_zero (pow_ne_zero _ hv) hD
  · right
    exact mul_ne_zero (pow_ne_zero _ hv) hD

theorem variableChange_negY (x y : F) :
    (C • W).toAffine.negY (variableChangeX C x) (variableChangeY C x y) =
      variableChangeY C x (W.toAffine.negY x y) := by
  simp only [Affine.negY, variableChangeX, variableChangeY, variableChange_a₁, variableChange_a₃]
  ring

theorem variableChange_tangentNum (x y : F) :
    3 * variableChangeX C x ^ 2 + 2 * (C • W).toAffine.a₂ * variableChangeX C x +
        (C • W).toAffine.a₄ - (C • W).toAffine.a₁ * variableChangeY C x y =
      ((C.u⁻¹ : Fˣ) : F) ^ 4 * ((3 * x ^ 2 + 2 * W.toAffine.a₂ * x + W.toAffine.a₄ -
        W.toAffine.a₁ * y) - C.s * (y - W.toAffine.negY x y)) := by
  simp only [Affine.negY, variableChangeX, variableChangeY, variableChange_a₁, variableChange_a₂,
    variableChange_a₄]
  ring

theorem variableChange_tangentDen (x y : F) :
    variableChangeY C x y - variableChangeY C x (W.toAffine.negY x y) =
      ((C.u⁻¹ : Fˣ) : F) ^ 3 * (y - W.toAffine.negY x y) := by
  simp only [variableChangeY]
  ring

theorem variableChange_addX (x₁ x₂ L : F) :
    (C • W).toAffine.addX (variableChangeX C x₁) (variableChangeX C x₂)
        (((C.u⁻¹ : Fˣ) : F) * (L - C.s)) =
      variableChangeX C (W.toAffine.addX x₁ x₂ L) := by
  simp only [Affine.addX, variableChangeX, variableChange_a₁, variableChange_a₂]
  ring

theorem variableChange_addY (x₁ x₂ y₁ L : F) :
    (C • W).toAffine.addY (variableChangeX C x₁) (variableChangeX C x₂) (variableChangeY C x₁ y₁)
        (((C.u⁻¹ : Fˣ) : F) * (L - C.s)) =
      variableChangeY C (W.toAffine.addX x₁ x₂ L) (W.toAffine.addY x₁ x₂ y₁ L) := by
  simp only [Affine.addY, Affine.negAddY, Affine.negY, Affine.addX, variableChangeX,
    variableChangeY, variableChange_a₁, variableChange_a₂, variableChange_a₃]
  ring

theorem div_aux_tangent {v N D s : F} (hv : v ≠ 0) (hD : D ≠ 0) :
    v ^ 4 * (N - s * D) / (v ^ 3 * D) = v * (N / D - s) := by
  rw [eq_comm, eq_div_iff (mul_ne_zero (pow_ne_zero 3 hv) hD)]
  have h := div_mul_cancel₀ N hD
  linear_combination v ^ 4 * h

theorem div_aux_secant {v Y Z s : F} (hv : v ≠ 0) (hZ : Z ≠ 0) :
    v ^ 3 * (Y - s * Z) / (v ^ 2 * Z) = v * (Y / Z - s) := by
  rw [eq_comm, eq_div_iff (mul_ne_zero (pow_ne_zero 2 hv) hZ)]
  have h := div_mul_cancel₀ Y hZ
  linear_combination v ^ 3 * h

/-- The change of variables `C` as a map of point groups `W(F) → (C • W)(F)`. -/
@[expose] def variableChangePoint : W.toAffine.Point → (C • W).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    .some (variableChangeX C x) (variableChangeY C x y) (variableChange_nonsingular W C h)

theorem variableChangePoint_zero : variableChangePoint W C 0 = 0 := rfl

theorem variableChangePoint_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    variableChangePoint W C (.some x y h) =
      .some (variableChangeX C x) (variableChangeY C x y) (variableChange_nonsingular W C h) := rfl

variable [DecidableEq F]

theorem variableChange_slope_tangent {x₁ y₁ : F} (hy : y₁ ≠ W.toAffine.negY x₁ y₁) :
    (C • W).toAffine.slope (variableChangeX C x₁) (variableChangeX C x₁) (variableChangeY C x₁ y₁)
        (variableChangeY C x₁ y₁) =
      ((C.u⁻¹ : Fˣ) : F) * (W.toAffine.slope x₁ x₁ y₁ y₁ - C.s) := by
  have hv : ((C.u⁻¹ : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have hD : y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
  have hy' : variableChangeY C x₁ y₁ ≠
      (C • W).toAffine.negY (variableChangeX C x₁) (variableChangeY C x₁ y₁) := by
    rw [variableChange_negY]
    exact fun h => hy ((variableChangeY_inj C).mp h)
  rw [Affine.slope_of_Y_ne rfl hy', Affine.slope_of_Y_ne rfl hy, variableChange_negY,
    variableChange_tangentNum, variableChange_tangentDen]
  exact div_aux_tangent hv hD

theorem variableChange_slope_secant {x₁ x₂ y₁ y₂ : F} (hx : x₁ ≠ x₂) :
    (C • W).toAffine.slope (variableChangeX C x₁) (variableChangeX C x₂) (variableChangeY C x₁ y₁)
        (variableChangeY C x₂ y₂) =
      ((C.u⁻¹ : Fˣ) : F) * (W.toAffine.slope x₁ x₂ y₁ y₂ - C.s) := by
  have hv : ((C.u⁻¹ : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have hx' : variableChangeX C x₁ ≠ variableChangeX C x₂ :=
    fun h => hx ((variableChangeX_inj C).mp h)
  have e1 : variableChangeY C x₁ y₁ - variableChangeY C x₂ y₂ =
      ((C.u⁻¹ : Fˣ) : F) ^ 3 * ((y₁ - y₂) - C.s * (x₁ - x₂)) := by
    simp only [variableChangeY]
    ring
  have e2 : variableChangeX C x₁ - variableChangeX C x₂ = ((C.u⁻¹ : Fˣ) : F) ^ 2 * (x₁ - x₂) := by
    simp only [variableChangeX]
    ring
  rw [Affine.slope_of_X_ne hx', Affine.slope_of_X_ne hx, e1, e2]
  exact div_aux_secant hv (sub_ne_zero.mpr hx)

theorem variableChange_slope {x₁ x₂ y₁ y₂ : F} (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    (C • W).toAffine.slope (variableChangeX C x₁) (variableChangeX C x₂) (variableChangeY C x₁ y₁)
        (variableChangeY C x₂ y₂) =
      ((C.u⁻¹ : Fˣ) : F) * (W.toAffine.slope x₁ x₂ y₁ y₂ - C.s) := by
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ W.toAffine.negY x₂ y₂ := fun hy => hxy ⟨hx, hy⟩
    have hy12 : y₁ = y₂ := Affine.Y_eq_of_Y_ne h₁ h₂ hx hy
    have hy₁ : y₁ ≠ W.toAffine.negY x₁ y₁ := fun h => hy (by rw [← hx, ← hy12]; exact h)
    rw [← hx, ← hy12]
    exact variableChange_slope_tangent W C hy₁
  · exact variableChange_slope_secant W C hx

/-- The change of variables is additive on points. -/
theorem variableChangePoint_add (P Q : W.toAffine.Point) :
    variableChangePoint W C (P + Q) = variableChangePoint W C P + variableChangePoint W C Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · rfl
  · rfl
  · by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · obtain ⟨hx, hy⟩ := hxy
      have hx' : variableChangeX C x₁ = variableChangeX C x₂ := by rw [hx]
      have hy' : variableChangeY C x₁ y₁ =
          (C • W).toAffine.negY (variableChangeX C x₂) (variableChangeY C x₂ y₂) := by
        rw [variableChange_negY, hx, hy]
      rw [Affine.Point.add_of_Y_eq hx hy, variableChangePoint_some, variableChangePoint_some,
        Affine.Point.add_of_Y_eq hx' hy']
      rfl
    · have hxy' : ¬(variableChangeX C x₁ = variableChangeX C x₂ ∧ variableChangeY C x₁ y₁ =
          (C • W).toAffine.negY (variableChangeX C x₂) (variableChangeY C x₂ y₂)) := by
        rintro ⟨hx, hy⟩
        rw [variableChange_negY] at hy
        have hx' : x₁ = x₂ := (variableChangeX_inj C).mp hx
        rw [hx'] at hy
        exact hxy ⟨hx', (variableChangeY_inj C).mp hy⟩
      rw [Affine.Point.add_some hxy, variableChangePoint_some, variableChangePoint_some,
        variableChangePoint_some, Affine.Point.add_some hxy']
      simp only [Affine.Point.some.injEq]
      rw [variableChange_slope W C ((Affine.nonsingular_iff' x₁ y₁).mp h₁).1
        ((Affine.nonsingular_iff' x₂ y₂).mp h₂).1 hxy]
      exact ⟨(variableChange_addX W C _ _ _).symm, (variableChange_addY W C _ _ _ _).symm⟩

/-- A change of variables carries a nonzero `n`-torsion point to a nonzero `n`-torsion point. -/
theorem exists_nsmul_eq_zero_variableChange (n : ℕ)
    (h : ∃ P : W.toAffine.Point, n • P = 0 ∧ P ≠ 0) :
    ∃ P : (C • W).toAffine.Point, n • P = 0 ∧ P ≠ 0 := by
  obtain ⟨P, hP, hP0⟩ := h
  let φ : W.toAffine.Point →+ (C • W).toAffine.Point :=
    AddMonoidHom.mk' (variableChangePoint W C) (variableChangePoint_add W C)
  refine ⟨φ P, by rw [← map_nsmul, hP, map_zero], ?_⟩
  rcases P with _ | ⟨x, y, h⟩
  · exact (hP0 rfl).elim
  · change variableChangePoint W C (.some x y h) ≠ 0
    rw [variableChangePoint_some]
    exact Affine.Point.some_ne_zero _

end VariableChange

/-- A change of variables preserves supersingularity. -/
theorem isSupersingular_smul {K : Type*} [Field K] (p : ℕ) (E : WeierstrassCurve K)
    (C : VariableChange K) (h : IsSupersingular p E) : IsSupersingular p (C • E) := by
  classical
  rw [isSupersingular_iff_not_exists] at h ⊢
  rintro ⟨P, hP, hP0⟩
  apply h
  have hb : (C • E).baseChange (AlgebraicClosure K) =
      (C.map (algebraMap K (AlgebraicClosure K))) • E.baseChange (AlgebraicClosure K) := by
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_variableChange]
  have hex : ∃ Q : ((C • E).baseChange (AlgebraicClosure K)).toAffine.Point,
      p • Q = 0 ∧ Q ≠ 0 := ⟨P, hP, hP0⟩
  rw [hb] at hex
  have h' := exists_nsmul_eq_zero_variableChange _
    (C.map (algebraMap K (AlgebraicClosure K)))⁻¹ p hex
  rwa [inv_smul_smul] at h'

/-- **Supersingularity is a property of the isomorphism class**: for every change of variables
`C`, `C • E` is supersingular iff `E` is. -/
theorem isSupersingular_smul_iff {K : Type*} [Field K] (p : ℕ) (E : WeierstrassCurve K)
    (C : VariableChange K) : IsSupersingular p (C • E) ↔ IsSupersingular p E := by
  refine ⟨fun h => ?_, isSupersingular_smul p E C⟩
  have := isSupersingular_smul p (C • E) C⁻¹ h
  rwa [inv_smul_smul] at this

/-! ### The supersingular locus -/

open scoped Classical in
theorem mem_supersingularJ_iff (ℓ : ℕ) [Fact ℓ.Prime] (j : AlgebraicClosure (ZMod ℓ)) :
    j ∈ supersingularJ ℓ ↔ IsSupersingular ℓ (WeierstrassCurve.ofJ j) :=
  Iff.rfl

open scoped Classical in
/-- **Model independence.** For an elliptic curve `E/𝔽̄_ℓ`, `j(E)` is a supersingular
`j`-invariant iff `E` is supersingular. -/
theorem j_mem_supersingularJ_iff (ℓ : ℕ) [Fact ℓ.Prime]
    (E : WeierstrassCurve (AlgebraicClosure (ZMod ℓ))) [E.IsElliptic] :
    E.j ∈ supersingularJ ℓ ↔ IsSupersingular ℓ E := by
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq
    (E := WeierstrassCurve.ofJ E.j) (E' := E) (heq := WeierstrassCurve.ofJ_j ..)
  have h1 : IsSupersingular ℓ (C • WeierstrassCurve.ofJ E.j) ↔ IsSupersingular ℓ E := by
    rw [hC]
  change IsSupersingular ℓ (WeierstrassCurve.ofJ E.j) ↔ _
  exact (isSupersingular_smul_iff ℓ _ C).symm.trans h1

open scoped Classical in
/-- `supersingularJ ℓ` is the set of `j`-invariants of supersingular elliptic curves over
`𝔽̄_ℓ`. -/
theorem mem_supersingularJ_iff_exists (ℓ : ℕ) [Fact ℓ.Prime] (j : AlgebraicClosure (ZMod ℓ)) :
    j ∈ supersingularJ ℓ ↔ ∃ (E : WeierstrassCurve (AlgebraicClosure (ZMod ℓ)))
      (_ : E.IsElliptic), E.j = j ∧ IsSupersingular ℓ E := by
  constructor
  · intro h
    exact ⟨WeierstrassCurve.ofJ j, inferInstance, WeierstrassCurve.ofJ_j .., h⟩
  · rintro ⟨E, _, rfl, hE⟩
    exact (j_mem_supersingularJ_iff ℓ E).mpr hE

/-! ### The Legendre description of the supersingular locus -/

/-- The `j`-invariant of the Legendre curve: `j = 256 (z² - z + 1)³ / (z² (z - 1)²)`. -/
theorem legendreCurve_j {K : Type*} [Field K] (z : K) [(legendreCurve z).IsElliptic] :
    (legendreCurve z).j = 256 * (z ^ 2 - z + 1) ^ 3 / (z ^ 2 * (z - 1) ^ 2) := by
  have hΔ : (legendreCurve z).Δ ≠ 0 := (legendreCurve z).isUnit_Δ.ne_zero
  have hc : (legendreCurve z).c₄ = 16 * (z ^ 2 - z + 1) := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, legendreCurve_a₁,
      legendreCurve_a₂, legendreCurve_a₃, legendreCurve_a₄]
    ring
  rw [legendreCurve_Δ] at hΔ
  have e : (16 : K) * z ^ 2 * (z - 1) ^ 2 = 16 * (z ^ 2 * (z - 1) ^ 2) := by ring
  rw [e] at hΔ
  have h16 : (16 : K) ≠ 0 := left_ne_zero_of_mul hΔ
  have hz : z ^ 2 * (z - 1) ^ 2 ≠ 0 := right_ne_zero_of_mul hΔ
  rw [WeierstrassCurve.j_eq, legendreCurve_Δ, hc, e, mul_inv, eq_div_iff hz]
  have h1 : (16 : K)⁻¹ * 16 = 1 := inv_mul_cancel₀ h16
  have h2 : (z ^ 2 * (z - 1) ^ 2)⁻¹ * (z ^ 2 * (z - 1) ^ 2) = 1 := inv_mul_cancel₀ hz
  linear_combination (4096 * (z ^ 2 - z + 1) ^ 3 * (16 : K)⁻¹) * h2 +
    (256 * (z ^ 2 - z + 1) ^ 3) * h1

open scoped Classical in
/-- **Supersingular `j`-invariants via the Legendre family** (Deuring), conditional only on the
cited Hasse–Deuring criterion. For a prime `ℓ = 2m + 1 ≥ 5`, `j ∈ 𝔽̄_ℓ` is a supersingular
`j`-invariant iff `j = 256 (z² - z + 1)³ / (z² (z - 1)²)` for some `z ≠ 0, 1` with
`∑_{i ≤ m} binom(m,i)² z^i = 0`. -/
theorem mem_supersingularJ_iff_legendre (hHasse : HasseSupersingularCriterion.{0})
    (ℓ m : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = 2 * m + 1) (h5 : 5 ≤ ℓ)
    (j : AlgebraicClosure (ZMod ℓ)) :
    j ∈ supersingularJ ℓ ↔ ∃ z : AlgebraicClosure (ZMod ℓ), z ≠ 0 ∧ z ≠ 1 ∧
      256 * (z ^ 2 - z + 1) ^ 3 = j * (z ^ 2 * (z - 1) ^ 2) ∧
      ∑ i ∈ range (m + 1), ((m.choose i : ℕ) : AlgebraicClosure (ZMod ℓ)) ^ 2 * z ^ i = 0 := by
  have : CharP (AlgebraicClosure (ZMod ℓ)) ℓ :=
    charP_of_injective_algebraMap (algebraMap (ZMod ℓ) (AlgebraicClosure (ZMod ℓ))).injective ℓ
  have hchar : ∀ k : ℕ, k < ℓ → 0 < k → (k : AlgebraicClosure (ZMod ℓ)) ≠ 0 := by
    intro k hk hk0 h
    have hd := (CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod ℓ)) ℓ k).mp h
    have := Nat.le_of_dvd hk0 hd
    omega
  have h2 : (2 : AlgebraicClosure (ZMod ℓ)) ≠ 0 := by
    exact_mod_cast hchar 2 (by omega) (by norm_num)
  have h3 : (3 : AlgebraicClosure (ZMod ℓ)) ≠ 0 := by
    exact_mod_cast hchar 3 (by omega) (by norm_num)
  have h256 : (256 : AlgebraicClosure (ZMod ℓ)) ≠ 0 := by
    rw [show (256 : AlgebraicClosure (ZMod ℓ)) = 2 ^ 8 by norm_num]
    exact pow_ne_zero _ h2
  have key : ∀ z : AlgebraicClosure (ZMod ℓ), z ≠ 0 → z ≠ 1 →
      256 * (z ^ 2 - z + 1) ^ 3 = j * (z ^ 2 * (z - 1) ^ 2) →
      (j ∈ supersingularJ ℓ ↔
        ∑ i ∈ range (m + 1), ((m.choose i : ℕ) : AlgebraicClosure (ZMod ℓ)) ^ 2 * z ^ i = 0) := by
    intro z hz0 hz1 hrel
    have := legendreCurve_isElliptic h2 hz0 hz1
    have hj : (legendreCurve z).j = j := by
      rw [legendreCurve_j, div_eq_iff (mul_ne_zero (pow_ne_zero 2 hz0)
        (pow_ne_zero 2 (sub_ne_zero.mpr hz1)))]
      exact hrel
    rw [← hj, j_mem_supersingularJ_iff]
    exact legendreCurve_isSupersingular_iff_closure hHasse ℓ m hℓ hz0 hz1
  constructor
  · intro hj
    obtain ⟨Q, hQ⟩ : ∃ Q : (AlgebraicClosure (ZMod ℓ))[X],
        Q = C 256 * (polyX ^ 2 - polyX + 1) ^ 3 - C j * (polyX ^ 2 * (polyX - 1) ^ 2) := ⟨_, rfl⟩
    have hev : ∀ x, Q.eval x = 256 * (x ^ 2 - x + 1) ^ 3 - j * (x ^ 2 * (x - 1) ^ 2) := by
      intro x
      rw [hQ]
      simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
    have hdeg : Q.degree ≠ 0 := by
      intro hd
      have hc := eq_C_of_degree_eq_zero hd
      have e0 := hev 0
      have e1 := hev (-1)
      have e3 := hev 3
      rw [hc, eval_C] at e0 e1 e3
      have h27648 : (27648 : AlgebraicClosure (ZMod ℓ)) = 0 := by
        linear_combination (-8) * e0 + 9 * e1 - e3
      rw [show (27648 : AlgebraicClosure (ZMod ℓ)) = 2 ^ 10 * 3 ^ 3 by norm_num] at h27648
      exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3) h27648
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root Q hdeg
    rw [IsRoot.def, hev] at hz
    have hrel : 256 * (z ^ 2 - z + 1) ^ 3 = j * (z ^ 2 * (z - 1) ^ 2) := sub_eq_zero.mp hz
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0] at hrel
      exact h256 (by linear_combination hrel)
    have hz1 : z ≠ 1 := by
      intro h1
      rw [h1] at hrel
      exact h256 (by linear_combination hrel)
    exact ⟨z, hz0, hz1, hrel, (key z hz0 hz1 hrel).mp hj⟩
  · rintro ⟨z, hz0, hz1, hrel, hH⟩
    exact (key z hz0 hz1 hrel).mpr hH

/-! ### The reduction of `Y^a (Y - 1728)^b F̃_{ℓ-1}` modulo `ℓ` -/

theorem coeff_ratPolyReduction (ℓ : ℕ) [Fact ℓ.Prime] (f : ℚ[X]) (i : ℕ) :
    (ratPolyReduction ℓ f).coeff i = ((f.coeff i : ℚ) : ZMod ℓ) := by
  simp only [ratPolyReduction, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq',
    Finset.mem_range]
  split_ifs with h
  · rfl
  · have hc : f.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hc, Rat.cast_zero]

/-- The reduction of an `ℓ`-integral rational `q = a / b` (`ℓ ∤ b`) is `a / b ∈ 𝔽_ℓ`. -/
theorem ratCast_zmod_eq_div {ℓ : ℕ} [Fact ℓ.Prime] (q : ℚ) (a b : ℤ) (hb : ¬ (ℓ : ℤ) ∣ b)
    (hq : q = a / b) : (q : ZMod ℓ) = (a : ZMod ℓ) / (b : ZMod ℓ) := by
  have hb0 : (b : ℚ) ≠ 0 := by
    intro h
    apply hb
    rw [Int.cast_eq_zero.mp h]
    exact dvd_zero _
  have hbZ : (b : ZMod ℓ) ≠ 0 := fun h => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b ℓ).mp h)
  have hdvd : (q.den : ℤ) ∣ b := by
    rw [hq, Rat.intCast_div_eq_divInt]
    exact Rat.den_dvd a b
  have hden : (q.den : ZMod ℓ) ≠ 0 := by
    intro h
    have h1 : ℓ ∣ q.den := (ZMod.natCast_eq_zero_iff q.den ℓ).mp h
    have h2 : (ℓ : ℤ) ∣ (q.den : ℤ) := Int.natCast_dvd_natCast.mpr h1
    exact hb (h2.trans hdvd)
  have hqb : q * b = a := by rw [hq, div_mul_cancel₀ _ hb0]
  have hnum : q.num * b = a * q.den := by
    have h1 : (q.num : ℚ) = q * q.den := (Rat.mul_den_eq_num q).symm
    have h2 : ((q.num * b : ℤ) : ℚ) = ((a * q.den : ℤ) : ℚ) := by
      push_cast
      rw [h1]
      linear_combination (q.den : ℚ) * hqb
    exact_mod_cast h2
  rw [Rat.cast_def, div_eq_div_iff hden hbZ]
  have := congrArg (Int.cast : ℤ → ZMod ℓ) hnum
  push_cast at this
  exact this

/-- If `A - 1 = ℓ a / b` with `ℓ ∤ b`, then `A` reduces to `1` in `𝔽_ℓ`. -/
theorem ratCast_zmod_eq_one_of_sub_one_eq {ℓ : ℕ} [Fact ℓ.Prime] {A : ℚ} {a b : ℤ}
    (hb : ¬ (ℓ : ℤ) ∣ b) (hA : A - 1 = ℓ * a / b) : (A : ZMod ℓ) = 1 := by
  have hb0 : (b : ℚ) ≠ 0 := by
    intro h
    apply hb
    rw [Int.cast_eq_zero.mp h]
    exact dvd_zero _
  have hbZ : (b : ZMod ℓ) ≠ 0 := fun h => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b ℓ).mp h)
  have hq : A = (((ℓ : ℤ) * a + b : ℤ) : ℚ) / (b : ℚ) := by
    rw [eq_div_iff hb0]
    have e : A = 1 + ℓ * a / b := by linear_combination hA
    rw [e, add_mul, div_mul_cancel₀ _ hb0]
    push_cast
    ring
  rw [ratCast_zmod_eq_div A _ _ hb hq]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_add]
  exact div_self hbZ

/-- **§6.4, the reduction is monic.** If `ℓ = 12n + 6 + 2λ + 3μ` is prime, the
reduction modulo `ℓ` of `Y^a (Y - 1728)^b F̃_{ℓ-1}(Y)` is monic of degree `a + b + n`
(its leading coefficient `A_{n,r}` is `≡ 1 mod ℓ`). -/
theorem kanekoZagierReduction_monic {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (n ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : ℤ) = 12 * n + 6 + 2 * l + 3 * μ) :
    (ratPolyReduction ℓ (kanekoZagierSupersingularPoly l μ n)).Monic ∧
      (ratPolyReduction ℓ (kanekoZagierSupersingularPoly l μ n)).natDegree =
        ((l + 1) / 2).toNat + ((μ + 1) / 2).toNat + n := by
  obtain ⟨a', b', hb', hA⟩ := kanekoZagierLeading_sub_one_eq hl hμ n ℓ hℓ Fact.out
  have hA1 := ratCast_zmod_eq_one_of_sub_one_eq hb' hA
  have hF0 : kanekoZagierModularPoly l μ n ≠ 0 := by
    intro h
    have hlc := leadingCoeff_kanekoZagierModularPoly (l := l) hμ n
    rw [h, leadingCoeff_zero] at hlc
    rw [← hlc, Rat.cast_zero] at hA1
    exact zero_ne_one hA1
  have h1 : (polyX : ℚ[X]) ^ ((l + 1) / 2).toNat ≠ 0 := pow_ne_zero _ X_ne_zero
  have h2 : (polyX - C (1728 : ℚ)) ^ ((μ + 1) / 2).toNat ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero _)
  have hdeg : (kanekoZagierSupersingularPoly l μ n).natDegree =
      ((l + 1) / 2).toNat + ((μ + 1) / 2).toNat + n := by
    rw [kanekoZagierSupersingularPoly, natDegree_mul (mul_ne_zero h1 h2) hF0,
      natDegree_mul h1 h2, natDegree_X_pow, natDegree_pow, natDegree_X_sub_C, mul_one,
      natDegree_kanekoZagierModularPoly hμ]
  have hlead : (kanekoZagierSupersingularPoly l μ n).coeff
      (((l + 1) / 2).toNat + ((μ + 1) / 2).toNat + n) =
        (-1) ^ n * Ring.choose (2 * (n : ℚ) + ((2 * l + 3 * μ : ℤ) : ℚ) / 6) n := by
    rw [← hdeg]
    change leadingCoeff _ = _
    rw [kanekoZagierSupersingularPoly, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_X_pow,
      leadingCoeff_pow, leadingCoeff_X_sub_C, leadingCoeff_kanekoZagierModularPoly hμ]
    simp only [one_pow, one_mul]
  have htop : (ratPolyReduction ℓ (kanekoZagierSupersingularPoly l μ n)).coeff
      (((l + 1) / 2).toNat + ((μ + 1) / 2).toNat + n) = 1 := by
    rw [coeff_ratPolyReduction, hlead, hA1]
  have hle : (ratPolyReduction ℓ (kanekoZagierSupersingularPoly l μ n)).natDegree ≤
      ((l + 1) / 2).toNat + ((μ + 1) / 2).toNat + n := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have hc : (kanekoZagierSupersingularPoly l μ n).coeff N = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hN)
    rw [coeff_ratPolyReduction, hc, Rat.cast_zero]
  have hRdeg := natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [htop]; exact one_ne_zero)
  refine ⟨?_, hRdeg⟩
  rw [Monic.def, leadingCoeff, hRdeg, htop]

/-! ### The prime `ℓ` determines `(λ, μ, n)` -/

/-- Every prime `ℓ ≥ 5` is `12n + 6 + 2λ + 3μ` with `n = ⌊ℓ/12⌋`, `λ = kzLambda ℓ`,
`μ = kzMu ℓ`. -/
theorem kzParams_of_prime {ℓ : ℕ} (hp : ℓ.Prime) (h5 : 5 ≤ ℓ) :
    (kzLambda ℓ = 1 ∨ kzLambda ℓ = -1) ∧ (kzMu ℓ = 1 ∨ kzMu ℓ = -1) ∧
      (ℓ : ℤ) = 12 * ((ℓ / 12 : ℕ) : ℤ) + 6 + 2 * kzLambda ℓ + 3 * kzMu ℓ := by
  have h2 : ¬ 2 ∣ ℓ := fun h => by
    have := hp.eq_one_or_self_of_dvd 2 h
    omega
  have h3 : ¬ 3 ∣ ℓ := fun h => by
    have := hp.eq_one_or_self_of_dvd 3 h
    omega
  unfold kzLambda kzMu
  split_ifs <;> omega

/-- The representation `ℓ = 12n + 6 + 2λ + 3μ` is unique. -/
theorem kzParams_unique {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {n ℓ : ℕ}
    (hℓ : (ℓ : ℤ) = 12 * n + 6 + 2 * l + 3 * μ) :
    kzLambda ℓ = l ∧ kzMu ℓ = μ ∧ ℓ / 12 = n := by
  unfold kzLambda kzMu
  rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl <;> split_ifs <;> omega

theorem kzReduction_eq {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {n ℓ : ℕ}
    [Fact ℓ.Prime] (hℓ : (ℓ : ℤ) = 12 * n + 6 + 2 * l + 3 * μ) :
    kzReduction ℓ = ratPolyReduction ℓ (kanekoZagierSupersingularPoly l μ n) := by
  obtain ⟨h1, h2, h3⟩ := kzParams_unique hl hμ hℓ
  rw [kzReduction, h1, h2, h3]

/-- For every prime `ℓ ≥ 5`, `kzReduction ℓ` is monic. -/
theorem kzReduction_monic (ℓ : ℕ) [Fact ℓ.Prime] (h5 : 5 ≤ ℓ) : (kzReduction ℓ).Monic := by
  obtain ⟨hl, hμ, hℓ⟩ := kzParams_of_prime (Fact.out : ℓ.Prime) h5
  exact (kanekoZagierReduction_monic hl hμ (ℓ / 12) ℓ hℓ).1

/-! ### [KZ, Theorem 1] -/

/-- **§6.4**, conditional on the cited [KZ, Theorem 1]. Let `λ, μ ∈ {-1, 1}` and
`ℓ = 12n + 6 + 2λ + 3μ` prime. Then `Y^a (Y - 1728)^b F̃_{ℓ-1}(Y)` has `ℓ`-integral
coefficients, its reduction modulo `ℓ` is monic, and over `𝔽̄_ℓ` the reduction is
`∏ (Y - j)` over the (finitely many) supersingular `j`-invariants `j ∈ 𝔽̄_ℓ`. The integrality
and monicity are proved; only the last identity uses `hKZ`. -/
theorem kanekoZagier_supersingular_reduction (hKZ : KanekoZagierSupersingularReduction)
    {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : ℤ) = 12 * n + 6 + 2 * l + 3 * μ) :
    (∀ i, (kanekoZagierSupersingularPoly l μ n).coeff i ≠ 0 →
        0 ≤ padicValRat ℓ ((kanekoZagierSupersingularPoly l μ n).coeff i)) ∧
      (ratPolyReduction ℓ (kanekoZagierSupersingularPoly l μ n)).Monic ∧
      ∃ s : Finset (AlgebraicClosure (ZMod ℓ)),
        (s : Set (AlgebraicClosure (ZMod ℓ))) = supersingularJ ℓ ∧
          (ratPolyReduction ℓ (kanekoZagierSupersingularPoly l μ n)).map
              (algebraMap (ZMod ℓ) (AlgebraicClosure (ZMod ℓ))) = ∏ j ∈ s, (polyX - C j) := by
  have h5 : 5 ≤ ℓ := by
    have := (Fact.out : ℓ.Prime).two_le
    rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl <;> omega
  refine ⟨fun i hi => ?_, (kanekoZagierReduction_monic hl hμ n ℓ hℓ).1, ?_⟩
  · rw [kanekoZagierSupersingularPoly] at hi ⊢
    exact padicValRat_coeff_kanekoZagier_nonneg hl hμ n ℓ hℓ Fact.out _ _ i hi
  · rw [← kzReduction_eq hl hμ hℓ]
    exact kanekoZagierReductionAtManuscriptPoly_of_source hKZ ℓ h5

/-- Conditional on [KZ, Theorem 1]: the roots in `𝔽̄_ℓ` of the reduction of
`Y^a (Y - 1728)^b F̃_{ℓ-1}` are exactly the supersingular `j`-invariants. -/
theorem kanekoZagier_isRoot_iff (hKZ : KanekoZagierSupersingularReduction)
    {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : ℤ) = 12 * n + 6 + 2 * l + 3 * μ) (j : AlgebraicClosure (ZMod ℓ)) :
    ((ratPolyReduction ℓ (kanekoZagierSupersingularPoly l μ n)).map
        (algebraMap (ZMod ℓ) (AlgebraicClosure (ZMod ℓ)))).IsRoot j ↔ j ∈ supersingularJ ℓ := by
  obtain ⟨-, -, s, hs, hprod⟩ := kanekoZagier_supersingular_reduction hKZ hl hμ n ℓ hℓ
  rw [hprod, ← hs, IsRoot.def, eval_prod, Finset.prod_eq_zero_iff, Finset.mem_coe]
  simp only [eval_sub, eval_X, eval_C, sub_eq_zero]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hj
    exact ⟨j, hj, rfl⟩

/-- Conditional on [KZ, Theorem 1] and the Hasse–Deuring criterion: for `ℓ = 2m + 1`, the roots
in `𝔽̄_ℓ` of the reduction of `Y^a (Y - 1728)^b F̃_{ℓ-1}` are the values
`256 (z² - z + 1)³ / (z² (z - 1)²)` at the roots `z ≠ 0, 1` of `∑_{i ≤ m} binom(m,i)² z^i`. -/
theorem kanekoZagier_isRoot_iff_legendre (hKZ : KanekoZagierSupersingularReduction)
    (hHasse : HasseSupersingularCriterion.{0})
    {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (n ℓ m : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : ℤ) = 12 * n + 6 + 2 * l + 3 * μ) (hm : ℓ = 2 * m + 1)
    (j : AlgebraicClosure (ZMod ℓ)) :
    ((ratPolyReduction ℓ (kanekoZagierSupersingularPoly l μ n)).map
        (algebraMap (ZMod ℓ) (AlgebraicClosure (ZMod ℓ)))).IsRoot j ↔
      ∃ z : AlgebraicClosure (ZMod ℓ), z ≠ 0 ∧ z ≠ 1 ∧
        256 * (z ^ 2 - z + 1) ^ 3 = j * (z ^ 2 * (z - 1) ^ 2) ∧
        ∑ i ∈ range (m + 1), ((m.choose i : ℕ) : AlgebraicClosure (ZMod ℓ)) ^ 2 * z ^ i = 0 := by
  have h5 : 5 ≤ ℓ := by
    have := (Fact.out : ℓ.Prime).two_le
    rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl <;> omega
  rw [kanekoZagier_isRoot_iff hKZ hl hμ n ℓ hℓ]
  exact mem_supersingularJ_iff_legendre hHasse ℓ m hm h5 j

end ArithmeticOfJacobiPolynomials
