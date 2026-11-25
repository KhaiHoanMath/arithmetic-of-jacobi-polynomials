/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Remarks.ModularForms
public import ArithmeticOfJacobiPolynomials.Jacobi.DifferentialEquation
public import Mathlib.NumberTheory.ModularForms.RamanujanFormula
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
public import ArithmeticOfJacobiPolynomials.Modular.JInvariant

/-!
# The Kaneko–Zagier differential equation for `F_k` (§6.4)

With `r = 2λ + 3μ`, `ℓ = 12n + 6 + r`, `a = (λ+1)/2`, `b = (μ+1)/2` and
`k = ℓ - 1 = 12n + 4a + 6b`, the "associated modular solution" of §6.4 is
`F_k = Δ^n E₄^a E₆^b F̃_{ℓ-1}(j)` (`kzModularForm`). "Solution" refers to the Kaneko–Zagier
differential equation ([KZ, §8, (24)])
`f'' - ((k+1)/6) E₂ f' + (k(k+1)/12) E₂' f = 0`, with `' = D = (2πi)⁻¹ d/dz = q d/dq`
(Mathlib's `normalizedDerivOfComplex`, Ramanujan's formulas `normalizedDerivOfComplex_E₂`,
`_E₄`, `_E₆`), equivalently `ϑ_{k+2} ϑ_k f = (k(k+2)/144) E₄ f` with Mathlib's Serre derivative
`ϑ_k f = D f - (k/12) E₂ f`. We prove:

* `kanekoZagierModularPoly_ode_eval`: the second order equation
  `6Y(Y - 1728) F̃'' + ((12 + 2λ + 3μ) Y - 3456(λ + 3)) F̃' - n(6n + 6 + 2λ + 3μ) F̃ = 0`
  satisfied by `F̃ = F̃_{ℓ-1}` in the variable `Y = j`, from the Jacobi equation (5.6)
  (`jacobiP_ode`) under `x = 1 - Y/864` (for all integers `λ, μ`);
* `normalizedDerivOfComplex_discriminant` (`D Δ = E₂ Δ`) and `normalizedDerivOfComplex_jInvariant`
  (`D j = -E₄² E₆/Δ`), from Ramanujan's formulas and `1728 Δ = E₄³ - E₆²`;
* `kzModularForm_kanekoZagier_ode`: **`F_k` satisfies the Kaneko–Zagier equation** for
  `λ, μ ∈ {-1, 1}`;
* `kzModularForm_serreDerivative`: the Serre form `ϑ_{k+2} ϑ_k F_k = (k(k+2)/144) E₄ F_k`.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial ModularForm UpperHalfPlane Derivative

open scoped MatrixGroups Manifold

local notation "Δ" => ModularForm.discriminant

/-! ### The equation for `F̃` in the variable `j` -/

/-- **The Kaneko–Zagier equation for `F̃_{ℓ-1}` in the variable `Y = j`.** For
`F̃(Y) = 1728^n P_n^{(λ/3,μ/2)}(1 - Y/864)`,
`6Y(Y - 1728) F̃'' + ((12 + 2λ + 3μ) Y - 3456(λ + 3)) F̃' - n(6n + 6 + 2λ + 3μ) F̃ = 0`
(the Jacobi equation (5.6) after the affine change of variable). -/
theorem kanekoZagierModularPoly_ode_eval (l μ : ℤ) (n : ℕ) (y : ℂ) :
    6 * y * (y - 1728) *
        (derivative (derivative ((kanekoZagierModularPoly l μ n).map (algebraMap ℚ ℂ)))).eval y +
      ((12 + 2 * l + 3 * μ) * y - 3456 * (l + 3)) *
        (derivative ((kanekoZagierModularPoly l μ n).map (algebraMap ℚ ℂ))).eval y -
      n * (6 * n + 6 + 2 * l + 3 * μ) *
        ((kanekoZagierModularPoly l μ n).map (algebraMap ℚ ℂ)).eval y = 0 := by
  obtain ⟨J, hJ⟩ : ∃ J : ℂ[X], J = (jacobiP ((l : ℚ) / 3) ((μ : ℚ) / 2) n).map (algebraMap ℚ ℂ) :=
    ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℂ[X], L = C (-1 / 864 : ℂ) * polyX + C 1 := ⟨_, rfl⟩
  have hP : (kanekoZagierModularPoly l μ n).map (algebraMap ℚ ℂ) =
      C ((1728 : ℂ) ^ n) * J.comp L := by
    rw [kanekoZagierModularPoly_eq, hJ, hL]
    simp [Polynomial.map_comp]
  have hL' : derivative L = C (-1 / 864 : ℂ) := by
    rw [hL, derivative_add, derivative_C_mul_X, derivative_C, add_zero]
  have hLy : L.eval y = -1 / 864 * y + 1 := by
    rw [hL]; simp
  have e0 : ((kanekoZagierModularPoly l μ n).map (algebraMap ℚ ℂ)).eval y =
      1728 ^ n * J.eval (L.eval y) := by
    rw [hP]; simp only [eval_mul, eval_C, eval_comp]
  have e1 : (derivative ((kanekoZagierModularPoly l μ n).map (algebraMap ℚ ℂ))).eval y =
      1728 ^ n * ((-1 / 864) * (derivative J).eval (L.eval y)) := by
    rw [hP, derivative_C_mul, derivative_comp, hL']
    simp only [eval_mul, eval_C, eval_comp]
  have e2 :
      (derivative (derivative ((kanekoZagierModularPoly l μ n).map (algebraMap ℚ ℂ)))).eval y =
        1728 ^ n * ((-1 / 864) * ((-1 / 864) *
          (derivative (derivative J)).eval (L.eval y))) := by
    rw [hP, derivative_C_mul, derivative_comp, hL', derivative_C_mul, derivative_C_mul,
      derivative_comp, hL']
    simp only [eval_mul, eval_C, eval_comp]
  have hode := congrArg (fun p => (p.map (algebraMap ℚ ℂ)).eval (L.eval y))
    (jacobiP_ode ((l : ℚ) / 3) ((μ : ℚ) / 2) n)
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.map_zero,
    ← derivative_map, ← hJ, eval_add, eval_mul, eval_sub, eval_one, eval_pow, eval_X, eval_C,
    eval_zero, eq_ratCast] at hode
  push_cast at hode
  rw [e0, e1, e2]
  rw [hLy] at hode ⊢
  linear_combination (-6 * (1728 : ℂ) ^ n) * hode

/-! ### Holomorphy and normalized derivatives -/

theorem mdifferentiable_E₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₄ : ℍ → ℂ) :=
  ModularFormClass.holo E₄

theorem mdifferentiable_E₆ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₆ : ℍ → ℂ) :=
  ModularFormClass.holo E₆

theorem mdifferentiable_discriminant : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Δ := by
  rw [← coe_deltaForm]; exact ModularFormClass.holo deltaForm

theorem mdifferentiable_inv_discriminant : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Δ⁻¹ :=
  fun z => (mdifferentiable_discriminant z).inv (discriminant_ne_zero z)

theorem mdifferentiable_eval_comp (p : ℂ[X]) {h : ℍ → ℂ} (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => p.eval (h z)) :=
  p.differentiable.comp_mdifferentiable hh

/-- Product rule for `D`, pointwise. -/
theorem normalizedDerivOfComplex_mul_apply {F G : ℍ → ℂ} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) (z : ℍ) :
    D (F * G) z = D F z * G z + F z * D G z := by
  simp only [normalizedDerivOfComplex_mul F G hF hG, Pi.add_apply, Pi.mul_apply]

/-- Leibniz rule for `D²`, pointwise. -/
theorem normalizedDerivOfComplex_two_mul_apply {F G : ℍ → ℂ}
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) (z : ℍ) :
    D (D (F * G)) z = D (D F) z * G z + 2 * (D F z * D G z) + F z * D (D G) z := by
  have hDF := normalizedDerivOfComplex_mdifferentiable hF
  have hDG := normalizedDerivOfComplex_mdifferentiable hG
  rw [normalizedDerivOfComplex_mul F G hF hG,
    normalizedDerivOfComplex_add _ _ (hDF.mul hG) (hF.mul hDG),
    normalizedDerivOfComplex_mul _ _ hDF hG, normalizedDerivOfComplex_mul _ _ hF hDG]
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

/-- Chain rule for `D` and a polynomial. -/
theorem normalizedDerivOfComplex_eval_comp (p : ℂ[X]) {h : ℍ → ℂ}
    (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) :
    D (fun z => p.eval (h z)) = fun z => (derivative p).eval (h z) * D h z := by
  refine Polynomial.induction_on' p (fun p q hp hq => ?_) (fun m a => ?_)
  · have hsum : (fun z => (p + q).eval (h z)) =
        (fun z => p.eval (h z)) + fun z => q.eval (h z) := by
      funext z; simp only [eval_add, Pi.add_apply]
    rw [hsum, normalizedDerivOfComplex_add _ _ (mdifferentiable_eval_comp p hh)
      (mdifferentiable_eval_comp q hh), hp, hq]
    funext z
    simp only [Pi.add_apply, derivative_add, eval_add]
    ring
  · have hmon : (fun z => (monomial m a).eval (h z)) = a • h ^ m := by
      funext z; simp only [eval_monomial, Pi.smul_apply, Pi.pow_apply, smul_eq_mul]
    rw [hmon, normalizedDerivOfComplex_smul _ _ (hh.pow m), normalizedDerivOfComplex_pow _ m hh]
    funext z
    simp only [Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, smul_eq_mul,
      derivative_monomial, eval_monomial]
    ring

theorem normalizedDerivOfComplex_eval_comp_apply (p : ℂ[X]) {h : ℍ → ℂ}
    (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) (z : ℍ) :
    D (fun z => p.eval (h z)) z = (derivative p).eval (h z) * D h z := by
  rw [normalizedDerivOfComplex_eval_comp p hh]

theorem normalizedDerivOfComplex_two_eval_comp_apply (p : ℂ[X]) {h : ℍ → ℂ}
    (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) (z : ℍ) :
    D (D (fun z => p.eval (h z))) z =
      (derivative (derivative p)).eval (h z) * D h z * D h z +
        (derivative p).eval (h z) * D (D h) z := by
  have hDh := normalizedDerivOfComplex_mdifferentiable hh
  rw [normalizedDerivOfComplex_eval_comp p hh,
    show (fun z => (derivative p).eval (h z) * D h z) =
      (fun z => (derivative p).eval (h z)) * D h from rfl,
    normalizedDerivOfComplex_mul_apply (mdifferentiable_eval_comp _ hh) hDh,
    normalizedDerivOfComplex_eval_comp _ hh]

/-- `D(F^a) = a D F` for `a ∈ {0, 1}`. -/
theorem normalizedDerivOfComplex_pow_of_le_one {F : ℍ → ℂ} {a : ℕ} (ha : a ≤ 1) :
    D (F ^ a) = (a : ℂ) • D F := by
  interval_cases a
  · rw [pow_zero, Nat.cast_zero, zero_smul]; exact normalizedDerivOfComplex_const 1
  · rw [pow_one, Nat.cast_one, one_smul]

theorem normalizedDerivOfComplex_pow_of_le_one_apply (F : ℍ → ℂ) {a : ℕ} (ha : a ≤ 1)
    (z : ℍ) : D (F ^ a) z = a * D F z := by
  rw [normalizedDerivOfComplex_pow_of_le_one ha, Pi.smul_apply, smul_eq_mul]

theorem normalizedDerivOfComplex_two_pow_of_le_one_apply {F : ℍ → ℂ}
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) {a : ℕ} (ha : a ≤ 1) (z : ℍ) :
    D (D (F ^ a)) z = a * D (D F) z := by
  rw [normalizedDerivOfComplex_pow_of_le_one ha,
    normalizedDerivOfComplex_smul _ _ (normalizedDerivOfComplex_mdifferentiable hF),
    Pi.smul_apply, smul_eq_mul]

/-! ### Ramanujan's formulas, pointwise -/

theorem normalizedDerivOfComplex_E₂_apply (z : ℍ) :
    D EisensteinSeries.E2 z = (EisensteinSeries.E2 z ^ 2 - E₄ z) / 12 := by
  rw [normalizedDerivOfComplex_E₂]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.pow_apply, smul_eq_mul]
  ring

theorem normalizedDerivOfComplex_E₄_apply (z : ℍ) :
    D E₄ z = (EisensteinSeries.E2 z * E₄ z - E₆ z) / 3 := by
  rw [normalizedDerivOfComplex_E₄]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul]
  ring

theorem normalizedDerivOfComplex_E₆_apply (z : ℍ) :
    D E₆ z = (EisensteinSeries.E2 z * E₆ z - E₄ z ^ 2) / 2 := by
  rw [normalizedDerivOfComplex_E₆]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
  ring

theorem normalizedDerivOfComplex_two_E₄_apply (z : ℍ) :
    D (D E₄) z = (D EisensteinSeries.E2 z * E₄ z + EisensteinSeries.E2 z * D E₄ z -
      D E₆ z) / 3 := by
  have h24 := E2_mdifferentiable.mul mdifferentiable_E₄
  conv_lhs => rw [normalizedDerivOfComplex_E₄]
  rw [normalizedDerivOfComplex_smul _ _ (h24.sub mdifferentiable_E₆),
    normalizedDerivOfComplex_sub _ _ h24 mdifferentiable_E₆,
    normalizedDerivOfComplex_mul _ _ E2_mdifferentiable mdifferentiable_E₄]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul]
  ring

theorem normalizedDerivOfComplex_two_E₆_apply (z : ℍ) :
    D (D E₆) z = (D EisensteinSeries.E2 z * E₆ z + EisensteinSeries.E2 z * D E₆ z -
      2 * E₄ z * D E₄ z) / 2 := by
  have h26 := E2_mdifferentiable.mul mdifferentiable_E₆
  have h44 := mdifferentiable_E₄.mul mdifferentiable_E₄
  conv_lhs => rw [normalizedDerivOfComplex_E₆, pow_two]
  rw [normalizedDerivOfComplex_smul _ _ (h26.sub h44),
    normalizedDerivOfComplex_sub _ _ h26 h44,
    normalizedDerivOfComplex_mul _ _ E2_mdifferentiable mdifferentiable_E₆,
    normalizedDerivOfComplex_mul _ _ mdifferentiable_E₄ mdifferentiable_E₄]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-! ### The discriminant and the `j`-invariant -/

/-- **`D Δ = E₂ Δ`**, from `1728 Δ = E₄³ - E₆²` and Ramanujan's formulas. -/
theorem normalizedDerivOfComplex_discriminant : D Δ = EisensteinSeries.E2 * Δ := by
  have h4 := mdifferentiable_E₄
  have h6 := mdifferentiable_E₆
  have h44 := h4.mul h4
  have h444 := h44.mul h4
  have h66 := h6.mul h6
  have hfun : Δ = (1728⁻¹ : ℂ) • ((E₄ : ℍ → ℂ) * E₄ * E₄ - (E₆ : ℍ → ℂ) * E₆) := by
    funext z
    rw [discriminant_eq_E₄_cube_sub_E₆_sq]
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul]
    ring
  conv_lhs => rw [hfun]
  rw [normalizedDerivOfComplex_smul _ _ (h444.sub h66),
    normalizedDerivOfComplex_sub _ _ h444 h66, normalizedDerivOfComplex_mul _ _ h44 h4,
    normalizedDerivOfComplex_mul _ _ h4 h4, normalizedDerivOfComplex_mul _ _ h6 h6,
    normalizedDerivOfComplex_E₄, normalizedDerivOfComplex_E₆]
  funext z
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
  rw [discriminant_eq_E₄_cube_sub_E₆_sq]
  ring

/-- `D (1/Δ) = -E₂/Δ`. -/
theorem normalizedDerivOfComplex_inv_discriminant :
    D Δ⁻¹ = -(EisensteinSeries.E2 * Δ⁻¹) := by
  have h := normalizedDerivOfComplex_mul Δ Δ⁻¹ mdifferentiable_discriminant
    mdifferentiable_inv_discriminant
  have h1 : Δ * Δ⁻¹ = 1 := by
    funext z
    rw [Pi.mul_apply, Pi.inv_apply, Pi.one_apply, mul_inv_cancel₀ (discriminant_ne_zero z)]
  have h0 : D (1 : ℍ → ℂ) = 0 := normalizedDerivOfComplex_const 1
  rw [h1, h0, normalizedDerivOfComplex_discriminant] at h
  funext z
  have hz := congrFun h z
  have hw : Δ z * (Δ z)⁻¹ = 1 := mul_inv_cancel₀ (discriminant_ne_zero z)
  simp only [Pi.zero_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.inv_apply] at hz ⊢
  linear_combination (-(Δ z)⁻¹) * hz - (D Δ⁻¹ z + EisensteinSeries.E2 z * (Δ z)⁻¹) * hw

theorem normalizedDerivOfComplex_discriminant_pow_apply (n : ℕ) (z : ℍ) :
    D (Δ ^ n) z = n * EisensteinSeries.E2 z * Δ z ^ n := by
  rw [normalizedDerivOfComplex_pow _ n mdifferentiable_discriminant,
    normalizedDerivOfComplex_discriminant]
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply]
  cases n with
  | zero => simp
  | succ m => rw [Nat.add_sub_cancel, pow_succ]; ring

theorem normalizedDerivOfComplex_discriminant_pow (n : ℕ) :
    D (Δ ^ n) = (n : ℂ) • (EisensteinSeries.E2 * Δ ^ n) := by
  funext z
  rw [normalizedDerivOfComplex_discriminant_pow_apply]
  simp only [Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
  ring

theorem normalizedDerivOfComplex_two_discriminant_pow_apply (n : ℕ) (z : ℍ) :
    D (D (Δ ^ n)) z = n * (D EisensteinSeries.E2 z * Δ z ^ n +
      EisensteinSeries.E2 z * (n * EisensteinSeries.E2 z * Δ z ^ n)) := by
  have hN := mdifferentiable_discriminant.pow n
  rw [normalizedDerivOfComplex_discriminant_pow,
    normalizedDerivOfComplex_smul _ _ (E2_mdifferentiable.mul hN), Pi.smul_apply,
    normalizedDerivOfComplex_mul_apply E2_mdifferentiable hN,
    normalizedDerivOfComplex_discriminant_pow_apply, smul_eq_mul, Pi.pow_apply]

theorem jInvariant_eq_mul : jInvariant = (E₄ : ℍ → ℂ) * E₄ * E₄ * Δ⁻¹ := by
  funext z
  simp only [jInvariant_apply, Pi.mul_apply, Pi.inv_apply]
  ring

theorem mdifferentiable_jInvariant : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jInvariant := by
  rw [jInvariant_eq_mul]
  exact ((mdifferentiable_E₄.mul mdifferentiable_E₄).mul mdifferentiable_E₄).mul
    mdifferentiable_inv_discriminant

/-- **`D j = -E₄² E₆/Δ`.** -/
theorem normalizedDerivOfComplex_jInvariant :
    D jInvariant = -((E₄ : ℍ → ℂ) * E₄ * E₆ * Δ⁻¹) := by
  have h4 := mdifferentiable_E₄
  have h44 := h4.mul h4
  rw [jInvariant_eq_mul,
    normalizedDerivOfComplex_mul _ _ (h44.mul h4) mdifferentiable_inv_discriminant,
    normalizedDerivOfComplex_mul _ _ h44 h4, normalizedDerivOfComplex_mul _ _ h4 h4,
    normalizedDerivOfComplex_inv_discriminant, normalizedDerivOfComplex_E₄]
  funext z
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply,
    Pi.inv_apply, smul_eq_mul]
  ring

theorem normalizedDerivOfComplex_jInvariant_apply (z : ℍ) :
    D jInvariant z = -(E₄ z ^ 2 * E₆ z * (Δ z)⁻¹) := by
  rw [normalizedDerivOfComplex_jInvariant]
  simp only [Pi.neg_apply, Pi.mul_apply, Pi.inv_apply]
  ring

theorem normalizedDerivOfComplex_two_jInvariant_apply (z : ℍ) :
    D (D jInvariant) z = -(2 * E₄ z * D E₄ z * E₆ z * (Δ z)⁻¹ +
      E₄ z ^ 2 * D E₆ z * (Δ z)⁻¹ +
        E₄ z ^ 2 * E₆ z * (-(EisensteinSeries.E2 z * (Δ z)⁻¹))) := by
  have h4 := mdifferentiable_E₄
  have h6 := mdifferentiable_E₆
  have h44 := h4.mul h4
  have h446 := h44.mul h6
  rw [normalizedDerivOfComplex_jInvariant,
    normalizedDerivOfComplex_neg _ (h446.mul mdifferentiable_inv_discriminant), Pi.neg_apply,
    normalizedDerivOfComplex_mul_apply h446 mdifferentiable_inv_discriminant,
    normalizedDerivOfComplex_mul_apply h44 h6, normalizedDerivOfComplex_mul_apply h4 h4,
    normalizedDerivOfComplex_inv_discriminant]
  simp only [Pi.mul_apply, Pi.neg_apply, Pi.inv_apply]
  ring

/-! ### The Kaneko–Zagier equation for `F_k` -/

/-- **§6.4: `F_k` is a solution of the Kaneko–Zagier equation.** For `λ, μ ∈ {-1, 1}`,
`a = (λ+1)/2`, `b = (μ+1)/2` and `k = 12n + 4a + 6b`, the modular form
`F_k = Δ^n E₄^a E₆^b F̃_{ℓ-1}(j)` satisfies
`D²F_k - ((k+1)/6) E₂ D F_k + (k(k+1)/12) (D E₂) F_k = 0`, `D = (2πi)⁻¹ d/dz = q d/dq`
([KZ, §8, (24)]). -/
theorem kzModularForm_kanekoZagier_ode {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (n a b : ℕ) (ha : (a : ℤ) = (l + 1) / 2) (hb : (b : ℤ) = (μ + 1) / 2) (z : ℍ) :
    D (D (kzModularForm l μ n a b)) z -
        (12 * (n : ℂ) + 4 * a + 6 * b + 1) / 6 * EisensteinSeries.E2 z *
          D (kzModularForm l μ n a b) z +
      (12 * (n : ℂ) + 4 * a + 6 * b) * (12 * n + 4 * a + 6 * b + 1) / 12 *
        D EisensteinSeries.E2 z * kzModularForm l μ n a b z = 0 := by
  have ha1 : a ≤ 1 := by rcases hl with rfl | rfl <;> omega
  have hb1 : b ≤ 1 := by rcases hμ with rfl | rfl <;> omega
  obtain ⟨P, hP⟩ : ∃ P : ℂ[X], P = (kanekoZagierModularPoly l μ n).map (algebraMap ℚ ℂ) :=
    ⟨_, rfl⟩
  have hE4 := mdifferentiable_E₄
  have hE6 := mdifferentiable_E₆
  have hN := mdifferentiable_discriminant.pow n
  have hA := hE4.pow a
  have hB := hE6.pow b
  have hG := hA.mul hB
  have hH := hN.mul hG
  have hj := mdifferentiable_jInvariant
  have hPj := mdifferentiable_eval_comp P hj
  have hF : ⇑(kzModularForm l μ n a b) =
      Δ ^ n * ((E₄ : ℍ → ℂ) ^ a * (E₆ : ℍ → ℂ) ^ b) * fun z => P.eval (jInvariant z) := by
    funext z
    rw [kzModularForm_apply hμ, ← hP]
    simp only [Pi.mul_apply, Pi.pow_apply, jInvariant_apply]
    ring
  rw [hF, normalizedDerivOfComplex_two_mul_apply hH hPj, normalizedDerivOfComplex_mul_apply hH hPj,
    normalizedDerivOfComplex_two_mul_apply hN hG, normalizedDerivOfComplex_mul_apply hN hG,
    normalizedDerivOfComplex_two_mul_apply hA hB, normalizedDerivOfComplex_mul_apply hA hB,
    normalizedDerivOfComplex_two_eval_comp_apply P hj,
    normalizedDerivOfComplex_eval_comp_apply P hj,
    normalizedDerivOfComplex_two_discriminant_pow_apply,
    normalizedDerivOfComplex_discriminant_pow_apply,
    normalizedDerivOfComplex_two_pow_of_le_one_apply hE4 ha1,
    normalizedDerivOfComplex_pow_of_le_one_apply _ ha1,
    normalizedDerivOfComplex_two_pow_of_le_one_apply hE6 hb1,
    normalizedDerivOfComplex_pow_of_le_one_apply _ hb1,
    normalizedDerivOfComplex_two_jInvariant_apply, normalizedDerivOfComplex_jInvariant_apply,
    normalizedDerivOfComplex_two_E₄_apply, normalizedDerivOfComplex_two_E₆_apply,
    normalizedDerivOfComplex_E₂_apply, normalizedDerivOfComplex_E₄_apply,
    normalizedDerivOfComplex_E₆_apply]
  simp only [Pi.mul_apply, Pi.pow_apply]
  have hODE := kanekoZagierModularPoly_ode_eval l μ n (jInvariant z)
  rw [← hP] at hODE
  have hne := discriminant_ne_zero z
  have h1728 : E₄ z ^ 3 - E₆ z ^ 2 = 1728 * Δ z := by
    rw [discriminant_eq_E₄_cube_sub_E₆_sq]; ring
  have hw : (E₄ z ^ 3 - E₆ z ^ 2) * (Δ z)⁻¹ = 1728 := by
    rw [h1728, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  generalize (derivative (derivative P)).eval (jInvariant z) = p2 at hODE ⊢
  generalize (derivative P).eval (jInvariant z) = p1 at hODE ⊢
  generalize P.eval (jInvariant z) = p0 at hODE ⊢
  rw [jInvariant_apply, div_eq_mul_inv] at hODE
  generalize Δ z ^ n = N at ⊢
  generalize (Δ z)⁻¹ = w at hODE hw ⊢
  generalize EisensteinSeries.E2 z = e2 at ⊢
  generalize E₄ z = e4 at hODE hw ⊢
  generalize E₆ z = e6 at hw ⊢
  rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl
  · obtain rfl : a = 1 := by omega
    obtain rfl : b = 1 := by omega
    simp only [Nat.cast_one, Int.cast_one] at hODE ⊢
    linear_combination (e4 * N * e4 * e6 / 6) * hODE +
      (-(N * e4 ^ 2 * e6 * (3 * e4 ^ 3 * p2 * w + 4 * p1) / 3)) * hw
  · obtain rfl : a = 1 := by omega
    obtain rfl : b = 0 := by omega
    simp only [Nat.cast_one, Nat.cast_zero, Int.cast_one, Int.cast_neg] at hODE ⊢
    linear_combination (e4 * N * e4 / 6) * hODE +
      (-(N * e4 ^ 2 * (3 * e4 ^ 3 * p2 * w + 4 * p1) / 3)) * hw
  · obtain rfl : a = 0 := by omega
    obtain rfl : b = 1 := by omega
    simp only [Nat.cast_one, Nat.cast_zero, Int.cast_one, Int.cast_neg] at hODE ⊢
    linear_combination (e4 * N * e6 / 6) * hODE +
      (-(N * e4 * e6 * (3 * e4 ^ 3 * p2 * w + 2 * p1) / 3)) * hw
  · obtain rfl : a = 0 := by omega
    obtain rfl : b = 0 := by omega
    simp only [Nat.cast_zero, Int.cast_one, Int.cast_neg] at hODE ⊢
    linear_combination (e4 * N / 6) * hODE +
      (-(N * e4 * (3 * e4 ^ 3 * p2 * w + 2 * p1) / 3)) * hw

/-- `ϑ_{k+2} ϑ_k F = D²F - ((k+1)/6) E₂ DF + (k(k+1)/12) (D E₂) F + (k(k+2)/144) E₄ F`, with
Mathlib's Serre derivative `ϑ_k F = D F - (k/12) E₂ F`. -/
theorem serreDerivative_serreDerivative_apply {F : ℍ → ℂ} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (k : ℂ) (z : ℍ) :
    serreDerivative (k + 2) (serreDerivative k F) z =
      D (D F) z - (k + 1) / 6 * EisensteinSeries.E2 z * D F z +
        k * (k + 1) / 12 * D EisensteinSeries.E2 z * F z + k * (k + 2) / 144 * E₄ z * F z := by
  have hE2F := E2_mdifferentiable.mul hF
  have hDF := normalizedDerivOfComplex_mdifferentiable hF
  have hS : serreDerivative k F = D F - (k * 12⁻¹ : ℂ) • (EisensteinSeries.E2 * F) := by
    funext w
    rw [serreDerivative_apply]
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  rw [serreDerivative_apply, hS, normalizedDerivOfComplex_sub _ _ hDF (hE2F.const_smul _),
    normalizedDerivOfComplex_smul _ _ hE2F, normalizedDerivOfComplex_mul _ _ E2_mdifferentiable hF,
    normalizedDerivOfComplex_E₂]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, smul_eq_mul]
  ring

/-- **§6.4, Serre form.** With `k = 12n + 4a + 6b`, `ϑ_{k+2} ϑ_k F_k = (k(k+2)/144) E₄ F_k`. -/
theorem kzModularForm_serreDerivative {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (n a b : ℕ) (ha : (a : ℤ) = (l + 1) / 2) (hb : (b : ℤ) = (μ + 1) / 2) (z : ℍ) :
    serreDerivative ((12 * n + 4 * a + 6 * b : ℂ) + 2)
        (serreDerivative (12 * n + 4 * a + 6 * b : ℂ) (kzModularForm l μ n a b)) z =
      (12 * (n : ℂ) + 4 * a + 6 * b) * (12 * n + 4 * a + 6 * b + 2) / 144 * E₄ z *
        kzModularForm l μ n a b z := by
  have h1 := serreDerivative_serreDerivative_apply (ModularFormClass.holo (kzModularForm l μ n a b))
    (12 * n + 4 * a + 6 * b : ℂ) z
  have h2 := kzModularForm_kanekoZagier_ode hl hμ n a b ha hb z
  linear_combination h1 + h2

end ArithmeticOfJacobiPolynomials
