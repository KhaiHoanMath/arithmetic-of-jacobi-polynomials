/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.Divisors.Degree
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.WeilDivisorClass
public import StacksFrontier.AlgebraicGeometry.Divisors.RationalFunctionWeilDivisor

/-!
# Linear equivalence of effective Cartier divisors through orders of a rational function

Let `X` be a normal Noetherian integral scheme (for instance a smooth curve over a field) and
`D`, `D'` effective Cartier divisors ([Stacks, Tag 01WR (2)]) given by ideal sheaves. The library
proves

* `Stacks.Divisors.linearlyEquivalent_iff_weilDivisorClass_eq_of_isNormal` (untagged): `D` and
  `D'` are linearly equivalent (`Stacks.Divisors.LinearlyEquivalent D D'`, which is `𝒪_X(D) ≅
  𝒪_X(D')` and carries `@[stacks 0CCT]` as the *definition*) iff their Weil divisors `[D]`,
  `[D']` (`AlgebraicGeometry.effectiveCartierWeilDivisor`, `@[stacks 02AR]` part (5)) have the
  same class in `AlgebraicGeometry.weilDivisorClassGroup` (`@[stacks 0BE4]`). It rests on the
  injectivity `Pic(X) → Cl(X)` of `@[stacks 0BE8]` (`[IsNormal X]`).
* `Stacks.Divisors.linearlyEquivalent_iff_weilDivisorClass_eq`, the declaration that carries the
  tag `@[stacks 0CCT]` for this equivalence, is stated only for a smooth projective curve over an
  algebraically closed field; the statement used here is the more general normal-scheme one.

This file only unfolds that class equality into the concrete statement used in computations: the
coefficients of `[D']` and `[D]` differ by the orders of one rational function.

## Main results

* `ArithmeticOfJacobiPolynomials.Divisors.effectiveCartierWeilDivisor_apply_eq_ord`: the
coefficient of `[D]` at a
  prime divisor `Z` is the order of vanishing, at the generic point of `Z`, of *any* generator of
  the ideal that `D` induces in the local ring there.
* `ArithmeticOfJacobiPolynomials.Divisors.linearlyEquivalent_iff_exists_ord`: on a normal
Noetherian integral
  scheme, `D ∼ D'` iff there is a rational function `φ` with `[D'] = [D] + div φ`
  coefficientwise.
*
`ArithmeticOfJacobiPolynomials.Divisors.linearlyEquivalent_iff_exists_rationalFunctionWeilDivisor`:
the same
  as an equation in `AlgebraicGeometry.WeilDivisor X`, with
  `AlgebraicGeometry.rationalFunctionWeilDivisor X φ`.
*
`Divisors.weilDivisorDegree_effectiveCartierWeilDivisor_eq_of_linearlyEquivalent`:
  linearly equivalent effective Cartier divisors on a proper normal curve have the same degree
  (Stacks 02RU applied to `φ`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace Divisors

open AlgebraicGeometry CategoryTheory

universe u

variable {X : Scheme.{u}}

section

variable [IsNoetherian X] [IsIntegral X]

/-- **The coefficient of `[D]` at `Z` is the order of any local generator of `D`.** If `c`
generates the ideal that the effective Cartier divisor `D` induces in the local ring at the
generic point of the prime divisor `Z`, the coefficient of `Weil(D)` at `Z` is the order of
vanishing at that point of `c`, read in the function field ([Stacks, Tag 02AR (5)]). -/
theorem effectiveCartierWeilDivisor_apply_eq_ord (I : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (Z : PrimeDivisor X)
    {c : X.presheaf.stalk Z.genericPoint}
    (hc : IdealSheafData.stalk I Z.genericPoint = Ideal.span {c}) :
    (effectiveCartierWeilDivisor I hI).1 Z =
      X.ord (algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField c)
        Z.genericPoint := by
  obtain ⟨g, hg, hgreg⟩ := exists_stalk_eq_span_of_isEffectiveCartierDivisor hI Z.genericPoint
  have hassoc : Associated c g := by
    rw [← Ideal.span_singleton_eq_span_singleton, ← hc, hg]
  have hcreg : c ∈ nonZeroDivisors (X.presheaf.stalk Z.genericPoint) := by
    obtain ⟨u, rfl⟩ := hassoc.symm
    exact mul_mem_nonZeroDivisors.mpr ⟨hgreg, u.isUnit.mem_nonZeroDivisors⟩
  rw [effectiveCartierWeilDivisor_apply_of_stalk_eq_span I hI Z c hc,
    ord_algebraMap_eq_length_quotient Z hcreg]

/-- The same coefficient, when `D` is cut out by `f` on an affine open `U` containing the generic
point of `Z`: it is the order of vanishing, at that point, of the image of the germ of `f` in the
function field. -/
theorem effectiveCartierWeilDivisor_apply_eq_ord_of_ideal_eq_span (I : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (Z : PrimeDivisor X) {U : X.affineOpens}
    (hxU : Z.genericPoint ∈ U.1) {f : Γ(X, U.1)} (hf : I.ideal U = Ideal.span {f}) :
    (effectiveCartierWeilDivisor I hI).1 Z =
      X.ord (algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField
        ((X.presheaf.germ U.1 Z.genericPoint hxU).hom f)) Z.genericPoint :=
  effectiveCartierWeilDivisor_apply_eq_ord I hI Z
    (IdealSheafData.stalk_eq_span_germ_of_ideal_eq_span hxU hf)

/-- **Linear equivalence of effective Cartier divisors is a rational function with the right
orders** (the normal-scheme class equality unfolded; see the module docstring on 0CCT). On a
normal Noetherian integral scheme, `𝒪_X(D) ≅ 𝒪_X(D')` iff there is a unit `φ` of the function
field with `[D'] Z = [D] Z + ord_Z φ` for every prime divisor `Z`. -/
theorem linearlyEquivalent_iff_exists_ord [IsNormal X] (D D' : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hD' : Stacks.Divisors.IsEffectiveCartierDivisor D') :
    Stacks.Divisors.LinearlyEquivalent D D' ↔
      ∃ φ : X.functionFieldˣ, ∀ Z : PrimeDivisor X,
        (effectiveCartierWeilDivisor D' hD').1 Z =
          (effectiveCartierWeilDivisor D hD).1 Z + X.ord (φ : X.functionField) Z.genericPoint := by
  rw [Stacks.Divisors.linearlyEquivalent_iff_weilDivisorClass_eq_of_isNormal D D' (hD := hD)
    (hD' := hD'), QuotientAddGroup.eq]
  set e := (Stacks.Chow.rationalFunctionsEquivFunctionField X).val with he
  have h1 : ∀ (A B : WeilDivisor X) (Z : PrimeDivisor X),
      (-A + B).1 Z = -(A.1 Z) + B.1 Z := fun _ _ _ => rfl
  constructor
  · rintro ⟨f, hf⟩
    rw [principalDivisor_eq_rationalFunctionWeilDivisor] at hf
    refine ⟨Units.map e.toMonoidHom f, fun Z => ?_⟩
    have hZ := congrArg (fun E : WeilDivisor X => E.1 Z) hf
    rw [h1, rationalFunctionWeilDivisor_apply] at hZ
    rw [he]
    omega
  · rintro ⟨φ, hφ⟩
    have hφe : Units.map e.toMonoidHom (Units.map e.symm.toMonoidHom φ) = φ :=
      Units.ext (e.apply_symm_apply _)
    refine ⟨Units.map e.symm.toMonoidHom φ, Subtype.ext (funext fun Z => ?_)⟩
    rw [principalDivisor_eq_rationalFunctionWeilDivisor, hφe, rationalFunctionWeilDivisor_apply]
    rw [h1]
    have := hφ Z
    omega

/-- **Linear equivalence of effective Cartier divisors as an equation of Weil divisors**
(the normal-scheme class equality unfolded): `[D'] = [D] + div φ` in
`AlgebraicGeometry.WeilDivisor X`. -/
theorem linearlyEquivalent_iff_exists_rationalFunctionWeilDivisor [IsNormal X]
    (D D' : X.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hD' : Stacks.Divisors.IsEffectiveCartierDivisor D') :
    Stacks.Divisors.LinearlyEquivalent D D' ↔
      ∃ φ : X.functionFieldˣ, effectiveCartierWeilDivisor D' hD' =
        effectiveCartierWeilDivisor D hD + rationalFunctionWeilDivisor X φ := by
  rw [linearlyEquivalent_iff_exists_ord D D' hD hD']
  refine exists_congr fun φ => ⟨fun h => Subtype.ext (funext fun Z => h Z), fun h Z => ?_⟩
  exact congrFun (congrArg Subtype.val h) Z

end

section

variable [IsNoetherian X]

/-- **Linearly equivalent effective Cartier divisors on a proper normal curve have the same
degree.** -/
theorem weilDivisorDegree_effectiveCartierWeilDivisor_eq_of_linearlyEquivalent {k : Type u}
    [Field k] [IsNormal X] (π : X ⟶ Spec (CommRingCat.of k)) [IsCurve k π] [IsProper π]
    (D D' : X.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hD' : Stacks.Divisors.IsEffectiveCartierDivisor D')
    (h : Stacks.Divisors.LinearlyEquivalent D D') :
    weilDivisorDegree π (effectiveCartierWeilDivisor D hD) =
      weilDivisorDegree π (effectiveCartierWeilDivisor D' hD') := by
  obtain ⟨φ, hφ⟩ := (linearlyEquivalent_iff_exists_rationalFunctionWeilDivisor D D' hD hD').mp h
  rw [hφ, map_add, weilDivisorDegree_rationalFunctionWeilDivisor_eq_zero π φ, add_zero]

end

end Divisors

end ArithmeticOfJacobiPolynomials
