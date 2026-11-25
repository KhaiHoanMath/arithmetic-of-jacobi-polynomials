/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.Divisors.Weil
public import StacksFrontier.AlgebraicGeometry.Properties.NormalCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Properties.NormalStalkDvr

/-!
# Rational functions with effective divisor are regular: global form of algebraic Hartogs

The library proves *algebraic Hartogs at a point* for a normal locally Noetherian integral scheme
(`AlgebraicGeometry.Scheme.mem_range_algebraMap_stalk_of_forall_zero_le_ord`): a non-zero element
of the function field whose order of vanishing is `≥ 0` at all codimension-one points
specializing to `x` lies in the local ring at `x`; and it proves the gluing step
(`AlgebraicGeometry.Scheme.exists_globalSection_of_forall_mem_range_stalk`: an element of the
function field lying in every local ring is a global section). For global sections it only states
the case `ord = 0`
(`Stacks.AlgebraicGeometry.UnitsNormalProper.exists_globalSection_of_forall_ord_eq_zero`).
This file records the combination with `ord ≥ 0`, which the library lacks, in the language of
`AlgebraicGeometry.WeilDivisor`, and the consequence for schemes with `Γ(X, ⊤)` a field.

The hypothesis is `IsNormal X`. For a scheme of dimension `≤ 1` known only to
have DVR local rings at codimension one, `isNormal_of_coheight_le_one_of_dvr` produces `IsNormal`.

## Main results

* `ArithmeticOfJacobiPolynomials.Divisors.exists_germ_eq_of_forall_zero_le_ord`: `f ≠ 0` with
`ord_y f ≥ 0` at
  all `y` of coheight one is a global section (normal, locally Noetherian, integral).
* `ArithmeticOfJacobiPolynomials.Divisors.exists_germ_eq_of_rationalFunctionWeilDivisor_nonneg` and
  `…_of_principalDivisor_nonneg`: the same for the Weil divisor being effective.
* `ArithmeticOfJacobiPolynomials.Divisors.rationalFunctionWeilDivisor_eq_zero_iff_of_isField` and
  `ArithmeticOfJacobiPolynomials.Divisors.exists_eq_const_of_rationalFunctionWeilDivisor_eq_zero`:
  if `Γ(X, ⊤)`
  is a field (e.g. `X` proper and integral over a field,
  `Scheme.isField_globalSections_of_isProper`), `div f = 0` iff `f` is constant.
* `ArithmeticOfJacobiPolynomials.Divisors.isNormal_of_coheight_le_one_of_dvr`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Divisors

variable {X : Scheme.{u}} [IsIntegral X]

/-- **A scheme of dimension `≤ 1` with DVR local rings at its codimension-one points is normal.**
(The local ring at the generic point is the function field.) -/
theorem isNormal_of_coheight_le_one_of_dvr (hdim : ∀ z : X, Order.coheight z ≤ 1)
    (hdvr : ∀ z : X, Order.coheight z = 1 → IsDiscreteValuationRing (X.presheaf.stalk z)) :
    IsNormal X where
  stalk_isDomain x := inferInstance
  stalk_normal x := by
    rcases Order.le_one_iff.mp (hdim x) with h0 | h1
    · have hmax : IsMax x := Order.coheight_eq_zero.mp h0
      have hηx : genericPoint X ⤳ x := (genericPoint_spec X).specializes (Set.mem_univ x)
      have hxη : x ⤳ genericPoint X :=
        Scheme.le_iff_specializes.mp (hmax (Scheme.le_iff_specializes.mpr hηx))
      have hx : x = genericPoint X := (hxη.antisymm hηx).eq
      subst hx
      exact inferInstanceAs (IsIntegrallyClosed X.functionField)
    · have := hdvr x h1
      infer_instance

section

variable [IsLocallyNoetherian X] [IsNormal X]

/-- **Global algebraic Hartogs with `ord ≥ 0`.** On a normal locally Noetherian integral scheme, a
non-zero rational function whose order of vanishing is `≥ 0` at every point of coheight one is the
germ at the generic point of a global section. -/
theorem exists_germ_eq_of_forall_zero_le_ord {f : X.functionField} (hf : f ≠ 0)
    (h : ∀ y : X, Order.coheight y = 1 → 0 ≤ X.ord f y) :
    ∃ s : Γ(X, ⊤), X.presheaf.germ ⊤ (genericPoint X) trivial s = f :=
  Scheme.exists_globalSection_of_forall_mem_range_stalk fun x =>
    Scheme.mem_range_algebraMap_stalk_of_forall_zero_le_ord x hf fun y hy _ => h y hy

/-- If the principal divisor of a rational function is effective, the function is a global
section. -/
theorem exists_germ_eq_of_principalDivisor_nonneg (f : (Stacks.Chow.rationalFunctions X)ˣ)
    (h : ∀ Z : PrimeDivisor X, 0 ≤ (principalDivisor X f).1 Z) :
    ∃ s : Γ(X, ⊤), X.presheaf.germ ⊤ (genericPoint X) trivial s =
      (Stacks.Chow.rationalFunctionsEquivFunctionField X).val f :=
  exists_germ_eq_of_forall_zero_le_ord
    (Units.ne_zero
      (Units.map (Stacks.Chow.rationalFunctionsEquivFunctionField X).val.toMonoidHom f))
    fun y hy => by
      rw [← principalDivisor_apply_ofCoheightOne f hy]
      exact h _

end

section Noetherian

variable [IsNoetherian X] [IsNormal X]

/-- If `rationalFunctionWeilDivisor X f` is effective, `f` is a global section. -/
theorem exists_germ_eq_of_rationalFunctionWeilDivisor_nonneg
    (f : X.functionFieldˣ) (h : ∀ Z : PrimeDivisor X, 0 ≤ (rationalFunctionWeilDivisor X f).1 Z) :
    ∃ s : Γ(X, ⊤), X.presheaf.germ ⊤ (genericPoint X) trivial s = (f : X.functionField) :=
  exists_germ_eq_of_forall_zero_le_ord f.ne_zero fun y hy => by
    rw [← rationalFunctionWeilDivisor_apply_ofCoheightOne f hy]
    exact h _

/-- If `Γ(X, ⊤)` is a field, a rational function has trivial divisor if and only if it is
constant, i.e. is the germ of a global section. -/
theorem rationalFunctionWeilDivisor_eq_zero_iff_of_isField
    (hΓ : IsField Γ(X, ⊤)) (f : X.functionFieldˣ) :
    rationalFunctionWeilDivisor X f = 0 ↔
      ∃ s : Γ(X, ⊤), X.presheaf.germ ⊤ (genericPoint X) trivial s = (f : X.functionField) := by
  constructor
  · intro h
    refine exists_germ_eq_of_rationalFunctionWeilDivisor_nonneg f fun Z => ?_
    rw [h]
    exact le_rfl
  · rintro ⟨s, hs⟩
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact f.ne_zero (by rw [← hs, map_zero])
    obtain ⟨b, hb⟩ := hΓ.mul_inv_cancel hs0
    let v : Γ(X, ⊤)ˣ := ⟨s, b, hb, by rw [mul_comm]; exact hb⟩
    have hv : f = Units.map (X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toMonoidHom v :=
      Units.ext hs.symm
    rw [hv]
    exact rationalFunctionWeilDivisor_germ_unit v

/-- **Rational functions with trivial divisor are constant.** If `k → Γ(X, ⊤)` is a surjective
ring map from a field, a unit `f` of the function field with `div f = 0` is the germ of the image
of a constant `c ∈ k`. -/
theorem exists_eq_const_of_rationalFunctionWeilDivisor_eq_zero {k : Type*} [Field k]
    (φ : k →+* Γ(X, ⊤)) (hφ : Function.Surjective φ) (f : X.functionFieldˣ)
    (hf : rationalFunctionWeilDivisor X f = 0) :
    ∃ c : k, X.presheaf.germ ⊤ (genericPoint X) trivial (φ c) = (f : X.functionField) := by
  obtain ⟨s, hs⟩ := exists_germ_eq_of_rationalFunctionWeilDivisor_nonneg f fun Z => by
    rw [hf]
    exact le_rfl
  obtain ⟨c, rfl⟩ := hφ s
  exact ⟨c, hs⟩

end Noetherian

end Divisors

end ArithmeticOfJacobiPolynomials
