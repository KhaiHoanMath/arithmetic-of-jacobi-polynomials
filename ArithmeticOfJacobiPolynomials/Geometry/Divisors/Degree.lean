/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.Divisors.Weil
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Jacobson.Ring
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.NormalizationDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorMiddleExactness

/-!
# The degree of a Weil divisor on a proper curve: bridges to the library

Residue degree, the degree of a cycle and the degree of a principal divisor are the library's:

* `AlgebraicGeometry.Scheme.Hom.residueDegree π x = [κ(x) : κ(π x)]` (Mathlib; the multiplicity
  of Stacks 02R4, whose `@[stacks]` attribute sits on `AlgebraicCycle.mapCoeff`);
* `AlgebraicGeometry.AlgebraicCycle.degree π : AlgebraicCycle X R →+ R`,
  `∑ᶠ x, π.residueDegree x • D x` for `X` quasi-compact (Mathlib, `@[stacks 0AZ2]`);
* `Stacks.Chow.principalDivisorDegree π f = ∑ᶠ x, ord_x f * π.residueDegree x` (no tag), and
  `Stacks.Chow.principalDivisorDegree_eq_zero` (`@[stacks 02RU "the displayed sum"]`): for
  `X` a scheme over `k` with `[IsCurve k (X ↘ Spec k)]` (integral, separated, locally of finite
  type, quasi-compact, `topologicalKrullDim = 1`), `[IsProper …]`, `[IsLocallyNoetherian X]`
  and `f ≠ 0`, the degree of `div f` is zero. The Lean statement is for a *curve* in this
  sense; it is not claimed for non-integral proper schemes of dimension `≤ 1`.

This file adds (a) the degree on the canonical `AlgebraicGeometry.WeilDivisor`, which is
`AlgebraicCycle.degree` after `ArithmeticOfJacobiPolynomials.Divisors.cycleOfWeilDivisor`; (b) the
agreement with
`Stacks.Chow.principalDivisorDegree`, hence 02RU for `WeilDivisor`s; (c) the descent to the class
group `weilDivisorClassGroup`; and (d) positivity of `Hom.residueDegree` at closed points of a
scheme locally of finite type over a field (Stacks proves it only for its own
`Stacks.EtaleCohomology.residueDegree`, a different declaration; that a point of coheight one on
a curve is closed is `Stacks.EtaleCohomology.isClosed_singleton_of_coheight_eq_one`).

## Main results

* `ArithmeticOfJacobiPolynomials.Divisors.weilDivisorDegree π : WeilDivisor X →+ ℤ`.
* `ArithmeticOfJacobiPolynomials.Divisors.weilDivisorDegree_eq_finsum`: `deg D = ∑ᶠ Z, [κ(Z) : κ(π
Z)] · D Z` over
  prime divisors.
* `ArithmeticOfJacobiPolynomials.Divisors.weilDivisorDegree_principalDivisor` and
  `ArithmeticOfJacobiPolynomials.Divisors.weilDivisorDegree_rationalFunctionWeilDivisor`: agreement
  with
  `Stacks.Chow.principalDivisorDegree`.
* `ArithmeticOfJacobiPolynomials.Divisors.weilDivisorDegree_principalDivisor_eq_zero`: **Stacks
02RU** for
  `WeilDivisor`s on a proper curve.
* `ArithmeticOfJacobiPolynomials.Divisors.weilDivisorClassGroupDegree`: the degree on
`weilDivisorClassGroup X`,
  with kernel the classes of degree-zero divisors
  (`ArithmeticOfJacobiPolynomials.Divisors.ker_weilDivisorClassGroupDegree`).
* `ArithmeticOfJacobiPolynomials.Divisors.residueDegree_pos_of_isClosed`,
  `ArithmeticOfJacobiPolynomials.Divisors.residueDegree_pos_of_coheight_eq_one`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open AlgebraicGeometry CategoryTheory

universe u

namespace Divisors

/-! ### Residue degrees at closed points -/

section ResidueDegree

variable {k : Type u} [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of k))

/-- **Closed points of a scheme locally of finite type over a field have finite residue degree**
(Zariski's lemma): `κ(x)` is a finite extension of `κ(π x)`. This is stated for the library's
`Scheme.Hom.residueFieldMap`, the algebra structure behind `Scheme.Hom.residueDegree`. -/
theorem finite_residueFieldMap_of_isClosed [LocallyOfFiniteType π] {x : X}
    (hx : IsClosed ({x} : Set X)) :
    letI := (π.residueFieldMap x).hom.toAlgebra
    Module.Finite ((Spec (CommRingCat.of k)).residueField (π x)) (X.residueField x) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace π
  have h1 : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  have h2 : LocallyOfFiniteType (Spec.map (π.residueFieldMap x) ≫
      (Spec (CommRingCat.of k)).fromSpecResidueField (π x)) := by
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    infer_instance
  have h3 : LocallyOfFiniteType (Spec.map (π.residueFieldMap x)) :=
    locallyOfFiniteType_of_comp (Spec.map (π.residueFieldMap x))
      ((Spec (CommRingCat.of k)).fromSpecResidueField (π x))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h3
  let := (π.residueFieldMap x).hom.toAlgebra
  have : Algebra.FiniteType ((Spec (CommRingCat.of k)).residueField (π x)) (X.residueField x) :=
    h3
  exact finite_of_finite_type_of_isJacobsonRing _ _

/-- A closed point of a scheme locally of finite type over a field has positive residue degree. -/
theorem residueDegree_pos_of_isClosed [LocallyOfFiniteType π] {x : X}
    (hx : IsClosed ({x} : Set X)) : 0 < π.residueDegree x := by
  have := finite_residueFieldMap_of_isClosed π hx
  let := (π.residueFieldMap x).hom.toAlgebra
  exact Module.finrank_pos

/-- On a curve over a field, a point of coheight one (the generic point of a prime divisor) has
positive finite residue degree. (That such a point is closed is
`Stacks.EtaleCohomology.isClosed_singleton_of_coheight_eq_one`.) -/
theorem residueDegree_pos_of_coheight_eq_one [IsCurve k π] {x : X}
    (hx : Order.coheight x = 1) : 0 < π.residueDegree x :=
  residueDegree_pos_of_isClosed π
    (Stacks.EtaleCohomology.isClosed_singleton_of_coheight_eq_one π hx)

end ResidueDegree

/-! ### The degree of a Weil divisor -/

section Degree

variable {X Y : Scheme.{u}} [CompactSpace X] (π : X ⟶ Y)

/-- **The degree of a Weil divisor** with respect to `π : X ⟶ Y` (typically `Y = Spec k`): the
library's `AlgebraicCycle.degree` (Stacks 0AZ2) of the cycle of the divisor. -/
@[expose] noncomputable def weilDivisorDegree : WeilDivisor X →+ ℤ :=
  (AlgebraicCycle.degree π : AlgebraicCycle X ℤ →+ ℤ).comp cycleOfWeilDivisor

theorem weilDivisorDegree_apply (D : WeilDivisor X) :
    weilDivisorDegree π D = ∑ᶠ x, π.residueDegree x • cycleOfWeilDivisor D x :=
  rfl

/-- The degree as a sum over prime divisors: `∑ᶠ Z, [κ(Z) : κ(π Z)] · D Z`. -/
theorem weilDivisorDegree_eq_finsum (D : WeilDivisor X) :
    weilDivisorDegree π D = ∑ᶠ Z : PrimeDivisor X, π.residueDegree Z.genericPoint • D.1 Z := by
  rw [weilDivisorDegree_apply]
  have h : ∑ᶠ x ∈ Set.range (PrimeDivisor.genericPoint (X := X)),
      π.residueDegree x • cycleOfWeilDivisor D x =
      ∑ᶠ x, π.residueDegree x • cycleOfWeilDivisor D x := by
    rw [← finsum_mem_univ (fun x => π.residueDegree x • cycleOfWeilDivisor D x)]
    refine finsum_mem_inter_support_eq'
      (fun x => π.residueDegree x • cycleOfWeilDivisor D x) _ _ fun x hx => ?_
    rw [mem_range_genericPoint_iff]
    refine ⟨fun _ => Set.mem_univ x, fun _ => ?_⟩
    by_contra h
    exact hx (by simp only [cycleOfWeilDivisor_apply_of_coheight_ne_one D h, smul_zero])
  rw [← h, finsum_mem_range PrimeDivisor.genericPoint_injective]
  exact finsum_congr fun Z => by rw [cycleOfWeilDivisor_genericPoint]

section Principal

variable [IsIntegral X] [IsLocallyNoetherian X]

/-- The degree of the principal divisor of a rational function is the library's
`Stacks.Chow.principalDivisorDegree`. -/
theorem weilDivisorDegree_principalDivisor (f : (Stacks.Chow.rationalFunctions X)ˣ) :
    weilDivisorDegree π (principalDivisor X f) =
      Stacks.Chow.principalDivisorDegree π
        ((Stacks.Chow.rationalFunctionsEquivFunctionField X).val f) := by
  rw [weilDivisorDegree_apply, Stacks.Chow.principalDivisorDegree]
  refine finsum_congr fun x => ?_
  rw [cycleOfWeilDivisor_principalDivisor, nsmul_eq_mul, mul_comm]

end Principal

end Degree

section RationalFunctions

variable {X Y : Scheme.{u}} (π : X ⟶ Y) [IsIntegral X] [IsNoetherian X]

/-- The degree of `rationalFunctionWeilDivisor X f` is `Stacks.Chow.principalDivisorDegree`. -/
theorem weilDivisorDegree_rationalFunctionWeilDivisor (f : X.functionFieldˣ) :
    weilDivisorDegree π (rationalFunctionWeilDivisor X f) =
      Stacks.Chow.principalDivisorDegree π (f : X.functionField) := by
  rw [weilDivisorDegree_apply, Stacks.Chow.principalDivisorDegree]
  refine finsum_congr fun x => ?_
  rw [cycleOfWeilDivisor_rationalFunctionWeilDivisor, nsmul_eq_mul, mul_comm]

end RationalFunctions

/-! ### Stacks 02RU and the class group -/

section ProperCurve

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (π : X ⟶ Spec (CommRingCat.of k)) [IsCurve k π] [IsProper π]

/-- **The degree of a principal divisor on a proper curve is zero** (Stacks 02RU, in the form of
`Stacks.Chow.principalDivisorDegree_eq_zero`: `π` is a curve, i.e. an integral variety of
dimension one, and proper), for `AlgebraicGeometry.principalDivisor`. -/
theorem weilDivisorDegree_principalDivisor_eq_zero [CompactSpace X] [IsLocallyNoetherian X]
    (f : (Stacks.Chow.rationalFunctions X)ˣ) :
    weilDivisorDegree π (principalDivisor X f) = 0 := by
  let : X.Over (Spec (CommRingCat.of k)) := ⟨π⟩
  have : IsCurve k (X ↘ Spec (CommRingCat.of k)) := inferInstanceAs (IsCurve k π)
  have : IsProper (X ↘ Spec (CommRingCat.of k)) := inferInstanceAs (IsProper π)
  rw [weilDivisorDegree_principalDivisor]
  exact Stacks.Chow.principalDivisorDegree_eq_zero k X _
    (Units.ne_zero
      (Units.map (Stacks.Chow.rationalFunctionsEquivFunctionField X).val.toMonoidHom f))

/-- **The degree of `rationalFunctionWeilDivisor X f` on a proper curve is zero**
(Stacks 02RU). -/
theorem weilDivisorDegree_rationalFunctionWeilDivisor_eq_zero [IsNoetherian X]
    (f : X.functionFieldˣ) : weilDivisorDegree π (rationalFunctionWeilDivisor X f) = 0 := by
  let : X.Over (Spec (CommRingCat.of k)) := ⟨π⟩
  have : IsCurve k (X ↘ Spec (CommRingCat.of k)) := inferInstanceAs (IsCurve k π)
  have : IsProper (X ↘ Spec (CommRingCat.of k)) := inferInstanceAs (IsProper π)
  rw [weilDivisorDegree_rationalFunctionWeilDivisor]
  exact Stacks.Chow.principalDivisorDegree_eq_zero k X _ f.ne_zero

variable [CompactSpace X] [IsLocallyNoetherian X]

/-- **The degree on the Weil divisor class group of a proper curve**, well defined because
principal divisors have degree zero (Stacks 02RU). -/
@[expose] noncomputable def weilDivisorClassGroupDegree : weilDivisorClassGroup X →+ ℤ :=
  QuotientAddGroup.lift (principalWeilDivisors X) (weilDivisorDegree π) (by
    rintro _ ⟨f, rfl⟩
    exact weilDivisorDegree_principalDivisor_eq_zero π f)

theorem weilDivisorClassGroupDegree_mk (D : WeilDivisor X) :
    weilDivisorClassGroupDegree π (D : weilDivisorClassGroup X) = weilDivisorDegree π D :=
  QuotientAddGroup.lift_mk' _ _ D

/-- The kernel of the degree on the class group is the image of the degree-zero divisors
(`Cl⁰`). -/
theorem ker_weilDivisorClassGroupDegree :
    (weilDivisorClassGroupDegree π).ker =
      (weilDivisorDegree π).ker.map (QuotientAddGroup.mk' (principalWeilDivisors X)) := by
  ext c
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective c
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_map, weilDivisorClassGroupDegree_mk]
  constructor
  · intro hD
    exact ⟨D, hD, rfl⟩
  · rintro ⟨E, hE, hED⟩
    have e := congrArg (weilDivisorClassGroupDegree π) hED
    simp only [QuotientAddGroup.mk'_apply, weilDivisorClassGroupDegree_mk] at e
    rw [← e]
    exact hE

end ProperCurve

end Divisors

end ArithmeticOfJacobiPolynomials
