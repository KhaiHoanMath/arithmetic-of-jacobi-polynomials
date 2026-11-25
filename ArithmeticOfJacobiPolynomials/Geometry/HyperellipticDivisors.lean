/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.Divisors.LinearEquivalence
public import ArithmeticOfJacobiPolynomials.Geometry.Divisors.WeilCurve
public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticDedekind

/-!
# The hyperelliptic model is a normal curve: rational functions with trivial divisor

Let `k` be a field with `2 ≠ 0` and `f ∈ k[x]` separable of degree `≥ 1`. The projective model
`X = projectiveModel f` of `y^2 = f(x)` is a scheme of dimension `≤ 1`
(`ArithmeticOfJacobiPolynomials.Hyperelliptic.coheight_le_one`) whose local rings at points of
codimension one are
discrete valuation rings (`isDiscreteValuationRing_stalk_projectiveModel`), so it is normal
(`isNormal_projectiveModel`, from
`ArithmeticOfJacobiPolynomials.Divisors.isNormal_of_coheight_le_one_of_dvr`).
It is quasi-compact and locally Noetherian (`HyperellipticDedekind`), hence Noetherian.

All divisor theory is Stacks': `AlgebraicGeometry.rationalFunctionWeilDivisor` (Tag 02R3),
`AlgebraicGeometry.effectiveCartierWeilDivisor` (Tag 02AR (5)), and
`Stacks.Divisors.LinearlyEquivalent` (Tag 0CCT), unfolded on normal Noetherian integral schemes by
`ArithmeticOfJacobiPolynomials.Divisors.linearlyEquivalent_iff_exists_ord`. Since `Γ(X, ⊤) = k`
(`globalStructureMap_bijective`), a rational function has trivial divisor iff it is a constant
(`rationalFunctionWeilDivisor_eq_zero_iff_projectiveModel`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace Hyperelliptic

open _root_.Polynomial renaming X → polyX

open _root_.Polynomial AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k] {f : k[X]}

/-- **The hyperelliptic model is normal** (for `f` separable of degree `≥ 1` and `2 ≠ 0`). -/
theorem isNormal_projectiveModel (h2 : (2 : k) ≠ 0) (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    haveI := isIntegral_projectiveModel hf hdeg
    IsNormal (projectiveModel f) := by
  have := isIntegral_projectiveModel hf hdeg
  exact Divisors.isNormal_of_coheight_le_one_of_dvr (coheight_le_one hf hdeg)
    (isDiscreteValuationRing_stalk_projectiveModel h2 hf hdeg)

theorem isField_globalSections_projectiveModel (f : k[X]) :
    IsField Γ(projectiveModel f, ⊤) :=
  MulEquiv.isField (Field.toIsField k)
    (RingEquiv.ofBijective (globalStructureMap f) (globalStructureMap_bijective f)).symm.toMulEquiv

/-- **Rational functions with trivial divisor on the hyperelliptic model**: for `f` separable of
degree `≥ 1` over a field `k` with `2 ≠ 0`, a rational function `φ` on `projectiveModel f` has
`div φ = 0` if and only if it is the germ of a constant `c ∈ k`. -/
theorem rationalFunctionWeilDivisor_eq_zero_iff_projectiveModel (h2 : (2 : k) ≠ 0)
    (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    haveI := isIntegral_projectiveModel hf hdeg
    ∀ φ : (projectiveModel f).functionFieldˣ,
      rationalFunctionWeilDivisor (projectiveModel f) φ = 0 ↔
        ∃ c : k, (projectiveModel f).presheaf.germ ⊤ (genericPoint (projectiveModel f)) trivial
          (globalStructureMap f c) = (φ : (projectiveModel f).functionField) := by
  have := isIntegral_projectiveModel hf hdeg
  have := isNormal_projectiveModel h2 hf hdeg
  intro φ
  rw [Divisors.rationalFunctionWeilDivisor_eq_zero_iff_of_isField
    (isField_globalSections_projectiveModel f) φ]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨c, rfl⟩ := (globalStructureMap_bijective f).2 s
    exact ⟨c, hs⟩
  · rintro ⟨c, hc⟩
    exact ⟨_, hc⟩

end Hyperelliptic

end ArithmeticOfJacobiPolynomials
