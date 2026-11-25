/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticSquareMap
public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticCurve
public import ArithmeticOfJacobiPolynomials.Galois.FixedRationalParametersDerivatives
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# The degree-two morphism is finite of degree two

Let `k` be a field, `q ∈ k[t]` of degree `m ≥ 1` and `f = q(x^2)` (`expand k 2 q`). The morphism
`squareMorphism q hq : projectiveModel f ⟶ projectiveModel q`, `(x, y) ↦ (x^2, y)`, of the
projective models is constructed in
`ArithmeticOfJacobiPolynomials.Geometry.HyperellipticSquareMap`. This file
proves that it is a finite morphism, and that the induced extension of function fields has degree
two (the degree of the morphism; used in the paragraph after Corollary 6.6 of the manuscript).

## Finiteness

* `preimage_basicOpen_squareMorphism`: the preimage of each standard chart `D₊(X_c)` (`c = Z, X`)
  of `projectiveModel q` is the corresponding chart `D₊(X_c)` of `projectiveModel f`; on the
  chart `D₊(X_{c'})` of the source this is because `X_c/X_{c'} ↦ (X_c/X_{c'})^2`
  (`chartSquareMap_isLocalizationElem`);
* `isPullback_awayι_squareMorphism`: hence the chart maps
  `Spec (S_f)_{(X_c)} → Spec (S_q)_{(X_c)}` are the base changes of `squareMorphism` to the charts
  of the target;
* `isFinite_specMap_chartSquareMap`, `finite_chartSquareMap`: each chart map is finite: it is
  integral (`isIntegralHom_chartSquareMorphism_one`, `isIntegralHom_chartSquareMorphism_zero`) and
  locally of finite type (a base change of the proper morphism `squareMorphism`);
* `isIntegralHom_squareMorphism`, **`isFinite_squareMorphism`**: `squareMorphism` is integral
  (integrality is local on the target) and locally of finite type (it is proper), hence finite.

## Degree two

For a morphism `φ : X ⟶ Y` of irreducible schemes with `φ(ξ_X) ⤳ ξ_Y` (e.g. `φ` surjective,
`specializes_genericPoint_of_surjective`), `functionFieldMap φ h : K(Y) → K(X)` is the stalk map
at the generic point. It is functorial
(`functionFieldMap_comp`) and an isomorphism for open immersions
(`isIso_functionFieldMap`). For a nonempty affine open `U ⊆ Y` with affine preimage,
`[K(X) : K(Y)] = rank_{Γ(Y, U)} Γ(X, φ⁻¹ U)` (`finrank_functionField_eq_finrank_app`; both are
fraction fields, `IsFractionRing.finrank_eq`). Comparing with the affine charts `y^2 = f(x)`,
`y^2 = q(t)`, where the morphism is `Spec (squareMap q)` and `k[x, y]/(y^2 - q(x^2))` is free of
rank two over `k[t, y]/(y^2 - q(t))` (`ArithmeticOfJacobiPolynomials.free_and_finrank_squareMap`):

* **`finrank_functionField_squareMorphism`**: for `q` and `f = q(x^2)` separable (so that both
  models are integral, `isIntegral_projectiveModel`),
  `[K(projectiveModel f) : K(projectiveModel q)] = 2` for the map of function fields induced by
  `squareMorphism` (`squareFunctionFieldMap`);
* `separable_expand_two`: `q(x^2)` is separable if `q` is separable, `q(0) ≠ 0` and `2 ≠ 0` in `k`;
  `finrank_functionField_squareMorphism_of_coeff_zero` is the degree statement under these
  hypotheses.

## The derivative families

For `f = F_{m,r,δ} = Q_{m,r,δ}(x^2)`
(`ArithmeticOfJacobiPolynomials.expand_reducedGegenbauerSquare`):
`isFinite_derivativeSquareMorphism` (finiteness, `m ≥ 1`),
`finrank_functionField_reducedGegenbauerSquare` (degree two when `Q_{m,r,δ}` and `F_{m,r,δ}` are
separable), and `exists_finrank_functionField_reducedGegenbauerSquare` (degree two for all large
`m`, from the irreducibility of `F_{m,r,δ}` and `Q_{m,r,δ}` in Corollary 1.7,
`ArithmeticOfJacobiPolynomials.fixedDerivativesGaloisStatement`, conditional on the literature
results used
there).

Not proved here: the genus/ramification (Riemann–Hurwitz) data of the double cover.
-/

public section

namespace ArithmeticOfJacobiPolynomials

universe u

attribute [local instance 2000] CommRingCat.commRing

-- The ring structure determines the geometric-field instances.
noncomputable local instance (priority := 2000) functionFieldCommSemiring
    (S : AlgebraicGeometry.Scheme.{u}) [IrreducibleSpace S] : CommSemiring S.functionField :=
  (CommRingCat.commRing S.functionField).toCommSemiring

noncomputable local instance (priority := 2000) functionFieldSemiring
    (S : AlgebraicGeometry.Scheme.{u}) [IrreducibleSpace S] : Semiring S.functionField :=
  (CommRingCat.commRing S.functionField).toSemiring

namespace Hyperelliptic

open Polynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-! ### Function fields and dominant morphisms -/

section FunctionField

/-- A surjective morphism sends the generic point to a generization of the generic point. -/
theorem specializes_genericPoint_of_surjective {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (φ : X ⟶ Y) (hφ : Function.Surjective φ) :
    φ (genericPoint X) ⤳ genericPoint Y := by
  obtain ⟨x, hx⟩ := hφ (genericPoint Y)
  rw [← hx]
  exact φ.base.hom.map_specializes ((genericPoint_spec X).specializes trivial)

/-- **The map of function fields** `K(Y) → K(X)` of a morphism `φ : X ⟶ Y` with
`φ(ξ_X) ⤳ ξ_Y`: the stalk map at the generic point. -/
@[expose]
noncomputable def functionFieldMap {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (φ : X ⟶ Y) (h : φ (genericPoint X) ⤳ genericPoint Y) :
    Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes h ≫ φ.stalkMap (genericPoint X)

theorem functionFieldMap_congr {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    {φ φ' : X ⟶ Y} (e : φ = φ') (h : φ (genericPoint X) ⤳ genericPoint Y)
    (h' : φ' (genericPoint X) ⤳ genericPoint Y) :
    functionFieldMap φ h = functionFieldMap φ' h' := by
  subst e
  rfl

/-- Functoriality of `functionFieldMap`. -/
theorem functionFieldMap_comp {X Y Z : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    [IrreducibleSpace Z] (φ : X ⟶ Y) (ψ : Y ⟶ Z) (hφ : φ (genericPoint X) ⤳ genericPoint Y)
    (hψ : ψ (genericPoint Y) ⤳ genericPoint Z)
    (hφψ : (φ ≫ ψ) (genericPoint X) ⤳ genericPoint Z) :
    functionFieldMap (φ ≫ ψ) hφψ = functionFieldMap ψ hψ ≫ functionFieldMap φ hφ := by
  simp only [functionFieldMap, Scheme.Hom.stalkMap_comp, Category.assoc]
  rw [← reassoc_of% (Scheme.Hom.stalkSpecializes_stalkMap (f := ψ) (h := hφ)),
    ← Category.assoc (Z.presheaf.stalkSpecializes hψ), TopCat.Presheaf.stalkSpecializes_comp]
  all_goals rfl

theorem isIso_stalkSpecializes_of_eq (Y : Scheme.{u}) {x y : Y} (h : x ⤳ y) (e : x = y) :
    IsIso (Y.presheaf.stalkSpecializes h) := by
  subst e
  have h1 : Y.presheaf.stalkSpecializes h = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
  rw [h1]
  infer_instance

/-- For an open immersion the map of function fields is an isomorphism. -/
theorem isIso_functionFieldMap {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (j : X ⟶ Y) [IsOpenImmersion j] (h : j (genericPoint X) ⤳ genericPoint Y) :
    IsIso (functionFieldMap j h) := by
  have := isIso_stalkSpecializes_of_eq Y h (genericPoint_eq_of_isOpenImmersion j)
  have : IsIso (j.stalkMap (genericPoint X)) :=
    inferInstanceAs (IsIso (j.toLRSHom.stalkMap (genericPoint X)))
  rw [functionFieldMap]
  infer_instance

/-- **The degree of the function field extension is the rank over an affine open**: for a
nonempty affine open `U ⊆ Y` with nonempty affine preimage,
`[K(X) : K(Y)] = rank_{Γ(Y, U)} Γ(X, φ⁻¹ U)`. -/
theorem finrank_functionField_eq_finrank_app {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (φ : X ⟶ Y) (h : φ (genericPoint X) ⤳ genericPoint Y) (U : Y.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen (φ ⁻¹ᵁ U)) [Nonempty U] [Nonempty (φ ⁻¹ᵁ U)]
    [Algebra Y.functionField X.functionField]
    (hKL : algebraMap Y.functionField X.functionField = (functionFieldMap φ h).hom)
    [Algebra Γ(Y, U) Γ(X, φ ⁻¹ᵁ U)] (hAB : algebraMap Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) = (φ.app U).hom) :
    Module.finrank Y.functionField X.functionField = Module.finrank Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := by
  have key : Y.germToFunctionField U ≫ functionFieldMap φ h =
      φ.app U ≫ X.germToFunctionField (φ ⁻¹ᵁ U) := by
    rw [functionFieldMap, ← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes,
      Scheme.Hom.germ_stalkMap]
  let _ : Algebra Γ(Y, U) X.functionField :=
    ((algebraMap Y.functionField X.functionField).comp
      (algebraMap Γ(Y, U) Y.functionField)).toAlgebra
  have : IsScalarTower Γ(Y, U) Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) X.functionField :=
    IsScalarTower.of_algebraMap_eq' (by
      change (algebraMap Y.functionField X.functionField).comp (Y.germToFunctionField U).hom =
        (X.germToFunctionField (φ ⁻¹ᵁ U)).hom.comp (algebraMap Γ(Y, U) Γ(X, φ ⁻¹ᵁ U))
      rw [hKL, hAB, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, key])
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  have := functionField_isFractionRing_of_isAffineOpen X (φ ⁻¹ᵁ U) hV
  exact IsFractionRing.finrank_eq Γ(Y, U) Y.functionField Γ(X, φ ⁻¹ᵁ U) X.functionField

/-- For `Spec B → Spec A` of domains, `[K(Spec B) : K(Spec A)] = rank_A B`. -/
theorem finrank_functionField_specMap {A B : Type u} [CommRing A] [CommRing B] [IsDomain A]
    [IsDomain B] (θ : A →+* B)
    (h : Spec.map (CommRingCat.ofHom θ) (genericPoint (Spec (CommRingCat.of B))) ⤳
      genericPoint (Spec (CommRingCat.of A)))
    [Algebra (Spec (CommRingCat.of A)).functionField (Spec (CommRingCat.of B)).functionField]
    (hKL : algebraMap (Spec (CommRingCat.of A)).functionField
        (Spec (CommRingCat.of B)).functionField =
      (functionFieldMap (Spec.map (CommRingCat.ofHom θ)) h).hom)
    [Algebra A B] (hθ : algebraMap A B = θ) :
    Module.finrank (Spec (CommRingCat.of A)).functionField
      (Spec (CommRingCat.of B)).functionField = Module.finrank A B := by
  have : Nonempty (⊤ : (Spec (CommRingCat.of A)).Opens) := ⟨⟨genericPoint _, trivial⟩⟩
  have : Nonempty (Spec.map (CommRingCat.ofHom θ) ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A)).Opens)) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  let _ : Algebra Γ(Spec (CommRingCat.of A), ⊤)
      Γ(Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom θ) ⁻¹ᵁ ⊤) :=
    ((Spec.map (CommRingCat.ofHom θ)).app ⊤).hom.toAlgebra
  rw [finrank_functionField_eq_finrank_app (Spec.map (CommRingCat.ofHom θ)) h ⊤
    (isAffineOpen_top _) (isAffineOpen_top _) hKL rfl]
  refine Algebra.finrank_eq_of_equiv_equiv
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
    (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv ?_
  rw [hθ]
  ext x
  exact (congrArg (fun F => F.hom x) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom θ))).symm

/-- **Transport of the degree along open immersions**: in a commutative square
`jX ≫ φ = ψ ≫ jY` with open immersions `jX`, `jY`, the extensions of function fields of `φ` and
`ψ` have the same degree. -/
theorem finrank_functionField_of_comm_square {X Y X' Y' : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] [IrreducibleSpace X'] [IrreducibleSpace Y'] (φ : X ⟶ Y) (ψ : X' ⟶ Y')
    (jX : X' ⟶ X) (jY : Y' ⟶ Y) [IsOpenImmersion jX] [IsOpenImmersion jY]
    (hsq : jX ≫ φ = ψ ≫ jY) (hφ : φ (genericPoint X) ⤳ genericPoint Y)
    (hψ : ψ (genericPoint X') ⤳ genericPoint Y')
    [Algebra Y.functionField X.functionField]
    (hKL : algebraMap Y.functionField X.functionField = (functionFieldMap φ hφ).hom)
    [Algebra Y'.functionField X'.functionField]
    (hKL' : algebraMap Y'.functionField X'.functionField = (functionFieldMap ψ hψ).hom) :
    Module.finrank Y.functionField X.functionField =
      Module.finrank Y'.functionField X'.functionField := by
  have hjX : jX (genericPoint X') ⤳ genericPoint X :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion jX)
  have hjY : jY (genericPoint Y') ⤳ genericPoint Y :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion jY)
  have h1 : (jX ≫ φ) (genericPoint X') ⤳ genericPoint Y :=
    (φ.base.hom.map_specializes hjX).trans hφ
  have h2 : (ψ ≫ jY) (genericPoint X') ⤳ genericPoint Y :=
    (jY.base.hom.map_specializes hψ).trans hjY
  have e : functionFieldMap φ hφ ≫ functionFieldMap jX hjX =
      functionFieldMap jY hjY ≫ functionFieldMap ψ hψ := by
    rw [← functionFieldMap_comp jX φ hjX hφ h1, ← functionFieldMap_comp ψ jY hψ hjY h2]
    exact functionFieldMap_congr hsq h1 h2
  have := isIso_functionFieldMap jX hjX
  have := isIso_functionFieldMap jY hjY
  refine Algebra.finrank_eq_of_equiv_equiv
    (asIso (functionFieldMap jY hjY)).commRingCatIsoToRingEquiv
    (asIso (functionFieldMap jX hjX)).commRingCatIsoToRingEquiv ?_
  rw [hKL, hKL']
  ext x
  exact (congrArg (fun F => F.hom x) e).symm

end FunctionField

variable {k : Type u} [Field k] {q : k[X]}

/-! ### The preimages of the charts -/

/-- On the chart `D₊(X_{c'})`, `D₊(X_c)` is cut out by `X_c/X_{c'}`. -/
theorem awayι_mem_basicOpen_iff (p : k[X]) {c c' : Fin 3} (hc : c ≠ 2) (hc' : c' ≠ 2)
    (z : Spec (CommRingCat.of (ChartRing p c'))) :
    Proj.awayι (grading p) (var p c') (var_mem_one p (weights_eq_one_of_ne_two _ hc'))
        Nat.one_pos z ∈ Proj.basicOpen (grading p) (var p c) ↔
      HomogeneousLocalization.Away.isLocalizationElem
        (var_mem_one p (weights_eq_one_of_ne_two _ hc'))
        (var_mem_one p (weights_eq_one_of_ne_two _ hc)) ∉ z.asIdeal := by
  have h := Proj.awayι_preimage_basicOpen (grading p)
    (var_mem_one p (weights_eq_one_of_ne_two _ hc')) Nat.one_pos
    (var_mem_one p (weights_eq_one_of_ne_two _ hc)) Nat.one_pos
  exact (Iff.of_eq (congrArg (fun U => z ∈ U) h)).trans (PrimeSpectrum.mem_basicOpen _ _)

/-- The chart map sends `X_c/X_{c'}` to `(X_c/X_{c'})^2`. -/
theorem chartSquareMap_isLocalizationElem (hq : 0 < q.natDegree) {c c' : Fin 3} (hc : c ≠ 2)
    (hc' : c' ≠ 2) :
    chartSquareMap hq c' hc' (HomogeneousLocalization.Away.isLocalizationElem
        (var_mem_one q (weights_eq_one_of_ne_two _ hc'))
        (var_mem_one q (weights_eq_one_of_ne_two _ hc))) =
      HomogeneousLocalization.Away.isLocalizationElem
        (var_mem_one (expand k 2 q) (weights_eq_one_of_ne_two _ hc'))
        (var_mem_one (expand k 2 q) (weights_eq_one_of_ne_two _ hc)) ^ 2 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.isLocalizationElem, chartSquareMap, scaledAwayMap_mk,
    HomogeneousLocalization.val_pow, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_pow]
  congr 1
  · rw [map_pow, squareHom_var_of_ne_two hq hc]
    ring
  · apply Subtype.ext
    simp

theorem squareMorphism_awayι_mem_basicOpen_iff (hq : 0 < q.natDegree) {c c' : Fin 3}
    (hc : c ≠ 2) (hc' : c' ≠ 2)
    (hcomp : Proj.awayι (grading (expand k 2 q)) (var _ c')
        (var_mem_one _ (weights_eq_one_of_ne_two _ hc')) Nat.one_pos ≫ squareMorphism q hq =
      chartSquareMorphism hq c' hc')
    (w : Spec (CommRingCat.of (ChartRing (expand k 2 q) c'))) :
    squareMorphism q hq (Proj.awayι (grading (expand k 2 q)) (var _ c')
        (var_mem_one _ (weights_eq_one_of_ne_two _ hc')) Nat.one_pos w) ∈
        Proj.basicOpen (grading q) (var q c) ↔
      Proj.awayι (grading (expand k 2 q)) (var _ c')
        (var_mem_one _ (weights_eq_one_of_ne_two _ hc')) Nat.one_pos w ∈
        Proj.basicOpen (grading (expand k 2 q)) (var _ c) := by
  have e : squareMorphism q hq (Proj.awayι (grading (expand k 2 q)) (var _ c')
      (var_mem_one _ (weights_eq_one_of_ne_two _ hc')) Nat.one_pos w) =
      Proj.awayι (grading q) (var q c') (var_mem_one q (weights_eq_one_of_ne_two _ hc'))
        Nat.one_pos (Spec.map (CommRingCat.ofHom (chartSquareMap hq c' hc')) w) := by
    rw [← Scheme.Hom.comp_apply (Proj.awayι (grading (expand k 2 q)) (var _ c')
      (var_mem_one _ (weights_eq_one_of_ne_two _ hc')) Nat.one_pos) (squareMorphism q hq) w,
      hcomp, chartSquareMorphism, Scheme.Hom.comp_apply]
  have hmem : ∀ a, a ∈ (Spec.map (CommRingCat.ofHom (chartSquareMap hq c' hc')) w).asIdeal ↔
      chartSquareMap hq c' hc' a ∈ w.asIdeal := fun a => Iff.rfl
  rw [e, awayι_mem_basicOpen_iff q hc hc', awayι_mem_basicOpen_iff (expand k 2 q) hc hc', hmem,
    chartSquareMap_isLocalizationElem hq hc hc', w.isPrime.pow_mem_iff_mem 2 two_pos]

theorem squareMorphism_mem_basicOpen_iff (hq : 0 < q.natDegree) {c : Fin 3} (hc : c ≠ 2)
    (x : projectiveModel (expand k 2 q)) :
    squareMorphism q hq x ∈ Proj.basicOpen (grading q) (var q c) ↔
      x ∈ Proj.basicOpen (grading (expand k 2 q)) (var _ c) := by
  have key : ∀ a : Fin 2, x ∈ Proj.basicOpen (grading (expand k 2 q)) (var _ (coverVar a)) →
      (squareMorphism q hq x ∈ Proj.basicOpen (grading q) (var q c) ↔
        x ∈ Proj.basicOpen (grading (expand k 2 q)) (var _ c)) := by
    intro a hx
    have hx' : x ∈ (Proj.awayι (grading (expand k 2 q)) (var _ (coverVar a))
        (var_mem_one _ (weights_eq_one_of_ne_two _ (coverVar_ne_two a))) Nat.one_pos).opensRange
        := by
      rw [Proj.opensRange_awayι]
      exact hx
    obtain ⟨w, rfl⟩ := hx'
    exact squareMorphism_awayι_mem_basicOpen_iff hq hc (coverVar_ne_two a)
      (awayι_comp_squareMorphism hq a) w
  rcases mem_chart_or_mem_chart x with hx | hx
  · exact key 0 hx
  · exact key 1 hx

/-- **The preimage of a standard chart is the corresponding standard chart**:
`squareMorphism⁻¹ D₊(X_c) = D₊(X_c)` for `X_c = Z, X`. -/
theorem preimage_basicOpen_squareMorphism (hq : 0 < q.natDegree) {c : Fin 3} (hc : c ≠ 2) :
    squareMorphism q hq ⁻¹ᵁ Proj.basicOpen (grading q) (var q c) =
      Proj.basicOpen (grading (expand k 2 q)) (var _ c) := by
  ext x
  exact squareMorphism_mem_basicOpen_iff hq hc x

/-- Over the chart `D₊(X_c)` of the target, `squareMorphism` is the chart map
`Spec (S_f)_{(X_c)} → Spec (S_q)_{(X_c)}`. -/
theorem isPullback_awayι_squareMorphism (hq : 0 < q.natDegree) (a : Fin 2) :
    IsPullback (Spec.map (CommRingCat.ofHom (chartSquareMap hq (coverVar a) (coverVar_ne_two a))))
      (Proj.awayι (grading (expand k 2 q)) (var _ (coverVar a))
        (var_mem_one _ (weights_eq_one_of_ne_two _ (coverVar_ne_two a))) Nat.one_pos)
      (Proj.awayι (grading q) (var q (coverVar a))
        (var_mem_one q (weights_eq_one_of_ne_two _ (coverVar_ne_two a))) Nat.one_pos)
      (squareMorphism q hq) :=
  IsOpenImmersion.isPullback _ _ _ _
    (by rw [awayι_comp_squareMorphism hq a, chartSquareMorphism])
    (by
      rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
      exact preimage_basicOpen_squareMorphism hq (coverVar_ne_two a))

theorem isIntegralHom_chartSquareMap (hq : 0 < q.natDegree) (a : Fin 2) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom
      (chartSquareMap hq (coverVar a) (coverVar_ne_two a)))) := by
  fin_cases a
  · exact isIntegralHom_chartSquareMorphism_one hq
  · exact isIntegralHom_chartSquareMorphism_zero hq

/-! ### Finiteness -/

/-- Each chart map `Spec (S_f)_{(X_c)} → Spec (S_q)_{(X_c)}` is locally of finite type (a base
change of the proper morphism `squareMorphism`). -/
theorem locallyOfFiniteType_specMap_chartSquareMap (hq : 0 < q.natDegree) (a : Fin 2) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (chartSquareMap hq (coverVar a) (coverVar_ne_two a)))) := by
  have := (isProper_squareMorphism hq).toLocallyOfFiniteType
  have := isProper_squareMorphism hq
  exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
    (isPullback_awayι_squareMorphism hq a).flip inferInstance

/-- Each chart map `Spec (S_f)_{(X_c)} → Spec (S_q)_{(X_c)}` is finite (integral and locally of
finite type). -/
theorem isFinite_specMap_chartSquareMap (hq : 0 < q.natDegree) (a : Fin 2) :
    IsFinite (Spec.map (CommRingCat.ofHom
      (chartSquareMap hq (coverVar a) (coverVar_ne_two a)))) := by
  have := isIntegralHom_chartSquareMap hq a
  have := locallyOfFiniteType_specMap_chartSquareMap hq a
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
  exact ⟨inferInstance, inferInstance⟩

/-- Each chart map `(S_q)_{(X_c)} → (S_f)_{(X_c)}` is a finite ring map. -/
theorem finite_chartSquareMap (hq : 0 < q.natDegree) (a : Fin 2) :
    (chartSquareMap hq (coverVar a) (coverVar_ne_two a)).Finite :=
  (IsFinite.SpecMap_iff _).mp (isFinite_specMap_chartSquareMap hq a)

/-- **The morphism is integral** (integrality is local on the target, and the chart maps, its
base changes to the charts of the target, are integral). -/
theorem isIntegralHom_squareMorphism (hq : 0 < q.natDegree) :
    IsIntegralHom (squareMorphism q hq) := by
  have hA := IsIntegralHom.hasAffineProperty.{u}
  have hL : IsZariskiLocalAtTarget @IsIntegralHom.{u} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ hA
  have hR : MorphismProperty.RespectsIso @IsIntegralHom.{u} :=
    @HasAffineProperty.instRespectsIsoScheme _ _ hA
  refine (@IsZariskiLocalAtTarget.iff_of_openCover @IsIntegralHom.{u} hL _ _
    (squareMorphism q hq) (chartCover q).openCover).mpr fun a => ?_
  have H := (isPullback_awayι_squareMorphism hq a).flip
  have hg := isIntegralHom_chartSquareMap hq a
  rw [← H.isoPullback_hom_snd, MorphismProperty.cancel_left_of_respectsIso (hP := hR)] at hg
  exact hg

/-- **The degree-two morphism `(x, y) ↦ (x^2, y)` of projective models is finite**: it is
integral and (being proper) locally of finite type. -/
theorem isFinite_squareMorphism (hq : 0 < q.natDegree) : IsFinite (squareMorphism q hq) := by
  have := (isProper_squareMorphism hq).toLocallyOfFiniteType
  have := isProper_squareMorphism hq
  have := isIntegralHom_squareMorphism hq
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
  exact ⟨inferInstance, inferInstance⟩

/-! ### Degree two -/

theorem natDegree_expand_two_pos (hq : 0 < q.natDegree) : 0 < (expand k 2 q).natDegree := by
  rw [natDegree_expand]
  omega

/-- `q(x^2)` is separable if `q` is separable, `q(0) ≠ 0` and `2 ≠ 0` in `k`. -/
theorem separable_expand_two (h2 : (2 : k) ≠ 0) (hs : q.Separable) (h0 : q.coeff 0 ≠ 0) :
    (expand k 2 q).Separable := by
  rw [Polynomial.Separable, derivative_expand]
  have hu : IsUnit ((2 : ℕ) : k[X]) := by
    rw [Nat.cast_ofNat, ← map_ofNat C 2]
    exact Polynomial.isUnit_C.mpr (IsUnit.mk0 _ h2)
  have hX : IsCoprime (expand k 2 q) (Polynomial.X ^ (2 - 1)) := by
    refine IsCoprime.pow_right (IsCoprime.symm ((Irreducible.coprime_iff_not_dvd irreducible_X).mpr
      ?_))
    rw [X_dvd_iff, coeff_expand two_pos]
    simpa using h0
  exact IsCoprime.mul_right (IsCoprime.map hs (expand k 2 : k[X] →ₐ[k] k[X]).toRingHom)
    ((isCoprime_mul_unit_left_right hu _ _).mpr hX)

theorem specializes_squareMorphism (hq : 0 < q.natDegree) [IrreducibleSpace (projectiveModel q)]
    [IrreducibleSpace (projectiveModel (expand k 2 q))] :
    squareMorphism q hq (genericPoint (projectiveModel (expand k 2 q))) ⤳
      genericPoint (projectiveModel q) :=
  specializes_genericPoint_of_surjective _ (Surjective.surj (self := surjective_squareMorphism hq))

variable (q) in
/-- **The map of function fields** `K(projectiveModel q) → K(projectiveModel (expand k 2 q))`
induced by the (surjective) morphism `squareMorphism q hq`. -/
@[expose]
noncomputable def squareFunctionFieldMap (hq : 0 < q.natDegree)
    [IrreducibleSpace (projectiveModel q)] [IrreducibleSpace (projectiveModel (expand k 2 q))] :
    (projectiveModel q).functionField ⟶ (projectiveModel (expand k 2 q)).functionField :=
  functionFieldMap (squareMorphism q hq) (specializes_squareMorphism hq)

theorem isOpenImmersion_affineChart (p : k[X]) : IsOpenImmersion (affineChart p) :=
  inferInstanceAs (IsOpenImmersion (chart (chartData_finite p)))

theorem injective_isIntegral_squareMap (q : k[X]) :
    Function.Injective (squareMap q) ∧ (squareMap q).IsIntegral :=
  injective_isIntegral_of_square one_ne_zero (squareMap q)
    (fun r => by rw [squareMap_of, expand_C]) (by rw [squareMap_of, expand_X, map_pow])
    (by rw [squareMap_root, map_one, mul_one])

theorem specializes_specMap_squareMap (q : k[X]) [IsDomain (HyperellipticCoordRing q)]
    [IsDomain (HyperellipticCoordRing (expand k 2 q))] :
    Spec.map (CommRingCat.ofHom (squareMap q))
        (genericPoint (Spec (CommRingCat.of (HyperellipticCoordRing (expand k 2 q))))) ⤳
      genericPoint (Spec (CommRingCat.of (HyperellipticCoordRing q))) :=
  specializes_genericPoint_of_surjective _ (surjective_specMap_of_isIntegral (squareMap q)
    (injective_isIntegral_squareMap q).1 (injective_isIntegral_squareMap q).2)

/-- On the affine charts: the extension of function fields of `Spec (squareMap q)` has degree
`2`. -/
theorem finrank_functionField_specMap_squareMap (q : k[X]) [IsDomain (HyperellipticCoordRing q)]
    [IsDomain (HyperellipticCoordRing (expand k 2 q))]
    [Algebra (Spec (CommRingCat.of (HyperellipticCoordRing q))).functionField
      (Spec (CommRingCat.of (HyperellipticCoordRing (expand k 2 q)))).functionField]
    (hKL : algebraMap (Spec (CommRingCat.of (HyperellipticCoordRing q))).functionField
        (Spec (CommRingCat.of (HyperellipticCoordRing (expand k 2 q)))).functionField =
      (functionFieldMap _ (specializes_specMap_squareMap q)).hom) :
    Module.finrank (Spec (CommRingCat.of (HyperellipticCoordRing q))).functionField
      (Spec (CommRingCat.of (HyperellipticCoordRing (expand k 2 q)))).functionField = 2 := by
  let _ : Algebra (HyperellipticCoordRing q) (HyperellipticCoordRing (expand k 2 q)) :=
    (squareMap q).toAlgebra
  rw [finrank_functionField_specMap (squareMap q) (specializes_specMap_squareMap q) hKL rfl]
  exact (free_and_finrank_squareMap q rfl).2

theorem finrank_squareFunctionFieldMap (hq : 0 < q.natDegree) (hs : q.Separable)
    (hfs : (expand k 2 q).Separable) [IrreducibleSpace (projectiveModel q)]
    [IrreducibleSpace (projectiveModel (expand k 2 q))]
    [Algebra (projectiveModel q).functionField (projectiveModel (expand k 2 q)).functionField]
    (hφ : algebraMap (projectiveModel q).functionField
        (projectiveModel (expand k 2 q)).functionField = (squareFunctionFieldMap q hq).hom) :
    Module.finrank (projectiveModel q).functionField
      (projectiveModel (expand k 2 q)).functionField = 2 := by
  have := isDomain_hyperellipticCoordRing hs hq
  have := isDomain_hyperellipticCoordRing hfs (natDegree_expand_two_pos hq)
  have := isOpenImmersion_affineChart q
  have := isOpenImmersion_affineChart (expand k 2 q)
  let _ : Algebra (Spec (CommRingCat.of (HyperellipticCoordRing q))).functionField
      (Spec (CommRingCat.of (HyperellipticCoordRing (expand k 2 q)))).functionField :=
    (functionFieldMap _ (specializes_specMap_squareMap q)).hom.toAlgebra
  rw [finrank_functionField_of_comm_square (squareMorphism q hq)
    (Spec.map (CommRingCat.ofHom (squareMap q))) (affineChart (expand k 2 q)) (affineChart q)
    (affineChart_comp_squareMorphism hq) (specializes_squareMorphism hq)
    (specializes_specMap_squareMap q) hφ rfl]
  exact finrank_functionField_specMap_squareMap q rfl

/-- **The morphism `(x, y) ↦ (x^2, y)` has degree two**: for `q` of positive degree with `q` and
`f = q(x^2)` separable (so both projective models are integral curves), the extension of
function fields `K(projectiveModel q) → K(projectiveModel f)` induced by `squareMorphism` has
degree `2`. -/
theorem finrank_functionField_squareMorphism (hq : 0 < q.natDegree) (hs : q.Separable)
    (hfs : (expand k 2 q).Separable) :
    haveI := irreducibleSpace_projectiveModel hs hq
    haveI := irreducibleSpace_projectiveModel hfs (natDegree_expand_two_pos hq)
    letI := (squareFunctionFieldMap q hq).hom.toAlgebra
    Module.finrank (projectiveModel q).functionField
      (projectiveModel (expand k 2 q)).functionField = 2 := by
  have := irreducibleSpace_projectiveModel hs hq
  have := irreducibleSpace_projectiveModel hfs (natDegree_expand_two_pos hq)
  let _ := (squareFunctionFieldMap q hq).hom.toAlgebra
  exact finrank_squareFunctionFieldMap hq hs hfs rfl

/-- The degree statement for `q` separable with `q(0) ≠ 0` and `2 ≠ 0` in `k`. -/
theorem finrank_functionField_squareMorphism_of_coeff_zero (h2 : (2 : k) ≠ 0)
    (hq : 0 < q.natDegree) (hs : q.Separable) (h0 : q.coeff 0 ≠ 0) :
    haveI := irreducibleSpace_projectiveModel hs hq
    haveI := irreducibleSpace_projectiveModel (separable_expand_two h2 hs h0)
      (natDegree_expand_two_pos hq)
    letI := (squareFunctionFieldMap q hq).hom.toAlgebra
    Module.finrank (projectiveModel q).functionField
      (projectiveModel (expand k 2 q)).functionField = 2 :=
  finrank_functionField_squareMorphism hq hs (separable_expand_two h2 hs h0)

end Hyperelliptic

/-! ### The derivative families -/

section DerivativeFamily

open Polynomial AlgebraicGeometry CategoryTheory Hyperelliptic

theorem isFinite_eqToHom_comp {k : Type u} [Field k] {p p' : Polynomial k} (h : p = p')
    {Y : Scheme.{u}} (g : projectiveModel p' ⟶ Y) (hg : IsFinite g) :
    IsFinite (eqToHom (congrArg projectiveModel h) ≫ g) := by
  subst h
  simpa using hg

/-- **The morphism `{y^2 = F_{m,r,δ}(x)} → {y^2 = Q_{m,r,δ}(t)}` of projective models is
finite** (`m ≥ 1`). -/
theorem isFinite_derivativeSquareMorphism (m r δ : ℕ) (hm : 0 < m) :
    IsFinite (derivativeSquareMorphism m r δ hm) :=
  isFinite_eqToHom_comp (expand_reducedGegenbauerSquare m r δ).symm _
    (isFinite_squareMorphism _)

theorem separable_expand_reducedGegenbauerSquare {m r δ : ℕ}
    (hF : (reducedGegenbauer m r δ).Separable) :
    (expand ℚ 2 (reducedGegenbauerSquare m r δ)).Separable := by
  rw [expand_reducedGegenbauerSquare]
  exact hF

/-- **Degree two for the derivative families**: if `Q_{m,r,δ}` and `F_{m,r,δ} = Q_{m,r,δ}(x^2)`
are separable (`m ≥ 1`), the map `(x, y) ↦ (x^2, y)` of projective models induces an extension of
function fields of degree `2`. -/
theorem finrank_functionField_reducedGegenbauerSquare {m r δ : ℕ} (hm : 0 < m)
    (hQ : (reducedGegenbauerSquare m r δ).Separable) (hF : (reducedGegenbauer m r δ).Separable) :
    haveI := irreducibleSpace_projectiveModel hQ (natDegree_reducedGegenbauerSquare_pos hm r δ)
    haveI := irreducibleSpace_projectiveModel (separable_expand_reducedGegenbauerSquare hF)
      (natDegree_expand_two_pos (natDegree_reducedGegenbauerSquare_pos hm r δ))
    letI := (squareFunctionFieldMap _ (natDegree_reducedGegenbauerSquare_pos hm r δ)).hom.toAlgebra
    Module.finrank (projectiveModel (reducedGegenbauerSquare m r δ)).functionField
      (projectiveModel (expand ℚ 2 (reducedGegenbauerSquare m r δ))).functionField = 2 :=
  finrank_functionField_squareMorphism _ hQ (separable_expand_reducedGegenbauerSquare hF)

/-- **Degree two for the derivative families, for all large `m`**: for fixed `r` there is `N`
such that for `m ≥ N` and `δ ∈ {0, 1}`, `Q_{m,r,δ}` and `F_{m,r,δ}` are separable and the map
`(x, y) ↦ (x^2, y)` of projective models induces an extension of function fields of degree `2`.
The separability comes from the irreducibility in Corollary 1.7
(`fixedDerivativesGaloisStatement`), conditional on the literature results it uses. -/
theorem exists_finrank_functionField_reducedGegenbauerSquare (hQ :
    GegenbauerQuadraticTransformation) (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros)
    (hBMOR : BMORPrimeCountingBound) (h619 : BMORLargeModulusPrimeCounting)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem) (r : ℕ) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ δ : ℕ, δ ≤ 1 →
      ∃ (hm : 0 < m) (hs : (reducedGegenbauerSquare m r δ).Separable)
        (hfs : (expand ℚ 2 (reducedGegenbauerSquare m r δ)).Separable),
        haveI := irreducibleSpace_projectiveModel hs (natDegree_reducedGegenbauerSquare_pos hm r δ)
        haveI := irreducibleSpace_projectiveModel hfs
          (natDegree_expand_two_pos (natDegree_reducedGegenbauerSquare_pos hm r δ))
        letI := (squareFunctionFieldMap _
          (natDegree_reducedGegenbauerSquare_pos hm r δ)).hom.toAlgebra
        Module.finrank (projectiveModel (reducedGegenbauerSquare m r δ)).functionField
          (projectiveModel (expand ℚ 2 (reducedGegenbauerSquare m r δ))).functionField = 2 := by
  obtain ⟨N, hN⟩ := fixedDerivativesGaloisStatement hQ hH hZ hBMOR h619 hBT hJones r ℚ
  refine ⟨max N 1, fun m hm δ hδ => ?_⟩
  obtain ⟨hFirr, -, hQirr, -, -, -⟩ := hN m (le_trans (le_max_left _ _) hm) δ hδ
  have e : ∀ p : ℚ[X], p.map (algebraMap ℚ ℚ) = p := fun p => by
    rw [Algebra.algebraMap_self, Polynomial.map_id]
  rw [e] at hFirr
  rw [e] at hQirr
  have hm0 : 0 < m := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right _ _) hm)
  exact ⟨hm0, hQirr.separable, separable_expand_reducedGegenbauerSquare hFirr.separable,
    finrank_functionField_squareMorphism (natDegree_reducedGegenbauerSquare_pos hm0 r δ)
      hQirr.separable (separable_expand_reducedGegenbauerSquare hFirr.separable)⟩

end DerivativeFamily

end ArithmeticOfJacobiPolynomials
