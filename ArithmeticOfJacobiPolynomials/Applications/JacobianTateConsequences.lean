/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.External
public import ArithmeticOfJacobiPolynomials.Geometry.EtaleCycleClassInterface
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianArithmeticInterface
public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticProjective
public import ArithmeticOfJacobiPolynomials.Geometry.Jacobian.Basic
public import ArithmeticOfJacobiPolynomials.Geometry.GroupSchemeProduct
public import ArithmeticOfJacobiPolynomials.Algebra.ZarhinGroups
public import ArithmeticOfJacobiPolynomials.Algebra.HyperellipticModel
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Corollary 6.6: Tate classes on powers of hyperelliptic Jacobians

The manuscript's proof of the cycle-class sentence of Corollary 6.6 is: *Zarhin's Theorem 8.1 gives
the Tate statement over every finite extension and on every power; a Galois-invariant class
represented by algebraic cycles over a finite extension descends with rational coefficients by
averaging over a finite Galois extension.*

* `Zarhin.TateClassesDivisorProducts` is the **characteristic-zero assertion of Zarhin (2002),
  Theorem 8.1, in the source's full characteristic-zero generality** (a *cited input* in
  `External.lean`; see `External.lean`): for every field `K` of characteristic `0`
  finitely generated over `ℚ`, `K_a = L` an algebraic closure of `K` (`IsAlgClosure K L`, which is
  also its separable closure, so the source's `K_a` *is* our `L`), `deg f ≥ 5`, **all** Galois
  alternatives of the source (`Zarhin.AdmissibleGalois`), every finite extension `K' ⊂ L` of `K`,
  every prime `ℓ` (invertible in `K`, as `char K = 0`) and every positive power `J(C_f)^{h+1}`,
  every Tate class is a `ℚ_ℓ`-linear combination of products of divisor classes over `K_a`.
  The positive-characteristic global-field alternative of the source is **not** stated (the
  manuscript's Corollary 6.6 is over `ℚ`; only the characteristic-zero assertion is used).
  The statement is relative to a *canonical cycle class system* (`CanonicalCycleSystem`), the
  characterized cited object whose divisor classes it speaks of.
* `Zarhin.TateClassesDivisorProducts.span_clBase_eq_invariants`: the manuscript's reduction —
  from the input and the canonical system, the cycle class map of `X = (J^{h+1})_{K'}` is
  surjective onto the Galois invariants, by finite-extension representation (Stacks finite Chow
  stage) and rational averaging (`EtaleCycleClassInterface.span_clBase_eq_invariants`).
* `Zarhin.TateClassesDivisorProducts.cycleClasses_rat`: the shape of
  `JacobianSetting.CycleClasses` (`K = ℚ`, `K_a = ℚ̄`, `K' = E` a number field, `deg f ≥ 9`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

namespace ArithmeticOfJacobiPolynomials

open ArithmeticOfJacobiPolynomials.GroupObject GroupScheme AbelianEtale AbelianCycleClass
  EtaleCycleClassInterface

namespace Zarhin

/-- **Surjectivity of the cycle class map over `K'`, from Zarhin's Theorem 8.1** (the manuscript's
reduction, Corollary 6.6). The conclusion is for every functoriality package `F` selected by the
canonical predicate `CanonicalCycleClass`: the `ℚ_ℓ`-span of the classes of cycles on
`X = (J^{h+1})_{K'}` is the whole of `H^{2c}(X_L, ℚ_ℓ(c))^{Gal(L/K')}`. -/
theorem TateClassesDivisorProducts.span_clBase_eq_invariants (Z : TateClassesDivisorProducts)
    (K L : Type) [Field K] [CharZero K] [Algebra ℚ K] [Algebra.EssFiniteType ℚ K]
    [Field L] [Algebra K L] [IsAlgClosure K L]
    (f : K[X]) (hf : f.Separable) (hfd : 5 ≤ f.natDegree)
    (hG : Zarhin.AdmissibleGalois f)
    (C : Over (Spec (.of K))) (hCm : Zarhin.HyperellipticModel f C)
    (B : BigFppfSite.{0}) (hC : B.Contains C.left) (hK : B.Contains (Spec (.of K)))
    (g : B.obj hC ⟶ B.obj hK) (hg : B.inclusion.map g = C.hom) [IsProper (B.inclusion.map g)]
    (hdim : topologicalKrullDim C.left ≤ 1) (J : Grp (Over (Spec (.of K))))
    (hJ : Jacobian.IsJacobianOf B hC hK g hdim J)
    (K' : IntermediateField K L) [FiniteDimensional K K'] [Algebra.IsSeparable K' L] [Normal K' L]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) (h c : ℕ) (i : ℤ)
    (B' : BigEtaleSite.{0}) [EllAdicSite B' ℓ] (X : B'.Scheme) [IsNoetherian X.1]
    (fX : X.1 ⟶ Spec (.of K')) [IsProper fX] (π : X.1 ⟶ (powObj K J.X (h + 1)).left)
    (hπ : IsPullback π fX (powObj K J.X (h + 1)).hom
      (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
    (F : CycleClassFunctoriality B' ℓ X fX L c i) (hF : CanonicalCycleClass B' ℓ X fX L c i F) :
    Submodule.span ℚ_[ℓ] (Set.range F.clBase) =
      (etaleCohomologyTwistRep B' ℓ X fX L c).invariants := by
  obtain ⟨h0, hd, ζ, P, rfl⟩ := hF
  exact EtaleCycleClassInterface.span_clBase_eq_invariants P c i (by omega)
    (fun w hw =>
      Z K L f hf hfd hG C hCm B hC hK g hg hdim J hJ K' ℓ hℓ h c _ B' X fX π hπ hd ζ P w hw)

/-- **The rational case, in the shape of `JacobianSetting.CycleClasses`:** `K = ℚ`, `K_a = ℚ̄`,
`K' = E` a number field, `f ∈ ℚ[x]` separable of degree `≥ 9` with an admissible Galois group. -/
theorem TateClassesDivisorProducts.cycleClasses_rat (Z : TateClassesDivisorProducts)
    (f : ℚ[X]) (hf : f.Separable) (hdeg : 9 ≤ f.natDegree) (hG : Zarhin.AdmissibleGalois f)
    (B : BigFppfSite.{0}) (hC : B.Contains (Hyperelliptic.projectiveModel f))
    (hQ : B.Contains (Spec (.of ℚ))) (g : B.obj hC ⟶ B.obj hQ)
    (hg : B.inclusion.map g = Hyperelliptic.toSpecField f) [IsProper (B.inclusion.map g)]
    (hdim : topologicalKrullDim (Hyperelliptic.projectiveModel f) ≤ 1)
    (J : Grp (Over (Spec (.of ℚ)))) (hJ : Jacobian.IsJacobianOf B hC hQ g hdim J)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E]
    (ℓ : ℕ) [Fact ℓ.Prime] (h c : ℕ) (i : ℤ)
    (B' : BigEtaleSite.{0}) [EllAdicSite B' ℓ] (X : B'.Scheme) [IsNoetherian X.1]
    (fX : X.1 ⟶ Spec (.of E)) [IsProper fX] (π : X.1 ⟶ (powObj ℚ J.X (h + 1)).left)
    (hπ : IsPullback π fX (powObj ℚ J.X (h + 1)).hom
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ E))))
    (F : CycleClassFunctoriality B' ℓ X fX (AlgebraicClosure ℚ) c i)
    (hF : CanonicalCycleClass B' ℓ X fX (AlgebraicClosure ℚ) c i F) :
    Submodule.span ℚ_[ℓ] (Set.range F.clBase) =
      (etaleCohomologyTwistRep B' ℓ X fX (AlgebraicClosure ℚ) c).invariants :=
  Z.span_clBase_eq_invariants ℚ (AlgebraicClosure ℚ) f hf (by omega) hG
    (Over.mk (Hyperelliptic.toSpecField f))
    (Zarhin.hyperellipticModel_projectiveModel (by norm_num) hf (by omega)) B hC hQ g hg hdim J
    hJ E ℓ (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero) h c i B' X fX π hπ F hF

end Zarhin

end ArithmeticOfJacobiPolynomials
