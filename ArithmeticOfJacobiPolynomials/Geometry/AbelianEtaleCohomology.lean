/- Assembled by AxiomProver. -/
module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.ConstantSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LowerShriekAffineLine.QuasiFiniteLowerShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisEquivariantCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTateTwistCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantLevelExtComparison
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.FieldTheory.Galois.Notation

/-!
# `ℓ`-adic cohomology of a proper scheme over a field, with its Galois action

Chow-theoretic Corollary 6.6 needs the target `H^{2c}_{ét}(X_{k̄}, ℚ_ℓ(c))` of the cycle class map
as a `ℚ_ℓ`-vector space with an action of `Gal(k̄/k)`.  Everything geometric is from the
Stacks library:

* the underlying `ℤ_ℓ`-module is
  `Stacks.EtaleCohomology.LAdicSheaf.geometricCompactlySupportedCohomology` (Tag 03UT) at
  the identity compactification of the proper `k`-scheme `X` and the constant `ℓ`-adic sheaf;
  `cohomologyZl`, `cohomologyQl` are the library values;
* the Galois action is the library's `galoisDerivedCompactSupport`: the level complex
  `RΓ^Gal_c(X_{k̄}, Fₙ)` in discrete Galois modules.  `galoisLevelCohomology` is the composite
  `padicCoefficientComplex ⋙ j_! ⋙ Q ⋙ galoisDerivedGlobalSections ⋙ Hⁱ`, and
  `galoisLevelCohomology_obj` records that its value is `Hⁱ(galoisDerivedCompactSupport …)` on the
  nose;
* the two presentations agree: `galoisLevelForgetIso` is the natural isomorphism
  `Hⁱ_Gal ⋙ forget ≅ geometricCompactSupportPadicCohomology` (using the library's
  `galoisCompactSupportForgetNatIso` and our `compactSupportComparison`, the
  `RΓ(X̄_{k̄}, -) ≅ Rπ_* ⋙ RΓ(Spec k̄, -)` identification), and `galoisCohomologyForgetIso`
  shows that the underlying `ℤ_ℓ`-module of the limit `galoisCohomologyZl` is the library's
  `geometricCompactlySupportedCohomology`.

Two bridges not provided by the library: `ratRep` (the library has only the
`ModuleCat` extension of scalars `ratSpace`, not the induced representation) and `tateTwistQlRep`
(the library has only the finite-level `Hom(μₙ, -)` twist; the `ℓ`-adic character is Mathlib's
`cyclotomicCharacter`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
  Stacks.EtaleCohomology Stacks.Frobenius

universe u

namespace ArithmeticOfJacobiPolynomials.AbelianEtale

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-- The set-theoretic and sheafification hypotheses under which Stacks forms `ℓ`-adic sheaves on
the big étale site `B`. -/
class EllAdicSite (B : BigEtaleSite.{u}) (ℓ : ℕ) : Prop where
  isRightAdjoint : ∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint
  hasWeakSheafifyOver : ∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
  hasWeakSheafify : ∀ (n : ℕ) (T : B.Scheme),
    HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))

section Inst

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [h : EllAdicSite B ℓ]

instance (n : ℕ) (S T : B.Scheme) (f : T ⟶ S) :
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint :=
  h.isRightAdjoint n S T f

instance (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property) :
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) :=
  h.hasWeakSheafifyOver n T V

instance (n : ℕ) (T : B.Scheme) :
    HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) :=
  h.hasWeakSheafify n T

end Inst

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime] [EllAdicSite B ℓ]
  (X : B.Scheme) [IsNoetherian X.1]
  {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) [IsProper f]
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- `H^i(X_{k̄}, ℤ_ℓ)` of a proper `k`-scheme, via the identity compactification. -/
noncomputable def cohomologyZl (i : ℤ) : ModuleCat.{u + 1} ℤ_[ℓ] :=
  LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f
    (CompactificationOf.ofIsProper f) kbar (LAdicSheaf.constantSystem B X ℓ) i

/-- `H^i(X_{k̄}, ℚ_ℓ)`. -/
noncomputable def cohomologyQl (i : ℤ) : ModuleCat.{u + 1} ℚ_[ℓ] :=
  LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
    (CompactificationOf.ofIsProper f) kbar (LAdicSheaf.constantSystem B X ℓ) i

section Galois

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat

local instance (priority := 3000) etaleModules_enoughInjectives_abelian (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

local instance (priority := 3000) galoisModules_enoughInjectives_abelian (Λ : Type) [Ring Λ]
    (k : Type u) [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar] :
    EnoughInjectives (GaloisModules Λ k kbar) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)

variable [Algebra.IsSeparable k kbar] (j : CompactificationOf (Over.mk f))

/-- `H^i_c(X_{k̄}, -)` of a level sheaf of `ℤ_ℓ`-modules, as a discrete Galois module: the `i`-th
cohomology of the library's Galois-equivariant `RΓ^Gal_c(X_{k̄}, -)`
(`Stacks.EtaleCohomology.galoisDerivedCompactSupport`). -/
noncomputable def galoisLevelCohomology (i : ℤ) :
    Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} ℤ_[ℓ]) ⥤
      GaloisModules ℤ_[ℓ] k kbar :=
  padicCoefficientComplex B X ℓ ⋙
    (etaleModuleExtensionByZero.{u, 0} ℤ_[ℓ] j.immersion).mapCochainComplexPlus ⋙
    DerivedCategory.Plus.Q ⋙ galoisDerivedGlobalSections ℤ_[ℓ] (Over.mk j.toBase) kbar ⋙
    DerivedCategory.Plus.homologyFunctor (GaloisModules ℤ_[ℓ] k kbar) i

/-- **The two presentations of `RΓ_c(X_{k̄}, -)` agree, naturally in the complex.**  The library's
`compactSupportFrobeniusFunctor` (the functor behind
`LAdicSheaf.geometricCompactlySupportedCohomology`) is `RΓ(Spec k̄, Rπ_* (j_! K)|_{X̄_k̄})`,
while the Galois-equivariant `galoisDerivedCompactSupport` is `RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})`; they
differ by the composition isomorphism
`RΓ(X̄_k̄, -) ≅ Rπ_* ⋙ RΓ(Spec k̄, -)` (`etaleModuleDerivedGlobalSectionsCompIso`). -/
noncomputable def compactSupportComparison :
    compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar ≅
      (etaleModuleExtensionByZero.{u, 0} ℤ_[ℓ] j.immersion).mapCochainComplexPlus ⋙
        fieldBaseChangeRestrictionFunctor.{u, 0} ℤ_[ℓ] (Over.mk j.toBase) kbar ⋙
        etaleModuleDerivedGlobalSections.{u, 0} ℤ_[ℓ]
          (fieldBaseChange (Over.mk j.toBase) kbar) :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
    (etaleModuleDerivedGlobalSectionsCompIso.{u, 0} ℤ_[ℓ]
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).symm)

omit [EllAdicSite B ℓ] [AlgebraicGeometry.IsNoetherian X.1] [IsProper f] in
/-- The value of `galoisLevelCohomology` on a level sheaf `G` is the `i`-th cohomology of the
library's `galoisDerivedCompactSupport` of `G` (placed in degree `0`). -/
theorem galoisLevelCohomology_obj (i : ℤ)
    (G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} ℤ_[ℓ])) :
    (galoisLevelCohomology B ℓ X f kbar j i).obj G =
      (DerivedCategory.Plus.homologyFunctor (GaloisModules ℤ_[ℓ] k kbar) i).obj
        (galoisDerivedCompactSupport ℤ_[ℓ] f j kbar ((padicCoefficientComplex B X ℓ).obj G)) :=
  rfl

/-- **Forgetting the Galois action commutes with cohomology**, as functors on bounded below
derived categories: `Hⁱ_Gal ⋙ U ≅ U⁺ ⋙ Hⁱ` (the library's `derivedHomologyIso` for the exact
functor `U`). -/
noncomputable def homologyForgetIso (i : ℤ) :
    DerivedCategory.Plus.homologyFunctor (GaloisModules ℤ_[ℓ] k kbar) i ⋙
        Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} ℤ_[ℓ] (kbar ≃ₐ[k] kbar) ≅
      (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} ℤ_[ℓ]
        (kbar ≃ₐ[k] kbar)).mapDerivedCategoryPlus ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i :=
  (Functor.isoWhiskerLeft DerivedCategory.Plus.ι
    (Stacks.DerivedFunctor.derivedHomologyIso
      (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} ℤ_[ℓ]
        (kbar ≃ₐ[k] kbar)) i)).symm

/-- **The Galois-equivariant and the geometric `H^i_c(X_{k̄}, -)` agree**, naturally in the level
sheaf: forgetting the Galois action on `Hⁱ(RΓ^Gal_c(X_{k̄}, -))` gives
`geometricCompactSupportPadicCohomology`. -/
noncomputable def galoisLevelForgetIso (i : ℤ) :
    galoisLevelCohomology B ℓ X f kbar j i ⋙
        Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} ℤ_[ℓ] (kbar ≃ₐ[k] kbar) ≅
      geometricCompactSupportPadicCohomology B X ℓ f j kbar i :=
  Functor.isoWhiskerLeft (padicCoefficientComplex B X ℓ)
    (Functor.isoWhiskerLeft ((etaleModuleExtensionByZero.{u, 0} ℤ_[ℓ]
        j.immersion).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⋙
        galoisDerivedGlobalSections ℤ_[ℓ] (Over.mk j.toBase) kbar)
      (homologyForgetIso ℓ kbar i) ≪≫
    Functor.isoWhiskerRight
      (galoisCompactSupportForgetNatIso ℤ_[ℓ] f j kbar ≪≫
        (compactSupportComparison B ℓ X f kbar j).symm)
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i))

/-- The finite levels `F₀ ⟵ F₁ ⟵ ⋯` of an `ℓ`-adic sheaf, as an inverse system of sheaves of
`ℤ_ℓ`-modules. -/
noncomputable def padicLevelSystem (F : LAdicSheaf B X ℓ) :
    ℕᵒᵖ ⥤ Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} ℤ_[ℓ]) :=
  Functor.ofOpSequence (X := fun n => LAdicSheaf.padicLevel B X ℓ F n)
    (fun n => LAdicSheaf.padicTransition B X ℓ F n)

theorem padicLevelSystem_map_succ (F : LAdicSheaf B X ℓ) (n : ℕ) :
    (padicLevelSystem B ℓ X F).map (homOfLE (n.le_add_right 1)).op =
      LAdicSheaf.padicTransition B X ℓ F n :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- A discrete Galois module is a `ℤ_ℓ`-module with an action of the Galois group. -/
noncomputable abbrev galoisModuleToAction : GaloisModules ℤ_[ℓ] k kbar ⥤
    Action (ModuleCat.{u + 1} ℤ_[ℓ]) (kbar ≃ₐ[k] kbar) :=
  ObjectProperty.ι _ ⋙ ObjectProperty.ι _

/-- The inverse system `n ↦ H^i_c(X_{k̄}, Fₙ)` of Galois modules. -/
noncomputable def galoisCohomologySystem (F : LAdicSheaf B X ℓ) (i : ℤ) :
    ℕᵒᵖ ⥤ Action (ModuleCat.{u + 1} ℤ_[ℓ]) (kbar ≃ₐ[k] kbar) :=
  padicLevelSystem B ℓ X F ⋙ galoisLevelCohomology B ℓ X f kbar j i ⋙
    galoisModuleToAction ℓ kbar

/-- `H^i_c(X_{k̄}, F) = lim_n H^i_c(X_{k̄}, Fₙ)` with its action of `Gal(k̄/k)`. -/
noncomputable def galoisCohomologyZl (F : LAdicSheaf B X ℓ) (i : ℤ) :
    Action (ModuleCat.{u + 1} ℤ_[ℓ]) (kbar ≃ₐ[k] kbar) :=
  limit (galoisCohomologySystem B ℓ X f kbar j F i)

/-- The comparison of the inverse systems `n ↦ H^i_c(X_{k̄}, Fₙ)`, componentwise
`galoisLevelForgetIso`; naturality in `n` needs only the transition maps. -/
noncomputable def galoisCohomologySystemForgetHom (F : LAdicSheaf B X ℓ) (i : ℤ) :
    galoisCohomologySystem B ℓ X f kbar j F i ⋙
        Action.forget (ModuleCat.{u + 1} ℤ_[ℓ]) (kbar ≃ₐ[k] kbar) ⟶
      LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i :=
  NatTrans.ofOpSequence
    (fun n => (galoisLevelForgetIso B ℓ X f kbar j i).hom.app (LAdicSheaf.padicLevel B X ℓ F n))
    (fun n => by
      have h := (galoisLevelForgetIso B ℓ X f kbar j i).hom.naturality
        (LAdicSheaf.padicTransition B X ℓ F n)
      rw [LAdicSheaf.geometricCompactlySupportedCohomologySystem_map_succ]
      change (galoisLevelCohomology B ℓ X f kbar j i ⋙
        Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} ℤ_[ℓ]
          (kbar ≃ₐ[k] kbar)).map ((padicLevelSystem B ℓ X F).map
            (homOfLE (n.le_add_right 1)).op) ≫ _ = _
      rw [padicLevelSystem_map_succ]
      exact h)

instance (F : LAdicSheaf B X ℓ) (i : ℤ) :
    IsIso (galoisCohomologySystemForgetHom B ℓ X f kbar j F i) :=
  haveI : ∀ n : ℕᵒᵖ, IsIso ((galoisCohomologySystemForgetHom B ℓ X f kbar j F i).app n) :=
    fun n => inferInstanceAs (IsIso ((galoisLevelForgetIso B ℓ X f kbar j i).hom.app
      (LAdicSheaf.padicLevel B X ℓ F n.unop)))
  NatIso.isIso_of_isIso_app _

/-- **The underlying `ℤ_ℓ`-module of `H^i_c(X_{k̄}, F) = lim_n H^i_c(X_{k̄}, Fₙ)` with its Galois
action is the library's `geometricCompactlySupportedCohomology`** (Tag 03UT): forgetting the
action preserves the limit and identifies the two inverse systems. -/
noncomputable def galoisCohomologyForgetIso (F : LAdicSheaf B X ℓ) (i : ℤ) :
    (Action.forget (ModuleCat.{u + 1} ℤ_[ℓ]) (kbar ≃ₐ[k] kbar)).obj
        (galoisCohomologyZl B ℓ X f kbar j F i) ≅
      LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F i :=
  preservesLimitIso (Action.forget (ModuleCat.{u + 1} ℤ_[ℓ]) (kbar ≃ₐ[k] kbar))
      (galoisCohomologySystem B ℓ X f kbar j F i) ≪≫
    HasLimit.isoOfNatIso (asIso (galoisCohomologySystemForgetHom B ℓ X f kbar j F i))

end Galois

section Rationalisation

variable {G : Type*} [Group G]

/-- The `ℚ_ℓ`-vector space `A ⊗_{ℤ_ℓ} ℚ_ℓ` underlying a `ℤ_ℓ`-linear `G`-representation. -/
noncomputable def ratSpace (A : Action (ModuleCat.{u + 1} ℤ_[ℓ]) G) : ModuleCat.{u + 1} ℚ_[ℓ] :=
  (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj A.V

/-- The extension of scalars of a `ℤ_ℓ`-linear representation to `ℚ_ℓ`. -/
noncomputable def ratRep (A : Action (ModuleCat.{u + 1} ℤ_[ℓ]) G) :
    Representation ℚ_[ℓ] G (ratSpace ℓ A) where
  toFun g := ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
    (A.ρ g).asHom).hom
  map_one' := by
    have h : (A.ρ 1).asHom = 𝟙 _ := by rw [map_one]; rfl
    rw [h, CategoryTheory.Functor.map_id]
    rfl
  map_mul' g h := by
    have e : (A.ρ (g * h)).asHom = (A.ρ h).asHom ≫ (A.ρ g).asHom := by rw [map_mul]; rfl
    rw [e, CategoryTheory.Functor.map_comp]
    rfl

end Rationalisation

section Twist

variable (k)

/-- The `ℓ`-adic cyclotomic character of `Gal(k̄/k)`, valued in `ℚ_ℓˣ`
(Mathlib's `cyclotomicCharacter`, composed with `ℤ_ℓˣ ↪ ℚ_ℓˣ`). -/
noncomputable def cyclotomicCharacterQl : (kbar ≃ₐ[k] kbar) →* ℚ_[ℓ]ˣ :=
  (Units.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toMonoidHom).comp
    ((cyclotomicCharacter kbar ℓ).comp (MulSemiringAction.toRingAut (kbar ≃ₐ[k] kbar) kbar))

/-- **The Tate twist `ℚ_ℓ(c)`**: the one-dimensional `ℚ_ℓ`-representation of `Gal(k̄/k)` on which
`σ` acts as multiplication by `χ_ℓ(σ)^c`. -/
noncomputable def tateTwistQlRep (c : ℕ) : Representation ℚ_[ℓ] (kbar ≃ₐ[k] kbar) ℚ_[ℓ] where
  toFun σ := (((cyclotomicCharacterQl ℓ k kbar σ ^ c : ℚ_[ℓ]ˣ) : ℚ_[ℓ])) • LinearMap.id
  map_one' := by simp; rfl
  map_mul' σ τ := by
    ext
    simp [mul_pow, mul_comm]

/-- The twist `V(c) = V ⊗_{ℚ_ℓ} ℚ_ℓ(c)` of a `ℚ_ℓ`-representation of `Gal(k̄/k)`: the diagonal
action on the tensor product. -/
noncomputable def twistRep {V : Type*} [AddCommGroup V] [Module ℚ_[ℓ] V]
    (ρ : Representation ℚ_[ℓ] (kbar ≃ₐ[k] kbar) V) (c : ℕ) :
    Representation ℚ_[ℓ] (kbar ≃ₐ[k] kbar) (TensorProduct ℚ_[ℓ] V ℚ_[ℓ]) :=
  ρ.tprod (tateTwistQlRep ℓ k kbar c)

end Twist

section Abelian

variable [Algebra.IsSeparable k kbar]

/-- **`H^{2c}_{ét}(X_{k̄}, ℚ_ℓ)`** of a proper `k`-scheme `X` (identity compactification,
constant `ℓ`-adic coefficients), the `ℚ_ℓ`-vector space of the Stacks `ℓ`-adic cohomology
`lim_n H^{2c}(X_{k̄}, ℤ/ℓ^{n+1})` with `ℚ_ℓ` coefficients, carrying its action of `Gal(k̄/k)`. -/
noncomputable abbrev etaleCohomologyQlSpace (c : ℕ) : ModuleCat.{u + 1} ℚ_[ℓ] :=
  ratSpace ℓ (galoisCohomologyZl B ℓ X f kbar (CompactificationOf.ofIsProper f)
    (LAdicSheaf.constantSystem B X ℓ) (2 * c : ℕ))

/-- **`H^{2c}_{ét}(X_{k̄}, ℚ_ℓ)` is the library's `H^{2c}_c(X_{k̄}, ℚ_ℓ)`**
(`rationalGeometricCompactlySupportedCohomology`, Tag 03UT), as `ℚ_ℓ`-vector spaces: the
extension of scalars of `galoisCohomologyForgetIso`. -/
noncomputable def etaleCohomologyQlSpaceIso (c : ℕ) :
    etaleCohomologyQlSpace B ℓ X f kbar c ≅ cohomologyQl B ℓ X f kbar (2 * c : ℕ) :=
  (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).mapIso
    (galoisCohomologyForgetIso B ℓ X f kbar (CompactificationOf.ofIsProper f)
      (LAdicSheaf.constantSystem B X ℓ) (2 * c : ℕ))

/-- The Galois representation on `H^{2c}_{ét}(X_{k̄}, ℚ_ℓ)`. -/
noncomputable def etaleCohomologyQlRep (c : ℕ) :
    Representation ℚ_[ℓ] (kbar ≃ₐ[k] kbar) (etaleCohomologyQlSpace B ℓ X f kbar c) :=
  ratRep ℓ (galoisCohomologyZl B ℓ X f kbar (CompactificationOf.ofIsProper f)
    (LAdicSheaf.constantSystem B X ℓ) (2 * c : ℕ))

/-- **`H^{2c}_{ét}(X_{k̄}, ℚ_ℓ(c))`**: `H^{2c}_{ét}(X_{k̄}, ℚ_ℓ) ⊗_{ℚ_ℓ} ℚ_ℓ(c)`, the target of the
cycle class map in codimension `c`. -/
abbrev etaleCohomologyTwistSpace (c : ℕ) : Type _ :=
  TensorProduct ℚ_[ℓ] (etaleCohomologyQlSpace B ℓ X f kbar c) ℚ_[ℓ]

/-- The Galois representation on `H^{2c}_{ét}(X_{k̄}, ℚ_ℓ(c))` (diagonal action). -/
noncomputable def etaleCohomologyTwistRep (c : ℕ) :
    Representation ℚ_[ℓ] (kbar ≃ₐ[k] kbar) (etaleCohomologyTwistSpace B ℓ X f kbar c) :=
  twistRep ℓ k kbar (etaleCohomologyQlRep B ℓ X f kbar c) c

/-- The `Gal(k̄/k)`-invariants `H^{2c}_{ét}(X_{k̄}, ℚ_ℓ(c))^{Gal(k̄/k)}` (the target of the
cycle class map in Corollary 6.6). -/
noncomputable abbrev etaleCohomologyTwistInvariants (c : ℕ) :
    Submodule ℚ_[ℓ] (etaleCohomologyTwistSpace B ℓ X f kbar c) :=
  (etaleCohomologyTwistRep B ℓ X f kbar c).invariants

end Abelian

section LevelBridge

open Opposite CategoryTheory.Abelian

variable [Algebra.IsSeparable k kbar]

/-- The inverse system `n ↦ H^i_c(X_{k̄}, ℤ/ℓⁿ⁺¹)` of discrete Galois modules whose limit is
`galoisCohomologyZl` (identity compactification, constant `ℓ`-adic sheaf). -/
noncomputable abbrev constantLevelSystem (i : ℤ) :
    ℕᵒᵖ ⥤ Action (ModuleCat.{u + 1} ℤ_[ℓ]) (kbar ≃ₐ[k] kbar) :=
  galoisCohomologySystem B ℓ X f kbar (CompactificationOf.ofIsProper f)
    (LAdicSheaf.constantSystem B X ℓ) i

/-- `H^i_{ét}(X_{k̄}, ℤ_ℓ) = lim_n H^i(X_{k̄}, ℤ/ℓⁿ⁺¹)` with its Galois action. -/
noncomputable abbrev constantLimit (i : ℤ) : Action (ModuleCat.{u + 1} ℤ_[ℓ]) (kbar ≃ₐ[k] kbar) :=
  galoisCohomologyZl B ℓ X f kbar (CompactificationOf.ofIsProper f)
    (LAdicSheaf.constantSystem B X ℓ) i

/-- The `n`-th level `H^i(X_{k̄}, ℤ/ℓⁿ⁺¹)` as a `ℤ_ℓ`-module. -/
noncomputable abbrev levelModule (i : ℤ) (n : ℕ) : ModuleCat.{u + 1} ℤ_[ℓ] :=
  (Action.forget (ModuleCat.{u + 1} ℤ_[ℓ]) (kbar ≃ₐ[k] kbar)).obj
    ((constantLevelSystem B ℓ X f kbar i).obj (op n))

/-- **The projection of the `ℓ`-adic cohomology onto its `n`-th finite level.** -/
noncomputable def levelProj (i : ℤ) (n : ℕ) :
    (constantLimit B ℓ X f kbar i).V ⟶ levelModule B ℓ X f kbar i n :=
  (limit.π (constantLevelSystem B ℓ X f kbar i) (op n)).hom

/-- The projection to a finite level is Galois-equivariant. -/
theorem levelProj_comm (i : ℤ) (n : ℕ) (σ : kbar ≃ₐ[k] kbar)
    (x : (constantLimit B ℓ X f kbar i).V) :
    (levelProj B ℓ X f kbar i n).hom (((constantLimit B ℓ X f kbar i).ρ σ).asHom.hom x) =
      ((((constantLevelSystem B ℓ X f kbar i).obj (op n)).ρ σ).asHom.hom
        ((levelProj B ℓ X f kbar i n).hom x)) :=
  congrArg (fun φ => φ.hom x) ((limit.π (constantLevelSystem B ℓ X f kbar i) (op n)).comm σ)

/-- **Elements of the `ℓ`-adic cohomology are determined by their finite-level components.** -/
theorem levelProj_ext (i : ℤ) {x y : (constantLimit B ℓ X f kbar i).V}
    (h : ∀ n, (levelProj B ℓ X f kbar i n).hom x = (levelProj B ℓ X f kbar i n).hom y) :
    x = y := by
  let G := Action.forget (ModuleCat.{u + 1} ℤ_[ℓ]) (kbar ≃ₐ[k] kbar)
  let e := preservesLimitIso G (constantLevelSystem B ℓ X f kbar i)
  have hπ : ∀ n, e.hom ≫ limit.π (constantLevelSystem B ℓ X f kbar i ⋙ G) (op n) =
      levelProj B ℓ X f kbar i n := fun n => by
    simp [e, levelProj, G]
  have hxy : e.hom.hom x = e.hom.hom y := by
    refine Concrete.limit_ext _ _ _ fun j => ?_
    obtain ⟨n⟩ := j
    have h1 : (limit.π (constantLevelSystem B ℓ X f kbar i ⋙ G) (op n)).hom (e.hom.hom x) =
        (levelProj B ℓ X f kbar i n).hom x := congrArg (fun φ => φ.hom x) (hπ n)
    have h2 : (limit.π (constantLevelSystem B ℓ X f kbar i ⋙ G) (op n)).hom (e.hom.hom y) =
        (levelProj B ℓ X f kbar i n).hom y := congrArg (fun φ => φ.hom y) (hπ n)
    exact h1.trans ((h n).trans h2.symm)
  exact e.toLinearEquiv.injective hxy

/-- **The finite level `n` of `H^i(X_{k̄}, ℤ_ℓ)` is `Ext^i(ℤ/ℓⁿ⁺¹, ℤ/ℓⁿ⁺¹)` on `X_{k̄}`**: the
library's `LAdicSheaf.constantLevelCohomologyAddEquiv`, read through the identification
`galoisCohomologySystemForgetHom` of the Galois-equivariant levels with the library's levels. -/
noncomputable def levelExtEquiv (i n : ℕ) :
    levelModule B ℓ X f kbar (i : ℤ) n ≃+
      (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf
          (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) i).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) :=
  ((asIso (galoisCohomologySystemForgetHom B ℓ X f kbar (CompactificationOf.ofIsProper f)
    (LAdicSheaf.constantSystem B X ℓ) (i : ℤ))).app (op n)).toLinearEquiv.toAddEquiv.trans
    (LAdicSheaf.constantLevelCohomologyAddEquiv B X ℓ f kbar i n)

/-- The vector `1 ⊗ x ∈ A ⊗_{ℤ_ℓ} ℚ_ℓ` (the unit of extension of scalars), additively. -/
noncomputable def ratMk {G : Type*} [Group G] (A : Action (ModuleCat.{u + 1} ℤ_[ℓ]) G) :
    A.V →+ ratSpace ℓ A :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap ℤ_[ℓ] ℚ_[ℓ])).unit.app A.V).hom.toAddMonoidHom

theorem ratRep_ratMk {G : Type*} [Group G] (A : Action (ModuleCat.{u + 1} ℤ_[ℓ]) G) (g : G)
    (x : A.V) : ratRep ℓ A g (ratMk ℓ A x) = ratMk ℓ A ((A.ρ g).asHom.hom x) :=
  rfl

/-- **The rational twisted class `x ⊗ 1 ∈ H^{2c}(X_{k̄}, ℚ_ℓ) ⊗ ℚ_ℓ(c)` of an `ℓ`-adic class.**  The
identification of the twist `ℚ_ℓ(c)` with `ℚ_ℓ` (the line `ℚ_ℓ · 1`, on which `σ` acts by
`χ_ℓ(σ)^c`) is the choice of the compatible system of roots of unity used to normalise the
finite-level classes. -/
noncomputable def twistMk (c : ℕ) :
    (constantLimit B ℓ X f kbar ((2 * c : ℕ) : ℤ)).V →+ etaleCohomologyTwistSpace B ℓ X f kbar c :=
  (((TensorProduct.mk ℚ_[ℓ] (etaleCohomologyQlSpace B ℓ X f kbar c) ℚ_[ℓ]).flip
    (1 : ℚ_[ℓ])).toAddMonoidHom).comp (ratMk ℓ _)

/-- Galois transformation law of `twistMk`: `σ (x ⊗ 1) = χ_ℓ(σ)^c · (σ x ⊗ 1)`. -/
theorem twistRep_twistMk (c : ℕ) (σ : kbar ≃ₐ[k] kbar)
    (x : (constantLimit B ℓ X f kbar ((2 * c : ℕ) : ℤ)).V) :
    etaleCohomologyTwistRep B ℓ X f kbar c σ (twistMk B ℓ X f kbar c x) =
      ((cyclotomicCharacterQl ℓ k kbar σ ^ c : ℚ_[ℓ]ˣ) : ℚ_[ℓ]) •
        twistMk B ℓ X f kbar c
          (((constantLimit B ℓ X f kbar ((2 * c : ℕ) : ℤ)).ρ σ).asHom.hom x) := by
  have h1 : tateTwistQlRep ℓ k kbar c σ (1 : ℚ_[ℓ]) =
      ((cyclotomicCharacterQl ℓ k kbar σ ^ c : ℚ_[ℓ]ˣ) : ℚ_[ℓ]) • (1 : ℚ_[ℓ]) := by
    simp [tateTwistQlRep]
  simp only [twistMk, etaleCohomologyTwistRep, twistRep, etaleCohomologyQlRep,
    AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
    LinearMap.flip_apply, TensorProduct.mk_apply,
    Representation.tprod_apply, TensorProduct.map_tmul, ratRep_ratMk, h1]
  rw [TensorProduct.tmul_smul]

theorem twistMk_smul (c : ℕ) (a : ℤ_[ℓ])
    (x : (constantLimit B ℓ X f kbar ((2 * c : ℕ) : ℤ)).V) :
    twistMk B ℓ X f kbar c (a • x) = algebraMap ℤ_[ℓ] ℚ_[ℓ] a • twistMk B ℓ X f kbar c x := by
  have hrat := ((ModuleCat.extendRestrictScalarsAdj (algebraMap ℤ_[ℓ] ℚ_[ℓ])).unit.app
    (constantLimit B ℓ X f kbar ((2 * c : ℕ) : ℤ)).V).hom.map_smul a x
  change ratMk ℓ (constantLimit B ℓ X f kbar ((2 * c : ℕ) : ℤ)) (a • x) =
    algebraMap ℤ_[ℓ] ℚ_[ℓ] a • ratMk ℓ (constantLimit B ℓ X f kbar ((2 * c : ℕ) : ℤ)) x at hrat
  simp only [twistMk, AddMonoidHom.coe_comp, Function.comp_apply,
    LinearMap.toAddMonoidHom_coe, LinearMap.flip_apply, TensorProduct.mk_apply, hrat]
  exact TensorProduct.smul_tmul' _ _ _

end LevelBridge

/-! ### The scalar Tate twist is the library's Tate twist, level by level

The twist `tateTwistQlRep` above is the one-dimensional representation `χ_ℓ^c`.  The library's
twist is `Stacks.EtaleCohomology.tateTwistNegOne` (Tag 03VK; `Hom(μₙ, M)` of
`Stacks.EtaleCohomology.rootsOfUnityHomRepresentation`, `σ ↦ f ↦ τ(σ) ∘ f ∘ σ⁻¹`, equal to
`χ_{cycl}(σ)⁻¹ τ(σ)` after evaluating at a primitive root).  This section proves that the `ℓ`-adic
scalar character reduces, modulo every `ℓⁿ`, to the library's mod-`ℓⁿ` cyclotomic character
`Stacks.EtaleCohomology.cyclotomicCharacterModN`, hence that the library's `M(-1)` is the scalar
twist by `χ_ℓ⁻¹` on every `ℤ/ℓⁿ`-representation, and that the `+1` twist `tateTwistPos` is its
two-sided inverse.  So `M(c)`, `c ∈ ℤ`, is the `|c|`-fold iterate of the library's twist (or its
inverse), with no choice involved: the scalar twist of `etaleCohomologyTwistRep` is, level by level,
the library's twist.  What this does *not* do is compute the Galois action on the cohomology of the
twisted *sheaf* `Hom(μ, F)` on a general `X`; the library proves that identification only for
`H²_c` of a curve (`AlgebraicGeometry.compactSupportCanonicalTwistEquiv_galois`, Tag 03VK), and
general cycle systems are explicit existence inputs in `External.lean`. -/

section TwistComparison

open Stacks.EtaleCohomology

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- The `ℓ`-adic cyclotomic character of `Gal(k̄/k)` with values in `ℤ_ℓˣ`. -/
noncomputable def cyclotomicCharacterZl : (kbar ≃ₐ[k] kbar) →* ℤ_[ℓ]ˣ :=
  (cyclotomicCharacter kbar ℓ).comp (MulSemiringAction.toRingAut (kbar ≃ₐ[k] kbar) kbar)

omit [Fact ℓ.Prime] in
/-- The `ℚ_ℓ`-valued character used by `tateTwistQlRep` is the `ℤ_ℓˣ`-valued one, composed with
the inclusion `ℤ_ℓˣ ↪ ℚ_ℓˣ`. -/
theorem cyclotomicCharacterQl_eq [Fact ℓ.Prime] :
    cyclotomicCharacterQl ℓ k kbar =
      (Units.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toMonoidHom).comp (cyclotomicCharacterZl ℓ k kbar) :=
  rfl

variable [IsSepClosed kbar] [NeZero (ℓ : kbar)]

local instance neZero_pow_aux (n : ℕ) : NeZero (ℓ ^ n) :=
  ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩

local instance neZero_natCast_pow_aux (n : ℕ) : NeZero (((ℓ ^ n : ℕ) : kbar)) :=
  ⟨by rw [Nat.cast_pow]; exact pow_ne_zero _ (NeZero.ne _)⟩

/-- **The `ℓ`-adic cyclotomic character reduces modulo `ℓⁿ` to the library's mod-`ℓⁿ`
cyclotomic character.** -/
theorem cyclotomicCharacterZl_toZModPow (n : ℕ) (σ : kbar ≃ₐ[k] kbar) :
    (cyclotomicCharacterZl ℓ k kbar σ : ℤ_[ℓ]).toZModPow n =
      ((cyclotomicCharacterModN k kbar (ℓ ^ n) σ : (ZMod (ℓ ^ n))ˣ) : ZMod (ℓ ^ n)) := by
  have h := cyclotomicCharacter.toZModPow (L := kbar) ℓ (n := n) (galoisRingEquivHom k kbar σ)
  exact h

/-- The reduction of the units `ℤ_ℓˣ → (ℤ/ℓⁿ)ˣ` carries `χ_ℓ` to `χ_{ℓⁿ}`. -/
theorem units_map_cyclotomicCharacterZl (n : ℕ) (σ : kbar ≃ₐ[k] kbar) :
    Units.map (PadicInt.toZModPow (p := ℓ) n).toMonoidHom (cyclotomicCharacterZl ℓ k kbar σ) =
      cyclotomicCharacterModN k kbar (ℓ ^ n) σ :=
  Units.ext (cyclotomicCharacterZl_toZModPow ℓ k kbar n σ)

/-- **The library's twist by `-1` is the scalar twist by `χ_ℓ⁻¹`**: on a `ℤ/ℓⁿ`-representation
`τ`, `Stacks.EtaleCohomology.tateTwistNegOne` multiplies `τ(σ)` by the reduction modulo `ℓⁿ` of
`χ_ℓ(σ)⁻¹ ∈ ℤ_ℓ`. -/
theorem tateTwistNegOne_apply_zl (n : ℕ) {M : Type*} [AddCommGroup M] [Module (ZMod (ℓ ^ n)) M]
    (τ : Representation (ZMod (ℓ ^ n)) (kbar ≃ₐ[k] kbar) M) (σ : kbar ≃ₐ[k] kbar) (m : M) :
    tateTwistNegOne k kbar (ℓ ^ n) (ZMod (ℓ ^ n)) τ σ m =
      (PadicInt.toZModPow (p := ℓ) n ((cyclotomicCharacterZl ℓ k kbar σ)⁻¹ : ℤ_[ℓ]ˣ)) •
        τ σ m := by
  rw [tateTwistNegOne_apply, Algebra.algebraMap_self_apply]
  congr 2
  rw [← units_map_cyclotomicCharacterZl ℓ k kbar n σ, ← map_inv]
  rfl

/-- **The twist by `+1` of a Galois module over `ℤ/n`**: `σ` acts as `χ_{cycl}(σ) · τ(σ)`. -/
noncomputable def tateTwistPos (n : ℕ) [NeZero n] [NeZero (n : kbar)]
    (Λ : Type*) [Ring Λ] [Algebra (ZMod n) Λ] {M : Type*} [AddCommGroup M] [Module Λ M]
    (τ : Representation Λ (kbar ≃ₐ[k] kbar) M) : Representation Λ (kbar ≃ₐ[k] kbar) M where
  toFun σ := (centralScalar n Λ M ((cyclotomicCharacterModN k kbar n σ : (ZMod n)ˣ) :
    ZMod n)).comp (τ σ)
  map_one' := by
    refine LinearMap.ext fun m => ?_
    change centralScalar n Λ M ((cyclotomicCharacterModN k kbar n 1 : (ZMod n)ˣ) : ZMod n)
      (τ 1 m) = m
    rw [map_one, map_one]
    simp
  map_mul' σ σ' := by
    refine LinearMap.ext fun m => ?_
    change algebraMap (ZMod n) Λ ((cyclotomicCharacterModN k kbar n (σ * σ') : (ZMod n)ˣ) :
        ZMod n) • τ (σ * σ') m =
      algebraMap (ZMod n) Λ ((cyclotomicCharacterModN k kbar n σ : (ZMod n)ˣ) : ZMod n) •
        τ σ (algebraMap (ZMod n) Λ ((cyclotomicCharacterModN k kbar n σ' : (ZMod n)ˣ) :
          ZMod n) • τ σ' m)
    rw [map_smul, smul_smul, ← map_mul, ← Units.val_mul,
      ← map_mul (cyclotomicCharacterModN k kbar n), map_mul τ]
    rfl

/-- **`tateTwistPos` is a right inverse of the library's twist by `-1`**: twisting by `+1` and then
by `-1` is the identity. -/
theorem tateTwistNegOne_tateTwistPos (n : ℕ) [NeZero n] [NeZero (n : kbar)] (Λ : Type*) [Ring Λ]
    [Algebra (ZMod n) Λ] {M : Type*} [AddCommGroup M] [Module Λ M]
    (τ : Representation Λ (kbar ≃ₐ[k] kbar) M) :
    tateTwistNegOne k kbar n Λ (tateTwistPos k kbar n Λ τ) = τ := by
  ext σ m
  exact centralScalar_units_inv_centralScalar n Λ M _ (τ σ m)

/-- **`tateTwistPos` is a left inverse of the library's twist by `-1`.** -/
theorem tateTwistPos_tateTwistNegOne (n : ℕ) [NeZero n] [NeZero (n : kbar)] (Λ : Type*) [Ring Λ]
    [Algebra (ZMod n) Λ] {M : Type*} [AddCommGroup M] [Module Λ M]
    (τ : Representation Λ (kbar ≃ₐ[k] kbar) M) :
    tateTwistPos k kbar n Λ (tateTwistNegOne k kbar n Λ τ) = τ := by
  ext σ m
  change algebraMap (ZMod n) Λ ((cyclotomicCharacterModN k kbar n σ : (ZMod n)ˣ) : ZMod n) •
    (algebraMap (ZMod n) Λ (((cyclotomicCharacterModN k kbar n σ)⁻¹ : (ZMod n)ˣ) : ZMod n) •
      τ σ m) = τ σ m
  rw [smul_smul, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, one_smul]

end TwistComparison

end ArithmeticOfJacobiPolynomials.AbelianEtale
