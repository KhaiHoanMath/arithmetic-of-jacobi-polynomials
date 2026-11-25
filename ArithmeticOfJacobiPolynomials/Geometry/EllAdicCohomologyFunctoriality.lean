/- Assembled by AxiomProver. -/
module

public import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Functoriality of `ℓ`-adic cohomology under isomorphisms of schemes

Mathlib defines `X.EllAdicCohomology ℓ n` (`Mathlib/AlgebraicGeometry/Sites/ElladicCohomology`)
as the `n`-th cohomology `Ext^n(ℤ, ℤ_ℓ)` of the sheaf `U ↦ C(U, ℤ_ℓ)` on the small pro-étale
site `X.ProEt`, without any functoriality. This file adds functoriality along isomorphisms.

* **Ext transport** (`ArithmeticOfJacobiPolynomials.extTransport`). For an exact functor `F : 𝒜 ⥤
ℬ` of abelian
  categories and morphisms `c : X' ⟶ F X`, `l : F Y ⟶ Y'`, the additive map
  `Ext^n(X, Y) → Ext^n(X', Y')`, `α ↦ c ∘ F(α) ∘ l`. It is compatible with identities
  (`extTransport_id`), composition of functors (`extTransport_comp`) and natural
  transformations (`extTransport_natTrans`).
* **Sites.** For `e : X ≅ Y`, `proEtMap e : X.ProEt ⥤ Y.ProEt` composes the structure morphism
  with `e`; it is an equivalence of categories (`proEtEquiv e`), it preserves covers
  (`coverPreserving_proEtMap`) and hence is continuous.
* **Sheaves.** `sheafPullback e : Sh(Y.ProEt) ⥤ Sh(X.ProEt)` (restriction along `proEtMap e`) is
  an equivalence of abelian categories (`sheafPullbackEquiv e`). It carries the constant sheaf
  `ℤ` of `Y` to that of `X` (`constSheafPullback e`, induced by sheafification) and the sheaf
  `ℤ_ℓ` of `Y` to that of `X` *on the nose* (`ellSheafPullback e`, an identity morphism: both
  are the restriction of the same sheaf on the big pro-étale site of schemes).
* **Cohomology.** `EllAdicCohomology.pullbackMap e : H^n(Y, ℤ_ℓ) →+ H^n(X, ℤ_ℓ)` and the additive
  equivalence `EllAdicCohomology.mapIso e : H^n(X, ℤ_ℓ) ≃+ H^n(Y, ℤ_ℓ)`. The variance of
  `mapIso` is *covariant* (transport of structure along `e`): `mapIso e` is the pullback along
  `e⁻¹`, and
  `mapIso_refl : mapIso (Iso.refl X) = AddEquiv.refl _`,
  `mapIso_trans : mapIso (e ≪≫ f) = (mapIso e).trans (mapIso f)`.
* **Automorphisms.** `Aut X` acts on `H^n(X, ℤ_ℓ)` by additive automorphisms,
  `x • α = mapIso x α` (`EllAdicCohomology.instDistribMulActionAut`); as a group homomorphism,
  `EllAdicCohomology.autAction X ℓ n : Aut X →* Multiplicative (AddAut (H^n(X, ℤ_ℓ)))`.
-/

public section

open CategoryTheory Limits Abelian AlgebraicGeometry Opposite

universe w u₁ v₁ u₂ v₂ u₃ v₃ u

namespace ArithmeticOfJacobiPolynomials

/-! ### Transport of `Ext` groups along exact functors -/

section ExtTransport

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasExt.{w} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasExt.{w} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasExt.{w} C₃]

/-- For an exact functor `F` and morphisms `c : X' ⟶ F X`, `l : F Y ⟶ Y'`, the additive map
`Ext^n(X, Y) → Ext^n(X', Y')` sending `α` to `c ∘ F(α) ∘ l`. -/
@[expose]
noncomputable def extTransport (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {X Y : C₁} {X' Y' : C₂} (c : X' ⟶ F.obj X)
    (l : F.obj Y ⟶ Y') (n : ℕ) : Ext.{w} X Y n →+ Ext.{w} X' Y' n :=
  ((Ext.mk₀ c).precomp Y' (zero_add n)).comp
    (((Ext.mk₀ l).postcomp (F.obj X) (add_zero n)).comp (F.mapExtAddHom X Y n))

theorem extTransport_apply (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {X Y : C₁} {X' Y' : C₂} (c : X' ⟶ F.obj X)
    (l : F.obj Y ⟶ Y') (n : ℕ) (α : Ext.{w} X Y n) :
    extTransport F c l n α =
      (Ext.mk₀ c).comp ((α.mapExactFunctor F).comp (Ext.mk₀ l) (add_zero n)) (zero_add n) :=
  rfl

/-- Transport along the identity functor and identity morphisms is the identity. -/
theorem extTransport_id {X Y : C₁} (n : ℕ) (α : Ext.{w} X Y n) :
    extTransport (𝟭 C₁) (𝟙 X) (𝟙 Y) n α = α := by
  rw [extTransport_apply]
  exact (Ext.mk₀_id_comp _).trans ((Ext.comp_mk₀_id _).trans (Ext.id_mapExactFunctor α))

/-- Transport is compatible with composition of exact functors. -/
theorem extTransport_comp (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (G : C₂ ⥤ C₃) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] {X Y : C₁} {X' Y' : C₂} {X'' Y'' : C₃}
    (c : X' ⟶ F.obj X) (l : F.obj Y ⟶ Y') (c' : X'' ⟶ G.obj X') (l' : G.obj Y' ⟶ Y'')
    (n : ℕ) (α : Ext.{w} X Y n) :
    extTransport G c' l' n (extTransport F c l n α) =
      extTransport (F ⋙ G) (c' ≫ G.map c) (G.map l ≫ l') n α := by
  rw [extTransport_apply, extTransport_apply, extTransport_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀,
    Ext.comp_mapExactFunctor,
    Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ (G.map c))
      (((α.mapExactFunctor F).mapExactFunctor G).comp (Ext.mk₀ (G.map l)) (add_zero n))
      (Ext.mk₀ l') (zero_add n),
    Ext.comp_assoc_of_third_deg_zero ((α.mapExactFunctor F).mapExactFunctor G)
      (Ext.mk₀ (G.map l)) (Ext.mk₀ l') (add_zero n),
    Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀_assoc]

/-- Transport is invariant under a natural transformation between the functors, when the
morphisms are related accordingly. -/
theorem extTransport_natTrans (F F' : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [F'.Additive] [PreservesFiniteLimits F']
    [PreservesFiniteColimits F'] (τ : F ⟶ F') {X Y : C₁} {X' Y' : C₂}
    (c : X' ⟶ F.obj X) (l : F.obj Y ⟶ Y') (c' : X' ⟶ F'.obj X) (l' : F'.obj Y ⟶ Y')
    (hc : c ≫ τ.app X = c') (hl : l = τ.app Y ≫ l') (n : ℕ) (α : Ext.{w} X Y n) :
    extTransport F c l n α = extTransport F' c' l' n α := by
  subst hc hl
  rw [extTransport_apply, extTransport_apply, ← Ext.mk₀_comp_mk₀ (τ.app Y) l',
    ← Ext.comp_assoc_of_third_deg_zero (α.mapExactFunctor F) (Ext.mk₀ (τ.app Y)) (Ext.mk₀ l')
      (add_zero n),
    Ext.mapExactFunctor_comp_mk₀_natTransApp,
    Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ (τ.app X)) (α.mapExactFunctor F') (Ext.mk₀ l')
      (zero_add n),
    Ext.mk₀_comp_mk₀_assoc]

end ExtTransport

/-! ### The pro-étale site along an isomorphism of schemes -/

namespace ProEtIso

variable {X Y Z : Scheme.{u}}

/-- Weakly étale morphisms are stable under composition. -/
theorem isStableUnderComposition_weaklyEtale :
    MorphismProperty.IsStableUnderComposition @WeaklyEtale where
  comp_mem f g hf hg := by
    have : WeaklyEtale f := hf
    have : WeaklyEtale g := hg
    infer_instance

attribute [local instance] isStableUnderComposition_weaklyEtale

/-- For `e : X ≅ Y`, the functor `X.ProEt ⥤ Y.ProEt` sending `U → X` to `U → X → Y`. -/
@[expose]
noncomputable def proEtMap (e : X ≅ Y) : X.ProEt ⥤ Y.ProEt :=
  MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ (f := e.hom) inferInstance

@[simp]
theorem proEtMap_obj_hom (e : X ≅ Y) (U : X.ProEt) :
    ((proEtMap e).obj U).hom = U.hom ≫ e.hom :=
  rfl

/-- `proEtMap e` commutes (strictly) with the forgetful functors to schemes. -/
theorem proEtMap_comp_forget (e : X ≅ Y) :
    proEtMap e ⋙ Scheme.ProEt.forget Y ⋙ CategoryTheory.Over.forget Y =
      Scheme.ProEt.forget X ⋙ CategoryTheory.Over.forget X :=
  rfl

/-- The comparison `proEtMap e ⋙ proEtMap f ≅ proEtMap g` when `e ≫ f = g`; it is the
identity on underlying schemes. -/
@[expose]
noncomputable def proEtMapComp (e : X ≅ Y) (f : Y ≅ Z) (g : X ≅ Z) (h : e.hom ≫ f.hom = g.hom) :
    proEtMap e ⋙ proEtMap f ≅ proEtMap g :=
  NatIso.ofComponents (fun U => MorphismProperty.Over.isoMk (Iso.refl U.left) (by
    change 𝟙 U.left ≫ U.hom ≫ g.hom = (U.hom ≫ e.hom) ≫ f.hom
    rw [Category.id_comp, ← h, Category.assoc]))

/-- The comparison `proEtMap e ≅ 𝟭` when `e = 𝟙`; it is the identity on underlying schemes. -/
@[expose]
noncomputable def proEtMapId (e : X ≅ X) (h : e.hom = 𝟙 X) : proEtMap e ≅ 𝟭 X.ProEt :=
  NatIso.ofComponents (fun U => MorphismProperty.Over.isoMk (Iso.refl U.left) (by
    change 𝟙 U.left ≫ U.hom = U.hom ≫ e.hom
    rw [Category.id_comp, h]
    exact (Category.comp_id _).symm))
    (fun {U V} φ => by
      apply MorphismProperty.Over.Hom.ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- `proEtMap e` is an equivalence of categories, with inverse `proEtMap e.symm`. -/
@[expose]
noncomputable def proEtEquiv (e : X ≅ Y) : X.ProEt ≌ Y.ProEt :=
  CategoryTheory.Equivalence.mk (proEtMap e) (proEtMap e.symm)
    ((proEtMapId (Iso.refl X) rfl).symm ≪≫ (proEtMapComp e e.symm (Iso.refl X) (by simp)).symm)
    (proEtMapComp e.symm e (Iso.refl Y) (by simp) ≪≫ proEtMapId (Iso.refl Y) rfl)

instance (e : X ≅ Y) : (proEtMap e).IsEquivalence :=
  (proEtEquiv e).isEquivalence_functor

/-- The pro-étale topology of `X` is generated by the covers whose image under `proEtMap e`
are pro-étale covers of `Y`. -/
theorem topology_eq_toGrothendieck_comap (e : X ≅ Y) :
    Scheme.ProEt.topology X =
      ((Scheme.ProEt.precoverage Y).comap (proEtMap e)).toGrothendieck := by
  change (Scheme.proetalePrecoverage.comap
    (Scheme.ProEt.forget X ⋙ CategoryTheory.Over.forget X)).toGrothendieck = _
  rw [Scheme.ProEt.precoverage, ← Precoverage.comap_comp, proEtMap_comp_forget]

/-- `proEtMap e` sends pro-étale covering sieves to pro-étale covering sieves. -/
theorem coverPreserving_proEtMap (e : X ≅ Y) :
    CoverPreserving (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) (proEtMap e) where
  cover_preserve {U S} hS := by
    rw [topology_eq_toGrothendieck_comap e] at hS
    exact (Functor.coverPreserving_restrictedTopology (G := proEtMap e)
      (K := Scheme.ProEt.topology Y)).cover_preserve
      (Precoverage.toGrothendieck_comap_le_restrictedTopology (F := proEtMap e)
        (Scheme.ProEt.precoverage Y) _ hS)

instance isContinuous_proEtMap (e : X ≅ Y) :
    (proEtMap e).IsContinuous (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) :=
  Functor.IsCoverDense.isContinuous (J := Scheme.ProEt.topology X)
    (K := Scheme.ProEt.topology Y) (G := proEtMap e) (coverPreserving_proEtMap e)

/-! ### Abelian sheaves -/

/-- Restriction of abelian sheaves along `proEtMap e`, i.e. pullback along `e : X ≅ Y`. -/
noncomputable abbrev sheafPullback (e : X ≅ Y) :
    Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  (proEtMap e).sheafPushforwardContinuous AddCommGrpCat.{u + 1} (Scheme.ProEt.topology X)
    (Scheme.ProEt.topology Y)

/-- The comparison `sheafPullback f ⋙ sheafPullback e ≅ sheafPullback g` when `e ≫ f = g`. -/
@[expose]
noncomputable def sheafPullbackComp (e : X ≅ Y) (f : Y ≅ Z) (g : X ≅ Z)
    (h : e.hom ≫ f.hom = g.hom) : sheafPullback f ⋙ sheafPullback e ≅ sheafPullback g :=
  letI := Functor.isContinuous_comp (proEtMap e) (proEtMap f) (Scheme.ProEt.topology X)
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Z)
  Functor.sheafPushforwardContinuousComp (proEtMap e) (proEtMap f) AddCommGrpCat.{u + 1}
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Z) ≪≫
  Functor.sheafPushforwardContinuousIso (proEtMapComp e f g h) AddCommGrpCat.{u + 1}
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)

/-- The comparison `sheafPullback e ≅ 𝟭` when `e = 𝟙`. -/
@[expose]
noncomputable def sheafPullbackId (e : X ≅ X) (h : e.hom = 𝟙 X) : sheafPullback e ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousIso (proEtMapId e h) AddCommGrpCat.{u + 1}
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology X) ≪≫
  Functor.sheafPushforwardContinuousId AddCommGrpCat.{u + 1} (Scheme.ProEt.topology X)

/-- Pullback of abelian sheaves along `e : X ≅ Y` is an equivalence, with inverse the pullback
along `e.symm`. -/
@[expose]
noncomputable def sheafPullbackEquiv (e : X ≅ Y) :
    Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1} ≌
      Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  CategoryTheory.Equivalence.mk (sheafPullback e) (sheafPullback e.symm)
    ((sheafPullbackId (Iso.refl Y) rfl).symm ≪≫
      (sheafPullbackComp e.symm e (Iso.refl Y) (by simp)).symm)
    (sheafPullbackComp e e.symm (Iso.refl X) (by simp) ≪≫ sheafPullbackId (Iso.refl X) rfl)

instance (e : X ≅ Y) : (sheafPullback e).IsEquivalence :=
  (sheafPullbackEquiv e).isEquivalence_functor

instance (e : X ≅ Y) : (sheafPullback e).Additive where
  map_add {_ _ f g} := by
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun U => ?_)
    rw [Sheaf.Hom.add_app]
    exact Sheaf.Hom.add_app f g _

/-! ### The coefficient sheaves -/

variable (X) in
/-- The constant abelian sheaf `ℤ` on `X.ProEt` (the source of the `Ext` groups defining
cohomology). -/
noncomputable abbrev constSheaf : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

variable (X) in
/-- The constant presheaf `ℤ` on `X.ProEt`. -/
noncomputable abbrev constPresheaf : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))

variable (X) in
/-- The unit `ℤ ⟶ ℤ⁺` of the sheafification of the constant presheaf. -/
noncomputable abbrev constUnit :
    constPresheaf X ⟶ (constSheaf X).obj :=
  (sheafificationAdjunction (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).unit.app
    (constPresheaf X)

/-- The comparison `ℤ_X ⟶ e^* ℤ_Y` of constant sheaves, adjoint to the restriction along
`proEtMap e` of the sheafification unit of `Y`. -/
@[expose]
noncomputable def constSheafPullback (e : X ≅ Y) :
    constSheaf X ⟶ (sheafPullback e).obj (constSheaf Y) :=
  ((sheafificationAdjunction (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).homEquiv
    (constPresheaf X) ((sheafPullback e).obj (constSheaf Y))).symm
    (Functor.whiskerLeft (proEtMap e).op (constUnit Y))

@[reassoc]
theorem constUnit_comp_constSheafPullback (e : X ≅ Y) :
    constUnit X ≫ (constSheafPullback e).hom =
      Functor.whiskerLeft (proEtMap e).op (constUnit Y) := by
  have := ((sheafificationAdjunction (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).homEquiv
    (constPresheaf X) ((sheafPullback e).obj (constSheaf Y))).apply_symm_apply
    (Functor.whiskerLeft (proEtMap e).op (constUnit Y))
  rw [Adjunction.homEquiv_unit] at this
  exact this

@[reassoc]
theorem constUnit_app_comp_constSheafPullback_app (e : X ≅ Y) (U : X.ProEtᵒᵖ) :
    (constUnit X).app U ≫ (constSheafPullback e).hom.app U =
      (constUnit Y).app (op ((proEtMap e).obj U.unop)) :=
  NatTrans.congr_app (constUnit_comp_constSheafPullback e) U

/-- Two morphisms out of the constant sheaf agree if they agree after the sheafification
unit. -/
theorem constSheaf_hom_ext {S : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
    {f g : (presheafToSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
      (constPresheaf X) ⟶ S} (h : constUnit X ≫ f.hom = constUnit X ≫ g.hom) : f = g := by
  apply ((sheafificationAdjunction (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).homEquiv
    _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact h

variable (X) in
/-- The abelian sheaf `ℤ_ℓ` (in the universe `u + 1`) on `X.ProEt` whose cohomology is
`X.EllAdicCohomology ℓ n`. -/
noncomputable abbrev ellSheaf (ℓ : ℕ) [Fact ℓ.Prime] :
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  (sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (X.ellAdicSheaf ℓ)

/-- The pullback of `ℤ_ℓ` along `e` *is* `ℤ_ℓ`: both are restrictions of the sheaf
`U ↦ C(U, ℤ_ℓ)` of the big pro-étale site along the same functor to schemes. -/
@[expose]
noncomputable def ellSheafPullback (e : X ≅ Y) (ℓ : ℕ) [Fact ℓ.Prime] :
    (sheafPullback e).obj (ellSheaf Y ℓ) ⟶ ellSheaf X ℓ :=
  𝟙 (ellSheaf X ℓ)

/-! ### Compatibilities -/

/-- The natural transformation `sheafPullback f ⋙ sheafPullback e ⟶ sheafPullback g`. -/
noncomputable abbrev sheafPullbackCompHom (e : X ≅ Y) (f : Y ≅ Z) (g : X ≅ Z)
    (h : e.hom ≫ f.hom = g.hom) : sheafPullback f ⋙ sheafPullback e ⟶ sheafPullback g :=
  (sheafPullbackComp e f g h).hom

theorem constSheafPullback_comp (e : X ≅ Y) (f : Y ≅ Z) (g : X ≅ Z)
    (h : e.hom ≫ f.hom = g.hom) :
    (constSheafPullback e ≫ (sheafPullback e).map (constSheafPullback f)) ≫
      (sheafPullbackCompHom e f g h).app (constSheaf Z) = constSheafPullback g := by
  apply constSheaf_hom_ext
  refine NatTrans.ext (funext fun U => ?_)
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom, Category.assoc,
    Functor.sheafPushforwardContinuous_map_hom_app]
  erw [constUnit_app_comp_constSheafPullback_app_assoc,
    constUnit_app_comp_constSheafPullback_app_assoc, constUnit_app_comp_constSheafPullback_app]
  simp only [sheafPullbackCompHom, sheafPullbackComp, Iso.trans_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, Functor.sheafPushforwardContinuousIso_hom,
    Functor.sheafPushforwardContinuousNatTrans_app_hom]
  erw [← (constUnit Z).naturality]
  simp
  rfl

theorem ellSheafPullback_comp (e : X ≅ Y) (f : Y ≅ Z) (g : X ≅ Z)
    (h : e.hom ≫ f.hom = g.hom) (ℓ : ℕ) [Fact ℓ.Prime] :
    (sheafPullback e).map (ellSheafPullback f ℓ) ≫ ellSheafPullback e ℓ =
      (sheafPullbackCompHom e f g h).app (ellSheaf Z ℓ) ≫ ellSheafPullback g ℓ := by
  apply Sheaf.hom_ext
  ext U x
  rfl

/-- The natural transformation `sheafPullback e ⟶ 𝟭` when `e = 𝟙`. -/
noncomputable abbrev sheafPullbackIdHom (e : X ≅ X) (h : e.hom = 𝟙 X) : sheafPullback e ⟶ 𝟭 _ :=
  (sheafPullbackId e h).hom

theorem constSheafPullback_id (e : X ≅ X) (h : e.hom = 𝟙 X) :
    constSheafPullback e ≫ (sheafPullbackIdHom e h).app (constSheaf X) = 𝟙 _ := by
  apply constSheaf_hom_ext
  refine NatTrans.ext (funext fun U => ?_)
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.id_hom, Category.comp_id]
  erw [constUnit_app_comp_constSheafPullback_app_assoc]
  simp only [sheafPullbackIdHom, sheafPullbackId, Iso.trans_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, Functor.sheafPushforwardContinuousIso_hom,
    Functor.sheafPushforwardContinuousNatTrans_app_hom]
  erw [← (constUnit X).naturality]
  simp

theorem ellSheafPullback_id (e : X ≅ X) (h : e.hom = 𝟙 X) (ℓ : ℕ) [Fact ℓ.Prime] :
    ellSheafPullback e ℓ = (sheafPullbackIdHom e h).app (ellSheaf X ℓ) ≫ 𝟙 _ := by
  apply Sheaf.hom_ext
  ext U x
  rfl

end ProEtIso

/-! ### Functoriality of `ℓ`-adic cohomology -/

namespace EllAdicCohomology

open ProEtIso

variable {X Y Z : Scheme.{u}} (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)

/-- `ℓ`-adic cohomology is `Ext^n(ℤ, ℤ_ℓ)` of the sheaves `constSheaf` and `ellSheaf`. -/
theorem ellAdicCohomology_eq :
    X.EllAdicCohomology ℓ n = Ext.{u + 1} (constSheaf X) (ellSheaf X ℓ) n :=
  rfl

/-- Pullback along `e : X ≅ Y` on the `Ext` groups `Ext^n(ℤ_Y, ℤ_ℓ) →+ Ext^n(ℤ_X, ℤ_ℓ)`: the
transport along the equivalence `sheafPullback e` of sheaf categories. -/
@[expose]
noncomputable def pullbackExt (e : X ≅ Y) :
    Ext.{u + 1} (constSheaf Y) (ellSheaf Y ℓ) n →+ Ext.{u + 1} (constSheaf X) (ellSheaf X ℓ) n :=
  extTransport (sheafPullback e) (constSheafPullback e) (ellSheafPullback e ℓ) n

theorem pullbackExt_of_hom_eq_id (e : X ≅ X) (h : e.hom = 𝟙 X)
    (α : Ext.{u + 1} (constSheaf X) (ellSheaf X ℓ) n) : pullbackExt ℓ n e α = α := by
  rw [pullbackExt, extTransport_natTrans (sheafPullback e) (𝟭 _) (sheafPullbackIdHom e h)
    (constSheafPullback e) (ellSheafPullback e ℓ) (𝟙 _) (𝟙 _) (constSheafPullback_id e h)
    (ellSheafPullback_id e h ℓ)]
  exact extTransport_id n α

theorem pullbackExt_pullbackExt (e : X ≅ Y) (f : Y ≅ Z) (g : X ≅ Z) (h : e.hom ≫ f.hom = g.hom)
    (α : Ext.{u + 1} (constSheaf Z) (ellSheaf Z ℓ) n) :
    pullbackExt ℓ n e (pullbackExt ℓ n f α) = pullbackExt ℓ n g α := by
  rw [pullbackExt, pullbackExt, pullbackExt, extTransport_comp,
    extTransport_natTrans (sheafPullback f ⋙ sheafPullback e) (sheafPullback g)
      (sheafPullbackCompHom e f g h) _ _ _ _ (constSheafPullback_comp e f g h)
      (ellSheafPullback_comp e f g h ℓ)]

/-- Pullback along an isomorphism `e : X ≅ Y`, `H^n(Y, ℤ_ℓ) →+ H^n(X, ℤ_ℓ)`. -/
@[expose]
noncomputable def pullbackMap (e : X ≅ Y) : Y.EllAdicCohomology ℓ n →+ X.EllAdicCohomology ℓ n :=
  pullbackExt ℓ n e

/-- Pullback along an isomorphism whose underlying morphism is the identity is the identity. -/
theorem pullbackMap_of_hom_eq_id (e : X ≅ X) (h : e.hom = 𝟙 X) (α : X.EllAdicCohomology ℓ n) :
    pullbackMap ℓ n e α = α :=
  pullbackExt_of_hom_eq_id ℓ n e h α

/-- Pullback is contravariantly functorial: `e^* ∘ f^* = (e ≫ f)^*`. -/
theorem pullbackMap_pullbackMap (e : X ≅ Y) (f : Y ≅ Z) (g : X ≅ Z)
    (h : e.hom ≫ f.hom = g.hom) (α : Z.EllAdicCohomology ℓ n) :
    pullbackMap ℓ n e (pullbackMap ℓ n f α) = pullbackMap ℓ n g α :=
  pullbackExt_pullbackExt ℓ n e f g h α

theorem pullbackMap_congr (e e' : X ≅ Y) (h : e.hom = e'.hom) :
    pullbackMap ℓ n e = pullbackMap ℓ n e' := by
  rw [Iso.ext h]

@[simp]
theorem pullbackMap_refl (α : X.EllAdicCohomology ℓ n) :
    pullbackMap ℓ n (Iso.refl X) α = α :=
  pullbackMap_of_hom_eq_id ℓ n _ rfl α

theorem pullbackMap_trans (e : X ≅ Y) (f : Y ≅ Z) (α : Z.EllAdicCohomology ℓ n) :
    pullbackMap ℓ n (e ≪≫ f) α = pullbackMap ℓ n e (pullbackMap ℓ n f α) :=
  (pullbackMap_pullbackMap ℓ n e f (e ≪≫ f) rfl α).symm

/-- The additive equivalence `H^n(X, ℤ_ℓ) ≃+ H^n(Y, ℤ_ℓ)` induced by an isomorphism
`e : X ≅ Y` (covariant transport of structure: it is the pullback along `e.symm`, with inverse
the pullback along `e`). -/
@[expose]
noncomputable def mapIso (e : X ≅ Y) : X.EllAdicCohomology ℓ n ≃+ Y.EllAdicCohomology ℓ n where
  toFun := pullbackMap ℓ n e.symm
  invFun := pullbackMap ℓ n e
  left_inv α :=
    (pullbackMap_pullbackMap ℓ n e e.symm (Iso.refl X) (by simp) α).trans (pullbackMap_refl ℓ n α)
  right_inv α :=
    (pullbackMap_pullbackMap ℓ n e.symm e (Iso.refl Y) (by simp) α).trans
      (pullbackMap_refl ℓ n α)
  map_add' := map_add (pullbackMap ℓ n e.symm)

theorem mapIso_apply (e : X ≅ Y) (α : X.EllAdicCohomology ℓ n) :
    mapIso ℓ n e α = pullbackMap ℓ n e.symm α :=
  rfl

theorem mapIso_symm_apply (e : X ≅ Y) (α : Y.EllAdicCohomology ℓ n) :
    (mapIso ℓ n e).symm α = pullbackMap ℓ n e α :=
  rfl

@[simp]
theorem mapIso_refl : mapIso ℓ n (Iso.refl X) = AddEquiv.refl _ := by
  ext α
  exact pullbackMap_of_hom_eq_id ℓ n (Iso.refl X).symm rfl α

theorem mapIso_trans (e : X ≅ Y) (f : Y ≅ Z) :
    mapIso ℓ n (e ≪≫ f) = (mapIso ℓ n e).trans (mapIso ℓ n f) := by
  ext α
  exact (pullbackMap_pullbackMap ℓ n f.symm e.symm (e ≪≫ f).symm (by simp) α).symm

theorem mapIso_symm (e : X ≅ Y) : mapIso ℓ n e.symm = (mapIso ℓ n e).symm := by
  ext α
  rfl

/-- The action of the automorphism group `Aut X = (X ≅ X)` on `H^n(X, ℤ_ℓ)` by transport of
structure, `x • α = mapIso x α`, by additive automorphisms. (In `Aut X`, `x * y = y ≪≫ x`.) -/
noncomputable instance instDistribMulActionAut :
    DistribMulAction (Aut X) (X.EllAdicCohomology ℓ n) where
  smul x α := mapIso ℓ n x.asIso α
  one_smul α := pullbackMap_of_hom_eq_id ℓ n (Iso.symm (1 : Aut X).asIso) rfl α
  mul_smul x y α := DFunLike.congr_fun (mapIso_trans ℓ n y.asIso x.asIso) α
  smul_zero x := map_zero (mapIso ℓ n x.asIso)
  smul_add x α β := map_add (mapIso ℓ n x.asIso) α β

theorem aut_smul_def (x : Aut X) (α : X.EllAdicCohomology ℓ n) :
    x • α = mapIso ℓ n x.asIso α :=
  rfl

variable (X) in
/-- The automorphism action as a group homomorphism
`Aut X →* Multiplicative (AddAut (H^n(X, ℤ_ℓ)))` (`AddAut` is an additive
group in Mathlib, hence the `Multiplicative`). -/
@[expose]
noncomputable def autAction : Aut X →* Multiplicative (AddAut (X.EllAdicCohomology ℓ n)) :=
  DistribMulAction.toAddAut (Aut X) (X.EllAdicCohomology ℓ n)

theorem autAction_apply (x : Aut X) (α : X.EllAdicCohomology ℓ n) :
    Multiplicative.toAdd (autAction X ℓ n x) α = pullbackMap ℓ n (Iso.symm x.asIso) α :=
  rfl

end EllAdicCohomology

end ArithmeticOfJacobiPolynomials
