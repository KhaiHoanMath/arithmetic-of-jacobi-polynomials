/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.AbelianWeilPairing
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianDuality
public import StacksFrontier.AlgebraicGeometry.InvertibleFunctions.ProperVariety
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso
public import StacksFrontier.Topology.Sheaves.Functors.Module.UnitEndomorphismSections

/-!
# The finite Weil pairing pinned to the Poincaré line bundle

For an abelian variety `A` over `K`, an extension `L/K`, an integer `m`, and torsion points
`a ∈ A[m](L)`, `b ∈ Â[m](L)`, the **Weil value** `e_m(a, b) ∈ L^×` is characterized by the
classical recipe (Milne, *Abelian Varieties*, §16 p. 29 = Mumford §20 p. 184, with the Cartier
duality of Theorem 11.1 behind it): let `M_b` be the fibre at `b` of the Poincaré line bundle
on `A_L`. Because `m b = 0`, `[m]^* M_b` is trivial; choose a trivialization
`θ : 𝒪_{A_L} ≅ [m]^* M_b`. Because `m a = 0`, `[m] ∘ t_a = [m]`, so translation by `a` carries
`θ` to another trivialization `t_a^* θ`, and `t_a^* θ = c · θ` for a unique `c ∈ L^×`; then
`e_m(a, b) = c`.

The objects are scheme and sheaf data:

* `pb`, `pbComp`, `pbCongr`, `pbUnit`: pullback of `𝒪`-modules along morphisms of schemes
  (Stacks' `modulePullback`), the canonical identification `(f ≫ g)^* ≅ g^* ⋙ f^*`, pullbacks
  along equal morphisms, and `f^* 𝒪_Y ≅ 𝒪_X`;
* `scal`: multiplication by a global function, as an endomorphism of `𝒪_X`;
* `transTriv`: the transport `t^* θ : 𝒪_X ≅ n^* M` of a trivialization `θ : 𝒪_X ≅ n^* M`
  along `t` when `t ≫ n = n`, composed of the canonical pullback identifications;
* `IsTranslationScalar`: the relation `t^* θ = c · θ`;
* `IsWeilValue`: the relation for `t = t_a`, `n = [m]` on `A_L` (some trivialization works);
* `IsWeilPairingAt`, `IsWeilData`, `IsGeometricWeilPairing`: a pairing, respectively a
  `DualPairingData`, is the Weil pairing of a Poincaré class `P` whose fibres are the sheaves
  `N` with `N.cls = fibreClass P b`.

Proofs: `transTriv_trans` (change of trivialization), `IsTranslationScalar.of_trivialization`
(independence of the trivialization, from the constant global sections of the proper
geometrically integral `A_L`, Stacks Tag 0BUG (7)), `IsTranslationScalar.unique`,
`IsTranslationScalar.congr_iso`, `IsWeilValue.unique` (the value is pinned by the class of
the fibre), `IsWeilPairingAt.unique`, `IsWeilData.pairing_eq`. Existence (the trivialization
exists and the pairing is bilinear, perfect, compatible) is a literature result; see `External.lean`
for the general existence statement.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace ArithmeticOfJacobiPolynomials.WeilPairingGeometry

section Pullback

variable {X Y Z : Scheme.{u}}

/-- The sheaf of rings `𝒪_X`, as a sheaf of (not necessarily commutative) rings. -/
abbrev ringSheaf (X : Scheme.{u}) :=
  Stacks.RingedSpace.structureRingSheaf X.toRingedSpace

/-- `𝒪_X`-modules. -/
abbrev Mod (X : Scheme.{u}) := SheafOfModules.{u} (ringSheaf X)

/-- Pullback of modules along a morphism of schemes. -/
abbrev pb (f : X ⟶ Y) : Mod Y ⥤ Mod X :=
  Stacks.RingedSpace.pullbackFunctor f.toLRSHom.toShHom

/-- The structure sheaf as a module over itself. -/
abbrev unitMod (X : Scheme.{u}) : Mod X := SheafOfModules.unit (ringSheaf X)

open RingedSpaceModuleAdjunction in
/-- Pullback along a composite is the composite of pullbacks (the same isomorphism that
`Stacks.Picard.pullbackClass_comp` uses). -/
def pbComp (f : X ⟶ Y) (g : Y ⟶ Z) : pb g ⋙ pb f ≅ pb (f ≫ g) :=
  SheafOfModules.pullbackComp (structureSheafHom g.toLRSHom.toShHom)
    (structureSheafHom f.toLRSHom.toShHom)

/-- Pullbacks along equal morphisms are isomorphic. -/
def pbCongr {f g : X ⟶ Y} (h : f = g) : pb f ≅ pb g :=
  eqToIso (by rw [h])

/-- `f^* 𝒪_Y ≅ 𝒪_X`. -/
def pbUnit (f : X ⟶ Y) : (pb f).obj (unitMod Y) ≅ unitMod X :=
  RingedSpaceModuleAdjunction.modulePullbackObjUnitIso f.toLRSHom.toShHom

end Pullback

section Scalar

variable (X : Scheme.{u})

/-- The restriction of a global function to an open, as an element of the ring `𝒪_X(U)`. -/
def restrictTop (s : Γ(X, ⊤)) (U : (Opens X)ᵒᵖ) : (ringSheaf X).obj.obj U :=
  X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op s

/-- The section of `𝒪_X` given by the restrictions of a global function. -/
def scalSection (s : Γ(X, ⊤)) : (unitMod X).sections :=
  PresheafOfModules.sectionsMk (M := (unitMod X).val) (fun U => restrictTop X s U)
    (fun U V f => by
      change X.presheaf.map f ((X.presheaf.map (homOfLE le_top).op) s) = _
      rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
      rfl)

/-- **Multiplication by a global function** `s ∈ Γ(X, 𝒪_X)`, as an endomorphism of the structure
sheaf: the morphism `𝒪_X ⟶ 𝒪_X` of `𝒪_X`-modules sending `1` to `s`. -/
def scal (s : Γ(X, ⊤)) : unitMod X ⟶ unitMod X :=
  (SheafOfModules.unitHomEquiv (unitMod X)).symm (scalSection X s)

/-- `scal s` sends `1` to the restriction of `s`. -/
theorem scal_val_app_one (s : Γ(X, ⊤)) (U : (Opens X)ᵒᵖ) :
    (scal X s).val.app U (1 : (ringSheaf X).obj.obj U) = restrictTop X s U :=
  (SheafOfModules.unitHomEquiv_apply_coe (unitMod X) (scal X s) U).symm.trans
    (congrArg (fun z => z.val U) (Equiv.apply_symm_apply _ (scalSection X s)))

/-- A morphism out of `𝒪_X` is determined by its value at `1` over every open. -/
theorem unitHom_ext {M : Mod X} {a b : unitMod X ⟶ M}
    (h : ∀ U : (Opens X)ᵒᵖ, a.val.app U (1 : (ringSheaf X).obj.obj U) =
      b.val.app U (1 : (ringSheaf X).obj.obj U)) : a = b := by
  apply (SheafOfModules.unitHomEquiv M).injective
  apply PresheafOfModules.sections_ext
  intro U
  rw [SheafOfModules.unitHomEquiv_apply_coe, SheafOfModules.unitHomEquiv_apply_coe]
  exact h U

/-- Restriction to the whole space is the identity. -/
theorem restrictTop_top (s : Γ(X, ⊤)) : restrictTop X s (op ⊤) = s := by
  unfold restrictTop
  have : (homOfLE (le_top : (op (⊤ : Opens X)).unop ≤ ⊤)).op = 𝟙 _ := rfl
  rw [this, X.presheaf.map_id]
  rfl

/-- An endomorphism of `𝒪_X` takes the value `a(1)|_U` at `1` over every open `U`. -/
theorem unitHom_val_app_one_eq_restrictTop (a : unitMod X ⟶ unitMod X) (U : (Opens X)ᵒᵖ) :
    a.val.app U (1 : (ringSheaf X).obj.obj U) =
      restrictTop X (a.val.app (op ⊤) (1 : (ringSheaf X).obj.obj (op ⊤))) U := by
  have := PresheafOfModules.naturality_apply a.val (homOfLE (le_top : U.unop ≤ ⊤)).op
    (1 : (ringSheaf X).obj.obj (op ⊤))
  erw [PresheafOfModules.unit_map_one] at this
  exact this

/-- Every endomorphism of `𝒪_X` is multiplication by a global function. -/
theorem eq_scal (a : unitMod X ⟶ unitMod X) :
    a = scal X (a.val.app (op ⊤) (1 : (ringSheaf X).obj.obj (op ⊤))) :=
  unitHom_ext X fun U => (unitHom_val_app_one_eq_restrictTop X a U).trans
    (scal_val_app_one X _ U).symm

/-- Scalars commute with every endomorphism of `𝒪_X`. -/
theorem comp_scal_comm (a : unitMod X ⟶ unitMod X) (c : Γ(X, ⊤)) :
    a ≫ scal X c = scal X c ≫ a := by
  refine unitHom_ext X fun U => ?_
  have h1 := Stacks.SheafOfModules.unitHom_val_app_apply (scal X c) U
    (a.val.app U (1 : (ringSheaf X).obj.obj U))
  have h2 := Stacks.SheafOfModules.unitHom_val_app_apply a U
    ((scal X c).val.app U (1 : (ringSheaf X).obj.obj U))
  change (scal X c).val.app U (a.val.app U (1 : (ringSheaf X).obj.obj U)) =
    a.val.app U ((scal X c).val.app U (1 : (ringSheaf X).obj.obj U))
  rw [h1, h2]
  exact mul_comm (G := X.presheaf.obj U) _ _

/-- The global function is recovered from the scalar endomorphism. -/
theorem scal_injective : Function.Injective (scal X) := by
  intro c c' h
  have := congrArg (fun z => z.val.app (op ⊤) (1 : (ringSheaf X).obj.obj (op ⊤))) h
  rw [scal_val_app_one, scal_val_app_one, restrictTop_top, restrictTop_top] at this
  exact this

/-- Pullback of a global function and restriction: `f^♯(g|_U) = (f^♯ g)|_{f⁻¹U}`. -/
theorem hom_app_restrictTop {Y : Scheme.{u}} (f : X ⟶ Y) (g : Γ(Y, ⊤)) (U : (Opens Y)ᵒᵖ) :
    f.app U.unop (restrictTop Y g U) =
      restrictTop X (f.appTop g) (op (f ⁻¹ᵁ U.unop)) :=
  congr($(f.naturality (homOfLE (le_top : U.unop ≤ ⊤)).op) g)

end Scalar

section Translation

variable {X : Scheme.{u}} (t n : X ⟶ X) (h : t ≫ n = n) (M : Mod X)

/-- **The translate of a trivialization.** Given `θ : 𝒪_X ≅ n^* M`, the isomorphism
`t^*θ : 𝒪_X ≅ t^*𝒪_X ≅ t^* n^* M ≅ (t ≫ n)^* M = n^* M`, where the first identification is
`f^*𝒪 ≅ 𝒪`, the third the canonical identification of pullbacks along a composite, and the last
is induced by `t ≫ n = n`. -/
def transTriv (θ : unitMod X ≅ (pb n).obj M) : unitMod X ≅ (pb n).obj M :=
  (pbUnit t).symm ≪≫ (pb t).mapIso θ ≪≫ (pbComp t n).app M ≪≫ (pbCongr h).app M

/-- The relation `t^*θ = c · θ` between a trivialization and its translate, for a global
function `c` (acting through `scal`). -/
def IsTranslationScalar (θ : unitMod X ≅ (pb n).obj M) (c : Γ(X, ⊤)) : Prop :=
  (transTriv t n h M θ).hom = scal X c ≫ θ.hom

theorem conj_trans_aux {C C' : Type*} [Category C] [Category C'] (F : C ⥤ C') {B N : C}
    {B' Z : C'} (e : F.obj B ≅ B') (u : B ≅ B) (θ : B ≅ N) (K : F.obj N ≅ Z) :
    e.symm ≪≫ F.mapIso (u ≪≫ θ) ≪≫ K =
      (e.symm ≪≫ F.mapIso u ≪≫ e) ≪≫ (e.symm ≪≫ F.mapIso θ ≪≫ K) := by
  ext
  simp

/-- Changing a trivialization by an automorphism `u` of `𝒪_X` changes its translate by the
pullback of `u`. -/
theorem transTriv_trans (u : unitMod X ≅ unitMod X) (θ : unitMod X ≅ (pb n).obj M) :
    (transTriv t n h M (u ≪≫ θ)).hom =
      (RingedSpaceModuleAdjunction.pullbackUnitAut t.toLRSHom.toShHom u).hom ≫
        (transTriv t n h M θ).hom := by
  have := congrArg Iso.hom (conj_trans_aux (pb t) (pbUnit t) u θ
    ((pbComp t n).app M ≪≫ (pbCongr h).app M))
  exact this

/-- If `t` acts trivially on global functions, the pullback of every automorphism of `𝒪_X`
along `t` is that automorphism. -/
theorem pullbackUnitAut_eq_self (hglob : ∀ g : Γ(X, ⊤), t.appTop g = g)
    (u : unitMod X ≅ unitMod X) :
    RingedSpaceModuleAdjunction.pullbackUnitAut t.toLRSHom.toShHom u = u := by
  refine (RingedSpaceModuleAdjunction.pullbackUnitAut_eq_iff_val_app_one _ u u).2 ?_
  intro U
  have e1 := unitHom_val_app_one_eq_restrictTop X u.hom U
  have e2 := unitHom_val_app_one_eq_restrictTop X u.hom
    ((RingedSpaceModuleAdjunction.opensMap t.toLRSHom.toShHom).op.obj U)
  refine (congrArg _ e1).trans (Eq.trans ?_ e2.symm)
  exact (hom_app_restrictTop X t _ U).trans
    (congrArg (fun g => restrictTop X g (op (t ⁻¹ᵁ U.unop))) (hglob _))

/-- **Independence of the trivialization.** If `t` acts trivially on global functions, the
relation `t^*θ = c · θ` holds for one trivialization `θ` of `n^* M` as soon as it holds for
any other. -/
theorem IsTranslationScalar.of_trivialization (hglob : ∀ g : Γ(X, ⊤), t.appTop g = g)
    {θ : unitMod X ≅ (pb n).obj M} {c : Γ(X, ⊤)} (hθ : IsTranslationScalar t n h M θ c)
    (θ' : unitMod X ≅ (pb n).obj M) : IsTranslationScalar t n h M θ' c := by
  obtain ⟨u, rfl⟩ : ∃ u : unitMod X ≅ unitMod X, θ' = u ≪≫ θ :=
    ⟨θ' ≪≫ θ.symm, by ext; simp⟩
  unfold IsTranslationScalar at hθ ⊢
  rw [transTriv_trans t n h M u θ, pullbackUnitAut_eq_self t hglob u, hθ, Iso.trans_hom]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ θ.hom) (comp_scal_comm X u.hom c)).trans (Category.assoc _ _ _))

/-- **Uniqueness of the scalar.** For a fixed trivialization the scalar `c` is determined. -/
theorem IsTranslationScalar.unique {θ : unitMod X ≅ (pb n).obj M} {c c' : Γ(X, ⊤)}
    (hc : IsTranslationScalar t n h M θ c) (hc' : IsTranslationScalar t n h M θ c') : c = c' := by
  apply scal_injective X
  unfold IsTranslationScalar at hc hc'
  exact (cancel_mono θ.hom).1 (hc.symm.trans hc')

/-- The relation is invariant under an isomorphism `M ≅ M'` of the line bundle, carrying the
trivialization along. -/
theorem IsTranslationScalar.congr_iso {M' : Mod X} (φ : M ≅ M') {θ : unitMod X ≅ (pb n).obj M}
    {c : Γ(X, ⊤)} (hθ : IsTranslationScalar t n h M θ c) :
    IsTranslationScalar t n h M' (θ ≪≫ (pb n).mapIso φ) c := by
  have h1 : (pb t).map ((pb n).map φ.hom) ≫ (pbComp t n).hom.app M' =
      (pbComp t n).hom.app M ≫ (pb (t ≫ n)).map φ.hom := (pbComp t n).hom.naturality φ.hom
  have h2 : (pb (t ≫ n)).map φ.hom ≫ (pbCongr h).hom.app M' =
      (pbCongr h).hom.app M ≫ (pb n).map φ.hom := (pbCongr h).hom.naturality φ.hom
  unfold IsTranslationScalar at hθ ⊢
  have key : (transTriv t n h M' (θ ≪≫ (pb n).mapIso φ)).hom =
      (transTriv t n h M θ).hom ≫ (pb n).map φ.hom := by
    simp only [transTriv, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
      Category.assoc, Iso.app_hom]
    rw [reassoc_of% h1, h2]
  rw [key, hθ, Category.assoc]
  simp

end Translation

section Invertible

variable (X : Scheme.{u})

/-- Invertible `𝒪_X`-modules, as in Stacks Tag 01CX. -/
abbrev Inv :=
  Stacks.SheafOfModules.InvertibleModules X.toRingedSpace.presheaf
    (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace)

variable {X}

/-- The class of an invertible sheaf in `Pic(X)`. -/
noncomputable def Inv.cls (N : Inv X) : Stacks.Picard.ofScheme X :=
  Stacks.SheafOfModules.picardClass X.toRingedSpace.presheaf
    (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) N.obj N.property

/-- Invertible sheaves with the same class are isomorphic. -/
theorem Inv.nonempty_iso_of_cls_eq {N N' : Inv X} (h : N.cls = N'.cls) :
    Nonempty (N.obj ≅ N'.obj) :=
  (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ N.property N'.property).1 h

end Invertible

section Abelian

open ArithmeticOfJacobiPolynomials.GroupScheme ArithmeticOfJacobiPolynomials.GroupObject
  ArithmeticOfJacobiPolynomials.AbelianDuality
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L]
  (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]

/-- Multiplication by `m` on the base change `A_L`. -/
noncomputable def mulBy (m : ℕ) : baseChange L A ⟶ baseChange L A :=
  (m : GrpObjEnd (baseChange L A)).hom

instance mulBy.isMonHom (m : ℕ) : IsMonHom (mulBy L A m) :=
  GrpObjEnd.isMonHom_hom _

/-- If a rational point `a` is killed by a homomorphism `f`, translation by `a` followed by `f`
is `f`: `f ∘ t_a = f`. -/
theorem translate_comp_of_comp_eq_one {B : Over (Spec (.of L))} [GrpObj B] (f : B ⟶ B)
    [IsMonHom f] (a : 𝟙_ (Over (Spec (.of L))) ⟶ B) (ha : a ≫ f = 1) :
    AbelianDuality.translate B a ≫ f = f := by
  unfold AbelianDuality.translate
  rw [MonObj.mul_comp, Category.id_comp, Category.assoc, ha, MonObj.comp_one, one_mul]

/-- The unit object of `Over (Spec L)` is `Spec L` over `Spec L`. -/
noncomputable def unitIsoSpec : 𝟙_ (Over (Spec (.of L))) ≅ specOver L L :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap L L)) = 𝟙 _
    rw [Category.id_comp]
    exact specMap_algEquiv_one L L)

/-- A point `a ∈ A(L)` of `A` over `K`, as a point `𝟙 ⟶ A_L` of the base change. -/
noncomputable def pointOfGeom (a : GeomPoints K L A) :
    𝟙_ (Over (Spec (.of L))) ⟶ baseChange L A :=
  (unitIsoSpec L).hom ≫
    GeomPoints.toHom L L (baseChange L A) ((baseChangePointsEquiv L A L).symm a)

/-- A torsion point `a ∈ A(L)` with `m • a = 0` is killed by `[m]` as a point of `A_L`. -/
theorem pointOfGeom_comp_mulBy (m : ℕ) (a : GeomPoints K L A) (h : m • a = 0) :
    pointOfGeom L A a ≫ mulBy L A m = 1 := by
  have key : GeomPoints.toHom L L (baseChange L A) ((baseChangePointsEquiv L A L).symm a) ≫
      mulBy L A m = 1 := by
    have h1 := toHom_geomPointsMap (K := L) (L := L) (A := baseChange L A)
      (m : GrpObjEnd (baseChange L A)) ((baseChangePointsEquiv L A L).symm a)
    have h2 : geomPointsMap L L (baseChange L A) (m : GrpObjEnd (baseChange L A))
        ((baseChangePointsEquiv L A L).symm a) = 0 := by
      change geomPointsAction L L (baseChange L A) (m : GrpObjEnd (baseChange L A))
        ((baseChangePointsEquiv L A L).symm a) = 0
      rw [map_natCast, AddMonoid.End.natCast_apply, ← map_nsmul, h, map_zero]
    rw [h2, GeomPoints.toHom_zero] at h1
    exact h1.symm
  unfold pointOfGeom
  rw [Category.assoc, key, MonObj.comp_one]

/-- For `a ∈ A(L)[m]`, translation by `a` followed by `[m]` is `[m]`. -/
theorem translate_comp_mulBy (m : ℕ) (a : GeomPoints K L A) (h : m • a = 0) :
    AbelianDuality.translate (baseChange L A) (pointOfGeom L A a) ≫ mulBy L A m =
      mulBy L A m :=
  translate_comp_of_comp_eq_one L (mulBy L A m) _ (pointOfGeom_comp_mulBy L A m a h)

/-- The ring homomorphism `L → Γ(X, 𝒪_X)` of an `L`-scheme `X`. -/
def structureFun {X : Scheme.{u}} (π : X ⟶ Spec (.of L)) (c : L) : Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of L)).inv ≫ π.appTop).hom c

/-- An endomorphism of an `L`-scheme fixes the functions coming from `L`. -/
theorem appTop_structureFun {X : Scheme.{u}} (π : X ⟶ Spec (.of L)) (t : X ⟶ X)
    (ht : t ≫ π = π) (c : L) : t.appTop (structureFun L π c) = structureFun L π c := by
  have h : (Scheme.ΓSpecIso (.of L)).inv ≫ π.appTop ≫ t.appTop =
      (Scheme.ΓSpecIso (.of L)).inv ≫ π.appTop := by
    rw [← Scheme.Hom.comp_appTop, ht]
  exact congr(ConcreteCategory.hom $h c)

omit [IsCommMonObj A] in
/-- **Constant global sections** (Stacks Tag 0BUG (7)): for an abelian variety `A` over `K`, the
global functions on `A_L` are the constants `L`. -/
theorem structureFun_bijective [IsAbelianVariety K A] :
    Function.Bijective (structureFun L (baseChange L A).hom) := by
  have : GeometricallyConnected (baseChange L A).hom :=
    geometricallyConnected_of_geometricallyIrreducible _
  have : IsIso ((Scheme.ΓSpecIso (.of L)).inv ≫ (baseChange L A).hom.appTop) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.isIso_globalSections_of_isProper L
      (baseChange L A).hom
  exact (ConcreteCategory.isIso_iff_bijective _).mp this

/-- `[m] ∘ t_a = [m]` as a morphism of underlying schemes. -/
theorem left_comp_eq {B : Over (Spec (.of L))} {t n : B ⟶ B} (h : t ≫ n = n) :
    t.left ≫ n.left = n.left := by
  rw [← Over.comp_left, h]

/-- **The finite Weil value relation.** `c ∈ L` is the Weil value of `a ∈ A_L[m]` against an
invertible sheaf `N` on `A_L` if `[m]^* N` has a trivialization `θ : 𝒪_{A_L} ≅ [m]^* N` that
`t_a^*` multiplies by `c`:
`t_a^*θ = c · θ`, where `t_a^*θ` is the transport of `θ` along `t_a`, the identification
`t_a^*𝒪 = 𝒪`, and `t_a^*[m]^* N = ([m] ∘ t_a)^* N = [m]^* N`. -/
def IsWeilValue (m : ℕ) (a : 𝟙_ (Over (Spec (.of L))) ⟶ baseChange L A)
    (h : AbelianDuality.translate (baseChange L A) a ≫ mulBy L A m = mulBy L A m)
    (N : Inv (baseChange L A).left) (c : L) : Prop :=
  ∃ θ : unitMod (baseChange L A).left ≅ (pb (mulBy L A m).left).obj N.obj,
    IsTranslationScalar (AbelianDuality.translate (baseChange L A) a).left (mulBy L A m).left
      (left_comp_eq L h) N.obj θ (structureFun L (baseChange L A).hom c)

omit [IsCommMonObj A] in
/-- Translations of `A_L` act trivially on global functions. -/
theorem appTop_translate [IsAbelianVariety K A] (a : 𝟙_ (Over (Spec (.of L))) ⟶ baseChange L A)
    (g : Γ((baseChange L A).left, ⊤)) :
    (AbelianDuality.translate (baseChange L A) a).left.appTop g = g := by
  obtain ⟨d, rfl⟩ := (structureFun_bijective L A).2 g
  exact appTop_structureFun L (baseChange L A).hom _
    (Over.w (AbelianDuality.translate (baseChange L A) a)) d

/-- **The Weil value is pinned.** For an abelian variety `A` over `K`, the value `c ∈ L` of
`IsWeilValue` depends only on the class of the invertible sheaf `N` in `Pic(A_L)`: it does not
depend on the trivialization (constant global sections of the proper geometrically integral
`A_L`), nor on the representative of the class. -/
theorem IsWeilValue.unique [IsAbelianVariety K A] {m : ℕ}
    {a : 𝟙_ (Over (Spec (.of L))) ⟶ baseChange L A}
    {h : AbelianDuality.translate (baseChange L A) a ≫ mulBy L A m = mulBy L A m}
    {N N' : Inv (baseChange L A).left} (hcls : N.cls = N'.cls) {c c' : L}
    (h1 : IsWeilValue L A m a h N c) (h2 : IsWeilValue L A m a h N' c') : c = c' := by
  obtain ⟨θ, hθ⟩ := h1
  obtain ⟨θ', hθ'⟩ := h2
  obtain ⟨φ⟩ := Inv.nonempty_iso_of_cls_eq hcls
  have h3 := IsTranslationScalar.congr_iso (AbelianDuality.translate (baseChange L A) a).left
    (mulBy L A m).left (left_comp_eq L h) N.obj φ hθ
  have h4 := IsTranslationScalar.of_trivialization
    (AbelianDuality.translate (baseChange L A) a).left (mulBy L A m).left (left_comp_eq L h)
    N'.obj (appTop_translate L A a) h3 θ'
  exact (structureFun_bijective L A).1
    (IsTranslationScalar.unique _ _ _ _ hθ' h4).symm

variable (Â : Over (Spec (.of K))) [GrpObj Â] [IsCommMonObj Â]

/-- **The fibre of a Poincaré class.** The class of the restriction of `P ∈ Pic(A × Â)` to
`A_L = A × Spec L` along the `L`-point `b` of `Â` (the pullback along
`A_L ⟶ A × Â`). -/
noncomputable def fibreClass (P : Stacks.Picard.ofScheme (A ⊗ Â).left) (b : GeomPoints K L Â) :
    Stacks.Picard.ofScheme (baseChange L A).left :=
  Stacks.Picard.schemePullbackClass (familyFibreMap A Â L (GeomPoints.toHom K L Â b)) P

/-- **A pairing `A[m](L) × Â[m](L) → L^×` is the geometric Weil pairing of the Poincaré class
`P`**: for all torsion points `a`, `b`, there is an invertible sheaf `N` on `A_L` representing the
fibre `P_b` of the Poincaré class such that `e m (a, b)` is the Weil value
(`IsWeilValue`) of `a` against `N`: translation by `a` multiplies a trivialization of
`[m]^* N` by `e m (a, b)`. This is Milne, *Abelian Varieties*, §16 p. 29 (= Mumford §20 p. 184),
stated for an arbitrary integer `m` (no condition on the characteristic is needed to state it). -/
def IsWeilPairingAt (m : ℕ) (P : Stacks.Picard.ofScheme (A ⊗ Â).left)
    (e : AddSubgroup.torsionBy (GeomPoints K L A) (m : ℤ) →
      AddSubgroup.torsionBy (GeomPoints K L Â) (m : ℤ) → Lˣ) : Prop :=
  ∀ (a : AddSubgroup.torsionBy (GeomPoints K L A) (m : ℤ))
    (b : AddSubgroup.torsionBy (GeomPoints K L Â) (m : ℤ)),
    ∃ N : Inv (baseChange L A).left, N.cls = fibreClass L A Â P b.1 ∧
      IsWeilValue L A m (pointOfGeom L A a.1)
        (translate_comp_mulBy L A m a.1 (AddSubgroup.torsionBy.nsmul_iff.1 a.2)) N
        ((e a b : Lˣ) : L)

/-- **The geometric Weil pairing is unique.** For an abelian variety, two pairings satisfying
`IsWeilPairingAt` for the same class `P` agree. -/
theorem IsWeilPairingAt.unique [IsAbelianVariety K A] {m : ℕ}
    {P : Stacks.Picard.ofScheme (A ⊗ Â).left}
    {e e' : AddSubgroup.torsionBy (GeomPoints K L A) (m : ℤ) →
      AddSubgroup.torsionBy (GeomPoints K L Â) (m : ℤ) → Lˣ}
    (he : IsWeilPairingAt L A Â m P e) (he' : IsWeilPairingAt L A Â m P e') : e = e' := by
  funext a b
  obtain ⟨N, hN, hv⟩ := he a b
  obtain ⟨N', hN', hv'⟩ := he' a b
  exact Units.ext (IsWeilValue.unique L A (hN.trans hN'.symm) hv hv')

variable {ℓ : ℕ} (D : DualPairingData ℓ L A Â)

/-- **`IsWeilData`**: the finite-level pairings `e n` of the duality datum `D` are, for every
`n`, the geometric Weil pairing `A[ℓ^n](L) × Â[ℓ^n](L) → L^×` of the Poincaré class `P`
(`IsWeilPairingAt` at `m = ℓ^n`). -/
def IsWeilData (P : Stacks.Picard.ofScheme (A ⊗ Â).left) : Prop :=
  ∀ n : ℕ, IsWeilPairingAt L A Â (ℓ ^ n) P (fun a b => Additive.toMul (D.pairing n a b).1)

/-- A duality datum that is the geometric Weil pairing of a Poincaré pair `(Â, P)` of
`A`: `P` is the normalized Poincaré class of the dual (`IsPoincarePair`) and the pairings are
its Weil pairings. -/
structure IsGeometricWeilPairing (P : Stacks.Picard.ofScheme (A ⊗ Â).left) where
  poincare : IsPoincarePair A Â P
  weil : IsWeilData L A Â D P

variable {L A Â D}

/-- **The geometric pairing pins the duality datum**: two duality data that are both the
Weil pairing of the same Poincaré class have the same finite-level pairings. -/
theorem IsWeilData.pairing_eq [IsAbelianVariety K A] {D' : DualPairingData ℓ L A Â}
    {P : Stacks.Picard.ofScheme (A ⊗ Â).left} (h : IsWeilData L A Â D P)
    (h' : IsWeilData L A Â D' P) : D.pairing = D'.pairing := by
  funext n
  refine AddMonoidHom.ext fun a => AddMonoidHom.ext fun b => ?_
  apply Subtype.ext
  have := congrFun (congrFun (IsWeilPairingAt.unique L A Â (h n) (h' n)) a) b
  exact Additive.toMul.injective this

variable (L A Â)

/-- **A family of finite Weil pairings** `e_m : A[m](L) × Â[m](L) → μ_m(L)`, one for each integer
`m` invertible in `K`, with all the properties of the finite Weil pairing of the Poincaré class `P`
(Milne, *Abelian Varieties*, Theorem 11.1 and §16 with Lemmas 16.1, 16.2; course notes
§13 and Lemma 13.1):

* `weil`: `e_m` is the geometric Weil pairing of `P` (`IsWeilPairingAt`);
* `galois`: `e_m(σ a, σ b) = σ e_m(a, b)` for `σ ∈ Aut(L/K)`;
* `mul` (Lemma 16.1): `e_{mn}(a, b)^n = e_m(n a, n b)`;
* `perfect` (Theorem 11.1: Cartier duality): over an *algebraically closed* `L` the pairing has
  trivial left and right kernels. (For a general field `L` this is false: a rational elliptic curve
  with a single nonzero rational 2-torsion point has an alternating, hence zero, pairing on the
  rational points.)

This is only the bundle of properties for a given family `e`; it asserts no existence. -/
structure IsWeilFamily (P : Stacks.Picard.ofScheme (A ⊗ Â).left)
    (e : ∀ m : ℕ, (m : K) ≠ 0 →
      AddSubgroup.torsionBy (GeomPoints K L A) (m : ℤ) →+
        AddSubgroup.torsionBy (GeomPoints K L Â) (m : ℤ) →+
          AddSubgroup.torsionBy (Additive Lˣ) (m : ℤ)) : Prop where
  weil : ∀ (m : ℕ) (hm : (m : K) ≠ 0),
    IsWeilPairingAt L A Â m P (fun a b => Additive.toMul (e m hm a b).1)
  galois : ∀ (m : ℕ) (hm : (m : K) ≠ 0) (σ : L ≃ₐ[K] L) a b,
    e m hm (Stacks.AbelianGroup.torsionMap (DistribSMul.toAddMonoidHom (GeomPoints K L A) σ) _ a)
        (Stacks.AbelianGroup.torsionMap (DistribSMul.toAddMonoidHom (GeomPoints K L Â) σ) _ b) =
      Stacks.AbelianGroup.torsionMap (DistribSMul.toAddMonoidHom (Additive Lˣ) σ) _ (e m hm a b)
  mul : ∀ (m n k : ℕ) (_ : k = m * n) (hm : (m : K) ≠ 0) (hk' : (k : K) ≠ 0)
    (a : AddSubgroup.torsionBy (GeomPoints K L A) (k : ℤ))
    (b : AddSubgroup.torsionBy (GeomPoints K L Â) (k : ℤ))
    (ha : n • a.1 ∈ AddSubgroup.torsionBy (GeomPoints K L A) (m : ℤ))
    (hb : n • b.1 ∈ AddSubgroup.torsionBy (GeomPoints K L Â) (m : ℤ)),
    n • (e k hk' a b).1 = (e m hm ⟨n • a.1, ha⟩ ⟨n • b.1, hb⟩).1
  perfect : IsAlgClosed L → ∀ (m : ℕ) (hm : (m : K) ≠ 0),
    (∀ a, (∀ b, e m hm a b = 0) → a = 0) ∧ (∀ b, (∀ a, e m hm a b = 0) → b = 0)

theorem natCast_pow_ne_zero {K : Type*} [Field K] {ℓ : ℕ} (hℓ : (ℓ : K) ≠ 0) (n : ℕ) :
    ((ℓ ^ n : ℕ) : K) ≠ 0 := by
  rw [Nat.cast_pow]
  exact pow_ne_zero n hℓ

variable {L A Â}

/-- **The `ℓ`-power duality datum of a Weil family.** For `ℓ` invertible in `K` and `L`
algebraically closed, the Weil pairings `e_{ℓ^n}` form a `DualPairingData`: compatibility is
Lemma 16.1 (with `m = ℓ^n`, `n = ℓ`), equivariance is `galois`, and injectivity is the trivial
left kernel of Theorem 11.1. -/
def IsWeilFamily.dualPairingData [IsAlgClosed L] {P : Stacks.Picard.ofScheme (A ⊗ Â).left}
    {e : ∀ m : ℕ, (m : K) ≠ 0 →
      AddSubgroup.torsionBy (GeomPoints K L A) (m : ℤ) →+
        AddSubgroup.torsionBy (GeomPoints K L Â) (m : ℤ) →+
          AddSubgroup.torsionBy (Additive Lˣ) (m : ℤ)}
    (he : IsWeilFamily L A Â P e) (ℓ : ℕ) (hℓ : (ℓ : K) ≠ 0) :
    DualPairingData ℓ L A Â where
  pairing n := e (ℓ ^ n) (natCast_pow_ne_zero hℓ n)
  compatible n x y := by
    refine Subtype.ext ?_
    exact (he.mul (ℓ ^ n) ℓ (ℓ ^ (n + 1)) (pow_succ ℓ n) (natCast_pow_ne_zero hℓ n)
      (natCast_pow_ne_zero hℓ (n + 1)) x y
      (torsionTransition ℓ n x).2 (torsionTransition ℓ n y).2).symm
  equivariant σ n x y := he.galois (ℓ ^ n) (natCast_pow_ne_zero hℓ n) σ x y
  injective n := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    refine (he.perfect inferInstance (ℓ ^ n) (natCast_pow_ne_zero hℓ n)).1 a fun b => ?_
    exact congrFun (congrArg DFunLike.coe ha) b

/-- **The Weil family pins the duality datum**: the datum built from a Weil family of `P` is the
geometric Weil pairing of `P` (`IsWeilData`), hence, by `IsWeilData.pairing_eq`, the only duality
datum with this property. -/
theorem IsWeilFamily.isWeilData [IsAlgClosed L] {P : Stacks.Picard.ofScheme (A ⊗ Â).left}
    {e : ∀ m : ℕ, (m : K) ≠ 0 →
      AddSubgroup.torsionBy (GeomPoints K L A) (m : ℤ) →+
        AddSubgroup.torsionBy (GeomPoints K L Â) (m : ℤ) →+
          AddSubgroup.torsionBy (Additive Lˣ) (m : ℤ)}
    (he : IsWeilFamily L A Â P e) (ℓ : ℕ) (hℓ : (ℓ : K) ≠ 0) :
    IsWeilData L A Â (he.dualPairingData ℓ hℓ) P :=
  fun n => he.weil (ℓ ^ n) (natCast_pow_ne_zero hℓ n)

/-- The duality datum of a Weil family of a Poincaré pair is its geometric Weil pairing. -/
def IsWeilFamily.isGeometricWeilPairing [IsAlgClosed L]
    {P : Stacks.Picard.ofScheme (A ⊗ Â).left}
    {e : ∀ m : ℕ, (m : K) ≠ 0 →
      AddSubgroup.torsionBy (GeomPoints K L A) (m : ℤ) →+
        AddSubgroup.torsionBy (GeomPoints K L Â) (m : ℤ) →+
          AddSubgroup.torsionBy (Additive Lˣ) (m : ℤ)}
    (he : IsWeilFamily L A Â P e) (hP : IsPoincarePair A Â P) (ℓ : ℕ) (hℓ : (ℓ : K) ≠ 0) :
    IsGeometricWeilPairing L A Â (he.dualPairingData ℓ hℓ) P :=
  ⟨hP, he.isWeilData ℓ hℓ⟩

end Abelian

end ArithmeticOfJacobiPolynomials.WeilPairingGeometry

end
