/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticOverlap
public import Mathlib.Algebra.Category.ModuleCat.Kernels

/-!
# The Čech complex of `𝒪` on the sections of the hyperelliptic model

Let `k` be a field, `f ∈ k[x]`, `X = projectiveModel f`, `U = (affineChart f).opensRange`
(`= D₊(Z)`, `chartOpen f`) and `V = (affineChartAtInfinity f).opensRange` (`= D₊(X)`,
`chartOpenAtInfinity f`). We identify the sections of the structure sheaf over `U`, `V` and
`U ⊓ V` with the rings of `ArithmeticOfJacobiPolynomials.Geometry.HyperellipticGenus`:

* `sectionsEquivFinite f : Γ(X, U) ≃+* k[x, y]/(y^2 - f)`,
  `sectionsEquivInfinite f : Γ(X, V) ≃+* k[x', w]/(w^2 - x'^N f(1/x'))`,
  `sectionsEquivOverlap f : Γ(X, U ⊓ V) ≃+* OverlapRing f`.
  They are obtained from the open immersions `affineChart f`, `affineChartAtInfinity f` and
  `overlapChart f` (`sectionsRingEquiv`: for an open immersion `g : Spec A ⟶ Y` with image `W`,
  `Γ(Y, W) → Γ(Spec A, ⊤) ≅ A`).
* Under these isomorphisms the restriction maps `X.presheaf.map (U ⊓ V ≤ U)` and
  `X.presheaf.map (U ⊓ V ≤ V)` are `cechRestrictFinite f` and `cechRestrictInfinite f`
  (`sectionsEquivOverlap_restrict_left`, `sectionsEquivOverlap_restrict_right`), and the
  structure maps `k → Γ(X, ⊤) → Γ(X, W)` (`sectionsStructureMap`, the `k`-algebra structure
  `sectionsAlgebra`) are the structure maps of the coordinate rings
  (`sectionsEquivFinite_algebraMap`, …), so the isomorphisms are `k`-algebra isomorphisms
  (`sectionsAlgEquivFinite`, `sectionsAlgEquivInfinite`, `sectionsAlgEquivOverlap`).
* Hence the Čech differential of the sections,
  `sectionsCechDifferential f : Γ(X, U) × Γ(X, V) →ₗ[k] Γ(X, U ⊓ V)`,
  `(a, b) ↦ a|_{U ⊓ V} - b|_{U ⊓ V}`, has cokernel `≃ₗ[k] CechH1 f` (`sectionsCechH1Equiv`), of
  dimension `⌊(deg f - 1)/2⌋` (`finrank_sectionsCechH1`), and kernel `≃ₗ[k] k`
  (`sectionsCechH0EquivField`, `finrank_ker_sectionsCechDifferential`). In `ModuleCat k`:
  `cokernelSectionsCechDifferentialIso` and `kernelSectionsCechDifferentialIso`.
  `restrictScalarsSectionsEquiv` identifies `Γ(X, W)` with scalars restricted along
  `sectionsStructureMap f W` with `Γ(X, W)` as a `k`-module (identity map).

The comparison of the cokernel of `sectionsCechDifferential f` with derived-functor
cohomology `H¹(X, 𝒪_X)` is in `ArithmeticOfJacobiPolynomials.Geometry.HyperellipticGenusComparison`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace Hyperelliptic

open Polynomial AlgebraicGeometry CategoryTheory Limits Opposite

universe u

/-! ### Sections over the image of an open immersion of an affine scheme -/

section OpenImmersion

variable {Y : Scheme.{u}} {A : CommRingCat.{u}}

/-- For `g : Spec A ⟶ Y` and an open `W` with `g⁻¹ W = ⊤`, the map
`Γ(Y, W) → Γ(Spec A, ⊤) ≅ A`. -/
@[expose]
noncomputable def sectionsToRing (g : Spec A ⟶ Y) (W : Y.Opens) (h : ⊤ ≤ g ⁻¹ᵁ W) :
    Γ(Y, W) ⟶ A :=
  g.appLE W ⊤ h ≫ (Scheme.ΓSpecIso A).hom

theorem appTop_eq_appLE_top {Y' Z : Scheme.{u}} (φ : Y' ⟶ Z) :
    φ.appTop = φ.appLE ⊤ ⊤ (le_of_eq (TopologicalSpace.Opens.map_top φ.base).symm) :=
  φ.app_eq_appLE

theorem top_le_preimage_of_opensRange_eq (g : Spec A ⟶ Y) [IsOpenImmersion g] {W : Y.Opens}
    (hW : g.opensRange = W) : ⊤ ≤ g ⁻¹ᵁ W := by
  subst hW
  exact (Scheme.Hom.preimage_opensRange g).ge

theorem isIso_sectionsToRing (g : Spec A ⟶ Y) [IsOpenImmersion g] {W : Y.Opens}
    (hW : W ≤ g.opensRange) (h : ⊤ ≤ g ⁻¹ᵁ W) : IsIso (sectionsToRing g W h) := by
  have : IsIso (g.app W) := g.isIso_app W hW
  have : IsIso (homOfLE h) := ⟨⟨homOfLE le_top, rfl, rfl⟩⟩
  rw [sectionsToRing, Scheme.Hom.appLE]
  infer_instance

/-- For an open immersion `g : Spec A ⟶ Y` with image `W`, the ring isomorphism
`Γ(Y, W) ≃+* A`. -/
@[expose]
noncomputable def sectionsRingEquiv (g : Spec A ⟶ Y) [IsOpenImmersion g] {W : Y.Opens}
    (hW : g.opensRange = W) : Γ(Y, W) ≃+* A :=
  haveI := isIso_sectionsToRing g hW.ge (top_le_preimage_of_opensRange_eq g hW)
  (asIso (sectionsToRing g W (top_le_preimage_of_opensRange_eq g hW))).commRingCatIsoToRingEquiv

theorem sectionsRingEquiv_apply (g : Spec A ⟶ Y) [IsOpenImmersion g] {W : Y.Opens}
    (hW : g.opensRange = W) (x : Γ(Y, W)) :
    sectionsRingEquiv g hW x =
      (sectionsToRing g W (top_le_preimage_of_opensRange_eq g hW)).hom x :=
  rfl

/-- **Restriction maps**: if `g' = g ∘ Spec φ` and `W' ≤ W`, then restricting from `W` to `W'`
corresponds to `φ`. -/
theorem map_sectionsToRing {B : CommRingCat.{u}} (g : Spec A ⟶ Y) (g' : Spec B ⟶ Y)
    (φ : A ⟶ B) (hg : Spec.map φ ≫ g = g') {W W' : Y.Opens} (hW : W' ≤ W)
    (h : ⊤ ≤ g ⁻¹ᵁ W) (h' : ⊤ ≤ g' ⁻¹ᵁ W') :
    Y.presheaf.map (homOfLE hW).op ≫ sectionsToRing g' W' h' = sectionsToRing g W h ≫ φ := by
  subst hg
  rw [sectionsToRing, sectionsToRing, Scheme.Hom.map_appLE_assoc, Category.assoc,
    ← Scheme.ΓSpecIso_naturality, appTop_eq_appLE_top, Scheme.Hom.appLE_comp_appLE_assoc]

/-- **Structure maps**: if `g` is a morphism over `Spec R` (`g ≫ π = Spec α`), then
`R → Γ(Y, ⊤) → Γ(Y, W) → A` is `α`. -/
theorem structure_sectionsToRing {R : CommRingCat.{u}} (π : Y ⟶ Spec R) (g : Spec A ⟶ Y)
    (α : R ⟶ A) (hg : g ≫ π = Spec.map α) (W : Y.Opens) (h : ⊤ ≤ g ⁻¹ᵁ W) :
    (Scheme.ΓSpecIso R).inv ≫ π.appTop ≫ Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
      sectionsToRing g W h = α := by
  rw [sectionsToRing, Scheme.Hom.map_appLE_assoc, appTop_eq_appLE_top π,
    Scheme.Hom.appLE_comp_appLE_assoc]
  simp only [hg]
  rw [← appTop_eq_appLE_top, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

end OpenImmersion

/-! ### The charts of the hyperelliptic model -/

variable {k : Type u} [Field k] (f : k[X])

/-- The open `U = D₊(Z)`, the image of the chart `affineChart f`. -/
noncomputable abbrev chartOpen : (projectiveModel f).Opens := (affineChart f).opensRange

/-- The open `V = D₊(X)`, the image of the chart `affineChartAtInfinity f`. -/
noncomputable abbrev chartOpenAtInfinity : (projectiveModel f).Opens :=
  (affineChartAtInfinity f).opensRange

/-- The structure map `k → Γ(Spec k, ⊤) → Γ(X, ⊤)` of the model. -/
@[expose]
noncomputable def globalStructureMap : k →+* Γ(projectiveModel f, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (toSpecField f).appTop).hom

/-- The structure map `k → Γ(X, ⊤) → Γ(X, W)`. -/
@[expose]
noncomputable def sectionsStructureMap (W : (projectiveModel f).Opens) :
    k →+* Γ(projectiveModel f, W) :=
  ((projectiveModel f).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom.comp
    (globalStructureMap f)

/-- `Γ(X, W)` is a `k`-algebra through `k → Γ(X, ⊤) → Γ(X, W)`. -/
noncomputable instance sectionsAlgebra (W : (projectiveModel f).Opens) :
    Algebra k Γ(projectiveModel f, W) :=
  (sectionsStructureMap f W).toAlgebra

theorem algebraMap_sections (W : (projectiveModel f).Opens) (r : k) :
    algebraMap k Γ(projectiveModel f, W) r = sectionsStructureMap f W r :=
  rfl

theorem sectionsStructureMap_restrict {W W' : (projectiveModel f).Opens} (h : W' ≤ W) (r : k) :
    ((projectiveModel f).presheaf.map (homOfLE h).op).hom (sectionsStructureMap f W r) =
      sectionsStructureMap f W' r := by
  change ((projectiveModel f).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
    (projectiveModel f).presheaf.map (homOfLE h).op).hom (globalStructureMap f r) = _
  rw [← Functor.map_comp]
  rfl

/-- The restriction `Γ(X, W) → Γ(X, W')`, `W' ≤ W`, as a `k`-algebra map. -/
@[expose]
noncomputable def sectionsRestrict {W W' : (projectiveModel f).Opens} (h : W' ≤ W) :
    Γ(projectiveModel f, W) →ₐ[k] Γ(projectiveModel f, W') :=
  AlgHom.mk ((projectiveModel f).presheaf.map (homOfLE h).op).hom
    (fun r => sectionsStructureMap_restrict f h r)

theorem sectionsRestrict_apply {W W' : (projectiveModel f).Opens} (h : W' ≤ W)
    (x : Γ(projectiveModel f, W)) :
    sectionsRestrict f h x = ((projectiveModel f).presheaf.map (homOfLE h).op).hom x :=
  rfl

/-- `Γ(X, W)` with scalars restricted along `sectionsStructureMap f W` (the shape
`ModuleCat.restrictScalars ψ (Γ(X, W))` of section functors of sheaves of modules) is `Γ(X, W)`
with the `k`-module structure of `sectionsAlgebra`; the identity map. -/
@[expose]
noncomputable def restrictScalarsSectionsEquiv (W : (projectiveModel f).Opens) :
    (ModuleCat.restrictScalars (sectionsStructureMap f W)).obj
        (ModuleCat.of Γ(projectiveModel f, W) Γ(projectiveModel f, W)) ≃ₗ[k]
      Γ(projectiveModel f, W) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### The ring isomorphisms -/

/-- `Γ(X, U) ≃+* k[x, y]/(y^2 - f(x))`. -/
@[expose]
noncomputable def sectionsEquivFinite :
    Γ(projectiveModel f, chartOpen f) ≃+* HyperellipticCoordRing f :=
  sectionsRingEquiv (affineChart f) rfl

/-- `Γ(X, V) ≃+* k[x', w]/(w^2 - x'^N f(1/x'))`. -/
@[expose]
noncomputable def sectionsEquivInfinite :
    Γ(projectiveModel f, chartOpenAtInfinity f) ≃+*
      HyperellipticCoordRing (reflect (2 * genus f + 2) f) :=
  sectionsRingEquiv (affineChartAtInfinity f) rfl

/-- `Γ(X, U ⊓ V) ≃+* k[x, x⁻¹, y]/(y^2 - f(x))`. -/
@[expose]
noncomputable def sectionsEquivOverlap :
    Γ(projectiveModel f, chartOpen f ⊓ chartOpenAtInfinity f) ≃+* OverlapRing f :=
  sectionsRingEquiv (overlapChart f) (opensRange_overlapChart_eq_inf f)

theorem sectionsEquivFinite_apply (x : Γ(projectiveModel f, chartOpen f)) :
    sectionsEquivFinite f x =
      (sectionsToRing (affineChart f) (chartOpen f)
        (top_le_preimage_of_opensRange_eq (affineChart f) rfl)).hom x :=
  rfl

theorem sectionsEquivInfinite_apply (x : Γ(projectiveModel f, chartOpenAtInfinity f)) :
    sectionsEquivInfinite f x =
      (sectionsToRing (affineChartAtInfinity f) (chartOpenAtInfinity f)
        (top_le_preimage_of_opensRange_eq (affineChartAtInfinity f) rfl)).hom x :=
  rfl

theorem sectionsEquivOverlap_apply
    (x : Γ(projectiveModel f, chartOpen f ⊓ chartOpenAtInfinity f)) :
    sectionsEquivOverlap f x =
      (sectionsToRing (overlapChart f) (chartOpen f ⊓ chartOpenAtInfinity f)
        (top_le_preimage_of_opensRange_eq (overlapChart f)
          (opensRange_overlapChart_eq_inf f))).hom x :=
  rfl

/-- **The restriction `Γ(X, U) → Γ(X, U ⊓ V)` is `cechRestrictFinite f`.** -/
theorem sectionsEquivOverlap_restrict_left (x : Γ(projectiveModel f, chartOpen f)) :
    sectionsEquivOverlap f (((projectiveModel f).presheaf.map
        (homOfLE (inf_le_left : chartOpen f ⊓ chartOpenAtInfinity f ≤ chartOpen f)).op).hom x) =
      cechRestrictFinite f (sectionsEquivFinite f x) := by
  have h := map_sectionsToRing (affineChart f) (overlapChart f)
    (CommRingCat.ofHom (cechRestrictFinite f).toRingHom)
    (SpecMap_cechRestrictFinite_affineChart f)
    (inf_le_left : chartOpen f ⊓ chartOpenAtInfinity f ≤ chartOpen f)
    (top_le_preimage_of_opensRange_eq (affineChart f) rfl)
    (top_le_preimage_of_opensRange_eq (overlapChart f) (opensRange_overlapChart_eq_inf f))
  have hx := congrArg
    (fun φ : Γ(projectiveModel f, chartOpen f) ⟶ CommRingCat.of (OverlapRing f) => φ.hom x) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hx
  rw [sectionsEquivOverlap_apply, sectionsEquivFinite_apply]
  exact hx

/-- **The restriction `Γ(X, V) → Γ(X, U ⊓ V)` is `cechRestrictInfinite f`.** -/
theorem sectionsEquivOverlap_restrict_right (x : Γ(projectiveModel f, chartOpenAtInfinity f)) :
    sectionsEquivOverlap f (((projectiveModel f).presheaf.map
        (homOfLE (inf_le_right : chartOpen f ⊓ chartOpenAtInfinity f ≤
          chartOpenAtInfinity f)).op).hom x) =
      cechRestrictInfinite f (sectionsEquivInfinite f x) := by
  have h := map_sectionsToRing (affineChartAtInfinity f) (overlapChart f)
    (CommRingCat.ofHom (cechRestrictInfinite f).toRingHom)
    (SpecMap_cechRestrictInfinite_affineChartAtInfinity f)
    (inf_le_right : chartOpen f ⊓ chartOpenAtInfinity f ≤ chartOpenAtInfinity f)
    (top_le_preimage_of_opensRange_eq (affineChartAtInfinity f) rfl)
    (top_le_preimage_of_opensRange_eq (overlapChart f) (opensRange_overlapChart_eq_inf f))
  have hx := congrArg
    (fun φ : Γ(projectiveModel f, chartOpenAtInfinity f) ⟶ CommRingCat.of (OverlapRing f) =>
      φ.hom x) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hx
  rw [sectionsEquivOverlap_apply, sectionsEquivInfinite_apply]
  exact hx

theorem sectionsEquivFinite_algebraMap (r : k) :
    sectionsEquivFinite f (algebraMap k _ r) = algebraMap k (HyperellipticCoordRing f) r := by
  have h := structure_sectionsToRing (toSpecField f) (affineChart f)
    (CommRingCat.ofHom (algebraMap k (HyperellipticCoordRing f)))
    (chart_toSpecField (chartData_finite f)) (chartOpen f)
    (top_le_preimage_of_opensRange_eq (affineChart f) rfl)
  have hr := congrArg
    (fun φ : CommRingCat.of k ⟶ CommRingCat.of (HyperellipticCoordRing f) => φ.hom r) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hr
  simp only [algebraMap_sections, sectionsStructureMap, globalStructureMap,
    CommRingCat.hom_comp, RingHom.comp_apply, sectionsEquivFinite_apply]
  exact hr

theorem sectionsEquivInfinite_algebraMap (r : k) :
    sectionsEquivInfinite f (algebraMap k _ r) =
      algebraMap k (HyperellipticCoordRing (reflect (2 * genus f + 2) f)) r := by
  have h := structure_sectionsToRing (toSpecField f) (affineChartAtInfinity f)
    (CommRingCat.ofHom (algebraMap k (HyperellipticCoordRing (reflect (2 * genus f + 2) f))))
    (chart_toSpecField (chartData_infinite f)) (chartOpenAtInfinity f)
    (top_le_preimage_of_opensRange_eq (affineChartAtInfinity f) rfl)
  have hr := congrArg
    (fun φ : CommRingCat.of k ⟶
      CommRingCat.of (HyperellipticCoordRing (reflect (2 * genus f + 2) f)) => φ.hom r) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hr
  simp only [algebraMap_sections, sectionsStructureMap, globalStructureMap,
    CommRingCat.hom_comp, RingHom.comp_apply, sectionsEquivInfinite_apply]
  exact hr

theorem sectionsEquivOverlap_algebraMap (r : k) :
    sectionsEquivOverlap f (algebraMap k _ r) = algebraMap k (OverlapRing f) r := by
  have h := structure_sectionsToRing (toSpecField f) (overlapChart f)
    (CommRingCat.ofHom (algebraMap k (OverlapRing f))) (overlapChart_toSpecField f)
    (chartOpen f ⊓ chartOpenAtInfinity f)
    (top_le_preimage_of_opensRange_eq (overlapChart f) (opensRange_overlapChart_eq_inf f))
  have hr := congrArg
    (fun φ : CommRingCat.of k ⟶ CommRingCat.of (OverlapRing f) => φ.hom r) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hr
  simp only [algebraMap_sections, sectionsStructureMap, globalStructureMap,
    CommRingCat.hom_comp, RingHom.comp_apply, sectionsEquivOverlap_apply]
  exact hr

/-- `Γ(X, U) ≃ₐ[k] k[x, y]/(y^2 - f(x))`. -/
@[expose]
noncomputable def sectionsAlgEquivFinite :
    Γ(projectiveModel f, chartOpen f) ≃ₐ[k] HyperellipticCoordRing f :=
  AlgEquiv.ofRingEquiv (f := sectionsEquivFinite f) (sectionsEquivFinite_algebraMap f)

/-- `Γ(X, V) ≃ₐ[k] k[x', w]/(w^2 - x'^N f(1/x'))`. -/
@[expose]
noncomputable def sectionsAlgEquivInfinite :
    Γ(projectiveModel f, chartOpenAtInfinity f) ≃ₐ[k]
      HyperellipticCoordRing (reflect (2 * genus f + 2) f) :=
  AlgEquiv.ofRingEquiv (f := sectionsEquivInfinite f) (sectionsEquivInfinite_algebraMap f)

/-- `Γ(X, U ⊓ V) ≃ₐ[k] k[x, x⁻¹, y]/(y^2 - f(x))`. -/
@[expose]
noncomputable def sectionsAlgEquivOverlap :
    Γ(projectiveModel f, chartOpen f ⊓ chartOpenAtInfinity f) ≃ₐ[k] OverlapRing f :=
  AlgEquiv.ofRingEquiv (f := sectionsEquivOverlap f) (sectionsEquivOverlap_algebraMap f)

/-! ### The Čech complex of the sections -/

/-- **The Čech differential of the sections** `Γ(X, U) × Γ(X, V) → Γ(X, U ⊓ V)`,
`(a, b) ↦ a|_{U ⊓ V} - b|_{U ⊓ V}`. -/
@[expose]
noncomputable def sectionsCechDifferential :
    (Γ(projectiveModel f, chartOpen f) × Γ(projectiveModel f, chartOpenAtInfinity f)) →ₗ[k]
      Γ(projectiveModel f, chartOpen f ⊓ chartOpenAtInfinity f) :=
  (sectionsRestrict f (inf_le_left : chartOpen f ⊓ chartOpenAtInfinity f ≤
      chartOpen f)).toLinearMap ∘ₗ LinearMap.fst k _ _ -
    (sectionsRestrict f (inf_le_right : chartOpen f ⊓ chartOpenAtInfinity f ≤
      chartOpenAtInfinity f)).toLinearMap ∘ₗ LinearMap.snd k _ _

theorem sectionsCechDifferential_apply (a : Γ(projectiveModel f, chartOpen f))
    (b : Γ(projectiveModel f, chartOpenAtInfinity f)) :
    sectionsCechDifferential f (a, b) =
      ((projectiveModel f).presheaf.map
        (homOfLE (inf_le_left : chartOpen f ⊓ chartOpenAtInfinity f ≤ chartOpen f)).op).hom a -
      ((projectiveModel f).presheaf.map
        (homOfLE (inf_le_right : chartOpen f ⊓ chartOpenAtInfinity f ≤
          chartOpenAtInfinity f)).op).hom b :=
  rfl

/-- The product `Γ(X, U) × Γ(X, V) ≃ₗ[k] A_Z × A_X`. -/
@[expose]
noncomputable def sectionsProdEquiv :
    (Γ(projectiveModel f, chartOpen f) × Γ(projectiveModel f, chartOpenAtInfinity f)) ≃ₗ[k]
      (HyperellipticCoordRing f × HyperellipticCoordRing (reflect (2 * genus f + 2) f)) :=
  (sectionsAlgEquivFinite f).toLinearEquiv.prodCongr (sectionsAlgEquivInfinite f).toLinearEquiv

theorem sectionsAlgEquivOverlap_sectionsCechDifferential (a : Γ(projectiveModel f, chartOpen f))
    (b : Γ(projectiveModel f, chartOpenAtInfinity f)) :
    sectionsAlgEquivOverlap f (sectionsCechDifferential f (a, b)) =
      cechDifferential f (sectionsAlgEquivFinite f a, sectionsAlgEquivInfinite f b) := by
  rw [sectionsCechDifferential_apply, map_sub, cechDifferential_apply]
  exact congrArg₂ (· - ·) (sectionsEquivOverlap_restrict_left f a)
    (sectionsEquivOverlap_restrict_right f b)

/-- **The Čech complex of the sections is the Čech complex of `HyperellipticGenus`**:
`sectionsAlgEquivOverlap ∘ sectionsCechDifferential = cechDifferential ∘ sectionsProdEquiv`. -/
theorem sectionsCechDifferential_comm :
    ((sectionsAlgEquivOverlap f).toLinearEquiv : _ →ₗ[k] OverlapRing f) ∘ₗ
        sectionsCechDifferential f =
      cechDifferential f ∘ₗ (sectionsProdEquiv f : _ →ₗ[k] _) :=
  LinearMap.ext fun p => sectionsAlgEquivOverlap_sectionsCechDifferential f p.1 p.2

theorem map_range_sectionsCechDifferential :
    (LinearMap.range (sectionsCechDifferential f)).map
        ((sectionsAlgEquivOverlap f).toLinearEquiv : _ →ₗ[k] OverlapRing f) =
      LinearMap.range (cechDifferential f) := by
  rw [← LinearMap.range_comp, sectionsCechDifferential_comm,
    LinearMap.range_comp_of_range_eq_top _ (sectionsProdEquiv f).range]

theorem map_ker_sectionsCechDifferential :
    (LinearMap.ker (sectionsCechDifferential f)).map (sectionsProdEquiv f : _ →ₗ[k] _) =
      LinearMap.ker (cechDifferential f) := by
  ext y
  rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
  have hy := LinearMap.congr_fun (sectionsCechDifferential_comm f) ((sectionsProdEquiv f).symm y)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at hy
  constructor
  · intro h
    rw [← hy, h, map_zero]
  · intro h
    apply (sectionsAlgEquivOverlap f).toLinearEquiv.injective
    rw [hy, h, map_zero]

/-- **The cokernel of the Čech differential of the sections is `CechH1 f`.** -/
@[expose]
noncomputable def sectionsCechH1Equiv :
    (Γ(projectiveModel f, chartOpen f ⊓ chartOpenAtInfinity f) ⧸
        LinearMap.range (sectionsCechDifferential f)) ≃ₗ[k] CechH1 f :=
  Submodule.Quotient.equiv _ _ (sectionsAlgEquivOverlap f).toLinearEquiv
    (map_range_sectionsCechDifferential f)

/-- **The kernel of the Čech differential of the sections is `CechH0 f`.** -/
@[expose]
noncomputable def sectionsCechH0Equiv :
    LinearMap.ker (sectionsCechDifferential f) ≃ₗ[k] CechH0 f :=
  (sectionsProdEquiv f).ofSubmodules _ _ (map_ker_sectionsCechDifferential f)

/-- The kernel of the Čech differential of the sections consists of the constants `k`. -/
@[expose]
noncomputable def sectionsCechH0EquivField :
    LinearMap.ker (sectionsCechDifferential f) ≃ₗ[k] k :=
  (sectionsCechH0Equiv f).trans (cechH0Equiv f).symm

/-- **`dim_k coker = ⌊(deg f - 1)/2⌋`** for the Čech differential of the sections. -/
theorem finrank_sectionsCechH1 :
    Module.finrank k (Γ(projectiveModel f, chartOpen f ⊓ chartOpenAtInfinity f) ⧸
        LinearMap.range (sectionsCechDifferential f)) = (f.natDegree - 1) / 2 :=
  (sectionsCechH1Equiv f).finrank_eq.trans (finrank_cechH1 f)

/-- **`dim_k ker = 1`** for the Čech differential of the sections. -/
theorem finrank_ker_sectionsCechDifferential :
    Module.finrank k (LinearMap.ker (sectionsCechDifferential f)) = 1 :=
  (sectionsCechH0Equiv f).finrank_eq.trans (finrank_cechH0 f)

/-- The categorical cokernel (in `ModuleCat k`) of the Čech differential of the sections is
`CechH1 f`. -/
@[expose]
noncomputable def cokernelSectionsCechDifferentialIso :
    cokernel (ModuleCat.ofHom (sectionsCechDifferential f)) ≅ ModuleCat.of k (CechH1 f) :=
  ModuleCat.cokernelIsoRangeQuotient _ ≪≫ (sectionsCechH1Equiv f).toModuleIso

/-- The categorical kernel (in `ModuleCat k`) of the Čech differential of the sections is `k`. -/
@[expose]
noncomputable def kernelSectionsCechDifferentialIso :
    kernel (ModuleCat.ofHom (sectionsCechDifferential f)) ≅ ModuleCat.of k k :=
  ModuleCat.kernelIsoKer _ ≪≫ (sectionsCechH0EquivField f).toModuleIso

end Hyperelliptic

end ArithmeticOfJacobiPolynomials
