/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticCechSections

/-!
# Global sections of the hyperelliptic model

For every field `k` and `f ∈ k[x]`, the structure map `k → Γ(X, ⊤)` of `X = projectiveModel f`
is bijective: the global regular functions on the model are the constants. The proof glues
sections over the two affine charts (`TopCat.Sheaf.objSupIsoProdEqLocus`), so `Γ(X, ⊤)` is the
kernel of the Čech differential, which is one-dimensional (`finrank_ker_sectionsCechDifferential`);
an injective `k`-linear map between one-dimensional spaces is bijective.

* `finrank_globalSections`: `dim_k Γ(X, ⊤) = 1`;
* `globalStructureMap_bijective`, `globalSectionsAlgEquiv : Γ(X, ⊤) ≃ₐ[k] k`;
* `isIso_globalStructureMorphism`: `Γ(Spec k, ⊤) ≅ k → Γ(X, ⊤)` is an isomorphism of
  commutative rings.
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace Hyperelliptic

open Polynomial AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

variable {k : Type u} [Field k] (f : k[X])

theorem chartOpen_sup_chartOpenAtInfinity' : chartOpen f ⊔ chartOpenAtInfinity f = ⊤ := by
  rw [chartOpen, chartOpenAtInfinity, opensRange_affineChart, opensRange_affineChartAtInfinity]
  exact iSup_chart_eq_top f

/-- `sectionsStructureMap f ⊤` is `globalStructureMap f`. -/
theorem sectionsStructureMap_top : sectionsStructureMap f ⊤ = globalStructureMap f := by
  ext r
  change ((projectiveModel f).presheaf.map (𝟙 (op ⊤))).hom (globalStructureMap f r) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- The restriction of global sections to the two charts, as a `k`-linear map. -/
@[expose]
noncomputable def globalRestrict :
    Γ(projectiveModel f, ⊤) →ₗ[k]
      (Γ(projectiveModel f, chartOpen f) × Γ(projectiveModel f, chartOpenAtInfinity f)) :=
  (sectionsRestrict f (le_top : chartOpen f ≤ ⊤)).toLinearMap.prod
    (sectionsRestrict f (le_top : chartOpenAtInfinity f ≤ ⊤)).toLinearMap

theorem globalRestrict_injective : Function.Injective (globalRestrict f) := by
  intro s t hst
  have h1 := congrArg Prod.fst hst
  have h2 := congrArg Prod.snd hst
  exact TopCat.Sheaf.eq_of_locally_eq₂ (projectiveModel f).sheaf
    (homOfLE (le_top : chartOpen f ≤ ⊤)) (homOfLE (le_top : chartOpenAtInfinity f ≤ ⊤))
    (chartOpen_sup_chartOpenAtInfinity' f).ge s t h1 h2

theorem presheaf_map_map {W₁ W₂ W₃ : (projectiveModel f).Opens} (h₁ : W₂ ≤ W₁) (h₂ : W₃ ≤ W₂)
    (x : Γ(projectiveModel f, W₁)) :
    ((projectiveModel f).presheaf.map (homOfLE h₂).op).hom
        (((projectiveModel f).presheaf.map (homOfLE h₁).op).hom x) =
      ((projectiveModel f).presheaf.map (homOfLE (h₂.trans h₁)).op).hom x := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem range_globalRestrict :
    LinearMap.range (globalRestrict f) = LinearMap.ker (sectionsCechDifferential f) := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨s, hs⟩
    rw [← hs, LinearMap.mem_ker]
    change ((projectiveModel f).presheaf.map (homOfLE (inf_le_left :
          chartOpen f ⊓ chartOpenAtInfinity f ≤ chartOpen f)).op).hom
        (((projectiveModel f).presheaf.map (homOfLE (le_top : chartOpen f ≤ ⊤)).op).hom s) -
      ((projectiveModel f).presheaf.map (homOfLE (inf_le_right :
          chartOpen f ⊓ chartOpenAtInfinity f ≤ chartOpenAtInfinity f)).op).hom
        (((projectiveModel f).presheaf.map
          (homOfLE (le_top : chartOpenAtInfinity f ≤ ⊤)).op).hom s) = 0
    rw [presheaf_map_map, presheaf_map_map, sub_eq_zero]
  · intro h
    rw [LinearMap.mem_ker] at h
    change ((projectiveModel f).presheaf.map (homOfLE (inf_le_left :
          chartOpen f ⊓ chartOpenAtInfinity f ≤ chartOpen f)).op).hom a -
      ((projectiveModel f).presheaf.map (homOfLE (inf_le_right :
          chartOpen f ⊓ chartOpenAtInfinity f ≤ chartOpenAtInfinity f)).op).hom b = 0 at h
    rw [sub_eq_zero] at h
    set F := (projectiveModel f).sheaf with hF
    let x : CommRingCat.of (RingHom.eqLocus
        (RingHom.comp (F.obj.map (homOfLE inf_le_left :
          chartOpen f ⊓ chartOpenAtInfinity f ⟶ chartOpen f).op).hom
          (RingHom.fst (F.obj.obj (op (chartOpen f))) (F.obj.obj (op (chartOpenAtInfinity f)))))
        (RingHom.comp (F.obj.map (homOfLE inf_le_right :
          chartOpen f ⊓ chartOpenAtInfinity f ⟶ chartOpenAtInfinity f).op).hom
          (RingHom.snd (F.obj.obj (op (chartOpen f))) (F.obj.obj (op (chartOpenAtInfinity f)))))) :=
      ⟨(a, b), h⟩
    obtain ⟨s₀, hs₀⟩ :
        ∃ s₀, s₀ = (F.objSupIsoProdEqLocus (chartOpen f) (chartOpenAtInfinity f)).inv x :=
      ⟨_, rfl⟩
    have hfst :=
      TopCat.Sheaf.objSupIsoProdEqLocus_hom_fst F (chartOpen f) (chartOpenAtInfinity f) s₀
    have hsnd :=
      TopCat.Sheaf.objSupIsoProdEqLocus_hom_snd F (chartOpen f) (chartOpenAtInfinity f) s₀
    rw [hs₀, Iso.inv_hom_id_apply] at hfst hsnd
    refine ⟨((projectiveModel f).presheaf.map
        (homOfLE (chartOpen_sup_chartOpenAtInfinity' f).ge).op).hom s₀, Prod.ext ?_ ?_⟩
    · change ((projectiveModel f).presheaf.map (homOfLE (le_top : chartOpen f ≤ ⊤)).op).hom
        (((projectiveModel f).presheaf.map
          (homOfLE (chartOpen_sup_chartOpenAtInfinity' f).ge).op).hom s₀) = a
      refine (presheaf_map_map f _ _ s₀).trans ?_
      rw [hs₀]
      exact hfst.symm
    · change ((projectiveModel f).presheaf.map
          (homOfLE (le_top : chartOpenAtInfinity f ≤ ⊤)).op).hom
        (((projectiveModel f).presheaf.map
          (homOfLE (chartOpen_sup_chartOpenAtInfinity' f).ge).op).hom s₀) = b
      refine (presheaf_map_map f _ _ s₀).trans ?_
      rw [hs₀]
      exact hsnd.symm

/-- **`dim_k Γ(X, ⊤) = 1`.** -/
theorem finrank_globalSections : Module.finrank k Γ(projectiveModel f, ⊤) = 1 := by
  rw [← LinearMap.finrank_range_of_inj (globalRestrict_injective f), range_globalRestrict]
  exact finrank_ker_sectionsCechDifferential f

/-- **The constants are the only global sections**: `k → Γ(X, ⊤)` is bijective. -/
theorem globalStructureMap_bijective : Function.Bijective (globalStructureMap f) := by
  have h1 := finrank_globalSections f
  have : Module.Finite k Γ(projectiveModel f, ⊤) := Module.finite_of_finrank_eq_succ h1
  have : Nontrivial Γ(projectiveModel f, ⊤) := Module.nontrivial_of_finrank_eq_succ h1
  have hinj : Function.Injective (Algebra.linearMap k Γ(projectiveModel f, ⊤)) :=
    (algebraMap k Γ(projectiveModel f, ⊤)).injective
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [Module.finrank_self, h1])).mp hinj
  have e : ⇑(Algebra.linearMap k Γ(projectiveModel f, ⊤)) = globalStructureMap f := by
    funext r
    rw [Algebra.linearMap_apply, algebraMap_sections, sectionsStructureMap_top]
  rw [← e]
  exact ⟨hinj, hsurj⟩

/-- **`Γ(X, ⊤) ≃ₐ[k] k`**, inverse to the structure map. -/
@[expose]
noncomputable def globalSectionsAlgEquiv : Γ(projectiveModel f, ⊤) ≃ₐ[k] k :=
  (AlgEquiv.ofBijective (Algebra.ofId k Γ(projectiveModel f, ⊤)) (by
    have e : ⇑(Algebra.ofId k Γ(projectiveModel f, ⊤)) = globalStructureMap f := by
      funext r
      rw [Algebra.ofId_apply, algebraMap_sections, sectionsStructureMap_top]
    rw [e]
    exact globalStructureMap_bijective f)).symm

/-- The structure morphism `Γ(Spec k, ⊤) ≅ k ⟶ Γ(X, ⊤)` is an isomorphism of commutative
rings. -/
theorem isIso_globalStructureMorphism :
    IsIso ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (toSpecField f).appTop) := by
  let e := (RingEquiv.ofBijective (globalStructureMap f)
    (globalStructureMap_bijective f)).toCommRingCatIso
  have he : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (toSpecField f).appTop = e.hom := by
    ext x
    rfl
  rw [he]
  infer_instance

end Hyperelliptic

end ArithmeticOfJacobiPolynomials
