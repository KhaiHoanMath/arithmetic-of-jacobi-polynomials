/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticCurve
public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticGenusComparison
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Base change of the hyperelliptic model

Let `k` be a field, `f ∈ k[x]` and `K/k` a field extension (`K` in the same universe). The
projective model `projectiveModel f = Proj k[X, Z, Y]/(Y^2 - Z^N f(X/Z))`
(`ArithmeticOfJacobiPolynomials.Geometry.HyperellipticProjective`) commutes with base change:

* `baseChangeGradedHom K f`: the graded ring map `k[X, Z, Y]/(Y^2 - F) → K[X, Z, Y]/(Y^2 - F)`
  induced by `k → K` (the genus `⌊(d - 1)/2⌋`, hence the weights, is unchanged);
* `baseChangeMap K f : projectiveModel (f.map (algebraMap k K)) ⟶ projectiveModel f`, the
  induced morphism `Proj.map`;
* **`isPullback_baseChangeMap`**: the square
  ```
  projectiveModel (f ⊗ K) ──→ projectiveModel f
          │                          │
       Spec K ───────────────→   Spec k
  ```
  is a pullback square of schemes;
* `baseChangeIso K f : pullback (toSpecField f) (Spec.map (algebraMap k K)) ≅
  projectiveModel (f.map (algebraMap k K))`, compatible with the structure maps to `Spec K`
  (`baseChangeIso_hom_toSpecField`) and to the model over `k`
  (`baseChangeIso_hom_baseChangeMap`).

The pullback property is checked on the two charts `D₊(Z)` and `D₊(X)`: on a chart the square is
`Spec` of the square of rings `k → k[x, y]/(y^2 - p(x))`, `K → K[x, y]/(y^2 - p(x))`, which is a
pushout (`isPushout_hyperelliptic`, by the universal property of `AdjoinRoot`); a morphism over a
base change which is a pullback over each member of an open cover of the target is a pullback
(`isPullback_of_cover`).

Consequences, for `f` separable of degree `≥ 1`:

* **`geometricallyIntegral_toSpecField`**: `projectiveModel f → Spec k` is geometrically integral
  (Mathlib's `GeometricallyIntegral`: every base change to a field is an integral scheme);
* `baseChange_curve` (for `2 ≠ 0` in `k`): over every field extension `K/k` (in particular over
  an algebraic closure) the model of `f ⊗ K` is smooth and proper over `K`, integral, of dimension
  one and of genus `dim_K H¹(𝒪) = ⌊(deg f - 1)/2⌋`;
* `pullback_curve`: the base change `pullback (toSpecField f) (Spec.map (algebraMap k K))` itself
  is smooth and proper over `K` (via `pullback.snd`), integral and of dimension one.
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace Hyperelliptic

open Polynomial AlgebraicGeometry CategoryTheory Limits GradedQuotient

universe u

/-! ### A local criterion for pullback squares of schemes -/

section Abstract

variable {X' X S' S : Scheme.{u}}

theorem isIso_of_isPullback_restrict {g : X ⟶ S} {h : S' ⟶ S} (τ : X' ⟶ pullback g h)
    {F : X' ⟶ X} {g' : X' ⟶ S'} (hF : τ ≫ pullback.fst g h = F)
    (hg : τ ≫ pullback.snd g h = g') {ι : Type*} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (H : ∀ i, IsPullback (F ∣_ U i) ((F ⁻¹ᵁ U i).ι ≫ g') ((U i).ι ≫ g) h) : IsIso τ := by
  subst hF hg
  have hU' : iSup (fun i => pullback.fst g h ⁻¹ᵁ U i) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]
  have key : ∀ i, IsIso (τ ∣_ (pullback.fst g h ⁻¹ᵁ U i)) := by
    intro i
    have BC := (isPullback_morphismRestrict (pullback.fst g h) (U i)).paste_vert
      (IsPullback.of_hasPullback g h)
    have e := Scheme.Hom.comp_preimage τ (pullback.fst g h) (U i)
    have Hi : IsPullback (τ ∣_ (pullback.fst g h ⁻¹ᵁ U i) ≫ pullback.fst g h ∣_ U i)
        ((τ ⁻¹ᵁ (pullback.fst g h ⁻¹ᵁ U i)).ι ≫ τ ≫ pullback.snd g h) ((U i).ι ≫ g) h := by
      refine (H i).of_iso (X'.isoOfEq e) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      · rw [Iso.refl_hom, Category.comp_id, ← cancel_mono (U i).ι, Category.assoc,
          Category.assoc, morphismRestrict_ι, morphismRestrict_ι, morphismRestrict_ι_assoc,
          Scheme.isoOfEq_hom_ι_assoc]
      · rw [Iso.refl_hom, Category.comp_id, Scheme.isoOfEq_hom_ι_assoc]
      · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    have he : (Hi.isoIsPullback _ _ BC).hom = τ ∣_ (pullback.fst g h ⁻¹ᵁ U i) := by
      refine BC.hom_ext ?_ ?_
      · exact IsPullback.isoIsPullback_hom_fst _ _ Hi BC
      · rw [IsPullback.isoIsPullback_hom_snd, morphismRestrict_ι_assoc]
    rw [← he]
    infer_instance
  rw [isIso_iff_isOpenImmersion_and_surjective]
  constructor
  · refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsOpenImmersion) _ hU' fun i => ?_
    have := key i
    change IsOpenImmersion (τ ∣_ (pullback.fst g h ⁻¹ᵁ U i))
    infer_instance
  · refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Surjective) _ hU' fun i => ?_
    have := key i
    change Surjective (τ ∣_ (pullback.fst g h ⁻¹ᵁ U i))
    infer_instance

/-- **Local criterion for pullbacks.** Let `F : X' ⟶ X` lie over `h : S' ⟶ S` (via
`g' : X' ⟶ S'`, `g : X ⟶ S`). If for an open cover `(U_i)` of `X` every restricted square
`F⁻¹(U_i) → U_i` over `S' → S` is a pullback, then so is the whole square. -/
theorem isPullback_of_cover (F : X' ⟶ X) (g' : X' ⟶ S') (g : X ⟶ S) (h : S' ⟶ S)
    {ι : Type*} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (H : ∀ i, IsPullback (F ∣_ U i) ((F ⁻¹ᵁ U i).ι ≫ g') ((U i).ι ≫ g) h) :
    IsPullback F g' g h := by
  have hV : TopologicalSpace.IsOpenCover (fun i => F ⁻¹ᵁ U i) := by
    change iSup (fun i => F ⁻¹ᵁ U i) = ⊤
    rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]
  have w : F ≫ g = g' ≫ h := by
    refine Scheme.Cover.hom_ext (X'.openCoverOfIsOpenCover _ hV) _ _ fun i => ?_
    change (F ⁻¹ᵁ U i).ι ≫ F ≫ g = (F ⁻¹ᵁ U i).ι ≫ g' ≫ h
    rw [← morphismRestrict_ι_assoc, (H i).w, Category.assoc]
  have := isIso_of_isPullback_restrict (pullback.lift F g' w) (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _) U hU H
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso (pullback.lift F g' w)) (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)

end Abstract

/-! ### Homogeneous localizations at equal elements -/

section AwayCongr

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- `A[t⁻¹]₀ ≃ A[t'⁻¹]₀` for `t = t'`. -/
noncomputable def awayCongr {t t' : A} (h : t = t') :
    HomogeneousLocalization.Away 𝒜 t ≃+* HomogeneousLocalization.Away 𝒜 t' := by
  subst h
  exact RingEquiv.refl _

theorem awayCongr_mk {t t' : A} (h : t = t') {d : ℕ} (ht : t ∈ 𝒜 d) (n : ℕ) (a : A)
    (ha : a ∈ 𝒜 (n • d)) :
    awayCongr 𝒜 h (HomogeneousLocalization.Away.mk 𝒜 ht n a ha) =
      HomogeneousLocalization.Away.mk 𝒜 (h ▸ ht) n a ha := by
  subst h
  rfl

theorem awayCongr_fromZeroRingHom {t t' : A} (h : t = t') (a : 𝒜 0) :
    awayCongr 𝒜 h (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers t) a) =
      HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers t') a := by
  subst h
  rfl

theorem away_mk_congr {t : A} {d : ℕ} (ht : t ∈ 𝒜 d) {n n' : ℕ} (hn : n = n') {a a' : A}
    (ha : a = a') (h1 : a ∈ 𝒜 (n • d)) (h2 : a' ∈ 𝒜 (n' • d)) :
    HomogeneousLocalization.Away.mk 𝒜 ht n a h1 =
      HomogeneousLocalization.Away.mk 𝒜 ht n' a' h2 := by
  subst hn ha
  rfl

theorem awayMap_fromZeroRingHom {B τ : Type*} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {ℬ : ℕ → τ} [GradedRing ℬ] (g : GradedRingHom 𝒜 ℬ) (s : A) (a : 𝒜 0) :
    HomogeneousLocalization.Away.map g s
        (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers s) a) =
      HomogeneousLocalization.fromZeroRingHom ℬ (Submonoid.powers (g s))
        ⟨g a, g.map_mem a.2⟩ := by
  apply HomogeneousLocalization.val_injective
  change Localization.mk (g (a : A)) (⟨g 1, _⟩ : Submonoid.powers (g s)) =
    Localization.mk (g (a : A)) (⟨1, _⟩ : Submonoid.powers (g s))
  exact congrArg (Localization.mk _) (Subtype.ext (map_one g))

end AwayCongr

/-! ### The base change of the homogeneous coordinate ring -/

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]

theorem genus_map (f : k[X]) : genus (f.map (algebraMap k K)) = genus f := by
  unfold genus
  rw [natDegree_map]

theorem equation_map (o c : Fin 3) (p : k[X]) (N : ℕ) :
    MvPolynomial.map (algebraMap k K) (equation o c p N) =
      equation o c (p.map (algebraMap k K)) N := by
  simp only [equation, binaryForm, map_sub, map_pow, map_sum, map_mul, MvPolynomial.map_X,
    MvPolynomial.map_C, Polynomial.coeff_map]

theorem map_coordIdeal (f : k[X]) :
    Ideal.map (MvPolynomial.map (algebraMap k K)) (coordIdeal f) =
      coordIdeal (f.map (algebraMap k K)) := by
  rw [coordIdeal, coordIdeal, Ideal.map_span, Set.image_singleton, equation_map, genus_map]

theorem coordIdeal_le_comap (f : k[X]) :
    coordIdeal f ≤
      (coordIdeal (f.map (algebraMap k K))).comap (MvPolynomial.map (algebraMap k K)) := by
  rw [← map_coordIdeal]
  exact Ideal.le_comap_map

/-- `k[X, Z, Y]/(Y^2 - F) → K[X, Z, Y]/(Y^2 - F)`. -/
@[expose]
noncomputable def baseChangeRingHom (f : k[X]) :
    HomogeneousCoordRing f →+* HomogeneousCoordRing (f.map (algebraMap k K)) :=
  Ideal.quotientMap _ (MvPolynomial.map (algebraMap k K)) (coordIdeal_le_comap K f)

theorem baseChangeRingHom_mk (f : k[X]) (P : MvPolynomial (Fin 3) k) :
    baseChangeRingHom K f (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap k K) P) :=
  Ideal.quotientMap_mk

theorem baseChangeRingHom_var (f : k[X]) (i : Fin 3) :
    baseChangeRingHom K f (var f i) = var (f.map (algebraMap k K)) i := by
  rw [var, var, baseChangeRingHom_mk, MvPolynomial.map_X]

theorem baseChangeRingHom_algebraMap (f : k[X]) (r : k) :
    baseChangeRingHom K f (algebraMap k _ r) = algebraMap K _ (algebraMap k K r) := by
  rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, baseChangeRingHom_mk,
    MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_eq, MvPolynomial.map_C]

theorem baseChangeRingHom_mem (f : k[X]) {n : ℕ} {x : HomogeneousCoordRing f}
    (hx : x ∈ grading f n) :
    baseChangeRingHom K f x ∈ grading (f.map (algebraMap k K)) n := by
  obtain ⟨P, hP, rfl⟩ := hx
  have hP' : P.IsWeightedHomogeneous (weights (genus f)) n := hP
  refine Submodule.mem_map.mpr ⟨MvPolynomial.map (algebraMap k K) P, ?_, ?_⟩
  · change (MvPolynomial.map (algebraMap k K) P).IsWeightedHomogeneous
      (weights (genus (f.map (algebraMap k K)))) n
    rw [genus_map]
    intro d hd
    apply hP'
    intro h0
    apply hd
    rw [MvPolynomial.coeff_map, h0, map_zero]
  · exact (baseChangeRingHom_mk K f P).symm

/-- The graded ring map `S_f → S_{f ⊗ K}`. -/
@[expose]
noncomputable def baseChangeGradedHom (f : k[X]) :
    GradedRingHom (grading f) (grading (f.map (algebraMap k K))) where
  toRingHom := baseChangeRingHom K f
  map_mem := baseChangeRingHom_mem K f

theorem baseChangeGradedHom_apply (f : k[X]) (x : HomogeneousCoordRing f) :
    baseChangeGradedHom K f x = baseChangeRingHom K f x :=
  rfl

theorem baseChangeGradedHom_var (f : k[X]) (i : Fin 3) :
    baseChangeGradedHom K f (var f i) = var (f.map (algebraMap k K)) i :=
  baseChangeRingHom_var K f i

/-- The irrelevant ideal is generated by the variables. -/
theorem irrelevant_le_span_var (f : k[X]) :
    (HomogeneousIdeal.irrelevant (grading f)).toIdeal ≤ Ideal.span (Set.range (var f)) := by
  intro x hx
  convert_to x - GradedRing.projZeroRingHom (grading f) x ∈ _
  · rw [GradedRing.projZeroRingHom_apply, ← GradedRing.proj_apply,
      (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx, sub_zero]
  clear hx
  have := (eq_iff_iff.mp congr(x ∈ $(adjoin_range_var f))).mpr trivial
  induction this using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [GradedRing.projZeroRingHom_apply,
      DirectSum.decompose_of_mem_ne (grading f) (var_mem f i) (weights_ne_zero _ i), sub_zero]
    exact Ideal.subset_span ⟨i, rfl⟩
  | algebraMap r =>
    convert zero_mem (Ideal.span _)
    rw [sub_eq_zero]
    exact (DirectSum.decompose_of_mem_same (grading f) r.2).symm
  | add x y _ _ hx hy =>
    rw [map_add, add_sub_add_comm]
    exact add_mem hx hy
  | mul x y _ _ hx' hy' =>
    convert add_mem (Ideal.mul_mem_left _ x hy')
      (Ideal.mul_mem_right (GradedRing.projZeroRingHom (grading f) y) _ hx') using 1
    rw [map_mul]
    ring

theorem irrelevant_le_map (f : k[X]) :
    HomogeneousIdeal.irrelevant (grading (f.map (algebraMap k K))) ≤
      (HomogeneousIdeal.irrelevant (grading f)).map (baseChangeGradedHom K f) := by
  intro x hx
  have h1 := irrelevant_le_span_var (f.map (algebraMap k K)) hx
  have h2 : Ideal.span (Set.range (var (f.map (algebraMap k K)))) ≤
      ((HomogeneousIdeal.irrelevant (grading f)).map (baseChangeGradedHom K f)).toIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [← baseChangeGradedHom_var K f i]
    exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _
      (Nat.pos_of_ne_zero (weights_ne_zero _ i)) (var_mem f i))
  exact h2 h1

/-- The base change morphism `projectiveModel (f ⊗ K) ⟶ projectiveModel f`. -/
noncomputable def baseChangeMap (f : k[X]) :
    projectiveModel (f.map (algebraMap k K)) ⟶ projectiveModel f :=
  Proj.map (baseChangeGradedHom K f) (irrelevant_le_map K f)

/-! ### Charts -/

/-- `k → A[t⁻¹]₀`. -/
noncomputable def awayStructureMap (f : k[X]) (t : HomogeneousCoordRing f) :
    k →+* HomogeneousLocalization.Away (grading f) t :=
  (HomogeneousLocalization.fromZeroRingHom (grading f) (Submonoid.powers t)).comp
    (algebraMap k (grading f 0))

theorem basicOpen_ι_toSpecField_of_mem (f : k[X]) {t : HomogeneousCoordRing f}
    (ht : t ∈ grading f 1) :
    (Proj.basicOpen (grading f) t).ι ≫ toSpecField f =
      (Proj.basicOpenIsoSpec (grading f) t ht Nat.one_pos).hom ≫
        Spec.map (CommRingCat.ofHom (awayStructureMap f t)) := by
  have e : (Proj.basicOpen (grading f) t).ι =
      (Proj.basicOpenIsoSpec (grading f) t ht Nat.one_pos).hom ≫
        Proj.awayι (grading f) t ht Nat.one_pos := by
    rw [Proj.awayι, Iso.hom_inv_id_assoc]
  rw [e, toSpecField, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rfl

/-- The map `k[x, y]/(y^2 - p(x)) → K[x, y]/(y^2 - p(x))`. -/
noncomputable def hypMap (p : k[X]) :
    HyperellipticCoordRing p →+* HyperellipticCoordRing (p.map (algebraMap k K)) :=
  AdjoinRoot.lift ((algebraMap K[X] (HyperellipticCoordRing (p.map (algebraMap k K)))).comp
    (Polynomial.mapRingHom (algebraMap k K))) (AdjoinRoot.root _) (by
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, RingHom.comp_apply, coe_mapRingHom,
        AdjoinRoot.algebraMap_eq, root_sq_eq_of, sub_self])

theorem hypMap_of (p q : k[X]) :
    hypMap K p (AdjoinRoot.of _ q) = AdjoinRoot.of _ (q.map (algebraMap k K)) := by
  rw [hypMap, AdjoinRoot.lift_of, RingHom.comp_apply, coe_mapRingHom, AdjoinRoot.algebraMap_eq]

theorem hypMap_root (p : k[X]) :
    hypMap K p (AdjoinRoot.root _) = AdjoinRoot.root _ := by
  rw [hypMap, AdjoinRoot.lift_root]

theorem algebraMap_hyp_eq (q : k[X]) (a : k) :
    algebraMap k (HyperellipticCoordRing q) a = AdjoinRoot.of _ (C a) := by
  rw [IsScalarTower.algebraMap_apply k k[X] (HyperellipticCoordRing q), Polynomial.algebraMap_eq,
    AdjoinRoot.algebraMap_eq]

theorem hypMap_algebraMap_X (p : k[X]) :
    hypMap K p (algebraMap k[X] _ Polynomial.X) = algebraMap K[X] _ Polynomial.X := by
  rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.algebraMap_eq, hypMap_of, Polynomial.map_X]

theorem hypMap_algebraMap (p : k[X]) (r : k) :
    hypMap K p (algebraMap k _ r) = algebraMap K _ (algebraMap k K r) := by
  rw [algebraMap_hyp_eq, algebraMap_hyp_eq, hypMap_of, Polynomial.map_C]

theorem eval₂_comp_algebraMap {T : Type*} [CommRing T] (p : k[X])
    (χ : HyperellipticCoordRing p →+* T) :
    p.eval₂ (χ.comp (algebraMap k _)) (χ (algebraMap k[X] _ Polynomial.X)) =
      χ (AdjoinRoot.root _) ^ 2 := by
  rw [← Polynomial.hom_eval₂, ← aeval_def, aeval_algebraMap_X, ← map_pow, root_sq_eq_algebraMap]

section Desc

variable {T : Type*} [CommRing T]

/-- The map out of `K[x, y]/(y^2 - p(x))` given by compatible maps out of `k[x, y]/(y^2 - p(x))`
and `K`. -/
noncomputable def hypDesc (p : k[X]) (χ : HyperellipticCoordRing p →+* T) (ψ : K →+* T)
    (hχψ : χ.comp (algebraMap k _) = ψ.comp (algebraMap k K)) :
    HyperellipticCoordRing (p.map (algebraMap k K)) →+* T :=
  AdjoinRoot.lift (eval₂RingHom ψ (χ (algebraMap k[X] _ Polynomial.X))) (χ (AdjoinRoot.root _))
    (by
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, coe_eval₂RingHom, eval₂_map, ← hχψ,
        eval₂_comp_algebraMap, sub_self])

variable (p : k[X]) (χ : HyperellipticCoordRing p →+* T) (ψ : K →+* T)
  (hχψ : χ.comp (algebraMap k _) = ψ.comp (algebraMap k K))

theorem hypDesc_of (q : K[X]) :
    hypDesc K p χ ψ hχψ (AdjoinRoot.of _ q) = q.eval₂ ψ (χ (algebraMap k[X] _ Polynomial.X)) := by
  rw [hypDesc, AdjoinRoot.lift_of, coe_eval₂RingHom]

theorem hypDesc_root : hypDesc K p χ ψ hχψ (AdjoinRoot.root _) = χ (AdjoinRoot.root _) := by
  rw [hypDesc, AdjoinRoot.lift_root]

theorem hypDesc_comp_hypMap : (hypDesc K p χ ψ hχψ).comp (hypMap K p) = χ := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply]
      rw [hypMap_of, Polynomial.map_C, hypDesc_of, eval₂_C, ← algebraMap_hyp_eq]
      exact (RingHom.congr_fun hχψ a).symm
    · simp only [RingHom.comp_apply]
      rw [hypMap_of, Polynomial.map_X, hypDesc_of, eval₂_X, AdjoinRoot.algebraMap_eq]
  · simp only [RingHom.comp_apply]
    rw [hypMap_root, hypDesc_root]

theorem hypDesc_comp_algebraMap : (hypDesc K p χ ψ hχψ).comp (algebraMap K _) = ψ :=
  RingHom.ext fun b => by
    rw [RingHom.comp_apply, algebraMap_hyp_eq, hypDesc_of, eval₂_C]

theorem hypDesc_unique (m : HyperellipticCoordRing (p.map (algebraMap k K)) →+* T)
    (h1 : m.comp (hypMap K p) = χ) (h2 : m.comp (algebraMap K _) = ψ) :
    m = hypDesc K p χ ψ hχψ := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro b
      simp only [RingHom.comp_apply]
      rw [hypDesc_of, eval₂_C, ← algebraMap_hyp_eq]
      exact RingHom.congr_fun h2 b
    · simp only [RingHom.comp_apply]
      rw [hypDesc_of, eval₂_X, ← h1, RingHom.comp_apply, hypMap_algebraMap_X,
        AdjoinRoot.algebraMap_eq]
  · rw [hypDesc_root, ← h1, RingHom.comp_apply, hypMap_root]

end Desc

/-- **The affine hyperelliptic curve commutes with base change**: the square of rings
`k → k[x, y]/(y^2 - p(x))`, `K → K[x, y]/(y^2 - p(x))` is a pushout. -/
theorem isPushout_hyperelliptic (p : k[X]) :
    IsPushout (CommRingCat.ofHom (algebraMap k (HyperellipticCoordRing p)))
      (CommRingCat.ofHom (algebraMap k K)) (CommRingCat.ofHom (hypMap K p))
      (CommRingCat.ofHom (algebraMap K (HyperellipticCoordRing (p.map (algebraMap k K))))) := by
  have hw : CommRingCat.ofHom (algebraMap k (HyperellipticCoordRing p)) ≫
      CommRingCat.ofHom (hypMap K p) = CommRingCat.ofHom (algebraMap k K) ≫
      CommRingCat.ofHom (algebraMap K (HyperellipticCoordRing (p.map (algebraMap k K)))) :=
    CommRingCat.hom_ext (RingHom.ext fun r => hypMap_algebraMap K p r)
  refine IsPushout.of_isColimit' ⟨hw⟩ (PushoutCocone.IsColimit.mk hw
    (fun s => CommRingCat.ofHom (hypDesc K p s.inl.hom s.inr.hom
      (congrArg CommRingCat.Hom.hom s.condition)))
    (fun s => CommRingCat.hom_ext (hypDesc_comp_hypMap K p s.inl.hom s.inr.hom
      (congrArg CommRingCat.Hom.hom s.condition)))
    (fun s => CommRingCat.hom_ext (hypDesc_comp_algebraMap K p s.inl.hom s.inr.hom
      (congrArg CommRingCat.Hom.hom s.condition)))
    (fun s m h1 h2 => CommRingCat.hom_ext (hypDesc_unique K p s.inl.hom s.inr.hom
      (congrArg CommRingCat.Hom.hom s.condition) m.hom (congrArg CommRingCat.Hom.hom h1)
      (congrArg CommRingCat.Hom.hom h2))))

variable {f : k[X]} {o c : Fin 3} {p : k[X]}

/-- The chart data of `f` give chart data of `f ⊗ K`. -/
theorem chartData_map (h : ChartData f o c p) :
    ChartData (f.map (algebraMap k K)) o c (p.map (algebraMap k K)) where
  ne := h.ne
  ne_two := h.ne_two
  ne_two' := h.ne_two'
  cover := h.cover
  weight_o := by rw [genus_map]; exact h.weight_o
  weight_c := by rw [genus_map]; exact h.weight_c
  ideal_eq := by
    rw [← map_coordIdeal, h.ideal_eq, Ideal.map_span, Set.image_singleton, equation_map,
      genus_map]
  natDegree_le := by rw [natDegree_map, genus_map]; exact h.natDegree_le

/-- `K[x, y]/(y^2 - p(x)) ≃ (S_{f ⊗ K})[θ(X_c)⁻¹]₀`. -/
@[expose]
noncomputable def chartBaseChangeEquiv (h : ChartData f o c p) :
    HyperellipticCoordRing (p.map (algebraMap k K)) ≃+*
      HomogeneousLocalization.Away (grading (f.map (algebraMap k K)))
        (baseChangeGradedHom K f (var f c)) :=
  (chartEquiv (chartData_map K h)).symm.trans
    (awayCongr _ (baseChangeGradedHom_var K f c).symm)

theorem chartBaseChangeEquiv_apply (h : ChartData f o c p)
    (x : HyperellipticCoordRing (p.map (algebraMap k K))) :
    chartBaseChangeEquiv K h x =
      awayCongr _ (baseChangeGradedHom_var K f c).symm (affineToChart (chartData_map K h) x) :=
  rfl

theorem chartBaseChangeEquiv_hypMap (h : ChartData f o c p) :
    (chartBaseChangeEquiv K h).toRingHom.comp (hypMap K p) =
      (HomogeneousLocalization.Away.map (baseChangeGradedHom K f) (var f c)).comp
        (affineToChart h) := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        chartBaseChangeEquiv_apply]
      rw [hypMap_of, Polynomial.map_C, ← algebraMap_hyp_eq, ← algebraMap_hyp_eq,
        affineToChart_algebraMap, affineToChart_algebraMap, chartStructureMap, chartStructureMap,
        RingHom.comp_apply, RingHom.comp_apply, awayCongr_fromZeroRingHom,
        awayMap_fromZeroRingHom]
      congr 1
      exact Subtype.ext (baseChangeRingHom_algebraMap K f r).symm
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        chartBaseChangeEquiv_apply]
      rw [hypMap_of, Polynomial.map_X, ← AdjoinRoot.algebraMap_eq, ← AdjoinRoot.algebraMap_eq,
        affineToChart_X, affineToChart_X, chartX, chartX, awayCongr_mk,
        HomogeneousLocalization.Away.map_mk]
      exact away_mk_congr _ _ rfl (baseChangeGradedHom_var K f o).symm _ _
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      chartBaseChangeEquiv_apply]
    rw [hypMap_root, affineToChart_root, affineToChart_root, chartY, chartY, awayCongr_mk,
      HomogeneousLocalization.Away.map_mk]
    exact away_mk_congr _ _ (by rw [genus_map]) (baseChangeGradedHom_var K f 2).symm _ _

/-- On the chart `D₊(X_c)` the base change square of rings is a pushout. -/
theorem isPushout_chart (h : ChartData f o c p) :
    IsPushout (CommRingCat.ofHom (awayStructureMap f (var f c)))
      (CommRingCat.ofHom (algebraMap k K))
      (CommRingCat.ofHom (HomogeneousLocalization.Away.map (baseChangeGradedHom K f) (var f c)))
      (CommRingCat.ofHom (awayStructureMap (f.map (algebraMap k K))
        (baseChangeGradedHom K f (var f c)))) := by
  refine (isPushout_hyperelliptic K p).of_iso (Iso.refl _) (chartEquiv h).symm.toCommRingCatIso
    (Iso.refl _) (chartBaseChangeEquiv K h).toCommRingCatIso ?_ ?_ ?_ ?_
  · exact CommRingCat.hom_ext (RingHom.ext fun r => affineToChart_algebraMap h r)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · exact CommRingCat.hom_ext (RingHom.ext fun x =>
      RingHom.congr_fun (chartBaseChangeEquiv_hypMap K h) x)
  · exact CommRingCat.hom_ext (RingHom.ext fun b =>
      (congrArg (awayCongr (grading (f.map (algebraMap k K)))
        (baseChangeGradedHom_var K f c).symm)
          (affineToChart_algebraMap (chartData_map K h) b)).trans
        (awayCongr_fromZeroRingHom (grading (f.map (algebraMap k K)))
          (baseChangeGradedHom_var K f c).symm (algebraMap K _ b)))

/-- On the chart `D₊(X_c)` the base change square of schemes is a pullback. -/
theorem isPullback_chart (h : ChartData f o c p) :
    IsPullback (baseChangeMap K f ∣_ Proj.basicOpen (grading f) (var f c))
      ((baseChangeMap K f ⁻¹ᵁ Proj.basicOpen (grading f) (var f c)).ι ≫
        toSpecField (f.map (algebraMap k K)))
      ((Proj.basicOpen (grading f) (var f c)).ι ≫ toSpecField f)
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  have hs := var_mem_one f h.weight_c
  have hs' : baseChangeGradedHom K f (var f c) ∈ grading (f.map (algebraMap k K)) 1 :=
    (baseChangeGradedHom K f).map_mem hs
  have R := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_chart K h)
  have hpre : Proj.basicOpen (grading (f.map (algebraMap k K))) (baseChangeGradedHom K f (var f c))
      = baseChangeMap K f ⁻¹ᵁ Proj.basicOpen (grading f) (var f c) :=
    (Proj.map_preimage_basicOpen (baseChangeGradedHom K f) (irrelevant_le_map K f) (var f c)).symm
  refine R.of_iso
    ((Proj.basicOpenIsoSpec (grading (f.map (algebraMap k K))) _ hs' Nat.one_pos).symm ≪≫
      Scheme.isoOfEq _ hpre)
    (Proj.basicOpenIsoSpec (grading f) (var f c) hs Nat.one_pos).symm (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · rw [Iso.trans_hom, Iso.symm_hom, Iso.symm_hom,
      ← cancel_mono (Proj.basicOpen (grading f) (var f c)).ι]
    simp only [Category.assoc]
    rw [morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]
    have := Proj.awayι_comp_map (baseChangeGradedHom K f) (irrelevant_le_map K f) Nat.one_pos
      (var f c) hs
    rw [Proj.awayι, Proj.awayι, Category.assoc] at this
    exact this.symm
  · rw [Iso.refl_hom, Category.comp_id, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Scheme.isoOfEq_hom_ι_assoc, Iso.eq_inv_comp]
    exact (basicOpen_ι_toSpecField_of_mem (f.map (algebraMap k K)) hs').symm
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.eq_inv_comp]
    exact (basicOpen_ι_toSpecField_of_mem f hs).symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-! ### The base change theorem -/

variable (f) in
/-- **The hyperelliptic model commutes with base change**: for a field extension `K/k`, the
square formed by `baseChangeMap K f : projectiveModel (f ⊗ K) ⟶ projectiveModel f`, the
structure morphisms and `Spec K ⟶ Spec k` is a pullback square. -/
theorem isPullback_baseChangeMap :
    IsPullback (baseChangeMap K f) (toSpecField (f.map (algebraMap k K))) (toSpecField f)
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  refine isPullback_of_cover _ _ _ _
    ![Proj.basicOpen (grading f) (var f 1), Proj.basicOpen (grading f) (var f 0)] ?_ ?_
  · refine eq_top_iff.mpr fun x _ => ?_
    have hx : x ∈ Proj.basicOpen (grading f) (var f 1) ⊔ Proj.basicOpen (grading f) (var f 0) :=
      by rw [iSup_chart_eq_top f]; trivial
    rw [TopologicalSpace.Opens.mem_sup] at hx
    rw [TopologicalSpace.Opens.mem_iSup]
    rcases hx with hx | hx
    · exact ⟨0, hx⟩
    · exact ⟨1, hx⟩
  · intro i
    fin_cases i
    · exact isPullback_chart K (chartData_finite f)
    · exact isPullback_chart K (chartData_infinite f)

variable (f) in
/-- The base change `projectiveModel f ×_k K` is the model of `f ⊗ K`. -/
noncomputable def baseChangeIso :
    pullback (toSpecField f) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≅
      projectiveModel (f.map (algebraMap k K)) :=
  (isPullback_baseChangeMap K f).isoPullback.symm

variable (f) in
/-- `baseChangeIso` is an isomorphism over `Spec K`. -/
theorem baseChangeIso_hom_toSpecField :
    (baseChangeIso K f).hom ≫ toSpecField (f.map (algebraMap k K)) = pullback.snd _ _ :=
  (isPullback_baseChangeMap K f).isoPullback_inv_snd

variable (f) in
theorem baseChangeIso_hom_baseChangeMap :
    (baseChangeIso K f).hom ≫ baseChangeMap K f = pullback.fst _ _ :=
  (isPullback_baseChangeMap K f).isoPullback_inv_fst

/-! ### Consequences -/

/-- **The model is geometrically integral** for `f` separable of degree `≥ 1`: every base change
of `projectiveModel f → Spec k` to a field is an integral scheme. -/
theorem geometricallyIntegral_toSpecField (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    GeometricallyIntegral (toSpecField f) := by
  rw [geometricallyIntegral_iff]
  intro L _ y Z fst snd hZ
  let : Algebra k L := (Spec.preimage y).hom.toAlgebra
  have hy : Spec.map (CommRingCat.ofHom (algebraMap k L)) = y := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage y).hom) = y
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hP := isPullback_baseChangeMap L f
  rw [hy] at hP
  have := isIntegral_projectiveModel (f := f.map (algebraMap k L)) hf.map
    (by rw [natDegree_map]; exact hdeg)
  exact AlgebraicGeometry.IsIntegral.of_isIso (hP.isoIsPullback _ _ hZ).hom

/-- **The base-changed model is a smooth proper integral curve of genus `⌊(d - 1)/2⌋`**: for
`f` separable of degree `d ≥ 1` over `k` with `2 ≠ 0` and a field extension `K/k` (e.g. an
algebraic closure), `projectiveModel (f ⊗ K) → Spec K` is smooth and proper, the model is
integral of dimension one, and `dim_K H¹(𝒪) = ⌊(d - 1)/2⌋`. -/
theorem baseChange_curve (h2 : (2 : k) ≠ 0) (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    Smooth (toSpecField (f.map (algebraMap k K))) ∧
      IsProper (toSpecField (f.map (algebraMap k K))) ∧
      IsIntegral (projectiveModel (f.map (algebraMap k K))) ∧
      topologicalKrullDim (projectiveModel (f.map (algebraMap k K))) = 1 ∧
      AlgebraicGeometry.genus (toSpecField (f.map (algebraMap k K))) = (f.natDegree - 1) / 2 := by
  have h2' : (2 : K) ≠ 0 := by
    rw [← map_ofNat (algebraMap k K) 2]
    exact (_root_.map_ne_zero _).mpr h2
  have hdeg' : 0 < (f.map (algebraMap k K)).natDegree := by
    rw [natDegree_map]
    exact hdeg
  obtain ⟨h1, h3, h4, h5⟩ := projectiveModel_curve h2' hf.map hdeg'
  refine ⟨h1, h3, h4, h5, ?_⟩
  rw [genus_projectiveModel, natDegree_map]

/-- **The base change `projectiveModel f ×_k K` is a smooth proper integral curve** over `K`
(structure map `pullback.snd`), for `f` separable of degree `≥ 1` and `2 ≠ 0` in `k`. -/
theorem pullback_curve (h2 : (2 : k) ≠ 0) (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    Smooth (pullback.snd (toSpecField f) (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
      IsProper (pullback.snd (toSpecField f) (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
      IsIntegral (pullback (toSpecField f) (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
      topologicalKrullDim
        (pullback (toSpecField f) (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) =
        1 := by
  obtain ⟨h1, h3, h4, h5, -⟩ := baseChange_curve K h2 hf hdeg
  have : IsZariskiLocalAtTarget @Smooth :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth) (Q := RingHom.Smooth)
  have : MorphismProperty.RespectsIso @Smooth :=
    MorphismProperty.IsLocalAtTarget.toRespects Scheme.zariskiPrecoverage
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← baseChangeIso_hom_toSpecField,
      MorphismProperty.cancel_left_of_respectsIso (P := @Smooth)]
    exact h1
  · rw [← baseChangeIso_hom_toSpecField,
      MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)]
    exact h3
  · exact AlgebraicGeometry.IsIntegral.of_isIso (baseChangeIso K f).inv
  · rw [IsHomeomorph.topologicalKrullDim_eq _ (baseChangeIso K f).hom.homeomorph.isHomeomorph]
    exact h5

end Hyperelliptic

end ArithmeticOfJacobiPolynomials
