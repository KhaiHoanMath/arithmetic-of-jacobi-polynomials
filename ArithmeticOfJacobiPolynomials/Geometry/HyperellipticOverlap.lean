/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticGenus

/-!
# The overlap `D₊(XZ)` of the two charts of the hyperelliptic model

Let `k` be a field, `f ∈ k[x]`, `g = genus f` and `N = 2g + 2`. The projective model
`projectiveModel f = Proj S`, `S = k[X, Z, Y]/(Y^2 - Z^N f(X/Z))`
(`ArithmeticOfJacobiPolynomials.Geometry.HyperellipticProjective`), is covered by the charts
`D₊(Z)` and `D₊(X)`,
whose coordinate rings `(S_Z)_0`, `(S_X)_0` are identified by `chartEquiv` with
`A_Z = k[x, y]/(y^2 - f(x))` and `A_X = k[x', w]/(w^2 - x'^N f(1/x'))`. Their intersection is
`D₊(Z) ∩ D₊(X) = D₊(XZ)`, with coordinate ring `(S_{XZ})_0` (`OverlapChartRing f`). We prove:

* `overlapEquiv f : (S_{XZ})_0 ≃+* OverlapRing f`, where `OverlapRing f = k[x, x⁻¹, y]/(y^2 - f)`
  (`ArithmeticOfJacobiPolynomials.Geometry.HyperellipticGenus`). It is obtained by localising
  `chartEquiv` at
  `x = X/Z`: `(S_{XZ})_0 = (S_Z)_0[Z/X]` (`HomogeneousLocalization.Away.isLocalization_mul`) and
  `OverlapRing f = A_Z[1/x]` (`isLocalization_overlapRing`). It is `k`-linear for the
  structure map `k → S_0 → (S_{XZ})_0` (`overlapEquiv_overlapStructureMap`, `overlapAlgEquiv`).
* Compatibility with the restriction maps: under `chartEquiv` and `overlapEquiv`, the maps
  `HomogeneousLocalization.awayMap : (S_Z)_0 → (S_{XZ})_0` and `(S_X)_0 → (S_{XZ})_0`
  (`overlapRestrictFinite`, `overlapRestrictInfinite`) are `cechRestrictFinite f` and
  `cechRestrictInfinite f` (`overlapEquiv_overlapRestrictFinite`,
  `overlapEquiv_overlapRestrictInfinite`).
* Scheme level: `overlapChart f : Spec (OverlapRing f) ⟶ projectiveModel f` is an open immersion
  with image `D₊(Z) ⊓ D₊(X)` (`opensRange_overlapChart`); it factors through the two charts by
  `Spec` of the Čech restriction maps (`SpecMap_cechRestrictFinite_affineChart`,
  `SpecMap_cechRestrictInfinite_affineChartAtInfinity`), and is compatible with the structure
  morphisms to `Spec k` (`overlapChart_toSpecField`). The two-chart cover consists of affine
  opens with union `⊤` and affine intersection (`twoChartCover_isAffine`).

The comparison of the Čech cohomology of this cover with derived-functor cohomology is in
`ArithmeticOfJacobiPolynomials.Geometry.HyperellipticGenusComparison`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace Hyperelliptic

open Polynomial AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial

universe u

/-- Two fractions in a localisation agree if they agree after cross-multiplication. -/
theorem localization_mk_eq_mk {R : Type*} [CommRing R] {M : Submonoid R} {a b : R} {s t : M}
    (h : a * t = b * s) : Localization.mk a s = Localization.mk b t := by
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, congrArg (fun z => ((1 : M) : R) * z) ((mul_comm _ _).trans (h.trans (mul_comm _ _)))⟩

variable {k : Type u} [Field k] (f : k[X])

/-! ### The coordinate ring of `D₊(XZ)` and the restriction maps -/

theorem varXZ_mem : var f 0 * var f 1 ∈ grading f 2 :=
  SetLike.mul_mem_graded (var_mem_one f (weights_zero _)) (var_mem_one f (weights_one _))

/-- The coordinate ring `(S_{XZ})_0` of the overlap `D₊(XZ) = D₊(Z) ∩ D₊(X)`. -/
abbrev OverlapChartRing : Type u :=
  HomogeneousLocalization.Away (grading f) (var f 0 * var f 1)

/-- The restriction `(S_Z)_0 → (S_{XZ})_0`, `a/Z^n ↦ a X^n/(XZ)^n`. -/
@[expose]
noncomputable def overlapRestrictFinite : ChartRing f 1 →+* OverlapChartRing f :=
  HomogeneousLocalization.awayMap (grading f) (var_mem_one f (weights_zero _))
    (mul_comm (var f 0) (var f 1))

/-- The restriction `(S_X)_0 → (S_{XZ})_0`, `a/X^n ↦ a Z^n/(XZ)^n`. -/
@[expose]
noncomputable def overlapRestrictInfinite : ChartRing f 0 →+* OverlapChartRing f :=
  HomogeneousLocalization.awayMap (grading f) (var_mem_one f (weights_one _))
    (rfl : var f 0 * var f 1 = var f 0 * var f 1)

/-- The structure map `k → S_0 → (S_{XZ})_0`. -/
@[expose]
noncomputable def overlapStructureMap : k →+* OverlapChartRing f :=
  (HomogeneousLocalization.fromZeroRingHom (grading f) _).comp (algebraMap k (grading f 0))

theorem overlapRestrictFinite_chartStructureMap (r : k) :
    overlapRestrictFinite f (chartStructureMap f 1 r) = overlapStructureMap f r := by
  have h := (HomogeneousLocalization.awayMapₐ (grading f) (var_mem_one f (weights_zero _))
    (mul_comm (var f 0) (var f 1))).commutes (algebraMap k (grading f 0) r)
  rw [HomogeneousLocalization.awayMapₐ_apply, HomogeneousLocalization.algebraMap_eq,
    HomogeneousLocalization.algebraMap_eq] at h
  exact h

theorem overlapRestrictInfinite_chartStructureMap (r : k) :
    overlapRestrictInfinite f (chartStructureMap f 0 r) = overlapStructureMap f r := by
  have h := (HomogeneousLocalization.awayMapₐ (grading f) (var_mem_one f (weights_one _))
    (rfl : var f 0 * var f 1 = var f 0 * var f 1)).commutes (algebraMap k (grading f 0) r)
  rw [HomogeneousLocalization.awayMapₐ_apply, HomogeneousLocalization.algebraMap_eq,
    HomogeneousLocalization.algebraMap_eq] at h
  exact h

/-! ### `(S_{XZ})_0` is the localisation of `(S_Z)_0` at `x = X/Z` -/

theorem isLocalizationElem_eq_chartX :
    HomogeneousLocalization.Away.isLocalizationElem (var_mem_one f (weights_one _))
      (var_mem_one f (weights_zero _)) = chartX (chartData_finite f) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem, chartX,
    HomogeneousLocalization.Away.val_mk, pow_one]

theorem isLocalization_overlapRestrictFinite :
    @IsLocalization.Away _ _ (chartX (chartData_finite f)) (OverlapChartRing f) _
      (overlapRestrictFinite f).toAlgebra := by
  let _ := (overlapRestrictFinite f).toAlgebra
  rw [← isLocalizationElem_eq_chartX]
  exact HomogeneousLocalization.Away.isLocalization_mul (var_mem_one f (weights_one _))
    (var_mem_one f (weights_zero _)) (mul_comm (var f 0) (var f 1)) one_ne_zero

theorem chartEquiv_chartX_finite :
    chartEquiv (chartData_finite f) (chartX (chartData_finite f)) =
      AdjoinRoot.of (X ^ 2 - C f : k[X][X]) X := by
  change chartToAffine _ _ = _
  rw [chartX, chartToAffine_mk, dehomogenize_var,
    chartValues_o f (chartData_finite f).ne (chartData_finite f).ne_two, AdjoinRoot.algebraMap_eq]

theorem chartEquiv_chartY_finite :
    chartEquiv (chartData_finite f) (chartY (chartData_finite f)) =
      AdjoinRoot.root (X ^ 2 - C f : k[X][X]) := by
  change chartToAffine _ _ = _
  rw [chartY, chartToAffine_mk, dehomogenize_var, chartValues_two f (chartData_finite f).ne_two']

theorem chartEquiv_chartStructureMap {o c : Fin 3} {p : k[X]} (h : ChartData f o c p) (r : k) :
    chartEquiv h (chartStructureMap f c r) = algebraMap k _ r :=
  chartToAffine_chartStructureMap h r

theorem map_powers_chartX :
    (Submonoid.powers (chartX (chartData_finite f))).map
        (chartEquiv (chartData_finite f)).toMonoidHom =
      Submonoid.powers (AdjoinRoot.of (X ^ 2 - C f : k[X][X]) X) := by
  rw [Submonoid.map_powers]
  exact congrArg Submonoid.powers (chartEquiv_chartX_finite f)

/-! ### The identification `(S_{XZ})_0 ≃ k[x, x⁻¹, y]/(y^2 - f)` -/

/-- **The coordinate ring of `D₊(XZ)` is `k[x, x⁻¹, y]/(y^2 - f(x))`**: the localisation of
`chartEquiv : (S_Z)_0 ≃ A_Z` at `x = X/Z`. -/
@[expose]
noncomputable def overlapEquiv : OverlapChartRing f ≃+* OverlapRing f :=
  letI := (overlapRestrictFinite f).toAlgebra
  letI := (cechRestrictFinite f).toRingHom.toAlgebra
  haveI := isLocalization_overlapRestrictFinite f
  haveI := isLocalization_overlapRing f
  IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (chartX (chartData_finite f)))
    (T := Submonoid.powers (AdjoinRoot.of (X ^ 2 - C f : k[X][X]) X)) (S := OverlapChartRing f)
    (Q := OverlapRing f) (h := chartEquiv (chartData_finite f)) (H := map_powers_chartX f)

/-- **Compatibility with the restriction from `D₊(Z)`**: under `chartEquiv` and `overlapEquiv`,
`awayMap : (S_Z)_0 → (S_{XZ})_0` is `cechRestrictFinite f`. -/
theorem overlapEquiv_overlapRestrictFinite (a : ChartRing f 1) :
    overlapEquiv f (overlapRestrictFinite f a) =
      cechRestrictFinite f (chartEquiv (chartData_finite f) a) := by
  let _ := (overlapRestrictFinite f).toAlgebra
  let _ := (cechRestrictFinite f).toRingHom.toAlgebra
  have := isLocalization_overlapRestrictFinite f
  have := isLocalization_overlapRing f
  exact IsLocalization.ringEquivOfRingEquiv_eq
    (M := Submonoid.powers (chartX (chartData_finite f)))
    (T := Submonoid.powers (AdjoinRoot.of (X ^ 2 - C f : k[X][X]) X)) (S := OverlapChartRing f)
    (Q := OverlapRing f) (j := chartEquiv (chartData_finite f)) (H := map_powers_chartX f) (x := a)

theorem overlapEquiv_comp_overlapRestrictFinite :
    (overlapEquiv f).toRingHom.comp (overlapRestrictFinite f) =
      (cechRestrictFinite f).toRingHom.comp (chartEquiv (chartData_finite f)).toRingHom :=
  RingHom.ext (overlapEquiv_overlapRestrictFinite f)

theorem overlapEquiv_overlapStructureMap (r : k) :
    overlapEquiv f (overlapStructureMap f r) = algebraMap k (OverlapRing f) r := by
  rw [← overlapRestrictFinite_chartStructureMap, overlapEquiv_overlapRestrictFinite,
    chartEquiv_chartStructureMap, AlgHom.commutes]

/-- `overlapEquiv` as an isomorphism of `k`-algebras, `(S_{XZ})_0` being a `k`-algebra through
`overlapStructureMap` (`k → S_0 → (S_{XZ})_0`). -/
@[expose]
noncomputable def overlapAlgEquiv :
    @AlgEquiv k (OverlapChartRing f) (OverlapRing f) _ _ _ (overlapStructureMap f).toAlgebra _ :=
  letI := (overlapStructureMap f).toAlgebra
  AlgEquiv.ofRingEquiv (f := overlapEquiv f) (overlapEquiv_overlapStructureMap f)

/-! ### Compatibility with the restriction from `D₊(X)` -/

/-- An element of `(S_{XZ})_0` is determined by its product with the restriction of an element
of `(S_Z)_0` that becomes a unit. -/
theorem overlapEquiv_eq_of_mul_eq {u : OverlapChartRing f} {v w : ChartRing f 1}
    {t : OverlapRing f} (huv : u * overlapRestrictFinite f v = overlapRestrictFinite f w)
    (hv : IsUnit (cechRestrictFinite f (chartEquiv (chartData_finite f) v)))
    (ht : t * cechRestrictFinite f (chartEquiv (chartData_finite f) v) =
      cechRestrictFinite f (chartEquiv (chartData_finite f) w)) :
    overlapEquiv f u = t := by
  have h1 : overlapEquiv f (u * overlapRestrictFinite f v) =
      overlapEquiv f (overlapRestrictFinite f w) := by rw [huv]
  rw [map_mul, overlapEquiv_overlapRestrictFinite, overlapEquiv_overlapRestrictFinite] at h1
  exact hv.mul_left_inj.mp (h1.trans ht.symm)

/-- `(Z/X)|_{XZ} · (X/Z)|_{XZ} = 1`. -/
theorem overlapRestrictInfinite_chartX_mul :
    overlapRestrictInfinite f (chartX (chartData_infinite f)) *
      overlapRestrictFinite f (chartX (chartData_finite f)) = overlapRestrictFinite f 1 := by
  rw [map_one]
  simp only [overlapRestrictInfinite, overlapRestrictFinite, chartX,
    HomogeneousLocalization.awayMap_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one, Localization.mk_mul,
    ← Localization.mk_one]
  refine localization_mk_eq_mk ?_
  push_cast
  ring

/-- `(Y/X^{g+1})|_{XZ} · ((X/Z)|_{XZ})^{g+1} = (Y/Z^{g+1})|_{XZ}`. -/
theorem overlapRestrictInfinite_chartY_mul :
    overlapRestrictInfinite f (chartY (chartData_infinite f)) *
      overlapRestrictFinite f (chartX (chartData_finite f) ^ (genus f + 1)) =
      overlapRestrictFinite f (chartY (chartData_finite f)) := by
  simp only [overlapRestrictInfinite, overlapRestrictFinite, chartX, chartY, map_pow,
    HomogeneousLocalization.awayMap_mk]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
    HomogeneousLocalization.Away.val_mk, Localization.mk_pow, Localization.mk_mul]
  refine localization_mk_eq_mk ?_
  push_cast
  ring

theorem overlapEquiv_overlapRestrictInfinite_chartX :
    overlapEquiv f (overlapRestrictInfinite f (chartX (chartData_infinite f))) =
      cechRestrictInfinite f (AdjoinRoot.of _ X) := by
  rw [cechRestrictInfinite_of]
  refine overlapEquiv_eq_of_mul_eq f (overlapRestrictInfinite_chartX_mul f) ?_ ?_
  · rw [chartEquiv_chartX_finite, cechRestrictFinite_of, toLaurent_X]
    exact (LaurentPolynomial.isUnit_T 1).map _
  · rw [chartEquiv_chartX_finite, cechRestrictFinite_of, map_one, map_one, toLaurent_X,
      LaurentPolynomial.invert_T, ← map_mul, ← LaurentPolynomial.T_add, neg_add_cancel,
      LaurentPolynomial.T_zero, map_one]

theorem overlapEquiv_overlapRestrictInfinite_chartY :
    overlapEquiv f (overlapRestrictInfinite f (chartY (chartData_infinite f))) =
      cechRestrictInfinite f (AdjoinRoot.root _) := by
  refine overlapEquiv_eq_of_mul_eq f (overlapRestrictInfinite_chartY_mul f) ?_ ?_
  · rw [map_pow, chartEquiv_chartX_finite, cechRestrictFinite_X_pow]
    exact (LaurentPolynomial.isUnit_T _).map _
  · rw [map_pow, chartEquiv_chartX_finite, cechRestrictFinite_X_pow, chartEquiv_chartY_finite,
      cechRestrictFinite_root, cechRestrictInfinite, AdjoinRoot.liftAlgHom_root, mul_right_comm,
      ← map_mul, ← LaurentPolynomial.T_add,
      show -((genus f : ℤ) + 1) + ((genus f + 1 : ℕ) : ℤ) = 0 by omega,
      LaurentPolynomial.T_zero, map_one, one_mul]

theorem overlapEquiv_comp_affineToChart_infinite :
    ((overlapEquiv f).toRingHom.comp (overlapRestrictInfinite f)).comp
      (affineToChart (chartData_infinite f)) = (cechRestrictInfinite f).toRingHom := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      change overlapEquiv f (overlapRestrictInfinite f (affineToChart (chartData_infinite f)
        (AdjoinRoot.of _ (C r)))) = cechRestrictInfinite f (AdjoinRoot.of _ (C r))
      rw [← algebraMap_hyperellipticCoordRing, affineToChart_algebraMap, AlgHom.commutes,
        overlapRestrictInfinite_chartStructureMap, overlapEquiv_overlapStructureMap]
    · change overlapEquiv f (overlapRestrictInfinite f (affineToChart (chartData_infinite f)
        (AdjoinRoot.of _ X))) = cechRestrictInfinite f (AdjoinRoot.of _ X)
      have hX : affineToChart (chartData_infinite f) (AdjoinRoot.of _ X) =
          chartX (chartData_infinite f) := affineToChart_X _
      rw [hX]
      exact overlapEquiv_overlapRestrictInfinite_chartX f
  · change overlapEquiv f (overlapRestrictInfinite f (affineToChart (chartData_infinite f)
      (AdjoinRoot.root _))) = cechRestrictInfinite f (AdjoinRoot.root _)
    rw [affineToChart_root]
    exact overlapEquiv_overlapRestrictInfinite_chartY f

/-- **Compatibility with the restriction from `D₊(X)`**: under `chartEquiv` and `overlapEquiv`,
`awayMap : (S_X)_0 → (S_{XZ})_0` is `cechRestrictInfinite f`. -/
theorem overlapEquiv_overlapRestrictInfinite (a : ChartRing f 0) :
    overlapEquiv f (overlapRestrictInfinite f a) =
      cechRestrictInfinite f (chartEquiv (chartData_infinite f) a) := by
  have h := congrArg (fun φ => φ (chartEquiv (chartData_infinite f) a))
    (overlapEquiv_comp_affineToChart_infinite f)
  have ha : affineToChart (chartData_infinite f) (chartEquiv (chartData_infinite f) a) = a :=
    congrArg (fun φ => φ a) (affineToChart_chartToAffine (chartData_infinite f))
  calc overlapEquiv f (overlapRestrictInfinite f a)
      = overlapEquiv f (overlapRestrictInfinite f (affineToChart (chartData_infinite f)
          (chartEquiv (chartData_infinite f) a))) := by rw [ha]
    _ = _ := h

theorem overlapEquiv_comp_overlapRestrictInfinite :
    (overlapEquiv f).toRingHom.comp (overlapRestrictInfinite f) =
      (cechRestrictInfinite f).toRingHom.comp (chartEquiv (chartData_infinite f)).toRingHom :=
  RingHom.ext (overlapEquiv_overlapRestrictInfinite f)

/-! ### The overlap as an open subscheme -/

/-- The open immersion `Spec k[x, x⁻¹, y]/(y^2 - f(x)) → projectiveModel f` of `D₊(XZ)`. -/
@[expose]
noncomputable def overlapChart : Spec (CommRingCat.of (OverlapRing f)) ⟶ projectiveModel f :=
  Spec.map (overlapEquiv f).toCommRingCatIso.hom ≫
    Proj.awayι (grading f) (var f 0 * var f 1) (varXZ_mem f) two_pos

instance : IsOpenImmersion (overlapChart f) := by
  rw [overlapChart]
  infer_instance

theorem awayι_overlap_finite :
    Proj.awayι (grading f) (var f 0 * var f 1) (varXZ_mem f) two_pos =
      Spec.map (CommRingCat.ofHom (overlapRestrictFinite f)) ≫
        Proj.awayι (grading f) (var f 1) (var_mem_one f (weights_one _)) Nat.one_pos :=
  (Proj.SpecMap_awayMap_awayι (grading f) (var_mem_one f (weights_one _)) Nat.one_pos
    (var_mem_one f (weights_zero _)) (mul_comm (var f 0) (var f 1))).symm

theorem awayι_overlap_infinite :
    Proj.awayι (grading f) (var f 0 * var f 1) (varXZ_mem f) two_pos =
      Spec.map (CommRingCat.ofHom (overlapRestrictInfinite f)) ≫
        Proj.awayι (grading f) (var f 0) (var_mem_one f (weights_zero _)) Nat.one_pos :=
  (Proj.SpecMap_awayMap_awayι (grading f) (var_mem_one f (weights_zero _)) Nat.one_pos
    (var_mem_one f (weights_one _)) (rfl : var f 0 * var f 1 = var f 0 * var f 1)).symm

/-- **The overlap chart factors through the chart `D₊(Z)`** by `Spec` of
`cechRestrictFinite f : A_Z → k[x, x⁻¹, y]/(y^2 - f)`. -/
theorem SpecMap_cechRestrictFinite_affineChart :
    Spec.map (CommRingCat.ofHom (cechRestrictFinite f).toRingHom) ≫ affineChart f =
      overlapChart f := by
  rw [overlapChart, awayι_overlap_finite, affineChart, chart, ← Category.assoc,
    ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  congr 1
  ext a
  exact (overlapEquiv_overlapRestrictFinite f a).symm

/-- **The overlap chart factors through the chart `D₊(X)`** by `Spec` of
`cechRestrictInfinite f : A_X → k[x, x⁻¹, y]/(y^2 - f)`. -/
theorem SpecMap_cechRestrictInfinite_affineChartAtInfinity :
    Spec.map (CommRingCat.ofHom (cechRestrictInfinite f).toRingHom) ≫ affineChartAtInfinity f =
      overlapChart f := by
  rw [overlapChart, awayι_overlap_infinite, affineChartAtInfinity, chart, ← Category.assoc,
    ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  congr 1
  ext a
  exact (overlapEquiv_overlapRestrictInfinite f a).symm

/-- The overlap chart is a morphism over `Spec k`. -/
theorem overlapChart_toSpecField :
    overlapChart f ≫ toSpecField f =
      Spec.map (CommRingCat.ofHom (algebraMap k (OverlapRing f))) := by
  rw [← SpecMap_cechRestrictFinite_affineChart, Category.assoc, affineChart, chart_toSpecField,
    ← Spec.map_comp]
  congr 1
  ext r
  exact (cechRestrictFinite f).commutes r

instance : IsOpenImmersion (affineChart f) :=
  inferInstanceAs (IsOpenImmersion (chart (chartData_finite f)))

instance : IsOpenImmersion (affineChartAtInfinity f) :=
  inferInstanceAs (IsOpenImmersion (chart (chartData_infinite f)))

/-- The image of the chart `D₊(Z)` is `D₊(Z)`. -/
theorem opensRange_affineChart :
    (affineChart f).opensRange = Proj.basicOpen (grading f) (var f 1) := by
  refine (Scheme.Hom.opensRange_comp_of_isIso
    (Spec.map (chartEquiv (chartData_finite f)).toCommRingCatIso.hom)
    (Proj.awayι (grading f) (var f 1) (var_mem_one f (weights_one _)) Nat.one_pos)).trans ?_
  rw [Proj.opensRange_awayι]

/-- The image of the chart `D₊(X)` is `D₊(X)`. -/
theorem opensRange_affineChartAtInfinity :
    (affineChartAtInfinity f).opensRange = Proj.basicOpen (grading f) (var f 0) := by
  refine (Scheme.Hom.opensRange_comp_of_isIso
    (Spec.map (chartEquiv (chartData_infinite f)).toCommRingCatIso.hom)
    (Proj.awayι (grading f) (var f 0) (var_mem_one f (weights_zero _)) Nat.one_pos)).trans ?_
  rw [Proj.opensRange_awayι]

/-- **The image of the overlap chart is `D₊(Z) ∩ D₊(X)`.** -/
theorem opensRange_overlapChart :
    (overlapChart f).opensRange =
      Proj.basicOpen (grading f) (var f 1) ⊓ Proj.basicOpen (grading f) (var f 0) := by
  refine (Scheme.Hom.opensRange_comp_of_isIso
    (Spec.map (overlapEquiv f).toCommRingCatIso.hom)
    (Proj.awayι (grading f) (var f 0 * var f 1) (varXZ_mem f) two_pos)).trans ?_
  rw [Proj.opensRange_awayι, Proj.basicOpen_mul]
  exact inf_comm _ _

theorem opensRange_overlapChart_eq_inf :
    (overlapChart f).opensRange =
      (affineChart f).opensRange ⊓ (affineChartAtInfinity f).opensRange := by
  rw [opensRange_overlapChart, opensRange_affineChart, opensRange_affineChartAtInfinity]

/-- **The two-chart cover**: `U = D₊(Z)` and `V = D₊(X)` are affine opens covering the model,
with affine intersection `U ⊓ V` (the image of `overlapChart f`). These are the hypotheses of a
two-affine Čech computation of the cohomology of quasi-coherent sheaves. -/
theorem twoChartCover_isAffine :
    IsAffineOpen (Proj.basicOpen (grading f) (var f 1)) ∧
      IsAffineOpen (Proj.basicOpen (grading f) (var f 0)) ∧
      Proj.basicOpen (grading f) (var f 1) ⊔ Proj.basicOpen (grading f) (var f 0) = ⊤ ∧
      IsAffineOpen (Proj.basicOpen (grading f) (var f 1) ⊓ Proj.basicOpen (grading f) (var f 0))
    := by
  refine ⟨?_, ?_, iSup_chart_eq_top f, ?_⟩
  · exact Proj.isAffineOpen_basicOpen (grading f) (var f 1) (var_mem_one f (weights_one _))
      Nat.one_pos
  · exact Proj.isAffineOpen_basicOpen (grading f) (var f 0) (var_mem_one f (weights_zero _))
      Nat.one_pos
  · rw [← opensRange_overlapChart]
    exact isAffineOpen_opensRange _

end Hyperelliptic

end ArithmeticOfJacobiPolynomials
