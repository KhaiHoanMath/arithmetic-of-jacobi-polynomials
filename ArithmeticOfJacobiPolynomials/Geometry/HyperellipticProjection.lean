/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticSquareMapDegree
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The hyperelliptic double cover `x : X → ℙ¹`

Let `k` be a field and `f ∈ k[x]`. This file constructs the projection
`toProjectiveLine f : projectiveModel f ⟶ projectiveLine k`, `(x, y) ↦ x`, from the projective
model of `y^2 = f(x)` (`ArithmeticOfJacobiPolynomials.Hyperelliptic.projectiveModel`, weighted
`Proj k[X, Z, Y]/(Y^2 - Z^N f(X/Z))`) to the projective line, and shows that it is a finite
morphism, which over each of the two standard charts of `ℙ¹` is `Spec` of a free algebra of
rank two (used in the subsection "Hyperelliptic Jacobians" of the manuscript, where the curve is
viewed as a double cover of the projective line).

## The projective line

`projectiveLine k = Proj k[U₀, U₁]` for the standard grading by total degree
(`MvPolynomial.homogeneousSubmodule`). Its charts `D₊(U_c)` are identified with the affine line:
the coordinate ring `(k[U₀, U₁]_{U_c})_0` is `k[x]`, `x = U_o/U_c` (`lineEquiv`, by
dehomogenization `U_c ↦ 1`, `U_o ↦ x`), giving the open immersions `affineLineChart k`
(`x = U₀/U₁`) and `affineLineChartAtInfinity k` (`x' = U₁/U₀`); they cover `ℙ¹`
(`mem_lineChart_or_mem_lineChart`, `lineCover`).

## The projection

The `k`-algebra map `k[U₀, U₁] → k[X, Z, Y]/(Y^2 - Z^N f(X/Z))`, `U₀ ↦ X`, `U₁ ↦ Z`
(`projectionHom`) preserves degrees. Mathlib's `Proj.map` does not apply (the irrelevant ideal of
the target is only contained in the *radical* of `(X, Z)`, since `Y ∉ (X, Z)`), so the morphism
is glued from the chart maps `(k[U]_{U_c})_0 → (S_{X_c})_0` (`chartProjectionMap`), which agree
on the overlaps (`projection_glue_condition`). Results:

* `toProjectiveLine_lineToSpecField`: it is a morphism over `Spec k`;
* `affineChart_comp_toProjectiveLine`: **on the finite charts it is `Spec` of
  `k[x] → k[x, y]/(y^2 - f(x))`**, and `affineChartAtInfinity_comp_toProjectiveLine`: on the
  charts at infinity it is `Spec` of `k[x'] → k[x', w]/(w^2 - x'^N f(1/x'))`;
* `preimage_basicOpen_toProjectiveLine`: the preimage of `D₊(U₁)` (resp. `D₊(U₀)`) is `D₊(Z)`
  (resp. `D₊(X)`), so the two squares above are pullback squares
  (`isPullback_affineChart_toProjectiveLine`, `isPullback_affineChartAtInfinity_toProjectiveLine`);
* `free_and_finrank_hyperellipticCoordRing`: `k[x, y]/(y^2 - p(x))` is free of rank two over
  `k[x]` (basis `1, y`); hence (`toProjectiveLine_affineLine_free_rank_two`,
  `toProjectiveLine_affineLineAtInfinity_free_rank_two`) over each standard chart of `ℙ¹` the
  projection is `Spec` of a free algebra of rank two;
* `isFinite_toProjectiveLine`: the projection is a finite morphism.

The branch locus is computed in
`ArithmeticOfJacobiPolynomials.Geometry.HyperellipticProjectionBranch`.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

namespace Hyperelliptic

open Polynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits GradedQuotient

universe u

attribute [local instance] MvPolynomial.weightedGradedAlgebra MvPolynomial.gradedAlgebra

/-! ### The projective line -/

section Line

variable (k : Type u) [Field k]

/-- The standard grading of `k[U₀, U₁]` by total degree. -/
abbrev lineGrading : ℕ → Submodule k (MvPolynomial (Fin 2) k) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) k

/-- **The projective line** `ℙ¹_k = Proj k[U₀, U₁]` (standard grading). -/
noncomputable abbrev projectiveLine : Scheme.{u} := Proj (lineGrading k)

/-- The structure morphism `ℙ¹_k → Spec k`. -/
@[expose]
noncomputable def lineToSpecField : projectiveLine k ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero (lineGrading k) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (lineGrading k 0)))

/-- The coordinate ring `(k[U₀, U₁]_{U_c})_0` of the chart `D₊(U_c)`. -/
abbrev LineRing (c : Fin 2) : Type u :=
  HomogeneousLocalization.Away (lineGrading k) (MvPolynomial.X c : MvPolynomial (Fin 2) k)

variable {k}

theorem lineVar_mem (i : Fin 2) :
    (MvPolynomial.X i : MvPolynomial (Fin 2) k) ∈ lineGrading k 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X k i)

theorem fin2_cover (o c : Fin 2) (h : o ≠ c) (i : Fin 2) : i = o ∨ i = c := by
  revert o c i
  decide

/-- The values of the dehomogenization `U_c ↦ 1`, `U_o ↦ x`. -/
@[expose]
noncomputable def lineValues (c : Fin 2) (i : Fin 2) : k[X] := if i = c then 1 else polyX

theorem lineValues_c (c : Fin 2) : lineValues (k := k) c c = 1 := by simp [lineValues]

theorem lineValues_o {o c : Fin 2} (h : o ≠ c) : lineValues (k := k) c o = polyX := by
  simp [lineValues, h]

/-- The dehomogenization `k[U₀, U₁] → k[x]`, `U_c ↦ 1`, `U_o ↦ x`. -/
@[expose]
noncomputable def lineDehom (c : Fin 2) : MvPolynomial (Fin 2) k →ₐ[k] k[X] :=
  MvPolynomial.aeval (lineValues c)

theorem lineDehom_X (c i : Fin 2) :
    lineDehom (k := k) c (MvPolynomial.X i) = lineValues c i :=
  MvPolynomial.aeval_X _ _

/-- `k[U₀, U₁]_{U_c} → k[x]`, `a/U_c^n ↦ a(U_c = 1, U_o = x)`. -/
@[expose]
noncomputable def lineLift (c : Fin 2) :
    Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k) →+* k[X] :=
  IsLocalization.Away.lift (S := Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k))
    (MvPolynomial.X c)
    (g := ((lineDehom c : _ →ₐ[k] _) : MvPolynomial (Fin 2) k →+* k[X])) (by
      change IsUnit (lineDehom c (MvPolynomial.X c))
      rw [lineDehom_X, lineValues_c]
      exact isUnit_one)

theorem lineLift_algebraMap (c : Fin 2) (s : MvPolynomial (Fin 2) k) :
    lineLift c (algebraMap _ _ s) = lineDehom c s :=
  IsLocalization.Away.lift_eq _ _ s

/-- `(k[U₀, U₁]_{U_c})_0 → k[x]`. -/
@[expose]
noncomputable def lineToAffine (c : Fin 2) : LineRing k c →+* k[X] :=
  (lineLift c).comp
    (algebraMap (LineRing k c) (Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k)))

theorem lineToAffine_mk (c : Fin 2) (n : ℕ) (s : MvPolynomial (Fin 2) k)
    (hs : s ∈ lineGrading k (n • 1)) :
    lineToAffine c (HomogeneousLocalization.Away.mk (lineGrading k) (lineVar_mem c) n s hs) =
      lineDehom c s := by
  have h1 : (HomogeneousLocalization.Away.mk (lineGrading k) (lineVar_mem c) n s hs).val *
      algebraMap _ (Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k))
        ((MvPolynomial.X c : MvPolynomial (Fin 2) k) ^ n) =
      algebraMap _ (Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k)) s := by
    rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk'_apply]
    exact IsLocalization.mk'_spec _ s _
  have h2 := congrArg (lineLift c) h1
  rw [map_mul, lineLift_algebraMap, lineLift_algebraMap, map_pow, lineDehom_X, lineValues_c,
    one_pow, mul_one] at h2
  exact h2

/-- `1/U_c` in `k[U₀, U₁]_{U_c}`. -/
@[expose]
noncomputable def invLineVar (c : Fin 2) :
    Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k) :=
  IsLocalization.mk' _ (1 : MvPolynomial (Fin 2) k) ⟨MvPolynomial.X c, Submonoid.mem_powers _⟩

theorem invLineVar_mul (c : Fin 2) :
    invLineVar (k := k) c *
      algebraMap _ (Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k))
        (MvPolynomial.X c : MvPolynomial (Fin 2) k) = 1 := by
  have := IsLocalization.mk'_spec (Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k))
    (1 : MvPolynomial (Fin 2) k) ⟨MvPolynomial.X c, Submonoid.mem_powers _⟩
  rw [map_one] at this
  exact this

theorem lineLocalization_mk_eq (c : Fin 2) (n : ℕ) (s : MvPolynomial (Fin 2) k)
    (hn : (MvPolynomial.X c : MvPolynomial (Fin 2) k) ^ n ∈
      Submonoid.powers (MvPolynomial.X c : MvPolynomial (Fin 2) k)) :
    Localization.mk s ⟨MvPolynomial.X c ^ n, hn⟩ =
      invLineVar c ^ n *
        algebraMap _ (Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k)) s := by
  rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_mul_mk'_one, mul_comm, invLineVar,
    ← IsLocalization.mk'_pow, one_pow]
  congr 2

theorem val_lineAway_mk (c : Fin 2) (n : ℕ) (s : MvPolynomial (Fin 2) k)
    (hs : s ∈ lineGrading k (n • 1)) :
    algebraMap (LineRing k c) (Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k))
      (HomogeneousLocalization.Away.mk (lineGrading k) (lineVar_mem c) n s hs) =
      invLineVar c ^ n *
        algebraMap _ (Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k)) s := by
  rw [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
    lineLocalization_mk_eq]

/-- `k → (k[U₀, U₁]_{U_c})_0`. -/
@[expose]
noncomputable def lineStructureMap (c : Fin 2) : k →+* LineRing k c :=
  (HomogeneousLocalization.fromZeroRingHom (lineGrading k) _).comp
    (algebraMap k (lineGrading k 0))

theorem val_lineStructureMap (c : Fin 2) (r : k) :
    algebraMap (LineRing k c) (Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k))
      (lineStructureMap c r) =
      algebraMap k (Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k)) r := by
  rw [HomogeneousLocalization.algebraMap_apply]
  change Localization.mk _ 1 = _
  rw [Localization.mk_one_eq_algebraMap, SetLike.GradeZero.coe_algebraMap,
    ← IsScalarTower.algebraMap_apply]

/-- The coordinate `x = U_o/U_c` on the chart `D₊(U_c)`. -/
@[expose]
noncomputable def lineX (o c : Fin 2) : LineRing k c :=
  HomogeneousLocalization.Away.mk (lineGrading k) (lineVar_mem c) 1 (MvPolynomial.X o)
    (by simpa using lineVar_mem o)

/-- `k[x] → (k[U₀, U₁]_{U_c})_0`, `x ↦ U_o/U_c`. -/
@[expose]
noncomputable def affineToLine (o c : Fin 2) : k[X] →+* LineRing k c :=
  eval₂RingHom (lineStructureMap c) (lineX o c)

theorem affineToLine_C (o c : Fin 2) (r : k) :
    affineToLine o c (C r) = lineStructureMap c r := by
  rw [affineToLine, coe_eval₂RingHom, eval₂_C]

theorem affineToLine_X (o c : Fin 2) : affineToLine (k := k) o c polyX = lineX o c := by
  rw [affineToLine, coe_eval₂RingHom, eval₂_X]

theorem lineToAffine_lineStructureMap (c : Fin 2) (r : k) :
    lineToAffine c (lineStructureMap c r) = algebraMap k k[X] r := by
  rw [lineToAffine, RingHom.comp_apply, val_lineStructureMap,
    IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 2) k), lineLift_algebraMap]
  exact (lineDehom c).commutes r

theorem lineToAffine_affineToLine {o c : Fin 2} (h : o ≠ c) :
    (lineToAffine c).comp (affineToLine (k := k) o c) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply, RingHom.id_apply, affineToLine_C, lineToAffine_lineStructureMap,
      Polynomial.algebraMap_eq]
  · rw [RingHom.comp_apply, RingHom.id_apply, affineToLine_X, lineX, lineToAffine_mk,
      lineDehom_X, lineValues_o h]

/-- The values `U_i ↦ U_c^{-1} U_i` in `k[U₀, U₁]_{U_c}`. -/
@[expose]
noncomputable def scaledLineVars (c : Fin 2) (i : Fin 2) :
    Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k) :=
  invLineVar c * algebraMap _ _ (MvPolynomial.X i : MvPolynomial (Fin 2) k)

theorem lineAeval_var (c : Fin 2) (s : MvPolynomial (Fin 2) k) :
    MvPolynomial.aeval (fun i => algebraMap _
      (Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k))
        (MvPolynomial.X i : MvPolynomial (Fin 2) k)) s = algebraMap _ _ s := by
  let φ := IsScalarTower.toAlgHom k (MvPolynomial (Fin 2) k)
    (Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k))
  change MvPolynomial.aeval (φ ∘ MvPolynomial.X) s = φ s
  rw [← MvPolynomial.aeval_unique]

theorem aeval_scaledLineVars (c : Fin 2) {n : ℕ} {s : MvPolynomial (Fin 2) k}
    (hs : s.IsHomogeneous n) :
    MvPolynomial.aeval (scaledLineVars c) s =
      invLineVar c ^ n *
        algebraMap _ (Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k)) s := by
  have h := aeval_pow_weight_mul (1 : Fin 2 → ℕ) hs (invLineVar c)
    (fun i => algebraMap _ (Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k))
      (MvPolynomial.X i : MvPolynomial (Fin 2) k))
  simp only [Pi.one_apply, pow_one] at h
  rw [lineAeval_var] at h
  exact h

theorem affineToLine_lineToAffine {o c : Fin 2} (h : o ≠ c) :
    (affineToLine (k := k) o c).comp (lineToAffine c) = RingHom.id _ := by
  refine RingHom.ext fun u => ?_
  obtain ⟨n, s, hs, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (lineGrading k) (lineVar_mem c) u
  rw [RingHom.comp_apply, lineToAffine_mk, RingHom.id_apply]
  have hs' : s.IsHomogeneous n := by
    have := (MvPolynomial.mem_homogeneousSubmodule _ _).mp hs
    simpa [smul_eq_mul] using this
  refine HomogeneousLocalization.val_injective _ (?_ : algebraMap (LineRing k c)
    (Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k))
      (affineToLine o c (lineDehom c s)) = _)
  refine Eq.trans ?_ (val_lineAway_mk c n _ _).symm
  refine Eq.trans ?_ (aeval_scaledLineVars c hs')
  change ((algebraMap (LineRing k c)
    (Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k))).comp
      ((affineToLine o c).comp (lineDehom c).toRingHom)) s = _
  have key : (algebraMap (LineRing k c)
      (Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k))).comp
        ((affineToLine o c).comp (lineDehom c).toRingHom) =
      (MvPolynomial.aeval (scaledLineVars c)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change algebraMap (LineRing k c)
          (Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k))
          (affineToLine o c (lineDehom c (algebraMap k (MvPolynomial (Fin 2) k) r))) =
        MvPolynomial.aeval (scaledLineVars c) (MvPolynomial.C r)
      rw [AlgHom.commutes, Polynomial.algebraMap_eq, affineToLine_C, val_lineStructureMap,
        MvPolynomial.aeval_C]
    · intro i
      change algebraMap (LineRing k c)
          (Localization.Away (MvPolynomial.X c : MvPolynomial (Fin 2) k))
          (affineToLine o c (lineDehom c (MvPolynomial.X i))) =
        MvPolynomial.aeval (scaledLineVars c) (MvPolynomial.X i)
      rw [MvPolynomial.aeval_X, lineDehom_X]
      rcases fin2_cover o c h i with rfl | rfl
      · rw [lineValues_o h, affineToLine_X, lineX, val_lineAway_mk, scaledLineVars, pow_one]
      · rw [lineValues_c, map_one, map_one]
        exact (invLineVar_mul _).symm
  exact congrArg (fun φ => φ s) key

/-- The coordinate ring of the chart `D₊(U_c)` of `ℙ¹` is `k[x]`, `x = U_o/U_c`. -/
@[expose]
noncomputable def lineEquiv {o c : Fin 2} (h : o ≠ c) : LineRing k c ≃+* k[X] :=
  RingEquiv.ofRingHom (lineToAffine c) (affineToLine o c) (lineToAffine_affineToLine h)
    (affineToLine_lineToAffine h)

/-- The open immersion `𝔸¹ = Spec k[x] → ℙ¹` of the chart `D₊(U_c)`, `x = U_o/U_c`. -/
@[expose]
noncomputable def lineChart {o c : Fin 2} (h : o ≠ c) :
    Spec (CommRingCat.of k[X]) ⟶ projectiveLine k :=
  Spec.map (lineEquiv h).toCommRingCatIso.hom ≫
    Proj.awayι (lineGrading k) (MvPolynomial.X c) (lineVar_mem c) Nat.one_pos

instance {o c : Fin 2} (h : o ≠ c) : IsOpenImmersion (lineChart (k := k) h) := by
  rw [lineChart]
  infer_instance

theorem opensRange_lineChart {o c : Fin 2} (h : o ≠ c) :
    (lineChart (k := k) h).opensRange = Proj.basicOpen (lineGrading k) (MvPolynomial.X c) := by
  change (Spec.map (lineEquiv h).toCommRingCatIso.hom ≫
    Proj.awayι (lineGrading k) (MvPolynomial.X c) (lineVar_mem c) Nat.one_pos).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

variable (k) in
/-- The finite chart `𝔸¹ → ℙ¹`, `x ↦ (x : 1)` (`x = U₀/U₁`). -/
@[expose]
noncomputable def affineLineChart : Spec (CommRingCat.of k[X]) ⟶ projectiveLine k :=
  lineChart (o := 0) (c := 1) (by decide)

variable (k) in
/-- The chart at infinity `𝔸¹ → ℙ¹`, `x' ↦ (1 : x')` (`x' = U₁/U₀`). -/
@[expose]
noncomputable def affineLineChartAtInfinity : Spec (CommRingCat.of k[X]) ⟶ projectiveLine k :=
  lineChart (o := 1) (c := 0) (by decide)

theorem adjoin_range_lineVar :
    Algebra.adjoin (lineGrading k 0)
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k)) = ⊤ := by
  have key : ∀ P : MvPolynomial (Fin 2) k, P ∈ Algebra.adjoin (lineGrading k 0)
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k)) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a =>
      have := Subalgebra.algebraMap_mem (Algebra.adjoin (lineGrading k 0)
        (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k)))
        (⟨MvPolynomial.C a, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
          (MvPolynomial.isHomogeneous_C _ a)⟩ : lineGrading k 0)
      rwa [SetLike.GradeZero.algebraMap_apply] at this
    | add P Q hP hQ => exact Subalgebra.add_mem _ hP hQ
    | mul_X P i hP => exact Subalgebra.mul_mem _ hP (Algebra.subset_adjoin ⟨i, rfl⟩)
  exact eq_top_iff.mpr fun s _ => key s

/-- The two standard charts cover `ℙ¹`. -/
theorem mem_lineChart_or_mem_lineChart (x : projectiveLine k) :
    x ∈ Proj.basicOpen (lineGrading k) (MvPolynomial.X 1) ∨
      x ∈ Proj.basicOpen (lineGrading k) (MvPolynomial.X 0) := by
  have htop := Proj.iSup_basicOpen_eq_top' (lineGrading k)
    (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k) (fun i => ⟨1, lineVar_mem i⟩)
    adjoin_range_lineVar
  have hx : x ∈ ⨆ i, Proj.basicOpen (lineGrading k)
      (MvPolynomial.X i : MvPolynomial (Fin 2) k) := by
    rw [htop]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  fin_cases i
  · exact Or.inr hi
  · exact Or.inl hi

/-- The line chart variables: `U₁` (index `0`) and `U₀` (index `1`). -/
@[expose]
def lineCoverVar : Fin 2 → Fin 2 := ![1, 0]

variable (k) in
open Classical in
/-- The cover of `ℙ¹` by the charts `D₊(U₁)` and `D₊(U₀)`. -/
@[expose]
noncomputable def lineCover : (projectiveLine k).AffineOpenCover where
  I₀ := Fin 2
  X a := CommRingCat.of (LineRing k (lineCoverVar a))
  f a := Proj.awayι (lineGrading k) (MvPolynomial.X (lineCoverVar a)) (lineVar_mem _) Nat.one_pos
  idx x := if x ∈ Proj.basicOpen (lineGrading k) (MvPolynomial.X 1) then 0 else 1
  covers x := by
    change x ∈ (Proj.awayι _ _ _ _).opensRange
    rw [Proj.opensRange_awayι]
    split_ifs with h
    · exact h
    · exact (mem_lineChart_or_mem_lineChart x).resolve_left h

end Line

/-! ### The graded map `k[U₀, U₁] → S_f` -/

variable {k : Type u} [Field k] (f : k[X])

/-- `k[U₀, U₁] → S_f = k[X, Z, Y]/(Y^2 - Z^N f(X/Z))`, `U₀ ↦ X`, `U₁ ↦ Z`. -/
@[expose]
noncomputable def projectionAlgHom : MvPolynomial (Fin 2) k →ₐ[k] HomogeneousCoordRing f :=
  (Ideal.Quotient.mkₐ k (coordIdeal f)).comp
    (MvPolynomial.aeval fun i : Fin 2 => (MvPolynomial.X i.castSucc : MvPolynomial (Fin 3) k))

/-- `projectionAlgHom` as a ring map. -/
@[expose]
noncomputable def projectionHom : MvPolynomial (Fin 2) k →+* HomogeneousCoordRing f :=
  (projectionAlgHom f).toRingHom

theorem projectionAlgHom_X (i : Fin 2) :
    projectionAlgHom f (MvPolynomial.X i) = var f i.castSucc := by
  rw [projectionAlgHom, AlgHom.comp_apply, MvPolynomial.aeval_X]
  rfl

theorem projectionHom_X (i : Fin 2) :
    projectionHom f (MvPolynomial.X i) = var f i.castSucc :=
  projectionAlgHom_X f i

theorem projectionHom_algebraMap (r : k) :
    projectionHom f (algebraMap k _ r) = algebraMap k _ r :=
  (projectionAlgHom f).commutes r

theorem isWeightedHomogeneous_X_castSucc (g : ℕ) (i : Fin 2) :
    (MvPolynomial.X i.castSucc : MvPolynomial (Fin 3) k).IsWeightedHomogeneous (weights g)
      (1 * (1 : Fin 2 → ℕ) i) := by
  have hw : weights g i.castSucc = 1 * (1 : Fin 2 → ℕ) i := by
    fin_cases i <;> rfl
  rw [← hw]
  exact MvPolynomial.isWeightedHomogeneous_X (R := k) (weights g) _

/-- `projectionHom` preserves degrees. -/
theorem projectionHom_mem :
    ∀ (n : ℕ) (a : MvPolynomial (Fin 2) k), a ∈ lineGrading k n →
      projectionHom f a ∈ grading f (1 * n) := by
  intro n a ha
  change Ideal.Quotient.mk (coordIdeal f) (MvPolynomial.aeval
    (fun i : Fin 2 => (MvPolynomial.X i.castSucc : MvPolynomial (Fin 3) k)) a) ∈ grading f (1 * n)
  exact mk_mem_quotientGrading _ _ (isWeightedHomogeneous_aeval (c := 1)
    (w := (1 : Fin 2 → ℕ))
    (v := fun i : Fin 2 => (MvPolynomial.X i.castSucc : MvPolynomial (Fin 3) k))
    (fun i => isWeightedHomogeneous_X_castSucc (genus f) i)
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mp ha))

theorem castSucc_lineCoverVar (a : Fin 2) : (lineCoverVar a).castSucc = coverVar a := by
  fin_cases a <;> rfl

theorem projectionHom_X_lineCoverVar (a : Fin 2) :
    projectionHom f (MvPolynomial.X (lineCoverVar a)) = var f (coverVar a) := by
  rw [projectionHom_X, castSucc_lineCoverVar]

/-! ### The chart maps and the gluing -/

/-- On `D₊(X_c)` (`X_c = Z, X`): `(k[U]_{U_c})_0 → (S_{X_c})_0`, `a/U_c^n ↦ φ(a)/X_c^n`. -/
@[expose]
noncomputable def chartProjectionMap (a : Fin 2) :
    LineRing k (lineCoverVar a) →+* ChartRing f (coverVar a) :=
  scaledAwayMap (c := 1) (projectionHom f) (projectionHom_mem f) (lineVar_mem (lineCoverVar a))
    (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two a)))
    (by rw [projectionHom_X_lineCoverVar, pow_one]) rfl

/-- On the overlaps `D₊(X_{c₁} X_{c₂})`. -/
@[expose]
noncomputable def overlapProjectionMap (a b : Fin 2) :
    HomogeneousLocalization.Away (lineGrading k)
        (MvPolynomial.X (lineCoverVar a) * MvPolynomial.X (lineCoverVar b)) →+*
      HomogeneousLocalization.Away (grading f) (var f (coverVar a) * var f (coverVar b)) :=
  scaledAwayMap (c := 1) (projectionHom f) (projectionHom_mem f)
    (SetLike.mul_mem_graded (lineVar_mem (lineCoverVar a)) (lineVar_mem (lineCoverVar b)))
    (SetLike.mul_mem_graded (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two a)))
      (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two b))))
    (by rw [map_mul, projectionHom_X_lineCoverVar, projectionHom_X_lineCoverVar, pow_one]) rfl

theorem projection_overlap_compat_left (a b : Fin 2) :
    (HomogeneousLocalization.awayMap (grading f)
        (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two b))) rfl).comp
        (chartProjectionMap f a) =
      (overlapProjectionMap f a b).comp
        (HomogeneousLocalization.awayMap (lineGrading k) (lineVar_mem (lineCoverVar b)) rfl) :=
  awayMap_comp_scaledAwayMap _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem projection_overlap_compat_right (a b : Fin 2) :
    (HomogeneousLocalization.awayMap (grading f)
        (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two a))) (mul_comm _ _)).comp
        (chartProjectionMap f b) =
      (overlapProjectionMap f a b).comp
        (HomogeneousLocalization.awayMap (lineGrading k) (lineVar_mem (lineCoverVar a))
          (mul_comm _ _)) :=
  awayMap_comp_scaledAwayMap _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The morphism `Spec (S_f)_{(X_c)} → Spec (k[U]_{U_c})_0 → ℙ¹`. -/
@[expose]
noncomputable def chartProjection (a : Fin 2) :
    Spec (CommRingCat.of (ChartRing f (coverVar a))) ⟶ projectiveLine k :=
  Spec.map (CommRingCat.ofHom (chartProjectionMap f a)) ≫
    Proj.awayι (lineGrading k) (MvPolynomial.X (lineCoverVar a)) (lineVar_mem _) Nat.one_pos

/-- **The chart morphisms agree on the overlaps.** -/
theorem projection_glue_condition (a b : Fin 2) :
    pullback.fst
        (Proj.awayι (grading f) (var f (coverVar a))
          (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two a))) Nat.one_pos)
        (Proj.awayι (grading f) (var f (coverVar b))
          (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two b))) Nat.one_pos) ≫
        chartProjection f a =
      pullback.snd
        (Proj.awayι (grading f) (var f (coverVar a))
          (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two a))) Nat.one_pos)
        (Proj.awayι (grading f) (var f (coverVar b))
          (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two b))) Nat.one_pos) ≫
        chartProjection f b := by
  rw [← cancel_epi (Proj.pullbackAwayιIso (grading f)
      (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two a))) Nat.one_pos
      (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two b))) Nat.one_pos rfl).inv,
    Proj.pullbackAwayιIso_inv_fst_assoc, Proj.pullbackAwayιIso_inv_snd_assoc,
    chartProjection, chartProjection,
    specMap_comm_square_assoc (projection_overlap_compat_left f a b),
    specMap_comm_square_assoc (projection_overlap_compat_right f a b),
    Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]

/-- The family of chart morphisms. -/
@[expose]
noncomputable def projectionChartFamily (a : Fin 2) :
    (chartCover f).openCover.X a ⟶ projectiveLine k :=
  chartProjection f a

/-- **The projection `(x, y) ↦ x`** from the projective model of `y^2 = f(x)` to the projective
line, `(X : Z : Y) ↦ (X : Z)`. -/
@[expose]
noncomputable def toProjectiveLine : projectiveModel f ⟶ projectiveLine k :=
  (chartCover f).openCover.glueMorphisms (projectionChartFamily f)
    (fun a b => projection_glue_condition f a b)

theorem awayι_comp_toProjectiveLine (a : Fin 2) :
    Proj.awayι (grading f) (var f (coverVar a))
        (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two a))) Nat.one_pos ≫
        toProjectiveLine f =
      chartProjection f a :=
  (chartCover f).openCover.ι_glueMorphisms (projectionChartFamily f) _ a

/-! ### Over `Spec k` -/

theorem chartProjectionMap_lineStructureMap (a : Fin 2) (r : k) :
    chartProjectionMap f a (lineStructureMap (lineCoverVar a) r) =
      chartStructureMap f (coverVar a) r := by
  apply HomogeneousLocalization.val_injective
  rw [chartProjectionMap, val_scaledAwayMap, ← HomogeneousLocalization.algebraMap_apply,
    ← HomogeneousLocalization.algebraMap_apply, val_lineStructureMap, val_chartStructureMap,
    IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 2) k)
      (Localization.Away (MvPolynomial.X (lineCoverVar a) : MvPolynomial (Fin 2) k)),
    scaledLocalizationMap_algebraMap, projectionHom_algebraMap, ← IsScalarTower.algebraMap_apply]

theorem chartProjection_lineToSpecField (a : Fin 2) :
    chartProjection f a ≫ lineToSpecField k =
      Proj.awayι (grading f) (var f (coverVar a))
        (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two a))) Nat.one_pos ≫
        toSpecField f := by
  rw [chartProjection, lineToSpecField, toSpecField, Category.assoc,
    Proj.awayι_toSpecZero_assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun r => chartProjectionMap_lineStructureMap f a r)

/-- **The projection is a morphism over `Spec k`.** -/
theorem toProjectiveLine_lineToSpecField :
    toProjectiveLine f ≫ lineToSpecField k = toSpecField f := by
  refine (chartCover f).openCover.hom_ext _ _ fun a => ?_
  exact (Scheme.Cover.ι_glueMorphisms_assoc (chartCover f).openCover
    (projectionChartFamily f) _ a (lineToSpecField k)).trans
      (chartProjection_lineToSpecField f a)

/-! ### The projection on the affine charts -/

variable {f}

theorem dehomogenize_projectionHom {o : Fin 3} {p : k[X]} (a : Fin 2)
    (h : ChartData f o (coverVar a) p) {o' : Fin 2} (ho' : o' ≠ lineCoverVar a)
    (ho : o'.castSucc = o) (s : MvPolynomial (Fin 2) k) :
    dehomogenize h (projectionHom f s) =
      algebraMap k[X] (HyperellipticCoordRing p) (lineDehom (lineCoverVar a) s) := by
  have e : (dehomogenize h).comp (projectionAlgHom f) =
      (IsScalarTower.toAlgHom k k[X] (HyperellipticCoordRing p)).comp
        (lineDehom (lineCoverVar a)) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, AlgHom.comp_apply, projectionAlgHom_X, dehomogenize_var, lineDehom_X,
      IsScalarTower.toAlgHom_apply]
    rcases fin2_cover o' (lineCoverVar a) ho' i with rfl | rfl
    · rw [ho, chartValues_o p h.ne h.ne_two, lineValues_o ho']
    · rw [castSucc_lineCoverVar, chartValues_c, lineValues_c, map_one]
  exact AlgHom.congr_fun e s

theorem chartToAffine_comp_chartProjectionMap {o : Fin 3} {p : k[X]} (a : Fin 2)
    (h : ChartData f o (coverVar a) p) {o' : Fin 2} (ho' : o' ≠ lineCoverVar a)
    (ho : o'.castSucc = o) :
    (chartToAffine h).comp (chartProjectionMap f a) =
      (algebraMap k[X] (HyperellipticCoordRing p)).comp (lineToAffine (lineCoverVar a)) := by
  refine RingHom.ext fun u => ?_
  obtain ⟨n, s, hs, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (lineGrading k) (lineVar_mem (lineCoverVar a)) u
  rw [RingHom.comp_apply, RingHom.comp_apply, chartProjectionMap, scaledAwayMap_mk,
    chartToAffine_mk, lineToAffine_mk]
  exact dehomogenize_projectionHom a h ho' ho s

theorem chart_comp_toProjectiveLine {o : Fin 3} {p : k[X]} (a : Fin 2)
    (h : ChartData f o (coverVar a) p) {o' : Fin 2} (ho' : o' ≠ lineCoverVar a)
    (ho : o'.castSucc = o) :
    chart h ≫ toProjectiveLine f =
      Spec.map (CommRingCat.ofHom (algebraMap k[X] (HyperellipticCoordRing p))) ≫
        lineChart ho' := by
  rw [chart, lineChart, Category.assoc, awayι_comp_toProjectiveLine, chartProjection,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext fun z =>
    RingHom.congr_fun (chartToAffine_comp_chartProjectionMap a h ho' ho) z)

variable (f)

/-- **On the finite charts, the projection is `Spec` of `k[x] → k[x, y]/(y^2 - f(x))`.** -/
theorem affineChart_comp_toProjectiveLine :
    affineChart f ≫ toProjectiveLine f =
      Spec.map (CommRingCat.ofHom (algebraMap k[X] (HyperellipticCoordRing f))) ≫
        affineLineChart k :=
  chart_comp_toProjectiveLine (o' := 0) 0 (chartData_finite f) (by decide) rfl

/-- On the charts at infinity, the projection is `Spec` of
`k[x'] → k[x', w]/(w^2 - x'^N f(1/x'))`. -/
theorem affineChartAtInfinity_comp_toProjectiveLine :
    affineChartAtInfinity f ≫ toProjectiveLine f =
      Spec.map (CommRingCat.ofHom
        (algebraMap k[X] (HyperellipticCoordRing (reflect (2 * genus f + 2) f)))) ≫
        affineLineChartAtInfinity k :=
  chart_comp_toProjectiveLine (o' := 1) 1 (chartData_infinite f) (by decide) rfl

/-! ### Preimages of the charts -/

theorem lineAwayι_mem_basicOpen_iff {c c' : Fin 2} (z : Spec (CommRingCat.of (LineRing k c'))) :
    Proj.awayι (lineGrading k) (MvPolynomial.X c') (lineVar_mem c') Nat.one_pos z ∈
        Proj.basicOpen (lineGrading k) (MvPolynomial.X c) ↔
      HomogeneousLocalization.Away.isLocalizationElem (lineVar_mem c') (lineVar_mem c) ∉
        z.asIdeal := by
  have h := Proj.awayι_preimage_basicOpen (lineGrading k) (lineVar_mem c') Nat.one_pos
    (lineVar_mem c) Nat.one_pos
  exact (Iff.of_eq (congrArg (fun U => z ∈ U) h)).trans (PrimeSpectrum.mem_basicOpen _ _)

theorem chartProjectionMap_isLocalizationElem (a a' : Fin 2) :
    chartProjectionMap f a' (HomogeneousLocalization.Away.isLocalizationElem
        (lineVar_mem (k := k) (lineCoverVar a')) (lineVar_mem (lineCoverVar a))) =
      HomogeneousLocalization.Away.isLocalizationElem
        (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two a')))
        (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two a))) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.isLocalizationElem, chartProjectionMap, scaledAwayMap_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, map_pow,
    projectionHom_X_lineCoverVar]

theorem toProjectiveLine_awayι_mem_basicOpen_iff (a a' : Fin 2)
    (w : Spec (CommRingCat.of (ChartRing f (coverVar a')))) :
    toProjectiveLine f (Proj.awayι (grading f) (var f (coverVar a'))
        (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two a'))) Nat.one_pos w) ∈
        Proj.basicOpen (lineGrading k) (MvPolynomial.X (lineCoverVar a)) ↔
      Proj.awayι (grading f) (var f (coverVar a'))
        (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two a'))) Nat.one_pos w ∈
        Proj.basicOpen (grading f) (var f (coverVar a)) := by
  have e : toProjectiveLine f (Proj.awayι (grading f) (var f (coverVar a'))
      (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two a'))) Nat.one_pos w) =
      Proj.awayι (lineGrading k) (MvPolynomial.X (lineCoverVar a')) (lineVar_mem _) Nat.one_pos
        (Spec.map (CommRingCat.ofHom (chartProjectionMap f a')) w) := by
    rw [← Scheme.Hom.comp_apply (Proj.awayι (grading f) (var f (coverVar a'))
      (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two a'))) Nat.one_pos)
      (toProjectiveLine f) w, awayι_comp_toProjectiveLine, chartProjection,
      Scheme.Hom.comp_apply]
  have hmem : ∀ u, u ∈ (Spec.map (CommRingCat.ofHom (chartProjectionMap f a')) w).asIdeal ↔
      chartProjectionMap f a' u ∈ w.asIdeal := fun u => Iff.rfl
  rw [e, lineAwayι_mem_basicOpen_iff, awayι_mem_basicOpen_iff f (coverVar_ne_two a)
    (coverVar_ne_two a'), hmem, chartProjectionMap_isLocalizationElem]

theorem toProjectiveLine_mem_basicOpen_iff (a : Fin 2) (x : projectiveModel f) :
    toProjectiveLine f x ∈ Proj.basicOpen (lineGrading k) (MvPolynomial.X (lineCoverVar a)) ↔
      x ∈ Proj.basicOpen (grading f) (var f (coverVar a)) := by
  have key : ∀ a' : Fin 2, x ∈ Proj.basicOpen (grading f) (var f (coverVar a')) →
      (toProjectiveLine f x ∈ Proj.basicOpen (lineGrading k) (MvPolynomial.X (lineCoverVar a)) ↔
        x ∈ Proj.basicOpen (grading f) (var f (coverVar a))) := by
    intro a' hx
    have hx' : x ∈ (Proj.awayι (grading f) (var f (coverVar a'))
        (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two a'))) Nat.one_pos).opensRange
        := by
      rw [Proj.opensRange_awayι]
      exact hx
    obtain ⟨w, rfl⟩ := hx'
    exact toProjectiveLine_awayι_mem_basicOpen_iff f a a' w
  rcases mem_chart_or_mem_chart x with hx | hx
  · exact key 0 hx
  · exact key 1 hx

/-- **The preimage of a standard chart of `ℙ¹` is the corresponding chart of the model**:
the preimage of `D₊(U₁)` is `D₊(Z)` and the preimage of `D₊(U₀)` is `D₊(X)`. -/
theorem preimage_basicOpen_toProjectiveLine (a : Fin 2) :
    toProjectiveLine f ⁻¹ᵁ Proj.basicOpen (lineGrading k) (MvPolynomial.X (lineCoverVar a)) =
      Proj.basicOpen (grading f) (var f (coverVar a)) := by
  ext x
  exact toProjectiveLine_mem_basicOpen_iff f a x

/-- Over the chart `D₊(U_c)` of `ℙ¹`, the projection is the chart map
`Spec (S_f)_{(X_c)} → Spec (k[U]_{U_c})_0`. -/
theorem isPullback_awayι_toProjectiveLine (a : Fin 2) :
    IsPullback (Spec.map (CommRingCat.ofHom (chartProjectionMap f a)))
      (Proj.awayι (grading f) (var f (coverVar a))
        (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two a))) Nat.one_pos)
      (Proj.awayι (lineGrading k) (MvPolynomial.X (lineCoverVar a)) (lineVar_mem _) Nat.one_pos)
      (toProjectiveLine f) :=
  IsOpenImmersion.isPullback _ _ _ _
    (by rw [awayι_comp_toProjectiveLine, chartProjection])
    (by
      rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
      exact preimage_basicOpen_toProjectiveLine f a)

variable {f} in
theorem opensRange_chart {o c : Fin 3} {p : k[X]} (h : ChartData f o c p) :
    (chart h).opensRange = Proj.basicOpen (grading f) (var f c) := by
  change (Spec.map (chartEquiv h).toCommRingCatIso.hom ≫
    Proj.awayι (grading f) (var f c) (var_mem_one f h.weight_c) Nat.one_pos).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

variable {f} in
theorem isPullback_chart_toProjectiveLine {o : Fin 3} {p : k[X]} (a : Fin 2)
    (h : ChartData f o (coverVar a) p) {o' : Fin 2} (ho' : o' ≠ lineCoverVar a)
    (ho : o'.castSucc = o) :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap k[X] (HyperellipticCoordRing p))))
      (chart h) (lineChart ho') (toProjectiveLine f) :=
  IsOpenImmersion.isPullback _ _ _ _ (chart_comp_toProjectiveLine a h ho' ho) (by
    rw [opensRange_lineChart, opensRange_chart]
    exact preimage_basicOpen_toProjectiveLine f a)

/-- **Over the finite chart `𝔸¹ ⊂ ℙ¹`, the projection is `Spec k[x, y]/(y^2 - f(x)) → 𝔸¹`**:
the square formed with `affineChart f` and `affineLineChart k` is a pullback square. -/
theorem isPullback_affineChart_toProjectiveLine :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap k[X] (HyperellipticCoordRing f))))
      (affineChart f) (affineLineChart k) (toProjectiveLine f) :=
  isPullback_chart_toProjectiveLine (o' := 0) 0 (chartData_finite f) (by decide) rfl

/-- Over the chart at infinity, the projection is
`Spec k[x', w]/(w^2 - x'^N f(1/x')) → 𝔸¹`. -/
theorem isPullback_affineChartAtInfinity_toProjectiveLine :
    IsPullback (Spec.map (CommRingCat.ofHom
        (algebraMap k[X] (HyperellipticCoordRing (reflect (2 * genus f + 2) f)))))
      (affineChartAtInfinity f) (affineLineChartAtInfinity k) (toProjectiveLine f) :=
  isPullback_chart_toProjectiveLine (o' := 1) 1 (chartData_infinite f) (by decide) rfl

/-! ### Degree two: finite and locally free of rank two -/

/-- `k[x, y]/(y^2 - p(x))` is free of rank two over `k[x]` (basis `1, y`). -/
theorem free_and_finrank_hyperellipticCoordRing (p : k[X]) :
    Module.Free k[X] (HyperellipticCoordRing p) ∧
      Module.finrank k[X] (HyperellipticCoordRing p) = 2 := by
  have hm : (polyX ^ 2 - C p : k[X][X]).Monic := monic_X_pow_sub_C p two_ne_zero
  refine ⟨Module.Free.of_basis (AdjoinRoot.powerBasis' hm).basis, ?_⟩
  rw [(AdjoinRoot.powerBasis' hm).finrank, AdjoinRoot.powerBasis'_dim, natDegree_X_pow_sub_C]

theorem finite_algebraMap_hyperellipticCoordRing (p : k[X]) :
    (algebraMap k[X] (HyperellipticCoordRing p)).Finite :=
  RingHom.finite_algebraMap.mpr (AdjoinRoot.powerBasis'
    (monic_X_pow_sub_C p two_ne_zero : (polyX ^ 2 - C p : k[X][X]).Monic)).finite

/-- **Over the finite chart of `ℙ¹`, the projection is `Spec` of a free algebra of rank two**:
the pullback square `isPullback_affineChart_toProjectiveLine` together with the freeness of
`k[x, y]/(y^2 - f(x))` of rank two over `k[x]`. -/
theorem toProjectiveLine_affineLine_free_rank_two :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap k[X] (HyperellipticCoordRing f))))
        (affineChart f) (affineLineChart k) (toProjectiveLine f) ∧
      Module.Free k[X] (HyperellipticCoordRing f) ∧
      Module.finrank k[X] (HyperellipticCoordRing f) = 2 :=
  ⟨isPullback_affineChart_toProjectiveLine f, free_and_finrank_hyperellipticCoordRing f⟩

/-- **Over the chart at infinity of `ℙ¹`, the projection is `Spec` of a free algebra of rank
two.** -/
theorem toProjectiveLine_affineLineAtInfinity_free_rank_two :
    IsPullback (Spec.map (CommRingCat.ofHom
          (algebraMap k[X] (HyperellipticCoordRing (reflect (2 * genus f + 2) f)))))
        (affineChartAtInfinity f) (affineLineChartAtInfinity k) (toProjectiveLine f) ∧
      Module.Free k[X] (HyperellipticCoordRing (reflect (2 * genus f + 2) f)) ∧
      Module.finrank k[X] (HyperellipticCoordRing (reflect (2 * genus f + 2) f)) = 2 :=
  ⟨isPullback_affineChartAtInfinity_toProjectiveLine f,
    free_and_finrank_hyperellipticCoordRing _⟩

variable {f} in
theorem chartProjectionMap_eq {o : Fin 3} {p : k[X]} (a : Fin 2)
    (h : ChartData f o (coverVar a) p) {o' : Fin 2} (ho' : o' ≠ lineCoverVar a)
    (ho : o'.castSucc = o) :
    chartProjectionMap f a = (affineToChart h).comp
      ((algebraMap k[X] (HyperellipticCoordRing p)).comp (lineToAffine (lineCoverVar a))) := by
  rw [← chartToAffine_comp_chartProjectionMap a h ho' ho, ← RingHom.comp_assoc,
    affineToChart_chartToAffine, RingHom.id_comp]

variable {f} in
theorem finite_chartProjectionMap_of {o : Fin 3} {p : k[X]} (a : Fin 2)
    (h : ChartData f o (coverVar a) p) {o' : Fin 2} (ho' : o' ≠ lineCoverVar a)
    (ho : o'.castSucc = o) : (chartProjectionMap f a).Finite := by
  rw [chartProjectionMap_eq a h ho' ho]
  refine RingHom.Finite.comp (RingHom.Finite.of_surjective _ fun z =>
      ⟨chartToAffine h z, RingHom.congr_fun (affineToChart_chartToAffine h) z⟩)
    (RingHom.Finite.comp (finite_algebraMap_hyperellipticCoordRing p)
      (RingHom.Finite.of_surjective _ fun z =>
        ⟨affineToLine o' (lineCoverVar a) z, RingHom.congr_fun (lineToAffine_affineToLine ho') z⟩))

/-- Each chart map `(k[U]_{U_c})_0 → (S_{X_c})_0` is finite. -/
theorem finite_chartProjectionMap (a : Fin 2) : (chartProjectionMap f a).Finite := by
  fin_cases a
  · exact finite_chartProjectionMap_of (o' := 0) 0 (chartData_finite f) (by decide) rfl
  · exact finite_chartProjectionMap_of (o' := 1) 1 (chartData_infinite f) (by decide) rfl

/-- The projection is integral (integrality is local on the target; over the chart `D₊(U_c)` it
is the finite chart map). -/
theorem isIntegralHom_toProjectiveLine : IsIntegralHom (toProjectiveLine f) := by
  have hA := IsIntegralHom.hasAffineProperty.{u}
  have hL : IsZariskiLocalAtTarget @IsIntegralHom.{u} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ hA
  have hR : MorphismProperty.RespectsIso @IsIntegralHom.{u} :=
    @HasAffineProperty.instRespectsIsoScheme _ _ hA
  refine (@IsZariskiLocalAtTarget.iff_of_openCover @IsIntegralHom.{u} hL _ _
    (toProjectiveLine f) (lineCover k).openCover).mpr fun a => ?_
  have H := (isPullback_awayι_toProjectiveLine f a).flip
  have hg : IsIntegralHom (Spec.map (CommRingCat.ofHom (chartProjectionMap f a))) :=
    ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mp
      ((IsFinite.SpecMap_iff _).mpr (finite_chartProjectionMap f a))).1
  rw [← H.isoPullback_hom_snd, MorphismProperty.cancel_left_of_respectsIso (hP := hR)] at hg
  exact hg

/-- The projection is locally of finite type (its composite with `ℙ¹ → Spec k` is proper). -/
theorem locallyOfFiniteType_toProjectiveLine : LocallyOfFiniteType (toProjectiveLine f) := by
  have := isProper_toSpecField f
  have : LocallyOfFiniteType (toProjectiveLine f ≫ lineToSpecField k) := by
    rw [toProjectiveLine_lineToSpecField]
    infer_instance
  exact locallyOfFiniteType_of_comp (toProjectiveLine f) (lineToSpecField k)

/-- **The projection `X → ℙ¹` is a finite morphism.** -/
theorem isFinite_toProjectiveLine : IsFinite (toProjectiveLine f) :=
  (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
    ⟨isIntegralHom_toProjectiveLine f, locallyOfFiniteType_toProjectiveLine f⟩

end Hyperelliptic

end ArithmeticOfJacobiPolynomials
