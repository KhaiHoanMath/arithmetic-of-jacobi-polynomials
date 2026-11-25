/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticProjective
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.AlgebraicGeometry.Properties

/-!
# The hyperelliptic model is an integral curve

Let `k` be a field and `f ∈ k[x]` separable of degree `d ≥ 1`. This file proves that the
projective model `projectiveModel f` of `y^2 = f(x)`
(`ArithmeticOfJacobiPolynomials.Hyperelliptic`, built in
`ArithmeticOfJacobiPolynomials.Geometry.HyperellipticProjective`) is an integral scheme of
dimension one.

## Affine results

* `irreducible_X_sq_sub_C`: for `f` squarefree and not constant, `Y^2 - f(x)` is irreducible in
  `k[x][Y]` (a monic quadratic without roots: a root `r` gives `f = r^2`, so `r` is a unit by
  squarefreeness, hence `f` is a unit);
* `isDomain_hyperellipticCoordRing`: `k[x, y]/(y^2 - f(x))` is a domain;
* `isDomain_hyperellipticCoordRing_map`: the same holds over every field extension `K/k` for the
  image of `f` in `K[x]` (geometric integrality of the affine curve);
* `ringKrullDim_hyperellipticCoordRing`: `k[x, y]/(y^2 - f(x))` has Krull dimension `1` (it is a
  domain, finite over the principal ideal domain `k[x]`, and not a field);
* `isDomain_hyperellipticCoordRing_reflect`, `ringKrullDim_hyperellipticCoordRing_reflect`: the
  same for the chart at infinity `w^2 = x'^{2g+2} f(1/x')`.

## The projective model

* `exists_mem_chart_inter`: the two charts `D₊(Z)` and `D₊(X)` meet (the homogeneous core of the
  kernel of the dehomogenization `Z ↦ 1` is a relevant homogeneous prime containing neither `X`
  nor `Z`);
* `irreducibleSpace_projectiveModel`, `isReduced_projectiveModel`, `isIntegral_projectiveModel`:
  the model is irreducible, reduced and integral (both charts are spectra of domains, and they
  meet);
* `topologicalKrullDim_projectiveModel`: `topologicalKrullDim (projectiveModel f) = 1` (every
  point has coheight `≤ 1`, being the coheight of a point of the spectrum of a one-dimensional
  ring, and the chart `D₊(Z)` already has dimension `1`);
* `projectiveModel_curve`: the bundled statement — `projectiveModel f → Spec k` is smooth (when
  `2 ≠ 0` in `k`), proper, the model is integral and `topologicalKrullDim (projectiveModel f) = 1`.
  These are the hypotheses `[Smooth g] [IsProper g] (hdim : topologicalKrullDim X ≤ 1)` of
  `Stacks.Zeta.exists_jacobian_data_abelianVarietyDimension_eq_genus`
  together with integrality.
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace Hyperelliptic

open Polynomial AlgebraicGeometry CategoryTheory

universe u

/-! ### Topological and order-theoretic helpers -/

/-- A space covered by two irreducible open sets that meet is irreducible. -/
theorem irreducibleSpace_of_isOpen_union {T : Type*} [TopologicalSpace T] {U V : Set T}
    (hU : IsOpen U) (hUi : IsIrreducible U) (hVi : IsIrreducible V)
    (hUV : (U ∩ V).Nonempty) (hcov : ∀ x, x ∈ U ∨ x ∈ V) : IrreducibleSpace T := by
  have meets : ∀ W : Set T, IsOpen W → W.Nonempty → (U ∩ W).Nonempty := by
    rintro W hW ⟨w, hw⟩
    rcases hcov w with hwU | hwV
    · exact ⟨w, hwU, hw⟩
    · obtain ⟨z, hzV, hzW, hzU⟩ := hVi.2 W U hW hU ⟨w, hwV, hw⟩
        ⟨hUV.some, hUV.some_mem.2, hUV.some_mem.1⟩
      exact ⟨z, hzU, hzW⟩
  rw [irreducibleSpace_def]
  refine ⟨⟨hUV.some, trivial⟩, fun u v hu hv hu' hv' => ?_⟩
  obtain ⟨z, hzU, hzu, hzv⟩ := hUi.2 u v hu hv
    (meets u hu (by simpa using hu')) (meets v hv (by simpa using hv'))
  exact ⟨z, trivial, hzu, hzv⟩

theorem eq_one_of_le_one_of_not_le_zero {a : WithBot ℕ∞} (h1 : a ≤ 1) (h0 : ¬a ≤ 0) : a = 1 :=
  eq_of_le_of_not_lt h1 fun h => h0 (Order.le_of_lt_succ h)

/-- The coheight of a point of an affine scheme is at most the dimension of the ring. -/
theorem coheight_le_ringKrullDim (R : CommRingCat.{u}) (x : Spec R) :
    (Order.coheight x : WithBot ℕ∞) ≤ ringKrullDim R := by
  rw [← ringKrullDim_stalk_eq_coheight]
  have : x.asIdeal.IsPrime := x.isPrime
  let _ : Algebra R ((Spec R).presheaf.stalk x) := StructureSheaf.stalkAlgebra (↑R) x
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R x
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal ((Spec R).presheaf.stalk x)]
  exact Ideal.height_le_ringKrullDim_of_isPrime

/-- A scheme all of whose points have coheight `≤ n` has dimension `≤ n`. -/
theorem topologicalKrullDim_le_of_coheight_le {Y : Scheme.{u}} {n : ℕ∞}
    (h : ∀ y : Y, Order.coheight y ≤ n) : topologicalKrullDim Y ≤ n := by
  have gp : ∀ Z : TopologicalSpace.IrreducibleCloseds Y,
      IsGenericPoint Z.isIrreducible.genericPoint (Z : Set Y) := fun Z => by
    have h' := Z.isIrreducible.isGenericPoint_genericPoint_closure
    rwa [Z.isClosed.closure_eq] at h'
  have hmono : StrictMono fun Z : TopologicalSpace.IrreducibleCloseds Y =>
      Z.isIrreducible.genericPoint := by
    intro Z Z' hZ
    refine lt_of_le_not_ge ?_ ?_
    · rw [Scheme.le_iff_specializes]
      exact (gp Z').specializes (SetLike.coe_subset_coe.mpr hZ.le (gp Z).mem)
    · intro hle
      rw [Scheme.le_iff_specializes] at hle
      have hmem : Z'.isIrreducible.genericPoint ∈ (Z : Set Y) := by
        rw [← (gp Z).def]
        exact specializes_iff_mem_closure.mp hle
      have hsub : (Z' : Set Y) ⊆ Z := by
        rw [← (gp Z').def]
        exact Z.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem)
      exact hZ.not_ge (SetLike.coe_subset_coe.mp hsub)
  refine (Order.krullDim_le_of_strictMono _ hmono).trans ?_
  rw [Order.krullDim_eq_iSup_coheight]
  exact iSup_le fun y => WithBot.coe_le_coe.mpr (h y)

variable {k : Type u} [Field k]

/-! ### The affine curve `y^2 = f(x)` is integral of dimension one -/

theorem monic_X_sq_sub_C (f : k[X]) : (X ^ 2 - C f : k[X][X]).Monic :=
  monic_X_pow_sub_C f two_ne_zero

theorem roots_X_sq_sub_C_eq_zero {f : k[X]} (hf : Squarefree f) (hdeg : 0 < f.natDegree) :
    (X ^ 2 - C f : k[X][X]).roots = 0 := by
  refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
  rw [mem_roots (monic_X_sq_sub_C f).ne_zero, IsRoot.def, eval_sub, eval_pow, eval_X, eval_C,
    sub_eq_zero] at hr
  have hu : IsUnit r := hf r ⟨1, by rw [mul_one, ← hr, sq]⟩
  have hfu : IsUnit f := hr ▸ hu.pow 2
  exact absurd (natDegree_eq_zero_of_isUnit hfu) hdeg.ne'

/-- `Y^2 - f(x)` is irreducible in `k[x][Y]` when `f` is squarefree and not constant. -/
theorem irreducible_X_sq_sub_C {f : k[X]} (hf : Squarefree f) (hdeg : 0 < f.natDegree) :
    Irreducible (X ^ 2 - C f : k[X][X]) := by
  rw [(monic_X_sq_sub_C f).irreducible_iff_roots_eq_zero_of_degree_le_three
    natDegree_X_pow_sub_C.symm.le (natDegree_X_pow_sub_C.le.trans (by norm_num))]
  exact roots_X_sq_sub_C_eq_zero hf hdeg

theorem isDomain_hyperellipticCoordRing_of_squarefree {f : k[X]} (hf : Squarefree f)
    (hdeg : 0 < f.natDegree) : IsDomain (HyperellipticCoordRing f) :=
  AdjoinRoot.isDomain_of_prime (irreducible_X_sq_sub_C hf hdeg).prime

/-- **The affine curve `y^2 = f(x)` is integral**: for `f` separable of positive degree,
`k[x, y]/(y^2 - f(x))` is a domain. -/
theorem isDomain_hyperellipticCoordRing {f : k[X]} (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    IsDomain (HyperellipticCoordRing f) :=
  isDomain_hyperellipticCoordRing_of_squarefree hf.squarefree hdeg

/-- **Geometric integrality of the affine curve**: for every field extension `K/k`,
`K[x, y]/(y^2 - f(x))` is a domain. -/
theorem isDomain_hyperellipticCoordRing_map {f : k[X]} (hf : f.Separable)
    (hdeg : 0 < f.natDegree) (K : Type*) [Field K] [Algebra k K] :
    IsDomain (HyperellipticCoordRing (f.map (algebraMap k K))) :=
  isDomain_hyperellipticCoordRing hf.map (by rwa [natDegree_map])

theorem finite_hyperellipticCoordRing (f : k[X]) :
    Module.Finite k[X] (HyperellipticCoordRing f) :=
  (AdjoinRoot.powerBasis' (monic_X_sq_sub_C f)).finite

theorem injective_algebraMap_hyperellipticCoordRing (f : k[X]) :
    Function.Injective (algebraMap k[X] (HyperellipticCoordRing f)) := by
  rw [AdjoinRoot.algebraMap_eq]
  refine AdjoinRoot.of.injective_of_degree_ne_zero ?_
  rw [degree_X_pow_sub_C two_pos]
  norm_num

theorem ringKrullDim_hyperellipticCoordRing_of_squarefree {f : k[X]} (hf : Squarefree f)
    (hdeg : 0 < f.natDegree) : ringKrullDim (HyperellipticCoordRing f) = 1 := by
  have := isDomain_hyperellipticCoordRing_of_squarefree hf hdeg
  have := finite_hyperellipticCoordRing f
  have : Ring.DimensionLEOne (HyperellipticCoordRing f) :=
    Ring.DimensionLEOne.of_isIntegral (R := k[X]) _
  refine eq_one_of_le_one_of_not_le_zero ?_ fun h0 => ?_
  · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
    infer_instance
  · rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h0
    exact Polynomial.not_isField k (isField_of_isIntegral_of_isField
      (injective_algebraMap_hyperellipticCoordRing f) Ring.KrullDimLE.isField_of_isDomain)

/-- **The affine curve `y^2 = f(x)` has dimension one.** -/
theorem ringKrullDim_hyperellipticCoordRing {f : k[X]} (hf : f.Separable)
    (hdeg : 0 < f.natDegree) : ringKrullDim (HyperellipticCoordRing f) = 1 :=
  ringKrullDim_hyperellipticCoordRing_of_squarefree hf.squarefree hdeg

/-! ### The chart at infinity -/

/-- The reflection `x^N f(1/x)` (`N ≥ 2`) of a squarefree polynomial is not constant. -/
theorem natDegree_reflect_pos {f : k[X]} (hf : Squarefree f) {N : ℕ} (hN2 : 2 ≤ N) :
    0 < (reflect N f).natDegree := by
  by_contra h
  have h0 : (reflect N f).natDegree = 0 := by omega
  have hc := eq_C_of_natDegree_eq_zero h0
  have hfe : f = C ((reflect N f).coeff 0) * X ^ N := by
    rw [← reflect_C, ← hc, reflect_reflect]
  have hdvd : X * X ∣ f := by
    rw [hfe, ← sq]
    exact dvd_mul_of_dvd_right (pow_dvd_pow X hN2) _
  exact not_isUnit_X (hf X hdvd)

theorem separable_reflect_genus {f : k[X]} (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    (reflect (2 * genus f + 2) f).Separable :=
  separable_reflect hf (natDegree_le_two_mul_genus_add_two f) (two_mul_genus_add_two_le f hdeg)

theorem natDegree_reflect_genus_pos {f : k[X]} (hf : f.Separable) :
    0 < (reflect (2 * genus f + 2) f).natDegree :=
  natDegree_reflect_pos hf.squarefree (by omega)

/-- The chart at infinity `k[x', w]/(w^2 - x'^{2g+2} f(1/x'))` is a domain. -/
theorem isDomain_hyperellipticCoordRing_reflect {f : k[X]} (hf : f.Separable)
    (hdeg : 0 < f.natDegree) :
    IsDomain (HyperellipticCoordRing (reflect (2 * genus f + 2) f)) :=
  isDomain_hyperellipticCoordRing (separable_reflect_genus hf hdeg)
    (natDegree_reflect_genus_pos hf)

/-- The chart at infinity `k[x', w]/(w^2 - x'^{2g+2} f(1/x'))` has dimension one. -/
theorem ringKrullDim_hyperellipticCoordRing_reflect {f : k[X]} (hf : f.Separable)
    (hdeg : 0 < f.natDegree) :
    ringKrullDim (HyperellipticCoordRing (reflect (2 * genus f + 2) f)) = 1 :=
  ringKrullDim_hyperellipticCoordRing (separable_reflect_genus hf hdeg)
    (natDegree_reflect_genus_pos hf)

/-! ### The projective model -/

variable {f : k[X]} {o c : Fin 3} {p : k[X]}

theorem isDomain_chartRing (h : ChartData f o c p) [IsDomain (HyperellipticCoordRing p)] :
    IsDomain (ChartRing f c) :=
  MulEquiv.isDomain (HyperellipticCoordRing p) (chartEquiv h).toMulEquiv

theorem ringKrullDim_chartRing (h : ChartData f o c p) :
    ringKrullDim (ChartRing f c) = ringKrullDim (HyperellipticCoordRing p) :=
  ringKrullDim_eq_of_ringEquiv (chartEquiv h)

theorem range_awayι (h : ChartData f o c p) :
    Set.range (Proj.awayι (grading f) (var f c) (var_mem_one f h.weight_c) Nat.one_pos) =
      (Proj.basicOpen (grading f) (var f c) : Set (projectiveModel f)) := by
  rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]

/-- Each chart of the model is irreducible when its affine ring is a domain. -/
theorem isIrreducible_chart (h : ChartData f o c p) [IsDomain (HyperellipticCoordRing p)] :
    IsIrreducible (Proj.basicOpen (grading f) (var f c) : Set (projectiveModel f)) := by
  have := isDomain_chartRing h
  rw [← range_awayι h, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _
    ((Proj.awayι (grading f) (var f c) (var_mem_one f h.weight_c) Nat.one_pos).continuous
      ).continuousOn

theorem dehomogenize_var_one_ne_zero [Nontrivial (HyperellipticCoordRing f)] :
    dehomogenize (chartData_finite f) (var f 1) ≠ 0 := by
  rw [dehomogenize_var, chartValues_c]
  exact one_ne_zero

theorem dehomogenize_var_zero_ne_zero [Nontrivial (HyperellipticCoordRing f)] :
    dehomogenize (chartData_finite f) (var f 0) ≠ 0 := by
  rw [dehomogenize_var, chartValues_o f (chartData_finite f).ne (chartData_finite f).ne_two]
  intro h0
  have := injective_algebraMap_hyperellipticCoordRing f (h0.trans (map_zero _).symm)
  exact X_ne_zero this

/-- **The two charts meet**: there is a point of `projectiveModel f` in `D₊(Z) ∩ D₊(X)`. -/
theorem exists_mem_chart_inter [IsDomain (HyperellipticCoordRing f)] :
    ∃ x : projectiveModel f, x ∈ Proj.basicOpen (grading f) (var f 1) ∧
      x ∈ Proj.basicOpen (grading f) (var f 0) := by
  let φ : HomogeneousCoordRing f →+* HyperellipticCoordRing f :=
    (dehomogenize (chartData_finite f)).toRingHom
  let J := (RingHom.ker φ).homogeneousCore (grading f)
  have hJ : ∀ s, s ∈ J → φ s = 0 := fun s hs =>
    RingHom.mem_ker.mp (Ideal.toIdeal_homogeneousCore_le (grading f) _ hs)
  have hprime : J.toIdeal.IsPrime := (RingHom.ker_isPrime φ).homogeneousCore
  have hrel : ¬HomogeneousIdeal.irrelevant (grading f) ≤ J := fun hle =>
    dehomogenize_var_one_ne_zero (hJ _ (hle (HomogeneousIdeal.mem_irrelevant_of_mem
      (grading f) Nat.one_pos (var_mem_one f (chartData_finite f).weight_c))))
  let x : ProjectiveSpectrum (grading f) := ⟨J, hprime, hrel⟩
  exact ⟨x, (Proj.mem_basicOpen (grading f) (var f 1) x).mpr fun hm =>
      dehomogenize_var_one_ne_zero (hJ _ hm),
    (Proj.mem_basicOpen (grading f) (var f 0) x).mpr fun hm =>
      dehomogenize_var_zero_ne_zero (hJ _ hm)⟩

theorem mem_chart_or_mem_chart (x : projectiveModel f) :
    x ∈ Proj.basicOpen (grading f) (var f 1) ∨ x ∈ Proj.basicOpen (grading f) (var f 0) := by
  have hx : x ∈ Proj.basicOpen (grading f) (var f 1) ⊔ Proj.basicOpen (grading f) (var f 0) := by
    rw [iSup_chart_eq_top f]
    trivial
  exact TopologicalSpace.Opens.mem_sup.mp hx

/-- **The model is irreducible.** -/
theorem irreducibleSpace_projectiveModel (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    IrreducibleSpace (projectiveModel f) := by
  have := isDomain_hyperellipticCoordRing hf hdeg
  have := isDomain_hyperellipticCoordRing_reflect hf hdeg
  obtain ⟨x, hx1, hx0⟩ := exists_mem_chart_inter (f := f)
  exact irreducibleSpace_of_isOpen_union (Proj.basicOpen (grading f) (var f 1)).isOpen
    (isIrreducible_chart (chartData_finite f))
    (isIrreducible_chart (chartData_infinite f)) ⟨x, hx1, hx0⟩ mem_chart_or_mem_chart

theorem isReduced_chart (h : ChartData f o c p) [IsDomain (HyperellipticCoordRing p)] :
    IsReduced (Proj.basicOpen (grading f) (var f c)).toScheme := by
  have := isDomain_chartRing h
  exact isReduced_of_isOpenImmersion
    (Proj.basicOpenIsoSpec (grading f) (var f c) (var_mem_one f h.weight_c) Nat.one_pos).hom

/-- **The model is reduced.** -/
theorem isReduced_projectiveModel (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    IsReduced (projectiveModel f) := by
  have := isDomain_hyperellipticCoordRing hf hdeg
  have := isDomain_hyperellipticCoordRing_reflect hf hdeg
  let U : Fin 2 → (projectiveModel f).Opens :=
    ![Proj.basicOpen (grading f) (var f 1), Proj.basicOpen (grading f) (var f 0)]
  have hU : TopologicalSpace.IsOpenCover U := by
    refine eq_top_iff.mpr fun x _ => ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    rcases mem_chart_or_mem_chart x with hx | hx
    · exact ⟨0, hx⟩
    · exact ⟨1, hx⟩
  have hred' : ∀ i : Fin 2, IsReduced (U i).toScheme := by
    intro i
    fin_cases i
    · exact isReduced_chart (chartData_finite f)
    · exact isReduced_chart (chartData_infinite f)
  have hred : ∀ i, IsReduced ((Scheme.openCoverOfIsOpenCover _ U hU).X i) := hred'
  exact IsReduced.of_openCover (X := projectiveModel f) (Scheme.openCoverOfIsOpenCover _ U hU)

/-- **The model is integral.** -/
theorem isIntegral_projectiveModel (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    IsIntegral (projectiveModel f) := by
  have := isReduced_projectiveModel hf hdeg
  have := irreducibleSpace_projectiveModel hf hdeg
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem coheight_le_one_of_mem_chart (h : ChartData f o c p)
    (hp : ringKrullDim (HyperellipticCoordRing p) ≤ 1) {x : projectiveModel f}
    (hx : x ∈ Proj.basicOpen (grading f) (var f c)) : Order.coheight x ≤ 1 := by
  have hx' : x ∈ Set.range
      (Proj.awayι (grading f) (var f c) (var_mem_one f h.weight_c) Nat.one_pos) := by
    rw [range_awayι h]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  rw [coheight_eq_of_isOpenImmersion]
  have := (coheight_le_ringKrullDim _ y).trans ((ringKrullDim_chartRing h).trans_le hp)
  exact_mod_cast this

/-- Every point of the model has coheight at most one. -/
theorem coheight_le_one (hf : f.Separable) (hdeg : 0 < f.natDegree) (x : projectiveModel f) :
    Order.coheight x ≤ 1 := by
  rcases mem_chart_or_mem_chart x with hx | hx
  · exact coheight_le_one_of_mem_chart (chartData_finite f)
      (ringKrullDim_hyperellipticCoordRing hf hdeg).le hx
  · exact coheight_le_one_of_mem_chart (chartData_infinite f)
      (ringKrullDim_hyperellipticCoordRing_reflect hf hdeg).le hx

/-- **The model has dimension one.** -/
theorem topologicalKrullDim_projectiveModel (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    topologicalKrullDim (projectiveModel f) = 1 := by
  have hle : topologicalKrullDim (projectiveModel f) ≤ ((1 : ℕ∞) : WithBot ℕ∞) :=
    topologicalKrullDim_le_of_coheight_le (coheight_le_one hf hdeg)
  refine le_antisymm (by exact_mod_cast hle) ?_
  have h := (Proj.awayι (grading f) (var f 1) (var_mem_one f (chartData_finite f).weight_c)
    Nat.one_pos).isOpenEmbedding.isInducing.topologicalKrullDim_le
  refine le_trans ?_ h
  refine le_of_eq ?_
  refine Eq.trans ?_ (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (ChartRing f 1)).symm
  rw [ringKrullDim_chartRing (chartData_finite f), ringKrullDim_hyperellipticCoordRing hf hdeg]

/-- **The hyperelliptic model is a smooth proper integral curve**: for `f` separable of degree
`≥ 1` over a field `k` with `2 ≠ 0`, the structure morphism `projectiveModel f → Spec k` is
smooth and proper, `projectiveModel f` is integral, and it has dimension one. -/
theorem projectiveModel_curve (h2 : (2 : k) ≠ 0) (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    Smooth (toSpecField f) ∧ IsProper (toSpecField f) ∧ IsIntegral (projectiveModel f) ∧
      topologicalKrullDim (projectiveModel f) = 1 :=
  ⟨smooth_toSpecField h2 hf hdeg, isProper_toSpecField f, isIntegral_projectiveModel hf hdeg,
    topologicalKrullDim_projectiveModel hf hdeg⟩

end Hyperelliptic

end ArithmeticOfJacobiPolynomials
