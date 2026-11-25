/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticAffine
public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticGraded
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The smooth projective model of `y^2 = f(x)`

Let `k` be a field and `f ∈ k[x]` of degree `d ≥ 1`; put `g = ⌊(d - 1)/2⌋` (`genus f`) and
`N = 2g + 2 ∈ {d, d + 1}`. The projective model of `y^2 = f(x)` is
`Proj k[X, Z, Y]/(Y^2 - F(X, Z))`, where `X, Z` have weight `1`, `Y` has weight `g + 1` and
`F(X, Z) = Z^N f(X/Z) = Σ_{i ≤ N} f_i X^i Z^{N-i}` (`projectiveModel f`, built from the weighted
grading of `MvPolynomial (Fin 3) k` descended to the quotient,
`ArithmeticOfJacobiPolynomials.GradedQuotient`).
It is the gluing of the two affine charts
* `D₊(Z) ≅ Spec k[x, y]/(y^2 - f(x))`, `x = X/Z`, `y = Y/Z^{g+1}` (`affineChart`), and
* `D₊(X) ≅ Spec k[x', w]/(w^2 - x'^N f(1/x'))`, `x' = Z/X`, `w = Y/X^{g+1}`
  (`affineChartAtInfinity`; the polynomial is `reflect N f`),

glued along `x' = 1/x`, `w = y/x^{g+1}` on `D₊(XZ)`; the two charts cover the model
(`iSup_chart_eq_top`). Results:

* `isProper_toSpecField`: the structure morphism `projectiveModel f → Spec k` is proper (in
  particular separated, `isSeparated_toSpecField`);
* `chartEquiv`: the coordinate ring of each chart `D₊(·)` of `Proj` is isomorphic, compatibly
  with `k`, to the affine coordinate ring `k[x, y]/(y^2 - p(x))` of the chart (`p = f` or
  `p = reflect N f`), so `affineChart` and `affineChartAtInfinity` are open immersions over `k`
  (`affineChart_toSpecField`);
* `smooth_toSpecField`: if `2 ≠ 0` in `k` and `f` is separable, the model is smooth over `k`
  (both charts are smooth by the Jacobian criterion,
  `ArithmeticOfJacobiPolynomials.Hyperelliptic.smooth_hyperellipticCoordRing`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace Hyperelliptic

open Polynomial AlgebraicGeometry CategoryTheory GradedQuotient

universe u

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ### Weighted homogeneous polynomials -/

/-- Scaling the variables by `t^{w_i}` scales a weighted homogeneous polynomial of degree `n` by
`t^n`. -/
theorem aeval_pow_weight_mul {σ R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (w : σ → ℕ) {P : MvPolynomial σ R} {n : ℕ} (hP : P.IsWeightedHomogeneous w n) (t : B)
    (a : σ → B) :
    MvPolynomial.aeval (fun i => t ^ w i * a i) P = t ^ n * MvPolynomial.aeval a P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight w d = n := hP (MvPolynomial.mem_support_iff.mp hd)
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, ← hw, Finsupp.weight_apply]
  simp only [Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum, smul_eq_mul, mul_comm (w _) (d _)]
  ring

variable {k : Type u} [Field k]

/-- The weights `(1, 1, g + 1)` of the variables `(X, Z, Y)`. -/
@[expose]
def weights (g : ℕ) : Fin 3 → ℕ := ![1, 1, g + 1]

@[simp] theorem weights_zero (g : ℕ) : weights g 0 = 1 := rfl

@[simp] theorem weights_one (g : ℕ) : weights g 1 = 1 := rfl

@[simp] theorem weights_two (g : ℕ) : weights g 2 = g + 1 := rfl

theorem weights_ne_zero (g : ℕ) (i : Fin 3) : weights g i ≠ 0 := by
  fin_cases i <;> simp [weights]

/-- `g = ⌊(deg f - 1)/2⌋`. -/
@[expose]
def genus (f : k[X]) : ℕ := (f.natDegree - 1) / 2

theorem natDegree_le_two_mul_genus_add_two (f : k[X]) : f.natDegree ≤ 2 * genus f + 2 := by
  unfold genus
  omega

theorem two_mul_genus_add_two_le (f : k[X]) (hf : 0 < f.natDegree) :
    2 * genus f + 2 ≤ f.natDegree + 1 := by
  unfold genus
  omega

/-- The binary form `Σ_{i ≤ N} p_i X_o^i X_c^{N - i}`. -/
@[expose]
noncomputable def binaryForm (o c : Fin 3) (p : k[X]) (N : ℕ) : MvPolynomial (Fin 3) k :=
  ∑ i ∈ Finset.range (N + 1),
    MvPolynomial.C (p.coeff i) * MvPolynomial.X o ^ i * MvPolynomial.X c ^ (N - i)

/-- The weighted homogeneous equation `Y^2 - Σ_{i ≤ N} p_i X_o^i X_c^{N - i}`. -/
@[expose]
noncomputable def equation (o c : Fin 3) (p : k[X]) (N : ℕ) : MvPolynomial (Fin 3) k :=
  MvPolynomial.X 2 ^ 2 - binaryForm o c p N

theorem aeval_binaryForm {B : Type*} [CommRing B] [Algebra k B] (o c : Fin 3) (p : k[X])
    {N : ℕ} (hp : p.natDegree ≤ N) (v : Fin 3 → B) (hv : v c = 1) :
    MvPolynomial.aeval v (binaryForm o c p N) = aeval (v o) p := by
  rw [aeval_eq_sum_range' (by omega : p.natDegree < N + 1), binaryForm]
  simp only [map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X, hv,
    one_pow, mul_one, Algebra.smul_def]

/-- `Z^N f(X/Z) = X^N f^*(Z/X)` with `f^* = reflect N f`. -/
theorem binaryForm_reflect (p : k[X]) (N : ℕ) :
    binaryForm 0 1 p N = binaryForm 1 0 (reflect N p) N := by
  rw [binaryForm, binaryForm, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [coeff_reflect, revAt_le hj', show N + 1 - 1 - j = N - j by omega, Nat.sub_sub_self hj']
  ring

theorem binaryForm_mem (g : ℕ) {o c : Fin 3} (ho : weights g o = 1) (hc : weights g c = 1)
    (p : k[X]) (N : ℕ) :
    binaryForm o c p N ∈ MvPolynomial.weightedHomogeneousSubmodule k (weights g) N := by
  refine Submodule.sum_mem _ fun i hi => ?_
  have hi' : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
  have h := ((MvPolynomial.isWeightedHomogeneous_C (weights g) (p.coeff i)).mul
    ((MvPolynomial.isWeightedHomogeneous_X (R := k) (weights g) o).pow i)).mul
    ((MvPolynomial.isWeightedHomogeneous_X (R := k) (weights g) c).pow (N - i))
  convert h using 1
  rw [ho, hc, smul_eq_mul, smul_eq_mul, mul_one, mul_one, zero_add]
  omega

theorem equation_mem (g : ℕ) {o c : Fin 3} (ho : weights g o = 1) (hc : weights g c = 1)
    (p : k[X]) :
    equation o c p (2 * g + 2) ∈
      MvPolynomial.weightedHomogeneousSubmodule k (weights g) (2 * g + 2) := by
  refine Submodule.sub_mem _ ?_ (binaryForm_mem g ho hc p _)
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
  convert (MvPolynomial.isWeightedHomogeneous_X (R := k) (weights g) 2).pow 2 using 1
  rw [weights_two, smul_eq_mul]
  ring

/-! ### The projective model -/

/-- The ideal `(Y^2 - Z^N f(X/Z))` of `k[X, Z, Y]`, `N = 2g + 2`. -/
@[expose]
noncomputable def coordIdeal (f : k[X]) : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span {equation 0 1 f (2 * genus f + 2)}

/-- The weighted homogeneous coordinate ring `k[X, Z, Y]/(Y^2 - Z^N f(X/Z))`. -/
abbrev HomogeneousCoordRing (f : k[X]) : Type u := MvPolynomial (Fin 3) k ⧸ coordIdeal f

/-- The grading of `HomogeneousCoordRing f` (weights `1, 1, g + 1`). -/
@[expose]
noncomputable def grading (f : k[X]) : ℕ → Submodule k (HomogeneousCoordRing f) :=
  quotientGrading (MvPolynomial.weightedHomogeneousSubmodule k (weights (genus f)))
    (coordIdeal f)

theorem coordIdeal_isHomogeneous (f : k[X]) :
    (coordIdeal f).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule k (weights (genus f))) := by
  apply Ideal.homogeneous_span
  rintro x rfl
  exact ⟨_, equation_mem (genus f) (weights_zero _) (weights_one _) f⟩

noncomputable instance (f : k[X]) : GradedAlgebra (grading f) :=
  quotientGradedAlgebra _ _ (coordIdeal_isHomogeneous f)

/-- The projective model `Proj k[X, Z, Y]/(Y^2 - Z^N f(X/Z))` of `y^2 = f(x)`. -/
noncomputable abbrev projectiveModel (f : k[X]) : Scheme.{u} := Proj (grading f)

/-- The structure morphism `projectiveModel f → Spec k`. -/
@[expose]
noncomputable def toSpecField (f : k[X]) : projectiveModel f ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero (grading f) ≫ Spec.map (CommRingCat.ofHom (algebraMap k (grading f 0)))

/-- The degree-zero part of the homogeneous coordinate ring is `k`. -/
theorem algebraMap_gradeZero_surjective (f : k[X]) :
    Function.Surjective (algebraMap k (grading f 0)) := by
  rintro ⟨_, P, hP, rfl⟩
  have h1 : P = MvPolynomial.C (P.coeff 0) :=
    (MvPolynomial.weightedHomogeneousComponent_eq_self hP).symm.trans
      (MvPolynomial.weightedHomogeneousComponent_zero P (weights_ne_zero _))
  refine ⟨P.coeff 0, Subtype.ext ?_⟩
  change algebraMap k (HomogeneousCoordRing f) (P.coeff 0) = Ideal.Quotient.mk _ P
  conv_rhs => rw [h1]
  rfl

instance (f : k[X]) : IsScalarTower k (grading f 0) (HomogeneousCoordRing f) :=
  IsScalarTower.of_algebraMap_eq (R := k) (S := grading f 0) (A := HomogeneousCoordRing f)
    fun _ => rfl

instance (f : k[X]) : Algebra.FiniteType (grading f 0) (HomogeneousCoordRing f) :=
  Algebra.FiniteType.of_restrictScalars_finiteType (R := k) _ _

/-- The projective model is proper over `k`. -/
theorem isProper_toSpecField (f : k[X]) : IsProper (toSpecField f) := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (grading f 0)))) :=
    (IsFinite.SpecMap_iff _).mpr
      (RingHom.Finite.of_surjective _ (algebraMap_gradeZero_surjective f))
  rw [toSpecField]
  infer_instance

/-- The projective model is separated over `k`. -/
theorem isSeparated_toSpecField (f : k[X]) : IsSeparated (toSpecField f) := by
  have := isProper_toSpecField f
  infer_instance

/-! ### The affine charts -/

/-- The class of the variable `X_i` (`X_0 = X`, `X_1 = Z`, `X_2 = Y`). -/
@[expose]
noncomputable def var (f : k[X]) (i : Fin 3) : HomogeneousCoordRing f :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

theorem var_mem (f : k[X]) (i : Fin 3) : var f i ∈ grading f (weights (genus f) i) :=
  mk_mem_quotientGrading _ _ (MvPolynomial.isWeightedHomogeneous_X (R := k) _ i)

theorem var_mem_one (f : k[X]) {i : Fin 3} (hi : weights (genus f) i = 1) :
    var f i ∈ grading f 1 :=
  hi ▸ var_mem f i

/-- The data of a chart `D₊(X_c)`: `X_o` is the other variable of weight one, and the equation
is `Y^2 = Σ p_i X_o^i X_c^{N-i}`. -/
structure ChartData (f : k[X]) (o c : Fin 3) (p : k[X]) : Prop where
  ne : o ≠ c
  ne_two : o ≠ 2
  ne_two' : c ≠ 2
  cover : ∀ i, i = o ∨ i = c ∨ i = 2
  weight_o : weights (genus f) o = 1
  weight_c : weights (genus f) c = 1
  ideal_eq : coordIdeal f = Ideal.span {equation o c p (2 * genus f + 2)}
  natDegree_le : p.natDegree ≤ 2 * genus f + 2

/-- The chart `D₊(Z)`: `y^2 = f(x)`. -/
theorem chartData_finite (f : k[X]) : ChartData f 0 1 f where
  ne := by decide
  ne_two := by decide
  ne_two' := by decide
  cover := by decide
  weight_o := rfl
  weight_c := rfl
  ideal_eq := rfl
  natDegree_le := natDegree_le_two_mul_genus_add_two f

/-- The chart `D₊(X)`: `w^2 = x'^N f(1/x')`. -/
theorem chartData_infinite (f : k[X]) :
    ChartData f 1 0 (reflect (2 * genus f + 2) f) where
  ne := by decide
  ne_two := by decide
  ne_two' := by decide
  cover := by decide
  weight_o := rfl
  weight_c := rfl
  ideal_eq := by rw [coordIdeal, equation, equation, binaryForm_reflect]
  natDegree_le := natDegree_reflect_le.trans
    (max_le le_rfl (natDegree_le_two_mul_genus_add_two f))

/-- The values of the dehomogenization `X_c ↦ 1`, `Y ↦ y`, `X_o ↦ x`. -/
@[expose]
noncomputable def chartValues (c : Fin 3) (p : k[X]) (i : Fin 3) : HyperellipticCoordRing p :=
  if i = c then 1 else if i = 2 then AdjoinRoot.root _ else algebraMap k[X] _ Polynomial.X

theorem chartValues_c (c : Fin 3) (p : k[X]) : chartValues c p c = 1 := by
  simp [chartValues]

theorem chartValues_two {c : Fin 3} (p : k[X]) (hc : c ≠ 2) :
    chartValues c p 2 = AdjoinRoot.root _ := by
  simp [chartValues, Ne.symm hc]

theorem chartValues_o {o c : Fin 3} (p : k[X]) (hoc : o ≠ c) (ho : o ≠ 2) :
    chartValues c p o = algebraMap k[X] _ Polynomial.X := by
  simp [chartValues, hoc, ho]

theorem root_sq_eq_algebraMap (p : k[X]) :
    (AdjoinRoot.root (X ^ 2 - C p : k[X][X])) ^ 2 =
      algebraMap k[X] (HyperellipticCoordRing p) p := by
  rw [root_sq_eq_of, AdjoinRoot.algebraMap_eq]

theorem aeval_algebraMap_X (p : k[X]) :
    aeval (algebraMap k[X] (HyperellipticCoordRing p) Polynomial.X) p =
      algebraMap k[X] (HyperellipticCoordRing p) p := by
  rw [aeval_algebraMap_apply, aeval_X_left_apply]

variable {f : k[X]} {o c : Fin 3} {p : k[X]}

/-- The dehomogenization `S → k[x, y]/(y^2 - p(x))`. -/
@[expose]
noncomputable def dehomogenize (h : ChartData f o c p) :
    HomogeneousCoordRing f →ₐ[k] HyperellipticCoordRing p :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (chartValues c p)) (by
    intro a ha
    rw [h.ideal_eq, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, equation, map_sub, aeval_binaryForm o c p h.natDegree_le _ (chartValues_c c p),
      map_pow, MvPolynomial.aeval_X, chartValues_two p h.ne_two', chartValues_o p h.ne h.ne_two,
      aeval_algebraMap_X, root_sq_eq_algebraMap, sub_self, mul_zero])

theorem dehomogenize_mk (h : ChartData f o c p) (P : MvPolynomial (Fin 3) k) :
    dehomogenize h (Ideal.Quotient.mk _ P) = MvPolynomial.aeval (chartValues c p) P :=
  rfl

theorem dehomogenize_var (h : ChartData f o c p) (i : Fin 3) :
    dehomogenize h (var f i) = chartValues c p i := by
  rw [var, dehomogenize_mk, MvPolynomial.aeval_X]

/-- The coordinate ring `(S_{X_c})_0` of the chart `D₊(X_c)`. -/
abbrev ChartRing (f : k[X]) (c : Fin 3) : Type u :=
  HomogeneousLocalization.Away (grading f) (var f c)

/-- `S_{X_c} → k[x, y]/(y^2 - p(x))`, `a/X_c^n ↦ a(x, 1, y)`. -/
@[expose]
noncomputable def chartLift (h : ChartData f o c p) :
    Localization.Away (var f c) →+* HyperellipticCoordRing p :=
  IsLocalization.Away.lift (S := Localization.Away (var f c)) (var f c)
    (g := ((dehomogenize h : _ →ₐ[k] _) : HomogeneousCoordRing f →+* _)) (by
      change IsUnit (dehomogenize h (var f c))
      rw [dehomogenize_var, chartValues_c]
      exact isUnit_one)

theorem chartLift_algebraMap (h : ChartData f o c p) (s : HomogeneousCoordRing f) :
    chartLift h (algebraMap _ _ s) = dehomogenize h s :=
  IsLocalization.Away.lift_eq _ _ s

/-- `(S_{X_c})_0 → k[x, y]/(y^2 - p(x))`, `a/X_c^n ↦ a(x, 1, y)`. -/
@[expose]
noncomputable def chartToAffine (h : ChartData f o c p) :
    ChartRing f c →+* HyperellipticCoordRing p :=
  (chartLift h).comp (algebraMap (ChartRing f c) (Localization.Away (var f c)))

theorem chartToAffine_mk (h : ChartData f o c p) (n : ℕ) (s : HomogeneousCoordRing f)
    (hs : s ∈ grading f (n • 1)) :
    chartToAffine h (HomogeneousLocalization.Away.mk (grading f) (var_mem_one f h.weight_c) n s
      hs) = dehomogenize h s := by
  have h1 : (HomogeneousLocalization.Away.mk (grading f) (var_mem_one f h.weight_c) n s hs).val *
      algebraMap _ (Localization.Away (var f c)) (var f c ^ n) =
      algebraMap _ (Localization.Away (var f c)) s := by
    rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk'_apply]
    exact IsLocalization.mk'_spec _ s _
  have h2 := congrArg (chartLift h) h1
  rw [map_mul, chartLift_algebraMap, chartLift_algebraMap, map_pow, dehomogenize_var,
    chartValues_c, one_pow, mul_one] at h2
  exact h2

/-- `1/X_c` in `S_{X_c}`. -/
@[expose]
noncomputable def invVar (f : k[X]) (c : Fin 3) : Localization.Away (var f c) :=
  IsLocalization.mk' _ (1 : HomogeneousCoordRing f) ⟨var f c, Submonoid.mem_powers _⟩

theorem invVar_mul (f : k[X]) (c : Fin 3) :
    invVar f c * algebraMap _ (Localization.Away (var f c)) (var f c) = 1 := by
  have := IsLocalization.mk'_spec (Localization.Away (var f c)) (1 : HomogeneousCoordRing f)
    ⟨var f c, Submonoid.mem_powers _⟩
  rw [map_one] at this
  exact this

theorem localization_mk_eq (f : k[X]) (c : Fin 3) (n : ℕ) (s : HomogeneousCoordRing f)
    (hn : var f c ^ n ∈ Submonoid.powers (var f c)) :
    Localization.mk s ⟨var f c ^ n, hn⟩ =
      invVar f c ^ n * algebraMap _ (Localization.Away (var f c)) s := by
  rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_mul_mk'_one, mul_comm, invVar,
    ← IsLocalization.mk'_pow, one_pow]
  congr 2

theorem val_away_mk (h : ChartData f o c p) (n : ℕ) (s : HomogeneousCoordRing f)
    (hs : s ∈ grading f (n • 1)) :
    algebraMap (ChartRing f c) (Localization.Away (var f c))
      (HomogeneousLocalization.Away.mk (grading f) (var_mem_one f h.weight_c) n s hs) =
      invVar f c ^ n * algebraMap _ (Localization.Away (var f c)) s := by
  rw [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
    localization_mk_eq]

/-- `k → (S_{X_c})_0`. -/
@[expose]
noncomputable def chartStructureMap (f : k[X]) (c : Fin 3) : k →+* ChartRing f c :=
  (HomogeneousLocalization.fromZeroRingHom (grading f) _).comp (algebraMap k (grading f 0))

theorem val_chartStructureMap (f : k[X]) (c : Fin 3) (r : k) :
    algebraMap (ChartRing f c) (Localization.Away (var f c)) (chartStructureMap f c r) =
      algebraMap k (Localization.Away (var f c)) r := by
  rw [HomogeneousLocalization.algebraMap_apply]
  change Localization.mk _ 1 = _
  rw [Localization.mk_one_eq_algebraMap, SetLike.GradeZero.coe_algebraMap,
    ← IsScalarTower.algebraMap_apply]

/-- The coordinate `x = X_o/X_c` on the chart. -/
@[expose]
noncomputable def chartX (h : ChartData f o c p) : ChartRing f c :=
  HomogeneousLocalization.Away.mk (grading f) (var_mem_one f h.weight_c) 1 (var f o)
    (by simpa using var_mem_one f h.weight_o)

/-- The coordinate `y = Y/X_c^{g+1}` on the chart. -/
@[expose]
noncomputable def chartY (h : ChartData f o c p) : ChartRing f c :=
  HomogeneousLocalization.Away.mk (grading f) (var_mem_one f h.weight_c) (genus f + 1)
    (var f 2) (by simpa [smul_eq_mul] using var_mem f 2)

/-- The values `X_i ↦ X_c^{-w_i} X_i` in `S_{X_c}`. -/
@[expose]
noncomputable def scaledVars (f : k[X]) (c : Fin 3) (i : Fin 3) : Localization.Away (var f c) :=
  invVar f c ^ weights (genus f) i * algebraMap _ (Localization.Away (var f c)) (var f i)

theorem aeval_var (f : k[X]) (c : Fin 3) (P : MvPolynomial (Fin 3) k) :
    MvPolynomial.aeval (fun i => algebraMap _ (Localization.Away (var f c)) (var f i)) P =
      algebraMap _ (Localization.Away (var f c)) (Ideal.Quotient.mk (coordIdeal f) P) := by
  let φ := (IsScalarTower.toAlgHom k (HomogeneousCoordRing f)
    (Localization.Away (var f c))).comp (Ideal.Quotient.mkₐ k (coordIdeal f))
  change MvPolynomial.aeval (φ ∘ MvPolynomial.X) P = φ P
  rw [← MvPolynomial.aeval_unique]

theorem aeval_scaledVars (f : k[X]) (c : Fin 3) {n : ℕ} {P : MvPolynomial (Fin 3) k}
    (hP : P.IsWeightedHomogeneous (weights (genus f)) n) :
    MvPolynomial.aeval (scaledVars f c) P =
      invVar f c ^ n *
        algebraMap _ (Localization.Away (var f c)) (Ideal.Quotient.mk (coordIdeal f) P) := by
  rw [← aeval_var, ← aeval_pow_weight_mul _ hP]
  rfl

theorem scaledVars_c (h : ChartData f o c p) : scaledVars f c c = 1 := by
  rw [scaledVars, h.weight_c, pow_one, invVar_mul]

theorem chartY_sq (h : ChartData f o c p) :
    chartY h ^ 2 = eval₂ (chartStructureMap f c) (chartX h) p := by
  apply HomogeneousLocalization.val_injective
  rw [← HomogeneousLocalization.algebraMap_apply, ← HomogeneousLocalization.algebraMap_apply,
    map_pow, hom_eval₂, chartY, chartX, val_away_mk h, val_away_mk h]
  have hψ : (algebraMap (ChartRing f c) (Localization.Away (var f c))).comp
      (chartStructureMap f c) = algebraMap k _ :=
    RingHom.ext (val_chartStructureMap f c)
  rw [hψ]
  have he : MvPolynomial.aeval (scaledVars f c) (equation o c p (2 * genus f + 2)) = 0 := by
    rw [aeval_scaledVars f c (equation_mem _ h.weight_o h.weight_c p)]
    rw [(Ideal.Quotient.eq_zero_iff_mem).mpr (h.ideal_eq ▸ Ideal.subset_span rfl), map_zero,
      mul_zero]
  rw [equation, map_sub, aeval_binaryForm o c p h.natDegree_le _ (scaledVars_c h), map_pow,
    MvPolynomial.aeval_X, sub_eq_zero] at he
  rw [← aeval_def, pow_one]
  convert he using 1
  · rw [scaledVars, weights_two]
  · rw [scaledVars, h.weight_o, pow_one]

/-- `k[x, y]/(y^2 - p(x)) → (S_{X_c})_0`, `x ↦ X_o/X_c`, `y ↦ Y/X_c^{g+1}`. -/
@[expose]
noncomputable def affineToChart (h : ChartData f o c p) :
    HyperellipticCoordRing p →+* ChartRing f c :=
  AdjoinRoot.lift (eval₂RingHom (chartStructureMap f c) (chartX h)) (chartY h) (by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, coe_eval₂RingHom, chartY_sq, sub_self])

theorem affineToChart_algebraMap (h : ChartData f o c p) (r : k) :
    affineToChart h (algebraMap k _ r) = chartStructureMap f c r := by
  rw [IsScalarTower.algebraMap_apply k k[X], AdjoinRoot.algebraMap_eq, affineToChart,
    AdjoinRoot.lift_of, Polynomial.algebraMap_apply, coe_eval₂RingHom, eval₂_C]
  rfl

theorem affineToChart_X (h : ChartData f o c p) :
    affineToChart h (algebraMap k[X] _ Polynomial.X) = chartX h := by
  rw [AdjoinRoot.algebraMap_eq, affineToChart, AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_X]

theorem affineToChart_root (h : ChartData f o c p) :
    affineToChart h (AdjoinRoot.root _) = chartY h := by
  rw [affineToChart, AdjoinRoot.lift_root]

theorem chartToAffine_chartStructureMap (h : ChartData f o c p) (r : k) :
    chartToAffine h (chartStructureMap f c r) = algebraMap k _ r := by
  rw [chartToAffine, RingHom.comp_apply, val_chartStructureMap,
    IsScalarTower.algebraMap_apply k (HomogeneousCoordRing f), chartLift_algebraMap]
  exact (dehomogenize h).commutes r

theorem chartToAffine_affineToChart (h : ChartData f o c p) :
    (chartToAffine h).comp (affineToChart h) = RingHom.id _ := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      have := chartToAffine_chartStructureMap h r
      rw [← affineToChart_algebraMap] at this
      simpa [IsScalarTower.algebraMap_apply k k[X], AdjoinRoot.algebraMap_eq] using this
    · rw [RingHom.comp_apply, RingHom.comp_apply, ← AdjoinRoot.algebraMap_eq,
        affineToChart_X, chartX, chartToAffine_mk, dehomogenize_var, chartValues_o p h.ne h.ne_two]
      rfl
  · rw [RingHom.comp_apply, affineToChart_root, chartY, chartToAffine_mk, dehomogenize_var,
      chartValues_two p h.ne_two']
    rfl

theorem affineToChart_chartToAffine (h : ChartData f o c p) :
    (affineToChart h).comp (chartToAffine h) = RingHom.id _ := by
  refine RingHom.ext fun u => ?_
  obtain ⟨n, s, hs, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grading f) (var_mem_one f h.weight_c) u
  rw [RingHom.comp_apply, chartToAffine_mk, RingHom.id_apply]
  obtain ⟨P, hP, rfl⟩ := hs
  have hP' : P.IsWeightedHomogeneous (weights (genus f)) n := by
    simpa [smul_eq_mul] using hP
  refine HomogeneousLocalization.val_injective _ (?_ : algebraMap (ChartRing f c)
    (Localization.Away (var f c)) (affineToChart h (dehomogenize h
      (Ideal.Quotient.mk (coordIdeal f) P))) = _)
  refine Eq.trans ?_ (val_away_mk h n _ _).symm
  refine Eq.trans ?_ (aeval_scaledVars f c hP')
  change ((algebraMap (ChartRing f c) (Localization.Away (var f c))).comp
    ((affineToChart h).comp (dehomogenize h).toRingHom)) (Ideal.Quotient.mk (coordIdeal f) P) = _
  have key : ((algebraMap (ChartRing f c) (Localization.Away (var f c))).comp
      ((affineToChart h).comp (dehomogenize h).toRingHom)).comp
        (Ideal.Quotient.mk (coordIdeal f)) =
      (MvPolynomial.aeval (scaledVars f c)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change algebraMap _ _ (affineToChart h (dehomogenize h (algebraMap k _ r))) =
        MvPolynomial.aeval (scaledVars f c) (MvPolynomial.C r)
      rw [AlgHom.commutes, affineToChart_algebraMap, val_chartStructureMap, MvPolynomial.aeval_C]
    · intro i
      change algebraMap _ _ (affineToChart h (dehomogenize h (var f i))) =
        MvPolynomial.aeval (scaledVars f c) (MvPolynomial.X i)
      rw [MvPolynomial.aeval_X, dehomogenize_var]
      rcases h.cover i with rfl | rfl | rfl
      · rw [chartValues_o p h.ne h.ne_two, affineToChart_X, chartX, val_away_mk h, scaledVars,
          h.weight_o]
      · rw [chartValues_c, map_one, map_one, scaledVars_c h]
      · rw [chartValues_two p h.ne_two', affineToChart_root, chartY, val_away_mk h, scaledVars,
          weights_two]
  exact congrArg (fun φ => φ P) key

/-- The coordinate ring of the chart `D₊(X_c)` of the projective model is the affine coordinate
ring `k[x, y]/(y^2 - p(x))`. -/
@[expose]
noncomputable def chartEquiv (h : ChartData f o c p) :
    ChartRing f c ≃+* HyperellipticCoordRing p :=
  RingEquiv.ofRingHom (chartToAffine h) (affineToChart h) (chartToAffine_affineToChart h)
    (affineToChart_chartToAffine h)

theorem chartStructureMap_eq (h : ChartData f o c p) :
    chartStructureMap f c = (chartEquiv h).symm.toRingHom.comp (algebraMap k _) := by
  refine RingHom.ext fun r => ?_
  exact (affineToChart_algebraMap h r).symm

theorem basicOpen_ι_toSpecField (h : ChartData f o c p) :
    (Proj.basicOpen (grading f) (var f c)).ι ≫ toSpecField f =
      (Proj.basicOpenIsoSpec (grading f) (var f c) (var_mem_one f h.weight_c)
        Nat.one_pos).hom ≫ Spec.map (CommRingCat.ofHom (chartStructureMap f c)) := by
  have e : (Proj.basicOpen (grading f) (var f c)).ι =
      (Proj.basicOpenIsoSpec (grading f) (var f c) (var_mem_one f h.weight_c)
        Nat.one_pos).hom ≫ Proj.awayι (grading f) (var f c) (var_mem_one f h.weight_c)
          Nat.one_pos := by
    rw [Proj.awayι, Iso.hom_inv_id_assoc]
  rw [e, toSpecField, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rfl

/-- The open immersion `Spec k[x, y]/(y^2 - p(x)) → projectiveModel f` of the chart
`D₊(X_c)`. -/
@[expose]
noncomputable def chart (h : ChartData f o c p) :
    Spec (CommRingCat.of (HyperellipticCoordRing p)) ⟶ projectiveModel f :=
  Spec.map (chartEquiv h).toCommRingCatIso.hom ≫
    Proj.awayι (grading f) (var f c) (var_mem_one f h.weight_c) Nat.one_pos

instance (h : ChartData f o c p) : IsOpenImmersion (chart h) := by
  rw [chart]
  infer_instance

theorem chart_toSpecField (h : ChartData f o c p) :
    chart h ≫ toSpecField f =
      Spec.map (CommRingCat.ofHom (algebraMap k (HyperellipticCoordRing p))) := by
  rw [chart, toSpecField, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  ext r
  exact (chartToAffine_chartStructureMap h r)

theorem smooth_basicOpen_ι_toSpecField (h : ChartData f o c p)
    (hs : Algebra.Smooth k (HyperellipticCoordRing p)) :
    Smooth ((Proj.basicOpen (grading f) (var f c)).ι ≫ toSpecField f) := by
  have hS : Smooth (Spec.map (CommRingCat.ofHom (chartStructureMap f c))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)
      (φ := CommRingCat.ofHom (chartStructureMap f c)), CommRingCat.hom_ofHom,
      chartStructureMap_eq h]
    exact RingHom.Smooth.respectsIso.1 _ _ (RingHom.smooth_algebraMap.mpr hs)
  rw [basicOpen_ι_toSpecField h]
  infer_instance

/-- The chart `D₊(Z)`, `Spec k[x, y]/(y^2 - f(x)) → projectiveModel f`. -/
@[expose]
noncomputable def affineChart (f : k[X]) :
    Spec (CommRingCat.of (HyperellipticCoordRing f)) ⟶ projectiveModel f :=
  chart (chartData_finite f)

/-- The chart `D₊(X)`, `Spec k[x', w]/(w^2 - x'^N f(1/x')) → projectiveModel f`. -/
@[expose]
noncomputable def affineChartAtInfinity (f : k[X]) :
    Spec (CommRingCat.of (HyperellipticCoordRing (reflect (2 * genus f + 2) f))) ⟶
      projectiveModel f :=
  chart (chartData_infinite f)

theorem adjoin_range_var (f : k[X]) :
    Algebra.adjoin (grading f 0) (Set.range (var f)) = ⊤ := by
  have key : ∀ P : MvPolynomial (Fin 3) k, Ideal.Quotient.mk (coordIdeal f) P ∈
      Algebra.adjoin (grading f 0) (Set.range (var f)) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a =>
      have := Subalgebra.algebraMap_mem (Algebra.adjoin (grading f 0) (Set.range (var f)))
        (⟨_, mk_mem_quotientGrading _ _ (MvPolynomial.isWeightedHomogeneous_C
          (weights (genus f)) a)⟩ : grading f 0)
      rwa [SetLike.GradeZero.algebraMap_apply] at this
    | add P Q hP hQ => rw [map_add]; exact Subalgebra.add_mem _ hP hQ
    | mul_X P i hP =>
      rw [map_mul]
      exact Subalgebra.mul_mem _ hP (Algebra.subset_adjoin ⟨i, rfl⟩)
  refine eq_top_iff.mpr fun s _ => ?_
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective s
  exact key P

theorem var_two_mem (f : k[X]) (x : ProjectiveSpectrum (grading f))
    (h0 : var f 0 ∈ x.asHomogeneousIdeal) (h1 : var f 1 ∈ x.asHomogeneousIdeal) :
    var f 2 ∈ x.asHomogeneousIdeal := by
  have hrel : var f 2 ^ 2 = Ideal.Quotient.mk _ (binaryForm 0 1 f (2 * genus f + 2)) := by
    rw [var, ← map_pow, Ideal.Quotient.eq]
    exact Ideal.subset_span rfl
  have hF : Ideal.Quotient.mk (coordIdeal f) (binaryForm 0 1 f (2 * genus f + 2)) ∈
      x.asHomogeneousIdeal.toIdeal := by
    rw [binaryForm, map_sum]
    refine Ideal.sum_mem _ fun i hi => ?_
    rw [map_mul, map_mul, map_pow, map_pow]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · refine Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ h1 _ (by omega))
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ h0 _ hi0))
  rw [← hrel] at hF
  exact x.isPrime.mem_of_pow_mem 2 hF

/-- The two affine charts cover the projective model. -/
theorem iSup_chart_eq_top (f : k[X]) :
    Proj.basicOpen (grading f) (var f 1) ⊔ Proj.basicOpen (grading f) (var f 0) = ⊤ := by
  have htop := Proj.iSup_basicOpen_eq_top' (grading f) (var f)
    (fun i => ⟨_, var_mem f i⟩) (adjoin_range_var f)
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : x ∈ ⨆ i, Proj.basicOpen (grading f) (var f i) := by
    rw [htop]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  rw [TopologicalSpace.Opens.mem_sup]
  by_contra hcon
  push Not at hcon
  obtain ⟨hz, hx0⟩ := hcon
  rw [Proj.mem_basicOpen, not_not] at hz hx0
  rw [Proj.mem_basicOpen] at hi
  fin_cases i
  · exact hi hx0
  · exact hi hz
  · exact hi (var_two_mem f x hx0 hz)

/-- **The projective model is smooth over `k`** when `2 ≠ 0` in `k` and `f` is separable of
positive degree. -/
theorem smooth_toSpecField {f : k[X]} (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hdeg : 0 < f.natDegree) : Smooth (toSpecField f) := by
  have : IsZariskiLocalAtSource @Smooth :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Smooth) (f := toSpecField f)
    ![Proj.basicOpen (grading f) (var f 1), Proj.basicOpen (grading f) (var f 0)]
    (by
      refine eq_top_iff.mpr fun x _ => ?_
      have hx : x ∈ Proj.basicOpen (grading f) (var f 1) ⊔ Proj.basicOpen (grading f) (var f 0) :=
        by rw [iSup_chart_eq_top f]; trivial
      rw [TopologicalSpace.Opens.mem_sup] at hx
      rw [TopologicalSpace.Opens.mem_iSup]
      rcases hx with hx | hx
      · exact ⟨0, hx⟩
      · exact ⟨1, hx⟩)]
  intro i
  fin_cases i
  · exact smooth_basicOpen_ι_toSpecField (chartData_finite f)
      (smooth_hyperellipticCoordRing h2 hf)
  · exact smooth_basicOpen_ι_toSpecField (chartData_infinite f)
      (smooth_hyperellipticCoordRing_reflect h2 hf (natDegree_le_two_mul_genus_add_two f)
        (two_mul_genus_add_two_le f hdeg))

end Hyperelliptic

end ArithmeticOfJacobiPolynomials
