/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticCurve
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic

/-!
# The two-chart Čech complex of the structure sheaf of the hyperelliptic model

Let `k` be a field, `f ∈ k[x]`, `g = genus f = ⌊(deg f - 1)/2⌋` and `N = 2g + 2`. The projective
model `projectiveModel f` (`ArithmeticOfJacobiPolynomials.Geometry.HyperellipticProjective`) is
covered by the
charts
* `D₊(Z) = Spec A_Z`, `A_Z = k[x, y]/(y^2 - f(x))` (`HyperellipticCoordRing f`), and
* `D₊(X) = Spec A_X`, `A_X = k[x', w]/(w^2 - x'^N f(1/x'))`
  (`HyperellipticCoordRing (reflect N f)`),

glued along `x' = 1/x`, `w = y/x^{g+1}`. The overlap ring is
`A_{ZX} = k[x, x⁻¹, y]/(y^2 - f(x))` (`OverlapRing f`, built over the Laurent polynomials
`k[T;T⁻¹]`), and the two restriction maps are
* `cechRestrictFinite f : A_Z → A_{ZX}`, `x ↦ T`, `y ↦ y`;
* `cechRestrictInfinite f : A_X → A_{ZX}`, `x' ↦ T⁻¹`, `w ↦ T^{-(g+1)} y`.

The two-term Čech complex of `𝒪` for this cover is
`cechDifferential f : A_Z × A_X → A_{ZX}`, `(a, b) ↦ a|_{ZX} - b|_{ZX}`; we put
`CechH0 f = ker` and `CechH1 f = coker` (as `k`-vector spaces) and prove, for every `f`:

* `finrank_cechH0`: `dim_k CechH0 f = 1` (the kernel is the constants `k`);
* `finrank_cechH1`: `dim_k CechH1 f = ⌊(deg f - 1)/2⌋`; explicitly
  `cechH1Equiv : CechH1 f ≃ₗ[k] (Fin g → k)` reads off the coefficients of
  `x^{-1} y, …, x^{-g} y` (`cechFunctional`), whose classes form a basis of `CechH1 f`.

`isLocalization_overlapRing` shows that `A_{ZX}` is the localisation `A_Z[1/x]`, with
`cechRestrictFinite f` the localisation map.

The computation uses the `k[T;T⁻¹]`-basis `1, y` of `A_{ZX}` (`quadCoord`): the image of `A_Z`
is spanned by `x^i` and `x^i y` with `i ≥ 0`, the image of `A_X` by `x^{-i}` (`i ≥ 0`) and
`x^{-i} y` (`i ≥ g + 1`).

## Cohomology comparison

The overlap sections and restriction maps are identified in `HyperellipticOverlap` and
`HyperellipticCechSections`. The derived-functor comparison is proved in
`HyperellipticGenusComparison`, using Stacks' `AlgebraicGeometry.structureSheafCohomology`
and `AlgebraicGeometry.genus` (Tag 0BY7).
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace Hyperelliptic

open Polynomial
open scoped LaurentPolynomial

universe u

/-! ### The quadratic algebra `B[y]/(y^2 - a)` and its coordinates -/

section Quad

variable {B : Type*} [CommRing B] [Nontrivial B]

/-- The ring `B[y]/(y^2 - a)`. -/
abbrev QuadRing (a : B) : Type _ := AdjoinRoot (X ^ 2 - C a : B[X])

omit [Nontrivial B] in
theorem monic_quad (a : B) : (X ^ 2 - C a : B[X]).Monic :=
  monic_X_pow_sub_C a two_ne_zero

/-- The coordinate of `y^j` in `B[y]/(y^2 - a) = B ⊕ B y` (`j = 0, 1`). -/
@[expose]
noncomputable def quadCoord (a : B) (j : ℕ) : QuadRing a →ₗ[B] B :=
  (lcoeff B j).comp (AdjoinRoot.modByMonicHom (monic_quad a))

theorem modByMonic_quad (a p q : B) :
    (C p + C q * X) %ₘ (X ^ 2 - C a) = C p + C q * X := by
  rw [modByMonic_eq_self_iff (monic_quad a), degree_X_pow_sub_C two_pos]
  refine ((degree_add_le _ _).trans
    (max_le (degree_C_le.trans zero_le_one) (degree_C_mul_X_le q))).trans_lt ?_
  exact WithBot.coe_lt_coe.mpr one_lt_two

omit [Nontrivial B] in
theorem of_add_mul_root_eq_mk (a p q : B) :
    AdjoinRoot.of (X ^ 2 - C a) p + AdjoinRoot.of _ q * AdjoinRoot.root _ =
      AdjoinRoot.mk (X ^ 2 - C a : B[X]) (C p + C q * X) := by
  rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X]

theorem quadCoord_zero (a p q : B) :
    quadCoord a 0 (AdjoinRoot.of _ p + AdjoinRoot.of _ q * AdjoinRoot.root _) = p := by
  rw [of_add_mul_root_eq_mk, quadCoord, LinearMap.comp_apply, AdjoinRoot.modByMonicHom_mk,
    modByMonic_quad, lcoeff_apply]
  simp

theorem quadCoord_one (a p q : B) :
    quadCoord a 1 (AdjoinRoot.of _ p + AdjoinRoot.of _ q * AdjoinRoot.root _) = q := by
  rw [of_add_mul_root_eq_mk, quadCoord, LinearMap.comp_apply, AdjoinRoot.modByMonicHom_mk,
    modByMonic_quad, lcoeff_apply]
  simp

theorem quadCoord_zero_of (a p : B) : quadCoord a 0 (AdjoinRoot.of _ p) = p := by
  simpa using quadCoord_zero a p 0

theorem quadCoord_one_of (a p : B) : quadCoord a 1 (AdjoinRoot.of _ p) = 0 := by
  simpa using quadCoord_one a p 0

theorem quadCoord_zero_of_mul_root (a q : B) :
    quadCoord a 0 (AdjoinRoot.of _ q * AdjoinRoot.root _) = 0 := by
  simpa using quadCoord_zero a 0 q

theorem quadCoord_one_of_mul_root (a q : B) :
    quadCoord a 1 (AdjoinRoot.of _ q * AdjoinRoot.root _) = q := by
  simpa using quadCoord_one a 0 q

/-- Every element of `B[y]/(y^2 - a)` is `p + q y` with `p, q ∈ B` its coordinates. -/
theorem eq_quadCoord (a : B) (z : QuadRing a) :
    z = AdjoinRoot.of _ (quadCoord a 0 z) + AdjoinRoot.of _ (quadCoord a 1 z) *
      AdjoinRoot.root _ := by
  obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective z
  have hlt : (P %ₘ (X ^ 2 - C a)).degree < ((2 : ℕ) : WithBot ℕ) := by
    have := degree_modByMonic_lt P (monic_quad a)
    rwa [degree_X_pow_sub_C two_pos] at this
  have hP : P %ₘ (X ^ 2 - C a) =
      C ((P %ₘ (X ^ 2 - C a)).coeff 0) + C ((P %ₘ (X ^ 2 - C a)).coeff 1) * X := by
    ext n
    rcases n with _ | _ | n
    · simp
    · simp
    · rw [coeff_eq_zero_of_degree_lt
        (hlt.trans_le (WithBot.coe_le_coe.mpr (show 2 ≤ n + 1 + 1 by omega)))]
      simp
  conv_lhs => rw [← AdjoinRoot.mk_leftInverse (monic_quad a) (AdjoinRoot.mk _ P)]
  rw [of_add_mul_root_eq_mk, quadCoord, quadCoord, LinearMap.comp_apply, LinearMap.comp_apply,
    AdjoinRoot.modByMonicHom_mk, lcoeff_apply, lcoeff_apply, ← hP]

theorem quad_ext {a : B} {z z' : QuadRing a} (h0 : quadCoord a 0 z = quadCoord a 0 z')
    (h1 : quadCoord a 1 z = quadCoord a 1 z') : z = z' := by
  rw [eq_quadCoord a z, eq_quadCoord a z', h0, h1]

end Quad

/-! ### Laurent polynomial facts -/

section Laurent

variable {k : Type u} [Field k]

theorem coeff_toLaurent_of_neg (p : k[X]) {n : ℤ} (hn : n < 0) :
    (toLaurent p).coeff n = 0 := by
  rw [← Finsupp.notMem_support_iff, LaurentPolynomial.support_coeff_toLaurent, Finset.mem_map]
  rintro ⟨m, -, rfl⟩
  exact absurd hn (not_lt.mpr (Int.natCast_nonneg m))

theorem coeff_C_mul_T (a : k) (n m : ℤ) :
    (LaurentPolynomial.C a * LaurentPolynomial.T n : k[T;T⁻¹]).coeff m =
      if n = m then a else 0 := by
  rw [← LaurentPolynomial.smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply,
    LaurentPolynomial.T_apply]
  split_ifs <;> simp

theorem coeff_toLaurent_natCast (p : k[X]) (m : ℕ) :
    (toLaurent p).coeff (m : ℤ) = p.coeff m := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, Polynomial.coeff_add]
  | monomial n r =>
    rw [Polynomial.toLaurent_C_mul_T, coeff_C_mul_T, coeff_monomial]
    by_cases h : n = m
    · subst h
      simp
    · have h' : (n : ℤ) ≠ m := by exact_mod_cast h
      rw [ite_eq_right h, ite_eq_right h']

theorem toLaurent_reflect (N : ℕ) (p : k[X]) (hp : p.natDegree ≤ N) :
    toLaurent (reflect N p) =
      LaurentPolynomial.invert (toLaurent p) * LaurentPolynomial.T (N : ℤ) := by
  refine induction_with_natDegree_le
    (fun p => toLaurent (reflect N p) =
      LaurentPolynomial.invert (toLaurent p) * LaurentPolynomial.T (N : ℤ)) N ?_ ?_ ?_ p hp
  · simp
  · intro n r _ hn
    rw [reflect_C_mul_X_pow, revAt_le hn, toLaurent_C_mul_X_pow, toLaurent_C_mul_X_pow, map_mul,
      LaurentPolynomial.invert_C, LaurentPolynomial.invert_T, mul_assoc,
      ← LaurentPolynomial.T_add, Nat.cast_sub hn, neg_add_eq_sub]
  · intro p q _ _ hp hq
    beta_reduce at hp hq ⊢
    rw [reflect_add, map_add, map_add, map_add, add_mul, hp, hq]

theorem invert_toLaurent_reflect (N : ℕ) (p : k[X]) (hp : p.natDegree ≤ N) :
    LaurentPolynomial.invert (toLaurent (reflect N p)) =
      toLaurent p * LaurentPolynomial.T (-(N : ℤ)) := by
  rw [toLaurent_reflect N p hp, map_mul, LaurentPolynomial.invert_T,
    LaurentPolynomial.involutive_invert (toLaurent p)]

/-- If `p(T) = p'(T⁻¹)` then `p` and `p'` are the same constant. -/
theorem eq_C_of_toLaurent_eq_invert {p p' : k[X]}
    (h : toLaurent p = LaurentPolynomial.invert (toLaurent p')) :
    p = C (p.coeff 0) ∧ p' = C (p.coeff 0) := by
  have h' : toLaurent p' = LaurentPolynomial.invert (toLaurent p) := by
    rw [h, LaurentPolynomial.involutive_invert (toLaurent p')]
  have key : ∀ {u v : k[X]}, toLaurent u = LaurentPolynomial.invert (toLaurent v) →
      u = C (u.coeff 0) := by
    intro u v huv
    ext m
    rcases m with _ | m
    · simp
    · rw [coeff_C, ite_eq_right (Nat.succ_ne_zero m), ← coeff_toLaurent_natCast, huv,
        LaurentPolynomial.invert_apply, coeff_toLaurent_of_neg]
      omega
  have h0 : p'.coeff 0 = p.coeff 0 := by
    have e1 := coeff_toLaurent_natCast p' 0
    have e2 := coeff_toLaurent_natCast p 0
    rw [h', LaurentPolynomial.invert_apply, Nat.cast_zero, neg_zero] at e1
    rw [Nat.cast_zero] at e2
    rw [← e1, e2]
  refine ⟨key h, ?_⟩
  rw [← h0]
  exact key h'

end Laurent

/-! ### The Čech complex -/

variable {k : Type u} [Field k] (f : k[X])

/-- The ring `k[x, x⁻¹, y]/(y^2 - f(x))` of the overlap `D₊(Z) ∩ D₊(X)`. -/
abbrev OverlapRing : Type u := QuadRing (toLaurent f : k[T;T⁻¹])

/-- `k[x] → k[x, x⁻¹] → A_{ZX}`. -/
@[expose]
noncomputable def overlapFinite : k[X] →ₐ[k] OverlapRing f :=
  (IsScalarTower.toAlgHom k k[T;T⁻¹] (OverlapRing f)).comp toLaurentAlg

/-- `k[x'] → A_{ZX}`, `x' ↦ x⁻¹`. -/
@[expose]
noncomputable def overlapInfinite : k[X] →ₐ[k] OverlapRing f :=
  (IsScalarTower.toAlgHom k k[T;T⁻¹] (OverlapRing f)).comp
    ((LaurentPolynomial.invert : k[T;T⁻¹] ≃ₐ[k] k[T;T⁻¹]).toAlgHom.comp toLaurentAlg)

theorem overlapFinite_apply (p : k[X]) :
    overlapFinite f p = AdjoinRoot.of _ (toLaurent p) := rfl

theorem overlapInfinite_apply (p : k[X]) :
    overlapInfinite f p = AdjoinRoot.of _ (LaurentPolynomial.invert (toLaurent p)) := rfl

theorem T_neg_genus_sq :
    (LaurentPolynomial.T (-((genus f : ℤ) + 1)) : k[T;T⁻¹]) ^ 2 =
      LaurentPolynomial.T (-((2 * genus f + 2 : ℕ) : ℤ)) := by
  rw [sq, ← LaurentPolynomial.T_add]
  congr 1
  push_cast
  ring

/-- The restriction `A_Z → A_{ZX}`: `x ↦ x`, `y ↦ y`. -/
@[expose]
noncomputable def cechRestrictFinite : HyperellipticCoordRing f →ₐ[k] OverlapRing f :=
  AdjoinRoot.liftAlgHom (X ^ 2 - C f) (overlapFinite f) (AdjoinRoot.root _) (by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, root_sq_eq_of]
    exact sub_self _)

/-- The restriction `A_X → A_{ZX}`: `x' ↦ x⁻¹`, `w ↦ x^{-(g+1)} y`. -/
@[expose]
noncomputable def cechRestrictInfinite :
    HyperellipticCoordRing (reflect (2 * genus f + 2) f) →ₐ[k] OverlapRing f :=
  AdjoinRoot.liftAlgHom (X ^ 2 - C (reflect (2 * genus f + 2) f)) (overlapInfinite f)
    (AdjoinRoot.of _ (LaurentPolynomial.T (-((genus f : ℤ) + 1))) * AdjoinRoot.root _) (by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, mul_pow, root_sq_eq_of, ← map_pow, ← map_mul,
      sub_eq_zero, T_neg_genus_sq]
    change _ = AdjoinRoot.of _ (LaurentPolynomial.invert
      (toLaurent (reflect (2 * genus f + 2) f)))
    rw [invert_toLaurent_reflect _ _ (natDegree_le_two_mul_genus_add_two f), mul_comm])

theorem cechRestrictFinite_of (p : k[X]) :
    cechRestrictFinite f (AdjoinRoot.of _ p) = AdjoinRoot.of _ (toLaurent p) := by
  rw [cechRestrictFinite, AdjoinRoot.liftAlgHom_of, overlapFinite_apply]

theorem cechRestrictFinite_root :
    cechRestrictFinite f (AdjoinRoot.root _) = AdjoinRoot.root _ := by
  rw [cechRestrictFinite, AdjoinRoot.liftAlgHom_root]

theorem cechRestrictInfinite_of (p : k[X]) :
    cechRestrictInfinite f (AdjoinRoot.of _ p) =
      AdjoinRoot.of _ (LaurentPolynomial.invert (toLaurent p)) := by
  rw [cechRestrictInfinite, AdjoinRoot.liftAlgHom_of, overlapInfinite_apply]

theorem cechRestrictInfinite_of_mul_root (q : k[X]) :
    cechRestrictInfinite f (AdjoinRoot.of _ q * AdjoinRoot.root _) =
      AdjoinRoot.of _ (LaurentPolynomial.invert (toLaurent (q * X ^ (genus f + 1)))) *
        AdjoinRoot.root _ := by
  rw [map_mul (cechRestrictInfinite f), cechRestrictInfinite_of]
  rw [cechRestrictInfinite, AdjoinRoot.liftAlgHom_root]
  simp only [map_mul, toLaurent_X_pow, LaurentPolynomial.invert_T, Nat.cast_add, Nat.cast_one]
  ring

theorem quadCoord_cechRestrictFinite (a : HyperellipticCoordRing f) (j : ℕ) (hj : j ≤ 1) :
    quadCoord _ j (cechRestrictFinite f a) = toLaurent (quadCoord _ j a) := by
  conv_lhs => rw [eq_quadCoord _ a]
  rw [map_add (cechRestrictFinite f), map_mul (cechRestrictFinite f), cechRestrictFinite_of,
    cechRestrictFinite_of, cechRestrictFinite_root]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · rw [quadCoord_zero]
  · rw [quadCoord_one]

theorem quadCoord_zero_cechRestrictInfinite
    (b : HyperellipticCoordRing (reflect (2 * genus f + 2) f)) :
    quadCoord _ 0 (cechRestrictInfinite f b) =
      LaurentPolynomial.invert (toLaurent (quadCoord _ 0 b)) := by
  conv_lhs => rw [eq_quadCoord _ b]
  rw [map_add (cechRestrictInfinite f), cechRestrictInfinite_of,
    cechRestrictInfinite_of_mul_root, quadCoord_zero]

theorem quadCoord_one_cechRestrictInfinite
    (b : HyperellipticCoordRing (reflect (2 * genus f + 2) f)) :
    quadCoord _ 1 (cechRestrictInfinite f b) =
      LaurentPolynomial.invert (toLaurent (quadCoord _ 1 b * X ^ (genus f + 1))) := by
  conv_lhs => rw [eq_quadCoord _ b]
  rw [map_add (cechRestrictInfinite f), cechRestrictInfinite_of,
    cechRestrictInfinite_of_mul_root, quadCoord_one]

/-- **The Čech differential** `A_Z × A_X → A_{ZX}`, `(a, b) ↦ a|_{ZX} - b|_{ZX}`, of the
structure sheaf for the cover of the model by the charts `D₊(Z)` and `D₊(X)`. -/
@[expose]
noncomputable def cechDifferential :
    (HyperellipticCoordRing f × HyperellipticCoordRing (reflect (2 * genus f + 2) f)) →ₗ[k]
      OverlapRing f :=
  (cechRestrictFinite f).toLinearMap ∘ₗ LinearMap.fst k _ _ -
    (cechRestrictInfinite f).toLinearMap ∘ₗ LinearMap.snd k _ _

theorem cechDifferential_apply (a : HyperellipticCoordRing f)
    (b : HyperellipticCoordRing (reflect (2 * genus f + 2) f)) :
    cechDifferential f (a, b) = cechRestrictFinite f a - cechRestrictInfinite f b := rfl

/-- The Čech `H⁰` of the structure sheaf for the two-chart cover: the kernel of the Čech
differential. -/
abbrev CechH0 : Type u := LinearMap.ker (cechDifferential f)

/-- The Čech `H¹` of the structure sheaf for the two-chart cover: the cokernel of the Čech
differential. -/
abbrev CechH1 : Type u := OverlapRing f ⧸ LinearMap.range (cechDifferential f)

/-! ### The overlap ring is the localisation `A_Z[1/x]` -/

theorem cechRestrictFinite_injective : Function.Injective (cechRestrictFinite f) := by
  intro a b h
  refine quad_ext (toLaurent_injective ?_) (toLaurent_injective ?_)
  · rw [← quadCoord_cechRestrictFinite f a 0 (Nat.zero_le 1),
      ← quadCoord_cechRestrictFinite f b 0 (Nat.zero_le 1), h]
  · rw [← quadCoord_cechRestrictFinite f a 1 le_rfl, ← quadCoord_cechRestrictFinite f b 1 le_rfl,
      h]

theorem cechRestrictFinite_X_pow (n : ℕ) :
    cechRestrictFinite f (AdjoinRoot.of _ X ^ n) = AdjoinRoot.of _ (LaurentPolynomial.T n) := by
  rw [map_pow, cechRestrictFinite_of, toLaurent_X, ← map_pow, LaurentPolynomial.T_pow, mul_one]

/-- **`A_{ZX}` is the localisation `A_Z[1/x]`**, with `cechRestrictFinite` the localisation
map: the overlap ring is the ring of functions on the basic open `D(x)` of the chart `D₊(Z)`. -/
theorem isLocalization_overlapRing :
    @IsLocalization.Away _ _ (AdjoinRoot.of (X ^ 2 - C f) X) (OverlapRing f) _
      (cechRestrictFinite f).toRingHom.toAlgebra := by
  let _ := (cechRestrictFinite f).toRingHom.toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    change IsUnit (cechRestrictFinite f (AdjoinRoot.of _ X ^ n))
    rw [cechRestrictFinite_X_pow]
    exact (LaurentPolynomial.isUnit_T _).map _
  · intro z
    obtain ⟨n, u, hu⟩ := LaurentPolynomial.exists_T_pow (quadCoord _ 0 z)
    obtain ⟨m, v, hv⟩ := LaurentPolynomial.exists_T_pow (quadCoord _ 1 z)
    refine ⟨⟨AdjoinRoot.of _ (u * X ^ m) + AdjoinRoot.of _ (v * X ^ n) * AdjoinRoot.root _,
      ⟨_, n + m, rfl⟩⟩, ?_⟩
    change z * cechRestrictFinite f (AdjoinRoot.of _ X ^ (n + m)) =
      cechRestrictFinite f (AdjoinRoot.of _ (u * X ^ m) +
        AdjoinRoot.of _ (v * X ^ n) * AdjoinRoot.root _)
    rw [cechRestrictFinite_X_pow, map_add, map_mul (cechRestrictFinite f), cechRestrictFinite_of,
      cechRestrictFinite_of, cechRestrictFinite_root]
    simp only [map_mul, toLaurent_X_pow, hu, hv, Nat.cast_add, LaurentPolynomial.T_add]
    conv_lhs => rw [eq_quadCoord _ z]
    ring
  · intro a b h
    exact ⟨1, by rw [cechRestrictFinite_injective f h]⟩

/-! ### `H¹` -/

/-- The coefficients of `x^{-1} y, …, x^{-g} y`. -/
@[expose]
noncomputable def cechFunctional : OverlapRing f →ₗ[k] (Fin (genus f) → k) where
  toFun z i := (quadCoord _ 1 z).coeff (-(((i : ℕ) : ℤ) + 1))
  map_add' z z' := by
    ext i
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Pi.add_apply]
  map_smul' c z := by
    ext i
    simp only [LinearMap.map_smul_of_tower, AddMonoidAlgebra.coeff_smul_apply, Pi.smul_apply,
      RingHom.id_apply]

theorem cechFunctional_apply (z : OverlapRing f) (i : Fin (genus f)) :
    cechFunctional f z i = (quadCoord _ 1 z).coeff (-(((i : ℕ) : ℤ) + 1)) := rfl

/-- The classes `x^{-i} y`, `1 ≤ i ≤ g`. -/
@[expose]
noncomputable def cechSection : (Fin (genus f) → k) →ₗ[k] OverlapRing f :=
  Fintype.linearCombination k fun i : Fin (genus f) =>
    AdjoinRoot.of _ (LaurentPolynomial.T (-(((i : ℕ) : ℤ) + 1))) * AdjoinRoot.root _

theorem of_smul_mul_root (a : k) (t : k[T;T⁻¹]) :
    AdjoinRoot.of (X ^ 2 - C (toLaurent f)) (a • t) * AdjoinRoot.root _ =
      a • (AdjoinRoot.of _ t * AdjoinRoot.root _ : OverlapRing f) := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc,
    IsScalarTower.algebraMap_apply k k[T;T⁻¹] (OverlapRing f), AdjoinRoot.algebraMap_eq]

theorem cechFunctional_cechSection : cechFunctional f ∘ₗ cechSection f = LinearMap.id := by
  refine (Pi.basisFun k (Fin (genus f))).ext fun j => ?_
  ext i
  rw [LinearMap.comp_apply, Pi.basisFun_apply, cechSection, Fintype.linearCombination_apply_single,
    one_smul, cechFunctional_apply, quadCoord_one_of_mul_root, LaurentPolynomial.T_apply,
    LinearMap.id_apply, Pi.single_apply]
  by_cases h : i = j
  · subst h
    simp
  · have h' : -(((j : ℕ) : ℤ) + 1) ≠ -(((i : ℕ) : ℤ) + 1) := by
      intro h'
      apply h
      ext
      omega
    rw [ite_eq_right h, ite_eq_right h']

theorem cechFunctional_surjective : Function.Surjective (cechFunctional f) := fun c =>
  ⟨cechSection f c, by
    rw [← LinearMap.comp_apply, cechFunctional_cechSection, LinearMap.id_apply]⟩

theorem cechFunctional_cechRestrictFinite (a : HyperellipticCoordRing f) :
    cechFunctional f (cechRestrictFinite f a) = 0 := by
  ext i
  rw [cechFunctional_apply, quadCoord_cechRestrictFinite f a 1 le_rfl,
    coeff_toLaurent_of_neg _ (show -(((i : ℕ) : ℤ) + 1) < 0 by omega), Pi.zero_apply]

theorem cechFunctional_cechRestrictInfinite
    (b : HyperellipticCoordRing (reflect (2 * genus f + 2) f)) :
    cechFunctional f (cechRestrictInfinite f b) = 0 := by
  ext i
  have hi := i.2
  rw [cechFunctional_apply, quadCoord_one_cechRestrictInfinite, LaurentPolynomial.invert_apply,
    neg_neg, show ((i : ℕ) : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) by push_cast; ring,
    coeff_toLaurent_natCast, coeff_mul_X_pow',
    ite_eq_right (show ¬(genus f + 1 ≤ (i : ℕ) + 1) by omega), Pi.zero_apply]

theorem range_le_ker_cechFunctional :
    LinearMap.range (cechDifferential f) ≤ LinearMap.ker (cechFunctional f) := by
  rintro _ ⟨⟨a, b⟩, rfl⟩
  rw [LinearMap.mem_ker, cechDifferential_apply, map_sub, cechFunctional_cechRestrictFinite,
    cechFunctional_cechRestrictInfinite, sub_zero]

theorem of_mem_range (n : ℤ) (a : k) :
    AdjoinRoot.of _ (LaurentPolynomial.C a * LaurentPolynomial.T n) ∈
      LinearMap.range (cechDifferential f) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · refine ⟨(AdjoinRoot.of _ (C a * X ^ m), 0), ?_⟩
    rw [cechDifferential_apply, map_zero, sub_zero, cechRestrictFinite_of,
      toLaurent_C_mul_X_pow]
  · refine ⟨(0, -AdjoinRoot.of _ (C a * X ^ m)), ?_⟩
    rw [cechDifferential_apply, map_zero, map_neg, sub_neg_eq_add, zero_add,
      cechRestrictInfinite_of, toLaurent_C_mul_X_pow, map_mul, LaurentPolynomial.invert_C,
      LaurentPolynomial.invert_T]

theorem of_mul_root_mem_range (n : ℤ) (a : k) (hn : 0 ≤ n ∨ n ≤ -((genus f : ℤ) + 1)) :
    AdjoinRoot.of _ (LaurentPolynomial.C a * LaurentPolynomial.T n) * AdjoinRoot.root _ ∈
      LinearMap.range (cechDifferential f) := by
  rcases hn with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    refine ⟨(AdjoinRoot.of _ (C a * X ^ m) * AdjoinRoot.root _, 0), ?_⟩
    rw [cechDifferential_apply, map_zero, sub_zero, map_mul (cechRestrictFinite f),
      cechRestrictFinite_of, cechRestrictFinite_root, toLaurent_C_mul_X_pow]
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -((m : ℤ) + genus f + 1) :=
      ⟨(-n - genus f - 1).toNat, by omega⟩
    have e : -(((m + (genus f + 1) : ℕ)) : ℤ) = n := by
      rw [hm]
      push_cast
      ring
    refine ⟨(0, -(AdjoinRoot.of _ (C a * X ^ m) * AdjoinRoot.root _)), ?_⟩
    rw [cechDifferential_apply, map_zero, map_neg, sub_neg_eq_add, zero_add,
      cechRestrictInfinite_of_mul_root, mul_assoc (C a), ← pow_add, toLaurent_C_mul_X_pow,
      map_mul LaurentPolynomial.invert, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
      e]

/-- Every element differs from its `cechSection`-part by a coboundary. -/
theorem sub_cechSection_mem_range (z : OverlapRing f) :
    z - cechSection f (cechFunctional f z) ∈ LinearMap.range (cechDifferential f) := by
  let S := (LinearMap.range (cechDifferential f)).comap
    (LinearMap.id - cechSection f ∘ₗ cechFunctional f)
  have hS : ∀ w, w ∈ S ↔ w - cechSection f (cechFunctional f w) ∈
      LinearMap.range (cechDifferential f) := fun w => Iff.rfl
  have h0 : ∀ u : k[T;T⁻¹], AdjoinRoot.of (X ^ 2 - C (toLaurent f)) u ∈ S := by
    intro u
    induction u using LaurentPolynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
    | C_mul_T n a =>
      rw [hS]
      have hΦ : cechFunctional f (AdjoinRoot.of _ (LaurentPolynomial.C a *
          LaurentPolynomial.T n)) = 0 := by
        ext i
        rw [cechFunctional_apply, quadCoord_one_of]
        rfl
      rw [hΦ, map_zero, sub_zero]
      exact of_mem_range f n a
  have h1 : ∀ v : k[T;T⁻¹], AdjoinRoot.of (X ^ 2 - C (toLaurent f)) v * AdjoinRoot.root _ ∈ S := by
    intro v
    induction v using LaurentPolynomial.induction_on' with
    | add p q hp hq => rw [map_add, add_mul]; exact S.add_mem hp hq
    | C_mul_T n a =>
      rw [hS]
      by_cases hn : 0 ≤ n ∨ n ≤ -((genus f : ℤ) + 1)
      · have hΦ : cechFunctional f (AdjoinRoot.of _ (LaurentPolynomial.C a *
            LaurentPolynomial.T n) * AdjoinRoot.root _) = 0 := by
          ext i
          have hi := i.2
          rw [cechFunctional_apply, quadCoord_one_of_mul_root, coeff_C_mul_T,
            ite_eq_right (show ¬(n = -(((i : ℕ) : ℤ) + 1)) by omega)]
          rfl
        rw [hΦ, map_zero, sub_zero]
        exact of_mul_root_mem_range f n a hn
      · obtain ⟨j, hj⟩ : ∃ j : Fin (genus f), n = -(((j : ℕ) : ℤ) + 1) :=
          ⟨⟨(-n - 1).toNat, by omega⟩, show n = -((((-n - 1).toNat : ℕ) : ℤ) + 1) by omega⟩
        have hΦ : cechFunctional f (AdjoinRoot.of _ (LaurentPolynomial.C a *
            LaurentPolynomial.T n) * AdjoinRoot.root _) = Pi.single j a := by
          ext i
          rw [cechFunctional_apply, quadCoord_one_of_mul_root, coeff_C_mul_T, Pi.single_apply]
          by_cases h : i = j
          · subst h
            rw [ite_eq_left hj, ite_eq_left rfl]
          · have h' : n ≠ -(((i : ℕ) : ℤ) + 1) := by
              intro h'
              apply h
              ext
              omega
            rw [ite_eq_right h', ite_eq_right h]
        rw [hΦ, cechSection, Fintype.linearCombination_apply_single, ← hj,
          ← of_smul_mul_root, LaurentPolynomial.smul_eq_C_mul, sub_self]
        exact Submodule.zero_mem _
  rw [← hS, eq_quadCoord _ z]
  exact S.add_mem (h0 _) (h1 _)

theorem range_cechDifferential_eq :
    LinearMap.range (cechDifferential f) = LinearMap.ker (cechFunctional f) := by
  refine le_antisymm (range_le_ker_cechFunctional f) fun z hz => ?_
  have h := sub_cechSection_mem_range f z
  rwa [LinearMap.mem_ker.mp hz, map_zero, sub_zero] at h

/-- `CechH1 f ≃ k^g`, by the coefficients of `x^{-1} y, …, x^{-g} y`. -/
@[expose]
noncomputable def cechH1Equiv : CechH1 f ≃ₗ[k] (Fin (genus f) → k) :=
  (Submodule.quotEquivOfEq _ _ (range_cechDifferential_eq f)).trans
    ((cechFunctional f).quotKerEquivOfSurjective (cechFunctional_surjective f))

/-- **The Čech `H¹` of the structure sheaf of the hyperelliptic model has dimension
`⌊(deg f - 1)/2⌋`.** -/
theorem finrank_cechH1 : Module.finrank k (CechH1 f) = (f.natDegree - 1) / 2 := by
  rw [(cechH1Equiv f).finrank_eq, Module.finrank_fin_fun]
  rfl

/-! ### `H⁰` -/

/-- The constants `k → A_Z × A_X`. -/
@[expose]
noncomputable def cechConstants :
    k →ₗ[k] (HyperellipticCoordRing f × HyperellipticCoordRing (reflect (2 * genus f + 2) f)) :=
  LinearMap.prod (Algebra.linearMap k _) (Algebra.linearMap k _)

theorem algebraMap_hyperellipticCoordRing (p : k[X]) (c : k) :
    algebraMap k (HyperellipticCoordRing p) c = AdjoinRoot.of _ (C c) := by
  rw [IsScalarTower.algebraMap_apply k k[X] (HyperellipticCoordRing p),
    AdjoinRoot.algebraMap_eq, Polynomial.algebraMap_eq]

theorem cechConstants_injective : Function.Injective (cechConstants f) := by
  intro c c' h
  have h1 : algebraMap k (HyperellipticCoordRing f) c =
      algebraMap k (HyperellipticCoordRing f) c' := congrArg Prod.fst h
  rw [algebraMap_hyperellipticCoordRing, algebraMap_hyperellipticCoordRing,
    ← AdjoinRoot.algebraMap_eq] at h1
  exact C_injective (injective_algebraMap_hyperellipticCoordRing f h1)

theorem range_cechConstants :
    LinearMap.range (cechConstants f) = LinearMap.ker (cechDifferential f) := by
  refine le_antisymm ?_ fun ⟨a, b⟩ hab => ?_
  · rintro _ ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    change cechDifferential f (algebraMap k _ c, algebraMap k _ c) = 0
    rw [cechDifferential_apply, AlgHom.commutes, AlgHom.commutes, sub_self]
  · rw [LinearMap.mem_ker, cechDifferential_apply, sub_eq_zero] at hab
    have h0 := congrArg (quadCoord _ 0) hab
    have h1 := congrArg (quadCoord _ 1) hab
    rw [quadCoord_cechRestrictFinite f a 0 (Nat.zero_le 1),
      quadCoord_zero_cechRestrictInfinite] at h0
    rw [quadCoord_cechRestrictFinite f a 1 le_rfl, quadCoord_one_cechRestrictInfinite] at h1
    obtain ⟨hp, hp'⟩ := eq_C_of_toLaurent_eq_invert h0
    obtain ⟨hq, hq'⟩ := eq_C_of_toLaurent_eq_invert h1
    have hc : (quadCoord _ 1 a).coeff 0 = 0 := by
      rw [← coeff_C_zero (a := (quadCoord _ 1 a).coeff 0), ← hq', coeff_mul_X_pow',
        ite_eq_right (show ¬(genus f + 1 ≤ 0) by omega)]
    rw [hc, C_0] at hq hq'
    have hq'' : quadCoord _ 1 b = 0 :=
      (mul_eq_zero.mp hq').resolve_right (pow_ne_zero _ X_ne_zero)
    refine LinearMap.mem_range.mpr ⟨(quadCoord _ 0 a).coeff 0, ?_⟩
    change (algebraMap k _ _, algebraMap k _ _) = (a, b)
    rw [algebraMap_hyperellipticCoordRing, algebraMap_hyperellipticCoordRing]
    refine Prod.ext ?_ ?_
    · change _ = a
      conv_rhs => rw [eq_quadCoord _ a]
      rw [hq, map_zero (AdjoinRoot.of (X ^ 2 - C f)), zero_mul, add_zero, ← hp]
    · change _ = b
      conv_rhs => rw [eq_quadCoord _ b]
      rw [hq'', map_zero (AdjoinRoot.of (X ^ 2 - C (reflect (2 * genus f + 2) f))), zero_mul,
        add_zero, ← hp']

/-- `CechH0 f ≃ k`: the Čech `H⁰` consists of the constants. -/
@[expose]
noncomputable def cechH0Equiv : k ≃ₗ[k] CechH0 f :=
  (LinearEquiv.ofInjective (cechConstants f) (cechConstants_injective f)).trans
    (LinearEquiv.ofEq _ _ (range_cechConstants f))

/-- **The Čech `H⁰` of the structure sheaf of the hyperelliptic model is one-dimensional.** -/
theorem finrank_cechH0 : Module.finrank k (CechH0 f) = 1 := by
  rw [← (cechH0Equiv f).finrank_eq, Module.finrank_self]

/-! ### Derived-functor cohomology of the structure sheaf

`H^i(X, 𝒪_X)` and the genus are the Stacks library's `AlgebraicGeometry.structureSheafCohomology`
and `AlgebraicGeometry.genus` (`dim_k H¹(X, 𝒪_X)`, Stacks Tag 0BY7). -/

open AlgebraicGeometry in
/-- Interface: **any** `k`-linear identification of `H¹(X, 𝒪_X)` with the two-chart Čech `H¹`
gives `genus = ⌊(deg f - 1)/2⌋`. -/
theorem genus_eq_of_linearEquiv
    (e : structureSheafCohomology (toSpecField f) 1 ≃ₗ[k] CechH1 f) :
    AlgebraicGeometry.genus (toSpecField f) = (f.natDegree - 1) / 2 := by
  rw [AlgebraicGeometry.genus_eq_finrank_structureSheafCohomology, e.finrank_eq, finrank_cechH1]

end Hyperelliptic

end ArithmeticOfJacobiPolynomials
