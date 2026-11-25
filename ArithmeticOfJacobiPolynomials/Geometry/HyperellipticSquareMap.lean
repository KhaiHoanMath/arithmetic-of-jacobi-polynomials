/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticProjective
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# The degree-two morphism `(x, y) ↦ (x^2, y)` of projective hyperelliptic models

Let `k` be a field, `q ∈ k[t]` of degree `m ≥ 1` and `f = q(x^2)` (`expand k 2 q`, of degree
`2m`). The paragraph after Corollary 6.6 of the manuscript uses the map
`{y^2 = f(x)} → {y^2 = q(t)}`, `(x, y) ↦ (x^2, y)`, and the fact that it extends to a morphism
of the smooth projective models. This file constructs that extension as a morphism of schemes
`squareMorphism q hq : projectiveModel (expand k 2 q) ⟶ projectiveModel q`
(`ArithmeticOfJacobiPolynomials.Hyperelliptic.projectiveModel`, weighted `Proj`).

## The graded map

Write `g_q = ⌊(m - 1)/2⌋`, `N_q = 2 g_q + 2 ∈ {m, m + 1}`; for `f` one has `g_f = m - 1` and
`N_f = 2m` (`genus_expand`). Put `e = N_q - m` (`squareShift q`): `e = 0` if `m` is even and
`e = 1` if `m` is odd (`squareShift_eq_zero_of_even`, `squareShift_eq_one_of_odd`). The
`k`-algebra map `S_q = k[X, Z, Y]/(Y^2 - Z^{N_q} q(X/Z)) → S_f`,
`X ↦ X^2`, `Z ↦ Z^2`, `Y ↦ Y Z^e` (`squareGradedMap`), is well defined because
`Z^{2N_q} q(X^2/Z^2) = Z^{2e} · Z^{2m} f(X/Z)` (`aeval_squareValues_equation`), and it doubles
weighted degrees (`squareHom_mem`): `Y` has weight `g_q + 1` and `Y Z^e` has weight
`m + e = 2(g_q + 1)`. Since `Proj.map` only handles degree-preserving maps, the morphism is
obtained by gluing.

## The gluing

For a homogeneous `s` and `t` with `φ(s) = t^c` (and compatible degrees), a degree-multiplying
ring map `φ` induces `(A_s)_0 → (B_t)_0`, `a/s^n ↦ φ(a)/t^{cn}` (`scaledAwayMap`), compatible
with the restriction maps `awayMap` (`awayMap_comp_scaledAwayMap`). On the two standard charts
`D₊(Z)` and `D₊(X)` of the source (`chartCover`; they cover by `iSup_chart_eq_top`), the
morphisms `Spec (S_f)_{(X_c)} → Spec (S_q)_{(X_c)} → projectiveModel q`
(`chartSquareMorphism`) agree on the overlaps `D₊(X_c X_{c'})` (`squareGlue_condition`, via
`Proj.pullbackAwayιIso`), so they glue to `squareMorphism q hq`.

## Main results

For `q` of positive degree:

* `squareMorphism_toSpecField`: the morphism is a morphism over `Spec k`;
* `affineChart_comp_squareMorphism`: **on the affine charts `y^2 = f(x)` and `y^2 = q(t)` it is
  `Spec` of `squareMap q : k[t, y]/(y^2 - q(t)) → k[x, y]/(y^2 - q(x^2))`, `t ↦ x^2`, `y ↦ y`**;
  `affineChartAtInfinity_comp_squareMorphism` describes the charts at infinity
  (`x' ↦ u^2`, `w ↦ v u^e`, `chartAffineSquareMap_infinite_algebraMap_X`,
  `chartAffineSquareMap_infinite_root`);
* `surjective_squareMorphism`: it is surjective;
* `isProper_squareMorphism`: it is proper (source proper over `k`, target separated);
* `isIntegralHom_chartSquareMorphism_one`, `isIntegralHom_chartSquareMorphism_zero`: on each
  source chart, the map to the corresponding target chart is integral;
* `isFinite_specMap_squareMap`, `ArithmeticOfJacobiPolynomials.free_and_finrank_squareMap`: on the
affine chart
  the map is
  finite, and `k[x, y]/(y^2 - q(x^2))` is free of rank `2` over `k[t, y]/(y^2 - q(t))`
  (`ArithmeticOfJacobiPolynomials.free_and_finrank_squareMap`), i.e. it has degree two there.

The instance for the derivative families of the manuscript, `f = F_{m,r,δ} = Q_{m,r,δ}(x^2)`
(`ArithmeticOfJacobiPolynomials.expand_reducedGegenbauerSquare`), is `derivativeSquareMorphism`,
with
`derivativeSquareMorphism_toSpecField`, `surjective_derivativeSquareMorphism`,
`isProper_derivativeSquareMorphism`.

The finiteness of the whole morphism (affine over the target) and the degree of the extension of
function fields of the (integral) projective models are in
`ArithmeticOfJacobiPolynomials.Geometry.HyperellipticSquareMapDegree`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

universe u

namespace Hyperelliptic

open Polynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits GradedQuotient

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ### Degree-multiplying maps of homogeneous localizations -/

section ScaledAway

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule R B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

theorem awayLift_algebraMap {S P : Type*} [CommRing S] [CommRing P] (g : S →+* P) (r : S)
    (hr : IsUnit (g r)) (a : S) :
    Localization.awayLift g r hr (algebraMap S (Localization.Away r) a) = g a :=
  IsLocalization.Away.lift_eq r hr a

variable (φ : A →+* B) {s : A} {t : B} {c : ℕ}

theorem isUnit_of_eq_pow (hst : φ s = t ^ c) :
    IsUnit ((algebraMap B (Localization.Away t)).comp φ s) := by
  rw [RingHom.comp_apply, hst, map_pow]
  exact (IsLocalization.Away.algebraMap_isUnit t).pow c

/-- `a/s^n ↦ φ(a)/t^{cn}` on the ordinary localizations, when `φ s = t^c`. -/
@[expose]
noncomputable def scaledLocalizationMap (hst : φ s = t ^ c) :
    Localization.Away s →+* Localization.Away t :=
  Localization.awayLift ((algebraMap B (Localization.Away t)).comp φ) s (isUnit_of_eq_pow φ hst)

theorem scaledLocalizationMap_algebraMap (hst : φ s = t ^ c) (a : A) :
    scaledLocalizationMap φ hst (algebraMap A _ a) = algebraMap B _ (φ a) :=
  awayLift_algebraMap _ _ (isUnit_of_eq_pow φ hst) a

theorem scaledLocalizationMap_mk (hst : φ s = t ^ c) (n : ℕ) (a : A) :
    scaledLocalizationMap φ hst (Localization.mk a (⟨s ^ n, n, rfl⟩ : Submonoid.powers s)) =
      Localization.mk (φ a) (⟨t ^ (c * n), c * n, rfl⟩ : Submonoid.powers t) := by
  have h1 := congrArg (scaledLocalizationMap φ hst)
    (IsLocalization.mk'_spec (Localization.Away s) a (⟨s ^ n, n, rfl⟩ : Submonoid.powers s))
  rw [map_mul, scaledLocalizationMap_algebraMap, scaledLocalizationMap_algebraMap] at h1
  have h2 : φ (s ^ n) = t ^ (c * n) := by rw [map_pow, hst, ← pow_mul]
  rw [Localization.mk_eq_mk'_apply, Localization.mk_eq_mk'_apply,
    IsLocalization.eq_mk'_iff_mul_eq]
  change _ * algebraMap B _ (t ^ (c * n)) = _
  rw [← h2]
  exact h1

theorem scaledLocalizationMap_comp_awayLift {s₁ x : A} {t₁ y : B} (hst₁ : φ s₁ = t₁ ^ c)
    (hstx : φ x = y ^ c) (hu₁ : IsUnit (algebraMap B (Localization.Away y) t₁))
    (hu₂ : IsUnit (algebraMap A (Localization.Away x) s₁)) :
    (Localization.awayLift (algebraMap B (Localization.Away y)) t₁ hu₁).comp
        (scaledLocalizationMap φ hst₁) =
      (scaledLocalizationMap φ hstx).comp
        (Localization.awayLift (algebraMap A (Localization.Away x)) s₁ hu₂) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers s₁)
  ext b
  simp only [RingHom.comp_apply, scaledLocalizationMap_algebraMap, awayLift_algebraMap]

variable {d : ℕ} (hφ : ∀ (n : ℕ) (a : A), a ∈ 𝒜 n → φ a ∈ ℬ (d * n)) {i j : ℕ}

include hφ in
omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
theorem scaled_mem (hdeg : d * i = c * j) {n : ℕ} {x : A} (hx : x ∈ 𝒜 (n • i)) :
    φ x ∈ ℬ ((c * n) • j) := by
  have e : d * (n • i) = (c * n) • j := by
    rw [smul_eq_mul, smul_eq_mul, mul_left_comm, hdeg]
    ring
  rw [← e]
  exact hφ _ x hx

variable (hs : s ∈ 𝒜 i) (ht : t ∈ ℬ j) (hst : φ s = t ^ c) (hdeg : d * i = c * j)

include hφ hs ht hdeg in
theorem scaledLocalizationMap_mem (a : HomogeneousLocalization.Away 𝒜 s) :
    ((scaledLocalizationMap φ hst).comp
        (algebraMap (HomogeneousLocalization.Away 𝒜 s) (Localization.Away s))) a ∈
      (algebraMap (HomogeneousLocalization.Away ℬ t) (Localization.Away t)).range := by
  obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hs a
  refine RingHom.mem_range.mpr
    ⟨HomogeneousLocalization.Away.mk ℬ ht (c * n) (φ x) (scaled_mem φ hφ hdeg hx), ?_⟩
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, scaledLocalizationMap_mk]

variable (ℬ) in
/-- `(B_t)_0` is isomorphic to its image in `B_t`. -/
@[expose]
noncomputable def awayValEquiv (t : B) :
    HomogeneousLocalization.Away ℬ t ≃+*
      (algebraMap (HomogeneousLocalization.Away ℬ t) (Localization.Away t)).range :=
  RingEquiv.ofLeftInverse (f := algebraMap (HomogeneousLocalization.Away ℬ t)
    (Localization.Away t))
    (h := (HomogeneousLocalization.val_injective _).hasLeftInverse.choose_spec)

/-- **The map `(A_s)_0 → (B_t)_0`, `a/s^n ↦ φ(a)/t^{cn}`**, for a ring map `φ` multiplying degrees
by `d`, with `φ s = t^c` and `d deg s = c deg t`. -/
@[expose]
noncomputable def scaledAwayMap :
    HomogeneousLocalization.Away 𝒜 s →+* HomogeneousLocalization.Away ℬ t :=
  (awayValEquiv ℬ t).symm.toRingHom.comp
    (((scaledLocalizationMap φ hst).comp
      (algebraMap (HomogeneousLocalization.Away 𝒜 s) (Localization.Away s))).codRestrict _
        (scaledLocalizationMap_mem φ hφ hs ht hst hdeg))

theorem val_scaledAwayMap (a : HomogeneousLocalization.Away 𝒜 s) :
    (scaledAwayMap φ hφ hs ht hst hdeg a).val = scaledLocalizationMap φ hst a.val :=
  congrArg Subtype.val ((awayValEquiv ℬ t).apply_symm_apply
    ((((scaledLocalizationMap φ hst).comp
      (algebraMap (HomogeneousLocalization.Away 𝒜 s) (Localization.Away s))).codRestrict _
        (scaledLocalizationMap_mem φ hφ hs ht hst hdeg)) a))

theorem scaledAwayMap_mk (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • i)) :
    scaledAwayMap φ hφ hs ht hst hdeg (HomogeneousLocalization.Away.mk 𝒜 hs n x hx) =
      HomogeneousLocalization.Away.mk ℬ ht (c * n) (φ x) (scaled_mem φ hφ hdeg hx) := by
  apply HomogeneousLocalization.val_injective
  rw [val_scaledAwayMap, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, scaledLocalizationMap_mk]

/-- `scaledAwayMap` commutes with the restriction maps `awayMap` to `D₊(s₁ s₂)`. -/
theorem awayMap_comp_scaledAwayMap {s₁ s₂ x : A} {t₁ t₂ y : B} {i₁ i₂ j₁ j₂ i' j' : ℕ}
    (hs₁ : s₁ ∈ 𝒜 i₁) (hs₂ : s₂ ∈ 𝒜 i₂) (ht₁ : t₁ ∈ ℬ j₁) (ht₂ : t₂ ∈ ℬ j₂)
    (hst₁ : φ s₁ = t₁ ^ c) (hdeg₁ : d * i₁ = c * j₁) (hx : x = s₁ * s₂) (hy : y = t₁ * t₂)
    (hsx : x ∈ 𝒜 i') (hty : y ∈ ℬ j') (hstx : φ x = y ^ c) (hdegx : d * i' = c * j') :
    (HomogeneousLocalization.awayMap ℬ ht₂ hy).comp (scaledAwayMap φ hφ hs₁ ht₁ hst₁ hdeg₁) =
      (scaledAwayMap φ hφ hsx hty hstx hdegx).comp (HomogeneousLocalization.awayMap 𝒜 hs₂ hx) := by
  refine RingHom.ext fun a => ?_
  apply HomogeneousLocalization.val_injective
  rw [RingHom.comp_apply, RingHom.comp_apply, HomogeneousLocalization.val_awayMap,
    val_scaledAwayMap, val_scaledAwayMap, HomogeneousLocalization.val_awayMap]
  exact RingHom.congr_fun (scaledLocalizationMap_comp_awayLift φ hst₁ hstx
    (isUnit_of_dvd_unit (map_dvd _ ⟨_, hy⟩) (IsLocalization.Away.algebraMap_isUnit y))
    (isUnit_of_dvd_unit (map_dvd _ ⟨_, hx⟩) (IsLocalization.Away.algebraMap_isUnit x))) a.val

end ScaledAway

/-- A commutative square of rings gives a commutative square of spectra. -/
@[reassoc]
theorem specMap_comm_square {R₁ R₂ R₃ R₄ : Type u} [CommRing R₁] [CommRing R₂] [CommRing R₃]
    [CommRing R₄] {α : R₁ →+* R₂} {β : R₂ →+* R₃} {γ : R₁ →+* R₄} {δ : R₄ →+* R₃}
    (h : β.comp α = δ.comp γ) :
    Spec.map (CommRingCat.ofHom β) ≫ Spec.map (CommRingCat.ofHom α) =
      Spec.map (CommRingCat.ofHom δ) ≫ Spec.map (CommRingCat.ofHom γ) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, h]

/-! ### Polynomial identities -/

variable {k : Type u} [Field k]

theorem fin3_cases (c : Fin 3) : c = 0 ∨ c = 1 ∨ c = 2 := by
  revert c
  decide

theorem weights_eq_one_of_ne_two (g : ℕ) {c : Fin 3} (hc : c ≠ 2) : weights g c = 1 := by
  rcases fin3_cases c with rfl | rfl | rfl
  · rfl
  · rfl
  · exact absurd rfl hc

/-- `e = N_q - deg q`, the power of `Z` in the image `Y Z^e` of `Y`. -/
@[expose]
def squareShift (q : k[X]) : ℕ := 2 * genus q + 2 - q.natDegree

theorem genus_expand (q : k[X]) (hq : 0 < q.natDegree) :
    genus (expand k 2 q) = q.natDegree - 1 := by
  rw [genus, natDegree_expand]
  omega

theorem genus_expand_add_squareShift {q : k[X]} (hq : 0 < q.natDegree) :
    genus (expand k 2 q) + 1 + squareShift q = 2 * (genus q + 1) := by
  have h1 := genus_expand q hq
  have h2 := natDegree_le_two_mul_genus_add_two q
  rw [squareShift]
  omega

/-- For `deg q` even, `Y ↦ Y`. -/
theorem squareShift_eq_zero_of_even {q : k[X]} (hq : 0 < q.natDegree) (he : Even q.natDegree) :
    squareShift q = 0 := by
  obtain ⟨j, hj⟩ := he
  rw [squareShift, genus]
  omega

/-- For `deg q` odd, `Y ↦ Y Z`. -/
theorem squareShift_eq_one_of_odd {q : k[X]} (ho : Odd q.natDegree) : squareShift q = 1 := by
  obtain ⟨j, hj⟩ := ho
  rw [squareShift, genus]
  omega

/-- The images `X^2, Z^2, Y Z^e` of `X, Z, Y`. -/
@[expose]
noncomputable def squareValues (q : k[X]) : Fin 3 → MvPolynomial (Fin 3) k :=
  ![MvPolynomial.X 0 ^ 2, MvPolynomial.X 1 ^ 2,
    MvPolynomial.X 2 * MvPolynomial.X 1 ^ squareShift q]

theorem squareValues_zero (q : k[X]) : squareValues q 0 = MvPolynomial.X 0 ^ 2 := rfl

theorem squareValues_one (q : k[X]) : squareValues q 1 = MvPolynomial.X 1 ^ 2 := rfl

theorem squareValues_two (q : k[X]) :
    squareValues q 2 = MvPolynomial.X 2 * MvPolynomial.X 1 ^ squareShift q := rfl

theorem sum_range_two_mul_add_one_of_odd {M : Type*} [AddCommMonoid M] (g : ℕ → M) (N : ℕ)
    (hg : ∀ i, g (2 * i + 1) = 0) :
    ∑ j ∈ Finset.range (2 * N + 1), g j = ∑ i ∈ Finset.range (N + 1), g (2 * i) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ g (2 * n + 1 + 1),
      Finset.sum_range_succ g (2 * n + 1), ih, hg n, add_zero,
      Finset.sum_range_succ (fun i => g (2 * i)) (n + 1),
      show 2 * n + 1 + 1 = 2 * (n + 1) by ring]

/-- `X_c^j · Σ_{i ≤ N} p_i X_o^i X_c^{N-i} = Σ_{i ≤ N + j} p_i X_o^i X_c^{N+j-i}`. -/
theorem X_pow_mul_binaryForm (o c : Fin 3) (p : k[X]) {N : ℕ} (hp : p.natDegree ≤ N) (j : ℕ) :
    MvPolynomial.X c ^ j * binaryForm o c p N = binaryForm o c p (N + j) := by
  rw [binaryForm, binaryForm, Finset.mul_sum]
  have hsub : Finset.range (N + 1) ⊆ Finset.range (N + j + 1) :=
    Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [show N + j - i = (N - i) + j by omega, pow_add]
    ring
  · intro i hi hi'
    have : N < i := by
      rw [Finset.mem_range] at hi hi'
      omega
    rw [coeff_eq_zero_of_natDegree_lt (show p.natDegree < i by omega), map_zero, zero_mul,
      zero_mul]

/-- `Z^{2N} q(X^2/Z^2)` is the binary form of `q(x^2)` of degree `2N`. -/
theorem aeval_square_binaryForm (q : k[X]) (N : ℕ) {v : Fin 3 → MvPolynomial (Fin 3) k}
    (h0 : v 0 = MvPolynomial.X 0 ^ 2) (h1 : v 1 = MvPolynomial.X 1 ^ 2) :
    MvPolynomial.aeval v (binaryForm 0 1 q N) = binaryForm 0 1 (expand k 2 q) (2 * N) := by
  rw [binaryForm, binaryForm, map_sum]
  symm
  refine (sum_range_two_mul_add_one_of_odd _ N fun i => ?_).trans
    (Finset.sum_congr rfl fun i hi => ?_)
  · rw [coeff_expand two_pos]
    simp [show ¬ 2 ∣ 2 * i + 1 by omega]
  · have hi' : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [map_mul (MvPolynomial.aeval v), map_mul (MvPolynomial.aeval v),
      map_pow (MvPolynomial.aeval v), map_pow (MvPolynomial.aeval v), MvPolynomial.aeval_C,
      MvPolynomial.aeval_X, MvPolynomial.aeval_X, h0, h1, coeff_expand_mul' two_pos, ← pow_mul,
      ← pow_mul, MvPolynomial.algebraMap_eq,
      show 2 * N - 2 * i = 2 * (N - i) by omega]

/-- **The equation is preserved**: the image of `Y^2 - Z^{N_q} q(X/Z)` is
`Z^{2e} (Y^2 - Z^{2m} f(X/Z))`. -/
theorem aeval_squareValues_equation (q : k[X]) (hq : 0 < q.natDegree) :
    MvPolynomial.aeval (squareValues q) (equation 0 1 q (2 * genus q + 2)) =
      MvPolynomial.X 1 ^ (2 * squareShift q) *
        equation 0 1 (expand k 2 q) (2 * genus (expand k 2 q) + 2) := by
  have hN : 2 * genus (expand k 2 q) + 2 = 2 * q.natDegree := by
    rw [genus_expand q hq]
    omega
  have hdeg : (expand k 2 q).natDegree ≤ 2 * q.natDegree := by
    rw [natDegree_expand]
    omega
  have hsum : 2 * q.natDegree + 2 * squareShift q = 2 * (2 * genus q + 2) := by
    have := natDegree_le_two_mul_genus_add_two q
    rw [squareShift]
    omega
  rw [equation, equation, map_sub, map_pow, MvPolynomial.aeval_X,
    aeval_square_binaryForm q _ rfl rfl, hN, mul_sub, X_pow_mul_binaryForm 0 1 _ hdeg, hsum]
  congr 1
  rw [squareValues_two]
  ring

/-! ### Weighted degrees -/

theorem isWeightedHomogeneous_aeval {σ τ S : Type*} [CommSemiring S] {w : σ → ℕ} {w' : τ → ℕ}
    {v : σ → MvPolynomial τ S} {c : ℕ} (hv : ∀ i, (v i).IsWeightedHomogeneous w' (c * w i))
    {P : MvPolynomial σ S} {n : ℕ} (hP : P.IsWeightedHomogeneous w n) :
    (MvPolynomial.aeval v P).IsWeightedHomogeneous w' (c * n) := by
  rw [P.as_sum, map_sum]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have hw : Finsupp.weight w d = n := hP (MvPolynomial.mem_support_iff.mp hd)
  rw [MvPolynomial.aeval_monomial, ← hw, Finsupp.weight_apply, Finsupp.sum, Finset.mul_sum]
  have h := (MvPolynomial.isWeightedHomogeneous_C w' (P.coeff d)).mul
    (MvPolynomial.IsWeightedHomogeneous.prod d.support (fun i => v i ^ d i)
      (fun i => d i • (c * w i)) fun i _ => (hv i).pow (d i))
  rw [zero_add] at h
  convert h using 1
  · rw [Finsupp.prod, MvPolynomial.algebraMap_eq]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [smul_eq_mul]
    ring

variable {q : k[X]}

theorem isWeightedHomogeneous_squareValues (hq : 0 < q.natDegree) (i : Fin 3) :
    (squareValues q i).IsWeightedHomogeneous (weights (genus (expand k 2 q)))
      (2 * weights (genus q) i) := by
  rcases fin3_cases i with rfl | rfl | rfl
  · have h := (MvPolynomial.isWeightedHomogeneous_X (R := k)
      (weights (genus (expand k 2 q))) 0).pow 2
    rw [weights_zero, smul_eq_mul] at h
    exact h
  · have h := (MvPolynomial.isWeightedHomogeneous_X (R := k)
      (weights (genus (expand k 2 q))) 1).pow 2
    rw [weights_one, smul_eq_mul] at h
    exact h
  · have h := (MvPolynomial.isWeightedHomogeneous_X (R := k)
      (weights (genus (expand k 2 q))) 2).mul
      ((MvPolynomial.isWeightedHomogeneous_X (R := k)
        (weights (genus (expand k 2 q))) 1).pow (squareShift q))
    rw [weights_two, weights_one, smul_eq_mul, mul_one, genus_expand_add_squareShift hq] at h
    rw [weights_two]
    exact h

/-! ### The graded map `S_q → S_f` -/

variable (q) in
/-- **The map of homogeneous coordinate rings** `S_q → S_f`, `X ↦ X^2`, `Z ↦ Z^2`,
`Y ↦ Y Z^e` (`f = q(x^2)`). -/
@[expose]
noncomputable def squareGradedMap (hq : 0 < q.natDegree) :
    HomogeneousCoordRing q →ₐ[k] HomogeneousCoordRing (expand k 2 q) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ k _).comp (MvPolynomial.aeval (squareValues q)))
    (by
      intro a ha
      rw [coordIdeal, Ideal.mem_span_singleton'] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, map_mul,
        aeval_squareValues_equation q hq]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))

variable (q) in
/-- `squareGradedMap` as a ring map. -/
@[expose]
noncomputable def squareHom (hq : 0 < q.natDegree) :
    HomogeneousCoordRing q →+* HomogeneousCoordRing (expand k 2 q) :=
  (squareGradedMap q hq).toRingHom

theorem squareHom_mk (hq : 0 < q.natDegree) (P : MvPolynomial (Fin 3) k) :
    squareHom q hq (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk _ (MvPolynomial.aeval (squareValues q) P) :=
  rfl

theorem squareHom_algebraMap (hq : 0 < q.natDegree) (r : k) :
    squareHom q hq (algebraMap k _ r) = algebraMap k _ r :=
  (squareGradedMap q hq).commutes r

theorem squareHom_var (hq : 0 < q.natDegree) (i : Fin 3) :
    squareHom q hq (var q i) = Ideal.Quotient.mk _ (squareValues q i) := by
  rw [var, squareHom_mk, MvPolynomial.aeval_X]

theorem squareHom_var_of_ne_two (hq : 0 < q.natDegree) {c : Fin 3} (hc : c ≠ 2) :
    squareHom q hq (var q c) = var (expand k 2 q) c ^ 2 := by
  rw [squareHom_var, var, ← map_pow]
  rcases fin3_cases c with rfl | rfl | rfl
  · rfl
  · rfl
  · exact absurd rfl hc

theorem squareHom_var_two (hq : 0 < q.natDegree) :
    squareHom q hq (var q 2) =
      var (expand k 2 q) 2 * var (expand k 2 q) 1 ^ squareShift q := by
  rw [squareHom_var, var, var, ← map_pow, ← map_mul]
  rfl

/-- `squareHom` doubles weighted degrees. -/
theorem squareHom_mem (hq : 0 < q.natDegree) :
    ∀ (n : ℕ) (a : HomogeneousCoordRing q), a ∈ grading q n →
      squareHom q hq a ∈ grading (expand k 2 q) (2 * n) := by
  rintro n _ ⟨P, hP, rfl⟩
  exact mk_mem_quotientGrading _ _
    (isWeightedHomogeneous_aeval (isWeightedHomogeneous_squareValues hq) hP)

/-! ### The chart maps -/

/-- On `D₊(X_c)` (`c = 0, 1`): `(S_q)_{(X_c)} → (S_f)_{(X_c)}`, `a/X_c^n ↦ φ(a)/X_c^{2n}`. -/
@[expose]
noncomputable def chartSquareMap (hq : 0 < q.natDegree) (c : Fin 3) (hc : c ≠ 2) :
    ChartRing q c →+* ChartRing (expand k 2 q) c :=
  scaledAwayMap (c := 2) (squareHom q hq) (squareHom_mem hq)
    (var_mem_one q (weights_eq_one_of_ne_two _ hc))
    (var_mem_one (expand k 2 q) (weights_eq_one_of_ne_two _ hc)) (squareHom_var_of_ne_two hq hc)
    rfl

/-- On the overlaps `D₊(X_{c₁} X_{c₂})`. -/
@[expose]
noncomputable def overlapSquareMap (hq : 0 < q.natDegree) {c₁ c₂ : Fin 3} (hc₁ : c₁ ≠ 2)
    (hc₂ : c₂ ≠ 2) :
    HomogeneousLocalization.Away (grading q) (var q c₁ * var q c₂) →+*
      HomogeneousLocalization.Away (grading (expand k 2 q))
        (var (expand k 2 q) c₁ * var (expand k 2 q) c₂) :=
  scaledAwayMap (c := 2) (squareHom q hq) (squareHom_mem hq)
    (SetLike.mul_mem_graded (var_mem_one q (weights_eq_one_of_ne_two _ hc₁))
      (var_mem_one q (weights_eq_one_of_ne_two _ hc₂)))
    (SetLike.mul_mem_graded (var_mem_one _ (weights_eq_one_of_ne_two _ hc₁))
      (var_mem_one _ (weights_eq_one_of_ne_two _ hc₂)))
    (by rw [map_mul, squareHom_var_of_ne_two hq hc₁, squareHom_var_of_ne_two hq hc₂, mul_pow])
    rfl

theorem overlap_compat_left (hq : 0 < q.natDegree) {c₁ c₂ : Fin 3} (hc₁ : c₁ ≠ 2)
    (hc₂ : c₂ ≠ 2) :
    (HomogeneousLocalization.awayMap (grading (expand k 2 q))
        (var_mem_one (expand k 2 q) (weights_eq_one_of_ne_two _ hc₂)) rfl).comp
        (chartSquareMap hq c₁ hc₁) =
      (overlapSquareMap hq hc₁ hc₂).comp
        (HomogeneousLocalization.awayMap (grading q)
          (var_mem_one q (weights_eq_one_of_ne_two _ hc₂)) rfl) :=
  awayMap_comp_scaledAwayMap _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem overlap_compat_right (hq : 0 < q.natDegree) {c₁ c₂ : Fin 3} (hc₁ : c₁ ≠ 2)
    (hc₂ : c₂ ≠ 2) :
    (HomogeneousLocalization.awayMap (grading (expand k 2 q))
        (var_mem_one (expand k 2 q) (weights_eq_one_of_ne_two _ hc₁)) (mul_comm _ _)).comp
        (chartSquareMap hq c₂ hc₂) =
      (overlapSquareMap hq hc₁ hc₂).comp
        (HomogeneousLocalization.awayMap (grading q)
          (var_mem_one q (weights_eq_one_of_ne_two _ hc₁)) (mul_comm _ _)) :=
  awayMap_comp_scaledAwayMap _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The morphism `Spec (S_f)_{(X_c)} → Spec (S_q)_{(X_c)} → projectiveModel q`. -/
@[expose]
noncomputable def chartSquareMorphism (hq : 0 < q.natDegree) (c : Fin 3) (hc : c ≠ 2) :
    Spec (CommRingCat.of (ChartRing (expand k 2 q) c)) ⟶ projectiveModel q :=
  Spec.map (CommRingCat.ofHom (chartSquareMap hq c hc)) ≫
    Proj.awayι (grading q) (var q c) (var_mem_one q (weights_eq_one_of_ne_two _ hc)) Nat.one_pos

/-- **The chart morphisms agree on the overlaps.** -/
theorem squareGlue_condition (hq : 0 < q.natDegree) {c₁ c₂ : Fin 3} (hc₁ : c₁ ≠ 2)
    (hc₂ : c₂ ≠ 2) :
    pullback.fst
        (Proj.awayι (grading (expand k 2 q)) (var _ c₁)
          (var_mem_one _ (weights_eq_one_of_ne_two _ hc₁)) Nat.one_pos)
        (Proj.awayι (grading (expand k 2 q)) (var _ c₂)
          (var_mem_one _ (weights_eq_one_of_ne_two _ hc₂)) Nat.one_pos) ≫
        chartSquareMorphism hq c₁ hc₁ =
      pullback.snd
        (Proj.awayι (grading (expand k 2 q)) (var _ c₁)
          (var_mem_one _ (weights_eq_one_of_ne_two _ hc₁)) Nat.one_pos)
        (Proj.awayι (grading (expand k 2 q)) (var _ c₂)
          (var_mem_one _ (weights_eq_one_of_ne_two _ hc₂)) Nat.one_pos) ≫
        chartSquareMorphism hq c₂ hc₂ := by
  rw [← cancel_epi (Proj.pullbackAwayιIso (grading (expand k 2 q))
      (var_mem_one _ (weights_eq_one_of_ne_two _ hc₁)) Nat.one_pos
      (var_mem_one _ (weights_eq_one_of_ne_two _ hc₂)) Nat.one_pos rfl).inv,
    Proj.pullbackAwayιIso_inv_fst_assoc, Proj.pullbackAwayιIso_inv_snd_assoc,
    chartSquareMorphism, chartSquareMorphism,
    specMap_comm_square_assoc (overlap_compat_left hq hc₁ hc₂),
    specMap_comm_square_assoc (overlap_compat_right hq hc₁ hc₂),
    Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]

/-! ### The glued morphism -/

/-- The chart variables: `Z` (index `0`) and `X` (index `1`). -/
@[expose]
def coverVar : Fin 2 → Fin 3 := ![1, 0]

theorem coverVar_ne_two (a : Fin 2) : coverVar a ≠ 2 := by
  revert a
  decide

open Classical in
/-- The cover of the projective model by the charts `D₊(Z)` and `D₊(X)`. -/
@[expose]
noncomputable def chartCover (f : k[X]) : (projectiveModel f).AffineOpenCover where
  I₀ := Fin 2
  X a := CommRingCat.of (ChartRing f (coverVar a))
  f a := Proj.awayι (grading f) (var f (coverVar a))
    (var_mem_one f (weights_eq_one_of_ne_two _ (coverVar_ne_two a))) Nat.one_pos
  idx x := if x ∈ Proj.basicOpen (grading f) (var f 1) then 0 else 1
  covers x := by
    have hx : x ∈ Proj.basicOpen (grading f) (var f 1) ⊔ Proj.basicOpen (grading f) (var f 0) := by
      rw [iSup_chart_eq_top f]
      trivial
    rw [TopologicalSpace.Opens.mem_sup] at hx
    change x ∈ (Proj.awayι _ _ _ _).opensRange
    rw [Proj.opensRange_awayι]
    split_ifs with h
    · exact h
    · exact hx.resolve_left h

/-- The family of chart morphisms. -/
@[expose]
noncomputable def squareChartFamily (hq : 0 < q.natDegree) (a : Fin 2) :
    (chartCover (expand k 2 q)).openCover.X a ⟶ projectiveModel q :=
  chartSquareMorphism hq (coverVar a) (coverVar_ne_two a)

variable (q) in
/-- **The degree-two morphism `(x, y) ↦ (x^2, y)`** from the projective model of
`y^2 = q(x^2)` to that of `y^2 = q(t)`. -/
@[expose]
noncomputable def squareMorphism (hq : 0 < q.natDegree) :
    projectiveModel (expand k 2 q) ⟶ projectiveModel q :=
  (chartCover (expand k 2 q)).openCover.glueMorphisms (squareChartFamily hq)
    (fun a b => squareGlue_condition hq (coverVar_ne_two a) (coverVar_ne_two b))

theorem awayι_comp_squareMorphism (hq : 0 < q.natDegree) (a : Fin 2) :
    Proj.awayι (grading (expand k 2 q)) (var _ (coverVar a))
        (var_mem_one _ (weights_eq_one_of_ne_two _ (coverVar_ne_two a))) Nat.one_pos ≫
        squareMorphism q hq =
      chartSquareMorphism hq (coverVar a) (coverVar_ne_two a) :=
  (chartCover (expand k 2 q)).openCover.ι_glueMorphisms (squareChartFamily hq) _ a

/-- On `D₊(Z)`. -/
theorem awayι_one_comp_squareMorphism (hq : 0 < q.natDegree) :
    Proj.awayι (grading (expand k 2 q)) (var _ 1)
        (var_mem_one _ (chartData_finite (expand k 2 q)).weight_c) Nat.one_pos ≫
        squareMorphism q hq =
      chartSquareMorphism hq 1 (chartData_finite q).ne_two' :=
  awayι_comp_squareMorphism hq 0

/-- On `D₊(X)`. -/
theorem awayι_zero_comp_squareMorphism (hq : 0 < q.natDegree) :
    Proj.awayι (grading (expand k 2 q)) (var _ 0)
        (var_mem_one _ (chartData_infinite (expand k 2 q)).weight_c) Nat.one_pos ≫
        squareMorphism q hq =
      chartSquareMorphism hq 0 (chartData_infinite q).ne_two' :=
  awayι_comp_squareMorphism hq 1

theorem chartSquareMap_chartStructureMap (hq : 0 < q.natDegree) {c : Fin 3} (hc : c ≠ 2)
    (r : k) :
    chartSquareMap hq c hc (chartStructureMap q c r) = chartStructureMap (expand k 2 q) c r := by
  apply HomogeneousLocalization.val_injective
  rw [chartSquareMap, val_scaledAwayMap, ← HomogeneousLocalization.algebraMap_apply,
    ← HomogeneousLocalization.algebraMap_apply, val_chartStructureMap, val_chartStructureMap,
    IsScalarTower.algebraMap_apply k (HomogeneousCoordRing q) (Localization.Away (var q c)),
    scaledLocalizationMap_algebraMap, squareHom_algebraMap, ← IsScalarTower.algebraMap_apply]

theorem chartSquareMorphism_toSpecField (hq : 0 < q.natDegree) {c : Fin 3} (hc : c ≠ 2) :
    chartSquareMorphism hq c hc ≫ toSpecField q =
      Proj.awayι (grading (expand k 2 q)) (var _ c)
        (var_mem_one _ (weights_eq_one_of_ne_two _ hc)) Nat.one_pos ≫
        toSpecField (expand k 2 q) := by
  rw [chartSquareMorphism, toSpecField, toSpecField, Category.assoc,
    Proj.awayι_toSpecZero_assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun r => chartSquareMap_chartStructureMap hq hc r)

/-- **The morphism is a morphism over `Spec k`.** -/
theorem squareMorphism_toSpecField (hq : 0 < q.natDegree) :
    squareMorphism q hq ≫ toSpecField q = toSpecField (expand k 2 q) := by
  refine (chartCover (expand k 2 q)).openCover.hom_ext _ _ fun a => ?_
  exact (Scheme.Cover.ι_glueMorphisms_assoc (chartCover (expand k 2 q)).openCover
    (squareChartFamily hq) _ a (toSpecField q)).trans
      (chartSquareMorphism_toSpecField hq (coverVar_ne_two a))

/-- **The morphism is proper.** -/
theorem isProper_squareMorphism (hq : 0 < q.natDegree) : IsProper (squareMorphism q hq) := by
  have : IsProper (squareMorphism q hq ≫ toSpecField q) := by
    rw [squareMorphism_toSpecField]
    exact isProper_toSpecField _
  have : IsSeparated (toSpecField q) := isSeparated_toSpecField q
  exact IsProper.of_comp (f := squareMorphism q hq) (g := toSpecField q)

/-! ### The morphism on the affine charts -/

theorem of_C_eq_algebraMap (p : k[X]) (r : k) :
    AdjoinRoot.of (X ^ 2 - C p : k[X][X]) (C r) = algebraMap k (HyperellipticCoordRing p) r := by
  rw [IsScalarTower.algebraMap_apply k k[X] (HyperellipticCoordRing p), AdjoinRoot.algebraMap_eq,
    Polynomial.algebraMap_eq]

theorem squareMap_algebraMap (r : k) :
    squareMap q (algebraMap k _ r) = algebraMap k _ r := by
  rw [← of_C_eq_algebraMap, squareMap_of, expand_C, of_C_eq_algebraMap]

theorem squareMap_algebraMap_X :
    squareMap q (algebraMap k[X] _ X) = algebraMap k[X] _ X ^ 2 := by
  rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.algebraMap_eq, squareMap_of, expand_X, map_pow]

variable {o c : Fin 3} {p p' : k[X]}

/-- The chart map on affine coordinate rings: `k[x, y]/(y^2 - p(x)) → k[x, y]/(y^2 - p'(x))`. -/
@[expose]
noncomputable def chartAffineSquareMap (hq : 0 < q.natDegree) (hqd : ChartData q o c p)
    (hfd : ChartData (expand k 2 q) o c p') :
    HyperellipticCoordRing p →+* HyperellipticCoordRing p' :=
  (chartToAffine hfd).comp ((chartSquareMap hq c hqd.ne_two').comp (affineToChart hqd))

theorem chartToAffine_comp_chartSquareMap (hq : 0 < q.natDegree) (hqd : ChartData q o c p)
    (hfd : ChartData (expand k 2 q) o c p') :
    (chartToAffine hfd).comp (chartSquareMap hq c hqd.ne_two') =
      (chartAffineSquareMap hq hqd hfd).comp (chartToAffine hqd) := by
  rw [chartAffineSquareMap, RingHom.comp_assoc, RingHom.comp_assoc, affineToChart_chartToAffine,
    RingHom.comp_id]

theorem chartAffineSquareMap_algebraMap (hq : 0 < q.natDegree) (hqd : ChartData q o c p)
    (hfd : ChartData (expand k 2 q) o c p') (r : k) :
    chartAffineSquareMap hq hqd hfd (algebraMap k _ r) = algebraMap k _ r := by
  rw [chartAffineSquareMap, RingHom.comp_apply, RingHom.comp_apply, affineToChart_algebraMap,
    chartSquareMap_chartStructureMap, chartToAffine_chartStructureMap]

theorem chartAffineSquareMap_X (hq : 0 < q.natDegree) (hqd : ChartData q o c p)
    (hfd : ChartData (expand k 2 q) o c p') :
    chartAffineSquareMap hq hqd hfd (algebraMap k[X] _ X) = algebraMap k[X] _ X ^ 2 := by
  rw [chartAffineSquareMap, RingHom.comp_apply, RingHom.comp_apply, affineToChart_X, chartX,
    chartSquareMap, scaledAwayMap_mk, chartToAffine_mk, squareHom_var_of_ne_two hq hqd.ne_two,
    map_pow, dehomogenize_var, chartValues_o _ hfd.ne hfd.ne_two]

theorem chartAffineSquareMap_root (hq : 0 < q.natDegree) (hqd : ChartData q o c p)
    (hfd : ChartData (expand k 2 q) o c p') :
    chartAffineSquareMap hq hqd hfd (AdjoinRoot.root _) =
      AdjoinRoot.root _ * chartValues c p' 1 ^ squareShift q := by
  rw [chartAffineSquareMap, RingHom.comp_apply, RingHom.comp_apply, affineToChart_root, chartY,
    chartSquareMap, scaledAwayMap_mk, chartToAffine_mk, squareHom_var_two, map_mul, map_pow,
    dehomogenize_var, dehomogenize_var, chartValues_two _ hfd.ne_two']

/-- On the chart `D₊(Z)` the map is `squareMap q`: `t ↦ x^2`, `y ↦ y`. -/
theorem chartAffineSquareMap_finite (hq : 0 < q.natDegree) :
    chartAffineSquareMap hq (chartData_finite q) (chartData_finite (expand k 2 q)) =
      squareMap q := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply]
      rw [of_C_eq_algebraMap, chartAffineSquareMap_algebraMap, squareMap_algebraMap]
    · simp only [RingHom.comp_apply]
      rw [← AdjoinRoot.algebraMap_eq, chartAffineSquareMap_X, squareMap_algebraMap_X]
  · rw [chartAffineSquareMap_root, squareMap_root, chartValues_c, one_pow, mul_one]

/-- On the chart `D₊(X)`: `x' ↦ u^2`. -/
theorem chartAffineSquareMap_infinite_algebraMap_X (hq : 0 < q.natDegree) :
    chartAffineSquareMap hq (chartData_infinite q) (chartData_infinite (expand k 2 q))
        (algebraMap k[X] _ X) = algebraMap k[X] _ X ^ 2 :=
  chartAffineSquareMap_X hq _ _

/-- On the chart `D₊(X)`: `w ↦ v u^e`. -/
theorem chartAffineSquareMap_infinite_root (hq : 0 < q.natDegree) :
    chartAffineSquareMap hq (chartData_infinite q) (chartData_infinite (expand k 2 q))
        (AdjoinRoot.root _) = AdjoinRoot.root _ * AdjoinRoot.of _ (X ^ squareShift q) := by
  rw [chartAffineSquareMap_root, chartValues_o _ (by decide : (1 : Fin 3) ≠ 0) (by decide),
    ← map_pow, AdjoinRoot.algebraMap_eq]

theorem chart_comp_squareMorphism (hq : 0 < q.natDegree) (hqd : ChartData q o c p)
    (hfd : ChartData (expand k 2 q) o c p')
    (hcomp : Proj.awayι (grading (expand k 2 q)) (var _ c) (var_mem_one _ hfd.weight_c)
        Nat.one_pos ≫ squareMorphism q hq = chartSquareMorphism hq c hqd.ne_two') :
    chart hfd ≫ squareMorphism q hq =
      Spec.map (CommRingCat.ofHom (chartAffineSquareMap hq hqd hfd)) ≫ chart hqd := by
  rw [chart, chart, Category.assoc, hcomp, chartSquareMorphism, ← Spec.map_comp_assoc,
    ← Spec.map_comp_assoc]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext fun z =>
    RingHom.congr_fun (chartToAffine_comp_chartSquareMap hq hqd hfd) z)

/-- **On the affine charts `y^2 = q(x^2)` and `y^2 = q(t)`, the morphism is `Spec` of
`squareMap q`** (`t ↦ x^2`, `y ↦ y`). -/
theorem affineChart_comp_squareMorphism (hq : 0 < q.natDegree) :
    affineChart (expand k 2 q) ≫ squareMorphism q hq =
      Spec.map (CommRingCat.ofHom (squareMap q)) ≫ affineChart q := by
  have h := chart_comp_squareMorphism hq (chartData_finite q) (chartData_finite (expand k 2 q))
    (awayι_one_comp_squareMorphism hq)
  rw [chartAffineSquareMap_finite] at h
  exact h

/-- On the charts at infinity, the morphism is `Spec` of `x' ↦ u^2`, `w ↦ v u^e`. -/
theorem affineChartAtInfinity_comp_squareMorphism (hq : 0 < q.natDegree) :
    affineChartAtInfinity (expand k 2 q) ≫ squareMorphism q hq =
      Spec.map (CommRingCat.ofHom (chartAffineSquareMap hq (chartData_infinite q)
        (chartData_infinite (expand k 2 q)))) ≫ affineChartAtInfinity q :=
  chart_comp_squareMorphism hq (chartData_infinite q) (chartData_infinite (expand k 2 q))
    (awayι_zero_comp_squareMorphism hq)

/-! ### Injectivity and integrality on the charts; surjectivity -/

theorem exists_eq_of_mul_root_add_of (a : k[X]) (z : HyperellipticCoordRing a) :
    ∃ α β : k[X], z = AdjoinRoot.of _ α * AdjoinRoot.root _ + AdjoinRoot.of _ β := by
  obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective z
  have hmon : (X ^ 2 - C a : k[X][X]).Monic := monic_X_pow_sub_C a two_ne_zero
  have hne : (X ^ 2 - C a : k[X][X]) ≠ 1 := fun h => by
    have := congrArg natDegree h
    rw [natDegree_X_pow_sub_C, natDegree_one] at this
    omega
  have hdeg : (P %ₘ (X ^ 2 - C a)).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt P hmon hne
    rw [natDegree_X_pow_sub_C] at this
    omega
  refine ⟨(P %ₘ (X ^ 2 - C a)).coeff 1, (P %ₘ (X ^ 2 - C a)).coeff 0, ?_⟩
  have h1 : AdjoinRoot.mk (X ^ 2 - C a) P = AdjoinRoot.mk _ (P %ₘ (X ^ 2 - C a)) := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨_, sub_eq_iff_eq_add.mpr ((modByMonic_add_div P _).symm.trans (add_comm _ _))⟩
  rw [h1]
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hdeg]
  rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X]

theorem eq_zero_of_of_mul_root_add_of (b : k[X]) {P Q : k[X]}
    (h : AdjoinRoot.of (X ^ 2 - C b : k[X][X]) P * AdjoinRoot.root _ + AdjoinRoot.of _ Q = 0) :
    P = 0 ∧ Q = 0 := by
  have h' : AdjoinRoot.mk (X ^ 2 - C b) (C P * X + C Q) = 0 := by
    rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    exact h
  rw [AdjoinRoot.mk_eq_zero] at h'
  have h0 : C P * X + C Q = 0 := by
    refine eq_zero_of_dvd_of_natDegree_lt h' ?_
    rw [natDegree_X_pow_sub_C]
    exact natDegree_linear_le.trans_lt one_lt_two
  constructor
  · simpa using congrArg (coeff · 1) h0
  · simpa using congrArg (coeff · 0) h0

/-- A map `k[x, y]/(y^2 - a(x)) → k[x, y]/(y^2 - b(x))` with `x ↦ x^2`, `y ↦ y c(x)`,
`c ≠ 0`, is injective and integral. -/
theorem injective_isIntegral_of_square {a b c : k[X]} (hc : c ≠ 0)
    (ψ : HyperellipticCoordRing a →+* HyperellipticCoordRing b)
    (hC : ∀ r : k, ψ (AdjoinRoot.of _ (C r)) = AdjoinRoot.of _ (C r))
    (hX : ψ (AdjoinRoot.of _ (X : k[X])) = AdjoinRoot.of _ (X : k[X]) ^ 2)
    (hroot : ψ (AdjoinRoot.root _) = AdjoinRoot.root _ * AdjoinRoot.of _ c) :
    Function.Injective ψ ∧ ψ.IsIntegral := by
  have hof : ∀ p : k[X], ψ (AdjoinRoot.of _ p) = AdjoinRoot.of _ (expand k 2 p) := by
    intro p
    have := Polynomial.ringHom_ext (f := ψ.comp (AdjoinRoot.of _))
      (g := (AdjoinRoot.of (X ^ 2 - C b : k[X][X])).comp
        (expand k 2 : k[X] →ₐ[k] k[X]).toRingHom)
      (fun r => by simp [hC]) (by simp [hX])
    exact RingHom.congr_fun this p
  refine ⟨(injective_iff_map_eq_zero ψ).mpr fun z hz => ?_, ?_⟩
  · obtain ⟨α, β, rfl⟩ := exists_eq_of_mul_root_add_of a z
    have e : AdjoinRoot.of (X ^ 2 - C b : k[X][X]) (expand k 2 α) *
        (AdjoinRoot.root _ * AdjoinRoot.of _ c) =
        AdjoinRoot.of _ (expand k 2 α * c) * AdjoinRoot.root _ := by
      rw [map_mul]
      ring
    rw [map_add, map_mul, hof, hof, hroot, e] at hz
    obtain ⟨h1, h2⟩ := eq_zero_of_of_mul_root_add_of b hz
    have hα : α = 0 := (expand_eq_zero two_pos).mp ((mul_eq_zero.mp h1).resolve_right hc)
    have hβ : β = 0 := (expand_eq_zero two_pos).mp h2
    rw [hα, hβ, map_zero, zero_mul, zero_add]
  · let _ := ψ.toAlgebra
    have hXi : IsIntegral (HyperellipticCoordRing a)
        (AdjoinRoot.of (X ^ 2 - C b : k[X][X]) (X : k[X])) := by
      refine IsIntegral.of_pow two_pos ?_
      rw [← hX]
      exact isIntegral_algebraMap
    have hpoly : ∀ p : k[X], IsIntegral (HyperellipticCoordRing a)
        (AdjoinRoot.of (X ^ 2 - C b : k[X][X]) p) := by
      intro p
      induction p using Polynomial.induction_on with
      | C r =>
        rw [← hC r]
        exact isIntegral_algebraMap
      | add p p' hp hp' =>
        rw [map_add]
        exact hp.add hp'
      | monomial n r hp =>
        rw [pow_succ (X : k[X]) n, ← mul_assoc, map_mul]
        exact hp.mul hXi
    have hr : IsIntegral (HyperellipticCoordRing a) (AdjoinRoot.root (X ^ 2 - C b : k[X][X])) :=
      IsIntegral.of_pow two_pos (by rw [root_sq_eq_of]; exact hpoly b)
    intro z
    obtain ⟨α, β, rfl⟩ := exists_eq_of_mul_root_add_of b z
    exact ((hpoly α).mul hr).add (hpoly β)

theorem injective_isIntegral_chartSquareMap (hq : 0 < q.natDegree) (hqd : ChartData q o c p)
    (hfd : ChartData (expand k 2 q) o c p')
    (h : Function.Injective (chartAffineSquareMap hq hqd hfd) ∧
      (chartAffineSquareMap hq hqd hfd).IsIntegral) :
    Function.Injective (chartSquareMap hq c hqd.ne_two') ∧
      (chartSquareMap hq c hqd.ne_two').IsIntegral := by
  have e : chartSquareMap hq c hqd.ne_two' =
      (affineToChart hfd).comp ((chartAffineSquareMap hq hqd hfd).comp (chartToAffine hqd)) := by
    rw [chartAffineSquareMap, RingHom.comp_assoc, RingHom.comp_assoc, affineToChart_chartToAffine,
      RingHom.comp_id, ← RingHom.comp_assoc, affineToChart_chartToAffine, RingHom.id_comp]
  have l1 : Function.LeftInverse (chartToAffine hfd) (affineToChart hfd) := fun z =>
    RingHom.congr_fun (chartToAffine_affineToChart hfd) z
  have l2 : Function.LeftInverse (affineToChart hfd) (chartToAffine hfd) := fun z =>
    RingHom.congr_fun (affineToChart_chartToAffine hfd) z
  have l3 : Function.LeftInverse (chartToAffine hqd) (affineToChart hqd) := fun z =>
    RingHom.congr_fun (chartToAffine_affineToChart hqd) z
  have l4 : Function.LeftInverse (affineToChart hqd) (chartToAffine hqd) := fun z =>
    RingHom.congr_fun (affineToChart_chartToAffine hqd) z
  rw [e]
  refine ⟨?_, ?_⟩
  · rw [RingHom.coe_comp, RingHom.coe_comp]
    exact l1.injective.comp (h.1.comp l4.injective)
  · exact RingHom.IsIntegral.trans (hf := RingHom.IsIntegral.trans
      (hf := RingHom.isIntegral_of_surjective (hf := l3.surjective)) (hg := h.2))
      (hg := RingHom.isIntegral_of_surjective (hf := l2.surjective))

theorem injective_isIntegral_chartSquareMap_one (hq : 0 < q.natDegree) :
    Function.Injective (chartSquareMap hq 1 (chartData_finite q).ne_two') ∧
      (chartSquareMap hq 1 (chartData_finite q).ne_two').IsIntegral := by
  refine injective_isIntegral_chartSquareMap hq (chartData_finite q)
    (chartData_finite (expand k 2 q)) ?_
  rw [chartAffineSquareMap_finite]
  refine injective_isIntegral_of_square one_ne_zero (squareMap q) (fun r => ?_) ?_ ?_
  · rw [squareMap_of, expand_C]
  · rw [squareMap_of, expand_X, map_pow]
  · rw [squareMap_root, map_one, mul_one]

theorem injective_isIntegral_chartSquareMap_zero (hq : 0 < q.natDegree) :
    Function.Injective (chartSquareMap hq 0 (chartData_infinite q).ne_two') ∧
      (chartSquareMap hq 0 (chartData_infinite q).ne_two').IsIntegral := by
  refine injective_isIntegral_chartSquareMap hq (chartData_infinite q)
    (chartData_infinite (expand k 2 q)) ?_
  refine injective_isIntegral_of_square (pow_ne_zero _ X_ne_zero) _ (fun r => ?_) ?_
    (chartAffineSquareMap_infinite_root hq)
  · rw [of_C_eq_algebraMap, of_C_eq_algebraMap, chartAffineSquareMap_algebraMap]
  · have := chartAffineSquareMap_infinite_algebraMap_X hq
    rwa [AdjoinRoot.algebraMap_eq, AdjoinRoot.algebraMap_eq] at this

theorem surjective_specMap_of_isIntegral {R S : Type u} [CommRing R] [CommRing S] (θ : R →+* S)
    (hinj : Function.Injective θ) (hint : θ.IsIntegral) :
    Function.Surjective (Spec.map (CommRingCat.ofHom θ)) := by
  intro z
  obtain ⟨w, hw⟩ := hint.comap_surjective hinj z
  exact ⟨w, (Spec.map_apply (f := CommRingCat.ofHom θ) (x := w)).trans hw⟩

/-- On `D₊(Z)`, the chart map `Spec (S_f)_{(Z)} → Spec (S_q)_{(Z)}` is integral. -/
theorem isIntegralHom_chartSquareMorphism_one (hq : 0 < q.natDegree) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom (chartSquareMap hq 1
      (chartData_finite q).ne_two'))) :=
  IsIntegralHom.SpecMap_iff.mpr (injective_isIntegral_chartSquareMap_one hq).2

/-- On `D₊(X)`, the chart map `Spec (S_f)_{(X)} → Spec (S_q)_{(X)}` is integral. -/
theorem isIntegralHom_chartSquareMorphism_zero (hq : 0 < q.natDegree) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom (chartSquareMap hq 0
      (chartData_infinite q).ne_two'))) :=
  IsIntegralHom.SpecMap_iff.mpr (injective_isIntegral_chartSquareMap_zero hq).2

theorem exists_squareMorphism_eq (hq : 0 < q.natDegree) {c : Fin 3} (hc : c ≠ 2)
    (hcomp : Proj.awayι (grading (expand k 2 q)) (var _ c)
        (var_mem_one _ (weights_eq_one_of_ne_two _ hc)) Nat.one_pos ≫ squareMorphism q hq =
      chartSquareMorphism hq c hc)
    (hsurj : Function.Surjective (Spec.map (CommRingCat.ofHom (chartSquareMap hq c hc))))
    {y : projectiveModel q} (hy : y ∈ Proj.basicOpen (grading q) (var q c)) :
    ∃ x, squareMorphism q hq x = y := by
  have hy' : y ∈ (Proj.awayι (grading q) (var q c)
      (var_mem_one q (weights_eq_one_of_ne_two _ hc)) Nat.one_pos).opensRange := by
    rw [Proj.opensRange_awayι]
    exact hy
  obtain ⟨z, rfl⟩ := hy'
  obtain ⟨w, rfl⟩ := hsurj z
  refine ⟨Proj.awayι (grading (expand k 2 q)) (var _ c)
    (var_mem_one _ (weights_eq_one_of_ne_two _ hc)) Nat.one_pos w, ?_⟩
  rw [← Scheme.Hom.comp_apply (Proj.awayι (grading (expand k 2 q)) (var _ c)
    (var_mem_one _ (weights_eq_one_of_ne_two _ hc)) Nat.one_pos) (squareMorphism q hq) w, hcomp,
    chartSquareMorphism, Scheme.Hom.comp_apply]

/-- **The morphism is surjective.** -/
theorem surjective_squareMorphism (hq : 0 < q.natDegree) : Surjective (squareMorphism q hq) := by
  refine ⟨fun y => ?_⟩
  have hy : y ∈ Proj.basicOpen (grading q) (var q 1) ⊔ Proj.basicOpen (grading q) (var q 0) := by
    rw [iSup_chart_eq_top q]
    trivial
  rw [TopologicalSpace.Opens.mem_sup] at hy
  rcases hy with hy | hy
  · exact exists_squareMorphism_eq hq (chartData_finite q).ne_two'
      (awayι_one_comp_squareMorphism hq)
      (surjective_specMap_of_isIntegral _ (injective_isIntegral_chartSquareMap_one hq).1
        (injective_isIntegral_chartSquareMap_one hq).2) hy
  · exact exists_squareMorphism_eq hq (chartData_infinite q).ne_two'
      (awayι_zero_comp_squareMorphism hq)
      (surjective_specMap_of_isIntegral _ (injective_isIntegral_chartSquareMap_zero hq).1
        (injective_isIntegral_chartSquareMap_zero hq).2) hy

/-! ### Degree two on the affine chart -/

/-- `squareMap q` is finite (free of rank two, `free_and_finrank_squareMap`). -/
theorem finite_squareMap (q : k[X]) : (squareMap q).Finite := by
  have : Nontrivial (HyperellipticCoordRing q) :=
    (AdjoinRoot.nontrivial_iff_of_monic (monic_X_pow_sub_C q two_ne_zero)).2
      (natDegree_pos_iff_degree_pos.1 (by rw [natDegree_X_pow_sub_C]; exact two_pos))
  let _ := (squareMap q).toAlgebra
  have h := free_and_finrank_squareMap q rfl
  have := h.1
  exact Module.finite_of_finrank_pos (by rw [h.2]; exact two_pos)

/-- On the affine chart the morphism is `Spec (squareMap q)`, which is finite. -/
theorem isFinite_specMap_squareMap (q : k[X]) :
    IsFinite (Spec.map (CommRingCat.ofHom (squareMap q))) :=
  (IsFinite.SpecMap_iff _).mpr (finite_squareMap q)

end Hyperelliptic

/-! ### The derivative families -/

section DerivativeFamily

open Polynomial AlgebraicGeometry CategoryTheory Hyperelliptic

theorem natDegree_reducedGegenbauerSquare_pos {m : ℕ} (hm : 0 < m) (r δ : ℕ) :
    0 < (reducedGegenbauerSquare m r δ).natDegree := by
  rw [natDegree_reducedGegenbauerSquare]
  exact hm

theorem eqToHom_comp_toSpecField {k : Type u} [Field k] {p p' : Polynomial k} (h : p = p') :
    eqToHom (congrArg projectiveModel h) ≫ toSpecField p' = toSpecField p := by
  subst h
  simp

/-- **The degree-two morphism `{y^2 = F_{m,r,δ}(x)} → {y^2 = Q_{m,r,δ}(t)}`,
`(x, y) ↦ (x^2, y)`, of the projective models**, for `m ≥ 1`
(`F_{m,r,δ} = Q_{m,r,δ}(x^2)`, `expand_reducedGegenbauerSquare`). -/
@[expose]
noncomputable def derivativeSquareMorphism (m r δ : ℕ) (hm : 0 < m) :
    projectiveModel (reducedGegenbauer m r δ) ⟶ projectiveModel (reducedGegenbauerSquare m r δ) :=
  eqToHom (congrArg projectiveModel (expand_reducedGegenbauerSquare m r δ).symm) ≫
    squareMorphism _ (natDegree_reducedGegenbauerSquare_pos hm r δ)

theorem derivativeSquareMorphism_toSpecField (m r δ : ℕ) (hm : 0 < m) :
    derivativeSquareMorphism m r δ hm ≫ toSpecField (reducedGegenbauerSquare m r δ) =
      toSpecField (reducedGegenbauer m r δ) := by
  rw [derivativeSquareMorphism, Category.assoc, squareMorphism_toSpecField,
    eqToHom_comp_toSpecField (expand_reducedGegenbauerSquare m r δ).symm]

theorem surjective_eqToHom_comp {k : Type u} [Field k] {p p' : Polynomial k} (h : p = p')
    {Y : Scheme.{u}} (g : projectiveModel p' ⟶ Y) (hg : Surjective g) :
    Surjective (eqToHom (congrArg projectiveModel h) ≫ g) := by
  subst h
  simpa using hg

theorem isProper_eqToHom_comp {k : Type u} [Field k] {p p' : Polynomial k} (h : p = p')
    {Y : Scheme.{u}} (g : projectiveModel p' ⟶ Y) (hg : IsProper g) :
    IsProper (eqToHom (congrArg projectiveModel h) ≫ g) := by
  subst h
  simpa using hg

theorem surjective_derivativeSquareMorphism (m r δ : ℕ) (hm : 0 < m) :
    Surjective (derivativeSquareMorphism m r δ hm) :=
  surjective_eqToHom_comp (expand_reducedGegenbauerSquare m r δ).symm _
    (surjective_squareMorphism _)

theorem isProper_derivativeSquareMorphism (m r δ : ℕ) (hm : 0 < m) :
    IsProper (derivativeSquareMorphism m r δ hm) :=
  isProper_eqToHom_comp (expand_reducedGegenbauerSquare m r δ).symm _
    (isProper_squareMorphism _)

/-- On the affine charts the morphism is `Spec` of `t ↦ x^2`, `y ↦ y`
(`ℚ[t, y]/(y^2 - Q_{m,r,δ}(t)) → ℚ[x, y]/(y^2 - Q_{m,r,δ}(x^2))`). -/
theorem affineChart_comp_derivativeSquareMorphism (m r δ : ℕ) (hm : 0 < m) :
    affineChart (expand ℚ 2 (reducedGegenbauerSquare m r δ)) ≫
        squareMorphism _ (natDegree_reducedGegenbauerSquare_pos hm r δ) =
      Spec.map (CommRingCat.ofHom (squareMap (reducedGegenbauerSquare m r δ))) ≫
        affineChart (reducedGegenbauerSquare m r δ) :=
  affineChart_comp_squareMorphism _

end DerivativeFamily

end ArithmeticOfJacobiPolynomials
