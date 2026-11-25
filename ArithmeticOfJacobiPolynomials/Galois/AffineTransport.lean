/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.Defs
public import ArithmeticOfJacobiPolynomials.Jacobi.IntegralNormalization
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Algebra.Polynomial.Splits

/-!
# Transport of Galois cycles along affine changes of variable

For a field `F`, `f ∈ F[X]` and `a, b ∈ Fˣ`, `c ∈ F`, the polynomial
`g = a · f(bX + c)` has the roots `(x - c)/b`, `x` a root of `f`, in the splitting field of `f`.
Every `σ ∈ Gal(f/F)` induces `τ ∈ Gal(g/F)` whose action on the roots of `g` is conjugate to
that of `σ` on the roots of `f` (`exists_galPerm_eq_permCongr_affine`). Hence single cycles,
with their lengths, transfer between `f` and `g` in both directions; when `c = 0` the
conjugating bijection commutes with negation, so the property "`π^k` negates every point of
the support" transfers as well.

This is used in Proposition 5.2: `K_n = u^n n! P_n^{(α,β)}(1 + (2D/u) X)` and
`K_n((uc/2D) X^2) = u^n n! P_n^{(α,β)}(1 + c X^2)` (`integralJacobi_map`,
`integralJacobi_map_comp_C_mul_X_sq`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-! ### Conjugate permutations -/

section PermCongr

variable {α β : Type*}

theorem permCongr_zpow (e : α ≃ β) (σ : Equiv.Perm α) (i : ℤ) :
    e.permCongr σ ^ i = e.permCongr (σ ^ i) :=
  (map_zpow e.permCongrHom σ i).symm

theorem isCycle_permCongr (e : α ≃ β) {σ : Equiv.Perm α} (hσ : σ.IsCycle) :
    (e.permCongr σ).IsCycle := by
  obtain ⟨x, hx, hall⟩ := hσ
  refine ⟨e x, ?_, ?_⟩
  · rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    exact fun h => hx (e.injective h)
  · intro y hy
    have hy' : σ (e.symm y) ≠ e.symm y := by
      intro h; apply hy; rw [Equiv.permCongr_apply, h, Equiv.apply_symm_apply]
    obtain ⟨i, hi⟩ := hall hy'
    refine ⟨i, ?_⟩
    rw [permCongr_zpow, Equiv.permCongr_apply, Equiv.symm_apply_apply, hi,
      Equiv.apply_symm_apply]

theorem support_permCongr [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (σ : Equiv.Perm α) : (e.permCongr σ).support = σ.support.map e.toEmbedding := by
  ext y
  rw [Finset.mem_map_equiv, Equiv.Perm.mem_support, Equiv.Perm.mem_support,
    Equiv.permCongr_apply]
  exact not_congr (by rw [Equiv.eq_symm_apply])

theorem card_support_permCongr [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (σ : Equiv.Perm α) : (e.permCongr σ).support.card = σ.support.card := by
  rw [support_permCongr, Finset.card_map]

end PermCongr

/-! ### Affine changes of variable -/

variable {F : Type*} [Field F]

/-- `a f(bX + c) ≠ 0` for `f ≠ 0`, `a, b ≠ 0`. -/
theorem C_mul_comp_affine_ne_zero {f : F[X]} {a b : F} (c : F) (hf : f ≠ 0) (ha : a ≠ 0)
    (hb : b ≠ 0) : C a * f.comp (C b * X + C c) ≠ 0 := by
  refine mul_ne_zero (C_ne_zero.mpr ha) ?_
  rw [Ne, comp_eq_zero_iff]
  rintro (h | ⟨_, h⟩)
  · exact hf h
  · have := congrArg (fun q => q.coeff 1) h
    exact hb (by simpa using this)

/-- Inverting an affine change of variable. -/
theorem eq_C_mul_comp_affine_inv {f g : F[X]} {a b c : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (hg : g = C a * f.comp (C b * X + C c)) :
    f = C a⁻¹ * g.comp (C b⁻¹ * X + C (-(c / b))) := by
  have hlin : (C b * X + C c).comp (C b⁻¹ * X + C (-(c / b))) = X := by
    simp only [add_comp, mul_comp, C_comp, X_comp]
    rw [mul_add, ← mul_assoc, ← C_mul, ← C_mul, mul_inv_cancel₀ hb, C_1, one_mul,
      add_assoc, ← C_add]
    rw [show b * -(c / b) + c = 0 by field_simp; ring, C_0, add_zero]
  rw [hg, mul_comp, C_comp, comp_assoc, hlin, comp_X, ← mul_assoc, ← C_mul,
    inv_mul_cancel₀ ha, C_1, one_mul]

variable (f : F[X]) {a b : F} (c : F)

private lemma aeval_affine {E : Type*} [Field E] [Algebra F E] (y : E) :
    aeval y (C a * f.comp (C b * X + C c)) =
      algebraMap F E a * aeval (algebraMap F E b * y + algebraMap F E c) f := by
  simp [aeval_comp]

/-- The bijection `x ↦ (x - c)/b` from the roots of `f` to the roots of `a f(bX + c)`. -/
noncomputable def affineRootsEquiv (ha : a ≠ 0) (hb : b ≠ 0) (E : Type*) [Field E]
    [Algebra F E] : f.rootSet E ≃ (C a * f.comp (C b * X + C c)).rootSet E where
  toFun x := ⟨(algebraMap F E b)⁻¹ * ((x : E) - algebraMap F E c), by
    have hx := x.2
    have hb' : algebraMap F E b ≠ 0 := (_root_.map_ne_zero _).mpr hb
    rw [mem_rootSet] at hx ⊢
    refine ⟨C_mul_comp_affine_ne_zero c hx.1 ha hb, ?_⟩
    rw [aeval_affine, ← mul_assoc, mul_inv_cancel₀ hb', one_mul, sub_add_cancel, hx.2,
      mul_zero]⟩
  invFun y := ⟨algebraMap F E b * (y : E) + algebraMap F E c, by
    have hy := y.2
    have hf : f ≠ 0 := by
      rintro rfl; simp at hy
    rw [mem_rootSet] at hy ⊢
    refine ⟨hf, ?_⟩
    rw [aeval_affine] at hy
    exact (mul_eq_zero.mp hy.2).resolve_left ((_root_.map_ne_zero _).mpr ha)⟩
  left_inv x := by
    have hb' : algebraMap F E b ≠ 0 := (_root_.map_ne_zero _).mpr hb
    ext; simp only; rw [← mul_assoc, mul_inv_cancel₀ hb', one_mul, sub_add_cancel]
  right_inv y := by
    have hb' : algebraMap F E b ≠ 0 := (_root_.map_ne_zero _).mpr hb
    ext; simp only; rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ hb', one_mul]

theorem coe_affineRootsEquiv (ha : a ≠ 0) (hb : b ≠ 0) (E : Type*) [Field E] [Algebra F E]
    (x : f.rootSet E) : (affineRootsEquiv f c ha hb E x : E) =
      (algebraMap F E b)⁻¹ * ((x : E) - algebraMap F E c) := (rfl)

theorem fact_splits_affine :
    Fact (((C a * f.comp (C b * X + C c)).map (algebraMap F f.SplittingField)).Splits) := by
  refine ⟨?_⟩
  rw [Polynomial.map_mul, map_C, Polynomial.map_comp]
  refine Splits.C_mul (Splits.comp_of_degree_le_one (SplittingField.splits f) ?_) _
  simp only [Polynomial.map_add, Polynomial.map_mul, map_C, map_X]
  exact degree_linear_le

/-- **Affine transport of the root action.** For `g = a f(bX + c)` with `a, b ≠ 0` and
`σ ∈ Gal(f/F)` there are `τ ∈ Gal(g/F)` and a bijection `e` from the roots of `f` to those
of `g` with `galPerm g τ = e ∘ galPerm f σ ∘ e⁻¹`; when `c = 0`, `e` commutes with
negation. -/
theorem exists_galPerm_eq_permCongr_affine (ha : a ≠ 0) (hb : b ≠ 0) (σ : f.Gal) :
    ∃ (τ : (C a * f.comp (C b * X + C c)).Gal)
      (e : f.rootSet f.SplittingField ≃
        (C a * f.comp (C b * X + C c)).rootSet (C a * f.comp (C b * X + C c)).SplittingField),
      galPerm _ τ = e.permCongr (galPerm f σ) ∧
      (c = 0 → ∀ x y : f.rootSet f.SplittingField,
        (y : f.SplittingField) = -(x : f.SplittingField) →
        ((e y : _) : (C a * f.comp (C b * X + C c)).SplittingField) =
          -((e x : _) : (C a * f.comp (C b * X + C c)).SplittingField)) := by
  set g := C a * f.comp (C b * X + C c) with hg
  set E := f.SplittingField
  have hfact : Fact ((g.map (algebraMap F E)).Splits) := fact_splits_affine f c
  set ψ := Gal.rootsEquivRootsAux g E with hψ
  set A := affineRootsEquiv f c ha hb E with hA
  set τ := Gal.restrict g E σ with hτ
  have hψcoe : ∀ w : g.rootSet g.SplittingField,
      ((ψ w : E)) = IsScalarTower.toAlgHom F g.SplittingField E (w : g.SplittingField) :=
    fun w => rfl
  refine ⟨τ, A.trans ψ.symm, ?_, ?_⟩
  · ext1 y
    rw [Equiv.permCongr_apply]
    apply ψ.injective
    rw [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.symm_trans_apply, Equiv.symm_symm]
    have h1 : ψ (galPerm g τ y) = τ • ψ y := by
      rw [hψ, Gal.smul_def, Equiv.symm_apply_apply, galPerm_apply]
    rw [h1]
    apply Subtype.ext
    have h3 := Gal.restrict_smul (p := g) (E := E) σ (ψ y)
    rw [hτ, h3, coe_affineRootsEquiv, galPerm_apply]
    change σ (ψ y : E) = (algebraMap F E b)⁻¹ * (σ ((A.symm (ψ y) : E)) - algebraMap F E c)
    have h2 : ((ψ y : E)) = A (A.symm (ψ y)) := by rw [Equiv.apply_symm_apply]
    conv_lhs => rw [h2, coe_affineRootsEquiv]
    have hcb : σ (algebraMap F E b) = algebraMap F E b := AlgEquiv.commutes (σ : E ≃ₐ[F] E) b
    have hcc : σ (algebraMap F E c) = algebraMap F E c := AlgEquiv.commutes (σ : E ≃ₐ[F] E) c
    rw [map_mul, map_inv₀, map_sub, hcb, hcc]
  · intro hc x y hxy
    subst hc
    have hinj := (IsScalarTower.toAlgHom F g.SplittingField E).toRingHom.injective
    apply hinj
    change ((ψ (ψ.symm (A y)) : E)) = IsScalarTower.toAlgHom F g.SplittingField E
      (-((ψ.symm (A x) : g.SplittingField)))
    rw [map_neg, ← hψcoe, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      coe_affineRootsEquiv, coe_affineRootsEquiv, hxy]
    simp only [map_zero, sub_zero]
    ring

/-- **The splitting field is unchanged by an affine change of variable.** The splitting field of
`f` is a splitting field of `a f(bX + c)` for `a, b ≠ 0`: the roots of the latter are
`(x - c)/b`, `x` a root of `f`, so they generate the same field. -/
theorem isSplittingField_affine (ha : a ≠ 0) (hb : b ≠ 0) :
    Polynomial.IsSplittingField F f.SplittingField (C a * f.comp (C b * X + C c)) := by
  refine ⟨(fact_splits_affine f c (a := a) (b := b)).out, ?_⟩
  rw [eq_top_iff, ← SplittingField.adjoin_rootSet f, Algebra.adjoin_le_iff]
  intro x hx
  set A := affineRootsEquiv f c ha hb f.SplittingField with hA
  have hxA : (A ⟨x, hx⟩).1 ∈
      Algebra.adjoin F
        ((C a * f.comp (C b * X + C c)).rootSet f.SplittingField : Set f.SplittingField) :=
    Algebra.subset_adjoin (A ⟨x, hx⟩).2
  have hb' : algebraMap F f.SplittingField b ≠ 0 := (_root_.map_ne_zero _).mpr hb
  have hx' : x = algebraMap F f.SplittingField b * (A ⟨x, hx⟩).1 +
      algebraMap F f.SplittingField c := by
    rw [hA, coe_affineRootsEquiv, ← mul_assoc, mul_inv_cancel₀ hb', one_mul, sub_add_cancel]
  rw [hx']
  exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ b) hxA) (Subalgebra.algebraMap_mem _ c)

/-- **Isomorphic splitting fields.** For `a, b ≠ 0`, the splitting fields of `f` and of
`a f(bX + c)` over `F` are isomorphic `F`-algebras. -/
noncomputable def splittingFieldAffineEquiv (ha : a ≠ 0) (hb : b ≠ 0) :
    f.SplittingField ≃ₐ[F] (C a * f.comp (C b * X + C c)).SplittingField :=
  haveI := isSplittingField_affine f c ha hb
  Polynomial.IsSplittingField.algEquiv f.SplittingField (C a * f.comp (C b * X + C c))

/-- A single cycle of length `d` in `Gal(f/F)` gives one in `Gal(a f(bX + c)/F)`. -/
theorem exists_isCycle_galPerm_affine (ha : a ≠ 0) (hb : b ≠ 0) {d : ℕ} (σ : f.Gal)
    [DecidableEq (f.rootSet f.SplittingField)]
    [DecidableEq ((C a * f.comp (C b * X + C c)).rootSet
      (C a * f.comp (C b * X + C c)).SplittingField)]
    (hσ : (galPerm f σ).IsCycle) (hd : (galPerm f σ).support.card = d) :
    ∃ τ : (C a * f.comp (C b * X + C c)).Gal,
      (galPerm _ τ).IsCycle ∧ (galPerm _ τ).support.card = d := by
  obtain ⟨τ, e, he, -⟩ := exists_galPerm_eq_permCongr_affine f c ha hb σ
  refine ⟨τ, ?_, ?_⟩
  · rw [he]; exact isCycle_permCongr e hσ
  · rw [he, card_support_permCongr, hd]

/-- A single cycle of length `d` whose `k`-th power negates every point of its support
transfers from `Gal(f/F)` to `Gal(a f(bX)/F)`. -/
theorem exists_isCycle_galPerm_scale (ha : a ≠ 0) (hb : b ≠ 0) {d k : ℕ} (σ : f.Gal)
    [DecidableEq (f.rootSet f.SplittingField)]
    [DecidableEq ((C a * f.comp (C b * X + C 0)).rootSet
      (C a * f.comp (C b * X + C 0)).SplittingField)]
    (hσ : (galPerm f σ).IsCycle) (hd : (galPerm f σ).support.card = d)
    (hneg : ∀ x ∈ (galPerm f σ).support,
      (((galPerm f σ ^ k) x : f.rootSet f.SplittingField) : f.SplittingField) = -(x : _)) :
    ∃ τ : (C a * f.comp (C b * X + C 0)).Gal,
      (galPerm _ τ).IsCycle ∧ (galPerm _ τ).support.card = d ∧
      ∀ y ∈ (galPerm _ τ).support,
        (((galPerm _ τ ^ k) y : (C a * f.comp (C b * X + C 0)).rootSet _) :
          (C a * f.comp (C b * X + C 0)).SplittingField) = -(y : _) := by
  obtain ⟨τ, e, he, hneg'⟩ := exists_galPerm_eq_permCongr_affine f 0 ha hb σ
  refine ⟨τ, ?_, ?_, ?_⟩
  · rw [he]; exact isCycle_permCongr e hσ
  · rw [he, card_support_permCongr, hd]
  · intro y hy
    rw [he, support_permCongr, Finset.mem_map_equiv] at hy
    rw [he, ← zpow_natCast, permCongr_zpow, zpow_natCast, Equiv.permCongr_apply]
    have := hneg' rfl (e.symm y) _ (hneg _ hy)
    rw [Equiv.apply_symm_apply] at this
    exact this

/-- A single cycle of length `d` in `Gal(a f(bX + c)/F)` gives one in `Gal(f/F)`. -/
theorem exists_isCycle_galPerm_of_affine {g : F[X]} (ha : a ≠ 0) (hb : b ≠ 0) {d : ℕ}
    (hg : g = C a * f.comp (C b * X + C c)) (τ : g.Gal)
    [DecidableEq (f.rootSet f.SplittingField)] [DecidableEq (g.rootSet g.SplittingField)]
    (hτ : (galPerm g τ).IsCycle) (hd : (galPerm g τ).support.card = d) :
    ∃ σ : f.Gal, (galPerm f σ).IsCycle ∧ (galPerm f σ).support.card = d := by
  have hf := eq_C_mul_comp_affine_inv ha hb hg
  subst hf
  exact exists_isCycle_galPerm_affine g (-(c / b)) (inv_ne_zero ha) (inv_ne_zero hb) τ hτ hd

/-- Variant of `exists_isCycle_galPerm_scale` with the target polynomial named. -/
theorem exists_isCycle_galPerm_scale_of_eq {g : F[X]} (ha : a ≠ 0) (hb : b ≠ 0) {d k : ℕ}
    (hg : g = C a * f.comp (C b * X + C 0)) (σ : f.Gal)
    [DecidableEq (f.rootSet f.SplittingField)] [DecidableEq (g.rootSet g.SplittingField)]
    (hσ : (galPerm f σ).IsCycle) (hd : (galPerm f σ).support.card = d)
    (hneg : ∀ x ∈ (galPerm f σ).support,
      (((galPerm f σ ^ k) x : f.rootSet f.SplittingField) : f.SplittingField) = -(x : _)) :
    ∃ τ : g.Gal, (galPerm g τ).IsCycle ∧ (galPerm g τ).support.card = d ∧
      ∀ y ∈ (galPerm g τ).support,
        (((galPerm g τ ^ k) y : g.rootSet g.SplittingField) : g.SplittingField) = -(y : _) := by
  subst hg
  exact exists_isCycle_galPerm_scale f ha hb σ hσ hd hneg

/-! ### Application to Jacobi polynomials -/

/-- A single `d`-cycle in the Galois group of `K_n` gives one in that of `P_n^{(a/u,β)}`
(`K_n = u^n n! P_n^{(α,β)}(1 + (2D/u) X)`, (5.8)). -/
theorem exists_isCycle_galPerm_jacobiP_of_integralJacobi (a u D r : ℤ) (β : ℚ) (n : ℕ)
    (hu : u ≠ 0) (hD : D ≠ 0) (hr : (r : ℚ) = D * ((a : ℚ) / u + β)) {d : ℕ}
    (τ : ((integralJacobi a u D r n).map (Int.castRingHom ℚ)).Gal)
    [DecidableEq (((integralJacobi a u D r n).map (Int.castRingHom ℚ)).rootSet
      ((integralJacobi a u D r n).map (Int.castRingHom ℚ)).SplittingField)]
    [DecidableEq ((jacobiP ((a : ℚ) / u) β n).rootSet
      (jacobiP ((a : ℚ) / u) β n).SplittingField)]
    (hτ : (galPerm _ τ).IsCycle) (hd : (galPerm _ τ).support.card = d) :
    ∃ σ : (jacobiP ((a : ℚ) / u) β n).Gal,
      (galPerm _ σ).IsCycle ∧ (galPerm _ σ).support.card = d := by
  have hu' : (u : ℚ) ≠ 0 := by exact_mod_cast hu
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hs : (u : ℚ) ^ n * n.factorial ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hu') (by exact_mod_cast n.factorial_ne_zero)
  have hb : 2 * (D : ℚ) / u ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero hD') hu'
  have hg := integralJacobi_map a u D r β n hu hr
  rw [show (1 + C (2 * (D : ℚ) / u) * X : ℚ[X]) = C (2 * (D : ℚ) / u) * X + C 1 by
    rw [C_1, add_comm]] at hg
  exact exists_isCycle_galPerm_of_affine (jacobiP ((a : ℚ) / u) β n) 1 hs hb hg τ hτ hd

/-- The quadratic transport for Proposition 5.2: if `s/t = uγ/(2D)` with `t ≠ 0`, a single
`d`-cycle in the Galois group of `K_n(st X^2)` whose `k`-th power negates its support gives
one in that of `P_n^{(a/u,β)}(1 + γ X^2)`. -/
theorem exists_isCycle_galPerm_jacobiP_quadratic_of_integralJacobi (a u D r : ℤ) (β : ℚ)
    (n : ℕ) (hu : u ≠ 0) (hD : D ≠ 0) (hr : (r : ℚ) = D * ((a : ℚ) / u + β)) (γ : ℚ)
    (s t : ℤ) (ht : t ≠ 0) (hst : (s : ℚ) / t = u * γ / (2 * D)) {d k : ℕ}
    (τ : (((integralJacobi a u D r n).comp (C (s * t) * X ^ 2)).map (Int.castRingHom ℚ)).Gal)
    [DecidableEq ((((integralJacobi a u D r n).comp (C (s * t) * X ^ 2)).map
      (Int.castRingHom ℚ)).rootSet (((integralJacobi a u D r n).comp (C (s * t) * X ^ 2)).map
      (Int.castRingHom ℚ)).SplittingField)]
    [DecidableEq (((jacobiP ((a : ℚ) / u) β n).comp (1 + C γ * X ^ 2)).rootSet
      ((jacobiP ((a : ℚ) / u) β n).comp (1 + C γ * X ^ 2)).SplittingField)]
    (hτ : (galPerm _ τ).IsCycle) (hd : (galPerm _ τ).support.card = d)
    (hneg : ∀ x ∈ (galPerm _ τ).support, (((galPerm _ τ ^ k) x : _) :
      (((integralJacobi a u D r n).comp (C (s * t) * X ^ 2)).map
        (Int.castRingHom ℚ)).SplittingField) = -((x : _) :
      (((integralJacobi a u D r n).comp (C (s * t) * X ^ 2)).map
        (Int.castRingHom ℚ)).SplittingField)) :
    ∃ σ : ((jacobiP ((a : ℚ) / u) β n).comp (1 + C γ * X ^ 2)).Gal,
      (galPerm _ σ).IsCycle ∧ (galPerm _ σ).support.card = d ∧
      ∀ y ∈ (galPerm _ σ).support, (((galPerm _ σ ^ k) y : _) :
        ((jacobiP ((a : ℚ) / u) β n).comp (1 + C γ * X ^ 2)).SplittingField) = -((y : _) :
        ((jacobiP ((a : ℚ) / u) β n).comp (1 + C γ * X ^ 2)).SplittingField) := by
  have hu' : (u : ℚ) ≠ 0 := by exact_mod_cast hu
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have ht' : (t : ℚ) ≠ 0 := by exact_mod_cast ht
  have hs : (u : ℚ) ^ n * n.factorial ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hu') (by exact_mod_cast n.factorial_ne_zero)
  refine exists_isCycle_galPerm_scale_of_eq _ (inv_ne_zero hs) (inv_ne_zero ht') ?_ τ hτ hd hneg
  rw [Polynomial.map_comp, comp_assoc]
  have hq : ((C (s * t) * X ^ 2 : ℤ[X]).map (Int.castRingHom ℚ)).comp
      (C (t : ℚ)⁻¹ * X + C 0) = C ((s : ℚ) / t) * X ^ 2 := by
    rw [C_0, add_zero, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, mul_comp, C_comp,
      pow_comp, X_comp, mul_pow, ← mul_assoc, ← C_pow, ← C_mul]
    congr 2
    simp only [eq_intCast, Int.cast_mul]
    field_simp
  rw [hq, integralJacobi_map_comp_C_mul_X_sq a u D r β n hu hr, ← mul_assoc, ← C_mul,
    inv_mul_cancel₀ hs, C_1, one_mul]
  congr 3
  rw [mul_div_assoc, hst]
  field_simp

end ArithmeticOfJacobiPolynomials
