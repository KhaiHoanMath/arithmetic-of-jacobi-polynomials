/- Assembled by AxiomProver. -/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Module.LinearMap.End

/-!
# Similitude and symplectic groups of a bilinear map, and their Lie algebras

Let `F` be a field, `V` and `W` vector spaces over `F` and `ψ : V × V → W` an `F`-bilinear map
(in the application `W` is the one-dimensional space `ℚ_ℓ(1)` and `ψ` the alternating Weil
pairing). This file defines, for an arbitrary such `ψ`:

* `ArithmeticOfJacobiPolynomials.similitudeGroup ψ`: the linear automorphisms `g` of `V` with
  `ψ (g x) (g y) = c • ψ x y` for some `c : Fˣ` (the group `GSp(V, ψ)` when `ψ` is alternating
  and nondegenerate);
* `ArithmeticOfJacobiPolynomials.symplecticGroup ψ`: the automorphisms preserving `ψ` (`Sp(V, ψ)`),
with
  `symplecticGroup_le_similitudeGroup`;
* `ArithmeticOfJacobiPolynomials.similitudeMultiplier ψ hψ : similitudeGroup ψ →* Fˣ` for `ψ ≠ 0`
(in particular
  when `ψ` is nondegenerate and `V ≠ 0`, `ne_zero_of_nondegenerate`), the multiplier `c`, with
  kernel `symplecticGroup ψ` (`ker_similitudeMultiplier`);
* `ArithmeticOfJacobiPolynomials.symplecticLie ψ`, `ArithmeticOfJacobiPolynomials.similitudeLie ψ`:
the Lie-algebra-level
  submodules `𝔰𝔭(V, ψ) = {A | ψ (A x) y + ψ x (A y) = 0}` and
  `𝔤𝔰𝔭(V, ψ) = {A | ∃ c, ψ (A x) y + ψ x (A y) = c • ψ x y}` of `Module.End F V`;
* `ArithmeticOfJacobiPolynomials.similitudeLie_eq_span_id_sup_symplecticLie`: if `(2 : F) ≠ 0`, then
  `𝔤𝔰𝔭(V, ψ) = F · id ⊔ 𝔰𝔭(V, ψ)`, and `disjoint_span_id_symplecticLie`: this sum is direct when
  moreover `ψ ≠ 0`.

Mathlib's `LieAlgebra.Symplectic.sp` is the matrix Lie algebra of the standard form `J`, so it does
not apply to an abstract bilinear map; everything here is stated for an arbitrary `ψ`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

section Group

/-- **The similitude group** `GSp(V, ψ)`: the `F`-linear automorphisms `g` of `V` multiplying `ψ`
by a unit, `ψ (g x) (g y) = c • ψ x y` for some `c : Fˣ`. -/
@[expose]
def similitudeGroup (ψ : V →ₗ[F] V →ₗ[F] W) : Subgroup (V ≃ₗ[F] V) where
  carrier := {g | ∃ c : Fˣ, ∀ x y, ψ (g x) (g y) = (c : F) • ψ x y}
  one_mem' := ⟨1, fun x y => by
    simp only [LinearEquiv.coe_one, id_eq, Units.val_one, one_smul]⟩
  mul_mem' := by
    rintro g h ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, fun x y => ?_⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hc, hd, Units.val_mul, mul_smul]
  inv_mem' := by
    rintro g ⟨c, hc⟩
    refine ⟨c⁻¹, fun x y => ?_⟩
    have h := hc (g⁻¹ x) (g⁻¹ y)
    rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    rw [LinearEquiv.coe_inv, h, smul_smul, Units.inv_mul, one_smul]

/-- Membership in the similitude group. -/
theorem mem_similitudeGroup {ψ : V →ₗ[F] V →ₗ[F] W} {g : V ≃ₗ[F] V} :
    g ∈ similitudeGroup ψ ↔ ∃ c : Fˣ, ∀ x y, ψ (g x) (g y) = (c : F) • ψ x y :=
  Iff.rfl

/-- **The symplectic group** `Sp(V, ψ)`: the `F`-linear automorphisms `g` of `V` preserving `ψ`,
`ψ (g x) (g y) = ψ x y`. -/
@[expose]
def symplecticGroup (ψ : V →ₗ[F] V →ₗ[F] W) : Subgroup (V ≃ₗ[F] V) where
  carrier := {g | ∀ x y, ψ (g x) (g y) = ψ x y}
  one_mem' := by
    intro x y
    rfl
  mul_mem' := by
    intro g h hg hh x y
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg, hh]
  inv_mem' := by
    intro g hg x y
    have h := hg (g⁻¹ x) (g⁻¹ y)
    rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    rw [LinearEquiv.coe_inv, h]

/-- Membership in the symplectic group. -/
theorem mem_symplecticGroup {ψ : V →ₗ[F] V →ₗ[F] W} {g : V ≃ₗ[F] V} :
    g ∈ symplecticGroup ψ ↔ ∀ x y, ψ (g x) (g y) = ψ x y :=
  Iff.rfl

/-- `Sp(V, ψ) ≤ GSp(V, ψ)` (multiplier `1`). -/
theorem symplecticGroup_le_similitudeGroup (ψ : V →ₗ[F] V →ₗ[F] W) :
    symplecticGroup ψ ≤ similitudeGroup ψ :=
  fun g hg => mem_similitudeGroup.2
    ⟨1, fun x y => by rw [mem_symplecticGroup.1 hg x y, Units.val_one, one_smul]⟩

/-- A nondegenerate bilinear map on a nonzero space is nonzero. -/
theorem ne_zero_of_nondegenerate [Nontrivial V] {ψ : V →ₗ[F] V →ₗ[F] W}
    (hnd : ∀ x, (∀ y, ψ x y = 0) → x = 0) : ψ ≠ 0 := by
  intro h0
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  exact hx (hnd x fun y => by rw [h0, LinearMap.zero_apply, LinearMap.zero_apply])

/-- In a vector space, `c • w = d • w` with `w ≠ 0` forces `c = d`. -/
theorem eq_of_smul_eq_smul_of_ne_zero {c d : F} {w : W} (hw : w ≠ 0) (h : c • w = d • w) :
    c = d := by
  by_contra hcd
  have hcd' : c - d ≠ 0 := sub_ne_zero.2 hcd
  have h0 : (c - d) • w = 0 := by rw [sub_smul, h, sub_self]
  apply hw
  rw [← one_smul F w, ← inv_mul_cancel₀ hcd', mul_smul, h0, smul_zero]

/-- A nonzero bilinear map takes a nonzero value. -/
theorem exists_apply_ne_zero {ψ : V →ₗ[F] V →ₗ[F] W} (hψ : ψ ≠ 0) : ∃ x y, ψ x y ≠ 0 := by
  by_contra h
  simp only [ne_eq, not_exists, not_not] at h
  exact hψ (LinearMap.ext fun x => LinearMap.ext fun y => h x y)

/-- If `ψ ≠ 0`, the scalar `c` with `ψ (g x) (g y) = c • ψ x y` is unique. -/
theorem similitude_scalar_unique {ψ : V →ₗ[F] V →ₗ[F] W} (hψ : ψ ≠ 0) {g : V → V} {c d : F}
    (hc : ∀ x y, ψ (g x) (g y) = c • ψ x y) (hd : ∀ x y, ψ (g x) (g y) = d • ψ x y) :
    c = d := by
  obtain ⟨x, y, hxy⟩ := exists_apply_ne_zero hψ
  exact eq_of_smul_eq_smul_of_ne_zero hxy ((hc x y).symm.trans (hd x y))

/-- **The multiplier** `GSp(V, ψ) →* Fˣ`, `g ↦ c` where `ψ (g x) (g y) = c • ψ x y`; well defined
for `ψ ≠ 0` (e.g. `ψ` nondegenerate on `V ≠ 0`, see `ne_zero_of_nondegenerate`). -/
@[expose]
noncomputable def similitudeMultiplier (ψ : V →ₗ[F] V →ₗ[F] W) (hψ : ψ ≠ 0) :
    similitudeGroup ψ →* Fˣ where
  toFun g := Classical.choose (mem_similitudeGroup.1 g.2)
  map_one' := by
    refine Units.ext (similitude_scalar_unique hψ
      (Classical.choose_spec (mem_similitudeGroup.1 (1 : similitudeGroup ψ).2)) ?_)
    intro x y
    change ψ ((1 : V ≃ₗ[F] V) x) ((1 : V ≃ₗ[F] V) y) = ((1 : Fˣ) : F) • ψ x y
    rw [Units.val_one, one_smul]
    rfl
  map_mul' g h := by
    refine Units.ext (similitude_scalar_unique hψ
      (Classical.choose_spec (mem_similitudeGroup.1 (g * h).2)) ?_)
    intro x y
    change ψ ((g : V ≃ₗ[F] V) ((h : V ≃ₗ[F] V) x)) ((g : V ≃ₗ[F] V) ((h : V ≃ₗ[F] V) y)) = _
    rw [Classical.choose_spec (mem_similitudeGroup.1 g.2),
      Classical.choose_spec (mem_similitudeGroup.1 h.2), Units.val_mul, mul_smul]

/-- The defining property of the multiplier: `ψ (g x) (g y) = μ(g) • ψ x y`. -/
theorem similitudeMultiplier_spec (ψ : V →ₗ[F] V →ₗ[F] W) (hψ : ψ ≠ 0) (g : similitudeGroup ψ)
    (x y : V) :
    ψ ((g : V ≃ₗ[F] V) x) ((g : V ≃ₗ[F] V) y) = (similitudeMultiplier ψ hψ g : F) • ψ x y :=
  Classical.choose_spec (mem_similitudeGroup.1 g.2) x y

/-- The multiplier of `g` is the unique `c` with `ψ (g x) (g y) = c • ψ x y`. -/
theorem similitudeMultiplier_eq {ψ : V →ₗ[F] V →ₗ[F] W} (hψ : ψ ≠ 0) (g : similitudeGroup ψ)
    {c : Fˣ} (hc : ∀ x y, ψ ((g : V ≃ₗ[F] V) x) ((g : V ≃ₗ[F] V) y) = (c : F) • ψ x y) :
    similitudeMultiplier ψ hψ g = c :=
  Units.ext (similitude_scalar_unique hψ (similitudeMultiplier_spec ψ hψ g) hc)

/-- **The kernel of the multiplier is the symplectic group:** for `ψ ≠ 0`,
`ker (GSp(V, ψ) → Fˣ) = Sp(V, ψ)` (as subgroups of `GSp(V, ψ)`). -/
theorem ker_similitudeMultiplier (ψ : V →ₗ[F] V →ₗ[F] W) (hψ : ψ ≠ 0) :
    (similitudeMultiplier ψ hψ).ker = (symplecticGroup ψ).subgroupOf (similitudeGroup ψ) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_symplecticGroup]
  constructor
  · intro h x y
    rw [similitudeMultiplier_spec ψ hψ, h, Units.val_one, one_smul]
  · intro h
    exact similitudeMultiplier_eq hψ g fun x y => by rw [h, Units.val_one, one_smul]

/-- The kernel of the multiplier is the symplectic group, for `ψ` nondegenerate on `V ≠ 0`. -/
theorem ker_similitudeMultiplier_of_nondegenerate [Nontrivial V] (ψ : V →ₗ[F] V →ₗ[F] W)
    (hnd : ∀ x, (∀ y, ψ x y = 0) → x = 0) :
    (similitudeMultiplier ψ (ne_zero_of_nondegenerate hnd)).ker =
      (symplecticGroup ψ).subgroupOf (similitudeGroup ψ) :=
  ker_similitudeMultiplier ψ _

end Group

section Lie

/-- **The symplectic Lie algebra** `𝔰𝔭(V, ψ)`: the endomorphisms `A` of `V` with
`ψ (A x) y + ψ x (A y) = 0`. -/
@[expose]
def symplecticLie (ψ : V →ₗ[F] V →ₗ[F] W) : Submodule F (Module.End F V) where
  carrier := {A | ∀ x y, ψ (A x) y + ψ x (A y) = 0}
  add_mem' := by
    intro A B hA hB x y
    simp only [LinearMap.add_apply, map_add]
    rw [add_add_add_comm, hA, hB, add_zero]
  zero_mem' := by
    intro x y
    simp
  smul_mem' := by
    intro a A hA x y
    simp only [LinearMap.smul_apply, map_smul, LinearMap.smul_apply]
    rw [← smul_add, hA, smul_zero]

/-- Membership in `𝔰𝔭(V, ψ)`. -/
theorem mem_symplecticLie {ψ : V →ₗ[F] V →ₗ[F] W} {A : Module.End F V} :
    A ∈ symplecticLie ψ ↔ ∀ x y, ψ (A x) y + ψ x (A y) = 0 :=
  Iff.rfl

/-- **The similitude Lie algebra** `𝔤𝔰𝔭(V, ψ)`: the endomorphisms `A` of `V` with
`ψ (A x) y + ψ x (A y) = c • ψ x y` for some `c : F`. -/
@[expose]
def similitudeLie (ψ : V →ₗ[F] V →ₗ[F] W) : Submodule F (Module.End F V) where
  carrier := {A | ∃ c : F, ∀ x y, ψ (A x) y + ψ x (A y) = c • ψ x y}
  add_mem' := by
    rintro A B ⟨c, hA⟩ ⟨d, hB⟩
    refine ⟨c + d, fun x y => ?_⟩
    simp only [LinearMap.add_apply, map_add]
    rw [add_add_add_comm, hA, hB, add_smul]
  zero_mem' := ⟨0, fun x y => by simp only [LinearMap.zero_apply, map_zero, zero_smul, add_zero]⟩
  smul_mem' := by
    rintro a A ⟨c, hA⟩
    refine ⟨a * c, fun x y => ?_⟩
    simp only [LinearMap.smul_apply, map_smul, LinearMap.smul_apply]
    rw [← smul_add, hA, smul_smul]

/-- Membership in `𝔤𝔰𝔭(V, ψ)`. -/
theorem mem_similitudeLie {ψ : V →ₗ[F] V →ₗ[F] W} {A : Module.End F V} :
    A ∈ similitudeLie ψ ↔ ∃ c : F, ∀ x y, ψ (A x) y + ψ x (A y) = c • ψ x y :=
  Iff.rfl

/-- `𝔰𝔭(V, ψ) ≤ 𝔤𝔰𝔭(V, ψ)`. -/
theorem symplecticLie_le_similitudeLie (ψ : V →ₗ[F] V →ₗ[F] W) :
    symplecticLie ψ ≤ similitudeLie ψ :=
  fun A hA => mem_similitudeLie.2 ⟨0, fun x y => by rw [mem_symplecticLie.1 hA x y, zero_smul]⟩

/-- For a scalar endomorphism, `ψ (a x) y + ψ x (a y) = (2 a) • ψ x y`. -/
theorem bilin_smul_id_add (ψ : V →ₗ[F] V →ₗ[F] W) (a : F) (x y : V) :
    ψ ((a • LinearMap.id : Module.End F V) x) y + ψ x ((a • LinearMap.id : Module.End F V) y) =
      (2 * a) • ψ x y := by
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, LinearMap.smul_apply]
  rw [two_mul, add_smul]

/-- The identity lies in `𝔤𝔰𝔭(V, ψ)` (with `c = 2`). -/
theorem id_mem_similitudeLie (ψ : V →ₗ[F] V →ₗ[F] W) :
    (LinearMap.id : Module.End F V) ∈ similitudeLie ψ :=
  mem_similitudeLie.2 ⟨2, fun x y => by rw [LinearMap.id_apply, LinearMap.id_apply, two_smul]⟩

/-- **`𝔤𝔰𝔭 = F · id + 𝔰𝔭`.** If `(2 : F) ≠ 0`, then
`𝔤𝔰𝔭(V, ψ) = F ∙ id ⊔ 𝔰𝔭(V, ψ)`. -/
theorem similitudeLie_eq_span_id_sup_symplecticLie (ψ : V →ₗ[F] V →ₗ[F] W) (h2 : (2 : F) ≠ 0) :
    similitudeLie ψ = (F ∙ (LinearMap.id : Module.End F V)) ⊔ symplecticLie ψ := by
  refine le_antisymm ?_ (sup_le ?_ (symplecticLie_le_similitudeLie ψ))
  · intro A hA'
    obtain ⟨c, hA⟩ := mem_similitudeLie.1 hA'
    rw [Submodule.mem_sup]
    refine ⟨(c / 2) • LinearMap.id, Submodule.mem_span_singleton.2 ⟨c / 2, rfl⟩,
      A - (c / 2) • LinearMap.id, mem_symplecticLie.2 fun x y => ?_, add_sub_cancel _ _⟩
    have h := bilin_smul_id_add ψ (c / 2) x y
    rw [mul_div_cancel₀ c h2] at h
    simp only [LinearMap.sub_apply, map_sub, LinearMap.sub_apply]
    rw [sub_add_sub_comm, hA, h, sub_self]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact id_mem_similitudeLie ψ

/-- **The sum `F · id + 𝔰𝔭` is direct.** If `ψ ≠ 0` and `(2 : F) ≠ 0`, then
`F ∙ id` and `𝔰𝔭(V, ψ)` are disjoint. -/
theorem disjoint_span_id_symplecticLie {ψ : V →ₗ[F] V →ₗ[F] W} (hψ : ψ ≠ 0) (h2 : (2 : F) ≠ 0) :
    Disjoint (F ∙ (LinearMap.id : Module.End F V)) (symplecticLie ψ) := by
  rw [Submodule.disjoint_def]
  rintro A hA hsp
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hA
  obtain ⟨x, y, hxy⟩ := exists_apply_ne_zero hψ
  have h0 := (bilin_smul_id_add ψ a x y).symm.trans (mem_symplecticLie.1 hsp x y)
  have h : 2 * a = 0 := eq_of_smul_eq_smul_of_ne_zero hxy (h0.trans (zero_smul F _).symm)
  rw [mul_eq_zero, or_iff_right h2] at h
  rw [h, zero_smul]

end Lie

end ArithmeticOfJacobiPolynomials
