/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.JacobianTate

/-!
# The Tate pairing of a principal polarization on the Tate module

This file turns finite-level dual pairings on the groups of geometric points of
abelian varieties into the pairing on the Tate module
`T_ℓ(A(L)) = tateModule (GeomPoints K L A) ℓ` of
`ArithmeticOfJacobiPolynomials.Algebra.JacobianTate`, and
derives its properties (compatibility, Galois equivariance with the cyclotomic character,
alternating, nondegenerate, perfect, `GSp`/`Sp` structure) from the generic machinery of
`TatePairing` and `TatePairingPerfect`.

## The finite-level input (cited)

Let `A`, `Â` be abelian varieties over `K` and `L/K` algebraically closed with `(ℓ : L) ≠ 0`.
The classical Weil pairing (Milne, *Abelian varieties*, §16, p. 29, built from the Poincaré sheaf
of §9 and the Cartier duality of Theorem 11.1; Mumford, *Abelian varieties* (1970), §20, p. 184) is
a family of biadditive maps
`e n : A(L)[ℓ^n] × Â(L)[ℓ^n] → μ_{ℓ^n}(L)` such that

1. (compatibility; Milne, Lemma 16.1) `e n (ℓ x) (ℓ y) = ℓ • e (n+1) x y`;
2. (Galois equivariance; Milne §16 first paragraph, Mumford §20) `e n (σ x) (σ y) = σ (e n x y)`
   for `σ ∈ Aut(L/K)`;
3. (nondegeneracy; Milne §16 first paragraph via Theorem 11.1, Mumford §20) the pairing is
   perfect, in particular `x ↦ e n x` is injective;

and, for a polarization `φ : A → Â` (Milne §13, p. 25: an isogeny which over `K̄` is `φ_L` for an
ample invertible sheaf `L`),

4. (alternating; Milne §16, the paragraph before Theorem 16.4 and Proposition 16.6, where
   `E_ζ = e_ζ` is the alternating `∧²`-pairing; Mumford (1970), §24, p. 237 for `φ_L`)
   `e^φ n x x = e n x (φ x) = 0`.

These are the hypotheses `hcompat`, `hequiv`, `hperf`, `halt` of the theorems below, supplied by
a cited proposition stated in `External.lean`. What this file proves,
without further input, is:

* `polarizedPairing e lam`: `e^φ n x y = e n x (φ y)` from `e` and a homomorphism `lam = φ`;
  its compatibility, equivariance and (for `φ` an isomorphism, i.e. a *principal* polarization)
  injectivity are deduced from those of `e` (`isCompatibleTorsionPairing_polarizedPairing`,
  `isEquivariantTorsionPairing_polarizedPairing`, `injective_polarizedPairing`);
* `geomPointsHom φ`, `geomPointsEquivOfIso φ`: the action of a group-scheme homomorphism / an
  isomorphism `φ : A ⟶ Â` on geometric points, commuting with the Galois action;
* for an abelian variety `A` and the data above with `φ` an isomorphism of group schemes:
  the Tate pairing `abelianTatePairing`, the rational pairing `abelianWeilPairing` on
  `V_ℓ(A(L))` with values in `ℚ_ℓ(1)`, and
  * `isAlt_abelianWeilPairing`: alternating;
  * `abelianWeilPairing_galois`: `ψ (σ x) (σ y) = χ_ℓ(σ) ψ(x, y)` with `χ_ℓ` the cyclotomic
    character;
  * `abelianWeilPairing_nondegenerate`, `abelianWeilPairing_bijective`: nondegenerate and
    `V_ℓ(A(L)) ≅ Hom(V_ℓ(A(L)), ℚ_ℓ(1))`, using the rank `2 * dim A_L` of
    `JacobianTate` (`finrank_rationalTate_geomPoints`);
  * `abelianTatePairing_bijective`: the integral pairing is perfect `T_ℓ ≅ Hom(T_ℓ, ℤ_ℓ(1))`;
  * `abelianWeilPairing_mem_symplecticGroup_iff`: `σ` acts through `Sp(V_ℓ, ψ)` iff
    `χ_ℓ(σ) = 1`.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry PadicInt
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace ArithmeticOfJacobiPolynomials

open Stacks.AbelianGroup

/-! ### Cross pairings and the pairing twisted by a homomorphism -/

section CrossPairing

variable {ℓ : ℕ} {M M' N : Type*} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N]

/-- **Compatibility of finite-level dual pairings** `e n : M[ℓ^n] × M'[ℓ^n] → N[ℓ^n]` with the
transition maps `M[ℓ^(n+1)] → M[ℓ^n]` (multiplication by `ℓ`):
`e n (ℓ x) (ℓ y) = ℓ • e (n+1) x y`. -/
@[expose]
def IsCompatibleDualPairing (ℓ : ℕ)
    (e : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+
      AddSubgroup.torsionBy M' ((ℓ ^ n : ℕ) : ℤ) →+ AddSubgroup.torsionBy N ((ℓ ^ n : ℕ) : ℤ)) :
    Prop :=
  ∀ n x y, e n (torsionTransition ℓ n x) (torsionTransition ℓ n y) =
    torsionTransition ℓ n (e (n + 1) x y)

/-- **Equivariance of finite-level dual pairings** for actions of a monoid `G` on `M`, `M'`, `N`:
`e n (g x) (g y) = g (e n x y)`. -/
@[expose]
def IsEquivariantDualPairing (ℓ : ℕ) (G : Type*) [Monoid G] [DistribMulAction G M]
    [DistribMulAction G M'] [DistribMulAction G N]
    (e : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+
      AddSubgroup.torsionBy M' ((ℓ ^ n : ℕ) : ℤ) →+ AddSubgroup.torsionBy N ((ℓ ^ n : ℕ) : ℤ)) :
    Prop :=
  ∀ (g : G) n x y, e n (torsionMap (DistribSMul.toAddMonoidHom M g) _ x)
      (torsionMap (DistribSMul.toAddMonoidHom M' g) _ y) =
    torsionMap (DistribSMul.toAddMonoidHom N g) _ (e n x y)

/-- **The pairing twisted by a homomorphism** `lam : M →+ M'` (a polarization `φ : A → Â` on
points): `e^φ n x y = e n x (φ y)`, a pairing `M[ℓ^n] × M[ℓ^n] → N[ℓ^n]`. -/
@[expose]
def polarizedPairing
    (e : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+
      AddSubgroup.torsionBy M' ((ℓ ^ n : ℕ) : ℤ) →+ AddSubgroup.torsionBy N ((ℓ ^ n : ℕ) : ℤ))
    (lam : M →+ M') (n : ℕ) :
    AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+
      AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+ AddSubgroup.torsionBy N ((ℓ ^ n : ℕ) : ℤ) :=
  ((e n).flip.comp (torsionMap lam ((ℓ ^ n : ℕ) : ℤ))).flip

variable
  (e : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+
    AddSubgroup.torsionBy M' ((ℓ ^ n : ℕ) : ℤ) →+ AddSubgroup.torsionBy N ((ℓ ^ n : ℕ) : ℤ))
  (lam : M →+ M')

/-- `e^φ n x y = e n x (φ y)`. -/
theorem polarizedPairing_apply (n : ℕ) (x y : AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ)) :
    polarizedPairing e lam n x y = e n x (torsionMap lam ((ℓ ^ n : ℕ) : ℤ) y) :=
  rfl

/-- Multiplication by `ℓ` commutes with the restriction of a homomorphism to torsion. -/
theorem torsionMap_torsionTransition (n : ℕ) (y : AddSubgroup.torsionBy M ((ℓ ^ (n + 1) : ℕ) : ℤ)) :
    torsionMap lam ((ℓ ^ n : ℕ) : ℤ) (torsionTransition ℓ n y) =
      torsionTransition ℓ n (torsionMap lam ((ℓ ^ (n + 1) : ℕ) : ℤ) y) :=
  Subtype.ext (by
    rw [coe_torsionMap, coe_torsionTransition, coe_torsionTransition, coe_torsionMap, map_nsmul])

variable {e lam}

/-- Twisting a compatible dual pairing by a homomorphism gives a compatible pairing. -/
theorem isCompatibleTorsionPairing_polarizedPairing (he : IsCompatibleDualPairing ℓ e) :
    IsCompatibleTorsionPairing ℓ (polarizedPairing e lam) := fun n x y => by
  rw [polarizedPairing_apply, polarizedPairing_apply, torsionMap_torsionTransition, he]

/-- Twisting an equivariant dual pairing by an equivariant homomorphism gives an equivariant
pairing. -/
theorem isEquivariantTorsionPairing_polarizedPairing {G : Type*} [Monoid G]
    [DistribMulAction G M] [DistribMulAction G M'] [DistribMulAction G N]
    (heq : IsEquivariantDualPairing ℓ G e) (hlam : ∀ (g : G) y, lam (g • y) = g • lam y) :
    IsEquivariantTorsionPairing ℓ G (polarizedPairing e lam) := fun g n x y => by
  rw [polarizedPairing_apply, polarizedPairing_apply, ← heq g n x]
  congr 2
  exact Subtype.ext (hlam g _)

/-- **Perfectness (injectivity) for a principal polarization.** If `x ↦ e n x` is injective and
`lam : M ≃+ M'` is an isomorphism, then `x ↦ e^φ n x` is injective. -/
theorem injective_polarizedPairing (lam : M ≃+ M') (hperf : ∀ n, Function.Injective (e n))
    (n : ℕ) : Function.Injective (polarizedPairing e lam.toAddMonoidHom n) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  refine (injective_iff_map_eq_zero (e n)).1 (hperf n) x (AddMonoidHom.ext fun z => ?_)
  have hz : torsionMap lam.toAddMonoidHom ((ℓ ^ n : ℕ) : ℤ)
      (torsionMap lam.symm.toAddMonoidHom ((ℓ ^ n : ℕ) : ℤ) z) = z :=
    Subtype.ext (by simp)
  have h1 : polarizedPairing e lam.toAddMonoidHom n x
      (torsionMap lam.symm.toAddMonoidHom ((ℓ ^ n : ℕ) : ℤ) z) = 0 := by
    rw [hx]
    rfl
  rwa [polarizedPairing_apply, hz] at h1

section Alternating

variable {ℓ : ℕ} [Fact ℓ.Prime] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {e : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+
    AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+ AddSubgroup.torsionBy N ((ℓ ^ n : ℕ) : ℤ)}
  {he : IsCompatibleTorsionPairing ℓ e}

/-- **Tate-level alternating gives finite-level alternating.** If `M` is `ℓ`-divisible and the
Tate pairing satisfies `ψ(x, x) = 0`, then every finite-level pairing satisfies
`e n z z = 0`, because every `z ∈ M[ℓ^n]` is the reduction of some `x ∈ T_ℓ M`. So the alternating
property may be supplied either at the finite level (Mumford) or at the Tate level
(Milne's `E_ζ = e_ζ`, `∧² T_ℓ A → ℤ_ℓ(1)`). -/
theorem alt_of_tatePairing_self (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (h : ∀ x : tateModule M ℓ, tatePairing e he x x = 0) (n : ℕ)
    (z : AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ)) : e n z z = 0 := by
  obtain ⟨x, rfl⟩ := tateReduction_surjective hdiv n z
  rw [← tateReduction_tatePairing e he x x n, h x, map_zero]

end Alternating

end CrossPairing

/-! ### Group-scheme homomorphisms on geometric points -/

namespace GroupScheme

variable {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L]
  {A B : Over (Spec (.of K))} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]

/-- The image `P ≫ φ` of an `L`-point `P` of `A` under a homomorphism `φ : A ⟶ B` of group
schemes. -/
@[expose]
noncomputable def geomPointsHom (φ : A ⟶ B) [IsMonHom φ] : GeomPoints K L A →+ GeomPoints K L B
    where
  toFun P := (GeomPoints.toHom K L B).symm (GeomPoints.toHom K L A P ≫ φ)
  map_zero' := (GeomPoints.toHom K L B).injective (by
    rw [Equiv.apply_symm_apply, GeomPoints.toHom_zero, MonObj.one_comp, GeomPoints.toHom_zero])
  map_add' P Q := (GeomPoints.toHom K L B).injective (by
    rw [Equiv.apply_symm_apply, GeomPoints.toHom_add, GeomPoints.toHom_add,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, MonObj.mul_comp])

variable {L}

/-- On underlying morphisms, `geomPointsHom L φ P = P ≫ φ`. -/
theorem toHom_geomPointsHom (φ : A ⟶ B) [IsMonHom φ] (P : GeomPoints K L A) :
    GeomPoints.toHom K L B (geomPointsHom L φ P) = GeomPoints.toHom K L A P ≫ φ :=
  Equiv.apply_symm_apply _ _

/-- A homomorphism of group schemes acts on points compatibly with the Galois action:
`φ (σ • P) = σ • φ P`. -/
theorem geomPointsHom_smul (φ : A ⟶ B) [IsMonHom φ] (σ : L ≃ₐ[K] L) (P : GeomPoints K L A) :
    geomPointsHom L φ (σ • P) = σ • geomPointsHom L φ P :=
  (GeomPoints.toHom K L B).injective (by
    rw [toHom_geomPointsHom, GeomPoints.toHom_smul, GeomPoints.toHom_smul,
      toHom_geomPointsHom, Category.assoc])

variable (L)

/-- An isomorphism of group schemes `φ : A ⟶ B` induces an isomorphism `A(L) ≃+ B(L)`. -/
@[expose]
noncomputable def geomPointsEquivOfIso (φ : A ⟶ B) [IsMonHom φ] [IsIso φ] :
    GeomPoints K L A ≃+ GeomPoints K L B :=
  AddEquiv.ofBijective (geomPointsHom L φ)
    ⟨fun P Q h => (GeomPoints.toHom K L A).injective (by
        have := congrArg (GeomPoints.toHom K L B) h
        rw [toHom_geomPointsHom, toHom_geomPointsHom] at this
        exact (cancel_mono φ).1 this),
      fun Q => ⟨(GeomPoints.toHom K L A).symm (GeomPoints.toHom K L B Q ≫ inv φ),
        (GeomPoints.toHom K L B).injective (by
          rw [toHom_geomPointsHom, Equiv.apply_symm_apply, Category.assoc, IsIso.inv_hom_id,
            Category.comp_id])⟩⟩

/-- `geomPointsEquivOfIso` acts as `geomPointsHom`. -/
theorem geomPointsEquivOfIso_apply (φ : A ⟶ B) [IsMonHom φ] [IsIso φ] (P : GeomPoints K L A) :
    geomPointsEquivOfIso L φ P = geomPointsHom L φ P :=
  rfl

end GroupScheme

/-! ### The Tate pairing of a principal polarization on `T_ℓ(A(L))` -/

section WeilTate

open GroupScheme

variable (ℓ : ℕ) {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L]
  (A Â : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A] [GrpObj Â] [IsCommMonObj Â]

/-- **Finite-level duality data** between the `ℓ`-power torsion of `A(L)` and of `Â(L)`, with
values in the roots of unity `μ_{ℓ^n}(L) = (Additive Lˣ)[ℓ^n]`: biadditive pairings
`e n : A(L)[ℓ^n] × Â(L)[ℓ^n] → μ_{ℓ^n}(L)` that are compatible with the transition maps,
`Aut(L/K)`-equivariant, and with trivial left kernel (a perfect pairing).

This is only the bundle of the properties 1-3 of the file header, for a *given* family `e`; it
asserts nothing about the existence of such a family. -/
structure DualPairingData where
  /-- The finite-level pairings `e n : A(L)[ℓ^n] × Â(L)[ℓ^n] → μ_{ℓ^n}(L)`. -/
  pairing : ∀ n : ℕ, AddSubgroup.torsionBy (GeomPoints K L A) ((ℓ ^ n : ℕ) : ℤ) →+
    AddSubgroup.torsionBy (GeomPoints K L Â) ((ℓ ^ n : ℕ) : ℤ) →+
      AddSubgroup.torsionBy (Additive Lˣ) ((ℓ ^ n : ℕ) : ℤ)
  /-- `e n (ℓ x) (ℓ y) = ℓ • e (n + 1) x y`. -/
  compatible : IsCompatibleDualPairing ℓ pairing
  /-- `e n (σ x) (σ y) = σ (e n x y)`. -/
  equivariant : IsEquivariantDualPairing ℓ (L ≃ₐ[K] L) pairing
  /-- `x ↦ e n x` is injective. -/
  injective : ∀ n, Function.Injective (pairing n)

variable {ℓ L A Â} (D : DualPairingData ℓ L A Â) (φ : A ⟶ Â) [IsMonHom φ]

/-- The twisted finite-level pairings `e^φ n x y = e n x (φ y)` on `A(L)[ℓ^n]`. -/
noncomputable abbrev DualPairingData.polarized :=
  polarizedPairing D.pairing (geomPointsHom L φ)

theorem DualPairingData.isCompatible : IsCompatibleTorsionPairing ℓ (D.polarized φ) :=
  isCompatibleTorsionPairing_polarizedPairing D.compatible

theorem DualPairingData.isEquivariant :
    IsEquivariantTorsionPairing ℓ (L ≃ₐ[K] L) (D.polarized φ) :=
  isEquivariantTorsionPairing_polarizedPairing D.equivariant fun σ y => geomPointsHom_smul φ σ y

/-- **Perfectness of the polarized pairing for a principal polarization**: if `φ` is an
isomorphism, `x ↦ e^φ n x` is injective. -/
theorem DualPairingData.injective_polarized [IsIso φ] (n : ℕ) :
    Function.Injective (D.polarized φ n) :=
  injective_polarizedPairing (lam := geomPointsEquivOfIso L φ) D.injective n

variable [Fact ℓ.Prime]

/-- **The integral Tate pairing** `T_ℓ(A(L)) × T_ℓ(A(L)) → ℤ_ℓ(1) = T_ℓ(L^×)` induced by the
finite-level pairings `e^φ`. -/
@[expose]
noncomputable def abelianTatePairing :
    tateModule (GeomPoints K L A) ℓ →ₗ[ℤ_[ℓ]] tateModule (GeomPoints K L A) ℓ →ₗ[ℤ_[ℓ]]
      tateModule (Additive Lˣ) ℓ :=
  tatePairing (D.polarized φ) (D.isCompatible φ)

/-- **The rational pairing** `ψ_ℓ : V_ℓ(A(L)) × V_ℓ(A(L)) → ℚ_ℓ(1)`, the `ℚ_ℓ`-bilinear base
change of `abelianTatePairing`. -/
@[expose]
noncomputable def abelianWeilPairing :
    rationalTate ℓ (GeomPoints K L A) →ₗ[ℚ_[ℓ]] rationalTate ℓ (GeomPoints K L A) →ₗ[ℚ_[ℓ]]
      rationalTate ℓ (Additive Lˣ) :=
  rationalTatePairing (D.polarized φ) (D.isCompatible φ)

/-- **Alternating.** If `e^φ n z z = 0` (`e n z (φ z) = 0`), the Tate pairing is alternating. -/
theorem isAlt_abelianTatePairing (halt : ∀ n z, D.polarized φ n z z = 0) :
    LinearMap.IsAlt (abelianTatePairing D φ) :=
  isAlt_tatePairing halt

/-- **Alternating**, rational version. -/
theorem isAlt_abelianWeilPairing (halt : ∀ n z, D.polarized φ n z z = 0) :
    LinearMap.IsAlt (abelianWeilPairing D φ) :=
  isAlt_rationalTatePairing halt

/-- **Alternating from the Tate level.** On `T_ℓ(A(L))`, for `(ℓ : L) ≠ 0`, it
suffices that `ψ(x, x) = 0` on Tate modules to get the finite-level `e^φ n z z = 0`. -/
theorem DualPairingData.alt_polarized [IsAlgClosed L] [IsAbelianVariety K A] (hℓ : (ℓ : L) ≠ 0)
    (h : ∀ x, abelianTatePairing D φ x x = 0) (n : ℕ) (z : AddSubgroup.torsionBy
      (GeomPoints K L A) ((ℓ ^ n : ℕ) : ℤ)) : D.polarized φ n z z = 0 :=
  alt_of_tatePairing_self (geomPoints_ell_divisible L A hℓ) h n z

/-- **Galois equivariance up to the cyclotomic character.** For `L` algebraically closed with
`(ℓ : L) ≠ 0`, `ψ (σ x) (σ y) = χ_ℓ(σ) • ψ x y`. -/
theorem abelianWeilPairing_galois [IsAlgClosed L] (hℓ : (ℓ : L) ≠ 0) (σ : L ≃ₐ[K] L)
    (x y : rationalTate ℓ (GeomPoints K L A)) :
    abelianWeilPairing D φ
        (rationalTate.representation ℓ (GeomPoints K L A) (L ≃ₐ[K] L) σ x)
        (rationalTate.representation ℓ (GeomPoints K L A) (L ≃ₐ[K] L) σ y) =
      algebraMap ℤ_[ℓ] ℚ_[ℓ] (cyclotomicCharacter L ℓ σ.toRingEquiv) •
        abelianWeilPairing D φ x y :=
  rationalTatePairing_galois_eq_cyclotomicCharacter_smul hℓ (D.isEquivariant φ) σ x y

/-- **Integral Galois equivariance** on `T_ℓ(A(L))`, as an identity in `ℤ_ℓ(1)`. -/
theorem abelianTatePairing_galois (σ : L ≃ₐ[K] L) (x y : tateModule (GeomPoints K L A) ℓ) :
    abelianTatePairing D φ (GroupScheme.galoisRepresentation ℓ K L A σ x)
        (GroupScheme.galoisRepresentation ℓ K L A σ y) =
      tateModule.representation ℓ (Additive Lˣ) (L ≃ₐ[K] L) σ (abelianTatePairing D φ x y) :=
  tatePairing_representation (D.isEquivariant φ) σ x y

variable [IsAlgClosed L] [IsAbelianVariety K A]

/-- **Nondegeneracy** of the rational pairing of a principal polarization, on the
rational Tate module `V_ℓ(A(L))`: `ψ z w = 0` for all `w` implies `z = 0`. -/
theorem abelianWeilPairing_nondegenerate [IsIso φ] (hℓ : (ℓ : L) ≠ 0)
    (z : rationalTate ℓ (GeomPoints K L A))
    (hz : ∀ w, abelianWeilPairing D φ z w = 0) : z = 0 :=
  rationalTatePairing_nondegenerate (geomPoints_ell_divisible L A hℓ)
    (D.injective_polarized φ) z hz

/-- **Perfectness of the integral pairing**: `T_ℓ(A(L)) ≃ Hom_{ℤ_ℓ}(T_ℓ(A(L)), ℤ_ℓ(1))`, for the
Tate module of an abelian variety and a principal polarization. -/
theorem abelianTatePairing_bijective [IsIso φ] (hℓ : (ℓ : L) ≠ 0) :
    Function.Bijective (abelianTatePairing D φ) :=
  tatePairing_bijective_of_injective (geomPoints_ell_divisible L A hℓ)
    (nonempty_torsionEquiv_geomPoints L A hℓ) (tateTwist.nonempty_torsionEquiv L ℓ hℓ)
    (D.injective_polarized φ)

/-- **Perfectness of the rational pairing**: `V_ℓ(A(L)) ≃ Hom_{ℚ_ℓ}(V_ℓ(A(L)), ℚ_ℓ(1))`. -/
theorem abelianWeilPairing_bijective [IsIso φ] (hℓ : (ℓ : L) ≠ 0) :
    Function.Bijective (abelianWeilPairing D φ) :=
  rationalTatePairing_bijective (geomPoints_ell_divisible L A hℓ)
    (nonempty_torsionEquiv_geomPoints L A hℓ) (exists_div_units L (Fact.out : ℓ.Prime).pos)
    (tateTwist.nonempty_torsionEquiv L ℓ hℓ) (D.injective_polarized φ)

/-- **The multiplier of Galois on `V_ℓ(A(L))` is the cyclotomic character**, for a nonzero
pairing (`0 < dim A_L`). -/
theorem abelianWeilPairing_ne_zero [IsIso φ] (hℓ : (ℓ : L) ≠ 0) (hg : 0 < geomDim L A) :
    abelianWeilPairing D φ ≠ 0 :=
  rationalTatePairing_ne_zero (geomPoints_ell_divisible L A hℓ)
    (nonempty_torsionEquiv_geomPoints L A hℓ) (by omega) (D.injective_polarized φ)

/-- **`σ` acts through `Sp(V_ℓ, ψ)` iff `χ_ℓ(σ) = 1`**, for `V_ℓ(A(L))`. -/
theorem abelianWeilPairing_mem_symplecticGroup_iff [IsIso φ] (hℓ : (ℓ : L) ≠ 0)
    (hg : 0 < geomDim L A) (σ : L ≃ₐ[K] L) :
    ((galoisSimilitudeRepresentation (he := D.isCompatible φ) hℓ (D.isEquivariant φ) σ :
        rationalTate ℓ (GeomPoints K L A) ≃ₗ[ℚ_[ℓ]] rationalTate ℓ (GeomPoints K L A)) ∈
        symplecticGroup (abelianWeilPairing D φ)) ↔
      cyclotomicCharacter L ℓ σ.toRingEquiv = 1 :=
  galoisSimilitudeRepresentation_mem_symplecticGroup_iff hℓ (D.isEquivariant φ)
    (geomPoints_ell_divisible L A hℓ) (nonempty_torsionEquiv_geomPoints L A hℓ)
    (by omega) (D.injective_polarized φ) σ

end WeilTate

end ArithmeticOfJacobiPolynomials
