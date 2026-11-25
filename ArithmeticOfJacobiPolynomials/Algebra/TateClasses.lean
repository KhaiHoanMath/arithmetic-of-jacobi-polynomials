/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.HodgeStructure
public import ArithmeticOfJacobiPolynomials.Algebra.RationalDescent
public import ArithmeticOfJacobiPolynomials.Algebra.SymplecticSimilitude
public import ArithmeticOfJacobiPolynomials.Algebra.TatePairing

/-!
# Tate classes of a linear representation in tensor spaces; finite-index behaviour

The statement of Corollary 6.6 concerns the Tate classes of
`V_ℓ = V_ℓ(J)` and of its powers: the `Gal(Q̄/K)`-invariant vectors of the twisted tensor
spaces `V_ℓ^{⊗m} ⊗ (V_ℓ^*)^{⊗n} ⊗ ℚ_ℓ(p)`; its proof (§6.5) passes from one
Galois group to a subgroup of finite index. This file sets up the generic linear algebra, for an
arbitrary group `G`, a field `F`, a representation `ρ : G →* GL(V)` and a character
`χ : G →* Fˣ` playing the role of the cyclotomic character (the action of `G` on `F(1)`).
Nothing about Jacobians, algebraic cycles or cycle classes is asserted.

## Conventions

* **Twisted tensor action** (`twistedTensorRep ρ χ m n p`): `G` acts on
  `T m n ⊗ F(p) = V^{⊗m} ⊗ (V^*)^{⊗n} ⊗ F(p)` by `g ↦ χ(g)^p • tensorRep m n (ρ g)`, where
  `F(p) = F(1)^{⊗p}` is the line on which `G` acts through `χ^p` (we identify `T m n ⊗ F(p)`
  with `T m n` and record the twist in the action; `p : ℤ`, negative `p` meaning duals).
  The action of `GL(V)` on `T m n` is that of `ArithmeticOfJacobiPolynomials.Algebra.HodgeStructure`
  (contragredient on the dual factors).
* **Tate classes** (`tateClasses ρ χ H m n p`): the `H`-invariant vectors of this action, for a
  subgroup `H ≤ G` (in the application `H = Gal(Q̄/K)` for a number field `K`).
* **The twist of the polarization.** A form `ψ` with `ψ (g x) (g y) = χ(g) ψ(x, y)` (values in
  `F(1)`) is the tensor `bilinTensor ψ ∈ T 0 2`, on which `g` acts by `χ(g)⁻¹` (contragredient
  action), so it is a Tate class of **twist `p = 1`**: `ψ ∈ (T 0 2 ⊗ F(1))^H`. This matches the
  `(p, p)` convention of `ArithmeticOfJacobiPolynomials.Algebra.HodgeStructure`, where a
  polarization is a Hodge
  class of twist `1` (`2 · 1 = 2 - 0`).

## Main results

* `tateClasses_mono`: a larger subgroup has fewer Tate classes; `tateClasses_bot`.
* **Finite index**:
  - `invariants_subgroupOf_eq_tateClasses`: for `K ≤ H`, the `K`-Tate classes are the invariants
    of the restriction to `K` of the action of `H`;
  - `tateQuotientRep`, `tateQuotientRep_mk_apply`: if `K` is normal in `H`, then `H` acts on the
    `K`-Tate classes through the quotient `H ⧸ K` (Mathlib's
    `Representation.quotientToInvariants`);
  - `tateClasses_eq_map_range_averageMap`: if moreover `H ⧸ K` is finite of order invertible in
    `F` (any finite `H ⧸ K` in characteristic zero), the `H`-Tate classes are exactly the images
    of Mathlib's averaging operator `Representation.averageMap` of `tateQuotientRep` (its
    invariance and identity lemmas `Representation.averageMap_invariant`,
    `Representation.averageMap_id` are used);
  - `forall_exists_preimage_tateClasses_of_relIndex` (via
    `ArithmeticOfJacobiPolynomials.forall_exists_invariant_preimage_of_index` of
    `RationalDescent`): for an
    equivariant map `φ : C → T m n ⊗ F(p)` (e.g. a cycle class map), if every `K`-Tate class is
    the image of a `K`-invariant vector and `[H : K]` is invertible in `F`, then every `H`-Tate
    class is the image of an `H`-invariant vector.
* **The similitude link**:
  - `bilinTensor_mem_tateClasses_iff`: `bilinTensor ψ` is a Tate class of twist `1` for `H` iff
    `ψ (ρ g x) (ρ g y) = χ(g) ψ(x, y)` for all `g ∈ H`;
  - `bilinTensor_compr₂_mem_tateClasses`: for `σ : G →* GSp(V, ψ)` with values of `ψ` in a space
    `W` and any linear form `f` on `W`, `f ∘ ψ` is a Tate class of twist `1` for the multiplier
    character, for every subgroup;
  - `bilinTensor_rationalTatePairing_compr₂_mem_tateClasses`: the case of the Galois action on
    `V_ℓ M` by similitudes of a Weil-type pairing with values in `ℚ_ℓ(1)`
    (`ArithmeticOfJacobiPolynomials.Algebra.TatePairing`), whose multiplier is the cyclotomic
    character
    (`similitudeMultiplier_galoisSimilitudeRepresentation`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

section TwistedTensor

variable {G F V : Type*} [Group G] [Field F] [AddCommGroup V] [Module F V]

/-- **The twisted tensor action** of `G` on `T m n ⊗ F(p)`, identified with `T m n`:
`g ↦ χ(g)^p • tensorRep m n (ρ g)`. -/
@[expose]
noncomputable def twistedTensorRep (ρ : G →* (V ≃ₗ[F] V)) (χ : G →* Fˣ) (m n : ℕ) (p : ℤ) :
    Representation F G (TensorSpace F V m n) where
  toFun g := ((χ g ^ p : Fˣ) : F) • tensorRep m n (ρ g)
  map_one' := by
    simp only [map_one, one_zpow, Units.val_one, one_smul]
  map_mul' g h := by
    change ((χ (g * h) ^ p : Fˣ) : F) • tensorRep m n (ρ (g * h)) =
      (((χ g ^ p : Fˣ) : F) • tensorRep m n (ρ g)) * (((χ h ^ p : Fˣ) : F) • tensorRep m n (ρ h))
    rw [smul_mul_smul_comm, map_mul χ, mul_zpow, Units.val_mul, map_mul ρ,
      map_mul (tensorRep m n)]

/-- The twisted tensor action on a tensor. -/
theorem twistedTensorRep_apply (ρ : G →* (V ≃ₗ[F] V)) (χ : G →* Fˣ) (m n : ℕ) (p : ℤ) (g : G)
    (t : TensorSpace F V m n) :
    twistedTensorRep ρ χ m n p g t = ((χ g ^ p : Fˣ) : F) • tensorMap m n (ρ g) t :=
  rfl

/-- **Tate classes** for a subgroup `H ≤ G`: the `H`-invariant vectors of `T m n ⊗ F(p)` under
the twisted tensor action. -/
@[expose]
noncomputable def tateClasses (ρ : G →* (V ≃ₗ[F] V)) (χ : G →* Fˣ) (H : Subgroup G)
    (m n : ℕ) (p : ℤ) : Submodule F (TensorSpace F V m n) :=
  Representation.invariants ((twistedTensorRep ρ χ m n p).comp H.subtype)

variable {ρ : G →* (V ≃ₗ[F] V)} {χ : G →* Fˣ} {m n : ℕ} {p : ℤ}

/-- Membership in `tateClasses`. -/
theorem mem_tateClasses {H : Subgroup G} {t : TensorSpace F V m n} :
    t ∈ tateClasses ρ χ H m n p ↔ ∀ g ∈ H, twistedTensorRep ρ χ m n p g t = t := by
  rw [tateClasses, Representation.mem_invariants]
  exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.2⟩

/-- **A larger subgroup has fewer Tate classes**: if `H ≤ H'` then every `H'`-Tate class is an
`H`-Tate class. -/
theorem tateClasses_mono {H H' : Subgroup G} (hHH' : H ≤ H') :
    tateClasses ρ χ H' m n p ≤ tateClasses ρ χ H m n p :=
  fun _ ht => mem_tateClasses.2 fun g hg => mem_tateClasses.1 ht g (hHH' hg)

/-- For the trivial subgroup every tensor is a Tate class. -/
theorem tateClasses_bot : tateClasses ρ χ (⊥ : Subgroup G) m n p = ⊤ :=
  eq_top_iff.2 fun _ _ => mem_tateClasses.2 fun g hg => by
    rw [Subgroup.mem_bot.1 hg, map_one, Module.End.one_apply]

end TwistedTensor

section FiniteIndex

variable {G F V : Type*} [Group G] [Field F] [AddCommGroup V] [Module F V]
  (ρ : G →* (V ≃ₗ[F] V)) (χ : G →* Fˣ) (m n : ℕ) (p : ℤ)

/-- For `K ≤ H`, the `K`-Tate classes are the invariants of the restriction to
`K` (as the subgroup `K.subgroupOf H` of `H`) of the action of `H`. -/
theorem invariants_subgroupOf_eq_tateClasses {H K : Subgroup G} (hKH : K ≤ H) :
    Representation.invariants
      (((twistedTensorRep ρ χ m n p).comp H.subtype).comp (K.subgroupOf H).subtype) =
      tateClasses ρ χ K m n p := by
  ext t
  rw [Representation.mem_invariants, mem_tateClasses]
  constructor
  · intro h g hg
    exact h ⟨⟨g, hKH hg⟩, Subgroup.mem_subgroupOf.2 hg⟩
  · intro h s
    exact h ((s : H) : G) (Subgroup.mem_subgroupOf.1 s.2)

/-- **The action of `H` on the `K`-Tate classes through the quotient `H ⧸ K`**, for `K` normal
in `H` (Mathlib's `Representation.quotientToInvariants`; the `K`-Tate classes appear as the
invariants of the restricted action, see `invariants_subgroupOf_eq_tateClasses`). -/
@[expose]
noncomputable def tateQuotientRep (H K : Subgroup G) [(K.subgroupOf H).Normal] :
    Representation F (H ⧸ K.subgroupOf H) (Representation.invariants
      (((twistedTensorRep ρ χ m n p).comp H.subtype).comp (K.subgroupOf H).subtype)) :=
  Representation.quotientToInvariants ((twistedTensorRep ρ χ m n p).comp H.subtype)
    (K.subgroupOf H)

/-- The class of `g ∈ H` in `H ⧸ K` acts on the `K`-Tate classes as `g`. -/
theorem tateQuotientRep_mk_apply (H K : Subgroup G) [(K.subgroupOf H).Normal] (g : H)
    (t : Representation.invariants
      (((twistedTensorRep ρ χ m n p).comp H.subtype).comp (K.subgroupOf H).subtype)) :
    (tateQuotientRep ρ χ m n p H K (g : H ⧸ K.subgroupOf H) t : TensorSpace F V m n) =
      twistedTensorRep ρ χ m n p g t :=
  rfl

/-- **The `H`-Tate classes are the averages of the `K`-Tate classes.** Let `K ≤ H` with `K`
normal in `H` and `H ⧸ K` finite of order invertible in `F` (in characteristic zero,
`invertibleOfNonzero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)`). Then the `H`-Tate classes are
exactly the images of Mathlib's averaging operator `Representation.averageMap`
(`|H ⧸ K|⁻¹ ∑_{q ∈ H ⧸ K} q`) of the representation `tateQuotientRep` on the `K`-Tate classes. -/
theorem tateClasses_eq_map_range_averageMap {H K : Subgroup G} (hKH : K ≤ H)
    [(K.subgroupOf H).Normal] [Fintype (H ⧸ K.subgroupOf H)]
    [Invertible (Fintype.card (H ⧸ K.subgroupOf H) : F)] :
    tateClasses ρ χ H m n p =
      (LinearMap.range (Representation.averageMap (k := F)
        (V := Representation.invariants (((twistedTensorRep ρ χ m n p).comp
          H.subtype).comp (K.subgroupOf H).subtype))
        (tateQuotientRep ρ χ m n p H K))).map
        (Submodule.subtype (Representation.invariants (((twistedTensorRep ρ χ m n p).comp
          H.subtype).comp (K.subgroupOf H).subtype))) := by
  apply le_antisymm
  · intro t ht
    have htK : t ∈ Representation.invariants
        (((twistedTensorRep ρ χ m n p).comp H.subtype).comp (K.subgroupOf H).subtype) := by
      rw [invariants_subgroupOf_eq_tateClasses ρ χ m n p hKH]
      exact tateClasses_mono hKH ht
    have hinv : ∀ q, tateQuotientRep ρ χ m n p H K q ⟨t, htK⟩ = ⟨t, htK⟩ := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      apply Subtype.ext
      rw [tateQuotientRep_mk_apply]
      exact mem_tateClasses.1 ht g g.2
    exact Submodule.mem_map.2 ⟨⟨t, htK⟩, LinearMap.mem_range.2
      ⟨⟨t, htK⟩,
        Representation.averageMap_id _ _ ((Representation.mem_invariants _ _).2 hinv)⟩, rfl⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.1 ht
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hs
    refine mem_tateClasses.2 fun g hg => ?_
    have h' := congrArg Subtype.val
      ((Representation.mem_invariants _ _).1
        (Representation.averageMap_invariant (tateQuotientRep ρ χ m n p H K) u)
        ((⟨g, hg⟩ : H) : H ⧸ K.subgroupOf H))
    rw [tateQuotientRep_mk_apply] at h'
    exact h'

/-- **The span condition descends along a subgroup of finite index** (relative averaging,
`ArithmeticOfJacobiPolynomials.forall_exists_invariant_preimage_of_index`). Let `π` be a
representation of `G` on
`C` and `φ : C → T m n ⊗ F(p)` a `G`-equivariant linear map (e.g. a cycle class map). Let
`K ≤ H` with `[H : K]` nonzero in `F`. If every `K`-Tate class is the image of a `K`-invariant
vector of `C`, then every `H`-Tate class is the image of an `H`-invariant vector of `C`. -/
theorem forall_exists_preimage_tateClasses_of_relIndex {C : Type*} [AddCommGroup C]
    [Module F C] (π : Representation F G C) (φ : C →ₗ[F] TensorSpace F V m n)
    (hφ : ∀ g c, φ (π g c) = twistedTensorRep ρ χ m n p g (φ c)) {H K : Subgroup G}
    (hKH : K ≤ H) (hidx : (K.relIndex H : F) ≠ 0)
    (hK : ∀ t ∈ tateClasses ρ χ K m n p, ∃ c : C, (∀ g ∈ K, π g c = c) ∧ φ c = t) :
    ∀ t ∈ tateClasses ρ χ H m n p, ∃ c : C, (∀ g ∈ H, π g c = c) ∧ φ c = t := by
  intro t ht
  have hsurj : ∀ w : TensorSpace F V m n, (∀ h ∈ K.subgroupOf H,
      ((twistedTensorRep ρ χ m n p).comp H.subtype) h w = w) →
      ∃ c : C, (∀ h ∈ K.subgroupOf H, (π.comp H.subtype) h c = c) ∧ φ c = w := by
    intro w hw
    obtain ⟨c, hc, hφc⟩ := hK w (mem_tateClasses.2 fun g hg =>
      hw ⟨g, hKH hg⟩ (Subgroup.mem_subgroupOf.2 hg))
    exact ⟨c, fun h hh => hc h (Subgroup.mem_subgroupOf.1 hh), hφc⟩
  have htH : t ∈ Representation.invariants ((twistedTensorRep ρ χ m n p).comp H.subtype) := by
    rw [Representation.mem_invariants]
    exact fun g => mem_tateClasses.1 ht g g.2
  obtain ⟨c, hc, hφc⟩ := forall_exists_invariant_preimage_of_index (π.comp H.subtype)
    ((twistedTensorRep ρ χ m n p).comp H.subtype) φ (fun g c => hφ g c) (K.subgroupOf H) hidx
    hsurj t htH
  rw [Representation.mem_invariants] at hc
  exact ⟨c, fun g hg => hc ⟨g, hg⟩, hφc⟩

end FiniteIndex

section Similitude

variable {G F V : Type*} [Group G] [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

/-- If `ψ (g x) (g y) = c ψ(x, y)`, the contragredient action of `g` multiplies the tensor of `ψ`
by `c⁻¹`. -/
theorem tensorMap_bilinTensor_of_similitude (ψ : LinearMap.BilinForm F V) (g : V ≃ₗ[F] V)
    (c : Fˣ) (h : ∀ x y, ψ (g x) (g y) = (c : F) * ψ x y) :
    tensorMap 0 2 g (bilinTensor ψ) = ((c⁻¹ : Fˣ) : F) • bilinTensor ψ := by
  have key : PiTensorProduct.map (fun _ : Fin 2 =>
      (g.symm.dualMap : Module.Dual F V →ₗ[F] Module.Dual F V))
      (bilinDualTensor (Module.finBasis F V) ψ) =
      ((c⁻¹ : Fˣ) : F) • bilinDualTensor (Module.finBasis F V) ψ := by
    refine eq_of_dualSqEval_basis (Module.finBasis F V) fun i j => ?_
    rw [dualSqEval_map, map_smul, dualSqEval_bilinDualTensor, dualSqEval_bilinDualTensor,
      smul_eq_mul]
    have h' := h (g.symm (Module.finBasis F V i)) (g.symm (Module.finBasis F V j))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h'
    rw [h', ← mul_assoc, Units.inv_mul, one_mul]
  rw [bilinTensor, tensorMap_unit_tmul, key, TensorProduct.tmul_smul]

variable {ρ : G →* (V ≃ₗ[F] V)} {χ : G →* Fˣ}

/-- **A similitude form with multiplier `χ` is a Tate class of twist `1`**: if
`ψ (ρ g x) (ρ g y) = χ(g) ψ(x, y)` for `g ∈ H`, then `bilinTensor ψ ∈ (T 0 2 ⊗ F(1))^H`. -/
theorem bilinTensor_mem_tateClasses (ψ : LinearMap.BilinForm F V) {H : Subgroup G}
    (h : ∀ g ∈ H, ∀ x y, ψ (ρ g x) (ρ g y) = (χ g : F) * ψ x y) :
    bilinTensor ψ ∈ tateClasses ρ χ H 0 2 1 := by
  refine mem_tateClasses.2 fun g hg => ?_
  rw [twistedTensorRep_apply, tensorMap_bilinTensor_of_similitude ψ (ρ g) (χ g) (h g hg),
    smul_smul, zpow_one, Units.mul_inv, one_smul]

/-- Conversely, a Tate class of twist `1` of the form `bilinTensor ψ` is a similitude form with
multiplier `χ` on `H`. -/
theorem similitude_of_bilinTensor_mem_tateClasses (ψ : LinearMap.BilinForm F V)
    {H : Subgroup G} (hψ : bilinTensor ψ ∈ tateClasses ρ χ H 0 2 1) {g : G} (hg : g ∈ H)
    (x y : V) : ψ (ρ g x) (ρ g y) = (χ g : F) * ψ x y := by
  have h1 := mem_tateClasses.1 hψ g hg
  rw [twistedTensorRep_apply, zpow_one] at h1
  have h2 : tensorMap 0 2 (ρ g) (bilinTensor ψ) = (((χ g)⁻¹ : Fˣ) : F) • bilinTensor ψ := by
    calc tensorMap 0 2 (ρ g) (bilinTensor ψ)
        = (((χ g)⁻¹ : Fˣ) : F) • ((χ g : F) • tensorMap 0 2 (ρ g) (bilinTensor ψ)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = (((χ g)⁻¹ : Fˣ) : F) • bilinTensor ψ := by rw [h1]
  have h3 := bilin_eq_smul_of_tensorMap_bilinTensor ψ (ρ g) _ h2 x y
  rw [h3, ← mul_assoc, Units.mul_inv, one_mul]

/-- **The polarization tensor is a Tate class of twist `1` exactly when the action is by
similitudes with multiplier `χ`.** -/
theorem bilinTensor_mem_tateClasses_iff (ψ : LinearMap.BilinForm F V) {H : Subgroup G} :
    bilinTensor ψ ∈ tateClasses ρ χ H 0 2 1 ↔
      ∀ g ∈ H, ∀ x y, ψ (ρ g x) (ρ g y) = (χ g : F) * ψ x y :=
  ⟨fun hψ _ hg x y => similitude_of_bilinTensor_mem_tateClasses ψ hψ hg x y,
    bilinTensor_mem_tateClasses ψ⟩

/-- **Similitude representations.** Let `ψ : V × V → W` be a nonzero bilinear map, `σ` a
homomorphism from `G` to the similitude group `GSp(V, ψ)` and `f : W → F` linear (for `W` a line,
such as `ℚ_ℓ(1)`, a coordinate). Then `f ∘ ψ` is a Tate class of twist `1` in `T 0 2`, for the
action of `G` on `V` through `σ` and the multiplier character `μ ∘ σ`, for every subgroup `H`. -/
theorem bilinTensor_compr₂_mem_tateClasses {W : Type*} [AddCommGroup W] [Module F W]
    {ψ : V →ₗ[F] V →ₗ[F] W} (hψ : ψ ≠ 0) (σ : G →* similitudeGroup ψ) (f : W →ₗ[F] F)
    (H : Subgroup G) :
    bilinTensor (ψ.compr₂ f) ∈ tateClasses ((similitudeGroup ψ).subtype.comp σ)
      ((similitudeMultiplier ψ hψ).comp σ) H 0 2 1 := by
  refine bilinTensor_mem_tateClasses _ fun g _ x y => ?_
  rw [LinearMap.compr₂_apply, LinearMap.compr₂_apply]
  change f (ψ ((σ g : V ≃ₗ[F] V) x) ((σ g : V ≃ₗ[F] V) y)) =
    (similitudeMultiplier ψ hψ (σ g) : F) * f (ψ x y)
  rw [similitudeMultiplier_spec, map_smul, smul_eq_mul]

end Similitude

section GaloisSimilitude

open PadicInt

variable {ℓ : ℕ} [Fact ℓ.Prime] {M : Type*} [AddCommGroup M] {K L : Type*} [Field K] [Field L]
  [Algebra K L] [DistribMulAction (L ≃ₐ[K] L) M]
  {e : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+
    AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) →+
      AddSubgroup.torsionBy (Additive Lˣ) ((ℓ ^ n : ℕ) : ℤ)}
  {he : IsCompatibleTorsionPairing ℓ e}

/-- **The Weil-type pairing on `V_ℓ M` is a Tate class of twist `1` for every subgroup of the
Galois group.** Let `L` be algebraically closed with `(ℓ : L) ≠ 0`, the finite-level pairings
`e n : M[ℓ^n] × M[ℓ^n] → μ_{ℓ^n}(L)` compatible and `Aut(L/K)`-equivariant, `V_ℓ M` finite
dimensional and `ψ = rationalTatePairing e he ≠ 0` (values in `ℚ_ℓ(1)`). For any linear form
`f` on `ℚ_ℓ(1)` and any subgroup `H ≤ Aut(L/K)`, `f ∘ ψ ∈ (T 0 2 ⊗ ℚ_ℓ(1))^H` for the action of
`Aut(L/K)` on `V_ℓ M` by similitudes; the twisting character is the multiplier, which is the
cyclotomic character by `multiplier_galoisSimilitudeRepresentation_apply`. -/
theorem bilinTensor_rationalTatePairing_compr₂_mem_tateClasses [IsAlgClosed L]
    [FiniteDimensional ℚ_[ℓ] (rationalTate ℓ M)] (hℓL : (ℓ : L) ≠ 0)
    (heq : IsEquivariantTorsionPairing ℓ (L ≃ₐ[K] L) e) (hψ : rationalTatePairing e he ≠ 0)
    (f : rationalTate ℓ (Additive Lˣ) →ₗ[ℚ_[ℓ]] ℚ_[ℓ]) (H : Subgroup (L ≃ₐ[K] L)) :
    bilinTensor ((rationalTatePairing e he).compr₂ f) ∈
      tateClasses ((similitudeGroup (rationalTatePairing e he)).subtype.comp
          (galoisSimilitudeRepresentation (he := he) hℓL heq))
        ((similitudeMultiplier _ hψ).comp (galoisSimilitudeRepresentation (he := he) hℓL heq))
        H 0 2 1 :=
  bilinTensor_compr₂_mem_tateClasses hψ _ f H

/-- The twisting character of `bilinTensor_rationalTatePairing_compr₂_mem_tateClasses` is the
cyclotomic character `χ_ℓ : Aut(L/K) → ℤ_ℓˣ ⊆ ℚ_ℓˣ`. -/
theorem multiplier_galoisSimilitudeRepresentation_apply [IsAlgClosed L] (hℓL : (ℓ : L) ≠ 0)
    (heq : IsEquivariantTorsionPairing ℓ (L ≃ₐ[K] L) e) (hψ : rationalTatePairing e he ≠ 0)
    (τ : L ≃ₐ[K] L) :
    ((similitudeMultiplier _ hψ).comp (galoisSimilitudeRepresentation (he := he) hℓL heq)) τ =
      Units.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toMonoidHom (cyclotomicCharacter L ℓ τ.toRingEquiv) :=
  similitudeMultiplier_galoisSimilitudeRepresentation hℓL heq hψ τ

/-- The action on `V_ℓ M` in `bilinTensor_rationalTatePairing_compr₂_mem_tateClasses` is the
Galois action `rationalTate.representation`. -/
theorem subtype_comp_galoisSimilitudeRepresentation_apply [IsAlgClosed L] (hℓL : (ℓ : L) ≠ 0)
    (heq : IsEquivariantTorsionPairing ℓ (L ≃ₐ[K] L) e) (τ : L ≃ₐ[K] L)
    (z : rationalTate ℓ M) :
    ((similitudeGroup (rationalTatePairing e he)).subtype.comp
        (galoisSimilitudeRepresentation (he := he) hℓL heq)) τ z =
      rationalTate.representation ℓ M (L ≃ₐ[K] L) τ z :=
  coe_galoisSimilitudeRepresentation_apply (he := he) hℓL heq τ z

end GaloisSimilitude

end ArithmeticOfJacobiPolynomials
