/- Assembled by AxiomProver. -/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Rational descent by averaging (proof of Corollary 6.6, transfer steps)

The proof of Corollary 6.6 transfers Zarhin's conclusions [Zarhin02] from the situation
treated there to the one stated, by three formal steps:

* "A Galois-invariant class represented by algebraic cycles over a finite extension descends
  with rational coefficients by averaging over a finite Galois extension";
* "Passing to a number field preserves [...] because the Galois subgroup has finite index";
* "For powers, the groups act diagonally on direct sums".

This file proves the linear-algebra content of these steps for an arbitrary group `G` acting
linearly on vector spaces over a field `k` (in the application `k = ℚ_ℓ` and `G` is an
absolute Galois group).

* `exists_invariant_preimage_of_index` (relative averaging): if `φ : V → W` is
  `G`-equivariant, `H ≤ G` has index invertible in `k`, `w ∈ W` is `G`-invariant, and
  `w = φ v₀` with `v₀` invariant under `H`, then `w = φ v` with `v` invariant under `G`:
  take `v = [G : H]⁻¹ ∑_{gH ∈ G/H} g v₀`.
* `forall_exists_invariant_preimage_of_index`: surjectivity of `φ` onto invariants passes
  from a subgroup of index invertible in `k` to the whole group.
* `invariants_inf_range_eq_map`: for a finite group of order invertible in `k`, the invariant
  vectors in the image of `φ` are exactly the images of invariant vectors.
* `forall_exists_invariant_preimage_galois`: the case of the Galois group of a Galois
  extension `E/F` and the subgroup `Gal(E/L)` fixing a finite intermediate extension `L/F`
  (its index is `[L : F]`), for coefficients of characteristic zero.
* `mem_invariants_prod`, `mem_invariants_directSum`: invariants of a diagonal action on a
  product / direct sum are computed componentwise.
* `ker_directSum_const`, `ker_asGroupHom_directSum_const`,
  `nonempty_range_directSum_const_mulEquiv`: a group acting diagonally
  on a nonempty power `⨁_{i ∈ ι} V` has the same kernel as on `V`, so its image on the power
  is isomorphic to its image on `V`.

The Galois descent of algebraic cycles is in `ArithmeticOfJacobiPolynomials.ChowGaloisDescent`
(applied to cycle classes in `ArithmeticOfJacobiPolynomials/Geometry/AbelianCycleClass.lean`), and
the `ℓ`-adic Lie algebra of a subgroup of `GL` is in
`ArithmeticOfJacobiPolynomials/Algebra/EllAdicLie.lean`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

section Averaging

variable {k G V W : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- **Relative averaging.** Let `φ : V → W` be `G`-equivariant and let `H ≤ G` be a subgroup
whose index is nonzero in `k`. If `w` is `G`-invariant and `w = φ v₀` with `v₀` invariant
under `H`, then `w = φ v` for a `G`-invariant `v` (namely
`v = [G : H]⁻¹ ∑_{gH ∈ G/H} g v₀`). -/
theorem exists_invariant_preimage_of_index (ρ : Representation k G V)
    (σ : Representation k G W) (φ : V →ₗ[k] W) (hφ : ∀ g v, φ (ρ g v) = σ g (φ v))
    (H : Subgroup G) (hH : (H.index : k) ≠ 0) {w : W} (hw : w ∈ σ.invariants) {v₀ : V}
    (hv₀ : ∀ h ∈ H, ρ h v₀ = v₀) (hφv₀ : φ v₀ = w) :
    ∃ v ∈ ρ.invariants, φ v = w := by
  have hfin : H.FiniteIndex := ⟨fun h => hH (by rw [h, Nat.cast_zero])⟩
  classical
  let _inst : Fintype (G ⧸ H) := Fintype.ofFinite _
  -- the translate of `v₀` by a left coset of `H`
  let T : G ⧸ H → V := fun q => Quotient.liftOn' q (fun g => ρ g v₀) (fun a b hab => by
    have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have hb : b = a * (a⁻¹ * b) := (mul_inv_cancel_left a b).symm
    change ρ a v₀ = ρ b v₀
    rw [hb, map_mul, Module.End.mul_apply, hv₀ _ hab'])
  have hT : ∀ g : G, T (g : G ⧸ H) = ρ g v₀ := fun g => rfl
  have hTsmul : ∀ (x : G) (q : G ⧸ H), T (x • q) = ρ x (T q) := by
    intro x q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulAction.Quotient.smul_mk, hT, hT, smul_eq_mul, map_mul, Module.End.mul_apply]
  have hφT : ∀ q, φ (T q) = w := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hT, hφ, hφv₀]
    rw [Representation.mem_invariants] at hw
    exact hw g
  refine ⟨(H.index : k)⁻¹ • ∑ q, T q, ?_, ?_⟩
  · rw [Representation.mem_invariants]
    intro x
    rw [map_smul, map_sum]
    congr 1
    calc ∑ q, ρ x (T q) = ∑ q, T (x • q) := by simp only [hTsmul]
      _ = ∑ q, T q := Fintype.sum_equiv (MulAction.toPerm x) _ _ (fun _ => rfl)
  · rw [map_smul, map_sum]
    simp only [hφT]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      ← Subgroup.index_eq_card, ← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hH,
      one_smul]

/-- **Surjectivity onto invariants descends along a subgroup of finite index.** If every
`H`-invariant vector of `W` is the image of an `H`-invariant vector of `V`, and the index of
`H` is nonzero in `k`, then every `G`-invariant vector of `W` is the image of a `G`-invariant
vector of `V`. -/
theorem forall_exists_invariant_preimage_of_index (ρ : Representation k G V)
    (σ : Representation k G W) (φ : V →ₗ[k] W) (hφ : ∀ g v, φ (ρ g v) = σ g (φ v))
    (H : Subgroup G) (hH : (H.index : k) ≠ 0)
    (hsurj : ∀ w : W, (∀ h ∈ H, σ h w = w) → ∃ v : V, (∀ h ∈ H, ρ h v = v) ∧ φ v = w) :
    ∀ w ∈ σ.invariants, ∃ v ∈ ρ.invariants, φ v = w := by
  intro w hw
  have hw' := hw
  rw [Representation.mem_invariants] at hw'
  obtain ⟨v₀, hv₀, hφv₀⟩ := hsurj w (fun h _ => hw' h)
  exact exists_invariant_preimage_of_index ρ σ φ hφ H hH hw hv₀ hφv₀

/-- An equivariant map sends invariant vectors to invariant vectors. -/
theorem map_invariants_le (ρ : Representation k G V) (σ : Representation k G W)
    (φ : V →ₗ[k] W) (hφ : ∀ g v, φ (ρ g v) = σ g (φ v)) :
    ρ.invariants.map φ ≤ σ.invariants := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
  rw [Representation.mem_invariants] at hv
  rw [Representation.mem_invariants]
  intro g
  rw [← hφ, hv]

/-- **Averaging over a finite group.** For a finite group `G` whose order is nonzero in `k`
and a `G`-equivariant map `φ : V → W`, the `G`-invariant vectors in the image of `φ` are
exactly the images of the `G`-invariant vectors. -/
theorem invariants_inf_range_eq_map [Finite G] (hG : (Nat.card G : k) ≠ 0)
    (ρ : Representation k G V) (σ : Representation k G W) (φ : V →ₗ[k] W)
    (hφ : ∀ g v, φ (ρ g v) = σ g (φ v)) :
    σ.invariants ⊓ LinearMap.range φ = ρ.invariants.map φ := by
  refine le_antisymm ?_ (le_inf (map_invariants_le ρ σ φ hφ) (LinearMap.map_le_range))
  intro w hwr
  obtain ⟨hw, hr⟩ := Submodule.mem_inf.1 hwr
  obtain ⟨v₀, hv₀⟩ := LinearMap.mem_range.1 hr
  have hbot : ((⊥ : Subgroup G).index : k) ≠ 0 := by rwa [Subgroup.index_bot]
  obtain ⟨v, hv, hφv⟩ := exists_invariant_preimage_of_index ρ σ φ hφ ⊥ hbot hw
    (v₀ := v₀) (fun h hh => by rw [Subgroup.mem_bot.1 hh, map_one, Module.End.one_apply]) hv₀
  exact Submodule.mem_map.2 ⟨v, hv, hφv⟩

/-- **Galois descent of invariants along a finite extension.** Let `E/F` be a Galois
extension, `L` an intermediate field finite over `F`, and `k` a field of characteristic zero.
For `Gal(E/F)`-equivariant `φ : V → W`: if every `Gal(E/L)`-invariant vector of `W` is the
image of a `Gal(E/L)`-invariant vector of `V`, then every `Gal(E/F)`-invariant vector of `W`
is the image of a `Gal(E/F)`-invariant vector of `V`. (Here `Gal(E/L)` is
`L.fixingSubgroup`, of index `[L : F]`.) -/
theorem forall_exists_invariant_preimage_galois {F E : Type*} [Field F] [Field E]
    [Algebra F E] [IsGalois F E] [CharZero k] (L : IntermediateField F E)
    [FiniteDimensional F L] (ρ : Representation k (E ≃ₐ[F] E) V)
    (σ : Representation k (E ≃ₐ[F] E) W) (φ : V →ₗ[k] W)
    (hφ : ∀ g v, φ (ρ g v) = σ g (φ v))
    (hsurj : ∀ w : W, (∀ h ∈ L.fixingSubgroup, σ h w = w) →
      ∃ v : V, (∀ h ∈ L.fixingSubgroup, ρ h v = v) ∧ φ v = w) :
    ∀ w ∈ σ.invariants, ∃ v ∈ ρ.invariants, φ v = w := by
  have hidx : (L.fixingSubgroup.index : k) ≠ 0 := by
    exact Nat.cast_ne_zero.2 fun h0 =>
      Module.finrank_pos.ne' ((IntermediateField.finrank_eq_fixingSubgroup_index (L := L)).trans h0)
  exact forall_exists_invariant_preimage_of_index ρ σ φ hφ _ hidx hsurj

end Averaging

section Diagonal

variable {k G : Type*} [Field k] [Group G]

/-- Invariants of the diagonal action on a product are computed componentwise. -/
theorem mem_invariants_prod {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (ρ : Representation k G V) (σ : Representation k G W) (x : V × W) :
    x ∈ (ρ.prod σ).invariants ↔ x.1 ∈ ρ.invariants ∧ x.2 ∈ σ.invariants := by
  simp only [Representation.mem_invariants, Representation.prod_apply_apply, Prod.ext_iff,
    forall_and]

/-- Invariants of the diagonal action on a direct sum are computed componentwise. -/
theorem mem_invariants_directSum {ι : Type*} {V : ι → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] (ρ : ∀ i, Representation k G (V i)) (x : DirectSum ι V) :
    x ∈ (Representation.directSum ρ).invariants ↔ ∀ i, x i ∈ (ρ i).invariants := by
  simp only [Representation.mem_invariants, Representation.directSum_apply, DirectSum.ext_iff,
    DirectSum.lmap_apply]
  exact forall_comm

/-- A group acting diagonally on a nonempty power `⨁_{i ∈ ι} V` of a representation `V` acts
with the same kernel as on `V`. -/
theorem ker_directSum_const {ι V : Type*} [Nonempty ι] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    (Representation.directSum fun _ : ι => ρ).ker = ρ.ker := by
  classical
  ext g
  simp only [MonoidHom.mem_ker, Representation.directSum_apply]
  constructor
  · intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    refine LinearMap.ext fun v => ?_
    have h1 := congrArg (fun x => x i)
      (LinearMap.congr_fun h (DirectSum.lof k ι (fun _ => V) i v))
    simpa only [DirectSum.lof_eq_of, DirectSum.lmap_of, DirectSum.of_eq_same,
      Module.End.one_apply] using h1
  · intro h
    rw [h]
    exact DirectSum.lmap_id

/-- Viewed as a group homomorphism to the units of `End V`, a representation acting diagonally
on a nonempty power `⨁_{i ∈ ι} V` has the same kernel as on `V`. -/
theorem ker_asGroupHom_directSum_const {ι V : Type*} [Nonempty ι] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) :
    (Representation.directSum fun _ : ι => ρ).asGroupHom.ker = ρ.asGroupHom.ker := by
  ext g
  have h : g ∈ (Representation.directSum fun _ : ι => ρ).ker ↔ g ∈ ρ.ker := by
    rw [ker_directSum_const]
  simp only [MonoidHom.mem_ker, Units.ext_iff, Representation.asGroupHom_apply,
    Units.val_one] at h ⊢
  exact h

/-- The image of a group acting diagonally on a nonempty power `⨁_{i ∈ ι} V` is isomorphic
to its image on `V` (images taken in the unit groups of the endomorphism rings). -/
theorem nonempty_range_directSum_const_mulEquiv {ι V : Type*} [Nonempty ι] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) :
    Nonempty ((Representation.directSum fun _ : ι => ρ).asGroupHom.range ≃*
      ρ.asGroupHom.range) :=
  ⟨(QuotientGroup.quotientKerEquivRange _).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (ker_asGroupHom_directSum_const ρ)).trans
      (QuotientGroup.quotientKerEquivRange ρ.asGroupHom))⟩

end Diagonal

end ArithmeticOfJacobiPolynomials
