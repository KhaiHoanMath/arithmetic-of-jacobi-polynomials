/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.EllAdicLie
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Compactness.Compact

/-!
# Finite index, open subgroups and the identity germ (proof of Corollary 6.6)

The proof of Corollary 6.6 says: "Passing to a number field preserves the Lie algebra because
the Galois subgroup has finite index." This file proves, for an arbitrary topological group `Γ`,
the generic topology behind this sentence, and applies it to the `ℓ`-adic Lie algebra
`ArithmeticOfJacobiPolynomials.ellAdicLie` of
`ArithmeticOfJacobiPolynomials/Algebra/EllAdicLie.lean`.

## Generic part (any topological group `Γ`, subgroups `H ≤ G`)

* `isOpen_subgroupOf_iff`: `H` is open in `G` iff some neighbourhood `W` of `1` in `Γ`
  satisfies `G ∩ W ⊆ H` (local identity criterion);
* `finiteIndex_subgroupOf_iff_isOpen`: for `G` compact and `H` closed, `H` has finite index in
  `G` iff `H` is open in `G` (closed + finite index ⇒ open is Mathlib's
  `Subgroup.isOpen_of_isClosed_of_finiteIndex`; open in a compact group ⇒ finite index is proved
  here);
* `SameGerm G H` (the subgroups agree on a neighbourhood of `1`): an equivalence relation, and
  for `H ≤ G`, `SameGerm G H ↔ H` is open in `G`
  (`sameGerm_iff_isOpen_subgroupOf`), hence ↔ finite index when `G` is compact and `H` closed
  (`sameGerm_iff_finiteIndex`).

## Application to the `p`-adic Lie algebra

* `ellAdicLie_eq_of_sameGerm`: subgroups of `Aˣ` with the same germ at `1` have the same
  `p`-adic Lie algebra (the Lie algebra is a germ invariant);
* `ellAdicLie_eq_of_commensurable`: two compact subgroups `G`, `H` of `Aˣ` for which `G ⊓ H` has
  finite index in both have the same Lie algebra (commensurability invariance; the file
  `EllAdicLie` has the case `H ≤ G`);

## What is *not* proved: the Mathlib Lie algebra

`ArithmeticOfJacobiPolynomials.ellAdicLie p G = {X | ∀ᶠ t → 0, exp (t • X) ∈ G}` is the textbook
definition of the
Lie algebra of a closed subgroup of `GL_n(ℚ_p)` (Serre, *Lie algebras and Lie groups*, Part II,
Ch. IV §§ 1, 7, 8; Bourbaki, *Lie*, III §§ 1, 7; Zarhin 2002, §2 quotes Serre [23]).
Mathlib has an *abstract* Lie algebra `GroupLieAlgebra I G` of a Lie group
(`Mathlib/Geometry/Manifold/GroupLieAlgebra.lean`: the tangent space at `1` with the bracket of
left-invariant vector fields; Lie groups `LieGroup I n G` over any nontrivially normed field,
including `ℚ_p`), but it does not contain what would be required to compare the two:

1. a `ChartedSpace`/`LieGroup` structure on an *open subgroup* `U` of a Lie group `G`
   (an open subset inherits charts, but no group-compatible instance on `↥U` exists), and the
   fact that the inclusion `U ↪ G` induces a Lie algebra isomorphism
   `GroupLieAlgebra I U ≃ₗ⁅𝕜⁆ GroupLieAlgebra I G` (this is the Mathlib form of the
   statement "`Lie(H) = Lie(G)` for `H` open in `G`");
2. Cartan's closed subgroup theorem over `ℚ_p` (a closed subgroup of `GL_n(ℚ_p)` is a Lie
   subgroup: `LieGroup` structure on `H`, with `H ↪ GL_n` an immersion);
3. the comparison `GroupLieAlgebra I H ≃ ellAdicLie p H` via `exp` (Serre LG 4.8 / Bourbaki
   III §7.3: the Lie algebra of an analytic subgroup is `{X | exp(tX) ∈ H}`).

The arguments below use the exponential-defined Lie algebra directly. The statements proved here are
  therefore the statements about the exponential-defined
Lie algebra, which is what Zarhin's `g_{ℓ,X}` (Zarhin 2002, §2, "We write `g_{ℓ,X}` for the Lie
algebra of `G_{ℓ,X}`", with `G_{ℓ,X}` an `ℓ`-adic Lie subgroup by Serre [23]) denotes.
-/

@[expose] public section

open Filter Topology

namespace ArithmeticOfJacobiPolynomials

namespace FiniteIndexLie

/-! ### The identity germ -/

section Germ

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

/-- Two subgroups have the same germ at the identity if they agree on a neighbourhood of `1`. -/
def SameGerm (G H : Subgroup Γ) : Prop :=
  ∃ W ∈ 𝓝 (1 : Γ), ∀ u ∈ W, u ∈ G ↔ u ∈ H

theorem SameGerm.refl (G : Subgroup Γ) : SameGerm G G :=
  ⟨Set.univ, Filter.univ_mem, fun _ _ => Iff.rfl⟩

theorem SameGerm.symm {G H : Subgroup Γ} (h : SameGerm G H) : SameGerm H G := by
  obtain ⟨W, hW, hWiff⟩ := h
  exact ⟨W, hW, fun u hu => (hWiff u hu).symm⟩

theorem SameGerm.trans {G H K : Subgroup Γ} (h₁ : SameGerm G H) (h₂ : SameGerm H K) :
    SameGerm G K := by
  obtain ⟨W₁, hW₁, h₁⟩ := h₁
  obtain ⟨W₂, hW₂, h₂⟩ := h₂
  exact ⟨W₁ ∩ W₂, Filter.inter_mem hW₁ hW₂, fun u hu => (h₁ u hu.1).trans (h₂ u hu.2)⟩

end Germ

/-! ### Open subgroups, finite index, and the local identity criterion -/

section Topology

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- **Local identity criterion.** A subgroup `H` is open in a subgroup `G` of a topological
group iff `G ∩ W ⊆ H` for some neighbourhood `W` of `1`. -/
theorem isOpen_subgroupOf_iff {G H : Subgroup Γ} :
    IsOpen (H.subgroupOf G : Set G) ↔ ∃ W ∈ 𝓝 (1 : Γ), ∀ u ∈ G, u ∈ W → u ∈ H := by
  constructor
  · intro hH
    have h1 : (H.subgroupOf G : Set G) ∈ 𝓝 (1 : G) := hH.mem_nhds (H.subgroupOf G).one_mem
    obtain ⟨W, hW, hWsub⟩ := (mem_nhds_induced (Subtype.val : G → Γ) (1 : G) _).mp h1
    refine ⟨W, hW, fun u huG huW => ?_⟩
    have : (⟨u, huG⟩ : G) ∈ (H.subgroupOf G : Set G) := hWsub huW
    exact Subgroup.mem_subgroupOf.mp this
  · rintro ⟨W, hW, hWH⟩
    refine Subgroup.isOpen_of_mem_nhds (H.subgroupOf G) (g := (1 : G)) ?_
    refine (mem_nhds_induced (Subtype.val : G → Γ) (1 : G) _).mpr ⟨W, hW, fun x hx => ?_⟩
    exact Subgroup.mem_subgroupOf.mpr (hWH x.1 x.2 hx)

/-- For `H ≤ G`: `H` is open in `G` iff `G` and `H` have the same germ at `1`. -/
theorem sameGerm_iff_isOpen_subgroupOf {G H : Subgroup Γ} (hHG : H ≤ G) :
    SameGerm G H ↔ IsOpen (H.subgroupOf G : Set G) := by
  rw [isOpen_subgroupOf_iff]
  constructor
  · rintro ⟨W, hW, hWiff⟩
    exact ⟨W, hW, fun u huG huW => (hWiff u huW).mp huG⟩
  · rintro ⟨W, hW, hWH⟩
    exact ⟨W, hW, fun u huW => ⟨fun huG => hWH u huG huW, fun huH => hHG huH⟩⟩

/-- A closed subgroup of finite index in `G` is open in `G`. -/
theorem isOpen_subgroupOf_of_isClosed_of_finiteIndex {G H : Subgroup Γ}
    (hH : IsClosed (H : Set Γ)) [(H.subgroupOf G).FiniteIndex] :
    IsOpen (H.subgroupOf G : Set G) :=
  Subgroup.isOpen_of_isClosed_of_finiteIndex _ (hH.preimage continuous_subtype_val)

/-- A subgroup that is open in a compact subgroup `G` has finite index in `G`. -/
theorem finiteIndex_subgroupOf_of_isOpen {G H : Subgroup Γ} (hG : IsCompact (G : Set Γ))
    (hH : IsOpen (H.subgroupOf G : Set G)) : (H.subgroupOf G).FiniteIndex := by
  have : CompactSpace G := isCompact_iff_compactSpace.mp hG
  have : DiscreteTopology (G ⧸ H.subgroupOf G) := QuotientGroup.discreteTopology hH
  have : Finite (G ⧸ H.subgroupOf G) := finite_of_compact_of_discrete
  exact Subgroup.finiteIndex_of_finite_quotient

/-- **Finite index = open, in a compact group.** If `G` is compact and `H` closed, then `H` has
finite index in `G` iff `H` is open in `G`. -/
theorem finiteIndex_subgroupOf_iff_isOpen {G H : Subgroup Γ} (hG : IsCompact (G : Set Γ))
    (hH : IsClosed (H : Set Γ)) :
    (H.subgroupOf G).FiniteIndex ↔ IsOpen (H.subgroupOf G : Set G) :=
  ⟨fun _ => isOpen_subgroupOf_of_isClosed_of_finiteIndex hH, finiteIndex_subgroupOf_of_isOpen hG⟩

/-- **Finite index = same germ at `1`** (for `H ≤ G` closed, `G` compact). -/
theorem sameGerm_iff_finiteIndex {G H : Subgroup Γ} (hHG : H ≤ G) (hG : IsCompact (G : Set Γ))
    (hH : IsClosed (H : Set Γ)) :
    SameGerm G H ↔ (H.subgroupOf G).FiniteIndex :=
  (sameGerm_iff_isOpen_subgroupOf hHG).trans (finiteIndex_subgroupOf_iff_isOpen hG hH).symm

end Topology

/-! ### Application to the `p`-adic Lie algebra -/

section Lie

variable {p : ℕ} [Fact p.Prime] {A : Type*} [NormedRing A] [NormedAlgebra ℚ_[p] A]
  [CompleteSpace A]

/-- The `p`-adic Lie algebra depends only on the germ of the subgroup at `1`. -/
theorem ellAdicLie_eq_of_sameGerm {G H : Subgroup Aˣ} (h : SameGerm G H) :
    ellAdicLie p G = ellAdicLie p H := by
  obtain ⟨W, hW, hWiff⟩ := h
  obtain ⟨O, hOW, hOo, hO1⟩ := mem_nhds_iff.mp hW
  have h1 : ellAdicLie p (G ⊓ H) = ellAdicLie p G :=
    ellAdicLie_eq_of_nhds inf_le_left ⟨O, hOo, hO1, fun u huG huO =>
      Subgroup.mem_inf.mpr ⟨huG, (hWiff u (hOW huO)).mp huG⟩⟩
  have h2 : ellAdicLie p (G ⊓ H) = ellAdicLie p H :=
    ellAdicLie_eq_of_nhds inf_le_right ⟨O, hOo, hO1, fun u huH huO =>
      Subgroup.mem_inf.mpr ⟨(hWiff u (hOW huO)).mpr huH, huH⟩⟩
  exact h1.symm.trans h2

/-- **Commensurability invariance.** If `G` and `H` are compact subgroups of `Aˣ` and `G ⊓ H` has
finite index in both, then `G` and `H` have the same `p`-adic Lie algebra. -/
theorem ellAdicLie_eq_of_commensurable {G H : Subgroup Aˣ} (hG : IsCompact (G : Set Aˣ))
    (hH : IsCompact (H : Set Aˣ)) [((G ⊓ H).subgroupOf G).FiniteIndex]
    [((G ⊓ H).subgroupOf H).FiniteIndex] : ellAdicLie p G = ellAdicLie p H := by
  have := units_t2Space (A := A)
  have hGH : IsCompact ((G ⊓ H : Subgroup Aˣ) : Set Aˣ) := by
    rw [Subgroup.coe_inf]
    exact hG.inter_right hH.isClosed
  have h1 : ellAdicLie p (G ⊓ H) = ellAdicLie p G :=
    ellAdicLie_eq_of_isCompact_of_finiteIndex inf_le_left hGH
  have h2 : ellAdicLie p (G ⊓ H) = ellAdicLie p H :=
    ellAdicLie_eq_of_isCompact_of_finiteIndex inf_le_right hGH
  exact h1.symm.trans h2

end Lie

end FiniteIndexLie

end ArithmeticOfJacobiPolynomials
