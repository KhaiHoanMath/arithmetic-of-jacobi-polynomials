/- Assembled by AxiomProver. -/
module

public import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# Galois groups acting on roots

For a field `K` and `f ∈ K[X]`, `Gal(f/K)` acts faithfully on the roots of `f` in its
splitting field. We express the manuscript's group-theoretic conclusions through this
permutation representation `ArithmeticOfJacobiPolynomials.galPerm f`:

* `Gal(f/K) = S_n`: the action is the full symmetric group on the roots
  (`GaloisGroupIsSymmetric`);
* `Gal(f/K) = W_m = C_2 ≀ S_m`, for a polynomial whose roots are `2m` nonzero elements in
  opposite pairs: the image is the group of all permutations of the roots commuting with
  negation (`GaloisGroupIsWreath`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

variable {K : Type*} [Field K]

/-- The permutation representation of `Gal(f/K)` on the roots of `f` in its splitting
field. -/
@[expose] noncomputable def galPerm (f : K[X]) : f.Gal →* Equiv.Perm (f.rootSet f.SplittingField) :=
  MulAction.toPermHom _ _

theorem galPerm_apply (f : K[X]) (σ : f.Gal) (x : f.rootSet f.SplittingField) :
    galPerm f σ x = σ • x := (rfl)

/-- The permutations of a set `s` that commute with negation, in the sense that
`y = -x ↔ σ y = -σ x` for all `x, y ∈ s`. When `s` consists of `2m` nonzero elements of a
field of characteristic `≠ 2`, closed under negation, this is the hyperoctahedral group
`W_m = C_2 ≀ S_m = 𝔽_2^m ⋊ S_m`. -/
def negCommPerm {L : Type*} [Neg L] (s : Set L) : Subgroup (Equiv.Perm s) where
  carrier := {σ | ∀ x y : s, (y : L) = -(x : L) ↔ ((σ y : s) : L) = -((σ x : s) : L)}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := fun hσ hτ x y => (hτ x y).trans (hσ _ _)
  inv_mem' := by
    intro σ hσ x y
    have key := hσ (σ⁻¹ x) (σ⁻¹ y)
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at key
    exact key.symm

/-- `Gal(f/K)` acts on the roots of `f` as the full symmetric group on them. -/
def GaloisGroupIsSymmetric (f : K[X]) : Prop :=
  Function.Bijective (galPerm f)

theorem galoisGroupIsSymmetric_iff (f : K[X]) :
    GaloisGroupIsSymmetric f ↔ Function.Bijective (galPerm f) := (Iff.rfl)

/-- `Gal(f/K)` acts on the roots of `f` as the group of all permutations commuting with
negation; for `2m` nonzero roots in opposite pairs this is `W_m = C_2 ≀ S_m`. -/
def GaloisGroupIsWreath (f : K[X]) : Prop :=
  (galPerm f).range = negCommPerm (f.rootSet f.SplittingField)

theorem galoisGroupIsWreath_iff (f : K[X]) :
    GaloisGroupIsWreath f ↔ (galPerm f).range = negCommPerm (f.rootSet f.SplittingField) :=
  (Iff.rfl)

theorem mem_negCommPerm_iff {L : Type*} [Neg L] {s : Set L} (σ : Equiv.Perm s) :
    σ ∈ negCommPerm s ↔
      ∀ x y : s, (y : L) = -(x : L) ↔ ((σ y : s) : L) = -((σ x : s) : L) := (Iff.rfl)

end ArithmeticOfJacobiPolynomials
