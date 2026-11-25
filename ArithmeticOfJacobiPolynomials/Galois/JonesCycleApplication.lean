/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.External

/-!
# The manuscript's fixed-point formulation of Jones's theorem

Theorem 5.4 quotes Jones, Corollary 1.3. Jones counts fixed points by subtracting the support size.
Counting the fixed points directly gives the manuscript's formulation.
-/

public section

namespace ArithmeticOfJacobiPolynomials

/-- **Theorem 5.4 (Jones).** A primitive permutation group containing a
nontrivial single cycle with at least three fixed points contains the
alternating group. Conditional on the fully general Jones Corollary 1.3 input. -/
theorem alternatingGroup_le_of_singleCycle_three_fixedPoints
    (hJones : JonesCycleTheorem) {α : Type} [Fintype α] [DecidableEq α]
    (G : Subgroup (Equiv.Perm α)) (hprim : MulAction.IsPreprimitive G α)
    (σ : Equiv.Perm α) (hσG : σ ∈ G) (hσ : σ.IsCycle)
    (hfixed : 3 ≤ (Finset.univ.filter fun x => σ x = x).card) :
    alternatingGroup α ≤ G := by
  have he : (Finset.univ.filter fun x => σ x = x) = Finset.univ \ σ.support := by
    ext x
    simp
  rw [he, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ] at hfixed
  exact hJones α G hprim σ hσG hσ hfixed

end ArithmeticOfJacobiPolynomials
