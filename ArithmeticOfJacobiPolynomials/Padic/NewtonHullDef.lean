/- Assembled by AxiomProver. -/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The lower convex hull of finitely many points

`newtonHull a b S v` is the lower convex hull of the points `(j, v j)`, `j ∈ S ⊆ [a, b]`, as a
function on `[a, b]`: the greatest convex function on `[a, b]` lying below the points. It is the
domain definition of `NewtonPolygonRootSlopes` (the cited Newton polygon theorem, stated in
`External.lean`); it carries no statement about any particular polynomial.
-/

public section

namespace ArithmeticOfJacobiPolynomials

/-- The lower convex hull of the points `(j, v j)`, `j ∈ S ⊆ [a,b]`, evaluated at `x`: the greatest
convex function on `[a,b]` lying below the points. -/
@[expose] noncomputable def newtonHull (a b : ℕ) (S : Finset ℕ) (v : ℕ → ℝ) (x : ℝ) : ℝ :=
  sSup ((fun φ : ℝ → ℝ => φ x) ''
    {φ | ConvexOn ℝ (Set.Icc (a : ℝ) b) φ ∧ ∀ j ∈ S, φ j ≤ v j})

end ArithmeticOfJacobiPolynomials
