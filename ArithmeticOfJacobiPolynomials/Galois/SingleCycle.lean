/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.InertiaMembership

/-!
# Single cycles of every length `d ≥ 1`, and Proposition 5.2 including `d = 1`

The manuscript speaks of "a single `d`-cycle" for every `d ≥ 1`. Mathlib's `Equiv.Perm.IsCycle`
excludes the identity, so we record the convention explicitly: a single `1`-cycle is the
identity (a one-element orbit), and for `d ≥ 2` a single `d`-cycle is a cycle with support of
size `d`. With this convention Proposition 5.2's first assertion holds for every `d ≥ 1`, which
is the range its hypotheses give (`1 ≤ k₀ ≤ n`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial NumberField

/-- `σ` is a single `d`-cycle: the identity if `d = 1`, a cycle with support of size `d` if
`d ≥ 2`. (For `d = 0` there is no single `0`-cycle.) -/
def IsSingleCycleOfLength {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α)
    (d : ℕ) : Prop :=
  (d = 1 ∧ σ = 1) ∨ (2 ≤ d ∧ σ.IsCycle ∧ σ.support.card = d)

theorem isSingleCycleOfLength_iff {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α)
    (d : ℕ) : IsSingleCycleOfLength σ d ↔
      (d = 1 ∧ σ = 1) ∨ (2 ≤ d ∧ σ.IsCycle ∧ σ.support.card = d) := Iff.rfl

/-- A single `d`-cycle moves exactly `d` points when `d ≥ 2` and none when `d = 1`; in both cases
it has exactly one orbit that is not a fixed point, or (for `d = 1`) is the identity. -/
theorem IsSingleCycleOfLength.support_card {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Equiv.Perm α} {d : ℕ} (h : IsSingleCycleOfLength σ d) :
    σ.support.card = if d = 1 then 0 else d := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hd, -, hc⟩
  · simp
  · rw [hc]
    exact (ite_eq_right_iff.mpr fun h => absurd h (by omega)).symm

open Classical in
/-- **Proposition 5.2, first assertion, every `d ≥ 1`.** Under the hypotheses of Proposition 5.2,
with `d = n + 1 - k₀` (so `1 ≤ d ≤ n`), an inertia subgroup at `p` of
`Gal(P_n^{(a/u,b/v)}/ℚ)` contains a single `d`-cycle (the identity when `d = 1`). -/
theorem exists_isSingleCycleOfLength_galPerm_jacobiP_mem_inertia {p n : ℕ} {a u b v D r : ℤ}
    (h : JacobiCycleHypotheses p n a u b v D r) :
    1 ≤ n + 1 - jacobiCycleIndexNat p n D r ∧
    ∃ P : Ideal (𝓞 (jacobiP ((a : ℚ) / u) ((b : ℚ) / v) n).SplittingField),
      P.IsMaximal ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧
      ∃ σ : (jacobiP ((a : ℚ) / u) ((b : ℚ) / v) n).Gal,
        σ ∈ P.inertia Gal((jacobiP ((a : ℚ) / u) ((b : ℚ) / v) n).SplittingField/ℚ) ∧
        IsSingleCycleOfLength (galPerm _ σ) (n + 1 - jacobiCycleIndexNat p n D r) := by
  have hle := h.index_le_n
  refine ⟨by omega, ?_⟩
  rcases (show n + 1 - jacobiCycleIndexNat p n D r = 1 ∨
      2 ≤ n + 1 - jacobiCycleIndexNat p n D r by omega) with h1 | h2
  · have : Fact p.Prime := ⟨h.prime⟩
    have : NumberField (jacobiP ((a : ℚ) / u) ((b : ℚ) / v) n).SplittingField := ⟨⟩
    have := Int.ideal_span_isMaximal_of_prime p
    obtain ⟨P, hPmax, hPover⟩ :
        ∃ P : Ideal (𝓞 (jacobiP ((a : ℚ) / u) ((b : ℚ) / v) n).SplittingField),
          P.IsMaximal ∧ P.LiesOver (Ideal.span {(p : ℤ)}) :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral _
    refine ⟨P, hPmax, hPover, 1, Subgroup.one_mem _, Or.inl ⟨h1, map_one _⟩⟩
  · obtain ⟨P, hPmax, hPover, σ, hσ, hc, hcard⟩ := exists_isCycle_galPerm_jacobiP_mem_inertia h h2
    exact ⟨P, hPmax, hPover, σ, hσ, Or.inr ⟨h2, hc, hcard⟩⟩

end ArithmeticOfJacobiPolynomials
