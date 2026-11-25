/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.GaloisBridge
public import ArithmeticOfJacobiPolynomials.PermGroup.Wreath

/-!
# Transitive Galois groups and irreducibility

A separable polynomial whose Galois group acts transitively on its roots is irreducible, and the
group `W_N` of permutations commuting with negation acts transitively on `2N` nonzero elements
closed under negation. Together these give the irreducibility of `L_{2n+δ}` once its Galois
group is known to be `W_n` (the equivalence in Theorem 5.9).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- A separable polynomial of positive degree whose Galois group acts transitively on its roots
is irreducible. -/
theorem irreducible_of_isPretransitive {F : Type*} [Field F] {f : F[X]} (hsep : f.Separable)
    (hdeg : 0 < f.natDegree)
    (htrans : MulAction.IsPretransitive (galPerm f).range (f.rootSet f.SplittingField)) :
    Irreducible f := by
  classical
  set E := f.SplittingField
  have hf0 : f ≠ 0 := fun h => by rw [h, natDegree_zero] at hdeg; exact lt_irrefl _ hdeg
  have hcard : Fintype.card (f.rootSet E) = f.natDegree :=
    card_rootSet_eq_natDegree hsep (SplittingField.splits f)
  obtain ⟨x⟩ : Nonempty (f.rootSet E) := Fintype.card_pos_iff.mp (by omega)
  have hxint : IsIntegral F (x : E) := Algebra.IsIntegral.isIntegral _
  set m := minpoly F (x : E)
  have hmf : m ∣ f := minpoly.dvd F _ (mem_rootSet.mp x.2).2
  have hm0 : m ≠ 0 := minpoly.ne_zero hxint
  -- every root of `f` is a conjugate of `x`, hence a root of `m`
  have hsub : f.rootSet E ⊆ m.rootSet E := by
    intro y hy
    obtain ⟨γ, hγ⟩ := htrans.exists_smul_eq x ⟨y, hy⟩
    obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp γ.2
    have hγy : ((γ : Equiv.Perm (f.rootSet E)) x : E) = y := congrArg Subtype.val hγ
    rw [← hσ, galPerm_apply] at hγy
    rw [mem_rootSet]
    refine ⟨hm0, ?_⟩
    rw [← hγy]
    change aeval (σ (x : E)) m = 0
    rw [aeval_algHom_apply (σ : E ≃ₐ[F] E), minpoly.aeval, map_zero]
  have hle : f.natDegree ≤ m.natDegree := by
    have h1 : (f.rootSet E).ncard ≤ (m.rootSet E).ncard := Set.ncard_le_ncard hsub
    have h2 : (f.rootSet E).ncard = f.natDegree := by
      rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, hcard]
    have h3 : (m.rootSet E).ncard ≤ m.natDegree := by
      rw [rootSet_def, Set.ncard_coe_finset]
      exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans natDegree_map_le)
    omega
  obtain ⟨q, hq⟩ := hmf
  have hq0 : q ≠ 0 := fun h => hf0 (by rw [hq, h, mul_zero])
  have hqdeg : q.natDegree = 0 := by
    have := congrArg natDegree hq
    rw [natDegree_mul hm0 hq0] at this
    omega
  rw [hq, eq_C_of_natDegree_eq_zero hqdeg, irreducible_mul_isUnit
    (isUnit_C.mpr (Ne.isUnit (fun h => hq0 (by rw [eq_C_of_natDegree_eq_zero hqdeg, h, C_0]))))]
  exact minpoly.irreducible hxint

/-- `W_N` acts transitively on `2N` nonzero elements closed under negation. -/
theorem isPretransitive_negCommPerm {L : Type*} [Field L] {s : Set L} (h2 : (2 : L) ≠ 0)
    (h0 : (0 : L) ∉ s) (hneg : ∀ x ∈ s, -x ∈ s) :
    MulAction.IsPretransitive (negCommPerm s) s := by
  classical
  refine ⟨fun x y => ?_⟩
  obtain ⟨γ, hγ⟩ := pairPerm_surjective h2 h0 hneg (Equiv.swap (toSquare x) (toSquare y))
  have hγx : toSquare ((γ : Equiv.Perm s) x) = toSquare y := by
    rw [← pairPerm_apply_toSquare, hγ, Equiv.swap_apply_left]
  rcases eq_or_eq_negPerm_of_toSquare_eq hneg hγx with h | h
  · exact ⟨γ, h.symm⟩
  · refine ⟨⟨signFlip hneg {toSquare y}, signFlip_mem_negCommPerm hneg _⟩ * γ, ?_⟩
    change signFlip hneg {toSquare y} ((γ : Equiv.Perm s) x) = y
    have hmem : toSquare ((γ : Equiv.Perm s) x) ∈ ({toSquare y} : Set (squares s)) := hγx
    rw [signFlip_apply_of_mem hneg hmem]
    exact h.symm

end ArithmeticOfJacobiPolynomials
