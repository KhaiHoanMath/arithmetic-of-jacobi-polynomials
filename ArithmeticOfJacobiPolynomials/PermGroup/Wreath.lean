/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.Defs
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# The hyperoctahedral group `W_N = C_2 ≀ S_N` as `negCommPerm s`

Let `s` be a finite set of nonzero elements of a field `L` with `(2 : L) ≠ 0`, closed under
negation. Its elements come in opposite pairs `{x, -x}`, indexed by the squares
`squares s = {x ^ 2 | x ∈ s}`. The group `negCommPerm s` of permutations of `s` commuting
with negation is `W_N`, `N = Nat.card (squares s)`.

This file provides:

* `toSquare : s → squares s` and its fibres (`toSquare_eq_toSquare_iff`);
* `negPerm hneg`, negation as a permutation of `s`, and the characterisation
  `σ ∈ negCommPerm s ↔ Commute σ (negPerm hneg)`;
* the projection `pairPerm : negCommPerm s →* Equiv.Perm (squares s)` onto the permutation of
  pairs, with `pairPerm_apply_toSquare`, its surjectivity and its kernel;
* sign changes `signFlip hneg T` on a set `T` of pairs, their products, conjugates and the fact
  that every kernel element is a sign change;
* cardinalities: `Nat.card s = 2 * Nat.card (squares s)`, and the analogous count for
  negation-closed finsets such as supports.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Equiv Equiv.Perm

variable {L : Type*} [Field L] {s : Set L}

/-! ### Squares and pairs -/

/-- The set of squares of elements of `s`; for `s` closed under negation with `0 ∉ s` in
characteristic `≠ 2` it indexes the opposite pairs `{x, -x}` of `s`. -/
@[expose] def squares (s : Set L) : Set L := (fun x => x ^ 2) '' s

/-- The pair of `x ∈ s`, recorded by its square. -/
@[expose] def toSquare (x : s) : squares s := ⟨(x : L) ^ 2, x, x.2, rfl⟩

@[simp] theorem coe_toSquare (x : s) : ((toSquare x : squares s) : L) = (x : L) ^ 2 := rfl

theorem toSquare_surjective : Function.Surjective (toSquare (s := s)) := by
  rintro ⟨q, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem toSquare_eq_toSquare_iff {x y : s} :
    toSquare x = toSquare y ↔ (y : L) = x ∨ (y : L) = -x := by
  rw [Subtype.ext_iff, coe_toSquare, coe_toSquare, eq_comm, sq_eq_sq_iff_eq_or_eq_neg]

instance [Finite s] : Finite (squares s) := Finite.of_surjective _ toSquare_surjective

/-- In characteristic `≠ 2`, a nonzero element is different from its negative. -/
theorem coe_ne_neg_coe (h2 : (2 : L) ≠ 0) (h0 : (0 : L) ∉ s) (x : s) : (x : L) ≠ -(x : L) := by
  intro h
  have hx : (2 : L) * x = 0 := by linear_combination h
  rcases mul_eq_zero.1 hx with h' | h'
  · exact h2 h'
  · exact h0 (h' ▸ x.2)

/-! ### Negation as a permutation -/

/-- Negation, as a permutation of a set closed under negation. -/
@[expose] def negPerm (hneg : ∀ x ∈ s, -x ∈ s) : Perm s where
  toFun x := ⟨-x, hneg _ x.2⟩
  invFun x := ⟨-x, hneg _ x.2⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

section negPerm

variable (hneg : ∀ x ∈ s, -x ∈ s)

@[simp] theorem coe_negPerm_apply (x : s) : ((negPerm hneg x : s) : L) = -(x : L) := rfl

@[simp] theorem negPerm_negPerm (x : s) : negPerm hneg (negPerm hneg x) = x := by
  ext; simp

@[simp] theorem toSquare_negPerm (x : s) : toSquare (negPerm hneg x) = toSquare x := by
  ext; simp

theorem negPerm_ne_self (h2 : (2 : L) ≠ 0) (h0 : (0 : L) ∉ s) (x : s) : negPerm hneg x ≠ x :=
  fun h => coe_ne_neg_coe h2 h0 x (by rw [← coe_negPerm_apply hneg x, h])

theorem eq_or_eq_negPerm_of_toSquare_eq {x y : s} (h : toSquare x = toSquare y) :
    y = x ∨ y = negPerm hneg x := by
  rcases toSquare_eq_toSquare_iff.1 h with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem toSquare_eq_toSquare_iff' {x y : s} :
    toSquare x = toSquare y ↔ y = x ∨ y = negPerm hneg x := by
  refine ⟨eq_or_eq_negPerm_of_toSquare_eq hneg, ?_⟩
  rintro (rfl | rfl)
  · rfl
  · simp

end negPerm

/-! ### Membership in `negCommPerm s` -/

/-- A permutation in `negCommPerm s` maps opposite elements to opposite elements. -/
theorem negCommPerm_apply_eq_neg {σ : Perm s} (hσ : σ ∈ negCommPerm s) {x y : s}
    (h : (y : L) = -(x : L)) : ((σ y : s) : L) = -((σ x : s) : L) :=
  ((mem_negCommPerm_iff σ).1 hσ x y).1 h

theorem mem_negCommPerm_iff_commute (hneg : ∀ x ∈ s, -x ∈ s) {σ : Perm s} :
    σ ∈ negCommPerm s ↔ Commute σ (negPerm hneg) := by
  constructor
  · intro hσ
    refine Equiv.ext fun x => Subtype.ext ?_
    exact negCommPerm_apply_eq_neg hσ (coe_negPerm_apply hneg x)
  · intro hc
    have hc' : ∀ x, σ (negPerm hneg x) = negPerm hneg (σ x) := fun x => by
      simpa using congrArg (fun f : Perm s => f x) hc.eq
    rw [mem_negCommPerm_iff]
    intro x y
    constructor
    · intro h
      have hy : y = negPerm hneg x := Subtype.ext h
      rw [hy, hc', coe_negPerm_apply]
    · intro h
      have hy : σ y = σ (negPerm hneg x) := by
        rw [hc']; exact Subtype.ext (by rw [h, coe_negPerm_apply])
      rw [σ.injective hy, coe_negPerm_apply]

theorem negCommPerm_apply_negPerm (hneg : ∀ x ∈ s, -x ∈ s) {σ : Perm s}
    (hσ : σ ∈ negCommPerm s) (x : s) : σ (negPerm hneg x) = negPerm hneg (σ x) := by
  simpa using congrArg (fun f : Perm s => f x) ((mem_negCommPerm_iff_commute hneg).1 hσ).eq

/-- A permutation in `negCommPerm s` moving `x` also moves `-x`. -/
theorem negPerm_mem_support_of_mem_negCommPerm [Fintype s] [DecidableEq s]
    (hneg : ∀ x ∈ s, -x ∈ s) {σ : Perm s} (hσ : σ ∈ negCommPerm s) {x : s}
    (hx : x ∈ σ.support) : negPerm hneg x ∈ σ.support := by
  rw [mem_support] at hx ⊢
  rw [negCommPerm_apply_negPerm hneg hσ]
  exact fun h => hx ((negPerm hneg).injective h)

/-- Permutations in `negCommPerm s` respect pairs. -/
theorem toSquare_apply_eq_of_toSquare_eq {σ : Perm s} (hσ : σ ∈ negCommPerm s) {x y : s}
    (h : toSquare x = toSquare y) : toSquare (σ x) = toSquare (σ y) := by
  rw [toSquare_eq_toSquare_iff] at h ⊢
  rcases h with h | h
  · left; rw [Subtype.ext h]
  · exact Or.inr (negCommPerm_apply_eq_neg hσ h)

/-! ### The projection onto permutations of pairs -/

/-- The action of `negCommPerm s` on pairs: `σ • x ^ 2 = (σ x) ^ 2`. -/
noncomputable def pairSMul (σ : negCommPerm s) (q : squares s) : squares s :=
  toSquare ((σ : Perm s) (toSquare_surjective q).choose)

theorem pairSMul_toSquare (σ : negCommPerm s) (x : s) :
    pairSMul σ (toSquare x) = toSquare ((σ : Perm s) x) :=
  toSquare_apply_eq_of_toSquare_eq σ.2 (toSquare_surjective (toSquare x)).choose_spec

/-- The action of `negCommPerm s` on the set of pairs `squares s`. -/
@[reducible] noncomputable def pairAction : MulAction (negCommPerm s) (squares s) where
  smul := pairSMul
  one_smul q := by
    obtain ⟨x, rfl⟩ := toSquare_surjective q
    exact pairSMul_toSquare 1 x
  mul_smul σ τ q := by
    obtain ⟨x, rfl⟩ := toSquare_surjective q
    change pairSMul (σ * τ) (toSquare x) = pairSMul σ (pairSMul τ (toSquare x))
    rw [pairSMul_toSquare, pairSMul_toSquare, pairSMul_toSquare]
    rfl

/-- The projection `W_N → S_N`: a permutation commuting with negation induces a permutation
of the pairs, `x ^ 2 ↦ (σ x) ^ 2`. -/
noncomputable def pairPerm : negCommPerm s →* Perm (squares s) :=
  @MulAction.toPermHom _ _ _ pairAction

@[simp] theorem pairPerm_apply_toSquare (σ : negCommPerm s) (x : s) :
    pairPerm σ (toSquare x) = toSquare ((σ : Perm s) x) :=
  pairSMul_toSquare σ x

theorem zpow_pairPerm_apply_toSquare (σ : negCommPerm s) (i : ℤ) (x : s) :
    (pairPerm σ ^ i) (toSquare x) = toSquare (((σ : Perm s) ^ i) x) := by
  rw [← map_zpow, pairPerm_apply_toSquare, Subgroup.coe_zpow]

theorem mem_ker_pairPerm_iff {σ : negCommPerm s} :
    σ ∈ pairPerm.ker ↔ ∀ x : s, toSquare ((σ : Perm s) x) = toSquare x := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h x
    rw [← pairPerm_apply_toSquare, h, Perm.one_apply]
  · intro h
    ext q
    obtain ⟨x, rfl⟩ := toSquare_surjective q
    rw [pairPerm_apply_toSquare, h, Perm.one_apply]

/-- The projection `W_N → S_N` is surjective: every permutation of the pairs lifts. -/
theorem pairPerm_surjective (h2 : (2 : L) ≠ 0) (h0 : (0 : L) ∉ s) (hneg : ∀ x ∈ s, -x ∈ s) :
    Function.Surjective (pairPerm (s := s)) := by
  classical
  intro π
  set r : squares s → s := fun q => (toSquare_surjective q).choose with hr_def
  have hr : ∀ q, toSquare (r q) = q := fun q => (toSquare_surjective q).choose_spec
  set f : Perm (squares s) → s → s := fun π x =>
    if x = r (toSquare x) then r (π (toSquare x)) else negPerm hneg (r (π (toSquare x)))
    with hf_def
  have hx_cases : ∀ x : s, x = r (toSquare x) ∨ x = negPerm hneg (r (toSquare x)) := by
    intro x
    exact (eq_or_eq_negPerm_of_toSquare_eq hneg (hr (toSquare x))).imp id id
  have hf_sq : ∀ π x, toSquare (f π x) = π (toSquare x) := by
    intro π x
    simp only [hf_def]
    split_ifs <;> simp [hr]
  have hf_inv : ∀ π : Perm (squares s), ∀ x, f π⁻¹ (f π x) = x := by
    intro π x
    have hsq := hf_sq π x
    simp only [hf_def] at hsq ⊢
    by_cases hx : x = r (toSquare x)
    · rw [ite_eq_left hx] at hsq ⊢
      rw [hsq, ite_eq_left rfl]
      simpa using hx.symm
    · rw [ite_eq_right hx] at hsq ⊢
      rw [hsq, ite_eq_right (negPerm_ne_self hneg h2 h0 _)]
      simpa using ((hx_cases x).resolve_left hx).symm
  let e : Perm s := ⟨f π, f π⁻¹, hf_inv π, fun x => by simpa using hf_inv π⁻¹ x⟩
  have he : e ∈ negCommPerm s := by
    rw [mem_negCommPerm_iff_commute hneg]
    refine Equiv.ext fun x => ?_
    change f π (negPerm hneg x) = negPerm hneg (f π x)
    simp only [hf_def, toSquare_negPerm]
    by_cases hx : x = r (toSquare x)
    · rw [ite_eq_right, ite_eq_left hx]
      intro h
      exact negPerm_ne_self hneg h2 h0 x (h.trans hx.symm)
    · have hx' := (hx_cases x).resolve_left hx
      rw [ite_eq_right hx, negPerm_negPerm, ite_eq_left]
      rw [hx', negPerm_negPerm, toSquare_negPerm, hr]
  refine ⟨⟨e, he⟩, ?_⟩
  ext q
  obtain ⟨x, rfl⟩ := toSquare_surjective q
  rw [pairPerm_apply_toSquare]
  exact congrArg Subtype.val (hf_sq π x)

/-! ### Sign changes -/

open Classical in
/-- The sign change `x ↦ -x` on the pairs in `T`, fixing the other pairs. -/
noncomputable def signFlip (hneg : ∀ x ∈ s, -x ∈ s) (T : Set (squares s)) : Perm s :=
  Function.Involutive.toPerm (fun x => if toSquare x ∈ T then negPerm hneg x else x) (by
    intro x
    by_cases hx : toSquare x ∈ T
    · simp [hx]
    · simp [hx])

section signFlip

variable (hneg : ∀ x ∈ s, -x ∈ s)

theorem signFlip_apply_of_mem {T : Set (squares s)} {x : s} (hx : toSquare x ∈ T) :
    signFlip hneg T x = negPerm hneg x := by
  classical
  exact ite_eq_left hx

theorem signFlip_apply_of_notMem {T : Set (squares s)} {x : s} (hx : toSquare x ∉ T) :
    signFlip hneg T x = x := by
  classical
  exact ite_eq_right hx

theorem toSquare_signFlip_apply (T : Set (squares s)) (x : s) :
    toSquare (signFlip hneg T x) = toSquare x := by
  by_cases hx : toSquare x ∈ T
  · rw [signFlip_apply_of_mem hneg hx, toSquare_negPerm]
  · rw [signFlip_apply_of_notMem hneg hx]

theorem signFlip_mem_negCommPerm (T : Set (squares s)) : signFlip hneg T ∈ negCommPerm s := by
  rw [mem_negCommPerm_iff_commute hneg]
  refine Equiv.ext fun x => ?_
  change signFlip hneg T (negPerm hneg x) = negPerm hneg (signFlip hneg T x)
  by_cases hx : toSquare x ∈ T
  · rw [signFlip_apply_of_mem hneg (by rwa [toSquare_negPerm]), signFlip_apply_of_mem hneg hx]
  · rw [signFlip_apply_of_notMem hneg (by rwa [toSquare_negPerm]),
      signFlip_apply_of_notMem hneg hx]

theorem signFlip_mem_ker (T : Set (squares s)) :
    (⟨signFlip hneg T, signFlip_mem_negCommPerm hneg T⟩ : negCommPerm s) ∈ pairPerm.ker :=
  mem_ker_pairPerm_iff.2 (toSquare_signFlip_apply hneg T)

@[simp] theorem signFlip_empty : signFlip hneg (∅ : Set (squares s)) = 1 := by
  ext x
  rw [signFlip_apply_of_notMem hneg (Set.notMem_empty _), Perm.one_apply]

theorem signFlip_mul (T U : Set (squares s)) :
    signFlip hneg T * signFlip hneg U = signFlip hneg (symmDiff T U) := by
  ext x
  rw [Perm.mul_apply]
  have hn : toSquare (negPerm hneg x) = toSquare x := toSquare_negPerm hneg x
  by_cases hxT : toSquare x ∈ T <;> by_cases hxU : toSquare x ∈ U
  · have h : toSquare x ∉ symmDiff T U := by simp [Set.mem_symmDiff, hxT, hxU]
    rw [signFlip_apply_of_mem hneg hxU, signFlip_apply_of_mem hneg (hn ▸ hxT),
      signFlip_apply_of_notMem hneg h, negPerm_negPerm]
  · have h : toSquare x ∈ symmDiff T U := by simp [Set.mem_symmDiff, hxT, hxU]
    rw [signFlip_apply_of_notMem hneg hxU, signFlip_apply_of_mem hneg hxT,
      signFlip_apply_of_mem hneg h]
  · have h : toSquare x ∈ symmDiff T U := by simp [Set.mem_symmDiff, hxT, hxU]
    rw [signFlip_apply_of_mem hneg hxU, signFlip_apply_of_notMem hneg (hn ▸ hxT),
      signFlip_apply_of_mem hneg h]
  · have h : toSquare x ∉ symmDiff T U := by simp [Set.mem_symmDiff, hxT, hxU]
    rw [signFlip_apply_of_notMem hneg hxU, signFlip_apply_of_notMem hneg hxT,
      signFlip_apply_of_notMem hneg h]

/-- Conjugating a sign change by `σ ∈ W_N` moves its set of pairs by the projection of `σ`. -/
theorem conj_signFlip (σ : negCommPerm s) (T : Set (squares s)) :
    (σ : Perm s) * signFlip hneg T * (σ : Perm s)⁻¹ = signFlip hneg (pairPerm σ '' T) := by
  have key : ∀ y : s,
      signFlip hneg (pairPerm σ '' T) ((σ : Perm s) y) = (σ : Perm s) (signFlip hneg T y) := by
    intro y
    have hiff : toSquare ((σ : Perm s) y) ∈ pairPerm σ '' T ↔ toSquare y ∈ T := by
      rw [← pairPerm_apply_toSquare]
      exact (pairPerm σ).injective.mem_set_image
    by_cases hy : toSquare y ∈ T
    · rw [signFlip_apply_of_mem hneg (hiff.2 hy), signFlip_apply_of_mem hneg hy,
        negCommPerm_apply_negPerm hneg σ.2]
    · rw [signFlip_apply_of_notMem hneg (fun h => hy (hiff.1 h)),
        signFlip_apply_of_notMem hneg hy]
  refine Equiv.ext fun x => ?_
  obtain ⟨y, rfl⟩ := (σ : Perm s).surjective x
  rw [Perm.mul_apply, Perm.mul_apply, key]
  simp

/-- Every element of the kernel of the projection is a sign change. -/
theorem eq_signFlip_of_mem_ker (h2 : (2 : L) ≠ 0) (h0 : (0 : L) ∉ s) {k : negCommPerm s}
    (hk : k ∈ pairPerm.ker) :
    (k : Perm s) = signFlip hneg (toSquare '' {x | (k : Perm s) x ≠ x}) := by
  rw [mem_ker_pairPerm_iff] at hk
  ext x
  rcases eq_or_eq_negPerm_of_toSquare_eq hneg (hk x).symm with h | h
  · rw [signFlip_apply_of_notMem hneg, h]
    rintro ⟨y, hy, hyx⟩
    rcases eq_or_eq_negPerm_of_toSquare_eq hneg hyx.symm with rfl | rfl
    · exact hy h
    · exact hy (by rw [negCommPerm_apply_negPerm hneg k.2, h])
  · have hx : toSquare x ∈ toSquare '' {x | (k : Perm s) x ≠ x} := by
      refine ⟨x, ?_, rfl⟩
      rw [Set.mem_ofPred_eq, h]
      exact negPerm_ne_self hneg h2 h0 x
    rw [signFlip_apply_of_mem hneg hx, h]

end signFlip

/-! ### Counting -/

/-- A negation-closed finset of `s` has twice as many elements as it has pairs. -/
theorem card_eq_two_mul_card_image_toSquare [DecidableEq (squares s)] (h2 : (2 : L) ≠ 0)
    (h0 : (0 : L) ∉ s) (hneg : ∀ x ∈ s, -x ∈ s) (S : Finset s)
    (hS : ∀ x ∈ S, negPerm hneg x ∈ S) : S.card = 2 * (S.image toSquare).card := by
  classical
  rw [Finset.card_eq_sum_card_image toSquare S, Finset.sum_const_nat (m := 2), mul_comm]
  intro q hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hq
  rw [Finset.card_eq_two]
  refine ⟨x, negPerm hneg x, (negPerm_ne_self hneg h2 h0 x).symm, ?_⟩
  ext y
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hy⟩
    exact eq_or_eq_negPerm_of_toSquare_eq hneg hy.symm
  · rintro (rfl | rfl)
    · exact ⟨hx, rfl⟩
    · exact ⟨hS _ hx, toSquare_negPerm hneg _⟩

/-- `s` has twice as many elements as it has opposite pairs: `#s = 2 N`. -/
theorem nat_card_eq_two_mul_nat_card_squares [Finite s] (h2 : (2 : L) ≠ 0) (h0 : (0 : L) ∉ s)
    (hneg : ∀ x ∈ s, -x ∈ s) : Nat.card s = 2 * Nat.card (squares s) := by
  classical
  have : Fintype s := Fintype.ofFinite s
  have : Fintype (squares s) := Fintype.ofFinite _
  have h := card_eq_two_mul_card_image_toSquare h2 h0 hneg Finset.univ (fun _ _ => by simp)
  rw [Finset.image_univ_of_surjective toSquare_surjective, Finset.card_univ,
    Finset.card_univ] at h
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, h]

end ArithmeticOfJacobiPolynomials
