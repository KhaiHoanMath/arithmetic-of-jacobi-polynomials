/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.FixedRationalParameters
public import ArithmeticOfJacobiPolynomials.Galois.SquaresBridge
public import ArithmeticOfJacobiPolynomials.Galois.Transitivity
public import ArithmeticOfJacobiPolynomials.PermGroup.SignKernel

/-!
# Theorem 1.6: the quadratic substitution (Section 5.4)

For `c ∈ ℚ^×` and the dominant factor `h_n` of `f_n = P_n^{(α,β)} = κ_n h_n g_n` (Theorem 1.6,
Theorem 1.6), the polynomial `h_n(1 + cX²)` is irreducible with Galois group `W_{M_n}`, and
restriction `Gal(h_n(1+cX²) g_n(1+cX²)/ℚ) → Gal(h_n(1+cX²)/ℚ) × Gal(g_n(1+cX²)/ℚ)` is
bijective, for all large `n` (`quadratic_isDominant_jacobiP`, stated with the dominant-factor and
denominator conditions unfolded).

The proof follows the manuscript: the quadratic part of Proposition 5.2 gives single
`2d_p`-cycles on the roots of `f_n(1 + cX²)` for the primes (5.20); their supports lie above the
large orbit, i.e. on the roots of `h_n(1 + cX²)` (`aeval_eq_zero_of_isCycle_comp`); a cycle with
`d_p` odd and the squares bridge give `W_M` by Lemma 5.5 (`galoisGroupIsWreath_comp`); cycles
with `d_p` of both parities and Lemma 5.6 (2) give the product
(`restrictProd_bijective_of_wreath`).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Filter

namespace FixedRationalParameters

/-! ### Values at `1` -/

theorem ascPochhammer_eval_add_one_ne_zero {α : ℚ} (hα : ∀ k : ℕ, α ≠ -((k : ℚ) + 1))
    (n : ℕ) : (ascPochhammer ℚ n).eval (α + 1) ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval]
    refine mul_ne_zero ih fun h => hα n ?_
    linarith

/-- `binom(n + α, n) ≠ 0` unless `α` is a negative integer. -/
theorem ring_choose_add_ne_zero {α : ℚ} (hα : ∀ k : ℕ, α ≠ -((k : ℚ) + 1)) (n : ℕ) :
    Ring.choose ((n : ℚ) + α) n ≠ 0 := by
  intro h
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose ((n : ℚ) + α) n
  rw [h, smul_zero, descPochhammer_smeval_eq_ascPochhammer, ascPochhammer_smeval_eq_eval] at h1
  apply ascPochhammer_eval_add_one_ne_zero hα n
  rw [show α + 1 = (n : ℚ) + α - n + 1 by ring]
  exact h1

/-- `h_n(1) ≠ 0`: `P_n^{(α,β)}(1) = binom(n + α, n) ≠ 0`. -/
theorem eval_one_ne_zero_of_dvd {α β : ℚ} (hα : ∀ k : ℕ, α ≠ -((k : ℚ) + 1)) {n : ℕ}
    {h : ℚ[X]} (hdvd : h ∣ jacobiP α β n) : h.eval 1 ≠ 0 := by
  intro h0
  obtain ⟨k, hk⟩ := hdvd
  have := congrArg (eval 1) hk
  rw [jacobiP_eval_one, eval_mul, h0, zero_mul] at this
  exact ring_choose_add_ne_zero hα n this

/-- `v_p(c) = 0` for primes `p` exceeding the numerator and denominator of `c ≠ 0`. -/
theorem padicValRat_eq_zero_of_lt {p : ℕ} (hp : p.Prime) {c : ℚ} (hc : c ≠ 0)
    (h1 : c.num.natAbs < p) (h2 : c.den < p) : padicValRat p c = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [padicValRat_def]
  have hnum : padicValInt p c.num = 0 := by
    rw [show padicValInt p c.num = padicValNat p c.num.natAbs from (rfl)]
    refine padicValNat.eq_zero_of_not_dvd fun hd => ?_
    have := Nat.le_of_dvd (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hc)) hd
    omega
  have hden : padicValNat p c.den = 0 := by
    refine padicValNat.eq_zero_of_not_dvd fun hd => ?_
    have := Nat.le_of_dvd c.den_pos hd
    omega
  rw [hnum, hden]
  simp

/-! ### Roots after the substitution `x ↦ 1 + cx²` -/

theorem aeval_comp_quad {A : Type*} [CommRing A] [Algebra ℚ A] (f : ℚ[X]) (c : ℚ) (x : A) :
    aeval x (f.comp (1 + C c * polyX ^ 2)) = aeval (1 + algebraMap ℚ A c * x ^ 2) f := by
  rw [aeval_comp]
  simp

open Classical in
/-- **The support above the large orbit.** Let `h` be the dominant factor of `f`, `deg f ≤ n`,
and let `σ ∈ Gal(f(1 + cX²))` act as a single cycle with more than `n` moved roots. Then every
moved root is a root of `h(1 + cX²)`: the values `1 + cz²` on the support form at least half as
many conjugates of a root of `f`, whose minimal polynomial is therefore dominant. -/
theorem aeval_eq_zero_of_isCycle_comp {f h F : ℚ[X]} {n : ℕ} {c : ℚ} (hc : c ≠ 0)
    (hFdef : F = f.comp (1 + C c * polyX ^ 2)) (hdeg : f.natDegree ≤ n) (hh : IsDominant f h)
    {σ : F.Gal} (hσ : (galPerm F σ).IsCycle) (hcard : n < (galPerm F σ).support.card) :
    ∀ z ∈ (galPerm F σ).support,
      aeval (z : F.SplittingField) (h.comp (1 + C c * polyX ^ 2)) = 0 := by
  have hF0 : F ≠ 0 := ne_zero_of_isCycle hσ
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hF0 (by rw [hFdef, zero_comp])
  obtain ⟨z₀, -, hall⟩ := hσ
  let φ : F.SplittingField → F.SplittingField := fun x =>
    1 + algebraMap ℚ F.SplittingField c * x ^ 2
  have hφ : ∀ x, φ x = 1 + algebraMap ℚ F.SplittingField c * x ^ 2 := fun _ => rfl
  have hroot₀ : aeval (φ z₀) f = 0 := by
    have h1 := congrArg (aeval (z₀ : F.SplittingField)) hFdef
    rw [aeval_comp_quad] at h1
    rw [hφ, ← h1]
    exact (mem_rootSet.mp z₀.2).2
  have hint : IsIntegral ℚ (φ z₀) := Algebra.IsIntegral.isIntegral _
  have hφτ : ∀ τ : F.Gal, ∀ x : F.SplittingField, τ (φ x) = φ (τ x) := by
    intro τ x
    have hτc : τ (algebraMap ℚ F.SplittingField c) = algebraMap ℚ F.SplittingField c :=
      AlgEquiv.commutes (τ : F.SplittingField ≃ₐ[ℚ] F.SplittingField) c
    rw [hφ, hφ, map_add, map_one, map_mul, map_pow, hτc]
  have key : ∀ τ : F.Gal, aeval (φ (τ (z₀ : F.SplittingField))) (minpoly ℚ (φ z₀)) = 0 := by
    intro τ
    rw [← hφτ]
    have := aeval_algHom_apply (τ : F.SplittingField ≃ₐ[ℚ] F.SplittingField).toAlgHom (φ z₀)
      (minpoly ℚ (φ z₀))
    rw [minpoly.aeval, map_zero] at this
    exact this
  have hroots : ∀ z ∈ (galPerm F σ).support, aeval (φ z) (minpoly ℚ (φ z₀)) = 0 := by
    intro z hz
    obtain ⟨i, hi⟩ := hall (Equiv.Perm.mem_support.mp hz)
    have e : (((galPerm F σ ^ i) z₀ : F.rootSet F.SplittingField) : F.SplittingField) =
        (σ ^ i) (z₀ : F.SplittingField) := by
      rw [← map_zpow, galPerm_apply]
      rfl
    rw [← hi, e]
    exact key (σ ^ i)
  have hm0 : minpoly ℚ (φ z₀) ≠ 0 := minpoly.ne_zero hint
  have hTroots : ((galPerm F σ).support.image
      (fun z : F.rootSet F.SplittingField => φ (z : F.SplittingField))).val ⊆
      ((minpoly ℚ (φ z₀)).map (algebraMap ℚ F.SplittingField)).roots := by
    intro x hx
    rw [Finset.mem_val, Finset.mem_image] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [mem_roots_map hm0, ← aeval_def]
    exact hroots z hz
  have hTm := card_le_degree_of_subset_roots hTroots
  rw [natDegree_map] at hTm
  have hc' : algebraMap ℚ F.SplittingField c ≠ 0 := (_root_.map_ne_zero _).mpr hc
  have hfib : (galPerm F σ).support.card ≤ 2 * ((galPerm F σ).support.image
      (fun z : F.rootSet F.SplittingField => φ (z : F.SplittingField))).card := by
    refine Finset.card_le_mul_card_image
      (f := fun z : F.rootSet F.SplittingField => φ (z : F.SplittingField)) _ 2
      (fun b hb => ?_)
    obtain ⟨z₁, -, rfl⟩ := Finset.mem_image.mp hb
    refine (Finset.card_le_card_of_injOn
      (t := ({(z₁ : F.SplittingField), -(z₁ : F.SplittingField)} : Finset F.SplittingField))
      (fun z : F.rootSet F.SplittingField => (z : F.SplittingField)) ?_ ?_).trans
      Finset.card_le_two
    · intro z hz
      rw [Finset.mem_coe, Finset.mem_filter] at hz
      have h3 : 1 + algebraMap ℚ F.SplittingField c * (z : F.SplittingField) ^ 2 =
          1 + algebraMap ℚ F.SplittingField c * (z₁ : F.SplittingField) ^ 2 := hz.2
      have h2 : (z : F.SplittingField) ^ 2 = (z₁ : F.SplittingField) ^ 2 :=
        mul_left_cancel₀ hc' (add_left_cancel h3)
      change (z : F.SplittingField) ∈ (({(z₁ : F.SplittingField), -(z₁ : F.SplittingField)} :
        Finset F.SplittingField) : Set F.SplittingField)
      rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
      exact sq_eq_sq_iff_eq_or_eq_neg.mp h2
    · intro a _ b _ hab
      exact Subtype.ext hab
  have hmd : IsDominant f (minpoly ℚ (φ z₀)) :=
    (isDominant_iff _ _).mpr ⟨minpoly.monic hint, minpoly.irreducible hint,
      minpoly.dvd ℚ _ hroot₀, by omega⟩
  have hhm := eq_of_isDominant hf0 hh hmd
  intro z hz
  rw [aeval_comp_quad, hhm]
  exact hroots z hz

open Classical in
/-- **Restriction to a pair of factors.** Let `F = κ H G ≠ 0` with `H` and `G` without common
roots, and let `σ ∈ Gal(F)` act as a single cycle whose moved roots are roots of `H`. Then some
`ρ ∈ Gal(HG)` restricts to a cycle of the same length on the roots of `H` and trivially to `G`. -/
theorem exists_restrictProd_isCycle_of_noCommonRoot {F H G : ℚ[X]} {κ : ℚ} (hf : F ≠ 0)
    (hfac : F = C κ * H * G) {σ : F.Gal} (hσ : (galPerm F σ).IsCycle)
    (hsupp : ∀ z ∈ (galPerm F σ).support, aeval (z : F.SplittingField) H = 0)
    (hcop : ∀ y : (H * G).SplittingField, aeval y H = 0 → aeval y G = 0 → False) :
    ∃ ρ : (H * G).Gal, (galPerm H (Gal.restrictProd H G ρ).1).IsCycle ∧
      (galPerm H (Gal.restrictProd H G ρ).1).support.card = (galPerm F σ).support.card ∧
      (Gal.restrictProd H G ρ).2 = 1 := by
  have hP : H * G ∣ F := ⟨C κ, by rw [hfac]; ring⟩
  have hP0 : H * G ≠ 0 := ne_zero_of_dvd_ne_zero hf hP
  have := fact_splits_of_dvd hf hP
  obtain ⟨c1, c2, c3⟩ := galPerm_restrict_isCycle hf hP hσ (fun z hz => by
    rw [aeval_mul, hsupp z hz, zero_mul])
  have hsh := c3 H hsupp
  set ρ := Gal.restrict (H * G) F.SplittingField σ with hρ
  have := fact_splits_of_dvd hP0 (dvd_mul_right H G)
  have := fact_splits_of_dvd hP0 (dvd_mul_left G H)
  obtain ⟨d1, d2, -⟩ := galPerm_restrict_isCycle hP0 (dvd_mul_right H G) c1 hsh
  have hg1 : Gal.restrict G (H * G).SplittingField ρ = 1 := by
    apply restrict_eq_one_of_forall_fixed
    intro y
    by_contra hne
    have hyP : (y : (H * G).SplittingField) ∈ (H * G).rootSet (H * G).SplittingField := by
      have hy := y.2
      rw [mem_rootSet] at hy ⊢
      exact ⟨hP0, by rw [aeval_mul, hy.2, mul_zero]⟩
    have hmem : (⟨y, hyP⟩ : (H * G).rootSet (H * G).SplittingField) ∈
        (galPerm (H * G) ρ).support := by
      rw [Equiv.Perm.mem_support]
      intro heq
      apply hne
      have := congrArg Subtype.val heq
      rw [galPerm_apply] at this
      exact this
    exact hcop _ (hsh _ hmem) (mem_rootSet.mp y.2).2
  have e1 : (Gal.restrictProd H G ρ).1 = Gal.restrict H (H * G).SplittingField ρ := by
    simp only [Gal.restrictProd, Gal.restrictDvd_def, hP0, ↓reduceDIte]
    rfl
  have e2 : (Gal.restrictProd H G ρ).2 = Gal.restrict G (H * G).SplittingField ρ := by
    simp only [Gal.restrictProd, Gal.restrictDvd_def, hP0, ↓reduceDIte]
    rfl
  refine ⟨ρ, ?_, ?_, ?_⟩
  · rw [e1]; exact d1
  · rw [e1, d2, c2]
  · rw [e2, hg1]

/-! ### The wreath product -/

/-- `J = h(1 - cX)` satisfies `J(-X²) = h(1 + cX²)`. -/
theorem comp_neg_X_sq_eq (h : ℚ[X]) (c : ℚ) :
    (C 1 * h.comp (C (-c) * polyX + C 1)).comp (-polyX ^ 2) = C 1 * h.comp (1 + C c * polyX ^ 2)
      := by
  rw [mul_comp, C_comp, comp_assoc]
  congr 2
  simp only [add_comp, mul_comp, C_comp, X_comp]
  simp only [C_neg, C_1]
  ring

/-- `h(1 - cX)` is irreducible with `h`. -/
theorem irreducible_comp_affine {h : ℚ[X]} (hirr : Irreducible h) {c : ℚ} (hc : c ≠ 0) :
    Irreducible (C 1 * h.comp (C (-c) * polyX + C 1)) := by
  have hb : -c ≠ 0 := neg_ne_zero.mpr hc
  have h1 := affine_comp_affine_inv (b := -c) (c := 1) hb
  have h2 := affine_inv_comp_affine (b := -c) (c := 1) hb
  have e : (algEquivOfCompEqX _ _ h1 h2) h = h.comp (C (-c) * polyX + C 1) := by
    rw [comp_eq_aeval]
    rfl
  rw [show C (1 : ℚ) * h.comp (C (-c) * polyX + C 1) = h.comp (C (-c) * polyX + C 1) by
    rw [C_1, one_mul], ← e]
  exact hirr.map _

open Classical in
/-- **`Gal(h(1+cX²)/ℚ) = W_M`** (proof of Theorem 1.6, quadratic substitution). If `h` is
irreducible with `Gal(h/ℚ) = S_M` and `h(1) ≠ 0`, and `Gal(h(1+cX²)/ℚ)` contains a single
`2d`-cycle with `d` odd and `d < M`, then `h(1+cX²)` is irreducible with group `W_M`
(squares bridge and Lemma 5.5). -/
theorem galoisGroupIsWreath_comp {h H : ℚ[X]} (hirr : Irreducible h)
    (hS : GaloisGroupIsSymmetric h) {c : ℚ} (hc : c ≠ 0) (hHdef : H = h.comp (1 + C c * polyX ^ 2))
    (h1 : h.eval 1 ≠ 0) {τ : H.Gal} (hτ : (galPerm H τ).IsCycle) {d : ℕ}
    (hd : (galPerm H τ).support.card = 2 * d) (hodd : Odd d) (hdM : d < h.natDegree) :
    GaloisGroupIsWreath H ∧ Irreducible H ∧ (0 : H.SplittingField) ∉ H.rootSet H.SplittingField ∧
      (∀ x ∈ H.rootSet H.SplittingField, -x ∈ H.rootSet H.SplittingField) ∧
      Nat.card (squares (H.rootSet H.SplittingField)) = h.natDegree := by
  set J := C 1 * h.comp (C (-c) * polyX + C 1) with hJdef
  have hk : (1 : ℚ) ≠ 0 := one_ne_zero
  have hJL : J.comp (-polyX ^ 2) = C 1 * H := by rw [hHdef]; exact comp_neg_X_sq_eq h c
  have hJirr : Irreducible J := irreducible_comp_affine hirr hc
  have hJsep : J.Separable := hJirr.separable
  have hJ0 : J.coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero, hJdef, eval_mul, eval_C, one_mul, eval_comp]
    simpa using h1
  have hsym : GaloisGroupIsSymmetric J :=
    GaloisGroupIsSymmetric.affine h 1 one_ne_zero (neg_ne_zero.mpr hc) hS
  have hproj := map_pairPerm_range_galPerm_eq_top hk hJL hJsep hJ0 hsym
  have hΓ := range_galPerm_le_negCommPerm H
  have h0 := zero_not_mem_rootSet_of_comp_neg_X_sq hk hJL hJ0
  have hneg : ∀ x ∈ H.rootSet H.SplittingField, -x ∈ H.rootSet H.SplittingField :=
    fun x hx => neg_mem_rootSet_of_comp_neg_X_sq hk hJL hx
  have hJdeg : J.natDegree = h.natDegree := by
    rw [hJdef, natDegree_C_mul hk, natDegree_comp, natDegree_linear (neg_ne_zero.mpr hc),
      mul_one]
  have hN : Nat.card (squares (H.rootSet H.SplittingField)) = h.natDegree := by
    rw [nat_card_squares_of_comp_neg_X_sq hk hJL hJsep hJ0, hJdeg]
  have hW := eq_negCommPerm_of_isCycle_of_odd two_ne_zero h0 hneg hΓ hproj
    (MonoidHom.mem_range.mpr ⟨τ, rfl⟩) hτ hd hodd (by rw [hN]; exact hdM)
  have hHsep : H.Separable := separable_of_comp_neg_X_sq hk hJL hJsep hJ0
  have hHdeg : 0 < H.natDegree := by
    rw [natDegree_of_comp_neg_X_sq hk hJL, hJdeg]
    omega
  have htrans : MulAction.IsPretransitive (galPerm H).range (H.rootSet H.SplittingField) := by
    rw [hW]
    exact isPretransitive_negCommPerm two_ne_zero h0 hneg
  exact ⟨(galoisGroupIsWreath_iff H).mpr hW, irreducible_of_isPretransitive hHsep hHdeg htrans,
    h0, hneg, hN⟩

open Classical in
/-- **The product after quadratic substitution** (proof of Theorem 1.6). If `Gal(H/ℚ) = W_M`
on `2M` nonzero roots closed under negation and some `ρ₁, ρ₂ ∈ Gal(HG)` restrict trivially to
`G` and to single `2d₁`- and `2d₂`-cycles on the roots of `H`, `d₁` even, `d₂` odd,
`1 ≤ dᵢ < M`, then restriction `Gal(HG) → Gal(H) × Gal(G)` is bijective (Lemma 5.6 (2)). -/
theorem restrictProd_bijective_of_wreath {H G : ℚ[X]} (hP0 : H * G ≠ 0)
    (h0 : (0 : H.SplittingField) ∉ H.rootSet H.SplittingField)
    (hneg : ∀ x ∈ H.rootSet H.SplittingField, -x ∈ H.rootSet H.SplittingField)
    (hW : GaloisGroupIsWreath H) {ρ₁ ρ₂ : (H * G).Gal} {d₁ d₂ : ℕ}
    (hc₁ : (galPerm H (Gal.restrictProd H G ρ₁).1).IsCycle)
    (hd₁ : (galPerm H (Gal.restrictProd H G ρ₁).1).support.card = 2 * d₁)
    (hc₂ : (galPerm H (Gal.restrictProd H G ρ₂).1).IsCycle)
    (hd₂ : (galPerm H (Gal.restrictProd H G ρ₂).1).support.card = 2 * d₂)
    (heven : Even d₁) (hodd : Odd d₂) (hd₁pos : 1 ≤ d₁)
    (hd₁N : d₁ < Nat.card (squares (H.rootSet H.SplittingField)))
    (hd₂N : d₂ < Nat.card (squares (H.rootSet H.SplittingField)))
    (hρ₁ : (Gal.restrictProd H G ρ₁).2 = 1) (hρ₂ : (Gal.restrictProd H G ρ₂).2 = 1) :
    Function.Bijective (Gal.restrictProd H G) := by
  refine ⟨Gal.restrictProd_injective (p := H) (q := G), ?_⟩
  have hsurj1 : ∀ x : H.Gal, ∃ w, (Gal.restrictProd H G w).1 = x :=
    Gal.restrictDvd_surjective (dvd_mul_right H G) hP0
  have hsurj2 : ∀ y : G.Gal, ∃ w, (Gal.restrictProd H G w).2 = y :=
    Gal.restrictDvd_surjective (dvd_mul_left G H) hP0
  set N : Subgroup H.Gal := (Gal.restrictProd H G).range.comap (MonoidHom.inl H.Gal G.Gal)
    with hNdef
  have hmemN : ∀ x : H.Gal, x ∈ N ↔ ∃ v, Gal.restrictProd H G v = (x, 1) := by
    intro x
    rw [hNdef, Subgroup.mem_comap, MonoidHom.mem_range, MonoidHom.inl_apply]
  have hN : N.Normal := by
    refine ⟨fun x hx y => ?_⟩
    obtain ⟨w, hw⟩ := hsurj1 y
    obtain ⟨v, hv⟩ := (hmemN x).mp hx
    refine (hmemN _).mpr ⟨w * v * w⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, hv]
    ext
    · simp [hw]
    · simp
  have hWr := (galoisGroupIsWreath_iff H).mp hW
  have hle : N.map (galPerm H) ≤ negCommPerm (H.rootSet H.SplittingField) := by
    rw [← hWr]
    exact Subgroup.map_le_range _ _
  have hnorm : ((N.map (galPerm H)).subgroupOf
      (negCommPerm (H.rootSet H.SplittingField))).Normal := by
    refine ⟨fun a ha b => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp ha
    have hb : (b : Equiv.Perm (H.rootSet H.SplittingField)) ∈ (galPerm H).range := by
      rw [hWr]; exact b.2
    obtain ⟨w, hw⟩ := hb
    refine Subgroup.mem_map.mpr ⟨w * x * w⁻¹, hN.conj_mem x hx w, ?_⟩
    simp [map_mul, map_inv, hw, hxa]
  have hmem₁ : (Gal.restrictProd H G ρ₁).1 ∈ N := (hmemN _).mpr ⟨ρ₁, Prod.ext rfl hρ₁⟩
  have hmem₂ : (Gal.restrictProd H G ρ₂).1 ∈ N := (hmemN _).mpr ⟨ρ₂, Prod.ext rfl hρ₂⟩
  have htop := eq_negCommPerm_of_normal_of_isCycle two_ne_zero h0 hneg hle hnorm
    (Subgroup.mem_map_of_mem _ hmem₁) (Subgroup.mem_map_of_mem _ hmem₂) hc₁ hc₂ hd₁ hd₂
    heven hodd hd₁pos hd₁N hd₂N
  have hall : ∀ x : H.Gal, x ∈ N := by
    intro x
    have hx : galPerm H x ∈ N.map (galPerm H) := by
      rw [htop, ← hWr]
      exact ⟨x, rfl⟩
    obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.mp hx
    rwa [galPerm_injective H hxx'] at hx'
  rintro ⟨x, y⟩
  obtain ⟨w, hw⟩ := hsurj2 y
  obtain ⟨v, hv⟩ := (hmemN _).mp (hall (x * ((Gal.restrictProd H G w).1)⁻¹))
  refine ⟨v * w, ?_⟩
  rw [map_mul, hv]
  ext
  · simp
  · simp [hw]

/-! ### The Jacobi polynomials -/

theorem gcd_num_two_den {α β : ℚ} (hcond : DenomCond α β) :
    Int.gcd (α + β).num ((2 * (α + β).den : ℕ) : ℤ) = 1 := by
  obtain ⟨hDe, -⟩ := (denomCond_iff _ _).mp hcond
  have hr := gcd_num_den (α + β)
  rw [← Int.isCoprime_iff_gcd_eq_one] at hr ⊢
  have hDe' : Even ((α + β).den : ℤ) := by exact_mod_cast hDe
  have hrodd : Odd (α + β).num := by
    rw [← Int.not_even_iff_odd]
    intro hre
    have h2r : (2 : ℤ) ∣ (α + β).num := even_iff_two_dvd.mp hre
    have h2D : (2 : ℤ) ∣ ((α + β).den : ℤ) := even_iff_two_dvd.mp hDe'
    have := Int.dvd_gcd (c := 2) h2r h2D
    rw [Int.isCoprime_iff_gcd_eq_one.mp hr] at this
    omega
  have h2 : IsCoprime (α + β).num 2 := by
    obtain ⟨m, hm⟩ := hrodd
    rw [hm]
    exact ⟨1, -m, by ring⟩
  push_cast
  exact h2.mul_right hr

open Classical in
/-- **Proposition 5.2, quadratic part, for the primes (5.20).** For `c ≠ 0` with `v_p(c) = 0`,
`Gal(P_n^{(α,β)}(1 + cX²)/ℚ)` contains a single `2d_p`-cycle. -/
theorem exists_isCycle_comp_of_eligible {α β : ℚ} (hcond : DenomCond α β) {n p : ℕ}
    (hp : p.Prime) (h1 : (α + β).den * n + cycleBound α β < p)
    (h2 : 2 * (p + cycleBound α β) ≤ 3 * ((α + β).den * n))
    (h3 : (p : ℤ) ≡ (α + β).num [ZMOD (α + β).den]) {c : ℚ} (hc : c ≠ 0)
    (hcp : padicValRat p c = 0) :
    ∃ σ : ((jacobiP α β n).comp (1 + C c * polyX ^ 2)).Gal, (galPerm _ σ).IsCycle ∧
      ((galPerm _ σ).support.card : ℤ) =
        2 * (2 * n + 1 - ((p : ℤ) - (α + β).num) / (α + β).den) := by
  have H := jacobiCycleHypotheses_of_eligible hcond hp h1 h2 h3
  have hb := cycleLength_bounds (α + β).den_pos (cycleBound_bounds α β).1 h1 h2 h3
  have hidx := H.cast_index
  rw [jacobiCycleIndex_eq] at hidx
  have hD2 := (denomCond_facts hcond).1
  have h2n : 2 * n ≤ (α + β).den * n := Nat.mul_le_mul_right n hD2
  have h2d : 2 * (n + 1 - jacobiCycleIndexNat p n (α + β).den (α + β).num) < p := by
    have := H.one_le_index
    omega
  have eα : ((α.num : ℚ) / ((α.den : ℤ) : ℚ)) = α := by push_cast; exact Rat.num_div_den α
  have eβ : ((β.num : ℚ) / ((β.den : ℤ) : ℚ)) = β := by push_cast; exact Rat.num_div_den β
  obtain ⟨σ₀, hσ₀, hcard₀, -⟩ := exists_isCycle_galPerm_jacobiP_comp H hc hcp h2d
  have key : ∃ σ : ((jacobiP ((α.num : ℚ) / ((α.den : ℤ) : ℚ))
      ((β.num : ℚ) / ((β.den : ℤ) : ℚ)) n).comp (1 + C c * polyX ^ 2)).Gal,
      (galPerm _ σ).IsCycle ∧ (galPerm _ σ).support.card =
        2 * (n + 1 - jacobiCycleIndexNat p n (α + β).den (α + β).num) := ⟨σ₀, hσ₀, hcard₀⟩
  rw [eα, eβ] at key
  obtain ⟨σ, hσ, hcard⟩ := key
  refine ⟨σ, hσ, ?_⟩
  rw [hcard]
  generalize ((p : ℤ) - (α + β).num) / ((α + β).den : ℤ) = k at hidx hb ⊢
  have := H.index_le_n
  omega

open Classical in
/-- The data attached to one prime of (5.20) after quadratic substitution: an element of
`Gal(h(1+cX²) g(1+cX²))` restricting trivially to `g(1+cX²)` and to a single `2d_p`-cycle on
the roots of `h(1+cX²)`. -/
theorem exists_restrictProd_comp_of_eligible {α β : ℚ} (hcond : DenomCond α β) {n p : ℕ}
    (hp : p.Prime) (h1 : (α + β).den * n + cycleBound α β < p)
    (h2 : 2 * (p + cycleBound α β) ≤ 3 * ((α + β).den * n))
    (h3 : (p : ℤ) ≡ (α + β).num [ZMOD (α + β).den]) {c : ℚ} (hc : c ≠ 0)
    (hcp : padicValRat p c = 0) {h g : ℚ[X]} {κ : ℚ} (hh : IsDominant (jacobiP α β n) h)
    (hfac : jacobiP α β n = C κ * h * g) :
    h.comp (1 + C c * polyX ^ 2) * g.comp (1 + C c * polyX ^ 2) ≠ 0 ∧
    ∃ ρ : (h.comp (1 + C c * polyX ^ 2) * g.comp (1 + C c * polyX ^ 2)).Gal,
      (galPerm _ (Gal.restrictProd _ _ ρ).1).IsCycle ∧
      ((galPerm _ (Gal.restrictProd _ _ ρ).1).support.card : ℤ) =
        2 * (2 * n + 1 - ((p : ℤ) - (α + β).num) / (α + β).den) ∧
      (Gal.restrictProd _ _ ρ).2 = 1 := by
  obtain ⟨σ, hσ, hcard⟩ := exists_isCycle_comp_of_eligible hcond hp h1 h2 h3 hc hcp
  have hb := cycleLength_bounds (α + β).den_pos (cycleBound_bounds α β).1 h1 h2 h3
  have hF0 := ne_zero_of_isCycle hσ
  have hf0 : jacobiP α β n ≠ 0 := by
    intro h0
    apply hF0
    rw [h0, zero_comp]
  have hsupp := aeval_eq_zero_of_isCycle_comp hc rfl (natDegree_jacobiP_le α β n) hh hσ
    (by omega)
  have hFfac : (jacobiP α β n).comp (1 + C c * polyX ^ 2) =
      C κ * h.comp (1 + C c * polyX ^ 2) * g.comp (1 + C c * polyX ^ 2) := by
    rw [hfac, mul_comp, mul_comp, C_comp]
  obtain ⟨ρ, hρ1, hρc, hρ2⟩ := exists_restrictProd_isCycle_of_noCommonRoot hF0 hFfac hσ hsupp
    (fun y hyh hyg => by
      rw [aeval_comp_quad] at hyh hyg
      exact not_common_root hf0 hh hfac hyh hyg)
  refine ⟨ne_zero_of_dvd_ne_zero hF0 ⟨C κ, by rw [hFfac]; ring⟩, ρ, hρ1, ?_, hρ2⟩
  rw [hρc, hcard]

open Classical in
/-- **Theorem 1.6, the quadratic substitution** (unfolded form). Fix `c ∈ ℚ^×`. For all large
`n` and every factorization `P_n^{(α,β)} = κ h g` with `h` dominant, `h(1 + cX²)` is irreducible
with Galois group `W_{M_n}`, and restriction
`Gal(h(1+cX²) g(1+cX²)/ℚ) → Gal(h(1+cX²)/ℚ) × Gal(g(1+cX²)/ℚ)` is bijective.

Conditional on [BMOR, Corollary 1.7], [BMOR, Proposition 6.19], Brun–Titchmarsh [MV, Theorem 2]
and [Jones, Corollary 1.3], taken as the hypotheses `hBMOR`, `h619`, `hBT`, `hJones`. -/
theorem quadratic_isDominant_jacobiP (hBMOR : BMORPrimeCountingBound)
    (h619 : BMORLargeModulusPrimeCounting) (hBT : BrunTitchmarshInequality)
    (hJones : JonesCycleTheorem) {α β : ℚ} (hcond : DenomCond α β) {c : ℚ} (hc : c ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ h g : ℚ[X], ∀ κ : ℚ, IsDominant (jacobiP α β n) h → g.Monic →
      jacobiP α β n = C κ * h * g →
      Irreducible (h.comp (1 + C c * polyX ^ 2)) ∧ GaloisGroupIsWreath (h.comp (1 + C c * polyX
        ^ 2)) ∧
      Function.Bijective (Gal.restrictProd (h.comp (1 + C c * polyX ^ 2))
        (g.comp (1 + C c * polyX ^ 2))) := by
  obtain ⟨hD2, hr, hgc⟩ := denomCond_facts hcond
  have hgr := gcd_num_two_den hcond
  have hDpos := (α + β).den_pos
  obtain ⟨N₀, hN₀⟩ := galoisGroupIsSymmetric_isDominant_jacobiP hBMOR h619 hBT hJones hcond
  obtain ⟨C₀, N₁, hN₁⟩ := natDegree_isDominant_jacobiP h619 hcond 1 one_pos
  have eve := eventually_exists_prime_upper hBMOR h619 (B := cycleBound α β) hD2 hgc
  have evo := eventually_exists_prime_upper hBMOR h619 (B := cycleBound α β) hD2 hgr
  have ev3 := eventually_le_log_natCast (10 * |C₀| + 1)
  have ev4 := eventually_ge_atTop
    (N₀ + N₁ + 100 * ((α + β).num.natAbs + 1) + c.num.natAbs + c.den + 1)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eve.and (evo.and (ev3.and ev4)))
  refine ⟨N, fun n hn h g κ hh hg hfac => ?_⟩
  obtain ⟨⟨pe, hpe, he1, he2, he3, he4⟩, ⟨po, hpo, ho1, ho2, ho3, ho4⟩, hL, hn'⟩ := hN n hn
  obtain ⟨hS, -⟩ := hN₀ n (by omega) h g κ hh hg hfac
  have hM := hN₁ n (by omega) h hh
  -- `M ≥ 0.9 n`
  rw [Real.rpow_one] at hM
  have hn100 : (100 : ℝ) ≤ n := by
    have : 100 ≤ n := by omega
    exact_mod_cast this
  have hlogpos : 0 < Real.log n := by linarith [abs_nonneg C₀]
  have hCn : C₀ * n / Real.log n ≤ 0.1 * n := by
    rw [div_le_iff₀ hlogpos]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n)
      (by linarith [le_abs_self C₀] : (0 : ℝ) ≤ Real.log n - 10 * C₀)]
  have hM9 : 0.9 * (n : ℝ) ≤ h.natDegree := by linarith
  -- the primes are large
  have hnr : 100 * (|(α + β).num| + 1) ≤ (n : ℤ) := by
    have h0 : ((α + β).num.natAbs : ℤ) = |(α + β).num| := Int.natCast_natAbs _
    have h1 : 100 * ((α + β).num.natAbs + 1) ≤ n := by omega
    have h2 : (100 * (((α + β).num.natAbs : ℤ) + 1) : ℤ) ≤ n := by exact_mod_cast h1
    rw [← h0]
    exact h2
  have hnDn : n ≤ (α + β).den * n := Nat.le_mul_of_pos_left n hDpos
  have hcp : ∀ p : ℕ, p.Prime → (α + β).den * n + cycleBound α β < p →
      padicValRat p c = 0 := fun p hp hp1 =>
    padicValRat_eq_zero_of_lt hp hc (by omega) (by omega)
  -- the two cycles
  obtain ⟨he3', heven⟩ := modEq_and_even_of_modEq_add (n := n) hDpos he4
  obtain ⟨ho3', hodd⟩ := modEq_and_odd_of_modEq (n := n) hDpos ho4
  obtain ⟨hP0, ρe, hρe1, hρec, hρe2⟩ := exists_restrictProd_comp_of_eligible hcond hpe he1 he2
    he3' hc (hcp pe hpe he1) hh hfac
  obtain ⟨-, ρo, hρo1, hρoc, hρo2⟩ := exists_restrictProd_comp_of_eligible hcond hpo ho1 ho2 ho3' hc
    (hcp po hpo ho1) hh hfac
  have hbe := cycleLength_bounds hDpos (cycleBound_bounds α β).1 he1 he2 he3'
  have hbo := cycleLength_bounds hDpos (cycleBound_bounds α β).1 ho1 ho2 ho3'
  have hue := cycleLength_le_of_upper hDpos he3 he3' hnr
  have huo := cycleLength_le_of_upper hDpos ho3 ho3' hnr
  generalize hde : 2 * (n : ℤ) + 1 - ((pe : ℤ) - (α + β).num) / (α + β).den = de at *
  generalize hdo : 2 * (n : ℤ) + 1 - ((po : ℤ) - (α + β).num) / (α + β).den = do_ at *
  have hde0 : 0 ≤ de := by omega
  have hdo0 : 0 ≤ do_ := by omega
  lift de to ℕ using hde0
  lift do_ to ℕ using hdo0
  have hue' : (100 : ℝ) * de ≤ 61 * n := by exact_mod_cast hue
  have huo' : (100 : ℝ) * do_ ≤ 61 * n := by exact_mod_cast huo
  have hdeM : de < h.natDegree := by
    have : (de : ℝ) < h.natDegree := by linarith
    exact_mod_cast this
  have hdoM : do_ < h.natDegree := by
    have : (do_ : ℝ) < h.natDegree := by linarith
    exact_mod_cast this
  have hρec' : (galPerm _ (Gal.restrictProd _ _ ρe).1).support.card = 2 * de := by
    exact_mod_cast hρec
  have hρoc' : (galPerm _ (Gal.restrictProd _ _ ρo).1).support.card = 2 * do_ := by
    exact_mod_cast hρoc
  have heven' : Even de := (Int.even_coe_nat _).mp heven
  have hodd' : Odd do_ := (Int.odd_coe_nat _).mp hodd
  -- `W_M` and irreducibility
  have hhd := (isDominant_iff _ _).mp hh
  have h1 := eval_one_ne_zero_of_dvd ((denomCond_iff _ _).mp hcond).2.2.1 hhd.2.2.1
  obtain ⟨hW, hirr, h0, hneg, hNsq⟩ :=
    galoisGroupIsWreath_comp hhd.2.1 hS hc rfl h1 hρo1 hρoc' hodd' hdoM
  refine ⟨hirr, hW, ?_⟩
  exact restrictProd_bijective_of_wreath hP0 h0 hneg hW hρe1 hρec' hρo1 hρoc' heven' hodd'
    (by omega) (by rw [hNsq]; exact hdeM) (by rw [hNsq]; exact hdoM) hρe2 hρo2

end FixedRationalParameters

end ArithmeticOfJacobiPolynomials
