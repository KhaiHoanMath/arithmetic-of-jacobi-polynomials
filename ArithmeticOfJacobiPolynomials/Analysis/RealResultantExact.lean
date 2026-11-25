/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Analysis.RealResultant
public import ArithmeticOfJacobiPolynomials.Analysis.SourceRealResultantTwoPower
public import ArithmeticOfJacobiPolynomials.Padic.ProjectiveDistance

/-!
# Lemma 2.6 exactly as stated

This file proves Lemma 2.6 of the manuscript with the manuscript's
hypotheses: the 2-adic bound `v_2(R) ≤ e c_F + d c_G - de + d D_2`, which
`realResultant_lowerBound_of_twoAdic_bound` takes as a hypothesis, is derived here from the
bound `D_2` on the projective row sums of `h(2X+1)` at `2`.

* `resultant_comp_two_mul_X_add_one`: `Res(F(2X+1), G(2X+1)) = 2^{de} Res(F,G)`.
* `exists_comp_eq_C_two_pow_mul` (in `SourceRealResultantTwoPower`): `F(2X+1) = 2^{c_F} F̃` with
  `F̃ ∈ ℤ[X]` having an odd coefficient, so that `F̃` is primitive over `ℤ_[2]`.
* `padicValInt_resultant_le_of_rowBound`: the 2-adic bound, through the projective resultant
  formula (2.6) applied to `F̃, G̃`.
* `realResultant_lowerBound`: Lemma 2.6, with the comparison of `log κ - (c_F + c_G) log 2` and
  `-log b_h` proved as in the manuscript (`two_pow_shiftedTwoAdicOrder_mul_le`).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

local notation "K₂" => PadicAlgCl 2

/-- Over an algebraically closed field in which `2 ≠ 0`,
`Res(A(2X+1), B(2X+1)) = 2^{deg A · deg B} Res(A, B)`. -/
theorem resultant_comp_two_mul_X_add_one_of_isAlgClosed {k : Type*} [Field k] [IsAlgClosed k]
    (h2 : (2 : k) ≠ 0) (A B : k[X]) :
    resultant (A.comp (2 * polyX + 1)) (B.comp (2 * polyX + 1)) =
      2 ^ (A.natDegree * B.natDegree) * resultant A B := by
  have hL : (2 * polyX + 1 : k[X]) = C 2 * polyX + C 1 := by rw [map_ofNat C 2, C_1]
  have hLdeg : (2 * polyX + 1 : k[X]).natDegree = 1 := by rw [hL]; exact natDegree_linear h2
  have hdegA : (A.comp (2 * polyX + 1)).natDegree = A.natDegree := by
    rw [natDegree_comp, hLdeg, mul_one]
  have hdegB : (B.comp (2 * polyX + 1)).natDegree = B.natDegree := by
    rw [natDegree_comp, hLdeg, mul_one]
  have hlc : (A.comp (2 * polyX + 1)).leadingCoeff = A.leadingCoeff * 2 ^ A.natDegree := by
    rw [leadingCoeff_comp (by rw [hLdeg]; exact one_ne_zero), hL, leadingCoeff_linear h2]
  have hroots : (A.comp (2 * polyX + 1)).roots.map (fun x => 2 * x + 1) = A.roots := by
    rw [hL]; exact map_roots_comp_C_mul_X_add_C A 2 1 (IsUnit.mk0 _ h2)
  have e1 : resultant (A.comp (2 * polyX + 1)) (B.comp (2 * polyX + 1)) =
      resultant (A.comp (2 * polyX + 1)) (B.comp (2 * polyX + 1)) (A.comp (2 * polyX + 1)).natDegree
        B.natDegree := by rw [hdegB]
  rw [e1, resultant_eq_prod_eval _ _ _ hdegB.le (IsAlgClosed.splits _),
    resultant_eq_prod_eval _ _ _ le_rfl (IsAlgClosed.splits _), hlc, ← hroots, Multiset.map_map]
  have hfun : ((B.comp (2 * polyX + 1)).eval) = B.eval ∘ fun x => 2 * x + 1 := by
    funext x; simp [eval_comp]
  rw [hfun, mul_pow, ← pow_mul]
  ring

/-- The cast of an integer resultant to a field of characteristic zero. -/
theorem intCast_resultant {k : Type*} [Field k] [CharZero k] (A B : ℤ[X]) :
    ((resultant A B : ℤ) : k) =
      resultant (A.map (Int.castRingHom k)) (B.map (Int.castRingHom k)) := by
  have hinj : Function.Injective (Int.castRingHom k) := Int.cast_injective
  have h1 : resultant (A.map (Int.castRingHom k)) (B.map (Int.castRingHom k)) =
      resultant (A.map (Int.castRingHom k)) (B.map (Int.castRingHom k)) A.natDegree
        B.natDegree := by
    rw [← natDegree_map_eq_of_injective hinj A, ← natDegree_map_eq_of_injective hinj B]
  rw [h1, resultant_map_map]
  rfl

/-- `Res(F(2X+1), G(2X+1)) = 2^{de} Res(F,G)` in `ℤ[X]`. -/
theorem resultant_comp_two_mul_X_add_one (A B : ℤ[X]) :
    resultant (A.comp (2 * polyX + 1)) (B.comp (2 * polyX + 1)) =
      2 ^ (A.natDegree * B.natDegree) * resultant A B := by
  have hinj : Function.Injective (Int.castRingHom K₂) := Int.cast_injective
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → K₂))
  have key := resultant_comp_two_mul_X_add_one_of_isAlgClosed (two_ne_zero)
    (A.map (Int.castRingHom K₂)) (B.map (Int.castRingHom K₂))
  have hmapL : (2 * polyX + 1 : ℤ[X]).map (Int.castRingHom K₂) = 2 * polyX + 1 := by simp
  rw [intCast_resultant, Polynomial.map_comp, Polynomial.map_comp, hmapL, key]
  push_cast
  rw [intCast_resultant, natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj]

/-- An integer polynomial with an odd coefficient is primitive over `ℤ_[2]`. -/
theorem isPrimitive_map_padicInt_of_not_two_dvd {P : ℤ[X]} {j : ℕ}
    (hj : ¬ (2 : ℤ) ∣ P.coeff j) : (P.map (Int.castRingHom ℤ_[2])).IsPrimitive := by
  intro r hr
  have h1 : r ∣ ((P.coeff j : ℤ) : ℤ_[2]) := by
    have := (C_dvd_iff_dvd_coeff r _).mp hr j
    simpa [coeff_map] using this
  have hu : IsUnit ((P.coeff j : ℤ) : ℤ_[2]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => hj ?_)
    have := (PadicInt.norm_int_lt_one_iff_dvd (p := 2) _).mp hlt
    exact_mod_cast this
  exact isUnit_of_dvd_unit h1 hu

/-- `padicValInt 2 (2^k) = k`. -/
lemma padicValInt_two_pow (k : ℕ) : padicValInt 2 ((2 : ℤ) ^ k) = k := by
  rw [padicValInt, Int.natAbs_pow]
  exact padicValNat.prime_pow k

open Classical in
/-- **The 2-adic bound of Lemma 2.6.** Let `F, G ∈ ℤ[X]` be nonzero with
`F G = κ h` for some `κ ≠ 0`, where `h ∈ ℚ[X]` is such that `h(2X+1)` has simple roots in
`PadicAlgCl 2` whose projective row sums at `2` are at most `D₂`. Then, with `d = deg F`,
`e = deg G`, `v_2(Res(F,G)) ≤ e c_F + d c_G - de + d D₂`. -/
theorem padicValInt_resultant_le_of_rowBound {h : ℚ[X]} {κ : ℚ} (hκ : κ ≠ 0) {F G : ℤ[X]}
    (hF : F ≠ 0) (hG : G ≠ 0)
    (hFG : (F * G).map (Int.castRingHom ℚ) = C κ * h)
    (hnodup : ((h.comp (2 * polyX + 1)).map (algebraMap ℚ K₂)).roots.Nodup)
    {D₂ : ℝ}
    (hrow : ∀ z ∈ ((h.comp (2 * polyX + 1)).map (algebraMap ℚ K₂)).roots,
      ∑ w ∈ ((h.comp (2 * polyX + 1)).map (algebraMap ℚ K₂)).roots.toFinset.erase z,
        projDist 2 z w ≤ D₂) :
    (padicValInt 2 (F.resultant G) : ℝ) ≤
      G.natDegree * shiftedTwoAdicOrder F + F.natDegree * shiftedTwoAdicOrder G -
        F.natDegree * G.natDegree + F.natDegree * D₂ := by
  classical
  obtain ⟨F₂, hF₂, jF, hjF⟩ := exists_comp_eq_C_two_pow_mul hF
  obtain ⟨G₂, hG₂, jG, hjG⟩ := exists_comp_eq_C_two_pow_mul hG
  set cF := shiftedTwoAdicOrder F
  set cG := shiftedTwoAdicOrder G
  set d := F.natDegree with hd
  set e := G.natDegree with he
  set L : ℤ[X] := 2 * polyX + 1 with hLdef
  have hL : L = C 2 * polyX + C 1 := by simp [hLdef]
  have hLdeg : L.natDegree = 1 := by rw [hL]; exact natDegree_linear two_ne_zero
  have h2F : (2 : ℤ) ^ cF ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2G : (2 : ℤ) ^ cG ≠ 0 := pow_ne_zero _ two_ne_zero
  have hF₂d : F₂.natDegree = d := by
    have := congrArg natDegree hF₂
    rwa [natDegree_comp, hLdeg, mul_one, natDegree_C_mul h2F, eq_comm] at this
  have hG₂e : G₂.natDegree = e := by
    have := congrArg natDegree hG₂
    rwa [natDegree_comp, hLdeg, mul_one, natDegree_C_mul h2G, eq_comm] at this
  -- `2^{de} R = 2^{e c_F + d c_G} R₂`
  have hres : (2 : ℤ) ^ (d * e) * F.resultant G =
      ((2 : ℤ) ^ cF) ^ e * ((2 : ℤ) ^ cG) ^ d * F₂.resultant G₂ := by
    rw [← resultant_comp_two_mul_X_add_one F G, hF₂, hG₂]
    have e1 : resultant (C ((2 : ℤ) ^ cF) * F₂) (C ((2 : ℤ) ^ cG) * G₂) =
        resultant (C ((2 : ℤ) ^ cF) * F₂) (C ((2 : ℤ) ^ cG) * G₂) d e := by
      rw [natDegree_C_mul h2F, natDegree_C_mul h2G, hF₂d, hG₂e]
    have e2 : resultant F₂ G₂ = resultant F₂ G₂ d e := by rw [hF₂d, hG₂e]
    rw [e1, resultant_C_mul_left, resultant_C_mul_right, e2]
    ring
  -- the polynomials over `ℤ_[2]` and `K₂`
  set φ : ℤ →+* K₂ := Int.castRingHom K₂ with hφ
  have hφinj : Function.Injective φ := Int.cast_injective
  set F₂' := F₂.map (Int.castRingHom ℤ_[2]) with hF₂'
  set G₂' := G₂.map (Int.castRingHom ℤ_[2]) with hG₂'
  have hmapK : ∀ P : ℤ[X], (P.map (Int.castRingHom ℤ_[2])).map (algebraMap ℤ_[2] K₂) =
      P.map φ := by
    intro P
    rw [Polynomial.map_map]
    congr 1
  set F₃ := F₂.map φ with hF₃
  set G₃ := G₂.map φ with hG₃
  have hF₂0 : F₂ ≠ 0 := by
    rintro rfl
    rw [natDegree_zero] at hF₂d
    have := congrArg natDegree hF₂
    simp only [mul_zero, natDegree_zero] at this
    have hFL : F.comp L ≠ 0 := by
      intro h0
      have := leadingCoeff_comp (p := F) (by rw [hLdeg]; exact one_ne_zero : L.natDegree ≠ 0)
      rw [h0, leadingCoeff_zero, hL, leadingCoeff_linear two_ne_zero] at this
      exact mul_ne_zero (leadingCoeff_ne_zero.mpr hF) (pow_ne_zero _ two_ne_zero) this.symm
    exact hFL (by rw [hF₂, mul_zero])
  have hG₂0 : G₂ ≠ 0 := by
    rintro rfl
    have hGL : G.comp L ≠ 0 := by
      intro h0
      have := leadingCoeff_comp (p := G) (by rw [hLdeg]; exact one_ne_zero : L.natDegree ≠ 0)
      rw [h0, leadingCoeff_zero, hL, leadingCoeff_linear two_ne_zero] at this
      exact mul_ne_zero (leadingCoeff_ne_zero.mpr hG) (pow_ne_zero _ two_ne_zero) this.symm
    exact hGL (by rw [hG₂, mul_zero])
  have hF₃0 : F₃ ≠ 0 := (Polynomial.map_ne_zero_iff hφinj).mpr hF₂0
  have hG₃0 : G₃ ≠ 0 := (Polynomial.map_ne_zero_iff hφinj).mpr hG₂0
  set hL₂ := (h.comp (2 * polyX + 1)).map (algebraMap ℚ K₂) with hhL₂
  -- `κ h(2X+1) = 2^{c_F + c_G} F̃ G̃` over `K₂`
  have hκK : (algebraMap ℚ K₂ κ) ≠ 0 := (_root_.map_ne_zero _).mpr hκ
  have e0 : ((F.comp L) * (G.comp L)).map (Int.castRingHom ℚ) = C κ * h.comp (2 * polyX + 1) := by
    rw [← mul_comp, Polynomial.map_comp, hFG, mul_comp, C_comp]
    congr 2
    simp [hLdef]
  have e1 := congrArg (Polynomial.map (algebraMap ℚ K₂)) e0
  rw [Polynomial.map_map,
    show (algebraMap ℚ K₂).comp (Int.castRingHom ℚ) = φ from RingHom.ext_int _ _,
    Polynomial.map_mul (p := C κ), map_C] at e1
  have hroots : hL₂.roots = F₃.roots + G₃.roots := by
    rw [← roots_C_mul hL₂ hκK, ← e1, hF₂, hG₂, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_mul, map_C, map_C]
    have h2F' : φ ((2 : ℤ) ^ cF) ≠ 0 := (_root_.map_ne_zero_iff _ hφinj).mpr h2F
    have h2G' : φ ((2 : ℤ) ^ cG) ≠ 0 := (_root_.map_ne_zero_iff _ hφinj).mpr h2G
    rw [roots_mul (mul_ne_zero (mul_ne_zero (C_ne_zero.mpr h2F') hF₃0)
        (mul_ne_zero (C_ne_zero.mpr h2G') hG₃0)), roots_C_mul _ h2F', roots_C_mul _ h2G']
  have hnodup' := hnodup
  rw [hroots] at hnodup'
  obtain ⟨-, ndG, disj⟩ := Multiset.nodup_add.mp hnodup'
  have hprimF := isPrimitive_map_padicInt_of_not_two_dvd hjF
  have hprimG := isPrimitive_map_padicInt_of_not_two_dvd hjG
  have hsum := padicVal_resultant_eq_sum_projDist (p := 2) hprimF hprimG (by
    rw [hmapK, hmapK]
    rintro z hz w hw rfl
    exact Multiset.disjoint_left.mp disj hz hw)
  rw [hmapK, hmapK] at hsum
  -- nonvanishing of the resultants
  have hR₂ : F₂.resultant G₂ ≠ 0 := by
    intro h0
    have := intCast_resultant (k := K₂) F₂ G₂
    rw [h0, Int.cast_zero, resultant_eq_prod_eval _ _ _ le_rfl (IsAlgClosed.splits _)] at this
    refine mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hF₃0))
      (Multiset.prod_ne_zero fun hmem => ?_) this.symm
    obtain ⟨z, hz, hz0⟩ := Multiset.mem_map.mp hmem
    exact Multiset.disjoint_left.mp disj hz ((mem_roots hG₃0).mpr hz0)
  have hR : F.resultant G ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hres
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2F) (pow_ne_zero _ h2G)) hR₂ hres.symm
  -- valuations
  have hv := congrArg (padicValInt 2) hres
  rw [padicValInt.mul (pow_ne_zero _ two_ne_zero) hR,
    padicValInt.mul (mul_ne_zero (pow_ne_zero _ h2F) (pow_ne_zero _ h2G)) hR₂,
    padicValInt.mul (pow_ne_zero _ h2F) (pow_ne_zero _ h2G), ← pow_mul, ← pow_mul,
    padicValInt_two_pow, padicValInt_two_pow, padicValInt_two_pow] at hv
  have hvR : (d : ℝ) * e + padicValInt 2 (F.resultant G) =
      cF * e + cG * d + padicValInt 2 (F₂.resultant G₂) := by exact_mod_cast hv
  have hv₂ : (padicValInt 2 (F₂.resultant G₂) : ℝ) = padicVal 2 (resultant F₂' G₂') :=
    (padicVal_resultant_map_intCast hR₂).symm
  -- the row bound
  have hcard : F₃.roots.card = d := by
    rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map_eq_of_injective hφinj, hF₂d]
  have hle := Multiset.sum_le_card_nsmul
    (F₃.roots.map fun z => (G₃.roots.map fun w => projDist 2 z w).sum) D₂ (by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
      have hzH : z ∈ hL₂.roots := by rw [hroots]; exact Multiset.mem_add.mpr (Or.inl hz)
      refine le_trans ?_ (hrow z hzH)
      rw [show (G₃.roots.map fun w => projDist 2 z w).sum =
          ∑ w ∈ G₃.roots.toFinset, projDist 2 z w by
        rw [Finset.sum_eq_multiset_sum, Multiset.toFinset_val, ndG.dedup]]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => ?_)
        (fun w _ _ => projDist_nonneg z w)
      rw [Multiset.mem_toFinset] at hw
      refine Finset.mem_erase.mpr ⟨?_, Multiset.mem_toFinset.mpr
        (by rw [hroots]; exact Multiset.mem_add.mpr (Or.inr hw))⟩
      rintro rfl
      exact Multiset.disjoint_left.mp disj hz hw)
  rw [Multiset.card_map, hcard, nsmul_eq_mul] at hle
  rw [← hsum] at hle
  linarith

/-- Simplicity of the roots of `h(2X+1)` in `PadicAlgCl 2` when `h ∈ ℚ[X]` has
`deg h` distinct real roots. -/
theorem nodup_roots_comp_two_mul_X_add_one_of_real {h : ℚ[X]} (hh : h ≠ 0)
    (hcard : (h.map (algebraMap ℚ ℝ)).roots.card = h.natDegree)
    (hnodup : (h.map (algebraMap ℚ ℝ)).roots.Nodup) :
    ((h.comp (2 * polyX + 1)).map (algebraMap ℚ K₂)).roots.Nodup := by
  set hr := h.map (algebraMap ℚ ℝ) with hhr
  have hr0 : hr ≠ 0 := Polynomial.map_ne_zero hh
  have hsplit : hr.Splits := splits_iff_card_roots.mpr (by
    rw [hcard, hhr, natDegree_map])
  have hsep : h.Separable :=
    (separable_map _).mp ((nodup_roots_iff_of_splits hr0 hsplit).mp hnodup)
  have hK := nodup_roots (hsep.map (f := algebraMap ℚ K₂))
  have hL : (2 * polyX + 1 : K₂[X]) = C 2 * polyX + C 1 := by rw [map_ofNat C 2, C_1]
  have hmap : (h.comp (2 * polyX + 1)).map (algebraMap ℚ K₂) =
      (h.map (algebraMap ℚ K₂)).comp (C 2 * polyX + C 1) := by
    rw [Polynomial.map_comp, ← hL]
    simp
  rw [hmap]
  refine Multiset.Nodup.of_map (fun x => 2 * x + 1) ?_
  rw [map_roots_comp_C_mul_X_add_C _ 2 1 (IsUnit.mk0 _ two_ne_zero)]
  exact hK

open Classical in
/-- **Lemma 2.6.**

Let `h ∈ ℤ[1/2][x]` (a `ℚ[X]` with `2^k h ∈ ℤ[X]` for some `k`) have degree `N`, positive
leading coefficient, and `N` distinct real roots, all nonzero and in `(-1,1)`. Suppose
`b_h = h(1)` is a positive integer and `|h'(α)| > γ > 0` at every root, and that the projective
row sums of `h(2X+1)` at `2` are at most `D₂`: for every root `z ∈ PadicAlgCl 2` of `h(2X+1)`,
`∑_{w ≠ z} δ_2(z,w) ≤ D₂`. Let `κ > 0` be such that `H = κh` is a primitive integral
polynomial, and suppose `H = FG` with `F, G ∈ ℤ[x]` primitive with positive leading coefficients,
`1 ≤ d = deg F ≤ e = deg G` and `d + e = N`. Put `R = Res(F, G)`, `𝓡 = |R| / 2^{v_2(R)}`,
`u = lc F`, `c_F = min_j v_2([X^j] F(2X+1))` (`shiftedTwoAdicOrder`), likewise `c_G`, let
`α_1, …, α_d` be distinct roots of `F` (hence all of them) and `V_F = ∏_{i<j} (α_i - α_j)^2`.
Using the proved interval Vandermonde bound (`intervalVandermondeBound`, Lemma 2.5),
`u > 2^{c_F}`, (2.11)
`log 𝓡 / d > e log 2 - log V_F / d + log (γ / b_h) - D_2 log 2 + ((e-d)/d) log (u / 2^{c_F})`,
and (2.12) `log 𝓡 / d > (N-3) log 2 - log d + log (γ / b_h) - D_2 log 2`.

The hypotheses `h ∈ ℤ[1/2][x]` and the primitivity of `H` are used, as in the manuscript, to show
`log κ - (c_F + c_G) log 2 ≥ -log b_h` (`κ = 2^k/c` with `c` odd dividing `b_h`, Gauss
multiplicativity `c_F + c_G = k + t_2`, `t_2 ≤ v_2(b_h)`; see `SourceRealResultantTwoPower`).
The hypotheses `lc h > 0` and the primitivity of `F`, `G` are part of the manuscript's statement
but are not needed by the proof. -/
theorem realResultant_lowerBound {h : ℚ[X]} {N : ℕ}
    (hdyadic : ∃ (k : ℕ) (P : ℤ[X]), P.map (Int.castRingHom ℚ) = C ((2 : ℚ) ^ k) * h)
    (hdeg : h.natDegree = N) (_hlc : 0 < h.leadingCoeff)
    (hcard : (h.map (algebraMap ℚ ℝ)).roots.card = N)
    (hnodup : (h.map (algebraMap ℚ ℝ)).roots.Nodup)
    (hroots : ∀ x ∈ (h.map (algebraMap ℚ ℝ)).roots, x ≠ 0 ∧ -1 < x ∧ x < 1)
    {b : ℕ} (hb : 0 < b) (hb1 : h.eval 1 = b)
    {γ : ℝ} (hγ : 0 < γ)
    (hγ' : ∀ x ∈ (h.map (algebraMap ℚ ℝ)).roots,
      γ < |(derivative (h.map (algebraMap ℚ ℝ))).eval x|)
    {D₂ : ℝ}
    (hrow : ∀ z ∈ ((h.comp (2 * polyX + 1)).map (algebraMap ℚ K₂)).roots,
      ∑ w ∈ ((h.comp (2 * polyX + 1)).map (algebraMap ℚ K₂)).roots.toFinset.erase z,
        projDist 2 z w ≤ D₂)
    {κ : ℚ} (hκ : 0 < κ) {H : ℤ[X]} (hH : H.map (Int.castRingHom ℚ) = C κ * h)
    (hHprim : H.IsPrimitive)
    {F G : ℤ[X]} (hHFG : H = F * G) (_hFprim : F.IsPrimitive) (_hGprim : G.IsPrimitive)
    (hFlc : 0 < F.leadingCoeff) (hGlc : 0 < G.leadingCoeff)
    {d e : ℕ} (hdF : F.natDegree = d) (heG : G.natDegree = e) (hd : 1 ≤ d) (hde : d ≤ e)
    (hdeN : d + e = N)
    {α : Fin d → ℝ} (hα : Function.Injective α)
    (hαF : ∀ i, (F.map (Int.castRingHom ℝ)).eval (α i) = 0) :
    (2 : ℤ) ^ shiftedTwoAdicOrder F < F.leadingCoeff ∧
    (e : ℝ) * Real.log 2 -
          Real.log (∏ i, ∏ j ∈ univ.filter (fun j => i < j), (α i - α j) ^ 2) / d +
        Real.log (γ / b) - D₂ * Real.log 2 +
        ((e : ℝ) - d) / d * Real.log (F.leadingCoeff / 2 ^ shiftedTwoAdicOrder F) <
      Real.log (|(F.resultant G : ℝ)| / 2 ^ padicValInt 2 (F.resultant G)) / d ∧
    ((N : ℝ) - 3) * Real.log 2 - Real.log d + Real.log (γ / b) - D₂ * Real.log 2 <
      Real.log (|(F.resultant G : ℝ)| / 2 ^ padicValInt 2 (F.resultant G)) / d := by
  subst hdF heG hHFG
  have hh0 : h ≠ 0 := by
    rintro rfl
    simp only [eval_zero] at hb1
    exact absurd (by exact_mod_cast hb1.symm : b = 0) hb.ne'
  have hF0 : F ≠ 0 := by rintro rfl; simp at hFlc
  have hG0 : G ≠ 0 := by rintro rfl; simp at hGlc
  have hK := nodup_roots_comp_two_mul_X_add_one_of_real hh0 (hcard.trans hdeg.symm) hnodup
  have h2 := padicValInt_resultant_le_of_rowBound hκ.ne' hF0 hG0 hH hK hrow
  obtain ⟨m, P, hP⟩ := hdyadic
  have hκb : (2 : ℚ) ^ shiftedTwoAdicOrder F * 2 ^ shiftedTwoAdicOrder G ≤ κ * b :=
    two_pow_shiftedTwoAdicOrder_mul_le hκ hP hH hHprim rfl hF0 hG0 hb hb1
  have hκb' : (2 : ℝ) ^ shiftedTwoAdicOrder F * 2 ^ shiftedTwoAdicOrder G ≤ κ * b := by
    exact_mod_cast hκb
  exact realResultant_lowerBound_of_twoAdic_bound hroots hb hb1 hγ hγ' hκ hH hFlc rfl rfl
    hd hde hdeN hκb' h2 hα hαF

end ArithmeticOfJacobiPolynomials
