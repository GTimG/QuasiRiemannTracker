/- Modified by Joseph Bebel (2026-11-12): smaller-tolerance inverse
HIGH leaf; original coefficient, mask and principal-row proofs are retained. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.SlotDict
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.Pointwise
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.CenteredExceptionalCount

/-!
# High.Inverse.Trivial — trivial bounds of the inverse HIGH leaf

Used for the large heights (`|θ| + hv ≥ Z^A`, paid by the per-data height degree) and for the
slots below the width floor:

* `trivial_polynomial` — `‖polynomial χ inv Φ D 0 ω‖² ≤ C D` for `D ≥ 1`, uniformly in `χ, ω`;
* `trivial_slot` — `‖directSlot u L β D‖² ≤ 2^16 D` for pools of nonzero ideals of norm `≤ 2D`
  and `‖β‖ ≤ 1`;
* `row_count` — at most `768 Z` nonzero elements in the ball `‖u‖² ≤ Z`;
* `trivial_energy` — the whole inverse marked sum of the ball is `≤ C₀ 2^(16 card ι) Z^(2+∑ ell)`
  (used for the large heights `|θ| + hv ≥ Z^A`).
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High.Inverse
noncomputable section
open scoped Classical BigOperators
open Set
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDyadic
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O

/-- **Trivial bound of the dyadic polynomial.** -/
theorem trivial_polynomial (Φ : ℝ → ℂ) (ao bo : ℝ) (hΦs : Function.support Φ ⊆ Icc ao bo)
    (hΦ : Continuous Φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : Character) (inv : Bool) (D ω : ℝ), 1 ≤ D →
      ‖polynomial χ inv Φ D 0 ω‖^2 ≤ C * D := by
  have hcs : HasCompactSupport Φ := by
    apply HasCompactSupport.intro isCompact_Icc
    intro x hx
    by_contra h
    exact hx (hΦs h)
  obtain ⟨B, hB⟩ := hΦ.bounded_above_of_compact_support hcs
  set B' : ℝ := max B 0 with hB'
  set bb : ℝ := max bo 1 with hbb
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have hbb1 : 1 ≤ bb := le_max_right _ _
  refine ⟨(128 * bb * B')^2 + 1, by positivity, ?_⟩
  intro χ inv D ω hD
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  set f := summand χ inv Φ D 0 ω with hf
  have hfin := summand_finite_support χ inv Φ ao bo D 0 ω hD0 hΦs
  set s := hfin.toFinset with hs
  have htsum : (∑' I, f I) = ∑ I ∈ s, f I := by
    apply tsum_eq_sum
    intro b hb
    by_contra h
    exact hb ((Set.Finite.mem_toFinset hfin).mpr h)
  have hterm : ∀ I, ‖f I‖ ≤ B' := by
    intro I
    have hx : 0 < norm I / D := div_pos (norm_pos I) hD0
    rw [hf]
    unfold summand
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp only [Complex.neg_re, shift_re, neg_zero, Real.rpow_zero, mul_one]
    have h1 := coefficient_norm_le χ inv I.val
    have h2 : ‖Φ (norm I / D)‖ ≤ B' := (hB _).trans (le_max_left _ _)
    calc ‖coefficient χ inv I.val‖ * ‖Φ (norm I / D)‖ ≤ 1 * B' :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = B' := one_mul _
  have hcard : (s.card : ℝ) ≤ 128 * (bb * D) := by
    have hmap := DescentFiberCost.finite_ideal_count_real
      (s.map ⟨Subtype.val, Subtype.val_injective⟩) (bb * D) (one_le_mul_of_one_le_of_one_le hbb1 hD)
      (by
        intro I hI
        obtain ⟨J, _, rfl⟩ := Finset.mem_map.mp hI
        exact J.property)
      (by
        intro I hI
        obtain ⟨J, hJ, rfl⟩ := Finset.mem_map.mp hI
        have hJs : f J ≠ 0 := (Set.Finite.mem_toFinset hfin).mp hJ
        have hw : Φ (norm J / D) ≠ 0 := by
          intro h0
          apply hJs
          rw [hf]
          simp [summand, h0]
        have hup := (hΦs hw).2
        have h1 : norm J ≤ bo * D := by
          have := (div_le_iff₀ hD0).mp hup
          linarith
        have h2 : bo * D ≤ bb * D := mul_le_mul_of_nonneg_right (le_max_left _ _) hD0.le
        exact h1.trans h2)
    rwa [Finset.card_map] at hmap
  have hsum : ‖∑' I, f I‖ ≤ 128 * bb * B' * D := by
    rw [htsum]
    calc ‖∑ I ∈ s, f I‖ ≤ ∑ I ∈ s, ‖f I‖ := norm_sum_le _ _
      _ ≤ ∑ _I ∈ s, B' := Finset.sum_le_sum fun I _ => hterm I
      _ = (s.card : ℝ) * B' := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (128 * (bb * D)) * B' := mul_le_mul_of_nonneg_right hcard hB'0
      _ = 128 * bb * B' * D := by ring
  have hpre : ‖(D : ℂ)^(-(1/2 : ℂ))‖ = D^(-(1/2 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hD0]
    norm_num
  have hq2 : (D^(-(1/2 : ℝ)))^2 = D⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD0.le]
    norm_num
    exact Real.rpow_neg_one D
  have hq0 : 0 ≤ D^(-(1/2 : ℝ)) := Real.rpow_nonneg hD0.le _
  have hnorm : ‖polynomial χ inv Φ D 0 ω‖ ≤ D^(-(1/2 : ℝ)) * (128 * bb * B' * D) := by
    unfold polynomial
    rw [norm_mul, hpre]
    exact mul_le_mul_of_nonneg_left hsum hq0
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc ‖polynomial χ inv Φ D 0 ω‖^2 ≤ (D^(-(1/2 : ℝ)) * (128 * bb * B' * D))^2 := hsq
    _ = (128 * bb * B')^2 * D := by
        rw [mul_pow, hq2]
        field_simp
    _ ≤ ((128 * bb * B')^2 + 1) * D := by nlinarith

/-- **Trivial bound of a direct slot.** -/
theorem trivial_slot (u : O) (L : Finset (Ideal O)) (β : Ideal O → ℂ) (D : ℝ) (hD : 1 ≤ D)
    (hL : ∀ I ∈ L, I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ 2 * D) (hβ : ∀ I ∈ L, ‖β I‖ ≤ 1) :
    ‖directSlot u L β D‖^2 ≤ 65536 * D := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hcard : (L.card : ℝ) ≤ 128 * (2 * D) :=
    DescentFiberCost.finite_ideal_count_real L (2 * D) (by linarith) (fun I hI => (hL I hI).1)
      (fun I hI => (hL I hI).2)
  have hsum : ‖∑ I ∈ L, β I * CanonicalRowCompletion.idealRowHom u I‖ ≤ 256 * D := by
    calc ‖∑ I ∈ L, β I * CanonicalRowCompletion.idealRowHom u I‖
        ≤ ∑ I ∈ L, ‖β I * CanonicalRowCompletion.idealRowHom u I‖ := norm_sum_le _ _
      _ ≤ ∑ _I ∈ L, (1:ℝ) := Finset.sum_le_sum fun I hI => by
          rw [norm_mul]
          exact (mul_le_mul (hβ I hI) (CanonicalRowCompletion.idealRowHom_norm u I)
            (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
      _ = (L.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ 256 * D := by linarith
  have hs0 : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD0
  have hpre : ‖((Real.sqrt D : ℂ))⁻¹‖ = (Real.sqrt D)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
  have hnorm : ‖directSlot u L β D‖ ≤ (Real.sqrt D)⁻¹ * (256 * D) := by
    unfold directSlot
    rw [norm_mul, hpre]
    exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hs0.le)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hsD : (Real.sqrt D)^2 = D := Real.sq_sqrt hD0.le
  calc ‖directSlot u L β D‖^2 ≤ ((Real.sqrt D)⁻¹ * (256 * D))^2 := hsq
    _ = 65536 * D := by
        rw [mul_pow, inv_pow, hsD]
        field_simp
        ring

/-- **Trivial row count** of the ball. -/
theorem row_count (rows : Finset NonzeroElement) (Z : ℝ) (hZ : 1 ≤ Z)
    (hrows : ∀ u ∈ rows, ‖ConcreteTraceCRT.eisEmbedding u.val‖^2 ≤ Z) :
    (rows.card : ℝ) ≤ 768 * Z := by
  set S : Finset O := rows.map ⟨Subtype.val, Subtype.val_injective⟩ with hS
  have h1 := CenteredExceptionalCount.element_count_le_six_ideal_count S (by
    intro z hz
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hz
    exact u.property)
  have h2 := DescentFiberCost.finite_ideal_count_real (S.image (fun z => Ideal.span {z})) Z hZ
    (by
      intro I hI
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
      obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hz
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact u.property)
    (by
      intro I hI
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hz
      have := hrows u hu
      rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] at this
      exact this)
  have hc : S.card = rows.card := Finset.card_map _
  rw [hc] at h1
  linarith

/-- **Trivial energy** of the inverse marked sum over the ball. -/
theorem trivial_energy (Φ : ℝ → ℂ) (ao bo : ℝ) (hΦs : Function.support Φ ⊆ Icc ao bo)
    (hΦ : Continuous Φ) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ (data : RowData) {ι : Type} [Fintype ι] (L : ι → Finset (Ideal O))
      (ell : ι → ℝ) (β : ι → Ideal O → ℂ) (Z : ℝ), 1 ≤ Z → (∀ i, 0 ≤ ell i) →
      (∀ i, ∀ P ∈ L i, Prime P) → (∀ i, ∀ P ∈ L i, ((P.absNorm : ℝ)/Z^(ell i)) ∈ Icc (1 : ℝ) 2) →
      (∀ i, ∀ P ∈ L i, ‖β i P‖ ≤ 1) → ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      ∀ rows : Finset NonzeroElement,
        (∀ u ∈ rows, ‖ConcreteTraceCRT.eisEmbedding u.val‖^2 ≤ Z) → ∀ θ : ℝ,
        inverseMarkedSum data Φ L ell β rows Z r θ ≤
          C0 * (65536 : ℝ)^(Fintype.card ι) * Z^(2 + ∑ i, ell i) := by
  obtain ⟨Ctp, hCtp, htp⟩ := trivial_polynomial Φ ao bo hΦs hΦ
  refine ⟨768 * Ctp, by positivity, ?_⟩
  intro data ι _ L ell β Z hZ hell hpr hrat hβ r hr0 hr1 rows hrows θ
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hslot : ∀ (u : NonzeroElement) i,
      ‖directSlot u.val (L i) (β i) (Z^(ell i))‖^2 ≤ 65536 * Z^(ell i) := by
    intro u i
    have hD : 1 ≤ Z^(ell i) := Real.one_le_rpow hZ (hell i)
    refine trivial_slot u.val (L i) (β i) (Z^(ell i)) hD (fun P hP => ⟨?_, ?_⟩) (hβ i)
    · exact (hpr i P hP).ne_zero
    · have h2 := (hrat i P hP).2
      have hD0 : 0 < Z^(ell i) := zero_lt_one.trans_le hD
      have := (div_le_iff₀ hD0).mp h2
      linarith
  have hprod : ∀ u : NonzeroElement, ∏ i, ‖directSlot u.val (L i) (β i) (Z^(ell i))‖^2 ≤
      (65536 : ℝ)^(Fintype.card ι) * Z^(∑ i, ell i) := by
    intro u
    calc ∏ i, ‖directSlot u.val (L i) (β i) (Z^(ell i))‖^2 ≤ ∏ i, (65536 * Z^(ell i)) :=
          Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) (fun i _ => hslot u i)
      _ = (65536 : ℝ)^(Fintype.card ι) * Z^(∑ i, ell i) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
            Real.rpow_sum_of_pos hZ0]
  have hrow : ∀ u : NonzeroElement,
      ‖polynomial (data.character u) true (InverseMoment.childLogTest Φ θ) (Z^r) 0 0 *
        (∏ i, directSlot u.val (L i) (β i) (Z^(ell i)))‖^2 ≤
        Ctp * Z * ((65536 : ℝ)^(Fintype.card ι) * Z^(∑ i, ell i)) := by
    intro u
    have hD : 1 ≤ Z^r := Real.one_le_rpow hZ hr0
    have hM : ‖polynomial (data.character u) true (InverseMoment.childLogTest Φ θ) (Z^r) 0 0‖^2 ≤
        Ctp * Z := by
      rw [polynomial_childLogTest _ _ _ _ _ (zero_lt_one.trans_le hD)]
      refine (htp _ true (Z^r) (2*Real.pi*θ) hD).trans ?_
      have : Z^r ≤ Z := by
        calc Z^r ≤ Z^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ hr1
          _ = Z := Real.rpow_one Z
      exact mul_le_mul_of_nonneg_left this hCtp.le
    rw [norm_mul, mul_pow, norm_prod, ← Finset.prod_pow]
    exact mul_le_mul hM (hprod u) (Finset.prod_nonneg fun i _ => sq_nonneg _) (by positivity)
  have hcard := row_count rows Z hZ hrows
  have hZ2 : Z * Z^(∑ i, ell i) * Z = Z^(2 + ∑ i, ell i) := by
    rw [Real.rpow_add hZ0, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    ring
  unfold inverseMarkedSum
  calc ∑ u ∈ rows, ‖polynomial (data.character u) true (InverseMoment.childLogTest Φ θ) (Z^r) 0 0 *
        (∏ i, directSlot u.val (L i) (β i) (Z^(ell i)))‖^2
      ≤ ∑ _u ∈ rows, Ctp * Z * ((65536 : ℝ)^(Fintype.card ι) * Z^(∑ i, ell i)) :=
        Finset.sum_le_sum fun u _ => hrow u
    _ = (rows.card : ℝ) * (Ctp * Z * ((65536 : ℝ)^(Fintype.card ι) * Z^(∑ i, ell i))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (768 * Z) * (Ctp * Z * ((65536 : ℝ)^(Fintype.card ι) * Z^(∑ i, ell i))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 768 * Ctp * (65536 : ℝ)^(Fintype.card ι) * (Z * Z^(∑ i, ell i) * Z) := by ring
    _ = _ := by rw [hZ2]

end
end Qrh.TwoSlot.AnchorZeroLoss.High.Inverse

#print axioms Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.trivial_polynomial
#print axioms Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.trivial_slot
#print axioms Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.row_count
#print axioms Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.trivial_energy
