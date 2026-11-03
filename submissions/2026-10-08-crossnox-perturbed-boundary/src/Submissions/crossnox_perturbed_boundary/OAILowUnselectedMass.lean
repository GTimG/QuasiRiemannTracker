/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAILowUnselectedMass.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAILowSlotScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowUnselectedMass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowRemoteMass

namespace OAI

noncomputable section

open scoped Classical

namespace SevenEighths.ProbePhysical

open CompletedGauss CanonicalQuadraticSieve

local notation "O" => ActualEisensteinCubic.O

lemma canonical_slot_inverse_square_dyadic
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, Supported P.val)
    (amin b Z ell : ℝ) (ha : 0 < amin) (hZ : 1 ≤ Z)
    (hell : 0 ≤ ell)
    (hnorm : ∀ P ∈ T,
      amin * Z ^ ell ≤ (Ideal.absNorm P.val : ℝ) ∧
        (Ideal.absNorm P.val : ℝ) ≤ b * Z ^ ell) :
    (∑ x : canonicalSlotSupport T,
      elementNorm x.val ^ (-2 : ℝ)) ≤
      (128 * max 1 b / amin ^ (2 : ℝ)) * Z ^ (-ell) := by
  let H := max 1 b * Z ^ ell
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hze : 0 < Z ^ ell := Real.rpow_pos_of_pos hz _
  have hH : 1 ≤ H := by
    dsimp [H]
    exact one_le_mul_of_one_le_of_one_le
      (le_max_left _ _) (Real.one_le_rpow hZ hell)
  have hcount : ((canonicalSlotSupport T).card : ℝ) ≤ 128 * H :=
    canonicalSlot_count T hT H hH
      (fun P hP => (hnorm P hP).2.trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hze.le))
  have hterm (x : canonicalSlotSupport T) :
      elementNorm x.val ^ (-2 : ℝ) ≤
        (amin * Z ^ ell) ^ (-2 : ℝ) := by
    obtain ⟨P, rfl⟩ := (canonicalSlotEquiv T hT).surjective x
    rw [canonicalSlotEquiv_norm]
    exact Real.rpow_le_rpow_of_nonpos
      (mul_pos ha hze) (hnorm P.val P.property).1 (by norm_num)
  have hsum : (∑ x : canonicalSlotSupport T,
      elementNorm x.val ^ (-2 : ℝ)) ≤
      ((canonicalSlotSupport T).card : ℝ) *
        (amin * Z ^ ell) ^ (-2 : ℝ) := by
    simpa only [Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun x _ => hterm x)
  apply hsum.trans
  have hcount' := mul_le_mul_of_nonneg_right hcount
    (Real.rpow_nonneg (mul_pos ha hze).le (-2 : ℝ))
  apply hcount'.trans_eq
  dsimp [H]
  have hp : (amin * Z ^ ell) ^ (-2 : ℝ) =
      (amin ^ (2 : ℝ) * (Z ^ ell) ^ (2 : ℝ))⁻¹ := by
    rw [Real.rpow_neg (mul_pos ha hze).le]
    congr 1
    rw [Real.mul_rpow ha.le hze.le]
  rw [hp, Real.rpow_neg hz.le]
  have hpow : (Z ^ ell) ^ (2 : ℝ) = (Z ^ ell) ^ (2 : ℕ) :=
    Real.rpow_natCast _ _
  rw [hpow]
  field_simp

theorem perturbed_lowUnselectedMass_bound
    (K : ℕ) (amin b : ℝ) (ha : 0 < amin)
    (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Z : ℝ), 1 ≤ Z →
      ∀ (T : Fin K → Finset PrimeIdeal)
        (_hT : ∀ i P, P ∈ T i → Supported P.val)
        (_hnorm : ∀ i P, P ∈ T i →
          amin * Z ^ (ell i) ≤ (Ideal.absNorm P.val : ℝ) ∧
          (Ideal.absNorm P.val : ℝ) ≤ b * Z ^ (ell i))
        (J : Finset (Fin K)) (W : Fin K → ℝ → ℂ)
        (Yp : Fin K → ℝ),
        (∀ i x, ‖W i x‖ ≤ 1) →
        (∑ p : LowUnselectedTuple
          (fun i => canonicalSlotSupport (T i)) J,
          ‖lowUnselectedWeight
            (fun i => canonicalSlotSupport (T i)) J W Yp p‖ *
            elementNorm (∏ i : J, (p i).val) ^ (-(1 / 2 : ℝ))) ≤
          C * Z ^ (-lowUnselectedLength ell J) := by
  let D := 128 * max 1 b / amin ^ (2 : ℝ)
  have hD : 0 < D := by dsimp [D]; positivity
  let C := (max 1 D) ^ K
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro Z hZ T hT hnorm J W Yp hW
  simp_rw [lowUnselectedWeight_norm_identity _
    (fun i => canonicalSlotSupport_nonzero _ (hT i))]
  rw [← Fintype.prod_sum (fun (i : J)
    (x : canonicalSlotSupport (T i.val)) =>
      elementNorm x.val ^ (-2 : ℝ) *
        ‖W i.val (elementNorm x.val / Yp i.val)‖)]
  calc
    _ ≤ ∏ i : J, D * Z ^ (-ell i.val) := by
      apply Finset.prod_le_prod₀
        (fun i _ => Finset.sum_nonneg
          (fun x _ => mul_nonneg
            (Real.rpow_nonneg (by unfold elementNorm; positivity) _)
            (norm_nonneg _)))
      intro i _
      calc
        _ ≤ ∑ x : canonicalSlotSupport (T i.val),
            elementNorm x.val ^ (-2 : ℝ) := by
          apply Finset.sum_le_sum
          intro x _
          exact mul_le_of_le_one_right
            (Real.rpow_nonneg (by unfold elementNorm; positivity) _)
            (hW i.val _)
        _ ≤ _ := canonical_slot_inverse_square_dyadic
          (T i.val) (hT i.val) amin b Z (ell i.val)
          ha hZ (hell i.val) (hnorm i.val)
    _ = D ^ J.card * Z ^ (-lowUnselectedLength ell J) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_coe,
        ← Real.rpow_sum_of_pos (lt_of_lt_of_le zero_lt_one hZ)]
      congr 1
      simp only [lowUnselectedLength, Finset.sum_neg_distrib,
        Finset.sum_coe_sort]
    _ ≤ C * Z ^ (-lowUnselectedLength ell J) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp [C]
      exact (pow_le_pow_left₀ (by positivity) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _)
          (by simpa using Finset.card_le_card (Finset.subset_univ J)))

end SevenEighths.ProbePhysical

end

end OAI
