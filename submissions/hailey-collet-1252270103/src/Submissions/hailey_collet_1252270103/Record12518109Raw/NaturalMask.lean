/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Cycle61.Moment.JointSourceCount
import Submissions.hailey_collet_1252270103.Cycle61.Moment.ActualJointDictionary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CenteredMomentNaturalRowSource CenteredExceptionalProfile
open CenteredMomentFixedRowMask CenteredMomentDetectorEnergyInitialState
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon Cycle61Moment
open CenteredMomentCommonSectors UniqueFactorizationMonoid
open ActualEisensteinCubic
local notation "O" => HeckeFamily.O
local notation "ps" => CompletedGauss.primeSupport

/-- The raw row itself already forces a zero at every prime dividing it. -/
theorem natural_ideal_nonzero_coprime {η : Character} {w : O}
    (F : NaturalRow η w) (I : Ideal O) (h : idealCoeff F.character I ≠ 0) :
    IsCoprime I (Ideal.span {w}) := by
  have hI : I ≠ 0 := by intro hi; exact h (by rw [hi, idealCoeff_zero])
  let n := idealGenerator I
  have hn : n ≠ 0 := idealGenerator_ne_zero I hI
  have hs : Ideal.span {n} = I := span_idealGenerator I
  have he : rowTwist (elementHom η) fixedBadMask 1 w n ≠ 0 := by
    rw [← F.element, ← idealCoeff_span _ hn, hs]
    exact h
  have hc := (rowTwist_nonzero_coprime η fixedBadMask 1 w n
    (dvd_mul_right _ _) (dvd_mul_left _ _) he).2.of_mul_right_right
  simpa only [hs] using (Ideal.isCoprime_span_singleton_iff n w).mpr hc

/-- A mask may be replaced only when its extra support lies in the literal
row. This is an equality of coefficients, including their natural zeros. -/
theorem natural_mask_of_support {η : Character} {w : O}
    (F : NaturalRow η w) (hw : w ≠ 0) (A B : Ideal O)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : ps A ⊆ ps (Ideal.span {w} * B)) (hBA : ps B ⊆ ps A)
    (I : Ideal O) : idealCoeff (excluded F.character A) I =
      idealCoeff (excluded F.character B) I := by
  rw [excluded_ideal _ _ hA, excluded_ideal _ _ hB]
  by_cases hv : idealCoeff F.character I = 0
  · simp only [hv, ite_self]
  have hc := natural_ideal_nonzero_coprime F I hv
  have he : IsCoprime I A ↔ IsCoprime I B := by
    constructor
    · intro h
      exact (coprime_support_iff I B hB).mp (fun P hp =>
        (coprime_support_iff I A hA).mpr h P (hBA hp))
    · intro h
      exact (coprime_support_iff I A hA).mp (fun P hp =>
        (coprime_support_iff I (Ideal.span {w} * B)
          (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hw) hB)).mpr
            (hc.mul_right h) P (hAB hp))
  rw [he]

/-- Natural-row fixed-inducing membership is independent of its chosen
character presentation. This retains the primitive centered sector. -/
theorem natural_fixed_inducing_iff {η : Character} {w : O}
    (F : NaturalRow η w) (Q : Ideal O) :
    FixedInducingRow η Q fixedBadMask 1 w ↔
      ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
        Q ≤ ψ.modulus ∧ InducedBy F.character ψ := by
  constructor
  · rintro ⟨χ, ψ, hp, hi, hQ, he⟩
    refine ⟨ψ, hp, hQ, CenteredMomentHeckeVolume.inducedBy_of_elementCoeff_eq
      χ F.character ψ ?_ hi⟩
    intro n
    exact (F.element n).trans (by simpa only [one_mul] using (he n).symm)
  · rintro ⟨ψ, hp, hQ, hi⟩
    exact ⟨F.character, ψ, hp, hi, hQ, by simpa only [one_mul] using F.element⟩

/-- Equality of the actual masked dictionaries transports both the ordinary
and fixed-inducing sectors. No conductor comparison or exceptional estimate
is substituted for this equivalence. -/
theorem natural_fixed_inducing_of_masked_ideal_eq
    {η τ : Character} {w z : O} (F : NaturalRow η w) (G : NaturalRow τ z)
    (A B : Ideal O) (hA : A ≠ 0) (hB : B ≠ 0)
    (he : ∀ I : Ideal O, idealCoeff (excluded F.character A) I =
      idealCoeff (excluded G.character B) I) (Q : Ideal O) :
    FixedInducingRow η Q fixedBadMask 1 w ↔
      FixedInducingRow τ Q fixedBadMask 1 z := by
  have hzF : elementCoeff (excluded F.character A) 0 = 0 := by
    rw [excluded_element _ F.element_zero _ hA, F.element_zero]
    split_ifs <;> rfl
  have hzG : elementCoeff (excluded G.character B) 0 = 0 := by
    rw [excluded_element _ G.element_zero _ hB, G.element_zero]
    split_ifs <;> rfl
  have hel (n : O) : elementCoeff (excluded F.character A) n =
      elementCoeff (excluded G.character B) n := by
    by_cases hn : n = 0
    · rw [hn, hzF, hzG]
    · rw [← idealCoeff_span _ hn, ← idealCoeff_span _ hn, he]
  rw [natural_fixed_inducing_iff F Q, natural_fixed_inducing_iff G Q]
  have hf := HeckeMaskDescent.fixed_inducing_mask_iff F.character
    (excluded F.character A) (idealGenerator A) (idealGenerator_ne_zero A hA)
    (excluded_element_generator F.character F.element_zero A hA) Q
  have hg := HeckeMaskDescent.fixed_inducing_mask_iff G.character
    (excluded G.character B) (idealGenerator B) (idealGenerator_ne_zero B hB)
    (excluded_element_generator G.character G.element_zero B hB) Q
  apply hf.symm.trans
  apply Iff.trans ?_ hg
  constructor
  · rintro ⟨ψ, hp, hQ, hi⟩
    exact ⟨ψ, hp, hQ, CenteredMomentHeckeVolume.inducedBy_of_elementCoeff_eq
      _ _ ψ (fun n => (hel n).symm) hi⟩
  · rintro ⟨ψ, hp, hQ, hi⟩
    exact ⟨ψ, hp, hQ, CenteredMomentHeckeVolume.inducedBy_of_elementCoeff_eq
      _ _ ψ hel hi⟩

theorem natural_initialKeep_of_masked_ideal_eq
    {η τ : Character} {w z : O} (F : NaturalRow η w) (G : NaturalRow τ z)
    (hw : w ≠ 0) (hz : z ≠ 0)
    (A B : Ideal O) (hA : A ≠ 0) (hB : B ≠ 0)
    (he : ∀ I : Ideal O, idealCoeff (excluded F.character A) I =
      idealCoeff (excluded G.character B) I) (Q : Ideal O) :
    initialKeep η Q w ↔ z ≠ 0 ∧ ¬FixedInducingRow τ Q fixedBadMask 1 z := by
  have hm := fixedInducingRow_mul_mask_iff η Q fixedBadMask (idealGenerator 1) 1 w
    fixedBadMask_ne_zero (idealGenerator_ne_zero 1 one_ne_zero) one_ne_zero hw
    (dvd_mul_right _ _) (dvd_mul_left _ _)
  change (w ≠ 0 ∧ ¬FixedInducingRow η Q (fixedBadMask * idealGenerator 1) 1 w) ↔ _
  rw [hm, natural_fixed_inducing_of_masked_ideal_eq F G A B hA hB he Q]
  exact ⟨fun h => ⟨hz, h.2⟩, fun h => ⟨hw, h.2⟩⟩

theorem first_missing_dvd (left : Bool) (l : FirstSourceLabel)
    (hC : l.1.1 ≠ 0) : firstSourceMissing left l ∣ l.1.1 := by
  have h := (subsetGenerator_span_dvd l.1.1 l.1.2
    (firstMissingCommon l.1.1 l.1.2 l.2.val left)).trans (commonPart_dvd _ _ hC)
  simpa only [primeSubsetGenerator, span_idealGenerator, firstSourceMissing,
    firstMissingRadical] using h

/-- The literal joint mask reduces to one common fixed factor and the first
missing radical. Both first orientations and both second columns are included.
No first or second common ideal is charged again after this reduction. -/
theorem actual_joint_common_mask (left second : Bool) (u₀ : O)
    (unit : FirstSourceLabel → O) (l : NonzeroJointSourceLabel left u₀ unit)
    (hC₁ : Supported l.val.1.1.1) (hD₁ : Supported l.val.1.1.2)
    (hs₁ : ps l.val.1.1.1 = ps l.val.1.1.2)
    (hC₂ : Supported l.val.2.1.1) (hD₂ : Supported l.val.2.1.2)
    (hs₂ : ps l.val.2.1.1 = ps l.val.2.1.2)
    (η : Character) (F : NaturalRow η (nonzeroJointSourceRow l).val)
    (R : Ideal O) (hR : R ≠ 0) (I : Ideal O) :
    let e := primeSubsetGenerator
      (fun P : CommonIndex l.val.1.1.1 l.val.1.1.2 => P.val) l.val.1.2.val
    let A := Ideal.span {e * activeConductor l.val.1.1.1 l.val.1.1.2}
    let C := if left then l.val.1.1.1 else l.val.1.1.2
    let E := if second then l.val.2.1.2 else l.val.2.1.1
    idealCoeff (excluded F.character (R * (A * (C * E)))) I =
      idealCoeff (excluded F.character (R * firstSourceMissing left l.val.1)) I := by
  intro e A C E
  have hMdiv := first_missing_dvd left l.val.1 hC₁.1
  have hM : firstSourceMissing left l.val.1 ≠ 0 := by
    intro h
    rw [h] at hMdiv
    exact hC₁.1 (zero_dvd_iff.mp hMdiv)
  have hC : C ≠ 0 := by cases left <;> first | exact hC₁.1 | exact hD₁.1
  have hE : E ≠ 0 := by cases second <;> first | exact hC₂.1 | exact hD₂.1
  have hA : A ≠ 0 := by
    dsimp only [A]
    rw [← Ideal.span_singleton_mul_span_singleton]
    exact mul_ne_zero (subsetGenerator_supported _ _ hC₁ _).1
      (activeConductor_supported _ _ hC₁).1
  rw [excluded_ideal _ _ (mul_ne_zero hR (mul_ne_zero hA (mul_ne_zero hC hE))),
    excluded_ideal _ _ (mul_ne_zero hR hM)]
  by_cases hv : idealCoeff F.character I = 0
  · simp only [hv, ite_self]
  have hw := (nonzeroJointSourceRow l).property
  have hcraw := natural_ideal_nonzero_coprime F I hv
  have hfirst := first_source_literal_support left l.val.1 hC₁ hs₁
    (nonzeroJointSourceRow l).val hw
    ⟨u₀ * unit l.val.1, _, _, _, rfl⟩
  have hmiff : IsCoprime I l.val.1.1.1 ↔ IsCoprime I (firstSourceMissing left l.val.1) := by
    constructor
    · intro h
      exact h.of_isCoprime_of_dvd_right hMdiv
    · intro h
      exact (coprime_support_iff I _ hC₁.1).mp (fun P hp =>
        (coprime_support_iff I _
          (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hw) hM)).mpr
            (hcraw.mul_right h) P (hfirst hp))
  have hsecond := Cycle61.Physical.common_support_in_row _ _ hC₂ hs₂
    (nonzeroJointSourceRow l).val hw (joint_source_second_generator_dvd left u₀ unit l.val)
  have hc₂ : IsCoprime I l.val.2.1.1 :=
    (coprime_support_iff I _ hC₂.1).mp (fun P hp =>
      (coprime_support_iff I _ (Ideal.span_singleton_eq_bot.not.mpr hw)).mpr hcraw P (hsecond hp))
  have hcE : IsCoprime I E := by
    cases second
    · exact hc₂
    · exact (coprime_support_iff I _ hD₂.1).mp (by
        rw [← hs₂]
        exact (coprime_support_iff I _ hC₂.1).mpr hc₂)
  have hcC : IsCoprime I C ↔ IsCoprime I l.val.1.1.1 := by
    cases left
    · change IsCoprime I l.val.1.1.2 ↔ IsCoprime I l.val.1.1.1
      rw [← coprime_support_iff I _ hD₁.1, ← coprime_support_iff I _ hC₁.1, hs₁]
    · rfl
  have hcA (h : IsCoprime I l.val.1.1.1) : IsCoprime I A := by
    dsimp only [A]
    rw [← Ideal.span_singleton_mul_span_singleton]
    exact (h.of_isCoprime_of_dvd_right
      ((subsetGenerator_span_dvd _ _ _).trans (commonPart_dvd _ _ hC₁.1))).mul_right
      (h.of_isCoprime_of_dvd_right
        ((activeConductor_span_dvd _ _).trans (commonPart_dvd _ _ hC₁.1)))
  have hred : (IsCoprime I A ∧ IsCoprime I l.val.1.1.1) ↔
      IsCoprime I (firstSourceMissing left l.val.1) :=
    ⟨fun h => hmiff.mp h.2, fun h => ⟨hcA (hmiff.mpr h), hmiff.mpr h⟩⟩
  simp only [IsCoprime.mul_right_iff, hcE, and_true, hcC, hred]

end
end OAI.SevenEighths.Record12518109Raw

#print axioms OAI.SevenEighths.Record12518109Raw.natural_ideal_nonzero_coprime
#print axioms OAI.SevenEighths.Record12518109Raw.natural_mask_of_support
#print axioms OAI.SevenEighths.Record12518109Raw.natural_fixed_inducing_of_masked_ideal_eq
#print axioms OAI.SevenEighths.Record12518109Raw.natural_initialKeep_of_masked_ideal_eq
#print axioms OAI.SevenEighths.Record12518109Raw.first_missing_dvd
#print axioms OAI.SevenEighths.Record12518109Raw.actual_joint_common_mask
