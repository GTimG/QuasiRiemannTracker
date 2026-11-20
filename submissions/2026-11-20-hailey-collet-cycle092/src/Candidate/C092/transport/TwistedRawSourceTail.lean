/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Independently colored source mass and the authentic discarded-frequency
   bound. Geometry and profile budgets are those of the original source. -/
import Candidate.C092.transport.TwistedRawSourceZero

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawSource
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice
open QRH.SilDensitySplit.CubeFree.FP MixedOriginalNormCap MixedOriginalTail
local notation "Id" => Ideal HeckeFamily.O
local instance (priority := 2000) sumTailDecEq {κ κ₂ : Type*} :
    DecidableEq (κ ⊕ κ₂) := Classical.decEq _

/-- Same original profile/pool mass budget for the colored coefficient. -/
theorem sourceColumn_mass {ι : Type*} [Fintype ι] {a b : ℝ}
    (s : MixedPrincipalPair.Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (η₁ η₂ : Character) (seed : Id) :
    (∑ I ∈ MixedPrincipalWindow.sourceColumns s,
      ‖sourceColumn s ha (idealCoeff η₁) (idealCoeff η₂) seed I‖) ≤ massCap s := by
  have hm := finiteColumnCoefficient_mass
    (Fintype.piFinset (MixedPrincipalAllocations.tuplePools s))
    (fun v => MixedOriginalSecondZero.originalTuple s ha seed v *
      ordinaryColor (idealCoeff η₁) (idealCoeff η₂) v)
  calc
    _ ≤ ∑ v ∈ Fintype.piFinset (MixedPrincipalAllocations.tuplePools s),
        ‖MixedOriginalSecondZero.originalTuple s ha seed v *
          ordinaryColor (idealCoeff η₁) (idealCoeff η₂) v‖ := hm
    _ ≤ ∑ _v ∈ Fintype.piFinset (MixedPrincipalAllocations.tuplePools s), profileCap s := by
      apply Finset.sum_le_sum
      intro v hv
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (ordinaryColor_norm_le_one η₁ η₂ v)).trans
        (MixedOriginalSecondZero.original_tuple_norm s ha seed v)
    _ = profileCap s * ((Fintype.piFinset (MixedPrincipalAllocations.tuplePools s)).card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ massCap s := mul_le_mul_of_nonneg_left (source_pool_card s hb) (profileCap_nonneg s)

/-- The genuine localized discarded term, for the independently colored source,
    follows from the arbitrary-coefficient Poisson dictionary. -/
theorem source_discarded_localized (Adec : ℕ) :
    ∃ (control : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ {ι : Type*} [Fintype ι] {a b : ℝ}
      (s : MixedPrincipalPair.Source ι a b) (ha : 0 < a), 0 ≤ b →
    ∀ (η₁ η₂ : Character) (seed : Id) (τ : Character)
      (t K W X H Tsec Z Csec ξ : ℝ),
      0 < K → 0 < W → 0 < X → 1 < Z → 1 ≤ Csec →
      sourceNormCap s.P b s.T s.d ≤ Real.exp H * X →
      X^2/(16*K*W^4) ≤ Tsec →
      2*H/Real.log Z + Real.log (4*Csec)/Real.log Z < ξ/4 →
      ‖MixedPoissonLocalization.localizedDensity Finset.univ
        (sourceGenerator (MixedPrincipalWindow.sourceColumns s))
        (sourceGenerator_supported (MixedPrincipalWindow.sourceColumns s))
        (fun I => sourceColumn s ha (idealCoeff η₁) (idealCoeff η₂) seed I * heightCoeff τ t I)
        K W (discardedWeight (frequencyRadius Tsec Z ξ))‖ ≤
        massCap s^2 * (16*K*W^4) * (Real.exp H*X)^2 *
          (C * (control.sup (schwartzSeminormFamily ℝ ℝ ℂ)) ballProfile) /
          (min 1 (kernelReference Tsec H)^2 * (1+Z^(ξ/4))^Adec) / W := by
  obtain ⟨control, C, hC, hc⟩ := MixedLocalizedDictionary.source_discarded_bound Adec
  refine ⟨control, C, hC, ?_⟩
  intro ι _ a b s ha hb η₁ η₂ seed τ t K W X H Tsec Z Csec ξ hK hW hX hZ hCsec hcap hT hξ
  have hh := hc τ t (MixedPrincipalWindow.sourceColumns s)
    (sourceColumn s ha (idealCoeff η₁) (idealCoeff η₂) seed)
    K W X H Tsec Z Csec ξ hK hW hX hZ hCsec
    (fun I _ hi => (sourceColumn_cap s ha _ _ seed I hi).2.trans hcap) hT hξ
  refine hh.trans ?_
  have hm := sourceColumn_mass s ha hb η₁ η₂ seed
  have hmass : 0 ≤ ∑ I ∈ MixedPrincipalWindow.sourceColumns s,
      ‖sourceColumn s ha (idealCoeff η₁) (idealCoeff η₂) seed I‖ := by positivity
  have hctl : 0 ≤ (control.sup (schwartzSeminormFamily ℝ ℝ ℂ)) ballProfile := apply_nonneg _ _
  gcongr

#print axioms sourceColumn_mass
#print axioms source_discarded_localized
end
end QRH.Cycle092.TwistedRawSource
