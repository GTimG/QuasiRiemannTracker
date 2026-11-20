/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Colored discarded tails with arbitrary saving. The numerical order choice
   is reused verbatim from the native generic volume inequality. -/
import Candidate.C092.transport.TwistedRawSourceTail

set_option autoImplicit false
namespace QRH.Cycle092.TwistedRawSource
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentSupportedTailAggregate
open QRH.SilDensitySplit.CubeFree.FP MixedOriginalNormCap MixedOriginalTail
local notation "Id" => Ideal HeckeFamily.O

/-- Arbitrary saving for the actual colored physical discarded energy, uniform
    in both ordinary characters, under the original polynomial geometry. -/
theorem source_tail_arbitrary_saving (B ξ saving : ℝ) (hB : 0 ≤ B) (hξ : 0 < ξ) :
    ∃ (control : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ {ι : Type*} [Fintype ι] {a b : ℝ} (s : MixedPrincipalPair.Source ι a b)
      (ha : 0 < a), 0 ≤ b →
    ∀ (η₁ η₂ : Character) (seed : Id) (τ : Character) (t K W X Tsec : ℝ),
      0 < K → 0 < W → 0 < X → poolCap s ≤ Z^B → sourceNormCap s.P b s.T s.d ≤ X →
      X ≤ Z^B → K ≤ Z^B → W ≤ Z^B → W⁻¹ ≤ Z^B → Tsec ≤ Z^B →
      X^2/(16*K*W^4) ≤ Tsec →
      ‖secondDiscardedEnergy τ t (MixedPrincipalWindow.sourceColumns s)
        (sourceColumn s ha (idealCoeff η₁) (idealCoeff η₂) seed)
        ballProfile (16*K*W^4) Tsec Z ξ‖ ≤
        W * (C * profileCap s^2 *
          (control.sup (schwartzSeminormFamily ℝ ℝ ℂ)) ballProfile * Z^(-saving)) := by
  obtain ⟨Adec, horder⟩ := MixedOriginalTailPower.choose_fourth_tail_order B ξ saving hB hξ
  obtain ⟨control, C, hC, hc⟩ := source_discarded_localized Adec
  refine ⟨control, 64*C, by positivity, ?_⟩
  filter_upwards [CenteredMomentSourceInputTailUniform.eventually_tail_threshold 0 ξ hξ] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro ι _ a b s ha hb η₁ η₂ seed τ t K W X Tsec hK hW hX hp hcap hXc hKc hWc hWic hTc hscale
  have hT : 0 < Tsec := (div_pos (sq_pos_of_pos hX) (by positivity)).trans_le hscale
  have hnum := horder Z (poolCap s) K W X Tsec hZ.1.le (poolCap_nonneg s)
    hK hW hX hT hp hKc hWc hXc hTc hWic
  have hh := hc s ha hb η₁ η₂ seed τ t K W X 0 Tsec Z 1 ξ hK hW hX hZ.1
    le_rfl (by simpa using hcap) hscale (by simpa using hZ.2)
  simp only [Real.exp_zero, one_mul] at hh
  let ctl : ℝ := (control.sup (schwartzSeminormFamily ℝ ℝ ℂ)) ballProfile
  have hctl : 0 ≤ ctl := apply_nonneg _ _
  have hbound :
      ‖MixedPoissonLocalization.localizedDensity Finset.univ
        (sourceGenerator (MixedPrincipalWindow.sourceColumns s))
        (sourceGenerator_supported (MixedPrincipalWindow.sourceColumns s))
        (fun I => sourceColumn s ha (idealCoeff η₁) (idealCoeff η₂) seed I * heightCoeff τ t I)
        K W (discardedWeight (frequencyRadius Tsec Z ξ))‖ ≤
        (64*C)*profileCap s^2*ctl*Z^(-saving) := by
    refine hh.trans ?_
    calc
      _ = (C*profileCap s^2*ctl) *
        ((poolCap s)^2 * (16*K*W^4) * X^2 *
          (min 1 (kernelReference Tsec 0)^2)⁻¹ *
          ((1+Z^(ξ/4))^Adec)⁻¹ / W) := by
        unfold massCap
        dsimp only [ctl]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ (C*profileCap s^2*ctl)*(64*Z^(-saving)) :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
      _ = _ := by ring
  rw [MixedLocalizedDictionary.source_discarded τ t _ _ K W Tsec Z ξ hW,
    norm_div, Complex.norm_real, Real.norm_of_nonneg hW.le] at hbound
  exact (div_le_iff₀ hW).mp hbound |>.trans_eq (by dsimp only [ctl]; ring)

#print axioms source_tail_arbitrary_saving
end
end QRH.Cycle092.TwistedRawSource
