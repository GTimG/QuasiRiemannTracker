/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
Two-character row adaptation of Sil's common-profile separation.
The original one-column Fourier/profile lemmas and majorants are reused unchanged. -/
import Candidate.C092.transport.GroupedPairProfileSeparation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.GroupedPair
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff FourierTransform
open MeasureTheory OAI OAI.SevenEighths
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentFiniteProfileExceptional
open QRH.Cycle092.OrdinaryColumn
open QRH.SilDensitySplit.CubeFree.Packet
open ProfileSeparation (dilate commonPair commonProfile scale pairCoeff cellCoeff pairMajorant pairWeight
  scale_pos commonPair_profile_zero commonPair_profile_one rowTwistedBound)
local notation "O" => ActualEisensteinCubic.O

open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open QRH.Record12518109Source QRH.Record12518109Existence

/-- The unchanged two spectral masses cost finitely many of the original
profile seminorms. Only the four fixed Fourier cells are counted. -/
theorem majorant_masses_control (J : ℕ) :
    ∃ S : Finset (ℕ×ℕ),∃ K : ℝ,0 < K ∧
    ∀ (p₀ p₁ : 𝓢(ℝ,ℂ))
      (hs₀ : Function.support (p₀:ℝ→ℂ) ⊆ Set.Icc (1/4) (9/4))
      (hs₁ : Function.support (p₁:ℝ→ℂ) ⊆ Set.Icc (1/4) (9/4)),
      ((∑ e:Fin 2×Fin 2,∫τ:ℝ×ℝ,1*pairMajorant p₀ p₁ hs₀ hs₁ e τ)*
       (∑ e:Fin 2×Fin 2,∫τ:ℝ×ℝ,1*pairMajorant p₀ p₁ hs₀ hs₁ e τ*pairWeight J τ))  ≤ 
      K*(sourceControl S p₀*sourceControl S p₁)^2 := by
  obtain ⟨S₀,K₀,hK₀,h₀⟩:=ProfileSeparation.pairMajorant_mass_control 0
  obtain ⟨SJ,KJ,hKJ,hJ⟩:=ProfileSeparation.pairMajorant_mass_control J
  let S:=S₀∪SJ
  let K:=16*K₀*KJ
  refine ⟨S,K,by dsimp [K]; positivity,?_⟩
  intro p₀ p₁ hs₀ hs₁
  let A:=sourceControl S p₀*sourceControl S p₁
  have hA : 0 ≤ A:=mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hctl (R : Finset (ℕ×ℕ)) (hR : R ⊆ S) :
      R.sup (schwartzSeminormFamily ℝ ℝ ℂ) p₀*R.sup (schwartzSeminormFamily ℝ ℝ ℂ) p₁ ≤ A:=by
    exact mul_le_mul
      (CenteredMomentEnergyReferenceProfileBudget.control_mono hR p₀)
      (CenteredMomentEnergyReferenceProfileBudget.control_mono hR p₁)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hz : (∑ e:Fin 2×Fin 2,∫τ:ℝ×ℝ,1*pairMajorant p₀ p₁ hs₀ hs₁ e τ) ≤ 4*K₀*A:=by
    calc
      _  ≤  ∑ e:Fin 2×Fin 2,K₀*A := by
        apply Finset.sum_le_sum
        intro e he
        have h:=(h₀ p₀ p₁ hs₀ hs₁ e).trans
          (mul_le_mul_of_nonneg_left (hctl S₀ Finset.subset_union_left) hK₀.le)
        simpa only [ProfileSeparation.pairWeight_zero,mul_one,one_mul] using h
      _ = _:=by simp; ring
  have hj : (∑ e:Fin 2×Fin 2,∫τ:ℝ×ℝ,1*pairMajorant p₀ p₁ hs₀ hs₁ e τ*pairWeight J τ) ≤ 4*KJ*A:=by
    calc
      _  ≤  ∑ e:Fin 2×Fin 2,KJ*A := by
        apply Finset.sum_le_sum
        intro e he
        have h:=(hJ p₀ p₁ hs₀ hs₁ e).trans
          (mul_le_mul_of_nonneg_left (hctl SJ Finset.subset_union_right) hKJ.le)
        simpa only [one_mul] using h
      _ = _:=by simp; ring
  have hj0 : 0 ≤ ∑ e:Fin 2×Fin 2,∫τ:ℝ×ℝ,1*pairMajorant p₀ p₁ hs₀ hs₁ e τ*pairWeight J τ:=
    Finset.sum_nonneg (fun e _=>integral_nonneg (fun τ=>by
      exact mul_nonneg (by simpa using ProfileSeparation.pairMajorant_nonneg p₀ p₁ hs₀ hs₁ e τ)
        (ProfileSeparation.pairWeight_nonneg J τ)))
  exact (mul_le_mul hz hj hj0 (by positivity)).trans_eq (by dsimp [K,A];ring)

#print axioms majorant_masses_control
end
end QRH.Cycle092.GroupedPair
