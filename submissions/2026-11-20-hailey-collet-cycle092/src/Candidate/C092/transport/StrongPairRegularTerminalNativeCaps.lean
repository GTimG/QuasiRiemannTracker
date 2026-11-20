/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The native fourth source cap and strictly smaller marked quota are chosen
from the genuine conductor radius and scalar fee, before physical arrays. -/
import Candidate.C092.transport.StrongPairOrdinaryNearForward
import Candidate.C092.transport.NativeFourthEffective

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot ConcretePrimeRowBridge CenteredMomentEnergyBands
open QRH.Cycle092.MediumReplace.Source
open QRH.Record12518109Source QRH.Record12518109Existence
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source

/-- Below unit radius retain n/d. Above unit radius use n, so the native
fourth credit is exactly d times the source's mean quota. -/
def terminalNativeCap (n d : ℝ) : ℝ := if d ≤ 1 then n/d else n

theorem terminal_native_source_parameters {n y d fee : ℝ}
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hyn : y ≤ n)
    (hn : n ≤ sourceRatio*y) (hd : (98/100:ℝ) ≤ d) (hf : 0 < fee) :
    ∃ quota : ℝ,
      0 ≤ terminalNativeCap n d ∧ terminalNativeCap n d < 1/2 ∧
      0 < quota ∧ quota < 3/20 ∧ quota < (1-2*terminalNativeCap n d)/2 ∧
      2*NativeFourthEffective.credit n d-d*quota ≤ fee/4 ∧
      ∀ {U X : ℝ},0 < U → length U X ≤ n → length (U^d) X ≤ terminalNativeCap n d := by
  have hdp : 0 < d := by linarith
  have hylo : (369/1000:ℝ) ≤ y := by simpa only [sourceY0] using hy0
  have hnlo : (369/1000:ℝ) ≤ n := hylo.trans hyn
  have hnhi : n ≤ (5589/12500:ℝ) := by
    have h := hn.trans (mul_le_mul_of_nonneg_left hy1 (by norm_num [sourceRatio]))
    norm_num [sourceRatio,sourceY] at h ⊢
    exact h
  have hn0 : 0 ≤ n := by linarith
  have hN0 : 0 ≤ terminalNativeCap n d := by
    unfold terminalNativeCap;split <;> positivity
  have hNn : n ≤ terminalNativeCap n d := by
    unfold terminalNativeCap
    split
    · exact (le_div_iff₀ hdp).mpr (by nlinarith)
    · exact le_rfl
  have hN : terminalNativeCap n d < 1/2 := by
    unfold terminalNativeCap
    split
    · exact (div_lt_iff₀ hdp).mpr (by linarith)
    · linarith
  let mean := (1-2*terminalNativeCap n d)/2
  have hm0 : 0 < mean := by dsimp [mean];linarith
  have hm1 : mean < 3/20 := by dsimp [mean];linarith
  have hcredit : 2*NativeFourthEffective.credit n d = d*mean := by
    dsimp only [mean,NativeFourthEffective.credit,terminalNativeCap]
    split
    · field_simp <;> ring
    · ring
  let gap := min (mean/2) (fee/(4*d))
  have hg0 : 0 < gap := lt_min (by positivity) (by positivity)
  have hg1 : gap ≤ mean/2 := min_le_left _ _
  have hg2 : gap ≤ fee/(4*d) := min_le_right _ _
  refine ⟨mean-gap,hN0,hN,by linarith,by linarith,by dsimp [mean] at *;linarith,?_,?_⟩
  · rw [hcredit]
    have h := mul_le_mul_of_nonneg_left hg2 hdp.le
    have heq : d*(fee/(4*d))=fee/4 := by field_simp <;> ring
    rw [heq] at h
    nlinarith only [h]
  · intro U X hU hX
    rw [length_rpow_base U X d hU]
    have hX' := div_le_div_of_nonneg_right hX hdp.le
    refine hX'.trans ?_
    unfold terminalNativeCap
    split
    · exact le_rfl
    · exact (div_le_iff₀ hdp).mpr (by nlinarith)

#print axioms terminal_native_source_parameters
end
end QRH.Cycle092.StrongPair
