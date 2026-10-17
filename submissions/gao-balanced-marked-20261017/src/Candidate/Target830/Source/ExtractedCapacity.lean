import Candidate.Cycle63.Physical.FinalErrorCapacity.Capacity
import Candidate.Target830.Source.Capacity
import Candidate.Cycle63.Physical.FinalCapacity.Physical
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Target830.Source.ErrorCapacity
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAllocatedChildCapacity CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle
open CenteredMomentDivisorExtraction CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentSourceLiveColumn CenteredMomentAllocatedNaturalSource
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
open CompletedGauss CanonicalQuadraticSieve CenteredMomentEnergyBands
open CenteredMomentCanonicalFirst Cycle63FinalCapacity
open Cycle63FinalErrorCapacity
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Extraction contributes its exact prime power, rather than a third
 common-allocation support loss. -/
theorem extracted_supported_capacity (s : Input ι) (C₁ R₁ : Ideal O)
    (B₁ : actualAllocations s.pools C₁) (χ : Character) (t : ℝ)
    (Q : Ideal O) (hQ : Q ≠ 0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C₁ R₁ B₁ χ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C₁ R₁ B₁ χ t).pools (Q^k))
    (υ : Character) (v : ℝ) (C₂ R₂ : Ideal O)
    (B₂ : actualAllocations (twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v).pools C₂)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices B₂.val) ⊕ Fin 2)))
    (Z : ℝ) (hZ : 1 < Z) (hP : ∀i,1 ≤ s.P i)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hprod : X₁*X₂=(commonData (twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v)
      C₂ R₂ B₂).X₁*(commonData (twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v) C₂ R₂ B₂).X₂)
    (z : O) (hne : let f := commonData (twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v) C₂ R₂ B₂
      allocatedPositiveRow f.η f.m f.A z f.t f.slots f.coefficient f.P L a
        f.W₁ f.W₂ X₁ X₂ ≠ 0) :
    let e := twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v
    let f := commonData e C₂ R₂ B₂
    plainLogs L a Z X₁ X₂+(6*kappa0)*remainingLogs L a Z f.P ≤
      Real.logb Z (preVolume s.toData)-Real.logb Z (rawReduction B₁.val s.P)-
        (k:ℝ)*Real.logb Z (Q.absNorm:ℝ)-Real.logb Z (rawReduction B₂.val e.P)+
        (6*kappa0-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂) := by
  let first := child s C₁ R₁ B₁ χ t
  let e := twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v
  let f := commonData e C₂ R₂ B₂
  have hp₁ : ∀i,1 ≤ first.P i := fun i => hP i.val
  have hpe : ∀i,1 ≤ e.P i := fun i => hp₁ i.val
  have hpf : ∀i,1 ≤ f.P i := fun i => hpe i.val
  have hb := Capacity.supported_residual_capacity f L a Z hZ hpf X₁ X₂ hX₁ hX₂ hprod z hne
  have hv : Real.logb Z (preVolume f) = Real.logb Z (preVolume s.toData)-
      Real.logb Z (rawReduction B₁.val s.P)-(k:ℝ)*Real.logb Z (Q.absNorm:ℝ)-
      Real.logb Z (rawReduction B₂.val e.P) :=
    extracted_final_volume_log s C₁ R₁ B₁ χ t Q hQ k hslot Bp υ v C₂ R₂ B₂ Z
  have hl₁ := common_slot_logs_le s C₁ B₁ Z hZ hP
  have hlp := common_slot_logs_le first (Q^k) Bp Z hZ hp₁
  have hl₂ := common_slot_logs_le e C₂ B₂ Z hZ hpe
  change (∑i,Real.logb Z (first.P i)) ≤ ∑i,Real.logb Z (s.P i) at hl₁
  change (∑i,Real.logb Z (e.P i)) ≤ ∑i,Real.logb Z (first.P i) at hlp
  change (∑i,Real.logb Z (f.P i)) ≤ ∑i,Real.logb Z (e.P i) at hl₂
  rw [hv] at hb
  change _ ≤ _ at hb ⊢
  change _ ≤ Real.logb Z (preVolume s.toData)-Real.logb Z (rawReduction B₁.val s.P)-
    (k:ℝ)*Real.logb Z (Q.absNorm:ℝ)-Real.logb Z (rawReduction B₂.val e.P)+
    (6*kappa0-1)*(∑i,Real.logb Z (f.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂) at hb
  norm_num [kappa0] at *
  linarith

end
end OAI.SevenEighths.Target830.Source.ErrorCapacity
#print axioms OAI.SevenEighths.Target830.Source.ErrorCapacity.extracted_supported_capacity
