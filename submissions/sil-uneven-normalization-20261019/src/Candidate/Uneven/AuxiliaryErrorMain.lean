import Candidate.Cycle63.Physical.FinalErrorCapacity.Capacity
import Candidate.Uneven.AuxiliaryCapacity
import Candidate.Cycle63.Physical.FinalCapacity.Physical
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice
import Candidate.Uneven.AuxiliaryCellCapacity
import Candidate.Uneven.AuxiliaryErrorPaid
import Candidate.Cycle63.Physical.FinalError.Geometry
import Candidate.Cycle63.Physical.FinalError.Chain
import Candidate.Uneven.AuxiliaryGlobalEnvelope
import Candidate.Uneven.AuxiliaryErrorPayment
import Candidate.Cycle63.Physical.FinalError.Payment

/- Original module: Candidate.Uneven.AuxiliaryExtractedCapacity. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.AuxiliaryCapacity
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
    plainLogs L a Z X₁ X₂+(6*Sil.Uneven.AuxiliarySource.kappa)*remainingLogs L a Z f.P ≤
      Real.logb Z (preVolume s.toData)-Real.logb Z (rawReduction B₁.val s.P)-
        (k:ℝ)*Real.logb Z (Q.absNorm:ℝ)-Real.logb Z (rawReduction B₂.val e.P)+
        (6*Sil.Uneven.AuxiliarySource.kappa-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂) := by
  let first := child s C₁ R₁ B₁ χ t
  let e := twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v
  let f := commonData e C₂ R₂ B₂
  have hp₁ : ∀i,1 ≤ first.P i := fun i => hP i.val
  have hpe : ∀i,1 ≤ e.P i := fun i => hp₁ i.val
  have hpf : ∀i,1 ≤ f.P i := fun i => hpe i.val
  have hb := supported_residual_capacity f L a Z hZ hpf X₁ X₂ hX₁ hX₂ hprod z hne
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
    (6*Sil.Uneven.AuxiliarySource.kappa-1)*(∑i,Real.logb Z (f.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂) at hb
  norm_num [Sil.Uneven.AuxiliarySource.kappa] at *
  linarith

end
end OAI.SevenEighths.AuxiliaryCapacity
end

/- Original module: Candidate.Uneven.AuxiliaryErrorCapacity. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.AuxiliaryCapacity
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63FinalErrorCapacity
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
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Both actual second-label allocations share the same generator/unit
 cancellation. Prime extraction pays its exact removed width. -/
theorem actual_error_source_capacity (N : ℕ) (b : ℝ) (hb : 1  ≤  b)
    (s : Input ι) (hcard : Fintype.card ι  ≤  N) (hs : s.upper  ≤  b)
    (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (hf₁ : frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P ≠ 0)
    (χ : Character) (t : ℝ) (Q : Ideal O) (hQ : Q ≠ 0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C₁ R₁ B₁ χ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C₁ R₁ B₁ χ t).pools (Q^k))
    (υ : Character) (v : ℝ) (C₂ D₂ H R₂ : Ideal O) (hH : H=C₂ ∨ H=D₂)
    (B₂ : actualAllocations (twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v).pools H)
    (hf₂ : let e := twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v
      frozenCoefficient B₂.val H R₂ e.ν e.W e.P ≠ 0)
    (D₁ : Ideal O) (hD₁ : D₁ ≠ 0) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (hCD₂ : primeSupport C₂ = primeSupport D₂) (U : Finset (CommonIndex C₂ D₂))
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices B₂.val) ⊕ Fin 2)))
    (Z M amp omega wo : ℝ) (hZ : 1 < Z) (hM : 0 < M) (hP : ∀i,1  ≤  s.P i)
    (hwo : wo  ≤  (k:ℝ)*Real.logb Z (Q.absNorm:ℝ))
    (hz : Sil.Uneven.AuxiliarySource.widthLo*M  ≤  ∑i,Real.logb Z (s.P i) ∧
      (∑i,Real.logb Z (s.P i))  ≤  Sil.Uneven.AuxiliarySource.widthHi*M)
    (haffine : length Z s.X₁+length Z s.X₂+
      Sil.Uneven.AuxiliarySource.lambda*(∑i,Real.logb Z (s.P i))  ≤  Sil.Uneven.AuxiliarySource.B*M)
    (second : Bool) (z : O)
    (hne : Cycle63.Physical.sourcePositiveRow
      (commonData (twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v) H R₂ B₂).toSource second L a z ≠ 0) :
    let e := twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v
    let f := commonData e H R₂ B₂
    let w := (k:ℝ)*Real.logb Z (Q.absNorm:ℝ)
    let cell := Sil.Uneven.AuxiliarySource.widthCellUpper ((∑i,Real.logb Z (s.P i))/M)
    length Z (Cycle63Moment.LowBranch.finalPlain f second L a 0)+
      length Z (Cycle63Moment.LowBranch.finalPlain f second L a 1)+
        (6*Sil.Uneven.AuxiliarySource.kappa)*remainingLogs L a Z f.P-
      errorNominal M Z amp omega w wo C₁ D₁ C₂ D₂ U  ≤ 
        M*Sil.Uneven.AuxiliarySource.gap cell+3*amp+(w-wo)+omega+supportPadding N b s.b₁ s.b₂ Z := by
  let first := child s C₁ R₁ B₁ χ t
  let e := twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v
  let f := commonData e H R₂ B₂
  let X := Cycle63.Physical.sourcePlainScales f.toSource second
  have hx₁ := Cycle63Moment.LowBranch.source_plain_positive f second 0
  have hx₂ := Cycle63Moment.LowBranch.source_plain_positive f second 1
  have hprod : X 0*X 1=f.X₁*f.X₂ := by
    cases second
    · rfl
    · exact f.same_product
  have htotal := extracted_supported_capacity s C₁ R₁ B₁ χ t Q hQ k hslot Bp υ v
    H R₂ B₂ L a Z hZ hP (X 0) (X 1) hx₁ hx₂ hprod z hne
  have he : length Z (Cycle63Moment.LowBranch.finalPlain f second L a 0)+
      length Z (Cycle63Moment.LowBranch.finalPlain f second L a 1) =
        plainLogs L a Z (X 0) (X 1) := by
    change Real.logb Z (max 1 (CenteredMomentRetainedProfile.clippedScale (rawScale L a (X 0) 0)))+
      Real.logb Z (max 1 (CenteredMomentRetainedProfile.clippedScale (rawScale L a (X 1) 1))) = _
    rw [max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _),
      max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _)]
    rfl
  have hc₁ := Real.logb_nonneg hZ (norm_ge_one C₁ (allocation_ne s C₁ B₁))
  have hd₁ := Real.logb_nonneg hZ (norm_ge_one D₁ hD₁)
  have hw : 0  ≤  (k:ℝ)*Real.logb Z (Q.absNorm:ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.logb_nonneg hZ (norm_ge_one Q hQ))
  have hmax := extraction_max_loss _ _ _ wo hc₁ hd₁ hw hwo
  have hshift : Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))-
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)  ≤  Real.logb Z (H.absNorm:ℝ) := by
    rcases hH with hh|hh
    · rw [hh]
      exact actual_common_shift_le C₂ D₂ hC₂ hD₂ hCD₂ U Z hZ
    · rw [hh]
      exact actual_common_shift_le_right C₂ D₂ hC₂ hD₂ hCD₂ U Z hZ
  have hr₁ := common_reduction_log_lower N b hb s hcard hs C₁ R₁ B₁ hf₁ Z hZ
  have hce : Fintype.card (CenteredMomentCommonProfile.liveIndices Bp.val)  ≤  N :=
    (live_card_le Bp.val).trans ((live_card_le B₁.val).trans hcard)
  have hr₂ := common_reduction_log_lower N b hb e hce hs H R₂ B₂ hf₂ Z hZ
  have hcell := original_affine_capacity s Z M hZ hM hz haffine
  dsimp only at htotal hcell ⊢
  rw [he]
  change Real.logb Z (preVolume s.toData)+(6*Sil.Uneven.AuxiliarySource.kappa-1)*(∑i,Real.logb Z (s.P i))  ≤  _ at hcell
  unfold errorNominal supportPadding
  linarith


end
end OAI.SevenEighths.AuxiliaryCapacity
end

/- Original module: Candidate.Uneven.AuxiliaryErrorGeometry. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.AuxiliaryError
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63FinalError
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCompleteCommon CenteredMomentSecondHeightFamily ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonRadialData CenteredMomentCommonRawScale
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open Cycle63FinalNatural Cycle63FinalCapacity Cycle63FinalErrorCapacity
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem error_source_capacity {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b J : ℝ}
    (g : Geometry s q Z Mrow amp omega ξ b J (Fintype.card α)) (hb : 1 ≤ b)
    (hs : s.upper ≤ b) (hZ : 1 < Z) (hM : 0 < Mrow) (hP : ∀j,1 ≤ s.P j)
    (hz : Sil.Uneven.AuxiliarySource.widthLo*Mrow ≤ ∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j)) ≤ Sil.Uneven.AuxiliarySource.widthHi*Mrow)
    (haff : CenteredMomentEnergyBands.length Z s.X₁+CenteredMomentEnergyBands.length Z s.X₂+
      Sil.Uneven.AuxiliarySource.lambda*(∑j,Real.logb Z (s.P j)) ≤ Sil.Uneven.AuxiliarySource.B*Mrow)
    (η : Character) (v : ℝ) (second : Bool) (L : Ideal O)
    (a : CenteredMomentDivisorAllocation.Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))) (z : O)
    (hne : Cycle63.Physical.sourcePositiveRow (q.final η v).toSource second L a z≠0) :
    let cell := Sil.Uneven.AuxiliarySource.widthCellUpper ((∑j,Real.logb Z (s.P j))/Mrow)
    CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L a 0)+
      CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L a 1)+
        (6*Sil.Uneven.AuxiliarySource.kappa)*CenteredMomentAllocatedChildCapacity.remainingLogs L a Z (q.final η v).P-g.nominal  ≤ 
      Mrow*Sil.Uneven.AuxiliarySource.gap cell+3*amp+(errorRemoval q.p Z q.k-errorMoving q.p Z q.k)+omega+
        supportPadding (Fintype.card α) b s.b₁ s.b₂ Z := by
  exact AuxiliaryCapacity.actual_error_source_capacity (Fintype.card α) b hb s le_rfl hs q.C₁ q.R₁ q.B₁
    g.first_nonzero q.η₁ q.t₁ (Ideal.span {q.p}) (Ideal.span_singleton_eq_bot.not.mpr q.hp)
    q.k q.coprime q.Bp η v g.C g.D q.E₂ q.R₂ g.label q.B₂ g.second_nonzero
    g.D₁ g.hD₁.1 g.hC g.hD g.heq g.U L a Z Mrow amp omega (errorMoving q.p Z q.k)
    hZ hM hP (actual_prime_widths q.p q.hp Z hZ q.k q.hk).2.2 hz haff second z hne

end
end OAI.SevenEighths.AuxiliaryError
end

/- Original module: Candidate.Uneven.AuxiliaryErrorMain. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.AuxiliaryError
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63FinalError
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale CenteredMomentAllocatedChildCapacity
open CenteredMomentEnergyAllocatedProfiles
open CenteredMomentAmplificationErrorEnergy
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity Cycle63FinalErrorCapacity
open Cycle63Physical.ExtractedBranches
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The genuine extracted retained positive energy, with both common
 allocations and prime extraction paid in the original ambient family.
 Profiles and all moment constants precede the moving physical labels. -/
theorem actual_paid_error_uniform
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0 < A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (hap : 0 < ap) (hap' : ap ≤ 1/4) (hbp : 1 ≤ bp)
    (hBmask : 0 ≤ Bmask) (hL : 0 ≤ L) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hloss : 0 < loss) (hmargin : 0 < margin) (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ Sil.Uneven.AuxiliarySource.kappa)
    (ηseed : Character) (bs J εwidth εpad Mmin : ℝ)
    (hbs : 1 ≤ bs) (hJ : 0 < J) (hew : 0 < εwidth) (hep : 0 < εpad) (hmin : 0 < Mmin) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀_hQM : Q ≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀ ≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0 < Cg ∧ ∀ᶠZ : ℝ in atTop,1 < Z ∧
    ∀(hZ : 1 < Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh : ℝ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper ≤ bs → s.b₁=bp → s.b₂=bp →
      (∀j,0 ≤ w j) → (∀j,w j ≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      0 ≤ mesh → (∀j,w j ≤ mesh) → (∀j,lo ≤ σ j) → (∀j,σ j ≤ hi) →
      0 ≤ height → (∀j,|freq j| ≤ height) →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j ≤ Z^L) →
    ∀(Mrow omega ξ : ℝ),Mmin ≤ Mrow → 0 ≤ omega → 0 ≤ ξ → Mrow+εwidth*Mrow+ξ/2 ≤ Mcap →
      (Sil.Uneven.AuxiliarySource.widthLo*Mrow ≤ ∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j)) ≤ Sil.Uneven.AuxiliarySource.widthHi*Mrow) →
      length Z s.X₁+length Z s.X₂+Sil.Uneven.AuxiliarySource.lambda*(∑j,Real.logb Z (s.P j)) ≤ Sil.Uneven.AuxiliarySource.B*Mrow →
    ∀q : Chain s,
    let cell := Sil.Uneven.AuxiliarySource.widthCellUpper ((∑j,Real.logb Z (s.P j))/Mrow)
    let amp := Mrow*Sil.Uneven.AuxiliarySource.amp cell
    q.k=1 ∨ q.k=6 ∨ q.k=7 → 3*amp/4 ≤ Real.logb Z (normValue q.p) →
    ∀g : Geometry s q Z Mrow amp omega ξ bs J (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ) ≤ Z^Bmask)
      (second : Bool)(L₂ : Ideal O)
      (alloc : Allocation L₂ (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))),
    let st := retainedState Z Bmask hZ (g.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.radius g.C g.D g.U
    let src := q.final (g.τ χ) v
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀p : Profiles ap bp,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    finalPositiveEnergy src second L₂ alloc st.radial.keep st.radial.profile st.radial.scale ≤ 
      Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*(1+|v|+height)^degree*
        Z^(g.nominal+δwidth+errorRemoval q.p Z q.k-Mrow*branchReserve q.k+
          εold+loss*(Fintype.card α:ℝ)+padding/6+Sil.Uneven.AuxiliarySource.kappa*mesh) ∧
    localErrorCost q.p (q.k-1)*Z^(-errorRemoval q.p Z q.k+errorMoving q.p Z q.k)*
      finalPositiveEnergy src second L₂ alloc st.radial.keep st.radial.profile st.radial.scale ≤ 
      Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*(1+|v|+height)^degree*
        Z^(g.nominal+δwidth-Mrow*branchReserve q.k+εold+loss*(Fintype.card α:ℝ)+padding/6+Sil.Uneven.AuxiliarySource.kappa*mesh) := by
  have hapret : 0 < ap/max 1 bp := div_pos hap (by positivity)
  have hapret' : ap/max 1 bp ≤ 1/4 := (div_le_self hap.le (le_max_left _ _)).trans hap'
  obtain ⟨degree,S,hmain⟩ := AuxiliaryGlobal.actual_global_main_uniform (α:=α) M H hH W A B (ap/max 1 bp) bp
    2 Bmask L lo hi Mcap εold loss margin hA hWs hW hB hapret hapret' hbp (by norm_num)
    hBmask hMcap hεold hloss hmargin hbeta hκbeta
  obtain ⟨Sp,Cp,hCp,hcontrol⟩ := Cycle63FinalProfiles.clipped_pair_control ap bp hap S
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cg,hCg,hbound⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cg*Cp^2,by positivity,?_⟩
  filter_upwards [hbound,Cycle63FinalRadius.fixed_final_width_loss_uniform (fun _:Unit=>ηseed)
    (Fintype.card α) bs J εwidth Mmin (zero_lt_one.trans_le hbs) hJ hew hmin,
    support_padding_eventually_mass (Fintype.card α) bs bp bp εpad Mmin (zero_lt_one.trans_le hbs) hep hmin]
    with Z hZ hwidthLoss hpadLoss
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh hm hsη hsupper hsb₁ hsb₂ hw hwL hmesh hwm
    hσlo hσhi hheight hfreq hOrig Mrow omega ξ hMmin hω hξ hMcap' hz haff q
    cell amp hk hprime g χ hP hPN second L₂ alloc st src δwidth padding p hp₁ hp₂
  dsimp only
  suffices henergy : finalPositiveEnergy src second L₂ alloc st.radial.keep st.radial.profile st.radial.scale ≤ 
      (Cg*Cp^2)*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*(1+|v|+height)^degree*
        Z^(g.nominal+δwidth+errorRemoval q.p Z q.k-Mrow*branchReserve q.k+
          εold+loss*(Fintype.card α:ℝ)+padding/6+Sil.Uneven.AuxiliarySource.kappa*mesh) by
    refine ⟨henergy,?_⟩
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    apply normalize_error_energy q.p q.hp Z hZone q.k hk _ _ _ (by positivity)
    have hExp : (g.nominal+δwidth-Mrow*branchReserve q.k+εold+
        loss*(Fintype.card α:ℝ)+padding/6+Sil.Uneven.AuxiliarySource.kappa*mesh)+errorRemoval q.p Z q.k =
      g.nominal+δwidth+errorRemoval q.p Z q.k-Mrow*branchReserve q.k+
        εold+loss*(Fintype.card α:ℝ)+padding/6+Sil.Uneven.AuxiliarySource.kappa*mesh := by ring
    simpa only [hExp] using henergy
  have hM : 0 < Mrow := hmin.trans_le hMmin
  have hcell := (Sil.Uneven.AuxiliarySource.widthCellUpper_bounds
    (show (∑j,Real.logb Z (s.P j))/Mrow ∈ Set.Icc Sil.Uneven.AuxiliarySource.widthLo Sil.Uneven.AuxiliarySource.widthHi from
      ⟨(le_div_iff₀ hM).mpr hz.1,(div_le_iff₀ hM).mpr hz.2⟩)).1
  have hamp : 0≤ amp := by
    have ha : 0< Sil.Uneven.AuxiliarySource.amp cell :=
      lt_of_lt_of_le (by norm_num : (0:ℝ)<1/100000) (Sil.Uneven.AuxiliarySource.source_guards hcell).2.1
    exact (mul_pos hM ha).le
  have hshift := CenteredMomentSecondActualWidth.actual_common_log_ge_unit g.C g.D g.hC g.U Z hZone
  have hnominal : g.nominal ≤ Mrow := by
    have hm0 := le_max_right (Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (g.D₁.absNorm:ℝ)+
      2*errorRemoval q.p Z q.k-errorMoving q.p Z q.k) (0:ℝ)
    unfold Geometry.nominal errorNominal
    linarith
  have hwidth : st.width-g.nominal ≤ δwidth := by
    have ht := error_state_width g Bmask hZone (zero_lt_one.trans_le hbs) hJ χ (internalQ Q η₀) hP hPN
    have hl := hwidthLoss.2 () Mrow hMmin
    rw [←hsη] at hl
    dsimp [δwidth]; linarith
  have hδ : 0 ≤ δwidth := by dsimp [δwidth]; positivity
  have hpadding : 0 ≤ padding := by dsimp [padding]; positivity
  have hs : st.width ≤ Mcap := by dsimp [δwidth] at hwidth; linarith
  by_cases live : ∃z,Cycle63.Physical.sourcePositiveRow src.toSource second L₂ alloc z≠0
  · obtain ⟨z,hzrow⟩ := live
    let X := Cycle63.Physical.sourcePlainScales src.toSource second
    let U := fun j : Fin 2=> X j/(Ideal.absNorm (selectedPlain L₂ alloc j):ℝ)
    have hU : ∀j,0 < U j := fun j=> div_pos (source_plain_positive src second j)
      (zero_lt_one.trans_le (CenteredMomentAmplificationChildSourceCaps.norm_ge_one _
        (CenteredMomentDivisorExtraction.selectedDivisor_ne_zero L₂ Finset.univ alloc (Sum.inr j))))
    have hsurv := allocated_survives src L₂ alloc z (X 0) (X 1)
      (source_plain_positive src second 0) (source_plain_positive src second 1) hzrow
    have hret : ∀j,1 ≤ U j*bp := by
      intro j; fin_cases j
      · change 1 ≤ _/ _*bp
        have hs0 := hsurv.1
        change 1 ≤ _/ _*s.b₁ at hs0
        rw [hsb₁] at hs0
        exact hs0
      · change 1 ≤ _/ _*bp
        have hs1 := hsurv.2
        change 1 ≤ _/ _*s.b₂ at hs1
        rw [hsb₂] at hs1
        exact hs1
    let pret := retainedPair ap bp hap p U hU 0
    have hprofile (j : Fin 2) := Cycle63FinalProfiles.actual_clipped_pair ap bp hap p U hU hret j
    have hp0 : dilated s.W₁ (clipDilation (U 0))=pret.profile 0 := by rw [hp₁]; exact (hprofile 0).symm
    have hp1 : dilated s.W₂ (clipDilation (U 1))=pret.profile 1 := by rw [hp₂]; exact (hprofile 1).symm
    have hXcap₁ := final_plain_cap s q (g.τ χ) v Z L hZone hL hOrig second L₂ alloc 0
    have hXcap₂ := final_plain_cap s q (g.τ χ) v Z L hZone hL hOrig second L₂ alloc 1
    have htotal := error_source_capacity g hbs hsupper hZone hM
      (fun j=> by rw [hm.scale j]; exact Real.one_le_rpow hZone.le (hw j)) hz haff (g.τ χ) v second L₂ alloc z hzrow
    rw [original_slot_sum s q (g.τ χ) v Z hZone w hm.scale L₂ alloc] at htotal
    have hpadd := hpadLoss.2 Mrow hMmin
    rw [hsb₁,hsb₂] at htotal
    have hcap : length Z (finalPlain src second L₂ alloc 0)+length Z (finalPlain src second L₂ alloc 1)+
        (6*Sil.Uneven.AuxiliarySource.kappa)*(∑j∈q.indices L₂ alloc,w j)-g.nominal ≤ Mrow*Sil.Uneven.AuxiliarySource.gap cell+3*amp+
        ((q.k:ℝ)*Real.logb Z (normValue q.p)-(if q.k=6 then 0 else Real.logb Z (normValue q.p)))+padding := by
      change _ ≤ _ at htotal
      dsimp [padding]; unfold errorRemoval errorMoving at htotal; linarith
    have hpaid := paid_branch_exponent q.k hk hcell hM.le hwidth hδ hprime hpadding hcap
    have he := hZ.2 (q.indices L₂ alloc) θ w σ freq v height mesh hw hwL hmesh (fun j _=> hwm j)
      hσlo hσhi hheight hfreq st rfl hs pret _ _
      (zero_lt_one.trans_le (clippedScale_ge_one _)) (zero_lt_one.trans_le (clippedScale_ge_one _)) hXcap₁ hXcap₂
    have hcoef := hcontrol p U hU
    have hpn := Profiles.control_nonneg p Sp
    have hpretn := Profiles.control_nonneg pret S
    have hsq : (pret.control S)^2 ≤ Cp^2*(p.control Sp)^2 := by nlinarith
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    rw [original_positive_energy M H hH s η₀ θ w σ freq W B Z Bmask hZone hm q (g.τ χ) v
      (internalQ Q η₀) hP hPN g.radius g.C g.D g.U second L₂ alloc,hp0,hp1]
    apply he.trans
    have hpow := Real.rpow_le_rpow_of_exponent_le hZone.le
      (show st.width+εold+loss*(Fintype.card α:ℝ)+(1/6)*max
        (length Z (finalPlain src second L₂ alloc 0)+length Z (finalPlain src second L₂ alloc 1)+
          (6*Sil.Uneven.AuxiliarySource.kappa)*(∑j∈q.indices L₂ alloc,w j)-st.width) 0+Sil.Uneven.AuxiliarySource.kappa*mesh  ≤ 
          g.nominal+δwidth+errorRemoval q.p Z q.k-Mrow*branchReserve q.k+
            εold+loss*(Fintype.card α:ℝ)+padding/6+Sil.Uneven.AuxiliarySource.kappa*mesh by
        unfold errorRemoval; linarith)
    calc
      _  ≤  Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(Cp^2*(p.control Sp)^2)*
        (1+|v|+height)^degree*Z^_ := mul_le_mul
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity)) (by positivity))
          hpow (Real.rpow_nonneg (zero_le_one.trans hZone.le) _) (by positivity)
      _ = _ := by ring
  · have hzrow : ∀z,Cycle63.Physical.sourcePositiveRow src.toSource second L₂ alloc z=0 := by
      simpa only [not_exists,not_not] using live
    rw [no_surviving_row_energy_zero src second L₂ alloc _ _ _ hzrow]
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    positivity

end
end OAI.SevenEighths.AuxiliaryError
end
