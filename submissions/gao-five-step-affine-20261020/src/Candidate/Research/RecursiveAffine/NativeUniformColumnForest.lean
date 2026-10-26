/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeMetadataColumnForest
import Candidate.Cycle63.Physical.InitialMass.SecondExtraction

set_option autoImplicit false
set_option maxHeartbeats 700000
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonLinearNormalization Cycle63Moment Cycle63InitialMass
open CenteredMomentCommonPairedSource
open Cycle153SourceReturn Cycle153RegionalLow

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
/-- Actual normalized columns are extracted from the native common
retained cost, using its genuine pointwise extraction theorem. The SAME
whole attaining forest and source-weight provenance pass through this
operator unchanged. The residual shell power is exactly 3*eps. -/
theorem actual_uniform_low_columns_returned_forest (b eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀S : Finset alpha, ∀(M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)
      (hH : RayOrthogonality.globalUnits M≤H)
      (Depth : Type)[Fintype Depth](junction : Depth→ℝ)(Base : Depth→Type)
      (base : (d : Depth)→Character→Base d→Character)
      (eta : Character)(Bnorm Tz : ℝ)(root : O), ∀ (s : Input S), s.upper ≤ b →
      ∀ (C R seed : Ideal O), ∀hC : Supported C, seed ∣ C →
      ∀ (Ds : Finset (Ideal O)) (zs : Finset O) (rowWeight : O → ℝ)
        (T Z pad : ℝ), 1 ≤ T → 1 < Z →
      (∀ D ∈ Ds, Squarefree D ∧ T ≤ (D.absNorm : ℝ) ∧ (D.absNorm : ℝ) < 2*T) →
      ∀ (keep : O → Prop) (Phi : 𝓢(ℝ,ℂ)) (rad : ℝ), 0 < rad →
      (∀ z, keep z → 0 ≤ (Phi (‖eisEmbedding z‖^2/rad)).re) →
      (∀ z ∈ zs, 0 ≤ rowWeight z) →
      (∀ z ∈ zs, keep z) →
      (∀ z ∈ zs, rowWeight z ≤ (Phi (‖eisEmbedding z‖^2/rad)).re) →
      (∀ B : actualAllocations s.pools C, commonScalar s C R B ≠ 0 →
        (commonData s C R B).toSource.allowance Z ≤ pad) →
      ∀ (sourceConstant oldPart : ℝ), 0 ≤ sourceConstant → 0 ≤ oldPart →
      ∀ (sourceWeight : PhysicalDaughter s C R Ds → ℝ),
      ∀ (hweight : ∀ d, 0 ≤ sourceWeight d),
      ∀ (Provenance : PhysicalDaughter s C R Ds →
        DepthReturnedFamily M H hH junction Base base eta Z Bnorm Tz root → Prop),
      (∀ d : PhysicalDaughter s C R Ds, commonScalar s C R d.1 ≠ 0 →
        ∃ F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm Tz root,
          Provenance d F ∧ physicalDaughterEnergy s C R Ds keep Phi rad d ≤
            sourceConstant * (oldPart + sourceWeight d * F.value)) →
      ∃ Fout : DepthReturnedFamily M H hH junction Base base eta Z Bnorm Tz root,
        ((Fout = emptyReturnedForest ∧ ∀ d : PhysicalDaughter s C R Ds, commonScalar s C R d.1 = 0) ∨
          ∃ (d : PhysicalDaughter s C R Ds)
            (F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm Tz root),
            commonScalar s C R d.1 ≠ 0 ∧ Provenance d F ∧
            Fout = weightReturnedForest F (sourceWeight d) (hweight d) ∧
            physicalDaughterEnergy s C R Ds keep Phi rad d ≤
              sourceConstant * (oldPart + Fout.value)) ∧
        (∑ D ∈ Ds, ∑ z ∈ zs, rowWeight z * ‖normalizedColumn s C hC R seed D z‖^2) ≤
          K * s.toData.profileFactor * (∏ j, s.M j)^2 *
            (sourceConstant * (oldPart + Fout.value)) * (C.absNorm : ℝ)^(eps-1) *
            (2*T)^(3*eps) * Z^pad := by
  have hs (S : Finset alpha) :=
    actual_low_columns_returned_forest_uniform_metadata (alpha:=S) b eps heps
  choose K hK hb using hs
  let Ksum := 1+∑S : Finset alpha,K S
  have hsum : 0≤∑S : Finset alpha,K S := Finset.sum_nonneg (fun S _=>(hK S).le)
  refine ⟨Ksum,by dsimp only [Ksum];linarith only [hsum],?_⟩
  intro S M _ H hH Depth _ junction Base base eta Bnorm Tz root s hs C R seed hC hseed
    Ds zs rowWeight T Z pad hT hZ hDs keep Phi rad hrad hPhi hnonneg hkeep hw hallow
    sourceConstant oldPart hconstant hold sourceWeight hweight Provenance hsource
  obtain ⟨Fout,htrace,hbound⟩ := hb S M H hH Depth junction Base base eta Bnorm Tz root
    s hs C R seed hC hseed Ds zs rowWeight T Z pad hT hZ hDs keep Phi rad hrad hPhi
    hnonneg hkeep hw hallow sourceConstant oldPart hconstant hold sourceWeight hweight Provenance hsource
  refine ⟨Fout,htrace,hbound.trans ?_⟩
  have hle : K S≤Ksum := by
    have h:=Finset.single_le_sum (fun S _=>(hK S).le) (Finset.mem_univ S)
    dsimp only [Ksum]
    linarith only [h]
  have hsource0 : 0≤ sourceConstant*(oldPart+Fout.value) := by
    exact mul_nonneg hconstant (add_nonneg hold (Fout.value_nonneg (zero_lt_one.trans hZ).le))
  have hPF : 0≤ s.toData.profileFactor := by
    unfold CenteredMomentEligibleEnergy.Data.profileFactor
    positivity
  gcongr

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actual_uniform_low_columns_returned_forest
