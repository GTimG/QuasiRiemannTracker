/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeMetadataCommonForest
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
theorem actual_low_columns_returned_forest_uniform_metadata (b eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀(M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)
      (hH : RayOrthogonality.globalUnits M≤H)
      (Depth : Type)[Fintype Depth](junction : Depth→ℝ)(Base : Depth→Type)
      (base : (d : Depth)→Character→Base d→Character)
      (eta : Character)(Bnorm Tz : ℝ)(root : O), ∀ (s : Input alpha), s.upper ≤ b →
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
  obtain ⟨Kc,hKc,hpoint⟩ := actual_common_column_extraction (ι:=alpha) eps heps
  obtain ⟨K,hK,hcommon⟩ := actual_common_low_returned_forest_uniform_metadata (alpha:=alpha) b eps heps
  refine ⟨Kc*K,mul_pos hKc hK,?_⟩
  intro M _ H hH Depth _ junction Base base eta Bnorm Tz root s hb C R seed hC hseed Ds zs rowWeight T Z pad hT hZ hDs keep Phi rad hrad hPhi hnonneg hkeep hw hallow
    sourceConstant oldPart hconstant hold sourceWeight hweight Provenance hsource
  obtain ⟨Fout,hselected,hbound⟩ := hcommon M H hH Depth junction Base base eta Bnorm Tz root s hb C R hC.1 Ds zs rowWeight T Z pad hT hZ hDs
    keep Phi rad hrad hPhi hkeep hw hallow sourceConstant oldPart hconstant hold sourceWeight hweight
    Provenance hsource
  refine ⟨Fout,hselected,?_⟩
  have hT0 : 0 < 2*T := by linarith only [hT]
  have hmajor : (∑D∈Ds,∑z∈zs,rowWeight z*‖normalizedColumn s C hC R seed D z‖^2) ≤
      Kc*(2*T)^eps*(∑D∈Ds,∑z∈zs,rowWeight z*commonRetainedCost s C R D z) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_le_sum fun D hD => Finset.sum_le_sum fun z hz => ?_
    have hp := mul_le_mul_of_nonneg_left
      (hpoint s C hC R seed D hseed (hDs D hD).1 z) (hnonneg z hz)
    apply hp.trans
    have hd := Real.rpow_le_rpow (Nat.cast_nonneg D.absNorm) (hDs D hD).2.2.le heps.le
    have hc := common_retained_cost_nonneg s C R D z
    have hbnd := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hKc.le)
      (mul_nonneg (hnonneg z hz) hc)
    convert hbnd using 1 <;> ring
  apply hmajor.trans
  apply (mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ Kc*(2*T)^eps)).trans_eq
  rw [show 3*eps=eps+2*eps by ring,Real.rpow_add hT0 eps (2*eps)]
  ring

end
end OAI.SevenEighths.Cycle153ActualColumn

#print axioms OAI.SevenEighths.Cycle153ActualColumn.actual_low_columns_returned_forest_uniform_metadata
