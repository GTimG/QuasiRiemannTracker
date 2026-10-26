/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeCommonForest

set_option autoImplicit false
set_option maxHeartbeats 700000
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonLinearNormalization Cycle63Moment Cycle63InitialMass
open Cycle153SourceReturn Cycle153RegionalLow

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
/-- The actual common Cauchy and reciprocal-residual operator constructs
one whole attaining returned forest. The strict-depth source estimate is
applied to each literal native physical daughter; after that estimate,
the SAME daughter, residual allocation, orientation, and all terminal
depths are selected together. The native reciprocal and profile factors
are unchanged. This does not manufacture a proof of the strict-depth
source estimate supplied by the induction hypothesis. -/
theorem actual_common_low_returned_forest_uniform_metadata (b eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀(M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)
      (hH : RayOrthogonality.globalUnits M≤H)
      (Depth : Type)[Fintype Depth](junction : Depth→ℝ)(Base : Depth→Type)
      (base : (d : Depth)→Character→Base d→Character)
      (eta : Character)(Bnorm Tz : ℝ)(root : O), ∀ (s : Input alpha), s.upper ≤ b →
      ∀ (C R : Ideal O), C ≠ 0 →
      ∀ (Ds : Finset (Ideal O)) (zs : Finset O) (rowWeight : O → ℝ)
        (T Z pad : ℝ), 1 ≤ T → 1 < Z →
      (∀ D ∈ Ds, Squarefree D ∧ T ≤ (D.absNorm : ℝ) ∧ (D.absNorm : ℝ) < 2*T) →
      ∀ (keep : O → Prop) (Phi : 𝓢(ℝ,ℂ)) (rad : ℝ), 0 < rad →
      (∀ z, keep z → 0 ≤ (Phi (‖eisEmbedding z‖^2/rad)).re) →
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
        (∑ D ∈ Ds, ∑ z ∈ zs, rowWeight z * commonRetainedCost s C R D z) ≤
          K * s.toData.profileFactor * (∏ j, s.M j)^2 *
            (sourceConstant * (oldPart + Fout.value)) * (C.absNorm : ℝ)^(eps-1) *
            (2*T)^(2*eps) * Z^pad := by
  obtain ⟨K,hK,hcommon⟩ := actual_common_low_selected_return (α:=alpha) b eps heps
  refine ⟨K,hK,?_⟩
  intro M _ H hH Depth _ junction Base base eta Bnorm Tz root s hb C R hC Ds zs rowWeight T Z pad hT hZ hDs keep Phi rad hrad hPhi hkeep hw hallow
    sourceConstant oldPart hconstant hold sourceWeight hweight Provenance hsource
  let SourceReturn := fun d ret => ∃ F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm Tz root,
    Provenance d F ∧ ret = F.value
  obtain ⟨Ret,hRet,hselected,hbound⟩ := hcommon s hb C R hC Ds zs rowWeight T Z pad hT hZ hDs
    keep Phi rad hrad hPhi hkeep hw hallow sourceConstant oldPart hconstant hold sourceWeight hweight
    SourceReturn (by
      intro d hd
      obtain ⟨F,hF,hE⟩ := hsource d hd
      exact ⟨F.value,F.value_nonneg (zero_lt_one.trans hZ).le,⟨F,hF,rfl⟩,hE⟩)
  rcases hselected with ⟨hzero,hall⟩ | ⟨d,ret,hd,hr,⟨F,hF,heq⟩,hRetEq,hE⟩
  · refine ⟨emptyReturnedForest,Or.inl ⟨rfl,hall⟩,?_⟩
    simpa only [emptyReturnedForest_value,hzero] using hbound
  · let Fout := weightReturnedForest F (sourceWeight d) (hweight d)
    have hvalue : Fout.value = Ret := by
      dsimp only [Fout]
      rw [weightReturnedForest_value]
      rw [heq] at hRetEq
      exact hRetEq.symm
    refine ⟨Fout,Or.inr ⟨d,F,hd,hF,rfl,?_⟩,?_⟩
    · simpa only [hvalue] using hE
    · simpa only [hvalue] using hbound

end
end OAI.SevenEighths.Cycle153ActualColumn

#print axioms OAI.SevenEighths.Cycle153ActualColumn.actual_common_low_returned_forest_uniform_metadata
