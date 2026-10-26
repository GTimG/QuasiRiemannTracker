/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeCanonicalChain

set_option autoImplicit false
set_option maxHeartbeats 220000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153CanonicalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve ConcreteTraceCRT LocalMoment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentFirstAmplificationChoice CenteredMomentFixedRowMask CenteredExceptionalProfile
open CenteredMomentCommonPairedSource
open CenteredMomentCommonLinearNormalization CenteredMomentCommonHeightEnvelope
open CenteredMomentSecondHeightFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSourceLiveColumn
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentSectorLocalization CenteredMomentInductionEnergy
open Cycle63Moment Cycle63Moment.LowBranch Cycle63FinalLow Cycle63FinalNatural Cycle63InitialMass
open Cycle153LowPhysical
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The physical common operator and the actual LOW detector use the
literal same radial profile, scale and inducing-row exclusion. Neither a
new radial weight nor an energy majorant is introduced by the bridge. -/
theorem canonical_retained_radial (Z Bmask : ℝ) (hZ : 1<Z)
    (tau : Character) (Q P : Ideal O) (hP : P≠0)
    (hPN : (P.absNorm:ℝ)≤Z^Bmask) (datum : SecondInputDatum α) :
    let st:=retainedState Z Bmask hZ tau Q P hP hPN
      datum.radius datum.C datum.D datum.inactive
    st.radial.profile=ballProfile ∧
    st.radial.scale=retainedScale datum.radius datum.C datum.D datum.inactive ∧
    ∀z,st.radial.keep z ↔ z≠0 ∧ ¬FixedInducingRow tau Q fixedBadMask 1 z := by
  intro st
  refine ⟨rfl,rfl,?_⟩
  intro z
  exact retainedState_keep Z Bmask hZ tau Q P hP hPN _ _ _ _ z

/-- The canonical ordinary one-shell residual cost is exactly the SAME
actual-chain normalized column sum. The caller's physical coefficient
(in particular firstMass/childVolume, K and the common normalizer) stays
outside its original sum and is not divided into a returned family. -/
theorem ordinary_residual_shell_eq_actual_chain {Label : Type} [Fintype Label]
    (s : Input α) (ch : Label→Chain s)
    {Z Mrow amp omega xi b : ℝ} {N : ℕ}
    (g : ∀r,LiveMainGeometry s (ch r) Z Mrow amp omega xi b N)
    (datum : Label→SecondInputDatum α) (second : Bool)
    (frame : ∀r,CanonicalSourceFrame s (ch r) (g r) (datum r) second)
    (hE : ∀r,Supported (ch r).E₂)
    (χ₀ : Label→RayFourExpansion.RayCharacter) (Q : Ideal O) (m : O)
    (coefficient : Label→ℝ) (ray : Label→RayFourExpansion.RayCharacter)
    (height : Label→ℝ) (zs : Label→Finset O) (Ds : Finset (Ideal O)) :
    (∑r,∑D∈Ds,nativeResidualCost second (fun r=>ordinarySecondDatum (datum r) (χ₀ r) Q m)
      coefficient ray height zs (fun _ _=>1) r D) =
    ∑r,∑D∈Ds,coefficient r*∑z∈zs r,
      ‖normalizedColumn (withHeight (ch r).first ((g r).datum.τ (ray r)) (height r))
        (ch r).E₂ (hE r) (ch r).R₂ (datum r).seed D z‖^2 := by
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro D hD
  unfold nativeResidualCost
  simp only [one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  rw [actual_ordinary_column_eq_chain (frame r) (hE r) (χ₀ r) Q m (ray r) (height r) D z]

end
end OAI.SevenEighths.Cycle153CanonicalLow
#print axioms OAI.SevenEighths.Cycle153CanonicalLow.canonical_retained_radial
#print axioms OAI.SevenEighths.Cycle153CanonicalLow.ordinary_residual_shell_eq_actual_chain
