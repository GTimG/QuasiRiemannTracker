/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual colored allocation and selected-assignment masses for H.5. Native
Sil bounds are used only for nonnegative coefficient majorants. -/
import Candidate.C092.transport.RawPairDiagonalBudgetAverageMass
import Candidate.C092.transport.RawPairDiagonalBudgetRetained
import Candidate.C092.transport.PairedRetainedBudgetAverage
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderDiag9
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QRH.Cycle092.RawPairDiagonalBudget
noncomputable section
local instance (priority := 2000) diagSubtypeDecEqAverageLedger {κ : Type*} {p : κ→Prop} : DecidableEq (Subtype p) := Classical.decEq _
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentAddedZeroUniform
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstLiveSource MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.Concrete QRH.SilDensitySplit.CubeFree.Second.ConcreteDiagAssembly
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type} [Fintype ι] {a b : ℝ}


/-- Corrected native selected-image average numerical diagonal, with no free
assignment sum. Multiplicity is clipped only at the actual selected fiber cap. -/
def secondAverageDiagonalCost (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s) (G : Id)
    (Js : ∀B:actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (η₁ η₂ τ : Character) (t K Z Cz Ct : ℝ) (M : actualAllocations (tuplePools s) G→ℝ) : ℝ :=
  PairedRetainedBudget.coloredOuterAverage s cover G Js η₁ η₂ τ t M
    (fun B _=>Cz*profileCap (restOf s (by norm_num) cover G B (Js B))^2*K*Z^(93/100:ℝ)+
      Ct*profileCap (restOf s (by norm_num) cover G B (Js B))^2*Z^(-22:ℝ))

theorem second_average_diagonal_cost_le (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s) (G : Id)
    (Js : ∀B:actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (η₁ η₂ τ : Character) (t K Z Cz Ct W : ℝ) (N : ℕ)
    (M : actualAllocations (tuplePools s) G→ℝ) (hM0 : ∀B,0 ≤ M B)
    (hM : ∀B,M B ≤ (selY (allocatedLiveSource s (by norm_num) cover G B) (Js B)).card)
    (hJ : ∀B,Fintype.card (Js B) ≤ N)
    (hW : ∀B,slotWidth (allocatedLiveSource s (by norm_num) cover G B) (Js B) ≤ W)
    (hK : 0 ≤ K) (hZ : 0 ≤ Z) (hCz : 0 ≤ Cz) (hCt : 0 ≤ Ct) :
    secondAverageDiagonalCost s cover G Js η₁ η₂ τ t K Z Cz Ct M ≤
      ((actualAllocations (tuplePools s) G).card:ℝ)^2*shapeConstant N*
        (∏i,s.M i)^4*W^2*profileCap s^2*(Cz*K*Z^(93/100:ℝ)+Ct*Z^(-22:ℝ)) := by
  let T := Cz*K*Z^(93/100:ℝ)+Ct*Z^(-22:ℝ)
  have hT : 0 ≤ T := by dsimp [T];positivity
  have hper (B : actualAllocations (tuplePools s) G) :
      TwistedRawBall.allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B *
        (Atot (allocatedLiveSource s (by norm_num) cover G B) (Js B) τ t *
          ((2:ℝ)^Fintype.card (Js B)*M B)*
          ∑_χ:RayCharacter,∑_ζ:RayCharacter,
            (Cz*profileCap (restOf s (by norm_num) cover G B (Js B))^2*K*Z^(93/100:ℝ)+
             Ct*profileCap (restOf s (by norm_num) cover G B (Js B))^2*Z^(-22:ℝ))) ≤
      shapeConstant N*(∏i,s.M i)^4*W^2*profileCap s^2*T := by
    have hw := allocation_weight_le s η₁ η₂ G B
    have hm := selected_average_mass_le s (by norm_num) cover G Js B τ t W (M B) N (hJ B) (hW B) (hM0 B) (hM B)
    have hp := pow_le_pow_left₀ (profileCap_nonneg _) (restOf_profile_le s (by norm_num) cover G B (Js B)) 2
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    have hmass0 : 0 ≤ Atot (allocatedLiveSource s (by norm_num) cover G B) (Js B) τ t *
        ((2:ℝ)^Fintype.card (Js B)*M B)*((Fintype.card RayCharacter:ℝ)*(Fintype.card RayCharacter:ℝ)) := by
      have := hM0 B
      unfold Atot
      positivity
    have hm' := mul_le_mul hm hp (sq_nonneg _) (by have := pcMass_nonneg;positivity)
    have ht' := mul_le_mul_of_nonneg_right hm' hT
    have hfinal := mul_le_mul hw ht' (mul_nonneg (mul_nonneg hmass0 (sq_nonneg _)) hT) (sq_nonneg _)
    convert hfinal using 1 <;> simp only [shapeConstant,T] <;> ring
  unfold secondAverageDiagonalCost PairedRetainedBudget.coloredOuterAverage
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun B _=>hper B)) (Nat.cast_nonneg _)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,T]
  ring
end
end QRH.Cycle092.RawPairDiagonalBudget
#print axioms QRH.Cycle092.RawPairDiagonalBudget.second_average_diagonal_cost_le
