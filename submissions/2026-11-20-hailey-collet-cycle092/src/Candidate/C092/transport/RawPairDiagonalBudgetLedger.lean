/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual colored allocation and selected-assignment masses for H.5. Native
Sil bounds are used only for nonnegative coefficient majorants. -/
import Candidate.C092.transport.RawPairDiagonalBudgetMass
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderDiag9
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QRH.Cycle092.RawPairDiagonalBudget
noncomputable section
local instance (priority := 2000) diagSubtypeDecEq {κ : Type*} {p : κ→Prop} : DecidableEq (Subtype p) := Classical.decEq _
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentAddedZeroUniform
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstLiveSource MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.Concrete QRH.SilDensitySplit.CubeFree.Second.ConcreteDiagAssembly
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι] {a b : ℝ}


/-- Exactly the zero and discarded summands of the original SecondSidePrice
ledger, with all allocation, assignment, ray and squarefree-fiber costs. -/
def secondDiagonalCost (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s) (G : Id)
    (Js : ∀B:actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (η₁ η₂ τ : Character) (t K Z Cz Ct : ℝ) : ℝ :=
  ((actualAllocations (tuplePools s) G).card:ℝ)*
    ∑B:actualAllocations (tuplePools s) G,
      TwistedRawBall.allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B *
        (Atot (allocatedLiveSource s hb cover G B) (Js B) τ t *
          ∑y∈selY (allocatedLiveSource s hb cover G B) (Js B),∑χ:RayCharacter,∑ζ:RayCharacter,
            (2:ℝ)^(IdealMobiusDivisorSum.primeSupport (∏j,y j)).card *
              (Cz*profileCap (restOf s hb cover G B (Js B))^2*K*Z^(93/100:ℝ)+
               Ct*profileCap (restOf s hb cover G B (Js B))^2*Z^(-22:ℝ)))

def shapeConstant (N : ℕ) : ℝ :=
  pcMass*((2:ℝ)*256^2)^N*((Fintype.card RayCharacter:ℝ)*(Fintype.card RayCharacter:ℝ))

lemma shapeConstant_nonneg (N : ℕ) : 0≤ shapeConstant N := by
  unfold shapeConstant;have := pcMass_nonneg;positivity

/-- The actual #allocations appears TWICE, as in the original Cauchy.
The selected radius, profile controls and all colors remain genuine. -/
theorem second_diagonal_cost_le (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s) (G : Id)
    (Js : ∀B:actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (η₁ η₂ τ : Character) (t K Z Cz Ct W : ℝ) (N : ℕ)
    (hJ : ∀B,Fintype.card (Js B)≤N)
    (hW : ∀B,slotWidth (allocatedLiveSource s hb cover G B) (Js B)≤W)
    (hK : 0≤K) (hZ : 0≤Z) (hCz : 0≤Cz) (hCt : 0≤Ct) :
    secondDiagonalCost s hb cover G Js η₁ η₂ τ t K Z Cz Ct ≤
      ((actualAllocations (tuplePools s) G).card:ℝ)^2*shapeConstant N*
        (∏i,s.M i)^4*W^2*profileCap s^2*(Cz*K*Z^(93/100:ℝ)+Ct*Z^(-22:ℝ)) := by
  let T := Cz*K*Z^(93/100:ℝ)+Ct*Z^(-22:ℝ)
  have hT : 0≤T := by dsimp [T];positivity
  have hper (B : actualAllocations (tuplePools s) G) :
      TwistedRawBall.allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B *
        (Atot (allocatedLiveSource s hb cover G B) (Js B) τ t *
          ∑y∈selY (allocatedLiveSource s hb cover G B) (Js B),∑χ:RayCharacter,∑ζ:RayCharacter,
            (2:ℝ)^(IdealMobiusDivisorSum.primeSupport (∏j,y j)).card *
              (Cz*profileCap (restOf s hb cover G B (Js B))^2*K*Z^(93/100:ℝ)+
               Ct*profileCap (restOf s hb cover G B (Js B))^2*Z^(-22:ℝ))) ≤
      shapeConstant N*(∏i,s.M i)^4*W^2*profileCap s^2*T := by
    have hw := allocation_weight_le s η₁ η₂ G B
    have hm := selected_pair_mass_le s hb cover G Js B τ t W N (hJ B) (hW B)
    have hp := pow_le_pow_left₀ (profileCap_nonneg _) (restOf_profile_le s hb cover G B (Js B)) 2
    have hsum : (Atot (allocatedLiveSource s hb cover G B) (Js B) τ t *
          ∑y∈selY (allocatedLiveSource s hb cover G B) (Js B),∑χ:RayCharacter,∑ζ:RayCharacter,
            (2:ℝ)^(IdealMobiusDivisorSum.primeSupport (∏j,y j)).card *
              (Cz*profileCap (restOf s hb cover G B (Js B))^2*K*Z^(93/100:ℝ)+
               Ct*profileCap (restOf s hb cover G B (Js B))^2*Z^(-22:ℝ))) =
        (Atot (allocatedLiveSource s hb cover G B) (Js B) τ t *
          ∑y∈selY (allocatedLiveSource s hb cover G B) (Js B),∑χ:RayCharacter,∑ζ:RayCharacter,
            (2:ℝ)^(IdealMobiusDivisorSum.primeSupport (∏j,y j)).card)*
          profileCap (restOf s hb cover G B (Js B))^2*T := by
      dsimp only [T]
      simp only [Finset.sum_mul,Finset.mul_sum]
      congr 1
      funext y
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro ζ hζ
      ring
    rw [hsum]
    have hmass0 : 0≤Atot (allocatedLiveSource s hb cover G B) (Js B) τ t *
          ∑y∈selY (allocatedLiveSource s hb cover G B) (Js B),∑χ:RayCharacter,∑ζ:RayCharacter,
            (2:ℝ)^(IdealMobiusDivisorSum.primeSupport (∏j,y j)).card := by unfold Atot;positivity
    have hm' := mul_le_mul hm hp (sq_nonneg _) (by have := pcMass_nonneg;positivity)
    have ht' := mul_le_mul_of_nonneg_right hm' hT
    have hfinal := mul_le_mul hw ht' (mul_nonneg (mul_nonneg hmass0 (sq_nonneg _)) hT) (sq_nonneg _)
    convert hfinal using 1 <;> unfold shapeConstant <;> ring
  unfold secondDiagonalCost
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun B _=>hper B)) (Nat.cast_nonneg _)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,T]
  ring
end
end QRH.Cycle092.RawPairDiagonalBudget
#print axioms QRH.Cycle092.RawPairDiagonalBudget.second_diagonal_cost_le
