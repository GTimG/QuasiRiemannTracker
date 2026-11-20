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
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentAddedZeroUniform
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstLiveSource MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.Concrete QRH.SilDensitySplit.CubeFree.Second.ConcreteDiagAssembly
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

lemma selected_average_mass_le (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G : Id) (Js : ∀B:actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (B : actualAllocations (tuplePools s) G)
    (τ : Character) (t W M : ℝ) (N : ℕ) (hN : Fintype.card (Js B)≤N)
    (hW : slotWidth (allocatedLiveSource s hb cover G B) (Js B)≤W) (hM0 : 0 ≤ M)
    (hM : M ≤ (selY (allocatedLiveSource s hb cover G B) (Js B)).card) :
    Atot (allocatedLiveSource s hb cover G B) (Js B) τ t *
      ((2:ℝ)^Fintype.card (Js B)*M)*
      ((Fintype.card RayCharacter:ℝ)*(Fintype.card RayCharacter:ℝ)) ≤
      pcMass*(∏i,s.M i)^2*((2:ℝ)*256^2)^N*
        ((Fintype.card RayCharacter:ℝ)*(Fintype.card RayCharacter:ℝ))*W^2 := by
  let J := Js B
  let r := allocatedLiveSource s hb cover G B
  let p : ℝ := ∏j:J,r.P j.val
  have hp0 : 0≤p := Finset.prod_nonneg (fun j _=>(zero_le_one.trans (r.hP j.val)))
  have hpW : p≤W := (alloc_P_le_W s hb cover G Js B).trans hW
  have hW0 : 0≤W := hp0.trans hpW
  have hA := (Atot_le r J τ t).trans (alloc_AtotP_le s hb cover G Js B)
  have hcard := hM.trans (selY_card_le r J)
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] at hcard
  change M ≤ 256^(Fintype.card J)*p at hcard
  have hmass := mul_le_mul_of_nonneg_left hcard (show 0 ≤ (2:ℝ)^Fintype.card J by positivity)
  have hprod := mul_le_mul hA hmass (mul_nonneg (by positivity) hM0)
    (show 0 ≤ pcMass*(∏i,s.M i)^2*((256:ℝ)^(Fintype.card J)*p) by have := pcMass_nonneg;positivity)
  have hprod' := mul_le_mul_of_nonneg_right hprod
    (show 0 ≤ (Fintype.card RayCharacter:ℝ)*(Fintype.card RayCharacter:ℝ) by positivity)
  apply hprod'.trans
  have he : (256:ℝ)^(Fintype.card J)*((2:ℝ)^(Fintype.card J)*256^(Fintype.card J)) =
      ((2:ℝ)*256^2)^(Fintype.card J) := by
    rw [mul_pow,←pow_mul,show 2*Fintype.card J=Fintype.card J+Fintype.card J by omega,pow_add]
    ring
  have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2*256^2) hN
  have hp2 := pow_le_pow_left₀ hp0 hpW 2
  have hc : 0≤pcMass*(∏i,s.M i)^2*((Fintype.card RayCharacter:ℝ)*(Fintype.card RayCharacter:ℝ)) := by
    have := pcMass_nonneg;positivity
  calc
    _ = pcMass*(∏i,s.M i)^2*((Fintype.card RayCharacter:ℝ)*(Fintype.card RayCharacter:ℝ))*
        (((2:ℝ)*256^2)^(Fintype.card J)*p^2) := by rw [←he];ring
    _ ≤ pcMass*(∏i,s.M i)^2*((Fintype.card RayCharacter:ℝ)*(Fintype.card RayCharacter:ℝ))*
        (((2:ℝ)*256^2)^N*W^2) := mul_le_mul_of_nonneg_left (mul_le_mul hpow hp2 (sq_nonneg _) (by positivity)) hc
    _ = _ := by ring
end
end QRH.Cycle092.RawPairDiagonalBudget
#print axioms QRH.Cycle092.RawPairDiagonalBudget.selected_average_mass_le
