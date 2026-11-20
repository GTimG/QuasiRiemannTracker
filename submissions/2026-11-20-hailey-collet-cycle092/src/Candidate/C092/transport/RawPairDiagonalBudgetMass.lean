/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual colored allocation and selected-assignment masses for H.5. Native
Sil bounds are used only for nonnegative coefficient majorants. -/
import Candidate.C092.transport.TwistedRawBallPhysicalSides
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

lemma allocation_weight_le (s : Source ι a b) (η₁ η₂ : Character) (G : Id)
    (B : actualAllocations (tuplePools s) G) :
    TwistedRawBall.allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B ≤ (∏i,s.M i)^2 := by
  have hc := TwistedRawSource.ordinaryColor_norm_le_one η₁ η₂ B.val
  have he : TwistedRawBall.allocationScalar s (idealCoeff η₁) (idealCoeff η₂) G B =
      allocWeight s G B*TwistedRawSource.ordinaryColor (idealCoeff η₁) (idealCoeff η₂) B.val := by
    unfold TwistedRawBall.allocationScalar allocWeight;ring
  unfold TwistedRawBall.allocationWeight
  rw [he,norm_mul]
  exact (pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_right (norm_nonneg _) hc) 2).trans
    (allocWeight_sq_le s G B)

lemma selected_support_card (s : Source ι a b) (J : Finset ι) (y : J→Id) (hy : y∈selY s J) :
    (IdealMobiusDivisorSum.primeSupport (∏j,y j)).card ≤ Fintype.card J := by
  let m := (Finset.univ : Finset J).val.map y
  have hp : ∀q∈m,Prime q := by
    intro q hq
    obtain ⟨j,hj,rfl⟩ := Multiset.mem_map.mp hq
    exact selY_prime s J y hy j
  have he := UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hp
  have hf : UniqueFactorizationMonoid.normalizedFactors (∏j,y j)=m := by simpa only [m,Finset.prod_map_val] using he
  unfold IdealMobiusDivisorSum.primeSupport
  rw [hf]
  exact (Multiset.toFinset_card_le m).trans_eq (by simp only [m,Multiset.card_map];exact Finset.card_univ)

lemma assignment_mass_le (s : Source ι a b) (J : Finset ι) :
    (∑y∈selY s J,(2:ℝ)^(IdealMobiusDivisorSum.primeSupport (∏j,y j)).card) ≤
      (2:ℝ)^(Fintype.card J)*∏j:J,256*s.P j.val := by
  calc
    _ ≤ ∑_y∈selY s J,(2:ℝ)^(Fintype.card J) :=
      Finset.sum_le_sum (fun y hy=>pow_le_pow_right₀ (by norm_num) (selected_support_card s J y hy))
    _ = (2:ℝ)^(Fintype.card J)*(selY s J).card := by simp;ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (selY_card_le s J) (by positivity)

lemma selected_pair_mass_le (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G : Id) (Js : ∀B:actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (B : actualAllocations (tuplePools s) G)
    (τ : Character) (t W : ℝ) (N : ℕ) (hN : Fintype.card (Js B)≤N)
    (hW : slotWidth (allocatedLiveSource s hb cover G B) (Js B)≤W) :
    Atot (allocatedLiveSource s hb cover G B) (Js B) τ t *
      (∑y∈selY (allocatedLiveSource s hb cover G B) (Js B),∑χ:RayCharacter,∑ζ:RayCharacter,
        (2:ℝ)^(IdealMobiusDivisorSum.primeSupport (∏j,y j)).card) ≤
      pcMass*(∏i,s.M i)^2*((2:ℝ)*256^2)^N*
        ((Fintype.card RayCharacter:ℝ)*(Fintype.card RayCharacter:ℝ))*W^2 := by
  let J := Js B
  let r := allocatedLiveSource s hb cover G B
  let p : ℝ := ∏j:J,r.P j.val
  have hp0 : 0≤p := Finset.prod_nonneg (fun j _=>(zero_le_one.trans (r.hP j.val)))
  have hpW : p≤W := (alloc_P_le_W s hb cover G Js B).trans hW
  have hW0 : 0≤W := hp0.trans hpW
  have hA := (Atot_le r J τ t).trans (alloc_AtotP_le s hb cover G Js B)
  have hmass := assignment_mass_le r J
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] at hmass
  change (∑y∈selY r J,(2:ℝ)^(IdealMobiusDivisorSum.primeSupport (∏j,y j)).card) ≤
    (2:ℝ)^(Fintype.card J)*(256^(Fintype.card J)*p) at hmass
  have hsum : (∑y∈selY r J,∑χ:RayCharacter,∑ζ:RayCharacter,
      (2:ℝ)^(IdealMobiusDivisorSum.primeSupport (∏j,y j)).card) ≤
      ((Fintype.card RayCharacter:ℝ)*(Fintype.card RayCharacter:ℝ))*
        ((2:ℝ)^(Fintype.card J)*256^(Fintype.card J)*p) := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [←Finset.mul_sum,←Finset.mul_sum]
    have hh := mul_le_mul_of_nonneg_left hmass
      (show 0≤(Fintype.card RayCharacter:ℝ)*(Fintype.card RayCharacter:ℝ) by positivity)
    simpa only [mul_assoc] using hh
  have hprod := mul_le_mul hA hsum (by positivity)
    (show 0≤pcMass*(∏i,s.M i)^2*((256:ℝ)^(Fintype.card J)*p) by have := pcMass_nonneg;positivity)
  apply hprod.trans
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
#print axioms QRH.Cycle092.RawPairDiagonalBudget.selected_pair_mass_le
