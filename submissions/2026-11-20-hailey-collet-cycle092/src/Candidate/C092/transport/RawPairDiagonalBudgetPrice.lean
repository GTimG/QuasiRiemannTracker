/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual colored allocation and selected-assignment masses for H.5. Native
Sil bounds are used only for nonnegative coefficient majorants. -/
import Candidate.C092.transport.RawPairDiagonalBudgetLedger
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderDiag9
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QRH.Cycle092.RawPairDiagonalBudget
noncomputable section
local instance (priority := 2000) diagSubtypeDecEqPrice {κ : Type*} {p : κ→Prop} : DecidableEq (Subtype p) := Classical.decEq _
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentAddedZeroUniform
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstMixedAllowance
open MixedFirstLiveSource MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.Concrete QRH.SilDensitySplit.CubeFree.Second.ConcreteDiagAssembly
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι] {a b : ℝ}


/-- Keep the TRUE two label norms inside the symmetric source core. -/
def balancedCore (s : Source ι a b) (τ : Character) (G opp : Id) : ℝ :=
  (τ.modulus.absNorm:ℝ)*sourceVolume s^2/((G.absNorm:ℝ)*(opp.absNorm:ℝ))

lemma core_le_budget (s : Source ι a b) (τ : Character) (G opp : Id) (A Z loss : ℝ)
    (hA : 0≤A) (hZ : 1≤Z) (hloss : 0≤loss) :
    A*balancedCore s τ G opp ≤ balancedBudget s τ G opp A Z loss := by
  have ha := Real.one_le_rpow hZ (CenteredMomentFirstMixedAllowance.allowance_nonneg G opp Z)
  have hl := Real.one_le_rpow hZ hloss
  have hc : 0≤A*balancedCore s τ G opp := by unfold balancedCore;positivity
  calc
    _ ≤ A*balancedCore s τ G opp*Z^(allowance G opp Z) := le_mul_of_one_le_right hc ha
    _ ≤ (A*balancedCore s τ G opp*Z^(allowance G opp Z))*Z^loss :=
      le_mul_of_one_le_right (by unfold balancedCore;positivity) hl
    _ = _ := by unfold balancedBudget balancedCore;ring

lemma coarse_price_of_core (s : Source ι a b) (τ : Character) (G opp : Id)
    (hG : G≠0) (hopp : opp≠0) (A Z loss K M Cz Ct θ : ℝ)
    (hZ : 1<Z) (hA : 0≤A) (hloss : 0≤loss) (hK : 0≤K)
    (hM : 0≤M) (hCz : 0≤Cz) (hCt : 0≤Ct)
    (hV : (sourceVolume s)⁻¹≤Z^(2:ℝ))
    (hNG : (G.absNorm:ℝ)≤Z^(8:ℝ)) (hNO : (opp.absNorm:ℝ)≤Z^(8:ℝ))
    (hcore : K≤4*Z^(1/1000:ℝ)*balancedCore s τ G opp/Z)
    (hzero : 4*M*Cz*Z^(-33/500:ℝ)≤θ/2)
    (htail : M*Ct*Z^(-1997/1000:ℝ)≤θ/2) :
    M*A*Z^(3/1000:ℝ)*(Cz*K*Z^(93/100:ℝ)+Ct*Z^(-22:ℝ)) ≤
      θ*balancedBudget s τ G opp A Z loss := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hc : 0≤balancedCore s τ G opp := by unfold balancedCore;positivity
  have hθ : 0≤θ/2 := (by positivity : 0≤4*M*Cz*Z^(-33/500:ℝ)).trans hzero
  have hp0 : Z^(-33/500:ℝ)=Z^(3/1000:ℝ)*Z^(1/1000:ℝ)*Z^(93/100:ℝ)/Z := by
    rw [show (-33/500:ℝ)=3/1000+1/1000+93/100-1 by norm_num,
      Real.rpow_sub hz,Real.rpow_add hz,Real.rpow_add hz,Real.rpow_one]
  have hpT : Z^(3/1000:ℝ)*Z^(-22:ℝ)=Z^(-1997/1000:ℝ)*Z^(-20:ℝ) := by
    rw [←Real.rpow_add hz,←Real.rpow_add hz];norm_num
  have hb0 := core_le_budget s τ G opp A Z loss hA hZ.le hloss
  have hbT : A*Z^(-20:ℝ)≤balancedBudget s τ G opp A Z loss := by
    have hb := QRH.SilDensitySplit.CubeFree.Second.ProviderDiag.budget_lower s τ G opp hG hopp A Z loss hZ hA hV hNG hNO
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith : (-20:ℝ)≤loss-20)) hA).trans hb
  have hz0 : M*A*Z^(3/1000:ℝ)*Cz*K*Z^(93/100:ℝ) ≤ (θ/2)*balancedBudget s τ G opp A Z loss := by
    calc
      _ ≤ M*A*Z^(3/1000:ℝ)*Cz*(4*Z^(1/1000:ℝ)*balancedCore s τ G opp/Z)*Z^(93/100:ℝ) := by gcongr
      _ = (4*M*Cz*Z^(-33/500:ℝ))*(A*balancedCore s τ G opp) := by rw [hp0];ring
      _ ≤ (θ/2)*(A*balancedCore s τ G opp) := mul_le_mul_of_nonneg_right hzero (mul_nonneg hA hc)
      _ ≤ _ := mul_le_mul_of_nonneg_left hb0 hθ
  have ht0 : M*A*Z^(3/1000:ℝ)*Ct*Z^(-22:ℝ) ≤ (θ/2)*balancedBudget s τ G opp A Z loss := by
    calc
      _ = (M*Ct*Z^(-1997/1000:ℝ))*(A*Z^(-20:ℝ)) := by
        calc
          _ = M*A*Ct*(Z^(3/1000:ℝ)*Z^(-22:ℝ)) := by ring
          _ = M*A*Ct*(Z^(-1997/1000:ℝ)*Z^(-20:ℝ)) := by rw [hpT]
          _ = _ := by ring
      _ ≤ (θ/2)*(A*Z^(-20:ℝ)) := mul_le_mul_of_nonneg_right htail (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hbT hθ
  nlinarith only [hz0,ht0]
end
end QRH.Cycle092.RawPairDiagonalBudget
#print axioms QRH.Cycle092.RawPairDiagonalBudget.coarse_price_of_core
