/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual fixed H8 source reaches its original Fourier-window H.15. -/
import Candidate.C092.transport.FixedFourierH15Source
import Candidate.C092.transport.FixedFourierH15Allocations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory Filter
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion FourierBridge
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSmooth
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentDivisorAllocation
open CenteredMomentRowNorm CenteredMomentSecondSectorColumns CenteredMomentChildRows CenteredMomentChildAssembly
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedCommonHeights
open QRH.Cycle092.SignedCenter
open MixedPrincipalWindow MixedCommonRestriction CenteredMomentFiniteProfileExceptional
open QRH.Cycle092.FixedCubeGauss
namespace QRH.Cycle092.FixedFourierH15
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance c092LocalInst_Candidate_C092_transport_FixedFourierH15Subpower_5b9501d8c2624f68_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

/-- No H15 estimate is an input. The original same-supported-witness H8
source, exact allocations, original Fourier identity and integrability supply it. -/
theorem original_window_H15_subpower (ha : 0<a) (hb : 0 ≤ b) (ω₁ ω₂ : Character)
    (N : ℕ) (hN : Fintype.card ι ≤ N) (ε Bcap : ℝ) (hε : 0<ε) (hB : 0 ≤ Bcap) :
    ∃ J : ℕ,∃ S : Finset (ℕ×ℕ),∃ hS : (0,0)∈S,
    ∀ Q : Id,∃ C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
    ∀ (r : Source ι a b) (D : FixedCubeDatum),D.Q=Q →
      (HeckeRowClosure.rowConductorBound D.η D.m 1 (D.A*D.z):ℝ) ≤ U^Bcap →
    ∀ (G L : Id) (hG : Supported G),Squarefree L →
      (G.absNorm:ℝ) ≤ U^Bcap → (L.absNorm:ℝ) ≤ U^Bcap →
      (∀ (B : commonAlloc r G) (E : fullPrimaryAlloc r G B L),
        (r.Fhole.absNorm:ℝ)*(∏i:liveIndices E.val,2*r.P i.val.val)*
          (r.R.absNorm:ℝ)*(G.absNorm:ℝ)*(L.absNorm:ℝ) ≤ U^Bcap) →
    ∀ (η : Character) (χ : RayCharacter),D.η=childCharacter η χ → D.m=nativeSourceMask r →
    ∀ (t θ X : ℝ),0<X → ∀ (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V),
    ‖nativeWindowPolynomial r ha D ω₁ ω₂ η χ G hG L t θ X V‖^2 ≤
      C*fixedMarkCost r*(sourceControl S r.W₁*sourceControl S r.W₂)^2*U^ε*(sourceVolume r)^2*
        (sourcePrefix r G L*max 1 r.L)⁻¹*profileHeightCost r t θ J*(windowMass V hc hs J)^2 := by
  obtain ⟨J,S,hS,h⟩ := original_window_H15 (ι:=ι) ha hb ω₁ ω₂ (ε/4) Bcap (by positivity) hB
  obtain ⟨D,hD,hcount⟩ := allocationCount_subpower N Bcap (ε/4) hB (by positivity)
  refine ⟨J,S,hS,?_⟩
  intro Q
  obtain ⟨C,hC,hbound⟩ := h Q
  refine ⟨D^2*C^2,by positivity,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (1:ℝ)] with U hU hU1
  refine ⟨hU1,?_⟩
  intro r dat hQ hcond G L hG hL hNG hNL hbudget η χ hη hm t θ X hX V hc hs
  have hh := hU r dat hQ hcond G L hG hL hbudget η χ hη hm t θ X hX V hc hs
  have halloc := hcount r hN U hU1.le G L hG.1 hL.ne_zero hNG hNL
  let ctl := sourceControl S r.W₁*sourceControl S r.W₂
  have hscalar : (allocationCount r G L:ℝ)^2*(C*ctl*U^(ε/4))^2 ≤
      (D^2*C^2)*ctl^2*U^ε := by
    calc
      _ ≤ (D*U^(ε/4))^2*(C*ctl*U^(ε/4))^2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) halloc 2) (sq_nonneg _)
      _ = (D^2*C^2)*ctl^2*(U^(ε/4))^4 := by ring
      _ = _ := by rw [←Real.rpow_mul_natCast (zero_lt_one.trans hU1).le,show ε/4*(4:ℕ)=ε by norm_num]
  have hweight : 0 ≤ fixedMarkCost r*(sourceVolume r)^2*(sourcePrefix r G L*max 1 r.L)⁻¹*
      profileHeightCost r t θ J*(windowMass V hc hs J)^2 := by
    have hmark := fixedMarkCost_nonneg r
    have hp := sourcePrefix_pos r G L hG.1 hL.ne_zero
    have hcost : 0 ≤ profileHeightCost r t θ J := by
      unfold profileHeightCost
      exact mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (heightCost_pos t θ).le _)
    positivity
  apply hh.trans
  convert mul_le_mul_of_nonneg_right hscalar hweight using 1 <;> dsimp only [ctl] <;> ring

#print axioms original_window_H15_subpower
end QRH.Cycle092.FixedFourierH15
