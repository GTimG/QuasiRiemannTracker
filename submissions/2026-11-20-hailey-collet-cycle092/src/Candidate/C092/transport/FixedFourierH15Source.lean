/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual fixed H8 source reaches its original Fourier-window H.15. -/
import Candidate.C092.transport.FixedFourierH15Pointwise
import Candidate.C092.transport.FixedPhysicalPaymentAll

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
local instance c092LocalInst_Candidate_C092_transport_FixedFourierH15Source_93d280d1f29c498d_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

/-- No H15 estimate is an input. The original same-supported-witness H8
source, exact allocations, original Fourier identity and integrability supply it. -/
theorem original_window_H15 (ha : 0<a) (hb : 0 ≤ b) (ω₁ ω₂ : Character)
    (ε Bcap : ℝ) (hε : 0<ε) (hB : 0 ≤ Bcap) :
    ∃ J : ℕ,∃ S : Finset (ℕ×ℕ),∃ hS : (0,0)∈S,
    ∀ Q : Id,∃ C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,
    ∀ (r : Source ι a b) (D : FixedCubeDatum),D.Q=Q →
      (HeckeRowClosure.rowConductorBound D.η D.m 1 (D.A*D.z):ℝ) ≤ U^Bcap →
    ∀ (G L : Id) (hG : Supported G),Squarefree L →
      (∀ (B : commonAlloc r G) (E : fullPrimaryAlloc r G B L),
        (r.Fhole.absNorm:ℝ)*(∏i:liveIndices E.val,2*r.P i.val.val)*
          (r.R.absNorm:ℝ)*(G.absNorm:ℝ)*(L.absNorm:ℝ) ≤ U^Bcap) →
    ∀ (η : Character) (χ : RayCharacter),D.η=childCharacter η χ → D.m=nativeSourceMask r →
    ∀ (t θ X : ℝ),0<X → ∀ (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V),
    ‖nativeWindowPolynomial r ha D ω₁ ω₂ η χ G hG L t θ X V‖^2 ≤
      (allocationCount r G L:ℝ)^2*fixedMarkCost r*
        (C*(sourceControl S r.W₁*sourceControl S r.W₂)*U^ε)^2*(sourceVolume r)^2*
        (sourcePrefix r G L*max 1 r.L)⁻¹*profileHeightCost r t θ J*(windowMass V hc hs J)^2 := by
  obtain ⟨J,S,hS,h⟩ := allocated_physical_square (ι:=ι) ha hb ω₁ ω₂ ε Bcap hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q
  obtain ⟨C,hC,hbound⟩ := h Q
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with U hU
  intro r D hQ hcond G L hG hL hbudget η χ hη hm t θ X hX V hc hs
  let E : ℝ := (allocationCount r G L:ℝ)^2*fixedMarkCost r*
    (C*(sourceControl S r.W₁*sourceControl S r.W₂)*U^ε)^2*sourceVolume r*
      (sourcePrefix r G L*max 1 r.L)⁻¹
  have hE : 0 ≤ E := by
    have hm := fixedMarkCost_nonneg r
    have hv := (sourceVolume_pos r).le
    have hp := sourcePrefix_pos r G L hG.1 hL.ne_zero
    dsimp only [E]
    positivity
  have hheight (v : ℝ) : ‖coloredFullyAllocatedPhysicalHeight r ha hb D ω₁ ω₂ G L v‖^2 ≤
      E*(1+‖r.t₁+v‖+‖r.t₂+v‖)^(2*J) := by
    have hh := hU r D hQ hcond G L hG.1 hL hbudget v
    apply hh.trans_eq
    unfold E sourceVolume sourcePrefix
    rw [mul_pow,←pow_mul]
    ring_nf
  have hh := colored_window_unnormalized r ha hb D ω₁ ω₂ η χ hη hm G hG L hL t θ X hX V hc hs J E hE hheight
  apply hh.trans_eq
  dsimp only [E]
  ring

#print axioms original_window_H15
end QRH.Cycle092.FixedFourierH15
