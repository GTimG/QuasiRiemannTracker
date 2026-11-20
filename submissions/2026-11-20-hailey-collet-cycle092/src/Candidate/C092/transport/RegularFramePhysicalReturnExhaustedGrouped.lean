/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Unconditional genuinely exhausted regular native grouped term. Both native
source loss and grouped loss remain explicit, even at selected width zero. -/
import Candidate.C092.transport.RegularFramePhysicalReturnExhausted
import Candidate.C092.transport.RegularFramePhysicalReturnGroupedMesh
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularFramePhysicalReturn
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily CenteredMomentEnergyBands
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
open QRH.Cycle092.WholeSlot QRH.Cycle092.RegularColoredForward
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped

theorem exhausted_grouped {L : ℝ} (Mmin Mmax : ℝ) (hMmin : 0≤ Mmin) (hMmax : Mmax<2)
    (hL : 0≤ L) (epsilon delta : ℝ) (hepsilon : 0< epsilon) (hdelta : 0< delta) :
    ∃meshMax : ℝ,0< meshMax ∧ ∀mesh : ℝ,0< mesh → mesh≤ meshMax →
    ∀ (theta : GData L),theta.N=0 →
    ∀ (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
      (hPhi : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic theta.bΦ)
      (eta omega1 omega2 : Character),theta.Q≤ omega1.modulus → theta.Q≤ omega2.modulus →
    ∃D : ℕ,∃controls : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧
    ∀ᶠ U : ℝ in atTop,∀ (r : GSrc theta mesh U) (labels : Finset (GLabel theta mesh U))
      (w0 Hrad v : ℝ),
      Second.AdmissibleGroup (frameSideFrame L theta mesh omega1 omega2 eta U) Mmin Mmax mesh epsilon U r labels Hrad →
      r.X₁≤ U^(3/4:ℝ) → r.X₂≤ U^(3/4:ℝ) → r.Y₁≤ U^(3/4:ℝ) → r.Y₂≤ U^(3/4:ℝ) →
      (∑x∈labels,gWeight x*framegEnergy omega1 omega2 eta r x v)≤
        C*gAmp L theta mesh eta U r D controls*(1+‖v‖)^(2*D)*
          U^(r.colLog+r.twistLog+(PackedPrice.withLoss PackedPrice.exhausted delta hdelta.le).f
            w0 (gP r) (∑i,r.w i) Hrad+epsilon) := by
  let price := PackedPrice.withLoss PackedPrice.exhausted delta hdelta.le
  obtain ⟨mesh0,hm0,hgroup⟩ := terminal_frame_grouped_common_mesh price Mmin Mmax hMmin hMmax hL epsilon hepsilon
  refine ⟨min mesh0 ((2-Mmax)/2),lt_min hm0 (by linarith),?_⟩
  intro mesh hm hmm theta hN hbeta hPhi eta omega1 omega2 hQ1 hQ2
  obtain ⟨D,J,Cterm,hCterm,hframes⟩ := exhausted_frames theta hN hbeta hPhi eta omega1 omega2 hQ1 hQ2 delta hdelta
  obtain ⟨controls,Ctot,hCtot,hgroup⟩ := hgroup mesh hm (hmm.trans (min_le_left _ _)) theta J D
  refine ⟨D,controls,Ctot*Cterm,by positivity,?_⟩
  filter_upwards [hframes,hgroup,eventually_logb_le 2 ((2-Mmax)/2) (by linarith)] with U hframes hgroup hlog
  intro r labels w0 Hrad v hadm hx1 hx2 hy1 hy2
  have hHmax : Hrad≤ Mmax := hadm.2.1
  have hM : Real.logb U (2*U^(Hrad+mesh))≤2 := by
    rw [Real.logb_mul (by norm_num) (Real.rpow_pos_of_pos (zero_lt_one.trans r.hZ) _).ne',
      Real.logb_rpow (zero_lt_one.trans r.hZ) r.hZ.ne']
    have hmrad := hmm.trans (min_le_right _ _)
    linarith
  have hleaf := hframes mesh r v (Real.logb U (2*U^(Hrad+mesh))) (1-6*w0) (gP r+2*Real.logb U 3)
    hM hx1 hx2 hy1 hy2
  exact hgroup eta omega1 omega2 r labels w0 Hrad (1-6*w0) Cterm v hCterm.le hadm
    (by simpa only [price,PackedPrice.exhausted_with_loss] using hleaf)

end
end QRH.Cycle092.RegularFramePhysicalReturn
#print axioms QRH.Cycle092.RegularFramePhysicalReturn.exhausted_grouped
