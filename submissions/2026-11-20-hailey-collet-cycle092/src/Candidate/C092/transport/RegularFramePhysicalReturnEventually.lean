/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original all-V P2 supplier is the sole analytic input to the literal
regular frame leaves; the authentic reference and source matching are internal. -/
import Candidate.C092.transport.RegularFramePhysicalReturnLeaves
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularFramePhysicalReturn
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily CenteredMomentEnergyBands
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorPlainFiberSource
open QRH.Cycle092.WholeSlot QRH.Cycle092.StrongPair QRH.Cycle092.RegularColoredForward
open QRH.Cycle092.ReferenceArmRadial
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
local notation "O" => HeckeFamily.O

theorem regular_frames_of_p2 {L : ℝ} (theta : GData L)
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hPhi : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic theta.bΦ)
    (n y mesh : ℝ) (hy0 : sourceY0≤ y) (hy1 : y≤ sourceY) (hn0 : y≤ n)
    (eta omega1 omega2 : Character) (hQ1 : theta.Q≤ omega1.modulus) (hQ2 : theta.Q≤ omega2.modulus)
    (Dp : ℕ) (Sp : Finset (ℕ×ℕ)) (Cp : ℝ) (hCp : 0< Cp)
    (hP2 : ∀j : DictIdx,∀ᶠ U : ℝ in atTop,
      OrderedP2At (Fin theta.N) theta.rayM theta.Hray theta.hH theta.W n y mesh U
        (anchors eta j) theta.η₀ omega1 omega2 theta.Q Dp Sp Cp) :
    ∃D J : ℕ,∃Cterm : ℝ,0< Cterm ∧
    ∀ᶠ U : ℝ in atTop,∀ (r : GSrc theta mesh U) (v Mrad Pbd : ℝ),Mrad≤2 →
      r.X₁≤ U^n → r.X₂≤ U^y → r.Y₁≤ U^(23/200:ℝ) → r.Y₂≤ U^(18023/25000:ℝ) →
      (∑i,r.w i)≤ sourceWidth n y-(u:ℝ) →
      frameRectangularLeaves theta eta omega1 omega2 r v Mrad (H:ℝ) ((u:ℝ)-terminalReserve)
        (Cterm*r.height^D*(1+‖v‖)^(2*D)) Pbd J := by
  have hy : (1/3:ℝ)≤ y := by norm_num [sourceY0] at hy0;linarith
  have hn : (1/3:ℝ)≤ n := hy.trans hn0
  have hc : sourceWidth n y-(u:ℝ)≤ widthCap := by
    have h := actual_source_width_cap hy0 hy1 hn0
    have hu : (0:ℝ)≤(u:ℝ) := by norm_num [u]
    linarith
  obtain ⟨D,S,C,hC,hs⟩ := finite_anchor_sources theta hbeta hPhi n y mesh hn hy hc eta omega1 omega2 hQ1 hQ2
    Dp Sp Cp hCp hP2
  obtain ⟨J,K,hK,hframe⟩ := rectangle_frame_metadata D S C hC
  refine ⟨D,J,K,hK,?_⟩
  filter_upwards [hs,eventual_opened_arm_caps] with U hs hg
  intro r v Mrad Pbd hM2 hx1 hx2 hy1 hy2 hquota
  exact hframe theta eta omega1 omega2 r v Mrad Pbd hM2 hx1 hx2 hy1 hy2 hquota hg.2 hs.2

end
end QRH.Cycle092.RegularFramePhysicalReturn
#print axioms QRH.Cycle092.RegularFramePhysicalReturn.regular_frames_of_p2
