/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Early unconditional exhausted-prefix frame leaves. The native unmarked
payment is positive and independent of the sum of original marked widths. -/
import Candidate.C092.transport.RegularFramePhysicalReturnEmptyLeaves
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularFramePhysicalReturn
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily CenteredMomentEnergyBands
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
open QRH.Cycle092.WholeSlot QRH.Cycle092.StrongPair QRH.Cycle092.RegularColoredForward
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped

theorem exhausted_frames {L : ℝ} (theta : GData L) (hN : theta.N=0)
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hPhi : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic theta.bΦ)
    (eta omega1 omega2 : Character) (hQ1 : theta.Q≤ omega1.modulus) (hQ2 : theta.Q≤ omega2.modulus)
    (delta : ℝ) (hdelta : 0< delta) :
    ∃D J : ℕ,∃Cterm : ℝ,0< Cterm ∧ ∀ᶠ U : ℝ in atTop,
    ∀mesh : ℝ,∀ (r : GSrc theta mesh U) (v Mrad Hsource Pbd : ℝ),Mrad≤2 →
      r.X₁≤ U^(3/4:ℝ) → r.X₂≤ U^(3/4:ℝ) → r.Y₁≤ U^(3/4:ℝ) → r.Y₂≤ U^(3/4:ℝ) →
      frameRectangularLeaves theta eta omega1 omega2 r v Mrad Hsource delta
        (Cterm*r.height^D*(1+‖v‖)^(2*D)) Pbd J := by
  obtain ⟨D,S,C,hC,hs⟩ := exhausted_anchor_sources theta hbeta hPhi eta omega1 omega2 hQ1 hQ2 delta hdelta
  obtain ⟨J,K,hK,hframe⟩ := empty_frame_metadata D S C hC
  refine ⟨D,J,K,hK,?_⟩
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).eventually (eventually_ge_atTop (3:ℝ))
  filter_upwards [hs,ht] with U hs ht
  intro mesh r v Mrad Hsource Pbd hM2 hx1 hx2 hy1 hy2
  have hu : 0< U := zero_lt_one.trans hs.1
  have hc : 3*U^(3/4:ℝ)≤ U := by
    calc
      _ ≤ U^(1/4:ℝ)*U^(3/4:ℝ) := mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hu.le _)
      _ = _ := by rw [←Real.rpow_add hu];norm_num
  exact hframe theta hN eta omega1 omega2 hQ1 hQ2 r v Mrad Hsource Pbd delta hM2 hx1 hx2 hy1 hy2 hc hs.2

end
end QRH.Cycle092.RegularFramePhysicalReturn
#print axioms QRH.Cycle092.RegularFramePhysicalReturn.exhausted_frames
