/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal regular native grouped physical term, with the numerical P2 price.
The mesh precedes source/Fourier metadata. Only original ordered all-V P2 is analytic input. -/
import Candidate.C092.transport.RegularFramePhysicalReturnEventually
import Candidate.C092.transport.RegularFramePhysicalReturnGroupedMesh
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
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
local notation "O" => HeckeFamily.O
local notation "actualPrice" => PackedPrice.regular PackedPrice.terminalReserve PackedPrice.terminalReserve_le

theorem regular_grouped_of_p2 {L : ℝ} (Mmin Mmax : ℝ) (hMmin : 0≤ Mmin) (hMmax : Mmax<2)
    (hL : 0≤ L) (epsilon : ℝ) (hepsilon : 0< epsilon) :
    ∃meshMax : ℝ,0< meshMax ∧ ∀mesh : ℝ,0< mesh → mesh≤ meshMax →
    ∀ (theta : GData L) (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
      (hPhi : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic theta.bΦ)
      (n y : ℝ) (hy0 : sourceY0≤ y) (hy1 : y≤ sourceY) (hn0 : y≤ n)
      (eta omega1 omega2 : Character) (hQ1 : theta.Q≤ omega1.modulus) (hQ2 : theta.Q≤ omega2.modulus)
      (Dp : ℕ) (Sp : Finset (ℕ×ℕ)) (Cp : ℝ),0< Cp →
      (∀j : DictIdx,∀ᶠ U : ℝ in atTop,
        OrderedP2At (Fin theta.N) theta.rayM theta.Hray theta.hH theta.W n y mesh U
          (anchors eta j) theta.η₀ omega1 omega2 theta.Q Dp Sp Cp) →
    ∃D : ℕ,∃controls : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧
    ∀ᶠ U : ℝ in atTop,∀ (r : GSrc theta mesh U) (labels : Finset (GLabel theta mesh U))
      (w0 Hrad v : ℝ),
      Second.AdmissibleGroup (frameSideFrame L theta mesh omega1 omega2 eta U) Mmin Mmax mesh epsilon U r labels Hrad →
      r.X₁≤ U^n → r.X₂≤ U^y → r.Y₁≤ U^(23/200:ℝ) → r.Y₂≤ U^(18023/25000:ℝ) →
      (∑i,r.w i)≤ sourceWidth n y-(u:ℝ) →
      (∑x∈labels,gWeight x*framegEnergy omega1 omega2 eta r x v)≤
        C*gAmp L theta mesh eta U r D controls*(1+‖v‖)^(2*D)*
          U^(r.colLog+r.twistLog+(actualPrice).f w0 (gP r) (∑i,r.w i) Hrad+epsilon) := by
  obtain ⟨mesh0,hm0,hgroup⟩ := terminal_frame_grouped_common_mesh actualPrice Mmin Mmax hMmin hMmax hL epsilon hepsilon
  refine ⟨min mesh0 ((2-Mmax)/2),lt_min hm0 (by linarith),?_⟩
  intro mesh hm hmm theta hbeta hPhi n y hy0 hy1 hn0 eta omega1 omega2 hQ1 hQ2 Dp Sp Cp hCp hP2
  obtain ⟨D,J,Cterm,hCterm,hframes⟩ := regular_frames_of_p2 theta hbeta hPhi n y mesh hy0 hy1 hn0 eta omega1 omega2
    hQ1 hQ2 Dp Sp Cp hCp hP2
  obtain ⟨controls,Ctot,hCtot,hgroup⟩ := hgroup mesh hm (hmm.trans (min_le_left _ _)) theta J D
  refine ⟨D,controls,Ctot*Cterm,by positivity,?_⟩
  filter_upwards [hframes,hgroup,eventually_logb_le 2 ((2-Mmax)/2) (by linarith)]
    with U hframes hgroup hlog
  intro r labels w0 Hrad v hadm hx1 hx2 hy1 hy2 hquota
  have hHmax : Hrad≤ Mmax := hadm.2.1
  have hM : Real.logb U (2*U^(Hrad+mesh))≤2 := by
    rw [Real.logb_mul (by norm_num) (Real.rpow_pos_of_pos (zero_lt_one.trans r.hZ) _).ne',
      Real.logb_rpow (zero_lt_one.trans r.hZ) r.hZ.ne']
    have hmrad := hmm.trans (min_le_right _ _)
    linarith
  have hleaf := hframes r v (Real.logb U (2*U^(Hrad+mesh))) (gP r+2*Real.logb U 3) hM hx1 hx2 hy1 hy2 hquota
  have he := hgroup eta omega1 omega2 r labels w0 Hrad (H:ℝ) Cterm v hCterm.le hadm
    (by simpa only [PackedPrice.actual_leaf_loss,StrongPair.terminalReserve,PackedPrice.terminalReserve] using hleaf)
  exact he

end
end QRH.Cycle092.RegularFramePhysicalReturn
#print axioms QRH.Cycle092.RegularFramePhysicalReturn.regular_grouped_of_p2
