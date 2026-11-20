/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A genuinely exhausted original prefix has zero native mark slots. Its frame
uses only the authentic unmarked pair and an explicitly positive source loss. -/
import Candidate.C092.transport.RegularFramePhysicalReturnLeaves
import Candidate.C092.transport.RegularFramePhysicalReturnEmptySource
import Candidate.C092.transport.RegularFramePriceLoss
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularFramePhysicalReturn
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily CenteredMomentEnergyBands
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional
open LocalMoment ProbePhysical Record12518109GainRoot
open QRH.Cycle092 QRH.Cycle092.SixthCore QRH.Cycle092.WholeSlot QRH.Cycle092.StrongPair QRH.Cycle092.RegularColoredForward
open QRH.Cycle092.TerminalProfileUniform QRH.Cycle092.PackedPrice
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Packet.Reduce
open ProfileSeparation (commonPair scale pairWeight)
local notation "O" => HeckeFamily.O

theorem empty_frame_metadata (D : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0< C) :
    ∃J : ℕ,∃Cterm : ℝ,0< Cterm ∧
    ∀ {L mesh U : ℝ} (theta : GData L),theta.N=0 →
    ∀ (eta omega1 omega2 : Character),theta.Q≤ omega1.modulus → theta.Q≤ omega2.modulus →
    ∀ (r : GSrc theta mesh U) (v Mrad Hsource Pbd delta : ℝ),Mrad≤2 →
      r.X₁≤ U^(3/4:ℝ) → r.X₂≤ U^(3/4:ℝ) → r.Y₁≤ U^(3/4:ℝ) → r.Y₂≤ U^(3/4:ℝ) →
      3*U^(3/4:ℝ)≤ U →
      (∀j:DictIdx,EmptyAt U delta ((anchors eta j).product omega1) ((anchors eta j).product omega2)
        (internalQ theta.Q (theta.η₀.product omega1)) (internalQ theta.Q (theta.η₀.product omega2)) D S C) →
      frameRectangularLeaves theta eta omega1 omega2 r v Mrad Hsource delta
        (Cterm*r.height^D*(1+‖v‖)^(2*D)) Pbd J := by
  obtain ⟨J,K,hK,hpayment⟩ := common_pair_payment S (C:=1) (by norm_num)
  refine ⟨J,C*K*frameHeightConstant^D,by unfold frameHeightConstant;positivity,?_⟩
  intro L mesh U theta hN eta omega1 omega2 hQ1 hQ2 r v Mrad Hsource Pbd delta hM2 hX1 hX2 hY1 hY2 hcollar hsource
  intro A j Y1 Y2 hY1p hY2p hrect _hlen _hPbd
  dsimp only
  intro e tau R hR B hB D1 hD1 D2 hD2 T
  have hg := terminal_cofactor_geometry U Mrad r.hZ R (fun z hz=>(hR z hz).2) B hB
  have hT : T=∅ := by
    ext i
    have hh := i.val.isLt
    omega
  have hx1 : 0<(scale e.1*Y1)/(D1.absNorm:ℝ) ∧ (scale e.1*Y1)/(D1.absNorm:ℝ)≤ U := by
    rcases hrect with h|h
    · have hh := opened_le_three r.hZ r.hX₁ hY1p h.1 e.1 B D1 hD1
      exact ⟨hh.1,(hh.2.trans (mul_le_mul_of_nonneg_left hX1 (by norm_num))).trans hcollar⟩
    · have hh := opened_le_three r.hZ r.hY₁ hY1p h.1 e.1 B D1 hD1
      exact ⟨hh.1,(hh.2.trans (mul_le_mul_of_nonneg_left hY1 (by norm_num))).trans hcollar⟩
  have hx2 : 0<(scale e.2*Y2)/(D2.absNorm:ℝ) ∧ (scale e.2*Y2)/(D2.absNorm:ℝ)≤ U := by
    rcases hrect with h|h
    · have hh := opened_le_three r.hZ r.hX₂ hY2p h.2 e.2 B D2 hD2
      exact ⟨hh.1,(hh.2.trans (mul_le_mul_of_nonneg_left hX2 (by norm_num))).trans hcollar⟩
    · have hh := opened_le_three r.hZ r.hY₂ hY2p h.2 e.2 B D2 hD2
      exact ⟨hh.1,(hh.2.trans (mul_le_mul_of_nonneg_left hY2 (by norm_num))).trans hcollar⟩
  have hk (z:FreeRow) (hz:z∈sixthFreeFiber R B) : initialKeep (anchors eta j) (internalQ theta.Q theta.η₀) z.val :=
    (CofactorOrdinary.initialKeep_on_root _ _ z B).mp ((hR _ (MeasuredBall.fiber_mem hz)).1)
  have he := hsource j (coreWidth U Mrad B) hg.1 (hg.2.1.trans hM2) (commonPair e tau)
    (shiftedPitch r.t₁ v) (shiftedPitch r.t₂ v) _ _ hx1.1 hx2.1 hx1.2 hx2.2 (sixthFreeFiber R B)
    (fun z hz=>(FixedRayPair.product_keep theta.Q theta.η₀ (anchors eta j) omega1 hQ1 _).mpr (hk z hz))
    (fun z hz=>(FixedRayPair.product_keep theta.Q theta.η₀ (anchors eta j) omega2 hQ2 _).mpr (hk z hz)) hg.2.2
  change finiteEnergyOn T (sixthFreeFiber R B) _ _ _ _ _ _ _ _ _≤_
  rw [finiteEnergyOn,hT]
  simp only [Finset.prod_empty,mul_one]
  apply he.trans
  have hp := hpayment e tau
  simp only [one_pow,one_mul] at hp
  have hheightbase : 1+|shiftedPitch r.t₁ v|+|shiftedPitch r.t₂ v|≤
      1+|r.t+v|+2*|shiftedPitch r.t₁ v|+2*|shiftedPitch r.t₂ v|+r.Vf := by
    linarith [abs_nonneg (r.t+v),abs_nonneg (shiftedPitch r.t₁ v),abs_nonneg (shiftedPitch r.t₂ v),r.hVf]
  have hheight := (pow_le_pow_left₀ (by positivity) hheightbase D).trans (frame_height_power r v D)
  have hhp : 0≤ K*pairWeight J tau := (sq_nonneg _).trans hp
  have hu : 0< U := zero_lt_one.trans r.hZ
  have hpow : U^(coreWidth U Mrad B+delta)≤ U^(coreWidth U Mrad B+delta+(5/6)*max 0 (Hsource-coreWidth U Mrad B)) :=
    Real.rpow_le_rpow_of_exponent_le r.hZ.le (by linarith [le_max_left (0:ℝ) (Hsource-coreWidth U Mrad B)])
  calc
    _ ≤ C*(K*pairWeight J tau)*((frameHeightConstant^D*r.height^D)*(1+‖v‖)^(2*D))*
      U^(coreWidth U Mrad B+delta+(5/6)*max 0 (Hsource-coreWidth U Mrad B)) := by
      have hHC : 0≤frameHeightConstant := by unfold frameHeightConstant;positivity
      have hRH : 0≤r.height := zero_le_one.trans r.one_le_height
      gcongr <;> positivity
    _ = _ := by ring

end
end QRH.Cycle092.RegularFramePhysicalReturn
#print axioms QRH.Cycle092.RegularFramePhysicalReturn.empty_frame_metadata
