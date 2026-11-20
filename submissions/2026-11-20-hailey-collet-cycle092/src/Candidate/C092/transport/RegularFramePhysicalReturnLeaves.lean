/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine original/reference physical source returns to the literal native
rectangle leaf, on actual occupied sixth-free fibers and independent divisors. -/
import Candidate.C092.transport.RegularFramePhysicalReturnSources
import Candidate.C092.transport.RegularFrameHeightBudget
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
open QRH.Cycle092 QRH.Cycle092.SixthCore
open QRH.Cycle092.WholeSlot QRH.Cycle092.StrongPair QRH.Cycle092.RegularColoredForward
open QRH.Cycle092.ReferenceArmRadial QRH.Cycle092.TerminalProfileUniform
open QRH.Cycle092.PackedPrice
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Packet.Reduce
open ProfileSeparation (commonPair scale pairWeight)
local notation "O" => HeckeFamily.O

 theorem opened_le_three {U X Y : ℝ} (hU : 1< U) (hX : 0< X) (hY : 0< Y) (hYX : Y≤2*X)
    (e : Fin 2) (B : HeckeInverseAmplification.NonzeroIdeal) (D : Ideal O) (hD : D∈IdealMobiusDivisorSum.idealDivisors B.val) :
    0<(scale e*Y)/(D.absNorm:ℝ) ∧ (scale e*Y)/(D.absNorm:ℝ)≤3*X := by
  have hDn : (1:ℝ)≤(D.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (ne_zero_of_dvd_ne_zero B.property ((IdealMobiusDivisorSum.mem_idealDivisors B.property).mp hD)))
  have hp := mul_pos (ProfileSeparation.scale_pos e) hY
  refine ⟨div_pos hp (zero_lt_one.trans_le hDn),?_⟩
  exact (div_le_self hp.le hDn).trans (by nlinarith [(ProfileSeparation.scale_mem e).2])

theorem rectangle_frame_metadata (D : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0< C) :
    ∃J : ℕ,∃Cterm : ℝ,0< Cterm ∧
    ∀ {L mesh U n y : ℝ} (theta : GData L) (eta omega1 omega2 : Character)
      (r : GSrc theta mesh U) (v Mrad Pbd : ℝ),Mrad≤2 →
      r.X₁≤ U^n → r.X₂≤ U^y → r.Y₁≤ U^(23/200:ℝ) → r.Y₂≤ U^(18023/25000:ℝ) →
      (∑i,r.w i)≤ sourceWidth n y-(u:ℝ) →
      (∀X Y : ℝ,0< X → 0< Y → length U X≤(23/200:ℝ)+length U 3 →
        length U Y≤(18023/25000:ℝ)+length U 3 → X≤ U^shortCap ∧ Y≤ U) →
      (∀j:DictIdx,PhysicalArmsAt (Fin theta.N) theta.rayM theta.Hray theta.hH theta.W n y mesh U
        (anchors eta j) theta.η₀ omega1 omega2 theta.Q D S C) →
      frameRectangularLeaves theta eta omega1 omega2 r v Mrad (H:ℝ) ((u:ℝ)-StrongPair.terminalReserve)
        (Cterm*r.height^D*(1+‖v‖)^(2*D)) Pbd J := by
  obtain ⟨J,K,hK,hpayment⟩ := common_pair_payment S (C:=1) (by norm_num)
  refine ⟨J,C*K*frameHeightConstant^D,by unfold frameHeightConstant;positivity,?_⟩
  intro L mesh U n y theta eta omega1 omega2 r v Mrad Pbd hM2 hX1 hX2 hY1 hY2 hquota hcollar hsource
  intro A j Y1 Y2 hY1p hY2p hrect _hlen _hPbd
  dsimp only
  intro e tau R hR B hB D1 hD1 D2 hD2 T
  have hg := terminal_cofactor_geometry U Mrad r.hZ R (fun z hz=>(hR z hz).2) B hB
  let TT := T.map (Function.Embedding.subtype (fun i=> i∈A))
  have hsum : (∑i∈TT,r.w i)≤ sourceWidth n y-(u:ℝ) := by
    dsimp [TT]
    rw [Finset.sum_map]
    exact terminal_full_subset_quota r.w r.hw A T _ hquota
  have hcaps :
      (((scale e.1*Y1)/(D1.absNorm:ℝ)≤3*U^n ∧ (scale e.2*Y2)/(D2.absNorm:ℝ)≤3*U^y) ∨
        ((scale e.1*Y1)/(D1.absNorm:ℝ)≤ U^shortCap ∧ (scale e.2*Y2)/(D2.absNorm:ℝ)≤ U) ∨
        ((scale e.2*Y2)/(D2.absNorm:ℝ)≤ U^shortCap ∧ (scale e.1*Y1)/(D1.absNorm:ℝ)≤ U)) := by
    rcases hrect with h|h
    · exact Or.inl ⟨(opened_le_three r.hZ r.hX₁ hY1p h.1 e.1 B D1 hD1).2.trans
        (mul_le_mul_of_nonneg_left hX1 (by norm_num)),
        (opened_le_three r.hZ r.hX₂ hY2p h.2 e.2 B D2 hD2).2.trans
        (mul_le_mul_of_nonneg_left hX2 (by norm_num))⟩
    · have ho1 := terminal_divisor_length r.hZ r.hY₁ hY1p h.1 e.1 B D1 hD1
        (length_le_of_le_rpow U _ (23/200) r.hZ (by norm_num) hY1)
      have ho2 := terminal_divisor_length r.hZ r.hY₂ hY2p h.2 e.2 B D2 hD2
        (length_le_of_le_rpow U _ (18023/25000) r.hZ (by norm_num) hY2)
      exact Or.inr (Or.inl (hcollar _ _ ho1.1 ho2.1
        (by simpa only [length,show max (1:ℝ) 3=3 by norm_num] using ho1.2)
        (by simpa only [length,show max (1:ℝ) 3=3 by norm_num] using ho2.2)))
  have hx1 : 0<(scale e.1*Y1)/(D1.absNorm:ℝ) := by
    rcases hrect with h|h
    · exact (opened_le_three r.hZ r.hX₁ hY1p h.1 e.1 B D1 hD1).1
    · exact (opened_le_three r.hZ r.hY₁ hY1p h.1 e.1 B D1 hD1).1
  have hx2 : 0<(scale e.2*Y2)/(D2.absNorm:ℝ) := by
    rcases hrect with h|h
    · exact (opened_le_three r.hZ r.hX₂ hY2p h.2 e.2 B D2 hD2).1
    · exact (opened_le_three r.hZ r.hY₂ hY2p h.2 e.2 B D2 hD2).1
  have hk (z:FreeRow) (hz:z∈sixthFreeFiber R B) : initialKeep (anchors eta j) (internalQ theta.Q theta.η₀) z.val :=
    (QRH.Cycle092.CofactorOrdinary.initialKeep_on_root _ _ z B).mp ((hR _ (MeasuredBall.fiber_mem hz)).1)
  have he := hsource j (coreWidth U Mrad B) hg.1 (hg.2.1.trans hM2) TT r.χ r.w r.σ r.freq (r.t+v)
    (shiftedPitch r.t₁ v) (shiftedPitch r.t₂ v) r.Vf r.hw r.hwm r.hσ r.hVf r.hfreq hsum
    (commonPair e tau) _ _ hx1 hx2 hcaps (sixthFreeFiber R B) hk hg.2.2
  change finiteEnergyOn T (sixthFreeFiber R B) ((anchors eta j).product omega1) ((anchors eta j).product omega2)
    ((commonPair e tau).profile 0) ((commonPair e tau).profile 1) _ _ _ _
    (fun i z=> originalMark theta.rayM theta.Hray theta.hH (anchors eta j) theta.η₀ r.χ theta.W U r.w r.σ r.freq (r.t+v) i.val z)≤_
  apply (le_of_eq (finiteEnergyOn_subtype A T (sixthFreeFiber R B) ((anchors eta j).product omega1)
    ((anchors eta j).product omega2) ((commonPair e tau).profile 0) ((commonPair e tau).profile 1)
    (shiftedPitch r.t₁ v) (shiftedPitch r.t₂ v) _ _
    (originalMark theta.rayM theta.Hray theta.hH (anchors eta j) theta.η₀ r.χ theta.W U r.w r.σ r.freq (r.t+v)))).trans
  apply he.trans
  have hp := hpayment e tau
  simp only [one_pow,one_mul] at hp
  have hheight := frame_height_power r v D
  have hhp : 0≤ K*pairWeight J tau := (sq_nonneg _).trans hp
  have hu : 0< U := zero_lt_one.trans r.hZ
  calc
    _ ≤ C*(K*pairWeight J tau)*((frameHeightConstant^D*r.height^D)*(1+‖v‖)^(2*D))*U^(terminalFramePrice (coreWidth U Mrad B)) := by
      have hvf := r.hVf
      gcongr
    _ = _ := by simp only [terminalFramePrice,sub_eq_add_neg,add_assoc];ring

end
end QRH.Cycle092.RegularFramePhysicalReturn
#print axioms QRH.Cycle092.RegularFramePhysicalReturn.rectangle_frame_metadata
