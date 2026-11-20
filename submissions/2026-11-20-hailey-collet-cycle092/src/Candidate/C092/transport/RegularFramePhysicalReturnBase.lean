/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Original-arm all-radius P2 consumes the literal factor-three opened scales
at base64U, with exactly the same original prime slots, marks and finite rows. -/
import Candidate.C092.transport.RegularFramePhysicalReturnInterface
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularFramePhysicalReturn
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily CenteredMomentEnergyBands
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional
open QRH.Cycle092.WholeSlot QRH.Cycle092.StrongPair QRH.Cycle092.FixedBaseCollar
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source
local notation "O" => HeckeFamily.O

theorem ordered_p2_fixed_base {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (Hr : Subgroup (O⧸M)ˣ) (hHr : RayOrthogonality.globalUnits M≤ Hr)
    (W : ℝ→ℂ) (n y mesh U : ℝ) (hU : 1< U) (hn : (1/3:ℝ)≤ n) (hy : (1/3:ℝ)≤ y)
    (old baseChar omega1 omega2 : Character) (Q : Ideal O)
    (degree : ℕ) (controls : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤ C)
    (hP2 : OrderedP2At Slot M Hr hHr W n y mesh (base U) old baseChar omega1 omega2 Q degree controls C)
    (V : ℝ) (hV : 0≤ V) (hV2 : V≤2)
    (T : Finset Slot) (theta : Slot→RayQuotient.Characters M Hr)
    (w sigma freq : Slot→ℝ) (tOld t1 t2 height : ℝ)
    (hw : ∀i,0≤ w i) (hwm : ∀i,w i≤ mesh) (hsigma : ∀i,sigma i=33/50)
    (hh : 0≤ height) (ht : |tOld|≤ height) (hfreq : ∀i,|freq i|≤ height)
    (hf1 : ∀i,|tOld+freq i-t1|≤ height) (hf2 : ∀i,|tOld+freq i-t2|≤ height)
    (hwidth : (∑i∈T,w i)≤ sourceWidth n y-(u:ℝ))
    (p : Profiles (1/4) (9/4)) (X1 X2 : ℝ) (hX1 : 0< X1) (hX2 : 0< X2)
    (hcap1 : X1≤3*U^n) (hcap2 : X2≤3*U^y)
    (rows : Finset FreeRow)
    (hk : ∀z∈rows,initialKeep old (internalQ Q baseChar) z.val)
    (hk1 : ∀z∈rows,initialKeep (old.product omega1) (internalQ Q (baseChar.product omega1)) z.val)
    (hk2 : ∀z∈rows,initialKeep (old.product omega2) (internalQ Q (baseChar.product omega2)) z.val)
    (hrow : ∀z∈rows,rowNorm z≤ U^V)
    (hm1 : ∀z∈rows,∀i∈T,‖originalMark M Hr hHr old baseChar theta W U w sigma freq tOld i z‖=
      ‖originalMark M Hr hHr (old.product omega1) (baseChar.product omega1) theta W U w sigma
        (fun i=> tOld+freq i-t1) t1 i z‖)
    (hm2 : ∀z∈rows,∀i∈T,‖originalMark M Hr hHr old baseChar theta W U w sigma freq tOld i z‖=
      ‖originalMark M Hr hHr (old.product omega2) (baseChar.product omega2) theta W U w sigma
        (fun i=> tOld+freq i-t2) t2 i z‖) :
    finiteEnergyOn T rows (old.product omega1) (old.product omega2)
      (p.profile 0) (p.profile 1) t1 t2 X1 X2 (originalMark M Hr hHr old baseChar theta W U w sigma freq tOld)≤
      (C*factor^((u:ℝ)-terminalReserve+(5/6)*(H:ℝ)))*(p.control controls)^2*
        (1+|t1|+|t2|+height)^degree*U^(terminalFramePrice V) := by
  have hv := coord_range hU hV
  have hwc (i:Slot) := coord_range hU (hw i)
  have hsum : (∑i∈T,coord U (w i))≤ sourceWidth n y-(u:ℝ) :=
    (Finset.sum_le_sum (fun i _=>(hwc i).2)).trans hwidth
  have heq0 := original_mark M Hr hHr old baseChar theta W U hU w sigma freq tOld
  have heq1 := original_mark M Hr hHr (old.product omega1) (baseChar.product omega1)
    theta W U hU w sigma (fun i=> tOld+freq i-t1) t1
  have heq2 := original_mark M Hr hHr (old.product omega2) (baseChar.product omega2)
    theta W U hU w sigma (fun i=> tOld+freq i-t2) t2
  have he := hP2 (coord U V) hv.1 (hv.2.trans hV2) T theta (fun i=> coord U (w i)) sigma freq
    tOld t1 t2 height (fun i=>(hwc i).1) (fun i=>(hwc i).2.trans (hwm i)) hsigma hh ht hfreq hf1 hf2 hsum
    p X1 X2 hX1 hX2 (component hU hn (le_refl _) hcap1) (component hU hy (le_refl _) hcap2)
    rows hk hk1 hk2 (by simpa only [reconstruct hU] using hrow)
    (by simpa only [heq0,heq1] using hm1) (by simpa only [heq0,heq2] using hm2)
  have hH : 0≤(H:ℝ) := by norm_num [H,u]
  have hK : 0≤ C*(p.control controls)^2*(1+|t1|+|t2|+height)^degree := by positivity
  have he' := original_energy M Hr hHr (V:=V) (fee:=(u:ℝ)-terminalReserve) hU hH hK old baseChar (old.product omega1) (old.product omega2)
    theta W w sigma freq tOld T rows (p.profile 0) (p.profile 1) t1 t2 X1 X2
    (by convert he using 1 <;> unfold terminalFramePrice <;> ring)
  convert he' using 1 <;> unfold terminalFramePrice <;> ring

end
end QRH.Cycle092.RegularFramePhysicalReturn
#print axioms QRH.Cycle092.RegularFramePhysicalReturn.ordered_p2_fixed_base
