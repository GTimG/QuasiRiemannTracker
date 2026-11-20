/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine reference source acts on the unchanged common physical mark.
Only fixed bounded bad-color slots are discarded, uniformly before live data. -/
import Candidate.C092.transport.RegularFramePhysicalReturnInterface
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularFramePhysicalReturn
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily CenteredMomentEnergyBands
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional
open QRH.Cycle092.WholeSlot QRH.Cycle092.StrongPair QRH.Cycle092.FixedRayPair
open QRH.Cycle092.ReferenceArmRadial
local notation "O" => HeckeFamily.O

theorem physical_reference_source (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (M : Ideal O) [NeZero M] (Hr : Subgroup (O⧸M)ˣ) (hHr : RayOrthogonality.globalUnits M≤ Hr)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (bPhi : ℝ) (hbPhi : 0< bPhi) (hPhi : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi)
    (old baseChar omega1 omega2 : Character) (Q : Ideal O)
    (hQM : Q≤ M) (hQ0 : internalQ Q baseChar≠0) (hQt : internalQ Q baseChar≠⊤)
    (hQ72 : internalQ Q baseChar≤ Ideal.span {(72:O)}) (hQ1 : Q≤ omega1.modulus) (hQ2 : Q≤ omega2.modulus) :
    ∃degree : ℕ,∃controls : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧
    ∀ᶠ U : ℝ in atTop,1< U ∧
    ∀V : ℝ,0≤ V → V≤2 → ∀ (T : Finset Slot) (theta : Slot→RayQuotient.Characters M Hr)
      (w sigma freq : Slot→ℝ) (tOld t1 t2 height : ℝ),
      (∀i,0≤ w i) → (∀i,sigma i=33/50) → (∑i∈T,w i)≤ widthCap →
    ∀ (p : Profiles (1/4) (9/4)) (X1 X2 : ℝ),0≤ height → 0< X1 → 0< X2 →
      ((X1≤ U^shortCap ∧ X2≤ U) ∨ (X2≤ U^shortCap ∧ X1≤ U)) →
    ∀rows : Finset FreeRow,(∀z∈rows,initialKeep old (internalQ Q baseChar) z.val) →
      (∀z∈rows,rowNorm z≤ U^V) →
      finiteEnergyOn T rows (old.product omega1) (old.product omega2)
        (p.profile 0) (p.profile 1) t1 t2 X1 X2 (originalMark M Hr hHr old baseChar theta W U w sigma freq tOld)≤
      C*(p.control controls)^2*(1+|t1|+|t1|+|t2|+|t2|+height)^degree*U^(terminalFramePrice V) := by
  have hq1 := internalQ_product Q baseChar omega1 hQ1
  have hq2 := internalQ_product Q baseChar omega2 hQ2
  obtain ⟨d,S,C,hC,hsource⟩ := actual_reference_either_arm Slot hbeta M Hr hHr W hW hWs bPhi hbPhi hPhi
    (old.product omega1) (old.product omega2) (baseChar.product omega1) (baseChar.product omega2) Q Q
    hQM (hq1 ▸ hQ0) (hq1 ▸ hQt) (hq1 ▸ hQ72) hQM (hq2 ▸ hQ0) (hq2 ▸ hQt) (hq2 ▸ hQ72)
  obtain ⟨B,hB,hsupport⟩ := original_product_support (Slot:=Slot) M Hr hHr W hW hWs omega1 omega2
  refine ⟨d,S,B^(2*Fintype.card Slot)*C,by positivity,?_⟩
  filter_upwards [hsource] with U hU
  refine ⟨hU.1,?_⟩
  intro V hV hV2 T theta w sigma freq tOld t1 t2 height hw hsigma hwidth p X1 X2 hh hX1 hX2 hrect rows hk hy
  obtain ⟨F,hFT,hFw,hm,hbound⟩ := hsupport U hU.1 old baseChar theta w sigma freq tOld t1 t2 hw
    (fun i=> by rw [hsigma i];norm_num) T
  have he := hU.2 V hV hV2 F theta theta w sigma (fun i=> tOld+freq i-t1) (fun i=> tOld+freq i-t2)
    (fun i _=> by rw [hsigma i]) (fun i _=> by rw [hsigma i]) (hFw.trans hwidth) p t1 t2 height X1 X2
    hh hX1 hX2 hrect rows (originalMark M Hr hHr old baseChar theta W U w sigma freq tOld)
    (fun z hz=>(product_keep Q baseChar old omega1 hQ1 _).mpr (hk z hz))
    (fun z hz=>(product_keep Q baseChar old omega2 hQ2 _).mpr (hk z hz)) hy
    (fun z _ i hi=>(hm z i hi).1) (fun z _ i hi=>(hm z i hi).2)
  exact (hbound rows (p.profile 0) (p.profile 1) X1 X2).trans
    ((mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by ring))

end
end QRH.Cycle092.RegularFramePhysicalReturn
#print axioms QRH.Cycle092.RegularFramePhysicalReturn.physical_reference_source
