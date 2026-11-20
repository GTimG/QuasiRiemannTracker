/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Original-arm all-radius P2 consumes the literal factor-three opened scales
at base64U, with exactly the same original prime slots, marks and finite rows. -/
import Candidate.C092.transport.RegularFramePhysicalReturnBase
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

theorem physical_original_source (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (Hr : Subgroup (O⧸M)ˣ) (hHr : RayOrthogonality.globalUnits M≤ Hr)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (n y mesh : ℝ) (hn : (1/3:ℝ)≤ n) (hy : (1/3:ℝ)≤ y)
    (old baseChar omega1 omega2 : Character) (Q : Ideal O)
    (degree : ℕ) (controls : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0< C)
    (hP2 : ∀ᶠ Z : ℝ in atTop,OrderedP2At Slot M Hr hHr W n y mesh Z old baseChar omega1 omega2 Q degree controls C)
    (hQ1 : Q≤ omega1.modulus) (hQ2 : Q≤ omega2.modulus) :
    ∃K : ℝ,0< K ∧ ∀ᶠ U : ℝ in atTop,1< U ∧ ∀
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
    (hrow : ∀z∈rows,rowNorm z≤ U^V),
    finiteEnergyOn T rows (old.product omega1) (old.product omega2)
      (p.profile 0) (p.profile 1) t1 t2 X1 X2 (originalMark M Hr hHr old baseChar theta W U w sigma freq tOld)≤
      K*(p.control controls)^2*
        (1+|t1|+|t2|+height)^degree*U^(terminalFramePrice V) := by
  obtain ⟨B,hB,hsupport⟩ := QRH.Cycle092.FixedRayPair.original_product_support (Slot:=Slot) M Hr hHr W hW hWs omega1 omega2
  let K := B^(2*Fintype.card Slot)*(C*factor^((u:ℝ)-terminalReserve+(5/6)*(H:ℝ)))
  have hf : (0:ℝ)<factor := by norm_num [factor]
  have hB0 : 0<B := zero_lt_one.trans_le hB
  refine ⟨K,by dsimp [K];positivity,?_⟩
  obtain ⟨Z0,hZ0⟩ := Filter.eventually_atTop.mp hP2
  filter_upwards [eventually_ge_atTop Z0,eventually_gt_atTop (1:ℝ)] with U hZ0U hU
  refine ⟨hU,?_⟩
  intro V hV hV2 T theta w sigma freq tOld t1 t2 height hw hwm hsigma hh ht hfreq hf1 hf2 hwidth
    p X1 X2 hX1 hX2 hcap1 hcap2 rows hk hrow
  have hb : U≤ base U := by dsimp [base,factor];linarith
  obtain ⟨F,hFT,hFw,hm,hbound⟩ := hsupport U hU old baseChar theta w sigma freq tOld t1 t2 hw
    (fun i=> by rw [hsigma i];norm_num) T
  have he := ordered_p2_fixed_base M Hr hHr W n y mesh U hU hn hy old baseChar omega1 omega2 Q
    degree controls C hC.le (hZ0 (base U) (hZ0U.trans hb)) V hV hV2 F theta w sigma freq tOld t1 t2 height
    hw hwm hsigma hh ht hfreq hf1 hf2 (hFw.trans hwidth) p X1 X2 hX1 hX2 hcap1 hcap2 rows hk
    (fun z hz=>(QRH.Cycle092.FixedRayPair.product_keep Q baseChar old omega1 hQ1 _).mpr (hk z hz))
    (fun z hz=>(QRH.Cycle092.FixedRayPair.product_keep Q baseChar old omega2 hQ2 _).mpr (hk z hz)) hrow
    (fun z _ i hi=>(hm z i hi).1) (fun z _ i hi=>(hm z i hi).2)
  exact (hbound rows (p.profile 0) (p.profile 1) X1 X2).trans
    ((mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by dsimp [K];ring))

end
end QRH.Cycle092.RegularFramePhysicalReturn
#print axioms QRH.Cycle092.RegularFramePhysicalReturn.physical_original_source
