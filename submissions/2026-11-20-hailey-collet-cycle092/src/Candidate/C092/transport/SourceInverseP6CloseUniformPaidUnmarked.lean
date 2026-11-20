/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
P.6 with independent retained-long relative base. Adapted from the checked
SourceInverseP6Actual proof; the actual source dictionary keeps its original
base while the retained long prime slot is re-anchored separately. -/
import Candidate.C092.transport.SourceInverseP6CloseUniformUnmarkedEnergy
import Candidate.C092.transport.SourceInverseP6CloseConductor
import Candidate.C092.transport.MediumReplaceSourceUpper
import Candidate.C092.transport.MediumInversePriceJoin
import Candidate.C092.transport.WitnessConductorBank

namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators ContDiff SchwartzMap
open Filter Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentWholeSlotDeletion HeckeDetectorRowwisePolynomial
open HeckeDetectorInverseFiberCount HeckeDetectorSupportedWitness HeckeDetectorWitnessRows
open CenteredMomentPrimeSlot CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands ConcretePrimeRowBridge
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
open CenteredMomentInductionEnergy
open QRH.Cycle092.PairMarkAnchor QRH.Cycle092.LowActual
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness
open Qrh.MarkedAnchor.Interface QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.MediumInversePrice QRH.Cycle092.TinyCore
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_SourceInverseP6CloseUniformPaidUnmarked_e3f726786ce14865_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem uniform_attaining_unmarked_source_P6_paid
    {n yCell e0 nu0 loss : ℝ} (c : Cutoff)
    (hy0 : (369/1000:ℝ) ≤ yCell) (hy1 : yCell ≤ sourceY)
    (hn : n ≤ sourceRatio*yCell) (he0 : 0 ≤ e0) (hnub : e0 ≤ nu0) (hnu1 : nu0 ≤ 3/4)
    {bcell : ℚ} (hg : CutoffGuard bcell c) (hpaid : PaidWithBand yCell e0 nu0 c) (hloss : 0 < loss)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (εm nativeError : ℝ) (hεm : 0 < εm) (hnativeError : 0 < nativeError)
    {N quota : ℝ} (hN : N ≤ 1/2) (hq0 : 0 ≤ quota) (hqcap : quota < 3/20) (hqmean : quota < (1-2*N)/2)
    (dmin dmax : ℝ) (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) :
    ∃ step δ fee : ℝ,0 < step ∧ 0 < δ ∧ 0 < fee ∧ step=loss/10 ∧ δ=loss/10 ∧ 3*δ+2*step ≤ loss ∧
    ∃ nativeMesh : ℝ,0 < nativeMesh ∧
    ∀ (Slot : Type*) [Fintype Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ→ℂ) (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (η η₀ ηlong : Character) (Q : Ideal O) (hQM : Q ≤ M) (hQ0 : internalQ Q (anchoredBase η₀ η ηlong) ≠ 0)
    (hQt : internalQ Q (anchoredBase η₀ η ηlong) ≠ ⊤) (hQ72 : internalQ Q (anchoredBase η₀ η ηlong) ≤ Ideal.span {(72:O)})
    (bΦ : ℝ) (hbΦ : 2 ≤ bΦ)
    (hsΦ : Function.support (radialMajorant : ℝ→ℂ) ⊆ Iic bΦ),
    ∃ Fbound : ℝ,0 < Fbound ∧
    ∀ (buffer Cslot : ℝ),0 < buffer → 0 < Cslot →
    let b := buffer/2;
    let Kbig := ⌈(7/37:ℝ)/(b/dmax)⌉₊+1;
    ∃ Jc : Fin (Kbig+1)→ℕ,
    ∃ Cc : Fin (Kbig+1)→ℝ,
    ∃ degree : Fin (Kbig+1)→ℕ,
    ∃ controls : Fin (Kbig+1)→Finset (ℕ×ℕ),
    ∃ Cl : Fin (Kbig+1)→ℝ,
      (∀ kl,0 < Cc kl ∧ 0 < Cl kl) ∧
    ∀ (Mcap Bmask margin R τ εshort ez κ heightCost : ℝ)
    (hmargin : 0 < margin) (hR : 0 ≤ R)
    (hτ : 0 < τ) (hheight : 4*τ < dmin*heightCost) (hεshort : 0 < εshort)
    (hez : 0 < ez) (hez' : ez < 1/1000) (hκ : 0 < κ) (hκ' : κ ≤ 1) (hcost : 0 ≤ heightCost)
    (hbudget : 12*ez*(R+2)+8*κ+2*heightCost ≤ εshort)
    (profileBound : ℕ→ℝ) (hprofile : ∀ j,0 ≤ profileBound j) ,
    ∃ order : Fin (Kbig+1)→ℕ,∃ Cy : Fin (Kbig+1)→ℝ,(∀ kl,0 < Cy kl) ∧
    ∀ I : ℕ,
    ∀ᶠ Z : ℝ in atTop,1 < Z ∧
    ∀ d : ℝ,dmin ≤ d → d ≤ dmax → Mcap+Bmask+margin ≤ d →
    ∀ s : NaturalState Z Bmask bΦ,s.width ≤ Mcap → s.character=η → s.puncture=1 →
    ∀ (hsM : s.fixedModulus ≤ M) (hsη : s.fixedModulus ≤ η₀.modulus)
      (rows : Finset FreeRow) (hkeep : ∀ u∈rows,s.radial.keep u.val),
      (∀ u∈rows,s.radial.profile (‖ConcreteTraceCRT.eisEmbedding u.val‖^2/s.radial.scale) ≠ 0) →
      (∀ u∈rows,rowNorm u ≤ Z^d) →
    ∀ (a ε cutoff T allowance : ℝ) (i : ℕ),51/100 ≤ a → a ≤ 1 → i ≤ I →
      0 ≤ ε → ε ≤ 1/1000 → 1 ≤ cutoff → cutoff ≤ 3/2 →
    let F := fun u : FreeRow => naturalRow s.character u.val u.property.1
    ∀ ws : ∀ u : rows,SupportedWitness (family M H hH s η₀ (F u.val)) (Z^d) a ε cutoff T allowance i,
    ∀ (label : Option (RayQuotient.Characters M H × RayQuotient.Characters M H))
      (left right : Fin (dyadicLength (Z^d))),
      (∀ u,(ws u).label=label) → (∀ u,(ws u).left=left) → (∀ u,(ws u).right=right) →
    let r := Real.logb (Z^d) ((2:ℝ)^left.val);

      (∀ u : rows,HeckeDetectorZeros.zeroMaximum (family M H hH s η₀ (F u.val))
        (family_nonprincipal M H hH s η₀ hsM hsη (hkeep u.val u.property) (F u.val))
        (3*(i+1 : ℕ)*Z^τ) < a+2*ez) →
    ∀ (Wi : FreeRow→ℝ→ℂ) (Ai Bi σi fi : FreeRow→ℝ),
      0 ≤ yCell → yCell/d ≤ R →
      (∀ u∈rows,0 < Ai u) → (∀ u∈rows,Function.support (Wi u) ⊆ Icc (Ai u) (Bi u)) →
      (∀ u∈rows,ContDiff ℝ ∞ (Wi u)) →
      (∀ u∈rows,|fi u|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
      (∀ u∈rows,∀ x∈Icc (1-a-6*ez-σi u) (2-σi u),∀ t:ℝ,
        (1+|t|)^2*‖mellin (Wi u) ((x:ℂ)+t*Complex.I)‖ ≤ profileBound 2) →
      (∀ kl : Fin (Kbig+1),∀ u∈rows,∀ x∈Icc (1-a-6*ez-σi u) (2-σi u),∀ t:ℝ,
        (1+|t|)^(order kl+2)*‖mellin (Wi u) ((x:ℂ)+t*Complex.I)‖ ≤ profileBound (order kl+2)) →
    ∀ (θ : Slot→RayQuotient.Characters M H) (w v : Slot→ℝ)
      (tMark tLong slotHeight eu L X V : ℝ),
      (∀ j,0 ≤ w j) → (∀ j,w j/d ≤ nativeMesh) →
      0 ≤ slotHeight → (∀ j,|v j| ≤ slotHeight) →
      0 ≤ eu →
      (∑ j,w j) ≤ L →
      0 < X → length (Z^d) X ≤ N →
      (∀ u∈rows,initialKeep ηlong (internalQ Q (anchoredBase η₀ η ηlong)) u.val) →
      (98/100:ℝ) ≤ V → V ≤ d → d ≤ V+3*δ →
      nu0 ≤ 2*a-1 → 2*a-1 ≤ nu0+step → eu ≤ e0+step →
      (c.inverse:ℝ) ≤ r → cutoff=totalCutoff c → ε ≤ fee →
      0 ≤ L → L ≤ 1 → L ≤ sourceWidth n yCell-(u:ℝ) →
      2*NativeFourthEffective.credit n d-d*quota ≤ fee/2 →
      (r ≤ 1 → inverseQuota r ≤ fee) →
      d*εshort+(d*(2*ε+εm)+d*nativeError)/2+buffer*(Fintype.card Slot:ℝ) ≤ fee →
    ∀ (jd : Slot) (p : Profiles (1/4) (9/4)) (jprofile : Fin 2),
    let selectedRows := descriptorRows M H hH rows η η₀ W Z (Cslot*Z^buffer) b θ w v tMark jd;
      selectedRows.Nonempty →
      (∀ u∈selectedRows,e0 ≤ measured M H hH η η₀ W Z (Cslot*Z^buffer) θ w v tMark u) →
      (∀ u∈selectedRows,measured M H hH η η₀ W Z (Cslot*Z^buffer) θ w v tMark u ≤ eu) →
    let hi := max (|tMark|+slotHeight) (2*Real.pi*allowance+(3*i:ℕ)*T);
    let hl := |tMark|+|tLong|+slotHeight;
    ∃ kl : Fin (Kbig+1),
    (∑ u∈selectedRows,‖original ηlong (fixedBadMask*idealGenerator 1) 1 u.val
      (p.profile jprofile) tLong X*
      original s.character s.mask 1 u.val (twistProfile (Wi u) (σi u) (fi u)) 0 (Z^yCell)*
      (∏ j,descriptor M H hH η η₀ W Z θ w v tMark u j)‖^2) ≤
      Cslot^(Fintype.card Slot)*Cy kl*Real.sqrt (192*(1+hi)*(Cc kl*(1+hi)^(Jc kl)))*
        Real.sqrt (Cl kl*QuadraticInitialBound.diagonalControl radialMajorant*
          (sourceControl (controls kl) (p.profile jprofile))^4*(1+|tLong|+hl)^(degree kl))*
      Z^(V+radialAllowance V+loss) := by
  obtain ⟨step,δ,fee,hstep,hδ,hfee,hstepEq,hδEq,hwindow,hprice⟩ := actual_inverse_alternatives_paid c hy0 hy1 he0 hnub hnu1 hg hpaid hloss
  obtain ⟨nm,hnm,huniform⟩ := uniform_attaining_unmarked_source_P6
    hβ εm nativeError hεm hnativeError hN hq0 hqcap hqmean dmin dmax hdmin hdmax
  have hdmaxp : 0 < dmax := hdmin.trans_le hdmax
  let nmOut := min nm (fee/(2*dmax))
  have hnmOut : 0 < nmOut := lt_min hnm (by positivity)
  refine ⟨step,δ,fee,hstep,hδ,hfee,hstepEq,hδEq,hwindow,nmOut,hnmOut,?_⟩
  intro Slot _ M _ H hH W hWs hW η η₀ ηlong Q hQM hQ0 hQt hQ72 bΦ hbΦ hsΦ
  obtain ⟨Fb,hFb,hleaf⟩ := huniform Slot M H hH W hWs hW η η₀ ηlong Q hQM hQ0 hQt hQ72 bΦ hbΦ hsΦ
  refine ⟨Fb,hFb,?_⟩
  intro buffer Cslot hbuffer hCslot
  dsimp only
  let b := buffer/2
  have hb : 0 < b := by dsimp [b];positivity
  obtain ⟨Jc,Cc,degree,controls,Cl,hpos,hlate⟩ := hleaf b hb
  refine ⟨Jc,Cc,degree,controls,Cl,hpos,?_⟩
  intro Mcap Bmask margin R τ εshort ez κ heightCost hmargin hR hτ hheight hεshort hez hez' hκ hκ' hcost hbudget profileBound hprofile
  obtain ⟨order,Cy,hCy,hbounds⟩ := hlate Mcap Bmask margin R τ εshort ez κ heightCost
    hmargin hR hτ hheight hεshort hez hez' hκ hκ' hcost hbudget profileBound hprofile
  refine ⟨order,Cy,hCy,?_⟩
  intro I
  have hcalib : ∀ᶠ Z : ℝ in atTop,1 ≤ Cslot*Z^buffer ∧ Fb*Z^b ≤ Cslot*Z^buffer := by
    filter_upwards [(tendsto_rpow_atTop hbuffer).eventually (eventually_ge_atTop (1/Cslot)),
      (tendsto_rpow_atTop hb).eventually (eventually_ge_atTop (Fb/Cslot)),
      eventually_gt_atTop (0:ℝ)] with Z h1 h2 hZ
    refine ⟨by simpa only [mul_comm] using (div_le_iff₀ hCslot).mp h1,?_⟩
    have hf : Fb ≤ Cslot*Z^b := by simpa only [mul_comm] using (div_le_iff₀ hCslot).mp h2
    calc
      Fb*Z^b ≤ (Cslot*Z^b)*Z^b := mul_le_mul_of_nonneg_right hf (Real.rpow_nonneg hZ.le b)
      _ = Cslot*Z^buffer := by rw [mul_assoc,←Real.rpow_add hZ,show b+b=buffer by dsimp [b];ring]
  filter_upwards [hbounds I,hcalib] with Z hZleaf hcalib
  refine ⟨hZleaf.1,?_⟩
  intro d hd hd' hds s hswidth hη hp hsM hsη rows hkeep hΦ hnorm a ε cutoff T allowance i ha ha' hiI hε hεmax hcut hcutmax
  try dsimp only
  intro ws label left right hlabel hleft hright
  let r := Real.logb (Z^d) ((2:ℝ)^left.val)
  intro hnext Wi Ai Bi σi fi hy hyr hAi hWi hsm hfi hm₂ hmn
    θ w v tMark tLong slotHeight eu L X V hw hmesh hheight hv heu hwidth
    hX hXN hkeepLong hV hVd hdV hnul hnuu heuu hri hcutoffEq hεfee hL0 hL hLive hNativeBudget hInverseBudget hError
    jd p jprofile
  try dsimp only
  intro hne hlow hupp
  have hmeshOld (j : Slot) : w j/d ≤ nm := (hmesh j).trans (min_le_left _ _)
  have hwnarrow : w jd/d ≤ fee/(2*dmax) := (hmesh jd).trans (min_le_right _ _)
  obtain ⟨kl,hNatUp,hNatLo,hE⟩ := hZleaf.2 d hd hd' hds s hswidth hη hp hsM hsη rows hkeep hΦ hnorm
    a ε cutoff T allowance i ha ha' hiI hε hεmax hcut hcutmax ws label left right hlabel hleft hright hnext Wi Ai Bi σi fi yCell hy hyr
    hAi hWi hsm hfi hm₂ hmn θ w v tMark tLong slotHeight e0 eu L (Cslot*Z^buffer) X
    hw hmeshOld hheight hv hcalib.1 hcalib.2 he0 heu hwidth hX hXN hkeepLong
    jd p jprofile hne hlow hupp
  refine ⟨kl,?_⟩
  let nativeLoss := 2*NativeFourthEffective.credit n d-d*(quota-w jd/d)
  let inverseLoss := inverseQuota r
  let error := d*εshort+(d*(2*ε+εm)+d*nativeError)/2+buffer*(Fintype.card Slot:ℝ)
  have hdp : 0 < d := hdmin.trans_le hd
  have hwabsFee : w jd ≤ fee/2 := by
    have h1 := (div_le_iff₀ hdp).mp hwnarrow
    have h2 := mul_le_mul_of_nonneg_left hd' (div_nonneg hfee.le (by positivity : (0:ℝ) ≤ 2*dmax))
    have h3 : fee/(2*dmax)*dmax=fee/2 := by field_simp
    exact h1.trans (h2.trans_eq h3)
  have hnativeFee : nativeLoss ≤ fee := by
    dsimp only [nativeLoss]
    have heq : d*(quota-w jd/d)=d*quota-w jd := by field_simp <;> ring
    rw [heq]
    linarith
  have hT : 1 ≤ (c.inverse:ℝ)+(c.ordinary:ℝ) := (cutoff_detector_domain c hg).1
  obtain ⟨u0,hu0⟩ := hne
  have huRows : u0∈rows := (Finset.mem_filter.mp hu0).1
  have hrT : r ≤ (c.inverse:ℝ)+(c.ordinary:ℝ)+ε := by
    have hh := (ws ⟨u0,huRows⟩).inverse_length_upper
    have heq := (ws ⟨u0,huRows⟩).toWitness.left_exponent
      (Real.one_lt_rpow hZleaf.1 (hdmin.trans_le hd))
    rw [hleft ⟨u0,huRows⟩] at heq
    rw [heq,hcutoffEq] at hh
    exact hh
  have hInvFee : inverseLoss ≤ fee := by
    dsimp only [inverseLoss]
    by_cases hrs : r ≤ 1
    · exact hInverseBudget hrs
    · rw [inverseQuota_native (by linarith : (7/9:ℝ) ≤ r)]
      linarith [hfee.le]
  have hpaidPower := hprice n V d (2*a-1) eu r L ((kl.val:ℝ)*(w jd)) 0
    nativeLoss inverseLoss ε error hn hV hVd hdV hnul hnuu heuu hri hrT
    hL0 hL hLive (by dsimp [nativeLoss];linarith) (fun _=>by dsimp [inverseLoss];linarith)
    hnativeFee hInvFee hε hεfee hError
  simp only [ite_self] at hpaidPower
  unfold roundedSourcePrice at hpaidPower
  simp only [mul_zero,add_zero] at hpaidPower
  let hi := max (|tMark|+slotHeight) (2*Real.pi*allowance+(3*i:ℕ)*T)
  let hl := |tMark|+|tLong|+slotHeight
  have hCyPair := hCy kl
  let Cbase := Cy kl*Real.sqrt (192*(1+hi)*(Cc kl*(1+hi)^(Jc kl)))*
    Real.sqrt (Cl kl*QuadraticInitialBound.diagonalControl radialMajorant*
      (sourceControl (controls kl) (p.profile jprofile))^4*(1+|tLong|+hl)^(degree kl))
  let power := d+(2*a-1)*yCell+e0*(L-(kl.val:ℝ)*(w jd)/2)-
    d*unmarkedDeficit (2*a-1) r/2+
    d*εshort+(d*(2*ε+εm)+d*nativeError)/2+(eu-e0)*L
  have hpaidPower' : power+buffer*(Fintype.card Slot:ℝ) < V+radialAllowance V+loss := by
    dsimp [power,error] at *
    linarith
  have hZp := zero_lt_one.trans hZleaf.1
  have hE' : (∑ u∈descriptorRows M H hH rows η η₀ W Z (Cslot*Z^buffer) b θ w v tMark jd,
      ‖original ηlong (fixedBadMask*idealGenerator 1) 1 u.val (p.profile jprofile) tLong X*
        original s.character s.mask 1 u.val (twistProfile (Wi u) (σi u) (fi u)) 0 (Z^yCell)*
        (∏ j,descriptor M H hH η η₀ W Z θ w v tMark u j)‖^2) ≤
      Cslot^(Fintype.card Slot)*Cbase*Z^(power+buffer*(Fintype.card Slot:ℝ)) := by
    apply hE.trans_eq
    dsimp only [Cbase,power,hi,hl]
    rw [mul_pow,←Real.rpow_mul_natCast hZp.le]
    conv_rhs => rw [Real.rpow_add hZp]
    ring
  have hCbase : 0 ≤ Cbase := by dsimp [Cbase];positivity
  have hscale := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZleaf.1.le hpaidPower'.le)
    (mul_nonneg (pow_nonneg hCslot.le (Fintype.card Slot)) hCbase)
  convert hE'.trans hscale using 1 <;> dsimp only [Cbase,hi,hl] <;> ring

#print axioms uniform_attaining_unmarked_source_P6_paid
end
end QRH.Cycle092.SourceInverseP6
