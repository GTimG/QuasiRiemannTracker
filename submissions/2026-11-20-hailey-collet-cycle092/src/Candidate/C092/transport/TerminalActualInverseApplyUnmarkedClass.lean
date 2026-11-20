import Candidate.C092.transport.RegularColoredTerminalLeafGuards
import Candidate.C092.transport.SourceInverseP6GeneralPairPrice
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
P.6 with independent retained-long relative base. Adapted from the checked
SourceInverseP6Actual proof; the actual source dictionary keeps its original
base while the retained long prime slot is re-anchored separately. -/
import Candidate.C092.transport.TerminalActualInverseApplyUnmarkedEnergy
import Candidate.C092.transport.SourceInverseP6CloseConductor
import Candidate.C092.transport.MediumReplaceSourceUpper
import Candidate.C092.transport.MediumInversePriceJoin
import Candidate.C092.transport.WitnessConductorBank

namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators ContDiff SchwartzMap
open QRH.Cycle092.RegularColoredForward QRH.Cycle092.StrongPair QRH.Cycle092.TerminalActualRow
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
local instance c092LocalInst_Candidate_C092_transport_TerminalActualInverseApplyUnmarkedClass_92a8f36fdf06096c_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem actual_class_unmarked_paid
    {n yCell e0 nu0 loss : ℝ} (c : Cutoff)
    (hy0 : (369/1000:ℝ) ≤ yCell) (hy1 : yCell ≤ sourceY)
    (hn : n ≤ sourceRatio*yCell) (he0 : 0 ≤ e0) (hnub : e0 ≤ nu0) (hnu1 : nu0 ≤ 3/4)
    {bcell : ℚ} (hg : CutoffGuard bcell c) (hpaid : PaidWithBand yCell e0 nu0 c) (hloss : 0 < loss)
 :
    ∃ step δ fee : ℝ,0 < step ∧ 0 < δ ∧ 0 < fee ∧ step=loss/10 ∧ δ=loss/10 ∧ 3*δ+2*step ≤ loss ∧
    ∀ (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (εm nativeError : ℝ) (hεm : 0 < εm) (hnativeError : 0 < nativeError)
    {N quota : ℝ} (hN : N ≤ 1/2) (hq0 : 0 ≤ quota) (hqcap : quota < 3/20) (hqmean : quota < (1-2*N)/2)
    (dmin dmax : ℝ) (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax)
    (price : ℝ) (hprice0 : 0 ≤ price) (hpriceBudget : price*dmax ≤ loss/4),
    ∃ nativeMesh : ℝ,0 < nativeMesh ∧
    ∀ (Slot : Type) [Fintype Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ→ℂ) (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (η η₀ ηlong baseLong : Character) (Q : Ideal O) (hQM : Q ≤ M) (hQ0 : internalQ Q baseLong ≠ 0)
    (hQt : internalQ Q baseLong ≠ ⊤) (hQ72 : internalQ Q baseLong ≤ Ideal.span {(72:O)})
    (bΦ : ℝ) (hbΦ : 2 ≤ bΦ)
    (hsΦ : Function.support (radialMajorant : ℝ→ℂ) ⊆ Iic bΦ),
    ∃ Fbound : ℝ,0 < Fbound ∧
    ∀ (buffer : ℝ),0 < buffer →
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
    (Bshort : ℝ) (hBshort : 0 ≤ Bshort)
    (profileBound : ℕ→ℝ) (hprofile : ∀ j,0 ≤ profileBound j) ,
    ∃ order : Fin (Kbig+1)→ℕ,∃ Cy : Fin (Kbig+1)→ℝ,(∀ kl,0 < Cy kl) ∧
    ∀ (I : ℕ) (Cslot : ℝ),0 < Cslot →
    ∀ᶠ Z : ℝ in atTop,1 < Z ∧
    ∀ d : ℝ,dmin ≤ d → d ≤ dmax → Mcap+Bmask+margin ≤ d →
    ∀ s : NaturalState Z Bmask bΦ,s.width ≤ Mcap → s.character=η → s.puncture=1 →
    ∀ (hsM : s.fixedModulus ≤ M) (hsη : s.fixedModulus ≤ η₀.modulus)
      (rows : Finset FreeRow) (hkeep : ∀ u∈rows,s.radial.keep u.val),
      (∀ u∈rows,s.radial.profile (‖ConcreteTraceCRT.eisEmbedding u.val‖^2/s.radial.scale) ≠ 0) →
      (∀ u∈rows,rowNorm u ≤ Z^d) →
    ∀ (K Je Jν : ℕ) (ε : ℝ)
      (level : rows→Fin (I+1)) (band : rows→Fin (K+1))
      (window : rows→Fin Je×Fin Jν) (cutoffTable : Fin Je×Fin Jν→ℝ)
      (parentWS : ∀ u : rows,SupportedWitness
        (family M H hH s η₀ (naturalRow s.character u.val.val u.val.property.1))
        (Z^d) ((51/100:ℝ)+ez*(band u).val) ε (cutoffTable (window u))
        (Z^τ) ((Z^d)^(τ/(2*dmax))) (level u).val)
      (tag : Fin (I+1)×Fin (K+1)×(Fin Je×Fin Jν)×
        Option (RayQuotient.Characters M H×RayQuotient.Characters M H)×
        Fin (dyadicLength (Z^d))×Fin (dyadicLength (Z^d))),
    let parentRows := rows;
    let a := (51/100:ℝ)+ez*tag.2.1.val;
    let i := tag.1.val;
    let cutoff := cutoffTable tag.2.2.1;
    let T := Z^τ;
    let allowance := (Z^d)^(τ/(2*dmax));
    let label := tag.2.2.2.1;
    let left := tag.2.2.2.2.1;
    let right := tag.2.2.2.2.2;
    let r := Real.logb (Z^d) ((2:ℝ)^left.val);
    let rows := classRows parentRows (terminalWitnessKey level band window cutoffTable parentWS) tag;
      a ≤ 1 →
      (∀ u : parentRows,HeckeDetectorZeros.zeroMaximum
        (family M H hH s η₀ (naturalRow s.character u.val.val u.val.property.1))
        (family_nonprincipal M H hH s η₀ hsM hsη (hkeep u.val u.property)
          (naturalRow s.character u.val.val u.val.property.1))
        (3*((level u).val+1 : ℕ)*Z^τ) < ((51/100:ℝ)+ez*(band u).val)+2*ez) →
      0 ≤ ε → ε ≤ 1/1000 → 1 ≤ cutoff → cutoff ≤ 3/2 →
    ∀ (Wi : FreeRow→ℝ→ℂ) (Ai Bi σi fi : FreeRow→ℝ) (Y : ℝ),
      0 ≤ yCell → yCell/d ≤ R → 0 < Y → Y ≤ Z^yCell →
      (∀ u∈rows,0 < Ai u) → (∀ u∈rows,Function.support (Wi u) ⊆ Icc (Ai u) (Bi u)) →
      (∀ u∈rows,ContDiff ℝ ∞ (Wi u)) →
      (∀ u∈rows,Function.support (twistProfile (Wi u) (σi u) (fi u)) ⊆ Iic (9/4:ℝ)) →
      (∀ u∈rows,∀ x,‖twistProfile (Wi u) (σi u) (fi u) x‖ ≤ Bshort) →
      (∀ u∈rows,|fi u|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
      (∀ u∈rows,∀ x∈Icc (1-a-6*ez-σi u) (2-σi u),∀ t:ℝ,
        (1+|t|)^2*‖mellin (Wi u) ((x:ℂ)+t*Complex.I)‖ ≤ profileBound 2) →
      (∀ kl : Fin (Kbig+1),∀ u∈rows,∀ x∈Icc (1-a-6*ez-σi u) (2-σi u),∀ t:ℝ,
        (1+|t|)^(order kl+2)*‖mellin (Wi u) ((x:ℂ)+t*Complex.I)‖ ≤ profileBound (order kl+2)) →
    ∀ (θ θLong : Slot→RayQuotient.Characters M H) (w v vLong : Slot→ℝ)
      (tMark tLong slotHeight eu L X V : ℝ),
      (∀ j,0 ≤ w j) → (∀ j,w j/d ≤ nativeMesh) →
      0 ≤ slotHeight → (∀ j,|v j| ≤ slotHeight) → (∀ j,|vLong j| ≤ slotHeight) →
      (∀ u∈rows,∀ j,‖descriptor M H hH η η₀ W Z θ w v tMark u j‖=
        ‖normalizedSlot ηlong (fixedBadMask*idealGenerator 1) 1 u.val (primePool M H 2 (Z^(w j)))
          (fun I=>idealCoeff (relativeCharacter M H hH baseLong (θLong j)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w j)) (33/50) (vLong j) I) tLong (Z^(w j))‖) →
      0 ≤ eu →
      (∑ j,w j) ≤ L →
      0 < X → length (Z^d) X ≤ N →
      (∀ u∈rows,initialKeep ηlong (internalQ Q baseLong) u.val) →
      (98/100:ℝ) ≤ V → V ≤ d → d ≤ V+3*δ →
      nu0 ≤ 2*a-1+price → 2*a-1 ≤ nu0+step → eu ≤ e0+step →
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
      original s.character s.mask 1 u.val (twistProfile (Wi u) (σi u) (fi u)) 0 Y*
      (∏ j,descriptor M H hH η η₀ W Z θ w v tMark u j)‖^2) ≤
      Cslot^(Fintype.card Slot)*Cy kl*Real.sqrt (192*(1+hi)*(Cc kl*(1+hi)^(Jc kl)))*
        Real.sqrt (Cl kl*QuadraticInitialBound.diagonalControl radialMajorant*
          (sourceControl (controls kl) (p.profile jprofile))^4*(1+|tLong|+hl)^(degree kl))*
      Z^(V+radialAllowance V+loss) := by
  obtain ⟨step,δ,fee,hstep,hδ,hfee,hstepEq,hδEq,hwindow,hprice⟩ := general_pair_approx_inverse_alternatives_paid c hy0 hy1 he0 hnub hnu1 hg hpaid hloss
  refine ⟨step,δ,fee,hstep,hδ,hfee,hstepEq,hδEq,hwindow,?_⟩
  intro hβ εm nativeError hεm hnativeError N quota hN hq0 hqcap hqmean dmin dmax hdmin hdmax price hprice0 hpriceBudget
  obtain ⟨nm,hnm,huniform⟩ := actual_length_unmarked_energy
    hβ εm nativeError hεm hnativeError hN hq0 hqcap hqmean dmin dmax hdmin hdmax
  have hdmaxp : 0 < dmax := hdmin.trans_le hdmax
  let nmOut := min nm (fee/(2*dmax))
  have hnmOut : 0 < nmOut := lt_min hnm (by positivity)
  refine ⟨nmOut,hnmOut,?_⟩
  intro Slot _ M _ H hH W hWs hW η η₀ ηlong baseLong Q hQM hQ0 hQt hQ72 bΦ hbΦ hsΦ
  obtain ⟨Fb,hFb,hleaf⟩ := huniform Slot M H hH W hWs hW η η₀ ηlong baseLong Q hQM hQ0 hQt hQ72 bΦ hbΦ hsΦ
  refine ⟨Fb,hFb,?_⟩
  intro buffer hbuffer
  dsimp only
  let b := buffer/2
  have hb : 0 < b := by dsimp [b];positivity
  obtain ⟨Jc,Cc,degree,controls,Cl,hpos,hlate⟩ := hleaf b hb
  refine ⟨Jc,Cc,degree,controls,Cl,hpos,?_⟩
  intro Mcap Bmask margin R τ εshort ez κ heightCost hmargin hR hτ hheight hεshort hez hez' hκ hκ' hcost hbudget Bshort hBshort profileBound hprofile
  obtain ⟨order,Cy,hCy,hbounds⟩ := hlate Mcap Bmask margin R τ εshort ez κ heightCost
    hmargin hR hτ hheight hεshort hez hez' hκ hκ' hcost hbudget Bshort hBshort profileBound hprofile
  refine ⟨order,Cy,hCy,?_⟩
  intro I Cslot hCslot
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
  intro d hd hd' hds s hswidth hη hp hsM hsη parentRows hkeep0 hΦ0 hnorm0
    K Je Jν ε level band window cutoffTable parentWS tag
  try dsimp only
  intro ha' hnext0
  intro hε hεmax hcut hcutmax
  let χ := fun u : FreeRow => family M H hH s η₀ (naturalRow s.character u.val u.property.1)
  have hdp0 : 0 < d := hdmin.trans_le hd
  have hUd : 1 < Z^d := Real.one_lt_rpow hZleaf.1 hdp0
  obtain ⟨w0,hfields0⟩ := terminal_witness_class parentRows χ Z d dmax τ ε ez hUd
    level band window cutoffTable parentWS tag
  let rows := classRows parentRows (terminalWitnessKey level band window cutoffTable parentWS) tag
  let a := (51/100:ℝ)+ez*tag.2.1.val
  let i := tag.1.val
  let cutoff := cutoffTable tag.2.2.1
  let T := Z^τ
  let allowance := (Z^d)^(τ/(2*dmax))
  let label := tag.2.2.2.1
  let left := tag.2.2.2.2.1
  let right := tag.2.2.2.2.2
  let r := Real.logb (Z^d) ((2:ℝ)^left.val)
  let ws : ∀u : rows,SupportedWitness (χ u.val) (Z^d) a ε cutoff T allowance i := by
    intro u
    exact w0 ⟨u.val,by simpa only [rows,classRows_mem] using u.property⟩
  have hfields : ∀u : rows,(ws u).label=label ∧ (ws u).left=left ∧ (ws u).right=right ∧
      (ws u).r=r ∧ (ws u).m=Real.logb (Z^d) ((2:ℝ)^right.val) := by
    intro u
    exact hfields0 ⟨u.val,by simpa only [rows,classRows_mem] using u.property⟩
  have hsub : rows ⊆ parentRows := classRows_subset parentRows _ tag
  have hkeep (u : FreeRow) (hu : u∈rows) := hkeep0 u (hsub hu)
  have hΦ (u : FreeRow) (hu : u∈rows) := hΦ0 u (hsub hu)
  have hnorm (u : FreeRow) (hu : u∈rows) := hnorm0 u (hsub hu)
  have ha : 51/100 ≤ a := le_add_of_nonneg_right (mul_nonneg hez.le (Nat.cast_nonneg _))
  have hiI : i ≤ I := Nat.le_of_lt_succ tag.1.isLt
  have hlabel (u : rows) : (ws u).label=label := (hfields u).1
  have hr (u : rows) : (ws u).r=r := (hfields u).2.2.2.1
  have hleft (u : rows) : (ws u).left=left := (hfields u).2.1
  have hright (u : rows) : (ws u).right=right := (hfields u).2.2.1
  have hnext (u : rows) : HeckeDetectorZeros.zeroMaximum
      (family M H hH s η₀ (naturalRow s.character u.val.val u.val.property.1))
      (family_nonprincipal M H hH s η₀ hsM hsη (hkeep u.val u.property)
        (naturalRow s.character u.val.val u.val.property.1))
      (3*(i+1 : ℕ)*Z^τ) < a+2*ez := by
    let parent : parentRows := ⟨u.val,hsub u.property⟩
    have hk := (classRows_mem parentRows (terminalWitnessKey level band window cutoffTable parentWS) tag u.val).mp u.property
    have hf : level parent=tag.1 ∧ band parent=tag.2.1 ∧ window parent=tag.2.2.1 ∧
        (parentWS parent).label=tag.2.2.2.1 ∧ (parentWS parent).left=left ∧ (parentWS parent).right=right := by
      simpa only [terminalWitnessKey,Prod.ext_iff] using hk.2
    have hn := hnext0 parent
    simpa only [hf.1,hf.2.1] using hn
  intro Wi Ai Bi σi fi Y hy hyr hY hYcap hAi hWi hsm hsupp hsup hfi hm₂ hmn
    θ θLong w v vLong tMark tLong slotHeight eu L X V hw hmesh hheight hv hvLong hLongNorm heu hwidth
    hX hXN hkeepLong hV hVd hdV hnul hnuu heuu hri hcutoffEq hεfee hL0 hL hLive hNativeBudget hInverseBudget hError
    jd p jprofile
  try dsimp only
  intro hne hlow hupp
  have hmeshOld (j : Slot) : w j/d ≤ nm := (hmesh j).trans (min_le_left _ _)
  have hwnarrow : w jd/d ≤ fee/(2*dmax) := (hmesh jd).trans (min_le_right _ _)
  obtain ⟨kl,hNatUp,hNatLo,hE⟩ := hZleaf.2 d hd hd' hds s hswidth hη hp hsM hsη rows hkeep hΦ hnorm
    a ε cutoff T allowance i ha ha' hiI hε hεmax hcut hcutmax ws label left right hlabel hleft hright hnext Wi Ai Bi σi fi yCell Y hy hyr hY hYcap
    hAi hWi hsm hsupp hsup hfi hm₂ hmn θ θLong w v vLong tMark tLong slotHeight e0 eu L (Cslot*Z^buffer) X
    hw hmeshOld hheight hv hvLong hLongNorm hcalib.1 hcalib.2 he0 heu hwidth hX hXN hkeepLong
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
    rw [heq] at hh
    change r ≤ cutoff+ε at hh
    have hc : cutoff=(c.inverse:ℝ)+(c.ordinary:ℝ) := hcutoffEq
    rw [hc] at hh
    exact hh
  have hr2 : r ≤ 2 := by
    have hTmax := (cutoff_detector_domain c hg).2
    dsimp only [QRH.Cycle092.SourceFurtherWitness.totalCutoff] at hTmax
    linarith
  have hInvFee : inverseLoss ≤ fee := by
    dsimp only [inverseLoss]
    by_cases hrs : r ≤ 1
    · exact hInverseBudget hrs
    · rw [inverseQuota_native (by linarith : (7/9:ℝ) ≤ r)]
      linarith [hfee.le]
  have hpaidPower := hprice n V d (2*a-1) eu r L ((kl.val:ℝ)*(w jd)) 0
    nativeLoss inverseLoss ε error price dmax hn hV hVd hdV hprice0 hnul hnuu heuu hd'
    hr2 hpriceBudget hri hrT
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
        original s.character s.mask 1 u.val (twistProfile (Wi u) (σi u) (fi u)) 0 Y*
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

#print axioms actual_class_unmarked_paid
end
end QRH.Cycle092.SourceInverseP6
