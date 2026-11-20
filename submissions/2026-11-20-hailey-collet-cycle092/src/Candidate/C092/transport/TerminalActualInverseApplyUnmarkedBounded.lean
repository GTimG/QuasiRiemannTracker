/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.TerminalActualInverseApplyUnmarkedClass
import Candidate.C092.transport.StrongPairRegularTerminalHeights
namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators ContDiff SchwartzMap
open QRH.Cycle092.StrongPair
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
local instance c092LocalInst_Candidate_C092_transport_TerminalActualInverseApplyUnmarkedBounded_21d55823cf2fb99c_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem actual_class_unmarked_bounded
    {n yCell e0 nu0 loss : ℝ} (c : Cutoff)
    (hy0 : (369/1000:ℝ) ≤ yCell) (hy1 : yCell ≤ sourceY)
    (hn : n ≤ sourceRatio*yCell) (he0 : 0 ≤ e0) (hnub : e0 ≤ nu0) (hnu1 : nu0 ≤ 3/4)
    {bcell : ℚ} (hg : CutoffGuard bcell c) (hpaid : PaidWithBand yCell e0 nu0 c) (hloss : 0 < loss) (heightLoss : ℝ) (hheightLoss : 0 ≤ heightLoss)
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
    ∃ D : ℕ,(∀ kl,Jc kl+degree kl+1 ≤ D) ∧
      (∀ kl,0 < Cc kl ∧ 0 < Cl kl) ∧
    ∀ (Mcap Bmask margin R τ εshort ez κ heightCost : ℝ)
    (hmargin : 0 < margin) (hR : 0 ≤ R)
    (hτ : 0 < τ) (hτD : τ*(D:ℝ) ≤ heightLoss) (hheight : 4*τ < dmin*heightCost) (hεshort : 0 < εshort)
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
      |tMark|+|tLong|+slotHeight ≤ Z^τ →
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
      (Cslot^(Fintype.card Slot)*Cy kl*(192*Cc kl+1)*
        (Cl kl*QuadraticInitialBound.diagonalControl radialMajorant*
          (sourceControl (controls kl) (p.profile jprofile))^4+1)*
        (2+2*Real.pi+(3*I:ℕ))^(Jc kl+1)*(3:ℝ)^(degree kl))*
      Z^(V+radialAllowance V+loss+heightLoss) := by
  obtain ⟨step,δ,fee,hstep,hδ,hfee,hstepEq,hδEq,hwindow,hsupply⟩ :=
    actual_class_unmarked_paid c hy0 hy1 hn he0 hnub hnu1 hg hpaid hloss
  refine ⟨step,δ,fee,hstep,hδ,hfee,hstepEq,hδEq,hwindow,?_⟩
  intro hβ εm nativeError hεm hnativeError N quota hN hq0 hqcap hqmean dmin dmax hdmin hdmax price hprice0 hpriceBudget
  obtain ⟨nm,hnm,huniform⟩ := hsupply hβ εm nativeError hεm hnativeError hN hq0 hqcap hqmean dmin dmax hdmin hdmax price hprice0 hpriceBudget
  refine ⟨nm,hnm,?_⟩
  intro Slot _ M _ H hH W hWs hW η η₀ ηlong baseLong Q hQM hQ0 hQt hQ72 bΦ hbΦ hsΦ
  obtain ⟨Fb,hFb,hleaf⟩ := huniform Slot M H hH W hWs hW η η₀ ηlong baseLong Q hQM hQ0 hQt hQ72 bΦ hbΦ hsΦ
  refine ⟨Fb,hFb,?_⟩
  intro buffer hbuffer
  dsimp only
  let b := buffer/2
  let Kbig := ⌈(7/37:ℝ)/(b/dmax)⌉₊+1
  obtain ⟨Jc,Cc,degree,controls,Cl,hpos,hlate⟩ := hleaf buffer hbuffer
  let D : ℕ := ∑ kl : Fin (Kbig+1),(Jc kl+degree kl+1)
  have hD (kl : Fin (Kbig+1)) : Jc kl+degree kl+1 ≤ D :=
    Finset.single_le_sum (f:=fun k : Fin (Kbig+1)=>Jc k+degree k+1)
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ kl)
  refine ⟨Jc,Cc,degree,controls,Cl,D,hD,hpos,?_⟩
  intro Mcap Bmask margin R τ εshort ez κ heightCost hmargin hR hτ hτD hheight hεshort hez hez' hκ hκ' hcost hbudget Bshort hBshort profileBound hprofile
  obtain ⟨order,Cy,hCy,hbounds⟩ := hlate Mcap Bmask margin R τ εshort ez κ heightCost
    hmargin hR hτ hheight hεshort hez hez' hκ hκ' hcost hbudget Bshort hBshort profileBound hprofile
  refine ⟨order,Cy,hCy,?_⟩
  intro I Cslot hCslot
  filter_upwards [hbounds I Cslot hCslot] with Z hZleaf
  refine ⟨hZleaf.1,?_⟩
  intro d hd hd' hds s hswidth hη hp hsM hsη parentRows hkeep0 hΦ0 hnorm0
    K Je Jν ε level band window cutoffTable parentWS tag
  try dsimp only
  intro ha' hnext0
  intro hε hεmax hcut hcutmax
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
  have hiI : i ≤ I := Nat.le_of_lt_succ tag.1.isLt
  intro Wi Ai Bi σi fi Y hy hyr hY hYcap hAi hWi hsm hsupp hsup hfi hm₂ hmn
    θ θLong w v vLong tMark tLong slotHeight eu L X V hw hmesh hheight hv hvLong hLongNorm heu hwidth
    hX hXN hkeepLong hV hVd hdV hnul hnuu heuu hri hcutoffEq hεfee hL0 hL hLive hNativeBudget hInverseBudget hError
    hheightSmall jd p jprofile
  try dsimp only
  intro hne hlow hupp
  obtain ⟨kl,hE⟩ := hZleaf.2 d hd hd' hds s hswidth hη hp hsM hsη parentRows hkeep0 hΦ0 hnorm0
    K Je Jν ε level band window cutoffTable parentWS tag ha' hnext0 hε hεmax hcut hcutmax
    Wi Ai Bi σi fi Y hy hyr hY hYcap hAi hWi hsm hsupp hsup hfi hm₂ hmn
    θ θLong w v vLong tMark tLong slotHeight eu L X V hw hmesh hheight hv hvLong hLongNorm heu hwidth
    hX hXN hkeepLong hV hVd hdV hnul hnuu heuu hri hcutoffEq hεfee hL0 hL hLive hNativeBudget hInverseBudget hError
    jd p jprofile hne hlow hupp
  refine ⟨kl,?_⟩
  have hTsmall : T ≤ Z^τ := le_rfl
  have hallowanceSmall : allowance ≤ Z^τ := by
    dsimp only [allowance]
    rw [←Real.rpow_mul (zero_lt_one.trans hZleaf.1).le]
    apply Real.rpow_le_rpow_of_exponent_le hZleaf.1.le
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 2*dmax from mul_pos (by norm_num) (hdmin.trans_le hdmax))).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hd' hτ.le, mul_pos (hdmin.trans_le hdmax) hτ]
  let hi := max (|tMark|+slotHeight) (2*Real.pi*allowance+(3*i:ℕ)*T)
  let hl := |tMark|+|tLong|+slotHeight
  have hZp : 0 < Z := zero_lt_one.trans hZleaf.1
  have hzτ : 1 ≤ Z^τ := Real.one_le_rpow hZleaf.1.le hτ.le
  have hhi : 0 ≤ hi := (add_nonneg (abs_nonneg _) hheight).trans (le_max_left _ _)
  have hhl : 0 ≤ hl := by dsimp [hl];positivity
  have hI : ((3*i:ℕ):ℝ) ≤ (3*I:ℕ) := by exact_mod_cast Nat.mul_le_mul_left 3 hiI
  have hhiBound : hi ≤ (1+2*Real.pi+(3*I:ℕ))*Z^τ := by
    dsimp only [hi]
    apply max_le
    · have hpos := mul_nonneg (show 0 ≤ 2*Real.pi+(3*I:ℕ) by positivity) (show 0 ≤ Z^τ by positivity)
      linarith only [hpos,hheightSmall,abs_nonneg tLong]
    · have ha := mul_le_mul_of_nonneg_left hallowanceSmall (show 0 ≤ 2*Real.pi by positivity)
      have ht := mul_le_mul_of_nonneg_left hTsmall (show 0 ≤ ((3*i:ℕ):ℝ) by positivity)
      have hi := mul_le_mul_of_nonneg_right hI (show 0 ≤ Z^τ by positivity)
      nlinarith only [ha,ht,hi,hzτ]
  have hhlBound : |tLong|+hl ≤ 2*Z^τ := by
    dsimp only [hl]
    linarith only [hheightSmall,abs_nonneg tMark,hheight,abs_nonneg tLong]
  have hpaid := terminal_inverse_height_payment 192 (Jc kl) (degree kl) I hZleaf.1.le hτ.le hhi hhl
    hhiBound hhlBound (by norm_num) (hpos kl).1.le
    (mul_nonneg (pow_nonneg hCslot.le (Fintype.card Slot)) (hCy kl).le)
    (show 0 ≤ Cl kl*QuadraticInitialBound.diagonalControl radialMajorant*
      (sourceControl (controls kl) (p.profile jprofile))^4 by
      have hd := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
      have hCl := (hpos kl).2
      positivity) (q:=V+radialAllowance V+loss)
  have hE' := hE.trans hpaid
  have hdeg : τ*((Jc kl+degree kl+1:ℕ):ℝ) ≤ heightLoss :=
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hD kl)) hτ.le).trans hτD
  exact hE'.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZleaf.1.le (by linarith only [hdeg])) (by
      have hd := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
      have hCc := (hpos kl).1
      have hCl := (hpos kl).2
      have hcy := hCy kl
      positivity))



#print axioms actual_class_unmarked_bounded
end
end QRH.Cycle092.SourceInverseP6
