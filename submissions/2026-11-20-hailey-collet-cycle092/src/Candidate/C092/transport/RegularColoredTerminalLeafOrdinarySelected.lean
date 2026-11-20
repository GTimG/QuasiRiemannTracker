/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual regular-core P4 and authentic rowwise witness source on one finite family. -/
import Candidate.C092.transport.RegularColoredTerminalLeafOrdinaryClass
import Candidate.C092.transport.RegularColoredTerminalLeafWindowFee
import Candidate.C092.transport.StrongPairOrdinaryNearForward
import Candidate.C092.transport.RegularColoredTerminalLeafDecision
import Candidate.C092.transport.RegularColoredTerminalLeafNative
import Candidate.C092.transport.RegularColoredTerminalLeafReindex
import Candidate.C092.transport.StrongPairRegularTerminalOrdinaryApprox
import Candidate.C092.transport.StrongPairRegularTerminalWindowFinishApprox
import Candidate.C092.transport.StrongPairOrdinaryNearIndependent
import Candidate.C092.transport.StrongPairOrdinaryNearErrors

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification
open HeckeDetectorWitnessRows HeckeDetectorSupportedWitness ConcretePrimeRowBridge ConcreteTraceCRT HeckeDetectorZeros
open HeckeRowClosure ProbeHighRowFamily CanonicalRowCompletion
open CenteredMomentEnergyBands QRH.Cycle092.WholeSlot
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional
open QRH.Cycle092.LowActual
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair
open QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.WitnessRowSup.Actual
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafOrdinarySelected_594492244ad191b9_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- Genuine normalized P4 on one authentic full ticket class, using the
same parent supported zero and both dyads. -/
theorem terminal_actual_class_ordinary_selected
    (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ) (bΦ : ℝ) (ηLong baseLong ηShort baseShort : Character) (QLong Qfix : Ideal O)
    (n y dmin εsource mesh : ℝ) (bank : Finset (ℝ×ℝ)) (dec : (ℝ×ℝ)→ℝ)
    (degree : ℕ) (controls : Finset (ℕ×ℕ)) (Csource : ℝ) (J : ℕ) (Crow : ℝ)
    (hCsource : 0 ≤ Csource) (hesource : 0 ≤ εsource)
    (m0 gap : ℝ)
    (hbank : ∀ B ∈ bank,(98/100:ℝ) ≤ B.1 ∧ B.1 ≤ (QRH.SourceCertificate.H:ℝ) ∧ m0 ≤ B.2 ∧ B.2 ≤ 51/100 ∧
      0 < dec B ∧ dec B ≤ gap ∧ 0 < nearOrdinaryQuota n B.2 B.1-dec B)
    (hnet : ∀ d m : ℝ,(98/100:ℝ) ≤ d → m0 ≤ m → m ≤ 51/100 →
      ∃ B ∈ bank,B.1 ≤ min d (QRH.SourceCertificate.H:ℝ) ∧ min d (QRH.SourceCertificate.H:ℝ)-B.1 < gap ∧ m ≤ B.2 ∧ B.2-m < gap)
    (hphysical : TerminalOrdinaryNormalizedPhysical Slot M H hH W bΦ ηLong baseLong ηShort baseShort QLong Qfix
      n y dmin εsource mesh bank dec degree controls Csource J Crow) :
∀ (bstate Mcap Bmask margin R dmax τ ε e κ heightCost : ℝ)
    (hbstate : 0 ≤ bstate) (hmargin : 0 < margin) (hR : 0 ≤ R)
    (hdmax : dmin ≤ dmax) (hτ : 0 < τ)
    (hheight : 4*τ < dmin*heightCost) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκ' : κ ≤ 1)
    (hcost : 0 ≤ heightCost) (hbudget : 12*e*(R+2)+8*κ+2*heightCost ≤ ε),
    ∃ order : ℕ,∃ C4 : ℝ,0 < C4 ∧
    ∃ S : Finset (ℕ×ℕ),(0,0)∈S ∧ ∃ C : ℝ,1≤C ∧
    ∀ (I : ℕ),∀ᶠ U : ℝ in atTop,1 < U ∧
    ∀ (p : Profiles (1/4) (9/4)),
    ∀ d : ℝ,dmin ≤ d → d ≤ dmax → Mcap+Bmask+margin ≤ d →
    ∀ s : NaturalState U Bmask bstate,s.width ≤ Mcap → s.character=ηShort →
    ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ baseShort.modulus),
      s.mask=fixedBadMask*idealGenerator 1 →
      (∀ z : O,s.radial.keep z ↔ initialKeep s.character (internalQ Qfix baseShort) z) →
    ∀ rows : Finset FreeRow,∀ hrows : ∀ u∈rows,s.radial.keep u.val,
      (∀ u∈rows,s.radial.profile (‖eisEmbedding u.val‖^2/s.radial.scale) ≠ 0) →
    ∀ (K Je Jν : ℕ)
      (level : rows→Fin (I+1)) (band : rows→Fin (K+1))
      (window : rows→Fin Je×Fin Jν) (cutoffTable : Fin Je×Fin Jν→ℝ)
      (parentWS : ∀u : rows,SupportedWitness
        (family M H hH s baseShort (naturalRow s.character u.val.val u.val.property.1))
        (U^d) ((51/100:ℝ)+e*(band u).val) ε (cutoffTable (window u))
        (U^τ) ((U^d)^(τ/(2*dmax))) (level u).val)
      (tag : Fin (I+1)×Fin (K+1)×(Fin Je×Fin Jν)×
        Option (RayQuotient.Characters M H×RayQuotient.Characters M H)×
        Fin (dyadicLength (U^d))×Fin (dyadicLength (U^d))),
    let parentRows := rows;
    let a := (51/100:ℝ)+e*tag.2.1.val;
    let i := tag.1.val;
    let m := Real.logb (U^d) ((2:ℝ)^tag.2.2.2.2.2.val);
    let j := tag.2.2.2.1;
    let inverseLength := Real.logb (U^d) ((2:ℝ)^tag.2.2.2.2.1.val);
    let rows := TerminalActualRow.classRows parentRows
      (terminalWitnessKey level band window cutoffTable parentWS) tag;
    ∀ (r : ℝ) (c : Cutoff),0≤r → r≤R → a≤1 →
      cutoffTable tag.2.2.1=totalCutoff c → rows.Nonempty →
      (∀u : parentRows,zeroMaximum
        (family M H hH s baseShort (naturalRow s.character u.val.val u.val.property.1))
        (family_nonprincipal M H hH s baseShort hQM hQη (hrows u.val u.property)
          (naturalRow s.character u.val.val u.val.property.1))
        (3*((level u).val+1:ℕ)*U^τ)<((51/100:ℝ)+e*(band u).val)+2*e) →
    ∀ (tShort : ℝ), |tShort|+U^τ/2≤(3*i+2:ℕ)*U^τ →
    ∀ (θ : Slot→RayQuotient.Characters M H)
      (w σslot v : Slot→ℝ) (θLong : Slot→RayQuotient.Characters M H) (σLong vLong : Slot→ℝ)
      (tMark tLong slotHeight heightLong XL : ℝ),
      (∀ k,0 ≤ w k) → (∀ k,w k ≤ mesh) →
      (∀ k,(33/50:ℝ) ≤ σslot k) → (∀ k,σslot k ≤ (33/50:ℝ)) →
      0 ≤ slotHeight → (∀ k,|v k| ≤ slotHeight) →
      (∀ k,(33/50:ℝ) ≤ σLong k) → (∀ k,σLong k ≤ (33/50:ℝ)) →
      0 ≤ heightLong → (∀ k,|vLong k| ≤ heightLong) →
      0 < XL → length U XL ≤ n →
      (∀ u∈rows,initialKeep ηLong (internalQ QLong baseLong) u.val) →
      (∀ u∈rows,∀ k,
        ‖normalizedSlot s.character (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools M H 2 (U^d) w k)
          (originalCoefficients M H hH baseShort θ W (U^d) w σslot v k) tMark ((U^d)^(w k))‖ =
        ‖normalizedSlot ηLong (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools M H 2 (U^d) w k)
          (originalCoefficients M H hH baseLong θLong W (U^d) w σLong vLong k) tLong ((U^d)^(w k))‖) →
      (∀ u∈rows,rowNorm u ≤ U^d) →
    ∀ (eResp eLower νLower step price V rounding collar Cslot buffer conductor : ℝ) (b : ℚ),
      sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y →
      0 ≤ eResp → 0 ≤ eLower → eLower ≤ (responseUpper:ℝ) → eLower ≤ νLower → νLower ≤ 3/4 →
      νLower ≤ 2*a-1+price → 2*a-1 ≤ νLower+step → eResp ≤ eLower+step → 0 ≤ step → 0 ≤ price →
      CutoffGuard b c → y/(QRH.SourceCertificate.H:ℝ) ≤ (c.ordinary:ℝ) →
      sourceY0 ≤ (c.ordinary:ℝ) → PaidWithBand y eLower νLower c →
      inverseLength < (c.inverse:ℝ) →
      (98/100:ℝ) ≤ V → V ≤ d → d ≤ V+collar →
      m0 ≤ (c.ordinary:ℝ) → ε ≤ 1/7500 →
      0 ≤ gap → gap ≤ 1 → 0 ≤ rounding → rounding ≤ gap → (∀ k,d*w k ≤ rounding) →
      sourceWidth n y-(u:ℝ) ≤ 1 →
      0 < Cslot → 0 ≤ buffer → d*r ≤ y →
      (∑ k,d*w k) ≤ sourceWidth n y-(u:ℝ) →
      (∀ u : rows,∀ k,w k=0 →
        ‖normalizedSlot s.character s.mask 1 u.val.val
          (originalPools M H 2 (U^d) w k)
          (originalCoefficients M H hH baseShort θ W (U^d) w σslot v k) tMark ((U^d)^(w k))‖^2 ≤ Cslot*U^buffer) →
      (∀ u : rows,response U (Cslot*U^buffer) (fun k=>d*w k)
        (fun k=>‖normalizedSlot s.character s.mask 1 u.val.val
          (originalPools M H 2 (U^d) w k)
          (originalCoefficients M H hH baseShort θ W (U^d) w σslot v k) tMark ((U^d)^(w k))‖^2) ≤ eResp) →
      |tMark|+|tLong|+slotHeight+heightLong ≤ U^τ →
      collar ≤ 3*conductor → 3*conductor ≤ (rho:ℝ)/128 →
      (responseUpper:ℝ)*(dmax*(2*gap)+dmax*gap+gap) ≤ (rho:ℝ)/128 →
      (15/4:ℝ)*dmax*ε ≤ (rho:ℝ)/128 → dmax*εsource ≤ (rho:ℝ)/128 →
      buffer*(Fintype.card Slot:ℝ) ≤ (rho:ℝ)/128 →
      τ*((degree+2*J+1:ℕ):ℝ) ≤ (rho:ℝ)/128 →
      3*step+price*d*m ≤ (rho:ℝ)/128 →
      StrongPair.finiteEnergyOn Finset.univ rows ηLong s.character
        ((TerminalProfileUniform.unitPair S C p).profile 0) ((TerminalProfileUniform.unitPair S C p).profile 1) tLong tShort XL ((U^d)^r)
        (fun k u=>normalizedSlot s.character s.mask 1 u.val
          (originalPools M H 2 (U^d) w k)
          (originalCoefficients M H hH baseShort θ W (U^d) w σslot v k) tMark ((U^d)^(w k))) ≤
        ((max 1 Cslot)^(Fintype.card Slot)*
          (C4*12*Csource*QuadraticInitialBound.diagonalControl radialMajorant*Crow^2)*(4:ℝ)^degree*
              (1+2*Real.pi+(3*I:ℕ))^(2*J+1))*
          U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((QRH.SourceCertificate.H:ℝ)-V)) := by
  intro bstate Mcap Bmask margin R dmax τ ε e κ heightCost hbstate hmargin hR hdmax hτ hheight hε he he' hκ hκ' hcost hbudget
  obtain ⟨order,C4,hC4,S,hS,C,hC,hsource⟩ := terminal_actual_class_ordinary Slot M H hH W bΦ
    ηLong baseLong ηShort baseShort QLong Qfix n y dmin εsource mesh bank dec degree controls Csource J Crow hphysical
    bstate Mcap Bmask margin R dmax τ ε e κ heightCost hbstate hmargin hR hdmax hτ hheight hε he he' hκ hκ' hcost hbudget
  refine ⟨order,C4,hC4,S,hS,C,hC,?_⟩
  intro I
  filter_upwards [hsource I] with U hU
  refine ⟨hU.1,?_⟩
  intro p d hd hd' hds s hs hschar hQM hQη hmask hkeep parentRows hrows hΦrows
    K Je Jν level band window cutoffTable parentWS tag
  dsimp only
  intro r c hr hr' ha' hcut hn hnext tShort hfreq θ w σslot v θLong σLong vLong tMark tLong slotHeight heightLong XL
    hw hwm hσlo hσhi hh hv hσLonglo hσLonghi hhLong hvLong hXL hXN hkLong hmLong hy
    eResp eLower νLower step price V rounding collar Cslot buffer conductor b hy0' hycap hyn' hn'
    he0 hel0 hel1 hνlo hνhi hνactual0 hνactual1 heu hstep hprice hg hc hc0 hp
    hescape hV hdV hdc hm0 heps hgap hgap1 hround hroundgap hwidthmax hL hCslot hbuffer hshort hwidth hz hresponse hsmall
    hcollar hconductor hcapFee hwitFee hsourceFee hbufferFee hheightFee hwindowFee
  let key := terminalWitnessKey level band window cutoffTable parentWS
  let rows := TerminalActualRow.classRows parentRows key tag
  have hsub : rows⊆parentRows := TerminalActualRow.classRows_subset parentRows key tag
  have hU0 : 0 < U := by linarith [hU.1]
  have hd0 : 0 < d := by linarith
  have hUd : 1<U^d := Real.one_lt_rpow hU.1 hd0
  obtain ⟨wc,hfields⟩ := terminal_witness_class parentRows
    (fun u=>family M H hH s baseShort (naturalRow s.character u.val u.property.1))
    U d dmax τ ε e hUd level band window cutoffTable parentWS tag
  obtain ⟨u,hu⟩ := hn
  let uc : rows := ⟨u,hu⟩
  let v0 := (wc ⟨u,by simpa only [rows,key,TerminalActualRow.classRows_mem] using hu⟩)
  let witness := terminalCastWitness rfl hcut rfl v0
  have hm : witness.m=Real.logb (U^d) ((2:ℝ)^tag.2.2.2.2.2.val) := by
    exact (terminalCastWitness_fields rfl hcut rfl v0).2.2.2.2.1.trans
      (hfields ⟨u,by simpa only [rows,key,TerminalActualRow.classRows_mem] using hu⟩).2.2.2.2
  obtain ⟨B,hB,F,hB0,hBd,hBgap,hcap,hcapgap,hdec,hdecgap,hquota,hF,hrest,hex⟩ :=
    terminal_ordinary_witness_selection c witness bank dec hbank hnet (hV.trans hdV) hm0 hg heps
      w hw hwidthmax hround
  rw [hm] at hcap hcapgap
  have hN : length (U^d) XL ≤ n/B.1 := near_forward_long_cap hU0
    (by have h : (0:ℝ) ≤ sourceY0 := by norm_num [sourceY0]
        linarith) (by linarith) (hBd.trans (min_le_left _ _)) hXN
  have hm0' : 0 ≤ Real.logb (U^d) ((2:ℝ)^tag.2.2.2.2.2.val) :=
    Real.logb_nonneg hUd (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hY : length (U^d) ((U^d)^(Real.logb (U^d) ((2:ℝ)^tag.2.2.2.2.2.val))) ≤ nearOrdinaryCap n B.2 B.1 :=
    near_forward_witness_cap hU.1 hd0 hm0' ((le_max_left _ _).trans hcap)
  have hremoved (z : rows) (k : Slot) (_ : k∈Finset.univ\F) :
      ‖normalizedSlot s.character s.mask 1 z.val.val
        (originalPools M H 2 (U^d) w k)
        (originalCoefficients M H hH baseShort θ W (U^d) w σslot v k) tMark ((U^d)^(w k))‖^2 ≤
        (Cslot*U^buffer)*U^(eResp*(d*w k)) := by
    apply terminal_ordinary_removed_slots (fun k=>d*w k)
      (fun k=>normalizedSlot s.character s.mask 1 z.val.val
        (originalPools M H 2 (U^d) w k)
        (originalCoefficients M H hH baseShort θ W (U^d) w σslot v k) tMark ((U^d)^(w k)))
      hU.1 (mul_pos hCslot (Real.rpow_pos_of_pos (by linarith : 0<U) _))
      (fun k=>mul_nonneg hd0.le (hw k)) he0
      (fun k hk=>hz z k ((mul_eq_zero.mp hk).resolve_left (ne_of_gt hd0))) (hresponse z)
  have hfees := terminal_ordinary_named_fees
    (by linarith : 0 ≤ dmax) hd0.le hd' hel0 hel1 hgap (by linarith : 0 ≤ B.2-collaredOrdinaryCap c (Real.logb (U^d) ((2:ℝ)^tag.2.2.2.2.2.val))) hcapgap.le
    (by linarith : 0 ≤ min d (QRH.SourceCertificate.H:ℝ)-B.1) hBgap.le hdec.le hdecgap hround hroundgap
    hε.le hesource hcollar hconductor hcapFee hwitFee hsourceFee hbufferFee hheightFee hwindowFee
  have happ := hU.2 p d hd hd' hds s hs hschar hQM hQη hmask hkeep parentRows hrows hΦrows
    K Je Jν level band window cutoffTable parentWS tag r c hr hr' ha' hcut hnext tShort hfreq B hB F θ w σslot v θLong σLong vLong
    tMark tLong slotHeight heightLong XL hw hwm hσlo hσhi hh hv hσLonglo hσLonghi hhLong hvLong hF hXL hN hkLong
    (fun z hz k _=>hmLong z hz k) hy hY eResp eLower νLower step price V rounding collar Cslot buffer b
    hy0' hycap hyn' hn' he0 hel0 hel1 hνlo hνhi hνactual0 hνactual1 heu hstep hprice hg hc hc0 hp
    hescape hV hdV hdc hB0 hBd hcap hdec.le hround hL hquota.le (hroundgap.trans hgap1) hCslot.le hbuffer hshort hwidth hrest hremoved hsmall hfees.le
  apply happ.trans
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  have hpow := near_erased_constant F hCslot.le
  gcongr

#print axioms terminal_actual_class_ordinary_selected
end
end QRH.Cycle092.RegularColoredForward
