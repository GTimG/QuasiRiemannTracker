/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual original mixed packet with only the earlier P1 source remaining. -/
import Candidate.C092.transport.MixedUpperFinalMiddleFinalFee
import Candidate.C092.transport.MixedUpperFinalExitPhaseSumFinal
import Candidate.C092.transport.MixedMiddleReturnPaidSlicePhaseBanks
import Candidate.C092.transport.MixedMiddleReturnPaidSliceClassSplit
import Candidate.C092.transport.MixedMiddleReturnPaidSlicePhaseSplit
import Candidate.C092.transport.MixedTicketTailsLargeFinalFee
import Candidate.C092.transport.MixedOutsideActualFourthSmallFinalFee
import Candidate.C092.transport.MixedUpperFinalMerge
import Candidate.C092.transport.MixedUpperFinalEarlyGuards
import Candidate.C092.transport.FinalCycle092Interface
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
attribute [local reducible] QRH.Record1252270103Return.GenericPhysical.BaselineData.toMomentData
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.MixedMiddleReturn
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor QRH.Cycle092.MediumWitness
open QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount QRH.Cycle092.PacketJoinE49
open QRH.Cycle092.MixedUpperFinal QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]


open QRH.Cycle092.PacketJoin QRH.Cycle092.MixedTicketTails
local notation "contact" => Qrh.TwoSlot.AnchorContinuum.Contact.theta

theorem earlier_P1_guarded_mixed_upper
    (h : ℝ) (hh : hLower  ≤  h) (hh' : h  ≤  hUpper)
    (hgeometry : (inferInstance : Geometry.Parameters)=ActualGeometry.parameters h hh hh')
    (hP1 : RawTicket.EarlierP1) (hβ : (51/100:ℝ)  ≤  HeckeZeroSupremum.beta)
    (hκ : 2*HeckeZeroSupremum.beta-1  ≤  (3/4:ℝ)) :
  ∀ (affineError loss : ℝ),0<affineError → 0<loss →
  ∃ mc : ℝ→ℝ,(∀ t,0<t → 0 < mc t) ∧ ∃ mp : ℝ,0 < mp ∧
  ∀ (D : BaselineData) (F : BaselineSourceData D),
  (∀ s,D.length s  ≤  mc D.t/200) → (∀ s,D.length s  ≤  Cycle25.sourceMesh D.t/200) →
  (∀ s,D.length s  ≤  mp/200) → (∀ s,D.length s  ≤  Cycle25.Energy.commonMesh 2 0 1 (D.t/4)/200) →
  2*HeckeZeroSupremum.beta-1  ≤  D.momentKappa →
  D.ε  ≤  1/10000000 → D.t  ≤  1/10000000 → D.ε  ≤  3*witnessCollar →
  ∀ η : Character,∃ m : ℕ,∃ C0 : ℝ,0<C0 ∧
  ∀ (P : TransportParameters D) (padding τ : ℝ),0<τ →
  4*τ<(1/200:ℝ)*D.cost → padding+2*D.t  ≤  1/10000000000 → ∀ n : ℕ,
  ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀ idx grid : FreeRow→ℕ,
  selected D F padding τ n η Z idx grid →
  ∀ k∈smallDyadicIndices (Z^(Geometry.h+padding)),∀ i∈Finset.range (n+1),∀ j : ℕ,
  (cellRows D F padding Z idx grid k i j).Nonempty →
  let d := sourceDyadConductor Z D.t k
  let a : ℝ := 51/100+D.e*j
  let rows := cellRows D F padding Z idx grid k i j
  (19/25:ℝ)<d → d  ≤  Geometry.h+Cycle090.rowPad → ∀ (x z : ℂ),
  x.re=a+16*D.e → z.re=17/50 → |z.im|  ≤  (3*i+1:ℕ)*Z^τ →
  ∀ bins : Finset (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t),
  (∀ bin∈bins,(MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty →
    ¬upperSectorAdmission (2*a-1)
      (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) ∧
    ActualMixedPrice.MixedPaid Geometry.h contact d
      (2*a-1,classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))) →
  159*D.ε+12*D.t+P.mesh+16*D.e+2*P.eps+affineError/4+loss+2*Cycle090.rowPad  ≤  1/100000000000000 →
  (∑ bin∈bins,packetNorm D F (MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin)
    η Z x z (Z^Geometry.y))  ≤ 
    C0*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
      (Z^d)^(finalPower a d Cycle090.sourceCost (16*D.e+2*P.eps*d+17*D.t/25)
        (Cycle090.theta-Final.reserve))
 := by
  classical
  cases hgeometry
  letI := ActualGeometry.parameters h hh hh'
  have hgh : Geometry.h=h:=ActualGeometry.parameters_h h hh hh'
  intro affineError loss haff hloss
  obtain ⟨mcM,cap,hcap,hmcM,hM⟩:=earlier_P1_selected_middle_final_fee h hh hh' rfl hP1 hβ affineError loss haff hloss
  obtain ⟨mcE,hmcE,mpE,hmpE,hE⟩:=actual_selected_all_exit_descriptors_final_fee h hh hh' rfl hβ hκ
    affineError haff loss (loss/1000) hloss (by positivity) (by linarith)
  obtain ⟨mcL,hmcL,mpL,hmpL,hL⟩:=actual_original_large_phase_sum_final_fee hβ affineError haff loss hloss
  obtain ⟨mcS,hmcS,mpS,hmpS,hS⟩:=actual_original_small_phase_sum_final_fee hβ affineError haff loss hloss
  let mc:=fun t=>min (mcM t) (min (mcE t) (min (mcL t) (mcS t)))
  let mp:=min mpE (min mpL mpS)
  refine ⟨mc,(fun t ht=>lt_min (hmcM t ht) (lt_min (hmcE t ht) (lt_min (hmcL t ht) (hmcS t ht)))),mp,
    lt_min hmpE (lt_min hmpL hmpS),?_⟩
  intro D F hf hs hp hc hkβ he ht hcollar η
  have hfM : ∀s,D.length s  ≤  mcM D.t/200:=fun s=>(hf s).trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hfE : ∀s,D.length s  ≤  mcE D.t/200:=fun s=>(hf s).trans (div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num))
  have hfL : ∀s,D.length s  ≤  mcL D.t/200:=fun s=>(hf s).trans (div_le_div_of_nonneg_right ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) (by norm_num))
  have hfS : ∀s,D.length s  ≤  mcS D.t/200:=fun s=>(hf s).trans (div_le_div_of_nonneg_right ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))) (by norm_num))
  have hpE : ∀s,D.length s  ≤  mpE/200:=fun s=>(hp s).trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hpL : ∀s,D.length s  ≤  mpL/200:=fun s=>(hp s).trans (div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num))
  have hpS : ∀s,D.length s  ≤  mpS/200:=fun s=>(hp s).trans (div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num))
  obtain ⟨hfCap,mM,CM,hCM,hM⟩:=hM D F hfM hs he ht hkβ hcollar η
  obtain ⟨mE,CE,hCE,hE⟩:=hE D F hfE hs hpE hc hkβ η
  obtain ⟨mL,CL,hCL,hL⟩:=hL D F hfL hs hpL hc hkβ η
  obtain ⟨mS,CS,hCS,hS⟩:=hS D F hfS hs hpS hc hkβ η
  let m:=mM+mE+mL+mS
  let C0:=max 1 (phaseCardBound D)*CM+CE+CL+CS
  have hC0 : 0<C0:=by dsimp [C0];positivity
  refine ⟨m,C0,hC0,?_⟩
  intro P padding τ hτ hheight hpad n
  filter_upwards [hM P padding τ hτ hheight hpad n,hE P padding τ hτ hheight hpad n,
    hL P padding τ hτ hheight hpad n,hS P padding τ hτ hheight hpad n,
    actual_selected_phase_banks D F cap hcap hfCap hcollar P padding τ hτ hheight hpad n η,
    actual_cell_e49_data D F P padding τ hτ hheight hpad n η] with Z hM hE hL hS hB hcell
  refine ⟨hM.1,?_⟩
  intro idx grid hsel k hk i hi j hn
  dsimp only
  intro hd hdh x z hx hz him bins hbins hreserve
  let d:=sourceDyadConductor Z D.t k
  let a:ℝ:=51/100+D.e*j
  let rows:=cellRows D F padding Z idx grid k i j
  let ticket:=paidPhaseTicket D d a
  let big:=paidPhaseBigBins D d a bins
  let small:=bins.filter (fun bin=>¬originalDlow (ticket bin)  ≤  d)
  have hZ : 1<Z:=hM.1
  have hZ0 : 0<Z:=zero_lt_one.trans hZ
  have hd0 : 0<d:=by dsimp [d];linarith
  have hdhalf : (1/2:ℝ)  ≤  d:=by dsimp [d];linarith
  have hdh' : d  ≤  h+rowPad:=by simpa only [hgh] using hdh
  obtain ⟨hdhi,ha,hahi,hrows,hphase⟩:=hcell.2 idx grid hsel k hk i hi j hn
  have hnp : ∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1:=fun u hu=>(hrows u hu).2.2
  have hpaid : ∀bin∈bins,(amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty →
      ActualMixedPrice.MixedPaid Geometry.h contact d
        (2*a-1,classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)):=fun b hb hn=>(hbins b hb hn).2
  obtain ⟨data,hdata⟩:=hB.2 idx grid hsel k hk i hi j hn hdhalf hdh z hz him contact bins hpaid
  have hbigTicket : ∀bin∈big,(amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty →
      ticket bin∈TopData.rows ∧ (ticket bin).box.Contains (2*a-1,
        classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) ∧ originalDlow (ticket bin)  ≤  d:=by
    intro bin hb hn
    have hp:=original_phase_ticket (hpaid bin (Finset.mem_filter.mp hb).1 hn)
    exact ⟨hp.1,hp.2,(Finset.mem_filter.mp hb).2⟩
  have hsmallTicket : ∀bin∈small,(amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty →
      ticket bin∈TopData.rows ∧ (ticket bin).box.Contains (2*a-1,
        classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) ∧ d  ≤  originalDlow (ticket bin):=by
    intro bin hb hn
    have hp:=original_phase_ticket (hpaid bin (Finset.mem_filter.mp hb).1 hn)
    exact ⟨hp.1,hp.2,le_of_not_ge (Finset.mem_filter.mp hb).2⟩
  have hreserve' : 159*D.ε+12*D.t+P.mesh+16*D.e+2*P.eps+affineError/4+loss  ≤  1/100000000000000:=by
    have hpad0:0 ≤ rowPad:=by unfold rowPad;positivity
    linarith only [hreserve,hpad0]
  have bE:=hE.2 idx grid hsel k hk i hi j hn hdhalf x z hx hz him big data hreserve
  have bL:=hL.2 idx grid hsel k hk i hi j hn hdhalf hdh x z hx hz him
    (classCanonicalData D F rows hnp) big ticket hbigTicket
    (by simpa only [hgh] using hh) (by simpa only [hgh] using hh') rfl P.eps P.eps_pos.le P.mesh_pos.le
    (hreserve'.trans (by norm_num))
  have bS:=hS.2 idx grid hsel k hk i hi j hn hdhalf x z hx hz him small ticket hsmallTicket
    (by simpa only [hgh] using hh) (by simpa only [hgh] using hh') rfl P.eps P.eps_pos.le P.mesh_pos.le hreserve'
  let H:ℝ:=3+(3*i+1:ℕ)*Z^τ
  let Y:ℝ:=Z^Geometry.y
  let U:ℝ:=Z^d
  let fee:=16*D.e+2*P.eps*d+17*D.t/25
  let scale:ℝ:=Y^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*U^(finalPower a d sourceCost fee (theta-Final.reserve))
  let fMid:=phaseMiddleNorm D F η Z P d a rows z τ i hdhalf hdhi big data cap hcap hfCap x
  have hH:1 ≤ H:=by
    have hzp:0 ≤ (3*i+1:ℕ)*Z^τ:=by positivity
    dsimp [H];linarith only [hzp]
  have hU:1 ≤ U:=(Real.one_lt_rpow hZ hd0).le
  have hscale:0 ≤ scale:=by dsimp [scale,Y,U];positivity
  have hnorm : -4*Geometry.ell/25=-(4/25:ℝ)*Geometry.ell:=by ring
  have hperM (bin) (hb : bin∈big) : fMid bin  ≤  CM*H^mM*scale:=by
    unfold fMid phaseMiddleNorm
    rw [dif_pos hb]
    split_ifs with hne
    · let A:=data bin hb hne
      have hpM:=hM.2 idx grid hsel k hk i hi j hn hdhalf hdhi ha hahi z hz him bin A.t₀ A.γ A.bank
        A.r A.row A.point A.baseline A.gamma A.old_conductor
        (by simpa only [hgh] using A.upper_conductor) x hx hreserve
      change (∑σ∈Finset.univ.filter A.remaining,∑J∈Finset.univ.powerset,
        classSmallNorm D F J η Z x z (Z^Geometry.y) (Z^d) A.r
          ((A.bank.layoutCap P (by linarith) hdhi cap hcap hfCap).common σ))  ≤  _
      simpa only [ExitPhaseData.remaining,H,scale,Y,U,fee,hnorm,mul_assoc,Final.reserve] using hpM
    · exact mul_nonneg (mul_nonneg hCM.le (pow_nonneg (zero_le_one.trans hH) _)) hscale
  have bM0:=native_phase_sum_le D a hahi big fMid (CM*H^mM*scale)
    (mul_nonneg (mul_nonneg hCM.le (pow_nonneg (zero_le_one.trans hH) _)) hscale) hperM
  have bM : (∑bin∈big,fMid bin)  ≤  max 1 (phaseCardBound D)*CM*H^mM*scale:=by
    apply bM0.trans
    have hp:=mul_le_mul_of_nonneg_right (le_max_right 1 (phaseCardBound D))
      (show 0 ≤ CM*H^mM*scale by positivity)
    convert hp using 1 <;> ring
  have bSplit:=actual_phase_packet_split D F η Z P d a rows z τ i hdhalf hdhi big data
    (fun b hb hn=>(hdata b hb hn).1) cap hcap hfCap hnp hZ0 ha.le x hx hz
  have hold : theta-RawTicket.oldFee  ≤  theta-Final.reserve:=by
    have ht : Final.reserve  ≤  RawTicket.oldFee:=by norm_num [Final.reserve,RawTicket.oldFee]
    linarith only [ht]
  have pM : max 1 (phaseCardBound D)*CM*H^mM*scale  ≤  max 1 (phaseCardBound D)*CM*H^m*scale:=by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hH (show mM ≤ m by dsimp [m];omega)) (by positivity)) hscale
  have pE : CE*H^mE*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
      (Z^d)^(finalPower a d sourceCost fee (theta-Final.reserve))  ≤  CE*H^m*scale:=by
    have hb:=packet_envelope_mono (a:=a) (source:=sourceCost) (fee:=fee) hCE.le hH (by positivity : 0 ≤ Z^Geometry.y) hZ0.le hU hd0
      (show mE ≤ m by dsimp [m];omega) (le_rfl : theta-Final.reserve ≤ theta-Final.reserve)
    convert hb using 1 <;> dsimp [scale,Y,U] <;> ring
  have pL : CL*H^mL*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
      (Z^d)^(finalPower a d sourceCost fee (theta-RawTicket.oldFee))  ≤  CL*H^m*scale:=by
    have hb:=packet_envelope_mono (a:=a) (source:=sourceCost) (fee:=fee) hCL.le hH (by positivity : 0 ≤ Z^Geometry.y) hZ0.le hU hd0
      (show mL ≤ m by dsimp [m];omega) hold
    convert hb using 1 <;> dsimp [scale,Y,U] <;> ring
  have pS : CS*H^mS*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
      (Z^d)^(finalPower a d sourceCost fee (theta-RawTicket.oldFee))  ≤  CS*H^m*scale:=by
    have hb:=packet_envelope_mono (a:=a) (source:=sourceCost) (fee:=fee) hCS.le hH (by positivity : 0 ≤ Z^Geometry.y) hZ0.le hU hd0
      (show mS ≤ m by dsimp [m];omega) hold
    convert hb using 1 <;> dsimp [scale,Y,U] <;> ring
  have bE':=bE.trans (show CE*H^mE*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
      (Z^d)^(finalPower a d sourceCost fee (theta-1/10000000000000))  ≤  CE*H^m*scale from pE)
  have bL':=bL.trans pL
  have bS':=bS.trans pS
  have bM':=bM.trans pM
  have hpart : (∑bin∈bins,packetNorm D F (amplitudeCell D F Z d a rows (fun _=>z) bin) η Z x z (Z^Geometry.y))=
      (∑bin∈big,packetNorm D F (amplitudeCell D F Z d a rows (fun _=>z) bin) η Z x z (Z^Geometry.y))+
      (∑bin∈small,packetNorm D F (amplitudeCell D F Z d a rows (fun _=>z) bin) η Z x z (Z^Geometry.y)):=by
    exact (Finset.sum_filter_add_sum_filter_not bins
      (fun bin=>originalDlow (ticket bin)  ≤  d)
      (fun bin=>packetNorm D F (amplitudeCell D F Z d a rows (fun _=>z) bin) η Z x z (Z^Geometry.y))).symm
  calc
    _ = _ := hpart
    _  ≤  ((CE*H^m*scale+max 1 (phaseCardBound D)*CM*H^m*scale)+CL*H^m*scale)+CS*H^m*scale:=
      add_le_add (bSplit.trans (add_le_add (add_le_add bE' bM') bL')) bS'
    _ = _ := by dsimp [C0,scale,Y,U,H,fee];ring

#print axioms earlier_P1_guarded_mixed_upper
end
end QRH.Cycle092.MixedUpperFinal
