/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine source counts on every frozen bank class outside the middle branch. -/
import Candidate.C092.transport.MixedUpperFinalExitInput
import Candidate.C092.transport.MixedUpperFinalCentral
set_option autoImplicit false
set_option allowUnsafeReducibility true
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
attribute [local reducible] QRH.Record1252270103Return.GenericPhysical.BaselineData.toMomentData
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.MediumWitness QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount
open QRH.Cycle092.PacketJoin HeckeDetectorRawFiber
open QRH.Cycle092.PacketJoinE49 QRH.Cycle090 QRH.Cycle092.MixedTicketTails
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]


theorem actual_bank_exit_counts
    (h : ℝ) (hh : hLower ≤ h) (hh' : h ≤ hUpper)
    (hgeometry : (inferInstance : Geometry.Parameters)=ActualGeometry.parameters h hh hh')
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκ : 2*HeckeZeroSupremum.beta-1 ≤ (3/4:ℝ))
    (logLoss : ℝ) :
    ∃mesh : ℝ→ℝ,(∀t,0<t → 0 < mesh t) ∧
    ∀(D : BaselineData)(F : BaselineSourceData D),
      (∀s,D.length s ≤ mesh D.t/200) →
      (∀s,D.length s ≤ Cycle25.sourceMesh D.t/200) →
      D.ε ≤ 1/10000000 → D.t ≤ 1/10000000 →
    ∀κ : ℝ,7/10 ≤ κ → κ ≤ 3/4 → 2*HeckeZeroSupremum.beta-1 ≤ κ →
    ∀η : Character,∃Cc : ℝ,0<Cc ∧ ∃Jc : ℕ,
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀I : ExitInput D F η Z,
    ∀moment mass fee : ℝ,
      I.d*(3*(countLoss D.ε I.P.mesh D.t+logLoss)/4+moment/4+mass)+fee+rowPad ≤ 1/2000000000000 →
    ∀σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^I.d)),
      (I.layout.common σ).Nonempty → ¬I.remaining σ →
    ∃R : ℝ,(I.layout.common σ).card ≤
      outsideCountEnvelope Cc Jc Z I.d I.τ I.i*(dyadicLength (Z^I.d):ℝ)^2*(Z^I.d)^R ∧
      SelectedNonfloor.rowPrice (2*I.a-1) I.p (R+logLoss) I.d sourceCost+
        I.d*(moment/4+mass)+fee ≤ theta-1/2000000000000 := by
  cases hgeometry
  letI := ActualGeometry.parameters h hh hh'
  have hgh : Geometry.h=h:=ActualGeometry.parameters_h h hh hh'
  obtain ⟨mo,hmo,ho⟩:=actual_bank_outside_count_paid hβ hκ
  obtain ⟨mc,hmc,hc⟩:=actual_bank_central_routes hβ
  refine ⟨fun t=>min (mo t) (mc t),fun t ht=>lt_min (hmo t ht) (hmc t ht),?_⟩
  intro D F hf hs he ht κ hk hk' hκ' η
  have hfo : ∀s,D.length s ≤ mo D.t/200:=fun s=>(hf s).trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hfc : ∀s,D.length s ≤ mc D.t/200:=fun s=>(hf s).trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  obtain ⟨Jo,Co,hCo,ho⟩:=ho D F hfo hs η
  obtain ⟨K,hc⟩:=hc D F hfc hs he ht κ hk hk' hκ' η
  obtain ⟨Ki,hKi,Ji,hi⟩:=actual_bank_all_long_count D F
  obtain ⟨Ci,hCi,hi⟩:=hi η
  have hbinCap : 0 ≤ PacketJoin.phaseCardBound D:=by unfold PacketJoin.phaseCardBound;positivity
  obtain ⟨Cc,hCc,Jc,henv⟩:=native_count_common_envelope
    (Fintype.card (Sum Bool (RayQuotient.Characters F.modulus ⊤)))
    (PacketJoin.phaseCardBound D) hbinCap K Co Ci Ki Jo Ji hCo hCi hKi
  refine ⟨Cc,hCc,Jc,?_⟩
  filter_upwards [ho,hc,hi] with Z ho hc hi
  refine ⟨ho.1,?_⟩
  intro I moment mass fee hbudget σ hne hnot
  have hZ : 1<Z:=ho.1
  have hU : 1<Z^I.d:=Real.one_lt_rpow hZ (by linarith [I.d_min])
  have henv0:=henv Z I.d I.τ (Z^I.d) I.i 0
    (native_height_nonneg (zero_lt_one.trans hZ).le _ _ _) (by simpa only [Nat.cast_zero] using hbinCap)
  let L:=countLoss D.ε I.P.mesh D.t
  let R:=Return.valueI (2*I.a-1) I.p-4*(Mixed.rowBudget I.r.B:ℝ)/3+L
  have hprice : SelectedNonfloor.rowPrice (2*I.a-1) I.p (R+logLoss) I.d sourceCost+
      I.d*(moment/4+mass)+fee ≤ theta-1/2000000000000:=by
    apply large_count_price_paid h hh hh' I.row I.point (by linarith [I.d_min]) (by simpa only [hgh] using I.upper_conductor)
      (loss:=L+logLoss)
    · change R+logLoss ≤ Return.valueI (2*I.a-1) I.p-4*(Mixed.rowBudget I.r.B:ℝ)/3+(L+logLoss)
      dsimp only [R];ring_nf;exact le_rfl
    · exact hbudget
  have cases0:=not_remaining_cases (Z^I.d) (2*I.a-1) I.p I.t₀ I.γ
    ((Mixed.rowV I.r.box:ℝ)/(I.r.box.uHi:ℝ)) (Mixed.rowBudget I.r.B) σ hnot
  rcases cases0 with hall|hout|hcentral
  · have hcount:=hi.2 I.P I.d I.a I.rows I.z I.bin I.t₀ I.γ I.τ I.i I.bank I.hd I.d_hi
      I.a_min I.a_hi he I.lower I.z_re σ hne hall I.r I.row I.point I.baseline I.gamma
    refine ⟨R,?_,hprice⟩
    exact hcount.trans (mul_le_mul_of_nonneg_right henv0.2.2 (Real.rpow_nonneg (zero_lt_one.trans hU).le _))
  · rcases hout with ⟨j,first,outside⟩
    have hbo : I.d*(3*countLoss D.ε I.P.mesh D.t/4+(moment+3*logLoss)/4+mass)+fee+2*rowPad ≤ 7*RawTicket.oldFee:=by
      have hp:=rowPad_small
      norm_num [RawTicket.oldFee] at ⊢
      nlinarith only [hbudget,hp]
    obtain ⟨Ro,hcount,hpaid⟩:=ho.2 I.P I.d I.a I.rows I.z I.bin I.t₀ I.γ I.τ I.i I.bank I.hd I.d_hi
      I.a_min I.a_hi he ht I.lower I.z_re I.z_im σ hne j first outside I.r I.row I.point
      I.baseline I.gamma (by simpa only [hgh] using hh) (by simpa only [hgh] using hh') rfl I.old_conductor I.upper_conductor (moment+3*logLoss) mass fee hbo
    refine ⟨Ro+L,?_,?_⟩
    · exact hcount.trans (mul_le_mul_of_nonneg_right (le_trans (le_max_right 1 _) henv0.2.1)
        (Real.rpow_nonneg (zero_lt_one.trans hU).le _))
    · have hfee : (1/2000000000000:ℝ) ≤ RawTicket.oldFee:=by norm_num [RawTicket.oldFee]
      have heq : SelectedNonfloor.rowPrice (2*I.a-1) I.p (Ro+L+logLoss) I.d sourceCost+
          I.d*(moment/4+mass)+fee =
          SelectedNonfloor.rowPrice (2*I.a-1) I.p (Ro+L) I.d sourceCost+
          I.d*((moment+3*logLoss)/4+mass)+fee:=by unfold SelectedNonfloor.rowPrice;ring
      rw [heq]
      exact hpaid.trans (by linarith only [hfee])
  · rcases hcentral with ⟨j,first,central,hsave⟩
    let M:=I.bank.middleCap I.P I.cap I.cap_pos I.fine hZ I.hd I.d_hi I.a_min I.a_hi
      I.lower I.z_re I.z_im I.r I.row I.point I.baseline I.gamma I.collar σ hne j first central
    have hroute:=hc.2 I.P I.cap I.cap_pos I.fine I.d I.a I.rows I.z I.bin I.t₀ I.γ I.τ I.i I.bank
      hZ I.hd I.d_hi I.a_min I.a_hi I.lower I.z_re I.z_im I.r I.row I.point I.baseline I.gamma I.collar
      σ hne j first central
    have hscore : 4*(Mixed.rowBudget I.r.B:ℝ)/3 ≤ M.delta*M.centered:=hsave
    have hbin := MixedMiddleReturn.paid_native_phase_card D F M rfl rfl
    have henvM:=henv Z I.d I.τ (Z^I.d) I.i (Fintype.card M.base.batch.Bin)
      (native_height_nonneg (zero_lt_one.trans hZ).le _ _ _) hbin
    have hcoef : M.coefficient K ≤ outsideCountEnvelope Cc Jc Z I.d I.τ I.i*(dyadicLength (Z^I.d):ℝ)^2:=
      (le_max_right 1 _).trans henvM.1
    have hraw : ∃E : ℝ,(M.common.card:ℝ) ≤ M.coefficient K*(Z^I.d)^E:=by
      rcases hroute with hc0|hc0
      · exact ⟨_,hc0.2⟩
      · exact ⟨_,hc0.2.2.1⟩
    obtain ⟨E,hraw⟩:=hraw
    have hcoef0 : 0 ≤ M.coefficient K:=by
      exact nonneg_of_mul_nonneg_left ((Nat.cast_nonneg _).trans hraw)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hU) E)
    have hloss : M.loss ≤ L:=by
      change countLoss D.ε (min I.P.mesh I.cap) D.t ≤ countLoss D.ε I.P.mesh D.t
      unfold countLoss
      linarith only [min_le_left I.P.mesh I.cap]
    have hMR : M.R=Return.valueI (2*I.a-1) I.p:=rfl
    have hcount : (M.common.card:ℝ) ≤ M.coefficient K*(Z^I.d)^R:=by
      rcases hroute with hc0|hc0
      · exact hc0.2.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hU.le (by change M.R-4*(Mixed.rowBudget I.r.B:ℝ)/3+M.loss ≤ R; rw [hMR];dsimp [R];linarith only [hloss])) hcoef0)
      · exact hc0.2.2.1.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hU.le (by change M.R-M.delta*M.centered+M.loss ≤ R; rw [hMR];dsimp [R];linarith only [hloss,hscore])) hcoef0)
    exact ⟨R,hcount.trans (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (zero_lt_one.trans hU).le _)),hprice⟩

#print axioms actual_bank_exit_counts
end
end QRH.Cycle092.MixedUpperFinal
