/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual original ordinary-high continuations, with the common original mean. -/
import Candidate.C092.transport.MixedOutsidePaidPrice
import Candidate.C092.transport.DirectCountFields
import Candidate.C092.transport.DirectPrices
import Candidate.C092.transport.PacketJoinE49CountFiber
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace QRH.Cycle092.MixedOutsidePaid
open scoped Classical BigOperators
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorRawFiber HeckeDetectorWitnessRows
open QRH.Record12518109Count QRH.Record12518109Source Cycle25ProbeFinalAssembly
open QRH.Record1252270103Return QRH.Cycle092.PacketJoinE49 QRH.Cycle092.MixedOffsetCount
open QRH.Cycle092.DirectCount QRH.Cycle092.Direct QRH.PositiveGap.Return

def ordinaryHighR (δ p:ℝ):ℝ := max
  (plainCurve countCB countCL (countCap-1/10000000) δ p (anchorTop/2))
  (max (1-δ*((1-(9/2)*(27/1000))+2*p*(27/1000))) (1-(9/10)*δ))

theorem actual_ordinary_high_count (hβ:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκβ:2*HeckeZeroSupremum.beta-1≤(3/4:ℝ)) :
    ∃mesh:ℝ→ℝ,(∀t,0<t → 0 < mesh t) ∧
    ∀(D:Cycle25.Weighted.MomentData)(S:WeightedSourceData D),
      (∀s,D.ell s ≤ mesh D.t/200) → (∀s,D.ell s≤Cycle25.sourceMesh D.t/200) →
    ∀η:Character,∃J:ℕ,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(d a tstar T allowance height:ℝ)(i:ℕ),
      (1/200:ℝ)≤d → 51/100<a → 2*a-1≤3/4 → D.t≤1/10000000 →
      0≤height → 2*Real.pi*allowance+(3*i:ℕ)*T≤height →
    ∀(P:Presented D S η Z d a tstar T allowance i)(F:Slice P),
      (∀s,|(P.batch.external s).im|≤height) → anchorTop≤2*F.fiber.m →
    ∀common:Finset FreeRow,common⊆F.fiber.rows →
      (common.card:ℝ)≤192*(1+height)*(C*(1+height)^J)*
        (Z^d)^(ordinaryHighR (2*a-1) (F.fiber.q/(2*a-1))+countLoss D.ε P.batch.mesh D.t) := by
  obtain ⟨mesh,hm,hfields⟩:=q_actual_count_fields hβ
  refine ⟨mesh,hm,?_⟩
  intro D S hfine hstandard η
  obtain ⟨J,C,hC,hfields⟩:=hfields D S hfine hstandard (3/4) (by norm_num) le_rfl hκβ 1 1 (by norm_num) (by norm_num) η
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hfields] with Z hfields
  refine ⟨hfields.1,?_⟩
  intro d a tstar T allowance height i hd ha hδhi ht hh hf P F him hmhigh common hsub
  have hU:1<Z^d:=Real.one_lt_rpow hfields.1 (by linarith)
  have hδ:0<2*a-1:=by linarith
  have ha':1/2≤a:=by linarith
  have hgeo:=F.fiber.lengths hU
  have hm0:0≤F.fiber.m:=hgeo.2.2.2.2
  obtain ⟨hq,hqhi⟩:=F.fiber.mean_bounds ha'
  have hp:0≤F.fiber.q/(2*a-1):=div_nonneg hq hδ.le
  have hp1:F.fiber.q/(2*a-1)≤1/2:=(div_le_iff₀ hδ).mpr (by linarith)
  have hqp:(2*a-1)*(F.fiber.q/(2*a-1))=F.fiber.q:=mul_div_cancel₀ _ hδ.ne'
  have hq1:2*F.fiber.q≤1:=by linarith
  have hqDt:=mul_le_mul_of_nonneg_right hq1 D.t_pos.le
  have hmsh:(2*a-1)*F.fiber.mesh≤P.batch.mesh:=by
    change (2*a-1)*P.batch.mesh≤P.batch.mesh
    exact mul_le_of_le_one_left P.batch.mesh_nonneg (by linarith)
  have ht0:=D.t_pos.le
  have he0:=D.epsilon_pos.le
  have hraw:=hfields.2 P.batch.rows P.lower d hd a tstar T allowance i P.batch (fun _ hu=>hu)
    P.data P.profile P.widths P.upper P.real F.bin F.label F.left F.right F.nonempty height hh him
  let CC:=C*(1+height)^J
  have hCC:0≤CC:=by dsimp [CC];positivity
  have promote (e:ℝ) (hb:(F.fiber.rows.card:ℝ)≤192*(1+height)*CC*(Z^d)^e)
      (he:e≤ordinaryHighR (2*a-1) (F.fiber.q/(2*a-1))+countLoss D.ε P.batch.mesh D.t) :
      (common.card:ℝ)≤192*(1+height)*CC*
        (Z^d)^(ordinaryHighR (2*a-1) (F.fiber.q/(2*a-1))+countLoss D.ε P.batch.mesh D.t):=by
    have hs:(common.card:ℝ)≤(F.fiber.rows.card:ℝ):=by exact_mod_cast Finset.card_le_card hsub
    exact hs.trans (hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hU.le he) (by positivity)))
  by_cases hmA:F.fiber.m≤naturalM
  · have hmhalf:F.fiber.m<1/2:=by norm_num [naturalM,naturalK,sMinus] at hmA;linarith
    have hmlo:anchorTop/2≤F.fiber.m:=by linarith
    have hsmall:=source_contact_guards
    have haff:AffineMarkedMoment F.fiber Return.window.face CC height D.t:=by
      intro hml hmh selected hsel hs0 hs1 hs2 j k hjk σ hσ t hti
      apply hraw.2 hml hmh selected hsel hs0
      · change (∑s∈selected,F.fiber.widths s)≤3/20-1000*QRH.Cycle090.sourceCost/1143
        change (∑s∈selected,F.fiber.widths s)≤3/20-1/10000000 at hs1
        linarith [hsmall.2.1]
      · change 2*F.fiber.m+(2+10*QRH.Cycle090.sourceCost)*(∑s∈selected,F.fiber.widths s)≤1-QRH.Cycle090.sourceCost
        change 2*F.fiber.m+(200000000001/100000000000:ℝ)*(∑s∈selected,F.fiber.widths s)≤999999999999/1000000000000 at hs2
        nlinarith [mul_nonneg hs0 (show (0:ℝ)≤1/100000000000-10*QRH.Cycle090.sourceCost by linarith [hsmall.2.1])]
      · exact hjk
      · exact hσ
      · exact hti
    have hb:=piecewise_marked_count F.fiber hraw.1 haff hU (by linarith : 1/2<a) (by norm_num : (0:ℝ)≤3/4) hCC hh hf
      hmhalf hm0 (by norm_num [Return.window,countCL]) ht0
      (Return.window.widths D.t ht F.fiber.m hmlo hmA)
      Return.window.cap_le_source Return.window.cap_small
    have hmono:=plainCurve_antitone (B:=countCB) (cap:=countCap-1/10000000) Return.window.lam_gt_one hδ.le hp hp1 hmlo
    have hmax:=le_max_left (plainCurve countCB countCL (countCap-1/10000000) (2*a-1) (F.fiber.q/(2*a-1)) (anchorTop/2))
      (max (1-(2*a-1)*((1-(9/2)*(27/1000))+2*(F.fiber.q/(2*a-1))*(27/1000))) (1-(9/10)*(2*a-1)))
    apply promote _ hb
    change plainCurve countCB countCL (countCap-1/10000000) (2*a-1) (F.fiber.q/(2*a-1)) F.fiber.m+2*F.fiber.q*D.t+4*D.ε+(2*a-1)*F.fiber.mesh+D.t≤_
    change plainCurve countCB countCL (countCap-1/10000000) (2*a-1) (F.fiber.q/(2*a-1)) F.fiber.m ≤ plainCurve countCB countCL (countCap-1/10000000) (2*a-1) (F.fiber.q/(2*a-1)) (anchorTop/2) at hmono
    unfold ordinaryHighR countLoss
    nlinarith only [hmono,hmax,hqDt,hmsh,he0,ht0]
  · by_cases hm45:F.fiber.m<9/20
    · let z:ℝ:=(1-2*F.fiber.m)/(9/2)-D.t
      have hz:0≤z:=by dsimp [z];linarith
      have hzmax:z≤7/37:=by norm_num [naturalM,naturalK,sMinus] at hmA;dsimp [z];linarith
      have hcap:2*F.fiber.m+6*(3/4:ℝ)*z≤1:=by dsimp [z];linarith
      have hb:=Cycle25DetectorRawFiber.plain_marked_count F.fiber hraw.1 hU ha' (by norm_num:(0:ℝ)≤3/4) hCC hh hf z hz hzmax hcap
      apply promote _ hb
      have hmon:1-2*(2*a-1)*F.fiber.m-2*F.fiber.q*(1-2*F.fiber.m)/(9/2)≤
          1-(2*a-1)*((1-(9/2)*(27/1000))+2*(F.fiber.q/(2*a-1))*(27/1000)):=by
        norm_num [naturalM,naturalK,sMinus] at hmA
        have hc0:0≤(2*a-1)-2*F.fiber.q/(9/2):=by linarith
        have hmul:=mul_nonneg hc0 (by linarith : 0≤F.fiber.m-1757/4000)
        nlinarith only [hqp,hmul]
      have hmax:= (le_max_left (1-(2*a-1)*((1-(9/2)*(27/1000))+2*(F.fiber.q/(2*a-1))*(27/1000))) (1-(9/10)*(2*a-1))).trans
        (le_max_right (plainCurve countCB countCL (countCap-1/10000000) (2*a-1) (F.fiber.q/(2*a-1)) (anchorTop/2)) _)
      unfold ordinaryHighR countLoss
      dsimp [z]
      nlinarith only [hmon,hmax,hqDt,hmsh,he0,ht0]
    · have hb:=F.fiber.plain_unmarked_count hraw.1.original hU (by linarith:0≤a) hCC hh hf
      apply promote _ hb
      have hmax:1-(9/10)*(2*a-1)≤ordinaryHighR (2*a-1) (F.fiber.q/(2*a-1)):=
        (le_max_right _ _).trans (le_max_right _ _)
      unfold countLoss
      rw [max_def]
      split_ifs with hm2
      · have hprod:=mul_nonneg hδ.le (by linarith :0≤2*F.fiber.m-9/10)
        nlinarith only [hmax,hgeo.2.2.1,hmsh,he0,ht0,hprod,P.batch.mesh_nonneg]
      · have hprod:=mul_nonneg hδ.le (by linarith :0≤2*F.fiber.m-9/10)
        nlinarith only [hmax,hm45,hmsh,he0,ht0,hprod,P.batch.mesh_nonneg]
end QRH.Cycle092.MixedOutsidePaid
#print axioms QRH.Cycle092.MixedOutsidePaid.actual_ordinary_high_count
