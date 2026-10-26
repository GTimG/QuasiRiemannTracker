/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Exact source margins, retaining all stated width and frequency losses. -/
import Candidate.Uneven.MainParameters
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Sil.Uneven.MainSource

theorem C2_bootstrap_lo_0 {d : ℝ}
    (hd0 : (2561/4000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ highBase .C2 (17/500:ℝ) d+gamma d*supplied (17/500:ℝ) := by
  have hlo : 0 ≤ d-(2561/4000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (-1386875243469748000000+(-33298880005882151492785*d)+(55953308981784020277114*(d^2))) := by
    have he : (-1386875243469748000000+(-33298880005882151492785*d)+(55953308981784020277114*(d^2)))=(3678411962542743363843871194/6241:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^2+(19475212882997849252858537120/6241:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^1+(16146005521810419959564134400/6241:ℝ)*(d-(2561/4000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (164115000000000000000000+(-65646000000000000000000*d)) := by
    have he : (164115000000000000000000+(-65646000000000000000000*d))=120788640000000000000000+65646000000000000000000*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (highBase .C2 (17/500:ℝ) d+gamma d*supplied (17/500:ℝ))-highReserve=(-1386875243469748000000+(-33298880005882151492785*d)+(55953308981784020277114*(d^2)))/(164115000000000000000000+(-65646000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_bootstrap_lo_1 {d : ℝ}
    (hd0 : (2561/4000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C2 (17/500:ℝ) d 0 := by
  have hlo : 0 ≤ d-(2561/4000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (845088755742500000000+(-34191665605567050692785*d)+(51489380983359524277114*(d^2))) := by
    have he : (845088755742500000000+(-34191665605567050692785*d)+(51489380983359524277114*(d^2)))=(966481961011895129427871194/6241:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^2+(11962957733009233424378537120/6241:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^1+(11317820998714485085964134400/6241:ℝ)*(d-(2561/4000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (164115000000000000000000+(-65646000000000000000000*d)) := by
    have he : (164115000000000000000000+(-65646000000000000000000*d))=120788640000000000000000+65646000000000000000000*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C2 (17/500:ℝ) d 0)-highReserve=(845088755742500000000+(-34191665605567050692785*d)+(51489380983359524277114*(d^2)))/(164115000000000000000000+(-65646000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_bootstrap_lo_2 {d : ℝ}
    (hd0 : (2561/4000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C2 (17/500:ℝ) d 1 := by
  have hlo : 0 ≤ d-(2561/4000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (44677556551021691537500000000+(-1685439925914923942456206466575*d)+(-998264152364380491716773034652*(d^3))+(3162687942228319695628415173260*(d^2))) := by
    have he : (44677556551021691537500000000+(-1685439925914923942456206466575*d)+(-998264152364380491716773034652*(d^3))+(3162687942228319695628415173260*(d^2)))=(1800858746251383544648966793347804388/493039:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^3+(1442262758012529097393953853097988311360/493039:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^2+(2910209911781088261116864506748527206400/493039:ℝ)*(d-(2561/4000:ℝ))^2*((33/50:ℝ)-d)^1+(1469255829355392965474304074383654912000/493039:ℝ)*(d-(2561/4000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (8676316118925000000000000000000+(-7597512895140000000000000000000*d)+(1650794579028000000000000000000*(d^2))) := by
    have he : (8676316118925000000000000000000+(-7597512895140000000000000000000*d)+(1650794579028000000000000000000*(d^2)))=4381043726757196800000000000000+(21804268975035372000000000000000000/79:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^2+(21673856203292160000000000000000000/79:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C2 (17/500:ℝ) d 1)-highReserve=(44677556551021691537500000000+(-1685439925914923942456206466575*d)+(-998264152364380491716773034652*(d^3))+(3162687942228319695628415173260*(d^2)))/(8676316118925000000000000000000+(-7597512895140000000000000000000*d)+(1650794579028000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_bootstrap_lo_3 {d : ℝ}
    (hd0 : (2561/4000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C2 (17/500:ℝ) d 2 := by
  have hlo : 0 ≤ d-(2561/4000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (845088755742500000000+(-34567220611995462432785*d)+(51940046991073618365114*(d^2))) := by
    have he : (845088755742500000000+(-34567220611995462432785*d)+(51940046991073618365114*(d^2)))=(75089083939836155809319194/6241:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^2+(10243853188863152970881577120/6241:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^1+(10492921938194607267288934400/6241:ℝ)*(d-(2561/4000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (164115000000000000000000+(-65646000000000000000000*d)) := by
    have he : (164115000000000000000000+(-65646000000000000000000*d))=120788640000000000000000+65646000000000000000000*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C2 (17/500:ℝ) d 2)-highReserve=(845088755742500000000+(-34567220611995462432785*d)+(51940046991073618365114*(d^2)))/(164115000000000000000000+(-65646000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_bootstrap_lo_4 {d : ℝ}
    (hd0 : (2561/4000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C2 (17/500:ℝ) d 3 := by
  have hlo : 0 ≤ d-(2561/4000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (21127218893562500000000+(-451453225947750717319625*d)+(-270529704734879092988052*(d^3))+(853525197192452739397980*(d^2))) := by
    have he : (21127218893562500000000+(-451453225947750717319625*d)+(-270529704734879092988052*(d^3))+(853525197192452739397980*(d^2)))=(701472963063287044276914577098988/493039:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^3+(2494740987788420119701736668103360/493039:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^2+(2893398697467946823997283600486400/493039:ℝ)*(d-(2561/4000:ℝ))^2*((33/50:ℝ)-d)^1+(1099997291047720968519333773312000/493039:ℝ)*(d-(2561/4000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (4102875000000000000000000+(-4595220000000000000000000*d)+(1181628000000000000000000*(d^2))) := by
    have he : (4102875000000000000000000+(-4595220000000000000000000*d)+(1181628000000000000000000*(d^2)))=1584746956800000000000000+(12235232772000000000000000000/79:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^2+(12141884160000000000000000000/79:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C2 (17/500:ℝ) d 3)-highReserve=(21127218893562500000000+(-451453225947750717319625*d)+(-270529704734879092988052*(d^3))+(853525197192452739397980*(d^2)))/(4102875000000000000000000+(-4595220000000000000000000*d)+(1181628000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_bootstrap_lo_5 {d : ℝ}
    (hd0 : (2561/4000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C2 (17/500:ℝ) d 4 := by
  have hlo : 0 ≤ d-(2561/4000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (71645631732561152562500000000+(-1473252853065811152876385777625*d)+(-875702875659059938089963103956*(d^3))+(2767095029293533729567622070940*(d^2))) := by
    have he : (71645631732561152562500000000+(-1473252853065811152876385777625*d)+(-875702875659059938089963103956*(d^3))+(2767095029293533729567622070940*(d^2)))=(2102648592026958787879029520287544853164/493039:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^3+(7563234034496923405738856983012201574080/493039:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^2+(8845610447990443936480933213421376819200/493039:ℝ)*(d-(2561/4000:ℝ))^2*((33/50:ℝ)-d)^1+(3384593249850367251368289813377908736000/493039:ℝ)*(d-(2561/4000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (13913476864875000000000000000000+(-15976970088660000000000000000000*d)+(4164631737084000000000000000000*(d^2))) := by
    have he : (13913476864875000000000000000000+(-15976970088660000000000000000000*d)+(4164631737084000000000000000000*(d^2)))=5182790191033190400000000000000+(42247630690066116000000000000000000/79:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^2+(41918624782836480000000000000000000/79:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C2 (17/500:ℝ) d 4)-highReserve=(71645631732561152562500000000+(-1473252853065811152876385777625*d)+(-875702875659059938089963103956*(d^3))+(2767095029293533729567622070940*(d^2)))/(13913476864875000000000000000000+(-15976970088660000000000000000000*d)+(4164631737084000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_bootstrap_lo_6 {d : ℝ}
    (hd0 : (2561/4000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C2 (17/500:ℝ) d 5 := by
  have hlo : 0 ≤ d-(2561/4000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (21127218893562500000000+(-457086551044176893419625*d)+(-273233700781163657516052*(d^3))+(862538517346734621157980*(d^2))) := by
    have he : (21127218893562500000000+(-457086551044176893419625*d)+(-273233700781163657516052*(d^3))+(862538517346734621157980*(d^2)))=(661686533388052764048424127130988/493039:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^3+(2378646566113501840465358099143360/493039:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^2+(2780664496131211684612108970086400/493039:ℝ)*(d-(2561/4000:ℝ))^2*((33/50:ℝ)-d)^1+(1063569748535163164046636941312000/493039:ℝ)*(d-(2561/4000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (4102875000000000000000000+(-4595220000000000000000000*d)+(1181628000000000000000000*(d^2))) := by
    have he : (4102875000000000000000000+(-4595220000000000000000000*d)+(1181628000000000000000000*(d^2)))=1584746956800000000000000+(12235232772000000000000000000/79:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^2+(12141884160000000000000000000/79:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C2 (17/500:ℝ) d 5)-highReserve=(21127218893562500000000+(-457086551044176893419625*d)+(-273233700781163657516052*(d^3))+(862538517346734621157980*(d^2)))/(4102875000000000000000000+(-4595220000000000000000000*d)+(1181628000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_bootstrap_lo_7 {d : ℝ}
    (hd0 : (2561/4000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C2 (17/500:ℝ) d 6 := by
  have hlo : 0 ≤ d-(2561/4000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (211272188935625000000000+(-40571602165004701530494*(d^2))+(16920129865614253826235*d)) := by
    have he : (211272188935625000000000+(-40571602165004701530494*(d^2))+(16920129865614253826235*d))=(3287587014190090615169168201826/6241:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^2+(6564103977460872162129530632480/6241:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^1+(3276263755901669752618110617600/6241:ℝ)*(d-(2561/4000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (41028750000000000000000000+(-16411500000000000000000000*d)) := by
    have he : (41028750000000000000000000+(-16411500000000000000000000*d))=30197160000000000000000000+16411500000000000000000000*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C2 (17/500:ℝ) d 6)-highReserve=(211272188935625000000000+(-40571602165004701530494*(d^2))+(16920129865614253826235*d))/(41028750000000000000000000+(-16411500000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_bootstrap_hi_0 {d : ℝ}
    (hd0 : (2561/4000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ highBase .C2 (1/25:ℝ) d+gamma d*supplied (1/25:ℝ) := by
  have hlo : 0 ≤ d-(2561/4000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (-1031126599682248000000+(-32779185622876151492785*d)+(54489112015515620277114*(d^2))) := by
    have he : (-1031126599682248000000+(-32779185622876151492785*d)+(54489112015515620277114*(d^2)))=(5090880131855360647443871194/6241:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^2+(21871902914616066980858537120/6241:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^1+(17121089330849539319564134400/6241:ℝ)*(d-(2561/4000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (164115000000000000000000+(-65646000000000000000000*d)) := by
    have he : (164115000000000000000000+(-65646000000000000000000*d))=120788640000000000000000+65646000000000000000000*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (highBase .C2 (1/25:ℝ) d+gamma d*supplied (1/25:ℝ))-highReserve=(-1031126599682248000000+(-32779185622876151492785*d)+(54489112015515620277114*(d^2)))/(164115000000000000000000+(-65646000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_bootstrap_hi_1 {d : ℝ}
    (hd0 : (2561/4000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C2 (1/25:ℝ) d 0 := by
  have hlo : 0 ≤ d-(2561/4000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (1594713399530000000000+(-33829521622561050692785*d)+(49237432017091124277114*(d^2))) := by
    have he : (1594713399530000000000+(-33829521622561050692785*d)+(49237432017091124277114*(d^2)))=(1900374247532512413027871194/6241:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^2+(13033955678867451152378537120/6241:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^1+(11440872244553604445964134400/6241:ℝ)*(d-(2561/4000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (164115000000000000000000+(-65646000000000000000000*d)) := by
    have he : (164115000000000000000000+(-65646000000000000000000*d))=120788640000000000000000+65646000000000000000000*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C2 (1/25:ℝ) d 0)-highReserve=(1594713399530000000000+(-33829521622561050692785*d)+(49237432017091124277114*(d^2)))/(164115000000000000000000+(-65646000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_bootstrap_hi_2 {d : ℝ}
    (hd0 : (2561/4000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C2 (1/25:ℝ) d 1 := by
  have hlo : 0 ≤ d-(2561/4000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (84308183733405371350000000000+(-1713143069209374967923706466575*d)+(-966996508931436627235573034652*(d^3))+(3089259190614559055842415173260*(d^2))) := by
    have he : (84308183733405371350000000000+(-1713143069209374967923706466575*d)+(-966996508931436627235573034652*(d^3))+(3089259190614559055842415173260*(d^2)))=(1801212669814844885309539050547804388/493039:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^3+(1337001746533264034921283827081988311360/493039:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^2+(2699353022785937046961084374908527206400/493039:ℝ)*(d-(2561/4000:ℝ))^2*((33/50:ℝ)-d)^1+(1363675721930720810341854487183654912000/493039:ℝ)*(d-(2561/4000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (8676316118925000000000000000000+(-7597512895140000000000000000000*d)+(1650794579028000000000000000000*(d^2))) := by
    have he : (8676316118925000000000000000000+(-7597512895140000000000000000000*d)+(1650794579028000000000000000000*(d^2)))=4381043726757196800000000000000+(21804268975035372000000000000000000/79:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^2+(21673856203292160000000000000000000/79:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C2 (1/25:ℝ) d 1)-highReserve=(84308183733405371350000000000+(-1713143069209374967923706466575*d)+(-966996508931436627235573034652*(d^3))+(3089259190614559055842415173260*(d^2)))/(8676316118925000000000000000000+(-7597512895140000000000000000000*d)+(1650794579028000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_bootstrap_hi_3 {d : ℝ}
    (hd0 : (2561/4000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C2 (1/25:ℝ) d 2 := by
  have hlo : 0 ≤ d-(2561/4000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (1594713399530000000000+(-34575285609041562432785*d)+(50132348800867738365114*(d^2))) := by
    have he : (1594713399530000000000+(-34575285609041562432785*d)+(50132348800867738365114*(d^2)))=(130277473034288276329319194/6241:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^2+(9620218047696962740481577120/6241:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^1+(9802816563528890019288934400/6241:ℝ)*(d-(2561/4000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (164115000000000000000000+(-65646000000000000000000*d)) := by
    have he : (164115000000000000000000+(-65646000000000000000000*d))=120788640000000000000000+65646000000000000000000*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C2 (1/25:ℝ) d 2)-highReserve=(1594713399530000000000+(-34575285609041562432785*d)+(50132348800867738365114*(d^2)))/(164115000000000000000000+(-65646000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_bootstrap_hi_4 {d : ℝ}
    (hd0 : (2561/4000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C2 (1/25:ℝ) d 3 := by
  have hlo : 0 ≤ d-(2561/4000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (39867834988250000000000+(-490579162836525717319625*d)+(-270489861083127892988052*(d^3))+(866077464243434739397980*(d^2))) := by
    have he : (39867834988250000000000+(-490579162836525717319625*d)+(-270489861083127892988052*(d^3))+(866077464243434739397980*(d^2)))=(627624522404143600118041777098988/493039:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^3+(2244118912168202581174120668103360/493039:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^2+(2614015133486886334361443600486400/493039:ℝ)*(d-(2561/4000:ℝ))^2*((33/50:ℝ)-d)^1+(997387381672208789012133773312000/493039:ℝ)*(d-(2561/4000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (4102875000000000000000000+(-4595220000000000000000000*d)+(1181628000000000000000000*(d^2))) := by
    have he : (4102875000000000000000000+(-4595220000000000000000000*d)+(1181628000000000000000000*(d^2)))=1584746956800000000000000+(12235232772000000000000000000/79:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^2+(12141884160000000000000000000/79:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C2 (1/25:ℝ) d 3)-highReserve=(39867834988250000000000+(-490579162836525717319625*d)+(-270489861083127892988052*(d^3))+(866077464243434739397980*(d^2)))/(4102875000000000000000000+(-4595220000000000000000000*d)+(1181628000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_bootstrap_hi_5 {d : ℝ}
    (hd0 : (2561/4000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C2 (1/25:ℝ) d 4 := by
  have hlo : 0 ≤ d-(2561/4000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (135197928223908952250000000000+(-1628794698522331902763885777625*d)+(-887425967234625097266363103956*(d^3))+(2848451128976439279513622070940*(d^2))) := by
    have he : (135197928223908952250000000000+(-1628794698522331902763885777625*d)+(-887425967234625097266363103956*(d^3))+(2848451128976439279513622070940*(d^2)))=(1733969330965335345303977882839144853164/493039:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^3+(6374047865113301989595112682564201574080/493039:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^2+(7574744748493574492184311281901376819200/493039:ℝ)*(d-(2561/4000:ℝ))^2*((33/50:ℝ)-d)^1+(2934228678734148455569845371777908736000/493039:ℝ)*(d-(2561/4000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (13913476864875000000000000000000+(-15976970088660000000000000000000*d)+(4164631737084000000000000000000*(d^2))) := by
    have he : (13913476864875000000000000000000+(-15976970088660000000000000000000*d)+(4164631737084000000000000000000*(d^2)))=5182790191033190400000000000000+(42247630690066116000000000000000000/79:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^2+(41918624782836480000000000000000000/79:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C2 (1/25:ℝ) d 4)-highReserve=(135197928223908952250000000000+(-1628794698522331902763885777625*d)+(-887425967234625097266363103956*(d^3))+(2848451128976439279513622070940*(d^2)))/(13913476864875000000000000000000+(-15976970088660000000000000000000*d)+(4164631737084000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_bootstrap_hi_6 {d : ℝ}
    (hd0 : (2561/4000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C2 (1/25:ℝ) d 5 := by
  have hlo : 0 ≤ d-(2561/4000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (39867834988250000000000+(-501765622633733393419625*d)+(-275859361785787577516052*(d^3))+(883975799918967021157980*(d^2))) := by
    have he : (39867834988250000000000+(-501765622633733393419625*d)+(-275859361785787577516052*(d^3))+(883975799918967021157980*(d^2)))=(548618022971189864000638607130988/493039:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^3+(2013582673176697423520903699143360/493039:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^2+(2390151502427540462371852970086400/493039:ℝ)*(d-(2561/4000:ℝ))^2*((33/50:ℝ)-d)^1+(925050842798157399930156941312000/493039:ℝ)*(d-(2561/4000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (4102875000000000000000000+(-4595220000000000000000000*d)+(1181628000000000000000000*(d^2))) := by
    have he : (4102875000000000000000000+(-4595220000000000000000000*d)+(1181628000000000000000000*(d^2)))=1584746956800000000000000+(12235232772000000000000000000/79:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^2+(12141884160000000000000000000/79:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C2 (1/25:ℝ) d 5)-highReserve=(39867834988250000000000+(-501765622633733393419625*d)+(-275859361785787577516052*(d^3))+(883975799918967021157980*(d^2)))/(4102875000000000000000000+(-4595220000000000000000000*d)+(1181628000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_bootstrap_hi_7 {d : ℝ}
    (hd0 : (2561/4000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C2 (1/25:ℝ) d 6 := by
  have hlo : 0 ≤ d-(2561/4000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (398678349882500000000000+(-420378063678431744898765*d)+(104362689501113697959506*(d^2))) := by
    have he : (398678349882500000000000+(-420378063678431744898765*d)+(104362689501113697959506*(d^2)))=(2756986477045579139451720491826/6241:ℝ)*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^2+(5423362595923125492030369832480/6241:ℝ)*(d-(2561/4000:ℝ))^1*((33/50:ℝ)-d)^1+(2667027446422722803167614617600/6241:ℝ)*(d-(2561/4000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (41028750000000000000000000+(-16411500000000000000000000*d)) := by
    have he : (41028750000000000000000000+(-16411500000000000000000000*d))=30197160000000000000000000+16411500000000000000000000*(d-(2561/4000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C2 (1/25:ℝ) d 6)-highReserve=(398678349882500000000000+(-420378063678431744898765*d)+(104362689501113697959506*(d^2)))/(41028750000000000000000000+(-16411500000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_saturated_lo_0 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ highBase .C2 (17/500:ℝ) d+gamma d*supplied (17/500:ℝ) := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (-1386875243469748000000+(-33298880005882151492785*d)+(55953308981784020277114*(d^2))) := by
    have he : (-1386875243469748000000+(-33298880005882151492785*d)+(55953308981784020277114*(d^2)))=(10091253451131512474727584/81:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(56686045967328504695160100/81:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1+(51127010543721497862878750/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (164115000000000000000000+(-65646000000000000000000*d)) := by
    have he : (164115000000000000000000+(-65646000000000000000000*d))=114880500000000000000000+65646000000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (highBase .C2 (17/500:ℝ) d+gamma d*supplied (17/500:ℝ))-highReserve=(-1386875243469748000000+(-33298880005882151492785*d)+(55953308981784020277114*(d^2)))/(164115000000000000000000+(-65646000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_saturated_lo_1 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .C2 (17/500:ℝ) d 0 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (845088755742500000000+(-34191665605567050692785*d)+(51489380983359524277114*(d^2))) := by
    have he : (845088755742500000000+(-34191665605567050692785*d)+(51489380983359524277114*(d^2)))=(7073638124196553178727584/81:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(44544161811613875575160100/81:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1+(41641163547069443862878750/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (164115000000000000000000+(-65646000000000000000000*d)) := by
    have he : (164115000000000000000000+(-65646000000000000000000*d))=114880500000000000000000+65646000000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .C2 (17/500:ℝ) d 0)-highReserve=(845088755742500000000+(-34191665605567050692785*d)+(51489380983359524277114*(d^2)))/(164115000000000000000000+(-65646000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_saturated_lo_2 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .C2 (17/500:ℝ) d 1 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (21127218893562500000000+(-451453225947750717319625*d)+(-270529704734879092988052*(d^3))+(853525197192452739397980*(d^2))) := by
    have he : (21127218893562500000000+(-451453225947750717319625*d)+(-270529704734879092988052*(d^3))+(853525197192452739397980*(d^2)))=(17187457672620640133114590208/729:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(26837612158583047132182257600/243:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(37346032875452412896510345000/243:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(48515503668477010567310562500/729:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (4102875000000000000000000+(-4595220000000000000000000*d)+(1181628000000000000000000*(d^2))) := by
    have he : (4102875000000000000000000+(-4595220000000000000000000*d)+(1181628000000000000000000*(d^2)))=1321125750000000000000000+32545828000000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+31364200000000000000000000*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .C2 (17/500:ℝ) d 1)-highReserve=(21127218893562500000000+(-451453225947750717319625*d)+(-270529704734879092988052*(d^3))+(853525197192452739397980*(d^2)))/(4102875000000000000000000+(-4595220000000000000000000*d)+(1181628000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_saturated_lo_3 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .C2 (17/500:ℝ) d 2 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (97185206910387500000000+(-3698624075606280779670275*d)+(-2191106340112189406964156*(d^3))+(6941665847416448549278500*(d^2))) := by
    have he : (97185206910387500000000+(-3698624075606280779670275*d)+(-2191106340112189406964156*(d^3))+(6941665847416448549278500*(d^2)))=(49948651787953167738766106624/729:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(127979764119697833389463684800/243:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(213039719745227145553582835000/243:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(303531202142599318153446687500/729:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (18873225000000000000000000+(-16411500000000000000000000*d)+(3544884000000000000000000*(d^2))) := by
    have he : (18873225000000000000000000+(-16411500000000000000000000*d)+(3544884000000000000000000*(d^2)))=8558597250000000000000000+126813484000000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+123268600000000000000000000*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .C2 (17/500:ℝ) d 2)-highReserve=(97185206910387500000000+(-3698624075606280779670275*d)+(-2191106340112189406964156*(d^3))+(6941665847416448549278500*(d^2)))/(18873225000000000000000000+(-16411500000000000000000000*d)+(3544884000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_saturated_lo_4 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .C2 (17/500:ℝ) d 3 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (156341419812362500000000+(-3233178040914810478165225*d)+(-1922260271955243038241732*(d^3))+(6073907269077051546870420*(d^2))) := by
    have he : (156341419812362500000000+(-3233178040914810478165225*d)+(-1922260271955243038241732*(d^3))+(6073907269077051546870420*(d^2)))=(115595780072506685705361468928/729:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(183766874998780264545244489600/243:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(258061116137689153279237345000/243:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(337077175750977979732461812500/729:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (30361275000000000000000000+(-34792380000000000000000000*d)+(9059148000000000000000000*(d^2))) := by
    have he : (30361275000000000000000000+(-34792380000000000000000000*d)+(9059148000000000000000000*(d^2)))=9362760750000000000000000+244655348000000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+235596200000000000000000000*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .C2 (17/500:ℝ) d 3)-highReserve=(156341419812362500000000+(-3233178040914810478165225*d)+(-1922260271955243038241732*(d^3))+(6073907269077051546870420*(d^2)))/(30361275000000000000000000+(-34792380000000000000000000*d)+(9059148000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_saturated_hi_0 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ highBase .C2 (1/25:ℝ) d+gamma d*supplied (1/25:ℝ) := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (-1031126599682248000000+(-32779185622876151492785*d)+(54489112015515620277114*(d^2))) := by
    have he : (-1031126599682248000000+(-32779185622876151492785*d)+(54489112015515620277114*(d^2)))=(10700680831780962074727584/81:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(56633159677405944695160100/81:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1+(50346096918881747862878750/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (164115000000000000000000+(-65646000000000000000000*d)) := by
    have he : (164115000000000000000000+(-65646000000000000000000*d))=114880500000000000000000+65646000000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (highBase .C2 (1/25:ℝ) d+gamma d*supplied (1/25:ℝ))-highReserve=(-1031126599682248000000+(-32779185622876151492785*d)+(54489112015515620277114*(d^2)))/(164115000000000000000000+(-65646000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_saturated_hi_1 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .C2 (1/25:ℝ) d 0 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (1594713399530000000000+(-33829521622561050692785*d)+(49237432017091124277114*(d^2))) := by
    have he : (1594713399530000000000+(-33829521622561050692785*d)+(49237432017091124277114*(d^2)))=(7150545152846002778727584/81:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(42348590081691315575160100/81:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1+(39186276922229693862878750/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (164115000000000000000000+(-65646000000000000000000*d)) := by
    have he : (164115000000000000000000+(-65646000000000000000000*d))=114880500000000000000000+65646000000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .C2 (1/25:ℝ) d 0)-highReserve=(1594713399530000000000+(-33829521622561050692785*d)+(49237432017091124277114*(d^2)))/(164115000000000000000000+(-65646000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_saturated_hi_2 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .C2 (1/25:ℝ) d 1 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (39867834988250000000000+(-490579162836525717319625*d)+(-270489861083127892988052*(d^3))+(866077464243434739397980*(d^2))) := by
    have he : (39867834988250000000000+(-490579162836525717319625*d)+(-270489861083127892988052*(d^3))+(866077464243434739397980*(d^2)))=(15584177838628262328314590208/729:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(24559186023669560572182257600/243:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(34426564564817730896510345000/243:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(44989126353343173067310562500/729:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (4102875000000000000000000+(-4595220000000000000000000*d)+(1181628000000000000000000*(d^2))) := by
    have he : (4102875000000000000000000+(-4595220000000000000000000*d)+(1181628000000000000000000*(d^2)))=1321125750000000000000000+32545828000000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+31364200000000000000000000*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .C2 (1/25:ℝ) d 1)-highReserve=(39867834988250000000000+(-490579162836525717319625*d)+(-270489861083127892988052*(d^3))+(866077464243434739397980*(d^2)))/(4102875000000000000000000+(-4595220000000000000000000*d)+(1181628000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_saturated_hi_3 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .C2 (1/25:ℝ) d 2 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (183392040945950000000000+(-3756760791200865779670275*d)+(-2121812613674775806964156*(d^3))+(6777893124115058549278500*(d^2))) := by
    have he : (183392040945950000000000+(-3756760791200865779670275*d)+(-2121812613674775806964156*(d^3))+(6777893124115058549278500*(d^2)))=(46367524436854744084366106624/729:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(118885726709279178509463684800/243:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(198361030184108919553582835000/243:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(283246633465975055653446687500/729:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (18873225000000000000000000+(-16411500000000000000000000*d)+(3544884000000000000000000*(d^2))) := by
    have he : (18873225000000000000000000+(-16411500000000000000000000*d)+(3544884000000000000000000*(d^2)))=8558597250000000000000000+126813484000000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+123268600000000000000000000*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .C2 (1/25:ℝ) d 2)-highReserve=(183392040945950000000000+(-3756760791200865779670275*d)+(-2121812613674775806964156*(d^3))+(6777893124115058549278500*(d^2)))/(18873225000000000000000000+(-16411500000000000000000000*d)+(3544884000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C2_saturated_hi_4 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .C2 (1/25:ℝ) d 3 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (295021978913050000000000+(-3571737197907375478165225*d)+(-1947269496538843838241732*(d^3))+(6249665103876969546870420*(d^2))) := by
    have he : (295021978913050000000000+(-3571737197907375478165225*d)+(-1947269496538843838241732*(d^3))+(6249665103876969546870420*(d^2)))=(100197356366058670908561468928/729:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(164191225200056566785244489600/243:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(234649087086025621279237345000/243:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(310151382560989017232461812500/729:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (30361275000000000000000000+(-34792380000000000000000000*d)+(9059148000000000000000000*(d^2))) := by
    have he : (30361275000000000000000000+(-34792380000000000000000000*d)+(9059148000000000000000000*(d^2)))=9362760750000000000000000+244655348000000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+235596200000000000000000000*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .C2 (1/25:ℝ) d 3)-highReserve=(295021978913050000000000+(-3571737197907375478165225*d)+(-1947269496538843838241732*(d^3))+(6249665103876969546870420*(d^2)))/(30361275000000000000000000+(-34792380000000000000000000*d)+(9059148000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

end Sil.Uneven.MainSource
