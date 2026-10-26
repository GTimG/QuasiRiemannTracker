/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Exact source margins, retaining all stated width and frequency losses. -/
import Candidate.Uneven.MainParameters
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Sil.Uneven.MainSource

theorem A2_bootstrap_lo_0 {d : ℝ}
    (hd0 : (649/1000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ highBase .A2 (17/500:ℝ) d+gamma d*supplied (17/500:ℝ) := by
  have hlo : 0 ≤ d-(649/1000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (-115128744299524800000+(-3122676218910692642255*d)+(5149542741013801024902*(d^2))) := by
    have he : (-115128744299524800000+(-3122676218910692642255*d)+(5149542741013801024902*(d^2)))=(27246941685189680666252302/121:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^2+(93669616218556793301250360/121:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^1+(67045769205029782559011200/121:ℝ)*(d-(649/1000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (15099000000000000000000+(-6039600000000000000000*d)) := by
    have he : (15099000000000000000000+(-6039600000000000000000*d))=11112864000000000000000+6039600000000000000000*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (highBase .A2 (17/500:ℝ) d+gamma d*supplied (17/500:ℝ))-highReserve=(-115128744299524800000+(-3122676218910692642255*d)+(5149542741013801024902*(d^2)))/(15099000000000000000000+(-6039600000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_bootstrap_lo_1 {d : ℝ}
    (hd0 : (649/1000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A2 (17/500:ℝ) d 0 := by
  have hlo : 0 ≤ d-(649/1000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (90217655628000000000+(-3204814778881702562255*d)+(4738849941158751424902*(d^2))) := by
    have he : (90217655628000000000+(-3204814778881702562255*d)+(4738849941158751424902*(d^2)))=(6301198199782296016652302/121:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^2+(45010733291730516693250360/121:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^1+(39282935934828429599011200/121:ℝ)*(d-(649/1000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (15099000000000000000000+(-6039600000000000000000*d)) := by
    have he : (15099000000000000000000+(-6039600000000000000000*d))=11112864000000000000000+6039600000000000000000*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A2 (17/500:ℝ) d 0)-highReserve=(90217655628000000000+(-3204814778881702562255*d)+(4738849941158751424902*(d^2)))/(15099000000000000000000+(-6039600000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_bootstrap_lo_2 {d : ℝ}
    (hd0 : (649/1000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A2 (17/500:ℝ) d 1 := by
  have hlo : 0 ≤ d-(649/1000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (4769563414293886260000000000+(-158624901228460033701538450225*d)+(-92063949871880038137936552036*(d^3))+(292846705024756823023856760180*(d^2))) := by
    have he : (4769563414293886260000000000+(-158624901228460033701538450225*d)+(-92063949871880038137936552036*(d^3))+(292846705024756823023856760180*(d^2)))=(2776910415175182687715187030391836/1331:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^3+(1165066956326413546337527979880412720/1331:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^2+(2335548562956830517652995008166924800/1331:ℝ)*(d-(649/1000:ℝ))^2*((33/50:ℝ)-d)^1+(1173135979928312681672420621766144000/1331:ℝ)*(d-(649/1000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (798243287205000000000000000000+(-698990629764000000000000000000*d)+(151877325952800000000000000000*(d^2))) := by
    have he : (798243287205000000000000000000+(-698990629764000000000000000000*d)+(151877325952800000000000000000*(d^2)))=403067234745799680000000000000+(500183210091784800000000000000000/11:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^2+(498512559506304000000000000000000/11:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A2 (17/500:ℝ) d 1)-highReserve=(4769563414293886260000000000+(-158624901228460033701538450225*d)+(-92063949871880038137936552036*(d^3))+(292846705024756823023856760180*(d^2)))/(798243287205000000000000000000+(-698990629764000000000000000000*d)+(151877325952800000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_bootstrap_lo_3 {d : ℝ}
    (hd0 : (649/1000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A2 (17/500:ℝ) d 2 := by
  have hlo : 0 ≤ d-(649/1000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (90217655628000000000+(-3240064970918791486255*d)+(4781150171603258133702*(d^2))) := by
    have he : (90217655628000000000+(-3240064970918791486255*d)+(4781150171603258133702*(d^2)))=(1240722931168254593921102/121:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^2+(35105993332381122472034360/121:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^1+(34443789571976862112291200/121:ℝ)*(d-(649/1000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (15099000000000000000000+(-6039600000000000000000*d)) := by
    have he : (15099000000000000000000+(-6039600000000000000000*d))=11112864000000000000000+6039600000000000000000*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A2 (17/500:ℝ) d 2)-highReserve=(90217655628000000000+(-3240064970918791486255*d)+(4781150171603258133702*(d^2)))/(15099000000000000000000+(-6039600000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_bootstrap_lo_4 {d : ℝ}
    (hd0 : (649/1000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A2 (17/500:ℝ) d 3 := by
  have hlo : 0 ≤ d-(649/1000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (2255441390700000000000+(-43485961590253134056375*d)+(-25278996358942391248236*(d^3))+(80231004910864703743140*(d^2))) := by
    have he : (2255441390700000000000+(-43485961590253134056375*d)+(-25278996358942391248236*(d^3))+(80231004910864703743140*(d^2)))=(916179302133341784366720958036/1331:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^3+(3064361845026931612031698496720/1331:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^2+(3383938332332838338989155884800/1331:ℝ)*(d-(649/1000:ℝ))^2*((33/50:ℝ)-d)^1+(1235722143095094759001426944000/1331:ℝ)*(d-(649/1000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (377475000000000000000000+(-422772000000000000000000*d)+(108712800000000000000000*(d^2))) := by
    have he : (377475000000000000000000+(-422772000000000000000000*d)+(108712800000000000000000*(d^2)))=145800775680000000000000+(280466944800000000000000000/11:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^2+(279271104000000000000000000/11:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A2 (17/500:ℝ) d 3)-highReserve=(2255441390700000000000+(-43485961590253134056375*d)+(-25278996358942391248236*(d^3))+(80231004910864703743140*(d^2)))/(377475000000000000000000+(-422772000000000000000000*d)+(108712800000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_bootstrap_lo_5 {d : ℝ}
    (hd0 : (649/1000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A2 (17/500:ℝ) d 4 := by
  have hlo : 0 ≤ d-(649/1000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (7648546838396477100000000000+(-142262053519529312051225750375*d)+(-81998723702036688281936856108*(d^3))+(260677863168462768020548440420*(d^2))) := by
    have he : (7648546838396477100000000000+(-142262053519529312051225750375*d)+(-81998723702036688281936856108*(d^3))+(260677863168462768020548440420*(d^2)))=(2703124818749650645242496021494255508/1331:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^3+(9126698231926729585307072613599518160/1331:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^2+(10156246195727099512534866865887174400/1331:ℝ)*(d-(649/1000:ℝ))^2*((33/50:ℝ)-d)^1+(3732563642248773161638187015826432000/1331:ℝ)*(d-(649/1000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (1280075478675000000000000000000+(-1469922136116000000000000000000*d)+(383156777858400000000000000000*(d^2))) := by
    have he : (1280075478675000000000000000000+(-1469922136116000000000000000000*d)+(383156777858400000000000000000*(d^2)))=476829961273559040000000000000+(968369913899354400000000000000000/11:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^2+(964155189342912000000000000000000/11:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A2 (17/500:ℝ) d 4)-highReserve=(7648546838396477100000000000+(-142262053519529312051225750375*d)+(-81998723702036688281936856108*(d^3))+(260677863168462768020548440420*(d^2)))/(1280075478675000000000000000000+(-1469922136116000000000000000000*d)+(383156777858400000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_bootstrap_lo_6 {d : ℝ}
    (hd0 : (649/1000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A2 (17/500:ℝ) d 5 := by
  have hlo : 0 ≤ d-(649/1000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (2255441390700000000000+(-44014714470809467916375*d)+(-25532797741609431501036*(d^3))+(81077009519754837919140*(d^2))) := by
    have he : (2255441390700000000000+(-44014714470809467916375*d)+(-25532797741609431501036*(d^3))+(81077009519754837919140*(d^2)))=(859977663800114240325868250836/1331:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^3+(2898492156072898222503921152720/1331:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^2+(3220846443675791518279418924800/1331:ℝ)*(d-(649/1000:ℝ))^2*((33/50:ℝ)-d)^1+(1182297967249213453948038144000/1331:ℝ)*(d-(649/1000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (377475000000000000000000+(-422772000000000000000000*d)+(108712800000000000000000*(d^2))) := by
    have he : (377475000000000000000000+(-422772000000000000000000*d)+(108712800000000000000000*(d^2)))=145800775680000000000000+(280466944800000000000000000/11:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^2+(279271104000000000000000000/11:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A2 (17/500:ℝ) d 5)-highReserve=(2255441390700000000000+(-44014714470809467916375*d)+(-25532797741609431501036*(d^3))+(81077009519754837919140*(d^2)))/(377475000000000000000000+(-422772000000000000000000*d)+(108712800000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_bootstrap_lo_7 {d : ℝ}
    (hd0 : (649/1000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A2 (17/500:ℝ) d 6 := by
  have hlo : 0 ≤ d-(649/1000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (112772069535000000000000+(-89506253176907629113445*d)+(17758970150196051645378*(d^2))) := by
    have he : (112772069535000000000000+(-89506253176907629113445*d)+(17758970150196051645378*(d^2)))=(62162607209419675854459053978/121:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^2+(123594208209697867014062920040/121:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^1+(61433749835666364881852956800/121:ℝ)*(d-(649/1000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (18873750000000000000000000+(-7549500000000000000000000*d)) := by
    have he : (18873750000000000000000000+(-7549500000000000000000000*d))=13891080000000000000000000+7549500000000000000000000*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A2 (17/500:ℝ) d 6)-highReserve=(112772069535000000000000+(-89506253176907629113445*d)+(17758970150196051645378*(d^2)))/(18873750000000000000000000+(-7549500000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_bootstrap_hi_0 {d : ℝ}
    (hd0 : (649/1000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ highBase .A2 (1/25:ℝ) d+gamma d*supplied (1/25:ℝ) := by
  have hlo : 0 ≤ d-(649/1000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (-81835518374524800000+(-3071334075627692642255*d)+(5012429646072601024902*(d^2))) := by
    have he : (-81835518374524800000+(-3071334075627692642255*d)+(5012429646072601024902*(d^2)))=(36109045898528299466252302/121:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^2+(110000887451776577301250360/121:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^1+(74498345540423062559011200/121:ℝ)*(d-(649/1000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (15099000000000000000000+(-6039600000000000000000*d)) := by
    have he : (15099000000000000000000+(-6039600000000000000000*d))=11112864000000000000000+6039600000000000000000*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (highBase .A2 (1/25:ℝ) d+gamma d*supplied (1/25:ℝ))-highReserve=(-81835518374524800000+(-3071334075627692642255*d)+(5012429646072601024902*(d^2)))/(15099000000000000000000+(-6039600000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_bootstrap_hi_1 {d : ℝ}
    (hd0 : (649/1000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A2 (1/25:ℝ) d 0 := by
  have hlo : 0 ≤ d-(649/1000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (159748481553000000000+(-3167967675598702562255*d)+(4529261646217551424902*(d^2))) := by
    have he : (159748481553000000000+(-3167967675598702562255*d)+(4529261646217551424902*(d^2)))=(11466994737920914816652302/121:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^2+(52755142828950300693250360/121:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^1+(41836188750221709599011200/121:ℝ)*(d-(649/1000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (15099000000000000000000+(-6039600000000000000000*d)) := by
    have he : (15099000000000000000000+(-6039600000000000000000*d))=11112864000000000000000+6039600000000000000000*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A2 (1/25:ℝ) d 0)-highReserve=(159748481553000000000+(-3167967675598702562255*d)+(4529261646217551424902*(d^2)))/(15099000000000000000000+(-6039600000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_bootstrap_hi_2 {d : ℝ}
    (hd0 : (649/1000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A2 (1/25:ℝ) d 1 := by
  have hlo : 0 ≤ d-(649/1000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (8445470100064509135000000000+(-161006799385549451241538450225*d)+(-89134878386068585896336552036*(d^3))+(285888640503340659775856760180*(d^2))) := by
    have he : (8445470100064509135000000000+(-161006799385549451241538450225*d)+(-89134878386068585896336552036*(d^3))+(285888640503340659775856760180*(d^2)))=(2777325192786600660458065430391836/1331:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^3+(1080233094378028121816079947880412720/1331:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^2+(2165727720084261921538104128166924800/1331:ℝ)*(d-(649/1000:ℝ))^2*((33/50:ℝ)-d)^1+(1088153312375888543094654221766144000/1331:ℝ)*(d-(649/1000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (798243287205000000000000000000+(-698990629764000000000000000000*d)+(151877325952800000000000000000*(d^2))) := by
    have he : (798243287205000000000000000000+(-698990629764000000000000000000*d)+(151877325952800000000000000000*(d^2)))=403067234745799680000000000000+(500183210091784800000000000000000/11:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^2+(498512559506304000000000000000000/11:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A2 (1/25:ℝ) d 1)-highReserve=(8445470100064509135000000000+(-161006799385549451241538450225*d)+(-89134878386068585896336552036*(d^3))+(285888640503340659775856760180*(d^2)))/(798243287205000000000000000000+(-698990629764000000000000000000*d)+(151877325952800000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_bootstrap_hi_3 {d : ℝ}
    (hd0 : (649/1000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A2 (1/25:ℝ) d 2 := by
  have hlo : 0 ≤ d-(649/1000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (159748481553000000000+(-3237309593887591486255*d)+(4612471948164218133702*(d^2))) := by
    have he : (159748481553000000000+(-3237309593887591486255*d)+(4612471948164218133702*(d^2)))=(1512352158669967553921102/121:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^2+(33271173260465135272034360/121:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^1+(32316930207523038112291200/121:ℝ)*(d-(649/1000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (15099000000000000000000+(-6039600000000000000000*d)) := by
    have he : (15099000000000000000000+(-6039600000000000000000*d))=11112864000000000000000+6039600000000000000000*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A2 (1/25:ℝ) d 2)-highReserve=(159748481553000000000+(-3237309593887591486255*d)+(4612471948164218133702*(d^2)))/(15099000000000000000000+(-6039600000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_bootstrap_hi_4 {d : ℝ}
    (hd0 : (649/1000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A2 (1/25:ℝ) d 3 := by
  have hlo : 0 ≤ d-(649/1000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (3993712038825000000000+(-47018835393328134056375*d)+(-25248299636640791248236*(d^3))+(81289289322640703743140*(d^2))) := by
    have he : (3993712038825000000000+(-47018835393328134056375*d)+(-25248299636640791248236*(d^3))+(81289289322640703743140*(d^2)))=(815756543681601148185120958036/1331:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^3+(2739768815843517586799698496720/1331:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^2+(3036155833483773960109155884800/1331:ℝ)*(d-(649/1000:ℝ))^2*((33/50:ℝ)-d)^1+(1112109955835041152601426944000/1331:ℝ)*(d-(649/1000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (377475000000000000000000+(-422772000000000000000000*d)+(108712800000000000000000*(d^2))) := by
    have he : (377475000000000000000000+(-422772000000000000000000*d)+(108712800000000000000000*(d^2)))=145800775680000000000000+(280466944800000000000000000/11:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^2+(279271104000000000000000000/11:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A2 (1/25:ℝ) d 3)-highReserve=(3993712038825000000000+(-47018835393328134056375*d)+(-25248299636640791248236*(d^3))+(81289289322640703743140*(d^2)))/(377475000000000000000000+(-422772000000000000000000*d)+(108712800000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_bootstrap_hi_5 {d : ℝ}
    (hd0 : (649/1000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A2 (1/25:ℝ) d 4 := by
  have hlo : 0 ≤ d-(649/1000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (13543288561597515225000000000+(-156350362652207505401225750375*d)+(-82984664175761289517136856108*(d^3))+(267834879330133382348548440420*(d^2))) := by
    have he : (13543288561597515225000000000+(-156350362652207505401225750375*d)+(-82984664175761289517136856108*(d^3))+(267834879330133382348548440420*(d^2)))=(2199580134510209740261432616694255508/1331:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^3+(7549576444760661674648439717599518160/1331:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^2+(8513270398310465192863282225887174400/1331:ℝ)*(d-(649/1000:ℝ))^2*((33/50:ℝ)-d)^1+(3163163635471995320199927815826432000/1331:ℝ)*(d-(649/1000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (1280075478675000000000000000000+(-1469922136116000000000000000000*d)+(383156777858400000000000000000*(d^2))) := by
    have he : (1280075478675000000000000000000+(-1469922136116000000000000000000*d)+(383156777858400000000000000000*(d^2)))=476829961273559040000000000000+(968369913899354400000000000000000/11:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^2+(964155189342912000000000000000000/11:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A2 (1/25:ℝ) d 4)-highReserve=(13543288561597515225000000000+(-156350362652207505401225750375*d)+(-82984664175761289517136856108*(d^3))+(267834879330133382348548440420*(d^2)))/(1280075478675000000000000000000+(-1469922136116000000000000000000*d)+(383156777858400000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_bootstrap_hi_6 {d : ℝ}
    (hd0 : (649/1000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A2 (1/25:ℝ) d 5 := by
  have hlo : 0 ≤ d-(649/1000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (3993712038825000000000+(-48058964167661467916375*d)+(-25747561448320791501036*(d^3))+(82953495361574037919140*(d^2))) := by
    have he : (3993712038825000000000+(-48058964167661467916375*d)+(-25747561448320791501036*(d^3))+(82953495361574037919140*(d^2)))=(705200283196440127885228250836/1331:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^3+(2413480595740990881851121152720/1331:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^2+(2715331924072486288327418924800/1331:ℝ)*(d-(649/1000:ℝ))^2*((33/50:ℝ)-d)^1+(1007017341523647819388038144000/1331:ℝ)*(d-(649/1000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (377475000000000000000000+(-422772000000000000000000*d)+(108712800000000000000000*(d^2))) := by
    have he : (377475000000000000000000+(-422772000000000000000000*d)+(108712800000000000000000*(d^2)))=145800775680000000000000+(280466944800000000000000000/11:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^2+(279271104000000000000000000/11:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A2 (1/25:ℝ) d 5)-highReserve=(3993712038825000000000+(-48058964167661467916375*d)+(-25747561448320791501036*(d^3))+(82953495361574037919140*(d^2)))/(377475000000000000000000+(-422772000000000000000000*d)+(108712800000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_bootstrap_hi_7 {d : ℝ}
    (hd0 : (649/1000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A2 (1/25:ℝ) d 6 := by
  have hlo : 0 ≤ d-(649/1000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (199685601941250000000000+(-287316381955825846863445*d)+(82976856476763338745378*(d^2))) := by
    have he : (199685601941250000000000+(-287316381955825846863445*d)+(82976856476763338745378*(d^2)))=(48167204976788220428516153978/121:ℝ)*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^2+(94358673308837583492140920040/121:ℝ)*(d-(649/1000:ℝ))^1*((33/50:ℝ)-d)^1+(46201508531683051427612956800/121:ℝ)*(d-(649/1000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (18873750000000000000000000+(-7549500000000000000000000*d)) := by
    have he : (18873750000000000000000000+(-7549500000000000000000000*d))=13891080000000000000000000+7549500000000000000000000*(d-(649/1000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A2 (1/25:ℝ) d 6)-highReserve=(199685601941250000000000+(-287316381955825846863445*d)+(82976856476763338745378*(d^2)))/(18873750000000000000000000+(-7549500000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_saturated_lo_0 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ highBase .A2 (17/500:ℝ) d+gamma d*supplied (17/500:ℝ) := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (-115128744299524800000+(-3122676218910692642255*d)+(5149542741013801024902*(d^2))) := by
    have he : (-115128744299524800000+(-3122676218910692642255*d)+(5149542741013801024902*(d^2)))=(223485897350099275196704/27:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(1549387854468455963578100/27:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1+(1464939611125729316053750/27:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (15099000000000000000000+(-6039600000000000000000*d)) := by
    have he : (15099000000000000000000+(-6039600000000000000000*d))=10569300000000000000000+6039600000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (highBase .A2 (17/500:ℝ) d+gamma d*supplied (17/500:ℝ))-highReserve=(-115128744299524800000+(-3122676218910692642255*d)+(5149542741013801024902*(d^2)))/(15099000000000000000000+(-6039600000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_saturated_lo_1 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .A2 (17/500:ℝ) d 0 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (90217655628000000000+(-3204814778881702562255*d)+(4738849941158751424902*(d^2))) := by
    have he : (90217655628000000000+(-3204814778881702562255*d)+(4738849941158751424902*(d^2)))=(43647706594253810665568/9:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(392342127533292553192700/9:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1+(130448023469822501783750/3:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (15099000000000000000000+(-6039600000000000000000*d)) := by
    have he : (15099000000000000000000+(-6039600000000000000000*d))=10569300000000000000000+6039600000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .A2 (17/500:ℝ) d 0)-highReserve=(90217655628000000000+(-3204814778881702562255*d)+(4738849941158751424902*(d^2)))/(15099000000000000000000+(-6039600000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_saturated_lo_2 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .A2 (17/500:ℝ) d 1 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (2255441390700000000000+(-43485961590253134056375*d)+(-25278996358942391248236*(d^3))+(80231004910864703743140*(d^2))) := by
    have he : (2255441390700000000000+(-43485961590253134056375*d)+(-25278996358942391248236*(d^3))+(80231004910864703743140*(d^2)))=(137302460343899417666825216/81:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(705751105533921833014225600/81:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(1026755562944288305192445000/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(50695479894354617350437500/9:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (377475000000000000000000+(-422772000000000000000000*d)+(108712800000000000000000*(d^2))) := by
    have he : (377475000000000000000000+(-422772000000000000000000*d)+(108712800000000000000000*(d^2)))=121546950000000000000000+(8982898400000000000000000/3:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(8656760000000000000000000/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .A2 (17/500:ℝ) d 1)-highReserve=(2255441390700000000000+(-43485961590253134056375*d)+(-25278996358942391248236*(d^3))+(80231004910864703743140*(d^2)))/(377475000000000000000000+(-422772000000000000000000*d)+(108712800000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_saturated_lo_3 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .A2 (17/500:ℝ) d 2 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (10375030397220000000000+(-348001277287684664659325*d)+(-202037986238483186544708*(d^3))+(642635471647646104225500*(d^2))) := by
    have he : (10375030397220000000000+(-348001277287684664659325*d)+(-202037986238483186544708*(d^3))+(642635471647646104225500*(d^2)))=(94114294275696375059849216/27:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(3209571697188851022955748800/81:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(5790454978902339125753135000/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(2846861087655260089866812500/81:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (1736385000000000000000000+(-1509900000000000000000000*d)+(326138400000000000000000*(d^2))) := by
    have he : (1736385000000000000000000+(-1509900000000000000000000*d)+(326138400000000000000000*(d^2)))=787412850000000000000000+(35001495200000000000000000/3:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(34023080000000000000000000/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .A2 (17/500:ℝ) d 2)-highReserve=(10375030397220000000000+(-348001277287684664659325*d)+(-202037986238483186544708*(d^3))+(642635471647646104225500*(d^2)))/(1736385000000000000000000+(-1509900000000000000000000*d)+(326138400000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_saturated_lo_4 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .A2 (17/500:ℝ) d 3 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (16690266291180000000000+(-312108315100501834017175*d)+(-179959263222412365436476*(d^3))+(572071041488998623198060*(d^2))) := by
    have he : (16690266291180000000000+(-312108315100501834017175*d)+(-179959263222412365436476*(d^3))+(572071041488998623198060*(d^2)))=(906150628673991600023814656/81:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(4796998830881253494590217600/81:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(7069722306018292114779445000/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(3164297403490014818612687500/81:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (2793315000000000000000000+(-3200988000000000000000000*d)+(833464800000000000000000*(d^2))) := by
    have he : (2793315000000000000000000+(-3200988000000000000000000*d)+(833464800000000000000000*(d^2)))=861397950000000000000000+(67526754400000000000000000/3:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(65026360000000000000000000/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .A2 (17/500:ℝ) d 3)-highReserve=(16690266291180000000000+(-312108315100501834017175*d)+(-179959263222412365436476*(d^3))+(572071041488998623198060*(d^2)))/(2793315000000000000000000+(-3200988000000000000000000*d)+(833464800000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_saturated_hi_0 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ highBase .A2 (1/25:ℝ) d+gamma d*supplied (1/25:ℝ) := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (-81835518374524800000+(-3071334075627692642255*d)+(5012429646072601024902*(d^2))) := by
    have he : (-81835518374524800000+(-3071334075627692642255*d)+(5012429646072601024902*(d^2)))=(248327818468076875196704/27:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(1560177554092595963578100/27:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1+(1447185336068479316053750/27:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (15099000000000000000000+(-6039600000000000000000*d)) := by
    have he : (15099000000000000000000+(-6039600000000000000000*d))=10569300000000000000000+6039600000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (highBase .A2 (1/25:ℝ) d+gamma d*supplied (1/25:ℝ))-highReserve=(-81835518374524800000+(-3071334075627692642255*d)+(5012429646072601024902*(d^2)))/(15099000000000000000000+(-6039600000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_saturated_hi_1 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .A2 (1/25:ℝ) d 0 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (159748481553000000000+(-3167967675598702562255*d)+(4529261646217551424902*(d^2))) := by
    have he : (159748481553000000000+(-3167967675598702562255*d)+(4529261646217551424902*(d^2)))=(46484654166913010665568/9:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(374035078074672553192700/9:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1+40923753191524167261250*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (15099000000000000000000+(-6039600000000000000000*d)) := by
    have he : (15099000000000000000000+(-6039600000000000000000*d))=10569300000000000000000+6039600000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .A2 (1/25:ℝ) d 0)-highReserve=(159748481553000000000+(-3167967675598702562255*d)+(4529261646217551424902*(d^2)))/(15099000000000000000000+(-6039600000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_saturated_hi_2 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .A2 (1/25:ℝ) d 1 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (3993712038825000000000+(-47018835393328134056375*d)+(-25248299636640791248236*(d^3))+(81289289322640703743140*(d^2))) := by
    have he : (3993712038825000000000+(-47018835393328134056375*d)+(-25248299636640791248236*(d^3))+(81289289322640703743140*(d^2)))=(123567772870560128066825216/81:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(643588804085634473014225600/81:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(944642179997471305192445000/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(140858678837276352051312500/27:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (377475000000000000000000+(-422772000000000000000000*d)+(108712800000000000000000*(d^2))) := by
    have he : (377475000000000000000000+(-422772000000000000000000*d)+(108712800000000000000000*(d^2)))=121546950000000000000000+(8982898400000000000000000/3:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(8656760000000000000000000/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .A2 (1/25:ℝ) d 1)-highReserve=(3993712038825000000000+(-47018835393328134056375*d)+(-25248299636640791248236*(d^3))+(81289289322640703743140*(d^2)))/(377475000000000000000000+(-422772000000000000000000*d)+(108712800000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_saturated_hi_3 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .A2 (1/25:ℝ) d 2 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (18371075378595000000000+(-352985871528589664659325*d)+(-195549238898298386544708*(d^3))+(627128073796526104225500*(d^2))) := by
    have he : (18371075378595000000000+(-352985871528589664659325*d)+(-195549238898298386544708*(d^3))+(627128073796526104225500*(d^2)))=3234245719049930572587008*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(2978716114634417742955748800/81:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(5387457042239808125753135000/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(2654875342497672589866812500/81:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (1736385000000000000000000+(-1509900000000000000000000*d)+(326138400000000000000000*(d^2))) := by
    have he : (1736385000000000000000000+(-1509900000000000000000000*d)+(326138400000000000000000*(d^2)))=787412850000000000000000+(35001495200000000000000000/3:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(34023080000000000000000000/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .A2 (1/25:ℝ) d 2)-highReserve=(18371075378595000000000+(-352985871528589664659325*d)+(-195549238898298386544708*(d^3))+(627128073796526104225500*(d^2)))/(1736385000000000000000000+(-1509900000000000000000000*d)+(326138400000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A2_saturated_hi_4 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .A2 (1/25:ℝ) d 3 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (29553469087305000000000+(-342771677118796834017175*d)+(-182058347213646765436476*(d^3))+(587525983827022623198060*(d^2))) := by
    have he : (29553469087305000000000+(-342771677118796834017175*d)+(-182058347213646765436476*(d^3))+(587525983827022623198060*(d^2)))=(767714905935061526423814656/81:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(4251632451745978934590217600/81:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(6404465596396375114779445000/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(2905801324461152318612687500/81:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (2793315000000000000000000+(-3200988000000000000000000*d)+(833464800000000000000000*(d^2))) := by
    have he : (2793315000000000000000000+(-3200988000000000000000000*d)+(833464800000000000000000*(d^2)))=861397950000000000000000+(67526754400000000000000000/3:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(65026360000000000000000000/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .A2 (1/25:ℝ) d 3)-highReserve=(29553469087305000000000+(-342771677118796834017175*d)+(-182058347213646765436476*(d^3))+(587525983827022623198060*(d^2)))/(2793315000000000000000000+(-3200988000000000000000000*d)+(833464800000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

end Sil.Uneven.MainSource
