import Candidate.Uneven.AuxiliarySchedule
import Candidate.Uneven.SaturatedGeneralPayment
import Candidate.Target830.High.ActualAllocation
import Candidate.Target830.High.Frequency

/- Original module: Candidate.Uneven.AuxiliaryChannels. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
    Exact rational certificates for the auxiliary source's extended width interval. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Sil.Uneven.AuxiliarySource

theorem channel_lo_0 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (1/50:ℝ) d 0 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (-333342179274000000+(-31386564701372643895*d)+(46685626834944897558*(d^2))) := by
    have he : (-333342179274000000+(-31386564701372643895*d)+(46685626834944897558*(d^2)))=(812992457940765777712118518/2283121:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(10077208533257291828513800000/6849363:ℝ)*(d-70467/100000)^1*(3/4-d)^1+(7957997964510073183750000000/6849363:ℝ)*(d-70467/100000)^2*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (128221500000000000000+(-51288600000000000000*d)) := by
    have he : (128221500000000000000+(-51288600000000000000*d))=89755050000000000000+51288600000000000000*(d-70467/100000)^0*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (1/50:ℝ) d 0-highReserve=(-333342179274000000+(-31386564701372643895*d)+(46685626834944897558*(d^2)))/(128221500000000000000+(-51288600000000000000*d)) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_lo_1 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (1/50:ℝ) d 1 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (-122466854226500000+(-384020726312386735*d)+(819046084823594694*(d^2))) := by
    have he : (-122466854226500000+(-384020726312386735*d)+(819046084823594694*(d^2)))=(136306279232478109112439766/20548089:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(621786684911240977290200000/20548089:ℝ)*(d-70467/100000)^1*(3/4-d)^1+(502310237524819641250000000/20548089:ℝ)*(d-70467/100000)^2*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (2249500000000000000+(-899800000000000000*d)) := by
    have he : (2249500000000000000+(-899800000000000000*d))=1574650000000000000+899800000000000000*(d-70467/100000)^0*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (1/50:ℝ) d 1-highReserve=(-122466854226500000+(-384020726312386735*d)+(819046084823594694*(d^2)))/(2249500000000000000+(-899800000000000000*d)) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_lo_2 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (1/50:ℝ) d 2 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (3766714620000000+(-1660448873904960205*d)+(2349162319256384082*(d^2))) := by
    have he : (3766714620000000+(-1660448873904960205*d)+(2349162319256384082*(d^2)))=(219776633802846895079922/2283121:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(250681943674219317290200000/6849363:ℝ)*(d-70467/100000)^1*(3/4-d)^1+(266112879243319641250000000/6849363:ℝ)*(d-70467/100000)^2*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (6748500000000000000+(-2699400000000000000*d)) := by
    have he : (6748500000000000000+(-2699400000000000000*d))=4723950000000000000+2699400000000000000*(d-70467/100000)^0*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (1/50:ℝ) d 2-highReserve=(3766714620000000+(-1660448873904960205*d)+(2349162319256384082*(d^2)))/(6748500000000000000+(-2699400000000000000*d)) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_lo_3 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (1/50:ℝ) d 3 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (94167865500000000+(-21858903873039005125*d)+(-12592239397689313476*(d^3))+(40209093148966885740*(d^2))) := by
    have he : (94167865500000000+(-21858903873039005125*d)+(-12592239397689313476*(d^3))+(40209093148966885740*(d^2)))=(9293078339733053958177180218556/3449795831:ℝ)*(d-70467/100000)^0*(3/4-d)^3+(493443415398255465913512309700000/31048162479:ℝ)*(d-70467/100000)^1*(3/4-d)^2+(745281296606931990629382500000000/31048162479:ℝ)*(d-70467/100000)^2*(3/4-d)^1+(335084620371480087437500000000000/31048162479:ℝ)*(d-70467/100000)^3*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (168712500000000000000+(-188958000000000000000*d)+(48589200000000000000*(d^2))) := by
    have he : (168712500000000000000+(-188958000000000000000*d)+(48589200000000000000*(d^2)))=54325425000000000000+(3942558281200000000000000/1511:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(3869140000000000000000000/1511:ℝ)*(d-70467/100000)^1*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (1/50:ℝ) d 3-highReserve=(94167865500000000+(-21858903873039005125*d)+(-12592239397689313476*(d^3))+(40209093148966885740*(d^2)))/(168712500000000000000+(-188958000000000000000*d)+(48589200000000000000*(d^2))) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_lo_4 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (1/50:ℝ) d 4 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (433172181300000000+(-174809152226255423575*d)+(-98781721919135140428*(d^3))+(316808658103340020500*(d^2))) := by
    have he : (433172181300000000+(-174809152226255423575*d)+(-98781721919135140428*(d^3))+(316808658103340020500*(d^2)))=(6912497892958368551839567004/10349387493:ℝ)*(d-70467/100000)^0*(3/4-d)^3+(1881693334045481414302935993100000/31048162479:ℝ)*(d-70467/100000)^1*(3/4-d)^2+(3837286007537922070048947500000000/31048162479:ℝ)*(d-70467/100000)^2*(3/4-d)^1+(1952546420034018827312500000000000/31048162479:ℝ)*(d-70467/100000)^3*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (776077500000000000000+(-674850000000000000000*d)+(145767600000000000000*(d^2))) := by
    have he : (776077500000000000000+(-674850000000000000000*d)+(145767600000000000000*(d^2)))=351934275000000000000+(15426874843600000000000000/1511:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(15206620000000000000000000/1511:ℝ)*(d-70467/100000)^1*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (1/50:ℝ) d 4-highReserve=(433172181300000000+(-174809152226255423575*d)+(-98781721919135140428*(d^3))+(316808658103340020500*(d^2)))/(776077500000000000000+(-674850000000000000000*d)+(145767600000000000000*(d^2))) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_lo_5 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (1/50:ℝ) d 5 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (696842204700000000+(-153316145563467637925*d)+(-88262580294192203316*(d^3))+(281871413920179563460*(d^2))) := by
    have he : (696842204700000000+(-153316145563467637925*d)+(-88262580294192203316*(d^3))+(281871413920179563460*(d^2)))=(193504356979632978002468511426788/10349387493:ℝ)*(d-70467/100000)^0*(3/4-d)^3+(3440712548524045000636427863700000/31048162479:ℝ)*(d-70467/100000)^1*(3/4-d)^2+(5205148968714916005965132500000000/31048162479:ℝ)*(d-70467/100000)^2*(3/4-d)^1+(2342209100195980076187500000000000/31048162479:ℝ)*(d-70467/100000)^3*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (1248472500000000000000+(-1430682000000000000000*d)+(372517200000000000000*(d^2))) := by
    have he : (1248472500000000000000+(-1430682000000000000000*d)+(372517200000000000000*(d^2)))=385001925000000000000+(29626413489200000000000000/1511:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(29063540000000000000000000/1511:ℝ)*(d-70467/100000)^1*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (1/50:ℝ) d 5-highReserve=(696842204700000000+(-153316145563467637925*d)+(-88262580294192203316*(d^3))+(281871413920179563460*(d^2)))/(1248472500000000000000+(-1430682000000000000000*d)+(372517200000000000000*(d^2))) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_hi_0 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (7/250:ℝ) d 0 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (326245037748000000+(-30637437061153443895*d)+(44965959876898497558*(d^2))) := by
    have he : (326245037748000000+(-30637437061153443895*d)+(44965959876898497558*(d^2)))=(1183611897047542402897718518/2283121:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(12047913084763387268513800000/6849363:ℝ)*(d-70467/100000)^1*(3/4-d)^1+(8805065575461073183750000000/6849363:ℝ)*(d-70467/100000)^2*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (128221500000000000000+(-51288600000000000000*d)) := by
    have he : (128221500000000000000+(-51288600000000000000*d))=89755050000000000000+51288600000000000000*(d-70467/100000)^0*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (7/250:ℝ) d 0-highReserve=(326245037748000000+(-30637437061153443895*d)+(44965959876898497558*(d^2)))/(128221500000000000000+(-51288600000000000000*d)) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_hi_1 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (7/250:ℝ) d 1 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (-472628024941500000+(-912689376820360205*d)+(2366629467205184082*(d^2))) := by
    have he : (-472628024941500000+(-912689376820360205*d)+(2366629467205184082*(d^2)))=(198000759556705997299639766/6849363:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(254023638134380245763400000/2283121:ℝ)*(d-70467/100000)^1*(3/4-d)^1+(580280059153819641250000000/6849363:ℝ)*(d-70467/100000)^2*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (6748500000000000000+(-2699400000000000000*d)) := by
    have he : (6748500000000000000+(-2699400000000000000*d))=4723950000000000000+2699400000000000000*(d-70467/100000)^0*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (7/250:ℝ) d 1-highReserve=(-472628024941500000+(-912689376820360205*d)+(2366629467205184082*(d^2)))/(6748500000000000000+(-2699400000000000000*d)) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_hi_2 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (7/250:ℝ) d 2 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (47006252358000000+(-1624430871788160205*d)+(2215463131990784082*(d^2))) := by
    have he : (47006252358000000+(-1624430871788160205*d)+(2215463131990784082*(d^2)))=(2698332645973742957479922/2283121:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(242524187606119077290200000/6849363:ℝ)*(d-70467/100000)^1*(3/4-d)^1+(249603700872319641250000000/6849363:ℝ)*(d-70467/100000)^2*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (6748500000000000000+(-2699400000000000000*d)) := by
    have he : (6748500000000000000+(-2699400000000000000*d))=4723950000000000000+2699400000000000000*(d-70467/100000)^0*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (7/250:ℝ) d 2-highReserve=(47006252358000000+(-1624430871788160205*d)+(2215463131990784082*(d^2)))/(6748500000000000000+(-2699400000000000000*d)) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_hi_3 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (7/250:ℝ) d 3 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (1175156308950000000+(-23681316254163005125*d)+(-12467522313762913476*(d^3))+(40453307240648485740*(d^2))) := by
    have he : (1175156308950000000+(-23681316254163005125*d)+(-12467522313762913476*(d^3))+(40453307240648485740*(d^2)))=(7874406792208992867546341818556/3449795831:ℝ)*(d-70467/100000)^0*(3/4-d)^3+(435610466574953908044312309700000/31048162479:ℝ)*(d-70467/100000)^1*(3/4-d)^2+(668267387461511328629382500000000/31048162479:ℝ)*(d-70467/100000)^2*(3/4-d)^1+(303139488357930087437500000000000/31048162479:ℝ)*(d-70467/100000)^3*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (168712500000000000000+(-188958000000000000000*d)+(48589200000000000000*(d^2))) := by
    have he : (168712500000000000000+(-188958000000000000000*d)+(48589200000000000000*(d^2)))=54325425000000000000+(3942558281200000000000000/1511:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(3869140000000000000000000/1511:ℝ)*(d-70467/100000)^1*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (7/250:ℝ) d 3-highReserve=(1175156308950000000+(-23681316254163005125*d)+(-12467522313762913476*(d^3))+(40453307240648485740*(d^2)))/(168712500000000000000+(-188958000000000000000*d)+(48589200000000000000*(d^2))) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_hi_4 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (7/250:ℝ) d 4 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (5405719021170000000+(-176296267775435423575*d)+(-94491690093647140428*(d^3))+(305882817264912820500*(d^2))) := by
    have he : (5405719021170000000+(-176296267775435423575*d)+(-94491690093647140428*(d^3))+(305882817264912820500*(d^2)))=(53152210807629484410255567004/10349387493:ℝ)*(d-70467/100000)^0*(3/4-d)^3+(1723536570098474338047975993100000/31048162479:ℝ)*(d-70467/100000)^1*(3/4-d)^2+(3519284621096163148048947500000000/31048162479:ℝ)*(d-70467/100000)^2*(3/4-d)^1+(1792973714283168827312500000000000/31048162479:ℝ)*(d-70467/100000)^3*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (776077500000000000000+(-674850000000000000000*d)+(145767600000000000000*(d^2))) := by
    have he : (776077500000000000000+(-674850000000000000000*d)+(145767600000000000000*(d^2)))=351934275000000000000+(15426874843600000000000000/1511:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(15206620000000000000000000/1511:ℝ)*(d-70467/100000)^1*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (7/250:ℝ) d 4-highReserve=(5405719021170000000+(-176296267775435423575*d)+(-94491690093647140428*(d^3))+(305882817264912820500*(d^2)))/(776077500000000000000+(-674850000000000000000*d)+(145767600000000000000*(d^2))) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_hi_5 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (7/250:ℝ) d 5 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (8696156686230000000+(-169525977417783637925*d)+(-88714894746374603316*(d^3))+(288206242475317163460*(d^2))) := by
    have he : (8696156686230000000+(-169525977417783637925*d)+(-88714894746374603316*(d^3))+(288206242475317163460*(d^2)))=(145069225140153111938703234626788/10349387493:ℝ)*(d-70467/100000)^0*(3/4-d)^3+(2884585612392876857413787863700000/31048162479:ℝ)*(d-70467/100000)^1*(3/4-d)^2+(4532495302815940419965132500000000/31048162479:ℝ)*(d-70467/100000)^2*(3/4-d)^1+(2080362931377130076187500000000000/31048162479:ℝ)*(d-70467/100000)^3*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (1248472500000000000000+(-1430682000000000000000*d)+(372517200000000000000*(d^2))) := by
    have he : (1248472500000000000000+(-1430682000000000000000*d)+(372517200000000000000*(d^2)))=385001925000000000000+(29626413489200000000000000/1511:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(29063540000000000000000000/1511:ℝ)*(d-70467/100000)^1*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (7/250:ℝ) d 5-highReserve=(8696156686230000000+(-169525977417783637925*d)+(-88714894746374603316*(d^3))+(288206242475317163460*(d^2)))/(1248472500000000000000+(-1430682000000000000000*d)+(372517200000000000000*(d^2))) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_width_identity (b d : ℝ) (i : Fin 6) :
    ((7/250:ℝ)-1/50)*(channel b d i-highReserve)=
      ((7/250:ℝ)-b)*(channel (1/50) d i-highReserve)+
      (b-1/50)*(channel (7/250) d i-highReserve) := by
  fin_cases i <;> simp [channel,highBase,total,amp,gap,supplied,frequency] <;> ring

theorem channel_endpoints {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) (i : Fin 6) :
    highReserve ≤ channel (1/50) d i ∧ highReserve ≤ channel (7/250) d i := by
  fin_cases i
  · exact ⟨channel_lo_0 hd0 hd1,channel_hi_0 hd0 hd1⟩
  · exact ⟨channel_lo_1 hd0 hd1,channel_hi_1 hd0 hd1⟩
  · exact ⟨channel_lo_2 hd0 hd1,channel_hi_2 hd0 hd1⟩
  · exact ⟨channel_lo_3 hd0 hd1,channel_hi_3 hd0 hd1⟩
  · exact ⟨channel_lo_4 hd0 hd1,channel_hi_4 hd0 hd1⟩
  · exact ⟨channel_lo_5 hd0 hd1,channel_hi_5 hd0 hd1⟩

theorem all_channels {b d : ℝ} (hb : b∈Set.Icc widthLo widthHi)
    (hd0 : q ≤ d) (hd1 : d ≤ 3/4) (i : Fin 6) : highReserve ≤ channel b d i := by
  have hs := channel_endpoints hd0 hd1 i
  have hlo : 0 ≤ b-1/50 := by norm_num [widthLo] at hb;linarith [hb.1]
  have hhi : 0 ≤ (7/250:ℝ)-b := by norm_num [widthHi] at hb;linarith [hb.2]
  have hl := mul_nonneg hhi (sub_nonneg.mpr hs.1)
  have hh := mul_nonneg hlo (sub_nonneg.mpr hs.2)
  have he := channel_width_identity b d i
  nlinarith only [hl,hh,he]

end Sil.Uneven.AuxiliarySource
end

/- Original module: Candidate.Uneven.AuxiliaryPayment. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/

set_option autoImplicit false
noncomputable section
namespace Sil.Uneven.AuxiliarySource

def gamma (d : ℝ) : ℝ := d-max (3/19) (4*Saturated.rho d-5/4)

theorem gamma_bounds {d : ℝ} (hd : q ≤ d) (hu : d ≤ 3/4) :
    0 ≤ gamma d ∧ gamma d ≤ d ∧ 0 ≤ 5-6*Saturated.rho d := by
  have hlo : 70467/100000 ≤ d := hd
  have hden : 0 < 3*(5-2*d) := by linarith
  have hp : 27/50 ≤ 10*d/(3*(5-2*d)) := by
    apply (le_div_iff₀ hden).mpr
    linarith
  have hr : Saturated.rho d ≤ 23/50 := by unfold Saturated.rho;linarith only [hp]
  have hm : max (3/19:ℝ) (4*Saturated.rho d-5/4) ≤ d := max_le (by linarith) (by linarith)
  have hm0 : 0 ≤ max (3/19:ℝ) (4*Saturated.rho d-5/4) :=
    (by norm_num : (0:ℝ) ≤ 3/19).trans (le_max_left _ _)
  unfold gamma
  exact ⟨by linarith only [hm],by linarith only [hm0],by linarith only [hr]⟩

theorem channel_reserves {b d : ℝ} (hb : b∈Set.Icc widthLo widthHi)
    (hd : q ≤ d) (hu : d ≤ 3/4) :
    highReserve ≤ highBase b d+gamma d*supplied b ∧
    ∀i : Fin 4,highReserve ≤ highBase b d+Saturated.slope d i*supplied b+
      Saturated.offset d i*frequency b := by
  have h (i : Fin 6) := all_channels hb hd hu i
  constructor
  · by_cases hc : (3/19:ℝ) ≤ 4*Saturated.rho d-5/4
    · have hh := h 1
      change highReserve ≤ highBase b d+(d-4*Saturated.rho d+5/4)*supplied b at hh
      unfold gamma
      rw [max_eq_right hc]
      convert hh using 1 <;> ring
    · simpa [gamma,channel,max_eq_left (le_of_not_ge hc)] using h 0
  · intro i
    fin_cases i
    · simpa [channel] using h 2
    · simpa [channel] using h 3
    · simpa [channel] using h 4
    · simpa [channel] using h 5

theorem retained_payment {b d c c2 live freq error high : ℝ}
    (hb : b∈Set.Icc widthLo widthHi) (hd : q ≤ d) (hu : d ≤ 3/4)
    (hc : 0 ≤ c) (hc2 : 0 ≤ c2) (hlive : 0 ≤ live) (hfreq : 0 ≤ freq)
    (hsupply : supplied b ≤ c+c2+live) (hfrequency : frequency b ≤ 2*(c+c2)+freq)
    (hhigh : high ≤ error-highBase b d-gamma d*c-d*c2) :
    high-Saturated.physicalGain d live freq ≤ error-highReserve := by
  have hg := gamma_bounds hd hu
  have hs := source_guards hb
  have hr := channel_reserves hb hd hu
  apply Saturated.retained_high_payment_general (by norm_num [q] at hd;linarith) hu hg.1 hg.2.1
    hc hc2 hs.2.2.2.2.2.1.le hs.2.2.2.2.2.2.2.1.le hlive hfreq hsupply hfrequency hr.1 hr.2 hhigh

end Sil.Uneven.AuxiliarySource
end

/- Original module: Candidate.Uneven.AuxiliaryPointwise. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace OAI.SevenEighths.TargetHigh830
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic LocalMoment
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry Cycle63InitialMass
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentFirstSourceReduction Cycle63FinalCapacity
open Target830
local notation "O" => HeckeFamily.O

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

theorem actual_geometry_auxiliary_retained_payment
    (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin))
    (d2 : SecondInputDatum alpha) (reflected second : Bool)
    (U : Finset (CommonIndex d2.C d2.D))
    (A a reserve err errv b delta live : ℝ) (hZ : 1<Z)
    (hb : b∈Set.Icc Sil.Uneven.AuxiliarySource.widthLo Sil.Uneven.AuxiliarySource.widthHi)
    (hd : Sil.Uneven.AuxiliarySource.q ≤ delta) (hu : delta ≤ 3/4)
    (hA : A ≤ Sil.Uneven.AuxiliarySource.total b) (ha : a ≤ Sil.Uneven.AuxiliarySource.amp b)
    (homega : frequencyLoss Z 32 xi+reserve ≤ Sil.Uneven.AuxiliarySource.frequencyAllowance)
    (herr : 0 ≤ err) (hlive : 0 ≤ live) :
    let l:=geometryFirstLabel s R seed K Z xi hK bin j
    let side:=balancedGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val)
    let x:=childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U Z 1 A a xi reserve err) errv
    let c:=labelC reflected l Z
    let b2:=Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)
    let target:=(1-unmarkedDensity delta)*(frequencyLoss Z 32 xi+reserve)+unmarkedDensity delta*err+errv
    c+b2 ≤ Sil.Uneven.AuxiliarySource.supplied b → Sil.Uneven.AuxiliarySource.supplied b ≤ c+b2+live →
    retainedHighExponent delta (fun freq=>Sil.Uneven.Saturated.physicalGain delta live freq) x
      ≤ side+target-Sil.Uneven.AuxiliarySource.highReserve := by
  intro l side x c b2 target hsmall hsupply
  let xc:=compensatedHighCoordinates x side
  have hdelta : 31/50 ≤ delta := by norm_num [Sil.Uneven.AuxiliarySource.q] at hd;linarith
  have hcone:=actual_geometry_balanced_common_payment s R seed K Z xi hK bin j d2
    reflected second U 1 A a reserve err errv delta hZ hdelta hu
  have hf:=actual_geometry_balanced_moving_frequency s R seed K Z xi hK bin j d2 reflected second U
    1 A a reserve err errv (Sil.Uneven.AuxiliarySource.amp b) Sil.Uneven.AuxiliarySource.frequencyAllowance 1 hZ
    (by simpa using ha) (by simpa using homega) herr (by norm_num) (by norm_num)
  simp only [mul_one,one_mul] at hf
  change 0 ≤ c ∧ 0 ≤ b2 ∧ xc 3=A-(c+b2) ∧ Sil.Uneven.AuxiliarySource.frequency b-2*(c+b2) ≤ xc 2 at hf
  have hg:=Sil.Uneven.AuxiliarySource.gamma_bounds hd hu
  have hAA:=mul_le_mul_of_nonneg_left hA (show 0 ≤ delta by linarith)
  have haa:=mul_le_mul_of_nonneg_right ha hg.2.2
  have hsource : highExponentValue delta xc ≤ target-Sil.Uneven.AuxiliarySource.highBase b delta-Sil.Uneven.AuxiliarySource.gamma delta*c-delta*b2 := by
    change highExponentValue delta xc ≤ target-
      (1*(1-unmarkedDensity delta)-delta*A-a*(5-6*unmarkedDensity delta))-
        Sil.Uneven.AuxiliarySource.gamma delta*c-delta*b2 at hcone
    change a*(5-6*unmarkedDensity delta) ≤ Sil.Uneven.AuxiliarySource.amp b*(5-6*unmarkedDensity delta) at haa
    change highExponentValue delta xc ≤ target-
      (1-unmarkedDensity delta-delta*Sil.Uneven.AuxiliarySource.total b-Sil.Uneven.AuxiliarySource.amp b*(5-6*unmarkedDensity delta))-
        Sil.Uneven.AuxiliarySource.gamma delta*c-delta*b2
    linarith only [hcone,hAA,haa]
  have hguards:=Sil.Uneven.AuxiliarySource.source_guards hb
  have hF : 2*Sil.Uneven.AuxiliarySource.supplied b ≤ Sil.Uneven.AuxiliarySource.frequency b := hguards.2.2.2.2.2.2.2.1.le
  have hx2 : 0 ≤ xc 2 := by linarith only [hf.2.2.2,hF,hsmall]
  have hfrequency : Sil.Uneven.AuxiliarySource.frequency b ≤ 2*(c+b2)+xc 2 := by linarith only [hf.2.2.2]
  have hp:=Sil.Uneven.AuxiliarySource.retained_payment hb hd hu hf.1 hf.2.1 hlive hx2 hsupply hfrequency hsource
  have hid:=compensated_high_exponent delta side x
  have hx : xc 2=x 2 := by simp [xc,compensatedHighCoordinates,childHighCoordinates]
  unfold retainedHighExponent
  rw [hx] at hp
  change highExponentValue delta (compensatedHighCoordinates x side)=_ at hid
  linarith only [hp,hid]

theorem actual_geometry_auxiliary_unmarked_payment
    (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin))
    (d2 : SecondInputDatum alpha) (reflected second : Bool)
    (U : Finset (CommonIndex d2.C d2.D))
    (A a reserve err errv b delta : ℝ) (hZ : 1<Z)
    (hb : b∈Set.Icc Sil.Uneven.AuxiliarySource.widthLo Sil.Uneven.AuxiliarySource.widthHi) (hd : Sil.Uneven.AuxiliarySource.q ≤ delta) (hu : delta ≤ 3/4)
    (hA : A ≤ Sil.Uneven.AuxiliarySource.total b) (ha : a ≤ Sil.Uneven.AuxiliarySource.amp b) :
    let l:=geometryFirstLabel s R seed K Z xi hK bin j
    let side:=balancedGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val)
    let x:=childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U Z 1 A a xi reserve err) errv
    let c:=labelC reflected l Z
    let b2:=Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)
    let target:=(1-unmarkedDensity delta)*(frequencyLoss Z 32 xi+reserve)+unmarkedDensity delta*err+errv
    (Sil.Uneven.AuxiliarySource.supplied b ≤ c+b2) →
    highExponentValue delta x ≤ side+target-Sil.Uneven.AuxiliarySource.highReserve := by
  intro l side x c b2 target hbranch
  let xc:=compensatedHighCoordinates x side
  have hdelta : 31/50 ≤ delta := by norm_num [Sil.Uneven.AuxiliarySource.q] at hd;linarith
  have hcone:=actual_geometry_balanced_common_payment s R seed K Z xi hK bin j d2
    reflected second U 1 A a reserve err errv delta hZ hdelta hu
  have hC := (geometryFirstSource s R seed K Z xi hK bin j.1).hC
  have hD := (geometryFirstSource s R seed K Z xi hK bin j.1).hD
  have hc : 0 ≤ c := by
    apply Real.logb_nonneg hZ
    cases reflected
    · exact norm_ge_one l.1.1 hC.1
    · exact norm_ge_one l.1.2 hD.1
  have hb2 : 0 ≤ b2 := by
    apply Real.logb_nonneg hZ
    cases second
    · exact norm_ge_one d2.C d2.hC.1
    · exact norm_ge_one d2.D d2.hD.1
  have hg:=Sil.Uneven.AuxiliarySource.gamma_bounds hd hu
  have hr:=Target830.Source.Valuation.rho_extended_range
    (show (405/662:ℝ) ≤ delta by linarith) hu
  have hcoeff : 0 ≤ 5-6*unmarkedDensity delta := by
    change 0 ≤ 5-6*rho delta
    linarith [hr.2]
  have hAA:=mul_le_mul_of_nonneg_left hA (show 0 ≤ delta by linarith)
  have haa:=mul_le_mul_of_nonneg_left ha hcoeff
  have hbb:=mul_le_mul_of_nonneg_right hg.2.1 hb2
  have hsource : highExponentValue delta xc ≤ target-Sil.Uneven.AuxiliarySource.highBase b delta-Sil.Uneven.AuxiliarySource.gamma delta*(c+b2) := by
    change highExponentValue delta xc ≤ target-
      (1*(1-rho delta)-delta*A-a*(5-6*rho delta))-Sil.Uneven.AuxiliarySource.gamma delta*c-delta*b2 at hcone
    change highExponentValue delta xc ≤ target-
      (1-rho delta-delta*Sil.Uneven.AuxiliarySource.total b-Sil.Uneven.AuxiliarySource.amp b*(5-6*rho delta))-Sil.Uneven.AuxiliarySource.gamma delta*(c+b2)
    have haa2 : a*(5-6*rho delta) ≤ Sil.Uneven.AuxiliarySource.amp b*(5-6*rho delta) := by
      simpa only [←Target830.Source.Valuation.rho_eq_local,mul_comm] using haa
    linarith only [hcone,hAA,haa2,hbb]
  have hreserve : Sil.Uneven.AuxiliarySource.highReserve ≤ Sil.Uneven.AuxiliarySource.highBase b delta+Sil.Uneven.AuxiliarySource.gamma delta*(c+b2) := by
    have hh:=(Sil.Uneven.AuxiliarySource.channel_reserves hb hd hu).1
    have hm:=mul_le_mul_of_nonneg_left hbranch hg.1
    linarith only [hh,hm]
  have hid:=compensated_high_exponent delta side x
  change highExponentValue delta xc=highExponentValue delta x-side at hid
  linarith only [hsource,hreserve,hid]

end OAI.SevenEighths.TargetHigh830
end
