import Candidate.Target830.High.ChannelDefs

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace OAI.SevenEighths.TargetHigh830
open Target830

theorem channel_C_lo_0 (delta : ℝ) (hL : (6419/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .C (17/500:ℝ) delta 0 := by
  have hl : 0≤delta-(6419/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (31983137063716431694566213521/698687977312500000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (888708300113749832638395679/4192127863875000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (1209459981626321308086047/4192127863875000000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (255467789903045034341/2096063931937500:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .C (17/500:ℝ) delta 0-highFee)=
      (31983137063716431694566213521/698687977312500000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (888708300113749832638395679/4192127863875000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (1209459981626321308086047/4192127863875000000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (255467789903045034341/2096063931937500:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_C_lo_1 (delta : ℝ) (hL : (6419/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .C (17/500:ℝ) delta 1 := by
  have hl : 0≤delta-(6419/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (45391982853617992887126553/12257683812500000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (28796406006522868212547141/220638308625000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (54975182094077221478213/220638308625000000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (13452786308176054439/110319154312500:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .C (17/500:ℝ) delta 1-highFee)=
      (45391982853617992887126553/12257683812500000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (28796406006522868212547141/220638308625000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (54975182094077221478213/220638308625000000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (13452786308176054439/110319154312500:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_C_lo_2 (delta : ℝ) (hL : (6419/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .C (17/500:ℝ) delta 2 := by
  have hl : 0≤delta-(6419/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (154527835654795071221379659/36773051437500000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (17084844845836501452547141/220638308625000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (31847771966695441478213/220638308625000000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (7803518302036054439/110319154312500:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .C (17/500:ℝ) delta 2-highFee)=
      (154527835654795071221379659/36773051437500000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (17084844845836501452547141/220638308625000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (31847771966695441478213/220638308625000000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (7803518302036054439/110319154312500:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_C_lo_3 (delta : ℝ) (hL : (6419/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .C (17/500:ℝ) delta 3 := by
  have hl : 0≤delta-(6419/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (250852506670062502443043709/612884190625000000000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (356722362177227005912531386529/5515957715625000000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (45425030006170302496298657/344747357226562500000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (5752552926355761742333/86186839306640625:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .C (17/500:ℝ) delta 3-highFee)=
      (250852506670062502443043709/612884190625000000000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (356722362177227005912531386529/5515957715625000000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (45425030006170302496298657/344747357226562500000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (5752552926355761742333/86186839306640625:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_C_lo_4 (delta : ℝ) (hL : (6419/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .C (17/500:ℝ) delta 4 := by
  have hl : 0≤delta-(6419/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (34420506231369665830083081530143/3677305143750000000000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (944207626633989264017032803761/11031915431250000000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (201832855740977037597466451/1378989428906250000000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (48215563318018731870863/689494714453125000:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .C (17/500:ℝ) delta 4-highFee)=
      (34420506231369665830083081530143/3677305143750000000000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (944207626633989264017032803761/11031915431250000000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (201832855740977037597466451/1378989428906250000000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (48215563318018731870863/689494714453125000:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_C_lo_5 (delta : ℝ) (hL : (6419/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .C (17/500:ℝ) delta 5 := by
  have hl : 0≤delta-(6419/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (18969227780930179082959773892397/3677305143750000000000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (803410108696618203214738526819/11031915431250000000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (184484400973811738343829829/1378989428906250000000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (45463997341139485565777/689494714453125000:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .C (17/500:ℝ) delta 5-highFee)=
      (18969227780930179082959773892397/3677305143750000000000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (803410108696618203214738526819/11031915431250000000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (184484400973811738343829829/1378989428906250000000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (45463997341139485565777/689494714453125000:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_C_lo_6 (delta : ℝ) (hL : (6419/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .C (17/500:ℝ) delta 6 := by
  have hl : 0≤delta-(6419/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (151653758174109445081885859/36773051437500000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (82313366999425279421261891/1103191543125000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (2411364977559974546134/17237367861328125:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (38047152208585058437/551595771562500:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .C (17/500:ℝ) delta 6-highFee)=
      (151653758174109445081885859/36773051437500000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (82313366999425279421261891/1103191543125000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (2411364977559974546134/17237367861328125:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (38047152208585058437/551595771562500:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem unmarked_C_lo (delta : ℝ) (hL : (7/10:ℝ)≤delta) (hU : delta≤(3/4:ℝ)) :
    highFee ≤ highBase .C (17/500:ℝ) delta := by
  have hl : 0≤delta-(7/10:ℝ) := by linarith
  have hu : 0≤(3/4:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (104396209498038763/5625000000000000:ℝ)*(delta-(7/10:ℝ))^0*((3/4:ℝ)-delta)^2+
      (31261866672403867/500000000000000:ℝ)*(delta-(7/10:ℝ))^1*((3/4:ℝ)-delta)^1+
      (82326448006012921/1800000000000000:ℝ)*(delta-(7/10:ℝ))^2*((3/4:ℝ)-delta)^0 := by positivity
  have hid : (5-2*delta)*(highBase .C (17/500:ℝ) delta-highFee)=
      (104396209498038763/5625000000000000:ℝ)*(delta-(7/10:ℝ))^0*((3/4:ℝ)-delta)^2+
      (31261866672403867/500000000000000:ℝ)*(delta-(7/10:ℝ))^1*((3/4:ℝ)-delta)^1+
      (82326448006012921/1800000000000000:ℝ)*(delta-(7/10:ℝ))^2*((3/4:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < 5-2*delta := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_C_hi_0 (delta : ℝ) (hL : (6419/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .C (1/25:ℝ) delta 0 := by
  have hl : 0≤delta-(6419/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (49271939420471525398014986147443/896416674891937500000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (1269365031936009658073017456157/5378500049351625000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (1661821738928296766568798301/5378500049351625000000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (342972918754078627259503/2689250024675812500:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .C (1/25:ℝ) delta 0-highFee)=
      (49271939420471525398014986147443/896416674891937500000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (1269365031936009658073017456157/5378500049351625000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (1661821738928296766568798301/5378500049351625000000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (342972918754078627259503/2689250024675812500:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_C_hi_1 (delta : ℝ) (hL : (6419/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .C (1/25:ℝ) delta 1 := by
  have hl : 0≤delta-(6419/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (85992626543937385468683967499/15726608331437500000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (39672909852605551642906181903/283078949965875000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (74361691911273524014147279/283078949965875000000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (18061942931204185645237/141539474982937500:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .C (1/25:ℝ) delta 1-highFee)=
      (85992626543937385468683967499/15726608331437500000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (39672909852605551642906181903/283078949965875000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (74361691911273524014147279/283078949965875000000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (18061942931204185645237/141539474982937500:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_C_hi_2 (delta : ℝ) (hL : (6419/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .C (1/25:ℝ) delta 2 := by
  have hl : 0≤delta-(6419/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (285678435382461338160531902497/47179824994312500000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (21995340717721483089826181903/283078949965875000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (39452905129712700274147279/283078949965875000000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (9534870889326565645237/141539474982937500:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .C (1/25:ℝ) delta 2-highFee)=
      (285678435382461338160531902497/47179824994312500000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (21995340717721483089826181903/283078949965875000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (39452905129712700274147279/283078949965875000000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (9534870889326565645237/141539474982937500:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_C_hi_3 (delta : ℝ) (hL : (6419/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .C (1/25:ℝ) delta 3 := by
  have hl : 0≤delta-(6419/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (161123957352549606980233117877/393165208285937500000000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (212044549028037296589543389098837/3538486874573437500000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (108226883322673084890749430509/884621718643359375000000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (27459789838311245951915867/442310859321679687500:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .C (1/25:ℝ) delta 3-highFee)=
      (161123957352549606980233117877/393165208285937500000000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (212044549028037296589543389098837/3538486874573437500000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (108226883322673084890749430509/884621718643359375000000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (27459789838311245951915867/442310859321679687500:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_C_hi_4 (delta : ℝ) (hL : (6419/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .C (1/25:ℝ) delta 4 := by
  have hl : 0≤delta-(6419/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (16800947875553307339700383357207679/2358991249715625000000000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (529879279668636387493599585377033/7076973749146875000000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (29131138854499158580596643307/221155429660839843750000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (10992310987112498066579/172373678613281250:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .C (1/25:ℝ) delta 4-highFee)=
      (16800947875553307339700383357207679/2358991249715625000000000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (529879279668636387493599585377033/7076973749146875000000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (29131138854499158580596643307/221155429660839843750000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (10992310987112498066579/172373678613281250:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_C_hi_5 (delta : ℝ) (hL : (6419/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .C (1/25:ℝ) delta 5 := by
  have hl : 0≤delta-(6419/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (2517992850174355729315669631064941/2358991249715625000000000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (404084859781673903427031815999707/7076973749146875000000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (50730555105158765428212878431/442310859321679687500000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (6467397075524099587347989/110577714830419921875:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .C (1/25:ℝ) delta 5-highFee)=
      (2517992850174355729315669631064941/2358991249715625000000000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (404084859781673903427031815999707/7076973749146875000000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (50730555105158765428212878431/442310859321679687500000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (6467397075524099587347989/110577714830419921875:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem channel_C_hi_6 (delta : ℝ) (hL : (6419/10000:ℝ)≤delta) (hU : delta≤(7/10:ℝ)) :
    highFee ≤ channel .C (1/25:ℝ) delta 6 := by
  have hl : 0≤delta-(6419/10000:ℝ) := by linarith
  have hu : 0≤(7/10:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (2942882901642098334022239697/47179824994312500000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (83275615468793761234558785631/1415394749829375000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (170739331306494450594811961/1415394749829375000000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (43480504691726765986637/707697374914687500:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by positivity
  have hid : ((5-2*delta)*(380-240*delta))*(channel .C (1/25:ℝ) delta 6-highFee)=
      (2942882901642098334022239697/47179824994312500000000000:ℝ)*(delta-(6419/10000:ℝ))^0*((7/10:ℝ)-delta)^3+
      (83275615468793761234558785631/1415394749829375000000000:ℝ)*(delta-(6419/10000:ℝ))^1*((7/10:ℝ)-delta)^2+
      (170739331306494450594811961/1415394749829375000000:ℝ)*(delta-(6419/10000:ℝ))^2*((7/10:ℝ)-delta)^1+
      (43480504691726765986637/707697374914687500:ℝ)*(delta-(6419/10000:ℝ))^3*((7/10:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < (5 - 2*delta)*(380 - 240*delta) := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem unmarked_C_hi (delta : ℝ) (hL : (7/10:ℝ)≤delta) (hU : delta≤(3/4:ℝ)) :
    highFee ≤ highBase .C (1/25:ℝ) delta := by
  have hl : 0≤delta-(7/10:ℝ) := by linarith
  have hu : 0≤(3/4:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (115240043725876332929/7216875000000000000:ℝ)*(delta-(7/10:ℝ))^0*((3/4:ℝ)-delta)^2+
      (35951281954632561361/641500000000000000:ℝ)*(delta-(7/10:ℝ))^1*((3/4:ℝ)-delta)^1+
      (96565640999158777643/2309400000000000000:ℝ)*(delta-(7/10:ℝ))^2*((3/4:ℝ)-delta)^0 := by positivity
  have hid : (5-2*delta)*(highBase .C (1/25:ℝ) delta-highFee)=
      (115240043725876332929/7216875000000000000:ℝ)*(delta-(7/10:ℝ))^0*((3/4:ℝ)-delta)^2+
      (35951281954632561361/641500000000000000:ℝ)*(delta-(7/10:ℝ))^1*((3/4:ℝ)-delta)^1+
      (96565640999158777643/2309400000000000000:ℝ)*(delta-(7/10:ℝ))^2*((3/4:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < 5-2*delta := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem slope_C_0 (delta : ℝ) (hL : (6419/10000:ℝ)≤delta) (hU : delta≤(3/4:ℝ)) :
    2*SourcePlane.rootCutoff .C*(6*rho delta-1) ≤ (delta-3/19) := by
  have hl : 0≤delta-(6419/10000:ℝ) := by linarith
  have hu : 0≤(3/4:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (3316630574/22202659:ℝ)*(delta-(6419/10000:ℝ))^0*((3/4:ℝ)-delta)^2+
      (381823468/1168561:ℝ)*(delta-(6419/10000:ℝ))^1*((3/4:ℝ)-delta)^1+
      (3893610000/22202659:ℝ)*(delta-(6419/10000:ℝ))^2*((3/4:ℝ)-delta)^0 := by positivity
  have hid : (5-2*delta)*((delta-3/19)-2*SourcePlane.rootCutoff .C*(6*rho delta-1))=
      (3316630574/22202659:ℝ)*(delta-(6419/10000:ℝ))^0*((3/4:ℝ)-delta)^2+
      (381823468/1168561:ℝ)*(delta-(6419/10000:ℝ))^1*((3/4:ℝ)-delta)^1+
      (3893610000/22202659:ℝ)*(delta-(6419/10000:ℝ))^2*((3/4:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < 5-2*delta := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

theorem slope_C_1 (delta : ℝ) (hL : (6419/10000:ℝ)≤delta) (hU : delta≤(3/4:ℝ)) :
    2*SourcePlane.rootCutoff .C*(6*rho delta-1) ≤ (delta-4*rho delta+5/4) := by
  have hl : 0≤delta-(6419/10000:ℝ) := by linarith
  have hu : 0≤(3/4:ℝ)-delta := by linarith
  have hden : 0<5-2*delta := by linarith
  have hcapden : 0<380-240*delta := by linarith
  have hn : 0≤
      (201444038/3505683:ℝ)*(delta-(6419/10000:ℝ))^0*((3/4:ℝ)-delta)^2+
      (1101525404/3505683:ℝ)*(delta-(6419/10000:ℝ))^1*((3/4:ℝ)-delta)^1+
      (297690000/1168561:ℝ)*(delta-(6419/10000:ℝ))^2*((3/4:ℝ)-delta)^0 := by positivity
  have hid : (5-2*delta)*((delta-4*rho delta+5/4)-2*SourcePlane.rootCutoff .C*(6*rho delta-1))=
      (201444038/3505683:ℝ)*(delta-(6419/10000:ℝ))^0*((3/4:ℝ)-delta)^2+
      (1101525404/3505683:ℝ)*(delta-(6419/10000:ℝ))^1*((3/4:ℝ)-delta)^1+
      (297690000/1168561:ℝ)*(delta-(6419/10000:ℝ))^2*((3/4:ℝ)-delta)^0 := by
    norm_num [channel,highBase,highFee,SourcePlane.total,SourcePlane.amp,SourcePlane.gap,
      SourcePlane.frequency,SourcePlane.supplied,SourcePlane.B,SourcePlane.lambda,SourcePlane.q,
      SourcePlane.rootCutoff,kappa0,lowReserve,sourceWidthMesh,sourceDiscard,frequencyAllowance,
      highReserve,highRawFee,rho,phi,capI,capP,zeta]
    field_simp [hden.ne',hcapden.ne', show (380:ℝ)-delta*240≠0 by nlinarith, show (5:ℝ)-delta*2≠0 by nlinarith]
    <;> ring
  have hpos : 0 < 5-2*delta := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hn)
  linarith

end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.channel_C_lo_3
#print axioms OAI.SevenEighths.TargetHigh830.unmarked_C_lo
#print axioms OAI.SevenEighths.TargetHigh830.slope_C_1
