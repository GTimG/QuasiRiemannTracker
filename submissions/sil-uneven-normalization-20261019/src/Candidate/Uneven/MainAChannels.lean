/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Exact source margins, retaining all stated width and frequency losses. -/
import Candidate.Uneven.MainParameters
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Sil.Uneven.MainSource

theorem A_bootstrap_lo_0 {d : ℝ}
    (hd0 : (64883/100000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ highBase .A (17/500:ℝ) d+gamma d*supplied (17/500:ℝ) := by
  have hlo : 0 ≤ d-(64883/100000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (-361045308950563800000000+(-9771529950765794862409355*d)+(16119013981940688152963742*(d^2))) := by
    have he : (-361045308950563800000000+(-9771529950765794862409355*d)+(16119013981940688152963742*(d^2)))=(846813655157143559774739308344238/1247689:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^2+(2938576279494783466922173282052000/1247689:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^1+(2111874140773753502408317152000000/1247689:ℝ)*(d-(64883/100000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (47262750000000000000000000+(-18905100000000000000000000*d)) := by
    have he : (47262750000000000000000000+(-18905100000000000000000000*d))=34785384000000000000000000+18905100000000000000000000*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (highBase .A (17/500:ℝ) d+gamma d*supplied (17/500:ℝ))-highReserve=(-361045308950563800000000+(-9771529950765794862409355*d)+(16119013981940688152963742*(d^2)))/(47262750000000000000000000+(-18905100000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_bootstrap_lo_1 {d : ℝ}
    (hd0 : (64883/100000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A (17/500:ℝ) d 0 := by
  have hlo : 0 ≤ d-(64883/100000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (281728090822575000000000+(-10028639310675050382409355*d)+(14833467182394410552963742*(d^2))) := by
    have he : (281728090822575000000000+(-10028639310675050382409355*d)+(14833467182394410552963742*(d^2)))=(194445333877246002660672908344238/1247689:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^2+(1418782284322381347760573282052000/1247689:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^1+(1242844504280469844808317152000000/1247689:ℝ)*(d-(64883/100000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (47262750000000000000000000+(-18905100000000000000000000*d)) := by
    have he : (47262750000000000000000000+(-18905100000000000000000000*d))=34785384000000000000000000+18905100000000000000000000*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A (17/500:ℝ) d 0)-highReserve=(281728090822575000000000+(-10028639310675050382409355*d)+(14833467182394410552963742*(d^2)))/(47262750000000000000000000+(-18905100000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_bootstrap_lo_2 {d : ℝ}
    (hd0 : (64883/100000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A (17/500:ℝ) d 1 := by
  have hlo : 0 ≤ d-(64883/100000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (14894202087303865184625000000000+(-496341919641971946593630056544725*d)+(-288167196083201561983993177047156*(d^3))+(916571685730698031167894965235780*(d^2))) := by
    have he : (14894202087303865184625000000000+(-496341919641971946593630056544725*d)+(-288167196083201561983993177047156*(d^3))+(916571685730698031167894965235780*(d^2)))=(20512456213914272430260415855357264282628/1393668613:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^3+(3676312909579377762657713128632501507062168000/1393668613:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^2+(7396939229457967768352879642354009547136000000/1393668613:ℝ)*(d-(64883/100000:ℝ))^2*((33/50:ℝ)-d)^1+(3720245222758326545414107108838106624000000000/1393668613:ℝ)*(d-(64883/100000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (2498653746761250000000000000000000+(-2187973997409000000000000000000000*d)+(475404999481800000000000000000000*(d^2))) := by
    have he : (2498653746761250000000000000000000+(-2187973997409000000000000000000000*d)+(475404999481800000000000000000000*(d^2)))=1261677326245582080000000000000000+(156574967193723570600000000000000000000/1117:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^2+(156043939809302400000000000000000000000/1117:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A (17/500:ℝ) d 1)-highReserve=(14894202087303865184625000000000+(-496341919641971946593630056544725*d)+(-288167196083201561983993177047156*(d^3))+(916571685730698031167894965235780*(d^2)))/(2498653746761250000000000000000000+(-2187973997409000000000000000000000*d)+(475404999481800000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_bootstrap_lo_3 {d : ℝ}
    (hd0 : (64883/100000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A (17/500:ℝ) d 2 := by
  have hlo : 0 ≤ d-(64883/100000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (281728090822575000000000+(-10138941594159360701409355*d)+(14965829922575582935763742*(d^2))) := by
    have he : (281728090822575000000000+(-10138941594159360701409355*d)+(14965829922575582935763742*(d^2)))=(35992179846843385349333057544238/1247689:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^2+(1108741007989783617736910082052000/1247689:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^1+(1091421529513208638885117152000000/1247689:ℝ)*(d-(64883/100000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (47262750000000000000000000+(-18905100000000000000000000*d)) := by
    have he : (47262750000000000000000000+(-18905100000000000000000000*d))=34785384000000000000000000+18905100000000000000000000*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A (17/500:ℝ) d 2)-highReserve=(281728090822575000000000+(-10138941594159360701409355*d)+(14965829922575582935763742*(d^2)))/(47262750000000000000000000+(-18905100000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_bootstrap_lo_4 {d : ℝ}
    (hd0 : (64883/100000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A (17/500:ℝ) d 3 := by
  have hlo : 0 ≤ d-(64883/100000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (7043202270564375000000000+(-136017823987968592060233875*d)+(-79108106932795873553347356*(d^3))+(251050484563634752707461940*(d^2))) := by
    have he : (7043202270564375000000000+(-136017823987968592060233875*d)+(-79108106932795873553347356*(d^3))+(251050484563634752707461940*(d^2)))=(2870123574112814194827762255289609505228/1393668613:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^3+(9614011616460657471296964809008801768000/1393668613:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^2+(10629763496506829418301421874134336000000/1393668613:ℝ)*(d-(64883/100000:ℝ))^2*((33/50:ℝ)-d)^1+(3885765203673320056522912103424000000000/1393668613:ℝ)*(d-(64883/100000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (1181568750000000000000000000+(-1323357000000000000000000000*d)+(340291800000000000000000000*(d^2))) := by
    have he : (1181568750000000000000000000+(-1323357000000000000000000000*d)+(340291800000000000000000000*(d^2)))=456384238080000000000000000+(87797288340600000000000000000000/1117:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^2+(87417182400000000000000000000000/1117:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A (17/500:ℝ) d 3)-highReserve=(7043202270564375000000000+(-136017823987968592060233875*d)+(-79108106932795873553347356*(d^3))+(251050484563634752707461940*(d^2)))/(1181568750000000000000000000+(-1323357000000000000000000000*d)+(340291800000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_bootstrap_lo_5 {d : ℝ}
    (hd0 : (64883/100000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A (17/500:ℝ) d 4 := by
  have hlo : 0 ≤ d-(64883/100000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (23884576509431191974375000000000+(-444957545728694201183920160907875*d)+(-256598089049117089745446827141468*(d^3))+(815656708671830992566881132216820*(d^2))) := by
    have he : (23884576509431191974375000000000+(-444957545728694201183920160907875*d)+(-256598089049117089745446827141468*(d^3))+(815656708671830992566881132216820*(d^2)))=(8469828032282448844567250067243556087412847884/1393668613:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^3+(28642297278917464092675782458619421444358504000/1393668613:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^2+(31914561276015511503276006503364320729408000000/1393668613:ℝ)*(d-(64883/100000:ℝ))^2*((33/50:ℝ)-d)^1+(11741734416677632721664133978585807872000000000/1393668613:ℝ)*(d-(64883/100000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (4006880411268750000000000000000000+(-4601136660621000000000000000000000*d)+(1199353798445400000000000000000000*(d^2))) := by
    have he : (4006880411268750000000000000000000+(-4601136660621000000000000000000000*d)+(1199353798445400000000000000000000*(d^2)))=1492568729861706240000000000000000+(303138642860170711800000000000000000000/1117:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^2+(301798964667307200000000000000000000000/1117:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A (17/500:ℝ) d 4)-highReserve=(23884576509431191974375000000000+(-444957545728694201183920160907875*d)+(-256598089049117089745446827141468*(d^3))+(815656708671830992566881132216820*(d^2)))/(4006880411268750000000000000000000+(-4601136660621000000000000000000000*d)+(1199353798445400000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_bootstrap_lo_6 {d : ℝ}
    (hd0 : (64883/100000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A (17/500:ℝ) d 5 := by
  have hlo : 0 ≤ d-(64883/100000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (7043202270564375000000000+(-137672358240233246845233875*d)+(-79902283373882907850147356*(d^3))+(253697739367258200363461940*(d^2))) := by
    have he : (7043202270564375000000000+(-137672358240233246845233875*d)+(-79902283373882907850147356*(d^3))+(253697739367258200363461940*(d^2)))=(2694129339024937946974822460326347905228/1393668613:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^3+(9094715868705924017852502850159201768000/1393668613:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^2+(10119292126515694968413987614934336000000/1393668613:ℝ)*(d-(64883/100000:ℝ))^2*((33/50:ℝ)-d)^1+(3718594239530263685183699303424000000000/1393668613:ℝ)*(d-(64883/100000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (1181568750000000000000000000+(-1323357000000000000000000000*d)+(340291800000000000000000000*(d^2))) := by
    have he : (1181568750000000000000000000+(-1323357000000000000000000000*d)+(340291800000000000000000000*(d^2)))=456384238080000000000000000+(87797288340600000000000000000000/1117:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^2+(87417182400000000000000000000000/1117:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A (17/500:ℝ) d 5)-highReserve=(7043202270564375000000000+(-137672358240233246845233875*d)+(-79902283373882907850147356*(d^3))+(253697739367258200363461940*(d^2)))/(1181568750000000000000000000+(-1323357000000000000000000000*d)+(340291800000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_bootstrap_lo_7 {d : ℝ}
    (hd0 : (64883/100000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A (17/500:ℝ) d 6 := by
  have hlo : 0 ≤ d-(64883/100000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (704320227056437500000000+(-550218833432800067240915*d)+(107396297075598526896366*(d^2))) := by
    have he : (704320227056437500000000+(-550218833432800067240915*d)+(107396297075598526896366*(d^2)))=(3925334741216132914132058512994174/1247689:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^2+(7804776984006832697052165008996000/1247689:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^1+(3879576239969201739370531296000000/1247689:ℝ)*(d-(64883/100000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (118156875000000000000000000+(-47262750000000000000000000*d)) := by
    have he : (118156875000000000000000000+(-47262750000000000000000000*d))=86963460000000000000000000+47262750000000000000000000*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A (17/500:ℝ) d 6)-highReserve=(704320227056437500000000+(-550218833432800067240915*d)+(107396297075598526896366*(d^2)))/(118156875000000000000000000+(-47262750000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_bootstrap_hi_0 {d : ℝ}
    (hd0 : (64883/100000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ highBase .A (1/25:ℝ) d+gamma d*supplied (1/25:ℝ) := by
  have hlo : 0 ≤ d-(64883/100000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (-6264988881982425000000+(-234415502107147149083155*d)+(382682173906401047633262*(d^2))) := by
    have he : (-6264988881982425000000+(-234415502107147149083155*d)+(382682173906401047633262*(d^2)))=(27408836284079573643736500203518/1247689:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^2+(84102714754487999568682275172000/1247689:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^1+(57171346809287529541666272000000/1247689:ℝ)*(d-(64883/100000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (1152750000000000000000000+(-461100000000000000000000*d)) := by
    have he : (1152750000000000000000000+(-461100000000000000000000*d))=848424000000000000000000+461100000000000000000000*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (highBase .A (1/25:ℝ) d+gamma d*supplied (1/25:ℝ))-highReserve=(-6264988881982425000000+(-234415502107147149083155*d)+(382682173906401047633262*(d^2)))/(1152750000000000000000000+(-461100000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_bootstrap_hi_1 {d : ℝ}
    (hd0 : (64883/100000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A (1/25:ℝ) d 0 := by
  have hlo : 0 ≤ d-(64883/100000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (12179011112484375000000+(-241793102104933869083155*d)+(345794173917467447633262*(d^2))) := by
    have he : (12179011112484375000000+(-241793102104933869083155*d)+(345794173917467447633262*(d^2)))=(8689515729863369811686100203518/1247689:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^2+(40493130959570874711082275172000/1247689:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^1+(32235058816768415941666272000000/1247689:ℝ)*(d-(64883/100000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (1152750000000000000000000+(-461100000000000000000000*d)) := by
    have he : (1152750000000000000000000+(-461100000000000000000000*d))=848424000000000000000000+461100000000000000000000*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A (1/25:ℝ) d 0)-highReserve=(12179011112484375000000+(-241793102104933869083155*d)+(345794173917467447633262*(d^2)))/(1152750000000000000000000+(-461100000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_bootstrap_hi_2 {d : ℝ}
    (hd0 : (64883/100000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A (1/25:ℝ) d 1 := by
  have hlo : 0 ≤ d-(64883/100000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (643871373291989636015625000000+(-12287999633946101137039284915725*d)+(-6804922422732888499057733586516*(d^3))+(21824486490680869360697547932580*(d^2))) := by
    have he : (643871373291989636015625000000+(-12287999633946101137039284915725*d)+(-6804922422732888499057733586516*(d^3))+(21824486490680869360697547932580*(d^2)))=(500330630914268657059766532072145470308/1393668613:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^3+(83090073774134898525678079445457700172248000/1393668613:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^2+(167249010632433514165851644986644135296000000/1393668613:ℝ)*(d-(64883/100000:ℝ))^2*((33/50:ℝ)-d)^1+(84149953382135067164446659864344064000000000/1393668613:ℝ)*(d-(64883/100000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (60942774311250000000000000000000+(-53365219449000000000000000000000*d)+(11595243889800000000000000000000*(d^2))) := by
    have he : (60942774311250000000000000000000+(-53365219449000000000000000000000*d)+(11595243889800000000000000000000*(d^2)))=30772617713306880000000000000000+(3818901638871306600000000000000000000/1117:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^2+(3805949751446400000000000000000000000/1117:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A (1/25:ℝ) d 1)-highReserve=(643871373291989636015625000000+(-12287999633946101137039284915725*d)+(-6804922422732888499057733586516*(d^3))+(21824486490680869360697547932580*(d^2)))/(60942774311250000000000000000000+(-53365219449000000000000000000000*d)+(11595243889800000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_bootstrap_hi_3 {d : ℝ}
    (hd0 : (64883/100000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A (1/25:ℝ) d 2 := by
  have hlo : 0 ≤ d-(64883/100000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (12179011112484375000000+(-247086126980848753083155*d)+(352145803768565308433262*(d^2))) := by
    have he : (12179011112484375000000+(-247086126980848753083155*d)+(352145803768565308433262*(d^2)))=(1085897205779123050334591403518/1247689:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^2+(25615323027133388755687075172000/1247689:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^1+(24968794267112463186466272000000/1247689:ℝ)*(d-(64883/100000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (1152750000000000000000000+(-461100000000000000000000*d)) := by
    have he : (1152750000000000000000000+(-461100000000000000000000*d))=848424000000000000000000+461100000000000000000000*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A (1/25:ℝ) d 2)-highReserve=(12179011112484375000000+(-247086126980848753083155*d)+(352145803768565308433262*(d^2)))/(1152750000000000000000000+(-461100000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_bootstrap_hi_4 {d : ℝ}
    (hd0 : (64883/100000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A (1/25:ℝ) d 3 := by
  have hlo : 0 ≤ d-(64883/100000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (304475277812109375000000+(-3587330066844935477078875*d)+(-1927162783090703657398716*(d^3))+(6204122940008647834328340*(d^2))) := by
    have he : (304475277812109375000000+(-3587330066844935477078875*d)+(-1927162783090703657398716*(d^3))+(6204122940008647834328340*(d^2)))=(62327588253830577664842431322507548908/1393668613:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^3+(209653609096702646018343717517287848000/1393668613:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^2+(232630501543929021668186835954496000000/1393668613:ℝ)*(d-(64883/100000:ℝ))^2*((33/50:ℝ)-d)^1+(85301794874774018073866148864000000000/1393668613:ℝ)*(d-(64883/100000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (28818750000000000000000000+(-32277000000000000000000000*d)+(8299800000000000000000000*(d^2))) := by
    have he : (28818750000000000000000000+(-32277000000000000000000000*d)+(8299800000000000000000000*(d^2)))=11131322880000000000000000+(2141397276600000000000000000000/1117:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^2+(2132126400000000000000000000000/1117:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A (1/25:ℝ) d 3)-highReserve=(304475277812109375000000+(-3587330066844935477078875*d)+(-1927162783090703657398716*(d^3))+(6204122940008647834328340*(d^2)))/(28818750000000000000000000+(-32277000000000000000000000*d)+(8299800000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_bootstrap_hi_5 {d : ℝ}
    (hd0 : (64883/100000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A (1/25:ℝ) d 4 := by
  have hlo : 0 ≤ d-(64883/100000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (1032522251778368143359375000000+(-11928546464234699948224958192875*d)+(-6333901026605648759973256759548*(d^3))+(20440967591900769767641625176020*(d^2))) := by
    have he : (1032522251778368143359375000000+(-11928546464234699948224958192875*d)+(-6333901026605648759973256759548*(d^3))+(20440967591900769767641625176020*(d^2)))=(168098077057736056193886977159712274256410924/1393668613:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^3+(577988703476722585220369682993576684008744000/1393668613:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^2+(652695312648469050215411076966329773888000000/1393668613:ℝ)*(d-(64883/100000:ℝ))^2*((33/50:ℝ)-d)^1+(242795858870423892418323094033800192000000000/1393668613:ℝ)*(d-(64883/100000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (97728790518750000000000000000000+(-112222845381000000000000000000000*d)+(29252531669400000000000000000000*(d^2))) := by
    have he : (97728790518750000000000000000000+(-112222845381000000000000000000000*d)+(29252531669400000000000000000000*(d^2)))=36404115362480640000000000000000+(7393625435613919800000000000000000000/1117:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^2+(7360950357739200000000000000000000000/1117:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A (1/25:ℝ) d 4)-highReserve=(1032522251778368143359375000000+(-11928546464234699948224958192875*d)+(-6333901026605648759973256759548*(d^3))+(20440967591900769767641625176020*(d^2)))/(97728790518750000000000000000000+(-112222845381000000000000000000000*d)+(29252531669400000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_bootstrap_hi_6 {d : ℝ}
    (hd0 : (64883/100000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A (1/25:ℝ) d 5 := by
  have hlo : 0 ≤ d-(64883/100000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (304475277812109375000000+(-3666725439983658737078875*d)+(-1965272562197290822198716*(d^3))+(6331155537030605050328340*(d^2))) := by
    have he : (304475277812109375000000+(-3666725439983658737078875*d)+(-1965272562197290822198716*(d^3))+(6331155537030605050328340*(d^2)))=(53882233951893156618515787795329948908/1393668613:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^3+(184734403219939457068182292371687848000/1393668613:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^2+(208134747018686071136324384754496000000/1393668613:ℝ)*(d-(64883/100000:ℝ))^2*((33/50:ℝ)-d)^1+(77279838811953846232125348864000000000/1393668613:ℝ)*(d-(64883/100000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (28818750000000000000000000+(-32277000000000000000000000*d)+(8299800000000000000000000*(d^2))) := by
    have he : (28818750000000000000000000+(-32277000000000000000000000*d)+(8299800000000000000000000*(d^2)))=11131322880000000000000000+(2141397276600000000000000000000/1117:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^2+(2132126400000000000000000000000/1117:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A (1/25:ℝ) d 5)-highReserve=(304475277812109375000000+(-3666725439983658737078875*d)+(-1965272562197290822198716*(d^3))+(6331155537030605050328340*(d^2)))/(28818750000000000000000000+(-32277000000000000000000000*d)+(8299800000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_bootstrap_hi_7 {d : ℝ}
    (hd0 : (64883/100000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .A (1/25:ℝ) d 6 := by
  have hlo : 0 ≤ d-(64883/100000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (60895055562421875000000+(-87268346938114394925755*d)+(25164129886795257970302*(d^2))) := by
    have he : (60895055562421875000000+(-87268346938114394925755*d)+(25164129886795257970302*(d^2)))=(148663387013556950794307845544078/1247689:ℝ)*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^2+(291226405625046512314338649412000/1247689:ℝ)*(d-(64883/100000:ℝ))^1*((33/50:ℝ)-d)^1+(142594415619543887208652512000000/1247689:ℝ)*(d-(64883/100000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (5763750000000000000000000+(-2305500000000000000000000*d)) := by
    have he : (5763750000000000000000000+(-2305500000000000000000000*d))=4242120000000000000000000+2305500000000000000000000*(d-(64883/100000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .A (1/25:ℝ) d 6)-highReserve=(60895055562421875000000+(-87268346938114394925755*d)+(25164129886795257970302*(d^2)))/(5763750000000000000000000+(-2305500000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_saturated_lo_0 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ highBase .A (17/500:ℝ) d+gamma d*supplied (17/500:ℝ) := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (-361045308950563800000000+(-9771529950765794862409355*d)+(16119013981940688152963742*(d^2))) := by
    have he : (-361045308950563800000000+(-9771529950765794862409355*d)+(16119013981940688152963742*(d^2)))=(234652682308194833600924128/9:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(539954071718660339050708900/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1+(1530280658685252376927876250/9:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (47262750000000000000000000+(-18905100000000000000000000*d)) := by
    have he : (47262750000000000000000000+(-18905100000000000000000000*d))=33083925000000000000000000+18905100000000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (highBase .A (17/500:ℝ) d+gamma d*supplied (17/500:ℝ))-highReserve=(-361045308950563800000000+(-9771529950765794862409355*d)+(16119013981940688152963742*(d^2)))/(47262750000000000000000000+(-18905100000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_saturated_lo_1 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .A (17/500:ℝ) d 0 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (281728090822575000000000+(-10028639310675050382409355*d)+(14833467182394410552963742*(d^2))) := by
    have he : (281728090822575000000000+(-10028639310675050382409355*d)+(14833467182394410552963742*(d^2)))=(414281501426823281602772384/27:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(3694024213879318027456380100/27:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1+(3680246326377143830783628750/27:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (47262750000000000000000000+(-18905100000000000000000000*d)) := by
    have he : (47262750000000000000000000+(-18905100000000000000000000*d))=33083925000000000000000000+18905100000000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .A (17/500:ℝ) d 0)-highReserve=(281728090822575000000000+(-10028639310675050382409355*d)+(14833467182394410552963742*(d^2)))/(47262750000000000000000000+(-18905100000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_saturated_lo_2 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .A (17/500:ℝ) d 1 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (7043202270564375000000000+(-136017823987968592060233875*d)+(-79108106932795873553347356*(d^3))+(251050484563634752707461940*(d^2))) := by
    have he : (7043202270564375000000000+(-136017823987968592060233875*d)+(-79108106932795873553347356*(d^3))+(251050484563634752707461940*(d^2)))=(1295255067891106685507637367808/243:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(246128720317069225005405886400/9:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(3220036687369168395354319345000/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(4290666411453073399151173062500/243:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (1181568750000000000000000000+(-1323357000000000000000000000*d)+(340291800000000000000000000*(d^2))) := by
    have he : (1181568750000000000000000000+(-1323357000000000000000000000*d)+(340291800000000000000000000*(d^2)))=380465137500000000000000000+(28118185400000000000000000000/3:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(27097310000000000000000000000/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .A (17/500:ℝ) d 1)-highReserve=(7043202270564375000000000+(-136017823987968592060233875*d)+(-79108106932795873553347356*(d^3))+(251050484563634752707461940*(d^2)))/(1181568750000000000000000000+(-1323357000000000000000000000*d)+(340291800000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_saturated_lo_3 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .A (17/500:ℝ) d 2 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (32398730444596125000000000+(-1088910910704157001477075825*d)+(-632396127492188817460042068*(d^3))+(2011370886140747396240935500*(d^2))) := by
    have he : (32398730444596125000000000+(-1088910910704157001477075825*d)+(-632396127492188817460042068*(d^3))+(2011370886140747396240935500*(d^2)))=(2686443437755917854396401639424/243:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(3361092477901430001146054081600/27:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(18163415327988254336382969835000/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(26773184861627208970588034187500/243:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (5435216250000000000000000000+(-4726275000000000000000000000*d)+(1020875400000000000000000000*(d^2))) := by
    have he : (5435216250000000000000000000+(-4726275000000000000000000000*d)+(1020875400000000000000000000*(d^2)))=2464752412500000000000000000+(109561356200000000000000000000/3:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(106498730000000000000000000000/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .A (17/500:ℝ) d 2)-highReserve=(32398730444596125000000000+(-1088910910704157001477075825*d)+(-632396127492188817460042068*(d^3))+(2011370886140747396240935500*(d^2)))/(5435216250000000000000000000+(-4726275000000000000000000000*d)+(1020875400000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_saturated_lo_4 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .A (17/500:ℝ) d 3 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (52119696802176375000000000+(-976195971184508705745730675*d)+(-563147254361194689108996396*(d^3))+(1790007372886425441070783260*(d^2))) := by
    have he : (52119696802176375000000000+(-976195971184508705745730675*d)+(-563147254361194689108996396*(d^3))+(1790007372886425441070783260*(d^2)))=(8551661469967174332723638230528/243:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(5019530253410270300041435203200/27:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(22172998278820581428496446345000/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(29758039242926715608386574312500/243:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (8743608750000000000000000000+(-10019703000000000000000000000*d)+(2608903800000000000000000000*(d^2))) := by
    have he : (8743608750000000000000000000+(-10019703000000000000000000000*d)+(2608903800000000000000000000*(d^2)))=2696339887500000000000000000+(211371621400000000000000000000/3:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(203544910000000000000000000000/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .A (17/500:ℝ) d 3)-highReserve=(52119696802176375000000000+(-976195971184508705745730675*d)+(-563147254361194689108996396*(d^3))+(1790007372886425441070783260*(d^2)))/(8743608750000000000000000000+(-10019703000000000000000000000*d)+(2608903800000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_saturated_hi_0 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ highBase .A (1/25:ℝ) d+gamma d*supplied (1/25:ℝ) := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (-6264988881982425000000+(-234415502107147149083155*d)+(382682173906401047633262*(d^2))) := by
    have he : (-6264988881982425000000+(-234415502107147149083155*d)+(382682173906401047633262*(d^2)))=(19057115603095843180555424/27:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(119331721440982356498936100/27:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1+(110607024533359341604478750/27:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (1152750000000000000000000+(-461100000000000000000000*d)) := by
    have he : (1152750000000000000000000+(-461100000000000000000000*d))=806925000000000000000000+461100000000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (highBase .A (1/25:ℝ) d+gamma d*supplied (1/25:ℝ))-highReserve=(-6264988881982425000000+(-234415502107147149083155*d)+(382682173906401047633262*(d^2)))/(1152750000000000000000000+(-461100000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_saturated_hi_1 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .A (1/25:ℝ) d 0 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (12179011112484375000000+(-241793102104933869083155*d)+(345794173917467447633262*(d^2))) := by
    have he : (12179011112484375000000+(-241793102104933869083155*d)+(345794173917467447633262*(d^2)))=(3581673201863157326851808/9:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(9542955716779543610992900/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1+(28159341513732680534826250/9:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (1152750000000000000000000+(-461100000000000000000000*d)) := by
    have he : (1152750000000000000000000+(-461100000000000000000000*d))=806925000000000000000000+461100000000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .A (1/25:ℝ) d 0)-highReserve=(12179011112484375000000+(-241793102104933869083155*d)+(345794173917467447633262*(d^2)))/(1152750000000000000000000+(-461100000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_saturated_hi_2 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .A (1/25:ℝ) d 1 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (304475277812109375000000+(-3587330066844935477078875*d)+(-1927162783090703657398716*(d^3))+(6204122940008647834328340*(d^2))) := by
    have he : (304475277812109375000000+(-3587330066844935477078875*d)+(-1927162783090703657398716*(d^3))+(6204122940008647834328340*(d^2)))=(9477977208308224230429572096/81:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(49270890515160153938747633600/81:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(72257355971935784319617545000/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(32308342479653507615050187500/81:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (28818750000000000000000000+(-32277000000000000000000000*d)+(8299800000000000000000000*(d^2))) := by
    have he : (28818750000000000000000000+(-32277000000000000000000000*d)+(8299800000000000000000000*(d^2)))=9279637500000000000000000+(685809400000000000000000000/3:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(660910000000000000000000000/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .A (1/25:ℝ) d 1)-highReserve=(304475277812109375000000+(-3587330066844935477078875*d)+(-1927162783090703657398716*(d^3))+(6204122940008647834328340*(d^2)))/(28818750000000000000000000+(-32277000000000000000000000*d)+(8299800000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_saturated_hi_3 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .A (1/25:ℝ) d 2 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (1400586277935703125000000+(-26939903655992596194562825*d)+(-14929073043953535772196148*(d^3))+(47874550267805017408315500*(d^2))) := by
    have he : (1400586277935703125000000+(-26939903655992596194562825*d)+(-14929073043953535772196148*(d^3))+(47874550267805017408315500*(d^2)))=(20261686421332166587495948288/81:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(228236959700711962135564932800/81:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(412172347214126739430072435000/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(67662606339395569161485187500/27:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (132566250000000000000000000+(-115275000000000000000000000*d)+(24899400000000000000000000*(d^2))) := by
    have he : (132566250000000000000000000+(-115275000000000000000000000*d)+(24899400000000000000000000*(d^2)))=60115912500000000000000000+(2672228200000000000000000000/3:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(2597530000000000000000000000/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .A (1/25:ℝ) d 2)-highReserve=(1400586277935703125000000+(-26939903655992596194562825*d)+(-14929073043953535772196148*(d^3))+(47874550267805017408315500*(d^2)))/(132566250000000000000000000+(-115275000000000000000000000*d)+(24899400000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem A_saturated_hi_4 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .A (1/25:ℝ) d 3 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (2253117055809609375000000+(-26151419936164744530383675*d)+(-13895857221054828573390156*(d^3))+(44839712298124247745628860*(d^2))) := by
    have he : (2253117055809609375000000+(-26151419936164744530383675*d)+(-13895857221054828573390156*(d^3))+(44839712298124247745628860*(d^2)))=(19642785458497085459530726912/27:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(325564009935321894277178185600/81:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(489936274244562137871864545000/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(222175056249826058858833937500/81:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (213258750000000000000000000+(-244383000000000000000000000*d)+(63631800000000000000000000*(d^2))) := by
    have he : (213258750000000000000000000+(-244383000000000000000000000*d)+(63631800000000000000000000*(d^2)))=65764387500000000000000000+(5155405400000000000000000000/3:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(4964510000000000000000000000/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .A (1/25:ℝ) d 3)-highReserve=(2253117055809609375000000+(-26151419936164744530383675*d)+(-13895857221054828573390156*(d^3))+(44839712298124247745628860*(d^2)))/(213258750000000000000000000+(-244383000000000000000000000*d)+(63631800000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

end Sil.Uneven.MainSource
