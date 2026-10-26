/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Exact source margins, retaining all stated width and frequency losses. -/
import Candidate.Uneven.MainParameters
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Sil.Uneven.MainSource

theorem C_bootstrap_lo_0 {d : ℝ}
    (hd0 : (15987/25000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ highBase .C (17/500:ℝ) d+gamma d*supplied (17/500:ℝ) := by
  have hlo : 0 ≤ d-(15987/25000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (-2514476637620736000000000+(-59780577552777932723358355*d)+(100613951216838170849343342*(d^2))) := by
    have he : (-2514476637620736000000000+(-59780577552777932723358355*d)+(100613951216838170849343342*(d^2)))=(9295662208986757140784878745474/9747:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^2+(51319129128340486057975715191000/9747:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^1+(4778239011318250063162154000000/1083:ℝ)*(d-(15987/25000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (295117500000000000000000000+(-118047000000000000000000000*d)) := by
    have he : (295117500000000000000000000+(-118047000000000000000000000*d))=217206480000000000000000000+118047000000000000000000000*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (highBase .C (17/500:ℝ) d+gamma d*supplied (17/500:ℝ))-highReserve=(-2514476637620736000000000+(-59780577552777932723358355*d)+(100613951216838170849343342*(d^2)))/(295117500000000000000000000+(-118047000000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_bootstrap_lo_1 {d : ℝ}
    (hd0 : (15987/25000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C (17/500:ℝ) d 0 := by
  have hlo : 0 ≤ d-(15987/25000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (1499121360962700000000000+(-61386016752211307123358355*d)+(92586755219671298849343342*(d^2))) := by
    have he : (1499121360962700000000000+(-61386016752211307123358355*d)+(92586755219671298849343342*(d^2)))=(22067832795911565010607908709266/87723:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^2+(287933527824454480777781436719000/87723:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^1+(273987682956678141116134474000000/87723:ℝ)*(d-(15987/25000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (295117500000000000000000000+(-118047000000000000000000000*d)) := by
    have he : (295117500000000000000000000+(-118047000000000000000000000*d))=217206480000000000000000000+118047000000000000000000000*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C (17/500:ℝ) d 0)-highReserve=(1499121360962700000000000+(-61386016752211307123358355*d)+(92586755219671298849343342*(d^2)))/(295117500000000000000000000+(-118047000000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_bootstrap_lo_2 {d : ℝ}
    (hd0 : (15987/25000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C (17/500:ℝ) d 1 := by
  have hlo : 0 ≤ d-(15987/25000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (79254491230816544896500000000000+(-3024883946007071362160081294499725*d)+(-1794737337403635975842072375119956*(d^3))+(5684116203314200857285773455599780*(d^2))) := by
    have he : (79254491230816544896500000000000+(-3024883946007071362160081294499725*d)+(-1794737337403635975842072375119956*(d^3))+(5684116203314200857285773455599780*(d^2)))=(674721527001316927109983182787484990444/45001899:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^3+(72785483397757514933081921042625851253398000/15000633:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^2+(147208533942995683460656573126540892216000000/15000633:ℝ)*(d-(15987/25000:ℝ))^2*((33/50:ℝ)-d)^1+(223189059768852139551233454853952072000000000/45001899:ℝ)*(d-(15987/25000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (15602063932162500000000000000000000+(-13662121145730000000000000000000000*d)+(2968518229146000000000000000000000*(d^2))) := by
    have he : (15602063932162500000000000000000000+(-13662121145730000000000000000000000*d)+(2968518229146000000000000000000000*(d^2)))=7878150516596697600000000000000000+(4300259244438314000000000000000000000/9:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^2+(4273542580376000000000000000000000000/9:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C (17/500:ℝ) d 1)-highReserve=(79254491230816544896500000000000+(-3024883946007071362160081294499725*d)+(-1794737337403635975842072375119956*(d^3))+(5684116203314200857285773455599780*(d^2)))/(15602063932162500000000000000000000+(-13662121145730000000000000000000000*d)+(2968518229146000000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_bootstrap_lo_3 {d : ℝ}
    (hd0 : (15987/25000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C (17/500:ℝ) d 2 := by
  have hlo : 0 ≤ d-(15987/25000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (1499121360962700000000000+(-62060202613353822753358355*d)+(93395778253042317605343342*(d^2))) := by
    have he : (1499121360962700000000000+(-62060202613353822753358355*d)+(93395778253042317605343342*(d^2)))=(391304891287873116360832236422/29241:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^2+(82562308048724727406641145573000/29241:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^1+(84901989109334064699378158000000/29241:ℝ)*(d-(15987/25000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (295117500000000000000000000+(-118047000000000000000000000*d)) := by
    have he : (295117500000000000000000000+(-118047000000000000000000000*d))=217206480000000000000000000+118047000000000000000000000*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C (17/500:ℝ) d 2)-highReserve=(1499121360962700000000000+(-62060202613353822753358355*d)+(93395778253042317605343342*(d^2)))/(295117500000000000000000000+(-118047000000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_bootstrap_lo_4 {d : ℝ}
    (hd0 : (15987/25000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C (17/500:ℝ) d 3 := by
  have hlo : 0 ≤ d-(15987/25000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (37478034024067500000000000+(-808571954061420803083958875*d)+(-485825027080766631288180156*(d^3))+(1531994863881060139454033940*(d^2))) := by
    have he : (37478034024067500000000000+(-808571954061420803083958875*d)+(-485825027080766631288180156*(d^3))+(1531994863881060139454033940*(d^2)))=(5441973145151046014525954791245295276/2368521:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^3+(6482178342183296158094807668195342000/789507:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^2+(7545467334906810112636610604364000000/789507:ℝ)*(d-(15987/25000:ℝ))^2*((33/50:ℝ)-d)^1+(8630689436542621513689058288000000000/2368521:ℝ)*(d-(15987/25000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (7377937500000000000000000000+(-8263290000000000000000000000*d)+(2124846000000000000000000000*(d^2))) := by
    have he : (7377937500000000000000000000+(-8263290000000000000000000000*d)+(2124846000000000000000000000*(d^2)))=2849749017600000000000000000+(2413199614000000000000000000000/9:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^2+(2394076000000000000000000000000/9:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C (17/500:ℝ) d 3)-highReserve=(37478034024067500000000000+(-808571954061420803083958875*d)+(-485825027080766631288180156*(d^3))+(1531994863881060139454033940*(d^2)))/(7377937500000000000000000000+(-8263290000000000000000000000*d)+(2124846000000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_bootstrap_lo_5 {d : ℝ}
    (hd0 : (15987/25000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C (17/500:ℝ) d 4 := by
  have hlo : 0 ≤ d-(15987/25000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (127093747514818574827500000000000+(-2638074636402594783815870140832875*d)+(-1572328319970387307555371021359868*(d^3))+(4965715654878825483266495609732820*(d^2))) := by
    have he : (127093747514818574827500000000000+(-2638074636402594783815870140832875*d)+(-1572328319970387307555371021359868*(d^3))+(4965715654878825483266495609732820*(d^2)))=(310304700650400100460564110591652453109971332/45001899:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^3+(373857504999648462711664448965215999977194000/15000633:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^2+(438835295001744187698893949135733842148000000/15000633:ℝ)*(d-(15987/25000:ℝ))^2*((33/50:ℝ)-d)^1+(505167312896437128369647122359595216000000000/45001899:ℝ)*(d-(15987/25000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (25019714886937500000000000000000000+(-28730362673370000000000000000000000*d)+(7488990687438000000000000000000000*(d^2))) := by
    have he : (25019714886937500000000000000000000+(-28730362673370000000000000000000000*d)+(7488990687438000000000000000000000*(d^2)))=9319879865961292800000000000000000+(8332705725814942000000000000000000000/9:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^2+(8265304809628000000000000000000000000/9:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C (17/500:ℝ) d 4)-highReserve=(127093747514818574827500000000000+(-2638074636402594783815870140832875*d)+(-1572328319970387307555371021359868*(d^3))+(4965715654878825483266495609732820*(d^2)))/(25019714886937500000000000000000000+(-28730362673370000000000000000000000*d)+(7488990687438000000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_bootstrap_lo_6 {d : ℝ}
    (hd0 : (15987/25000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C (17/500:ℝ) d 5 := by
  have hlo : 0 ≤ d-(15987/25000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (37478034024067500000000000+(-818684741978558537533958875*d)+(-490679165280992743824180156*(d^3))+(1548175324548480514574033940*(d^2))) := by
    have he : (37478034024067500000000000+(-818684741978558537533958875*d)+(-490679165280992743824180156*(d^3))+(1548175324548480514574033940*(d^2)))=(97566456876204977696665952103524610244/45001899:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^3+(117495167480478512949297709483711498000/15000633:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^2+(137867490946754396025476197482916000000/15000633:ℝ)*(d-(15987/25000:ℝ))^2*((33/50:ℝ)-d)^1+(158661345780795247383124107472000000000/45001899:ℝ)*(d-(15987/25000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (7377937500000000000000000000+(-8263290000000000000000000000*d)+(2124846000000000000000000000*(d^2))) := by
    have he : (7377937500000000000000000000+(-8263290000000000000000000000*d)+(2124846000000000000000000000*(d^2)))=2849749017600000000000000000+(2413199614000000000000000000000/9:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^2+(2394076000000000000000000000000/9:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C (17/500:ℝ) d 5)-highReserve=(37478034024067500000000000+(-818684741978558537533958875*d)+(-490679165280992743824180156*(d^3))+(1548175324548480514574033940*(d^2)))/(7377937500000000000000000000+(-8263290000000000000000000000*d)+(2124846000000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_bootstrap_lo_7 {d : ℝ}
    (hd0 : (15987/25000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C (17/500:ℝ) d 6 := by
  have hlo : 0 ≤ d-(15987/25000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (299824272192540000000000+(-68072251967518843401054*(d^2))+(50250921081130108502635*d)) := by
    have he : (299824272192540000000000+(-68072251967518843401054*(d^2))+(50250921081130108502635*d))=(63358672350787085844430374436958/87723:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^2+(126559978675661987380396707097000/87723:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^1+(63195334822715554880466662000000/87723:ℝ)*(d-(15987/25000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (59023500000000000000000000+(-23609400000000000000000000*d)) := by
    have he : (59023500000000000000000000+(-23609400000000000000000000*d))=43441296000000000000000000+23609400000000000000000000*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C (17/500:ℝ) d 6)-highReserve=(299824272192540000000000+(-68072251967518843401054*(d^2))+(50250921081130108502635*d))/(59023500000000000000000000+(-23609400000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_bootstrap_hi_0 {d : ℝ}
    (hd0 : (15987/25000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ highBase .C (1/25:ℝ) d+gamma d*supplied (1/25:ℝ) := by
  have hlo : 0 ≤ d-(15987/25000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (-13130221011458802000000000+(-411964465539640378063508485*d)+(685895905990625159545403394*(d^2))) := by
    have he : (-13130221011458802000000000+(-411964465539640378063508485*d)+(685895905990625159545403394*(d^2)))=(271761028488725982263510053654954/29241:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^2+(1206530328377686610310890019011000/29241:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^1+(954825582076032498337647106000000/29241:ℝ)*(d-(15987/25000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (2065822500000000000000000000+(-826329000000000000000000000*d)) := by
    have he : (2065822500000000000000000000+(-826329000000000000000000000*d))=1520445360000000000000000000+826329000000000000000000000*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (highBase .C (1/25:ℝ) d+gamma d*supplied (1/25:ℝ))-highReserve=(-13130221011458802000000000+(-411964465539640378063508485*d)+(685895905990625159545403394*(d^2)))/(2065822500000000000000000000+(-826329000000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_bootstrap_hi_1 {d : ℝ}
    (hd0 : (15987/25000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C (1/25:ℝ) d 0 := by
  have hlo : 0 ≤ d-(15987/25000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (19922938978625250000000000+(-425185729535673998863508485*d)+(619789586010457055545403394*(d^2))) := by
    have he : (19922938978625250000000000+(-425185729535673998863508485*d)+(619789586010457055545403394*(d^2)))=(308045568268989201995338160964862/87723:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^2+(2187155172922790574724670057033000/87723:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^1+(1933479406507396697012941318000000/87723:ℝ)*(d-(15987/25000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (2065822500000000000000000000+(-826329000000000000000000000*d)) := by
    have he : (2065822500000000000000000000+(-826329000000000000000000000*d))=1520445360000000000000000000+826329000000000000000000000*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C (1/25:ℝ) d 0)-highReserve=(19922938978625250000000000+(-425185729535673998863508485*d)+(619789586010457055545403394*(d^2)))/(2065822500000000000000000000+(-826329000000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_bootstrap_hi_2 {d : ℝ}
    (hd0 : (15987/25000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C (1/25:ℝ) d 1 := by
  have hlo : 0 ≤ d-(15987/25000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (1053271892249979786198750000000000+(-21524891602092852349626574061498075*d)+(-12170206524205932232753851425839692*(d^3))+(38866949448586465895943458189198460*(d^2))) := by
    have he : (1053271892249979786198750000000000+(-21524891602092852349626574061498075*d)+(-12170206524205932232753851425839692*(d^3))+(38866949448586465895943458189198460*(d^2)))=(4723368903610726458294865300487594933108/45001899:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^3+(472175761723687142811629565829889358773786000/15000633:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^2+(955691678259706922157233345838586245512000000/15000633:ℝ)*(d-(15987/25000:ℝ))^2*((33/50:ℝ)-d)^1+(1450004790572151492345730401577664504000000000/45001899:ℝ)*(d-(15987/25000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (109214447525137500000000000000000000+(-95634848020110000000000000000000000*d)+(20779627604022000000000000000000000*(d^2))) := by
    have he : (109214447525137500000000000000000000+(-95634848020110000000000000000000000*d)+(20779627604022000000000000000000000*(d^2)))=55147053616176883200000000000000000+(30101814711068198000000000000000000000/9:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^2+(29914798062632000000000000000000000000/9:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C (1/25:ℝ) d 1)-highReserve=(1053271892249979786198750000000000+(-21524891602092852349626574061498075*d)+(-12170206524205932232753851425839692*(d^3))+(38866949448586465895943458189198460*(d^2)))/(109214447525137500000000000000000000+(-95634848020110000000000000000000000*d)+(20779627604022000000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_bootstrap_hi_3 {d : ℝ}
    (hd0 : (15987/25000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C (1/25:ℝ) d 2 := by
  have hlo : 0 ≤ d-(15987/25000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (19922938978625250000000000+(-434564704572977243873508485*d)+(631044356055220949557403394*(d^2))) := by
    have he : (19922938978625250000000000+(-434564704572977243873508485*d)+(631044356055220949557403394*(d^2)))=(214551053291628843108479468702/1083:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^2+(180806916856768186517856006337000/9747:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^1+(185026746715613765525215702000000/9747:ℝ)*(d-(15987/25000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (2065822500000000000000000000+(-826329000000000000000000000*d)) := by
    have he : (2065822500000000000000000000+(-826329000000000000000000000*d))=1520445360000000000000000000+826329000000000000000000000*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C (1/25:ℝ) d 2)-highReserve=(19922938978625250000000000+(-434564704572977243873508485*d)+(631044356055220949557403394*(d^2)))/(2065822500000000000000000000+(-826329000000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_bootstrap_hi_4 {d : ℝ}
    (hd0 : (15987/25000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C (1/25:ℝ) d 3 := by
  have hlo : 0 ≤ d-(15987/25000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (498073474465631250000000000+(-6153298084356498146587712125*d)+(-3400597108289336643817261092*(d^3))+(10883120248540422148178237580*(d^2))) := by
    have he : (498073474465631250000000000+(-6153298084356498146587712125*d)+(-3400597108289336643817261092*(d^3))+(10883120248540422148178237580*(d^2)))=(34093370016776176348883067859517066932/2368521:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^3+(40831953546386703597428377277367394000/789507:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^2+(47738260325215310345847474230548000000/789507:ℝ)*(d-(15987/25000:ℝ))^2*((33/50:ℝ)-d)^1+(54804235967598474026223408016000000000/2368521:ℝ)*(d-(15987/25000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (51645562500000000000000000000+(-57843030000000000000000000000*d)+(14873922000000000000000000000*(d^2))) := by
    have he : (51645562500000000000000000000+(-57843030000000000000000000000*d)+(14873922000000000000000000000*(d^2)))=19948243123200000000000000000+(16892397298000000000000000000000/9:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^2+(16758532000000000000000000000000/9:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C (1/25:ℝ) d 3)-highReserve=(498073474465631250000000000+(-6153298084356498146587712125*d)+(-3400597108289336643817261092*(d^3))+(10883120248540422148178237580*(d^2)))/(51645562500000000000000000000+(-57843030000000000000000000000*d)+(14873922000000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_bootstrap_hi_5 {d : ℝ}
    (hd0 : (15987/25000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C (1/25:ℝ) d 4 := by
  have hlo : 0 ≤ d-(15987/25000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (1689043357154548810331250000000000+(-20427053619464282737695665985830125*d)+(-11154971807518605346631951549519076*(d^3))+(35788004029396830561773985268129740*(d^2))) := by
    have he : (1689043357154548810331250000000000+(-20427053619464282737695665985830125*d)+(-11154971807518605346631951549519076*(d^3))+(35788004029396830561773985268129740*(d^2)))=(1792811357470795522333727455920951777369799324/45001899:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^3+(2208177762329621681223501144405197199840358000/15000633:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^2+(2634062052482796706715552839228536895036000000/15000633:ℝ)*(d-(15987/25000:ℝ))^2*((33/50:ℝ)-d)^1+(3069962233015690799091452549317166512000000000/45001899:ℝ)*(d-(15987/25000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (175138004208562500000000000000000000+(-201112538713590000000000000000000000*d)+(52422934812066000000000000000000000*(d^2))) := by
    have he : (175138004208562500000000000000000000+(-201112538713590000000000000000000000*d)+(52422934812066000000000000000000000*(d^2)))=65239159061729049600000000000000000+(58328940080704594000000000000000000000/9:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^2+(57857133667396000000000000000000000000/9:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C (1/25:ℝ) d 4)-highReserve=(1689043357154548810331250000000000+(-20427053619464282737695665985830125*d)+(-11154971807518605346631951549519076*(d^3))+(35788004029396830561773985268129740*(d^2)))/(175138004208562500000000000000000000+(-201112538713590000000000000000000000*d)+(52422934812066000000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_bootstrap_hi_6 {d : ℝ}
    (hd0 : (15987/25000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C (1/25:ℝ) d 5 := by
  have hlo : 0 ≤ d-(15987/25000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (498073474465631250000000000+(-6293982709916046821737712125*d)+(-3468125728557920007889261092*(d^3))+(11108215649435700028418237580*(d^2))) := by
    have he : (498073474465631250000000000+(-6293982709916046821737712125*d)+(-3468125728557920007889261092*(d^3))+(11108215649435700028418237580*(d^2)))=(566655284004266598850762592931552271708/45001899:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^3+(696981160661073519773165945345980486000/15000633:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^2+(830563625417541312362629702380412000000/15000633:ℝ)*(d-(15987/25000:ℝ))^2*((33/50:ℝ)-d)^1+(967246606029914111687308752304000000000/45001899:ℝ)*(d-(15987/25000:ℝ))^3*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (51645562500000000000000000000+(-57843030000000000000000000000*d)+(14873922000000000000000000000*(d^2))) := by
    have he : (51645562500000000000000000000+(-57843030000000000000000000000*d)+(14873922000000000000000000000*(d^2)))=19948243123200000000000000000+(16892397298000000000000000000000/9:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^2+(16758532000000000000000000000000/9:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C (1/25:ℝ) d 5)-highReserve=(498073474465631250000000000+(-6293982709916046821737712125*d)+(-3468125728557920007889261092*(d^3))+(11108215649435700028418237580*(d^2)))/(51645562500000000000000000000+(-57843030000000000000000000000*d)+(14873922000000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_bootstrap_hi_7 {d : ℝ}
    (hd0 : (15987/25000:ℝ) ≤ d) (hd1 : d ≤ (33/50:ℝ)) :
    highReserve ≤ bootstrapChannel .C (1/25:ℝ) d 6 := by
  have hlo : 0 ≤ d-(15987/25000:ℝ) := by linarith
  have hhi : 0 ≤ (33/50:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (3984587795725050000000000+(-4058238976706563141132835*d)+(985761543476794456453134*(d^2))) := by
    have he : (3984587795725050000000000+(-4058238976706563141132835*d)+(985761543476794456453134*(d^2)))=(373445251411544836168038370736882/87723:ℝ)*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^2+(734931235667751836345292030463000/87723:ℝ)*(d-(15987/25000:ℝ))^1*((33/50:ℝ)-d)^1+(361572458216085415017357098000000/87723:ℝ)*(d-(15987/25000:ℝ))^2*((33/50:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (413164500000000000000000000+(-165265800000000000000000000*d)) := by
    have he : (413164500000000000000000000+(-165265800000000000000000000*d))=304089072000000000000000000+165265800000000000000000000*(d-(15987/25000:ℝ))^0*((33/50:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (bootstrapChannel .C (1/25:ℝ) d 6)-highReserve=(3984587795725050000000000+(-4058238976706563141132835*d)+(985761543476794456453134*(d^2)))/(413164500000000000000000000+(-165265800000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_saturated_lo_0 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ highBase .C (17/500:ℝ) d+gamma d*supplied (17/500:ℝ) := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (-2514476637620736000000000+(-59780577552777932723358355*d)+(100613951216838170849343342*(d^2))) := by
    have he : (-2514476637620736000000000+(-59780577552777932723358355*d)+(100613951216838170849343342*(d^2)))=229355472543276003031783392*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(11431382311123813334349586700/9:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1+(10272708619185872844707626250/9:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (295117500000000000000000000+(-118047000000000000000000000*d)) := by
    have he : (295117500000000000000000000+(-118047000000000000000000000*d))=206582250000000000000000000+118047000000000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (highBase .C (17/500:ℝ) d+gamma d*supplied (17/500:ℝ))-highReserve=(-2514476637620736000000000+(-59780577552777932723358355*d)+(100613951216838170849343342*(d^2)))/(295117500000000000000000000+(-118047000000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_saturated_lo_1 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .C (17/500:ℝ) d 0 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (1499121360962700000000000+(-61386016752211307123358355*d)+(92586755219671298849343342*(d^2))) := by
    have he : (1499121360962700000000000+(-61386016752211307123358355*d)+(92586755219671298849343342*(d^2)))=(4383802927306850257858151584/27:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(27016155895940142723048760100/27:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1+(25132195359564417534122878750/27:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (295117500000000000000000000+(-118047000000000000000000000*d)) := by
    have he : (295117500000000000000000000+(-118047000000000000000000000*d))=206582250000000000000000000+118047000000000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .C (17/500:ℝ) d 0)-highReserve=(1499121360962700000000000+(-61386016752211307123358355*d)+(92586755219671298849343342*(d^2)))/(295117500000000000000000000+(-118047000000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_saturated_lo_2 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .C (17/500:ℝ) d 1 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (37478034024067500000000000+(-808571954061420803083958875*d)+(-485825027080766631288180156*(d^3))+(1531994863881060139454033940*(d^2))) := by
    have he : (37478034024067500000000000+(-808571954061420803083958875*d)+(-485825027080766631288180156*(d^3))+(1531994863881060139454033940*(d^2)))=(10494918354835827760645894878208/243:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(5427589854520051744308538619200/27:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(22583675951519510693758430345000/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(29279582037133267851741310562500/243:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (7377937500000000000000000000+(-8263290000000000000000000000*d)+(2124846000000000000000000000*(d^2))) := by
    have he : (7377937500000000000000000000+(-8263290000000000000000000000*d)+(2124846000000000000000000000*(d^2)))=2375695875000000000000000000+(175575238000000000000000000000/3:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(169200700000000000000000000000/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .C (17/500:ℝ) d 1)-highReserve=(37478034024067500000000000+(-808571954061420803083958875*d)+(-485825027080766631288180156*(d^3))+(1531994863881060139454033940*(d^2)))/(7377937500000000000000000000+(-8263290000000000000000000000*d)+(2124846000000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_saturated_lo_3 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .C (17/500:ℝ) d 2 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (172398956510710500000000000+(-6638131705666560394186210825*d)+(-3939356154946436469864540468*(d^3))+(12476059236589427692335835500*(d^2))) := by
    have he : (172398956510710500000000000+(-6638131705666560394186210825*d)+(-3939356154946436469864540468*(d^3))+(12476059236589427692335835500*(d^2)))=(31084765702218214426138290970624/243:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(25969308111897674744973132161600/27:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(128939603613983769177504142835000/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(183222539991438465191715446687500/243:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (33938512500000000000000000000+(-29511750000000000000000000000*d)+(6374538000000000000000000000*(d^2))) := by
    have he : (33938512500000000000000000000+(-29511750000000000000000000000*d)+(6374538000000000000000000000*(d^2)))=15390377625000000000000000000+(684121714000000000000000000000/3:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(664998100000000000000000000000/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .C (17/500:ℝ) d 2)-highReserve=(172398956510710500000000000+(-6638131705666560394186210825*d)+(-3939356154946436469864540468*(d^3))+(12476059236589427692335835500*(d^2)))/(33938512500000000000000000000+(-29511750000000000000000000000*d)+(6374538000000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_saturated_lo_4 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .C (17/500:ℝ) d 3 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (277337451778099500000000000+(-5789640527953885367821295675*d)+(-3451487625285608337209381196*(d^3))+(10900201282098487390151971260*(d^2))) := by
    have he : (277337451778099500000000000+(-5789640527953885367821295675*d)+(-3451487625285608337209381196*(d^3))+(10900201282098487390151971260*(d^2)))=(70671165163841669957931759676928/243:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+1377202179268771852828057161600*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(156095218083329054794443157345000/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(203457978358572871278101461812500/243:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (54596737500000000000000000000+(-62564910000000000000000000000*d)+(16290486000000000000000000000*(d^2))) := by
    have he : (54596737500000000000000000000+(-62564910000000000000000000000*d)+(16290486000000000000000000000*(d^2)))=16836453375000000000000000000+(1319844158000000000000000000000/3:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(1270972700000000000000000000000/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .C (17/500:ℝ) d 3)-highReserve=(277337451778099500000000000+(-5789640527953885367821295675*d)+(-3451487625285608337209381196*(d^3))+(10900201282098487390151971260*(d^2)))/(54596737500000000000000000000+(-62564910000000000000000000000*d)+(16290486000000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_saturated_hi_0 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ highBase .C (1/25:ℝ) d+gamma d*supplied (1/25:ℝ) := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (-13130221011458802000000000+(-411964465539640378063508485*d)+(685895905990625159545403394*(d^2))) := by
    have he : (-13130221011458802000000000+(-411964465539640378063508485*d)+(685895905990625159545403394*(d^2)))=(15277209313216519973402353696/9:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(79896231663231523200447106900/9:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1+(23597361834643543220984461250/3:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (2065822500000000000000000000+(-826329000000000000000000000*d)) := by
    have he : (2065822500000000000000000000+(-826329000000000000000000000*d))=1446075750000000000000000000+826329000000000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (highBase .C (1/25:ℝ) d+gamma d*supplied (1/25:ℝ))-highReserve=(-13130221011458802000000000+(-411964465539640378063508485*d)+(685895905990625159545403394*(d^2)))/(2065822500000000000000000000+(-826329000000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_saturated_hi_1 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .C (1/25:ℝ) d 0 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (19922938978625250000000000+(-425185729535673998863508485*d)+(619789586010457055545403394*(d^2))) := by
    have he : (19922938978625250000000000+(-425185729535673998863508485*d)+(619789586010457055545403394*(d^2)))=(30935670504118347152207061088/27:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(179752298207675488641341320700/27:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1+(165550946525839481988860151250/27:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (2065822500000000000000000000+(-826329000000000000000000000*d)) := by
    have he : (2065822500000000000000000000+(-826329000000000000000000000*d))=1446075750000000000000000000+826329000000000000000000000*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .C (1/25:ℝ) d 0)-highReserve=(19922938978625250000000000+(-425185729535673998863508485*d)+(619789586010457055545403394*(d^2)))/(2065822500000000000000000000+(-826329000000000000000000000*d)) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_saturated_hi_2 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .C (1/25:ℝ) d 1 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (498073474465631250000000000+(-6153298084356498146587712125*d)+(-3400597108289336643817261092*(d^3))+(10883120248540422148178237580*(d^2))) := by
    have he : (498073474465631250000000000+(-6153298084356498146587712125*d)+(-3400597108289336643817261092*(d^3))+(10883120248540422148178237580*(d^2)))=(66641950936599744415887664147456/243:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(34775718120881094681519770334400/27:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(145747301965401605707309012415000/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(190076048647560400599689173937500/243:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (51645562500000000000000000000+(-57843030000000000000000000000*d)+(14873922000000000000000000000*(d^2))) := by
    have he : (51645562500000000000000000000+(-57843030000000000000000000000*d)+(14873922000000000000000000000*(d^2)))=16629871125000000000000000000+(1229026666000000000000000000000/3:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(1184404900000000000000000000000/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .C (1/25:ℝ) d 1)-highReserve=(498073474465631250000000000+(-6153298084356498146587712125*d)+(-3400597108289336643817261092*(d^3))+(10883120248540422148178237580*(d^2)))/(51645562500000000000000000000+(-57843030000000000000000000000*d)+(14873922000000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_saturated_hi_3 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .C (1/25:ℝ) d 2 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (2291137982541903750000000000+(-47203062045177920294303475775*d)+(-26704617004368312203451783276*(d^3))+(85276185251774226306350848500*(d^2))) := by
    have he : (2291137982541903750000000000+(-47203062045177920294303475775*d)+(-26704617004368312203451783276*(d^3))+(85276185251774226306350848500*(d^2)))=(201984252703152349854187236794368/243:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(168874447520569276760091925131200/27:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(840423371645075782035528999845000/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(1196895118021194705254508126812500/243:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (237569587500000000000000000000+(-206582250000000000000000000000*d)+(44621766000000000000000000000*(d^2))) := by
    have he : (237569587500000000000000000000+(-206582250000000000000000000000*d)+(44621766000000000000000000000*(d^2)))=107732643375000000000000000000+(4788851998000000000000000000000/3:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(4654986700000000000000000000000/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .C (1/25:ℝ) d 2)-highReserve=(2291137982541903750000000000+(-47203062045177920294303475775*d)+(-26704617004368312203451783276*(d^3))+(85276185251774226306350848500*(d^2)))/(237569587500000000000000000000+(-206582250000000000000000000000*d)+(44621766000000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem C_saturated_hi_4 {d : ℝ}
    (hd0 : (33/50:ℝ) ≤ d) (hd1 : d ≤ (3/4:ℝ)) :
    highReserve ≤ saturatedChannel .C (1/25:ℝ) d 3 := by
  have hlo : 0 ≤ d-(33/50:ℝ) := by linarith
  have hhi : 0 ≤ (3/4:ℝ)-d := by linarith
  have hn : (0:ℝ) ≤ (3685743711045671250000000000+(-44794883597325376939749069725*d)+(-24477634149954472377265668372*(d^3))+(78522319819960882559063798820*(d^2))) := by
    have he : (3685743711045671250000000000+(-44794883597325376939749069725*d)+(-24477634149954472377265668372*(d^3))+(78522319819960882559063798820*(d^2)))=(429407047603523973973144717738496/243:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^3+(25854781858598104049229200393600/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^2+(993802116543519569212102101415000/81:ℝ)*(d-(33/50:ℝ))^2*((3/4:ℝ)-d)^1+(1310628001589197316834210232687500/243:ℝ)*(d-(33/50:ℝ))^3*((3/4:ℝ)-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (382177162500000000000000000000+(-437954370000000000000000000000*d)+(114033402000000000000000000000*(d^2))) := by
    have he : (382177162500000000000000000000+(-437954370000000000000000000000*d)+(114033402000000000000000000000*(d^2)))=117855173625000000000000000000+(9238909106000000000000000000000/3:ℝ)*(d-(33/50:ℝ))^0*((3/4:ℝ)-d)^2+(8896808900000000000000000000000/3:ℝ)*(d-(33/50:ℝ))^1*((3/4:ℝ)-d)^1 := by ring
    rw [he]
    positivity
  have he : (saturatedChannel .C (1/25:ℝ) d 3)-highReserve=(3685743711045671250000000000+(-44794883597325376939749069725*d)+(-24477634149954472377265668372*(d^3))+(78522319819960882559063798820*(d^2)))/(382177162500000000000000000000+(-437954370000000000000000000000*d)+(114033402000000000000000000000*(d^2))) := by
    norm_num [bootstrapChannel,saturatedChannel,highBase,total,amp,gap,supplied,frequency,
      Plane.B,Plane.lambda,Plane.q,Plane.incumbent,gamma,lowReserve,highReserve,widthMesh,discard,
      frequencyAllowance,Saturated.rho,Saturated.slope,Saturated.offset,Bootstrap.slope,Bootstrap.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

end Sil.Uneven.MainSource
