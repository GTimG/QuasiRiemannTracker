import Candidate.Uneven.RoundedAdmissionBase
import Candidate.Uneven.MainCountWindows
import Candidate.Uneven.WarmupAdmission10

/- Original module: Candidate.Uneven.RoundedAdmission10. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Count-admission arithmetic only; source moment theorems are separate. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.RoundedRows

theorem admission_10_D {d p : ℝ}
    (hd : (9087/20000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 0 d p := by
  let bx : ℝ := (d-(9087/20000:ℝ))/(429/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 0 d p-(7456109105/3782443642:ℝ) =
    (3891221821/484152786176:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 0 d p-(7456109105/3782443642:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_A {d p : ℝ}
    (hd : (9087/20000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 1 d p := by
  let bx : ℝ := (d-(9087/20000:ℝ))/(429/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 1 d p-(2782443642/1891221821:ℝ) =
    (7812500/1891221821:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 1 d p-(2782443642/1891221821:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_C {d p : ℝ}
    (hd : (9087/20000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 2 d p := by
  let bx : ℝ := (d-(9087/20000:ℝ))/(429/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 2 d p-(140060637487/189122182100:ℝ) =
    (49061544613/24207639308800:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 2 d p-(140060637487/189122182100:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_J {d p : ℝ}
    (hd : (9087/20000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 3 d p := by
  let bx : ℝ := (d-(9087/20000:ℝ))/(429/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 3 d p-(3131453249687/2904916717056:ℝ) =
    (288048784888877/29049167170560000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (384075927540473/29049167170560000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (2005002483627/605190982720000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (2454943012111/371829339783168:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (2452200824611/371829339783168:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 3 d p-(3131453249687/2904916717056:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_Tlo {d p : ℝ}
    (hd : (9087/20000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 4 d p := by
  let bx : ℝ := (d-(9087/20000:ℝ))/(429/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 4 d p-(1272731012844369/7564887284000000:ℝ) =
    (220420640654963931/123943113261056000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (9087/5120000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (2758220494793652057/991544906088448000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (7302894754358697/1936611144704000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 +
    (60086013481923/60519098272000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 4 d p-(1272731012844369/7564887284000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_Thi {d p : ℝ}
    (hd : (9087/20000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 5 d p := by
  let bx : ℝ := (d-(9087/20000:ℝ))/(429/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 5 d p-(3966752449945653407/39661796243537920000:ℝ) =
    (45397860937062497721/24788622652211200000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (47010391646240874577/12394311326105600000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (48579174730239585233/24788622652211200000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (2791149166697617/19830898121768960000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 +
    (5511889065402209/39661796243537920000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 5 d p-(3966752449945653407/39661796243537920000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_Rlo {d p : ℝ}
    (hd : (9087/20000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 6 d p := by
  let bx : ℝ := (d-(9087/20000:ℝ))/(429/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 6 d p-(80434455816024217809408239/317612733888918176440800000:ℝ) =
    (115973922195487887786962707693/26018835160180177014030336000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (9257725711297964640885392453/1040753406407207080561213440000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (28190869312571870442966517/6352254677778363528816000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (246313315671598211350108725667/41630136256288283222448537600000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (551895771948062993720402295251/41630136256288283222448537600000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (89273229842005584666122431/10163607484445381646105600000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 +
    (1222325836001675028409071/846967290370448470508800000:ℝ)*bx^1*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 6 d p-(80434455816024217809408239/317612733888918176440800000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_Rhi {d p : ℝ}
    (hd : (9087/20000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 7 d p := by
  let bx : ℝ := (d-(9087/20000:ℝ))/(429/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 7 d p-(60360967397413866106003/109876837669679801579520:ℝ) =
    (5407913000819813929022975171/703211761085950730108928000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (2654990976521667970338197/228910078478499586624000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (89601574441143766641783/22891007847849958662400000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (33748050099938281091541361/9001110541900169345394278400:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (10967733495094378479187/2930049004524794708787200:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 7 d p-(60360967397413866106003/109876837669679801579520:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_Mlo {d p : ℝ}
    (hd : (9087/20000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 8 d p := by
  let bx : ℝ := (d-(9087/20000:ℝ))/(429/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 8 d p-(3734662224845140237089084248851129/468807840723967153405952000000000000000:ℝ) =
    (268614602740702343489969556884432141/703211761085950730108928000000000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (71588028844019703166778894826038929/93761568144793430681190400000000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (536584958690148768066307317965469653/1406423522171901460217856000000000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (2874783845198533330249974143609952843/3750462725791737227247616000000000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (30017925814879344949860487200276814337/11251388177375211681742848000000000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (1423260208230184585106544720065986613/468807840723967153405952000000000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 +
    (1595577534299188949082130968802246613/1406423522171901460217856000000000000000:ℝ)*bx^1*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 8 d p-(3734662224845140237089084248851129/468807840723967153405952000000000000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_Mhi {d p : ℝ}
    (hd : (9087/20000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 9 d p := by
  let bx : ℝ := (d-(9087/20000:ℝ))/(429/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 9 d p-(2340462851490424960967457707/137346047087099751974400000000:ℝ) =
    (19360398269467558647212550926334407/14064235221719014602178560000000000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (3130130944481892312106118778980053/879014701357438412636160000000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (10277713687121476900399393681961/3433651177177493799360000000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (23144274930158379093450544047/28613759809812448328000000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (99720613409172200019584640349837/180022210838003386907885568000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (12453960016457926990238696063543/11251388177375211681742848000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (24302253676385045235862795531/43950735067871920631808000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 9 d p-(2340462851490424960967457707/137346047087099751974400000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_Width {d p : ℝ}
    (hd : (9087/20000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 10 d p := by
  let bx : ℝ := (d-(9087/20000:ℝ))/(429/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 10 d p-(5029622965732406225805523382174033/219753675339359603159040000000000000:ℝ) =
    (2045518276734914058844601929022124136763/1406423522171901460217856000000000000000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (5252177700813289045102783572561390761407/1406423522171901460217856000000000000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (17068415260271449981839818584175839559/5493841883483990078976000000000000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (37853522586817825377076584831326493/45782015695699917324800000000000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (11048519731589780448486653640098104633/18002221083800338690788556800000000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (22075901301299060873783571904500479717/18002221083800338690788556800000000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (43075441117799090994186555116348389/70321176108595073010892800000000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 10 d p-(5029622965732406225805523382174033/219753675339359603159040000000000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_Tail {d p : ℝ}
    (hd : (9087/20000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 11 d p := by
  let bx : ℝ := (d-(9087/20000:ℝ))/(429/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 11 d p-(39416614361133818913/7746444578816000000000:ℝ) =
    (41453961924384663717711323/96830557235200000000000000000:ℝ)*bx^0*(1-bx)^2*byv^0*(1-byv)^3 +
    (4253837629589548961102701/3873222289408000000000000000:ℝ)*bx^0*(1-bx)^2*byv^1*(1-byv)^2 +
    (5521643685972081740936591/6051909827200000000000000000:ℝ)*bx^0*(1-bx)^2*byv^2*(1-byv)^1 +
    (732950182448153441962047/3025954913600000000000000000:ℝ)*bx^0*(1-bx)^2*byv^3*(1-byv)^0 +
    (379488866419285566031673/619715566305280000000000000:ℝ)*bx^1*(1-bx)^1*byv^0*(1-byv)^3 +
    (181975584495876017488187/123943113261056000000000000:ℝ)*bx^1*(1-bx)^1*byv^1*(1-byv)^2 +
    (42593197060145597085311/38732222894080000000000000:ℝ)*bx^1*(1-bx)^1*byv^2*(1-byv)^1 +
    (590246875212006274119/2420763930880000000000000:ℝ)*bx^1*(1-bx)^1*byv^3*(1-byv)^0 +
    (2897219635725339160899/15864718497415168000000000:ℝ)*bx^2*(1-bx)^0*byv^0*(1-byv)^3 +
    (5791928485993588306173/15864718497415168000000000:ℝ)*bx^2*(1-bx)^0*byv^1*(1-byv)^2 +
    (180918415412120796189/991544906088448000000000:ℝ)*bx^2*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 11 d p-(39416614361133818913/7746444578816000000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_Antitone {d p : ℝ}
    (hd : (9087/20000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 12 d p := by
  let bx : ℝ := (d-(9087/20000:ℝ))/(429/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 12 d p-(82923486994592614403381/183128062782799669299200:ℝ) =
    (1466165855416131430293067167/234403920361983576702976000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (1044350291407815886552417/109876837669679801579520000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (372654397689524729118483/114455039239249793312000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (8932975053448872044706693/3000370180633389781798092800:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (104472649555105578786131/35160588054297536505446400:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 12 d p-(82923486994592614403381/183128062782799669299200:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem all_admissions_10 {d p : ℝ}
    (hd : (9087/20000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) {g : ℕ} (hg : g ≤ 12) :
    0 < admissionGuard 6 g d p := by
  interval_cases g
  · exact admission_10_D hd hp
  · exact admission_10_A hd hp
  · exact admission_10_C hd hp
  · exact admission_10_J hd hp
  · exact admission_10_Tlo hd hp
  · exact admission_10_Thi hd hp
  · exact admission_10_Rlo hd hp
  · exact admission_10_Rhi hd hp
  · exact admission_10_Mlo hd hp
  · exact admission_10_Mhi hd hp
  · exact admission_10_Width hd hp
  · exact admission_10_Tail hd hp
  · exact admission_10_Antitone hd hp

end Sil.Uneven.RoundedRows
end

/- Original module: Candidate.Uneven.MainCountAdmission10. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.MainCount
noncomputable section

theorem window10_admissible (S : Stage) (d p : ℝ)
    (ha : (window10 S).Available d p) : Admissible (window10 S).plane d p := by
  cases S
  · have hd := ha.1
    have hp := ha.2
    dsimp only [window10,Stage.deltaLo] at hd hp
    constructor
    · have hg := Sil.Uneven.WarmupRows.all_admissions_10 hd hp (g:=0) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_10 hd hp (g:=1) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_10 hd hp (g:=2) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_10 hd hp (g:=3) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_10 hd hp (g:=4) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_10 hd hp (g:=5) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_10 hd hp (g:=6) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_10 hd hp (g:=7) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_10 hd hp (g:=8) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_10 hd hp (g:=9) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_10 hd hp (g:=10) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_10 hd hp (g:=11) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_10 hd hp (g:=12) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
  · have hd := ha.1
    have hp := ha.2
    dsimp only [window10,Stage.deltaLo] at hd hp
    constructor
    · have hg := Sil.Uneven.RoundedRows.all_admissions_10 hd hp (g:=0) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_10 hd hp (g:=1) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_10 hd hp (g:=2) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_10 hd hp (g:=3) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_10 hd hp (g:=4) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_10 hd hp (g:=5) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_10 hd hp (g:=6) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_10 hd hp (g:=7) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_10 hd hp (g:=8) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_10 hd hp (g:=9) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_10 hd hp (g:=10) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_10 hd hp (g:=11) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_10 hd hp (g:=12) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window10,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
end
end OAI.SevenEighths.MainCount
end
