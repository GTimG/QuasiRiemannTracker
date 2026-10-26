/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Count-admission arithmetic only; source moment theorems are separate. -/
import Candidate.Uneven.WarmupAdmissionBase

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.WarmupRows

theorem admission_10_D {d p : ℝ}
    (hd : (4543/10000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 0 d p := by
  let bx : ℝ := (d-(4543/10000:ℝ))/(437/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 0 d p-(29837245/15134898:ℝ) =
    (15567449/1937266944:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 0 d p-(29837245/15134898:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_A {d p : ℝ}
    (hd : (4543/10000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 1 d p := by
  let bx : ℝ := (d-(4543/10000:ℝ))/(437/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 1 d p-(11134898/7567449:ℝ) =
    (31250/7567449:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 1 d p-(11134898/7567449:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_C {d p : ℝ}
    (hd : (4543/10000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 2 d p := by
  let bx : ℝ := (d-(4543/10000:ℝ))/(437/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 2 d p-(28024481/37837245:ℝ) =
    (2453191/1210791840:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 2 d p-(28024481/37837245:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_J {d p : ℝ}
    (hd : (4543/10000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 3 d p := by
  let bx : ℝ := (d-(4543/10000:ℝ))/(437/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 3 d p-(12531313003/11623601664:ℝ) =
    (579867109007/58118008320000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (775591418093/58118008320000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (8172925639/2421583680000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (9822310709/1487821012992:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (9811341959/1487821012992:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 3 d p-(12531313003/11623601664:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_Tlo {d p : ℝ}
    (hd : (4543/10000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 4 d p := by
  let bx : ℝ := (d-(4543/10000:ℝ))/(437/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 4 d p-(127315217183/756744900000:ℝ) =
    (5511772175833/3099627110400000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (4543/2560000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (138881018706787/49594033766400000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (5902003279057/1549813555200000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 +
    (12246698197/12107918400000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 4 d p-(127315217183/756744900000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_Thi {d p : ℝ}
    (hd : (4543/10000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 5 d p := by
  let bx : ℝ := (d-(4543/10000:ℝ))/(437/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 5 d p-(992119186502563/9918806753280000:ℝ) =
    (3855346539542239/2066418073600000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (11969101403825629/3099627110400000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (4120408817532847/2066418073600000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (174667864757/1239850844160000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 +
    (1379738937181/9918806753280000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 5 d p-(992119186502563/9918806753280000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_Rlo {d p : ℝ}
    (hd : (4543/10000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 6 d p := by
  let bx : ℝ := (d-(4543/10000:ℝ))/(437/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 6 d p-(2683180646040694291/10594262608006185000:ℝ) =
    (15473558623946242195363/3471527971391466700800000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (2058653028910441285063/231435198092764446720000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (120361829397695388569/27121312276495833600000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (66034029678918840237509/11108889508452693442560000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (148186867810950642950527/11108889508452693442560000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (85493200407809451751/9643133253865185280000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 +
    (249253535757309469/169508201728098960000:ℝ)*bx^1*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 6 d p-(2683180646040694291/10594262608006185000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_Rhi {d p : ℝ}
    (hd : (4543/10000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 7 d p := by
  let bx : ℝ := (d-(4543/10000:ℝ))/(437/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 7 d p-(48330817063382041/87961012788635136:ℝ) =
    (60705587643561684893/7818756692323123200000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (25829661602391656999/2199025319715878400000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (73081546908989453/18325210997632320000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (2251114119637200101/600480513970415861760:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (210697045948789061/56295048184726487040:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 7 d p-(48330817063382041/87961012788635136:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_Mlo {d p : ℝ}
    (hd : (4543/10000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 8 d p := by
  let bx : ℝ := (d-(4543/10000:ℝ))/(437/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 8 d p-(18505953800621935168829027/11259009636945297408000000000000:ℝ) =
    (134478121931068273140775721/351844051154540544000000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (1720297535222354731549360427/2251801927389059481600000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (1432712535562943684778274271/3753003212315099136000000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (46888840583844991267557093731/60048051397041586176000000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (488357569671073075780107373579/180144154191124758528000000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (34665173649201327646578102919/11259009636945297408000000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 +
    (1437159187221536778141418997/1251001070771699712000000000000:ℝ)*bx^1*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 8 d p-(18505953800621935168829027/11259009636945297408000000000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_Mhi {d p : ℝ}
    (hd : (4543/10000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 9 d p := by
  let bx : ℝ := (d-(4543/10000:ℝ))/(437/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 9 d p-(12492075552660646693609/733008439905292800000000:ℝ) =
    (816287979890874496463697059/586406751924234240000000000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (8460690983935217230948168879/2345627007696936960000000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (27845112935506329028333523/9162605498816160000000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (41944859295648404902239/50903363882312000000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (8316150965414219019366071/15012012849260396544000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (66469904600956902685930141/60048051397041586176000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (129707273517677825095997/234562700769693696000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 9 d p-(12492075552660646693609/733008439905292800000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_Width {d p : ℝ}
    (hd : (4543/10000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 10 d p := by
  let bx : ℝ := (d-(4543/10000:ℝ))/(437/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 10 d p-(322180864499294040772413997/14073762046181621760000000000:ℝ) =
    (22071023556518230702282331998171/15012012849260396544000000000000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (170305994822658157538552990544907/45036038547781189632000000000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (554795608822108239753951966559/175922025577270272000000000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (2469721508758613673224925361/2932033759621171200000000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (26209005570595547440446479561/42700836549007350169600000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (1413933017574692299545096544753/1152922586823198454579200000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (2758927624103537902934079601/4503603854778118963200000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 10 d p-(322180864499294040772413997/14073762046181621760000000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_Tail {d p : ℝ}
    (hd : (4543/10000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 11 d p := by
  let bx : ℝ := (d-(4543/10000:ℝ))/(437/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 11 d p-(52579820173829299/10332090368000000000:ℝ) =
    (251476925045265532011887/581180083200000000000000000:ℝ)*bx^0*(1-bx)^2*byv^0*(1-byv)^3 +
    (25850178263086044515069/23247203328000000000000000:ℝ)*bx^0*(1-bx)^2*byv^1*(1-byv)^2 +
    (33635999585899865946229/36323755200000000000000000:ℝ)*bx^0*(1-bx)^2*byv^2*(1-byv)^1 +
    (8962435987389042288661/36323755200000000000000000:ℝ)*bx^0*(1-bx)^2*byv^3*(1-byv)^0 +
    (4590142607475657880633/7439105064960000000000000:ℝ)*bx^1*(1-bx)^1*byv^0*(1-byv)^3 +
    (2205150356766150440927/1487821012992000000000000:ℝ)*bx^1*(1-bx)^1*byv^1*(1-byv)^2 +
    (258859313694619483453/232472033280000000000000:ℝ)*bx^1*(1-bx)^1*byv^2*(1-byv)^1 +
    (7218367571251581749/29059004160000000000000:ℝ)*bx^1*(1-bx)^1*byv^3*(1-byv)^0 +
    (7729181199256822279/42320242147328000000000:ℝ)*bx^2*(1-bx)^0*byv^0*(1-byv)^3 +
    (15451673065493753933/42320242147328000000000:ℝ)*bx^2*(1-bx)^0*byv^1*(1-byv)^2 +
    (241326687180377747/1322507567104000000000:ℝ)*bx^2*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 11 d p-(52579820173829299/10332090368000000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_10_Antitone {d p : ℝ}
    (hd : (4543/10000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 6 12 d p := by
  let bx : ℝ := (d-(4543/10000:ℝ))/(437/160000:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/256:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 6 12 d p-(24899074243962307/54975632992896960:ℝ) =
    (148151561080200290969/23456270076969369600000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (529264701752550563/54975632992896960000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (37992958527226751/11453256873520200000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (1787498917669746619/600480513970415861760:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (20905111446142573/7036881023090810880:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 6 12 d p-(24899074243962307/54975632992896960:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem all_admissions_10 {d p : ℝ}
    (hd : (4543/10000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ))
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

end Sil.Uneven.WarmupRows
