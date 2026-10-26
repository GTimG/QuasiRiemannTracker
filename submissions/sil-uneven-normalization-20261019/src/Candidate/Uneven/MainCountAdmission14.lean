import Candidate.Uneven.RoundedAdmissionBase
import Candidate.Uneven.MainCountWindows
import Candidate.Uneven.WarmupAdmission14

/- Original module: Candidate.Uneven.RoundedAdmission14. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Count-admission arithmetic only; source moment theorems are separate. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.RoundedRows

theorem admission_14_D {d p : ℝ}
    (hd : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 0 d p := by
  let bx : ℝ := (d-(123/256:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 0 d p-(72788669965/37115467986:ℝ) =
    (38557733993/2375389951104:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 0 d p-(72788669965/37115467986:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_14_A {d p : ℝ}
    (hd : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 1 d p := by
  let bx : ℝ := (d-(123/256:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 1 d p-(27115467986/18557733993:ℝ) =
    (156250000/18557733993:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 1 d p-(27115467986/18557733993:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_14_C {d p : ℝ}
    (hd : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 2 d p := by
  let bx : ℝ := (d-(123/256:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 2 d p-(273303308779/371154679860:ℝ) =
    (97851371081/23753899511040:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 2 d p-(273303308779/371154679860:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_14_J {d p : ℝ}
    (hd : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 3 d p := by
  let bx : ℝ := (d-(123/256:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 3 d p-(14660139214769/14252339706624:ℝ) =
    (50510174188841/1824299482447872:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (76760282278745/1824299482447872:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (45673201979/3167186601472:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (12095417852437/912149741223936:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (12065886602437/912149741223936:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 3 d p-(14660139214769/14252339706624:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_14_Tlo {d p : ℝ}
    (hd : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 4 d p := by
  let bx : ℝ := (d-(123/256:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 4 d p-(11205435659939/63343732029440:ℝ) =
    (977921786166961/259455926392586240:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (123/32768:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (1060611944903933/129727963196293120:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (6321415009729/506749856235520:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 +
    (273303308779/63343732029440:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 4 d p-(11205435659939/63343732029440:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_14_Thi {d p : ℝ}
    (hd : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 5 d p := by
  let bx : ℝ := (d-(123/256:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 5 d p-(1220895044016464103/16215995399536640000:ℝ) =
    (259840810726550517/32431990799073280000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (400982959508912879/24323993099304960000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (82367338352562959/9729597239721984000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (13500898053342707/24323993099304960000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 +
    (26624809059422539/48647986198609920000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 5 d p-(1220895044016464103/16215995399536640000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_14_Rlo {d p : ℝ}
    (hd : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 6 d p := by
  let bx : ℝ := (d-(123/256:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 6 d p-(20700732884864397417505211/78289374199806356212611072:ℝ) =
    (14815611266808836441743617233/1603366383612034175234274754560:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (265770209032207302289509247/14444742194703010587696168960:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (14341008954077391464127841/1565787483996127124252221440:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (12509997785803591999910143453/801683191806017087617137377280:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (9980585755918642085940513119/267227730602005695872379125760:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (21894633372242338934367431/782893741998063562126110720:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 +
    (18041759545328210002553/2899606451844679859726336:ℝ)*bx^1*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 6 d p-(20700732884864397417505211/78289374199806356212611072:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_14_Rhi {d p : ℝ}
    (hd : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 7 d p := by
  let bx : ℝ := (d-(123/256:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 7 d p-(521206669788096494815657/1057964516213599408278528:ℝ) =
    (1040674637101332138552609311/43334226584109031763088506880:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (3462894324745439523763709/84637161297087952662282240:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (3978676868611423624547/235103225825244312950784:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (148559277066171823712066131/21667113292054515881544253440:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (289189499240675650722409/42318580648543976331141120:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 7 d p-(521206669788096494815657/1057964516213599408278528:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_14_Mlo {d p : ℝ}
    (hd : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 8 d p := by
  let bx : ℝ := (d-(123/256:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 8 d p-(1127993435309891160075913646885716949/160497135496700117641068544000000000000:ℝ) =
    (14391021442440534973301797772259803/28889484389406021175392337920000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (4317633833818566375243745705683825947/4333422658410903176308850688000000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (2158815617309035437268679739219855497/4333422658410903176308850688000000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (544851771896407753182011056757162829/160497135496700117641068544000000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (15257917763650621027158000902843631163/1444474219470301058769616896000000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (47418590738794305480927931373287584923/4333422658410903176308850688000000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 +
    (16355666264508258343584045620950087817/4333422658410903176308850688000000000000:ℝ)*bx^1*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 8 d p-(1127993435309891160075913646885716949/160497135496700117641068544000000000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_14_Mhi {d p : ℝ}
    (hd : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 9 d p := by
  let bx : ℝ := (d-(123/256:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 9 d p-(41917006178691362319254605897/6612278226334996301740800000000:ℝ) =
    (9493257907451937613185351142808647/2166711329205451588154425344000000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (1108358775320161070681333648370859/90279638716893816173101056000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (24146883563674219950721275712061/2115929032427198816557056000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (5167052628329420787129490627/1469395161407776955942400000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (806257196285764693350485349787547/1083355664602725794077212672000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (67121696123743708703385279421679/45139819358446908086550528000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (785767668402471131319284681401/1057964516213599408278528000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 9 d p-(41917006178691362319254605897/6612278226334996301740800000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_14_Width {d p : ℝ}
    (hd : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 10 d p := by
  let bx : ℝ := (d-(123/256:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 10 d p-(1225249666900141765192271913986689919/105796451621359940827852800000000000000:ℝ) =
    (19791029425560666177330429451413774927943/4333422658410903176308850688000000000000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (2041688227797958792932810639059000530677/160497135496700117641068544000000000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (397586976655082410422162379785758952247/33854864518835181064912896000000000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (84400610999192162943743212915740629/23510322582524431295078400000000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (1854151437276312593564548828200848782043/2166711329205451588154425344000000000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (137168265633112487222053030696946521137/80248567748350058820534272000000000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (14447811384322883272650216639753328427/16927432259417590532456448000000000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 10 d p-(1225249666900141765192271913986689919/105796451621359940827852800000000000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_14_Tail {d p : ℝ}
    (hd : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 11 d p := by
  let bx : ℝ := (d-(123/256:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 11 d p-(10185228633141980103/6334373202944000000000:ℝ) =
    (19627324822194658940849/12972796319629312000000000:ℝ)*bx^0*(1-bx)^2*byv^0*(1-byv)^3 +
    (32974464235883031901063/7783677791777587200000000:ℝ)*bx^0*(1-bx)^2*byv^1*(1-byv)^2 +
    (19138545454536220136233/4864798619860992000000000:ℝ)*bx^0*(1-bx)^2*byv^2*(1-byv)^1 +
    (30675996666508728211/25337492811776000000000:ℝ)*bx^0*(1-bx)^2*byv^3*(1-byv)^0 +
    (5879710633938524672381/3243199079907328000000000:ℝ)*bx^1*(1-bx)^1*byv^0*(1-byv)^3 +
    (47351376241158838411463/9729597239721984000000000:ℝ)*bx^1*(1-bx)^1*byv^1*(1-byv)^2 +
    (5223507278749060485109/1216199654965248000000000:ℝ)*bx^1*(1-bx)^1*byv^2*(1-byv)^1 +
    (7861962693707021557/6334373202944000000000:ℝ)*bx^1*(1-bx)^1*byv^3*(1-byv)^0 +
    (870908166564025103577/3243199079907328000000000:ℝ)*bx^2*(1-bx)^0*byv^0*(1-byv)^3 +
    (1741709838114597691529/3243199079907328000000000:ℝ)*bx^2*(1-bx)^0*byv^1*(1-byv)^2 +
    (108846777089573526619/405399884988416000000000:ℝ)*bx^2*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 11 d p-(10185228633141980103/6334373202944000000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_14_Antitone {d p : ℝ}
    (hd : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 12 d p := by
  let bx : ℝ := (d-(123/256:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 12 d p-(2143532545162381353957917/5289822581067997041392640:ℝ) =
    (854671772007078135651808097/43334226584109031763088506880:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (11437967338352503433386781/338548645188351810649128960:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (16557646586844287067487/1175516129126221564753920:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (117979529210250865166921389/21667113292054515881544253440:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (917971468811171374695289/169274322594175905324564480:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 12 d p-(2143532545162381353957917/5289822581067997041392640:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem all_admissions_14 {d p : ℝ}
    (hd : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) {g : ℕ} (hg : g ≤ 12) :
    0 < admissionGuard 7 g d p := by
  interval_cases g
  · exact admission_14_D hd hp
  · exact admission_14_A hd hp
  · exact admission_14_C hd hp
  · exact admission_14_J hd hp
  · exact admission_14_Tlo hd hp
  · exact admission_14_Thi hd hp
  · exact admission_14_Rlo hd hp
  · exact admission_14_Rhi hd hp
  · exact admission_14_Mlo hd hp
  · exact admission_14_Mhi hd hp
  · exact admission_14_Width hd hp
  · exact admission_14_Tail hd hp
  · exact admission_14_Antitone hd hp

end Sil.Uneven.RoundedRows
end

/- Original module: Candidate.Uneven.MainCountAdmission14. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.MainCount
noncomputable section

theorem window14_admissible (S : Stage) (d p : ℝ)
    (ha : (window14 S).Available d p) : Admissible (window14 S).plane d p := by
  cases S
  · have hd := ha.1
    have hp := ha.2
    dsimp only [window14,Stage.deltaLo] at hd hp
    constructor
    · have hg := Sil.Uneven.WarmupRows.all_admissions_14 hd hp (g:=0) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_14 hd hp (g:=1) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_14 hd hp (g:=2) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_14 hd hp (g:=3) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_14 hd hp (g:=4) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_14 hd hp (g:=5) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_14 hd hp (g:=6) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_14 hd hp (g:=7) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_14 hd hp (g:=8) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_14 hd hp (g:=9) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_14 hd hp (g:=10) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_14 hd hp (g:=11) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_14 hd hp (g:=12) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
  · have hd := ha.1
    have hp := ha.2
    dsimp only [window14,Stage.deltaLo] at hd hp
    constructor
    · have hg := Sil.Uneven.RoundedRows.all_admissions_14 hd hp (g:=0) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_14 hd hp (g:=1) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_14 hd hp (g:=2) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_14 hd hp (g:=3) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_14 hd hp (g:=4) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_14 hd hp (g:=5) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_14 hd hp (g:=6) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_14 hd hp (g:=7) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_14 hd hp (g:=8) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_14 hd hp (g:=9) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_14 hd hp (g:=10) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_14 hd hp (g:=11) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_14 hd hp (g:=12) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window14,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
end
end OAI.SevenEighths.MainCount
end
