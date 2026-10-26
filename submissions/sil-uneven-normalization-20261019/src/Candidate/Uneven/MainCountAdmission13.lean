import Candidate.Uneven.RoundedAdmissionBase
import Candidate.Uneven.MainCountWindows
import Candidate.Uneven.WarmupAdmission13

/- Original module: Candidate.Uneven.RoundedAdmission13. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Count-admission arithmetic only; source moment theorems are separate. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.RoundedRows

theorem admission_13_D {d p : ℝ}
    (hd : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 0 d p := by
  let bx : ℝ := (d-(15/32:ℝ))/(3/256:ℝ)
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

theorem admission_13_A {d p : ℝ}
    (hd : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 1 d p := by
  let bx : ℝ := (d-(15/32:ℝ))/(3/256:ℝ)
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

theorem admission_13_C {d p : ℝ}
    (hd : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 2 d p := by
  let bx : ℝ := (d-(15/32:ℝ))/(3/256:ℝ)
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

theorem admission_13_J {d p : ℝ}
    (hd : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 3 d p := by
  let bx : ℝ := (d-(15/32:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 3 d p-(29731337247349/28504679413248:ℝ) =
    (6315218541613/228037435305984:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (9596657834101/228037435305984:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (45673201979/3167186601472:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (24202409848937/1824299482447872:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (24144753598937/1824299482447872:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 3 d p-(29731337247349/28504679413248:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_13_Tlo {d p : ℝ}
    (hd : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 4 d p := by
  let bx : ℝ := (d-(15/32:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 4 d p-(273303308779/1583593300736:ℝ) =
    (23851750882121/6486398159814656:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (15/4096:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (419474427785149/51891185278517248:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (12550041349493/1013499712471040:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 +
    (273303308779/63343732029440:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 4 d p-(273303308779/1583593300736:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_13_Thi {d p : ℝ}
    (hd : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 5 d p := by
  let bx : ℝ := (d-(15/32:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 5 d p-(2701630898759478723/32431990799073280000:ℝ) =
    (259840810726550517/32431990799073280000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (797407609749314551/48647986198609920000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (814574716752762551/97295972397219840000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (22443486838174207/48647986198609920000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 +
    (44150951345978039/97295972397219840000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 5 d p-(2701630898759478723/32431990799073280000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_13_Rlo {d p : ℝ}
    (hd : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 6 d p := by
  let bx : ℝ := (d-(15/32:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 6 d p-(2526700672142566968429535/9786171774975794526576384:ℝ) =
    (364689958004879397166966361/40084159590300854380856868864:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (242054882868268580013859123/13361386530100284793618956288:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (353010040677545131591417/39144687099903178106305536:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (24791982624993523444755324113/1603366383612034175234274754560:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (19809869092376357187723549019/534455461204011391744758251520:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (43568659417509091668263701/1565787483996127124252221440:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 +
    (18041759545328210002553/2899606451844679859726336:ℝ)*bx^1*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 6 d p-(2526700672142566968429535/9786171774975794526576384:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_13_Rhi {d p : ℝ}
    (hd : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 7 d p := by
  let bx : ℝ := (d-(15/32:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 7 d p-(1078221431393695802252237/2115929032427198816557056:ℝ) =
    (26272024991196575680114583/1083355664602725794077212672:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (87069057640232568410219/2115929032427198816557056:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (3978676868611423624547/235103225825244312950784:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (307324916678874536076106271/43334226584109031763088506880:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (598246979345214514089869/84637161297087952662282240:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 7 d p-(1078221431393695802252237/2115929032427198816557056:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_13_Mlo {d p : ℝ}
    (hd : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 8 d p := by
  let bx : ℝ := (d-(15/32:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 8 d p-(14578541585337085172347564753213853/4012428387417502941026713600000000000:ℝ) =
    (11152277772455522576080967585321819/18055927743378763234620211200000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (133741761311296381932561390885256403/108335566460272579407721267200000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (66824070282820546671690309748325489/108335566460272579407721267200000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (544851771896407753182011056757162829/160497135496700117641068544000000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (15430548913325036084579388421056386533/1444474219470301058769616896000000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (6056328419678449297873330162876751887/541677832301362897038606336000000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 +
    (421745336462801119329574456791581297/108335566460272579407721267200000000000:ℝ)*bx^1*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 8 d p-(14578541585337085172347564753213853/4012428387417502941026713600000000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_13_Mhi {d p : ℝ}
    (hd : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 9 d p := by
  let bx : ℝ := (d-(15/32:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 9 d p-(130337486012347511722674627437/13224556452669992603481600000000:ℝ) =
    (243871807467572878095001747177327/54167783230136289703860633600000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (28252075448478897111804725638243/2256990967922345404327526400000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (610014110904009995960114563817/52898225810679970413926400000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (5167052628329420787129490627/1469395161407776955942400000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (1874128783822506897315689443859527/2166711329205451588154425344000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (155967634866482231197625936002219/90279638716893816173101056000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (1825216209291122150321876203421/2115929032427198816557056000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 9 d p-(130337486012347511722674627437/13224556452669992603481600000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_13_Width {d p : ℝ}
    (hd : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 10 d p := by
  let bx : ℝ := (d-(15/32:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 10 d p-(3210104832793012996878232744215045499/211592903242719881655705600000000000000:ℝ) =
    (507925883929940192343525306044913488863/108335566460272579407721267200000000000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (52012885276655927858341355405243498429/4012428387417502941026713600000000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (10041692275625222759551341162400293259/846371612970879526622822400000000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (84400610999192162943743212915740629/23510322582524431295078400000000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (4234308806189566703539680446784462190663/4333422658410903176308850688000000000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (313163714534503295844949638544632448757/160497135496700117641068544000000000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (32976337138572266505191699989759434967/33854864518835181064912896000000000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 10 d p-(3210104832793012996878232744215045499/211592903242719881655705600000000000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_13_Tail {d p : ℝ}
    (hd : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 11 d p := by
  let bx : ℝ := (d-(15/32:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 11 d p-(71416911199076648623/25337492811776000000000:ℝ) =
    (300767759223032343041/202699942494208000000000:ℝ)*bx^0*(1-bx)^2*byv^0*(1-byv)^3 +
    (2503496878226451303619/608099827482624000000000:ℝ)*bx^0*(1-bx)^2*byv^1*(1-byv)^2 +
    (143772740885298840109/38006239217664000000000:ℝ)*bx^0*(1-bx)^2*byv^2*(1-byv)^1 +
    (29132288449870012177/25337492811776000000000:ℝ)*bx^0*(1-bx)^2*byv^3*(1-byv)^0 +
    (1473639760407474961613/810799769976832000000000:ℝ)*bx^1*(1-bx)^1*byv^0*(1-byv)^3 +
    (3903620718218350941309/810799769976832000000000:ℝ)*bx^1*(1-bx)^1*byv^1*(1-byv)^2 +
    (423362594652720493863/101349971247104000000000:ℝ)*bx^1*(1-bx)^1*byv^2*(1-byv)^1 +
    (14952071279094685097/12668746405888000000000:ℝ)*bx^1*(1-bx)^1*byv^3*(1-byv)^0 +
    (3921214528942190096817/12972796319629312000000000:ℝ)*bx^2*(1-bx)^0*byv^0*(1-byv)^3 +
    (23517328540142939909027/38918388958887936000000000:ℝ)*bx^2*(1-bx)^0*byv^1*(1-byv)^2 +
    (1469171374627192686697/4864798619860992000000000:ℝ)*bx^2*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 11 d p-(71416911199076648623/25337492811776000000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_13_Antitone {d p : ℝ}
    (hd : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 12 d p := by
  let bx : ℝ := (d-(15/32:ℝ))/(3/256:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 12 d p-(4436083909606361291523217/10579645162135994082785280:ℝ) =
    (107875425227028342814241581/5416778323013628970386063360:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (1437848413132544345813809/42318580648543976331141120:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (16557646586844287067487/1175516129126221564753920:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (244290688229650337195967329/43334226584109031763088506880:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (1900762904330194082514269/338548645188351810649128960:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 12 d p-(4436083909606361291523217/10579645162135994082785280:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem all_admissions_13 {d p : ℝ}
    (hd : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) {g : ℕ} (hg : g ≤ 12) :
    0 < admissionGuard 7 g d p := by
  interval_cases g
  · exact admission_13_D hd hp
  · exact admission_13_A hd hp
  · exact admission_13_C hd hp
  · exact admission_13_J hd hp
  · exact admission_13_Tlo hd hp
  · exact admission_13_Thi hd hp
  · exact admission_13_Rlo hd hp
  · exact admission_13_Rhi hd hp
  · exact admission_13_Mlo hd hp
  · exact admission_13_Mhi hd hp
  · exact admission_13_Width hd hp
  · exact admission_13_Tail hd hp
  · exact admission_13_Antitone hd hp

end Sil.Uneven.RoundedRows
end

/- Original module: Candidate.Uneven.MainCountAdmission13. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.MainCount
noncomputable section

theorem window13_admissible (S : Stage) (d p : ℝ)
    (ha : (window13 S).Available d p) : Admissible (window13 S).plane d p := by
  cases S
  · have hd := ha.1
    have hp := ha.2
    dsimp only [window13,Stage.deltaLo] at hd hp
    constructor
    · have hg := Sil.Uneven.WarmupRows.all_admissions_13 hd hp (g:=0) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_13 hd hp (g:=1) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_13 hd hp (g:=2) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_13 hd hp (g:=3) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_13 hd hp (g:=4) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_13 hd hp (g:=5) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_13 hd hp (g:=6) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_13 hd hp (g:=7) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_13 hd hp (g:=8) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_13 hd hp (g:=9) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_13 hd hp (g:=10) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_13 hd hp (g:=11) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_13 hd hp (g:=12) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
  · have hd := ha.1
    have hp := ha.2
    dsimp only [window13,Stage.deltaLo] at hd hp
    constructor
    · have hg := Sil.Uneven.RoundedRows.all_admissions_13 hd hp (g:=0) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_13 hd hp (g:=1) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_13 hd hp (g:=2) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_13 hd hp (g:=3) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_13 hd hp (g:=4) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_13 hd hp (g:=5) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_13 hd hp (g:=6) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_13 hd hp (g:=7) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_13 hd hp (g:=8) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_13 hd hp (g:=9) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_13 hd hp (g:=10) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_13 hd hp (g:=11) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_13 hd hp (g:=12) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window13,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
end
end OAI.SevenEighths.MainCount
end
