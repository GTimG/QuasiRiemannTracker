import Candidate.Uneven.RoundedAdmissionBase
import Candidate.Uneven.MainCountWindows
import Candidate.Uneven.WarmupAdmission12

/- Original module: Candidate.Uneven.RoundedAdmission12. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Count-admission arithmetic only; source moment theorems are separate. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.RoundedRows

theorem admission_12_D {d p : ℝ}
    (hd : (237/512:ℝ) ≤ d ∧ d ≤ (15/32:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 0 d p := by
  let bx : ℝ := (d-(237/512:ℝ))/(3/512:ℝ)
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

theorem admission_12_A {d p : ℝ}
    (hd : (237/512:ℝ) ≤ d ∧ d ≤ (15/32:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 1 d p := by
  let bx : ℝ := (d-(237/512:ℝ))/(3/512:ℝ)
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

theorem admission_12_C {d p : ℝ}
    (hd : (237/512:ℝ) ≤ d ∧ d ≤ (15/32:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 2 d p := by
  let bx : ℝ := (d-(237/512:ℝ))/(3/512:ℝ)
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

theorem admission_12_J {d p : ℝ}
    (hd : (237/512:ℝ) ≤ d ∧ d ≤ (15/32:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 3 d p := by
  let bx : ℝ := (d-(237/512:ℝ))/(3/512:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 3 d p-(3767799508145/3563084926656:ℝ) =
    (74747306469967/3648598964895744:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (100943977059871/3648598964895744:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (45673201979/6334373202944:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (3026747999125/228037435305984:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (3019716749125/228037435305984:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 3 d p-(3767799508145/3563084926656:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_12_Tlo {d p : ℝ}
    (hd : (237/512:ℝ) ≤ d ∧ d ≤ (15/32:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 4 d p := by
  let bx : ℝ := (d-(237/512:ℝ))/(3/512:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 4 d p-(21590961393541/126687464058880:ℝ) =
    (1884288319687559/518911852785172480:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (237/65536:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (189224401458029/32431990799073280:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (1010549967383/126687464058880:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 +
    (273303308779/126687464058880:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 4 d p-(21590961393541/126687464058880:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_12_Thi {d p : ℝ}
    (hd : (237/512:ℝ) ≤ d ∧ d ≤ (15/32:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 5 d p := by
  let bx : ℝ := (d-(237/512:ℝ))/(3/512:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 5 d p-(74036792737150731/810799769976832000:ℝ) =
    (259840810726550517/64863981598146560000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (101341809756308293/12161996549652480000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (52533020909562907/12161996549652480000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (17885177569663/48647986198609920:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 +
    (35052284573111/97295972397219840:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 5 d p-(74036792737150731/810799769976832000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_12_Rlo {d p : ℝ}
    (hd : (237/512:ℝ) ≤ d ∧ d ≤ (15/32:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 6 d p := by
  let bx : ℝ := (d-(237/512:ℝ))/(3/512:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 6 d p-(39940083246557209824803629/156578748399612712425222144:ℝ) =
    (28947183693776691218292346087/3206732767224068350468549509120:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (19213088210000559416951252621/1068910922408022783489516503040:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (28020195927228024326842199/3131574967992254248504442880:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (489394599982187984704612697/40084159590300854380856868864:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (366759524845577167551505459/13361386530100284793618956288:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (2873422685881765536572461/156578748399612712425222144:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 +
    (18041759545328210002553/5799212903689359719452672:ℝ)*bx^1*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 6 d p-(39940083246557209824803629/156578748399612712425222144:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_12_Rhi {d p : ℝ}
    (hd : (237/512:ℝ) ≤ d ∧ d ≤ (15/32:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 7 d p := by
  let bx : ℝ := (d-(237/512:ℝ))/(3/512:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 7 d p-(139253690401399826859145/264491129053399852069632:ℝ) =
    (1378618641419799340584637609/86668453168218063526177013760:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (4120745246682243675788731/169274322594175905324564480:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (3978676868611423624547/470206451650488625901568:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (7938281980635135618202007/1083355664602725794077212672:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (15452874005226943168373/2115929032427198816557056:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 7 d p-(139253690401399826859145/264491129053399852069632:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_12_Mlo {d p : ℝ}
    (hd : (237/512:ℝ) ≤ d ∧ d ≤ (15/32:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 8 d p := by
  let bx : ℝ := (d-(237/512:ℝ))/(3/512:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 8 d p-(621431554930559060605794123499945411/320994270993400235282137088000000000000:ℝ) =
    (195699559326729866959434233186424641/288894843894060211753923379200000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (11731377523536999456663621200546942413/8666845316821806352617701376000000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (5860072816629430163334157430579203183/8666845316821806352617701376000000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (544851771896407753182011056757162829/320994270993400235282137088000000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (16495362284795892948087253346094887423/2888948438940602117539233792000000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (54832334428512738562347806868150701389/8666845316821806352617701376000000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 +
    (20056923463828653069649523312309435503/8666845316821806352617701376000000000000:ℝ)*bx^1*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 8 d p-(621431554930559060605794123499945411/320994270993400235282137088000000000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_12_Mhi {d p : ℝ}
    (hd : (237/512:ℝ) ≤ d ∧ d ≤ (15/32:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 9 d p := by
  let bx : ℝ := (d-(237/512:ℝ))/(3/512:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 9 d p-(4421023991682807470171001077/330613911316749815087040000000:ℝ) =
    (12152229865027377042345196819521473/4333422658410903176308850688000000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (1329499138043627743251525715849661/180559277433787632346202112000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (26733142390423881764093072437339/4231858064854397633114112000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (5167052628329420787129490627/2938790322815553911884800000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (53393579376837110198260204703599/54167783230136289703860633600000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (4442296937136926124712032829027/2256990967922345404327526400000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (51972427044432550950129576101/52898225810679970413926400000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 9 d p-(4421023991682807470171001077/330613911316749815087040000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_12_Width {d p : ℝ}
    (hd : (237/512:ℝ) ≤ d ∧ d ≤ (15/32:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 10 d p := by
  let bx : ℝ := (d-(237/512:ℝ))/(3/512:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 10 d p-(99242758294643561584298041511417779/5289822581067997041392640000000000000:ℝ) =
    (25603356026661057430101858269346530998337/8666845316821806352617701376000000000000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (2471333492137297052980291009055851198883/320994270993400235282137088000000000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (442805456903434176807027879906276721553/67709729037670362129825792000000000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (84400610999192162943743212915740629/47020645165048862590156800000000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (119007868445662705498756580929180670431/108335566460272579407721267200000000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (8799772445069540431144830392384296381/4012428387417502941026713600000000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (926426287712469161627074167500305327/846371612970879526622822400000000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 10 d p-(99242758294643561584298041511417779/5289822581067997041392640000000000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_12_Tail {d p : ℝ}
    (hd : (237/512:ℝ) ≤ d ∧ d ≤ (15/32:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 11 d p := by
  let bx : ℝ := (d-(237/512:ℝ))/(3/512:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 11 d p-(62843249780591663/15835933007360000000:ℝ) =
    (46765808596516236592513/51891185278517248000000000:ℝ)*bx^0*(1-bx)^2*byv^0*(1-byv)^3 +
    (366443806267132290798611/155673555835551744000000000:ℝ)*bx^0*(1-bx)^2*byv^1*(1-byv)^2 +
    (7802072531199839464037/3891838895888793600000000:ℝ)*bx^0*(1-bx)^2*byv^2*(1-byv)^1 +
    (55949014574781950303/101349971247104000000000:ℝ)*bx^0*(1-bx)^2*byv^3*(1-byv)^0 +
    (403170707872387942543/324319907990732800000000:ℝ)*bx^1*(1-bx)^1*byv^0*(1-byv)^3 +
    (197502221713726992467/64863981598146560000000:ℝ)*bx^1*(1-bx)^1*byv^1*(1-byv)^2 +
    (95730282783660072677/40539988498841600000000:ℝ)*bx^1*(1-bx)^1*byv^2*(1-byv)^1 +
    (354505429269383177/633437320294400000000:ℝ)*bx^1*(1-bx)^1*byv^3*(1-byv)^0 +
    (108335122598515593/324319907990732800000:ℝ)*bx^2*(1-bx)^0*byv^0*(1-byv)^3 +
    (649555375737296683/972959723972198400000:ℝ)*bx^2*(1-bx)^0*byv^1*(1-byv)^2 +
    (40567817154828113/121619965496524800000:ℝ)*bx^2*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 11 d p-(62843249780591663/15835933007360000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_12_Antitone {d p : ℝ}
    (hd : (237/512:ℝ) ≤ d ∧ d ≤ (15/32:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 12 d p := by
  let bx : ℝ := (d-(237/512:ℝ))/(3/512:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 12 d p-(114627568222198996878265/264491129053399852069632:ℝ) =
    (1123957349664174293434149079/86668453168218063526177013760:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (13533190142806251515272123/677097290376703621298257920:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (16557646586844287067487/2351032258252443129507840:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (6315557950969973601452297/1083355664602725794077212672:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (49139571775951135390949/8463716129708795266228224:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 12 d p-(114627568222198996878265/264491129053399852069632:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem all_admissions_12 {d p : ℝ}
    (hd : (237/512:ℝ) ≤ d ∧ d ≤ (15/32:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) {g : ℕ} (hg : g ≤ 12) :
    0 < admissionGuard 7 g d p := by
  interval_cases g
  · exact admission_12_D hd hp
  · exact admission_12_A hd hp
  · exact admission_12_C hd hp
  · exact admission_12_J hd hp
  · exact admission_12_Tlo hd hp
  · exact admission_12_Thi hd hp
  · exact admission_12_Rlo hd hp
  · exact admission_12_Rhi hd hp
  · exact admission_12_Mlo hd hp
  · exact admission_12_Mhi hd hp
  · exact admission_12_Width hd hp
  · exact admission_12_Tail hd hp
  · exact admission_12_Antitone hd hp

end Sil.Uneven.RoundedRows
end

/- Original module: Candidate.Uneven.MainCountAdmission12. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.MainCount
noncomputable section

theorem window12_admissible (S : Stage) (d p : ℝ)
    (ha : (window12 S).Available d p) : Admissible (window12 S).plane d p := by
  cases S
  · have hd := ha.1
    have hp := ha.2
    dsimp only [window12,Stage.deltaLo] at hd hp
    constructor
    · have hg := Sil.Uneven.WarmupRows.all_admissions_12 hd hp (g:=0) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_12 hd hp (g:=1) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_12 hd hp (g:=2) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_12 hd hp (g:=3) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_12 hd hp (g:=4) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_12 hd hp (g:=5) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_12 hd hp (g:=6) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_12 hd hp (g:=7) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_12 hd hp (g:=8) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_12 hd hp (g:=9) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_12 hd hp (g:=10) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_12 hd hp (g:=11) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_12 hd hp (g:=12) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
  · have hd := ha.1
    have hp := ha.2
    dsimp only [window12,Stage.deltaLo] at hd hp
    constructor
    · have hg := Sil.Uneven.RoundedRows.all_admissions_12 hd hp (g:=0) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_12 hd hp (g:=1) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_12 hd hp (g:=2) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_12 hd hp (g:=3) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_12 hd hp (g:=4) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_12 hd hp (g:=5) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_12 hd hp (g:=6) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_12 hd hp (g:=7) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_12 hd hp (g:=8) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_12 hd hp (g:=9) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_12 hd hp (g:=10) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_12 hd hp (g:=11) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_12 hd hp (g:=12) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window12,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
end
end OAI.SevenEighths.MainCount
end
