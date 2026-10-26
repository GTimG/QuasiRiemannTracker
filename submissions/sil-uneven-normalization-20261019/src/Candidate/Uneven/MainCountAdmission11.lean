import Candidate.Uneven.RoundedAdmissionBase
import Candidate.Uneven.MainCountWindows
import Candidate.Uneven.WarmupAdmission11

/- Original module: Candidate.Uneven.RoundedAdmission11. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Count-admission arithmetic only; source moment theorems are separate. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.RoundedRows

theorem admission_11_D {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 0 d p := by
  let bx : ℝ := (d-(117/256:ℝ))/(3/512:ℝ)
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

theorem admission_11_A {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 1 d p := by
  let bx : ℝ := (d-(117/256:ℝ))/(3/512:ℝ)
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

theorem admission_11_C {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 2 d p := by
  let bx : ℝ := (d-(117/256:ℝ))/(3/512:ℝ)
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

theorem admission_11_J {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 3 d p := by
  let bx : ℝ := (d-(117/256:ℝ))/(3/512:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 3 d p-(60695850948131/57009358826496:ℝ) =
    (37379440307015/1824299482447872:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (50478478726967/1824299482447872:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (45673201979/6334373202944:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (48439542130063/3648598964895744:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (48328448380063/3648598964895744:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 3 d p-(60695850948131/57009358826496:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_11_Tlo {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 4 d p := by
  let bx : ℝ := (d-(117/256:ℝ))/(3/512:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 4 d p-(10658829042381/63343732029440:ℝ) =
    (930218284402719/259455926392586240:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (117/32768:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (3003738672446343/518911852785172480:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (16076010808163/2026999424942080:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 +
    (273303308779/126687464058880:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 4 d p-(10658829042381/63343732029440:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_11_Thi {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 5 d p := by
  let bx : ℝ := (d-(117/256:ℝ))/(3/512:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 5 d p-(6182784229698608997/64863981598146560000:ℝ) =
    (259840810726550517/64863981598146560000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (806176168781955137/97295972397219840000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (831429667780139473/194591944794439680000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (31212045870814793/97295972397219840000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 +
    (61005902373354961/194591944794439680000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 5 d p-(6182784229698608997/64863981598146560000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_11_Rlo {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 6 d p := by
  let bx : ℝ := (d-(117/256:ℝ))/(3/512:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 6 d p-(19726477869416674077367349/78289374199806356212611072:ℝ) =
    (14359585373581515331613691647/1603366383612034175234274754560:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (9530892895269816216396887701/534455461204011391744758251520:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (13899794300126219063185519/1565787483996127124252221440:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (38923555051961378221304052967/3206732767224068350468549509120:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (29189459568185246419962959501/1068910922408022783489516503040:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (57247846390659724530978059/3131574967992254248504442880:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 +
    (18041759545328210002553/5799212903689359719452672:ℝ)*bx^1*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 6 d p-(19726477869416674077367349/78289374199806356212611072:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_11_Rhi {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 7 d p := by
  let bx : ℝ := (d-(117/256:ℝ))/(3/512:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 7 d p-(2263867138239900042367243/4231858064854397633114112:ℝ) =
    (694412501983165114618305809/43334226584109031763088506880:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (2070306613773053444216891/84637161297087952662282240:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (3978676868611423624547/470206451650488625901568:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (645268920997341738108134569/86668453168218063526177013760:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (1256097901282018666114891/169274322594175905324564480:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 7 d p-(2263867138239900042367243/4231858064854397633114112:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_11_Mlo {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 8 d p := by
  let bx : ℝ := (d-(117/256:ℝ))/(3/512:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 8 d p-(38289891517075653711891533371391291/160497135496700117641068544000000000000:ℝ) =
    (106481337147085686350786492503850089/144447421947030105876961689600000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (6381707071085144179361165565136686293/4333422658410903176308850688000000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (3187110005316608296466545040646183623/4333422658410903176308850688000000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (544851771896407753182011056757162829/320994270993400235282137088000000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (16667993434470308005508640864307642793/2888948438940602117539233792000000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (27932185523573013732203258398938565781/4333422658410903176308850688000000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 +
    (10285535328916219749624227981511299783/4333422658410903176308850688000000000000:ℝ)*bx^1*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 8 d p-(38289891517075653711891533371391291/160497135496700117641068544000000000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_11_Mhi {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 9 d p := by
  let bx : ℝ := (d-(117/256:ℝ))/(3/512:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 9 d p-(400185392989589384697845501803/26449112905339985206963200000000:ℝ) =
    (6206922128139177276479957781902953/2166711329205451588154425344000000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (675611690331311278521190546504261/90279638716893816173101056000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (13493411631455030825888189638979/2115929032427198816557056000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (5167052628329420787129490627/2938790322815553911884800000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (4533100741397946326475535120572353/4333422658410903176308850688000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (377107997589948903767818003481021/180559277433787632346202112000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (4411475036040783963693672928699/4231858064854397633114112000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 9 d p-(400185392989589384697845501803/26449112905339985206963200000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_11_Width {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 10 d p := by
  let bx : ℝ := (d-(117/256:ℝ))/(3/512:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 10 d p-(8699026162564214393237532237155087981/423185806485439763311411200000000000000:ℝ) =
    (13064680979148999473256220529864647812457/4333422658410903176308850688000000000000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (1255080337702787687190567293103295302683/160497135496700117641068544000000000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (223443085636680338383459573308264749833/33854864518835181064912896000000000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (84400610999192162943743212915740629/47020645165048862590156800000000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (10046635407289957956311109264717218261057/8666845316821806352617701376000000000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (742808978873841555892430008541483116963/320994270993400235282137088000000000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (78194817386924032890057200110277204273/67709729037670362129825792000000000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 10 d p-(8699026162564214393237532237155087981/423185806485439763311411200000000000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_11_Tail {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 11 d p := by
  let bx : ℝ := (d-(117/256:ℝ))/(3/512:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 11 d p-(458145813170568593503/101349971247104000000000:ℝ) =
    (11684083005093735270289/12972796319629312000000000:ℝ)*bx^0*(1-bx)^2*byv^0*(1-byv)^3 +
    (6064672696666864027277/2594559263925862400000000:ℝ)*bx^0*(1-bx)^2*byv^1*(1-byv)^2 +
    (3200383125115101184691/1621599539953664000000000:ℝ)*bx^0*(1-bx)^2*byv^2*(1-byv)^1 +
    (54405306358143234269/101349971247104000000000:ℝ)*bx^0*(1-bx)^2*byv^3*(1-byv)^0 +
    (652641302019061584529/518911852785172480000000:ℝ)*bx^1*(1-bx)^1*byv^0*(1-byv)^3 +
    (119035943658598481820299/38918388958887936000000000:ℝ)*bx^1*(1-bx)^1*byv^1*(1-byv)^2 +
    (11409412524422786911681/4864798619860992000000000:ℝ)*bx^1*(1-bx)^1*byv^2*(1-byv)^1 +
    (27588580233231296143/50674985623552000000000:ℝ)*bx^1*(1-bx)^1*byv^3*(1-byv)^0 +
    (18119913134227878037377/51891185278517248000000000:ℝ)*bx^2*(1-bx)^0*byv^0*(1-byv)^3 +
    (108630747106537063802387/155673555835551744000000000:ℝ)*bx^2*(1-bx)^0*byv^1*(1-byv)^2 +
    (6783730260924793945657/19459194479443968000000000:ℝ)*bx^2*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 11 d p-(458145813170568593503/101349971247104000000000:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem admission_11_Antitone {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 < admissionGuard 7 12 d p := by
  let bx : ℝ := (d-(117/256:ℝ))/(3/512:ℝ)
  let byv : ℝ := (p-(63/128:ℝ))/(1/128:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : admissionGuard 7 12 d p-(9319224277057518333868583/21159290324271988165570560:ℝ) =
    (113228897947332290029627363/8666845316821806352617701376:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (6799005054757051424197907/338548645188351810649128960:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (16557646586844287067487/2351032258252443129507840:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (513576265886746494978308311/86668453168218063526177013760:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (3995985708783942164399611/677097290376703621298257920:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 12 d p-(9319224277057518333868583/21159290324271988165570560:ℝ) := by
    rw [hid]
    positivity
  linarith only [hh]

theorem all_admissions_11 {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ))
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) {g : ℕ} (hg : g ≤ 12) :
    0 < admissionGuard 7 g d p := by
  interval_cases g
  · exact admission_11_D hd hp
  · exact admission_11_A hd hp
  · exact admission_11_C hd hp
  · exact admission_11_J hd hp
  · exact admission_11_Tlo hd hp
  · exact admission_11_Thi hd hp
  · exact admission_11_Rlo hd hp
  · exact admission_11_Rhi hd hp
  · exact admission_11_Mlo hd hp
  · exact admission_11_Mhi hd hp
  · exact admission_11_Width hd hp
  · exact admission_11_Tail hd hp
  · exact admission_11_Antitone hd hp

end Sil.Uneven.RoundedRows
end

/- Original module: Candidate.Uneven.MainCountAdmission11. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.MainCount
noncomputable section

theorem window11_admissible (S : Stage) (d p : ℝ)
    (ha : (window11 S).Available d p) : Admissible (window11 S).plane d p := by
  cases S
  · have hd := ha.1
    have hp := ha.2
    dsimp only [window11,Stage.deltaLo] at hd hp
    constructor
    · have hg := Sil.Uneven.WarmupRows.all_admissions_11 hd hp (g:=0) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_11 hd hp (g:=1) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_11 hd hp (g:=2) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_11 hd hp (g:=3) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_11 hd hp (g:=4) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_11 hd hp (g:=5) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_11 hd hp (g:=6) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_11 hd hp (g:=7) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_11 hd hp (g:=8) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_11 hd hp (g:=9) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_11 hd hp (g:=10) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_11 hd hp (g:=11) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.WarmupRows.all_admissions_11 hd hp (g:=12) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.WarmupRows.admissionGuard,
        Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda] <;> ring_nf <;> simp
  · have hd := ha.1
    have hp := ha.2
    dsimp only [window11,Stage.deltaLo] at hd hp
    constructor
    · have hg := Sil.Uneven.RoundedRows.all_admissions_11 hd hp (g:=0) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_11 hd hp (g:=1) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_11 hd hp (g:=2) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_11 hd hp (g:=3) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_11 hd hp (g:=4) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_11 hd hp (g:=5) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_11 hd hp (g:=6) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_11 hd hp (g:=7) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_11 hd hp (g:=8) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_11 hd hp (g:=9) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_11 hd hp (g:=10) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_11 hd hp (g:=11) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
    · have hg := Sil.Uneven.RoundedRows.all_admissions_11 hd hp (g:=12) (by norm_num)
      convert hg using 1 <;> norm_num [guardD,guardA,guardC,guardJ,guardTLo,guardTHi,guardRLo,guardRHi,guardMLo,guardMHi,guardWidth,guardTail,guardMonotone,Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineC,Target830.Count.affineU,Target830.Count.affineJ,Target830.Count.affineN,Target830.Count.affineTNum,Target830.Count.affineRNum,Target830.Count.affineMNum,Target830.Count.affineAntitone,Target830.Count.affineUPrime,Target830.Count.affineJPrime,mHi,Target830.Count.mHi,Target830.kappa0,Target830.widthLower,Target830.widthUpper,Target830.plainLower,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,Stage.aPlane,Stage.cPlane,window11,Sil.Uneven.RoundedRows.admissionGuard,
        Sil.Uneven.RoundedRows.planeB,Sil.Uneven.RoundedRows.planeLambda] <;> ring_nf <;> simp
end
end OAI.SevenEighths.MainCount
end
