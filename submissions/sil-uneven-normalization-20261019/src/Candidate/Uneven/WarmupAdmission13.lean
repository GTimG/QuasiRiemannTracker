/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Count-admission arithmetic only; source moment theorems are separate. -/
import Candidate.Uneven.WarmupAdmissionBase

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.WarmupRows

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
  have hid : admissionGuard 7 0 d p-(145870295/74348118:ℝ) =
    (77174059/4758279552:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 0 d p-(145870295/74348118:ℝ) := by
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
  have hid : admissionGuard 7 1 d p-(54348118/37174059:ℝ) =
    (312500/37174059:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 1 d p-(54348118/37174059:ℝ) := by
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
  have hid : admissionGuard 7 2 d p-(27386650/37174059:ℝ) =
    (9787409/2379139776:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 2 d p-(27386650/37174059:ℝ) := by
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
  have hid : admissionGuard 7 3 d p-(59585305487/57099354624:ℝ) =
    (12650416619/456794836992:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (19225950863/456794836992:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (91522177/6344372736:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (48463938031/3654358695936:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (48348625531/3654358695936:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 3 d p-(59585305487/57099354624:ℝ) := by
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
  have hid : admissionGuard 7 4 d p-(68466625/396523296:ℝ) =
    (11944635925/3248318840832:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (15/4096:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (210121732985/25986550726656:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (5029627619/406039855104:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 +
    (13693325/3172186368:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 4 d p-(68466625/396523296:ℝ) := by
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
  have hid : admissionGuard 7 5 d p-(451196881851577/5413864734720000:ℝ) =
    (14464310161061/1804621578240000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (399522139329647/24362391306240000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (9491830200829/1133134479360000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (11267560822229/24362391306240000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 +
    (22166935827583/48724782612480000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 5 d p-(451196881851577/5413864734720000:ℝ) := by
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
  have hid : admissionGuard 7 6 d p-(2537000632359120025/9817093346652057024:ℝ) =
    (182972574325942666825/20105407173943412785152:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (121444618127099741845/6701802391314470928384:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (5667658702064780155/628293974185731649536:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (2488596440699611219325/160843257391547302281216:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (1988676491610933965369/53614419130515767427072:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (139981357489362412871/5026351793485853196288:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 +
    (1393812403398955/223751415308308992:ℝ)*bx^1*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 6 d p-(2537000632359120025/9817093346652057024:ℝ) := by
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
  have hid : admissionGuard 7 7 d p-(541308775823117125/1061307388827249408:ℝ) =
    (26367287814990084785/1086778766159103393792:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (699208506232872175/16980918221235990528:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (1997449357280875/117923043203027712:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (61623809139327587221/8694230129272827150336:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (959673650058589355/135847345769887924224:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 7 d p-(541308775823117125/1061307388827249408:ℝ) := by
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
  have hid : admissionGuard 7 8 d p-(4890155024574796455555719/1341702180443337523200000000:ℝ) =
    (932511904741586215804253/1509414952998754713600000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (134196616629371212943958107/108677876615910339379200000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (67051725677919167229645641/108677876615910339379200000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (750047296977571749060269/220856325998903296000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (5161731054027731831241897109/483012784959601508352000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (6077746489229341958462122903/543389383079551696896000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 +
    (423235199694558063951013193/108677876615910339379200000000:ℝ)*bx^1*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 8 d p-(4890155024574796455555719/1341702180443337523200000000:ℝ) := by
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
  have hid : admissionGuard 7 9 d p-(523550751707113798127453/53065369441362470400000000:ℝ) =
    (244743139836920482232704747/54338938307955169689600000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (113413386571768137889806467/9056489717992528281600000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (2448834134141284431882173/212261477765449881600000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (20742854275523012228563/5896152160151385600000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (1880609322240617702536898947/2173557532318206787584000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (626030997357344436478267211/362259588719701131264000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (7326185255379393966330449/8490459110617995264000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 9 d p-(523550751707113798127453/53065369441362470400000000:ℝ) := by
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
  have hid : admissionGuard 7 10 d p-(25836501008952422408375775953/1698091822123599052800000000000:ℝ) =
    (4078768829326293487402831001561/869423012927282715033600000000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (3759034056315058302094325197967/289807670975760905011200000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (80634775006570672342093420673/6792367288494396211200000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (677722505909329173410572063/188676869124844339200000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (34011043518818670871598857986161/34776920517091308601344000000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (22638783582860982645739594286711/11592306839030436200448000000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (264876421433088166161935230949/271694691539775848448000000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 10 d p-(25836501008952422408375775953/1698091822123599052800000000000:ℝ) := by
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
  have hid : admissionGuard 7 11 d p-(143123213847058249/50754981888000000000:ℝ) =
    (1205623837802118791/812079710208000000000:ℝ)*bx^0*(1-bx)^2*byv^0*(1-byv)^3 +
    (10035346639999285369/2436239130624000000000:ℝ)*bx^0*(1-bx)^2*byv^1*(1-byv)^2 +
    (288162245054205617/76132472832000000000:ℝ)*bx^0*(1-bx)^2*byv^2*(1-byv)^1 +
    (58390320664572151/50754981888000000000:ℝ)*bx^0*(1-bx)^2*byv^3*(1-byv)^0 +
    (5906976734755456363/3248318840832000000000:ℝ)*bx^1*(1-bx)^1*byv^0*(1-byv)^3 +
    (1738621829972623951/360924315648000000000:ℝ)*bx^1*(1-bx)^1*byv^1*(1-byv)^2 +
    (282844979519573623/67673309184000000000:ℝ)*bx^1*(1-bx)^1*byv^2*(1-byv)^1 +
    (29968674466766111/25377490944000000000:ℝ)*bx^1*(1-bx)^1*byv^3*(1-byv)^0 +
    (15716672739312899567/51973101453312000000000:ℝ)*bx^2*(1-bx)^0*byv^0*(1-byv)^3 +
    (94260648526566881777/155919304359936000000000:ℝ)*bx^2*(1-bx)^0*byv^1*(1-byv)^2 +
    (2944335905214554411/9744956522496000000000:ℝ)*bx^2*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 11 d p-(143123213847058249/50754981888000000000:ℝ) := by
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
  have hid : admissionGuard 7 12 d p-(890920776308200583/2122614777654498816:ℝ) =
    (21651690108860093039/1086778766159103393792:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (288647728037482811/8490459110617995264:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (3324857750518793/235846086406055424:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (48976114825715026603/8694230129272827150336:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (381072278191213183/67923672884943962112:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 12 d p-(890920776308200583/2122614777654498816:ℝ) := by
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

end Sil.Uneven.WarmupRows
