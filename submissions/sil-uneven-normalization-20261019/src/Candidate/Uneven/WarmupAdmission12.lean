/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Count-admission arithmetic only; source moment theorems are separate. -/
import Candidate.Uneven.WarmupAdmissionBase

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.WarmupRows

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
  have hid : admissionGuard 7 0 d p-(145870295/74348118:ℝ) =
    (77174059/4758279552:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 0 d p-(145870295/74348118:ℝ) := by
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
  have hid : admissionGuard 7 1 d p-(54348118/37174059:ℝ) =
    (312500/37174059:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 1 d p-(54348118/37174059:ℝ) := by
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
  have hid : admissionGuard 7 2 d p-(27386650/37174059:ℝ) =
    (9787409/2379139776:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 2 d p-(27386650/37174059:ℝ) := by
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
  have hid : admissionGuard 7 3 d p-(7551125635/7137419328:ℝ) =
    (3481686347/169970171904:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (202207099373/7308717391872:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (91522177/12688745472:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (6060819875/456794836992:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (6046757375/456794836992:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 3 d p-(7551125635/7137419328:ℝ) := by
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
  have hid : admissionGuard 7 4 d p-(1081772675/6344372736:ℝ) =
    (188725247615/51973101453312:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (237/65536:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (18955618325/3248318840832:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (404963495/50754981888:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 +
    (13693325/6344372736:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 4 d p-(1081772675/6344372736:ℝ) := by
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
  have hid : admissionGuard 7 5 d p-(12364745308369/135346618368000:ℝ) =
    (14464310161061/3609243156480000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (203113054234709/24362391306240000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (26325400711379/6090597826560000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (8985764981/24362391306240:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 +
    (17612324287/48724782612480:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 5 d p-(12364745308369/135346618368000:ℝ) := by
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
  have hid : admissionGuard 7 6 d p-(40102781964152887195/157073493546432912384:ℝ) =
    (2904684601681544788315/321686514783094604562432:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (1927933601997991842751/107228838261031534854144:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (89974256850054686209/10052703586971706392576:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (245593777985850917065/20105407173943412785152:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (184065821787007992085/6701802391314470928384:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (11538396545181178615/628293974185731649536:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 +
    (1393812403398955/447502830616617984:ℝ)*bx^1*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 6 d p-(40102781964152887195/157073493546432912384:ℝ) := by
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
  have hid : admissionGuard 7 7 d p-(69910727504830625/132663423603406176:ℝ) =
    (21281169691786595663/1337573866041973407744:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (6617083861180070845/271694691539775848448:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (1997449357280875/235846086406055424:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (7958794538289540785/1086778766159103393792:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (123943091335980175/16980918221235990528:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 7 d p-(69910727504830625/132663423603406176:ℝ) := by
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
  have hid : admissionGuard 7 8 d p-(208950908800433781422812153/107336174435467001856000000000:ℝ) =
    (16363517249850979537865267/24150639247980075417600000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (905474224686034161218293369/668786933020986703872000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (5879980039977522246270223927/8694230129272827150336000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (750047296977571749060269/441712651997806592000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (5517867934504463423699146829/966025569919203016704000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (55025272169578331245776472741/8694230129272827150336000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 +
    (20127319000643078115124926007/8694230129272827150336000000000:ℝ)*bx^1*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 8 d p-(208950908800433781422812153/107336174435467001856000000000:ℝ) := by
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
  have hid : admissionGuard 7 9 d p-(17755911004670522704613/1326634236034061760000000:ℝ) =
    (12195275857932233709512742053/4347115064636413575168000000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (5336929591126028882361044509/724519177439402262528000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (107315649901055912204745991/16980918221235990528000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (20742854275523012228563/11792304320302771200000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (53576994833700401534268139/54338938307955169689600000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (17830314070158097540588163/9056489717992528281600000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (208605872384799111197369/212261477765449881600000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 9 d p-(17755911004670522704613/1326634236034061760000000:ℝ) := by
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
  have hid : admissionGuard 7 10 d p-(798400089053409624226773113/42452295553089976320000000000:ℝ) =
    (205605591421921441130667576896839/69553841034182617202688000000000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (178609678596530907119506144165009/23184613678060872400896000000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (3555774128298788456621932625491/543389383079551696896000000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (677722505909329173410572063/377353738249688678400000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (955823522096104656326914935257/869423012927282715033600000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (636088749084869471018409131663/289807670975760905011200000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (7440744368363121613751637869/6792367288494396211200000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 10 d p-(798400089053409624226773113/42452295553089976320000000000:ℝ) := by
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
  have hid : admissionGuard 7 11 d p-(125945959069769/31721863680000000:ℝ) =
    (187454366602983887263/207892405813248000000000:ℝ)*bx^0*(1-bx)^2*byv^0*(1-byv)^3 +
    (1468865640542846839361/623677217439744000000000:ℝ)*bx^0*(1-bx)^2*byv^1*(1-byv)^2 +
    (15637382448805876831/7795965217996800000000:ℝ)*bx^0*(1-bx)^2*byv^2*(1-byv)^1 +
    (8626119732481853/15616917504000000000:ℝ)*bx^0*(1-bx)^2*byv^3*(1-byv)^0 +
    (1616014656472984793/1299327536332800000000:ℝ)*bx^1*(1-bx)^1*byv^0*(1-byv)^3 +
    (791656415193970217/259865507266560000000:ℝ)*bx^1*(1-bx)^1*byv^1*(1-byv)^2 +
    (191865118081821151/81207971020800000000:ℝ)*bx^1*(1-bx)^1*byv^2*(1-byv)^1 +
    (710541154945151/1268874547200000000:ℝ)*bx^1*(1-bx)^1*byv^3*(1-byv)^0 +
    (434205931470343/1299327536332800000:ℝ)*bx^2*(1-bx)^0*byv^0*(1-byv)^3 +
    (2603424742881433/3897982608998400000:ℝ)*bx^2*(1-bx)^0*byv^1*(1-byv)^2 +
    (81298566603619/243623913062400000:ℝ)*bx^2*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 11 d p-(125945959069769/31721863680000000:ℝ) := by
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
  have hid : admissionGuard 7 12 d p-(115105562007858715/265326847206812352:ℝ) =
    (17348410427436741233/1337573866041973407744:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (2716237066110724745/135847345769887924224:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (3324857750518793/471692172812110848:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (6330745594469494895/1086778766159103393792:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (49257970000129715/8490459110617995264:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 12 d p-(115105562007858715/265326847206812352:ℝ) := by
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

end Sil.Uneven.WarmupRows
