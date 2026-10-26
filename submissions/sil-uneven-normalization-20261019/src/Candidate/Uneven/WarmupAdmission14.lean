/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Count-admission arithmetic only; source moment theorems are separate. -/
import Candidate.Uneven.WarmupAdmissionBase

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.WarmupRows

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
  have hid : admissionGuard 7 0 d p-(145870295/74348118:ℝ) =
    (77174059/4758279552:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 0 d p-(145870295/74348118:ℝ) := by
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
  have hid : admissionGuard 7 1 d p-(54348118/37174059:ℝ) =
    (312500/37174059:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 1 d p-(54348118/37174059:ℝ) := by
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
  have hid : admissionGuard 7 2 d p-(27386650/37174059:ℝ) =
    (9787409/2379139776:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 2 d p-(27386650/37174059:ℝ) := by
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
  have hid : admissionGuard 7 3 d p-(29380802947/28549677312:ℝ) =
    (7783131691/281104515072:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (153782173435/3654358695936:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (91522177/6344372736:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (24220658531/1827179347968:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (24161596031/1827179347968:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 3 d p-(29380802947/28549677312:ℝ) := by
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
  have hid : admissionGuard 7 4 d p-(561426325/3172186368:ℝ) =
    (97946014585/25986550726656:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (123/32768:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (106255330085/12993275363328:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (2533400839/203019927552:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 +
    (13693325/3172186368:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 4 d p-(561426325/3172186368:ℝ) := by
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
  have hid : admissionGuard 7 5 d p-(203901975684197/2706932367360000:ℝ) =
    (14464310161061/1804621578240000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (100450983792719/6090597826560000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (41270331017623/4872478261248000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (6774678331729/12181195653120000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 +
    (13360773684083/24362391306240000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 5 d p-(203901975684197/2706932367360000:ℝ) := by
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
  have hid : admissionGuard 7 6 d p-(20785233212465993405/78536746773216456192:ℝ) =
    (1486657182141079215485/160843257391547302281216:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (986737233052401961529/53614419130515767427072:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (46049551999500037511/5026351793485853196288:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (1255736514116574550105/80421628695773651140608:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (1001928389823268996069/26807209565257883713536:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (70344819936172104571/2513175896742926598144:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 +
    (1393812403398955/223751415308308992:ℝ)*bx^1*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 6 d p-(20785233212465993405/78536746773216456192:ℝ) := by
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
  have hid : admissionGuard 7 7 d p-(261665865803794625/530653694413624704:ℝ) =
    (208891755352931939221/8694230129272827150336:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (5561796969233725355/135847345769887924224:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (1997449357280875/117923043203027712:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (29788630986169424081/4347115064636413575168:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (463901284714668655/67923672884943962112:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 7 d p-(261665865803794625/530653694413624704:ℝ) := by
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
  have hid : admissionGuard 7 8 d p-(377867694148541793243874127/53668087217733500928000000000:ℝ) =
    (1203353692789417928287361/2415063924798007541760000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (4332429074606101457437159043/4347115064636413575168000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (2166227041372777821287252993/4347115064636413575168000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (750047296977571749060269/220856325998903296000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (5103997983068307827842008349/483012784959601508352000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (47586536323265988607375817987/4347115064636413575168000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 +
    (16413566002038333690141955073/4347115064636413575168000000000:ℝ)*bx^1*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 8 d p-(377867694148541793243874127/53668087217733500928000000000:ℝ) := by
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
  have hid : admissionGuard 7 9 d p-(168432531613703344035193/26532684720681235200000000:ℝ) =
    (9527255122369420930474363267/2173557532318206787584000000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (4449353897421746050446999371/362259588719701131264000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (96935315725638806793722609/8490459110617995264000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (20742854275523012228563/5896152160151385600000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (809069425566609671851536167/1086778766159103393792000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (269424715954182485666503951/181129794359850565632000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (3154067807683411742383069/4245229555308997632000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 9 d p-(168432531613703344035193/26532684720681235200000000:ℝ) := by
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
  have hid : admissionGuard 7 10 d p-(9868499227884229923840313693/849045911061799526400000000000:ℝ) =
    (158928855808026224114635500638321/34776920517091308601344000000000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (147556595872068535888776236938871/11592306839030436200448000000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (3192637646961390195295606543109/271694691539775848448000000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (677722505909329173410572063/188676869124844339200000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (14894573076896577745060559281021/17388460258545654300672000000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (9917008601163593225371411653451/5796153419515218100224000000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (116061534065825733886902473569/135847345769887924224000000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 10 d p-(9868499227884229923840313693/849045911061799526400000000000:ℝ) := by
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
  have hid : admissionGuard 7 11 d p-(6803236387047163/4229581824000000000:ℝ) =
    (26225558331555002533/17324367151104000000000:ℝ)*bx^0*(1-bx)^2*byv^0*(1-byv)^3 +
    (132180133764947170813/31183860871987200000000:ℝ)*bx^0*(1-bx)^2*byv^1*(1-byv)^2 +
    (38359337173850115179/9744956522496000000000:ℝ)*bx^0*(1-bx)^2*byv^2*(1-byv)^1 +
    (61484377202492293/50754981888000000000:ℝ)*bx^0*(1-bx)^2*byv^3*(1-byv)^0 +
    (872917293628412153/481232420864000000000:ℝ)*bx^1*(1-bx)^1*byv^0*(1-byv)^3 +
    (189809501038607981213/38979826089984000000000:ℝ)*bx^1*(1-bx)^1*byv^1*(1-byv)^2 +
    (10469417276827684367/2436239130624000000000:ℝ)*bx^1*(1-bx)^1*byv^2*(1-byv)^1 +
    (15757851367863091/12688745472000000000:ℝ)*bx^1*(1-bx)^1*byv^3*(1-byv)^0 +
    (1163613609980392109/4331091787776000000000:ℝ)*bx^2*(1-bx)^0*byv^0*(1-byv)^3 +
    (6981294855670305779/12993275363328000000000:ℝ)*bx^2*(1-bx)^0*byv^1*(1-byv)^2 +
    (218146512899574497/812079710208000000000:ℝ)*bx^2*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 11 d p-(6803236387047163/4229581824000000000:ℝ) := by
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
  have hid : admissionGuard 7 12 d p-(430498528276765723/1061307388827249408:ℝ) =
    (171543670940839811755/8694230129272827150336:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (2296190342490037951/67923672884943962112:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (3324857750518793/235846086406055424:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (23653132447837047023/4347115064636413575168:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (184040398190694323/33961836442471981056:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 12 d p-(430498528276765723/1061307388827249408:ℝ) := by
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

end Sil.Uneven.WarmupRows
