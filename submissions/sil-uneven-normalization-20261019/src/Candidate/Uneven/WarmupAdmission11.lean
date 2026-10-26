/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Count-admission arithmetic only; source moment theorems are separate. -/
import Candidate.Uneven.WarmupAdmissionBase

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.WarmupRows

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
  have hid : admissionGuard 7 0 d p-(145870295/74348118:ℝ) =
    (77174059/4758279552:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 0 d p-(145870295/74348118:ℝ) := by
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
  have hid : admissionGuard 7 1 d p-(54348118/37174059:ℝ) =
    (312500/37174059:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 1 d p-(54348118/37174059:ℝ) := by
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
  have hid : admissionGuard 7 2 d p-(27386650/37174059:ℝ) =
    (9787409/2379139776:ℝ)*bx^0*(1-bx)^0*byv^0*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 2 d p-(27386650/37174059:ℝ) := by
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
  have hid : admissionGuard 7 3 d p-(2828876971/2655783936:ℝ) =
    (74867566945/3654358695936:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (101116266421/3654358695936:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (91522177/12688745472:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (96995738969/7308717391872:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (96773551469/7308717391872:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 3 d p-(2828876971/2655783936:ℝ) := by
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
  have hid : admissionGuard 7 4 d p-(13693325/81338112:ℝ) =
    (2388927185/666321813504:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (117/32768:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (7715409385/1332643627008:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (6442241861/812079710208:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 +
    (13693325/6344372736:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 4 d p-(13693325/81338112:ℝ) := by
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
  have hid : admissionGuard 7 5 d p-(1032572555152703/10827729469440000:ℝ) =
    (14464310161061/3609243156480000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (403944312628189/48724782612480000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (416651799841481/97449565224960000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (15689734120771/48724782612480000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 +
    (30670037033417/97449565224960000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 5 d p-(1032572555152703/10827729469440000:ℝ) := by
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
  have hid : admissionGuard 7 6 d p-(19806776905279926995/78536746773216456192:ℝ) =
    (1440904007074003453715/160843257391547302281216:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (956376656981193907991/53614419130515767427072:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (44632987233536444969/5026351793485853196288:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (3906623860240076792155/321686514783094604562432:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (2929872860556523846591/107228838261031534854144:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (183906062339917061569/10052703586971706392576:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 +
    (1393812403398955/447502830616617984:ℝ)*bx^1*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 6 d p-(19806776905279926995/78536746773216456192:ℝ) := by
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
  have hid : admissionGuard 7 7 d p-(1136548684292817875/2122614777654498816:ℝ) =
    (139350876580107241339/8694230129272827150336:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (3324477470904661445/135847345769887924224:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (1997449357280875/235846086406055424:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (129387259779621391619/17388460258545654300672:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (2014960542004934845/271694691539775848448:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 7 d p-(1136548684292817875/2122614777654498816:ℝ) := by
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
  have hid : admissionGuard 7 8 d p-(13344707817441923200583393/53668087217733500928000000000:ℝ) =
    (8903422011918289811431243/12075319623990037708800000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (6403300255743595578079489517/4347115064636413575168000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (3197911012860755557084398287/4347115064636413575168000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (750047296977571749060269/441712651997806592000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (428892385035683648238387353/74309659224554078208000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (28030353880073539153048818989/4347115064636413575168000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 +
    (10321580493193533491511749327/4347115064636413575168000000000:ℝ)*bx^1*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 8 d p-(13344707817441923200583393/53668087217733500928000000000:ℝ) := by
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
  have hid : admissionGuard 7 9 d p-(37375780671008114568049/2468156718202905600000000:ℝ) =
    (6228873164519816034173284333/2173557532318206787584000000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (2712055578287504173753151909/362259588719701131264000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (54166849770534241343155151/8490459110617995264000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (20742854275523012228563/11792304320302771200000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (4548630057803430481575277733/4347115064636413575168000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (1513606691061627268392312349/724519177439402262528000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (17706519430796499377353831/16980918221235990528000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 9 d p-(37375780671008114568049/2468156718202905600000000:ℝ) := by
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
  have hid : admissionGuard 7 10 d p-(1627244411103644941833418549/78981014982492979200000000000:ℝ) =
    (104913744393473478256072658160479/34776920517091308601344000000000000:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^3 +
    (90707222488532351657251457572409/11592306839030436200448000000000000:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^2 +
    (1794263740800112577505031454651/271694691539775848448000000000000:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^1 +
    (677722505909329173410572063/377353738249688678400000000000:ℝ)*bx^0*(1-bx)^1*byv^3*(1-byv)^0 +
    (80687779132713887887630934244679/69553841034182617202688000000000000:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^3 +
    (53691866307323353876469501512849/23184613678060872400896000000000000:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^2 +
    (628012902770486427488261313331/543389383079551696896000000000000:ℝ)*bx^1*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 10 d p-(1627244411103644941833418549/78981014982492979200000000000:ℝ) := by
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
  have hid : admissionGuard 7 11 d p-(918193694568785689/203019927552000000000:ℝ) =
    (46833704874259217039/51973101453312000000000:ℝ)*bx^0*(1-bx)^2*byv^0*(1-byv)^3 +
    (24309692919869562527/10394620290662400000000:ℝ)*bx^0*(1-bx)^2*byv^1*(1-byv)^2 +
    (6414376809777013033/3248318840832000000000:ℝ)*bx^0*(1-bx)^2*byv^2*(1-byv)^1 +
    (109045499984343947/203019927552000000000:ℝ)*bx^0*(1-bx)^2*byv^3*(1-byv)^0 +
    (201225622783585483/159917235240960000000:ℝ)*bx^1*(1-bx)^1*byv^0*(1-byv)^3 +
    (36702516536297829773/11993792643072000000000:ℝ)*bx^1*(1-bx)^1*byv^1*(1-byv)^2 +
    (22866905795798788403/9744956522496000000000:ℝ)*bx^1*(1-bx)^1*byv^2*(1-byv)^1 +
    (55296264126652009/101509963776000000000:ℝ)*bx^1*(1-bx)^1*byv^3*(1-byv)^0 +
    (72623460724185460127/207892405813248000000000:ℝ)*bx^2*(1-bx)^0*byv^0*(1-byv)^3 +
    (435387487633660995137/623677217439744000000000:ℝ)*bx^2*(1-bx)^0*byv^1*(1-byv)^2 +
    (13594527687205268891/38979826089984000000000:ℝ)*bx^2*(1-bx)^0*byv^2*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 11 d p-(918193694568785689/203019927552000000000:ℝ) := by
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
  have hid : admissionGuard 7 12 d p-(1871612711880408577/4245229555308997632:ℝ) =
    (113599592743359284293/8694230129272827150336:ℝ)*bx^0*(1-bx)^1*byv^0*(1-byv)^2 +
    (1364614273960274641/67923672884943962112:ℝ)*bx^0*(1-bx)^1*byv^1*(1-byv)^1 +
    (3324857750518793/471692172812110848:ℝ)*bx^0*(1-bx)^1*byv^2*(1-byv)^0 +
    (102961779441552850877/17388460258545654300672:ℝ)*bx^1*(1-bx)^0*byv^0*(1-byv)^2 +
    (801119001811899977/135847345769887924224:ℝ)*bx^1*(1-bx)^0*byv^1*(1-byv)^1 := by
    dsimp [admissionGuard,planeB,planeLambda,bx,byv]
    norm_num
    ring
  have hh : 0 ≤ admissionGuard 7 12 d p-(1871612711880408577/4245229555308997632:ℝ) := by
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

end Sil.Uneven.WarmupRows
