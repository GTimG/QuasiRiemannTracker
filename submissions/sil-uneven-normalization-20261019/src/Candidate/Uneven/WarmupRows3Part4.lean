/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Exact row arithmetic only; analytic source transfer is separate. -/
import Candidate.Uneven.WarmupRowsBase

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Sil.Uneven.WarmupRows

theorem gap_3_48 {d p : ℝ}
    (hd : (63/128:ℝ) ≤ d ∧ d ≤ (3/4:ℝ))
    (hp : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ)) :
    0 ≤ gap 3 0 d p := by
  let bx : ℝ := (d-(63/128:ℝ))/(33/128:ℝ)
  let byv : ℝ := (p-(127/256:ℝ))/(1/512:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : gap 3 0 d p =
    (24008148033420592845605071313/101522536730130907136000000000000:ℝ)*bx^0*(1-bx)^2*byv^0*(1-byv)^3 +
    (1152018010821470300428977652291/1827405661142356328448000000000000:ℝ)*bx^0*(1-bx)^2*byv^1*(1-byv)^2 +
    (403299890108231398066226234239/730962264456942531379200000000000:ℝ)*bx^0*(1-bx)^2*byv^2*(1-byv)^1 +
    (384503909170984873259842492379/2436540881523141771264000000000000:ℝ)*bx^0*(1-bx)^2*byv^3*(1-byv)^0 +
    (165664574211435831766386552647/42829820183023976448000000000000:ℝ)*bx^1*(1-bx)^1*byv^0*(1-byv)^3 +
    (971758902061245089389671967621/85659640366047952896000000000000:ℝ)*bx^1*(1-bx)^1*byv^1*(1-byv)^2 +
    (8441069119812358128631817429/761419025475981803520000000000:ℝ)*bx^1*(1-bx)^1*byv^2*(1-byv)^1 +
    (137417981537217640272169323263/38070951273799090176000000000000:ℝ)*bx^1*(1-bx)^1*byv^3*(1-byv)^0 +
    (46458408239498223761920939763/2676863761438998528000000000000:ℝ)*bx^2*(1-bx)^0*byv^0*(1-byv)^3 +
    (277500879001953741097379728849/5353727522877997056000000000000:ℝ)*bx^2*(1-bx)^0*byv^1*(1-byv)^2 +
    (36834056690843381437374925223/713830336383732940800000000000:ℝ)*bx^2*(1-bx)^0*byv^2*(1-byv)^1 +
    (13580942165389433780179585649/793144818204147712000000000000:ℝ)*bx^2*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [gap,base,denominator,numerator,theta,reserve,h,y,ell,
      rowHeight,rowCapacity,planeB,planeLambda,bx,byv]
    norm_num
    ring
  rw [hid]
  positivity

theorem gap_3_49 {d p : ℝ}
    (hd : (63/128:ℝ) ≤ d ∧ d ≤ (3/4:ℝ))
    (hp : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ)) :
    0 ≤ gap 3 0 d p := by
  let bx : ℝ := (d-(63/128:ℝ))/(33/128:ℝ)
  let byv : ℝ := (p-(255/512:ℝ))/(1/512:ℝ)
  have hx : 0 ≤ bx := by dsimp [bx]; linarith only [hd.1]
  have hx' : 0 ≤ 1-bx := by dsimp [bx]; linarith only [hd.2]
  have hy : 0 ≤ byv := by dsimp [byv]; linarith only [hp.1]
  have hy' : 0 ≤ 1-byv := by dsimp [byv]; linarith only [hp.2]
  have hid : gap 3 0 d p =
    (384503909170984873259842492379/2436540881523141771264000000000000:ℝ)*bx^0*(1-bx)^2*byv^0*(1-byv)^3 +
    (180504466499713358625931407527/456851415285589082112000000000000:ℝ)*bx^0*(1-bx)^2*byv^1*(1-byv)^2 +
    (125771330789500906923892739/396572409102073856000000000000:ℝ)*bx^0*(1-bx)^2*byv^2*(1-byv)^1 +
    (1113234794501992710371831/13941998757494784000000000000:ℝ)*bx^0*(1-bx)^2*byv^3*(1-byv)^0 +
    (137417981537217640272169323263/38070951273799090176000000000000:ℝ)*bx^1*(1-bx)^1*byv^0*(1-byv)^3 +
    (12576701038521497975044533379/1189717227306221568000000000000:ℝ)*bx^1*(1-bx)^1*byv^1*(1-byv)^2 +
    (1725709569630000427449073931/167303985089937408000000000000:ℝ)*bx^1*(1-bx)^1*byv^2*(1-byv)^1 +
    (2191400294906424577799231/653531191757568000000000000:ℝ)*bx^1*(1-bx)^1*byv^3*(1-byv)^0 +
    (13580942165389433780179585649/793144818204147712000000000000:ℝ)*bx^2*(1-bx)^0*byv^0*(1-byv)^3 +
    (22814394376412225609746773301/446143960239833088000000000000:ℝ)*bx^2*(1-bx)^0*byv^1*(1-byv)^2 +
    (532295886080461785489606269/10456499068121088000000000000:ℝ)*bx^2*(1-bx)^0*byv^2*(1-byv)^1 +
    (689957563252555966792049/40845699484848000000000000:ℝ)*bx^2*(1-bx)^0*byv^3*(1-byv)^0 := by
    dsimp [gap,base,denominator,numerator,theta,reserve,h,y,ell,
      rowHeight,rowCapacity,planeB,planeLambda,bx,byv]
    norm_num
    ring
  rw [hid]
  positivity

end Sil.Uneven.WarmupRows
