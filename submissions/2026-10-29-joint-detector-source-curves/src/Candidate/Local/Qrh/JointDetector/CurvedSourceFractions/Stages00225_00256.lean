/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00225_00256
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99970599449304,99970465078895,99970330680999,99970196255620,99970061802761,99969927322425,99969792814615,99969658279334,99969523716585,99969389126371,99969254508695,99969119863561,99968985190971,99968850490928,99968715763435,99968581008495,99968446226112,99968311416288,99968176579027,99968041714331,99967906822203,99967771902646,99967636955664,99967501981259,99967366979435,99967231950195,99967096893541,99966961809477,99966826698005,99966691559129,99966556392851,99966421199175,99966285978103]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (224+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(7997129919756942318286/9938680047851875497765:Fraction),(14393590239465082462867/17889274086133725895977:Fraction),(4797448860634365089321/5962974695378025298659:Fraction),(685290613470456048418/851836861244496471237:Fraction),(685231399209492261812/851820194577846471237:Fraction),(2055516548924145643745/2555410583733589413711:Fraction),(1598596944566589126679/1987502676237275099553:Fraction),(71930645591454782716064/89435870430679129479885:Fraction),(4794961978353510221044/5962274695378725298659:Fraction),(23972737850671540756957/29810790143560876493295:Fraction),(129571168336401389653/161136253028260143207:Fraction),(7989531588825145706176/9936541158965125497765:Fraction),(7988841107234939846869/9936346714520875497765:Fraction),(3423493115418149873444/4258350972889982356185:Fraction),(14377428376119427230352/17884724086138275895977:Fraction),(4792061875363258055522/5961458028712875298659:Fraction),(6534065034412517948846/8129101857335898134535:Fraction),(59444584300843227784/73960604161039395765:Fraction),(215802674051726258908/268518379671766905345:Fraction),(71856079497110515977613/89414870430700129479885:Fraction),(71849868328189560129742/89413120430701879479885:Fraction),(1596525710055019826384/1986919342904525099553:Fraction),(71837446575258848705138/89409620430705379479885:Fraction),(71831235991306250541011/89407870430707129479885:Fraction),(4788335093729117320778/5960408028713925298659:Fraction),(14363763563841655433194/17880874086142125895977:Fraction),(71812607820511788030559/89402620430712379479885:Fraction),(7978488891762325953022/9933430047857125497765:Fraction),(25326346393168264287/31534081280675795231:Fraction),(71793983816840222607196/89397370430717629479885:Fraction),(43115781746480262418/53691063321753381069:Fraction),(43112054292996636245/53690012270703381069:Fraction)]
abbrev p225 := params 0
abbrev ray225 := rays 0
def bank225 : Fin 1 → Cell := oneBank p225 ray225
theorem signs225 : ∀ j, Signs p225 (bank225 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p226 := params 1
abbrev ray226 := rays 1
def bank226 : Fin 1 → Cell := oneBank p226 ray226
theorem signs226 : ∀ j, Signs p226 (bank226 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p227 := params 2
abbrev ray227 := rays 2
def bank227 : Fin 1 → Cell := oneBank p227 ray227
theorem signs227 : ∀ j, Signs p227 (bank227 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p228 := params 3
abbrev ray228 := rays 3
def bank228 : Fin 1 → Cell := oneBank p228 ray228
theorem signs228 : ∀ j, Signs p228 (bank228 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p229 := params 4
abbrev ray229 := rays 4
def bank229 : Fin 1 → Cell := oneBank p229 ray229
theorem signs229 : ∀ j, Signs p229 (bank229 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p230 := params 5
abbrev ray230 := rays 5
def bank230 : Fin 1 → Cell := oneBank p230 ray230
theorem signs230 : ∀ j, Signs p230 (bank230 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p231 := params 6
abbrev ray231 := rays 6
def bank231 : Fin 1 → Cell := oneBank p231 ray231
theorem signs231 : ∀ j, Signs p231 (bank231 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p232 := params 7
abbrev ray232 := rays 7
def bank232 : Fin 1 → Cell := oneBank p232 ray232
theorem signs232 : ∀ j, Signs p232 (bank232 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p233 := params 8
abbrev ray233 := rays 8
def bank233 : Fin 1 → Cell := oneBank p233 ray233
theorem signs233 : ∀ j, Signs p233 (bank233 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p234 := params 9
abbrev ray234 := rays 9
def bank234 : Fin 1 → Cell := oneBank p234 ray234
theorem signs234 : ∀ j, Signs p234 (bank234 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p235 := params 10
abbrev ray235 := rays 10
def bank235 : Fin 1 → Cell := oneBank p235 ray235
theorem signs235 : ∀ j, Signs p235 (bank235 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p236 := params 11
abbrev ray236 := rays 11
def bank236 : Fin 1 → Cell := oneBank p236 ray236
theorem signs236 : ∀ j, Signs p236 (bank236 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p237 := params 12
abbrev ray237 := rays 12
def bank237 : Fin 1 → Cell := oneBank p237 ray237
theorem signs237 : ∀ j, Signs p237 (bank237 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p238 := params 13
abbrev ray238 := rays 13
def bank238 : Fin 1 → Cell := oneBank p238 ray238
theorem signs238 : ∀ j, Signs p238 (bank238 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p239 := params 14
abbrev ray239 := rays 14
def bank239 : Fin 1 → Cell := oneBank p239 ray239
theorem signs239 : ∀ j, Signs p239 (bank239 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p240 := params 15
abbrev ray240 := rays 15
def bank240 : Fin 1 → Cell := oneBank p240 ray240
theorem signs240 : ∀ j, Signs p240 (bank240 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p241 := params 16
abbrev ray241 := rays 16
def bank241 : Fin 1 → Cell := oneBank p241 ray241
theorem signs241 : ∀ j, Signs p241 (bank241 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p242 := params 17
abbrev ray242 := rays 17
def bank242 : Fin 1 → Cell := oneBank p242 ray242
theorem signs242 : ∀ j, Signs p242 (bank242 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p243 := params 18
abbrev ray243 := rays 18
def bank243 : Fin 1 → Cell := oneBank p243 ray243
theorem signs243 : ∀ j, Signs p243 (bank243 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p244 := params 19
abbrev ray244 := rays 19
def bank244 : Fin 1 → Cell := oneBank p244 ray244
theorem signs244 : ∀ j, Signs p244 (bank244 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p245 := params 20
abbrev ray245 := rays 20
def bank245 : Fin 1 → Cell := oneBank p245 ray245
theorem signs245 : ∀ j, Signs p245 (bank245 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p246 := params 21
abbrev ray246 := rays 21
def bank246 : Fin 1 → Cell := oneBank p246 ray246
theorem signs246 : ∀ j, Signs p246 (bank246 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p247 := params 22
abbrev ray247 := rays 22
def bank247 : Fin 1 → Cell := oneBank p247 ray247
theorem signs247 : ∀ j, Signs p247 (bank247 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p248 := params 23
abbrev ray248 := rays 23
def bank248 : Fin 1 → Cell := oneBank p248 ray248
theorem signs248 : ∀ j, Signs p248 (bank248 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p249 := params 24
abbrev ray249 := rays 24
def bank249 : Fin 1 → Cell := oneBank p249 ray249
theorem signs249 : ∀ j, Signs p249 (bank249 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p250 := params 25
abbrev ray250 := rays 25
def bank250 : Fin 1 → Cell := oneBank p250 ray250
theorem signs250 : ∀ j, Signs p250 (bank250 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p251 := params 26
abbrev ray251 := rays 26
def bank251 : Fin 1 → Cell := oneBank p251 ray251
theorem signs251 : ∀ j, Signs p251 (bank251 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p252 := params 27
abbrev ray252 := rays 27
def bank252 : Fin 1 → Cell := oneBank p252 ray252
theorem signs252 : ∀ j, Signs p252 (bank252 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p253 := params 28
abbrev ray253 := rays 28
def bank253 : Fin 1 → Cell := oneBank p253 ray253
theorem signs253 : ∀ j, Signs p253 (bank253 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p254 := params 29
abbrev ray254 := rays 29
def bank254 : Fin 1 → Cell := oneBank p254 ray254
theorem signs254 : ∀ j, Signs p254 (bank254 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p255 := params 30
abbrev ray255 := rays 30
def bank255 : Fin 1 → Cell := oneBank p255 ray255
theorem signs255 : ∀ j, Signs p255 (bank255 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p256 := params 31
abbrev ray256 := rays 31
def bank256 : Fin 1 → Cell := oneBank p256 ray256
theorem signs256 : ∀ j, Signs p256 (bank256 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00225_00256
