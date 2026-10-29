/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00385_00416
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99948752572516,99948613842387,99948475085247,99948336301099,99948197489946,99948058651790,99947919786635,99947780894484,99947641975339,99947503029203,99947364056079,99947225055970,99947086028879,99946946974809,99946807893762,99946668785742,99946529650751,99946390488793,99946251299870,99946112083985,99945972841141,99945833571341,99945694274588,99945554950884,99945415600233,99945276222637,99945136818099,99944997386623,99944857928211,99944718442866,99944578930591,99944439391388,99944299825261]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (384+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(1820109121338532735568/2286362062331971268715:Fraction),(3379909587292552626488/4246017639568982356185:Fraction),(876196873225941356232/1100797783098152833085:Fraction),(70965793134025654402561/89162870430952129479885:Fraction),(23653213513791386243716/29720373476984626493295:Fraction),(525581390711387683768/660439780970041699851:Fraction),(14189466949606000639067/17831524086191475895977:Fraction),(70941182754760427216204/89155870430959129479885:Fraction),(1125952885179122214266/1415144768745410785395:Fraction),(23642960191745427001838/29717456810320876493295:Fraction),(6447520834693521959506/8104601857360398134535:Fraction),(175102663686243630804/220120667730780566617:Fraction),(23636809803064458651607/29715706810322626493295:Fraction),(3376394277285618097453/4245017639569982356185:Fraction),(525171333587813409668/660323114303491699851:Fraction),(70891981250789998394848/89141870430973129479885:Fraction),(7876203719151067076116/9904457825663875497765:Fraction),(875057845575082116132/1100473709024402833085:Fraction),(14174707703204706490360/17827324086195675895977:Fraction),(14173478267634575576762/17826974086196025895977:Fraction),(3374344950383011179497/4244434306237232356185:Fraction),(23618365861082316170353/29710456810327876493295:Fraction),(70848952213841287557256/89129620430985379479885:Fraction),(4722853776150288987590/5941858028732475298659:Fraction),(70836662076143382672397/89126120430988879479885:Fraction),(70830517307907359560541/89124370430990629479885:Fraction),(23608124112519933016841/29707540143664126493295:Fraction),(70818228372801704603336/89120870430994129479885:Fraction),(70812085413689089315238/89119120430995879479885:Fraction),(2622442305650511518672/3300643349296208499255:Fraction),(874071606137893164791/1100192844827152833085:Fraction),(177427713633627003236/223343033661656966115:Fraction)]
abbrev p385 := params 0
abbrev ray385 := rays 0
def bank385 : Fin 1 → Cell := oneBank p385 ray385
theorem signs385 : ∀ j, Signs p385 (bank385 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p386 := params 1
abbrev ray386 := rays 1
def bank386 : Fin 1 → Cell := oneBank p386 ray386
theorem signs386 : ∀ j, Signs p386 (bank386 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p387 := params 2
abbrev ray387 := rays 2
def bank387 : Fin 1 → Cell := oneBank p387 ray387
theorem signs387 : ∀ j, Signs p387 (bank387 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p388 := params 3
abbrev ray388 := rays 3
def bank388 : Fin 1 → Cell := oneBank p388 ray388
theorem signs388 : ∀ j, Signs p388 (bank388 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p389 := params 4
abbrev ray389 := rays 4
def bank389 : Fin 1 → Cell := oneBank p389 ray389
theorem signs389 : ∀ j, Signs p389 (bank389 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p390 := params 5
abbrev ray390 := rays 5
def bank390 : Fin 1 → Cell := oneBank p390 ray390
theorem signs390 : ∀ j, Signs p390 (bank390 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p391 := params 6
abbrev ray391 := rays 6
def bank391 : Fin 1 → Cell := oneBank p391 ray391
theorem signs391 : ∀ j, Signs p391 (bank391 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p392 := params 7
abbrev ray392 := rays 7
def bank392 : Fin 1 → Cell := oneBank p392 ray392
theorem signs392 : ∀ j, Signs p392 (bank392 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p393 := params 8
abbrev ray393 := rays 8
def bank393 : Fin 1 → Cell := oneBank p393 ray393
theorem signs393 : ∀ j, Signs p393 (bank393 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p394 := params 9
abbrev ray394 := rays 9
def bank394 : Fin 1 → Cell := oneBank p394 ray394
theorem signs394 : ∀ j, Signs p394 (bank394 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p395 := params 10
abbrev ray395 := rays 10
def bank395 : Fin 1 → Cell := oneBank p395 ray395
theorem signs395 : ∀ j, Signs p395 (bank395 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p396 := params 11
abbrev ray396 := rays 11
def bank396 : Fin 1 → Cell := oneBank p396 ray396
theorem signs396 : ∀ j, Signs p396 (bank396 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p397 := params 12
abbrev ray397 := rays 12
def bank397 : Fin 1 → Cell := oneBank p397 ray397
theorem signs397 : ∀ j, Signs p397 (bank397 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p398 := params 13
abbrev ray398 := rays 13
def bank398 : Fin 1 → Cell := oneBank p398 ray398
theorem signs398 : ∀ j, Signs p398 (bank398 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p399 := params 14
abbrev ray399 := rays 14
def bank399 : Fin 1 → Cell := oneBank p399 ray399
theorem signs399 : ∀ j, Signs p399 (bank399 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p400 := params 15
abbrev ray400 := rays 15
def bank400 : Fin 1 → Cell := oneBank p400 ray400
theorem signs400 : ∀ j, Signs p400 (bank400 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p401 := params 16
abbrev ray401 := rays 16
def bank401 : Fin 1 → Cell := oneBank p401 ray401
theorem signs401 : ∀ j, Signs p401 (bank401 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p402 := params 17
abbrev ray402 := rays 17
def bank402 : Fin 1 → Cell := oneBank p402 ray402
theorem signs402 : ∀ j, Signs p402 (bank402 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p403 := params 18
abbrev ray403 := rays 18
def bank403 : Fin 1 → Cell := oneBank p403 ray403
theorem signs403 : ∀ j, Signs p403 (bank403 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p404 := params 19
abbrev ray404 := rays 19
def bank404 : Fin 1 → Cell := oneBank p404 ray404
theorem signs404 : ∀ j, Signs p404 (bank404 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p405 := params 20
abbrev ray405 := rays 20
def bank405 : Fin 1 → Cell := oneBank p405 ray405
theorem signs405 : ∀ j, Signs p405 (bank405 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p406 := params 21
abbrev ray406 := rays 21
def bank406 : Fin 1 → Cell := oneBank p406 ray406
theorem signs406 : ∀ j, Signs p406 (bank406 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p407 := params 22
abbrev ray407 := rays 22
def bank407 : Fin 1 → Cell := oneBank p407 ray407
theorem signs407 : ∀ j, Signs p407 (bank407 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p408 := params 23
abbrev ray408 := rays 23
def bank408 : Fin 1 → Cell := oneBank p408 ray408
theorem signs408 : ∀ j, Signs p408 (bank408 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p409 := params 24
abbrev ray409 := rays 24
def bank409 : Fin 1 → Cell := oneBank p409 ray409
theorem signs409 : ∀ j, Signs p409 (bank409 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p410 := params 25
abbrev ray410 := rays 25
def bank410 : Fin 1 → Cell := oneBank p410 ray410
theorem signs410 : ∀ j, Signs p410 (bank410 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p411 := params 26
abbrev ray411 := rays 26
def bank411 : Fin 1 → Cell := oneBank p411 ray411
theorem signs411 : ∀ j, Signs p411 (bank411 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p412 := params 27
abbrev ray412 := rays 27
def bank412 : Fin 1 → Cell := oneBank p412 ray412
theorem signs412 : ∀ j, Signs p412 (bank412 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p413 := params 28
abbrev ray413 := rays 28
def bank413 : Fin 1 → Cell := oneBank p413 ray413
theorem signs413 : ∀ j, Signs p413 (bank413 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p414 := params 29
abbrev ray414 := rays 29
def bank414 : Fin 1 → Cell := oneBank p414 ray414
theorem signs414 : ∀ j, Signs p414 (bank414 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p415 := params 30
abbrev ray415 := rays 30
def bank415 : Fin 1 → Cell := oneBank p415 ray415
theorem signs415 : ∀ j, Signs p415 (bank415 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p416 := params 31
abbrev ray416 := rays 31
def bank416 : Fin 1 → Cell := oneBank p416 ray416
theorem signs416 : ∀ j, Signs p416 (bank416 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00385_00416
