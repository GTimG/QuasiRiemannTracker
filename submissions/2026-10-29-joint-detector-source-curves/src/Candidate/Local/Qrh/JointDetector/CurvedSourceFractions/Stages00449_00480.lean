/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00449_00480
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99939819510230,99939679057203,99939538577349,99939398070670,99939257537170,99939116976851,99938976389717,99938835775769,99938695135012,99938554467447,99938413773078,99938273051907,99938132303937,99937991529171,99937850727612,99937709899263,99937569044127,99937428162206,99937287253503,99937146318021,99937005355763,99936864366732,99936723350930,99936582308361,99936441239027,99936300142931,99936159020076,99936017870464,99935876694099,99935735490983,99935594261120,99935453004512,99935311721161]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (448+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(4706079647035945189744/5937074695403925298659:Fraction),(7842785114872550714777/9894930047895625497765:Fraction),(70578938369425109181494/89052620431062379479885:Fraction),(14114562100808569011224/17810174086212825895977:Fraction),(1568148525466756278812/1978869342912575099553:Fraction),(70560556587066775850023/89047370431067629479885:Fraction),(4703628702370535634482/5936374695404625298659:Fraction),(3359443061105027816423/4240184306241482356185:Fraction),(14108435807673339884638/17808424086214575895977:Fraction),(70536053592740055931801/89040370431074629479885:Fraction),(2612219598322621813088/3297726682632458499255:Fraction),(70523805724334731158704/89036870431078129479885:Fraction),(2611765958698881110761/3297597053002958499255:Fraction),(2611539194871411214036/3297532238188208499255:Fraction),(7833937270839225154394/9892402270120375497765:Fraction),(290120627213818823094/366378067617634277695:Fraction),(23497730132071367369054/29676040143695626493295:Fraction),(70487068178904934315568/89026370431088629479885:Fraction),(70480946969530705263863/89024620431090379479885:Fraction),(42327223284173238479/53467189448103381069:Fraction),(10066958052328465677841/12717302918727697068555:Fraction),(70462585763996558066366/89019370431095629479885:Fraction),(1565699248217722138832/1978169342913275099553:Fraction),(23483448791733595569571/29671956810366376493295:Fraction),(70444227588792659965603/89014120431100879479885:Fraction),(23479369936876706533232/29670790143700876493295:Fraction),(70431991832167030147718/89010620431104379479885:Fraction),(1083474979283316220052/1369367237401632761229:Fraction),(869379709666944521672/1098853338655652833085:Fraction),(70413639112396910129278/89005370431109629479885:Fraction),(4693834850014309612630/5933574695407425298659:Fraction),(173830635546991271490/219757704768180566617:Fraction)]
abbrev p449 := params 0
abbrev ray449 := rays 0
def bank449 : Fin 1 → Cell := oneBank p449 ray449
theorem signs449 : ∀ j, Signs p449 (bank449 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p450 := params 1
abbrev ray450 := rays 1
def bank450 : Fin 1 → Cell := oneBank p450 ray450
theorem signs450 : ∀ j, Signs p450 (bank450 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p451 := params 2
abbrev ray451 := rays 2
def bank451 : Fin 1 → Cell := oneBank p451 ray451
theorem signs451 : ∀ j, Signs p451 (bank451 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p452 := params 3
abbrev ray452 := rays 3
def bank452 : Fin 1 → Cell := oneBank p452 ray452
theorem signs452 : ∀ j, Signs p452 (bank452 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p453 := params 4
abbrev ray453 := rays 4
def bank453 : Fin 1 → Cell := oneBank p453 ray453
theorem signs453 : ∀ j, Signs p453 (bank453 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p454 := params 5
abbrev ray454 := rays 5
def bank454 : Fin 1 → Cell := oneBank p454 ray454
theorem signs454 : ∀ j, Signs p454 (bank454 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p455 := params 6
abbrev ray455 := rays 6
def bank455 : Fin 1 → Cell := oneBank p455 ray455
theorem signs455 : ∀ j, Signs p455 (bank455 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p456 := params 7
abbrev ray456 := rays 7
def bank456 : Fin 1 → Cell := oneBank p456 ray456
theorem signs456 : ∀ j, Signs p456 (bank456 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p457 := params 8
abbrev ray457 := rays 8
def bank457 : Fin 1 → Cell := oneBank p457 ray457
theorem signs457 : ∀ j, Signs p457 (bank457 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p458 := params 9
abbrev ray458 := rays 9
def bank458 : Fin 1 → Cell := oneBank p458 ray458
theorem signs458 : ∀ j, Signs p458 (bank458 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p459 := params 10
abbrev ray459 := rays 10
def bank459 : Fin 1 → Cell := oneBank p459 ray459
theorem signs459 : ∀ j, Signs p459 (bank459 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p460 := params 11
abbrev ray460 := rays 11
def bank460 : Fin 1 → Cell := oneBank p460 ray460
theorem signs460 : ∀ j, Signs p460 (bank460 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p461 := params 12
abbrev ray461 := rays 12
def bank461 : Fin 1 → Cell := oneBank p461 ray461
theorem signs461 : ∀ j, Signs p461 (bank461 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p462 := params 13
abbrev ray462 := rays 13
def bank462 : Fin 1 → Cell := oneBank p462 ray462
theorem signs462 : ∀ j, Signs p462 (bank462 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p463 := params 14
abbrev ray463 := rays 14
def bank463 : Fin 1 → Cell := oneBank p463 ray463
theorem signs463 : ∀ j, Signs p463 (bank463 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p464 := params 15
abbrev ray464 := rays 15
def bank464 : Fin 1 → Cell := oneBank p464 ray464
theorem signs464 : ∀ j, Signs p464 (bank464 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p465 := params 16
abbrev ray465 := rays 16
def bank465 : Fin 1 → Cell := oneBank p465 ray465
theorem signs465 : ∀ j, Signs p465 (bank465 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p466 := params 17
abbrev ray466 := rays 17
def bank466 : Fin 1 → Cell := oneBank p466 ray466
theorem signs466 : ∀ j, Signs p466 (bank466 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p467 := params 18
abbrev ray467 := rays 18
def bank467 : Fin 1 → Cell := oneBank p467 ray467
theorem signs467 : ∀ j, Signs p467 (bank467 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p468 := params 19
abbrev ray468 := rays 19
def bank468 : Fin 1 → Cell := oneBank p468 ray468
theorem signs468 : ∀ j, Signs p468 (bank468 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p469 := params 20
abbrev ray469 := rays 20
def bank469 : Fin 1 → Cell := oneBank p469 ray469
theorem signs469 : ∀ j, Signs p469 (bank469 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p470 := params 21
abbrev ray470 := rays 21
def bank470 : Fin 1 → Cell := oneBank p470 ray470
theorem signs470 : ∀ j, Signs p470 (bank470 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p471 := params 22
abbrev ray471 := rays 22
def bank471 : Fin 1 → Cell := oneBank p471 ray471
theorem signs471 : ∀ j, Signs p471 (bank471 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p472 := params 23
abbrev ray472 := rays 23
def bank472 : Fin 1 → Cell := oneBank p472 ray472
theorem signs472 : ∀ j, Signs p472 (bank472 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p473 := params 24
abbrev ray473 := rays 24
def bank473 : Fin 1 → Cell := oneBank p473 ray473
theorem signs473 : ∀ j, Signs p473 (bank473 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p474 := params 25
abbrev ray474 := rays 25
def bank474 : Fin 1 → Cell := oneBank p474 ray474
theorem signs474 : ∀ j, Signs p474 (bank474 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p475 := params 26
abbrev ray475 := rays 26
def bank475 : Fin 1 → Cell := oneBank p475 ray475
theorem signs475 : ∀ j, Signs p475 (bank475 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p476 := params 27
abbrev ray476 := rays 27
def bank476 : Fin 1 → Cell := oneBank p476 ray476
theorem signs476 : ∀ j, Signs p476 (bank476 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p477 := params 28
abbrev ray477 := rays 28
def bank477 : Fin 1 → Cell := oneBank p477 ray477
theorem signs477 : ∀ j, Signs p477 (bank477 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p478 := params 29
abbrev ray478 := rays 29
def bank478 : Fin 1 → Cell := oneBank p478 ray478
theorem signs478 : ∀ j, Signs p478 (bank478 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p479 := params 30
abbrev ray479 := rays 30
def bank479 : Fin 1 → Cell := oneBank p479 ray479
theorem signs479 : ∀ j, Signs p479 (bank479 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p480 := params 31
abbrev ray480 := rays 31
def bank480 : Fin 1 → Cell := oneBank p480 ray480
theorem signs480 : ∀ j, Signs p480 (bank480 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00449_00480
