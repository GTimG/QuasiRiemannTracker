/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00481_00512
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99935311721161,99935170411071,99935029074245,99934887710685,99934746320394,99934604903375,99934463459631,99934321989164,99934180491977,99934038968074,99933897417457,99933755840129,99933614236092,99933472605349,99933330947904,99933189263759,99933047552917,99932905815380,99932764051152,99932622260235,99932480442632,99932338598346,99932196727380,99932054829736,99931912905417,99931770954426,99931628976767,99931486972441,99931344941452,99931202883802,99931060799494,99930918688531,99930776550915]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (480+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(79542702647133088879/100565107831768225401:Fraction),(670373105607363776761/847603527915396471237:Fraction),(426564008142093821338/539373457158293208969:Fraction),(4691796507119025132712/5932991362074675298659:Fraction),(14074166734020275626664/17798624086224375895977:Fraction),(4690981302227123206180/5932758028741575298659:Fraction),(14071721281098535402583/17797924086225075895977:Fraction),(70352494286414591282746/88987870431127129479885:Fraction),(200417042642230626551/253521710629996807635:Fraction),(70340269448532330231388/88984370431130629479885:Fraction),(23444719312863501485408/29660873477044126493295:Fraction),(2604742497690903913246/3295587793745708499255:Fraction),(23440645578971682239096/29659706810378626493295:Fraction),(426156520220519843438/539256790491743208969:Fraction),(7812190660552766573602/9886180047904375497765:Fraction),(520767459723986056475/659065706897341699851:Fraction),(70297497980809548859411/88972120431142879479885:Fraction),(520676962282508341876/659039780971441699851:Fraction),(70285281635831635652582/88968620431146379479885:Fraction),(14055834632780137876340/17793374086229625895977:Fraction),(173513742472444452188/219666964027530566617:Fraction),(70266959248206470978036/88963370431151629479885:Fraction),(14052170519109411216952/17792324086230675895977:Fraction),(3345464140590395637664/4236184306245482356185:Fraction),(1898611921885895777236/2404273525166402148105:Fraction),(70242535067699881961888/88956370431158629479885:Fraction),(7804047781694007173513/9883846714573375497765:Fraction),(14046065202494224441097/17790574086232425895977:Fraction),(371556729049397365942/470640848842136928465:Fraction),(2600671058443135217024/3294421127080208499255:Fraction),(23404005055429184977792/29649206810389126493295:Fraction),(2005883221841677372933/2541310583747689413711:Fraction)]
abbrev p481 := params 0
abbrev ray481 := rays 0
def bank481 : Fin 1 → Cell := oneBank p481 ray481
theorem signs481 : ∀ j, Signs p481 (bank481 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p482 := params 1
abbrev ray482 := rays 1
def bank482 : Fin 1 → Cell := oneBank p482 ray482
theorem signs482 : ∀ j, Signs p482 (bank482 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p483 := params 2
abbrev ray483 := rays 2
def bank483 : Fin 1 → Cell := oneBank p483 ray483
theorem signs483 : ∀ j, Signs p483 (bank483 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p484 := params 3
abbrev ray484 := rays 3
def bank484 : Fin 1 → Cell := oneBank p484 ray484
theorem signs484 : ∀ j, Signs p484 (bank484 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p485 := params 4
abbrev ray485 := rays 4
def bank485 : Fin 1 → Cell := oneBank p485 ray485
theorem signs485 : ∀ j, Signs p485 (bank485 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p486 := params 5
abbrev ray486 := rays 5
def bank486 : Fin 1 → Cell := oneBank p486 ray486
theorem signs486 : ∀ j, Signs p486 (bank486 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p487 := params 6
abbrev ray487 := rays 6
def bank487 : Fin 1 → Cell := oneBank p487 ray487
theorem signs487 : ∀ j, Signs p487 (bank487 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p488 := params 7
abbrev ray488 := rays 7
def bank488 : Fin 1 → Cell := oneBank p488 ray488
theorem signs488 : ∀ j, Signs p488 (bank488 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p489 := params 8
abbrev ray489 := rays 8
def bank489 : Fin 1 → Cell := oneBank p489 ray489
theorem signs489 : ∀ j, Signs p489 (bank489 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p490 := params 9
abbrev ray490 := rays 9
def bank490 : Fin 1 → Cell := oneBank p490 ray490
theorem signs490 : ∀ j, Signs p490 (bank490 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p491 := params 10
abbrev ray491 := rays 10
def bank491 : Fin 1 → Cell := oneBank p491 ray491
theorem signs491 : ∀ j, Signs p491 (bank491 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p492 := params 11
abbrev ray492 := rays 11
def bank492 : Fin 1 → Cell := oneBank p492 ray492
theorem signs492 : ∀ j, Signs p492 (bank492 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p493 := params 12
abbrev ray493 := rays 12
def bank493 : Fin 1 → Cell := oneBank p493 ray493
theorem signs493 : ∀ j, Signs p493 (bank493 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p494 := params 13
abbrev ray494 := rays 13
def bank494 : Fin 1 → Cell := oneBank p494 ray494
theorem signs494 : ∀ j, Signs p494 (bank494 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p495 := params 14
abbrev ray495 := rays 14
def bank495 : Fin 1 → Cell := oneBank p495 ray495
theorem signs495 : ∀ j, Signs p495 (bank495 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p496 := params 15
abbrev ray496 := rays 15
def bank496 : Fin 1 → Cell := oneBank p496 ray496
theorem signs496 : ∀ j, Signs p496 (bank496 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p497 := params 16
abbrev ray497 := rays 16
def bank497 : Fin 1 → Cell := oneBank p497 ray497
theorem signs497 : ∀ j, Signs p497 (bank497 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p498 := params 17
abbrev ray498 := rays 17
def bank498 : Fin 1 → Cell := oneBank p498 ray498
theorem signs498 : ∀ j, Signs p498 (bank498 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p499 := params 18
abbrev ray499 := rays 18
def bank499 : Fin 1 → Cell := oneBank p499 ray499
theorem signs499 : ∀ j, Signs p499 (bank499 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p500 := params 19
abbrev ray500 := rays 19
def bank500 : Fin 1 → Cell := oneBank p500 ray500
theorem signs500 : ∀ j, Signs p500 (bank500 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p501 := params 20
abbrev ray501 := rays 20
def bank501 : Fin 1 → Cell := oneBank p501 ray501
theorem signs501 : ∀ j, Signs p501 (bank501 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p502 := params 21
abbrev ray502 := rays 21
def bank502 : Fin 1 → Cell := oneBank p502 ray502
theorem signs502 : ∀ j, Signs p502 (bank502 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p503 := params 22
abbrev ray503 := rays 22
def bank503 : Fin 1 → Cell := oneBank p503 ray503
theorem signs503 : ∀ j, Signs p503 (bank503 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p504 := params 23
abbrev ray504 := rays 23
def bank504 : Fin 1 → Cell := oneBank p504 ray504
theorem signs504 : ∀ j, Signs p504 (bank504 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p505 := params 24
abbrev ray505 := rays 24
def bank505 : Fin 1 → Cell := oneBank p505 ray505
theorem signs505 : ∀ j, Signs p505 (bank505 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p506 := params 25
abbrev ray506 := rays 25
def bank506 : Fin 1 → Cell := oneBank p506 ray506
theorem signs506 : ∀ j, Signs p506 (bank506 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p507 := params 26
abbrev ray507 := rays 26
def bank507 : Fin 1 → Cell := oneBank p507 ray507
theorem signs507 : ∀ j, Signs p507 (bank507 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p508 := params 27
abbrev ray508 := rays 27
def bank508 : Fin 1 → Cell := oneBank p508 ray508
theorem signs508 : ∀ j, Signs p508 (bank508 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p509 := params 28
abbrev ray509 := rays 28
def bank509 : Fin 1 → Cell := oneBank p509 ray509
theorem signs509 : ∀ j, Signs p509 (bank509 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p510 := params 29
abbrev ray510 := rays 29
def bank510 : Fin 1 → Cell := oneBank p510 ray510
theorem signs510 : ∀ j, Signs p510 (bank510 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p511 := params 30
abbrev ray511 := rays 30
def bank511 : Fin 1 → Cell := oneBank p511 ray511
theorem signs511 : ∀ j, Signs p511 (bank511 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p512 := params 31
abbrev ray512 := rays 31
def bank512 : Fin 1 → Cell := oneBank p512 ray512
theorem signs512 : ∀ j, Signs p512 (bank512 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00481_00512
