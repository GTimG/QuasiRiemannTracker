/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00641_00672
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99912363885521,99912218332908,99912072753999,99911927148797,99911781517304,99911635859524,99911490175459,99911344465112,99911198728486,99911052965583,99910907176405,99910761360956,99910615519238,99910469651254,99910323757007,99910177836499,99910031889733,99909885916711,99909739917437,99909593891913,99909447840141,99909301762125,99909155657867,99909009527370,99908863370636,99908717187669,99908570978470,99908424743042,99908278481389,99908132193512,99907985879415,99907839539100,99907693172569]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (640+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(69422113404679493937961/88720120431394879479885:Fraction),(23138687995317006474752/29572790143798876493295:Fraction),(23136671860853931526702/29572206810466126493295:Fraction),(69403968194568164838319/88714870431400129479885:Fraction),(11480218463351374832/14675454165657879153:Fraction),(2570069364138840690166/3285606312274208499255:Fraction),(23128608689347991491541/29569873477135126493295:Fraction),(1101266335060185554674/1408061435419160785395:Fraction),(69373733165128819937536/88706120431408879479885:Fraction),(23122562745703494662242/29568123477136876493295:Fraction),(4624109540909263457156/5913508028760825298659:Fraction),(69355597794728425991884/88700870431414129479885:Fraction),(69349553491572422803328/88699120431415879479885:Fraction),(7704834332559010242688/9855263381268625497765:Fraction),(1612499197914605158064/2062688847242311150695:Fraction),(13866284608703661826021/17738774086284225895977:Fraction),(7702820042379864984998/9854680047935875497765:Fraction),(1414680357633494569607/1810007559824992438365:Fraction),(9901899383238310955113/12669802918775197068555:Fraction),(3300345411717710921069/4223184306258482356185:Fraction),(23100404208520490335178/29561706810476626493295:Fraction),(13859034524238856034570/17736674086286325895977:Fraction),(1215598814415778317058/1555817902305848762805:Fraction),(659838971686568539160/844570194585096471237:Fraction),(23092350882910658289646/29559373477145626493295:Fraction),(1099539909312439072861/1407561435419660785395:Fraction),(13852995145922965345504/17734924086288075895977:Fraction),(1539087488389743019660/1970508231809825099553:Fraction),(4616859949458753110276/5911408028762925298659:Fraction),(6295169320245204955672/8060851857404148134535:Fraction),(13848165121720450740116/17733524086289475895977:Fraction),(1538550882468088350590/1970352676254425099553:Fraction)]
abbrev p641 := params 0
abbrev ray641 := rays 0
def bank641 : Fin 1 → Cell := oneBank p641 ray641
theorem signs641 : ∀ j, Signs p641 (bank641 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p642 := params 1
abbrev ray642 := rays 1
def bank642 : Fin 1 → Cell := oneBank p642 ray642
theorem signs642 : ∀ j, Signs p642 (bank642 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p643 := params 2
abbrev ray643 := rays 2
def bank643 : Fin 1 → Cell := oneBank p643 ray643
theorem signs643 : ∀ j, Signs p643 (bank643 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p644 := params 3
abbrev ray644 := rays 3
def bank644 : Fin 1 → Cell := oneBank p644 ray644
theorem signs644 : ∀ j, Signs p644 (bank644 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p645 := params 4
abbrev ray645 := rays 4
def bank645 : Fin 1 → Cell := oneBank p645 ray645
theorem signs645 : ∀ j, Signs p645 (bank645 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p646 := params 5
abbrev ray646 := rays 5
def bank646 : Fin 1 → Cell := oneBank p646 ray646
theorem signs646 : ∀ j, Signs p646 (bank646 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p647 := params 6
abbrev ray647 := rays 6
def bank647 : Fin 1 → Cell := oneBank p647 ray647
theorem signs647 : ∀ j, Signs p647 (bank647 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p648 := params 7
abbrev ray648 := rays 7
def bank648 : Fin 1 → Cell := oneBank p648 ray648
theorem signs648 : ∀ j, Signs p648 (bank648 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p649 := params 8
abbrev ray649 := rays 8
def bank649 : Fin 1 → Cell := oneBank p649 ray649
theorem signs649 : ∀ j, Signs p649 (bank649 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p650 := params 9
abbrev ray650 := rays 9
def bank650 : Fin 1 → Cell := oneBank p650 ray650
theorem signs650 : ∀ j, Signs p650 (bank650 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p651 := params 10
abbrev ray651 := rays 10
def bank651 : Fin 1 → Cell := oneBank p651 ray651
theorem signs651 : ∀ j, Signs p651 (bank651 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p652 := params 11
abbrev ray652 := rays 11
def bank652 : Fin 1 → Cell := oneBank p652 ray652
theorem signs652 : ∀ j, Signs p652 (bank652 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p653 := params 12
abbrev ray653 := rays 12
def bank653 : Fin 1 → Cell := oneBank p653 ray653
theorem signs653 : ∀ j, Signs p653 (bank653 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p654 := params 13
abbrev ray654 := rays 13
def bank654 : Fin 1 → Cell := oneBank p654 ray654
theorem signs654 : ∀ j, Signs p654 (bank654 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p655 := params 14
abbrev ray655 := rays 14
def bank655 : Fin 1 → Cell := oneBank p655 ray655
theorem signs655 : ∀ j, Signs p655 (bank655 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p656 := params 15
abbrev ray656 := rays 15
def bank656 : Fin 1 → Cell := oneBank p656 ray656
theorem signs656 : ∀ j, Signs p656 (bank656 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p657 := params 16
abbrev ray657 := rays 16
def bank657 : Fin 1 → Cell := oneBank p657 ray657
theorem signs657 : ∀ j, Signs p657 (bank657 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p658 := params 17
abbrev ray658 := rays 17
def bank658 : Fin 1 → Cell := oneBank p658 ray658
theorem signs658 : ∀ j, Signs p658 (bank658 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p659 := params 18
abbrev ray659 := rays 18
def bank659 : Fin 1 → Cell := oneBank p659 ray659
theorem signs659 : ∀ j, Signs p659 (bank659 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p660 := params 19
abbrev ray660 := rays 19
def bank660 : Fin 1 → Cell := oneBank p660 ray660
theorem signs660 : ∀ j, Signs p660 (bank660 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p661 := params 20
abbrev ray661 := rays 20
def bank661 : Fin 1 → Cell := oneBank p661 ray661
theorem signs661 : ∀ j, Signs p661 (bank661 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p662 := params 21
abbrev ray662 := rays 21
def bank662 : Fin 1 → Cell := oneBank p662 ray662
theorem signs662 : ∀ j, Signs p662 (bank662 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p663 := params 22
abbrev ray663 := rays 22
def bank663 : Fin 1 → Cell := oneBank p663 ray663
theorem signs663 : ∀ j, Signs p663 (bank663 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p664 := params 23
abbrev ray664 := rays 23
def bank664 : Fin 1 → Cell := oneBank p664 ray664
theorem signs664 : ∀ j, Signs p664 (bank664 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p665 := params 24
abbrev ray665 := rays 24
def bank665 : Fin 1 → Cell := oneBank p665 ray665
theorem signs665 : ∀ j, Signs p665 (bank665 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p666 := params 25
abbrev ray666 := rays 25
def bank666 : Fin 1 → Cell := oneBank p666 ray666
theorem signs666 : ∀ j, Signs p666 (bank666 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p667 := params 26
abbrev ray667 := rays 26
def bank667 : Fin 1 → Cell := oneBank p667 ray667
theorem signs667 : ∀ j, Signs p667 (bank667 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p668 := params 27
abbrev ray668 := rays 27
def bank668 : Fin 1 → Cell := oneBank p668 ray668
theorem signs668 : ∀ j, Signs p668 (bank668 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p669 := params 28
abbrev ray669 := rays 28
def bank669 : Fin 1 → Cell := oneBank p669 ray669
theorem signs669 : ∀ j, Signs p669 (bank669 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p670 := params 29
abbrev ray670 := rays 29
def bank670 : Fin 1 → Cell := oneBank p670 ray670
theorem signs670 : ∀ j, Signs p670 (bank670 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p671 := params 30
abbrev ray671 := rays 30
def bank671 : Fin 1 → Cell := oneBank p671 ray671
theorem signs671 : ∀ j, Signs p671 (bank671 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p672 := params 31
abbrev ray672 := rays 31
def bank672 : Fin 1 → Cell := oneBank p672 ray672
theorem signs672 : ∀ j, Signs p672 (bank672 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00641_00672
