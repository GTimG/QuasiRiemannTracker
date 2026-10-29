/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00609_00640
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99917007668897,99916862959171,99916718223062,99916573460574,99916428671709,99916283856470,99916139014860,99915994146881,99915849252536,99915704331828,99915559384759,99915414411332,99915269411551,99915124385417,99914979332934,99914834254103,99914689148928,99914544017412,99914398859557,99914253675366,99914108464842,99913963227987,99913817964803,99913672675294,99913527359462,99913382017311,99913236648842,99913091254059,99912945832964,99912800385560,99912654911850,99912509411836,99912363885521]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (608+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(23205300029688071508566/29592040143779626493295:Fraction),(13921967756926690202512/17754874086268125895977:Fraction),(13920755214617867411536/17754524086268475895977:Fraction),(859231041673845197864/1095936671991902833085:Fraction),(9941664813166439997806/12681302918763697068555:Fraction),(4639039520818559866480/5917824695423175298659:Fraction),(4638635529771147286042/5917708028756625298659:Fraction),(69573472884439587151351/88763870431351129479885:Fraction),(13913482767314047324972/17752424086270575895977:Fraction),(23187118197446505482774/29586790143784876493295:Fraction),(69555296362449833444981/88758620431356379479885:Fraction),(23183079312084209063486/29585623477119376493295:Fraction),(662316004995063081910/845286861251046471237:Fraction),(69537122916456932365627/88753370431361629479885:Fraction),(69531066322941183342272/88751620431363379479885:Fraction),(1545000211849457154829/1972219342919225099553:Fraction),(69518953758101629825724/88748120431366879479885:Fraction),(23170965928944683860574/29582123477122876493295:Fraction),(220656643905526528865/281728953750382157079:Fraction),(69500787677557829219104/88742870431372129479885:Fraction),(69494733539633091876728/88741120431373879479885:Fraction),(208674712329346292261/266484595890016905345:Fraction),(13896525177310262453881/17747524086275475895977:Fraction),(69476573582327679008048/88735870431379129479885:Fraction),(7718946652363428701504/9859346714597875497765:Fraction),(69464468386073701339316/88732370431382629479885:Fraction),(69458416704989991991528/88730620431384379479885:Fraction),(23150788276011322992736/29576290143795376493295:Fraction),(23148771322056039249518/29575706810462626493295:Fraction),(13888052581696740725020/17745074086277925895977:Fraction),(514327502710913354600/657212003195491699851:Fraction),(13885632525539615891860/17744374086278625895977:Fraction)]
abbrev p609 := params 0
abbrev ray609 := rays 0
def bank609 : Fin 1 → Cell := oneBank p609 ray609
theorem signs609 : ∀ j, Signs p609 (bank609 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p610 := params 1
abbrev ray610 := rays 1
def bank610 : Fin 1 → Cell := oneBank p610 ray610
theorem signs610 : ∀ j, Signs p610 (bank610 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p611 := params 2
abbrev ray611 := rays 2
def bank611 : Fin 1 → Cell := oneBank p611 ray611
theorem signs611 : ∀ j, Signs p611 (bank611 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p612 := params 3
abbrev ray612 := rays 3
def bank612 : Fin 1 → Cell := oneBank p612 ray612
theorem signs612 : ∀ j, Signs p612 (bank612 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p613 := params 4
abbrev ray613 := rays 4
def bank613 : Fin 1 → Cell := oneBank p613 ray613
theorem signs613 : ∀ j, Signs p613 (bank613 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p614 := params 5
abbrev ray614 := rays 5
def bank614 : Fin 1 → Cell := oneBank p614 ray614
theorem signs614 : ∀ j, Signs p614 (bank614 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p615 := params 6
abbrev ray615 := rays 6
def bank615 : Fin 1 → Cell := oneBank p615 ray615
theorem signs615 : ∀ j, Signs p615 (bank615 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p616 := params 7
abbrev ray616 := rays 7
def bank616 : Fin 1 → Cell := oneBank p616 ray616
theorem signs616 : ∀ j, Signs p616 (bank616 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p617 := params 8
abbrev ray617 := rays 8
def bank617 : Fin 1 → Cell := oneBank p617 ray617
theorem signs617 : ∀ j, Signs p617 (bank617 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p618 := params 9
abbrev ray618 := rays 9
def bank618 : Fin 1 → Cell := oneBank p618 ray618
theorem signs618 : ∀ j, Signs p618 (bank618 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p619 := params 10
abbrev ray619 := rays 10
def bank619 : Fin 1 → Cell := oneBank p619 ray619
theorem signs619 : ∀ j, Signs p619 (bank619 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p620 := params 11
abbrev ray620 := rays 11
def bank620 : Fin 1 → Cell := oneBank p620 ray620
theorem signs620 : ∀ j, Signs p620 (bank620 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p621 := params 12
abbrev ray621 := rays 12
def bank621 : Fin 1 → Cell := oneBank p621 ray621
theorem signs621 : ∀ j, Signs p621 (bank621 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p622 := params 13
abbrev ray622 := rays 13
def bank622 : Fin 1 → Cell := oneBank p622 ray622
theorem signs622 : ∀ j, Signs p622 (bank622 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p623 := params 14
abbrev ray623 := rays 14
def bank623 : Fin 1 → Cell := oneBank p623 ray623
theorem signs623 : ∀ j, Signs p623 (bank623 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p624 := params 15
abbrev ray624 := rays 15
def bank624 : Fin 1 → Cell := oneBank p624 ray624
theorem signs624 : ∀ j, Signs p624 (bank624 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p625 := params 16
abbrev ray625 := rays 16
def bank625 : Fin 1 → Cell := oneBank p625 ray625
theorem signs625 : ∀ j, Signs p625 (bank625 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p626 := params 17
abbrev ray626 := rays 17
def bank626 : Fin 1 → Cell := oneBank p626 ray626
theorem signs626 : ∀ j, Signs p626 (bank626 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p627 := params 18
abbrev ray627 := rays 18
def bank627 : Fin 1 → Cell := oneBank p627 ray627
theorem signs627 : ∀ j, Signs p627 (bank627 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p628 := params 19
abbrev ray628 := rays 19
def bank628 : Fin 1 → Cell := oneBank p628 ray628
theorem signs628 : ∀ j, Signs p628 (bank628 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p629 := params 20
abbrev ray629 := rays 20
def bank629 : Fin 1 → Cell := oneBank p629 ray629
theorem signs629 : ∀ j, Signs p629 (bank629 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p630 := params 21
abbrev ray630 := rays 21
def bank630 : Fin 1 → Cell := oneBank p630 ray630
theorem signs630 : ∀ j, Signs p630 (bank630 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p631 := params 22
abbrev ray631 := rays 22
def bank631 : Fin 1 → Cell := oneBank p631 ray631
theorem signs631 : ∀ j, Signs p631 (bank631 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p632 := params 23
abbrev ray632 := rays 23
def bank632 : Fin 1 → Cell := oneBank p632 ray632
theorem signs632 : ∀ j, Signs p632 (bank632 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p633 := params 24
abbrev ray633 := rays 24
def bank633 : Fin 1 → Cell := oneBank p633 ray633
theorem signs633 : ∀ j, Signs p633 (bank633 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p634 := params 25
abbrev ray634 := rays 25
def bank634 : Fin 1 → Cell := oneBank p634 ray634
theorem signs634 : ∀ j, Signs p634 (bank634 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p635 := params 26
abbrev ray635 := rays 26
def bank635 : Fin 1 → Cell := oneBank p635 ray635
theorem signs635 : ∀ j, Signs p635 (bank635 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p636 := params 27
abbrev ray636 := rays 27
def bank636 : Fin 1 → Cell := oneBank p636 ray636
theorem signs636 : ∀ j, Signs p636 (bank636 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p637 := params 28
abbrev ray637 := rays 28
def bank637 : Fin 1 → Cell := oneBank p637 ray637
theorem signs637 : ∀ j, Signs p637 (bank637 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p638 := params 29
abbrev ray638 := rays 29
def bank638 : Fin 1 → Cell := oneBank p638 ray638
theorem signs638 : ∀ j, Signs p638 (bank638 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p639 := params 30
abbrev ray639 := rays 30
def bank639 : Fin 1 → Cell := oneBank p639 ray639
theorem signs639 : ∀ j, Signs p639 (bank639 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p640 := params 31
abbrev ray640 := rays 31
def bank640 : Fin 1 → Cell := oneBank p640 ray640
theorem signs640 : ∀ j, Signs p640 (bank640 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00609_00640
