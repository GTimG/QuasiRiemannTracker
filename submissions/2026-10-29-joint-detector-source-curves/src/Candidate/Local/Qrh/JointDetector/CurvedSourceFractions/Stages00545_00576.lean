/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00545_00576
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99926214091492,99926071075914,99925928033778,99925784965087,99925641869844,99925498748051,99925355599712,99925212424829,99925069223404,99924925995441,99924782740943,99924639459912,99924496152351,99924352818262,99924209457649,99924066070514,99923922656860,99923779216690,99923635750006,99923492256811,99923348737109,99923205190901,99923061618190,99922918018980,99922774393273,99922630741071,99922487062378,99922343357196,99922199625528,99922055867377,99921912082745,99921768271635,99921624434050]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (544+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(70004749609463822234068/88888120431226879479885:Fraction),(23332887002711240149156/29628790143742876493295:Fraction),(13998514441697618680192/17776924086246075895977:Fraction),(864030671854357373498/1097319388039902833085:Fraction),(7775599738148332517134/9875680047914875497765:Fraction),(23324769819518727903101/29626456810411876493295:Fraction),(3331820166426488587678/4232267639582732356185:Fraction),(14006433900539074319/17792967053301127023:Fraction),(23318683657759144066238/29624706810413626493295:Fraction),(9992852232139242481304/12696052918748947068555:Fraction),(4662925338571795111975/5924708028749625298659:Fraction),(9991113649124976970258/12695552918749447068555:Fraction),(23310570270377299824167/29622373477082626493295:Fraction),(1553902824225951198976/1974786009583325099553:Fraction),(13983908876208087624392/17772724086250275895977:Fraction),(1997527470684816378368/2538910583750089413711:Fraction),(517832432362706718800/658223114305591699851:Fraction),(13980259255181958827308/17771674086251325895977:Fraction),(69895213984977032249312/88856620431258379479885:Fraction),(123261256977204489692/156710529861128976155:Fraction),(69883052439261396196853/88853120431261879479885:Fraction),(4658464798311133212994/5923424695417575298659:Fraction),(4658059420820329095608/5923308028751025298659:Fraction),(1552551370269826222958/1974397120694825099553:Fraction),(180513522026444831158/229576538582090127855:Fraction),(862378446773515077967/1096844079398402833085:Fraction),(1108675796117750528032/1410200324305910785395:Fraction),(69840497134547302956788/88840870431274129479885:Fraction),(23278139638691137173784/29613040143758626493295:Fraction),(69828341710049247028597/88837370431277629479885:Fraction),(13964453103306041584921/17767124086255875895977:Fraction),(1551470869455654921631/1974086009584025099553:Fraction)]
abbrev p545 := params 0
abbrev ray545 := rays 0
def bank545 : Fin 1 → Cell := oneBank p545 ray545
theorem signs545 : ∀ j, Signs p545 (bank545 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p546 := params 1
abbrev ray546 := rays 1
def bank546 : Fin 1 → Cell := oneBank p546 ray546
theorem signs546 : ∀ j, Signs p546 (bank546 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p547 := params 2
abbrev ray547 := rays 2
def bank547 : Fin 1 → Cell := oneBank p547 ray547
theorem signs547 : ∀ j, Signs p547 (bank547 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p548 := params 3
abbrev ray548 := rays 3
def bank548 : Fin 1 → Cell := oneBank p548 ray548
theorem signs548 : ∀ j, Signs p548 (bank548 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p549 := params 4
abbrev ray549 := rays 4
def bank549 : Fin 1 → Cell := oneBank p549 ray549
theorem signs549 : ∀ j, Signs p549 (bank549 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p550 := params 5
abbrev ray550 := rays 5
def bank550 : Fin 1 → Cell := oneBank p550 ray550
theorem signs550 : ∀ j, Signs p550 (bank550 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p551 := params 6
abbrev ray551 := rays 6
def bank551 : Fin 1 → Cell := oneBank p551 ray551
theorem signs551 : ∀ j, Signs p551 (bank551 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p552 := params 7
abbrev ray552 := rays 7
def bank552 : Fin 1 → Cell := oneBank p552 ray552
theorem signs552 : ∀ j, Signs p552 (bank552 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p553 := params 8
abbrev ray553 := rays 8
def bank553 : Fin 1 → Cell := oneBank p553 ray553
theorem signs553 : ∀ j, Signs p553 (bank553 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p554 := params 9
abbrev ray554 := rays 9
def bank554 : Fin 1 → Cell := oneBank p554 ray554
theorem signs554 : ∀ j, Signs p554 (bank554 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p555 := params 10
abbrev ray555 := rays 10
def bank555 : Fin 1 → Cell := oneBank p555 ray555
theorem signs555 : ∀ j, Signs p555 (bank555 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p556 := params 11
abbrev ray556 := rays 11
def bank556 : Fin 1 → Cell := oneBank p556 ray556
theorem signs556 : ∀ j, Signs p556 (bank556 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p557 := params 12
abbrev ray557 := rays 12
def bank557 : Fin 1 → Cell := oneBank p557 ray557
theorem signs557 : ∀ j, Signs p557 (bank557 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p558 := params 13
abbrev ray558 := rays 13
def bank558 : Fin 1 → Cell := oneBank p558 ray558
theorem signs558 : ∀ j, Signs p558 (bank558 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p559 := params 14
abbrev ray559 := rays 14
def bank559 : Fin 1 → Cell := oneBank p559 ray559
theorem signs559 : ∀ j, Signs p559 (bank559 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p560 := params 15
abbrev ray560 := rays 15
def bank560 : Fin 1 → Cell := oneBank p560 ray560
theorem signs560 : ∀ j, Signs p560 (bank560 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p561 := params 16
abbrev ray561 := rays 16
def bank561 : Fin 1 → Cell := oneBank p561 ray561
theorem signs561 : ∀ j, Signs p561 (bank561 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p562 := params 17
abbrev ray562 := rays 17
def bank562 : Fin 1 → Cell := oneBank p562 ray562
theorem signs562 : ∀ j, Signs p562 (bank562 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p563 := params 18
abbrev ray563 := rays 18
def bank563 : Fin 1 → Cell := oneBank p563 ray563
theorem signs563 : ∀ j, Signs p563 (bank563 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p564 := params 19
abbrev ray564 := rays 19
def bank564 : Fin 1 → Cell := oneBank p564 ray564
theorem signs564 : ∀ j, Signs p564 (bank564 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p565 := params 20
abbrev ray565 := rays 20
def bank565 : Fin 1 → Cell := oneBank p565 ray565
theorem signs565 : ∀ j, Signs p565 (bank565 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p566 := params 21
abbrev ray566 := rays 21
def bank566 : Fin 1 → Cell := oneBank p566 ray566
theorem signs566 : ∀ j, Signs p566 (bank566 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p567 := params 22
abbrev ray567 := rays 22
def bank567 : Fin 1 → Cell := oneBank p567 ray567
theorem signs567 : ∀ j, Signs p567 (bank567 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p568 := params 23
abbrev ray568 := rays 23
def bank568 : Fin 1 → Cell := oneBank p568 ray568
theorem signs568 : ∀ j, Signs p568 (bank568 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p569 := params 24
abbrev ray569 := rays 24
def bank569 : Fin 1 → Cell := oneBank p569 ray569
theorem signs569 : ∀ j, Signs p569 (bank569 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p570 := params 25
abbrev ray570 := rays 25
def bank570 : Fin 1 → Cell := oneBank p570 ray570
theorem signs570 : ∀ j, Signs p570 (bank570 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p571 := params 26
abbrev ray571 := rays 26
def bank571 : Fin 1 → Cell := oneBank p571 ray571
theorem signs571 : ∀ j, Signs p571 (bank571 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p572 := params 27
abbrev ray572 := rays 27
def bank572 : Fin 1 → Cell := oneBank p572 ray572
theorem signs572 : ∀ j, Signs p572 (bank572 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p573 := params 28
abbrev ray573 := rays 28
def bank573 : Fin 1 → Cell := oneBank p573 ray573
theorem signs573 : ∀ j, Signs p573 (bank573 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p574 := params 29
abbrev ray574 := rays 29
def bank574 : Fin 1 → Cell := oneBank p574 ray574
theorem signs574 : ∀ j, Signs p574 (bank574 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p575 := params 30
abbrev ray575 := rays 30
def bank575 : Fin 1 → Cell := oneBank p575 ray575
theorem signs575 : ∀ j, Signs p575 (bank575 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p576 := params 31
abbrev ray576 := rays 31
def bank576 : Fin 1 → Cell := oneBank p576 ray576
theorem signs576 : ∀ j, Signs p576 (bank576 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00545_00576
