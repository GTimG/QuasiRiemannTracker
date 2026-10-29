/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00577_00608
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99921624434050,99921480569993,99921336679467,99921192762474,99921048819017,99920904849098,99920760852720,99920616829887,99920472780601,99920328704864,99920184602679,99920040474050,99919896318979,99919752137468,99919607929520,99919463695138,99919319434325,99919175147084,99919030833417,99918886493327,99918742126817,99918597733889,99918453314546,99918308868791,99918164396626,99918019898055,99917875373080,99917730821704,99917586243929,99917441639758,99917297009194,99917152352239,99917007668897]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (576+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(13962022507397040086900/17766424086256575895977:Fraction),(69804036961082942896732/88830370431284629479885:Fraction),(23265987465951431212546/29609540143762126493295:Fraction),(1107807740273464900192/1409950324306160785395:Fraction),(69785812679218082147398/88825120431289879479885:Fraction),(7753304438238467654872/9869263381254625497765:Fraction),(516841968900765620734/657937929120691699851:Fraction),(69767592671928959149553/88819870431295129479885:Fraction),(7751280061686485656358/9868680047921875497765:Fraction),(13951089648238750628230/17763274086259725895977:Fraction),(9964196532855463852316/12687802918757197068555:Fraction),(1549851205151518822040/1973619342917825099553:Fraction),(69737233746739399268513/88811120431303879479885:Fraction),(23243721021511885290352/29603123477101876493295:Fraction),(664048508528626766752/845786861250546471237:Fraction),(69719023529406374972512/88805870431309129479885:Fraction),(4647530231083365140800/5920274695420725298659:Fraction),(7745209379597801803102/9866930047923625497765:Fraction),(1991451896567169034127/2537160583751839413711:Fraction),(69694748146361194659961/88798870431316129479885:Fraction),(7229866264788520616/9212275177022292715:Fraction),(23227537836441815871863/29598456810439876493295:Fraction),(13935309179092200361256/17758724086264275895977:Fraction),(4644698619675473823262/5919458028754875298659:Fraction),(23221471236131355318092/29596706810441626493295:Fraction),(13931669584971975878932/17757674086265325895977:Fraction),(1547828514555569395556/1973036009585075099553:Fraction),(6331474380763559289184/8071351857393648134535:Fraction),(69640154235555467018401/88783120431331879479885:Fraction),(23211363362007829547152/29593790143777876493295:Fraction),(23209342316777782189768/29593206810445126493295:Fraction),(13924392723601764304990/17755574086267425895977:Fraction)]
abbrev p577 := params 0
abbrev ray577 := rays 0
def bank577 : Fin 1 → Cell := oneBank p577 ray577
theorem signs577 : ∀ j, Signs p577 (bank577 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p578 := params 1
abbrev ray578 := rays 1
def bank578 : Fin 1 → Cell := oneBank p578 ray578
theorem signs578 : ∀ j, Signs p578 (bank578 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p579 := params 2
abbrev ray579 := rays 2
def bank579 : Fin 1 → Cell := oneBank p579 ray579
theorem signs579 : ∀ j, Signs p579 (bank579 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p580 := params 3
abbrev ray580 := rays 3
def bank580 : Fin 1 → Cell := oneBank p580 ray580
theorem signs580 : ∀ j, Signs p580 (bank580 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p581 := params 4
abbrev ray581 := rays 4
def bank581 : Fin 1 → Cell := oneBank p581 ray581
theorem signs581 : ∀ j, Signs p581 (bank581 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p582 := params 5
abbrev ray582 := rays 5
def bank582 : Fin 1 → Cell := oneBank p582 ray582
theorem signs582 : ∀ j, Signs p582 (bank582 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p583 := params 6
abbrev ray583 := rays 6
def bank583 : Fin 1 → Cell := oneBank p583 ray583
theorem signs583 : ∀ j, Signs p583 (bank583 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p584 := params 7
abbrev ray584 := rays 7
def bank584 : Fin 1 → Cell := oneBank p584 ray584
theorem signs584 : ∀ j, Signs p584 (bank584 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p585 := params 8
abbrev ray585 := rays 8
def bank585 : Fin 1 → Cell := oneBank p585 ray585
theorem signs585 : ∀ j, Signs p585 (bank585 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p586 := params 9
abbrev ray586 := rays 9
def bank586 : Fin 1 → Cell := oneBank p586 ray586
theorem signs586 : ∀ j, Signs p586 (bank586 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p587 := params 10
abbrev ray587 := rays 10
def bank587 : Fin 1 → Cell := oneBank p587 ray587
theorem signs587 : ∀ j, Signs p587 (bank587 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p588 := params 11
abbrev ray588 := rays 11
def bank588 : Fin 1 → Cell := oneBank p588 ray588
theorem signs588 : ∀ j, Signs p588 (bank588 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p589 := params 12
abbrev ray589 := rays 12
def bank589 : Fin 1 → Cell := oneBank p589 ray589
theorem signs589 : ∀ j, Signs p589 (bank589 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p590 := params 13
abbrev ray590 := rays 13
def bank590 : Fin 1 → Cell := oneBank p590 ray590
theorem signs590 : ∀ j, Signs p590 (bank590 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p591 := params 14
abbrev ray591 := rays 14
def bank591 : Fin 1 → Cell := oneBank p591 ray591
theorem signs591 : ∀ j, Signs p591 (bank591 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p592 := params 15
abbrev ray592 := rays 15
def bank592 : Fin 1 → Cell := oneBank p592 ray592
theorem signs592 : ∀ j, Signs p592 (bank592 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p593 := params 16
abbrev ray593 := rays 16
def bank593 : Fin 1 → Cell := oneBank p593 ray593
theorem signs593 : ∀ j, Signs p593 (bank593 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p594 := params 17
abbrev ray594 := rays 17
def bank594 : Fin 1 → Cell := oneBank p594 ray594
theorem signs594 : ∀ j, Signs p594 (bank594 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p595 := params 18
abbrev ray595 := rays 18
def bank595 : Fin 1 → Cell := oneBank p595 ray595
theorem signs595 : ∀ j, Signs p595 (bank595 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p596 := params 19
abbrev ray596 := rays 19
def bank596 : Fin 1 → Cell := oneBank p596 ray596
theorem signs596 : ∀ j, Signs p596 (bank596 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p597 := params 20
abbrev ray597 := rays 20
def bank597 : Fin 1 → Cell := oneBank p597 ray597
theorem signs597 : ∀ j, Signs p597 (bank597 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p598 := params 21
abbrev ray598 := rays 21
def bank598 : Fin 1 → Cell := oneBank p598 ray598
theorem signs598 : ∀ j, Signs p598 (bank598 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p599 := params 22
abbrev ray599 := rays 22
def bank599 : Fin 1 → Cell := oneBank p599 ray599
theorem signs599 : ∀ j, Signs p599 (bank599 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p600 := params 23
abbrev ray600 := rays 23
def bank600 : Fin 1 → Cell := oneBank p600 ray600
theorem signs600 : ∀ j, Signs p600 (bank600 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p601 := params 24
abbrev ray601 := rays 24
def bank601 : Fin 1 → Cell := oneBank p601 ray601
theorem signs601 : ∀ j, Signs p601 (bank601 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p602 := params 25
abbrev ray602 := rays 25
def bank602 : Fin 1 → Cell := oneBank p602 ray602
theorem signs602 : ∀ j, Signs p602 (bank602 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p603 := params 26
abbrev ray603 := rays 26
def bank603 : Fin 1 → Cell := oneBank p603 ray603
theorem signs603 : ∀ j, Signs p603 (bank603 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p604 := params 27
abbrev ray604 := rays 27
def bank604 : Fin 1 → Cell := oneBank p604 ray604
theorem signs604 : ∀ j, Signs p604 (bank604 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p605 := params 28
abbrev ray605 := rays 28
def bank605 : Fin 1 → Cell := oneBank p605 ray605
theorem signs605 : ∀ j, Signs p605 (bank605 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p606 := params 29
abbrev ray606 := rays 29
def bank606 : Fin 1 → Cell := oneBank p606 ray606
theorem signs606 : ∀ j, Signs p606 (bank606 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p607 := params 30
abbrev ray607 := rays 30
def bank607 : Fin 1 → Cell := oneBank p607 ray607
theorem signs607 : ∀ j, Signs p607 (bank607 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p608 := params 31
abbrev ray608 := rays 31
def bank608 : Fin 1 → Cell := oneBank p608 ray608
theorem signs608 : ∀ j, Signs p608 (bank608 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00577_00608
