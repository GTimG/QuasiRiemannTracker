/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00097_00128
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99987570837663,99987440010906,99987309156267,99987178273748,99987047363353,99986916425084,99986785458945,99986654464939,99986523443069,99986392393338,99986261315750,99986130210307,99985999077013,99985867915871,99985736726884,99985605510055,99985474265387,99985342992884,99985211692548,99985080364383,99984949008392,99984817624578,99984686212944,99984554773493,99984423306229,99984291811155,99984160288273,99984028737587,99983897159100,99983765552815,99983633918735,99983502256864,99983370567205]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (96+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(72773463083724736080203/89672120430442879479885:Fraction),(72767193519159580813208/89670370430444629479885:Fraction),(76995686501098744813/94887429026927385693:Fraction),(8083850551109552266286/9962985603383125497765:Fraction),(72748387168562338342826/89665120430449879479885:Fraction),(8082457685131457889746/9962596714494625497765:Fraction),(14547170431204027261139/17932324086090675895977:Fraction),(24243194978320283372273/29886623476818376493295:Fraction),(24241105834339838750333/29886040143485626493295:Fraction),(72717051063410922077696/89656370430458629479885:Fraction),(4847385707746321970560/5976974695364025298659:Fraction),(24234839986066142701144/29884290143487376493295:Fraction),(6608932189948839164044/8150101857314898134535:Fraction),(72691989213185001123101/89649370430465629479885:Fraction),(130965270863964351502/161527244018860143207:Fraction),(2076556035290066662667/2561310583727689413711:Fraction),(72673198133459344249348/89644120430470879479885:Fraction),(8074103869018053502834/9960263381163625497765:Fraction),(72660671298274706282572/89640620430474379479885:Fraction),(691946750172947591074/853703527909296471237:Fraction),(128127243793430872562/158090159489378976155:Fraction),(3459137403957290965712/4268350972879982356185:Fraction),(1963124992655387533724/2422530281904902148105:Fraction),(146725987399930268128/181074485718147736323:Fraction),(474660801223967480734/585817780591404441045:Fraction),(14523368480920920050177/17925674086097325895977:Fraction),(8067842579448374280239/9958513381165375497765:Fraction),(72604323815153119112189/89624870430490129479885:Fraction),(1613290342410059829980/1991624898455375099553:Fraction),(130796048272967800577/161479946721610143207:Fraction),(14517109592860126093780/17923924086099075895977:Fraction),(10368470018629071907484/12802552918642447068555:Fraction)]
abbrev p97 := params 0
abbrev ray97 := rays 0
def bank97 : Fin 1 → Cell := oneBank p97 ray97
theorem signs97 : ∀ j, Signs p97 (bank97 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p98 := params 1
abbrev ray98 := rays 1
def bank98 : Fin 1 → Cell := oneBank p98 ray98
theorem signs98 : ∀ j, Signs p98 (bank98 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p99 := params 2
abbrev ray99 := rays 2
def bank99 : Fin 1 → Cell := oneBank p99 ray99
theorem signs99 : ∀ j, Signs p99 (bank99 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p100 := params 3
abbrev ray100 := rays 3
def bank100 : Fin 1 → Cell := oneBank p100 ray100
theorem signs100 : ∀ j, Signs p100 (bank100 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p101 := params 4
abbrev ray101 := rays 4
def bank101 : Fin 1 → Cell := oneBank p101 ray101
theorem signs101 : ∀ j, Signs p101 (bank101 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p102 := params 5
abbrev ray102 := rays 5
def bank102 : Fin 1 → Cell := oneBank p102 ray102
theorem signs102 : ∀ j, Signs p102 (bank102 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p103 := params 6
abbrev ray103 := rays 6
def bank103 : Fin 1 → Cell := oneBank p103 ray103
theorem signs103 : ∀ j, Signs p103 (bank103 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p104 := params 7
abbrev ray104 := rays 7
def bank104 : Fin 1 → Cell := oneBank p104 ray104
theorem signs104 : ∀ j, Signs p104 (bank104 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p105 := params 8
abbrev ray105 := rays 8
def bank105 : Fin 1 → Cell := oneBank p105 ray105
theorem signs105 : ∀ j, Signs p105 (bank105 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p106 := params 9
abbrev ray106 := rays 9
def bank106 : Fin 1 → Cell := oneBank p106 ray106
theorem signs106 : ∀ j, Signs p106 (bank106 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p107 := params 10
abbrev ray107 := rays 10
def bank107 : Fin 1 → Cell := oneBank p107 ray107
theorem signs107 : ∀ j, Signs p107 (bank107 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p108 := params 11
abbrev ray108 := rays 11
def bank108 : Fin 1 → Cell := oneBank p108 ray108
theorem signs108 : ∀ j, Signs p108 (bank108 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p109 := params 12
abbrev ray109 := rays 12
def bank109 : Fin 1 → Cell := oneBank p109 ray109
theorem signs109 : ∀ j, Signs p109 (bank109 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p110 := params 13
abbrev ray110 := rays 13
def bank110 : Fin 1 → Cell := oneBank p110 ray110
theorem signs110 : ∀ j, Signs p110 (bank110 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p111 := params 14
abbrev ray111 := rays 14
def bank111 : Fin 1 → Cell := oneBank p111 ray111
theorem signs111 : ∀ j, Signs p111 (bank111 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p112 := params 15
abbrev ray112 := rays 15
def bank112 : Fin 1 → Cell := oneBank p112 ray112
theorem signs112 : ∀ j, Signs p112 (bank112 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p113 := params 16
abbrev ray113 := rays 16
def bank113 : Fin 1 → Cell := oneBank p113 ray113
theorem signs113 : ∀ j, Signs p113 (bank113 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p114 := params 17
abbrev ray114 := rays 17
def bank114 : Fin 1 → Cell := oneBank p114 ray114
theorem signs114 : ∀ j, Signs p114 (bank114 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p115 := params 18
abbrev ray115 := rays 18
def bank115 : Fin 1 → Cell := oneBank p115 ray115
theorem signs115 : ∀ j, Signs p115 (bank115 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p116 := params 19
abbrev ray116 := rays 19
def bank116 : Fin 1 → Cell := oneBank p116 ray116
theorem signs116 : ∀ j, Signs p116 (bank116 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p117 := params 20
abbrev ray117 := rays 20
def bank117 : Fin 1 → Cell := oneBank p117 ray117
theorem signs117 : ∀ j, Signs p117 (bank117 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p118 := params 21
abbrev ray118 := rays 21
def bank118 : Fin 1 → Cell := oneBank p118 ray118
theorem signs118 : ∀ j, Signs p118 (bank118 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p119 := params 22
abbrev ray119 := rays 22
def bank119 : Fin 1 → Cell := oneBank p119 ray119
theorem signs119 : ∀ j, Signs p119 (bank119 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p120 := params 23
abbrev ray120 := rays 23
def bank120 : Fin 1 → Cell := oneBank p120 ray120
theorem signs120 : ∀ j, Signs p120 (bank120 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p121 := params 24
abbrev ray121 := rays 24
def bank121 : Fin 1 → Cell := oneBank p121 ray121
theorem signs121 : ∀ j, Signs p121 (bank121 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p122 := params 25
abbrev ray122 := rays 25
def bank122 : Fin 1 → Cell := oneBank p122 ray122
theorem signs122 : ∀ j, Signs p122 (bank122 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p123 := params 26
abbrev ray123 := rays 26
def bank123 : Fin 1 → Cell := oneBank p123 ray123
theorem signs123 : ∀ j, Signs p123 (bank123 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p124 := params 27
abbrev ray124 := rays 27
def bank124 : Fin 1 → Cell := oneBank p124 ray124
theorem signs124 : ∀ j, Signs p124 (bank124 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p125 := params 28
abbrev ray125 := rays 28
def bank125 : Fin 1 → Cell := oneBank p125 ray125
theorem signs125 : ∀ j, Signs p125 (bank125 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p126 := params 29
abbrev ray126 := rays 29
def bank126 : Fin 1 → Cell := oneBank p126 ray126
theorem signs126 : ∀ j, Signs p126 (bank126 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p127 := params 30
abbrev ray127 := rays 30
def bank127 : Fin 1 → Cell := oneBank p127 ray127
theorem signs127 : ∀ j, Signs p127 (bank127 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p128 := params 31
abbrev ray128 := rays 31
def bank128 : Fin 1 → Cell := oneBank p128 ray128
theorem signs128 : ∀ j, Signs p128 (bank128 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00097_00128
