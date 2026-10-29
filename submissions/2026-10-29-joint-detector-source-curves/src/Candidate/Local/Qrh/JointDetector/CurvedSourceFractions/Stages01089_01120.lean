/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01089_01120
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99844562216984,99844405142410,99844248042673,99844090917775,99843933767719,99843776592507,99843619392142,99843462166626,99843304915961,99843147640149,99842990339193,99842833013096,99842675661859,99842518285485,99842360883976,99842203457335,99842046005564,99841888528666,99841731026643,99841573499497,99841415947231,99841258369847,99841100767347,99840943139734,99840785487009,99840627809176,99840470106236,99840312378192,99840154625047,99839996846803,99839839043462,99839681215027,99839523361499]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1088+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(7417145586279653682508/9770680048019875497765:Fraction),(13349690056280713999940/17586874086436125895977:Fraction),(7415843479988164963291/9770291159131375497765:Fraction),(635587925472123532925/837436861258896471237:Fraction),(13346174812587105609982/17585824086437175895977:Fraction),(66725015767539093653083/87927370432187629479885:Fraction),(353011420666166989832/465214922921636928465:Fraction),(1803062190826066595812/2376320822491652148105:Fraction),(635308996657761307738/837353527925646471237:Fraction),(7411287561545345896871/9768930048021625497765:Fraction),(66695732492672666890379/87918620432196379479885:Fraction),(22229959321804423165412/29305623477399376493295:Fraction),(2469778593962678498786/3256115571562958499255:Fraction),(13335633672041368988464/17582674086440325895977:Fraction),(66672314499906193984676/87911620432203379479885:Fraction),(493825633008166219660/651184225423741699851:Fraction),(634862928061507284802/837220194592446471237:Fraction),(4443650283557491029848/5860424695480575298659:Fraction),(2468477855352066886114/3255726682674458499255:Fraction),(66643049752247741205134/87902870432212129479885:Fraction),(66637198444308765040739/87901120432213879479885:Fraction),(74782656512928892372/98652492067582075735:Fraction),(22208498832042732473966/29299206810739126493295:Fraction),(66619647073689056506832/87895870432219129479885:Fraction),(418954693397635011391/552793210265540122515:Fraction),(200023866904030032622/263941052349016905345:Fraction),(66602098924650710716546/87890620432224379479885:Fraction),(1057083333127970574914/1395061435432160785395:Fraction),(9512914583444342539192/12555302918889697068555:Fraction),(9512079142573242244607/12555052918889947068555:Fraction),(1479526821036230026496/1952969342938475099553:Fraction),(7396984412461484908661/9764652270248125497765:Fraction)]
abbrev p1089 := params 0
abbrev ray1089 := rays 0
def bank1089 : Fin 1 → Cell := oneBank p1089 ray1089
theorem signs1089 : ∀ j, Signs p1089 (bank1089 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1090 := params 1
abbrev ray1090 := rays 1
def bank1090 : Fin 1 → Cell := oneBank p1090 ray1090
theorem signs1090 : ∀ j, Signs p1090 (bank1090 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1091 := params 2
abbrev ray1091 := rays 2
def bank1091 : Fin 1 → Cell := oneBank p1091 ray1091
theorem signs1091 : ∀ j, Signs p1091 (bank1091 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1092 := params 3
abbrev ray1092 := rays 3
def bank1092 : Fin 1 → Cell := oneBank p1092 ray1092
theorem signs1092 : ∀ j, Signs p1092 (bank1092 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1093 := params 4
abbrev ray1093 := rays 4
def bank1093 : Fin 1 → Cell := oneBank p1093 ray1093
theorem signs1093 : ∀ j, Signs p1093 (bank1093 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1094 := params 5
abbrev ray1094 := rays 5
def bank1094 : Fin 1 → Cell := oneBank p1094 ray1094
theorem signs1094 : ∀ j, Signs p1094 (bank1094 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1095 := params 6
abbrev ray1095 := rays 6
def bank1095 : Fin 1 → Cell := oneBank p1095 ray1095
theorem signs1095 : ∀ j, Signs p1095 (bank1095 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1096 := params 7
abbrev ray1096 := rays 7
def bank1096 : Fin 1 → Cell := oneBank p1096 ray1096
theorem signs1096 : ∀ j, Signs p1096 (bank1096 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1097 := params 8
abbrev ray1097 := rays 8
def bank1097 : Fin 1 → Cell := oneBank p1097 ray1097
theorem signs1097 : ∀ j, Signs p1097 (bank1097 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1098 := params 9
abbrev ray1098 := rays 9
def bank1098 : Fin 1 → Cell := oneBank p1098 ray1098
theorem signs1098 : ∀ j, Signs p1098 (bank1098 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1099 := params 10
abbrev ray1099 := rays 10
def bank1099 : Fin 1 → Cell := oneBank p1099 ray1099
theorem signs1099 : ∀ j, Signs p1099 (bank1099 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1100 := params 11
abbrev ray1100 := rays 11
def bank1100 : Fin 1 → Cell := oneBank p1100 ray1100
theorem signs1100 : ∀ j, Signs p1100 (bank1100 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1101 := params 12
abbrev ray1101 := rays 12
def bank1101 : Fin 1 → Cell := oneBank p1101 ray1101
theorem signs1101 : ∀ j, Signs p1101 (bank1101 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1102 := params 13
abbrev ray1102 := rays 13
def bank1102 : Fin 1 → Cell := oneBank p1102 ray1102
theorem signs1102 : ∀ j, Signs p1102 (bank1102 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1103 := params 14
abbrev ray1103 := rays 14
def bank1103 : Fin 1 → Cell := oneBank p1103 ray1103
theorem signs1103 : ∀ j, Signs p1103 (bank1103 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1104 := params 15
abbrev ray1104 := rays 15
def bank1104 : Fin 1 → Cell := oneBank p1104 ray1104
theorem signs1104 : ∀ j, Signs p1104 (bank1104 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1105 := params 16
abbrev ray1105 := rays 16
def bank1105 : Fin 1 → Cell := oneBank p1105 ray1105
theorem signs1105 : ∀ j, Signs p1105 (bank1105 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1106 := params 17
abbrev ray1106 := rays 17
def bank1106 : Fin 1 → Cell := oneBank p1106 ray1106
theorem signs1106 : ∀ j, Signs p1106 (bank1106 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1107 := params 18
abbrev ray1107 := rays 18
def bank1107 : Fin 1 → Cell := oneBank p1107 ray1107
theorem signs1107 : ∀ j, Signs p1107 (bank1107 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1108 := params 19
abbrev ray1108 := rays 19
def bank1108 : Fin 1 → Cell := oneBank p1108 ray1108
theorem signs1108 : ∀ j, Signs p1108 (bank1108 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1109 := params 20
abbrev ray1109 := rays 20
def bank1109 : Fin 1 → Cell := oneBank p1109 ray1109
theorem signs1109 : ∀ j, Signs p1109 (bank1109 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1110 := params 21
abbrev ray1110 := rays 21
def bank1110 : Fin 1 → Cell := oneBank p1110 ray1110
theorem signs1110 : ∀ j, Signs p1110 (bank1110 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1111 := params 22
abbrev ray1111 := rays 22
def bank1111 : Fin 1 → Cell := oneBank p1111 ray1111
theorem signs1111 : ∀ j, Signs p1111 (bank1111 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1112 := params 23
abbrev ray1112 := rays 23
def bank1112 : Fin 1 → Cell := oneBank p1112 ray1112
theorem signs1112 : ∀ j, Signs p1112 (bank1112 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1113 := params 24
abbrev ray1113 := rays 24
def bank1113 : Fin 1 → Cell := oneBank p1113 ray1113
theorem signs1113 : ∀ j, Signs p1113 (bank1113 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1114 := params 25
abbrev ray1114 := rays 25
def bank1114 : Fin 1 → Cell := oneBank p1114 ray1114
theorem signs1114 : ∀ j, Signs p1114 (bank1114 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1115 := params 26
abbrev ray1115 := rays 26
def bank1115 : Fin 1 → Cell := oneBank p1115 ray1115
theorem signs1115 : ∀ j, Signs p1115 (bank1115 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1116 := params 27
abbrev ray1116 := rays 27
def bank1116 : Fin 1 → Cell := oneBank p1116 ray1116
theorem signs1116 : ∀ j, Signs p1116 (bank1116 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1117 := params 28
abbrev ray1117 := rays 28
def bank1117 : Fin 1 → Cell := oneBank p1117 ray1117
theorem signs1117 : ∀ j, Signs p1117 (bank1117 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1118 := params 29
abbrev ray1118 := rays 29
def bank1118 : Fin 1 → Cell := oneBank p1118 ray1118
theorem signs1118 : ∀ j, Signs p1118 (bank1118 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1119 := params 30
abbrev ray1119 := rays 30
def bank1119 : Fin 1 → Cell := oneBank p1119 ray1119
theorem signs1119 : ∀ j, Signs p1119 (bank1119 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1120 := params 31
abbrev ray1120 := rays 31
def bank1120 : Fin 1 → Cell := oneBank p1120 ray1120
theorem signs1120 : ∀ j, Signs p1120 (bank1120 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01089_01120
