/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01121_01152
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99839523361499,99839365482882,99839207579177,99839049650387,99838891696514,99838733717561,99838575713530,99838417684423,99838259630243,99838101550992,99837943446672,99837785317285,99837627162835,99837468983323,99837310778752,99837152549124,99836994294441,99836836014706,99836677709921,99836519380088,99836361025210,99836202645289,99836044240328,99835885810329,99835727355294,99835568875225,99835410370125,99835251839996,99835093284841,99834934704662,99834776099460,99834617469239,99834458814001]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1120+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(13313402702494052986928/17576024086446975895977:Fraction),(3169579445125561649968/4184684306296982356185:Fraction),(66555322999798092780296/87876620432238379479885:Fraction),(66549477468966193601404/87874870432240129479885:Fraction),(821526333001080284908/1084853338669652833085:Fraction),(256902657506821998238/339271700510593164015:Fraction),(4435462976698609571536/5857974695483025298659:Fraction),(22175366941266533345854/29289290144082376493295:Fraction),(66520258032232539263993/87866120432248879479885:Fraction),(22171472091943793129606/29288123477416876493295:Fraction),(22169524778876309099318/29287540144084126493295:Fraction),(13300546442927211027295/17572174086450825895977:Fraction),(13299378225582978451858/17571824086451175895977:Fraction),(7387894428717172578451/9761930048028625497765:Fraction),(820805057090671269626/1084637289287152833085:Fraction),(22159789735848750198334/29284623477420376493295:Fraction),(22157843275392241731658/29284040144087626493295:Fraction),(22155897160096777908952/29283456810754876493295:Fraction),(66461852951806436278198/87848620432266379479885:Fraction),(4430400949382392690340/5856458028817875298659:Fraction),(1898576473292944983428/2509860583779139413711:Fraction),(66444338707234815528224/87843370432271629479885:Fraction),(4429233458992255712564/5856108028818225298659:Fraction),(13286533219650701081591/17567974086455025895977:Fraction),(66426828910959052607656/87838120432276879479885:Fraction),(4428066265177902112475/5855758028818575298659:Fraction),(359000858713427772985/474781732066380429621:Fraction),(66409323563916714431002/87832870432282129479885:Fraction),(819796164219185201844/1084334820151652833085:Fraction),(66397656075549348919904/87829370432285629479885:Fraction),(1475373809972150512562/1951724898495275099553:Fraction),(567401616036510060706/750648465233240422905:Fraction)]
abbrev p1121 := params 0
abbrev ray1121 := rays 0
def bank1121 : Fin 1 → Cell := oneBank p1121 ray1121
theorem signs1121 : ∀ j, Signs p1121 (bank1121 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1122 := params 1
abbrev ray1122 := rays 1
def bank1122 : Fin 1 → Cell := oneBank p1122 ray1122
theorem signs1122 : ∀ j, Signs p1122 (bank1122 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1123 := params 2
abbrev ray1123 := rays 2
def bank1123 : Fin 1 → Cell := oneBank p1123 ray1123
theorem signs1123 : ∀ j, Signs p1123 (bank1123 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1124 := params 3
abbrev ray1124 := rays 3
def bank1124 : Fin 1 → Cell := oneBank p1124 ray1124
theorem signs1124 : ∀ j, Signs p1124 (bank1124 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1125 := params 4
abbrev ray1125 := rays 4
def bank1125 : Fin 1 → Cell := oneBank p1125 ray1125
theorem signs1125 : ∀ j, Signs p1125 (bank1125 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1126 := params 5
abbrev ray1126 := rays 5
def bank1126 : Fin 1 → Cell := oneBank p1126 ray1126
theorem signs1126 : ∀ j, Signs p1126 (bank1126 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1127 := params 6
abbrev ray1127 := rays 6
def bank1127 : Fin 1 → Cell := oneBank p1127 ray1127
theorem signs1127 : ∀ j, Signs p1127 (bank1127 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1128 := params 7
abbrev ray1128 := rays 7
def bank1128 : Fin 1 → Cell := oneBank p1128 ray1128
theorem signs1128 : ∀ j, Signs p1128 (bank1128 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1129 := params 8
abbrev ray1129 := rays 8
def bank1129 : Fin 1 → Cell := oneBank p1129 ray1129
theorem signs1129 : ∀ j, Signs p1129 (bank1129 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1130 := params 9
abbrev ray1130 := rays 9
def bank1130 : Fin 1 → Cell := oneBank p1130 ray1130
theorem signs1130 : ∀ j, Signs p1130 (bank1130 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1131 := params 10
abbrev ray1131 := rays 10
def bank1131 : Fin 1 → Cell := oneBank p1131 ray1131
theorem signs1131 : ∀ j, Signs p1131 (bank1131 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1132 := params 11
abbrev ray1132 := rays 11
def bank1132 : Fin 1 → Cell := oneBank p1132 ray1132
theorem signs1132 : ∀ j, Signs p1132 (bank1132 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1133 := params 12
abbrev ray1133 := rays 12
def bank1133 : Fin 1 → Cell := oneBank p1133 ray1133
theorem signs1133 : ∀ j, Signs p1133 (bank1133 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1134 := params 13
abbrev ray1134 := rays 13
def bank1134 : Fin 1 → Cell := oneBank p1134 ray1134
theorem signs1134 : ∀ j, Signs p1134 (bank1134 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1135 := params 14
abbrev ray1135 := rays 14
def bank1135 : Fin 1 → Cell := oneBank p1135 ray1135
theorem signs1135 : ∀ j, Signs p1135 (bank1135 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1136 := params 15
abbrev ray1136 := rays 15
def bank1136 : Fin 1 → Cell := oneBank p1136 ray1136
theorem signs1136 : ∀ j, Signs p1136 (bank1136 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1137 := params 16
abbrev ray1137 := rays 16
def bank1137 : Fin 1 → Cell := oneBank p1137 ray1137
theorem signs1137 : ∀ j, Signs p1137 (bank1137 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1138 := params 17
abbrev ray1138 := rays 17
def bank1138 : Fin 1 → Cell := oneBank p1138 ray1138
theorem signs1138 : ∀ j, Signs p1138 (bank1138 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1139 := params 18
abbrev ray1139 := rays 18
def bank1139 : Fin 1 → Cell := oneBank p1139 ray1139
theorem signs1139 : ∀ j, Signs p1139 (bank1139 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1140 := params 19
abbrev ray1140 := rays 19
def bank1140 : Fin 1 → Cell := oneBank p1140 ray1140
theorem signs1140 : ∀ j, Signs p1140 (bank1140 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1141 := params 20
abbrev ray1141 := rays 20
def bank1141 : Fin 1 → Cell := oneBank p1141 ray1141
theorem signs1141 : ∀ j, Signs p1141 (bank1141 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1142 := params 21
abbrev ray1142 := rays 21
def bank1142 : Fin 1 → Cell := oneBank p1142 ray1142
theorem signs1142 : ∀ j, Signs p1142 (bank1142 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1143 := params 22
abbrev ray1143 := rays 22
def bank1143 : Fin 1 → Cell := oneBank p1143 ray1143
theorem signs1143 : ∀ j, Signs p1143 (bank1143 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1144 := params 23
abbrev ray1144 := rays 23
def bank1144 : Fin 1 → Cell := oneBank p1144 ray1144
theorem signs1144 : ∀ j, Signs p1144 (bank1144 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1145 := params 24
abbrev ray1145 := rays 24
def bank1145 : Fin 1 → Cell := oneBank p1145 ray1145
theorem signs1145 : ∀ j, Signs p1145 (bank1145 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1146 := params 25
abbrev ray1146 := rays 25
def bank1146 : Fin 1 → Cell := oneBank p1146 ray1146
theorem signs1146 : ∀ j, Signs p1146 (bank1146 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1147 := params 26
abbrev ray1147 := rays 26
def bank1147 : Fin 1 → Cell := oneBank p1147 ray1147
theorem signs1147 : ∀ j, Signs p1147 (bank1147 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1148 := params 27
abbrev ray1148 := rays 27
def bank1148 : Fin 1 → Cell := oneBank p1148 ray1148
theorem signs1148 : ∀ j, Signs p1148 (bank1148 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1149 := params 28
abbrev ray1149 := rays 28
def bank1149 : Fin 1 → Cell := oneBank p1149 ray1149
theorem signs1149 : ∀ j, Signs p1149 (bank1149 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1150 := params 29
abbrev ray1150 := rays 29
def bank1150 : Fin 1 → Cell := oneBank p1150 ray1150
theorem signs1150 : ∀ j, Signs p1150 (bank1150 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1151 := params 30
abbrev ray1151 := rays 30
def bank1151 : Fin 1 → Cell := oneBank p1151 ray1151
theorem signs1151 : ∀ j, Signs p1151 (bank1151 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1152 := params 31
abbrev ray1152 := rays 31
def bank1152 : Fin 1 → Cell := oneBank p1152 ray1152
theorem signs1152 : ∀ j, Signs p1152 (bank1152 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01121_01152
