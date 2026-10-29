/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00129_00160
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99983370567205,99983238849760,99983107104533,99982975331526,99982843530743,99982711702188,99982579845863,99982447961771,99982316049916,99982184110300,99982052142927,99981920147801,99981788124923,99981656074297,99981523995927,99981391889815,99981259755964,99981127594378,99980995405059,99980863188012,99980730943239,99980598670742,99980466370526,99980334042593,99980201686946,99980069303588,99979936892523,99979804453754,99979671987284,99979539493116,99979406971253,99979274421698,99979141844454]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (128+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(68143693229919388355/84146591953520074629:Fraction),(14513355247837077004736/17922874086100125895977:Fraction),(72560520181951713623056/89612620430502379479885:Fraction),(2504375545015238656/3093123137982952935:Fraction),(14509601487451026694352/17921824086101175895977:Fraction),(1612038932298585939734/1991274898455725099553:Fraction),(8059499718137476725847/9956180047834375497765:Fraction),(24176414254357857371599/29867956810170376493295:Fraction),(72522989056618085535824/89602120430512879479885:Fraction),(371880693026952650270/459489079130844253743:Fraction),(24170160338000684193602/29866206810172126493295:Fraction),(72504227881573995445006/89596870430518129479885:Fraction),(690456911838356345143/853286861243046471237:Fraction),(72491723394690853475588/89593370430521629479885:Fraction),(24161824013441844060766/29863873476841126493295:Fraction),(4831948031748533377784/5972658028701675298659:Fraction),(14509103084321854982/17935559645751127023:Fraction),(72466719126474146339128/89586370430528629479885:Fraction),(24153489379033443550351/29861540143510126493295:Fraction),(72454218141902318971798/89582870430532129479885:Fraction),(72447969140937164640118/89581120430533879479885:Fraction),(84727157813348596048/104771193486006584187:Fraction),(72435471714210232426424/89577620430537379479885:Fraction),(10347031898358206265947/12796552918648447068555:Fraction),(24140991952403950623896/29858040143513626493295:Fraction),(72416728216474002357814/89572370430542629479885:Fraction),(72410480366309291362844/89570620430544379479885:Fraction),(8044914834518782037344/9952096714505125497765:Fraction),(1956702368908419662662/2420732984609402148105:Fraction),(24130580526409471337876/29855123476849876493295:Fraction),(8042832944835018018832/9951513381172375497765:Fraction),(24126417072844661789944/29853956810184376493295:Fraction)]
abbrev p129 := params 0
abbrev ray129 := rays 0
def bank129 : Fin 1 → Cell := oneBank p129 ray129
theorem signs129 : ∀ j, Signs p129 (bank129 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p130 := params 1
abbrev ray130 := rays 1
def bank130 : Fin 1 → Cell := oneBank p130 ray130
theorem signs130 : ∀ j, Signs p130 (bank130 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p131 := params 2
abbrev ray131 := rays 2
def bank131 : Fin 1 → Cell := oneBank p131 ray131
theorem signs131 : ∀ j, Signs p131 (bank131 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p132 := params 3
abbrev ray132 := rays 3
def bank132 : Fin 1 → Cell := oneBank p132 ray132
theorem signs132 : ∀ j, Signs p132 (bank132 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p133 := params 4
abbrev ray133 := rays 4
def bank133 : Fin 1 → Cell := oneBank p133 ray133
theorem signs133 : ∀ j, Signs p133 (bank133 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p134 := params 5
abbrev ray134 := rays 5
def bank134 : Fin 1 → Cell := oneBank p134 ray134
theorem signs134 : ∀ j, Signs p134 (bank134 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p135 := params 6
abbrev ray135 := rays 6
def bank135 : Fin 1 → Cell := oneBank p135 ray135
theorem signs135 : ∀ j, Signs p135 (bank135 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p136 := params 7
abbrev ray136 := rays 7
def bank136 : Fin 1 → Cell := oneBank p136 ray136
theorem signs136 : ∀ j, Signs p136 (bank136 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p137 := params 8
abbrev ray137 := rays 8
def bank137 : Fin 1 → Cell := oneBank p137 ray137
theorem signs137 : ∀ j, Signs p137 (bank137 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p138 := params 9
abbrev ray138 := rays 9
def bank138 : Fin 1 → Cell := oneBank p138 ray138
theorem signs138 : ∀ j, Signs p138 (bank138 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p139 := params 10
abbrev ray139 := rays 10
def bank139 : Fin 1 → Cell := oneBank p139 ray139
theorem signs139 : ∀ j, Signs p139 (bank139 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p140 := params 11
abbrev ray140 := rays 11
def bank140 : Fin 1 → Cell := oneBank p140 ray140
theorem signs140 : ∀ j, Signs p140 (bank140 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p141 := params 12
abbrev ray141 := rays 12
def bank141 : Fin 1 → Cell := oneBank p141 ray141
theorem signs141 : ∀ j, Signs p141 (bank141 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p142 := params 13
abbrev ray142 := rays 13
def bank142 : Fin 1 → Cell := oneBank p142 ray142
theorem signs142 : ∀ j, Signs p142 (bank142 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p143 := params 14
abbrev ray143 := rays 14
def bank143 : Fin 1 → Cell := oneBank p143 ray143
theorem signs143 : ∀ j, Signs p143 (bank143 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p144 := params 15
abbrev ray144 := rays 15
def bank144 : Fin 1 → Cell := oneBank p144 ray144
theorem signs144 : ∀ j, Signs p144 (bank144 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p145 := params 16
abbrev ray145 := rays 16
def bank145 : Fin 1 → Cell := oneBank p145 ray145
theorem signs145 : ∀ j, Signs p145 (bank145 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p146 := params 17
abbrev ray146 := rays 17
def bank146 : Fin 1 → Cell := oneBank p146 ray146
theorem signs146 : ∀ j, Signs p146 (bank146 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p147 := params 18
abbrev ray147 := rays 18
def bank147 : Fin 1 → Cell := oneBank p147 ray147
theorem signs147 : ∀ j, Signs p147 (bank147 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p148 := params 19
abbrev ray148 := rays 19
def bank148 : Fin 1 → Cell := oneBank p148 ray148
theorem signs148 : ∀ j, Signs p148 (bank148 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p149 := params 20
abbrev ray149 := rays 20
def bank149 : Fin 1 → Cell := oneBank p149 ray149
theorem signs149 : ∀ j, Signs p149 (bank149 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p150 := params 21
abbrev ray150 := rays 21
def bank150 : Fin 1 → Cell := oneBank p150 ray150
theorem signs150 : ∀ j, Signs p150 (bank150 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p151 := params 22
abbrev ray151 := rays 22
def bank151 : Fin 1 → Cell := oneBank p151 ray151
theorem signs151 : ∀ j, Signs p151 (bank151 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p152 := params 23
abbrev ray152 := rays 23
def bank152 : Fin 1 → Cell := oneBank p152 ray152
theorem signs152 : ∀ j, Signs p152 (bank152 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p153 := params 24
abbrev ray153 := rays 24
def bank153 : Fin 1 → Cell := oneBank p153 ray153
theorem signs153 : ∀ j, Signs p153 (bank153 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p154 := params 25
abbrev ray154 := rays 25
def bank154 : Fin 1 → Cell := oneBank p154 ray154
theorem signs154 : ∀ j, Signs p154 (bank154 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p155 := params 26
abbrev ray155 := rays 26
def bank155 : Fin 1 → Cell := oneBank p155 ray155
theorem signs155 : ∀ j, Signs p155 (bank155 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p156 := params 27
abbrev ray156 := rays 27
def bank156 : Fin 1 → Cell := oneBank p156 ray156
theorem signs156 : ∀ j, Signs p156 (bank156 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p157 := params 28
abbrev ray157 := rays 28
def bank157 : Fin 1 → Cell := oneBank p157 ray157
theorem signs157 : ∀ j, Signs p157 (bank157 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p158 := params 29
abbrev ray158 := rays 29
def bank158 : Fin 1 → Cell := oneBank p158 ray158
theorem signs158 : ∀ j, Signs p158 (bank158 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p159 := params 30
abbrev ray159 := rays 30
def bank159 : Fin 1 → Cell := oneBank p159 ray159
theorem signs159 : ∀ j, Signs p159 (bank159 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p160 := params 31
abbrev ray160 := rays 31
def bank160 : Fin 1 → Cell := oneBank p160 ray160
theorem signs160 : ∀ j, Signs p160 (bank160 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00129_00160
