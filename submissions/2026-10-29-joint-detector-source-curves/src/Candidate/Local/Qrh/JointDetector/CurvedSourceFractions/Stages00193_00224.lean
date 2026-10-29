/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00193_00224
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99974884771461,99974751282220,99974617765395,99974484220989,99974350649005,99974217049446,99974083422316,99973949767617,99973816085353,99973682375526,99973548638140,99973414873197,99973281080701,99973147260655,99973013413062,99972879537925,99972745635247,99972611705031,99972477747280,99972343761997,99972209749185,99972075708847,99971941640987,99971807545607,99971673422710,99971539272300,99971405094379,99971270888951,99971136656019,99971002395585,99970868107652,99970733792224,99970599449304]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (192+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(390126406454892011809/483806056381680429621:Fraction),(14433430656635581442140/17900474086122525895977:Fraction),(4810728157896010321558/5966708028707625298659:Fraction),(72154691245474423836238/89498870430616129479885:Fraction),(14429692223766981000509/17899424086123575895977:Fraction),(72214445229254113664/89584955386005635115:Fraction),(10305143063661302764412/12784802918660197068555:Fraction),(72129771899120292525344/89491870430623129479885:Fraction),(24041181116370863969711/29830040143541626493295:Fraction),(14423462918209846584128/17897674086125325895977:Fraction),(2060316766559251629860/2556760583732239413711:Fraction),(1602330196891114206994/1988552676236225099553:Fraction),(72098631887301197550761/89483120430631879479885:Fraction),(14418480941312535087832/17896274086126725895977:Fraction),(2669858463799468809344/3314060015949458499255:Fraction),(14415990426145290494780/17895574086127425895977:Fraction),(1947938560424743679299/2418273525152402148105:Fraction),(8007500125875530314378/9941596714515625497765:Fraction),(14412255305395809807076/17894524086128475895977:Fraction),(14411010342662177475214/17894174086128825895977:Fraction),(686179313301566492005/852086861244246471237:Fraction),(14408520774461599090868/17893474086129525895977:Fraction),(72036380845061243198302/89465620430649379479885:Fraction),(8003350845573528428456/9940430047850125497765:Fraction),(2057826724927355856304/2556060583732939413711:Fraction),(14403542585431801633780/17892074086130925895977:Fraction),(2182166408458861876042/2710867285777466044845:Fraction),(72005269823589051452302/89456870430658129479885:Fraction),(71999049165405476462179/89455120430659879479885:Fraction),(1599840628883136273040/1987852676236925099553:Fraction),(14397321686306402948836/17890324086132675895977:Fraction),(71980389560837385732154/89449870430665129479885:Fraction)]
abbrev p193 := params 0
abbrev ray193 := rays 0
def bank193 : Fin 1 → Cell := oneBank p193 ray193
theorem signs193 : ∀ j, Signs p193 (bank193 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p194 := params 1
abbrev ray194 := rays 1
def bank194 : Fin 1 → Cell := oneBank p194 ray194
theorem signs194 : ∀ j, Signs p194 (bank194 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p195 := params 2
abbrev ray195 := rays 2
def bank195 : Fin 1 → Cell := oneBank p195 ray195
theorem signs195 : ∀ j, Signs p195 (bank195 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p196 := params 3
abbrev ray196 := rays 3
def bank196 : Fin 1 → Cell := oneBank p196 ray196
theorem signs196 : ∀ j, Signs p196 (bank196 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p197 := params 4
abbrev ray197 := rays 4
def bank197 : Fin 1 → Cell := oneBank p197 ray197
theorem signs197 : ∀ j, Signs p197 (bank197 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p198 := params 5
abbrev ray198 := rays 5
def bank198 : Fin 1 → Cell := oneBank p198 ray198
theorem signs198 : ∀ j, Signs p198 (bank198 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p199 := params 6
abbrev ray199 := rays 6
def bank199 : Fin 1 → Cell := oneBank p199 ray199
theorem signs199 : ∀ j, Signs p199 (bank199 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p200 := params 7
abbrev ray200 := rays 7
def bank200 : Fin 1 → Cell := oneBank p200 ray200
theorem signs200 : ∀ j, Signs p200 (bank200 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p201 := params 8
abbrev ray201 := rays 8
def bank201 : Fin 1 → Cell := oneBank p201 ray201
theorem signs201 : ∀ j, Signs p201 (bank201 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p202 := params 9
abbrev ray202 := rays 9
def bank202 : Fin 1 → Cell := oneBank p202 ray202
theorem signs202 : ∀ j, Signs p202 (bank202 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p203 := params 10
abbrev ray203 := rays 10
def bank203 : Fin 1 → Cell := oneBank p203 ray203
theorem signs203 : ∀ j, Signs p203 (bank203 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p204 := params 11
abbrev ray204 := rays 11
def bank204 : Fin 1 → Cell := oneBank p204 ray204
theorem signs204 : ∀ j, Signs p204 (bank204 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p205 := params 12
abbrev ray205 := rays 12
def bank205 : Fin 1 → Cell := oneBank p205 ray205
theorem signs205 : ∀ j, Signs p205 (bank205 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p206 := params 13
abbrev ray206 := rays 13
def bank206 : Fin 1 → Cell := oneBank p206 ray206
theorem signs206 : ∀ j, Signs p206 (bank206 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p207 := params 14
abbrev ray207 := rays 14
def bank207 : Fin 1 → Cell := oneBank p207 ray207
theorem signs207 : ∀ j, Signs p207 (bank207 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p208 := params 15
abbrev ray208 := rays 15
def bank208 : Fin 1 → Cell := oneBank p208 ray208
theorem signs208 : ∀ j, Signs p208 (bank208 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p209 := params 16
abbrev ray209 := rays 16
def bank209 : Fin 1 → Cell := oneBank p209 ray209
theorem signs209 : ∀ j, Signs p209 (bank209 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p210 := params 17
abbrev ray210 := rays 17
def bank210 : Fin 1 → Cell := oneBank p210 ray210
theorem signs210 : ∀ j, Signs p210 (bank210 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p211 := params 18
abbrev ray211 := rays 18
def bank211 : Fin 1 → Cell := oneBank p211 ray211
theorem signs211 : ∀ j, Signs p211 (bank211 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p212 := params 19
abbrev ray212 := rays 19
def bank212 : Fin 1 → Cell := oneBank p212 ray212
theorem signs212 : ∀ j, Signs p212 (bank212 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p213 := params 20
abbrev ray213 := rays 20
def bank213 : Fin 1 → Cell := oneBank p213 ray213
theorem signs213 : ∀ j, Signs p213 (bank213 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p214 := params 21
abbrev ray214 := rays 21
def bank214 : Fin 1 → Cell := oneBank p214 ray214
theorem signs214 : ∀ j, Signs p214 (bank214 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p215 := params 22
abbrev ray215 := rays 22
def bank215 : Fin 1 → Cell := oneBank p215 ray215
theorem signs215 : ∀ j, Signs p215 (bank215 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p216 := params 23
abbrev ray216 := rays 23
def bank216 : Fin 1 → Cell := oneBank p216 ray216
theorem signs216 : ∀ j, Signs p216 (bank216 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p217 := params 24
abbrev ray217 := rays 24
def bank217 : Fin 1 → Cell := oneBank p217 ray217
theorem signs217 : ∀ j, Signs p217 (bank217 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p218 := params 25
abbrev ray218 := rays 25
def bank218 : Fin 1 → Cell := oneBank p218 ray218
theorem signs218 : ∀ j, Signs p218 (bank218 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p219 := params 26
abbrev ray219 := rays 26
def bank219 : Fin 1 → Cell := oneBank p219 ray219
theorem signs219 : ∀ j, Signs p219 (bank219 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p220 := params 27
abbrev ray220 := rays 27
def bank220 : Fin 1 → Cell := oneBank p220 ray220
theorem signs220 : ∀ j, Signs p220 (bank220 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p221 := params 28
abbrev ray221 := rays 28
def bank221 : Fin 1 → Cell := oneBank p221 ray221
theorem signs221 : ∀ j, Signs p221 (bank221 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p222 := params 29
abbrev ray222 := rays 29
def bank222 : Fin 1 → Cell := oneBank p222 ray222
theorem signs222 : ∀ j, Signs p222 (bank222 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p223 := params 30
abbrev ray223 := rays 30
def bank223 : Fin 1 → Cell := oneBank p223 ray223
theorem signs223 : ∀ j, Signs p223 (bank223 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p224 := params 31
abbrev ray224 := rays 31
def bank224 : Fin 1 → Cell := oneBank p224 ray224
theorem signs224 : ∀ j, Signs p224 (bank224 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00193_00224
