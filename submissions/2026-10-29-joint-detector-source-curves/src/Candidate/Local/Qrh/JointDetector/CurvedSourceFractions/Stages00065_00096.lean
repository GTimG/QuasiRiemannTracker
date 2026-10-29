/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00065_00096
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99991742552796,99991612619963,99991482659145,99991352670346,99991222653569,99991092608817,99990962536094,99990832435403,99990702306746,99990572150127,99990441965549,99990311753015,99990181512529,99990051244094,99989920947712,99989790623387,99989660271122,99989529890921,99989399482787,99989269046722,99989138582730,99989008090814,99988877570977,99988747023223,99988616447554,99988485843974,99988355212485,99988224553092,99988093865797,99987963150603,99987832407514,99987701636533,99987570837663]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (64+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(4864952927165422529948/5981874695359125298659:Fraction),(2702518958019399765599/3323198904829208499255:Fraction),(14592345922714209399028/17944924086078075895977:Fraction),(72955448351278418144624/89722870430392129479885:Fraction),(24316389359901519870601/29907040143464626493295:Fraction),(394285878898588536626/484969569894030429621:Fraction),(72936606900896987695112/89717620430397379479885:Fraction),(24310109065463998649587/29905290143466376493295:Fraction),(72924048482781266272912/89714120430400879479885:Fraction),(1279259115042041978227/1573901235621098762805:Fraction),(900141871888824426977/1107538523832152833085:Fraction),(4860347565125146956629/5980591362027075298659:Fraction),(4859929007937284345195/5980474695360525298659:Fraction),(656690610381465337408/808156490364050716035:Fraction),(4859092091785646927620/5980241362027425298659:Fraction),(10411443541375485674668/12814552918630447068555:Fraction),(24291275996962684101704/29900040143471626493295:Fraction),(14573510436685133451923/17939674086083325895977:Fraction),(14572255473459967584197/17939324086083675895977:Fraction),(179888894665906014588/221468815877580566617:Fraction),(14569745420123507181860/17938624086084375895977:Fraction),(24280817617665467884048/29897123476807876493295:Fraction),(385376611623741354004/474548256245636928465:Fraction),(4855327075294302236722/5979191362028475298659:Fraction),(24274544150197225973056/29895373476809626493295:Fraction),(4854490650893240612992/5978958028695375298659:Fraction),(1618024179286502581697/1992947120676275099553:Fraction),(10400688023020112210158/12811552918633447068555:Fraction),(24266181748721631666112/29893040143478626493295:Fraction),(72792274119999970340549/89677370430437629479885:Fraction),(1967189264396258388616/2423665417038902148105:Fraction),(2695545645822850768376/3321254460386708499255:Fraction)]
abbrev p65 := params 0
abbrev ray65 := rays 0
def bank65 : Fin 1 → Cell := oneBank p65 ray65
theorem signs65 : ∀ j, Signs p65 (bank65 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p66 := params 1
abbrev ray66 := rays 1
def bank66 : Fin 1 → Cell := oneBank p66 ray66
theorem signs66 : ∀ j, Signs p66 (bank66 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p67 := params 2
abbrev ray67 := rays 2
def bank67 : Fin 1 → Cell := oneBank p67 ray67
theorem signs67 : ∀ j, Signs p67 (bank67 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p68 := params 3
abbrev ray68 := rays 3
def bank68 : Fin 1 → Cell := oneBank p68 ray68
theorem signs68 : ∀ j, Signs p68 (bank68 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p69 := params 4
abbrev ray69 := rays 4
def bank69 : Fin 1 → Cell := oneBank p69 ray69
theorem signs69 : ∀ j, Signs p69 (bank69 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p70 := params 5
abbrev ray70 := rays 5
def bank70 : Fin 1 → Cell := oneBank p70 ray70
theorem signs70 : ∀ j, Signs p70 (bank70 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p71 := params 6
abbrev ray71 := rays 6
def bank71 : Fin 1 → Cell := oneBank p71 ray71
theorem signs71 : ∀ j, Signs p71 (bank71 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p72 := params 7
abbrev ray72 := rays 7
def bank72 : Fin 1 → Cell := oneBank p72 ray72
theorem signs72 : ∀ j, Signs p72 (bank72 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p73 := params 8
abbrev ray73 := rays 8
def bank73 : Fin 1 → Cell := oneBank p73 ray73
theorem signs73 : ∀ j, Signs p73 (bank73 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p74 := params 9
abbrev ray74 := rays 9
def bank74 : Fin 1 → Cell := oneBank p74 ray74
theorem signs74 : ∀ j, Signs p74 (bank74 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p75 := params 10
abbrev ray75 := rays 10
def bank75 : Fin 1 → Cell := oneBank p75 ray75
theorem signs75 : ∀ j, Signs p75 (bank75 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p76 := params 11
abbrev ray76 := rays 11
def bank76 : Fin 1 → Cell := oneBank p76 ray76
theorem signs76 : ∀ j, Signs p76 (bank76 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p77 := params 12
abbrev ray77 := rays 12
def bank77 : Fin 1 → Cell := oneBank p77 ray77
theorem signs77 : ∀ j, Signs p77 (bank77 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p78 := params 13
abbrev ray78 := rays 13
def bank78 : Fin 1 → Cell := oneBank p78 ray78
theorem signs78 : ∀ j, Signs p78 (bank78 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p79 := params 14
abbrev ray79 := rays 14
def bank79 : Fin 1 → Cell := oneBank p79 ray79
theorem signs79 : ∀ j, Signs p79 (bank79 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p80 := params 15
abbrev ray80 := rays 15
def bank80 : Fin 1 → Cell := oneBank p80 ray80
theorem signs80 : ∀ j, Signs p80 (bank80 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p81 := params 16
abbrev ray81 := rays 16
def bank81 : Fin 1 → Cell := oneBank p81 ray81
theorem signs81 : ∀ j, Signs p81 (bank81 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p82 := params 17
abbrev ray82 := rays 17
def bank82 : Fin 1 → Cell := oneBank p82 ray82
theorem signs82 : ∀ j, Signs p82 (bank82 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p83 := params 18
abbrev ray83 := rays 18
def bank83 : Fin 1 → Cell := oneBank p83 ray83
theorem signs83 : ∀ j, Signs p83 (bank83 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p84 := params 19
abbrev ray84 := rays 19
def bank84 : Fin 1 → Cell := oneBank p84 ray84
theorem signs84 : ∀ j, Signs p84 (bank84 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p85 := params 20
abbrev ray85 := rays 20
def bank85 : Fin 1 → Cell := oneBank p85 ray85
theorem signs85 : ∀ j, Signs p85 (bank85 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p86 := params 21
abbrev ray86 := rays 21
def bank86 : Fin 1 → Cell := oneBank p86 ray86
theorem signs86 : ∀ j, Signs p86 (bank86 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p87 := params 22
abbrev ray87 := rays 22
def bank87 : Fin 1 → Cell := oneBank p87 ray87
theorem signs87 : ∀ j, Signs p87 (bank87 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p88 := params 23
abbrev ray88 := rays 23
def bank88 : Fin 1 → Cell := oneBank p88 ray88
theorem signs88 : ∀ j, Signs p88 (bank88 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p89 := params 24
abbrev ray89 := rays 24
def bank89 : Fin 1 → Cell := oneBank p89 ray89
theorem signs89 : ∀ j, Signs p89 (bank89 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p90 := params 25
abbrev ray90 := rays 25
def bank90 : Fin 1 → Cell := oneBank p90 ray90
theorem signs90 : ∀ j, Signs p90 (bank90 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p91 := params 26
abbrev ray91 := rays 26
def bank91 : Fin 1 → Cell := oneBank p91 ray91
theorem signs91 : ∀ j, Signs p91 (bank91 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p92 := params 27
abbrev ray92 := rays 27
def bank92 : Fin 1 → Cell := oneBank p92 ray92
theorem signs92 : ∀ j, Signs p92 (bank92 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p93 := params 28
abbrev ray93 := rays 28
def bank93 : Fin 1 → Cell := oneBank p93 ray93
theorem signs93 : ∀ j, Signs p93 (bank93 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p94 := params 29
abbrev ray94 := rays 29
def bank94 : Fin 1 → Cell := oneBank p94 ray94
theorem signs94 : ∀ j, Signs p94 (bank94 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p95 := params 30
abbrev ray95 := rays 30
def bank95 : Fin 1 → Cell := oneBank p95 ray95
theorem signs95 : ∀ j, Signs p95 (bank95 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p96 := params 31
abbrev ray96 := rays 31
def bank96 : Fin 1 → Cell := oneBank p96 ray96
theorem signs96 : ∀ j, Signs p96 (bank96 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00065_00096
