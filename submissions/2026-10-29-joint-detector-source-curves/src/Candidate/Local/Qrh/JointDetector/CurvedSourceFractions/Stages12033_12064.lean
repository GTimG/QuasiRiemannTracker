/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12033_12064
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96683507503759,96683100596838,96682693670576,96682286724973,96681879760029,96681472775745,96681065772122,96680658749160,96680251706859,96679844645220,96679437564243,96679030463929,96678623344278,96678216205290,96677809046966,96677401869307,96676994672312,96676587455982,96676180220318,96675772965320,96675365690989,96674958397325,96674551084328,96674143751999,96673736400338,96673329029345,96672921639021,96672514229367,96672106800383,96671699352069,96671291884426,96670884397454,96670476891154]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12032+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12033 := params 0
abbrev ray12033 := rays 0
def bank12033 : Fin 2 → Cell := twoBank p12033 ray12033
theorem signs12033 : ∀ j, Signs p12033 (bank12033 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12034 := params 1
abbrev ray12034 := rays 1
def bank12034 : Fin 2 → Cell := twoBank p12034 ray12034
theorem signs12034 : ∀ j, Signs p12034 (bank12034 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12035 := params 2
abbrev ray12035 := rays 2
def bank12035 : Fin 2 → Cell := twoBank p12035 ray12035
theorem signs12035 : ∀ j, Signs p12035 (bank12035 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12036 := params 3
abbrev ray12036 := rays 3
def bank12036 : Fin 2 → Cell := twoBank p12036 ray12036
theorem signs12036 : ∀ j, Signs p12036 (bank12036 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12037 := params 4
abbrev ray12037 := rays 4
def bank12037 : Fin 2 → Cell := twoBank p12037 ray12037
theorem signs12037 : ∀ j, Signs p12037 (bank12037 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12038 := params 5
abbrev ray12038 := rays 5
def bank12038 : Fin 2 → Cell := twoBank p12038 ray12038
theorem signs12038 : ∀ j, Signs p12038 (bank12038 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12039 := params 6
abbrev ray12039 := rays 6
def bank12039 : Fin 2 → Cell := twoBank p12039 ray12039
theorem signs12039 : ∀ j, Signs p12039 (bank12039 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12040 := params 7
abbrev ray12040 := rays 7
def bank12040 : Fin 2 → Cell := twoBank p12040 ray12040
theorem signs12040 : ∀ j, Signs p12040 (bank12040 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12041 := params 8
abbrev ray12041 := rays 8
def bank12041 : Fin 2 → Cell := twoBank p12041 ray12041
theorem signs12041 : ∀ j, Signs p12041 (bank12041 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12042 := params 9
abbrev ray12042 := rays 9
def bank12042 : Fin 2 → Cell := twoBank p12042 ray12042
theorem signs12042 : ∀ j, Signs p12042 (bank12042 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12043 := params 10
abbrev ray12043 := rays 10
def bank12043 : Fin 2 → Cell := twoBank p12043 ray12043
theorem signs12043 : ∀ j, Signs p12043 (bank12043 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12044 := params 11
abbrev ray12044 := rays 11
def bank12044 : Fin 2 → Cell := twoBank p12044 ray12044
theorem signs12044 : ∀ j, Signs p12044 (bank12044 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12045 := params 12
abbrev ray12045 := rays 12
def bank12045 : Fin 2 → Cell := twoBank p12045 ray12045
theorem signs12045 : ∀ j, Signs p12045 (bank12045 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12046 := params 13
abbrev ray12046 := rays 13
def bank12046 : Fin 2 → Cell := twoBank p12046 ray12046
theorem signs12046 : ∀ j, Signs p12046 (bank12046 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12047 := params 14
abbrev ray12047 := rays 14
def bank12047 : Fin 2 → Cell := twoBank p12047 ray12047
theorem signs12047 : ∀ j, Signs p12047 (bank12047 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12048 := params 15
abbrev ray12048 := rays 15
def bank12048 : Fin 2 → Cell := twoBank p12048 ray12048
theorem signs12048 : ∀ j, Signs p12048 (bank12048 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12049 := params 16
abbrev ray12049 := rays 16
def bank12049 : Fin 2 → Cell := twoBank p12049 ray12049
theorem signs12049 : ∀ j, Signs p12049 (bank12049 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12050 := params 17
abbrev ray12050 := rays 17
def bank12050 : Fin 2 → Cell := twoBank p12050 ray12050
theorem signs12050 : ∀ j, Signs p12050 (bank12050 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12051 := params 18
abbrev ray12051 := rays 18
def bank12051 : Fin 2 → Cell := twoBank p12051 ray12051
theorem signs12051 : ∀ j, Signs p12051 (bank12051 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12052 := params 19
abbrev ray12052 := rays 19
def bank12052 : Fin 2 → Cell := twoBank p12052 ray12052
theorem signs12052 : ∀ j, Signs p12052 (bank12052 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12053 := params 20
abbrev ray12053 := rays 20
def bank12053 : Fin 2 → Cell := twoBank p12053 ray12053
theorem signs12053 : ∀ j, Signs p12053 (bank12053 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12054 := params 21
abbrev ray12054 := rays 21
def bank12054 : Fin 2 → Cell := twoBank p12054 ray12054
theorem signs12054 : ∀ j, Signs p12054 (bank12054 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12055 := params 22
abbrev ray12055 := rays 22
def bank12055 : Fin 2 → Cell := twoBank p12055 ray12055
theorem signs12055 : ∀ j, Signs p12055 (bank12055 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12056 := params 23
abbrev ray12056 := rays 23
def bank12056 : Fin 2 → Cell := twoBank p12056 ray12056
theorem signs12056 : ∀ j, Signs p12056 (bank12056 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12057 := params 24
abbrev ray12057 := rays 24
def bank12057 : Fin 2 → Cell := twoBank p12057 ray12057
theorem signs12057 : ∀ j, Signs p12057 (bank12057 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12058 := params 25
abbrev ray12058 := rays 25
def bank12058 : Fin 2 → Cell := twoBank p12058 ray12058
theorem signs12058 : ∀ j, Signs p12058 (bank12058 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12059 := params 26
abbrev ray12059 := rays 26
def bank12059 : Fin 2 → Cell := twoBank p12059 ray12059
theorem signs12059 : ∀ j, Signs p12059 (bank12059 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12060 := params 27
abbrev ray12060 := rays 27
def bank12060 : Fin 2 → Cell := twoBank p12060 ray12060
theorem signs12060 : ∀ j, Signs p12060 (bank12060 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12061 := params 28
abbrev ray12061 := rays 28
def bank12061 : Fin 2 → Cell := twoBank p12061 ray12061
theorem signs12061 : ∀ j, Signs p12061 (bank12061 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12062 := params 29
abbrev ray12062 := rays 29
def bank12062 : Fin 2 → Cell := twoBank p12062 ray12062
theorem signs12062 : ∀ j, Signs p12062 (bank12062 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12063 := params 30
abbrev ray12063 := rays 30
def bank12063 : Fin 2 → Cell := twoBank p12063 ray12063
theorem signs12063 : ∀ j, Signs p12063 (bank12063 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12064 := params 31
abbrev ray12064 := rays 31
def bank12064 : Fin 2 → Cell := twoBank p12064 ray12064
theorem signs12064 : ∀ j, Signs p12064 (bank12064 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12033_12064
