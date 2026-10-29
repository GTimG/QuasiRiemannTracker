/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14977_15008
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95409298539857,95408841571941,95408384587957,95407927587904,95407470571783,95407013539594,95406556491337,95406099427012,95405642346619,95405185250159,95404728137631,95404271009036,95403813864373,95403356703643,95402899526846,95402442333982,95401985125051,95401527900053,95401070658989,95400613401858,95400156128661,95399698839397,95399241534067,95398784212671,95398326875209,95397869521681,95397412152087,95396954766427,95396497364702,95396039946911,95395582513055,95395125063134,95394667597148]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14976+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14977 := params 0
abbrev ray14977 := rays 0
def bank14977 : Fin 1 → Cell := oneBank p14977 ray14977
theorem signs14977 : ∀ j, Signs p14977 (bank14977 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14978 := params 1
abbrev ray14978 := rays 1
def bank14978 : Fin 1 → Cell := oneBank p14978 ray14978
theorem signs14978 : ∀ j, Signs p14978 (bank14978 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14979 := params 2
abbrev ray14979 := rays 2
def bank14979 : Fin 1 → Cell := oneBank p14979 ray14979
theorem signs14979 : ∀ j, Signs p14979 (bank14979 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14980 := params 3
abbrev ray14980 := rays 3
def bank14980 : Fin 1 → Cell := oneBank p14980 ray14980
theorem signs14980 : ∀ j, Signs p14980 (bank14980 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14981 := params 4
abbrev ray14981 := rays 4
def bank14981 : Fin 1 → Cell := oneBank p14981 ray14981
theorem signs14981 : ∀ j, Signs p14981 (bank14981 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14982 := params 5
abbrev ray14982 := rays 5
def bank14982 : Fin 1 → Cell := oneBank p14982 ray14982
theorem signs14982 : ∀ j, Signs p14982 (bank14982 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14983 := params 6
abbrev ray14983 := rays 6
def bank14983 : Fin 1 → Cell := oneBank p14983 ray14983
theorem signs14983 : ∀ j, Signs p14983 (bank14983 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14984 := params 7
abbrev ray14984 := rays 7
def bank14984 : Fin 1 → Cell := oneBank p14984 ray14984
theorem signs14984 : ∀ j, Signs p14984 (bank14984 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14985 := params 8
abbrev ray14985 := rays 8
def bank14985 : Fin 1 → Cell := oneBank p14985 ray14985
theorem signs14985 : ∀ j, Signs p14985 (bank14985 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14986 := params 9
abbrev ray14986 := rays 9
def bank14986 : Fin 1 → Cell := oneBank p14986 ray14986
theorem signs14986 : ∀ j, Signs p14986 (bank14986 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14987 := params 10
abbrev ray14987 := rays 10
def bank14987 : Fin 1 → Cell := oneBank p14987 ray14987
theorem signs14987 : ∀ j, Signs p14987 (bank14987 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14988 := params 11
abbrev ray14988 := rays 11
def bank14988 : Fin 1 → Cell := oneBank p14988 ray14988
theorem signs14988 : ∀ j, Signs p14988 (bank14988 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14989 := params 12
abbrev ray14989 := rays 12
def bank14989 : Fin 1 → Cell := oneBank p14989 ray14989
theorem signs14989 : ∀ j, Signs p14989 (bank14989 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14990 := params 13
abbrev ray14990 := rays 13
def bank14990 : Fin 1 → Cell := oneBank p14990 ray14990
theorem signs14990 : ∀ j, Signs p14990 (bank14990 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14991 := params 14
abbrev ray14991 := rays 14
def bank14991 : Fin 1 → Cell := oneBank p14991 ray14991
theorem signs14991 : ∀ j, Signs p14991 (bank14991 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14992 := params 15
abbrev ray14992 := rays 15
def bank14992 : Fin 1 → Cell := oneBank p14992 ray14992
theorem signs14992 : ∀ j, Signs p14992 (bank14992 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14993 := params 16
abbrev ray14993 := rays 16
def bank14993 : Fin 1 → Cell := oneBank p14993 ray14993
theorem signs14993 : ∀ j, Signs p14993 (bank14993 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14994 := params 17
abbrev ray14994 := rays 17
def bank14994 : Fin 1 → Cell := oneBank p14994 ray14994
theorem signs14994 : ∀ j, Signs p14994 (bank14994 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14995 := params 18
abbrev ray14995 := rays 18
def bank14995 : Fin 1 → Cell := oneBank p14995 ray14995
theorem signs14995 : ∀ j, Signs p14995 (bank14995 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14996 := params 19
abbrev ray14996 := rays 19
def bank14996 : Fin 1 → Cell := oneBank p14996 ray14996
theorem signs14996 : ∀ j, Signs p14996 (bank14996 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14997 := params 20
abbrev ray14997 := rays 20
def bank14997 : Fin 1 → Cell := oneBank p14997 ray14997
theorem signs14997 : ∀ j, Signs p14997 (bank14997 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14998 := params 21
abbrev ray14998 := rays 21
def bank14998 : Fin 1 → Cell := oneBank p14998 ray14998
theorem signs14998 : ∀ j, Signs p14998 (bank14998 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14999 := params 22
abbrev ray14999 := rays 22
def bank14999 : Fin 1 → Cell := oneBank p14999 ray14999
theorem signs14999 : ∀ j, Signs p14999 (bank14999 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15000 := params 23
abbrev ray15000 := rays 23
def bank15000 : Fin 1 → Cell := oneBank p15000 ray15000
theorem signs15000 : ∀ j, Signs p15000 (bank15000 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15001 := params 24
abbrev ray15001 := rays 24
def bank15001 : Fin 1 → Cell := oneBank p15001 ray15001
theorem signs15001 : ∀ j, Signs p15001 (bank15001 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15002 := params 25
abbrev ray15002 := rays 25
def bank15002 : Fin 1 → Cell := oneBank p15002 ray15002
theorem signs15002 : ∀ j, Signs p15002 (bank15002 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15003 := params 26
abbrev ray15003 := rays 26
def bank15003 : Fin 1 → Cell := oneBank p15003 ray15003
theorem signs15003 : ∀ j, Signs p15003 (bank15003 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15004 := params 27
abbrev ray15004 := rays 27
def bank15004 : Fin 1 → Cell := oneBank p15004 ray15004
theorem signs15004 : ∀ j, Signs p15004 (bank15004 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15005 := params 28
abbrev ray15005 := rays 28
def bank15005 : Fin 1 → Cell := oneBank p15005 ray15005
theorem signs15005 : ∀ j, Signs p15005 (bank15005 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15006 := params 29
abbrev ray15006 := rays 29
def bank15006 : Fin 1 → Cell := oneBank p15006 ray15006
theorem signs15006 : ∀ j, Signs p15006 (bank15006 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15007 := params 30
abbrev ray15007 := rays 30
def bank15007 : Fin 1 → Cell := oneBank p15007 ray15007
theorem signs15007 : ∀ j, Signs p15007 (bank15007 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15008 := params 31
abbrev ray15008 := rays 31
def bank15008 : Fin 1 → Cell := oneBank p15008 ray15008
theorem signs15008 : ∀ j, Signs p15008 (bank15008 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14977_15008
