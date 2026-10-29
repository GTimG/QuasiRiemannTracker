/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06977_07008
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98482641741308,98482339465018,98482037166381,98481734845398,98481432502069,98481130136396,98480827748379,98480525338019,98480222905317,98479920450273,98479617972889,98479315473165,98479012951102,98478710406700,98478407839961,98478105250885,98477802639473,98477500005726,98477197349645,98476894671230,98476591970482,98476289247402,98475986501991,98475683734250,98475380944179,98475078131779,98474775297051,98474472439996,98474169560614,98473866658907,98473563734875,98473260788519,98472957819839]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6976+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6977 := params 0
abbrev ray6977 := rays 0
def bank6977 : Fin 2 → Cell := twoBank p6977 ray6977
theorem signs6977 : ∀ j, Signs p6977 (bank6977 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6978 := params 1
abbrev ray6978 := rays 1
def bank6978 : Fin 2 → Cell := twoBank p6978 ray6978
theorem signs6978 : ∀ j, Signs p6978 (bank6978 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6979 := params 2
abbrev ray6979 := rays 2
def bank6979 : Fin 2 → Cell := twoBank p6979 ray6979
theorem signs6979 : ∀ j, Signs p6979 (bank6979 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6980 := params 3
abbrev ray6980 := rays 3
def bank6980 : Fin 2 → Cell := twoBank p6980 ray6980
theorem signs6980 : ∀ j, Signs p6980 (bank6980 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6981 := params 4
abbrev ray6981 := rays 4
def bank6981 : Fin 2 → Cell := twoBank p6981 ray6981
theorem signs6981 : ∀ j, Signs p6981 (bank6981 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6982 := params 5
abbrev ray6982 := rays 5
def bank6982 : Fin 2 → Cell := twoBank p6982 ray6982
theorem signs6982 : ∀ j, Signs p6982 (bank6982 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6983 := params 6
abbrev ray6983 := rays 6
def bank6983 : Fin 2 → Cell := twoBank p6983 ray6983
theorem signs6983 : ∀ j, Signs p6983 (bank6983 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6984 := params 7
abbrev ray6984 := rays 7
def bank6984 : Fin 2 → Cell := twoBank p6984 ray6984
theorem signs6984 : ∀ j, Signs p6984 (bank6984 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6985 := params 8
abbrev ray6985 := rays 8
def bank6985 : Fin 2 → Cell := twoBank p6985 ray6985
theorem signs6985 : ∀ j, Signs p6985 (bank6985 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6986 := params 9
abbrev ray6986 := rays 9
def bank6986 : Fin 2 → Cell := twoBank p6986 ray6986
theorem signs6986 : ∀ j, Signs p6986 (bank6986 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6987 := params 10
abbrev ray6987 := rays 10
def bank6987 : Fin 2 → Cell := twoBank p6987 ray6987
theorem signs6987 : ∀ j, Signs p6987 (bank6987 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6988 := params 11
abbrev ray6988 := rays 11
def bank6988 : Fin 2 → Cell := twoBank p6988 ray6988
theorem signs6988 : ∀ j, Signs p6988 (bank6988 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6989 := params 12
abbrev ray6989 := rays 12
def bank6989 : Fin 2 → Cell := twoBank p6989 ray6989
theorem signs6989 : ∀ j, Signs p6989 (bank6989 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6990 := params 13
abbrev ray6990 := rays 13
def bank6990 : Fin 2 → Cell := twoBank p6990 ray6990
theorem signs6990 : ∀ j, Signs p6990 (bank6990 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6991 := params 14
abbrev ray6991 := rays 14
def bank6991 : Fin 2 → Cell := twoBank p6991 ray6991
theorem signs6991 : ∀ j, Signs p6991 (bank6991 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6992 := params 15
abbrev ray6992 := rays 15
def bank6992 : Fin 2 → Cell := twoBank p6992 ray6992
theorem signs6992 : ∀ j, Signs p6992 (bank6992 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6993 := params 16
abbrev ray6993 := rays 16
def bank6993 : Fin 2 → Cell := twoBank p6993 ray6993
theorem signs6993 : ∀ j, Signs p6993 (bank6993 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6994 := params 17
abbrev ray6994 := rays 17
def bank6994 : Fin 2 → Cell := twoBank p6994 ray6994
theorem signs6994 : ∀ j, Signs p6994 (bank6994 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6995 := params 18
abbrev ray6995 := rays 18
def bank6995 : Fin 2 → Cell := twoBank p6995 ray6995
theorem signs6995 : ∀ j, Signs p6995 (bank6995 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6996 := params 19
abbrev ray6996 := rays 19
def bank6996 : Fin 2 → Cell := twoBank p6996 ray6996
theorem signs6996 : ∀ j, Signs p6996 (bank6996 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6997 := params 20
abbrev ray6997 := rays 20
def bank6997 : Fin 2 → Cell := twoBank p6997 ray6997
theorem signs6997 : ∀ j, Signs p6997 (bank6997 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6998 := params 21
abbrev ray6998 := rays 21
def bank6998 : Fin 2 → Cell := twoBank p6998 ray6998
theorem signs6998 : ∀ j, Signs p6998 (bank6998 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6999 := params 22
abbrev ray6999 := rays 22
def bank6999 : Fin 2 → Cell := twoBank p6999 ray6999
theorem signs6999 : ∀ j, Signs p6999 (bank6999 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7000 := params 23
abbrev ray7000 := rays 23
def bank7000 : Fin 2 → Cell := twoBank p7000 ray7000
theorem signs7000 : ∀ j, Signs p7000 (bank7000 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7001 := params 24
abbrev ray7001 := rays 24
def bank7001 : Fin 2 → Cell := twoBank p7001 ray7001
theorem signs7001 : ∀ j, Signs p7001 (bank7001 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7002 := params 25
abbrev ray7002 := rays 25
def bank7002 : Fin 2 → Cell := twoBank p7002 ray7002
theorem signs7002 : ∀ j, Signs p7002 (bank7002 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7003 := params 26
abbrev ray7003 := rays 26
def bank7003 : Fin 2 → Cell := twoBank p7003 ray7003
theorem signs7003 : ∀ j, Signs p7003 (bank7003 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7004 := params 27
abbrev ray7004 := rays 27
def bank7004 : Fin 2 → Cell := twoBank p7004 ray7004
theorem signs7004 : ∀ j, Signs p7004 (bank7004 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7005 := params 28
abbrev ray7005 := rays 28
def bank7005 : Fin 2 → Cell := twoBank p7005 ray7005
theorem signs7005 : ∀ j, Signs p7005 (bank7005 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7006 := params 29
abbrev ray7006 := rays 29
def bank7006 : Fin 2 → Cell := twoBank p7006 ray7006
theorem signs7006 : ∀ j, Signs p7006 (bank7006 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7007 := params 30
abbrev ray7007 := rays 30
def bank7007 : Fin 2 → Cell := twoBank p7007 ray7007
theorem signs7007 : ∀ j, Signs p7007 (bank7007 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7008 := params 31
abbrev ray7008 := rays 31
def bank7008 : Fin 2 → Cell := twoBank p7008 ray7008
theorem signs7008 : ∀ j, Signs p7008 (bank7008 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06977_07008
