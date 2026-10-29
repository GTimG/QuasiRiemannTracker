/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13057_13088
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96256868927504,96256443106551,96256017269175,96255591415377,96255165545158,96254739658517,96254313755455,96253887835972,96253461900068,96253035947744,96252609979000,96252183993836,96251757992252,96251331974249,96250905939826,96250479888984,96250053821724,96249627738045,96249201637948,96248775521433,96248349388501,96247923239151,96247497073384,96247070891200,96246644692600,96246218477583,96245792246150,96245365998301,96244939734037,96244513453357,96244087156262,96243660842752,96243234512828]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13056+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13057 := params 0
abbrev ray13057 := rays 0
def bank13057 : Fin 1 → Cell := oneBank p13057 ray13057
theorem signs13057 : ∀ j, Signs p13057 (bank13057 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13058 := params 1
abbrev ray13058 := rays 1
def bank13058 : Fin 1 → Cell := oneBank p13058 ray13058
theorem signs13058 : ∀ j, Signs p13058 (bank13058 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13059 := params 2
abbrev ray13059 := rays 2
def bank13059 : Fin 1 → Cell := oneBank p13059 ray13059
theorem signs13059 : ∀ j, Signs p13059 (bank13059 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13060 := params 3
abbrev ray13060 := rays 3
def bank13060 : Fin 1 → Cell := oneBank p13060 ray13060
theorem signs13060 : ∀ j, Signs p13060 (bank13060 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13061 := params 4
abbrev ray13061 := rays 4
def bank13061 : Fin 1 → Cell := oneBank p13061 ray13061
theorem signs13061 : ∀ j, Signs p13061 (bank13061 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13062 := params 5
abbrev ray13062 := rays 5
def bank13062 : Fin 1 → Cell := oneBank p13062 ray13062
theorem signs13062 : ∀ j, Signs p13062 (bank13062 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13063 := params 6
abbrev ray13063 := rays 6
def bank13063 : Fin 1 → Cell := oneBank p13063 ray13063
theorem signs13063 : ∀ j, Signs p13063 (bank13063 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13064 := params 7
abbrev ray13064 := rays 7
def bank13064 : Fin 1 → Cell := oneBank p13064 ray13064
theorem signs13064 : ∀ j, Signs p13064 (bank13064 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13065 := params 8
abbrev ray13065 := rays 8
def bank13065 : Fin 1 → Cell := oneBank p13065 ray13065
theorem signs13065 : ∀ j, Signs p13065 (bank13065 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13066 := params 9
abbrev ray13066 := rays 9
def bank13066 : Fin 1 → Cell := oneBank p13066 ray13066
theorem signs13066 : ∀ j, Signs p13066 (bank13066 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13067 := params 10
abbrev ray13067 := rays 10
def bank13067 : Fin 1 → Cell := oneBank p13067 ray13067
theorem signs13067 : ∀ j, Signs p13067 (bank13067 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13068 := params 11
abbrev ray13068 := rays 11
def bank13068 : Fin 1 → Cell := oneBank p13068 ray13068
theorem signs13068 : ∀ j, Signs p13068 (bank13068 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13069 := params 12
abbrev ray13069 := rays 12
def bank13069 : Fin 1 → Cell := oneBank p13069 ray13069
theorem signs13069 : ∀ j, Signs p13069 (bank13069 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13070 := params 13
abbrev ray13070 := rays 13
def bank13070 : Fin 1 → Cell := oneBank p13070 ray13070
theorem signs13070 : ∀ j, Signs p13070 (bank13070 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13071 := params 14
abbrev ray13071 := rays 14
def bank13071 : Fin 1 → Cell := oneBank p13071 ray13071
theorem signs13071 : ∀ j, Signs p13071 (bank13071 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13072 := params 15
abbrev ray13072 := rays 15
def bank13072 : Fin 1 → Cell := oneBank p13072 ray13072
theorem signs13072 : ∀ j, Signs p13072 (bank13072 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13073 := params 16
abbrev ray13073 := rays 16
def bank13073 : Fin 1 → Cell := oneBank p13073 ray13073
theorem signs13073 : ∀ j, Signs p13073 (bank13073 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13074 := params 17
abbrev ray13074 := rays 17
def bank13074 : Fin 1 → Cell := oneBank p13074 ray13074
theorem signs13074 : ∀ j, Signs p13074 (bank13074 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13075 := params 18
abbrev ray13075 := rays 18
def bank13075 : Fin 1 → Cell := oneBank p13075 ray13075
theorem signs13075 : ∀ j, Signs p13075 (bank13075 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13076 := params 19
abbrev ray13076 := rays 19
def bank13076 : Fin 1 → Cell := oneBank p13076 ray13076
theorem signs13076 : ∀ j, Signs p13076 (bank13076 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13077 := params 20
abbrev ray13077 := rays 20
def bank13077 : Fin 1 → Cell := oneBank p13077 ray13077
theorem signs13077 : ∀ j, Signs p13077 (bank13077 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13078 := params 21
abbrev ray13078 := rays 21
def bank13078 : Fin 1 → Cell := oneBank p13078 ray13078
theorem signs13078 : ∀ j, Signs p13078 (bank13078 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13079 := params 22
abbrev ray13079 := rays 22
def bank13079 : Fin 1 → Cell := oneBank p13079 ray13079
theorem signs13079 : ∀ j, Signs p13079 (bank13079 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13080 := params 23
abbrev ray13080 := rays 23
def bank13080 : Fin 1 → Cell := oneBank p13080 ray13080
theorem signs13080 : ∀ j, Signs p13080 (bank13080 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13081 := params 24
abbrev ray13081 := rays 24
def bank13081 : Fin 1 → Cell := oneBank p13081 ray13081
theorem signs13081 : ∀ j, Signs p13081 (bank13081 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13082 := params 25
abbrev ray13082 := rays 25
def bank13082 : Fin 1 → Cell := oneBank p13082 ray13082
theorem signs13082 : ∀ j, Signs p13082 (bank13082 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13083 := params 26
abbrev ray13083 := rays 26
def bank13083 : Fin 1 → Cell := oneBank p13083 ray13083
theorem signs13083 : ∀ j, Signs p13083 (bank13083 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13084 := params 27
abbrev ray13084 := rays 27
def bank13084 : Fin 1 → Cell := oneBank p13084 ray13084
theorem signs13084 : ∀ j, Signs p13084 (bank13084 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13085 := params 28
abbrev ray13085 := rays 28
def bank13085 : Fin 1 → Cell := oneBank p13085 ray13085
theorem signs13085 : ∀ j, Signs p13085 (bank13085 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13086 := params 29
abbrev ray13086 := rays 29
def bank13086 : Fin 1 → Cell := oneBank p13086 ray13086
theorem signs13086 : ∀ j, Signs p13086 (bank13086 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13087 := params 30
abbrev ray13087 := rays 30
def bank13087 : Fin 1 → Cell := oneBank p13087 ray13087
theorem signs13087 : ∀ j, Signs p13087 (bank13087 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13088 := params 31
abbrev ray13088 := rays 31
def bank13088 : Fin 1 → Cell := oneBank p13088 ray13088
theorem signs13088 : ∀ j, Signs p13088 (bank13088 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13057_13088
