/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12929_12960
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96311238334503,96310814617748,96310390884538,96309967134872,96309543368751,96309119586175,96308695787144,96308271971659,96307848139719,96307424291325,96307000426478,96306576545177,96306152647423,96305728733216,96305304802557,96304880855445,96304456891881,96304032911866,96303608915399,96303184902481,96302760873112,96302336827292,96301912765022,96301488686301,96301064591130,96300640479510,96300216351440,96299792206921,96299368045953,96298943868537,96298519674672,96298095464359,96297671237598]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12928+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p12929 := params 0
abbrev ray12929 := rays 0
def bank12929 : Fin 1 → Cell := oneBank p12929 ray12929
theorem signs12929 : ∀ j, Signs p12929 (bank12929 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12930 := params 1
abbrev ray12930 := rays 1
def bank12930 : Fin 1 → Cell := oneBank p12930 ray12930
theorem signs12930 : ∀ j, Signs p12930 (bank12930 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12931 := params 2
abbrev ray12931 := rays 2
def bank12931 : Fin 1 → Cell := oneBank p12931 ray12931
theorem signs12931 : ∀ j, Signs p12931 (bank12931 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12932 := params 3
abbrev ray12932 := rays 3
def bank12932 : Fin 1 → Cell := oneBank p12932 ray12932
theorem signs12932 : ∀ j, Signs p12932 (bank12932 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12933 := params 4
abbrev ray12933 := rays 4
def bank12933 : Fin 1 → Cell := oneBank p12933 ray12933
theorem signs12933 : ∀ j, Signs p12933 (bank12933 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12934 := params 5
abbrev ray12934 := rays 5
def bank12934 : Fin 1 → Cell := oneBank p12934 ray12934
theorem signs12934 : ∀ j, Signs p12934 (bank12934 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12935 := params 6
abbrev ray12935 := rays 6
def bank12935 : Fin 1 → Cell := oneBank p12935 ray12935
theorem signs12935 : ∀ j, Signs p12935 (bank12935 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12936 := params 7
abbrev ray12936 := rays 7
def bank12936 : Fin 1 → Cell := oneBank p12936 ray12936
theorem signs12936 : ∀ j, Signs p12936 (bank12936 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12937 := params 8
abbrev ray12937 := rays 8
def bank12937 : Fin 1 → Cell := oneBank p12937 ray12937
theorem signs12937 : ∀ j, Signs p12937 (bank12937 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12938 := params 9
abbrev ray12938 := rays 9
def bank12938 : Fin 1 → Cell := oneBank p12938 ray12938
theorem signs12938 : ∀ j, Signs p12938 (bank12938 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12939 := params 10
abbrev ray12939 := rays 10
def bank12939 : Fin 1 → Cell := oneBank p12939 ray12939
theorem signs12939 : ∀ j, Signs p12939 (bank12939 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12940 := params 11
abbrev ray12940 := rays 11
def bank12940 : Fin 1 → Cell := oneBank p12940 ray12940
theorem signs12940 : ∀ j, Signs p12940 (bank12940 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12941 := params 12
abbrev ray12941 := rays 12
def bank12941 : Fin 1 → Cell := oneBank p12941 ray12941
theorem signs12941 : ∀ j, Signs p12941 (bank12941 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12942 := params 13
abbrev ray12942 := rays 13
def bank12942 : Fin 1 → Cell := oneBank p12942 ray12942
theorem signs12942 : ∀ j, Signs p12942 (bank12942 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12943 := params 14
abbrev ray12943 := rays 14
def bank12943 : Fin 1 → Cell := oneBank p12943 ray12943
theorem signs12943 : ∀ j, Signs p12943 (bank12943 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12944 := params 15
abbrev ray12944 := rays 15
def bank12944 : Fin 1 → Cell := oneBank p12944 ray12944
theorem signs12944 : ∀ j, Signs p12944 (bank12944 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12945 := params 16
abbrev ray12945 := rays 16
def bank12945 : Fin 1 → Cell := oneBank p12945 ray12945
theorem signs12945 : ∀ j, Signs p12945 (bank12945 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12946 := params 17
abbrev ray12946 := rays 17
def bank12946 : Fin 1 → Cell := oneBank p12946 ray12946
theorem signs12946 : ∀ j, Signs p12946 (bank12946 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12947 := params 18
abbrev ray12947 := rays 18
def bank12947 : Fin 1 → Cell := oneBank p12947 ray12947
theorem signs12947 : ∀ j, Signs p12947 (bank12947 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12948 := params 19
abbrev ray12948 := rays 19
def bank12948 : Fin 1 → Cell := oneBank p12948 ray12948
theorem signs12948 : ∀ j, Signs p12948 (bank12948 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12949 := params 20
abbrev ray12949 := rays 20
def bank12949 : Fin 1 → Cell := oneBank p12949 ray12949
theorem signs12949 : ∀ j, Signs p12949 (bank12949 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12950 := params 21
abbrev ray12950 := rays 21
def bank12950 : Fin 1 → Cell := oneBank p12950 ray12950
theorem signs12950 : ∀ j, Signs p12950 (bank12950 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12951 := params 22
abbrev ray12951 := rays 22
def bank12951 : Fin 1 → Cell := oneBank p12951 ray12951
theorem signs12951 : ∀ j, Signs p12951 (bank12951 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12952 := params 23
abbrev ray12952 := rays 23
def bank12952 : Fin 1 → Cell := oneBank p12952 ray12952
theorem signs12952 : ∀ j, Signs p12952 (bank12952 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12953 := params 24
abbrev ray12953 := rays 24
def bank12953 : Fin 1 → Cell := oneBank p12953 ray12953
theorem signs12953 : ∀ j, Signs p12953 (bank12953 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12954 := params 25
abbrev ray12954 := rays 25
def bank12954 : Fin 1 → Cell := oneBank p12954 ray12954
theorem signs12954 : ∀ j, Signs p12954 (bank12954 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12955 := params 26
abbrev ray12955 := rays 26
def bank12955 : Fin 1 → Cell := oneBank p12955 ray12955
theorem signs12955 : ∀ j, Signs p12955 (bank12955 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12956 := params 27
abbrev ray12956 := rays 27
def bank12956 : Fin 1 → Cell := oneBank p12956 ray12956
theorem signs12956 : ∀ j, Signs p12956 (bank12956 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12957 := params 28
abbrev ray12957 := rays 28
def bank12957 : Fin 1 → Cell := oneBank p12957 ray12957
theorem signs12957 : ∀ j, Signs p12957 (bank12957 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12958 := params 29
abbrev ray12958 := rays 29
def bank12958 : Fin 1 → Cell := oneBank p12958 ray12958
theorem signs12958 : ∀ j, Signs p12958 (bank12958 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12959 := params 30
abbrev ray12959 := rays 30
def bank12959 : Fin 1 → Cell := oneBank p12959 ray12959
theorem signs12959 : ∀ j, Signs p12959 (bank12959 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12960 := params 31
abbrev ray12960 := rays 31
def bank12960 : Fin 1 → Cell := oneBank p12960 ray12960
theorem signs12960 : ∀ j, Signs p12960 (bank12960 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12929_12960
