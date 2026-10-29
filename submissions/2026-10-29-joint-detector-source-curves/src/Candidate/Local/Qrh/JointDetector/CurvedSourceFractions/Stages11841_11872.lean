/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11841_11872
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96761274759821,96760871574449,96760468369652,96760065145431,96759661901786,96759258638717,96758855356225,96758452054310,96758048732973,96757645392215,96757242032035,96756838652435,96756435253414,96756031834973,96755628397113,96755224939834,96754821463136,96754417967020,96754014451486,96753610916535,96753207362167,96752803788382,96752400195181,96751996582565,96751592950534,96751189299088,96750785628228,96750381937954,96749978228267,96749574499167,96749170750654,96748766982729,96748363195393]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11840+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11841 := params 0
abbrev ray11841 := rays 0
def bank11841 : Fin 2 → Cell := twoBank p11841 ray11841
theorem signs11841 : ∀ j, Signs p11841 (bank11841 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11842 := params 1
abbrev ray11842 := rays 1
def bank11842 : Fin 2 → Cell := twoBank p11842 ray11842
theorem signs11842 : ∀ j, Signs p11842 (bank11842 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11843 := params 2
abbrev ray11843 := rays 2
def bank11843 : Fin 2 → Cell := twoBank p11843 ray11843
theorem signs11843 : ∀ j, Signs p11843 (bank11843 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11844 := params 3
abbrev ray11844 := rays 3
def bank11844 : Fin 2 → Cell := twoBank p11844 ray11844
theorem signs11844 : ∀ j, Signs p11844 (bank11844 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11845 := params 4
abbrev ray11845 := rays 4
def bank11845 : Fin 2 → Cell := twoBank p11845 ray11845
theorem signs11845 : ∀ j, Signs p11845 (bank11845 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11846 := params 5
abbrev ray11846 := rays 5
def bank11846 : Fin 2 → Cell := twoBank p11846 ray11846
theorem signs11846 : ∀ j, Signs p11846 (bank11846 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11847 := params 6
abbrev ray11847 := rays 6
def bank11847 : Fin 2 → Cell := twoBank p11847 ray11847
theorem signs11847 : ∀ j, Signs p11847 (bank11847 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11848 := params 7
abbrev ray11848 := rays 7
def bank11848 : Fin 2 → Cell := twoBank p11848 ray11848
theorem signs11848 : ∀ j, Signs p11848 (bank11848 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11849 := params 8
abbrev ray11849 := rays 8
def bank11849 : Fin 2 → Cell := twoBank p11849 ray11849
theorem signs11849 : ∀ j, Signs p11849 (bank11849 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11850 := params 9
abbrev ray11850 := rays 9
def bank11850 : Fin 2 → Cell := twoBank p11850 ray11850
theorem signs11850 : ∀ j, Signs p11850 (bank11850 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11851 := params 10
abbrev ray11851 := rays 10
def bank11851 : Fin 2 → Cell := twoBank p11851 ray11851
theorem signs11851 : ∀ j, Signs p11851 (bank11851 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11852 := params 11
abbrev ray11852 := rays 11
def bank11852 : Fin 2 → Cell := twoBank p11852 ray11852
theorem signs11852 : ∀ j, Signs p11852 (bank11852 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11853 := params 12
abbrev ray11853 := rays 12
def bank11853 : Fin 2 → Cell := twoBank p11853 ray11853
theorem signs11853 : ∀ j, Signs p11853 (bank11853 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11854 := params 13
abbrev ray11854 := rays 13
def bank11854 : Fin 2 → Cell := twoBank p11854 ray11854
theorem signs11854 : ∀ j, Signs p11854 (bank11854 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11855 := params 14
abbrev ray11855 := rays 14
def bank11855 : Fin 2 → Cell := twoBank p11855 ray11855
theorem signs11855 : ∀ j, Signs p11855 (bank11855 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11856 := params 15
abbrev ray11856 := rays 15
def bank11856 : Fin 2 → Cell := twoBank p11856 ray11856
theorem signs11856 : ∀ j, Signs p11856 (bank11856 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11857 := params 16
abbrev ray11857 := rays 16
def bank11857 : Fin 2 → Cell := twoBank p11857 ray11857
theorem signs11857 : ∀ j, Signs p11857 (bank11857 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11858 := params 17
abbrev ray11858 := rays 17
def bank11858 : Fin 2 → Cell := twoBank p11858 ray11858
theorem signs11858 : ∀ j, Signs p11858 (bank11858 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11859 := params 18
abbrev ray11859 := rays 18
def bank11859 : Fin 2 → Cell := twoBank p11859 ray11859
theorem signs11859 : ∀ j, Signs p11859 (bank11859 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11860 := params 19
abbrev ray11860 := rays 19
def bank11860 : Fin 2 → Cell := twoBank p11860 ray11860
theorem signs11860 : ∀ j, Signs p11860 (bank11860 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11861 := params 20
abbrev ray11861 := rays 20
def bank11861 : Fin 2 → Cell := twoBank p11861 ray11861
theorem signs11861 : ∀ j, Signs p11861 (bank11861 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11862 := params 21
abbrev ray11862 := rays 21
def bank11862 : Fin 2 → Cell := twoBank p11862 ray11862
theorem signs11862 : ∀ j, Signs p11862 (bank11862 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11863 := params 22
abbrev ray11863 := rays 22
def bank11863 : Fin 2 → Cell := twoBank p11863 ray11863
theorem signs11863 : ∀ j, Signs p11863 (bank11863 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11864 := params 23
abbrev ray11864 := rays 23
def bank11864 : Fin 2 → Cell := twoBank p11864 ray11864
theorem signs11864 : ∀ j, Signs p11864 (bank11864 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11865 := params 24
abbrev ray11865 := rays 24
def bank11865 : Fin 2 → Cell := twoBank p11865 ray11865
theorem signs11865 : ∀ j, Signs p11865 (bank11865 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11866 := params 25
abbrev ray11866 := rays 25
def bank11866 : Fin 2 → Cell := twoBank p11866 ray11866
theorem signs11866 : ∀ j, Signs p11866 (bank11866 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11867 := params 26
abbrev ray11867 := rays 26
def bank11867 : Fin 2 → Cell := twoBank p11867 ray11867
theorem signs11867 : ∀ j, Signs p11867 (bank11867 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11868 := params 27
abbrev ray11868 := rays 27
def bank11868 : Fin 2 → Cell := twoBank p11868 ray11868
theorem signs11868 : ∀ j, Signs p11868 (bank11868 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11869 := params 28
abbrev ray11869 := rays 28
def bank11869 : Fin 2 → Cell := twoBank p11869 ray11869
theorem signs11869 : ∀ j, Signs p11869 (bank11869 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11870 := params 29
abbrev ray11870 := rays 29
def bank11870 : Fin 2 → Cell := twoBank p11870 ray11870
theorem signs11870 : ∀ j, Signs p11870 (bank11870 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11871 := params 30
abbrev ray11871 := rays 30
def bank11871 : Fin 2 → Cell := twoBank p11871 ray11871
theorem signs11871 : ∀ j, Signs p11871 (bank11871 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11872 := params 31
abbrev ray11872 := rays 31
def bank11872 : Fin 2 → Cell := twoBank p11872 ray11872
theorem signs11872 : ∀ j, Signs p11872 (bank11872 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11841_11872
