/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10849_10880
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97151593143046,97151209453555,97150825744173,97150442014901,97150058265739,97149674496688,97149290707749,97148906898921,97148523070206,97148139221604,97147755353115,97147371464740,97146987556479,97146603628333,97146219680302,97145835712387,97145451724589,97145067716907,97144683689343,97144299641896,97143915574568,97143531487359,97143147380269,97142763253299,97142379106449,97141994939720,97141610753112,97141226546626,97140842320262,97140458074021,97140073807903,97139689521909,97139305216040]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10848+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10849 := params 0
abbrev ray10849 := rays 0
def bank10849 : Fin 2 → Cell := twoBank p10849 ray10849
theorem signs10849 : ∀ j, Signs p10849 (bank10849 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10850 := params 1
abbrev ray10850 := rays 1
def bank10850 : Fin 2 → Cell := twoBank p10850 ray10850
theorem signs10850 : ∀ j, Signs p10850 (bank10850 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10851 := params 2
abbrev ray10851 := rays 2
def bank10851 : Fin 2 → Cell := twoBank p10851 ray10851
theorem signs10851 : ∀ j, Signs p10851 (bank10851 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10852 := params 3
abbrev ray10852 := rays 3
def bank10852 : Fin 2 → Cell := twoBank p10852 ray10852
theorem signs10852 : ∀ j, Signs p10852 (bank10852 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10853 := params 4
abbrev ray10853 := rays 4
def bank10853 : Fin 2 → Cell := twoBank p10853 ray10853
theorem signs10853 : ∀ j, Signs p10853 (bank10853 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10854 := params 5
abbrev ray10854 := rays 5
def bank10854 : Fin 2 → Cell := twoBank p10854 ray10854
theorem signs10854 : ∀ j, Signs p10854 (bank10854 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10855 := params 6
abbrev ray10855 := rays 6
def bank10855 : Fin 2 → Cell := twoBank p10855 ray10855
theorem signs10855 : ∀ j, Signs p10855 (bank10855 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10856 := params 7
abbrev ray10856 := rays 7
def bank10856 : Fin 2 → Cell := twoBank p10856 ray10856
theorem signs10856 : ∀ j, Signs p10856 (bank10856 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10857 := params 8
abbrev ray10857 := rays 8
def bank10857 : Fin 2 → Cell := twoBank p10857 ray10857
theorem signs10857 : ∀ j, Signs p10857 (bank10857 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10858 := params 9
abbrev ray10858 := rays 9
def bank10858 : Fin 2 → Cell := twoBank p10858 ray10858
theorem signs10858 : ∀ j, Signs p10858 (bank10858 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10859 := params 10
abbrev ray10859 := rays 10
def bank10859 : Fin 2 → Cell := twoBank p10859 ray10859
theorem signs10859 : ∀ j, Signs p10859 (bank10859 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10860 := params 11
abbrev ray10860 := rays 11
def bank10860 : Fin 2 → Cell := twoBank p10860 ray10860
theorem signs10860 : ∀ j, Signs p10860 (bank10860 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10861 := params 12
abbrev ray10861 := rays 12
def bank10861 : Fin 2 → Cell := twoBank p10861 ray10861
theorem signs10861 : ∀ j, Signs p10861 (bank10861 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10862 := params 13
abbrev ray10862 := rays 13
def bank10862 : Fin 2 → Cell := twoBank p10862 ray10862
theorem signs10862 : ∀ j, Signs p10862 (bank10862 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10863 := params 14
abbrev ray10863 := rays 14
def bank10863 : Fin 2 → Cell := twoBank p10863 ray10863
theorem signs10863 : ∀ j, Signs p10863 (bank10863 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10864 := params 15
abbrev ray10864 := rays 15
def bank10864 : Fin 2 → Cell := twoBank p10864 ray10864
theorem signs10864 : ∀ j, Signs p10864 (bank10864 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10865 := params 16
abbrev ray10865 := rays 16
def bank10865 : Fin 2 → Cell := twoBank p10865 ray10865
theorem signs10865 : ∀ j, Signs p10865 (bank10865 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10866 := params 17
abbrev ray10866 := rays 17
def bank10866 : Fin 2 → Cell := twoBank p10866 ray10866
theorem signs10866 : ∀ j, Signs p10866 (bank10866 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10867 := params 18
abbrev ray10867 := rays 18
def bank10867 : Fin 2 → Cell := twoBank p10867 ray10867
theorem signs10867 : ∀ j, Signs p10867 (bank10867 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10868 := params 19
abbrev ray10868 := rays 19
def bank10868 : Fin 2 → Cell := twoBank p10868 ray10868
theorem signs10868 : ∀ j, Signs p10868 (bank10868 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10869 := params 20
abbrev ray10869 := rays 20
def bank10869 : Fin 2 → Cell := twoBank p10869 ray10869
theorem signs10869 : ∀ j, Signs p10869 (bank10869 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10870 := params 21
abbrev ray10870 := rays 21
def bank10870 : Fin 2 → Cell := twoBank p10870 ray10870
theorem signs10870 : ∀ j, Signs p10870 (bank10870 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10871 := params 22
abbrev ray10871 := rays 22
def bank10871 : Fin 2 → Cell := twoBank p10871 ray10871
theorem signs10871 : ∀ j, Signs p10871 (bank10871 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10872 := params 23
abbrev ray10872 := rays 23
def bank10872 : Fin 2 → Cell := twoBank p10872 ray10872
theorem signs10872 : ∀ j, Signs p10872 (bank10872 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10873 := params 24
abbrev ray10873 := rays 24
def bank10873 : Fin 2 → Cell := twoBank p10873 ray10873
theorem signs10873 : ∀ j, Signs p10873 (bank10873 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10874 := params 25
abbrev ray10874 := rays 25
def bank10874 : Fin 2 → Cell := twoBank p10874 ray10874
theorem signs10874 : ∀ j, Signs p10874 (bank10874 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10875 := params 26
abbrev ray10875 := rays 26
def bank10875 : Fin 2 → Cell := twoBank p10875 ray10875
theorem signs10875 : ∀ j, Signs p10875 (bank10875 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10876 := params 27
abbrev ray10876 := rays 27
def bank10876 : Fin 2 → Cell := twoBank p10876 ray10876
theorem signs10876 : ∀ j, Signs p10876 (bank10876 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10877 := params 28
abbrev ray10877 := rays 28
def bank10877 : Fin 2 → Cell := twoBank p10877 ray10877
theorem signs10877 : ∀ j, Signs p10877 (bank10877 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10878 := params 29
abbrev ray10878 := rays 29
def bank10878 : Fin 2 → Cell := twoBank p10878 ray10878
theorem signs10878 : ∀ j, Signs p10878 (bank10878 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10879 := params 30
abbrev ray10879 := rays 30
def bank10879 : Fin 2 → Cell := twoBank p10879 ray10879
theorem signs10879 : ∀ j, Signs p10879 (bank10879 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10880 := params 31
abbrev ray10880 := rays 31
def bank10880 : Fin 2 → Cell := twoBank p10880 ray10880
theorem signs10880 : ∀ j, Signs p10880 (bank10880 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10849_10880
