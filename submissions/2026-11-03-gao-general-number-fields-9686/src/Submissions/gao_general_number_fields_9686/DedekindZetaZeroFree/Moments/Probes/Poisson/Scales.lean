/-
2026-11-03 refinement by Zhongpai Gao (https://github.com/Gaozhongpai).
The following header records the PR #114 source provenance at 09afbb4ce6570c1615d58509dc197fc9f0956b7d.
This file now contains the native parameter refinement at
829193272c1eaf223bb7228fbfb9003f414808e9; local imports are relocated under Submissions.gao_general_number_fields_9686.
Original declaration namespaces and all source attribution are retained.
Native compilation and tracker admission remain pending; see Candidate.Provenance.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Moments/Probes/Poisson/Scales.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.Scales

noncomputable section

def xExponent : ℝ := 67 / 100

def yExponent : ℝ := 943 / 2500

def smoothingExponent : ℝ := 33 / 100

def supportExponent : ℝ := 1309 / 1250

def reflectedExponent : ℝ := 1793 / 5000

def smallCutoffExponent : ℝ := 1 / 5

def largeCutoffExponent : ℝ := 3301 / 10000

def contourOffset : ℝ := 1 / 10000000

def rightLine : ℝ := 1 + contourOffset

def goodLine : ℝ := 8801 / 10000

def wLine : ℝ := 3 / 25

def zLine : ℝ := 2 / 5

def tailShift : ℝ := 50000

def kernelExponent (x y z : ℝ) : ℝ := xExponent / 2 + x - 1 + smoothingExponent * z + yExponent * (y - 1)

def spectralExponent (s : ℝ) : ℝ := s - 61 / 100

def mainExponent : ℝ := 39 / 100

def xScale (Z : ℝ) : ℝ := Z ^ xExponent

def yScale (Z : ℝ) : ℝ := Z ^ yExponent

theorem xScale_pos (Z : ℝ) (hZ : 0 < Z) : 0 < xScale Z := Real.rpow_pos_of_pos hZ _

theorem yScale_pos (Z : ℝ) (hZ : 0 < Z) : 0 < yScale Z := Real.rpow_pos_of_pos hZ _

theorem rightLine_eq : rightLine = 10000001 / 10000000 := by
  unfold rightLine contourOffset; norm_num

end

end DedekindZetaZeroFree.Quantitative.Scales
