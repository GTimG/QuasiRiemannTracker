/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9672;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Successor namespace extension, 2026-11-03, Zhongpai Gao with AI assistance.
Original source: AxiomMath/DedekindZetaZeroFree at09afbb4ce6570c1615d58509dc197fc9f0956b7d;
starting refinement: Gaozhongpai/DedekindZetaZeroFree at829193272c1eaf223bb7228fbfb9003f414808e9.
Original path: DedekindZetaZeroFree/Moments/Probes/Poisson/Scales.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public import Submissions.gao_general_number_fields_9672.Refinement9672.FrozenBaseline

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.Scales

noncomputable section

def xExponent : ℝ := 67 / 100

def yExponent : ℝ := 234 / 625

def smoothingExponent : ℝ := 33 / 100

def supportExponent : ℝ := 2611 / 2500

def reflectedExponent : ℝ := 893 / 2500

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

end Refinement9672
