/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9686;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Successor namespace extension, 2026-11-03, Zhongpai Gao with AI assistance.
Original source: AxiomMath/DedekindZetaZeroFree at09afbb4ce6570c1615d58509dc197fc9f0956b7d;
starting refinement: Gaozhongpai/DedekindZetaZeroFree at829193272c1eaf223bb7228fbfb9003f414808e9.
Original path: DedekindZetaZeroFree/ZeroDetection/ExceptionalZeros/Poisson/RightHalfPlane.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.LogarithmicDiskBounds

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.DetectEuler

noncomputable section

open _root_.DedekindZetaZeroFree _root_.DedekindZetaZeroFree.Quantitative.DetectorDef
open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.DetectorDef
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem idealLSeries_ne_zero_of_one_lt (ω : Detector.PrimitiveFrequencyCharacter F) (s : ℂ)
    (hs : 1 < s.re) : Detector.idealLSeries F ω.character s ≠ 0 := by
  obtain ⟨_, -, hf⟩ := ReciprocalLogDiskAux.euler_log_facts F
  obtain ⟨-, hexp, -⟩ := hf ω
  rw [← hexp s hs]
  exact Complex.exp_ne_zero _

theorem IsLZero.re_le_one {ω : Detector.PrimitiveFrequencyCharacter F} {s : ℂ}
    (h : IsLZero ω s) : s.re ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨-, g, -, hg, hgs⟩ := h
  exact idealLSeries_ne_zero_of_one_lt ω s hlt (by rw [← hg s hlt]; exact hgs)

end

end DedekindZetaZeroFree.Quantitative.DetectEuler

end Refinement9672
