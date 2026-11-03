/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Quotients/ComplexRadialCoordinates.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Quotients.ExteriorNormRadialSection
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Analysis.Complex.LogarithmicRadialDerivatives

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SArithmeticData

open NumberField

variable {F : Type} [Field F] [NumberField F]

lemma radialSection_complex (A : SArithmeticData F) (w : InfinitePlace F) (t : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w
      ((A.radialSection (Real.exp t) (Real.exp_pos t)).1 w : w.Completion) =
    (Real.exp (t / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))) : ℂ) := by
  change (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w))
    ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)).symm
      ((Real.exp t ^ (1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))) : ℝ) : ℂ)) = _
  rw [RingEquiv.apply_symm_apply, ← Real.exp_mul]
  congr 2
  ring

lemma radialSection_complex_flow (A : SArithmeticData F) (w : InfinitePlace F)
    (t : ℝ) (z : w.Completionˣ) :
    Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom
      (z * (A.radialSection (Real.exp t) (Real.exp_pos t)).1 w) =
    KPCplxRotatedRapidDecay.logarithmicRadialFlow
      (t / (InfinitePlace.nrComplexPlaces F : ℝ))
      (Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom z) := by
  apply Units.ext
  simp only [Units.coe_map, Units.val_mul, map_mul,
    KPCplxRotatedRapidDecay.logarithmicRadialFlow, Units.val_mk0]
  change InfinitePlace.Completion.extensionEmbedding w (z : w.Completion) *
    InfinitePlace.Completion.extensionEmbedding w
      ((A.radialSection (Real.exp t) (Real.exp_pos t)).1 w : w.Completion) =
    (Real.exp (t / (InfinitePlace.nrComplexPlaces F : ℝ) / 2) : ℂ) *
      InfinitePlace.Completion.extensionEmbedding w (z : w.Completion)
  rw [radialSection_complex]
  have ht : t / (2 * (InfinitePlace.nrComplexPlaces F : ℝ)) =
      t / (InfinitePlace.nrComplexPlaces F : ℝ) / 2 := by ring
  rw [ht, mul_comm]

end DedekindZetaZeroFree.SArithmeticData

end
