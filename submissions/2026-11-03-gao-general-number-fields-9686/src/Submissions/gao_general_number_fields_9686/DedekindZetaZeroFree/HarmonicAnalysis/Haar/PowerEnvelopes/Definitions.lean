/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Haar/PowerEnvelopes/Definitions.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace DedekindZetaZeroFree.ThetaRawSheetEnvelope.WeightedWhittakerSheets
noncomputable section

def finitePowerMajorant (M r : ℝ) : ℝ :=
  if r ≤ M then Real.rpow r (1 / 4 : ℝ) else 0

def archPowerMajorant (B r : ℝ) : ℝ :=
  min (Real.rpow r (1 / 4 : ℝ)) (Real.rpow r (-B))

theorem finitePowerMajorant_nonneg (M r : ℝ) (hr : 0 ≤ r) :
    0 ≤ finitePowerMajorant M r := by
  unfold finitePowerMajorant
  split_ifs
  · exact Real.rpow_nonneg hr _
  · exact le_refl 0

theorem archPowerMajorant_nonneg (B r : ℝ) (hr : 0 ≤ r) :
    0 ≤ archPowerMajorant B r := by
  exact le_min (Real.rpow_nonneg hr _) (Real.rpow_nonneg hr _)

end
end DedekindZetaZeroFree.ThetaRawSheetEnvelope.WeightedWhittakerSheets
