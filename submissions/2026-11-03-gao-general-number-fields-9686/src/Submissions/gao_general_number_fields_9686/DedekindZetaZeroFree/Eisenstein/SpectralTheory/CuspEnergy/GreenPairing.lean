/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/SpectralTheory/CuspEnergy/GreenPairing.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.RadialTests

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPCompactGreenRadialIntegrability
open KPMeanZeroWeightedEnergy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)}
    {ρ : S →* rootsOfUnity 3 F} {V : Submodule ℂ ℂ} {T : ℝ}

def rawCutoffUpstairs (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (x : HyperbolicChart.Space (KPCuspLogShape.dimension F)) : ℂ :=
  (η (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
    (arch (KPCuspLogShape.dimension F) x)) : ℂ) *
      v.val (arch (KPCuspLogShape.dimension F) x)

def rawCutoffGradientSq (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (p : KPCuspCharts.Coordinates F) : ℝ :=
  let w := HyperbolicChart.differential (KPCuspLogShape.dimension F)
    (rawCutoffUpstairs v η)
    (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))
  ∑ i, ∑ k, ‖w i k‖ ^ 2

def rawWeightedGreenDensity (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (p : KPCuspCharts.Coordinates F) : ℝ :=
  let x := real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p)
  (HyperbolicChart.pairing (KPCuspLogShape.dimension F)
    (HyperbolicChart.differential (KPCuspLogShape.dimension F)
      (rawCutoffUpstairs v (fun t => η t ^ 2)) x)
    (HyperbolicChart.differential (KPCuspLogShape.dimension F)
      (v.val ∘ arch (KPCuspLogShape.dimension F)) x)).re

end DedekindZetaZeroFree.KPCompactGreenRadialIntegrability

end
