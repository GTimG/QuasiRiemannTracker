/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Continuation/RationalSummands/MixedJets.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.SpectralTheory.GreenIdentity.PairingsAndFluxDefinitions
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Induction.Cubic.SphericalFlatFamilies
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Continuation.Chambers.L2DefectData

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal BigOperators
open Topology

namespace DedekindZetaZeroFree.KPContActualChamberNormalSeries

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev V : Set ℂ := KPChamberL2Defect.chamber

abbrev Q := KPChamberBruhatTwoCells.RationalQuotient F

abbrev G := KPGlobalTorusFunctionData.G F ζ hζ

def lift (q : Q F) : G F ζ hζ :=
  KPContFlatRationalCosetCovariance.matrixRationalHom F ζ hζ (Quotient.out q)

abbrev Word := List (KPSmoothActualFlowData.B F)

def rightWord (w : Word F) (u : G F ζ hζ → ℂ) : G F ζ hζ → ℂ :=
  w.foldr (fun b v => KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 v) u

def mixedJet (u : ℂ → G F ζ hζ → ℂ) (k : ℕ) (w : Word F)
    (s : ℂ) : G F ζ hζ → ℂ :=
  rightWord F ζ hζ w (fun g => iteratedDerivWithin k (fun z => u z g) V s)

variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (f : ℂ → S)

def term (q : Q F) (s : ℂ) (g : G F ζ hζ) : ℂ :=
  KPContActualSphericalFlatStage.L F ζ hζ U ι s (f s) (lift F ζ hζ q * g)

end DedekindZetaZeroFree.KPContActualChamberNormalSeries

end
