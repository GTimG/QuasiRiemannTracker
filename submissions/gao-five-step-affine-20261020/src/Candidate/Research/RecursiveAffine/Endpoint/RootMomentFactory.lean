/- The single literal analytic interface for the final detector and numerator.
Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Moment.InitialAffineContract
import Submissions.akashlevy_20261009_weighted_numerator.WeightedQRH.HighRows.WeightedSourceCellGeometry

set_option autoImplicit false
namespace Cycle153Endpoint
noncomputable section
open scoped ComplexConjugate
open Filter OAI.SevenEighths HeckeFamily CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource

/-- The mesh is chosen before the ambient cardinality, weighted source,
fixed seed character and profiles. The only analytic field is the literal
initial energy estimate at radius `Z`, with the original fixed `Q` and
seed one. The source is unchanged by excluding the unit ideal, as proved
for both actual endpoint consumers. An implementation must construct this class from the actual
finite-depth proof; it is not an endpoint or an admission assertion. -/
class RootMomentFactory where
  mesh : ℝ→ℝ
  mesh_pos : ∀{ε:ℝ},0<ε→0< mesh ε
  moment : ∀{D:WeightedQRH.MomentData}
    (S:OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D)
    (η:Character),η.modulus≤ Ideal.span {fixedBadMask}→
    excluded η 1=η→
    ∀(ε meshUsed bΦ:ℝ),0<ε→0< meshUsed→meshUsed≤ mesh ε→2≤ bΦ→
    51/100≤ HeckeZeroSupremum.beta→HeckeZeroSupremum.beta≤7/8→
    ∃degree:ℕ,∃Sd:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,
      OAI.SevenEighths.Cycle153EndpointMoment.InitialAffineAt
        (α:=Fin D.N) S.modulus ⊤ le_top
        (fun x=>conj (S.W x)) 2 (1/4) (9/4) bΦ meshUsed (33/50) (33/50) 1 1 ε Z
        η η (weighted_sourceFixedIdeal S) degree Sd C
end
end Cycle153Endpoint
