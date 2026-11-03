/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/FirstRootSphericalSeedData.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Profiles.FirstRootSphericalRadialModel

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

structure FirstRootSphericalSeed (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) where
  base : JointExteriorCoefficientSources R N
  neighborhood : ∀ p : R.A.Sf, Set (p.val.adicCompletion F)ˣ
  open_neighborhood : ∀ p, IsOpen (neighborhood p)
  one_neighborhood : ∀ p, (1 : (p.val.adicCompletion F)ˣ) ∈ neighborhood p
  spherical_near : ∀ v y, (∀ p, y.2 p ∈ neighborhood p) →
    fourier R base.sources.dq (base.realization.theta v) (diagonal R y) =
      firstRootSphericalProduct R y

end DedekindZetaZeroFree.ThetaExpansion

end
