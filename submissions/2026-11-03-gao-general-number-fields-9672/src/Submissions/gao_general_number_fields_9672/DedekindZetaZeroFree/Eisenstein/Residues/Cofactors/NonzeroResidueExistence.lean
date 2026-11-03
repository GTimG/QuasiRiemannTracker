/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Residues/Cofactors/NonzeroResidueExistence.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.NonzeroUpperCoefficient

@[expose] public section

noncomputable section
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox renaming adelic_measure_box → adelic_measure_box
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox renaming finite_measure_sigmaFinite → finite_measure_sigmaFinite
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox renaming arch_measure_sigmaFinite → arch_measure_sigmaFinite
open _root_.DedekindZetaZeroFree.KPComplexIntertwinerParameterMajorant renaming forwardSection_real_formula → forwardSection_real_formula
open scoped Classical NumberField TensorProduct BigOperators Topology
open Filter
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber
open KPLocalPrincipalSeries KPGlobalTorusFiniteStages KPLocalExceptionalConstruction
open KPGlobalResidualConstruction
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem exists_coreResidue_ne_zero_unconditional :
    ∃ x : RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C),
      coreResidue R P C x ≠ 0 :=
  exists_coreResidue_ne_zero R P C

end DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber

end
