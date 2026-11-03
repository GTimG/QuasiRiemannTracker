/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/PartialPeriodSourcesAndRootCoinvariants.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Periods.ScalarQuotientsAndFourierDescent
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Periods.CompactKernelOrbitData
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.RankOne.Borel.TorusRetraction

@[expose] public section

section

noncomputable section

open scoped NumberField TensorProduct Classical

open NumberField IsDedekindDomain

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000

set_option maxRecDepth 4096

set_option synthInstance.maxHeartbeats 1000000

namespace DedekindZetaZeroFree.KPWildActualSectionAction

open KPGlobalResidualConstruction KPWildPartialPeriodFactorization

open KPLocalExceptionalConstruction

open KPKirillovGenuineSectionCharts

open _root_.DedekindZetaZeroFree.KPWildActualScalarPeriodSource renaming scalarSection → scalarSection

open _root_.DedekindZetaZeroFree.KPWildActualScalarPeriodSource renaming scalarSectionAdd → scalarSectionAdd

open _root_.DedekindZetaZeroFree.KPWildActualScalarPeriodSource renaming scalarTensor → scalarTensor

attribute [local instance] scalarSectionAdd

end DedekindZetaZeroFree.KPWildActualSectionAction

end

end

section

noncomputable section

open scoped NumberField TensorProduct Classical

open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPWildActualFullImageAction

open KPGlobalResidualConstruction KPWildPartialPeriodFactorization KPLocalExceptionalConstruction

open _root_.DedekindZetaZeroFree.KPWildActualScalarPeriodSource renaming scalarSection → scalarSection

open _root_.DedekindZetaZeroFree.KPWildActualScalarPeriodSource renaming scalarTensor → scalarTensor

open _root_.DedekindZetaZeroFree.KPWildActualScalarPeriodSource renaming scalarSectionAdd → scalarSectionAdd

attribute [local instance] scalarSectionAdd

end DedekindZetaZeroFree.KPWildActualFullImageAction

end

end

section

noncomputable section

open scoped NumberField TensorProduct Classical

open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPWildActualFullImageAction

open KPGlobalResidualConstruction KPWildPartialPeriodFactorization KPLocalExceptionalConstruction

open _root_.DedekindZetaZeroFree.KPWildActualScalarPeriodSource renaming scalarSection → scalarSection

open _root_.DedekindZetaZeroFree.KPWildActualScalarPeriodSource renaming scalarTensor → scalarTensor

open _root_.DedekindZetaZeroFree.KPWildActualScalarPeriodSource renaming scalarSectionAdd → scalarSectionAdd

attribute [local instance] scalarSectionAdd

end DedekindZetaZeroFree.KPWildActualFullImageAction

end

end
