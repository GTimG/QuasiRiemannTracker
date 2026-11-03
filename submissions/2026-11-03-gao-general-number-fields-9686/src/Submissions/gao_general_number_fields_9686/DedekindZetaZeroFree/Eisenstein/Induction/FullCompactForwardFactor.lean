/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Induction/FullCompactForwardFactor.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Iwasawa.IntegralCompact
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Kubota.FullIntegralCompactIwasawa

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.CurrentFullCompactBinding
open KPActualReflectionData KPLocalPrincipalSeries KPLocalExceptionalConstruction
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
 theorem forwardAbs_eq (q : KPFinitePlace F)
    (g : ActualCover F R.A.zeta12 R.A.primitive_zeta12 q) :
    LocalCompactChange.forwardAbs F R.A.zeta12 R.A.primitive_zeta12 q (C.canonical q)
      (FaithfulSource.RepairedInducing.fullCompact R P C q) g =
    LocalCompactChange.forwardAbs F R.A.zeta12 R.A.primitive_zeta12 q (C.canonical q)
      (ActualFullCompactTransport.fullCompactIwasawa F R.A.zeta12 R.A.primitive_zeta12 q
        (C.canonical q)) g := by
  let J := FaithfulSource.RepairedInducing.fullCompact R P C q
  let J' := ActualFullCompactTransport.fullCompactIwasawa F R.A.zeta12 R.A.primitive_zeta12 q
    (C.canonical q)
  have hJ : J.compact.toOpenSubgroup.toSubgroup = J'.compact.toOpenSubgroup.toSubgroup :=
    (FaithfulSource.RepairedInducing.fullCompact_eq R P C q).trans
      (ActualFullCompactTransport.fullCompactIwasawa_compact F R.A.zeta12
        R.A.primitive_zeta12 q (C.canonical q)).symm
  have hk : (J.compactPart g).val ∈ J'.compact.toOpenSubgroup := by
    change (J.compactPart g).val ∈ J'.compact.toOpenSubgroup.toSubgroup
    rw [← hJ]
    exact (J.compactPart g).property
  have hg : g = (J.borelPart g).val * (J.compactPart g).val := J.decomposition g
  change LocalCompactChange.forwardAbs _ _ _ _ _ J g =
    LocalCompactChange.forwardAbs _ _ _ _ _ J' g
  rw [hg, LocalCompactChange.forwardAbs_factorization F R.A.zeta12 R.A.primitive_zeta12 q
    (C.canonical q) J, LocalCompactChange.forwardAbs_factorization F R.A.zeta12
    R.A.primitive_zeta12 q (C.canonical q) J' (J.borelPart g) ⟨_, hk⟩]
end DedekindZetaZeroFree.FourierContinuation.CurrentFullCompactBinding

end
