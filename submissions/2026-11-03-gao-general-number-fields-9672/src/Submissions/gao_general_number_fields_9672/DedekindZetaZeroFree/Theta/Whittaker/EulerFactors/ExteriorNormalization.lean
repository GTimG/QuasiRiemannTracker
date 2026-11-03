/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/EulerFactors/ExteriorNormalization.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Whittaker.Tensors.CompactInvariance
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.HarmonicAnalysis.Haar.LevelProfiles.ProductIntegration

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding
open MomentSources KPGlobalTorusFiniteStages FaithfulSource FaithfulSource.RepairedInducing
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false

theorem exteriorFactor_good (E : Finset (KPFinitePlace F))
    (hD : localDifferentSupport F ⊆ (E : Set _))
    (q : KPFinitePlace F) (hq : q ∉ E) (z : ℂ) :
    exteriorFactor R N z (.inr q) = KPGlobalFiniteSIntertwiner.goodFactor F q z := by
  have hm : PoissonS.integerVolume F q = 1 := by
    rw [CurrentFiniteHaarBinding.integerVolume_eq, localHalfDifferentFactor,
      localDifferentExponent_eq_zero_of_not_mem F E hD q hq]
    norm_num
  rw [exteriorFactor, arithmeticRootScale, hm, Complex.ofReal_one, one_mul]
  exact ExteriorVectorHaar.forwardFactor_eq_goodFactor F q (integerHaar R N q)
    (integerHaar_integer R N q) z

theorem full_exterior_product (E Q : Finset (KPFinitePlace F))
    (hE : C.exceptional ⊆ E) (hQ : C.exceptional ⊆ Q)
    (hD : localDifferentSupport F ⊆ (E : Set _)) (z : ℂ) :
    (∏ p ∈ (fullLevel R P C Q hQ).val \ (fullLevel R P C E hE).val,
      exteriorFactor R N z p) = KPGlobalFiniteSIntertwiner.enlargementFactor F E Q z := by
  have he : (fullLevel R P C Q hQ).val \ (fullLevel R P C E hE).val =
      (Q \ E).map ⟨Sum.inr,Sum.inr_injective⟩ := by
    ext p
    cases p <;> simp [fullLevel,LiteralSource.cofactorSourceLevel]
  rw [he, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro q hq
  exact exteriorFactor_good R N E hD q (Finset.mem_sdiff.mp hq).2 z

end DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding

end
