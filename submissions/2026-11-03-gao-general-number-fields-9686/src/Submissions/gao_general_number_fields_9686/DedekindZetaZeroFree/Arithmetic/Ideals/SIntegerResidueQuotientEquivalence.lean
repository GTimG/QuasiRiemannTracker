/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/Ideals/SIntegerResidueQuotientEquivalence.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.Ideals.SIntegerResidueQuotientInjectivity
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.Ideals.SIntegerResidueQuotientSurjectivity

@[expose] public section

open scoped NumberField
open NumberField

namespace DedekindZetaZeroFree.ArithGaussCRT

noncomputable section
variable {F : Type} [Field F] [NumberField F]

def exteriorQuotientEquiv (A : SArithmeticData F) (I : A.Exterior) :
    (𝓞 F ⧸ I.val) ≃+* (A.R ⧸ A.extendIdeal I) :=
  RingEquiv.ofBijective
    (Ideal.quotientMap (A.extendIdeal I) (algebraMap (𝓞 F) A.R)
      (show I.val ≤ (A.extendIdeal I).comap (algebraMap (𝓞 F) A.R) from
        Ideal.le_comap_map))
    ⟨exteriorQuotientMap_injective A I, exteriorQuotientMap_surjective A I⟩

@[simp] theorem exteriorQuotientEquiv_mk (A : SArithmeticData F) (I : A.Exterior)
    (x : 𝓞 F) :
    exteriorQuotientEquiv A I (Ideal.Quotient.mk I.val x) =
      Ideal.Quotient.mk (A.extendIdeal I) (algebraMap (𝓞 F) A.R x) := rfl

end

end DedekindZetaZeroFree.ArithGaussCRT
