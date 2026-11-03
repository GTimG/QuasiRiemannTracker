/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/Borel/RootFibersAndHaar.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Adeles.Characters.CompactAbelianAndAdelicUniqueness
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Adeles.Quotients.AdditiveCompactness
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Torus.AdelicSmoothFunctionTopology
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Periods.WildPartialPeriodFactorization

@[expose] public section

noncomputable section
open scoped NumberField
open NumberField IsDedekindDomain MeasureTheory
namespace DedekindZetaZeroFree.KPWildRawSourceConstruction

def sourceFiber (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (b : KPGlobalTorusFunctionData.borel F ζ hζ) :
    (KPGlobalTorusFunctionData.G F ζ hζ → ℂ) →ₗ[ℂ]
      (KPCompactFourier.AdditiveQuotient F → ℂ) where
  toFun θ x := θ (KPGlobalTorusFunctionData.N F ζ hζ
    (KPCompactFourier.representative F x) * b.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end DedekindZetaZeroFree.KPWildRawSourceConstruction

namespace DedekindZetaZeroFree.KPWildKernelSource

def rawBorelRootFiber (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (θ : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (b : KPGlobalTorusFunctionData.borel F ζ hζ)
    (x : KPCompactFourier.AdditiveQuotient F) : ℂ :=
  θ (KPGlobalTorusFunctionData.N F ζ hζ (KPCompactFourier.representative F x) * b.val)

end DedekindZetaZeroFree.KPWildKernelSource

end
