/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Residues/ZeroProfiles/FiniteCovariance.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Induction.TensorProducts.FlatSectionsAndResidues

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.TensorActionSource
open KPLiteralRaw
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {K : Subgroup (G F ζ hζ)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

abbrev literalZeroProfiles (K : Subgroup (G F ζ hζ)) := (literalFlatZero K).range

def literalZeroProfileEquiv (hK : IwasawaCompact F ζ hζ K) :
    literalFlatModule K ≃ₗ[ℂ] literalZeroProfiles K :=
  LinearEquiv.ofInjective (literalFlatZero K) (literalFlatZero_injective hK)

@[simp] theorem literalZeroProfileEquiv_val (hK : IwasawaCompact F ζ hζ K)
    (f : literalFlatModule K) :
    (literalZeroProfileEquiv hK f).val = f.val 0 := rfl

theorem literalZeroProfiles_finite_mem (hK : IwasawaCompact F ζ hζ K)
    (q : KPFinitePlace F) (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (f : literalZeroProfiles K) :
    rightAction F ζ hζ
      (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inr q) a))
      f.val ∈ literalZeroProfiles K := by
  obtain ⟨u, hu⟩ := f.property
  obtain ⟨n, c, v, hv⟩ :=
    KPLiteralTensorEquivariance.FiniteClearedCovariance.finite_translate_exponential_expansion
      F ζ hζ K hK (asLiteralFlat u) q a
  have he : rightAction F ζ hζ
      (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inr q) a)) f.val =
      ∑ i, (v i).val 0 := by
    funext g
    change f.val (g * _) = _
    rw [← hu]
    simpa only [literalFlatZero, LinearMap.comp_apply, LinearMap.proj_apply,
      Submodule.subtype_apply, zero_mul, Complex.exp_zero, one_mul,
      Finset.sum_apply] using hv 0 g
  rw [he]
  apply Submodule.sum_mem
  intro i _
  exact ⟨(v i : literalFlatModule K), rfl⟩

def literalZeroProfileResidue (hK : IwasawaCompact F ζ hζ K)
    (E N : Flat F ζ hζ K → ℂ → Functions F ζ hζ)
    (hg : ExceptionalGerm F ζ hζ K E N)
    (hm : ∀ f g, MeromorphicOn (fun z => E f z g) KPContinuation.spectralDomain) :
    literalZeroProfiles K →ₗ[ℂ] Functions F ζ hζ :=
  (literalFlatResidue hK E N hg hm).comp (literalZeroProfileEquiv hK).symm.toLinearMap

@[simp] theorem literalZeroProfileResidue_flat (hK : IwasawaCompact F ζ hζ K)
    (E N : Flat F ζ hζ K → ℂ → Functions F ζ hζ)
    (hg : ExceptionalGerm F ζ hζ K E N)
    (hm : ∀ f g, MeromorphicOn (fun z => E f z g) KPContinuation.spectralDomain)
    (f : literalFlatModule K) :
    literalZeroProfileResidue hK E N hg hm (literalZeroProfileEquiv hK f) =
      N (asLiteralFlat f) 0 := by
  simp only [literalZeroProfileResidue, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rfl

def literalZeroProfileFinite (hK : IwasawaCompact F ζ hζ K)
    (q : KPFinitePlace F) (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :
    literalZeroProfiles K →ₗ[ℂ] literalZeroProfiles K :=
  ((rightAction F ζ hζ
    (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inr q) a))).comp
    (literalZeroProfiles K).subtype).codRestrict _
      (fun f => literalZeroProfiles_finite_mem hK q a f)

theorem literalZeroProfileResidue_finite (hK : IwasawaCompact F ζ hζ K)
    (E N : Flat F ζ hζ K → ℂ → Functions F ζ hζ)
    (hg : ExceptionalGerm F ζ hζ K E N)
    (hm : ∀ f g, MeromorphicOn (fun z => E f z g) KPContinuation.spectralDomain)
    (q : KPFinitePlace F) (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (f : literalZeroProfiles K) (g : G F ζ hζ) :
    literalZeroProfileResidue hK E N hg hm (literalZeroProfileFinite hK q a f) g =
      literalZeroProfileResidue hK E N hg hm f
        (g * KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inr q) a)) := by
  let u := (literalZeroProfileEquiv hK).symm f
  let v := (literalZeroProfileEquiv hK).symm (literalZeroProfileFinite hK q a f)
  have hu : u.val 0 = f.val := congrArg Subtype.val
    ((literalZeroProfileEquiv hK).apply_symm_apply f)
  have hv : v.val 0 = (literalZeroProfileFinite hK q a f).val := congrArg Subtype.val
    ((literalZeroProfileEquiv hK).apply_symm_apply (literalZeroProfileFinite hK q a f))
  change N (asLiteralFlat v) 0 g = N (asLiteralFlat u) 0 _
  apply literal_finite_residue_covariance hK E N hg hm
  intro x
  rw [hv, hu]
  rfl

end DedekindZetaZeroFree.FourierContinuation.TensorActionSource

end
