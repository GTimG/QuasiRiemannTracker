/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Induction/SphericalTensor/FlatPreimages.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Induction.Spherical.FlatSources

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory RootDerivatives
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

structure SphericalFlatPreimages (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (A : JointExteriorCoefficientSources R N) (D : SphericalTransportData R A)
    (P : NormalizedSphericalTensor R A D) where
  sources : AdmissibleFlatSources R
  dq_exact : sources.dq = A.sources.dq
  residue : ∀ v, FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 (sources.flat v)
  residue_exact : ∀ v, (residue v).numerator 0 =
    tensorFunction R A.factorization D.tensor.stage P.entries
  source_nonzero : ∀ v, (sources.flat v).val 0 ≠ 0
  residue_nonzero : ∀ v, (residue v).numerator 0 ≠ 0
  period_nonzero : ∀ v, fourier R sources.dq ((residue v).numerator 0) 1 ≠ 0

theorem sphericalFlatPreimages_nonempty
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R}
    (A : JointExteriorCoefficientSources R N) (D : SphericalTransportData R A)
    (P : NormalizedSphericalTensor R A D) :
    Nonempty (SphericalFlatPreimages R A D P) := by
  obtain ⟨Q,hQ,C,hC,hf,hne,hper⟩ := normalized_spherical_flat_sources R A D P
  exact ⟨{
    sources := Q
    dq_exact := hQ
    residue := C
    residue_exact := hC
    source_nonzero := hf
    residue_nonzero := hne
    period_nonzero := hper }⟩

end DedekindZetaZeroFree.ThetaExpansion

end
