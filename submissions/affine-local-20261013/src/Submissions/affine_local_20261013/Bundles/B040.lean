/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.affine_local_20261013.Bundles.B024
import Submissions.affine_local_20261013.Bundles.B033
import Submissions.affine_local_20261013.Bundles.B034
import Submissions.affine_local_20261013.Bundles.B035
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorInverseFields
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorPlainMarkedFineField
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorPlainUnmarkedField
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorPlainUnmarkedRestrictedField
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CappedWidthInduction
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FixedRayInducingTransport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ReflectedSource

/- BEGIN ORIGINAL MODULE Global.Weighted.Target ; sha256 4fa8d20ac9cdd4f03e3f73fc54d9b1729ff67b85792adc886fd8158219a9206e -/
section


namespace Submission20261012.Global
/-- A common reserve halfway across the assumed supremum gap. -/
noncomputable def weightedTarget : ℝ :=
  signal OAI.SevenEighths.HeckeZeroSupremum.beta -
    (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/2
end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Weighted.Target -/

/- BEGIN ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCertifiedBands ; sha256 d41f3d2a7fc675a1e72e02ff0be668a774120dc97ff007f04593d4a28c7e0675 -/
section






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

namespace SevenEighths.ProbeFinalAssemblyCertifiedBands
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open ProbeFinalAssembly ProbeHighRowFamily Parameters
open CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthSchedule CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open ProbeDetectorPlainMarkedFineField ProbeDetectorPlainUnmarkedField
local notation "O"=> HeckeFamily.O

def detectorMesh (Δ t:ℝ):ℝ:=fineMesh 2 0 1 (3/4+2*Δ) (t/4)

lemma detectorMesh_pos {Δ t:ℝ}(hΔ:0<Δ)(ht:0< t):0< detectorMesh Δ t:=by
  exact (bounds 2 (finalSourceCap 2 0 1 (t/4)) (3/4+2*Δ) (t/4)
    (by norm_num) (sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) _)
    (by linarith) (by positivity)).2.2.2.2.1

def DetectorCertifiedBands:Prop:=
  ∀_hβ:(7/8:ℝ)< HeckeZeroSupremum.beta,
  ∀D:HighData (HeckeZeroSupremum.beta-7/8),
    (∀j,D.ell j≤ detectorMesh (HeckeZeroSupremum.beta-7/8) D.t/200)→
  ∀F:SourceData D,∀bΦ:ℝ,0< bΦ→
    CertifiedBand (α:=Fin D.N) F.modulus ⊤ le_top (fun x=> conj (F.W x))
      2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2 (kappaPlain D) (stageError D)
      (count 2 (stageError D))

theorem plain_inputs {Δ:ℝ}{D:HighData Δ}(F:SourceData D)
    (hcert:∀bΦ:ℝ,0< bΦ→CertifiedBand (α:=Fin D.N) F.modulus ⊤ le_top
      (fun x=> conj (F.W x)) 2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2
      (kappaPlain D) (stageError D) (count 2 (stageError D))):
    PositiveFineSourceInput F (detectorMesh Δ D.t) ∧
    (∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) radialSupportUpper
        0 1 2 (D.t/4) U degree control A):=by
  have hp:=fixed_parameters D
  have ht (bΦ:ℝ)(hbΦ:0< bΦ):=
    certified_terminal F.modulus ⊤ le_top (fun x=> conj (F.W x))
      2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2 (kappaPlain D) (stageError D)
      (by norm_num) (by norm_num) hp.2.2.2.2.2.le hp.2.2.1 (hcert bΦ hbΦ)
  have hactual (bΦ:ℝ)(hbΦ:0< bΦ):
      ∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,
      ∃Czero Cpositive:ℝ,0< Czero ∧ 0< Cpositive ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) bΦ 0 1 2
        (stageError D) U degree control Czero ∧
      PositiveAt (α:=Fin D.N) F.modulus ⊤ le_top (fun x=> conj (F.W x))
        2 (1/4) (9/4) bΦ 0 1 (detectorMesh Δ D.t) (33/50) (33/50) 2
        (stageError D) (kappaPlain D) U η₀ (sourceFixedIdeal F) degree control Cpositive:=by
    obtain ⟨degree,control,hbound⟩:=ht bΦ hbΦ
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,hbound⟩:=hbound η₀ (sourceFixedIdeal F)
      (sourceFixedIdeal_le_modulus F) (source_fixed_gates F η₀).1
      (internalQ_ne_top _ (sourceFixedIdeal_ne_top F) η₀) (source_fixed_gates F η₀).2.2.2
    exact ⟨Cz,Cp,hCz,hCp,hbound.mono (fun U h=>⟨h.2.1,h.2.2⟩)⟩
  constructor
  · intro bΦ hbΦ
    obtain ⟨degree,control,h⟩:=hactual bΦ hbΦ
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,h⟩:=h η₀
    exact ⟨Cp,hCp,h.mono (fun U h=> h.2)⟩
  · obtain ⟨degree,control,h⟩:=hactual radialSupportUpper radialSupportUpper_spec.1
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,h⟩:=h η₀
    exact ⟨Cz,hCz,h.mono (fun U h=> h.1)⟩

theorem source_moments {Δ:ℝ}{D:HighData Δ}(F:SourceData D)
    (counts:CountParameters F.modulus ⊤ D.t)(mesh:ℝ)(hmesh:0< mesh)
    (hfine:∀j,D.ell j≤ mesh/200)
    (hpositive:PositiveFineSourceInput F mesh)
    (hzero:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) radialSupportUpper
        0 1 2 (D.t/4) U degree control A):
    ∃J:ℝ,0≤ J ∧ ∀η:Character,∃C:ℝ,0< C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ)):=by
  obtain ⟨Ji,hi⟩:=ProbeDetectorInverseFields.source_batch_inverse_fields F.modulus ⊤ le_top F counts
  obtain ⟨Jm,hm⟩:=source_batch_plain_marked_fine F mesh hmesh hfine hpositive
  obtain ⟨Ju,hu⟩:=ProbeDetectorPlainUnmarkedRestrictedField.source_batch_plain_unmarked D F hzero
  refine ⟨(Ji+Jm+Ju:ℕ),by positivity,?_⟩
  intro η
  obtain ⟨Ci,hCi,hi⟩:=hi η
  obtain ⟨Cm,hCm,hm⟩:=hm η
  obtain ⟨Cu,hCu,hu⟩:=hu η
  refine ⟨Ci+Cm+Cu,by positivity,?_⟩
  intro τ hτ hτ1
  filter_upwards [hi,hm,hu] with Z hi hm hu
  have hZ:0< Z:=zero_lt_one.trans hi.1
  let height:ℝ:=Z^(2*τ)
  have hh:0≤ height:=Real.rpow_nonneg hZ.le _
  have hbase:1≤1+height:=by linarith
  have hCi':Ci*(1+height)^Ji≤(Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCm':Cm*(1+height)^Jm≤(Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCu':Cu*(1+height)^Ju≤(Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  simp only [Real.rpow_natCast]
  intro rows d a hd hdmax ha hamax hrows i z hz hzim q B hB hdata hreverse hslots hwidth
    hprofile hupper hexternal hslotMesh hbinWidth hfamily bin label left right hne
  have hrows':∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u:=fun u hu=>(hrows u hu).2.1
  have hext:∀s,(B.external s).re=17/50:=by intro s;rw [hexternal];exact hz
  have hheight:∀s,|(B.external s).im|≤ height:=by intro s;rw [hexternal];exact hzim
  have hinv:=hi.2 d hd a D.ε _ _ _ i B hdata hprofile hupper hwidth hext
    bin label left right hne height hh
  have hmarked:=hm.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    (fun s=> by rw [hupper]) hext bin label left right hne height hh hheight
  have hunmarked:=hu.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    bin label left right hne height hh
  have hU:0≤ Z^d:=Real.rpow_nonneg hZ.le _
  constructor
  · intro n hn σ hσ t ht
    exact ⟨rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).1 hCi',
      rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).2 hCi'⟩
  · intro selected hselected hfirst hsecond n hn σ hσ t ht
    exact (hinv.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCi' (Real.rpow_nonneg hU _))
  · intro selected hselected hcap j k hjk σ hσ t ht
    exact (hmarked selected hselected hcap j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU _))
  · intro j k hjk σ hσ t ht
    exact (hunmarked j k hjk σ hσ t ht).1.trans
      (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))

theorem fine_moments_of_certified (h:DetectorCertifiedBands):FineMomentInput:=by
  intro hβ
  let Δ:=HeckeZeroSupremum.beta-7/8
  have hΔ:0<Δ:=by dsimp [Δ];linarith
  refine ⟨detectorMesh Δ,fun t ht=> detectorMesh_pos hΔ ht,?_⟩
  intro D hfine F counts
  obtain ⟨hp,hz⟩:=plain_inputs F (h hβ D hfine F)
  exact source_moments F counts (detectorMesh Δ D.t) (detectorMesh_pos hΔ D.t_pos) hfine hp hz

theorem chosen_moments_of_certified (h:DetectorCertifiedBands):ChosenMomentInput:=
  chosen_input_of_fine (fine_moments_of_certified h)

theorem dirichlet_of_certified (h:DetectorCertifiedBands)(q:ℕ)(hq:q≠0)
    (χ:DirichletCharacter ℂ q)(s:ℂ)(hs:(7/8:ℝ)< s.re)(hexc:¬(χ=1 ∧ s=1)):
    letI:NeZero q:=⟨hq⟩
    DirichletCharacter.LFunction χ s≠0:=
  dirichlet_of_chosen_moments (chosen_moments_of_certified h) q hq χ s hs hexc

theorem zeta_of_certified (h:DetectorCertifiedBands)(s:ℂ)(hs:(7/8:ℝ)< s.re):riemannZeta s≠0:=
  zeta_of_chosen_moments (chosen_moments_of_certified h) s hs

end SevenEighths.ProbeFinalAssemblyCertifiedBands

end

end OAI
end
/- END ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCertifiedBands -/

/- BEGIN ORIGINAL MODULE Analytic.JointDictionaryDensity ; sha256 6a40dbfc248a7eb101538b3775d9f1c594fedae381f56f8fcf75cfd9cd7dee2b -/
section





/-! Literal source-to-density bridge. The first and second ray twists belong
to a finite dictionary fixed before arithmetic labels. Fixed-inducing
eligibility is transported through exact coefficients and finite masks. -/

set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeRowClosure HeckeInverseAmplification HeckeDetectorZeros HeckeFiniteDeletion
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredExceptionalProfile CenteredMomentFixedRowMask CenteredMomentFixedRayInducingTransport
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource
open ProbeHighRowFamily LocalMoment RayFourExpansion CenteredMomentFixedRay
local notation "O" => HeckeFamily.O

def jointParentDictionary (η : Character) : Finset Character :=
  rayClosure (fixedParentDictionary η) ∪
    (rayClosure (fixedParentDictionary η)).image CenteredMomentReflectedSource.reflected

abbrev JointParentLabel (η : Character) := {τ : Character // τ ∈ jointParentDictionary η}

theorem jointParentDictionary_fixedQ (η : Character) (Q : Ideal O)
    (hQη : Q ≤ η.modulus) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (τ : JointParentLabel η) : Q ≤ τ.val.modulus := by
  have hbase (ψ : Character) (hψ : ψ ∈ rayClosure (fixedParentDictionary η)) :
      Q ≤ ψ.modulus := rayClosure_fixedQ (fixedParentDictionary η) Q hQ72
    (fun φ hφ => fixedParentDictionary_fixedQ η φ Q hQη hQ72 hφ) ψ hψ
  rcases Finset.mem_union.mp τ.property with hτ | hτ
  · exact hbase τ.val hτ
  · obtain ⟨ψ,hψ,he⟩ := Finset.mem_image.mp hτ
    rw [←he]
    change Q ≤ ψ.modulus ⊓ Ideal.span {(36 : O)}
    exact le_inf (hbase ψ hψ)
      (hQ72.trans (Ideal.span_singleton_le_span_singleton.mpr ⟨2,by norm_num⟩))

theorem jointParentDictionary_base_mem (η τ : Character)
    (hτ : τ ∈ rayClosure (fixedParentDictionary η)) : τ ∈ jointParentDictionary η :=
  Finset.mem_union_left _ hτ

theorem jointParentDictionary_reflected_base_mem (η τ : Character)
    (hτ : τ ∈ rayClosure (fixedParentDictionary η)) :
    CenteredMomentReflectedSource.reflected τ ∈ jointParentDictionary η :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨τ,hτ,rfl⟩)

lemma fixedParentDictionary_inducing_iff (η τ : Character) (hτ : τ ∈ fixedParentDictionary η)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (w : O) (hw : w ≠ 0) :
    FixedInducingRow τ Q fixedBadMask 1 w ↔ FixedInducingRow η Q fixedBadMask 1 w := by
  obtain ⟨⟨φ, ψ⟩, hmem, rfl⟩ := Finset.mem_image.mp hτ
  obtain ⟨hφ, hψ⟩ := Finset.mem_product.mp hmem
  exact (fixedInducingRow_product_iff (η.product φ) ψ Q fixedBadMask 1 w
    (fixedPhaseDictionary_fixedQ Q hQ72 ψ hψ) fixedBadMask_ne_zero one_ne_zero hw
    (dvd_mul_right _ _) (dvd_mul_left _ _)).trans
      (fixedInducingRow_product_iff η φ Q fixedBadMask 1 w
        (fixedPhaseDictionary_fixedQ Q hQ72 φ hφ) fixedBadMask_ne_zero one_ne_zero hw
        (dvd_mul_right _ _) (dvd_mul_left _ _))

lemma rayParent_inducing_iff (η : Character) (ξ : RayCharacter)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (w : O) (hw : w ≠ 0) :
    FixedInducingRow (rayParent η ξ) Q fixedBadMask 1 w ↔
      FixedInducingRow η Q fixedBadMask 1 w := by
  apply fixedInducingRow_product_iff η (primaryRayCharacter ξ) Q fixedBadMask 1 w
  · rw [primaryRayCharacter_modulus]
    exact hQ72.trans (Ideal.span_singleton_le_span_singleton.mpr ⟨6, by norm_num⟩)
  · exact fixedBadMask_ne_zero
  · exact one_ne_zero
  · exact hw
  · exact dvd_mul_right _ _
  · exact dvd_mul_left _ _

theorem jointParentDictionary_inducing_iff (η : Character) (τ : JointParentLabel η)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (w : O) (hw : w ≠ 0) :
    FixedInducingRow τ.val Q fixedBadMask 1 w ↔ FixedInducingRow η Q fixedBadMask 1 w := by
  have hbase (φ : Character) (hφ : φ ∈ rayClosure (fixedParentDictionary η)) :
      FixedInducingRow φ Q fixedBadMask 1 w ↔ FixedInducingRow η Q fixedBadMask 1 w := by
    obtain ⟨⟨ψ,ξ⟩,hmem,he⟩ := Finset.mem_image.mp hφ
    rw [←he]
    exact (rayParent_inducing_iff ψ ξ Q hQ72 w hw).trans
      (fixedParentDictionary_inducing_iff η ψ (Finset.mem_product.mp hmem).1 Q hQ72 w hw)
  rcases Finset.mem_union.mp τ.property with hτ | hτ
  · exact hbase τ.val hτ
  · obtain ⟨ψ,hψ,he⟩ := Finset.mem_image.mp hτ
    rw [←he]
    apply Iff.trans _ (hbase ψ hψ)
    apply fixedInducingRow_product_iff ψ (HeckeUnitRows.character (-1 : Oˣ))
      Q fixedBadMask 1 w
    · change Q ≤ Ideal.span {(36 : O)}
      exact hQ72.trans (Ideal.span_singleton_le_span_singleton.mpr ⟨2,by norm_num⟩)
    · exact fixedBadMask_ne_zero
    · exact one_ne_zero
    · exact hw
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _

theorem reflected_rowWeight (η : Character) (w : O) (t : ℝ) (I : Ideal O) :
    rowWeight η fixedBadMask 1 (-w) t I =
      rowWeight (CenteredMomentReflectedSource.reflected η) fixedBadMask 1 w t I := by
  by_cases hI : Supported I
  · simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,one_mul,
      CenteredMomentReflectedSource.reflected,idealCoeff_product,
      CenteredMomentReflectedSource.unit_ideal I hI]
    rw [show fixedBadMask^6*(-w) = (-1)*(fixedBadMask^6*w) by ring,
      idealRowHom_argument_mul]
    ring
  · have hz (ψ : Character) (z : O) : rowWeight ψ fixedBadMask 1 z t I = 0 :=
      rowWeight_zero_of_not_supported ψ fixedBadMask 1 z t
        (dvd_mul_right goodLambda 2) (dvd_mul_left 2 goodLambda) I hI
    rw [hz,hz]

/-- Reflection permutes the finite dictionary at the level of the literal
masked coefficients. A second reflection uses the original parent. -/
theorem jointParentDictionary_reflect (η : Character) (τ : JointParentLabel η) :
    ∃ ψ : JointParentLabel η, ∀ (w : O) (t : ℝ) (I : Ideal O),
      rowWeight τ.val fixedBadMask 1 (-w) t I = rowWeight ψ.val fixedBadMask 1 w t I := by
  rcases Finset.mem_union.mp τ.property with hτ | hτ
  · exact ⟨⟨CenteredMomentReflectedSource.reflected τ.val,
      jointParentDictionary_reflected_base_mem η τ.val hτ⟩,reflected_rowWeight τ.val⟩
  · obtain ⟨ψ,hψ,he⟩ := Finset.mem_image.mp hτ
    refine ⟨⟨ψ,jointParentDictionary_base_mem η ψ hψ⟩,?_⟩
    intro w t I
    rw [←he,←reflected_rowWeight,neg_neg]

lemma rowWeight_zero_span (η : Character) (m w n : O) :
    rowWeight η m 1 w 0 (Ideal.span {n}) = rowTwist (elementHom η) m 1 w n := by
  simp only [rowWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    Complex.ofReal_zero, mul_zero, Complex.cpow_zero, mul_one, one_mul]
  change idealCoeff η (Ideal.span {n}) * idealRowHom (m^6*w) (Ideal.span {n}) =
    elementCoeff η n * idealRowHom (m^6*1^4*w) (Ideal.span {n})
  rw [one_pow, mul_one]
  by_cases hn : n = 0
  · subst n
    rw [Ideal.span_singleton_zero]
    change idealCoeff η 0 * idealRowHom (m^6*w) 0 =
      elementCoeff η 0 * idealRowHom (m^6*w) 0
    simp only [map_zero, mul_zero]
  · rw [idealCoeff_span η hn]

lemma naturalRow_masked_height {η : Character} {w : O} (N : NaturalRow η w)
    (R : Ideal O) (hR : R ≠ 0) (t : ℝ) (I : Ideal O) :
    heightCoeff (excluded N.character R) t I =
      rowWeight η (fixedBadMask*idealGenerator R) 1 w t I := by
  simp only [heightCoeff, N.masked_ideal R hR I, rowWeight,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, one_mul]

lemma fixedInducing_of_natural_height_identity (source parent : Character)
    (j w : O) (hw : w ≠ 0) (N : NaturalRow parent w)
    (R : Ideal O) (hR : R ≠ 0)
    (heq : ∀ I : Ideal O, rowWeight source fixedBadMask 1 j 0 I =
      heightCoeff (excluded N.character R) 0 I) (Q : Ideal O) :
    FixedInducingRow source Q fixedBadMask 1 j ↔
      FixedInducingRow parent Q fixedBadMask 1 w := by
  have ht (n : O) : rowTwist (elementHom source) fixedBadMask 1 j n =
      rowTwist (elementHom parent) (fixedBadMask*idealGenerator R) 1 w n := by
    simpa only [naturalRow_masked_height N R hR, rowWeight_zero_span] using heq (Ideal.span {n})
  have hi : FixedInducingRow source Q fixedBadMask 1 j ↔
      FixedInducingRow parent Q (fixedBadMask*idealGenerator R) 1 w := by
    constructor
    · rintro ⟨χ, ψ, hp, hi, hQ, hc⟩
      refine ⟨χ, ψ, hp, hi, hQ, ?_⟩
      intro n
      simpa only [one_mul] using (hc n).trans (by simpa only [one_mul] using ht n)
    · rintro ⟨χ, ψ, hp, hi, hQ, hc⟩
      refine ⟨χ, ψ, hp, hi, hQ, ?_⟩
      intro n
      simpa only [one_mul] using (hc n).trans (by simpa only [one_mul] using (ht n).symm)
  exact hi.trans (fixedInducingRow_mul_mask_iff parent Q fixedBadMask (idealGenerator R) 1 w
    fixedBadMask_ne_zero (idealGenerator_ne_zero R hR) one_ne_zero hw
    (dvd_mul_right _ _) (dvd_mul_left _ _))

/-- Both actual source branches, including the second ray coefficient, are
literal finite deletions of natural rows over one fixed parent dictionary.
Their original source eligibility is exactly the base eligibility at the
reconstructed integer, with no enlarged exceptional set. -/
theorem actual_source_second_ray_natural_rows (η : Character) (C D : Ideal O)
    (hC : Supported C) (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair η C D hC E ξ₁ ξ₂) :
    ∃ u : Oˣ, ∃ τL ∈ fixedParentDictionary η, ∃ τR ∈ fixedParentDictionary η,
      activeConductor C D = (u : O) * ∏ i, activePrimary C D i ∧
      ∀ (ξ : RayCharacter) (j : O), j ≠ 0 →
        let wL := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E *
          (u : O) * leftEffectiveFactor C D * j
        let wR := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E *
          (u : O) * rightEffectiveFactor C D * j
        ∃ NL : NaturalRow (rayParent τL ξ) wL, ∃ NR : NaturalRow (rayParent τR ξ) wR,
          (∀ (t : ℝ) (I : Ideal O),
            (rowWeight F.left fixedBadMask 1 j t I * rayCharacter ξ (CompletedGauss.primaryGenerator I) =
              heightCoeff (excluded NL.character (canceledIdeal C D 5)) t I) ∧
            (rowWeight F.right fixedBadMask 1 j t I * rayCharacter ξ (CompletedGauss.primaryGenerator I) =
              heightCoeff (excluded NR.character (canceledIdeal C D 1)) t I)) ∧
          (∀ Q : Ideal O, Q ≤ Ideal.span {(72 : O)} →
            (FixedInducingRow F.left Q fixedBadMask 1 j ↔ FixedInducingRow η Q fixedBadMask 1 wL) ∧
            (FixedInducingRow F.right Q fixedBadMask 1 j ↔ FixedInducingRow η Q fixedBadMask 1 wR)) := by
  obtain ⟨u, τL, hτL, τR, hτR, hu, hrows⟩ := actual_source_second_ray_rows η C D hC E ξ₁ ξ₂ F
  refine ⟨u, τL, hτL, τR, hτR, hu, ?_⟩
  intro ξ j hj
  dsimp only
  have he := primeSubsetGenerator_ne_zero (fun P : CommonIndex C D => P.val) E
  have hL : leftEffectiveFactor C D ≠ 0 := active_product_pow_ne_zero C D hC _
  have hR : rightEffectiveFactor C D ≠ 0 := active_product_pow_ne_zero C D hC _
  let wL := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E *
    (u : O) * leftEffectiveFactor C D * j
  let wR := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E *
    (u : O) * rightEffectiveFactor C D * j
  have hwL : wL ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero he u.ne_zero) hL) hj
  have hwR : wR ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero he u.ne_zero) hR) hj
  let NL := naturalRow (rayParent τL ξ) wL hwL
  let NR := naturalRow (rayParent τR ξ) wR hwR
  have hcoeff (t : ℝ) (I : Ideal O) := hrows ξ j t I
  have hleft (t : ℝ) (I : Ideal O) : rowWeight F.left fixedBadMask 1 j t I *
      rayCharacter ξ (CompletedGauss.primaryGenerator I) =
      heightCoeff (excluded NL.character (canceledIdeal C D 5)) t I :=
    (hcoeff t I).1.trans (naturalRow_canceled_height NL C D hC 5 t I).symm
  have hright (t : ℝ) (I : Ideal O) : rowWeight F.right fixedBadMask 1 j t I *
      rayCharacter ξ (CompletedGauss.primaryGenerator I) =
      heightCoeff (excluded NR.character (canceledIdeal C D 1)) t I :=
    (hcoeff t I).2.trans (naturalRow_canceled_height NR C D hC 1 t I).symm
  refine ⟨NL, NR, fun t I => ⟨hleft t I, hright t I⟩, ?_⟩
  intro Q hQ72
  have hfl := fixedInducing_of_natural_height_identity (rayParent F.left ξ) (rayParent τL ξ)
    j wL hwL NL (canceledIdeal C D 5) (canceledIdeal_ne_zero C D hC 5)
    (fun I => (rayParent_rowWeight F.left ξ j 0 I).trans (hleft 0 I)) Q
  have hfr := fixedInducing_of_natural_height_identity (rayParent F.right ξ) (rayParent τR ξ)
    j wR hwR NR (canceledIdeal C D 1) (canceledIdeal_ne_zero C D hC 1)
    (fun I => (rayParent_rowWeight F.right ξ j 0 I).trans (hright 0 I)) Q
  exact ⟨(rayParent_inducing_iff F.left ξ Q hQ72 j hj).symm.trans
      (hfl.trans ((rayParent_inducing_iff τL ξ Q hQ72 wL hwL).trans
        (fixedParentDictionary_inducing_iff η τL hτL Q hQ72 wL hwL))),
    (rayParent_inducing_iff F.right ξ Q hQ72 j hj).symm.trans
      (hfr.trans ((rayParent_inducing_iff τR ξ Q hQ72 wR hwR).trans
        (fixedParentDictionary_inducing_iff η τR hτR Q hQ72 wR hwR)))⟩

lemma natural_momentData_coeff_nonzero (η : Character) (w : NonzeroElement)
    (N : NaturalRow η w.val) (I : Ideal O) :
    idealCoeff N.character I = idealCoeff ((momentData η).character w) I := by
  rw [N.ideal]
  have hm : fixedBadMask = rowMaskElement := by unfold fixedBadMask rowMaskElement; ring
  rw [hm]
  symm
  simpa only [one_pow, mul_one] using
    idealCoeff_eq_row η ((momentData η).character w) rowMaskElement 1 w.val
      ((momentData η).character_spec w) I

def jointNaturalFamily (η : Character) (w : NonzeroElement) : JointParentLabel η → Character :=
  fun τ => (naturalRow τ.val w.val w.property).character

theorem jointNatural_nonprincipal (η : Character) (Q : Ideal O)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (w : NonzeroElement)
    (hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val) :
    ∀ τ : JointParentLabel η, (jointNaturalFamily η w τ).residue ≠ 1 := by
  intro τ
  have ht : ¬FixedInducingRow τ.val Q fixedBadMask 1 w.val :=
    fun h => hex ((jointParentDictionary_inducing_iff η τ Q hQ72 w.val w.property).mp h)
  apply CenteredMomentNonprincipalGate.actual_row_nonprincipal τ.val
    (jointNaturalFamily η w τ) Q fixedBadMask 1 w.val _ ht
  intro n
  simpa only [one_mul, jointNaturalFamily] using (naturalRow τ.val w.val w.property).element n

lemma jointNatural_momentData_mask (η : Character) (w : NonzeroElement)
    (τ : JointParentLabel η) (I : Ideal O) :
    idealCoeff (jointNaturalFamily η w τ) I =
      if IsCoprime I (jointNaturalFamily η w τ).modulus then
        idealCoeff ((momentData τ.val).character w) I else 0 := by
  calc
    _ = if IsCoprime I (jointNaturalFamily η w τ).modulus then
      idealCoeff (jointNaturalFamily η w τ) I else 0 := idealCoeff_source_mask _ I
    _ = _ := by
      dsimp only [jointNaturalFamily]
      rw [natural_momentData_coeff_nonzero τ.val w (naturalRow τ.val w.val w.property) I]

theorem jointMoment_nonprincipal (η : Character) (Q : Ideal O)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (w : NonzeroElement)
    (hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val) :
    ∀ τ : JointParentLabel η, ((momentData τ.val).character w).residue ≠ 1 := by
  intro τ hp
  exact jointNatural_nonprincipal η Q hQ72 w hex τ
    ((principal_iff_of_mask (jointNaturalFamily η w τ) ((momentData τ.val).character w)
      (jointNatural_momentData_mask η w τ)).mpr hp)

/-- Exact equality for the entire fixed dictionary, including the baseline. -/
theorem jointNatural_zeroMaximum (η : Character) (Q : Ideal O)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (w : NonzeroElement)
    (hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val) (T : ℝ) :
    zeroMaximum (jointNaturalFamily η w) (jointNatural_nonprincipal η Q hQ72 w hex) T =
      zeroMaximum (fun τ : JointParentLabel η => (momentData τ.val).character w)
        (jointMoment_nonprincipal η Q hQ72 w hex) T :=
  zeroMaximum_eq_of_mask _ _ _ _ T (jointNatural_momentData_mask η w)

/-- The source gate and both bin boundaries are retained literally. -/
def jointNaturalZeroBin (η : Character) (Q : Ideal O)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (a b T : ℝ) (w : NonzeroElement) : Prop :=
  ∃ hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val,
    a ≤ zeroMaximum (jointNaturalFamily η w) (jointNatural_nonprincipal η Q hQ72 w hex) T ∧
      zeroMaximum (jointNaturalFamily η w) (jointNatural_nonprincipal η Q hQ72 w hex) T ≤ b

theorem jointNaturalZeroBin_iff (η : Character) (Q : Ideal O)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (a b T : ℝ) (w : NonzeroElement) :
    jointNaturalZeroBin η Q hQ72 a b T w ↔
      (¬FixedInducingRow η Q fixedBadMask 1 w.val) ∧
        rawZeroBin (fun τ : JointParentLabel η => momentData τ.val) a b T w := by
  constructor
  · rintro ⟨hex, hlo, hhi⟩
    rw [jointNatural_zeroMaximum η Q hQ72 w hex T] at hlo hhi
    exact ⟨hex, jointMoment_nonprincipal η Q hQ72 w hex, hlo, hhi⟩
  · rintro ⟨hex, hn, hlo, hhi⟩
    refine ⟨hex, ?_, ?_⟩ <;> rw [jointNatural_zeroMaximum η Q hQ72 w hex T]
    · exact hlo
    · exact hhi

/-- Each dictionary character can retain its own actual canceled-prime
puncture without changing any natural zero maximum or either bin boundary. -/
theorem jointCanceled_zeroMaximum (η : Character) (Q : Ideal O)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (w : NonzeroElement)
    (hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val)
    (R : JointParentLabel η → Ideal O) (T : ℝ) :
    zeroMaximum (fun τ => excluded (jointNaturalFamily η w τ) (R τ))
      (fun τ => excluded_nonprincipal _ _ (jointNatural_nonprincipal η Q hQ72 w hex τ)) T =
    zeroMaximum (fun τ : JointParentLabel η => (momentData τ.val).character w)
      (jointMoment_nonprincipal η Q hQ72 w hex) T :=
  (excluded_zeroMaximum (jointNaturalFamily η w) R
    (jointNatural_nonprincipal η Q hQ72 w hex) T).trans
      (jointNatural_zeroMaximum η Q hQ72 w hex T)

/-- Density for the entire fixed joint dictionary of actual natural rows.
Only the literal fixed-inducing gate and actual zero bins remain as row
conditions; coefficient identities and nonprincipality are discharged. -/
theorem actual_joint_dictionary_density (η : Character) (Q : Ideal O) [NeZero Q]
    (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hQη : Q ≤ η.modulus)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (hβupper : HeckeZeroSupremum.beta ≤ 7/8)
    (loss : ℝ) (hlosspos : 0 < loss) :
    ∃ (A : ℕ) (K : ℝ), 0 < K ∧
      (∀ Y : ℝ, 1 ≤ Y → ∀ p : DensityWindow, ∀ F : Finset FreeRow,
        (∀ u ∈ F, rowNorm u ≤ Y ∧ jointNaturalZeroBin η Q hQ72
          p.lower p.upper p.height ⟨u.val, u.property.1⟩) →
        (F.card : ℝ) ≤ K*(1+|p.height|)^A*Y^(unmarkedDensity (2*p.lower-1)+loss)) ∧
      (∀ p : DensityWindow, ∀ Y : ℝ, 0 < Y →
        ∀ R : Finset ProbePhysical.NonzeroFrequency,
        (∀ u ∈ R, rawFrequencyNorm u ≤ Y ∧ jointNaturalZeroBin η Q hQ72
          p.lower p.upper p.height u) →
        (R.card : ℝ) ≤ K*(1+|p.height|)^A*Y^(unmarkedDensity (2*p.lower-1)+loss)) := by
  obtain ⟨A, K, hK, hfree, hraw⟩ := actual_momentData_density
    (fun τ : JointParentLabel η => τ.val) Q hQtop hQ72
    (jointParentDictionary_fixedQ η Q hQη hQ72) hβ M H hH S
    φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper loss hlosspos
  refine ⟨A, K, hK, ?_, ?_⟩
  · intro Y hY p F hF
    apply hfree Y hY p F
    intro u hu
    exact ⟨(hF u hu).1, ((jointNaturalZeroBin_iff η Q hQ72 _ _ _ _).mp (hF u hu).2).2⟩
  · intro p Y hY R hR
    apply hraw p Y hY R
    intro u hu
    exact ⟨(hR u hu).1, ((jointNaturalZeroBin_iff η Q hQ72 _ _ _ _).mp (hR u hu).2).2⟩

/-- Any natural representative of a member of the fixed dictionary is
nonprincipal from the original base gate at the reconstructed integer. -/
theorem jointNaturalRow_nonprincipal (η : Character) (Q : Ideal O)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (w : NonzeroElement)
    (hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val)
    (τ : JointParentLabel η) (N : NaturalRow τ.val w.val) : N.character.residue ≠ 1 := by
  apply CenteredMomentNonprincipalGate.actual_row_nonprincipal τ.val N.character Q fixedBadMask 1 w.val
  · intro n
    simpa only [one_mul] using N.element n
  · exact fun h => hex ((jointParentDictionary_inducing_iff η τ Q hQ72 w.val w.property).mp h)

/-- The actual canceled natural character has all the same positive-real
zeros as the literal momentData row; the assertion includes s = 1. -/
theorem jointCanceled_positive_zeros (η : Character) (Q : Ideal O)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (w : NonzeroElement)
    (hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val)
    (τ : JointParentLabel η) (N : NaturalRow τ.val w.val) (R : Ideal O)
    {s : ℂ} (hs : 0 < s.re) :
    LFunction (excluded N.character R) s = 0 ↔
      LFunction ((momentData τ.val).character w) s = 0 := by
  have hn := jointNaturalRow_nonprincipal η Q hQ72 w hex τ N
  have hmask (I : Ideal O) : idealCoeff N.character I =
      if IsCoprime I N.character.modulus then idealCoeff ((momentData τ.val).character w) I else 0 := by
    calc
      _ = if IsCoprime I N.character.modulus then idealCoeff N.character I else 0 :=
        idealCoeff_source_mask N.character I
      _ = _ := by rw [natural_momentData_coeff_nonzero τ.val w N I]
  exact (excluded_positive_zeros N.character R hn hs).trans
    (positive_zeros_eq_of_mask N.character ((momentData τ.val).character w) hn hmask hs)

/-- A selected actual source character is counted by the full dictionary
maximum; no density union over growing first/second labels is needed. -/
theorem jointCanceled_zeroMaximum_le (η : Character) (Q : Ideal O)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (w : NonzeroElement)
    (hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val)
    (τ : JointParentLabel η) (N : NaturalRow τ.val w.val) (R : Ideal O) (T : ℝ) :
    zeroMaximum (fun _ : Unit => excluded N.character R)
      (fun _ => excluded_nonprincipal _ _ (jointNaturalRow_nonprincipal η Q hQ72 w hex τ N)) T ≤
      zeroMaximum (fun σ : JointParentLabel η => (momentData σ.val).character w)
        (jointMoment_nonprincipal η Q hQ72 w hex) T := by
  apply zeroMaximum_le_of_zero_inclusion
  intro _
  exact ⟨τ, fun s hs hz => (jointCanceled_positive_zeros η Q hQ72 w hex τ N R hs).mp hz⟩

/-- A high selected source row enters an actual complete bin of the fixed
joint dictionary. The upper boundary follows from the incumbent zero bound. -/
theorem jointCanceled_mem_rawZeroBin (η : Character) (Q : Ideal O)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (w : NonzeroElement)
    (hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val)
    (τ : JointParentLabel η) (N : NaturalRow τ.val w.val) (R : Ideal O) (a T : ℝ)
    (hβupper : HeckeZeroSupremum.beta ≤ 7/8)
    (hhigh : a ≤ zeroMaximum (fun _ : Unit => excluded N.character R)
      (fun _ => excluded_nonprincipal _ _ (jointNaturalRow_nonprincipal η Q hQ72 w hex τ N)) T) :
    rawZeroBin (fun σ : JointParentLabel η => momentData σ.val) a (7/8) T w := by
  refine ⟨jointMoment_nonprincipal η Q hQ72 w hex, ?_, ?_⟩
  · exact hhigh.trans (jointCanceled_zeroMaximum_le η Q hQ72 w hex τ N R T)
  · exact zeroMaximum_le_seven_eighths _ _ T hβupper

#print axioms actual_source_second_ray_natural_rows
#print axioms jointNaturalZeroBin_iff
#print axioms jointCanceled_zeroMaximum
#print axioms jointCanceled_positive_zeros
#print axioms jointCanceled_mem_rawZeroBin
#print axioms actual_joint_dictionary_density
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointDictionaryDensity -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstSwap ; sha256 725d815a51b54348fc7173a66cc22412bc82458b92faab90f4ba12531747a407 -/
section


/-! Right first-source rows are jointly counted by swapping the two first
common ideals. Second common data, residual frequency and the canonical unit
remain unchanged. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentActive CenteredMomentCompleteCommon
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
local notation "O" => ActualEisensteinCubic.O

def commonSwap (C D : Ideal O) : CommonIndex C D ≃ CommonIndex D C where
  toFun P := ⟨P.val,by rw [commonSupport_comm]; exact P.property⟩
  invFun P := ⟨P.val,by rw [commonSupport_comm]; exact P.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem commonSwap_val (C D : Ideal O) (P : CommonIndex C D) :
    (commonSwap C D P).val = P.val := rfl

theorem netExponent_swap (c d : ℕ) (h : netExponent c d ≠ 0) :
    netExponent d c = 6-netExponent c d := by
  unfold netExponent at *
  omega

def activeSwap (C D : Ideal O) : ActiveIndex C D ≃ ActiveIndex D C where
  toFun P := ⟨commonSwap C D P.val,by
    have hp := (Finset.mem_filter.mp P.property).2
    have hn := netExponent_lt_six (leftExponent C D P.val) (rightExponent C D P.val)
    have he := netExponent_swap (leftExponent C D P.val) (rightExponent C D P.val) hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change netExponent (rightExponent C D P.val) (leftExponent C D P.val) ≠ 0
    omega⟩
  invFun P := ⟨(commonSwap C D).symm P.val,by
    have hp := (Finset.mem_filter.mp P.property).2
    have hn := netExponent_lt_six (leftExponent D C P.val) (rightExponent D C P.val)
    have he := netExponent_swap (leftExponent D C P.val) (rightExponent D C P.val) hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change netExponent (rightExponent D C P.val) (leftExponent D C P.val) ≠ 0
    omega⟩
  left_inv _ := by rfl
  right_inv _ := by rfl

@[simp] theorem activeSwap_primary (C D : Ideal O) (P : ActiveIndex C D) :
    activePrimary D C (activeSwap C D P) = activePrimary C D P := rfl

theorem activeSwap_exponent (C D : Ideal O) (P : ActiveIndex C D) :
    activeExponent D C (activeSwap C D P) = 6-activeExponent C D P := by
  exact netExponent_swap (leftExponent C D P.val) (rightExponent C D P.val)
    ((Finset.mem_filter.mp P.property).2)

theorem leftEffectiveFactor_swap (C D : Ideal O) :
    leftEffectiveFactor D C = rightEffectiveFactor C D := by
  unfold leftEffectiveFactor rightEffectiveFactor
  apply (Fintype.prod_equiv (activeSwap C D) _ _ ?_).symm
  intro P
  rw [activeSwap_primary,activeSwap_exponent]
  have hp := activeExponent_lt C D P
  congr 2
  omega

def swappedFirstSubset (C D : Ideal O) (E : Finset (CommonIndex C D)) :
    Finset (CommonIndex D C) := E.map (commonSwap C D).toEmbedding

theorem swappedFirstSubset_generator (C D : Ideal O) (E : Finset (CommonIndex C D)) :
    primeSubsetGenerator (fun P : CommonIndex D C => P.val) (swappedFirstSubset C D E) =
      primeSubsetGenerator (fun P : CommonIndex C D => P.val) E := by
  unfold primeSubsetGenerator swappedFirstSubset
  simp only [Finset.prod_map,Equiv.toEmbedding_apply,commonSwap_val]

@[simp] theorem swappedFirstSubset_twice (C D : Ideal O) (E : Finset (CommonIndex C D)) :
    swappedFirstSubset D C (swappedFirstSubset C D E) = E := by
  unfold swappedFirstSubset
  rw [Finset.map_map]
  have he : (commonSwap C D).toEmbedding.trans (commonSwap D C).toEmbedding =
      Function.Embedding.refl _ := by ext P; rfl
  rw [he,Finset.map_refl]

namespace JointReconstructionLabel

def swapFirst (v : JointReconstructionLabel) : JointReconstructionLabel where
  C₁ := v.D₁
  D₁ := v.C₁
  C₂ := v.C₂
  D₂ := v.D₂
  E := swappedFirstSubset v.C₁ v.D₁ v.E
  U := v.U
  L := v.L
  h := v.h

@[simp] theorem swapFirst_twice (v : JointReconstructionLabel) : v.swapFirst.swapFirst = v := by
  cases v
  simp only [swapFirst,swappedFirstSubset_twice]

theorem swapFirst_injective : Function.Injective swapFirst := by
  intro v w he
  simpa only [swapFirst_twice] using congrArg swapFirst he

def swapFirstEquiv : JointReconstructionLabel ≃ JointReconstructionLabel where
  toFun := swapFirst
  invFun := swapFirst
  left_inv := swapFirst_twice
  right_inv := swapFirst_twice

theorem swapFirst_row (v : JointReconstructionLabel) (u : Oˣ) :
    v.swapFirst.row u =
      primeSubsetGenerator (fun P : CommonIndex v.C₁ v.D₁ => P.val) v.E*(u : O)*
        rightEffectiveFactor v.C₁ v.D₁*
        (commonFrequencyGenerator v.C₂ v.D₂*nonunitFrequencyGenerator v.C₂ v.D₂ v.U*v.h) := by
  simp only [row,swapFirst,jointLeftRow,swappedFirstSubset_generator,leftEffectiveFactor_swap]

theorem swapFirst_missing (v : JointReconstructionLabel) (w : O)
    (hCD : IdealMobiusDivisorSum.primeSupport v.C₁ = IdealMobiusDivisorSum.primeSupport v.D₁) :
    jointMissingRadical v.swapFirst.C₁ w = jointMissingRadical v.C₁ w := by
  simp only [swapFirst,jointMissingRadical,←hCD]

end JointReconstructionLabel

#print axioms leftEffectiveFactor_swap
#print axioms JointReconstructionLabel.swapFirst_injective
#print axioms JointReconstructionLabel.swapFirst_row
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstSwap -/

/- BEGIN ORIGINAL MODULE Analytic.JointMissingNorm ; sha256 d7235ecd3b01b591ca4e563572898f588db2f1416180566fd53318d4ad6d7085 -/
section


/-! The missing-radical width saving follows from the actual principal-support
mask restriction. The theorem is a multiplicative ideal-norm inequality. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CenteredMomentCanonicalFirst
open CenteredMomentActive CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalLedger
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

theorem joint_partition_product_bound {ι : Type*} [DecidableEq ι] (B A E K M : Finset ι)
    (hA : A ⊆ B) (hE : E ⊆ B \ A) (hK : K ⊆ A)
    (hM : M ⊆ ((B \ A) \ E) ∪ K) (f : ι → ℕ)
    (hf : ∀ i ∈ B, 1 ≤ f i) :
    (∏ i ∈ M, f i) * (∏ i ∈ A, f i) * (∏ i ∈ E, f i) ≤
      (∏ i ∈ B, f i) * (∏ i ∈ K, f i) := by
  have hd : Disjoint ((B \ A) \ E) K := by
    apply Finset.disjoint_left.mpr
    intro i hi hk
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hi).1).2 (hK hk)
  have hsub : ((B \ A) \ E) ∪ K ⊆ B :=
    Finset.union_subset (Finset.sdiff_subset.trans Finset.sdiff_subset) (hK.trans hA)
  have hm : (∏ i ∈ M, f i) ≤ (∏ i ∈ (B \ A) \ E, f i) * (∏ i ∈ K, f i) := by
    rw [← Finset.prod_union hd]
    exact Finset.prod_le_prod_of_subset_of_one_le hM (fun i hi _ => hf i (hsub hi))
  calc
    _ ≤ ((∏ i ∈ (B \ A) \ E, f i) * (∏ i ∈ K, f i)) *
        (∏ i ∈ A, f i) * (∏ i ∈ E, f i) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hm)
    _ = ((∏ i ∈ (B \ A) \ E, f i) * (∏ i ∈ E, f i)) *
        (∏ i ∈ A, f i) * (∏ i ∈ K, f i) := by ring
    _ = _ := by rw [Finset.prod_sdiff hE, Finset.prod_sdiff hA]

theorem joint_missing_radical_eq_indices (C D : Ideal O) (w : O) (hw : w ≠ 0)
    (hCD : primeSupport C = primeSupport D) :
    jointMissingRadical C w = ∏ P ∈ jointMissingIndices C D w, P.val := by
  have hwI : Ideal.span {w} ≠ (0 : Ideal O) := by simpa using hw
  have himg : (jointMissingIndices C D w).image Subtype.val =
      primeSupport C \ primeSupport (Ideal.span {w}) := by
    ext P
    constructor
    · intro hP
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
      refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp p.property).1, ?_⟩
      intro hmem
      exact (Finset.mem_filter.mp hp).2
        (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hmem))
    · intro hP
      obtain ⟨hPC, hPw⟩ := Finset.mem_sdiff.mp hP
      have hPD : P ∈ primeSupport D := hCD ▸ hPC
      let p : CommonIndex C D := ⟨P, Finset.mem_inter.mpr ⟨hPC, hPD⟩⟩
      refine Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      exact fun hd => hPw (joint_prime_mem_support hwI (support_prime hPC) hd)
  unfold jointMissingRadical
  rw [← himg, Finset.prod_image]
  exact fun _ _ _ _ h => Subtype.val_injective h

theorem joint_principal_eq_complement (C D : Ideal O) :
    principalSupport Finset.univ (leftExponent C D) (rightExponent C D) =
      Finset.univ \ activeSupport Finset.univ (leftExponent C D) (rightExponent C D) := by
  ext P
  simp only [principalSupport, CenteredMomentActive.activeSupport, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_sdiff, not_not]

theorem joint_canceledIdeal_eq (C D : Ideal O) (hC : Supported C) :
    canceledIdeal C D 5 = ∏ P ∈ jointLeftCanceledIndices C D, P.val := by
  have he : canceledIdeal C D 5 =
      ∏ i : ActiveIndex C D, if activeExponent C D i = 5 then i.val.val else 1 := by
    rw [canceledIdeal, canceledFactor, span_finset_product]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : activeExponent C D i = 5
    · simp only [hi, ite_true, activePrimary_span C D hC]
      rfl
    · simp only [hi, ite_false, Ideal.span_singleton_one, Ideal.one_eq_top]
  rw [he]
  change (∏ i : ActiveIndex C D,
    if netExponent (leftExponent C D i.val) (rightExponent C D i.val) = 5 then i.val.val else 1) = _
  rw [Finset.prod_coe_sort (s := CenteredMomentActive.activeSupport Finset.univ
    (leftExponent C D) (rightExponent C D))
    (f := fun P : CommonIndex C D =>
      if netExponent (leftExponent C D P) (rightExponent C D P) = 5 then P.val else 1)]
  rw [← Finset.prod_filter]
  apply Finset.prod_congr
  · ext P
    simp only [CenteredMomentActive.activeSupport, jointLeftCanceledIndices,
      Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro _ _
    rfl

/-- The exact multiplicative form of N(Rmiss) ≤ Z^(p−R−E+R₀).
The selected E is an actual principal-support mask from the first transform. -/
theorem joint_missing_radical_norm (C₁ D₁ C₂ D₂ : Ideal O) (hC₁ : Supported C₁)
    (hCD₁ : primeSupport C₁ = primeSupport D₁)
    (E : Finset (CommonIndex C₁ D₁))
    (hE : E ∈ (principalSupport Finset.univ (leftExponent C₁ D₁)
      (rightExponent C₁ D₁)).powerset)
    (u : Oˣ) (U : Finset (CommonIndex C₂ D₂)) (h : O)
    (hw : jointLeftRow C₁ D₁ C₂ D₂ E u U h ≠ 0) :
    Ideal.absNorm (jointMissingRadical C₁ (jointLeftRow C₁ D₁ C₂ D₂ E u U h)) *
      Ideal.absNorm (Ideal.span {activeConductor C₁ D₁}) *
      Ideal.absNorm (Ideal.span
        {primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E}) ≤
    Ideal.absNorm (commonRadical C₁ D₁) *
      Ideal.absNorm (∏ P ∈ jointLeftCanceledIndices C₁ D₁, P.val) := by
  have he : E ⊆ Finset.univ \ activeSupport Finset.univ
      (leftExponent C₁ D₁) (rightExponent C₁ D₁) := by
    rw [← joint_principal_eq_complement]
    exact Finset.mem_powerset.mp hE
  have hk : jointLeftCanceledIndices C₁ D₁ ⊆ activeSupport Finset.univ
      (leftExponent C₁ D₁) (rightExponent C₁ D₁) := by
    intro P hP
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hp := (Finset.mem_filter.mp hP).2
    omega
  have hm := joint_missing_indices_subset C₁ D₁ C₂ D₂ hC₁ E u U h
  rw [joint_principal_eq_complement] at hm
  have hb := joint_partition_product_bound Finset.univ
    (activeSupport Finset.univ (leftExponent C₁ D₁) (rightExponent C₁ D₁)) E
    (jointLeftCanceledIndices C₁ D₁)
    (jointMissingIndices C₁ D₁ (jointLeftRow C₁ D₁ C₂ D₂ E u U h))
    (Finset.subset_univ _) he hk hm (fun P => Ideal.absNorm P.val)
    (fun P _ => Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (support_prime (Finset.mem_inter.mp P.property).1).ne_zero))
  have hrad : commonRadical C₁ D₁ = ∏ P : CommonIndex C₁ D₁, P.val :=
    (Finset.prod_coe_sort (s := commonSupport C₁ D₁) (f := id)).symm
  have hactive : Ideal.span {activeConductor C₁ D₁} =
      ∏ P ∈ activeSupport Finset.univ (leftExponent C₁ D₁) (rightExponent C₁ D₁), P.val := by
    rw [activeConductor, span_finitePrimeModulus]
    exact Finset.prod_coe_sort _ _
  rw [joint_missing_radical_eq_indices _ _ _ hw hCD₁, hactive,
    primeSubsetGenerator, span_idealGenerator, hrad]
  simpa only [map_prod] using hb

#print axioms joint_missing_radical_norm
#print axioms joint_canceledIdeal_eq
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointMissingNorm -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.MomentDetectorPlainUnmarkedRestrictedField ; sha256 e83517d588c09275aa5432b5116004210ac73b96ba6dd22b4b9583e7a9f07f5d -/
section



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25ProbeDetectorPlainUnmarkedRestrictedField
open ProbeDetectorPlainUnmarkedRestrictedField Cycle25ProbeFinalAssembly
open HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch Cycle25ProbeHighRowFamily
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorDictionary Cycle25CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorDictionary CenteredMomentDetectorEnergyInitialState
open Cycle25CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainUnmarkedState
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainUnmarkedState
open Cycle25CenteredMomentDetectorPlainMomentParameters CenteredMomentDetectorPlainProfileControl
open CenteredMomentDetectorPlainMomentParameters CenteredMomentDetectorPlainProfileControl
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle25CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open QuadraticInitialBound

open Cycle25ProbeDetectorPlainUnmarkedField
open ProbeDetectorPlainUnmarkedField

theorem weighted_source_batch_plain_unmarked (D:Cycle25.Weighted.MomentData)
    (S:Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (henergy:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,
      ∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
        ZeroAt (internalQ (weighted_sourceFixedIdeal S) η₀) (1/4) (9/4) weighted_radialSupportUpper 0 1 2 (D.t/4) U degree control A):
    ∃Jheight:ℕ,∀η:Character,∃C:ℝ,0< C ∧
    ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u)→
      ∀d:ℝ,(1/200:ℝ) ≤ d→∀(a tstar T heightAllowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a D.ε tstar T heightAllowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=> D.ell s/d)→
      ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
      ∀height:ℝ,0 ≤ height→∀j k:ℕ,j+k ≤ 2→
      ∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let F:=B.fiber bin label left right hne;
      let value:=∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t‖^2;
      value ≤ C*(1+height)^Jheight*(Z^d)^(max 1 (2*F.m)+D.t) ∧
      value ≤ C*(1+height)^Jheight*max (Z^d) (((Z^d)^F.m)^2)*(Z^d)^D.t := by
  obtain ⟨degree,control,henergy⟩:=henergy
  obtain ⟨Jheight,Cp,hCp,hprofiles⟩:=paired_control control
  refine ⟨Jheight,?_⟩
  intro η
  let :Fintype (Sum Bool (RayQuotient.Characters S.modulus ⊤)):=Fintype.ofFinite _
  let η₀:=fun label=> sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
  let Q:=fun label=> internalQ (weighted_sourceFixedIdeal S) (η₀ label)
  choose A hA hzero using (fun label=> henergy (η₀ label))
  let Amax:ℝ:=1+∑label,A label
  have hsum:0 ≤ ∑label,A label:=Finset.sum_nonneg (fun j _=>(hA j).le)
  have hAmax:0< Amax:=by dsimp [Amax];linarith
  have hA_bound (label):A label ≤ Amax:=by
    have hh:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hA j).le) (Finset.mem_univ label)
    dsimp [Amax];linarith
  let C:=Amax*(1+diagonalControl radialMajorant)*Cp
  have hdiag:0 ≤ diagonalControl radialMajorant:=diagonalControl_nonneg _
  have hC:0< C:=mul_pos (mul_pos hAmax (by linarith)) hCp
  have hC_bound (label):A label*diagonalControl radialMajorant*Cp ≤ C:=by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hA_bound label) (by linarith) hdiag hAmax.le) hCp.le
  have hscales:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ) ≤ d→
      ZeroAt (Q label) (1/4) (9/4) weighted_radialSupportUpper 0 1 2 (weighted_stageError D)
        (Z^d) degree control (A label):=by
    apply Filter.eventually_all.mpr
    intro label
    obtain ⟨U₀,hU₀⟩:=eventually_atTop.mp (hzero label)
    filter_upwards [HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) U₀ (by norm_num)]
      with Z hz
    intro d hd
    exact hU₀ (Z^d) (hz d hd)
  refine ⟨C,hC,?_⟩
  filter_upwards [weighted_source_batch_plain_retained S η,weighted_source_label_fixed_allowance D S η,hscales]
    with Z hret hmod hscales
  refine ⟨hret.1,?_⟩
  intro rows hrows d hd a tstar T heightAllowance i B hB hdata hprofile hwidth
    bin label left right hne height hheight j k hjk σ hσ t ht F value
  have hU:1< Z^d:=weighted_source_base_gt_one D Z d hret.1 hd
  have hnorm:‖t‖ ≤ height:=by simpa only [Real.norm_eq_abs] using abs_le.mpr ht
  have hp:(weighted_detectorProfiles F.reverse j k σ t).control control ^2 ≤ Cp*(1+height)^Jheight:=by
    apply (hprofiles F.reverse j k hjk σ hσ t).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hnorm) Jheight) hCp.le
  have hcompare:value ≤ weighted_retainedSourceEnergy (weighted_initialKeep (η₀ label) (Q label))
      F (η₀ label) ∅ j k σ t radialMajorant:=by
    simpa only [Fiber.physicalProduct,Finset.prod_empty,mul_one] using
      hret.2 rows hrows d (by linarith) a D.ε tstar T heightAllowance i B hB hdata hprofile hwidth
        bin label left right hne ∅ j k σ t
  have hb:=weighted_retained_unmarked_bound D F (η₀ label) (Q label) hU (hmod.2 label d hd)
    degree control (A label) (hscales label d hd) j k σ t
  have hpow:(Z^d)^(max 1 (2*F.m)+weighted_delta D+weighted_stageError D) ≤ 
      (Z^d)^(max 1 (2*F.m)+D.t):=
    Real.rpow_le_rpow_of_exponent_le hU.le (weighted_final_exponent_budget D _)
  have hfinal:value ≤ C*(1+height)^Jheight*(Z^d)^(max 1 (2*F.m)+D.t):=by
    apply hcompare.trans (hb.trans ?_)
    calc
      _ ≤ (A label*diagonalControl radialMajorant*(Cp*(1+height)^Jheight))*
          (Z^d)^(max 1 (2*F.m)+D.t):=by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hp (mul_nonneg (hA label).le hdiag)
        · exact hpow
        · exact Real.rpow_nonneg (zero_lt_one.trans hU).le _
        · exact mul_nonneg (mul_nonneg (hA label).le hdiag)
            (mul_nonneg hCp.le (by positivity))
      _=(A label*diagonalControl radialMajorant*Cp)*(1+height)^Jheight*
          (Z^d)^(max 1 (2*F.m)+D.t):=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hC_bound label) (by positivity)) (by positivity)
  refine ⟨hfinal,?_⟩
  simpa only [weighted_unmarked_power_eq _ _ _ hU.le,mul_assoc] using hfinal

end SevenEighths.Cycle25ProbeDetectorPlainUnmarkedRestrictedField

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.MomentDetectorPlainUnmarkedRestrictedField -/
