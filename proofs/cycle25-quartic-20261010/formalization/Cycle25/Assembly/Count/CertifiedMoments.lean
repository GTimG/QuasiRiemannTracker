import Cycle25.Assembly.Count.MomentInput
import Cycle25.Assembly.Count.MomentDetectorInverseFields
import Cycle25.Assembly.Count.MomentDetectorPlainMarkedFineField
import Cycle25.Assembly.Count.MomentDetectorPlainUnmarkedRestrictedField
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono
namespace OAI.SevenEighths.Cycle25ProbeFinalAssemblyCertifiedBands
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open CenteredMomentEnergyBands ProbeHighRowFamily
open Cycle25ProbeFinalAssembly ProbeFinalAssembly
open Cycle25ProbeDetectorPlainMarkedFineField Cycle25ProbeDetectorPlainUnmarkedField
open CenteredMomentNaturalFixedRaySource Cycle25CenteredMomentNaturalFixedRaySource
theorem weighted_source_moments {D:Cycle25.Weighted.MomentData}(F:WeightedSourceData D)
    (κplain:ℝ)(hk1:κplain≤3/4)(counts:Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t)(mesh:ℝ)(hmesh:0<mesh)
    (hfine:∀j,D.ell j ≤ mesh/200)
    (hpositive:weighted_PositiveFineSourceInput F κplain mesh)
    (hzero:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (weighted_sourceFixedIdeal F) η₀) (1/4) (9/4) weighted_radialSupportUpper
        0 1 2 (D.t/4) U degree control A):
    ∃J:ℝ,0 ≤ J ∧ ∀η:Character,∃C:ℝ,0<C ∧
      ∀τ:ℝ,0<τ→τ ≤ 1→∀ᶠZ:ℝ in atTop,
        weighted_SourceMomentBound F κplain counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ)):=by
  obtain ⟨Ji,hi⟩:=Cycle25ProbeDetectorInverseFields.weighted_source_batch_inverse_fields F.modulus ⊤ le_top F counts
  obtain ⟨Jm,hm⟩:=weighted_source_batch_plain_marked_fine F κplain mesh hmesh hfine hpositive
  obtain ⟨Ju,hu⟩:=Cycle25ProbeDetectorPlainUnmarkedRestrictedField.weighted_source_batch_plain_unmarked D F hzero
  refine ⟨(Ji+Jm+Ju:ℕ),by positivity,?_⟩
  intro η
  obtain ⟨Ci,hCi,hi⟩:=hi η
  obtain ⟨Cm,hCm,hm⟩:=hm η
  obtain ⟨Cu,hCu,hu⟩:=hu η
  refine ⟨Ci+Cm+Cu,by positivity,?_⟩
  intro τ hτ hτ1
  filter_upwards [hi,hm,hu] with Z hi hm hu
  have hZ:0<Z:=zero_lt_one.trans hi.1
  let height:ℝ:=Z^(2*τ)
  have hh:0 ≤ height:=Real.rpow_nonneg hZ.le _
  have hbase:1 ≤ 1+height:=by linarith
  have hCi':Ci*(1+height)^Ji ≤ (Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCm':Cm*(1+height)^Jm ≤ (Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCu':Cu*(1+height)^Ju ≤ (Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  simp only [Real.rpow_natCast]
  intro rows d a hd hdmax ha hamax hrows i z hz hzim q B hB hdata hreverse hslots hwidth
    hprofile hupper hexternal hslotMesh hbinWidth hfamily bin label left right hne
  have hrows':∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u:=fun u hu=>(hrows u hu).2.1
  have hext:∀s,(B.external s).re=17/50:=by intro s;rw [hexternal];exact hz
  have hheight:∀s,|(B.external s).im| ≤ height:=by intro s;rw [hexternal];exact hzim
  have hinv:=hi.2 d hd a D.ε _ _ _ i B hdata hprofile hupper hwidth hext
    bin label left right hne height hh
  have hmarked:=hm.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    (fun s=>by rw [hupper]) hext bin label left right hne height hh hheight
  have hunmarked:=hu.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    bin label left right hne height hh
  have hU:0 ≤ Z^d:=Real.rpow_nonneg hZ.le _
  apply Cycle25DetectorRawFiber.Moments.of_fields (B.fiber bin label left right hne) hk1
  · constructor
    · intro n hn σ hσ t ht
      exact ⟨rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).1 hCi',
        rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).2 hCi'⟩
    · intro selected hselected hfirst hsecond n hn σ hσ t ht
      exact (hinv.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
        (mul_le_mul_of_nonneg_right hCi' (Real.rpow_nonneg hU _))
    · intro j k hjk σ hσ t ht
      exact (hunmarked j k hjk σ hσ t ht).1.trans
        (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))
  · intro selected hselected hcap j k hjk σ hσ t ht
    exact (hmarked selected hselected hcap j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU _))

end
end OAI.SevenEighths.Cycle25ProbeFinalAssemblyCertifiedBands
