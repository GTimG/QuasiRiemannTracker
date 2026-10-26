/- Source moments at the cutoff `cutoffA`. Collet's inverse, marked plain and unmarked plain
fields hold at every cutoff and are reused unchanged; the affine marked plain moment is an
explicit input. Adapted from the detector-affine submission of DaysSky (Apache-2.0).
Released under Apache 2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentInput
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDictionary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorBudget
import Candidate.Research.RecursiveAffine.Endpoint.Cycle25.Assembly.Count.Parameters
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCountParameters
import Candidate.Cycle25.Assembly.SourceData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono
import Candidate.Research.RecursiveAffine.Endpoint.Cycle25.Assembly.Count.MomentDetectorInverseFields
import Candidate.Cycle25.Assembly.Count.MomentDetectorPlainMarkedFineField
import Submissions.akashlevy_20261009_weighted_numerator.WeightedQRH.MomentDetectorPlainUnmarkedRestrictedField
import Candidate.Research.RecursiveAffine.Endpoint.Cycle25.Assembly.Count.PlainInput
import Candidate.Cycle25.Assembly.Mesh
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.CountAffine.SourceLevel

noncomputable local instance endpointFixedLedger_Candidate_Cycle63_CountAffine_SourceMoments : Cycle63.AffineLedger := Cycle153.Root.rootLedger


namespace OAI.SevenEighths.Cycle153EndpointProbeFinalAssemblyCertifiedBands
open OAI.SevenEighths.Cycle25ProbeDetectorPlainMarkedFineField
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open CenteredMomentEnergyBands ProbeHighRowFamily
open Cycle153EndpointProbeFinalAssembly ProbeFinalAssembly
open Cycle153EndpointProbeDetectorPlainMarkedFineField
open CenteredMomentNaturalFixedRaySource
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles ProbePhysical

/-- The affine marked plain moment on every fiber of every actual source batch, at any cutoff. -/
def weighted_AffineFineInput {D:WeightedQRH.MomentData}
    (S:OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D) : Prop :=
  ∀η:Character,∃J:ℕ,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
    1<Z ∧ ∀rows:Finset FreeRow,(∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u)→
    ∀d:ℝ,(1/200:ℝ) ≤ d→∀(a tstar T allowance:ℝ)(i:ℕ)
    (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
      (Z^d) a D.ε tstar T allowance i),B.rows⊆rows→
    B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
    B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>D.ell s/d)→
    (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0 ≤ height→(∀s,|(B.external s).im| ≤ height)→
    Cycle153EndpointDetectorRawFiber.AffineMarkedMoment (B.fiber bin label left right hne)
      (C*(1+height)^J) height D.t

/-- The detector affine moment for every source whose slots are below the given mesh. -/
def DetectorAffineInputAt (mesh : ℝ → ℝ) : Prop :=
  ∀{D:WeightedQRH.MomentData}(S:OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D),
    51/100 ≤ HeckeZeroSupremum.beta → HeckeZeroSupremum.beta ≤ 7/8 →
    (∀j,D.ell j ≤ mesh D.t/200) → weighted_AffineFineInput S

/-- `weighted_SourceMomentBound` at the cutoff `cutoffA`, with the affine field. -/
def weighted_SourceMomentBoundA {D : WeightedQRH.MomentData} (F : OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D)
    (κplain : ℝ) (counts : Cycle153EndpointProbeHighRowFamily.CountParameters F.modulus ⊤ D.t) (η : Character)
    (Z τ C height : ℝ) : Prop :=
  ∀rows : Finset FreeRow,∀d a : ℝ, (1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100<a → a ≤ 7/8 →
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-D.t)) →
    ∀i : ℕ,∀z : ℂ,z.re=17/50 → |z.im| ≤ height →
    Cycle153EndpointProbeHighRowFamily.SourceMomentsAtA F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell
      (fun _ y=>(F.w y:ℂ)) Z d a D.ε τ (7/8) 2 D.t D.t i z κplain counts.c counts.k C height D.t

theorem weighted_source_moments_A {D:WeightedQRH.MomentData}(F:OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D)
    (κplain:ℝ)(hk1:κplain≤3/4)(counts:Cycle153EndpointProbeHighRowFamily.CountParameters F.modulus ⊤ D.t)
    (mesh:ℝ)(hmesh:0< mesh)
    (hfine:∀j,D.ell j ≤ mesh/200)
    (hpositive:weighted_PositiveFineSourceInput F κplain mesh)
    (hzero:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal F) η₀) (1/4) (9/4) OAI.SevenEighths.ProbeDetectorPlainUnmarkedField.weighted_radialSupportUpper
        0 1 2 (D.t/4) U degree control A)
    (haffine:weighted_AffineFineInput F):
    ∀η:Character,∃J:ℝ,0 ≤ J ∧ ∃C:ℝ,0<C ∧
      ∀τ:ℝ,0<τ→τ ≤ 1→∀ᶠZ:ℝ in atTop,
        weighted_SourceMomentBoundA F κplain counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ)):=by
  obtain ⟨Ji,hi⟩:=Cycle153EndpointProbeDetectorInverseFields.weighted_source_batch_inverse_fields F.modulus ⊤ le_top F counts
  obtain ⟨Jm,hm⟩:=weighted_source_batch_plain_marked_fine F κplain mesh hmesh hfine hpositive
  obtain ⟨Ju,hu⟩:=OAI.SevenEighths.ProbeDetectorPlainUnmarkedRestrictedField.weighted_source_batch_plain_unmarked D F hzero
  intro η
  obtain ⟨Ja,Ca,hCa,ha⟩:=haffine η
  refine ⟨(Ji+Jm+Ju+Ja:ℕ),by positivity,?_⟩
  obtain ⟨Ci,hCi,hi⟩:=hi η
  obtain ⟨Cm,hCm,hm⟩:=hm η
  obtain ⟨Cu,hCu,hu⟩:=hu η
  refine ⟨Ci+Cm+Cu+Ca,by positivity,?_⟩
  intro τ hτ hτ1
  filter_upwards [hi,hm,hu,ha] with Z hi hm hu ha
  have hZ:0<Z:=zero_lt_one.trans hi.1
  let height:ℝ:=Z^(2*τ)
  have hh:0 ≤ height:=Real.rpow_nonneg hZ.le _
  have hbase:1 ≤ 1+height:=by linarith
  have hCi':Ci*(1+height)^Ji ≤ (Ci+Cm+Cu+Ca)*(1+height)^(Ji+Jm+Ju+Ja):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCm':Cm*(1+height)^Jm ≤ (Ci+Cm+Cu+Ca)*(1+height)^(Ji+Jm+Ju+Ja):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCu':Cu*(1+height)^Ju ≤ (Ci+Cm+Cu+Ca)*(1+height)^(Ji+Jm+Ju+Ja):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCa':Ca*(1+height)^Ja ≤ (Ci+Cm+Cu+Ca)*(1+height)^(Ji+Jm+Ju+Ja):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  simp only [Real.rpow_natCast]
  intro rows d a hd hdmax ha' hamax hrows i z hz hzim q B hB hdata hreverse hslots hwidth
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
  have haff:=ha.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    (fun s=>by rw [hupper]) hext bin label left right hne height hh hheight
  have hU:0 ≤ Z^d:=Real.rpow_nonneg hZ.le _
  constructor
  · apply Cycle25DetectorRawFiber.Moments.of_fields (B.fiber bin label left right hne) hk1
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
  · intro selected hsel h1 h2 h3 h4 h5 j k hjk σ hσ t ht
    exact (haff selected hsel h1 h2 h3 h4 h5 j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCa' (Real.rpow_nonneg hU _))

end
end OAI.SevenEighths.Cycle153EndpointProbeFinalAssemblyCertifiedBands

namespace OAI.SevenEighths.Cycle153EndpointProbeFinalAssembly
open OAI.SevenEighths.Cycle25ProbeFinalAssembly
noncomputable section
open scoped Classical
open Filter HeckeFamily
open Cycle153EndpointProbeDetectorPlainMarkedFineField

theorem weighted_actual_source_moments_A {D : WeightedQRH.MomentData}
    (F : OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D) (κplain : ℝ)
    (hk : 7/10≤κplain) (hk1 : κplain≤3/4)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤κplain)
    (counts : Cycle153EndpointProbeHighRowFamily.CountParameters F.modulus ⊤ D.t)
    (hfine : ∀j,D.ell j≤Cycle25.sourceMesh D.t/200)
    (haffine : Cycle153EndpointProbeFinalAssemblyCertifiedBands.weighted_AffineFineInput F) :
    ∀η:Character,∃J:ℝ,0≤J ∧ ∃C:ℝ,0<C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        Cycle153EndpointProbeFinalAssemblyCertifiedBands.weighted_SourceMomentBoundA F κplain counts η Z τ
          (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
  exact Cycle153EndpointProbeFinalAssemblyCertifiedBands.weighted_source_moments_A F κplain hk1
    counts (Cycle25.sourceMesh D.t) (Cycle25.sourceMesh_pos D.t_pos) hfine
    (terminal_plain_input F κplain hk hk1 hbeta hκbeta)
    (terminal_zero_input F κplain hk hk1 hbeta hκbeta) haffine
end
end OAI.SevenEighths.Cycle153EndpointProbeFinalAssembly
