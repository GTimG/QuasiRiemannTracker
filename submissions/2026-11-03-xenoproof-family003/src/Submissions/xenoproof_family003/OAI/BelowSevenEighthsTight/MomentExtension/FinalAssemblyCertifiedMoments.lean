/- UNVERIFIED physical moment assembly; no zero-free theorem asserted. -/
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.MomentExtension.RetunedSourceMomentInput
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.MomentExtension.DetectorInverseFields
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.MomentExtension.DetectorPlainMarkedFineField
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.MomentExtension.DetectorPlainUnmarkedRestrictedField
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.CapacityExtension.Energy.CertifiedExistence

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
local notation "O"=>HeckeFamily.O

def detectorMesh_retuned (Δ t:ℝ):ℝ:=fineMesh 2 0 1 (_root_.BelowSevenEighthsTight.kappaRat+2*Δ) (t/4)

lemma detectorMesh_pos_retuned {Δ t:ℝ}(hΔ:0<Δ)(ht:0<t):0<detectorMesh_retuned Δ t:=by
  have hκRat : (0:ℝ)<_root_.BelowSevenEighthsTight.kappaRat := by norm_num [_root_.BelowSevenEighthsTight.kappaRat]
  exact (bounds 2 (finalSourceCap 2 0 1 (t/4)) (_root_.BelowSevenEighthsTight.kappaRat+2*Δ) (t/4)
    (by norm_num) (sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) _)
    (by linarith) (by positivity)).2.2.2.2.1

theorem plain_inputs_retuned {Δ total margin recordMesh : ℝ}{D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ total margin recordMesh}(F:_root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D)
    (hcert:∀bΦ:ℝ,0<bΦ→CertifiedBand (α:=Fin D.N) F.modulus ⊤ le_top
      (fun x=>conj (F.W x)) 2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2
      (kappaPlain_retuned D) (stageError_retuned D) (count 2 (stageError_retuned D))):
    PositiveFineSourceInput_retuned F (detectorMesh_retuned Δ D.t) ∧
    (∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal_retuned F) η₀) (1/4) (9/4) radialSupportUpper
        0 1 2 (D.t/4) U degree control A):=by
  have hp:=fixed_parameters_retuned D
  have ht (bΦ:ℝ)(hbΦ:0<bΦ):=
    certified_terminal F.modulus ⊤ le_top (fun x=>conj (F.W x))
      2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2 (kappaPlain_retuned D) (stageError_retuned D)
      (by norm_num) (by norm_num) hp.2.2.2.2.2.le hp.2.2.1 (hcert bΦ hbΦ)
  have hactual (bΦ:ℝ)(hbΦ:0<bΦ):
      ∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,
      ∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal_retuned F) η₀) (1/4) (9/4) bΦ 0 1 2
        (stageError_retuned D) U degree control Czero ∧
      PositiveAt (α:=Fin D.N) F.modulus ⊤ le_top (fun x=>conj (F.W x))
        2 (1/4) (9/4) bΦ 0 1 (detectorMesh_retuned Δ D.t) (33/50) (33/50) 2
        (stageError_retuned D) (kappaPlain_retuned D) U η₀ (sourceFixedIdeal_retuned F) degree control Cpositive:=by
    obtain ⟨degree,control,hbound⟩:=ht bΦ hbΦ
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,hbound⟩:=hbound η₀ (sourceFixedIdeal_retuned F)
      (sourceFixedIdeal_le_modulus_retuned F) (source_fixed_gates_retuned F η₀).1
      (internalQ_ne_top _ (sourceFixedIdeal_ne_top_retuned F) η₀) (source_fixed_gates_retuned F η₀).2.2.2
    exact ⟨Cz,Cp,hCz,hCp,hbound.mono (fun U h=>⟨h.2.1,h.2.2⟩)⟩
  constructor
  · intro bΦ hbΦ
    obtain ⟨degree,control,h⟩:=hactual bΦ hbΦ
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,h⟩:=h η₀
    exact ⟨Cp,hCp,h.mono (fun U h=>h.2)⟩
  · obtain ⟨degree,control,h⟩:=hactual radialSupportUpper radialSupportUpper_spec.1
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,h⟩:=h η₀
    exact ⟨Cz,hCz,h.mono (fun U h=>h.1)⟩

theorem source_moments_retuned {Δ total margin recordMesh : ℝ}{D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ total margin recordMesh}(F:_root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D)
    (counts:_root_.BelowSevenEighthsTight.FiberExtension.RetunedCountParameters F.modulus ⊤ D.t)(mesh:ℝ)(hmesh:0<mesh)
    (hfine:∀j,D.ell j≤mesh/200)
    (hpositive:PositiveFineSourceInput_retuned F mesh)
    (hzero:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal_retuned F) η₀) (1/4) (9/4) radialSupportUpper
        0 1 2 (D.t/4) U degree control A):
    ∃J:ℝ,0≤J ∧ ∀η:Character,∃C:ℝ,0<C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        SourceMomentBound_retuned F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ)):=by
  obtain ⟨Ji,hi⟩:=ProbeDetectorInverseFields.source_batch_inverse_fields_retuned F.modulus ⊤ le_top F counts
  obtain ⟨Jm,hm⟩:=source_batch_plain_marked_fine_retuned F mesh hmesh hfine hpositive
  obtain ⟨Ju,hu⟩:=ProbeDetectorPlainUnmarkedRestrictedField.source_batch_plain_unmarked_retuned D F hzero
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
  have hh:0≤height:=Real.rpow_nonneg hZ.le _
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
  have hrows':∀u∈rows,Z^(1/100:ℝ)≤rowNorm u:=fun u hu=>(hrows u hu).2.1
  have hext:∀s,(B.external s).re=17/50:=by intro s;rw [hexternal];exact hz
  have hheight:∀s,|(B.external s).im|≤height:=by intro s;rw [hexternal];exact hzim
  have hinv:=hi.2 d hd a D.ε _ _ _ i B hdata hprofile hupper hwidth hext
    bin label left right hne height hh
  have hmarked:=hm.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    (fun s=>by rw [hupper]) hext bin label left right hne height hh hheight
  have hunmarked:=hu.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    bin label left right hne height hh
  have hU:0≤Z^d:=Real.rpow_nonneg hZ.le _
  constructor
  · intro n hn σ hσ t ht
    exact ⟨rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).1 hCi',
      rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).2 hCi'⟩
  · intro selected hselected hfirst hsecond n hn σ hσ t ht
    exact (hinv.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCi' (Real.rpow_nonneg hU _))
  · intro selected hselected hcap j k hjk σ hσ t ht
    have he : (3/4:ℝ)+2*((_root_.BelowSevenEighthsTight.kappaRat+2*Δ-3/4)/2)=
        _root_.BelowSevenEighthsTight.kappaRat+2*Δ := by ring
    rw [he] at hcap
    exact (hmarked selected hselected hcap j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU _))
  · intro j k hjk σ hσ t ht
    exact (hunmarked j k hjk σ hσ t ht).1.trans
      (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))


theorem source_moments_from_capacity_retuned {total margin recordMesh : ℝ}
    (hβ : _root_.BelowSevenEighthsTight.sigmaRat<HeckeZeroSupremum.beta)
    (D : _root_.BelowSevenEighthsTight.Parameters.RetunedHighData
      (HeckeZeroSupremum.beta-_root_.BelowSevenEighthsTight.sigmaRat) total margin recordMesh)
    (F : _root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D)
    (counts : _root_.BelowSevenEighthsTight.FiberExtension.RetunedCountParameters F.modulus ⊤ D.t)
    (hfine : ∀j,D.ell j≤detectorMesh_retuned
      (HeckeZeroSupremum.beta-_root_.BelowSevenEighthsTight.sigmaRat) D.t/200) :
    ∃J : ℝ,0≤J ∧ ∀η : Character,∃C : ℝ,0<C ∧
      ∀τ : ℝ,0<τ → τ≤1 → ∀ᶠZ : ℝ in atTop,
        SourceMomentBound_retuned F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
  have hΔ : 0<HeckeZeroSupremum.beta-_root_.BelowSevenEighthsTight.sigmaRat := sub_pos.mpr hβ
  have hp:=fixed_parameters_retuned D
  have hκ : 2*HeckeZeroSupremum.beta-1=kappaPlain_retuned D :=
    (actual_capacity_identity HeckeZeroSupremum.beta D).symm
  have hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta := by
    have hs : (51/100:ℝ)<_root_.BelowSevenEighthsTight.sigmaRat := by
      norm_num [_root_.BelowSevenEighthsTight.sigmaRat]
    linarith
  have hwindow:=CenteredMomentDetectorPlainMarkedState.fixed_window_data_retuned F
  have hcert (bΦ : ℝ) (hbΦ : 0<bΦ) :
      CertifiedBand (α:=Fin D.N) F.modulus ⊤ le_top (fun x=>conj (F.W x))
        2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2 (kappaPlain_retuned D)
        (stageError_retuned D) (count 2 (stageError_retuned D)) := by
    exact CenteredMomentEnergyCertifiedExistence.terminal_certificate_extended
      (α:=Fin D.N) F.modulus ⊤ le_top (fun x=>conj (F.W x))
      1 2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2 (kappaPlain_retuned D) (stageError_retuned D)
      (by norm_num) hwindow.1 hwindow.2.1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hbΦ (by norm_num) (by norm_num) hp.2.2.2.2.1.le hp.2.2.1 hbeta hκ.le
  obtain ⟨hpositive,hzero⟩:=plain_inputs_retuned F hcert
  exact source_moments_retuned F counts _ (detectorMesh_pos_retuned hΔ D.t_pos) hfine hpositive hzero

end SevenEighths.ProbeFinalAssemblyCertifiedBands

end

end OAI

#print axioms OAI.SevenEighths.ProbeFinalAssemblyCertifiedBands.detectorMesh_pos_retuned
#print axioms OAI.SevenEighths.ProbeFinalAssemblyCertifiedBands.plain_inputs_retuned
#print axioms OAI.SevenEighths.ProbeFinalAssemblyCertifiedBands.source_moments_retuned
#print axioms OAI.SevenEighths.ProbeFinalAssemblyCertifiedBands.source_moments_from_capacity_retuned
