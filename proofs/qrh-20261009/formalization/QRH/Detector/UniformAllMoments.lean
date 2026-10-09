import QRH.Detector.UniformDetectorMoment
import QRH.Detector.ActualPlainUnmarkedInput
import QRH.Detector.DetectorInverseFields
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono

/-! Actual dynamic-capacity detector row sum, uniform in κ, with an independent
physical slot vector. No unproved analytic estimate is a premise. -/
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter
namespace SevenEighths.QRHUniformDetectorMoment
open HeckeFamily ProbeFinalAssembly CenteredMomentEnergyBands
open CenteredMomentEnergyWidthRanges CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorPlainSlotProfile CenteredMomentNaturalFixedRaySource
open ProbeDetectorPlainMarkedFineField QRHPlainMoment
open CenteredMomentDetectorEnergyInitialState

open QRHDynamicMomentInput
open HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles ProbeHighRowFamily
open CenteredMomentDetectorDictionary

/- The original Moments structure uses the coordinate 3/4+2*gap. Here gap=(κ−3/4)/2 merely expresses the exact proved capacity κ; every field is discharged below. It is unrelated to the positive beta−theta gap in count optimization. -/
theorem actual_uniform_four_moment_fields {Δ:ℝ}{D:Parameters.HighData Δ}
    (S:SourceData D)(nslots:ℕ)(lengths:Fin nslots→ℝ)(hpos:∀s,0<lengths s)(hinj:Function.Injective lengths)
    (cB kB cH kH:ℝ)(hcB:0<cB)(hkB:0<kB)(hcH:0<cH)(hkH:0<kH)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hfine:∀j,lengths j≤dynamicMesh D.t/200):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
    1<Z ∧ ∀κ:ℝ,(13/18:ℝ)≤κ→2*HeckeZeroSupremum.beta-1≤κ→∀rows:Finset FreeRow,(∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→
    ∀d:ℝ,(1/200:ℝ)≤d→∀(a tstar T allowance:ℝ)(i:ℕ)
    (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin nslots)
      (Z^d) a D.ε tstar T allowance i),B.rows⊆rows→
    B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
    B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>lengths s/d)→
    (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤height→(∀s,|(B.external s).im|≤height)→
    let F:=B.fiber bin label left right hne;
    Moments F ((κ-3/4)/2)
      (if 2*a-1≤5/6 then cB else cH)
      (if 2*a-1≤5/6 then kB else kH) (C*(1+height)^J) height D.t := by
  obtain ⟨Ji,hi⟩ := ProbeDetectorInverseFields.source_batch_inverse_fields_slots S.modulus ⊤ le_top
    S nslots lengths hpos hinj cB kB cH kH hcB hkB hcH hkH
  obtain ⟨Jm,hm⟩ := actual_uniform_source_batch_plain_marked_slots S nslots lengths hpos hbeta hfine
  obtain ⟨Ju,hu⟩ := QRHDynamicSlotMomentInput.actual_source_batch_plain_unmarked_slots D S nslots lengths hpos hbeta
  refine ⟨Ji+Jm+Ju,?_⟩
  intro η
  obtain ⟨Ci,hCi,hi⟩ := hi η
  obtain ⟨Cm,hCm,hm⟩ := hm η
  obtain ⟨Cu,hCu,hu⟩ := hu η
  refine ⟨Ci+Cm+Cu,by positivity,?_⟩
  filter_upwards [hi,hm,hu] with Z hi hm hu
  refine ⟨hi.1,?_⟩
  intro κ hklo hkb rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth hupper hreal
    bin label left right hne height hheight hexternal F
  have hbase : 1≤1+height := by linarith
  have hCi' : Ci*(1+height)^Ji≤(Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju) := by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCm' : Cm*(1+height)^Jm≤(Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju) := by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCu' : Cu*(1+height)^Ju≤(Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju) := by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hinv := hi.2 d hd a D.ε tstar T allowance i B hdata hprofile (funext hupper) hwidth hreal
    bin label left right hne height hheight
  have hmarked := hm.2 κ hklo hkb rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth
    hupper hreal bin label left right hne height hheight hexternal
  have hunmarked := hu.2 rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth
    bin label left right hne height hheight
  have hU : 0≤Z^d := Real.rpow_nonneg (lt_trans zero_lt_one hi.1).le _
  constructor
  · intro n hn σ hσ t ht
    exact ⟨rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).1 hCi',
      rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).2 hCi'⟩
  · intro selected hselected hfirst hsecond n hn σ hσ t ht
    exact (hinv.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCi' (Real.rpow_nonneg hU _))
  · intro selected hselected hcap j k hjk σ hσ t ht
    have he : (3/4:ℝ)+2*((κ-3/4)/2)=κ := by ring
    rw [he] at hcap
    exact (hmarked selected hselected hcap j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU _))
  · intro j k hjk σ hσ t ht
    exact (hunmarked j k hjk σ hσ t ht).1.trans
      (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))

end SevenEighths.QRHUniformDetectorMoment
end
end OAI
