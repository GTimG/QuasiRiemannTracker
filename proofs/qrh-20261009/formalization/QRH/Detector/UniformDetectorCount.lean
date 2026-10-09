import QRH.Detector.UniformDetectorMoment
import OAI.NumberTheory.DirichletL.Hecke.DetectorRowCount

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

theorem actual_uniform_plain_detector_count {Δ:ℝ}{D:Parameters.HighData Δ}
    (S:SourceData D)(nslots:ℕ)(lengths:Fin nslots→ℝ)(hpos:∀s,0<lengths s)
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
    ∀selected:Finset (Fin nslots),selected⊆F.slots→
      2*F.m+6*κ*(∑s∈selected,F.widths s)≤1→
    ∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,∀q z εw εp:ℝ,
      (∀u∈F.rows,(Z^d)^(F.m-εw)≤‖polynomial (F.family u F.label) false
        positiveAnnular ((Z^d)^F.m) σ t‖^2)→
      (∀u∈F.rows,(Z^d)^(2*q*z-εp)≤‖F.physicalProduct selected u‖^2)→
      (F.rows.card:ℝ)≤(C*(1+height)^J)*
        (Z^d)^(1-2*F.m-2*q*z+2*εw+εp+D.t) := by
  obtain ⟨J,hbound⟩ := actual_uniform_source_batch_plain_marked_slots S nslots lengths hpos hbeta hfine
  refine ⟨J,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩ := hbound η
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro κ hklo hkb rows hrows d hd a tstar T allowance i B hB hdata hprof hwidth hupper hreal
    bin label left right hne height hheight hexternal F selected hselected hcap σ hσ t ht q z εw εp hspike hproduct
  have henergy := hz.2 κ hklo hkb rows hrows d hd a tstar T allowance i B hB hdata hprof hwidth hupper hreal
    bin label left right hne height hheight hexternal selected hselected hcap 0 0 (by norm_num) σ hσ t ht
  simp only [Function.iterate_zero, id_eq] at henergy
  have hzpos : 0<Z^d := Real.rpow_pos_of_pos (lt_trans zero_lt_one hz.1) _
  have hcount := HeckeDetectorRowCount.plain_count F.rows (fun u=>F.family u F.label) positiveAnnular
    ((Z^d)^F.m) (fun _=>σ) (fun _=>t) (F.physicalProduct selected)
    (Z^d) 1 F.m q z εw εp D.t (C*(1+height)^J) hzpos
    (by simpa only [one_mul] using hspike) hproduct henergy
  simpa only [mul_one] using hcount

end SevenEighths.QRHUniformDetectorMoment
end
end OAI
