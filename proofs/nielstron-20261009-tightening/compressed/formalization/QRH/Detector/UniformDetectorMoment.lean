import QRH.Detector.DynamicSlotMomentInput

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

theorem actual_uniform_source_batch_plain_marked_slots {Δ:ℝ}{D:Parameters.HighData Δ}
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
    ∀j k:ℕ,j+k≤2→∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
        (C*(1+height)^J)*(Z^d)^(1+D.t) := by
  let κ₀ : ℝ := max (13/18) (2*HeckeZeroSupremum.beta-1)
  obtain ⟨J, hbound⟩ := QRHDynamicSlotMomentInput.actual_source_batch_plain_marked_slots
    S nslots lengths hpos κ₀ (le_max_left _ _) (le_max_right _ _) hbeta hfine
  refine ⟨J, ?_⟩
  intro η
  obtain ⟨C, hC, hbound⟩ := hbound η
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1, ?_⟩
  intro κ hklo hkb rows hrows d hd a tstar T allowance i B hB hdata hprof hwidth hupper hreal
    bin label left right hne height hheight hexternal F selected hselected hcap
  have hk : κ₀ ≤ κ := max_le hklo hkb
  have hsum : 0 ≤ ∑ s ∈ selected, F.widths s :=
    Finset.sum_nonneg (fun s hs => (F.widths_pos s (hselected hs)).le)
  have hkc : 6*κ₀*(∑ s ∈ selected, F.widths s) ≤ 6*κ*(∑ s ∈ selected, F.widths s) :=
    mul_le_mul_of_nonneg_right (by linarith) hsum
  exact hz.2 rows hrows d hd a tstar T allowance i B hB hdata hprof hwidth hupper hreal
    bin label left right hne height hheight hexternal selected hselected (by linarith)

end SevenEighths.QRHUniformDetectorMoment
end
end OAI
