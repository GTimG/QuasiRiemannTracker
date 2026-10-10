import WeightedQRH.HighRows.WeightedSourceSelection

/-! The original certified full-amplitude count, expressed in the actual
canonical source polynomials and weakened to the diluted main-slot mean. -/
noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace OAI.SevenEighths.WeightedHighFinalAssembly
open ProbeFinalAssembly ProbeHighRowFamily HeckeFamily ProbePhysical HeckeInverseAmplification
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

theorem weighted_source_masked_amplitude_count {Δ : ℝ}
    (D : WeightedQRH.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData)
    (counts : CountParameters F.modulus ⊤ D.t) (τ : ℝ) (n : ℕ)
    (hτ : 0 < τ) (hτzero : τ < (1/200:ℝ)/2)
    (hτheight : 4*τ < (1/200:ℝ)*D.cost) (hτ2 : 2*τ ≤ D.t) :
    ∃C : ℝ,1 ≤ C ∧ ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d a C0 : ℝ,(1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100 < a → a ≤ 7/8 → 1 ≤ C0 →
      ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-D.t)) →
      ∀i : ℕ,i ≤ n →
      (∀u∈rows,detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^τ) < a+2*D.e) →
      (∀u∈rows,a ≤ detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        ((3*i:ℕ)*Z^τ)) →
      ∀z : ℂ,z.re=17/50 → |z.im| ≤ Z^(2*τ) →
      weighted_SourceMomentBound F counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
      let Q := fun (u : FreeRow) j=>
        HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z
      ∀main : Finset (Fin D.N),
      ∀bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun j=>D.ell j/d) Q bin
      let q := weightedMean Finset.univ (fun j=>D.ell j/d)
        (WeightedQRH.maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2*a-1)/2 ∧
        (rows'.card:ℝ) ≤ C*C0*Z^(3*D.t)*
          (Z^d)^(WeightedQRH.rowCount (2*a-1) (q/(2*a-1))+(159*D.ε+9*D.t)) := by
  obtain ⟨C,hC,hcount⟩ := weighted_source_amplitude_count D F counts τ n hτ hτzero hτheight hτ2
  refine ⟨C,hC,?_⟩
  intro η
  filter_upwards [hcount η,eventually_gt_atTop (1:ℝ)] with Z hc hZ
  intro d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only
  intro main bin hne
  have hdpos : 0 < d := by linarith
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  let Q := fun (u : FreeRow) j=>
    HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z
  have heq : physical F.modulus ⊤ (fun u : FreeRow=>u.val) (fun _ y=>(F.w y:ℂ))
      (fun _=>2) (fun j=>D.ell j/d) (fun _=>z) (Z^d)=Q := by
    funext u j
    exact WeightedQRH.source_count_physical_eq D F Z d hZpos hdpos.ne' z u j
  have hb := hc d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only at hb
  rw [heq] at hb
  have hcard := (hb bin hne).2.2
  exact WeightedQRH.masked_amplitude_class_count rows Finset.univ main (Z^d) (2*a-1)
    D.t D.t_pos (fun j=>D.ell j/d) Q bin (by linarith) (by linarith)
    (Real.one_le_rpow hZ.le hdpos.le)
    (fun j _=>(div_pos (D.slots_bounds j).1 hdpos).le)
    (by rw [←Finset.sum_div,D.slots_sum];positivity)
    (C*C0*Z^(3*D.t)) (159*D.ε+9*D.t)
    (by have := zero_le_one.trans hC;have := zero_le_one.trans hC0;positivity) hne hcard

end OAI.SevenEighths.WeightedHighFinalAssembly
end
