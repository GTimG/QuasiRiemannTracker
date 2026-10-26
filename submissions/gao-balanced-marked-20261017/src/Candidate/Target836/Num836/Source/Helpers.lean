/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/
import Candidate.Target836.Target836TransportParameters
import Candidate.Target836.Num836.Source.Collect
import Candidate.Target836.Detector836.Transport.HighApproximation
import Candidate.Target836.Detector836.Numerator.SourcePacket
import Candidate.Target836.Target836PublicCount
import Candidate.Cycle25.Assembly.Count.MaskedCount
import Candidate.Cycle25.Numerator.SourceScalar
import Candidate.Cycle25.Numerator.PhysicalFront
import Candidate.Target836.Detector836.Transport.LowNormalizer
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubePhaseBins
import Candidate.Target836.Detector836.Masked

/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                        
                                       
                                                   
                                            
                                    
                                         
                                     
                                      
                                      
                                                          
noncomputable section
set_option maxHeartbeats 2200000
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace Target836.Numerator.Source
open Target836.Arithmetic Target836.EndpointArithmetic Target836.Numerator.Scalar
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Target836DetectorCount Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open HeckePrimeAmplitudeBins ProbeMellinBoundary
instance source_fixed_product_neZero (D : BaselineData) (F : BaselineSourceData D) : NeZero (∏P∈F.S,P) :=
  ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩

 theorem source_prime_bins (D : BaselineData) (F : BaselineSourceData D) (P : FinalAssembly.TransportParameters D)
    (τ : ℝ) (n : ℕ) (hτ : 0 < τ) (hheight : 4*τ < (1/200:ℝ)*D.cost) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,(1/200:ℝ) ≤ d → d ≤ 7/8 →
      ∀(η : Character) (u : FreeRow),Z^(1/100:ℝ) ≤ rowNorm u →
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 → rowNorm u ≤ Z^(d-D.t) →
      ∀(a : ℝ) (i : ℕ),i ≤ n → (51/100:ℝ) ≤ a → a ≤ 1 →
      detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u
        (rayCubeFamily F.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^τ) < a+2*D.e →
      ∀z : ℂ,z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ → ∀j : Fin D.N,
      let Q := HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) z
      let g := amplitude (Z^(D.length j)) (a-1/2) D.t Q
      0 ≤ g ∧ g ≤ a-1/2 ∧ g∈labels (a-1/2) D.t ∧
      ‖Q‖ ≤ (Z^(D.length j))^(g+D.t) ∧
      (0 < g → (Z^d)^(2*(D.length j/d)*g) ≤ ‖Q‖^2) := by
  have hp := actual_phase_bins_on_cube F.modulus ⊤ le_top F.S F.exclusions.prime
    F.exclusions.bad F.maximal F.W 1 2 (by norm_num) (by norm_num)
    (Cycle25.Numerator.source_complex_support_open F) (F.W.smooth ⊤)
    D.t (1/200) (7/8) P.rmin τ P.phaseEpsilon D.e P.phaseKappa D.cost D.t (1/100) D.t n
    D.t_pos.le (by norm_num) (by norm_num) P.rmin_pos hτ P.phaseEpsilon_pos D.e_pos D.e_small
    P.phaseKappa_pos D.cost_pos.le D.t_pos (by norm_num) P.phase_budget (lt_of_lt_of_le P.phase_gap (mul_le_mul_of_nonneg_left P.mesh_small P.rmin_pos.le))
    D.t_pos (by linarith)
  filter_upwards [hp,HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) 2 (by norm_num),
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z hp hscale hT hZ
  intro d hd hd' η u hulo hcal huhi a i hi ha ha' hbin z hz hzim j
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hdpos : 0 < d := by linarith
  have hrlo : P.rmin ≤ D.length j/d := by
    apply (le_div_iff₀ hdpos).mpr
    have hh := (P.slots_lower j)
    nlinarith only [hh,hd',P.rmin_pos]
  have hrhi : D.length j/d ≤ D.t := by
    apply (div_le_iff₀ hdpos).mpr
    have hh := (D.slots_small j)
    nlinarith only [hh,hd,D.t_pos]
  have hH : 0 ≤ ((3*i+1:ℕ):ℝ)*Z^τ := by positivity
  have hhh : ((|((0,z.im),0).1.1| ≤ (3*i+1:ℕ)*Z^τ ∧
      |((0,z.im),0).2| ≤ (3*i+1:ℕ)*Z^τ) ∧
      |((0,z.im),0).1.2| ≤ (3*i+1:ℕ)*Z^τ) := by
    simpa only [abs_zero] using And.intro (And.intro hH hH) hzim
  have hh := hp d hd hd' (hscale d hd) hT η u hulo hcal huhi a i hi ha ha' hbin
    (D.length j/d) ((0,z.im),0) hrlo hrhi hhh
  have he : (Z^d)^(D.length j/d)=Z^(D.length j) := by
    rw [←Real.rpow_mul hZpos.le,mul_div_cancel₀ _ hdpos.ne']
  have hz' : (17/50:ℂ)+z.im*Complex.I=z := by
    apply Complex.ext <;> simp [hz]
  dsimp only at hh ⊢
  rw [he,hz'] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1⟩

theorem source_scalar_on_rows (D : BaselineData) (F : BaselineSourceData D) (eps : ℝ) (heps : 0< eps) :
    ∃Cs : ℝ,0 < Cs ∧ ∀(η : Character) (rows : Finset FreeRow) (Z τ d a : ℝ) (i : ℕ),
      0 < Z → 2 < Z^τ → (51/100:ℝ) ≤ a → a ≤ 7/8 →
      (∀u∈rows,Z^(d-2*D.t) ≤ rowNorm u) →
      (∀u∈rows,rowNorm u ≤ Z^d) →
      (∀u∈rows,detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^τ) < a+2*D.e) →
      ∀q∈Cycle25.Weighted.FullWContour.szRectangle ((3*i+1:ℕ)*Z^τ),∀u∈rows,
        ‖frequencyWeight ((17/50:ℂ)+q.2*Complex.I) ⟨u.val,u.property.1⟩*
          Cycle25.Weighted.Numerator.numeratorFreeRowScalar F.S F.exclusions F.maximal η u
            ((((a+16*D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)‖ ≤
          Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+((3*i+1:ℕ):ℝ)*Z^τ)^(2*eps)*
            (Z^d)^(2*eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*D.t) := by
  obtain ⟨Cs,hCs,hbound⟩ := Cycle25.Numerator.source_frequency_scalar_bound
    D.e eps D.e_pos D.e_small heps F.S F.exclusions F.maximal
  refine ⟨Cs,hCs,?_⟩
  intro η rows Z τ d a i hZ hB ha ha' hfreq hupper hnext q hq u hu
  have hH : ((3*i+1:ℕ):ℝ)*Z^τ ≤ ((3*i+2:ℕ):ℝ)*Z^τ := by
    push_cast
    have hp : 0 ≤ Z^τ := Real.rpow_nonneg hZ.le _
    nlinarith
  exact hbound η u (rayCubeFamily F.modulus ⊤ le_top u)
    (Z^τ) a (((3*i+1:ℕ):ℝ)*Z^τ) i hB ha (by linarith) hH (hnext u hu)
    ((((a+16*D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)
    (by simp) (by norm_num) (by simpa using hq.1)
    Z d D.t (Z^d) hZ rfl (hfreq u hu) (hupper u hu)

theorem eventually_uniform_source_conductor {P : ℝ→Prop} (dmin : ℝ) (hdmin : 0 < dmin)
    (hP : ∀ᶠU : ℝ in atTop,P U) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin ≤ d → P (Z^d) := by
  obtain ⟨U0,hU0⟩ := eventually_atTop.mp hP
  filter_upwards [(tendsto_rpow_atTop hdmin).eventually (eventually_ge_atTop U0),
    eventually_ge_atTop (1:ℝ)] with Z hZmin hZ
  intro d hd
  exact hU0 (Z^d) (hZmin.trans (Real.rpow_le_rpow_of_exponent_le hZ hd))

/-- The actual external rectangle is within the bounded-height source count
range, after a threshold depending only on the finite height index budget. -/
theorem weighted_source_height_le (τ : ℝ) (n : ℕ) (hτ : 0 < τ) :
    ∀ᶠZ : ℝ in atTop,∀i : ℕ,i ≤ n →
      0 ≤ ((3*i+1:ℕ):ℝ)*Z^τ ∧ ((3*i+1:ℕ):ℝ)*Z^τ ≤ Z^(2*τ) := by
  filter_upwards [HeckeDyadic.constant_absorbed_eventually (3*(n:ℝ)+1) τ hτ,
    eventually_gt_atTop (1:ℝ)] with Z hn hZ
  intro i hi
  have hi' : (i:ℝ) ≤ n := by exact_mod_cast hi
  have hZp : 0 < Z := zero_lt_one.trans hZ
  refine ⟨by positivity,?_⟩
  calc
    _ ≤ (3*(n:ℝ)+1)*Z^τ := by push_cast;gcongr
    _ ≤ Z^τ*Z^τ := mul_le_mul_of_nonneg_right hn (by positivity)
    _ = _ := by rw [←Real.rpow_add hZp];congr 1;ring

theorem source_normalizer_bound (D : BaselineData) (F : BaselineSourceData D) :
    ∃C : ℝ,0 < C ∧ ∀ᶠZ : ℝ in atTop,
      Target836HighTransport.actualNormalizer F.modulus ⊤ F.S D.length 1 2 (fun _=>F.w) F.W F.W Z≠0 ∧
      ‖(Target836HighTransport.actualNormalizer F.modulus ⊤ F.S D.length 1 2 (fun _=>F.w) F.W F.W Z)⁻¹‖ ≤ C*Z^(D.t/8) := by
  exact Target836LowNormalizer.actual_ray_normalizer_inverse F.modulus ⊤ le_top F.S F.exclusions
    1 2 (by norm_num) (by norm_num) D.length (fun j=>(D.slots_pos j)) D.slots_sum
    (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _ y=>(F.bounded y).1) (fun _=>F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t/8) (by have := D.t_pos;positivity)

theorem source_pools_nonempty (D : BaselineData) (F : BaselineSourceData D) :
    ∀ᶠZ:ℝ in atTop,∀j:Fin D.N,(sourcePrimePool F Z j).Nonempty := by
  obtain ⟨C,hC,hbound⟩ := source_normalizer_bound D F
  filter_upwards [hbound] with Z hn
  intro j
  by_contra hne
  have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
  have hmass : PrincipalSignalComparison.slotMass (sourcePrimePool F Z)
      (ProbePrincipalResidueActual.residueWeights (fun _=>F.w) (fun j=>Z^(D.length j))) j=0 := by
    simp only [PrincipalSignalComparison.slotMass,hempty,Finset.sum_empty]
  have hprod : (∏i:Fin D.N,PrincipalSignalComparison.slotMass (sourcePrimePool F Z)
      (ProbePrincipalResidueActual.residueWeights (fun _=>F.w) (fun j=>Z^(D.length j))) i)=0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) hmass
  apply hn.1
  unfold Target836HighTransport.actualNormalizer Probe.principalScalar
  exact mul_eq_zero_of_right _ (Complex.ofReal_eq_zero.mpr (mul_eq_zero_of_right _ hprod))

theorem source_masked_count_with_error (D : Data) (F : SourceData)
    (counts : Target836Count.CountParameters F.modulus ⊤ D.t) (τ σ : ℝ) (n : ℕ)
    (hτ : 0 < τ) (hτzero : τ < (1/200:ℝ)/2)
    (hτheight : 4*τ < (1/200:ℝ)*D.cost) (hτ2 : 2*τ ≤ D.t) (herror : 159*D.ε+609*D.t≤ σ) :
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
      SourceMomentBound D F counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
      let Q := canonicalFamily D F Z z
      ∀main : Finset (Fin D.N),
      ∀bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun j=>D.length j/d) Q bin
      let q := weightedMean Finset.univ (fun j=>D.length j/d) (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2*a-1)/2 ∧
        (rows'.card:ℝ) ≤ C*C0*
          (Z^d)^(Detector836.count D.momentKappa (2*a-1) (q/(2*a-1))+σ) := by
  obtain ⟨K,hK,hcount⟩ := canonical_source_count_with_error D F counts τ σ n hτ hτzero hτheight hτ2 herror
  refine ⟨K,hK,?_⟩
  intro η
  filter_upwards [hcount η,eventually_gt_atTop (1:ℝ)] with Z hc hZ
  intro d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only
  intro main bin hne
  have hdpos : 0< d := by linarith
  have hb := hc d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only at hb
  have hcard := (hb bin hne).2.2
  have hm := masked_amplitude_class_count836 rows Finset.univ main
    (Z^d) (2*a-1) D.momentKappa D.t D.t_pos (fun j=>D.length j/d)
    (canonicalFamily D F Z z) bin (by linarith) (by linarith) D.momentKappa_lo D.momentKappa_hi
    (Real.one_le_rpow hZ.le hdpos.le) (fun j _=>(div_pos (D.slots_pos j) hdpos).le)
    (by rw [←Finset.sum_div,D.slots_sum];exact div_pos Target836.Arithmetic.ell_pos hdpos)
    (K*C0) σ (by positivity) hne hcard
  exact hm

end Target836.Numerator.Source


#print axioms Target836.Numerator.Source.source_scalar_on_rows
#print axioms Target836.Numerator.Source.eventually_uniform_source_conductor
#print axioms Target836.Numerator.Source.weighted_source_height_le
#print axioms Target836.Numerator.Source.source_normalizer_bound
#print axioms Target836.Numerator.Source.source_pools_nonempty
#print axioms Target836.Numerator.Source.source_masked_count_with_error
