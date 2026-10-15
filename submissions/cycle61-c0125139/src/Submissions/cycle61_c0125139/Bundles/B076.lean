/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B024
import Submissions.cycle61_c0125139.Bundles.B031
import Submissions.cycle61_c0125139.Bundles.B043
import Submissions.cycle61_c0125139.Bundles.B045
import Submissions.cycle61_c0125139.Bundles.B047
import Submissions.cycle61_c0125139.Bundles.B058
import Submissions.cycle61_c0125139.Bundles.B067
import Submissions.cycle61_c0125139.Bundles.B071
import Submissions.cycle61_c0125139.Bundles.B074
import Submissions.cycle61_c0125139.Bundles.B075
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubePhaseBins

/- BEGIN ORIGINAL Cycle61.Numerator.Source.Helpers; sha256 c5e1bb037955a95be394d2b5514ba83d59528c801bdcd302a6f10995a46867ed -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                        
                                       
                                                   
                                            
                                    
                                         
                                     
                                      
                                      
                                                          
noncomputable section
set_option maxHeartbeats 2200000
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace Cycle61.Numerator.Source
open Cycle61.Arithmetic Cycle61.Arithmetic.Bernstein Cycle61.Numerator.Scalar
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle61DetectorCount Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
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

theorem source_scalar_on_rows (D : BaselineData) (F : BaselineSourceData D) (eps : ℝ) (heps : 0<eps) :
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
      Cycle61HighTransport.actualNormalizer F.modulus ⊤ F.S D.length 1 2 (fun _=>F.w) F.W F.W Z≠0 ∧
      ‖(Cycle61HighTransport.actualNormalizer F.modulus ⊤ F.S D.length 1 2 (fun _=>F.w) F.W F.W Z)⁻¹‖ ≤ C*Z^(D.t/8) := by
  exact Cycle61LowNormalizer.actual_ray_normalizer_inverse F.modulus ⊤ le_top F.S F.exclusions
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
  unfold Cycle61HighTransport.actualNormalizer Probe.principalScalar
  exact mul_eq_zero_of_right _ (Complex.ofReal_eq_zero.mpr (mul_eq_zero_of_right _ hprod))

theorem source_masked_count_with_error (D : Data) (F : SourceData)
    (counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t) (τ σ : ℝ) (n : ℕ)
    (hτ : 0 < τ) (hτzero : τ < (1/200:ℝ)/2)
    (hτheight : 4*τ < (1/200:ℝ)*D.cost) (hτ2 : 2*τ ≤ D.t) (herror : 159*D.ε+609*D.t≤σ) :
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
          (Z^d)^(Cycle61.Arithmetic.Bernstein.countingR D.momentKappa (2*a-1) (q/(2*a-1))+σ) := by
  obtain ⟨K,hK,hcount⟩ := canonical_source_count_with_error D F counts τ σ n hτ hτzero hτheight hτ2 herror
  refine ⟨K,hK,?_⟩
  intro η
  filter_upwards [hcount η,eventually_gt_atTop (1:ℝ)] with Z hc hZ
  intro d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only
  intro main bin hne
  have hdpos : 0<d := by linarith
  have hb := hc d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only at hb
  have hcard := (hb bin hne).2.2
  rw [←Cycle61.Assembly.Count.rowCount_eq D.momentKappa_lo] at hcard
  have hm := masked_amplitude_class_count rows Finset.univ main
    (Z^d) (2*a-1) D.momentKappa D.t D.t_pos (fun j=>D.length j/d)
    (canonicalFamily D F Z z) bin (by linarith) (by linarith) D.momentKappa_lo D.momentKappa_hi
    (Real.one_le_rpow hZ.le hdpos.le) (fun j _=>(div_pos (D.slots_pos j) hdpos).le)
    (by rw [←Finset.sum_div,D.slots_sum];exact div_pos Cycle61.Assembly.Count.ell_pos hdpos)
    (K*C0) σ (by positivity) hne hcard
  simpa only [Cycle61.Assembly.Count.rowCount_eq D.momentKappa_lo] using hm

end Cycle61.Numerator.Source

end
/- END ORIGINAL Cycle61.Numerator.Source.Helpers -/

/- BEGIN ORIGINAL Cycle61.Numerator.Source.Actual; sha256 5ad68d2f882fd678ec4bb9ad99e0439bfffb5f9417d6a4404906bf33233a665d -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                        
                                       
                                         

noncomputable section
set_option maxHeartbeats 3000000
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace Cycle61.Numerator.Source
open Cycle61.Arithmetic Cycle61.Arithmetic.Bernstein Cycle61.Numerator.Scalar Cycle61.Numerator.Fourth
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle61DetectorCount Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open Cycle61.FinalAssembly

/-- The genuine initial physical affine moment, at an error fixed before height. -/
def ActualAffineInput (A : ChosenData) : Prop :=
  ∃bPhi affineError : ℝ,0<affineError ∧ affineError≤(HeckeZeroSupremum.beta-theta)/10000 ∧
  Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi ∧
  ∃di : ℕ,∃control : Finset (ℕ×ℕ),∃Ci : ℝ,0<Ci ∧
    ∀ᶠU:ℝ in atTop,AffineAt A.F bPhi A.P.mesh affineError U di control Ci

def sourceTarget : ℝ := Assembly.signal HeckeZeroSupremum.beta-4999/5000000000-
  (HeckeZeroSupremum.beta-theta)/2

def RawSourceDyadBound (A : ChosenData) (η : Character) (Z τ : ℝ) (n : ℕ)
    (J C C0 : ℝ) : Prop :=
  ∀(rows : Finset FreeRow) (d a : ℝ) (i : ℕ),d0≤d → d≤dPlus →
  51/100<a → a≤7/8 → i≤n →
  (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
    (calibrationForSet A.F.S A.F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-A.D.t)) →
  (∀u∈rows,(Z^d)^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤Z^d) →
  (∀u∈rows,(rowCharacter A.F.S A.F.exclusions.prime u).residue≠1) →
  (∀u∈rows,Z^(d-2*A.D.t)≤rowNorm u) →
  (∀u∈rows,detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
    (rayCubeFamily A.F.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^τ)<a+2*A.D.e) →
  (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
    (rayCubeFamily A.F.modulus ⊤ le_top u)) ((3*i:ℕ)*Z^τ)) →
  ∀q∈Cycle25.Weighted.FullWContour.szRectangle ((3*i+1:ℕ)*Z^τ),
  ‖Cycle25.Weighted.FullWContour.integratedDyadValue A.F.S A.F.exclusions A.F.maximal η rows
    (sourcePrimePool A.F Z) (fun j=>source_prime_pool_outside A.F Z j)
    (fun _=>A.F.W) (fun j=>Z^(A.D.length j)) A.F.W (Z^y)
    ((((a+16*A.D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)‖≤
  C*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps)*(3+((3*i+1:ℕ):ℝ)*Z^τ)^J*
    Z^(sourceTarget-A.D.t-kernelExponent a A.D.e)

lemma actual_source_loss_budget (A : ChosenData) (affineError : ℝ)
    (haff : affineError≤(HeckeZeroSupremum.beta-theta)/10000) :
    16*A.D.e+2*A.P.eps+3*((HeckeZeroSupremum.beta-theta)/10000)/4+affineError/4+8*A.D.t≤
      (HeckeZeroSupremum.beta-theta)/4 := by
  have hep : A.P.eps≤A.D.t/100 := by
    have hn : (0:ℝ)≤A.D.N := Nat.cast_nonneg _
    have hp := A.P.eps_pos
    nlinarith [A.P.eps_budget]
  have ht : A.D.t≤(HeckeZeroSupremum.beta-theta)/10000 := by
    linarith [A.count_budget,A.D.epsilon_pos,A.D.t_pos]
  linarith [A.P.e_tsmall,A.D.t_pos]

/-- Genuine count and scalar theorems discharge every finite-class premise. -/
theorem actual_raw_source (hgap : theta<HeckeZeroSupremum.beta) (A : ChosenData)
    (hAffine : ActualAffineInput A) :
    ∃J : ℝ,0≤J ∧ ∀τ : ℝ,HeightAdmissible A.D A.P J τ →
    ∀n : ℕ,∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
    ∀C0 : ℝ,1≤C0 →
    SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ (C0*Z^A.D.t) (Z^(2*τ)) →
    RawSourceDyadBound A η Z τ n J C C0 := by
  obtain ⟨bPhi,affineError,haff,haffsmall,hsPhi,di,control,Ci,hCi,hinput⟩ := hAffine
  have hb : (51/100:ℝ)≤HeckeZeroSupremum.beta := by
    have ht : (51/100:ℝ)<theta := by norm_num [theta]
    linarith
  have hbetatop : HeckeZeroSupremum.beta≤7/8 := by
    have hh := A.D.momentKappa_hi
    rw [A.kappa_exact] at hh
    linarith
  let sigma : ℝ := (HeckeZeroSupremum.beta-theta)/10000
  have hsigma : 0 ≤ sigma := by dsimp [sigma];positivity
  obtain ⟨J,hJ,C,hC,hcollect⟩ := source_integrated_all_bands A.D hgap hbetatop A.kappa_exact A.F hb
    bPhi A.P.mesh affineError haff hsPhi di control Ci hCi hinput A.P.slots_mesh
    A.P.eps sigma A.P.eps_pos hsigma (actual_source_loss_budget A affineError haffsmall) A.fine
  obtain ⟨Cs,hCs,hscalar⟩ := source_scalar_on_rows A.D A.F A.P.eps A.P.eps_pos
  refine ⟨J,hJ,?_⟩
  intro τ hheight n η
  rcases hheight with ⟨hτ,hτzero,hτcost,hτ2,hτeps,hτJ⟩
  obtain ⟨K,hK,hcount⟩ := source_masked_count_with_error A.D.toData (baselineSource A.D A.F)
    A.counts τ sigma n hτ hτzero hτcost hτ2 A.count_budget
  refine ⟨C*Cs*K,by have hk := zero_lt_one.trans_le hK;positivity,?_⟩
  filter_upwards [eventually_uniform_source_conductor d0 d0_pos hcollect,hcount η,
    source_prime_bins A.D A.F A.P τ n hτ hτcost,
    source_prime_reconstruction_geometry A.F η,source_pools_nonempty A.D A.F,
    weighted_source_height_le τ n hτ,
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),eventually_gt_atTop (1:ℝ)]
    with Z hcollect hcount hupper hgeo hpools hheight hT hZ
  intro C0 hC0 hmom
  unfold RawSourceDyadBound
  intro rows d a i hd hdmax ha hatop hi hsource hrows hrow hfreq hnext hcurrent q hq
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hd' : d≤7/8 := hdmax.trans (by norm_num [dPlus,h])
  have hz : ((17/50:ℂ)+q.2*Complex.I).re=17/50 := by norm_num
  have hx : ((((a+16*A.D.e):ℝ):ℂ)+q.1*Complex.I).re=a+16*A.D.e := by simp
  have him : |((17/50:ℂ)+q.2*Complex.I).im|≤((3*i+1:ℕ):ℝ)*Z^τ := by simpa using hq.2
  have hcounts := hcount d a C0 hd hd' ha hatop hC0 rows hsource i hi hnext hcurrent
    ((17/50:ℂ)+q.2*Complex.I) hz (him.trans (hheight i hi).2) hmom
  have heq : canonicalFamily A.D.toData (baselineSource A.D A.F) Z ((17/50:ℂ)+q.2*Complex.I)=
      (fun (u:FreeRow) j=>HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ u.val A.F.W 2
        (Z^(A.D.length j)) ((17/50:ℂ)+q.2*Complex.I)) := by
    funext u j
    simp only [canonicalFamily,baselineSource,←A.F.complex_eq]
    rfl
  rw [heq] at hcounts
  let Q (u:FreeRow) (j:Fin A.D.N) := HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ u.val A.F.W 2
    (Z^(A.D.length j)) ((17/50:ℂ)+q.2*Complex.I)
  have hupper' : ∀u∈rows,∀j,‖Q u j‖≤(Z^(A.D.length j))^
      (HeckePrimeAmplitudeBins.amplitude (Z^(A.D.length j)) ((2*a-1)/2) A.D.t (Q u j)+A.D.t) := by
    intro u hu j
    have hh := hupper d hd hd' η u (hsource u hu).2.1 (hsource u hu).2.2.1
      (hsource u hu).2.2.2 a i hi ha.le (by linarith) (hnext u hu)
      ((17/50:ℂ)+q.2*Complex.I) hz him j
    simpa only [show a-1/2=(2*a-1)/2 by ring] using hh.2.2.2.1
  have hscalar' := hscalar η rows Z τ d a i hZ0 hT ha.le hatop hfreq
    (fun u hu=>(hrows u hu).2) hnext q hq
  have hbase : ∀j,sourcePrimePool A.F Z j := fun j=>⟨(hpools j).choose,(hpools j).choose_spec⟩
  have hc := (hcollect d hd).2 Z d hZ hd hdmax rfl η
    ((((a+16*A.D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)
    a (((3*i+1:ℕ):ℝ)*Z^τ) ha.le hatop hx hz (hheight i hi).1 him rows hrows hrow
    hgeo.2.1 hgeo.2.2.1 hgeo.2.2.2.1 hgeo.2.2.2.2.1 hgeo.2.2.2.2.2 hbase Cs K C0 hCs.le hK hC0
    (by
      dsimp only
      intro J bin hne
      apply (hcounts (Finset.univ\J) bin hne).2.2.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hp : 1≤Z^(3*A.D.t) := Real.one_le_rpow hZ.le (by have := A.D.t_pos;positivity)
      nlinarith [mul_nonneg (zero_le_one.trans hK) (zero_le_one.trans hC0)]) hscalar' hupper'
  simpa only [sourceTarget,mul_assoc] using hc
end Cycle61.Numerator.Source

end
/- END ORIGINAL Cycle61.Numerator.Source.Actual -/

/- BEGIN ORIGINAL Cycle61.Numerator.Source.FullW; sha256 90e33734007ce754ab7f57f2f9abf5f42601905d6d34368dfb032d54d6afa29b -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                      
                                   
noncomputable section
set_option maxHeartbeats 2400000
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace Cycle61.Numerator.Source
open Cycle61.Arithmetic Cycle61.Numerator.Scalar
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle61DetectorCount Cycle61.FinalAssembly
theorem source_height_absorption (J t τ : ℝ) (n : ℕ)
    (hJ : 0 ≤ J) (_ht : 0 < t) (hτ : 0 < τ) (hbudget : 2*τ*(1+J) ≤ t) :
    ∀ᶠZ : ℝ in atTop,∀i : ℕ,i ≤ n →
      (3+((3*i+1:ℕ):ℝ)*Z^τ)^J ≤ Z^t := by
  filter_upwards [HeckeDyadic.constant_absorbed_eventually (3*(n:ℝ)+4) τ hτ,
    eventually_ge_atTop (1:ℝ)] with Z hn hZ
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hp : 1 ≤ Z^τ := Real.one_le_rpow hZ hτ.le
  intro i hi
  have hhi : (i:ℝ) ≤ n := by exact_mod_cast hi
  have hheight : 3+((3*i+1:ℕ):ℝ)*Z^τ ≤ Z^(2*τ) := by
    calc
      _ ≤ (3*(n:ℝ)+4)*Z^τ := by push_cast;nlinarith
      _ ≤ Z^τ*Z^τ := mul_le_mul_of_nonneg_right hn (by positivity)
      _ = _ := by rw [←Real.rpow_add hZpos];congr 1;ring
  calc
    _ ≤ (Z^(2*τ))^J := Real.rpow_le_rpow (by positivity) hheight hJ
    _ = Z^(2*τ*J) := (Real.rpow_mul hZpos.le _ _).symm
    _ ≤ Z^t := Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith only [hbudget,hτ])

/-- Absorb the single fixed height degree after every amplitude class has
already been placed below the common numerical target. -/
theorem source_absorb_height (V : ℂ) (Z C H J E t : ℝ)
    (hZ : 0 < Z) (hC : 0 ≤ C) (hheight : (3+H)^J ≤ Z^t)
    (hV : ‖V‖ ≤ C*(3+H)^J*Z^(E-t)) :
    ‖V‖ ≤ C*Z^E := by
  calc
    _ ≤ C*(3+H)^J*Z^(E-t) := hV
    _ ≤ C*Z^t*Z^(E-t) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hheight hC) (Real.rpow_nonneg hZ.le _)
    _ = _ := by rw [mul_assoc,←Real.rpow_add hZ];congr 2;ring

def FullWCellBound (A : ChosenData) (η : Character) (Z τ : ℝ) (n : ℕ)
    (C C0 : ℝ) : Prop :=
  ∀(rows : Finset FreeRow) (d a : ℝ) (i : ℕ),d0≤d → d≤dPlus →
  51/100<a → a≤7/8 → i≤n →
  (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
    (calibrationForSet A.F.S A.F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-A.D.t)) →
  (∀u∈rows,(Z^d)^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤Z^d) →
  (∀u∈rows,(rowCharacter A.F.S A.F.exclusions.prime u).residue≠1) →
  (∀u∈rows,Z^(d-2*A.D.t)≤rowNorm u) →
  (∀u∈rows,detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
    (rayCubeFamily A.F.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^τ)<a+2*A.D.e) →
  (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
    (rayCubeFamily A.F.modulus ⊤ le_top u)) ((3*i:ℕ)*Z^τ)) →
  ‖Cycle25.Weighted.FullWContour.finiteCentralFullWRows A.F.S A.F.exclusions A.F.maximal η rows
    (sourcePrimePool A.F Z) (fun j=>source_prime_pool_outside A.F Z j)
    (fun _ y=>(A.F.w y:ℂ)) (fun j=>Z^(A.D.length j)) A.F.W A.F.W (Z^x) (Z^y) Z A.D.e
    (fun _=>a) (fun _=>(3*i+1:ℕ)*Z^τ)/
      Cycle61HighTransport.actualNormalizer A.F.modulus ⊤ A.F.S A.D.length 1 2 (fun _=>A.F.w) A.F.W A.F.W Z‖≤
    C*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps)*Z^(sourceTarget+A.D.t/8)

/-- The two remaining Mellin integrals and literal source normalization cost
only the displayed normalizer reserve, after the fixed degree is absorbed. -/
theorem actual_fullW_cells (hgap : theta<HeckeZeroSupremum.beta) (A : ChosenData)
    (hAffine : ActualAffineInput A) :
    ∃J : ℝ,0≤J ∧ ∀τ : ℝ,HeightAdmissible A.D A.P J τ →
    ∀n : ℕ,∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
    ∀C0 : ℝ,1≤C0 →
    SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ (C0*Z^A.D.t) (Z^(2*τ)) →
    FullWCellBound A η Z τ n C C0 := by
  obtain ⟨J,hJ,hraw⟩ := actual_raw_source hgap A hAffine
  obtain ⟨Ci,hCi,hi⟩ := Cycle25.Weighted.FullWContour.finiteFullW_uniform_norm_bound A.F.W 1 2
    (by norm_num) A.F.complex_support
  obtain ⟨Cn,hCn,hn⟩ := source_normalizer_bound A.D A.F
  refine ⟨J,hJ,?_⟩
  intro τ hheight n η
  obtain ⟨Cw,hCw,hw⟩ := hraw τ hheight n η
  refine ⟨Ci*Cn*Cw,by positivity,?_⟩
  filter_upwards [hw,hn,source_height_absorption J A.D.t τ n hJ A.D.t_pos hheight.1 hheight.2.2.2.2.2,
    (tendsto_rpow_atTop hheight.1).eventually (eventually_gt_atTop (2:ℝ)),eventually_gt_atTop (1:ℝ)]
    with Z hw hn hheight hT hZ
  intro C0 hC0 hmom
  have hraw := hw C0 hC0 hmom
  unfold FullWCellBound
  intro rows d a i hd hdmax ha hatop hiidx hsource hrows hrow hfreq hnext hcurrent
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  let B : ℝ := Cw*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps)*Z^(sourceTarget-kernelExponent a A.D.e)
  have hB : 0≤B := by dsimp [B];positivity
  have hintegrated : ∀q∈Cycle25.Weighted.FullWContour.szRectangle ((3*i+1:ℕ)*Z^τ),
      ‖Cycle25.Weighted.FullWContour.integratedDyadValue A.F.S A.F.exclusions A.F.maximal η rows
        (sourcePrimePool A.F Z) (fun j=>source_prime_pool_outside A.F Z j)
        (fun _ y=>(A.F.w y:ℂ)) (fun j=>Z^(A.D.length j)) A.F.W (Z^y)
        ((((a+16*A.D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)‖≤B := by
    intro q hq
    have hh := hraw rows d a i hd hdmax ha hatop hiidx hsource hrows hrow hfreq hnext hcurrent q hq
    rw [source_real_profile_eq A.F]
    exact source_absorb_height _ Z (Cw*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps))
      (((3*i+1:ℕ):ℝ)*Z^τ) J (sourceTarget-kernelExponent a A.D.e) A.D.t hZ0
      (by positivity) (hheight i hiidx) (by simpa only [sub_sub,add_comm] using hh)
  have hh := hi A.D.e a (Z^τ) (((3*i+1:ℕ):ℝ)*Z^τ) i A.D.e_pos A.D.e_small ha.le
    (by linarith) hT (by push_cast;have hp:=Real.rpow_nonneg hZ0.le τ;nlinarith)
    A.F.S A.F.exclusions A.F.maximal A.F.first η rows (fun u hu=>(hsource u hu).1)
    (sourcePrimePool A.F Z) (fun j=>source_prime_pool_outside A.F Z j)
    (rayCubeFamily A.F.modulus ⊤ le_top) hnext (fun _ y=>(A.F.w y:ℂ))
    (fun j=>Z^(A.D.length j)) A.F.W 1 2 (by norm_num) A.F.complex_support
    (Z^x) (Z^y) Z B (by positivity) (by positivity) hZ0 hB hintegrated
  rw [div_eq_mul_inv,norm_mul]
  apply (mul_le_mul hh hn.2 (norm_nonneg _) (by positivity)).trans_eq
  dsimp only [B]
  rw [←Real.rpow_mul hZ0.le]
  have hp : Z^(x*(1/2-17/50))*Z^(a+16*A.D.e+17/50-1)*
      Z^(sourceTarget-kernelExponent a A.D.e)*Z^(A.D.t/8)=Z^(sourceTarget+A.D.t/8) := by
    rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0,←Real.rpow_add hZ0]
    congr 1
    unfold kernelExponent
    ring
  calc
    _ = (Ci*Cn*Cw)*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps)*
        (Z^(x*(1/2-17/50))*Z^(a+16*A.D.e+17/50-1)*
          Z^(sourceTarget-kernelExponent a A.D.e)*Z^(A.D.t/8)) := by ring
    _ = _ := by rw [hp]
end Cycle61.Numerator.Source

end
/- END ORIGINAL Cycle61.Numerator.Source.FullW -/

/- BEGIN ORIGINAL Cycle61.Numerator.Finite.SourceCells; sha256 aa361edf366c4cf41aa990e6af80ffa2ab112ffddd2cc34d76f13c10c1d0253e -/
section
                                         
                                     

set_option autoImplicit false
namespace Cycle61.FiniteNumerator
noncomputable section
open scoped Classical BigOperators
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open Cycle61DetectorCount FinalAssembly Cycle61HighTransport Cycle25.Numerator

/-- Source's genuine cell theorem is specialized to the actual buffered partition. -/
theorem actual_cells_of_affine (hgap : Arithmetic.theta<HeckeZeroSupremum.beta)
    (A : ChosenData) (hAffine : Numerator.Source.ActualAffineInput A) :
    ∃J : ℝ,0≤J ∧ ActualFullWCellInput A J := by
  obtain ⟨J,hJ,hcells⟩:=Numerator.Source.actual_fullW_cells hgap A hAffine
  refine ⟨J,hJ,?_⟩
  intro τ hheight n η
  obtain ⟨C,hC,hcells⟩:=hcells τ hheight n η
  refine ⟨C,hC,?_⟩
  filter_upwards [hcells,actual_cell_geometry A η τ n] with Z hc hg
  intro C0 hC0 hmom idx grid hsel k hk i hi j hj hne
  have hf:=hg idx grid hsel k i j hne
  have hrow : ∀u∈cellRows A.D A.F Z idx grid k i j,
      (rowCharacter A.F.S A.F.exclusions.prime u).residue≠1 := by
    intro u hu
    exact calibrated_row_nonprincipal A.F.S A.F.exclusions.prime A.F.maximal A.F.exclusions.bad
      u (hf.source_rows u hu).1 (hf.source_rows u hu).2.2.1
  have hb:=hc C0 hC0 hmom (cellRows A.D A.F Z idx grid k i j)
    (sourceDyadConductor Z A.D.t k) (51/100+A.D.e*j) i hf.d_lower hf.d_upper hf.a_lower hf.a_upper
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hf.source_rows hf.moment_rows hrow
    hf.frequency_lower hf.next_maximum hf.current_maximum
  convert hb using 1 <;> rfl
end
end Cycle61.FiniteNumerator

end
/- END ORIGINAL Cycle61.Numerator.Finite.SourceCells -/
