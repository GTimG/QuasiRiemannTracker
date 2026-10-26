import Candidate.Uneven.EndpointHelpers
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeNormalizer
import Candidate.Uneven.EndpointCombined
import Candidate.Uneven.EndpointChosen
import Candidate.Uneven.EndpointMaskedSourceCount
import Candidate.Uneven.EndpointNormalizer
import Candidate.Cycle25.Numerator.FullWBound
import Candidate.Uneven.EndpointFiniteSummation
import Candidate.Uneven.EndpointFiniteTransfer

/- Original module: Candidate.Uneven.EndpointSourcePools. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace OAI.SevenEighths.UnevenEndpoint.Physical.Source
variable [config : Configuration]
open OAI.SevenEighths HeckeFamily ProbePhysical ProbeHighRowFamily Cycle25ProbeFinalAssembly
open PrincipalSignalComparison ProbePrincipalResidueActual ProbeRaySlots PrincipalMellinResidues
open Cycle25.Numerator Cycle25.Weighted.Numerator

theorem source_pools_nonempty (D : BaselineData) (F : BaselineSourceData D) :
    ∀ᶠZ : ℝ in atTop,∀j : Fin D.N,(sourcePrimePool F Z j).Nonempty := by
  have hpos : ∀j : Fin D.N,tsupport F.w⊆Set.Ioi 0 := by
    intro j
    exact F.positive_support
  have hh := power_ray_mass_and_normalizer F.modulus ⊤ le_top F.S (fun _ : Fin D.N=> F.w)
    1 2 (by norm_num) (by norm_num) (fun _=> F.support) (fun _=> F.smooth)
    (fun _=> F.compact) hpos (fun _ x=>(F.bounded x).1) (fun _=> F.nonzero)
    D.length D.slots_pos (D.t/8) (by have:=D.t_pos; positivity)
  filter_upwards [hh] with Z hm
  intro j
  by_contra he
  have he0 := Finset.not_nonempty_iff_eq_empty.mp he
  have hzero : slotMass (sourcePrimePool F Z)
      (residueWeights (fun _=> F.w) (fun i=> Z^(D.length i))) j=0 := by
    simp only [slotMass,he0,Finset.sum_empty]
  have hp := hm.1 j
  change 0 < slotMass (sourcePrimePool F Z) (residueWeights (fun _=> F.w) (fun i=> Z^(D.length i))) j at hp
  rw [hzero] at hp
  exact lt_irrefl _ hp
end OAI.SevenEighths.UnevenEndpoint.Physical.Source
end

/- Original module: Candidate.Uneven.EndpointSourceActual. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
noncomputable section
set_option maxHeartbeats 3000000
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace OAI.SevenEighths.UnevenEndpoint.Physical.Source
variable [config : Configuration]
open OAI.SevenEighths.UnevenEndpoint OAI.SevenEighths.UnevenEndpoint.Count OAI.SevenEighths.UnevenEndpoint.Physical.Scalar OAI.SevenEighths.UnevenEndpoint.Physical
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open OAI.SevenEighths.UnevenEndpoint.Physical Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open OAI.SevenEighths.UnevenEndpoint.Physical.FinalAssembly

/-- The genuine initial physical affine moment, at an error fixed before height. -/
def ActualAffineInput (A : ChosenData) : Prop :=
  ∃bPhi affineError : ℝ,0< affineError ∧ affineError≤(HeckeZeroSupremum.beta-theta)/10000 ∧
  Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi ∧
  ∃di : ℕ,∃control : Finset (ℕ×ℕ),∃Ci : ℝ,0< Ci ∧
    ∀ᶠU:ℝ in atTop,AffineAt SourcePlane.A A.F bPhi A.sourceMesh affineError U di control Ci

def sourceTarget : ℝ := Assembly.signal HeckeZeroSupremum.beta-sourceReserve-
  (HeckeZeroSupremum.beta-theta)/2

def RawSourceDyadBound (A : ChosenData) (η : Character) (Z τ : ℝ) (n : ℕ)
    (J C C0 : ℝ) : Prop :=
  ∀(rows : Finset FreeRow) (d a : ℝ) (i : ℕ),d0≤ d → d≤ dPlus →
  51/100< a → a≤7/8 → i≤ n →
  (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
    (calibrationForSet A.F.S A.F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-A.D.t)) →
  (∀u∈rows,(Z^d)^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ Z^d) →
  (∀u∈rows,(rowCharacter A.F.S A.F.exclusions.prime u).residue≠1) →
  (∀u∈rows,Z^(d-2*A.D.t)≤ rowNorm u) →
  (∀u∈rows,detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
    (rayCubeFamily A.F.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^τ)< a+2*A.D.e) →
  (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
    (rayCubeFamily A.F.modulus ⊤ le_top u)) ((3*i:ℕ)*Z^τ)) →
  ∀q∈Cycle25.Weighted.FullWContour.szRectangle ((3*i+1:ℕ)*Z^τ),
  ‖Cycle25.Weighted.FullWContour.integratedDyadValue A.F.S A.F.exclusions A.F.maximal η rows
    (sourcePrimePool A.F Z) (fun j=> source_prime_pool_outside A.F Z j)
    (fun _=> A.F.W) (fun j=> Z^(A.D.length j)) A.F.W (Z^y)
    ((((a+16*A.D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)‖≤
  C*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps)*(3+((3*i+1:ℕ):ℝ)*Z^τ)^J*
    Z^(sourceTarget-A.D.t-kernelExponent a A.D.e)

lemma actual_source_loss_budget (A : ChosenData) (affineError : ℝ)
    (haff : affineError≤(HeckeZeroSupremum.beta-theta)/10000) :
    16*A.D.e+2*A.P.eps+3*((HeckeZeroSupremum.beta-theta)/10000)/4+affineError/4+8*A.D.t≤
      (HeckeZeroSupremum.beta-theta)/4 := by
  have hep : A.P.eps≤ A.D.t/100 := by
    have hn : (0:ℝ)≤ A.D.N := Nat.cast_nonneg _
    have hp := A.P.eps_pos
    nlinarith [A.P.eps_budget]
  have ht : A.D.t≤(HeckeZeroSupremum.beta-theta)/10000 := by
    linarith [A.count_budget,A.D.epsilon_pos,A.D.t_pos]
  linarith [A.P.e_tsmall,A.D.t_pos]

/-- Genuine count and scalar theorems discharge every finite-class premise. -/
theorem actual_raw_source (hgap : theta< HeckeZeroSupremum.beta) (A : ChosenData)
    (hAffine : ActualAffineInput A) :
    ∃J : ℝ,0≤ J ∧ ∀τ : ℝ,HeightAdmissible A.D A.P J τ →
    ∀n : ℕ,∀η : Character,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,
    ∀C0 : ℝ,1≤ C0 →
    SourceMomentBound A.D (baselineSource A.D A.F) A.counts η Z τ (C0*Z^A.D.t) (Z^(2*τ)) →
    RawSourceDyadBound A η Z τ n J C C0 := by
  obtain ⟨bPhi,affineError,haff,haffsmall,hsPhi,di,control,Ci,hCi,hinput⟩ := hAffine
  have hb : (51/100:ℝ)≤ HeckeZeroSupremum.beta := by
    have ht : (51/100:ℝ)< theta := by have hh := parameter_gates.1; linarith only [hh]
    linarith
  have hbetatop : HeckeZeroSupremum.beta ≤ incumbent := A.beta_incumbent
  let sigma : ℝ := (HeckeZeroSupremum.beta-theta)/10000
  have hsigma : 0 ≤ sigma := by dsimp [sigma];positivity
  obtain ⟨J,hJ,C,hC,hcollect⟩ := source_integrated_all_bands A.D hgap hbetatop A.kappa_exact A.F hb
    bPhi A.sourceMesh affineError haff hsPhi di control Ci hCi hinput A.source_fine
    A.P.eps sigma A.P.eps_pos hsigma (actual_source_loss_budget A affineError haffsmall) A.fine
  obtain ⟨Cs,hCs,hscalar⟩ := source_scalar_on_rows A.D A.F A.P.eps A.P.eps_pos
  refine ⟨J,hJ,?_⟩
  intro τ hheight n η
  rcases hheight with ⟨hτ,hτzero,hτcost,hτ2,hτeps,hτJ⟩
  obtain ⟨K,hK,hcount⟩ := source_masked_count_with_error A.D (baselineSource A.D A.F) A.kappa_incumbent
    A.counts τ sigma n hτ hτzero hτcost hτ2 A.count_budget
  refine ⟨C*Cs*K,by have hk := zero_lt_one.trans_le hK;positivity,?_⟩
  filter_upwards [eventually_uniform_source_conductor d0 (by norm_num [d0]) hcollect,hcount η,
    source_prime_bins A.D A.F A.P τ n hτ hτcost,
    source_prime_reconstruction_geometry A.F η,source_pools_nonempty A.D A.F,
    weighted_source_height_le τ n hτ,
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),eventually_gt_atTop (1:ℝ)]
    with Z hcollect hcount hupper hgeo hpools hheight hT hZ
  intro C0 hC0 hmom
  unfold RawSourceDyadBound
  intro rows d a i hd hdmax ha hatop hi hsource hrows hrow hfreq hnext hcurrent q hq
  have hZ0 : 0< Z := zero_lt_one.trans hZ
  have hd' : d≤7/8 := hdmax.trans (by
    cases config with
    | mk stage => cases stage <;> norm_num [dPlus,h,upperPadding,
        Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.h])
  have hz : ((17/50:ℂ)+q.2*Complex.I).re=17/50 := by norm_num
  have hx : ((((a+16*A.D.e):ℝ):ℂ)+q.1*Complex.I).re=a+16*A.D.e := by simp
  have him : |((17/50:ℂ)+q.2*Complex.I).im|≤((3*i+1:ℕ):ℝ)*Z^τ := by simpa using hq.2
  have hcounts := hcount d a C0 hd hd' ha hatop hC0 rows hsource i hi hnext hcurrent
    ((17/50:ℂ)+q.2*Complex.I) hz (him.trans (hheight i hi).2) hmom
  have heq : canonicalFamily A.D (baselineSource A.D A.F) Z ((17/50:ℂ)+q.2*Complex.I)=
      (fun (u:FreeRow) j=> HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ u.val A.F.W 2
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
      have hp : 1≤ Z^(3*A.D.t) := Real.one_le_rpow hZ.le (by have := A.D.t_pos;positivity)
      nlinarith [mul_nonneg (zero_le_one.trans hK) (zero_le_one.trans hC0)]) hscalar' hupper'
  simpa only [sourceTarget,mul_assoc] using hc
end OAI.SevenEighths.UnevenEndpoint.Physical.Source
end

/- Original module: Candidate.Uneven.EndpointNormalizerHelpers. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace OAI.SevenEighths.UnevenEndpoint.Physical.Source
variable [config : _root_.OAI.SevenEighths.UnevenEndpoint.Configuration]
open OAI.SevenEighths.UnevenEndpoint.Physical
open OAI.SevenEighths Cycle25ProbeFinalAssembly HeckeFamily ProbeHighRowFamily ProbePhysical
open PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
theorem source_normalizer_bound (D : BaselineData) (F : BaselineSourceData D) :
    ∃C : ℝ,0 < C ∧ ∀ᶠZ : ℝ in atTop,
      UnevenEndpointPhysicalHighTransport.actualNormalizer F.modulus ⊤ F.S D.length 1 2 (fun _=> F.w) F.W F.W Z≠0 ∧
      ‖(UnevenEndpointPhysicalHighTransport.actualNormalizer F.modulus ⊤ F.S D.length 1 2 (fun _=> F.w) F.W F.W Z)⁻¹‖ ≤ C*Z^(D.t/8) := by
  exact UnevenEndpointPhysicalLowNormalizer.actual_ray_normalizer_inverse F.modulus ⊤ le_top F.S F.exclusions
    1 2 (by norm_num) (by norm_num) D.length (fun j=>(D.slots_pos j)) D.slots_sum
    (fun _=> F.w) (fun _=> F.smooth) (fun _=> F.compact) (fun _=> F.support)
    (fun _ y=>(F.bounded y).1) (fun _=> F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t/8) (by have := D.t_pos;positivity)


end OAI.SevenEighths.UnevenEndpoint.Physical.Source
end

/- Original module: Candidate.Uneven.EndpointSourceFullW. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace OAI.SevenEighths.UnevenEndpoint.Physical.Source
variable [config : _root_.OAI.SevenEighths.UnevenEndpoint.Configuration]
open OAI.SevenEighths.UnevenEndpoint OAI.SevenEighths.UnevenEndpoint.Count OAI.SevenEighths.UnevenEndpoint.Physical.Scalar
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open OAI.SevenEighths.UnevenEndpoint.Physical OAI.SevenEighths.UnevenEndpoint.Physical.FinalAssembly
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
  ∀(rows : Finset FreeRow) (d a : ℝ) (i : ℕ),d0≤ d → d≤ dPlus →
  51/100< a → a≤7/8 → i≤ n →
  (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
    (calibrationForSet A.F.S A.F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-A.D.t)) →
  (∀u∈rows,(Z^d)^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ Z^d) →
  (∀u∈rows,(rowCharacter A.F.S A.F.exclusions.prime u).residue≠1) →
  (∀u∈rows,Z^(d-2*A.D.t)≤ rowNorm u) →
  (∀u∈rows,detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
    (rayCubeFamily A.F.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^τ)< a+2*A.D.e) →
  (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
    (rayCubeFamily A.F.modulus ⊤ le_top u)) ((3*i:ℕ)*Z^τ)) →
  ‖Cycle25.Weighted.FullWContour.finiteCentralFullWRows A.F.S A.F.exclusions A.F.maximal η rows
    (sourcePrimePool A.F Z) (fun j=> source_prime_pool_outside A.F Z j)
    (fun _ y=>(A.F.w y:ℂ)) (fun j=> Z^(A.D.length j)) A.F.W A.F.W (Z^x) (Z^y) Z A.D.e
    (fun _=> a) (fun _=>(3*i+1:ℕ)*Z^τ)/
      UnevenEndpointPhysicalHighTransport.actualNormalizer A.F.modulus ⊤ A.F.S A.D.length 1 2 (fun _=> A.F.w) A.F.W A.F.W Z‖≤
    C*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps)*Z^(sourceTarget+A.D.t/8)

/-- The two remaining Mellin integrals and literal source normalization cost
only the displayed normalizer reserve, after the fixed degree is absorbed. -/
theorem actual_fullW_cells (hgap : theta< HeckeZeroSupremum.beta) (A : ChosenData)
    (hAffine : ActualAffineInput A) :
    ∃J : ℝ,0≤ J ∧ ∀τ : ℝ,HeightAdmissible A.D A.P J τ →
    ∀n : ℕ,∀η : Character,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,
    ∀C0 : ℝ,1≤ C0 →
    SourceMomentBound A.D (baselineSource A.D A.F) A.counts η Z τ (C0*Z^A.D.t) (Z^(2*τ)) →
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
  have hZ0 : 0< Z := zero_lt_one.trans hZ
  let B : ℝ := Cw*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps)*Z^(sourceTarget-kernelExponent a A.D.e)
  have hB : 0≤ B := by dsimp [B];positivity
  have hintegrated : ∀q∈Cycle25.Weighted.FullWContour.szRectangle ((3*i+1:ℕ)*Z^τ),
      ‖Cycle25.Weighted.FullWContour.integratedDyadValue A.F.S A.F.exclusions A.F.maximal η rows
        (sourcePrimePool A.F Z) (fun j=> source_prime_pool_outside A.F Z j)
        (fun _ y=>(A.F.w y:ℂ)) (fun j=> Z^(A.D.length j)) A.F.W (Z^y)
        ((((a+16*A.D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)‖≤ B := by
    intro q hq
    have hh := hraw rows d a i hd hdmax ha hatop hiidx hsource hrows hrow hfreq hnext hcurrent q hq
    rw [source_real_profile_eq A.F]
    exact source_absorb_height _ Z (Cw*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps))
      (((3*i+1:ℕ):ℝ)*Z^τ) J (sourceTarget-kernelExponent a A.D.e) A.D.t hZ0
      (by positivity) (hheight i hiidx) (by simpa only [sub_sub,add_comm] using hh)
  have hh := hi A.D.e a (Z^τ) (((3*i+1:ℕ):ℝ)*Z^τ) i A.D.e_pos A.D.e_small ha.le
    (by linarith) hT (by push_cast;have hp:=Real.rpow_nonneg hZ0.le τ;nlinarith)
    A.F.S A.F.exclusions A.F.maximal A.F.first η rows (fun u hu=>(hsource u hu).1)
    (sourcePrimePool A.F Z) (fun j=> source_prime_pool_outside A.F Z j)
    (rayCubeFamily A.F.modulus ⊤ le_top) hnext (fun _ y=>(A.F.w y:ℂ))
    (fun j=> Z^(A.D.length j)) A.F.W 1 2 (by norm_num) A.F.complex_support
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
end OAI.SevenEighths.UnevenEndpoint.Physical.Source
end

/- Original module: Candidate.Uneven.EndpointFiniteSourceCells. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.UnevenEndpoint.Physical.FiniteNumerator
variable [config : _root_.OAI.SevenEighths.UnevenEndpoint.Configuration]
noncomputable section
open scoped Classical BigOperators
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open OAI.SevenEighths.UnevenEndpoint.Physical FinalAssembly UnevenEndpointPhysicalHighTransport
open OAI.SevenEighths.UnevenEndpoint.Physical.Assembly Cycle25.Numerator

/-- Source's genuine cell theorem is specialized to the actual buffered partition. -/
theorem actual_cells_of_affine (hgap : OAI.SevenEighths.UnevenEndpoint.theta< HeckeZeroSupremum.beta)
    (A : ChosenData) (hAffine : Source.ActualAffineInput A) :
    ∃J : ℝ,0≤ J ∧ ActualFullWCellInput A J := by
  obtain ⟨J,hJ,hcells⟩:=Source.actual_fullW_cells hgap A hAffine
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
end OAI.SevenEighths.UnevenEndpoint.Physical.FiniteNumerator
end

/- Original module: Candidate.Uneven.EndpointFiniteBridge. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/

                                           
                                        

set_option autoImplicit false
namespace OAI.SevenEighths.UnevenEndpoint.Physical.FiniteNumerator
variable [config : _root_.OAI.SevenEighths.UnevenEndpoint.Configuration]
noncomputable section
open scoped Classical BigOperators
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open OAI.SevenEighths.UnevenEndpoint.Physical FinalAssembly UnevenEndpointPhysicalHighTransport
open OAI.SevenEighths.UnevenEndpoint.Physical.Assembly

theorem target_positive (A : ChosenData) (hgap : OAI.SevenEighths.UnevenEndpoint.theta< HeckeZeroSupremum.beta) :
    0< HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma := by
  have ht:=A.D.t_small
  have hs:=A.P.sigma_small
  have ha : (1/10:ℝ)< OAI.SevenEighths.UnevenEndpoint.theta+Assembly.signalShift := by
    rcases config with ⟨stage⟩; cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,OAI.SevenEighths.UnevenEndpoint.theta,Assembly.signalShift,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h]
  linarith

/-- Actual cell bounds and actual count moments imply the literal finite cube bound. -/
theorem fixed_numerator_of_cells (hgap : OAI.SevenEighths.UnevenEndpoint.theta< HeckeZeroSupremum.beta)
    (A : ChosenData) (J : ℝ) (hcell : ActualFullWCellInput A J)
    (τ : ℝ) (hheight : HeightAdmissible A.D A.P J τ) (η : Character)
    (hcount : ∃C : ℝ,1≤ C ∧ ∀ᶠZ : ℝ in atTop,
      SourceMomentBound A.D (baselineSource A.D A.F) A.counts η Z τ
        (C*Z^A.D.t) (Z^(2*τ))) : FixedFiniteNumeratorInputAt A.D A.F A.P τ η := by
  intro n _
  obtain ⟨Cc,hCc,hcount⟩:=hcount
  obtain ⟨Cs,hCs,hcell⟩:=hcell τ hheight n η
  have hCcpos : 0< Cc:=zero_lt_one.trans_le hCc
  have hηpos : (0:ℝ)<(η.modulus.absNorm:ℝ) :=
    zero_lt_one.trans_le (HeckeLogarithmicInput.modulus_norm_ge_one η)
  let C : ℝ:=Cs*Cc*(η.modulus.absNorm:ℝ)^(2*A.P.eps)
  have hC : 0< C:=by dsimp [C];positivity
  obtain ⟨Csum,hCsum,hsum⟩:=fullW_sum_bound A τ n η C hC
  obtain ⟨Ce,hCe,herror⟩:=actual_selected_error A τ hheight.1
  change ∃Ctot : ℝ,0< Ctot ∧ ∀ᶠZ : ℝ in atTop,∀idx grid : FreeRow→ℕ,
    ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
      η rowPadding A.D.e τ n Z idx grid →
    ‖finiteNonfloorNumerator A.F.modulus ⊤ A.F.S A.F.exclusions A.F.maximal A.D.length
      1 2 rowPadding A.D.e τ (fun _=> A.F.w) A.F.W A.F.W η Z idx grid‖ ≤
      Ctot*‖normalizer A.D A.F Z‖*Z^(HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma)
  refine ⟨Csum+1,by positivity,?_⟩
  filter_upwards [hcount,hcell,hsum,herror,eventually_ge_atTop ((Ce+1)*(η.modulus.absNorm:ℝ)^2),
    eventually_ge_atTop (1:ℝ)] with Z hc hcells hs he hlarge hZ
  intro idx grid hsel
  have hcells : FullWCellsAt A τ n η C Z:=hcells Cc hCc hc
  have hb:=hs hcells idx grid hsel
  obtain ⟨hN,herr⟩:=he n η idx grid hsel
  have hZp : 0< Z:=zero_lt_one.trans_le hZ
  have hsaving : Ce*(η.modulus.absNorm:ℝ)^2*Z^(-(1:ℝ))≤1 := by
    calc
      _ ≤ Z*Z^(-(1:ℝ)) := mul_le_mul_of_nonneg_right
        (by nlinarith only [hlarge,sq_nonneg (η.modulus.absNorm:ℝ)]) (by positivity)
      _ = 1 := by rw [Real.rpow_neg_one];exact mul_inv_cancel₀ hZp.ne'
  have hone : (1:ℝ)≤ Z^(HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma) :=
    Real.one_le_rpow hZ (target_positive A hgap).le
  let V := finiteNonfloorNumerator A.F.modulus ⊤ A.F.S A.F.exclusions A.F.maximal A.D.length
    1 2 rowPadding A.D.e τ (fun _=> A.F.w) A.F.W A.F.W η Z idx grid
  let W := fullW A.D A.F η Z (selectedRows A.D A.F Z grid)
    (fun u=>51/100+A.D.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)
  let N := normalizer A.D A.F Z
  let E := Z^(HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma)
  have hnormalized : ‖V/N‖≤(Csum+1)*E := by
    calc
      _ = ‖(V/N-W/N)+W/N‖ := by rw [sub_add_cancel]
      _ ≤ ‖V/N-W/N‖+‖W/N‖ := norm_add_le _ _
      _ ≤ 1+Csum*E := add_le_add (herr.trans hsaving) hb
      _ ≤ (Csum+1)*E := by dsimp [E];nlinarith only [hone]
  rw [norm_div] at hnormalized
  have hraw:=(div_le_iff₀ (norm_pos_iff.mpr hN)).mp hnormalized
  simpa only [V,N,E,mul_assoc,mul_comm,mul_left_comm] using hraw

/-- The only remaining analytic input is the initial affine moment at this fixed data. -/
theorem fixed_numerator_of_affine (hgap : OAI.SevenEighths.UnevenEndpoint.theta< HeckeZeroSupremum.beta)
    (A : ChosenData) (hAffine : Source.ActualAffineInput A) :
    ∃J : ℝ,0≤ J ∧ ∀τ : ℝ,HeightAdmissible A.D A.P J τ →
      ∀η : Character,(∃C : ℝ,1≤ C ∧ ∀ᶠZ : ℝ in atTop,
        SourceMomentBound A.D (baselineSource A.D A.F) A.counts η Z τ
          (C*Z^A.D.t) (Z^(2*τ))) → FixedFiniteNumeratorInputAt A.D A.F A.P τ η := by
  obtain ⟨J,hJ,hcells⟩:=actual_cells_of_affine hgap A hAffine
  exact ⟨J,hJ,fun τ hheight η hcount=> fixed_numerator_of_cells hgap A J hcells τ hheight η hcount⟩
end
end OAI.SevenEighths.UnevenEndpoint.Physical.FiniteNumerator
end
