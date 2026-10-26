import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Numerator.Source.Combined
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Numerator.Source.Helpers
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Final.CommonProbe
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Weighted.WeightedQRH.HighRows.WeightedSourceCellGeometry
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
noncomputable section
set_option maxHeartbeats 3000000
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace Cycle63.Numerator.Source
open Cycle63.Arithmetic Cycle63.Arithmetic.Bernstein Cycle63.Numerator.Scalar Cycle63.Numerator.Fourth
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle63DetectorCount Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open Cycle63.FinalAssembly

/-- The genuine initial physical affine moment, at an error fixed before height. -/
def ActualAffineInput (A : ChosenData) : Prop :=
  ∃bPhi affineError : ℝ,0<affineError ∧ affineError≤(HeckeZeroSupremum.beta-theta)/10000 ∧
  Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi ∧
  ∃di : ℕ,∃control : Finset (ℕ×ℕ),∃Ci : ℝ,0<Ci ∧
    ∀ᶠU:ℝ in atTop,AffineAt A.F bPhi A.P.mesh affineError U di control Ci

def sourceTarget : ℝ := Assembly.signal HeckeZeroSupremum.beta-rowSaving-
  (HeckeZeroSupremum.beta-theta)/2

def RawSourceDyadBound (A : ChosenData) (η : Character) (Z τ : ℝ) (n : ℕ)
    (J C C0 : ℝ) : Prop :=
  ∀(rows : Finset FreeRow) (d a : ℝ) (i : ℕ),d0≤d → d≤dPlus →
  51/100<a → a≤7/8 → i≤n →
  (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
    (calibrationForSet A.F.S A.F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-A.D.t)) →
  (∀u∈rows,(Z^d)^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤Z^d) →
  (∀u∈rows,(rowCharacter A.F.S A.F.exclusions.prime u).residue≠1) →
  (∀u∈rows,Z^(d-2*A.D.t)≤ rowNorm u) →
  (∀u∈rows,detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
    (rayCubeFamily A.F.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^τ)<a+2*A.D.e) →
  (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
    (rayCubeFamily A.F.modulus ⊤ le_top u)) ((3*i:ℕ)*Z^τ)) →
  ∀q∈WeightedQRH.FullWContour.szRectangle ((3*i+1:ℕ)*Z^τ),
  ‖WeightedQRH.FullWContour.integratedDyadValue A.F.S A.F.exclusions A.F.maximal η rows
    (WeightedQRH.Numerator.sourcePrimePool A.F Z) (fun j=>WeightedQRH.Numerator.source_prime_pool_outside A.F Z j)
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
  filter_upwards [OAI.SevenEighths.WeightedHighFinalAssembly.eventually_uniform_source_conductor d0 d0_pos hcollect,hcount η,
    source_prime_bins A.D A.F A.P τ n hτ hτcost,
    WeightedQRH.Numerator.source_prime_reconstruction_geometry A.F η,source_pools_nonempty A.D A.F,
    OAI.SevenEighths.WeightedHighFinalAssembly.weighted_source_height_le τ n hτ,
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),eventually_gt_atTop (1:ℝ)]
    with Z hcollect hcount hupper hgeo hpools hheight hT hZ
  intro C0 hC0 hmom
  unfold RawSourceDyadBound
  intro rows d a i hd hdmax ha hatop hi hsource hrows hrow hfreq hnext hcurrent q hq
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hd' : d≤7/8 := hdmax.trans (by unfold dPlus; linarith [h_bounds.2, dPlusOffset_bounds.2])
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
  have hbase : ∀j,WeightedQRH.Numerator.sourcePrimePool A.F Z j := fun j=>⟨(hpools j).choose,(hpools j).choose_spec⟩
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
end Cycle63.Numerator.Source

end
end Record1252270103Bootstrap.PR67
