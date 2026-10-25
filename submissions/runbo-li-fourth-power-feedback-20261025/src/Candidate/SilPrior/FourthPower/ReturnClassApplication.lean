/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
Actual H class application, with a numerical compatible source constructor.
The small contour parameter is reduced AFTER the finite slot system is fixed,
before the source is chosen, exactly as in PR69 TransportParameters. The only
change to that constructor is proving positive theta from our true rational
value, rather than requiring the incompatible global Geometry.Bounds class.

The application below discharges BOTH the full original-row cardinality and
canonical prime-amplitude upper bounds using actual upstream theorems. All
seventeen windows, the full physical source and the common finite detector
are kept. The full-source theorem remains an explicit unfinished premise.

-/
import Candidate.SilPrior.FourthPower.ReturnPacket
import Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.TransportParameters
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.Helpers
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.SourcePools
import Candidate.SilPrior.FourthPower.ReturnPhysicalHelpers
import Candidate.SilPrior.FourthPower.ReturnScalarBridge
import Candidate.SilPrior.FourthPower.ReturnCarrierInterfaces
import Candidate.SilPrior.FourthPower.OlderIncumbentContract

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.ReturnClassApplication
noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter Set OAI OAI.SevenEighths
open HeckeFamily ProbeHighRowFamily ProbePhysical HeckeInverseAmplification
open Cycle25.Weighted Cycle25.Weighted.Numerator Cycle25.Numerator
open Cycle25ProbeFinalAssembly Cycle25DetectorRowCount
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open QRH.Record12518109Count QRH.Record12518109Existence
open QRH.Record1252270103Return
open QRH.Record1252270103Return.GenericPhysical
open QRH.Record1252270103Return.GenericPhysical.Assembly
open ReturnCertificate ReturnWindows ReturnSourceFaces ReturnOldCount ReturnActualCount
open ReturnSourceInputs ReturnMaskedCount ReturnEnvelopeBridge
local instance : Geometry.Parameters := ReturnSourceInputs.parameters
local instance : CountScheme := ReturnWindows.countScheme

theorem exists_compatible_data_with_mesh {κ budget : ℝ} (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hb : 0< budget) (extraMesh : ℝ → ℝ)
    (hExtra : ∀t : ℝ,0< t → 0< extraMesh t) :
    ∃D : QRH.Record1252270103Return.GenericPhysical.BaselineData,D.momentKappa=κ ∧ 159*D.ε+609*D.t≤ budget ∧
      (∀j,D.length j≤ Cycle25.sourceMesh D.t/200) ∧
      (∀j,D.length j≤ ReturnCarrierInterfaces.commonMesh D.t/200) ∧
      (∀j,D.length j≤ extraMesh D.t/200) ∧ Nonempty (TransportParameters D) := by
  exact ReturnCarrierInterfaces.exists_compatible_data_with_mesh
    (by change 0<Candidate.SilPrior.FourthPower.theta; norm_num [Candidate.SilPrior.FourthPower.theta])
    hk hk1 hb extraMesh hExtra

/-- The actual finite detector can satisfy phase-bin geometry simultaneously
with both source meshes. The small contour e is chosen before F or eta. -/
theorem exists_compatible_joint
    (hsource : UniformUnitFaceSource fullSourceFace)
    (hbeta : theta<HeckeZeroSupremum.beta)
    (sigma affineError extraMesh : ℝ) (hsigma : 0< sigma)
    (herror : 0<affineError) (hextra : 0<extraMesh) :
    ∃A : JointData sigma affineError extraMesh,Nonempty (TransportParameters A.D) := by
  have hg := contrary_gates hbeta
  obtain ⟨physicalMesh,hphysicalMesh,hphysical⟩ := hsource affineError herror
  choose rawMesh hrawMesh hraw using
    fun t : {t : ℝ // 0<t}=>hsource t.val t.property
  let mesh : ℝ→ℝ := fun t=>if ht : 0<t then
    min (rawMesh ⟨t,ht⟩) (min physicalMesh extraMesh) else 1
  have hm : ∀t,0<t→0< mesh t := by
    intro t ht
    simp only [mesh,dif_pos ht]
    exact lt_min (hrawMesh ⟨t,ht⟩) (lt_min hphysicalMesh hextra)
  obtain ⟨D,hk,hcount,hfine,_,hsourceFine,hP⟩ :=
    exists_compatible_data_with_mesh hg.1 hg.2.1 hsigma mesh hm
  obtain ⟨F⟩ := exists_baseline_source D
  obtain ⟨counts⟩ := exists_saved_parameters F
  have hmraw : mesh D.t≤rawMesh ⟨D.t,D.t_pos⟩ := by
    simp only [mesh,dif_pos D.t_pos]
    exact min_le_left _ _
  have hmphys : mesh D.t≤physicalMesh := by
    simp only [mesh,dif_pos D.t_pos]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hmextra : mesh D.t≤extraMesh := by
    simp only [mesh,dif_pos D.t_pos]
    exact (min_le_right _ _).trans (min_le_right _ _)
  let A : JointData sigma affineError extraMesh := {
    D := D
    F := F
    mesh := mesh D.t
    mesh_pos := hm D.t D.t_pos
    mesh_extra := hmextra
    fine_source := hsourceFine
    fine_natural := hfine
    moment_exact := hk
    count_error := hcount
    count_unit := (hraw ⟨D.t,D.t_pos⟩).mono_mesh hmraw
    physical_unit := hphysical.mono_mesh hmphys
    counts := counts }
  exact ⟨A,hP⟩

variable {sigma affineError extraMesh : ℝ}

/-- Literal selected error-mask packet after discharging all finite-cardinality
and prime-amplitude assumptions. The remaining row conditions are the original
detector/calibration/nonprincipal restrictions, not a desired moment estimate.
This physical branch has ds<=d<=dplus; the low-conductor branch is separate. -/
def ActualClassPacket (A : JointData sigma affineError extraMesh)
    (η : Character) (tau C Z : ℝ) (degree n : ℕ) : Prop :=
  ∀d a : ℝ,ds≤d→d≤dplus→51/100<a→a≤7/8→
  ∀rows : Finset FreeRow,
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet A.F.S A.F.maximal).residueMonoid u.val≠0 ∧
      rowNorm u≤Z^(d-A.D.t))→
    (∀u∈rows,(rowCharacter A.F.S A.F.exclusions.prime u).residue≠1)→
  ∀i : ℕ,i≤n→
    (∀u∈rows,detectorMaximum
      (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
        (rayCubeFamily A.F.modulus ⊤ le_top u))
      (3*(i+1:ℕ)*Z^tau)<a+2*A.D.e)→
    (∀u∈rows,a≤detectorMaximum
      (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
        (rayCubeFamily A.F.modulus ⊤ le_top u))
      ((3*i:ℕ)*Z^tau))→
  ∀xc z : ℂ,xc.re=a+16*A.D.e→z.re=17/50→|z.im|≤((3*i+1:ℕ):ℝ)*Z^tau→
  ∀J : Finset (Fin A.D.N),
  ∀bin : BinLabel (Finset.univ : Finset (Fin A.D.N)) ((2*a-1)/2) A.D.t,
  let Q := fun (u:FreeRow) j=>HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤
    u.val A.F.W 2 (Z^(A.D.length j)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) A.D.t A.D.t_pos
    (fun j=>A.D.length j/d) Q bin
  let main := (Finset.univ : Finset (Fin A.D.N))\J
  let q := weightedMean Finset.univ (fun j=>A.D.length j/d)
    (maskedGain main (binValue Finset.univ ((2*a-1)/2) A.D.t bin))
  rows'.Nonempty→
    (∑r:rows',‖labelPolynomialPacket A.F.S A.F.exclusions η r.val
      (fun s:J=>sourcePrimePool A.F Z s.val)
      (fun s=>source_prime_pool_outside A.F Z s.val)
      (fun _=>A.F.W) (fun s=>Z^(A.D.length s.val)) xc z A.F.W
      ((Z^d)^(y/d))*(∏s∈main,Q r.val s)‖)≤
    C*(1+Z^(2*tau))^degree*((Z^d)^(y/d))^(-(1/2:ℝ))*
      (∏s:J,(Z^(A.D.length s.val))^(-(4/25:ℝ)))*
      (Z^d)^(A.D.t+q*(ell/d)-q*shiftedWidth d 0/2+
        (3*(variableEnvelope contraryKappa (2*a-1) (q/(2*a-1))+sigma)
          +1+A.D.t+affineError+A.D.t)/4+
        (2*a-1)*Cycle25.sourceMesh A.D.t/4+
        (2*a-1)*(A.D.t+A.D.t)/2+A.D.t*(ell/d))

/-- Genuine high-conductor class application. Every error mask uses the SAME
tau, saved count parameters and source, with the maximum physical degree fixed
before eta. No cardinality, moment, selected-energy or prime-bin estimate is
assumed. The original seventeen-window envelope appears literally in the RHS. -/
theorem actual_class_packets (hPrior : OlderIncumbentContract.OlderIncumbentInput) (A : JointData sigma affineError extraMesh)
    (P : TransportParameters A.D)
    (hsource : UniformUnitFaceSource fullSourceFace)
    (hbeta : theta<HeckeZeroSupremum.beta) (haff : 0<affineError)
    (heightLoss : ℝ) (hheightLoss : 0<heightLoss) :
    ∃degree : ℕ,∀η : Character,∃tau : ℝ,CountHeight A.D degree heightLoss tau ∧
      ∀n : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
        1<Z ∧ ActualClassPacket A η tau C Z degree n := by
  have hg := contrary_gates hbeta
  obtain ⟨bPhi,_,hsPhi,di,control,Ci,hCi,hinput⟩ := actual_physical_input A
  choose degree Cphys hCphys hpacket using fun J : Finset (Fin A.D.N)=>
    ReturnPacket.source_packet_amplitude_class A.D A.F hg.2.2
      (by rw [A.moment_exact]; exact le_rfl)
      bPhi A.mesh affineError haff hsPhi di control Ci hCi hinput
      A.fine_source A.fine_natural J
  let degreeMax : ℕ := Finset.univ.sup degree
  let Cmax : ℝ := 1+∑J,Cphys J
  have hdegree (J : Finset (Fin A.D.N)) : degree J≤degreeMax :=
    Finset.le_sup (Finset.mem_univ J)
  have hCmax : 0<Cmax := by
    have hh : 0≤∑J,Cphys J := Finset.sum_nonneg (fun J _=>(hCphys J).le)
    dsimp only [Cmax]
    linarith
  have hCbound (J : Finset (Fin A.D.N)) : Cphys J≤Cmax := by
    have hh := Finset.single_le_sum (fun K _=>(hCphys K).le) (Finset.mem_univ J)
    dsimp only [Cmax]
    linarith
  have hpacketAll := Filter.eventually_all.mpr hpacket
  have hds : (0:ℝ)<ds := by norm_num [ds,kappa,theta,y,ell,h]
  have hpacketZ := ProbeHighRowFamily.eventually_all_rpow_ge hpacketAll ds hds
  refine ⟨degreeMax,?_⟩
  intro η
  obtain ⟨tau,htau,hcount⟩ := actual_masked_count hPrior A hsource hbeta degreeMax heightLoss
    (Nat.cast_nonneg _) hheightLoss η
  refine ⟨tau,htau,?_⟩
  intro n
  obtain ⟨Ccount,hCcount,hcount⟩ := hcount n
  refine ⟨Cmax*Ccount,mul_pos hCmax (zero_lt_one.trans_le hCcount),?_⟩
  filter_upwards [hpacketZ,hcount,
    Candidate.SilPrior.FourthPower.ReturnPhysicalHelpers.source_prime_bins
      A.D A.F P tau n htau.pos htau.detector_cost,
    source_prime_reconstruction_geometry A.F η,
    Candidate.SilPrior.FourthPower.ReturnPhysicalHelpers.source_pools_nonempty A.D A.F,
    Candidate.SilPrior.FourthPower.ReturnPhysicalHelpers.weighted_source_height_le
      tau n htau.pos]
    with Z hpack hc hupper hgeo hpools hheight
  have hZ := hc.1
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  refine ⟨hZ,?_⟩
  intro d a hd hdhi ha hahi rows hrows hrow i hi hnext hcurrent xc z hx hz hzim J bin
  dsimp only
  intro hne
  have hd0 : (1/200:ℝ)≤d := (by norm_num [ds,kappa,theta,y,ell,h] : (1/200:ℝ)≤ds).trans hd
  have hdmax : d≤7/8 := hdhi.trans (by norm_num [dplus,h])
  have hd1 : d≤1 := by linarith
  have hdpos : 0<d := hds.trans_le hd
  have hzHeight : |z.im|≤Z^(2*tau) := hzim.trans (hheight i hi).2
  have hcounts := hc.2 d a hd0 hdmax ha hahi rows hrows i hi hnext hcurrent z hz hzHeight
  have heq : QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.canonicalFamily
      A.D (baselineSource A.D A.F) Z z=
      (fun (u:FreeRow) j=>HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤
        u.val A.F.W 2 (Z^(A.D.length j)) z) := by
    funext u j
    simp only [QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.canonicalFamily,
      baselineSource,←A.F.complex_eq]
    rfl
  dsimp only at hcounts
  rw [heq] at hcounts
  have hcard := (hcounts (Finset.univ\J) bin hne).2.2
  let Q := fun (u:FreeRow) j=>HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤
    u.val A.F.W 2 (Z^(A.D.length j)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) A.D.t A.D.t_pos
    (fun j=>A.D.length j/d) Q bin
  have hphysical (u:FreeRow) (hu:u∈rows) :
      (Z^d)^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤Z^d := by
    constructor
    · apply le_trans _ (hrows u hu).2.1
      rw [←Real.rpow_mul hZ0.le]
      exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    · apply (hrows u hu).2.2.2.trans
      exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [A.D.t_pos])
  have hupper' : ∀u∈rows',∀j,‖Q u j‖≤(Z^(A.D.length j))^
      (HeckePrimeAmplitudeBins.amplitude (Z^(A.D.length j)) ((2*a-1)/2) A.D.t (Q u j)+A.D.t) := by
    intro u hu j
    have hur : u∈rows := (Finset.filter_subset _ _) hu
    have hh := hupper d hd0 hdmax η u (hrows u hur).2.1 (hrows u hur).2.2.1
      (hrows u hur).2.2.2 a i hi ha.le (by linarith) (hnext u hur) z hz hzim j
    simpa only [show a-1/2=(2*a-1)/2 by ring] using hh.2.2.2.1
  have hbase : ∀s:J,sourcePrimePool A.F Z s.val :=
    fun s=>⟨(hpools s.val).choose,(hpools s.val).choose_spec⟩
  have hp := (hpack d hd J).2 Z d hZ hd hdhi rfl η xc z a (Z^(2*tau)) ha.le hahi
    hx hz (Real.rpow_nonneg hZ0.le _) hzHeight rows hphysical hrow
    (hgeo.2.1 J) hgeo.2.2.2.1 hbase bin hne _ Ccount hCcount hcard hupper'
  apply hp.trans
  have hscale : 1≤1+Z^(2*tau) := by linarith [Real.rpow_nonneg hZ0.le (2*tau)]
  have hcoeff : Cphys J*Ccount*(1+Z^(2*tau))^(degree J)≤
      (Cmax*Ccount)*(1+Z^(2*tau))^degreeMax :=
    mul_le_mul (mul_le_mul_of_nonneg_right (hCbound J) (zero_le_one.trans hCcount))
      (pow_le_pow_right₀ hscale (hdegree J))
      (pow_nonneg (by positivity) _)
      (mul_nonneg hCmax.le (zero_le_one.trans hCcount))
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (by positivity) _))
      (Finset.prod_nonneg (fun s _=>Real.rpow_nonneg (by positivity) _)))
    (Real.rpow_nonneg (by positivity) _)

/-- The literal inherited packet/front/normalizer loss ledger, with our actual
count error and physical source error. This is only arithmetic bookkeeping;
the front/normalizer aggregate itself is not claimed in this module. -/
def physicalLoss (A : JointData sigma affineError extraMesh) (eps : ℝ) :
    ReturnAnalyticFinish.LossData where
  front := 3*A.D.t
  frequency := (17/25)*A.D.t
  scalar := 2*eps
  mass := A.D.t
  count := sigma
  moment := A.D.t+affineError+A.D.t
  selection := 0
  mesh := Cycle25.sourceMesh A.D.t+4*A.D.t
  slack := A.D.t

theorem physical_loss_bound (A : JointData sigma affineError extraMesh)
    (eps d delta : ℝ) (heps : 0≤eps) (hsigma : 0≤ sigma)
    (haff : 0≤affineError) (hd : d≤1) (hdelta : delta∈Icc (0:ℝ) (3/4)) :
    ReturnAnalyticFinish.weightedSourceLoss d delta (physicalLoss A eps)≤
      2*eps+3*sigma/4+affineError/4+7*A.D.t := by
  have ht := A.D.t_pos.le
  have hm := (Cycle25.sourceMesh_pos A.D.t_pos).le
  have hmesh := Candidate.SilPrior.FourthPower.ReturnScalarBridge.sourceMesh_le A.D.t_pos
  have hdelta0 := hdelta.1
  have hell : ell≤(1/5:ℝ) := by norm_num [ell,theta]
  have hte := mul_le_mul_of_nonneg_left hell ht
  have hδmesh : delta*(Cycle25.sourceMesh A.D.t+4*A.D.t)≤(15/4)*A.D.t := by
    calc
      _≤(3/4)*(Cycle25.sourceMesh A.D.t+4*A.D.t) :=
        mul_le_mul_of_nonneg_right hdelta.2 (by positivity)
      _≤(3/4)*(A.D.t+4*A.D.t) :=
        mul_le_mul_of_nonneg_left (add_le_add hmesh le_rfl) (by norm_num)
      _=_ := by ring
  have hbracket : 0≤2*eps+A.D.t+(3*sigma+(A.D.t+affineError+A.D.t))/4+
      delta*(Cycle25.sourceMesh A.D.t+4*A.D.t)/4 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hd hbracket
  dsimp only [ReturnAnalyticFinish.weightedSourceLoss,physicalLoss]
  nlinarith

/-- Shared numerical schedule under the contrary hypothesis. The source/count
errors and phase parameters are honest pre-height choices. No old geometrical
guards, beta cap or desired packet estimate is assumed. -/
theorem actual_loss_budget
    {extraMesh : ℝ} (hbeta : theta<HeckeZeroSupremum.beta)
    (A : JointData ((HeckeZeroSupremum.beta-theta)/10000)
      ((HeckeZeroSupremum.beta-theta)/10000) extraMesh)
    (P : TransportParameters A.D) :
    16*A.D.e+2*P.eps+3*((HeckeZeroSupremum.beta-theta)/10000)/4+
      ((HeckeZeroSupremum.beta-theta)/10000)/4+8*A.D.t≤
      (HeckeZeroSupremum.beta-theta)/4 := by
  have hep : P.eps≤A.D.t/100 := by
    have hN : (0:ℝ)≤A.D.N := Nat.cast_nonneg _
    have hp := P.eps_pos
    nlinarith [P.eps_budget]
  have ht : A.D.t≤(HeckeZeroSupremum.beta-theta)/10000 := by
    linarith [A.count_error,A.D.epsilon_pos,A.D.t_pos]
  linarith [P.e_tsmall,A.D.t_pos]

/-- The actual common data's error ledger is paid by the checked86-box return,
including variable kappa feedback. This conclusion covers old and new scalar
capacities; the actual class theorem above currently supplies the new physical
branch. No claim is made that the finite numerator has yet been aggregated. -/
theorem actual_numeric_return
    {extraMesh : ℝ} (hbeta : theta<HeckeZeroSupremum.beta)
    (A : JointData ((HeckeZeroSupremum.beta-theta)/10000)
      ((HeckeZeroSupremum.beta-theta)/10000) extraMesh)
    (P : TransportParameters A.D)
    (d delta p : ℝ) (hd : d∈Icc d0 dplus)
    (hdelta : delta∈Icc (0:ℝ) (3/4)) (hp : p∈Icc (0:ℝ) (1/2)) :
    ReturnAnalyticFinish.numeratorExponent contraryKappa d
      (ReturnFeedback.variableCapacity contraryKappa d) delta p+
      ReturnAnalyticFinish.kernelExponent ((1+delta)/2) A.D.e+
      ReturnAnalyticFinish.weightedSourceLoss d delta (physicalLoss A P.eps)<
        ReturnAnalyticFinish.signal HeckeZeroSupremum.beta-reserve/2-
          (HeckeZeroSupremum.beta-theta)/2-A.D.t := by
  have herror : 0≤(HeckeZeroSupremum.beta-theta)/10000 := by positivity
  have hd1 : d≤1 := hd.2.trans feedback_domain.2.1.le
  have hl := physical_loss_bound A P.eps d delta P.eps_pos.le herror herror hd1 hdelta
  have hb := actual_loss_budget hbeta A P
  exact ReturnAnalyticFinish.physical_packet_certificate (physicalLoss A P.eps)
    hbeta hd hdelta hp (by linarith)

end
end Candidate.SilPrior.FourthPower.ReturnClassApplication
