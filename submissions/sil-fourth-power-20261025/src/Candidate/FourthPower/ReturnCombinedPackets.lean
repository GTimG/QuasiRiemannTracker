/- Copyright (c) 2026 Sil, Hailey Collet, Gao and OpenAI. Apache-2.0.
Both actual physical conductor ranges on one source, one count scheme and
one height parameter. The lower branch is used at the join d=ds, so the
variable-kappa old capacity is exactly the feedback capacity there.
No old Geometry.Bounds / PhysicalSchedule instance and no desired count,
moment or energy estimate is assumed by actual_class_packets.

-/
import Candidate.FourthPower.ReturnLowPacket
import Candidate.FourthPower.ReturnPhysicalHelpers
import Candidate.FourthPower.ReturnScalarBridge
import Candidate.FourthPower.OlderIncumbentContract

set_option autoImplicit false
namespace Candidate.FourthPower.ReturnCombinedPackets
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
open ReturnSourceInputs ReturnMaskedCount ReturnEnvelopeBridge ReturnPhysicalInput
local instance : Geometry.Parameters := ReturnSourceInputs.parameters
local instance : CountScheme := ReturnWindows.countScheme

/-- Row-base capacity with an honest variable-kappa lower branch. -/
def physicalCapacity (k d : ℝ) : ℝ :=
  if d≤ds then
    QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.OldFourth.baseCapacity k d
  else shiftedWidth d 0

theorem physical_capacity_scaled {k d : ℝ} (hd : 0<d) :
    d*physicalCapacity k d=ReturnFeedback.variableCapacity k d := by
  by_cases hlow : d≤ds
  · simp only [physicalCapacity,ReturnFeedback.variableCapacity,if_pos hlow]
    exact Candidate.FourthPower.ReturnScalarBridge.OldFourth.base_scaled hd
  · simp only [physicalCapacity,ReturnFeedback.variableCapacity,if_neg hlow]
    exact ReturnPhysicalSchedule.scaled_zero_capacity hd

private theorem packet_rhs_mono
    {C C' Cc H Y E U r r' : ℝ} {degree degree' : ℕ}
    (hC : C≤C') (hC' : 0≤C') (hCc : 0≤Cc) (hH : 1≤H)
    (hdegree : degree≤degree') (hY : 0≤Y) (hE : 0≤E)
    (hU : 1≤U) (hr : r≤r') :
    C*Cc*H^degree*Y*E*U^r≤C'*Cc*H^degree'*Y*E*U^r' := by
  have hc := mul_le_mul (mul_le_mul_of_nonneg_right hC hCc)
    (pow_le_pow_right₀ hH hdegree) (pow_nonneg (zero_le_one.trans hH) _)
    (mul_nonneg hC' hCc)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hY) hE)
    (Real.rpow_le_rpow_of_exponent_le hU hr)
    (Real.rpow_nonneg (zero_le_one.trans hU) _)
    (by positivity)


theorem combined_source_packet_amplitude_class (D:QRH.Record1252270103Return.GenericPhysical.BaselineData)
    (F:QRH.Record1252270103Return.GenericPhysical.BaselineSourceData D) (hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hkbeta : 2*HeckeZeroSupremum.beta-1 ≤ D.momentKappa)
    (bPhi mesh affineError : ℝ) (haff : 0< affineError)
    (hsPhi : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ → ℂ) ⊆ Set.Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0< Ci)
    (hinput : ∀ᶠU:ℝ in atTop,FullPhysicalAt F bPhi mesh affineError U di control Ci)
    (hfineAffine : ∀j,D.length j ≤  mesh/200)
    (hfine:∀j,D.length j ≤ Cycle25.sourceMesh D.t/200) (J:Finset (Fin D.N)) :
    ∃degree:ℕ,∃C:ℝ,0< C ∧ ∀ᶠU:ℝ in atTop,
      1< U ∧ ∀(Z d:ℝ),1< Z  →  d0 ≤ d  →  d ≤ dplus  →  U=Z^d  → 
      ∀(η:Character) (x z:ℂ) (a height:ℝ),(51/100:ℝ) ≤ a  →  a ≤ 7/8  → 
      x.re=a+16*D.e  →  z.re=17/50  →  0 ≤ height  →  |z.im| ≤ height  → 
      ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U)  → 
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1)  → 
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val))  → 
      (∀i P,P∈sourcePrimePool F Z i → IsCoprime P.val η.modulus)  → 
      (∀i:J,sourcePrimePool F Z i.val)  → 
      ∀bin:BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
      let main := (Finset.univ:Finset (Fin D.N)) \ J
      let q := weightedMean Finset.univ (fun s=>D.length s/d)
        (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty  →  ∀R Ccount:ℝ,1 ≤ Ccount  →  (rows'.card:ℝ) ≤ Ccount*U^R  → 
      (∀u∈rows',∀s,‖Q u s‖ ≤ (Z^(D.length s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  → 
      (∑i:rows',‖labelPolynomialPacket F.S F.exclusions η i.val
        (fun s:J=>sourcePrimePool F Z s.val) (fun s=>source_prime_pool_outside F Z s.val)
        (fun _=>F.W) (fun s=>Z^(D.length s.val)) x z F.W (U^(y/d))*(∏s∈main,Q i.val s)‖)  ≤ 
        C*Ccount*(1+height)^degree*(U^(y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
          U^(D.t+q*(ell/d)-q*physicalCapacity D.momentKappa d/2+
            (3*R+1+D.t+affineError+D.t)/4+(2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(ell/d)) := by
  obtain ⟨degreeL,CL,hCL,hL⟩ :=
    ReturnLowPacket.old_source_packet_amplitude_class D F hbeta hkbeta hfine J
  obtain ⟨degreeH,CH,hCH,hH⟩ :=
    ReturnPacket.source_packet_amplitude_class D F hbeta hkbeta bPhi mesh affineError
      haff hsPhi di control Ci hCi hinput hfineAffine hfine J
  let degree := max degreeL degreeH
  let C := CL+CH
  have hC : 0<C := add_pos hCL hCH
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hL,hH] with U hL hH
  have hUpos : 0 < U := zero_lt_one.trans hL.1
  refine ⟨hL.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow hdis hη Pbase bin
  dsimp only
  intro hne R Ccount hCc hcard hupper
  by_cases hlow : d≤ds
  · have hb := hL.2 Z d hZ hd hlow hUZ η x z a height ha hatop hx hz hheight hzim
      rows hrows hrow hdis hη Pbase bin hne R Ccount hCc hcard hupper
    simp only [physicalCapacity,if_pos hlow]
    apply hb.trans
    exact packet_rhs_mono (by dsimp only [C]; linarith) hC.le
      (zero_le_one.trans hCc) (by linarith) (le_max_left _ _)
      (Real.rpow_nonneg (by positivity) _)
      (Finset.prod_nonneg (fun _ _=>Real.rpow_nonneg (by positivity) _))
      hL.1.le (by linarith)
  · have hb := hH.2 Z d hZ (le_of_not_ge hlow) hdmax hUZ η x z a height ha hatop
      hx hz hheight hzim rows hrows hrow hdis hη Pbase bin hne R Ccount hCc hcard hupper
    simp only [physicalCapacity,if_neg hlow]
    apply hb.trans
    exact packet_rhs_mono (by dsimp only [C]; linarith) hC.le
      (zero_le_one.trans hCc) (by linarith) (le_max_right _ _)
      (Real.rpow_nonneg (by positivity) _)
      (Finset.prod_nonneg (fun _ _=>Real.rpow_nonneg (by positivity) _))
      hL.1.le le_rfl


variable {sigma affineError extraMesh : ℝ}

def ActualClassPacket (A : JointData sigma affineError extraMesh)
    (η : Character) (tau C Z : ℝ) (degree n : ℕ) : Prop :=
  ∀d a : ℝ,d0≤d→d≤dplus→51/100<a→a≤7/8→
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
      (Z^d)^(A.D.t+q*(ell/d)-q*physicalCapacity contraryKappa d/2+
        (3*(variableEnvelope contraryKappa (2*a-1) (q/(2*a-1))+sigma)
          +1+A.D.t+affineError+A.D.t)/4+
        (2*a-1)*Cycle25.sourceMesh A.D.t/4+
        (2*a-1)*(A.D.t+A.D.t)/2+A.D.t*(ell/d))

/-- Genuine full-conductor class application. Every error mask uses the SAME
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
    combined_source_packet_amplitude_class A.D A.F hg.2.2
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
  have hds : (0:ℝ)<d0 := by norm_num [d0]
  have hpacketZ := ProbeHighRowFamily.eventually_all_rpow_ge hpacketAll d0 hds
  refine ⟨degreeMax,?_⟩
  intro η
  obtain ⟨tau,htau,hcount⟩ := actual_masked_count hPrior A hsource hbeta degreeMax heightLoss
    (Nat.cast_nonneg _) hheightLoss η
  refine ⟨tau,htau,?_⟩
  intro n
  obtain ⟨Ccount,hCcount,hcount⟩ := hcount n
  refine ⟨Cmax*Ccount,mul_pos hCmax (zero_lt_one.trans_le hCcount),?_⟩
  filter_upwards [hpacketZ,hcount,
    Candidate.FourthPower.ReturnPhysicalHelpers.source_prime_bins
      A.D A.F P tau n htau.pos htau.detector_cost,
    source_prime_reconstruction_geometry A.F η,
    Candidate.FourthPower.ReturnPhysicalHelpers.source_pools_nonempty A.D A.F,
    Candidate.FourthPower.ReturnPhysicalHelpers.weighted_source_height_le
      tau n htau.pos]
    with Z hpack hc hupper hgeo hpools hheight
  have hZ := hc.1
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  refine ⟨hZ,?_⟩
  intro d a hd hdhi ha hahi rows hrows hrow i hi hnext hcurrent xc z hx hz hzim J bin
  dsimp only
  intro hne
  have hd0 : (1/200:ℝ)≤d := hd
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
  rw [A.moment_exact] at hp
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


end
end Candidate.FourthPower.ReturnCombinedPackets
