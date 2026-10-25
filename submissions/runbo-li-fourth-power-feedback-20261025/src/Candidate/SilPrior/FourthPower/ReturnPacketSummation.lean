/- Copyright (c) 2026 Sil, Hailey Collet, Gao and OpenAI. Apache-2.0.
Literal physical-front normalization, finite error-mask/amplitude-class sums
and integrated-dyad reconstruction, adapted from PR69 OldCollect for our
single all-band packet and checked variable-kappa return certificate.
Internal count/scalar interfaces are discharged by the actual final wrapper.
No global Geometry.Bounds or PhysicalSchedule is instantiated.

-/
import Candidate.SilPrior.FourthPower.ReturnCombinedPackets
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.FiniteHeight
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.PhysicalCollect
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.SourceScalar
import Submissions.hailey_collet_1252270103.Record1252270103Return.GenericScalar
import Candidate.SilPrior.FourthPower.ReturnCountBridge
import Candidate.SilPrior.FourthPower.ReturnPhysicalHelpers
import Candidate.SilPrior.FourthPower.ReturnScalarBridge
import Candidate.SilPrior.FourthPower.OlderIncumbentContract

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.ReturnPacketSummation
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
open QRH.Record1252270103Return.GenericPhysical.Scalar
open QRH.Record1252270103Return.GenericPhysical.PhysicalDirect
open ReturnCertificate ReturnWindows ReturnSourceFaces ReturnOldCount
open ReturnSourceInputs ReturnMaskedCount ReturnEnvelopeBridge ReturnPhysicalInput ReturnCombinedPackets
open QRH.Record1252270103Return.GenericPhysical.Assembly (TransportParameters)

local instance : Geometry.Parameters := ReturnSourceInputs.parameters
local instance : CountScheme := ReturnWindows.countScheme

private def returnLoss (D : QRH.Record1252270103Return.GenericPhysical.BaselineData) (eps sigma affineError : ℝ) :
    ReturnAnalyticFinish.LossData where
  front:=3*D.t
  frequency:=(17/25)*D.t
  scalar:=2*eps
  mass:=D.t
  count:=sigma
  moment:=D.t+affineError+D.t
  selection:=0
  mesh:=Cycle25.sourceMesh D.t+4*D.t
  slack:=D.t

local notation "physicalLoss" => QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.Source.physicalLoss

/-- Actual finite packet exponent, with our full-domain certificate. The
numeric budget is the same one supplied by actual_loss_budget. -/
private theorem packet_certificate (D : QRH.Record1252270103Return.GenericPhysical.BaselineData)
    (eps sigma affineError d a q : ℝ)
    (hgap : theta<HeckeZeroSupremum.beta)
    (hkap : D.momentKappa=2*HeckeZeroSupremum.beta-1)
    (heps : 0≤eps) (hsigma : 0≤ sigma) (haff : 0≤affineError)
    (hbudget : 16*D.e+2*eps+3*sigma/4+affineError/4+8*D.t≤
      (HeckeZeroSupremum.beta-theta)/4)
    (hd : d∈Icc d0 dplus) (ha : 51/100≤a) (hatop : a≤7/8)
    (hq : 0≤q ∧ q≤(2*a-1)/2) :
    numeratorExponent GenericCount.admittedBranches D.momentKappa d
        (ReturnFeedback.variableCapacity D.momentKappa d) (2*a-1) (q/(2*a-1))+
      weightedSourceLoss d (2*a-1) (physicalLoss D eps sigma affineError)≤
      ReturnAnalyticFinish.signal HeckeZeroSupremum.beta-reserve/2-
        (HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e := by
  have hdelta : 0<2*a-1 := by linarith
  have hdel : 2*a-1∈Icc (0:ℝ) (3/4) := by constructor <;> linarith
  have hp : q/(2*a-1)∈Icc (0:ℝ) (1/2) :=
    ⟨div_nonneg hq.1 hdelta.le,(div_le_iff₀ hdelta).mpr (by linarith [hq.2])⟩
  have hd1 : d≤1 := hd.2.trans feedback_domain.2.1.le
  have hl := Candidate.SilPrior.FourthPower.ReturnScalarBridge.physical_loss_bound
    D eps sigma affineError d (2*a-1) heps hsigma haff hd1 hdel
  have hl' : ReturnAnalyticFinish.weightedSourceLoss d (2*a-1)
      (returnLoss D eps sigma affineError)≤2*eps+3*sigma/4+affineError/4+7*D.t := hl
  have hh := ReturnAnalyticFinish.physical_packet_certificate
    (returnLoss D eps sigma affineError) hgap hd hdel hp
    (by linarith : 16*D.e+
      ReturnAnalyticFinish.weightedSourceLoss d (2*a-1) (returnLoss D eps sigma affineError)+D.t≤
        (HeckeZeroSupremum.beta-theta)/4)
  rw [←hkap,show (1+(2*a-1))/2=a by ring] at hh
  change numeratorExponent GenericCount.admittedBranches D.momentKappa d
      (ReturnFeedback.variableCapacity D.momentKappa d) (2*a-1) (q/(2*a-1))+
      kernelExponent a D.e+
      weightedSourceLoss d (2*a-1) (physicalLoss D eps sigma affineError)<_ at hh
  linarith

private theorem masked_class_mean_bounds (D : QRH.Record1252270103Return.GenericPhysical.BaselineData) (F : QRH.Record1252270103Return.GenericPhysical.BaselineSourceData D)
    (Z d delta : ℝ) (hZ : 1<Z) (hd : 0<d) (hdelta : 0≤delta)
    (z : ℂ) (rows : Finset FreeRow) (main : Finset (Fin D.N))
    (bin : BinLabel (Finset.univ : Finset (Fin D.N)) (delta/2) D.t)
    (hne : (amplitudeRows rows Finset.univ (Z^d) (delta/2) D.t D.t_pos
      (fun s=>D.length s/d)
      (fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2
        (Z^(D.length s)) z) bin).Nonempty) :
    let q := weightedMean Finset.univ (fun s=>D.length s/d)
      (maskedGain main (binValue Finset.univ (delta/2) D.t bin))
    0≤q ∧ q≤delta/2 := by
  obtain ⟨u,hu⟩ := hne
  apply weightedMean_bounds Finset.univ (fun s=>D.length s/d) _ delta
  · intro s _
    exact (div_pos (D.slots_pos s) hd).le
  · rw [←Finset.sum_div,D.slots_sum]
    exact div_pos Geometry.ell_pos hd
  · intro s _
    by_cases hs : s∈main
    · have he := amplitude_class_value rows Finset.univ (Z^d) (delta/2) D.t D.t_pos
        (fun s=>D.length s/d)
        (fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2
          (Z^(D.length s)) z) bin u hu s (Finset.mem_univ s)
      simp only [maskedGain,if_pos hs]
      rw [←he]
      exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)
    · simp only [maskedGain,if_neg hs]
      exact ⟨le_rfl,by positivity⟩


/-- A literal physical error-mask sum has the uniform pre-height certificate
exponent, with only the original full-class count and actual scalar as inputs. -/
theorem source_mask_amplitude_class (D:QRH.Record1252270103Return.GenericPhysical.BaselineData)
    (hgap:theta < HeckeZeroSupremum.beta)
    (hbetatop : HeckeZeroSupremum.beta ≤ 7/8)
    (hkap : D.momentKappa=2*HeckeZeroSupremum.beta-1)
    (F:QRH.Record1252270103Return.GenericPhysical.BaselineSourceData D) (hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (bPhi mesh affineError : ℝ) (haff : 0<affineError)
    (hsPhi : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0<Ci)
    (hinput : ∀ᶠU:ℝ in atTop,FullPhysicalAt F bPhi mesh affineError U di control Ci)
    (hfineAffine : ∀j,D.length j≤ mesh/200)
    (eps sigma : ℝ) (heps : 0< eps) (hsigma : 0 ≤ sigma)
    (hbudget : 16*D.e+2*eps+3*sigma/4+affineError/4+8*D.t ≤ (HeckeZeroSupremum.beta-theta)/4)
    (hfine:∀j,D.length j ≤  Cycle25.sourceMesh D.t/200) (J:Finset (Fin D.N)) :
    ∃degree:ℕ,∃C:ℝ,0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀(Z d:ℝ),1 < Z  →  d0 ≤ d  →  d ≤ dplus  →  U=Z^d  →
      ∀(η:Character) (x z:ℂ) (a height:ℝ),(51/100:ℝ) ≤ a  →  a ≤ 7/8  →
      x.re=a+16*D.e  →  z.re=17/50  →  0 ≤ height  →  |z.im| ≤ height  →
      ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U)  →
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1)  →
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val))  →
      (∀i P,P∈sourcePrimePool F Z i → IsCoprime P.val η.modulus)  →
      (∀i P,P∈sourcePrimePool F Z i → (4:ℝ) ≤ P.val.absNorm)  →
      (∀i,∀P∈F.S,(P.absNorm:ℝ) ≤ Z^(D.length i))  →
      (∀i:J,sourcePrimePool F Z i.val)  →
      ∀bin:BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
      let main := (Finset.univ:Finset (Fin D.N)) \ J
      let q := weightedMean Finset.univ (fun s=>D.length s/d)
        (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty  →  ∀Cs K C0:ℝ,0 ≤ Cs  →  1 ≤ K  →  1 ≤ C0  →
      (rows'.card:ℝ) ≤ K*C0*Z^(3*D.t)*U^(QRH.Record1252270103Return.GenericCount.envelope D.momentKappa (2*a-1) (q/(2*a-1))+sigma)  →
      (∀u∈rows',‖frequencyWeight z ⟨u.val,u.property.1⟩*numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖ ≤
        Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*U^(2*eps)*U^(-(17/50:ℝ))*Z^((17/25)*D.t))  →
      (∀u∈rows',∀s,‖Q u s‖ ≤ (Z^(D.length s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  →
      ‖sourceMaskContribution F η rows' J Z x z (Z^y)‖  ≤
        (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^((degree:ℝ)+2*eps)*
          Z^(ReturnAnalyticFinish.signal HeckeZeroSupremum.beta-(reserve/2)-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := by
  obtain ⟨degree,C,hC,hclass⟩ := combined_source_packet_amplitude_class D F hbeta (by rw [hkap]) bPhi mesh affineError haff hsPhi di control Ci hCi hinput hfineAffine hfine J
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hclass] with U hclass
  refine ⟨hclass.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow hdis hη hQ hS Pbase bin
  dsimp only
  let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
  let main := (Finset.univ:Finset (Fin D.N)) \ J
  let q := weightedMean Finset.univ (fun s=>D.length s/d)
    (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
  intro hne Cs K C0 hCs hK hC0 hcard hscalar hupper
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hU0 : 0 < U := zero_lt_one.trans hclass.1
  have hd0 : 0 < d := (show (0:ℝ)<d0 by norm_num [d0]).trans_le hd
  have hδ : 0 < 2*a-1 := by linarith
  have hsub : rows' ⊆ rows := Finset.filter_subset _ _
  have hY : U^(y/d)=Z^y := by
    rw [hUZ,←Real.rpow_mul hZ0.le,mul_div_cancel₀ _ hd0.ne']
  have hcount1 : 1 ≤ K*C0*Z^(3*D.t) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK hC0)
      (Real.one_le_rpow hZ.le (by have := D.t_pos;positivity))
  have hb := hclass.2 Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow
    hdis hη Pbase bin hne (QRH.Record1252270103Return.GenericCount.envelope D.momentKappa (2*a-1) (q/(2*a-1))+sigma)
    (K*C0*Z^(3*D.t)) hcount1 hcard hupper
  have heq (u:FreeRow) (hu:u∈rows') := errorLabelNumerator_eq_packet F.S F.exclusions (4*D.e) F.first η u
    (hrow u (hsub hu)) J (sourcePrimePool F Z) (fun s=>source_prime_pool_outside F Z s) hdis hη hQ
    (fun _=>F.W) (fun s=>Z^(D.length s)) x z (by rw [hx];linarith [D.e_pos]) hz.ge
    (by rw [hx];linarith [D.e_pos]) F.W 1 2 (by norm_num) F.complex_support (F.W.smooth ⊤)
    (Z^y) (Real.rpow_pos_of_pos hZ0 _)
  have hlabel : (∑u∈rows',‖errorLabelNumerator F.S F.exclusions η u J (sourcePrimePool F Z)
      (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) x z F.W (Z^y)*
      (∏s∈main,Q u s)‖)  ≤
    C*(K*C0*Z^(3*D.t))*(1+height)^degree*(U^(y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
      U^(D.t+q*(ell/d)-q*physicalCapacity D.momentKappa d/2+
        (3*(QRH.Record1252270103Return.GenericCount.envelope D.momentKappa (2*a-1) (q/(2*a-1))+sigma)+1+D.t+affineError+D.t)/4+
        (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(ell/d)) := by
    convert hb using 1
    calc
      _ = ∑i:rows',‖errorLabelNumerator F.S F.exclusions η i.val J (sourcePrimePool F Z)
          (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) x z F.W (Z^y)*
          (∏s∈main,Q i.val s)‖ := (Finset.sum_coe_sort rows' _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [heq i.val i.property,hY]
  let A := Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*U^(2*eps)*
    U^(-(17/50:ℝ))*Z^((17/25)*D.t)
  have hA : 0 ≤ A := by dsimp only [A];positivity
  have hphysical := source_mask_physical_front F η rows' J Z hZ0 x z hz (Z^y) hS A _ hA hscalar hlabel
  have hselection := masked_class_mean_bounds D F Z d (2*a-1) hZ hd0 hδ.le z rows main bin hne
  have hq0 : 0≤q := hselection.1
  have hqmax : q≤(2*a-1)/2 := hselection.2
  have he := Candidate.SilPrior.FourthPower.ReturnScalarBridge.source_packet_multiplicative_identity GenericCount.admittedBranches J D.length D.slots_sum Z D.momentKappa d
    (ReturnFeedback.variableCapacity D.momentKappa d) (2*a-1) q (C*K*C0*((1+height)^degree)) (physicalLoss D eps sigma affineError)
    hZ0 hd0.ne' hδ.ne'
  have hcapscale : ReturnFeedback.variableCapacity D.momentKappa d/d=physicalCapacity D.momentKappa d := by
    apply (div_eq_iff hd0.ne').mpr
    simpa only [mul_comm] using (physical_capacity_scaled (k:=D.momentKappa) hd0).symm
  rw [hcapscale] at he
  dsimp [QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.Source.physicalLoss] at he
  rw [show GenericArithmetic.y = y from rfl,
    show GenericArithmetic.ell = ell from rfl] at he
  have hcollapse : A*Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i ∉ J},D.length j.val))*
      (C*(K*C0*Z^(3*D.t))*(1+height)^degree*(U^(y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
      U^(D.t+q*(ell/d)-q*physicalCapacity D.momentKappa d/2+
        (3*(QRH.Record1252270103Return.GenericCount.envelope D.momentKappa (2*a-1) (q/(2*a-1))+sigma)+1+D.t+affineError+D.t)/4+
        (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(ell/d))) =
      (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*(1+height)^degree*
        Z^(numeratorExponent GenericCount.admittedBranches D.momentKappa d (ReturnFeedback.variableCapacity D.momentKappa d) (2*a-1) (q/(2*a-1))+
          weightedSourceLoss d (2*a-1) (physicalLoss D eps sigma affineError)) := by
    dsimp only [A]
    rw [hUZ]
    calc
      _ = (Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps))*
          (((Z^d)^(2*eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*D.t)*
            Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i ∉ J},D.length j.val)))*
          (C*(K*C0*Z^(3*D.t))*(1+height)^degree*((Z^d)^(y/d))^(-(1/2:ℝ))*
            (∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
            (Z^d)^(D.t+q*(ell/d)-q*physicalCapacity D.momentKappa d/2+
              (3*(QRH.Record1252270103Return.GenericCount.envelope D.momentKappa (2*a-1) (q/(2*a-1))+sigma)+1+D.t+affineError+D.t)/4+
              (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(ell/d)))) := by ring
      _ = _ := by
        have hex : (2*a-1)*(Cycle25.sourceMesh D.t+4*D.t)/4 =
          (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2 := by ring
        rw [hex] at he
        have hat : (Finset.univ : Finset J)=J.attach := rfl
        rw [←hat] at he
        dsimp only [QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.Source.physicalLoss]
        simp only [add_zero,zero_div,add_assoc] at he
        convert congrArg
          (fun r : ℝ => (Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps))*r) he using 1 <;> (try dsimp only [QRH.Record1252270103Return.GenericCount.envelope]) <;> ring
  have hphysical' := hphysical.trans_eq hcollapse
  have hheightpow : (1+height)^degree  ≤  (3+height)^(degree:ℝ) := by
    rw [Real.rpow_natCast]
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hcert := packet_certificate D eps sigma affineError d a q hgap hkap heps.le hsigma haff.le hbudget ⟨hd,hdmax⟩ ha hatop ⟨hq0,hqmax⟩
  apply hphysical'.trans
  calc
    _  ≤  (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*(3+height)^(degree:ℝ)*
        Z^(ReturnAnalyticFinish.signal HeckeZeroSupremum.beta-(reserve/2)-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hheightpow (by positivity)
      · exact Real.rpow_le_rpow_of_exponent_le hZ.le hcert
      · positivity
      · positivity
    _ = _ := by rw [Real.rpow_add (by linarith : 0 < 3+height) (degree:ℝ) (2*eps)];ring


theorem source_integrated_amplitude_classes (D : QRH.Record1252270103Return.GenericPhysical.BaselineData)
    (hgap : theta < HeckeZeroSupremum.beta)
    (hbetatop : HeckeZeroSupremum.beta ≤ 7/8)
    (hkap : D.momentKappa=2*HeckeZeroSupremum.beta-1)
    (F : QRH.Record1252270103Return.GenericPhysical.BaselineSourceData D) (hbeta : (51/100:ℝ)  ≤  HeckeZeroSupremum.beta)
    (bPhi mesh affineError : ℝ) (haff : 0<affineError)
    (hsPhi : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0<Ci)
    (hinput : ∀ᶠU:ℝ in atTop,FullPhysicalAt F bPhi mesh affineError U di control Ci)
    (hfineAffine : ∀j,D.length j≤ mesh/200)
    (eps sigma : ℝ) (heps : 0< eps) (hsigma : 0 ≤ sigma)
    (hbudget : 16*D.e+2*eps+3*sigma/4+affineError/4+8*D.t ≤ (HeckeZeroSupremum.beta-theta)/4)
    (hfine : ∀j,D.length j  ≤  Cycle25.sourceMesh D.t/200) :
    ∃Jw : ℝ,0  ≤  Jw ∧ ∃C : ℝ,0 < C ∧ ∀ᶠU : ℝ in atTop,
      1 < U ∧ ∀(Z d : ℝ),1 < Z  →  d0  ≤  d  →  d  ≤  dplus  →  U=Z^d  →
      ∀(η : Character) (x z : ℂ) (a height : ℝ),(51/100:ℝ)  ≤  a  →  a  ≤  7/8  →
      x.re=a+16*D.e  →  z.re=17/50  →  0  ≤  height  →  |z.im|  ≤  height  →
      ∀rows : Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ)  ≤  rowNorm u ∧ rowNorm u  ≤  U)  →
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1)  →
      (∀J : Finset (Fin D.N),∀P : ∀i:J,sourcePrimePool F Z i.val,
        Function.Injective (fun i=>(P i).val))  →
      (∀P : ∀i,sourcePrimePool F Z i,Function.Injective (fun i=>(P i).val))  →
      (∀i P,P∈sourcePrimePool F Z i  →  IsCoprime P.val η.modulus)  →
      (∀i P,P∈sourcePrimePool F Z i  →  (4:ℝ)  ≤  P.val.absNorm)  →
      (∀i,∀P∈F.S,(P.absNorm:ℝ)  ≤  Z^(D.length i))  →
      (∀i,sourcePrimePool F Z i)  →
      ∀Cs K C0 : ℝ,0  ≤  Cs  →  1  ≤  K  →  1  ≤  C0  →
      let Q := fun (u : FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude
        F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
      (∀J : Finset (Fin D.N),∀bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
        let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
        let q := weightedMean Finset.univ (fun s=>D.length s/d)
          (maskedGain (Finset.univ\J) (binValue Finset.univ ((2*a-1)/2) D.t bin))
        rows'.Nonempty  →  (rows'.card:ℝ)  ≤  K*C0*Z^(3*D.t)*
          U^(QRH.Record1252270103Return.GenericCount.envelope D.momentKappa (2*a-1) (q/(2*a-1))+sigma))  →
      (∀u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩*
        numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖  ≤
        Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*
          U^(2*eps)*U^(-(17/50:ℝ))*Z^((17/25)*D.t))  →
      (∀u∈rows,∀s,‖Q u s‖  ≤  (Z^(D.length s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  →
      ‖Cycle25.Weighted.FullWContour.integratedDyadValue F.S F.exclusions F.maximal η rows (sourcePrimePool F Z)
        (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) F.W (Z^y) x z‖  ≤
        (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^Jw*
          Z^(ReturnAnalyticFinish.signal HeckeZeroSupremum.beta-(reserve/2)-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := by
  choose degree Cmask hCmask hmask using (fun J : Finset (Fin D.N)=>source_mask_amplitude_class D hgap hbetatop hkap F hbeta bPhi mesh affineError haff hsPhi di control Ci hCi hinput hfineAffine eps sigma heps hsigma hbudget hfine J)
  obtain ⟨Jw,hJw,Ctot,hCtot,hcoeff,hheight⟩ := finite_height_envelope degree Cmask hCmask
  let classFactor : ℝ := (HeckeDetectorClassBudget.alphabetBound D.t:ℝ)^D.N
  let maskFactor : ℝ := (2:ℝ)^D.N
  have hcf : 0 < classFactor := by
    unfold classFactor HeckeDetectorClassBudget.alphabetBound
    positivity
  have hmf : 0 < maskFactor := by dsimp only [maskFactor];positivity
  refine ⟨Jw+2*eps,by linarith [heps],(2*Real.pi)*classFactor*maskFactor*Ctot,
    by positivity,?_⟩
  filter_upwards [Filter.eventually_all.mpr hmask] with U hall
  refine ⟨(hall ∅).1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hH him rows hrows hrow
    hdis hdisAll hη hQ hS Pbase Cs K C0 hCs hK hC0
  dsimp only
  let Q := fun (u : FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude
    F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
  let classRows := fun bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t=>
    amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
  intro hcount hscalar hupper
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  let common : ℝ := Cs*K*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
    Z^(ReturnAnalyticFinish.signal HeckeZeroSupremum.beta-(reserve/2)-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e)
  let A : ℝ := common*Ctot*(3+height)^(Jw+2*eps)
  have hcommon : 0  ≤  common := by dsimp only [common];positivity
  have hA : 0  ≤  A := by dsimp only [A];positivity
  have hmaskBound (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t)
      (hne : (classRows bin).Nonempty) (J : Finset (Fin D.N)) :
      ‖sourceMaskContribution F η (classRows bin) J Z x z (Z^y)‖  ≤  A := by
    have hsub : classRows bin  ⊆  rows := Finset.filter_subset _ _
    have hh := (hall J).2 Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hH him
      rows hrows hrow (hdis J) hη hQ hS (fun j:J=>Pbase j.val) bin hne Cs K C0 hCs hK hC0
      (hcount J bin hne) (fun u hu=>hscalar u (hsub hu)) (fun u hu=>hupper u (hsub hu))
    have he := (hheight height eps hH heps.le).1 J
    calc
      _  ≤  (Cmask J*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
          (3+height)^((degree J:ℝ)+2*eps)*
          Z^(ReturnAnalyticFinish.signal HeckeZeroSupremum.beta-(reserve/2)-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := hh
      _ = common*(Cmask J*(3+height)^((degree J:ℝ)+2*eps)) := by dsimp only [common];ring
      _  ≤  common*(Ctot*(3+height)^(Jw+2*eps)) := mul_le_mul_of_nonneg_left he hcommon
      _ = A := by dsimp only [A];ring
  have hclass (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t)
      (hne : (classRows bin).Nonempty) :
      ‖reconstructedDyadValue F.S F.exclusions F.maximal η (classRows bin) (sourcePrimePool F Z)
        (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) x z F.W (Z^y)‖  ≤  maskFactor*A := by
    calc
      _ = ‖∑J∈Finset.univ.powerset,sourceMaskContribution F η (classRows bin) J Z x z (Z^y)‖ :=
        congrArg norm (source_reconstructed_sum_masks F η (classRows bin) Z x z (Z^y))
      _  ≤  ∑J∈Finset.univ.powerset,A := by
        apply (norm_sum_le _ _).trans
        exact Finset.sum_le_sum (fun J _=>hmaskBound bin hne J)
      _ = maskFactor*A := by
        simp only [Finset.sum_const,Finset.card_powerset,Finset.card_univ,Fintype.card_fin,
          nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
        rfl
  have hr := reconstructedDyadValue_class_uniform F.S F.exclusions F.maximal η rows
    (sourcePrimePool F Z) (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s))
    x z F.W (Z^y) Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (by linarith)
    (fun s=>D.length s/d) Q (maskFactor*A) (mul_nonneg hmf.le hA) hclass
  have heq := integratedDyadValue_reconstruction F.S F.exclusions F.maximal (4*D.e) F.first η rows hrow
    (sourcePrimePool F Z) (fun s=>source_prime_pool_outside F Z s) hdis hdisAll hη hQ
    (fun _=>F.W) (fun s=>Z^(D.length s)) x z (by rw [hx];linarith [D.e_pos]) hz.ge
    (by rw [hx];linarith [D.e_pos]) F.W 1 2 (by norm_num) F.complex_support (Z^y)
    (Real.rpow_pos_of_pos hZ0 _)
  rw [heq,norm_mul]
  have hpi : ‖(2*Real.pi:ℂ)‖=2*Real.pi := by
    rw [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hpi]
  apply (mul_le_mul_of_nonneg_left hr (by positivity : 0  ≤  2*Real.pi)).trans_eq
  simp only [Finset.card_univ,Fintype.card_fin]
  dsimp only [classFactor,maskFactor,A,common]
  ring





/-- Exact final source numerator exponent, before its Mellin kernel. -/
def sourceTarget : ℝ := ReturnAnalyticFinish.signal HeckeZeroSupremum.beta-reserve/2-
  (HeckeZeroSupremum.beta-theta)/2

abbrev GapData (extraMesh : ℝ) :=
  JointData ((HeckeZeroSupremum.beta-theta)/10000)
    ((HeckeZeroSupremum.beta-theta)/10000) extraMesh

def RawSourceDyadBound {extraMesh : ℝ} (A : GapData extraMesh)
    (P : TransportParameters A.D) (η : Character) (Z tau : ℝ) (n : ℕ)
    (J C : ℝ) : Prop :=
  ∀(rows : Finset FreeRow) (d a : ℝ) (i : ℕ),d0≤d→d≤dplus→
  51/100<a→a≤7/8→i≤n→
  (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
    (calibrationForSet A.F.S A.F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-A.D.t))→
  (∀u∈rows,(Z^d)^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤Z^d)→
  (∀u∈rows,(rowCharacter A.F.S A.F.exclusions.prime u).residue≠1)→
  (∀u∈rows,Z^(d-2*A.D.t)≤rowNorm u)→
  (∀u∈rows,detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
    (rayCubeFamily A.F.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^tau)<a+2*A.D.e)→
  (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
    (rayCubeFamily A.F.modulus ⊤ le_top u)) ((3*i:ℕ)*Z^tau))→
  ∀q∈Cycle25.Weighted.FullWContour.szRectangle ((3*i+1:ℕ)*Z^tau),
  ‖Cycle25.Weighted.FullWContour.integratedDyadValue A.F.S A.F.exclusions A.F.maximal η rows
    (sourcePrimePool A.F Z) (fun j=>source_prime_pool_outside A.F Z j)
    (fun _=>A.F.W) (fun j=>Z^(A.D.length j)) A.F.W (Z^y)
    ((((a+16*A.D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)‖≤
    C*(η.modulus.absNorm:ℝ)^(2*P.eps)*(3+((3*i+1:ℕ):ℝ)*Z^tau)^J*
      Z^(sourceTarget-A.D.t-kernelExponent a A.D.e)

/-- The actual all-band integrated dyad. Count moments, all cardinalities,
physical fourth moments, prime amplitude caps, and frequency/scalar bounds
are constructed here. Only the exact unfinished full source is analytical
input. The output is an actual finite FullW dyad, not a final common probe.
The one height parameter follows eta and the physical polynomial degree. -/
theorem actual_raw_source (hPrior : OlderIncumbentContract.OlderIncumbentInput) {extraMesh : ℝ} (A : GapData extraMesh)
    (P : TransportParameters A.D)
    (hsource : UniformUnitFaceSource fullSourceFace)
    (hgap : theta<HeckeZeroSupremum.beta)
    (heightLoss : ℝ) (hheightLoss : 0<heightLoss) :
    ∃J : ℝ,0≤J ∧ ∀η : Character,∃tau : ℝ,CountHeight A.D J heightLoss tau ∧
      ∀n : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
        1<Z ∧ RawSourceDyadBound A P η Z tau n J C := by
  obtain ⟨bPhi,_,hsPhi,di,control,Ci,hCi,hinput⟩ := actual_physical_input A
  have hb := (contrary_gates hgap).2.2
  have hbetatop : HeckeZeroSupremum.beta≤7/8 := by
    have hh := A.D.momentKappa_hi
    rw [A.moment_exact] at hh
    dsimp only [contraryKappa] at hh
    linarith
  let sigma : ℝ := (HeckeZeroSupremum.beta-theta)/10000
  have hsigma : 0< sigma := by dsimp only [sigma]; positivity
  obtain ⟨J,hJ,C,hC,hcollect⟩ := source_integrated_amplitude_classes A.D hgap hbetatop
    A.moment_exact A.F hb bPhi A.mesh sigma hsigma hsPhi di control Ci hCi hinput
    A.fine_source P.eps sigma P.eps_pos hsigma.le
    (ReturnClassApplication.actual_loss_budget hgap A P) A.fine_natural
  obtain ⟨Cs,hCs,hscalar⟩ :=
    Candidate.SilPrior.FourthPower.ReturnPhysicalHelpers.source_scalar_on_rows
      A.D A.F P.eps P.eps_pos
  refine ⟨J,hJ,?_⟩
  intro η
  obtain ⟨tau,htau,C0,hC0,hmom⟩ :=
    actual_moments_at_count_height hPrior A hsource hgap J heightLoss hJ hheightLoss η
  refine ⟨tau,htau,?_⟩
  intro n
  obtain ⟨K,hK,hcount⟩ :=
    Candidate.SilPrior.FourthPower.ReturnCountBridge.source_masked_count_with_error
      A.D (baselineSource A.D A.F) A.counts tau sigma n htau.pos htau.zero_rows
      htau.detector_cost htau.count_scale A.count_error
  refine ⟨(C*Cs*K)*C0,by have hk := zero_lt_one.trans_le hK; have hc0:=zero_lt_one.trans_le hC0; positivity,?_⟩
  filter_upwards [ProbeHighRowFamily.eventually_all_rpow_ge hcollect d0
      (by norm_num [d0]),hcount η,hmom,
    Candidate.SilPrior.FourthPower.ReturnPhysicalHelpers.source_prime_bins
      A.D A.F P tau n htau.pos htau.detector_cost,
    source_prime_reconstruction_geometry A.F η,
    Candidate.SilPrior.FourthPower.ReturnPhysicalHelpers.source_pools_nonempty A.D A.F,
    Candidate.SilPrior.FourthPower.ReturnPhysicalHelpers.weighted_source_height_le
      tau n htau.pos,
    (tendsto_rpow_atTop htau.pos).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)]
    with Z hcollect hcount hmom hupper hgeo hpools hheight hT hZ
  refine ⟨hZ,?_⟩
  unfold RawSourceDyadBound

  intro rows d a i hd hdmax ha hatop hi hsource hrows hrow hfreq hnext hcurrent q hq
  have hZ0 : 0< Z := zero_lt_one.trans hZ
  have hd' : d≤7/8 := hdmax.trans (by norm_num [dplus,h])
  have hz : ((17/50:ℂ)+q.2*Complex.I).re=17/50 := by norm_num
  have hx : ((((a+16*A.D.e):ℝ):ℂ)+q.1*Complex.I).re=a+16*A.D.e := by simp
  have him : |((17/50:ℂ)+q.2*Complex.I).im|≤((3*i+1:ℕ):ℝ)*Z^tau := by simpa using hq.2
  have hcounts := hcount d a C0 hd hd' ha hatop hC0 rows hsource i hi hnext hcurrent
    ((17/50:ℂ)+q.2*Complex.I) hz (him.trans (hheight i hi).2) hmom
  have heq : QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.canonicalFamily A.D (baselineSource A.D A.F) Z ((17/50:ℂ)+q.2*Complex.I)=
      (fun (u:FreeRow) j=>HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ u.val A.F.W 2
        (Z^(A.D.length j)) ((17/50:ℂ)+q.2*Complex.I)) := by
    funext u j
    simp only [QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.canonicalFamily,baselineSource,←A.F.complex_eq]
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
  have hscalar' := hscalar η rows Z tau d a i hZ0 hT ha.le hatop hfreq
    (fun u hu=>(hrows u hu).2) hnext q hq
  have hbase : ∀j,sourcePrimePool A.F Z j := fun j=>⟨(hpools j).choose,(hpools j).choose_spec⟩
  have hc := (hcollect d hd).2 Z d hZ hd hdmax rfl η
    ((((a+16*A.D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)
    a (((3*i+1:ℕ):ℝ)*Z^tau) ha.le hatop hx hz (hheight i hi).1 him rows hrows hrow
    hgeo.2.1 hgeo.2.2.1 hgeo.2.2.2.1 hgeo.2.2.2.2.1 hgeo.2.2.2.2.2 hbase Cs K C0 hCs.le hK hC0
    (by
      dsimp only
      intro J bin hne
      apply (hcounts (Finset.univ\J) bin hne).2.2.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hp : 1≤ Z^(3*A.D.t) := Real.one_le_rpow hZ.le (by have := A.D.t_pos;positivity)
      nlinarith [mul_nonneg (zero_le_one.trans hK) (zero_le_one.trans hC0)]) hscalar' hupper'
  simpa only [sourceTarget,mul_assoc] using hc

end
end Candidate.SilPrior.FourthPower.ReturnPacketSummation
