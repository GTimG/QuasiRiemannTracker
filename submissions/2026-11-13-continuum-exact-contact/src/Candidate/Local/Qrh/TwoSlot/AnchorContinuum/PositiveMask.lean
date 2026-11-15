/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Variable-cost physical error-mask bound. Adapted from PR137 Mask (Sil,
Hailey Collet and predecessor authors, Apache-2.0). All original masks and
signed reconstruction identities are retained before taking norms. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveSchedule
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveAmplitudeClass
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.Mask
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
set_option maxHeartbeats 1200000
open scoped Classical BigOperators ContDiff
open Filter
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds] [scheme : Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line] [S : Schedule (line := line)]
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic QRH.Record12518109Count Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Scalar QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.Source
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open QRH.Record12518109Count
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

/-- A literal physical error-mask sum has the uniform pre-height certificate
exponent, with only the original full-class count and actual scalar as inputs. -/
theorem source_mask_amplitude_class (A:ChosenData)
    (hgap:theta < HeckeZeroSupremum.beta)
    (hbetatop : HeckeZeroSupremum.beta ≤ 7/8)
    (hkap : A.D.momentKappa=2*HeckeZeroSupremum.beta-1)
    (htop : dp (line := line) ≤ 2*Geometry.y)
    (hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (bPhi affineError : ℝ) (haff : 0< affineError)
    (hsPhi : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ → ℂ) ⊆ Set.Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0< Ci)
    (hinput : ∀ᶠU:ℝ in atTop,affineAtFace (PositiveSource.physicalFace S.cost) A bPhi affineError U di control Ci)
    (eps sigma : ℝ) (heps : 0< eps) (hsigma : 0 ≤ sigma)
    (hbudget : 16*A.D.e+2*eps+3*sigma/4+affineError/4+8*A.D.t ≤ (HeckeZeroSupremum.beta-theta)/4)
    (J:Finset (Fin A.D.N)) :
    ∃degree:ℕ,∃C:ℝ,0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀(Z d:ℝ),1 < Z  →  dm ≤ d  →  d ≤ dp  →  U=Z^d  →
      ∀(η:Character) (x z:ℂ) (a height:ℝ),(51/100:ℝ) ≤ a  →  a ≤ 7/8  →
      x.re=a+16*A.D.e  →  z.re=17/50  →  0 ≤ height  →  |z.im| ≤ height  →
      ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U)  →
      (∀u∈rows,(rowCharacter A.F.S A.F.exclusions.prime u).residue≠1)  →
      (∀P:∀i:J,sourcePrimePool A.F Z i.val,Function.Injective (fun i=>(P i).val))  →
      (∀i P,P∈sourcePrimePool A.F Z i → IsCoprime P.val η.modulus)  →
      (∀i P,P∈sourcePrimePool A.F Z i → (4:ℝ) ≤ P.val.absNorm)  →
      (∀i,∀P∈A.F.S,(P.absNorm:ℝ) ≤ Z^(A.D.length i))  →
      (∀i:J,sourcePrimePool A.F Z i.val)  →
      ∀bin:BinLabel (Finset.univ:Finset (Fin A.D.N)) ((2*a-1)/2) A.D.t,
      let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ u.val A.F.W 2 (Z^(A.D.length s)) z
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) A.D.t A.D.t_pos (fun s=>A.D.length s/d) Q bin
      let main := (Finset.univ:Finset (Fin A.D.N)) \ J
      let q := weightedMean Finset.univ (fun s=>A.D.length s/d)
        (maskedGain main (binValue Finset.univ ((2*a-1)/2) A.D.t bin))
      rows'.Nonempty  →  ∀Cs K C0:ℝ,0 ≤ Cs  →  1 ≤ K  →  1 ≤ C0  →
      (rows'.card:ℝ) ≤ K*C0*Z^(3*A.D.t)*U^(Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.envelope A.D.momentKappa (2*a-1) (q/(2*a-1))+sigma)  →
      (∀u∈rows',‖frequencyWeight z ⟨u.val,u.property.1⟩*numeratorFreeRowScalar A.F.S A.F.exclusions A.F.maximal η u x z‖ ≤
        Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*U^(2*eps)*U^(-(17/50:ℝ))*Z^((17/25)*A.D.t))  →
      (∀u∈rows',∀s,‖Q u s‖ ≤ (Z^(A.D.length s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(A.D.length s)) ((2*a-1)/2) A.D.t (Q u s)+A.D.t))  →
      ‖sourceMaskContribution A.F η rows' J Z x z (Z^Geometry.y)‖  ≤
        (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^((degree:ℝ)+2*eps)*
          Z^(Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly.signal HeckeZeroSupremum.beta-sourceReserve-(HeckeZeroSupremum.beta-theta)/2-A.D.t-kernelExponent a A.D.e) := by
  obtain ⟨degree,C,hC,hclass⟩ := amplitude_class_packet_with_cost A S.cost_pos.le S.cost_small hbeta (by rw [hkap]) bPhi affineError haff hsPhi di control Ci hCi hinput J
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hclass] with U hclass
  refine ⟨hclass.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow hdis hη hQ hS Pbase bin
  change (19/25:ℝ) ≤ d at hd
  dsimp only
  let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ u.val A.F.W 2 (Z^(A.D.length s)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) A.D.t A.D.t_pos (fun s=>A.D.length s/d) Q bin
  let main := (Finset.univ:Finset (Fin A.D.N)) \ J
  let q := weightedMean Finset.univ (fun s=>A.D.length s/d)
    (maskedGain main (binValue Finset.univ ((2*a-1)/2) A.D.t bin))
  intro hne Cs K C0 hCs hK hC0 hcard hscalar hupper
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hU0 : 0 < U := zero_lt_one.trans hclass.1
  have hd0 : 0 < d := (show 0 < d by norm_num [dm] at hd; linarith)
  have hδ : 0 < 2*a-1 := by linarith
  have hsub : rows' ⊆ rows := Finset.filter_subset _ _
  have hY : U^(Geometry.y/d)=Z^Geometry.y := by
    rw [hUZ,←Real.rpow_mul hZ0.le,mul_div_cancel₀ _ hd0.ne']
  have hcount1 : 1 ≤ K*C0*Z^(3*A.D.t) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK hC0)
      (Real.one_le_rpow hZ.le (by have := A.D.t_pos;positivity))
  have hb := hclass.2 Z d hZ (by linarith [hd]) (hdmax.trans htop) hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow
    hdis hη Pbase bin hne (Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.envelope A.D.momentKappa (2*a-1) (q/(2*a-1))+sigma)
    (K*C0*Z^(3*A.D.t)) hcount1 hcard hupper
  have heq (u:FreeRow) (hu:u∈rows') := errorLabelNumerator_eq_packet A.F.S A.F.exclusions (4*A.D.e) A.F.first η u
    (hrow u (hsub hu)) J (sourcePrimePool A.F Z) (fun s=>source_prime_pool_outside A.F Z s) hdis hη hQ
    (fun _=>A.F.W) (fun s=>Z^(A.D.length s)) x z (by rw [hx];linarith [A.D.e_pos]) hz.ge
    (by rw [hx];linarith [A.D.e_pos]) A.F.W 1 2 (by norm_num) A.F.complex_support (A.F.W.smooth ⊤)
    (Z^Geometry.y) (Real.rpow_pos_of_pos hZ0 _)
  have hlabel : (∑u∈rows',‖errorLabelNumerator A.F.S A.F.exclusions η u J (sourcePrimePool A.F Z)
      (fun s=>source_prime_pool_outside A.F Z s) (fun _=>A.F.W) (fun s=>Z^(A.D.length s)) x z A.F.W (Z^Geometry.y)*
      (∏s∈main,Q u s)‖)  ≤
    C*(K*C0*Z^(3*A.D.t))*(1+height)^degree*(U^(Geometry.y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(A.D.length s.val))^(-(4/25:ℝ)))*
      U^(A.D.t+q*(Geometry.ell/d)-q*Selection.zeroCapacity S.cost d/2+
        (3*(Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.envelope A.D.momentKappa (2*a-1) (q/(2*a-1))+sigma)+1+A.D.t+affineError+A.D.t)/4+
        (2*a-1)*Cycle25.sourceMesh A.D.t/4+(2*a-1)*(A.D.t+A.D.t)/2+A.D.t*(Geometry.ell/d)) := by
    convert hb using 1
    calc
      _ = ∑i:rows',‖errorLabelNumerator A.F.S A.F.exclusions η i.val J (sourcePrimePool A.F Z)
          (fun s=>source_prime_pool_outside A.F Z s) (fun _=>A.F.W) (fun s=>Z^(A.D.length s)) x z A.F.W (Z^Geometry.y)*
          (∏s∈main,Q i.val s)‖ := (Finset.sum_coe_sort rows' _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [heq i.val i.property,hY]
  let scalarFront := Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*U^(2*eps)*
    U^(-(17/50:ℝ))*Z^((17/25)*A.D.t)
  have hA : 0 ≤ scalarFront := by dsimp only [scalarFront];positivity
  have hphysical := source_mask_physical_front A.F η rows' J Z hZ0 x z hz (Z^Geometry.y) hS scalarFront _ hA hscalar hlabel
  have hselection := class_main_selection A S.cost Z d 0 (2*a-1) hZ ⟨by linarith [hd],hdmax.trans dp_lt_one.le⟩ hδ.le z rows main bin hne
  have hq0 : 0 ≤ q := hselection.1
  have hqmax : q ≤ (2*a-1)/2 := hselection.2.1
  have he := Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Scalar.source_packet_multiplicative_identity Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.admittedBranches J A.D.length A.D.slots_sum Z A.D.momentKappa d
    (newCapacity d) (2*a-1) q (C*K*C0*((1+height)^degree)) (physicalLoss A.D eps sigma affineError)
    hZ0 hd0.ne' hδ.ne'
  have hcapscale : newCapacity d/d=Selection.zeroCapacity S.cost d := by
    apply (div_eq_iff hd0.ne').mpr
    simpa only [mul_comm] using (scaled_capacity (line := line) d hd0).symm
  rw [hcapscale] at he
  dsimp [physicalLoss] at he
  have hcollapse : scalarFront*Z^(-(4/25:ℝ)*(∑j:{i:Fin A.D.N//i ∉ J},A.D.length j.val))*
      (C*(K*C0*Z^(3*A.D.t))*(1+height)^degree*(U^(Geometry.y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(A.D.length s.val))^(-(4/25:ℝ)))*
      U^(A.D.t+q*(Geometry.ell/d)-q*Selection.zeroCapacity S.cost d/2+
        (3*(Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.envelope A.D.momentKappa (2*a-1) (q/(2*a-1))+sigma)+1+A.D.t+affineError+A.D.t)/4+
        (2*a-1)*Cycle25.sourceMesh A.D.t/4+(2*a-1)*(A.D.t+A.D.t)/2+A.D.t*(Geometry.ell/d))) =
      (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*(1+height)^degree*
        Z^(numeratorExponent Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.admittedBranches A.D.momentKappa d (newCapacity d) (2*a-1) (q/(2*a-1))+
          weightedSourceLoss d (2*a-1) (physicalLoss A.D eps sigma affineError)) := by
    dsimp only [scalarFront]
    rw [hUZ]
    calc
      _ = (Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps))*
          (((Z^d)^(2*eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*A.D.t)*
            Z^(-(4/25:ℝ)*(∑j:{i:Fin A.D.N//i ∉ J},A.D.length j.val)))*
          (C*(K*C0*Z^(3*A.D.t))*(1+height)^degree*((Z^d)^(Geometry.y/d))^(-(1/2:ℝ))*
            (∏s:J,(Z^(A.D.length s.val))^(-(4/25:ℝ)))*
            (Z^d)^(A.D.t+q*(Geometry.ell/d)-q*Selection.zeroCapacity S.cost d/2+
              (3*(Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.envelope A.D.momentKappa (2*a-1) (q/(2*a-1))+sigma)+1+A.D.t+affineError+A.D.t)/4+
              (2*a-1)*Cycle25.sourceMesh A.D.t/4+(2*a-1)*(A.D.t+A.D.t)/2+A.D.t*(Geometry.ell/d)))) := by ring
      _ = _ := by
        have hex : (2*a-1)*(Cycle25.sourceMesh A.D.t+4*A.D.t)/4 =
          (2*a-1)*Cycle25.sourceMesh A.D.t/4+(2*a-1)*(A.D.t+A.D.t)/2 := by ring
        rw [hex] at he
        have hat : (Finset.univ : Finset J)=J.attach := rfl
        rw [←hat] at he
        dsimp only [physicalLoss]
        simp only [add_zero,zero_div,add_assoc] at he
        convert congrArg
          (fun r : ℝ => (Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps))*r) he using 1 <;> (try dsimp only [Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.envelope]) <;> ring
  have hphysical' := hphysical.trans_eq hcollapse
  have hheightpow : (1+height)^degree  ≤  (3+height)^(degree:ℝ) := by
    rw [Real.rpow_natCast]
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hcert := physical_packet_with_fee Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.admittedBranches A.D eps sigma affineError d a q (newCapacity d) S.fee hgap S.fee_pos hkap heps.le hsigma haff.le hbudget ⟨by linarith [hd],hdmax.trans dp_lt_one.le⟩ ha hatop ⟨hq0,hqmax⟩ (S.new_rows ⟨hd,hdmax⟩ (by constructor <;> linarith) ⟨div_nonneg hq0 hδ.le,(div_le_iff₀ hδ).mpr (by linarith)⟩)
  apply hphysical'.trans
  calc
    _  ≤  (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*(3+height)^(degree:ℝ)*
        Z^(Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly.signal HeckeZeroSupremum.beta-sourceReserve-(HeckeZeroSupremum.beta-theta)/2-A.D.t-kernelExponent a A.D.e) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hheightpow (by positivity)
      · exact Real.rpow_le_rpow_of_exponent_le hZ.le hcert
      · positivity
      · positivity
    _ = _ := by rw [Real.rpow_add (by linarith : 0 < 3+height) (degree:ℝ) (2*eps)];ring


end Qrh.TwoSlot.AnchorContinuum.PositiveTransport

#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.source_mask_amplitude_class
