/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Full conductor range for the variable-cost physical dyad estimate. Adapted from
PR137 Combined (Sil and predecessor authors, Apache-2.0). -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveCollect
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveOldCollect
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.Combined
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped Classical BigOperators ContDiff
open Filter
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds] [scheme : Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line] [S : Schedule (line := line)]
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic OAI OAI.SevenEighths
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic QRH.Record12518109Count Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Scalar QRH.Record1252270103Return.GenericPhysical
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open QRH.Record12518109Count
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

theorem source_integrated_all_bands (A : ChosenData)
    (hgap : theta < HeckeZeroSupremum.beta)
    (hbetatop : HeckeZeroSupremum.beta ≤ 7/8)
    (hkap : A.D.momentKappa=2*HeckeZeroSupremum.beta-1)
    (hbeta : (51/100:ℝ)  ≤  HeckeZeroSupremum.beta)
    (bPhi affineError : ℝ) (haff : 0< affineError)
    (hsPhi : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ → ℂ) ⊆ Set.Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0< Ci)
    (hinput : ∀ᶠU:ℝ in atTop,affineAtFace (PositiveSource.physicalFace S.cost) A bPhi affineError U di control Ci)
    (eps sigma : ℝ) (heps : 0< eps) (hsigma : 0 ≤ sigma)
    (hbudget : 16*A.D.e+2*eps+3*sigma/4+affineError/4+8*A.D.t ≤ (HeckeZeroSupremum.beta-theta)/4)
    (htop : dp (line := line) ≤ 2*Geometry.y) :
    ∃Jw : ℝ,0  ≤  Jw ∧ ∃C : ℝ,0 < C ∧ ∀ᶠU : ℝ in atTop,
      1 < U ∧ ∀(Z d : ℝ),1 < Z  →  d0  ≤  d  →  d  ≤  dp  →  U=Z^d  →
      ∀(η : Character) (x z : ℂ) (a height : ℝ),(51/100:ℝ)  ≤  a  →  a  ≤  7/8  →
      x.re=a+16*A.D.e  →  z.re=17/50  →  0  ≤  height  →  |z.im|  ≤  height  →
      ∀rows : Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ)  ≤  rowNorm u ∧ rowNorm u  ≤  U)  →
      (∀u∈rows,(rowCharacter A.F.S A.F.exclusions.prime u).residue≠1)  →
      (∀J : Finset (Fin A.D.N),∀P : ∀i:J,sourcePrimePool A.F Z i.val,
        Function.Injective (fun i=>(P i).val))  →
      (∀P : ∀i,sourcePrimePool A.F Z i,Function.Injective (fun i=>(P i).val))  →
      (∀i P,P∈sourcePrimePool A.F Z i  →  IsCoprime P.val η.modulus)  →
      (∀i P,P∈sourcePrimePool A.F Z i  →  (4:ℝ)  ≤  P.val.absNorm)  →
      (∀i,∀P∈A.F.S,(P.absNorm:ℝ)  ≤  Z^(A.D.length i))  →
      (∀i,sourcePrimePool A.F Z i)  →
      ∀Cs K C0 : ℝ,0  ≤  Cs  →  1  ≤  K  →  1  ≤  C0  →
      let Q := fun (u : FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude
        A.F.modulus ⊤ u.val A.F.W 2 (Z^(A.D.length s)) z
      (∀J : Finset (Fin A.D.N),∀bin : BinLabel (Finset.univ:Finset (Fin A.D.N)) ((2*a-1)/2) A.D.t,
        let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) A.D.t A.D.t_pos (fun s=>A.D.length s/d) Q bin
        let q := weightedMean Finset.univ (fun s=>A.D.length s/d)
          (maskedGain (Finset.univ\J) (binValue Finset.univ ((2*a-1)/2) A.D.t bin))
        rows'.Nonempty  →  (rows'.card:ℝ)  ≤  K*C0*Z^(3*A.D.t)*
          U^(Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.envelope A.D.momentKappa (2*a-1) (q/(2*a-1))+sigma))  →
      (∀u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩*
        numeratorFreeRowScalar A.F.S A.F.exclusions A.F.maximal η u x z‖  ≤
        Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*
          U^(2*eps)*U^(-(17/50:ℝ))*Z^((17/25)*A.D.t))  →
      (∀u∈rows,∀s,‖Q u s‖  ≤  (Z^(A.D.length s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(A.D.length s)) ((2*a-1)/2) A.D.t (Q u s)+A.D.t))  →
      ‖Cycle25.Weighted.FullWContour.integratedDyadValue A.F.S A.F.exclusions A.F.maximal η rows (sourcePrimePool A.F Z)
        (fun s=>source_prime_pool_outside A.F Z s) (fun _=>A.F.W) (fun s=>Z^(A.D.length s)) A.F.W (Z^Geometry.y) x z‖  ≤
        (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^Jw*
          Z^(Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly.signal HeckeZeroSupremum.beta-sourceReserve-(HeckeZeroSupremum.beta-theta)/2-A.D.t-kernelExponent a A.D.e) := by
  obtain ⟨Jn,hJn,Cn,hCn,hn⟩ := source_integrated_amplitude_classes A hgap hbetatop hkap hbeta
    bPhi affineError haff hsPhi di control Ci hCi hinput eps sigma heps hsigma hbudget htop
  obtain ⟨Jo,hJo,Co,hCo,ho⟩ := old_source_integrated_amplitude_classes A.D hgap hbetatop hkap A.F hbeta
    eps sigma heps hsigma (by linarith [haff]) A.fine
  refine ⟨Jn+Jo,add_nonneg hJn hJo,Cn+Co,add_pos hCn hCo,?_⟩
  filter_upwards [hn,ho] with U hn ho
  refine ⟨hn.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hH him rows hrows hrow
    hdis hdisAll hη hQ hS Pbase Cs K C0 hCs hK hC0
  dsimp only
  intro hcount hscalar hupper
  by_cases hdn : dm≤ d
  · have hh := hn.2 Z d hZ hdn hdmax hUZ η x z a height ha hatop hx hz hH him rows
      hrows hrow hdis hdisAll hη hQ hS Pbase Cs K C0 hCs hK hC0 hcount hscalar hupper
    apply hh.trans
    gcongr <;> linarith
  · have hh := ho.2 Z d hZ hd (le_of_not_ge hdn) hUZ η x z a height ha hatop hx hz hH him rows
      hrows hrow hdis hdisAll hη hQ hS Pbase Cs K C0 hCs hK hC0 hcount hscalar hupper
    apply hh.trans
    gcongr <;> linarith
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport

#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.source_integrated_all_bands
