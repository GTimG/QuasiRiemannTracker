/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine natural lower-conductor packet at the current conservative contact
price. BaselineData's momentKappa equality remains untouched. -/
import Candidate.C092.transport.NaturalPacketLowClass
import Candidate.C092.transport.DirectPrices
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths
open ProbePhysical HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Record1252270103Return.Geometry
open Cycle25.Weighted.Numerator Cycle25.Numerator Cycle25DetectorRowCount
namespace QRH.Cycle092.NaturalPacketLow
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

lemma q_kappa_bounds : (7/10 : ℝ) ≤ Direct.kap ∧ Direct.kap ≤ 3/4 := by
  norm_num [Direct.kap,QRH.ContactCertificate.alphaHi]

/-- The lower-conductor consumer at the current Q contact price, including
all original coefficient tuples and its actual amplitude-class subpartition. -/
theorem q_natural_packet_amplitude_class (D:BaselineData)
    (F:BaselineSourceData D) (hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hkbeta : 2*HeckeZeroSupremum.beta-1 ≤ Direct.kap)
    (hfine:∀j,D.length j ≤ Cycle25.sourceMesh D.t/200) (J:Finset (Fin D.N)) :
    ∃degree:ℕ,∃C:ℝ,0< C ∧ ∀ᶠU:ℝ in atTop,
      1< U ∧ ∀(Z d:ℝ),1< Z  →  (1/200:ℝ) ≤ d  →  d ≤ (19/25:ℝ)  →  U=Z^d  → 
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
          U^(D.t+q*(Geometry.ell/d)-q*baseCapacity Direct.kap d/2+
            (3*R+1+D.t+D.t)/4+(2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(Geometry.ell/d)) := by
  exact old_source_packet_amplitude_class (κ := Direct.kap)
    (hκlo := q_kappa_bounds.1) (hκhi := q_kappa_bounds.2)
    D F hbeta hkbeta hfine J

end QRH.Cycle092.NaturalPacketLow
#print axioms QRH.Cycle092.NaturalPacketLow.q_natural_packet_amplitude_class
