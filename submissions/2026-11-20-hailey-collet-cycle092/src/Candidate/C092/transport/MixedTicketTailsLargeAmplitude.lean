/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual error-label packet on its exact original full amplitude subpartition.
Adapted from Collet/Gao AmplitudeClass, inherited OpenAI/Levy provenance retained. -/
import Candidate.C092.transport.PacketJoinSelection
import Candidate.C092.transport.MixedTicketTailsLargeSource
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped Classical BigOperators ContDiff
open Filter
open OAI OAI.SevenEighths QRH.Record12518109Count
open ProbeRowRadicalConductor
open ProbePhysical HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open QRH.Cycle092.PacketJoin
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Cycle25.Weighted.Numerator Cycle25.Numerator Cycle25DetectorRowCount
namespace QRH.Cycle092.MixedTicketTails
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- Complete original coefficient packet on a literal amplitude class. Selected
products and full complementary products are proved from the real phase bins;
the original full row count remains a cardinality input, supplied by Native. -/
theorem q_large_packet_amplitude_class
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (affineError : ℝ) (haff : 0 < affineError) :
    ∃ mesh : ℝ, 0 < mesh ∧ ∀ (D : BaselineData) (F : BaselineSourceData D),
    (∀ j,D.length j ≤ mesh/200) →
    (∀ j,D.length j ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)/200) →
    (∀ j,D.length j ≤ Cycle25.sourceMesh D.t/200) →
    2*HeckeZeroSupremum.beta-1 ≤ D.momentKappa → ∀ J : Finset (Fin D.N),
    ∃degree:ℕ,∃C:ℝ,0< C ∧ ∀ᶠU:ℝ in atTop,
      1< U ∧ ∀(Z d:ℝ),1< Z  →  (1/2:ℝ) ≤ d  →  d ≤ 7/8  →  U=Z^d  → 
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
      rows'.Nonempty  →  ∀ (data : ∀i:rows',PhysicalReflectionData F.S F.exclusions.prime i.val) (vcut : ℝ), ∀R Ccount:ℝ,1 ≤ Ccount  →  (rows'.card:ℝ) ≤ Ccount*U^R  → 
      (∀u∈rows',∀s,‖Q u s‖ ≤ (Z^(D.length s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  → 
      (∑i:rows',‖largeLabelPolynomialPacket F.S F.exclusions η i.val
        (fun s:J=>sourcePrimePool F Z s.val) (fun s=>source_prime_pool_outside F Z s.val)
        (fun _=>F.W) (fun s=>Z^(D.length s.val)) x z F.W (U^(Geometry.y/d)) (data i).combinedConductor (fixedConductorConstant F.S) U vcut*(∏s∈main,Q i.val s)‖)  ≤ 
        C*Ccount*(1+height)^degree*(U^(Geometry.y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
          U^(D.t+q*(Geometry.ell/d)-q*Physical.Selection.zeroCapacity Geometry.y Cycle090.sourceCost d/2+
            (3*R+1+D.t+affineError+D.t)/4+(2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(2*D.t+D.t)/4-(2*a-1)*vcut/4+D.t*(Geometry.ell/d)) := by
  obtain ⟨mesh,hmesh,hlabel⟩ := q_large_label_packet_selected_bin hbeta affineError haff
  refine ⟨mesh,hmesh,?_⟩
  intro D F hfineAffine hfineCommon hfine hkbeta J
  obtain ⟨degree,C,hC,hbin⟩ := hlabel D F hfineAffine hfineCommon hkbeta J
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hbin] with U hbin
  refine ⟨hbin.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow hdis hη Pbase bin
  dsimp only
  let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
  let main := (Finset.univ:Finset (Fin D.N)) \ J
  let q := weightedMean Finset.univ (fun s=>D.length s/d)
    (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
  intro hne data vcut R Ccount hCc hcard hupper
  have hδ : 0 ≤ 2*a-1 := by linarith
  have hδtop : 2*a-1 ≤ 3/4 := by linarith
  have hU0 : 0< U := zero_lt_one.trans hbin.1
  have hsub : rows' ⊆ rows := Finset.filter_subset _ _
  have ht : 0 < D.t := D.t_pos
  have hselection (j:ℕ) := q_class_main_selection D F hfine Z d (2*((j:ℝ)*D.t+D.t+D.t)) (2*a-1)
    hZ ⟨hd,hdmax⟩ (by positivity) hδ z rows main bin hne
  have hq0 : 0 ≤ q := (hselection 0).1
  have hqtop : q ≤ (2*a-1)/2 := (hselection 0).2.1
  have hchoices (j:ℕ) : ∃selected:Finset (Fin D.N),selected ⊆ main ∧
      (∑s∈selected,D.length s/d) ≤ Physical.Selection.scheduledCapacity Geometry.y Cycle090.sourceCost d (2*((j:ℝ)*D.t+D.t+D.t)) ∧
      ∀u∈rows',
        (Z^d)^(2*q*Physical.Selection.scheduledCapacity Geometry.y Cycle090.sourceCost d (2*((j:ℝ)*D.t+D.t+D.t))-
          (2*a-1)*Cycle25.sourceMesh D.t) ≤ ‖∏s∈selected,Q u s‖^2 ∧
        ((∀s,‖Q u s‖ ≤ (Z^(D.length s))^
          (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  → 
          ‖∏s∈main,Q u s‖ ≤ (Z^d)^(q*(Geometry.ell/d)+D.t*(Geometry.ell/d))) := (hselection j).2.2
  choose selected hselectedMain hcapacity hselected using hchoices
  let Pmain (i:rows') := ∏s∈main,Q i.val s
  let Pnorm (i:rows') := Pmain i / (((U^(D.t*(Geometry.ell/d)):ℝ)):ℂ)
  have hfull (i:rows') : ‖Pnorm i‖ ≤ U^(q*(Geometry.ell/d)) := by
    apply upper_bin_normalized (Pmain i) U (q*(Geometry.ell/d)) (D.t*(Geometry.ell/d)) hU0
    rw [hUZ]
    exact (hselected 0 i.val i.property).2 (hupper i.val i.property)
  have hcap (j:ℕ) (_:j∈Finset.range (coefficientBoxCount D.t+1)) :
      (∑s∈selected j,D.length s/d)  ≤  Physical.Selection.scheduledCapacity Geometry.y Cycle090.sourceCost d (2*((j:ℝ)*D.t+D.t+D.t)) := by
    exact hcapacity j
  have hlow (j:ℕ) (_:j∈Finset.range (coefficientBoxCount D.t+1)) (i:rows') :
      U^(q*Physical.Selection.scheduledCapacity Geometry.y Cycle090.sourceCost d (2*((j:ℝ)*D.t+D.t+D.t))-
        ((2*a-1)*Cycle25.sourceMesh D.t/2))  ≤  ‖∏s∈selected j,Q i.val s‖ := by
    rw [hUZ]
    exact squared_selected_lower (Z^d) q _ (2*a-1) (Cycle25.sourceMesh D.t) _
      (by rw [←hUZ];exact hU0) (hselected j i.val i.property).1
  have hcrude (j:ℕ) (_:j∈Finset.range (coefficientBoxCount D.t+1)) (i:rows') :
      ‖∏s∈selected j,Q i.val s‖ ≤ U := by
    rw [hUZ]
    exact q_selected_product_crude D Z d (2*a-1) hZ hd hδ hδtop (selected j) (Q i.val)
      (hupper i.val i.property)
  have hb := hbin.2 Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim
    rows' (fun u hu=>hrows u (hsub hu)) (fun u hu=>hrow u (hsub hu)) hdis hη Pbase data vcut selected Pnorm
    q R ((2*a-1)*Cycle25.sourceMesh D.t/2) Ccount hq0 hqtop hCc hcard hfull hcap hlow hcrude
  have hrestore := restore_upper_bin_loss Finset.univ
    (fun i:rows'=>largeLabelPolynomialPacket F.S F.exclusions η i.val
      (fun s:J=>sourcePrimePool F Z s.val) (fun s=>source_prime_pool_outside F Z s.val)
      (fun _=>F.W) (fun s=>Z^(D.length s.val)) x z F.W (U^(Geometry.y/d)) (data i).combinedConductor (fixedConductorConstant F.S) U vcut) Pmain U (D.t*(Geometry.ell/d))
    (D.t+q*(Geometry.ell/d)-q*Physical.Selection.zeroCapacity Geometry.y Cycle090.sourceCost d/2+
      (3*R+1+D.t+affineError+D.t)/4+((2*a-1)*Cycle25.sourceMesh D.t/2)/2+(2*a-1)*(2*D.t+D.t)/4-(2*a-1)*vcut/4)
    (C*Ccount*(1+height)^degree*(U^(Geometry.y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ))))
    hU0 hb
  have he : ((2*a-1)*Cycle25.sourceMesh D.t/2)/2=(2*a-1)*Cycle25.sourceMesh D.t/4 := by ring
  simpa only [he,Pmain] using hrestore



end QRH.Cycle092.MixedTicketTails
#print axioms QRH.Cycle092.MixedTicketTails.q_large_packet_amplitude_class
