/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Entire original error packets on actual selected native-direct cell slices. -/
import Candidate.C092.transport.PacketJoinAmplitude
import Candidate.C092.transport.PacketJoinMean
import Candidate.C092.transport.PacketJoinActual
import Candidate.C092.transport.PacketJoinEnvelope

import Candidate.C092.transport.PacketFinalPower
import Candidate.C092.transport.Direct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths
open ProbePhysical HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorBatch
open HeckeDetectorWitnessRows HeckeDetectorRawFiber
open Cycle25.Weighted.Numerator Cycle25.Numerator
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor
open QRH.Cycle092.Direct QRH.Cycle092.DirectCount
namespace QRH.Cycle092.PacketJoin
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- The count is the actual cardinality of the SAME common row subset. -/
def outsideMaskWeight (D : BaselineData) (J : Finset (Fin D.N))
    (Ccount C : ℝ) (degree : ℕ) (Z d τ : ℝ) (i : ℕ) : ℝ :=
  C*Ccount*(1+nativeHeight Z d τ i)^degree*(Z^Geometry.y)^(-(1/2:ℝ))*
    mainFront D J Z*(∏ s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))

/-- Restricting a literal amplitude class preserves its ORIGINAL phase bin. -/
lemma amplitudeRows_of_subset (D : BaselineData) (F : BaselineSourceData D)
    (Z d a : ℝ) (rows common : Finset FreeRow) (z : ℂ)
    (bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t)
    (hsub : common ⊆ amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos
      (fun s=>D.length s/d)
      (fun u s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z) bin) :
    amplitudeRows common Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos
      (fun s=>D.length s/d)
      (fun u s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z) bin = common := by
  apply Finset.filter_eq_self.mpr
  intro u hu
  exact (Finset.mem_filter.mp (hsub hu)).2

/-- Genuine original-mask fourth/Hölder estimate from an arbitrary count at R
on the same actual common rows. The source/coefficient moment and the main
selection are proved internally, with the ORIGINAL whole class mean. -/
theorem actual_common_mask_bound (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (affineError : ℝ) (haff : 0 < affineError) :
    ∃ mp : ℝ,0 < mp ∧ ∀ (D : BaselineData) (F : BaselineSourceData D),
    (∀ s,D.length s ≤ mp/200) →
    (∀ s,D.length s ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)/200) →
    (∀ s,D.length s ≤ Cycle25.sourceMesh D.t/200) →
    2*HeckeZeroSupremum.beta-1 ≤ D.momentKappa →
    ∀ J : Finset (Fin D.N),∃ degree : ℕ,∃ C : ℝ,0 < C ∧
    ∀ (P : TransportParameters D) (padding τ : ℝ),0 < τ →
    4*τ < (1/200:ℝ)*D.cost → padding+2*D.t ≤ 1/10000000000 →
    ∀ (n : ℕ) (η : Character),∀ᶠ Z : ℝ in atTop,1 < Z ∧
    ∀ idx grid : FreeRow→ℕ,selected D F padding τ n η Z idx grid →
    ∀ k∈smallDyadicIndices (Z^(Geometry.h+padding)),∀ i∈Finset.range (n+1),∀ j : ℕ,
    (cellRows D F padding Z idx grid k i j).Nonempty →
    let d := sourceDyadConductor Z D.t k
    let a : ℝ := 51/100+D.e*j
    let rows := cellRows D F padding Z idx grid k i j
    (1/2:ℝ) ≤ d → ∀ (x z : ℂ),x.re=a+16*D.e → z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ →
    ∀ bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
    ∀ common : Finset FreeRow,
    common ⊆ MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin → common.Nonempty →
    ∀ R Ccount : ℝ,1 ≤ Ccount → (common.card:ℝ) ≤ Ccount*(Z^d)^R →
    maskNorm D F J common η Z x z (Z^Geometry.y) ≤
      outsideMaskWeight D J Ccount C degree Z d τ i*
        (Z^d)^(packetPower a
          (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))
          R d Cycle090.sourceCost (nativeMoment D affineError) (nativeMass D a d)) := by
  obtain ⟨mp,hmp,hpacket⟩ := q_packet_amplitude_class hβ affineError haff
  refine ⟨mp,hmp,?_⟩
  intro D F hfPacket hfCommon hfSource hkβ J
  obtain ⟨degree,C,hC,hpacket⟩ := hpacket D F hfPacket hfCommon hfSource hkβ J
  obtain ⟨U0,hU0⟩ := eventually_atTop.mp hpacket
  have hscaled : ∀ᶠ Z : ℝ in atTop,∀ d : ℝ,(1/2:ℝ) ≤ d → U0 ≤ Z^d := by
    filter_upwards [(tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).eventually
      (eventually_ge_atTop U0),eventually_ge_atTop (1:ℝ)] with Z hZ hZone
    intro d hd
    exact hZ.trans (Real.rpow_le_rpow_of_exponent_le hZone hd)
  refine ⟨degree,C,hC,?_⟩
  intro P padding τ hτ hheight hpad n η
  filter_upwards [hscaled,actual_cell_native_data D F P padding τ hτ hheight hpad n η,
    source_prime_reconstruction_geometry F η,SelectedFloorEstimate.source_pools_nonempty D F] with Z hscaled hc hg hpools
  refine ⟨hc.1,?_⟩
  intro idx grid hs k hk i hi j hn
  dsimp only
  intro hd x z hx hz him bin common hsub hne R Ccount hCc hcard
  let d := sourceDyadConductor Z D.t k
  let a : ℝ := 51/100+D.e*j
  let rows := cellRows D F padding Z idx grid k i j
  have hd0 : 0 < d := by dsimp [d];linarith
  have hZ : 0 < Z := zero_lt_one.trans hc.1
  obtain ⟨hdhi,ha,hahi,hrow,hrest⟩ := hc.2 idx grid hs k hk i hi j hn
  change 51/100 < a at ha
  change a ≤ 7/8 at hahi
  have heq := amplitudeCell_eq_original D F Z d a hZ hd0 rows z bin
  rw [heq] at hsub
  have hsame := amplitudeRows_of_subset D F Z d a rows common z bin hsub
  have hsubrows : common ⊆ rows := hsub.trans (Finset.filter_subset _ _)
  have hrows (u : FreeRow) (hu : u∈common) : (Z^d)^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ Z^d := by
    refine ⟨?_,(hrow u (hsubrows hu)).2.1.trans ?_⟩
    · rw [←Real.rpow_mul hZ.le]
      exact (Real.rpow_le_rpow_of_exponent_le hc.1.le (by nlinarith)).trans (hrow u (hsubrows hu)).1
    · exact Real.rpow_le_rpow_of_exponent_le hc.1.le (by linarith [D.t_pos])
  let H := nativeHeight Z d τ i
  have hH : 0 ≤ H := by dsimp [H,nativeHeight];positivity
  have himH : |z.im| ≤ H := him.trans (by dsimp [H,nativeHeight];exact le_add_of_nonneg_left (by positivity))
  have hne' : (amplitudeRows common Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d)
      (fun u s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z) bin).Nonempty := hsame.symm ▸ hne
  have hraw := (hU0 (Z^d) (hscaled d hd)).2 Z d hc.1 hd hdhi rfl η x z a H ha.le hahi hx hz hH himH
    common hrows (fun u hu=>(hrow u (hsubrows hu)).2.2) (hg.2.1 J) hg.2.2.2.1
    (fun s=>⟨(hpools s.val).choose,(hpools s.val).choose_spec⟩) bin hne' R Ccount hCc
    (hsame.symm ▸ hcard) (fun u hu s=>(hrest z hz him).1 u (hsubrows (hsame ▸ hu)) s)
  let q := classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin
  let qm := weightedMean Finset.univ (fun s=>D.length s/d)
    (Cycle25DetectorRowCount.maskedGain (Finset.univ\J) (binValue Finset.univ ((2*a-1)/2) D.t bin))
  have hmeanpower := packet_mean_power_mono hd0 hdhi
    (masked_class_mean_le D F Z d (2*a-1) hd0 (by linarith) z common (Finset.univ\J) bin hne')
  have hexp : D.t+qm*(Geometry.ell/d)-qm*Physical.Selection.zeroCapacity Geometry.y Cycle090.sourceCost d/2+
      (3*R+1+D.t+affineError+D.t)/4+(2*a-1)*Cycle25.sourceMesh D.t/4+
      (2*a-1)*(D.t+D.t)/2+D.t*(Geometry.ell/d) ≤
      D.t+q*(Geometry.ell/d)-q*Physical.Selection.zeroCapacity Geometry.y Cycle090.sourceCost d/2+
      (3*R+1+D.t+affineError+D.t)/4+(2*a-1)*Cycle25.sourceMesh D.t/4+
      (2*a-1)*(D.t+D.t)/2+D.t*(Geometry.ell/d) := by linarith only [hmeanpower]
  have hraw' := hraw.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (Real.one_le_rpow hc.1.le hd0.le) hexp) (by positivity))
  rw [hsame] at hraw'
  have hY : (Z^d)^(Geometry.y/d)=Z^Geometry.y := by
    rw [←Real.rpow_mul hZ.le,mul_div_cancel₀ _ hd0.ne']
  rw [hY] at hraw'
  have hpow : D.t+q*(Geometry.ell/d)-q*Physical.Selection.zeroCapacity Geometry.y Cycle090.sourceCost d/2+
      (3*R+1+D.t+affineError+D.t)/4+(2*a-1)*Cycle25.sourceMesh D.t/4+
      (2*a-1)*(D.t+D.t)/2+D.t*(Geometry.ell/d) =
      packetPower a (q/(2*a-1)) R d Cycle090.sourceCost (nativeMoment D affineError) (nativeMass D a d) := by
    dsimp only [packetPower,nativeMoment,nativeMass]
    have hδ : 2*a-1 ≠ 0 := by linarith
    field_simp [hδ,hd0.ne']
    <;> ring
  change _ ≤ _*(Z^d)^(D.t+q*(Geometry.ell/d)-q*Physical.Selection.zeroCapacity Geometry.y Cycle090.sourceCost d/2+
    (3*R+1+D.t+affineError+D.t)/4+(2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(Geometry.ell/d)) at hraw'
  rw [hpow] at hraw'
  have hm := mul_le_mul_of_nonneg_left hraw' (show 0 ≤ mainFront D J Z by unfold mainFront;positivity)
  convert hm using 1
  · simp only [maskNorm,errorPacket,mainProduct]
    rw [←Finset.sum_coe_sort]
  · dsimp only [outsideMaskWeight,H]
    ring
end QRH.Cycle092.PacketJoin
#print axioms QRH.Cycle092.PacketJoin.actual_common_mask_bound
