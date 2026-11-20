/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original full-class mean controls every error mask without changing the count. -/
import Candidate.C092.transport.PacketJoinAmplitude
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open ProbePhysical HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Cycle25.Numerator Cycle25DetectorRowCount QRH.Record12518109Count
namespace QRH.Cycle092.PacketJoin
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- Error masks zero only the gain used for selecting main prime factors.
The original native count continues to use the full class mean. -/
theorem masked_class_mean_le (D : BaselineData) (F : BaselineSourceData D)
    (Z d δ : ℝ) (hd : 0 < d) (hδ : 0 ≤ δ) (z : ℂ) (rows : Finset FreeRow)
    (main : Finset (Fin D.N))
    (bin : BinLabel (Finset.univ : Finset (Fin D.N)) (δ/2) D.t)
    (hne : (amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=>D.length j/d)
      (fun u j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) z) bin).Nonempty) :
    weightedMean Finset.univ (fun j=>D.length j/d) (maskedGain main (binValue Finset.univ (δ/2) D.t bin)) ≤
      classMean Finset.univ (δ/2) D.t (fun j=>D.length j/d) bin := by
  obtain ⟨u,hu⟩ := hne
  have hg (j : Fin D.N) : 0 ≤ binValue Finset.univ (δ/2) D.t bin j := by
    have he := amplitude_class_value rows Finset.univ (Z^d) (δ/2) D.t D.t_pos
      (fun j=>D.length j/d)
      (fun u j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) z)
      bin u hu j (Finset.mem_univ _)
    rw [←he]
    exact (HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)).1
  unfold classMean weightedMean
  apply div_le_div_of_nonneg_right _ (Finset.sum_nonneg (fun j _ => (div_pos (D.slots_pos j) hd).le))
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (div_pos (D.slots_pos j) hd).le
  dsimp only [maskedGain]
  split_ifs
  · exact le_rfl
  · exact hg j

/-- At these genuine direct conductors, decreasing the main-factor mean
improves the packet power while leaving the original full-class count intact. -/
theorem packet_mean_power_mono {d qMain qFull : ℝ}
    (hd : 0 < d) (hdhi : d ≤ 7/8) (hq : qMain ≤ qFull) :
    qMain*(Geometry.ell/d)-qMain*Physical.Selection.zeroCapacity Geometry.y Cycle090.sourceCost d/2 ≤
      qFull*(Geometry.ell/d)-qFull*Physical.Selection.zeroCapacity Geometry.y Cycle090.sourceCost d/2 := by
  have he : (1/10:ℝ) ≤ Geometry.ell/d := (le_div_iff₀ hd).mpr (by
    linarith [Geometry.sixth_lt_ell])
  have hc : Physical.Selection.zeroCapacity Geometry.y Cycle090.sourceCost d ≤ Cycle090.physicalCap :=
    min_le_left _ _
  have hp : 0 ≤ Geometry.ell/d-Physical.Selection.zeroCapacity Geometry.y Cycle090.sourceCost d/2 := by
    norm_num [Cycle090.physicalCap] at hc
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hq hp]

end QRH.Cycle092.PacketJoin
#print axioms QRH.Cycle092.PacketJoin.masked_class_mean_le
#print axioms QRH.Cycle092.PacketJoin.packet_mean_power_mono
