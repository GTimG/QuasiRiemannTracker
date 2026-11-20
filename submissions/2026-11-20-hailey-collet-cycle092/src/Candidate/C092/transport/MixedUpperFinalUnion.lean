/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact original packet summation over true source-bank common classes. -/
import Candidate.C092.transport.MixedUpperFinalActualBanks
import Candidate.C092.transport.MixedUpperFinalBankCost
import Candidate.C092.transport.PacketJoinPhaseSum
set_option autoImplicit false
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor QRH.Cycle092.MediumWitness
open QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

lemma packet_empty (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z : ℝ) (x z : ℂ) (Y : ℝ) : packetNorm D F ∅ η Z x z Y=0 := by
  simp [packetNorm]

lemma CellBank.packet_le_common (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z d a : ℝ) (rows : Finset FreeRow) (z : ℂ)
    (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t)
    (t₀ γ τ : ℝ) (i : ℕ) (B : CellBank D F η Z d a rows z bin t₀ γ τ i)
    (P : TransportParameters D) (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 7/8)
    (x : ℂ) (Y A : ℝ) (hA : 0 ≤ A)
    (hclass : ∀σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)),
      ((B.layout P hd hdhi).common σ).Nonempty →
        packetNorm D F ((B.layout P hd hdhi).common σ) η Z x z Y ≤ A) :
    packetNorm D F (amplitudeCell D F Z d a rows (fun _=>z) bin) η Z x z Y ≤
      (Fintype.card (Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d))):ℝ)*A := by
  rw [B.packet_partition P hd hdhi x Y]
  calc
    _ ≤ ∑σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)),A := by
      apply Finset.sum_le_sum
      intro σ _
      by_cases hne:((B.layout P hd hdhi).common σ).Nonempty
      · exact hclass σ hne
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne,packet_empty]
        exact hA
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

/-- This finite combiner uses genuine source banks already constructed on the
actual nonempty cells. All original masks and original norm weights remain
inside each common packet. No product of row counts is formed. -/
theorem phase_packets_le_common (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z d a : ℝ) (rows : Finset FreeRow) (z : ℂ)
    (P : TransportParameters D) (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 7/8) (ha : a ≤ 7/8)
    (τ : ℝ) (i : ℕ) (x : ℂ) (Y A : ℝ) (hA : 0 ≤ A)
    (bins : Finset (BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t))
    (t₀ γ : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t→ℝ)
    (banks : ∀bin∈bins,∀hne : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty,
      CellBank D F η Z d a rows z bin (t₀ bin) (γ bin) τ i)
    (hclass : ∀bin hb hne,∀σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)),
      (((banks bin hb hne).layout P hd hdhi).common σ).Nonempty →
        packetNorm D F (((banks bin hb hne).layout P hd hdhi).common σ) η Z x z Y ≤ A) :
    (∑bin∈bins,packetNorm D F (amplitudeCell D F Z d a rows (fun _=>z) bin) η Z x z Y) ≤
      QRH.Cycle092.PacketJoin.phaseCardBound D*
        (Fintype.card (Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d))):ℝ)*A := by
  let card:ℝ:=Fintype.card (Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)))
  have hcard:0 ≤ card:=by dsimp [card];positivity
  calc
    _ ≤ ∑bin∈bins,card*A := by
      apply Finset.sum_le_sum
      intro bin hb
      by_cases hne:(amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty
      · exact (banks bin hb hne).packet_le_common D F η Z d a rows z bin (t₀ bin) (γ bin) τ i
          P hd hdhi x Y A hA (hclass bin hb hne)
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne,packet_empty]
        exact mul_nonneg hcard hA
    _ = (bins.card:ℝ)*card*A := by simp [mul_assoc]
    _ ≤ _ := by
      have hb:(bins.card:ℝ) ≤ QRH.Cycle092.PacketJoin.phaseCardBound D:=
        (by exact_mod_cast Finset.card_le_univ bins : (bins.card:ℝ) ≤
          (Fintype.card (BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t):ℝ)).trans
          (by simpa only [Nat.card_eq_fintype_card] using QRH.Cycle092.PacketJoin.phase_card_le D a ha)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hcard) hA

lemma final_power_add_loss_le (a d source fee strong target loss : ℝ) (hd : 0<d)
    (hgap : d*loss ≤ target-strong) :
    finalPower a d source fee strong+loss ≤ finalPower a d source fee target := by
  have he:finalPower a d source fee target=
      finalPower a d source fee strong+(target-strong)/d:=by unfold finalPower;ring
  rw [he]
  have hl : loss ≤ (target-strong)/d := (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hgap)
  exact add_le_add_right hl _

#print axioms CellBank.packet_le_common
#print axioms phase_packets_le_common
#print axioms final_power_add_loss_le
end
end QRH.Cycle092.MixedUpperFinal
