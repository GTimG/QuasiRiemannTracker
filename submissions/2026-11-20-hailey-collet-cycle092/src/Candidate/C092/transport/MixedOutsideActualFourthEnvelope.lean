/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Entire original error packets on actual selected native-direct cell slices. -/
import Candidate.C092.transport.MixedOutsideActualFourthPacket
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

/-- Polynomial count envelope. The fixed Cc includes the original count
constant (for example 192*Cc); no row, mask or phase class is discarded. -/
def outsideCountEnvelope (Cc : ℝ) (Jc : ℕ) (Z d τ : ℝ) (i : ℕ) : ℝ :=
  max 1 Cc*(1+nativeHeight Z d τ i)^Jc

lemma outside_count_envelope_one (Cc : ℝ) (Jc : ℕ) (Z d τ : ℝ) (i : ℕ) (hZ : 0 ≤ Z) :
    1 ≤ outsideCountEnvelope Cc Jc Z d τ i := by
  have hH : 0 ≤ nativeHeight Z d τ i := by unfold nativeHeight;positivity
  exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ (by linarith))

/-- Full original phase alphabet and all masks absorbed into one fixed height
polynomial. Count logarithms, if any, belong to the supplied count reserve;
this lifting introduces no extra U-power loss. -/
theorem outside_prefactors_polynomial (D : BaselineData)
    (Cc : ℝ) (Jc : ℕ) (degree : Finset (Fin D.N)→ℕ) (C : Finset (Fin D.N)→ℝ)
    (hC : ∀ J,0 < C J) :
    ∃ m : ℕ,∃ C0 : ℝ,0 < C0 ∧ ∀ Z d a τ : ℝ,1 ≤ Z → d ≤ 7/8 → a ≤ 7/8 → 0 ≤ τ → ∀ i : ℕ,
    (Nat.card (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t):ℝ)*
      (∑ J∈Finset.univ.powerset,outsideMaskWeight D J (outsideCountEnvelope Cc Jc Z d τ i)
        (C J) (degree J) Z d τ i) ≤
    C0*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell) := by
  let B := phaseCardBound D
  let m : ℕ := Jc+∑ J : Finset (Fin D.N),degree J
  let S : ℝ := ∑ J : Finset (Fin D.N),C J
  let C0 : ℝ := (1+B)*S*max 1 Cc*(2*Real.pi+2)^m
  have hB : 0 ≤ B := by dsimp [B,phaseCardBound];positivity
  have hS : 0 < S := Finset.sum_pos (fun J _=>hC J) Finset.univ_nonempty
  have hCc : 0 < max 1 Cc := zero_lt_one.trans_le (le_max_left _ _)
  have hC0 : 0 < C0 := by dsimp [C0];positivity
  refine ⟨m,C0,hC0,?_⟩
  intro Z d a τ hZ hd ha hτ i
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  let H := nativeHeight Z d τ i
  let T : ℝ := 3+(3*i+1:ℕ)*Z^τ
  let bc : ℝ := Nat.card (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t)
  let front := (Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)
  have hbc : bc ≤ B := phase_card_le D a ha
  have hbc0 : 0 ≤ bc := by dsimp [bc];positivity
  have hH : 0 ≤ H := by dsimp [H,nativeHeight];positivity
  have hH1 : 1 ≤ 1+H := by linarith
  have hf : 0 ≤ front := by dsimp [front];positivity
  have hm (J : Finset (Fin D.N)) : Jc+degree J ≤ m := by
    exact Nat.add_le_add_left (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ J)) _
  have hheight : (1+H)^m ≤ (2*Real.pi+2)^m*T^m := by
    rw [←mul_pow]
    exact pow_le_pow_left₀ (by positivity) (nativeHeight_le Z d τ i hZ hd hτ) _
  have hmask (J : Finset (Fin D.N)) :
      outsideMaskWeight D J (outsideCountEnvelope Cc Jc Z d τ i) (C J) (degree J) Z d τ i ≤
      C J*max 1 Cc*(2*Real.pi+2)^m*T^m*front := by
    have he : outsideMaskWeight D J (outsideCountEnvelope Cc Jc Z d τ i) (C J) (degree J) Z d τ i =
        C J*max 1 Cc*(1+H)^(Jc+degree J)*front := by
      dsimp only [outsideMaskWeight,outsideCountEnvelope,front,H]
      rw [←prime_front_identity D J Z hZ0,pow_add]
      ring
    rw [he]
    calc
      _ ≤ C J*max 1 Cc*(1+H)^m*front := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH1 (hm J)) (mul_nonneg (hC J).le hCc.le)) hf
      _ ≤ (C J*max 1 Cc)*((2*Real.pi+2)^m*T^m)*front :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hheight (mul_nonneg (hC J).le hCc.le)) hf
      _ = _ := by ring
  have hsum : (∑ J∈Finset.univ.powerset,outsideMaskWeight D J (outsideCountEnvelope Cc Jc Z d τ i)
      (C J) (degree J) Z d τ i) ≤ S*max 1 Cc*(2*Real.pi+2)^m*T^m*front := by
    calc
      _ ≤ ∑ J∈Finset.univ.powerset,C J*max 1 Cc*(2*Real.pi+2)^m*T^m*front := Finset.sum_le_sum (fun J _=>hmask J)
      _ = _ := by simp only [Finset.powerset_univ];rw [←Finset.sum_mul,←Finset.sum_mul,←Finset.sum_mul,←Finset.sum_mul]
  calc
    _ ≤ bc*(S*max 1 Cc*(2*Real.pi+2)^m*T^m*front) := mul_le_mul_of_nonneg_left hsum hbc0
    _ ≤ (1+B)*(S*max 1 Cc*(2*Real.pi+2)^m*T^m*front) := by
      apply mul_le_mul_of_nonneg_right (hbc.trans (by linarith))
      positivity
    _ = _ := by dsimp only [C0,front,T];ring
end QRH.Cycle092.PacketJoin
#print axioms QRH.Cycle092.PacketJoin.outside_prefactors_polynomial
