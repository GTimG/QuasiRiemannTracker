/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Weighted dilation bins at variable physical capacity. Adapted from PR137
BinBound, FiniteBins and PacketBound (Sil, Hailey Collet, Akash Levy and
predecessor authors, Apache-2.0). The complete coefficient series and its
max-one dilation are retained. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveSelection
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.PacketBound

set_option autoImplicit false
set_option maxHeartbeats 700000
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103Return
open OAI.SevenEighths Cycle25.Numerator
variable [Geometry.Parameters]

theorem weighted_bin {ι : Type*} (rows : Finset ι) (S Q P : ι → ℂ)
    (cost d U R q L v xi ann delta loss epsilon Ccount Cmoment : ℝ)
    (hcost : 0 ≤ cost) (hU : 1 ≤ U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment)
    (hq : 0 ≤ q) (hqdelta : q ≤ delta/2) (hv : 0 ≤ v) (hxi : 0 ≤ xi) (hann : 0 ≤ ann)
    (hcard : (rows.card : ℝ) ≤ Ccount*U^R)
    (hselected : ∀ i ∈ rows,
      U^(q*Selection.scheduledCapacity cost d (2*(v+xi+ann))-loss) ≤ ‖Q i‖)
    (hfull : ∀ i ∈ rows, ‖P i‖ ≤ U^(q*L))
    (henergy : (∑ i ∈ rows, ‖S i‖^4*‖Q i‖^2) ≤ Cmoment*U^(1+epsilon)) :
    U^(-delta*v/2)*(∑ i ∈ rows, ‖S i*P i‖) ≤
      Ccount*Cmoment*U^(q*L-q*Selection.zeroCapacity cost d/2+(3*R+1+epsilon)/4+
        loss/2+delta*(xi+ann)/2-(1/500)*delta*(v+xi+ann)) := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hh := weighted_amplitude_bin rows S Q P U R (q*L)
    (q*Selection.scheduledCapacity cost d (2*(v+xi+ann))-loss) epsilon Ccount Cmoment
    hU0 hc hm hcard hselected hfull henergy
  have hdelta : 0 ≤ delta := by linarith
  have hdamp := Selection.capacity_damping (d := d) hcost
    (by positivity : 0 ≤ 2*(v+xi+ann)) hq hqdelta hdelta
  calc
    _ ≤ U^(-delta*v/2)*(Ccount*Cmoment*
        U^(q*L-(q*Selection.scheduledCapacity cost d (2*(v+xi+ann))-loss)/2+(3*R+1+epsilon)/4)) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hU0.le _)
    _ = Ccount*Cmoment*U^(-delta*v/2+q*L-
        (q*Selection.scheduledCapacity cost d (2*(v+xi+ann))-loss)/2+(3*R+1+epsilon)/4) := by
      rw [←mul_assoc,mul_comm (U^(-delta*v/2)),mul_assoc,←Real.rpow_add hU0]
      congr 2
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hU
      linarith

theorem finite_bins {ι : Type*} (rows : Finset ι) (n : ℕ)
    (S Q : ℕ → ι → ℂ) (P f : ι → ℂ)
    (cost d U R q L xi ann delta loss epsilon Ccount Cmoment M : ℝ)
    (hcost : 0 ≤ cost) (hU : 1 ≤ U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment) (hM : 0 ≤ M)
    (hq : 0 ≤ q) (hqdelta : q ≤ delta/2) (hxi : 0 ≤ xi) (hann : 0 ≤ ann)
    (hcard : (rows.card : ℝ) ≤ Ccount*U^R)
    (hsplit : ∀ i ∈ rows, f i = ∑ j ∈ Finset.range (n+1),
      ((M*U^(-delta*((j:ℝ)*xi)/2) : ℝ) : ℂ)*S j i)
    (hselected : ∀ j ∈ Finset.range (n+1), ∀ i ∈ rows,
      U^(q*Selection.scheduledCapacity cost d (2*((j:ℝ)*xi+xi+ann))-loss) ≤ ‖Q j i‖)
    (hfull : ∀ i ∈ rows, ‖P i‖ ≤ U^(q*L))
    (henergy : ∀ j ∈ Finset.range (n+1),
      (∑ i ∈ rows, ‖S j i‖^4*‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon)) :
    (∑ i ∈ rows, ‖f i*P i‖) ≤ ((n+1:ℕ):ℝ)*M*Ccount*Cmoment*
      U^(q*L-q*Selection.zeroCapacity cost d/2+(3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/2) := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hdelta : 0 ≤ delta := by linarith
  let E := q*L-q*Selection.zeroCapacity cost d/2+(3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/2
  have hj (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∑ i ∈ rows, ‖(((M*U^(-delta*((j:ℝ)*xi)/2):ℝ):ℂ)*S j i)*P i‖) ≤
      M*Ccount*Cmoment*U^E := by
    have hb := weighted_bin rows (S j) (Q j) P cost d U R q L ((j:ℝ)*xi) xi ann delta
      loss epsilon Ccount Cmoment hcost hU hc hm hq hqdelta
      (mul_nonneg (Nat.cast_nonneg _) hxi) hxi hann hcard (hselected j hj) hfull (henergy j hj)
    have hpow : U^(E-(1/500)*delta*((j:ℝ)*xi+xi+ann)) ≤ U^E :=
      Real.rpow_le_rpow_of_exponent_le hU (by
        have hv : 0 ≤ (j:ℝ)*xi+xi+ann := by positivity
        have hh := mul_nonneg hdelta hv
        dsimp only [E]
        nlinarith)
    calc
      _ = M*(U^(-delta*((j:ℝ)*xi)/2)*(∑ i ∈ rows, ‖S j i*P i‖)) := by
        rw [Finset.mul_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_assoc,norm_mul,Complex.norm_real,
          Real.norm_of_nonneg (mul_nonneg hM (Real.rpow_nonneg hU0.le _))]
        ring
      _ ≤ M*(Ccount*Cmoment*U^(E-(1/500)*delta*((j:ℝ)*xi+xi+ann))) :=
        mul_le_mul_of_nonneg_left hb hM
      _ ≤ M*(Ccount*Cmoment*U^E) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∑ i ∈ rows, ∑ j ∈ Finset.range (n+1),
        ‖(((M*U^(-delta*((j:ℝ)*xi)/2):ℝ):ℂ)*S j i)*P i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [hsplit i hi,Finset.sum_mul]
      exact norm_sum_le _ _
    _ = ∑ j ∈ Finset.range (n+1), ∑ i ∈ rows,
        ‖(((M*U^(-delta*((j:ℝ)*xi)/2):ℝ):ℂ)*S j i)*P i‖ := Finset.sum_comm
    _ ≤ ∑ j ∈ Finset.range (n+1), M*Ccount*Cmoment*U^E := Finset.sum_le_sum hj
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; dsimp only [E]; ring

/-- Complete countable coefficient series, grouped by the original max-one
dilation. No term is removed by an unsigned comparison of signed sums. -/
theorem packet_bins {ι : Type*} [Fintype ι] {α : ι → Type*}
    (base : ∀ i, α i) (A S : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ)
    (hN : ∀ i e, 0 < N i e) (Lc : ι → ℝ) (cost d U xi ann : ℝ) (n : ℕ)
    (valid : ∀ i, α i → Prop) [∀ i e, Decidable (valid i e)]
    (Q : ℕ → ι → ℂ) (P : ι → ℂ)
    (R q L delta loss epsilon Ccount Cmoment M : ℝ)
    (hcost : 0 ≤ cost) (hM : 0 < M) (hU : 1 ≤ U) (hxi : 0 ≤ xi) (hann : 0 ≤ ann)
    (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment) (hq : 0 ≤ q) (hqdelta : q ≤ delta/2)
    (hcard : (Fintype.card ι:ℝ) ≤ Ccount*U^R)
    (hzero : ∀ i e, ¬valid i e → S i e = 0)
    (hupper : ∀ i e, valid i e → max 1 (Lc i*N i e) ≤ U^((n:ℝ)*xi))
    (hseries : ∀ i, Summable (fun e => ‖A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e‖))
    (hs : ∀ i, Summable (fun e => ‖A i e‖*(N i e)^(-(1/2:ℝ))*max 1 (Lc i*N i e)^(delta/2)))
    (hmass : ∀ i, (∑' e, ‖A i e‖*(N i e)^(-(1/2:ℝ))*max 1 (Lc i*N i e)^(delta/2)) ≤ M)
    (hselected : ∀ j ∈ Finset.range (n+1), ∀ i,
      U^(q*Selection.scheduledCapacity cost d (2*((j:ℝ)*xi+xi+ann))-loss) ≤ ‖Q j i‖)
    (hfull : ∀ i, ‖P i‖ ≤ U^(q*L))
    (hselection : ∀ j ∈ Finset.range (n+1), ∀ e : ∀ i, α i,
      (∑ i, ‖if valid i (e i) ∧ dilationBox U xi n (max 1 (Lc i*N i (e i))) = j
        then S i (e i) else 0‖^4*‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon)) :
    (∑ i, ‖(∑' e, A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)*P i‖) ≤
      ((n+1:ℕ):ℝ)*M*Ccount*Cmoment*
        U^(q*L-q*Selection.zeroCapacity cost d/2+(3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/2) := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hrho : 0 ≤ delta/2 := by linarith
  let B (j : ℕ) (i : ι) := normalizedBox U xi n j (delta/2) M
    (fun e => max 1 (Lc i*N i e)) (fun e => A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)
  have hsplit (i : ι) : (∑' e, A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) =
      ∑ j ∈ Finset.range (n+1), ((M*U^(-delta*((j:ℝ)*xi)/2):ℝ):ℂ)*B j i := by
    have hh := normalized_box_reconstruction U xi n (delta/2) M hU0 hM.ne'
      (fun e => max 1 (Lc i*N i e)) (fun e => A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) (hseries i)
    have hexp (j : ℕ) : -(delta/2)*((j:ℝ)*xi) = -delta*((j:ℝ)*xi)/2 := by ring
    simpa only [hexp,B] using hh
  have henergy (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∑ i, ‖B j i‖^4*‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon) :=
    normalized_dilation_box_fourth base A S N hN Lc (delta/2) U xi n j valid (Q j) M
      (Cmoment*U^(1+epsilon)) hM hU hxi hrho hzero hupper hs hmass (hselection j hj)
  exact finite_bins Finset.univ n B Q P _ cost d U R q L xi ann delta loss epsilon
    Ccount Cmoment M hcost hU hc hm hM.le hq hqdelta hxi hann (by simpa using hcard)
    (fun i hi => hsplit i) (fun j hj i hi => hselected j hj i) (fun i hi => hfull i) henergy

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.weighted_bin
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.packet_bins
