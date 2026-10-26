/- Repeated marks: fork of Collet's generic return module PhysicalDirect.PacketBound (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Adapted from Gao Target830 physical closure, inherited OpenAI/Hailey Collet/Akash Levy; Apache-2.0. -/
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.Schedule
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.BoxReconstruction
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.PhysicalDirect.FiniteBins
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped BigOperators Classical
namespace QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect.Packet
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Geometry.BoundsR] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open QRH.RepeatedMarks.Return.GenericArithmetic
open QRH.RepeatedMarks.Return.GenericArithmetic QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect
open Cycle25.Numerator

variable {ι : Type*} [Fintype ι] {α : ι → Type*}

theorem packet_weighted_bins
    (base : ∀ i, α i) (A S : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ)
    (hN : ∀ i e, 0 < N i e) (Lc : ι → ℝ) (d U xi ann : ℝ) (n : ℕ)
    (valid : ∀ i, α i → Prop) [∀ i e, Decidable (valid i e)]
    (Q : ℕ → ι → ℂ) (P : ι → ℂ)
    (R q L delta loss epsilon Ccount Cmoment M : ℝ)
    (hd : dm ≤ d ∧ d ≤ dp) (hM : 0 < M) (hU : 1 ≤ U) (hxi : 0 ≤ xi) (hann : 0 ≤ ann)
    (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment) (hq : 0 ≤ q) (hqdelta : q ≤ delta/2)
    (hcard : (Fintype.card ι : ℝ) ≤ Ccount*U^R)
    (hzero : ∀ i e, ¬valid i e → S i e = 0)
    (hupper : ∀ i e, valid i e → max 1 (Lc i * N i e) ≤ U^((n : ℝ)*xi))
    (hseries : ∀ i, Summable (fun e=>‖A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e‖))
    (hs : ∀ i, Summable (fun e => ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (Lc i * N i e)^(delta/2)))
    (hmass : ∀ i, (∑' e, ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (Lc i * N i e)^(delta/2)) ≤ M)
    (hselected : ∀ j ∈ Finset.range (n+1), ∀ i,
      U^(q*scheduledCapacity d (2*((j : ℝ)*xi+xi+ann))-loss) ≤ ‖Q j i‖)
    (hfull : ∀ i, ‖P i‖ ≤ U^(q*L))
    (hselection : ∀ j ∈ Finset.range (n+1), ∀ e : ∀ i, α i,
      (∑ i, ‖if valid i (e i) ∧ dilationBox U xi n (max 1 (Lc i*N i (e i))) = j
        then S i (e i) else 0‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon)) :
    (∑ i, ‖(∑' e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)*P i‖) ≤
      ((n+1 : ℕ) : ℝ)*M*Ccount*Cmoment*
        U^(q*L-q*zeroCapacity d/2+(3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/2) := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hrho : 0 ≤ delta/2 := by linarith
  let B (j : ℕ) (i : ι) := normalizedBox U xi n j (delta/2) M
    (fun e=>max 1 (Lc i*N i e)) (fun e=>A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)
  have hsplit (i : ι) : (∑' e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) =
      ∑ j ∈ Finset.range (n+1), ((M*U^(-delta*((j : ℝ)*xi)/2) : ℝ):ℂ)*B j i := by
    have hh := normalized_box_reconstruction U xi n (delta/2) M hU0 hM.ne'
      (fun e=>max 1 (Lc i*N i e)) (fun e=>A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) (hseries i)
    have hexp (j : ℕ) : -(delta/2)*((j : ℝ)*xi) = -delta*((j : ℝ)*xi)/2 := by ring
    simpa only [hexp, B] using hh
  have henergy (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∑ i, ‖B j i‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon) :=
    normalized_dilation_box_fourth base A S N hN Lc (delta/2) U xi n j valid (Q j) M
      (Cmoment*U^(1+epsilon)) hM hU hxi hrho hzero hupper hs hmass (hselection j hj)
  exact finite_weighted_dilation_bins Finset.univ n B Q P _ d U R q L xi ann delta loss epsilon
    Ccount Cmoment M hd hU hc hm hM.le hq hqdelta hxi hann (by simpa using hcard)
    (fun i hi=>hsplit i) (fun j hj i hi=>hselected j hj i) (fun i hi=>hfull i) henergy


end QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect.Packet
