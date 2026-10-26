import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Weighted.WeightedQRH.NumeratorBoxReconstruction
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle25.Numerator.Imported.NumeratorLabelPacket
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Numerator.Source.FiniteBins
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
/-! Infinite coefficient sums are reconstructed by the existing normalized-box
lemmas. The rowwise fourth moment remains an explicit integration input. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace Cycle63.Numerator.Source
open Cycle63.Arithmetic Cycle63.Numerator.Capacity
open Cycle25.Numerator

variable {ι : Type*} [Fintype ι] {α : ι → Type*}

theorem packet_weighted_bins
    (base : ∀ i, α i) (A S : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ)
    (hN : ∀ i e, 0 < N i e) (Lc : ι → ℝ) (d U xi ann : ℝ) (n : ℕ)
    (valid : ∀ i, α i → Prop) [∀ i e, Decidable (valid i e)]
    (Q : ℕ → ι → ℂ) (P : ι → ℂ)
    (R q L delta loss epsilon Ccount Cmoment M : ℝ)
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (hM : 0 < M) (hU : 1 ≤ U) (hxi : 0 ≤ xi) (hann : 0 ≤ ann)
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
      (∑ i, ‖if valid i (e i) ∧ WeightedQRH.Numerator.dilationBox U xi n (max 1 (Lc i*N i (e i))) = j
        then S i (e i) else 0‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon)) :
    (∑ i, ‖(∑' e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)*P i‖) ≤
      ((n+1 : ℕ) : ℝ)*M*Ccount*Cmoment*
        U^(q*L-q*zeroCapacity d/2+(3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/2) := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hrho : 0 ≤ delta/2 := by linarith
  let B (j : ℕ) (i : ι) := WeightedQRH.Numerator.normalizedBox U xi n j (delta/2) M
    (fun e=>max 1 (Lc i*N i e)) (fun e=>A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)
  have hsplit (i : ι) : (∑' e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) =
      ∑ j ∈ Finset.range (n+1), ((M*U^(-delta*((j : ℝ)*xi)/2) : ℝ):ℂ)*B j i := by
    have hh := WeightedQRH.Numerator.normalized_box_reconstruction U xi n (delta/2) M hU0 hM.ne'
      (fun e=>max 1 (Lc i*N i e)) (fun e=>A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) (hseries i)
    have hexp (j : ℕ) : -(delta/2)*((j : ℝ)*xi) = -delta*((j : ℝ)*xi)/2 := by ring
    simpa only [hexp, B] using hh
  have henergy (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∑ i, ‖B j i‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon) :=
    WeightedQRH.Numerator.normalized_dilation_box_fourth base A S N hN Lc (delta/2) U xi n j valid (Q j) M
      (Cmoment*U^(1+epsilon)) hM hU hxi hrho hzero hupper hs hmass (hselection j hj)
  exact finite_weighted_dilation_bins Finset.univ n B Q P _ d U R q L xi ann delta loss epsilon
    Ccount Cmoment M hd hU hc hm hM.le hq hqdelta hxi hann (by simpa using hcard)
    (fun i hi=>hsplit i) (fun j hj i hi=>hselected j hj i) (fun i hi=>hfull i) henergy

end Cycle63.Numerator.Source

end
end Record1252270103Bootstrap.PR67
