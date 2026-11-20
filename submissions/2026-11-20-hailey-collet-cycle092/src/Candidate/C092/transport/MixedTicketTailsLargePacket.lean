/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Complete countable original coefficient series restricted by its literal large
max-one dilation, using the genuine quarter-density first-norm payment. -/
import Candidate.C092.transport.MixedTicketTailsFinite
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths Cycle25.Numerator
open QRH.Record1252270103Return
namespace QRH.Cycle092.MixedTicketTails
variable [Geometry.Parameters]
theorem packet_large_bins {ι : Type*} [Fintype ι] {α : ι → Type*}
    (base : ∀ i, α i) (A S : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ)
    (hN : ∀ i e, 0 < N i e) (Lc : ι → ℝ) (cost d U xi ann : ℝ) (n : ℕ)
    (valid : ∀ i, α i → Prop) [∀ i e, Decidable (valid i e)]
    (Q : ℕ → ι → ℂ) (P : ι → ℂ)
    (R q L delta loss epsilon Ccount Cmoment M vcut : ℝ)
    (hcost : 0 ≤ cost) (hM : 0 < M) (hU : 1 < U) (hxi : 0 ≤ xi) (hann : 0 ≤ ann)
    (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment) (hq : 0 ≤ q) (hqdelta : q ≤ delta/2)
    (hcard : (Fintype.card ι:ℝ) ≤ Ccount*U^R)
    (hzero : ∀ i e, ¬valid i e → S i e = 0)
    (hupper : ∀ i e, valid i e → max 1 (Lc i*N i e) ≤ U^((n:ℝ)*xi))
    (hlower : ∀ i e,valid i e → U^vcut ≤ max 1 (Lc i*N i e))
    (hseries : ∀ i, Summable (fun e => ‖A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e‖))
    (hs : ∀ i, Summable (fun e => ‖A i e‖*(N i e)^(-(1/2:ℝ))*max 1 (Lc i*N i e)^(delta/2)))
    (hmass : ∀ i, (∑' e, ‖A i e‖*(N i e)^(-(1/2:ℝ))*max 1 (Lc i*N i e)^(delta/2)) ≤ M)
    (hselected : ∀ j ∈ Finset.range (n+1), ∀ i,
      U^(q*QRH.Cycle092.Physical.Selection.scheduledCapacity Geometry.y cost d (2*((j:ℝ)*xi+xi+ann))-loss) ≤ ‖Q j i‖)
    (hfull : ∀ i, ‖P i‖ ≤ U^(q*L))
    (hselection : ∀ j ∈ Finset.range (n+1), ∀ e : ∀ i, α i,
      (∑ i, ‖if valid i (e i) ∧ dilationBox U xi n (max 1 (Lc i*N i (e i))) = j
        then S i (e i) else 0‖^4*‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon)) :
    (∑ i, ‖(∑' e, A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)*P i‖) ≤
      ((n+1:ℕ):ℝ)*M*Ccount*Cmoment*
        U^(q*L-q*QRH.Cycle092.Physical.Selection.zeroCapacity Geometry.y cost d/2+(3*R+1+epsilon)/4+loss/2+delta*(2*xi+ann)/4-delta*vcut/4) := by
  have hU0 : 0 < U := zero_lt_one.trans hU
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
      (Cmoment*U^(1+epsilon)) hM hU.le hxi hrho hzero hupper hs hmass (hselection j hj)
  have hsmall (j : ℕ) (_hj : j∈Finset.range (n+1)) (hcut : (j:ℝ)*xi+xi<vcut)
      (i : ι) (_hi : i∈(Finset.univ:Finset ι)) : B j i=0 := by
    dsimp only [B,normalizedBox]
    suffices hh : (∑'e,boxSeriesTerm U xi n j (fun e=>max 1 (Lc i*N i e))
        (fun e=>A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) e)=0 by rw [hh,mul_zero]
    refine (tsum_congr ?_).trans (tsum_zero : (∑'_e : α i,(0:ℂ))=0)
    intro e
    by_cases hv : valid i e
    · by_cases hb : dilationBox U xi n (max 1 (Lc i*N i e))=j
      · have ht := (dilationBox_spec U xi hU.le hxi n (max 1 (Lc i*N i e))
          (le_max_left _ _) (hupper i e hv)).2
        rw [hb] at ht
        have hx := (Real.rpow_le_rpow_left_iff hU).mp ((hlower i e hv).trans ht)
        have : False := by nlinarith only [hx,hcut]
        exact this.elim
      · simp only [boxSeriesTerm,hb,if_false]
    · simp only [boxSeriesTerm,hzero i e hv,mul_zero,ite_self]
  exact finite_large_bins Finset.univ n B Q P _ Geometry.y cost d U R q L xi ann delta loss epsilon
    Ccount Cmoment M vcut hcost hU.le hc hm hM.le hq hqdelta hxi hann (by simpa using hcard)
    (fun i hi => hsplit i) (fun j hj i hi => hselected j hj i) (fun i hi => hfull i) henergy hsmall

#print axioms packet_large_bins
end QRH.Cycle092.MixedTicketTails
