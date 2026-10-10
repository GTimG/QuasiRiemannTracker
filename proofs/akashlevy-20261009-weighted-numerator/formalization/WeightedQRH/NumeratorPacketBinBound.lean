import WeightedQRH.NumeratorBoxReconstruction

/-! The complete coefficient-packet and dilation-bin estimate. All infinite
coefficient sums and rowwise choice moments have been eliminated here. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace WeightedQRH.Numerator

variable {ι : Type*} [Fintype ι] {α : ι → Type*}

theorem packet_weighted_bins
    (base : ∀ i, α i) (A S : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ)
    (hN : ∀ i e, 0 < N i e) (Lc : ι → ℝ) (U xi : ℝ) (n : ℕ)
    (valid : ∀ i, α i → Prop) [∀ i e, Decidable (valid i e)]
    (Q : ℕ → ι → ℂ) (P : ι → ℂ)
    (R q L z delta loss epsilon Ccount Cmoment M : ℝ)
    (hM : 0 < M) (hU : 1 ≤ U) (hxi : 0 ≤ xi)
    (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment) (hq : 0 ≤ q) (hqdelta : q ≤ delta/2)
    (hcard : (Fintype.card ι : ℝ) ≤ Ccount*U^R)
    (hzero : ∀ i e, ¬valid i e → S i e = 0)
    (hupper : ∀ i e, valid i e → max 1 (Lc i * N i e) ≤ U^((n : ℝ)*xi))
    (hseries : ∀ i, Summable (fun e=>‖A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e‖))
    (hs : ∀ i, Summable (fun e => ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (Lc i * N i e)^(delta/4)))
    (hmass : ∀ i, (∑' e, ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (Lc i * N i e)^(delta/4)) ≤ M)
    (hselected : ∀ j ∈ Finset.range (n+1), ∀ i,
      U^(q*selectedCapacity z ((j : ℝ)*xi+xi)-loss) ≤ ‖Q j i‖)
    (hfull : ∀ i, ‖P i‖ ≤ U^(q*L))
    (hselection : ∀ j ∈ Finset.range (n+1), ∀ e : ∀ i, α i,
      (∑ i, ‖if valid i (e i) ∧ dilationBox U xi n (max 1 (Lc i*N i (e i))) = j
        then S i (e i) else 0‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon)) :
    (∑ i, ‖(∑' e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)*P i‖) ≤
      ((n+1 : ℕ) : ℝ)*M*Ccount*Cmoment*
        U^(q*L-q*z/2+(3*R+1+epsilon)/4+loss/2+delta*xi/4) := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hrho : 0 ≤ delta/4 := by linarith
  let B (j : ℕ) (i : ι) := normalizedBox U xi n j (delta/4) M
    (fun e=>max 1 (Lc i*N i e)) (fun e=>A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)
  have hsplit (i : ι) : (∑' e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) =
      ∑ j ∈ Finset.range (n+1), ((M*U^(-delta*((j : ℝ)*xi)/4) : ℝ):ℂ)*B j i := by
    have hh := normalized_box_reconstruction U xi n (delta/4) M hU0 hM.ne'
      (fun e=>max 1 (Lc i*N i e)) (fun e=>A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) (hseries i)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro j hj
    congr 3
    ring
  have henergy (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∑ i, ‖B j i‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon) :=
    normalized_dilation_box_fourth base A S N hN Lc (delta/4) U xi n j valid (Q j) M
      (Cmoment*U^(1+epsilon)) hM hU hxi hrho hzero hupper hs hmass (hselection j hj)
  exact finite_weighted_dilation_bins Finset.univ n B Q P _ U R q L z xi delta loss epsilon
    Ccount Cmoment M hU hc hm hM.le hq hqdelta hxi (by simpa using hcard)
    (fun i hi=>hsplit i) (fun j hj i hi=>hselected j hj i) (fun i hi=>hfull i) henergy

end WeightedQRH.Numerator
