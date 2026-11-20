/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual ordinary bank, response window, whole slots and height metadata
fit the stated fee of the genuine P4 supplier.
-/
import Candidate.C092.transport.RegularColoredTerminalLeafSelection
set_option autoImplicit false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.StrongPair

/-- The finite-window discrepancy is charged in addition to every genuine
native radius/cap/whole-slot error. The full P4 fee retains strict room. -/
theorem terminal_ordinary_named_fees
    {M conductor gap epsilon epsilonSource buffer tau d e B mbar radius dec rounding collar step price m : ℝ}
    {N degree J : ℕ}
    (hM : 0 ≤ M) (hd0 : 0 ≤ d) (hd : d ≤ M) (he : 0 ≤ e) (he1 : e ≤ (responseUpper:ℝ))
    (hg : 0 ≤ gap) (hcap0 : 0 ≤ B-mbar) (hcap : B-mbar ≤ gap)
    (hradius0 : 0 ≤ min d (H:ℝ)-radius) (hradius : min d (H:ℝ)-radius ≤ gap)
    (hdec0 : 0 ≤ dec) (hdec : dec ≤ gap) (hr0 : 0 ≤ rounding) (hr : rounding ≤ gap)
    (hε : 0 ≤ epsilon) (hes : 0 ≤ epsilonSource)
    (hcollar : collar ≤ 3*conductor) (hc : 3*conductor ≤ (rho:ℝ)/128)
    (hcapFee : (responseUpper:ℝ)*(M*(2*gap)+M*gap+gap) ≤ (rho:ℝ)/128)
    (hwit : (15/4:ℝ)*M*epsilon ≤ (rho:ℝ)/128)
    (hsource : M*epsilonSource ≤ (rho:ℝ)/128)
    (hbuffer : buffer*(N:ℝ) ≤ (rho:ℝ)/128)
    (hheight : tau*((degree+2*J+1:ℕ):ℝ) ≤ (rho:ℝ)/128)
    (hwindow : 3*step+price*d*m ≤ (rho:ℝ)/128) :
    collar+(15/4:ℝ)*d*epsilon+
      e*(d*((5/4:ℝ)*(min d (H:ℝ)-radius)+(3/4:ℝ)*(B-mbar))+d*dec+rounding)+
      (d*epsilonSource+buffer*(N:ℝ)+tau*((degree+2*J+1:ℕ):ℝ))+
      3*step+price*d*m  <  (3/4:ℝ)*(rho:ℝ) := by
  have hE : 0 ≤ (responseUpper:ℝ) := by norm_num [responseUpper]
  have hcap' : e*(d*((5/4:ℝ)*(min d (H:ℝ)-radius)+(3/4:ℝ)*(B-mbar))+d*dec+rounding) ≤ 
      (responseUpper:ℝ)*(M*(2*gap)+M*gap+gap) := by
    apply mul_le_mul he1 _ (by positivity) hE
    have hdelta : (5/4:ℝ)*(min d (H:ℝ)-radius)+(3/4:ℝ)*(B-mbar) ≤ 2*gap := by linarith
    have h1 := mul_le_mul hd hdelta (by positivity) hM
    have h2 := mul_le_mul hd hdec hdec0 hM
    linarith
  have hwit' : (15/4:ℝ)*d*epsilon ≤ (15/4:ℝ)*M*epsilon := by gcongr
  have hs' : d*epsilonSource ≤ M*epsilonSource := by gcongr
  have hrho : 0 < (rho:ℝ) := by norm_num [rho]
  linarith

/-- A single early natural-number bound for all actual source degrees
permits one later positive physical height exponent. -/
theorem terminal_ordinary_height_choice (D : ℕ) :
    ∃ tau : ℝ,0 < tau ∧ tau*(D:ℝ) ≤ (rho:ℝ)/128 := by
  refine ⟨(rho:ℝ)/(128*((D:ℝ)+1)),by norm_num [rho];positivity,?_⟩
  have hD : 0 ≤ (D:ℝ) := Nat.cast_nonneg D
  have hrho : 0 < (rho:ℝ) := by norm_num [rho]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 128*((D:ℝ)+1))).mpr
  nlinarith

#print axioms terminal_ordinary_named_fees
#print axioms terminal_ordinary_height_choice
end
end QRH.Cycle092.RegularColoredForward
