/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.NaturalScalarBudget

/-! Fixed dyadic constants in the actual natural near-frequency budget.
The physical radical dyad and both doubled pivot radii are retained. Bad
input punctures and bad output scale are separate quantities.
-/
namespace Qrh.JointDetector.NaturalRoundedBudget
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped BigOperators
open FiveColourNorm NaturalScalarBudget

theorem doubled_envelope_le (B T δ : ℝ) (hB : 0 < B) (hT : 0 < T)
    (hδ : δ ∈ Set.Icc (0:ℝ) 1) :
    T+(2*B)^(1-δ)*T^δ ≤ 2*(T+B^(1-δ)*T^δ) := by
  have hp : (2:ℝ)^(1-δ) ≤ 2 := by
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (by linarith [hδ.1] : 1-δ ≤ 1)).trans_eq (Real.rpow_one 2)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hB.le]
  have hh := mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ B^(1-δ)*T^δ)
  nlinarith

theorem doubled_root_le (BL BR T δ : ℝ) (hBL : 0 < BL) (hBR : 0 < BR)
    (hT : 0 < T) (hδ : δ ∈ Set.Icc (0:ℝ) 1) :
    Real.sqrt ((T+(2*BL)^(1-δ)*T^δ)*(T+(2*BR)^(1-δ)*T^δ)) ≤
      2*Real.sqrt ((T+BL^(1-δ)*T^δ)*(T+BR^(1-δ)*T^δ)) := by
  have hp := mul_le_mul (doubled_envelope_le BL T δ hBL hT hδ)
    (doubled_envelope_le BR T δ hBR hT hδ) (by positivity) (by positivity)
  calc
    _ ≤ Real.sqrt ((2*(T+BL^(1-δ)*T^δ))*(2*(T+BR^(1-δ)*T^δ))) := Real.sqrt_le_sqrt hp
    _ = Real.sqrt (4*((T+BL^(1-δ)*T^δ)*(T+BR^(1-δ)*T^δ))) := by ring_nf
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]; norm_num

theorem rescaled_shell_decay_le (r s C δ : ℝ) (n : ℕ)
    (hr : 0 < r) (hs : 0 < s) (hC : 1 ≤ C) (hsC : s ≤ C)
    (hδ : δ ∈ Set.Icc (0:ℝ) 1) (hn : 2 ≤ n) :
    (r*s+(r*s)^δ)/(1+r)^n ≤ 2*C := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hp : s^δ ≤ C :=
    (Real.rpow_le_rpow hs.le hsC hδ.1).trans
      ((Real.rpow_le_rpow_of_exponent_le hC hδ.2).trans_eq (Real.rpow_one C))
  have ht : r*s+(r*s)^δ ≤ C*(r+r^δ) := by
    rw [Real.mul_rpow hr.le hs.le]
    have hh := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hr.le δ)
    nlinarith
  calc
    _ ≤ C*(r+r^δ)/(1+r)^n := div_le_div_of_nonneg_right ht (by positivity)
    _ = C*((r+r^δ)/(1+r)^n) := by ring
    _ ≤ C*2 := mul_le_mul_of_nonneg_left (decayed_shell_le_two r δ n hr hδ hn) hC0.le
    _ = _ := by ring

/-- A source dyad [T,2T] uses the source envelope at 2T, even though its
Mellin coordinate is normalized by T. This is a fixed factor only. -/
theorem double_source_envelope_le (B T δ : ℝ) (hB : 0 < B) (hT : 0 < T)
    (hδ : δ ∈ Set.Icc (0:ℝ) 1) :
    2*T+B^(1-δ)*(2*T)^δ ≤ 2*(T+B^(1-δ)*T^δ) := by
  have hp : (2:ℝ)^δ ≤ 2 :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hδ.2).trans_eq
      (Real.rpow_one 2)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hT.le]
  have hh := mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ B^(1-δ)*T^δ)
  nlinarith

theorem double_source_root_le (BL BR T δ : ℝ) (hBL : 0 < BL) (hBR : 0 < BR)
    (hT : 0 < T) (hδ : δ ∈ Set.Icc (0:ℝ) 1) :
    Real.sqrt ((2*T+BL^(1-δ)*(2*T)^δ)*(2*T+BR^(1-δ)*(2*T)^δ)) ≤
      2*Real.sqrt ((T+BL^(1-δ)*T^δ)*(T+BR^(1-δ)*T^δ)) := by
  have hp := mul_le_mul (double_source_envelope_le BL T δ hBL hT hδ)
    (double_source_envelope_le BR T δ hBR hT hδ) (by positivity) (by positivity)
  calc
    _ ≤ Real.sqrt ((2*(T+BL^(1-δ)*T^δ))*(2*(T+BR^(1-δ)*T^δ))) := Real.sqrt_le_sqrt hp
    _ = Real.sqrt (4*((T+BL^(1-δ)*T^δ)*(T+BR^(1-δ)*T^δ))) := by ring_nf
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]; norm_num

/-- The actual doubled-radius near cost, uniformly in the common shell r.
The radial dyad distortion rho lies in [1/2,32], not identically one. -/
theorem rounded_shared_cost_le (U V X G H J E F R r b rho Nb Bad δ : ℝ) (n : ℕ)
    (hU : 0 < U) (hV : 0 < V) (hX : U*V^2 ≤ X)
    (hG : 1 ≤ G) (hH : 1 ≤ H) (hJ : 1 ≤ J) (hE : 1 ≤ E)
    (hF : 1 ≤ F) (hR : 1 ≤ R) (hpuncture : R ≤ G*H)
    (hr : 0 < r) (hb : 1 ≤ b) (hbBad : b ≤ Bad)
    (hrho : rho ∈ Set.Icc (1/2:ℝ) 32) (hNb : 1 ≤ Nb)
    (hδ : δ ∈ Set.Icc (0:ℝ) 1) (hn : 2 ≤ n) :
    let T := (r*(b*rho^2/Nb))*sharedDualScale U V X G H J E F R
    ((X*G/(U*R*Real.sqrt J))/(b*rho))*
      Real.sqrt ((T+(2*(U/(G*E)))^(1-δ)*T^δ)*
        (T+(2*(U/(G*F)))^(1-δ)*T^δ))/(1+r)^n ≤ 8192*Bad*X := by
  have hXp : 0 < X := (by positivity : 0 < U*V^2).trans_le hX
  have hGp : 0 < G := by linarith
  have hHp : 0 < H := by linarith
  have hJp : 0 < J := by linarith
  have hEp : 0 < E := by linarith
  have hFp : 0 < F := by linarith
  have hRp : 0 < R := by linarith
  have hbp : 0 < b := by linarith
  have hBad : 1 ≤ Bad := hb.trans hbBad
  have hBadp : 0 < Bad := by linarith
  have hrhop : 0 < rho := by linarith [hrho.1]
  have hNbp : 0 < Nb := by linarith
  let s := b*rho^2/Nb
  have hs : 0 < s := by dsimp [s]; positivity
  have hsC : s ≤ 1024*Bad := by
    apply (div_le_iff₀ hNbp).mpr
    have hp : rho^2 ≤ 1024 := by nlinarith [hrho.1,hrho.2]
    have hh := mul_le_mul hbBad hp (sq_nonneg rho) hBadp.le
    nlinarith
  have hY : 0 < sharedDualScale U V X G H J E F R := by
    unfold sharedDualScale
    positivity
  let T := (r*s)*sharedDualScale U V X G H J E F R
  have hT : 0 < T := by dsimp [T]; positivity
  let pref := X*G/(U*R*Real.sqrt J)
  have hpref : 0 ≤ pref := by dsimp [pref]; positivity
  have hpref' : pref/(b*rho) ≤ 2*pref := by
    apply (div_le_iff₀ (mul_pos hbp hrhop)).mpr
    have hbr : (1/2:ℝ) ≤ b*rho :=
      hrho.1.trans (le_mul_of_one_le_left hrhop.le hb)
    nlinarith
  have hroot := doubled_root_le (U/(G*E)) (U/(G*F)) T δ (by positivity) (by positivity) hT hδ
  have hshort := shared_shell_cost_le U V X G H J E F R (r*s) δ hU hV hX
    hG hH hJ hE hF hR hpuncture (mul_pos hr hs) hδ
  change pref*Real.sqrt ((T+(U/(G*E))^(1-δ)*T^δ)*
    (T+(U/(G*F))^(1-δ)*T^δ)) ≤ (r*s+(r*s)^δ)*X at hshort
  have hdec := rescaled_shell_decay_le r s (1024*Bad) δ n hr hs (by linarith) hsC hδ hn
  change (pref/(b*rho))*Real.sqrt ((T+(2*(U/(G*E)))^(1-δ)*T^δ)*
    (T+(2*(U/(G*F)))^(1-δ)*T^δ))/(1+r)^n ≤ _
  calc
    _ ≤ (2*pref)*(2*Real.sqrt ((T+(U/(G*E))^(1-δ)*T^δ)*
        (T+(U/(G*F))^(1-δ)*T^δ)))/(1+r)^n :=
      div_le_div_of_nonneg_right (mul_le_mul hpref' hroot (Real.sqrt_nonneg _) (by positivity)) (by positivity)
    _ = 4*(pref*Real.sqrt ((T+(U/(G*E))^(1-δ)*T^δ)*
        (T+(U/(G*F))^(1-δ)*T^δ)))/(1+r)^n := by ring
    _ ≤ 4*((r*s+(r*s)^δ)*X)/(1+r)^n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hshort (by norm_num)) (by positivity)
    _ = 4*X*((r*s+(r*s)^δ)/(1+r)^n) := by ring
    _ ≤ 4*X*(2*(1024*Bad)) := mul_le_mul_of_nonneg_left hdec (by positivity)
    _ = _ := by ring

end
end Qrh.JointDetector.NaturalRoundedBudget

#print axioms Qrh.JointDetector.NaturalRoundedBudget.rounded_shared_cost_le
