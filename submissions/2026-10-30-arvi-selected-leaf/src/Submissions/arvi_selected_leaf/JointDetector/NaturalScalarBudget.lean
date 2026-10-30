/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.FiveColourNorm

/-! Shared-table scalar budget for the complete squarefree envelope.

The linear dual-length term is retained even on small radial shells.
The same shell ratio multiplies both squarefree fibres. Common Mellin decay
pays this ratio uniformly; a finite dyadic truncation then costs only its
cardinality. The analytic Schwartz tail is a separate obligation.
-/
namespace Qrh.JointDetector.NaturalScalarBudget
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open FiveColourNorm OAI CanonicalQuadraticSieve

/-- Below the row radius, the nonlinear squarefree term pays the linear term. -/
theorem linear_le_short (B Y δ : ℝ) (hY : 0 < Y) (hYB : Y ≤ B)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    Y ≤ B^(1-δ)*Y^δ := by
  have hp := Real.rpow_le_rpow hY.le hYB (sub_nonneg.mpr hδ.2)
  calc
    Y = Y^(1-δ)*Y^δ := by
      rw [← Real.rpow_add hY]
      simp
    _ ≤ B^(1-δ)*Y^δ := mul_le_mul_of_nonneg_right hp (by positivity)

/-- Both terms of the complete bound at the actual radius tY. -/
theorem shell_envelope_le (B Y t δ : ℝ) (hY : 0 < Y) (hYB : Y ≤ B)
    (ht : 0 < t) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    t*Y+B^(1-δ)*(t*Y)^δ ≤ (t+t^δ)*(B^(1-δ)*Y^δ) := by
  rw [Real.mul_rpow ht.le hY.le]
  have hlin := mul_le_mul_of_nonneg_left (linear_le_short B Y δ hY hYB hδ) ht.le
  nlinarith

/-- A common shell ratio stays common after the two fibre Cauchy factors. -/
theorem shell_sqrt_envelope_le (BL BR Y t δ : ℝ) (hY : 0 < Y)
    (hYL : Y ≤ BL) (hYR : Y ≤ BR) (ht : 0 < t)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    Real.sqrt ((t*Y+BL^(1-δ)*(t*Y)^δ)*(t*Y+BR^(1-δ)*(t*Y)^δ)) ≤
      (t+t^δ)*Real.sqrt ((BL^(1-δ)*Y^δ)*(BR^(1-δ)*Y^δ)) := by
  have hBL : 0 < BL := hY.trans_le hYL
  have hBR : 0 < BR := hY.trans_le hYR
  have hprod := mul_le_mul (shell_envelope_le BL Y t δ hY hYL ht hδ)
    (shell_envelope_le BR Y t δ hY hYR ht hδ) (by positivity) (by positivity)
  calc
    _ ≤ Real.sqrt (((t+t^δ)*(BL^(1-δ)*Y^δ))*
        ((t+t^δ)*(BR^(1-δ)*Y^δ))) := Real.sqrt_le_sqrt hprod
    _ = Real.sqrt ((t+t^δ)^2*((BL^(1-δ)*Y^δ)*(BR^(1-δ)*Y^δ))) := by ring_nf
    _ = _ := by rw [Real.sqrt_mul (by positivity),Real.sqrt_sq (by positivity)]

/-- Full shared-table cost at any positive actual dual-shell radius.
The puncture R here is its good-prime part; a fixed bad factor can be
absorbed in t and discarded from the reciprocal prefactor. -/
theorem shared_shell_cost_le (U V X G H J E F R t δ : ℝ)
    (hU : 0 < U) (hV : 0 < V) (hX : U*V^2 ≤ X)
    (hG : 1 ≤ G) (hH : 1 ≤ H) (hJ : 1 ≤ J) (hE : 1 ≤ E)
    (hF : 1 ≤ F) (hR : 1 ≤ R) (hpuncture : R ≤ G*H)
    (ht : 0 < t) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    X*G/(U*R*Real.sqrt J)*
      Real.sqrt ((t*sharedDualScale U V X G H J E F R+
        (U/(G*E))^(1-δ)*(t*sharedDualScale U V X G H J E F R)^δ)*
        (t*sharedDualScale U V X G H J E F R+
        (U/(G*F))^(1-δ)*(t*sharedDualScale U V X G H J E F R)^δ)) ≤
      (t+t^δ)*X := by
  have hXp : 0 < X := (by positivity : 0 < U*V^2).trans_le hX
  have hGp : 0 < G := by linarith
  have hHp : 0 < H := by linarith
  have hJp : 0 < J := by linarith
  have hEp : 0 < E := by linarith
  have hFp : 0 < F := by linarith
  have hRp : 0 < R := by linarith
  have hY : 0 < sharedDualScale U V X G H J E F R := by
    unfold sharedDualScale
    positivity
  have hpiv := sharedDualScale_le_pivots U V X G H J E F R
    hU hV hX hG hH hJ hE hF hR hpuncture
  have hroot := shell_sqrt_envelope_le _ _ _ t δ hY hpiv.1 hpiv.2 ht hδ
  calc
    _ ≤ X*G/(U*R*Real.sqrt J)*((t+t^δ)*
        Real.sqrt (((U/(G*E))^(1-δ)*(sharedDualScale U V X G H J E F R)^δ)*
        ((U/(G*F))^(1-δ)*(sharedDualScale U V X G H J E F R)^δ))) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = (t+t^δ)*sharedSwapCost U V X G H J E F R δ := by
      unfold sharedSwapCost
      ring
    _ ≤ (t+t^δ)*X := mul_le_mul_of_nonneg_left
      (sharedSwapCost_le U V X G H J E F R δ hU hV hX hG hH hJ hE hF hR hδ)
      (by positivity)

/-- Uniform in arbitrarily small and large shell ratios. -/
theorem decayed_shell_le_two (t δ : ℝ) (n : ℕ) (ht : 0 < t)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hn : 2 ≤ n) :
    (t+t^δ)/(1+t)^n ≤ 2 := by
  have hbase : 1 ≤ 1+t := by linarith
  have hpow : (1+t)^2 ≤ (1+t)^n := pow_le_pow_right₀ hbase hn
  have hfrac : t^δ ≤ 1+t := by
    by_cases hsmall : t ≤ 1
    · exact (Real.rpow_le_one ht.le hsmall hδ.1).trans (by linarith)
    · have hlarge : 1 ≤ t := le_of_not_ge hsmall
      exact (Real.rpow_le_rpow_of_exponent_le hlarge hδ.2).trans_eq
        (Real.rpow_one t) |>.trans (by linarith)
  apply (div_le_iff₀ (by positivity : 0 < (1+t)^n)).mpr
  nlinarith

/-- Finite shell summation retains the actual shell cardinality. -/
theorem sum_decayed_shells_le {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    (δ C X : ℝ) (n : ℕ) (ht : ∀ i ∈ s, 0 < t i)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hC : 0 ≤ C) (hX : 0 ≤ X) (hn : 2 ≤ n) :
    ∑ i ∈ s, (C/(1+t i)^n)*((t i+(t i)^δ)*X) ≤
      2*C*(s.card : ℝ)*X := by
  calc
    _ = ∑ i ∈ s, C*X*((t i+(t i)^δ)/(1+t i)^n) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ _i ∈ s, C*X*2 := Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (decayed_shell_le_two (t i) δ n (ht i hi) hδ hn)
        (mul_nonneg hC hX)
    _ = _ := by simp; ring

/-- A dyadic truncation with polynomial endpoint has arbitrarily small
power cost, without any dependence on the later slot count in that power. -/
theorem dyadic_shell_card_le (Z P ε : ℝ) (hZ : 1 ≤ Z) (hP : 0 < P)
    (hε : 0 < ε) :
    (columnDyadicLength (Z^P)+1 : ℝ) ≤
      (2+P/(ε*Real.log 2))*Z^ε := by
  have hp : 0 < ε/P := div_pos hε hP
  have hz : 1 ≤ Z^P := Real.one_le_rpow hZ hP.le
  have h := columnDyadicLength_small_power (ε/P) hp (Z^P) hz
  have hcoeff : 2+1/((ε/P)*Real.log 2) = 2+P/(ε*Real.log 2) := by
    field_simp
  have hpow : (Z^P)^(ε/P) = Z^ε := by
    rw [← Real.rpow_mul (by linarith : 0 ≤ Z)]
    congr 1
    field_simp
  simpa only [hcoeff,hpow] using h

end
end Qrh.JointDetector.NaturalScalarBudget

#print axioms Qrh.JointDetector.NaturalScalarBudget.shared_shell_cost_le
#print axioms Qrh.JointDetector.NaturalScalarBudget.sum_decayed_shells_le
