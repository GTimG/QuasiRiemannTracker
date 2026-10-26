/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.RawPrefixPayment

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped BigOperators

private theorem sum_successive_sub (f : ℕ → ℝ) (n : ℕ) :
    (∑i∈Finset.range n, (f (i+1)-f i)) = f n-f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-- Complete finite-history price from the actual physical row payments.
Every raw AtState row scale and every historical missing radical is
included. Only the adjacent actual scale and volume potentials telescope.
The hypotheses are individual native source facts, not a desired terminal
count inequality or a recursive energy callback. -/
theorem finite_physical_path_price
    (n : ℕ) (rho delta cost terminalExponent terminalMissing terminalRow terminalLoss : ℝ)
    (m U A amp prefixLog X0 X1 X2 X3 small Gamma D extraVolume scalePad volumePad
      q fees : ℕ → ℝ)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (hdelta : 0 ≤ delta)
    (hunit : ∀i<n, m i ≤ U i)
    (hparent : ∀i<n, X0 i+X1 i+rho*X2 i+delta*X3 i ≤
      small i-(U i*(1-rho)-delta*A i-amp i*cost)-Gamma i)
    (hscale : ∀i<n, m (i+1)+prefixLog (i+1)-prefixLog i ≤ X2 i+scalePad i)
    (hvolume : ∀i<n, A (i+1) ≤ X3 i-D i-extraVolume i+volumePad i)
    (hterminal : terminalExponent-m n+terminalMissing+rho*(terminalRow-prefixLog n) ≤
      terminalLoss-(m n*(1-rho)-delta*A n-amp n*cost)) :
    (∑i∈Finset.range n, (m i+X0 i+q i*D i+fees i))+terminalExponent+
      (∑i∈Finset.range n, X1 i)+terminalMissing+rho*(terminalRow-prefixLog 0) ≤
    rho*m 0+delta*A 0+cost*((∑i∈Finset.range n, amp i)+amp n)+terminalLoss+
      (∑i∈Finset.range n,
        (small i+fees i+rho*scalePad i+delta*volumePad i-
          (Gamma i+delta*extraVolume i+(delta-q i)*D i))) := by
  let potential := fun i => rho*m i+delta*A i+rho*prefixLog i
  let edge := fun i => m i+X0 i+q i*D i+fees i
  let localLoss := fun i => small i+fees i+rho*scalePad i+delta*volumePad i-
    (Gamma i+delta*extraVolume i+(delta-q i)*D i)
  have hlocal : ∀i∈Finset.range n,
      edge i+X1 i+(potential (i+1)-potential i) ≤ cost*amp i+localLoss i := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hs := mul_le_mul_of_nonneg_left (hscale i hi') hrho
    have hv := mul_le_mul_of_nonneg_left (hvolume i hi') hdelta
    have hu := mul_le_mul_of_nonneg_right (hunit i hi') (sub_nonneg.mpr hrho1)
    dsimp only [edge,potential,localLoss]
    nlinarith only [hparent i hi',hs,hv,hu]
  have hsum := Finset.sum_le_sum hlocal
  have hleft : (∑i∈Finset.range n, (edge i+X1 i+(potential (i+1)-potential i))) =
      (∑i∈Finset.range n, edge i)+(∑i∈Finset.range n, X1 i)+potential n-potential 0 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_successive_sub]
    ring
  have hright : (∑i∈Finset.range n, (cost*amp i+localLoss i)) =
      cost*(∑i∈Finset.range n, amp i)+(∑i∈Finset.range n, localLoss i) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hleft,hright] at hsum
  change (∑i∈Finset.range n, edge i)+terminalExponent+
    (∑i∈Finset.range n, X1 i)+terminalMissing+rho*(terminalRow-prefixLog 0) ≤
      rho*m 0+delta*A 0+cost*((∑i∈Finset.range n, amp i)+amp n)+terminalLoss+
        (∑i∈Finset.range n, localLoss i)
  dsimp only [potential] at hsum
  nlinarith only [hsum,hterminal]

/-- The literal source edge weights are multiplied before counting the
single terminal HIGH class. This changes only the exponent description;
no intermediate unit or historical missing radical is removed. -/
theorem physical_path_weight_price
    (Z : ℝ) (hZ : 1 < Z)
    (n : ℕ) (rho delta cost terminalExponent terminalMissing terminalRow terminalLoss : ℝ)
    (m U A amp prefixLog X0 X1 X2 X3 small Gamma D extraVolume scalePad volumePad
      q fees : ℕ → ℝ)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (hdelta : 0 ≤ delta)
    (hunit : ∀i<n, m i ≤ U i)
    (hparent : ∀i<n, X0 i+X1 i+rho*X2 i+delta*X3 i ≤
      small i-(U i*(1-rho)-delta*A i-amp i*cost)-Gamma i)
    (hscale : ∀i<n, m (i+1)+prefixLog (i+1)-prefixLog i ≤ X2 i+scalePad i)
    (hvolume : ∀i<n, A (i+1) ≤ X3 i-D i-extraVolume i+volumePad i)
    (hterminal : terminalExponent-m n+terminalMissing+rho*(terminalRow-prefixLog n) ≤
      terminalLoss-(m n*(1-rho)-delta*A n-amp n*cost)) :
    (∏i∈Finset.range n, Z^(m i+X0 i+q i*D i+fees i)) *
      Z^(terminalExponent+(∑i∈Finset.range n, X1 i)+terminalMissing+
        rho*(terminalRow-prefixLog 0)) ≤
    Z^(rho*m 0+delta*A 0+cost*((∑i∈Finset.range n, amp i)+amp n)+terminalLoss+
      (∑i∈Finset.range n,
        (small i+fees i+rho*scalePad i+delta*volumePad i-
          (Gamma i+delta*extraVolume i+(delta-q i)*D i)))) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hprod : ∀k : ℕ, (∏i∈Finset.range k, Z^(m i+X0 i+q i*D i+fees i)) =
      Z^(∑i∈Finset.range k, (m i+X0 i+q i*D i+fees i)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ,Finset.sum_range_succ,ih]
      exact (Real.rpow_add hZ0 _ _).symm
  rw [hprod, ← Real.rpow_add hZ0]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  have hp := finite_physical_path_price n rho delta cost terminalExponent terminalMissing terminalRow
    terminalLoss m U A amp prefixLog X0 X1 X2 X3 small Gamma D extraVolume scalePad volumePad q fees
    hrho hrho1 hdelta hunit hparent hscale hvolume hterminal
  linarith only [hp]

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.finite_physical_path_price
#print axioms OAI.SevenEighths.Cycle153RegionalLow.physical_path_weight_price
