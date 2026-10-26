/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The first selection loss is chosen after the genuine regular saving. All
four actual contributions are paid without a cardinality-dependent mesh. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.ExceptionalFirstErrors

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialRegularToTruncated
noncomputable section
open Record1252270103Finite

theorem choose_losses (n:Source)(amp σ ξ:ℝ)(he:0<(n.allowance:ℝ))
    (hL:0≤(n.L:ℝ))(ha:0<amp)(hσ:0<σ)(hξ:ξ≤PhysicalLowGuard.step n):
    ∃e:ℝ,0<e ∧ 2*e+ξ/12≤PhysicalLowGuard.step n ∧
      10*e≤3*amp ∧ 3*e≤amp ∧ e≤σ ∧
      2*PhysicalLowGuard.step n+4*e≤2*(n.allowance:ℝ) := by
  have hs:=PhysicalLowGuard.step_positive n he hL
  have hse:PhysicalLowGuard.step n≤(n.allowance:ℝ)/16:=by
    unfold PhysicalLowGuard.step
    apply div_le_div_of_nonneg_left he.le (by norm_num)
    nlinarith only [hL]
  let e:=min (PhysicalLowGuard.step n/100) (min (amp/100) (σ/2))
  have hpos:0<e:=lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have h1:e≤PhysicalLowGuard.step n/100:=min_le_left _ _
  have h2:e≤amp/100:=(min_le_right _ _).trans (min_le_left _ _)
  have h3:e≤σ/2:=(min_le_right _ _).trans (min_le_right _ _)
  exact ⟨e,hpos,by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem selection_absorption (Z e saving S C P G H:ℝ)(d J:ℕ)
    (hZ:1≤Z)(hpay:e≤saving)(hS:0≤S)(hC:0≤C)(hG:0≤G)(hH:1≤H)(hd:d≤J):
    (S*Z^e)*(C*P^2*G*H^d*Z^(-saving))≤S*C*P^2*G*H^J := by
  have hZ0:=zero_lt_one.trans_le hZ
  have hz:Z^(e-saving)≤1:=by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hZ (show e-saving≤0 by linarith)
  have hheight:H^d≤H^J:=pow_le_pow_right₀ hH hd
  calc
    _=(S*C*P^2*G)*H^d*Z^(e-saving):=by
      rw [sub_eq_add_neg,Real.rpow_add hZ0]
      ring
    _≤(S*C*P^2*G)*H^J*1:=by gcongr
    _=_:=mul_one _

theorem selected_four_payment (Z e amp allowance σ S Cz Cr Ce Ct P G H B z r c t:ℝ)
    (dr de:ℕ)(hZ:1≤Z)(he:0≤e)(ha:3*e≤amp)(hp:e≤σ)(hallow:0≤allowance)
    (hS:0≤S)(hz0:0≤Cz)(hr0:0≤Cr)(hc0:0≤Ce)(ht0:0≤Ct)(hG:0≤G)(hH:1≤H)
    (hbase:B≤(S*Z^e)*(z+(r+c)+t))
    (hz:z≤Cz*P^2*G*Z^(-amp-allowance+2*e))
    (hr:r≤Cr*P^2*G*H^dr*Z^(-σ))
    (hc:c≤Ce*P^2*G*H^de*Z^(-amp))
    (ht:t≤Ct*P^2*G*Z^(-amp-allowance-1+2*e)):
    B≤S*(Cz+Cr+Ce+Ct)*P^2*G*H^(max dr de) := by
  have hz':(S*Z^e)*z≤S*Cz*P^2*G*H^(max dr de):=by
    apply (mul_le_mul_of_nonneg_left hz (mul_nonneg hS (Real.rpow_nonneg (zero_lt_one.trans_le hZ).le _))).trans
    have h:=selection_absorption Z e (amp+allowance-2*e) S Cz P G H 0 (max dr de)
      hZ (by linarith) hS hz0 hG hH (Nat.zero_le _)
    simpa only [pow_zero,mul_one,neg_sub,neg_add,sub_eq_add_neg,neg_neg,add_assoc] using h
  have hr':(S*Z^e)*r≤S*Cr*P^2*G*H^(max dr de):=
    (mul_le_mul_of_nonneg_left hr (mul_nonneg hS (Real.rpow_nonneg (zero_lt_one.trans_le hZ).le _))).trans
      (selection_absorption Z e σ S Cr P G H dr (max dr de) hZ hp hS hr0 hG hH (le_max_left _ _))
  have hc':(S*Z^e)*c≤S*Ce*P^2*G*H^(max dr de):=
    (mul_le_mul_of_nonneg_left hc (mul_nonneg hS (Real.rpow_nonneg (zero_lt_one.trans_le hZ).le _))).trans
      (selection_absorption Z e amp S Ce P G H de (max dr de) hZ (by linarith) hS hc0 hG hH (le_max_right _ _))
  have ht':(S*Z^e)*t≤S*Ct*P^2*G*H^(max dr de):=by
    apply (mul_le_mul_of_nonneg_left ht (mul_nonneg hS (Real.rpow_nonneg (zero_lt_one.trans_le hZ).le _))).trans
    have h:=selection_absorption Z e (amp+allowance+1-2*e) S Ct P G H 0 (max dr de)
      hZ (by linarith) hS ht0 hG hH (Nat.zero_le _)
    convert h using 1 <;> first | rfl | congr 2 <;> ring
  have hsum:=add_le_add (add_le_add hz' (add_le_add hr' hc')) ht'
  apply hbase.trans
  convert hsum using 1 <;> ring
end
end QRH.Record1252270103Source.InitialRegularToTruncated
#print axioms QRH.Record1252270103Source.InitialRegularToTruncated.choose_losses
#print axioms QRH.Record1252270103Source.InitialRegularToTruncated.selection_absorption
#print axioms QRH.Record1252270103Source.InitialRegularToTruncated.selected_four_payment
