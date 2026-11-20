/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The numerical dyad-box constructor applies to the selected second scale.
Only one generous absolute upper bound is needed for the entire range. -/
import Candidate.C092.transport.FirstGroupBudget
import Candidate.C092.transport.ActualColoredCutoff
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter
namespace QRH.Cycle092.FixedFramePacking

theorem box_parameters {Z G V rootVol K W X κ:ℝ}
    (hZ:4096 ≤ Z) (hG:0<G) (hV:0 ≤ V) (hVcap:V ≤ G^2) (hr:0 ≤ rootVol) (hroot:rootVol ≤ Z)
    (hK:1/2 ≤ K) (hW:1 ≤ W) (hw:W ≤ Z^(1/1000:ℝ)) (hκ:κ ≤ 1/1000)
    (hradius:K*G^2*Z ≤ 4*V*rootVol^2*Z^((3/2)*κ))
    (hx:1 ≤ X) (hX:X ≤ Z^(919/1000:ℝ)) :
    let K₂:=16*K*W^4
    let Tsec:=X^2/K₂
    8 ≤ K₂ ∧ K₂ ≤ Z^(2:ℝ) ∧ 0 ≤ Tsec ∧ Tsec ≤ Z^(2:ℝ) ∧ X ≤ Z^(8:ℝ) := by
  have hz:1<Z:=by linarith
  have h0:=zero_lt_one.trans hz
  have hkpos:0<K:=by linarith
  have hZκ:=Real.rpow_nonneg h0.le ((3/2)*κ)
  have hleft:K*Z  ≤  4*rootVol^2*Z^((3/2)*κ) := by
    apply le_of_mul_le_mul_right (a:=G^2) _ (sq_pos_of_pos hG)
    calc
      _ = K*G^2*Z := by ring
      _  ≤  _ := hradius
      _  ≤  4*G^2*rootVol^2*Z^((3/2)*κ) := by gcongr
      _ = _ := by ring
  have hk0:K  ≤  4*Z*Z^((3/2)*κ) := by
    apply le_of_mul_le_mul_right (a:=Z) _ h0
    calc
      _  ≤  _ := hleft
      _  ≤  4*Z^2*Z^((3/2)*κ) := by gcongr
      _ = _ := by ring
  have h64:64 ≤ Z^(1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.le_sqrt (by norm_num) h0.le).mpr (by norm_num at hZ ⊢;linarith)
  have hp : W^4  ≤  Z^(4/1000:ℝ) := by
    have h:=pow_le_pow_left₀ (zero_le_one.trans hW) hw 4
    rw [←Real.rpow_mul_natCast h0.le] at h
    convert h using 2 <;> norm_num
  have h8:8 ≤ 16*K*W^4 := by
    have hh:1 ≤ W^4:=one_le_pow₀ hW
    nlinarith only [hK,hh,mul_nonneg hkpos.le (sub_nonneg.mpr hh)]
  have hk:16*K*W^4  ≤  Z^(2:ℝ) := calc
    _  ≤  16*(4*Z*Z^((3/2)*κ))*Z^(4/1000:ℝ) := by gcongr
    _ = 64*(Z^(1:ℝ)*Z^((3/2)*κ)*Z^(4/1000:ℝ)) := by rw [Real.rpow_one];ring
    _  ≤  Z^(1/2:ℝ)*(Z^(1:ℝ)*Z^((3/2)*κ)*Z^(4/1000:ℝ)) := by gcongr
    _ = Z^(1/2+(1+(3/2)*κ+4/1000):ℝ) := by rw [←Real.rpow_add h0,←Real.rpow_add h0,←Real.rpow_add h0]
    _  ≤  _ := Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)
  refine ⟨h8,hk,div_nonneg (sq_nonneg _) (by linarith),?_,hX.trans (Real.rpow_le_rpow_of_exponent_le hz.le (by norm_num))⟩
  calc
    _  ≤  X^2 := div_le_self (sq_nonneg _) (by linarith)
    _  ≤  (Z^(919/1000:ℝ))^2 := pow_le_pow_left₀ (zero_le_one.trans hx) hX 2
    _  ≤  _ := by rw [←Real.rpow_mul_natCast h0.le];apply Real.rpow_le_rpow_of_exponent_le hz.le;norm_num

#print axioms box_parameters
end QRH.Cycle092.FixedFramePacking
