/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low

theorem common_initial_bound_algebra (E N R A p₀ pp pr p H Z ε Cp Cd Ct Cr : ℝ)
    (dp dr : ℕ) (hA : 0≤A) (h0 : 0≤p₀) (hpp : 0≤pp) (hpr : 0≤pr)
    (h₀p : p₀≤p) (hpp' : pp≤p) (hpr' : pr≤p) (hH : 1≤H) (hZ : 1≤Z)
    (hε : 0≤ε) (hCp : 0≤Cp) (hCd : 0≤Cd) (hCt : 0≤Ct) (hCr : 0≤Cr)
    (hN : N≤Cp*pp^2*H^dp*Z^(1+ε))
    (hR : R≤Cr*A*pr^2*H^dr*Z^(1+ε))
    (hE : E≤2*A*(N+Cd*p₀^2*Z*Z^ε+Ct*p₀^2*Z*Z^(-(0:ℝ)))+2*R) :
    E≤(2*(Cp+Cd+Ct)+2*Cr)*A*p^2*H^(dp+dr)*Z^(1+ε) := by
  have hp : 0≤p:=h0.trans h₀p
  have hz : 0<Z:=zero_lt_one.trans_le hZ
  have hpPow:=pow_le_pow_right₀ hH (Nat.le_add_right dp dr)
  have hrPow:=pow_le_pow_right₀ hH (Nat.le_add_left dr dp)
  have hPow1 : 1≤H^(dp+dr):=one_le_pow₀ hH
  have hzpow:=Real.rpow_nonneg hz.le (1+ε)
  have hZe : Z*Z^ε=Z^(1+ε):=by rw [Real.rpow_add hz,Real.rpow_one]
  have hZle : Z≤Z^(1+ε):=by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ
      (show (1:ℝ)≤1+ε by linarith)
  have hN' : N≤Cp*p^2*H^(dp+dr)*Z^(1+ε):=hN.trans (by gcongr)
  have hR' : R≤Cr*A*p^2*H^(dp+dr)*Z^(1+ε):=hR.trans (by gcongr)
  have hdi : Cd*p₀^2*Z*Z^ε≤Cd*p^2*H^(dp+dr)*Z^(1+ε) := by
    rw [mul_assoc _ Z (Z^ε),hZe]
    calc
      _≤Cd*p^2*Z^(1+ε):=by gcongr
      _≤_:=by
        have hh:=mul_le_mul_of_nonneg_left hPow1 (mul_nonneg (mul_nonneg hCd (sq_nonneg p)) hzpow)
        nlinarith only [hh]
  have hta : Ct*p₀^2*Z*Z^(-(0:ℝ))≤Ct*p^2*H^(dp+dr)*Z^(1+ε) := by
    simp only [neg_zero,Real.rpow_zero,mul_one]
    calc
      _≤Ct*p^2*Z^(1+ε):=by gcongr
      _≤_:=by
        have hh:=mul_le_mul_of_nonneg_left hPow1 (mul_nonneg (mul_nonneg hCt (sq_nonneg p)) hzpow)
        nlinarith only [hh]
  refine hE.trans ?_
  calc
    _≤2*A*(Cp*p^2*H^(dp+dr)*Z^(1+ε)+Cd*p^2*H^(dp+dr)*Z^(1+ε)+
      Ct*p^2*H^(dp+dr)*Z^(1+ε))+2*(Cr*A*p^2*H^(dp+dr)*Z^(1+ε)) := by gcongr
    _=_:=by ring

end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.common_initial_bound_algebra
