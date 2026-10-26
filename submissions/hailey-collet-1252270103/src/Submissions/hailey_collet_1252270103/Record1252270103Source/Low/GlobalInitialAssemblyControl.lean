/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.BandMonotonicity
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBandMonotonicity QuadraticInitialBound

theorem source_control_promote {a b : ℝ} (p : Profiles a b) (Φ : 𝓢(ℝ,ℂ))
    (S U : Finset (ℕ×ℕ)) (hS : S⊆U) (d D : ℕ) (hd : d≤D)
    (C C' t height Z ε : ℝ) (hC : 0≤C) (hCC : C*2^d≤C') (hh : 0≤height) (hZ : 0≤Z) :
    C*diagonalControl Φ*(p.control S)^2*(1+|t|+|t|+height)^d*Z^ε≤
      C'*diagonalControl Φ*(p.control U)^2*(1+|t|+height)^D*Z^ε := by
  have hbase : 1≤1+|t|+height:=by linarith [abs_nonneg t]
  have hp:=profile_control_mono p hS
  have hp0:=p.control_nonneg S
  have hu0:=p.control_nonneg U
  have hdiag:=diagonalControl_nonneg Φ
  have hpow : (1+|t|+|t|+height)^d≤2^d*(1+|t|+height)^D := by
    have h1:=pow_le_pow_left₀ (by positivity : 0≤1+|t|+|t|+height)
      (show 1+|t|+|t|+height≤2*(1+|t|+height) by linarith) d
    rw [mul_pow] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase hd) (by positivity))
  calc
    _≤C*diagonalControl Φ*(p.control U)^2*(2^d*(1+|t|+height)^D)*Z^ε := by gcongr
    _=(C*2^d)*diagonalControl Φ*(p.control U)^2*(1+|t|+height)^D*Z^ε := by ring
    _≤_ := by gcongr

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.source_control_promote
