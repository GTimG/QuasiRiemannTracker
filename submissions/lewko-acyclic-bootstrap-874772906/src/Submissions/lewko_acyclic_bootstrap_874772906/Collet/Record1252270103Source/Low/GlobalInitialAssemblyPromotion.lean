/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialAssemblyControl
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.Contract
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open QRH.Record1252270103Source

theorem source_control_promote_standard {a b : ℝ} (p : Profiles a b) (Φ : 𝓢(ℝ,ℂ))
    (S U : Finset (ℕ×ℕ)) (hS : S⊆U) (d D : ℕ) (hd : d≤D)
    (C C' t height Z ε : ℝ) (hC : 0≤C) (hCC : C*2^d≤C') (hh : 0≤height) (hZ : 0≤Z) :
    C*diagonalControl Φ*(p.control S)^2*(1+|t|+height)^d*Z^ε≤
      C'*diagonalControl Φ*(p.control U)^2*(1+|t|+height)^D*Z^ε := by
  apply le_trans _ (source_control_promote p Φ S U hS d D hd C C' t height Z ε hC hCC hh hZ)
  have hdiag:=diagonalControl_nonneg Φ
  have h0 : 0≤1+|t|+height:=by positivity
  have h1 : 1+|t|+height≤1+|t|+|t|+height:=by linarith [abs_nonneg t]
  gcongr

theorem inherit_lower_width {B lam cap B₀ lam₀ cap₀ cross m₁ m₂ s : ℝ}
    (hlam : 0≤lam) (hL : lam≤lam₀) (hcross : cross≤cap₀)
    (hbudget : B-B₀+(lam₀-lam)*cross≤0)
    (hm₁ : 0≤m₁) (hm₂ : 0≤m₂) (hs : 0≤s) (hsc : s≤cross)
    (hadm : (globalFace B lam cap).Admissible m₁ m₂ s 1) :
    (globalFace B₀ lam₀ cap₀).Admissible m₁ m₂ s 1 := by
  apply globalFace_inherit hm₁ hm₂ hs hlam (hlam.trans hL) hadm
  · simpa using hsc.trans hcross
  · have h:=mul_le_mul_of_nonneg_left hsc (sub_nonneg.mpr hL)
    nlinarith only [h,hbudget]

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.source_control_promote_standard
#print axioms QRH.Record1252270103Low.inherit_lower_width
