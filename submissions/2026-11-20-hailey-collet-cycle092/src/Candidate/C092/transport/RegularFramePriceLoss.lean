/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Keep the positive native unmarked-source loss explicit at exhaustion,
including prefixes and residual slot sets of width zero. -/
import Candidate.C092.transport.RegularFrameHeightBudget
set_option autoImplicit false
noncomputable section
open QRH.SilDensitySplit.CubeFree
namespace QRH.Cycle092.PackedPrice

def withLoss (base:Price) (ε:ℝ) (hε:0 ≤ ε) : Price where
  f:=fun w p s M=>base.f w p s M+ε
  nonneg:=fun w p s M=>add_nonneg (base.nonneg w p s M) hε
  mono:=by intro w p p' s s' M h₁ h₂;linarith only [base.mono w p p' s s' M h₁ h₂]
  lip:=base.lip
  lip_nonneg:=base.lip_nonneg
  lipP:=by intro w p s M δ hd;linarith only [base.lipP w p s M δ hd]
  lipS:=by intro w p s M δ hd;linarith only [base.lipS w p s M δ hd]
  lipM:=by intro w p s M δ;linarith only [base.lipM w p s M δ]

theorem exhausted_with_loss (u' p s M ε:ℝ) (he:0 ≤ ε) :
    (withLoss exhausted ε he).f u' p s M-(5/6)*max 0 (1-6*u'-M)=ε := by
  change (5/6)*max 0 (1-6*u'-M)+ε-_=ε
  ring

theorem exhausted_window {u' M collar ε:ℝ} (hε:0 ≤ ε) (hc:0 ≤ collar)
    (hm:1-6*u' ≤ M+collar) (p s:ℝ) :
    (withLoss exhausted ε hε).f u' p s M  ≤  (5/6)*collar+ε := by
  have h:=max_le hc (by linarith:1-6*u'-M ≤ collar)
  change (5/6)*max 0 (1-6*u'-M)+ε  ≤  _
  linarith

#print axioms exhausted_with_loss
#print axioms exhausted_window
end QRH.Cycle092.PackedPrice
