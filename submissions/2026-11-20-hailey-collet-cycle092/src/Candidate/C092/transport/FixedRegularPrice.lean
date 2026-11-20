/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The grouped-frame price for P.2; its radius term pays moving sixth-power
cofactors and its strict constant fits the first-side gain. -/
import Candidate.C092.transport.FixedFrameTerminal
import Submissions.sil_density_split_20261026.CubeFree.Price
set_option autoImplicit false
noncomputable section
open QRH.SilDensitySplit.CubeFree
namespace QRH.Cycle092.PackedPrice
open QRH.SourceCertificate

def terminalReserve : ℝ := (rho:ℝ)/8

theorem terminalReserve_pos : 0 < terminalReserve := by norm_num [terminalReserve,rho]

def regular (reserve : ℝ) (hs : reserve ≤ (u:ℝ)) : Price where
  f := fun _ _ _ M=>(u:ℝ)-reserve+(5/6)*max 0 ((H:ℝ)-M)
  nonneg := by
    intro _ _ _ M
    have h:0≤(u:ℝ)-reserve:=sub_nonneg.mpr hs
    linarith [le_max_left 0 ((H:ℝ)-M)]
  mono := by intro;intros;rfl
  lip := 5/6
  lip_nonneg := by norm_num
  lipP := by intros;linarith
  lipS := by intros;linarith
  lipM := by
    intro w P s M e
    have h : max 0 ((H:ℝ)-(M+e)) ≤ max 0 ((H:ℝ)-M)+|e| := by
      apply max_le <;> linarith [le_max_left 0 ((H:ℝ)-M),le_max_right 0 ((H:ℝ)-M),abs_nonneg e,neg_abs_le e]
    linarith

theorem actual_leaf_loss (reserve : ℝ) (hs : reserve ≤ (u:ℝ)) (w p s M:ℝ) :
    (regular reserve hs).f w p s M-(5/6)*max 0 ((H:ℝ)-M)=(u:ℝ)-reserve := by
  unfold regular;dsimp;ring

/-- In a filled admissible frame the dual-radius collar costs at most
five sixths of its actual width. -/
theorem filled (reserve : ℝ) (hs : reserve ≤ (u:ℝ)) (w p s M collar:ℝ) (h:0≤collar) (hM:(H:ℝ)≤M+collar) :
    (regular reserve hs).f w p s M ≤ (u:ℝ)-reserve+(5/6)*collar := by
  have hm:max 0 ((H:ℝ)-M)≤collar:=max_le h (by linarith)
  change (u:ℝ)-reserve+(5/6)*max 0 ((H:ℝ)-M) ≤ _
  linarith

theorem terminalReserve_le : terminalReserve ≤ (u:ℝ) := by norm_num [terminalReserve,rho,u]

theorem fee_budget (a b c : ℝ) (ha : a ≤ (rho:ℝ)/32) (hb : b ≤ (rho:ℝ)/32)
    (hc : c ≤ (rho:ℝ)/32) :
    (u:ℝ)-terminalReserve+a+b+c ≤ (u:ℝ)-(rho:ℝ)/32 := by
  unfold terminalReserve
  linarith

#print axioms actual_leaf_loss
#print axioms filled
end QRH.Cycle092.PackedPrice
