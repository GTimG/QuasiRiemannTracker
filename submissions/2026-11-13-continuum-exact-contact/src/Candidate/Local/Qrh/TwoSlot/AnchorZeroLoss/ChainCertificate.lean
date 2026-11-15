/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Generic finite rational certificate for the zero-stage-decrement anchor chain.
The underlying gain and stage gates are Sil's PR137 formulas. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.ChainCheck

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorZeroLoss.Certificate
open Qrh.TwoSlot.AnchorExtension.ChainData

def pad : ℚ := 1/10^13
def witnessPad : ℚ := 1/10^12
def highReserve : ℚ := 3/10^11
def targetG0 : ℚ := 2902544862471/(5*10^13)
def targetG1 : ℚ := 1899637920999/(25*10^12)

/-- Only the actual stage inputs are data. Gain, HIGH price, witness cuts
and output comparisons are recalculated by the kernel checker. -/
structure Stage where
  R : ℚ
  left : ℚ
  gain : ℚ
  cut : ℚ
  a0 : ℚ
  a1 : ℚ
  deriving Inhabited

def Stage.Y (s : Stage) (r : ℚ) : ℚ := fY s.R s.gain s.cut r
def Stage.line (s : Stage) (r : ℚ) : ℚ := fline s.a0 s.a1 r
def Stage.w (s : Stage) (r nu : ℚ) : ℚ :=
  fg s.R s.gain s.cut s.a0 s.a1 r nu / fH s.R r + witnessPad

/-- The fourteen gates at a single endpoint, with the new positive HIGH
reserve and witness shift. The ordinary/reference gates are unchanged. -/
def Stage.gates (s : Stage) (r : ℚ) : List ℚ :=
  let H := fH s.R r
  let u := fu s.R r
  let S := fS s.R s.gain s.cut r
  let s0 := fs s.R s.gain s.cut r
  let whi := s.w r (3/4)
  let sig := (1-whi)/2+s.a0-s.a1*whi
  [H*fF0 s.R s.gain s.cut s.a0 s.a1-highReserve,
   137/1000-S, 14/100-S/H, 9/10-r-S-4*u, 91/100-r-S-4*u,
   5/6+21/250-r-S-3*u-1/100,
   3*H-2*r-8*s0-1/5, r-1/2-s.Y r+u-1/5,
   r/2-s0-(3/2)*(5/6-s.cut)*(u/(s.cut*s.cut))/(1/2-s.a1)-1/10,
   H+u-H/6-1/15-(3/4)*r-s0-3/100,
   s.w r s.cut-2/3, 79/100-whi,
   1-(3/4)*whi-(3/4)*max 0 sig-1/6,
   79/100-r-(2+1/10^11)*u]

def Stage.basic (s : Stage) : Prop :=
  7/10 ≤ s.R ∧ s.R ≤ 311/400 ∧
  1467/2000 ≤ s.left ∧ s.left < s.R ∧
  45457/125000 ≤ s.cut ∧ s.cut < 1/2 ∧ 0 ≤ s.gain ∧
  0 ≤ s.a1 ∧ s.a1 < 2/5 ∧
  fu s.R s.left ≤ 1/10000 ∧
  (s.R ≤ fwb s.R s.gain s.a0 s.a1) ∧
  (s.a0 = 0 ∧ s.a1 = 0 ∨ s.line (311/400) < 0 ∧ 0 < s.a1) ∧
  (s.line s.R ≤ s.gain) ∧
  (fline targetG0 targetG1 s.left + pad < s.Y s.left) ∧
  (fline targetG0 targetG1 s.R + pad < s.Y s.R)

instance (s : Stage) : Decidable s.basic := by unfold Stage.basic; infer_instance

def Stage.ok (s : Stage) : Bool :=
  decide s.basic && (s.gates s.left).all (fun x => decide (0 < x)) &&
    (s.gates s.R).all (fun x => decide (0 < x))

def Adjacent (s t : Stage) : Prop :=
  t.R = s.left ∧ t.gain ≤ s.Y s.left ∧ s.a1 ≤ t.a1 ∧
  t.line s.R ≤ s.line s.R ∧
  t.line s.left+pad < s.Y s.left ∧ t.line s.R+pad < s.Y s.R

instance (s t : Stage) : Decidable (Adjacent s t) := by unfold Adjacent; infer_instance

theorem Stage.ok_sound {s : Stage} (h : s.ok = true) :
    s.basic ∧ (∀x∈s.gates s.left,0 < x) ∧ (∀x∈s.gates s.R,0 < x) := by
  simp only [Stage.ok, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  exact ⟨h.1.1,h.1.2,h.2⟩

end Qrh.TwoSlot.AnchorZeroLoss.Certificate
