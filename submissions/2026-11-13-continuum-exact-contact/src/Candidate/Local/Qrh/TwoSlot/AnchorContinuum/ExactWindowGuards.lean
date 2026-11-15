/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Uniform count-window guard certificate over the exact tangent's coefficient
enclosure. Formulas are Sil's PR137 window with the inherited Collet native
counts; certification uses ArviFoxy's rational polynomial engine (Apache-2.0). -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ContactCapacity
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.CountWindow

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Qrh.TwoSlot.AnchorContinuum.Contact.WindowGuards
noncomputable section
open Set QRH.ArviReturnTuning QRH.ArviReturnTuning.Q2
open QRH.PositiveGap.Return QRH.PositiveGap.ReturnTuning
open Qrh.MarkedAnchor.Interface (anchorLeft anchorTop)

def lo0 : ℚ := 5805911/100000000
def hi0 : ℚ := 5805913/100000000
def lo1 : ℚ := 3799809/50000000
def hi1 : ℚ := 379981/5000000

def k (a1 p : ℝ) : ℝ := 1-p*(1+2*a1)
def J (a1 d p : ℝ) : ℝ := 3*(5/6-d)+2*d*k a1 p
def U (a0 a1 p : ℝ) : ℝ := 1-p*(1+6*a0-4*a1)
def N (a0 a1 d p : ℝ) : ℝ := (1-d)*J a1 d p+(5/6-d)*d*U a0 a1 p
def T (a0 a1 d p : ℝ) : ℝ := J a1 d p+d*U a0 a1 p
def below (a0 a1 d p c0 c1 : ℝ) : ℝ := N a0 a1 d p-(1-d*(c0+c1*p))*J a1 d p

def guard (a0 a1 d p : ℝ) : Fin 10 → ℝ :=
  ![k a1 p,J a1 d p,T a0 a1 d p-J a1 d p,
    (12499/10000)*J a1 d p-T a0 a1 d p,
    2*T a0 a1 d p-3*(anchorLeft+1/1000000)*J a1 d p,
    below a0 a1 d p anchorTop (1-anchorTop),
    below a0 a1 d p anchorTop (2*(countCB-anchorTop)/countCL),
    below a0 a1 d p anchorTop (2*(countCap-1/10000000)),
    N a0 a1 d p-(1-2*naturalM*d-2*sMinus*d*p)*J a1 d p,
    U a0 a1 p*(-2*(1+2*a1)*d)+(1+6*a0-4*a1)*J a1 d p]

def kQ (a1 : ℚ) : Q2 := sub (C 1) (smul (1+2*a1) Y)
def VQ : Q2 := sub (C (5/6)) X
def JQ (a1 : ℚ) : Q2 := add (smul 3 VQ) (smul 2 (mul X (kQ a1)))
def UQ (a0 a1 : ℚ) : Q2 := sub (C 1) (smul (1+6*a0-4*a1) Y)
def NQ (a0 a1 : ℚ) : Q2 := add (mul (sub (C 1) X) (JQ a1)) (mul (mul VQ X) (UQ a0 a1))
def TQ (a0 a1 : ℚ) : Q2 := add (JQ a1) (mul X (UQ a0 a1))
def belowQ (a0 a1 c0 c1 : ℚ) : Q2 :=
  sub (NQ a0 a1) (mul (sub (C 1) (mul X (add (C c0) (smul c1 Y)))) (JQ a1))
def guardQ (a0 a1 : ℚ) : Fin 10 → Q2 :=
  ![kQ a1,JQ a1,sub (TQ a0 a1) (JQ a1),sub (smul (12499/10000) (JQ a1)) (TQ a0 a1),
    sub (smul 2 (TQ a0 a1)) (smul (3*(1467/2000+1/1000000)) (JQ a1)),
    belowQ a0 a1 (311/400) (1-311/400),
    belowQ a0 a1 (311/400) (2*(countBQ-311/400)/countLQ),
    belowQ a0 a1 (311/400) (2*(countCapQ-1/10000000)),
    sub (NQ a0 a1) (mul (sub (sub (C 1) (smul (2*naturalMQ) X))
      (smul (2*sMinusQ) (mul X Y))) (JQ a1)),
    sub (mul (UQ a0 a1) (smul (-2*(1+2*a1)) X))
      (smul (-(1+6*a0-4*a1)) (JQ a1))]

theorem ev_guard (a0 a1 : ℚ) (j : Fin 10) (d p : ℝ) :
    Q2.ev (guardQ a0 a1 j) d p = guard a0 a1 d p j := by
  fin_cases j <;>
    simp [guardQ,guard,kQ,VQ,JQ,UQ,NQ,TQ,belowQ,k,J,U,N,T,below,
      ev_add,ev_sub,ev_mul,ev_smul,ev_C,ev_X,ev_Y,
      anchorLeft,anchorTop,countCB,countCL,countCap,countBQ,countLQ,countCapQ,
      naturalM,naturalMQ,naturalK,naturalKQ,sMinus,sMinusQ] <;> push_cast <;> ring <;> simp

def corner0 (i : Fin 2) : ℚ := ![lo0,hi0] i
def corner1 (i : Fin 2) : ℚ := ![lo1,hi1] i

theorem corners_checked : ∀ a b : Fin 2, ∀ j : Fin 10,
    posBox (guardQ (corner0 a) (corner1 b) j) 0 (189/512) (15/32) (15/32) (1/2) = true := by
  decide +kernel

theorem corner_pos (a b : Fin 2) (j : Fin 10) {d p : ℝ}
    (hd : d ∈ Icc (189/512:ℝ) (15/32)) (hp : p ∈ Icc (15/32:ℝ) (1/2)) :
    0 < guard (corner0 a) (corner1 b) d p j := by
  rw [←ev_guard]
  exact posBox_sound _ _ _ _ _ _ (corners_checked a b j)
    (by simpa using hd.1) (by simpa using hd.2)
    (by simpa using hp.1) (by simpa using hp.2)

theorem affine_first (a1 d p : ℝ) (j : Fin 10) (a0 : ℝ) :
    guard a0 a1 d p j = guard 0 a1 d p j+(guard 1 a1 d p j-guard 0 a1 d p j)*a0 := by
  fin_cases j <;> simp [guard,k,J,U,N,T,below] <;> ring

theorem affine_second (a0 d p : ℝ) (j : Fin 10) (a1 : ℝ) :
    guard a0 a1 d p j = guard a0 0 d p j+(guard a0 1 d p j-guard a0 0 d p j)*a1 := by
  fin_cases j <;> simp [guard,k,J,U,N,T,below] <;> ring

theorem enclosure_pos {a0 a1 d p : ℝ}
    (h0 : (lo0:ℝ) ≤ a0 ∧ a0 ≤ (hi0:ℝ))
    (h1 : (lo1:ℝ) ≤ a1 ∧ a1 ≤ (hi1:ℝ))
    (hd : d ∈ Icc (189/512:ℝ) (15/32)) (hp : p ∈ Icc (15/32:ℝ) (1/2))
    (j : Fin 10) : 0 < guard a0 a1 d p j := by
  apply Qrh.MarkedAnchor.Price.pos_affine (affine_first a1 d p j)
    (show (lo0:ℝ) < (hi0:ℝ) by norm_num [lo0,hi0]) h0.1 h0.2
  · apply Qrh.MarkedAnchor.Price.pos_affine (affine_second lo0 d p j)
      (show (lo1:ℝ) < (hi1:ℝ) by norm_num [lo1,hi1]) h1.1 h1.2
    · simpa [corner0,corner1] using corner_pos 0 0 j hd hp
    · simpa [corner0,corner1] using corner_pos 0 1 j hd hp
  · apply Qrh.MarkedAnchor.Price.pos_affine (affine_second hi0 d p j)
      (show (lo1:ℝ) < (hi1:ℝ) by norm_num [lo1,hi1]) h1.1 h1.2
    · simpa [corner0,corner1] using corner_pos 1 0 j hd hp
    · simpa [corner0,corner1] using corner_pos 1 1 j hd hp

theorem exact_guards (j : Fin 10) {d p : ℝ}
    (hd : d ∈ Icc (189/512:ℝ) (15/32)) (hp : p ∈ Icc (15/32:ℝ) (1/2)) :
    0 < guard tangentIntercept (-tangentSlope) d p j := by
  have hc := tangent_coefficient_bounds
  apply enclosure_pos (by simpa [lo0,hi0] using ⟨hc.1.le,hc.2.1.le⟩)
    (by simpa [lo1,hi1] using ⟨hc.2.2.1.le,hc.2.2.2.le⟩) hd hp j

end
end Qrh.TwoSlot.AnchorContinuum.Contact.WindowGuards
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.WindowGuards.exact_guards
