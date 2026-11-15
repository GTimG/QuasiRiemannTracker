/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Literal rational return polynomial at the finite target. Uses ArviFoxy's
Q2/Bernstein engine (Apache-2.0), Sil's marked count, and Collet's native count.
All geometry and the old-count kappa are recomputed at the new target. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.FiniteScheme
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.BoundsCore

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorZeroLoss.Finite.ReturnQ
open QRH.ArviReturnTuning QRH.ArviReturnTuning.Q2
open QRH.PositiveGap.ReturnTuning (toQ)

def thetaQ : ℚ := 87334587/100000000
def hQ : ℚ := 8153237/10000000
def ellQ : ℚ := 11/3-4*thetaQ
def yQ : ℚ := hQ-2*ellQ
def kappaQ : ℚ := 2*thetaQ-1
def reserveQ : ℚ := 1/1000000000000

def edgeD (e : Fin 4) : ℚ := ![1/200,19/25,19/25,hQ+1/10000000000] e

def edgeC (e : Fin 4) : ℚ :=
  if e.val < 2 then min (edgeD e) (2*yQ-edgeD e)/(6*kappaQ)
  else min ((3/40)*edgeD e)
    ((2*yQ-(2-999999999999/1000000000000)*edgeD e)/(200000000001/100000000000))

inductive Code | old | native | nativeLow | improved deriving DecidableEq, Repr

def oldD : Q2 := sub (sub (C 3) Y) (smul (2/(3*kappaQ)) Y)
def oldC : Q2 := mul (smul 2 (sub (C 1) Y)) (sub (C 1) (smul (1/(3*kappaQ)) Y))
def oldJ : Q2 := add (mul BranchQ.Vq oldD) (mul X oldC)
def oldN : Q2 := add (mul (sub (C 1) X) oldJ) (smul (1/2) (mul (mul X oldC) BranchQ.Vq))

def J : Code → Q2
  | .old => oldJ
  | .native | .nativeLow => (toQ .C).Jq
  | .improved => Affine.Return.FiniteQ.JQ

def N : Code → Q2
  | .old => oldN
  | .native | .nativeLow => (toQ .C).Nq
  | .improved => Affine.Return.FiniteQ.NQ

def Ebase (d cap : ℚ) : Q2 :=
  add (C (1/2+13*hQ/75-yQ/2-ellQ/2-9*d/100))
    (add (smul (1/2) X) (smul (ellQ-cap/2) (mul X Y)))

def margin (e : Fin 4) (b : Code) : Q2 :=
  sub (mul (J b) (sub (C (thetaQ-reserveQ)) (Ebase (edgeD e) (edgeC e))))
    (smul (3/4*edgeD e) (N b))

structure Cell where
  edge : Fin 4
  code : Code
  dlo : ℚ
  dhi : ℚ
  plo : ℚ
  phi : ℚ

def Cell.admitted (s : Cell) : Prop := match s.code with
  | .old => True
  | .native => 15/64 ≤ s.dlo ∧ s.dhi ≤ 9/16 ∧ 9/32 ≤ s.plo ∧ s.phi ≤ 1/2
  | .nativeLow => 15/64 ≤ s.dlo ∧ s.dhi ≤ 1/2 ∧ 3/16 ≤ s.plo ∧ s.phi ≤ 1/2
  | .improved => 189/512 ≤ s.dlo ∧ s.dhi ≤ 15/32 ∧ 15/32 ≤ s.plo ∧ s.phi ≤ 1/2
instance (s : Cell) : Decidable s.admitted := by unfold Cell.admitted; split <;> infer_instance

def Cell.ok (s : Cell) : Bool := decide s.admitted &&
  bernCheck (margin s.edge s.code) s.dlo s.dhi s.plo s.phi

theorem Cell.margin_pos (s : Cell) (hs : s.ok = true) {δ p : ℝ}
    (hd0 : (s.dlo:ℝ) ≤ δ) (hd1 : δ ≤ s.dhi)
    (hp0 : (s.plo:ℝ) ≤ p) (hp1 : p ≤ s.phi) :
    0 < Q2.ev (margin s.edge s.code) δ p := by
  have h := hs
  simp only [Cell.ok,Bool.and_eq_true] at h
  exact bernCheck_sound _ _ _ _ _ h.2 hd0 hd1 hp0 hp1

end Qrh.TwoSlot.AnchorZeroLoss.Finite.ReturnQ
