/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/

import Candidate.Local.Qrh.JointDetector.RepeatedMarks.FractionHighData

namespace Qrh.JointDetector.RepeatedMarks.FractionCurveData

set_option autoImplicit false

open FractionArithmetic

def affineCapPower (B L c a0 a1 s : Fraction) (i : Fin 6) (j : Fin 5) : Fraction :=
  match i.val,j.val with

  | 0,2 => (25/144:Fraction)*a0^3*s + (-25/144:Fraction)*c*a0^3

  | 1,1 => (-25/12:Fraction)*a0^2*s + (25/12:Fraction)*c*a0^2

  | 1,2 => (25/48:Fraction)*a0^2*a1*s + (5/12:Fraction)*a0^3*s + (-25/48:Fraction)*c*a0^2*a1

  | 2,0 => (-25/36:Fraction)*a0 + (25/4:Fraction)*a0*s + (-25/12:Fraction)*c*a0

  | 2,1 => (-25/6:Fraction)*a0*a1*s + (-5/3:Fraction)*a0^2*s + (25/6:Fraction)*c*a0*a1 + (-10/3:Fraction)*c*a0^2

  | 2,2 => (25/48:Fraction)*a0*a1^2*s + (5/4:Fraction)*a0^2*a1*s + (1/4:Fraction)*a0^3*s + (-25/48:Fraction)*c*a0*a1^2 + (1/4:Fraction)*c*a0^3

  | 3,0 => (-25/36:Fraction)*a1 + (25/4:Fraction)*a1*s + (5/3:Fraction)*a0 + (-5:Fraction)*a0*s + (-25/12:Fraction)*c*a1 + (10/3:Fraction)*c*a0

  | 3,1 => (-25/12:Fraction)*a1^2*s + (-10/3:Fraction)*a0*a1*s + (1:Fraction)*a0^2*s + (25/12:Fraction)*c*a1^2 + (-20/3:Fraction)*c*a0*a1 + (1:Fraction)*c*a0^2

  | 3,2 => (25/144:Fraction)*a1^3*s + (5/4:Fraction)*a0*a1^2*s + (3/4:Fraction)*a0^2*a1*s + (-25/144:Fraction)*c*a1^3 + (3/4:Fraction)*c*a0^2*a1

  | 4,0 => (5/3:Fraction)*a1 + (-5:Fraction)*a1*s + (-1:Fraction)*a0 + (1:Fraction)*a0*s + (10/3:Fraction)*c*a1 + (-1:Fraction)*c*a0

  | 4,1 => (-5/3:Fraction)*a1^2*s + (2:Fraction)*a0*a1*s + (-10/3:Fraction)*c*a1^2 + (2:Fraction)*c*a0*a1

  | 4,2 => (5/12:Fraction)*a1^3*s + (3/4:Fraction)*a0*a1^2*s + (3/4:Fraction)*c*a0*a1^2

  | 5,0 => (-1:Fraction)*a1 + (1:Fraction)*a1*s + (-1:Fraction)*c*a1

  | 5,1 => (1:Fraction)*a1^2*s + (1:Fraction)*c*a1^2

  | 5,2 => (1/4:Fraction)*a1^3*s + (1/4:Fraction)*c*a1^3

  | _,_ => 0

def affineBudgetPower (B L c a0 a1 s : Fraction) (i : Fin 6) (j : Fin 5) : Fraction :=
  match i.val,j.val with

  | 0,2 => (25/144:Fraction)*a0^3*s + (25/18:Fraction)*(1/L)*a0^3*s + (25/9:Fraction)*(1/L)^2*a0^3*s + (-25/144:Fraction)*B*(1/L)*a0^3 + (-25/36:Fraction)*B*(1/L)^2*a0^3

  | 0,3 => (-5/6:Fraction)*(1/L)*a0^4*s + (-10/3:Fraction)*(1/L)^2*a0^4*s

  | 0,4 => (1:Fraction)*(1/L)^2*a0^5*s

  | 1,1 => (-25/12:Fraction)*a0^2*s + (-25/3:Fraction)*(1/L)*a0^2*s + (25/12:Fraction)*B*(1/L)*a0^2

  | 1,2 => (25/48:Fraction)*a0^2*a1*s + (5/12:Fraction)*a0^3*s + (25/6:Fraction)*(1/L)*a0^2*a1*s + (5/12:Fraction)*(1/L)*a0^3 + (20/3:Fraction)*(1/L)*a0^3*s + (25/3:Fraction)*(1/L)^2*a0^2*a1*s + (-25/48:Fraction)*B*(1/L)*a0^2*a1 + (-25/12:Fraction)*B*(1/L)^2*a0^2*a1 + (5/3:Fraction)*B*(1/L)^2*a0^3

  | 1,3 => (-10/3:Fraction)*(1/L)*a0^3*a1*s + (-1:Fraction)*(1/L)*a0^4*s + (-40/3:Fraction)*(1/L)^2*a0^3*a1*s

  | 1,4 => (5:Fraction)*(1/L)^2*a0^4*a1*s

  | 2,0 => (-25/36:Fraction)*a0 + (25/4:Fraction)*a0*s + (25/18:Fraction)*(1/L)*a0 + (-25/12:Fraction)*B*(1/L)*a0

  | 2,1 => (-25/6:Fraction)*a0*a1*s + (-5/3:Fraction)*a0^2*s + (-50/3:Fraction)*(1/L)*a0*a1*s + (-5/3:Fraction)*(1/L)*a0^2 + (10/3:Fraction)*(1/L)*a0^2*s + (25/6:Fraction)*B*(1/L)*a0*a1 + (-10/3:Fraction)*B*(1/L)*a0^2

  | 2,2 => (25/48:Fraction)*a0*a1^2*s + (5/4:Fraction)*a0^2*a1*s + (1/4:Fraction)*a0^3*s + (25/6:Fraction)*(1/L)*a0*a1^2*s + (5/4:Fraction)*(1/L)*a0^2*a1 + (20:Fraction)*(1/L)*a0^2*a1*s + (-1/2:Fraction)*(1/L)*a0^3 + (-2:Fraction)*(1/L)*a0^3*s + (25/3:Fraction)*(1/L)^2*a0*a1^2*s + (-25/48:Fraction)*B*(1/L)*a0*a1^2 + (1/4:Fraction)*B*(1/L)*a0^3 + (-25/12:Fraction)*B*(1/L)^2*a0*a1^2 + (5:Fraction)*B*(1/L)^2*a0^2*a1 + (-1:Fraction)*B*(1/L)^2*a0^3

  | 2,3 => (-5:Fraction)*(1/L)*a0^2*a1^2*s + (-4:Fraction)*(1/L)*a0^3*a1*s + (-20:Fraction)*(1/L)^2*a0^2*a1^2*s

  | 2,4 => (10:Fraction)*(1/L)^2*a0^3*a1^2*s

  | 3,0 => (-25/36:Fraction)*a1 + (25/4:Fraction)*a1*s + (5/3:Fraction)*a0 + (-5:Fraction)*a0*s + (25/18:Fraction)*(1/L)*a1 + (-5/3:Fraction)*(1/L)*a0 + (-25/12:Fraction)*B*(1/L)*a1 + (10/3:Fraction)*B*(1/L)*a0

  | 3,1 => (-25/12:Fraction)*a1^2*s + (-10/3:Fraction)*a0*a1*s + (1:Fraction)*a0^2*s + (-25/3:Fraction)*(1/L)*a1^2*s + (-10/3:Fraction)*(1/L)*a0*a1 + (20/3:Fraction)*(1/L)*a0*a1*s + (2:Fraction)*(1/L)*a0^2 + (25/12:Fraction)*B*(1/L)*a1^2 + (-20/3:Fraction)*B*(1/L)*a0*a1 + (1:Fraction)*B*(1/L)*a0^2

  | 3,2 => (25/144:Fraction)*a1^3*s + (5/4:Fraction)*a0*a1^2*s + (3/4:Fraction)*a0^2*a1*s + (25/18:Fraction)*(1/L)*a1^3*s + (5/4:Fraction)*(1/L)*a0*a1^2 + (20:Fraction)*(1/L)*a0*a1^2*s + (-3/2:Fraction)*(1/L)*a0^2*a1 + (-6:Fraction)*(1/L)*a0^2*a1*s + (25/9:Fraction)*(1/L)^2*a1^3*s + (-25/144:Fraction)*B*(1/L)*a1^3 + (3/4:Fraction)*B*(1/L)*a0^2*a1 + (-25/36:Fraction)*B*(1/L)^2*a1^3 + (5:Fraction)*B*(1/L)^2*a0*a1^2 + (-3:Fraction)*B*(1/L)^2*a0^2*a1

  | 3,3 => (-10/3:Fraction)*(1/L)*a0*a1^3*s + (-6:Fraction)*(1/L)*a0^2*a1^2*s + (-40/3:Fraction)*(1/L)^2*a0*a1^3*s

  | 3,4 => (10:Fraction)*(1/L)^2*a0^2*a1^3*s

  | 4,0 => (5/3:Fraction)*a1 + (-5:Fraction)*a1*s + (-1:Fraction)*a0 + (1:Fraction)*a0*s + (-5/3:Fraction)*(1/L)*a1 + (10/3:Fraction)*B*(1/L)*a1 + (-1:Fraction)*B*(1/L)*a0

  | 4,1 => (-5/3:Fraction)*a1^2*s + (2:Fraction)*a0*a1*s + (-5/3:Fraction)*(1/L)*a1^2 + (10/3:Fraction)*(1/L)*a1^2*s + (4:Fraction)*(1/L)*a0*a1 + (-10/3:Fraction)*B*(1/L)*a1^2 + (2:Fraction)*B*(1/L)*a0*a1

  | 4,2 => (5/12:Fraction)*a1^3*s + (3/4:Fraction)*a0*a1^2*s + (5/12:Fraction)*(1/L)*a1^3 + (20/3:Fraction)*(1/L)*a1^3*s + (-3/2:Fraction)*(1/L)*a0*a1^2 + (-6:Fraction)*(1/L)*a0*a1^2*s + (3/4:Fraction)*B*(1/L)*a0*a1^2 + (5/3:Fraction)*B*(1/L)^2*a1^3 + (-3:Fraction)*B*(1/L)^2*a0*a1^2

  | 4,3 => (-5/6:Fraction)*(1/L)*a1^4*s + (-4:Fraction)*(1/L)*a0*a1^3*s + (-10/3:Fraction)*(1/L)^2*a1^4*s

  | 4,4 => (5:Fraction)*(1/L)^2*a0*a1^4*s

  | 5,0 => (-1:Fraction)*a1 + (1:Fraction)*a1*s + (-1:Fraction)*B*(1/L)*a1

  | 5,1 => (1:Fraction)*a1^2*s + (2:Fraction)*(1/L)*a1^2 + (1:Fraction)*B*(1/L)*a1^2

  | 5,2 => (1/4:Fraction)*a1^3*s + (-1/2:Fraction)*(1/L)*a1^3 + (-2:Fraction)*(1/L)*a1^3*s + (1/4:Fraction)*B*(1/L)*a1^3 + (-1:Fraction)*B*(1/L)^2*a1^3

  | 5,3 => (-1:Fraction)*(1/L)*a1^4*s

  | 5,4 => (1:Fraction)*(1/L)^2*a1^5*s

  | _,_ => 0

def affineCapHighPower (B L c a0 a1 H P S u rho : Fraction) (i : Fin 4) (_j : Fin 1) : Fraction :=
  match i.val with

  | 0 => (5/12:Fraction)*a0*rho + (-5/12:Fraction)*a0*u + (5/12:Fraction)*a0^2*S + (-5/12:Fraction)*c*a0^2*H

  | 1 => (-5/2:Fraction)*rho + (5/2:Fraction)*u + (5/12:Fraction)*a1*rho + (-5/12:Fraction)*a1*u + (1/2:Fraction)*a0*rho + (-1/2:Fraction)*a0*u + (-5/2:Fraction)*a0*S + (5/12:Fraction)*a0*P + (5/6:Fraction)*a0*a1*S + (1/2:Fraction)*a0^2*S + (5/6:Fraction)*c*a0*H + (-5/6:Fraction)*c*a0*a1*H + (1/2:Fraction)*c*a0^2*H

  | 2 => (1:Fraction)*rho + (-1:Fraction)*u + (-5/2:Fraction)*P + (5/3:Fraction)*H + (1/2:Fraction)*a1*rho + (-1/2:Fraction)*a1*u + (-5/2:Fraction)*a1*S + (5/12:Fraction)*a1*P + (5/12:Fraction)*a1^2*S + (1:Fraction)*a0*S + (1/2:Fraction)*a0*P + (-1:Fraction)*a0*H + (1:Fraction)*a0*a1*S + (5/6:Fraction)*c*a1*H + (-5/12:Fraction)*c*a1^2*H + (-1:Fraction)*c*a0*H + (1:Fraction)*c*a0*a1*H

  | 3 => (1:Fraction)*P + (1:Fraction)*a1*S + (1/2:Fraction)*a1*P + (-1:Fraction)*a1*H + (1/2:Fraction)*a1^2*S + (-1:Fraction)*c*a1*H + (1/2:Fraction)*c*a1^2*H

  | _ => 0

def affineBudgetHighPower (B L c a0 a1 H P S u rho : Fraction) (i : Fin 4) (_j : Fin 1) : Fraction :=
  match i.val with

  | 0 => (5/12:Fraction)*a0*rho + (-5/12:Fraction)*a0*u + (5/12:Fraction)*a0^2*S + (5/3:Fraction)*(1/L)*a0*rho + (-5/3:Fraction)*(1/L)*a0*u + (-1:Fraction)*(1/L)*a0^2*rho + (1:Fraction)*(1/L)*a0^2*u + (5/3:Fraction)*(1/L)*a0^2*S + (-1:Fraction)*(1/L)*a0^3*S + (-5/12:Fraction)*B*(1/L)*a0^2*H

  | 1 => (-5/2:Fraction)*rho + (5/2:Fraction)*u + (5/12:Fraction)*a1*rho + (-5/12:Fraction)*a1*u + (1/2:Fraction)*a0*rho + (-1/2:Fraction)*a0*u + (-5/2:Fraction)*a0*S + (5/12:Fraction)*a0*P + (5/6:Fraction)*a0*a1*S + (1/2:Fraction)*a0^2*S + (5/3:Fraction)*(1/L)*a1*rho + (-5/3:Fraction)*(1/L)*a1*u + (5/3:Fraction)*(1/L)*a0*P + (-5/3:Fraction)*(1/L)*a0*H + (-2:Fraction)*(1/L)*a0*a1*rho + (2:Fraction)*(1/L)*a0*a1*u + (10/3:Fraction)*(1/L)*a0*a1*S + (-1:Fraction)*(1/L)*a0^2*P + (1:Fraction)*(1/L)*a0^2*H + (-3:Fraction)*(1/L)*a0^2*a1*S + (5/6:Fraction)*B*(1/L)*a0*H + (-5/6:Fraction)*B*(1/L)*a0*a1*H + (1/2:Fraction)*B*(1/L)*a0^2*H

  | 2 => (1:Fraction)*rho + (-1:Fraction)*u + (-5/2:Fraction)*P + (5/3:Fraction)*H + (1/2:Fraction)*a1*rho + (-1/2:Fraction)*a1*u + (-5/2:Fraction)*a1*S + (5/12:Fraction)*a1*P + (5/12:Fraction)*a1^2*S + (1:Fraction)*a0*S + (1/2:Fraction)*a0*P + (-1:Fraction)*a0*H + (1:Fraction)*a0*a1*S + (5/3:Fraction)*(1/L)*a1*P + (-5/3:Fraction)*(1/L)*a1*H + (-1:Fraction)*(1/L)*a1^2*rho + (1:Fraction)*(1/L)*a1^2*u + (5/3:Fraction)*(1/L)*a1^2*S + (-2:Fraction)*(1/L)*a0*a1*P + (2:Fraction)*(1/L)*a0*a1*H + (-3:Fraction)*(1/L)*a0*a1^2*S + (5/6:Fraction)*B*(1/L)*a1*H + (-5/12:Fraction)*B*(1/L)*a1^2*H + (-1:Fraction)*B*(1/L)*a0*H + (1:Fraction)*B*(1/L)*a0*a1*H

  | 3 => (1:Fraction)*P + (1:Fraction)*a1*S + (1/2:Fraction)*a1*P + (-1:Fraction)*a1*H + (1/2:Fraction)*a1^2*S + (-1:Fraction)*(1/L)*a1^2*P + (1:Fraction)*(1/L)*a1^2*H + (-1:Fraction)*(1/L)*a1^3*S + (-1:Fraction)*B*(1/L)*a1*H + (1/2:Fraction)*B*(1/L)*a1^2*H

  | _ => 0

def hCoeff (A D : Fraction) : Fin 3 → Fraction := ![1,D-6*A,0]

def pCoeff (B L s D : Fraction) : Fin 3 → Fraction := ![B-L*s,D*(B-L*s)-L,-D*L]

def sCoeff (s A D : Fraction) : Fin 3 → Fraction := ![s,1+D*s-A,D]

def uCoeff (A : Fraction) : Fin 3 → Fraction := ![0,A,0]

def rCoeff (rho D : Fraction) : Fin 3 → Fraction := ![rho,rho*D,0]

def capPower (B0 L0 c a0 a1 B L s A D rho : Fraction) (i : Fin 4) (j : Fin 3) : Fraction :=
  affineCapHighPower B0 L0 c a0 a1 (hCoeff A D j) (pCoeff B L s D j) (sCoeff s A D j) (uCoeff A j) (rCoeff rho D j) i 0

def budgetPower (B0 L0 c a0 a1 B L s A D rho : Fraction) (i : Fin 4) (j : Fin 3) : Fraction :=
  affineBudgetHighPower B0 L0 c a0 a1 (hCoeff A D j) (pCoeff B L s D j) (sCoeff s A D j) (uCoeff A j) (rCoeff rho D j) i 0

def selectedPower (B0 L0 c a0 a1 B L s A D rho : Fraction) (i : Fin 4) (j : Fin 3) : Fraction :=
  if hi : i.val<3 then FractionHighTemplates.selectedPower a0 a1 (hCoeff A D j) (pCoeff B L s D j) (sCoeff s A D j) (uCoeff A j) (rCoeff rho D j) ⟨i.val,hi⟩ 0 else 0

def tailPower (B0 L0 c a0 a1 B L s A D rho : Fraction) (i : Fin 4) (j : Fin 3) : Fraction :=
  if hi : i.val<3 then FractionHighTemplates.tailPower B0 a0 a1 (hCoeff A D j) (pCoeff B L s D j) (sCoeff s A D j) (uCoeff A j) (rCoeff rho D j) ⟨i.val,hi⟩ 0 else 0

def mapped (a : Fin 4 → Fin 3 → Fraction) (k e0 ev hi : Fraction)
    (h : Fin 4) (l : Fin 6) : Fraction :=
  ![![a 0 0*e0^3 + a 1 0*k*e0^2 + a 2 0*k^2*e0 + a 3 0*k^3,
      (3:Fraction)*a 0 0*e0^2*ev + a 0 1*e0^3 + (2:Fraction)*a 1 0*k*e0*ev + a 1 1*k*e0^2 + a 2 0*k^2*ev + a 2 1*k^2*e0 + a 3 1*k^3,
      (3:Fraction)*a 0 0*e0*ev^2 + (3:Fraction)*a 0 1*e0^2*ev + a 0 2*e0^3 + a 1 0*k*ev^2 + (2:Fraction)*a 1 1*k*e0*ev + a 1 2*k*e0^2 + a 2 1*k^2*ev + a 2 2*k^2*e0 + a 3 2*k^3,
      a 0 0*ev^3 + (3:Fraction)*a 0 1*e0*ev^2 + (3:Fraction)*a 0 2*e0^2*ev + a 1 1*k*ev^2 + (2:Fraction)*a 1 2*k*e0*ev + a 2 2*k^2*ev,
      a 0 1*ev^3 + (3:Fraction)*a 0 2*e0*ev^2 + a 1 2*k*ev^2,
      a 0 2*ev^3],
    ![a 1 0*(hi*e0-k)*e0^2 + (2:Fraction)*a 2 0*k*(hi*e0-k)*e0 + (3:Fraction)*a 3 0*k^2*(hi*e0-k),
      (2:Fraction)*a 1 0*(hi*e0-k)*e0*ev + a 1 0*(hi*ev)*e0^2 + a 1 1*(hi*e0-k)*e0^2 + (2:Fraction)*a 2 0*k*(hi*e0-k)*ev + (2:Fraction)*a 2 0*k*(hi*ev)*e0 + (2:Fraction)*a 2 1*k*(hi*e0-k)*e0 + (3:Fraction)*a 3 0*k^2*(hi*ev) + (3:Fraction)*a 3 1*k^2*(hi*e0-k),
      a 1 0*(hi*e0-k)*ev^2 + (2:Fraction)*a 1 0*(hi*ev)*e0*ev + (2:Fraction)*a 1 1*(hi*e0-k)*e0*ev + a 1 1*(hi*ev)*e0^2 + a 1 2*(hi*e0-k)*e0^2 + (2:Fraction)*a 2 0*k*(hi*ev)*ev + (2:Fraction)*a 2 1*k*(hi*e0-k)*ev + (2:Fraction)*a 2 1*k*(hi*ev)*e0 + (2:Fraction)*a 2 2*k*(hi*e0-k)*e0 + (3:Fraction)*a 3 1*k^2*(hi*ev) + (3:Fraction)*a 3 2*k^2*(hi*e0-k),
      a 1 0*(hi*ev)*ev^2 + a 1 1*(hi*e0-k)*ev^2 + (2:Fraction)*a 1 1*(hi*ev)*e0*ev + (2:Fraction)*a 1 2*(hi*e0-k)*e0*ev + a 1 2*(hi*ev)*e0^2 + (2:Fraction)*a 2 1*k*(hi*ev)*ev + (2:Fraction)*a 2 2*k*(hi*e0-k)*ev + (2:Fraction)*a 2 2*k*(hi*ev)*e0 + (3:Fraction)*a 3 2*k^2*(hi*ev),
      a 1 1*(hi*ev)*ev^2 + a 1 2*(hi*e0-k)*ev^2 + (2:Fraction)*a 1 2*(hi*ev)*e0*ev + (2:Fraction)*a 2 2*k*(hi*ev)*ev,
      a 1 2*(hi*ev)*ev^2],
    ![a 2 0*(hi*e0-k)^2*e0 + (3:Fraction)*a 3 0*k*(hi*e0-k)^2,
      a 2 0*(hi*e0-k)^2*ev + (2:Fraction)*a 2 0*(hi*e0-k)*(hi*ev)*e0 + a 2 1*(hi*e0-k)^2*e0 + (6:Fraction)*a 3 0*k*(hi*e0-k)*(hi*ev) + (3:Fraction)*a 3 1*k*(hi*e0-k)^2,
      (2:Fraction)*a 2 0*(hi*e0-k)*(hi*ev)*ev + a 2 0*(hi*ev)^2*e0 + a 2 1*(hi*e0-k)^2*ev + (2:Fraction)*a 2 1*(hi*e0-k)*(hi*ev)*e0 + a 2 2*(hi*e0-k)^2*e0 + (3:Fraction)*a 3 0*k*(hi*ev)^2 + (6:Fraction)*a 3 1*k*(hi*e0-k)*(hi*ev) + (3:Fraction)*a 3 2*k*(hi*e0-k)^2,
      a 2 0*(hi*ev)^2*ev + (2:Fraction)*a 2 1*(hi*e0-k)*(hi*ev)*ev + a 2 1*(hi*ev)^2*e0 + a 2 2*(hi*e0-k)^2*ev + (2:Fraction)*a 2 2*(hi*e0-k)*(hi*ev)*e0 + (3:Fraction)*a 3 1*k*(hi*ev)^2 + (6:Fraction)*a 3 2*k*(hi*e0-k)*(hi*ev),
      a 2 1*(hi*ev)^2*ev + (2:Fraction)*a 2 2*(hi*e0-k)*(hi*ev)*ev + a 2 2*(hi*ev)^2*e0 + (3:Fraction)*a 3 2*k*(hi*ev)^2,
      a 2 2*(hi*ev)^2*ev],
    ![a 3 0*(hi*e0-k)^3,
      (3:Fraction)*a 3 0*(hi*e0-k)^2*(hi*ev) + a 3 1*(hi*e0-k)^3,
      (3:Fraction)*a 3 0*(hi*e0-k)*(hi*ev)^2 + (3:Fraction)*a 3 1*(hi*e0-k)^2*(hi*ev) + a 3 2*(hi*e0-k)^3,
      a 3 0*(hi*ev)^3 + (3:Fraction)*a 3 1*(hi*e0-k)*(hi*ev)^2 + (3:Fraction)*a 3 2*(hi*e0-k)^2*(hi*ev),
      a 3 1*(hi*ev)^3 + (3:Fraction)*a 3 2*(hi*e0-k)*(hi*ev)^2,
      a 3 2*(hi*ev)^3]] h l

def widthShift (a : Fin 4 → Fin 6 → Fraction) (lo hi : Fraction) (i : Fin 4) (j : Fin 6) : Fraction :=
  ![a i 0 + a i 1*lo + a i 2*lo^2 + a i 3*lo^3 + a i 4*lo^4 + a i 5*lo^5,
    a i 1*(hi-lo) + a i 2*(2:Fraction)*lo*(hi-lo) + a i 3*(3:Fraction)*lo^2*(hi-lo) + a i 4*(4:Fraction)*lo^3*(hi-lo) + a i 5*(5:Fraction)*lo^4*(hi-lo),
    a i 2*(hi-lo)^2 + a i 3*(3:Fraction)*lo*(hi-lo)^2 + a i 4*(6:Fraction)*lo^2*(hi-lo)^2 + a i 5*(10:Fraction)*lo^3*(hi-lo)^2,
    a i 3*(hi-lo)^3 + a i 4*(4:Fraction)*lo*(hi-lo)^3 + a i 5*(10:Fraction)*lo^2*(hi-lo)^3,
    a i 4*(hi-lo)^4 + a i 5*(5:Fraction)*lo*(hi-lo)^4,
    a i 5*(hi-lo)^5] j

structure Params where

  B0 : Fraction

  L0 : Fraction

  c0 : Fraction

  B : Fraction

  L : Fraction

  c : Fraction

  A : Fraction

  D : Fraction

structure Cell where

  lo : Fraction

  hi : Fraction

  vl : Fraction

  vh : Fraction

  a0 : Fraction

  a1 : Fraction

  k : Fraction

  e0 : Fraction

  ev : Fraction

def crossing (p : Params) : Fraction := (p.B0-p.B)/(p.L0-p.L)

def cutNumerator (p : Params) (phi : Fraction) : Fraction := phi*p.L0*p.A

def cutIntercept (p : Params) : Fraction := p.L0-p.L+(6*p.B0-p.L0)*p.A

def matchedCut (p : Params) (phi v : Fraction) : Fraction := cutNumerator p phi/(cutIntercept p+(p.L0-p.L)*p.D*v)

def amplitudeFloor : Fraction := 250001/500000

def clippingWidth (p : Params) (phi ray : Fraction) : Fraction := (cutNumerator p phi/(amplitudeFloor/ray)-cutIntercept p)/((p.L0-p.L)*p.D)

def rayCell (p : Params) (phi ray : Fraction) : Cell :=
  ⟨matchedCut p phi (p.c-crossing p),3/4,0,p.c-crossing p,0,ray,cutNumerator p phi,cutIntercept p,(p.L0-p.L)*p.D⟩

def constantCell (p : Params) (phi ray : Fraction) : Cell :=
  ⟨matchedCut p phi (p.c-crossing p),amplitudeFloor/ray,clippingWidth p phi ray,p.c-crossing p,amplitudeFloor,0,cutNumerator p phi,cutIntercept p,(p.L0-p.L)*p.D⟩

def lateRayCell (p : Params) (phi ray : Fraction) : Cell :=
  ⟨amplitudeFloor/ray,3/4,clippingWidth p phi ray,p.c-crossing p,0,ray,amplitudeFloor/ray,1,0⟩

def earlyRayCell (p : Params) (phi ray : Fraction) : Cell :=
  ⟨amplitudeFloor/ray,3/4,0,clippingWidth p phi ray,0,ray,cutNumerator p phi,cutIntercept p,(p.L0-p.L)*p.D⟩

def highReserve : Fraction := 1/10000000000000

def cellPower (p : Params) (cell : Cell) (i : Fin 4) : Fin 4 → Fin 3 → Fraction :=
  match i.val with
  | 0 => capPower p.B0 p.L0 (1/10) cell.a0 cell.a1 p.B p.L (crossing p) p.A p.D highReserve
  | 1 => budgetPower p.B0 p.L0 (1/10) cell.a0 cell.a1 p.B p.L (crossing p) p.A p.D highReserve
  | 2 => tailPower p.B0 p.L0 (1/10) cell.a0 cell.a1 p.B p.L (crossing p) p.A p.D highReserve
  | _ => selectedPower p.B0 p.L0 (1/10) cell.a0 cell.a1 p.B p.L (crossing p) p.A p.D highReserve

def Signs (p : Params) (cell : Cell) (combined : Bool) : Prop :=
  (∀ i j, 0 ≤ (FractionHighTemplates.fast54 (affineCapPower p.B0 p.L0 (1/10) cell.a0 cell.a1 (crossing p)) cell.lo cell.hi i j).num) ∧
  (∀ i j, 0 ≤ (FractionHighTemplates.fast54 (affineBudgetPower p.B0 p.L0 (1/10) cell.a0 cell.a1 (crossing p)) cell.lo cell.hi i j).num) ∧
  (∀ i : Fin 4, i.val < 3 ∨ combined = true → ∀ j k,
    0 ≤ (FractionHighTemplates.fast35
      (widthShift (mapped (cellPower p cell i) cell.k cell.e0 cell.ev cell.hi) cell.vl cell.vh) 0 1 j k).num)

end Qrh.JointDetector.RepeatedMarks.FractionCurveData
