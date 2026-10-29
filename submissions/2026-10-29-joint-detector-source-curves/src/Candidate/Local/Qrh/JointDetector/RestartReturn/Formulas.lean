/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/
/- Modified by Sil (2026-10-26): branches reduced to `old`, the count face `C` and the capped physical
face `capP` (the only branches used by the certificate on the four conductor edges); the literals
`2/5` (plain floor) and `17/500` (tail slope) are replaced by `mMinus = 19/50`, `sMinus = 3/100`;
the row margin uses the certificate reserve `reserve` in place of `rowFee`. -/
import Submissions.hailey_collet_1252270103.Record12518109.Bernstein
import Candidate.Local.Qrh.JointDetector.RestartReturn.Constants
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.RestartReturn
noncomputable section

inductive CountBranch | old | Cnew | Pnew | Cphys | Cold | Pold | Cphysold | Pwide | Pcount | Pcountmid | Cbridge0 | Cbridge1 | Cbridge2 | Cbridge3 | Cbridge4 | Cbridge5 | Cbridge6
 deriving DecidableEq
def branchB : CountBranch → ℝ
 | .old => 0
 | .Cnew => (94429431246019/100000000000000:ℝ)
 | .Pnew => (49136538916807/50000000000000:ℝ)
 | .Cphys => (49136538916807/50000000000000:ℝ)
 | .Cold => (19452098647453/20000000000000:ℝ)
 | .Pold => (3945996453113/4000000000000:ℝ)
 | .Cphysold => (3945996453113/4000000000000:ℝ)
 | .Pwide => (49136538916807/50000000000000:ℝ)
 | .Pcount => (94429431246019/100000000000000:ℝ)
 | .Pcountmid => (94429431246019/100000000000000:ℝ)
 | .Cbridge0 => (24592977418591/25000000000000:ℝ)
 | .Cbridge1 => (48854077528557/50000000000000:ℝ)
 | .Cbridge2 => (96961445541543/100000000000000:ℝ)
 | .Cbridge3 => (19227283965471/20000000000000:ℝ)
 | .Cbridge4 => (47621575591377/50000000000000:ℝ)
 | .Cbridge5 => (47848933494537/50000000000000:ℝ)
 | .Cbridge6 => (94772395367213/100000000000000:ℝ)
def branchL : CountBranch → ℝ
 | .old => 1
 | .Cnew => (342923181897/200000000000:ℝ)
 | .Pnew => (436853181897/200000000000:ℝ)
 | .Cphys => (436853181897/200000000000:ℝ)
 | .Cold => (4230401/2000000:ℝ)
 | .Pold => (4603201/2000000:ℝ)
 | .Cphysold => (4603201/2000000:ℝ)
 | .Pwide => (436853181897/200000000000:ℝ)
 | .Pcount => (342923181897/200000000000:ℝ)
 | .Pcountmid => (342923181897/200000000000:ℝ)
 | .Cbridge0 => (440003181897/200000000000:ℝ)
 | .Cbridge1 => (420003181897/200000000000:ℝ)
 | .Cbridge2 => (400003181897/200000000000:ℝ)
 | .Cbridge3 => (380003181897/200000000000:ℝ)
 | .Cbridge4 => (360003181897/200000000000:ℝ)
 | .Cbridge5 => (370003181897/200000000000:ℝ)
 | .Cbridge6 => (350003181897/200000000000:ℝ)
def branchCap : CountBranch → ℝ
 | .old => 1/25
 | .Cnew => (10099/100000:ℝ)
 | .Pnew => (31/500:ℝ)
 | .Cphys => (9999/100000:ℝ)
 | .Cold => (9999/100000:ℝ)
 | .Pold => (31/500:ℝ)
 | .Cphysold => (9999/100000:ℝ)
 | .Pwide => (9/100:ℝ)
 | .Pcount => (10099/100000:ℝ)
 | .Pcountmid => (10049/100000:ℝ)
 | .Cbridge0 => (9999/100000:ℝ)
 | .Cbridge1 => (9999/100000:ℝ)
 | .Cbridge2 => (9999/100000:ℝ)
 | .Cbridge3 => (9999/100000:ℝ)
 | .Cbridge4 => (9999/100000:ℝ)
 | .Cbridge5 => (9999/100000:ℝ)
 | .Cbridge6 => (9999/100000:ℝ)
def isCap : CountBranch → Bool
 | .old => false
 | .Cnew => false
 | .Pnew => true
 | .Cphys => false
 | .Cold => false
 | .Pold => true
 | .Cphysold => false
 | .Pwide => true
 | .Pcount => true
 | .Pcountmid => true
 | .Cbridge0 => false
 | .Cbridge1 => false
 | .Cbridge2 => false
 | .Cbridge3 => false
 | .Cbridge4 => false
 | .Cbridge5 => false
 | .Cbridge6 => false
def branchZ (b : CountBranch) : ℝ := branchCap b-1/10000000
def V (δ : ℝ) : ℝ := 5/6-δ
def D (b : CountBranch) (p : ℝ) : ℝ :=
 if isCap b then 3-p else 3-p-4*p/branchL b
def A (b : CountBranch) (p : ℝ) : ℝ :=
 if isCap b then 2 else 2-4*p/branchL b
def C0 (b : CountBranch) (p : ℝ) : ℝ :=
 if isCap b then 1-2*p*branchZ b else 1-2*p*branchB b/branchL b
def Z (b : CountBranch) (p : ℝ) : ℝ :=
 if isCap b then 2*p*branchZ b else 2*p*branchB b/branchL b
def U (b : CountBranch) (p : ℝ) : ℝ := (1-p)*C0 b p
def oldD (p : ℝ) : ℝ := 3-p-2*p/(3*kappa)
def oldC (p : ℝ) : ℝ := 2*(1-p)*(1-p/(3*kappa))
def countJ (b : CountBranch) (δ p : ℝ) : ℝ :=
 match b with
 | .old => V δ*oldD p+δ*oldC p
 | b => V δ*D b p+δ*(1-p)*A b p
def countN (b : CountBranch) (δ p : ℝ) : ℝ :=
 match b with
 | .old => (1-δ)*countJ .old δ p+δ*oldC p*V δ/2
 | b => (1-δ)*countJ b δ p+V δ*δ*U b p
def countT (b : CountBranch) (δ p : ℝ) : ℝ := countJ b δ p+δ*U b p
def RN (b : CountBranch) (δ p : ℝ) : ℝ :=
 A b p*countT b δ p+(Z b p-p)*countJ b δ p
def MN (b : CountBranch) (δ p : ℝ) : ℝ :=
 D b p*countT b δ p-RN b δ p
def DJ (b : CountBranch) (δ p : ℝ) : ℝ := D b p*countJ b δ p
def naturalM : ℝ := (1-naturalK*sMinus)/2
def lowerM (b : CountBranch) : ℝ :=
 if isCap b then mMinus+1/10000000 else
 max (mMinus+1/10000000) ((branchB b-branchL b*(branchCap b-1/10000000))/2+1/10000000)
def upperM (b : CountBranch) : ℝ :=
 if isCap b then min (min (11/25-1/10000000) (naturalM-1/10000000))
 ((branchB b-branchL b*branchZ b)/2-1/10000000)
 else min (min (11/25-1/10000000) (naturalM-1/10000000))
 ((branchB b-branchL b*(sMinus+1/10000000))/2-1/10000000)
def derivativeD (b : CountBranch) : ℝ := if isCap b then -1 else -1-4/branchL b
def derivativeA (b : CountBranch) : ℝ := if isCap b then 0 else -4/branchL b
def derivativeC (b : CountBranch) : ℝ := if isCap b then -2*branchZ b else -2*branchB b/branchL b
def derivativeU (b : CountBranch) (p : ℝ) : ℝ := -C0 b p+(1-p)*derivativeC b
def derivativeJ (b : CountBranch) (δ p : ℝ) : ℝ :=
 V δ*derivativeD b+δ*(-A b p+(1-p)*derivativeA b)
def admissionGuard (b : CountBranch) (δ p : ℝ) (j : Fin 15) : ℝ :=
 match b with
 | .old => countJ .old δ p
 | b => ![D b p,A b p,C0 b p,countJ b δ p,countT b δ p-countJ b δ p,
 (12499/10000)*countJ b δ p-countT b δ p,
 RN b δ p-(23/37)*DJ b δ p,DJ b δ p-RN b δ p,
 MN b δ p-lowerM b*DJ b δ p,upperM b*DJ b δ p-MN b δ p,
 countN b δ p-(1-2*δ*naturalM-2*δ*p*sMinus)*countJ b δ p,
 U b p*derivativeJ b δ p-derivativeU b p*countJ b δ p,
 11/25-naturalM-1/10000000,
 branchB b-2*naturalM-branchL b*(sMinus+1/10000000)-2/10000000,
 if isCap b then (branchZ b-sMinus-1/10000000)*DJ b δ p else 1] j

def Ebase (d C δ p : ℝ) : ℝ :=
 1/2+13*h/75-y/2-ell/2-9*d/100+δ/2+δ*p*(ell-C/2)
def rowMargin (e : Edge) (b : CountBranch) (δ p : ℝ) : ℝ :=
 countJ b δ p*(theta-reserve-Ebase (edgeD e) (edgeC e) δ p)-3/4*edgeD e*countN b δ p

end
end Qrh.JointDetector.RestartReturn
