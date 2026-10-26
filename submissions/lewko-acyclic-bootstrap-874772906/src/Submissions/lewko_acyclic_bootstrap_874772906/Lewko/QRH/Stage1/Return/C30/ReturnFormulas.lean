/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnConstants
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
inductive CountBranch | old | C | P | capC | capP | weakC2 | weakC6 | weakC8
 deriving DecidableEq
def branchB : CountBranch → ℝ
 | .C | .capC => countCB
 | .P | .capP => physicalB
 | .weakC2 => countCB-2/4000
 | .weakC6 => countCB-6/4000
 | .weakC8 => countCB-8/4000
 | .old => 0
def branchL : CountBranch → ℝ
 | .C | .capC | .weakC2 | .weakC6 | .weakC8 => countCL
 | .P | .capP => physicalLambda
 | .old => 1
def branchCap : CountBranch → ℝ
 | .C | .capC | .weakC2 | .weakC6 | .weakC8 => 11/250
 | .P | .capP => 43/1000
 | .old => 1/25
def isCap : CountBranch → Bool
 | .capC | .capP => true
 | _ => false
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
def naturalM : ℝ := (1-naturalK*(17/500))/2
def lowerM (b : CountBranch) : ℝ :=
 if isCap b then 2/5+1/10000000 else
 max (2/5+1/10000000) ((branchB b-branchL b*(branchCap b-1/10000000))/2+1/10000000)
def upperM (b : CountBranch) : ℝ :=
 if isCap b then min (min (11/25-1/10000000) (naturalM-1/10000000))
 ((branchB b-branchL b*branchZ b)/2-1/10000000)
 else min (min (11/25-1/10000000) (naturalM-1/10000000))
 ((branchB b-branchL b*(17/500+1/10000000))/2-1/10000000)
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
 countN b δ p-(1-2*δ*naturalM-2*δ*p*(17/500))*countJ b δ p,
 U b p*derivativeJ b δ p-derivativeU b p*countJ b δ p,
 11/25-naturalM-1/10000000,
 branchB b-2*naturalM-branchL b*(17/500+1/10000000)-2/10000000,
 if isCap b then (branchZ b-17/500-1/10000000)*DJ b δ p else 1] j

def Ebase (d C δ p : ℝ) : ℝ :=
 1/2+13*h/75-y/2-ell/2-9*d/100+δ/2+δ*p*(ell-C/2)
def rowMargin (e : Edge) (b : CountBranch) (δ p : ℝ) : ℝ :=
 countJ b δ p*(theta-rowFee-Ebase (edgeD e) (edgeC e) δ p)-3/4*edgeD e*countN b δ p
end
end LewkoStage1Return.C30
