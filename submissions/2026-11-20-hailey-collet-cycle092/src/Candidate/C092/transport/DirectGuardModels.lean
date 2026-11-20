/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.DirectCertificates
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
namespace QRH.Cycle092.Direct
open QRH.Cycle090 QRH.Coverage

/-- The .15-cap native fork's original length cutoffs, including its exact fees. -/
def nativeLower {K : Type*} [Field K] (s : K) : K :=
  (1-s-(2+10*s)*(3/20-1000*s/1143-1/10000000))/2+1/10000000

def nativeUpper {K : Type*} [Field K] : K := 4392499/10000000

/-- All fifteen actual M.4 guards; in particular this is not the smaller-cap fork. -/
def nativeGuard {K : Type*} [Field K] (i : Fin 15) (s d p : K) : K :=
  let D := nativeD s p
  let A := nativeA s p
  let C := nativeC s p
  let U := (1-p)*C
  let V := 5/6-d
  let J := countJ .native s 0 d p
  let T := J+d*U
  let DJ := D*J
  let RN := A*T+((1-C)-p)*J
  let MN := D*T-RN
  let N := countN .native s 0 d p
  let Jp := V*(-1-4/(2+10*s))+d*(-A-4*(1-p)/(2+10*s))
  let Up := -C-2*(1-p)*(1-s)/(2+10*s)
  match i.val with
  | 0 => D
  | 1 => A
  | 2 => C
  | 3 => J
  | 4 => T-J
  | 5 => (12499/10000)*J-T
  | 6 => RN-(23/37)*DJ
  | 7 => DJ-RN
  | 8 => MN-nativeLower s*DJ
  | 9 => nativeUpper*DJ-MN
  | 10 => N-(1-2*d*(1757/4000)-2*d*p*(27/1000))*J
  | 11 => U*Jp-Up*J
  | 12 => 11/25-1757/4000-1/10000000
  | 13 => 1-s-2*(1757/4000)-(2+10*s)*(27/1000+1/10000000)-2/10000000
  | _ => 1

theorem nativeGuard_cast (i : Fin 15) (s d p : ℚ) :
    ((nativeGuard i s d p : ℚ) : ℝ) = nativeGuard i (s : ℝ) d p := by
  fin_cases i <;> push_cast [nativeGuard,nativeLower,nativeUpper,nativeD,nativeA,nativeC,countJ,countN] <;> rfl

def qNativeGuard (i : Fin 15) (d p : ℚ) : ℚ := nativeGuard i qSource d p

theorem qNativeGuard_cast (i : Fin 15) (d p : ℚ) :
    (qNativeGuard i d p : ℝ) = nativeGuard i sourceCost (d : ℝ) p := by
  unfold qNativeGuard
  rw [nativeGuard_cast]
  simp only [qSource,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
  rfl

def nativeGuardCoefficients (k : Fin 15) (s : ℚ) (box : Box) (i j : ℕ) : ℚ :=
  Physical.quadraticCoefficients
    (fun d => cubicCoefficients (nativeGuard k s d) box.vLo box.vHi j)
    box.uLo box.uHi i


end QRH.Cycle092.Direct
#print axioms QRH.Cycle092.Direct.nativeGuard_cast
