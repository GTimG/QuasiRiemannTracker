/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.DirectPaired

/-!
# Original fixed, saved and native direct-route formulas

All cleared formulas below use the authentic original counts. The available
native source is B=1-s,L=2+10s,s=10^-260, and the old count uses the original
contact upper moment parameter. No stored margin or saved polynomial is read.
-/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
namespace QRH.Cycle092.Direct
open QRH.Cycle090 QRH.Coverage

inductive CountRoute where
  | old | native | fixedS | fixedA
  deriving DecidableEq, Repr

section Formulas
variable {K : Type*} [Field K]

def nativeD (s p : K) : K := 3-p-4*p/(2+10*s)
def nativeA (s p : K) : K := 2-4*p/(2+10*s)
def nativeC (s p : K) : K := 1-2*p*(1-s)/(2+10*s)

def countJ (route : CountRoute) (s kap d p : K) : K :=
  match route with
  | .old => (5/6-d)*(3-p-2*p/(3*kap))+d*(2*(1-p)*(1-p/(3*kap)))
  | .native => (5/6-d)*nativeD s p+d*(1-p)*nativeA s p
  | _ => 1

def countN (route : CountRoute) (s kap d p : K) : K :=
  match route with
  | .old => (1-d)*countJ route s kap d p+d*(2*(1-p)*(1-p/(3*kap)))*(5/6-d)/2
  | .native => (1-d)*countJ route s kap d p+(5/6-d)*d*(1-p)*nativeC s p
  | .fixedS => 1-d*(p*(1+2*(5805911/100000000))+
      (1-p*(1+2*(379981/5000000)))*(360001/500000))+1/100000000000
  | .fixedA => 1/6+(5/6-d)*(3*(360001/500000)/2)+1/100000000000

def edgeD (edge : Fin 4) (h : K) : K :=
  match edge.val with
  | 0 => 1/200
  | 1 | 2 => 19/25
  | _ => h

/-- The edge-specific conservative capacity is affine in the actual h. -/
def edgeProxy (edge : Fin 4) (t kap h : K) : K :=
  let ell := 11/3-4*t
  match edge.val with
  | 0 => (1/200)/(6*kap)
  | 1 => (2*(h-2*ell)-19/25)/(6*kap)
  | 2 => (17/200)*(19/25)
  | _ => h/2-2*ell-1/1000000000000

def directBase (t kap h d p : K) (edge : Fin 4) : K :=
  let ell := 11/3-4*t
  1/2+13*h/75-(h-2*ell)/2-ell/2-9*edgeD edge h/100+d/2+
    d*p*(ell-edgeProxy edge t kap h/2)

/-- Clearing the original count denominator gives a polynomial, never a fitted margin. -/
def directCleared (route : CountRoute) (edge : Fin 4) (t s kap h d p : K) : K :=
  (t-directBase t kap h d p edge)*countJ route s kap d p-
    3*edgeD edge h*countN route s kap d p/4
end Formulas

noncomputable section

def kap : ℝ := 2*(QRH.ContactCertificate.alphaHi : ℝ)-1

def cleared (route : CountRoute) (edge : Fin 4) (h d p : ℝ) : ℝ :=
  directCleared route edge theta sourceCost kap h d p

/-- Both endpoint checks fill the entire directed conductor interval. -/
theorem direct_interpolation (route : CountRoute) (edge : Fin 4) (h d p : ℝ) :
    cleared route edge h d p =
      (1-(h-hLower)/(hUpper-hLower))*cleared route edge hLower d p+
      ((h-hLower)/(hUpper-hLower))*cleared route edge hUpper d p := by
  fin_cases edge <;>
    norm_num [cleared, directCleared, directBase, edgeD, edgeProxy, hLower,hUpper] <;> ring

end

def qSource : ℚ := 1/10^(260 : ℕ)
def qKap : ℚ := 2*QRH.ContactCertificate.alphaHi-1

def qDirectCleared (route : CountRoute) (edge : Fin 4) (h d p : ℚ) : ℚ :=
  directCleared route edge (436666397/500000000) qSource qKap h d p

theorem directCleared_cast (route : CountRoute) (edge : Fin 4) (t s kap h d p : ℚ) :
    ((directCleared route edge t s kap h d p : ℚ) : ℝ) =
      directCleared route edge (t : ℝ) s kap h d p := by
  cases route <;> fin_cases edge <;>
    push_cast [directCleared,directBase,edgeD,edgeProxy,countJ,countN,nativeD,nativeA,nativeC] <;>
    rfl

theorem qDirectCleared_cast (route : CountRoute) (edge : Fin 4) (h d p : ℚ) :
    (qDirectCleared route edge h d p : ℝ) = cleared route edge h d p := by
  unfold qDirectCleared
  rw [directCleared_cast]
  simp only [qSource,qKap,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_pow,
    Rat.cast_sub,Rat.cast_mul]
  rfl

/-- Cubic Bernstein coefficients from four exact equidistant evaluations. -/
def cubicCoefficients (f : ℚ → ℚ) (a b : ℚ) : ℕ → ℚ
  | 0 => f a
  | 1 => (-5*f a+18*f ((2*a+b)/3)-9*f ((a+2*b)/3)+2*f b)/6
  | 2 => (2*f a-9*f ((2*a+b)/3)+18*f ((a+2*b)/3)-5*f b)/6
  | 3 => f b
  | _ => 0

def directCoefficients (route : CountRoute) (edge : Fin 4) (h : ℚ)
    (box : Box) (i j : ℕ) : ℚ :=
  Physical.quadraticCoefficients
    (fun d => cubicCoefficients (qDirectCleared route edge h d) box.vLo box.vHi j)
    box.uLo box.uHi i

theorem direct_expansion (route : CountRoute) (edge : Fin 4) (h : ℚ)
    (box : Box) (x y : ℝ) :
    cleared route edge h
      ((box.uLo : ℝ)+((box.uHi : ℝ)-box.uLo)*x)
      ((box.vLo : ℝ)+((box.vHi : ℝ)-box.vLo)*y) =
    QRH.Bernstein.value 2 3 (fun i j => (directCoefficients route edge h box i j : ℝ)) x y := by
  norm_num [QRH.Bernstein.value,QRH.Bernstein.tensorBasis,QRH.Bernstein.basis,
    Finset.sum_range_succ,directCoefficients,Physical.quadraticCoefficients,cubicCoefficients]
  simp only [Rat.cast_add,Rat.cast_div,Rat.cast_ofNat,Rat.cast_sub,Rat.cast_mul,
    Rat.cast_neg,qDirectCleared_cast]
  cases route <;>
    norm_num [cleared,directCleared,directBase,countJ,countN,
      nativeD,nativeA,nativeC] <;> ring

/-- The exact regenerated coefficients certify all real points, including the box boundary. -/
theorem direct_box_bound (route : CountRoute) (edge : Fin 4) (h : ℚ) (box : Box) (M : ℚ)
    (hu : box.uLo < box.uHi) (hv : box.vLo < box.vHi)
    (hc : QRH.Bernstein.coefficientsCheck 2 3 (directCoefficients route edge h box) M = true)
    {point : Point} (hp : box.Contains point) :
    (M : ℝ) ≤ cleared route edge h point.1 point.2 := by
  have hu' : (box.uLo : ℝ) < (box.uHi : ℝ) := Rat.cast_lt.mpr hu
  have hv' : (box.vLo : ℝ) < (box.vHi : ℝ) := Rat.cast_lt.mpr hv
  have hb := QRH.Bernstein.checked_boxValue_lower_bound 2 3
    (directCoefficients route edge h box) M hc hu' hv' hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  dsimp [QRH.Bernstein.boxValue] at hb
  rw [← direct_expansion] at hb
  simpa only [Physical.reconstruct hu',Physical.reconstruct hv'] using hb

end QRH.Cycle092.Direct
#print axioms QRH.Cycle092.Direct.direct_expansion
#print axioms QRH.Cycle092.Direct.direct_box_bound
