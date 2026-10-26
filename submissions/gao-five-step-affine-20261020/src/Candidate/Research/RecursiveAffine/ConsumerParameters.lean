/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.FixedStages
import Candidate.Research.RecursiveAffine.Geometry.Coordinates

set_option autoImplicit false
namespace Cycle153.Consumer
noncomputable section
open OAI.SevenEighths.Cycle153Geometry

def theta : ℝ := 8748087/10000000
def h : ℝ := 79716116522/100000000000
def ell : ℝ := 11/3-4*theta
def y : ℝ := h-2*ell
def kappaStar : ℝ := 2*theta-1
def lambda : ℝ := FixedStages.stage0.lam
def B : ℝ := Coordinates.outerB
def topSaving : ℝ := 1/25000000
def rowSaving : ℝ := 1/50000000
def countCap : ℝ := (1-81/200-264/625)/(9/2)
def dMinus : ℝ := 2*y/(lambda*countCap+2-B)
def dPlus : ℝ := h+topSaving/4

theorem lambda_bounds : lambda∈Set.Icc (374133137186239/100000000000000) (374133137186240/100000000000000) := by
  norm_num [lambda,FixedStages.stage0]
theorem B_bounds : B∈Set.Icc (98202950630894/100000000000000) (98202950630895/100000000000000) := by
  norm_num [B,Coordinates.outerB]

def newCapacity (L : ℝ) : ℝ := (2*y-(2-B)*L)/lambda
def oldCapacity (L : ℝ) : ℝ := (2*y-L)/(6*kappaStar)
def V (d : ℝ) : ℝ := 5/6-d
def D (p : ℝ) : ℝ := 3-p-2*p/(3*kappaStar)
def P (p : ℝ) : ℝ := 2*(1-p)*(1-p/(3*kappaStar))
def J (d p : ℝ) : ℝ := V d*D p+d*P p

def common (d p : ℝ) : ℝ := (1+d)/2+13*h/75-y/2-ell/2+ell*d*p

def affineSI (d p : ℝ) : ℝ := d*(1-p)
def affineSP (d p : ℝ) : ℝ := 2*d-4*d*p/lambda
def affineA (d p : ℝ) : ℝ := 1-2*d*p*B/lambda
def affineN (d p : ℝ) : ℝ := (1-d*p)*affineSP d p+affineA d p*affineSI d p-(affineSI d p+affineSP d p)/6
def affineD (d p : ℝ) : ℝ := V d*(affineSI d p+affineSP d p)+affineSI d p*affineSP d p

def cappedSP (d : ℝ) : ℝ := 2*d
def cappedA (d p : ℝ) : ℝ := 1-2*d*p*Coordinates.top
def cappedN (d p : ℝ) : ℝ := (1-d*p)*cappedSP d+cappedA d p*affineSI d p-(affineSI d p+cappedSP d)/6
def cappedD (d p : ℝ) : ℝ := V d*(affineSI d p+cappedSP d)+affineSI d p*cappedSP d

def plain (d p : ℝ) : ℝ := 1-2*d*(264/625)-2*d*p*(1-2*(264/625))/(6*kappaStar)
def oldCleared (L C saving d p : ℝ) : ℝ :=
  8*J d p*(theta-saving-common d p-L*(66/100-3*d/4)+d*p*C/2)-3*L*d*P p*V d

def affineCleared (L C saving d p : ℝ) : ℝ :=
  4*affineD d p*(theta-saving-common d p-(7/200)*L+d*p*C/2)-3*L*V d*affineN d p

def cappedCleared (L C saving d p : ℝ) : ℝ :=
  4*cappedD d p*(theta-saving-common d p-(7/200)*L+d*p*C/2)-3*L*V d*cappedN d p

def plainMargin (L C saving d p : ℝ) : ℝ :=
  theta-saving-common d p-L*(1/4+3*plain d p/4-17/50)+d*p*C/2

end
end Cycle153.Consumer
