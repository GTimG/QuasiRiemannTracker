/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original stationary separation and unrounded coarse ticket debit.
The independently checked top-price B is compared to this OLD debit only;
none of the refined central widths or thresholds replace the raw ticket. -/
import Candidate.C092.transport.RawTicketAdmission
set_option autoImplicit false
noncomputable section
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData QRH.Cycle092.RawTicket

def originalSepQ (r : Row) : ℚ :=
  max 0 (max ((425830047444893/1000000000000000)-r.box.uHi)
    (r.box.uLo-(425830047444894/1000000000000000)))
def originalSep (r : Row) : ℝ := originalSepQ r

def rawUQ (p g0 g1 : ℚ) := 1-p*(1+6*g0-4*g1)
def rawJQ (d p g1 : ℚ) := 5/2-d*(1+2*p*(1+2*g1))
def rawCrossQ (d p g0 g1 : ℚ) := 1+d*rawUQ p g0 g1/rawJQ d p g1

def rawDebitProxyQ (r : Row) : ℚ :=
  let a:=r.box.uLo
  let b:=r.box.uHi
  let f:=r.box.vLo
  let e:=r.box.vHi
  let q:= -140952330598569/10^(15:ℕ)+a*(117667768631473/200000000000000-328860096935511/10^(15:ℕ)*e)
  let R:=1-a*(f*(1+2*(5805911/100000000))+2*(1-e*(1+2*(379981/5000000)))*
    rawCrossQ a e (5805913/100000000) (3799809/50000000)/3)
  let slope:= -5/12-a*f/4+3*R/4;
  -(205830466908273/10^(15:ℕ)*(originalSepQ r)^2+(1/2-e)*a*q)/
    rawJQ a f (3799809/50000000)+(3+8*b*e)*
    (174669171221343715360237/200000000000000000000000-436666397/500000000)+
    (22595743/10000000000)*slope

def rawBridgeCheck (r : Row) : Bool := decide (r.B ≤ rawDebitProxyQ r)

/-- Genuine mathematical separation used by the frozen original engine. -/
theorem original_sep_eq (r : Row) : originalSep r=
    max 0 (max ((425830047444893/1000000000000000:ℝ)-(r.box.uHi:ℝ))
      ((r.box.uLo:ℝ)-(425830047444894/1000000000000000:ℝ))) := by
  norm_num [originalSep,originalSepQ,Rat.cast_max]

theorem raw_debit_proxy_cast (r : Row) : (rawDebitProxyQ r:ℝ)=
    -((205830466908273/10^(15:ℕ)*(originalSep r)^2+
      (1/2-(r.box.vHi:ℝ))*(r.box.uLo:ℝ)*oldQ r.box.uLo r.box.vHi)/
      oldJmax r.box.uLo r.box.vLo)+
    (3+8*(r.box.uHi:ℝ)*(r.box.vHi:ℝ))*RawTicket.xi+
    (22595743/10000000000)*oldSlope r.box.uLo r.box.vLo r.box.vHi := by
  norm_num [rawDebitProxyQ,originalSep,oldQ,oldJmax,oldSlope,oldRhi,crossing,J,U,
    RawTicket.xi,rawCrossQ,rawUQ,rawJQ,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,
    Rat.cast_div,Rat.cast_pow,Rat.cast_neg]
  ring

/-- Outward floor/ceiling can only INCREASE the original raw debit. -/
theorem raw_proxy_le_old_debit (r : Row) : (rawDebitProxyQ r:ℝ) ≤
    oldDebit r.box.uLo r.box.uHi r.box.vLo r.box.vHi (originalSep r) := by
  rw [raw_debit_proxy_cast]
  have hf := (rounding (x:=
    (205830466908273/10^(15:ℕ)*(originalSep r)^2+
      (1/2-(r.box.vHi:ℝ))*(r.box.uLo:ℝ)*oldQ r.box.uLo r.box.vHi)/oldJmax r.box.uLo r.box.vLo)
    (n:=10^(15:ℕ)) (by norm_num)).2.1
  have hc := (rounding (x:= -oldMargin r.box.uLo r.box.uHi r.box.vLo r.box.vHi (originalSep r))
    (n:=10^(15:ℕ)) (by norm_num)).2.2.1
  dsimp only [oldMargin] at hc
  dsimp only [oldDebit,oldMargin]
  linarith only [hf,hc]
end QRH.Cycle092.MixedTicketTails
#print axioms QRH.Cycle092.MixedTicketTails.raw_proxy_le_old_debit
