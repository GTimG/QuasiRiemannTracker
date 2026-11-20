/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Metadata for a true bank class outside the remaining small-source branch. -/
import Candidate.C092.transport.MixedUpperFinalRouting
import Candidate.C092.transport.MixedUpperFinalOutside
import Candidate.C092.transport.MixedUpperFinalAllLongCount
import Candidate.C092.transport.MixedUpperFinalCountPrice
import Candidate.C092.transport.MixedUpperFinalEnvelopeCount
import Candidate.C092.transport.MixedMiddleReturnPaidSliceNative
set_option autoImplicit false
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.MediumWitness QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount
open QRH.Cycle092.PacketJoinE49 QRH.Cycle090
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- Original geometric metadata only. In particular no count, moment,
physical upper, or continuation price is a field. -/
structure ExitInput (D : BaselineData) (F : BaselineSourceData D) (η : Character) (Z : ℝ) where
  P : TransportParameters D
  cap : ℝ
  cap_pos : 0<cap
  fine : ∀s,D.length s ≤ cap/200
  d : ℝ
  a : ℝ
  rows : Finset FreeRow
  z : ℂ
  bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t
  t₀ : ℝ
  γ : ℝ
  τ : ℝ
  i : ℕ
  bank : CellBank D F η Z d a rows z bin t₀ γ τ i
  d_min : (1/2:ℝ) ≤ d
  d_hi : d ≤ 7/8
  a_min : 51/100<a
  a_hi : a ≤ 7/8
  lower : ∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u
  z_re : z.re=17/50
  z_im : |z.im| ≤ (3*i+1:ℕ)*Z^τ
  r : TopData.Row
  row : r∈TopData.rows
  point : r.box.Contains (2*a-1,classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))
  baseline : t₀=Return.cutoffI (2*a-1) (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))
  gamma : γ=(Mixed.rowGamma r.box r.B:ℝ)
  collar : D.ε ≤ 3*witnessCollar
  old_conductor : MixedTicketTails.originalDlow r ≤ d
  upper_conductor : d ≤ Geometry.h+rowPad

namespace ExitInput
variable {D : BaselineData} {F : BaselineSourceData D} {η : Character} {Z : ℝ}
def hd (I : ExitInput D F η Z) : (1/200:ℝ) ≤ I.d := (by norm_num : (1/200:ℝ) ≤ 1/2).trans I.d_min
def layout (I : ExitInput D F η Z) := I.bank.layout I.P I.hd I.d_hi
def p (I : ExitInput D F η Z) : ℝ :=
  classMean Finset.univ ((2*I.a-1)/2) D.t (fun s=>D.length s/I.d) I.bin/(2*I.a-1)
def remaining (I : ExitInput D F η Z)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^I.d))) : Prop :=
  remainingMiddle (Z^I.d) (2*I.a-1) I.p I.t₀ I.γ
    ((Mixed.rowV I.r.box:ℝ)/(I.r.box.uHi:ℝ)) (Mixed.rowBudget I.r.B) σ
end ExitInput
end
end QRH.Cycle092.MixedUpperFinal
