/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine source counts on every frozen bank class outside the middle branch. -/
import Candidate.C092.transport.MixedUpperFinalExitInput
import Candidate.C092.transport.MixedUpperFinalNativeFacts
set_option autoImplicit false
set_option allowUnsafeReducibility true
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
attribute [local reducible] QRH.Record1252270103Return.GenericPhysical.BaselineData.toMomentData
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.MediumWitness QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount
open QRH.Cycle092.PacketJoin HeckeDetectorRawFiber
open QRH.Cycle092.PacketJoinE49 QRH.Cycle090 QRH.Cycle092.MixedTicketTails
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]


/-- Per-original-phase metadata and the chosen true source bank. No count,
price, moment or amplitude estimate is a field. All indices are literal. -/
structure ExitPhaseData (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z : ℝ) (P : TransportParameters D) (d a : ℝ) (rows : Finset FreeRow) (z : ℂ)
    (bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t) (τ : ℝ) (i : ℕ) where
  cap : ℝ
  cap_pos : 0 < cap
  fine : ∀s,D.length s ≤ cap/200
  t₀ : ℝ
  γ : ℝ
  bank : CellBank D F η Z d a rows z bin t₀ γ τ i
  r : TopData.Row
  row : r∈TopData.rows
  point : r.box.Contains (2*a-1,classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))
  baseline : t₀=Return.cutoffI (2*a-1) (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))
  gamma : γ=(Mixed.rowGamma r.box r.B:ℝ)
  collar : D.ε ≤ 3*witnessCollar
  old_conductor : originalDlow r ≤ d
  upper_conductor : d ≤ Geometry.h+rowPad

namespace ExitPhaseData
variable {D : BaselineData} {F : BaselineSourceData D} {η : Character}
    {Z : ℝ} {P : TransportParameters D} {d a : ℝ} {rows : Finset FreeRow} {z : ℂ}
    {bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t} {τ : ℝ} {i : ℕ}

/-- Canonical constructor from the actual mixed-bank supplier. -/
def ofCellBank (r : TopData.Row) (hr : r∈TopData.rows)
    (point : r.box.Contains (2*a-1,classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)))
    (B : CellBank D F η Z d a rows z bin
      (Return.cutoffI (2*a-1) (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)))
      (Mixed.rowGamma r.box r.B:ℝ) τ i)
    (cap : ℝ) (hcap : 0 < cap) (fine : ∀s,D.length s ≤ cap/200)
    (collar : D.ε ≤ 3*witnessCollar) (old : originalDlow r ≤ d)
    (upper : d ≤ Geometry.h+rowPad) : ExitPhaseData D F η Z P d a rows z bin τ i where
  cap := cap
  cap_pos := hcap
  fine := fine
  t₀ := Return.cutoffI (2*a-1) (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))
  γ := (Mixed.rowGamma r.box r.B:ℝ)
  bank := B
  r := r
  row := hr
  point := point
  baseline := rfl
  gamma := rfl
  collar := collar
  old_conductor := old
  upper_conductor := upper

def remaining (A : ExitPhaseData D F η Z P d a rows z bin τ i)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d))) : Prop :=
  remainingMiddle (Z^d) (2*a-1)
    (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))
    A.t₀ A.γ ((Mixed.rowV A.r.box:ℝ)/(A.r.box.uHi:ℝ)) (Mixed.rowBudget A.r.B) σ

def toInput (A : ExitPhaseData D F η Z P d a rows z bin τ i)
    (hd : (1/2:ℝ) ≤ d) (hdhi : d ≤ 7/8) (ha : 51/100<a) (hahi : a ≤ 7/8)
    (lower : ∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u)
    (hz : z.re=17/50) (him : |z.im| ≤ (3*i+1:ℕ)*Z^τ) : ExitInput D F η Z where
  P := P
  cap := A.cap
  cap_pos := A.cap_pos
  fine := A.fine
  d := d
  a := a
  rows := rows
  z := z
  bin := bin
  t₀ := A.t₀
  γ := A.γ
  τ := τ
  i := i
  bank := A.bank
  d_min := hd
  d_hi := hdhi
  a_min := ha
  a_hi := hahi
  lower := lower
  z_re := hz
  z_im := him
  r := A.r
  row := A.row
  point := A.point
  baseline := A.baseline
  gamma := A.gamma
  collar := A.collar
  old_conductor := A.old_conductor
  upper_conductor := A.upper_conductor
end ExitPhaseData

/-- The same chosen bank in each actual nonempty phase, and a single chosen
frozen descriptor there. Empty phases contribute the literal empty row set. -/
def phaseExitCommon (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z : ℝ) (P : TransportParameters D) (d a : ℝ) (rows : Finset FreeRow) (z : ℂ) (τ : ℝ) (i : ℕ)
    (hd : (1/2:ℝ) ≤ d)
    (bins : Finset (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t))
    (data : ∀bin∈bins,∀hne : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty,
      ExitPhaseData D F η Z P d a rows z bin τ i)
    (σ : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t →
      Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)))
    (bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t) : Finset FreeRow :=
  if hb : bin∈bins then
    if hne : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty then
      if hhi : d ≤ 7/8 then
        ((data bin hb hne).bank.layout P (by linarith) hhi).common (σ bin)
      else ∅
    else ∅
  else ∅

#print axioms ExitPhaseData.toInput
end
end QRH.Cycle092.MixedUpperFinal
