/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Construct the remaining middle with a genuine early source mesh cap. -/
import Candidate.C092.transport.MixedUpperFinalClamp
import Candidate.C092.transport.MixedOffsetCountBranchData
import Candidate.C092.transport.PacketJoinActual
set_option autoImplicit false
set_option allowUnsafeReducibility true
namespace QRH.Cycle092.MixedUpperFinal.CellBank
noncomputable section
attribute [local reducible] QRH.Record1252270103Return.GenericPhysical.BaselineData.toMomentData
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor QRH.Cycle092.MediumWitness
open QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount QRH.Cycle092.PacketJoinE49
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]
variable {D : BaselineData} {F : BaselineSourceData D} {η : Character}
variable {Z d a : ℝ} {rows : Finset FreeRow} {z : ℂ}
variable {bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t}
variable {t₀ γ τ : ℝ} {i : ℕ}

/-- Actual original metadata discharge every native middle-bank field.
The remaining conditions are the literal first-short/anchor branch and
original scalar collar, rather than analytic count or energy assumptions. -/
def middleCap (B : CellBank D F η Z d a rows z bin t₀ γ τ i)
    (P : TransportParameters D) (cap : ℝ) (hcap : 0<cap)
    (hfine : ∀s,D.length s ≤ cap/200) (hZ : 1<Z) (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 7/8)
    (ha : 51/100<a) (hahi : a ≤ 7/8)
    (hlower : ∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u)
    (hz : z.re=17/50) (him : |z.im| ≤ (3*i+1:ℕ)*Z^τ)
    (r : Row) (hr : r∈TopData.rows)
    (hp : r.box.Contains (2*a-1,classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)))
    (ht : t₀=Return.cutoffI (2*a-1)
      (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)))
    (hg : γ=(rowGamma r.box r.B:ℝ)) (hs : D.ε ≤ 3*witnessCollar)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)))
    (hne : ((B.layoutCap P hd hdhi cap hcap hfine).common σ).Nonempty) (j : Offset)
    (first : firstShort (inverseLength (Z^d) σ)=some j)
    (central : centralLengths (inverseLength (Z^d) σ j) (ordinaryLength (Z^d) σ j)) :
    MiddleBank D.toMomentData F η Z := by
  have haδ : 2*a-1 ≤ 3/4:=by linarith
  have hb:=original_bank_admission hr hp
  have hl : ∀u∈amplitudeCell D F Z d a rows (fun _=>z) bin,Z^(1/100:ℝ) ≤ rowNorm u:=
    fun u hu=>hlower u (Finset.mem_filter.mp hu).1
  let height:=QRH.Cycle092.PacketJoin.nativeHeight Z d τ i
  have hh:0 ≤ height:=by dsimp [height,QRH.Cycle092.PacketJoin.nativeHeight];positivity
  have hf:2*Real.pi*(Z^d)^(τ/(2*(7/8:ℝ)))+(3*i:ℕ)*Z^τ ≤ height:=by
    dsimp [height,QRH.Cycle092.PacketJoin.nativeHeight]
    push_cast
    have hpos:=Real.rpow_nonneg (zero_lt_one.trans hZ).le τ
    linarith
  have hext:∀s,|((B.layoutCap P hd hdhi cap hcap hfine).external s).im| ≤ height:=by
    intro s
    change |z.im| ≤ height
    exact him.trans (le_add_of_nonneg_left (by positivity))
  exact MiddleBank.ofLayout _ d a t₀ γ (Z^τ) ((Z^d)^(τ/(2*(7/8:ℝ)))) i B.source
    (B.layoutCap P hd hdhi cap hcap hfine) σ hne j first hl rfl rfl rfl (fun _=>hz)
    height witnessCollar ((rowV r.box:ℝ)/(r.box.uHi:ℝ)) hd ha haδ hh hf hext
    (by rw [hg];exact hb.2.1) (by rw [ht,hg];exact hb.2.2.2.1)
    (by rw [ht];exact hb.2.2.2.2.1) (by norm_num [witnessCollar]) hs
    hb.1 ht central.1 central.2.1 central.2.2.1 central.2.2.2 hb.2.2.2.2.2

#print axioms middleCap
end
end QRH.Cycle092.MixedUpperFinal.CellBank
