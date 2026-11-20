/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
True source presentations at every response of an actual selected bank. -/
import Candidate.C092.transport.MixedUpperFinalMiddle
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
open QRH.Cycle092.MediumWitness QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]
variable {D : BaselineData} {F : BaselineSourceData D} {η : Character}
variable {Z d a : ℝ} {rows : Finset FreeRow} {z : ℂ}
variable {bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t}
variable {t₀ γ τ : ℝ} {i : ℕ}

/-- Actual source data and profile are copied into the presentation.
The constructor supplies no cardinality, energy or moment hypothesis. -/
def presented (B : CellBank D F η Z d a rows z bin t₀ γ τ i)
    (P : TransportParameters D) (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 7/8)
    (hlower : ∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u) (hz : z.re=17/50) (j : Offset) :
    Presented D.toMomentData F η Z d a (cutoff t₀ γ j)
      (Z^τ) ((Z^d)^(τ/(2*(7/8:ℝ)))) i :=
  ⟨(B.layout P hd hdhi).batch j,
    (fun u hu=>hlower u (Finset.mem_filter.mp hu).1),rfl,rfl,rfl,rfl,fun _=>hz⟩

def slice (B : CellBank D F η Z d a rows z bin t₀ γ τ i)
    (P : TransportParameters D) (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 7/8)
    (hlower : ∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u) (hz : z.re=17/50)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)))
    (hne : ((B.layout P hd hdhi).common σ).Nonempty) (j : Offset) :
    Slice (B.presented P hd hdhi hlower hz j) :=
  ⟨bin,σ.1,σ.2.1 j,σ.2.2 j,hne.mono ((B.layout P hd hdhi).common_subset_fiber σ j)⟩

theorem slice_fiber (B : CellBank D F η Z d a rows z bin t₀ γ τ i)
    (P : TransportParameters D) (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 7/8)
    (hlower : ∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u) (hz : z.re=17/50)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)))
    (hne : ((B.layout P hd hdhi).common σ).Nonempty) (j : Offset) :
    (B.slice P hd hdhi hlower hz σ hne j).fiber=(B.layout P hd hdhi).fiber σ hne j := rfl

#print axioms presented
#print axioms slice
#print axioms slice_fiber
end
end QRH.Cycle092.MixedUpperFinal.CellBank
