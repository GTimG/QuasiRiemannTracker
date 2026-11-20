/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Refine declared mesh for a genuine source while retaining all original data. -/
import Candidate.C092.transport.MixedUpperFinalMiddle
set_option autoImplicit false
namespace QRH.Cycle092.MixedUpperFinal.CellBank
noncomputable section
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

/-- The source response does not use the declared slot mesh. Early slot
fineness permits this smaller metadata bound even for arbitrary later P. -/
def layoutCap (B : CellBank D F η Z d a rows z bin t₀ γ τ i)
    (P : TransportParameters D) (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 7/8)
    (cap : ℝ) (hcap : 0<cap) (hfine : ∀s,D.length s ≤ cap/200) :
    BankLayout (Slot:=Fin D.N) B.source := by
  let L:=B.layout P hd hdhi
  have hw : ∀s∈L.slots,L.widths s ≤ min P.mesh cap:=by
    intro s hs
    refine le_min (L.widths_mesh s hs) ?_
    change D.length s/d ≤ cap
    apply (div_le_iff₀ (show 0<d by linarith)).mpr
    nlinarith only [hfine s,mul_le_mul_of_nonneg_left hd hcap.le]
  exact { L with mesh:=min P.mesh cap,mesh_nonneg:=le_min P.mesh_pos.le hcap.le,widths_mesh:=hw }

/-- Every original class membership, phase and response dyad is unchanged. -/
theorem layoutCap_common (B : CellBank D F η Z d a rows z bin t₀ γ τ i)
    (P : TransportParameters D) (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 7/8)
    (cap : ℝ) (hcap : 0<cap) (hfine : ∀s,D.length s ≤ cap/200)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d))) :
    (B.layoutCap P hd hdhi cap hcap hfine).common σ=(B.layout P hd hdhi).common σ := rfl

#print axioms layoutCap
#print axioms layoutCap_common
end
end QRH.Cycle092.MixedUpperFinal.CellBank
