/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Original-row and early positive-width facts for the actual native bank. -/
import Candidate.C092.transport.MixedUpperFinalMiddleClamp
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.MediumWitness QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- Fixed before every later transport P, height exponent and live conductor. -/
def sourceWidthMin (D : BaselineData) : ℝ := ∏s : Fin D.N,D.length s

theorem sourceWidthMin_pos (D : BaselineData) : 0<sourceWidthMin D :=
  Finset.prod_pos (fun s _=>D.slots_pos s)

theorem sourceWidthMin_le (D : BaselineData) (s : Fin D.N) : sourceWidthMin D ≤ D.length s := by
  have hh (k : Fin D.N) : D.length k ≤ 1:=by linarith [D.slots_small k,D.t_small]
  have h:=Finset.prod_le_prod_of_subset_of_le_one₀ (f:=D.length)
    (s:={s}) (t:=Finset.univ) (Finset.subset_univ _)
    (fun k _=>(D.slots_pos k).le) (fun k _ _=>hh k)
  simpa only [sourceWidthMin,Finset.prod_singleton] using h

theorem sourceWidthMin_le_normalized (D : BaselineData) {d : ℝ} (hd : 0<d) (hdhi : d ≤ 1)
    (s : Fin D.N) : sourceWidthMin D ≤ D.length s/d := by
  apply (sourceWidthMin_le D s).trans
  apply (le_div_iff₀ hd).mpr
  exact mul_le_of_le_one_right (D.slots_pos s).le hdhi

private theorem filterSubset {α : Type*} (s : Finset α) (p : α→Prop) (dec : DecidablePred p) :
    @Finset.filter α p dec s ⊆ s := @Finset.filter_subset α p dec s

namespace CellBank
variable {D : BaselineData} {F : BaselineSourceData D} {η : Character}
variable {Z d a : ℝ} {rows : Finset FreeRow} {z : ℂ}
variable {bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t}
variable {t₀ γ τ : ℝ} {i : ℕ}

theorem native_rows_subset (B : CellBank D F η Z d a rows z bin t₀ γ τ i)
    (P : TransportParameters D) (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 7/8)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)))
    (hne : ((B.layout P hd hdhi).common σ).Nonempty) (j : Offset) :
    ((B.layout P hd hdhi).fiber σ hne j).rows ⊆ amplitudeCell D F Z d a rows (fun _=>z) bin := by
  exact filterSubset _ _ _

theorem capped_rows_subset (B : CellBank D F η Z d a rows z bin t₀ γ τ i)
    (P : TransportParameters D) (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 7/8)
    (cap : ℝ) (hcap : 0<cap) (hfine : ∀s,D.length s ≤ cap/200)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)))
    (hne : ((B.layoutCap P hd hdhi cap hcap hfine).common σ).Nonempty) (j : Offset) :
    ((B.layoutCap P hd hdhi cap hcap hfine).fiber σ hne j).rows ⊆
      amplitudeCell D F Z d a rows (fun _=>z) bin := by
  exact filterSubset _ _ _

end CellBank
#print axioms sourceWidthMin_pos
#print axioms sourceWidthMin_le_normalized
#print axioms CellBank.capped_rows_subset
end
end QRH.Cycle092.MixedUpperFinal
