/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Keep the full packet on direct exits; split only the actual remaining middle. -/
import Candidate.C092.transport.MixedUpperFinalUnion
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

/-- Every norm and original row weight is retained on the SAME actual rows.
The large term is bounded once on the original phase cell. In particular,
no invalid comparison between a small-piece norm and the full norm is used. -/
theorem norm_split (B : CellBank D F η Z d a rows z bin t₀ γ τ i)
    (P : TransportParameters D) (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 7/8)
    (middle : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d))→Prop)
    (full small large : FreeRow→ℂ)
    (hsplit : ∀u∈amplitudeCell D F Z d a rows (fun _=>z) bin,full u=small u+large u) :
    (∑u∈amplitudeCell D F Z d a rows (fun _=>z) bin,‖full u‖) ≤
      (∑σ∈Finset.univ.filter (fun σ=>¬middle σ),∑u∈(B.layout P hd hdhi).common σ,‖full u‖)+
      (∑σ∈Finset.univ.filter middle,∑u∈(B.layout P hd hdhi).common σ,‖small u‖)+
      (∑u∈amplitudeCell D F Z d a rows (fun _=>z) bin,‖large u‖) := by
  classical
  let L:=B.layout P hd hdhi
  let X:=Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d))
  have hlocal (σ : X) :
      (∑u∈L.common σ,‖full u‖) ≤
        (if middle σ then ∑u∈L.common σ,‖small u‖ else ∑u∈L.common σ,‖full u‖)+
        (∑u∈L.common σ,‖large u‖) := by
    by_cases hm:middle σ
    · rw [if_pos hm,←Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro u hu
      have hcell:=class_subset _ L.labels (fun j u=>(L.witness j u).left)
        (fun j u=>(L.witness j u).right) σ hu
      rw [hsplit u hcell]
      exact norm_add_le _ _
    · rw [if_neg hm]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _=>norm_nonneg _))
  rw [L.weighted_union (fun u=>‖full u‖)]
  calc
    _ ≤ ∑σ : X,((if middle σ then ∑u∈L.common σ,‖small u‖ else ∑u∈L.common σ,‖full u‖)+
        ∑u∈L.common σ,‖large u‖) := Finset.sum_le_sum (fun σ _=>hlocal σ)
    _ = (∑σ : X,if middle σ then ∑u∈L.common σ,‖small u‖ else ∑u∈L.common σ,‖full u‖)+
        (∑σ : X,∑u∈L.common σ,‖large u‖) := Finset.sum_add_distrib
    _ = _ := by
      rw [←L.weighted_union (fun u=>‖large u‖)]
      congr 1
      simp only [Finset.sum_filter]
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hm:middle σ <;> simp only [hm,not_true_eq_false,not_false_eq_true,if_true,if_false,zero_add,add_zero] <;> rfl

#print axioms norm_split
end
end QRH.Cycle092.MixedUpperFinal.CellBank
