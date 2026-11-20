/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal selected packet decomposition over its genuine same-zero bank. -/
import Candidate.C092.transport.MixedUpperFinalCellBank
import Candidate.C092.transport.MixedOffsetCountRoutes
set_option autoImplicit false
namespace QRH.Cycle092.MixedUpperFinal.CellBank
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.SelectedNonfloor QRH.Cycle092.MediumWitness
open QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]
variable {D : BaselineData} {F : BaselineSourceData D} {η : Character}
variable {Z d a : ℝ} {rows : Finset FreeRow} {z : ℂ}
variable {bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t}
variable {t₀ γ τ : ℝ} {i : ℕ}

/-- Every original mask, complementary main product and front stays in
its original order. The 65,537 offset dyads partition the SAME original rows. -/
theorem packet_partition (B : CellBank D F η Z d a rows z bin t₀ γ τ i)
    (P : TransportParameters D) (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 7/8)
    (x : ℂ) (Y : ℝ) :
    packetNorm D F (amplitudeCell D F Z d a rows (fun _=>z) bin) η Z x z Y=
      ∑σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)),
        packetNorm D F ((B.layout P hd hdhi).common σ) η Z x z Y := by
  let L:=B.layout P hd hdhi
  unfold packetNorm
  trans ∑J∈Finset.univ.powerset,mainFront D J Z*
    ∑σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)),
      ∑u∈L.common σ,‖errorPacket D F J η u Z x z Y*mainProduct D F J u Z z‖
  · apply Finset.sum_congr rfl
    intro J hJ
    exact congrArg (fun r=>mainFront D J Z*r)
      (L.weighted_union (fun u=>‖errorPacket D F J η u Z x z Y*mainProduct D F J u Z z‖))
  · simp_rw [Finset.mul_sum]
    exact Finset.sum_comm

/-- Native fields on every common class are exact original metadata. -/
theorem native_fields (B : CellBank D F η Z d a rows z bin t₀ γ τ i)
    (P : TransportParameters D) (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 7/8)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)))
    (hne : ((B.layout P hd hdhi).common σ).Nonempty) (j : Offset) :
    let f:=(B.layout P hd hdhi).fiber σ hne j
    f.slots=Finset.univ ∧ f.mesh=P.mesh ∧ f.binWidth=D.t ∧
      f.profile=(fun _ x=>(F.w x:ℂ)) ∧ f.upper=(fun _=>2) ∧
      f.widths=(fun s=>D.length s/d) ∧ f.external=(fun _=>z) ∧
      f.q=classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The full original phase mean stays fixed on every common class, even
when the eventual numerator estimate selects a proper main-slot subset. -/
theorem common_full_mean (B : CellBank D F η Z d a rows z bin t₀ γ τ i)
    (P : TransportParameters D) (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 7/8)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)))
    (hne : ((B.layout P hd hdhi).common σ).Nonempty) (j : Offset)
    (u : FreeRow) (hu : u∈(B.layout P hd hdhi).common σ) :
    rowMean Finset.univ (Z^d) ((2*a-1)/2) D.t (fun s=>D.length s/d)
      (originalPhysical D F Z d (fun _=>z)) u=
      classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin :=
  (B.layout P hd hdhi).original_full_mean σ hne j u hu

#print axioms packet_partition
#print axioms native_fields
#print axioms common_full_mean
end
end QRH.Cycle092.MixedUpperFinal.CellBank
