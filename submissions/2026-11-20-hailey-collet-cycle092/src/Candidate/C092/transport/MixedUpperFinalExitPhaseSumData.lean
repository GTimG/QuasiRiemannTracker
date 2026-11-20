/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine source counts on every frozen bank class outside the middle branch. -/
import Candidate.C092.transport.MixedUpperFinalExitPhaseFinalFee
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
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]


/-- True nonremaining condition at the same chosen original phase bank. -/
def phaseExitKeep (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z : ℝ) (P : TransportParameters D) (d a : ℝ) (rows : Finset FreeRow) (z : ℂ) (τ : ℝ) (i : ℕ)
    (bins : Finset (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t))
    (data : ∀bin∈bins,∀hne : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty,
      ExitPhaseData D F η Z P d a rows z bin τ i)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)))
    (bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t) : Prop :=
  if hb : bin∈bins then
    if hne : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty then
      ¬(data bin hb hne).remaining σ
    else False
  else False

/-- Literal exit-class norm, zero on empty phases and remaining descriptors. -/
def phaseExitClassNorm (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z : ℝ) (P : TransportParameters D) (d a : ℝ) (rows : Finset FreeRow) (z : ℂ) (τ : ℝ) (i : ℕ)
    (hd : (1/2:ℝ) ≤ d)
    (bins : Finset (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t))
    (data : ∀bin∈bins,∀hne : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty,
      ExitPhaseData D F η Z P d a rows z bin τ i)
    (x : ℂ)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)))
    (bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t) : ℝ :=
  if phaseExitKeep D F η Z P d a rows z τ i bins data σ bin then
    packetNorm D F (phaseExitCommon D F η Z P d a rows z τ i hd bins data (fun _=>σ) bin)
      η Z x z (Z^Geometry.y)
  else 0

lemma phaseExitCommon_restrict (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z : ℝ) (P : TransportParameters D) (d a : ℝ) (rows : Finset FreeRow) (z : ℂ) (τ : ℝ) (i : ℕ)
    (hd : (1/2:ℝ) ≤ d)
    (bins small : Finset (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t))
    (hsub : small ⊆ bins)
    (data : ∀bin∈bins,∀hne : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty,
      ExitPhaseData D F η Z P d a rows z bin τ i)
    (σ : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t →
      Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)))
    (bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t) (hb : bin∈small) :
    phaseExitCommon D F η Z P d a rows z τ i hd small (fun b hb hne=>data b (hsub hb) hne) σ bin =
      phaseExitCommon D F η Z P d a rows z τ i hd bins data σ bin := by
  by_cases hne : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty
  · simp only [phaseExitCommon,dif_pos hb,dif_pos (hsub hb),dif_pos hne]
  · simp only [phaseExitCommon,dif_pos hb,dif_pos (hsub hb),dif_neg hne]

/-- Filtering phases at fixed σ and filtering descriptors at fixed phase
are the exact same finite original row sum. -/
lemma phaseExitClassNorm_filtered (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z : ℝ) (P : TransportParameters D) (d a : ℝ) (rows : Finset FreeRow) (z : ℂ) (τ : ℝ) (i : ℕ)
    (hd : (1/2:ℝ) ≤ d)
    (bins : Finset (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t))
    (data : ∀bin∈bins,∀hne : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty,
      ExitPhaseData D F η Z P d a rows z bin τ i)
    (x : ℂ)
    (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d))) :
    let small := bins.filter (phaseExitKeep D F η Z P d a rows z τ i bins data σ)
    (∑bin∈small,packetNorm D F
      (phaseExitCommon D F η Z P d a rows z τ i hd small
        (fun b hb hne=>data b (Finset.mem_filter.mp hb).1 hne) (fun _=>σ) bin) η Z x z (Z^Geometry.y)) =
    ∑bin∈bins,phaseExitClassNorm D F η Z P d a rows z τ i hd bins data x σ bin := by
  dsimp only
  calc
    _ = ∑bin∈bins.filter (phaseExitKeep D F η Z P d a rows z τ i bins data σ),
        packetNorm D F (phaseExitCommon D F η Z P d a rows z τ i hd bins data (fun _=>σ) bin)
          η Z x z (Z^Geometry.y) := by
      apply Finset.sum_congr rfl
      intro bin hb
      rw [phaseExitCommon_restrict D F η Z P d a rows z τ i hd bins _ (Finset.filter_subset _ _) data (fun _=>σ) bin hb]
    _ = _ := by rw [Finset.sum_filter];rfl

/-- On a genuine nonempty original phase, this is exactly the excluded
native descriptor packet sum required by the actual class split. -/
lemma phaseExitClassNorm_sum_eq (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z : ℝ) (P : TransportParameters D) (d a : ℝ) (rows : Finset FreeRow) (z : ℂ) (τ : ℝ) (i : ℕ)
    (hd : (1/2:ℝ) ≤ d) (hdhi : d ≤ 7/8)
    (bins : Finset (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t))
    (data : ∀bin∈bins,∀hne : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty,
      ExitPhaseData D F η Z P d a rows z bin τ i)
    (x : ℂ) (bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t)
    (hb : bin∈bins) (hne : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty) :
    (∑σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)),
      phaseExitClassNorm D F η Z P d a rows z τ i hd bins data x σ bin) =
    ∑σ∈Finset.univ.filter (fun σ=>¬(data bin hb hne).remaining σ),
      packetNorm D F (((data bin hb hne).bank.layout P (by linarith) hdhi).common σ) η Z x z (Z^Geometry.y) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro σ hσ
  simp only [phaseExitClassNorm,phaseExitKeep,dif_pos hb,dif_pos hne,phaseExitCommon,dif_pos hdhi]

#print axioms phaseExitClassNorm_filtered
#print axioms phaseExitClassNorm_sum_eq
end
end QRH.Cycle092.MixedUpperFinal
