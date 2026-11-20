/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual count Batches on LowActual-normalized measured medium cells. -/
import Candidate.C092.transport.MediumWitnessLowCompatibility

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open HeckeDetectorBatch HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
namespace QRH.Cycle092.MediumWitness
variable [Geometry.Parameters]

/-- Restriction retains every original family, witness and moment dictionary;
only the already finite row set is narrowed. -/
def restrictBatch {M : Ideal HeckeFamily.O} {H : Subgroup (HeckeFamily.O ⧸ M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (B : Batch M H Label Slot U a ε tstar T allowance i)
    (rows : Finset FreeRow) (hrows : rows ⊆ B.rows) : Batch M H Label Slot U a ε tstar T allowance i :=
  {B with rows:=rows
          row_norm:=fun u hu => B.row_norm u (hrows hu)
          row_coeff:=fun u hu => B.row_coeff u (hrows hu)}

lemma amplitudeCell_mono (D : BaselineData) (F : BaselineSourceData D) (Z d a : ℝ)
    (rows₁ rows₂ : Finset FreeRow) (z : Fin D.N → ℂ)
    (bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t) (hsub : rows₁ ⊆ rows₂) :
    amplitudeCell D F Z d a rows₁ z bin ⊆ amplitudeCell D F Z d a rows₂ z bin := by
  intro u hu
  exact Finset.mem_filter.mpr ⟨hsub (Finset.mem_filter.mp hu).1,(Finset.mem_filter.mp hu).2⟩

/-- Complete source Batch producer at the shared LowActual normalization.
The source constants and thresholds are uniform in the subsequently chosen
low payment, and both attaining-zero spikes remain those of the same Batch. -/
theorem original_shared_batches (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding τ r0 m0 : ℝ) (hτ : 0 < τ)
    (hheight : 4*τ < (1/200 : ℝ)*D.cost) (hcut0 : 1 ≤ r0+m0) (hcut1 : r0+m0 ≤ 3/2) :
    ∃ n : ℕ,0 < n ∧ ∀ η : Character,∀ᶠ Z : ℝ in atTop,1 < Z ∧
      ∃ idx grid : FreeRow → ℕ,ProbeAssembly.selected D F padding τ n η Z idx grid ∧
      ∀ (d threshold lowPay : ℝ),(1/200 : ℝ) ≤ d → d ≤ 7/8 → 1/50 < threshold →
      ∀ (i k : ℕ) (z : Fin D.N → ℂ),(∀ j,(z j).re=17/50) →
      (∀ j,|(z j).im| ≤ (3*i+1 : ℕ)*Z^τ) →
      let rows := sharedRows D F (Z^(Geometry.h+padding)) Z d threshold lowPay idx grid (fun _ => z) i k
      rows.Nonempty → threshold ≤ squaredBand D k ∧ squaredBand D k ≤ 3/4 ∧
      ∀ bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*bandLower D k-1)/2) D.t,
      (amplitudeCell D F Z d (bandLower D k) rows z bin).Nonempty →
      ∃ B : Batch F.modulus ⊤ (Sum Bool (RayQuotient.Characters F.modulus ⊤))
        (Fin D.N) (Z^d) (bandLower D k) D.ε (r0+m0) (Z^τ) ((Z^d)^(τ/(2*(7/8 : ℝ)))) i,
        B.rows=amplitudeCell D F Z d (bandLower D k) rows z bin ∧
        B.rows ⊆ rows ∧
        B.data=sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η ∧
        B.reverse=sourceMomentReverse F.modulus ⊤ ∧ B.slots=Finset.univ ∧
        B.widths=(fun j => D.length j/d) ∧ B.profile=(fun _ x => (F.w x : ℂ)) ∧
        B.upper=(fun _ => 2) ∧ B.external=z ∧ B.mesh=P.mesh ∧ B.binWidth=D.t ∧
        (∀ u∈B.rows,∀ j,B.family u j=originalFamily D F η u j) := by
  obtain ⟨n,hn,hsupplier⟩ := original_medium_batches D F P padding τ r0 m0 hτ hheight hcut0 hcut1
  refine ⟨n,hn,?_⟩
  intro η
  filter_upwards [hsupplier η] with Z hZ
  obtain ⟨idx,grid,hsel,hrest⟩ := hZ.2
  refine ⟨hZ.1,idx,grid,hsel,?_⟩
  intro d threshold lowPay hd hd' hthreshold i k z hz hzim
  dsimp only
  intro hne
  have hsub := sharedRows_subset_mediumRows D F (Z^(Geometry.h+padding)) Z d threshold lowPay idx grid (fun _ => z) i k hZ.1
  obtain ⟨hband,hbatch⟩ := hrest d threshold hd hd' hthreshold i k z hz hzim (hne.mono hsub)
  refine ⟨hband.response_lower,hband.band_upper,?_⟩
  intro bin hneBin
  have hsubAmp := amplitudeCell_mono D F Z d (bandLower D k) _ _ z bin hsub
  obtain ⟨B,hBr,hData,hRev,hSlots,hWidths,hW,hUpper,hExternal,hMesh,hBin,hFamily⟩ :=
    hbatch bin (hneBin.mono hsubAmp)
  have hrestrict : amplitudeCell D F Z d (bandLower D k)
      (sharedRows D F (Z^(Geometry.h+padding)) Z d threshold lowPay idx grid (fun _ => z) i k) z bin ⊆ B.rows := by
    rw [hBr]
    exact hsubAmp
  let B' := restrictBatch B _ hrestrict
  refine ⟨B',rfl,?_,hData,hRev,hSlots,hWidths,hW,hUpper,hExternal,hMesh,hBin,?_⟩
  · exact Finset.filter_subset _ _
  · intro u hu j
    exact hFamily u (hrestrict hu) j

end QRH.Cycle092.MediumWitness
