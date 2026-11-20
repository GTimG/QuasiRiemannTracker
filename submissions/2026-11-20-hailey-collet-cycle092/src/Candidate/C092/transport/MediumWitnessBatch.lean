/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Constructs the original detector Batch on the derived measured medium cells,
so the same-zero fibers feed the actual ordinary/inverse source counts. -/
import Candidate.C092.transport.MediumWitnessOriginal
import Submissions.hailey_collet_1252270103.Record1252270103Return.RetainedBatches

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

/-- A fixed i-cell only reads z at rows with idx=i. Giving other rows zero
height therefore preserves the literal measured cell exactly. -/
def cellHeights {N : ℕ} (idx : FreeRow → ℕ) (i : ℕ) (z : Fin N → ℂ) : FreeRow → Fin N → ℂ :=
  fun u j => if idx u=i then z j else (17/50 : ℂ)

lemma mediumRows_cellHeights (D : BaselineData) (F : BaselineSourceData D)
    (rowCap Z d threshold : ℝ) (idx grid : FreeRow → ℕ) (z : Fin D.N → ℂ) (i k : ℕ) :
    mediumRows D F rowCap Z d threshold idx grid (cellHeights idx i z) i k=
      mediumRows D F rowCap Z d threshold idx grid (fun _ => z) i k := by
  ext u
  by_cases hi : idx u=i
  · have he : cellHeights idx i z u=z := by funext j;simp [cellHeights,hi]
    simp only [mem_mediumRows,he]
  · simp [mem_mediumRows,hi]

def originalPhysical (D : BaselineData) (F : BaselineSourceData D) (Z d : ℝ)
    (z : Fin D.N → ℂ) : FreeRow → Fin D.N → ℂ :=
  HeckeDetectorPhysicalSelection.physical F.modulus ⊤ (fun u : FreeRow => u.val)
    (fun _ x => (F.w x : ℂ)) (fun _ => 2) (fun j => D.length j/d) z (Z^d)

lemma originalPhysical_eq (D : BaselineData) (F : BaselineSourceData D) (Z d : ℝ)
    (hZ : 0 < Z) (hd : 0 < d) (z : Fin D.N → ℂ) (u : FreeRow) (j : Fin D.N) :
    originalPhysical D F Z d z u j=
      HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) (z j) := by
  unfold originalPhysical HeckeDetectorPhysicalSelection.physical
  have he : (Z^d)^(D.length j/d)=Z^(D.length j) := by
    rw [←Real.rpow_mul hZ.le,mul_div_cancel₀ _ hd.ne']
  rw [he]
  have hW : (fun x => (F.w x : ℂ))=(F.W : ℝ → ℂ) := funext (fun x => (F.complex_eq x).symm)
  change HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val (fun x => (F.w x : ℂ)) 2 (Z^(D.length j)) (z j)=_
  rw [hW]

def amplitudeCell (D : BaselineData) (F : BaselineSourceData D) (Z d a : ℝ)
    (rows : Finset FreeRow) (z : Fin D.N → ℂ)
    (bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t) : Finset FreeRow :=
  amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos
    (fun j => D.length j/d) (originalPhysical D F Z d z) bin

/-- Literal construction at a preselected cutoff. The whole source Batch,
including its original source dictionary and same-zero supported witnesses,
is supplied from the proved medium band; no cardinality or moment is assumed. -/
theorem original_medium_batches (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding τ r0 m0 : ℝ) (hτ : 0 < τ)
    (hheight : 4*τ < (1/200 : ℝ)*D.cost) (hcut0 : 1 ≤ r0+m0) (hcut1 : r0+m0 ≤ 3/2) :
    ∃ n : ℕ,0 < n ∧ ∀ η : Character,∀ᶠ Z : ℝ in atTop,1 < Z ∧
      ∃ idx grid : FreeRow → ℕ,ProbeAssembly.selected D F padding τ n η Z idx grid ∧
      ∀ (d threshold : ℝ),(1/200 : ℝ) ≤ d → d ≤ 7/8 → 1/50 < threshold →
      ∀ (i k : ℕ) (z : Fin D.N → ℂ),(∀ j,(z j).re=17/50) →
      (∀ j,|(z j).im| ≤ (3*i+1 : ℕ)*Z^τ) →
      let rows := mediumRows D F (Z^(Geometry.h+padding)) Z d threshold idx grid (fun _ => z) i k
      rows.Nonempty → CommonBand D F η (Z^(Geometry.h+padding)) Z τ d threshold n idx grid (cellHeights idx i z) i k ∧
      ∀ bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*bandLower D k-1)/2) D.t,
      (amplitudeCell D F Z d (bandLower D k) rows z bin).Nonempty →
      ∃ B : Batch F.modulus ⊤ (Sum Bool (RayQuotient.Characters F.modulus ⊤))
        (Fin D.N) (Z^d) (bandLower D k) D.ε (r0+m0) (Z^τ) ((Z^d)^(τ/(2*(7/8 : ℝ)))) i,
        B.rows=amplitudeCell D F Z d (bandLower D k) rows z bin ∧
        B.data=sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η ∧
        B.reverse=sourceMomentReverse F.modulus ⊤ ∧ B.slots=Finset.univ ∧
        B.widths=(fun j => D.length j/d) ∧ B.profile=(fun _ x => (F.w x : ℂ)) ∧
        B.upper=(fun _ => 2) ∧ B.external=z ∧ B.mesh=P.mesh ∧ B.binWidth=D.t ∧
        (∀ u∈B.rows,∀ j,B.family u j=originalFamily D F η u j) := by
  obtain ⟨n,hn,hselect⟩ := SelectedActual.buffered_selection D F padding τ hτ
  refine ⟨n,hn,?_⟩
  intro η
  have hband := actual_common_band D F P τ n hτ hheight
  have hbatch := GenericCount.actual_source_amplitude_batches_at_cutoff F.modulus ⊤ le_top
    F.S F.exclusions F.maximal η (1/200) (7/8) τ D.ε D.e D.witnessKappa D.cost D.t P.mesh D.t n
    (fun _ _ => r0+m0) (fun _ _ _ _ _ _ => ⟨hcut0,hcut1⟩)
    (by norm_num) (by norm_num) hτ (witness_zero_height_from_budget D hheight) hheight
    D.epsilon_pos D.e_pos D.e_small D.witnessKappa_pos D.witnessKappa_small D.cost_pos.le
    D.t_pos P.mesh_pos.le D.t_pos D.detector_budget
  filter_upwards [hselect,hband,hbatch] with Z hselect hband hbatch
  obtain ⟨idx,grid,hsel⟩ := hselect η
  refine ⟨hband.1,idx,grid,hsel,?_⟩
  intro d threshold hd hd' hthreshold i k z hz hzim
  dsimp only
  intro hne
  have hgateRe : ∀ u j,(cellHeights idx i z u j).re=17/50 := by
    intro u j
    by_cases h : idx u=i <;> simp [cellHeights,h,hz]
  have hgateIm : ∀ u j,|(cellHeights idx i z u j).im| ≤ (3*idx u+1 : ℕ)*Z^τ := by
    intro u j
    by_cases h : idx u=i
    · simpa [cellHeights,h] using hzim j
    · norm_num [cellHeights,h]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (zero_lt_one.trans hband.1).le _)
  have hne' := hne
  rw [←mediumRows_cellHeights D F (Z^(Geometry.h+padding)) Z d threshold idx grid z i k] at hne'
  have hb := hband.2 d padding (Z^(Geometry.h+padding)) threshold hd hd' hthreshold
    η idx grid hsel (cellHeights idx i z) hgateRe hgateIm i k hne'
  refine ⟨hb,?_⟩
  intro bin hneBin
  have hrows := hb.rows_band
  have hcal := hb.calibration
  have hrow := hb.conductor
  have hnext := hb.next
  have hcurrent := hb.current
  rw [mediumRows_cellHeights] at hrows hcal hrow hnext hcurrent
  have hsmall (j : Fin D.N) : D.length j ≤ (1/200 : ℝ)*P.mesh := by
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using P.slots_mesh j
  have hsum : (7/37 : ℝ)*(7/8) ≤ ∑ j,D.length j := by
    rw [D.slots_sum]
    linarith [Geometry.sixth_lt_ell]
  obtain ⟨B,hBr,hData,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam,hMean⟩ :=
    hbatch d hd hd' (Z^(Geometry.h+padding))
      (mediumRows D F (Z^(Geometry.h+padding)) Z d threshold idx grid (fun _ => z) i k)
      hne hrows hcal hrow (bandLower D k) i hb.index_bound hb.nonfloor hb.a_upper hnext hcurrent
      D.N D.length D.slots_pos hsmall hsum (fun _ x => (F.w x : ℂ)) (fun _ => 2) z bin hneBin
  exact ⟨B,hBr,hData,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,fun u hu j => hFam u (hBr ▸ hu) j⟩

end QRH.Cycle092.MediumWitness
