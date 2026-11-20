/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal calibrated medium cells on the original row band, with their actual
common detector band derived from measured response and buffered selection. -/
import Candidate.C092.transport.MediumWitnessResponse

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
namespace QRH.Cycle092.MediumWitness
variable [Geometry.Parameters]

/-- The same original rows, partitioned only by actual calibration, conductor,
measured canonical response, and the already chosen buffer/grid labels. -/
def mediumRows (D : BaselineData) (F : BaselineSourceData D)
    (rowCap Z d threshold : ℝ) (idx grid : FreeRow → ℕ)
    (z : FreeRow → Fin D.N → ℂ) (i k : ℕ) : Finset FreeRow :=
  (rowBand (Z^(1/100 : ℝ)) rowCap).filter fun u =>
    (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
    rowNorm u ≤ Z^(d-D.t) ∧ threshold ≤ canonicalResponse D F Z (z u) u ∧ idx u=i ∧ grid u=k

lemma mem_mediumRows (D : BaselineData) (F : BaselineSourceData D)
    (rowCap Z d threshold : ℝ) (idx grid : FreeRow → ℕ)
    (z : FreeRow → Fin D.N → ℂ) (i k : ℕ) (u : FreeRow) :
    u∈mediumRows D F rowCap Z d threshold idx grid z i k ↔
      u∈rowBand (Z^(1/100 : ℝ)) rowCap ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
      rowNorm u ≤ Z^(d-D.t) ∧ threshold ≤ canonicalResponse D F Z (z u) u ∧ idx u=i ∧ grid u=k :=
  Finset.mem_filter

def bandLower (D : BaselineData) (k : ℕ) : ℝ := 51/100+D.e*k

def squaredBand (D : BaselineData) (k : ℕ) : ℝ := 2*bandLower D k-1

/-- Every analytic condition needed by the original source-cube witness
supplier, certified on the literal measured medium cell. -/
structure CommonBand (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (rowCap Z τ d threshold : ℝ) (n : ℕ) (idx grid : FreeRow → ℕ)
    (z : FreeRow → Fin D.N → ℂ) (i k : ℕ) : Prop where
  response_lower : threshold ≤ squaredBand D k
  band_upper : squaredBand D k ≤ 3/4
  nonfloor : 51/100 < bandLower D k
  a_upper : bandLower D k ≤ 7/8
  index_bound : i ≤ n
  rows_supported : mediumRows D F rowCap Z d threshold idx grid z i k ⊆
    supportedNonfloorRows F.S F.maximal (rowBand (Z^(1/100 : ℝ)) rowCap) grid
  rows_band : mediumRows D F rowCap Z d threshold idx grid z i k ⊆
    rowBand (Z^(1/100 : ℝ)) rowCap
  calibration : ∀ u∈mediumRows D F rowCap Z d threshold idx grid z i k,
    (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0
  conductor : ∀ u∈mediumRows D F rowCap Z d threshold idx grid z i k,rowNorm u ≤ Z^(d-D.t)
  current : ∀ u∈mediumRows D F rowCap Z d threshold idx grid z i k,
    bandLower D k ≤ detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u
      (rayCubeFamily F.modulus ⊤ le_top u)) ((3*i : ℕ)*Z^τ)
  next : ∀ u∈mediumRows D F rowCap Z d threshold idx grid z i k,
    detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u
      (rayCubeFamily F.modulus ⊤ le_top u)) (3*(i+1 : ℕ)*Z^τ) < bandLower D k+2*D.e

/-- No lower-a, nonfloor, conductor, calibration, or next-band inequality is
assumed here. All come from actual row membership and existing source theorems. -/
theorem actual_common_band (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (τ : ℝ) (n : ℕ) (hτ : 0 < τ)
    (hheight : 4*τ < (1/200 : ℝ)*D.cost) :
    ∀ᶠ Z : ℝ in atTop,1 < Z ∧ ∀ (d padding rowCap threshold : ℝ),
      (1/200 : ℝ) ≤ d → d ≤ 7/8 → 1/50 < threshold →
      ∀ (η : Character) (idx grid : FreeRow → ℕ),ProbeAssembly.selected D F padding τ n η Z idx grid →
      ∀ z : FreeRow → Fin D.N → ℂ,(∀ u j,(z u j).re=17/50) →
      (∀ u j,|(z u j).im| ≤ (3*idx u+1 : ℕ)*Z^τ) →
      ∀ i k : ℕ,(mediumRows D F rowCap Z d threshold idx grid z i k).Nonempty →
      CommonBand D F η rowCap Z τ d threshold n idx grid z i k := by
  have hr := response_bounded_from_actual_selection D F P τ n hτ hheight
  filter_upwards [hr] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d padding rowCap threshold hd hd' hthreshold η idx grid hsel z hz hzim i k hne
  obtain ⟨u,hu⟩ := hne
  have hf := (mem_mediumRows D F rowCap Z d threshold idx grid z i k u).mp hu
  have hulo := (mem_rowBand.mp hf.1).2.1
  have hresponse := (hZ.2 d padding hd hd' η idx grid hsel u hulo hf.2.1 hf.2.2.1 (z u) (hz u) (hzim u)).2
  have hgrid := hf.2.2.2.2.2
  have hidx := hf.2.2.2.2.1
  have hresp : threshold ≤ squaredBand D k := by
    unfold squaredBand bandLower
    rw [hgrid] at hresponse
    exact hf.2.2.2.1.trans hresponse
  have hnonfloor : 51/100 < bandLower D k := by unfold squaredBand at hresp;linarith
  have hs := hsel
  change _ ∧ _ ∧ _ at hs
  have hb := hs.2.1 u
  have hupper : bandLower D k ≤ 7/8 := by simpa only [bandLower,hgrid] using hb.2.1
  have hk : k ≠ 0 := by
    intro hk
    rw [hk] at hnonfloor
    norm_num [bandLower] at hnonfloor
  have hindex : i ≤ n := by simpa only [hidx] using (hs.1 u).2.1
  refine ⟨hresp,by unfold squaredBand;linarith,hnonfloor,hupper,hindex,?_,?_,?_,?_,?_,?_⟩
  · intro v hv
    have hh := (mem_mediumRows D F rowCap Z d threshold idx grid z i k v).mp hv
    exact (mem_supportedNonfloorRows F.S F.maximal _ grid v).mpr
      ⟨hh.1,hh.2.1,fun h => hk (hh.2.2.2.2.2 ▸ h)⟩
  · intro v hv
    exact ((mem_mediumRows D F rowCap Z d threshold idx grid z i k v).mp hv).1
  · intro v hv
    exact ((mem_mediumRows D F rowCap Z d threshold idx grid z i k v).mp hv).2.1
  · intro v hv
    exact ((mem_mediumRows D F rowCap Z d threshold idx grid z i k v).mp hv).2.2.1
  · intro v hv
    have hh := (mem_mediumRows D F rowCap Z d threshold idx grid z i k v).mp hv
    have hb := (hs.2.1 v).2.2.1
    simpa only [bandLower,hh.2.2.2.2.1,hh.2.2.2.2.2,Nat.cast_mul,Nat.cast_ofNat] using hb
  · intro v hv
    have hh := (mem_mediumRows D F rowCap Z d threshold idx grid z i k v).mp hv
    have hb := (hs.2.1 v).2.2.2.2.1
    simpa only [bandLower,hh.2.2.2.2.1,hh.2.2.2.2.2,Nat.cast_mul,Nat.cast_ofNat] using hb

end QRH.Cycle092.MediumWitness
