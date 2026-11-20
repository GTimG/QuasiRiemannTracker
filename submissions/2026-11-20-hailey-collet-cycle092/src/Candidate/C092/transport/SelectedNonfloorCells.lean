/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Complete actual nonfloor row-dyad/height/amplitude-cell summation. -/
import Candidate.C092.transport.SelectedNonfloorBudget
import Candidate.C092.transport.SelectedActualIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
open Filter
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open Cycle25.Weighted.FullWContour
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.ProbeAssembly
namespace QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters]

def fullW (D : BaselineData) (F : BaselineSourceData D) (padding tau : ℝ) (η : Character)
    (Z : ℝ) (idx grid : FreeRow → ℕ) : ℂ :=
  finiteCentralFullWRows F.S F.exclusions F.maximal η
    (SelectedActualIntegral.selectedRows D F padding Z grid)
    (SelectedActualIntegral.primePool D F Z) (SelectedActualIntegral.pool_outside D F Z)
    (fun _ => F.W) (fun j => Z^(D.length j)) F.W F.W
    (Z^Geometry.x) (Z^Geometry.y) Z D.e (fun u => 51/100+D.e*grid u)
    (fun u => (3*idx u+1:ℕ)*Z^tau)

def cellRows (D : BaselineData) (F : BaselineSourceData D) (padding Z : ℝ)
    (idx grid : FreeRow → ℕ) (k i j : ℕ) : Finset FreeRow :=
  cubeBinRows (SelectedActualIntegral.selectedRows D F padding Z grid ∩ dyadicRows 1 k) idx grid i j

def cellValue (D : BaselineData) (F : BaselineSourceData D) (padding tau : ℝ)
    (η : Character) (Z : ℝ) (idx grid : FreeRow → ℕ) (k i j : ℕ) : ℂ :=
  finiteCentralFullWRows F.S F.exclusions F.maximal η (cellRows D F padding Z idx grid k i j)
    (SelectedActualIntegral.primePool D F Z) (SelectedActualIntegral.pool_outside D F Z)
    (fun _ => F.W) (fun j => Z^(D.length j)) F.W F.W
    (Z^Geometry.x) (Z^Geometry.y) Z D.e (fun _ => 51/100+D.e*j)
    (fun _ => (3*i+1:ℕ)*Z^tau)

/-- This is a finite cell interface below the original integral. A supplier
uses the full packet/source/count estimates and the exact physical price;
the positive allowance pays the actual number of row dyads only once. -/
def CellBound (D : BaselineData) (F : BaselineSourceData D) (padding tau saving allowance : ℝ)
    (n : ℕ) (η : Character) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ idx grid : FreeRow → ℕ,
    selected D F padding tau n η Z idx grid →
    ∀ k ∈ smallDyadicIndices (Z^(Geometry.h+padding)), ∀ i ∈ Finset.range (n+1),
    ∀ j ∈ Finset.range (⌊(49/100:ℝ)/D.e⌋₊+1),
    (cellRows D F padding Z idx grid k i j).Nonempty →
    ‖cellValue D F padding tau η Z idx grid k i j/normalizer D F Z‖ ≤
      C*Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-saving-allowance)

def FullWBound (D : BaselineData) (F : BaselineSourceData D) (padding tau saving : ℝ)
    (n : ℕ) (η : Character) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ idx grid : FreeRow → ℕ,
    selected D F padding tau n η Z idx grid →
    ‖fullW D F padding tau η Z idx grid/normalizer D F Z‖ ≤
      C*Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-saving)

/-- All dyads and every original finite height/amplitude grid are summed.
The finite packet sum was already completed before invoking this theorem. -/
theorem fullW_bound_of_cells (D : BaselineData) (F : BaselineSourceData D)
    (padding tau saving allowance : ℝ) (hallowance : 0 < allowance)
    (hupper : Geometry.h+padding ≤ 1) (n : ℕ) (η : Character)
    (hcell : CellBound D F padding tau saving allowance n η) :
    FullWBound D F padding tau saving n η := by
  obtain ⟨C, hC, hc⟩ := hcell
  obtain ⟨Cd, hCd, hd⟩ := canonical_dyad_cost allowance hallowance
  let m : ℕ := ⌊(49/100:ℝ)/D.e⌋₊
  refine ⟨Cd*(n+1:ℕ)*(m+1:ℕ)*C, by positivity, ?_⟩
  filter_upwards [hc, eventually_gt_atTop (1:ℝ)] with Z hc hZ
  intro idx grid hs
  have hR (u : FreeRow) (hu : u ∈ SelectedActualIntegral.selectedRows D F padding Z grid) :
      u.val ≠ 1 ∧ rowNorm u ≤ Z^(Geometry.h+padding) := by
    have hh := (mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu
    have hb := mem_rowBand.mp hh.1
    exact ⟨hb.1, hb.2.2.le⟩
  have hlabels (u : FreeRow) (_hu : u ∈ SelectedActualIntegral.selectedRows D F padding Z grid) :
      idx u ≤ n ∧ grid u ≤ m := ⟨(hs.1 u).2.1, (hs.1 u).2.2.1⟩
  have hh := SelectedFloorEstimate.Partition.fullW_cells_norm_bound F.S F.exclusions F.maximal η
    (SelectedActualIntegral.selectedRows D F padding Z grid) (SelectedActualIntegral.primePool D F Z)
    (SelectedActualIntegral.pool_outside D F Z) (fun _ => F.W) (fun j => Z^(D.length j)) F.W F.W
    (Z^Geometry.x) (Z^Geometry.y) Z D.e (Z^tau) (Z^(Geometry.h+padding)) idx grid n m
    (normalizer D F Z) (C*Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-saving-allowance))
    (by positivity) hR hlabels (hc idx grid hs)
  have hdyad := hd Z (Geometry.h+padding) hZ.le hupper
  calc
    _ ≤ _ := hh
    _ ≤ (Cd*Z^allowance)*(n+1:ℕ)*(m+1:ℕ)*
        (C*Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-saving-allowance)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdyad (by positivity))
          (by positivity)) (by positivity)
    _ = _ := by
      rw [show HeckeZeroSupremum.beta+ProbeAssembly.shift-saving =
        allowance+(HeckeZeroSupremum.beta+ProbeAssembly.shift-saving-allowance) by ring,
        Real.rpow_add (zero_lt_one.trans hZ)]
      ring

end QRH.Cycle092.SelectedNonfloor
#print axioms QRH.Cycle092.SelectedNonfloor.fullW_bound_of_cells
