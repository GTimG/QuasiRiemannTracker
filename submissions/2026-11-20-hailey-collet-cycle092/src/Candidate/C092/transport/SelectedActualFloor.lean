/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original supported floor/nonfloor identity is OpenAI's; the literal
finite-cube transport and source interfaces follow the credited Collet/Levy/Gao
development and Bebel's positive averaged-floor transport. -/
import Candidate.C092.transport.SelectedActualData

/-!
Exact separation of the outstanding SelectedTransport estimate into full-row
contour transport and the normalized supported floor. The buffered selection
and normalizer are constructed, not assumed. The two displayed error inputs
remain unproved at Q; this file does not replace them by scalar certificates.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Filter
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open OAI.SevenEighths.ProbeHighRowFamily OAI.SevenEighths.HeckeInverseAmplification
open OAI.SevenEighths.ProbeRaySlots
open OAI.SevenEighths.ProbePhysical OAI.SevenEighths.PrincipalSignalComparison
open OAI.SevenEighths.BoundaryDensitySplitReturn.TransportHighTransport
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.ProbeAssembly

namespace QRH.Cycle092.SelectedActualFloor
variable [Geometry.Parameters]

def cube (D : BaselineData) (F : BaselineSourceData D) (tau : ℝ)
    (η : Character) (Z : ℝ) (rows : Finset FreeRow)
    (alpha : FreeRow → ℝ) (idx : FreeRow → ℕ) : ℂ :=
  let Yp := fun j => Z^(D.length j)
  let T := fun j => pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Yp j)
  let hT : ∀ j P, P ∈ T j → P.val ∉ F.S :=
    fun j P hP => (mem_pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Yp j) P).mp hP |>.2.2.2
  finiteCentralCubeRows F.S F.exclusions F.maximal η rows T hT
    (fun (_ : Fin D.N) y => (F.w y : ℂ)) Yp F.W F.W
    (Z^Geometry.x) (Z^Geometry.y) Z D.e alpha (fun u => (3*idx u+1 : ℕ)*Z^tau)

def whole (D : BaselineData) (F : BaselineSourceData D) (padding tau : ℝ)
    (η : Character) (Z : ℝ) (idx grid : FreeRow → ℕ) : ℂ :=
  cube D F tau η Z (rowBand (Z^(1/100 : ℝ)) (Z^(Geometry.h+padding)))
    (fun u => 51/100+D.e*grid u) idx

def floor (D : BaselineData) (F : BaselineSourceData D) (padding tau : ℝ)
    (η : Character) (Z : ℝ) (idx grid : FreeRow → ℕ) : ℂ :=
  cube D F tau η Z
    (supportedFloorRows F.S F.maximal (rowBand (Z^(1/100 : ℝ)) (Z^(Geometry.h+padding))) grid)
    (fun _ => 51/100) idx

/-- Exact equality, retaining the calibration mask, full row band and natural
zero-grid filtering in both original pieces. -/
theorem whole_split (D : BaselineData) (F : BaselineSourceData D)
    (padding tau : ℝ) (η : Character) (Z : ℝ) (idx grid : FreeRow → ℕ) :
    whole D F padding tau η Z idx grid =
      floor D F padding tau η Z idx grid + numerator D F padding tau η Z idx grid := by
  let Yp := fun j => Z^(D.length j)
  let T := fun j => pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Yp j)
  let hT : ∀ j P, P ∈ T j → P.val ∉ F.S :=
    fun j P hP => (mem_pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Yp j) P).mp hP |>.2.2.2
  exact finiteCentralCubeRows_supported_split F.S F.exclusions F.maximal η
    (rowBand (Z^(1/100 : ℝ)) (Z^(Geometry.h+padding))) T hT
    (fun (_ : Fin D.N) y => (F.w y : ℂ)) Yp F.W F.W
    (Z^Geometry.x) (Z^Geometry.y) Z D.e grid (fun u => (3*idx u+1 : ℕ)*Z^tau)

/-- Full-row contour/principal transport, uniform on the actual buffered
choices. This is the first remaining analytic estimate. -/
def FullTransportBound (D : BaselineData) (F : BaselineSourceData D)
    (padding tau saving : ℝ) (n : ℕ) (η : Character) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ idx grid : FreeRow → ℕ,
    selected D F padding tau n η Z idx grid →
    ‖residual D F η Z-whole D F padding tau η Z idx grid/normalizer D F Z‖ ≤
      C*Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-saving)

/-- The normalized genuine supported floor. This is the second remaining
analytic estimate; its actual-source/count proof is separate. -/
def FloorBound (D : BaselineData) (F : BaselineSourceData D)
    (padding tau saving : ℝ) (n : ℕ) (η : Character) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ idx grid : FreeRow → ℕ,
    selected D F padding tau n η Z idx grid →
    ‖floor D F padding tau η Z idx grid/normalizer D F Z‖ ≤
      C*Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-saving)

/-- Given those two literal estimates, no additional source, normalization,
selection, conductor or cap hypothesis remains in SelectedTransport. The
common saving is fixed before the character and is the minimum of the two. -/
theorem selected_transport_of_full_and_floor (D : BaselineData) (F : BaselineSourceData D)
    (padding tau fullSaving floorSaving : ℝ) (htau : 0 < tau)
    (hfull : ∀ n : ℕ, 0 < n → ∀ η : Character,
      FullTransportBound D F padding tau fullSaving n η)
    (hfloor : ∀ n : ℕ, 0 < n → ∀ η : Character,
      FloorBound D F padding tau floorSaving n η) :
    ∃ n : ℕ, 0 < n ∧ ∀ η : Character,
      SelectedTransport D F padding tau (min fullSaving floorSaving) n η := by
  obtain ⟨n, hn, hselection⟩ := SelectedActual.normalized_buffered_selection D F padding tau htau
  refine ⟨n, hn, ?_⟩
  intro η
  obtain ⟨Ct, hCt, ht⟩ := hfull n hn η
  obtain ⟨Cf, hCf, hf⟩ := hfloor n hn η
  refine ⟨Ct+Cf, by positivity, ?_⟩
  filter_upwards [hselection, ht, hf, eventually_ge_atTop (1 : ℝ)] with Z hs ht hf hZ
  obtain ⟨hN, hsel⟩ := hs
  obtain ⟨idx, grid, hsel⟩ := hsel η
  refine ⟨hN, idx, grid, hsel, ?_⟩
  have hwhole := ht idx grid hsel
  have hfloor := hf idx grid hsel
  let E := Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-min fullSaving floorSaving)
  have het : Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-fullSaving) ≤ E :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith [min_le_left fullSaving floorSaving])
  have hef : Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-floorSaving) ≤ E :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith [min_le_right fullSaving floorSaving])
  have heq : residual D F η Z-numerator D F padding tau η Z idx grid/normalizer D F Z =
      (residual D F η Z-whole D F padding tau η Z idx grid/normalizer D F Z)+
        floor D F padding tau η Z idx grid/normalizer D F Z := by
    rw [whole_split]
    ring
  rw [heq]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ Ct*E+Cf*E := add_le_add
      (hwhole.trans (mul_le_mul_of_nonneg_left het hCt.le))
      (hfloor.trans (mul_le_mul_of_nonneg_left hef hCf.le))
    _ = (Ct+Cf)*E := by ring

end QRH.Cycle092.SelectedActualFloor
#print axioms QRH.Cycle092.SelectedActualFloor.whole_split
#print axioms QRH.Cycle092.SelectedActualFloor.selected_transport_of_full_and_floor
