/- Repeated marks: fork of Collet's generic return module PhysicalDirect.Finite.Summation (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/
import Submissions.arvi_repeated_marks_20261024.ReturnD.PhysicalDirect.Finite.Geometry
import Submissions.arvi_repeated_marks_20261024.ReturnD.Schedule
import Submissions.arvi_repeated_marks_20261024.ReturnD.GenericScalar

set_option autoImplicit false
namespace QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect.FiniteNumerator
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
noncomputable section
set_option maxHeartbeats 200000
variable [QRH.Record1252270103Return.Geometry.Parameters] [QRH.Record1252270103Return.Geometry.BoundsR]
variable [scheme : QRH.Record1252270103Return.CountScheme] [QRH.RepeatedMarks.Return.GenericArithmetic.PhysicalSchedule]
open QRH.RepeatedMarks.Return.GenericArithmetic QRH.Record1252270103Return.GenericPhysical OAI OAI.SevenEighths
open scoped Classical BigOperators
open QRH.Record1252270103Return.GenericPhysical (baselineSource)
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect QRH.RepeatedMarks.Return.GenericPhysical.FinalAssembly OAI.SevenEighths.RepeatedMarksReturn.TransportHighTransport
open QRH.RepeatedMarks.Return.GenericPhysical.Assembly

def FullWCellsAt (A : ChosenData) (τ : ℝ) (n : ℕ) (η : Character) (C Z : ℝ) : Prop :=
  ∀idx grid : FreeRow→ℕ,
    ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
      η rowPadding A.D.e τ n Z idx grid →
    ∀k∈smallDyadicIndices (Z^(QRH.RepeatedMarks.Return.GenericArithmetic.h+rowPadding)),
    ∀i∈Finset.range (n+1),∀j∈Finset.range (⌊(49/100:ℝ)/A.D.e⌋₊+1),
      (cellRows A.D A.F Z idx grid k i j).Nonempty →
      ‖fullW A.D A.F η Z (cellRows A.D A.F Z idx grid k i j)
        (fun _=>51/100+A.D.e*j) (fun _=>(3*i+1:ℕ)*Z^τ)/normalizer A.D A.F Z‖ ≤
        C*Z^(cellTarget+A.D.t/8)

/-- The genuine normalized full-W cell theorem fixes its degree before height. -/
def ActualFullWCellInput (A : ChosenData) (J : ℝ) : Prop :=
  ∀τ : ℝ,HeightAdmissible A.D A.P J τ → ∀n : ℕ,∀η : Character,
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,∀C0 : ℝ,1≤ C0 →
      SourceMomentBound A.D (baselineSource A.D A.F) A.counts η Z τ
        (C0*Z^A.D.t) (Z^(2*τ)) →
      FullWCellsAt A τ n η (C*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps)) Z

theorem cell_exponent_le (A : ChosenData) :
    cellTarget+A.D.t/4≤ HeckeZeroSupremum.beta+QRH.RepeatedMarks.Return.GenericPhysical.Assembly.signalShift-A.P.sigma := by
  have ht:=A.P.t_padding
  have hs:=A.P.sigma_small
  have hc:=A.count_budget
  have he:=A.D.epsilon_pos
  have htp:=A.D.t_pos
  have hfee : 0≤QRH.RepeatedMarks.Return.GenericArithmetic.rowFee := by norm_num [QRH.RepeatedMarks.Return.GenericArithmetic.rowFee]
  dsimp [cellTarget,QRH.RepeatedMarks.Return.GenericPhysical.Scalar.sourceReserve]
  linarith

theorem fullW_sum_bound (A : ChosenData) (τ : ℝ) (n : ℕ) (η : Character)
    (C : ℝ) (hC : 0< C) :
    ∃Csum : ℝ,0< Csum ∧ ∀ᶠZ : ℝ in atTop,
      FullWCellsAt A τ n η C Z → ∀idx grid : FreeRow→ℕ,
      ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
        η rowPadding A.D.e τ n Z idx grid →
      ‖fullW A.D A.F η Z (selectedRows A.D A.F Z grid)
        (fun u=>51/100+A.D.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normalizer A.D A.F Z‖ ≤
        Csum*Z^(HeckeZeroSupremum.beta+QRH.RepeatedMarks.Return.GenericPhysical.Assembly.signalShift-A.P.sigma) := by
  have ht:=A.D.t_pos
  obtain ⟨Cd,hCd,hdyad⟩:=canonical_dyad_cost (A.D.t/8) (by positivity)
  let m : ℕ:=⌊(49/100:ℝ)/A.D.e⌋₊
  refine ⟨Cd*(n+1:ℕ)*(m+1:ℕ)*C,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with Z hZ
  intro hcell idx grid hsel
  have hZp : 0< Z:=zero_lt_one.trans_le hZ
  have hrows:=selected_rows_facts A.D A.F Z grid
  have hb:=fullW_cells_norm_bound A.F.S A.F.exclusions A.F.maximal η
    (selectedRows A.D A.F Z grid) (primePool A.D A.F Z) (poolOutside A.D A.F Z)
    (fun _ y=>(A.F.w y:ℂ)) (fun j=>Z^(A.D.length j)) A.F.W A.F.W
    (Z^QRH.RepeatedMarks.Return.GenericArithmetic.x) (Z^QRH.RepeatedMarks.Return.GenericArithmetic.y) Z A.D.e (Z^τ) (Z^(QRH.RepeatedMarks.Return.GenericArithmetic.h+rowPadding))
    idx grid n m (normalizer A.D A.F Z) (C*Z^(cellTarget+A.D.t/8)) (by positivity)
    (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.2.2⟩)
    (fun u _=>⟨(hsel.1 u).2.1,(hsel.1 u).2.2.1⟩) (hcell idx grid hsel)
  have htop : QRH.RepeatedMarks.Return.GenericArithmetic.h+rowPadding≤1 := by
    change QRH.Record1252270103Return.Geometry.h+1/20000000000≤1
    linarith [QRH.Record1252270103Return.Geometry.BoundsR.h_interval.2]
  have hd:=hdyad Z (QRH.RepeatedMarks.Return.GenericArithmetic.h+rowPadding) hZ htop
  have hexp:=Real.rpow_le_rpow_of_exponent_le hZ (cell_exponent_le A)
  calc
    _ ≤ ((smallDyadicIndices (Z^(QRH.RepeatedMarks.Return.GenericArithmetic.h+rowPadding))).card:ℝ)*(n+1:ℕ)*(m+1:ℕ)*
        (C*Z^(cellTarget+A.D.t/8)) := hb
    _ ≤ (Cd*Z^(A.D.t/8))*(n+1:ℕ)*(m+1:ℕ)*(C*Z^(cellTarget+A.D.t/8)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (by positivity)) (by positivity))
        (by positivity)
    _ = (Cd*(n+1:ℕ)*(m+1:ℕ)*C)*Z^(cellTarget+A.D.t/4) := by
      have hp : Z^(A.D.t/8)*Z^(cellTarget+A.D.t/8)=Z^(cellTarget+A.D.t/4) := by
        rw [←Real.rpow_add hZp]
        congr 1
        ring
      calc
        _ = (Cd*(n+1:ℕ)*(m+1:ℕ)*C)*(Z^(A.D.t/8)*Z^(cellTarget+A.D.t/8)) := by ring
        _ = _ := by rw [hp]
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
end
end QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect.FiniteNumerator

