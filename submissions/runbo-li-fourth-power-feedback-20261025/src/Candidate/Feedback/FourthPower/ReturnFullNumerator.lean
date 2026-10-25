/- Copyright (c) 2026 Sil, Hailey Collet, Gao and OpenAI. Apache-2.0.
Actual two-dimensional Mellin integration and source-normalizer division for
our all-band packet. Adapted PR69 SourceFullW, with actual count/source inputs
already discharged by ReturnPacketSummation.actual_raw_source. The one height is
chosen after the physical degree and eta; no desired moment bound is a premise.
Only our true Geometry.Parameters / CountScheme are instantiated.

-/
import Candidate.Feedback.FourthPower.ReturnPacketSummation
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.NormalizerHelpers
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.FullWBound
import Candidate.Feedback.FourthPower.ReturnCarrierInterfaces
import Candidate.Feedback.FourthPower.OlderIncumbentContract

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.ReturnFullNumerator
noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter Set OAI OAI.SevenEighths
open HeckeFamily ProbeHighRowFamily ProbePhysical HeckeInverseAmplification
open Cycle25.Weighted Cycle25.Weighted.Numerator Cycle25.Numerator
open Cycle25ProbeFinalAssembly Cycle25DetectorRowCount
open QRH.Record12518109Count QRH.Record12518109Existence
open QRH.Record1252270103Return
open QRH.Record1252270103Return.GenericPhysical
open QRH.Record1252270103Return.GenericPhysical.Scalar
open QRH.Record1252270103Return.GenericPhysical.PhysicalDirect
open ReturnCertificate ReturnWindows ReturnSourceFaces ReturnOldCount
open ReturnSourceInputs ReturnMaskedCount ReturnPacketSummation
open QRH.Record1252270103Return.GenericPhysical.Assembly (TransportParameters)

local instance : Geometry.Parameters := ReturnSourceInputs.parameters
local instance : CountScheme := ReturnWindows.countScheme

theorem source_height_absorption (J t τ : ℝ) (n : ℕ)
    (hJ : 0 ≤ J) (_ht : 0 < t) (hτ : 0 < τ) (hbudget : 2*τ*(1+J) ≤ t) :
    ∀ᶠZ : ℝ in atTop,∀i : ℕ,i ≤ n →
      (3+((3*i+1:ℕ):ℝ)*Z^τ)^J ≤ Z^t := by
  filter_upwards [HeckeDyadic.constant_absorbed_eventually (3*(n:ℝ)+4) τ hτ,
    eventually_ge_atTop (1:ℝ)] with Z hn hZ
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hp : 1 ≤ Z^τ := Real.one_le_rpow hZ hτ.le
  intro i hi
  have hhi : (i:ℝ) ≤ n := by exact_mod_cast hi
  have hheight : 3+((3*i+1:ℕ):ℝ)*Z^τ ≤ Z^(2*τ) := by
    calc
      _ ≤ (3*(n:ℝ)+4)*Z^τ := by push_cast;nlinarith
      _ ≤ Z^τ*Z^τ := mul_le_mul_of_nonneg_right hn (by positivity)
      _ = _ := by rw [←Real.rpow_add hZpos];congr 1;ring
  calc
    _ ≤ (Z^(2*τ))^J := Real.rpow_le_rpow (by positivity) hheight hJ
    _ = Z^(2*τ*J) := (Real.rpow_mul hZpos.le _ _).symm
    _ ≤ Z^t := Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith only [hbudget,hτ])

/-- Absorb the single fixed height degree after every amplitude class has
already been placed below the common numerical target. -/
theorem source_absorb_height (V : ℂ) (Z C H J E t : ℝ)
    (hZ : 0 < Z) (hC : 0 ≤ C) (hheight : (3+H)^J ≤ Z^t)
    (hV : ‖V‖ ≤ C*(3+H)^J*Z^(E-t)) :
    ‖V‖ ≤ C*Z^E := by
  calc
    _ ≤ C*(3+H)^J*Z^(E-t) := hV
    _ ≤ C*Z^t*Z^(E-t) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hheight hC) (Real.rpow_nonneg hZ.le _)
    _ = _ := by rw [mul_assoc,←Real.rpow_add hZ];congr 2;ring

def FullWCellBound {extraMesh : ℝ} (A : GapData extraMesh)
    (P : TransportParameters A.D) (η : Character) (Z τ : ℝ) (n : ℕ)
    (C : ℝ) : Prop :=
  ∀(rows : Finset FreeRow) (d a : ℝ) (i : ℕ),d0≤ d → d≤ dplus →
  51/100< a → a≤7/8 → i≤ n →
  (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
    (calibrationForSet A.F.S A.F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-A.D.t)) →
  (∀u∈rows,(Z^d)^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ Z^d) →
  (∀u∈rows,(rowCharacter A.F.S A.F.exclusions.prime u).residue≠1) →
  (∀u∈rows,Z^(d-2*A.D.t)≤ rowNorm u) →
  (∀u∈rows,detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
    (rayCubeFamily A.F.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^τ)< a+2*A.D.e) →
  (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
    (rayCubeFamily A.F.modulus ⊤ le_top u)) ((3*i:ℕ)*Z^τ)) →
  ‖Cycle25.Weighted.FullWContour.finiteCentralFullWRows A.F.S A.F.exclusions A.F.maximal η rows
    (sourcePrimePool A.F Z) (fun j=>source_prime_pool_outside A.F Z j)
    (fun _ y=>(A.F.w y:ℂ)) (fun j=>Z^(A.D.length j)) A.F.W A.F.W (Z^x) (Z^y) Z A.D.e
    (fun _=>a) (fun _=>(3*i+1:ℕ)*Z^τ)/
      ReturnCarrierInterfaces.normalizer A.D A.F Z‖≤
    C*(η.modulus.absNorm:ℝ)^(2*P.eps)*Z^(sourceTarget+A.D.t/8)

/-- The actual normalized FullW cell on the whole d0..dplus interval.
The raw moment, counting and physical estimates are supplied by the exact
full-source input through actual_raw_source, not requested again here.
This is a cell estimate, not yet the full dyadic-conductor or common-probe sum. -/
theorem actual_fullW_cells (hPrior : OlderIncumbentContract.OlderIncumbentInput) {extraMesh : ℝ} (A : GapData extraMesh)
    (P : TransportParameters A.D)
    (hsource : UniformUnitFaceSource fullSourceFace)
    (hgap : theta<HeckeZeroSupremum.beta)
    (heightLoss : ℝ) (hheightLoss : 0<heightLoss) (hloss : heightLoss≤A.D.t) :
    ∃J : ℝ,0≤J ∧ ∀η : Character,∃tau : ℝ,CountHeight A.D J heightLoss tau ∧
      ∀n : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
        1<Z ∧ FullWCellBound A P η Z tau n C := by
  obtain ⟨J,hJ,hraw⟩ := actual_raw_source hPrior A P hsource hgap heightLoss hheightLoss
  obtain ⟨Ci,hCi,hi⟩ := Cycle25.Weighted.FullWContour.finiteFullW_uniform_norm_bound A.F.W 1 2
    (by norm_num) A.F.complex_support
  obtain ⟨Cn,hCn,hn⟩ :=
    Candidate.Feedback.FourthPower.ReturnCarrierInterfaces.source_normalizer_bound A.D A.F
  refine ⟨J,hJ,?_⟩
  intro η
  obtain ⟨tau,htau,hcells⟩ := hraw η
  refine ⟨tau,htau,?_⟩
  intro n
  obtain ⟨Cw,hCw,hw⟩ := hcells n
  refine ⟨Ci*Cn*Cw,by positivity,?_⟩
  filter_upwards [hw,hn,source_height_absorption J A.D.t tau n hJ A.D.t_pos
      htau.pos (htau.physical_height.trans hloss),
    (tendsto_rpow_atTop htau.pos).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z hw hn hheight hT hZ
  refine ⟨hZ,?_⟩
  have hraw := hw.2
  unfold FullWCellBound
  intro rows d a i hd hdmax ha hatop hiidx hsourceRows hrows hrow hfreq hnext hcurrent
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  let B : ℝ := Cw*(η.modulus.absNorm:ℝ)^(2*P.eps)*
    Z^(sourceTarget-kernelExponent a A.D.e)
  have hB : 0≤B := by dsimp only [B]; positivity
  have hintegrated : ∀q∈Cycle25.Weighted.FullWContour.szRectangle ((3*i+1:ℕ)*Z^tau),
      ‖Cycle25.Weighted.FullWContour.integratedDyadValue A.F.S A.F.exclusions A.F.maximal η rows
        (sourcePrimePool A.F Z) (fun j=>source_prime_pool_outside A.F Z j)
        (fun _ y=>(A.F.w y:ℂ)) (fun j=>Z^(A.D.length j)) A.F.W (Z^y)
        ((((a+16*A.D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)‖≤B := by
    intro q hq
    have hh := hraw rows d a i hd hdmax ha hatop hiidx hsourceRows hrows hrow hfreq hnext hcurrent q hq
    rw [Cycle25.Numerator.source_real_profile_eq A.F]
    exact source_absorb_height _ Z (Cw*(η.modulus.absNorm:ℝ)^(2*P.eps))
      (((3*i+1:ℕ):ℝ)*Z^tau) J (sourceTarget-kernelExponent a A.D.e) A.D.t hZ0
      (by positivity) (hheight i hiidx) (by simpa only [sub_sub,add_comm] using hh)
  have hh := hi A.D.e a (Z^tau) (((3*i+1:ℕ):ℝ)*Z^tau) i A.D.e_pos A.D.e_small ha.le
    (by linarith) hT (by push_cast;have hp:=Real.rpow_nonneg hZ0.le tau;nlinarith)
    A.F.S A.F.exclusions A.F.maximal A.F.first η rows (fun u hu=>(hsourceRows u hu).1)
    (sourcePrimePool A.F Z) (fun j=>source_prime_pool_outside A.F Z j)
    (rayCubeFamily A.F.modulus ⊤ le_top) hnext (fun _ y=>(A.F.w y:ℂ))
    (fun j=>Z^(A.D.length j)) A.F.W 1 2 (by norm_num) A.F.complex_support
    (Z^x) (Z^y) Z B (by positivity) (by positivity) hZ0 hB hintegrated
  rw [div_eq_mul_inv,norm_mul]
  apply (mul_le_mul hh hn.2 (norm_nonneg _) (by positivity)).trans_eq
  dsimp only [B]
  rw [←Real.rpow_mul hZ0.le]
  have hp : Z^(x*(1/2-17/50))*Z^(a+16*A.D.e+17/50-1)*
      Z^(sourceTarget-kernelExponent a A.D.e)*Z^(A.D.t/8)=Z^(sourceTarget+A.D.t/8) := by
    rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0,←Real.rpow_add hZ0]
    congr 1
    unfold kernelExponent
    rw [show GenericArithmetic.x = x from rfl]
    ring
  calc
    _ = (Ci*Cn*Cw)*(η.modulus.absNorm:ℝ)^(2*P.eps)*
        (Z^(x*(1/2-17/50))*Z^(a+16*A.D.e+17/50-1)*
          Z^(sourceTarget-kernelExponent a A.D.e)*Z^(A.D.t/8)) := by ring
    _ = _ := by rw [hp]

/-- The final transport consumes a slightly stronger height allowance than
FullW alone. It is chosen before eta and n and does not change any Z exponent. -/
def transportHeightLoss {D : QRH.Record1252270103Return.GenericPhysical.BaselineData} (P : TransportParameters D) : ℝ :=
  D.t/(2+4*P.eps)

theorem transport_height_loss_bounds {D : QRH.Record1252270103Return.GenericPhysical.BaselineData} (P : TransportParameters D) :
    0<transportHeightLoss P ∧ transportHeightLoss P≤D.t := by
  have he := P.eps_pos
  have hq : 0<2+4*P.eps := by positivity
  refine ⟨div_pos D.t_pos hq,?_⟩
  change D.t/(2+4*P.eps)≤D.t
  apply (div_le_iff₀ hq).mpr
  nlinarith [D.t_pos,mul_nonneg D.t_pos.le he.le]

/-- Honest strict phase-transport gate, derived from the stronger scalar
height selection. It is not an additional analytical input. -/
theorem count_height_transport_gate {D : QRH.Record1252270103Return.GenericPhysical.BaselineData} (P : TransportParameters D)
    {J tau : ℝ} (hJ : 0≤J) (htau : CountHeight D J (transportHeightLoss P) tau) :
    tau*(2+4*P.eps)<D.t := by
  have hq : 0<2+4*P.eps := by have := P.eps_pos; positivity
  have hsmall : 2*tau≤D.t/(2+4*P.eps) := by
    have hh := htau.physical_height
    change 2*tau*(1+J)≤D.t/(2+4*P.eps) at hh
    nlinarith [htau.pos,mul_nonneg htau.pos.le hJ]
  have hm := (le_div_iff₀ hq).mp hsmall
  nlinarith [D.t_pos]

end
end Candidate.Feedback.FourthPower.ReturnFullNumerator
