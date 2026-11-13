/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The complete finite-cube error on actual chosen floor rows. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.FloorRows
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.FiniteError.Normalized
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace Qrh.TwoSlot.AnchorZeroLoss
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.Source
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.FinalAssembly
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic
open OAI OAI.SevenEighths ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open HeckeDetectorPhysicalSelection Cycle25.Numerator Cycle25.Weighted.FullWContour
open BoundaryDensitySplitReturn.TransportHighTransport
variable [Geometry.Parameters] [BoundsCore]
variable [Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]
variable [Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.PhysicalSchedule]

theorem actual_floor_cube_error (A : ChosenData) (tau : ℝ) (ht : 0<tau) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ Z : ℝ in atTop, ∀ η : Character,
    ∀ (rows : Finset FreeRow) (idx : FreeRow → ℕ),
    (∀u∈rows,u.val≠1 ∧ rowNorm u≤Z^(h+rowPadding)) →
    (∀u∈rows,detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
      (rayCubeFamily A.F.modulus ⊤ le_top u)) (3*(idx u+1:ℕ)*Z^tau)<51/100+2*A.D.e) →
    floorNormalizer A Z≠0 ∧
    ‖finiteCentralCubeRows A.F.S A.F.exclusions A.F.maximal η rows
      (sourcePrimePool A.F Z) (fun j => source_prime_pool_outside A.F Z j)
      (fun _ => A.F.W) (fun j => Z^(A.D.length j)) A.F.W A.F.W
      (Z^x) (Z^y) Z A.D.e (fun _ => 51/100) (fun u => (3*idx u+1:ℕ)*Z^tau)/
      floorNormalizer A Z -
      finiteCentralFullWRows A.F.S A.F.exclusions A.F.maximal η rows
      (sourcePrimePool A.F Z) (fun j => source_prime_pool_outside A.F Z j)
      (fun _ => A.F.W) (fun j => Z^(A.D.length j)) A.F.W A.F.W
      (Z^x) (Z^y) Z A.D.e (fun _ => 51/100) (fun u => (3*idx u+1:ℕ)*Z^tau)/
      floorNormalizer A Z‖ ≤ C*(η.modulus.absNorm:ℝ)^2*Z^(-(1:ℝ)) := by
  obtain ⟨C,hC,herror⟩ := PhysicalHighRowFamily.actual_normalized_cube_fullW_arbitrary_saving
    A.F.modulus ⊤ le_top A.D.N tau 1 1 2 1 rowPadding (A.D.t/8)
    ht (by norm_num) (by norm_num) (by norm_num) (by norm_num [rowPadding])
    (by have := A.D.t_pos; positivity) A.D.e A.D.e_pos A.D.e_small
    A.F.S A.F.exclusions A.F.maximal A.F.first A.D.length A.D.slots_pos A.D.slots_injective A.D.slots_sum
    (fun _=>A.F.w) (fun _=>A.F.smooth) (fun _=>A.F.compact) (fun _=>A.F.support)
    (fun _=>A.F.bounded) (fun _=>A.F.nonzero) A.F.W A.F.W 1 2 1 2 (by norm_num) (by norm_num)
    A.F.complex_support A.F.complex_support A.F.real A.F.real A.F.nonnegative A.F.nonnegative
    A.F.complex_nonzero A.F.complex_nonzero
  refine ⟨C,hC,?_⟩
  filter_upwards [herror,(tendsto_rpow_atTop ht).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_ge_atTop (1:ℝ)] with Z he hT hZ
  intro η rows idx hr hb
  have hbin : ∀u∈rows,(51/100:ℝ)≤51/100 ∧ (51/100:ℝ)≤1 ∧ 2<Z^tau ∧
      Z^tau≤(3*idx u+1:ℕ)*Z^tau ∧ (3*idx u+1:ℕ)*Z^tau≤(3*idx u+2:ℕ)*Z^tau ∧
      detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
        (rayCubeFamily A.F.modulus ⊤ le_top u)) (3*(idx u+1:ℕ)*Z^tau)<51/100+2*A.D.e := by
    intro u hu
    refine ⟨le_rfl,by norm_num,hT,?_,?_,hb u hu⟩
    · have hm : (1:ℝ)≤(3*idx u+1:ℕ) := by exact_mod_cast (by omega : 1≤3*idx u+1)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (by linarith) tau)
    · have hm : ((3*idx u+1:ℕ):ℝ)≤(3*idx u+2:ℕ) := by exact_mod_cast (by omega : 3*idx u+1≤3*idx u+2)
      exact mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (by linarith) tau)
  have hb := he η rows hr (fun _=>51/100) (fun _=>Z^tau)
    (fun u=>(3*idx u+1:ℕ)*Z^tau) idx hbin
  have hW : (fun (_ : Fin A.D.N) y => (A.F.w y:ℂ)) = (fun _ => ⇑A.F.W) := by
    funext j y
    exact (A.F.complex_eq y).symm
  rw [hW] at hb
  convert hb using 1 <;> rfl

/-- The complete physical cube floor sum, including its full Fourier-tail error. -/
theorem actual_averaged_floor_cube_rows (hgap : theta < HeckeZeroSupremum.beta)
    (A : ChosenData) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ tau : ℝ, HeightAdmissible A.D A.P J tau →
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
    ∀ (rows : Finset FreeRow) (idx : FreeRow → ℕ),
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet A.F.S A.F.maximal).residueMonoid u.val≠0 ∧
      rowNorm u≤Z^(h+rowPadding)) →
    (∀u∈rows,(rowCharacter A.F.S A.F.exclusions.prime u).residue≠1) →
    (∀u∈rows,idx u≤n) →
    (∀u∈rows,detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
      (rayCubeFamily A.F.modulus ⊤ le_top u)) (3*(idx u+1:ℕ)*Z^tau)<51/100+2*A.D.e) →
    floorNormalizer A Z≠0 ∧
    ‖finiteCentralCubeRows A.F.S A.F.exclusions A.F.maximal η rows
      (sourcePrimePool A.F Z) (fun j => source_prime_pool_outside A.F Z j)
      (fun _ => A.F.W) (fun j => Z^(A.D.length j)) A.F.W A.F.W
      (Z^x) (Z^y) Z A.D.e (fun _ => 51/100) (fun u => (3*idx u+1:ℕ)*Z^tau)/
      floorNormalizer A Z‖ ≤ C*(η.modulus.absNorm:ℝ)^(2+2*A.P.eps)*
        Z^(Geometry.signal theta-1/4000) := by
  obtain ⟨J,hJ,hw⟩ := actual_averaged_floor_rows hgap A
  refine ⟨J,hJ,?_⟩
  intro tau ht n
  obtain ⟨Cw,hCw,hw⟩ := hw tau ht n
  obtain ⟨Ce,hCe,he⟩ := actual_floor_cube_error A tau ht.1
  refine ⟨Cw+Ce,by positivity,?_⟩
  intro η
  filter_upwards [hw η,he,eventually_ge_atTop (1:ℝ)] with Z hw he hZ
  intro rows idx hr hnp hi hb
  obtain ⟨hN,hw⟩ := hw rows idx hr hnp hi hb
  have herr := (he η rows idx (fun u hu=>⟨(hr u hu).1,(hr u hu).2.2.2⟩) hb).2
  refine ⟨hN,?_⟩
  have hM : (1:ℝ)≤(η.modulus.absNorm:ℝ) := HeckeLogarithmicInput.modulus_norm_ge_one η
  have hMp : (0:ℝ)<(η.modulus.absNorm:ℝ) := zero_lt_one.trans_le hM
  have h1 : (η.modulus.absNorm:ℝ)^(2*A.P.eps)≤
      (η.modulus.absNorm:ℝ)^(2+2*A.P.eps) :=
    Real.rpow_le_rpow_of_exponent_le hM (by linarith)
  have h2 : (η.modulus.absNorm:ℝ)^2≤(η.modulus.absNorm:ℝ)^(2+2*A.P.eps) := by
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hM (by norm_num only [Nat.cast_ofNat]; linarith [A.P.eps_pos])
  have hE : (-1:ℝ)≤Geometry.signal theta-1/4000 := by
    change -1≤Geometry.signal Geometry.theta-1/4000
    rw [Geometry.signal_at_boundary]
    linarith [Geometry.ell_pos,Geometry.ell_lt_x,Geometry.x_lt_y]
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ hE
  have htriangle := norm_le_norm_add_norm_sub
    (finiteCentralFullWRows A.F.S A.F.exclusions A.F.maximal η rows
      (sourcePrimePool A.F Z) (fun j => source_prime_pool_outside A.F Z j)
      (fun _ => A.F.W) (fun j => Z^(A.D.length j)) A.F.W A.F.W
      (Z^x) (Z^y) Z A.D.e (fun _ => 51/100) (fun u => (3*idx u+1:ℕ)*Z^tau)/floorNormalizer A Z)
    (finiteCentralCubeRows A.F.S A.F.exclusions A.F.maximal η rows
      (sourcePrimePool A.F Z) (fun j => source_prime_pool_outside A.F Z j)
      (fun _ => A.F.W) (fun j => Z^(A.D.length j)) A.F.W A.F.W
      (Z^x) (Z^y) Z A.D.e (fun _ => 51/100) (fun u => (3*idx u+1:ℕ)*Z^tau)/floorNormalizer A Z)
  rw [norm_sub_rev] at htriangle
  apply htriangle.trans
  calc
    _ ≤ Cw*(η.modulus.absNorm:ℝ)^(2*A.P.eps)*Z^(Geometry.signal theta-1/4000)+
        Ce*(η.modulus.absNorm:ℝ)^2*Z^(-(1:ℝ)) := add_le_add hw herr
    _ ≤ Cw*(η.modulus.absNorm:ℝ)^(2+2*A.P.eps)*Z^(Geometry.signal theta-1/4000)+
        Ce*(η.modulus.absNorm:ℝ)^(2+2*A.P.eps)*Z^(Geometry.signal theta-1/4000) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hCw.le) (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left h2 hCe) hpow
          (by positivity) (by positivity)
    _ = _ := by ring

end Qrh.TwoSlot.AnchorZeroLoss
#print axioms Qrh.TwoSlot.AnchorZeroLoss.actual_floor_cube_error

#print axioms Qrh.TwoSlot.AnchorZeroLoss.actual_averaged_floor_cube_rows
