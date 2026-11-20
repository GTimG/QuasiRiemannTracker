/- Literal finite-cube floor, adapted to Q from Bebel's PositiveFloorError.
Apache-2.0; all physical masks, complete prime pools, and tails are retained. -/
import Candidate.C092.transport.SelectedFloorEstimateRows
import Candidate.C092.transport.SelectedFloorEstimateError2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace QRH.Cycle092.SelectedFloorEstimate
open Qrh.TwoSlot.AnchorZeroLoss
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.SelectedActualKernel.Return.GenericPhysical.PhysicalDirect
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.FinalAssembly
open QRH.Record1252270103Return.Geometry
open OAI OAI.SevenEighths ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open HeckeDetectorPhysicalSelection Cycle25.Numerator Cycle25.Weighted.FullWContour
open BoundaryDensitySplitReturn.TransportHighTransport
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

theorem actual_floor_cube_error (D : BaselineData) (F : BaselineSourceData D) (P : TransportParameters D) (padding : ℝ)
    (hpadding : padding ≤ QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Transport.rowExtension)
    (tau : ℝ) (ht : 0<tau) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ Z : ℝ in atTop, ∀ η : Character,
    ∀ (rows : Finset FreeRow) (idx : FreeRow → ℕ),
    (∀u∈rows,u.val≠1 ∧ rowNorm u≤Z^(h+padding)) →
    (∀u∈rows,detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u
      (rayCubeFamily F.modulus ⊤ le_top u)) (3*(idx u+1:ℕ)*Z^tau)<51/100+2*D.e) →
    ProbeAssembly.normalizer D F Z≠0 ∧
    ‖finiteCentralCubeRows F.S F.exclusions F.maximal η rows
      (sourcePrimePool F Z) (fun j => source_prime_pool_outside F Z j)
      (fun _ => F.W) (fun j => Z^(D.length j)) F.W F.W
      (Z^x) (Z^y) Z D.e (fun _ => 51/100) (fun u => (3*idx u+1:ℕ)*Z^tau)/
      ProbeAssembly.normalizer D F Z -
      finiteCentralFullWRows F.S F.exclusions F.maximal η rows
      (sourcePrimePool F Z) (fun j => source_prime_pool_outside F Z j)
      (fun _ => F.W) (fun j => Z^(D.length j)) F.W F.W
      (Z^x) (Z^y) Z D.e (fun _ => 51/100) (fun u => (3*idx u+1:ℕ)*Z^tau)/
      ProbeAssembly.normalizer D F Z‖ ≤ C*(η.modulus.absNorm:ℝ)^2*Z^(-(1:ℝ)) := by
  obtain ⟨C,hC,herror⟩ := PhysicalHighRowFamily.actual_normalized_cube_fullW_arbitrary_saving
    F.modulus ⊤ le_top D.N tau 1 1 2 1 padding (D.t/8)
    ht (by norm_num) (by norm_num) (by norm_num) hpadding
    (by have := D.t_pos; positivity) D.e D.e_pos D.e_small
    F.S F.exclusions F.maximal F.first D.length D.slots_pos D.slots_injective D.slots_sum
    (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _=>F.bounded) (fun _=>F.nonzero) F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero
  refine ⟨C,hC,?_⟩
  filter_upwards [herror,(tendsto_rpow_atTop ht).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_ge_atTop (1:ℝ)] with Z he hT hZ
  intro η rows idx hr hb
  have hbin : ∀u∈rows,(51/100:ℝ)≤51/100 ∧ (51/100:ℝ)≤1 ∧ 2<Z^tau ∧
      Z^tau≤(3*idx u+1:ℕ)*Z^tau ∧ (3*idx u+1:ℕ)*Z^tau≤(3*idx u+2:ℕ)*Z^tau ∧
      detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u
        (rayCubeFamily F.modulus ⊤ le_top u)) (3*(idx u+1:ℕ)*Z^tau)<51/100+2*D.e := by
    intro u hu
    refine ⟨le_rfl,by norm_num,hT,?_,?_,hb u hu⟩
    · have hm : (1:ℝ)≤(3*idx u+1:ℕ) := by exact_mod_cast (by omega : 1≤3*idx u+1)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (by linarith) tau)
    · have hm : ((3*idx u+1:ℕ):ℝ)≤(3*idx u+2:ℕ) := by exact_mod_cast (by omega : 3*idx u+1≤3*idx u+2)
      exact mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (by linarith) tau)
  have hb := he η rows hr (fun _=>51/100) (fun _=>Z^tau)
    (fun u=>(3*idx u+1:ℕ)*Z^tau) idx hbin
  have hW : (fun (_ : Fin D.N) y => (F.w y:ℂ)) = (fun _ => ⇑F.W) := by
    funext j y
    exact (F.complex_eq y).symm
  rw [hW] at hb
  convert hb using 1 <;> rfl

/-- The complete physical cube floor sum, including its full Fourier-tail error. -/
theorem actual_averaged_floor_cube_rows
    (D : BaselineData) (F : BaselineSourceData D) (P : TransportParameters D)
    (padding : ℝ) (hpadding : 0 < padding)
    (hpad : padding+2*D.t ≤ 1/10000000000)
    (hpadSmall : padding ≤ QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Transport.rowExtension)
    (hbeta : theta ≤ HeckeZeroSupremum.beta) :
    ∀ tau : ℝ, HeightAdmissible D P tau →
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
    ∀ (rows : Finset FreeRow) (idx : FreeRow → ℕ),
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧
      rowNorm u≤Z^(h+padding)) →
    (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1) →
    (∀u∈rows,idx u≤n) →
    (∀u∈rows,detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u
      (rayCubeFamily F.modulus ⊤ le_top u)) (3*(idx u+1:ℕ)*Z^tau)<51/100+2*D.e) →
    ProbeAssembly.normalizer D F Z≠0 ∧
    ‖finiteCentralCubeRows F.S F.exclusions F.maximal η rows
      (sourcePrimePool F Z) (fun j => source_prime_pool_outside F Z j)
      (fun _ => F.W) (fun j => Z^(D.length j)) F.W F.W
      (Z^x) (Z^y) Z D.e (fun _ => 51/100) (fun u => (3*idx u+1:ℕ)*Z^tau)/
      ProbeAssembly.normalizer D F Z‖ ≤ C*(η.modulus.absNorm:ℝ)^(2+2*P.eps)*
        Z^(Geometry.signal theta-1/4000) := by
  have hw := actual_averaged_floor_rows D F P padding hpadding hpad hbeta
  intro tau ht n
  obtain ⟨Cw,hCw,hw⟩ := hw tau ht n
  obtain ⟨Ce,hCe,he⟩ := actual_floor_cube_error D F P padding hpadSmall tau ht.1
  refine ⟨Cw+Ce,by positivity,?_⟩
  intro η
  filter_upwards [hw η,he,eventually_ge_atTop (1:ℝ)] with Z hw he hZ
  intro rows idx hr hnp hi hb
  obtain ⟨hN,hw⟩ := hw rows idx hr hnp hi hb
  have herr := (he η rows idx (fun u hu=>⟨(hr u hu).1,(hr u hu).2.2.2⟩) hb).2
  refine ⟨hN,?_⟩
  have hM : (1:ℝ)≤(η.modulus.absNorm:ℝ) := HeckeLogarithmicInput.modulus_norm_ge_one η
  have hMp : (0:ℝ)<(η.modulus.absNorm:ℝ) := zero_lt_one.trans_le hM
  have h1 : (η.modulus.absNorm:ℝ)^(2*P.eps)≤
      (η.modulus.absNorm:ℝ)^(2+2*P.eps) :=
    Real.rpow_le_rpow_of_exponent_le hM (by linarith)
  have h2 : (η.modulus.absNorm:ℝ)^2≤(η.modulus.absNorm:ℝ)^(2+2*P.eps) := by
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hM (by norm_num only [Nat.cast_ofNat]; linarith [P.eps_pos])
  have hE : (-1:ℝ)≤Geometry.signal theta-1/4000 := by
    change -1≤Geometry.signal Geometry.theta-1/4000
    rw [Geometry.signal_at_boundary]
    linarith [Geometry.ell_pos,Geometry.ell_lt_x,Geometry.x_lt_y]
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ hE
  have htriangle := norm_le_norm_add_norm_sub
    (finiteCentralFullWRows F.S F.exclusions F.maximal η rows
      (sourcePrimePool F Z) (fun j => source_prime_pool_outside F Z j)
      (fun _ => F.W) (fun j => Z^(D.length j)) F.W F.W
      (Z^x) (Z^y) Z D.e (fun _ => 51/100) (fun u => (3*idx u+1:ℕ)*Z^tau)/ProbeAssembly.normalizer D F Z)
    (finiteCentralCubeRows F.S F.exclusions F.maximal η rows
      (sourcePrimePool F Z) (fun j => source_prime_pool_outside F Z j)
      (fun _ => F.W) (fun j => Z^(D.length j)) F.W F.W
      (Z^x) (Z^y) Z D.e (fun _ => 51/100) (fun u => (3*idx u+1:ℕ)*Z^tau)/ProbeAssembly.normalizer D F Z)
  rw [norm_sub_rev] at htriangle
  apply htriangle.trans
  calc
    _ ≤ Cw*(η.modulus.absNorm:ℝ)^(2*P.eps)*Z^(Geometry.signal theta-1/4000)+
        Ce*(η.modulus.absNorm:ℝ)^2*Z^(-(1:ℝ)) := add_le_add hw herr
    _ ≤ Cw*(η.modulus.absNorm:ℝ)^(2+2*P.eps)*Z^(Geometry.signal theta-1/4000)+
        Ce*(η.modulus.absNorm:ℝ)^(2+2*P.eps)*Z^(Geometry.signal theta-1/4000) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hCw.le) (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left h2 hCe) hpow
          (by positivity) (by positivity)
    _ = _ := by ring

end QRH.Cycle092.SelectedFloorEstimate
#print axioms QRH.Cycle092.SelectedFloorEstimate.actual_floor_cube_error

#print axioms QRH.Cycle092.SelectedFloorEstimate.actual_averaged_floor_cube_rows
