/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Normalized averaged-floor cells for the actual chosen physical source. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.BoundsCore
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.FloorFullW
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.SourceFullW
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace Qrh.TwoSlot.AnchorZeroLoss
open QRH.Record1252270103Return
open QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.Source
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.FinalAssembly
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic
open Cycle25.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open HeckeDetectorPhysicalSelection
variable [Geometry.Parameters] [BoundsCore]
variable [scheme : Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]
variable [Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.PhysicalSchedule]

def averagedFloorExponent (d : ℝ) : ℝ :=
  4*x/25-3/20-y/2-3*ell/20+33*d/50

theorem averagedFloorExponent_eq (d : ℝ) :
    averagedFloorExponent d = Geometry.signalShift + floorPrice d := by
  have he := Geometry.x_add_y
  unfold averagedFloorExponent floorPrice Geometry.signalShift Geometry.h
  change 4*Geometry.x/25-3/20-Geometry.y/2-3*Geometry.ell/20+33*d/50 = _
  nlinarith

def floorNormalizer (A : ChosenData) (Z : ℝ) : ℂ :=
  BoundaryDensitySplitReturn.TransportHighTransport.actualNormalizer A.F.modulus ⊤
    A.F.S A.D.length 1 2 (fun _ => A.F.w) A.F.W A.F.W Z

theorem chosen_floor_loss (A : ChosenData) {d : ℝ} (hd : d ≤ 1) :
    16*A.D.e+(17/25)*A.D.t+A.D.t*ell+
      d*(2*A.P.eps+(38/25)*A.D.t)+A.D.t+A.D.t/8 < 1/100000 := by
  have he := A.P.e_tsmall
  have hep : A.P.eps ≤ A.D.t/100 := by
    have hn : (0:ℝ) ≤ A.D.N := Nat.cast_nonneg _
    nlinarith [A.P.eps_budget,A.P.eps_pos]
  have ht := A.D.t_pos
  have hepspos := A.P.eps_pos
  have htmax := A.D.t_small
  have hel : ell < 1/5 := Geometry.ell_lt_fifth
  have hm := mul_le_mul_of_nonneg_right hd
    (show 0 ≤ 2*A.P.eps+(38/25)*A.D.t by positivity)
  have hte := mul_le_mul_of_nonneg_left hel.le ht.le
  nlinarith

/-- Every actual floor cell has a fixed normalized reserve, using the
trivial row count and the original detector/phase event. The source is
the chosen physical source; no arbitrary moment or old floor-margin
premise occurs. Height is chosen after the fixed scalar degree. -/
theorem actual_averaged_floor_cells (hgap : theta < HeckeZeroSupremum.beta)
    (A : ChosenData) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ tau : ℝ, HeightAdmissible A.D A.P J tau →
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
    ∀ (rows : Finset FreeRow) (d : ℝ) (i : ℕ), d0 ≤ d → d ≤ dp → i ≤ n →
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet A.F.S A.F.maximal).residueMonoid u.val≠0 ∧
      rowNorm u≤Z^(d-A.D.t)) →
    (∀u∈rows,(Z^d)^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤Z^d) →
    (∀u∈rows,(rowCharacter A.F.S A.F.exclusions.prime u).residue≠1) →
    (∀u∈rows,Z^(d-2*A.D.t)≤rowNorm u) →
    (∀u∈rows,detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
      (rayCubeFamily A.F.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^tau)<51/100+2*A.D.e) →
    floorNormalizer A Z≠0 ∧
    ‖Cycle25.Weighted.FullWContour.finiteCentralFullWRows A.F.S A.F.exclusions A.F.maximal
      η rows (sourcePrimePool A.F Z) (fun j => source_prime_pool_outside A.F Z j)
      (fun _ => A.F.W) (fun j => Z^(A.D.length j)) A.F.W A.F.W
      (Z^x) (Z^y) Z A.D.e (fun _ => 51/100) (fun _ => (3*i+1:ℕ)*Z^tau)/
      floorNormalizer A Z‖ ≤ C*(η.modulus.absNorm:ℝ)^(2*A.P.eps)*
        Z^(Geometry.signal theta-1/2000) := by
  have hb : (51/100:ℝ) ≤ HeckeZeroSupremum.beta := by
    have := BoundsCore.theta_bounds.1
    linarith
  obtain ⟨Cf,hCf,hf⟩ := physical_floor_fullW A.F A.D.momentKappa A.D.momentKappa_lo
    A.D.momentKappa_hi (by rw [A.kappa_exact]) hb A.D.e_small A.P.eps A.P.eps_pos
  obtain ⟨Cn,hCn,hn⟩ := source_normalizer_bound A.D A.F
  have hepspos := A.P.eps_pos
  refine ⟨2*A.P.eps,by positivity,?_⟩
  intro tau hheight n
  refine ⟨Cf*Cn,by positivity,?_⟩
  intro η
  filter_upwards [eventually_uniform_source_conductor d0 (by norm_num [d0]) hf,
    hn,source_prime_bins A.D A.F A.P tau n hheight.1 hheight.2.2.1,
    source_prime_reconstruction_geometry A.F η,source_pools_nonempty A.D A.F,
    source_height_absorption (2*A.P.eps) A.D.t tau n (by positivity) A.D.t_pos
      hheight.1 hheight.2.2.2.2.2,
    (tendsto_rpow_atTop hheight.1).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z hf hn hprime hgeo hpools hheight hT hZ
  intro rows d i hd hdmax hi hsource hrows hrow hfreq hnext
  have hZp := zero_lt_one.trans hZ
  have hdp : 0 < d := (show (0:ℝ)<d0 by norm_num [d0]).trans_le hd
  have hd1 : d ≤ 1 := hdmax.trans (by
    change Geometry.h+_ ≤ 1
    linarith [BoundsCore.h_interval.2])
  have hdtop : d ≤ 7/8 := hdmax.trans (by
    change Geometry.h+_ ≤ 7/8
    linarith [BoundsCore.h_interval.2])
  have hypos : 0 < y/d := div_pos (by linarith [BoundsCore.ly_coarse.1]) hdp
  have hyhi : y/d ≤ 99 := (div_le_iff₀ hdp).mpr (by
    change (1/200:ℝ) ≤ d at hd
    linarith [BoundsCore.ly_coarse.2])
  have hY : (Z^d)^(y/d)=Z^y := by
    rw [←Real.rpow_mul hZp.le,mul_div_cancel₀ _ hdp.ne']
  have hprimecap (z:ℂ) (hz:z.re=17/50) (him:|z.im|≤(3*i+1:ℕ)*Z^tau)
      (u:FreeRow) (hu:u∈rows) (j:Fin A.D.N) :
      ‖HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ u.val A.F.W 2
        (Z^(A.D.length j)) z‖ ≤ Z^(A.D.length j*(1/100+A.D.t)) := by
    have hh := hprime d hd hdtop η u (hsource u hu).2.1
      (hsource u hu).2.2.1 (hsource u hu).2.2.2 (51/100) i hi le_rfl
      (by norm_num) (hnext u hu) z hz him j
    have hg := hh.2.1
    apply hh.2.2.2.1.trans
    rw [←Real.rpow_mul hZp.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    nlinarith [A.D.slots_pos j]
  have hh := (hf d hd).2 Z d hZ.le rfl η rows (fun u hu => (hsource u hu).1)
    hrows hfreq hrow hgeo.2.1 hgeo.2.2.1 hgeo.2.2.2.1 hgeo.2.2.2.2.1
    hgeo.2.2.2.2.2 (fun j => ⟨(hpools j).choose,(hpools j).choose_spec⟩)
    (rayCubeFamily A.F.modulus ⊤ le_top) (Z^tau) ((3*i+1:ℕ)*Z^tau) i hT
    (by positivity) (by push_cast; have hp := Real.rpow_nonneg hZp.le tau; nlinarith)
    hnext hprimecap (Z^x) (y/d) (Real.rpow_pos_of_pos hZp _) hypos hyhi
  dsimp only [QRH.Record1252270103Return.GenericPhysical.BaselineData.toMomentData] at hh
  rw [hY] at hh
  have hnorm : ‖(floorNormalizer A Z)⁻¹‖ ≤ Cn*Z^(A.D.t/8) := hn.2
  refine ⟨hn.1,?_⟩
  rw [div_eq_mul_inv,norm_mul]
  apply (mul_le_mul hh hnorm (norm_nonneg _) (by positivity)).trans
  let L : ℝ := 16*A.D.e+(17/25)*A.D.t+A.D.t*ell+
    d*(2*A.P.eps+(38/25)*A.D.t)
  have hcollapse :
      Cf*(Z^x)^(4/25:ℝ)*Z^(-3/20+16*A.D.e)*(η.modulus.absNorm:ℝ)^(2*A.P.eps)*
      (3+((3*i+1:ℕ):ℝ)*Z^tau)^(2*A.P.eps)*(Z^y)^(-(1/2:ℝ))*
      Z^((17/25)*A.D.t+(-3/20+A.D.t)*∑j,A.D.length j)*
      (Z^d)^(33/50+2*A.P.eps+(38/25)*A.D.t) =
      Cf*(η.modulus.absNorm:ℝ)^(2*A.P.eps)*
      (3+((3*i+1:ℕ):ℝ)*Z^tau)^(2*A.P.eps)*Z^(averagedFloorExponent d+L) := by
    rw [A.D.slots_sum]
    simp_rw [←Real.rpow_mul hZp.le]
    have he : averagedFloorExponent d+L = x*(4/25)+(-3/20+16*A.D.e)+y*(-(1/2))+
        ((17/25)*A.D.t+(-3/20+A.D.t)*ell)+d*(33/50+2*A.P.eps+(38/25)*A.D.t) := by
      dsimp [averagedFloorExponent,L]; ring
    rw [he]
    simp_rw [Real.rpow_add hZp]
    ring
  erw [hcollapse]
  have hm := floor_margin_coarse (d:=d) (hdmax.trans (by
    change Geometry.h+_ ≤ Geometry.h+1/10000000000
    norm_num))
  have hl := chosen_floor_loss A hd1
  have hexp : averagedFloorExponent d+L+A.D.t+A.D.t/8 ≤
      Geometry.signal theta-1/2000 := by
    rw [averagedFloorExponent_eq]
    change _ ≤ theta+Geometry.signalShift-1/2000
    dsimp only [L] at *
    linarith
  calc
    _ ≤ (Cf*(η.modulus.absNorm:ℝ)^(2*A.P.eps)*Z^A.D.t*
        Z^(averagedFloorExponent d+L))*(Cn*Z^(A.D.t/8)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hheight i hi) (by positivity)) (by positivity)
    _ = (Cf*Cn)*(η.modulus.absNorm:ℝ)^(2*A.P.eps)*
        Z^(averagedFloorExponent d+L+A.D.t+A.D.t/8) := by
      simp_rw [Real.rpow_add hZp]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le hexp) (by positivity)

end Qrh.TwoSlot.AnchorZeroLoss
#print axioms Qrh.TwoSlot.AnchorZeroLoss.actual_averaged_floor_cells
