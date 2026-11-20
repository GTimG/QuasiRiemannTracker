/- Adapted at Q's genuine geometry from Joseph Bebel's PositiveFloorCells.
Apache-2.0; preceding Collet/OpenAI/Levy/Gao analytic attribution retained in imports. -/
import Candidate.C092.transport.SelectedFloorEstimateHeight
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.PhysicalFront
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace QRH.Cycle092.SelectedFloorEstimate
open Qrh.TwoSlot.AnchorZeroLoss
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Record1252270103Return
open QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.FinalAssembly
open QRH.Record1252270103Return.Geometry
open Cycle25.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open HeckeDetectorPhysicalSelection
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

def averagedFloorExponent (d : ℝ) : ℝ :=
  4*x/25-3/20-y/2-3*ell/20+33*d/50

theorem averagedFloorExponent_eq (d : ℝ) :
    averagedFloorExponent d = Geometry.signalShift + (51/100-49/150*h+51/100*ell+33*d/50) := by
  have he := Geometry.x_add_y
  unfold averagedFloorExponent Geometry.signalShift Geometry.h
  change 4*Geometry.x/25-3/20-Geometry.y/2-3*Geometry.ell/20+33*d/50 = _
  nlinarith

theorem chosen_floor_loss (D : BaselineData) (F : BaselineSourceData D) (P : TransportParameters D) {d : ℝ} (hd : d ≤ 1) :
    16*D.e+(17/25)*D.t+D.t*ell+
      d*(2*P.eps+(38/25)*D.t)+D.t+D.t/8 < 1/100000 := by
  have he := P.e_tsmall
  have hep : P.eps ≤ D.t/100 := by
    have hn : (0:ℝ) ≤ D.N := Nat.cast_nonneg _
    nlinarith [P.eps_budget,P.eps_pos]
  have ht := D.t_pos
  have hepspos := P.eps_pos
  have htmax := D.t_small
  have hel : ell < 1/5 := by linarith [ActualGeometry.WidenedCoreBounds.ell_interval.2]
  have hm := mul_le_mul_of_nonneg_right hd
    (show 0 ≤ 2*P.eps+(38/25)*D.t by positivity)
  have hte := mul_le_mul_of_nonneg_left hel.le ht.le
  nlinarith

/-- Every actual floor cell has a fixed normalized reserve, using the
trivial row count and the original detector/phase event. The source is
the chosen physical source; no arbitrary moment or old floor-margin
premise occurs. Height is chosen after the fixed scalar degree. -/
theorem actual_averaged_floor_cells (D : BaselineData) (F : BaselineSourceData D) (P : TransportParameters D)
    (padding : ℝ) (hpad : padding+2*D.t ≤ 1/10000000000)
    (hbeta : theta ≤ HeckeZeroSupremum.beta) :
    ∀ tau : ℝ, HeightAdmissible D P tau →
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
    ∀ (rows : Finset FreeRow) (d : ℝ) (i : ℕ), (1/200:ℝ) ≤ d → d ≤ h+padding+2*D.t → i ≤ n →
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧
      rowNorm u≤Z^(d-D.t)) →
    (∀u∈rows,(Z^d)^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤Z^d) →
    (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1) →
    (∀u∈rows,Z^(d-2*D.t)≤rowNorm u) →
    (∀u∈rows,detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u
      (rayCubeFamily F.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^tau)<51/100+2*D.e) →
    ProbeAssembly.normalizer D F Z≠0 ∧
    ‖Cycle25.Weighted.FullWContour.finiteCentralFullWRows F.S F.exclusions F.maximal
      η rows (sourcePrimePool F Z) (fun j => source_prime_pool_outside F Z j)
      (fun _ => F.W) (fun j => Z^(D.length j)) F.W F.W
      (Z^x) (Z^y) Z D.e (fun _ => 51/100) (fun _ => (3*i+1:ℕ)*Z^tau)/
      ProbeAssembly.normalizer D F Z‖ ≤ C*(η.modulus.absNorm:ℝ)^(2*P.eps)*
        Z^(Geometry.signal theta-1/2000) := by
  have hb : (51/100:ℝ) ≤ HeckeZeroSupremum.beta := by
    have := ActualGeometry.WidenedCoreBounds.theta_bounds.1
    linarith
  obtain ⟨Cf,hCf,hf⟩ := physical_floor_fullW F (3/4) (by norm_num)
    (by norm_num) (by linarith [SelectedActual.baseline_beta]) hb D.e_small P.eps P.eps_pos
  obtain ⟨Cn,hCn,hn⟩ := SelectedActual.actual_normalizer_inverse D F (D.t/8) (by have := D.t_pos; positivity)
  have hepspos := P.eps_pos
  intro tau hheight n
  refine ⟨Cf*Cn,by positivity,?_⟩
  intro η
  filter_upwards [eventually_uniform_source_conductor (1/200) (by norm_num) hf,
    hn,source_prime_bins D F P tau n hheight.1 (by simpa only [div_eq_mul_inv, mul_comm, one_mul] using hheight.2.1),
    source_prime_reconstruction_geometry F η,source_pools_nonempty D F,
    source_height_absorption (2*P.eps) D.t tau n (by positivity) D.t_pos
      hheight.1 hheight.2.2,
    (tendsto_rpow_atTop hheight.1).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z hf hn hprime hgeo hpools hheight hT hZ
  intro rows d i hd hdmax hi hsource hrows hrow hfreq hnext
  have hZp := zero_lt_one.trans hZ
  have hdp : 0 < d := (show (0:ℝ)<1/200 by norm_num).trans_le hd
  have hdtop : d ≤ 7/8 := by
    have hh := ActualGeometry.WidenedCoreBounds.h_interval.2
    linarith
  have hd1 : d ≤ 1 := hdtop.trans (by norm_num)
  have hypos : 0 < y/d := div_pos (by linarith [ActualGeometry.WidenedCoreBounds.ly_coarse.1]) hdp
  have hyhi : y/d ≤ 99 := (div_le_iff₀ hdp).mpr (by
    change (1/200:ℝ) ≤ d at hd
    linarith [ActualGeometry.WidenedCoreBounds.ly_coarse.2])
  have hY : (Z^d)^(y/d)=Z^y := by
    rw [←Real.rpow_mul hZp.le,mul_div_cancel₀ _ hdp.ne']
  have hprimecap (z:ℂ) (hz:z.re=17/50) (him:|z.im|≤(3*i+1:ℕ)*Z^tau)
      (u:FreeRow) (hu:u∈rows) (j:Fin D.N) :
      ‖HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2
        (Z^(D.length j)) z‖ ≤ Z^(D.length j*(1/100+D.t)) := by
    have hh := hprime d hd hdtop η u (hsource u hu).2.1
      (hsource u hu).2.2.1 (hsource u hu).2.2.2 (51/100) i hi le_rfl
      (by norm_num) (hnext u hu) z hz him j
    have hg := hh.2.1
    apply hh.2.2.2.1.trans
    rw [←Real.rpow_mul hZp.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    nlinarith [D.slots_pos j]
  have hh := (hf d hd).2 Z d hZ.le rfl η rows (fun u hu => (hsource u hu).1)
    hrows hfreq hrow hgeo.2.1 hgeo.2.2.1 hgeo.2.2.2.1 hgeo.2.2.2.2.1
    hgeo.2.2.2.2.2 (fun j => ⟨(hpools j).choose,(hpools j).choose_spec⟩)
    (rayCubeFamily F.modulus ⊤ le_top) (Z^tau) ((3*i+1:ℕ)*Z^tau) i hT
    (by positivity) (by push_cast; have hp := Real.rpow_nonneg hZp.le tau; nlinarith)
    hnext hprimecap (Z^x) (y/d) (Real.rpow_pos_of_pos hZp _) hypos hyhi
  dsimp only [QRH.Record1252270103Return.GenericPhysical.BaselineData.toMomentData] at hh
  rw [hY] at hh
  have hnorm : ‖(ProbeAssembly.normalizer D F Z)⁻¹‖ ≤ Cn*Z^(D.t/8) := hn.2
  refine ⟨hn.1,?_⟩
  rw [div_eq_mul_inv,norm_mul]
  apply (mul_le_mul hh hnorm (norm_nonneg _) (by positivity)).trans
  let L : ℝ := 16*D.e+(17/25)*D.t+D.t*ell+
    d*(2*P.eps+(38/25)*D.t)
  have hcollapse :
      Cf*(Z^x)^(4/25:ℝ)*Z^(-3/20+16*D.e)*(η.modulus.absNorm:ℝ)^(2*P.eps)*
      (3+((3*i+1:ℕ):ℝ)*Z^tau)^(2*P.eps)*(Z^y)^(-(1/2:ℝ))*
      Z^((17/25)*D.t+(-3/20+D.t)*∑j,D.length j)*
      (Z^d)^(33/50+2*P.eps+(38/25)*D.t) =
      Cf*(η.modulus.absNorm:ℝ)^(2*P.eps)*
      (3+((3*i+1:ℕ):ℝ)*Z^tau)^(2*P.eps)*Z^(averagedFloorExponent d+L) := by
    rw [D.slots_sum]
    simp_rw [←Real.rpow_mul hZp.le]
    have he : averagedFloorExponent d+L = x*(4/25)+(-3/20+16*D.e)+y*(-(1/2))+
        ((17/25)*D.t+(-3/20+D.t)*ell)+d*(33/50+2*P.eps+(38/25)*D.t) := by
      dsimp [averagedFloorExponent,L]; ring
    rw [he]
    simp_rw [Real.rpow_add hZp]
    ring
  erw [hcollapse]
  have hm := ActualGeometry.widened_floor_margin (D:=d) (by linarith only [hdmax,hpad])
  have hl := chosen_floor_loss D F P hd1
  have hexp : averagedFloorExponent d+L+D.t+D.t/8 ≤
      Geometry.signal theta-1/2000 := by
    rw [averagedFloorExponent_eq]
    change _ ≤ theta+Geometry.signalShift-1/2000
    dsimp only [L] at *
    linarith
  calc
    _ ≤ (Cf*(η.modulus.absNorm:ℝ)^(2*P.eps)*Z^D.t*
        Z^(averagedFloorExponent d+L))*(Cn*Z^(D.t/8)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hheight i hi) (by positivity)) (by positivity)
    _ = (Cf*Cn)*(η.modulus.absNorm:ℝ)^(2*P.eps)*
        Z^(averagedFloorExponent d+L+D.t+D.t/8) := by
      simp_rw [Real.rpow_add hZp]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le hexp) (by positivity)

end QRH.Cycle092.SelectedFloorEstimate
#print axioms QRH.Cycle092.SelectedFloorEstimate.actual_averaged_floor_cells
