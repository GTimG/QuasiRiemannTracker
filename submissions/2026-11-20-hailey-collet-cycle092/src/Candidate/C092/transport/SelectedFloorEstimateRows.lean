/- Q geometry adaptation of Joseph Bebel's actual averaged-floor partition.
Apache-2.0; original source and analytic attribution are retained in imports. -/
import Candidate.C092.transport.SelectedFloorEstimateCells
import Candidate.C092.transport.SelectedFloorEstimatePartition
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace QRH.Cycle092.SelectedFloorEstimate
open Qrh.TwoSlot.AnchorZeroLoss
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open QRH.Cycle092.SelectedFloorEstimate.Partition
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.FinalAssembly
open QRH.Record1252270103Return.Geometry
open OAI OAI.SevenEighths ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open HeckeDetectorPhysicalSelection Cycle25.Numerator Cycle25.Weighted.FullWContour
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- Full floor row sum at the actual chosen source, with varying height labels.
All natural row and detector restrictions remain; no legacy floor premise is used. -/
theorem actual_averaged_floor_rows (D : BaselineData) (F : BaselineSourceData D) (P : TransportParameters D)
    (padding : ℝ) (hpadding : 0 < padding) (hpad : padding+2*D.t ≤ 1/10000000000)
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
    ‖finiteCentralFullWRows F.S F.exclusions F.maximal η rows
      (sourcePrimePool F Z) (fun j => source_prime_pool_outside F Z j)
      (fun _ => F.W) (fun j => Z^(D.length j)) F.W F.W
      (Z^x) (Z^y) Z D.e (fun _ => 51/100) (fun u => (3*idx u+1:ℕ)*Z^tau)/
      ProbeAssembly.normalizer D F Z‖ ≤ C*(η.modulus.absNorm:ℝ)^(2*P.eps)*
        Z^(Geometry.signal theta-1/4000) := by
  have hcells := actual_averaged_floor_cells D F P padding hpad hbeta
  obtain ⟨Cd,hCd,hdyad⟩ := canonical_dyad_cost (1/4000) (by norm_num)
  intro tau ht n
  obtain ⟨C,hC,hcell⟩ := hcells tau ht n
  refine ⟨Cd*(n+1:ℕ)*C,by positivity,?_⟩
  intro η
  filter_upwards [hcell η,
    sourceDyad_geometry_eventually (1/200) (h+padding+2*D.t) D.t (h+padding)
      (by norm_num) (by norm_num) D.t_pos (le_refl _),
    eventually_gt_atTop (1:ℝ)] with Z hc hg hZ
  intro rows idx hr hnp hi hb
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hr0 (u) (hu:u∈rows) := (hr u hu).1
  have emptycell := hc ∅ (1/200) 0 le_rfl (by
    have hh := ActualGeometry.WidenedCoreBounds.h_interval.1
    linarith [D.t_pos]) (Nat.zero_le _) (by simp) (by simp)
      (by simp) (by simp) (by simp)
  refine ⟨emptycell.1,?_⟩
  have hbound := fullW_cells_norm_bound (K:=D.N) F.S F.exclusions F.maximal η rows
    (sourcePrimePool F Z) (fun j => source_prime_pool_outside F Z j)
    (fun _ => F.W) (fun j => Z^(D.length j)) F.W F.W
    (Z^x) (Z^y) Z D.e (Z^tau) (Z^(h+padding)) idx (fun _=>0) n 0
    (ProbeAssembly.normalizer D F Z) (C*(η.modulus.absNorm:ℝ)^(2*P.eps)*
      Z^(Geometry.signal theta-1/2000)) (by positivity)
    (fun u hu=>⟨(hr u hu).1,(hr u hu).2.2.2⟩)
    (fun u hu=>⟨hi u hu,le_rfl⟩) ?_
  · erw [Nat.cast_zero,mul_zero,add_zero] at hbound
    have htop : h+padding≤1 := by
      have hh := ActualGeometry.WidenedCoreBounds.h_interval.2
      linarith [D.t_pos]
    have hd := hdyad Z (h+padding) hZ.le htop
    calc
      _ ≤ _ := hbound
      _ ≤ (Cd*Z^(1/4000:ℝ))*(n+1:ℕ)*(0+1:ℕ)*
          (C*(η.modulus.absNorm:ℝ)^(2*P.eps)*Z^(Geometry.signal theta-1/2000)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (by positivity))
            (by positivity)) (by positivity)
      _ = _ := by
        simp only [Nat.cast_add,Nat.cast_zero,Nat.cast_one,zero_add,mul_one]
        rw [show Geometry.signal theta-1/4000 =
          (1/4000:ℝ)+(Geometry.signal theta-1/2000) by ring,Real.rpow_add hZp]
        ring
  · intro k hk i him j hj hn
    have hj0 : j=0 := by simpa using Finset.mem_range.mp hj
    subst j
    let R := cubeBinRows (rows∩dyadicRows 1 k) idx (fun _=>0) i 0
    have hsubk : R⊆rows∩dyadicRows 1 k := Finset.filter_subset _ _
    have hsub : R⊆rows := hsubk.trans Finset.inter_subset_left
    have hgeom := hg rows (fun u hu=>⟨(hr u hu).1,(hr u hu).2.1,(hr u hu).2.2.2⟩)
      k (hn.mono hsubk)
    have hd1 : sourceDyadConductor Z D.t k≤1 := hgeom.2.2.2.1.trans (by
      have hh := ActualGeometry.WidenedCoreBounds.h_interval.2
      linarith)
    have hh := hc R (sourceDyadConductor Z D.t k) i hgeom.2.2.1 hgeom.2.2.2.1
      (Nat.le_of_lt_succ (Finset.mem_range.mp him))
      (fun u hu=>⟨(hr u (hsub hu)).1,(hr u (hsub hu)).2.1,
        (hr u (hsub hu)).2.2.1,hgeom.2.2.2.2.2 u (hsubk hu)⟩) ?_
      (fun u hu=>hnp u (hsub hu)) ?_ ?_
    · erw [Nat.cast_zero,mul_zero,add_zero]
      exact hh.2
    · intro u hu
      constructor
      · rw [←Real.rpow_mul hZp.le]
        exact (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith only [hd1])).trans
          (hr u (hsub hu)).2.1
      · exact (hgeom.2.2.2.2.2 u (hsubk hu)).trans
          (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [D.t_pos]))
    · intro u hu
      have hlow := (hgeom.2.2.2.2.1 u (hsubk hu)).1
      apply (Real.rpow_le_rpow_of_exponent_le hZ.le ?_).trans hlow
      unfold sourceDyadConductor
      linarith [D.t_pos]
    · intro u hu
      have hidx := (mem_cubeBinRows (rows∩dyadicRows 1 k) idx (fun _=>0) i 0 u).mp hu
      simpa only [hidx.2.1] using hb u (hsub hu)

end QRH.Cycle092.SelectedFloorEstimate
#print axioms QRH.Cycle092.SelectedFloorEstimate.actual_averaged_floor_rows
