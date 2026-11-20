/- Geometry-free actual-source mass and fixed height-degree absorption.
Adapted from credited Bebel/Collet source helpers, Apache-2.0. -/
import Candidate.C092.transport.SelectedFloorEstimateHelpers
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly HeckeFamily ProbeHighRowFamily ProbePhysical
open PrincipalSignalComparison ProbePrincipalResidueActual ProbeRaySlots PrincipalMellinResidues
open Cycle25.Numerator Cycle25.Weighted.Numerator
namespace QRH.Cycle092.SelectedFloorEstimate
variable [Geometry.Parameters]
def HeightAdmissible (D : BaselineData)
    (P : Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly.TransportParameters D)
    (tau : ℝ) : Prop := 0 < tau ∧ 4*tau < D.cost/200 ∧ 2*tau*(1+2*P.eps) ≤ D.t
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

theorem source_pools_nonempty (D : BaselineData) (F : BaselineSourceData D) :
    ∀ᶠZ : ℝ in atTop,∀j : Fin D.N,(sourcePrimePool F Z j).Nonempty := by
  have hpos : ∀j : Fin D.N,tsupport F.w⊆Set.Ioi 0 := by
    intro j
    exact F.positive_support
  have hh := power_ray_mass_and_normalizer F.modulus ⊤ le_top F.S (fun _ : Fin D.N=>F.w)
    1 2 (by norm_num) (by norm_num) (fun _=>F.support) (fun _=>F.smooth)
    (fun _=>F.compact) hpos (fun _ x=>(F.bounded x).1) (fun _=>F.nonzero)
    D.length D.slots_pos (D.t/8) (by have:=D.t_pos; positivity)
  filter_upwards [hh] with Z hm
  intro j
  by_contra he
  have he0 := Finset.not_nonempty_iff_eq_empty.mp he
  have hzero : slotMass (sourcePrimePool F Z)
      (residueWeights (fun _=>F.w) (fun i=>Z^(D.length i))) j=0 := by
    simp only [slotMass,he0,Finset.sum_empty]
  have hp := hm.1 j
  change 0 < slotMass (sourcePrimePool F Z) (residueWeights (fun _=>F.w) (fun i=>Z^(D.length i))) j at hp
  rw [hzero] at hp
  exact lt_irrefl _ hp

end QRH.Cycle092.SelectedFloorEstimate
