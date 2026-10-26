/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform LOW guards for both actual graph rule types and both NF fee profiles. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.PhysicalLowGuard
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.PhysicalLowGuard
noncomputable section
open Filter Record1252270103Finite Record1252270103StepScalar QRH.Record1252270103Graph
open OAI.SevenEighths.CenteredMomentSectorLocalization

/-- This is a numerical guard, not a source or energy assumption. Its inputs
are the actual geometric upper/lower bounds and the preselected small parameters. -/
def GuardAt (n low : Source) (N : ℕ) (upper plainUpper ξ Z b : ℝ) : Prop :=
  ∀(t F slots width reserve rho plainRound : ℝ),
    0≤reserve → 0≤rho → width≤step n → reserve≤step n → rho≤step n → plainRound≤step n →
    t≤sourceTReal n b+(n.L:ℝ)*width →
    sourceFReal n low b-frequencyLoss Z 32 ξ-reserve≤F → slots≤b →
    (3*(N:ℝ)*Real.logb Z upper+2*Real.logb Z (max 1 plainUpper)+2*plainRound)+
      (low.B:ℝ)*rho+2*(n.allowance:ℝ)≤(low.B:ℝ)*F-t-slots

theorem nf_guard_step_positive (n low : Source) (high : Option Source)
    (hv : SourceValid n low high) (ha : NFAccounting n) : 0<step n := by
  apply step_positive
  · exact_mod_cast (nf_accounting_positive ha).1
  · have hl : (1:ℝ)<n.L := by exact_mod_cast hv.2.2.1
    linarith

theorem seed_allowance_positive (n low : Source) (hv : SeedSourceValid n low) :
    0<(n.allowance:ℝ) := by
  have ha : n.allowance=1/10^12 := by
    rcases hv with ⟨_,_,_,_,_,_,_,_,_,_,_,ha,_⟩
    exact ha
  rw [ha]
  norm_num

theorem seed_guard_step_positive (n low : Source) (hv : SeedSourceValid n low) :
    0<step n := by
  apply step_positive n (seed_allowance_positive n low hv)
  have hl : (1:ℝ)<n.L := by exact_mod_cast hv.2.2.1
  linarith

/-- One threshold works for every real width in the selected NF cell, including
its endpoints and either supplied exact accounting profile. -/
theorem nf_eventually_guard (n low : Source) (high : Option Source)
    (hv : SourceValid n low high) (hlow : ParentGood low) (ha : NFAccounting n)
    (N : ℕ) (upper plainUpper ξ : ℝ) (hupper : 1≤upper) (hξ : 0<ξ) (hξstep : ξ≤step n) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀b∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ),
      GuardAt n low N upper plainUpper ξ Z b := by
  have he : 0<(n.allowance:ℝ) := by exact_mod_cast (nf_accounting_positive ha).1
  have hL : 0≤(n.L:ℝ) := by
    have hl : (1:ℝ)<n.L := by exact_mod_cast hv.2.2.1
    linarith
  have hB0 : 0≤(low.B:ℝ) := by exact_mod_cast hlow.1.le
  have hB1 : (low.B:ℝ)≤1 := by exact_mod_cast hlow.2.1
  filter_upwards [eventually_geometry_guard n low N upper plainUpper ξ he hL hB0 hB1
    hupper hξ hξstep] with Z hz
  exact ⟨hz.1,fun b hb => hz.2 _ b (nf_real_geometry n low high hv hlow hb)⟩

theorem seed_eventually_guard (n low : Source) (hv : SeedSourceValid n low)
    (hlow : ParentGood low) (N : ℕ) (upper plainUpper ξ : ℝ)
    (hupper : 1≤upper) (hξ : 0<ξ) (hξstep : ξ≤step n) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀b∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ),
      GuardAt n low N upper plainUpper ξ Z b := by
  have he := seed_allowance_positive n low hv
  have hL : 0≤(n.L:ℝ) := by
    have hl : (1:ℝ)<n.L := by exact_mod_cast hv.2.2.1
    linarith
  have hB0 : 0≤(low.B:ℝ) := by exact_mod_cast hlow.1.le
  have hB1 : (low.B:ℝ)≤1 := by exact_mod_cast hlow.2.1
  filter_upwards [eventually_geometry_guard n low N upper plainUpper ξ he hL hB0 hB1
    hupper hξ hξstep] with Z hz
  exact ⟨hz.1,fun b hb => hz.2 _ b (seed_real_geometry n low hv hlow hb)⟩

end
end QRH.Record1252270103Source.PhysicalLowGuard
#print axioms QRH.Record1252270103Source.PhysicalLowGuard.nf_guard_step_positive
#print axioms QRH.Record1252270103Source.PhysicalLowGuard.seed_allowance_positive
#print axioms QRH.Record1252270103Source.PhysicalLowGuard.seed_guard_step_positive
#print axioms QRH.Record1252270103Source.PhysicalLowGuard.nf_eventually_guard
#print axioms QRH.Record1252270103Source.PhysicalLowGuard.seed_eventually_guard
