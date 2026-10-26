/- A single height is chosen after the physical and count polynomial degrees.
Adapted Gao/Hailey Collet/OpenAI; Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.Schedule
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.SourceMoments
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.MomentMono
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.Chosen
set_option autoImplicit false
open QRH.Record1252270103Return

namespace QRH.Record1252270103Return.GenericPhysical.PhysicalDirect
variable [Geometry.Parameters] [Geometry.Bounds] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
noncomputable section
set_option maxHeartbeats 200000
open scoped Classical
open Filter OAI OAI.SevenEighths HeckeFamily QRH.Record1252270103Return.GenericArithmetic
open QRH.Record1252270103Return.GenericPhysical (baselineSource)
open QRH.Record1252270103Return.GenericPhysical.FinalAssembly
open QRH.Record12518109Count
open QRH.Record1252270103Return.GenericCount

theorem actual_joint_height (A : ChosenData) (hgap : theta<HeckeZeroSupremum.beta)
    (haffine : ∀w∈scheme.windows,WeightedAffineFineInput A.F w.face)
    (Jw : ℝ) (hJw : 0≤Jw) :
    ∀η : Character,∃τ : ℝ,HeightAdmissible A.D A.P Jw τ ∧
      ∃C : ℝ,1≤C ∧ ∀ᶠZ : ℝ in atTop,
        SourceMomentBound A.D (baselineSource A.D A.F) A.counts η Z τ
          (C*Z^A.D.t) (Z^(2*τ)) := by
  intro η
  have hb : (51/100:ℝ)≤HeckeZeroSupremum.beta := by
    have ht : (51/100:ℝ)<theta := by linarith [Geometry.Bounds.theta_bounds.1]
    linarith
  have hk : 2*HeckeZeroSupremum.beta-1≤scheme.naturalκ := by
    rw [←A.kappa_exact];exact A.kappa_incumbent
  obtain ⟨J,hJ,C,hC,hbound⟩ := actual_source_moments A.D A.F A.counts hb A.kappa_exact.ge hk A.fine haffine η
  obtain ⟨τ,hheight⟩ := choose_height A.D A.P (J+Jw) (by positivity)
  have hw : HeightAdmissible A.D A.P Jw τ := height_admissible_mono hheight (by linarith)
  have hc : HeightAdmissible A.D A.P J τ := height_admissible_mono hheight (by linarith)
  refine ⟨τ,hw,max 1 (C*2^J),le_max_left _ _,?_⟩
  filter_upwards [hbound τ hc.1 (by linarith [hc.2.1]),eventually_ge_atTop (1:ℝ)] with Z hm hZ
  apply hm.mono_constant (by linarith)
  apply (ProbeFinalAssembly.polynomial_height_absorption C Z τ J A.D.t hC.le hZ hc.1.le hJ
    (by linarith [hc.2.2.2.2.2])).trans
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _)
end
end QRH.Record1252270103Return.GenericPhysical.PhysicalDirect
#print axioms QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.actual_joint_height
