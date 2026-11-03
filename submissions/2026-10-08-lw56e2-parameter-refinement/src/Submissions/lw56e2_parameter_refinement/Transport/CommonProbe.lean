/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/CommonProbe.lean
Original SHA-256: 49305aa24aff3edd3264d544e317110da4bd6a10811d3d029fcdb02fb123eae4
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.FixedHigh
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.DataMoments
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalAnalytic.HeckeBridge
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalAnalytic.SourceCorrection

/-! Assembly of the actual common probe. Every arithmetic and analytic input
is produced by the preceding modules; only the original 7/8 family ceiling
is a hypothesis here. OriginalBaseline discharges that hypothesis separately. -/

namespace LW56e2.Transport
noncomputable section
open scoped Classical
open Filter Asymptotics
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeFinalAssembly PrincipalSignalComparison

lemma tuned_signal_add_shift (s : ℝ) :
    TunedCandidate.signal s=s+TunedCandidate.signal 0 := by
  rw [TunedCandidate.signal_eq,TunedCandidate.signal_eq]
  ring

theorem actual_uniform_common_probe
    (hceiling : HeckeZeroSupremum.beta≤7/8) :
    PhysicalAnalytic.UniformCommonProbe TunedCandidate.B (TunedCandidate.signal 0) := by
  intro hβ
  obtain ⟨D⟩ := PhysicalHigh.exists_tuned_data 0 1 (by norm_num)
  obtain ⟨seed,F,_,hfirst⟩ := PhysicalHigh.exists_tuned_source_data D.P.e D.P.e_pos ∅ (by simp)
  obtain ⟨counts⟩ := PhysicalHigh.exists_tuned_count_parameters F PhysicalHigh.reservedLoss
    PhysicalHigh.reservedLoss_pos
  have hβ51 : (51/100:ℝ)≤HeckeZeroSupremum.beta := by
    have hB := TunedCandidate.boundary_value
    linarith
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτ2,hτeps,hsource⟩ :=
    PhysicalHigh.data_chosen_moments F D counts hβ51 hceiling
  obtain ⟨C,hC,hhigh⟩ := PhysicalHigh.fixed_high_bound hβ hceiling D F hfirst counts τ
    hτ hτd hτcost hτt hτ2 hτeps
  let ω := (HeckeZeroSupremum.beta-TunedCandidate.B)/2
  have hω : 0<ω := by dsimp [ω];linarith
  have hωgap : ω<HeckeZeroSupremum.beta-TunedCandidate.B := by dsimp [ω];linarith
  refine ⟨ω,D.P.sigma,hω,hωgap,D.P.sigma_pos,?_⟩
  intro η _hprimitive
  obtain ⟨hmask,hH,hHbound⟩ := PhysicalAnalytic.actual_source_analytic_transported
    TunedCandidate.p TunedCandidate.p_lt_one_thousandth F.S F.exclusions η
  rw [←TunedCandidate.boundary_eq_geometry] at hH hHbound
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,
    dataProbe F D η,hmask,hH,hHbound,?_,?_⟩
  · simpa only [tuned_signal_add_shift TunedCandidate.B] using dataProbe_low F D ω hω η
  · obtain ⟨Ct,hCt,hbound⟩ := hhigh η
    obtain ⟨Cm,hCm,hmoment⟩ := hsource η
    apply PhysicalLow.isBigO_rpow_of_eventual_norm_bound
    refine ⟨Ct+C*Cm*(η.modulus.absNorm:ℝ)^(2*D.P.eps),by positivity,?_⟩
    filter_upwards [hbound,hmoment] with Z hb hm
    simpa only [tuned_signal_add_shift HeckeZeroSupremum.beta] using hb Cm hCm.le hm.2

theorem improved_hecke_boundary_of_original
    (hceiling : HeckeZeroSupremum.beta≤7/8) :
    HeckeZeroSupremum.beta≤TunedCandidate.B :=
  PhysicalAnalytic.hecke_beta_le_boundary
    (by rw [TunedCandidate.boundary_value];norm_num)
    TunedCandidate.boundary_improvement.le (actual_uniform_common_probe hceiling)

end
end LW56e2.Transport
