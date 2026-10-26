import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondCoarseSupport
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.HighFrequency
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondFrequencyBudget
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstCanonicalFamily
open CenteredMomentAmplifiedRetainedRadius
open Cycle63Moment Cycle63HighFrequency CenteredMomentFirstScale

theorem eventual_actual_joint_frequency_coarse (u₀ : O)(b ε : ℝ)(N : ℕ)
    (hb : 0<b)(hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀(reflected left : Bool)(unit : FirstSourceLabel→Oˣ)
      (l : NonzeroJointSourceLabel left u₀ (fun k=>(unit k:O)))
      (_hC : Supported l.val.1.1.1)(_hD : Supported l.val.1.1.2),
      primeSupport l.val.1.1.1=primeSupport l.val.1.1.2 →
      ∀(K V a δ reserve ξ M Amax : ℝ),0<K → 0<V → ξ≤ε →
      K≤Z^M → (l.val.1.1.1.absNorm:ℝ)≤Z^Amax →
      0≤a → 0≤δ → 0≤ reserve →
      let C := l.val.1.1.1
      let D := l.val.1.1.2
      let E := l.val.1.2.val
      let c := Real.logb Z ((if reflected then D else C).absNorm:ℝ)
      let d := Real.logb Z ((if reflected then C else D).absNorm:ℝ)
      let Kmain := mainCommonRadius Z d
        (nominalLog C D (Ideal.span {primeSubsetGenerator (fun p:CommonIndex C D=>p.val) E}) K V Z)
        c (3*a) δ reserve
      let R := frequencyRadius ((b^N*V/((if reflected then D else C).absNorm:ℝ))^2/Kmain) Z ξ
      let A := (commonFrequencyGenerator l.val.2.1.1 l.val.2.1.2*
        nonunitFrequencyGenerator l.val.2.1.1 l.val.2.1.2 l.val.2.2.val.1)*l.val.2.2.val.2
      retainedWeight R (normValue A)≠0 →
      normValue (jointSourceRow left u₀ (fun k=>(unit k:O)) l.val)≤Z^(M+5*Amax+ε) := by
  filter_upwards [eventual_actual_joint_frequency_budget u₀ b ε N hb hε] with Z h
  refine ⟨h.1,?_⟩
  intro reflected left unit l hC hD heq K V a δ reserve ξ M Amax hK hV hξ hKM hCA ha hδ hreserve
    C D E c d Kmain R A hret
  have hf := h.2 reflected left unit l hC hD heq K V a δ reserve ξ hK hV hξ hret
  have hlogK := Real.logb_le_logb_of_le h.1 hK hKM
  rw [Real.logb_rpow (zero_lt_one.trans h.1) h.1.ne'] at hlogK
  have hlogC := Real.logb_le_logb_of_le h.1 (norm_pos _ hC.1) hCA
  rw [Real.logb_rpow (zero_lt_one.trans h.1) h.1.ne'] at hlogC
  have hnum := first_numerator_log_le left l.val.1 hC hD Z h.1
  have hactive : 0≤Real.logb Z (normValue (activeConductor C D)) := by
    apply Real.logb_nonneg h.1
    have hp := active_norm_pos C D
    change (1:ℝ)≤((Ideal.span {activeConductor C D}).absNorm:ℝ)
    have hn : 0<(Ideal.span {activeConductor C D}).absNorm := by exact_mod_cast hp
    exact_mod_cast hn
  apply hf.2.trans
  apply Real.rpow_le_rpow_of_exponent_le h.1.le
  dsimp only [C,D,c,d] at hactive ⊢
  linarith [le_max_right (Real.logb Z ((if reflected then l.val.1.1.2 else l.val.1.1.1).absNorm:ℝ)-
    Real.logb Z ((if reflected then l.val.1.1.1 else l.val.1.1.2).absNorm:ℝ)) 0]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
