import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondFrequency
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.HighFrequency
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
open Cycle63Moment Cycle63HighFrequency

/-- Fixed units and fixed presentation constants have uniformly vanishing
logarithmic cost. The threshold precedes every arithmetic label and unit
choice. -/
theorem eventual_joint_fixed_frequency_cost (u₀ : O)(b ε : ℝ)(N : ℕ)(hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀u : Oˣ,
      Real.logb Z (normValue (u₀*(u:O)))+2*(N:ℝ)*Real.logb Z b+Real.logb Z 4≤ε := by
  let c := Real.log (normValue u₀)+2*(N:ℝ)*Real.log b+Real.log 4
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (c/ε)),
    eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro u
  rw [fixed_unit_norm u₀ (u:O) u.isUnit]
  have he : Real.logb Z (normValue u₀)+2*(N:ℝ)*Real.logb Z b+Real.logb Z 4=c/Real.log Z := by
    dsimp only [Real.logb,c]
    ring
  rw [he]
  exact (div_le_iff₀ (Real.log_pos hZ)).mpr (by nlinarith [(div_le_iff₀ hε).mp hc])

/-- A source times a unit, with the fixed presentation constants, has
logarithmic cost at most `ε` above the logarithm of the source norm. The
threshold precedes the source and the unit. -/
theorem eventual_joint_frequency_cost_uniform (b ε : ℝ)(N : ℕ)(hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀(u₀ : O)(u : Oˣ),
      Real.logb Z (normValue (u₀*(u:O)))+2*(N:ℝ)*Real.logb Z b+Real.logb Z 4≤
        Real.logb Z (normValue u₀)+ε := by
  let c := 2*(N:ℝ)*Real.log b+Real.log 4
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (c/ε)),
    eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro u₀ u
  rw [fixed_unit_norm u₀ (u:O) u.isUnit]
  have he : 2*(N:ℝ)*Real.logb Z b+Real.logb Z 4=c/Real.log Z := by
    dsimp only [Real.logb,c]
    ring
  have hle : c/Real.log Z≤ε :=
    (div_le_iff₀ (Real.log_pos hZ)).mpr (by nlinarith [(div_le_iff₀ hε).mp hc])
  linarith

/-- The literal retained weight supplies the sharp joint frequency
budget with all fixed costs absorbed before any moving source is chosen. -/
theorem eventual_actual_joint_frequency_budget (u₀ : O)(b ε : ℝ)(N : ℕ)
    (hb : 0<b)(hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀(reflected left : Bool)(unit : FirstSourceLabel→Oˣ)
      (l : NonzeroJointSourceLabel left u₀ (fun k=>(unit k:O)))
      (_hC : Supported l.val.1.1.1)(_hD : Supported l.val.1.1.2),
      primeSupport l.val.1.1.1=primeSupport l.val.1.1.2 →
      ∀(K V a δ reserve ξ : ℝ),0<K → 0<V → ξ≤ε →
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
      let q := Real.logb Z K-Real.logb Z (normValue (activeConductor C D))-max (c-d) 0+
        Real.logb Z (normValue (firstSourceNumerator left l.val.1))-6*a-δ-reserve+ε
      0≤q ∧ normValue (jointSourceRow left u₀ (fun k=>(unit k:O)) l.val)≤Z^q := by
  filter_upwards [eventual_joint_fixed_frequency_cost u₀ b (ε/2) N (by positivity)] with Z h
  refine ⟨h.1,?_⟩
  intro reflected left unit l hC hD heq K V a δ reserve ξ hK hV hξ C D E c d Kmain R A hret q
  have hf := actual_joint_frequency_log_oriented reflected left u₀ (fun k=>(unit k:O)) l
    hC hD heq K V Z a δ reserve ξ b N hK hV h.1 hb hret
  have hp := h.2 (unit l.val.1)
  have hlog : Real.logb Z (normValue (jointSourceRow left u₀ (fun k=>(unit k:O)) l.val))≤q := by
    dsimp only [q,c,d,C,D]
    linarith
  exact ⟨hf.1.trans hlog,(Real.logb_le_iff_le_rpow h.1 (normValue_pos _ l.property)).mp hlog⟩

/-- The literal retained weight supplies the sharp joint frequency budget with
the source norm kept as an exact additive exponent. The threshold precedes the
source and every arithmetic label. -/
theorem eventual_actual_joint_frequency_budget_uniform (b ε : ℝ)(N : ℕ)
    (hb : 0<b)(hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀(u₀ : O)(reflected left : Bool)(unit : FirstSourceLabel→Oˣ)
      (l : NonzeroJointSourceLabel left u₀ (fun k=>(unit k:O)))
      (_hC : Supported l.val.1.1.1)(_hD : Supported l.val.1.1.2),
      primeSupport l.val.1.1.1=primeSupport l.val.1.1.2 →
      ∀(K V a δ reserve ξ : ℝ),0<K → 0<V → ξ≤ε →
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
      let q := Real.logb Z K-Real.logb Z (normValue (activeConductor C D))-max (c-d) 0+
        Real.logb Z (normValue (firstSourceNumerator left l.val.1))-6*a-δ-reserve+ε
      0≤q+Real.logb Z (normValue u₀) ∧
        normValue (jointSourceRow left u₀ (fun k=>(unit k:O)) l.val)≤
          Z^(q+Real.logb Z (normValue u₀)) := by
  filter_upwards [eventual_joint_frequency_cost_uniform b (ε/2) N (by positivity)] with Z h
  refine ⟨h.1,?_⟩
  intro u₀ reflected left unit l hC hD heq K V a δ reserve ξ hK hV hξ C D E c d Kmain R A hret q
  have hf := actual_joint_frequency_log_oriented reflected left u₀ (fun k=>(unit k:O)) l
    hC hD heq K V Z a δ reserve ξ b N hK hV h.1 hb hret
  have hp := h.2 u₀ (unit l.val.1)
  have hlog : Real.logb Z (normValue (jointSourceRow left u₀ (fun k=>(unit k:O)) l.val))≤
      q+Real.logb Z (normValue u₀) := by
    dsimp only [q,c,d,C,D]
    linarith
  exact ⟨hf.1.trans hlog,(Real.logb_le_iff_le_rpow h.1 (normValue_pos _ l.property)).mp hlog⟩

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
