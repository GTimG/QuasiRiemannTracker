/- Adapted from Zhongpai Gao, gao-balanced-marked-20261017, Apache-2.0;
upstream math snapshot 9c0e14f985041e397f71c574028193ee595a0f98.
Underlying Cycle61: Hailey Collet; original analytic interfaces: OpenAI, Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalBalancedBudget

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle61InitialMass
open scoped Classical BigOperators ContDiff SchwartzMap
open MeasureTheory HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceMass CenteredMomentScale
open CenteredMomentFirstSourceReduction CenteredMomentSectorLocalization
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstPhysicalSource CenteredMomentSourceLiveColumn
open CenteredMomentLogDyadic CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O

/-- The two actual first-source budgets pass through their own Mellin
windows and the cross-label normalization, with no per-label Cauchy shortcut. -/
theorem actual_first_energy_from_balanced_budgets {ι : Type*}[Fintype ι][DecidableEq ι]
    (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)(K Z ξ B M A : ℝ)(hK : 0<K)(hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ))
    (weight : SourceCoordinate s modifier R seed K Z ξ→ℂ)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^B)
    (hc : HasCompactSupport logAnnulus)(hsm : ContDiff ℝ ∞ logAnnulus)
    (t : ℝ)(J : ℕ)(E H : ℝ)(hE : 0≤E)(hH : 0<H)
    (hleft : ∀u : ℝ,balancedLiveBudget false s modifier R seed K Z ξ M A hK key weight
      (s.t+2*Real.pi*(u-t))≤(E*H)*(1+‖u‖)^(2*J))
    (hright : ∀u : ℝ,balancedLiveBudget true s modifier R seed K Z ξ M A hK key weight
      (s.t+2*Real.pi*(u-(-t)))≤(E/H)*(1+‖u‖)^(2*J)) :
    firstActiveEnergyPair (geometryFirstSource s modifier R seed K Z ξ hK key)
      (fun q=>weight q.val) (fun _=>logAnnulus) t ≤
      4*Z^M*(volume s*E)*
        |∫u : ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus hc hsm u‖| *
        |∫u : ℝ,(1+‖u‖)^J*‖columnDensity (fun x=>star (logAnnulus x))
          (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
          (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hsm) u‖| := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hL := actual_balanced_left_budget_window s modifier R seed K Z ξ M A hK hz key weight
    hs hz₁ hz₂ hc hsm t J (E*H) (mul_nonneg hE hH.le) hleft
  have hR := actual_balanced_right_budget_window s modifier R seed K Z ξ M A hK hz key weight
    hs hz₁ hz₂ hc hsm t J (E/H) (div_nonneg hE hH.le) hright
  let IL := ∫u : ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus hc hsm u‖
  let IR := ∫u : ℝ,(1+‖u‖)^J*‖columnDensity (fun x=>star (logAnnulus x))
    (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
    (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hsm) u‖
  have hv := volume_pos s
  have hve : 0≤volume s*E := mul_nonneg hv.le hE
  have hLe : balancedLeftEnergy s modifier R seed K Z ξ M A hK key (fun q=>weight q.val)
      (fun _=>logAnnulus) t≤(volume s*(E*H))*IL^2 := by
    have hh := (div_le_iff₀ hv).mp hL
    simpa only [IL,mul_assoc,mul_comm,mul_left_comm] using hh
  have hRe : balancedRightEnergy s modifier R seed K Z ξ A hK key (fun _=>logAnnulus) t≤
      (volume s*(E/H))*IR^2 := by
    have hh := (div_le_iff₀ hv).mp hR
    simpa only [IR,mul_assoc,mul_comm,mul_left_comm] using hh
  have hLs := Real.sqrt_le_sqrt hLe
  have hRs := Real.sqrt_le_sqrt hRe
  rw [Real.sqrt_mul (mul_nonneg hv.le (mul_nonneg hE hH.le)),Real.sqrt_sq_eq_abs] at hLs
  rw [Real.sqrt_mul (mul_nonneg hv.le (div_nonneg hE hH.le)),Real.sqrt_sq_eq_abs] at hRs
  have hprod := mul_le_mul hLs hRs (Real.sqrt_nonneg _) (by positivity)
  have hh := actual_first_energy_balanced_payment s modifier R seed K Z ξ B M A hK hZ hs hz₁ hz₂
    hsource key (fun q=>weight q.val) (fun _=>logAnnulus) t
  apply hh.trans
  calc
    _≤(4*Z^M)*((Real.sqrt (volume s*(E*H))*|IL|)*(Real.sqrt (volume s*(E/H))*|IR|)) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod (by positivity : 0≤4*Z^M)
    _=_ := by
      have heq : (Real.sqrt (volume s*(E*H))*|IL|)*(Real.sqrt (volume s*(E/H))*|IR|)=
          (volume s*E)*|IL| *|IR| := by
        have hp : (volume s*(E*H))*(volume s*(E/H))=(volume s*E)^2 := by
          field_simp
        have hr : Real.sqrt (volume s*(E*H))*Real.sqrt (volume s*(E/H))=volume s*E := by
          rw [←Real.sqrt_mul (mul_nonneg hv.le (mul_nonneg hE hH.le)),hp,Real.sqrt_sq hve]
        calc
          _=(Real.sqrt (volume s*(E*H))*Real.sqrt (volume s*(E/H)))*|IL| *|IR| := by ring
          _=_ := by rw [hr]
      rw [heq]
      dsimp only [IL,IR]
      ring


/-- The remaining analytic input is a bound on the literal normalized
live-source budgets. Both Mellin integrals and original physical contraction
are discharged here, uniformly before moving sources and geometry bins. -/
theorem actual_physical_mass_from_balanced_budgets {ι : Type*}[Fintype ι][DecidableEq ι]
    (W : 𝓢(ℝ,ℂ))(decay degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus)(hsm : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ,0≤C ∧ ∀(s : Input ι)(modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)(R seed : Ideal O)(K Z ξ B M A : ℝ)
      (hK : 0<K)(hZ : 1<Z),Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^B →
      ∀E H : ℤ×(Fin 5→ℤ)→ℝ,(∀key∈commonGeometryBins s modifier R seed K Z ξ,0≤E key) →
      (∀key∈commonGeometryBins s modifier R seed K Z ξ,0<H key) →
      (∀key∈commonGeometryBins s modifier R seed K Z ξ,∀(reflected : Bool)(t u : ℝ),
        balancedLiveBudget reflected s modifier R seed K Z ξ M A hK key
          (fun q=>normPhase (coordinateBlock s modifier R seed W K Z ξ q))
          (s.t+2*Real.pi*(u-(if reflected then -t else t)))≤
          ((if reflected then E key/H key else E key*H key)*(1+‖t‖)^degree)*(1+‖u‖)^(2*windowDegree)) →
      physicalMass s modifier R seed (CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator R) 1 W K Z ξ ≤
        C*Z^M*volume s*∑key∈commonGeometryBins s modifier R seed K Z ξ,
          E key/(1+dyadicScale key.1)^decay := by
  obtain ⟨C,hC,hphysical⟩ := actual_physical_mass_geometry_contraction (ι:=ι) W decay degree
  let IL := ∫u : ℝ,(1+‖u‖)^windowDegree*‖columnDensity logAnnulus hc hsm u‖
  let IR := ∫u : ℝ,(1+‖u‖)^windowDegree*‖columnDensity (fun x=>star (logAnnulus x))
    (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
    (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hsm) u‖
  refine ⟨C*4*|IL| *|IR|,by positivity,?_⟩
  intro s modifier R seed K Z ξ B M A hK hZ hs hz₁ hz₂ hsource E H hE hH hbudget
  let factor := 4*Z^M*volume s*|IL| *|IR|
  have hf : 0≤factor := by
    have hv := (volume_pos s).le
    have hz := (zero_lt_one.trans hZ).le
    dsimp [factor]
    positivity
  have hh := hphysical s modifier R seed K Z ξ hK (fun key=>factor*E key)
    (fun key hk=>mul_nonneg hf (hE key hk)) (by
      intro key hk t
      have he := actual_first_energy_from_balanced_budgets s modifier R seed K Z ξ B M A hK hZ
        key (fun q=>normPhase (coordinateBlock s modifier R seed W K Z ξ q))
        hs hz₁ hz₂ hsource hc hsm t windowDegree (E key*(1+‖t‖)^degree) (H key)
        (mul_nonneg (hE key hk) (by positivity)) (hH key hk)
        (fun u=>by simpa only [Bool.false_eq_true,ite_false,mul_assoc,mul_comm,mul_left_comm] using hbudget key hk false t u)
        (fun u=>by simpa only [ite_true,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hbudget key hk true t u)
      apply he.trans_eq
      dsimp only [factor,IL,IR]
      ring)
  apply hh.trans_eq
  simp only [mul_div_assoc,←Finset.mul_sum]
  dsimp only [factor]
  ring



end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_first_energy_from_balanced_budgets
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_physical_mass_from_balanced_budgets
