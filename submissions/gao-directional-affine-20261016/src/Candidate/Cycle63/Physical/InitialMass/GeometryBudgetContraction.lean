import Candidate.Cycle63.Physical.InitialMass.GeometrySources

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
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
theorem actual_first_energy_from_geometry_budgets {ι : Type*}[Fintype ι]
    (s : Input ι) (R seed : Ideal O)(K Z ξ B M A : ℝ)(hK : 0<K)(hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (N : ℕ)(a b : ℝ)(ha : 0<a)(hcard : Fintype.card ι≤N)
    (haS : a≤s.lower)(hbS : s.upper≤b)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^B)
    (hc : HasCompactSupport logAnnulus)(hsm : ContDiff ℝ ∞ logAnnulus)
    (t : ℝ)(J : ℕ)(E H : ℝ)(hE : 0≤E)(hH : 0<H)
    (hleft : ∀u : ℝ,geometryLiveBudget false s R seed K Z ξ M A hK key weight N b
      (s.t+2*Real.pi*(u-t))≤(E*H)*(1+‖u‖)^(2*J))
    (hright : ∀u : ℝ,geometryLiveBudget true s R seed K Z ξ M A hK key weight N b
      (s.t+2*Real.pi*(u-(-t)))≤(E/H)*(1+‖u‖)^(2*J)) :
    firstActiveEnergyPair (geometryFirstSource s R seed K Z ξ hK key)
      (fun q=>weight q.val) (fun _=>logAnnulus) t ≤
      32*Z^M*(volume s*E)*
        |∫u : ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus hc hsm u‖| *
        |∫u : ℝ,(1+‖u‖)^J*‖columnDensity (fun x=>star (logAnnulus x))
          (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
          (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hsm) u‖| := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hL := actual_geometry_left_budget_window s R seed K Z ξ M A hK hz key weight
    N a b ha hcard haS hbS hs hz₁ hz₂ hc hsm t J (E*H) (mul_nonneg hE hH.le) hleft
  have hR := actual_geometry_right_budget_window s R seed K Z ξ M A hK hz key weight
    N a b ha hcard haS hbS hs hz₁ hz₂ hc hsm t J (E/H) (div_nonneg hE hH.le) hright
  let IL := ∫u : ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus hc hsm u‖
  let IR := ∫u : ℝ,(1+‖u‖)^J*‖columnDensity (fun x=>star (logAnnulus x))
    (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
    (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hsm) u‖
  have hv := volume_pos s
  have hve : 0≤volume s*E := mul_nonneg hv.le hE
  have hLe : geometryLeftEnergy s R seed K Z ξ M A hK key (fun q=>weight q.val)
      (fun _=>logAnnulus) t≤(volume s*(E*H))*IL^2 := by
    have hh := (div_le_iff₀ hv).mp hL
    simpa only [IL,mul_assoc,mul_comm,mul_left_comm] using hh
  have hRe : geometryRightEnergy s R seed K Z ξ A hK key (fun _=>logAnnulus) t≤
      (volume s*(E/H))*IR^2 := by
    have hh := (div_le_iff₀ hv).mp hR
    simpa only [IR,mul_assoc,mul_comm,mul_left_comm] using hh
  have hLs := Real.sqrt_le_sqrt hLe
  have hRs := Real.sqrt_le_sqrt hRe
  rw [Real.sqrt_mul (mul_nonneg hv.le (mul_nonneg hE hH.le)),Real.sqrt_sq_eq_abs] at hLs
  rw [Real.sqrt_mul (mul_nonneg hv.le (div_nonneg hE hH.le)),Real.sqrt_sq_eq_abs] at hRs
  have hprod := mul_le_mul hLs hRs (Real.sqrt_nonneg _) (by positivity)
  have hh := actual_first_energy_geometry_payment s R seed K Z ξ B M A hK hZ hs hz₁ hz₂
    hsource key (fun q=>weight q.val) (fun _=>logAnnulus) t
  apply hh.trans
  calc
    _≤(32*Z^M)*((Real.sqrt (volume s*(E*H))*|IL|)*(Real.sqrt (volume s*(E/H))*|IR|)) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod (by positivity : 0≤32*Z^M)
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
theorem actual_physical_mass_from_geometry_budgets {ι : Type*}[Fintype ι][DecidableEq ι]
    (W : 𝓢(ℝ,ℂ))(decay degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus)(hsm : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ,0≤C ∧ ∀(s : Input ι)(R seed : Ideal O)(K Z ξ B M A : ℝ)
      (hK : 0<K)(hZ : 1<Z)(N : ℕ)(a b : ℝ),0<a → Fintype.card ι≤N →
      a≤s.lower → s.upper≤b → Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^B →
      ∀E H : ℤ×(Fin 5→ℤ)→ℝ,(∀key∈commonGeometryBins s R seed K Z ξ,0≤E key) →
      (∀key∈commonGeometryBins s R seed K Z ξ,0<H key) →
      (∀key∈commonGeometryBins s R seed K Z ξ,∀(reflected : Bool)(t u : ℝ),
        geometryLiveBudget reflected s R seed K Z ξ M A hK key
          (fun q=>normPhase (coordinateBlock s R seed W K Z ξ q)) N b
          (s.t+2*Real.pi*(u-(if reflected then -t else t)))≤
          ((if reflected then E key/H key else E key*H key)*(1+‖t‖)^degree)*(1+‖u‖)^(2*windowDegree)) →
      physicalMass s R seed (CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator R) 1 W K Z ξ ≤
        C*Z^M*volume s*∑key∈commonGeometryBins s R seed K Z ξ,
          E key/(1+dyadicScale key.1)^decay := by
  obtain ⟨C,hC,hphysical⟩ := actual_physical_mass_geometry_contraction (ι:=ι) W decay degree
  let IL := ∫u : ℝ,(1+‖u‖)^windowDegree*‖columnDensity logAnnulus hc hsm u‖
  let IR := ∫u : ℝ,(1+‖u‖)^windowDegree*‖columnDensity (fun x=>star (logAnnulus x))
    (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
    (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hsm) u‖
  refine ⟨C*32*|IL| *|IR|,by positivity,?_⟩
  intro s R seed K Z ξ B M A hK hZ N a b ha hn haS hbS hs hz₁ hz₂ hsource E H hE hH hbudget
  let factor := 32*Z^M*volume s*|IL| *|IR|
  have hf : 0≤factor := by
    have hv := (volume_pos s).le
    have hz := (zero_lt_one.trans hZ).le
    dsimp [factor]
    positivity
  have hh := hphysical s R seed K Z ξ hK (fun key=>factor*E key)
    (fun key hk=>mul_nonneg hf (hE key hk)) (by
      intro key hk t
      have he := actual_first_energy_from_geometry_budgets s R seed K Z ξ B M A hK hZ
        key (fun q=>normPhase (coordinateBlock s R seed W K Z ξ q)) N a b ha hn haS hbS
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


/-- Separate the original height, outer Mellin height and column-window
height with one fixed factor; both reflection signs have the same cost. -/
lemma geometry_mellin_height (base height t u scale : ℝ)(hh : 0≤height) :
    1+|base+scale*(u-t)|+height≤
      (1+|base|+height)*(1+|scale|)*(1+‖t‖)*(1+‖u‖) := by
  have hsub : |u-t|≤|u|+|t| := by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le u (-t)
  have hab : |base+scale*(u-t)|≤|base|+|scale| *(|u|+|t|) := by
    calc
      _≤|base|+|scale*(u-t)| := abs_add_le _ _
      _≤_ := by rw [abs_mul]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsub (abs_nonneg scale))
  have ht : 0≤|t| := abs_nonneg t
  have hu : 0≤|u| := abs_nonneg u
  have hs : 0≤|scale| := abs_nonneg scale
  have hbase : 1≤1+|base|+height := by linarith [abs_nonneg base]
  have hprod : 0≤|t| *|u| := mul_nonneg ht hu
  have hprodS : 0≤|scale| *(|t| *|u|) := mul_nonneg hs hprod
  have hinner : 1+|scale| *(|u|+|t|)≤(1+|scale|)*(1+|t|)*(1+|u|) := by nlinarith
  have hfirst : 1+|base+scale*(u-t)|+height≤
      (1+|base|+height)*(1+|scale| *(|u|+|t|)) := by
    have hmul := mul_le_mul_of_nonneg_right hbase (mul_nonneg hs (add_nonneg hu ht))
    nlinarith
  apply hfirst.trans
  simpa only [Real.norm_eq_abs,mul_assoc] using
    mul_le_mul_of_nonneg_left hinner (zero_le_one.trans hbase)

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_first_energy_from_geometry_budgets

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_physical_mass_from_geometry_budgets

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_mellin_height
