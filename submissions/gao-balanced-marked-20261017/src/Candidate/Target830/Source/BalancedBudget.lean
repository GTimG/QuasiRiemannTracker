import Candidate.Target830.Source.BalancedWindows

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Target830.Source
noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentFirstPhysicalSource
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy FourierBridge
local notation "O" => HeckeFamily.O

open Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentFirstAllocationGaussEnergy
open CenteredMomentLogDyadic CenteredMomentFirstCanonicalFamily CenteredMomentOriginalCommonHarmonic


lemma inverse_sqrt_rpow_shift (Z e σ : ℝ) (hZ : 0<Z) :
    (Real.sqrt (Z^e))⁻¹*Z^(-σ/2)=(Real.sqrt (Z^(e+σ)))⁻¹ := by
  simp only [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le,←Real.rpow_neg hZ.le,
    ←Real.rpow_add hZ]
  congr 1
  ring

lemma complex_inverse_sqrt_rpow_shift (Z e σ : ℝ) (hZ : 0<Z) :
    (Real.sqrt (Z^e):ℂ)⁻¹*((Z^(-σ/2):ℝ):ℂ)=
      (Real.sqrt (Z^(e+σ)):ℂ)⁻¹ := by
  exact_mod_cast inverse_sqrt_rpow_shift Z e σ hZ

variable {ι : Type*} [Fintype ι]

theorem balancedColumnScalar_formula (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (hZ : 0<Z) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) :
    balancedColumnScalar reflected s R seed K Z ξ M A hK key weight j=
      if reflected then
        (Real.sqrt (Z^(balancedRight A (geometryExponents s R seed K Z ξ j.1.val))):ℂ)⁻¹
      else weight j.1.val*(geometryFirstSource s R seed K Z ξ hK key j.1).outside/
        (Real.sqrt (Z^(2*outsideExponent M A (geometryExponents s R seed K Z ξ j.1.val)+
          balancedLeft A (geometryExponents s R seed K Z ξ j.1.val))):ℂ) := by
  unfold balancedColumnScalar geometryColumnScalar
  cases reflected
  · simp only [Bool.false_eq_true,ite_false]
    rw [left_eq_old]
    simp only [div_eq_mul_inv,mul_assoc]
    have he := complex_inverse_sqrt_rpow_shift Z
      (2*outsideExponent M A (geometryExponents s R seed K Z ξ j.1.val)+
        leftExponent A (geometryExponents s R seed K Z ξ j.1.val))
      (surplus (geometryExponents s R seed K Z ξ j.1.val)) hZ
    simp only [div_eq_mul_inv] at he
    rw [he]
    congr 3
    ring
  · simp only [ite_true]
    rw [right_eq_old]
    exact complex_inverse_sqrt_rpow_shift Z _ _ hZ


/-- The literal left child budget supplies the source premise of the
Mellin-window theorem, with original source volume as normalization. -/
theorem actual_balanced_left_budget_window (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (hZ : 0<Z) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (N : ℕ) (a b : ℝ) (ha : 0<a) (hcard : Fintype.card ι≤N)
    (haS : a≤s.lower) (hbS : s.upper≤b)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hc : HasCompactSupport logAnnulus) (hsm : ContDiff ℝ ∞ logAnnulus)
    (t : ℝ) (J : ℕ) (E : ℝ) (hE : 0≤E)
    (hbudget : ∀u : ℝ, balancedLiveBudget false s R seed K Z ξ M A hK key weight N b
      (s.t+2*Real.pi*(u-t))≤E*(1+‖u‖)^(2*J)) :
    balancedLeftEnergy s R seed K Z ξ M A hK key (fun q=>weight q.val)
      (fun _=>logAnnulus) t/volume s≤
      E*(∫u : ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
        logAnnulus hc hsm u‖)^2 := by
  apply actual_balanced_left_window_energy s R seed K Z ξ M A hK hZ key weight
    (fun q=>(actual_geometry_seed s R seed K Z ξ hK key hs hz₁ hz₂ q).1)
    (fun _=>logAnnulus) hc hsm t (volume s) (volume_pos s) J E hE
  intro u
  have hh := actual_balanced_source_budget false s R seed K Z ξ M A hK key weight N a b
    (s.t+2*Real.pi*(u-t)) ha hcard haS hbS hs hz₁ hz₂
  simp only [balancedColumnScalar_formula false s R seed K Z ξ M A hK hZ key,
    Bool.false_eq_true,ite_false] at hh
  exact le_trans hh (hbudget u)

/-- The reflected right budget passes through its independent Mellin
height, retaining the conjugate window from the actual first transform. -/
theorem actual_balanced_right_budget_window (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (hZ : 0<Z) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (N : ℕ) (a b : ℝ) (ha : 0<a) (hcard : Fintype.card ι≤N)
    (haS : a≤s.lower) (hbS : s.upper≤b)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hc : HasCompactSupport logAnnulus) (hsm : ContDiff ℝ ∞ logAnnulus)
    (t : ℝ) (J : ℕ) (E : ℝ) (hE : 0≤E)
    (hbudget : ∀u : ℝ, balancedLiveBudget true s R seed K Z ξ M A hK key weight N b
      (s.t+2*Real.pi*(u-(-t)))≤E*(1+‖u‖)^(2*J)) :
    balancedRightEnergy s R seed K Z ξ A hK key (fun _=>logAnnulus) t/volume s≤
      E*(∫u : ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
        (fun x=>star (logAnnulus x))
        (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
        (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hsm) u‖)^2 := by
  apply actual_balanced_right_window_energy s R seed K Z ξ A hK hZ key
    (fun q=>(actual_geometry_seed s R seed K Z ξ hK key hs hz₁ hz₂ q).2)
    (fun _=>logAnnulus) hc hsm t (volume s) (volume_pos s) J E hE
  intro u
  have hh := actual_balanced_source_budget true s R seed K Z ξ M A hK key weight N a b
    (s.t+2*Real.pi*(u-(-t))) ha hcard haS hbS hs hz₁ hz₂
  simp only [balancedColumnScalar_formula true s R seed K Z ξ M A hK hZ key,
    ite_true] at hh
  exact le_trans hh (hbudget u)

end
end OAI.SevenEighths.Target830.Source
#print axioms OAI.SevenEighths.Target830.Source.balancedColumnScalar_formula

#print axioms OAI.SevenEighths.Target830.Source.actual_balanced_left_budget_window
#print axioms OAI.SevenEighths.Target830.Source.actual_balanced_right_budget_window
