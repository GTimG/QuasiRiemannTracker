import WeightedQRH.NumeratorPhysicalMomentInput
import OAI.NumberTheory.DirichletL.Energy.ReferenceChildProfiles

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
namespace SevenEighths.WeightedNumeratorReflection
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyProfiles
open CenteredMomentEnergyReferenceChild CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentEnergyReferenceChildProfiles CenteredMomentDetectorDictionary
open CenteredMomentNaturalMaskedFloor CenteredMomentRetainedProfile CenteredMomentLattice

/-- Fixed conjugated annular derivative tests used after reflecting the numerator. -/
def numeratorAnnular (j : Fin 2) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap
    (derivativeChoice annulusTemplate.profile j)

lemma numeratorAnnular_apply (j : Fin 2) :
    (numeratorAnnular j : ℝ → ℂ) =
      fun x=>conj (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j x) := by
  change (fun x=>conj (derivativeChoice annulusTemplate.profile j x)) = _
  rw [derivativeChoice_apply]
  rfl

lemma numeratorAnnular_support (j : Fin 2) :
    Function.support (numeratorAnnular j : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4) := by
  rw [numeratorAnnular_apply,conjugate_profile_support]
  intro x hx
  have hh := scaleTest_support (fun y:ℝ=>(annulus y:ℂ)) (1/4) 1 annulus_support j hx
  exact ⟨hh.1,hh.2.trans (by norm_num)⟩

def numeratorFourierProfiles (j k : Fin 2) (v w : ℝ) : Profiles (1/4) (9/4) :=
  independentProfiles (by norm_num) (numeratorAnnular j) (numeratorAnnular k)
    (numeratorAnnular_support j) (numeratorAnnular_support k) (-2*Real.pi*v) (-2*Real.pi*w)

/-- The two unbounded Fourier frequencies have independently controlled polynomial
growth. This fixed degree is chosen before any final contour-height parameter. -/
theorem numerator_fourier_profiles_control (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ, ∃C : ℝ, 0 < C ∧ ∀j k : Fin 2, ∀v w : ℝ,
      (numeratorFourierProfiles j k v w).control S ^2 ≤
        C*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  obtain ⟨J,T,C,hC,hc⟩ := normPowerProfile_source_control (1/4) (9/4) (by norm_num) S
  let A : ℝ := 1+∑j:Fin 2, sourceControl T (numeratorAnnular j)
  have hA : 0 < A := by
    have hh := Finset.sum_nonneg (fun j (_:j∈Finset.univ)=>sourceControl_nonneg T (numeratorAnnular j))
    dsimp [A]; linarith
  have hA' (j : Fin 2) : sourceControl T (numeratorAnnular j) ≤ A := by
    have hh := Finset.single_le_sum
      (fun j (_:j∈Finset.univ)=>sourceControl_nonneg T (numeratorAnnular j)) (Finset.mem_univ j)
    dsimp [A]; linarith
  let B := C*A*(1+2*Real.pi)^J
  have hB : 0 < B := by dsimp [B]; positivity
  have hone (j : Fin 2) (v : ℝ) :
      sourceControl S (normPowerProfile (numeratorAnnular j) (1/4) (9/4) (by norm_num)
        (numeratorAnnular_support j) ((numeratorAnnular j).smooth ⊤) (-2*Real.pi*v))
        ≤ B*(1+‖v‖)^J := by
    have hh := hc (numeratorAnnular j) (numeratorAnnular_support j) (-2*Real.pi*v)
    have hv : 1+‖-2*Real.pi*v‖ ≤ (1+2*Real.pi)*(1+‖v‖) := by
      rw [norm_mul,norm_mul,Real.norm_of_nonneg Real.pi_pos.le]
      norm_num only [norm_neg,Real.norm_of_nonneg (by norm_num:0≤(2:ℝ))]
      nlinarith [Real.pi_pos,norm_nonneg v]
    calc
      _ ≤ C*sourceControl T (numeratorAnnular j)*(1+‖-2*Real.pi*v‖)^J := hh
      _ ≤ C*A*((1+2*Real.pi)*(1+‖v‖))^J := by
        gcongr
        exact hA' j
      _ = _ := by dsimp [B]; rw [mul_pow]; ring
  refine ⟨J,B^4,by positivity,?_⟩
  intro j k v w
  have hh : (numeratorFourierProfiles j k v w).control S ≤
      (B*(1+‖v‖)^J)*(B*(1+‖w‖)^J) := by
    simpa only [numeratorFourierProfiles,independentProfiles,Profiles.control,
      Fin.zero_eta,ite_true,show (1:Fin 2)≠0 by decide,ite_false] using
      mul_le_mul (hone j v) (hone k w) (sourceControl_nonneg _ _) (by positivity)
  calc
    _ ≤ ((B*(1+‖v‖)^J)*(B*(1+‖w‖)^J))^2 :=
      pow_le_pow_left₀ (Profiles.control_nonneg _ _) hh 2
    _ = _ := by ring

lemma numerator_fourier_polynomial_zero (χ : Character) (j k : Fin 2)
    (v w X : ℝ) :
    polynomial χ false ((numeratorFourierProfiles j k v w).profile 0) X 0 0 =
      polynomial χ false (fun x=>conj (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j x))
        X 0 (-2*Real.pi*v) := by
  change polynomial χ false (normPowerProfile _ _ _ _ _ _ _) X 0 0 = _
  rw [twist_polynomial,numeratorAnnular_apply]

lemma numerator_fourier_polynomial_one (χ : Character) (j k : Fin 2)
    (v w X : ℝ) :
    polynomial χ false ((numeratorFourierProfiles j k v w).profile 1) X 0 0 =
      polynomial χ false (fun x=>conj (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k x))
        X 0 (-2*Real.pi*w) := by
  change polynomial χ false (normPowerProfile _ _ _ _ _ _ _) X 0 0 = _
  rw [twist_polynomial,numeratorAnnular_apply]

lemma inverse_annular_norm_eq {D : WeightedQRH.MomentData}
    (F : ProbeFinalAssembly.WeightedSourceData D) (u : FreeRow) (j : Fin 2)
    (v X : ℝ) (hX : 0 < X) :
    ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X 0 (2*Real.pi*v)‖ =
    ‖polynomial ((momentData (fixedSourcePrincipal F.S F.exclusions.prime)).character
      (momentElement u)) false (fun x=>conj (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j x))
        X 0 (-2*Real.pi*v)‖ := by
  have hh := polynomial_inverse_norm (rowCharacter F.S F.exclusions.prime u) false
    (fun x=>conj (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j x)) X 0 (-2*Real.pi*v) hX
  simp only [Complex.conj_conj,neg_mul,neg_neg] at hh
  rw [hh,numerator_polynomial_eq_moment F.S F.exclusions.prime F.exclusions.bad]
  congr 2 <;> ring

end SevenEighths.WeightedNumeratorReflection
end
end OAI
