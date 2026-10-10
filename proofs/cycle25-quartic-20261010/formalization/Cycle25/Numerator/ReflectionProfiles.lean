import OAI.NumberTheory.DirichletL.Moments.OneReflectionScaleEnergy
import OAI.NumberTheory.DirichletL.Moments.UniformReflectionProfile
import OAI.NumberTheory.DirichletL.Moments.FrequencyScaleSupremum
import OAI.NumberTheory.DirichletL.Moments.ReflectedNormalization

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
namespace SevenEighths.Cycle25WeightedNumeratorReflection
open HeckeFamily HeckeDyadic EisensteinSchwartzPoisson
open CenteredMomentOneReflectionScaleEnergy
open CenteredMomentUniformReflectionProfile CenteredMomentReflectedProfileMeasure
open CenteredMomentFrequencyScaleSupremum CenteredMomentScaleSupremum
open CenteredMomentReflectedNormalization CenteredMomentSectorLocalization

/-- Applying the actual Fourier separation theorem twice transports a fourth moment,
with selected prime factors still squared. Profiles and scales may depend on the row. -/
theorem reflected_fourth_profiles (V : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hV : ∀y, V y ≠ 0 → |y| ≤ M) (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ), ∃C : ℝ, 0 < C ∧ ∀{ι : Type} [Fintype ι],
      ∀(G : ι → 𝓢(ℝ,ℂ)) (χ : ι → Character) (P : ι → ℂ) (s X : ι → ℝ),
      (∀i, 0 < s i) → (∀i, 0 < X i) → ∀D E : ℝ, 0 < D → 0 ≤ E →
      (∀i, H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i) ≤ D) →
      (∀v w : ℝ,
        (∑i, ‖polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v) *
          polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*w) * P i‖^2)
          ≤ E * ((1+‖v‖)^J)^2 * ((1+‖w‖)^J)^2) →
      (∑i, ‖polynomial (χ i) false
        (fun x => logWindow V x * ((1+s i)^A:ℂ) * paperRadialFourier (G i) (s i*x))
          (X i) 0 0‖^4 * ‖P i‖^2) ≤ C*D^4*E := by
  obtain ⟨H,K,hK,hbound⟩ := actual_one_uniform V M hM hV A J
  refine ⟨H,K^2,by positivity,?_⟩
  intro ι _ G χ P s X hs hX D E hD hE hGD henergy
  let f (i : ι) : ℂ := polynomial (χ i) false
    (fun x => logWindow V x * ((1+s i)^A:ℂ) * paperRadialFourier (G i) (s i*x))
      (X i) 0 0
  let p (i : ι) (v : ℝ) : ℂ :=
    polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)
  have hinner (v : ℝ) :
      (∑i, ‖p i v * f i * P i‖^2) ≤ K*D^2*(E*((1+‖v‖)^J)^2) := by
    have hh := hbound G χ (fun i => p i v * P i) s X hs hX D
      (E*((1+‖v‖)^J)^2) hD (by positivity) hGD (by
        intro w
        have he : (∑i, ‖p i w * (p i v * P i)‖^2) =
            ∑i, ‖p i v * p i w * P i‖^2 := by
          apply Finset.sum_congr rfl
          intro i _
          congr 2
          ring
        change (∑i, ‖p i w * (p i v * P i)‖^2) ≤ _
        rw [he]
        exact henergy v w)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    ring
  have houter := hbound G χ (fun i => f i * P i) s X hs hX D
    (K*D^2*E) hD (by positivity) hGD (by
      intro v
      have he : (∑i, ‖p i v * (f i * P i)‖^2) = ∑i, ‖p i v * f i * P i‖^2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_assoc]
      change (∑i, ‖p i v * (f i * P i)‖^2) ≤ _
      rw [he]
      exact (hinner v).trans_eq (by ring))
  calc
    _ = ∑i, ‖f i * (f i * P i)‖^2 := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [f,norm_mul]
      ring
    _ ≤ K*D^2*(K*D^2*E) := houter
    _ = _ := by ring

/-- The two scale-supremum variables remove row-dependent reflected lengths.
This is an actual fourth-moment statement about Hecke polynomials. -/
theorem reflected_fourth_rowwise_scales (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ), ∃C : ℝ, 0 < C ∧ ∀{ι : Type} [Fintype ι],
      ∀(G : ι → 𝓢(ℝ,ℂ)) (χ : ι → Character) (P : ι → ℂ)
        (s X : ι → ℝ) (lo hi D E : ℝ),
      lo ≤ hi → (∀i, 0 < s i) → (∀i, 0 < X i) →
      (∀i, Real.log (X i) ∈ Set.Icc lo hi) → 0 < D → 0 ≤ E →
      (∀i, H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i) ≤ D) →
      (∀v w : ℝ, ∀j k : Fin 2, ∀x ∈ Set.Icc lo hi, ∀y ∈ Set.Icc lo hi,
        (∑i, ‖polynomial (χ i) false (scaleTest (fun z : ℝ => (annulus z:ℂ)) j)
          (Real.exp x) 0 (2*Real.pi*v) *
          polynomial (χ i) false (scaleTest (fun z : ℝ => (annulus z:ℂ)) k)
          (Real.exp y) 0 (2*Real.pi*w) * P i‖^2)
          ≤ E * ((1+‖v‖)^J)^2 * ((1+‖w‖)^J)^2) →
      (∑i, ‖polynomial (χ i) false
        (fun x => (annulus x:ℂ) * ((1+s i)^A:ℂ) * paperRadialFourier (G i) (s i*x))
          (X i) 0 0‖^4 * ‖P i‖^2) ≤ C*D^4*(1+2*(hi-lo))^2*E := by
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hwindow : ∀y, CenteredMomentReflectedAnnuli.logWindow y ≠ 0 → |y| ≤ Real.log 4 := by
    intro y hy
    have hh := CenteredMomentReflectedAnnuli.logWindow_support hy
    exact abs_le.mpr ⟨hh.1,hh.2.trans hlog⟩
  obtain ⟨H,C,hC,hbound⟩ := reflected_fourth_profiles
    CenteredMomentReflectedAnnuli.logWindow (Real.log 4) hlog hwindow A J
  refine ⟨H,C,hC,?_⟩
  intro ι _ G χ P s X lo hi D E hlh hs hX hlogX hD hE hGD henergy
  have hlength : 0 ≤ 1+2*(hi-lo) := by linarith
  have hfixed (v w : ℝ) :
      (∑i, ‖polynomial (χ i) false (logWindow CenteredMomentReflectedAnnuli.logWindow)
        (X i) 0 (2*Real.pi*v) *
        polynomial (χ i) false (logWindow CenteredMomentReflectedAnnuli.logWindow)
        (X i) 0 (2*Real.pi*w) * P i‖^2)
      ≤ ((1+2*(hi-lo))^2*E) * ((1+‖v‖)^J)^2 * ((1+‖w‖)^J)^2 := by
    have hh := paired_rowwise_scales Finset.univ χ χ (fun _ => 2*Real.pi*v)
      (fun _ => 2*Real.pi*w) P (fun z : ℝ => (annulus z:ℂ))
      (fun z : ℝ => (annulus z:ℂ)) (1/4) 1 (1/4) 1 (by norm_num) (by norm_num)
      annulus_complex_support annulus_complex_support annulus_complex_smooth annulus_complex_smooth
      lo hi lo hi (E*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2) hlh hlh
      (fun i => Real.log (X i)) (fun i => Real.log (X i))
      (fun i _ => hlogX i) (fun i _ => hlogX i) (henergy v w)
    simp only [Real.exp_log (hX _)] at hh
    rw [actual_log_window]
    exact hh.trans_eq (by ring)
  have hh := hbound G χ P s X hs hX D ((1+2*(hi-lo))^2*E)
    hD (by positivity) hGD hfixed
  simp only [actual_log_window] at hh
  exact hh.trans_eq (by ring)

end SevenEighths.Cycle25WeightedNumeratorReflection
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/
