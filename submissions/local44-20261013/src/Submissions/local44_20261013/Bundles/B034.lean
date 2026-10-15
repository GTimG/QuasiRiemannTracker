/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B006
import Submissions.local44_20261013.Bundles.B007
import Submissions.local44_20261013.Bundles.B029
import Submissions.local44_20261013.Bundles.B030
import Submissions.local44_20261013.Bundles.B031
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondBlockRadicalHarmonicMass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceBlockWindows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceLowerSupport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersHighDataFine

/- BEGIN ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblyChosenData ; sha256 3bba00cc2d9fd6a48badfac7e69be7bb2785f887b3b0c689b6c3660b18ce9450 -/
section



namespace OAI

noncomputable section
open scoped Classical
open Filter

namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison

def ChosenMomentInput:Prop:=
  ∀_hβ:(7/8:ℝ)< HeckeZeroSupremum.beta,
    ∃D:HighData (HeckeZeroSupremum.beta-7/8),∃F:SourceData D,
    ∃counts:CountParameters F.modulus ⊤ D.t,
    ∃J:ℝ,0≤ J ∧ ∀η:Character,∃C:ℝ,0< C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

def FineMomentInput:Prop:=
  ∀_hβ:(7/8:ℝ)< HeckeZeroSupremum.beta,
    ∃mesh:ℝ→ℝ,(∀t:ℝ,0< t→0< mesh t) ∧
    ∀D:HighData (HeckeZeroSupremum.beta-7/8),(∀j,D.ell j≤ mesh D.t/200)→
    ∀F:SourceData D,∀counts:CountParameters F.modulus ⊤ D.t,
    ∃J:ℝ,0≤ J ∧ ∀η:Character,∃C:ℝ,0< C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

theorem chosen_input_of_fine (h:FineMomentInput):ChosenMomentInput:=by
  intro hβ
  obtain ⟨mesh,hmesh,hmom⟩:=h hβ
  obtain ⟨D,hD⟩:=exists_high_data_fine (HeckeZeroSupremum.beta-7/8) (by linarith) mesh hmesh
  obtain ⟨F⟩:=exists_source_data D
  obtain ⟨counts⟩:=source_count_parameters F
  exact ⟨D,F,counts,hmom D hD F counts⟩

theorem chosen_data_height {Δ:ℝ}(D:HighData Δ)(F:SourceData D)
    (counts:CountParameters F.modulus ⊤ D.t)(J:ℝ)(hJ:0≤ J)
    (hbound:∀η:Character,∃C:ℝ,0< C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))):
    ∃τ:ℝ,0<τ ∧ τ<(1/200:ℝ)/2 ∧ 4*τ<(1/200)*D.cost ∧ τ< D.t ∧
      2*τ≤ D.t ∧ τ*(2+4*D.eps)< D.t ∧
      ∀η:Character,∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*Z^D.t) (Z^(2*τ)):=by
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτJ,hτeps⟩:=D.height_choice J hJ
  have htau1:τ≤1:=by linarith
  refine ⟨τ,hτ,hτd,hτcost,hτt,by nlinarith,hτeps,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩:=hbound η
  refine ⟨C*2^J,by positivity,?_⟩
  filter_upwards [hbound τ hτ htau1,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  exact hb.mono_constant (by linarith)
    (polynomial_height_absorption C Z τ J D.t hC.le hZ hτ.le hJ (by linarith))

theorem common_probe_of_chosen_moments (hmom : ChosenMomentInput) : HeckeCommonProbe.UniformCommonProbe := by
  intro hβ
  obtain ⟨D,F,counts,J,hJ,hmom⟩:=hmom hβ
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτ2,hτeps,hsource⟩ := chosen_data_height D F counts J hJ hmom
  obtain ⟨C,hC,hhigh⟩ := fixed_high_bound hβ D F counts τ hτ hτd hτcost hτt hτ2 hτeps
  let loss := (HeckeZeroSupremum.beta-7/8)/2
  have hloss : 0< loss := by dsimp [loss];linarith
  have hlossgap : loss< HeckeZeroSupremum.beta-7/8 := by dsimp [loss];linarith
  refine ⟨loss,D.sigma,hloss,hlossgap,D.sigma_pos,?_⟩
  intro η hprimitive
  obtain ⟨hmask,hH,hHbound⟩ := actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,F.probe η,
    hmask,hH,hHbound,F.probe_low loss hloss η,?_⟩
  obtain ⟨Ct,hCt,hhigh⟩ := hhigh η
  obtain ⟨Cm,hCm,hsource⟩ := hsource η
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct+C*Cm*(η.modulus.absNorm:ℝ)^(2*D.eps),by positivity,?_⟩
  filter_upwards [hhigh,hsource] with Z hh hs
  exact hh Cm hCm.le hs

theorem dirichlet_of_chosen_moments (hmom : ChosenMomentInput) (q : ℕ) (hq : q≠0)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : (7/8:ℝ)< s.re)
    (hexc : ¬(χ=1 ∧ s=1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s≠0 :=
  HeckeCommonProbe.dirichlet_of_common_probe (common_probe_of_chosen_moments hmom) q hq χ s hs hexc

theorem zeta_of_chosen_moments (hmom : ChosenMomentInput) (s : ℂ) (hs : (7/8:ℝ)< s.re) :
    riemannZeta s≠0 :=
  HeckeCommonProbe.zeta_of_common_probe (common_probe_of_chosen_moments hmom) s hs

theorem hecke_of_chosen_moments (hmom : ChosenMomentInput) (χ : Character) (s : ℂ)
    (hs : (7/8:ℝ)< s.re) (hpole : s≠1 ∨ χ.residue≠1) : LFunction χ s≠0 :=
  HeckeCommonProbe.hecke_ne_zero_of_common_probe (common_probe_of_chosen_moments hmom) χ s hs hpole

end SevenEighths.ProbeFinalAssembly

end

end OAI
end
/- END ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblyChosenData -/

/- BEGIN ORIGINAL MODULE Analytic.ActualRawDensity ; sha256 eb6d1db4b6480dd439a7d666b5d508fc3fd30df4e22b806373a9aec9c7df2fc5 -/
section



set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros HeckeFiniteDeletion
open ProbeHighRowFamily LocalMoment ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource
local notation "O" => HeckeFamily.O

/-- A complete zero bin. Its lower boundary lies in the local density range. -/
structure DensityWindow where
  lower : ℝ
  upper : ℝ
  height : ℝ
  lower_bound : 167/200 ≤ lower
  upper_bound : lower ≤ 7/8

lemma densityWindow_exponent_bounds (p : DensityWindow) (loss : ℝ) (hloss : 0 ≤ loss) :
    2/7 ≤ unmarkedDensity (2*p.lower-1)+loss ∧
      unmarkedDensity (2*p.lower-1)+loss ≤ 1+loss := by
  have hg := unmarkedDensity_ge_two_sevenths (δ := 2*p.lower-1) (by linarith [p.upper_bound])
  have hp : 0 ≤ 10*(2*p.lower-1)/(3*(5-2*(2*p.lower-1))) :=
    div_nonneg (by linarith [p.lower_bound]) (by linarith [p.upper_bound])
  constructor
  · linarith
  · unfold unmarkedDensity
    linarith

/-- The conductor-bounded representative has a literal mask of the fixed
moment dictionary. Consequently it has exactly the same positive zeros. -/
lemma natural_momentData_mask (η : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff (naturalRow η u.val u.property.1).character I =
      if IsCoprime I (naturalRow η u.val u.property.1).character.modulus then
        idealCoeff ((momentData η).character ⟨u.val, u.property.1⟩) I else 0 := by
  have he := natural_row_moment_dictionary η u I
  calc
    _ = if IsCoprime I (naturalRow η u.val u.property.1).character.modulus then
      idealCoeff (naturalRow η u.val u.property.1).character I else 0 :=
        idealCoeff_source_mask _ I
    _ = _ := by rw [he]; rfl

theorem actual_momentData_free_density_eventually {Label : Type*} [Fintype Label]
    (η : Label → Character) (Q : Ideal O) [NeZero Q]
    (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hQη : ∀ label, Q ≤ (η label).modulus)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (hβupper : HeckeZeroSupremum.beta ≤ 7/8)
    (loss : ℝ) (hlosspos : 0 < loss) :
    ∃ (A : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ Y : ℝ in atTop,
      ∀ p : DensityWindow, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ rawZeroBin (fun j => momentData (η j))
        p.lower p.upper p.height ⟨u.val, u.property.1⟩) →
      (F.card : ℝ) ≤ K*(1+|p.height|)^A*Y^(unmarkedDensity (2*p.lower-1)+loss) := by
  obtain ⟨A, K, hK, hfree⟩ := actual_free_density_eventually
    η Q hQtop hQ72 hQη hβ M H hH S φ hφ hφc hφp hφ0 hφne
    a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper loss hlosspos
  let L : ℝ := max 1 (∑ j : Label, ((η j).modulus.absNorm : ℝ)*(fixedConductorFactor : ℝ))
  have hL : 1 ≤ L := le_max_left _ _
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hLj (j : Label) : ((η j).modulus.absNorm : ℝ)*(fixedConductorFactor : ℝ) ≤ L := by
    apply le_trans _ (le_max_right _ _)
    exact Finset.single_le_sum (f := fun j : Label =>
      ((η j).modulus.absNorm : ℝ)*(fixedConductorFactor : ℝ))
      (fun j _ => by positivity) (Finset.mem_univ j)
  have hscale : Tendsto (fun Y : ℝ => L*Y) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hLpos).2 tendsto_id
  refine ⟨A, K*L^(1+loss), mul_pos hK (Real.rpow_pos_of_pos hLpos _), ?_⟩
  filter_upwards [hscale.eventually hfree, eventually_ge_atTop (1 : ℝ)] with Y hb hY
  intro p F hF
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  have hρ := densityWindow_exponent_bounds p loss hlosspos.le
  have hw : 0 ≤ (1+|p.height|)^A := by positivity
  by_cases hne : F.Nonempty
  · let family : F → Label → Character := fun u j =>
      (naturalRow (η j) u.val.val u.val.property.1).character
    have hn : ∀ u j, (family u j).residue ≠ 1 := by
      intro u j hprin
      obtain ⟨hn, _, _⟩ := (hF u.val u.property).2
      exact hn j ((principal_iff_of_mask (family u j)
        ((momentData (η j)).character ⟨u.val.val, u.val.property.1⟩)
        (natural_momentData_mask (η j) u.val)).mp hprin)
    obtain ⟨χ, hχ, hext⟩ := extend_nonprincipal_supported_family F hne family hn
    have hext' (u : F) : χ u.val = family u := funext (hext u)
    have hnorm : ∀ u ∈ F, rowNorm u ≤ L*Y := by
      intro u hu
      exact (hF u hu).1.trans (le_mul_of_one_le_left hYpos.le hL)
    have hcoeff : ∀ u ∈ F, ∀ j I,
        idealCoeff (χ u j) I =
          if (false : Bool) then starRingEnd ℂ (idealCoeff ((momentData (η j)).character
            ⟨u.val, u.property.1⟩) I)
          else idealCoeff ((momentData (η j)).character ⟨u.val, u.property.1⟩) I := by
      intro u hu j I
      rw [hext ⟨u, hu⟩ j]
      simpa [family, momentElement] using natural_row_moment_dictionary (η j) u I
    have hcond : ∀ u ∈ F, ∀ j, ((χ u j).modulus.absNorm : ℝ) ≤ L*Y := by
      intro u hu j
      rw [hext ⟨u, hu⟩ j]
      have hn := (naturalRow (η j) u.val u.property.1).natural_modulus_bound
      have hn' : ((family ⟨u, hu⟩ j).modulus.absNorm : ℝ) ≤
          ((η j).modulus.absNorm : ℝ)*(fixedConductorFactor : ℝ)*rowNorm u := by
        dsimp [family, rowNorm]
        exact_mod_cast hn
      exact hn'.trans (mul_le_mul (hLj j) (hF u hu).1 (zero_le_one.trans (rowNorm_ge_one u)) hLpos.le)
    have hstart : ∀ u ∈ F, p.lower ≤ zeroMaximum (χ u) (hχ u) p.height := by
      intro u hu
      obtain ⟨hnraw, hlo, hhi⟩ := (hF u hu).2
      have heq := zeroMaximum_eq_of_mask (family ⟨u, hu⟩)
        (fun j => (momentData (η j)).character ⟨u.val, u.property.1⟩)
        (hn ⟨u, hu⟩) hnraw p.height (fun j => natural_momentData_mask (η j) u)
      have hs : p.lower ≤ zeroMaximum (family ⟨u, hu⟩) (hn ⟨u, hu⟩) p.height := by
        rw [heq]
        exact hlo
      simpa only [hext' ⟨u, hu⟩] using hs
    have hc := hb.2 F χ (fun _ => false) hχ hnorm hcoeff hcond
      p.lower p.height p.lower_bound p.upper_bound hstart
    have hp : L^(unmarkedDensity (2*p.lower-1)+loss) ≤ L^(1+loss) :=
      Real.rpow_le_rpow_of_exponent_le hL hρ.2
    calc
      (F.card : ℝ) ≤ K*(1+|p.height|)^A*(L*Y)^(unmarkedDensity (2*p.lower-1)+loss) := hc
      _ = K*(1+|p.height|)^A*L^(unmarkedDensity (2*p.lower-1)+loss)*
          Y^(unmarkedDensity (2*p.lower-1)+loss) := by rw [Real.mul_rpow hLpos.le hYpos.le]; ring
      _ ≤ K*(1+|p.height|)^A*L^(1+loss)*Y^(unmarkedDensity (2*p.lower-1)+loss) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (mul_nonneg hK.le hw)) (by positivity)
      _ = (K*L^(1+loss))*(1+|p.height|)^A*Y^(unmarkedDensity (2*p.lower-1)+loss) := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

/-- Polynomial height density on every bounded free-row window and on
all raw integer rows. Both conclusions use the literal fixed moment
family and complete actual zero bins. No moment or density estimate is
an input to this theorem. -/
theorem actual_momentData_density {Label : Type*} [Fintype Label]
    (η : Label → Character) (Q : Ideal O) [NeZero Q]
    (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hQη : ∀ label, Q ≤ (η label).modulus)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (hβupper : HeckeZeroSupremum.beta ≤ 7/8)
    (loss : ℝ) (hlosspos : 0 < loss) :
    ∃ (A : ℕ) (K : ℝ), 0 < K ∧
      (∀ Y : ℝ, 1 ≤ Y → ∀ p : DensityWindow, ∀ F : Finset FreeRow,
        (∀ u ∈ F, rowNorm u ≤ Y ∧ rawZeroBin (fun j => momentData (η j))
          p.lower p.upper p.height ⟨u.val, u.property.1⟩) →
        (F.card : ℝ) ≤ K*(1+|p.height|)^A*Y^(unmarkedDensity (2*p.lower-1)+loss)) ∧
      (∀ p : DensityWindow, ∀ Y : ℝ, 0 < Y →
        ∀ R : Finset ProbePhysical.NonzeroFrequency,
        (∀ u ∈ R, rawFrequencyNorm u ≤ Y ∧ rawZeroBin (fun j => momentData (η j))
          p.lower p.upper p.height u) →
        (R.card : ℝ) ≤ K*(1+|p.height|)^A*Y^(unmarkedDensity (2*p.lower-1)+loss)) := by
  obtain ⟨A, C, hC, hevent⟩ := actual_momentData_free_density_eventually
    η Q hQtop hQ72 hQη hβ M H hH S φ hφ hφc hφp hφ0 hφne
    a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper loss hlosspos
  let weight : DensityWindow → ℝ := fun p => (1+|p.height|)^A
  let ρ : DensityWindow → ℝ := fun p => unmarkedDensity (2*p.lower-1)+loss
  let P : DensityWindow → FreeRow → Prop := fun p u =>
    rawZeroBin (fun j => momentData (η j)) p.lower p.upper p.height ⟨u.val, u.property.1⟩
  have hw (p : DensityWindow) : 1 ≤ weight p := one_le_pow₀ (by linarith [abs_nonneg p.height])
  have hρ (p : DensityWindow) : 2/7 ≤ ρ p := (densityWindow_exponent_bounds p loss hlosspos.le).1
  obtain ⟨Kf, hKf, _, hfree⟩ := uniform_free_density_weighted_of_eventually
    P C ρ weight (fun p => by linarith [hρ p]) hw hevent
  obtain ⟨Kr, hKr, hraw⟩ := raw_density_weighted_from_eventual_free
    (fun (_p : DensityWindow) j => momentData (η j))
    (fun p => p.lower) (fun p => p.upper) (fun p => p.height) weight ρ C (2/7)
    (by norm_num) hρ hw hevent
  refine ⟨A, max Kf Kr, lt_of_lt_of_le hKf (le_max_left _ _), ?_, ?_⟩
  · intro Y hY p F hF
    apply (hfree Y hY p F hF).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le_one.trans (hw p)))
      (Real.rpow_nonneg (zero_le_one.trans hY) _)
  · intro p Y hY R hR
    apply (hraw p Y hY R hR).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans (hw p)))
      (Real.rpow_nonneg hY.le _)

#print axioms actual_momentData_free_density_eventually
#print axioms actual_momentData_density
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualRawDensity -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentExceptionalMass ; sha256 b728a0d4de9957b1ee330d9812d8629d3a8057fe976c5e674bf6f5ecc26fea47 -/
section




/-! The actual coherent second support sum is seeded by the first
projector. Its radical weight pays all second common and dyadic labels. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondBlockRadicalHarmonicMass CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondBlockAggregate CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O

theorem actual_common_second_radical_mass (B L Cr ε : ℝ)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hCr : 0 < Cr) (hε : 0 < ε) :
    ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop,
      ∀ {ι : Type*} [Fintype ι] (src : Input ι) (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁),
      Squarefree L₁ → L₁ ≠ 0 → src.W₁ 0 = 0 → src.W₂ 0 = 0 →
      sourceRadius src/(C₁.absNorm : ℝ) ≤ Z^B →
      ∀ K Radius Hsource : ℝ, 0 < K → Radius ≤ Cr*Z^L → Hsource ≤ Z^B →
      (∑ q : ActiveBlocks (commonSecondColumns (original src R seed) C₁ hC₁)
        (commonSecondBeta (original src R seed) C₁ L₁) K Radius Hsource,
        radicalWeight q.1.1.val.1 q.1.1.val.2) ≤ Cbound*Z^ε/(L₁.absNorm : ℝ) := by
  obtain ⟨Cbound,hCbound,hbound⟩ := actual_block_radical_mass B L Cr ε hB hL hCr hε
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hbound] with Z hZ
  intro ι instF src R seed C₁ L₁ hC₁ hL₁ hL₁0 hz₁ hz₂ hsource K Radius Hsource hK hRadius hH
  apply hZ L₁ hL₁ hL₁0 _ _ _ _ K Radius Hsource hK hRadius hH
  · intro I hI hβ
    by_contra hd
    exact hβ (by simp only [commonSecondBeta,hd,and_false,ite_false])
  · intro I hI hβ
    exact (commonSecond_source_norm_cap (original src R seed) C₁ L₁ hC₁ (sourceRadius src)
      (fun J _ hJ => (original_column_norm src R seed J hz₁ hz₂ hJ).2) I hI hβ).trans hsource

#print axioms actual_common_second_radical_mass
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentExceptionalMass -/

/- BEGIN ORIGINAL MODULE Analytic.JointCommonErrorExtraction ; sha256 133988f67f74cc458bd9126565c5e8492f18cb08c6a88f7bfa533ab50a5a2c71 -/
section




/-! Uniform genuine error families for arbitrary surviving slot sets. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentAmplificationEnergy
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationRadicalChoice CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentGaussNormalization CenteredMomentFirstAnnularInput
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows CenteredMomentHeckeExpansion RayFourExpansion
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance commonErrorExtractionDecEq : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

/-- Prime separation and actual radical extraction give the whole dyadic
error sum. The family is chosen before the input and its heights. -/
theorem exists_input_common_error_families
    (P : Finset (Ideal O)) (hP : ∀ Q ∈ P, Prime Q)
    (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (Z sigma b eta delta reserve : ℝ) (hZ : 1 < Z) (hsigma : 0 ≤ sigma)
    (hb : 0 ≤ b) (hsep : b*Z^eta < Z^(sigma/6))
    (hpl : ∀ Q ∈ P, Z^(sigma/6) ≤ (Q.absNorm : ℝ))
    (hdelta : 0 ≤ delta) (hreserve : 2 ≤ Z^reserve) :
    ∃ τ : Character → elementPool P → Fin 3 → RayCharacter → Character,
      (∀ η (p : elementPool P) i χ, ((τ η p i χ).modulus.absNorm : ℝ) ≤
        radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
      ∀ (s : Input ι), (∀ i, Function.support (s.W i) ⊆ Set.Iic b) →
      ∀ (z : ι → ℝ), (∀ i, z i ≤ eta) → (∀ i, s.P i = Z^(z i)) →
      ∀ (R seed : Ideal O) (d K₀ c : ℝ) (j : ℤ),
        Real.logb Z (dyadicScale j) ≤ K₀+delta →
        (∑ p ∈ elementPool P, ∑ h ∈ (dyadRows j).filter (fun h => eligible R seed h p),
          errorEnergy Finset.univ (sourceGenerator (original s R seed).columns)
            (sourceGenerator_supported (original s R seed).columns)
            ((original s R seed).coefficient s.η fixedBadMask s.t (volume s)) h p) ≤
          ∑ p : elementPool P,
            firstExtractedErrors s R seed Z d K₀ c sigma delta reserve p (τ s.η p) := by
  have hf (η : Character) := CenteredMomentAmplificationRadicalChoice.exists_pool_error_families (ι := ι) P hP hbad η fixedBadMask
    fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
  choose τ hτ herr using hf
  refine ⟨τ,?_,?_⟩
  · intro η p i χ
    exact_mod_cast hτ η p i χ
  · intro s hsupp z hz hlen R seed d K₀ c j hj
    have hcop (p : O) (hp : p ∈ elementPool P) :
        ∀ i, ∀ Q ∈ (original s R seed).active.S (Sum.inl i), IsCoprime (Ideal.span {p}) Q := by
      have hd := elementPool_data P hP hbad p hp
      exact original_slot_coprime (original s R seed).active Z sigma b eta hZ.le hb hsep
        z hz hlen hsupp (original s R seed).active_slot
        (fun i Q hQ => s.prime i Q ((original s R seed).active_subset _ hQ))
        (Ideal.span {p}) (hP _ hd.2.1) (hpl _ hd.2.1)
    have he := herr s.η (original s R seed).active
      (fun i I hI => s.pools_ne i I ((original s R seed).active_subset i hI))
      (fun i I hI => s.prime i I ((original s R seed).active_subset _ hI))
      hcop s.t (volume s) Z sigma (d+K₀-Real.logb Z (dyadicScale j)) c
      (volume_pos s) hZ hsigma j
    simp only [OriginalData.active_errorEnergy] at he
    apply he.trans
    apply Finset.sum_le_sum
    intro p _
    unfold firstExtractedErrors
    apply Finset.sum_le_sum
    intro i _
    apply (child_energy_common (original s R seed).active (τ s.η p i) p (errorIndex i)
      s.t (volume s) Z d K₀ (Real.logb Z (dyadicScale j)) c sigma delta reserve
      (volume_pos s).le hZ hdelta hj hreserve).trans_eq
    rw [←original_active]
    have hd := elementPool_data P hP hbad p.val p.property
    exact original_childEnergy_eq_inputs (activeInput s) R seed (τ s.η p i) p.val hd.1.ne_zero
      (hcop p.val p.property) (errorIndex i) s.t _

#print axioms exists_input_common_error_families
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCommonErrorExtraction -/

/- BEGIN ORIGINAL MODULE Analytic.JointReconstruction ; sha256 7b34d8940f0379740851b0e857771b85223b0ed99bbb7a477d82f261b7faea55 -/
section


/-! The actual dependent arithmetic labels, with a concrete reconstruction
code. On a fixed joint row the code determines the residual frequency h. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonical CenteredMomentRankinRadical
open IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

structure JointReconstructionLabel where
  C₁ : Ideal O
  D₁ : Ideal O
  C₂ : Ideal O
  D₂ : Ideal O
  E : Finset (CommonIndex C₁ D₁)
  U : Finset (CommonIndex C₂ D₂)
  L : Ideal O
  h : O

def JointReconstructionLabel.row (u : Oˣ) (v : JointReconstructionLabel) : O :=
  jointLeftRow v.C₁ v.D₁ v.C₂ v.D₂ v.E u v.U v.h

def JointReconstructionLabel.code (v : JointReconstructionLabel) : JointArithmeticCode :=
  ((v.C₁, v.D₁), ((v.C₂, v.D₂),
    (v.E.image Subtype.val, (v.U.image Subtype.val, primeSupport v.L))))

/-- The full arithmetic code is injective on a fixed actual row. In particular
there is no independent count of the residual second frequency. -/
theorem joint_reconstruction_injective (u : Oˣ) (v v' : JointReconstructionLabel)
    (hC₁ : Supported v.C₁) (hC₂ : Supported v.C₂)
    (hL : Squarefree v.L) (hL' : Squarefree v'.L)
    (hrow : v.row u = v'.row u) (hcode : v.code = v'.code) : v = v' := by
  cases v with
  | mk C₁ D₁ C₂ D₂ E U L h =>
    cases v' with
    | mk C₁' D₁' C₂' D₂' E' U' L' h' =>
      simp only [JointReconstructionLabel.code, Prod.mk.injEq] at hcode
      obtain ⟨⟨rfl, rfl⟩, ⟨⟨rfl, rfl⟩, hE, hU, hLL⟩⟩ := hcode
      change Squarefree L at hL
      change Squarefree L' at hL'
      have hEE : E = E' := Finset.image_injective Subtype.val_injective hE
      have hUU : U = U' := Finset.image_injective Subtype.val_injective hU
      have hLL' : L = L' := by
        rw [← squarefree_support_product_self hL, ← squarefree_support_product_self hL', hLL]
      subst E'
      subst U'
      subst L'
      have hh : h = h' := jointLeftRow_injective C₁ D₁ C₂ D₂ hC₁ hC₂ E u U hrow
      subst h'
      rfl

theorem joint_subset_code_support (C D : Ideal O) (E : Finset (CommonIndex C D)) :
    E.image Subtype.val ⊆ primeSupport C := by
  intro P hP
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
  exact (Finset.mem_inter.mp p.property).1

/-- All five discrete pieces of the reconstruction code are supported on
Rmiss·(w). This includes the first projector and excludes the second one. -/
theorem joint_reconstruction_code_support (u : Oˣ) (v : JointReconstructionLabel)
    (hC₂ : Supported v.C₂)
    (hCD₁ : primeSupport v.C₁ = primeSupport v.D₁)
    (hCD₂ : primeSupport v.C₂ = primeSupport v.D₂)
    (_hL : Squarefree v.L) (hLC₂ : v.L ∣ v.C₂) (_hLD₂ : v.L ∣ v.D₂)
    (hw : v.row u ≠ 0) :
    let Q := jointMissingRadical v.C₁ (v.row u) * Ideal.span {v.row u}
    primeSupport v.C₁ ⊆ primeSupport Q ∧
      primeSupport v.D₁ ⊆ primeSupport Q ∧
      primeSupport v.C₂ ⊆ primeSupport Q ∧
      primeSupport v.D₂ ⊆ primeSupport Q ∧
      v.E.image Subtype.val ⊆ primeSupport Q ∧
      v.U.image Subtype.val ⊆ primeSupport Q ∧
      primeSupport v.L ⊆ primeSupport Q := by
  dsimp only
  have hwI : Ideal.span {v.row u} ≠ (0 : Ideal O) := by simpa using hw
  have hQ := mul_ne_zero (jointMissingRadical_ne_zero v.C₁ (v.row u)) hwI
  have hrowQ := joint_primeSupport_mono hQ (dvd_mul_left (Ideal.span {v.row u})
    (jointMissingRadical v.C₁ (v.row u)))
  have hfirst := joint_first_support v.C₁ v.D₁ (v.row u) hw hCD₁
  have hsecond := joint_second_support v.C₁ v.D₁ v.C₂ v.D₂ hC₂ hCD₂ v.E u v.U v.h hw
  have hC := hsecond.1.trans hrowQ
  have hD := hsecond.2.trans hrowQ
  have hLQ : primeSupport v.L ⊆
      primeSupport (jointMissingRadical v.C₁ (v.row u) * Ideal.span {v.row u}) :=
    (joint_primeSupport_mono hC₂.1 hLC₂).trans hC
  exact ⟨hfirst.1, hfirst.2, hC, hD,
    (joint_subset_code_support v.C₁ v.D₁ v.E).trans hfirst.1,
    (joint_subset_code_support v.C₂ v.D₂ v.U).trans hC, hLQ⟩

/-- A concrete fixed-(w,Rmiss,u) reconstruction fiber has arbitrarily small
power cost in the four common-label norms and in N(Rmiss·(w)). -/
theorem joint_reconstruction_fiber_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (u : Oˣ) (w : O), w ≠ 0 →
      ∀ (R : Ideal O), R ≠ 0 → ∀ S : Finset JointReconstructionLabel,
      (∀ v ∈ S, Supported v.C₁ ∧ Supported v.D₁ ∧ Supported v.C₂ ∧ Supported v.D₂) →
      (∀ v ∈ S, primeSupport v.C₁ = primeSupport v.D₁ ∧
        primeSupport v.C₂ = primeSupport v.D₂) →
      (∀ v ∈ S, Squarefree v.L ∧ v.L ∣ v.C₂ ∧ v.L ∣ v.D₂) →
      (∀ v ∈ S, v.row u = w ∧ jointMissingRadical v.C₁ w = R) →
      ∀ X₁ Y₁ X₂ Y₂ : ℝ, 0 < X₁ → 0 < Y₁ → 0 < X₂ → 0 < Y₂ →
      (∀ v ∈ S, (Ideal.absNorm v.C₁ : ℝ) ≤ X₁ ∧
        (Ideal.absNorm v.D₁ : ℝ) ≤ Y₁ ∧
        (Ideal.absNorm v.C₂ : ℝ) ≤ X₂ ∧
        (Ideal.absNorm v.D₂ : ℝ) ≤ Y₂) →
      (S.card : ℝ) ≤ K * X₁^a * Y₁^a * X₂^a * Y₂^a *
        (Ideal.absNorm (R * Ideal.span {w}) : ℝ)^(5*ε) := by
  obtain ⟨K, hK, hcount⟩ := joint_arithmetic_fiber_count a ε ha hε
  refine ⟨K, hK, ?_⟩
  intro u w hw R hR S hsup heq hproj hrow X₁ Y₁ X₂ Y₂ hX₁ hY₁ hX₂ hY₂ hnorm
  have hQ : R * Ideal.span {w} ≠ (0 : Ideal O) := mul_ne_zero hR (by simpa using hw)
  have hinj : Set.InjOn JointReconstructionLabel.code (↑S : Set JointReconstructionLabel) := by
    intro v hv v' hv' hcode
    exact joint_reconstruction_injective u v v' (hsup v hv).1 (hsup v hv).2.2.1
      (hproj v hv).1 (hproj v' hv').1 ((hrow v hv).1.trans (hrow v' hv').1.symm) hcode
  have hcard := Finset.card_image_iff.mpr hinj
  rw [← hcard]
  apply hcount (R * Ideal.span {w}) hQ (S.image JointReconstructionLabel.code)
  · intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨(hsup v hv).1.1, (hsup v hv).2.1.1,
      (hsup v hv).2.2.1.1, (hsup v hv).2.2.2.1⟩
  · intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    have hh := joint_reconstruction_code_support u v (hsup v hv).2.2.1
      (heq v hv).1 (heq v hv).2 (hproj v hv).1 (hproj v hv).2.1 (hproj v hv).2.2
      ((hrow v hv).1 ▸ hw)
    dsimp only at hh
    rw [(hrow v hv).1, (hrow v hv).2] at hh
    exact hh
  · exact hX₁
  · exact hY₁
  · exact hX₂
  · exact hY₂
  · intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact hnorm v hv

#print axioms joint_reconstruction_injective
#print axioms joint_reconstruction_fiber_count
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointReconstruction -/

/- BEGIN ORIGINAL MODULE Analytic.JointSourceLowerSupport ; sha256 099f1d9352d08db9b1e3b7ae8a24fe6078b771c751d8cd84fbc4fe4a89a82d99 -/
section






/-! Original lower profile supports give an actual residual-column lower
bound. A nonzero physical block then supplies both cumulative lower dyads. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceLowerSupport
open CenteredMomentSourceBlockWindows CenteredMomentSecondPhysicalBlock
open CenteredMomentSectorLocalization CenteredMomentFiniteProfileExceptional
open CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance sourceLowerSumDecidableEq : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def originalLowerProfile (s : Input ι) (a₁ a₂ : ℝ) : ℝ :=
  (∏ i,s.lo i)*a₁*a₂

lemma originalLowerProfile_pos (s : Input ι) (a₁ a₂ : ℝ)
    (h₁ : 0 < a₁) (h₂ : 0 < a₂) : 0 < originalLowerProfile s a₁ a₂ :=
  mul_pos (mul_pos (Finset.prod_pos (fun i _ => s.lo_pos i)) h₁) h₂

theorem original_column_lower (s : Input ι) (R seed I : Ideal O) (a₁ a₂ : ℝ)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (h₁ : ∀ x,s.W₁ x ≠ 0 → a₁ ≤ x) (h₂ : ∀ x,s.W₂ x ≠ 0 → a₂ ≤ x)
    (hne : (original s R seed).beta I ≠ 0) :
    originalLowerProfile s a₁ a₂*CenteredMomentExceptionalAmplitudePair.volume s.toData ≤
      (I.absNorm : ℝ) := by
  have hh := profile_column_lower R s.ν s.W s.P s.lo s.W₁ s.W₂ a₁ a₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos (fun i => (s.lo_pos i).le)
    ha₁ ha₂ s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero
    rfl s.same_product (fun i x hx => (s.support i hx).1) h₁ h₂
    (Fintype.piFinset s.pools) I hne
  simpa only [originalLowerProfile,CenteredMomentExceptionalAmplitudePair.volume,
    map_one,Nat.cast_one,mul_one,div_one,mul_assoc] using hh

theorem common_second_column_lower (s : Input ι) (R seed C L : Ideal O)
    (hC : C ≠ 0) (a₁ a₂ : ℝ) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (h₁ : ∀ x,s.W₁ x ≠ 0 → a₁ ≤ x) (h₂ : ∀ x,s.W₂ x ≠ 0 → a₂ ≤ x) :
    ∀ I : Ideal O,commonSecondBeta (original s R seed) C L I ≠ 0 →
      originalLowerProfile s a₁ a₂*
        (CenteredMomentExceptionalAmplitudePair.volume s.toData/(C.absNorm : ℝ)) ≤ (I.absNorm : ℝ) := by
  intro I hne
  have hβ : (original s R seed).beta (C*I) ≠ 0 := by
    intro hz
    simp only [commonSecondBeta,hz,ite_self] at hne
    exact hne rfl
  have hNC : (0 : ℝ) < C.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hh := original_column_lower s R seed (C*I) a₁ a₂ ha₁ ha₂ h₁ h₂ hβ
  rw [←mul_div_assoc]
  apply (div_le_iff₀ hNC).mpr
  simpa only [map_mul,Nat.cast_mul,mul_comm] using hh

theorem common_second_column_lower_profiles (s : Input ι) (R seed C L : Ideal O)
    (hC : C ≠ 0) (a b : ℝ) (ha : 0 < a) (p : Profiles a b)
    (h₁ : p.profile 0 = s.W₁) (h₂ : p.profile 1 = s.W₂) :
    ∀ I : Ideal O,commonSecondBeta (original s R seed) C L I ≠ 0 →
      originalLowerProfile s a a*
        (CenteredMomentExceptionalAmplitudePair.volume s.toData/(C.absNorm : ℝ)) ≤ (I.absNorm : ℝ) := by
  apply common_second_column_lower s R seed C L hC a a ha.le ha.le
  · intro x hx
    exact (p.support 0 (by simpa only [h₁,Function.mem_support] using hx)).1
  · intro x hx
    exact (p.support 1 (by simpa only [h₂,Function.mem_support] using hx)).1

theorem actual_common_physical_lower_dyads (s : Input ι) (R seed C₀ L : Ideal O)
    (hC₀ : C₀ ≠ 0) (a b : ℝ) (ha : 0 < a) (p : Profiles a b)
    (h₁ : p.profile 0 = s.W₁) (h₂ : p.profile 1 = s.W₂)
    (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (Radius : ℝ) (rows : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4 → ℤ)
    (hne : physicalBlock η t S (commonSecondBeta (original s R seed) C₀ L)
      C D hC hD U Radius rows W K n ≠ 0) :
    originalLowerProfile s a a*CenteredMomentExceptionalAmplitudePair.volume s.toData/
      ((C₀*C).absNorm : ℝ) ≤ dyadicScale (n 2) ∧
    originalLowerProfile s a a*CenteredMomentExceptionalAmplitudePair.volume s.toData/
      ((C₀*D).absNorm : ℝ) ≤ dyadicScale (n 3) := by
  have haSource := originalLowerProfile_pos s a a ha ha
  have hwin := physicalBlock_scale_lower η t S (commonSecondBeta (original s R seed) C₀ L)
    C D hC hD U Radius rows W K n (originalLowerProfile s a a)
    (CenteredMomentExceptionalAmplitudePair.volume s.toData/(C₀.absNorm : ℝ)) haSource
    (common_second_column_lower_profiles s R seed C₀ L hC₀ a b ha p h₁ h₂) hne
  constructor
  · have hh := (le_div_iff₀ haSource).mp hwin.1
    convert hh using 1
    simp only [map_mul,Nat.cast_mul]
    field_simp
    <;> ring
  · have hh := (le_div_iff₀ haSource).mp hwin.2
    convert hh using 1
    simp only [map_mul,Nat.cast_mul]
    field_simp
    <;> ring

#print axioms common_second_column_lower_profiles
#print axioms actual_common_physical_lower_dyads
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSourceLowerSupport -/
