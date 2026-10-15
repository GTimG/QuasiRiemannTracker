/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B002
import Submissions.local44_20261013.Bundles.B007
import Submissions.local44_20261013.Bundles.B008
import Submissions.local44_20261013.Bundles.B009
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorMomentFiberGates
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorMomentPrimeGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.RayPoolDisjoint
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorAmplitudeFirst
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialPhysicalSlots

/- BEGIN ORIGINAL MODULE Analytic.JointFirstVariableWindow ; sha256 e4dc8ce355035feac25af8268657ac055700dfc82055639b6f223563c59e4c52 -/
section


/-! Joint Fourier windows with a separate finite row set for each label. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentFirstColumns
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open CenteredMomentSmooth CenteredMomentConjugateWindow
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem joint_label_variable_row_subtype_sum {Λ : Type*} [DecidableEq Λ]
    (labels : Finset Λ) (rows : Λ → Finset O) (f : Λ → O → ℝ) :
    (∑ q : (l : ↥labels) × ↥(rows l), f q.1 q.2) = ∑ l ∈ labels, ∑ z ∈ rows l, f l z := by
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ l : ↥labels, ∑ z ∈ rows l, f l z :=
      Finset.sum_congr rfl (fun l _ => Finset.sum_coe_sort (rows l) (fun z => f l z))
    _ = _ := Finset.sum_coe_sort labels (fun l => ∑ z ∈ rows l, f l z)

theorem joint_first_variable_left_window_energy {Λ : Type*} [DecidableEq Λ]
    (labels : Finset Λ) (rows : Λ → Finset O) (s : Λ → FirstJointLabel ι)
    (t X : Λ → ℝ) (hX : ∀ l ∈ labels, 0 < X l) (θ : ℝ)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (U : Λ → 𝓢(ℝ, ℂ)) (K : Λ → ℝ)
    (hK : ∀ l ∈ labels, 0 < K l)
    (hU : ∀ l ∈ labels, ∀ z : O, 0 ≤ (U l (‖eisEmbedding z‖^2 / K l)).re)
    (hmajor : ∀ l ∈ labels, ∀ z ∈ rows l,
      1 ≤ (U l (‖eisEmbedding z‖^2 / K l)).re)
    (J : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (henergy : ∀ w : ℝ, (∑ l ∈ labels,
      (s l).leftEnergy (t l+2*Real.pi*(w-θ)) (U l) (K l)) ≤
        E*(1+‖w‖)^(2*J)) :
    (∑ l ∈ labels, ∑ z ∈ rows l, ‖(s l).leftWindowValue (t l) θ (X l) V z‖^2) ≤
      E*(∫ w : ℝ, (1+‖w‖)^J * ‖columnDensity V hVc hVs w‖)^2 := by
  let φ : ((l : ↥labels) × ↥(rows l)) → ℝ → ℂ := fun q w =>
    logPhase (θ-w) (Real.log (X q.1)) *
      (s q.1).leftValue (t q.1+2*Real.pi*(w-θ)) q.2
  have hi (q : (l : ↥labels) × ↥(rows l)) :
      Integrable (fun w => columnDensity V hVc hVs w * φ q w) := by
    simpa only [φ, mul_assoc] using (s q.1).left_window_integrable
      (t q.1) θ (X q.1) (hX q.1 q.1.property) V hVc hVs q.2
  have he (w : ℝ) : (∑ q : (l : ↥labels) × ↥(rows l), ‖φ q w‖^2) ≤ E*((1+‖w‖)^J)^2 := by
    simp only [φ, norm_mul, logPhase_norm, one_mul, ← pow_mul]
    rw [joint_label_variable_row_subtype_sum labels rows
      (fun l z => ‖(s l).leftValue (t l+2*Real.pi*(w-θ)) z‖^2)]
    apply le_trans (Finset.sum_le_sum (fun l hl =>
      (s l).finite_left_energy (t l+2*Real.pi*(w-θ)) (U l) (K l)
        (hK l hl) (rows l) (hU l hl) (hmajor l hl)))
    simpa only [Nat.mul_comm] using henergy w
  have hh := finite_weighted_integral_energy (columnDensity V hVc hVs) φ
    (fun w => (1+‖w‖)^J) (by intro w; positivity) E hE
    (columnDensity_moments V hVc hVs J) hi he
  have hid (q : (l : ↥labels) × ↥(rows l)) :
      (∫ w : ℝ, columnDensity V hVc hVs w * φ q w) =
        (s q.1).leftWindowValue (t q.1) θ (X q.1) V q.2 := by
    simpa only [φ, mul_assoc] using ((s q.1).left_window_integral
      (t q.1) θ (X q.1) (hX q.1 q.1.property) V hVc hVs q.2).symm
  simp_rw [hid] at hh
  rw [joint_label_variable_row_subtype_sum labels rows
    (fun l z => ‖(s l).leftWindowValue (t l) θ (X l) V z‖^2)] at hh
  exact hh

theorem joint_first_variable_right_window_energy {Λ : Type*} [DecidableEq Λ]
    (labels : Finset Λ) (rows : Λ → Finset O) (s : Λ → FirstJointLabel ι)
    (t X : Λ → ℝ) (hX : ∀ l ∈ labels, 0 < X l) (θ : ℝ)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (U : Λ → 𝓢(ℝ, ℂ)) (K : Λ → ℝ)
    (hK : ∀ l ∈ labels, 0 < K l)
    (hU : ∀ l ∈ labels, ∀ z : O, 0 ≤ (U l (‖eisEmbedding z‖^2 / K l)).re)
    (hmajor : ∀ l ∈ labels, ∀ z ∈ rows l,
      1 ≤ (U l (‖eisEmbedding z‖^2 / K l)).re)
    (J : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (henergy : ∀ w : ℝ, (∑ l ∈ labels,
      (s l).rightEnergy (t l+2*Real.pi*(w-(-θ))) (U l) (K l)) ≤
        E*(1+‖w‖)^(2*J)) :
    (∑ l ∈ labels, ∑ z ∈ rows l, ‖(s l).rightWindowValue (t l) θ (X l) V z‖^2) ≤
      E*(∫ w : ℝ, (1+‖w‖)^J * ‖columnDensity (fun x => star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs) w‖)^2 := by
  let φ : ((l : ↥labels) × ↥(rows l)) → ℝ → ℂ := fun q w =>
    logPhase (-θ-w) (Real.log (X q.1)) *
      (s q.1).rightValue (t q.1+2*Real.pi*(w-(-θ))) q.2
  have hi (q : (l : ↥labels) × ↥(rows l)) :
      Integrable (fun w => columnDensity (fun x => star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs) w * φ q w) := by
    simpa only [φ, mul_assoc] using (s q.1).right_window_integrable
      (t q.1) θ (X q.1) (hX q.1 q.1.property) V hVc hVs q.2
  have he (w : ℝ) : (∑ q : (l : ↥labels) × ↥(rows l), ‖φ q w‖^2) ≤ E*((1+‖w‖)^J)^2 := by
    simp only [φ, norm_mul, logPhase_norm, one_mul, ← pow_mul]
    rw [joint_label_variable_row_subtype_sum labels rows
      (fun l z => ‖(s l).rightValue (t l+2*Real.pi*(w-(-θ))) z‖^2)]
    apply le_trans (Finset.sum_le_sum (fun l hl =>
      (s l).finite_right_energy (t l+2*Real.pi*(w-(-θ))) (U l) (K l)
        (hK l hl) (rows l) (hU l hl) (hmajor l hl)))
    simpa only [Nat.mul_comm] using henergy w
  have hh := finite_weighted_integral_energy (columnDensity (fun x => star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs)) φ
    (fun w => (1+‖w‖)^J) (by intro w; positivity) E hE
    (columnDensity_moments (fun x => star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs) J) hi he
  have hid (q : (l : ↥labels) × ↥(rows l)) :
      (∫ w : ℝ, columnDensity (fun x => star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs) w * φ q w) =
        (s q.1).rightWindowValue (t q.1) θ (X q.1) V q.2 := by
    simpa only [φ, mul_assoc] using ((s q.1).right_window_integral
      (t q.1) θ (X q.1) (hX q.1 q.1.property) V hVc hVs q.2).symm
  simp_rw [hid] at hh
  rw [joint_label_variable_row_subtype_sum labels rows
    (fun l z => ‖(s l).rightWindowValue (t l) θ (X l) V z‖^2)] at hh
  exact hh

theorem joint_first_variable_window_abs_bound {Λ : Type*} [DecidableEq Λ]
    (labels : Finset Λ) (rows : Λ → Finset O) (s : Λ → FirstJointLabel ι)
    (t₁ t₂ X₁ X₂ : Λ → ℝ)
    (hX₁ : ∀ l ∈ labels, 0 < X₁ l) (hX₂ : ∀ l ∈ labels, 0 < X₂ l) (θ : ℝ)
    (V₁ : ℝ → ℂ) (hV₁c : HasCompactSupport V₁) (hV₁s : ContDiff ℝ ∞ V₁)
    (V₂ : ℝ → ℂ) (hV₂c : HasCompactSupport V₂) (hV₂s : ContDiff ℝ ∞ V₂)
    (U : Λ → 𝓢(ℝ, ℂ)) (K : Λ → ℝ)
    (hK : ∀ l ∈ labels, 0 < K l)
    (hU : ∀ l ∈ labels, ∀ z : O, 0 ≤ (U l (‖eisEmbedding z‖^2 / K l)).re)
    (hmajor : ∀ l ∈ labels, ∀ z ∈ rows l,
      1 ≤ (U l (‖eisEmbedding z‖^2 / K l)).re)
    (J₁ J₂ : ℕ) (E₁ E₂ : ℝ) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (hleft : ∀ w : ℝ, (∑ l ∈ labels,
      (s l).leftEnergy (t₁ l+2*Real.pi*(w-θ)) (U l) (K l)) ≤
        E₁*(1+‖w‖)^(2*J₁))
    (hright : ∀ w : ℝ, (∑ l ∈ labels,
      (s l).rightEnergy (t₂ l+2*Real.pi*(w-(-θ))) (U l) (K l)) ≤
        E₂*(1+‖w‖)^(2*J₂)) :
    (∑ l ∈ labels, ∑ z ∈ rows l,
      ‖(s l).leftWindowValue (t₁ l) θ (X₁ l) V₁ z‖ *
      ‖(s l).rightWindowValue (t₂ l) θ (X₂ l) V₂ z‖) ≤
      (Real.sqrt E₁ * jointColumnMoment V₁ hV₁c hV₁s J₁) *
      (Real.sqrt E₂ * jointColumnMoment (fun x => star (V₂ x))
        (conjugate_compact V₂ hV₂c) (conjugate_smooth V₂ hV₂s) J₂) := by
  have hl := joint_first_variable_left_window_energy labels rows s t₁ X₁ hX₁ θ V₁ hV₁c hV₁s
    U K hK hU hmajor J₁ E₁ hE₁ hleft
  have hr := joint_first_variable_right_window_energy labels rows s t₂ X₂ hX₂ θ V₂ hV₂c hV₂s
    U K hK hU hmajor J₂ E₂ hE₂ hright
  have hc := Real.sum_mul_le_sqrt_mul_sqrt (labels.sigma rows)
    (fun q => ‖(s q.1).leftWindowValue (t₁ q.1) θ (X₁ q.1) V₁ q.2‖)
    (fun q => ‖(s q.1).rightWindowValue (t₂ q.1) θ (X₂ q.1) V₂ q.2‖)
  simp only [Finset.sum_sigma] at hc
  apply hc.trans
  have hsl := Real.sqrt_le_sqrt hl
  have hsr := Real.sqrt_le_sqrt hr
  change Real.sqrt _ ≤ Real.sqrt (E₁*(jointColumnMoment V₁ hV₁c hV₁s J₁)^2) at hsl
  change Real.sqrt _ ≤ Real.sqrt (E₂*(jointColumnMoment (fun x => star (V₂ x))
    (conjugate_compact V₂ hV₂c) (conjugate_smooth V₂ hV₂s) J₂)^2) at hsr
  rw [Real.sqrt_mul hE₁, Real.sqrt_sq (jointColumnMoment_nonneg V₁ hV₁c hV₁s J₁)] at hsl
  rw [Real.sqrt_mul hE₂, Real.sqrt_sq (jointColumnMoment_nonneg (fun x => star (V₂ x))
    (conjugate_compact V₂ hV₂c) (conjugate_smooth V₂ hV₂s) J₂)] at hsr
  exact mul_le_mul hsl hsr (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (jointColumnMoment_nonneg V₁ hV₁c hV₁s J₁))

#print axioms joint_first_variable_window_abs_bound
#print axioms joint_first_variable_left_window_energy
#print axioms joint_first_variable_right_window_energy
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstVariableWindow -/

/- BEGIN ORIGINAL MODULE Analytic.JointOriginalComparisonOriginal ; sha256 146e340e9a77f07cf55893069860082671b836a397344628533fdc5049c76e22 -/
section



set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance originalComparisonOriginalFinite : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyReferenceDeletionEnergy
open CenteredMomentInductionEnergy
theorem local_comparison_original_energy
    (epsilonDelete:ℝ)(hepsilonDelete:0< epsilonDelete)
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi saving Mcap Bmask L:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hepsilon:0< epsilon)(hxi:0< xi)
    (hxicap:xi≤1/1000)(hBmask:0≤ Bmask)(hL:Mcap+Bmask+xi≤ L)
    (B:ℕ)(hB:2≤ B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0< Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D Cweight:ℝ,0< C ∧ 0< D ∧ 0< Cweight ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → κ=3/4 →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤ Mcap → 1≤ s.width → s.width≤101/100 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,1≤ X₁ → 1≤ X₂ → X₁≤ Z^(1/4:ℝ) → X₂≤ Z^(3/5:ℝ) →
      (∑i,w i)≤37/1000 →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      Cweight*(s.puncture.radical.absNorm:ℝ)^epsilonDelete*(
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i))) :=by
  obtain ⟨Bslot,hBslot,hslot⟩:=CenteredMomentRayMaskedFloor.slot_coefficient_bounds
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
  obtain ⟨Cweight,hCweight,hweight⟩:=original_energy_weighted_deletion (α:=α)
    (fun _=> bslot) (fun _=> Bslot) (fun _=> hBslot.le) epsilonDelete hepsilonDelete
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=local_comparison_deleted_energy (α:=α) M H hH
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ epsilon xi saving Mcap Bmask L ha hlo hhi hbΦ hepsilon hxi hxicap hBmask hL B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,Cweight,hC,hD,hCweight,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot ε κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hwidthLo hwidthHi W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hslots
  have hZpos:0< Z:=zero_lt_one.trans hZ.1
  have hp : 0< X₁ ∧ 0< X₂ := ⟨zero_lt_one.trans_le hX₁,zero_lt_one.trans_le hX₂⟩
  apply hweight Z Bmask bΦ a b s W₁ W₂ ha (by linarith) hs₁ hs₂
    (fun i=> primePool M H bslot (Z^(w i)))
    (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i=> Z^(w i)) t X₁ X₂ _ 0
  · intro i I hI
    exact (Finset.mem_filter.mp hI).2.1
  · intro i
    exact Real.rpow_pos_of_pos hZpos _
  · intro i I hI
    have hpI:Prime I:=(Finset.mem_filter.mp hI).2.1
    have hh:=(hslot (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (freq i) 0
      (Real.rpow_pos_of_pos hZpos _) (hσlo i) (hσhi i) I hpI.ne_zero).1
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hh
  · intro i I hI hn
    have hpI:Prime I:=(Finset.mem_filter.mp hI).2.1
    have hh:=(hslot (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (freq i) 0
      (Real.rpow_pos_of_pos hZpos _) (hσlo i) (hσhi i) I hpI.ne_zero).2
    apply hh
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hn
  · exact hp.1
  · exact hp.2
  · have hdiag:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
    have hLpos:0≤ L:=by linarith [s.width_nonneg]
    have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
    positivity
  · norm_num
  · intro D₁ hD₁ D₂ hD₂ J hJ
    simpa only [Real.rpow_zero,mul_one] using hZ.2 Lslot ε κ η₀ Q K hK hlow
      θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ s hQ hs hwidthLo hwidthHi
      W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hslots D₁ hD₁ D₂ hD₂ (Finset.univ\J)

#print axioms local_comparison_original_energy
end SevenEighths.Local44.Analytic

end

end OAI
end
/- END ORIGINAL MODULE Analytic.JointOriginalComparisonOriginal -/

/- BEGIN ORIGINAL MODULE Cycle25.Arithmetic.AlgebraicForms ; sha256 ec8d129936fe121abb6232b943b3f7a5e8abaa99a230a9fb5c7160f0a174ca5b -/
section


/-! Polynomial representatives of the endpoint parameters in Q[ell0]/(quartic).
Every representative below is verified by ordinary ring arithmetic using ell0_quartic.
The rational computations that suggested these expressions are not proof oracles. -/

namespace Cycle25.Arithmetic

noncomputable def deltaPoly : ℝ := (4255/4398) + (-9075/2932) * ell0 + (823/1466) * ell0^2 + (2163/2932) * ell0^3
noncomputable def countPoly : ℝ := (661/2907) + (61/204) * ell0 + (7655/1938) * ell0^2 + (-2575/1292) * ell0^3
noncomputable def rprimePoly : ℝ := (-270599/136800) + (35413/7200) * ell0 + (342793/45600) * ell0^2 + (-72203/15200) * ell0^3
noncomputable def hPoly : ℝ := (181525300/284324837) + (393539385/284324837) * ell0 + (-813066675/284324837) * ell0^2 + (247160448/284324837) * ell0^3

theorem delta0_poly : delta0 = deltaPoly := by
  unfold delta0
  apply (div_eq_iff (ne_of_gt delta0_den_pos)).2
  have hp := ell0_quartic
  unfold quartic at hp
  unfold deltaPoly
  linear_combination ((59+21*ell0)/1466)*hp

theorem count0_poly : count0 = countPoly := by
  unfold count0
  apply (div_eq_iff (ne_of_gt count0_den_pos)).2
  have hp := ell0_quartic
  unfold quartic at hp
  unfold countPoly kappa0
  linear_combination (-125/7752)*hp

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem rprime0_poly : rprime0 = rprimePoly := by
  have hp := ell0_quartic
  unfold quartic at hp
  have hid : count0*(v0^2-delta0^2*count0) =
      (rprimePoly+1)*(2*(v0+delta0*count0)^2) := by
    unfold v0
    rw [delta0_poly, count0_poly]
    unfold deltaPoly countPoly rprimePoly
    linear_combination (-((-1850156447833/6189830479823616) + (88781606967431189/11925740057793500160) * ell0 + (601208208889333027/4969058357413958400) * ell0^2 + (-798255385330938761/79504933718623334400) * ell0^3 + (-124580769109824421/174352924821542400) * ell0^4 + (16293028907208269/87176462410771200) * ell0^5 + (543818563504917311/414088196451163200) * ell0^6 + (-3875935381540667357/4416940762145740800) * ell0^7 + (-21318954494550061/73615679369095680) * ell0^8 + (2649881780969587/9815423915879424) * ell0^9 + (306384259895/21525052447104) * ell0^10 + (-96650255286725/4362410629279744) * ell0^11))*hp
  have hq : count0*(v0^2-delta0^2*count0)/(2*(v0+delta0*count0)^2) = rprimePoly+1 :=
    (div_eq_iff (ne_of_gt rprime0_den_pos)).2 hid
  unfold rprime0
  rw [hq]
  ring

theorem h0_poly : h0 = hPoly := by
  have hk : kappa0 ≠ 0 := ne_of_gt (lt_trans (by norm_num) kappa0_range.1)
  have hh : hPoly*(18*kappa0*rprime0-1)+12*kappa0*(1+ell0)+4*ell0 = 0 := by
    rw [rprime0_poly]
    unfold hPoly rprimePoly kappa0
    have hp := ell0_quartic
    unfold quartic at hp
    linear_combination ((248456502563/2593042513440) + (530749913/22745986960) * ell0 + (-546973817511/4321737522400) * ell0^2 + (5414358564/135054297575) * ell0^3)*hp
  unfold h0
  apply (div_eq_iff (ne_of_lt h0_den_neg)).2
  apply mul_right_cancel₀ (show 24*kappa0 ≠ 0 by exact mul_ne_zero (by norm_num) hk)
  have hn : -((1+ell0)/2+ell0/(6*kappa0))*(24*kappa0) =
      -12*kappa0*(1+ell0)-4*ell0 := by field_simp; ring
  have hd : (3*rprime0/4-1/(24*kappa0))*(24*kappa0) = 18*kappa0*rprime0-1 := by
    field_simp; ring
  rw [hn]
  rw [mul_assoc hPoly, hd]
  linear_combination -hh

end Cycle25.Arithmetic
end
/- END ORIGINAL MODULE Cycle25.Arithmetic.AlgebraicForms -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.FromMoments ; sha256 6b79f0b4cdfb7c3d7f7e990c416b6557503934889d57367114e1eec2e707714c -/
section




namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.Cycle25DetectorCountFromMoments
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber Cycle25DetectorBranchBudget
open Cycle25DetectorRawFiber
open Cycle25DetectorRowCount

theorem count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0< c ∧ c≤1 ∧ 0<κ ∧ 0≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε tstar T allowance κplain ν C height : ℝ) (i : ℕ),
      1< U → 51/100< a → 2*a-1≤3/4 → 0≤ε → ε≤1/1000 →
      1≤ tstar → tstar≤3/2 → 7/10≤κplain → κplain≤3/4 → 0<ν → 0≤ C → 0≤ height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤ height →
      ∀ {Label Slot : Type*} (F : Fiber M H Label Slot U a ε tstar T allowance i),
      Cycle25DetectorRawFiber.Moments F κplain c κ C height εm →
      (F.rows.card : ℝ)≤ fiberConstant C height K₀*
        U^(max (shortExponent (2*a-1) (F.q/(2*a-1)) κplain tstar) (longExponent (2*a-1) tstar)+
          159*ε+εm+F.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hamp⟩ := HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hamp] with U hamp
  intro a ε tstar T allowance κplain ν C height i hU ha hδcap hε hεsmall ht ht' hk hk1 hν hC hh hf
    Label Slot F moments
  let δ := 2*a-1
  let x := F.q/δ
  have hδ : 0<δ := by dsimp [δ]; linarith
  have ha' : 1/2≤ a := by linarith
  have hδ1 : δ≤1 := by dsimp [δ]; linarith
  obtain ⟨hq0,hqδ⟩ := F.mean_bounds ha'
  have hx : 0≤ x := div_nonneg hq0 hδ.le
  have hx' : x≤1/2 := (div_le_iff₀ hδ).mpr (by dsimp [δ]; linarith)
  have hqx : δ*x=F.q := by dsimp [x]; field_simp
  have hgeom := F.lengths hU
  have hr0 : 0≤ F.r := by linarith [hgeom.2.2.2.1]
  have hr2 : F.r≤2 := by linarith [hgeom.2.1]
  have hUp : 0< U := zero_lt_one.trans hU
  obtain ⟨hconst,hconstP,hconstI,hconstI0⟩ := fiberConstant_bounds C height K₀ hC hh hK
  have promote (C' p q : ℝ) (hC' : C'≤ fiberConstant C height K₀)
      (hb : (F.rows.card : ℝ)≤ C'*U^p) (hpq : p≤ q) :
      (F.rows.card : ℝ)≤ fiberConstant C height K₀*U^q := by
    exact hb.trans ((mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hUp.le _)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hpq) hconst))
  have hi0 := hamp F.rows F.family a ε tstar T allowance i hU ha'
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    hr0 hr2 F.rowData F.reverse C height hC hh hf F.row_norm F.row_coeff moments.original.inverse_raw
  have hI0 : (F.rows.card : ℝ)≤ fiberConstant C height K₀*
      U^(max 1 ((1+5*F.r)/6)-δ*F.r+commonLoss ε εm F.mesh ν) := by
    apply promote _ _ _ hconstI0 hi0
    exact no_slot_inverse_loss F.r δ ε εm F.mesh ν hε F.mesh_nonneg hν.le
  have hp0 := F.plain_unmarked_count moments.original hU (by linarith) hC hh hf
  have hP0 : (F.rows.card : ℝ)≤ fiberConstant C height K₀*
      U^(1-2*δ*F.m+commonLoss ε εm F.mesh ν) := by
    apply promote _ _ _ hconstP hp0
    exact no_slot_plain_loss F.m δ ε εm F.mesh ν hε hgeom.2.2.1 F.mesh_nonneg hν.le
  have hI : 23/37≤ F.r → F.r<1 → ν<(1-F.r)/2 →
      (F.rows.card : ℝ)≤ fiberConstant C height K₀*
        U^(inverseExponent δ x F.r+commonLoss ε εm F.mesh ν) := by
    intro hr hr1 hv
    obtain ⟨hz,hz',hcap1,hcap2⟩ := inverse_requested_capacity F.r ν hr hr1 hν hv
    have hb := F.inverse_marked_count moments.original hU ha' hC hh hf ((1-F.r)/2-ν) hz hz' hcap1 hcap2
    apply promote _ _ _ hconstI hb
    have hl := inverse_marked_loss F.r δ x ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
    rwa [hqx] at hl
  have hP : F.r≤ crossing x κplain tstar → F.m<1/2 → ν<(1-2*F.m)/(6*κplain) →
      (F.rows.card : ℝ)≤ fiberConstant C height K₀*
        U^(1-2*δ*F.m-2*(δ*x)*(1-2*F.m)/(6*κplain)+commonLoss ε εm F.mesh ν) := by
    intro hr hm hv
    obtain ⟨hz,hz',hcap⟩ := plain_requested_capacity κplain x tstar F.r F.m ε ν hk hk1 hx hx' ht ht'
      hr hgeom.1 (by linarith) hν.le hv
    have hb := Cycle25DetectorRawFiber.plain_marked_count F moments hU ha' (by linarith) hC hh hf
      ((1-2*F.m)/(6*κplain)-ν) hz hz' hcap
    apply promote _ _ _ hconstP hb
    have hl := plain_marked_loss F.m δ x κplain ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
    simpa only [hqx] using hl
  have hc' := count_bound_of_source_branches (F.rows.card : ℝ) (fiberConstant C height K₀) U δ x κplain
    tstar F.r F.m (commonLoss ε εm F.mesh ν) ν ε hconst hU.le hδ.le (by dsimp [δ]; linarith) hx hx' hk hk1
    ht ht' hν.le hε hgeom.1 hgeom.2.1 hI0 hP0 hI hP
  convert hc' using 1; congr 2
  unfold commonLoss
  ring

end SevenEighths.Cycle25DetectorCountFromMoments

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.FromMoments -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.MaskedCount ; sha256 484525dd10b6ef7995edb6020839f34d737077b5d6b52921264439b15569b51b -/
section



namespace OAI.SevenEighths.Cycle25DetectorRowCount
noncomputable section
open HeckeDetectorPhysicalSelection
open scoped Classical BigOperators

theorem coefficient_antitone {κ x y : ℝ} (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hx : 0≤ x) (hxy : x≤ y) (hy : y≤1/2) : coefficient y κ≤ coefficient x κ := by
  have hdx : 0< denominator x κ := lt_of_lt_of_le (by norm_num) (denominator_lower hx (hxy.trans hy) hk hk1)
  have hdy : 0< denominator y κ := lt_of_lt_of_le (by norm_num) (denominator_lower (hx.trans hxy) hy hk hk1)
  let a : ℝ := 1/(3*κ)
  have ha : 0≤ a := by dsimp [a]; positivity
  have ha1 : a≤10/21 := (div_le_iff₀ (show 0<3*κ by linarith)).mpr (by linarith)
  have hbx : b x κ=x*a := by unfold b; dsimp [a]; ring
  have hby : b y κ=y*a := by unfold b; dsimp [a]; ring
  have he : primeWeight x κ*denominator y κ-primeWeight y κ*denominator x κ=
      (y-x)*(4+2*a-6*a*(x+y)+2*a*(1+2*a)*x*y) := by
    unfold primeWeight denominator
    rw [hbx,hby]
    ring
  have hsum : x+y≤1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsum ha
  have hp : 0≤4+2*a-6*a*(x+y)+2*a*(1+2*a)*x*y := by
    have hp := mul_nonneg (mul_nonneg (mul_nonneg ha (by linarith : 0≤1+2*a)) hx) (hx.trans hxy)
    nlinarith
  have hh := mul_nonneg (sub_nonneg.mpr hxy) hp
  unfold coefficient
  apply (div_le_div_iff₀ hdy hdx).mpr
  linarith

theorem rowCount_antitone {δ κ x y : ℝ}
    (hδ : 0≤δ) (hδ1 : δ≤3/4) (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hx : 0≤ x) (hxy : x≤ y) (hy : y≤1/2) : rowCount δ y κ≤ rowCount δ x κ := by
  have hc := coefficient_antitone hk hk1 hx hxy hy
  have hcx := coefficient_nonneg hx (hxy.trans hy) hk hk1
  have hcy := coefficient_nonneg (hx.trans hxy) hy hk hk1
  have hv : 0< V δ := by unfold V; linarith
  have hdx : 0<2*(V δ+δ*coefficient x κ) := by positivity
  have hdy : 0<2*(V δ+δ*coefficient y κ) := by positivity
  unfold rowCount
  apply add_le_add le_rfl
  apply (div_le_div_iff₀ hdy hdx).mpr
  have hh := mul_nonneg (mul_nonneg hδ (sq_nonneg (V δ))) (sub_nonneg.mpr hc)
  nlinarith
def maskedGain {α : Type*} [DecidableEq α] (main : Finset α) (g : α→ℝ) (i : α) : ℝ :=
  if i∈main then g i else 0

theorem maskedMean_bounds {α : Type*} [DecidableEq α]
    (slots main : Finset α) (width g : α→ℝ) (δ : ℝ)
    (hw : ∀j∈slots,0 ≤ width j) (hL : 0 < ∑j∈slots,width j)
    (hg : ∀j∈slots,0 ≤ g j ∧ g j ≤ δ/2) :
    0 ≤ weightedMean slots width (maskedGain main g) ∧
    weightedMean slots width (maskedGain main g) ≤ weightedMean slots width g ∧
    weightedMean slots width g ≤ δ/2 := by
  have hmasked : ∀j∈slots,0 ≤ maskedGain main g j ∧ maskedGain main g j ≤ δ/2 := by
    intro j hj
    unfold maskedGain
    split_ifs with hm
    · exact hg j hj
    · have hh := hg j hj
      exact ⟨le_rfl,by linarith⟩
  have hb := weightedMean_bounds slots width (maskedGain main g) δ hw hL hmasked
  have hfull := weightedMean_bounds slots width g δ hw hL hg
  refine ⟨hb.1,?_,hfull.2⟩
  unfold weightedMean
  apply div_le_div_of_nonneg_right _ hL.le
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (hw j hj)
  unfold maskedGain
  split_ifs with hm
  · exact le_rfl
  · exact (hg j hj).1

/-- A card bound in the original full physical bins remains true at the
weaker diluted main-slot mean. Both means divide by the full slot length. -/
theorem masked_row_count_transfer {α ι : Type*} [DecidableEq α]
    (slots main : Finset α) (width g : α→ℝ) (rows : Finset ι)
    (δ κ U C loss : ℝ) (hδ : 0 < δ) (hδtop : δ ≤ 3/4) (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hU : 1 ≤ U) (hC : 0 ≤ C)
    (hw : ∀j∈slots,0 ≤ width j) (hL : 0 < ∑j∈slots,width j)
    (hg : ∀j∈slots,0 ≤ g j ∧ g j ≤ δ/2)
    (hcard : (rows.card:ℝ) ≤ C*U^(rowCount δ (weightedMean slots width g/δ) κ+loss)) :
    (rows.card:ℝ) ≤ C*U^(rowCount δ (weightedMean slots width (maskedGain main g)/δ) κ+loss) := by
  obtain ⟨hq0,hq,hqtop⟩ := maskedMean_bounds slots main width g δ hw hL hg
  apply hcard.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_le hU
  apply add_le_add _ le_rfl
  apply rowCount_antitone hδ.le hδtop hk hk1
  · exact div_nonneg hq0 hδ.le
  · exact div_le_div_of_nonneg_right hq hδ.le
  · apply (div_le_iff₀ hδ).mpr
    linarith


/-- Every amplitude in a nonempty original class equals its fixed bin value. -/
theorem amplitude_class_value {Row Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0 < mesh) (width : Slot→ℝ) (Q : Row→Slot→ℂ)
    (bin : HeckeDetectorFiberPartition.BinLabel slots cap mesh) (u : Row)
    (hu : u∈HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U cap mesh hm width Q bin)
    (j : Slot) (hj : j∈slots) :
    HeckePrimeAmplitudeBins.amplitude (U^(width j)) cap mesh (Q u j)=
      HeckeDetectorFiberPartition.binValue slots cap mesh bin j := by
  have he := (Finset.mem_filter.mp hu).2
  have hv := congrArg (fun f : HeckeDetectorFiberPartition.BinLabel slots cap mesh=>(f ⟨j,hj⟩).val) he
  simpa only [HeckeDetectorFiberPartition.amplitudeLabel,HeckeDetectorFiberPartition.binValue,
    dite_eq_left hj] using hv

/-- Direct count transfer on an actual full amplitude class. The full bin is
retained, while main amplitudes are zeroed only after the count is proved. -/
theorem masked_amplitude_class_count {Row Slot : Type*} [DecidableEq Slot]
    (rows : Finset Row) (slots main : Finset Slot) (U δ κ mesh : ℝ) (hm : 0 < mesh)
    (width : Slot→ℝ) (Q : Row→Slot→ℂ)
    (bin : HeckeDetectorFiberPartition.BinLabel slots (δ/2) mesh)
    (hδ : 0 < δ) (hδtop : δ ≤ 3/4) (hk : 7/10≤κ) (hk1 : κ≤3/4) (hU : 1 ≤ U)
    (hw : ∀j∈slots,0 ≤ width j) (hL : 0 < ∑j∈slots,width j)
    (C loss : ℝ) (hC : 0 ≤ C)
    (hne : (HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).Nonempty)
    (hcard : ((HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).card:ℝ) ≤
      C*U^(rowCount δ (HeckeDetectorAmplitudeFirst.classMean slots (δ/2) mesh width bin/δ) κ+loss)) :
    let g := HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin
    let q := weightedMean slots width (maskedGain main g)
    0 ≤ q ∧ q ≤ δ/2 ∧
      ((HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).card:ℝ) ≤
        C*U^(rowCount δ (q/δ) κ+loss) := by
  dsimp only
  have hg : ∀j∈slots,0 ≤ HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin j ∧
      HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin j ≤ δ/2 := by
    obtain ⟨u,hu⟩ := hne
    intro j hj
    rw [←amplitude_class_value rows slots U (δ/2) mesh hm width Q bin u hu j hj]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)
  obtain ⟨hq0,hq,hqtop⟩ := maskedMean_bounds slots main width
    (HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin) δ hw hL hg
  refine ⟨hq0,hq.trans hqtop,?_⟩
  exact masked_row_count_transfer slots main width _ _ δ κ U C loss hδ hδtop hk hk1 hU hC hw hL hg hcard

end
end OAI.SevenEighths.Cycle25DetectorRowCount
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.MaskedCount -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.MomentDetectorMomentPrimeGeometry ; sha256 8a67369f763c980eb7a060c9134f296913f0e47647f08df4dd73e58a09e9f9b5 -/
section





namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.Cycle25ProbeHighRowFamily
open ProbeHighRowFamily Cycle25ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialPhysicalSlots
open HeckeDetectorBatch HeckeDetectorRawFiber HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O

theorem weighted_sourceMoment_physical_scale (Z d ell : ℝ) (hZ : 0 ≤ Z) (hd : d≠0) :
    (Z^d)^(ell/d)=Z^ell := by
  rw [←Real.rpow_mul hZ,mul_div_cancel₀ _ hd]

theorem weighted_sourceMoment_separation_eventually {Slot : Type*} [Fintype Slot]
    (ell : Slot→ℝ) (hinj : Function.Injective ell) :
    ∀ᶠ Z : ℝ in atTop, 1 ≤ Z ∧ ∀d : ℝ,0< d→∀s t : Slot,s≠t→
      2*(Z^d)^(ell s/d)<1*(Z^d)^(ell t/d) ∨
      2*(Z^d)^(ell t/d)<1*(Z^d)^(ell s/d) := by
  have hs : ∀ᶠ Z : ℝ in atTop,∀s t : Slot,s≠t→
      2*Z^(ell s)<1*Z^(ell t) ∨ 2*Z^(ell t)<1*Z^(ell s) := by
    apply Filter.eventually_all.mpr
    intro s
    apply Filter.eventually_all.mpr
    intro t
    by_cases he : s=t
    · exact Filter.Eventually.of_forall (fun _ h=> False.elim (h he))
    rcases lt_or_gt_of_ne (fun h=> he (hinj h)) with hlt|hlt
    · filter_upwards [ProbeRaySlots.annular_power_separation 1 2 (ell s) (ell t)
        (by norm_num) hlt] with Z hZ _
      exact Or.inl hZ
    · filter_upwards [ProbeRaySlots.annular_power_separation 1 2 (ell t) (ell s)
        (by norm_num) hlt] with Z hZ _
      exact Or.inr hZ
  filter_upwards [hs,eventually_ge_atTop (1:ℝ)] with Z hs hZ
  refine ⟨hZ,?_⟩
  intro d hd s t hst
  simp only [weighted_sourceMoment_physical_scale Z d _ (by linarith) hd.ne']
  exact hs s t hst

theorem weighted_sourceMoment_fixedBase_norm_one (data : RowData) (P : Ideal O) (hP : Prime P)
    (hlarge : ((baseCharacter data).modulus.absNorm:ℝ)<(P.absNorm:ℝ)) :
    ‖fixedBase data.η data.m data.f P‖=1 := by
  rw [←baseCharacter_coeff]
  exact PrincipalSignalComparison.idealCoeff_norm_one_of_coprime
    (baseCharacter data) P hP.ne_zero
    (ProbeRaySlots.prime_coprime_of_norm_gt (baseCharacter data) ⟨P,hP⟩ hlarge)

theorem weighted_sourceMoment_primeProfile_norm {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (X : ℝ) (ζ : ℂ) (hz : ζ.re ≤ 1)
    (P : Ideal O) : ‖primeProfile F.W X ζ P‖ ≤ 1 := by
  by_cases hw : F.W ((P.absNorm:ℝ)/X)=0
  · simp [primeProfile,hw]
  have hx := F.complex_support hw
  have hp : 0<(P.absNorm:ℝ)/X := lt_of_lt_of_le (by norm_num) hx.1
  have hnorm : ‖F.W ((P.absNorm:ℝ)/X)‖ ≤ 1 := by
    rw [F.complex_eq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (F.bounded _).1]
    exact (F.bounded _).2
  rw [primeProfile,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hp]
  have hr : ((P.absNorm:ℝ)/X)^((ζ-1).re) ≤ 1 :=
    (Real.rpow_le_rpow_of_exponent_le hx.1
      (show (ζ-1).re ≤ 0 by simp only [Complex.sub_re,Complex.one_re];linarith)).trans_eq
        (Real.rpow_zero _)
  simpa only [one_mul] using mul_le_mul hnorm hr (Real.rpow_nonneg hp.le _) (by norm_num : (0:ℝ) ≤ 1)

section Live
variable (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)

theorem weighted_sourceMoment_live_disjoint {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) {ι : Type*} (ell : ι→ℝ)
    (U : ℝ) (hU : 0< U) (s t : ι)
    (hsep : 2*U^(ell s)<1*U^(ell t) ∨ 2*U^(ell t)<1*U^(ell s)) :
    Disjoint (livePrimes M H F.W 2 (U^(ell s))) (livePrimes M H F.W 2 (U^(ell t))) := by
  apply Finset.disjoint_left.mpr
  intro P hs ht
  have hs' := livePrime_data M H F.W 1 2 (U^(ell s))
    (Real.rpow_pos_of_pos hU _) F.complex_support P hs
  have ht' := livePrime_data M H F.W 1 2 (U^(ell t))
    (Real.rpow_pos_of_pos hU _) F.complex_support P ht
  rcases hsep with hsep|hsep <;> linarith [hs'.2.2.1,hs'.2.2.2,ht'.2.2.1,ht'.2.2.2]

theorem weighted_sourceMoment_live_denominator {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) {ι : Type*} [Fintype ι]
    (data : RowData) (U : ℝ) (ell : ι→ℝ) (hU : 0< U)
    (hlarge : ∀s,((baseCharacter data).modulus.absNorm:ℝ)<1*U^(ell s))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset (fun s=> livePrimes M H F.W 2 (U^(ell s)))) :
    ‖fixedBase data.η data.m data.f (∏s,p s)‖=1 := by
  rw [map_prod,norm_prod]
  apply Finset.prod_eq_one
  intro s _
  have hs := livePrime_data M H F.W 1 2 (U^(ell s))
    (Real.rpow_pos_of_pos hU _) F.complex_support (p s) (Fintype.mem_piFinset.mp hp s)
  exact weighted_sourceMoment_fixedBase_norm_one data (p s) hs.1 ((hlarge s).trans_le hs.2.2.1)

theorem weighted_sourceMoment_live_quotient_norm {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) {ι : Type*} [Fintype ι]
    (data : RowData) (U : ℝ) (ell : ι→ℝ) (ζ : ι→ℂ) (hU : 0< U)
    (hz : ∀s,(ζ s).re=17/50)
    (hlarge : ∀s,((baseCharacter data).modulus.absNorm:ℝ)<1*U^(ell s))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset (fun s=> livePrimes M H F.W 2 (U^(ell s)))) :
    ‖star (∏s,primeProfile F.W (U^(ell s)) (ζ s) (p s))/
      fixedBase data.η data.m data.f (∏s,p s)‖ ≤ 1 := by
  rw [norm_div,norm_star,weighted_sourceMoment_live_denominator M H F data U ell hU hlarge p hp,
    div_one,norm_prod]
  exact Finset.prod_le_one₀ (fun s _=> norm_nonneg _)
    (fun s _=> weighted_sourceMoment_primeProfile_norm F _ _ (by rw [hz s];norm_num) _)
end Live

theorem weighted_sourceMoment_capacity_eventually {Slot : Type*} [Fintype Slot]
    (ell : Slot→ℝ) (hell : ∀s,0 ≤ ell s) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in atTop,1 ≤ Z ∧ ∀d : ℝ,1/200 ≤ d→
      (∀s,1 ≤ 2*(Z^d)^(ell s/d)) ∧ ∀selected : Finset Slot,
      (∏s:selected,2*(Z^d)^(ell s/d)) ≤
        (Z^d)^((∑s:selected,ell s/d)+ε) := by
  have ht := (tendsto_rpow_atTop (show 0<ε/200 by positivity)).eventually
    (eventually_ge_atTop ((2:ℝ)^Fintype.card Slot))
  filter_upwards [ht,eventually_ge_atTop (1:ℝ)] with Z ht hZ
  refine ⟨hZ,?_⟩
  intro d hd
  have hd0 : 0< d := by linarith
  have hz0 : 0< Z := zero_lt_one.trans_le hZ
  have hu0 : 0< Z^d := Real.rpow_pos_of_pos hz0 _
  have hu1 : 1 ≤ Z^d := Real.one_le_rpow hZ hd0.le
  refine ⟨?_,?_⟩
  · intro s
    have hh : 1 ≤ (Z^d)^(ell s/d) := Real.one_le_rpow hu1 (div_nonneg (hell s) hd0.le)
    linarith
  · intro selected
    have hf : (2:ℝ)^selected.card ≤ (2:ℝ)^Fintype.card Slot :=
      pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ selected)
    have hp : (2:ℝ)^selected.card ≤ (Z^d)^ε := by
      rw [←Real.rpow_mul hz0.le]
      exact (hf.trans ht).trans (Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith))
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
      ←Real.rpow_sum_of_pos hu0,Real.rpow_add hu0]
    calc
      _  ≤  (Z^d)^ε*(Z^d)^(∑s:selected,ell s/d) :=
        mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hu0.le _)
      _ = _ := mul_comm _ _

section Source
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem weighted_sourceMoment_fiber_prime_geometry_eventually
    {D : Cycle25.Weighted.MomentData} (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (η : Character) (εg : ℝ) (hεg : 0<εg) :
    ∀ᶠ Z : ℝ in atTop,1 ≤ Z ∧ ∀d : ℝ,1/200 ≤ d→
      ∀(a ε tstar T allowance : ℝ)(i : ℕ)
      (B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH F.S F.exclusions.prime η→
      B.profile=(fun _ x=>(F.w x:ℂ))→B.upper=(fun _=>2)→
      B.widths=(fun s=> D.ell s/d)→(∀s,(B.external s).re=17/50)→
      ∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
      let f:=B.fiber bin j J K hne
      (∀s t,s≠t→Disjoint
        (livePrimes M H (f.profile s) (f.upper s) ((Z^d)^(f.widths s)))
        (livePrimes M H (f.profile t) (f.upper t) ((Z^d)^(f.widths t)))) ∧
      ∀selected : Finset (Fin D.N),
        (∀s:selected,1 ≤ 2*(Z^d)^(f.widths s)) ∧
        (∏s:selected,2*(Z^d)^(f.widths s)) ≤
          (Z^d)^((∑s:selected,f.widths s)+εg) ∧
        ∀p : selected→Ideal O,
        p∈Fintype.piFinset (fun s:selected=>
          livePrimes M H (f.profile s) (f.upper s) ((Z^d)^(f.widths s)))→
        Function.Injective p ∧ CanonicalQuadraticSieve.Admissible (∏s:selected,p s) ∧
        (∀s:selected,((p s).absNorm:ℝ) ≤ 2*(Z^d)^(f.widths s)) ∧
        ‖fixedBase f.rowData.η f.rowData.m f.rowData.f (∏s:selected,p s)‖=1 ∧
        ‖star (∏s:selected,primeProfile (f.profile s) ((Z^d)^(f.widths s)) (f.external s) (p s))/
          fixedBase f.rowData.η f.rowData.m f.rowData.f (∏s:selected,p s)‖ ≤ 1 := by
  filter_upwards [weighted_sourceMoment_separation_eventually D.ell D.slots_injective,
    weighted_sourceMoment_capacity_eventually D.ell (fun s=>(D.slots_bounds s).1.le) εg hεg,
    sourceMoment_fiber_large_eventually M H hH F.S F.exclusions.prime η
      D.ell (fun s=>(D.slots_bounds s).1)] with Z hsep hcap hlarge
  refine ⟨hsep.1,?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile0 hupper hwidths hz bin j J K hne
  have hprofile : B.profile=(fun _=>(F.W:ℝ→ℂ)) := by
    rw [hprofile0]
    funext s x
    exact (F.complex_eq x).symm
  have hd0 : 0< d := by linarith
  have hu : 0< Z^d := Real.rpow_pos_of_pos (zero_lt_one.trans_le hsep.1) _
  have hs := hsep.2 d hd0
  have hc := hcap.2 d hd
  have hl := hlarge.2 d hd0 a ε tstar T allowance i B hdata hwidths bin j J K hne
  dsimp only
  change (∀s t,s≠t→Disjoint
      (livePrimes M H (B.profile s) (B.upper s) ((Z^d)^(B.widths s)))
      (livePrimes M H (B.profile t) (B.upper t) ((Z^d)^(B.widths t)))) ∧ _
  refine ⟨?_,?_⟩
  · intro s t hst
    rw [hprofile,hupper,hwidths]
    exact weighted_sourceMoment_live_disjoint M H F (fun s=> D.ell s/d) (Z^d) hu s t (hs s t hst)
  · intro selected
    change (∀s:selected,1 ≤ 2*(Z^d)^(B.widths s)) ∧
      (∏s:selected,2*(Z^d)^(B.widths s)) ≤ (Z^d)^((∑s:selected,B.widths s)+εg) ∧ _
    refine ⟨?_,?_,?_⟩
    · rw [hwidths]
      exact fun s=> hc.1 s
    · rw [hwidths]
      exact hc.2 selected
    · intro p hp
      have hp' : p∈Fintype.piFinset (fun s:selected=> livePrimes M H F.W 2 ((Z^d)^(D.ell s/d))) := by
        change p∈Fintype.piFinset (fun s:selected=> livePrimes M H (B.profile s) (B.upper s) ((Z^d)^(B.widths s))) at hp
        simpa only [hprofile,hupper,hwidths] using hp
      have hl' : ∀s:selected,((baseCharacter (B.data j)).modulus.absNorm:ℝ)<1*(Z^d)^(D.ell s/d) := by
        intro s
        have hh:=hl s
        change ((baseCharacter (B.data j)).modulus.absNorm:ℝ)<1*(Z^d)^(B.widths s) at hh
        simpa only [hwidths] using hh
      have hs' : ∀s t:selected,s≠t→2*(Z^d)^(D.ell s/d)<1*(Z^d)^(D.ell t/d) ∨
          2*(Z^d)^(D.ell t/d)<1*(Z^d)^(D.ell s/d) := by
        intro s t hst
        exact hs s t (fun he=> hst (Subtype.ext he))
      refine ⟨?_,?_,?_,?_,?_⟩
      · exact live_tuple_injective M H (fun _=> F.W) (fun _=>1) (fun _=>2)
          (fun s:selected=> D.ell s/d) (Z^d) hu (fun _=> F.complex_support) hs' p (by simpa only [Fintype.mem_piFinset] using hp')
      · exact live_tuple_admissible M H (B.data j) (fun _=> F.W) (fun _=>1) (fun _=>2)
          (fun s:selected=> D.ell s/d) (Z^d) hu (fun _=> F.complex_support) hl' hs' p (by simpa only [Fintype.mem_piFinset] using hp')
      · intro s
        change ((p s).absNorm:ℝ) ≤ 2*(Z^d)^(B.widths s)
        rw [hwidths]
        exact (livePrime_data M H F.W 1 2 ((Z^d)^(D.ell s/d))
          (Real.rpow_pos_of_pos hu _) F.complex_support (p s) (Fintype.mem_piFinset.mp (by simpa only [Fintype.mem_piFinset] using hp') s)).2.2.2
      · exact weighted_sourceMoment_live_denominator M H F (B.data j) (Z^d)
          (fun s:selected=> D.ell s/d) hu hl' p (by simpa only [Fintype.mem_piFinset] using hp')
      · change ‖star (∏s:selected,primeProfile (B.profile s) ((Z^d)^(B.widths s)) (B.external s) (p s))/
          fixedBase (B.data j).η (B.data j).m (B.data j).f (∏s:selected,p s)‖ ≤ 1
        rw [hprofile,hwidths]
        exact weighted_sourceMoment_live_quotient_norm M H F (B.data j) (Z^d)
          (fun s:selected=> D.ell s/d) (fun s:selected=> B.external s) hu (fun s=> hz s) hl' p (by simpa only [Fintype.mem_piFinset] using hp')

end Source
end SevenEighths.Cycle25ProbeHighRowFamily

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.MomentDetectorMomentPrimeGeometry -/
