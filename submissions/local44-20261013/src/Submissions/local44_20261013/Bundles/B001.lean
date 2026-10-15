/- Deterministically bundled proof sources; original notices are retained below. -/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Max
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowDeletedGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.Dirichlet
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.PrimitiveSupremum
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.SignalIdentity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondSupportedChildren
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.UniformDivisorShell
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell

/- BEGIN ORIGINAL MODULE Analytic.JointLowFrequency ; sha256 177cc4bd67db72433c2c5654ad605007225f3155f8a908ab9c62ee1caf1f78b4 -/
section


/-! A fixed finite bin family and the original height cap supply every
low source gate on the second Fourier cube. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeDetectorDyadicGeometry

lemma low_shifted_plain_height (t u θ X : ℝ)
    (ht : |t| ≤ X) (hu : |u| ≤ X) (hθ : |θ| ≤ X) :
    |t+2*Real.pi*(u-θ)| ≤ (1+4*Real.pi)*X := by
  have hp : 0 ≤ 2*Real.pi := by positivity
  have hs : |u-θ| ≤ 2*X := (abs_sub u θ).trans (by linarith)
  have ha := abs_add_le t (2*Real.pi*(u-θ))
  rw [abs_mul,abs_of_nonneg hp] at ha
  nlinarith [mul_le_mul_of_nonneg_left hs hp]

theorem eventually_low_source_heights (τ ν d η : ℝ) (I : ℕ)
    (hτ : 0 < τ) (hd : 0 < d) (hgap : ν < τ) (hη : 0 ≤ η)
    (hheight : 2*τ < d*η) :
    ∀ᶠ Z : ℝ in atTop, 2 ≤ Z^d ∧ 2 < Z^τ ∧
      (∀ t f u θ : ℝ, |t| ≤ Z^ν → |f| ≤ Z^ν → |u| ≤ Z^ν → |θ| ≤ Z^ν →
        ∀ k : ℕ, |t+2*Real.pi*(u-θ)+f|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ) ∧
      (∀ k : ℕ,k ≤ I → (3+(3*k+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^η) := by
  have hf := uniform_power_allowance (2+4*Real.pi) ν τ 1 zero_le_one (by simpa using hgap)
  have hh := uniform_power_allowance ((3*(I : ℝ)+5)^2) (2*τ) d η hη hheight
  filter_upwards [hf,hh,eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop hd).eventually (eventually_ge_atTop (2 : ℝ)),
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2 : ℝ))] with Z hf hh hZ hscale hT
  refine ⟨hscale,hT,?_,?_⟩
  · intro t f u θ ht hfreq hu hθ k
    have hp := low_shifted_plain_height t u θ (Z^ν) ht hu hθ
    have hs := abs_add_le (t+2*Real.pi*(u-θ)) f
    have hc : (2+4*Real.pi)*Z^ν ≤ Z^τ := by simpa using hf τ le_rfl
    have hk : (2 : ℝ) ≤ (3*k+2 : ℕ) := by exact_mod_cast (show 2 ≤ 3*k+2 by omega)
    have hzτ : 0 ≤ Z^τ := Real.rpow_nonneg (zero_le_one.trans hZ) _
    nlinarith [mul_le_mul_of_nonneg_right hk hzτ]
  · intro k hk
    have ht : 1 ≤ Z^τ := Real.one_le_rpow hZ hτ.le
    have hkR : (k : ℝ) ≤ I := by exact_mod_cast hk
    have harg : 3+(3*k+2 : ℕ)*Z^τ ≤ (3*(I : ℝ)+5)*Z^τ := by
      push_cast
      nlinarith
    calc
      _ ≤ ((3*(I : ℝ)+5)*Z^τ)^2 := pow_le_pow_left₀ (by positivity) harg 2
      _ = (3*(I : ℝ)+5)^2*Z^(2*τ) := by
        rw [mul_pow]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul (zero_le_one.trans hZ)]
        congr 1
        norm_num
        ring
      _ ≤ _ := hh d le_rfl

#print axioms eventually_low_source_heights
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowFrequency -/

/- BEGIN ORIGINAL MODULE Analytic.JointOriginalComparisonGeometry ; sha256 fe86c07f2a8b0baa50c7e8f7f08c9e96a92f2f6eba0f5a369694182c50421fdb -/
section


/-! The quarter-length comparison has low old capacity after either
retention or reflection, without an old-capacity premise on the original pair. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceDivisors CenteredMomentEnergyReferenceLowBranchGeometry
local notation "O" => HeckeFamily.O

theorem local_comparison_deleted_gates {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ)
    (hZ : 1 < Z) (hB : 0 ≤ Bmask) (Mcap L X₁ X₂ z ξ : ℝ)
    (hwidth : s.width ≤ Mcap) (hL : Mcap+Bmask+ξ ≤ L)
    (hwidthLo : 1 ≤ s.width) (hwidthHi : s.width ≤ 101/100)
    (hξ : 0 ≤ ξ) (hξcap : ξ ≤ 1/1000)
    (hX₁ : 1 ≤ X₁) (hX₂ : 1 ≤ X₂)
    (hcap₁ : X₁ ≤ Z^(1/4:ℝ)) (hcap₂ : X₂ ≤ Z^(3/5:ℝ))
    (hz : z ≤ 37/1000)
    (D₁ D₂ : Finset (Ideal O))
    (hD₁ : D₁ ∈ (CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂ : D₂ ∈ (CompletedGauss.primeSupport s.puncture).powerset) :
    let short := Real.logb Z X₁-Real.logb Z ((∏ P ∈ D₁,P).absNorm : ℝ)
    let along := Real.logb Z X₂-Real.logb Z ((∏ P ∈ D₂,P).absNorm : ℝ)
    Z^short = X₁/((∏ P ∈ D₁,P).absNorm : ℝ) ∧
    Z^along = X₂/((∏ P ∈ D₂,P).absNorm : ℝ) ∧
    short ≤ 1/4 ∧ short ≤ L ∧ along ≤ L ∧
    s.width ≤ (Mcap+Bmask)+along ∧ max 0 (s.width-along+ξ) ≤ L ∧
    ((length Z (Z^short)+length Z (Z^along)+z ≤ 5*s.width/6 ∧
        length Z (Z^short)+length Z (Z^along)+6*(3/4)*z ≤ s.width) ∨
      (max 0 (s.width-along+ξ)+length Z (Z^short)+z ≤ 5*s.width/6 ∧
        max 0 (s.width-along+ξ)+length Z (Z^short)+6*(3/4)*z ≤ s.width)) := by
  have hbase := zero_lt_one.trans hZ
  have hd₁ := divisor_reflection_range s hZ Mcap X₁ hwidth hX₁ D₁ hD₁
  have hd₂ := divisor_reflection_range s hZ Mcap X₂ hwidth hX₂ D₂ hD₂
  have hn₁ := (divisor_norm s D₁ hD₁).1
  have hn₂ := (divisor_norm s D₂ hD₂).1
  have hlog₁ := Real.logb_nonneg hZ hn₁
  have hlog₂ := Real.logb_nonneg hZ hn₂
  have hlogX₁ := (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hX₁)).mpr hcap₁
  have hlogX₂ := (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hX₂)).mpr hcap₂
  let short := Real.logb Z X₁-Real.logb Z ((∏ P ∈ D₁,P).absNorm : ℝ)
  let along := Real.logb Z X₂-Real.logb Z ((∏ P ∈ D₂,P).absNorm : ℝ)
  change -Bmask ≤ short ∧ _ at hd₁
  change -Bmask ≤ along ∧ _ at hd₂
  have hshort : short ≤ 1/4 := by dsimp only [short]; linarith
  have halong : along ≤ 3/5 := by dsimp only [along]; linarith
  have hLone : 1 ≤ L := by linarith
  dsimp only
  refine ⟨hd₁.2.2,hd₂.2.2,hshort,by linarith,by linarith,hd₂.2.1,
    max_le (by linarith) (by linarith [hd₂.1]),?_⟩
  have hlength (v : ℝ) : length Z (Z^v)=max 0 v := by
    rw [length_eq_max_log Z _ hZ (Real.rpow_pos_of_pos hbase _),Real.logb_rpow hbase hZ.ne']
  rw [hlength,hlength]
  have hs : max 0 short ≤ 1/4 := max_le (by norm_num) hshort
  by_cases hlong : along ≤ 1/2
  · have hl : max 0 along ≤ 1/2 := max_le (by norm_num) hlong
    exact Or.inl ⟨by linarith,by linarith⟩
  · have hl : 1/2 < along := lt_of_not_ge hlong
    have href : max 0 (s.width-along+ξ) ≤ s.width-1/2+ξ :=
      max_le (by linarith) (by linarith)
    exact Or.inr ⟨by linarith,by linarith⟩

#print axioms local_comparison_deleted_gates
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointOriginalComparisonGeometry -/

/- BEGIN ORIGINAL MODULE Analytic.JointSecondProjector ; sha256 2b02fc674230d18a8257ab84b6e6154575d5e9f836eab1eca1b89c012f8bcb18 -/
section





/-! The second projector remains external to the reconstructed row. Its two
extraction scalars give a harmonic ideal weight. First labels are retained
inside the squared window-budget sums before Cauchy--Schwarz. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSecondSectorColumns
open CenteredMomentMobiusRegroup CenteredMomentSecondWindowBudget
open CenteredMomentSecondHarmonicBudget CenteredMomentMobiusHarmonicMass
open CenteredMomentSecondOriginalChildren CenteredMomentCommonHeightEnvelope
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceProfileMass CenteredMomentCommonRadialData
open CenteredMomentSecondHeightFamily
open CenteredMomentCanonicalFirst UniqueFactorizationMonoid
open CenteredMomentActiveDivisorShell CenteredMomentUniformDivisorShell
open CenteredMomentWholeDivisorShell CenteredMomentSlotRatios
open CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle
open CenteredMomentDivisorRetained CenteredMomentDivisorExtraction
open CenteredMomentDivisorRows CenteredMomentDivisorRowEnergy
open CenteredMomentActiveAllocation
local notation "O" => ActualEisensteinCubic.O

def liveSecondProjectors (D : Ideal O) (hD : Supported D)
    (S : Finset (Ideal O)) (Hsource : ℝ) : Finset (Ideal O) :=
  (divisorPool Finset.univ (fun J : sectorPool D hD.1 S => (J : Ideal O))).filter
    (fun L => (L.absNorm : ℝ) ≤ Hsource/(D.absNorm : ℝ))

def jointSecondProjectors {α : Type*} (Λ : Finset α) (D : α → Ideal O)
    (hD : ∀ ℓ, Supported (D ℓ)) (S : α → Finset (Ideal O)) (Hsource : α → ℝ) :
    Finset (Ideal O) := Λ.biUnion (fun ℓ => liveSecondProjectors (D ℓ) (hD ℓ) (S ℓ) (Hsource ℓ))

def jointSecondWindowEnergy {α : Type*} (Λ : Finset α) (D : α → Ideal O)
    (hD : ∀ ℓ, Supported (D ℓ)) (S : α → Finset (Ideal O)) (Hsource : α → ℝ)
    (J : ℕ) (t : α → ℝ) (E : α → Ideal O → ℝ) (L : Ideal O) : ℝ :=
  ∑ ℓ ∈ Λ, if L ∈ liveSecondProjectors (D ℓ) (hD ℓ) (S ℓ) (Hsource ℓ)
    then (windowBudget J (t ℓ) (E ℓ L))^2 else 0

theorem jointSecondWindowEnergy_nonneg {α : Type*} (Λ : Finset α) (D : α → Ideal O)
    (hD : ∀ ℓ, Supported (D ℓ)) (S : α → Finset (Ideal O)) (Hsource : α → ℝ)
    (J : ℕ) (t : α → ℝ) (E : α → Ideal O → ℝ) (L : Ideal O) :
    0 ≤ jointSecondWindowEnergy Λ D hD S Hsource J t E L := by
  apply Finset.sum_nonneg
  intro ℓ hℓ
  split_ifs <;> positivity

/-- The exact two extraction scalars are combined before summing first labels.
The right side has one Hilbert-space sum over those labels for each fixed L. -/
theorem joint_second_projector_cauchy {α : Type*} (Λ : Finset α)
    (D : α → Ideal O) (hD : ∀ ℓ, Supported (D ℓ))
    (S : α → Finset (Ideal O)) (Hsource : α → ℝ)
    (J₁ J₂ : ℕ) (t : α → ℝ) (E₁ E₂ : α → Ideal O → ℝ) :
    (∑ ℓ ∈ Λ, ∑ L ∈ liveSecondProjectors (D ℓ) (hD ℓ) (S ℓ) (Hsource ℓ),
      ‖(moebius L : ℂ)‖ *
        (windowBudget J₁ (t ℓ) (E₁ ℓ L/(L.absNorm : ℝ)) *
          windowBudget J₂ (t ℓ) (E₂ ℓ L/(L.absNorm : ℝ)))) ≤
    ∑ L ∈ jointSecondProjectors Λ D hD S Hsource,
      (‖(moebius L : ℂ)‖/(L.absNorm : ℝ)) *
        (Real.sqrt (jointSecondWindowEnergy Λ D hD S Hsource J₁ t E₁ L) *
          Real.sqrt (jointSecondWindowEnergy Λ D hD S Hsource J₂ t E₂ L)) := by
  let Ds := jointSecondProjectors Λ D hD S Hsource
  let live := fun ℓ => liveSecondProjectors (D ℓ) (hD ℓ) (S ℓ) (Hsource ℓ)
  have hsubset (ℓ : α) (hℓ : ℓ ∈ Λ) : live ℓ ⊆ Ds := by
    intro L hL
    exact Finset.mem_biUnion.mpr ⟨ℓ, hℓ, hL⟩
  have hrow (ℓ : α) (hℓ : ℓ ∈ Λ) :
      (∑ L ∈ live ℓ, ‖(moebius L : ℂ)‖ *
        (windowBudget J₁ (t ℓ) (E₁ ℓ L/(L.absNorm : ℝ)) *
          windowBudget J₂ (t ℓ) (E₂ ℓ L/(L.absNorm : ℝ)))) =
      ∑ L ∈ Ds, if L ∈ live ℓ then ‖(moebius L : ℂ)‖ *
        (windowBudget J₁ (t ℓ) (E₁ ℓ L/(L.absNorm : ℝ)) *
          windowBudget J₂ (t ℓ) (E₂ ℓ L/(L.absNorm : ℝ))) else 0 := by
    have hf : Ds.filter (fun L => L ∈ live ℓ) = live ℓ := by
      ext L
      exact ⟨fun h => (Finset.mem_filter.mp h).2,
        fun h => Finset.mem_filter.mpr ⟨hsubset ℓ hℓ h, h⟩⟩
    rw [← Finset.sum_filter, hf]
  calc
    _ = ∑ L ∈ Ds, ∑ ℓ ∈ Λ, if L ∈ live ℓ then ‖(moebius L : ℂ)‖ *
        (windowBudget J₁ (t ℓ) (E₁ ℓ L/(L.absNorm : ℝ)) *
          windowBudget J₂ (t ℓ) (E₂ ℓ L/(L.absNorm : ℝ))) else 0 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl hrow
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro L hL
      have hcs := Real.sum_mul_le_sqrt_mul_sqrt Λ
        (fun ℓ => if L ∈ live ℓ then windowBudget J₁ (t ℓ) (E₁ ℓ L) else 0)
        (fun ℓ => if L ∈ live ℓ then windowBudget J₂ (t ℓ) (E₂ ℓ L) else 0)
      have hnonneg : 0 ≤ ‖(moebius L : ℂ)‖/(L.absNorm : ℝ) :=
        div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
      calc
        _ = (‖(moebius L : ℂ)‖/(L.absNorm : ℝ)) *
            ∑ ℓ ∈ Λ, (if L ∈ live ℓ then windowBudget J₁ (t ℓ) (E₁ ℓ L) else 0) *
              (if L ∈ live ℓ then windowBudget J₂ (t ℓ) (E₂ ℓ L) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ℓ hℓ
          split_ifs
          · rw [paired_divisor J₁ J₂ (t ℓ) (E₁ ℓ L) (E₂ ℓ L) _ (Nat.cast_nonneg _)]
            ring
          · ring
        _ ≤ _ := by
          convert mul_le_mul_of_nonneg_left hcs hnonneg using 1 <;>
            simp only [jointSecondWindowEnergy, live, apply_ite (fun x : ℝ => x^2), zero_pow (by decide : 2 ≠ 0)]

/-- The actual live second-projector pool has a uniform harmonic cost even
after union over every first label. There is no cardinality factor for Λ. -/
theorem joint_second_projector_mass (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ {α : Type*} (Λ : Finset α) (D : α → Ideal O) (hD : ∀ ℓ, Supported (D ℓ))
        (S : α → Finset (Ideal O)) (Hsource : α → ℝ),
      (∀ ℓ ∈ Λ, Hsource ℓ/((D ℓ).absNorm : ℝ) ≤ Z^B) →
      (∑ L ∈ jointSecondProjectors Λ D hD S Hsource,
        ‖(moebius L : ℂ)‖/(L.absNorm : ℝ)) ≤ C*Z^δ := by
  obtain ⟨C, hC, hmass⟩ := full_mass_subpower B δ hB hδ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro α Λ D hD S Hsource hcap
  apply hZ.2
  intro L hL hμ
  obtain ⟨ℓ, hℓ, hLL⟩ := Finset.mem_biUnion.mp hL
  exact (Finset.mem_filter.mp hLL).2.trans (hcap ℓ hℓ)

/-- Paired extraction pays the full second-projector count while keeping the
first-label direct sums as the only child norm budgets. -/
theorem joint_second_projector_budget (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ {α : Type*} (Λ : Finset α) (D : α → Ideal O) (hD : ∀ ℓ, Supported (D ℓ))
        (S : α → Finset (Ideal O)) (Hsource : α → ℝ),
      (∀ ℓ ∈ Λ, Hsource ℓ/((D ℓ).absNorm : ℝ) ≤ Z^B) →
      ∀ (J₁ J₂ : ℕ) (t : α → ℝ) (E₁ E₂ : α → Ideal O → ℝ) (F₁ F₂ : ℝ),
      (∀ L ∈ jointSecondProjectors Λ D hD S Hsource,
        jointSecondWindowEnergy Λ D hD S Hsource J₁ t E₁ L ≤ F₁) →
      (∀ L ∈ jointSecondProjectors Λ D hD S Hsource,
        jointSecondWindowEnergy Λ D hD S Hsource J₂ t E₂ L ≤ F₂) →
      (∑ ℓ ∈ Λ, ∑ L ∈ liveSecondProjectors (D ℓ) (hD ℓ) (S ℓ) (Hsource ℓ),
        ‖(moebius L : ℂ)‖ *
          (windowBudget J₁ (t ℓ) (E₁ ℓ L/(L.absNorm : ℝ)) *
            windowBudget J₂ (t ℓ) (E₂ ℓ L/(L.absNorm : ℝ)))) ≤
        C*Z^δ*(Real.sqrt F₁*Real.sqrt F₂) := by
  obtain ⟨C, hC, hmass⟩ := joint_second_projector_mass B δ hB hδ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro α Λ D hD S Hsource hcap J₁ J₂ t E₁ E₂ F₁ F₂ hF₁ hF₂
  apply (joint_second_projector_cauchy Λ D hD S Hsource J₁ J₂ t E₁ E₂).trans
  calc
    _ ≤ ∑ L ∈ jointSecondProjectors Λ D hD S Hsource,
        (‖(moebius L : ℂ)‖/(L.absNorm : ℝ))*(Real.sqrt F₁*Real.sqrt F₂) := by
      apply Finset.sum_le_sum
      intro L hL
      gcongr
      · exact hF₁ L hL
      · exact hF₂ L hL
    _ = (∑ L ∈ jointSecondProjectors Λ D hD S Hsource,
        ‖(moebius L : ℂ)‖/(L.absNorm : ℝ))*(Real.sqrt F₁*Real.sqrt F₂) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hZ.2 Λ D hD S Hsource hcap) (by positivity)

/-- These are the literal extraction envelopes of the source. Pairing them
extracts exactly one inverse ideal norm, including the subunit convention. -/
theorem actual_second_envelope_extraction {ι : Type*} [Fintype ι]
    (s : Input ι) (C D L : Ideal O) (Ce Z δ E₁ E₂ t : ℝ) (J₁ J₂ : ℕ) :
    windowBudget J₁ t (envelope s C L Ce Z δ E₁) *
      windowBudget J₂ t (envelope s D L Ce Z δ E₂) =
    (windowBudget J₁ t (core s C Ce Z δ E₁) *
      windowBudget J₂ t (core s D Ce Z δ E₂))/(L.absNorm : ℝ) := by
  rw [envelope_eq_core, envelope_eq_core, paired_divisor _ _ _ _ _ _ (Nat.cast_nonneg _)]

/-- Specialization to the actual source extraction envelopes, retaining all
first labels in the two joint window-energy sums. -/
theorem actual_joint_second_envelope_budget (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ {α ι : Type*} [Fintype ι] (Λ : Finset α) (s : α → Input ι)
        (C D : α → Ideal O) (hD : ∀ ℓ, Supported (D ℓ))
        (S : α → Finset (Ideal O)) (Hsource : α → ℝ),
      (∀ ℓ ∈ Λ, Hsource ℓ/((D ℓ).absNorm : ℝ) ≤ Z^B) →
      ∀ (Ce : ℝ) (J₁ J₂ : ℕ) (t : α → ℝ)
        (E₁ E₂ : α → Ideal O → ℝ) (F₁ F₂ : ℝ),
      (∀ L ∈ jointSecondProjectors Λ D hD S Hsource,
        jointSecondWindowEnergy Λ D hD S Hsource J₁ t
          (fun ℓ L => core (s ℓ) (C ℓ) Ce Z δ (E₁ ℓ L)) L ≤ F₁) →
      (∀ L ∈ jointSecondProjectors Λ D hD S Hsource,
        jointSecondWindowEnergy Λ D hD S Hsource J₂ t
          (fun ℓ L => core (s ℓ) (D ℓ) Ce Z δ (E₂ ℓ L)) L ≤ F₂) →
      (∑ ℓ ∈ Λ, ∑ L ∈ liveSecondProjectors (D ℓ) (hD ℓ) (S ℓ) (Hsource ℓ),
        ‖(moebius L : ℂ)‖ *
          (windowBudget J₁ (t ℓ) (envelope (s ℓ) (C ℓ) L Ce Z δ (E₁ ℓ L)) *
            windowBudget J₂ (t ℓ) (envelope (s ℓ) (D ℓ) L Ce Z δ (E₂ ℓ L)))) ≤
        K*Z^δ*(Real.sqrt F₁*Real.sqrt F₂) := by
  obtain ⟨K, hK, hbudget⟩ := joint_second_projector_budget B δ hB hδ
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbudget] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro α ι _ Λ s C D hD S Hsource hcap Ce J₁ J₂ t E₁ E₂ F₁ F₂ hF₁ hF₂
  simpa only [envelope_eq_core] using hZ.2 Λ D hD S Hsource hcap J₁ J₂ t
    (fun ℓ L => core (s ℓ) (C ℓ) Ce Z δ (E₁ ℓ L))
    (fun ℓ L => core (s ℓ) (D ℓ) Ce Z δ (E₂ ℓ L)) F₁ F₂ hF₁ hF₂

/-- The exact physical prefactor identity can be summed over first labels
with arbitrary weights. It introduces no independent first-label count. -/
theorem joint_physicalBlock_norm {α : Type*} (Λ : Finset α) (weight : α → ℝ)
    (η : α → Character) (t : α → ℝ) (S : α → Finset (Ideal O))
    (β : α → Ideal O → ℂ) (C D : α → Ideal O)
    (hC : ∀ ℓ, Supported (C ℓ)) (hD : ∀ ℓ, Supported (D ℓ))
    (U : ∀ ℓ, Finset (CommonIndex (C ℓ) (D ℓ)))
    (R : α → ℝ) (rows : α → Finset O) (hrows : ∀ ℓ, ∀ z ∈ rows ℓ, z ≠ 0)
    (W : 𝓢(ℝ,ℂ)) (K : α → ℝ) (hK : ∀ ℓ, 0 < K ℓ) (n : α → Fin 4 → ℤ) :
    (∑ ℓ ∈ Λ, weight ℓ * ‖physicalBlock (η ℓ) (t ℓ) (S ℓ) (β ℓ)
      (C ℓ) (D ℓ) (hC ℓ) (hD ℓ) (U ℓ) (R ℓ) (rows ℓ) W (K ℓ) (n ℓ)‖) =
    ∑ ℓ ∈ Λ, (weight ℓ * outerScalar (C ℓ) (D ℓ) (K ℓ) (n ℓ) *
      normalizer (C ℓ) (D ℓ) (U ℓ)) *
      ‖normalizedBlock (η ℓ) (t ℓ) (S ℓ) (β ℓ)
        (C ℓ) (D ℓ) (hC ℓ) (hD ℓ) (U ℓ) (R ℓ) (rows ℓ) W (K ℓ) (n ℓ)‖ := by
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  have ho : 0 ≤ outerScalar (C ℓ) (D ℓ) (K ℓ) (n ℓ) := by
    unfold outerScalar
    have hk := hK ℓ
    positivity
  have hn : 0 ≤ normalizer (C ℓ) (D ℓ) (U ℓ) := (normalizer_pos _ _ (hC ℓ) _).le
  rw [physicalBlock_eq _ _ _ _ _ _ _ _ _ _ _ (hrows ℓ) _ _ (hK ℓ),
    norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ho,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
  ring

/-- The literal reduction factors pay both the projector ideal and all
active allocations. The constants precede the surviving slot sets, source
characters, frequencies, rows, and projector pool. -/
theorem actual_second_allocation_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lo hi : ι → ℝ) (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (J L : Finset ι) (s : Source J) (v : Source L),
      (∀ i : J, s.lo i = lo i) → (∀ i : J, s.hi i = hi i) →
      (∀ i : L, v.lo i = lo i) → (∀ i : L, v.hi i = hi i) →
      ∀ Ds : Finset (Ideal O),
      (∀ D ∈ Ds, (moebius D : ℂ) ≠ 0 → (D.absNorm : ℝ) ≤ Z^B) →
      (∑ D ∈ Ds, ‖(moebius D : ℂ)‖ *
        ∑ a ∈ s.active D, ∑ b ∈ v.active D,
          1 / Real.sqrt (formalReductionFactor D a s.P *
            formalReductionFactor D b v.P)) ≤ C*Z^δ := by
  obtain ⟨C₁, hC₁, hshell⟩ := paired_shell_subpower lo hi B (δ/2) hB (by positivity)
  obtain ⟨C₂, hC₂, hcount⟩ := selected_card_subpower B (δ/2) hB (by positivity)
  refine ⟨C₁*C₂, mul_pos hC₁ hC₂, ?_⟩
  filter_upwards [hcount] with Z hZ
  have hz : 0 < Z := zero_lt_one.trans hZ.1
  refine ⟨hZ.1, ?_⟩
  intro J L s v hslo hshi hvlo hvhi Ds hcap
  rw [sum_norm_moebius_shells]
  calc
    _ ≤ ∑ n ∈ selectedShells Ds, C₁*Z^(δ/2) := by
      apply Finset.sum_le_sum
      intro n hn
      have hb := selected_scale_bounds Ds (Z^B) hcap n hn
      calc
        _ ≤ ∑ D ∈ shell Ds n, ∑ a ∈ s.active D, ∑ b ∈ v.active D,
            1 / Real.sqrt (formalReductionFactor D a s.P *
              formalReductionFactor D b v.P) := by
          apply Finset.sum_le_sum
          intro D hD
          exact (mul_le_mul_of_nonneg_right (moebius_norm_le_one D) (by positivity)).trans_eq
            (one_mul _)
        _ ≤ _ := hshell J L s v hslo hshi hvlo hvhi (shell Ds n)
          (fun D hD => (shell_member_data Ds n D hD).2.2.1) _ Z hb.1 hZ.1 hb.2
          (fun D hD => (shell_member_data Ds n D hD).2.2.2.2.1)
          (fun D hD => (shell_member_data Ds n D hD).2.2.2.2.2)
    _ = ((selectedShells Ds).card : ℝ) * (C₁*Z^(δ/2)) := by simp
    _ ≤ (C₂*Z^(δ/2)) * (C₁*Z^(δ/2)) :=
      mul_le_mul_of_nonneg_right (hZ.2 Ds hcap) (by positivity)
    _ = (C₁*C₂)*Z^δ := by
      rw [mul_mul_mul_comm, ← Real.rpow_add (zero_lt_one.trans hZ.1)]
      rw [show δ/2+δ/2=δ by ring]
      ring

/-- The high-branch scalar sum acts boundedly on the direct sum of first
labels. The two energies can themselves be sums over reconstructed rows;
only their joint sums occur, and the projector is never required to divide
any reconstructed row. -/
theorem actual_joint_second_allocation_budget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lo hi : ι → ℝ) (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ {α : Type*} (Λ : Finset α) (J L : α → Finset ι)
        (s : ∀ ℓ, Source (J ℓ)) (v : ∀ ℓ, Source (L ℓ)),
      (∀ ℓ, ∀ i : J ℓ, (s ℓ).lo i = lo i) →
      (∀ ℓ, ∀ i : J ℓ, (s ℓ).hi i = hi i) →
      (∀ ℓ, ∀ i : L ℓ, (v ℓ).lo i = lo i) →
      (∀ ℓ, ∀ i : L ℓ, (v ℓ).hi i = hi i) →
      ∀ Ds : α → Finset (Ideal O),
      (∀ ℓ ∈ Λ, ∀ D ∈ Ds ℓ, (moebius D : ℂ) ≠ 0 → (D.absNorm : ℝ) ≤ Z^B) →
      ∀ E₁ E₂ : α → ℝ, (∀ ℓ, 0 ≤ E₁ ℓ) → (∀ ℓ, 0 ≤ E₂ ℓ) →
      (∑ ℓ ∈ Λ, (∑ D ∈ Ds ℓ, ‖(moebius D : ℂ)‖ *
        ∑ a ∈ (s ℓ).active D, ∑ b ∈ (v ℓ).active D,
          1 / Real.sqrt (formalReductionFactor D a (s ℓ).P *
            formalReductionFactor D b (v ℓ).P)) *
        (Real.sqrt (E₁ ℓ) * Real.sqrt (E₂ ℓ))) ≤
        C*Z^δ*(Real.sqrt (∑ ℓ ∈ Λ, E₁ ℓ) * Real.sqrt (∑ ℓ ∈ Λ, E₂ ℓ)) := by
  obtain ⟨C, hC, hmass⟩ := actual_second_allocation_mass lo hi B δ hB hδ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmass] with Z hZ
  have hz : 0 < Z := zero_lt_one.trans hZ.1
  refine ⟨hZ.1, ?_⟩
  intro α Λ J L s v hslo hshi hvlo hvhi Ds hcap E₁ E₂ hE₁ hE₂
  calc
    _ ≤ ∑ ℓ ∈ Λ, (C*Z^δ)*(Real.sqrt (E₁ ℓ)*Real.sqrt (E₂ ℓ)) := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      exact mul_le_mul_of_nonneg_right
        (hZ.2 (J ℓ) (L ℓ) (s ℓ) (v ℓ) (hslo ℓ) (hshi ℓ) (hvlo ℓ) (hvhi ℓ)
          (Ds ℓ) (hcap ℓ hℓ)) (by positivity)
    _ = (C*Z^δ)*(∑ ℓ ∈ Λ, Real.sqrt (E₁ ℓ)*Real.sqrt (E₂ ℓ)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le Λ hE₁ hE₂) (by positivity)

def secondAllocatedValue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Source ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (z : O) : ℂ :=
  (Real.sqrt (s.X₁*s.X₂*∏ i, s.P i) : ℂ)⁻¹ *
    allocatedRectangle s.η s.m s.A z s.t s.slots
      (fun i I => s.ν i I*s.W i ((I.absNorm : ℝ)/s.P i)) D a
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂

def secondRetainedEnergy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Source ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (z : O) : ℝ :=
  ‖allocatedPositiveRow s.η s.m s.A z s.t s.slots
    (fun i I => s.ν i I*s.W i ((I.absNorm : ℝ)/s.P i)) s.P D a
    s.W₁ s.W₂ s.X₁ s.X₂‖^2 +
  ‖allocatedPositiveRow s.η s.m s.A z s.t s.slots
    (fun i I => s.ν i I*s.W i ((I.absNorm : ℝ)/s.P i)) s.P D a
    s.W₁ s.W₂ s.Y₁ s.Y₂‖^2

def secondMaskedValue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Source ι) (D : Ideal O) (z : O) : ℂ :=
  (Real.sqrt (s.X₁*s.X₂*∏ i, s.P i) : ℂ)⁻¹ *
    maskedRectangle s.η s.m s.A z s.t s.slots
      (fun i I => s.ν i I*s.W i ((I.absNorm : ℝ)/s.P i)) D
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂

/-- The complete projector mask is split into precisely its active
allocations before any estimate or count. -/
theorem secondMaskedValue_eq_active {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Source ι) (D : Ideal O) (hD : Squarefree D) (z : O)
    (b₁ b₂ : ℝ) (hW₁ : Function.support s.W₁ ⊆ Set.Iic b₁)
    (hW₂ : Function.support s.W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < s.X₁) (hX₂ : 0 < s.X₂) (hY₁ : 0 < s.Y₁) (hY₂ : 0 < s.Y₂) :
    secondMaskedValue s D z = ∑ a ∈ s.active D, secondAllocatedValue s D a z := by
  unfold secondMaskedValue
  rw [masked_eq_active_allocations s.η s.m s.A z s.t s.slots
    (fun i I => s.ν i I*s.W i ((I.absNorm : ℝ)/s.P i)) D hD
    s.W₁ s.W₂ b₁ b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂,
    Finset.mul_sum]
  rfl

def secondExtractionNumerator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ℝ) (b₁ b₂ : ℝ) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : ℝ :=
  (2*(max 1 b₁*max 1 b₂))*(∏ i ∈ frozenIndices D a, M i)^2

/-- Literal normalized allocated rectangles expose the reduction factor;
the remaining two terms are the actual retained positive rows. -/
theorem actual_second_allocated_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Source ι) (M : ι → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hcoeff : ∀ i, ∀ I ∈ s.slots i,
      ‖s.ν i I*s.W i ((I.absNorm : ℝ)/s.P i)‖ ≤ M i)
    (b₁ b₂ : ℝ) (hW₁ : Function.support s.W₁ ⊆ Set.Iic b₁)
    (hW₂ : Function.support s.W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < s.X₁) (hX₂ : 0 < s.X₂) (hY₁ : 0 < s.Y₁) (hY₂ : 0 < s.Y₂)
    (hXY : s.Y₁*s.Y₂ = s.X₁*s.X₂)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (z : O) :
    ‖secondAllocatedValue s D a z‖ ≤
      Real.sqrt (secondExtractionNumerator M b₁ b₂ D a * secondRetainedEnergy s D a z) /
        Real.sqrt (formalReductionFactor D a s.P) := by
  have hn : 0 ≤ secondExtractionNumerator M b₁ b₂ D a := by
    unfold secondExtractionNumerator
    positivity
  have he : 0 ≤ secondRetainedEnergy s D a z := by
    unfold secondRetainedEnergy
    positivity
  have h := allocated_to_retained_energy s.η s.m s.A z s.t s.slots s.prime
    (fun i I => s.ν i I*s.W i ((I.absNorm : ℝ)/s.P i)) M s.P hM s.P_pos hcoeff
    D a s.W₁ s.W₂ b₁ b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ rfl hXY
  have hh : ‖secondAllocatedValue s D a z‖^2 ≤
      secondExtractionNumerator M b₁ b₂ D a * secondRetainedEnergy s D a z /
        formalReductionFactor D a s.P := by
    convert h using 1 <;>
      dsimp [secondAllocatedValue, secondExtractionNumerator, secondRetainedEnergy]
    ring
  have hr := Real.le_sqrt_of_sq_le hh
  rwa [Real.sqrt_div (mul_nonneg hn he)] at hr

/-- Pairing the actual extracted rectangles produces exactly the scalar
summed by `actual_second_allocation_mass`. -/
theorem actual_second_allocated_pair {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (s : Source ι) (v : Source κ) (M : ι → ℝ) (N : κ → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hN : ∀ i, 0 ≤ N i)
    (hscoeff : ∀ i, ∀ I ∈ s.slots i,
      ‖s.ν i I*s.W i ((I.absNorm : ℝ)/s.P i)‖ ≤ M i)
    (hvcoeff : ∀ i, ∀ I ∈ v.slots i,
      ‖v.ν i I*v.W i ((I.absNorm : ℝ)/v.P i)‖ ≤ N i)
    (b₁ b₂ c₁ c₂ : ℝ)
    (hsW₁ : Function.support s.W₁ ⊆ Set.Iic b₁)
    (hsW₂ : Function.support s.W₂ ⊆ Set.Iic b₂)
    (hvW₁ : Function.support v.W₁ ⊆ Set.Iic c₁)
    (hvW₂ : Function.support v.W₂ ⊆ Set.Iic c₂)
    (hsX₁ : 0 < s.X₁) (hsX₂ : 0 < s.X₂) (hsY₁ : 0 < s.Y₁) (hsY₂ : 0 < s.Y₂)
    (hvX₁ : 0 < v.X₁) (hvX₂ : 0 < v.X₂) (hvY₁ : 0 < v.Y₁) (hvY₂ : 0 < v.Y₂)
    (hsXY : s.Y₁*s.Y₂ = s.X₁*s.X₂) (hvXY : v.Y₁*v.Y₂ = v.X₁*v.X₂)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ ⊕ Fin 2))) (z w : O) :
    ‖secondAllocatedValue s D a z‖ * ‖secondAllocatedValue v D b w‖ ≤
      (1 / Real.sqrt (formalReductionFactor D a s.P * formalReductionFactor D b v.P)) *
        (Real.sqrt (secondExtractionNumerator M b₁ b₂ D a * secondRetainedEnergy s D a z) *
         Real.sqrt (secondExtractionNumerator N c₁ c₂ D b * secondRetainedEnergy v D b w)) := by
  have hs := actual_second_allocated_norm s M hM hscoeff b₁ b₂ hsW₁ hsW₂
    hsX₁ hsX₂ hsY₁ hsY₂ hsXY D a z
  have hv := actual_second_allocated_norm v N hN hvcoeff c₁ c₂ hvW₁ hvW₂
    hvX₁ hvX₂ hvY₁ hvY₂ hvXY D b w
  have hF : 0 ≤ formalReductionFactor D a s.P :=
    (mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _ => s.P_pos i))).le
  apply (mul_le_mul hs hv (norm_nonneg _) (by positivity)).trans_eq
  rw [div_mul_div_comm, ← Real.sqrt_mul hF]
  ring

/-- A complete pair of actual second masks is bounded using the literal
paired extraction scalars. No allocation cardinality or first-label
cardinality is spent in this step. -/
theorem actual_second_masked_pair {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (s : Source ι) (v : Source κ) (M : ι → ℝ) (N : κ → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hN : ∀ i, 0 ≤ N i)
    (hscoeff : ∀ i, ∀ I ∈ s.slots i,
      ‖s.ν i I*s.W i ((I.absNorm : ℝ)/s.P i)‖ ≤ M i)
    (hvcoeff : ∀ i, ∀ I ∈ v.slots i,
      ‖v.ν i I*v.W i ((I.absNorm : ℝ)/v.P i)‖ ≤ N i)
    (b₁ b₂ c₁ c₂ : ℝ)
    (hsW₁ : Function.support s.W₁ ⊆ Set.Iic b₁)
    (hsW₂ : Function.support s.W₂ ⊆ Set.Iic b₂)
    (hvW₁ : Function.support v.W₁ ⊆ Set.Iic c₁)
    (hvW₂ : Function.support v.W₂ ⊆ Set.Iic c₂)
    (hsX₁ : 0 < s.X₁) (hsX₂ : 0 < s.X₂) (hsY₁ : 0 < s.Y₁) (hsY₂ : 0 < s.Y₂)
    (hvX₁ : 0 < v.X₁) (hvX₂ : 0 < v.X₂) (hvY₁ : 0 < v.Y₁) (hvY₂ : 0 < v.Y₂)
    (hsXY : s.Y₁*s.Y₂ = s.X₁*s.X₂) (hvXY : v.Y₁*v.Y₂ = v.X₁*v.X₂)
    (D : Ideal O) (hD : Squarefree D) (z w : O) :
    ‖secondMaskedValue s D z‖ * ‖secondMaskedValue v D w‖ ≤
      ∑ a ∈ s.active D, ∑ b ∈ v.active D,
        (1 / Real.sqrt (formalReductionFactor D a s.P * formalReductionFactor D b v.P)) *
          (Real.sqrt (secondExtractionNumerator M b₁ b₂ D a * secondRetainedEnergy s D a z) *
           Real.sqrt (secondExtractionNumerator N c₁ c₂ D b * secondRetainedEnergy v D b w)) := by
  rw [secondMaskedValue_eq_active s D hD z b₁ b₂ hsW₁ hsW₂ hsX₁ hsX₂ hsY₁ hsY₂,
    secondMaskedValue_eq_active v D hD w c₁ c₂ hvW₁ hvW₂ hvX₁ hvX₂ hvY₁ hvY₂]
  calc
    _ ≤ (∑ a ∈ s.active D, ‖secondAllocatedValue s D a z‖) *
        (∑ b ∈ v.active D, ‖secondAllocatedValue v D b w‖) := by
      exact mul_le_mul (norm_sum_le _ _) (norm_sum_le _ _) (norm_nonneg _) (by positivity)
    _ = ∑ a ∈ s.active D, ∑ b ∈ v.active D,
        ‖secondAllocatedValue s D a z‖ * ‖secondAllocatedValue v D b w‖ := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb =>
      actual_second_allocated_pair s v M N hM hN hscoeff hvcoeff b₁ b₂ c₁ c₂
        hsW₁ hsW₂ hvW₁ hvW₂ hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂
        hsXY hvXY D a b z w))

#print axioms joint_second_projector_cauchy
#print axioms joint_second_projector_mass
#print axioms joint_second_projector_budget
#print axioms actual_joint_second_envelope_budget
#print axioms joint_physicalBlock_norm
#print axioms actual_second_allocation_mass
#print axioms actual_joint_second_allocation_budget
#print axioms actual_second_allocated_norm
#print axioms actual_second_allocated_pair
#print axioms actual_second_masked_pair
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSecondProjector -/

/- BEGIN ORIGINAL MODULE Analytic.JointWeightedFibers ; sha256 62c4477bf121e1b1cbe5fda0d046bc636179db6d1178941d9606850b33f29062 -/
section



/-! Extraction and allocation fibers are paid by their weight mass. One
maximizing branch is selected at each arithmetic label before invoking a
joint bound; the arithmetic labels are never counted a second time. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic

variable {α : Type*} {β : α → Type*}
local instance weightedFiberDecidableEq {κ : Type*} : DecidableEq κ := Classical.decEq _

def liveFiberLabels (labels : Finset α) (fiber : (a : α) → Finset (β a)) : Finset α :=
  labels.filter (fun a => (fiber a).Nonempty)

/-- Empty fibers disappear exactly. Every other label selects just one
branch, and its entire fiber costs only the supplied mass cap. -/
theorem exists_joint_fiber_maximizers
    (labels : Finset α) (fiber : (a : α) → Finset (β a))
    (weight value : (a : α) → β a → ℝ) (B : ℝ)
    (hweight : ∀ a ∈ labels, ∀ b ∈ fiber a, 0 ≤ weight a b)
    (hvalue : ∀ a ∈ labels, ∀ b ∈ fiber a, 0 ≤ value a b)
    (hmass : ∀ a ∈ labels, (∑ b ∈ fiber a, weight a b) ≤ B) :
    ∃ pick : (a : liveFiberLabels labels fiber) → β a,
      (∀ a : liveFiberLabels labels fiber, pick a ∈ fiber a) ∧
      (∀ a : liveFiberLabels labels fiber, ∀ b ∈ fiber a, value a b ≤ value a (pick a)) ∧
      (∑ a ∈ labels, ∑ b ∈ fiber a, weight a b*value a b) ≤
        B*(∑ a : liveFiberLabels labels fiber, value a (pick a)) := by
  have hmax (a : liveFiberLabels labels fiber) :
      ∃ b ∈ fiber a, ∀ c ∈ fiber a, value a c ≤ value a b :=
    Finset.exists_max_image (fiber a) (value a) (Finset.mem_filter.mp a.property).2
  choose pick hpick hmax using hmax
  refine ⟨pick,hpick,hmax,?_⟩
  have heq : (∑ a ∈ labels, ∑ b ∈ fiber a, weight a b*value a b) =
      ∑ a : liveFiberLabels labels fiber, ∑ b ∈ fiber a, weight a b*value a b := by
    rw [Finset.sum_coe_sort (liveFiberLabels labels fiber)
      (fun a => ∑ b ∈ fiber a, weight a b*value a b)]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a ha hnot
    have hempty : fiber a = ∅ := by
      by_contra hn
      exact hnot (Finset.mem_filter.mpr ⟨ha,Finset.nonempty_iff_ne_empty.mpr hn⟩)
    rw [hempty,Finset.sum_empty]
  rw [heq]
  calc
    _ ≤ ∑ a : liveFiberLabels labels fiber, B*value a (pick a) := by
      apply Finset.sum_le_sum
      intro a ha
      have halabel := (Finset.mem_filter.mp a.property).1
      calc
        _ ≤ ∑ b ∈ fiber a, weight a b*value a (pick a) :=
          Finset.sum_le_sum (fun b hb =>
            mul_le_mul_of_nonneg_left (hmax a b hb) (hweight a halabel b hb))
        _ = (∑ b ∈ fiber a, weight a b)*value a (pick a) := (Finset.sum_mul _ _ _).symm
        _ ≤ B*value a (pick a) :=
          mul_le_mul_of_nonneg_right (hmass a halabel) (hvalue a halabel (pick a) (hpick a))
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- A joint estimate uniform over one chosen branch at each label transfers
to the complete weighted fiber sum using only the fiber mass. -/
theorem joint_weighted_fibers
    (labels : Finset α) (fiber : (a : α) → Finset (β a))
    (weight value : (a : α) → β a → ℝ) (B E : ℝ) (hB : 0 ≤ B)
    (hweight : ∀ a ∈ labels, ∀ b ∈ fiber a, 0 ≤ weight a b)
    (hvalue : ∀ a ∈ labels, ∀ b ∈ fiber a, 0 ≤ value a b)
    (hmass : ∀ a ∈ labels, (∑ b ∈ fiber a, weight a b) ≤ B)
    (hchoice : ∀ (S : Finset α), S ⊆ labels →
      ∀ pick : (a : S) → β a, (∀ a : S, pick a ∈ fiber a) →
      (∑ a : S, value a (pick a)) ≤ E) :
    (∑ a ∈ labels, ∑ b ∈ fiber a, weight a b*value a b) ≤ B*E := by
  obtain ⟨pick,hpick,_,hbound⟩ := exists_joint_fiber_maximizers labels fiber weight value B
    hweight hvalue hmass
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (hchoice (liveFiberLabels labels fiber) (Finset.filter_subset _ _) pick hpick) hB)

#print axioms exists_joint_fiber_maximizers
#print axioms joint_weighted_fibers
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointWeightedFibers -/

/- BEGIN ORIGINAL MODULE Cycle25.Arithmetic.Endpoint ; sha256 51dadfc13d1cc0d7d28b6e685f0be2c2503b9e011cd6866e2bc53abc00942fb9 -/
section





/-! Exact arithmetic for T1 of the selected Cycle25 proof packet.
The endpoint is an algebraic real, specified by its polynomial and isolating interval.
These declarations make no assertion about Hecke or Dirichlet L-functions. -/

namespace Cycle25.Arithmetic

def quartic (x : ℝ) : ℝ := 927*x^4 - 3135*x^3 + 2433*x^2 + 275*x - 100
noncomputable def rootLo : ℝ := 16712007850680 / 100000000000000
noncomputable def rootHi : ℝ := 16712007850682 / 100000000000000

theorem rootLo_lt_rootHi : rootLo < rootHi := by norm_num [rootLo, rootHi]
theorem rootLo_coarse : (1:ℝ)/6 < rootLo := by norm_num [rootLo]
theorem rootHi_coarse : rootHi < (1:ℝ)/5 := by norm_num [rootHi]
theorem quartic_rootLo_neg : quartic rootLo < 0 := by norm_num [quartic, rootLo]
theorem quartic_rootHi_pos : 0 < quartic rootHi := by norm_num [quartic, rootHi]

theorem quartic_continuous : Continuous quartic := by unfold quartic; fun_prop

theorem quartic_hasDerivAt (x : ℝ) :
    HasDerivAt quartic (3708*x^3 - 9405*x^2 + 4866*x + 275) x := by
  unfold quartic
  convert ((((((hasDerivAt_id x).pow 4).const_mul 927).sub
    (((hasDerivAt_id x).pow 3).const_mul 3135)).add
    (((hasDerivAt_id x).pow 2).const_mul 2433)).add
    ((hasDerivAt_id x).const_mul 275)).sub_const 100 using 1
  · ext y; simp
  · simp; ring

theorem quartic_derivative_lower {x : ℝ} (hx : x ∈ Set.Icc (1/6:ℝ) (1/5)) :
    (3549:ℝ)/5 ≤ 3708*x^3 - 9405*x^2 + 4866*x + 275 := by
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hx2 : x^2 ≤ (1:ℝ)/25 := by nlinarith [hx.2]
  have hx3 : 0 ≤ x^3 := pow_nonneg hx0 _
  nlinarith [hx.1]

theorem quartic_strictMonoOn : StrictMonoOn quartic (Set.Icc (1/6:ℝ) (1/5)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) quartic_continuous.continuousOn
  intro x hx
  rw [(quartic_hasDerivAt x).deriv]
  have hxc : x ∈ Set.Icc (1/6:ℝ) (1/5) := interior_subset hx
  linarith [quartic_derivative_lower hxc]

theorem exists_isolated_root : ∃ x : ℝ, rootLo < x ∧ x < rootHi ∧ quartic x = 0 := by
  have h := intermediate_value_Icc (le_of_lt rootLo_lt_rootHi)
    quartic_continuous.continuousOn
  obtain ⟨x, hx, hpx⟩ := h (show (0:ℝ) ∈ Set.Icc (quartic rootLo) (quartic rootHi) from
    ⟨le_of_lt quartic_rootLo_neg, le_of_lt quartic_rootHi_pos⟩)
  refine ⟨x, ?_, ?_, hpx⟩
  · exact lt_of_le_of_ne hx.1 (by intro he; subst x; linarith [quartic_rootLo_neg])
  · exact lt_of_le_of_ne hx.2 (by intro he; subst x; linarith [quartic_rootHi_pos])

noncomputable def ell0 : ℝ := Classical.choose exists_isolated_root
theorem ell0_lo : rootLo < ell0 := (Classical.choose_spec exists_isolated_root).1
theorem ell0_hi : ell0 < rootHi := (Classical.choose_spec exists_isolated_root).2.1
theorem ell0_quartic : quartic ell0 = 0 := (Classical.choose_spec exists_isolated_root).2.2
theorem ell0_coarse : ell0 ∈ Set.Icc (1/6:ℝ) (1/5) :=
  ⟨le_of_lt (rootLo_coarse.trans ell0_lo), le_of_lt (ell0_hi.trans rootHi_coarse)⟩

theorem quartic_root_unique {x : ℝ} (hx : x ∈ Set.Icc (1/6:ℝ) (1/5))
    (hp : quartic x = 0) : x = ell0 :=
  quartic_strictMonoOn.injOn hx ell0_coarse (hp.trans ell0_quartic.symm)

noncomputable def b0 : ℝ := 11/12 - ell0/4
noncomputable def kappa0 : ℝ := (5-3*ell0)/6
noncomputable def theta : ℝ := 683505193/781250000

theorem kappa0_eq : kappa0 = 2*b0-1 := by unfold kappa0 b0; ring
theorem b0_lt_theta : b0 < theta := by
  have h := ell0_lo
  norm_num [rootLo] at h
  unfold b0 theta
  linarith

theorem theta_gap : 0 < theta-b0 ∧ theta-b0 < (4:ℝ)/100000000000000 := by
  constructor
  · linarith [b0_lt_theta]
  · have h := ell0_hi
    norm_num [rootHi] at h
    unfold theta b0
    linarith

theorem kappa0_range : (7:ℝ)/10 < kappa0 ∧ kappa0 < (3:ℝ)/4 := by
  have h := ell0_lo
  have h' := ell0_hi
  norm_num [rootLo, rootHi] at h h'
  unfold kappa0
  constructor <;> linarith

theorem theta_catalogue_chain : theta < (10499:ℝ)/12000 ∧
    (10499:ℝ)/12000 < 874957019420098946128604623/1000000000000000000000000000 ∧
    (874957019420098946128604623:ℝ)/1000000000000000000000000000 < 7/8 := by
  norm_num [theta]

end Cycle25.Arithmetic
end
/- END ORIGINAL MODULE Cycle25.Arithmetic.Endpoint -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Continuation ; sha256 225fc957beb9ef7a221c8acd7a940fe97260969b7d40aba0c40af3a88e16cdfc -/
section




/-!
The continuation and actual L-function transfer for a variable boundary.
These are infrastructure lemmas: their probe hypotheses must be discharged
by the physical estimates before they yield a new zero-free theorem.
-/

noncomputable section
open Filter Asymptotics
open scoped Classical
open OAI.SevenEighths

namespace Cycle25

def continuationMargin (θ β ω σ : ℝ) : ℝ := min (β - θ - ω) σ

theorem continuationMargin_pos {θ β ω σ : ℝ}
    (hω : ω < β - θ) (hσ : 0 < σ) :
    0 < continuationMargin θ β ω σ :=
  lt_min (sub_pos.mpr hω) hσ

theorem continuation_boundary_gt {θ β ω σ : ℝ} (hω : 0 < ω) :
    θ < β - continuationMargin θ β ω σ := by
  have h : continuationMargin θ β ω σ ≤ β - θ - ω := min_le_left _ _
  linarith

theorem max_signal_exponents (θ β ω σ c : ℝ) :
    max (θ + c + ω) (β + c - σ) =
      (β - continuationMargin θ β ω σ) + c := by
  unfold continuationMargin
  rcases le_total (β - θ - ω) σ with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
    ring
  · rw [min_eq_right h, max_eq_right (by linarith)]
    ring

theorem nonzero_of_probe_bounds (χ : HeckeFamily.Character)
    (H : ℂ → ℂ) (J : ℝ → ℂ) (θ β ω σ c : ℝ)
    (hθ0 : 0 < θ) (hθ7 : θ ≤ (7/8 : ℝ))
    (hβ : β ≤ 1) (hω0 : 0 < ω) (hω : ω < β - θ) (hσ : 0 < σ)
    (hH : AnalyticOnNhd ℂ H {s : ℂ | θ < s.re})
    (hb : ∀ s : ℂ, θ < s.re → ‖H s - 1‖ ≤ 1/2)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (θ+c+ω)))
    (herror : (fun x => J x - HeckeSignal.signal χ H c x) =O[atTop]
      (fun x : ℝ => x ^ (β+c-σ)))
    {ρ : ℂ} (hρ : β - continuationMargin θ β ω σ < ρ.re)
    (hpole : ρ ≠ 1 ∨ χ.residue ≠ 1) : HeckeFamily.LFunction χ ρ ≠ 0 := by
  let a := β - continuationMargin θ β ω σ
  have hθa : θ < a := continuation_boundary_gt hω0
  have ha2 : a < 2 := by
    have hp := continuationMargin_pos hω hσ
    dsimp [a]
    linarith
  have hH7 : AnalyticOnNhd ℂ H {s : ℂ | (7/8 : ℝ) < s.re} :=
    hH.mono (fun _ hs => hθ7.trans_lt hs)
  have hb7 : ∀ s : ℂ, (7/8 : ℝ) < s.re → ‖H s - 1‖ ≤ 1/2 :=
    fun s hs => hb s (hθ7.trans_lt hs)
  have htop : HeckeSignal.signal χ H c =O[atTop]
      (fun x : ℝ => x ^ (a+c)) := by
    simpa only [max_signal_exponents, a] using
      Continuation.common_signal_bound J (HeckeSignal.signal χ H c)
        (θ+c+ω) (β+c-σ) hJ herror
  have hHa : AnalyticOnNhd ℂ H {s : ℂ | a < s.re} :=
    hH.mono (fun _ hs => hθa.trans hs)
  apply Continuation.nonzero_of_regularized_signal a 1 c
    (HeckeFamily.LFunction χ) (HeckeSignal.regularL χ)
    (HeckeSignal.targetRegularizer χ) (Continuation.gaussianMultiplier H)
    (HeckeSignal.signal χ H c)
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (HeckeSignal.regularL_entire χ)).mono (Set.subset_univ _))
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (HeckeSignal.targetRegularizer_entire χ)).mono (Set.subset_univ _))
    (Continuation.gaussianMultiplier_analytic hHa)
    (HeckeSignal.signal_locallyIntegrable χ H hH7.differentiableOn hb7 c)
    htop (HeckeSignal.signal_rapidDecayAtZero χ H hH7.differentiableOn hb7 c)
    ?_ hρ ?_ (HeckeSignal.targetRegularizer_ne_zero χ hpole)
    (Continuation.gaussianMultiplier_ne_zero (hb ρ (hθa.trans hρ)))
  · intro s hs
    have hs1 : 1 < s.re := (le_max_right a 1).trans_lt hs
    have h0 : s ≠ 0 := by intro h; norm_num [h] at hs1
    have h1 : s ≠ 1 := by intro h; norm_num [h] at hs1
    rw [HeckeSignal.regularL_eq χ h0 (Or.inl h1),
      HeckeSignal.signalMellin_eq_amplitude χ H hH7.differentiableOn hb7
        c a ha2 htop hs]
    unfold HeckeSignal.amplitude HeckeSignal.quotient Continuation.gaussianMultiplier
    rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
    have hn := HeckeFamily.LFunction_ne_zero_of_one_lt_re χ hs1
    field_simp
  · apply HeckeSignal.regularL_eq χ _ hpole
    intro h
    rw [h] at hρ
    norm_num at hρ
    linarith

def PrimitiveProbeContract (θ c ω σ : ℝ) : Prop :=
  ∀ η : HeckeFamily.Character,
    FiniteFourier.IsPrimitiveOnIdeals η.residue →
    ∃ (χ : HeckeFamily.Character) (H : ℂ → ℂ) (J : ℝ → ℂ),
      (∀ I, HeckeFamily.idealCoeff χ I =
        if IsCoprime I χ.modulus then HeckeFamily.idealCoeff η I else 0) ∧
      AnalyticOnNhd ℂ H {s : ℂ | θ < s.re} ∧
      (∀ s : ℂ, θ < s.re → ‖H s - 1‖ ≤ 1/2) ∧
      J =O[atTop] (fun x : ℝ => x ^ (θ+c+ω)) ∧
      (fun x => J x - HeckeSignal.signal χ H c x) =O[atTop]
        (fun x : ℝ => x ^ (HeckeZeroSupremum.beta+c-σ))

def UniformCommonProbe (θ c : ℝ) : Prop :=
  θ < HeckeZeroSupremum.beta → ∃ ω σ : ℝ,
    0 < ω ∧ ω < HeckeZeroSupremum.beta - θ ∧ 0 < σ ∧
      PrimitiveProbeContract θ c ω σ

theorem beta_le_of_common_probe {θ c : ℝ}
    (hθ : (1/2 : ℝ) ≤ θ) (hθ7 : θ ≤ (7/8 : ℝ))
    (h : UniformCommonProbe θ c) : HeckeZeroSupremum.beta ≤ θ := by
  by_contra hn
  obtain ⟨ω, σ, hω0, hω, hσ, hcontract⟩ := h (lt_of_not_ge hn)
  have hmargin := continuationMargin_pos hω hσ
  have hboundary := continuation_boundary_gt
    (θ := θ) (β := HeckeZeroSupremum.beta) (σ := σ) hω0
  obtain ⟨η, ρ, hp, hhalf, _, hpole, hz, hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta hmargin (by linarith)
  obtain ⟨χ, H, J, hmask, hH, hb, hJ, herr⟩ := hcontract η hp
  have hχpole : ρ ≠ 1 ∨ χ.residue ≠ 1 := by
    rcases hpole with h1 | hη
    · exact Or.inl h1
    · exact Or.inr (fun hc => hη
        ((HeckeFiniteDeletion.principal_iff_of_mask χ η hmask).mp hc))
  have hzχ : HeckeFamily.LFunction χ ρ = 0 := by
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole χ η hmask
      (by linarith) hχpole, hz, zero_mul]
  exact (nonzero_of_probe_bounds χ H J θ HeckeZeroSupremum.beta ω σ c
    (by linarith) hθ7 HeckeZeroSupremum.beta_le_one hω0 hω hσ
    hH hb hJ herr hnear hχpole) hzχ

theorem hecke_ne_zero_of_common_probe {θ c : ℝ}
    (hθ : (1/2 : ℝ) ≤ θ) (hθ7 : θ ≤ (7/8 : ℝ))
    (h : UniformCommonProbe θ c) (χ : HeckeFamily.Character) (s : ℂ)
    (hs : θ < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    HeckeFamily.LFunction χ s ≠ 0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
    ((beta_le_of_common_probe hθ hθ7 h).trans_lt hs) hpole

theorem dirichlet_of_hecke {θ : ℝ} (hθ : 0 < θ)
    (hH : ∀ (η : HeckeFamily.Character) (s : ℂ), θ < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → HeckeFamily.LFunction η s ≠ 0)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : θ < s.re) (hexc : ¬ (χ = 1 ∧ s = 1)) :
    χ.LFunction s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hexc) hge
  have hs1 : s ≠ 1 := by intro h; simp [h] at hge
  have hs0 : s ≠ 0 := by intro h; simp only [h, Complex.zero_re] at hs; linarith
  have h := hH (HeckeDirichlet.character χ) s hs (Or.inl hs1)
  rw [HeckeDirichlet.LFunction_eq_dirichlet_product χ hs0 hs1] at h
  exact (mul_ne_zero_iff.mp h).1

theorem zeta_of_hecke {θ : ℝ} (hθ : 0 < θ)
    (hH : ∀ (η : HeckeFamily.Character) (s : ℂ), θ < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → HeckeFamily.LFunction η s ≠ 0)
    (s : ℂ) (hs : θ < s.re) : riemannZeta s ≠ 0 := by
  by_cases h1 : s = 1
  · simpa [h1] using riemannZeta_one_ne_zero
  have h := dirichlet_of_hecke hθ hH (1 : DirichletCharacter ℂ 1) s hs
    (by simp [h1])
  simpa only [DirichletCharacter.LFunction_modOne_eq] using h

end Cycle25

/- Adapted unchanged from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
end
/- END ORIGINAL MODULE Cycle25.Assembly.Continuation -/
