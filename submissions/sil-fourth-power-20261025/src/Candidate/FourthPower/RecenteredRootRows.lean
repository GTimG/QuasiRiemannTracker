/- Copyright (c) 2026 Sil. Apache-2.0.
Exact root rectangle split and finite initial-energy triangle. The
original initialKeep stays in BOTH right-hand terms. 
-/
import Candidate.FourthPower.RecenteredRootSetup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RecenteredRootRows
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentUncenteredTerminal
open CenteredMomentLattice
open CenteredMomentCommonMaskEnergy CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open CenteredMomentAllocatedNaturalRadial ReferencePrimeEnclosure
open MixedPrincipalPair MixedPrincipalHeights MixedPrincipalWindow
open MixedFirstRebase MixedFirstPuncturedReference MixedFirstReferenceDispatch MixedLiveNormalization
open RestoredRootEnergy RecenteredRootSource RecenteredRootSetup RestoredInitialSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ:Type*} : DecidableEq κ := Classical.decEq _
variable {α:Type u}[Fintype α]{a b:ℝ}

def rectangle (s:Source α a b)(ha:0<a)(χ:Character)(X Y:ℝ) : ℂ :=
  rectangleRow χ s.S s.H s.R s.pool s.ν s.Wslot s.P
    (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
    (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂) b X Y

theorem rectangle_recenter (s:Source α a b)(q:ℝ)(hq:0<q)(hY:s.Y₁≤q)
    (h₁:q≤s.X₁)(h₂:q≤s.X₂)(ha:0<a)(χ:Character)(X Y:ℝ) :
    rectangle (recenter s q hq hY h₁ h₂) ha χ X Y=rectangle s ha χ X Y := rfl

/-- The reference rectangle is exactly the height-zero rectangle
consumed by the existing nonprincipal reference estimate, in norm. -/
theorem rectangle_height_zero_norm (s:Source α a b)(ha:0<a)(χ:Character)(X Y:ℝ) :
    ‖rectangle s ha χ X Y‖=‖heightRectangle s ha χ 0 X Y‖ := by
  have he (i : α) : heightCoefficient (s.ν i) (0:ℝ) = s.ν i := by
    funext I
    simp only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one]
  rw [height_rectangle_norm]
  simp only [rectangle,shiftSource,he,add_zero]

theorem weighted_row_split (s:Source α a b)(q:ℝ)(hq:0<q)(hY:s.Y₁≤q)
    (h₁:q≤s.X₁)(h₂:q≤s.X₂)(ha:0<a)(hd:s.d=(1,1))
    (hc:s.Y₁=comparisonScale b)(χ:Character) :
    weightedRow s ha 1 (idealCoeff χ)=
      weightedRow (recenter s q hq hY h₁ h₂) ha 1 (idealCoeff χ)+rectangle s ha χ q (s.T/q) := by
  rw [weighted_row_uncentered s ha hd hc χ]
  have he:=weighted_row_centering (recenter s q hq hY h₁ h₂) ha hd χ
  simpa only [rectangle,recenter] using he

private theorem norm_add_square (x y:ℂ) : ‖x+y‖^2≤2*(‖x‖^2+‖y‖^2) := by
  have h:=norm_add_le x y
  nlinarith [norm_nonneg x,norm_nonneg y,norm_nonneg (x+y),sq_nonneg (‖x‖-‖y‖)]

/-- A finite weighted triangle with the literal recentered source.
Weights may already contain the original keep; no mask is deleted. -/
theorem finite_weighted_triangle (s:Source α a b)(q:ℝ)(hq:0<q)(hY:s.Y₁≤q)
    (h₁:q≤s.X₁)(h₂:q≤s.X₂)(ha:0<a)(hd:s.d=(1,1))(hc:s.Y₁=comparisonScale b)
    (rows:Finset O)(weight:O→ℝ)(hw:∀z∈rows,0≤weight z)(χ:O→Character) :
    (∑z∈rows,weight z*‖weightedRow s ha 1 (idealCoeff (χ z))‖^2)≤
      2*((∑z∈rows,weight z*‖weightedRow (recenter s q hq hY h₁ h₂) ha 1 (idealCoeff (χ z))‖^2)+
        ∑z∈rows,weight z*‖rectangle s ha (χ z) q (s.T/q)‖^2) := by
  have hp (z:O)(hz:z∈rows):
      weight z*‖weightedRow s ha 1 (idealCoeff (χ z))‖^2≤
        2*(weight z*‖weightedRow (recenter s q hq hY h₁ h₂) ha 1 (idealCoeff (χ z))‖^2+
          weight z*‖rectangle s ha (χ z) q (s.T/q)‖^2) := by
    rw [weighted_row_split s q hq hY h₁ h₂ ha hd hc (χ z)]
    have he:=mul_le_mul_of_nonneg_left (norm_add_square
      (weightedRow (recenter s q hq hY h₁ h₂) ha 1 (idealCoeff (χ z)))
      (rectangle s ha (χ z) q (s.T/q))) (hw z hz)
    convert he using 1 <;> ring
  apply (Finset.sum_le_sum (fun z hz=>hp z hz)).trans_eq
  simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib]

variable (M:Id)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

set_option maxHeartbeats 500000 in
/-- The actual initial restored energy is split BEFORE enlarging its
keep. Both displayed terms retain the SAME original initialWeight. -/
theorem actual_initial_triangle (s:Setup M H α)(ε:ℝ)(hε:0<ε)
    (hn₁:comparisonScale (9/4)<s.Y₁)(hn₂:comparisonScale (9/4)<s.Y₂)
    (hhigh:RepairedRootParameters.NeedsCentering ε (ordinaryExponent M H s) (markedWidth M H s))
    (h₁:rootReference M H s ε≤s.Y₁)(h₂:rootReference M H s ε≤s.Y₂)
    (η:Character)(Q:Id)(Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(rows:Finset O) :
    (∑z∈rows,initialWeight η s.η₀ Q Φ s.Z z*‖s.literalRow hH (naturalCharacter η z)‖^2)≤
      2*((∑z∈rows,initialWeight η s.η₀ Q Φ s.Z z*
        ‖weightedRow (centeredRoot M H hH s ε hε hn₁ hn₂ hhigh h₁ h₂)
          (by norm_num) 1 (idealCoeff (naturalCharacter η z))‖^2)+
        ∑z∈rows,initialWeight η s.η₀ Q Φ s.Z z*
          ‖rectangle (s.rootSource hH hn₁ hn₂) (by norm_num) (naturalCharacter η z)
            (rootReference M H s ε) ((s.Y₁*s.Y₂)/rootReference M H s ε)‖^2) := by
  rw [s.initial_energy_source hH hn₁ hn₂ η Q Φ rows]
  exact finite_weighted_triangle (s.rootSource hH hn₁ hn₂) (rootReference M H s ε)
    (reference_geometry M H s ε hε hhigh).1 (reference_geometry M H s ε hε hhigh).2.2.1
    h₁ h₂ (by norm_num) rfl rfl rows (initialWeight η s.η₀ Q Φ s.Z)
      (fun z _=>initial_weight_nonneg η s.η₀ Q Φ hΦ s.Z z) (naturalCharacter η)

end
end Candidate.FourthPower.RecenteredRootRows
