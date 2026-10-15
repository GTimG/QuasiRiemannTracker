/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Physical.InitialMass.SecondHighPayment
import Candidate.Cycle62.Physical.InitialMass.GeometrySecondSplit
import Candidate.Cycle62.Physical.SecondZero.Uniform

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic Cycle62Moment
open CenteredMomentFirstExceptionalPrefactor
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst
open CenteredMomentFirstScale CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentOriginalCommonHarmonic CenteredMomentFiniteProfileExceptional
open CenteredMomentSourceRow CenteredMomentSourceMass EisensteinSchwartzPoisson
open Cycle62SecondZero
local notation "O" => HeckeFamily.O

lemma original_zero_radiusTerm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    ‖originalSecondZero s R seed W K‖/volume s = radiusTerm s R seed W K := by
  rfl

def firstZeroReference (reflected : Bool) (Z A a : ℝ) (l : FirstSourceLabel) : ℝ :=
  a+A-Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)+
    Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)+
    Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)

def firstZeroSaving (reflected : Bool) (Z M A ξ reserve padding ε s₀ : ℝ)
    (l : FirstSourceLabel) : ℝ :=
  -M*(336582307/4825296000)+frequencyLoss Z 32 ξ+reserve+
    ε*(A-Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)+padding)-s₀

/-- The literal zero term at the enlarged main radius, with the first
projector and actual child normalization retained in both orientations. -/
theorem actual_first_label_main_zero (N : ℕ) (Cs bs lo hi ε : ℝ)
    (hCs : 1 ≤ Cs) (hbs : 1 ≤ bs) (hlo : 0 < lo) (hhi : 0 ≤ hi) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
    ∀ (s : Input ι), Fintype.card ι ≤ N → (∀ i,s.M i ≤ Cs) → s.upper ≤ bs →
    ∀ p : Profiles lo hi, s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
    ∀ (reflected : Bool) (l : FirstSourceLabel), Supported l.1.1 → Supported l.1.2 →
    CompletedGauss.primeSupport l.1.1 = CompletedGauss.primeSupport l.1.2 →
    ∀ (R seed : Ideal O), seed ≠ 0 →
    ∀ (B : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
      (χ : Character) (t : ℝ),
    frozenCoefficient B.val (if reflected then l.1.2 else l.1.1) R s.ν s.W s.P ≠ 0 →
    ∀ (W : 𝓢(ℝ,ℂ)) (Z beta M A a ξ reserve padding s₀ : ℝ), 1 < Z →
    3401/100000 ≤ beta ∧ beta ≤ 1/25 → 0 ≤ M →
    A ≤ M*Cycle62.Arithmetic.totalA beta → a ≤ M*Cycle62.Arithmetic.amp beta →
    volume s = Z^A → bs^N ≤ Z^padding → Z^s₀ ≤ (seed.absNorm:ℝ) →
    let u := child s (if reflected then l.1.2 else l.1.1) R B χ t
    Z^(-firstZeroReference reflected Z A a l)*
      (‖originalSecondZero u (R*(if reflected then l.1.2 else l.1.1)) seed W
        (firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l)‖/volume u) ≤
      C₀*(p.control {(0,0)})^2*‖paperRadialFourier W 0‖*
        Z^(firstZeroSaving reflected Z M A ξ reserve padding ε s₀ l) := by
  obtain ⟨C₀,hC₀,hbound⟩ := uniform_radius_certificates N Cs bs hi ε hCs hbs hε
  refine ⟨C₀,hC₀,?_⟩
  intro ι _ _ s hn hm hs p hp₁ hp₂ reflected l hC hD heq R seed hseed B χ t hB
    W Z beta M A a ξ reserve padding s₀ hZ hb hM hA ha hV hgeo hseedN
  let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
  let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
  let Rw := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
  let e := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
  have hselected : (if reflected then l.1.2 else l.1.1) ≠ 0 := by
    cases reflected <;> first | exact hC.1 | exact hD.1
  have hother : (if reflected then l.1.1 else l.1.2) ≠ 0 := by
    cases reflected <;> first | exact hD.1 | exact hC.1
  have hcn : Z^c ≤ ((if reflected then l.1.2 else l.1.1).absNorm:ℝ) := by
    rw [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (norm_pos _ hselected)]
  have hv := actual_common_volume_cap N bs hbs s hn hs _ R B χ t hB Z A c padding hZ
    hgeo (le_of_eq hV) hcn
  have hh := hbound hv.1 lo hlo hhi (child s _ R B χ t) p
    (fun i => hm i.val) hs hp₁ hp₂ (R*(if reflected then l.1.2 else l.1.1)) seed hseed
    W Z beta M A a c d 0 Rw e (2*A-c-d+Rw+e-M) 0 (frequencyLoss Z 32 ξ) reserve
    (A-c+padding) s₀ hZ hb hM hA ha
    (ideal_log_nonneg _ hselected Z hZ) (ideal_log_nonneg _ hother Z hZ)
    (by norm_num) (by simp) hv.2 hseedN
  have hr : firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l =
      mainCommonRadius Z d (2*A-c-d+Rw+e-M) c (3*a) (frequencyLoss Z 32 ξ) reserve := by
    rw [hV,actual_main_radius_power reflected l hC hD heq Z M A a ξ reserve hZ]
    unfold mainCommonRadius
    congr 1
    dsimp only [c,d,Rw,e]
    ring
  dsimp only
  rw [hr,original_zero_radiusTerm]
  convert hh.1 using 1 <;>
    dsimp only [firstZeroReference,firstZeroSaving,c,d,Rw,e,radiusTerm] <;>
    congr 2 <;> ring

/-- Remove only the displayed positive reference power; the normalized
child volume is still literal. -/
lemma reference_power_remove (Z ref saving x bound : ℝ) (hZ : 0 < Z)
    (h : Z^(-ref)*x ≤ bound*Z^saving) : x ≤ bound*Z^(ref+saving) := by
  have hh := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hZ.le ref)
  have he : Z^ref*Z^(-ref) = 1 := by rw [←Real.rpow_add hZ]; simp
  apply (show x ≤ Z^ref*bound*Z^saving by simpa only [←mul_assoc,he,one_mul] using hh).trans_eq
  rw [Real.rpow_add hZ]
  ring

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.original_zero_radiusTerm
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_first_label_main_zero
#print axioms OAI.SevenEighths.Cycle62InitialMass.reference_power_remove
