import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.ActiveColumns
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.JointWindowEnergy

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentFirstAllocationGaussEnergy CenteredMomentLogDyadic
open CenteredMomentFirstCanonicalFamily CenteredMomentOriginalCommonHarmonic
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem actual_geometry_seed (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (key : ℤ×(Fin 5→ℤ)) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (q : CommonGeometryFiber s R seed K Z ξ key) :
    seed∣(geometryFirstSource s R seed K Z ξ hK key q).C ∧
      seed∣(geometryFirstSource s R seed K Z ξ hK key q).D := by
  have hh := actual_common_gates s R seed hs hz₁ hz₂ q.val.1.val.1 q.val.1.val.2 q.val.1.property
  exact ⟨hh.2.2.2.1,hh.2.2.2.2.1⟩

def geometryColumnIdeal (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) : Ideal O :=
  if reflected then (geometryFirstSource s R seed K Z ξ hK key j.1).D
    else (geometryFirstSource s R seed K Z ξ hK key j.1).C

def geometryColumnCharacter (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) : Character :=
  let src := geometryFirstSource s R seed K Z ξ hK key j.1
  let pair := fixedPair s.η src.C src.D src.hC src.inactive j.2.2.1 j.2.2.2⁻¹
  if reflected then pair.right else pair.left

def geometryColumnScalar (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) : ℂ :=
  if reflected then
    (Real.sqrt (Z^(rightExponent A (geometryExponents s R seed K Z ξ j.1.val))):ℂ)⁻¹
  else weight j.1.val*(geometryFirstSource s R seed K Z ξ hK key j.1).outside/
    (Real.sqrt (Z^(2*outsideExponent M A (geometryExponents s R seed K Z ξ j.1.val)+
      leftExponent A (geometryExponents s R seed K Z ξ j.1.val))):ℂ)

/-- Literal live child-source budget for one side of the first transform.
No estimate of its main, error, low or high branch is assumed here. -/
def geometryLiveBudget (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (N : ℕ) (b t : ℝ) : ℝ :=
  let src := geometryFirstSource s R seed K Z ξ hK key
  let C := geometryColumnIdeal reflected s R seed K Z ξ hK key
  let τ := geometryColumnCharacter reflected s R seed K Z ξ hK key
  ∑j∈firstLiveColumns src (fun _=>logAnnulus),
    ‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j‖^2*
      ((max 1 b)^N*((actualAllocations s.pools (C j)).card:ℝ)/(C j).absNorm*
        ∑B : actualAllocations s.pools (C j),
          if frozenCoefficient B.val (C j) R s.ν s.W s.P≠0 then
            (frozenControl B.val s.M)^2*childNormalizedGaussSource s (C j) R j.2.1.val B
              (τ j) t CenteredMomentFirstAnnularMajorant.profile (src j.1).H0
          else 0)

theorem actual_geometry_source_budget (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (N : ℕ) (a b t : ℝ) (ha : 0<a) (hcard : Fintype.card ι≤N)
    (haS : a≤s.lower) (hbS : s.upper≤b)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) :
    let src := geometryFirstSource s R seed K Z ξ hK key
    let C := geometryColumnIdeal reflected s R seed K Z ξ hK key
    let τ := geometryColumnCharacter reflected s R seed K Z ξ hK key
    (∑q∈firstActiveSectors src (fun _=>logAnnulus),
      ‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight (firstSectorColumn src q)*
        allocatedPolynomial (original s R seed) (C (firstSectorColumn src q)) q.2.1.val
          (τ (firstSectorColumn src q)) t (volume s) (firstSignedRow reflected q.2.2.2.2.val)‖^2)≤
      geometryLiveBudget reflected s R seed K Z ξ M A hK key weight N b t := by
  intro src C τ
  have hC (j : FirstColumnIndex src) : Supported (C j) := by
    cases reflected
    · exact (src j.1).hC
    · exact (src j.1).hD
  have hseed (j : FirstColumnIndex src) : seed∣C j := by
    have hh := actual_geometry_seed s R seed K Z ξ hK key hs hz₁ hz₂ j.1
    cases reflected
    · exact hh.1
    · exact hh.2
  have hh := actual_active_common_live_energy reflected src N a b ha s hcard haS hbS C R seed
    hC hseed τ (fun _=>t)
    (fun j=>‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j‖^2)
    (fun _=>sq_nonneg _)
  simpa only [norm_mul,mul_pow,geometryLiveBudget,src,C,τ] using hh


/-- The literal left child budget supplies the source premise of the
Mellin-window theorem, with original source volume as normalization. -/
theorem actual_geometry_left_budget_window (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (hZ : 0<Z) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (N : ℕ) (a b : ℝ) (ha : 0<a) (hcard : Fintype.card ι≤N)
    (haS : a≤s.lower) (hbS : s.upper≤b)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hc : HasCompactSupport logAnnulus) (hsm : ContDiff ℝ ∞ logAnnulus)
    (t : ℝ) (J : ℕ) (E : ℝ) (hE : 0≤E)
    (hbudget : ∀u : ℝ, geometryLiveBudget false s R seed K Z ξ M A hK key weight N b
      (s.t+2*Real.pi*(u-t))≤E*(1+‖u‖)^(2*J)) :
    geometryLeftEnergy s R seed K Z ξ M A hK key (fun q=>weight q.val)
      (fun _=>logAnnulus) t/volume s≤
      E*(∫u : ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
        logAnnulus hc hsm u‖)^2 := by
  apply actual_geometry_left_window_energy s R seed K Z ξ M A hK hZ key weight
    (fun q=>(actual_geometry_seed s R seed K Z ξ hK key hs hz₁ hz₂ q).1)
    (fun _=>logAnnulus) hc hsm t (volume s) (volume_pos s) J E hE
  intro u
  have hh := actual_geometry_source_budget false s R seed K Z ξ M A hK key weight N a b
    (s.t+2*Real.pi*(u-t)) ha hcard haS hbS hs hz₁ hz₂
  exact le_trans hh (hbudget u)

/-- The reflected right budget passes through its independent Mellin
height, retaining the conjugate window from the actual first transform. -/
theorem actual_geometry_right_budget_window (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (hZ : 0<Z) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (N : ℕ) (a b : ℝ) (ha : 0<a) (hcard : Fintype.card ι≤N)
    (haS : a≤s.lower) (hbS : s.upper≤b)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hc : HasCompactSupport logAnnulus) (hsm : ContDiff ℝ ∞ logAnnulus)
    (t : ℝ) (J : ℕ) (E : ℝ) (hE : 0≤E)
    (hbudget : ∀u : ℝ, geometryLiveBudget true s R seed K Z ξ M A hK key weight N b
      (s.t+2*Real.pi*(u-(-t)))≤E*(1+‖u‖)^(2*J)) :
    geometryRightEnergy s R seed K Z ξ A hK key (fun _=>logAnnulus) t/volume s≤
      E*(∫u : ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
        (fun x=>star (logAnnulus x))
        (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
        (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hsm) u‖)^2 := by
  apply actual_geometry_right_window_energy s R seed K Z ξ A hK hZ key
    (fun q=>(actual_geometry_seed s R seed K Z ξ hK key hs hz₁ hz₂ q).2)
    (fun _=>logAnnulus) hc hsm t (volume s) (volume_pos s) J E hE
  intro u
  have hh := actual_geometry_source_budget true s R seed K Z ξ M A hK key weight N a b
    (s.t+2*Real.pi*(u-(-t))) ha hcard haS hbS hs hz₁ hz₂
  exact le_trans hh (hbudget u)

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_seed
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_source_budget

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_left_budget_window
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_right_budget_window
