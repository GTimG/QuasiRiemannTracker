/- Copyright (c) 2026 Sil. Apache-2.0.
The actual restored root supplies the face and adaptive centering data.
The chosen exponent is independent of every later common allocation.

-/
import Candidate.SilPrior.FourthPower.RecenteredRootSource
import Candidate.SilPrior.FourthPower.RestoredRootEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.RecenteredRootSetup
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103KernelMass QRH.Record1252270103Source
open CenteredMomentEnergyBands CenteredMomentUncenteredTerminal CenteredMomentSourceMass
open MixedPrincipalPair MixedPrincipalAllocations MixedFirstActualNonexceptional
open MixedFirstChosenEnergy MixedFirstGeometricCaps MixedLiveNormalization
open RestoredRootDictionary RestoredRootEnergy RecenteredRootSource NativeMaskedEnergy
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ:Type*} : DecidableEq κ := Classical.decEq _
variable {α:Type u}[Fintype α]
variable (M:Id)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

def ordinaryExponent (s:Setup M H α) : ℝ := Real.logb s.Z (s.Y₁*s.Y₂)
def markedWidth (s:Setup M H α) : ℝ := ∑i:remainingSet s.r s.A,s.w i.val

/-- The original capped face survives both shortening and restoration.
No conductor-dependent upper width is substituted for its unit bound. -/
theorem actual_face (s:Setup M H α) :
    RepairedRootParameters.Face (ordinaryExponent M H s) (markedWidth M H s) := by
  have hs:0≤∑i,s.w i:=Finset.sum_nonneg (fun i _=>s.hw i)
  obtain ⟨hcap,hbudget⟩:=(globalFace_admissible_iff
    (length_nonneg s.Z s.X₁ s.hZ) (length_nonneg s.Z s.X₂ s.hZ) hs
    (by norm_num:(0:ℝ)≤93/25)).mp s.hface
  simp only [mul_one] at hcap hbudget
  have hsub:(∑i:remainingSet s.r s.A,s.w i.val)≤∑i,s.w i := by
    rw [Finset.sum_coe_sort (remainingSet s.r s.A) s.w]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>s.hw i)
  have hlog₁:Real.logb s.Z s.Y₁≤length s.Z s.X₁:=
    Real.logb_le_logb_of_le s.hZ s.hY₁ (s.hy₁.trans (le_max_right _ _))
  have hlog₂:Real.logb s.Z s.Y₂≤length s.Z s.X₂:=
    Real.logb_le_logb_of_le s.hZ s.hY₂ (s.hy₂.trans (le_max_right _ _))
  refine ⟨Finset.sum_nonneg (fun i _=>s.hw i.val),hsub.trans hcap,?_⟩
  dsimp only [ordinaryExponent,markedWidth,RepairedRootParameters.rootReserve]
  rw [Real.logb_mul s.hY₁.ne' s.hY₂.ne']
  linarith

def rootExponent (s:Setup M H α)(ε:ℝ) : ℝ :=
  RepairedRootParameters.centeredExponent ε (ordinaryExponent M H s) (markedWidth M H s)

def rootReference (s:Setup M H α)(ε:ℝ) : ℝ := s.Z^(rootExponent M H s ε)

theorem reference_geometry (s:Setup M H α)(ε:ℝ)(hε:0<ε)
    (hhigh:RepairedRootParameters.NeedsCentering ε (ordinaryExponent M H s) (markedWidth M H s)) :
    0<rootReference M H s ε ∧ 1≤rootReference M H s ε ∧
      comparisonScale (9/4)≤rootReference M H s ε ∧ rootReference M H s ε≤s.Z ∧
      0<rootExponent M H s ε ∧ rootExponent M H s ε<ordinaryExponent M H s/2 := by
  have he:=RepairedRootParameters.centered_spec hε (actual_face M H s) hhigh
  have hq:0<rootReference M H s ε:=Real.rpow_pos_of_pos (zero_lt_one.trans s.hZ) _
  have hq1:1≤rootReference M H s ε:=Real.one_le_rpow s.hZ.le he.1.le
  have hqZ:rootReference M H s ε≤s.Z := by
    simpa only [Real.rpow_one,rootReference,rootExponent] using
      Real.rpow_le_rpow_of_exponent_le s.hZ.le he.2.2.2.2.2.le
  refine ⟨hq,hq1,?_,hqZ,he.1,he.2.1⟩
  exact (by norm_num [comparisonScale]:comparisonScale (9/4:ℝ)≤1).trans hq1

/-- The new reference is installed in the actual root. The two original
short-side branches are dealt with separately by the reference estimate. -/
def centeredRoot (s:Setup M H α)(ε:ℝ)(hε:0<ε)
    (hn₁:comparisonScale (9/4)<s.Y₁)(hn₂:comparisonScale (9/4)<s.Y₂)
    (hhigh:RepairedRootParameters.NeedsCentering ε (ordinaryExponent M H s) (markedWidth M H s))
    (h₁:rootReference M H s ε≤s.Y₁)(h₂:rootReference M H s ε≤s.Y₂) :
    Source (remainingSet s.r s.A) (1/4) (9/4) :=
  recenter (s.rootSource hH hn₁ hn₂) (rootReference M H s ε)
    (reference_geometry M H s ε hε hhigh).1
    (reference_geometry M H s ε hε hhigh).2.2.1 h₁ h₂

theorem centeredRoot_geometry (s:Setup M H α)(ε:ℝ)(hε:0<ε)
    (hn₁:comparisonScale (9/4)<s.Y₁)(hn₂:comparisonScale (9/4)<s.Y₂)
    (hhigh:RepairedRootParameters.NeedsCentering ε (ordinaryExponent M H s) (markedWidth M H s))
    (h₁:rootReference M H s ε≤s.Y₁)(h₂:rootReference M H s ε≤s.Y₂) :
    let r:=centeredRoot M H hH s ε hε hn₁ hn₂ hhigh h₁ h₂
    r.T=s.Y₁*s.Y₂ ∧ r.L=rootReference M H s ε ∧
      r.Y₁=rootReference M H s ε ∧ r.Y₂=(s.Y₁*s.Y₂)/rootReference M H s ε ∧
      r.d=(1,1) ∧ r.R=1 ∧ r.G=1 ∧ r.H=∅ ∧ r.Fhole=1 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem centeredRoot_canonical (s:Setup M H α)(ε:ℝ)(hε:0<ε)
    (hn₁:comparisonScale (9/4)<s.Y₁)(hn₂:comparisonScale (9/4)<s.Y₂)
    (hhigh:RepairedRootParameters.NeedsCentering ε (ordinaryExponent M H s) (markedWidth M H s))
    (h₁:rootReference M H s ε≤s.Y₁)(h₂:rootReference M H s ε≤s.Y₂) :
    Canonical M H hH s.W 16 s.Lcap s.Z s.η₀
      (fun i:remainingSet s.r s.A=>s.θ i.val) (fun i=>s.w i.val)
      (fun _=>33/50) (fun i=>s.v i.val) s.t
      (fun _=>restorationHoles s.r (RestoredInitialSource.primeEnclosure s.Z) s.tc s.A s.ti)
      (centeredRoot M H hH s ε hε hn₁ hn₂ hhigh h₁ h₂) :=
  (s.rootData hn₁ hn₂).source_canonical hH

theorem centeredRoot_capacity (s:Setup M H α)(ε:ℝ)(hε:0<ε)
    (hn₁:comparisonScale (9/4)<s.Y₁)(hn₂:comparisonScale (9/4)<s.Y₂)
    (hhigh:RepairedRootParameters.NeedsCentering ε (ordinaryExponent M H s) (markedWidth M H s))
    (h₁:rootReference M H s ε≤s.Y₁)(h₂:rootReference M H s ε≤s.Y₂)
    (η:Character)(K:ℝ)(hK:s.Z≤K) :
    let r:=centeredRoot M H hH s ε hε hn₁ hn₂ hhigh h₁ h₂
    Real.logb s.Z (r.T/pairNorm r.d)+(93/25:ℝ)*markedWidth M H s≤
      inputWidth η K s.Z-RepairedRootParameters.rootReserve := by
  have hf:=(actual_face M H s).2.2
  have hi:=RestoredRootSource.input_width_one η K s.Z s.hZ hK
  change Real.logb s.Z ((s.Y₁*s.Y₂)/pairNorm (1,1))+(93/25:ℝ)*markedWidth M H s≤_
  simp only [pairNorm,map_one,Nat.cast_one,mul_one,div_one]
  dsimp only [ordinaryExponent] at hf
  linarith

end
end Candidate.SilPrior.FourthPower.RecenteredRootSetup
