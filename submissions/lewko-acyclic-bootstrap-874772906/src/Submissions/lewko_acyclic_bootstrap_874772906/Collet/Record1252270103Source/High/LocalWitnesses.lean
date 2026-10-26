/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.Witnesses
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.LocalizedBatch
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace QRH.Record1252270103Source.High
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily CanonicalRowCompletion
open HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount HeckeDetectorDyadicProfiles
open DetectorDictionaryInverseRawInitialGates LocalMoment
open ConcreteTraceCRT ActualEisensteinCubic CenteredMomentDetectorPlainFiberSource
open HeckeDetectorSupportedWitness HeckeDetectorFiberPartition HeckeDetectorWitnessRows
open HeckeDetectorCoefficientTransfer Record12518109GainActual
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
theorem ordinary_local_witness_family
    (capacity lam cap dmin dmax τ ε e κ η : ℝ)
    (hB : 22/23≤capacity) (hlam : 1<lam) (hh0 : 0≤cap) (hh1 : cap<1) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 288*e+8*κ+2*η≤ε/2) :
    ∃Z₀ : ℝ,∀Z : ℝ,Z₀≤Z →∀d : ℝ,dmin≤d →d≤dmax →
      ∀{base anchor : Label→Character}{bad : Label→Ideal O}{W : ℝ→ℂ}{lo hi : ℝ},
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi (Z^d),
      ∀pick : FreeRow,∀hpick : pick∈B.rows,
      ∀hn : ∀u∈B.rows,∀j,(B.family u j).residue≠1,
      ∀a : ℝ,∀i : ℕ,i≤I →1/2≤2*a-1 →2*a-1≤3/4 →
      (∀(u : FreeRow)(hu : u∈B.rows),HeckeDetectorZeros.zeroMaximum (B.family u) (hn u hu)
        (3*(i+1 : ℕ)*Z^τ)<a+2*e) →
      (∀(u : FreeRow)(hu : u∈B.rows),a≤HeckeDetectorZeros.zeroMaximum (B.family u) (hn u hu)
        ((3*i : ℕ)*Z^τ)) →
      (∀u∈B.rows,∀j,(B.family u j).modulus.absNorm≤Z^d) →
      ∀S : ℝ,0≤S →Nonempty (∀u,SupportedWitness
        ((B.localizeFamily M H hH pick hpick).family u) (Z^d) a ε (cutoff (2*a-1) capacity lam cap S 1)
        (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hw⟩ := actual_feedback_witness_family capacity lam cap dmin dmax τ ε e κ η hB hlam hh0 hh1 I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hη (by norm_num; linarith)
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' base anchor bad W lo hi B pick hpick hn a i hi' ha ha' hnxt hcur hmod S hS
  let chooseRow : FreeRow→FreeRow := fun u=>if u∈B.rows then u else pick
  have hmem (u : FreeRow) : chooseRow u∈B.rows := by
    dsimp [chooseRow]; split_ifs with h
    · exact h
    · exact hpick
  exact hw Z hZ d hd hd' (fun u=>B.family (chooseRow u))
    (fun u=>hn _ (hmem u)) a i hi' (by linarith) (by linarith)
    (fun u=>hnxt _ (hmem u)) (fun u=>hcur _ (hmem u))
    (fun u=>hmod _ (hmem u)) S hS ha ha'

end QRH.Record1252270103Source.High
end
#print axioms QRH.Record1252270103Source.High.ordinary_local_witness_family
