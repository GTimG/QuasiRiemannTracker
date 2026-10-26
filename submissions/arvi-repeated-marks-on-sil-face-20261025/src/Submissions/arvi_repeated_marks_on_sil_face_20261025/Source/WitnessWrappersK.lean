/- Repeated marks: detector witnesses at every admissible cutoff.
Fork of Collet's `actual_feedback_witness_family` (High/Witnesses.lean) and
`ordinary_local_witness_family` (High/LocalWitnesses.lean), Apache-2.0. Collet supplies witnesses at
the uniform cutoff of a slot width; the repeated-mark count asks for them at the cutoff of each
amplitude class. The underlying `actual_supported_witness_family` already accepts every cutoff in
`[1,3/2]`, so the statements quantify over the cutoff. The argument lists are Collet's; the face
parameters only served to bound Collet's uniform cutoff and are unused here. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.LocalWitnesses
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000
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

theorem actual_feedback_witness_family_rm (capacity lam cap dmin dmax τ ε e κ η : ℝ)
    (hB : 22/23≤capacity) (hlam : 1<lam) (hh0 : 0≤cap) (hh1 : cap<1) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ,∀ Z : ℝ,Z₀≤Z → ∀ d : ℝ,dmin≤d → d≤dmax →
      ∀ {Row Label : Type*} [Fintype Label] (χ : Row→Label→Character)
        (hχ : ∀ u j,(χ u j).residue≠1) (a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
        (∀ u,HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1 : ℕ)*Z^τ)<a+2*e) →
        (∀ u,a≤HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i : ℕ)*Z^τ)) →
        (∀ u j,(χ u j).modulus.absNorm≤Z^d) →
        ∀t : ℝ,1≤t → t≤3/2 →
          Nonempty (∀ u,SupportedWitness (χ u) (Z^d) a ε t
            (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hZ₀⟩ := HeckeDetectorSupportedWitness.actual_supported_witness_family
    dmin dmax τ ε e κ η I hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Row Label inst χ hχ a i hi ha ha' hnext hcurrent hQ t ht1 ht2
  exact hZ₀ Z hZ d hd hd' χ hχ a i hi ha ha' hnext hcurrent hQ t ht1 ht2

local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance witnessWrappersFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem ordinary_local_witness_family_rm
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
      ∀t : ℝ,1≤t → t≤3/2 →Nonempty (∀u,SupportedWitness
        ((B.localizeFamily M H hH pick hpick).family u) (Z^d) a ε t
        (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hw⟩ := actual_feedback_witness_family_rm capacity lam cap dmin dmax τ ε e κ η hB hlam hh0
    hh1 I hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hη (by norm_num; linarith)
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' base anchor bad W lo hi B pick hpick hn a i hi' ha ha' hnxt hcur hmod t ht1 ht2
  let chooseRow : FreeRow→FreeRow := fun u=>if u∈B.rows then u else pick
  have hmem (u : FreeRow) : chooseRow u∈B.rows := by
    dsimp [chooseRow]; split_ifs with h
    · exact h
    · exact hpick
  exact hw Z hZ d hd hd' (fun u=>B.family (chooseRow u))
    (fun u=>hn _ (hmem u)) a i hi' (by linarith) (by linarith)
    (fun u=>hnxt _ (hmem u)) (fun u=>hcur _ (hmem u))
    (fun u=>hmod _ (hmem u)) t ht1 ht2

end QRH.Record1252270103Source.High
end
