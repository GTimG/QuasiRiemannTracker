/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Range extension of outputs/record-c012518109-20261019/formalization/Record12518109Gain/LocalizedBatch.lean. Original formulas and source attribution retained. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.NaturalLowDensity.ActualMaxWeighted
import Submissions.hailey_collet_1252270103.Record1252270103Source.NaturalLowDensity.ActualWitnesses

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.NaturalLowDensity.Actual
open OAI OAI.SevenEighths
open OAI.SevenEighths.Record12518109GainActual
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily LocalMoment
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorEnergyInitialState
open HeckeDetectorSupportedWitness Record12518109Gain
open QRH.Record1252270103Source.NaturalLowDensity
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance localizedBatchFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- Only retained rows enter the count. Outside that population the family
is extended by one actual retained row, so no witness for an exceptional
or principal row is requested. -/
def NaturalBatch.localizeFamily {base anchor : Label→Character} {bad : Label→Ideal O}
    {W : ℝ→ℂ} {lo hi U : ℝ} (B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U)
    (pick : FreeRow) (hpick : pick∈B.rows) : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U :=
  { B with
    family := fun u=>B.family (if u∈B.rows then u else pick)
    idealCoefficients := by intro u hu j I; simpa only [if_pos hu] using B.idealCoefficients u hu j I
    elementCoefficients := by intro u hu j n; simpa only [if_pos hu] using B.elementCoefficients u hu j n
    plainIdentity := by intro u hu j s hs; simpa only [if_pos hu] using B.plainIdentity u hu j s hs }

theorem NaturalBatch.retained_nonprincipal {base anchor : Label→Character} {bad : Label→Ideal O}
    {W : ℝ→ℂ} {lo hi U : ℝ} (B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U)
    (u : FreeRow) (hu : u∈B.rows) : ∀j,(B.family u j).residue≠1 := by
  intro j hp
  have hn := (CenteredMomentNaturalRowSource.naturalRow (base j) u.val u.property.1).nonprincipal
    u.property.1 (internalQ (bad j) (anchor j)) 1 one_ne_zero (B.retained u hu j).2
  have hc : ∀I,idealCoeff (B.family u j) I=
      idealCoeff (CenteredMomentNaturalRowSource.naturalRow (base j) u.val u.property.1).character I := by
    intro I
    exact (B.idealCoefficients u hu j I).trans (natural_raw_coefficients (base j) (momentElement u) I).symm
  exact hn ((HeckeFiniteDeletion.principal_iff_of_mask _ _ (coefficient_equality_mask _ _ hc)).mp hp)

theorem actual_local_witness_family
    (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
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
        ((QRH.Record1252270103Source.NaturalLowDensity.Actual.NaturalBatch.localizeFamily M H hH B pick hpick).family u) (Z^d) a ε (cutoff (2*a-1) S)
        (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hw⟩ := actual_homogeneous_witness_family dmin dmax τ ε e κ η I
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

end
end QRH.Record1252270103Source.NaturalLowDensity.Actual
