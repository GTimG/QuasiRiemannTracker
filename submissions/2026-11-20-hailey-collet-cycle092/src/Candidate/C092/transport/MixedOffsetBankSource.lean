/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Q.2 bank from the original source family, one actual attaining zero per row. -/
import Candidate.C092.transport.MixedOffsetBankGrid
import Candidate.C092.transport.MediumWitnessBatch
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetBank
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorSupportedWitness HeckeDetectorZeros
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
local instance c092LocalInst_Candidate_C092_transport_MixedOffsetBankSource_80b8d7bec076ce5c_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (hH : RayOrthogonality.globalUnits M≤H)

/-- The list is fixed before every selected witness response. Dyads, phases
and both lengths may vary with the offset; label and actual zero cannot. -/
structure SourceBank (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character)
    (rows : Finset FreeRow) (U a ε t₀ γ T allowance : ℝ) (i : ℕ) where
  label : rows→Sum Bool (RayQuotient.Characters M H)
  zero : rows→ℂ
  witness : ∀ j : Offset,∀ u : rows,SupportedWitness
    (sourceDetectorFamily S hS.prime η u.val (rayCubeFamily M H hH u.val))
    U a ε (cutoff t₀ γ j) T allowance i
  fixed_label : ∀ j u,(witness j u).label=label u
  fixed_zero : ∀ j u,(witness j u).zero=zero u
  zero_equation : ∀ u,LFunction
    (sourceDetectorFamily S hS.prime η u.val (rayCubeFamily M H hH u.val) (label u)) (zero u)=0
  attaining : ∀ u,(zero u).re=detectorMaximum
    (sourceDetectorFamily S hS.prime η u.val (rayCubeFamily M H hH u.val)) ((3*i:ℕ)*T)
  zero_height : ∀ u,|(zero u).im|≤(3*i:ℕ)*T

/-- Original source conductor and nonprincipality suppliers discharge the
analytic gates. The same zero precedes all 65,537 cutoff responses. -/
theorem actual_source_bank (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*heightCost)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1)
    (hcost : 0≤heightCost) (hmargin : 0 < margin)
    (hbudget : 12*e*(22+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠ Z : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax →
    ∀ (rowCap : ℝ) (rows : Finset FreeRow),rows⊆rowBand (Z^(1/100:ℝ)) rowCap →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤Z^(d-margin)) →
    ∀ (a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
    ∀ (t₀ γ : ℝ),0≤γ → 1≤t₀-γ → t₀≤3/2 →
      Nonempty (SourceBank M H hH S hS η rows (Z^d) a ε t₀ γ (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hsim⟩:=SharedCutoffZero.simultaneous_cutoffs dmin dmax τ ε e κ heightCost I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hcost hbudget
  filter_upwards [eventually_ge_atTop Z₀,
    source_ray_nonprincipal_eventually M H hH S hS hmax η (1/100) (by norm_num),
    source_ray_conductor_eventually M H hH S hS.prime η margin hmargin] with Z hZ hnp hcond
  intro d hd hd' rowCap rows hrows hcal hnorm a i hi ha ha' hnext hcurrent t₀ γ hγ ht ht'
  let χ := fun u : rows=>sourceDetectorFamily S hS.prime η u.val (rayCubeFamily M H hH u.val)
  have hn (u : rows) : ∀l,(χ u l).residue≠1 := hnp rowCap u.val (hrows u.property) (hcal u.val u.property)
  have heq (u : rows) := detectorMaximum_eq_nonprincipal (χ u) (hn u)
  have hex (u : rows) := hsim Z hZ d hd hd' (χ u) (hn u) a i hi ha ha'
    (by rw [←heq u];exact hnext u.val u.property)
    (by rw [←heq u];exact hcurrent u.val u.property)
    (hcond u.val d (hnorm u.val u.property))
  choose label zero hz hmaxzero hheight hw using hex
  have hww (j : Offset) (u : rows) := hw u (cutoff t₀ γ j)
    (cutoff_bounds t₀ γ hγ ht ht' j).1 (cutoff_bounds t₀ γ hγ ht ht' j).2
  choose w hl hzero using hww
  exact ⟨⟨label,zero,w,hl,hzero,hz,fun u=>(hmaxzero u).trans (heq u _).symm,hheight⟩⟩

end
end QRH.Cycle092.MixedOffsetBank
