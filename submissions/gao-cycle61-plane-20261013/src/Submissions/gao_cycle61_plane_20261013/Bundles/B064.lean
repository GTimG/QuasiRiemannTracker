/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B000
import Submissions.gao_cycle61_plane_20261013.Bundles.B060
import Submissions.gao_cycle61_plane_20261013.Bundles.B062
import Submissions.gao_cycle61_plane_20261013.Bundles.B063
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.Bands

/- BEGIN ORIGINAL Cycle61.Moment.InitialAffineContract; sha256 22ff66f4494084ac8f52b1d91d1b08f91af22f5b8d9d7135b944d1a61449208c -/
section
                                  
                                   
                                               

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge
open CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayModulus : Ideal O) [NeZero rayModulus]
local instance : Finite (O ⧸ rayModulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (H : Subgroup (O ⧸ rayModulus)ˣ)
variable (hH : RayOrthogonality.globalUnits rayModulus ≤ H)

/-- The required moment applies to the fixed initial parent, uniformly over
a compact positive width interval and all live canonical slot parameters. -/
def InitialAffineAt (W : ℝ → ℂ) (bslot a b bΦ mesh lo hi Mmin Mmax ε Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ T : Finset α, ∀ (θ : T → RayQuotient.Characters rayModulus H)
      (w σ v : T → ℝ) (t height : ℝ),
    (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
    (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) →
    0 ≤ height → (∀ i, |v i| ≤ height) →
  ∀ M : ℝ, Mmin ≤ M → M ≤ Mmax →
  ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ →
    (∀ x, 0 ≤ (Φ x).re) →
  ∀ p : Profiles a b, ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ →
    (41/100)*M ≤ length Z X₁ → length Z X₁ ≤ (44/100)*M →
    (41/100)*M ≤ length Z X₂ → length Z X₂ ≤ (44/100)*M →
    (17/500)*M ≤ ∑ i, w i → (∑ i, w i) ≤ (1/25)*M →
    length Z X₁ + length Z X₂ + Cycle61.Arithmetic.lambda*(∑ i, w i) ≤
      Cycle61.Arithmetic.B*M →
    energy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool rayModulus H bslot (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter rayModulus H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i => Z^(w i)) X₁ X₂ (initialKeep η (internalQ Q η₀)) Φ (Z^M) ≤
      C*QuadraticInitialBound.diagonalControl Φ*(p.control S)^2*
        (1+|t|+height)^degree*Z^(M+ε)

end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.InitialAffineContract -/

/- BEGIN ORIGINAL Cycle61.Numerator.Fourth.Input; sha256 20c612292579ccbf1f3b3465b569f16de792822260b438ca87d2cc2dbb663031 -/
section
                                           
                                              
                                          

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace Cycle61.Numerator.Fourth
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentEnergyBands CenteredMomentRowNorm ConcretePrimeRowBridge
open CenteredMomentHeckeSlots CenteredMomentRetainedEnergy QuadraticInitialBound
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization CenteredMomentNaturalPrimitive
open ProbePhysical CenteredMomentWholeSlotDeletion
open Cycle25WeightedNumeratorPhysical
local notation "O" => HeckeFamily.O

/-- The literal affine initial-energy input, evaluated at radial width one.
The source is conjugated, matching the reflected physical numerator. -/
def AffineAt {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (bΦ mesh ε U : ℝ) (degree : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ) : Prop :=
  let η := fixedSourcePrincipal F.S F.exclusions.prime
  Cycle61Moment.InitialAffineAt (α:=Fin D.N) F.modulus ⊤ le_top
    (fun x=>conj (F.W x)) 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε U
    η η (weighted_sourceFixedIdeal F) degree control C

/-- The genuine initial energy controls the finite physical reflected pair.
No conductor, Euler factor, source mask, or ramified zero is altered. -/
theorem finite_physical_pair_affine {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (rows : Finset FreeRow)
    (Φ : 𝓢(ℝ,ℂ)) (U bΦ mesh ε : ℝ)
    (hU : 1 ≤ U) (hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic bΦ)
    (hp : ∀x,0≤(Φ x).re)
    (hη : ((fixedSourcePrincipal F.S F.exclusions.prime).modulus.absNorm:ℝ)≤ U)
    (hrows : ∀u∈rows,rowNorm u≤ U)
    (hkeep : ∀u∈rows, initialKeep (fixedSourcePrincipal F.S F.exclusions.prime)
      (internalQ (weighted_sourceFixedIdeal F) (fixedSourcePrincipal F.S F.exclusions.prime)) u.val)
    (hone : ∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (degree : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ)
    (haffine : AffineAt F bΦ mesh ε U degree control C)
    (T : Finset (Fin D.N)) (width : T→ℝ) (z : T→ℂ) (height : ℝ)
    (hw : ∀i,0≤ width i) (hwmax : ∀i,width i≤ mesh)
    (hz : ∀i,(z i).re=17/50) (hh : 0≤ height) (hzim : ∀i,|(z i).im|≤ height)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hlo₁ : 41/100≤ length U X₁) (hhi₁ : length U X₁≤44/100)
    (hlo₂ : 41/100≤ length U X₂) (hhi₂ : length U X₂≤44/100)
    (hslotlo : 17/500≤∑i,width i) (hslothi : (∑i,width i)≤1/25)
    (hcap : length U X₁+length U X₂+Arithmetic.lambda*(∑i,width i)≤ Arithmetic.B) :
    (∑u∈rows, ‖polynomial ((momentData (fixedSourcePrincipal F.S F.exclusions.prime)).character
      (momentElement u)) false (p.profile 0) X₁ 0 0 *
      polynomial ((momentData (fixedSourcePrincipal F.S F.exclusions.prime)).character
      (momentElement u)) false (p.profile 1) X₂ 0 0 *
      ∏i,normalizedSlot (fixedSourcePrincipal F.S F.exclusions.prime) rowMaskElement 1 u.val
        (CenteredMomentPrimeSlot.primePool F.modulus ⊤ 2 (U^(width i)))
        (physicalSlotCoefficient (fixedSourcePrincipal F.S F.exclusions.prime) F.W (U^(width i)) (z i))
        0 (U^(width i))‖^2) ≤ C*diagonalControl Φ*(p.control control)^2*(1+height)^degree*U^(1+ε) := by
  let η := fixedSourcePrincipal F.S F.exclusions.prime
  have he := finite_actual_pair_le_energy rows η (internalQ (weighted_sourceFixedIdeal F) η)
    Φ U bΦ 1 hU (by norm_num) hs hp (by simpa using hη) hrows hkeep hone (p.profile 0) (p.profile 1)
    (9/4) (9/4) X₁ X₂ (fun _ hx=>(p.support 0 hx).2)
    (fun _ hx=>(p.support 1 hx).2) hX₁ hX₂
    (fun i=>CenteredMomentPrimeSlot.primePool F.modulus ⊤ 2 (U^(width i)))
    (fun i=>physicalSlotCoefficient η F.W (U^(width i)) (z i))
    (fun i=>U^(width i)) (fun _=>Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _)
  have hcoef : (fun (i:T) I=>physicalSlotCoefficient η F.W (U^(width i)) (z i) I) =
      (fun (i:T) I=>idealCoeff η.inverse I*HeckePrimeAnnular.annularWeight
        (fun x=>conj (F.W x)) (U^(width i)) (33/50) (-(z i).im) I) := by
    funext i I
    rw [weighted_physical_annular_all F η _ (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _) (z i) I,hz i]
    norm_num
  rw [hcoef] at he
  have heq := CenteredMomentDetectorPlainRelativeClass.energy_eq F.modulus ⊤ le_top
    η η (fun (_:T)=>1) (fixedBadMask*idealGenerator 1) 1 (p.profile 0) (p.profile 1)
    (fun _=>2) (fun i=>U^(width i))
    (fun i I=>HeckePrimeAnnular.annularWeight (fun x=>conj (F.W x))
      (U^(width i)) (33/50) (-(z i).im) I) 0 X₁ X₂
    (initialKeep η (internalQ (weighted_sourceFixedIdeal F) η)) Φ U
  have hb := haffine T (fun _=>1) width (fun _=>33/50) (fun i=>-(z i).im)
    0 height hw hwmax (fun _=>le_rfl) (fun _=>le_rfl) hh
    (fun i=>by simpa only [abs_neg] using hzim i) 1 le_rfl le_rfl Φ hs hp p X₁ X₂
    hX₁ hX₂ (by simpa using hlo₁) (by simpa using hhi₁)
    (by simpa using hlo₂) (by simpa using hhi₂)
    (by simpa using hslotlo) (by simpa using hslothi) (by simpa using hcap)
  exact he.trans (heq.le.trans (by simpa [η] using hb))

end Cycle61.Numerator.Fourth

end
/- END ORIGINAL Cycle61.Numerator.Fourth.Input -/

/- BEGIN ORIGINAL Cycle61.Numerator.Fourth.Fourier; sha256 26d4fb71169911f8c0d2997f63e1793219fc72e6e6cabedbe001cf7fd87d6373 -/
section
                                     
                                               

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace Cycle61.Numerator.Fourth
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondHeightFamily CenteredMomentEnergyBands CenteredMomentRowNorm
open CenteredMomentDetectorPlainFiberSource CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentHeckeSlots CenteredMomentRetainedEnergy QuadraticInitialBound
open CenteredMomentNaturalPrimitive
open ProbePhysical CenteredMomentWholeSlotDeletion
open Cycle25WeightedNumeratorPhysical
local notation "O" => HeckeFamily.O

/-- Affine interior physical Fourier pair. The analytic premise is the actual
initial radial energy, not a row fourth moment or an improved zero-free endpoint. -/
theorem affine_fourier {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (bΦ mesh ε : ℝ) (hsΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (degree : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0<Ci)
    (hinput : ∀ᶠU:ℝ in atTop,AffineAt F bΦ mesh ε U degree control Ci) :
    ∃J:ℕ,∃C:ℝ,0<C ∧ ∀ᶠU:ℝ in atTop,
      1<U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ U) →
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height:ℝ,
      (∀i,0≤ width i) → (∀i,width i≤ mesh) → (∀i,(z i).re=17/50) →
      0≤ height → (∀i,|(z i).im|≤ height) →
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      41/100≤ length U X₁ → length U X₁≤44/100 →
      41/100≤ length U X₂ → length U X₂≤44/100 →
      17/500≤∑i,width i → (∑i,width i)≤1/25 →
      length U X₁+length U X₂+Arithmetic.lambda*(∑i,width i)≤ Arithmetic.B →
      ∀j k:Fin 2,∀v w:ℝ,
      (∑u∈rows,‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏i,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2)
      ≤ (C*(1+height)^degree*U^(1+ε))*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  let η := fixedSourcePrincipal F.S F.exclusions.prime
  obtain ⟨J,Cp,hCp,hprofile⟩:=numerator_fourier_profiles_control control
  let C:=Ci*(1+diagonalControl radialMajorant)*Cp
  have hC:0<C:=by have:=diagonalControl_nonneg radialMajorant;dsimp [C];positivity
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hinput,eventually_fixed_source_keep F η,eventually_gt_atTop (1:ℝ),
    eventually_ge_atTop (η.modulus.absNorm:ℝ)] with U ha hkeep hU hη
  refine ⟨hU,?_⟩
  intro rows hrows T width z height hw hwmax hz hh hzim X₁ X₂ hX₁ hX₂ hlo₁ hhi₁ hlo₂ hhi₂ hslo hshi hcap j k v w
  have he:=finite_physical_pair_affine F rows radialMajorant U bΦ mesh ε hU.le hsΦ
    radialMajorant_nonneg hη (fun u hu=>(hrows u hu).2)
    (fun u hu=>hkeep u (hrows u hu).1) radialMajorant_one degree control Ci ha
    T width z height hw hwmax hz hh hzim (numeratorFourierProfiles j k v w) X₁ X₂
    hX₁ hX₂ hlo₁ hhi₁ hlo₂ hhi₂ hslo hshi hcap
  have heq :
      (∑u∈rows, ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
          (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏i,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2) =
      (∑u∈rows, ‖polynomial ((momentData η).character (momentElement u)) false
        ((numeratorFourierProfiles j k v w).profile 0) X₁ 0 0 *
        polynomial ((momentData η).character (momentElement u)) false
        ((numeratorFourierProfiles j k v w).profile 1) X₂ 0 0 *
        ∏i,normalizedSlot η rowMaskElement 1 u.val (CenteredMomentPrimeSlot.primePool F.modulus ⊤ 2 (U^(width i)))
          (physicalSlotCoefficient η F.W (U^(width i)) (z i)) 0 (U^(width i))‖^2) := by
    apply Finset.sum_congr rfl
    intro u hu
    dsimp only [η]
    simp_rw [numerator_fourier_polynomial_zero,numerator_fourier_polynomial_one,
      source_physical_slot_conj F u _ _ (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _),
      norm_mul,inverse_annular_norm_eq F u j v X₁ hX₁,
      inverse_annular_norm_eq F u k w X₂ hX₂,←map_prod,Complex.norm_conj]
  rw [heq]
  apply he.trans
  have hd:=diagonalControl_nonneg radialMajorant
  have hp:=hprofile j k v w
  calc
    _ ≤ (Ci*(1+diagonalControl radialMajorant))*
        (Cp*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2)*(1+height)^degree*U^(1+ε) := by
      gcongr
      linarith
    _ = _ := by dsimp [C];ring

end Cycle61.Numerator.Fourth

end
/- END ORIGINAL Cycle61.Numerator.Fourth.Fourier -/

/- BEGIN ORIGINAL Cycle61.Numerator.Fourth.Hybrid; sha256 b9085bc1968d12b9d4a1249c8614d905efd3f83dae659d433d5937f97f41d2d3 -/
section
                                       
                                            

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace Cycle61.Numerator.Fourth
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands CenteredMomentScaleSupremum
open CenteredMomentSectorLocalization CenteredMomentDetectorPlainFiberSource
open Cycle25WeightedNumeratorPhysical

/-- The improved interior is combined with genuine original small-plain,
small-slot and empty-slot bounds, covering every dual scale in restoration. -/
theorem hybrid_fourier {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ)
    (hk0 : 7/10≤κ) (hk1 : κ≤3/4) (hb : 51/100≤ HeckeZeroSupremum.beta)
    (hkb : 2*HeckeZeroSupremum.beta-1≤κ)
    (bΦ mesh ε : ℝ) (hε : 0<ε)
    (hsΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0<Ci)
    (hinput : ∀ᶠU:ℝ in atTop,AffineAt F bΦ mesh ε U di control Ci) :
    ∃degree J:ℕ,∃C:ℝ,0<C ∧ ∀ᶠU:ℝ in atTop,
      1<U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ U) →
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height n:ℝ,
      (∀i,0≤ width i) → (∀i,width i≤ mesh) →
      (∀i,width i≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀i,(z i).re=17/50) → 0≤ height → (∀i,|(z i).im|≤ height) →
      0≤ n → n≤2 →
      ((∃d t:ℝ,Arithmetic.dMinus≤ d ∧ d≤ Arithmetic.dPlus ∧ 0≤ t ∧ t≤ Arithmetic.t0 ∧
        n=Physical.plainScale d t ∧ (∑i,width i)≤ Physical.affineCapacity d t) ∨
        (2*n+6*κ*(∑i,width i)≤1 ∨ T=∅)) →
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ → X₁≤ U^n → X₂≤ U^n →
      length U X₁≤ n → length U X₂≤ n → ∀j k:Fin 2,∀v w:ℝ,
      (∑u∈rows,‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏i,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2)
      ≤ (C*(1+height)^degree*U^(1+D.t+ε))*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  obtain ⟨Ja,Ca,hCa,ha⟩:=affine_fourier F bΦ mesh ε hsΦ di control Ci hCi hinput
  obtain ⟨dp,Jp,Cp,hCp,hp⟩:=certified_reflected_fourier_moment F κ hk0 hk1 hb hkb
  obtain ⟨Jz,Cz,hCz,hz⟩:=certified_reflected_zero_fourier_moment F
  refine ⟨di+dp,Ja+Jp+Jz,Ca+Cp+Cz,by positivity,?_⟩
  filter_upwards [ha,hp,hz] with U ha hp hz
  have hU:=ha.1
  have hUp:=zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows T width z height n hw hmesh hwmax hzre hh him hn hn2 hcap X₁ X₂ hX₁ hX₂ hX₁max hX₂max hx₁ hx₂ j k v w
  have hsum:0≤∑i,width i:=Finset.sum_nonneg (fun i _=>hw i)
  have hUε:U^(1+ε)≤ U^(1+D.t+ε):=Real.rpow_le_rpow_of_exponent_le hU.le (by linarith [D.t_pos])
  have hUt:U^(1+D.t)≤ U^(1+D.t+ε):=Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)
  have baseline (hbudget : 2*n+6*κ*(∑i,width i)≤1) := by
    have hn1:n≤1:=by nlinarith
    have hpow:U^n≤ U:=by simpa using Real.rpow_le_rpow_of_exponent_le hU.le hn1
    have hb':=hp.2 rows hrows T width z height hw hwmax hzre hh him X₁ X₂ hX₁ hX₂
      (hX₁max.trans hpow) (hX₂max.trans hpow) (by linarith) j k v w
    exact hb'
  rcases hcap with ⟨d,t,hd0,hd1,ht0,ht1,heq,hslots⟩ | hold
  · have hnhi:= (Physical.plainScale_interior ⟨hd0,hd1⟩ ⟨ht0,ht1⟩).2
    have hslotshi:= (Physical.affineCapacity_interior ⟨hd0,hd1⟩ ⟨ht0,ht1⟩).2
    rw [←heq] at hnhi
    have hx1hi:length U X₁≤264/625:=hx₁.trans hnhi.le
    have hx2hi:length U X₂≤264/625:=hx₂.trans hnhi.le
    have hs37:(∑i,width i)≤37/1000:=hslots.trans hslotshi.le
    by_cases hslo:17/500≤∑i,width i
    · by_cases h1:41/100≤ length U X₁
      · by_cases h2:41/100≤ length U X₂
        · have hbound:=ha.2 rows hrows T width z height hw hmesh hzre hh him X₁ X₂ hX₁ hX₂
            h1 (by linarith) h2 (by linarith) hslo (by linarith)
            (Physical.affine_shortening (heq ▸ hx₁) (heq ▸ hx₂) hslots) j k v w
          apply hbound.trans
          gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]
        · have hc:=Physical.small_plain_shortening (le_of_not_ge h2) hx1hi hs37
          have hb':=hp.2 rows hrows T width z height hw hwmax hzre hh him X₁ X₂ hX₁ hX₂
            (hX₁max.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hU.le (by linarith : n≤1)))
            (hX₂max.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hU.le (by linarith : n≤1)))
            (by nlinarith) j k v w
          apply hb'.trans
          gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]
      · have hc:=Physical.small_plain_shortening (le_of_not_ge h1) hx2hi hs37
        have hb':=hp.2 rows hrows T width z height hw hwmax hzre hh him X₁ X₂ hX₁ hX₂
          (hX₁max.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hU.le (by linarith : n≤1)))
          (hX₂max.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hU.le (by linarith : n≤1)))
          (by nlinarith) j k v w
        apply hb'.trans
        gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]
    · have hc:=Physical.small_slot_shortening hx1hi hx2hi (le_of_not_ge hslo)
      have hb':=hp.2 rows hrows T width z height hw hwmax hzre hh him X₁ X₂ hX₁ hX₂
        (hX₁max.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hU.le (by linarith : n≤1)))
        (hX₂max.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hU.le (by linarith : n≤1)))
        (by nlinarith) j k v w
      apply hb'.trans
      gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]
  · rcases hold with hbudget | hempty
    · apply (baseline hbudget).trans
      gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]
    · subst T
      simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one]
      have hb':=hz.2 rows hrows X₁ X₂ hX₁ hX₂
        (hX₁max.trans (Real.rpow_le_rpow_of_exponent_le hU.le hn2))
        (hX₂max.trans (Real.rpow_le_rpow_of_exponent_le hU.le hn2)) j k v w
      apply hb'.trans
      have hheight:1≤(1+height)^(di+dp):=one_le_pow₀ (by linarith)
      have hc:Cz≤(Ca+Cp+Cz)*(1+height)^(di+dp):=by nlinarith
      gcongr <;> first | exact hc | linarith [norm_nonneg v,norm_nonneg w]

end Cycle61.Numerator.Fourth

end
/- END ORIGINAL Cycle61.Numerator.Fourth.Hybrid -/
