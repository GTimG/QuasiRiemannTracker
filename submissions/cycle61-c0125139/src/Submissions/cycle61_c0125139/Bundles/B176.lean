/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B117
import Submissions.cycle61_c0125139.Bundles.B133
import Submissions.cycle61_c0125139.Bundles.B135
import Submissions.cycle61_c0125139.Bundles.B150
import Submissions.cycle61_c0125139.Bundles.B155
import Submissions.cycle61_c0125139.Bundles.B161
import Submissions.cycle61_c0125139.Bundles.B172
import Submissions.cycle61_c0125139.Bundles.B173
import Submissions.cycle61_c0125139.Bundles.B174
import Submissions.cycle61_c0125139.Bundles.B175

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainCoarseNormalized; sha256 2f7112e80c4daa3a8de2bd171ea131f26d7f5afadc641f74b3a4f30cb391a014 -/
section
                                                          
                                                      
                                                        
                                                       

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstSourceReduction CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstScale CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondInputCapacitySource CenteredMomentSectorLocalization
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonProfile
open Cycle61Moment CompletedGauss CenteredMomentOriginalCommonHarmonic
local notation "O" => HeckeFamily.O

lemma geometry_high_factor_coarse (reflected : Bool)(C Z B : ℝ)
    (bin : ℤ×(Fin 5→ℤ))(hZ : 1≤ Z)(hB : 0≤ B)
    (hlo : 1≤2*geometryDCompensator bin)(hhi : geometryDCompensator bin≤ Z^B) :
    geometryHighFactor reflected C bin≤2*(C^2+1)*Z^B := by
  have hp:=geometryDCompensator_pos bin
  have hz:=Real.one_le_rpow hZ hB
  cases reflected
  · change 2*C^2*geometryDCompensator bin≤ _
    nlinarith [mul_le_mul_of_nonneg_left hhi (sq_nonneg C)]
  · change (geometryDCompensator bin)⁻¹≤ _
    have hi : (geometryDCompensator bin)⁻¹≤2 := by
      rw [←one_div]
      apply (div_le_iff₀ hp).mpr
      simpa [mul_comm] using hlo
    nlinarith [sq_nonneg C]

 theorem actual_geometry_high_mass_coarse {α : Type}[Fintype α][DecidableEq α]
    (reflected : Bool)(N : ℕ)(lo ap : ℝ)(hlo : 0< lo)(hap : 0< ap)
    (s : Input α)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(M Z ξ B ε : ℝ)
    (hZ : 1< Z)(hK : 0< Z^M)(hB : 0≤ B)(hε : 0≤ε)
    (hcard : Fintype.card α≤ N)(hlower : lo≤ s.lower)(hs : Squarefree seed)
    (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)(hsource : sourceRadius s≤ Z^B)
    (hs₁ : ∀x,s.W₁ x≠0→ ap≤ x)(hs₂ : ∀x,s.W₂ x≠0→ ap≤ x)
    (hA : |Real.logb Z (CenteredMomentExceptionalAmplitudePair.volume s.toData)|≤ B)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK bin)) :
    geometryFirstHighMass reflected s R seed W M Z ξ ε hK bin j≤
      2*((geometrySupportConstant N lo ap ap)^2+1)*Z^(B*ε+6*B) := by
  have hn:=actual_geometry_norm_caps s R seed (Z^M) Z ξ B hs hz₁ hz₂ hsource j.1.val
  have hd:=actual_geometry_D_compensation s R seed (Z^M) Z ξ B hs hz₁ hz₂ hsource bin j.1
  have hdlo := (hn 1).1
  change 1≤(j.1.val.1.val.2.absNorm:ℝ) at hdlo
  have hg:=geometry_high_factor_coarse reflected (geometrySupportConstant N lo ap ap)
    Z B bin hZ.le hB (by linarith [hdlo,hd.2]) (hd.1.trans (hn 1).2)
  have hh:=actual_geometry_uniform_high_mass reflected N lo ap hlo hap s R seed W M Z ξ B ε
    hZ hK hε hcard hlower hs hz₁ hz₂ hsource hs₁ hs₂ bin j
  have hb:=geometry_high_side_box reflected (Real.logb Z (CenteredMomentExceptionalAmplitudePair.volume s.toData)) B
    (geometryExponents s R seed (Z^M) Z ξ j.1.val) hB hA (fun k=>
      ⟨Real.logb_nonneg hZ (hn k).1,
       (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le (hn k).1)).mpr (hn k).2⟩)
  have hz : 0< Z:=zero_lt_one.trans hZ
  have hi : (Z^(geometryHighSide reflected (Real.logb Z (CenteredMomentExceptionalAmplitudePair.volume s.toData))
      (geometryExponents s R seed (Z^M) Z ξ j.1.val)))⁻¹≤ Z^(5*B) := by
    rw [←Real.rpow_neg hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith [(abs_le.mp hb).1]
  calc
    _≤ geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      Z^(B*ε)*(Z^(geometryHighSide reflected (Real.logb Z (CenteredMomentExceptionalAmplitudePair.volume s.toData))
      (geometryExponents s R seed (Z^M) Z ξ j.1.val)))⁻¹ := by
        simpa [div_eq_mul_inv] using hh
    _≤(2*((geometrySupportConstant N lo ap ap)^2+1)*Z^B)*Z^(B*ε)*Z^(5*B) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hz.le _)
      · exact hi
      · positivity
      · positivity
    _=_ := by
      rw [show B*ε+6*B=B+B*ε+5*B by ring,Real.rpow_add hz,Real.rpow_add hz]
      ring

/-- The child-volume threshold precedes all sources and both heights. -/
theorem eventual_actual_main_normalizer_coarse (N : ℕ)(lo εv : ℝ)
    (hlo : 0< lo)(hev : 0<εv) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀{α : Type}[Fintype α]
      (s : Input α),Fintype.card α≤ N → lo≤ s.lower →
    ∀(reflected _left second : Bool)(l : FirstSourceLabel)
      (_hC : Supported l.1.1)(_hD : Supported l.1.2),
      primeSupport l.1.1=primeSupport l.1.2 →
    ∀(R : Ideal O)(alloc : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
      (χ : Character)(t : ℝ),
      frozenCoefficient alloc.val (if reflected then l.1.2 else l.1.1) R s.ν s.W s.P≠0 →
    ∀(C₂ D₂ : Ideal O)(_hC₂ : Supported C₂)(_hD₂ : Supported D₂),
      primeSupport C₂=primeSupport D₂ →
    ∀(U : Finset (CommonIndex C₂ D₂))(M a ξ reserve B ε : ℝ),0≤ B → 0≤ε →
      ((l.1.1.absNorm:ℝ)≤ Z^B ∧ (l.1.2.absNorm:ℝ)≤ Z^B) →
      ((C₂.absNorm:ℝ)≤ Z^B ∧ (D₂.absNorm:ℝ)≤ Z^B) →
      |M|≤ B → |Real.logb Z (volume s)|≤ B → |a|≤ B →
      |frequencyLoss Z 32 ξ+reserve|≤ B →
      (firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l /
        volume (child s (if reflected then l.1.2 else l.1.1) R alloc χ t))*
        normalizer C₂ D₂ U*((if second then D₂ else C₂).absNorm:ℝ)^(ε-1)
        ≤ Z^(33*B+εv+B*ε) := by
  filter_upwards [eventual_actual_child_high_coefficient N lo εv hlo hev] with Z hz
  refine ⟨hz.1,?_⟩
  intro α _ s hcard hlow reflected left second l hC hD heq R alloc χ t halloc
    C₂ D₂ hC₂ hD₂ heq₂ U M a ξ reserve B ε hB hε hfirst hsecond hM hA ha hω
  have hZ : 0< Z:=zero_lt_one.trans hz.1
  let E := if second then D₂ else C₂
  have hE : E≠0 := by
    cases second
    · exact hC₂.1
    · exact hD₂.1
  have hn : 0<(E.absNorm:ℝ):=norm_pos E hE
  have hcap : (E.absNorm:ℝ)≤ Z^B := by
    cases second
    · exact hsecond.1
    · exact hsecond.2
  have hcoef:=hz.2 s hcard hlow reflected left second l hC hD heq R alloc χ t halloc
    C₂ D₂ hC₂ U M a ξ reserve 0
  have hbox:=actual_high_coordinate_box reflected left second l hC hD C₂ D₂ hC₂ hD₂ heq₂
    U Z M (Real.logb Z (volume s)) a ξ reserve 0 B hz.1 hB hfirst hsecond hM hA ha hω
    (by simpa using hB)
  have hc : Z^(-a)*((firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l /
      volume (child s (if reflected then l.1.2 else l.1.1) R alloc χ t))*
      normalizer C₂ D₂ U/(E.absNorm:ℝ))≤ Z^(32*B+εv) := by
    have he : Z^(Real.logb Z (E.absNorm:ℝ))=(E.absNorm:ℝ):=
      Real.rpow_logb hZ hz.1.ne' hn
    change _≤ Z^(_+εv) at hcoef
    rw [he] at hcoef
    have hh : Z^(-a)*((firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l /
      volume (child s (if reflected then l.1.2 else l.1.1) R alloc χ t))*
      normalizer C₂ D₂ U/(E.absNorm:ℝ))≤
      Z^((actualHighCoordinates reflected left second l C₂ D₂ U Z M (Real.logb Z (volume s)) a ξ reserve 0) 0+εv) := by
        simpa [div_eq_mul_inv,mul_assoc] using hcoef
    apply hh.trans
    exact Real.rpow_le_rpow_of_exponent_le hz.1.le (by linarith [(hbox 0).2])
  have hp : (E.absNorm:ℝ)^ε≤ Z^(B*ε) := by
    rw [Real.rpow_mul hZ.le]
    exact Real.rpow_le_rpow hn.le hcap hε
  have hr := mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hZ.le a)
  rw [←mul_assoc,←Real.rpow_add hZ,add_neg_cancel,Real.rpow_zero,one_mul] at hr
  calc
    _=((firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l /
      volume (child s (if reflected then l.1.2 else l.1.1) R alloc χ t))*
      normalizer C₂ D₂ U/(E.absNorm:ℝ))*(E.absNorm:ℝ)^ε := by
        rw [Real.rpow_sub hn,Real.rpow_one]; ring
    _≤(Z^a*Z^(32*B+εv))*Z^(B*ε) :=
      mul_le_mul hr hp (Real.rpow_nonneg hn.le _) (by positivity)
    _=Z^(a+32*B+εv+B*ε) := by simp only [←Real.rpow_add hZ]; congr 1; ring
    _≤ _ := Real.rpow_le_rpow_of_exponent_le hz.1.le (by linarith [(abs_le.mp ha).2])

lemma actual_child_profile_product_coarse {α : Type}[Fintype α][DecidableEq α]
    (s : Input α)(N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)(hcard : Fintype.card α≤ N)
    (hM : ∀j,s.M j≤ Cs)(C R : Ideal O)(alloc : actualAllocations s.pools C)
    (χ : Character)(t : ℝ) :
    (∏j,(child s C R alloc χ t).M j)^2≤(Cs^N)^2 := by
  have hm0 : 0≤∏j,(child s C R alloc χ t).M j :=
    Finset.prod_nonneg (fun j _=>zero_le_one.trans ((child s C R alloc χ t).M_ge_one j))
  have hp : (∏j,(child s C R alloc χ t).M j)≤ Cs^N := by
    calc
      _≤∏_j : liveIndices alloc.val,Cs := Finset.prod_le_prod₀
        (fun j _=>zero_le_one.trans ((child s C R alloc χ t).M_ge_one j))
        (fun j _=>hM j.val)
      _=Cs^(Fintype.card (liveIndices alloc.val)) := by simp
      _≤ Cs^N := pow_le_pow_right₀ hCs ((live_card_le alloc.val).trans hcard)
  nlinarith

/-- Literal normalized main coefficient, including the child profile product.
The large coarse exponent is uniform in the first and second heights. -/
theorem eventual_actual_geometry_main_scalar_cap (N : ℕ)(lo ap εv : ℝ)
    (hlo : 0< lo)(hap : 0< ap)(hev : 0<εv) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀{α : Type}[Fintype α][DecidableEq α]
    (s : Input α),Fintype.card α≤ N → lo≤ s.lower →
    ∀(reflected _left second : Bool)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ))
      (M ξ a reserve B εmass ε Cs : ℝ)(hK : 0< Z^M),
      0≤ B → 0≤εmass → 0≤ε → 1≤ Cs → (∀j,s.M j≤ Cs) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^B →
      (∀x,s.W₁ x≠0→ ap≤ x) → (∀x,s.W₂ x≠0→ ap≤ x) →
      |M|≤ B → |Real.logb Z (volume s)|≤ B → |a|≤ B →
      |frequencyLoss Z 32 ξ+reserve|≤ B →
    ∀(bin : ℤ×(Fin 5→ℤ))
      (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK bin)),
    let l:=geometryFirstLabel s R seed (Z^M) Z ξ hK bin j
    ∀(Rfirst : Ideal O)
      (alloc : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
      (χ : Character)(t : ℝ),
      frozenCoefficient alloc.val (if reflected then l.1.2 else l.1.1) Rfirst s.ν s.W s.P≠0 →
    ∀(C₂ D₂ : Ideal O)(_hC₂ : Supported C₂)(_hD₂ : Supported D₂),
      primeSupport C₂=primeSupport D₂ →
      ((C₂.absNorm:ℝ)≤ Z^B ∧ (D₂.absNorm:ℝ)≤ Z^B) →
    ∀U : Finset (CommonIndex C₂ D₂),
      geometryFirstHighMass reflected s R seed W M Z ξ εmass hK bin j*
      ((firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l /
        volume (child s (if reflected then l.1.2 else l.1.1) Rfirst alloc χ t))*
        normalizer C₂ D₂ U/lowerFactor N lo ap)*
      (∏i,(child s (if reflected then l.1.2 else l.1.1) Rfirst alloc χ t).M i)^2*
      ((if second then D₂ else C₂).absNorm:ℝ)^(ε-1)≤
      (2*((geometrySupportConstant N lo ap ap)^2+1)*(Cs^N)^2/lowerFactor N lo ap)*
      Z^(39*B+B*εmass+B*ε+εv) := by
  filter_upwards [eventual_actual_main_normalizer_coarse N lo εv hlo hev] with Z hz
  refine ⟨hz.1,?_⟩
  intro α _ _ s hcard hlow reflected left second R seed W M ξ a reserve B εmass ε Cs
    hK hB hεmass hε hCs hM hs hz₁ hz₂ hsource hs₁ hs₂ hMbox hA habox hω bin j l
    Rfirst alloc χ t halloc C₂ D₂ hC₂ hD₂ heq₂ hsecond U
  have hn:=actual_geometry_norm_caps s R seed (Z^M) Z ξ B hs hz₁ hz₂ hsource j.1.val
  have hf : (l.1.1.absNorm:ℝ)≤ Z^B ∧ (l.1.2.absNorm:ℝ)≤ Z^B := ⟨(hn 0).2,(hn 1).2⟩
  have hmass:=actual_geometry_high_mass_coarse reflected N lo ap hlo hap s R seed W M Z ξ B
    εmass hz.1 hK hB hεmass hcard hlow hs hz₁ hz₂ hsource hs₁ hs₂ hA bin j
  have hc:=hz.2 s hcard hlow reflected left second l
    (geometryFirstSource s R seed (Z^M) Z ξ hK bin j.1).hC
    (geometryFirstSource s R seed (Z^M) Z ξ hK bin j.1).hD
    (geometryFirstSource s R seed (Z^M) Z ξ hK bin j.1).sameSupport
    Rfirst alloc χ t halloc C₂ D₂ hC₂ hD₂ heq₂ U M a ξ reserve B ε hB hε hf hsecond
    hMbox hA habox hω
  have hp:=actual_child_profile_product_coarse s N Cs hCs hcard hM _ Rfirst alloc χ t
  have hl:=lowerFactor_pos N lo ap hlo hap
  have hm0:=geometry_first_high_mass_nonneg reflected s R seed W M Z ξ εmass hK bin j
  have hnorm0 : 0≤(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l /
      volume (child s (if reflected then l.1.2 else l.1.1) Rfirst alloc χ t))*
      normalizer C₂ D₂ U*((if second then D₂ else C₂).absNorm:ℝ)^(ε-1) := by
    apply mul_nonneg (mul_nonneg ?_ (normalizer_pos C₂ D₂ hC₂ U).le) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact div_nonneg (first_main_radius_pos reflected (Z^M) (volume s) Z ξ (3*a) reserve
      (zero_lt_one.trans hz.1) l).le (CenteredMomentAmplificationChildInput.volume_pos _).le
  have hzpos : 0< Z:=zero_lt_one.trans hz.1
  have hmasscap0 : 0≤2*((geometrySupportConstant N lo ap ap)^2+1)*Z^(B*εmass+6*B) :=
    mul_nonneg (by nlinarith [sq_nonneg (geometrySupportConstant N lo ap ap)]) (Real.rpow_nonneg hzpos.le _)
  have hall:=mul_le_mul (mul_le_mul hmass hc hnorm0 hmasscap0) hp
    (sq_nonneg _) (mul_nonneg hmasscap0 (Real.rpow_nonneg hzpos.le _))
  have hh:=div_le_div_of_nonneg_right hall hl.le
  convert hh using 1
  · ring
  · rw [show 39*B+B*εmass+B*ε+εv=(B*εmass+6*B)+(33*B+εv+B*ε) by ring,
      Real.rpow_add (zero_lt_one.trans hz.1)]
    ring

section ScalarConstructor
variable {α : Type}[Fintype α][DecidableEq α]
variable (reflected : Bool)(s : Input α)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ))
variable (M Z ξ εmass a reserve : ℝ)(hK : 0< Z^M)(bin : ℤ×(Fin 5→ℤ))
variable (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK bin))
variable (Rfirst : Ideal O)
variable (alloc : actualAllocations s.pools
  (if reflected then (geometryFirstLabel s R seed (Z^M) Z ξ hK bin j).1.2
   else (geometryFirstLabel s R seed (Z^M) Z ξ hK bin j).1.1))
variable (χ : Character)(t : ℝ)(C₂ D₂ : Ideal O)(U : Finset (CommonIndex C₂ D₂))
variable (N : ℕ)(lo ap : ℝ)

def geometryMainCoarseScalar : ℂ :=
  (Real.sqrt (geometryFirstHighMass reflected s R seed W M Z ξ εmass hK bin j*
    ((firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve
      (geometryFirstLabel s R seed (Z^M) Z ξ hK bin j)/
      volume (child s _ Rfirst alloc χ t))*normalizer C₂ D₂ U/lowerFactor N lo ap)) : ℝ)

omit [DecidableEq α] in
lemma actual_geometry_main_coarse_scalar_norm (hZ : 1< Z)(hC₂ : Supported C₂)
    (hlo : 0< lo)(hap : 0< ap) :
    ‖geometryMainCoarseScalar reflected s R seed W M Z ξ εmass a reserve hK bin j
      Rfirst alloc χ t C₂ D₂ U N lo ap‖^2=
      geometryFirstHighMass reflected s R seed W M Z ξ εmass hK bin j*
      ((firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve
        (geometryFirstLabel s R seed (Z^M) Z ξ hK bin j)/
        volume (child s _ Rfirst alloc χ t))*normalizer C₂ D₂ U/lowerFactor N lo ap) := by
  have hm:=geometry_first_high_mass_nonneg reflected s R seed W M Z ξ εmass hK bin j
  have hl:=lowerFactor_pos N lo ap hlo hap
  have hk:=first_main_radius_pos reflected (Z^M) (volume s) Z ξ (3*a) reserve
    (zero_lt_one.trans hZ) (geometryFirstLabel s R seed (Z^M) Z ξ hK bin j)
  have hv:=CenteredMomentAmplificationChildInput.volume_pos (child s _ Rfirst alloc χ t)
  have hn:=(normalizer_pos C₂ D₂ hC₂ U).le
  unfold geometryMainCoarseScalar
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt]
  exact mul_nonneg hm (div_nonneg (mul_nonneg (div_nonneg hk.le hv.le) hn) hl.le)
end ScalarConstructor

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_high_factor_coarse
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_high_mass_coarse
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_main_normalizer_coarse

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_child_profile_product_coarse
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_main_scalar_cap

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_coarse_scalar_norm

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainCoarseNormalized -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainCoarseFamily; sha256 9ab5aeb70109181eb2521fb5fab7c857dfc19e094fb893fa86c97e4dcf1ab307 -/
section
                                                                
                                                                 
                                                         
                                                      
                                                        

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic CenteredMomentNaturalRowSource CenteredMomentEnergyState Cycle61FinalNatural
open CenteredMomentSecondEnergySplit CenteredMomentWholeDivisorShell
open CenteredMomentSourceRow CenteredMomentCommonPairedSource CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical CenteredMomentSecondCanonicalScalar
open CenteredMomentCommonHeightEnvelope CenteredMomentSecondInputCapacitySource
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstSourceReduction
local notation "O" => HeckeFamily.O
local instance geometryMainCoarseFamilySumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem geometry_ordinary_high_image_sum
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→ SecondInputDatum α)
    (χ : Label→ RayCharacter) (Q : Label→ Ideal O) (m : Label→ O)
    (hrows : ∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius)
    (rows : Finset (secondLiveRows
      (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block)))
    (second : Bool)
    (weight height : secondLiveRows (fun l=>(d l).block)→ℝ)
    (Ds : secondLiveRows (fun l=>(d l).block)→ Finset (Ideal O)) :
    (∑r∈rows,weight (ordinaryHighOriginalRow d χ Q m hrows r)*
      highNormalizedRowCost second (fun l=>ordinarySecondDatum (d l) (χ l) (Q l) (m l))
        r (height (ordinaryHighOriginalRow d χ Q m hrows r))
        (Ds (ordinaryHighOriginalRow d χ Q m hrows r))) =
      ∑r∈rows.image (ordinaryHighOriginalRow d χ Q m hrows),
        weight r*highNormalizedRowCost second d r (height r) (Ds r) := by
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro r _
    rw [ordinary_high_original_row_cost]
  · intro r _ s _ h
    exact ordinary_high_original_row_injective d χ Q m hrows h

theorem actual_geometry_main_all_height_coarse_family {α : Type}[Fintype α][DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(hα : Fintype.card α≤ N)
    (B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ : ℝ)
    (hB : 0≤ B)(hloss : 0< loss)(hε : 0<ε)(hpad : 0< pad)
    (hCs : 1≤ Cs)(hb : 1≤ b)(hbs : 1≤ bs)(hwindow : 0≤ window)(hcap : 0≤ plainCap)
    (hlo : 0< lo)(hap : 0< ap)(hev : 0<εvolume)(hem : 0≤εmass)
    (hξ : 0≤ξ)(hξε : ξ≤ loss) :
    ∃K : ℝ,0< K ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
      ∀{Label : Type}[Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(Dfirst a reserve t : ℝ)(hK : 0< Z^Dfirst),
      Squarefree seed → Endpoints b bs bs s →
      lo≤ s.lower → sourceRadius s≤ Z^B → |Real.logb Z (volume s)|≤ B → |Dfirst|≤ B →
      |a|≤ B → |frequencyLoss Z 32 ξ+reserve|≤ B → (∀j,s.M j≤ Cs) →
      (∀j,CenteredMomentSlotRatios.logWindow (s.lo j) (s.hi j)≤ window) →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^plainCap) →
      (∀j,s.P j≤ Z^plainCap) →
      (∀x,s.W₁ x≠0→ ap≤ x) → (∀x,s.W₂ x≠0→ ap≤ x) →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤ a → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (column : Label→↥(firstLiveColumns (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin) (fun _=>logAnnulus))),
      Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (column l).val,
        (column l).val.2.1.val)) →
      let C := fun l=>geometryColumnIdeal reflected s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      let χ := fun l=>geometryColumnCharacter reflected s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      ∀alloc : (l : Label)→ actualAllocations s.pools (C l),
      (∀l,frozenCoefficient (alloc l).val (C l) R s.ν s.W s.P≠0) →
      let slots := fun l=>liveIndices (alloc l).val
      let source := fun l=>child s (C l) R (alloc l) (χ l) t
      let first := fun l=>geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      let projector := fun l=>(column l).val.2.1.val
      let Kmain := firstMainRadius reflected (Z^Dfirst) (volume s) Z ξ (3*a) reserve
      let Tsec := firstMainFourierScale reflected (Z^Dfirst) (volume s) Z ξ (3*a) reserve b N
      let hprojector := fun l=>actual_first_live_squarefree
        (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin) (fun _=>logAnnulus) (column l).val (column l).property
      let hz₁ : ∀l,(source l).W₁ 0=0 := fun _=>hs₁
      let hz₂ : ∀l,(source l).W₂ 0=0 := fun _=>hs₂
      let hKm : ∀l,0< Kmain (first l) := fun l=>first_main_radius_pos reflected (Z^Dfirst) (volume s)
        Z ξ (3*a) reserve (zero_lt_one.trans hZ) (first l)
      let Index := (l : Label)×ActualSecondBlockIndex (source l) (R*C l) (projector l)
        (Kmain (first l)) (Tsec (first l)) Z ξ
      let datum := fun q : Index=>actualSecondBlockDatum (slots q.1) (source q.1) (R*C q.1) (projector q.1)
        (hprojector q.1) (hz₁ q.1) (hz₂ q.1) (Kmain (first q.1)) (Tsec (first q.1)) Z ξ (hKm q.1) q.2
      let block := fun q : Index=>(datum q).block
      ∀(rows : Finset (secondLiveRows block))(second : Bool)(W : 𝓢(ℝ,ℂ))(height : rows→ℝ)(Ds : rows→ Finset (Ideal O))
        (control T B₁ B₂ : ℝ),0≤ control → 1≤ T → 0≤ B₁ → 0≤ B₂ →
      (∀x,‖s.W₁ x‖≤ B₁) → (∀x,‖s.W₂ x‖≤ B₂) → (B₁*B₂)^2≤ control →
      (∀r : rows,∀L∈Ds r,Squarefree L ∧ T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      let outer := fun r : rows=>(Kmain (first r.val.val.1.1)/volume (source r.val.val.1.1))*
        normalizer (datum r.val.val.1).C (datum r.val.val.1).D (datum r.val.val.1).inactive/lowerFactor N lo ap
      let cost := fun r : rows=>geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin
        (column r.val.val.1.1).val * outer r * highNormalizedRowCost second datum r.val (height r) (Ds r)
      (∑r : rows,cost r)≤ K*control*(2*T)^(3*ε)*
        Z^(B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
          8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+pad) := by
  let SB:=B+loss
  let scalarCap:=39*SB+SB*εmass+SB*ε+εvolume
  let Cscalar:=2*((geometrySupportConstant N lo ap ap)^2+1)*(Cs^N)^2/lowerFactor N lo ap
  have hSB : 0≤ SB:=by dsimp [SB]; positivity
  have hCscalar : 0< Cscalar := by
    dsimp [Cscalar]
    apply div_pos _ (lowerFactor_pos N lo ap hlo hap)
    exact mul_pos (by nlinarith [sq_nonneg (geometrySupportConstant N lo ap ap)])
      (sq_pos_of_pos (pow_pos (zero_lt_one.trans_le hCs) _))
  obtain ⟨D,hD,hselection⟩:=actual_geometry_high_weighted_normalized_family_selection
    η₀ u₀ F₀ R₀ hu₀ N b bs loss B B ξ hb hbs hloss hB hB hξ hξε
  obtain ⟨Kc,hKc,hcoarse⟩:=actual_child_weighted_coarse_columns N hα
    (8*SB) loss ε pad Cs b bs window plainCap scalarCap (by positivity)
    hloss hε hpad hCs hb hbs hwindow hcap
  refine ⟨D*Kc*Cscalar,by positivity,?_⟩
  filter_upwards [hselection,hcoarse,eventual_actual_geometry_main_scalar_cap N lo ap εvolume hlo hap hev,
    eventual_geometry_child_source_cap N b bs loss hb hbs hloss,
    eventual_geometry_joint_support η₀ u₀ F₀ R₀ hu₀ b loss N (zero_lt_one.trans_le hb) hloss]
    with Z hselect hc hscalar hchild hjoint
  intro hZ Label _ reflected s R seed Dfirst a reserve t hK hseed he hlow hsource hA hMbox habox hω
    hM hwin hscales hP hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin column hinj C χ alloc halloc slots source first projector
    Kmain Tsec hprojector hz₁ hz₂ hKm Index datum block rows second W
    height Ds control T B₁ B₂ hcontrol hT hB₁ hB₂ hW₁ hW₂ hcontrolB hDs outer cost
  let label := fun q : Index=>first q.1
  let left := !reflected
  let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
  have hunit : ∀l,unit l≠0 := fun _=>Units.ne_zero _
  have hf : ∀r : secondLiveRows block,jointFirstFrequency left u₀ unit (secondEncodedRow block label r)≠0 :=
    fun r=>actual_joint_first_frequency_ne_zero left u₀ unit (secondEncodedRow block label r)
      hu₀ (hunit _) (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin (column r.val.1.1).val.1).hC
  let key := fun r : rows=>secondEncodedNonzeroRow block label r.val left u₀ unit (hf r.val)
  have hzpos : 0< Z:=zero_lt_one.trans hZ
  have hV : volume s≤ Z^B :=
    (Real.logb_le_iff_le_rpow hZ (volume_pos s)).mp (abs_le.mp hA).2
  have hKM : Z^Dfirst≤ Z^B:=Real.rpow_le_rpow_of_exponent_le hZ.le (abs_le.mp hMbox).2
  have houter : ∀r : rows,0≤ outer r := by
    intro r
    dsimp only [outer]
    exact div_nonneg (mul_nonneg (div_nonneg (hKm _).le (volume_pos _).le)
      (normalizer_pos _ _ (datum r.val.val.1).hC _).le) (lowerFactor_pos N lo ap hlo hap).le
  obtain ⟨pick,hpick,hinjpick,hinjreflect,hsum⟩:=hselect hZ reflected s R seed Dfirst a reserve t hK
    hseed hα he hV hKM hs₁ hs₂ ha hreserve bin column hinj alloc halloc rows second W εmass
    height Ds outer houter
  let κ:=Finset.univ.image key
  let chooseRow := fun k : κ=>(pick k).val
  let col := fun k : κ=>(column (chooseRow k).val.1.1).val
  let v := fun k : κ=>datum (chooseRow k).val.1
  let encoded := fun k : κ=>if second then reflectedNonzeroJointLabel (key (pick k)) else key (pick k)
  let E := fun k : κ=>if second then (v k).D else (v k).C
  have hE : ∀k,Supported (E k) := by intro k; cases second <;> first | exact (v k).hC | exact (v k).hD
  let ψ := fun k : κ=>if second then (chooseRow k).val.2.2.1⁻¹ else (chooseRow k).val.2.1
  let z := fun k : κ=>if second then -(chooseRow k).val.2.2.2.val else (chooseRow k).val.2.2.2.val
  let scalar := fun k : κ=>(Real.sqrt (geometryFirstHighMass reflected s R seed W
    Dfirst Z ξ εmass hK bin (col k)*outer (pick k)) : ℂ)
  have hscalarnorm (k : κ) : ‖scalar k‖^2=geometryFirstHighMass reflected s R seed W
      Dfirst Z ξ εmass hK bin (col k)*outer (pick k) := by
    dsimp only [scalar]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt]
    exact mul_nonneg (geometry_first_high_mass_nonneg reflected s R seed W Dfirst Z ξ εmass
      hK bin (col k)) (houter (pick k))
  have hsrc : ∀l,sourceRadius (source l)≤ Z^SB := fun l=>
    hchild.2 s B hα he hV (C l) R (alloc l) (χ l) t (halloc l)
  have hvgates (k : κ) : (v k).seed∣(v k).C ∧ (v k).seed∣(v k).D ∧
      ((v k).C.absNorm:ℝ)≤ Z^SB ∧ ((v k).D.absNorm:ℝ)≤ Z^SB := by
    have hg:=actual_retained_block_gates (slots (chooseRow k).val.1.1) (source (chooseRow k).val.1.1)
      (R*C (chooseRow k).val.1.1) (projector (chooseRow k).val.1.1)
      (hprojector _) (hz₁ _) (hz₂ _) (Kmain (first _)) (Tsec (first _)) Z ξ (hKm _)
      (chooseRow k).val.1.2
    exact ⟨hg.1,hg.2.1,hg.2.2.1.trans (hsrc _),hg.2.2.2.trans (hsrc _)⟩
  have hsupp (k : κ) := actual_second_encoded_support block label
    (fun q=>⟨(geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin (column q.1).val.1).hC,
      (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin (column q.1).val.1).hD,
      (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin (column q.1).val.1).sameSupport⟩) (chooseRow k)
  have hsupport (k : κ) := hjoint hZ reflected s R seed (Z^Dfirst) ξ a reserve B B hK hseed hs₁ hs₂
    hsource hKM hξ hξε ha hreserve bin (col k) datum label (chooseRow k) rfl rfl
  have hrow (k : κ) : LocalMoment.rawFrequencyNorm (nonzeroJointSourceRow (encoded k))≤ Z^(8*SB) := by
    have hh : LocalMoment.rawFrequencyNorm (nonzeroJointSourceRow (key (pick k)))≤ Z^(B+5*B+loss) :=
      (hsupport k).1
    cases second
    · exact hh.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by dsimp [SB]; linarith))
    · rw [show encoded k=reflectedNonzeroJointLabel (key (pick k)) by rfl,reflected_joint_norm]
      exact hh.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by dsimp [SB]; linarith))
  have hnorm (k : κ) : ((encoded k).val.1.1.1.absNorm:ℝ)≤ Z^(8*SB) ∧
      ((encoded k).val.1.1.2.absNorm:ℝ)≤ Z^(8*SB) ∧
      ((encoded k).val.2.1.1.absNorm:ℝ)≤ Z^(8*SB) ∧ ((encoded k).val.2.1.2.absNorm:ℝ)≤ Z^(8*SB) := by
    have hn:=actual_geometry_norm_caps s R seed (Z^Dfirst) Z ξ B hseed hs₁ hs₂ hsource (col k).1.val
    have hb : Z^B≤ Z^(8*SB):=Real.rpow_le_rpow_of_exponent_le hZ.le (by dsimp [SB]; linarith)
    have hb' : Z^SB≤ Z^(8*SB):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    cases second <;> exact ⟨(hn 0).2.trans hb,(hn 1).2.trans hb,
      (hvgates k).2.2.1.trans hb',(hvgates k).2.2.2.trans hb'⟩
  have hscalarcap (k : κ) : ‖scalar k‖^2*(∏i,(source (chooseRow k).val.1.1).M i)^2*
      ((E k).absNorm:ℝ)^(ε-1)≤ Cscalar*Z^scalarCap := by
    have hscalarpoint := hscalar.2 s hα hlow reflected left second R seed W Dfirst ξ a reserve SB εmass ε Cs hK
      hSB hem hε.le hCs hM hseed hs₁ hs₂
      (hsource.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by dsimp [SB]; linarith)))
      hsap₁ hsap₂
      (hMbox.trans (by dsimp [SB]; linarith)) (hA.trans (by dsimp [SB]; linarith))
      (habox.trans (by dsimp [SB]; linarith)) (hω.trans (by dsimp [SB]; linarith))
      bin (col k) R (alloc (chooseRow k).val.1.1) (χ (chooseRow k).val.1.1) t (halloc _)
      (v k).C (v k).D (v k).hC (v k).hD (v k).sameSupport ⟨(hvgates k).2.2.1,(hvgates k).2.2.2⟩ (v k).inactive
    exact (congrArg (fun x : ℝ=>x*(∏i,(source (chooseRow k).val.1.1).M i)^2*
      ((E k).absNorm:ℝ)^(ε-1)) (hscalarnorm k)).le.trans hscalarpoint
  have hh:=hc.2 left u₀ unit B control T Cscalar hcontrol hT hCscalar.le encoded hinjreflect Finset.univ
    (fun k _=>hrow k)
    (fun k _=>by cases second <;> exact (hsupp k).1)
    (fun k _=>by cases second <;> exact (hsupp k).2)
    (fun k _=>by
      have hg: ((Ideal.span {jointSourceRow left u₀ unit (encoded k).val}*
        firstSourceMissing left (encoded k).val.1).absNorm:ℝ)≤ Z^(B+6*B+loss) := by
        cases second
        · exact (hsupport k).2.2
        · change ((Ideal.span {jointSourceRow left u₀ unit (reflectedJointLabel (key (pick k)).val)}*
              firstSourceMissing left (key (pick k)).val.1).absNorm:ℝ)≤ Z^(B+6*B+loss)
          simpa only [reflected_joint_row,Ideal.span_singleton_neg] using (hsupport k).2.2
      exact hg.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by dsimp [SB]; linarith)))
    (fun k _=>hnorm k) (fun k _=>by cases second <;> exact (hsupport k).2.1)
    s hM he.1 he.2.2.2.1 he.2.2.2.2.2 hwin hscales hP
    (fun k=>C (chooseRow k).val.1.1) (fun _=>R) (fun k=>alloc (chooseRow k).val.1.1)
    (fun k=>χ (chooseRow k).val.1.1) (fun _=>t)
    E (fun k=>(v k).R) (fun k=>(v k).seed) hE (fun k=>(v k).τ (ψ k))
    (fun k=>height (pick k)) (fun _=>0) z scalar (fun k=>Ds (pick k)) B₁ B₂
    hB₁ hB₂ hW₁ hW₂ hcontrolB
    (fun k _=>by cases second <;> first | exact (hvgates k).1 | exact (hvgates k).2.1)
    (fun k _=>hscalarcap k) (fun k _=>hDs (pick k)) 0
  have hcosteq : (∑k : κ,cost (pick k))=
      ∑k∈(Finset.univ : Finset κ),∑L∈Ds (pick k),‖scalar k*normalizedColumn
        (withHeight (source (chooseRow k).val.1.1) ((v k).τ (ψ k)) (height (pick k)))
          (E k) (hE k) (v k).R (v k).seed L (z k)‖^2 := by
    apply Finset.sum_congr rfl
    intro k _
    let c := normalizedColumn
      (withHeight (source (chooseRow k).val.1.1) ((v k).τ (ψ k)) (height (pick k)))
        (E k) (hE k) (v k).R (v k).seed
    have hpoint (L : Ideal O) :
        (geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin (col k)*
          outer (pick k))*‖c L (z k)‖^2=‖scalar k*c L (z k)‖^2 := by
      calc
        _=‖scalar k‖^2*‖c L (z k)‖^2 :=
          congrArg (fun x : ℝ=>x*‖c L (z k)‖^2) (hscalarnorm k).symm
        _=(‖scalar k‖*‖c L (z k)‖)^2 := (mul_pow _ _ 2).symm
        _=_ := congrArg (fun x : ℝ=>x^2) (norm_mul (scalar k) (c L (z k))).symm
    exact (Finset.mul_sum (Ds (pick k)) (fun L=>‖c L (z k)‖^2)
      (geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin (col k)*
        outer (pick k))).trans (Finset.sum_congr rfl (fun L _=>hpoint L))

  have hcub : (∑k : κ,cost (pick k))≤ Kc*(Cscalar*control)*(2*T)^(3*ε)*
      Z^(B+scalarCap+8*SB+loss+((N:ℝ)+2)*plainCap+pad) := by
    rw [hcosteq]
    simpa only [sub_zero,zero_mul,mul_zero,add_zero] using hh
  apply hsum.trans
  have h := mul_le_mul_of_nonneg_left hcub (by positivity : 0≤ D*Z^(2*loss))
  convert h using 1
  rw [show B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
      8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+pad=
      2*loss+(B+scalarCap+8*SB+loss+((N:ℝ)+2)*plainCap+pad) by
        dsimp [SB,scalarCap]; ring,Real.rpow_add hzpos]
  ring

theorem actual_geometry_main_all_projector_coarse_family {α : Type}[Fintype α][DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(hα : Fintype.card α≤ N)
    (B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ U : ℝ)
    (hB : 0≤ B)(hloss : 0< loss)(hε : 0<ε)(hpad : 0< pad)
    (hCs : 1≤ Cs)(hb : 1≤ b)(hbs : 1≤ bs)(hwindow : 0≤ window)(hcap : 0≤ plainCap)
    (hlo : 0< lo)(hap : 0< ap)(hev : 0<εvolume)(hem : 0≤εmass)
    (hξ : 0≤ξ)(hξε : ξ≤ loss)(hU : 0≤ U) :
    ∃K : ℝ,0< K ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
      ∀{Label : Type}[Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(Dfirst a reserve t : ℝ)(hK : 0< Z^Dfirst),
      Squarefree seed → Endpoints b bs bs s →
      lo≤ s.lower → sourceRadius s≤ Z^B → |Real.logb Z (volume s)|≤ B → |Dfirst|≤ B →
      |a|≤ B → |frequencyLoss Z 32 ξ+reserve|≤ B → (∀j,s.M j≤ Cs) →
      (∀j,CenteredMomentSlotRatios.logWindow (s.lo j) (s.hi j)≤ window) →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^plainCap) →
      (∀j,s.P j≤ Z^plainCap) →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U) →
      (∀x,s.W₁ x≠0→ ap≤ x) → (∀x,s.W₂ x≠0→ ap≤ x) →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤ a → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (column : Label→↥(firstLiveColumns (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin) (fun _=>logAnnulus))),
      Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (column l).val,
        (column l).val.2.1.val)) →
      let C := fun l=>geometryColumnIdeal reflected s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      let χ := fun l=>geometryColumnCharacter reflected s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      ∀alloc : (l : Label)→ actualAllocations s.pools (C l),
      (∀l,frozenCoefficient (alloc l).val (C l) R s.ν s.W s.P≠0) →
      let slots := fun l=>liveIndices (alloc l).val
      let source := fun l=>child s (C l) R (alloc l) (χ l) t
      let first := fun l=>geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      let projector := fun l=>(column l).val.2.1.val
      let Kmain := firstMainRadius reflected (Z^Dfirst) (volume s) Z ξ (3*a) reserve
      let Tsec := firstMainFourierScale reflected (Z^Dfirst) (volume s) Z ξ (3*a) reserve b N
      let hprojector := fun l=>actual_first_live_squarefree
        (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin) (fun _=>logAnnulus) (column l).val (column l).property
      let hz₁ : ∀l,(source l).W₁ 0=0 := fun _=>hs₁
      let hz₂ : ∀l,(source l).W₂ 0=0 := fun _=>hs₂
      let hKm : ∀l,0< Kmain (first l) := fun l=>first_main_radius_pos reflected (Z^Dfirst) (volume s)
        Z ξ (3*a) reserve (zero_lt_one.trans hZ) (first l)
      let Index := (l : Label)×ActualSecondBlockIndex (source l) (R*C l) (projector l)
        (Kmain (first l)) (Tsec (first l)) Z ξ
      let datum := fun q : Index=>actualSecondBlockDatum (slots q.1) (source q.1) (R*C q.1) (projector q.1)
        (hprojector q.1) (hz₁ q.1) (hz₂ q.1) (Kmain (first q.1)) (Tsec (first q.1)) Z ξ (hKm q.1) q.2
      let block := fun q : Index=>(datum q).block
      ∀(rows : Finset (secondLiveRows block))(second : Bool)(W : 𝓢(ℝ,ℂ))(height : rows→ℝ)(Ds : rows→ Finset (Ideal O))
        (control B₁ B₂ : ℝ),0≤ control → 0≤ B₁ → 0≤ B₂ →
      (∀x,‖s.W₁ x‖≤ B₁) → (∀x,‖s.W₂ x‖≤ B₂) → (B₁*B₂)^2≤ control →
      (∀r : rows,∀L∈Ds r,L∈(datum r.val.val.1).block.divisors ∧ Squarefree L) →
      let outer := fun r : rows=>(Kmain (first r.val.val.1.1)/volume (source r.val.val.1.1))*
        normalizer (datum r.val.val.1).C (datum r.val.val.1).D (datum r.val.val.1).inactive/lowerFactor N lo ap
      let cost := fun r : rows=>geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin
        (column r.val.val.1.1).val * outer r * highNormalizedRowCost second datum r.val (height r) (Ds r)
      (∑r : rows,cost r)≤ K*control*
        Z^(B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
          8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+2*pad+3*(((N:ℝ)+2)*U)*ε) := by
  let exponent := B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
    8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+pad
  let L := ((N:ℝ)+2)*U
  obtain ⟨K,hK,hfamily⟩ := actual_geometry_main_all_height_coarse_family
    η₀ u₀ F₀ R₀ hu₀ N hα B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ
    hB hloss hε hpad hCs hb hbs hwindow hcap hlo hap hev hem hξ hξε
  obtain ⟨Cp,hCp,hpayment⟩ := shared_projector_shell_payment L pad (by positivity) hpad
  refine ⟨Cp*K*(2:ℝ)^(3*ε),by positivity,?_⟩
  filter_upwards [hfamily,hpayment] with Z hfam hp
  intro hZ Label _ reflected s R seed Dfirst a reserve t hKfirst hseed he hlow hsource hA hMbox habox hω
    hM hwin hscales hP hpool hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin column hinj C χ alloc halloc slots source first projector
    Kmain Tsec hprojector hz₁ hz₂ hKm Index datum block rows second W
    height Ds control B₁ B₂ hcontrol hB₁ hB₂ hW₁ hW₂ hcontrolB hDs outer cost
  let projectors := sharedProjectors Ds
  let columnCost := fun (r : rows) (D : Ideal O)=>
    geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hKfirst bin
      (column r.val.val.1.1).val*outer r*highNormalizedRowCost second datum r.val (height r) {D}
  have houter : ∀r : rows,0≤ outer r := by
    intro r
    exact div_nonneg (mul_nonneg (div_nonneg (hKm _).le (volume_pos _).le)
      (normalizer_pos _ _ (datum r.val.val.1).hC _).le) (lowerFactor_pos N lo ap hlo hap).le
  have hnonneg : ∀r D,0≤ columnCost r D := by
    intro r D
    exact mul_nonneg (mul_nonneg
      (geometry_first_high_mass_nonneg reflected s R seed W Dfirst Z ξ εmass hKfirst bin _)
      (houter r)) (high_normalized_row_cost_nonneg second datum r.val (height r) {D})
  have hnorm : ∀r : rows,∀D∈Ds r,(D.absNorm:ℝ)≤ Z^L := by
    intro r D hD
    apply (second_datum_projector_cap (datum r.val.val.1) N Z U
      ((live_card_le (alloc r.val.val.1.1).val).trans hα) hZ.le hU
      (actual_child_pool_cap s (C r.val.val.1.1) R (alloc r.val.val.1.1)
        (χ r.val.val.1.1) t (Z^U) hpool) D (hDs r D hD).1).2
  have hscale n (hn : n∈selectedShells projectors) :=
    shared_projector_shell_scale Ds Z L hnorm n hn
  have hZpos : 0< Z := zero_lt_one.trans hZ
  let E := K*control*(2:ℝ)^(3*ε)*Z^(exponent+3*L*ε)
  have hE : 0≤ E := by dsimp [E]; positivity
  have hpay (n : ℤ)(hn : n∈selectedShells projectors) :
      (∑r : rows,∑D∈shell projectors n,columnCost r D)≤ E := by
    have h := hfam hZ reflected s R seed Dfirst a reserve t hKfirst hseed he hlow hsource hA hMbox habox hω
      hM hwin hscales hP hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin column hinj alloc halloc
      rows second W height (fun _=>shell projectors n) control (dyadicScale n) B₁ B₂ hcontrol
      (hscale n hn).1 hB₁ hB₂ hW₁ hW₂ hcontrolB
      (fun _ D hD=>by
        have hd:=shared_projector_shell_gates Ds n D hD
        exact ⟨hd.1,hd.2.2⟩)
    have hleft : (∑r : rows,∑D∈shell projectors n,columnCost r D)=
        ∑r : rows,geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hKfirst bin
          (column r.val.val.1.1).val*outer r*
          highNormalizedRowCost second datum r.val (height r) (shell projectors n) := by
      simp only [columnCost,highNormalizedRowCost,Finset.sum_singleton,Finset.mul_sum]
    rw [hleft]
    apply h.trans
    have hdyadic : 0< dyadicScale n := zero_lt_one.trans_le (hscale n hn).1
    have hpow : (2*dyadicScale n)^(3*ε)≤(2:ℝ)^(3*ε)*Z^(3*L*ε) := by
      calc
        _≤(2*Z^L)^(3*ε) := Real.rpow_le_rpow (by positivity)
          (mul_le_mul_of_nonneg_left (hscale n hn).2 (by norm_num)) (by positivity)
        _=_ := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hZpos.le _),←Real.rpow_mul hZpos.le]
          congr 1
          ring
    have hp := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (mul_nonneg hK.le hcontrol))
      (Real.rpow_nonneg hZpos.le exponent)
    convert hp using 1
    dsimp [E]
    rw [Real.rpow_add hZpos]
    ring
  have h := hp.2 Ds (fun r D hD=>(hDs r D hD).2) hnorm columnCost E hnonneg hE hpay
  have hleft : (∑r : rows,cost r)=∑r : rows,∑D∈Ds r,columnCost r D := by
    simp only [cost,columnCost,highNormalizedRowCost,Finset.sum_singleton,Finset.mul_sum]
  rw [hleft]
  convert h using 1
  dsimp [E,exponent,L]
  rw [show B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
      8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+2*pad+3*(((N:ℝ)+2)*U)*ε=
      pad+(B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
      8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+pad+3*(((N:ℝ)+2)*U)*ε) by ring,
    Real.rpow_add hZpos]
  ring


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_ordinary_high_image_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_all_height_coarse_family

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_all_projector_coarse_family
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryMainCoarseFamilySumDecidable

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainCoarseFamily -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryHighCostNormalization; sha256 a31ae78fd5d91d262e241fc74ef9463f53d07f15589048e60e23d39469225f6f -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                             

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentCommonPairedSource
open CenteredMomentCommonLinearNormalization
open CenteredMomentSecondInputCapacitySource
local notation "O" => HeckeFamily.O

private theorem high_cost_scalar (Z amp mass K V lower norm energy : ℝ) (hZ : 0< Z) :
    (mass/V)*(K/lower)*norm*energy=
      (Z^amp/lower)*(mass*(Z^(-amp)*(K/V)*norm)*energy) := by
  have hne : Z^amp≠0 := (Real.rpow_pos_of_pos hZ amp).ne'
  rw [Real.rpow_neg hZ.le]
  simp only [div_eq_mul_inv]
  calc
    _=(Z^amp*(Z^amp)⁻¹)*(mass*V⁻¹*(K*lower⁻¹)*norm*energy) := by
      rw [mul_inv_cancel₀ hne,one_mul]
    _=_ := by ring

/-- The high estimate includes the amplification factor Z^(-amp). This exact
conversion restores Z^amp and the first-source lower factor before using it
as a selected physical cost. Both rays and the right-side sign are retained. -/
theorem actual_main_high_cost_normalization
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (N : ℕ) (a ap Z amp : ℝ) (hZ : 0< Z) (second : Bool)
    (d : Label → SecondInputDatum α) (mass : Label → ℝ) (t u : ℝ)
    (r : SecondRow (fun l=>(d l).block)) (D : Ideal O) :
    let columnEnergy : ℝ := if second then
      ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.2.1⁻¹)
        ((d r.1).input.t+2*Real.pi*(u-(-t))))
        (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed D (-r.2.2.2.val)‖^2
    else
      ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.1)
        ((d r.1).input.t+2*Real.pi*(u-t)))
        (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed D r.2.2.2.val‖^2
    mainNormalizedPhysicalCost N a ap second d
      (fun l=>mass l/volume (d l).input.toData) t u r D=
      (Z^amp/lowerFactor N a ap)*
        (mass r.1*(Z^(-amp)*((d r.1).K/volume (d r.1).input.toData)*
          normalizer (d r.1).C (d r.1).D (d r.1).inactive)*columnEnergy) := by
  intro columnEnergy
  exact high_cost_scalar Z amp (mass r.1) (d r.1).K (volume (d r.1).input.toData)
    (lowerFactor N a ap) (normalizer (d r.1).C (d r.1).D (d r.1).inactive) columnEnergy hZ


/-- The actual amplification factor cancels the restored high power before
summing complete physical rows. The first-source lower factor remains. -/
theorem actual_main_amplified_high_cost_rows
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (N : ℕ) (a ap Z amp : ℝ) (hZ : 0< Z) (second : Bool)
    (d : Label → SecondInputDatum α) (mass : Label → ℝ) (t u : ℝ) :
    let energy := fun (r : SecondRow (fun l=>(d l).block)) (D : Ideal O) =>
      if second then
        ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.2.1⁻¹)
          ((d r.1).input.t+2*Real.pi*(u-(-t))))
          (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed D (-r.2.2.2.val)‖^2
      else
        ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.1)
          ((d r.1).input.t+2*Real.pi*(u-t)))
          (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed D r.2.2.2.val‖^2
    Z^(-amp)*(∑l,mass l/volume (d l).input.toData *
      mainNormalizedBlockCost N a ap second (d l) t u)=
    (1/lowerFactor N a ap)*
      ∑r∈secondLiveRows (fun l=>(d l).block),
        ∑D∈secondResidualIdeals (fun l=>(d l).block) r,
          mass r.1*(Z^(-amp)*((d r.1).K/volume (d r.1).input.toData)*
            normalizer (d r.1).C (d r.1).D (d r.1).inactive)*energy r D := by
  intro energy
  rw [actual_main_block_cost_rows]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro D hD
  rw [actual_main_high_cost_normalization N a ap Z amp hZ]
  change Z^(-amp)*((Z^amp/lowerFactor N a ap)*_)=_
  have hne : Z^amp≠0 := (Real.rpow_pos_of_pos hZ amp).ne'
  rw [Real.rpow_neg hZ.le]
  simp only [div_eq_mul_inv,one_mul]
  dsimp only [energy]
  simp only [←mul_assoc,inv_mul_cancel₀ hne,one_mul]


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_high_cost_normalization

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_amplified_high_cost_rows

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryHighCostNormalization -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryHighNormalized; sha256 28a0997218588432773837eab477c193b0b5eb0b067a6942f85cbef5850fa26f -/
section
                                                      
                                                                 
                                                      

set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open MeasureTheory
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle61HighProfiles Cycle61FinalLow CenteredMomentFiniteProfileExceptional
open Cycle61HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle61Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstSourceReduction ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O

open CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit

open CenteredMomentCommonPairedSource CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonWindowColumn CenteredMomentHeckeColumnWindow FourierBridge

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Full finite high-source column energy from the genuine high density
bound and the bounded joint-key fibers. The maximizing representative keeps
both physical scalar factors inside its cost. No energy bound is assumed. -/
theorem actual_geometry_full_high_columns {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (B Q loss ε : ℝ) (hB : 0≤ B) (hQ : 0≤ Q) (hQB : Q≤ B)
    (hloss : 0< loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0< ap)
    (N : ℕ)(lo εmass εfreq εvolume : ℝ)(hlo : 0< lo)(hεmass : 0≤εmass)
    (hεfreq : 0<εfreq)(hεvolume : 0<εvolume)
    (Cs bs b window pad : ℝ)
    (hCs : 1≤ Cs)(hbs : 1≤ bs)(hb : 1≤ b)(hwindow : 0≤ window)(hpad : 0< pad) :
    ∃bound : ℕ→ℝ,(∀k,0< bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤ P.d*P.vslot → 16*P.τ≤ P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C Kcolumn : ℝ,(0,0)∈F ∧ 0< Cprofile ∧ 0< C ∧ 0< Kcolumn ∧
      ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)(_hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(D ξ : ℝ)(hK : 0< Z^D)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→ FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin))
        (datum : DataLabel→ SecondInputDatum α)(first : DataLabel→ FirstSourceLabel)
        (row : κ→ secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→ RayCharacter),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^D) Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width Wfiber : ℝ) (i : ℕ),
      21/25 ≤ β → β ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T → 0< width →
      0≤ Wfiber →
      ∀labels : Finset κ,
      (∀k,((Finset.univ.filter (fun r : labels=>key r.val=k)).card:ℝ)≤ Wfiber) →
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      let target:=(1-unmarkedDensity (2*β-1))*(frequencyLoss Z 32 ξ+reserveShift)+
        unmarkedDensity (2*β-1)*εfreq+εvolume
      (∀l∈labels,x l 2+width≤ Q) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^B → lo≤ s.lower →
      3401/100000≤ bAmpl → bAmpl≤1/25 → 0≤ D → |D|≤ B → |A|≤ B → |ampExponent|≤ B →
      |frequencyLoss Z 32 ξ+reserveShift|≤ B → εfreq≤ B → ξ≤εfreq →
      A≤ D*Cycle61.Arithmetic.totalA bAmpl → ampExponent≤ D*Cycle61.Arithmetic.amp bAmpl →
      (∀l∈labels,((datum (row l).val.1).C.absNorm:ℝ)≤ Z^B ∧
        ((datum (row l).val.1).D.absNorm:ℝ)≤ Z^B) →
      (∀l∈labels,(datum (row l).val.1).radius=frequencyRadius
        (firstMainFourierScale reflected (Z^D) (volume s.toData) Z ξ (3*ampExponent)
          reserveShift b N (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))) Z ξ) →
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (_hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (_hpuncture : ∀l,(st l).puncture=(datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))
        (_hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀ l ∈ labels, β ≤ HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^B) →
      (i:ℝ)≤ Z^P.τ →
      Fintype.card α≤ N → (∀j,s.M j≤ Cs) →
      s.b₁≤ bs → s.b₂≤ bs → s.upper≤ b →
      (∀j,logWindow (s.lo j) (s.hi j)≤ window) →
      let C₁:=fun l=>geometryColumnIdeal reflected s R seed (Z^D) Z ξ hK bin (column l)
      let χ₁:=fun l=>geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l)
      ∀(B₁ : ∀l,actualAllocations s.pools (C₁ l))(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) R s.ν s.W s.P≠0) →
      let firstChild:=fun l=>child s (C₁ l) R (B₁ l) (χ₁ l) (t₁ l)
      let E:=fun l=>if second then (datum (row l).val.1).D else (datum (row l).val.1).C
      let R₂:=fun l=>(datum (row l).val.1).R
      let outer:=fun l=>Z^(-ampExponent)*
        (firstMainRadius reflected (Z^D) (volume s.toData) Z ξ (3*ampExponent) reserveShift
          (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))/volume (firstChild l))*
        normalizer (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
      let hE : ∀l,Supported (E l):=fun l=>by
        dsimp only [E]; split <;> first | exact (datum (row l).val.1).hD | exact (datum (row l).val.1).hC
      ∀(seed₂ : κ→ Ideal O)(t : κ→ℝ)(w σ v : α→ℝ)(θ : α→ RayQuotient.Characters M H)
        (p : κ→ Profiles ap bp)(Ds : κ→ Finset (Ideal O))(cap : ℝ),
      cap≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap) →
      pad≤ allowance →
      (∀l∈labels,seed₂ l∣E l) →
      (∀l∈labels,(st l).width≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<β+2*P.e) →
      (∀j,0≤ w j) → (∀j,w j/P.d≤ P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤ Kcontrol) →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ)≤ rawError →
      (∑l∈labels,geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)*
        outer l*(∑L∈Ds l,‖normalizedColumn (withHeight (firstChild l) (st l).character (t l))
          (E l) (hE l) (R₂ l) (seed₂ l) L (z l)‖^2))≤
      Wfiber*(Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε)*(
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
          Z^(target-D*(720486667/30493190000000)+4*width+loss+rawError+allowance+B*εmass)))) := by
  obtain ⟨bound,hbound,J,hhigh⟩:=actual_geometry_selected_high_columns (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ B Q loss ε hB hQ hQB hloss hε hap
    N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume
    Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,hjoint⟩:=hhigh P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,?_⟩
  filter_upwards [hjoint] with Z he
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width Wfiber i
    hβ hβ' hKcontrol hT hwidthbin hWfiber labels hfiber A x target hq hseed hs₁ hs₂ hsource hlower
    hbAmpl hbAmpl' hD hDcap hA hamp homega hεfreqB hξε htotalA hampcap hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hzero hsupport hi hcard hM hb₁ hb₂ hupper hwin
    C₁ χ₁ B₁ t₁ hf₁ firstChild E R₂ outer hE seed₂ t w σ v θ p Ds cap hcap hmatches hscales hpadallow
    hseed₂ hwidth hradial hzeroUpper hw hwr hσlo hσhi hheight hplainheight hW hDs hdyad hcontrol hledger
  have hZ : 1< Z:=(by norm_num : (1:ℝ)<2).trans_le he.1
  have hZpos : 0< Z:=zero_lt_one.trans hZ
  let cost (l : κ):=geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)*
    outer l*(∑L∈Ds l,‖normalizedColumn (withHeight (firstChild l) (st l).character (t l))
      (E l) (hE l) (R₂ l) (seed₂ l) L (z l)‖^2)
  let rhs:=Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε)*(
    geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
    ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
    (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
      Z^(target-D*(720486667/30493190000000)+4*width+loss+rawError+allowance+B*εmass)))
  have hrhs : 0≤ rhs := by
    dsimp only [rhs]
    apply mul_nonneg (by positivity)
    exact mul_nonneg (mul_nonneg (geometry_high_factor_pos reflected _ bin
      (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le (Nat.cast_nonneg _)) (by positivity)
  have hc (l : κ) : 0≤ cost l := by
    have houter : 0≤ outer l := by
      dsimp only [outer]
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hZpos.le _)
        (div_nonneg (first_main_radius_pos reflected (Z^D) (volume s) Z ξ (3*ampExponent)
          reserveShift hZpos _).le (volume_pos (firstChild l)).le))
        (normalizer_pos _ _ (datum (row l).val.1).hC _).le
    exact mul_nonneg (mul_nonneg
      (geometry_first_high_mass_nonneg reflected s R seed W D Z ξ εmass hK bin _) houter)
      (Finset.sum_nonneg (fun _ _=>sq_nonneg _))
  by_cases hnil : labels=∅
  · subst labels
    simp only [Finset.sum_empty]
    exact mul_nonneg hWfiber hrhs
  have hnonempty:=Finset.nonempty_iff_ne_empty.mpr hnil
  obtain ⟨pick,hpick,hinj,hsum⟩:=high_family_max_selection
    (fun r : labels=>key r.val) (fun r=>cost r.val) Wfiber hWfiber (fun r=>hc r.val) hfiber
  let Keys:=Finset.univ.image (fun r : labels=>key r.val)
  let selected (j : Keys):κ:=(pick j).val
  have hmem (j : Keys) : selected j∈labels:=(pick j).property
  haveI : Nonempty Keys := by
    obtain ⟨l,hl⟩:=hnonempty
    exact ⟨⟨key l,Finset.mem_image.mpr ⟨⟨l,hl⟩,Finset.mem_univ _,rfl⟩⟩⟩
  have hh:=he.2 (κ:=Keys) reflected second s hη R seed W D ξ hK bin
    (fun j=>column (selected j)) datum first (fun j=>row (selected j))
    (fun j=>hparent (selected j)) (fun j=>hfirst (selected j)) (fun j=>hR (selected j))
    (fun j=>ψ (selected j)) β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width i
    hβ hβ' hKcontrol hT hwidthbin
    (show Function.Injective (fun j : Keys=>key (selected j)) from hinj) Finset.univ
    (fun j _=>hq (selected j) (hmem j)) hseed hs₁ hs₂ hsource hlower
    hbAmpl hbAmpl' hD hDcap hA hamp homega hεfreqB hξε htotalA hampcap
    (fun j _=>hnorm (selected j) (hmem j)) (fun j _=>hradius (selected j) (hmem j))
    (fun j=>st (selected j)) (fun j=>hQM (selected j)) (fun j=>hQη (selected j))
    (fun j=>z (selected j)) (fun j=>hz (selected j)) (fun j=>hchar (selected j))
    (fun j=>hpuncture (selected j)) (fun j=>hrow (selected j))
    (fun j _=>hzero (selected j) (hmem j)) (fun j _=>hsupport (selected j) (hmem j))
    hi hcard hM hb₁ hb₂ hupper hwin
    (fun j=>B₁ (selected j)) (fun j=>t₁ (selected j)) (fun j _=>hf₁ (selected j) (hmem j))
    (fun j=>seed₂ (selected j)) (fun j=>t (selected j)) w σ v θ (fun j=>p (selected j))
    (fun j=>Ds (selected j)) cap hcap hmatches hscales hpadallow
    (fun j _=>hseed₂ (selected j) (hmem j)) (fun j _=>hwidth (selected j) (hmem j))
    (fun j _=>hradial (selected j) (hmem j)) (fun j _=>hzeroUpper (selected j) (hmem j))
    hw hwr hσlo hσhi (fun j _=>hheight (selected j) (hmem j))
    (fun j _=>hplainheight (selected j) (hmem j)) (fun j _=>hW (selected j) (hmem j))
    (fun j _=>hDs (selected j) (hmem j)) (fun j _=>hdyad (selected j) (hmem j))
    (fun j _=>hcontrol (selected j) (hmem j)) hledger
  have hselected : (∑j : Keys,cost (selected j))≤ rhs := by
    simpa only [cost,selected,rhs] using hh
  change (∑l∈labels,cost l)≤ Wfiber*rhs
  rw [←Finset.sum_coe_sort labels cost]
  exact hsum.trans (mul_le_mul_of_nonneg_left hselected hWfiber)

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_full_high_columns

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryHighNormalized -/
