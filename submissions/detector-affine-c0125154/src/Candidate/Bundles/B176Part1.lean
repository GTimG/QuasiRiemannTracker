/- Packaging rehearsal. Original notices retained; separate replay required. -/
/- B176 part 1 of 4: one original source section, unchanged, split out for the 600-second per-module replay limit. -/
import Candidate.Bundles.B117
import Candidate.Bundles.B133
import Candidate.Bundles.B135
import Candidate.Bundles.B150
import Candidate.Bundles.B155
import Candidate.Bundles.B161
import Candidate.Bundles.B172
import Candidate.Bundles.B173
import Candidate.Bundles.B174
import Candidate.Bundles.B175

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
