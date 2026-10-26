import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondHighBox
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondFrequencyBudget
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic LocalMoment
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn

/-- The fixed lower-volume loss belongs to the outside scalar coordinate. -/
def childHighCoordinates (x : Fin 4→ℝ) (εv : ℝ) : Fin 4→ℝ :=
  fun j=>x j+if j=0 then εv else 0

lemma child_high_exponent_value (δ εv : ℝ) (x : Fin 4→ℝ) :
    highExponentValue δ (childHighCoordinates x εv)=highExponentValue δ x+εv := by
  simp [highExponentValue,childHighCoordinates]
  ring

lemma child_high_coordinate_box (x : Fin 4→ℝ) (B εv : ℝ)
    (hx : ∀j,-B≤x j ∧ x j≤B) :
    ∀j,-(B+|εv|)≤ childHighCoordinates x εv j ∧
      childHighCoordinates x εv j≤B+|εv| := by
  intro j
  have hh:=hx j
  have he:=abs_le.mp (le_refl |εv|)
  by_cases hj : j=0
  · subst j
    simp only [childHighCoordinates,ite_true]
    constructor <;> linarith
  · simp only [childHighCoordinates,hj,ite_false]
    constructor <;> linarith [abs_nonneg εv]

/-- The literal child denominator is paid uniformly before the moving source.
No estimate of a high density or a selected row is assumed here. -/
theorem eventual_actual_child_high_coefficient (N : ℕ) (lo εv : ℝ)
    (hlo : 0<lo) (hev : 0<εv) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤N → lo≤ s.lower →
    ∀(reflected left second : Bool) (l : FirstSourceLabel)
    (_hC : Supported l.1.1) (_hD : Supported l.1.2),
    primeSupport l.1.1=primeSupport l.1.2 →
    ∀(Rfirst : Ideal O)(B : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ),
    frozenCoefficient B.val (if reflected then l.1.2 else l.1.1) Rfirst s.ν s.W s.P≠0 →
    ∀(C₂ D₂ : Ideal O)(_hC₂ : Supported C₂)
    (U : Finset (CommonIndex C₂ D₂))(M a ξ reserve ε : ℝ),
    let x:=childHighCoordinates (actualHighCoordinates reflected left second l C₂ D₂ U
      Z M (Real.logb Z (volume s)) a ξ reserve ε) εv
    Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/volume
      (child s (if reflected then l.1.2 else l.1.1) Rfirst B χ t))*
      (normalizer C₂ D₂ U/Z^(Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)))≤Z^(x 0) := by
  filter_upwards [eventual_common_inverse_volume N lo εv hlo hev] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ s hcard hlow reflected left second l hC hD heq Rfirst B χ t hB
    C₂ D₂ hC₂ U M a ξ reserve ε
  have hZ:=zero_lt_one.trans hz.1
  let A:=Real.logb Z (volume s)
  let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
  have hc : (0:ℝ)<(if reflected then l.1.2 else l.1.1).absNorm := by
    cases reflected
    · exact norm_pos _ hC.1
    · exact norm_pos _ hD.1
  have hV : Z^A=volume s:=Real.rpow_logb hZ hz.1.ne' (volume_pos s)
  have hratio : ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)/volume s=
      (Z^(A-c))⁻¹ := by
    rw [Real.rpow_sub hZ,hV,Real.rpow_logb hZ hz.1.ne' hc,inv_div]
  have hi:=hz.2 s hcard hlow _ Rfirst B χ t hB
  rw [hratio] at hi
  have hm:=mul_le_mul_of_nonneg_left hi
    (first_main_radius_pos reflected (Z^M) (volume s) Z ξ (3*a) reserve hZ l).le
  have hr : firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/
      volume (child s (if reflected then l.1.2 else l.1.1) Rfirst B χ t)≤
      Z^εv*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/Z^(A-c)) := by
    simpa only [div_eq_mul_inv,mul_left_comm] using hm
  have hh:=mul_le_mul_of_nonneg_left hr (Real.rpow_pos_of_pos hZ (-a)).le
  have hn:=div_nonneg (normalizer_pos C₂ D₂ hC₂ U).le
    (Real.rpow_pos_of_pos hZ (Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ))).le
  apply (mul_le_mul_of_nonneg_right hh hn).trans_eq
  rw [←hV,actual_main_radius_power reflected l hC hD heq Z M A a ξ reserve hz.1,
    actual_second_normalizer_power C₂ D₂ hC₂ U Z hz.1]
  simp only [←Real.rpow_sub hZ,←Real.rpow_add hZ]
  congr 1
  dsimp [childHighCoordinates,actualHighCoordinates,A,c]
  rw [Real.logb_rpow hZ hz.1.ne']
  ring

/-- The missing-radical bin coordinate is an exact identity. -/
lemma actual_child_high_missing (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2) (C₂ D₂ : Ideal O) (U : Finset (CommonIndex C₂ D₂))
    (Z M A a ξ reserve ε εv : ℝ) (hZ : 1<Z) :
    ((firstSourceMissing left l).absNorm:ℝ)=Z^((childHighCoordinates
      (actualHighCoordinates reflected left second l C₂ D₂ U Z M A a ξ reserve ε) εv) 1) := by
  have hn:= (first_missing_norm_le left l hC hD).1
  have hp : (0:ℝ)<(firstSourceMissing left l).absNorm := by exact_mod_cast hn
  simpa [childHighCoordinates,actualHighCoordinates] using
    (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hp).symm

/-- Fixed geometric support supplies the arithmetic gates for both signs.
The remaining hypotheses are scalar caps, not analytic density estimates. -/
theorem actual_geometry_high_coordinate_gates {α : Type} [Fintype α] [DecidableEq α]
    (s : Input α)(Rseed seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (column : FirstColumnIndex (geometryFirstSource s Rseed seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (M A a reserve ε εv B : ℝ)(hZ : 1<Z)(hB : 0≤B)
    (hfirst : ((geometryFirstLabel s Rseed seed K Z ξ hK bin column).1.1.absNorm:ℝ)≤Z^B ∧
      ((geometryFirstLabel s Rseed seed K Z ξ hK bin column).1.2.absNorm:ℝ)≤Z^B)
    (hsecond : (d₂.C.absNorm:ℝ)≤Z^B ∧ (d₂.D.absNorm:ℝ)≤Z^B)
    (hMbox : |M|≤B)(hAbox : |A|≤B)(habox : |a|≤B)
    (hω : |frequencyLoss Z 32 ξ+reserve|≤B)(hε : |ε|≤B) :
    let l:=geometryFirstLabel s Rseed seed K Z ξ hK bin column
    let x:=childHighCoordinates (actualHighCoordinates reflected left second l d₂.C d₂.D U
      Z M A a ξ reserve ε) εv
    ((firstSourceMissing left l).absNorm:ℝ)=Z^(x 1) ∧
      (∀j,-(32*B+|εv|)≤x j ∧ x j≤32*B+|εv|) := by
  intro l x
  have hC : Supported l.1.1 := (geometryFirstSource s Rseed seed K Z ξ hK bin column.1).hC
  have hD : Supported l.1.2 := (geometryFirstSource s Rseed seed K Z ξ hK bin column.1).hD
  refine ⟨actual_child_high_missing reflected left second l hC hD d₂.C d₂.D U
    Z M A a ξ reserve ε εv hZ,?_⟩
  exact child_high_coordinate_box _ (32*B) εv
    (actual_high_coordinate_box reflected left second l hC hD d₂.C d₂.D d₂.hC d₂.hD
      d₂.sameSupport U Z M A a ξ reserve ε B hZ hB hfirst hsecond hMbox hAbox habox hω hε)

/-- Nonzero literal retention derives the third bin coordinate. Fixed unit
costs are absorbed before the first label, projector and second row move. -/
theorem eventual_actual_child_high_frequency (u₀ : O)(b ε : ℝ)(N : ℕ)
    (hb : 0<b)(hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀(reflected left second : Bool)(unit : FirstSourceLabel→Oˣ)
      (l : NonzeroJointSourceLabel left u₀ (fun k=>(unit k:O)))
      (_hC : Supported l.val.1.1.1)(_hD : Supported l.val.1.1.2),
      primeSupport l.val.1.1.1=primeSupport l.val.1.1.2 →
      ∀(V M a reserve ξ εv : ℝ),0<V → ξ≤ε →
      let R:=frequencyRadius (firstMainFourierScale reflected (Z^M) V Z ξ (3*a) reserve b N l.val.1) Z ξ
      let A:=(commonFrequencyGenerator l.val.2.1.1 l.val.2.1.2*
        nonunitFrequencyGenerator l.val.2.1.1 l.val.2.1.2 l.val.2.2.val.1)*l.val.2.2.val.2
      retainedWeight R (normValue A)≠0 →
      let x:=childHighCoordinates (actualHighCoordinates reflected left second l.val.1
        l.val.2.1.1 l.val.2.1.2 l.val.2.2.val.1 Z M (Real.logb Z V) a ξ reserve ε) εv
      0≤x 2 ∧ normValue (jointSourceRow left u₀ (fun k=>(unit k:O)) l.val)≤Z^(x 2) := by
  filter_upwards [eventual_actual_joint_frequency_budget u₀ b ε N hb hε] with Z hz
  refine ⟨hz.1,?_⟩
  intro reflected left second unit l hC hD heq V M a reserve ξ εv hV hξ R A hret x
  have hp:=zero_lt_one.trans hz.1
  have hh:=hz.2 reflected left unit l hC hD heq (Z^M) V a (frequencyLoss Z 32 ξ) reserve ξ
    (Real.rpow_pos_of_pos hp M) hV hξ hret
  rw [Real.logb_rpow hp hz.1.ne'] at hh
  simpa [x,childHighCoordinates,actualHighCoordinates,normValue,sub_add_eq_sub_sub] using hh

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
