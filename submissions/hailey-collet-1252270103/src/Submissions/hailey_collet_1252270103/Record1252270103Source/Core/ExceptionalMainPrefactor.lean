/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original first MAIN prefactor and Fourier scale, with parent volume and
the actual allocation-card square, are paid before the first-key sum. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.MarkedMainPrefactor
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.ExceptionalFirstScalar

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.ExceptionalPrice
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentFirstAnnularMajorant CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst Cycle61Moment Cycle61InitialMass
open MarkedMainRemainder Pool
local notation "O"=>HeckeFamily.O

theorem uniform_first_main_prefactor (N : ℕ) (B ε ell lower radiusMax : ℝ)
    (hB : 0≤B) (hε : 0<ε) (hell : 0<ell) (hlower : 0<lower) (hmax : 0≤radiusMax) :
    ∃A : ℝ,0<A ∧ ∀{ι : Type}[Fintype ι](s : Input ι),Fintype.card ι≤N→
      ∀(C : Ideal O)(P : Finset (Ideal O))(Z amp mesh loss BD Bsource : ℝ)(depth : ℕ),
      C≠0→(C.absNorm:ℝ)≤Z^B→FixedCellPoolData P Z amp ell mesh loss BD Bsource depth→
      ∀H0 radius : ℝ,0<H0 → 0≤radius+6*amp → radius+6*amp≤radiusMax →
      (((bands H0).card:ℝ)*((actualAllocations s.pools C).card:ℝ)^2/(P.card:ℝ)*
        ((radius+6*amp)/ell))/lower≤A*Z^(-amp+ε+loss) := by
  let δ:=ε/(B+1)
  have hδ : 0<δ:=div_pos hε (by positivity)
  obtain ⟨A,hA,hcard⟩:=uniform_allocation_card_square N δ hδ
  refine ⟨1+7*A*(radiusMax/ell)/lower,by positivity,?_⟩
  intro ι inst s hN C P Z amp mesh loss BD Bsource depth hC hcap hp H0 radius hH hr0 hr
  have hZ0:=zero_lt_one.trans hp.scale_gt_one
  have hδeq : δ*(B+1)=ε := by dsimp only [δ];field_simp
  have hc : ((actualAllocations s.pools C).card:ℝ)^2≤A*Z^ε := by
    apply (hcard s hN C hC).trans
    apply mul_le_mul_of_nonneg_left _ hA.le
    calc
      _≤(Z^B)^δ:=Real.rpow_le_rpow (Nat.cast_nonneg _) hcap hδ.le
      _=Z^(B*δ):=(Real.rpow_mul hZ0.le B δ).symm
      _≤Z^ε:=Real.rpow_le_rpow_of_exponent_le hp.scale_gt_one.le (by nlinarith)
  have hb:=mul_le_mul (bands_card H0 hH) hc (sq_nonneg _) (by norm_num : (0:ℝ)≤7)
  have hpool:=hp.reciprocal
  have hr' : (radius+6*amp)/ell≤radiusMax/ell:=div_le_div_of_nonneg_right hr hell.le
  have hm:=mul_le_mul
    (mul_le_mul hb hpool (by positivity : 0≤(P.card:ℝ)⁻¹) (by positivity)) hr'
    (div_nonneg hr0 hell.le) (by positivity)
  have hd:=div_le_div_of_nonneg_right hm hlower.le
  have he : (7*(A*Z^ε))*Z^(-amp+loss)*(radiusMax/ell)/lower=
      (7*A*(radiusMax/ell)/lower)*Z^(-amp+ε+loss) := by
    simp only [Real.rpow_add hZ0]
    ring
  change (((bands H0).card:ℝ)*((actualAllocations s.pools C).card:ℝ)^2*(P.card:ℝ)⁻¹*
    ((radius+6*amp)/ell))/lower≤_ at hd
  rw [he] at hd
  have hd' : (((bands H0).card:ℝ)*((actualAllocations s.pools C).card:ℝ)^2/(P.card:ℝ)*
      ((radius+6*amp)/ell))/lower≤(7*A*(radiusMax/ell)/lower)*Z^(-amp+ε+loss) := by
    simpa only [div_eq_mul_inv] using hd
  exact hd'.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hZ0.le _))

theorem radial_parent_identity (b V C H Z ξ : ℝ)
    (hb : 0≤b) (hV : 0<V) (hC : 0<C) (hH : 0<H) (hZ : 0<Z) :
    H*(4*frequencyRadius ((b*V/C)^2/H) Z ξ)^(1/6:ℝ)=
      (4:ℝ)^(1/6:ℝ)*b^(1/3:ℝ)*(V/C)^(1/3:ℝ)*H^(5/6:ℝ)*Z^(ξ/12) := by
  have hbc : 0≤b*V/C:=by positivity
  unfold frequencyRadius
  rw [Real.mul_rpow (by positivity : (0:ℝ)≤4) (by positivity),
    Real.mul_rpow (by positivity) (Real.rpow_nonneg hZ.le _),
    Real.div_rpow (sq_nonneg _) hH.le,←Real.rpow_natCast_mul hbc,
    show ((2:ℕ):ℝ)*(1/6)=1/3 by norm_num,
    show b*V/C=b*(V/C) by ring,Real.mul_rpow hb (div_pos hV hC).le,
    ←Real.rpow_mul hZ.le,show ξ/2*(1/6)=ξ/12 by ring]
  have hh : H/H^(1/6:ℝ)=H^(5/6:ℝ) := by
    calc
      _=H^((1:ℝ)-1/6) := by rw [Real.rpow_sub hH,Real.rpow_one]
      _=_ := by norm_num
  calc
    _=(4:ℝ)^(1/6:ℝ)*b^(1/3:ℝ)*(V/C)^(1/3:ℝ)*(H/H^(1/6:ℝ))*Z^(ξ/12) := by ring
    _=_ := by rw [hh]

theorem actual_first_fourier_payment (reflected : Bool)(l : FirstSourceLabel)
    (hC : Supported l.1.1)(hD : Supported l.1.2)
    (N : ℕ)(Z V ξ amp reserve : ℝ)(hZ : 0<Z)(hV : 0<V) :
    firstMainRadius reflected Z V Z ξ (3*amp) reserve l*
      (4*frequencyRadius (firstMainFourierScale reflected Z V Z ξ (3*amp) reserve 2 N l) Z ξ)^(1/6:ℝ)=
      ((4:ℝ)^(1/6:ℝ)*((2:ℝ)^N)^(1/3:ℝ))*
        (V/((if reflected then l.1.2 else l.1.1).absNorm:ℝ))^(1/3:ℝ)*
        (firstMainRadius reflected Z V Z ξ (3*amp) reserve l)^(5/6:ℝ)*Z^(ξ/12) := by
  have hn : (0:ℝ)<(if reflected then l.1.2 else l.1.1).absNorm := by
    have hc : (if reflected then l.1.2 else l.1.1)≠0 := by cases reflected <;> first | exact hC.1 | exact hD.1
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hc)
  exact radial_parent_identity ((2:ℝ)^N) V _ _ Z ξ (by positivity) hV hn
    (first_main_radius_pos reflected Z V Z ξ (3*amp) reserve hZ l) hZ

end
end QRH.Record1252270103Source.ExceptionalPrice
#print axioms QRH.Record1252270103Source.ExceptionalPrice.uniform_first_main_prefactor
#print axioms QRH.Record1252270103Source.ExceptionalPrice.radial_parent_identity
#print axioms QRH.Record1252270103Source.ExceptionalPrice.actual_first_fourier_payment
